import Lean.Compiler.LCNF.ToLCNF
import Lean.Meta

import LeanToLambdaBox.Basic
import LeanToLambdaBox.Printing
import Std.Data

open Lean
open Lean.Compiler.LCNF

namespace Erasure

/--
State carried by EraseM to handle constants and inductive types registered in the global environment.
-/
structure ErasureState: Type where
  inductives: Std.HashMap Name inductive_id := ∅
  constants: Std.HashMap Name kername := ∅
  /-- This field is only updated, not read. -/
  gdecls: global_declarations := []

namespace Config

/--
How to handle functions with the @[extern] attribute.
Notably, this includes `Nat.add` et al., but also some constructors such as those of `Int`.
-/
inductive Extern where
  /-- If a Lean definition is present, use that one. -/
  | preferLogical
  /-- Ignore any Lean definitions and always treat as an axiom to be provided OCaml-side. -/
  | preferAxiom
deriving BEq

/-- How to handle literals and constructors of `Nat`. -/
inductive Nat
  /-- Keep Nat as an inductive type and represent literals by using constructors. -/
  | peano
  /--
  Turn Nat literals into i63 (panic on overflow), translate .zero into literal 0 and .succ x into x + literal 1.
  For this to work, the usual functions on `Nat` (addition, multiplication etc) must not use the logical implementation in Lean
  and instead use Zarith functions linked with the ML files, so setting config.extern to .preferAxiom is necessary.
  -/
  | machine

end Config

structure ErasureConfig: Type where
  extern: Config.Extern := .preferAxiom
  nat: Config.Nat := .machine
  /-- Whether to perform csimp replacements before erasure. -/
  csimp: Bool := true

structure ErasureContext: Type where
  lctx: LocalContext := {}
  fixvars: Option (Std.HashMap Name FVarId) := .none
  config: ErasureConfig

/-- The monad in ToLCNF has caches, a local context and toAny as a set of fvars, all as mutable state for some reason.
    Here I just have a read-only local context, in order to be able to use MetaM's type inference, and keep the complexity low.
    If this is much too slow, try caching stuff again.

    Above the local context there is also a state handling the global environment of the extracted program.
    -/
abbrev EraseM := StateT ErasureState <| ReaderT ErasureContext CoreM

def run (x : EraseM α) (config: ErasureConfig): CoreM (α × ErasureState) :=
  x |>.run {} |>.run { config }

def fvar_to_name (x: FVarId): EraseM ppname := do
  let n := (← read).lctx.fvarIdToDecl |>.find! x |>.userName
  let s: String := n.toString
  -- check if s is ASCII graphic, otherwise the λbox parser will complain
  if s.all (fun c => 33 <= c.toNat /\ c.toNat < 127) then
    return .named n.toString
  else
    return .anon

def mkLambda (x: FVarId) (body: neterm): EraseM neterm := do return .lambda (← fvar_to_name x) (abstract x body)

def mkLetIn (x: FVarId) (val body: neterm): EraseM neterm := do return .letIn (← fvar_to_name x) val (abstract x body)

/--
In Rocq it is mutual blocks which are named, so I'm just making something up here.
-/
def to_inductive_id (indinfo: InductiveVal): EraseM inductive_id := do
  if let .some iid := (← get).inductives.get? indinfo.name then
    return iid
  else
    let names := indinfo.all
    let mutual_block_name := indinfo.all |>.map toString |> String.join |> root_kername
    let ind_bodies: List one_inductive_body ← names.zipIdx.mapM fun (ind_name, idx) => do
      modify (fun s => { s with inductives := s.inductives.insert ind_name { mutual_block_name, idx }})
      let .inductInfo inf ← getConstInfo ind_name | unreachable!
      let ind_ctors: List constructor_body ← inf.ctors.mapM fun ctor_name => do
        let .ctorInfo ci ← getConstInfo ctor_name | unreachable!
        return { cstr_name := toString ctor_name, cstr_nargs := ci.numFields }
      let ind_name := toString ind_name
      let is_struct := names.length == 1 && inf.ctors.length == 1 && !inf.isRec
      let ind_projs: List projection_body ←
        if is_struct then
          let .ctorInfo ci ← getConstInfo inf.ctors[0]! | unreachable!
          let num_fields := ci.numFields
          pure (List.range num_fields |>.map toString |>.map projection_body.mk)
        else
          pure []
      return { ind_name, ind_ctors, ind_projs }
    let mutual_body := { ind_npars := indinfo.numParams, ind_bodies }
    modify (fun s => { s with gdecls := s.gdecls.cons (mutual_block_name, .InductiveDecl mutual_body) })
    return (← get).inductives[indinfo.name]!

def getExternSymbolName (name: Name): CoreM String := do
  return (getExternNameFor (← getEnv) `all name).get!

/-- Silently do nothing if `name` is already present in `constants`. -/
def addAxiom (name: Name): EraseM Unit := do
  unless (← get).constants.contains name do
    logInfo s!"Emitting axiom for constant {name}."
    let kn := to_kername name
    modify (fun s => { s with constants := s.constants.insert name kn, gdecls := s.gdecls.cons (kn, .ConstantDecl ⟨.none⟩) })

/-- The order of variables here is what it is because the other way around led to segfaults. -/
def mkAlt (xs: List FVarId) (body: neterm): EraseM (List ppname × neterm) := do
  let mut body := body
  let names ← xs.mapM fvar_to_name
  for (fvarid, i) in xs.zipIdx do
    body := toBvar fvarid i body
  return (names, body)

def mkCase (indInfo: InductiveVal) (discr: neterm) (alts: List (List ppname × neterm)): EraseM neterm :=
  do return .case (← to_inductive_id indInfo, indInfo.numParams) discr alts

/-- Remove the ._unsafe_rec suffix from a Name if it is present. -/
def remove_unsafe_rec (n: Name): Name := Compiler.isUnsafeRecName? n |>.getD n

/-- Check binding order here as well, may be wrong. -/
def mkDef (name: Name) (fixvarnames: List Name) (body: neterm): EraseM (@edef neterm) := do
  let mut body := body
  for (n, i) in fixvarnames.reverse.zipIdx do
    body := toBvar ((← read).fixvars.get![n]!) i body
  return { name := .named name.toString, body }

/-- Run an action of MetaM in EraseM using EraseM's local context of Lean types. -/
@[inline] def liftMetaM (x : MetaM α) : EraseM α := do
  x.run' { lctx := (← read).lctx }

/-- Similar to Meta.withLocalDecl, but in EraseM.
    k will be passed some fresh FVarId and run in a context in which it is bound. -/
def withLocalDecl (n: Name) (type: Expr) (bi: BinderInfo) (k: FVarId -> EraseM α): EraseM α := do
  let fvarid <- mkFreshFVarId;
  withReader (fun ctx => { ctx with lctx := ctx.lctx.mkLocalDecl fvarid n type bi }) (k fvarid)

/-- Like Meta.withLetDecl. -/
def withLocalDef (n: Name) (type val: Expr) (nd: Bool) (k: FVarId -> EraseM α): EraseM α := do
  let fvarid <- mkFreshFVarId;
  withReader (fun ctx => { ctx with lctx := ctx.lctx.mkLetDecl fvarid n type val nd }) (k fvarid)

/--
A version of Meta.lambdaTelescope that
- unpacks exactly one layer of lambda-abstraction (ie does not telescope)
- works in PrepareM instead of (any monad from which we can control) MetaM.
- yields an FVarId instead of an Expr for the bound variable
Panics if applied to something which is not of the form .lambda ..
-/
def lambdaMonocular {α} [Inhabited α] (e: Expr) (k: FVarId -> Expr -> EraseM α): EraseM α := do
  let .lam binderName type body bi := e | unreachable!
  withLocalDecl binderName type bi (fun fvarid => k fvarid <| body.instantiate1 (.fvar fvarid))
/-- Destructures a let-expression for handling by a continuation in an appropriate context. The continuation gets an FVarId for the bound variable and bound value and body as expressions. Panics if applied to an expression which is not of the form .letE ..
-/
def letMonocular {α} [Inhabited α] (e: Expr) (k: FVarId -> Expr -> Expr -> EraseM α): EraseM α := do
  let .letE binderName type val body nd := e | unreachable!
  withLocalDef binderName type val nd (fun fvarid => k fvarid val (body.instantiate1 (.fvar fvarid)))

/--
Destructures a type expression of the form `∀ a: A, B`,
running the continuation on the body B (with DB variable 0 suitably instantiated with some fvar `a`) and the bound fvar,
in a context with `a: A`.
Panics if applied to an expression which is not of the form .forallE ..
-/
def forallMonocular {α} [Inhabited α] (t: Expr) (k: FVarId -> Expr -> EraseM α) := do
  let Expr.forallE binderName type body bi := t | unreachable!
  withLocalDecl binderName type bi (fun fvarid => k fvarid <| body.instantiate1 <| .fvar fvarid)

/--
Given an expression `e` and its type, which is assumed to be of the form `∀ a:A, B`,
run a continuation `k` in a context where a fvar `a` has type `A`.
- if `e` is `fun a: A => body`, `k` will be run on the expression `body` directly.
- if `e` is not of this form, `k` will be run on the expression `.app e (.fvar a)`
In both cases the second argument to `k` is `B`, the type of the first argument in the new context.
Assumes that `type` is the type of `e` in the context where it is called.
Panics if `type` is not a function type.
-/
def lambdaMonocularOrIntro {α} [Inhabited α] (e type: Expr) (k: Expr -> Expr -> FVarId -> EraseM α): EraseM α :=
  forallMonocular type fun fvarid bodytype => do
    if let .lam _ _ body _ := e then
      /-
      Here I use the binder name and info from the type-level forall binder we are under.
      It might be better to get it from the lambda binder.
      -/
      k (body.instantiate1 <| .fvar fvarid) bodytype fvarid
    else
      -- Here in any case I must use the binder name and info from the forall binder.
      k (.app e (.fvar fvarid)) bodytype fvarid

/--
Given an expression `e` and its type, which is assumed to start with at least `arity` `∀` quantifiers,
get the body of `e` after application to `arity` arguments.
For example, if `e` is `fun a b => asdf` with type `A -> B -> C -> D`, applying `lambdaOrIntroToArity 3`
will run the continuation in the context `a: A, b: B, c: C` on the expression `.app asdf (.fvar c)`
with the fvars `#[a, b, c]`.
I think I got the order of fvars right but thinking about continuations is hard.
Writing the code in this way is suboptimal; there is a first phase in which we only descend through lambdas
and a second phase in which we descend the remaining distance through the type by appending fvars,
but here we check whether there is a lambda to go under each time.
This is probably easily fixable using something like lambdaBoundedTelescope.
-/
def lambdaOrIntroToArity {α} [Inhabited α] (e type: Expr) (arity: Nat) (k: Expr -> Array FVarId -> EraseM α): EraseM α :=
  match arity with
  | 0 => k e #[]
  | n+1 => lambdaMonocularOrIntro e type fun body bodytype fvarid =>
      lambdaOrIntroToArity body bodytype n (fun e fvarids => k e (fvarids.push fvarid))

/--
Given an expression, deconstruct it into an application to at least arity arguments,
then build a neterm from it given the continuation.
This will eta-expand if necessary.
Panics if the type of e does not start with at least arity .forallE constructors.
-/
partial def withAppEtaToMinArity (e: Expr) (arity: Nat) (k: Expr -> Array Expr -> EraseM neterm): EraseM neterm := do
  let type ← liftMetaM do Meta.inferType e
  e.withApp (fun f args => go type f args)
where
  -- Invariant: type is the type of f *args.
  go (type f: Expr) (args: Array Expr): EraseM neterm :=
    if args.size >= arity then
      k f args
    else
      forallMonocular type fun fvarid bodytype => do
        let res ← go bodytype f (args.push (.fvar fvarid))
        mkLambda fvarid res

/--
TODO: The function ToLCNF.isTypeFormerType has an auxiliary function "quick"
which I removed here because I didn't understand why it was correct.
Maybe putting it back makes things faster.
-/
def isErasable (e : Expr) : EraseM Bool :=
  liftMetaM do
    let type ← Meta.inferType e
    -- Erase evidence of propositions
    -- ToLCNF includes an explicit check for isLcProof, but I think the type information should be enough to erase those here.
    if (← Meta.isProp type) then
      return true
    -- Erase types and type formers
    if (← Meta.isTypeFormerType type) then
      return true
    return false
      
/--
This is used to detect if a definition is recursive.
Occurrences of `name` in types may or may not be detected, but I don't think this matters in practice.
-/
def name_occurs (name: Name) (e: Expr): Bool :=
  match e with
  | .const n' .. => name == remove_unsafe_rec n'
  | .bvar .. | .fvar .. | .mvar .. | .sort .. | .forallE .. /- these are types, so ignoring -/ | .lit .. => .false
  | .lam _ _ e _ | .mdata _ e | .proj _ _ e => name_occurs name e
  | .app a b | .letE _ _ a b _ => name_occurs name a || name_occurs name b

/--
Replace nested occurrences of `unsafeRec` names with the safe ones.
Copied over from ToDecl.lean because it is private there.
I think this doesn't actually need to be in CoreM and could just use `Expr.replace`.
-/
def replaceUnsafeRecNames (value : Expr) : CoreM Expr :=
  Core.transform value fun e =>
    match e with
    | .const declName us =>
      if let some safeDeclName := Compiler.isUnsafeRecName? declName then
        return .done (.const safeDeclName us)
      else
        return .done e
    | _ => return .continue

/--
Honor @[macro_inline] directives and inline auxiliary matchers.
This is lifted from LCNF/ToDecl.lean .
It processes the whole expression tree, so the code here doesn't have to be at the start of visitExpr,
and it is sufficient to run it before entering the "toplevel" expression and the definition of a dependency in the environment.
-/
def prepare_erasure (e: Expr): EraseM Expr := do
  let mut e := e
  e ← replaceUnsafeRecNames e
  e ← macroInline e
  e ← inlineMatchers e
  -- According to the comment in ToDecl.lean, inlined matchers might contain occurrences of `ite` and `dite`.
  -- I'm sort of assuming that inlining matchers doesn't expose arbitrary macro_inline stuff which might itself contain more matchers etc.
  -- Just `ite` and `dite` are fine, their bodies are just a Decidable.casesOn.
  -- It's important to inline them because otherwise both arms of the conditional will be strictly evaluated.
  e ← macroInline e
  if (← read).config.csimp then
    -- This has to be done after _unsafe_rec name replacement.
    e := Compiler.CSimp.replaceConstants (← getEnv) e
  pure e

/--
Copied over from toLCNF, then quite heavily pruned and modified.

This not only erases the expression but also gives a context with all necessary global declarations of inductive types and top-level constants.
-/
partial def erase (e : Expr) (config: ErasureConfig): CoreM program := do
  let (t, s) ← run (do visitExpr (← prepare_erasure e)) config
  return (s.gdecls, t)

where
  /- Proofs (terms whose type is of type Prop) and type formers/predicates are all erased. -/
  visitExpr (e : Expr) : EraseM neterm := do
    if (← isErasable e) then
      return .box
    match e with
    | .app ..      => visitApp e
    | .const ..    => visitApp e -- treat as an application to zero args to handle special constants
    | .proj s i e  => visitProj s i e
    | .mdata _ e   => visitExpr e -- metadata is ignored
    | .lam ..      => visitLambda e
    | .letE ..     => visitLet e
    | .lit l     => visitLiteral l
    | .fvar fvarId => pure (.fvar fvarId)
    | .forallE .. | .mvar .. | .bvar .. | .sort ..  => unreachable!

  visitLiteral (l: Literal): EraseM neterm := do
    match (← read).config.nat, l with
    | .peano, .natVal 0 => visitConstructor ``Nat.zero #[]
    | .peano, .natVal (n+1) => visitConstructor ``Nat.succ #[.lit (.natVal n)]
    | .machine, .natVal n =>
      if n <= BitVec.intMax 63 then
        pure <| .prim ⟨.primInt, n⟩ 
      else
        panic! "Nat literal not representable as a 63-bit signed integer."
    | _, .strVal _ => panic! "string literals not supported"

  /-
  The original in ToLCNF also handles eta-reduction of implicit lambdas introduced by the elaborator.
  This is beyond the scope of what I want to do here for the moment.
  -/
  visitLambda (e : Expr) : EraseM neterm :=
    lambdaMonocular e (fun fvarid body => do mkLambda fvarid (← visitExpr body))

  visitLet (e : Expr): EraseM neterm :=
    /-
    In the original ToLCNF, if the bound value is erasable then the let-binding is not generated,
    since all occurrences of the variable must be erased anyway.
    Keep this optimization?
    -/
    letMonocular e (fun fvarid val body => do mkLetIn fvarid (← visitExpr val) (← visitExpr body))

  visitProj (s : Name) (i : Nat) (e : Expr) : EraseM neterm := do
    let .inductInfo indinfo ← getConstInfo s | unreachable!
    let projinfo: projectioninfo := { ind_type := ← to_inductive_id indinfo, param_count := indinfo.numParams, field_idx := i }
    return .proj projinfo (← visitExpr e)

  /--
  When visiting expressions of the form f g, it is not sufficient to just recurse on f and g.
  visitApp will explore an expression "in depth" to get the leftmost applicand and handle:
  - converting applications marked as let_fun back into actual let bindings
  - applications of constants
  Contrary to the original ToLCNF, I have removed CSimp.replaceConstants here and assume it will just be run once before erasure.
  -/
  visitApp (e : Expr) : EraseM neterm :=
    -- Compile let_fun as let-expressions, not functions
    if let some (args, n, t, v, b) := e.letFunAppArgs? then
      visitExpr <| mkAppN (.letE n t v b (nonDep := true)) args
    -- The applicand is a constant, check for special cases
    else if let .const .. := e.getAppFn then
      visitConstApp e
    -- The applicand is not a constant, so we just normally recurse.
    else
      e.withApp fun f args => do visitAppArgs (← visitExpr f) args

  /-- A constant which is being defined in the current mutual block will be replaced with a free variable (to be bound by mkDef later).
  Other constants should previously have been added to the (λbox-side) context and will just be translated to Rocq kernames. -/
  visitConst (e: Expr): EraseM neterm := do
    let .const declName _ := e | unreachable!
    if let .some id := (← read).fixvars.bind (fun hmap => hmap[declName]?) then
      return .fvar id
    return .const (← get_constant_kername declName)
    
  /--
  Special handling of
  - casesOn (will be eta-expanded)
  -constructors (will be eta-expanded)
  - structure projection functions (will be inlined with their definition, except for runtime builtin types)
  Since noConfusion principles are just defined, I think it's ok to not handle them specially.
  Check visitNoConfusion in the original ToLCNF, which seems to do quite limited things.
  -/
  visitConstApp (e: Expr): EraseM neterm :=
    e.withApp fun f args => do
      let .const declName _ := f | unreachable!
      if let some casesInfo ← getCasesInfo? declName then
        /-
        I have removed the check for whether there is an [implemented_by] annotation.
        TODO: These probably should be handled somewhere before erasure.
        -/
        withAppEtaToMinArity e casesInfo.arity (fun _ args => visitCases casesInfo args)
      else if let some arity ← getCtorArity? declName then
        withAppEtaToMinArity e arity (fun _ args => visitConstructor declName args)
      else if let some projInfo ← getProjectionFnInfo? declName then
        visitProjFn projInfo e
      else
        visitAppArgs (← visitConst f) args

  visitConstructor (ctorname: Name) (args: Array Expr): EraseM neterm := do
    if isExtern (← getEnv) ctorname && (← read).config.extern == .preferAxiom then
      addAxiom ctorname
      return ← visitAppArgs (.const <| to_kername ctorname) args

    match (← read).config.nat, ctorname with
    | .machine, ``Nat.zero =>
      unless args.size == 0 do
        panic s!"Nat.zero applied to {args.size} arguments."
      return ← visitLiteral (.natVal 0)
    | .machine, ``Nat.succ =>
      unless args.size == 1 do
        panic s!"Nat.succ applied to {args.size} arguments."
      let nat_add ← visitConst (.const ``Nat.add [])
      return ← visitAppArgs nat_add #[args[0]!, .lit (.natVal 1)]
    | .machine, _
    | .peano, _ => pure ()

    let .ctorInfo info ← getConstInfo ctorname | unreachable!
    let idx := info.cidx
    let .inductInfo indinfo ← getConstInfo info.induct | unreachable!
    let indid ← to_inductive_id indinfo
    -- Instead of making this a "real" use of .construct, in the stage of λbox I am targeting constructor application is function application
    visitAppArgs (.construct indid idx []) args

  /--
  Automatically defined projection functions out of structures are inlined,
  unless the projection is out of a builtin type of the runtime.
  The definition seems to just be def spam.egg := fun s: spam => s.1,
  so after β-reduction this becomes a primitive projection.
  -/
  visitProjFn (projInfo : ProjectionFunctionInfo) (e : Expr) : EraseM neterm :=
    e.withApp fun f args => do
      let typeName := projInfo.ctorName.getPrefix
      if isRuntimeBultinType typeName then
        panic! "The Lean compiler does something special here but I don't know how to handle this case."
      else
        let .const declName us := f | unreachable!
        let info ← getConstInfo declName
        let f ← Core.instantiateValueLevelParams info us
        visitExpr (f.beta args)

  /-- Normal application of a function to some arguments. -/
  visitAppArgs (f : neterm) (args : Array Expr) : EraseM neterm := do
      args.foldlM (fun e arg => do return neterm.app e (← visitExpr arg)) f

  visitCases (casesInfo : CasesInfo) (args: Array Expr) : EraseM neterm := do
    let discr_nt ← visitExpr args[casesInfo.discrPos]!
    let typeName := casesInfo.declName.getPrefix
    
    -- If we are using machine Nats then the inductive casesOn will not work.
    let mut ret: neterm ← (match typeName, (← read).config.nat with
    | ``Int, .machine => panic! "Int.casesOn not implemented."
    | ``Nat, .machine => do
      /-
      Compile this to "let n = discr in Bool.casesOn (Nat.beq n 0) (succ_case (n - 1)) zero_case".
      The let-binding is necessary to avoid double evaluation of the discriminee.
      I'm doing part of this this on neterms instead of constructing Exprs because visitExpr
      assumes expressions are well-typed, which wouldn't be the case naïvely as (n - 1).succ is not defeq to n.
      Using casts to make the dependent types typecheck is not an option,
      because those explicitly use the recursor Eq.req which I am not special-casing at the moment.
      -/
      let zero_arm := args[casesInfo.altsRange.start]!
      let zero_nt ← visitExpr zero_arm
      let succ_arm := args[casesInfo.altsRange.start + 1]! -- a function with one argument of type Nat
      let bool_indval := (← getConstInfo ``Bool).inductiveVal!
      withLocalDecl `n (.const ``Nat []) .default (fun n_fvar => do
        let gtz_arm := Expr.app succ_arm <| mkAppN (.const ``Nat.sub []) #[.fvar n_fvar, .lit (.natVal 1)] -- no longer takes an argument, n_fvar is free here
        let gtz_nt: neterm ← visitExpr gtz_arm
        let condition: neterm ← visitExpr <| mkAppN (.const ``Nat.beq []) #[.fvar n_fvar, .lit (.natVal 0)]
        let case_nt ← mkCase bool_indval condition [← mkAlt [] gtz_nt, ← mkAlt [] zero_nt]
        mkLetIn n_fvar discr_nt case_nt
      )
    | _, _ => do
      let .inductInfo indVal ← getConstInfo typeName | unreachable!
      let mut alts := #[]
      for i in casesInfo.altsRange, numFields in casesInfo.altNumParams do
        let alt ← visitAlt numFields args[i]!
        alts := alts.push alt
      mkCase indVal discr_nt alts.toList
    )

    -- The casesOn function may be overapplied, so handle the extra arguments.
    for arg in args[casesInfo.arity:] do
      ret := .app ret (← visitExpr arg)
    return ret

  /--
  Visit a `matcher`/`casesOn` alternative.
  On the Lean side, e should be a function taking numFields arguments.
  For λbox, I think we only need the body, as the neterm.cases constructor includes the bindings.
  -/
  visitAlt (numFields : Nat) (e : Expr) : EraseM (List ppname × neterm) := do
    lambdaOrIntroToArity e (← liftMetaM <| Meta.inferType e) numFields fun e fvarids => do
      mkAlt (fvarids.toList) (← visitExpr e)

  get_constant_kername (n: Name): EraseM kername := do
    if let .some kn := (← get).constants.get? n then
      return kn
    else
     visitMutual n
     return (← get).constants[n]!

  /--
  Add all the declarations in the Lean-side mutual block of `name` to the global_declarations,
  and add their mappings to kernames to the erasure state.
  -/
  visitMutual (name: Name): EraseM Unit := do
    -- Use original recursive definition, not the elaborated one with recursors, if available.
    let ci := (← Compiler.LCNF.getDeclInfo? name).get!
    let names := ci.all -- possibly these are ._unsafe_rec
    let single_decl := names.length == 1
    -- A single declaration may have to be output as an axiom.
    if single_decl then
      match ci.value? (allowOpaque := true), isExtern (← getEnv) name, (← read).config.extern with
      | .none, _, _ =>
        logInfo s!"No value found for name {name}."
        return ← addAxiom name
      | .some _, false, _ => pure ()
      | .some _, true, .preferAxiom =>
        logInfo s!"Name {name} has a value but is tagged @[extern]."
        return ← addAxiom name
      | .some _, true, .preferLogical =>
        logInfo s!"Name {name} is tagged @[extern] but has a value, using value."
        pure ()

    let nonrecursive: Bool := single_decl && !(name_occurs name (ci.value! (allowOpaque := true)))
    if nonrecursive
    then -- translate into a single nonrecursive constant declaration
      let e: Expr := ci.value! (allowOpaque := true)
      let t: neterm ← visitExpr (← prepare_erasure e)
      let kn := to_kername name
      modify (fun s => { s with constants := s.constants.insert name kn, gdecls := s.gdecls.cons (kn, .ConstantDecl <| ⟨.some t⟩) })
    else -- translate into a mutual fixpoint declaration
      let ids ← names.mapM (fun _ => mkFreshFVarId)
      let fixvarnames := names.map remove_unsafe_rec
      withReader (fun env => { env with fixvars := fixvarnames |>.zip ids |> Std.HashMap.ofList |> .some }) do
        let defs: List edef ← names.mapM (fun n => do
          let ci ← getConstInfo n -- here n is directly from the above ci.all, possibly _unsafe_rec
          let e: Expr := ci.value! (allowOpaque := true)
          -- TODO: eta-expand fixpoints? (I think this must be done, unsure how far)
          let t: neterm ← visitExpr (← prepare_erasure e)
          mkDef (remove_unsafe_rec n) fixvarnames t
        )
        for (n, i) in fixvarnames.zipIdx do
          let kn := to_kername n
          modify (fun s => { s with constants := s.constants.insert n kn, gdecls := s.gdecls.cons (kn, .ConstantDecl ⟨.some <| .fix defs i⟩) })

inductive MLType: Type where
  | arrow (a b: MLType)
  | Z
  | unit
  | bool
deriving Inhabited

def MLType.toString: MLType -> String
  | arrow a b => s!"{toStringProtected a} -> {b.toString}"
  | Z => "Z.t"
  | unit => "unit"
  | bool => "bool"
where
  toStringProtected: MLType -> String
  | arrow a b => s!"({toStringProtected a} -> {b.toString})"
  | Z => "Z.t"
  | unit => "unit"
  | bool => "bool"

instance : ToString MLType := ⟨MLType.toString⟩

partial def to_ml_type (ty: Expr): MetaM MLType :=
  Meta.forallTelescopeReducing ty fun vars body => do
    let vartypes ← vars.mapM Meta.inferType
    let varmltypes ← vartypes.mapM to_ml_type
    let bodymltype := match (← Meta.whnf body) with
    | .const `Nat _ => .Z
    | .const `Unit _ | .const `PUnit _ => .unit
    | .const `Bool _ => .bool
    | t => panic! s!"failed to translate {t} into ML type"
    return varmltypes.foldr .arrow bodymltype

def gen_mli (ty: Expr): MetaM String := do return s!"val main: {← to_ml_type ty}"

syntax (name := erasestx) "#erase" ppSpace term (ppSpace "config" term)? (ppSpace "to" ppSpace str)? (ppSpace "mli" ppSpace str)?: command

@[command_elab erasestx]
def eraseElab: Elab.Command.CommandElab
  | `(command| #erase $t:term $[config $cfg?:term]? $[to $path?:str]? $[mli $mli?:str]?) => Elab.Command.liftTermElabM do
    let e: Expr ← Elab.Term.elabTerm t (expectedType? := .none)
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Lean.instantiateMVars e

    let cfg: ErasureConfig ← match cfg? with
    | .none => pure {}
    | .some cfg => unsafe Elab.Term.evalTerm ErasureConfig (.const ``Erasure.ErasureConfig []) cfg

    let p: program ← erase e cfg
    let s: String := p |> Serialize.to_sexpr |>.toString
    match path? with
    | .some path => do
        IO.FS.writeFile path.getString s
    | .none => logInfo s

    let ty: Expr ← Meta.inferType e
    let mlistr ← gen_mli ty
    match mli? with
    | .none => logInfo mlistr
    | .some mlipath => IO.FS.writeFile mlipath.getString mlistr

  | _ => Elab.throwUnsupportedSyntax

end Erasure
