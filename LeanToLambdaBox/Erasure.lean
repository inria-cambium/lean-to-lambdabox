import Lean.Compiler.LCNF.ToLCNF
import Lean.Meta

import LeanToLambdaBox.Basic
import LeanToLambdaBox.Printing

open Lean
open Lean.Compiler.LCNF

namespace Erasure

/-- The monad in ToLCNF has caches, a local context and toAny as a set of fvars, all as mutable state for some reason.
    Here I just have a read-only local context, in order to be able to use MetaM's type inference, and keep the complexity low.
    If this is much too slow, try caching stuff again.
    Why not do this straight-up in MetaM?
    -/
abbrev EraseM := ReaderT LocalContext CoreM

def run (x : EraseM α) : CoreM α :=
  x |>.run {}

def fvar_to_name (x: FVarId): EraseM ppname := do
  let n := (← read).fvarIdToDecl |>.find! x |>.userName
  return .named n.toString

def mkLambda (x: FVarId) (body: neterm): EraseM neterm := do return .lambda (← fvar_to_name x) (abstract x body)

def mkLetIn (x: FVarId) (val body: neterm): EraseM neterm := do return .letIn (← fvar_to_name x) val (abstract x body)

/--
In Rocq it is mutual blocks which are named, so I'm just making something up here.
-/
def to_inductive_id (indinfo: InductiveVal): inductive_id :=
  let idx := indinfo.all.findIdx? (. = indinfo.name) |>.get!
  let mutual_block_name := indinfo.all |>.map toString |> String.join |> root_kername
  { mutual_block_name, idx }

/-- Maybe I want this to be reversed, idk -/
def mkAlt (xs: List FVarId) (body: neterm): EraseM (List ppname × neterm) := do
  let mut body := body
  let names ← xs.mapM fvar_to_name
  for (fvarid, i) in xs.reverse.zipIdx do
    body := toBvar fvarid i body
  return (names, body)

def mkCase (indInfo: InductiveVal) (discr: neterm) (alts: List (List ppname × neterm)): neterm :=
  .case (to_inductive_id indInfo, indInfo.numParams) discr alts

/-- Run an action of MetaM in EraseM using EraseM's local context of Lean types. -/
@[inline] def liftMetaM (x : MetaM α) : EraseM α := do
  x.run' { lctx := ← read }

/-- Similar to Meta.withLocalDecl, but in EraseM.
    k will be passed some fresh FVarId and run in a context in which it is bound. -/
def withLocalDecl (n: Name) (type: Expr) (bi: BinderInfo) (k: FVarId -> EraseM α): EraseM α := do
  let fvarid <- mkFreshFVarId;
  withReader (fun lctx => lctx.mkLocalDecl fvarid n type bi) (k fvarid)

/-- Like Meta.withLetDecl. -/
def withLocalDef (n: Name) (type val: Expr) (nd: Bool) (k: FVarId -> EraseM α): EraseM α := do
  let fvarid <- mkFreshFVarId;
  withReader (fun lctx => lctx.mkLetDecl fvarid n type val nd) (k fvarid)

/--
A version of Meta.lambdaTelescope that
- unpacks exactly one layer of lambda-abstraction (ie does not telescope)
- works in PrepareM instead of (any monad from which we can control) MetaM.
- yields an FVarId instead of an Expr for the bound variable
Panics if applied to something which is not of the form .lambda ..
-/
def lambdaMonocular {α} [Inhabited α] (e: Expr) (k: FVarId -> Expr -> EraseM α): EraseM α := do
  let .lam binderName type body bi := e | unreachable!
  withLocalDecl binderName type bi (fun fvarid => k fvarid <| body.instantiate #[.fvar fvarid])
/-- Destructures a let-expression for handling by a continuation in an appropriate context. The continuation gets an FVarId for the bound variable and bound value and body as expressions. Panics if applied to an expression which is not of the form .letE ..
-/
def letMonocular {α} [Inhabited α] (e: Expr) (k: FVarId -> Expr -> Expr -> EraseM α): EraseM α := do
  let .letE binderName type val body nd := e | unreachable!
  withLocalDef binderName type val nd (fun fvarid => k fvarid val (body.instantiate #[.fvar fvarid]))

/--
Destructures a type expression of the form `∀ a: A, B`,
running the continuation on the body B (with DB variable 0 suitably instantiated with some fvar `a`) and the bound fvar,
in a context with `a: A`.
Panics if applied to an expression which is not of the form .forallE ..
-/
def forallMonocular {α} [Inhabited α] (t: Expr) (k: FVarId -> Expr -> EraseM α) := do
  let Expr.forallE binderName type body bi := t | unreachable!
  withLocalDecl binderName type bi (fun fvarid => k fvarid <| body.instantiate #[.fvar fvarid])

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
      k (body.instantiate #[.fvar fvarid]) bodytype fvarid
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

/-
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
    -- TODO: ToLCNF includes an explicit check for isLcProof, but I think the type information should be enough to erase those.
    let type ← Meta.inferType e
    -- Erase evidence of propositions
    if (← Meta.isProp type) then
      return true
    -- Erase types and type formers
    if (← Meta.isTypeFormerType type) then
      return true
    return false

/--
Copied over from toLCNF, then quite heavily pruned and modified.
-/
partial def erase_term (e : Expr) : CoreM neterm :=
  run (visit e)
where
  /- Proofs (terms whose type is of type Prop) and type formers/predicates are all erased. -/
  visit (e : Expr) : EraseM neterm := do
    if (← isErasable e) then
      return .box
    match e with
    | .app ..      => visitApp e
    | .const ..    => visitApp e -- treat as an application to zero args to handle special constants
    | .proj s i e  => visitProj s i e
    | .mdata _ e   => visit e -- metadata is ignored
    | .lam ..      => visitLambda e
    | .letE ..     => visitLet e
    | .lit _     => todo! -- Literals unsupported for now. Add support for at least nat?
    | .fvar fvarId => pure (.fvar fvarId)
    | .forallE .. | .mvar .. | .bvar .. | .sort ..  => unreachable!

  /-
  The original in ToLCNF also handles eta-reduction of implicit lambdas introduced by the elaborator.
  This is beyond the scope of what I want to do here for the moment.
  -/
  visitLambda (e : Expr) : EraseM neterm :=
    lambdaMonocular e (fun fvarid body => do mkLambda fvarid (← visit body))

  visitLet (e : Expr): EraseM neterm :=
    /-
    In the original ToLCNF, if the bound value is erasable then the let-binding is not generated,
    since all occurrences of the variable must be erased anyway.
    Keep this optimization?
    -/
    letMonocular e (fun fvarid val body => do mkLetIn fvarid (← visit val) (← visit body))

  visitProj (s : Name) (i : Nat) (e : Expr) : EraseM neterm := do
    let .inductInfo indinfo ← getConstInfo s | unreachable!
    let projinfo: projectioninfo := { ind_type := to_inductive_id indinfo, param_count := indinfo.numParams, field_idx := i }
    return .proj projinfo (← visit e)

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
      visit <| mkAppN (.letE n t v b (nonDep := true)) args
    -- The applicand is a constant, check for special cases
    else if let .const .. := e.getAppFn then
      visitConstApp e
    -- The applicand is not a constant, so we just normally recurse.
    else
      e.withApp fun f args => do visitAppArgs (← visit f) args

  /-- Constants which are not special will just be translated to Rocq kernames. -/
  visitConst (e: Expr): EraseM neterm := do
    let .const declName _ := e | unreachable!
    return .const (to_kername declName)
    
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
    let .ctorInfo info ← getConstInfo ctorname | unreachable!
    let idx := info.cidx
    let .inductInfo indinfo ← getConstInfo info.induct | unreachable!
    let indid := to_inductive_id indinfo
    return .construct indid idx (← args.toList.mapM visit)

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
        let arity := projInfo.numParams + 1
        withAppEtaToMinArity e arity (fun f args => do visitAppArgs (← visitConst f) args)
      else
        let .const declName us := f | unreachable!
        let info ← getConstInfo declName
        let f ← Core.instantiateValueLevelParams info us
        visit (f.beta args)

  /-- Normal application of a function to some arguments. -/
  visitAppArgs (f : neterm) (args : Array Expr) : EraseM neterm := do
    -- This is a minor optimization (already β-reducing applications of □). Keep it or not?
    /-
    if let .box := f then
      return .box
    else
    -/
      args.foldlM (fun e arg => do return neterm.app e (← visit arg)) f

  visitCases (casesInfo : CasesInfo) (args: Array Expr) : EraseM neterm := do
    let mut alts := #[]
    let typeName := casesInfo.declName.getPrefix
    let discr ← visit args[casesInfo.discrPos]!
    let .inductInfo indVal ← getConstInfo typeName | unreachable!
    for i in casesInfo.altsRange, numFields in casesInfo.altNumParams do
      let alt ← visitAlt numFields args[i]!
      alts := alts.push alt
    let mut ret := mkCase indVal discr alts.toList
    -- The casesOn function may be overapplied, so handle the extra arguments.
    for arg in args[casesInfo.arity:] do
      ret := .app ret (← visit arg)
    return ret

  /--
  Visit a `matcher`/`casesOn` alternative.
  On the Lean side, e should be a function taking numFields arguments.
  For λbox, I think we only need the body, as the neterm.cases constructor includes the bindings.
  -/
  visitAlt (numFields : Nat) (e : Expr) : EraseM (List ppname × neterm) := do
    lambdaOrIntroToArity e (← liftMetaM <| Meta.inferType e) numFields fun e fvarids => do
      mkAlt (fvarids.toList) (← visit e)

elab "#erase_term" t:term : command => Elab.Command.liftTermElabM do
  let e: Expr ← t |> Elab.Term.elabTerm (expectedType? := .none)
  let nt: neterm ← erase_term e
  let s: String := nt |> Serialize.to_sexpr |>.toString
  logInfo s

end Erasure
