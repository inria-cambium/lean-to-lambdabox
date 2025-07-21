import Lean

open Lean (Name FVarId InductiveVal)

abbrev ident := String
abbrev dirpath := List String

inductive modpath where
| MPfile  (dp : dirpath)
| MPdot   (mp : modpath) (id : ident)
-- Removed MPBound because I still don't know what a functor is in OCaml-like module systems.
deriving Inhabited, Repr

/--
Mimicking MetaRocq kernames.
-/
structure kername where
  mp: modpath
  id: ident
deriving Inhabited, Repr

def to_modpath (n: Name): modpath :=
  match n with
  | .str name s => .MPdot (to_modpath name) s
  | .num name nb => .MPdot (to_modpath name) (nb.repr)
  | .anonymous => .MPfile []

/-- Clean up a string potentially coming from Lean's very permissive grammar to only use characters valid in OCaml identifiers. -/
def cleanIdent (s : String) : String :=
  let escapeChar (c : Char) : String :=
    if c.isAlphanum || c == '_' then toString c
    else "_u" ++ toString c.toNat

  s.toList.map escapeChar |> String.join
/--
Ad hoc conversion function from `Name`s to MetaRocq kernames.
-/
def to_kername (n: Name): kername :=
  match n with
  | .str name s =>  { mp := to_modpath name, id := cleanIdent s }
  | .num name nb =>  { mp := to_modpath name, id := nb.repr }
  | .anonymous =>  panic! "Cannot convert empty name to kername." -- This should not happen.

def root_kername (s: String): kername :=
  { mp := .MPfile [], id := cleanIdent s }

/-- A name used to pretty-print bound variables. -/
inductive ppname: Type where
  | named (s: String)
  | anon
  deriving Inhabited, Repr

structure inductive_id where
  mutual_block_name: kername
  /-- Which of the mutually inductive types defined in this block is used here? -/
  idx: Nat
  deriving Inhabited, Repr

structure projectioninfo where
  ind_type: inductive_id 
  param_count: Nat
  field_idx: Nat
  deriving Inhabited, Repr

structure edef {term: Type} where
  name: ppname
  /-- The body typically (necessarily?) starts with a certain number (at least rarg + 1) of lambda constructor applications, one for each argument. -/
  body: term
  /-- Principal/structural argument for recursion. -/
  principal_arg_idx: Nat := 0 -- this doesn't matter computationally and is just needed in the proof of correctness, so it's safe to let this be 0
  deriving Inhabited, Repr

inductive prim_tag where
  | primInt
  /- Rocq has these, but I'm not supporting them for the moment.
  | primFloat
  | primArray
  -/
deriving Repr

/--
In MetaRocq they need to do something fancy to keep positivity because there everything is parametrized by the type of terms.
Since I don't handle arrays for now there's no need for that.
--/
abbrev prim_model: prim_tag -> Type
  | .primInt => BitVec 63

abbrev prim_val: Type := Σ t: prim_tag, prim_model t

/--
Basically `term` as defined in `MetaRocq/Erasure/EAst.v`, with an extra constructor `.fvar` to mimic Lean's locally nameless representation.
This is very useful when using the standard API to navigate Lean expressions and build a `LBTerm`.
-/
inductive LBTerm where
  | box: LBTerm
  /-- A bound variable, accessed as a de Bruijn index. -/
  | bvar: Nat -> LBTerm
  | fvar: FVarId -> LBTerm
  | lambda: ppname -> LBTerm -> LBTerm
  | letIn: ppname -> LBTerm -> LBTerm -> LBTerm
  | app: LBTerm -> LBTerm -> LBTerm
  /-- A constant living in the environment. -/
  | const: kername -> LBTerm
  | construct: inductive_id -> Nat /- index in the mutual block of the constructor used -/ -> List LBTerm -> LBTerm
  | case: (inductive_id × Nat /- number of parameters, maybe redundant -/) -> LBTerm -> List (List ppname × LBTerm) -> LBTerm
  | proj: projectioninfo -> LBTerm -> LBTerm
  /-- Define some number of mutually inductive functions, then access one. -/
  | fix: List (@edef LBTerm) -> Nat /- index of the one mutually defined function we want to access -/ -> LBTerm
  | prim: prim_val -> LBTerm
  deriving Inhabited, Repr

/-- This is actually structurally recursive, I think, Lean just has trouble seeing it. -/
partial def toBvar (x: FVarId) (lvl: Nat) (e: LBTerm): LBTerm :=
  match e with
  | .box => .box
  | .bvar i => .bvar i
  | .fvar y => if y == x then .bvar lvl else .fvar y
  | .lambda name body => .lambda name (toBvar x (lvl + 1) body)
  | .letIn name val body => .letIn name (toBvar x lvl val) (toBvar x (lvl + 1) body)
  | .app a b => .app (toBvar x lvl a) (toBvar x lvl b)
  | .const kn => .const kn
  | .construct indid n args => .construct indid n (args.map <| toBvar x lvl)
  | .case (indid, n) discr alts => .case (indid, n) (toBvar x lvl discr) (alts.map fun (names, alt) => (names, toBvar x (lvl + names.length) alt))
  | .proj pinfo e => .proj pinfo (toBvar x lvl e)
  | .fix defs i =>
    let def_count := defs.length;
    .fix (defs.map fun nd => { nd with body := toBvar x (lvl + def_count) nd.body }) i
  | .prim p => .prim p

def abstract (x: FVarId) (e: LBTerm): LBTerm := toBvar x 0 e

structure constructor_body where
  cstr_name: ident
  cstr_nargs: Nat
deriving Inhabited, Repr

-- should be unused
structure projection_body where
  proj_name: ident
deriving Repr

inductive allowed_eliminations where
  | IntoSProp
  | IntoPropSProp
  | IntoSetPropSProp
  | IntoAny
deriving Inhabited, Repr

structure one_inductive_body where
  ind_name : ident
  /-- True iff the inductive lives in Prop. -/
  ind_propositional : Bool := false -- I think, since erasure should remove anything which ends up in Prop
  /-- Allowed eliminations. -/
  ind_kelim : allowed_eliminations := .IntoAny -- I think, but this shouldn't matter
  ind_ctors : List constructor_body
  ind_projs : List projection_body -- This is only about giving user-visible names to projections, but `lbox` complains about wellformedness if it is empty.
deriving Inhabited, Repr

inductive recursivity_kind where
  | Finite
  | CoFinite -- Lean doesn't have primitive coinductive types, but including this here anyway to match the MetaCoq side.
  | BiFinite
deriving Repr

structure mutual_inductive_body where
  ind_finite : recursivity_kind := .Finite
  ind_npars : Nat
  ind_bodies : List one_inductive_body
deriving Repr

structure constant_body where
  cst_body: Option LBTerm
deriving Repr

inductive global_decl where
  | ConstantDecl (body: constant_body)
  | InductiveDecl (body: mutual_inductive_body)
deriving Repr

-- The first declarations to be added to the context are the deepest/first-consed in the list.
abbrev global_declarations := List (kername × global_decl)
abbrev program: Type := global_declarations × LBTerm
