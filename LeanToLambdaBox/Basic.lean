import Lean

open Lean (Name FVarId InductiveVal)

abbrev ident := String
abbrev dirpath := List String

inductive modpath where
| MPfile  (dp : dirpath)
| MPdot   (mp : modpath) (id : ident)
-- Removed MPBound because I still don't know what a functor is in OCaml-like module systems.
deriving BEq, Inhabited

/--
Mimicking MetaRocq kernames.
-/
structure kername where
  mp: modpath
  id: ident
deriving BEq, Inhabited

def to_modpath (n: Name): modpath :=
  match n with
  | .str name s => .MPdot (to_modpath name) s
  | .num name nb => .MPdot (to_modpath name) (nb.repr)
  | .anonymous => .MPfile []

/--
Ad hoc conversion function from `Name`s to MetaRocq kernames.
-/
def to_kername (n: Name): kername :=
  match n with
  | .str name s =>  { mp := to_modpath name, id := s }
  | .num name nb =>  { mp := to_modpath name, id := nb.repr }
  | .anonymous =>  unreachable! -- This should not happen.

def root_kername (s: String): kername :=
  { mp := .MPfile [], id := s }

/-- A name used to pretty-print bound variables. -/
inductive ppname: Type where
  | named (s: String)
  | anon
  deriving BEq, Inhabited

structure inductive_id where
  mutual_block_name: kername
  /-- Which of the mutually inductive types defined in this block is used here? -/
  idx: Nat
  deriving BEq, Inhabited

structure projectioninfo where
  ind_type: inductive_id 
  param_count: Nat
  field_idx: Nat
  deriving BEq, Inhabited

structure edef {term: Type} where
  name: ppname
  /-- The body typically (necessarily?) starts with a certain number (at least rarg + 1) of lambda constructor applications, one for each argument. -/
  body: term
  /-- Principal/structural argument for recursion. -/
  principal_arg_idx: Nat := 0 -- this doesn't matter computationally and is just needed in the proof of correctness, so it's safe to let this be 0
  deriving BEq, Inhabited

/--
Basically `term` as defined in `MetaRocq/Erasure/EAst.v`, with an extra constructor `.fvar` to mimic Lean's locally nameless representation.
This is very useful when using the standard API to navigate Lean expressions and build a `neterm`.
-/
inductive neterm where
  | box: neterm
  /-- A bound variable, accessed as a de Bruijn index. -/
  | bvar: Nat -> neterm
  | fvar: FVarId -> neterm
  | lambda: ppname -> neterm -> neterm
  | letIn: ppname -> neterm -> neterm -> neterm
  | app: neterm -> neterm -> neterm
  /-- A constant living in the environment. -/
  | const: kername -> neterm
  | construct: inductive_id -> Nat /- index of the constructor used -/ -> List neterm -> neterm
  | case: (inductive_id × Nat /- number of parameters, maybe redundant -/) -> neterm -> List (List ppname × neterm) -> neterm
  | proj: projectioninfo -> neterm -> neterm
  /-- Define some number of mutually inductive functions, then access one. -/
  | fix: List (@edef neterm) -> Nat /- index of the one mutually defined function we want to access -/ -> neterm
  deriving BEq, Inhabited

/-- This is actually structurally recursive, I think, Lean just has trouble seeing it. -/
partial def toBvar (x: FVarId) (lvl: Nat) (e: neterm): neterm :=
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

def abstract (x: FVarId) (e: neterm): neterm := toBvar x 0 e

structure constructor_body where
  cstr_name: ident
  cstr_nargs: Nat
deriving Inhabited

-- should be unused
structure projection_body where
  proj_name: ident

inductive allowed_eliminations where
  | IntoSProp
  | IntoPropSProp
  | IntoSetPropSProp
  | IntoAny
deriving Inhabited

structure one_inductive_body where
  ind_name : ident
  /-- True iff the inductive lives in Prop. -/
  ind_propositional : Bool := false -- I think, since erasure should remove anything which ends up in Prop
  /-- Allowed eliminations. -/
  ind_kelim : allowed_eliminations := .IntoAny -- I think, but this shouldn't matter
  ind_ctors : List constructor_body
  ind_projs : List projection_body -- This is only about giving user-visible names to projections, but `lbox` complains about wellformedness if it is empty.
deriving Inhabited

inductive recursivity_kind where
  | Finite
  | CoFinite -- Lean doesn't have primitive coinductive types, but including this here anyway to match the MetaCoq side.
  | BiFinite

structure mutual_inductive_body where
  ind_finite : recursivity_kind := .Finite
  ind_npars : Nat
  ind_bodies : List one_inductive_body

structure constant_body where
  cst_body: Option neterm

inductive global_decl where
  | ConstantDecl (body: constant_body)
  | InductiveDecl (body: mutual_inductive_body)

-- The first declarations to be added to the context are the deepest/first-consed in the list.
abbrev global_declarations := List (kername × global_decl)
abbrev program: Type := global_declarations × neterm
