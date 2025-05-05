import Lean

open Lean (Name FVarId InductiveVal)

def todo! {α} [Inhabited α]: α := unreachable!

abbrev ident := String
abbrev dirpath := List String

inductive modpath where
| MPfile  (dp : dirpath)
| MPdot   (mp : modpath) (id : ident)
-- Removed MPBound because I still don't know what a functor is in OCaml-like module systems.
deriving BEq, Inhabited

/--
Mimicing MetaRocq kernames.
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
  principal_arg_idx: Nat 
  deriving BEq, Inhabited

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

-- TODO: Have this return a result in EraseM and get the binder name from context?
def fvar_to_name (x: FVarId): ppname := .named x.name.toString

def mkLambda (x: FVarId) (body: neterm): neterm := .lambda (fvar_to_name x) (abstract x body)

def mkLetIn (x: FVarId) (val body: neterm): neterm := .letIn (fvar_to_name x) val (abstract x body)

/--
In Rocq it is mutual blocks which are named, so I'm just making something up here.
-/
def to_inductive_id (indinfo: InductiveVal): inductive_id :=
  let idx := indinfo.all.findIdx? (. = indinfo.name) |>.get!
  let mutual_block_name := indinfo.all |>.map toString |> String.join |> root_kername
  { mutual_block_name, idx }

/-- Maybe I want this to be reversed, idk -/
def mkAlt (xs: List FVarId) (body: neterm): List ppname × neterm := Id.run do
  let mut body := body
  let names := xs.map fvar_to_name
  for (fvarid, i) in xs.reverse.zipIdx do
    body := toBvar fvarid i body
  return (names, body)

def mkCase (indInfo: InductiveVal) (discr: neterm) (alts: List (List ppname × neterm)): neterm :=
  .case (to_inductive_id indInfo, indInfo.numParams) discr alts
