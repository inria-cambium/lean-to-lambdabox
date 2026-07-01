import LeanToLambdaBox.Basic

/-!
# de Bruijn substitution kit for λ□ terms

The environment lookup and the shift/substitution operations on `LBTerm`, shared
by every layer that reasons about λ□ reduction (`WcbvEval`, `LBOptimize`, the
`Erases` substitution lemmas, and the legacy small-step relation).

The conventions here **match lean4lean's `Expr.liftLooseBVars'`/`instantiate1'`**
(`shift d cutoff ≡ liftLooseBVars' · cutoff d`, `subst ≡ instantiate1'`), which is
what lets `erases_shift`/`erases_subst` line source and target up. Preserve them.
-/

namespace LBTerm

/-- Look up a declaration in a `GlobalDeclarations` list. Linear scan; fine for the
    scaffolding, the list is logically a finite map. -/
def envLookup : GlobalDeclarations → Kername → Option GlobalDecl
  | [], _ => none
  | (k, d) :: rest, kn => if k.id == kn.id then some d else envLookup rest kn

/-! ### Shift / subst (mutual recursion with explicit list helpers).

We deliberately avoid `List.map` inside the principal recursive functions: the
structural-recursion checker cannot see through `map` for nested inductives,
so we factor the per-list traversals out into dedicated mutually-recursive
helpers. -/

mutual
/-- Shift de Bruijn indices ≥ `cutoff` up by `d`. -/
def shift (d cutoff : Nat) : LBTerm → LBTerm
  | bvar i => if i ≥ cutoff then bvar (i + d) else bvar i
  | lambda n b => lambda n (shift d (cutoff + 1) b)
  | letIn n v b => letIn n (shift d cutoff v) (shift d (cutoff + 1) b)
  | app f a => app (shift d cutoff f) (shift d cutoff a)
  | construct ind k args => construct ind k (shiftArgs d cutoff args)
  | case info scr alts => case info (shift d cutoff scr) (shiftAlts d cutoff alts)
  | proj p e => proj p (shift d cutoff e)
  | fix defs i => fix (shiftDefs d (cutoff + defs.length) defs) i
  | box => box
  | fvar x => fvar x
  | const k => const k
  | prim p => prim p

def shiftArgs (d cutoff : Nat) : List LBTerm → List LBTerm
  | [] => []
  | t :: rest => shift d cutoff t :: shiftArgs d cutoff rest

def shiftAlts (d cutoff : Nat) :
    List (List BinderName × LBTerm) → List (List BinderName × LBTerm)
  | [] => []
  | (ns, b) :: rest => (ns, shift d (cutoff + ns.length) b) :: shiftAlts d cutoff rest

def shiftDefs (d cutoff : Nat) : List (@FixDef LBTerm) → List (@FixDef LBTerm)
  | [] => []
  | fd :: rest => { fd with body := shift d cutoff fd.body } :: shiftDefs d cutoff rest
end

mutual
/-- Substitute `s` for the bound variable at depth `d`, decrementing higher indices. -/
def subst (s : LBTerm) (d : Nat) : LBTerm → LBTerm
  | bvar i =>
    if i < d then bvar i
    else if i = d then shift d 0 s
    else bvar (i - 1)
  | lambda n b => lambda n (subst s (d + 1) b)
  | letIn n v b => letIn n (subst s d v) (subst s (d + 1) b)
  | app f a => app (subst s d f) (subst s d a)
  | construct ind k args => construct ind k (substArgs s d args)
  | case info scr alts => case info (subst s d scr) (substAlts s d alts)
  | proj p e => proj p (subst s d e)
  | fix defs i => fix (substDefs s (d + defs.length) defs) i
  | box => box
  | fvar x => fvar x
  | const k => const k
  | prim p => prim p

def substArgs (s : LBTerm) (d : Nat) : List LBTerm → List LBTerm
  | [] => []
  | t :: rest => subst s d t :: substArgs s d rest

def substAlts (s : LBTerm) (d : Nat) :
    List (List BinderName × LBTerm) → List (List BinderName × LBTerm)
  | [] => []
  | (ns, b) :: rest => (ns, subst s (d + ns.length) b) :: substAlts s d rest

def substDefs (s : LBTerm) (d : Nat) : List (@FixDef LBTerm) → List (@FixDef LBTerm)
  | [] => []
  | fd :: rest => { fd with body := subst s d fd.body } :: substDefs s d rest
end

/-- Substitute the bvar 0 only. -/
@[inline] def subst1 (s : LBTerm) (t : LBTerm) : LBTerm := subst s 0 t

/--
Simultaneous substitution of `ss` for de Bruijn indices `0 .. ss.length - 1`.
Implemented by sequencing `subst1` applications: substituting `ss[0]` first
reduces every higher index by one, which is exactly what we want before
substituting `ss[1]` into position 0, and so on.
-/
def substList (ss : List LBTerm) (t : LBTerm) : LBTerm :=
  ss.foldl (fun acc s => subst1 s acc) t

end LBTerm
