import LeanToLambdaBox.Basic
import LeanToLambdaBox.Semantics.Substitution

/-!
# Metatheory of `abstract`/`toBvar` (fvar → de Bruijn) — foundation

Foundation for the `fvar`↔de-Bruijn reconciliation between the shipping erasure
(`Erasure.visitExpr`, which opens binders into fresh `fvar`s, recurses, then
`abstract`s back to de Bruijn) and the pure de-Bruijn model (`eraseCore`/`Erases`).

These lemmas were **unprovable while `toBvar` was a `partial def`**; de-partializing
it (`Basic.lean`) into a structural `def` with explicit list helpers is what makes
them available — a concrete instance of the de-partialization technique that the
shipping `visitExpr` family will also need.

`toBvar x lvl` replaces the free variable `x` by the de Bruijn index `lvl`,
incrementing under binders — the LBTerm analogue of "close the binder".
-/

namespace LeanToLambdaBox

open Lean

/-! ### The list-helper traversals are `map`s (as for `shift`/`subst`).

These push `toBvar` through the nested `List` occurrences (`construct` args, `case`
alternatives, `fix` definitions), exactly as `shiftArgs_eq_map`/`substArgs_eq_map`
do for the substitution kit — the standard shape every structural induction over
`toBvar` needs. -/

theorem toBvarArgs_eq_map (x : FVarId) (lvl : Nat) (l : List LBTerm) :
    toBvarArgs x lvl l = l.map (toBvar x lvl) := by
  induction l with
  | nil => rfl
  | cons t rest ih => simp [toBvarArgs, ih]

theorem toBvarAlts_eq_map (x : FVarId) (lvl : Nat) (l : List (List BinderName × LBTerm)) :
    toBvarAlts x lvl l = l.map (fun a => (a.1, toBvar x (lvl + a.1.length) a.2)) := by
  induction l with
  | nil => rfl
  | cons a rest ih => obtain ⟨ns, b⟩ := a; simp [toBvarAlts, ih]

theorem toBvarDefs_eq_map (x : FVarId) (lvl : Nat) (l : List (@FixDef LBTerm)) :
    toBvarDefs x lvl l = l.map (fun fd => { fd with body := toBvar x lvl fd.body }) := by
  induction l with
  | nil => rfl
  | cons fd rest ih => simp [toBvarDefs, ih]

/-- `abstract` unfolds to `toBvar … 0`. -/
theorem abstract_eq (x : FVarId) (t : LBTerm) : abstract x t = toBvar x 0 t := rfl

/-!
Next (deferred — the harder foundation): a `hasFVar`/no-occurrence predicate + the
no-op lemma `¬ hasFVar x t → toBvar x lvl t = t` (needs a structural `hasFVar` and a
shared `LBTerm.rec'` eliminator, currently local to `Optimize.lean`), then the
`toBvar`↔`shift`/`subst` commutations and the binder-case simulation relating
`abstract x (eraseCore (e.instantiate1' (.fvar x)))` to `eraseCore e`. That
simulation — together with lean4lean's `TrExprS.inst_fvar` (fvar-opening ↔ `VLCtx`
extension) — is the crux of the `fvar`↔de-Bruijn bridge, and is a substantial
(HIGH-difficulty) effort in its own right.
-/

end LeanToLambdaBox
