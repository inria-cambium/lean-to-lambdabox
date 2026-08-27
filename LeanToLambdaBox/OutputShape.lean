import LeanToLambdaBox.Closed
import LeanToLambdaBox.Abstract
import LeanToLambdaBox.ErasesCorrectData

/-!
# Output-shape metatheory for the binder-closing operations (slice S1b)

`ColdStartShape.regInvShape_nonrec_cons_iff` shows that the cold-start registry
invariant cannot get past `visitMutual`'s non-recursive constant cons without knowing
`NoFix t` and `LBClosed t 0` of the stored `visitExpr` output. Establishing those is an
induction over the *results* of the 18-function erasure family ("R11"), and every one of
its binder cases goes through `Erasure.mkLambda`/`mkLetIn`/`mkAlt`/`mkDef`, i.e. through
`toBvar`.

This file is the metatheory those cases need: `toBvar` preserves `NoFix`, and it takes a
body closed at level `k` to one closed at `k + 1` — plus the fold forms for the
multi-binder closings (`mkAlt` over an alternative's fields, `mkDef` over a mutual
block's fixpoint variables), which apply `toBvar` at levels `0, 1, 2, …` in turn.

Since slice δ-D7a the same three shapes are here for **`NoBlock`** (applied form), which
the shape induction now carries as a third output conjunct — see `ShapeC`. That is why
this file imports `ErasesCorrectData`, where `NoBlock` is defined next to its de-Bruijn
metatheory (`noBlock_shift`/`noBlock_subst`); the import is free in practice, the only
consumer of this file being `ColdStartInduction`, which already pulls that cone in
through `ColdStartShape`.

Deliberately independent of `ErasureRun`: these are pure `LBTerm` facts, so they can be
used by the shape induction, by the recursion wall's `.fix` reasoning, and by the ι
layer alike.
-/

namespace LeanToLambdaBox

open Lean

/-! ### The panic fall-through's output

Every destructuring helper and every `unreachable!` arm of the erasure family `panic!`s,
and a panic *succeeds* at `EraseM`, returning `default : LBTerm`
(`Erasure.run_panicWithPosWithDecl`). `default` is `.box`, which is fix-free and closed at
every level, so the shape induction's panic arms are **discharged**, not refuted — the
honest reading of code whose "impossible" branches are reachable in the model. -/

@[simp] theorem noFix_default : NoFix (default : LBTerm) := trivial

@[simp] theorem lbClosed_default (k : Nat) : LBClosed (default : LBTerm) k := trivial

/-- `default = .box`, and boxing is invisible to `NoBlock` — the predicate forbids exactly
one node, a `.construct` with a non-empty argument list. So the panic arms are discharged
for the third output conjunct too. -/
@[simp] theorem noBlock_default : NoBlock (default : LBTerm) := trivial

theorem noFix_toBvar {t : LBTerm} (x : FVarId) :
    ∀ (lvl : Nat), NoFix t → NoFix (toBvar x lvl t) := by
  induction t using LBTerm.recData with
  | hbox => intro lvl _; simp [toBvar]
  | hbvar i => intro lvl _; simp [toBvar]
  | hfvar y => intro lvl _; simp [toBvar]; split <;> simp
  | hconst kn => intro lvl _; simp [toBvar]
  | hprim p => intro lvl _; simp [toBvar]
  | hlam nm b ih => intro lvl h; simpa [toBvar] using ih (lvl + 1) h
  | hletIn nm v b ihv ihb =>
    intro lvl h
    obtain ⟨hv, hb⟩ := h
    exact ⟨ihv lvl hv, ihb (lvl + 1) hb⟩
  | happ f a ihf iha =>
    intro lvl h
    obtain ⟨hf, ha⟩ := h
    exact ⟨ihf lvl hf, iha lvl ha⟩
  | hconstruct iid k args ih => intro lvl _; simp [toBvar]
  | hcase info discr alts ihd iha =>
    intro lvl h
    obtain ⟨hd, ha⟩ := h
    rw [NoFixAlts_iff] at ha
    refine ⟨ihd lvl hd, ?_⟩
    rw [toBvarAlts_eq_map, NoFixAlts_iff]
    intro a hmem
    simp only [List.mem_map] at hmem
    obtain ⟨a', hmem', rfl⟩ := hmem
    exact iha a' hmem' (lvl + a'.1.length) (ha a' hmem')
  | hproj p e ih => intro lvl _; simp [toBvar]
  | hfix defs i ih => intro lvl h; exact absurd h (by simp)

/-- **`toBvar` preserves applied form.** The third `toBvar` lemma, and the one the shape
induction's binder cases (motives 8/9/14/16/18) and `mkDef` need once `ShapeC` carries
`NoBlock`.

Routine, and for a structural reason: `toBvar` maps `.construct iid n args` to
`.construct iid n (toBvarArgs x lvl args)`, and `toBvarArgs` preserves list emptiness —
so the one node `NoBlock` forbids is neither created nor destroyed. The proof is
`noBlock_shift`'s (`ErasesCorrectData.lean`) with `shift` replaced by `toBvar`. -/
theorem noBlock_toBvar {t : LBTerm} (x : FVarId) :
    ∀ (lvl : Nat), NoBlock t → NoBlock (toBvar x lvl t) := by
  induction t using LBTerm.recData with
  | hbvar i => intro lvl _; simp [toBvar]
  | hfvar y => intro lvl _; simp only [toBvar]; split <;> trivial
  | hlam nm b ih => intro lvl h; exact ih (lvl + 1) h
  | hletIn nm v b ihv ihb => intro lvl h; exact ⟨ihv lvl h.1, ihb (lvl + 1) h.2⟩
  | happ f a ihf iha => intro lvl h; exact ⟨ihf lvl h.1, iha lvl h.2⟩
  | hconstruct iid c args ih =>
    intro lvl h
    cases args with
    | nil => simp only [toBvar, toBvarArgs]; trivial
    | cons a as => exact absurd h (by simp [NoBlock])
  | hcase info discr alts ihd iha =>
    intro lvl h
    rw [NoBlock_case] at h
    obtain ⟨iid, np⟩ := info
    simp only [toBvar, NoBlock_case, toBvarAlts_eq_map]
    refine ⟨ihd lvl h.1, fun a ha => ?_⟩
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact iha b hb (lvl + b.1.length) (h.2 b hb)
  | hproj p e ih => intro lvl _; trivial
  | hfix defs i ih =>
    intro lvl h
    rw [NoBlock_fix] at h
    simp only [toBvar, NoBlock_fix, toBvarDefs_eq_map]
    intro fd hfd
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hfd
    exact ih d hd (lvl + defs.length) (h d hd)
  | _ => intro lvl _; trivial

/-! ### The binder-closing folds

`Erasure.mkAlt` and `Erasure.mkDef` close a body over several free variables at once, by
folding `toBvar` at successive levels (`for (x, i) in xs.reverse.zipIdx do body :=
toBvar x i body`). These are the fold forms of the two lemmas above. -/

theorem noFix_foldl_toBvar :
    ∀ (L : List (FVarId × Nat)) {t : LBTerm}, NoFix t →
      NoFix (L.foldl (fun b p => toBvar p.1 p.2 b) t)
  | [], _, h => h
  | p :: rest, _, h => noFix_foldl_toBvar rest (noFix_toBvar p.1 p.2 h)

theorem noBlock_foldl_toBvar :
    ∀ (L : List (FVarId × Nat)) {t : LBTerm}, NoBlock t →
      NoBlock (L.foldl (fun b p => toBvar p.1 p.2 b) t)
  | [], _, h => h
  | p :: rest, _, h => noBlock_foldl_toBvar rest (noBlock_toBvar p.1 p.2 h)

/-- The `mkDef` instance for applied form: the block-closing fold indexes its binders by
*name* through the reader's fixvar map, exactly as `lbClosed_foldl_zipIdx_map` does. There
is no arithmetic to do here — `NoBlock` carries no level — so the statement is the fold of
`noBlock_toBvar` and nothing else. -/
theorem noBlock_foldl_zipIdx_map {α : Type} {t : LBTerm} (fv : α → FVarId) (xs : List α)
    (h : NoBlock t) :
    NoBlock (xs.reverse.zipIdx.foldl (fun b p => toBvar (fv p.1) p.2 b) t) := by
  have hmap : xs.reverse.zipIdx.foldl (fun b p => toBvar (fv p.1) p.2 b) t
      = (xs.reverse.zipIdx.map (fun p => (fv p.1, p.2))).foldl
          (fun b q => toBvar q.1 q.2 b) t := by
    rw [List.foldl_map]
  rw [hmap]
  exact noBlock_foldl_toBvar _ h

end LeanToLambdaBox
