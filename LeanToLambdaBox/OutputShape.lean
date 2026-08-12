import LeanToLambdaBox.Closed
import LeanToLambdaBox.Abstract

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

theorem lbClosed_toBvar {t : LBTerm} (x : FVarId) :
    ∀ (k : Nat), LBClosed t k → LBClosed (toBvar x k t) (k + 1) := by
  induction t using LBTerm.recData with
  | hbox => intro k _; simp [toBvar]
  | hbvar i => intro k h; simp only [toBvar]; simp only [LBClosed_bvar] at h ⊢; omega
  | hfvar y =>
    intro k _
    simp only [toBvar]
    split
    · simp
    · simp
  | hconst kn => intro k _; simp [toBvar]
  | hprim p => intro k _; simp [toBvar]
  | hlam nm b ih => intro k h; simpa [toBvar] using ih (k + 1) h
  | hletIn nm v b ihv ihb =>
    intro k h
    obtain ⟨hv, hb⟩ := h
    exact ⟨ihv k hv, ihb (k + 1) hb⟩
  | happ f a ihf iha =>
    intro k h
    obtain ⟨hf, ha⟩ := h
    exact ⟨ihf k hf, iha k ha⟩
  | hconstruct iid c args ih =>
    intro k h
    rw [LBClosed_construct, LBClosedArgs_iff] at h
    rw [toBvar, toBvarArgs_eq_map, LBClosed_construct, LBClosedArgs_iff]
    intro a hmem
    simp only [List.mem_map] at hmem
    obtain ⟨a', hmem', rfl⟩ := hmem
    exact ih a' hmem' k (h a' hmem')
  | hcase info discr alts ihd iha =>
    intro k h
    obtain ⟨hd, ha⟩ := h
    rw [LBClosedAlts_iff] at ha
    obtain ⟨iid, np⟩ := info
    refine ⟨ihd k hd, ?_⟩
    rw [toBvarAlts_eq_map, LBClosedAlts_iff]
    intro a hmem
    simp only [List.mem_map] at hmem
    obtain ⟨a', hmem', rfl⟩ := hmem
    have hcl := iha a' hmem' (k + a'.1.length) (ha a' hmem')
    have heq : k + 1 + a'.1.length = k + a'.1.length + 1 := by omega
    rw [heq]
    exact hcl
  | hproj p e ih => intro k h; exact ih k h
  | hfix defs i ih =>
    intro k h
    rw [LBClosed_fix, LBClosedDefs_iff] at h
    rw [toBvar, LBClosed_fix, LBClosedDefs_iff, toBvarDefs_length]
    intro d hmem
    rw [toBvarDefs_eq_map] at hmem
    simp only [List.mem_map] at hmem
    obtain ⟨d', hmem', rfl⟩ := hmem
    have := ih d' hmem' (k + defs.length) (h d' hmem')
    simpa [Nat.add_right_comm] using this

/-! ### The binder-closing folds

`Erasure.mkAlt` and `Erasure.mkDef` close a body over several free variables at once, by
folding `toBvar` at successive levels (`for (x, i) in xs.reverse.zipIdx do body :=
toBvar x i body`). These are the fold forms of the two lemmas above. -/

theorem noFix_foldl_toBvar :
    ∀ (L : List (FVarId × Nat)) {t : LBTerm}, NoFix t →
      NoFix (L.foldl (fun b p => toBvar p.1 p.2 b) t)
  | [], _, h => h
  | p :: rest, _, h => noFix_foldl_toBvar rest (noFix_toBvar p.1 p.2 h)

theorem lbClosed_foldl_toBvar :
    ∀ (L : List (FVarId × Nat)) {t : LBTerm} (k : Nat),
      (∀ (j : Nat) (h : j < L.length), (L[j]'h).2 = k + j) → LBClosed t k →
      LBClosed (L.foldl (fun b p => toBvar p.1 p.2 b) t) (k + L.length)
  | [], t, k, _, h => by simpa using h
  | p :: rest, t, k, hidx, h => by
    have hp : p.2 = k := by
      have h0 := hidx 0 (by simp)
      simp only [List.getElem_cons_zero, Nat.add_zero] at h0
      exact h0
    have hstep : LBClosed (toBvar p.1 p.2 t) (k + 1) := by
      rw [hp]; exact lbClosed_toBvar p.1 k h
    have hrest : ∀ (j : Nat) (hj : j < rest.length), (rest[j]'hj).2 = (k + 1) + j := by
      intro j hj
      have := hidx (j + 1) (by simpa using Nat.succ_lt_succ hj)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
    have := lbClosed_foldl_toBvar rest (k + 1) hrest hstep
    simpa [List.foldl_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

/-- The instance the erasure family actually uses: closing over `xs.reverse.zipIdx`
takes a body closed at `0` to one closed at `xs.length`. -/
theorem lbClosed_foldl_zipIdx {t : LBTerm} (xs : List FVarId) (h : LBClosed t 0) :
    LBClosed (xs.reverse.zipIdx.foldl (fun b p => toBvar p.1 p.2 b) t) xs.length := by
  have hidx : ∀ (j : Nat) (hj : j < xs.reverse.zipIdx.length),
      (xs.reverse.zipIdx[j]'hj).2 = 0 + j := by
    intro j hj
    simp only [List.length_zipIdx] at hj
    rw [List.getElem_zipIdx]
  have := lbClosed_foldl_toBvar xs.reverse.zipIdx 0 hidx h
  simpa using this

end LeanToLambdaBox
