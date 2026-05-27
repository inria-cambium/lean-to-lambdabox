import LeanToLambdaBox.Proofs.Constants

/-!
Stage 3 of the verified-erasure programme: add inductive constructors and
`casesOn`.

Beyond Stage 2 this handles:
  * the `.ctor` and `.cases` CExpr constructors;
  * the `iota` rule of `CExpr.Step` / `LBTerm.Step` (case analysis on a
    known constructor).

The substitution lemma needs to be extended to handle the new
constructors. This routes through small list-level helper lemmas about
`substArgs`/`substAlts` etc. preserving length and per-element
relations.

The `iota` case of `preservation_inductives` further needs a
`substList`-preservation lemma. The `casesDiscr` congruence is closed
via the new `LBTerm.Steps.caseDiscr` helper added in Lambda.lean.
-/

namespace ErasureProofs.Inductives

open LBTerm CExpr

inductive InSubset : CExpr → Prop
  | box                                           : InSubset .box
  | bvar (i)                                      : InSubset (.bvar i)
  | fvar (x)                                      : InSubset (.fvar x)
  | const (n)                                     : InSubset (.const n)
  | app  {f a} (hf : InSubset f) (ha : InSubset a) : InSubset (.app f a)
  | lam  (n) {b} (hb : InSubset b)                 : InSubset (.lam n b)
  | letE (n) {v b} (hv : InSubset v) (hb : InSubset b) : InSubset (.letE n v b)
  | ctor (tn) (k) {args} (hargs : ∀ i (h : i < args.length), InSubset args[i]) :
      InSubset (.ctor tn k args)
  | cases (tn) {discr} {alts} (hd : InSubset discr)
          (halts : ∀ i (h : i < alts.length), InSubset alts[i].2) :
      InSubset (.cases tn discr alts)

/-! ### List-helper length and indexing lemmas. -/

theorem length_shiftArgs (d c : Nat) :
    ∀ xs, (CExpr.shiftArgs d c xs).length = xs.length
  | [] => rfl
  | _ :: rest => by simp [CExpr.shiftArgs, length_shiftArgs]

theorem length_shiftArgs_LB (d c : Nat) :
    ∀ xs, (LBTerm.shiftArgs d c xs).length = xs.length
  | [] => rfl
  | _ :: rest => by simp [LBTerm.shiftArgs, length_shiftArgs_LB]

theorem length_substArgs (s : CExpr) (n : Nat) :
    ∀ xs, (CExpr.substArgs s n xs).length = xs.length
  | [] => rfl
  | _ :: rest => by simp [CExpr.substArgs, length_substArgs]

theorem length_substArgs_LB (s : LBTerm) (n : Nat) :
    ∀ xs, (LBTerm.substArgs s n xs).length = xs.length
  | [] => rfl
  | _ :: rest => by simp [LBTerm.substArgs, length_substArgs_LB]

theorem length_shiftAlts (d c : Nat) :
    ∀ (alts : List (List Lean.Name × CExpr)),
      (CExpr.shiftAlts d c alts).length = alts.length
  | [] => rfl
  | _ :: rest => by simp [CExpr.shiftAlts, length_shiftAlts]

theorem length_shiftAlts_LB (d c : Nat) :
    ∀ (alts : List (List BinderName × LBTerm)),
      (LBTerm.shiftAlts d c alts).length = alts.length
  | [] => rfl
  | _ :: rest => by simp [LBTerm.shiftAlts, length_shiftAlts_LB]

theorem length_substAlts (s : CExpr) (n : Nat) :
    ∀ (alts : List (List Lean.Name × CExpr)),
      (CExpr.substAlts s n alts).length = alts.length
  | [] => rfl
  | _ :: rest => by simp [CExpr.substAlts, length_substAlts]

theorem length_substAlts_LB (s : LBTerm) (n : Nat) :
    ∀ (alts : List (List BinderName × LBTerm)),
      (LBTerm.substAlts s n alts).length = alts.length
  | [] => rfl
  | _ :: rest => by simp [LBTerm.substAlts, length_substAlts_LB]

/-! ### Indexing equations for the list helpers (used to unfold a
specific position after applying the helper). -/

theorem getElem_substArgs (s : CExpr) (n : Nat) :
    ∀ (xs : List CExpr) (i : Nat) (h : i < (CExpr.substArgs s n xs).length),
      (CExpr.substArgs s n xs)[i] = CExpr.subst s n (xs[i]'(by
        rw [length_substArgs] at h; exact h))
  | [], i, h => by simp [CExpr.substArgs] at h
  | x :: rest, 0, _ => by simp [CExpr.substArgs]
  | x :: rest, i + 1, h => by
    simp [CExpr.substArgs] at h ⊢
    exact getElem_substArgs s n rest i h

theorem getElem_substArgs_LB (s : LBTerm) (n : Nat) :
    ∀ (xs : List LBTerm) (i : Nat) (h : i < (LBTerm.substArgs s n xs).length),
      (LBTerm.substArgs s n xs)[i] = LBTerm.subst s n (xs[i]'(by
        rw [length_substArgs_LB] at h; exact h))
  | [], i, h => by simp [LBTerm.substArgs] at h
  | _ :: _, 0, _ => by simp [LBTerm.substArgs]
  | _ :: rest, i + 1, h => by
    simp [LBTerm.substArgs] at h ⊢
    exact getElem_substArgs_LB s n rest i h

theorem getElem_substAlts_fst (s : CExpr) (n : Nat) :
    ∀ (alts : List (List Lean.Name × CExpr)) (i : Nat)
        (h : i < (CExpr.substAlts s n alts).length),
      (CExpr.substAlts s n alts)[i].1 = (alts[i]'(by
        rw [length_substAlts] at h; exact h)).1
  | [], i, h => by simp [CExpr.substAlts] at h
  | (_, _) :: _, 0, _ => by simp [CExpr.substAlts]
  | _ :: rest, i + 1, h => by
    simp [CExpr.substAlts] at h ⊢
    exact getElem_substAlts_fst s n rest i h

theorem getElem_substAlts_snd (s : CExpr) (n : Nat) :
    ∀ (alts : List (List Lean.Name × CExpr)) (i : Nat)
        (h : i < (CExpr.substAlts s n alts).length),
      (CExpr.substAlts s n alts)[i].2 = CExpr.subst s (n + (alts[i]'(by
        rw [length_substAlts] at h; exact h)).1.length) (alts[i]'(by
        rw [length_substAlts] at h; exact h)).2
  | [], i, h => by simp [CExpr.substAlts] at h
  | (_, _) :: _, 0, _ => by simp [CExpr.substAlts]
  | _ :: rest, i + 1, h => by
    simp [CExpr.substAlts] at h ⊢
    exact getElem_substAlts_snd s n rest i h

theorem getElem_substAlts_fst_LB (s : LBTerm) (n : Nat) :
    ∀ (alts : List (List BinderName × LBTerm)) (i : Nat)
        (h : i < (LBTerm.substAlts s n alts).length),
      (LBTerm.substAlts s n alts)[i].1 = (alts[i]'(by
        rw [length_substAlts_LB] at h; exact h)).1
  | [], i, h => by simp [LBTerm.substAlts] at h
  | (_, _) :: _, 0, _ => by simp [LBTerm.substAlts]
  | _ :: rest, i + 1, h => by
    simp [LBTerm.substAlts] at h ⊢
    exact getElem_substAlts_fst_LB s n rest i h

theorem getElem_substAlts_snd_LB (s : LBTerm) (n : Nat) :
    ∀ (alts : List (List BinderName × LBTerm)) (i : Nat)
        (h : i < (LBTerm.substAlts s n alts).length),
      (LBTerm.substAlts s n alts)[i].2 = LBTerm.subst s (n + (alts[i]'(by
        rw [length_substAlts_LB] at h; exact h)).1.length) (alts[i]'(by
        rw [length_substAlts_LB] at h; exact h)).2
  | [], i, h => by simp [LBTerm.substAlts] at h
  | (_, _) :: _, 0, _ => by simp [LBTerm.substAlts]
  | _ :: rest, i + 1, h => by
    simp [LBTerm.substAlts] at h ⊢
    exact getElem_substAlts_snd_LB s n rest i h

theorem length_substDefs (s : CExpr) (n : Nat) :
    ∀ (defs : List (Lean.Name × CExpr)), (CExpr.substDefs s n defs).length = defs.length
  | [] => rfl
  | _ :: rest => by simp [CExpr.substDefs, length_substDefs]

theorem length_substDefs_LB (s : LBTerm) (n : Nat) :
    ∀ (defs : List (@FixDef LBTerm)), (LBTerm.substDefs s n defs).length = defs.length
  | [] => rfl
  | _ :: rest => by simp [LBTerm.substDefs, length_substDefs_LB]

theorem getElem_substDefs_snd (s : CExpr) (n : Nat) :
    ∀ (defs : List (Lean.Name × CExpr)) (i : Nat)
        (h : i < (CExpr.substDefs s n defs).length),
      (CExpr.substDefs s n defs)[i].2 = CExpr.subst s n (defs[i]'(by
        rw [length_substDefs] at h; exact h)).2
  | [], i, h => by simp [CExpr.substDefs] at h
  | (_, _) :: _, 0, _ => by simp [CExpr.substDefs]
  | _ :: rest, i + 1, h => by
    simp [CExpr.substDefs] at h ⊢
    exact getElem_substDefs_snd s n rest i h

theorem getElem_substDefs_body_LB (s : LBTerm) (n : Nat) :
    ∀ (defs : List (@FixDef LBTerm)) (i : Nat)
        (h : i < (LBTerm.substDefs s n defs).length),
      (LBTerm.substDefs s n defs)[i].body = LBTerm.subst s n (defs[i]'(by
        rw [length_substDefs_LB] at h; exact h)).body
  | [], i, h => by simp [LBTerm.substDefs] at h
  | _ :: _, 0, _ => by simp [LBTerm.substDefs]
  | _ :: rest, i + 1, h => by
    simp [LBTerm.substDefs] at h ⊢
    exact getElem_substDefs_body_LB s n rest i h

/-! ### Shift indexing helpers. -/

theorem getElem_shiftArgs (d c : Nat) :
    ∀ (xs : List CExpr) (i : Nat) (h : i < (CExpr.shiftArgs d c xs).length),
      (CExpr.shiftArgs d c xs)[i] = CExpr.shift d c (xs[i]'(by
        rw [length_shiftArgs] at h; exact h))
  | [], i, h => by simp [CExpr.shiftArgs] at h
  | _ :: _, 0, _ => by simp [CExpr.shiftArgs]
  | _ :: rest, i + 1, h => by
    simp [CExpr.shiftArgs] at h ⊢
    exact getElem_shiftArgs d c rest i h

theorem getElem_shiftArgs_LB (d c : Nat) :
    ∀ (xs : List LBTerm) (i : Nat) (h : i < (LBTerm.shiftArgs d c xs).length),
      (LBTerm.shiftArgs d c xs)[i] = LBTerm.shift d c (xs[i]'(by
        rw [length_shiftArgs_LB] at h; exact h))
  | [], i, h => by simp [LBTerm.shiftArgs] at h
  | _ :: _, 0, _ => by simp [LBTerm.shiftArgs]
  | _ :: rest, i + 1, h => by
    simp [LBTerm.shiftArgs] at h ⊢
    exact getElem_shiftArgs_LB d c rest i h

theorem getElem_shiftAlts_fst (d c : Nat) :
    ∀ (alts : List (List Lean.Name × CExpr)) (i : Nat)
        (h : i < (CExpr.shiftAlts d c alts).length),
      (CExpr.shiftAlts d c alts)[i].1 = (alts[i]'(by
        rw [length_shiftAlts] at h; exact h)).1
  | [], i, h => by simp [CExpr.shiftAlts] at h
  | (_, _) :: _, 0, _ => by simp [CExpr.shiftAlts]
  | _ :: rest, i + 1, h => by
    simp [CExpr.shiftAlts] at h ⊢
    exact getElem_shiftAlts_fst d c rest i h

theorem getElem_shiftAlts_snd (d c : Nat) :
    ∀ (alts : List (List Lean.Name × CExpr)) (i : Nat)
        (h : i < (CExpr.shiftAlts d c alts).length),
      (CExpr.shiftAlts d c alts)[i].2 = CExpr.shift d (c + (alts[i]'(by
        rw [length_shiftAlts] at h; exact h)).1.length) (alts[i]'(by
        rw [length_shiftAlts] at h; exact h)).2
  | [], i, h => by simp [CExpr.shiftAlts] at h
  | (_, _) :: _, 0, _ => by simp [CExpr.shiftAlts]
  | _ :: rest, i + 1, h => by
    simp [CExpr.shiftAlts] at h ⊢
    exact getElem_shiftAlts_snd d c rest i h

theorem getElem_shiftAlts_fst_LB (d c : Nat) :
    ∀ (alts : List (List BinderName × LBTerm)) (i : Nat)
        (h : i < (LBTerm.shiftAlts d c alts).length),
      (LBTerm.shiftAlts d c alts)[i].1 = (alts[i]'(by
        rw [length_shiftAlts_LB] at h; exact h)).1
  | [], i, h => by simp [LBTerm.shiftAlts] at h
  | (_, _) :: _, 0, _ => by simp [LBTerm.shiftAlts]
  | _ :: rest, i + 1, h => by
    simp [LBTerm.shiftAlts] at h ⊢
    exact getElem_shiftAlts_fst_LB d c rest i h

theorem getElem_shiftAlts_snd_LB (d c : Nat) :
    ∀ (alts : List (List BinderName × LBTerm)) (i : Nat)
        (h : i < (LBTerm.shiftAlts d c alts).length),
      (LBTerm.shiftAlts d c alts)[i].2 = LBTerm.shift d (c + (alts[i]'(by
        rw [length_shiftAlts_LB] at h; exact h)).1.length) (alts[i]'(by
        rw [length_shiftAlts_LB] at h; exact h)).2
  | [], i, h => by simp [LBTerm.shiftAlts] at h
  | (_, _) :: _, 0, _ => by simp [LBTerm.shiftAlts]
  | _ :: rest, i + 1, h => by
    simp [LBTerm.shiftAlts] at h ⊢
    exact getElem_shiftAlts_snd_LB d c rest i h

theorem length_shiftDefs (d c : Nat) :
    ∀ (defs : List (Lean.Name × CExpr)), (CExpr.shiftDefs d c defs).length = defs.length
  | [] => rfl
  | _ :: rest => by simp [CExpr.shiftDefs, length_shiftDefs]

theorem length_shiftDefs_LB (d c : Nat) :
    ∀ (defs : List (@FixDef LBTerm)), (LBTerm.shiftDefs d c defs).length = defs.length
  | [] => rfl
  | _ :: rest => by simp [LBTerm.shiftDefs, length_shiftDefs_LB]

theorem getElem_shiftDefs_snd (d c : Nat) :
    ∀ (defs : List (Lean.Name × CExpr)) (i : Nat)
        (h : i < (CExpr.shiftDefs d c defs).length),
      (CExpr.shiftDefs d c defs)[i].2 = CExpr.shift d c (defs[i]'(by
        rw [length_shiftDefs] at h; exact h)).2
  | [], i, h => by simp [CExpr.shiftDefs] at h
  | (_, _) :: _, 0, _ => by simp [CExpr.shiftDefs]
  | _ :: rest, i + 1, h => by
    simp [CExpr.shiftDefs] at h ⊢
    exact getElem_shiftDefs_snd d c rest i h

theorem getElem_shiftDefs_body_LB (d c : Nat) :
    ∀ (defs : List (@FixDef LBTerm)) (i : Nat)
        (h : i < (LBTerm.shiftDefs d c defs).length),
      (LBTerm.shiftDefs d c defs)[i].body = LBTerm.shift d c (defs[i]'(by
        rw [length_shiftDefs_LB] at h; exact h)).body
  | [], i, h => by simp [LBTerm.shiftDefs] at h
  | _ :: _, 0, _ => by simp [LBTerm.shiftDefs]
  | _ :: rest, i + 1, h => by
    simp [LBTerm.shiftDefs] at h ⊢
    exact getElem_shiftDefs_body_LB d c rest i h

/-! ### General shift / subst preservation (full `Erases`). -/

/-- Erasure commutes with `shift` for the **full** `Erases` relation
    (no `InSubset` restriction). -/
theorem erases_shift_general {Γ : ErasureCtx} (d : Nat) :
    ∀ (c : Nat) {b : CExpr} {b' : LBTerm}, Erases Γ b b' →
      Erases Γ (CExpr.shift d c b) (LBTerm.shift d c b') := by
  intro c b b' hb
  induction hb generalizing c with
  | box =>
    simp only [CExpr.shift, LBTerm.shift]; exact .box
  | bvar i =>
    simp only [CExpr.shift, LBTerm.shift]
    by_cases h : i ≥ c
    · rw [if_pos h, if_pos h]; exact .bvar _
    · rw [if_neg h, if_neg h]; exact .bvar _
  | fvar x =>
    simp only [CExpr.shift, LBTerm.shift]; exact .fvar _
  | const n kn heq =>
    simp only [CExpr.shift, LBTerm.shift]; exact .const _ _ heq
  | app _ _ ihf iha =>
    simp only [CExpr.shift, LBTerm.shift]; exact .app (ihf c) (iha c)
  | lam name _ ihb =>
    simp only [CExpr.shift, LBTerm.shift]; exact .lam name (ihb (c + 1))
  | letE name _ _ ihv ihb =>
    simp only [CExpr.shift, LBTerm.shift]; exact .letE name (ihv c) (ihb (c + 1))
  | ctor tn k iid hi hl _hes ihhes =>
    rename_i args args'
    simp only [CExpr.shift, LBTerm.shift]
    refine .ctor tn k iid hi ?lenEq ?pw
    case lenEq => rw [length_shiftArgs, length_shiftArgs_LB]; exact hl
    case pw =>
      intros i h
      have h_orig : i < args.length := by rw [length_shiftArgs] at h; exact h
      rw [getElem_shiftArgs, getElem_shiftArgs_LB]
      exact ihhes i h_orig c
  | cases tn iid np hi _hd hl hns _hes ihhd ihhes =>
    rename_i alts alts'
    simp only [CExpr.shift, LBTerm.shift]
    refine .cases tn iid np hi (ihhd c) ?lenEq ?nsEq ?pw
    case lenEq => rw [length_shiftAlts, length_shiftAlts_LB]; exact hl
    case nsEq =>
      intros i h
      have h_orig : i < alts.length := by rw [length_shiftAlts] at h; exact h
      rw [getElem_shiftAlts_fst, getElem_shiftAlts_fst_LB]
      exact hns i h_orig
    case pw =>
      intros i h
      have h_orig : i < alts.length := by rw [length_shiftAlts] at h; exact h
      rw [getElem_shiftAlts_snd, getElem_shiftAlts_snd_LB]
      have hn := hns i h_orig
      rw [← hn]
      exact ihhes i h_orig (c + alts[i].1.length)
  | fix i hl _hes ihhes =>
    rename_i defs defs'
    simp only [CExpr.shift, LBTerm.shift]
    refine .fix i ?lenEq ?pw
    case lenEq => rw [length_shiftDefs, length_shiftDefs_LB]; exact hl
    case pw =>
      intros j h
      have h_orig : j < defs.length := by rw [length_shiftDefs] at h; exact h
      rw [getElem_shiftDefs_snd, getElem_shiftDefs_body_LB]
      have ih := ihhes j h_orig (c + defs.length)
      have hdepth : c + defs.length = c + defs'.length := by rw [hl]
      exact hdepth ▸ ih

/-- Erasure commutes with substitution for the **full** `Erases` relation
    (no `InSubset` restriction). -/
theorem erases_subst_general {Γ : ErasureCtx} {s : CExpr} {s' : LBTerm}
    (hs : Erases Γ s s') :
    ∀ (n : Nat) {b : CExpr} {b' : LBTerm}, Erases Γ b b' →
      Erases Γ (CExpr.subst s n b) (LBTerm.subst s' n b') := by
  intro n b b' hb
  induction hb generalizing n with
  | box =>
    simp only [CExpr.subst, LBTerm.subst]; exact .box
  | bvar i =>
    simp only [CExpr.subst, LBTerm.subst]
    by_cases h1 : i < n
    · rw [if_pos h1, if_pos h1]; exact .bvar _
    rw [if_neg h1, if_neg h1]
    by_cases h2 : i = n
    · rw [if_pos h2, if_pos h2]; exact erases_shift_general n 0 hs
    · rw [if_neg h2, if_neg h2]; exact .bvar _
  | fvar x =>
    simp only [CExpr.subst, LBTerm.subst]; exact .fvar _
  | const _ _ heq =>
    simp only [CExpr.subst, LBTerm.subst]; exact .const _ _ heq
  | app _ _ ihf iha =>
    simp only [CExpr.subst, LBTerm.subst]; exact .app (ihf n) (iha n)
  | lam name _ ihb =>
    simp only [CExpr.subst, LBTerm.subst]; exact .lam name (ihb (n + 1))
  | letE name _ _ ihv ihb =>
    simp only [CExpr.subst, LBTerm.subst]; exact .letE name (ihv n) (ihb (n + 1))
  | ctor tn k iid hi hl _hes ihhes =>
    rename_i args args'
    simp only [CExpr.subst, LBTerm.subst]
    refine .ctor tn k iid hi ?lenEq ?pw
    case lenEq => rw [length_substArgs, length_substArgs_LB]; exact hl
    case pw =>
      intros i h
      have h_orig : i < args.length := by rw [length_substArgs] at h; exact h
      rw [getElem_substArgs, getElem_substArgs_LB]
      exact ihhes i h_orig n
  | cases tn iid np hi _hd hl hns _hes ihhd ihhes =>
    rename_i alts alts'
    simp only [CExpr.subst, LBTerm.subst]
    refine .cases tn iid np hi (ihhd n) ?lenEq ?nsEq ?pw
    case lenEq => rw [length_substAlts, length_substAlts_LB]; exact hl
    case nsEq =>
      intros i h
      have h_orig : i < alts.length := by rw [length_substAlts] at h; exact h
      rw [getElem_substAlts_fst, getElem_substAlts_fst_LB]
      exact hns i h_orig
    case pw =>
      intros i h
      have h_orig : i < alts.length := by rw [length_substAlts] at h; exact h
      rw [getElem_substAlts_snd, getElem_substAlts_snd_LB]
      have hn := hns i h_orig
      rw [← hn]
      exact ihhes i h_orig (n + alts[i].1.length)
  | fix i hl _hes ihhes =>
    rename_i defs defs'
    simp only [CExpr.subst, LBTerm.subst]
    refine .fix i ?lenEq ?pw
    case lenEq => rw [length_substDefs, length_substDefs_LB]; exact hl
    case pw =>
      intros j h
      have h_orig : j < defs.length := by rw [length_substDefs] at h; exact h
      rw [getElem_substDefs_snd, getElem_substDefs_body_LB]
      have ih := ihhes j h_orig (n + defs.length)
      have hdepth : n + defs.length = n + defs'.length := by rw [hl]
      exact hdepth ▸ ih

theorem preservation_inductives
    {Γ : ErasureCtx} {Δ : CExpr.Env} {E : GlobalDeclarations}
    (hEnv : EnvConsistent Γ Δ E)
    {e e' : CExpr} {t : LBTerm}
    (hSub : InSubset e)
    (he   : Erases Γ e t)
    (hred : CExpr.Step Δ e e') :
    ∃ t', LBTerm.Steps E t t' ∧ Erases Γ e' t' := by
  induction he generalizing e' with
  | box                 => cases hred
  | bvar _              => cases hred
  | fvar _              => cases hred
  | lam _ _ _           => cases hred
  | fix _ _ _           => cases hSub
  | const n_src kn hkn =>
    cases hred with
    | delta _ _ hΔ =>
      obtain ⟨body', henvLookup, herB⟩ := hEnv n_src e' hΔ
      refine ⟨body', LBTerm.Steps.single ?_, herB⟩
      have heq : LBTerm.envLookup E kn = some (.constantDecl ⟨some body'⟩) := by
        rw [← hkn]; exact henvLookup
      exact .delta _ _ heq
  | ctor _ _ _ _ _ _ _ =>
    -- No `Step` rule has `.ctor` on the LHS, so `cases hred` is vacuous.
    cases hred
  | app hf ha ihf iha =>
    cases hSub with
    | app hSubf hSuba =>
      cases hred with
      | beta _ _ _ =>
        -- This is the beta case: needs `erases_subst` extended to handle
        -- bodies containing `ctor` / `cases`. Currently sorry.
        sorry
      | appLeft h =>
        obtain ⟨_, hsteps, hef'⟩ := ihf hSubf h
        exact ⟨_, LBTerm.Steps.appLeft hsteps, .app hef' ha⟩
      | appRight h =>
        obtain ⟨_, hsteps, hea'⟩ := iha hSuba h
        exact ⟨_, LBTerm.Steps.appRight hsteps, .app hf hea'⟩
      | fixUnfold _ _ _ _ _ =>
        cases hSubf
  | letE _ _ _ _ _ =>
    cases hSub with
    | letE _ _ _ =>
      cases hred with
      | zeta _ _ _ =>
        -- Needs `erases_subst` extended; sorry for the same reason as beta.
        sorry
  | cases tn iid np hi hd hl hns hes hd_ih _hes_ih =>
    cases hSub with
    | cases _ hSubd _hSubalts =>
      cases hred with
      | iota _ _ _ _ _ _ _ =>
        -- The iota case needs `erases_substList` (substituting a list of
        -- ctor args into the chosen alternative body, preserving erasure).
        -- This is the big remaining obligation of Stage 3.
        sorry
      | casesDiscr h =>
        obtain ⟨discr_new', hsteps, herr_discr_new⟩ := hd_ih hSubd h
        refine ⟨_, LBTerm.Steps.caseDiscr hsteps, ?_⟩
        exact .cases tn iid np hi herr_discr_new hl hns hes

end ErasureProofs.Inductives
