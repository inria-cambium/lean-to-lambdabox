import LeanToLambdaBox.Correctness

/-!
Stage 1 of the verified-erasure programme: the pure-lambda subset.

The fragment of `CExpr` considered here is

  `box | bvar | fvar | app | lam | letE`

with reductions limited to `beta`, `zeta`, and the `appLeft`/`appRight`
congruences. No constants, constructors, case analysis, or fix.

What's proved here:
  * `LBTerm.Steps.{single, trans, appLeft, appRight}` — boilerplate.
  * `erases_shift` / `erases_subst` — Stage-1-scoped (restricted via
    `InSubset` to avoid the ctor / cases / fix case explosion).
  * `preservation_lambda` — the restricted preservation theorem.
-/

/-! ### Reflexive-transitive-closure helpers (top-level so other stages can
    reuse them). -/

theorem LBTerm.Steps.single {Γ : GlobalDeclarations} {t u : LBTerm}
    (h : LBTerm.Step Γ t u) : LBTerm.Steps Γ t u :=
  .step h (.refl _)

theorem LBTerm.Steps.trans {Γ : GlobalDeclarations} {t u v : LBTerm}
    (h₁ : LBTerm.Steps Γ t u) (h₂ : LBTerm.Steps Γ u v) : LBTerm.Steps Γ t v := by
  induction h₁ with
  | refl _      => exact h₂
  | step h₁ _ ih => exact .step h₁ (ih h₂)

theorem LBTerm.Steps.appLeft {Γ : GlobalDeclarations} {f f' a : LBTerm}
    (h : LBTerm.Steps Γ f f') : LBTerm.Steps Γ (.app f a) (.app f' a) := by
  induction h with
  | refl _       => exact .refl _
  | step h₁ _ ih => exact .step (.appLeft h₁) ih

theorem LBTerm.Steps.appRight {Γ : GlobalDeclarations} {f a a' : LBTerm}
    (h : LBTerm.Steps Γ a a') : LBTerm.Steps Γ (.app f a) (.app f a') := by
  induction h with
  | refl _       => exact .refl _
  | step h₁ _ ih => exact .step (.appRight h₁) ih

namespace ErasureProofs.Lambda

open LBTerm CExpr

/-- The CExpr fragment treated in Stage 1. -/
inductive InSubset : CExpr → Prop
  | box                                          : InSubset .box
  | bvar (i : Nat)                               : InSubset (.bvar i)
  | fvar (x : Lean.FVarId)                       : InSubset (.fvar x)
  | app  {f a}   (hf : InSubset f) (ha : InSubset a) : InSubset (.app f a)
  | lam  (n)     {b} (hb : InSubset b)               : InSubset (.lam n b)
  | letE (n) {v b} (hv : InSubset v) (hb : InSubset b) : InSubset (.letE n v b)

/-! ### Shift and substitution lemmas (Stage-1-scoped).

These are proved by induction on `InSubset` so the ctor / cases / fix
branches of `Erases` are simply unreachable.
-/

/-- Erasure commutes with `shift` for the lambda subset. -/
theorem erases_shift {Γ : ErasureCtx} (d c : Nat) {b : CExpr} {b' : LBTerm}
    (hSub : InSubset b) (hb : Erases Γ b b') :
    Erases Γ (CExpr.shift d c b) (LBTerm.shift d c b') := by
  induction hSub generalizing c b' with
  | box =>
    cases hb
    simp only [CExpr.shift, LBTerm.shift]
    exact .box
  | bvar i =>
    cases hb
    simp only [CExpr.shift, LBTerm.shift]
    by_cases h : i ≥ c
    · rw [if_pos h, if_pos h]; exact .bvar _
    · rw [if_neg h, if_neg h]; exact .bvar _
  | fvar x =>
    cases hb
    simp only [CExpr.shift, LBTerm.shift]
    exact .fvar _
  | app _ _ ihf iha =>
    cases hb with
    | app hf ha =>
      simp only [CExpr.shift, LBTerm.shift]
      exact .app (ihf c hf) (iha c ha)
  | lam n _ ihb =>
    cases hb with
    | lam _ hb =>
      simp only [CExpr.shift, LBTerm.shift]
      exact .lam n (ihb (c + 1) hb)
  | letE n _ _ ihv ihb =>
    cases hb with
    | letE _ hv hb =>
      simp only [CExpr.shift, LBTerm.shift]
      exact .letE n (ihv c hv) (ihb (c + 1) hb)

/-- Erasure commutes with substitution for the lambda subset. -/
theorem erases_subst {Γ : ErasureCtx} (n : Nat) {b s : CExpr} {b' s' : LBTerm}
    (hSubB : InSubset b) (hSubS : InSubset s)
    (hb : Erases Γ b b') (hs : Erases Γ s s') :
    Erases Γ (CExpr.subst s n b) (LBTerm.subst s' n b') := by
  induction hSubB generalizing n b' with
  | box =>
    cases hb
    simp only [CExpr.subst, LBTerm.subst]
    exact .box
  | bvar i =>
    cases hb
    simp only [CExpr.subst, LBTerm.subst]
    by_cases h1 : i < n
    · rw [if_pos h1, if_pos h1]; exact .bvar _
    rw [if_neg h1, if_neg h1]
    by_cases h2 : i = n
    · rw [if_pos h2, if_pos h2]; exact erases_shift n 0 hSubS hs
    · rw [if_neg h2, if_neg h2]; exact .bvar _
  | fvar x =>
    cases hb
    simp only [CExpr.subst, LBTerm.subst]
    exact .fvar _
  | app _ _ ihf iha =>
    cases hb with
    | app hf ha =>
      simp only [CExpr.subst, LBTerm.subst]
      exact .app (ihf n hf) (iha n ha)
  | lam name _ ihb =>
    cases hb with
    | lam _ hb =>
      simp only [CExpr.subst, LBTerm.subst]
      exact .lam name (ihb (n + 1) hb)
  | letE name _ _ ihv ihb =>
    cases hb with
    | letE _ hv hb =>
      simp only [CExpr.subst, LBTerm.subst]
      exact .letE name (ihv n hv) (ihb (n + 1) hb)

/-! ### Stage-1 preservation. -/

/--
Preservation restricted to the pure-lambda fragment.
-/
theorem preservation_lambda
    {Γ : ErasureCtx} {Δ : CExpr.Env} {E : GlobalDeclarations}
    {e e' : CExpr} {t : LBTerm}
    (hSub : InSubset e)
    (he   : Erases Γ e t)
    (hred : CExpr.Step Δ e e') :
    ∃ t', LBTerm.Steps E t t' ∧ Erases Γ e' t' := by
  induction he generalizing e' with
  | box                 => cases hred
  | bvar _              => cases hred
  | fvar _              => cases hred
  | const _ _ _         => cases hSub
  | lam _ _ _           => cases hred
  | ctor _ _ _ _ _ _    => cases hSub
  | cases _ _ _ _ _ _ _ _ => cases hSub
  | fix _ _ _           => cases hSub
  | app hf ha ihf iha =>
    cases hSub with
    | app hSubf hSuba =>
      cases hred with
      | beta _ _ _ =>
        cases hf with
        | lam _ hb =>
          cases hSubf with
          | lam _ hSubBody =>
            exact ⟨_, LBTerm.Steps.single (.beta _ _ _),
                   erases_subst 0 hSubBody hSuba hb ha⟩
      | appLeft h =>
        obtain ⟨_, hsteps, hef'⟩ := ihf hSubf h
        exact ⟨_, LBTerm.Steps.appLeft hsteps, .app hef' ha⟩
      | appRight h =>
        obtain ⟨_, hsteps, hea'⟩ := iha hSuba h
        exact ⟨_, LBTerm.Steps.appRight hsteps, .app hf hea'⟩
      | fixUnfold _ _ _ _ _ =>
        cases hSubf  -- `.fix` is not in the lambda subset
  | letE name hv hb ihv ihb =>
    cases hSub with
    | letE name' hSubv hSubb =>
      cases hred with
      | zeta _ _ _ =>
        exact ⟨_, LBTerm.Steps.single (.zeta _ _ _),
               erases_subst 0 hSubb hSubv hb hv⟩

end ErasureProofs.Lambda
