import LeanToLambdaBox.Correctness

/-!
Stage 1 of the verified-erasure programme: the pure-lambda subset.

The fragment of `CExpr` considered here is

  `box | bvar | fvar | app | lam | letE`

with reductions limited to `beta`, `zeta`, and the `appLeft`/`appRight`
congruences. No constants, constructors, case analysis, or fix.

What's proved here:
  * `Steps.single`, `Steps.appLeft`, `Steps.appRight` — boilerplate lifting
    one-step reductions and congruences to the reflexive-transitive closure.
  * `preservation_lambda` — the restricted preservation theorem, with the
    vacuous and congruence cases discharged.

What's deferred (with `sorry`):
  * `erases_subst` — the central substitution lemma relating CExpr- and
    LBTerm-level substitutions through `Erases`. This is the standard
    "substitution preserves erasure" property; proving it cleanly requires
    `CExpr.subst` / `LBTerm.subst` to be `def`s rather than `partial def`s,
    so a future commit will refactor those before discharging.

These five files (`Lambda`, `Constants`, `Inductives`, `Fix`, `Irrel`) are
intended to be the staged path to `erase_preservation` in `Correctness.lean`.
-/

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

/-! ### Reflexive-transitive-closure helpers. -/

namespace LBTerm.Steps

/-- One step is zero-or-more steps. -/
theorem single {Γ : GlobalDeclarations} {t u : LBTerm}
    (h : LBTerm.Step Γ t u) : LBTerm.Steps Γ t u :=
  .step h (.refl _)

theorem trans {Γ : GlobalDeclarations} {t u v : LBTerm}
    (h₁ : LBTerm.Steps Γ t u) (h₂ : LBTerm.Steps Γ u v) : LBTerm.Steps Γ t v := by
  induction h₁ with
  | refl _      => exact h₂
  | step h₁ _ ih => exact .step h₁ (ih h₂)

/-- `Steps` is closed under the left side of an application. -/
theorem appLeft {Γ : GlobalDeclarations} {f f' a : LBTerm}
    (h : LBTerm.Steps Γ f f') : LBTerm.Steps Γ (.app f a) (.app f' a) := by
  induction h with
  | refl _       => exact .refl _
  | step h₁ _ ih => exact .step (.appLeft h₁) ih

/-- `Steps` is closed under the right side of an application. -/
theorem appRight {Γ : GlobalDeclarations} {f a a' : LBTerm}
    (h : LBTerm.Steps Γ a a') : LBTerm.Steps Γ (.app f a) (.app f a') := by
  induction h with
  | refl _       => exact .refl _
  | step h₁ _ ih => exact .step (.appRight h₁) ih

end LBTerm.Steps

/-! ### The substitution lemma — deferred. -/

/--
Substitution lemma: if `b` erases to `b'` and `s` erases to `s'`, then
substituting `s` for the variable at depth `n` in `b` corresponds to the
same substitution on the target side.

This is the core analytical content of preservation; the proof is deferred
until `CExpr.subst` and `LBTerm.subst` are refactored from `partial def` to
ordinary structurally-recursive defs (the nested `List.map` calls inside
`case` / `fix` are the reason for the current `partial`).
-/
theorem erases_subst {Γ : ErasureCtx} (n : Nat) {b s : CExpr} {b' s' : LBTerm}
    (hb : Erases Γ b b') (hs : Erases Γ s s') :
    Erases Γ (CExpr.subst s n b) (LBTerm.subst s' n b') := by
  sorry

/-! ### Stage-1 preservation. -/

/--
Preservation restricted to the pure-lambda fragment.

Structure of the proof:
  * `box`, `bvar`, `fvar`, `lam` — vacuous, no `Step` rule has that shape on
    the LHS.
  * `const`, `ctor`, `cases`, `fix` — `InSubset` rules them out.
  * `app` + `beta`     — uses `erases_subst` (deferred).
  * `app` + `appLeft`  — uses the IH and `Steps.appLeft`.
  * `app` + `appRight` — uses the IH and `Steps.appRight`.
  * `app` + `fixUnfold` — `InSubset` rules out `f = .fix _ _`.
  * `letE` + `zeta`    — uses `erases_subst` (deferred).
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
      | beta n body arg =>
        -- f = .lam n body. Destructure hf to get the body's erasure.
        cases hf with
        | lam _ hb =>
          exact ⟨_, LBTerm.Steps.single (.beta _ _ _), erases_subst 0 hb ha⟩
      | appLeft h =>
        obtain ⟨f'', hsteps, hef'⟩ := ihf hSubf h
        exact ⟨_, LBTerm.Steps.appLeft hsteps, .app hef' ha⟩
      | appRight h =>
        obtain ⟨a'', hsteps, hea'⟩ := iha hSuba h
        exact ⟨_, LBTerm.Steps.appRight hsteps, .app hf hea'⟩
      | fixUnfold defs i _ _ _ =>
        cases hSubf  -- `.fix` is not in the lambda subset
  | letE n hv hb ihv ihb =>
    cases hSub with
    | letE hSubv hSubb =>
      cases hred with
      | zeta _ _ _ =>
        exact ⟨_, LBTerm.Steps.single (.zeta _ _ _), erases_subst 0 hb hv⟩

end ErasureProofs.Lambda
