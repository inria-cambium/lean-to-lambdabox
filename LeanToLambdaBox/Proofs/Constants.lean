import LeanToLambdaBox.Proofs.Lambda

/-!
Stage 2 of the verified-erasure programme: add constants and the global
environment.

Beyond Stage 1 this handles:
  * the `.const` CExpr constructor;
  * the `delta` rule of `CExpr.Step` / `LBTerm.Step`, which uses
    `EnvConsistent` to relate the two global environments.

The Stage-1 substitution / shift lemmas have to be re-stated in Stage 2 to
include the new `const` case; the structure of the proof is otherwise
identical to Lambda's. (A future cleanup would prove these once for the
full `Erases` relation with the help of `substArgs`/`substAlts`/`substDefs`
preservation lemmas; for now we just thread Stage-by-Stage.)
-/

namespace ErasureProofs.Constants

open LBTerm CExpr

/-- Extends `Lambda.InSubset` with the `.const` constructor. -/
inductive InSubset : CExpr → Prop
  | box                                           : InSubset .box
  | bvar (i)                                      : InSubset (.bvar i)
  | fvar (x)                                      : InSubset (.fvar x)
  | const (n : Lean.Name)                         : InSubset (.const n)
  | app  {f a} (hf : InSubset f) (ha : InSubset a) : InSubset (.app f a)
  | lam  (n) {b} (hb : InSubset b)                 : InSubset (.lam n b)
  | letE (n) {v b} (hv : InSubset v) (hb : InSubset b) : InSubset (.letE n v b)

/-- Erasure commutes with `shift` for the Constants subset. -/
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
  | const _ =>
    cases hb with
    | const _ _ heq =>
      simp only [CExpr.shift, LBTerm.shift]
      exact .const _ _ heq
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

/-- Erasure commutes with substitution for the Constants subset. -/
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
  | const _ =>
    cases hb with
    | const _ _ heq =>
      simp only [CExpr.subst, LBTerm.subst]
      exact .const _ _ heq
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

/-- Stage-2 preservation: extends `preservation_lambda` with the `delta`
    rule for `.const` reduction, which is discharged via `hEnv`. -/
theorem preservation_constants
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
  | ctor _ _ _ _ _ _    => cases hSub
  | cases _ _ _ _ _ _ _ _ => cases hSub
  | fix _ _ _           => cases hSub
  | const n_src kn hkn =>
    -- Source: e = .const n_src, t = .const kn. After `cases hred` only delta
    -- applies; pattern names are forced by unification, so we pull them from
    -- the context (`hΔ` and `e'`) instead of binding fresh.
    cases hred with
    | delta _ _ hΔ =>
      obtain ⟨body', henvLookup, herB⟩ := hEnv n_src e' hΔ
      refine ⟨body', LBTerm.Steps.single ?_, herB⟩
      have heq : LBTerm.envLookup E kn = some (.constantDecl ⟨some body'⟩) := by
        rw [← hkn]; exact henvLookup
      exact .delta _ _ heq
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
        cases hSubf
  | letE name hv hb ihv ihb =>
    cases hSub with
    | letE _ hSubv hSubb =>
      cases hred with
      | zeta _ _ _ =>
        exact ⟨_, LBTerm.Steps.single (.zeta _ _ _),
               erases_subst 0 hSubb hSubv hb hv⟩

end ErasureProofs.Constants
