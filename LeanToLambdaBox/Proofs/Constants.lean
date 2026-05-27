import LeanToLambdaBox.Proofs.Lambda

/-!
Stage 2 of the verified-erasure programme: add constants and the global
environment to the verified subset.

Beyond Stage 1, this stage handles:
  * the `.const` CExpr constructor;
  * the `delta` rule of `CExpr.Step` / `LBTerm.Step`;
  * the `EnvConsistent` predicate connecting source and target environments.

Stub: the subset predicate and restricted theorem statement are committed
to fix the directory layout. Proofs come in a follow-on pass.
-/

namespace ErasureProofs.Constants

/-- Extends `Lambda.InSubset` with the `.const` constructor. -/
inductive InSubset : CExpr → Prop
  | box                                           : InSubset .box
  | bvar (i)                                      : InSubset (.bvar i)
  | fvar (x)                                      : InSubset (.fvar x)
  | const (n : Lean.Name)                         : InSubset (.const n)
  | app  {f a} (hf : InSubset f) (ha : InSubset a) : InSubset (.app f a)
  | lam  (n) {b} (hb : InSubset b)                 : InSubset (.lam n b)
  | letE (n) {v b} (hv : InSubset v) (hb : InSubset b) : InSubset (.letE n v b)

theorem preservation_constants
    {Γ : ErasureCtx} {Δ : CExpr.Env} {E : GlobalDeclarations}
    (hEnv : EnvConsistent Γ Δ E)
    {e e' : CExpr} {t : LBTerm}
    (hSub : InSubset e)
    (he   : Erases Γ e t)
    (hred : CExpr.Step Δ e e') :
    ∃ t', LBTerm.Steps E t t' ∧ Erases Γ e' t' := by
  sorry

end ErasureProofs.Constants
