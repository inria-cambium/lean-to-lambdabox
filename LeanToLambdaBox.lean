-- This module serves as the root of the `LeanToLambdabox` library.
-- Import modules here that should be built as part of the library.
import LeanToLambdaBox.Basic
import LeanToLambdaBox.Erasure
-- Verification scaffolding (Phase 2 of the attack plan). Definitions only;
-- the correctness theorem ships with a `sorry` to be discharged in Phase 3.
import LeanToLambdaBox.Semantics
import LeanToLambdaBox.CExpr
import LeanToLambdaBox.Correctness
-- Staged proofs (Phase 3). All five stages are fully proved.
import LeanToLambdaBox.Proofs.Lambda
import LeanToLambdaBox.Proofs.Constants
import LeanToLambdaBox.Proofs.Inductives
import LeanToLambdaBox.Proofs.Fix
import LeanToLambdaBox.Proofs.Irrel
-- Grounding re-base on lean4lean (Half A): typed `Erases` over real `Lean.Expr`,
-- irrelevance predicate, substitution lemmas, and big-step λ□ evaluation.
import LeanToLambdaBox.Erasability
import LeanToLambdaBox.Erases
import LeanToLambdaBox.Eval

/-- **Erasure preservation** (top-level export).

If a source term `e` erases to target term `t` and `e` takes one source-level
reduction step to `e'`, then `t` reduces in zero or more target-level steps
to some `t'` that erases `e'`. -/
theorem erase_preservation
    {Γ : ErasureCtx} {Δ : CExpr.Env} {E : GlobalDeclarations}
    (hEnv : EnvConsistent Γ Δ E)
    {e e' : CExpr} {t : LBTerm}
    (he   : Erases Γ e t)
    (hred : CExpr.Step Δ e e') :
    ∃ t', LBTerm.Steps E t t' ∧ Erases Γ e' t' :=
  ErasureProofs.Irrel.preservation_irrel hEnv he hred
