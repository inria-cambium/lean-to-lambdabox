-- This module serves as the root of the `LeanToLambdabox` library.
-- Import modules here that should be built as part of the library.
import LeanToLambdaBox.Basic
import LeanToLambdaBox.Erasure
-- Verification scaffolding (Phase 2 of the attack plan). Definitions only;
-- the correctness theorem ships with a `sorry` to be discharged in Phase 3.
import LeanToLambdaBox.Semantics
import LeanToLambdaBox.CExpr
import LeanToLambdaBox.Correctness
-- Staged proofs (Phase 3). Stage 1 (Lambda) compiles modulo the substitution
-- lemma; Stages 2-5 are stubs committing to the directory layout.
import LeanToLambdaBox.Proofs.Lambda
import LeanToLambdaBox.Proofs.Constants
import LeanToLambdaBox.Proofs.Inductives
import LeanToLambdaBox.Proofs.Fix
import LeanToLambdaBox.Proofs.Irrel
