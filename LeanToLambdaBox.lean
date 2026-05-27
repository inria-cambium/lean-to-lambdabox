-- This module serves as the root of the `LeanToLambdabox` library.
-- Import modules here that should be built as part of the library.
import LeanToLambdaBox.Basic
import LeanToLambdaBox.Erasure
-- Verification scaffolding (Phase 2 of the attack plan). Definitions only;
-- the correctness theorem ships with a `sorry` to be discharged in Phase 3.
import LeanToLambdaBox.Semantics
import LeanToLambdaBox.CExpr
import LeanToLambdaBox.Correctness
