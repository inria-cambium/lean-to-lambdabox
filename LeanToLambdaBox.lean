-- This module serves as the root of the `LeanToLambdabox` library.
-- Import modules here that should be built as part of the library.
import LeanToLambdaBox.Basic
import LeanToLambdaBox.Erasure
-- Operational-semantics model (a Lean translation of MetaCoq `EWcbvEval`). The
-- `Semantics/` directory holds the de Bruijn substitution kit, `WcbvFlags`, the
-- faithful `Value`/`atom` predicates, the flag-parameterised big-step `WcbvEval`
-- (with `Eval`/`EvalProp` recovered as abbrevs), and its metatheory (determinism,
-- `eval_to_value`, `value_final`, …).
import LeanToLambdaBox.Semantics.Substitution
import LeanToLambdaBox.Semantics.Env
import LeanToLambdaBox.Semantics.Flags
import LeanToLambdaBox.Semantics.Values
import LeanToLambdaBox.Semantics.Eval
import LeanToLambdaBox.Semantics.Metatheory
import LeanToLambdaBox.Semantics
-- Grounding on lean4lean (Half A): the erasure context, the typed `Erases` relation
-- over real `Lean.Expr`, the irrelevance predicate, substitution lemmas, source-side
-- evaluation, subject reduction, and forward-simulation correctness.
import LeanToLambdaBox.ErasureContext
import LeanToLambdaBox.Erasability
import LeanToLambdaBox.Erases
import LeanToLambdaBox.SourceEval
import LeanToLambdaBox.SubjectReduction
import LeanToLambdaBox.SubjectReductionFull
import LeanToLambdaBox.ErasesCorrect
-- Implementation refinement bridge (Half B): pure `eraseCore` + refinement of `Erases`.
import LeanToLambdaBox.EraseCore
-- Closing the gap to MetaCoq §7.3/§7.4: first-order determinism + the `optimize` pass.
import LeanToLambdaBox.FirstOrder
import LeanToLambdaBox.Optimize
