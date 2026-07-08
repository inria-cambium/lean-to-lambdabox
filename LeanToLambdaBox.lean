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
import LeanToLambdaBox.Abstract
import LeanToLambdaBox.EraseCore
-- The shipping bridge (Half B, plan of record): `visitExpr` → `Erases` directly.
-- `Bridge` holds the supported-fragment predicate; the fvar↔de-Bruijn transport
-- (`ErasesAbstract`), the vlet strengthening (`ErasesStrengthen`), and the
-- `EraseM` run/admissibility toolkit (`ErasureRun`) feed the fixpoint-induction
-- bridge theorem.
import LeanToLambdaBox.Bridge
import LeanToLambdaBox.ErasesAbstract
import LeanToLambdaBox.ErasesStrengthen
import LeanToLambdaBox.ErasureRun
-- Relevance-oracle soundness via lean4lean's verified checker (discharges the
-- `isProp`/proof disjunct of `OracleSound` with no axiom of ours).
import LeanToLambdaBox.RelevanceCheck
-- Run-adequacy of the verified relevance check at an ambient local context
-- (`kernel_isErasable_sound` = `isErasable.WF` + the generalized `M.WF.run'`),
-- and the oracle discharge (`ResidualHyps ⟹ BridgeHyps`) that plugs it into the
-- bridge, shrinking the oracle trust to reflection + `Meta` fallback.
import LeanToLambdaBox.CheckerAdequacy
import LeanToLambdaBox.VisitExprRefines
import LeanToLambdaBox.OracleDischarge
import LeanToLambdaBox.ShippingCorrect
-- Closing the gap to MetaCoq §7.3/§7.4: first-order determinism + the `optimize` pass.
import LeanToLambdaBox.FirstOrder
import LeanToLambdaBox.Optimize
