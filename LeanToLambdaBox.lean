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
-- `Type`-valued twin `WcbvEvalT` of `WcbvEval` (+ `All2T` and the axiom-free
-- `wcbvEvalT_iff`), exported to Rocq via lean4export/rocq-lean-import to validate the
-- λ□ semantics translation against MetaRocq's `EWcbvEval.eval` (workstream WS-R).
import LeanToLambdaBox.Export.EvalT
-- Grounding on lean4lean (Half A): the erasure context, the typed `Erases` relation
-- over real `Lean.Expr`, the irrelevance predicate, substitution lemmas, source-side
-- evaluation, subject reduction, and forward-simulation correctness.
import LeanToLambdaBox.ErasureContext
import LeanToLambdaBox.Erasability
import LeanToLambdaBox.Erases
import LeanToLambdaBox.SourceEval
import LeanToLambdaBox.SubjectReduction
import LeanToLambdaBox.SubjectReductionFull
import LeanToLambdaBox.SourceEvalData
import LeanToLambdaBox.ErasesCorrect
-- Implementation refinement bridge (Half B): pure `eraseCore` + refinement of `Erases`.
import LeanToLambdaBox.Abstract
-- P3 foundation: the `n`-way fvar→de-Bruijn abstraction (`closeFix`) modelling the
-- `mkDef` closing loop of a recursive mutual block (env-level erasure, deferred rule).
import LeanToLambdaBox.FixMetatheory
import LeanToLambdaBox.EraseCore
-- Data-fragment forward simulation at MetaRocq's non-block `appliedFlags`
-- (β + δ + saturated constructors): `erases_correct_data` (A5–A7).
import LeanToLambdaBox.ErasesCorrectData
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
-- The data-fragment trust bundle (constructor data-path primitive specs), beside
-- `BridgeHyps`; consumed by the widened bridge.
import LeanToLambdaBox.DataBridgeHyps
-- The ι-fragment trust bundle (`casesOn` classifier / inductive registration /
-- `inferType` specs), beside `BridgeHyps`; consumed by the ι-widened bridge.
import LeanToLambdaBox.CasesBridgeHyps
-- P3-v2b: recursive (value-`fix`) cold-start env-consistency — the `Erases.fix`
-- reconciliation (`erases_fix_of_closed`) + `LBClosed` de-Bruijn-closedness metatheory.
import LeanToLambdaBox.EnvErasureRec
-- P3-v2b composition: the D3 capstone with its env-δ-consistency premise sourced from
-- the registration record (`erasesEnvDeltaData_of_registeredClosureData`), plus the
-- honest trust bundle for full cold-start (DAG + `NoFixEnv` relaxation deferred).
import LeanToLambdaBox.EnvErasure
import LeanToLambdaBox.VisitExprRefines
import LeanToLambdaBox.OracleDischarge
import LeanToLambdaBox.ShippingCorrect
-- Closing the gap to MetaCoq §7.3/§7.4: first-order determinism + the `optimize` pass.
import LeanToLambdaBox.FirstOrder
import LeanToLambdaBox.Optimize
-- ι (`casesOn`) fragment (WS-F2, C2/C3): subject-reduction-as-defeq over `SEvalDataι`
-- (`SEvalDataι_defeq`, discharging ι only via `IotaConsistent`), the non-vacuity guards
-- for the ζ-fragment theorems, and the documented C3 forward-simulation finding
-- (`Erases.cases` under-constrains minor arities — an upstream `Erases.lean` gap).
import LeanToLambdaBox.SubjectReductionIota
-- ι Task 2: the pattern-side core of the pinned fork's ι interface — `Pattern.Matches`
-- introduction for spines, the `SimplePattern.iotaRHS` reduct calculation (`take`/`drop`
-- conventions), `TrExprS` spine inversion, the named upstream spec `PatsIotaSpec`, and
-- `iota_defeq_spine` (the ι rule fires on a translated exact-arity redex); plus the
-- constructed non-vacuity guard and the accounting of the remaining chain.
import LeanToLambdaBox.IotaPattern
import LeanToLambdaBox.IotaDischarge
-- The shipping eraser is correct on the data fragment (β+δ+saturated constructors)
-- at MetaRocq's non-block `appliedFlags` (`shipping_visitExpr_correct_data`, A9), and
-- the first-order capstone (`shipping_erase_correct_firstorder`, D3): the shipping
-- erasure of a source term evaluating to a first-order value reaches the unique
-- applied-form erasure of that value.
import LeanToLambdaBox.ShippingCorrectData
import LeanToLambdaBox.FirstOrderShipping
-- P3-v1 (env-level cold-start erasure, non-recursive + inductive fragment): the
-- elaborator-transformation trust class `PrepareHyps` (csimp-off gate), and the
-- discharge of the env-consistency hypotheses `ErasesEnvCtor`/`ErasesEnvCases` (from
-- `register_inductive`'s local arity) and non-recursive `ErasesEnvDelta`/
-- `ErasesEnvDeltaData` (via the `visitExpr → Erases` bridge), isolating the cold-start
-- DAG registration behind clean `Prop` hypotheses for P3-v2b.
import LeanToLambdaBox.PrepareHyps
import LeanToLambdaBox.EnvErasureNonrec
