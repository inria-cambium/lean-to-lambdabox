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
-- Target-side de-Bruijn metatheory: the closedness predicate `LBClosed` and the general
-- `shift`/`subst` commutation kit (`subst_subst`), shared by the env-erasure and ι layers.
import LeanToLambdaBox.Closed
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
-- Recursion wall, slice W0: `substFix` (the fvar → closed-term simultaneous
-- substitution), the `toBvar` ↔ `subst` commutation pair, and
-- `closeFix_substList_fixSubst` — static fix-closing (`mkDef`) inverts the dynamic
-- fix-unfolding that `WcbvEval.fix_guarded` performs.
import LeanToLambdaBox.FixUnfold
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
-- conventions), `TrExprS` spine inversion, the named upstream spec `PatsIotaSpec` with
-- its discharge `PatsIotaSpec.of_trEnv`, and
-- `iota_defeq_spine` (the ι rule fires on a translated exact-arity redex); plus the
-- constructed non-vacuity guard and the accounting of the remaining chain.
import LeanToLambdaBox.IotaPattern
import LeanToLambdaBox.IotaDischarge
-- The ι reversal bridge: a β chain over an erased minor's λ-telescope has the same
-- evaluations as the target ι rule's one-shot `substList (fields.reverse) body`, for
-- closed field values (`wcbvEval_mkApps_mkLambdas_substList`).
import LeanToLambdaBox.IotaBridge
-- ι Task 3: the ι forward simulation `erases_correct_dataι`, at any constructor arity —
-- the ι counterpart of `erases_correct_data`, consuming the `casesOn`-spine erasure
-- inversion (`Erases.cases_spine_inv`/`iota_redex_inv`), the reversal bridge, the
-- `LBClosed` thread, the relevance guard `IotaRelevant` and the two Γ/`ia` coherence
-- predicates.
import LeanToLambdaBox.ErasesCorrectIota
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
-- ι Task 5: the ι capstone (D3ι) — `shipping_erase_correct_firstorderι` plus its
-- `_of_shape` / `_registered` twins, composing the T4b bridge, the flat-fragment ι
-- forward simulation and D1 uniqueness over `SEvalDataι`, with the whole `Γ`/`E`
-- certificate block constructed jointly at a registered flat inductive.
import LeanToLambdaBox.FirstOrderShippingIota
-- Cold-start slice S1: the registry invariant `RegInvShape` (scoped registration
-- records + `KeysDistinct` + the disjunctive `NoFixEnvD`), vacuous at the empty state
-- and preserved by the registration primitives via the *true* run shapes proved in
-- `ErasureRun` (`run_addAxiom_ok`, `run_register_inductive_cold_ok`) — replacing the
-- assumed state-preservation of `register_inductive` with its actual `gdecls` cons.
import LeanToLambdaBox.ColdStartShape
-- Output-shape metatheory for the binder-closing operations (`toBvar` preserves
-- `NoFix`; it takes a body closed at `k` to one closed at `k+1`), plus the fold forms
-- `mkAlt`/`mkDef` need. Prerequisite of the `visitExpr` output-shape induction that
-- `ColdStartShape.regInvShape_nonrec_cons_iff` shows the registry invariant requires.
import LeanToLambdaBox.OutputShape
-- The output-shape induction itself (R11): `visitExpr_shape`, all 18 motives of the
-- erasure family in Hoare form over a `RunClosed` state predicate. Yields
-- `visitExpr_noFix_closed` — every successful `visitExpr` run returns a fix-free,
-- de-Bruijn-closed term, with no hypotheses — and, at `Q := RegInvShape Γ`, the
-- preservation of the cold-start registry invariant across a whole run.
import LeanToLambdaBox.ColdStartInduction
-- Cold-start slice S3: the entry point and the registration exits, decomposed
-- (`erase_run_ok` (R1), `run_prepare_erasure_ok` (R2) — which also *derives*
-- `PrepareHyps`' former `prepare_sound` field — and `run_visitMutual_decomp`, which hands
-- the inner `visitExpr` run back where the Hoare form cannot); and the δ half of the
-- registry record: the body a non-recursive `visitMutual` exit stored really erases the
-- body it erased, plus the recursive block's registration.
import LeanToLambdaBox.ColdStartRun
import LeanToLambdaBox.ColdStartDelta
