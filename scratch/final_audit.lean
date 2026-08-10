import LeanToLambdaBox
/-! Final axiom audit for the dev/verify verification stack (2026-07-07;
re-baselined 2026-08-10 for Lean v4.33.0-rc2 + the `barabbs/lean4lean` ι fork
`7c5e652`).

Allowed: ⊆ [propext, sorryAx, Classical.choice, Quot.sound] + lean4lean's
modeling axioms (`Verify/Axioms.lean`, `PtrEq.lean`) where the executable
checker / `Expr` model is involved. The pure-LBTerm layers must be sorryAx-free.

## lean4lean-side baseline drift at the 2026-08-10 repoint

Nothing of ours changed: no axiom of ours was added, and every result below that
was sorryAx-free before is still sorryAx-free. The lean4lean modeling set moved:

* **Discharged upstream, so they no longer appear**: `Lean.Expr.hasFVar_eq`,
  `Lean.Expr.hasExprMVar_eq`, `Lean.Expr.hasLevelMVar_eq`,
  `Lean.Expr.hasLevelParam_eq` (now theorems) and `Lean.Expr.mkAppRangeAux.eq_def`
  (now proved).
* **Added upstream by the `Level` standardization**: `Lean.Level.normalize_eq`
  (reached by the deep kernel-checker cluster below), plus `Lean.Level.mkMaxAux_eq`,
  `Lean.Level.skipExplicit_eq`, `Lean.Level.isExplicitSubsumedAux_eq` (declared
  upstream, not reached from anything audited here).
* **`bv_decide` native-LRAT artifacts** from lean4lean's `Verify/Expr.lean`:
  `Lean.Expr.mkData_flags._native.bv_decide.ax_*` and
  `Lean.Expr.Data.looseBVarRange_le._native.bv_decide.ax_*`. lean4lean-side SAT
  certificates; they occur only in the executable-checker cluster (WS-O below).
* **`sorryAx` reach grew upstream** (the fork's twelve `IOTA-TODO(soundness)`
  items: `Aligned.addInduct`, `addInduct_WF`, the `IsDefEq`/`IsDefEqStrong` `pat`
  inversion cases, …). This widens the *inherited* trust boundary but does not
  reach any result here that was previously clean.
-/

open LeanToLambdaBox

-- Task A: the de-partialized shipping family (must be sorryAx-free).
#print axioms Erasure.visitExpr.eq_def
#print axioms Erasure.visitLambda.eq_def
#print axioms Erasure.visitLet.eq_def
#print axioms Erasure.visitApp.eq_def
#print axioms Erasure.visitConstApp.eq_def
#print axioms Erasure.visitAppArgs.eq_def
#print axioms Erasure.visitMutual.eq_def
#print axioms Erasure.expr_withApp_eq

-- B1/B2: toBvar metatheory (must be lean4lean-free).
#print axioms toBvar_eq_of_not_hasFVar
#print axioms abstract_eq_of_not_hasFVar
#print axioms toBvar_shift
#print axioms toBvar_toBvar

-- B3/B3b: Erases transport (lean4lean boundary allowed).
#print axioms Erases.abstract
#print axioms Erases.uninstantiateN
#print axioms Erases.uninstantiate
#print axioms Erases.thin_vlet
#print axioms Erases.strengthen_vlet

-- Bridge part 1 (fragment + binder cores).
#print axioms Supported.instantiate1
#print axioms bridge_lam_case
#print axioms bridge_let_case
#print axioms TrLCtx.mkLocalDecl
#print axioms TrLCtx.mkLetDecl
#print axioms LocalContext.find?_mkLocalDecl_self
#print axioms LocalContext.fvarIdToDecl_find!_of_find?

-- B4 infra (must be lean4lean-free).
#print axioms Erasure.run_bind_ok
#print axioms Erasure.eraseM_admissible_ok
#print axioms Erasure.run_array_foldlM_ok
#print axioms Erasure.visitExpr_run_shape

-- Pre-existing flagship results (unchanged expectations).
#print axioms erases_correct
#print axioms eraseCore_correct
#print axioms isErasable.WF
#print axioms eval_deterministic
#print axioms LBOptimize_correct

-- B4 + Task C: the bridge and the top-level theorem.
#print axioms visitExpr_refines_erases
#print axioms shipping_visitExpr_correct

-- WS-F(theory): data-fragment widening (A3–A7). Expected: lean4lean boundary
-- (`[propext, sorryAx, Classical.choice, Quot.sound]`); A5 (`construct_app_spine`)
-- is sorryAx-free; `SEvalData`/`SEvalDataC` axiom-free.
#print axioms SEvalData
#print axioms SEvalDataC
#print axioms Erases.ctor_head
#print axioms SEvalData_const_spine_lam_elim
#print axioms construct_app_spine
#print axioms Erases.ctor_spine_inv
#print axioms erases_correct_data
-- WS-F2 (theory): ζ transport + ζ-including data simulation, and the ι subject
-- reduction. Expected: 4 standard + lean4lean `sorryAx` (inherited TrProj cluster).
-- `IotaConsistent` is a HYPOTHESIS of `SEvalDataι_defeq` (never an axiom), so it adds
-- nothing to the axiom set. (Still no `erases_correct_dataι`: `Erases.cases` now carries
-- the arity pins that unblock it — see the C3 status note in `SubjectReductionIota.lean` —
-- but the ι forward simulation itself is not built yet.)
#print axioms Erases.defeqDFC
#print axioms erases_correct_data_zeta
#print axioms SEvalDataι_defeq
#print axioms erases_correct_data_zeta_fires
#print axioms Erases_defeqDFC_fires
-- D0–D2: uniqueness of the applied erasure on first-order values.
#print axioms firstOrder_value_erases_unique
#print axioms firstOrderValue_erases_eq_eraseCore
#print axioms erases_correct_data_fires

-- WS-O: oracle-discharge stack (run-adequacy at ambient MLCtx + the discharge).
#print axioms Lean4Lean.TypeChecker.VContext.ofMLCtx
#print axioms Lean4Lean.TypeChecker.VState.WF.initial
#print axioms Lean4Lean.TypeChecker.M.WF.run'
#print axioms Lean4Lean.TypeChecker.kernel_isErasable_sound
#print axioms ResidualHyps.toBridgeHyps
#print axioms shipping_visitExpr_correct'

-- P3 (env-level erasure foundation): the `n`-way `closeFix` abstraction modelling the
-- `mkDef` closing loop. Pure LBTerm (imports only `Abstract`) — must be sorryAx-free.
#print axioms LeanToLambdaBox.closeFixFold_eq_foldl
#print axioms LeanToLambdaBox.closeFixFold_eq_self_of_not_hasFVar
#print axioms LeanToLambdaBox.closeFixFold_bvar
#print axioms LeanToLambdaBox.closeFixFold_fvar_of_not_mem
#print axioms LeanToLambdaBox.closeFixFold_fvar_head
#print axioms LeanToLambdaBox.closeFixFold_app
#print axioms LeanToLambdaBox.closeFix_2block_first
#print axioms LeanToLambdaBox.closeFix_2block_last

-- ============================================================================
-- P3-v2a: the `Erases.fix` rule bundle + its transport metatheory + the ripple.
-- The D3 capstone + the two data forward-sims must be UNCHANGED (4 standard +
-- lean4lean modeling set). The new transport/ripple theorems inherit `sorryAx`
-- from lean4lean's `TrExprS` lemmas (documented), no new axioms of ours.
-- ============================================================================
#print axioms shipping_erase_correct_firstorder
#print axioms shipping_visitExpr_correct_data
#print axioms erases_correct_data
#print axioms erases_correct_data_zeta
#print axioms erases_correct
#print axioms erases_correct_beta
-- new transport fix cases + ripple + rule guard:
#print axioms erases_shift
#print axioms erases_subst
#print axioms Erases.abstract
#print axioms Erases.thin_vlet
#print axioms Erases.lam_inv
#print axioms Erases.defeqDFC
#print axioms noFix_subst1
#print axioms noFix_mkApps
-- P3-v1 (non-recursive + inductive cold-start env-consistency discharge). New trust is
-- Prop hypotheses (`PrepareHyps`, `Registered*`), NEVER axioms. Expected axiom set:
-- 4 standard [propext, Classical.choice, Quot.sound] (+ sorryAx via the lean4lean Expr
-- typing model where `Erases`/`TrExprS`/`BridgeInv` are involved). No axiom of ours.
#print axioms LeanToLambdaBox.PrepareHyps
#print axioms LeanToLambdaBox.prepareHyps_conclusion_at_identity
#print axioms LeanToLambdaBox.prepareHyps_inhabited_point
#print axioms LeanToLambdaBox.prepareHyps_csimp_off_satisfiable
#print axioms LeanToLambdaBox.ErasesEnvCases
#print axioms LeanToLambdaBox.erasesEnvCtor_of_registeredCtors
#print axioms LeanToLambdaBox.erasesEnvCases_of_registeredCases
#print axioms LeanToLambdaBox.gΓctor_registeredCtors
#print axioms LeanToLambdaBox.gΓctor_erasesEnvCtor
#print axioms LeanToLambdaBox.gΓcases_erasesEnvCases
#print axioms LeanToLambdaBox.erases_nonrec_const_body
#print axioms LeanToLambdaBox.erasesEnvDelta_of_registeredClosure
#print axioms LeanToLambdaBox.erasesEnvDeltaData_of_registeredClosureData
#print axioms LeanToLambdaBox.gRegisteredClosure
#print axioms LeanToLambdaBox.gErasesEnvDelta
#print axioms LeanToLambdaBox.gBridgeInv_nil

-- ============================================================================
-- P3-v2b: recursive (value-`fix`) cold-start env-consistency discharge.
-- New trust is Prop hypotheses (`RegisteredClosureRec`), NEVER axioms. The pure
-- `LBClosed` metatheory must be sorryAx-free; the `Erases.fix` reconciliation
-- inherits `sorryAx` only via the lean4lean Expr typing model (`Closed`/`FVarsIn`).
-- ============================================================================
#print axioms LeanToLambdaBox.LBClosed.shift_eq
#print axioms LeanToLambdaBox.LBClosed.subst_eq
#print axioms LeanToLambdaBox.erases_fix_of_closed
#print axioms LeanToLambdaBox.erasesEnvDelta_of_registeredClosureRec
#print axioms LeanToLambdaBox.gErases_fix
#print axioms LeanToLambdaBox.gRegisteredClosureRec
#print axioms LeanToLambdaBox.gErasesEnvDeltaRec

-- ============================================================================
-- ι-T4a/b: the `casesOn` bridge (`Supported.casesApp`, motives 15–18), now at
-- general λ-telescope alternatives. New trust is the `CasesBridgeHyps` **Prop**
-- bundle, NEVER an axiom. The `EraseM` loop rule, the pure `visitCases` loop
-- arithmetic and the `mkAlt`/`closeAlt` layer must be lean4lean-free (4 standard
-- at most); the fragment inversions, the telescope opener and the widened bridge
-- inherit `sorryAx` exactly as before, with no axiom of ours added. The `mkAlt`
-- name lookup and the lctx-persistence lemma go through lean4lean's
-- `PersistentHashMap`/`PersistentArray` modeling axioms, as `Bridge.lean`'s other
-- `find?` lemmas already do.
-- ============================================================================
#print axioms Erasure.run_list_forIn_ok'
#print axioms Erasure.run_array_forIn_ok'
#print axioms LeanToLambdaBox.IsLamTelescope.instantiate1'
#print axioms LeanToLambdaBox.exists_app_of_foldl_app_ne_nil
#print axioms LeanToLambdaBox.rco_toArray_getElem
#print axioms LeanToLambdaBox.slice_toArray_toList_drop
#print axioms LeanToLambdaBox.list_split_cases
#print axioms LeanToLambdaBox.subarray_next?_facts
#print axioms LeanToLambdaBox.visitCases_match_default
#print axioms LeanToLambdaBox.CasesBridgeHyps
#print axioms LeanToLambdaBox.CasesInfoAgrees
#print axioms LeanToLambdaBox.ForallMatchesLam
#print axioms LeanToLambdaBox.Supported.casesApp_inv
#print axioms LeanToLambdaBox.casesApp_spine_facts
-- ι-T4b: the λ-telescope layer.
#print axioms LeanToLambdaBox.ForallMatchesLam.instantiate1'
#print axioms LeanToLambdaBox.closeAlt_foldl
#print axioms LeanToLambdaBox.mkLambdas_closeAlt_cons
#print axioms LeanToLambdaBox.filter_replicate_keep
#print axioms LeanToLambdaBox.run_mkAlt
#print axioms LeanToLambdaBox.LocalContext.find?_mkLocalDecl_of_ne
#print axioms LeanToLambdaBox.LocalContext.fvarIdToDecl_find!_congr
#print axioms LeanToLambdaBox.bridge_alt_telescope

-- P3-v2b Part 4 + composition: recursion subsumed by v1's RegisteredClosure, and the
-- D3 capstone with env-δ-consistency sourced from registration. No axiom of ours.
#print axioms LeanToLambdaBox.registeredClosure_of_registeredClosureRec
#print axioms LeanToLambdaBox.erasesEnvDelta_of_registeredClosureRec'
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder_registered

-- ============================================================================
-- ι Task 2: the pattern-side ι interface (`IotaPattern.lean`) + its guard
-- (`IotaDischarge.lean`).
--
-- The pure pattern plumbing (`Matches` introduction for spines, the
-- `SimplePattern.iotaRHS` reduct calculation) must be **sorryAx-free**: it touches
-- only `Pattern`/`VExpr`, never `TrExprS`. `TrExprS.mkApps_inv` and
-- `iota_defeq_spine` inherit `sorryAx` from lean4lean's `TrProj` placeholder carried
-- in `TrExprS` — the pre-existing boundary, no new gap. `PatsIotaSpec` is a
-- HYPOTHESIS structure (discharged by `TrEnv.pats_iota'` after the fork re-pin),
-- never an axiom, so it adds nothing to any axiom set.
--
-- The constructed guard `envι_iota_fires` must be **sorryAx-free**: it builds its
-- `VEnv` with `VEnv.addPat` directly and applies `VEnv.IsDefEq.pat`, neither of which
-- routes through `Aligned.addInduct`/`addInduct_WF`/`TrProj`. (The δ-unfold step of
-- the remaining chain WOULD route through `Aligned.addInduct` via `TrEnv.of_value` —
-- documented in `IotaDischarge.lean`, not exercised here.)
-- ============================================================================
#print axioms Lean4Lean.Pattern.matches_varN_const
#print axioms Lean4Lean.Pattern.matches_iota
#print axioms Lean4Lean.SimplePattern.iotaRHS_apply
#print axioms Lean4Lean.TrExprS.mkApps_inv
#print axioms LeanToLambdaBox.iota_defeq_spine
#print axioms LeanToLambdaBox.envι_iota_fires
-- The β-normalisation engine for steps (2)/(4)/(5). A β step builds its reduct's
-- `TrExprS` by `TrExprS.inst`, so it needs no application node — hence none of the
-- `HasType` premises that block the ι reduct. Inherits `sorryAx` from `TrExprS`
-- (`TrProj`) only.
#print axioms LeanToLambdaBox.trExprS_beta_step
#print axioms LeanToLambdaBox.trExprS_betaN

-- ι Task 2, part 2: `TrExprS` spine *construction* via application generation
-- (`Lean4Lean.VEnv.HasType.app_inv`, `Theory/Typing/Strong.lean` — a proved theorem at
-- this pin, whose sorry-frontier is a subset of the one `VEnv.IsDefEq.uniqU` already
-- carries), the `[] → Δ` transport of the fork-supplied rule template, and the payoff
-- `iotaConsistent_of_shape`.
--
-- `iotaConsistent_of_shape` picks up lean4lean's `Lean.Expr`-implementation modelling
-- axioms (`mkData_eq`, `mkAppData_eq`, `replace_eq`, `Level.hasMVar_eq`,
-- `Level.hasParam_eq`, `Level.instLawfulBEqLevel`, and two `bv_decide` native checks in
-- lean4lean's own `Expr.Data` bit-packing proofs) via `TrExprS.instL` — the price of
-- level-instantiating a polymorphic recursor rule. They are NOT new: its axiom set is a
-- strict SUBSET of the already-committed `shipping_visitExpr_correct'`'s. No axiom of
-- ours; `PatsIotaSpec`/`SEnvConsistent`/`IotaShape` are hypotheses, never axioms.
--
-- The two `IotaShape` `Expr`-equation guards must be `rfl`-provable and essentially
-- axiom-free (`[propext]`): they are closed `Expr` computations.
#print axioms Lean4Lean.VExpr.WF.mkApps_head
#print axioms Lean4Lean.TrExprS.mkApps
#print axioms Lean4Lean.VEnv.IsDefEqU.mkApps_congr_head
#print axioms Lean4Lean.TrExprS.weak_nil
#print axioms Lean4Lean.TrExprS.instL_weak
#print axioms LeanToLambdaBox.iotaConsistent_of_shape
#print axioms LeanToLambdaBox.betaN_casesOn_guard
#print axioms LeanToLambdaBox.betaN_ruleTemplate_guard

-- ============================================================================
-- ι Task 3: the ι forward simulation (`ErasesCorrectIota.lean`), the `casesOn`-spine
-- erasure inversion (`ErasesCorrectData.lean`), the relocated closedness/de-Bruijn kit
-- (`Closed.lean`), and the Γ-population coherence discharge (`EnvErasureNonrec.lean`).
--
-- The `LBTerm` layers must be **sorryAx-free**: `Closed.lean` touches only `LBTerm`,
-- never `TrExprS`, so `LBClosed`'s metatheory and the general de Bruijn commutation kit
-- (`subst_subst` and friends) carry nothing beyond `propext`/`Quot.sound`. Everything
-- that mentions `Erases`/`TrExprS` inherits `sorryAx` from lean4lean's `TrProj`
-- placeholder — the pre-existing boundary, no new gap.
--
-- `IotaConsistent`, `PatsIotaSpec`, `IotaShape`, `IotaRelevant`, `ClosedEnv`,
-- `ErasesEnvCasesι`, `FlatCaseFields`, `CtorFieldsCoherent`, `IotaArityCoherent` are all
-- HYPOTHESES (Props with constructed guards where constructible), never axioms, so they
-- add nothing to any axiom set below.
-- ============================================================================

-- The de Bruijn / closedness kit: pure LBTerm, must be sorryAx-free.
#print axioms LeanToLambdaBox.LBClosed.mono
#print axioms LeanToLambdaBox.LBClosed.shift
#print axioms LeanToLambdaBox.LBClosed.subst
#print axioms LeanToLambdaBox.LBClosed.subst1
#print axioms LeanToLambdaBox.LBClosed.substList
#print axioms LeanToLambdaBox.LBClosed.mkApps
#print axioms LeanToLambdaBox.LBClosed.mkApps_inv
#print axioms LeanToLambdaBox.LBClosed.mkLambdas
#print axioms LBTerm.shift_shift
#print axioms LBTerm.subst_shift_cancel
#print axioms LBTerm.subst_shift_comm
#print axioms LBTerm.subst_subst

-- `NoBlock`/`NoFix` now traverse `.case`; their shift/subst preservation must stay
-- sorryAx-free (pure LBTerm).
#print axioms LeanToLambdaBox.noBlock_shift
#print axioms LeanToLambdaBox.noBlock_subst
#print axioms LeanToLambdaBox.noFix_shift
#print axioms LeanToLambdaBox.noFix_subst

-- A6ι: the `casesOn`-spine erasure inversion and its exact-arity corollary.
-- Spine injectivity is pure `Expr` combinatorics (sorryAx-free); the inversions
-- themselves inherit `sorryAx` via `Erases`/`TrExprS`.
#print axioms LeanToLambdaBox.foldl_app_const_inj
#print axioms LeanToLambdaBox.Erases.app_inv_t
#print axioms LeanToLambdaBox.Erases.const_inv_full
#print axioms LeanToLambdaBox.Erases.cases_spine_inv
#print axioms LeanToLambdaBox.Erases.iota_redex_inv

-- C2, with `IotaConsistent` discharged, and the extracted ι reduct step.
#print axioms LeanToLambdaBox.SEvalDataι_iota_reduct
#print axioms LeanToLambdaBox.SEvalDataι_defeq_of_shape

-- The two-stage `IotaShape` guards (closed `Expr` computations, `rfl`).
#print axioms LeanToLambdaBox.betaN_ruleTemplate_eta_guard
#print axioms LeanToLambdaBox.betaN_ruleTemplate_rec_guard

-- C3: the ι forward simulation on the flat fragment, and the source-side elimination
-- it rests on. No axiom of ours.
#print axioms LeanToLambdaBox.SEvalDataι_partial_cases_lam_elim
#print axioms LeanToLambdaBox.erases_correct_dataι

-- Γ-population coherence: the non-Prop conjunct and the `CtorFieldsCoherent` discharge,
-- plus the constructed non-vacuity guards for every ι side condition except
-- `IotaRelevant` (see `ErasesCorrectIota.lean` for why that one has none at this pin).
#print axioms LeanToLambdaBox.ErasesEnvCases.nonProp
#print axioms LeanToLambdaBox.ctorFieldsCoherent_of_registered
#print axioms LeanToLambdaBox.gΓι_ctorFieldsCoherent
#print axioms LeanToLambdaBox.gΓι_iotaArityCoherent
#print axioms LeanToLambdaBox.gΓι_nonProp
#print axioms LeanToLambdaBox.gΓflat_flat
#print axioms LeanToLambdaBox.gΓflat_erasesEnvCasesι
#print axioms LeanToLambdaBox.gΓflat_ctorFieldsCoherent
#print axioms LeanToLambdaBox.gΓflat_iotaArityCoherent
#print axioms LeanToLambdaBox.gEcl_closedEnv
