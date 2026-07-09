import LeanToLambdaBox
/-! Final axiom audit for the dev/verify verification stack (2026-07-07).
Allowed: ⊆ [propext, sorryAx, Classical.choice, Quot.sound] + lean4lean's
modeling axioms (Verify/Axioms.lean) where the executable checker/Expr model
is involved. The pure-LBTerm layers must be sorryAx-free. -/

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
-- nothing to the axiom set. (No `erases_correct_dataι`: the general ι forward
-- simulation is falsified by the under-constrained `Erases.cases` — see
-- `SubjectReductionIota.lean`'s C3 finding.)
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
