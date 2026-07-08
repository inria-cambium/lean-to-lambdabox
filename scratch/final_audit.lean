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

-- WS-O: oracle-discharge stack (run-adequacy at ambient MLCtx + the discharge).
#print axioms Lean4Lean.TypeChecker.VContext.ofMLCtx
#print axioms Lean4Lean.TypeChecker.VState.WF.initial
#print axioms Lean4Lean.TypeChecker.M.WF.run'
#print axioms Lean4Lean.TypeChecker.kernel_isErasable_sound
#print axioms ResidualHyps.toBridgeHyps
#print axioms shipping_visitExpr_correct'
