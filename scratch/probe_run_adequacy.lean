import Lean4Lean.Verify.TypeChecker
import Lean4Lean.Verify.NameGenerator

/-!
# PROBE P1 (GO/NO-GO): generalize `M.WF.run` to an ambient MLCtx

lean4lean's `M.WF.run` is stated only for the EMPTY local context
(`VContext.mk'` fixes `mlctx := .nil`, so `lctx = {}`). The shipping oracle
runs `isErasable` in the *ambient* `LocalContext` with declaration-level
`lparams`. This probe checks — with ALL-PUBLIC lean4lean ingredients, no fork —
that we can:

1. build a `VContext` from an ambient `MLCtx` (`VContext.ofMLCtx`);
2. prove the initial `VState` (`{}`, whose `ngen` is the kernel's
   `_kernel_fresh` generator) is `VState.WF` at that ambient context, given the
   single premise that every ambient fvar is `kernelNGen.Reserves` (vacuous for
   the `_uniq`-named fvars real `CoreM` produces);
3. transplant lean4lean's 7-line `M.WF.run` proof with `.empty → .initial`.

If any ingredient is non-public / a defeq mismatch blocks it: STOP (fork).
-/

namespace Lean4Lean.TypeChecker

open Lean hiding Environment Exception
open Kernel
open Lean4Lean

/-- The kernel type-checker's initial name generator (the default `State.ngen`). -/
def kernelNGen : NameGenerator := { namePrefix := `_kernel_fresh, idx := 0 }

/-- **Ingredient 1.** Build a `VContext` at an *arbitrary* ambient `MLCtx` `m`
(not just `.nil`), from a `VEnvs.WF` witness. All fields come straight from the
`VEnvs.WF` bundle + the supplied `m.WF`; `lctx := m.lctx`, `lctx_eq := rfl`. -/
def VContext.ofMLCtx {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (safety : DefinitionSafety := .safe) (lparams : List Name := [])
    (m : MLCtx) (mwf : m.WF (ves.venv safety) lparams) : VContext where
  env; safety; lparams
  lctx := m.lctx
  venv := ves.venv safety
  hasPrimitives := wf.hasPrimitives
  safePrimitives := wf.safePrimitives
  trenv := wf.tr
  mlctx := m
  mlctx_wf := mwf
  lctx_eq := rfl

/-- **Ingredient 2.** The initial `VState` (`{}`) is `VState.WF` at an ambient
`VContext.ofMLCtx`, provided every ambient fvar is reserved by `kernelNGen`
(the initial state's `ngen`). Transplant of `VState.WF.empty` with `.nil → m`:
`trctx` becomes `c.trlctx` (generic), the two `Reserves` obligations become the
`hfresh` premise, and `ectx` is witnessed at `Δ' := c.vlctx` (reflexive
`FVLift'`, empty `eqvManager`) instead of `[]`. -/
theorem VState.WF.initial {env : Environment} {ves : VEnvs} {wf : ves.WF env}
    {safety : DefinitionSafety} {lparams : List Name}
    {m : MLCtx} {mwf : m.WF (ves.venv safety) lparams}
    (hfresh : ∀ fv ∈ m.vlctx.fvars, kernelNGen.Reserves fv) :
    VState.WF (.ofMLCtx wf safety lparams m mwf) {} where
  trctx := (VContext.ofMLCtx wf safety lparams m mwf).trlctx
  ngen_wf := hfresh
  ectx := ⟨_, .refl, (VContext.ofMLCtx wf safety lparams m mwf).Δwf, .refl,
    .empty, hfresh⟩
  inferTypeI_wf := .empty
  inferTypeC_wf := .empty
  whnfCore_wf := .empty
  whnf_wf := .empty
  unfold_wf _ := by simp

/-- **Ingredient 3.** `M.WF.run` generalized to the ambient local context
`m.lctx`. Byte-for-byte the lean4lean proof, with the initial-state witness
`.empty` replaced by `.initial hfresh`. -/
theorem M.WF.run' {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {safety : DefinitionSafety} {lparams : List Name}
    {m : MLCtx} (mwf : m.WF (ves.venv safety) lparams)
    (hfresh : ∀ fv ∈ m.vlctx.fvars, kernelNGen.Reserves fv)
    {x : M α} {Q} (H : x.WF (.ofMLCtx wf safety lparams m mwf) {} fun a _ => Q a) :
    (M.run env safety m.lctx lparams x).WF Q := by
  intro a eq
  simp [M.run, Functor.map, Except.map] at eq
  split at eq <;> cases eq; rename_i eq
  let ⟨_, _, _, _, H⟩ := H (VState.WF.initial hfresh) _ _ eq
  exact H

end Lean4Lean.TypeChecker

-- GO check: axiom audit — must be lean4lean's set only, nothing new of ours.
#print axioms Lean4Lean.TypeChecker.VContext.ofMLCtx
#print axioms Lean4Lean.TypeChecker.VState.WF.initial
#print axioms Lean4Lean.TypeChecker.M.WF.run'
