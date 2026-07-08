import LeanToLambdaBox.RelevanceCheck
import Lean4Lean.Verify.TypeChecker
import Lean4Lean.Verify.NameGenerator

/-!
# Run-adequacy of the verified relevance check at an ambient local context

`RelevanceCheck.lean` proves `isErasable.WF`: lean4lean's *verified* relevance
check, when it returns `true` on a translated term, witnesses `Erasable`. But
that lemma is phrased against an abstract `VContext`/`VState`; the shipping
oracle actually executes `Lean4Lean.TypeChecker.M.run … (RecM.run (isErasable e))`
in the **ambient** `LocalContext` with the definition's `levelParams`.

lean4lean's `M.WF.run` connects `M.WF` to a *successful* `M.run`, but only for the
**empty** local context (`VContext.mk'` hardwires `mlctx := .nil`). This file
lifts that restriction *without forking lean4lean* — every ingredient is public:

* `VContext.ofMLCtx` — a `VContext` at an arbitrary ambient `MLCtx` (not `.nil`);
* `VState.WF.initial` — the initial `VState` (`{}`, whose `ngen` is the kernel's
  `_kernel_fresh` generator) is `VState.WF` at that ambient context, given only
  that every ambient fvar is `kernelNGen.Reserves` — which is *vacuous* for the
  `_uniq`-named fvars a real `CoreM` produces (`Reserves` for an `idx = 0`
  generator only constrains `.num _kernel_fresh _`-shaped names);
* `M.WF.run'` — lean4lean's 7-line `M.WF.run`, transplanted with `.empty →
  `.initial`;
* `kernel_isErasable_sound` — the payoff: a pure `M.run` of the verified check
  returning `.ok true` at a translated ambient `MLCtx` entails `Erasable`.

No new `axiom`/`sorry`: the trust inherited is exactly lean4lean's (its `Verify`
`sorryAx` on `TrProj`, and its `Expr`/`Level`/`PersistentHashMap`/`PersistentArray`
modeling axioms surfaced through the executable checker).
-/

namespace Lean4Lean.TypeChecker

open Lean hiding Environment Exception
open Kernel
open Lean4Lean
open LeanToLambdaBox (Erasable)

/-- The kernel type-checker's initial name generator (the default `State.ngen`,
`Lean4Lean.TypeChecker.State`). `Reserves` for this generator (`idx = 0`) holds
of every fvar *not* of the shape `⟨.num `_kernel_fresh i⟩` — in particular of
every `_uniq`-named runtime fvar. -/
def kernelNGen : NameGenerator := { namePrefix := `_kernel_fresh, idx := 0 }

/-- Build a `VContext` at an *arbitrary* ambient `MLCtx` `m` (not just `.nil`),
from a `VEnvs.WF` witness. Everything but `mlctx`/`lctx` is the `VContext.mk'`
data; `lctx := m.lctx`, `lctx_eq := rfl`. -/
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

@[simp] theorem VContext.ofMLCtx_venv {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {safety : DefinitionSafety} {lparams : List Name}
    {m : MLCtx} (mwf : m.WF (ves.venv safety) lparams) :
    (VContext.ofMLCtx wf safety lparams m mwf).venv = ves.venv safety := rfl

@[simp] theorem VContext.ofMLCtx_lparams {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {safety : DefinitionSafety} {lparams : List Name}
    {m : MLCtx} (mwf : m.WF (ves.venv safety) lparams) :
    (VContext.ofMLCtx wf safety lparams m mwf).lparams = lparams := rfl

@[simp] theorem VContext.ofMLCtx_vlctx {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {safety : DefinitionSafety} {lparams : List Name}
    {m : MLCtx} (mwf : m.WF (ves.venv safety) lparams) :
    (VContext.ofMLCtx wf safety lparams m mwf).vlctx = m.vlctx := rfl

/-- The initial `VState` (`{}`) is `VState.WF` at an ambient `VContext.ofMLCtx`,
provided every ambient fvar is reserved by `kernelNGen` (the initial state's
`ngen`). Transplant of `VState.WF.empty` with `.nil → m`: `trctx` becomes the
generic `c.trlctx`, the two `Reserves` obligations become the `hfresh` premise,
and `ectx` is witnessed at `Δ' := c.vlctx` (reflexive `FVLift'`, empty
`eqvManager`) instead of `[]`. -/
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

/-- `M.WF.run` generalized to the ambient local context `m.lctx`. Byte-for-byte
the lean4lean proof, with the initial-state witness `.empty` replaced by
`.initial hfresh`. -/
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

/-- **The kernel path of the relevance oracle is sound.** A pure run of
lean4lean's *verified* relevance check (`LeanToLambdaBox.isErasable`) via
`M.run` at the ambient local context `m.lctx` with the declaration's `lparams`,
returning `.ok true` on a term `e` that translates to `ve`, witnesses that `ve`
is `Erasable`. Composition of `isErasable.WF` (soundness), `RecM.WF.run` (fuel),
and `M.WF.run'` (run-adequacy at the ambient context). -/
theorem kernel_isErasable_sound {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {safety : DefinitionSafety} {lparams : List Name}
    {m : MLCtx} (mwf : m.WF (ves.venv safety) lparams)
    (hfresh : ∀ fv ∈ m.vlctx.fvars, kernelNGen.Reserves fv)
    {e : Expr} {ve : VExpr}
    (he : TrExprS (ves.venv safety) lparams m.vlctx e ve)
    (hrun : M.run env safety m.lctx lparams
      (RecM.run (LeanToLambdaBox.isErasable e)) = .ok true) :
    Erasable (ves.venv safety) lparams.length m.vlctx.toCtx ve :=
  M.WF.run' wf mwf hfresh
    (RecM.WF.run (LeanToLambdaBox.isErasable.WF (c := .ofMLCtx wf safety lparams m mwf) he))
    true hrun rfl

end Lean4Lean.TypeChecker
