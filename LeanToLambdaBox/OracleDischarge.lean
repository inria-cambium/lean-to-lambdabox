import LeanToLambdaBox.VisitExprRefines

/-!
# Discharging the oracle's kernel path: `ResidualHyps ⟹ BridgeHyps`

`BridgeHyps.orc_run` assumes the relevance oracle is *sound*: a `true` verdict
means the term is `Erasable`. This file shrinks that assumption. It defines
`ResidualHyps`, a **strictly smaller trust bundle** in which the oracle's kernel
path is trusted only to *reflect* the pure verified checker run — and then
**proves** its soundness from `kernel_isErasable_sound` (`CheckerAdequacy.lean`,
itself `isErasable.WF` + the generalized `M.WF.run'`).

Concretely, `ResidualHyps.orc_refl` says a `true` verdict entails a *disjunction*:

* **kernel reflection** — the outer, impure `liftMetaM (isErasable ctx.lparams e)`
  run reflects a *pure* `M.run … (isErasable e) = .ok true` at the *same* local
  context and level params, over a lean4lean-modelled environment
  (`ves.WF env₀`). This is the residual assumption: only the reflection of impure
  `CoreM`/`MetaM` plumbing onto the pure `M.run` — its **soundness is proved**,
  via `kernel_isErasable_sound`; or
* **`Meta` fallback** — the elaborator-based `isErasableMeta` fallback fired, whose
  soundness is *still assumed* (it has no verified counterpart).

`ResidualHyps.toBridgeHyps` composes these into a full `BridgeHyps`, discharging
the kernel branch and leaving only the reflection + fallback as trust. The gain:
the previous batch's verified relevance check (`isErasable.WF`) is now **plugged
into** the bridge, not merely assumed alongside it.

Trust boundary: `kernel_isErasable_sound`'s (lean4lean's) axioms; no new `axiom`
or `sorry`.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure
open Lean4Lean.TypeChecker (MLCtx kernelNGen M RecM kernel_isErasable_sound)

/-- The residual trust bundle: like `BridgeHyps`, but the oracle's soundness is
*not* assumed. Instead `orc_refl` records that a `true` verdict either **reflects**
a pure verified `M.run` returning `.ok true` (soundness then *proved*), or comes
from the assumed-sound `Meta` fallback. Parameterised by the lean4lean environment
model `env₀ : Lean.Kernel.Environment` / `ves : VEnvs` (the `BridgeHyps`' `VEnv` is
recovered as `ves.venv .safe`). -/
structure ResidualHyps (env₀ : Lean.Kernel.Environment) (ves : VEnvs) (Us : List Name)
    (Γ : ErasureCtx) (gw : Void IO.RealWorld → NameGenerator) : Prop where
  orc_refl : ∀ (e : Expr) (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (b : Bool)
    (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    Erasure.liftMetaM (Erasure.isErasable ctx.lparams e) s ctx cctx ref w = .ok (b, s₁) w₁ →
    gw w ≤ gw w₁ ∧
    (b = true → ctx.lparams = Us →
      -- kernel reflection: the pure verified checker returned `true` at the same
      -- local context / level params, over the modelled environment `env₀`.
      (M.run env₀ .safe ctx.lctx ctx.lparams
          (RecM.run (LeanToLambdaBox.isErasable e)) = .ok true)
      ∨
      -- `Meta` fallback: soundness assumed (no verified counterpart).
      (∀ (m : MLCtx) (ve : VExpr), m.WF (ves.venv .safe) Us → m.lctx = ctx.lctx →
        (∀ fv ∈ m.vlctx.fvars, kernelNGen.Reserves fv) →
        TrExprS (ves.venv .safe) Us m.vlctx e ve →
        Erasable (ves.venv .safe) Us.length m.vlctx.toCtx ve))
  fresh_run : ∀ (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (x : FVarId)
    (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    (mkFreshFVarId : EraseM FVarId) s ctx cctx ref w = .ok (x, s₁) w₁ →
    s₁ = s ∧ ¬ (gw w).Reserves x ∧ (gw w₁).Reserves x ∧ gw w ≤ gw w₁ ∧
    kernelNGen.Reserves x
  cases_run : ∀ (n : Name) (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) (r : Option CasesInfo) (w₁ : Void IO.RealWorld),
    getCasesInfo? n cctx ref w = .ok r w₁ →
    gw w ≤ gw w₁ ∧ (Γ.casesOns n = none → r = none)
  ctor_run : ∀ (n : Name) (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) (r : Option Nat) (w₁ : Void IO.RealWorld),
    Lean.Compiler.LCNF.getCtorArity? n cctx ref w = .ok r w₁ →
    gw w ≤ gw w₁ ∧ (Γ.ctors n = none → r = none)

/-- **The oracle-discharge theorem.** From the residual bundle and a lean4lean
environment model `ves.WF env₀`, build a full `BridgeHyps` over the modelled
`VEnv` `ves.venv .safe`. The `orc_run` field's soundness is *proved* on the kernel
branch (via `kernel_isErasable_sound`), assumed only on the `Meta` fallback branch;
the other three fields are inherited verbatim. -/
theorem ResidualHyps.toBridgeHyps {env₀ : Lean.Kernel.Environment} {ves : VEnvs}
    {Us : List Name} {Γ : ErasureCtx} {gw : Void IO.RealWorld → NameGenerator}
    (R : ResidualHyps env₀ ves Us Γ gw) (wf : ves.WF env₀) :
    BridgeHyps (ves.venv .safe) Us Γ gw where
  orc_run e s ctx cctx ref w b s₁ w₁ hrun := by
    obtain ⟨hmono, hsound⟩ := R.orc_refl e s ctx cctx ref w b s₁ w₁ hrun
    refine ⟨hmono, fun hb hlp m ve mwf hlctx hkf htr => ?_⟩
    rcases hsound hb hlp with hker | hfb
    · -- kernel reflection ⟹ soundness, via the verified checker adequacy
      subst hlp
      exact kernel_isErasable_sound wf mwf hkf htr (by rw [hlctx]; exact hker)
    · -- `Meta` fallback: assumed sound
      exact hfb m ve mwf hlctx hkf htr
  fresh_run := R.fresh_run
  cases_run := R.cases_run
  ctor_run := R.ctor_run

end LeanToLambdaBox
