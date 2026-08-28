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
  (`ves.WF env₀`), *and* that scope is the ambient one. This is the residual
  assumption: only the reflection of impure `CoreM`/`MetaM` plumbing onto the pure
  `M.run` — its **soundness is proved**, via `kernel_isErasable_sound`; or
* **`Meta` fallback** — the elaborator-based `isErasableMeta` fallback fired, whose
  soundness is *still assumed* (it has no verified counterpart).

`ResidualHyps.toBridgeHyps` composes these into a full `BridgeHyps`, discharging
the kernel branch and leaving only the reflection + fallback as trust. The gain:
the previous batch's verified relevance check (`isErasable.WF`) is now **plugged
into** the bridge, not merely assumed alongside it.

Trust boundary: `kernel_isErasable_sound`'s (lean4lean's) axioms; no new `axiom`
or `sorry`.

## Where the verified branch stops, and why (slice Γ-U2)

`BridgeHyps.orc_run`'s scope guard is `ctx.lparams <+: Us` since Γ-U2, because
`BridgeInv.lparams` carries a prefix and a dependency's sub-run reads its own
`ci.levelParams`. The kernel branch **cannot** follow it there, and the reason is not a
missing lemma. `kernel_isErasable_sound` concludes `Erasable env lparams.length …` from
`m.WF env lparams` and `TrExprS env lparams m.vlctx e ve` — everything at the scope the
checker ran in — while the box arm that consumes `orc_run` holds both at the *ambient*
`Us`. Moving them down to `ctx.lparams` is a *strengthening*: a term that translates at
`Us` need not translate at a proper prefix of it, since it may mention a parameter the
prefix does not resolve. The Γ-U1 kit (`ErasesLevels`) transports in the other direction
only, and here the two directions are needed at once — the clause is contravariant in
`TrExprS` and covariant in `Erasable`.

So `orc_refl`'s kernel disjunct carries `ctx.lparams = Us` as a conjunct, and a
strict-prefix reader lands in the assumed-sound `Meta` fallback. That is the whole of
what Γ-U2 costs on the oracle, stated where it is paid rather than hidden in the guard:
**at `Us = []` nothing moved** (`<+:` is `=` there, `List.prefix_nil`), and at `Us ≠ []`
the verified relevance check still covers every run at the subject's own scope — what it
stops covering is a dependency erased at a *strictly* narrower one.
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
    (b = true → ctx.lparams <+: Us →
      -- kernel reflection: the pure verified checker returned `true` at the same
      -- local context / level params, over the modelled environment `env₀` — and the
      -- run's level scope *is* the ambient one. The equation is not decoration: the
      -- adequacy theorem concludes at the scope it ran in, and the consumer's `TrExprS`
      -- witness lives at `Us` (slice Γ-U2's one cost; see the module docstring).
      (ctx.lparams = Us ∧ M.run env₀ .safe ctx.lctx ctx.lparams
          (x := RecM.run (LeanToLambdaBox.isErasable e)) = .ok true)
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
    ¬ (gw w).Reserves x ∧ (gw w₁).Reserves x ∧ gw w ≤ gw w₁ ∧
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
    rcases hsound hb hlp with ⟨heq, hker⟩ | hfb
    · -- kernel reflection ⟹ soundness, via the verified checker adequacy
      subst heq
      exact kernel_isErasable_sound wf mwf hkf htr (by rw [hlctx]; exact hker)
    · -- `Meta` fallback: assumed sound
      exact hfb m ve mwf hlctx hkf htr
  fresh_run := R.fresh_run
  cases_run := R.cases_run
  ctor_run := R.ctor_run

end LeanToLambdaBox
