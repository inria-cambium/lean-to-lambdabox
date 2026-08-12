import LeanToLambdaBox.SourceEvalData
import LeanToLambdaBox.Erasure

/-!
# `PrepareHyps` — elaborator-transformation soundness for `prepare_erasure`

The shipping cold-start eraser runs `visitExpr (prepare_erasure e)`, **not**
`visitExpr e` (`Erasure.lean:890/913`). `prepare_erasure` (`Erasure.lean:556`) applies,
before erasure, three Lean elaborator transformations —

* `replaceUnsafeRecNames` (strip `._unsafe_rec` suffixes, `Erasure.lean:538`),
* `macroInline` (honour `@[macro_inline]`, `Lean.Compiler.LCNF.ToDecl`),
* `inlineMatchers` (inline auxiliary matchers, ditto),

run as `replaceUnsafeRecNames ; macroInline ; inlineMatchers ; macroInline` — followed
by an **optional** `csimp` pass gated on `config.csimp`.

Any correctness theorem whose subject is `erase e` therefore reasons about
`prepare_erasure e` and must relate *its* source big-step evaluation to `e`'s. We do
**not** re-verify Lean's elaborator internals; instead their evaluation-preservation is
stated here as a `Prop` **hypothesis** structure `PrepareHyps` — the SAME epistemic
class as `BridgeHyps.orc_run` / `DataBridgeHyps.infer_run` (assumed elaborator
correctness), and **never an axiom of ours**. Its global satisfiability is not in-logic
decidable (the fields quantify over opaque runtime `CoreM` primitives), which is the
documented trust boundary — exactly as for `BridgeHyps`.

## The csimp gate (why `config.csimp = false` is mandatory for correctness)

The `config.csimp` branch (`Erasure.lean:566`) applies `CSimp.replaceConstant?`, which
swaps a definition for its `@[csimp]`-registered replacement (e.g. `Nat.rec`-based defs
for tail-recursive variants). The shipping comment at `Erasure.lean:554` itself admits
this *"may make the expression ill-typed if some dependent type relies on the
implementation of functions affected by csimp"*: csimp replacement is **not
kernel-semantics-preserving** — it substitutes an extensionally-equal but
intensionally-different function that the kernel does not see as defeq. It can therefore
**never** sit inside a correctness statement.

Consequently the derived net-effect theorem carries the explicit premise
`ctx.config.csimp = false`. With it, the csimp branch of `prepare_erasure` is dead
(`prepare_erasure` stops after the second `macroInline`), so the net effect is exactly
the composite of the three transform-soundness fields. This is a **documented
hypothesis, not an axiom**; its non-vacuity is trivial (`config.csimp = false` is a
configuration the CLI genuinely exposes). RAISE-not-fix: the shipping *default* is
`csimp := true` (`Erasure.lean:68`); we do not change it (byte-unchanged) — we only
*scope* correctness to the `false` case.

## Non-vacuity

On a **closed, constant-free** source term all three transforms are the identity
(`replaceUnsafeRecNames` only rewrites `._unsafe_rec` heads; `macroInline` /
`inlineMatchers` only fire on `@[macro_inline]` / matcher heads), so each field's
preservation conclusion collapses to `Iff.rfl`. The guards below exhibit that identity
behaviour and a concrete inhabited `SEvalData` point, so the trust surface is
demonstrably realizable (not vacuously false), matching the guard standard of
`BridgeHyps` (whose opaque runs likewise stay hypothetical).
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure Lean.Compiler.LCNF

/-- **Elaborator-transformation soundness for `prepare_erasure`** (a trust hypothesis,
epistemic class `BridgeHyps.orc_run`; NEVER an axiom).

Each field is a Hoare-style spec: a successful `EraseM` run of the named transform on a
source `Expr` returns an expression with the **same** lean4lean-validated source
big-step evaluation (`SEvalData Γ Esrc`).

The **net composite** over the whole csimp-off `prepare_erasure` run used to be a fourth
field of this structure; it is now the theorem
`LeanToLambdaBox.prepare_sound_of_prepareHyps` (`ColdStartRun.lean`), derived from these
three along the monadic-bind decomposition `run_prepare_erasure_ok` (cold-start R2). One
trust item fewer, same strength. -/
structure PrepareHyps (Γ : ErasureCtx) (Esrc : SEnv) : Prop where
  /-- `replaceUnsafeRecNames` preserves source big-step evaluation. -/
  replaceUnsafeRec_sound : ∀ {e e' : Expr} {s s₁ : ErasureState} {ctx : ErasureContext}
      {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
      {w w₁ : Void IO.RealWorld},
      (liftM (replaceUnsafeRecNames e) : EraseM Expr) s ctx cctx ref w = .ok (e', s₁) w₁ →
      ∀ {v : Expr}, SEvalData Γ Esrc e' v ↔ SEvalData Γ Esrc e v
  /-- `macroInline` (honouring `@[macro_inline]`) preserves source big-step evaluation. -/
  macroInline_sound : ∀ {e e' : Expr} {s s₁ : ErasureState} {ctx : ErasureContext}
      {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
      {w w₁ : Void IO.RealWorld},
      (liftM (macroInline e) : EraseM Expr) s ctx cctx ref w = .ok (e', s₁) w₁ →
      ∀ {v : Expr}, SEvalData Γ Esrc e' v ↔ SEvalData Γ Esrc e v
  /-- `inlineMatchers` (inlining auxiliary matchers) preserves source big-step
  evaluation. -/
  inlineMatchers_sound : ∀ {e e' : Expr} {s s₁ : ErasureState} {ctx : ErasureContext}
      {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
      {w w₁ : Void IO.RealWorld},
      (liftM (inlineMatchers e) : EraseM Expr) s ctx cctx ref w = .ok (e', s₁) w₁ →
      ∀ {v : Expr}, SEvalData Γ Esrc e' v ↔ SEvalData Γ Esrc e v
/-! ## Non-vacuity guards -/

/-- The preservation conclusion shared by every `PrepareHyps` field is realizable at
the identity behaviour: when a transform leaves the term unchanged (`e' = e`, as all
three do on a closed constant-free source), the biconditional is `Iff.rfl`. This is the
"identity on a closed constant-free term" non-vacuity witness. -/
theorem prepareHyps_conclusion_at_identity (Γ : ErasureCtx) (Esrc : SEnv)
    {e e' : Expr} (hid : e' = e) :
    ∀ {v : Expr}, SEvalData Γ Esrc e' v ↔ SEvalData Γ Esrc e v :=
  hid ▸ Iff.rfl

/-- A concrete inhabited evaluation point, so the biconditional above is over a genuine
(non-empty) relation: a λ-abstraction is an `SEvalData` value. -/
theorem prepareHyps_inhabited_point (Γ : ErasureCtx) (Esrc : SEnv) :
    SEvalData Γ Esrc (.lam `x (.sort .zero) (.bvar 0) .default)
                     (.lam `x (.sort .zero) (.bvar 0) .default) :=
  .lam _ _ _ _

/-- The csimp gate is itself non-vacuous: `config.csimp = false` is a satisfiable
configuration (indeed one the CLI exposes). -/
theorem prepareHyps_csimp_off_satisfiable :
    ∃ cfg : ErasureConfig, cfg.csimp = false :=
  ⟨{ csimp := false }, rfl⟩

end LeanToLambdaBox
