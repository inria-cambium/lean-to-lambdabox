import LeanToLambdaBox.ErasureRun
import LeanToLambdaBox.ErasureContext
import Lean4Lean.Verify.NameGenerator

/-!
# The data-fragment trust bundle: `DataBridgeHyps`

This structure sits *beside* `BridgeHyps` (`VisitExprRefines.lean`) and carries the
Hoare-style specifications the `visitExpr`→`Erases` bridge needs to cover the
**saturated-constructor** fragment (`Supported.ctorApp`, `Bridge.lean`) — the A8
extension of the β+δ bridge to first-order data.

Six clauses, over the same ghost world-measure `gw : Void IO.RealWorld →
NameGenerator` used by `BridgeHyps`. All the runtime primitives they spec
(`getCtorArity?`, `getConstInfo`, `register_inductive`, `getEnv`, `Meta.inferType`)
are **real** — not part of the `visitExpr` mutual block — so their Hoare specs are
usable directly inside the fixpoint induction (whose step sees the erasure family's
bodies with the *approximation* functions in place of the recursive calls, but the
external primitives unchanged).

* `ctor_run` — `getCtorArity?` is *positive* on a registered constructor: returns
  `Γ.ctorArities`' declared arity (`BridgeHyps.ctor_run` gave only the negative
  direction). Generator-monotone.
* `ctorinfo_run` / `indinfo_run` — `getConstInfo cn` / `getConstInfo info.induct`
  return the constructor's `ctorInfo` (with `cidx` matching `Γ`) / the inductive's
  `inductInfo`. Monotone.
* `reg_run` — `register_inductive` returns `Γ`'s `InductiveId` (`indid = iid`) and a
  *trivial* argmask, so the `param ++ filter mask fields ++ extra` slice reconstructs
  `args` (holds on the data fragment: relevant fields, default
  `remove_irrel_constr_args := false`, pre-registered inductive). Monotone.
* `extern_run` — a registered constructor is not `@[extern]` (`isExtern env cn =
  false`), killing `visitConstructor`'s `@[extern]`-axiom short-circuit. Monotone.
* `infer_run` — `Meta.inferType` (in `visitCtorEta`, to drive η-expansion) is
  generator-monotone (state-preservation is derivable via `run_liftMetaM_state`).
  An elaborator-correctness assumption, same epistemic class as `BridgeHyps.orc_run`.

Because these quantify over opaque runtime primitives, their global satisfiability is
not in-logic decidable — this is the documented trust boundary of the data bridge,
exactly as for `BridgeHyps`. (The `nat := .machine` special-casing of `Nat.zero` /
`Nat.succ` is killed *purely*, by the `cn ≠ ``Nat.zero``/`Nat.succ`` premises of the
supported `ctorApp` rule — no assumption needed.)

## Trust-surface reductions (cold-start S2)

**Four state clauses removed, none replaced.** Every `s = s₁` conjunct this bundle used
to carry is gone:

* `ctorinfo_run`, `indinfo_run` — *provable*, `Erasure.run_getConstInfo_state`;
  `extern_run` — *provable*, `Erasure.run_getEnv_state`. Assuming them was redundant;
  the bridge now derives them.
* `reg_run` — **it was false.** `s` is universally quantified and `indinfo`
  unconstrained, so the clause asserted `register_inductive` is state-preserving from
  *every* state, for *every* inductive; `Erasure.run_register_inductive_cold_ok` shows
  the miss branch conses one `.inductiveDecl` (plus one axiom per `@[extern]`
  constructor). What replaces it is not an assumption but a theorem,
  `Erasure.run_register_inductive_runConcl` (`RunConcl s s₁`: hit branch preserves —
  R5 — and miss branch only grows — R4), which is what the bridge threads now. The
  clause is *not* re-added under a pre-registration precondition: the call sites cannot
  establish one, and the remaining content (`r.1 = iid`, the trivial argmask) is
  branch-independent.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure

/-- The data-fragment trust bundle (see module docstring). -/
structure DataBridgeHyps (Γ : ErasureCtx) (gw : Void IO.RealWorld → NameGenerator) : Prop where
  /-- `getCtorArity?` on a registered constructor returns its declared arity
  (`Γ.ctorArities`), and advances the generator monotonically. -/
  ctor_run : ∀ (n : Name) (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) (r : Option Nat) (w₁ : Void IO.RealWorld),
    Lean.Compiler.LCNF.getCtorArity? n cctx ref w = .ok r w₁ →
    gw w ≤ gw w₁ ∧
    (∀ iid cidx ar, Γ.ctors n = some (iid, cidx) → Γ.ctorArities n = some ar → r = some ar)
  /-- `getConstInfo cn` on a registered constructor returns its `ctorInfo` (whose
  `cidx` matches `Γ`), advancing the generator monotonically.
  (The `getConstInfo`/`register_inductive` runtime primitives are real — not part of
  the `visitExpr` mutual block — so these Hoare specs are usable inside the fixpoint
  induction.)

  State-preservation is **not** assumed: it is the theorem
  `Erasure.run_getConstInfo_state`. -/
  ctorinfo_run : ∀ (cn : Name) (iid : InductiveId) (cidx : Nat)
    (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (ci : ConstantInfo)
    (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    Γ.ctors cn = some (iid, cidx) →
    (getConstInfo cn : EraseM ConstantInfo) s ctx cctx ref w = .ok (ci, s₁) w₁ →
    gw w ≤ gw w₁ ∧ ∃ info : ConstructorVal, ci = .ctorInfo info ∧ info.cidx = cidx
  /-- `getConstInfo (info.induct)` on a registered constructor's inductive returns its
  `inductInfo`, monotonically (state-preservation is `Erasure.run_getConstInfo_state`). -/
  indinfo_run : ∀ (cn : Name) (iid : InductiveId) (cidx : Nat) (info : ConstructorVal)
    (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (ci : ConstantInfo)
    (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    Γ.ctors cn = some (iid, cidx) →
    (getConstInfo info.induct : EraseM ConstantInfo) s ctx cctx ref w = .ok (ci, s₁) w₁ →
    gw w ≤ gw w₁ ∧ ∃ indinfo : InductiveVal, ci = .inductInfo indinfo
  /-- `register_inductive indinfo` returns the constructor's `Γ`-`InductiveId`,
  monotonically; and on the data fragment (relevant fields, default
  `remove_irrel_constr_args := false`) the produced argmask is *trivial*, so the
  constructor's `param ++ filter mask fields ++ extra` slice reconstructs `args`.

  **No state clause.** The one this field used to carry (`s = s₁`, unconditionally over
  `s` and `indinfo`) is refuted by `Erasure.run_register_inductive_cold_ok`; the true
  state effect is the theorem `Erasure.run_register_inductive_runConcl`. See the module
  docstring. -/
  reg_run : ∀ (indinfo : InductiveVal) (info : ConstructorVal) (cn : Name)
    (iid : InductiveId) (cidx : Nat) (args : Array Expr)
    (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld)
    (r : InductiveId × InductiveArgMasks) (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    Γ.ctors cn = some (iid, cidx) → info.cidx = cidx →
    register_inductive indinfo s ctx cctx ref w = .ok (r, s₁) w₁ →
    gw w ≤ gw w₁ ∧ r.1 = iid ∧
    (Std.Slice.toArray (args.toSubarray 0 info.numParams)
      ++ filter (r.2[cidx]!) ↑(args.toSubarray info.numParams (info.numParams + info.numFields))
      ++ Std.Slice.toArray (args.toSubarray (info.numParams + info.numFields))) = args
  /-- A registered constructor is not `@[extern]`, so `visitConstructor`'s
  `@[extern]`-axiom short-circuit is dead (`isExtern env cn = false`). `getEnv` is
  monotone (state-preservation is the theorem `Erasure.run_getEnv_state`). -/
  extern_run : ∀ (cn : Name) (iid : InductiveId) (cidx : Nat)
    (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (env : Lean.Environment)
    (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    Γ.ctors cn = some (iid, cidx) →
    (getEnv : EraseM Lean.Environment) s ctx cctx ref w = .ok (env, s₁) w₁ →
    gw w ≤ gw w₁ ∧ isExtern env cn = false
  /-- `Meta.inferType` (run by `visitCtorEta`) advances the generator monotonically. -/
  infer_run : ∀ (e : Expr) (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (ty : Expr)
    (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    Erasure.liftMetaM (Lean.Meta.inferType e) s ctx cctx ref w = .ok (ty, s₁) w₁ →
    gw w ≤ gw w₁

end LeanToLambdaBox
