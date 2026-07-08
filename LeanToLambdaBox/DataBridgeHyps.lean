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
  `inductInfo`. State-preserving, monotone.
* `reg_run` — `register_inductive` returns `Γ`'s `InductiveId` (`indid = iid`) and a
  *trivial* argmask, so the `param ++ filter mask fields ++ extra` slice reconstructs
  `args` (holds on the data fragment: relevant fields, default
  `remove_irrel_constr_args := false`, pre-registered inductive). State-preserving,
  monotone.
* `extern_run` — a registered constructor is not `@[extern]` (`isExtern env cn =
  false`), killing `visitConstructor`'s `@[extern]`-axiom short-circuit. `getEnv`
  state-preserving, monotone.
* `infer_run` — `Meta.inferType` (in `visitCtorEta`, to drive η-expansion) is
  generator-monotone (state-preservation is derivable via `run_liftMetaM_state`).
  An elaborator-correctness assumption, same epistemic class as `BridgeHyps.orc_run`.

Because these quantify over opaque runtime primitives, their global satisfiability is
not in-logic decidable — this is the documented trust boundary of the data bridge,
exactly as for `BridgeHyps`. (The `nat := .machine` special-casing of `Nat.zero` /
`Nat.succ` is killed *purely*, by the `cn ≠ ``Nat.zero``/`Nat.succ`` premises of the
supported `ctorApp` rule — no assumption needed.)
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
  `cidx` matches `Γ`), advancing the generator monotonically and preserving state.
  (The `getConstInfo`/`register_inductive` runtime primitives are real — not part of
  the `visitExpr` mutual block — so these Hoare specs are usable inside the fixpoint
  induction.) -/
  ctorinfo_run : ∀ (cn : Name) (iid : InductiveId) (cidx : Nat)
    (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (ci : ConstantInfo)
    (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    Γ.ctors cn = some (iid, cidx) →
    (getConstInfo cn : EraseM ConstantInfo) s ctx cctx ref w = .ok (ci, s₁) w₁ →
    gw w ≤ gw w₁ ∧ s = s₁ ∧ ∃ info : ConstructorVal, ci = .ctorInfo info ∧ info.cidx = cidx
  /-- `getConstInfo (info.induct)` on a registered constructor's inductive returns its
  `inductInfo`, monotone and state-preserving. -/
  indinfo_run : ∀ (cn : Name) (iid : InductiveId) (cidx : Nat) (info : ConstructorVal)
    (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (ci : ConstantInfo)
    (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    Γ.ctors cn = some (iid, cidx) →
    (getConstInfo info.induct : EraseM ConstantInfo) s ctx cctx ref w = .ok (ci, s₁) w₁ →
    gw w ≤ gw w₁ ∧ s = s₁ ∧ ∃ indinfo : InductiveVal, ci = .inductInfo indinfo
  /-- `register_inductive indinfo` returns the constructor's `Γ`-`InductiveId`, monotone
  and state-preserving; and on the data fragment (relevant fields, default
  `remove_irrel_constr_args := false`, pre-registered inductive) the produced argmask
  is *trivial*, so the constructor's `param ++ filter mask fields ++ extra` slice
  reconstructs `args`. -/
  reg_run : ∀ (indinfo : InductiveVal) (info : ConstructorVal) (cn : Name)
    (iid : InductiveId) (cidx : Nat) (args : Array Expr)
    (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld)
    (r : InductiveId × InductiveArgMasks) (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    Γ.ctors cn = some (iid, cidx) → info.cidx = cidx →
    register_inductive indinfo s ctx cctx ref w = .ok (r, s₁) w₁ →
    gw w ≤ gw w₁ ∧ s = s₁ ∧ r.1 = iid ∧
    (Std.Slice.toArray (args.toSubarray 0 info.numParams)
      ++ filter (r.2[cidx]!) ↑(args.toSubarray info.numParams (info.numParams + info.numFields))
      ++ Std.Slice.toArray (args.toSubarray (info.numParams + info.numFields))) = args
  /-- A registered constructor is not `@[extern]`, so `visitConstructor`'s
  `@[extern]`-axiom short-circuit is dead (`isExtern env cn = false`). `getEnv` is
  monotone and state-preserving. -/
  extern_run : ∀ (cn : Name) (iid : InductiveId) (cidx : Nat)
    (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (env : Lean.Environment)
    (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    Γ.ctors cn = some (iid, cidx) →
    (getEnv : EraseM Lean.Environment) s ctx cctx ref w = .ok (env, s₁) w₁ →
    gw w ≤ gw w₁ ∧ s = s₁ ∧ isExtern env cn = false
  /-- `Meta.inferType` (run by `visitCtorEta`) advances the generator monotonically. -/
  infer_run : ∀ (e : Expr) (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (ty : Expr)
    (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    Erasure.liftMetaM (Lean.Meta.inferType e) s ctx cctx ref w = .ok (ty, s₁) w₁ →
    gw w ≤ gw w₁

end LeanToLambdaBox
