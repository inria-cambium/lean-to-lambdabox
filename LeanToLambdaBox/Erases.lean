import LeanToLambdaBox.Basic
import LeanToLambdaBox.Correctness
import LeanToLambdaBox.Erasability
import Lean4Lean.Verify.Typing.Expr

/-!
# Typed erasure relation over real `Lean.Expr` (step A2.1)

This is the grounding re-base of the erasure relation: where the legacy
`_root_.Erases` (in `Correctness.lean`) relates the hand-written IR `CExpr` to
`LBTerm` with a *trivial* box rule, `LeanToLambdaBox.Erases` relates the **real**
`Lean.Expr` to `LBTerm`, and its `box` rule carries a genuine irrelevance witness
phrased over lean4lean's `VExpr` typing (`TrExprS` + `Erasable`).

Both languages are locally-nameless (`bvar`/`fvar`), so they line up
constructor-for-constructor; the typing premise on `box` lives over `VExpr`, so
the relation threads a lean4lean `VLCtx` (extended under binders exactly as
`TrExprS` does).

## Scope (documented, deliberate)

* **Projection-free.** `.proj`/`LBTerm.proj` are excluded *because lean4lean's
  projection translation `TrProj` and `inferProj.WF` are `sorry`* — see memory
  `lean4lean-sorry-boundary`. Including them would make every downstream result
  rest on lean4lean sorries.
* **Constructors / `casesOn` / structural recursion are NOT dedicated rules.**
  In real `Expr` these are applied `.const`s (`List.cons`, `Nat.casesOn`,
  `f._unary`/`brecOn`), detected by the shipping `visitExpr` via environment
  queries that have no place in a `Prop`-valued relation. Here they erase
  *structurally* through `const`/`app` to a `.const`-spine on the target. The
  agreement between that spine and the optimized `.construct`/`.case`/`.fix`
  target nodes the real erasure emits is deferred to Half B
  (`erase_refines_Erases`), where the environment is available.

So this relation covers the projection-free fragment as
`box | bvar | fvar | const | app | lam | letE`.

The legacy `_root_.Erases`/`erase_preservation` are left intact until the new
substitution lemmas and big-step correctness (A2.2–A3) are in place; the cut-over
that retires `CExpr.lean` is a separate, deliberate step.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/--
Typed erasure relation between real `Lean.Expr` and `LBTerm`.

Parameters `env`/`Us`/`Γ` are fixed; the `VLCtx` is an index because binder rules
recurse under an extended context (mirroring `TrExprS.lam`/`letE`). `Γ` resolves
source `Name`s to target `Kername`s as before.
-/
inductive Erases (env : VEnv) (Us : List Name) (Γ : ErasureCtx) :
    VLCtx → Expr → LBTerm → Prop
  /-- Irrelevant subterms erase to `box`, witnessed by a real lean4lean typing
      derivation showing the term is a proof or a type-former. -/
  | box {Δ e ve}
      (htr : TrExprS env Us Δ e ve)
      (her : Erasable env Us.length Δ.toCtx ve) :
      Erases env Us Γ Δ e .box
  | bvar {Δ} (i : Nat) :
      Erases env Us Γ Δ (.bvar i) (.bvar i)
  | fvar {Δ} (x : FVarId) :
      Erases env Us Γ Δ (.fvar x) (.fvar x)
  | const {Δ} (n : Name) (us : List Level) (kn : Kername)
      (h : Γ.constants n = kn) :
      Erases env Us Γ Δ (.const n us) (.const kn)
  | app {Δ f f' a a'}
      (hf : Erases env Us Γ Δ f f') (ha : Erases env Us Γ Δ a a') :
      Erases env Us Γ Δ (.app f a) (.app f' a')
  | lam {Δ name ty bi b b'} {ty' : VExpr}
      (hty : TrExprS env Us Δ ty ty')
      (hb : Erases env Us Γ ((none, .vlam ty') :: Δ) b b') :
      Erases env Us Γ Δ (.lam name ty b bi) (.lambda (nameToBinder name) b')
  | letE {Δ name ty nd v v' b b'} {ty' val' : VExpr}
      (hty : TrExprS env Us Δ ty ty')
      (hval : TrExprS env Us Δ v val')
      (hv : Erases env Us Γ Δ v v')
      (hb : Erases env Us Γ ((none, .vlet ty' val') :: Δ) b b') :
      Erases env Us Γ Δ (.letE name ty v b nd) (.letIn (nameToBinder name) v' b')

end LeanToLambdaBox
