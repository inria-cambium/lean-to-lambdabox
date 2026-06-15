import LeanToLambdaBox.Basic
import LeanToLambdaBox.Correctness
import LeanToLambdaBox.Erasability
import Lean4Lean.Verify.Typing.Expr
import Lean4Lean.Verify.Typing.Lemmas

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

## Trust boundary: inherited `sorryAx`

lean4lean's reusable `TrExprS` structural lemmas (`weakBV`, `inst`, `instN`, …) are
monolithic inductions over *all* `Expr` constructors; their `proj` case calls
lean4lean's sorried `TrProj`. So those lemmas carry `sorryAx`, and every result
here that uses them (`erases_shift`, `erases_subst`, …) inherits `sorryAx` — *even
on projection-free terms*. This is intentional and in scope: lean4lean's job is to
prove the Lean kernel correct; ours is to prove the transpilation pipeline correct
**assuming** that. lean4lean's results — including its still-open projection
metatheory — are used as-is as assumed building blocks. The `sorryAx` reported by
`#print axioms` is exactly the trust boundary "modulo the Lean kernel's correctness
as formalized by lean4lean"; we do not try to eliminate it. See memory
`lean4lean-sorry-boundary`.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-! ### Distribution of de Bruijn ops over an application spine.

The implementation applies a (nullary) head to its arguments by a left fold of
`Expr.app` (`visitAppArgs`). These lemmas push `liftLooseBVars'`/`instantiate1'`
through that spine, used by the constructor/`casesOn` cases of the substitution
lemmas. -/

theorem liftLooseBVars'_foldl_app (s d : Nat) (f : Expr) (args : List Expr) :
    (args.foldl Expr.app f).liftLooseBVars' s d
      = (args.map (·.liftLooseBVars' s d)).foldl Expr.app (f.liftLooseBVars' s d) := by
  induction args generalizing f with
  | nil => rfl
  | cons a as ih => simp only [List.foldl, List.map, ih, Expr.liftLooseBVars']

theorem instantiate1'_foldl_app (e₀ : Expr) (d : Nat) (f : Expr) (args : List Expr) :
    (args.foldl Expr.app f).instantiate1' e₀ d
      = (args.map (·.instantiate1' e₀ d)).foldl Expr.app (f.instantiate1' e₀ d) := by
  induction args generalizing f with
  | nil => rfl
  | cons a as ih => simp only [List.foldl, List.map, ih, Expr.instantiate1']

theorem LBTerm.shiftArgs_eq_map (d c : Nat) (l : List LBTerm) :
    LBTerm.shiftArgs d c l = l.map (LBTerm.shift d c) := by
  induction l with
  | nil => rfl
  | cons a as ih => simp only [LBTerm.shiftArgs, List.map, ih]

theorem LBTerm.substArgs_eq_map (s : LBTerm) (d : Nat) (l : List LBTerm) :
    LBTerm.substArgs s d l = l.map (LBTerm.subst s d) := by
  induction l with
  | nil => rfl
  | cons a as ih => simp only [LBTerm.substArgs, List.map, ih]

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
  /-- A fully-applied constructor. The implementation emits `.construct iid cidx []`
      applied to its (filtered) args via `.app`; here we use the abstract
      args-inside `.construct iid cidx args'` (reusing `Semantics.lean`'s ι-rule).
      The source is the application spine `args.foldl Expr.app (.const cn us)`. The
      wrapping of the implementation's literal applied-`[]` output into this node is
      anchored in Half B's refinement. -/
  | ctor {Δ} (cn : Name) (us : List Level) (iid : InductiveId) (cidx : Nat)
      {args : List Expr} {args' : List LBTerm}
      (hc : Γ.ctors cn = some (iid, cidx))
      (hlen : args.length = args'.length)
      (hargs : ∀ i (h : i < args.length),
                 Erases env Us Γ Δ args[i] (args'[i]'(hlen ▸ h))) :
      Erases env Us Γ Δ (args.foldl Expr.app (.const cn us)) (.construct iid cidx args')

/-! ### Erasure commutes with de Bruijn weakening (step A2.2).

Mirrors lean4lean's `TrExprS.weakBV`: lifting the source `Expr` by
`liftLooseBVars'` matches lifting the target `LBTerm` by `shift`, under a
`VLCtx.BVLift` weakening of the context. The `box`/`lam`/`letE` cases reuse
`weakBV`/`Erasable.weakN` for their `TrExprS`/`Erasable` premises; the rest is
structural index bookkeeping (the conventions align: source `if i < dk then i
else i + dn` equals `LBTerm.shift dn dk`). -/
theorem erases_shift {env : VEnv} (henv : env.Ordered) {Us : List Name}
    {Γ : ErasureCtx} {Δ Δ' : VLCtx} {dn dk n k : Nat}
    (W : VLCtx.BVLift Δ Δ' dn dk n k)
    {e : Expr} {t : LBTerm} (h : Erases env Us Γ Δ e t) :
    Erases env Us Γ Δ' (e.liftLooseBVars' dk dn) (LBTerm.shift dn dk t) := by
  induction h generalizing Δ' dk k with
  | box htr her => exact .box (htr.weakBV henv W) (her.weakN henv W.toCtx)
  | bvar i =>
    simp only [Expr.liftLooseBVars', LBTerm.shift]
    by_cases hlt : i < dk
    · rw [if_pos hlt, if_neg (by omega : ¬ i ≥ dk)]; exact .bvar i
    · rw [if_neg hlt, if_pos (by omega : i ≥ dk)]; exact .bvar (i + dn)
  | fvar x => exact .fvar x
  | const n us kn h => exact .const n us kn h
  | app _ _ ihf iha => exact .app (ihf W) (iha W)
  | lam hty _ ihb => exact .lam (hty.weakBV henv W) (ihb (W.cons _))
  | letE hty hval _ _ ihv ihb =>
      exact .letE (hty.weakBV henv W) (hval.weakBV henv W) (ihv W) (ihb (W.cons _))
  | ctor cn us iid cidx hc hlen _ ihargs =>
      simp only [liftLooseBVars'_foldl_app, Expr.liftLooseBVars', LBTerm.shift,
                 LBTerm.shiftArgs_eq_map]
      refine .ctor cn us iid cidx hc (by simp [hlen]) (fun i hi => ?_)
      rw [List.getElem_map, List.getElem_map]
      exact ihargs i (by simpa using hi) W

/-- A `VLCtx.InstN` witness yields the de Bruijn weakening of the substitutee's
context `Δ₀` into the instantiated context `Δ` (it gained `dk` binders). Used to
lift the substitutee's erasure in the `bvar i = dk` case of `erases_subst`. -/
theorem instN_toBVLift {Δ₀ Δ₁ Δ : VLCtx} {e₀' A₀ : VExpr} {dk k : Nat}
    (W : VLCtx.InstN Δ₀ e₀' A₀ dk k Δ₁ Δ) : VLCtx.BVLift Δ₀ Δ dk 0 k 0 := by
  induction W with
  | zero => exact .refl
  | @succ _ k _ _ d _ ih => cases d <;> exact ih.skip _

/-! ### Erasure commutes with substitution (step A2.3).

Mirrors lean4lean's `TrExprS.instN`: source `Expr.instantiate1'` ↔ target
`LBTerm.subst` under a `VLCtx.InstN`. `box`/`lam`/`letE` discharge their
`TrExprS`/`Erasable` premises via `instN`/`Erasable.inst`; the `bvar = dk` case
lifts the substitutee via `erases_shift` (using `InstN.toBVLift`). -/
theorem erases_subst {env : VEnv} (henv : env.Ordered) {Us : List Name}
    {Γ : ErasureCtx} {Δ₀ : VLCtx} {e₀ : Expr} {e₀' A₀ : VExpr} {s' : LBTerm}
    (ht₀ : TrExprS env Us Δ₀ e₀ e₀')
    (t₀ : env.HasType Us.length Δ₀.toCtx e₀' A₀)
    (h₀ : Erases env Us Γ Δ₀ e₀ s')
    {Δ₁ Δ : VLCtx} {dk k : Nat} (W : VLCtx.InstN Δ₀ e₀' A₀ dk k Δ₁ Δ)
    {e : Expr} {t : LBTerm} (h : Erases env Us Γ Δ₁ e t) :
    Erases env Us Γ Δ (e.instantiate1' e₀ dk) (LBTerm.subst s' dk t) := by
  induction h generalizing Δ dk k with
  | box htr her =>
      exact .box (TrExprS.instN henv ht₀ t₀ W htr) (her.inst henv W.toCtx t₀)
  | bvar i =>
      simp only [Expr.instantiate1', LBTerm.subst]
      split <;> rename_i h
      · exact .bvar i
      · split <;> rename_i h2
        · exact erases_shift henv (instN_toBVLift W) h₀
        · exact .bvar (i - 1)
  | fvar x => exact .fvar x
  | const n us kn h => exact .const n us kn h
  | app _ _ ihf iha => exact .app (ihf W) (iha W)
  | lam hty _ ihb =>
      exact .lam (TrExprS.instN henv ht₀ t₀ W hty) (ihb (W.succ (d := .vlam _)))
  | letE hty hval _ _ ihv ihb =>
      exact .letE (TrExprS.instN henv ht₀ t₀ W hty) (TrExprS.instN henv ht₀ t₀ W hval)
        (ihv W) (ihb (W.succ (d := .vlet ..)))
  | ctor cn us iid cidx hc hlen _ ihargs =>
      simp only [instantiate1'_foldl_app, Expr.instantiate1', LBTerm.subst,
                 LBTerm.substArgs_eq_map]
      refine .ctor cn us iid cidx hc (by simp [hlen]) (fun i hi => ?_)
      rw [List.getElem_map, List.getElem_map]
      exact ihargs i (by simpa using hi) W

end LeanToLambdaBox
