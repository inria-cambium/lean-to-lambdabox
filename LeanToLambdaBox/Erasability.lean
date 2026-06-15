import Lean4Lean.Theory.VExpr
import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.UniqueTyping

/-!
# Erasability over lean4lean's `VExpr`

The relevance decision is the heart of erasure: a subterm is replaced by `box`
exactly when it is *irrelevant* — a proof or a type-former. The shipping
`Erasure.isErasable` decides this with `Meta.isProp ∨ Meta.isTypeFormerType` on
the inferred type. This file states the same predicate over lean4lean's formal
type theory (`VExpr` + the `HasType` judgment), so that the (forthcoming) typed
`Erases` relation can carry a *real* irrelevance witness in its `box` rule
instead of the trivial `box : Erases .box .box`.

This is step A1 of the semantic-grounding programme (see the project plan).
-/

namespace LeanToLambdaBox

open Lean4Lean

/--
A `VExpr` is an *arity* when it is a (possibly nullary) telescope ending in a
sort: `∀ x₁ … xₙ, Sort u`. These are the type-formers/predicates whose inhabitants
erasure replaces with `box`.

NOTE: this is a *syntactic* characterisation of the inferred type. The shipping
`Meta.isTypeFormerType` whnf-reduces while peeling `∀`s; bridging the two will
require taking the type up to definitional equality (deferred to the
`isErasable` adequacy lemma, step A5/B1).
-/
inductive IsArity : VExpr → Prop
  | sort (u : VLevel) : IsArity (.sort u)
  | forallE (A B : VExpr) : IsArity B → IsArity (.forallE A B)

/-- `A` is an arity *up to definitional equality* — defeq to a syntactic arity.
Unlike `IsArity`, this is defeq-invariant (by transitivity of `IsDefEqU`), which is
what lets `Erasable` survive reduction (needed for box-soundness in
`erases_correct`). It is also more faithful to `Meta.isTypeFormerType`, which
whnf-reduces while peeling `∀`s. -/
def IsArityUpTo (env : VEnv) (U : Nat) (Γ : List VExpr) (A : VExpr) : Prop :=
  ∃ A', env.IsDefEqU U Γ A A' ∧ IsArity A'

/--
`Erasable env U Γ e` holds when `e` is irrelevant in the typing context `Γ`
(with `U` universe parameters) under environment `env`: either

* a **proof** — its type `A` itself has type `Prop = Sort 0`; or
* a **type-former** — its type `A` is an arity up to defeq (`IsArityUpTo`).

This is the `VExpr` analogue of `Erasure.isErasable`
(`Meta.isProp (inferType e) ∨ Meta.isTypeFormerType (inferType e)`).
-/
def Erasable (env : VEnv) (U : Nat) (Γ : List VExpr) (e : VExpr) : Prop :=
  ∃ A, env.HasType U Γ e A ∧ (env.HasType U Γ A (.sort .zero) ∨ IsArityUpTo env U Γ A)

/-! ### Stability of `IsArity`/`Erasable` under instantiation and weakening (step A2.0).

These are the only genuinely new metatheory the `Expr`-based `Erases` re-base needs:
when a `box`-erased subterm is substituted into or lifted, its irrelevance witness
must survive. `IsArity` survives because `VExpr.inst`/`VExpr.liftN` fix `.sort` and
map `.forallE` structurally; `Erasable` survives by combining that with lean4lean's
`HasType.instN`/`HasType.weakN`. -/

theorem IsArity.inst {A : VExpr} (h : IsArity A) (e₀ : VExpr) (k : Nat) :
    IsArity (A.inst e₀ k) := by
  induction h generalizing k with
  | sort u => exact .sort u
  | forallE _ _ _ ih => exact .forallE _ _ (ih (k + 1))

theorem IsArity.liftN {A : VExpr} (h : IsArity A) (n k : Nat) :
    IsArity (A.liftN n k) := by
  induction h generalizing k with
  | sort u => exact .sort u
  | forallE _ _ _ ih => exact .forallE _ _ (ih (k + 1))

theorem IsArityUpTo.inst {env : VEnv} (henv : env.Ordered)
    {U : Nat} {Γ₀ Γ₁ Γ : List VExpr} {e₀ A₀ : VExpr} {k : Nat}
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (h₀ : env.HasType U Γ₀ e₀ A₀)
    {A : VExpr} (h : IsArityUpTo env U Γ₁ A) :
    IsArityUpTo env U Γ (A.inst e₀ k) := by
  obtain ⟨A', hd, har⟩ := h
  exact ⟨A'.inst e₀ k, hd.instN henv W h₀, har.inst e₀ k⟩

theorem IsArityUpTo.weakN {env : VEnv} (henv : env.Ordered)
    {U : Nat} {Γ Γ' : List VExpr} {n k : Nat} (W : Ctx.LiftN n k Γ Γ')
    {A : VExpr} (h : IsArityUpTo env U Γ A) :
    IsArityUpTo env U Γ' (A.liftN n k) := by
  obtain ⟨A', hd, har⟩ := h
  exact ⟨A'.liftN n k, hd.weakN henv W, har.liftN n k⟩

/-- The payoff of the up-to-defeq refinement: `IsArityUpTo` is **defeq-invariant**
in its type argument (which the syntactic `IsArity` was not). If `A''` is defeq to
`A` and `A` is an arity-up-to-defeq, so is `A''` — by transitivity of `IsDefEqU`.
This is what lets the type-former disjunct of `Erasable` survive reduction in the
forthcoming box-soundness argument. -/
theorem IsArityUpTo.defeq {env : VEnv} (henv : env.WF) {U : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) {A A'' : VExpr}
    (hAA : env.IsDefEqU U Γ A'' A) (h : IsArityUpTo env U Γ A) :
    IsArityUpTo env U Γ A'' := by
  obtain ⟨A', hd, har⟩ := h
  exact ⟨A', VEnv.IsDefEqU.trans henv hΓ hAA hd, har⟩

/-- `Erasable` is preserved by weakening: lifting an irrelevant term keeps it
irrelevant. Uses lean4lean's `HasType.weakN` and `IsArity.liftN`; the type-of-type
`Sort 0` is fixed by `liftN`. -/
theorem Erasable.weakN {env : VEnv} (henv : env.Ordered)
    {U : Nat} {Γ Γ' : List VExpr} {n k : Nat} (W : Ctx.LiftN n k Γ Γ')
    {e : VExpr} (h : Erasable env U Γ e) :
    Erasable env U Γ' (e.liftN n k) := by
  obtain ⟨A, hA, hcase⟩ := h
  refine ⟨A.liftN n k, hA.weakN henv W, ?_⟩
  cases hcase with
  | inl hp => exact .inl (hp.weakN henv W)
  | inr ha => exact .inr (ha.weakN henv W)

/-- `Erasable` is preserved by instantiation: substituting into an irrelevant term
keeps it irrelevant. Uses lean4lean's `HasType.instN` and `IsArity.inst`; the
type-of-type `Sort 0` is fixed by `inst`. This is the witness that discharges the
`box` case of `erases_subst`. -/
theorem Erasable.inst {env : VEnv} (henv : env.Ordered)
    {U : Nat} {Γ₀ Γ₁ Γ : List VExpr} {e₀ A₀ : VExpr} {k : Nat}
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (h₀ : env.HasType U Γ₀ e₀ A₀)
    {e : VExpr} (h : Erasable env U Γ₁ e) :
    Erasable env U Γ (e.inst e₀ k) := by
  obtain ⟨A, hA, hcase⟩ := h
  refine ⟨A.inst e₀ k, hA.instN henv W h₀, ?_⟩
  cases hcase with
  | inl hp => exact .inl (hp.instN henv W h₀)
  | inr ha => exact .inr (ha.inst henv W h₀)

end LeanToLambdaBox
