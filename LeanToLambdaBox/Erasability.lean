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

/-- **Box-soundness core.** `Erasable` is preserved under definitional equality of
the *term*: if `e` is erasable and `e ≡ e'`, then `e'` is erasable. Since a
reduction step `e ⟶ e'` is a definitional equality, this says an irrelevant term
stays irrelevant when reduced — the property that makes erasing it to `box` sound
in `erases_correct`. The type witness transfers via lean4lean's `HasType.defeqU_l`
(same type `A`, so the proof/arity disjunct carries over unchanged). -/
theorem Erasable.defeq {env : VEnv} (henv : env.WF) {U : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) {e e' : VExpr}
    (hee : env.IsDefEqU U Γ e e') (h : Erasable env U Γ e) :
    Erasable env U Γ e' := by
  obtain ⟨A, hA, hcase⟩ := h
  exact ⟨A, hA.defeqU_l henv hΓ hee, hcase⟩

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

/-! ### Box propagation through application (MetaCoq's `eval_box` content).

If a function `f` is erasable (a proof or a type-former) and `f a` is well-typed,
then `f a` is erasable too. This is the type-theoretic fact behind the target
`Eval.app_box` rule: applying an irrelevant head yields an irrelevant result.

* If `f` is a **proof** (`f : A`, `A : Sort 0`): then `A`, being defeq to the
  function type `∀ x : Aᵈ, B`, is a `Prop`, so `imax · v ≈ 0` forces `v ≈ 0`,
  i.e. `B : Sort 0`; hence `f a : B[a] : Sort 0` is a proof.
* If `f` is a **type-former** (`A` is an arity up to defeq): then `B` is an arity
  up to defeq, so `B[a]` is too (`IsArityUpTo.inst`); hence `f a` is a
  type-former. -/
theorem Erasable.app {env : VEnv} (henv : env.WF) {U : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) {f a A B : VExpr}
    (hf : Erasable env U Γ f)
    (hTf : env.HasType U Γ f (.forallE A B))
    (hTa : env.HasType U Γ a A) :
    Erasable env U Γ (.app f a) := by
  obtain ⟨T, hfT, hcase⟩ := hf
  -- `f`'s type `T` is defeq to its function type `∀ A, B`.
  have hTeq : env.IsDefEqU U Γ T (.forallE A B) :=
    VEnv.IsDefEq.uniqU henv hΓ hfT hTf
  -- `f a : B.inst a`.
  have hTapp : env.HasType U Γ (.app f a) (B.inst a) := hTf.app hTa
  refine ⟨B.inst a, hTapp, ?_⟩
  cases hcase with
  | inl hp =>
      -- Proof case: `∀ A, B : Sort 0`, so `B : Sort 0`, so `B.inst a : Sort 0`.
      left
      -- Transport `T : Sort 0` to `∀ A, B : Sort 0`.
      have hforallProp : env.HasType U Γ (.forallE A B) (.sort .zero) :=
        hp.defeqU_l henv hΓ hTeq
      -- Invert: `B : Sort v` with `imax u v ≈ 0`, i.e. `v ≈ 0`.
      obtain ⟨⟨u, hAu⟩, v, hBv⟩ := VEnv.IsType.forallE_inv henv.ordered ⟨_, hforallProp⟩
      have hforallImax : env.HasType U Γ (.forallE A B) (.sort (.imax u v)) :=
        hAu.forallE hBv
      have hsorteq : env.IsDefEqU U Γ (.sort .zero) (.sort (.imax u v)) :=
        VEnv.IsDefEq.uniqU henv hΓ hforallProp hforallImax
      have hzero : VLevel.imax u v ≈ VLevel.zero :=
        (VEnv.IsDefEqU.sort_inv henv hΓ hsorteq).symm
      have hv0 : v ≈ VLevel.zero := VLevel.imax_eq_zero.1 hzero
      -- `B : Sort v ≡ Sort 0`, so `B : Sort 0` (in `A :: Γ`).
      have hΓA : OnCtx (A :: Γ) (env.IsType U) := ⟨hΓ, _, hAu⟩
      have hvWF : v.WF U := hBv.sort_r henv.ordered hΓA
      have hB0 : env.HasType U (A :: Γ) B (.sort .zero) :=
        (VEnv.IsDefEq.sortDF hvWF (l' := VLevel.zero) trivial hv0).defeq hBv
      -- Instantiate by `a : A` at depth 0: `(Sort 0).inst a = Sort 0`.
      have := hB0.instN henv.ordered (Ctx.InstN.zero) hTa
      simpa [VExpr.inst] using this
  | inr ha =>
      -- Type-former case: `B` is an arity up to defeq, so `B.inst a` is too.
      right
      have hforallAr : IsArityUpTo env U Γ (.forallE A B) :=
        ha.defeq henv hΓ (VEnv.IsDefEqU.symm hTeq)
      obtain ⟨C, hC, harC⟩ := hforallAr
      -- `forallE A B ≡ C` and `IsArity C`; `C` must itself be a `.forallE`.
      cases harC with
      | sort u => exact absurd hC (VEnv.IsDefEqU.sort_forallE_inv henv hΓ ∘ VEnv.IsDefEqU.symm)
      | forallE A' B' harB' =>
          obtain ⟨_, _, hBB'⟩ := VEnv.IsDefEqU.forallE_inv henv hΓ hC
          exact IsArityUpTo.inst henv.ordered (Ctx.InstN.zero) hTa
            ⟨B', ⟨_, hBB'⟩, harB'⟩

end LeanToLambdaBox
