import Lean4Lean.Theory.VExpr
import Lean4Lean.Theory.Typing.Basic

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

/--
`Erasable env U Γ e` holds when `e` is irrelevant in the typing context `Γ`
(with `U` universe parameters) under environment `env`: either

* a **proof** — its type `A` itself has type `Prop = Sort 0`; or
* a **type-former** — its type `A` is an arity (`IsArity A`).

This is the `VExpr` analogue of `Erasure.isErasable`
(`Meta.isProp (inferType e) ∨ Meta.isTypeFormerType (inferType e)`).
-/
def Erasable (env : VEnv) (U : Nat) (Γ : List VExpr) (e : VExpr) : Prop :=
  ∃ A, env.HasType U Γ e A ∧ (env.HasType U Γ A (.sort .zero) ∨ IsArity A)

end LeanToLambdaBox
