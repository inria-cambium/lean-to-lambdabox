import LeanToLambdaBox.Erasability
import LeanToLambdaBox.Relevance
import Lean4Lean.Verify.TypeChecker.IsDefEq

/-!
# Relevance-oracle soundness via lean4lean's verified `isProp`

The erasure relevance oracle (`Erasure.isErasable`) decides irrelevance by
`Meta.isProp (inferType e) ∨ Meta.isTypeFormerType (inferType e)`. Its
`OracleSound` obligation asks: whenever the oracle returns `true`, the term is
genuinely `Erasable` in lean4lean's formal type theory
(`LeanToLambdaBox/Erasability.lean`).

This file discharges **both disjuncts** of that obligation against lean4lean's
*verified* type checker:

* the **proof disjunct** via `isErasableProp` / `isErasableProp.WF` — run
  lean4lean's kernel `inferType` then its verified `isProp` on the inferred type;
  returning `true` gives `Erasable` via the *proof* case (`Or.inl`), the inferred
  type living in `Sort 0`;
* the **type-former disjunct** via `isArityCheck` / `isArityCheck.WF` — whnf-reduce
  and peel the entire `∀`-telescope of the inferred type, succeeding iff it ends in
  a sort; returning `true` gives `Erasable` via the *arity* case (`Or.inr`,
  `IsArityUpTo`);
* their combination `isErasable` / `isErasable.WF` — the full oracle
  `isProp ∨ isArityCheck`, sound for `Erasable` on either disjunct.

The soundness statements say: if the computation returns `true` on a well-typed
term `e` (translated to `e'`), then `e'` is `Erasable`.

The proof is a two-step Hoare-style composition of lean4lean's own verified WF
lemmas, mirroring the structure of `Inner.isProp.WF`:

* `Inner.inferType.WF` gives, from running `inferType e`, an inferred-type
  `VExpr` `ty'` with `c.HasType e' ty'` (the term has that type) together with a
  translation `c.TrExprS ty ty'` of the inferred-type `Expr`.
* `Inner.isProp.WF`, fed that translation, gives `c.HasType ty' (.sort .zero)`
  when it returns `true` — i.e. the inferred type is a `Prop`.

Assembling `⟨ty', c.HasType e' ty', Or.inl (c.HasType ty' (.sort .zero))⟩`
yields `Erasable`. No new axiom is introduced: the only trust inherited is
lean4lean's (whatever `Inner.inferType.WF` / `Inner.isProp.WF` themselves rest
on).
-/

namespace LeanToLambdaBox

open Lean Lean4Lean
open Lean4Lean.TypeChecker.Inner
open Lean4Lean.TypeChecker (VContext VState)

/-! The executable relevance checks (`isErasableProp`, `isArityCheck`, `isErasable`)
live in `LeanToLambdaBox.Relevance` (importing only lean4lean's executable
`TypeChecker`); this file proves them sound against `Erasable`. -/

/--
**Relevance-oracle soundness, proof disjunct.** If `e` translates to the `VExpr`
`e'` in the verified context `c`, and running lean4lean's verified `isErasableProp`
on `e` returns `true`, then `e'` is `Erasable` in lean4lean's formal type theory —
specifically because its inferred type is a `Prop` (the `Or.inl` disjunct of
`Erasable`).

The conclusion `Erasable c.venv c.lparams.length c.vlctx.toCtx e'` unfolds
(definitionally) to use `c.HasType`, matching what the checker's WF lemmas
produce, so no defeq bridging is needed.
-/
theorem isErasableProp.WF {c : VContext} {s : VState} {e : Expr} {e' : VExpr}
    (he : c.TrExprS e e') :
    (isErasableProp e).WF c s fun b _ =>
      b → Erasable c.venv c.lparams.length c.vlctx.toCtx e' := by
  refine (inferType.WF he).bind fun ty s' le h => ?_
  obtain ⟨ty', _, _, hty, hHT⟩ := h
  exact (isProp.WF hty).mono fun b s'' le' hb hbt => ⟨ty', hHT, Or.inl (hb hbt)⟩

/--
**`IsArityUpTo` is closed under `∀`-introduction.** If the codomain `B` is an arity
up to defeq (in the extended context `A :: Γ`) and both `A` and `B` are types, then
`∀ (_ : A), B` is an arity up to defeq. The witness `B ≡ Y` with `Y` a syntactic
arity lifts to `.forallE A B ≡ .forallE A Y` by the untyped `∀`-congruence
(`IsDefEq.forallEDF`), and `.forallE A Y` is a syntactic arity (`IsArity.forallE`).
This is the inductive step that lets the `∀`-telescope recursion in `isArityCheck`
build an `IsArityUpTo` witness for the whole type from the one for the body.
-/
theorem IsArityUpTo.forallE {env : VEnv} (henv : env.WF) {U : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) {A B : VExpr}
    (hA : env.IsType U Γ A) (hB : env.IsType U (A :: Γ) B)
    (h : IsArityUpTo env U (A :: Γ) B) :
    IsArityUpTo env U Γ (.forallE A B) := by
  obtain ⟨Y, hBY, harY⟩ := h
  obtain ⟨u, hAu⟩ := hA
  obtain ⟨v, hBv⟩ := hB
  exact ⟨.forallE A Y, ⟨_, .forallEDF hAu (hBY.of_l henv ⟨hΓ, _, hAu⟩ hBv)⟩, .forallE _ _ harY⟩

/--
**Arity-check soundness (full recursion).** If `ty` translates to `ty'` and the
verified `isArityCheck.loop` returns `true` for any `fuel`, then `ty'` is an arity up
to defeq (`IsArityUpTo`). Proof by induction on `fuel`: the `.sort` leaf gives the
base arity (its translation is a sort defeq to the reduced type), and the `.forallE`
node opens the binder (`withLocalDecl`), recurses under it (the induction hypothesis
at the extended context), then reassembles the whole-telescope witness with
`IsArityUpTo.forallE` before transporting it across the whnf-reduction defeq
(`IsArityUpTo.defeq`).
-/
theorem isArityCheck.loop.WF {c : VContext} {s : VState} {ty : Expr} {ty' : VExpr}
    {fuel : Nat} (hty : c.TrExprS ty ty') :
    (isArityCheck.loop fuel ty).WF c s fun b _ =>
      b → IsArityUpTo c.venv c.lparams.length c.vlctx.toCtx ty' := by
  induction fuel generalizing c s ty ty' with
  | zero => exact .pure nofun
  | succ fuel ih =>
    refine (whnf.WF hty).bind fun ty1 s' le h => ?_
    obtain ⟨_, e₂, hS, hdefeq⟩ := h
    split
    · -- `ty1 = .forallE name dom body bi`
      rename_i name dom body bi _
      cases hS with
      | @forallE A' B' _ _ _ _ _ hA' hB' hdom hbody =>
        refine c.withMLC_self ▸ Lean4Lean.TypeChecker.RecM.WF.withLocalDecl
          (m := c.mlctx) hdom hA' le fun id cwf' s'' le'' _ => ?_
        have hbody' : (c.withMLC (.vlam id name dom A' bi c.mlctx)).TrExprS
            (body.instantiate1 (.fvar id)) B' := by
          rw [Expr.instantiate1_eq]
          exact hbody.inst_fvar c.Ewf.ordered
            (c.withMLC (.vlam id name dom A' bi c.mlctx)).Δwf
        refine (ih hbody').mono fun b s3 le3 har hbt => ?_
        exact IsArityUpTo.defeq c.Ewf c.Δwf.toCtx hdefeq.symm
          (IsArityUpTo.forallE c.Ewf c.Δwf.toCtx hA' hB' (har hbt))
    · -- `ty1 = .sort u`
      cases hS
      exact .pure fun _ => ⟨.sort _, hdefeq.symm, .sort _⟩
    · exact .pure nofun

theorem isArityCheck.WF {c : VContext} {s : VState} {ty : Expr} {ty' : VExpr}
    (hty : c.TrExprS ty ty') :
    (isArityCheck ty).WF c s fun b _ =>
      b → IsArityUpTo c.venv c.lparams.length c.vlctx.toCtx ty' :=
  isArityCheck.loop.WF hty

/--
**Relevance-oracle soundness (both disjuncts).** If `e` translates to `e'` and the
verified `isErasable` returns `true`, then `e'` is `Erasable`: either its inferred
type is a `Prop` (`Or.inl`, via `isProp.WF`) or that type is an arity up to defeq
(`Or.inr`, via `isArityCheck.WF`).
-/
theorem isErasable.WF {c : VContext} {s : VState} {e : Expr} {e' : VExpr}
    (he : c.TrExprS e e') :
    (isErasable e).WF c s fun b _ =>
      b → Erasable c.venv c.lparams.length c.vlctx.toCtx e' := by
  refine (inferType.WF he).bind fun ty s' le h => ?_
  obtain ⟨ty', _, _, hty, hHT⟩ := h
  refine (isProp.WF hty).bind fun b s'' le' hb => ?_
  split
  · rename_i hbtrue
    exact .pure fun _ => ⟨ty', hHT, Or.inl (hb (by simpa using hbtrue))⟩
  · exact (isArityCheck.WF hty).mono fun b s''' le'' har hbt =>
      ⟨ty', hHT, Or.inr (har hbt)⟩

/-!
Note on the trust boundary: `isErasableProp.WF`, `isArityCheck.WF` and `isErasable.WF`
inherit, beyond the usual `[propext, sorryAx, Classical.choice, Quot.sound]`, the
lean4lean-declared *modeling* axioms for native `Expr`/`Level`/`PersistentHashMap`/
`PersistentArray` (`Lean4Lean/Verify/Axioms.lean`) that the executable checker's
`whnf`/`inferType`/`isProp` and the `Expr.instantiate1 = instantiate1'` bridge
(`Expr.instantiate1_eq`, used to re-open binders in the `∀`-telescope recursion) rest
on. These are all lean4lean's, not introduced here — the price of routing through the
*verified executable* checker rather than the pure `HasType` judgment. In particular
no new `axiom`/`sorry`/`native_decide` is added by this file: `sorryAx` is inherited
from lean4lean's own unproven `Verify` lemmas, whose trust this development sits atop.
[Provenance corrected at the `fee3ada` re-pin, 2026-08-27: this used to name
"projections/`TrProj`" as the source. `TrProj` has a real definition upstream now; the
live source is the unique-typing cluster (`TrExprS.uniq` → `TrProj.uniq`, and
`IsDefEq.uniqU`). See `ColdStart.lean`'s inherited-boundary section for the measurement.]
-/

end LeanToLambdaBox
