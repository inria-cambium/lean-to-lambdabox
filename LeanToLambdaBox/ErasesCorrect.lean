import LeanToLambdaBox.Erases
import LeanToLambdaBox.Eval

/-!
# Towards erasure correctness (step A3.2)

The target operational semantics is `Eval` (big-step weak CBV, with `app_box`).
The full statement we are heading for is MetaCoq's `erases_correct`: for a
well-typed source term that evaluates to a value, its erasure evaluates to a
value that erases the source value.

This file collects the reusable, fully-proved computational cores of that
theorem. The β case is a direct instance of `erases_subst`; it is the heart of
why erasure preserves β-reduction.

Still required for the full `erases_correct` (next): a source-side evaluation
relation, and the `box`-soundness lemma (an irrelevant subterm never blocks a
relevant redex), which needs lean4lean subject reduction — the genuinely deep
obligation, and where the `box` rule's typing premise earns its keep.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-- **β-correctness (substitution form).** Erasure commutes with the body
substitution of a β-redex: if the argument `a` (of the binder type, witnessed by
`hTa`) erases to `a'` and the body `b` erases to `b'` under the binder, then the
source reduct `b[a]` erases to the target reduct `subst1 a' b'`.

A direct instance of `erases_subst` at depth 0 (`VLCtx.InstN.zero`). This is the
core computational content of the β case of erasure correctness: combined with
`Eval.beta`, the target redex `(λ. b') a'` evaluates through `subst1 a' b'`, which
this lemma shows still erases the source reduct. -/
theorem erases_beta_struct {env : VEnv} (henv : env.Ordered) {Us : List Name}
    {Γ : ErasureCtx} {Δ : VLCtx}
    {b a : Expr} {b' a' : LBTerm} {ty' va : VExpr}
    (hta : TrExprS env Us Δ a va) (hTa : env.HasType Us.length Δ.toCtx va ty')
    (hb : Erases env Us Γ ((none, .vlam ty') :: Δ) b b')
    (ha : Erases env Us Γ Δ a a') :
    Erases env Us Γ Δ (b.instantiate1' a 0) (LBTerm.subst1 a' b') :=
  erases_subst henv hta hTa ha .zero hb

end LeanToLambdaBox
