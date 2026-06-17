import LeanToLambdaBox.Erases

/-!
# Source-side big-step evaluation (step A3.2)

`SEval` is the weak call-by-value big-step evaluation of *source* `Lean.Expr`
terms — the operational counterpart, on the source, of the target `Eval`. It is
what "the source program computes to a value" means in the erasure-correctness
statement `erases_correct`.

This file defines the β/ζ/δ + constructor-value fragment (the pure-functional
core). `iota` (pattern matching on a constructor) and the full `erases_correct`
assembly are the next steps; see the project notes.

The constructor cases use the same application-spine encoding as the `Erases`
`ctor` rule (`args.foldl Expr.app (.const cn us)`), so values produced here line
up with what `Erases.ctor` consumes.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-- Source global environment: constant name ↦ its (unfolded) definition body. -/
abbrev SEnv := Name → Option Expr

/-- Weak call-by-value big-step evaluation of source `Expr` to a value, relative
to a source environment `E` (for δ-reduction of constants). Restricted to the
β/ζ/δ + constructor-value fragment. -/
inductive SEval (E : SEnv) : Expr → Expr → Prop
  /-- λ-abstractions are values. -/
  | lam (n : Name) (ty b : Expr) (bi : BinderInfo) :
      SEval E (.lam n ty b bi) (.lam n ty b bi)
  /-- β: function evaluates to a λ, argument to a value, then the substituted body. -/
  | beta {f a : Expr} {n : Name} {ty b : Expr} {bi : BinderInfo} {av r : Expr} :
      SEval E f (.lam n ty b bi) → SEval E a av → SEval E (b.instantiate1' av 0) r →
      SEval E (.app f a) r
  /-- ζ: let-binding evaluates the bound value then the substituted body. -/
  | zeta {n : Name} {ty v b : Expr} {nd : Bool} {vv r : Expr} :
      SEval E v vv → SEval E (b.instantiate1' vv 0) r → SEval E (.letE n ty v b nd) r
  /-- δ: unfold a defined constant and evaluate its body. -/
  | delta {n : Name} {us : List Level} {body r : Expr} :
      E n = some body → SEval E body r → SEval E (.const n us) r
  /-- A saturated constructor application is a value; evaluate its arguments.
      (The head `.const cn us` is left in place, matching the spine encoding used
      by the `Erases` `ctor` rule.) -/
  | ctor_val {cn : Name} {us : List Level} {args vs : List Expr}
      (hl : args.length = vs.length)
      (hargs : ∀ i (h : i < args.length), SEval E args[i] (vs[i]'(hl ▸ h))) :
      SEval E (args.foldl Expr.app (.const cn us)) (vs.foldl Expr.app (.const cn us))

/-- Weak call-by-value big-step evaluation of source `Expr`, the **β + ζ + δ**
fragment (plus constructor values). This is the relation over which we prove the
generalized erasure correctness `erases_correct`. It extends the β-only `SEvalβ`
with:

* `zeta` — let-binding reduction,
* `delta` — constant unfolding (relative to the source env `E`),
* `ctor_val` — saturated constructor applications are values (args evaluated).

ι (`casesOn`/recursor reduction) is deliberately **not** here: lean4lean's
`IsDefEq` exposes no iota rule, so subject-reduction-as-defeq for ι cannot be
discharged against the pinned lean4lean (see `SEvalβζδι` below and the project
report). The constructor spine encoding mirrors exactly the `Erases` `ctor` rule
(and the target `Eval`'s `construct`), so values line up.

We keep `SEvalβ` (and its committed metatheory) intact and define this as a
*separate* inductive; the β cases are duplicated verbatim so the existing β proofs
need not be touched. -/
inductive SEvalβζδ (E : SEnv) : Expr → Expr → Prop
  /-- λ-abstractions are values. -/
  | lam (n : Name) (ty b : Expr) (bi : BinderInfo) :
      SEvalβζδ E (.lam n ty b bi) (.lam n ty b bi)
  /-- β: function evaluates to a λ, argument to a value, then the substituted body. -/
  | beta {f a : Expr} {n : Name} {ty b : Expr} {bi : BinderInfo} {av r : Expr} :
      SEvalβζδ E f (.lam n ty b bi) → SEvalβζδ E a av →
      SEvalβζδ E (b.instantiate1' av 0) r →
      SEvalβζδ E (.app f a) r
  /-- ζ: let-binding evaluates the bound value then the substituted body. -/
  | zeta {n : Name} {ty v b : Expr} {nd : Bool} {vv r : Expr} :
      SEvalβζδ E v vv → SEvalβζδ E (b.instantiate1' vv 0) r →
      SEvalβζδ E (.letE n ty v b nd) r
  /-- δ: unfold a defined constant and evaluate its body. -/
  | delta {n : Name} {us : List Level} {body r : Expr} :
      E n = some body → SEvalβζδ E body r → SEvalβζδ E (.const n us) r
  /-- A saturated constructor application is a value; evaluate its arguments. -/
  | ctor_val {cn : Name} {us : List Level} {args vs : List Expr}
      (hl : args.length = vs.length)
      (hargs : ∀ i (h : i < args.length), SEvalβζδ E args[i] (vs[i]'(hl ▸ h))) :
      SEvalβζδ E (args.foldl Expr.app (.const cn us))
        (vs.foldl Expr.app (.const cn us))

/-- Weak call-by-value big-step evaluation of source `Expr`, the **β + δ**
fragment (λ-values, β-redexes, and constant δ-unfolding). This is the relation over
which the *forward-simulation* `erases_correct` is proved fully sorry-free.

ζ (let), ι (`casesOn`) and saturated-constructor values are scoped out of the
simulation (constructor *values* and ζ appear in `SEvalβζδ`, over which the subject
reduction `SEvalβζδ_defeq` IS fully proved). See the project report for the precise
reasons each is deferred. -/
inductive SEvalβδ (E : SEnv) : Expr → Expr → Prop
  /-- λ-abstractions are values. -/
  | lam (n : Name) (ty b : Expr) (bi : BinderInfo) :
      SEvalβδ E (.lam n ty b bi) (.lam n ty b bi)
  /-- β: function evaluates to a λ, argument to a value, then the substituted body. -/
  | beta {f a : Expr} {n : Name} {ty b : Expr} {bi : BinderInfo} {av r : Expr} :
      SEvalβδ E f (.lam n ty b bi) → SEvalβδ E a av →
      SEvalβδ E (b.instantiate1' av 0) r →
      SEvalβδ E (.app f a) r
  /-- δ: unfold a defined constant and evaluate its body. -/
  | delta {n : Name} {us : List Level} {body r : Expr} :
      E n = some body → SEvalβδ E body r → SEvalβδ E (.const n us) r

/-- Every `SEvalβδ` evaluation is an `SEvalβζδ` evaluation. Lets the β+δ simulation
reuse the β+ζ+δ subject reduction `SEvalβζδ_defeq`. -/
theorem SEvalβδ.toβζδ {E : SEnv} {e v : Expr} (h : SEvalβδ E e v) : SEvalβζδ E e v := by
  induction h with
  | lam n ty b bi => exact .lam n ty b bi
  | beta _ _ _ ihf iha ihb => exact .beta ihf iha ihb
  | delta hu _ ih => exact .delta hu ih

/-- Weak call-by-value big-step evaluation of source `Expr`, the **β + ζ + δ + ι**
fragment — the eventual target including `casesOn`/recursor reduction (`iota`).
This is `SEvalβζδ` plus the `iota` rule.

ι is defined here for documentation and future work, but the subject-reduction and
correctness theorems are proved only for `SEvalβζδ`: discharging ι requires a
recursor/iota definitional-equality rule that the pinned lean4lean's `IsDefEq`
simply does not provide (its only computation rules are `beta` and the generic
`extra` registered-defeq), so subject-reduction-as-defeq for ι is out of reach
against this lean4lean without faking it. See the project report. -/
inductive SEvalβζδι (E : SEnv) : Expr → Expr → Prop
  /-- λ-abstractions are values. -/
  | lam (n : Name) (ty b : Expr) (bi : BinderInfo) :
      SEvalβζδι E (.lam n ty b bi) (.lam n ty b bi)
  /-- β: function evaluates to a λ, argument to a value, then the substituted body. -/
  | beta {f a : Expr} {n : Name} {ty b : Expr} {bi : BinderInfo} {av r : Expr} :
      SEvalβζδι E f (.lam n ty b bi) → SEvalβζδι E a av →
      SEvalβζδι E (b.instantiate1' av 0) r →
      SEvalβζδι E (.app f a) r
  /-- ζ: let-binding evaluates the bound value then the substituted body. -/
  | zeta {n : Name} {ty v b : Expr} {nd : Bool} {vv r : Expr} :
      SEvalβζδι E v vv → SEvalβζδι E (b.instantiate1' vv 0) r →
      SEvalβζδι E (.letE n ty v b nd) r
  /-- δ: unfold a defined constant and evaluate its body. -/
  | delta {n : Name} {us : List Level} {body r : Expr} :
      E n = some body → SEvalβζδι E body r → SEvalβζδι E (.const n us) r
  /-- A saturated constructor application is a value; evaluate its arguments.
      (Head `.const cn us` stays, matching the `Erases` `ctor` spine encoding.) -/
  | ctor_val {cn : Name} {us : List Level} {args vs : List Expr}
      (hl : args.length = vs.length)
      (hargs : ∀ i (h : i < args.length), SEvalβζδι E args[i] (vs[i]'(hl ▸ h))) :
      SEvalβζδι E (args.foldl Expr.app (.const cn us))
        (vs.foldl Expr.app (.const cn us))
  /-- ι: `casesOn`/recursor reduction. The discriminant `discr` evaluates to a
      saturated constructor application `cargs.foldl Expr.app (.const ctor cus)`;
      the selected minor `minors[cidx]` (`cidx` = the constructor's index) applied
      to the constructor's arguments `cargs` evaluates to the result `r`.

      The `casesOn` head spine mirrors the `Erases` `cases` rule exactly:
      `(discr :: minors).foldl Expr.app (pre.foldl Expr.app (.const con us))`, where
      `pre` collects the dropped params/motive/indices. -/
  | iota {con : Name} {us : List Level} {pre minors : List Expr}
      {discr : Expr} {ctor : Name} {cus : List Level} {cargs : List Expr}
      {cidx : Nat} {r : Expr}
      (hdiscr : SEvalβζδι E discr (cargs.foldl Expr.app (.const ctor cus)))
      (hidx : cidx < minors.length)
      (hbranch : SEvalβζδι E (cargs.foldl Expr.app minors[cidx]) r) :
      SEvalβζδι E
        ((discr :: minors).foldl Expr.app (pre.foldl Expr.app (.const con us))) r

end LeanToLambdaBox
