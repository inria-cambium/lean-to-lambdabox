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

end LeanToLambdaBox
