import LeanToLambdaBox.Semantics.Flags

/-!
# Values and atoms for λ□

Faithful translation of MetaCoq's `EWcbvEval.atom` / `value_head` / `value`
predicates (the characterisation of weak call-by-value normal forms), adapted to
the block-constructor (args-inside) form our syntax uses. Replaces the old crude
`LBTerm.IsValue`, which wrongly listed `const` (it δ-reduces) as a value.

Correspondence with MetaCoq:
* `atomValue`        ↔ `atom` (the head-atom cases: `box`, `lambda`, `fix`,
  `prim`; plus our locally-nameless `fvar`). We drop MetaCoq's nullary-declared-
  `tConstruct` atom because a nullary constructor is just `construct iid k []`,
  covered by the `Value.construct` case below.
* `isConstructorValue` — recognises a (block) constructor value; guards the
  guarded-`fix` unfolding (MetaCoq's `isConstruct`/constructor-value test).
* `isStuckApp`       — head of an `app_cong` (MetaCoq's negative side condition
  in `eval_app_cong`): an application head that is neither reducible nor a `fix`.
* `Value`            ↔ `value` (`value_atom` + block `value_constructor` +
  `value_app_nonnil`; the under-applied/stuck-`fix` case is `Value.fix_stuck`).
-/

namespace LeanToLambdaBox

open Lean

/-- Head atoms: irreducible on their own. MetaCoq `atom` (block form). Note
    `const` is **not** here (it δ-reduces), fixing the old `IsValue` bug. -/
def atomValue : LBTerm → Prop
  | .box | .lambda _ _ | .fvar _ | .prim _ | .fix _ _ => True
  | _ => False

instance : DecidablePred atomValue := fun t => by
  unfold atomValue; split <;> infer_instance

/-- Is `t` a (saturated, block-form) constructor value? Guards the guarded-`fix`
    unfolding: a `fix` reduces only once its principal argument is a constructor. -/
def isConstructorValue : LBTerm → Bool
  | .construct _ _ _ => true
  | _ => false

/-- Head of an `app_cong` step: a value that is stuck as an application head.
    Excludes `lambda` (β), `box` (`app_box`), `fix` (the `fix_*` rules handle fix
    applications) and `construct` (the `construct_app` rule accumulates arguments
    onto an under-applied constructor, MetaCoq's `~~ isConstructApp`), so
    `app_cong` stays disjoint from all of those. -/
def isStuckApp (_fl : WcbvFlags) : LBTerm → Bool
  | .lambda _ _ => false
  | .box => false
  | .fix _ _ => false
  | .construct _ _ _ => false
  | .prim _ => true
  | .fvar _ => true
  | .app _ _ => true
  | _ => false

/-- Weak call-by-value values (normal forms). MetaCoq `EWcbvEval.value`. -/
inductive Value (fl : WcbvFlags) : LBTerm → Prop
  /-- A head atom (`box`/`lambda`/`fvar`/`prim`/bare `fix`). MetaCoq `value_atom`. -/
  | atom {t : LBTerm} (h : atomValue t) : Value fl t
  /-- A block constructor whose arguments are all values. MetaCoq
      `value_constructor` (block form). -/
  | construct {iid : InductiveId} {k : Nat} {args : List LBTerm}
      (hargs : ∀ i (h : i < args.length), Value fl args[i]) :
      Value fl (.construct iid k args)
  /-- A stuck application: a stuck head applied to a value. MetaCoq
      `value_app_nonnil` (non-`fix` heads). -/
  | app_stuck {f a : LBTerm} (hf : Value fl f) (hstuck : isStuckApp fl f = true)
      (ha : Value fl a) : Value fl (.app f a)
  /-- An under-applied / stuck `fix`: under guarded fix, a `fix` applied to a value
      that is *not* a constructor (so the guarded unfolding does not fire) is a
      value. MetaCoq `value_app_nonnil` with `value_head_fix`. (Under *unguarded*
      fix such an application reduces, so the guard is required.) -/
  | fix_stuck (hg : fl.with_guarded_fix = true) {defs : List (@FixDef LBTerm)} {i : Nat}
      {av : LBTerm} (ha : Value fl av) (hnc : isConstructorValue av = false) :
      Value fl (.app (.fix defs i) av)

end LeanToLambdaBox
