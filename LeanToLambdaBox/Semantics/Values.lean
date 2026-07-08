import LeanToLambdaBox.Semantics.Flags
import LeanToLambdaBox.Semantics.Env

/-!
# Values and atoms for λ□

Faithful translation of MetaCoq's `EWcbvEval.atom` / `value_head` / `value`
predicates (the characterisation of weak call-by-value normal forms). The model is
**flag-parametric**; the *validated* target is the non-block flags
(`with_constructor_as_block = false`, MetaCoq's `default`/`opt`/`target_wcbv_flags`),
where constructor and applied-`fix` values are `mkApps`-**spines**, exactly as in
MetaCoq. The block-form cases are kept for the block-mode instances.

Correspondence with MetaCoq:
* `atomValue`        ↔ `atom` minus the flag-dependent nullary-`tConstruct` case
  (the head-atom cases: `box`, `lambda`, `fix`, `prim`; plus our locally-nameless
  `fvar`). MetaCoq's `atom (tConstruct ind c []) = negb block && isSome lookup`
  is handled instead by the `Value.construct_spine` case with `args = []`.
* `isLambda`/`isBox`/`isFix`/`isConstruct`/`isPrim` and their `…App` variants (over
  the spine head, `LBTerm.spineHead` ↔ MetaCoq `head`) ↔ the same-named MetaCoq
  predicates. `isStuckApp` ↔ the negated side condition of `eval_app_cong`
  (`~~ (isLambda ∨ isFixApp/isFix ∨ isBox ∨ isConstructApp ∨ isPrimApp ∨ isLazyApp)`;
  there is no `tLazy` in `LBTerm`).
* `Value`            ↔ `value` (`value_atom` + block `value_constructor` +
  non-block spine `value_app_nonnil` for `tConstruct`/`tFix` heads via `value_head`).
-/

namespace LeanToLambdaBox

open Lean

/-- Head atoms: irreducible on their own. MetaCoq `atom`, minus the flag-dependent
    nullary-`tConstruct` case (see `Value.construct_spine`). Note `const` is **not**
    here (it δ-reduces). -/
def atomValue : LBTerm → Prop
  | .box | .lambda _ _ | .fvar _ | .prim _ | .fix _ _ => True
  | _ => False

instance : DecidablePred atomValue := fun t => by
  unfold atomValue; split <;> infer_instance

/-! ### Head-shape predicates (MetaCoq `EAstUtils`). -/

/-- `t` is a λ-abstraction. MetaCoq `isLambda`. -/
def isLambda : LBTerm → Bool | .lambda _ _ => true | _ => false
/-- `t` is `□`. MetaCoq `isBox`. -/
def isBox : LBTerm → Bool | .box => true | _ => false
/-- `t` is a bare `fix`. MetaCoq `isFix`. -/
def isFix : LBTerm → Bool | .fix _ _ => true | _ => false
/-- `t` is a bare (block) constructor node. MetaCoq `isConstruct`. -/
def isConstruct : LBTerm → Bool | .construct _ _ _ => true | _ => false
/-- `t` is a primitive. MetaCoq `isPrim`. -/
def isPrim : LBTerm → Bool | .prim _ => true | _ => false

/-- The application spine of `t` is `fix`-headed. MetaCoq `isFixApp := isFix ∘ head`. -/
def isFixApp (t : LBTerm) : Bool := isFix (LBTerm.spineHead t)
/-- The application spine of `t` is constructor-headed. MetaCoq
    `isConstructApp := isConstruct ∘ head`. -/
def isConstructApp (t : LBTerm) : Bool := isConstruct (LBTerm.spineHead t)
/-- The application spine of `t` is primitive-headed. MetaCoq
    `isPrimApp := isPrim ∘ head`. -/
def isPrimApp (t : LBTerm) : Bool := isPrim (LBTerm.spineHead t)

/-- Head of an `app_cong` step: a value that is stuck as an application head.
    Direct transcription of the negated side condition of MetaCoq's `eval_app_cong`:
    `~~ (isLambda f' || (if with_guarded_fix then isFixApp f' else isFix f') || isBox f'
        || isConstructApp f' || isPrimApp f' || isLazyApp f')`.
    (`LBTerm` has no `tLazy`, so `isLazyApp` is dropped.) In particular a **prim**-headed
    application is *not* stuck (`isPrimApp` excludes it — MetaCoq has no rule applying a
    primitive), fixing the previous model which wrongly let prim-headed apps step. -/
def isStuckApp (fl : WcbvFlags) (f : LBTerm) : Bool :=
  ! (isLambda f || (if fl.with_guarded_fix then isFixApp f else isFix f)
     || isBox f || isConstructApp f || isPrimApp f)

/-- Weak call-by-value values (normal forms). MetaCoq `EWcbvEval.value`,
    parameterised (as there) by the global environment `Γ` — needed to bound
    non-block constructor spines by the constructor arity.

    The non-block constructor and applied-`fix` spine cases (MetaCoq's
    `value_app_nonnil`, whose index is `mkApps f args`) are phrased **structurally**
    over `.app` — with the `mkApps` spine shape carried as a premise equation rather
    than in the conclusion index — so that the definition remains invertible by
    `cases` (`mkApps` is a function, `.app` is a constructor). The recursion in
    `construct_app_val`/`fix_app_val` is structural down the spine. -/
inductive Value (Γ : GlobalDeclarations) (fl : WcbvFlags) : LBTerm → Prop
  /-- A head atom (`box`/`lambda`/`fvar`/`prim`/bare `fix`). MetaCoq `value_atom`
      (the `atom` cases). -/
  | atom {t : LBTerm} (h : atomValue t) : Value Γ fl t
  /-- A block constructor whose arguments are all values. MetaCoq
      `value_constructor` (block form, `with_constructor_as_block = true`). -/
  | construct_block (hb : fl.with_constructor_as_block = true)
      {iid : InductiveId} {k : Nat} {args : List LBTerm}
      (hargs : ∀ i (h : i < args.length), Value Γ fl args[i]) :
      Value Γ fl (.construct iid k args)
  /-- The nullary head of a **non-block** constructor spine — MetaCoq's
      `atom (tConstruct ind c [])` at `with_constructor_as_block = false`. -/
  | construct_nil (hb : fl.with_constructor_as_block = false)
      {iid : InductiveId} {c ar : Nat}
      (harity : constructorArity Γ iid c = some ar) :
      Value Γ fl (.construct iid c [])
  /-- A **non-block** constructor spine, extended by one value argument, still under
      the constructor arity. Together with `construct_nil` this builds MetaCoq's
      `value_app_nonnil`/`value_head_cstr` spine `mkApps (.construct iid c []) args`
      with `#args ≤ cstr_arity`. -/
  | construct_app_val (hb : fl.with_constructor_as_block = false)
      {hd a : LBTerm} {iid : InductiveId} {c ar : Nat} {args : List LBTerm}
      (hval : Value Γ fl hd)
      (hd_eq : hd = LBTerm.mkApps (.construct iid c []) args)
      (harity : constructorArity Γ iid c = some ar)
      (hlt : args.length < ar)
      (ha : Value Γ fl a) :
      Value Γ fl (.app hd a)
  /-- A stuck application: a stuck head applied to a value. MetaCoq
      `value_app_nonnil` (non-`fix`/non-constructor heads; here the locally-nameless
      `fvar`-headed spines). -/
  | app_stuck {f a : LBTerm} (hf : Value Γ fl f) (hstuck : isStuckApp fl f = true)
      (ha : Value Γ fl a) : Value Γ fl (.app f a)
  /-- A guarded-`fix` spine, extended by one value argument, still under the
      recursive-argument count `rarg`, so the guarded unfolding has not fired.
      Together with the bare-`fix` `atom` case this builds MetaCoq's
      `value_app_nonnil`/`value_head_fix` spine `mkApps (.fix defs i) argsv` with
      `#argsv ≤ rarg`. -/
  | fix_app_val (hg : fl.with_guarded_fix = true)
      {hd a : LBTerm} {defs : List (@FixDef LBTerm)} {i rarg : Nat} {argsv : List LBTerm}
      (hval : Value Γ fl hd)
      (hd_eq : hd = LBTerm.mkApps (.fix defs i) argsv)
      (hrarg : (defs[i]?).map (·.principalArgIdx) = some rarg)
      (hlt : argsv.length < rarg)
      (ha : Value Γ fl a) :
      Value Γ fl (.app hd a)

end LeanToLambdaBox
