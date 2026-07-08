import LeanToLambdaBox.Semantics.Substitution
import LeanToLambdaBox.Semantics.Env
import LeanToLambdaBox.Semantics.Flags
import LeanToLambdaBox.Semantics.Values

/-!
# Big-step weak call-by-value evaluation for λ□ — `WcbvEval`

A faithful, flag-parameterised Lean translation of MetaCoq's
`EWcbvEval.eval` (`MetaCoq.Erasure.EWcbvEval`), the operational semantics our
erased terms actually run under (the model peregrine→malfunction→OCaml
implements).

`WcbvEval Γ fl` is parameterised by the global environment `Γ` (for δ-reduction of
constants and inductive-metadata lookups) and the `WcbvFlags` `fl`. The two prior
ad-hoc relations are recovered as instances:

* `Eval Γ     := WcbvEval Γ optFlags`     — prop-cases **off** (MetaCoq's
  `disable_prop_cases`/`opt_wcbv_flags`); the target of the `optimize` pass and
  the relation `erases_correct` produces.
* `EvalProp Γ := WcbvEval Γ defaultFlags` — prop-cases **on** (MetaCoq's
  `default_wcbv_flags`); the source of `optimize_correct`.

## Constructor ↔ MetaCoq `eval` rule correspondence

| `WcbvEval` | MetaCoq | flag guard |
|---|---|---|
| `box`/`lam`/`fvar`/`prim`/`fix_atom` | `eval_atom` (decomposed by head) | — |
| `beta`     | `eval_beta`             | — |
| `app_box`  | `eval_box` (evaluates the argument) | — |
| `zeta`     | `eval_zeta`             | — |
| `delta`    | `eval_delta`            | — |
| `construct`     | `eval_construct_block` | `with_constructor_as_block` |
| `construct_atom`| `eval_atom` (`tConstruct ind c []`) | `¬ with_constructor_as_block` |
| `construct_app` | `eval_construct` (accumulate one arg onto a spine) | `¬ with_constructor_as_block` |
| `iota`     | `eval_iota` (spine discriminant)      | `¬ with_constructor_as_block`, non-`Prop` |
| `iota_block`| `eval_iota_block` (block discriminant)| `with_constructor_as_block`, non-`Prop` |
| `iota_sing`| `eval_iota_sing`        | `with_prop_case` |
| `proj`     | `eval_proj` (spine discriminant)      | `¬ with_constructor_as_block`, non-`Prop` |
| `proj_block`| `eval_proj_block` (block discriminant)| `with_constructor_as_block`, non-`Prop` |
| `proj_prop`| `eval_proj_prop`        | `with_prop_case` |
| `fix_guarded` | `eval_fix` (spine head, unfold at `#argsv = rarg`) | `with_guarded_fix` |
| `fix_stuck`   | `eval_fix_value` (spine head, `#argsv < rarg`)     | `with_guarded_fix` |
| `fix_unguarded`| `eval_fix'` (bare-`fix` head)                     | `¬ with_guarded_fix` |
| `app_cong` | `eval_app_cong`         | head is a stuck application (`isStuckApp`) |

**No `cofix`:** `LBTerm` has no `cofix` node, so MetaCoq's `eval_cofix_case`/
`eval_cofix_proj` are unrepresentable — nothing to model.

The model is **flag-parametric** and the *validated* target is the **non-block**
flags (`with_constructor_as_block = false`: MetaCoq's `default`/`opt`/`target_wcbv_flags`),
at which `WcbvEval` matches `EWcbvEval.eval` rule-for-rule. Both constructor
representations are supported and kept mutually exclusive by the flag guard:
* **non-block/applied form** (validated): a constructor is `.construct iid c []`
  applied through `.app` — `WcbvEval` values are the `mkApps`-spines
  `(…((construct iid c []) a₁)… aₙ)` (`construct_atom` for the nullary head,
  `construct_app` accumulating one argument at a time up to `cstr_arity`, never
  over-applying — MetaCoq `eval_construct`); `iota`/`proj` scrutinise the spine.
* **block form** (`with_constructor_as_block = true`, MetaCoq-internal): `.construct
  iid k args` carries its arguments inside; `construct`/`iota_block`/`proj_block`
  handle it. This is what `LBOptimize_correct` currently runs under.

The `fix` rules dispatch on the *evaluated* function head — MetaCoq's `mkApps (tFix ..)
argsv` spine, accumulated one argument per application (`fix_stuck` while under
`rarg` args, `fix_guarded` unfolding exactly when the `rarg`-th argument arrives),
so a `fix` reached through, e.g., a `const` unfolds too. `fix_unguarded` (`eval_fix'`)
uses a **bare** `fix` head, unfolding on every argument.
`app_box` follows `eval_box` in evaluating the argument (dropping the value) —
required for faithfulness and for determinism.
-/

namespace LeanToLambdaBox

open Lean

/-- Weak call-by-value big-step evaluation of λ□ terms to values, relative to a
global environment `Γ` and evaluation flags `fl`. Faithful to MetaCoq
`EWcbvEval.eval`. -/
inductive WcbvEval (Γ : GlobalDeclarations) (fl : WcbvFlags) : LBTerm → LBTerm → Prop
  /-- `□` is a value. -/
  | box : WcbvEval Γ fl .box .box
  /-- λ-abstractions are values (weak: no reduction under binders). -/
  | lam (n : BinderName) (b : LBTerm) : WcbvEval Γ fl (.lambda n b) (.lambda n b)
  /-- Free variables are values. -/
  | fvar (x : FVarId) : WcbvEval Γ fl (.fvar x) (.fvar x)
  /-- Primitives are values. -/
  | prim (p : PrimVal) : WcbvEval Γ fl (.prim p) (.prim p)
  /-- A bare `fix` is a value/atom (MetaCoq `tFix ∈ atom`). -/
  | fix_atom (defs : List (@FixDef LBTerm)) (i : Nat) : WcbvEval Γ fl (.fix defs i) (.fix defs i)
  /-- β: the function evaluates to a λ, the argument to a value, then the body with
      the argument substituted evaluates to the result. (`eval_beta`) -/
  | beta {f a : LBTerm} {n : BinderName} {b av r : LBTerm} :
      WcbvEval Γ fl f (.lambda n b) → WcbvEval Γ fl a av → WcbvEval Γ fl (LBTerm.subst1 av b) r →
      WcbvEval Γ fl (.app f a) r
  /-- `eval_box`: applying an irrelevant (boxed) head yields `box`; the argument is
      still evaluated (to some `av`, which is discarded). -/
  | app_box {f a av : LBTerm} :
      WcbvEval Γ fl f .box → WcbvEval Γ fl a av → WcbvEval Γ fl (.app f a) .box
  /-- ζ: let-binding evaluates the value then the body with it substituted. (`eval_zeta`) -/
  | zeta {n : BinderName} {v b vv r : LBTerm} :
      WcbvEval Γ fl v vv → WcbvEval Γ fl (LBTerm.subst1 vv b) r → WcbvEval Γ fl (.letIn n v b) r
  /-- δ: unfold a defined constant and evaluate its body. (`eval_delta`) -/
  | delta {kn : Kername} {body r : LBTerm} :
      LBTerm.envLookup Γ kn = some (.constantDecl ⟨some body⟩) → WcbvEval Γ fl body r →
      WcbvEval Γ fl (.const kn) r
  /-- Constructor (block form, `eval_construct_block`, enabled when
      `with_constructor_as_block = true`): evaluate each argument of a saturated
      block constructor node. -/
  | construct (hb : fl.with_constructor_as_block = true)
      {iid : InductiveId} {k : Nat} {args vs : List LBTerm}
      (hl : args.length = vs.length)
      (hargs : ∀ i (h : i < args.length), WcbvEval Γ fl args[i] (vs[i]'(hl ▸ h))) :
      WcbvEval Γ fl (.construct iid k args) (.construct iid k vs)
  /-- Nullary non-block constructor (`eval_atom` for `tConstruct ind c []`, when
      `with_constructor_as_block = false` and the constructor is declared): a bare
      applied-form constructor head is a value. This is the base of a constructor
      spine built up by `construct_app`. -/
  | construct_atom (hb : fl.with_constructor_as_block = false)
      {iid : InductiveId} {c ar : Nat} :
      constructorArity Γ iid c = some ar →
      WcbvEval Γ fl (.construct iid c []) (.construct iid c [])
  /-- Non-block constructor application (`eval_construct`, enabled when
      `with_constructor_as_block = false`): the function evaluates to an
      **under-applied constructor spine** `mkApps (.construct iid c []) args`; the
      argument is accumulated onto it, keeping the `mkApps`-spine shape (no block
      accumulation). Only fires while under the arity (`args.length < ar`); a
      saturated head has no rule and `app_cong` excludes constructor-headed spines,
      so over-application is stuck — exactly MetaCoq's "we do not allow
      over-applications". -/
  | construct_app (hb : fl.with_constructor_as_block = false)
      {f a a' : LBTerm} {iid : InductiveId} {c : Nat} {args : List LBTerm} {ar : Nat} :
      WcbvEval Γ fl f (LBTerm.mkApps (.construct iid c []) args) →
      constructorArity Γ iid c = some ar →
      args.length < ar →
      WcbvEval Γ fl a a' →
      WcbvEval Γ fl (.app f a) (.app (LBTerm.mkApps (.construct iid c []) args) a')
  /-- ι, non-block (`eval_iota`, when `with_constructor_as_block = false`): the
      discriminant evaluates to a **spine** `mkApps (.construct iid k []) args` of a
      non-propositional inductive; select alternative `k` and evaluate its body with
      the constructor's *fields* (`args` after dropping the `np` parameters), in
      **reverse**, substituted for the field binders — MetaCoq's
      `iota_red np args br = substl (rev (skipn np args)) br.2`. -/
  | iota (hb : fl.with_constructor_as_block = false)
         {iid : InductiveId} {np k : Nat} {discr : LBTerm}
         {alts : List (List BinderName × LBTerm)} {args : List LBTerm}
         {names : List BinderName} {body r : LBTerm} :
      isPropositionalInductive Γ iid = false →
      WcbvEval Γ fl discr (LBTerm.mkApps (.construct iid k []) args) →
      alts[k]? = some (names, body) →
      (args.drop np).length = names.length →
      WcbvEval Γ fl (LBTerm.substList ((args.drop np).reverse) body) r →
      WcbvEval Γ fl (.case (iid, np) discr alts) r
  /-- ι, block (`eval_iota_block`, when `with_constructor_as_block = true`): as
      `iota`, but the discriminant evaluates to a **block** constructor node
      `.construct iid k cargs`. Uses the same `iota_red` (drop `np` params, reverse
      fields). -/
  | iota_block (hb : fl.with_constructor_as_block = true)
         {iid : InductiveId} {np k : Nat} {discr : LBTerm}
         {alts : List (List BinderName × LBTerm)} {cargs : List LBTerm}
         {names : List BinderName} {body r : LBTerm} :
      isPropositionalInductive Γ iid = false →
      WcbvEval Γ fl discr (.construct iid k cargs) →
      alts[k]? = some (names, body) →
      (cargs.drop np).length = names.length →
      WcbvEval Γ fl (LBTerm.substList ((cargs.drop np).reverse) body) r →
      WcbvEval Γ fl (.case (iid, np) discr alts) r
  /-- ι on an erased proof (`eval_iota_sing`, enabled by `with_prop_case`): a
      single-branch case on a **propositional** inductive whose discriminant
      evaluates to `box` reduces by substituting `|names|` boxes for the field
      binders of its sole branch. -/
  | iota_sing (hpc : fl.with_prop_case = true) {iid : InductiveId} {np : Nat} {discr : LBTerm}
              {names : List BinderName} {body r : LBTerm} :
      isPropositionalInductive Γ iid = true →
      WcbvEval Γ fl discr .box →
      WcbvEval Γ fl (LBTerm.substList (List.replicate names.length .box) body) r →
      WcbvEval Γ fl (.case (iid, np) discr [(names, body)]) r
  /-- Projection, non-block (`eval_proj`, when `with_constructor_as_block = false`):
      the discriminant evaluates to a **spine** `mkApps (.construct p.indType 0 []) args`
      of the projection's own inductive (constructor `0`), non-propositional; select
      and evaluate the projected field `args[p.paramCount + p.fieldIdx]`. -/
  | proj (hb : fl.with_constructor_as_block = false)
         {p : ProjectionInfo} {discr : LBTerm} {args : List LBTerm} {v r : LBTerm} :
      isPropositionalInductive Γ p.indType = false →
      WcbvEval Γ fl discr (LBTerm.mkApps (.construct p.indType 0 []) args) →
      args[p.paramCount + p.fieldIdx]? = some v →
      WcbvEval Γ fl v r →
      WcbvEval Γ fl (.proj p discr) r
  /-- Projection, block (`eval_proj_block`, when `with_constructor_as_block = true`):
      as `proj`, but the discriminant evaluates to a **block** constructor node
      `.construct p.indType 0 cargs` (constructor `0`). -/
  | proj_block (hb : fl.with_constructor_as_block = true)
         {p : ProjectionInfo} {discr : LBTerm} {cargs : List LBTerm} {v r : LBTerm} :
      isPropositionalInductive Γ p.indType = false →
      WcbvEval Γ fl discr (.construct p.indType 0 cargs) →
      cargs[p.paramCount + p.fieldIdx]? = some v →
      WcbvEval Γ fl v r →
      WcbvEval Γ fl (.proj p discr) r
  /-- Projection on an erased proof (`eval_proj_prop`, enabled by `with_prop_case`):
      projecting a **propositional** discriminant that evaluates to `box` yields `box`. -/
  | proj_prop (hpc : fl.with_prop_case = true) {p : ProjectionInfo} {discr : LBTerm} :
      isPropositionalInductive Γ p.indType = true →
      WcbvEval Γ fl discr .box →
      WcbvEval Γ fl (.proj p discr) .box
  /-- Guarded `fix` unfolding (`eval_fix`, enabled by `with_guarded_fix`): the
      function evaluates to a `fix` **spine** `mkApps (.fix defs idx) argsv`, and the
      accumulated argument count `#argsv` equals the recursive-argument index `rarg`
      of the selected definition (`cunfold_fix = Some (#argsv, fn)`), so this
      application supplies the principal argument; unfold the fix (via `fixSubst`) and
      apply the unfolded body to `argsv` and then to the argument. -/
  | fix_guarded (hg : fl.with_guarded_fix = true) {f a av : LBTerm}
                {defs : List (@FixDef LBTerm)} {idx : Nat} {def_i : @FixDef LBTerm}
                {argsv : List LBTerm} {r : LBTerm} :
      WcbvEval Γ fl f (LBTerm.mkApps (.fix defs idx) argsv) →
      WcbvEval Γ fl a av →
      defs[idx]? = some def_i →
      def_i.principalArgIdx = argsv.length →
      WcbvEval Γ fl
        (.app (LBTerm.mkApps (LBTerm.substList (LBTerm.fixSubst defs) def_i.body) argsv) av) r →
      WcbvEval Γ fl (.app f a) r
  /-- Stuck guarded `fix` (`eval_fix_value`, enabled by `with_guarded_fix`): the
      function evaluates to a `fix` spine `mkApps (.fix defs idx) argsv` that is still
      **under** its recursive-argument count (`#argsv < rarg`), so the application
      accumulates the argument onto the spine and is a value. -/
  | fix_stuck (hg : fl.with_guarded_fix = true) {f a av : LBTerm}
              {defs : List (@FixDef LBTerm)} {idx : Nat} {def_i : @FixDef LBTerm}
              {argsv : List LBTerm} :
      WcbvEval Γ fl f (LBTerm.mkApps (.fix defs idx) argsv) →
      WcbvEval Γ fl a av →
      defs[idx]? = some def_i →
      argsv.length < def_i.principalArgIdx →
      WcbvEval Γ fl (.app f a) (.app (LBTerm.mkApps (.fix defs idx) argsv) av)
  /-- Unguarded `fix` unfolding (`eval_fix'`, when `with_guarded_fix` is off): the
      function evaluates to a **bare** `fix` (no spine — every application unfolds
      immediately); unfold (via `fixSubst`) and apply to the argument. -/
  | fix_unguarded (hg : fl.with_guarded_fix = false) {f a av : LBTerm}
                  {defs : List (@FixDef LBTerm)} {idx : Nat} {def_i : @FixDef LBTerm} {r : LBTerm} :
      WcbvEval Γ fl f (.fix defs idx) →
      defs[idx]? = some def_i →
      WcbvEval Γ fl a av →
      WcbvEval Γ fl (.app (LBTerm.substList (LBTerm.fixSubst defs) def_i.body) av) r →
      WcbvEval Γ fl (.app f a) r
  /-- Stuck application congruence (`eval_app_cong`): the function evaluates to a
      stuck value head (`isStuckApp`: not a λ/`box`/`fix`(-app)/constructor(-app)/
      prim(-app) head), and the argument to a value. -/
  | app_cong {f a f' a' : LBTerm} :
      WcbvEval Γ fl f f' → isStuckApp fl f' = true → WcbvEval Γ fl a a' →
      WcbvEval Γ fl (.app f a) (.app f' a')

/-- λ□ evaluation with propositional cases **disabled** (MetaCoq `opt_wcbv_flags`);
    the target of `LBOptimize` and the relation `erases_correct` produces. -/
abbrev Eval (Γ : GlobalDeclarations) : LBTerm → LBTerm → Prop := WcbvEval Γ optFlags

/-- λ□ evaluation with propositional cases **enabled** (MetaCoq `default_wcbv_flags`);
    the source of `optimize_correct`. -/
abbrev EvalProp (Γ : GlobalDeclarations) : LBTerm → LBTerm → Prop := WcbvEval Γ defaultFlags

end LeanToLambdaBox
