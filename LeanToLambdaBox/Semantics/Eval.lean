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
| `construct`| `eval_construct_block`  | (block form) |
| `construct_app` | `eval_construct` (accumulate an applied arg) | `¬ with_constructor_as_block` |
| `iota`     | `eval_iota_block`       | discriminant's inductive not `Prop` |
| `iota_sing`| `eval_iota_sing`        | `with_prop_case` |
| `proj`     | `eval_proj_block`       | projectee's inductive not `Prop` |
| `proj_prop`| `eval_proj_prop`        | `with_prop_case` |
| `fix_guarded` | `eval_fix`           | `with_guarded_fix` |
| `fix_stuck`   | `eval_fix_value`     | `with_guarded_fix` |
| `fix_unguarded`| `eval_fix'`         | `¬ with_guarded_fix` |
| `app_cong` | `eval_app_cong`         | head is a stuck application (`isStuckApp`) |

**No `cofix`:** `LBTerm` has no `cofix` node, so MetaCoq's `eval_cofix_case`/
`eval_cofix_proj` are unrepresentable — nothing to model.

Both constructor representations are supported: the **block form** `.construct iid
k args` (args inside — what the `Erases` relation produces and `erases_correct`/
`LBOptimize_correct` use), and the **non-block/applied form** `.construct iid c []`
applied via `.app` (what the shipping `visitExpr` emits), evaluated by
`construct_app` under `with_constructor_as_block = false` — it accumulates each
applied argument onto the constructor value up to its arity, after which the block
`iota`/`proj` rules scrutinise it directly.
The `fix` rules dispatch on the *evaluated* function head (MetaCoq's `mkApps
(tFix ..) argsv` spine), so a `fix` reached through, e.g., a `const` unfolds too.
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
  /-- Constructor: evaluate each argument (block form; the head is saturated).
      (`eval_construct_block`) -/
  | construct {iid : InductiveId} {k : Nat} {args vs : List LBTerm}
      (hl : args.length = vs.length)
      (hargs : ∀ i (h : i < args.length), WcbvEval Γ fl args[i] (vs[i]'(hl ▸ h))) :
      WcbvEval Γ fl (.construct iid k args) (.construct iid k vs)
  /-- Non-block constructor application (`eval_construct`, enabled when
      `with_constructor_as_block = false`): the shipping `visitExpr` emits a
      constructor `.construct iid c []` **applied** via `.app` to its arguments.
      This rule evaluates that applied form, accumulating each argument onto the
      (under-applied) constructor value until it is saturated. A saturated or
      over-applied constructor head has no rule here (`args.length < arity`), and
      `app_cong` excludes constructor heads, so it does not fire. -/
  | construct_app (hb : fl.with_constructor_as_block = false)
      {f a a' : LBTerm} {iid : InductiveId} {c : Nat} {args : List LBTerm} {ar : Nat} :
      WcbvEval Γ fl f (.construct iid c args) →
      constructorArity Γ iid c = some ar →
      args.length < ar →
      WcbvEval Γ fl a a' →
      WcbvEval Γ fl (.app f a) (.construct iid c (args ++ [a']))
  /-- ι: the discriminant evaluates to a constructor of a **non-propositional**
      inductive; select the matching alternative and evaluate its body with the
      constructor's args substituted for the field binders. (`eval_iota_block`) -/
  | iota {iid : InductiveId} {np k : Nat} {discr : LBTerm}
         {alts : List (List BinderName × LBTerm)} {cargs : List LBTerm}
         {names : List BinderName} {body r : LBTerm} :
      isPropositionalInductive Γ iid = false →
      WcbvEval Γ fl discr (.construct iid k cargs) →
      alts[k]? = some (names, body) →
      WcbvEval Γ fl (LBTerm.substList cargs body) r →
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
  /-- Projection: the discriminant evaluates to a constructor of a
      **non-propositional** inductive; select and evaluate the projected field
      (offset by the parameter count). (`eval_proj_block`) -/
  | proj {p : ProjectionInfo} {discr : LBTerm} {iid : InductiveId} {k : Nat}
         {cargs : List LBTerm} {v r : LBTerm} :
      isPropositionalInductive Γ p.indType = false →
      WcbvEval Γ fl discr (.construct iid k cargs) →
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
      function evaluates to a `fix`, and its principal argument evaluates to a
      **constructor value**; unfold the recursive occurrences and apply. -/
  | fix_guarded (hg : fl.with_guarded_fix = true) {f arg : LBTerm}
                {defs : List (@FixDef LBTerm)} {i : Nat} {def_i : @FixDef LBTerm} {argv r : LBTerm} :
      WcbvEval Γ fl f (.fix defs i) →
      defs[i]? = some def_i →
      WcbvEval Γ fl arg argv →
      isConstructorValue argv = true →
      WcbvEval Γ fl (.app (LBTerm.substList ((List.range defs.length).map (fun j => LBTerm.fix defs j)) def_i.body) argv) r →
      WcbvEval Γ fl (.app f arg) r
  /-- Stuck guarded `fix` (`eval_fix_value`, enabled by `with_guarded_fix`): the
      function evaluates to a `fix` but its principal argument is **not** a
      constructor value, so the application is a value. -/
  | fix_stuck (hg : fl.with_guarded_fix = true) {f arg : LBTerm}
              {defs : List (@FixDef LBTerm)} {i : Nat} {argv : LBTerm} :
      WcbvEval Γ fl f (.fix defs i) →
      WcbvEval Γ fl arg argv →
      isConstructorValue argv = false →
      WcbvEval Γ fl (.app f arg) (.app (.fix defs i) argv)
  /-- Unguarded `fix` unfolding (`eval_fix'`, when `with_guarded_fix` is off): the
      function evaluates to a `fix`; unfold on any value argument. -/
  | fix_unguarded (hg : fl.with_guarded_fix = false) {f arg : LBTerm}
                  {defs : List (@FixDef LBTerm)} {i : Nat} {def_i : @FixDef LBTerm} {argv r : LBTerm} :
      WcbvEval Γ fl f (.fix defs i) →
      defs[i]? = some def_i →
      WcbvEval Γ fl arg argv →
      WcbvEval Γ fl (.app (LBTerm.substList ((List.range defs.length).map (fun j => LBTerm.fix defs j)) def_i.body) argv) r →
      WcbvEval Γ fl (.app f arg) r
  /-- Stuck application congruence (`eval_app_cong`): the function evaluates to a
      stuck value head (not a λ/`box`/`fix`), and the argument to a value. -/
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
