import LeanToLambdaBox.SourceEval
import LeanToLambdaBox.SubjectReduction

/-!
# Source-side evaluation with saturated constructor data (step A4)

`SEvalData Γ E` is the source big-step weak call-by-value evaluation for the **data
fragment**: the β + ζ + δ core (as in `SEvalβζδ`) plus a *saturated* constructor-value
rule `ctor_val` that carries the arity bound `args.length ≤ ar` in the eval node,
where `ar = Γ.ctorArities cn` is the constructor's declared arity. This is the source
relation over which `erases_correct_data` (the forward simulation at MetaRocq's
non-block `appliedFlags`) is proved.

Two design points:

* **The saturation bound lives here, on the source.** MetaRocq's `iota`/`proj`
  evaluation rules carry a `#args = pars + cstr_nargs` premise; the P0 `Semantics/`
  model deliberately does *not* replicate that on the target `WcbvEval` — instead the
  bound rides on the source `ctor_val` node (`hsat : args.length ≤ ar`), which is the
  right place for it (the source is where saturation is a real, checkable fact about
  the program).
* **It is a conservative extension of `SEvalβζδ`.** The forgetful map
  `SEvalData.toβζδ` drops the registration/arity data, so the β+ζ+δ subject reduction
  `SEvalβζδ_defeq` applies verbatim (via `toβζδ`) to any `SEvalData` evaluation — no
  new metatheory of `SEvalβζδ` is touched.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-- Weak call-by-value big-step evaluation of source `Expr`, the **data fragment**:
β + ζ + δ (as `SEvalβζδ`) plus a *saturated* `ctor_val` whose arity bound
`args.length ≤ ar` is recorded in the eval node (with `ar = Γ.ctorArities cn`).

The constructor spine encoding mirrors the `Erases` `ctor`/`ctor_head` rules exactly
(`args.foldl Expr.app (.const cn us)`), so values line up with the erasure relation. -/
inductive SEvalData (Γ : ErasureCtx) (E : SEnv) : Expr → Expr → Prop
  /-- λ-abstractions are values. -/
  | lam (n : Name) (ty b : Expr) (bi : BinderInfo) :
      SEvalData Γ E (.lam n ty b bi) (.lam n ty b bi)
  /-- β: function evaluates to a λ, argument to a value, then the substituted body. -/
  | beta {f a : Expr} {n : Name} {ty b : Expr} {bi : BinderInfo} {av r : Expr} :
      SEvalData Γ E f (.lam n ty b bi) → SEvalData Γ E a av →
      SEvalData Γ E (b.instantiate1' av 0) r →
      SEvalData Γ E (.app f a) r
  /-- ζ: let-binding evaluates the bound value then the substituted body. -/
  | zeta {n : Name} {ty v b : Expr} {nd : Bool} {vv r : Expr} :
      SEvalData Γ E v vv → SEvalData Γ E (b.instantiate1' vv 0) r →
      SEvalData Γ E (.letE n ty v b nd) r
  /-- δ: unfold a defined constant and evaluate its body. -/
  | delta {n : Name} {us : List Level} {body r : Expr} :
      E n = some body → SEvalData Γ E body r → SEvalData Γ E (.const n us) r
  /-- A **saturated** constructor application is a value; evaluate its arguments. The
      head `cn` is a registered constructor (`Γ.ctors cn = some (iid, cidx)`) with
      declared arity `ar` (`Γ.ctorArities cn = some ar`), and the number of supplied
      arguments does not exceed it (`args.length ≤ ar`). -/
  | ctor_val {cn : Name} {us : List Level} {iid : InductiveId} {cidx ar : Nat}
      {args vs : List Expr}
      (hc : Γ.ctors cn = some (iid, cidx))
      (har : Γ.ctorArities cn = some ar)
      (hsat : args.length ≤ ar)
      (hl : args.length = vs.length)
      (hargs : ∀ i (h : i < args.length), SEvalData Γ E args[i] (vs[i]'(hl ▸ h))) :
      SEvalData Γ E (args.foldl Expr.app (.const cn us))
        (vs.foldl Expr.app (.const cn us))

/-- **Forgetful map to the β+ζ+δ fragment.** Every `SEvalData` evaluation is an
`SEvalβζδ` evaluation (dropping the registration/arity data on `ctor_val`). This lets
the data-fragment simulation reuse the β+ζ+δ subject reduction `SEvalβζδ_defeq`
verbatim — `SEvalβζδ` and its committed metatheory are left untouched. -/
theorem SEvalData.toβζδ {Γ : ErasureCtx} {E : SEnv} {e v : Expr}
    (h : SEvalData Γ E e v) : SEvalβζδ E e v := by
  induction h with
  | lam n ty b bi => exact .lam n ty b bi
  | beta _ _ _ ihf iha ihb => exact .beta ihf iha ihb
  | zeta _ _ ihv ihb => exact .zeta ihv ihb
  | delta hu _ ih => exact .delta hu ih
  | ctor_val _ _ _ hl _ ihargs => exact .ctor_val hl (fun i h => ihargs i h)

/-- **A registered-head spine never `SEvalData`-evaluates to a λ.** If `e` is a
`SEvalData`-evaluation whose source is a constructor/`casesOn`-headed application
spine `args.foldl Expr.app (.const cn us)` (with `cn` registered), its value `r` is
never a λ-abstraction.

The `hnf` premise (a registered head has no δ-unfolding — exactly the first component
of `ErasesEnvDelta`) blocks the `delta` rule on a registered head, so only `ctor_val`
fires and delivers a *const-spine* value; `beta` is impossible because the shorter
head spine would itself have to evaluate to a λ (refuted by the IH).

This is the data analogue of `SEvalβδ_const_spine_elim`; it discharges the
`ctor`/`cases` spine disjunct of `Erases.app_inv` in the `beta` case of
`erases_correct_data`. -/
theorem SEvalData_const_spine_lam_elim {Γ : ErasureCtx} {E : SEnv}
    (hnf : ∀ {n : Name} {body : Expr}, E n = some body →
              Γ.ctors n = none ∧ Γ.casesOns n = none)
    {e r : Expr} (hev : SEvalData Γ E e r) :
    ∀ {cn : Name} {us : List Level} {args : List Expr},
      e = args.foldl Expr.app (.const cn us) →
      (Γ.ctors cn ≠ none ∨ Γ.casesOns cn ≠ none) →
      ¬ ∃ (n : Name) (ty b : Expr) (bi : BinderInfo), r = .lam n ty b bi := by
  induction hev with
  | lam n ty b bi =>
      intro cn us args heq _
      exact absurd heq.symm foldl_app_const_ne_lam
  | @beta f a n ty b bi av r hf ha hbody ihf _ _ =>
      intro cn us args heq hreg
      rcases List.eq_nil_or_concat args with rfl | ⟨init, last, rfl⟩
      · exact absurd heq (by simp)
      · rw [List.concat_eq_append, List.foldl_append, List.foldl_cons,
          List.foldl_nil] at heq
        injection heq with hf_eq _
        exact absurd (ihf hf_eq hreg) (by exact fun h => h ⟨n, ty, b, bi, rfl⟩)
  | @zeta n ty v b nd vv r hval hbody _ _ =>
      intro cn us args heq _
      exact absurd heq.symm foldl_app_const_ne_letE
  | @delta n us body r hunf hbodyev _ =>
      intro cn us' args heq hreg
      rcases List.eq_nil_or_concat args with rfl | ⟨init, last, rfl⟩
      · simp only [List.foldl] at heq
        cases heq
        rcases hreg with h | h
        · exact absurd (hnf hunf).1 h
        · exact absurd (hnf hunf).2 h
      · rw [List.concat_eq_append, List.foldl_append, List.foldl_cons,
          List.foldl_nil] at heq
        exact absurd heq (by simp)
  | @ctor_val cn us iid cidx ar args vs hc har hsat hl hargs _ =>
      intro cn' us' args' _ _
      rintro ⟨n, ty, b, bi, hlam⟩
      exact foldl_app_const_ne_lam hlam

end LeanToLambdaBox
