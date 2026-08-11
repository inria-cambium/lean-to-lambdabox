import LeanToLambdaBox.Closed
import LeanToLambdaBox.Semantics.Metatheory

/-!
# The ι reversal bridge — a β-chain of field applications *is* MetaRocq's `iota_red`

The λ□ ι rule (`WcbvEval.iota`, `Semantics/Eval.lean`) reduces a `.case` to
`substList ((args.drop np).reverse) body`: **one** simultaneous substitution of the
constructor's fields, **reversed**, into the selected alternative's body. The erasure
side produces the same reduct in an entirely different shape: `Erases.cases` erases a
minor to its λ-telescope `mkLambdas names body`, and the source ι rule applies that
minor to the fields *in order*, so the erased reduct is the application spine
`mkApps (mkLambdas names body) fields`, contracted by a **chain of β steps**.

This module reconciles the two, over closed field values:

* `wcbvEval_mkApps_head_congr` — replacing the head of an application spine by one with
  the same evaluations preserves evaluation (the β chain contracts the *innermost*
  application first, while `WcbvEval` dispatches on the outermost);
* `value_mkApps_construct_args` — the arguments of a non-block constructor-spine value
  are themselves values (so they evaluate to themselves, `value_final`);
* `wcbvEval_mkApps_mkLambdas_substList` — the bridge itself.

It sits between `Closed.lean` (which owns the de-Bruijn half, `substList_reverse_subst`)
and `ErasesCorrectIota.lean` (its only consumer), and mentions neither `Erases` nor
lean4lean: everything here is target-side, hence `sorryAx`-free.
-/

namespace LeanToLambdaBox

open Lean

/-! ## Head congruence for an application spine -/

/-- **Replacing the head of an application spine by one with the same evaluations
preserves evaluation.** Every `.app` rule of `WcbvEval` (`beta`, `app_box`,
`construct_app`, `fix_guarded`, `fix_stuck`, `fix_unguarded`, `app_cong`) evaluates its
function first and dispatches on that *value*, so the replacement is sound rule by rule;
the spine is then traversed from the front, one application at a time. -/
theorem wcbvEval_mkApps_head_congr {E : GlobalDeclarations} {fl : WcbvFlags} :
    ∀ (args : List LBTerm) {g h : LBTerm},
      (∀ {v : LBTerm}, WcbvEval E fl g v → WcbvEval E fl h v) →
      ∀ {r : LBTerm}, WcbvEval E fl (LBTerm.mkApps g args) r →
        WcbvEval E fl (LBTerm.mkApps h args) r := by
  intro args
  induction args with
  | nil => intro g h hgh r hev; exact hgh hev
  | cons a as ih =>
      intro g h hgh r hev
      rw [LBTerm.mkApps] at hev ⊢
      refine ih (g := .app g a) (h := .app h a) ?_ hev
      intro v hv
      cases hv with
      | beta hf ha hb => exact .beta (hgh hf) ha hb
      | app_box hf ha => exact .app_box (hgh hf) ha
      | construct_app hb hf harity hlt ha => exact .construct_app hb (hgh hf) harity hlt ha
      | fix_guarded hg hf ha hsel hpai hunf => exact .fix_guarded hg (hgh hf) ha hsel hpai hunf
      | fix_stuck hg hf ha hsel hlt => exact .fix_stuck hg (hgh hf) ha hsel hlt
      | fix_unguarded hg hf hsel ha hunf => exact .fix_unguarded hg (hgh hf) hsel ha hunf
      | app_cong hf hstuck ha => exact .app_cong (hgh hf) hstuck ha

/-! ## The arguments of a constructor-spine value are values -/

/-- **The arguments accumulated onto a non-block constructor spine are values.** Inverts
`Value.construct_app_val` down the spine; `Value.app_stuck` is excluded by
`isStuckApp_construct_spine` and `Value.fix_app_val` by `mkApps_construct_ne_fix`.
Composed with `eval_to_value` and `value_final` this is what supplies the ι bridge's
"every field evaluates to itself". -/
theorem value_mkApps_construct_args {E : GlobalDeclarations} {fl : WcbvFlags}
    {iid : InductiveId} {c : Nat} :
    ∀ (n : Nat) {args : List LBTerm}, args.length = n →
      Value E fl (LBTerm.mkApps (.construct iid c []) args) → ∀ x ∈ args, Value E fl x := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro args hn hv x hx
    rcases List.eq_nil_or_concat args with rfl | ⟨init, last, rfl⟩
    · exact absurd hx (by simp)
    · rw [List.concat_eq_append, LBTerm.mkApps_concat] at hv
      have hinit : init.length < n := by
        rw [← hn]; simp only [List.concat_eq_append, List.length_append, List.length_cons]; omega
      have hx' : x ∈ init ++ [last] := by rwa [List.concat_eq_append] at hx
      cases hv with
      | atom h => exact absurd h (by simp [atomValue])
      | construct_app_val hb hval hd_eq harity hlt hlastv =>
          rcases List.mem_append.mp hx' with hxi | hxl
          · exact ih init.length hinit rfl hval x hxi
          · rw [List.mem_singleton.mp hxl]; exact hlastv
      | app_stuck hf hstuck hlastv =>
          rw [isStuckApp_construct_spine] at hstuck; exact absurd hstuck (by simp)
      | fix_app_val hg hval hd_eq hrarg hlt hlastv =>
          exact absurd hd_eq LBTerm.mkApps_construct_ne_fix

/-! ## The bridge -/

/-- **β-chain ↔ reversing `iota_red`.** Applying an alternative's λ-telescope to the
constructor's fields *in order* and substituting the **reversed** field list into its
body have the same evaluations — provided the telescope has exactly the fields' length
and the fields are closed values.

The closedness is not slack. At two fields the β chain reduces to
`subst f₁ 0 (subst f₀ 1 body)` while `substList [f₁, f₀] body` is
`subst f₀ 0 (subst f₁ 0 body)`, and `LBTerm.subst_subst` makes the two agree exactly when
`subst f₀ 0 f₁ = f₁`. Take `body = .bvar 0` and `f₁ = .lambda n (.bvar 1)` — a genuine
`WcbvEval` value at a nonempty ambient context: the β chain yields `f₁`, the `substList`
form yields `.lambda n (LBTerm.shift 1 0 f₀)`. So the ι forward simulation is *false* for
field values with loose de Bruijn indices; the `LBClosed` thread of
`erases_correct_dataι` is exactly MetaRocq's own `closedn 0` convention, a faithfulness
constraint rather than a modelling shortcut. The de-Bruijn half of the argument is
`LBTerm.substList_reverse_subst` (`Closed.lean`), which carries the same proviso. -/
theorem wcbvEval_mkApps_mkLambdas_substList {E : GlobalDeclarations} {fl : WcbvFlags} :
    ∀ (fields : List LBTerm) (names : List BinderName) (body : LBTerm),
      names.length = fields.length →
      (∀ x ∈ fields, WcbvEval E fl x x) → (∀ x ∈ fields, LBClosed x 0) →
      ∀ {r : LBTerm}, WcbvEval E fl (LBTerm.mkApps (mkLambdas names body) fields) r →
        WcbvEval E fl (LBTerm.substList fields.reverse body) r := by
  intro fields
  induction fields with
  | nil =>
      intro names body hlen _ _ r hev
      obtain rfl : names = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      simpa only [mkLambdas, LBTerm.mkApps, List.reverse_nil, LBTerm.substList,
        List.foldl_nil] using hev
  | cons f rest ih =>
      intro names body hlen hval hcl r hev
      cases names with
      | nil => simp at hlen
      | cons n ns =>
          have hlen' : ns.length = rest.length := by simpa using hlen
          have hf : WcbvEval E fl f f := hval f (List.mem_cons_self ..)
          have hfc : LBClosed f 0 := hcl f (List.mem_cons_self ..)
          have hvalr : ∀ x ∈ rest, WcbvEval E fl x x :=
            fun x hx => hval x (List.mem_cons_of_mem _ hx)
          have hclr : ∀ x ∈ rest, LBClosed x 0 :=
            fun x hx => hcl x (List.mem_cons_of_mem _ hx)
          rw [mkLambdas, LBTerm.mkApps] at hev
          -- the single β step, as a head replacement
          have hstep : ∀ {v : LBTerm},
              WcbvEval E fl (.app (.lambda n (mkLambdas ns body)) f) v →
              WcbvEval E fl (LBTerm.subst1 f (mkLambdas ns body)) v := by
            intro v hv
            cases hv with
            | @beta _ _ n' b' av _ hfun harg hbody =>
                have hlam := eval_deterministic (WcbvEval.lam n (mkLambdas ns body)) hfun
                injection hlam with _ hb'
                subst hb'
                have : f = av := eval_deterministic hf harg
                subst this
                exact hbody
            | app_box hfun _ =>
                exact absurd (eval_deterministic (WcbvEval.lam n (mkLambdas ns body)) hfun)
                  (by simp)
            | construct_app _ hfun _ _ _ =>
                exact absurd (congrArg LBTerm.spineHead
                  (eval_deterministic (WcbvEval.lam n (mkLambdas ns body)) hfun))
                  (by simp [LBTerm.spineHead_mkApps])
            | fix_guarded _ hfun _ _ _ _ =>
                exact absurd (congrArg LBTerm.spineHead
                  (eval_deterministic (WcbvEval.lam n (mkLambdas ns body)) hfun))
                  (by simp [LBTerm.spineHead_mkApps])
            | fix_stuck _ hfun _ _ _ =>
                exact absurd (congrArg LBTerm.spineHead
                  (eval_deterministic (WcbvEval.lam n (mkLambdas ns body)) hfun))
                  (by simp [LBTerm.spineHead_mkApps])
            | fix_unguarded _ hfun _ _ _ =>
                exact absurd (eval_deterministic (WcbvEval.lam n (mkLambdas ns body)) hfun)
                  (by simp)
            | app_cong hfun hstuck _ =>
                rw [← eval_deterministic (WcbvEval.lam n (mkLambdas ns body)) hfun] at hstuck
                exact absurd hstuck (by simp [isStuckApp, isLambda])
          have hev2 : WcbvEval E fl
              (LBTerm.mkApps (LBTerm.subst1 f (mkLambdas ns body)) rest) r :=
            wcbvEval_mkApps_head_congr rest hstep hev
          rw [LBTerm.subst1, subst_mkLambdas, Nat.zero_add] at hev2
          have hres := ih ns (LBTerm.subst f ns.length body) hlen' hvalr hclr hev2
          have heq : LBTerm.substList (f :: rest).reverse body
              = LBTerm.substList rest.reverse (LBTerm.subst f ns.length body) := by
            rw [hlen', List.reverse_cons, LBTerm.substList_concat]
            simp only [LBTerm.subst1]
            rw [← LBTerm.substList_reverse_subst f rest hclr 0 body, Nat.zero_add]
          rw [heq]
          exact hres

/-! ## Non-vacuity -/

/-- **The bridge fires**, at two fields — the first regime the flat (zero-field) slice
could not reach. The telescope `λ x y. #1` applied to `[□, λ y. □]` β-reduces to `□`, and
the bridge turns that into the ι rule's own reduct
`substList [λ y. □, □] (#1) ⇓ □`: the reversal really is what makes index `1` (the
*first* field) select `□`. The second field is a λ, i.e. a genuine non-atomic closed
value, so the closedness hypothesis is exercised rather than sidestepped. -/
theorem wcbvEval_mkApps_mkLambdas_substList_fires :
    WcbvEval [] appliedFlags
      (LBTerm.substList ([(.box : LBTerm), .lambda (.named "y") .box].reverse) (.bvar 1)) .box := by
  refine wcbvEval_mkApps_mkLambdas_substList [(.box : LBTerm), .lambda (.named "y") .box]
    [.named "x", .named "y"] (.bvar 1) rfl ?_ ?_ ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact .box
    · rw [List.mem_singleton.mp hx]; exact .lam _ _
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · trivial
    · rw [List.mem_singleton.mp hx]; trivial
  · exact .beta (.beta (.lam _ _) .box (.lam _ _)) (.lam _ _) .box

end LeanToLambdaBox
