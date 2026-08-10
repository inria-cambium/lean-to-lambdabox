import LeanToLambdaBox.SubjectReduction

/-!
# Subject reduction as definitional equality (β + ζ + δ fragment) — step A3.3′

This file generalizes `SEvalβ_defeq` (the β-only subject-reduction-as-defeq) to
the larger source evaluation relation `SEvalβζδι` (β + ζ + δ + ι). The conclusion
is the same shape: if `e` translates to `ve` and `e` big-step evaluates to `v`,
then `v` translates to some `vve` definitionally equal to `ve`.

## The four new cases

* **ζ (let).** At `VExpr` level there is *no* let node: `TrExprS.letE` translates
  `letE n ty val b` straight to the body's `VExpr` `body'`, in the extended context
  `(none, .vlet ty' val') :: Δ`. lean4lean's `TrExprS.inst_let` then says the
  *substituted* body `b.instantiate1' val` translates to the **same** `body'`. So
  the ζ defeq is essentially *reflexivity* of the translated body — modulo the IH
  on the body evaluation. No new hypotheses are needed.

* **δ (const).** A constant `n` unfolds to `body` (`E n = some body`). At `VExpr`
  level this is the defeq `.const n us' ≡ ⟦body⟧`, which holds because a real
  `VEnv` registers each definition as an `extra` defeq (`addDefEq ci.toDefEq`). We
  do not reconstruct that from the kernel translation; instead we **thread it as a
  hypothesis** via `SEnvConsistent`, asserting exactly the defeq facts the δ case
  needs. This is the source-env ↔ `VEnv` consistency the project notes call for.

* **ι (casesOn).** SCOPED OUT of this file — see the report. The pinned lean4lean
  fork *does* expose an ι/recursor rule (`IsDefEq.pat`, fed by `VEnv.pats` /
  `VEnv.addInduct`), but it is not yet chainable into a concrete instance, so the
  iota fact is threaded as a per-reduction defeq hypothesis (`IotaConsistent`,
  `SourceEvalData.lean`) whose *use* requires fully inverting the `casesOn`
  translation spine (a nested application of the translated `pre`/`discr`/`minors`).
  That is a substantial separate development, carried out in
  `SubjectReductionIota.lean`; we deliberately do not fake it here. `ctor_val` is
  handled (it is a value, structurally).

`SEvalβ`/`SEvalβ_defeq` and all their committed metatheory are left untouched.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-- **Source-env ↔ `VEnv` consistency for δ-unfolding.**

The source environment `Esrc : SEnv` and the lean4lean `VEnv` `env` agree on
constant unfolding: whenever `Esrc n = some body` and the constant application
`.const n us` translates to a `VExpr` `cve`, the body `body` also translates (to
some `bve`) and the constant is definitionally equal to its unfolding
(`cve ≡ bve`).

This is exactly the δ fact a well-formed `VEnv` provides for every definition (it
registers `def n := body` as the `extra` defeq `.const n us ≡ ⟦body⟧`); we take it
as a hypothesis rather than reconstructing it from the kernel translation, since
`SEnv` is an *opaque* unfolding map with no a-priori link to `env.defeqs`.

`U` is the universe-parameter count and `Γ` the typing context at which the defeq
is required (the context is universally quantified so the predicate can be applied
under binders). -/
def SEnvConsistent (env : VEnv) (Us : List Name) (Esrc : SEnv) : Prop :=
  ∀ {Δ : VLCtx} {n : Name} {us : List Level} {body : Expr} {cve : VExpr},
    Esrc n = some body →
    TrExprS env Us Δ (.const n us) cve →
    ∃ bve, TrExprS env Us Δ body bve ∧ env.IsDefEqU Us.length Δ.toCtx cve bve

/-- The head of a translated application spine itself translates. -/
theorem TrExprS_spine_head {env : VEnv} {Us : List Name} {Δ : VLCtx} :
    ∀ (args : List Expr) {head : Expr} {ve : VExpr},
      TrExprS env Us Δ (args.foldl Expr.app head) ve →
      ∃ hve, TrExprS env Us Δ head hve
  | [], _, _, htr => ⟨_, htr⟩
  | a :: as, head, ve, htr => by
      simp only [List.foldl_cons] at htr
      obtain ⟨hve', htr'⟩ := TrExprS_spine_head as htr
      cases htr' with
      | app _ _ htrhead _ => exact ⟨_, htrhead⟩

/-- **Subject reduction along a constructor application spine.**

If a head `head` translating to `hve` is defeq to `hve₂` (the value head's
translation), and each argument `args[i]` evaluates (in the subject-reduction
sense: translates to `a'`, the value `vs[i]` translates to some `v'`, and
`a' ≡ v'`) to `vs[i]`, then the whole spine `args.foldl Expr.app head` translating
to `ve` has its value `vs.foldl Expr.app head₂` translating to some `vve` defeq to
`ve`.

This is the spine-level congruence powering the `ctor_val` case: the head is a
`.const` (unchanged), and each argument reduces to a defeq value, so the whole
application is defeq to the application of the reduced arguments. -/
theorem SEvalβζδ_defeq_spine {env : VEnv} (henv : env.WF) {Us : List Name}
    {Δ : VLCtx} (hΔ : VLCtx.WF env Us.length Δ)
    (P : Expr → Expr → Prop)
    (hP : ∀ {e v : Expr} {ev : VExpr}, TrExprS env Us Δ e ev → P e v →
      ∃ vv, TrExprS env Us Δ v vv ∧ env.IsDefEqU Us.length Δ.toCtx ev vv) :
    ∀ (n : Nat) (args vs : List Expr) (head head₂ : Expr) (hve hve₂ : VExpr),
      args.length = n → vs.length = n →
      TrExprS env Us Δ head hve → TrExprS env Us Δ head₂ hve₂ →
      env.IsDefEqU Us.length Δ.toCtx hve hve₂ →
      (∀ i (h : i < args.length) (h2 : i < vs.length), P args[i] vs[i]) →
      ∀ {ve : VExpr}, TrExprS env Us Δ (args.foldl Expr.app head) ve →
        ∃ vve, TrExprS env Us Δ (vs.foldl Expr.app head₂) vve ∧
          env.IsDefEqU Us.length Δ.toCtx ve vve := by
  have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
  intro n
  -- Strong induction on the spine length, peeling the LAST argument (the outermost
  -- `.app` of the foldl spine), which `TrExprS.app` inverts directly.
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro args vs head head₂ hve hve₂ hlenA hlenV hh hh₂ hd hargs ve htr
    rcases List.eq_nil_or_concat args with rfl | ⟨init, last, rfl⟩
    · -- empty spine: `vs` empty too; value head is defeq to `head`'s translation.
      have : vs = [] := List.eq_nil_of_length_eq_zero (by simp_all)
      subst this
      simp only [List.foldl]
      simp only [List.foldl] at htr
      exact ⟨hve₂, hh₂,
        VEnv.IsDefEqU.trans henv hΓ (TrExprS.uniq henv
          (VLCtx.IsDefEq.refl henv.ordered hΔ) htr hh) hd⟩
    · -- `vs` must also be a snoc list `vinit ++ [vlast]` of matching length.
      rcases List.eq_nil_or_concat vs with rfl | ⟨vinit, vlast, rfl⟩
      · simp [List.concat_eq_append] at hlenA hlenV; omega
      · rw [List.concat_eq_append, List.length_append] at hlenA
        rw [List.concat_eq_append, List.length_append] at hlenV
        simp only [List.length_singleton] at hlenA hlenV
        have hlen : init.length = vinit.length := by omega
        -- Spine = `(init.foldl app head).app last`; invert the outer app.
        rw [List.concat_eq_append, List.foldl_append, List.foldl_cons,
          List.foldl_nil] at htr
        simp only [List.concat_eq_append] at hargs
        cases htr with
        | @app fve A B lastVE _Δ _f _a hTf hTa htrf htrlast =>
          -- IH on the init spine (strictly shorter).
          have hargsInit : ∀ i (h : i < init.length) (h2 : i < vinit.length),
              P init[i] vinit[i] := by
            intro i h h2
            have := hargs i (by simp; omega) (by simp; omega)
            rwa [List.getElem_append_left h, List.getElem_append_left h2] at this
          obtain ⟨fvv, htrfvv, hfdef⟩ :=
            ih init.length (by omega) init vinit head head₂ hve hve₂ rfl hlen.symm
              hh hh₂ hd hargsInit htrf
          -- The last argument: its value translates defeq (via P/hP).
          have hlastP : P last vlast := by
            have h := hargs init.length (by simp) (by simp [hlen])
            rw [List.getElem_append_right (Nat.le_refl _),
              List.getElem_append_right (hlen ▸ Nat.le_refl init.length)] at h
            simpa [hlen] using h
          obtain ⟨lvv, htrlvv, hldef⟩ := hP htrlast hlastP
          -- Reassemble the value spine `(vinit.foldl app head₂).app vlast`.
          refine ⟨.app fvv lvv, ?_, ?_⟩
          · rw [List.concat_eq_append, List.foldl_append, List.foldl_cons,
              List.foldl_nil]
            have hTfvv : env.HasType Us.length Δ.toCtx fvv (.forallE A B) :=
              hTf.defeqU_l henv hΓ hfdef
            have hTlvv : env.HasType Us.length Δ.toCtx lvv A :=
              hTa.defeqU_l henv hΓ hldef
            exact .app hTfvv hTlvv htrfvv htrlvv
          · have hfd : env.IsDefEq Us.length Δ.toCtx fve fvv (.forallE A B) :=
              VEnv.IsDefEqU.of_l henv hΓ hfdef hTf
            have hld : env.IsDefEq Us.length Δ.toCtx lastVE lvv A :=
              VEnv.IsDefEqU.of_l henv hΓ hldef hTa
            exact ⟨_, .appDF hfd hld⟩

/-- **Subject reduction as definitional equality (β + ζ + δ fragment).**

If `e` translates to `ve` and `e` evaluates to `v` under `SEvalβζδ`, then `v`
translates to some `vve` definitionally equal to `ve`.

Requires `env.WF`, `VLCtx.WF` of the context, and `SEnvConsistent` linking the
source unfolding map to the `VEnv` (for the δ case). -/
theorem SEvalβζδ_defeq {env : VEnv} (henv : env.WF) {Us : List Name} {Δ : VLCtx}
    (hΔ : VLCtx.WF env Us.length Δ) {Esrc : SEnv}
    (hcon : SEnvConsistent env Us Esrc) {e v : Expr} {ve : VExpr}
    (htr : TrExprS env Us Δ e ve)
    (hev : SEvalβζδ Esrc e v) :
    ∃ vve, TrExprS env Us Δ v vve ∧ env.IsDefEqU Us.length Δ.toCtx ve vve := by
  induction hev generalizing ve Δ with
  | lam n ty b bi =>
      exact ⟨ve, htr, VEnv.IsDefEqU.refl (htr.wf henv.ordered hΔ)⟩
  | @beta f a n ty b bi av r hf ha hbody ihf iha ihbody =>
      cases htr with
      | @app f' A B a' _Δ _f _a hTf hTa htrf htra =>
        obtain ⟨fv, htrfv, hfd⟩ := ihf hΔ htrf
        cases htrfv with
        | @lam ty' _Δ _ty _body body' _name _bi hty' htrty htrb =>
          obtain ⟨av_v, htrav, had⟩ := iha hΔ htra
          have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
          have hΔ' : VLCtx.WF env Us.length ((none, .vlam ty') :: Δ) := ⟨hΔ, nofun, hty'⟩
          obtain ⟨B'', hbodyT⟩ := htrb.wf henv.ordered hΔ'
          obtain ⟨u, hty'sort⟩ := hty'
          have lamT1 : env.HasType Us.length Δ.toCtx (.lam ty' body') (.forallE ty' B'') :=
            VEnv.HasType.lam hty'sort hbodyT
          have lamT2 : env.HasType Us.length Δ.toCtx (.lam ty' body') (.forallE A B) :=
            hTf.defeqU_l henv hΓ hfd
          have huForall : env.IsDefEqU Us.length Δ.toCtx (.forallE A B) (.forallE ty' B'') :=
            VEnv.IsDefEq.uniqU henv hΓ lamT2 lamT1
          obtain ⟨⟨w, hAty'⟩, _⟩ := VEnv.IsDefEqU.forallE_inv henv hΓ huForall
          have hadT : env.IsDefEq Us.length Δ.toCtx a' av_v A :=
            VEnv.IsDefEqU.of_l henv hΓ had hTa
          have havT : env.HasType Us.length Δ.toCtx av_v ty' :=
            (hadT.hasType.2).defeqU_r henv hΓ ⟨_, hAty'⟩
          have htrbody : TrExprS env Us Δ (b.instantiate1' av) (body'.inst av_v) :=
            TrExprS.inst henv.ordered havT htrb htrav
          obtain ⟨vve, htrr, hrd⟩ := ihbody hΔ htrbody
          refine ⟨vve, htrr, ?_⟩
          have hfdT : env.IsDefEq Us.length Δ.toCtx f' (.lam ty' body') (.forallE A B) :=
            VEnv.IsDefEqU.of_l henv hΓ hfd hTf
          have step1 : env.IsDefEq Us.length Δ.toCtx
              (.app f' a') (.app (.lam ty' body') av_v) (B.inst a') :=
            .appDF hfdT hadT
          have step2 : env.IsDefEq Us.length Δ.toCtx
              (.app (.lam ty' body') av_v) (body'.inst av_v) (B''.inst av_v) :=
            .beta hbodyT havT
          have hcong : env.IsDefEqU Us.length Δ.toCtx (.app f' a') (body'.inst av_v) :=
            VEnv.IsDefEqU.trans henv hΓ ⟨_, step1⟩ ⟨_, step2⟩
          exact VEnv.IsDefEqU.trans henv hΓ hcong hrd
  | @zeta n ty val b nd vv r hval hbody ihval ihbody =>
      -- ζ: `letE` translates straight to the body's VExpr `ve`; substituting the
      -- bound value into the body translates to the SAME `ve` (TrExprS.inst_let).
      cases htr with
      | @letE val' ty' _ _ _ _ body' _ _ hValT htrty htrval htrb =>
          have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
          -- Subject reduction on the bound value: `val` evaluates to `vv`; both
          -- translate, and `val' ≡ vvv`. So `vv` translates *up to defeq* to the
          -- let value `val'`, hence `b.instantiate1' vv` translates up to defeq to
          -- the SAME body VExpr `body' = ve` (TrExpr.inst_let).
          obtain ⟨vvv, htrvv, hvald⟩ := ihval hΔ htrval
          have hvvTrExpr : TrExpr env Us Δ vv val' :=
            ⟨vvv, htrvv, VEnv.IsDefEqU.symm hvald⟩
          have hΔlet : VLCtx.WF env Us.length ((none, .vlet ty' val') :: Δ) :=
            ⟨hΔ, nofun, hValT⟩
          have hbodyTrExpr : TrExpr env Us ((none, .vlet ty' val') :: Δ) b ve :=
            ⟨ve, htrb, VEnv.IsDefEqU.refl (htrb.wf henv.ordered hΔlet)⟩
          obtain ⟨sub', htrsub, hsubd⟩ :=
            TrExpr.inst_let henv hΔ hValT hbodyTrExpr hvvTrExpr
          -- IH on the body evaluation: `b.instantiate1' vv` evaluates to `r`.
          obtain ⟨vve, htrr, hrd⟩ := ihbody hΔ htrsub
          -- Assemble: `ve = body' ≡ sub' ≡ vve`.
          exact ⟨vve, htrr,
            VEnv.IsDefEqU.trans henv hΓ (VEnv.IsDefEqU.symm hsubd) hrd⟩
  | @delta n us body r hunf hbodyev ihbody =>
      obtain ⟨bve, htrb, hdefeq⟩ := hcon hunf htr
      obtain ⟨vve, htrr, hrd⟩ := ihbody hΔ htrb
      exact ⟨vve, htrr, VEnv.IsDefEqU.trans henv hΔ.toCtx hdefeq hrd⟩
  | @ctor_val cn us args vs hl hargs ihargs =>
      -- The head `.const cn us` is unchanged; each argument subject-reduces to a
      -- defeq value, so the whole application is defeq to the reduced application.
      obtain ⟨hve, htrhead⟩ := TrExprS_spine_head args htr
      refine SEvalβζδ_defeq_spine henv hΔ
        (fun e v => ∀ {ev}, TrExprS env Us Δ e ev →
          ∃ vv, TrExprS env Us Δ v vv ∧ env.IsDefEqU Us.length Δ.toCtx ev vv)
        (fun htr p => p htr)
        args.length args vs (Expr.const cn us) (Expr.const cn us) hve hve rfl hl.symm
        htrhead htrhead (VEnv.IsDefEqU.refl (htrhead.wf henv.ordered hΔ))
        (fun i h h2 => ihargs i h hΔ) htr

end LeanToLambdaBox
