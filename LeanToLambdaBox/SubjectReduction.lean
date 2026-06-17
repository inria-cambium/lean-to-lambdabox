import LeanToLambdaBox.SourceEval
import LeanToLambdaBox.Erasability
import Lean4Lean.Verify.Typing.Expr
import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Theory.Typing.UniqueTyping
import Lean4Lean.Theory.Typing.Injectivity

/-!
# Subject reduction as definitional equality (β fragment) — step A3.3

This file proves the gating lemma for erasure correctness on the pure β
fragment: if a source `Expr` `e` translates to a `VExpr` `ve` (`TrExprS`) and `e`
big-step evaluates to a value `v` (under the β-only relation `SEvalβ`), then `v`
also translates to *some* `vve`, and `ve` is definitionally equal to `vve`.

The β case is the heart: inverting the redex translation gives translations of
the function and argument; the IH on the function evaluation gives a translated
λ defeq to `f'`; the IH on the argument gives the value's translation; and
`TrExprS.inst` + lean4lean's `IsDefEq` β-rule (`IsDefEq.beta`) + congruence
(`appDF`) + transitivity assemble the defeq, with the lambda-domain alignment
discharged by type uniqueness (`IsDefEq.uniqU` + `IsDefEqU.forallE_inv`).

We work with the β-only fragment `SEvalβ` (λ-abstractions are values; β-redexes
reduce). The full `SEval`'s `zeta`/`delta`/`ctor_val` cases are out of scope here
(`delta` would need source-env ↔ `VEnv` consistency); the priority is a complete,
sorry-free β-fragment result.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-- Weak call-by-value big-step evaluation, **β fragment only** (λ-values + β).
The pure functional core on which we prove subject-reduction-as-defeq. -/
inductive SEvalβ (E : SEnv) : Expr → Expr → Prop
  /-- λ-abstractions are values. -/
  | lam (n : Name) (ty b : Expr) (bi : BinderInfo) :
      SEvalβ E (.lam n ty b bi) (.lam n ty b bi)
  /-- β: function evaluates to a λ, argument to a value, then the substituted body. -/
  | beta {f a : Expr} {n : Name} {ty b : Expr} {bi : BinderInfo} {av r : Expr} :
      SEvalβ E f (.lam n ty b bi) → SEvalβ E a av →
      SEvalβ E (b.instantiate1' av 0) r →
      SEvalβ E (.app f a) r

/-- **Subject reduction as definitional equality (β fragment).**

If `e` translates to `ve` and `e` β-evaluates to `v`, then `v` translates to some
`vve` definitionally equal to `ve`.

Requires `env.WF` and `VLCtx.WF` of the translation context (to invoke type
uniqueness / well-formedness of the translated subterms). -/
theorem SEvalβ_defeq {env : VEnv} (henv : env.WF) {Us : List Name} {Δ : VLCtx}
    (hΔ : VLCtx.WF env Us.length Δ) {Esrc : SEnv} {e v : Expr} {ve : VExpr}
    (htr : TrExprS env Us Δ e ve)
    (hev : SEvalβ Esrc e v) :
    ∃ vve, TrExprS env Us Δ v vve ∧ env.IsDefEqU Us.length Δ.toCtx ve vve := by
  induction hev generalizing ve with
  | lam n ty b bi =>
      exact ⟨ve, htr, VEnv.IsDefEqU.refl (htr.wf henv.ordered hΔ)⟩
  | @beta f a n ty b bi av r hf ha hbody ihf iha ihbody =>
      -- Invert the redex translation: ve = .app f' a', with the typing premises.
      cases htr with
      | @app f' A B a' _Δ _f _a hTf hTa htrf htra =>
        -- IH on the function: f' is defeq to a translated λ.
        obtain ⟨fv, htrfv, hfd⟩ := ihf htrf
        cases htrfv with
        | @lam ty' _Δ _ty _body body' _name _bi hty' htrty htrb =>
          -- IH on the argument: a' is defeq to the translated value av_v.
          obtain ⟨av_v, htrav, had⟩ := iha htra
          -- The translation context for the body and its OnCtx form.
          have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
          -- Body type B'' from well-formedness of htrb (under the extended context).
          have hΔ' : VLCtx.WF env Us.length ((none, .vlam ty') :: Δ) := ⟨hΔ, nofun, hty'⟩
          obtain ⟨B'', hbodyT⟩ := htrb.wf henv.ordered hΔ'
          -- (lambda-domain bookkeeping below)
          -- The lambda has its own forallE type `.forallE ty' B''`.
          obtain ⟨u, hty'sort⟩ := hty'
          have lamT1 : env.HasType Us.length Δ.toCtx (.lam ty' body') (.forallE ty' B'') :=
            VEnv.HasType.lam hty'sort hbodyT
          -- … and also type `.forallE A B`, transported from f' via hfd.
          have lamT2 : env.HasType Us.length Δ.toCtx (.lam ty' body') (.forallE A B) :=
            hTf.defeqU_l henv hΓ hfd
          -- Type uniqueness ⟹ the two forallE types are defeq ⟹ A ≡ ty'.
          have huForall : env.IsDefEqU Us.length Δ.toCtx (.forallE A B) (.forallE ty' B'') :=
            VEnv.IsDefEq.uniqU henv hΓ lamT2 lamT1
          obtain ⟨⟨w, hAty'⟩, _⟩ := VEnv.IsDefEqU.forallE_inv henv hΓ huForall
          -- av_v has type A; coerce it to ty'.
          have hadT : env.IsDefEq Us.length Δ.toCtx a' av_v A :=
            VEnv.IsDefEqU.of_l henv hΓ had hTa
          have havT : env.HasType Us.length Δ.toCtx av_v ty' :=
            (hadT.hasType.2).defeqU_r henv hΓ ⟨_, hAty'⟩
          -- The body substituted translates, via TrExprS.inst.
          have htrbody : TrExprS env Us Δ (b.instantiate1' av) (body'.inst av_v) :=
            TrExprS.inst henv.ordered havT htrb htrav
          -- IH on the body evaluation gives the result translation + defeq.
          obtain ⟨vve, htrr, hrd⟩ := ihbody htrbody
          refine ⟨vve, htrr, ?_⟩
          -- Assemble: .app f' a' ≡ .app (.lam ty' body') av_v ≡ body'.inst av_v ≡ vve.
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

/-! ### Inversion of `Erases` on `.lam`/`.app` sources.

`Erases`'s `ctor`/`cases` rules index the source by an application *spine*
(`args.foldl Expr.app …`). To invert `Erases` on a literal `.lam`/`.app` we must
refute (resp. classify) those spine cases. We induct on the derivation (so the
spine equation is available) and use the shape lemma below. -/

/-- An application spine `args.foldl Expr.app head` is either `head` itself
(empty spine) or syntactically an `.app`. -/
theorem foldl_app_eq_or_isApp (head : Expr) :
    ∀ (args : List Expr),
      args.foldl Expr.app head = head ∨ (args.foldl Expr.app head).isApp = true
  | [] => .inl rfl
  | x :: xs => by
      simp only [List.foldl]
      rcases foldl_app_eq_or_isApp (head.app x) xs with h | h
      · exact .inr (by rw [h]; rfl)
      · exact .inr h

/-- A `.const`-headed spine is never a `.lam`. -/
theorem foldl_app_const_ne_lam {cn : Name} {us : List Level} {args : List Expr}
    {n : Name} {ty b : Expr} {bi : BinderInfo} :
    args.foldl Expr.app (.const cn us) ≠ .lam n ty b bi := by
  intro heq
  rcases foldl_app_eq_or_isApp (.const cn us) args with h | h
  · rw [heq] at h; simp at h
  · rw [heq] at h; simp [Expr.isApp] at h

/-- A spine `(discr :: minors).foldl Expr.app pre` is never a `.lam`
(it is a non-empty application spine). -/
theorem foldl_app_cons_ne_lam {pre : Expr} {discr : Expr} {minors : List Expr}
    {n : Name} {ty b : Expr} {bi : BinderInfo} :
    (discr :: minors).foldl Expr.app pre ≠ .lam n ty b bi := by
  intro heq
  simp only [List.foldl] at heq
  rcases foldl_app_eq_or_isApp (pre.app discr) minors with h | h
  · rw [heq] at h; simp at h
  · rw [heq] at h; simp [Expr.isApp] at h

/-- **Inversion of `Erases` on a `.lam` source.** Only the `box` and `lam` rules
apply. -/
theorem Erases.lam_inv {env : VEnv} {Us : List Name} {Γ : ErasureCtx} {Δ : VLCtx}
    {n : Name} {ty b : Expr} {bi : BinderInfo} {t : LBTerm}
    (h : Erases env Us Γ Δ (.lam n ty b bi) t) :
    (∃ ve, TrExprS env Us Δ (.lam n ty b bi) ve ∧
        Erasable env Us.length Δ.toCtx ve ∧ t = .box) ∨
    (∃ ty' b', TrExprS env Us Δ ty ty' ∧
        Erases env Us Γ ((none, .vlam ty') :: Δ) b b' ∧
        t = .lambda (nameToBinder n) b') := by
  generalize he : (Expr.lam n ty b bi) = e₀ at h
  induction h with
  | box htr' her' => subst he; exact .inl ⟨_, htr', her', rfl⟩
  | lam hty hb => cases he; exact .inr ⟨_, _, hty, hb, rfl⟩
  | ctor cn us _ _ _ _ _ => exact absurd he.symm foldl_app_const_ne_lam
  | cases _ _ _ _ _ _ _ _ _ => exact absurd he.symm foldl_app_cons_ne_lam
  | _ => exact absurd he (by simp)

/-- A `.const`-headed spine never reduces to a `.lam` under `SEvalβ`
(the head stays a `.const`; `SEvalβ` only produces a `.lam` from a `.lam`). This
rules out the `ctor` erasure of a β-redex in `erases_correct_beta`. -/
theorem SEvalβ_const_spine_elim {E : SEnv} {e r : Expr} (hev : SEvalβ E e r) :
    ∀ {cn : Name} {us : List Level} {args : List Expr},
      e ≠ args.foldl Expr.app (.const cn us) := by
  induction hev with
  | lam n ty b bi =>
      intro cn us args; exact (foldl_app_const_ne_lam (args := args)).symm
  | @beta f a n ty b bi av r hf ha hbody ihf iha ihbody =>
      intro cn us args h
      -- `.app f a = foldl .. const args` forces `args = init ++ [a]`, `f = foldl .. init`.
      rcases List.eq_nil_or_concat args with rfl | ⟨init, last, hcat⟩
      · exact absurd h (by simp)
      · rw [hcat] at h
        simp only [List.concat_eq_append, List.foldl_append, List.foldl] at h
        injection h with hf_eq ha_eq
        exact ihf hf_eq

/-- **Inversion of `Erases` on an `.app` source.** Either the application is
irrelevant (`box`), erased structurally (`app`), or it is (syntactically) a
`.const`-headed application spine — the latter covering the `ctor`/`cases` rules,
whose heads are `.const`s. In the pure-β setting the spine case is excluded by
`SEvalβ_const_spine_elim`. -/
theorem Erases.app_inv {env : VEnv} {Us : List Name} {Γ : ErasureCtx} {Δ : VLCtx}
    {f a : Expr} {t : LBTerm}
    (h : Erases env Us Γ Δ (.app f a) t) :
    (∃ ve, TrExprS env Us Δ (.app f a) ve ∧
        Erasable env Us.length Δ.toCtx ve ∧ t = .box) ∨
    (∃ f' a', Erases env Us Γ Δ f f' ∧ Erases env Us Γ Δ a a' ∧ t = .app f' a') ∨
    (∃ (cn : Name) (us : List Level) (args : List Expr),
        Expr.app f a = args.foldl Expr.app (.const cn us)) := by
  generalize he : (Expr.app f a) = e₀ at h
  induction h with
  | box htr' her' => subst he; exact .inl ⟨_, htr', her', rfl⟩
  | app hf ha => cases he; exact .inr (.inl ⟨_, _, hf, ha, rfl⟩)
  | @ctor _ cn us _ _ args _ _ _ _ => exact .inr (.inr ⟨cn, us, args, rfl⟩)
  | @cases _ con us _ numParams pre discr _ minors _ _ _ _ _ _ =>
      exact .inr (.inr ⟨con, us, pre ++ discr :: minors, (List.foldl_append ..).symm⟩)
  | _ => exact absurd he (by simp)

end LeanToLambdaBox
