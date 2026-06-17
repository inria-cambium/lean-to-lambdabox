import LeanToLambdaBox.Erases
import LeanToLambdaBox.Eval
import LeanToLambdaBox.SubjectReduction

/-!
# Towards erasure correctness (step A3.2)

The target operational semantics is `Eval` (big-step weak CBV, with `app_box`).
The full statement we are heading for is MetaCoq's `erases_correct`: for a
well-typed source term that evaluates to a value, its erasure evaluates to a
value that erases the source value.

This file collects the reusable, fully-proved computational cores of that
theorem. The β case is a direct instance of `erases_subst`; it is the heart of
why erasure preserves β-reduction.

Still required for the full `erases_correct` (next): a source-side evaluation
relation, and the `box`-soundness lemma (an irrelevant subterm never blocks a
relevant redex), which needs lean4lean subject reduction — the genuinely deep
obligation, and where the `box` rule's typing premise earns its keep.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-- **β-correctness (substitution form).** Erasure commutes with the body
substitution of a β-redex: if the argument `a` (of the binder type, witnessed by
`hTa`) erases to `a'` and the body `b` erases to `b'` under the binder, then the
source reduct `b[a]` erases to the target reduct `subst1 a' b'`.

A direct instance of `erases_subst` at depth 0 (`VLCtx.InstN.zero`). This is the
core computational content of the β case of erasure correctness: combined with
`Eval.beta`, the target redex `(λ. b') a'` evaluates through `subst1 a' b'`, which
this lemma shows still erases the source reduct. -/
theorem erases_beta_struct {env : VEnv} (henv : env.Ordered) {Us : List Name}
    {Γ : ErasureCtx} {Δ : VLCtx}
    {b a : Expr} {b' a' : LBTerm} {ty' va : VExpr}
    (hta : TrExprS env Us Δ a va) (hTa : env.HasType Us.length Δ.toCtx va ty')
    (hb : Erases env Us Γ ((none, .vlam ty') :: Δ) b b')
    (ha : Erases env Us Γ Δ a a') :
    Erases env Us Γ Δ (b.instantiate1' a 0) (LBTerm.subst1 a' b') :=
  erases_subst henv hta hTa ha .zero hb

/-- **β-reduction preservation** (the operational core of erasure correctness for
the β case). If a β-redex `(fun x : ty => b) a` erases structurally to
`(λ. b') a'` — with `a` of the binder type — then the target redex takes one
`Step` to `subst1 a' b'`, and that target reduct still erases the source reduct
`b[a]`.

This is the forward-simulation square for β closed end-to-end, composing the
target β-`Step` with `erases_beta_struct`. It is the typed-`Erases`/real-`Expr`
analogue of the β case of the legacy `erase_preservation`. -/
theorem erases_beta_step {env : VEnv} (henv : env.Ordered) {Us : List Name}
    {Γ : ErasureCtx} {Δ : VLCtx} {E : GlobalDeclarations}
    {b a : Expr} {n' : BinderName} {b' a' : LBTerm} {ty' va : VExpr}
    (hta : TrExprS env Us Δ a va) (hTa : env.HasType Us.length Δ.toCtx va ty')
    (hb : Erases env Us Γ ((none, .vlam ty') :: Δ) b b')
    (ha : Erases env Us Γ Δ a a') :
    LBTerm.Step E (.app (.lambda n' b') a') (LBTerm.subst1 a' b')
    ∧ Erases env Us Γ Δ (b.instantiate1' a 0) (LBTerm.subst1 a' b') :=
  ⟨.beta n' b' a', erases_beta_struct henv hta hTa hb ha⟩

/-- **Erasure correctness — forward simulation, β fragment.**

If the source term `e` translates to `ve` (`TrExprS`), erases to the target term
`t` (`Erases`), and β-evaluates to the value `v` (`SEvalβ`), then `t` evaluates
(target `Eval`) to some `t'` which erases the value `v`, and `v` itself
translates to some `vve`. This is MetaCoq's `erases_correct` restricted to the
pure β fragment.

The proof is by induction on the source evaluation `hev` (`SEvalβ`), inverting
the erasure `her` with `Erases.lam_inv`/`Erases.app_inv` (whose spine cases are
discharged by `SEvalβ_const_spine_elim`):
* `lam` (a λ-value): both source and target are already values; the `box`
  erasure subcase carries the irrelevance witness through unchanged.
* `beta` (a β-redex):
  - `box` erasure: by `SEvalβ_defeq` (subject reduction as defeq) the value's
    translation is defeq to `ve`, so `Erasable.defeq` carries irrelevance to the
    value; the target `box` steps to `box`.
  - `app` erasure: the IH on the function yields its target value.
    * If that value is a `λ` (head erased to a lambda), the IH on the argument and
      `erases_beta_struct`/`Eval.beta` close the β square.
    * If the head erased to `box` (MetaCoq's `eval_box`), box propagation
      (`Erasable.app`) makes the whole application — and hence its value —
      irrelevant; the target steps `(box a') → box` via `Eval.app_box`.

This is a complete, `sorry`-free forward-simulation result for the pure β
fragment. -/
theorem erases_correct_beta {env : VEnv} (henv : env.WF) {Us : List Name} {Δ : VLCtx}
    (hΔ : VLCtx.WF env Us.length Δ) {Γ : ErasureCtx} {Esrc : SEnv}
    {E : GlobalDeclarations} {e v : Expr} {ve : VExpr} {t : LBTerm}
    (htr : TrExprS env Us Δ e ve)
    (her : Erases env Us Γ Δ e t)
    (hev : SEvalβ Esrc e v) :
    ∃ t' vve, Eval E t t' ∧ TrExprS env Us Δ v vve ∧ Erases env Us Γ Δ v t' := by
  induction hev generalizing ve t with
  | lam n ty b bi =>
      -- e = v = .lam …; both languages already have it as a value.
      have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
      rcases Erases.lam_inv her with ⟨veb, htrb, herbox, rfl⟩ | ⟨_, _, hty, hb, rfl⟩
      · -- box: align the box's own translation with `ve` and reuse the witness.
        exact ⟨.box, ve, .box, htr, .box htr
          (herbox.defeq henv hΓ
            (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrb htr))⟩
      · exact ⟨_, ve, .lam _ _, htr, .lam hty hb⟩
  | @beta f a n ty b bi av r hf ha hbody ihf iha ihbody =>
      have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
      rcases Erases.app_inv her with
        ⟨veb, htrb, herbox, rfl⟩ | ⟨f't, a't, hf', ha', rfl⟩ | ⟨cn, us, args, hspine⟩
      · -- Whole redex irrelevant: subject reduction carries it to the value.
        obtain ⟨vve, htrr, hdef⟩ := SEvalβ_defeq henv hΔ htr (.beta hf ha hbody)
        have herve : Erasable env Us.length Δ.toCtx ve := herbox.defeq henv hΓ
          (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrb htr)
        exact ⟨.box, vve, .box, htrr, .box htrr (herve.defeq henv hΓ hdef)⟩
      · -- Structural application. Invert the redex translation.
        cases htr with
        | @app f' A B a'' _Δ _f _a hTf hTa htrf htra =>
          -- IH on the function: f't evaluates to a value erasing the λ value of f.
          obtain ⟨ftv, fvv, hEf, htrlam, herlam⟩ := ihf htrf hf'
          rcases Erases.lam_inv herlam with ⟨velam, htrvelam, herlamE, rfl⟩
            | ⟨tyE, b', htrtyE, hb', rfl⟩
          · -- Head erased to `box` (MetaCoq's `eval_box`): the function is
            -- irrelevant, so the application is too (box propagation,
            -- `Erasable.app`), and the value `r` inherits the irrelevance.
            obtain ⟨vve, htrr, hdef⟩ :=
              SEvalβ_defeq henv hΔ (.app hTf hTa htrf htra) (.beta hf ha hbody)
            -- `f'` is erasable: it is defeq to the λ-value's translation, which is.
            obtain ⟨fvv0, htrlam0, hfdef⟩ := SEvalβ_defeq henv hΔ htrf hf
            have hferase : Erasable env Us.length Δ.toCtx f' :=
              (herlamE.defeq henv hΓ
                (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrvelam htrlam0)).defeq
                henv hΓ (VEnv.IsDefEqU.symm hfdef)
            -- The whole redex `f' a''` is erasable, hence so is its value `vve`.
            have herapp : Erasable env Us.length Δ.toCtx (.app f' a'') :=
              hferase.app henv hΓ hTf hTa
            exact ⟨.box, vve, .app_box hEf, htrr,
              .box htrr (herapp.defeq henv hΓ hdef)⟩
          · -- Head erased to a λ. Subject reduction gives `f' ≡ λ`-translation;
            -- invert *that* translation to expose the λ body.
            obtain ⟨fvv0, htrlam0, hfdef⟩ := SEvalβ_defeq henv hΔ htrf hf
            cases htrlam0 with
            | @lam ty' _Δ _ty _body body' _name _bi hty' htrty htrb =>
              obtain ⟨atv, avv, hEa, htrav, herav⟩ := iha htra ha'
              obtain ⟨B'', hbodyT⟩ :=
                TrExprS.wf (Us := Us) (Δ := (none, .vlam ty') :: Δ) henv.ordered
                  ⟨hΔ, nofun, hty'⟩ htrb
              -- `A ≡ ty'` (app domain ≡ λ's translated domain), as in Lemma 1.
              have hAty' : env.IsDefEqU Us.length Δ.toCtx A ty' := by
                obtain ⟨u, hty'sort⟩ := hty'
                have lamT1 : env.HasType Us.length Δ.toCtx (.lam ty' body')
                    (.forallE ty' B'') := VEnv.HasType.lam hty'sort hbodyT
                have lamT2 : env.HasType Us.length Δ.toCtx (.lam ty' body')
                    (.forallE A B) := hTf.defeqU_l henv hΓ hfdef
                obtain ⟨⟨_, h⟩, _⟩ := VEnv.IsDefEqU.forallE_inv henv hΓ
                  (VEnv.IsDefEq.uniqU henv hΓ lamT2 lamT1)
                exact ⟨_, h⟩
              -- `avv : A`: subject reduction `a ≡ av` (so `a'' ≡ avv`), then `: A`.
              have havIsA : env.IsDefEqU Us.length Δ.toCtx avv a'' := by
                obtain ⟨avv0, htrav0, had0⟩ := SEvalβ_defeq henv hΔ htra ha
                exact VEnv.IsDefEqU.trans henv hΓ
                  (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrav htrav0)
                  (VEnv.IsDefEqU.symm had0)
              have havA : env.HasType Us.length Δ.toCtx avv A :=
                hTa.defeqU_l henv hΓ (VEnv.IsDefEqU.symm havIsA)
              -- `avv : ty'` (htrlam0's domain), used by `TrExprS.inst`.
              have havT : env.HasType Us.length Δ.toCtx avv ty' :=
                havA.defeqU_r henv hΓ hAty'
              -- `avv : tyE` (the erasure's domain), used by `erases_beta_struct`.
              have havTE : env.HasType Us.length Δ.toCtx avv tyE := by
                have : env.IsDefEqU Us.length Δ.toCtx tyE ty' :=
                  TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrtyE htrty
                exact havT.defeqU_r henv hΓ (VEnv.IsDefEqU.symm this)
              -- β square: the substituted body translates (TrExprS.inst) and erases
              -- the source reduct (erases_beta_struct); the IH on the body closes it.
              obtain ⟨t', vve, hEr, htrr, herr⟩ := ihbody
                (TrExprS.inst henv.ordered havT htrb htrav)
                (erases_beta_struct henv.ordered htrav havTE hb' herav)
              exact ⟨t', vve, .beta hEf hEa hEr, htrr, herr⟩
      · -- The redex erased via a `.const`-headed spine (`ctor`/`cases`): impossible
        -- under `SEvalβ`, since a const-headed spine has no β-evaluation.
        exact absurd hspine (SEvalβ_const_spine_elim (.beta hf ha hbody))

end LeanToLambdaBox
