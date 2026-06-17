import LeanToLambdaBox.Erases
import LeanToLambdaBox.Eval
import LeanToLambdaBox.SubjectReduction
import LeanToLambdaBox.SubjectReductionFull

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
        ⟨veb, htrb, herbox, rfl⟩ | ⟨f't, a't, hf', ha', rfl⟩ | ⟨cn, us, args, hspine, _⟩
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

/-! ## Generalized forward simulation: β + ζ + δ fragment

The β-only `erases_correct_beta` is generalized to `SEvalβζδ` below. The δ case
needs, beyond the `SEnvConsistent` source-env ↔ `VEnv` link (for subject
reduction), a *target-side* consistency `ErasesEnvDelta` linking a source unfolding
`Esrc n = some body` to the target global env `E` (so the target `Eval.delta` can
fire). ι (`casesOn`) is scoped out (see `SEvalβζδ`). -/

/-- A `VLCtx.InstLet` witness yields the de Bruijn weakening of the substitutee's
context `Δ₀` into the instantiated context `Δ`. Used by the `bvar = dk` case of
`erases_subst_let` (mirrors `instN_toBVLift`). -/
theorem instLet_toBVLift {Δ₀ Δ₁ Δ : VLCtx} {e₀' A₀ : VExpr} {dk k : Nat}
    (W : VLCtx.InstLet Δ₀ e₀' A₀ dk k Δ₁ Δ) : VLCtx.BVLift Δ₀ Δ dk 0 k 0 := by
  induction W with
  | zero => exact .refl
  | @succ _ k _ _ d _ ih => cases d <;> exact ih.skip _

/-- **Erasure commutes with let-substitution.** The `vlet`-binder analogue of
`erases_subst`: if the substitutee `e₀` (translating to `e₀'`) erases to `s'`, and
`e` (under a `vlet e₀' A₀`-extended context) erases to `t`, then the substituted
`e.instantiate1' e₀` erases to `subst s' t`.

Mirrors lean4lean's `TrExprS.instN_let` (whose `InstLet` keeps both the result
`VExpr` and the typing context unchanged); accordingly the `box` case reuses the
*same* `Erasable` witness (no context change). The de Bruijn bookkeeping in the
`bvar` case is identical to `erases_subst`. -/
theorem erases_subst_let {env : VEnv} (henv : env.Ordered) {Us : List Name}
    {Γ : ErasureCtx} {Δ₀ : VLCtx} {e₀ : Expr} {e₀' A₀ : VExpr} {s' : LBTerm}
    (ht₀ : TrExprS env Us Δ₀ e₀ e₀')
    (h₀ : Erases env Us Γ Δ₀ e₀ s')
    {Δ₁ Δ : VLCtx} {dk k : Nat} (W : VLCtx.InstLet Δ₀ e₀' A₀ dk k Δ₁ Δ)
    {e : Expr} {t : LBTerm} (h : Erases env Us Γ Δ₁ e t) :
    Erases env Us Γ Δ (e.instantiate1' e₀ dk) (LBTerm.subst s' dk t) := by
  induction h generalizing Δ dk k with
  | box htr her =>
      refine .box (TrExprS.instN_let henv ht₀ W htr) ?_
      rwa [W.toCtx] at her
  | bvar i =>
      simp only [Expr.instantiate1', LBTerm.subst]
      split <;> rename_i h
      · exact .bvar i
      · split <;> rename_i h2
        · exact erases_shift henv (instLet_toBVLift W) h₀
        · exact .bvar (i - 1)
  | fvar x => exact .fvar x
  | const n us kn h => exact .const n us kn h
  | app _ _ ihf iha => exact .app (ihf W) (iha W)
  | lam hty _ ihb =>
      exact .lam (TrExprS.instN_let henv ht₀ W hty) (ihb (W.succ (d := .vlam _)))
  | letE hty hval _ _ ihv ihb =>
      exact .letE (TrExprS.instN_let henv ht₀ W hty)
        (TrExprS.instN_let henv ht₀ W hval) (ihv W) (ihb (W.succ (d := .vlet ..)))
  | ctor cn us iid cidx hc hlen _ ihargs =>
      simp only [instantiate1'_foldl_app, Expr.instantiate1', LBTerm.subst,
                 LBTerm.substArgs_eq_map]
      refine .ctor cn us iid cidx hc (by simp [hlen]) (fun i hi => ?_)
      rw [List.getElem_map, List.getElem_map]
      exact ihargs i (by simpa using hi) W
  | @cases _ con us iid numParams pre discr discr' minors alts' hc _ hlen _ ihd ihalts =>
      simp only [instantiate1'_foldl_app, List.map_cons,
                 Expr.instantiate1', LBTerm.subst, LBTerm.substAlts_eq_map]
      refine .cases con us iid numParams (pre.map (·.instantiate1' e₀ dk)) hc (ihd W)
        (minors := minors.map (·.instantiate1' e₀ dk))
        (alts' := alts'.map (fun a => (a.1, LBTerm.subst s' (dk + a.1.length) a.2)))
        (by simpa using hlen) (fun j hj => ?_)
      rw [List.getElem_map, List.getElem_map, ← subst_mkLambdas]
      exact ihalts j (by simpa using hj) W

/-- **Target-side δ consistency.** When the source constant `n` unfolds to `body`
(`Esrc n = some body`) and `n` is bound to the kername `Γ.constants n`, the target
global env `E` has a matching definition whose body erases `body`. This is the
target analogue of `SEnvConsistent`; together they make a constant δ-step on the
source simulate a `Eval.delta` step on the target.

The translation context is `[]`/`Δ` quantified: a constant unfolds to a *closed*
body, erased in the same context. -/
def ErasesEnvDelta (env : VEnv) (Us : List Name) (Γ : ErasureCtx)
    (Esrc : SEnv) (E : GlobalDeclarations) : Prop :=
  ∀ {Δ : VLCtx} {n : Name} {body : Expr},
    Esrc n = some body →
    Γ.ctors n = none ∧ Γ.casesOns n = none ∧
    ∃ body', LBTerm.envLookup E (Γ.constants n) = some (.constantDecl ⟨some body'⟩) ∧
      Erases env Us Γ Δ body body'

/-- **A `β`/`δ`-evaluating const-spine is headed by a non-ctor/non-`casesOn`.**

If `args.foldl Expr.app (.const cn us)` evaluates under `SEvalβδ`, then `cn` is
neither a registered constructor nor a registered `casesOn` (`Γ.ctors cn = none ∧
Γ.casesOns cn = none`). Reason: `SEvalβδ` only reduces such a spine by δ-unfolding
its head (a value head that is not a `λ` cannot β-reduce, and there is no `ι`/ctor
rule), and `hdelta` records that any constant with an unfolding is not a registered
constructor/`casesOn`. This is the β+δ analogue of `SEvalβ_const_spine_elim`, and
it discharges the `ctor`/`cases` spine disjunct of `Erases.app_inv` in the `beta`
case of `erases_correct`. -/
theorem SEvalβδ_const_spine_elim {env : VEnv} {Us : List Name} {Γ : ErasureCtx}
    {Esrc : SEnv} {E : GlobalDeclarations}
    (hdelta : ErasesEnvDelta env Us Γ Esrc E) {e r : Expr} (hev : SEvalβδ Esrc e r) :
    ∀ {cn : Name} {us : List Level} {args : List Expr},
      e = args.foldl Expr.app (.const cn us) →
      Γ.ctors cn = none ∧ Γ.casesOns cn = none := by
  induction hev with
  | lam n ty b bi =>
      intro cn us args heq
      exact absurd heq.symm foldl_app_const_ne_lam
  | @beta f a n ty b bi av r hf ha hbody ihf _ _ =>
      intro cn us args heq
      -- `.app f a = const-spine` forces `args = init ++ [a]`, `f = init-spine`.
      rcases List.eq_nil_or_concat args with rfl | ⟨init, last, rfl⟩
      · exact absurd heq (by simp)
      · rw [List.concat_eq_append, List.foldl_append, List.foldl_cons,
          List.foldl_nil] at heq
        injection heq with hf_eq _
        exact ihf hf_eq
  | @delta n us body r hunf _ _ =>
      intro cn us' args heq
      -- `.const n us = const-spine` forces `args = []`, `n = cn`.
      rcases List.eq_nil_or_concat args with rfl | ⟨init, last, rfl⟩
      · simp only [List.foldl] at heq
        cases heq
        obtain ⟨hnoc, hnocases, _⟩ := hdelta (Δ := []) hunf
        exact ⟨hnoc, hnocases⟩
      · rw [List.concat_eq_append, List.foldl_append, List.foldl_cons,
          List.foldl_nil] at heq
        exact absurd heq (by simp)

/-- **Erasure correctness — forward simulation, β + δ fragment.**

If the source term `e` translates to `ve` (`TrExprS`), erases to `t` (`Erases`),
and evaluates to the value `v` under `SEvalβδ` (β + δ + constructor values), then
`t` target-evaluates to some `t'` erasing `v`, with `v` translating to some `vve`.
Generalizes `erases_correct_beta` (which is the β-only fragment).

Threads two consistency hypotheses: `SEnvConsistent` (the source-env ↔ `VEnv`
δ-defeq link, used by subject reduction `SEvalβζδ_defeq` for the `box` cases) and
`ErasesEnvDelta` (the source-env ↔ target-env δ link, for the structural δ case;
it also records that a constant with an unfolding is not a registered constructor).

ζ (let) and ι (`casesOn`) are scoped out — see `SEvalβδ`. The β+ζ+δ *subject
reduction* `SEvalβζδ_defeq` is proved separately and fully. -/
theorem erases_correct {env : VEnv} (henv : env.WF) {Us : List Name} {Δ : VLCtx}
    (hΔ : VLCtx.WF env Us.length Δ) {Γ : ErasureCtx} {Esrc : SEnv}
    {E : GlobalDeclarations}
    (hcon : SEnvConsistent env Us Esrc)
    (hdelta : ErasesEnvDelta env Us Γ Esrc E)
    {e v : Expr} {ve : VExpr} {t : LBTerm}
    (htr : TrExprS env Us Δ e ve)
    (her : Erases env Us Γ Δ e t)
    (hev : SEvalβδ Esrc e v) :
    ∃ t' vve, Eval E t t' ∧ TrExprS env Us Δ v vve ∧ Erases env Us Γ Δ v t' := by
  induction hev generalizing ve t with
  | lam n ty b bi =>
      have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
      rcases Erases.lam_inv her with ⟨veb, htrb, herbox, rfl⟩ | ⟨_, _, hty, hb, rfl⟩
      · exact ⟨.box, ve, .box, htr, .box htr
          (herbox.defeq henv hΓ
            (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrb htr))⟩
      · exact ⟨_, ve, .lam _ _, htr, .lam hty hb⟩
  | @beta f a n ty b bi av r hf ha hbody ihf iha ihbody =>
      have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
      rcases Erases.app_inv her with
        ⟨veb, htrb, herbox, rfl⟩ | ⟨f't, a't, hf', ha', rfl⟩ | ⟨cn, us, args, hspine, hmem⟩
      · -- Whole redex irrelevant: subject reduction carries it to the value.
        obtain ⟨vve, htrr, hdef⟩ :=
          SEvalβζδ_defeq henv hΔ hcon htr (.beta hf.toβζδ ha.toβζδ hbody.toβζδ)
        have herve : Erasable env Us.length Δ.toCtx ve := herbox.defeq henv hΓ
          (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrb htr)
        exact ⟨.box, vve, .box, htrr, .box htrr (herve.defeq henv hΓ hdef)⟩
      · -- Structural application.
        cases htr with
        | @app f' A B a'' _Δ _f _a hTf hTa htrf htra =>
          obtain ⟨ftv, fvv, hEf, htrlam, herlam⟩ := ihf htrf hf'
          rcases Erases.lam_inv herlam with ⟨velam, htrvelam, herlamE, rfl⟩
            | ⟨tyE, b', htrtyE, hb', rfl⟩
          · -- Head erased to `box` (MetaCoq's `eval_box`).
            obtain ⟨vve, htrr, hdef⟩ :=
              SEvalβζδ_defeq henv hΔ hcon (.app hTf hTa htrf htra)
                (.beta hf.toβζδ ha.toβζδ hbody.toβζδ)
            obtain ⟨fvv0, htrlam0, hfdef⟩ := SEvalβζδ_defeq henv hΔ hcon htrf hf.toβζδ
            have hferase : Erasable env Us.length Δ.toCtx f' :=
              (herlamE.defeq henv hΓ
                (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrvelam htrlam0)).defeq
                henv hΓ (VEnv.IsDefEqU.symm hfdef)
            have herapp : Erasable env Us.length Δ.toCtx (.app f' a'') :=
              hferase.app henv hΓ hTf hTa
            exact ⟨.box, vve, .app_box hEf, htrr,
              .box htrr (herapp.defeq henv hΓ hdef)⟩
          · -- Head erased to a λ.
            obtain ⟨fvv0, htrlam0, hfdef⟩ := SEvalβζδ_defeq henv hΔ hcon htrf hf.toβζδ
            cases htrlam0 with
            | @lam ty' _Δ _ty _body body' _name _bi hty' htrty htrb =>
              obtain ⟨atv, avv, hEa, htrav, herav⟩ := iha htra ha'
              obtain ⟨B'', hbodyT⟩ :=
                TrExprS.wf (Us := Us) (Δ := (none, .vlam ty') :: Δ) henv.ordered
                  ⟨hΔ, nofun, hty'⟩ htrb
              have hAty' : env.IsDefEqU Us.length Δ.toCtx A ty' := by
                obtain ⟨u, hty'sort⟩ := hty'
                have lamT1 : env.HasType Us.length Δ.toCtx (.lam ty' body')
                    (.forallE ty' B'') := VEnv.HasType.lam hty'sort hbodyT
                have lamT2 : env.HasType Us.length Δ.toCtx (.lam ty' body')
                    (.forallE A B) := hTf.defeqU_l henv hΓ hfdef
                obtain ⟨⟨_, h⟩, _⟩ := VEnv.IsDefEqU.forallE_inv henv hΓ
                  (VEnv.IsDefEq.uniqU henv hΓ lamT2 lamT1)
                exact ⟨_, h⟩
              have havIsA : env.IsDefEqU Us.length Δ.toCtx avv a'' := by
                obtain ⟨avv0, htrav0, had0⟩ := SEvalβζδ_defeq henv hΔ hcon htra ha.toβζδ
                exact VEnv.IsDefEqU.trans henv hΓ
                  (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrav htrav0)
                  (VEnv.IsDefEqU.symm had0)
              have havA : env.HasType Us.length Δ.toCtx avv A :=
                hTa.defeqU_l henv hΓ (VEnv.IsDefEqU.symm havIsA)
              have havT : env.HasType Us.length Δ.toCtx avv ty' :=
                havA.defeqU_r henv hΓ hAty'
              have havTE : env.HasType Us.length Δ.toCtx avv tyE := by
                have : env.IsDefEqU Us.length Δ.toCtx tyE ty' :=
                  TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrtyE htrty
                exact havT.defeqU_r henv hΓ (VEnv.IsDefEqU.symm this)
              obtain ⟨t', vve, hEr, htrr, herr⟩ := ihbody
                (TrExprS.inst henv.ordered havT htrb htrav)
                (erases_beta_struct henv.ordered htrav havTE hb' herav)
              exact ⟨t', vve, .beta hEf hEa hEr, htrr, herr⟩
      · -- Const-headed spine erasure (`ctor`/`cases`): the head `cn` is a
        -- registered constructor/`casesOn` (`hmem`).  But a `β`/`δ`-evaluating
        -- const-spine is headed by a *non*-ctor/non-casesOn (`SEvalβδ` keeps the
        -- head a const that must δ-unfold, and registered ctors/casesOns have no
        -- unfolding by `hdelta`) — contradiction.
        obtain ⟨hnoc, hnocases⟩ :=
          SEvalβδ_const_spine_elim hdelta (.beta hf ha hbody) hspine
        rcases hmem with h | h
        · exact absurd hnoc h
        · exact absurd hnocases h
  | @delta n us body r hunf hbodyev ihbody =>
      have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
      obtain ⟨bve, htrbody, hbdef⟩ := hcon hunf htr
      obtain ⟨hnoctor, _, body', hlook, herbody⟩ := hdelta hunf
      rcases Erases.const_inv her with ⟨veb, htrb, herbox, rfl⟩
        | ⟨kn, hkn, rfl⟩ | ⟨iid, cidx, hctor, rfl⟩
      · obtain ⟨vve, htrr, hrdef⟩ :=
          SEvalβζδ_defeq henv hΔ hcon htr (.delta hunf hbodyev.toβζδ)
        have herve : Erasable env Us.length Δ.toCtx ve := herbox.defeq henv hΓ
          (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrb htr)
        exact ⟨.box, vve, .box, htrr, .box htrr (herve.defeq henv hΓ hrdef)⟩
      · obtain ⟨t', vve, hEbody, htrr, herr⟩ := ihbody htrbody herbody
        subst hkn
        exact ⟨t', vve, .delta hlook hEbody, htrr, herr⟩
      · rw [hnoctor] at hctor; exact absurd hctor (by simp)

end LeanToLambdaBox
