import LeanToLambdaBox.SubjectReductionIota
import LeanToLambdaBox.Closed

/-!
# Erasure correctness for the ι (`casesOn`) fragment — the forward simulation

`erases_correct_dataι` is the ι counterpart of `erases_correct_data`: forward simulation
at MetaRocq's non-block `appliedFlags` over `SEvalDataι` (β + δ + saturated constructors +
the corrected ι), with the same conclusion shape. It is **additive** —
`erases_correct_data` / `erases_correct_data_zeta` are untouched.

It lives in its own file because it needs `SEvalDataι_defeq`, and `SubjectReductionIota`
already imports `ErasesCorrectData`.

## What the ι case needs beyond the β/δ/ctor cases

Four things that the non-ι fragment never met, each recorded on the declaration that
carries it:

* **`NoBlock`/`NoFix` must see `.case`** (done in `Erases.lean` / `ErasesCorrectData.lean`).
  Inverting the target `.case (iid, np) discr' alts'` is useless if the discriminant IH
  cannot be fed.
* **A closedness thread (`LBClosed t 0`).** The β-chain ↔ reversing-`iota_red` bridge is
  *false* for field values with loose de Bruijn variables: at two fields the β chain gives
  `subst f₁ 0 (subst f₀ 1 body)` while `substList (fields.reverse) body` gives
  `subst f₀ 0 (subst f₁ 0 body)`, and these agree only when `subst f₀ 0 f₁ = f₁`. This is
  MetaRocq's own `closedn 0` convention (its `eval`/`erases_correct` carry it everywhere),
  not a modelling shortcut. `ClosedEnv` is the environment-level counterpart, parallel to
  `NoFixEnv`.
* **Relevance side conditions** (`IotaRelevant`, `SubjectReductionIota.lean`): the model
  permits `Erases` derivations that box a *proper prefix* of an ι redex, or box the
  scrutinee's constructor value; both leave the target `.case` stuck, so both must be
  excluded. The shipping `visitCases` emits neither.
* **A source/target pin reconciliation.** `SEvalDataι.iota` pins its redex arithmetically
  (through `IotaArities`); `Erases.cases` pins it through `Γ`
  (`casesDiscrPos`/`ctorFields`). `IotaArityCoherent` links them, and
  `CtorFieldsCoherent` turns the constructor's full arity into `numParams + nfields` — the
  step that converts `(cargs.drop np).length` into the selected alternative's binder count.

## Scope: the flat fragment (`FlatCaseFields`)

The simulation is proved under `FlatCaseFields Γ` — every constructor of an inductive that
some registered `casesOn` eliminates has **zero** retained fields (`Bool`, `Ordering`,
enumerations). Under it `cargs.drop np = []`, `substList [] body = body`, and the whole
reversal bridge degenerates to `rfl`.

This is not an arbitrary restriction: it is exactly the region the rest of the ι stack
covers today. The shipping-side inversion `Supported.casesApp_inv` carries the same
zero-field condition, and the `IotaShape` certificate as landed can only be satisfied by
zero-field constructors (Lean's generated `casesOn` η-expands every minor that takes
fields — `Option.casesOn := fun {α} {motive} t none some => Option.rec none (fun val =>
some val) t` — so the reduct ends in a redex `betaN` cannot contract, since it is built by
the template's body rather than pending in the supplied argument list). Lifting the
restriction means lifting all three together: the general bridge (needing
`LBTerm.subst_subst`, already available in `Closed.lean`), a two-stage `IotaShape`, and
`Supported.casesApp`'s `hflat`.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-! ## The two new environment/`Γ` side conditions -/

/-- **Every stored constant body is de Bruijn closed** — the target-side counterpart of
"constant bodies are closed terms", and the environment-level analogue of `NoFixEnv`. It
is what keeps the `LBClosed` thread alive across a δ step. (`RegisteredClosure`'s
context-uniformity clause already relies on the same fact on the source side.) -/
def ClosedEnv (E : GlobalDeclarations) : Prop :=
  ∀ {kn : Kername} {body : LBTerm},
    LBTerm.envLookup E kn = some (.constantDecl ⟨some body⟩) → LBClosed body 0

/-- **Target-side ι precondition.** `WcbvEval.iota` fires only on a non-propositional
inductive (`isPropositionalInductive E iid = false`); a propositional one reduces by
`iota_sing` instead, which needs `with_prop_case`. `ErasesEnvCases`
(`EnvErasureNonrec.lean`) delivers the `.inductiveDecl`/`npars` half of the `casesOn` env
consistency but says nothing about `oib.propositional`, so the ι simulation asks for this
separately. -/
def ErasesEnvCasesι (Γ : ErasureCtx) (E : GlobalDeclarations) : Prop :=
  ∀ {con : Name} {iid : InductiveId} {numParams : Nat},
    Γ.casesOns con = some (iid, numParams) → isPropositionalInductive E iid = false

/-- **The flat fragment.** Every constructor of an inductive eliminated by some registered
`casesOn` has zero retained fields. See the module docstring for why this is the region
the whole ι stack currently covers, and what lifting it requires. -/
def FlatCaseFields (Γ : ErasureCtx) : Prop :=
  ∀ {con : Name} {iid : InductiveId} {np : Nat} {nfs : List Nat},
    Γ.casesOns con = some (iid, np) → Γ.ctorFields iid = some nfs →
    ∀ j (h : j < nfs.length), nfs[j] = 0

/-! ## A partial `casesOn` spine never evaluates to a λ

The ι analogue of `SEvalData_const_spine_lam_elim`, and the reason the `beta` case of the
simulation still closes once ι is in the source relation. The plain statement is **false**
with ι — `Bool.casesOn d (fun x => x) (fun x => x)` evaluates to a λ — so the arity bound
is load-bearing: a spine *shorter* than one full ι redex cannot fire `iota` (which is
pinned to exact arity), cannot fire `delta` (a registered `casesOn` has no unfolding), and
cannot fire `beta` without a still shorter spine doing so first.

The bound is exactly what the caller has: `Erases.app_inv_t`'s `cases` disjunct exhibits
the *whole* application as a saturated `casesOn` spine, so its function part is one
argument short. -/
theorem SEvalDataι_partial_cases_lam_elim {Γ : ErasureCtx} {ia : IotaArities} {E : SEnv}
    (hnf : ∀ {n : Name} {body : Expr}, E n = some body →
              Γ.ctors n = none ∧ Γ.casesOns n = none)
    (hiacoh : IotaArityCoherent Γ ia)
    {e r : Expr} (hev : SEvalDataι Γ ia E e r) :
    ∀ {con : Name} {us : List Level} {args : List Expr} {iid : InductiveId}
      {np dp : Nat} {nfs : List Nat},
      e = args.foldl Expr.app (.const con us) →
      Γ.casesOns con = some (iid, np) → Γ.casesDiscrPos con = some dp →
      Γ.ctorFields iid = some nfs → args.length < dp + 1 + nfs.length →
      ¬ ∃ (n : Name) (ty b : Expr) (bi : BinderInfo), r = .lam n ty b bi := by
  induction hev with
  | lam n ty b bi =>
      intro con us args iid np dp nfs heq _ _ _ _
      exact absurd heq.symm foldl_app_const_ne_lam
  | @beta f a n ty b bi av r hf ha hbody ihf _ _ =>
      intro con us args iid np dp nfs heq hcs hdp hnfs hlt
      rcases List.eq_nil_or_concat args with rfl | ⟨init, last, rfl⟩
      · exact absurd heq (by simp)
      · rw [List.concat_eq_append, List.foldl_append, List.foldl_cons,
          List.foldl_nil] at heq
        injection heq with hf_eq _
        refine absurd (ihf hf_eq hcs hdp hnfs ?_) (by exact fun h => h ⟨n, ty, b, bi, rfl⟩)
        have hll : (init.concat last).length = init.length + 1 := by simp
        omega
  | @delta n us body r hunf hbodyev _ =>
      intro con us' args iid np dp nfs heq hcs _ _ _
      rcases List.eq_nil_or_concat args with rfl | ⟨init, last, rfl⟩
      · simp only [List.foldl] at heq
        cases heq
        rw [(hnf hunf).2] at hcs; exact absurd hcs (by simp)
      · rw [List.concat_eq_append, List.foldl_append, List.foldl_cons,
          List.foldl_nil] at heq
        exact absurd heq (by simp)
  | @ctor_val cn us iid cidx ar args vs hc har hsat hl hargs _ =>
      intro con us' args' iid' np dp nfs _ _ _ _ _
      rintro ⟨n, ty, b, bi, hlam⟩
      exact foldl_app_const_ne_lam hlam
  | @iota con us cus pre minors cargs discr ctor iid np cidx nmot nidx nmin ar r
      hcases hctor hia har hpre hmin hcargs hdiscr hidx hbranch _ _ =>
      intro con' us' args iid' np' dp nfs heq hcs hdp hnfs hlt
      exfalso
      have heq' : (pre ++ discr :: minors).foldl Expr.app (.const con us)
          = args.foldl Expr.app (.const con' us') := by
        rw [List.foldl_append]; exact heq
      obtain ⟨hcon, _, hargs⟩ := foldl_app_const_inj heq'
      subst hcon; subst hargs
      obtain ⟨hdp2, nfs2, hnfs2, hnfs2len⟩ := hiacoh hcases hia
      have hiid : iid' = iid := by
        rw [hcases] at hcs; simp only [Option.some.injEq, Prod.mk.injEq] at hcs
        exact hcs.1.symm
      have hdpeq : dp = np + nmot + nidx := by
        rw [hdp2] at hdp; exact (Option.some.inj hdp).symm
      have hnfslen : nfs.length = nmin := by
        rw [hiid, hnfs2] at hnfs
        rw [← Option.some.inj hnfs]
        exact hnfs2len
      have hargslen : (pre ++ discr :: minors).length = pre.length + 1 + minors.length := by
        simp only [List.length_append, List.length_cons]; omega
      omega

/-! ## The ι forward simulation -/

/-- **Erasure correctness — forward simulation, β + δ + saturated constructors + ι, at
MetaRocq's non-block `appliedFlags`, on the flat fragment.**

The ι counterpart of `erases_correct_data`: same conclusion shape, over `SEvalDataι`
(which has no `zeta` rule), plus the `LBClosed` thread and the ι-specific side conditions
documented in the module header. Additive — `erases_correct_data`'s signature is untouched.

The ported β/δ/ctor cases differ from `erases_correct_data`'s only in that `SEvalDataι`
has no forgetful map to `SEvalβζδ` (ι is not in that fragment), so every
`SEvalβζδ_defeq henv hΔ hcon …` becomes `SEvalDataι_defeq henv hΔ hcon hiota …` — same
rôle, same output triple, one extra argument — and in the `LBClosed` bookkeeping.

Note the *reverse* disjointness (`Γ.casesOns con = some _ → Γ.ctors con = none`) is not a
new premise: it follows from `hcc`. -/
theorem erases_correct_dataι {env : VEnv} (henv : env.WF) {Us : List Name} {Δ : VLCtx}
    (hΔ : VLCtx.WF env Us.length Δ) {Γ : ErasureCtx} {ia : IotaArities}
    {Esrc : SEnv} {E : GlobalDeclarations}
    (hcon : SEnvConsistent env Us Esrc)
    (hiota : IotaConsistent env Us Γ ia)
    (hdelta : ErasesEnvDeltaData env Us Γ Esrc E)
    (hctorenv : ErasesEnvCtor Γ E)
    (hcasesenv : ErasesEnvCasesι Γ E)
    (hcoh : CtorFieldsCoherent Γ)
    (hiacoh : IotaArityCoherent Γ ia)
    (hflat : FlatCaseFields Γ)
    (hrel : IotaRelevant env Us Γ)
    (hcc : ∀ {cn : Name} {iid : InductiveId} {cidx : Nat},
             Γ.ctors cn = some (iid, cidx) → Γ.casesOns cn = none)
    (hnfenv : NoFixEnv E)
    (hclenv : ClosedEnv E)
    {e v : Expr} (hev : SEvalDataι Γ ia Esrc e v) :
    ∀ {ve : VExpr} {t : LBTerm},
      TrExprS env Us Δ e ve → Erases env Us Γ Δ e t →
      NoBlock t → NoFix t → LBClosed t 0 →
      ∃ t' vve, WcbvEval E appliedFlags t t' ∧ TrExprS env Us Δ v vve ∧
        Erases env Us Γ Δ v t' ∧ NoBlock t' ∧ NoFix t' ∧ LBClosed t' 0 := by
  have hnf : ∀ {n : Name} {body : Expr}, Esrc n = some body →
      Γ.ctors n = none ∧ Γ.casesOns n = none :=
    fun h => ⟨(hdelta (Δ := Δ) h).1, (hdelta (Δ := Δ) h).2.1⟩
  induction hev with
  | lam n ty b bi =>
      intro ve t htr her hnb hnfx hcl
      have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
      rcases Erases.lam_inv her with ⟨veb, htrb, herbox, rfl⟩ | ⟨_, _, hty, hb, rfl⟩
        | ⟨defs, idx, rfl, _⟩
      · exact ⟨.box, ve, .box, htr, .box htr
          (herbox.defeq henv hΓ
            (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrb htr)),
          trivial, trivial, trivial⟩
      · exact ⟨_, ve, .lam _ _, htr, .lam hty hb, hnb, hnfx, hcl⟩
      · exact hnfx.elim
  | @beta f a n ty b bi av r hf ha hbody ihf iha ihbody =>
      intro ve t htr her hnb hnfx hcl
      have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
      rcases her.app_inv_t with
        ⟨veb, htrb, herbox, rfl⟩ |
        ⟨f't, a't, hf', ha', rfl⟩ |
        ⟨cn2, us2, args2, iid2, cidx2, args'', hsrc, hc2, hlen2, rfl⟩ |
        ⟨con2, us2, pre2, discr2, minors2, iid2, np2, discr', alts', nfs2, hsrc,
          hcase2, hpre2, hnfs2, hd2, hlen2, hnlen2, harity2, halts2, rfl⟩
      · obtain ⟨vve, htrr, hdef⟩ :=
          SEvalDataι_defeq henv hΔ hcon hiota htr (.beta hf ha hbody)
        have herve : Erasable env Us.length Δ.toCtx ve := herbox.defeq henv hΓ
          (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrb htr)
        exact ⟨.box, vve, .box, htrr, .box htrr (herve.defeq henv hΓ hdef),
          trivial, trivial, trivial⟩
      · cases htr with
        | @app f' A B a'' _Δ _f _a hTf hTa htrf htra =>
          obtain ⟨ftv, fvv, hEf, htrlam, herlam, hnbftv, hnfftv, hclftv⟩ :=
            ihf htrf hf' hnb.1 hnfx.1 hcl.1
          rcases Erases.lam_inv herlam with ⟨velam, htrvelam, herlamE, rfl⟩
            | ⟨tyE, b', htrtyE, hb', rfl⟩ | ⟨defs, idx, rfl, _⟩
          · obtain ⟨vve, htrr, hdef⟩ :=
              SEvalDataι_defeq henv hΔ hcon hiota (.app hTf hTa htrf htra)
                (.beta hf ha hbody)
            obtain ⟨fvv0, htrlam0, hfdef⟩ :=
              SEvalDataι_defeq henv hΔ hcon hiota htrf hf
            have hferase : Erasable env Us.length Δ.toCtx f' :=
              (herlamE.defeq henv hΓ
                (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrvelam htrlam0)).defeq
                henv hΓ (VEnv.IsDefEqU.symm hfdef)
            have herapp : Erasable env Us.length Δ.toCtx (.app f' a'') :=
              hferase.app henv hΓ hTf hTa
            obtain ⟨_, _, hEa, _, _, _, _, _⟩ := iha htra ha' hnb.2 hnfx.2 hcl.2
            exact ⟨.box, vve, .app_box hEf hEa, htrr,
              .box htrr (herapp.defeq henv hΓ hdef), trivial, trivial, trivial⟩
          · obtain ⟨fvv0, htrlam0, hfdef⟩ :=
              SEvalDataι_defeq henv hΔ hcon hiota htrf hf
            cases htrlam0 with
            | @lam ty' _Δ _ty _body body' _name _bi hty' htrty htrb =>
              obtain ⟨atv, avv, hEa, htrav, herav, hnbatv, hnfatv, hclatv⟩ :=
                iha htra ha' hnb.2 hnfx.2 hcl.2
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
                obtain ⟨avv0, htrav0, had0⟩ :=
                  SEvalDataι_defeq henv hΔ hcon hiota htra ha
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
              have hnbsub : NoBlock (LBTerm.subst1 atv b') :=
                noBlock_subst1 (by simpa [NoBlock] using hnbftv) hnbatv
              have hnfsub : NoFix (LBTerm.subst1 atv b') :=
                noFix_subst1 (by simpa [NoFix] using hnfftv) hnfatv
              have hclsub : LBClosed (LBTerm.subst1 atv b') 0 :=
                LBClosed.subst1 (by simpa using hclftv) hclatv
              obtain ⟨t', vve, hEr, htrr, herr, hnbt', hnft', hclt'⟩ := ihbody
                (TrExprS.inst henv.ordered havT htrb htrav)
                (erases_beta_struct henv.ordered htrav havTE hb' herav) hnbsub hnfsub hclsub
              exact ⟨t', vve, .beta hEf hEa hEr, htrr, herr, hnbt', hnft', hclt'⟩
          · exact hnfftv.elim
      · -- block-`ctor` rule: a nonempty block node, refuted by `NoBlock`
        exfalso
        have hargs2_ne : args2 ≠ [] := by
          intro h; subst h; simp only [List.foldl_nil] at hsrc; exact absurd hsrc (by simp)
        have hne : args''.length ≠ 0 := by
          rw [← hlen2]; exact fun h => hargs2_ne (List.eq_nil_of_length_eq_zero h)
        cases args'' with
        | nil => exact absurd rfl hne
        | cons x xs => exact absurd hnb (by simp [NoBlock])
      · -- `cases` rule: the whole application is a *saturated* `casesOn` spine, so its
        -- function part `f` is one argument short — and a partial `casesOn` spine never
        -- evaluates to a λ, contradicting `hf`.
        exfalso
        have hsrc' : Expr.app f a
            = (pre2 ++ discr2 :: minors2).foldl Expr.app (.const con2 us2) := by
          rw [List.foldl_append]; exact hsrc
        rcases List.eq_nil_or_concat (pre2 ++ discr2 :: minors2) with hnil | ⟨init, last, hcc2⟩
        · rw [hnil] at hsrc'; exact absurd hsrc' (by simp)
        · rw [hcc2, List.concat_eq_append, List.foldl_append, List.foldl_cons,
            List.foldl_nil] at hsrc'
          injection hsrc' with hf_eq _
          refine absurd (SEvalDataι_partial_cases_lam_elim hnf hiacoh hf hf_eq
            hcase2 hpre2 hnfs2 ?_) (by exact fun h => h ⟨n, ty, b, bi, rfl⟩)
          have hl : (pre2 ++ discr2 :: minors2).length = init.length + 1 := by
            rw [hcc2]; simp
          simp only [List.length_append, List.length_cons] at hl
          omega
  | @delta n us body r hunf hbodyev ihbody =>
      intro ve t htr her hnb hnfx hcl
      have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
      obtain ⟨bve, htrbody, hbdef⟩ := hcon hunf htr
      obtain ⟨hnoctor, _, body', hlook, herbody, hnbbody⟩ := hdelta hunf
      rcases Erases.const_inv her with ⟨veb, htrb, herbox, rfl⟩
        | ⟨kn, hkn, rfl⟩ | ⟨iid, cidx, hctor, rfl⟩
      · obtain ⟨vve, htrr, hrdef⟩ :=
          SEvalDataι_defeq henv hΔ hcon hiota htr (.delta hunf hbodyev)
        have herve : Erasable env Us.length Δ.toCtx ve := herbox.defeq henv hΓ
          (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrb htr)
        exact ⟨.box, vve, .box, htrr, .box htrr (herve.defeq henv hΓ hrdef),
          trivial, trivial, trivial⟩
      · obtain ⟨t', vve, hEbody, htrr, herr, hnbt', hnft', hclt'⟩ :=
          ihbody htrbody herbody hnbbody (hnfenv hlook) (hclenv hlook)
        subst hkn
        exact ⟨t', vve, .delta hlook hEbody, htrr, herr, hnbt', hnft', hclt'⟩
      · rw [hnoctor] at hctor; exact absurd hctor (by simp)
  | @ctor_val cn us iid cidx ar args vs hcctors har hsat hl hargs ihargs =>
      intro ve t htr her hnb hnfx hcl
      have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
      have harE : constructorArity E iid cidx = some ar := hctorenv hcctors har
      rcases Erases.ctor_spine_inv henv hΔ hcctors (hcc hcctors) args.length args rfl htr her with
        ⟨herve, args', rfl, hmem⟩ | ⟨args', hlen', rfl, hcorr⟩ | hnbt
      · obtain ⟨vve, htrr, hdef⟩ :=
          SEvalDataι_defeq henv hΔ hcon hiota htr
            (.ctor_val hcctors har hsat hl (fun i h => hargs i h))
        have heval : ∀ a' ∈ args', ∃ w, WcbvEval E appliedFlags a' w := by
          intro a' ha'
          obtain ⟨sa, hsa, hera⟩ := hmem a' ha'
          obtain ⟨j, hj, hsaj⟩ := List.mem_iff_getElem.mp hsa
          obtain ⟨sve, htrsa⟩ := (trExprS_appSpine_inv args (.const cn us) ve htr).2 j hj
          obtain ⟨w, _, hEa, _, _, _, _, _⟩ :=
            ihargs j hj htrsa (hsaj ▸ hera) (noBlock_mkApps_inv hnb a' ha')
              (noFix_mkApps_inv hnfx a' ha') (LBClosed.mkApps_inv hcl a' ha')
          exact ⟨w, hEa⟩
        exact ⟨.box, vve, mkApps_headBox_eval WcbvEval.box heval, htrr,
          .box htrr (herve.defeq henv hΓ hdef), trivial, trivial, trivial⟩
      · have hpt : ∀ i, i < args.length →
            ∃ w, ∃ (hiA : i < args'.length) (hiV : i < vs.length),
              WcbvEval E appliedFlags (args'[i]'hiA) w ∧
              Erases env Us Γ Δ (vs[i]'hiV) w ∧ NoBlock w ∧ NoFix w ∧ LBClosed w 0 := by
          intro i h
          have hiA : i < args'.length := hlen' ▸ h
          have hiV : i < vs.length := hl ▸ h
          obtain ⟨sve, htrsa⟩ := (trExprS_appSpine_inv args (.const cn us) ve htr).2 i h
          have hnba' : NoBlock (args'[i]'hiA) := noBlock_mkApps_inv hnb _ (List.getElem_mem _)
          have hnfa' : NoFix (args'[i]'hiA) := noFix_mkApps_inv hnfx _ (List.getElem_mem _)
          have hcla' : LBClosed (args'[i]'hiA) 0 := LBClosed.mkApps_inv hcl _ (List.getElem_mem _)
          obtain ⟨w, vve, hEa, htrvi, hervi, hnbw, hnfw, hclw⟩ :=
            ihargs i h htrsa (hcorr i hiA) hnba' hnfa' hcla'
          exact ⟨w, hiA, hiV, hEa, hervi, hnbw, hnfw, hclw⟩
        obtain ⟨ws, hwslen, hws⟩ := choose_list args.length hpt
        have hbase : WcbvEval E appliedFlags (.construct iid cidx [])
            (LBTerm.mkApps (.construct iid cidx []) []) := by
          simpa using WcbvEval.construct_atom (Γ := E) (fl := appliedFlags) rfl harE
        have hle : ([] : List LBTerm).length + args'.length ≤ ar := by
          simp only [List.length_nil, Nat.zero_add]; rw [← hlen']; exact hsat
        have hlaw : args'.length = ws.length := by omega
        have hpe : ∀ i (hi : i < args'.length),
            WcbvEval E appliedFlags (args'[i]'hi) (ws[i]'(hlaw ▸ hi)) := by
          intro i hi
          obtain ⟨_, _, hE, _, _, _, _⟩ := hws i (hlaw ▸ hi)
          exact hE
        have hTeval := construct_app_spine harE args' ws (.construct iid cidx []) [] hbase hle hlaw hpe
        rw [← mkApps_eq_foldl, List.nil_append] at hTeval
        obtain ⟨vve, htrr, _⟩ :=
          SEvalDataι_defeq henv hΔ hcon hiota htr
            (.ctor_val hcctors har hsat hl (fun i h => hargs i h))
        have hVerase : Erases env Us Γ Δ (vs.foldl Expr.app (.const cn us))
            (LBTerm.mkApps (.construct iid cidx []) ws) := by
          refine erases_app_spine (.ctor_head cn us iid cidx hcctors) vs ws (by omega) ?_
          intro i hi
          obtain ⟨_, _, _, hEr, _, _, _⟩ := hws i (by omega)
          exact hEr
        have hVnb : NoBlock (LBTerm.mkApps (.construct iid cidx []) ws) := by
          refine noBlock_mkApps_construct (fun w hw => ?_)
          obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hw
          obtain ⟨_, _, _, _, hnbw, _, _⟩ := hws j hj
          exact hnbw
        have hVnf : NoFix (LBTerm.mkApps (.construct iid cidx []) ws) := by
          refine noFix_mkApps (NoFix_construct iid cidx []) (fun w hw => ?_)
          obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hw
          obtain ⟨_, _, _, _, _, hnfw, _⟩ := hws j hj
          exact hnfw
        have hVcl : LBClosed (LBTerm.mkApps (.construct iid cidx []) ws) 0 := by
          refine LBClosed.mkApps (by simp [LBClosedArgs]) (fun w hw => ?_)
          obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hw
          obtain ⟨_, _, _, _, _, _, hclw⟩ := hws j hj
          exact hclw
        exact ⟨_, vve, hTeval, htrr, hVerase, hVnb, hVnf, hVcl⟩
      · exact absurd hnb hnbt
  | @iota con us cus pre minors cargs discr ctor iid np cidx nmot nidx nmin ar r
      hcases hctor hia har hpre hmin hcargs hdiscr hidx hbranch ihdiscr ihbranch =>
      intro ve t htr her hnb hnfx hcl
      have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
      -- (1) reconcile the two parses of the redex: `ia`-arithmetic vs `Γ`-pins.
      obtain ⟨hdp0, nfs, hnfs, hnfsl⟩ := hiacoh hcases hia
      have hdp : Γ.casesDiscrPos con = some pre.length := by rw [hpre]; exact hdp0
      have hminl : minors.length = nfs.length := by omega
      have hctors : Γ.ctors con = none := by
        rcases h : Γ.ctors con with _ | ⟨i2, c2⟩
        · rfl
        · rw [hcc h] at hcases; exact absurd hcases (by simp)
      -- (2) invert the erasure of the redex, using prefix-relevance.
      have hrel' : ∀ k, k < pre.length + 1 + nfs.length → ∀ {vk : VExpr},
          TrExprS env Us Δ (((pre ++ discr :: minors).take k).foldl Expr.app (.const con us)) vk →
          ¬ Erasable env Us.length Δ.toCtx vk := by
        intro k hk vk htrk
        refine informativeType_not_erasable henv hΔ (hrel.partialCases hcases hdp hnfs ?_) htrk
        have hlk : ((pre ++ discr :: minors).take k).length = k := by
          rw [List.length_take]
          simp only [List.length_append, List.length_cons]
          omega
        omega
      rcases Erases.iota_redex_inv henv hΔ hcases hdp hnfs hctors hminl hrel' htr her hnb with
        ⟨herve, rfl⟩ | ⟨discr', alts', hlen, rfl, hd, harity, halts⟩
      · -- the whole match is irrelevant: `t = .box`
        obtain ⟨vve, htrr, hdef⟩ :=
          SEvalDataι_defeq henv hΔ hcon hiota htr
            (.iota hcases hctor hia har hpre hmin hcargs hdiscr hidx hbranch)
        exact ⟨.box, vve, .box, htrr, .box htrr (herve.defeq henv hΓ hdef),
          trivial, trivial, trivial⟩
      · -- (3) evaluate the discriminant
        obtain ⟨dve, htrd⟩ :=
          (trExprS_appSpine_inv (discr :: minors) (pre.foldl Expr.app (.const con us)) ve htr).2
            0 (by simp)
        rw [NoBlock_case] at hnb
        rw [NoFix_case] at hnfx
        rw [LBClosed_case, LBClosedAlts_iff] at hcl
        obtain ⟨dt', dvv, hEd, htrdv, herdv, hnbd, hnfd, hcld⟩ :=
          ihdiscr (by simpa using htrd) hd hnb.1 hnfx.1 hcl.1
        -- (4) shape the discriminant's value: a non-erasable constructor spine
        rcases Erases.ctor_spine_inv henv hΔ hctor (hcc hctor) cargs.length cargs rfl
            htrdv herdv with
          ⟨hercv, cargs', rfl, _⟩ | ⟨cargs', hclen, rfl, hccorr⟩ | hnbt
        · exact absurd hercv (informativeType_not_erasable henv hΔ
            (hrel.ctorValue hctor ⟨con, np, hcases⟩) htrdv)
        · -- (5) arity arithmetic: flatness collapses the field list
          obtain ⟨hcidx, harc⟩ := hcoh hcases hnfs hctor
          have hzero : nfs[cidx]'hcidx = 0 := hflat hcases hnfs cidx hcidx
          have harnp : ar = np := by
            rw [har] at harc; simp only [Option.some.injEq] at harc
            omega
          have hcargsnp : cargs.length = np := by omega
          have hcidxa : cidx < alts'.length := by omega
          have hnames : (alts'[cidx]'hcidxa).1.length = 0 := by
            rw [harity cidx hcidxa]; simpa using hzero
          obtain hnamesnil : (alts'[cidx]'hcidxa).1 = [] :=
            List.eq_nil_of_length_eq_zero hnames
          have hdropc : cargs.drop np = [] := by
            apply List.eq_nil_of_length_eq_zero; simp; omega
          have hdropc' : cargs'.drop np = [] := by
            apply List.eq_nil_of_length_eq_zero; simp; omega
          -- (6) the reduct's erasure: the branch body itself (flat regime)
          have herbranch : Erases env Us Γ Δ
              ((cargs.drop np).foldl Expr.app (minors[cidx]'hidx))
              (alts'[cidx]'hcidxa).2 := by
            rw [hdropc, List.foldl_nil]
            have := halts cidx hcidxa
            rw [hnamesnil] at this
            simpa [mkLambdas] using this
          -- (7) the reduct's translation, from `IotaConsistent`
          obtain ⟨bve, htrbranch, hdefb⟩ :=
            SEvalDataι_iota_reduct henv hΔ hiota hcases hctor hia har hpre hmin hcargs hidx
              (fun htrx => SEvalDataι_defeq henv hΔ hcon hiota htrx hdiscr) htr
          -- (8) the branch IH
          have hnbb : NoBlock (alts'[cidx]'hcidxa).2 :=
            hnb.2 _ (List.getElem_mem hcidxa)
          have hnfb : NoFix (alts'[cidx]'hcidxa).2 :=
            hnfx.2 _ (List.getElem_mem hcidxa)
          have hclb : LBClosed (alts'[cidx]'hcidxa).2 0 := by
            have := hcl.2 _ (List.getElem_mem hcidxa)
            rw [hnamesnil] at this; simpa using this
          obtain ⟨t', vve, hEbranch, htrr, herr, hnbt', hnft', hclt'⟩ :=
            ihbranch htrbranch herbranch hnbb hnfb hclb
          -- (9)/(10) fire the target ι rule; the reversal bridge is `rfl` here
          refine ⟨t', vve, ?_, htrr, herr, hnbt', hnft', hclt'⟩
          refine WcbvEval.iota (names := (alts'[cidx]'hcidxa).1)
            (body := (alts'[cidx]'hcidxa).2) rfl (hcasesenv hcases) hEd ?_ ?_ ?_
          · rw [List.getElem?_eq_getElem hcidxa]
          · rw [hdropc']; simp only [List.length_nil]; exact hnames.symm
          · rw [hdropc']
            simpa [LBTerm.substList] using hEbranch
        · exact absurd hnbd hnbt

end LeanToLambdaBox
