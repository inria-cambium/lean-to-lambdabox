import LeanToLambdaBox.SubjectReductionIota
import LeanToLambdaBox.Closed
import LeanToLambdaBox.IotaBridge

/-!
# Erasure correctness for the ι (`casesOn`) fragment — the forward simulation

`erases_correct_dataι` is the ι counterpart of `erases_correct_data`: forward simulation
at MetaRocq's non-block `appliedFlags` over `SEvalDataι` (β + δ + saturated constructors +
the corrected ι, and since projection round slice P5 structure projections as well), with
the same conclusion shape. It is **additive** —
`erases_correct_data` / `erases_correct_data_zeta` are untouched.

It lives in its own file because it needs `SEvalDataι_defeq`, and `SubjectReductionIota`
already imports `ErasesCorrectData`.

## What the ι case needs beyond the β/δ/ctor cases

Four things that the non-ι fragment never met, each recorded on the declaration that
carries it:

* **`NoBlock` must see `.case`** (done in `ErasesCorrectData.lean`). Inverting the target
  `.case (iid, np) discr' alts'` is useless if the discriminant IH cannot be fed. (`NoFix`
  was threaded here too until the recursion wall's slice W2 retired it from the
  simulations.)
* **A closedness thread (`LBClosed t 0`).** The β-chain ↔ reversing-`iota_red` bridge is
  *false* for field values with loose de Bruijn variables: at two fields the β chain gives
  `subst f₁ 0 (subst f₀ 1 body)` while `substList (fields.reverse) body` gives
  `subst f₀ 0 (subst f₁ 0 body)`, and these agree only when `subst f₀ 0 f₁ = f₁`. This is
  MetaRocq's own `closedn 0` convention (its `eval`/`erases_correct` carry it everywhere),
  not a modelling shortcut. `ClosedEnv` is the environment-level counterpart. The thread
  is *ι-specific*: it exists only to feed the bridge, which is why no other forward
  simulation in the development carries it. The full counterexample is
  recorded on `wcbvEval_mkApps_mkLambdas_substList` (`IotaBridge.lean`).
* **Relevance side conditions** (`IotaRelevant`, `SubjectReductionIota.lean`): the model
  permits `Erases` derivations that box a *proper prefix* of an ι redex, or box the
  scrutinee's constructor value; both leave the target `.case` stuck, so both must be
  excluded. The shipping `visitCases` emits neither.
* **A source/target pin reconciliation.** `SEvalDataι.iota` pins its redex arithmetically
  (through `IotaArities`); `Erases.cases` pins it through `Γ`
  (`casesDiscrPos`/`ctorFields`). `IotaArityCoherent` links them, and
  `CtorFieldsCoherent` turns the constructor's full arity into `numParams + nfields` — the
  step that converts `(cargs.drop np).length` into the selected alternative's binder count.

## Scope: field-carrying constructors are covered

The simulation carries **no** zero-field restriction. Every constructor arity is in
scope: the ι case builds the erased reduct as the minor's λ-telescope applied to the
constructor's field values, `mkApps (mkLambdas names body) fields`, and
`wcbvEval_mkApps_mkLambdas_substList` (`IotaBridge.lean`) turns the resulting β chain
into the target rule's one-shot `substList (fields.reverse) body`. The zero-field regime
that the earlier `FlatCaseFields` slice covered is the bridge's `fields = []` base case,
where it degenerates to `rfl`.

The other two pieces of the ι stack were already general, which is why the lift is
confined to this file: T4b's `Supported.casesApp` / `Supported.casesApp_inv` pin each
minor to a *manifest λ-telescope* of its constructor's field arity, and `IotaShape`'s
per-constructor equation landed in **two β stages** precisely because Lean's generated
`casesOn` η-expands every minor that takes fields —
`Option.casesOn := fun {α} {motive} t none some => Option.rec none (fun val => some val) t`
— so the reduct ends in a redex `betaN` cannot contract (it is built by the template's
body rather than pending in the supplied argument list), which made the *single*-stage
form unsatisfiable for every field-carrying inductive (`betaN_ruleTemplate_eta_guard` /
`betaN_ruleTemplate_rec_guard`, `IotaDischarge.lean`).

`FlatCaseFields` survives only as the *measure* of what was lifted: `gΓflat_flat` and
`gΓfield_not_flat` below exhibit a `Γ` inside it and a field-carrying `Γ` outside it, at
which the simulation's certificate block is still constructed.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-! ## The two new environment/`Γ` side conditions -/

/-- **Every stored constant body is de Bruijn closed** — the target-side counterpart of
"constant bodies are closed terms". It is what keeps the `LBClosed` thread alive across a
δ step. (`RegisteredClosure`'s
context-uniformity clause already relies on the same fact on the source side.) -/
def ClosedEnv (E : GlobalDeclarations) : Prop :=
  ∀ {kn : Kername} {body : LBTerm},
    LBTerm.envLookup E kn = some (.constantDecl ⟨some body⟩) → LBClosed body 0

/-- **Target-side ι precondition.** `WcbvEval.iota` fires only on a non-propositional
inductive (`isPropositionalInductive E iid = false`); a propositional one reduces by
`iota_sing` instead, which needs `with_prop_case`. `ErasesEnvCases`
(`EnvErasureNonrec.lean`) delivers the `.inductiveDecl`/`npars` half of the `casesOn` env
consistency but says nothing about `oib.propositional`, so the ι simulation asks for this
separately.

It is *derived*, not assumed, wherever the registration record is in scope:
`ErasesEnvCases.nonProp` (`EnvErasureNonrec.lean`, whose `ErasesEnvCases`/`RegisteredCases`
now carry the `oib.propositional = false` conjunct) has exactly this conclusion, so
`fun hc => ErasesEnvCases.nonProp h hc` discharges it. The two are kept as separate
predicates only because importing `EnvErasureNonrec` here would drag the whole shipping
bridge into the forward simulation's dependency cone; the composition happens at the
capstone, where both are already in scope. -/
def ErasesEnvCasesι (Γ : ErasureCtx) (E : GlobalDeclarations) : Prop :=
  ∀ {con : Name} {iid : InductiveId} {numParams : Nat},
    Γ.casesOns con = some (iid, numParams) → isPropositionalInductive E iid = false

/-- **The projection simulation's thin env premise** (projection round, slice P0), the
`ErasesEnvCasesι` transpose. `WcbvEval.proj` — the non-block rule, the one `appliedFlags`
runs — asks for `isPropositionalInductive E p.indType = false` and nothing else, so this
is what the simulation takes; the fat record with the `npars` agreement is
`ErasesEnvProjs`/`RegisteredProjs` (`EnvErasureNonrec.lean`), and
`ErasesEnvProjs.nonProp` is exactly this conclusion, so
`fun hS => ErasesEnvProjs.nonProp h hS` discharges it. The two are kept apart for the
reason recorded above: importing `EnvErasureNonrec` here would drag the whole shipping
bridge into the forward simulation's dependency cone. -/
def ErasesEnvProjsι (Γ : ErasureCtx) (E : GlobalDeclarations) : Prop :=
  ∀ {S : Name} {iid : InductiveId} {np : Nat},
    Γ.projs S = some (iid, np) → isPropositionalInductive E iid = false

/-- **Free at a structure-free `Γ`** (projection round, slice P7), the third member of
the vacuity trio with `projConsistent_of_noProjs` / `projFieldsCoherent_of_noProjs`
(`SourceEvalData.lean`). Every capstone instantiation that predates the round registers
no structure, so all three of the simulation's new premises are *discharged* there
rather than assumed — which is what keeps the round additive at the guards. -/
theorem erasesEnvProjsι_of_noProjs {Γ : ErasureCtx} {E : GlobalDeclarations}
    (h : Γ.projs = fun _ => none) : ErasesEnvProjsι Γ E := by
  intro _ _ _ hs; rw [h] at hs; exact absurd hs (by simp)

/-- **The flat fragment.** Every constructor of an inductive eliminated by some registered
`casesOn` has zero retained fields (`Bool`, `Ordering`, enumerations).

This is **no longer a hypothesis of anything.** It was the scope restriction the ι
simulation carried while the reversal bridge was missing, and it is retained purely as
the *measure* of the region S4b lifted: `gΓflat_flat` exhibits a `Γ` inside it,
`gΓfield_not_flat` a field-carrying `Γ` outside it — and `erases_correct_dataι` now
covers both. -/
def FlatCaseFields (Γ : ErasureCtx) : Prop :=
  ∀ {con : Name} {iid : InductiveId} {np : Nat} {nfs : List Nat},
    Γ.casesOns con = some (iid, np) → Γ.ctorFields iid = some nfs →
    ∀ j (h : j < nfs.length), nfs[j] = 0

/-! ## `NoBlock`/`NoFix` under a λ-telescope

The two structural predicates pass through `mkLambdas` unchanged (`LBClosed` does not —
a telescope *closes* `names.length` levels, which is `LBClosed.mkLambdas`). The ι case
needs all three to feed the branch IH on `mkApps (mkLambdas names body) fields`. -/

theorem noBlock_mkLambdas {names : List BinderName} {body : LBTerm} (h : NoBlock body) :
    NoBlock (mkLambdas names body) := by
  induction names with
  | nil => exact h
  | cons n ns ih => exact ih

theorem noFix_mkLambdas {names : List BinderName} {body : LBTerm} (h : NoFix body) :
    NoFix (mkLambdas names body) := by
  induction names with
  | nil => exact h
  | cons n ns ih => exact ih

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
  | @proj S ctor cus cargs iid np nf i ar discr r hs hctor hnfs har hcargs hi
      hdiscr hlt hsel _ _ =>
      -- a `.proj` source is never a `.const`-headed spine, so the premise is refuted —
      -- the `lit` arm verbatim, at the projection round's own head-mismatch lemma
      intro con us args iid₀ np₀ dp nfs heq _ _ _ _
      exact absurd heq.symm foldl_app_const_ne_proj
  | @lit l r hev _ =>
      -- a `.lit` source is never a `.const`-headed spine, so the premise is refuted
      intro con us args iid np dp nfs heq _ _ _ _
      exact absurd heq.symm foldl_app_const_ne_lit

/-! ## The ι forward simulation -/

/-- **Erasure correctness — forward simulation, β + δ + saturated constructors + ι +
projections, at MetaRocq's non-block `appliedFlags`.**

The ι counterpart of `erases_correct_data`: same conclusion shape, over `SEvalDataι`
(which has no `zeta` rule), plus the `LBClosed` thread and the ι-specific side conditions
documented in the module header. Additive — `erases_correct_data`'s signature is untouched.
Constructors of **any** arity are covered; the reversal bridge
(`wcbvEval_mkApps_mkLambdas_substList`) is what reconciles the β chain the erased minor
produces with the one-shot `substList` of the target ι rule.

The ported β/δ/ctor cases differ from `erases_correct_data`'s only in that `SEvalDataι`
has no forgetful map to `SEvalβζδ` (ι is not in that fragment), so every
`SEvalβζδ_defeq henv hΔ hcon …` becomes `SEvalDataι_defeq henv hΔ hcon hiota hproj …` — same
rôle, same output triple, one extra argument — and in the `LBClosed` bookkeeping.

Note the *reverse* disjointness (`Γ.casesOns con = some _ → Γ.ctors con = none`) is not a
new premise: it follows from `hcc`.

**Recursion (wall slice W2).** As for `erases_correct_data`: `NoFixEnv E` and the
`NoFix t`/`NoFix t'` slots are gone, replaced by `RecEnvConsistent`. The β case's
recursive head goes through `erases_lam_head_step` at
`P := fun x => NoBlock x ∧ LBClosed x 0`, whose two chain-preservation instances are
`FixUnfoldChain.noBlock` and `FixUnfoldChain.lbClosed` — the latter is why the closedness
thread survives a fix unfolding (each entry of `fixSubst defs` is closed exactly when the
block is, and `defs[idx].body` is closed under `defs.length` binders). -/
theorem erases_correct_dataι {env : VEnv} (henv : env.WF) {Us : List Name} {Δ : VLCtx}
    (hΔ : VLCtx.WF env Us.length Δ) {Γ : ErasureCtx} {ia : IotaArities}
    {Esrc : SEnv} {E : GlobalDeclarations}
    (hcon : SEnvConsistent env Us Esrc)
    (hiota : IotaConsistent env Us Γ ia)
    (hproj : ProjConsistent env Us Γ)
    (hdelta : ErasesEnvDeltaData env Us Γ Esrc E)
    (hctorenv : ErasesEnvCtor Γ E)
    (hcasesenv : ErasesEnvCasesι Γ E)
    (hprojenv : ErasesEnvProjsι Γ E)
    (hcoh : CtorFieldsCoherent Γ)
    (hpcoh : ProjFieldsCoherent Γ)
    (hiacoh : IotaArityCoherent Γ ia)
    (hrel : IotaRelevant env Us Γ)
    (hcc : ∀ {cn : Name} {iid : InductiveId} {cidx : Nat},
             Γ.ctors cn = some (iid, cidx) → Γ.casesOns cn = none)
    (hrec : RecEnvConsistent env Us Γ Esrc E)
    (hnfv : Γ.fixvars = fun _ => none)
    (hclenv : ClosedEnv E)
    {e v : Expr} (hev : SEvalDataι Γ ia Esrc e v) :
    ∀ {ve : VExpr} {t : LBTerm},
      TrExprS env Us Δ e ve → Erases env Us Γ Δ e t →
      NoBlock t → LBClosed t 0 →
      ∃ t' vve, WcbvEval E appliedFlags t t' ∧ TrExprS env Us Δ v vve ∧
        Erases env Us Γ Δ v t' ∧ NoBlock t' ∧ LBClosed t' 0 := by
  have hnf : ∀ {n : Name} {body : Expr}, Esrc n = some body →
      Γ.ctors n = none ∧ Γ.casesOns n = none :=
    fun h => ⟨(hdelta (Δ := Δ) h).1, (hdelta (Δ := Δ) h).2.1⟩
  induction hev with
  | lam n ty b bi =>
      intro ve t htr her hnb hcl
      have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
      rcases Erases.lam_inv her with ⟨veb, htrb, herbox, rfl⟩ | ⟨_, _, hty, hb, rfl⟩
        | ⟨defs, idx, rfl, herfix⟩
      · exact ⟨.box, ve, .box, htr, .box htr
          (herbox.defeq henv hΓ
            (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrb htr)),
          trivial, trivial⟩
      · exact ⟨_, ve, .lam _ _, htr, .lam hty hb, hnb, hcl⟩
      · -- A recursive λ-value: the target block is already a value (`fix_atom`).
        exact ⟨_, ve, .fix_atom _ _, htr, herfix, hnb, hcl⟩
  | @beta f a n ty b bi av r hf ha hbody ihf iha ihbody =>
      intro ve t htr her hnb hcl
      have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
      rcases her.app_inv_t with
        ⟨veb, htrb, herbox, rfl⟩ |
        ⟨f't, a't, hf', ha', rfl⟩ |
        ⟨cn2, us2, args2, iid2, cidx2, args'', hsrc, hc2, hlen2, rfl⟩ |
        ⟨con2, us2, pre2, discr2, minors2, iid2, np2, discr', alts', nfs2, hsrc,
          hcase2, hpre2, hnfs2, hd2, hlen2, hnlen2, harity2, halts2, rfl⟩
      · obtain ⟨vve, htrr, hdef⟩ :=
          SEvalDataι_defeq henv hΔ hcon hiota hproj htr (.beta hf ha hbody)
        have herve : Erasable env Us.length Δ.toCtx ve := herbox.defeq henv hΓ
          (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrb htr)
        exact ⟨.box, vve, .box, htrr, .box htrr (herve.defeq henv hΓ hdef),
          trivial, trivial⟩
      · cases htr with
        | @app f' A B a'' _Δ _f _a hTf hTa htrf htra =>
          obtain ⟨ftv, fvv, hEf, htrlam, herlam, hnbftv, hclftv⟩ :=
            ihf htrf hf' hnb.1 hcl.1
          obtain ⟨atv, avv, hEa, htrav, herav, hnbatv, hclatv⟩ :=
            iha htra ha' hnb.2 hcl.2
          rcases erases_lam_head_step (P := fun x => NoBlock x ∧ LBClosed x 0) rfl
              (fun hch hP => ⟨hch.noBlock hP.1, hch.lbClosed hP.2⟩)
              hEf hEa herlam ⟨hnbftv, hclftv⟩ with
            ⟨velam, htrvelam, herlamE, hEbox⟩ | ⟨tyE, b', htrtyE, hb', hPb', hEstep⟩
          · obtain ⟨vve, htrr, hdef⟩ :=
              SEvalDataι_defeq henv hΔ hcon hiota hproj (.app hTf hTa htrf htra)
                (.beta hf ha hbody)
            obtain ⟨fvv0, htrlam0, hfdef⟩ :=
              SEvalDataι_defeq henv hΔ hcon hiota hproj htrf hf
            have hferase : Erasable env Us.length Δ.toCtx f' :=
              (herlamE.defeq henv hΓ
                (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrvelam htrlam0)).defeq
                henv hΓ (VEnv.IsDefEqU.symm hfdef)
            have herapp : Erasable env Us.length Δ.toCtx (.app f' a'') :=
              hferase.app henv hΓ hTf hTa
            exact ⟨.box, vve, hEbox, htrr,
              .box htrr (herapp.defeq henv hΓ hdef), trivial, trivial⟩
          · obtain ⟨fvv0, htrlam0, hfdef⟩ :=
              SEvalDataι_defeq henv hΔ hcon hiota hproj htrf hf
            cases htrlam0 with
            | @lam ty' _Δ _ty _body body' _name _bi hty' htrty htrb =>
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
                  SEvalDataι_defeq henv hΔ hcon hiota hproj htra ha
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
                noBlock_subst1 (by simpa [NoBlock] using hPb'.1) hnbatv
              have hclsub : LBClosed (LBTerm.subst1 atv b') 0 :=
                LBClosed.subst1 (by simpa using hPb'.2) hclatv
              obtain ⟨t', vve, hEr, htrr, herr, hnbt', hclt'⟩ := ihbody
                (TrExprS.inst henv.ordered havT htrb htrav)
                (erases_beta_struct henv.ordered htrav havTE hb' herav) hnbsub hclsub
              exact ⟨t', vve, hEstep hEr, htrr, herr, hnbt', hclt'⟩
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
      intro ve t htr her hnb hcl
      have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
      obtain ⟨bve, htrbody, hbdef⟩ := hcon hunf htr
      obtain ⟨hnoctor, _, body', hlook, herbody, hnbbody⟩ := hdelta hunf
      rcases Erases.const_inv her with ⟨veb, htrb, herbox, rfl⟩
        | ⟨kn, hkn, rfl⟩ | ⟨iid, cidx, hctor, rfl⟩ | ⟨defs, fidx, hrecn, rfl⟩
        | ⟨x, hfx, rfl⟩
      · obtain ⟨vve, htrr, hrdef⟩ :=
          SEvalDataι_defeq henv hΔ hcon hiota hproj htr (.delta hunf hbodyev)
        have herve : Erasable env Us.length Δ.toCtx ve := herbox.defeq henv hΓ
          (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrb htr)
        exact ⟨.box, vve, .box, htrr, .box htrr (herve.defeq henv hΓ hrdef),
          trivial, trivial⟩
      · obtain ⟨t', vve, hEbody, htrr, herr, hnbt', hclt'⟩ :=
          ihbody htrbody herbody hnbbody (hclenv hlook)
        subst hkn
        exact ⟨t', vve, .delta hlook hEbody, htrr, herr, hnbt', hclt'⟩
      · rw [hnoctor] at hctor; exact absurd hctor (by simp)
      · -- `const_fix`: see `erases_correct_data`'s δ case — `RecEnvConsistent` turns
        -- the block back into the source body's erasure and the IH does the rest.
        obtain ⟨_, _, _, body₀, hunf₀, her₀⟩ := hrec.reg hrecn
        rw [hunf] at hunf₀
        obtain rfl : body₀ = body := by simpa using hunf₀.symm
        exact ihbody htrbody her₀ hnb hcl
      · -- `fixvar`: `hnfv` says `Γ` installs no fixvar map, so an in-block sibling
        -- reference cannot occur at a top-level evaluation.
        rw [hnfv] at hfx; exact absurd hfx (by simp)
  | @ctor_val cn us iid cidx ar args vs hcctors har hsat hl hargs ihargs =>
      intro ve t htr her hnb hcl
      have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
      have harE : constructorArity E iid cidx = some ar := hctorenv hcctors har
      rcases Erases.ctor_spine_inv henv hΔ hcctors (hcc hcctors) args.length args rfl htr her with
        ⟨herve, args', rfl, hmem⟩ | ⟨args', hlen', rfl, hcorr⟩ | hnbt
      · obtain ⟨vve, htrr, hdef⟩ :=
          SEvalDataι_defeq henv hΔ hcon hiota hproj htr
            (.ctor_val hcctors har hsat hl (fun i h => hargs i h))
        have heval : ∀ a' ∈ args', ∃ w, WcbvEval E appliedFlags a' w := by
          intro a' ha'
          obtain ⟨sa, hsa, hera⟩ := hmem a' ha'
          obtain ⟨j, hj, hsaj⟩ := List.mem_iff_getElem.mp hsa
          obtain ⟨sve, htrsa⟩ := (trExprS_appSpine_inv args (.const cn us) ve htr).2 j hj
          obtain ⟨w, _, hEa, _, _, _, _⟩ :=
            ihargs j hj htrsa (hsaj ▸ hera) (noBlock_mkApps_inv hnb a' ha')
              (LBClosed.mkApps_inv hcl a' ha')
          exact ⟨w, hEa⟩
        exact ⟨.box, vve, mkApps_headBox_eval WcbvEval.box heval, htrr,
          .box htrr (herve.defeq henv hΓ hdef), trivial, trivial⟩
      · have hpt : ∀ i, i < args.length →
            ∃ w, ∃ (hiA : i < args'.length) (hiV : i < vs.length),
              WcbvEval E appliedFlags (args'[i]'hiA) w ∧
              Erases env Us Γ Δ (vs[i]'hiV) w ∧ NoBlock w ∧ LBClosed w 0 := by
          intro i h
          have hiA : i < args'.length := hlen' ▸ h
          have hiV : i < vs.length := hl ▸ h
          obtain ⟨sve, htrsa⟩ := (trExprS_appSpine_inv args (.const cn us) ve htr).2 i h
          have hnba' : NoBlock (args'[i]'hiA) := noBlock_mkApps_inv hnb _ (List.getElem_mem _)
          have hcla' : LBClosed (args'[i]'hiA) 0 := LBClosed.mkApps_inv hcl _ (List.getElem_mem _)
          obtain ⟨w, vve, hEa, htrvi, hervi, hnbw, hclw⟩ :=
            ihargs i h htrsa (hcorr i hiA) hnba' hcla'
          exact ⟨w, hiA, hiV, hEa, hervi, hnbw, hclw⟩
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
          obtain ⟨_, _, hE, _, _, _⟩ := hws i (hlaw ▸ hi)
          exact hE
        have hTeval := construct_app_spine harE args' ws (.construct iid cidx []) [] hbase hle hlaw hpe
        rw [← mkApps_eq_foldl, List.nil_append] at hTeval
        obtain ⟨vve, htrr, _⟩ :=
          SEvalDataι_defeq henv hΔ hcon hiota hproj htr
            (.ctor_val hcctors har hsat hl (fun i h => hargs i h))
        have hVerase : Erases env Us Γ Δ (vs.foldl Expr.app (.const cn us))
            (LBTerm.mkApps (.construct iid cidx []) ws) := by
          refine erases_app_spine (.ctor_head cn us iid cidx hcctors) vs ws (by omega) ?_
          intro i hi
          obtain ⟨_, _, _, hEr, _, _⟩ := hws i (by omega)
          exact hEr
        have hVnb : NoBlock (LBTerm.mkApps (.construct iid cidx []) ws) := by
          refine noBlock_mkApps_construct (fun w hw => ?_)
          obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hw
          obtain ⟨_, _, _, _, hnbw, _⟩ := hws j hj
          exact hnbw
        have hVcl : LBClosed (LBTerm.mkApps (.construct iid cidx []) ws) 0 := by
          refine LBClosed.mkApps (by simp [LBClosedArgs]) (fun w hw => ?_)
          obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hw
          obtain ⟨_, _, _, _, _, hclw⟩ := hws j hj
          exact hclw
        exact ⟨_, vve, hTeval, htrr, hVerase, hVnb, hVcl⟩
      · exact absurd hnb hnbt
  | @iota con us cus pre minors cargs discr ctor iid np cidx nmot nidx nmin ar r
      hcases hctor hia har hpre hmin hcargs hdiscr hidx hbranch ihdiscr ihbranch =>
      intro ve t htr her hnb hcl
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
        refine informativeType_not_erasable henv hΔ (hrel.partialCases hcases hdp hnfs ?_ htrk) htrk
        have hlk : ((pre ++ discr :: minors).take k).length = k := by
          rw [List.length_take]
          simp only [List.length_append, List.length_cons]
          omega
        omega
      rcases Erases.iota_redex_inv henv hΔ hcases hdp hnfs hctors hminl hrel' htr her hnb with
        ⟨herve, rfl⟩ | ⟨discr', alts', hlen, rfl, hd, harity, halts⟩
      · -- the whole match is irrelevant: `t = .box`
        obtain ⟨vve, htrr, hdef⟩ :=
          SEvalDataι_defeq henv hΔ hcon hiota hproj htr
            (.iota hcases hctor hia har hpre hmin hcargs hdiscr hidx hbranch)
        exact ⟨.box, vve, .box, htrr, .box htrr (herve.defeq henv hΓ hdef),
          trivial, trivial⟩
      · -- (3) evaluate the discriminant
        obtain ⟨dve, htrd⟩ :=
          (trExprS_appSpine_inv (discr :: minors) (pre.foldl Expr.app (.const con us)) ve htr).2
            0 (by simp)
        rw [NoBlock_case] at hnb
        rw [LBClosed_case, LBClosedAlts_iff] at hcl
        obtain ⟨dt', dvv, hEd, htrdv, herdv, hnbd, hcld⟩ :=
          ihdiscr (by simpa using htrd) hd hnb.1 hcl.1
        -- (4) shape the discriminant's value: a non-erasable constructor spine
        rcases Erases.ctor_spine_inv henv hΔ hctor (hcc hctor) cargs.length cargs rfl
            htrdv herdv with
          ⟨hercv, cargs', rfl, _⟩ | ⟨cargs', hclen, rfl, hccorr⟩ | hnbt
        · exact absurd hercv (informativeType_not_erasable henv hΔ
            (hrel.ctorValue hctor (.inl ⟨con, np, hcases⟩) htrdv) htrdv)
        · -- (5) arity arithmetic: the constructor's field block *is* the selected
          --     alternative's λ-telescope (`CtorFieldsCoherent` links the two arities)
          obtain ⟨hcidx, harc⟩ := hcoh hcases hnfs hctor
          have harnf : ar = np + nfs[cidx]'hcidx := by rw [har] at harc; exact Option.some.inj harc
          have hcidxa : cidx < alts'.length := by omega
          have hnames : (alts'[cidx]'hcidxa).1.length = nfs[cidx]'hcidx := harity cidx hcidxa
          have hdropl : (cargs.drop np).length = nfs[cidx]'hcidx := by
            simp only [List.length_drop]; omega
          have hdropl' : (cargs'.drop np).length = nfs[cidx]'hcidx := by
            simp only [List.length_drop]; omega
          -- (6) the reduct's erasure: the minor's λ-telescope applied to the field values
          have hfields : ∀ i (h : i < (cargs.drop np).length),
              Erases env Us Γ Δ ((cargs.drop np)[i]'h) ((cargs'.drop np)[i]'(by omega)) := by
            intro i h
            have hi : np + i < cargs'.length := by
              simp only [List.length_drop] at h; omega
            simpa only [List.getElem_drop] using hccorr (np + i) hi
          have herbranch : Erases env Us Γ Δ
              ((cargs.drop np).foldl Expr.app (minors[cidx]'hidx))
              (LBTerm.mkApps (mkLambdas (alts'[cidx]'hcidxa).1 (alts'[cidx]'hcidxa).2)
                (cargs'.drop np)) :=
            erases_app_spine (halts cidx hcidxa) (cargs.drop np) (cargs'.drop np)
              (by omega) hfields
          -- (7) the reduct's translation, from `IotaConsistent`
          obtain ⟨bve, htrbranch, hdefb⟩ :=
            SEvalDataι_iota_reduct henv hΔ hiota hcases hctor hia har hpre hmin hcargs hidx
              (fun htrx => SEvalDataι_defeq henv hΔ hcon hiota hproj htrx hdiscr) htr
          -- (8) the branch IH, on the applied telescope
          have hfieldnb : ∀ x ∈ cargs'.drop np, NoBlock x :=
            fun x hx => noBlock_mkApps_inv hnbd x (List.mem_of_mem_drop hx)
          have hfieldcl : ∀ x ∈ cargs'.drop np, LBClosed x 0 :=
            fun x hx => LBClosed.mkApps_inv hcld x (List.mem_of_mem_drop hx)
          have hnbb := noBlock_mkApps
            (noBlock_mkLambdas (names := (alts'[cidx]'hcidxa).1)
              (hnb.2 _ (List.getElem_mem hcidxa))) hfieldnb
          have hclb := LBClosed.mkApps
            (LBClosed.mkLambdas (hcl.2 _ (List.getElem_mem hcidxa))) hfieldcl
          obtain ⟨t', vve, hEbranch, htrr, herr, hnbt', hclt'⟩ :=
            ihbranch htrbranch herbranch hnbb hclb
          -- (9) the constructor's field values are closed *values* — the bridge's proviso
          have hfieldval : ∀ x ∈ cargs'.drop np, WcbvEval E appliedFlags x x :=
            fun x hx => value_final (value_mkApps_construct_args _ rfl (eval_to_value hEd)
              x (List.mem_of_mem_drop hx))
          -- (10) fire the target ι rule, through the reversal bridge
          refine ⟨t', vve, ?_, htrr, herr, hnbt', hclt'⟩
          refine WcbvEval.iota (names := (alts'[cidx]'hcidxa).1)
            (body := (alts'[cidx]'hcidxa).2) rfl (hcasesenv hcases) hEd ?_ ?_ ?_
          · rw [List.getElem?_eq_getElem hcidxa]
          · rw [hdropl', hnames]
          · exact wcbvEval_mkApps_mkLambdas_substList (cargs'.drop np) _ _
              (by rw [hnames, hdropl']) hfieldval hfieldcl hEbranch
        · exact absurd hnbd hnbt
  | @proj S ctor cus cargs iid np nf i ar discr r hs hctor hnfs har hcargs hi
      hdiscr hlt hsel ihdiscr ihsel =>
      intro ve t htr her hnb hcl
      have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
      have htr₀ := htr
      -- (1) invert the erasure of the redex. `Erases.proj_inv` is total and two-way —
      --     `box` and `proj` are the only rules concluding at a `.proj` source — so no
      --     `proj_redex_inv` analogue of `iota_redex_inv` is needed: there is no spine
      --     arithmetic and no prefix-relevance side condition to thread.
      rcases her.proj_inv with ⟨veb, htrb, herbox, rfl⟩
        | ⟨iid', np', nf', discr', hs', hnfs', hi', hd, rfl⟩
      · -- the whole projection is irrelevant: `t = .box`
        obtain ⟨vve, htrr, hdef⟩ :=
          SEvalDataι_defeq henv hΔ hcon hiota hproj htr
            (.proj hs hctor hnfs har hcargs hi hdiscr hlt hsel)
        have herve : Erasable env Us.length Δ.toCtx ve := herbox.defeq henv hΓ
          (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrb htr)
        exact ⟨.box, vve, .box, htrr, .box htrr (herve.defeq henv hΓ hdef),
          trivial, trivial⟩
      · -- the model's `ProjectionInfo` is the source rule's own registration data
        obtain ⟨rfl, rfl⟩ : iid = iid' ∧ np = np' := by
          rw [hs] at hs'
          simp only [Option.some.injEq, Prod.mk.injEq] at hs'
          exact ⟨hs'.1, hs'.2⟩
        -- (2) evaluate the discriminant. This is where §2.6's de-opacification is
        --     cashed in: with `NoBlock (.proj p t) = True` the IH's argument would be
        --     unobtainable.
        obtain ⟨dve, htrd, _⟩ := htr.proj_inv
        rw [NoBlock_proj] at hnb
        rw [LBClosed_proj] at hcl
        obtain ⟨dt', dvv, hEd, htrdv, herdv, hnbd, hcld⟩ := ihdiscr htrd hd hnb hcl
        -- (3) shape the value: a non-erasable constructor spine at index `0`
        rcases Erases.ctor_spine_inv henv hΔ hctor (hcc hctor) cargs.length cargs rfl
            htrdv herdv with
          ⟨hercv, cargs', rfl, _⟩ | ⟨cargs', hclen, rfl, hccorr⟩ | hnbt
        · exact absurd hercv (informativeType_not_erasable henv hΔ
            (hrel.ctorValue hctor (.inr ⟨S, np, hs⟩) htrdv) htrdv)
        · -- (4) the selected field, on both sides. `ProjFieldsCoherent` is what puts
          --     the target index `np + i` in range: it decomposes the spine length
          --     `ar` the source rule pins as `np + nf`.
          obtain ⟨_, harc⟩ := hpcoh hs hnfs hctor
          have harnf : ar = np + nf := by
            rw [har] at harc; simpa using Option.some.inj harc
          have hlt' : np + i < cargs'.length := by omega
          have herfield : Erases env Us Γ Δ (cargs[np + i]'hlt) (cargs'[np + i]'hlt') :=
            hccorr (np + i) hlt'
          obtain ⟨sve, htrsel⟩ :=
            (trExprS_appSpine_inv cargs (.const ctor cus) dvv htrdv).2 (np + i) hlt
          obtain ⟨t', vve, hEfield, htrr, herr, hnbt', hclt'⟩ :=
            ihsel htrsel herfield
              (noBlock_mkApps_inv hnbd _ (List.getElem_mem hlt'))
              (LBClosed.mkApps_inv hcld _ (List.getElem_mem hlt'))
          -- (5) fire the target rule — the **non-block** `WcbvEval.proj`, which is the
          --     one `appliedFlags` runs (`with_constructor_as_block = false`).
          refine ⟨t', vve, ?_, htrr, herr, hnbt', hclt'⟩
          exact WcbvEval.proj (p := ⟨iid, np, i⟩) rfl (hprojenv hs) hEd
            (by simp [List.getElem?_eq_getElem hlt']) hEfield
        · exact absurd hnbd hnbt
  | @lit l r hev ih =>
      intro ve t htr her hnb hcl
      have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
      obtain ⟨hcll, htrC⟩ := TrExprS.lit_inv' htr
      rcases Erases.lit_inv her with ⟨veb, htrb, herbox, rfl⟩ | ⟨_, herC⟩
      · obtain ⟨vve, htrr, hdef⟩ := SEvalDataι_defeq henv hΔ hcon hiota hproj htr (.lit hev)
        have herve : Erasable env Us.length Δ.toCtx ve := herbox.defeq henv hΓ
          (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrb htr)
        exact ⟨.box, vve, .box, htrr, .box htrr (herve.defeq henv hΓ hdef),
          trivial, trivial⟩
      · -- source and target both step to the unfolding: the IH *is* the goal
        exact ih htrC herC hnb hcl

/-! ## Non-vacuity guards for the ι side conditions

Constructed witnesses for the side conditions this file introduces, at **two** pins:

* `gΓflat` — a genuinely registered *flat* inductive `Flat` (one nullary constructor `c`,
  no parameters, not propositional) with a `casesOn` head `con` at `discrPos = 1`, so
  none of the `Γ` maps is the all-`none` function and none of the guards is vacuous;
* `gΓfield` — the *field-carrying* pin (§"the second pin" below), at which
  `FlatCaseFields` provably **fails** and the same certificate block still holds. That
  pair is what makes the S4b lift checkable rather than merely asserted.

`IotaRelevant` is **not** guarded here: exhibiting it needs a `VEnv` in which every
translatable partial `casesOn` spine and every constructor value is informatively typed,
which at this pin runs into the same obstruction that already blocks an end-to-end guard
for `SEvalDataι_defeq` — `VEnv.WF` is unconstructible for a `pats`-carrying environment
upstream (`VEnv.Ordered` has no `addPat` clause; `addInduct_WF` is `sorry`). It is
recorded in the ι trust ledger (`SubjectReductionIota.lean`) instead. Note that its
statement *is* satisfiable: the translation premise on both clauses is exactly what makes
it so (see its docstring). -/

private def flatKn : Kername := rootKername "Flat"
private def flatIid : InductiveId := { mutualBlockName := flatKn, idx := 0 }
private def flatOIB : OneInductiveBody :=
  { name := "Flat", propositional := false, kelim := .IntoAny,
    ctors := [{ name := "c", nargs := 0 }], projs := [] }
private def flatE : GlobalDeclarations :=
  [(flatKn, .inductiveDecl { finite := .finite, npars := 0, bodies := [flatOIB] })]

/-- A `Γ` registering the nullary constructor `c` of `Flat` **and** a `casesOn` head
`con` for it, with the field-count list `[0]` and `discrPos = 1` (motive only). -/
private def gΓflat : ErasureCtx where
  inductives := fun _ => none
  constants := fun _ => default
  ctors := fun n => if n = `c then some (flatIid, 0) else none
  ctorArities := fun n => if n = `c then some 0 else none
  casesOns := fun n => if n = `con then some (flatIid, 0) else none
  ctorFields := fun _ => some [0]
  casesDiscrPos := fun n => if n = `con then some 1 else none

/-- The matching `IotaArities`: `numMotives = 1`, `numIndices = 0`, `numMinors = 1`. -/
private def gIAflat : IotaArities := fun n => if n = `con then some (1, 0, 1) else none

/-- One half of the S4b coverage measure: `FlatCaseFields` holds at a `Γ` that really
does register a `casesOn` (`gΓfield_not_flat` is the other half). -/
theorem gΓflat_flat : FlatCaseFields gΓflat := by
  intro con iid np nfs hcases hnfs j hj
  simp only [gΓflat] at hnfs
  obtain rfl : nfs = [0] := by simpa using hnfs.symm
  match j, hj with
  | 0, _ => rfl

/-- Non-vacuity: `ErasesEnvCasesι` fires — `Flat` is registered non-propositional, so the
target ι rule's guard is satisfied at the registered head. -/
theorem gΓflat_erasesEnvCasesι : ErasesEnvCasesι gΓflat flatE := by
  intro con iid numParams hcases
  by_cases h : con = `con
  · subst h; simp [gΓflat] at hcases
    obtain ⟨rfl, _⟩ := hcases
    rfl
  · simp [gΓflat, if_neg h] at hcases

/-- Non-vacuity: `CtorFieldsCoherent` holds at the flat `Γ` — `ctorArities c = 0`
decomposes as `npars 0 + nfs[0] 0`. -/
theorem gΓflat_ctorFieldsCoherent : CtorFieldsCoherent gΓflat := by
  intro con cn iid np cidx nfs hcases hnfs hctors
  by_cases h : cn = `c
  · subst h
    simp [gΓflat] at hctors
    obtain ⟨_, rfl⟩ := hctors
    by_cases hc2 : con = `con
    · subst hc2
      simp [gΓflat] at hcases
      obtain ⟨_, rfl⟩ := hcases
      simp only [gΓflat] at hnfs
      obtain rfl : nfs = [0] := by simpa using hnfs.symm
      exact ⟨by simp, by simp [gΓflat]⟩
    · simp [gΓflat, if_neg hc2] at hcases
  · simp [gΓflat, if_neg h] at hctors

/-- Non-vacuity: `IotaArityCoherent` holds at the flat `(Γ, ia)` pair —
`discrPos = 1 = np + nmot + nidx` and the constructor count `|[0]| = 1 = numMinors`. -/
theorem gΓflat_iotaArityCoherent : IotaArityCoherent gΓflat gIAflat := by
  intro con iid np nmot nidx nmin hcases hia
  by_cases h : con = `con
  · subst h
    simp [gΓflat, gIAflat] at hcases hia
    obtain ⟨rfl, rfl⟩ := hcases
    obtain ⟨rfl, rfl, rfl⟩ := hia
    exact ⟨rfl, [0], rfl, rfl⟩
  · simp [gΓflat, if_neg h] at hcases

/-- A concrete `E` binding one constant to the closed body `.box`. (`EnvErasureNonrec`'s
`gED` binds `.bvar 0`, which is *not* `LBClosed … 0` — the loose index is the whole point
of that guard — so `ClosedEnv` needs its own witness.) -/
private def gEcl : GlobalDeclarations := [(rootKername "c", .constantDecl ⟨some .box⟩)]

/-- Non-vacuity: `ClosedEnv` holds at a genuinely non-empty target environment. -/
theorem gEcl_closedEnv : ClosedEnv gEcl := by
  intro kn body h
  simp only [gEcl, LBTerm.envLookup] at h
  split at h
  · injection h with h; injection h with h; injection h with h
    obtain rfl : body = .box := (Option.some.inj h).symm
    trivial
  · exact absurd h (by simp)

/-! ### The second pin: a field-carrying `Γ`, outside `FlatCaseFields`

The pin the flat slice could not reach. `AC`/`mk` (`Semantics/Metatheory.lean`) is a
genuinely registered, non-propositional inductive with **one parameter and one field**,
so `ctorArities mk = npars 1 + nfields 1 = 2` decomposes non-degenerately and the
`casesOn` head sits at `discrPos = np + nmot + nidx = 1 + 1 + 0 = 2`. Every certificate
premise of `erases_correct_dataι` holds here exactly as at `gΓflat`, and
`gΓfield_not_flat` records that the old scope restriction does **not**.

What is *not* constructible at this pin is the same thing that is not constructible at
`gΓflat`: an end-to-end run of the simulation, which needs `IotaConsistent` (hence
`env.WF` for a `pats`-carrying `VEnv`, `sorry` upstream) and `IotaRelevant`. The ι step's
target half — the reversal bridge on a genuinely multi-field constructor — *is* guarded,
at `wcbvEval_mkApps_mkLambdas_substList_fires` (`IotaBridge.lean`), where a two-field
telescope β-reduces and the bridge turns that into the ι rule's own `substList` reduct. -/

/-- A field-carrying `Γ`: `AC.mk` as constructor `(acIid, 0)` of arity `2`, and an
`AC.casesOn` head `con` at `(acIid, 1)`, with field-count list `[1]` and `discrPos = 2`.
(The same shape as `EnvErasureNonrec`'s `gΓι`, re-declared because importing the shipping
bridge here would drag it into the forward simulation's dependency cone.) -/
private def gΓfield : ErasureCtx where
  inductives := fun _ => none
  constants := fun _ => default
  ctors := fun n => if n = `mk then some (acIid, 0) else none
  ctorArities := fun n => if n = `mk then some 2 else none
  casesOns := fun n => if n = `con then some (acIid, 1) else none
  ctorFields := fun _ => some [1]
  casesDiscrPos := fun n => if n = `con then some 2 else none

/-- The matching `IotaArities`: `numMotives = 1`, `numIndices = 0`, `numMinors = 1`. -/
private def gIAfield : IotaArities := fun n => if n = `con then some (1, 0, 1) else none

/-- **The lift is real**: the field-carrying pin is outside the old flat fragment, and
`erases_correct_dataι` covers it all the same. -/
theorem gΓfield_not_flat : ¬ FlatCaseFields gΓfield := by
  intro h
  have h0 := h (con := `con) (iid := acIid) (np := 1) (nfs := [1])
    (by simp [gΓfield]) rfl 0 (by simp)
  simp at h0

/-- Non-vacuity at the field-carrying pin: `ErasesEnvCasesι` fires — `AC` is registered
non-propositional. -/
theorem gΓfield_erasesEnvCasesι : ErasesEnvCasesι gΓfield acΓ := by
  intro con iid numParams hcases
  by_cases h : con = `con
  · subst h
    simp only [gΓfield] at hcases
    obtain ⟨rfl, _⟩ := hcases
    rfl
  · simp [gΓfield, if_neg h] at hcases

/-- Non-vacuity at the field-carrying pin: `CtorFieldsCoherent` — `ctorArities mk = 2`
decomposes as `npars 1 + nfs[0] 1`, i.e. with a **non-zero** field count. -/
theorem gΓfield_ctorFieldsCoherent : CtorFieldsCoherent gΓfield := by
  intro con cn iid np cidx nfs hcases hnfs hctors
  by_cases h : cn = `mk
  · subst h
    simp only [gΓfield] at hctors
    obtain ⟨_, rfl⟩ := hctors
    by_cases hc2 : con = `con
    · subst hc2
      simp only [gΓfield] at hcases
      obtain ⟨_, rfl⟩ := hcases
      obtain rfl : nfs = [1] := (Option.some.inj hnfs).symm
      exact ⟨by simp, by simp [gΓfield]⟩
    · simp [gΓfield, if_neg hc2] at hcases
  · simp [gΓfield, if_neg h] at hctors

/-- Non-vacuity at the field-carrying pin: `IotaArityCoherent` — `discrPos = 2 =
np + nmot + nidx` with `np = 1`, and the constructor count `|[1]| = 1 = numMinors`. -/
theorem gΓfield_iotaArityCoherent : IotaArityCoherent gΓfield gIAfield := by
  intro con iid np nmot nidx nmin hcases hia
  by_cases h : con = `con
  · subst h
    simp only [gΓfield, gIAfield] at hcases hia
    obtain ⟨rfl, rfl⟩ := hcases
    obtain ⟨rfl, rfl, rfl⟩ := hia
    exact ⟨by simp [gΓfield], [1], rfl, rfl⟩
  · simp [gΓfield, if_neg h] at hcases

/-- Non-vacuity at the field-carrying pin: the constructor/`casesOn` disjointness `hcc`. -/
theorem gΓfield_cc {cn : Name} {iid : InductiveId} {cidx : Nat} :
    gΓfield.ctors cn = some (iid, cidx) → gΓfield.casesOns cn = none := by
  intro hc
  by_cases h : cn = `mk
  · subst h; simp [gΓfield]
  · simp [gΓfield, if_neg h] at hc

/-- **The certificate block of `erases_correct_dataι`, at a field-carrying `Γ`.** Every
`Γ`/`E`-level side condition of the simulation holds at `(gΓfield, gIAfield, acΓ)` —
which `FlatCaseFields` does not. -/
theorem gΓfield_certificates :
    ErasesEnvCasesι gΓfield acΓ ∧ CtorFieldsCoherent gΓfield ∧
      IotaArityCoherent gΓfield gIAfield ∧ ¬ FlatCaseFields gΓfield ∧
      (∀ {cn : Name} {iid : InductiveId} {cidx : Nat},
        gΓfield.ctors cn = some (iid, cidx) → gΓfield.casesOns cn = none) :=
  ⟨gΓfield_erasesEnvCasesι, gΓfield_ctorFieldsCoherent, gΓfield_iotaArityCoherent,
    gΓfield_not_flat, gΓfield_cc⟩

/-! ## Non-vacuity for the projection step (projection round, slices P5–P7)

The round's own guards, all at **one** fixture — `Γproj` (`Erases.lean`) on the source
side and `acΓ` (`Semantics/Metatheory.lean`) on the target, linked by `projInd = acIid`
(`rfl`). That link is what the a7c8ebc fixture merge bought: the `ProjectionInfo` the
model builds is keyed on the `InductiveId` the target environment actually registers, so
the two halves are about the same `AC` and not about a lookalike.

`AC` is one parameter and one field, so `np + i = 1 + 0 = 1` is the *second* spine
position: a rule that confused `paramCount` with `fieldIdx` would select the parameter
and every guard below would fail. To make that visible the parameter and the field are
given **different** erasures — the parameter is the nullary head `AC.mk`, the field is
`AC.mk` applied to one argument — so both the source selection and the target selection
are observable.

The one thing not constructible here is the same one the ι round records: an actual
call to `erases_correct_dataι`, which needs `env.WF` for a `pats`-carrying `VEnv`
(`sorry` upstream) plus `TrExprS` witnesses. So the guard is the theorem's **conclusion**,
built by hand at a projection redex: `proj_step_fires` below is `erases_correct_dataι`'s
output tuple minus its two `TrExprS` components. -/

/-- The source parameter: the structure's own constructor, nullary. -/
private def projSrcParam : Expr := .const `AC.mk []
/-- The source field: the same constructor applied to one argument — a *different* term
from the parameter, and one with a different erasure. -/
private def projSrcField : Expr := .app (.const `AC.mk []) (.const `AC.mk [])
/-- The discriminant: `AC.mk` saturated at its parameter and its field. -/
private def projSrcSpine : Expr :=
  [projSrcParam, projSrcField].foldl Expr.app (.const `AC.mk [])

private def projTgtParam : LBTerm := .construct projInd 0 []
private def projTgtField : LBTerm := .app projTgtParam projTgtParam
private def projTgtSpine : LBTerm := .app (.app projTgtParam projTgtParam) projTgtField

/-- The parameter is a source value: a constructor spine at arity `0 ≤ 2`. -/
private theorem projSrc_param_eval :
    SEvalDataι Γproj (fun _ => none) (fun _ => none) projSrcParam projSrcParam := by
  have h : projSrcParam = ([] : List Expr).foldl Expr.app (.const `AC.mk []) := rfl
  rw [h]
  exact .ctor_val Γproj_ctors Γproj_arity (by simp) rfl (fun i h => absurd h (by simp))

/-- …and so is the field, at arity `1 ≤ 2`. -/
private theorem projSrc_field_eval :
    SEvalDataι Γproj (fun _ => none) (fun _ => none) projSrcField projSrcField := by
  have h : projSrcField = ([projSrcParam] : List Expr).foldl Expr.app (.const `AC.mk []) := rfl
  rw [h]
  exact .ctor_val Γproj_ctors Γproj_arity (by simp) rfl
    (fun i hi => by match i, hi with | 0, _ => exact projSrc_param_eval)

/-- The discriminant evaluates to itself — a **saturated** spine, `2 = 1 + 1`, which is
what makes the projection's selection total. -/
private theorem projSrc_spine_eval :
    SEvalDataι Γproj (fun _ => none) (fun _ => none) projSrcSpine projSrcSpine :=
  .ctor_val Γproj_ctors Γproj_arity (by simp) rfl
    (fun i hi => by
      match i, hi with
      | 0, _ => exact projSrc_param_eval
      | 1, _ => exact projSrc_field_eval)

/-- **`SEvalDataι.proj` fires** (slice P5): field `0` of a saturated `AC.mk` spine
evaluates to the spine's position `np + i = 1`, i.e. the **field** and not the
parameter. -/
theorem sEvalDataι_proj_fires :
    SEvalDataι Γproj (fun _ => none) (fun _ => none)
      (.proj `AC 0 projSrcSpine) projSrcField :=
  .proj (cargs := [projSrcParam, projSrcField])
    Γproj_projs Γproj_ctors Γproj_ctorFields Γproj_arity (by simp) (by omega)
    projSrc_spine_eval (by simp) projSrc_field_eval

private theorem projTgt_param_eval : WcbvEval acΓ appliedFlags projTgtParam projTgtParam :=
  .construct_atom rfl rfl

private theorem projTgt_field_eval : WcbvEval acΓ appliedFlags projTgtField projTgtField :=
  .construct_app (args := []) (ar := 2) rfl projTgt_param_eval rfl (by decide)
    projTgt_param_eval

private theorem projTgt_spine_eval : WcbvEval acΓ appliedFlags projTgtSpine projTgtSpine :=
  .construct_app (args := [projTgtParam]) (ar := 2) rfl
    (.construct_app (args := []) (ar := 2) rfl projTgt_param_eval rfl (by decide)
      projTgt_param_eval)
    rfl (by decide) projTgt_field_eval

/-- **`WcbvEval.proj` fires at `appliedFlags`** (slice P7) — the guard the design records
as genuinely new: `LBOptimize_correct`'s non-block `proj` arm is *vacuous*
(`simp [defaultFlags] at hb`), so nothing in the tree had ever exercised this rule at the
flavour the data development runs. It selects `args[paramCount + fieldIdx] = args[1]`,
the field, on a two-element applied-form spine of a non-propositional inductive. -/
theorem wcbvEval_proj_fires :
    WcbvEval acΓ appliedFlags (.proj ⟨projInd, 1, 0⟩ projTgtSpine) projTgtField :=
  .proj (args := [projTgtParam, projTgtField]) rfl rfl projTgt_spine_eval rfl
    projTgt_field_eval

private theorem projSrc_param_erases {env : VEnv} {Us : List Name} {Δ : VLCtx} :
    Erases env Us Γproj Δ projSrcParam projTgtParam :=
  .ctor_head `AC.mk [] projInd 0 Γproj_ctors

private theorem projSrc_field_erases {env : VEnv} {Us : List Name} {Δ : VLCtx} :
    Erases env Us Γproj Δ projSrcField projTgtField :=
  .app projSrc_param_erases projSrc_param_erases

private theorem projSrc_spine_erases {env : VEnv} {Us : List Name} {Δ : VLCtx} :
    Erases env Us Γproj Δ projSrcSpine projTgtSpine :=
  .app (.app projSrc_param_erases projSrc_param_erases) projSrc_field_erases

/-- **The projection step, end to end** (slices P5–P7). At `Γproj`/`acΓ`, on one and the
same projection redex: the source rule fires, the redex erases to a `.proj` node over the
erased discriminant, that node is applied-form and closed, the **non-block** target rule
steps it, and the target it reaches is an erasure of the source value.

That is `erases_correct_dataι`'s conclusion tuple, minus the two `TrExprS` components —
which are exactly the parts that need a `VEnv` with `env.WF`, unconstructible at this pin
for the same upstream reason the ι round records (`VEnv.Ordered` has no `addPat` clause;
`addInduct_WF` is `sorry`). Every *other* component of the simulation's output is
exhibited here, at a projection, non-degenerately: the value reached is the field
(`AC.mk` applied once), not the parameter (`AC.mk` nullary). -/
theorem proj_step_fires {env : VEnv} (Us : List Name) (Δ : VLCtx) :
    SEvalDataι Γproj (fun _ => none) (fun _ => none)
        (.proj `AC 0 projSrcSpine) projSrcField ∧
      Erases env Us Γproj Δ (.proj `AC 0 projSrcSpine)
        (.proj ⟨projInd, 1, 0⟩ projTgtSpine) ∧
      NoBlock (.proj ⟨projInd, 1, 0⟩ projTgtSpine) ∧
      LBClosed (.proj ⟨projInd, 1, 0⟩ projTgtSpine) 0 ∧
      WcbvEval acΓ appliedFlags (.proj ⟨projInd, 1, 0⟩ projTgtSpine) projTgtField ∧
      Erases env Us Γproj Δ projSrcField projTgtField ∧
      NoBlock projTgtField ∧ LBClosed projTgtField 0 :=
  ⟨sEvalDataι_proj_fires,
    .proj `AC 0 projInd 1 1 Γproj_projs Γproj_ctorFields (by omega) projSrc_spine_erases,
    by simp [projTgtSpine, projTgtParam, projTgtField, NoBlock],
    by simp [projTgtSpine, projTgtParam, projTgtField, LBClosedArgs],
    wcbvEval_proj_fires, projSrc_field_erases,
    by simp [projTgtParam, projTgtField, NoBlock],
    by simp [projTgtParam, projTgtField, LBClosedArgs]⟩

/-- **The two halves are about the same inductive.** The `InductiveId` the model puts in
the emitted `ProjectionInfo` (`Γproj`'s `projInd`) is the one `acΓ` registers, so
`wcbvEval_proj_fires`' non-propositionality premise is delivered at the node
`sEvalDataι_proj_fires`/`Erases.proj` actually build. -/
theorem projInd_eq_acIid : projInd = acIid := rfl

/-- **`ErasesEnvProjsι` fires** at the merged fixture — the thin env premise the
simulation takes, at a genuinely registered non-propositional structure. -/
theorem Γproj_erasesEnvProjsι : ErasesEnvProjsι Γproj acΓ := by
  intro S iid np hs
  by_cases h : S = `AC
  · subst h; simp only [Γproj] at hs; obtain ⟨rfl, _⟩ := hs; rfl
  · simp [Γproj, if_neg h] at hs

/-- **Negative polarity, and the reason the vacuity trio is honest**: at a `Γ` that
registers no structure the projection premises hold *because nothing satisfies them*, and
`Γproj` is a `Γ` at which they do not. Together with `Γproj_erasesEnvProjsι` this is the
pair that keeps `projConsistent_of_noProjs` and friends from being the whole story. -/
theorem Γproj_projs_ne_bot : Γproj.projs ≠ fun _ => none := by
  intro h
  have := congrFun h `AC
  rw [Γproj_projs] at this
  exact absurd this (by simp)

end LeanToLambdaBox
