import LeanToLambdaBox.SubjectReductionFull
import LeanToLambdaBox.SourceEvalData
import LeanToLambdaBox.ErasesCorrectData
import LeanToLambdaBox.FirstOrder
import LeanToLambdaBox.IotaDischarge
import LeanToLambdaBox.ProjPattern
import LeanToLambdaBox.ProjDischarge

/-!
# Subject reduction and forward simulation for the ι (`casesOn`) fragment — C2/C3

`SEvalDataι` (`SourceEvalData.lean`) is the β + δ + saturated-constructor + **corrected
ι** source evaluation. This file adds the two ι theorems:

* `SEvalDataι_defeq` — subject-reduction-as-defeq over `SEvalDataι` (C2), mirroring
  `SEvalβζδ_defeq` for the non-ι rules and discharging the ι case **only** through the
  `IotaConsistent` hypothesis; and
* the ι-relevance side conditions `IotaRelevant` and the C3 analysis that motivates
  them. The ι-reduct correspondence itself — the source ι reduct (the minor applied to
  the constructor fields *in order*, `(cargs.drop np).foldl Expr.app (minors[cidx])`)
  against the target `iota_red` (the field-substituted alternative body, in **reverse**:
  `substList ((args.drop np).reverse) body`) — is the β-chain ↔ reversing-`iota_red`
  bridge `wcbvEval_mkApps_mkLambdas_substList` (`IotaBridge.lean`), consumed by
  `erases_correct_dataι`.

## The ι trust ledger (REQUIRED, precise)

`IotaConsistent env Us Γ ia` (defined in `SourceEvalData.lean`) is **no longer an
undischarged hypothesis**. `iotaConsistent_of_shape` (`IotaDischarge.lean`) derives it,
and `SEvalDataι_defeq_of_shape` below is `SEvalDataι_defeq` with that derivation
plugged in. `IotaConsistent` survives as a *premise* of `SEvalDataι_defeq` purely as an
**interface**: it keeps the kernel-environment parameters (`safety`, `kenv`) out of a
subject-reduction statement about `VEnv`s, and lets a future `TrEnv`-based discharge drop
in without touching consumers. (Same precedent as `ErasesEnvCtor`, which stays a premise
of `erases_correct_data` even though `erasesEnvCtor_of_registeredCtors` proves it.)

What that leaves. The ι fragment now rests on exactly three named things, none of them
an axiom of ours:

* **`PatsIotaSpec`** (`IotaPattern.lean`) — the fork's *strengthened* rule lookup
  (`pats_iota'`). A `Prop` structure, and no longer an obligation: `PatsIotaSpec.of_trEnv`
  discharges it for every `TrEnv`-translated environment. It stays a premise here for the
  same reason `ErasesEnvCtor` does — it is the interface, not the assumption.
* **`IotaShape`** (`IotaDischarge.lean`) — the per-`casesOn` kernel-shape certificate:
  two kernel lookups plus closed `Expr` equations, `rfl`-checkable per inductive. It is
  **not** derivable from lean4lean by that development's own admission (`VInductDecl.WF`'s
  docstring says it does not pin the recursor/rule shape to the one `addInduct` reduces
  with). Its two equations are exercised by the constructed guards
  `betaN_casesOn_guard` / `betaN_ruleTemplate_guard` (`IotaDischarge.lean`), at
  `np = nmot = nmin = nidx = nfields = 1` so that neither the argument reordering nor the
  `take`/`drop` slicing is degenerate.
* **`IotaRelevant`** (below) — a *model-over-approximation guard* of the same class as
  `NoBlock`, not a typing assumption: it excludes the two `Erases` derivations that the
  relation permits, the shipping eraser never emits, and under which the target `.case` is
  provably stuck (see its docstring). Discharged for free in the first-order world by
  `FirstOrderValue`'s `info` field.

plus lean4lean's own pre-existing `sorry` frontier, which the whole development already
inherits. [Updated at the `fee3ada` re-pin, 2026-08-27: this used to lead with `TrProj`.
That item is retired — `TrProj` has a real definition upstream. The frontier this file
actually inherits is the ι one (`forallE_inv'`/`sort_inv'`/`addInduct_WF`, the `IsDefEq`
`pat` cases) together with unique typing (`TrExprS.uniq` → `TrProj.uniq`, `IsDefEq.uniqU`).]

There is **no** "sole exception" left on non-vacuity: `envι_iota_fires`
(`IotaDischarge.lean`) shows the ι machinery fires and yields real content on a
`VEnv.addPat`-built environment, the two `betaN` guards show `IotaShape`'s equations are
satisfiable, and the coherence/relevance predicates introduced by ι Task 3 carry their own
constructed guards. What is *not* constructible at this pin is a guard instantiating
`iotaConsistent_of_shape` (or `SEvalDataι_defeq`) end to end, because `VEnv.WF` is
unconstructible for a `pats`-carrying environment upstream (`VEnv.Ordered` has no `addPat`
clause; `addInduct_WF` is `sorry`) — so the guards stay at the level of the halves, which
is documented at each of them.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-! ## C2 — subject reduction as definitional equality over `SEvalDataι`. -/

/-- **The ι redex is definitionally equal to its source reduct, and the reduct is
translatable.** Two steps: the congruence that replaces the discriminant by its
constructor-spine value inside the outer spine (`SEvalβζδ_defeq_spine` used as pure head
congruence), then one application of `IotaConsistent`.

The discriminant's subject reduction arrives as the *function* `hdiscr` rather than as an
`SEvalDataι` derivation, so this lemma is usable both from `SEvalDataι_defeq`'s own ι arm
(passing its induction hypothesis) and from `erases_correct_dataι`'s ι case (passing
`SEvalDataι_defeq` itself) — with no circularity in either direction. -/
theorem SEvalDataι_iota_reduct {env : VEnv} (henv : env.WF) {Us : List Name} {Δ : VLCtx}
    (hΔ : VLCtx.WF env Us.length Δ) {Γ : ErasureCtx} {ia : IotaArities}
    (hiota : IotaConsistent env Us Γ ia)
    {con ctor : Name} {us cus : List Level} {pre minors cargs : List Expr}
    {discr : Expr} {iid : InductiveId} {np cidx nmot nidx nmin ar : Nat} {ve : VExpr}
    (hcases : Γ.casesOns con = some (iid, np))
    (hctor : Γ.ctors ctor = some (iid, cidx))
    (hia : ia con = some (nmot, nidx, nmin))
    (har : Γ.ctorArities ctor = some ar)
    (hpre : pre.length = np + nmot + nidx) (hmin : minors.length = nmin)
    (hcargs : cargs.length = ar) (hidx : cidx < minors.length)
    (hdiscr : ∀ {dve : VExpr}, TrExprS env Us Δ discr dve →
      ∃ cve, TrExprS env Us Δ (cargs.foldl Expr.app (.const ctor cus)) cve ∧
        env.IsDefEqU Us.length Δ.toCtx dve cve)
    (htr : TrExprS env Us Δ
      ((discr :: minors).foldl Expr.app (pre.foldl Expr.app (.const con us))) ve) :
    ∃ bve, TrExprS env Us Δ ((cargs.drop np).foldl Expr.app (minors[cidx]'hidx)) bve ∧
      env.IsDefEqU Us.length Δ.toCtx ve bve := by
  have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
  obtain ⟨hveHEAD, htrHEAD⟩ := TrExprS_spine_head (discr :: minors) htr
  -- congruence: replace `discr` by its constructor-spine value inside the outer spine
  obtain ⟨vve1, htr_replaced, hdef1⟩ :=
    SEvalβζδ_defeq_spine henv hΔ
      (fun e v => ∀ {ev}, TrExprS env Us Δ e ev →
        ∃ vv, TrExprS env Us Δ v vv ∧ env.IsDefEqU Us.length Δ.toCtx ev vv)
      (fun htr p => p htr)
      (discr :: minors).length (discr :: minors)
      ((cargs.foldl Expr.app (.const ctor cus)) :: minors)
      (pre.foldl Expr.app (.const con us)) (pre.foldl Expr.app (.const con us))
      hveHEAD hveHEAD rfl (by simp) htrHEAD htrHEAD
      (VEnv.IsDefEqU.refl (htrHEAD.wf henv.ordered hΔ))
      (fun i h h2 => by
        cases i with
        | zero => exact fun htr => hdiscr htr
        | succ j => exact fun htr => ⟨_, htr, VEnv.IsDefEqU.refl (htr.wf henv.ordered hΔ)⟩)
      htr
  -- IotaConsistent: the replaced casesOn spine is defeq to the branch reduct
  obtain ⟨bve, htr_branch, hdef2⟩ :=
    hiota hΔ hcases hctor hia har hpre hmin hcargs hidx htr_replaced
  exact ⟨bve, htr_branch, VEnv.IsDefEqU.trans henv hΓ hdef1 hdef2⟩

/-- **Subject reduction as definitional equality (β + δ + saturated constructors + ι).**

If `e` translates to `ve` and `e` evaluates to `v` under `SEvalDataι`, then `v` translates
to some `vve` definitionally equal to `ve`. The λ/β/δ/ctor cases reuse the reasoning of
`SEvalβζδ_defeq` (`SEvalβζδ_defeq_spine` for the constructor spine); the ι case is
discharged **only** via the `IotaConsistent` hypothesis `hiota` — the pinned fork's ι rule
(`IsDefEq.pat`) exists but is not yet chainable into a concrete instance (see the module
docstring). `IotaConsistent` stays a hypothesis, never an axiom.

**The δ premise is the universe-aware one since slice Γ-U4**: `SEnvConsistentL env Us
Γ.lparams Esrc`, matching `SEvalDataι.delta`'s unfolding at
`body.instantiateLevelParams (Γ.lparams n) us`. The δ *case* did not move a character —
the restated premise hands back the `TrExprS` of exactly the expression the restated rule
recursed on, which is the whole reason the two had to be repaired together. A caller with
the old monomorphic premise passes `hcon.toL rfl`. -/
theorem SEvalDataι_defeq {env : VEnv} (henv : env.WF) {Us : List Name} {Δ : VLCtx}
    (hΔ : VLCtx.WF env Us.length Δ) {Γ : ErasureCtx} {ia : IotaArities} {Esrc : SEnv}
    (hcon : SEnvConsistentL env Us Γ.lparams Esrc) (hiota : IotaConsistent env Us Γ ia)
    (hproj : ProjConsistent env Us Γ)
    {e v : Expr} {ve : VExpr}
    (htr : TrExprS env Us Δ e ve)
    (hev : SEvalDataι Γ ia Esrc e v) :
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
  | @delta n us body r hunf hbodyev ihbody =>
      obtain ⟨bve, htrb, hdefeq⟩ := hcon hunf htr
      obtain ⟨vve, htrr, hrd⟩ := ihbody hΔ htrb
      exact ⟨vve, htrr, VEnv.IsDefEqU.trans henv hΔ.toCtx hdefeq hrd⟩
  | @ctor_val cn us iid cidx ar args vs hc har hsat hl hargs ihargs =>
      obtain ⟨hve, htrhead⟩ := TrExprS_spine_head args htr
      refine SEvalβζδ_defeq_spine henv hΔ
        (fun e v => ∀ {ev}, TrExprS env Us Δ e ev →
          ∃ vv, TrExprS env Us Δ v vv ∧ env.IsDefEqU Us.length Δ.toCtx ev vv)
        (fun htr p => p htr)
        args.length args vs (Expr.const cn us) (Expr.const cn us) hve hve rfl hl.symm
        htrhead htrhead (VEnv.IsDefEqU.refl (htrhead.wf henv.ordered hΔ))
        (fun i h h2 => ihargs i h hΔ) htr
  | @iota con us cus pre minors cargs discr ctor iid np cidx nmot nidx nmin ar r
        hcases hctor hia har hpre hmin hcargs hdiscr hidx hbranch ihdiscr ihbranch =>
      obtain ⟨bve, htr_branch, hdef12⟩ :=
        SEvalDataι_iota_reduct henv hΔ hiota hcases hctor hia har hpre hmin hcargs hidx
          (fun htr => ihdiscr hΔ htr) htr
      obtain ⟨rvv, htr_r, hdef3⟩ := ihbranch hΔ htr_branch
      exact ⟨rvv, htr_r, VEnv.IsDefEqU.trans henv hΔ.toCtx hdef12 hdef3⟩
  | @proj S ctor cus cargs iid np nf i ar discr r hs hctor hnfs har hcargs hi
        hdiscr hlt hsel ihdiscr ihsel =>
      -- One application of `ProjConsistent`, with the discriminant's own subject
      -- reduction handed over as a function: the interface takes its discriminant up to
      -- definitional equality, so no `TrProj` congruence is needed (see its docstring).
      obtain ⟨fve, htr_f, hd₂⟩ :=
        hproj hΔ hs hctor hnfs har hcargs hi hlt htr (fun htrd => ihdiscr hΔ htrd)
      obtain ⟨rvv, htr_r, hd₃⟩ := ihsel hΔ htr_f
      exact ⟨rvv, htr_r, VEnv.IsDefEqU.trans henv hΔ.toCtx hd₂ hd₃⟩
  | @lit l r hev ih =>
      -- Free: `TrExprS.lit` gives the literal and its unfolding the *same* `VExpr`.
      cases htr with | lit _ htrC => exact ih hΔ htrC

/-- **`SEvalDataι_defeq`, with `IotaConsistent` discharged.** The ι premise is no longer
assumed: it is derived from the fork's rule lookup (`PatsIotaSpec`), the δ facts the
theorem already carries (`SEnvConsistent`), and the per-`casesOn` kernel shape
certificate (`IotaShape`) — see `IotaDischarge.lean`.

`SEvalDataι_defeq`'s own signature is deliberately left byte-identical: `IotaConsistent`
is the *interface*, `PatsIotaSpec + IotaShape` is one (currently the only)
*implementation*, and threading `safety`/`kenv` through every downstream ι statement
would pollute them with kernel-environment data they never use.

Since the projection round (slice P6) the same treatment covers `ProjConsistent`: it is
discharged here by `projConsistent_of_coh` (`ProjDischarge.lean`) from the upstream
interface `ProjDefeqSpec`, the constructor agreement `ProjCtorAgree` — the link
`ProjShape` provably cannot supply, see that module's docstring — and the registration
fact `ProjFieldsCoherent`. Since the `b6a5a38` re-pin the middle one is no longer a bare
premise: `projCtorAgree_of_trEnv` derives it from a `TrEnv` plus a `kenv`-side
certificate, on upstream's `TrEnv.pats_iota_inv`. `ProjDefeqSpec` is the one that stays,
its statement corrected upstream and its proof still deferred.

**`hlp` is new at slice Γ-U4, and it is the honest cost of the discharge route.** The
general theorem above takes the universe-aware `SEnvConsistentL`; this one takes the
monomorphic `SEnvConsistent`, because `iotaConsistent_of_shape` δ-unfolds the `casesOn`
head and then reasons about the *uninstantiated* value (`IotaShape.shape`'s `hunfold` is
stated there). So the ι discharge route is available exactly on a universe-monomorphic
`Γ` — which every `ErasureCtx` on a capstone path is, the column's default, so `hlp` is
`rfl` at every call site (`ErasesDeltaL.ΓPolyδ` is the one that is not, and it is a guard
fixture rather than a capstone). Recorded here rather than buried: a `casesOn` is
universe-polymorphic in the real kernel, and lifting this premise means restating
`IotaShape` at the instantiated recursor value. -/
theorem SEvalDataι_defeq_of_shape {safety : DefinitionSafety} {kenv : Lean.Kernel.Environment}
    {env : VEnv} (henv : env.WF) {Us : List Name} {Δ : VLCtx}
    (hΔ : VLCtx.WF env Us.length Δ) {Γ : ErasureCtx} {ia : IotaArities} {Esrc : SEnv}
    (hspec : PatsIotaSpec safety kenv env)
    (hcon : SEnvConsistent env Us Esrc)
    (hlp : Γ.lparams = fun _ => [])
    (hshape : IotaShape safety kenv Γ ia Esrc)
    (hpspec : ProjDefeqSpec safety kenv env)
    (hpagree : ProjCtorAgree env Γ)
    (hpcoh : ProjFieldsCoherent Γ)
    {e v : Expr} {ve : VExpr}
    (htr : TrExprS env Us Δ e ve)
    (hev : SEvalDataι Γ ia Esrc e v) :
    ∃ vve, TrExprS env Us Δ v vve ∧ env.IsDefEqU Us.length Δ.toCtx ve vve :=
  SEvalDataι_defeq henv hΔ (hcon.toL hlp) (iotaConsistent_of_shape henv hspec hcon hshape)
    (projConsistent_of_coh henv hpspec hpagree hpcoh) htr hev

/-! ## ι-redex relevance — the two side conditions the model needs

Two `Erases` derivations that the relation permits, the shipping eraser never emits, and
that leave the target **stuck** — so the ι forward simulation is *false* without excluding
them, in the same way (one level down) as the C3 counterexample recorded below:

1. **Boxed proper prefix of the redex.** `Erases.app (Erases.box …) …` over a prefix of
   the `casesOn` spine gives `t = mkApps .box args'` with `args' ≠ []`. Such a `t`
   evaluates only if *every* element of `args'` evaluates — but the ι rule evaluates
   neither the dropped prefix `pre` (params/motive/indices) nor the minors, so no IH
   supplies those evaluations. This is structural: `SEvalDataι.iota` is the first rule in
   the development carrying source subterms it does not evaluate (`beta` evaluates its
   argument, `ctor_val` all of them).
2. **Boxed scrutinee value.** Inverting the discriminant's *value* can return the
   box-headed shape, i.e. the constructor value is `Erasable`. Then `discr'` evaluates to
   `box`, and `WcbvEval` has no rule for a `.case` on `box` except `iota_sing`, which
   needs `isPropositionalInductive = true`. Stuck.

Both say "the eliminated data is irrelevant", so they are stated *positively* through
`InformativeType` and consumed via `informativeType_not_erasable` (`FirstOrder.lean`). -/

/-- **ι-redex relevance.** Neither a *partial* application of a registered `casesOn` head
(fewer arguments than one full ι redex), nor a constructor value of an inductive that some
registered `casesOn` eliminates, is irrelevant.

Both clauses are **false in general** (a `casesOn` into `Prop` is itself a proof; a `Prop`
inductive's constructors are proofs) and **true throughout the data fragment**, which is
why they are premises rather than lemmas. They exclude precisely the `Erases` derivations
that box a proper prefix of an ι redex, or box its scrutinee — derivations the shipping
`visitCases` never emits (it boxes the whole application or none of it) but that the
relation permits, and under which the target `.case` is stuck. In the first-order
composition both clauses are supplied by `FirstOrderValue`'s `info` field.

This is a *model-over-approximation guard*, the ι analogue of the `NoBlock` premise — not
a typing assumption. It belongs in the trust ledger beside `IotaShape`/`PatsIotaSpec`.

**Both clauses are guarded by a translation premise, and that is not cosmetic.** Without
it the structure quantifies over *arbitrary* `args : List Expr`, including terms with no
`TrExprS` derivation at all (`.bvar 999` at `Δ = []`); `InformativeType` exhibits a
translation, so it is false for those, so the whole structure would be **unsatisfiable at
every `Γ` that registers a `casesOn`** — which would make `erases_correct_dataι`
vacuously true exactly on the environments it is about. The simulation only ever needs
these facts for spines it already has a `TrExprS` for (the redex's own prefixes, and the
scrutinee's evaluated value), so the premise costs nothing at the use sites. -/
structure IotaRelevant (env : VEnv) (Us : List Name) (Γ : ErasureCtx) : Prop where
  partialCases : ∀ {Δ : VLCtx} {con : Name} {us : List Level} {iid : InductiveId}
      {np dp : Nat} {nfs : List Nat} {args : List Expr} {vk : VExpr},
    Γ.casesOns con = some (iid, np) → Γ.casesDiscrPos con = some dp →
    Γ.ctorFields iid = some nfs → args.length < dp + 1 + nfs.length →
    TrExprS env Us Δ (args.foldl Expr.app (.const con us)) vk →
    InformativeType env Us Δ (args.foldl Expr.app (.const con us))
  /-- A constructor value of an inductive that some registered eliminator consumes is
  not irrelevant. The eliminator is a `casesOn` (ι) **or** a projection (projection
  round, slice P7): `.proj S i e` has no proper application prefix for the relation to
  box, so the `partialCases` clause has no projection analogue and this disjunction is
  the *whole* of what the projection simulation needs from `IotaRelevant`. Widening the
  hypothesis rather than adding a structure keeps the field count at two and leaves
  every `IotaRelevant` **consumer** stronger, not weaker; nothing in the tree
  constructs one, so there are no discharge sites to repair. -/
  ctorValue : ∀ {Δ : VLCtx} {cn : Name} {us : List Level} {iid : InductiveId}
      {cidx : Nat} {args : List Expr} {vk : VExpr},
    Γ.ctors cn = some (iid, cidx) →
    ((∃ con np, Γ.casesOns con = some (iid, np)) ∨
      (∃ S np, Γ.projs S = some (iid, np))) →
    TrExprS env Us Δ (args.foldl Expr.app (.const cn us)) vk →
    InformativeType env Us Δ (args.foldl Expr.app (.const cn us))

/-! ## C3 — the ι forward simulation: a raised implementation finding

**Status: fixed, and the simulation is proved.** `Erases.cases` now
carries three arity pins — `hpre` (`Γ.casesDiscrPos con = some pre.length`), `hnfs` +
`hnlen` (one alternative per constructor, from `Γ.ctorFields`) and `harity` (alternative
`j` binds exactly constructor `j`'s fields) — which make the model's parse of a `casesOn`
spine coincide with `visitCasesEtaGo`'s. Note that a *third* pin beyond the two identified
below was required: without `hpre` the counterexample survives in shifted form, because an
**over-applied** `casesOn` can be re-parsed with the first minor as the discriminant
(`pre = [motive, discr]`, `minors = [min₁, min₂, …]`), again yielding a `.case` on a
`.lambda` — stuck, since `WcbvEval` has no `case_cong` rule. The analysis below is kept as
the record of *why* the three pins exist.

The ι forward simulation itself is `erases_correct_dataι` (`ErasesCorrectIota.lean`),
proved for constructors of **any** arity: the shipping bridge's `Supported.casesApp`
(λ-telescope minors, T4b), the two-stage `IotaShape` certificate (T3g) and the reversal
bridge (`IotaBridge.lean`) all cover field-carrying constructors. Three further
obstructions surfaced while proving it, all of them recorded on the declarations that
carry them:

* **`NoBlock`/`NoFix` were opaque on `.case`** (a `| _ => True` catch-all), so inverting a
  target `.case` could not deliver `NoBlock discr'` to the discriminant IH. Both now
  traverse `.case`; see `Erases.lean` / `ErasesCorrectData.lean`.
* **The β-chain ↔ reversing-`iota_red` bridge needs de-Bruijn closedness.** Applying an
  alternative's λ-telescope to the fields *in order* and substituting the **reversed**
  field list into its body agree only when the field values have no loose bvars: at
  `k = 2` the β chain gives `subst f₁ 0 (subst f₀ 1 body)` and the `substList` form gives
  `subst f₀ 0 (subst f₁ 0 body)`, which coincide iff `subst f₀ 0 f₁ = f₁`. With
  `body = .bvar 0` and `f₁ = .lambda n (.bvar 1)` — a legal `WcbvEval` value at nonempty
  `Δ` — the two genuinely differ. This is MetaRocq's own `closedn 0` convention, not a
  modelling shortcut, and it is why `erases_correct_dataι` threads `LBClosed t 0`. The
  bridge is `wcbvEval_mkApps_mkLambdas_substList` (`IotaBridge.lean`), over
  `LBTerm.substList_reverse_subst` (`Closed.lean`); at zero fields it degenerates to
  `rfl`.
* **`IotaRelevant`** (above) — the two relevance side conditions.

**A general `erases_correct_dataι` (ι forward simulation matching `erases_correct_data_zeta`'s
generality) was FALSE against the then-current `Erases.cases` relation, and the obstruction was a
genuine under-constraint of that relation** — reported here (not silently patched;
`Erases.lean` is out of scope) per the project's "raise implementation issues" discipline.

**The gap.** The shipping eraser's `visitCases` (`Erasure.lean`) wraps *each* minor to
**exactly** its constructor's field arity, via `lambdaOrIntroToArity ar` (it knows each
constructor's arity). The `Erases.cases` **relation**, by contrast, only requires each
`minors[j]` to erase to `mkLambdas names body` for *some* `names`/`body` — it does **not**
pin `names.length` to the constructor's field count, nor `minors.length` to the inductive's
constructor count. So the relation strictly over-approximates the shipping eraser.

**Why that breaks the ι forward simulation.** MetaRocq's non-block `WcbvEval.iota` fires
only when `(args.drop np).length = names.length` (the evaluated constructor's field count
equals the selected alternative's binder count). A relational `Erases.cases` derivation that
mis-counts binders (e.g. splits a result-returning minor `fun n => n` as the 1-binder
alternative `([n], .bvar 0)` for a *zero-field* constructor) yields a `.case` node whose
target-iota field-count premise is unsatisfiable — the node is **stuck**, so no `t'` exists,
falsifying the conclusion. Concretely: for `f := Bool.casesOn (motive := fun _ => Nat → Nat)
discr (fun n => n) (fun n => n+1) : Nat → Nat` and `a : Nat`, the term `f a`
(i) `SEvalDataι`-evaluates by **β** (its casesOn head reduces to a `λ`, then applies `a`),
while (ii) it is *also* a syntactic casesOn spine `(discr :: [min₁, min₂, a]).foldl` that
`Erases.cases` can erase to a `.case` with over-counted minors/binders; that `.case` cannot
`WcbvEval.iota`-step (the true `Bool.true` has 0 fields, but the erased alternative claims 1
binder), so the forward-simulation conclusion `∃ t', WcbvEval … t t'` fails.

**Consequences, as resolved.** The relation was tightened (the three pins above, ι T1),
the source relation `SEvalDataι` was given matching arithmetic pins (ι T2) and the two
parses reconciled by `IotaArityCoherent` (`SourceEvalData.lean`), and the inversion that
consumes all of it is `Erases.cases_spine_inv` / `Erases.iota_redex_inv`
(`ErasesCorrectData.lean`). The **β-chain ↔ reversing-`iota_red` bridge** named here is
`wcbvEval_mkApps_mkLambdas_substList` (`IotaBridge.lean`), which closes the
*field-carrying* case: `mkApps (mkLambdas names body) fields` and
`substList fields.reverse body` evaluate identically when `names.length = fields.length`,
the fields are values **and the fields are de-Bruijn closed** (the closedness is not
slack — see the worked counterexample in the status note above). At `fields = []` it is
`rfl`, the regime the first slice of the simulation was restricted to. D3's ι variant
composes `SEvalDataι_defeq` with
`erases_correct_dataι`; for first-order values there is no over-application (a `casesOn`
returns data, never a further-applied function), so the saturation constraint holds
automatically.

## Non-vacuity guards for the non-ι theorems (`ErasesCorrectData.lean`)

The ζ-fragment simulation `erases_correct_data_zeta` and the `VLCtx`-defeq transport
`Erases.defeqDFC` carry no `IotaConsistent`, so — per the standing discipline — each ships
a **constructed** non-vacuity guard: they *fire* on the shared first-order witness
(`envFO`/`ΓFOd`/`EFOd`, a nullary constructor `c`), showing their hypothesis bundles are
jointly satisfiable and produce real content. -/

/-- **`erases_correct_data_zeta` fires** on the concrete first-order witness (the nullary
constructor `c`), delivering a real target evaluation erasing the value — its hypothesis
bundle is jointly satisfiable (the source-env consistency hypotheses hold vacuously for the
empty `Esrc`). -/
theorem erases_correct_data_zeta_fires :
    ∃ t' vve, WcbvEval EFOd appliedFlags (.construct ⟨toKername `I, 0⟩ 0 []) t' ∧
      TrExprS envFO [] [] (.const `c []) vve ∧
      Erases envFO [] ΓFOd [] (.const `c []) t' ∧ NoBlock t' := by
  refine erases_correct_data_zeta (env := envFO) envFO_wf (Us := []) (Δ := []) trivial
    (Esrc := fun _ => none) (E := EFOd) ?_ ?_ ΓFOd_envctor ?_
    (recEnvConsistent_of_noRec (Γ := ΓFOd) rfl) rfl
    (v := .const `c []) ?_ envFO_trC (.ctor_head `c [] _ 0 ΓFOd_ctorsC) trivial
  · intro Δ n us body cve h; exact absurd h (by simp)
  · intro Δ n body h; exact absurd h (by simp)
  · intro cn iid cidx hc
    by_cases h : cn = `c
    · subst h; rfl
    · simp [ΓFOd, if_neg h] at hc
  · have heq : (.const `c [] : Expr) = ([] : List Expr).foldl Expr.app (.const `c []) := rfl
    rw [heq]
    exact .ctor_val ΓFOd_ctorsC ΓFOd_ctorAritiesC (by simp) rfl (fun i h => absurd h (by simp))

/-- **`Erases.defeqDFC` fires**: transporting the `.const c` erasure across the (reflexive,
hence trivially definitionally-equal) empty `VLCtx` yields the same erasure — its
hypothesis bundle (`env.WF` + `VLCtx.IsDefEq` + a paired `TrExprS` + an `Erases`) is jointly
satisfiable on the first-order witness. -/
theorem Erases_defeqDFC_fires :
    Erases envFO [] ΓFOd [] (.const `c []) (.construct ⟨toKername `I, 0⟩ 0 []) :=
  Erases.defeqDFC envFO_wf (Δ₁ := []) (Δ₂ := []) .nil envFO_trC
    (.ctor_head `c [] ⟨toKername `I, 0⟩ 0 ΓFOd_ctorsC)

end LeanToLambdaBox
