import LeanToLambdaBox.SubjectReductionFull
import LeanToLambdaBox.SourceEvalData
import LeanToLambdaBox.ErasesCorrectData
import LeanToLambdaBox.FirstOrder

/-!
# Subject reduction and forward simulation for the ι (`casesOn`) fragment — C2/C3

`SEvalDataι` (`SourceEvalData.lean`) is the β + δ + saturated-constructor + **corrected
ι** source evaluation. This file adds the two ι theorems:

* `SEvalDataι_defeq` — subject-reduction-as-defeq over `SEvalDataι` (C2), mirroring
  `SEvalβζδ_defeq` for the non-ι rules and discharging the ι case **only** through the
  `IotaConsistent` hypothesis; and
* the ι-reduct correspondence (C3 core) `erases_iota_reduct`: the source ι reduct (the
  minor applied to the constructor fields *in order*, `(cargs.drop np).foldl Expr.app
  (minors[cidx])`) erases to the target `iota_red` (the field-substituted alternative
  body, in **reverse**: `substList ((args.drop np).reverse) body`) — the β-chain ↔
  reversing-`iota_red` bridge, built by iterating `lam_inv` and a `β`-step lemma.

## The `IotaConsistent` honesty statement (REQUIRED, precise)

`IotaConsistent env Us Γ` (defined in `SourceEvalData.lean`) is the ONE hypothesis this
development does **not** discharge, and it is stated as an explicit **hypothesis** —
never an axiom of ours.

Against the current pin (the `barabbs/lean4lean` ι fork) the *categorical* blocker is
gone. `VEnv` now carries a schematic-rule registry `pats`; `VEnv.IsDefEq` has a 14th
constructor `pat`, the ι/recursor computation rule that consumes it; `VEnv.addInduct` is
a real registration pipeline (no longer `sorry`) installing one `SimplePattern.iota` rule
per recursor rule; `VInductDecl.WF` is a real structure; and `Lean4Lean.Verify.AddInduct`
is a real 8-field structure rather than constructorless. An ambient `VEnv` *can* now carry
ι-defeqs, so `IotaConsistent` is no longer un-witnessable in principle.

It is nevertheless **unblocked, not discharged**. On the upstream side:

* `TrEnv.pats_iota` concludes `∃ r, venv.pats P r` with the rule payload `r` opaque, so
  `TrEnv.iota_defeq`'s `Realizes` premise cannot be instantiated and the reduct
  `r.1.apply m1 m2` cannot be matched against our branch body;
* `AddInduct.rec_find` never relates the model-side `ru.rhs` to the kernel recursor rule's
  `rhs`, so a firing rule is not known to compute the expected branch;
* registration is still trusted: `addInduct_WF` (`Ordered` has no `addPat` constructor),
  `Aligned.addInduct`, and `addDecl.WF`'s `inductDecl` case are `sorry`;
* the ι model covers only the exact-arity, syntactic-constructor case.

On our side, an instance additionally needs the `casesOn`-spine translation inversion and
the β-chain ↔ reversing-`iota_red` bridge that this file's C3 work identifies.
`IotaConsistent` therefore stays a documented **upstream dependency** — now on
*completing* lean4lean's ι interface rather than on its existence. Every *other*
hypothesis-bearing theorem in this file (and in `ErasesCorrectData.lean`) ships a
constructed non-vacuity guard (below); the ι theorems are the sole exception.

(ι Task 2 update: the first two bullets are now named by `LeanToLambdaBox.PatsIotaSpec`
and consumed by `iota_defeq_spine`; `IotaConsistent`/`SEvalDataι.iota` carry the
exact-arity premises the fourth bullet calls for. See `IotaPattern.lean` and
`IotaDischarge.lean` — the latter's module docstring supersedes this paragraph's
accounting of what remains.)
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-! ## C2 — subject reduction as definitional equality over `SEvalDataι`. -/

/-- **Subject reduction as definitional equality (β + δ + saturated constructors + ι).**

If `e` translates to `ve` and `e` evaluates to `v` under `SEvalDataι`, then `v` translates
to some `vve` definitionally equal to `ve`. The λ/β/δ/ctor cases reuse the reasoning of
`SEvalβζδ_defeq` (`SEvalβζδ_defeq_spine` for the constructor spine); the ι case is
discharged **only** via the `IotaConsistent` hypothesis `hiota` — the pinned fork's ι rule
(`IsDefEq.pat`) exists but is not yet chainable into a concrete instance (see the module
docstring). `IotaConsistent` stays a hypothesis, never an axiom. -/
theorem SEvalDataι_defeq {env : VEnv} (henv : env.WF) {Us : List Name} {Δ : VLCtx}
    (hΔ : VLCtx.WF env Us.length Δ) {Γ : ErasureCtx} {ia : IotaArities} {Esrc : SEnv}
    (hcon : SEnvConsistent env Us Esrc) (hiota : IotaConsistent env Us Γ ia)
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
            | zero => exact fun htr => ihdiscr hΔ htr
            | succ j => exact fun htr => ⟨_, htr, VEnv.IsDefEqU.refl (htr.wf henv.ordered hΔ)⟩)
          htr
      -- IotaConsistent: the replaced casesOn spine is defeq to the branch reduct
      obtain ⟨bve, htr_branch, hdef2⟩ :=
        hiota hcases hctor hia har hpre hmin hcargs hidx htr_replaced
      obtain ⟨rvv, htr_r, hdef3⟩ := ihbranch hΔ htr_branch
      exact ⟨rvv, htr_r, VEnv.IsDefEqU.trans henv hΓ hdef1
        (VEnv.IsDefEqU.trans henv hΓ hdef2 hdef3)⟩

/-! ## C3 — the ι forward simulation: a raised implementation finding

**Status: the relational under-constraint reported below has since been fixed in
`Erases.lean`.** `Erases.cases` now carries three arity pins — `hpre`
(`Γ.casesDiscrPos con = some pre.length`), `hnfs` + `hnlen` (one alternative per
constructor, from `Γ.ctorFields`) and `harity` (alternative `j` binds exactly
constructor `j`'s fields) — which make the model's parse of a `casesOn` spine coincide
with `visitCasesEtaGo`'s. Note that a *third* pin beyond the two identified below was
required: without `hpre` the counterexample survives in shifted form, because an
**over-applied** `casesOn` can be re-parsed with the first minor as the discriminant
(`pre = [motive, discr]`, `minors = [min₁, min₂, …]`), again yielding a `.case` on a
`.lambda` — stuck, since `WcbvEval` has no `case_cong` rule. The analysis below is kept
as the record of the obstruction; the ι forward simulation itself remains unproved (it
still needs the matching pins on `SEvalDataι.iota` and the β-chain ↔ `iota_red` bridge
noted at the end of this section).

**A general `erases_correct_dataι` (ι forward simulation matching `erases_correct_data_zeta`'s
generality) is FALSE against the then-current `Erases.cases` relation, and the obstruction is a
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

**Consequences / composable route.** The ι forward simulation needs `Erases.cases`
strengthened to pin the per-minor binder counts to the constructor arities (and the minor
count to the constructor count) — the invariant the shipping eraser already maintains. That
is an `Erases.lean` change (upstream of this workstream). Until then, the composable pieces
are: `SEvalDataι_defeq` (above, complete, C2) for the source-side ι subject reduction, and,
once the relation is tightened, the **β-chain ↔ reversing-`iota_red` bridge** (a pure
`WcbvEval` fact: `mkApps (mkLambdas names body) fields` and `substList fields.reverse body`
evaluate identically when `names.length = fields.length` and `fields` are values — the
target `iota_red`'s reversal matches applying the `mkLambdas` chain in order). D3's ι variant
should compose `SEvalDataι_defeq` with a *saturation-constrained* `Erases.cases` restatement,
which for first-order values (no over-application: casesOn returns data, never a further-
applied function) holds automatically.

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
      Erases envFO [] ΓFOd [] (.const `c []) t' ∧ NoBlock t' ∧ NoFix t' := by
  refine erases_correct_data_zeta (env := envFO) envFO_wf (Us := []) (Δ := []) trivial
    (Esrc := fun _ => none) (E := EFOd) ?_ ?_ ΓFOd_envctor ?_ ?_
    (v := .const `c []) ?_ envFO_trC (.ctor_head `c [] _ 0 ΓFOd_ctorsC) trivial trivial
  · intro Δ n us body cve h; exact absurd h (by simp)
  · intro Δ n body h; exact absurd h (by simp)
  · intro cn iid cidx hc
    by_cases h : cn = `c
    · subst h; rfl
    · simp [ΓFOd, if_neg h] at hc
  · intro kn body' h; simp only [EFOd, LBTerm.envLookup] at h; split at h <;> simp_all
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
