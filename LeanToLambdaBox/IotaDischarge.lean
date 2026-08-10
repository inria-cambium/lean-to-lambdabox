import LeanToLambdaBox.IotaPattern
import LeanToLambdaBox.SourceEvalData
import LeanToLambdaBox.SubjectReductionFull

/-!
# Discharging `IotaConsistent` — the chain, end to end

`IotaPattern.lean` supplies the pattern-side core: a `Pattern.Matches` introduction
rule for spines, the `SimplePattern.iotaRHS` reduct calculation, `TrExprS` spine
inversion *and construction*, the named upstream spec `PatsIotaSpec`, and
`iota_defeq_spine`, which **fires** the ι rule on a translated exact-arity redex.

This file closes the chain: the source-level β engine, the per-`casesOn` shape
certificate `IotaShape`, the derivation `iotaConsistent_of_shape`, and the constructed
non-vacuity guards.

## The chain

For a `casesOn` spine `con pre… discr minors…` whose scrutinee has evaluated to a
saturated constructor spine, `IotaConsistent` asks for a definitional equality to
`(cargs.drop np).foldl Expr.app minors[cidx]`:

```
 (0)  ve   = ⟦con pre… (ctor C̄) minors…⟧                  -- the source spine
 (1)  ≡ δ    unfold `con` to its value                     -- SEnvConsistent
 (2)  ≡ β    reduce the casesOn wrapper to the rec spine   -- trExprS_betaN + IotaShape
 (3)  ≡ ι    the registered rule fires                     -- iota_defeq_spine
 (4)  ≡ β    reduce the rule template through its telescope
 (5)  ≡ β    unwrap the casesOn-inserted minor wrapper     -- trExprS_betaN + IotaShape
           = ⟦minors[cidx] (C̄.drop np)⟧
```

**δ via `SEnvConsistent`, not `TrEnv.of_value`.** The repo already threads the source
δ facts as `SEnvConsistent` (a premise of `SEvalβζδ_defeq` and `SEvalDataι_defeq`), so
step (1) reuses it. That is not just economical: `TrEnv.of_value` routes through
`H.map_wf`, and `TrEnv'.map_wf := H.aligned.map_wf` whose `induct` case is
`Aligned.addInduct`, an IOTA-TODO `sorry` at the current pin — so the `of_value` route
*would* inherit a gap that `pats_iota` (deliberately routed through the
`Aligned`-free `TrEnv'.constMap_wf`) does not. This contradicts the handoff note's
"you inherit no new gap", which is accurate for `pats_iota` alone. The fork's
`iota-consume` branch de-taints `of_value` by swapping `map_wf → constMap_wf`; we
neither rely on it nor work around it.

## `TrExprS` for the ι *reduct* spine

`IotaConsistent`'s conclusion demands a **`TrExprS` of an application spine** that is
*not* a subterm of the redex and is well-typed only because the ι rule fired, so no app
node of the input supplies the two `HasType` fields of `TrExprS.app`.

They are supplied by **application generation**: `Lean4Lean.VEnv.HasType.app_inv`
(`Theory/Typing/Strong.lean`) is a *proved theorem* at the current pin —
`Strong.lean`'s `IsDefEq.strong` / `IsDefEqStrong.hasType'` layering exists precisely
to prove it — with premises `env.Ordered` and `OnCtx Γ (env.IsType U)`, both already in
scope everywhere here. (`Experimental/NormalEq.lean` also *states* an `app_inv`, but as
a field of an abstract `Typing` class — an interface, not evidence of unavailability.)
`TrExprS.mkApps` (`IotaPattern.lean`) packages it. Its sorry-frontier is a subset of
the one `VEnv.IsDefEq.uniqU` already carries, and `uniqU` is used pervasively in the
committed development, so this adds no sorry-carrying declaration.

## What is assumed

* **`PatsIotaSpec`** — the one named hypothesis structure: the fork's strengthened
  rule lookup, dischargeable by `exact TrEnv.pats_iota' …` after the re-pin.
* **`SEnvConsistent`** — already an accepted premise of the surrounding development.
* **`IotaShape`** — the per-`casesOn` certificate: kernel lookups plus `Expr`
  equations, `rfl`/`decide`-checkable for any concrete inductive. Nothing in it is a
  typing or translation assumption.

No new `sorry` and no new axiom.

## Non-vacuity guards

`iotaConsistent_of_shape` takes `env.WF`, and `VEnv.WF` is **unconstructible for a
`pats`-carrying environment at this pin** (`VEnv.Ordered` has no `addPat` clause;
`addInduct_WF` and `addDecl.WF`'s `inductDecl` case are `sorry`). So — exactly as for
`SEvalDataι_defeq` — a guard that instantiates the whole theorem is not available, and
the guards stay at the level of its two halves:

* `envι_iota_fires` — the ι machinery fires and yields a real `IsDefEqU`, on a `VEnv`
  built by `VEnv.addPat` directly. `sorryAx`-free. Its shape exercises the `take`/`drop`
  conventions of `SimplePattern.iotaRHS_apply` at `np = nmot = nmin = nind = nfields = 1`,
  so **both** `np > 0` and `nind > 0`: with `np = nind = 0` (`Bool`, enums) both slices
  degenerate and a reversed convention would still look right, whereas here the six
  arguments are pairwise distinct (`bvar 0 … bvar 5`) and the reduct visibly drops
  `bvar 3` — the recursor's **index**, which sits between the minors and the major —
  and `bvar 4` — the constructor's **parameter** — keeping `[bvar 0, bvar 1, bvar 2]`
  and `[bvar 5]`.
* `betaN_casesOn_guard` / `betaN_ruleTemplate_guard` — `IotaShape`'s `Expr` equations
  hold, by `rfl`, on a concrete `casesOn` wrapper and a concrete recursor rule template
  at the same `np = nmot = nmin = nind = nfields = 1` shape. The first certifies the
  argument **reordering** between `C.casesOn`'s telescope
  (`params motive indices major minors`) and `C.rec`'s
  (`params motives minors indices major`); the second certifies that `betaN` stops with
  the branch **applied to** the fields rather than contracting them away.
* `betaN_ruleTemplate_eta_guard` / `betaN_ruleTemplate_rec_guard` — the *two-stage* form
  against the shapes the kernel really generates: `Option.casesOn`'s η-wrapper
  (`ihs = []`) and `Nat.casesOn`'s IH-discarding wrapper (`ihs ≠ []`). The degenerate
  guard above uses a hand-written non-η template, which is why the single-stage
  statement's unsatisfiability for every field-carrying inductive went unnoticed.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-! ## Steps (2)/(4)/(5): the β-normalisation engine

Steps (2), (4) and (5) of the chain are all the same operation — apply a source
λ-telescope to a list of arguments and β-reduce — so they share one engine.

The key point is that a β step produces the reduct's `TrExprS` **for free**, via
`TrExprS.inst`: no application node has to be built. (The one place an application
node *is* built — re-attaching the model's ι reduct to the source rule template — goes
through `TrExprS.mkApps`, i.e. through application generation.) -/

/-- One head β step on a source `Expr`: contract if the head is a λ, otherwise just
apply. Splitting this out of `betaN` keeps `betaN e (a :: as) = betaN (betaHead e a) as`
an unconditional `rfl`. -/
def betaHead : Expr → Expr → Expr
  | .lam _ _ b _, a => b.instantiate1' a 0
  | e, a => .app e a

/-- Iterated head β: apply `f` to `args`, contracting each redex as it appears. This
is the *source-level* normal form the shape certificate's `casesOn`-value and
rule-template equations are stated against. -/
def betaN : Expr → List Expr → Expr
  | e, [] => e
  | e, a :: as => betaN (betaHead e a) as

@[simp] theorem betaN_nil (e : Expr) : betaN e [] = e := rfl

@[simp] theorem betaN_cons (e a : Expr) (as : List Expr) :
    betaN e (a :: as) = betaN (betaHead e a) as := rfl

/-- **One β step, as a definitional equality.** A translated redex
`(fun x => b) a` is defeq to the translation of `b[a]` — and the reduct's `TrExprS`
comes from `TrExprS.inst`, so no application node has to be constructed. This is the
`SEvalβζδ_defeq` `beta` case with the "evaluate `f` and `a` first" detour removed. -/
theorem trExprS_beta_step {env : VEnv} (henv : env.WF) {Us : List Name} {Δ : VLCtx}
    (hΔ : VLCtx.WF env Us.length Δ)
    {n : Name} {ty b : Expr} {bi : BinderInfo} {a : Expr} {ve : VExpr}
    (htr : TrExprS env Us Δ (.app (.lam n ty b bi) a) ve) :
    ∃ ve', TrExprS env Us Δ (b.instantiate1' a 0) ve' ∧
      env.IsDefEqU Us.length Δ.toCtx ve ve' := by
  cases htr with
  | @app f' A B a' _ _ _ hTf hTa htrf htra =>
    cases htrf with
    | @lam ty' _Δ _ty _body body' _name _bi hty' htrty htrb =>
      have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
      have hΔ' : VLCtx.WF env Us.length ((none, .vlam ty') :: Δ) := ⟨hΔ, nofun, hty'⟩
      obtain ⟨B'', hbodyT⟩ := htrb.wf henv.ordered hΔ'
      obtain ⟨u, hty'sort⟩ := hty'
      have lamT1 : env.HasType Us.length Δ.toCtx (.lam ty' body') (.forallE ty' B'') :=
        VEnv.HasType.lam hty'sort hbodyT
      have huForall : env.IsDefEqU Us.length Δ.toCtx (.forallE A B) (.forallE ty' B'') :=
        VEnv.IsDefEq.uniqU henv hΓ hTf lamT1
      obtain ⟨⟨w, hAty'⟩, _⟩ := VEnv.IsDefEqU.forallE_inv henv hΓ huForall
      have havT : env.HasType Us.length Δ.toCtx a' ty' :=
        hTa.defeqU_r henv hΓ ⟨_, hAty'⟩
      exact ⟨body'.inst a', TrExprS.inst henv.ordered havT htrb htra,
        ⟨_, .beta hbodyT havT⟩⟩

/-- `betaHead` is a defeq step (a β contraction when the head is a λ, the
identity otherwise). -/
theorem trExprS_betaHead {env : VEnv} (henv : env.WF) {Us : List Name} {Δ : VLCtx}
    (hΔ : VLCtx.WF env Us.length Δ) {f a : Expr} {ve : VExpr}
    (htr : TrExprS env Us Δ (.app f a) ve) :
    ∃ ve', TrExprS env Us Δ (betaHead f a) ve' ∧
      env.IsDefEqU Us.length Δ.toCtx ve ve' := by
  cases f <;>
    first
      | exact trExprS_beta_step henv hΔ htr
      | exact ⟨ve, htr, VEnv.IsDefEqU.refl (htr.wf henv.ordered hΔ)⟩

/-- **The β-normalisation chain.** A translated application spine is defeq to the
translation of its iterated head-β normal form. Each step replaces the spine's head
in place (`SEvalβζδ_defeq_spine`, used as pure head congruence) and then contracts
it (`trExprS_betaHead`).

This is the engine for steps (2), (4) and (5): with a shape certificate stating
`betaN (casesOn-value) (pre ++ discr :: minors) = recSpine` and
`betaN (rule-template) (params ++ motives ++ minors ++ fields)
  = (fields).foldl Expr.app minors[cidx]` — both `rfl`-checkable `Expr` equations for
any concrete inductive — it delivers exactly the defeqs those steps need. -/
theorem trExprS_betaN {env : VEnv} (henv : env.WF) {Us : List Name} {Δ : VLCtx}
    (hΔ : VLCtx.WF env Us.length Δ) :
    ∀ (args : List Expr) {f : Expr} {ve : VExpr},
      TrExprS env Us Δ (args.foldl Expr.app f) ve →
      ∃ ve', TrExprS env Us Δ (betaN f args) ve' ∧
        env.IsDefEqU Us.length Δ.toCtx ve ve'
  | [], _, ve, htr => ⟨ve, htr, VEnv.IsDefEqU.refl (htr.wf henv.ordered hΔ)⟩
  | a :: as, f, ve, htr => by
    have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
    -- The spine is `as.foldl app (.app f a)`; contract the head `.app f a`.
    have htr' : TrExprS env Us Δ (as.foldl Expr.app (.app f a)) ve := htr
    obtain ⟨hve, htrHead⟩ := TrExprS_spine_head as htr'
    obtain ⟨hve₂, htrHead₂, hdhead⟩ := trExprS_betaHead henv hΔ htrHead
    -- Head congruence: replace `.app f a` by its contraction inside the spine.
    obtain ⟨mid, htrmid, hdmid⟩ :=
      SEvalβζδ_defeq_spine henv hΔ
        (fun e v => ∀ {ev}, TrExprS env Us Δ e ev →
          ∃ vv, TrExprS env Us Δ v vv ∧ env.IsDefEqU Us.length Δ.toCtx ev vv)
        (fun htr p => p htr)
        as.length as as (.app f a) (betaHead f a) hve hve₂ rfl rfl
        htrHead htrHead₂ hdhead
        (fun i h _ => fun htr => ⟨_, htr, VEnv.IsDefEqU.refl (htr.wf henv.ordered hΔ)⟩)
        htr'
    obtain ⟨ve', htrve', hd'⟩ := trExprS_betaN henv hΔ as htrmid
    exact ⟨ve', htrve', VEnv.IsDefEqU.trans henv hΓ hdmid hd'⟩

/-! ## The per-`casesOn` shape certificate

Everything the ι chain needs about the *kernel* that `TrEnv`/`VInductDecl.WF` do not
pin — `VInductDecl.WF`'s own docstring says it does not "pin the recursor/rule shape to
the one `addInduct` reduces with" — is packaged here, per registered `casesOn`, as
kernel lookups plus **`Expr` equations**. For any concrete inductive every equation is
a closed `Expr` equality between a `betaN` computation and a spine, hence `rfl`- or
`decide`-checkable; nothing in it is a typing or translation assumption.

The two β equations are exactly steps (2) and (4)/(5) of the chain:

* `hunfold` — the `casesOn`'s δ-value, applied to `params ++ motive ++ indices`, the
  major premise and the minors, β-normalises to the **recursor redex**
  `(rec P̄ M̄ minors Ī) major`. This is where the argument reordering between
  `C.casesOn`'s telescope (`params motive indices major minors`) and `C.rec`'s
  (`params motives minors indices major`) is recorded, by the `recArgs` function.
* the per-constructor equation, **in two β stages** — the recursor rule's template,
  applied to the recursor spine's `params ++ motives ++ minors` (the ι reduct's rec-side
  slice) and then the constructor's fields (its ctor-side slice), β-normalises to a
  *wrapper* applied to the fields **and the recursive calls**; the wrapper then discards
  the recursive calls and hands the fields to the selected minor. `betaN` stops when its
  pending argument list is exhausted, so the applications the template's body builds
  survive even when the minor is itself a λ — which is what makes this equal to
  `IotaConsistent`'s target rather than to its β-contraction.

  **Why two stages** (probed against the real kernel, v4.33.0-rc2). Lean's generated
  `casesOn` **η-expands every minor that takes fields**, and for a recursive inductive
  the wrapper additionally swallows the induction hypotheses:
  ```
  Bool.casesOn   := fun {motive} t false true => Bool.rec false true t
  Option.casesOn := fun {α} {motive} t none some => Option.rec none (fun val => some val) t
  Nat.casesOn    := fun {motive} t zero succ => Nat.rec zero (fun n n_ih => succ n) t
  Nat.rec's succ rule rhs = fun motive zero succ n => succ n (Nat.rec zero succ n)
  ```
  So for anything but a zero-field constructor the single-stage reduct ends in a redex
  `betaN` cannot contract — it is created *inside* the template's body, not pending in
  the supplied argument list — and the old one-stage equation was **unsatisfiable for
  `Option`, `Nat`, `List`, `Prod`, …**, i.e. for every inductive except enumerations.
  (The earlier guard did not catch this because it used a hand-written, *non*-η-expanded
  template, a shape no real `casesOn` has.)

  Stage two *discards* `ihs`, which is exactly the semantic content of "a `casesOn` is a
  recursor whose minors ignore the recursive results" — the fact that makes
  `SEvalDataι.iota`'s reduct `(cargs.drop np).foldl app minors[cidx]` (fields only, no
  IHs) the right source-side reduct in the first place. Making it a certificate
  *obligation* rather than an unstated assumption is a strict improvement in honesty.
  For a non-recursive inductive with a zero-field constructor the wrapper is the minor
  itself, `ihs = []`, and stage two is `rfl`. -/

/-- **Per-`casesOn` shape certificate** (see the section docstring). -/
structure IotaShape (safety : DefinitionSafety) (kenv : Lean.Environment)
    (Γ : ErasureCtx) (ia : IotaArities) (Esrc : SEnv) : Prop where
  shape : ∀ {con : Name} {iid : InductiveId} {np nmot nidx nmin : Nat},
    Γ.casesOns con = some (iid, np) → ia con = some (nmot, nidx, nmin) →
    ∃ (conVal : Expr) (recName : Name) (rval : RecursorVal) (rus : List Level)
      (recArgs : List Expr → List Expr → List Expr),
      -- the `casesOn`'s source δ-value, and the recursor it unfolds to
      Esrc con = some conVal ∧
      kenv.find? recName = some (.recInfo rval) ∧
      safety ≤ (Lean.ConstantInfo.recInfo rval).safety ∧
      rval.levelParams.length = rus.length ∧
      rval.numParams = np ∧ rval.numMotives = nmot ∧
      rval.numMinors = nmin ∧ rval.numIndices = nidx ∧
      -- (i) the recursor spine the `casesOn` wrapper β-reduces to
      (∀ pre minors, pre.length = np + nmot + nidx → minors.length = nmin →
        (recArgs pre minors).length = np + nmot + nmin + nidx) ∧
      (∀ pre minors discr, pre.length = np + nmot + nidx → minors.length = nmin →
        betaN conVal (pre ++ discr :: minors)
          = .app ((recArgs pre minors).foldl Expr.app (.const recName rus)) discr) ∧
      -- (ii) per constructor: its rule, and the rule template's β-normal form
      (∀ {ctor : Name} {cidx : Nat}, Γ.ctors ctor = some (iid, cidx) →
        ∃ rule : RecursorRule, rval.rules.find? (·.ctor == ctor) = some rule ∧
          Γ.ctorArities ctor = some (np + rule.nfields) ∧
          (rule.rhs.instantiateLevelParams rval.levelParams rus).looseBVarRange' = 0 ∧
          ∀ (pre minors fields : List Expr) (hidx : cidx < minors.length),
            pre.length = np + nmot + nidx → minors.length = nmin →
            fields.length = rule.nfields →
            ∃ (wrapper : Expr) (ihs : List Expr),
              betaN (rule.rhs.instantiateLevelParams rval.levelParams rus)
                ((recArgs pre minors).take (np + nmot + nmin) ++ fields)
                = (fields ++ ihs).foldl Expr.app wrapper ∧
              betaN wrapper (fields ++ ihs) = fields.foldl Expr.app (minors[cidx]'hidx))

/-! ## The payoff: `IotaConsistent` from the spec plus the certificate -/

/-- **`IotaConsistent` is derivable** from

* `PatsIotaSpec` — the one named hypothesis, the fork's strengthened rule lookup;
* `SEnvConsistent` — the δ facts, already a premise of `SEvalDataι_defeq` (this is
  *not* `TrEnv.of_value`, and therefore does **not** inherit the `Aligned.addInduct`
  `sorry` that taints that route at the current pin);
* `IotaShape` — the per-inductive, `rfl`-checkable kernel shape certificate.

The chain is (0)→(1)(2) `SEnvConsistent` + head congruence + `trExprS_betaN` to the
recursor redex, (3) `iota_defeq_spine` fires the rule, (4)(5) `TrExprS.instL_weak` +
`TrExprS.mkApps` re-attach the ι reduct to the *source* rule template and
`trExprS_betaN` normalises it to the branch applied to the fields. The reduct spine's
`TrExprS` — the step that needs application generation — is built by
`TrExprS.mkApps`. -/
theorem iotaConsistent_of_shape {safety : DefinitionSafety} {kenv : Lean.Environment}
    {env : VEnv} (henv : env.WF) {Us : List Name} {Γ : ErasureCtx} {ia : IotaArities}
    {Esrc : SEnv}
    (hspec : PatsIotaSpec safety kenv env)
    (hcon : SEnvConsistent env Us Esrc)
    (hshape : IotaShape safety kenv Γ ia Esrc) :
    IotaConsistent env Us Γ ia := by
  intro Δ con ctor us cus pre minors cargs iid np cidx nmot nidx nmin ar ve
    hΔ hcases hctor hia har hpre hmin hcargs hidx htr
  obtain ⟨conVal, recName, rval, rus, recArgs, hconVal, hrec, hsafe, hlen,
    hnp, hnmot, hnmin, hnidx, hraLen, hunfold, hctors⟩ := hshape.shape hcases hia
  subst hnp; subst hnmot; subst hnmin; subst hnidx
  obtain ⟨rule, hrule, harity, hsrcclosed, hbeta2⟩ := hctors hctor
  have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
  have harEq : ar = rval.numParams + rule.nfields := by
    rw [har] at harity; exact Option.some.inj harity
  subst harEq
  -- (0) reshape the redex into a single flat spine `con (pre ++ discr :: minors)`.
  rw [show ((cargs.foldl Expr.app (.const ctor cus)) :: minors).foldl Expr.app
        (pre.foldl Expr.app (.const con us))
      = (pre ++ (cargs.foldl Expr.app (.const ctor cus)) :: minors).foldl Expr.app
        (.const con us) from (List.foldl_append ..).symm] at htr
  -- (1) δ-unfold the `casesOn` head, (2a) transport the spine to the unfolded head.
  obtain ⟨hve, htrHead⟩ := TrExprS_spine_head _ htr
  obtain ⟨cveb, htrConVal, hdδ⟩ := hcon hconVal htrHead
  obtain ⟨ve₁, htr₁, hd₁⟩ :=
    SEvalβζδ_defeq_spine henv hΔ
      (fun e v => ∀ {ev}, TrExprS env Us Δ e ev →
        ∃ vv, TrExprS env Us Δ v vv ∧ env.IsDefEqU Us.length Δ.toCtx ev vv)
      (fun htr p => p htr)
      _ (pre ++ (cargs.foldl Expr.app (.const ctor cus)) :: minors)
      (pre ++ (cargs.foldl Expr.app (.const ctor cus)) :: minors)
      (.const con us) conVal hve cveb rfl rfl htrHead htrConVal hdδ
      (fun i h _ => fun htr => ⟨_, htr, VEnv.IsDefEqU.refl (htr.wf henv.ordered hΔ)⟩)
      htr
  -- (2b) β-normalise the unfolded wrapper to the recursor redex.
  obtain ⟨ve₂, htr₂, hd₂⟩ := trExprS_betaN henv hΔ _ htr₁
  rw [hunfold pre minors _ hpre hmin] at htr₂
  -- (3) the ι rule fires.
  obtain ⟨rhs, hc, rus', recArgs', cargs', htrRhs, hmapM, hall1, hall2, hd₃⟩ :=
    iota_defeq_spine hspec henv hΔ hrec hrule hsafe
      (hraLen pre minors hpre hmin) hcargs htr₂
  -- (4a) re-attach the model reduct to the *source* rule template.
  obtain ⟨e₂, htrRhsSrc, hdhead⟩ := TrExprS.instL_weak henv hΔ hmapM hlen hsrcclosed htrRhs
  have hcongr := VEnv.IsDefEqU.mkApps_congr_head henv hΓ
    (recArgs'.take (rval.numParams + rval.numMotives + rval.numMinors)
      ++ cargs'.drop rval.numParams) hdhead hd₃.wf_r
  have htr₃ := TrExprS.mkApps henv.ordered hΓ
    (forall2_append
      (forall2_take (rval.numParams + rval.numMotives + rval.numMinors) hall1)
      (forall2_drop rval.numParams hall2))
    htrRhsSrc hcongr.wf_l
  -- (4b) β-normalise the template to the `casesOn`-inserted wrapper applied to the
  -- fields and the recursive calls, then (5) β-normalise the wrapper away.
  obtain ⟨ve₄, htr₄, hd₄⟩ := trExprS_betaN henv hΔ _ htr₃
  obtain ⟨wrapper, ihs, hstage1, hstage2⟩ :=
    hbeta2 pre minors (cargs.drop rval.numParams) hidx hpre hmin (by simp [hcargs])
  rw [hstage1] at htr₄
  obtain ⟨ve₅, htr₅, hd₅⟩ := trExprS_betaN henv hΔ _ htr₄
  rw [hstage2] at htr₅
  refine ⟨ve₅, htr₅, ?_⟩
  exact VEnv.IsDefEqU.trans henv hΓ hd₁ (VEnv.IsDefEqU.trans henv hΓ hd₂
    (VEnv.IsDefEqU.trans henv hΓ hd₃ (VEnv.IsDefEqU.trans henv hΓ hcongr.symm
      (VEnv.IsDefEqU.trans henv hΓ hd₄ hd₅))))

/-! ### The guard environment

Three constants over a single base type `I : Sort 1`: a "recursor" `R` of arity
`4 + 1` (params + motives + minors + indices, then the major premise) and a
"constructor" `K` of arity `2` (one parameter, one field). No `VEnv.WF` is needed or
claimed — `VEnv.IsDefEq.pat` does not require it, and `VEnv.addPat` is outside the
`Ordered` decl chain anyway (`addInduct_WF` is `sorry` upstream). -/

/-- The guard's single base type, `I`. -/
def Ity : VExpr := .const `I []

/-- The guard "constructor" `K : I → I → I` (one parameter, one field). -/
def Kty : VExpr := .forallE Ity (.forallE Ity Ity)

/-- The guard "recursor" `R : I → I → I → I → I → I` — four spine arguments
(one each of parameter, motive, minor, index) then the major premise. -/
def Rty : VExpr :=
  .forallE Ity (.forallE Ity (.forallE Ity (.forallE Ity (.forallE Ity Ity))))

/-- The guard environment before the ι rule is registered. -/
noncomputable def envιBase : VEnv :=
  ((((VEnv.empty.addConst `I ⟨0, .sort (.succ .zero)⟩).getD .empty).addConst `K
      ⟨0, Kty⟩).getD .empty |>.addConst `R ⟨0, Rty⟩).getD .empty

theorem envιBase_K : envιBase.constants `K = some ⟨0, Kty⟩ := by
  unfold envιBase VEnv.addConst VEnv.empty; simp

theorem envιBase_R : envιBase.constants `R = some ⟨0, Rty⟩ := by
  unfold envιBase VEnv.addConst VEnv.empty; simp

/-- The guard's rule template: a four-ary projection returning its last argument —
the model of "the selected minor applied to the constructor's fields". -/
def rhsι : VExpr := .lam Ity (.lam Ity (.lam Ity (.lam Ity (.bvar 0))))

theorem rhsι_closed : rhsι.Closed := by
  unfold rhsι Ity VExpr.Closed
  simp [VExpr.ClosedN]

/-- The guard environment, with one ι rule registered by `VEnv.addPat` — exactly the
shape `VEnv.addRecRule` installs, at `np = nmot = nmin = nind = nfields = 1`. -/
noncomputable def envι : VEnv :=
  envιBase.addPat (SimplePattern.iota `R (1+1+1+1) `K (1+1)).toPattern
    (SimplePattern.iotaRHS `R `K 1 1 1 1 1 rhsι rhsι_closed, .true)

theorem envι_K : envι.constants `K = some ⟨0, Kty⟩ := envιBase_K
theorem envι_R : envι.constants `R = some ⟨0, Rty⟩ := envιBase_R

/-- Six distinct variables of type `I`, so the reduct's slicing is *visible*. -/
def Γι : List VExpr := [Ity, Ity, Ity, Ity, Ity, Ity]

theorem hb0 : envι.HasType 0 Γι (.bvar 0) Ity := .bvar .zero
theorem hb1 : envι.HasType 0 Γι (.bvar 1) Ity := .bvar (.succ .zero)
theorem hb2 : envι.HasType 0 Γι (.bvar 2) Ity := .bvar (.succ (.succ .zero))
theorem hb3 : envι.HasType 0 Γι (.bvar 3) Ity := .bvar (.succ (.succ (.succ .zero)))
theorem hb4 : envι.HasType 0 Γι (.bvar 4) Ity :=
  .bvar (.succ (.succ (.succ (.succ .zero))))
theorem hb5 : envι.HasType 0 Γι (.bvar 5) Ity :=
  .bvar (.succ (.succ (.succ (.succ (.succ .zero)))))

theorem hK : envι.HasType 0 Γι (.const `K []) Kty :=
  VEnv.HasType.const envι_K (by simp) (by simp)

theorem hR : envι.HasType 0 Γι (.const `R []) Rty :=
  VEnv.HasType.const envι_R (by simp) (by simp)

/-- The ι redex `R b₀ b₁ b₂ b₃ (K b₄ b₅)` is well-typed — the `hty` premise of
`VEnv.IsDefEq.pat`. -/
theorem hredex : envι.HasType 0 Γι
    (.app (VExpr.mkApps (.const `R []) [.bvar 0, .bvar 1, .bvar 2, .bvar 3])
      (VExpr.mkApps (.const `K []) [.bvar 4, .bvar 5])) Ity :=
  ((((hR.app hb0).app hb1).app hb2).app hb3).app ((hK.app hb4).app hb5)

/-- The rule is registered (`VEnv.addPat` is a plain set extension, so this is
`Or.inl ⟨rfl, rfl⟩`). -/
theorem envι_pats :
    envι.pats (SimplePattern.iota `R (1+1+1+1) `K (1+1)).toPattern
      (SimplePattern.iotaRHS `R `K 1 1 1 1 1 rhsι rhsι_closed, .true) :=
  VEnv.addPat_self

/-- **The guard: the ι machinery fires and produces real content.**

`Pattern.matches_iota` builds the match, `envι_pats` supplies the rule, `hredex` the
typing, and `SimplePattern.iotaRHS_apply` computes the reduct — yielding a genuine
`IsDefEqU`, so the `PatsIotaSpec`/`iota_defeq_spine` bundle is not vacuous.

**It also pins the `take`/`drop` conventions.** The recursor spine is
`[b₀, b₁, b₂, b₃]` and the constructor spine `[b₄, b₅]`, with `np = nind = 1`; the
reduct is the template applied to `[b₀, b₁, b₂, b₅]`. So `b₃` (the recursor's
**index**) and `b₄` (the constructor's **parameter**) are dropped, and the order is
forward — no reversal (MetaRocq's `iota_red` reverses; the model's `RHS.apply` does
not, and that asymmetry lives on the target side, not here). -/
theorem envι_iota_fires :
    envι.IsDefEqU 0 Γι
      (.app (VExpr.mkApps (.const `R []) [.bvar 0, .bvar 1, .bvar 2, .bvar 3])
        (VExpr.mkApps (.const `K []) [.bvar 4, .bvar 5]))
      (VExpr.mkApps rhsι [.bvar 0, .bvar 1, .bvar 2, .bvar 5]) := by
  obtain ⟨m2, hm, hva, hvb⟩ :=
    Pattern.matches_iota (recName := `R) (cName := `K) (ls := []) (ls' := [])
      (1+1+1+1) (1+1) [.bvar 0, .bvar 1, .bvar 2, .bvar 3] [.bvar 4, .bvar 5]
      (by simp) (by simp)
  have h := TrEnv.iota_defeq (chk := []) envι_pats hm hredex trivial nofun
  rw [SimplePattern.iotaRHS_apply (np := 1) (nm := 1) (nmin := 1) (nind := 1) (nf := 1)
      (by simp) (by simp) hva hvb] at h
  exact h

/-! ### Guards for `IotaShape`'s two `Expr` equations

Both are checked at the same `np = nmot = nmin = nind = nfields = 1` shape as
`envι_iota_fires`, on five/four pairwise distinct arguments, so the reordering and the
slicing are visible rather than degenerate. -/

private def A0 : Expr := .const `a0 []
private def A1 : Expr := .const `a1 []
private def A2 : Expr := .const `a2 []
private def A3 : Expr := .const `a3 []
private def A4 : Expr := .const `a4 []
private def F0 : Expr := .const `f0 []
private def ty : Expr := .const `I []

/-- The `casesOn` wrapper at `np = nmot = nidx = nmin = 1`:
`fun p motive idx major minor => R p motive minor idx major`. Inside the body the
binders are `minor = #0`, `major = #1`, `idx = #2`, `motive = #3`, `p = #4`. -/
private def conValG : Expr :=
  .lam `p ty (.lam `motive ty (.lam `idx ty (.lam `major ty (.lam `minor ty
    ((([Expr.bvar 4, .bvar 3, .bvar 0, .bvar 2]).foldl Expr.app (.const `R [])).app
      (.bvar 1))
    .default) .default) .default) .default) .default

/-- **`IotaShape.hunfold` fires.** The `casesOn` wrapper, applied to
`pre = [p, motive, idx]`, the major premise and `minors = [minor]`, β-normalises to the
recursor redex — with the arguments **reordered** from `C.casesOn`'s telescope
(`params motive indices major minors`) to `C.rec`'s
(`params motives minors indices major`): `recArgs [p,m,i] [mn] = [p, m, mn, i]`, and
the major premise moves to the outside. -/
theorem betaN_casesOn_guard :
    betaN conValG ([A0, A1, A2] ++ A3 :: [A4])
      = .app (([A0, A1, A4, A2]).foldl Expr.app (.const `R [])) A3 := by
  rfl

/-- The recursor rule template for a one-field constructor at the same shape:
`fun p motive minor field => minor field`. Inside the body `field = #0`,
`minor = #1`. -/
private def ruleRhsG : Expr :=
  .lam `p ty (.lam `motive ty (.lam `minor ty (.lam `field ty
    (.app (.bvar 1) (.bvar 0)) .default) .default) .default) .default

/-- **`IotaShape`'s per-constructor equation fires — degenerate case.** The rule
template, applied to the recursor spine's `take (np+nmot+nmin) = [p, motive, minor]`
(the **index** `A2` is dropped) and then the constructor's fields `[f0]` (its
**parameter** having been dropped by the ctor-side `drop np`), β-normalises to the
selected minor **applied to** the fields — not to their contraction: `betaN` stops when
its pending argument list is exhausted, so the application the template's body builds
survives. Here the `casesOn` inserted no wrapper, so `wrapper = minor`, `ihs = []` and
stage two is `rfl`. -/
theorem betaN_ruleTemplate_guard :
    ∃ (wrapper : Expr) (ihs : List Expr),
      betaN ruleRhsG (([A0, A1, A4, A2]).take (1 + 1 + 1) ++ [F0])
        = ([F0] ++ ihs).foldl Expr.app wrapper ∧
      betaN wrapper ([F0] ++ ihs) = ([F0]).foldl Expr.app A4 :=
  ⟨A4, [], rfl, rfl⟩

/-! ### Guards for the *two-stage* form (ι Task 3)

The degenerate guard above uses a hand-written, non-η-expanded template — a shape no
real `casesOn` has, which is exactly why the single-stage statement survived as long as
it did. These two check the stage split against the shapes the kernel actually generates:
`Option.casesOn`'s η-wrapper (`fun val => some val`, `ihs = []`) and `Nat.casesOn`'s
IH-discarding wrapper (`fun n n_ih => succ n`, `ihs ≠ []`). Both stages are closed `Expr`
computations, hence `rfl`. -/

/-- The η-wrapper Lean's `Option.casesOn` inserts for the one-field minor:
`fun val => minor val`. -/
private def someW : Expr := .lam `v ty (.app A4 (.bvar 0)) .default

/-- `Option.rec`'s `some` rule template: `fun α motive none some val => some val`.
Inside the body `val = #0`, `some = #1`. -/
private def ruleRhsEtaG : Expr :=
  .lam `a ty (.lam `motive ty (.lam `mnone ty (.lam `msome ty (.lam `field ty
    (.app (.bvar 1) (.bvar 0)) .default) .default) .default) .default) .default

/-- **Stage split at `Option.some`'s shape** (`np = nmot = 1`, `nmin = 2`, one field).
The template reduces to the *η-wrapper* applied to the field — a redex the single-stage
equation could not express — and the wrapper then hands the field to the minor. -/
theorem betaN_ruleTemplate_eta_guard :
    ∃ (wrapper : Expr) (ihs : List Expr),
      betaN ruleRhsEtaG (([A0, A1, A2, someW]).take (1 + 1 + 2) ++ [F0])
        = ([F0] ++ ihs).foldl Expr.app wrapper ∧
      betaN wrapper ([F0] ++ ihs) = ([F0]).foldl Expr.app A4 :=
  ⟨someW, [], rfl, rfl⟩

/-- The IH-discarding wrapper Lean's `Nat.casesOn` inserts: `fun n n_ih => minor n`. -/
private def succW : Expr := .lam `n ty (.lam `nih ty (.app A4 (.bvar 1)) .default) .default

/-- `Nat.rec`'s `succ` rule template: `fun motive zero succ n => succ n (R n)`, with
`R n` standing for the recursive call the rule builds. Inside the body `n = #0`,
`succ = #1`. -/
private def ruleRhsRecG : Expr :=
  .lam `motive ty (.lam `mzero ty (.lam `msucc ty (.lam `n ty
    (.app (.app (.bvar 1) (.bvar 0)) (.app (.const `R []) (.bvar 0))) .default)
    .default) .default) .default

/-- **Stage split at `Nat.succ`'s shape** (`np = 0`, `nmot = 1`, `nmin = 2`, one field,
**recursive**). Stage one produces the wrapper applied to the field *and the recursive
call*; stage two **discards** the recursive call — which is precisely the fact that makes
`SEvalDataι.iota`'s fields-only reduct the right one. -/
theorem betaN_ruleTemplate_rec_guard :
    ∃ (wrapper : Expr) (ihs : List Expr),
      betaN ruleRhsRecG (([A1, A2, succW]).take (0 + 1 + 2) ++ [F0])
        = ([F0] ++ ihs).foldl Expr.app wrapper ∧
      betaN wrapper ([F0] ++ ihs) = ([F0]).foldl Expr.app A4 :=
  ⟨succW, [.app (.const `R []) F0], rfl, rfl⟩

end LeanToLambdaBox
