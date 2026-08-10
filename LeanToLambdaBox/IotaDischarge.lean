import LeanToLambdaBox.IotaPattern
import LeanToLambdaBox.SourceEvalData
import LeanToLambdaBox.SubjectReductionFull

/-!
# Discharging `IotaConsistent` — how far the pinned ι interface reaches

`IotaPattern.lean` supplies the pattern-side core: a `Pattern.Matches` introduction
rule for spines, the `SimplePattern.iotaRHS` reduct calculation, `TrExprS` spine
inversion, the named upstream spec `PatsIotaSpec`, and — on top of them —
`iota_defeq_spine`, which **fires** the ι rule on a translated exact-arity redex.
This file records the non-vacuity guard for that machinery and the precise state of
the remaining chain to `IotaConsistent`.

## The chain, and where it stands

For a `casesOn` spine `con pre… discr minors…` whose scrutinee has evaluated to a
saturated constructor spine, `IotaConsistent` asks for a definitional equality to
`(cargs.drop np).foldl Expr.app minors[cidx]`. The chain is

```
 (0)  ve   = ⟦con pre… (ctor C̄) minors…⟧                       -- the source spine
 (1)  ≡ δ    unfold `con` to its value                          -- TrEnv.of_value
 (2)  ≡ β    reduce the casesOn wrapper to the recursor spine
 (3)  ≡ ι    the registered rule fires                          -- iota_defeq_spine  ✔
 (4)  ≡ β    reduce the rule template through its telescope
 (5)  ≡ β    unwrap the casesOn-inserted minor wrapper
           = ⟦minors[cidx] (C̄.drop np)⟧
```

**(3) is done** (`iota_defeq_spine`, `IotaPattern.lean`), modulo the single named
hypothesis `PatsIotaSpec`, and is guarded below.

**(1) is available but `sorry`-tainted at the current pin.** `TrEnv.of_value` routes
through `H.map_wf`, and `TrEnv'.map_wf := H.aligned.map_wf` whose `induct` case is
`Aligned.addInduct`, an IOTA-TODO `sorry` (`Verify/Environment/Lemmas.lean`). This
contradicts the handoff note's "you inherit no new gap", which is accurate for
`pats_iota` (deliberately routed through the `Aligned`-free `TrEnv'.constMap_wf`) but
not for the δ-unfold. The fork's `iota-consume` branch de-taints it by swapping
`map_wf → constMap_wf` in `of_value`; we do **not** work around it here.

**(2)/(4)/(5) are β-telescope bookkeeping** over a per-inductive shape certificate
(`casesOn`'s δ-value and the recursor rule's template, both `rfl`-checkable `Expr`
equations for any concrete inductive). They are laborious but unblocked.

## The blocker this workstream found: `TrExprS` for the ι *reduct* spine

`IotaConsistent`'s conclusion demands a **`TrExprS` of an application spine**,
`TrExprS env Us Δ ((cargs.drop np).foldl Expr.app minors[cidx]) bve`. Building a
`TrExprS.app` node requires its two `HasType` fields — `HasType f' (.forallE A B)`
and `HasType a' A` — and that spine is well-typed only *because* of the ι reduction:
it is not a subterm of the redex, so no app node of the input supplies them.

Recovering them needs a **`HasType` application-generation lemma**
(`HasType Γ (.app f a) V → ∃ A B, HasType f (.forallE A B) ∧ HasType a A`), which the
pinned lean4lean does **not** prove outside `Experimental/` (`Theory/Typing/Lemmas.lean`
has `HasType.forallE_inv` and `HasType.sort_inv` — inversion of forallE/sort *terms*,
not of applications; `Theory/Typing/Injectivity.lean` has only `IsDefEqU.forallE_inv`).
`Experimental/NormalEq.lean` states `app_inv` as a *field of a hypothesis class*, i.e.
as an assumption, not a theorem.

There is a route that does not need general generation — uniqueness of types
(`VEnv.IsDefEq.uniqU`) against the *registered* constant type
(`TrExprS.const` carries `env.constants c = some ci`, and `HasType.const` needs
nothing more), then `IsDefEqU.forallE_inv` to peel the telescope — but it additionally
requires tying the recursor's telescope domains to the rule template's binder types,
which is a further kernel fact beyond the `PatsIotaSpec` bundle. That is the natural
next increment; it is *not* discharged here, and no hypothesis stands in for it.

## Non-vacuity guard

Per the standing discipline every hypothesis-bearing theorem ships a **constructed**
guard. `iota_defeq_spine`'s content is the ι rule firing, so the guard below builds a
`VEnv` by `VEnv.addPat` directly (deliberately *not* through `TrEnv`: `TrEnv` for an
environment containing inductives is unconstructible at this pin —
`addDecl.WF`'s `inductDecl` case is `sorry`) and shows a *real* `IsDefEqU`.

The shape is chosen to exercise the `take`/`drop` conventions of
`SimplePattern.iotaRHS_apply`: `np = nmot = nmin = nind = nfields = 1`, so **both**
`np > 0` and `nind > 0`. With `np = nind = 0` (`Bool`, enums) both slices degenerate
to the identity and a reversed convention would still look right; here the six
arguments are pairwise distinct (`bvar 0 … bvar 5`) and the reduct visibly drops
`bvar 3` — the recursor's **index**, which sits between the minors and the major
premise — and `bvar 4` — the constructor's **parameter** — keeping
`[bvar 0, bvar 1, bvar 2]` (params/motives/minors) and `[bvar 5]` (the field).
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-! ## Steps (2)/(4)/(5): the β-normalisation engine

Steps (2), (4) and (5) of the chain are all the same operation — apply a source
λ-telescope to a list of arguments and β-reduce — so they share one engine.

The key point is that a β step produces the reduct's `TrExprS` **for free**, via
`TrExprS.inst`: no application node has to be built, so none of the `HasType`
premises that block the ι *reduct* (see the module docstring) are needed here. The
engine is therefore fully proved. What is still missing, to compose it into a
derivation of `IotaConsistent`, is the per-inductive shape certificate (which `Expr`
the `casesOn` δ-unfolds to, and what the recursor rule's template is) and the
ι-reduct `TrExprS` discussed in the module docstring. -/

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

end LeanToLambdaBox
