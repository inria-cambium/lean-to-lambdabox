import LeanToLambdaBox.IotaPattern
import LeanToLambdaBox.SourceEvalData

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
