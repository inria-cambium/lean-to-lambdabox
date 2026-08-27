import LeanToLambdaBox.ProjPattern
import LeanToLambdaBox.IotaPattern
import LeanToLambdaBox.SourceEvalData

/-!
# Discharging `ProjConsistent` — the chain, and the one link `ProjShape` does not supply

`ProjPattern.lean` supplies the interface half: `TrProjCtor` (the `TrProj` witness with
its constructor named), `ProjDefeqSpec` (upstream's `TrEnv.proj_defeq` in the
strengthened form it has to be stated in), `ProjShape` (the `rfl`-checkable per-structure
kernel certificate) and `TrExprS.proj_inv'`. This file composes them into
`projConsistent_of_shape`, the `iotaConsistent_of_shape` analogue.

## The chain, and why it is short

```
 (0)  ve = ⟦.proj S i discr⟧                    -- TrExprS.proj_inv'
 (1)  ⇒ TrExprS Δ discr dve  ∧  TrProjCtor env … S i dve ve c
 (2)  hdiscr dve             ⇒ TrExprS Δ (ctor c̄) cve ∧ IsDefEqU dve cve
 (3)  cve = mkApps (const ctor us') cargs'      -- TrExprS.mkApps_inv + const_inv
 (4)  c = ctor                                  -- ProjCtorAgree (see below)
 (5)  ≡ proj  ProjDefeqSpec.proj_defeq at params := cargs'.take np,
                                          fields := cargs'.drop np
 (6)  TrExprS Δ cargs[np+i] cargs'[np+i]        -- straight off the Forall₂ of (3)
```

Step (6) is *free*, and it was the expensive step in ι: the ι reduct is a spine that is
**not** a subterm of the redex, so its `TrExprS` had to be built by application
generation (`TrExprS.mkApps` / `VEnv.HasType.app_inv`, `IotaDischarge.lean`). A
projection's reduct **is** a subterm of the redex, so it is read straight off
`TrExprS.mkApps_inv`'s `List.Forall₂`. No `HasType.app_inv`, no `TrExprS.mkApps`, no
`betaN`, no two-stage η problem, and no new sorry-frontier: this file's declarations
measure the three standard axioms and nothing else.

## ⚠️ `ProjShape` does not discharge the constructor agreement — a design claim that failed

The design (`§3.1` item 3, `§3.2` step (3)) states that `ProjShape`'s `ival.ctors =
[ctor]` conjunct supplies `ProjDefeqSpec`'s missing agreement: *"the structure has
exactly one constructor, so the `TrProj` witness's `ctorName` and the spine's head are
the same name."* **It does not, and cannot.**

`ProjShape` relates `kenv` to `Γ`. The `TrProjCtor` witness's `ctorName` comes from
neither: it is bound by the `env.pats` membership, i.e. it is a fact about the **`VEnv`**.
`ProjShape` never mentions `env`, so no instance of it can constrain that name. The
informal argument silently uses a `kenv`↔`env` alignment — which is exactly what a
`TrEnv` is, and exactly what `ProjDefeqSpec`'s eventual `of_trEnv` discharge will have in
hand.

So the agreement is named here, as `ProjCtorAgree`, in the same idiom and for the same
reason `ProjDefeqSpec` itself is named: it is the *interface*, `TrEnv` is the (future)
implementation, and naming it keeps the obligation one declaration instead of an
assumption smuggled through a certificate that provably cannot carry it. It is a `Prop`
hypothesis, never an axiom, and it is **not** a new trust item of a new kind: it is the
`VEnv`-side half of the same `TrEnv.proj_defeq` statement correction this round already
escalates upstream.

`ProjShape` still earns its place — `projConsistent_of_shape` takes it, and its
`ctorAgreement` accessor is what pins `Γ.ctorArities cn = some (np + nf)` — but it
reaches a caller's constructor only through a `Γ`-side uniqueness side condition (`hone`
below), while `ProjFieldsCoherent` (slice P0, discharged at registration by
`projFieldsCoherent_of_registered`) delivers the same fact with no kernel environment and
no side condition. `projConsistent_of_coh` is therefore the form a registered `Γ` should
use, and `projConsistent_of_shape` the form to quote against a `kenv`.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-- **The pattern/registration constructor agreement.** The constructor named by the ι
rule that `env.pats` registers for structure `S`'s recursor is the constructor `Γ`
registers at index `0` for `S`'s inductive.

This is the hypothesis `TrEnv.proj_defeq` is missing (`ProjPattern.lean`'s section
docstring), pushed one layer down to where the discharge actually needs it, and it is
**not** derivable from `ProjShape`: `ProjShape` relates `kenv` to `Γ` and says nothing
about `env.pats`. See this module's docstring.

It is true for any `env` that a `TrEnv` translated from a `kenv` in which `S` is a
structure — one constructor, so there is only one name the rule could carry — and it is
refuted outright at a `pats`-free `env` (`projCtorAgree_of_noPats`), which is the
negative polarity. -/
def ProjCtorAgree (env : VEnv) (Γ : ErasureCtx) : Prop :=
  ∀ {U : Nat} {Γc : List VExpr} {S ctor c : Name} {i : Nat} {iid : InductiveId}
    {np : Nat} {e e' : VExpr},
    Γ.projs S = some (iid, np) → Γ.ctors ctor = some (iid, 0) →
    TrProjCtor env U Γc S i e e' c → c = ctor

/-- **Negative polarity.** At a `pats`-free environment `TrProjCtor` is uninhabited
(`trProjCtor_refuted`), so the agreement holds by refutation — which is exactly what
makes it a *hypothesis about the environment* rather than a fact about `Γ`. -/
theorem projCtorAgree_of_noPats {env : VEnv} {Γ : ErasureCtx}
    (hp : ∀ (p : Pattern) r, ¬ env.pats p r) : ProjCtorAgree env Γ :=
  fun _ _ h => absurd h (trProjCtor_refuted hp)

/-! ## The payoff -/

/-- **`ProjConsistent` is derivable** from

* `ProjDefeqSpec` — the upstream projection-reduction rule in the strengthened form
  (`ProjPattern.lean`); the round's single interface to `TrEnv.proj_defeq`;
* `ProjCtorAgree` — the constructor agreement `ProjShape` provably cannot supply (see
  the module docstring); and
* the `Γ`-internal arity decomposition `ctorArities cn = np + nf` at the structure's
  registered constructor — supplied either by `ProjFieldsCoherent` (registration route,
  `projConsistent_of_coh`) or by `ProjShape` (certificate route,
  `projConsistent_of_shape`).

The proof is the seven-step chain of the module docstring. Nothing in it builds a
`TrExprS`; the reduct's translation is a component of the redex's own. -/
theorem projConsistent_of_arity {safety : DefinitionSafety} {kenv : Lean.Kernel.Environment}
    {env : VEnv} (henv : env.WF) {Us : List Name} {Γ : ErasureCtx}
    (hspec : ProjDefeqSpec safety kenv env)
    (hagree : ProjCtorAgree env Γ)
    (harity : ∀ {S cn : Name} {iid : InductiveId} {np nf : Nat},
      Γ.projs S = some (iid, np) → Γ.ctorFields iid = some [nf] →
      Γ.ctors cn = some (iid, 0) → Γ.ctorArities cn = some (np + nf)) :
    ProjConsistent env Us Γ := by
  intro Δ S ctor cus cargs iid np nf i ar discr ve
    hΔ hs hctor hnfs har hcargs hi hlt htr hdiscr
  -- (0)/(1) invert the projection node
  obtain ⟨dve, c, htrd, hpc⟩ := htr.proj_inv'
  -- (2) the discriminant's own subject reduction
  obtain ⟨cve, htrsp, hdef⟩ := hdiscr htrd
  -- (3) the spine's translation is a translated head applied to translated arguments
  obtain ⟨hve, cargs', htrhead, hall, rfl⟩ := TrExprS.mkApps_inv htrsp
  obtain ⟨us', _, rfl⟩ := htrhead.const_inv
  -- (4) the agreement. `subst` eliminates the `Γ`-side name in favour of the pattern's
  -- witness, so from here the chain reads `c` where the statement said `ctor`.
  obtain rfl : c = ctor := hagree hs hctor hpc
  -- (5) the arity decomposition, and the two spine lengths it fixes
  have harc := harity hs hnfs hctor
  have harnf : ar = np + nf := by rw [har] at harc; exact Option.some.inj harc
  have hlen : cargs'.length = np + nf := by
    rw [← Lean4Lean.List.Forall₂.length_eq hall]; omega
  have hlt' : np + i < cargs'.length := by omega
  have hpl : (cargs'.take np).length = np := by rw [List.length_take]; omega
  have hfl : (cargs'.drop np).length = nf := by rw [List.length_drop]; omega
  -- (6) `ProjDefeqSpec` fires, at `params ++ fields = cargs'`
  obtain ⟨A, hty⟩ := htrd.wf henv.ordered hΔ
  have hd : env.IsDefEqU Us.length Δ.toCtx dve
      ((VExpr.const c us').mkApps (cargs'.take np ++ cargs'.drop np)) := by
    rw [List.take_append_drop]; exact hdef
  have hstep := hspec.proj_defeq hpc hd hty hpl hfl hi
  -- (7) the reduct's translation is a component of the redex's own
  refine ⟨cargs'[np + i]'hlt', forall2_getElem hall (np + i) hlt hlt', ?_⟩
  have hg : (cargs'.drop np)[i]'(hfl ▸ hi) = cargs'[np + i]'hlt' := by
    simp only [List.getElem_drop]
  exact hg ▸ hstep

/-- **The registration route.** `ProjFieldsCoherent` (slice P0, discharged at
registration by `projFieldsCoherent_of_registered`) delivers the arity fact directly, at
the singleton field-count list the projection rules always carry. This is the form a
registered `Γ` should use — no kernel environment anywhere in it. -/
theorem projConsistent_of_coh {safety : DefinitionSafety} {kenv : Lean.Kernel.Environment}
    {env : VEnv} (henv : env.WF) {Us : List Name} {Γ : ErasureCtx}
    (hspec : ProjDefeqSpec safety kenv env)
    (hagree : ProjCtorAgree env Γ)
    (hpcoh : ProjFieldsCoherent Γ) :
    ProjConsistent env Us Γ :=
  projConsistent_of_arity henv hspec hagree
    (fun hs hnfs hctor => by
      obtain ⟨_, harc⟩ := hpcoh hs hnfs hctor; simpa using harc)

/-- **The certificate route.** `ProjShape.ctorAgreement` delivers the arity
decomposition at the constructor the *certificate* names, which need not syntactically be
the one a caller holds — `Γ.ctors` is an arbitrary map, and two names could in principle
both sit at `(iid, 0)`. `hone` excludes that; it is what "`register_inductive` registered
exactly one constructor for this inductive" says in the data `Γ` carries, and it is
`rfl`-checkable at any concrete `Γ` (`Γproj_ctorsUnique`).

That side condition is the module docstring's finding in operational form: a certificate
about `kenv` reaches a caller's `Γ`-side constructor only through a `Γ`-side uniqueness
fact, and it reaches the `env`-side pattern constructor not at all — hence
`ProjCtorAgree`. -/
theorem projConsistent_of_shape {safety : DefinitionSafety} {kenv : Lean.Kernel.Environment}
    {env : VEnv} (henv : env.WF) {Us : List Name} {Γ : ErasureCtx}
    (hspec : ProjDefeqSpec safety kenv env)
    (hagree : ProjCtorAgree env Γ)
    (hpshape : ProjShape safety kenv Γ)
    (hone : ∀ {c₁ c₂ : Name} {iid : InductiveId},
      Γ.ctors c₁ = some (iid, 0) → Γ.ctors c₂ = some (iid, 0) → c₁ = c₂) :
    ProjConsistent env Us Γ :=
  projConsistent_of_arity henv hspec hagree
    (fun hs hnfs hctor => by
      obtain ⟨ctor', hctor', harc⟩ := hpshape.ctorAgreement hs hnfs
      obtain rfl : ctor' = _ := hone hctor' hctor
      exact harc)

/-! ### Guards

`ProjDefeqSpec` cannot be constructed — that is the point of a named premise, and its one
implementation is upstream's deferred lemma — so the guards are at the halves, exactly as
the ι round's are (`IotaDischarge.lean` records the same boundary for
`iotaConsistent_of_shape`). What is shown here is that the *composition* is not vacuous
in the trivial way: the agreement premise is inhabited at both polarities, and the
`Γ`-side inputs of the discharge fire at the round's fixture. -/

/-- **The agreement holds vacuously at a `pats`-free `env`** — and at `Γproj`, which is a
`Γ` that really does register a structure, so the vacuity is the environment's and not
`Γ`'s. -/
theorem projCtorAgree_Γproj_of_noPats {env : VEnv}
    (hp : ∀ (p : Pattern) r, ¬ env.pats p r) : ProjCtorAgree env Γproj :=
  projCtorAgree_of_noPats hp

/-- **The agreement's conclusion is reachable**: at `Γproj` the constructor it must name
is `AC.mk`, registered at index `0` — so an instance of `ProjCtorAgree Γproj` says
something with content (`c = AC.mk`) rather than something that holds for every `c`. -/
example {env : VEnv} (h : ProjCtorAgree env Γproj) {U Γc i e e' c}
    (hw : TrProjCtor env U Γc `AC i e e' c) : c = `AC.mk :=
  h Γproj_projs Γproj_ctors hw

/-- **`TrProjCtor` is inhabited at a `pats`-carrying environment**, so the agreement
premise is not about an empty domain — the positive polarity, imported from the P3/P4
witnesses. -/
example : TrProjCtor envQ 0 ΓqV `MyOfNat 0 (.bvar 0) (eProjQ (.bvar 0)) `MyOfNat.mk :=
  trProjCtorQ_bvar

/-- **The certificate route's side condition is `rfl`-checkable**: at `Γproj` only
`AC.mk` sits at constructor index `0`, so `projConsistent_of_shape`'s `hone` is a fact
about the fixture and not a further assumption. -/
theorem Γproj_ctorsUnique {c₁ c₂ : Name} {iid : InductiveId}
    (h₁ : Γproj.ctors c₁ = some (iid, 0)) (h₂ : Γproj.ctors c₂ = some (iid, 0)) :
    c₁ = c₂ := by
  by_cases hc₁ : c₁ = `AC.mk <;> by_cases hc₂ : c₂ = `AC.mk
  · rw [hc₁, hc₂]
  · simp [Γproj, if_neg hc₂] at h₂
  · simp [Γproj, if_neg hc₁] at h₁
  · simp [Γproj, if_neg hc₁] at h₁

/-- …so the two routes agree at the fixture: `ProjFieldsCoherent Γproj` is what
`EnvErasureNonrec`'s `projFieldsCoherent_of_registered` delivers there, and it is exactly
what the certificate route would have had to reconstruct. -/
example : Γproj.ctorArities `AC.mk = some (1 + 1) := Γproj_arity

end LeanToLambdaBox
