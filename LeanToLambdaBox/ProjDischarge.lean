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
assumption smuggled through a certificate that provably cannot carry it. Like
`ProjDefeqSpec` it is a `Prop` hypothesis, **never an axiom** — the round's two
upstream-gated items are both premises — and it is **not** a new trust item of a new
kind: it is the `VEnv`-side half of the same `TrEnv.proj_defeq` statement correction this
round already escalates upstream.

## ✅ …and the implementation arrived (re-pin `b6a5a38`)

The prediction above — *"`TrEnv` is what the eventual discharge will have in hand"* — is
now a theorem. `projCtorAgree_of_trEnv` derives `ProjCtorAgree` from a `TrEnv` plus
`ProjRecRules`, on upstream's new `TrEnv.pats_iota_inv` (the converse of `pats_iota'`,
delivered **fully proved and `sorryAx`-free**). The derivation is `sorryAx`-free too.

The one thing upstream did *not* deliver is the specialization that would have made the
discharge premise-free: `pats_iota_ctor`, folding in the recursor-rules ↔ `ival.ctors`
correspondence, is blocked because `VInductDecl.WF` does not pin the recursor/rule shape
at the inductive-translation boundary. So the fact moves rather than vanishes — but it
moves *from* the `VEnv`, where no downstream certificate can reach it, *to* `kenv`, where
`ProjShape` already states facts of exactly that class. That is the whole content of the
trade, and it is the one the round-2 ask sanctioned in advance.

`ProjDefeqSpec` is therefore the projection round's **single** remaining upstream-gated
premise. Its statement was corrected at the same re-pin (upstream adopted `TrProjCtor`
verbatim); only its proof is outstanding.

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

/-! ### The positive discharge (re-pin `b6a5a38`)

The module docstring's finding stands — `ProjShape` cannot reach the `env.pats`-side
name — but the *route* it named as future work is now open. `TrEnv.pats_iota_inv`, the
converse of `pats_iota'`, is the `kenv`↔`env` alignment the informal argument was
silently using: from a registered ι pattern it recovers the kernel recursor `rval` under
`recName` and the rule keyed by the pattern's constructor. That turns the agreement from a
fact about an opaque `VEnv` into a fact about `kenv`'s recursor rules — which is the class
of fact `ProjShape` already carries, and which a certificate *can* state. -/

/-- **The kernel-side half of the agreement.** For every structure `S` that `Γ` registers,
`S`'s recursor is resolvable in `kenv` and every one of its ι rules is keyed by the
constructor `Γ` registers at index `0`.

This is a `kenv` fact of exactly the class `ProjShape`'s `find?` conjuncts are, and it is
the *one* ingredient upstream did not deliver: the round-2 ask proposed a specialization
`TrEnv.pats_iota_ctor` folding in the recursor-rules ↔ `ival.ctors` correspondence, and it
came back **not landed**, because lean4lean's `VInductDecl.WF` does not pin the
recursor/rule shape at the inductive-translation boundary. The ask sanctioned this
fallback explicitly ("2a alone is acceptable: downstream can bridge with a kernel-side
rules↔ctors fact, at the cost of an extra premise"), and this is that premise.

For a real Lean structure it is a kernel well-formedness triviality — `S.rec` has one rule
per constructor and a structure has one constructor — but a `Kernel.Environment` is opaque
in-logic, so it is stated rather than computed, exactly like `ProjShape.shape`. -/
def ProjRecRules (kenv : Lean.Kernel.Environment) (Γ : ErasureCtx) : Prop :=
  ∀ {S ctor : Name} {iid : InductiveId} {np : Nat},
    Γ.projs S = some (iid, np) → Γ.ctors ctor = some (iid, 0) →
    ∃ rval : Lean.RecursorVal,
      kenv.find? (mkRecName S) = some (.recInfo rval) ∧
      ∀ rule ∈ rval.rules, rule.ctor = ctor

/-- **`ProjCtorAgree` is a theorem at a translated environment.** The upstream-gated row it
used to be is discharged here, from a `TrEnv` — the `kenv`↔`env` alignment the module
docstring identified as the missing ingredient — plus the kernel certificate above.

The proof is the four-step bridge: destructure `TrProjCtor` for its `env.pats` membership
and `recName = mkRecName S`; invert it with `TrEnv.pats_iota_inv` to a kernel recursor and
the rule keyed by the witness's constructor `c`; match that recursor against the
certificate's; and read `c = ctor` off `List.find?`. Nothing here is deferred: it is
`sorryAx`-free, and so is `pats_iota_inv` itself.

What this does **not** discharge is `ProjDefeqSpec` — that is the other half of the same
statement correction, and its proof is still `sorry` upstream. So a `TrEnv`-holding caller
now supplies one of `projConsistent_of_coh`'s two upstream-gated premises for real, and
takes the other on trust. -/
theorem projCtorAgree_of_trEnv {safety : DefinitionSafety} {kenv : Lean.Kernel.Environment}
    {env : VEnv} {Γ : ErasureCtx} (H : TrEnv safety kenv env)
    (hrr : ProjRecRules kenv Γ) : ProjCtorAgree env Γ := by
  intro _ _ S ctor c _ _ _ _ _ hs hctor hw
  obtain ⟨recName, _, _, fieldTys, np, _, _, r, rfl, hp, -⟩ := hw
  obtain ⟨rval, rule, hrec, hfind, -, -⟩ := H.pats_iota_inv hp
  have hmem := List.mem_of_find?_eq_some hfind
  have hctc : rule.ctor = c := by simpa using List.find?_some hfind
  obtain ⟨rval', hrec', hall⟩ := hrr hs hctor
  rw [hrec'] at hrec
  obtain rfl : rval' = rval := Lean.ConstantInfo.recInfo.inj (Option.some.inj hrec)
  exact hctc.symm.trans (hall rule hmem)

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

/-- **The registration route, at a translated environment** — the shape a `TrEnv`-holding
caller should quote after the `b6a5a38` re-pin. `ProjCtorAgree` is gone from the premise
list, discharged by `projCtorAgree_of_trEnv`; what is left is the kernel certificate
`ProjRecRules` (in-logic-unconstructible, like `ProjShape`'s `find?` conjuncts, but a
kernel triviality), the registration-side `ProjFieldsCoherent`, and `ProjDefeqSpec` —
**the one genuinely upstream-gated premise of the projection round**, and the only one
whose implementation is still `sorry`. -/
theorem projConsistent_of_coh_trEnv {safety : DefinitionSafety}
    {kenv : Lean.Kernel.Environment} {env : VEnv} (henv : env.WF) {Us : List Name}
    {Γ : ErasureCtx} (H : TrEnv safety kenv env)
    (hspec : ProjDefeqSpec safety kenv env)
    (hrr : ProjRecRules kenv Γ)
    (hpcoh : ProjFieldsCoherent Γ) :
    ProjConsistent env Us Γ :=
  projConsistent_of_coh henv hspec (projCtorAgree_of_trEnv H hrr) hpcoh

/-! ### Guards

`ProjDefeqSpec` cannot be constructed *soundly* — its one implementation is upstream's
still-deferred lemma, and `ProjDefeqSpec.of_trEnv` (`ProjPattern.lean`) exists only to
price that deferral — so the guards are at the halves, exactly as the ι round's are
(`IotaDischarge.lean` records the same boundary for `iotaConsistent_of_shape`). What is
shown here is that the *composition* is not vacuous in the trivial way: the agreement
premise is inhabited at both polarities, and the `Γ`-side inputs of the discharge fire at
the round's fixture.

Since the re-pin the agreement is no longer only inhabited — it is **derived**
(`projCtorAgree_of_trEnv`), so the guard that matters for it is that its new kernel
premise costs nothing where the round's old `hnoprojs` guard sat. -/

/-- **`ProjRecRules` is free at a `Γ` that registers no structure.** The premise
`projCtorAgree_of_trEnv` trades `ProjCtorAgree` for is vacuous exactly where the whole
projection column is, so threading it through the pre-projection cone costs nothing — the
same property `ProjBridgeHyps.of_bot` has, and the reason the trade is a trade rather than
a new assumption. -/
theorem projRecRules_of_noProjs {kenv : Lean.Kernel.Environment} {Γ : ErasureCtx}
    (h : Γ.projs = fun _ => none) : ProjRecRules kenv Γ := by
  intro S _ _ _ hs _; rw [h] at hs; exact absurd hs (by simp)

/-- **…and it is not free at `Γproj`**, which does register one — so the premise has
content exactly where the discharge needs it, and the guard above is measuring vacuity
rather than asserting it. -/
example : ¬ (Γproj.projs = fun _ => none) := by
  intro h; have := congrFun h `AC; rw [Γproj_projs] at this; simp at this

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
