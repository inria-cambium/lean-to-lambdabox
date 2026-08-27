import Lean4Lean.Verify.Environment.Lemmas
import Lean4Lean.Verify.Typing.Lemmas
import LeanToLambdaBox.Erases
import LeanToLambdaBox.ErasesUniform

/-!
# The projection pattern interface: the first constructed `TrProj`

At the `fee3ada` re-pin, `TrProj` (`Lean4Lean/Verify/Typing/Expr.lean`) stopped being a
`sorry` and became a real definition — a *recursor expansion*. `VExpr` has no projection
node, so a source `Expr.proj S i e` is translated to the structure's recursor applied to
the parameters, a motive, the **field selector** `fun f₀ … f_{n-1} => fᵢ`, and the major
premise. At `7a5e96d` the motive stopped being existential and was pinned to the constant
one, which is the shape this file is written against:

```lean
def TrProj (env : VEnv) (U : Nat) (Γ : List VExpr)
    (S : Name) (i : Nat) (e e' : VExpr) : Prop :=
  ∃ (recName ctorName : Name) (us : List VLevel) (params fieldTys : List VExpr)
    (np : Nat) (structTy fieldTy : VExpr) (r : … .RHS × … .Check),
    recName = mkRecName S ∧
    env.pats (SimplePattern.iota recName (np+1+1+0) ctorName (np+fieldTys.length)).toPattern r ∧
    params.length = np ∧ i < fieldTys.length ∧
    env.HasType U Γ e structTy ∧
    e' = (VExpr.const recName us).mkApps
           (params ++ [.lam structTy fieldTy.lift, VExpr.fieldSelector fieldTys i, e]) ∧
    env.HasType U Γ e' fieldTy
```

Nine binders, seven conjuncts. The two `HasType`s are what pin `structTy` and `fieldTy`,
and through them the motive.

**Nobody had ever constructed one** — no `example`, no test, upstream or down. Every
downstream statement about projections was therefore possibly vacuous, and the whole
projection round rests on the answer. This file settles it: **`TrProj` is inhabited, and
so is `TrExprS` at a `.proj` node.**

## What is here

A synthetic structure, registered exactly the way `VEnv.addInduct` would register it:

```lean
structure MyProd (α : Type) where
  mk :: (fst : α) (snd : α)
```

— one parameter, one constructor, **two** fields, no indices, non-recursive: the
`is_struct` shape `register_inductive` (`Erasure.lean`) gates on, and the shape whose
recursor has `numMotives = numMinors = 1`, `numIndices = 0` — i.e. `TrProj`'s hard-wired
`np+1+1+0`.

* `envP` — a `VEnv` with `N`, `MyProd`, `MyProd.mk`, `MyProd.rec` and **one ι rule**
  registered by `VEnv.addPat`, at the honest `SimplePattern.iotaRHS` shape. Built by
  `addPat` rather than `addInduct` for the same reason `envι` (`IotaDischarge.lean`) is:
  `VEnv.Ordered` has no `addPat` clause and `addInduct_WF` is `sorry` upstream, so a
  `VEnv.WF`-carrying guard is not available at this pin and is not claimed.
* `trProjP_bvar 0/1` and `trProjP_ctor 0/1` — **four positive `TrProj` witnesses**, at a
  variable discriminant and at a saturated constructor spine `MyProd.mk N x y`, for
  *both* fields.
* `trExprSP_proj_bvar` / `trExprSP_proj_ctor` — the second half: `TrExprS` at a real
  `Expr.proj`, via `TrExprS.proj` over those witnesses.
* `trProj_refuted` — the negative polarity: no `TrProj` at a `pats`-free environment.

Since slice **P4** the file also carries the *interface* layer the round consumes:

* `TrProjCtor` — `TrProj` with its constructor witness named, and the two conversions
  (`toTrProj`, `TrProj.exists_ctorName`) that make it a reparenthesisation rather than a
  strengthening;
* `ProjDefeqSpec` — the projection-reduction rule as a **named premise**, stated over
  `TrProjCtor` because the upstream `TrEnv.proj_defeq` is missing the agreement between
  its two constructor names and is therefore likely unprovable as written (see §"Why the
  upstream statement is not the one to plan on" below);
* `ProjShape` — the `rfl`-checkable per-structure certificate, and
  `ProjShape.ctorAgreement`, the accessor that supplies `ProjDefeqSpec`'s missing
  hypothesis locally;
* `TrExprS.proj_inv` / `proj_inv'` — total inversion at a `.proj` source.

All `sorryAx`-free (audited in `scratch/final_audit.lean`). In particular
`ProjDefeqSpec.of_trEnv` is deliberately **not** here: it would be one line, and it would
be this development's only `sorryAx` provenance.

## The recipe, for the slices that follow

Five of the seven conjuncts are `rfl`, `VEnv.addPat_self` and `by simp`; a sixth,
`env.HasType U Γ e structTy`, is the discriminant's own typing, which every caller has
anyway and `trProjP` therefore takes as a parameter. **The whole cost is the last one,
`env.HasType U Γ e' fieldTy`**, and it decomposes as:

1. `HasType.const` for the recursor at its own type — with `ci.type.instL [] = ci.type`
   by `rfl` at a monomorphic guard.
2. Three `HasType.app` steps whose result types `B.inst a` are `rfl`-computable, so each
   intermediate type can simply be *written down*.
3. **One conversion, and it is the only interesting step.** The recursor's minor premise
   has type `∀ (f₀ f₁ : α), motive (MyProd.mk α f₀ f₁)`, while the field selector
   `fun f₀ f₁ => fᵢ` naturally has type `∀ (f₀ f₁ : α), α`. The *constant* motive
   `fun _ : MyProd N => N` makes the two definitionally equal by **one β step** under two
   `forallEDF` congruences (`hconvP`). That is the whole trick, and it is the reason a
   non-dependent structure goes through by β alone.
4. **One more β step, on the way out.** The recursor spine's own type is `motive d`, not
   `fieldTy`, and the definition now demands the latter on the nose. `hEProj*raw` proves
   the former; `hEProj*` converts by `VEnv.IsDefEq.beta`, which is `rfl`-cheap here
   because `Nty` is closed and so `Nty.lift = Nty` and `Nty.inst d = Nty`. Since
   `.lam structTy fieldTy.lift` is *definitionally* the `motiveP` this file already used,
   the spine equation stayed `rfl` across the `7a5e96d` re-pin.

Step 3 also draws the **exact** line between the easy and the hard case, which is the
answer this file owes survey item R2 (*"can the `HasType` conjunct be met at a dependent
structure?"*). Upstream's `7a5e96d` docstring now draws the same line from the other
side, and declares it the definition's **scope** rather than a choice a witness makes:
the constant motive is correct exactly for non-dependent fields, and the dependent case
would need structure-η in `IsDefEq` or a dependent motive. The two analyses were reached
independently and agree. Concretely: the constant motive `fun _ => T` discharges step 3
iff `T` can be chosen closed with respect to the field binders — i.e. iff `fieldTys[i]`,
which sits under the binders `f₀ … f_{i-1}` of the selector telescope, **does not mention
them**. So:

* **field `0` of *any* structure is as easy as this file**, dependent or not: the first
  field's type is fixed before any field is bound. `Subtype.val`, `Sigma.fst`,
  `OfNat.ofNat` and every one-field class are in this case;
* a field `i > 0` whose type genuinely depends on an earlier field (`Sigma.snd : β fst`)
  needs the honest motive `fun p => β p.0`, which mentions a projection itself — so step
  3 becomes β **plus a firing of the ι rule** (`VEnv.IsDefEq.pat`, which `envP` does
  register, via `Pattern.matches_iota`). Inhabitable by the same kit, materially more
  work, and **not attempted here**.

Nothing in `Erases.proj`'s planned premises (`Γ.projs`, `Γ.ctorFields`, `i < nf`)
restricts to the easy case, so the open half of R2 is a real residue — but it is a
narrow one, it is now *upstream's* residue rather than this file's, and it does not touch
the typeclass-dispatch payoff, whose methods are all field `0` or fields whose types are
independent of the earlier ones.

## Scope notes

* **Monomorphic by construction.** `us = []`, `U = 0`, `uvars = 0` throughout, so
  `instL` is the identity and no level bookkeeping appears. A universe-polymorphic
  witness would ride `TrProj.instL` (proved in the delivery); it is not needed to answer
  the inhabitation question and is not attempted.
* **The motive is pinned; `fieldTys` is not.** Since `7a5e96d` the motive is forced to
  `.lam structTy fieldTy.lift`, and the two `HasType` conjuncts fix `structTy` and
  `fieldTy` — which is what took `TrProj.uniq` from *false* to merely unproved. `params`
  and `fieldTys` remain existential and constrained only up to definitional equality,
  which is still `TrProj.uniq`'s reason for claiming `IsDefEqU` and not equality, and
  still why on-the-nose `TrExprS.unique` at `.proj` is unavailable. The witnesses below
  pick the natural ones.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-! ### The guard structure

```lean
structure MyProd (α : Type) where
  mk :: (fst : α) (snd : α)
```

with a single base type `N : Type` to instantiate the parameter at. Everything is
monomorphic: the recursor's motive is fixed at `Sort 1` rather than universe-polymorphic,
which is the one place this differs from what `addInduct` would build and which costs
nothing, since `TrProj` quantifies `us` existentially and `instL []` is the identity. -/

/-- `Type`, i.e. `Sort 1`. -/
def Ty1 : VExpr := .sort (.succ .zero)

/-- The base type `N : Type` the structure parameter is instantiated at. -/
def Nty : VExpr := .const `N []

/-- The structure type constant `MyProd : Type → Type`. -/
def MPc : VExpr := .const `MyProd []

/-- The constructor `MyProd.mk : ∀ (α : Type), α → α → MyProd α`. -/
def MKc : VExpr := .const `MyProd.mk []

/-- The recursor `MyProd.rec`. -/
def MRc : VExpr := .const `MyProd.rec []

/-- `MyProd N`. -/
def PN : VExpr := .app MPc Nty

def MPty : VExpr := .forallE Ty1 Ty1

/-- `∀ (α : Type) (fst : α) (snd : α), MyProd α`. -/
def MKty : VExpr :=
  .forallE Ty1 (.forallE (.bvar 0) (.forallE (.bvar 1) (.app MPc (.bvar 2))))

/-- `∀ (α : Type) (motive : MyProd α → Type)
      (mk : ∀ (fst snd : α), motive (MyProd.mk α fst snd)) (t : MyProd α), motive t`.

The `numMotives = numMinors = 1`, `numIndices = 0` telescope `TrProj` assumes: the
argument list is `params ++ [motive, minor, major]`. -/
def MRty : VExpr :=
  .forallE Ty1
    (.forallE (.forallE (.app MPc (.bvar 0)) Ty1)
      (.forallE
        (.forallE (.bvar 1)
          (.forallE (.bvar 2)
            (.app (.bvar 2) (.app (.app (.app MKc (.bvar 3)) (.bvar 1)) (.bvar 0)))))
        (.forallE (.app MPc (.bvar 2)) (.app (.bvar 2) (.bvar 0)))))

/-- The four constants, before the ι rule is registered. -/
noncomputable def envPBase : VEnv :=
  ((((((VEnv.empty.addConst `N ⟨0, Ty1⟩).getD .empty).addConst `MyProd ⟨0, MPty⟩).getD .empty
    ).addConst `MyProd.mk ⟨0, MKty⟩).getD .empty).addConst `MyProd.rec ⟨0, MRty⟩ |>.getD .empty

theorem envPBase_N : envPBase.constants `N = some ⟨0, Ty1⟩ := by
  unfold envPBase VEnv.addConst VEnv.empty; simp

theorem envPBase_MP : envPBase.constants `MyProd = some ⟨0, MPty⟩ := by
  unfold envPBase VEnv.addConst VEnv.empty; simp

theorem envPBase_MK : envPBase.constants `MyProd.mk = some ⟨0, MKty⟩ := by
  unfold envPBase VEnv.addConst VEnv.empty; simp

theorem envPBase_MR : envPBase.constants `MyProd.rec = some ⟨0, MRty⟩ := by
  unfold envPBase VEnv.addConst VEnv.empty; simp

/-- The structure recursor's ι rule template:
`fun α motive minor fst snd => minor fst snd`. Fed to `SimplePattern.iotaRHS`, which
applies it to the recursor's `params ++ motives ++ minors` and the constructor's
**fields** (dropping the parameters) — here `[α, motive, minor] ++ [fst, snd]`. -/
def rhsP : VExpr :=
  .lam Ty1
    (.lam (.forallE (.app MPc (.bvar 0)) Ty1)
      (.lam
        (.forallE (.bvar 1)
          (.forallE (.bvar 2)
            (.app (.bvar 2) (.app (.app (.app MKc (.bvar 3)) (.bvar 1)) (.bvar 0)))))
        (.lam (.bvar 2)
          (.lam (.bvar 3)
            (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))))))

theorem rhsP_closed : rhsP.Closed := by
  unfold rhsP MKc MPc Ty1 VExpr.Closed; simp [VExpr.ClosedN]

/-- The guard environment: the four constants plus **one** ι rule, at the structure
shape `np = 1`, `nmotives = nminors = 1`, `nindices = 0`, `nfields = 2` — so the pattern
arity is `1+1+1+0` on the recursor side and `1+2` on the constructor side, which is
literally `TrProj`'s `(np+1+1+0)` / `(np+fieldTys.length)`. -/
noncomputable def envP : VEnv :=
  envPBase.addPat (SimplePattern.iota `MyProd.rec (1+1+1+0) `MyProd.mk (1+2)).toPattern
    (SimplePattern.iotaRHS `MyProd.rec `MyProd.mk 1 1 1 0 2 rhsP rhsP_closed, .true)

theorem envP_N : envP.constants `N = some ⟨0, Ty1⟩ := envPBase_N
theorem envP_MP : envP.constants `MyProd = some ⟨0, MPty⟩ := envPBase_MP
theorem envP_MK : envP.constants `MyProd.mk = some ⟨0, MKty⟩ := envPBase_MK
theorem envP_MR : envP.constants `MyProd.rec = some ⟨0, MRty⟩ := envPBase_MR

/-- `MyProd.rec` really is `mkRecName MyProd` — the first conjunct of `TrProj`, and the
one thing about the recursor's *name* the definition pins. -/
theorem envP_mkRecName : (`MyProd.rec : Name) = mkRecName `MyProd := rfl

/-! ### The typing kit

Everything is stated at an arbitrary `Γ`, because the two families of witnesses below
live at different contexts (`[MyProd N]` and `[N, N]`). -/

theorem hNtyP {Γ} : envP.HasType 0 Γ Nty Ty1 :=
  VEnv.HasType.const envP_N (by simp) (by simp)

theorem hMPc {Γ} : envP.HasType 0 Γ MPc MPty :=
  VEnv.HasType.const envP_MP (by simp) (by simp)

theorem hMKc {Γ} : envP.HasType 0 Γ MKc MKty :=
  VEnv.HasType.const envP_MK (by simp) (by simp)

theorem hMRc {Γ} : envP.HasType 0 Γ MRc MRty :=
  VEnv.HasType.const envP_MR (by simp) (by simp)

theorem hPN {Γ} : envP.HasType 0 Γ PN Ty1 := hMPc.app hNtyP

/-- The saturated constructor spine `MyProd.mk N #1 #0`, under two `N` binders. -/
def mkappP : VExpr := .app (.app (.app MKc Nty) (.bvar 1)) (.bvar 0)

theorem hmkappP {Γ} : envP.HasType 0 (Nty :: Nty :: Γ) mkappP PN :=
  ((hMKc.app hNtyP).app (.bvar (.succ .zero))).app (.bvar .zero)

/-- The **constant** motive `fun _ : MyProd N => N`. Constant is what makes the field
selector fit by one β step; see the module docstring, step 3. Since `7a5e96d` this is
also the only motive `TrProj` admits: it demands `.lam structTy fieldTy.lift`, which at
`structTy = PN`, `fieldTy = Nty` is this term by `rfl` (`Nty` is closed, so
`Nty.lift = Nty`). -/
def motiveP : VExpr := .lam PN Nty

theorem hMotiveP {Γ} : envP.HasType 0 Γ motiveP (.forallE PN Ty1) :=
  VEnv.HasType.lam hPN hNtyP

/-- The field selector `fun (f₀ f₁ : N) => fᵢ`, i.e. `VExpr.fieldSelector [N, N] i`. -/
def selP (i : Nat) : VExpr := VExpr.fieldSelector [Nty, Nty] i

/-- `fieldSelector`'s de Bruijn convention, checked rather than assumed: field `i` is
numbered **from the outside**, so it sits at index `n - 1 - i`. Getting this backwards
would silently select the wrong field. -/
theorem selP_zero : selP 0 = .lam Nty (.lam Nty (.bvar 1)) := rfl
theorem selP_one : selP 1 = .lam Nty (.lam Nty (.bvar 0)) := rfl

theorem hSelP0 {Γ} : envP.HasType 0 Γ (selP 0) (.forallE Nty (.forallE Nty Nty)) :=
  selP_zero ▸ VEnv.HasType.lam hNtyP (VEnv.HasType.lam hNtyP (.bvar (.succ .zero)))

theorem hSelP1 {Γ} : envP.HasType 0 Γ (selP 1) (.forallE Nty (.forallE Nty Nty)) :=
  selP_one ▸ VEnv.HasType.lam hNtyP (VEnv.HasType.lam hNtyP (.bvar .zero))

/-- The type the recursor demands of its minor premise, after the parameter and the
motive have been instantiated: `∀ (f₀ f₁ : N), (fun _ => N) (MyProd.mk N f₀ f₁)`. -/
def selTyP : VExpr := .forallE Nty (.forallE Nty (.app motiveP mkappP))

/-- **The conversion — the only non-mechanical step.** The field selector's natural type
`∀ (f₀ f₁ : N), N` is definitionally the minor premise's type, by one β step under two
`forallEDF` congruences. -/
theorem hconvP {Γ} : envP.IsDefEq 0 Γ (.forallE Nty (.forallE Nty Nty)) selTyP
    (.sort (.imax (.succ .zero) (.imax (.succ .zero) (.succ .zero)))) :=
  .forallEDF hNtyP (.forallEDF hNtyP (VEnv.IsDefEq.beta hNtyP hmkappP).symm)

/-- The translation of `MyProd.i d`: `MyProd.rec N (fun _ => N) (fun f₀ f₁ => fᵢ) d`. -/
def eProj (i : Nat) (d : VExpr) : VExpr :=
  (VExpr.const `MyProd.rec []).mkApps ([Nty] ++ [motiveP, selP i, d])

/-! The recursor spine's own type is `motive d`. `TrProj` demands `fieldTy` on the nose,
so each `hEProj*` is a `raw` derivation at `.app motiveP d` followed by one β step. The
step is cheap only because the motive is constant and `Nty` is closed, so `Nty.inst d`
is `Nty` — the same fact that makes the conversion in `hconvP` work, used on the way out
instead of on the way in. -/

theorem hEProj0raw {Γ} {d} (hd : envP.HasType 0 Γ d PN) :
    envP.HasType 0 Γ (eProj 0 d) (.app motiveP d) := by
  have h := (((hMRc.app hNtyP).app hMotiveP).app (hconvP.defeq hSelP0)).app hd
  simpa [eProj, MRc, motiveP, PN, Nty, MPc, VExpr.inst, VExpr.lift, VExpr.liftN,
    VExpr.mkApps] using h

theorem hEProj0 {Γ} {d} (hd : envP.HasType 0 Γ d PN) :
    envP.HasType 0 Γ (eProj 0 d) Nty :=
  (VEnv.IsDefEq.beta hNtyP hd).defeq (hEProj0raw hd)

theorem hEProj1raw {Γ} {d} (hd : envP.HasType 0 Γ d PN) :
    envP.HasType 0 Γ (eProj 1 d) (.app motiveP d) := by
  have h := (((hMRc.app hNtyP).app hMotiveP).app (hconvP.defeq hSelP1)).app hd
  simpa [eProj, MRc, motiveP, PN, Nty, MPc, VExpr.inst, VExpr.lift, VExpr.liftN,
    VExpr.mkApps] using h

theorem hEProj1 {Γ} {d} (hd : envP.HasType 0 Γ d PN) :
    envP.HasType 0 Γ (eProj 1 d) Nty :=
  (VEnv.IsDefEq.beta hNtyP hd).defeq (hEProj1raw hd)

/-! ### The witnesses -/

/-- The generic `TrProj` introduction at this structure: any well-typed discriminant of
type `MyProd N`, either field. `hd` is the `structTy` conjunct `7a5e96d` added — the
caller has it anyway, since it is what `hEProj*` needs. -/
theorem trProjP {Γ} {i} {d} (hi : i < 2)
    (hd : envP.HasType 0 Γ d PN)
    (h : envP.HasType 0 Γ (eProj i d) Nty) :
    TrProj envP 0 Γ `MyProd i d (eProj i d) :=
  ⟨`MyProd.rec, `MyProd.mk, [], [Nty], [Nty, Nty], 1, PN, Nty,
    (SimplePattern.iotaRHS `MyProd.rec `MyProd.mk 1 1 1 0 2 rhsP rhsP_closed, .true),
    envP_mkRecName, VEnv.addPat_self, rfl, by simpa using hi, hd, rfl, h⟩

/-- `Γ = [p : MyProd N]` — a variable discriminant. -/
def ΓpV : List VExpr := [PN]

theorem hdV : envP.HasType 0 ΓpV (.bvar 0) PN := .bvar .zero

/-- **THE WITNESS.** `TrProj` is inhabited: the first field of `MyProd N` at a variable
discriminant. -/
theorem trProjP_bvar0 : TrProj envP 0 ΓpV `MyProd 0 (.bvar 0) (eProj 0 (.bvar 0)) :=
  trProjP (by omega) hdV (hEProj0 hdV)

/-- The second field — so the guard is not degenerate in `fieldSelector`'s index. -/
theorem trProjP_bvar1 : TrProj envP 0 ΓpV `MyProd 1 (.bvar 0) (eProj 1 (.bvar 0)) :=
  trProjP (by omega) hdV (hEProj1 hdV)

/-- `Γ = [x : N, y : N]` — the discriminant is the saturated constructor spine
`MyProd.mk N x y`, which is the shape `TrEnv.proj_defeq` and hence the whole
`ProjConsistent` discharge (slice P5) will consume. -/
def ΓpC : List VExpr := [Nty, Nty]

theorem hdC : envP.HasType 0 ΓpC mkappP PN := hmkappP

theorem trProjP_ctor0 : TrProj envP 0 ΓpC `MyProd 0 mkappP (eProj 0 mkappP) :=
  trProjP (by omega) hdC (hEProj0 hdC)

theorem trProjP_ctor1 : TrProj envP 0 ΓpC `MyProd 1 mkappP (eProj 1 mkappP) :=
  trProjP (by omega) hdC (hEProj1 hdC)

/-! ### `TrExprS` at a `.proj` node

The second half of the kill-check: the `TrExprS.proj` constructor, applied to the
witnesses above. This is `DeltaHyps.prepared`'s second conjunct in miniature — the
conjunct the projection round exists to make satisfiable. -/

/-- `Δ = [p : MyProd N]`, whose `toCtx` is `ΓpV`. -/
def ΔpV : VLCtx := [(none, .vlam PN)]

theorem ΔpV_toCtx : ΔpV.toCtx = ΓpV := rfl

/-- **The second half.** `TrExprS` accepts a real `Expr.proj`. -/
theorem trExprSP_proj_bvar :
    TrExprS envP [] ΔpV (.proj `MyProd 0 (.bvar 0)) (eProj 0 (.bvar 0)) :=
  .proj (.bvar (by rfl)) trProjP_bvar0

theorem trExprSP_proj_bvar1 :
    TrExprS envP [] ΔpV (.proj `MyProd 1 (.bvar 0)) (eProj 1 (.bvar 0)) :=
  .proj (.bvar (by rfl)) trProjP_bvar1

/-- `Δ = [x : N, y : N]`, whose `toCtx` is `ΓpC`. -/
def ΔpC : VLCtx := [(none, .vlam Nty), (none, .vlam Nty)]

theorem ΔpC_toCtx : ΔpC.toCtx = ΓpC := rfl

/-- The source-side constructor application `MyProd.mk N x y`. -/
def mkappSrc : Expr :=
  .app (.app (.app (.const `MyProd.mk []) (.const `N [])) (.bvar 1)) (.bvar 0)

theorem trExprS_mkappSrc : TrExprS envP [] ΔpC mkappSrc mkappP :=
  .app ((hMKc.app hNtyP).app (.bvar (.succ .zero))) (.bvar .zero)
    (.app (hMKc.app hNtyP) (.bvar (.succ .zero))
      (.app hMKc hNtyP
        (.const envP_MK (by simp) (by simp))
        (.const envP_N (by simp) (by simp)))
      (.bvar (by rfl)))
    (.bvar (by rfl))

/-- …and at a compound discriminant, so the `TrExprS Δ e e'` premise of `TrExprS.proj`
is doing work rather than being a variable lookup. -/
theorem trExprSP_proj_ctor :
    TrExprS envP [] ΔpC (.proj `MyProd 0 mkappSrc) (eProj 0 mkappP) :=
  .proj trExprS_mkappSrc trProjP_ctor0

/-! ### The negative polarity

Non-vacuity cuts both ways: at an environment that registers no ι rule, `TrProj` is
uninhabited — so the witnesses above are *about* the registration, not artefacts of a
degenerate definition. (This direction compiled before the witnesses did; it is the half
the earlier survey already had.) -/

theorem trProj_refuted {env : VEnv} {U Γ S i e e'}
    (hp : ∀ (p : Pattern) r, ¬ env.pats p r) : ¬ TrProj env U Γ S i e e' := by
  rintro ⟨_, _, _, _, _, _, _, _, _, _, hpat, _⟩
  exact hp _ _ hpat

theorem trProj_refuted_empty {U Γ S i e e'} : ¬ TrProj .empty U Γ S i e e' :=
  trProj_refuted fun _ _ h => h

/-! ### The payoff shape: a one-field type class

`MyProd` answers the inhabitation question at the shape that stresses `fieldSelector`'s
index arithmetic (`nf = 2`). The *payoff* shape — the one the design's `OfNat.ofNat`
trace runs through — is a **type class**: two parameters, one field.

```lean
class MyOfNat (α : Type) (n : N) where
  mk :: (ofNat : α)
```

so `np = 2` and `nf = 1`, and `TrProj`'s pattern arities become `2+1+1+0` and `2+1`. The
construction is the same five `rfl`s and the same single β conversion; what it adds is
that `params` is a **two**-element list, so the `params ++ [motive, selector, major]`
append is not degenerate. `MyOfNat.ofNat`'s prepared body `fun α x self => self.1` is
`DeltaHyps.prepared`'s hard conjunct, and this is the `TrProj` it needs. -/

/-- A closed inhabitant of `N`, to instantiate the class's second (value) parameter. -/
def n0c : VExpr := .const `n0 []

def QCc : VExpr := .const `MyOfNat []
def QKc : VExpr := .const `MyOfNat.mk []
def QRc : VExpr := .const `MyOfNat.rec []

/-- `MyOfNat N n0`. -/
def QN : VExpr := .app (.app QCc Nty) n0c

def QCty : VExpr := .forallE Ty1 (.forallE Nty Ty1)

/-- `∀ (α : Type) (n : N) (ofNat : α), MyOfNat α n`. -/
def QKty : VExpr :=
  .forallE Ty1 (.forallE Nty (.forallE (.bvar 1) (.app (.app QCc (.bvar 2)) (.bvar 1))))

/-- `∀ (α : Type) (n : N) (motive : MyOfNat α n → Type)
      (mk : ∀ (ofNat : α), motive (MyOfNat.mk α n ofNat)) (t : MyOfNat α n), motive t`. -/
def QRty : VExpr :=
  .forallE Ty1
    (.forallE Nty
      (.forallE (.forallE (.app (.app QCc (.bvar 1)) (.bvar 0)) Ty1)
        (.forallE
          (.forallE (.bvar 2)
            (.app (.bvar 1) (.app (.app (.app QKc (.bvar 3)) (.bvar 2)) (.bvar 0))))
          (.forallE (.app (.app QCc (.bvar 3)) (.bvar 2)) (.app (.bvar 2) (.bvar 0))))))

noncomputable def envQBase : VEnv :=
  ((((((((VEnv.empty.addConst `N ⟨0, Ty1⟩).getD .empty).addConst `n0 ⟨0, Nty⟩).getD .empty
    ).addConst `MyOfNat ⟨0, QCty⟩).getD .empty).addConst `MyOfNat.mk ⟨0, QKty⟩).getD .empty
    ).addConst `MyOfNat.rec ⟨0, QRty⟩ |>.getD .empty

theorem envQBase_N : envQBase.constants `N = some ⟨0, Ty1⟩ := by
  unfold envQBase VEnv.addConst VEnv.empty; simp
theorem envQBase_n0 : envQBase.constants `n0 = some ⟨0, Nty⟩ := by
  unfold envQBase VEnv.addConst VEnv.empty; simp
theorem envQBase_QC : envQBase.constants `MyOfNat = some ⟨0, QCty⟩ := by
  unfold envQBase VEnv.addConst VEnv.empty; simp
theorem envQBase_QK : envQBase.constants `MyOfNat.mk = some ⟨0, QKty⟩ := by
  unfold envQBase VEnv.addConst VEnv.empty; simp
theorem envQBase_QR : envQBase.constants `MyOfNat.rec = some ⟨0, QRty⟩ := by
  unfold envQBase VEnv.addConst VEnv.empty; simp

/-- `fun α n motive minor ofNat => minor ofNat`. -/
def rhsQ : VExpr :=
  .lam Ty1
    (.lam Nty
      (.lam (.forallE (.app (.app QCc (.bvar 1)) (.bvar 0)) Ty1)
        (.lam
          (.forallE (.bvar 2)
            (.app (.bvar 1) (.app (.app (.app QKc (.bvar 3)) (.bvar 2)) (.bvar 0))))
          (.lam (.bvar 3) (.app (.bvar 1) (.bvar 0))))))

theorem rhsQ_closed : rhsQ.Closed := by
  unfold rhsQ QKc QCc Nty Ty1 VExpr.Closed; simp [VExpr.ClosedN]

/-- The class environment, with its ι rule at `np = 2`, `nfields = 1`. -/
noncomputable def envQ : VEnv :=
  envQBase.addPat (SimplePattern.iota `MyOfNat.rec (2+1+1+0) `MyOfNat.mk (2+1)).toPattern
    (SimplePattern.iotaRHS `MyOfNat.rec `MyOfNat.mk 2 1 1 0 1 rhsQ rhsQ_closed, .true)

theorem envQ_mkRecName : (`MyOfNat.rec : Name) = mkRecName `MyOfNat := rfl

theorem envQ_N : envQ.constants `N = some ⟨0, Ty1⟩ := envQBase_N
theorem envQ_n0 : envQ.constants `n0 = some ⟨0, Nty⟩ := envQBase_n0
theorem envQ_QC : envQ.constants `MyOfNat = some ⟨0, QCty⟩ := envQBase_QC
theorem envQ_QK : envQ.constants `MyOfNat.mk = some ⟨0, QKty⟩ := envQBase_QK
theorem envQ_QR : envQ.constants `MyOfNat.rec = some ⟨0, QRty⟩ := envQBase_QR

theorem hNtyQ {Γ} : envQ.HasType 0 Γ Nty Ty1 :=
  VEnv.HasType.const envQ_N (by simp) (by simp)
theorem hn0c {Γ} : envQ.HasType 0 Γ n0c Nty :=
  VEnv.HasType.const envQ_n0 (by simp) (by simp)
theorem hQCc {Γ} : envQ.HasType 0 Γ QCc QCty :=
  VEnv.HasType.const envQ_QC (by simp) (by simp)
theorem hQKc {Γ} : envQ.HasType 0 Γ QKc QKty :=
  VEnv.HasType.const envQ_QK (by simp) (by simp)
theorem hQRc {Γ} : envQ.HasType 0 Γ QRc QRty :=
  VEnv.HasType.const envQ_QR (by simp) (by simp)

theorem hQN {Γ} : envQ.HasType 0 Γ QN Ty1 := (hQCc.app hNtyQ).app hn0c

/-- The class instance value `MyOfNat.mk N n0 f`, under the field binder. -/
def mkappQ : VExpr := .app (.app (.app QKc Nty) n0c) (.bvar 0)

theorem hmkappQ {Γ} : envQ.HasType 0 (Nty :: Γ) mkappQ QN :=
  ((hQKc.app hNtyQ).app hn0c).app (.bvar .zero)

def motiveQ : VExpr := .lam QN Nty

theorem hMotiveQ {Γ} : envQ.HasType 0 Γ motiveQ (.forallE QN Ty1) :=
  VEnv.HasType.lam hQN hNtyQ

/-- `VExpr.fieldSelector [N] 0 = fun (f : N) => f`. -/
def selQ : VExpr := VExpr.fieldSelector [Nty] 0

theorem selQ_eq : selQ = .lam Nty (.bvar 0) := rfl

theorem hSelQ {Γ} : envQ.HasType 0 Γ selQ (.forallE Nty Nty) :=
  selQ_eq ▸ VEnv.HasType.lam hNtyQ (.bvar .zero)

theorem hconvQ {Γ} : envQ.IsDefEq 0 Γ (.forallE Nty Nty)
    (.forallE Nty (.app motiveQ mkappQ))
    (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .forallEDF hNtyQ (VEnv.IsDefEq.beta hNtyQ hmkappQ).symm

/-- `MyOfNat.ofNat`'s translation: `MyOfNat.rec N n0 (fun _ => N) (fun f => f) d`. -/
def eProjQ (d : VExpr) : VExpr :=
  (VExpr.const `MyOfNat.rec []).mkApps ([Nty, n0c] ++ [motiveQ, selQ, d])

theorem hEProjQraw {Γ} {d} (hd : envQ.HasType 0 Γ d QN) :
    envQ.HasType 0 Γ (eProjQ d) (.app motiveQ d) := by
  have h := ((((hQRc.app hNtyQ).app hn0c).app hMotiveQ).app (hconvQ.defeq hSelQ)).app hd
  simpa [eProjQ, QRc, motiveQ, QN, QCc, Nty, n0c, VExpr.inst, VExpr.lift, VExpr.liftN,
    VExpr.mkApps] using h

theorem hEProjQ {Γ} {d} (hd : envQ.HasType 0 Γ d QN) :
    envQ.HasType 0 Γ (eProjQ d) Nty :=
  (VEnv.IsDefEq.beta hNtyQ hd).defeq (hEProjQraw hd)

/-- `Γ = [self : MyOfNat N n0]`. -/
def ΓqV : List VExpr := [QN]

/-- **The payoff witness**: `TrProj` at a one-field type class with **two** parameters —
the shape `OfNat.ofNat` needs. -/
theorem trProjQ_bvar : TrProj envQ 0 ΓqV `MyOfNat 0 (.bvar 0) (eProjQ (.bvar 0)) :=
  ⟨`MyOfNat.rec, `MyOfNat.mk, [], [Nty, n0c], [Nty], 2, QN, Nty,
    (SimplePattern.iotaRHS `MyOfNat.rec `MyOfNat.mk 2 1 1 0 1 rhsQ rhsQ_closed, .true),
    envQ_mkRecName, VEnv.addPat_self, rfl, by simp, .bvar .zero, rfl,
    hEProjQ (.bvar .zero)⟩

/-- `Δ = [self : MyOfNat N n0]`; `self.ofNat` translates. -/
def ΔqV : VLCtx := [(none, .vlam QN)]

theorem trExprSQ_proj :
    TrExprS envQ [] ΔqV (.proj `MyOfNat 0 (.bvar 0)) (eProjQ (.bvar 0)) :=
  .proj (.bvar (by rfl)) trProjQ_bvar

/-! ### The fragment guard: a class method's body, at the empty context (slice P2)

`DeltaHyps.esrc_shape` asks two things of every body the fragment records:
`NoProjBinders` and a translation at the **empty** `VLCtx`. Until slice P2 its predicate
was `NoProj`, and no projection body could satisfy it at all. This is the check that the
weakened field is not merely weaker but *satisfiable on the intended data*: `MyOfNat.ofNat`'s
prepared body, closed, at `[]`, with the projection where the payoff needs it — the class's
parameters instantiated (`N`, `n0`) rather than abstracted, which is the one respect in
which it is smaller than the real `fun α x self => self.1`. The binder-type half of the
predicate is the interesting one: it holds because `MyOfNat N n0` is a constant
application, and it would *fail* for a body binding at a projection type — which is exactly
the boundary `NoProjBinders` was cut at. -/

/-- `fun (self : MyOfNat N n0) => self.ofNat`, as a source `Expr`. -/
def ofNatBodyQ : Expr :=
  .lam `self (.app (.app (.const `MyOfNat []) (.const `N [])) (.const `n0 []))
    (.proj `MyOfNat 0 (.bvar 0)) .instImplicit

/-- The binder type `MyOfNat N n0` translates to `QN`. -/
theorem trExprSQ_ofNatTy :
    TrExprS envQ [] [] (.app (.app (.const `MyOfNat []) (.const `N [])) (.const `n0 [])) QN :=
  .app (hQCc.app hNtyQ) hn0c
    (.app hQCc hNtyQ (.const envQ_QC (by simp) (by simp)) (.const envQ_N (by simp) (by simp)))
    (.const envQ_n0 (by simp) (by simp))

/-- …and so does the whole body, at the **empty** context. -/
theorem trExprSQ_ofNatBody :
    TrExprS envQ [] [] ofNatBodyQ (.lam QN (eProjQ (.bvar 0))) :=
  .lam ⟨_, hQN⟩ trExprSQ_ofNatTy trExprSQ_proj

/-- **`DeltaHyps.esrc_shape` is satisfiable at a genuine projection body** — the guard the
P2 weakening exists for, in the field's own shape. -/
theorem gEsrcShapeProj :
    NoProjBinders ofNatBodyQ ∧ ∃ ve, TrExprS envQ [] [] ofNatBodyQ ve :=
  ⟨⟨⟨⟨⟨⟩, ⟨⟩⟩, ⟨⟩⟩, ⟨⟩⟩, _, trExprSQ_ofNatBody⟩

/-- …and the field's **old** predicate refutes the same body, so the relaxation is what
admitted it. Together with `gEsrcShapeProj` this is the whole non-vacuity story for slice
P2 at the environment level; `ErasesUniform.noProjBinders_ofNatBody` is the syntactic half,
at the full three-binder `fun α x self => self.1`. -/
theorem gEsrcShapeProj_noProj_refuted : ¬ NoProj ofNatBodyQ := fun h => h.2

/-! ## The projection-reduction interface (slice P4)

Above, `TrProj` was shown inhabited. Here it is turned into the *interface* the
projection round consumes, in the `PatsIotaSpec` two-layer idiom: a named hypothesis
structure stating the reduction rule the discharge needs, plus a `rfl`-checkable
per-structure certificate. Neither is an axiom, and nothing below carries `sorryAx`.

### Why the upstream statement is not the one to plan on

`TrEnv.proj_defeq` (`Verify/Environment/Lemmas.lean`) exists as a statement with a
deferred proof (`PROJ-TODO`). Read its premises:

```lean
    (hp : TrProj venv U Γ S i d e'')
    (hd : venv.IsDefEqU U Γ d ((VExpr.const ctorName cus).mkApps (params ++ fields)))
```

`hp` carries its **own**, existentially bound constructor name — the one in the `env.pats`
membership — while `hd` supplies a *different*, universally quantified `ctorName` for the
spine `d` is defeq to. **Nothing in the premises ties the two together.** The PROJ-TODO's
own sketch ("rewrite `d` by `hd` so the ι rule fires") silently assumes they coincide, and
they must: `Pattern.Matches` on `SimplePattern.iota recName _ ctorName' _` requires the
major premise to be a spine of `ctorName'`. Recovering `ctorName = ctorName'` from
`TrEnv` plus `HasType` alone is a canonicity argument, not a rewrite. So as stated the
theorem is plausibly **unprovable, not merely unproved**, and the downstream must not plan
on the discharge arriving in the delivered shape.

This is the disease `PatsIotaSpec` was created for — *the witness is existentially bound,
so the upstream lemma cannot be instantiated* — in a different field. The cure is the
same: expose the witness. `TrProjCtor` is `TrProj` with its `ctorName` named, and
`ProjDefeqSpec` states `proj_defeq` over it.

### What this slice does *not* do

It does **not** ship `ProjDefeqSpec.of_trEnv`. That discharge is one line —
`⟨fun hp hd hty hlen hflen hi => H.proj_defeq hp.toTrProj hd hty hlen hflen hi⟩`, and
`TrProjCtor.toTrProj` below is exactly the piece it needs — but calling
`TrEnv.proj_defeq` today injects the upstream `PROJ-TODO` `sorryAx`, and this slice is
zero-new-`sorryAx`. `ProjDefeqSpec` therefore stays a **named premise**: a consumer that
holds a `TrEnv` supplies it once upstream proves the lemma (or, better, once upstream
corrects the *statement* to carry the agreement, at which point `toTrProj` is not even
needed). That is a statement correction to escalate, not a proof request. -/

end LeanToLambdaBox

namespace Lean4Lean

open Lean LeanToLambdaBox

/-- **`TrProj` with its constructor witness named.** Definitionally `TrProj` after one
existential introduction: `TrProjCtor … c → TrProj …` is `⟨_, c, …⟩`
(`TrProjCtor.toTrProj`) and `TrProj … → ∃ c, TrProjCtor … c` is one `obtain`
(`TrProj.exists_ctorName`). The `c` is the constructor of `S`'s ι rule — the one the
registered `SimplePattern.iota` pattern matches its major premise against — and naming it
is what lets a reduction lemma relate it to the constructor heading the spine the
discriminant is defeq to. -/
def TrProjCtor (env : VEnv) (U : Nat) (Γ : List VExpr)
    (S : Name) (i : Nat) (e e' : VExpr) (ctorName : Name) : Prop :=
  ∃ (recName : Name) (us : List VLevel) (params fieldTys : List VExpr)
    (np : Nat) (structTy fieldTy : VExpr)
    (r : (SimplePattern.iota recName (np+1+1+0) ctorName (np+fieldTys.length)).toPattern.RHS ×
         (SimplePattern.iota recName (np+1+1+0) ctorName (np+fieldTys.length)).toPattern.Check),
    recName = mkRecName S ∧
    env.pats (SimplePattern.iota recName (np+1+1+0) ctorName (np+fieldTys.length)).toPattern r ∧
    params.length = np ∧ i < fieldTys.length ∧
    env.HasType U Γ e structTy ∧
    e' = (VExpr.const recName us).mkApps
           (params ++ [.lam structTy fieldTy.lift, VExpr.fieldSelector fieldTys i, e]) ∧
    env.HasType U Γ e' fieldTy

/-- Forgetting the name gives `TrProj` back, on the nose. -/
theorem TrProjCtor.toTrProj {env : VEnv} {U : Nat} {Γ : List VExpr} {S : Name} {i : Nat}
    {e e' : VExpr} {c : Name} (h : TrProjCtor env U Γ S i e e' c) :
    TrProj env U Γ S i e e' := by
  obtain ⟨recName, us, params, fieldTys, np, structTy, fieldTy, r, h⟩ := h
  exact ⟨recName, c, us, params, fieldTys, np, structTy, fieldTy, r, h⟩

/-- …and every `TrProj` names one. The two are interderivable, so `ProjDefeqSpec` is not
a *stronger* interface than the upstream statement wants to be — it is the same content
with one binder moved out, which is the whole point. -/
theorem TrProj.exists_ctorName {env : VEnv} {U : Nat} {Γ : List VExpr} {S : Name} {i : Nat}
    {e e' : VExpr} (h : TrProj env U Γ S i e e') :
    ∃ c, TrProjCtor env U Γ S i e e' c := by
  obtain ⟨recName, c, us, params, fieldTys, np, structTy, fieldTy, r, h⟩ := h
  exact ⟨c, recName, us, params, fieldTys, np, structTy, fieldTy, r, h⟩

/-! ### `TrExprS` inversion at a projection

`TrExprS.proj` is the only rule concluding at a `.proj` source, so the inversion is total
and one `cases`. The primed form hands back the constructor witness as well, which is the
shape `projConsistent_of_shape` consumes: it needs the discriminant's translation *and* a
name to instantiate `ProjDefeqSpec` at. -/

theorem TrExprS.proj_inv {env : VEnv} {Us : List Name} {Δ : VLCtx} {S : Name} {i : Nat}
    {e : Expr} {e'' : VExpr} (h : TrExprS env Us Δ (.proj S i e) e'') :
    ∃ e', TrExprS env Us Δ e e' ∧ TrProj env Us.length Δ.toCtx S i e' e'' := by
  cases h with | proj hd hp => exact ⟨_, hd, hp⟩

theorem TrExprS.proj_inv' {env : VEnv} {Us : List Name} {Δ : VLCtx} {S : Name} {i : Nat}
    {e : Expr} {e'' : VExpr} (h : TrExprS env Us Δ (.proj S i e) e'') :
    ∃ (e' : VExpr) (c : Name),
      TrExprS env Us Δ e e' ∧ TrProjCtor env Us.length Δ.toCtx S i e' e'' c := by
  obtain ⟨e', hd, hp⟩ := h.proj_inv
  obtain ⟨c, hpc⟩ := hp.exists_ctorName
  exact ⟨e', c, hd, hpc⟩

end Lean4Lean

namespace LeanToLambdaBox

open Lean Lean4Lean

/-- **The projection-reduction interface.** `TrEnv.proj_defeq`'s statement, strengthened
with the one hypothesis it is missing: the constructor heading the spine `d` is defeq to
is the *same* one the `TrProj` witness carries. See the section docstring for why the
upstream form is likely unprovable as written, and why naming the witness is the
`PatsIotaSpec` move rather than a new assumption.

Stated at a `VEnv` with `safety`/`kenv` as parameters it only ever uses through the
eventual discharge — the same discipline `SEvalDataι_defeq`'s docstring records for
`IotaConsistent`: the interface keeps kernel-environment data out of every downstream
`VEnv`-level statement.

A `Prop` **hypothesis**, never an axiom. -/
structure ProjDefeqSpec (safety : DefinitionSafety) (kenv : Lean.Kernel.Environment)
    (venv : VEnv) : Prop where
  /-- A projection whose discriminant is definitionally a saturated spine of *its own
  structure's* constructor is definitionally the spine's `i`-th field. -/
  proj_defeq : ∀ {U : Nat} {Γ : List VExpr} {S ctorName : Name} {i np nf : Nat}
      {cus : List VLevel} {params fields : List VExpr} {d e'' A : VExpr},
    TrProjCtor venv U Γ S i d e'' ctorName →
    venv.IsDefEqU U Γ d ((VExpr.const ctorName cus).mkApps (params ++ fields)) →
    venv.HasType U Γ d A →
    params.length = np → ∀ (hflen : fields.length = nf) (hi : i < nf),
    venv.IsDefEqU U Γ e'' (fields[i]'(hflen ▸ hi))

/-- **Per-structure shape certificate** — `IotaShape`'s analogue, and much smaller: four
kernel lookups and no `Expr` equation at all, because a projection's reduct is a *subterm*
of the redex rather than a rule template that has to be β-normalised.
`rfl`/`decide`-checkable for any concrete structure; nothing in it is a typing or
translation assumption.

`ival.ctors = [ctor]` is the load-bearing conjunct: it is `register_inductive`'s own
`is_struct` gate (`inf.ctors.length == 1`), it is what makes the target rule's hard-wired
constructor index `0` correct, and it is what discharges `ProjDefeqSpec`'s agreement
premise locally — a structure has exactly one constructor, so the `TrProjCtor` witness's
name and the spine's head are the same name.

The `kenv.find?` conjuncts are not constructible in-logic (a `Kernel.Environment` is
opaque), which is the same documented boundary `IotaShape` has; what *is* guarded is the
`Γ` half, and `ProjShape.ctorAgreement` below is the accessor the discharge uses. -/
structure ProjShape (safety : DefinitionSafety) (kenv : Lean.Kernel.Environment)
    (Γ : ErasureCtx) : Prop where
  shape : ∀ {S : Name} {iid : InductiveId} {np nf : Nat},
    Γ.projs S = some (iid, np) → Γ.ctorFields iid = some [nf] →
    ∃ (ival : InductiveVal) (ctor : Name) (cval : ConstructorVal),
      kenv.find? S = some (.inductInfo ival) ∧
      ival.ctors = [ctor] ∧ ival.numParams = np ∧ ival.numIndices = 0 ∧
      ival.isRec = false ∧
      kenv.find? ctor = some (.ctorInfo cval) ∧
      cval.numParams = np ∧ cval.numFields = nf ∧
      Γ.ctors ctor = some (iid, 0) ∧ Γ.ctorArities ctor = some (np + nf) ∧
      safety ≤ (Lean.ConstantInfo.inductInfo ival).safety

/-- **The agreement, read off the certificate.** The `Γ`-side half of `ProjShape`: the
structure's unique constructor, registered at index `0` with arity `np + nf`. This is what
`projConsistent_of_shape` (slice P5) instantiates `ProjDefeqSpec`'s `ctorName` at, and it
is the step that has no ι analogue — the ι discharge had to *build* its reduct's
translation by application generation, whereas a projection's reduct is a subterm. -/
theorem ProjShape.ctorAgreement {safety : DefinitionSafety}
    {kenv : Lean.Kernel.Environment} {Γ : ErasureCtx} (h : ProjShape safety kenv Γ)
    {S : Name} {iid : InductiveId} {np nf : Nat}
    (hs : Γ.projs S = some (iid, np)) (hnfs : Γ.ctorFields iid = some [nf]) :
    ∃ ctor : Name, Γ.ctors ctor = some (iid, 0) ∧ Γ.ctorArities ctor = some (np + nf) := by
  obtain ⟨ival, ctor, cval, -, -, -, -, -, -, -, -, hc, har, -⟩ := h.shape hs hnfs
  exact ⟨ctor, hc, har⟩

/-! ### Guards for the interface

`ProjDefeqSpec` cannot be *constructed* — that is the point of a named premise, and the
one implementation is upstream's deferred lemma. What can be guarded, and what matters, is
that it does not quantify over an empty domain: its premise `TrProjCtor` is inhabited, at
both fixtures above and at both polarities. -/

/-- **`TrProjCtor` is inhabited** — the witness with its constructor named, at `MyProd`'s
first field. -/
theorem trProjCtorP_bvar0 :
    TrProjCtor envP 0 ΓpV `MyProd 0 (.bvar 0) (eProj 0 (.bvar 0)) `MyProd.mk :=
  ⟨`MyProd.rec, [], [Nty], [Nty, Nty], 1, PN, Nty,
    (SimplePattern.iotaRHS `MyProd.rec `MyProd.mk 1 1 1 0 2 rhsP rhsP_closed, .true),
    envP_mkRecName, VEnv.addPat_self, rfl, by simp, hdV, rfl, hEProj0 hdV⟩

/-- …and at the payoff shape, the two-parameter one-field class. This is the
`ProjDefeqSpec` instance the `OfNat.ofNat` trace runs through. -/
theorem trProjCtorQ_bvar :
    TrProjCtor envQ 0 ΓqV `MyOfNat 0 (.bvar 0) (eProjQ (.bvar 0)) `MyOfNat.mk :=
  ⟨`MyOfNat.rec, [], [Nty, n0c], [Nty], 2, QN, Nty,
    (SimplePattern.iotaRHS `MyOfNat.rec `MyOfNat.mk 2 1 1 0 1 rhsQ rhsQ_closed, .true),
    envQ_mkRecName, VEnv.addPat_self, rfl, by simp, .bvar .zero, rfl,
    hEProjQ (.bvar .zero)⟩

/-- The forgetful direction lands back on `TrProj` — so `TrProjCtor` really is a
reparenthesisation and not a strengthening in disguise. -/
example : TrProj envP 0 ΓpV `MyProd 0 (.bvar 0) (eProj 0 (.bvar 0)) :=
  trProjCtorP_bvar0.toTrProj

/-- …and the naming direction recovers a constructor from the bare witness. -/
example : ∃ c, TrProjCtor envP 0 ΓpV `MyProd 0 (.bvar 0) (eProj 0 (.bvar 0)) c :=
  trProjP_bvar0.exists_ctorName

/-- The negative polarity travels too: at a `pats`-free environment no `TrProjCtor`
exists, for any constructor name. -/
theorem trProjCtor_refuted {env : VEnv} {U Γ S i e e' c}
    (hp : ∀ (p : Pattern) r, ¬ env.pats p r) : ¬ TrProjCtor env U Γ S i e e' c :=
  fun h => trProj_refuted hp h.toTrProj

/-- **`ProjShape`'s `Γ`-side conjuncts fire** at `Γproj` (`Erases.lean`), the
one-parameter one-field structure fixture: its unique constructor is registered at index
`0` with arity `1 + 1`. The `kenv.find?` half is the documented in-logic boundary
(`IotaShape` has the same one), so what a guard can show is that the certificate's `Γ`
demands are the ones registration actually meets — non-degenerately, since a
`paramCount`/`fieldIdx` confusion would give `2 ≠ 1 + 1`. -/
example : Γproj.ctors `AC.mk = some (projInd, 0) ∧ Γproj.ctorArities `AC.mk = some (1 + 1) :=
  ⟨Γproj_ctors, Γproj_arity⟩

/-- **`TrExprS.proj_inv'` fires**, and hands back exactly what the discharge asks for: the
discriminant's translation and the constructor name. -/
example : ∃ (e' : VExpr) (c : Name),
    TrExprS envQ [] ΔqV (.bvar 0) e' ∧
      TrProjCtor envQ 0 ΔqV.toCtx `MyOfNat 0 e' (eProjQ (.bvar 0)) c :=
  trExprSQ_proj.proj_inv'

end LeanToLambdaBox

