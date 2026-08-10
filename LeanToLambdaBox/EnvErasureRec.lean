import LeanToLambdaBox.EnvErasureNonrec
import LeanToLambdaBox.Closed

/-!
# Cold-start env-consistency discharge: the **recursive** (value-`fix`) fragment (P3-v2b)

This file is the recursive counterpart of `EnvErasureNonrec.lean`. For a **recursive**
mutual block, `visitMutual` (`Erasure.lean:904`) erases each def body with its sibling
`.const`s mapped to fresh fvars, closes the result with `mkDef` (`closeFix`), and stores
`(toKername nⱼ, .constantDecl ⟨some (.fix defs j)⟩)` for each name (`:918`). The
env-consistency obligation `ErasesEnvDelta` (`ErasesCorrect.lean:268`) therefore needs,
for such a constant, `Erases … Δ (ci.value! nⱼ) (.fix defs j)` — the `Erases.fix` rule
(`Erases.lean:377`, `notes/P3_ENV_ERASURE_DESIGN.md` §1).

The core deliverable is **`erases_fix_of_closed`**: it constructs that `Erases.fix`
derivation from
* the **bridge facts** — each opened sibling source body `osrcs[j]` erases to
  `obodies[j]` at the fixed erasure context `Δf` (`hbodies`), supplied by the (deferred,
  bridge-sized) `visitConst`-fixvar extension of `visitExpr_refines_erases`;
* the **closing fact** — `defs[j].body = closeFix ids 0 obodies[j]` (`hclose`), from the
  `mkDef` `toBvar`-loop (`FixMetatheory.closeFixFold_eq_foldl`); and
* **closedness** — the source `.lam` telescope and the constructed target `.fix` are both
  closed and fvar-free (top-level recursive defs). From closedness the six transport-
  inertness equalities of `Erases.fix` (`hlift`/`hinst`/`habsl`/`hshift`/`hsubst`/`htobv`)
  are *derived* rather than assumed — the Expr side via lean4lean's
  `liftLooseBVars_eq_self`/`instantiate1'_eq_self`/`FVarsIn.abstract_eq_self`, the LBTerm
  side via the small `LBClosed` de-Bruijn-closedness metatheory (`Closed.lean`).

As in the non-recursive fragment, the cold-start DAG registration (which recursive
constants land in `E`, and that each is registered with a consistent `.fix` decl) is
isolated behind a clean `Prop` hypothesis (`RegisteredClosureRec`) — the analogue of
`RegisteredClosure`, and what a full DAG walk (P3.13, deferred) would discharge. These
are `Prop` hypotheses, **never axioms**.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure

/-! ## Part 1 — `LBClosed` (now in `Closed.lean`)

The de-Bruijn-closedness predicate `LBClosed`/`LBClosedArgs`/`LBClosedAlts`/`LBClosedDefs`
and its metatheory (`LBClosed.shift_eq`/`LBClosed.subst_eq`, monotonicity, the
shift/subst bound laws, the spine/telescope helpers) used to live here; they are pure
target-side de-Bruijn facts with no `Erases` content, so they now live in
`LeanToLambdaBox/Closed.lean` (imported above) where the ι-bridge can share them.
-/

/-! ## Part 2 — the `Erases.fix` reconciliation from closedness + bridge facts

`erases_fix_of_closed` builds the `Erases.fix` derivation (`Erases.lean:377`) for a
registered recursive constant. The six transport-inertness equalities of the rule are
*derived* from closedness (Part 1's `LBClosed` for the target, lean4lean's
`Closed`/`FVarsIn` metatheory for the source), so the caller supplies natural "the fix
block is closed and fvar-free" premises instead of three magic equalities per side. -/

/-- **The recursive-constant reconciliation.** Given the bridge facts (each opened
sibling source body `osrcs[j]` erases to `obodies[j]` at the fixed context `Δf`), the
`mkDef` closing fact (`hclose`), and closedness/fvar-freeness of the source `.lam`
telescope and the constructed target `.fix`, the recursive constant body
`.lam n ty b bi` erases to `.fix defs idx` at **any** erasure context `Δ` (the `Erases.fix`
rule's conclusion `Δ` is free, exactly the context-uniformity `ErasesEnvDelta` needs).

The Expr-side inertness (`hlift`/`hinst`/`habsl`) comes from lean4lean's
`Expr.liftLooseBVars_eq_self`/`Expr.instantiate1'_eq_self`/`FVarsIn.abstract_eq_self`
(a closed, fvar-free `Expr` is fixed by lift/instantiate/abstract); the LBTerm-side
(`hshift`/`hsubst`/`htobv`) from `LBClosed.shift_eq`/`LBClosed.subst_eq`/
`toBvar_eq_of_not_hasFVar`. -/
theorem erases_fix_of_closed {env : VEnv} {Us : List Name} {Γ : ErasureCtx}
    {Δ Δf : VLCtx} {n : Name} {ty b : Expr} {bi : BinderInfo}
    {ids : List FVarId} {osrcs : List Expr} {obodies : List LBTerm}
    {defs : List (@FixDef LBTerm)} {idx : Nat}
    (hidx : idx < defs.length)
    (holen : osrcs.length = defs.length)
    (hblen : obodies.length = defs.length)
    (hilen : ids.length = defs.length)
    (heclosed : Closed (.lam n ty b bi) 0)
    (henofv : FVarsIn (fun _ => False) (.lam n ty b bi))
    (hfclosed : LBClosed (.fix defs idx) 0)
    (hffv : ∀ x, ¬ hasFVar x (.fix defs idx))
    (hclose : ∀ j (h : j < defs.length),
        (defs[j]'h).body = closeFix ids 0 (obodies[j]'(hblen ▸ h)))
    (hbodies : ∀ j (h : j < defs.length),
        Erases env Us Γ Δf (osrcs[j]'(holen ▸ h)) (obodies[j]'(hblen ▸ h))) :
    Erases env Us Γ Δ (.lam n ty b bi) (.fix defs idx) := by
  have hlbr : (Expr.lam n ty b bi).looseBVarRange' = 0 := heclosed.looseBVarRange_zero
  refine .fix idx hidx holen hblen hilen
    (fun s d => Expr.liftLooseBVars_eq_self (hlbr ▸ Nat.zero_le s))
    (fun e₀ d => Expr.instantiate1'_eq_self (hlbr ▸ Nat.zero_le d))
    (fun v d => FVarsIn.abstract_eq_self (henofv.mono (fun _ h => h.elim)) (heclosed.mono (Nat.zero_le d)))
    (fun d c => LBClosed.shift_eq hfclosed (Nat.zero_le c) d)
    (fun s d => LBClosed.subst_eq hfclosed (Nat.zero_le d) s)
    (fun x l => toBvar_eq_of_not_hasFVar x l (.fix defs idx) (hffv x))
    hclose hbodies

/-! ## Part 3 — recursive `ErasesEnvDelta` discharge

`RegisteredClosureRec` is the recursive analogue of `EnvErasureNonrec.RegisteredClosure`:
a clean `Prop` hypothesis recording, for every source constant `n` whose (recursive) body
`Esrc n` the run stored as a `.fix` decl, both the disjointness fact and the `Erases`
witness (context-uniform, `∀ Δ`) that a full DAG walk would produce — here already in the
`.fix defs idx` shape. Its non-vacuity guard constructs that `Erases` witness through the
`erases_fix_of_closed` reconciliation, exercising the whole chain. -/

/-- **Cold-start closure registration for the recursive fragment** (a clean `Prop`
hypothesis; the deferred DAG walk P3.13 discharges it). For every source constant `n`
with a recursive unfolding `Esrc n = some body`, the run consed
`(Γ.constants n, .constantDecl ⟨some (.fix defs idx)⟩)` onto `E`, and `body` erases to
that **fix** body in *any* context `Δ` (the constant body is closed, so `Erases.fix`'s
free-`Δ` conclusion gives context-uniformity for free). -/
structure RegisteredClosureRec (env : VEnv) (Us : List Name) (Γ : ErasureCtx)
    (Esrc : SEnv) (E : GlobalDeclarations) : Prop where
  disj : ∀ {n : Name} {body : Expr}, Esrc n = some body →
    Γ.ctors n = none ∧ Γ.casesOns n = none
  erase : ∀ {n : Name} {body : Expr}, Esrc n = some body →
    ∃ (defs : List (@FixDef LBTerm)) (idx : Nat),
      LBTerm.envLookup E (Γ.constants n) = some (.constantDecl ⟨some (.fix defs idx)⟩) ∧
      ∀ {Δ : VLCtx}, Erases env Us Γ Δ body (.fix defs idx)

/-- **Recursive `ErasesEnvDelta` discharge.** Assembles the per-constant records of
`RegisteredClosureRec` into the `ErasesEnvDelta` the forward simulation assumes — the
`.fix`-valued counterpart of `erasesEnvDelta_of_registeredClosure`. -/
theorem erasesEnvDelta_of_registeredClosureRec {env : VEnv} {Us : List Name}
    {Γ : ErasureCtx} {Esrc : SEnv} {E : GlobalDeclarations}
    (h : RegisteredClosureRec env Us Γ Esrc E) : ErasesEnvDelta env Us Γ Esrc E := by
  intro Δ n body hunf
  obtain ⟨defs, idx, hlook, her⟩ := h.erase hunf
  exact ⟨(h.disj hunf).1, (h.disj hunf).2, _, hlook, her⟩

/-! ### Non-vacuity guards for Part 3

A concrete one-def recursive block: the constant body is the closed, fvar-free
`.lam a (Sort 0) (Sort 0)` and its stored decl is the self-loop
`.fix [{name := "f", body := .bvar 0}] 0` (the `def f := f` shape at the pure `LBTerm`
level). The `Erases` witness is produced by `erases_fix_of_closed` from `ids = [x]`,
`osrcs = [.fvar x]`, `obodies = [.fvar x]` — the sole opened body `.fvar x` erases by
`Erases.fvar` and re-closes to `.bvar 0` by `closeFix` — so the reconciliation genuinely
fires and `RegisteredClosureRec`/`ErasesEnvDelta` are non-vacuous. -/

/-- The concrete recursive constant body (a closed, fvar-free `.lam`). -/
private def gLamR : Expr := .lam `a (.sort .zero) (.sort .zero) .default

/-- Its stored `.fix` decl body — the `def f := f` self-loop. -/
private def gFixR : LBTerm := .fix [{ name := .named "f", body := .bvar 0 }] 0

/-- The reconciliation fires: `gLamR` erases to `gFixR` at any `Δ`. -/
theorem gErases_fix (env : VEnv) (Us : List Name) (Γ : ErasureCtx) {Δ : VLCtx} :
    Erases env Us Γ Δ gLamR gFixR := by
  refine erases_fix_of_closed (Δf := Δ) (ids := [⟨`x⟩])
    (osrcs := [.fvar ⟨`x⟩]) (obodies := [.fvar ⟨`x⟩])
    Nat.zero_lt_one rfl rfl rfl ⟨trivial, trivial⟩ ⟨rfl, rfl⟩ ?_ ?_ ?_ ?_
  · -- LBClosed gFixR 0
    exact ⟨Nat.zero_lt_one, trivial⟩
  · -- no fvars in gFixR
    intro x
    show ¬ hasFVar x (LBTerm.fix [{ name := .named "f", body := .bvar 0 }] 0)
    simp only [hasFVar_fix, hasFVarDefs, hasFVar_bvar, or_self, not_false_iff]
  · -- hclose: .bvar 0 = closeFix [x] 0 (.fvar x)
    intro j h
    obtain rfl : j = 0 := by simp only [List.length_cons, List.length_nil] at h; omega
    exact (closeFixFold_fvar_head ⟨`x⟩ 0 []).symm
  · -- hbodies: .fvar x erases to .fvar x
    intro j h
    obtain rfl : j = 0 := by simp only [List.length_cons, List.length_nil] at h; omega
    exact .fvar ⟨`x⟩

/-- A source env where a constant unfolds to the recursive body `gLamR`. -/
private def gEsrcR : SEnv := fun _ => some gLamR

/-- A concrete `Γ` mapping every constant to a fixed kername, empty ctors/casesOns. -/
private def gΓR : ErasureCtx where
  inductives := fun _ => none
  constants := fun _ => rootKername "f"
  ctors := fun _ => none
  ctorArities := fun _ => none
  casesOns := fun _ => none

/-- A concrete `E` binding that kername to the recursive `.fix` decl `gFixR`. -/
private def gER : GlobalDeclarations := [(rootKername "f", .constantDecl ⟨some gFixR⟩)]

/-- Non-vacuity: `RegisteredClosureRec` is realizable at `(gΓR, gEsrcR, gER)` with a
genuine (non-`none`) recursive `Esrc` and the `erases_fix_of_closed`-built `Erases`
witness. -/
theorem gRegisteredClosureRec (env : VEnv) (Us : List Name) :
    RegisteredClosureRec env Us gΓR gEsrcR gER where
  disj := fun _ => ⟨rfl, rfl⟩
  erase := by
    intro n body h
    simp only [gEsrcR, Option.some.injEq] at h
    subst h
    exact ⟨[{ name := .named "f", body := .bvar 0 }], 0, rfl, fun {_} => gErases_fix env Us gΓR⟩

/-- Non-vacuity: the recursive `ErasesEnvDelta` is then *derived* over the constructed
run (the `.fix`-valued counterpart of `gErasesEnvDelta`). -/
theorem gErasesEnvDeltaRec (env : VEnv) (Us : List Name) :
    ErasesEnvDelta env Us gΓR gEsrcR gER :=
  erasesEnvDelta_of_registeredClosureRec (gRegisteredClosureRec env Us)

/-! ## Part 4 — recursion is subsumed by v1's general `RegisteredClosure`

`EnvErasureNonrec.RegisteredClosure.erase` leaves the stored body `body'` *arbitrary*
(any `LBTerm`, `∀ Δ`-uniform `Erases`), so a recursive constant — whose stored body is
`.fix defs idx` with the witness from `erases_fix_of_closed` — is just a special case.
`registeredClosure_of_registeredClosureRec` makes that explicit: the recursive
registration collapses into v1's `RegisteredClosure`, so **v1's env-level discharge
machinery (`erasesEnvDelta_of_registeredClosure`) already covers recursive constants**
once this reconciliation supplies the `.fix` witness. A cold-start `RegisteredClosure`
built by a full DAG walk (P3.13, deferred) may therefore mix plain and `.fix` bodies
freely, and its `ErasesEnvDelta` follows uniformly. -/

/-- The recursive closure registration is subsumed by the general (v1) one: store the
`.fix defs idx` body as the arbitrary `body'` that `RegisteredClosure` allows. -/
theorem registeredClosure_of_registeredClosureRec {env : VEnv} {Us : List Name}
    {Γ : ErasureCtx} {Esrc : SEnv} {E : GlobalDeclarations}
    (h : RegisteredClosureRec env Us Γ Esrc E) : RegisteredClosure env Us Γ Esrc E where
  disj := h.disj
  erase := fun hunf => by
    obtain ⟨defs, idx, hlook, her⟩ := h.erase hunf
    exact ⟨.fix defs idx, hlook, her⟩

/-- Sanity: the recursive `ErasesEnvDelta` discharge factors through v1's discharge via
the subsumption — the two discharge paths agree. -/
theorem erasesEnvDelta_of_registeredClosureRec' {env : VEnv} {Us : List Name}
    {Γ : ErasureCtx} {Esrc : SEnv} {E : GlobalDeclarations}
    (h : RegisteredClosureRec env Us Γ Esrc E) : ErasesEnvDelta env Us Γ Esrc E :=
  erasesEnvDelta_of_registeredClosure (registeredClosure_of_registeredClosureRec h)

end LeanToLambdaBox
