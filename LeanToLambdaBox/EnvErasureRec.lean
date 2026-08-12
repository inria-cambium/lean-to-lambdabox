import LeanToLambdaBox.EnvErasureNonrec
import LeanToLambdaBox.Closed
import LeanToLambdaBox.FixUnfold

/-!
# Cold-start env-consistency discharge: the **recursive** (value-`fix`) fragment (P3-v2b)

This file is the recursive counterpart of `EnvErasureNonrec.lean`. For a **recursive**
mutual block, `visitMutual` (`Erasure.lean:904`) erases each def body with its sibling
`.const`s mapped to fresh fvars, closes the result with `mkDef` (`closeFix`), and stores
`(toKername nⱼ, .constantDecl ⟨some (.fix defs j)⟩)` for each name (`:918`). The
env-consistency obligation `ErasesEnvDelta` (`ErasesCorrect.lean`) therefore needs,
for such a constant, `Erases … Δ (ci.value! nⱼ) (.fix defs j)` — the `Erases.fix` rule
(`Erases.lean`, re-founded by the recursion wall's slice W1).

The core deliverable is **`erases_fix_of_closed`**: it constructs that `Erases.fix`
derivation from
* the **registration fact** — `Γ.recBodies` records this block for each of the block's
  own names (`hreg`), and every def's `principalArgIdx` is the `mkDef` default `0`
  (`hrarg`);
* the **bridge facts** — each sibling source body `srcs[j]` erases, at every context, to
  the fvar-instantiated opened body `substFix ids defs obodies[j]` (`hbodies`), supplied
  by the (deferred, bridge-sized) `visitConst`-fixvar extension of
  `visitExpr_refines_erases` composed with the fvar→block instantiation;
* the **closing fact** — `defs[j].body = closeFix ids 0 obodies[j]` (`hclose`), from the
  `mkDef` `toBvar`-loop (`FixMetatheory.closeFixFold_eq_foldl`), which
  `closeFix_substList_fixSubst` (`FixUnfold`) turns into the dynamic unfolding the rule
  asks for; and
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

`erases_fix_of_closed` builds the `Erases.fix` derivation (`Erases.lean`) for a
registered recursive constant. The six transport-inertness equalities of the rule are
*derived* from closedness (Part 1's `LBClosed` for the target, lean4lean's
`Closed`/`FVarsIn` metatheory for the source), so the caller supplies natural "the fix
block is closed and fvar-free" premises instead of three magic equalities per side. -/

/-- **The recursive-constant reconciliation.** Given the block's registration in `Γ`
(`hreg`), the bridge facts (each *opened*, fvar-siblinged source body `srcs[j]` erases to
the fvar-instantiated `substFix ids defs obodies[j]`), the `mkDef` closing fact
(`hclose`), and closedness/fvar-freeness of the source `.lam` telescope and the
constructed target `.fix`, the recursive constant body `.lam n ty b bi` erases to
`.fix defs idx` at **any** erasure context `Δ` (the `Erases.fix` rule's conclusion `Δ` is
free, exactly the context-uniformity `ErasesEnvDelta` needs).

This is where the recursion wall's two halves meet. `Erases.fix` asks for its bodies
against the *dynamic* unfolding `substList (fixSubst defs) defs[j].body` — what
`WcbvEval.fix_guarded` actually produces — while a run (and hence the bridge) knows the
*static* `closeFix`-closed form. `closeFix_substList_fixSubst` (`FixUnfold`, slice W0)
is exactly the bridge between them, and it is discharged here, once, so no consumer of
the rule ever meets `closeFix` again.

The Expr-side inertness (`hlift`/`hinst`/`habsl`) comes from lean4lean's
`Expr.liftLooseBVars_eq_self`/`Expr.instantiate1'_eq_self`/`FVarsIn.abstract_eq_self`
(a closed, fvar-free `Expr` is fixed by lift/instantiate/abstract); the LBTerm-side
(`hshift`/`hsubst`/`htobv`) from `LBClosed.shift_eq`/`LBClosed.subst_eq`/
`toBvar_eq_of_not_hasFVar`. Both closedness facts are stated at the conclusion's index
`idx` and reused at every `j`: `LBClosed`/`hasFVar` on a `.fix` node do not look at the
index (`LBClosed_fix`/`hasFVar_fix` are `Iff.rfl` into the `defs`-only predicates).

**Signature change (recursion wall, slice W1).** `hreg`/`hrarg`/`hsrc`/`hslen`/`hoclosed`
are new, and the bodies premise moved from the fvar-open form at a fixed `Δf` to the
fvar-instantiated form at every `Δf`. The old signature could not be kept: it was
precisely the pre-W1 rule's contentlessness (Part 3b). -/
theorem erases_fix_of_closed {env : VEnv} {Us : List Name} {Γ : ErasureCtx}
    {Δ : VLCtx} {n : Name} {ty b : Expr} {bi : BinderInfo}
    {nms : List Name} {ids : List FVarId} {srcs : List Expr} {obodies : List LBTerm}
    {defs : List (@FixDef LBTerm)} {idx : Nat}
    (hidx : idx < defs.length)
    (hnlen : nms.length = defs.length)
    (hslen : srcs.length = defs.length)
    (hblen : obodies.length = defs.length)
    (hilen : ids.length = defs.length)
    (hsrc : (srcs[idx]'(hslen ▸ hidx)) = .lam n ty b bi)
    (hreg : ∀ j (h : j < defs.length), Γ.recBodies (nms[j]'(hnlen ▸ h)) = some (defs, j))
    (hrarg : ∀ d ∈ defs, d.principalArgIdx = 0)
    (heclosed : Closed (.lam n ty b bi) 0)
    (henofv : FVarsIn (fun _ => False) (.lam n ty b bi))
    (hfclosed : LBClosed (.fix defs idx) 0)
    (hffv : ∀ x, ¬ hasFVar x (.fix defs idx))
    (hoclosed : ∀ j (h : j < defs.length), LBClosed (obodies[j]'(hblen ▸ h)) 0)
    (hclose : ∀ j (h : j < defs.length),
        (defs[j]'h).body = closeFix ids 0 (obodies[j]'(hblen ▸ h)))
    (hbodies : ∀ j (h : j < defs.length) (Δf : VLCtx),
        Erases env Us Γ Δf (srcs[j]'(hslen ▸ h))
          (substFix ids defs (obodies[j]'(hblen ▸ h)))) :
    Erases env Us Γ Δ (.lam n ty b bi) (.fix defs idx) := by
  have hlbr : (Expr.lam n ty b bi).looseBVarRange' = 0 := heclosed.looseBVarRange_zero
  -- `LBClosed`/`hasFVar` on a `.fix` ignore the index, so the conclusion's witnesses
  -- serve every sibling.
  have hdefs : ∀ j, LBClosed (LBTerm.fix defs j) 0 := fun _ => hfclosed
  have hidsfv : ∀ x ∈ ids, ∀ j, ¬ hasFVar x (LBTerm.fix defs j) := fun x _ _ => hffv x
  refine .fix idx hidx hnlen hslen hsrc hreg hrarg
    (fun s d => Expr.liftLooseBVars_eq_self (hlbr ▸ Nat.zero_le s))
    (fun e₀ d => Expr.instantiate1'_eq_self (hlbr ▸ Nat.zero_le d))
    (fun v d => FVarsIn.abstract_eq_self (henofv.mono (fun _ h => h.elim)) (heclosed.mono (Nat.zero_le d)))
    (fun d c => LBClosed.shift_eq hfclosed (Nat.zero_le c) d)
    (fun s d => LBClosed.subst_eq hfclosed (Nat.zero_le d) s)
    (fun x l => toBvar_eq_of_not_hasFVar x l (.fix defs idx) (hffv x))
    (fun j h Δf => ?_)
  -- static closing ↦ dynamic unfolding, discharged once (slice W0's capstone)
  rw [hclose j h, closeFix_substList_fixSubst hilen hdefs hidsfv (hoclosed j h)]
  exact hbodies j h Δf

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

A **genuinely recursive** one-def block — `def f (a : Prop) := f a` — carried all the way
through the reconciliation:

* source body `gLamR = fun (a : Prop) => f a` (closed, fvar-free, as a top-level def is);
* the run's opened body `gObodyR = λa. x #0`, with the sibling `f` sitting as the fresh
  fixvar `x`, which `mkDef`/`closeFix` closes to `gFixDefsR = [f ↦ λa. #1 #0]`;
* the stored decl `gFixR = fix f. λa. f a`.

`erases_fix_of_closed` then fires on real data: `hclose` is the `closeFix` step above, and
`hbodies` is the opened body's erasure *after* fvar instantiation — where the recursive
call is discharged by the `const_fix` leaf against `gΓR`'s registration. So
`RegisteredClosureRec`/`ErasesEnvDelta` are non-vacuous, and non-vacuous at a fixture
that the *shipping* eraser could actually emit.

This replaces the pre-W1 fixture, which related the dummy source `fun (a : Prop) => Prop`
to the contentless self-loop `fix f. f` — see Part 3b for why that was possible and what
it cost. -/

/-- The concrete recursive constant body: `fun (a : Prop) => f a` (closed, fvar-free). -/
private def gLamR : Expr := .lam `a (.sort .zero) (.app (.const `f []) (.bvar 0)) .default

/-- The one-def block behind `gFixR`, as `mkDef` closes it: the sibling reference has
become the fix binder `#1`. -/
private def gFixDefsR : List (@FixDef LBTerm) :=
  [{ name := .named "f", body := .lambda (nameToBinder `a) (.app (.bvar 1) (.bvar 0)) }]

/-- Its stored `.fix` decl body — `fix f. λa. f a`. -/
private def gFixR : LBTerm := .fix gFixDefsR 0

/-- The fresh fixvar the run mints for the sibling `f`. -/
private def gIdR : FVarId := ⟨`x⟩

/-- The *opened* target body the run erases before closing: `λa. x #0`. -/
private def gObodyR : LBTerm := .lambda (nameToBinder `a) (.app (.fvar gIdR) (.bvar 0))

/-- A concrete `Γ`: every constant to a fixed kername, empty ctors/casesOns, and the
block above registered under the name `f`. -/
private def gΓR : ErasureCtx where
  inductives := fun _ => none
  constants := fun _ => rootKername "f"
  ctors := fun _ => none
  ctorArities := fun _ => none
  casesOns := fun _ => none
  recBodies := fun n => if n = `f then some (gFixDefsR, 0) else none

/-- `closeFix` really does produce the stored block from the opened body. -/
private theorem gCloseR : (gFixDefsR[0]'(by simp [gFixDefsR])).body = closeFix [gIdR] 0 gObodyR := by
  rw [closeFix_cons]
  simp [gFixDefsR, gObodyR, closeFix, closeFixFold, toBvar, gIdR]

/-- …and instantiating the fixvar back gives the block's own node in call position. -/
private theorem gSubstFixR :
    substFix [gIdR] gFixDefsR gObodyR
      = .lambda (nameToBinder `a) (.app gFixR (.bvar 0)) := by
  simp [substFix, substFVarList, substFVar, substFVarArgs, gObodyR, gFixR, gIdR]

/-- The reconciliation fires: `gLamR` erases to `gFixR` at any `Δ`. The recursive call in
the body is related to the block by `Erases.const_fix`, against `gΓR`'s registration. -/
theorem gErases_fix (env : VEnv) (Us : List Name) {Δ : VLCtx} :
    Erases env Us gΓR Δ gLamR gFixR := by
  have hrec : gΓR.recBodies `f = some (gFixDefsR, 0) := by simp [gΓR]
  have hshift : ∀ (d c : Nat), LBTerm.shift d c gFixR = gFixR := by
    intro d c
    simp only [gFixR, gFixDefsR, LBTerm.shift, LBTerm.shiftDefs, List.length_cons,
      List.length_nil]
    rw [if_neg (by omega), if_neg (by omega)]
  have hsubst : ∀ (s : LBTerm) (d : Nat), LBTerm.subst s d gFixR = gFixR := by
    intro s d
    simp only [gFixR, gFixDefsR, LBTerm.subst, LBTerm.substDefs, List.length_cons,
      List.length_nil]
    rw [if_pos (by omega), if_pos (by omega)]
  refine erases_fix_of_closed (nms := [`f]) (ids := [gIdR]) (srcs := [gLamR])
    (obodies := [gObodyR])
    Nat.zero_lt_one rfl rfl rfl rfl rfl (fun j h => ?_) (fun d hd => ?_)
    ⟨trivial, trivial, Nat.zero_lt_one⟩ ⟨rfl, by simp [FVarsIn], trivial⟩ ?_ ?_
    (fun j h => ?_) (fun j h => ?_) (fun j h Δf => ?_)
  · -- hreg
    obtain rfl : j = 0 := by simp only [gFixDefsR, List.length_cons, List.length_nil] at h; omega
    exact hrec
  · -- hrarg: `mkDef` leaves `principalArgIdx` at the default `0`
    simp only [gFixDefsR, List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd; rfl
  · -- LBClosed gFixR 0
    show LBClosed gFixR 0
    simp [gFixR, gFixDefsR, LBClosedDefs]
  · -- no fvars in gFixR
    intro x
    show ¬ hasFVar x gFixR
    simp [gFixR, gFixDefsR, hasFVarDefs]
  · -- the opened body is de-Bruijn closed
    obtain rfl : j = 0 := by simp only [gFixDefsR, List.length_cons, List.length_nil] at h; omega
    show LBClosed gObodyR 0
    simp [gObodyR]
  · -- hclose
    obtain rfl : j = 0 := by simp only [gFixDefsR, List.length_cons, List.length_nil] at h; omega
    exact gCloseR
  · -- hbodies, through the `const_fix` leaf
    obtain rfl : j = 0 := by simp only [gFixDefsR, List.length_cons, List.length_nil] at h; omega
    show Erases env Us gΓR Δf gLamR (substFix [gIdR] gFixDefsR gObodyR)
    rw [gSubstFixR]
    exact .lam (ty' := .sort .zero) (.sort rfl)
      (.app (.const_fix `f [] hrec (by simp [gΓR]) (by simp [gΓR]) hshift hsubst
        (fun x l => rfl)) (.bvar 0))

/-- A source env where a constant unfolds to the recursive body `gLamR`. -/
private def gEsrcR : SEnv := fun _ => some gLamR

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
    exact ⟨gFixDefsR, 0, rfl, fun {_} => gErases_fix env Us⟩

/-- Non-vacuity: the recursive `ErasesEnvDelta` is then *derived* over the constructed
run (the `.fix`-valued counterpart of `gErasesEnvDelta`). -/
theorem gErasesEnvDeltaRec (env : VEnv) (Us : List Name) :
    ErasesEnvDelta env Us gΓR gEsrcR gER :=
  erasesEnvDelta_of_registeredClosureRec (gRegisteredClosureRec env Us)

/-! ## Part 3b — the historical record: the **pre-W1** `Erases.fix` was contentless, so
`NoFix` was load-bearing (recursion wall, slices W0/W1)

Before the recursion wall's slice W1, `Erases.fix` imposed **no relation whatsoever**
between its conclusion's source `.lam n ty b bi` and the block data: `n ty b bi` occurred
only in the three Expr-side inertness equalities and in the conclusion, and nothing tied
`.lam n ty b bi` to the `idx`-th source body, nor the source bodies to the real bodies of
the defs. `erases_fix_of_closed` then derived the rule from *nothing but* closedness and
fvar-freeness of the two sides, at **any** `Γ` — so the dummy `fun (a : Prop) => Prop`
erased to the self-loop `fix f. f`.

`ContentlessFix` below states exactly that consequence, and this section keeps the
machine-checked refutation it enables, because the refutation is *why* the rule was
re-founded: **the `NoFix t` premise of `erases_correct_data` was load-bearing for
soundness, not merely for convenience.** Take the (closed, fvar-free) higher-order
identity `fun (h : Prop → Prop) => h`, which the old rule related to `fix f. f`, and apply
it to `fun (a : Prop) => a`. That gives

* a source term that `SEvalDataC`-evaluates in one β step (`gCxSEval`) and is
  genuinely `TrExprS`-typeable over the empty, well-formed `VEnv` (`gCxTrExprS`);
* a target `.app (fix f. f) (λ. #0)` that it erases to, in applied (`NoBlock`) form
  (`gCxErases`, `gCxNoBlock`);
* and **no** `WcbvEval` value for that target, at *any* environment
  (`no_wcbvEval_app_gCxFix`): with `principalArgIdx = 0` the only applicable rule is
  `fix_guarded` (`beta`/`app_box`/`construct_app` need a different head value and
  `WcbvEval` is deterministic; `fix_stuck` needs `argsv.length < 0`; `fix_unguarded`
  is flag-off; `app_cong` is refuted by `isStuckApp_fix_bare`), and its reduct is the
  *same* redex, since `substList (fixSubst gCxFixDefs) (.bvar 0) = fix f. f`. So no
  finite derivation exists.

`erases_correct_data_without_noFix_false_of_contentless_fix` therefore refutes
`erases_correct_data` with `hnfenv`, `NoFix t` and `NoFix t'` deleted and *everything else
verbatim* — the "just relax the premise" reading of the recursion wall. Note the
counterexample runs at `E = []`, where `NoFixEnv E` **holds** (`gCxNoFixEnv`): it was
`NoFix t` alone that was doing the work.

**What W1 changed.** The rule now carries `hsrc` (the missing source ↔ block link),
`hreg` (the block is registered in `Γ`) and bodies stated against each def's *unfolding*,
and the `const_fix` leaf handles the sibling references a fix unfolding exposes. The
hypothesis this section runs on is therefore no longer derivable — `not_contentlessFix`
proves it outright at the counterexample's own `Γ`, which is the machine-checked
statement that W1 closed the hole. The refutation is kept, hypothesis and all, as the
record of why the rule could not simply have been un-gated. -/

/-- Source: `Prop → Prop`, the type of the counterexample's argument. -/
private def gCxArr : Expr := .forallE `a (.sort .zero) (.sort .zero) .default

/-- Source: `fun (a : Prop) => a`. -/
private def gCxId : Expr := .lam `a (.sort .zero) (.bvar 0) .default

/-- Source: `fun (h : Prop → Prop) => h`. Closed and fvar-free — which, under the
*pre-W1* rule, was the whole of what `erases_fix_of_closed` needed to relate it to the
contentless block `gCxFix`. -/
private def gCxHId : Expr := .lam `h gCxArr (.bvar 0) .default

/-- Source: the redex `(fun (h : Prop → Prop) => h) (fun (a : Prop) => a)`. -/
private def gCxApp : Expr := .app gCxHId gCxId

/-- Target: the erasure of `gCxId`. -/
private def gCxId' : LBTerm := .lambda (nameToBinder `a) (.bvar 0)

/-- The counterexample's block — the **contentless** self-loop `def f := f`, whose sole
body is the fix binder itself. (Part 3's fixture is now a genuinely recursive block, so
this data is local to the record.) -/
private def gCxFixDefs : List (@FixDef LBTerm) := [{ name := .named "f", body := .bvar 0 }]

/-- `fix f. f`. -/
private def gCxFix : LBTerm := .fix gCxFixDefs 0

/-- Target: the erasure of `gCxApp` — `(fix f. f) (λ. #0)`. -/
private def gCxApp' : LBTerm := .app gCxFix gCxId'

/-- **The target of the counterexample has no value.** No `WcbvEval` derivation
concludes `.app (fix f. f) a` for any argument `a`, at any environment and any flags
with `with_guarded_fix = true` (in particular `appliedFlags` and `optFlags`).

The induction is on the target derivation: every rule that can conclude an
application either needs the head to evaluate to something other than a bare `fix`
(refuted by determinism against `fix_atom`), or is flag- or arity-blocked
(`fix_unguarded`, `fix_stuck`, `app_cong`), or is `fix_guarded` — whose last premise
is `WcbvEval E fl (.app (fix f. f) av) r`, a strictly smaller derivation of the same
shape, closed by the induction hypothesis. -/
theorem no_wcbvEval_app_gCxFix {E : GlobalDeclarations} {fl : WcbvFlags}
    (hg : fl.with_guarded_fix = true) {u r : LBTerm} (h : WcbvEval E fl u r) :
    ∀ {a : LBTerm}, u = .app gCxFix a → False := by
  induction h with
  | @beta f a n b av r hf _ _ _ _ _ =>
      intro a₀ heq
      injection heq with hfe _
      subst hfe
      exact absurd (eval_deterministic (WcbvEval.fix_atom gCxFixDefs 0) hf) (by simp)
  | @app_box f a av hf _ _ _ =>
      intro a₀ heq
      injection heq with hfe _
      subst hfe
      exact absurd (eval_deterministic (WcbvEval.fix_atom gCxFixDefs 0) hf) (by simp)
  | @construct_app hb f a a' iid c args ar hf _ _ _ _ _ =>
      intro a₀ heq
      injection heq with hfe _
      subst hfe
      have hval := eval_deterministic (WcbvEval.fix_atom gCxFixDefs 0) hf
      exact absurd hval.symm
        (LBTerm.mkApps_construct_ne_fix (iid := iid) (c := c) (defs := gCxFixDefs) (i := 0)
          (args := args) (argsv := []))
  | @fix_guarded hg' f a av defs idx def_i argsv r hf ha hsel hrarg hrec _ _ ihrec =>
      intro a₀ heq
      injection heq with hfe hae
      subst hfe; subst hae
      obtain ⟨hd, hi, hargs⟩ :=
        LBTerm.mkApps_fix_inj (defs := gCxFixDefs) (i := 0) (argsv := [])
          (eval_deterministic (WcbvEval.fix_atom gCxFixDefs 0) hf)
      subst hd; subst hi; subst hargs
      obtain rfl : def_i = { name := .named "f", body := (.bvar 0 : LBTerm) } := by
        simpa [gCxFixDefs] using hsel.symm
      exact ihrec (a := av) rfl
  | @fix_stuck hg' f a av defs idx def_i argsv hf ha hsel hlt _ _ =>
      intro a₀ heq
      injection heq with hfe hae
      subst hfe; subst hae
      obtain ⟨hd, hi, hargs⟩ :=
        LBTerm.mkApps_fix_inj (defs := gCxFixDefs) (i := 0) (argsv := [])
          (eval_deterministic (WcbvEval.fix_atom gCxFixDefs 0) hf)
      subst hd; subst hi; subst hargs
      obtain rfl : def_i = { name := .named "f", body := (.bvar 0 : LBTerm) } := by
        simpa [gCxFixDefs] using hsel.symm
      simp at hlt
  | @fix_unguarded hg' f a av defs idx def_i r _ _ _ _ _ _ =>
      exact absurd hg (by rw [hg']; simp)
  | @app_cong f a f' a' hf hstuck _ _ _ =>
      intro a₀ heq
      injection heq with hfe _
      subst hfe
      rw [← eval_deterministic (WcbvEval.fix_atom gCxFixDefs 0) hf, isStuckApp_fix_bare] at hstuck
      exact absurd hstuck (by simp)
  | _ => intro a₀ heq; cases heq

/-- The counterexample's source redex `SEvalDataC`-evaluates (one β step, to
`fun (a : Prop) => a`) — at every `Γ`/`Esrc`. -/
theorem gCxSEval {Γ : ErasureCtx} {Esrc : SEnv} : SEvalDataC Γ Esrc gCxApp gCxId :=
  .beta (.lam _ _ _ _) (.lam _ _ _ _) (.lam _ _ _ _)

/-- …and it is genuinely typeable: `TrExprS` over the empty (well-formed) `VEnv`,
no universe parameters, empty local context. -/
theorem gCxTrExprS : TrExprS .empty [] [] gCxApp
    (.app (.lam (.forallE (.sort .zero) (.sort .zero)) (.bvar 0))
          (.lam (.sort .zero) (.bvar 0))) := by
  have hsort : ∀ {Γ : List VExpr},
      VEnv.HasType .empty 0 Γ (.sort .zero) (.sort (.succ .zero)) :=
    .sortDF trivial trivial rfl
  have harr : VEnv.HasType .empty 0 [] (.forallE (.sort .zero) (.sort .zero))
      (.sort (.imax (.succ .zero) (.succ .zero))) := .forallEDF hsort hsort
  have hfind : ∀ {A : VExpr}, Lean4Lean.VLCtx.find? [(none, Lean4Lean.VLocalDecl.vlam A)] (.inl 0)
      = some (.bvar 0, A.lift) := by
    intro A
    simp [Lean4Lean.VLCtx.find?, Lean4Lean.VLCtx.next,
      Lean4Lean.VLocalDecl.value, Lean4Lean.VLocalDecl.type]
  exact .app (.lamDF harr (.bvar .zero)) (.lamDF hsort (.bvar .zero))
    (.lam ⟨_, harr⟩ (.forallE ⟨_, hsort⟩ ⟨_, hsort⟩ (.sort rfl) (.sort rfl)) (.bvar hfind))
    (.lam ⟨_, hsort⟩ (.sort rfl) (.bvar hfind))

/-- **The pre-W1 rule's content, as a hypothesis.** Exactly what
`erases_fix_of_closed` used to conclude, at the counterexample's block: *any* closed,
fvar-free source `.lam` relates to `fix f. f`, at any context, with no tie to the block
whatsoever. It was provable before slice W1 (`erases_fix_of_closed` needed only the two
closedness facts, and imposed nothing on `Γ`); it is refutable after it
(`not_contentlessFix`). -/
def ContentlessFix (env : VEnv) (Us : List Name) (Γ : ErasureCtx) : Prop :=
  ∀ {Δ : VLCtx} {n : Name} {ty b : Expr} {bi : BinderInfo},
    Closed (.lam n ty b bi) 0 → FVarsIn (fun _ => False) (.lam n ty b bi) →
      Erases env Us Γ Δ (.lam n ty b bi) gCxFix

/-- The counterexample's source head is closed… -/
private theorem gCxHId_closed : Closed gCxHId 0 :=
  ⟨⟨trivial, trivial⟩, Nat.zero_lt_one⟩

/-- …and fvar-free, which is all the pre-W1 rule asked for. -/
private theorem gCxHId_fvarFree : FVarsIn (fun _ => False) gCxHId :=
  ⟨⟨rfl, rfl⟩, trivial⟩

/-- The head of the redex erases to `fix f. f` — under `ContentlessFix`, which is the
very `erases_fix_of_closed` call the pre-W1 fixture made. -/
theorem gCxErasesHead {env : VEnv} {Us : List Name} {Γ : ErasureCtx} {Δ : VLCtx}
    (hcf : ContentlessFix env Us Γ) : Erases env Us Γ Δ gCxHId gCxFix :=
  hcf gCxHId_closed gCxHId_fvarFree

/-- The whole redex erases to `(fix f. f) (λ. #0)`. -/
theorem gCxErases {Γ : ErasureCtx} (hcf : ContentlessFix .empty [] Γ) :
    Erases .empty [] Γ [] gCxApp gCxApp' :=
  .app (gCxErasesHead hcf) (.lam (.sort rfl) (.bvar 0))

/-- …in applied (non-block) form. -/
theorem gCxNoBlock : NoBlock gCxApp' := by
  show NoBlock (.app gCxFix gCxId')
  refine ⟨?_, ?_⟩ <;> simp [gCxFix, gCxId', gCxFixDefs]

/-- The counterexample's target environment is *fix-free*, so `NoFixEnv` is **not**
what fails: the load-bearing premise is `NoFix t` on the term. -/
theorem gCxNoFixEnv : NoFixEnv ([] : GlobalDeclarations) := by
  intro kn body h
  simp [LBTerm.envLookup] at h

/-- A concrete `Γ` for the counterexample: no constructors, no `casesOn`s. -/
private def gCxΓ : ErasureCtx where
  inductives := fun _ => none
  constants := fun _ => rootKername "f"
  ctors := fun _ => none
  ctorArities := fun _ => none
  casesOns := fun _ => none

/-- **Under the pre-W1 rule, `erases_correct_data` minus `NoFix` was false.** The
statement below is `erases_correct_data` verbatim, with the `hnfenv` premise and the two
`NoFix` slots deleted — the "just relax the premise" reading of the recursion wall. It is
refuted by the fixture above, from the single hypothesis `ContentlessFix`, which is what
the pre-W1 `Erases.fix`/`erases_fix_of_closed` handed out for free.

This was *not* a defect of the simulation proof: it was a defect of `Erases.fix`, which
related an arbitrary closed `.lam` to an arbitrary closed `.fix` block. Re-founding that
rule (slice W1, done) is therefore a precondition for dropping `NoFix` (slice W2), and
`not_contentlessFix` below records that the precondition is met. -/
theorem erases_correct_data_without_noFix_false_of_contentless_fix
    (hcf : ContentlessFix .empty [] gCxΓ) :
    ¬ (∀ {env : VEnv}, env.WF → ∀ {Us : List Name} {Δ : VLCtx}, VLCtx.WF env Us.length Δ →
        ∀ {Γ : ErasureCtx} {Esrc : SEnv} {E : GlobalDeclarations},
          SEnvConsistent env Us Esrc → ErasesEnvDeltaData env Us Γ Esrc E →
          ErasesEnvCtor Γ E →
          (∀ {cn : Name} {iid : InductiveId} {cidx : Nat},
             Γ.ctors cn = some (iid, cidx) → Γ.casesOns cn = none) →
          ∀ {e v : Expr}, SEvalDataC Γ Esrc e v →
            ∀ {ve : VExpr} {t : LBTerm},
              TrExprS env Us Δ e ve → Erases env Us Γ Δ e t → NoBlock t →
              ∃ t' vve, WcbvEval E appliedFlags t t' ∧ TrExprS env Us Δ v vve ∧
                Erases env Us Γ Δ v t' ∧ NoBlock t') := by
  intro h
  obtain ⟨t', _, hev, _⟩ :=
    h (env := .empty) ⟨[], .empty⟩ (Δ := []) trivial (Γ := gCxΓ) (Esrc := fun _ => none)
      (E := []) (fun h₀ _ => nomatch h₀) (fun h₀ => nomatch h₀)
      (fun h₀ _ => nomatch h₀) (fun h₀ => nomatch h₀)
      gCxSEval gCxTrExprS (gCxErases hcf) gCxNoBlock
  exact no_wcbvEval_app_gCxFix rfl hev rfl

/-- **…and slice W1 closed exactly that hole.** At the counterexample's own `Γ` — which
registers no recursion — nothing erases to `fix f. f`: the only rule with a `.fix` target
and a `.lam` source is `Erases.fix`, whose `hreg` premise demands that `Γ` record the
block for the block's own names. So the hypothesis the refutation above runs on is no
longer available, and the refutation no longer refutes anything about the current
relation. (It is also the honest statement of *why* `fix f. f` is unrelatable: the
re-founded rule's `hbodies` at such a block degenerates into its own conclusion.) -/
theorem not_contentlessFix (env : VEnv) (Us : List Name) :
    ¬ ContentlessFix env Us gCxΓ := by
  intro hcf
  have hd : Erases env Us gCxΓ [] gCxHId gCxFix :=
    hcf gCxHId_closed gCxHId_fvarFree
  obtain ⟨_, _, ⟨nm, hreg⟩, _⟩ := Erases.fix_inv (defs := gCxFixDefs) (idx := 0) hd
  exact absurd hreg (by simp [gCxΓ])

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
