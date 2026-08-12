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

/-- The one-def block behind `gFixR`. -/
private def gFixDefsR : List (@FixDef LBTerm) := [{ name := .named "f", body := .bvar 0 }]

/-- Its stored `.fix` decl body — the `def f := f` self-loop. -/
private def gFixR : LBTerm := .fix gFixDefsR 0

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
    obtain rfl : j = 0 := by
      simp only [gFixDefsR, List.length_cons, List.length_nil] at h; omega
    exact (closeFixFold_fvar_head ⟨`x⟩ 0 []).symm
  · -- hbodies: .fvar x erases to .fvar x
    intro j h
    obtain rfl : j = 0 := by
      simp only [gFixDefsR, List.length_cons, List.length_nil] at h; omega
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

/-! ## Part 3b — the honest counterexample: `Erases.fix` is contentless, so `NoFix`
is load-bearing (recursion wall, slice W0)

`Erases.fix` (`Erases.lean:462`) imposes **no relation whatsoever** between its
conclusion's source `.lam n ty b bi` and the block data `osrcs`/`obodies`/`defs`:
`n ty b bi` occur only in the three Expr-side inertness equalities and in the
conclusion, and nothing ties `.lam n ty b bi` to `osrcs[idx]`, nor `osrcs[j]` to the
real body of def `j`. `gErases_fix` above already says so out loud — the dummy
`fun (a : Prop) => Prop` erases to `fix f. f`.

This section turns that observation into a machine-checked refutation, because it has
a consequence for the forward simulations: **the `NoFix t` premise of
`erases_correct_data` is load-bearing for *soundness*, not merely for convenience.**
Swap the fixture's dummy source for the (equally closed, equally fvar-free)
higher-order identity `fun (h : Prop → Prop) => h` — `erases_fix_of_closed` applies
verbatim — and apply it to `fun (a : Prop) => a`. That gives

* a source term that `SEvalDataC`-evaluates in one β step (`gCxSEval`) and is
  genuinely `TrExprS`-typeable over the empty, well-formed `VEnv` (`gCxTrExprS`);
* a target `.app (fix f. f) (λ. #0)` that it erases to, in applied (`NoBlock`) form
  (`gCxErases`, `gCxNoBlock`);
* and **no** `WcbvEval` value for that target, at *any* environment
  (`no_wcbvEval_app_gFixR`): with `principalArgIdx = 0` the only applicable rule is
  `fix_guarded` (`beta`/`app_box`/`construct_app` need a different head value and
  `WcbvEval` is deterministic; `fix_stuck` needs `argsv.length < 0`; `fix_unguarded`
  is flag-off; `app_cong` is refuted by `isStuckApp_fix_bare`), and its reduct is the
  *same* redex, since `substList (fixSubst gFixDefsR) (.bvar 0) = fix f. f`. So no
  finite derivation exists.

`erases_correct_data_without_noFix_false` therefore refutes `erases_correct_data`
(`ErasesCorrectData.lean:886`) with `hnfenv`, `NoFix t` and `NoFix t'` deleted and
*everything else verbatim*. Note the counterexample runs at `E = []`, where
`NoFixEnv E` **holds** (`gCxNoFixEnv`): it is `NoFix t` alone that is doing the work.

**Consequence for the recursion wall.** Admitting `.fix` targets into the simulations
is not "relax a premise" — the rule that the premise was hiding is vacuous, and must
be re-founded first (minimally: the missing `srcs[idx] = .lam n ty b bi` link, plus a
`.const`-source leaf rule, since a fix *unfolding* puts `.fix defs j` where the source
has a sibling `.const nⱼ`). Until that lands, `NoFix` stays. These declarations are
the record of why, and are expected to be retired together with the dummy fixture when
the re-founded rule arrives. -/

/-- Source: `Prop → Prop`, the type of the counterexample's argument. -/
private def gCxArr : Expr := .forallE `a (.sort .zero) (.sort .zero) .default

/-- Source: `fun (a : Prop) => a`. -/
private def gCxId : Expr := .lam `a (.sort .zero) (.bvar 0) .default

/-- Source: `fun (h : Prop → Prop) => h`. Closed and fvar-free, hence — by
`erases_fix_of_closed`, exactly as for `gLamR` — relatable to `gFixR`. -/
private def gCxHId : Expr := .lam `h gCxArr (.bvar 0) .default

/-- Source: the redex `(fun (h : Prop → Prop) => h) (fun (a : Prop) => a)`. -/
private def gCxApp : Expr := .app gCxHId gCxId

/-- Target: the erasure of `gCxId`. -/
private def gCxId' : LBTerm := .lambda (nameToBinder `a) (.bvar 0)

/-- Target: the erasure of `gCxApp` — `(fix f. f) (λ. #0)`. -/
private def gCxApp' : LBTerm := .app gFixR gCxId'

/-- **The target of the counterexample has no value.** No `WcbvEval` derivation
concludes `.app (fix f. f) a` for any argument `a`, at any environment and any flags
with `with_guarded_fix = true` (in particular `appliedFlags` and `optFlags`).

The induction is on the target derivation: every rule that can conclude an
application either needs the head to evaluate to something other than a bare `fix`
(refuted by determinism against `fix_atom`), or is flag- or arity-blocked
(`fix_unguarded`, `fix_stuck`, `app_cong`), or is `fix_guarded` — whose last premise
is `WcbvEval E fl (.app (fix f. f) av) r`, a strictly smaller derivation of the same
shape, closed by the induction hypothesis. -/
theorem no_wcbvEval_app_gFixR {E : GlobalDeclarations} {fl : WcbvFlags}
    (hg : fl.with_guarded_fix = true) {u r : LBTerm} (h : WcbvEval E fl u r) :
    ∀ {a : LBTerm}, u = .app gFixR a → False := by
  induction h with
  | @beta f a n b av r hf _ _ _ _ _ =>
      intro a₀ heq
      injection heq with hfe _
      subst hfe
      exact absurd (eval_deterministic (WcbvEval.fix_atom gFixDefsR 0) hf) (by simp)
  | @app_box f a av hf _ _ _ =>
      intro a₀ heq
      injection heq with hfe _
      subst hfe
      exact absurd (eval_deterministic (WcbvEval.fix_atom gFixDefsR 0) hf) (by simp)
  | @construct_app hb f a a' iid c args ar hf _ _ _ _ _ =>
      intro a₀ heq
      injection heq with hfe _
      subst hfe
      have hval := eval_deterministic (WcbvEval.fix_atom gFixDefsR 0) hf
      exact absurd hval.symm
        (LBTerm.mkApps_construct_ne_fix (iid := iid) (c := c) (defs := gFixDefsR) (i := 0)
          (args := args) (argsv := []))
  | @fix_guarded hg' f a av defs idx def_i argsv r hf ha hsel hrarg hrec _ _ ihrec =>
      intro a₀ heq
      injection heq with hfe hae
      subst hfe; subst hae
      obtain ⟨hd, hi, hargs⟩ :=
        LBTerm.mkApps_fix_inj (defs := gFixDefsR) (i := 0) (argsv := [])
          (eval_deterministic (WcbvEval.fix_atom gFixDefsR 0) hf)
      subst hd; subst hi; subst hargs
      obtain rfl : def_i = { name := .named "f", body := (.bvar 0 : LBTerm) } := by
        simpa [gFixDefsR] using hsel.symm
      exact ihrec (a := av) rfl
  | @fix_stuck hg' f a av defs idx def_i argsv hf ha hsel hlt _ _ =>
      intro a₀ heq
      injection heq with hfe hae
      subst hfe; subst hae
      obtain ⟨hd, hi, hargs⟩ :=
        LBTerm.mkApps_fix_inj (defs := gFixDefsR) (i := 0) (argsv := [])
          (eval_deterministic (WcbvEval.fix_atom gFixDefsR 0) hf)
      subst hd; subst hi; subst hargs
      obtain rfl : def_i = { name := .named "f", body := (.bvar 0 : LBTerm) } := by
        simpa [gFixDefsR] using hsel.symm
      simp at hlt
  | @fix_unguarded hg' f a av defs idx def_i r _ _ _ _ _ _ =>
      exact absurd hg (by rw [hg']; simp)
  | @app_cong f a f' a' hf hstuck _ _ _ =>
      intro a₀ heq
      injection heq with hfe _
      subst hfe
      rw [← eval_deterministic (WcbvEval.fix_atom gFixDefsR 0) hf, isStuckApp_fix_bare] at hstuck
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

/-- The head of the redex erases to `gFixR`, by the very same `erases_fix_of_closed`
call that `gErases_fix` makes — only the (unconstrained) source `.lam` differs. -/
theorem gCxErasesHead {env : VEnv} {Us : List Name} {Γ : ErasureCtx} {Δ : VLCtx} :
    Erases env Us Γ Δ gCxHId gFixR := by
  refine erases_fix_of_closed (Δf := Δ) (ids := [⟨`x⟩])
    (osrcs := [.fvar ⟨`x⟩]) (obodies := [.fvar ⟨`x⟩])
    Nat.zero_lt_one rfl rfl rfl ⟨⟨trivial, trivial⟩, Nat.zero_lt_one⟩ ⟨⟨rfl, rfl⟩, trivial⟩
    ?_ ?_ ?_ ?_
  · exact ⟨Nat.zero_lt_one, trivial⟩
  · intro x
    show ¬ hasFVar x (LBTerm.fix gFixDefsR 0)
    simp only [gFixDefsR, hasFVar_fix, hasFVarDefs, hasFVar_bvar, or_self, not_false_iff]
  · intro j h
    obtain rfl : j = 0 := by simp only [gFixDefsR, List.length_cons, List.length_nil] at h; omega
    exact (closeFixFold_fvar_head ⟨`x⟩ 0 []).symm
  · intro j h
    obtain rfl : j = 0 := by simp only [gFixDefsR, List.length_cons, List.length_nil] at h; omega
    exact .fvar ⟨`x⟩

/-- The whole redex erases to `(fix f. f) (λ. #0)`. -/
theorem gCxErases {Γ : ErasureCtx} : Erases .empty [] Γ [] gCxApp gCxApp' :=
  .app gCxErasesHead (.lam (.sort rfl) (.bvar 0))

/-- …in applied (non-block) form. -/
theorem gCxNoBlock : NoBlock gCxApp' := by
  show NoBlock (.app gFixR gCxId')
  refine ⟨?_, ?_⟩ <;> simp [gFixR, gCxId', gFixDefsR]

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

/-- **`erases_correct_data` minus `NoFix` is false.** The statement below is
`erases_correct_data` (`ErasesCorrectData.lean:886`) verbatim, with the `hnfenv`
premise and the two `NoFix` slots deleted — the "just relax the premise" reading of
the recursion wall. It is refuted by the fixture above.

This is *not* a defect of the simulation proof: it is a defect of `Erases.fix`, which
relates an arbitrary closed `.lam` to an arbitrary closed `.fix` block. Re-founding
that rule (slice W1) is a precondition for dropping `NoFix` (slice W2); see the
section docstring. -/
theorem erases_correct_data_without_noFix_false :
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
      gCxSEval gCxTrExprS gCxErases gCxNoBlock
  exact no_wcbvEval_app_gFixR rfl hev rfl

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
