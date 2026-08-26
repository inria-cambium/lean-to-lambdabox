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
  the fvar-instantiated opened body `substFix ids defs obodies[j]` (`hbodies`). Since
  slice W3.1 the fvar→block instantiation is *proved* (`Erases.instFixvars`, Part 1b), so
  what is left to supply is the run's own output at the block-local `Γ` — the bridge's
  motive 4 gives it per term, and slice D6 (`ColdStartRun.run_rec_exit_siblings`) walks
  the block's `List.mapM` to hand back the per-sibling runs; joining the two still needs
  `Γ` inside the motives (design §W3.2/D8).
  `erases_fix_of_open` is `erases_fix_of_closed` already composed with the
  instantiation, i.e. the form that correspondence hands over;
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

/-! ## Part 1b — `Erases.instFixvars`: instantiating the block's own fixvars (W3.1)

This is the `visitMutual` → registration correspondence at the `Erases` level.

The shipping run erases sibling `j`'s body under
`withReader (fun env => { env with fixvars := nms.zip ids })`, so an in-block reference
comes out as `.fvar ids[k]` (`visitConst`, modelled by the `Erases.fixvar` leaf); `mkDef`
then closes those fvars with `closeFix ids`. `Erases.fix`, by contrast, wants each body's
erasure against the def's *dynamic* unfolding `substList (fixSubst defs) defs[j].body` —
what `WcbvEval.fix_guarded` actually produces. Slice W0's `closeFix_substList_fixSubst`
already reduces the closing to the static `substFix ids defs`; the missing move was the
corresponding one on the **derivation**:

    Erases … (Γ.withFixvars fv) Δ e t   ⟹   Erases … Γ Δ e (substFix ids defs t)

The fixvar leaf is where the two registrations meet: `fv nm = some ids[j]` becomes
`Γ.recBodies nm = some (defs, j)`, so `Erases.fixvar` becomes `Erases.const_fix` and the
target `.fvar ids[j]` becomes `.fix defs j`. Every other rule is structural — `substFix`
commutes with every node (`FixUnfold`, Part 3b) and is the identity on the closed,
fvar-free blocks the `const_fix` arm carries.

## The two side conditions, and the one residue

* `hsc : FVarsIn (· ∉ ids) e` — the *source* must not itself mention a fixvar. It is the
  `fvar` arm: `Erases.fvar` relates `.fvar y` to `.fvar y`, and if `y` were a fixvar the
  conclusion would demand `Erases … (.fvar y) (.fix defs j)`, which no rule provides. Free
  at the call site: an `_unsafe_rec` body is a closed, fvar-free `Expr`, and the run's
  fixvars are minted fresh.
* `hlink` — the block-local map and `Γ.recBodies` agree. This is exactly what
  `visitMutual` establishes: it mints `ids`, erases under them, then files `(defs, j)`
  for each of the block's names.
* `hnest` — **the residue**, and the one obligation this induction cannot discharge.
  `Erases.fix`'s `hbodies` premise lives at the rule's own `Γ`, so rebuilding a *nested*
  block at the outer `Γ` would need each of its sibling bodies transported too — and the
  rule carries neither the source-side fvar-freeness `hsc` needs for those bodies nor the
  target-side inertness of their (already unfolded) targets. Carrying it as a `Prop`
  hypothesis is the honest shape, and it is **unreachable in the intended use**: the
  shipping eraser never nests a `.fix` inside a body, because a reference to an
  unregistered constant is erased to `.const kn` (`get_constant_kername`'s miss branch
  runs `visitMutual` and returns a *kername*), never to a block node. The `const_fix` arm
  needs no such hypothesis — its premises are `Γ`-blind apart from `recBodies`, which
  `withFixvars` leaves alone. -/

/-- `substFix` pushes under a re-wrapped `casesOn` alternative (mirror of
`shift_mkLambdas`/`toBvar_mkLambdas`; the substituted nodes are closed, so no level
bookkeeping happens). -/
theorem substFix_mkLambdas (ids : List FVarId) (defs : List (@FixDef LBTerm))
    (names : List BinderName) (body : LBTerm) :
    substFix ids defs (mkLambdas names body) = mkLambdas names (substFix ids defs body) := by
  induction names with
  | nil => rfl
  | cons n ns ih =>
      show substFVarList _ (LBTerm.lambda n (mkLambdas ns body)) = _
      rw [substFVarList_lambda]
      show LBTerm.lambda n (substFix ids defs (mkLambdas ns body)) = _
      rw [ih]; rfl

/-- **Instantiate the block's fixvars with the block's own nodes.** An erasure derived
*inside* the block (at `Γ.withFixvars fv`) becomes one at the plain `Γ`, with every
`.fvar ids[j]` replaced by `.fix defs j` — which is precisely the `hbodies` shape
`erases_fix_of_closed` consumes. See the section docstring for the three hypotheses. -/
theorem Erases.instFixvars {env : VEnv} {Us : List Name} {Γ : ErasureCtx}
    {fv : Name → Option FVarId} {ids : List FVarId} {defs : List (@FixDef LBTerm)}
    (hnd : ids.Nodup)
    (hfcl : LBClosed (LBTerm.fix defs 0) 0)
    (hffv : ∀ x, ¬ hasFVar x (LBTerm.fix defs 0))
    (hlink : ∀ (nm : Name) (x : FVarId), fv nm = some x →
      ∃ j, ∃ h : j < ids.length, (ids[j]'h) = x ∧ Γ.recBodies nm = some (defs, j))
    (hnest : ∀ {Δ' : VLCtx} {n' : Name} {ty' b' : Expr} {bi' : BinderInfo}
        {d' : List (@FixDef LBTerm)} {i' : Nat},
        Erases env Us (Γ.withFixvars fv) Δ' (.lam n' ty' b' bi') (.fix d' i') →
        Erases env Us Γ Δ' (.lam n' ty' b' bi') (.fix d' i'))
    {Δ : VLCtx} {e : Expr} {t : LBTerm}
    (h : Erases env Us (Γ.withFixvars fv) Δ e t) :
    FVarsIn (· ∉ ids) e → Erases env Us Γ Δ e (substFix ids defs t) := by
  -- `LBClosed`/`hasFVar` on a `.fix` node do not look at the index, so one witness each
  -- serves every sibling (same trick as `erases_fix_of_closed`).
  have hfclj : ∀ j, LBClosed (LBTerm.fix defs j) 0 := fun _ => hfcl
  have hffvj : ∀ (x : FVarId) (j : Nat), ¬ hasFVar x (LBTerm.fix defs j) := fun x _ => hffv x
  -- `substFix` is the identity on a block the derivation certifies fvar-free.
  have hinert : ∀ (d' : List (@FixDef LBTerm)) (i' : Nat),
      (∀ (y : FVarId) (l : Nat), toBvar y l (LBTerm.fix d' i') = .fix d' i') →
      substFix ids defs (.fix d' i') = .fix d' i' := fun d' i' htobv =>
    substFVarList_eq_self_of_not_hasFVar _ _ (fun p _ =>
      not_hasFVar_of_toBvar_eq_self p.1 _ 0 (htobv p.1 0))
  -- …and on an fvar that is not one of the block's.
  have hfvarid : ∀ (y : FVarId), y ∉ ids → substFix ids defs (.fvar y) = .fvar y := by
    intro y hy
    refine substFVarList_eq_self_of_not_hasFVar _ _ (fun p hp => ?_)
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    simp only [hasFVar_fvar]
    intro he
    exact hy (by rw [he]; exact List.fst_mem_of_mem_zipIdx hq)
  induction h with
  | box htr her =>
      intro _
      simp only [substFix, substFVarList_box]
      exact .box htr her
  | lit hcl _ ih => intro _; exact .lit hcl (ih FVarsIn.toConstructor)
  | bvar i =>
      intro _
      simp only [substFix, substFVarList_bvar]
      exact .bvar i
  | fvar y => intro hsc; rw [hfvarid y hsc]; exact .fvar y
  | const n us kn hkn hctor hcases =>
      intro _
      simp only [substFix, substFVarList_const]
      exact .const n us kn hkn hctor hcases
  | app _ _ ihf iha =>
      intro hsc
      simp only [substFix, substFVarList_app]
      exact .app (ihf hsc.1) (iha hsc.2)
  | lam hty _ ihb =>
      intro hsc
      simp only [substFix, substFVarList_lambda]
      exact .lam hty (ihb hsc.2)
  | letE hty hval _ _ ihv ihb =>
      intro hsc
      simp only [substFix, substFVarList_letIn]
      exact .letE hty hval (ihv hsc.2.1) (ihb hsc.2.2)
  | ctor_head cn us iid cidx hc =>
      intro _
      simp only [substFix, substFVarList_construct, List.map_nil]
      exact .ctor_head cn us iid cidx hc
  | @ctor _ cn us iid cidx args args' hc hlen _ ihargs =>
      intro hsc
      obtain ⟨-, hall⟩ := fvarsIn_foldl_app hsc
      simp only [substFix, substFVarList_construct]
      refine .ctor cn us iid cidx hc (by simp [hlen]) (fun i hi => ?_)
      rw [List.getElem_map]
      exact ihargs i hi (hall _ (List.getElem_mem hi))
  | @cases _ con us iid numParams pre discr discr' minors alts' nfs hc hpre hnfs _
      hlen hnlen harity _ ihd ihalts =>
      intro hsc
      obtain ⟨-, hall⟩ := fvarsIn_foldl_app hsc
      simp only [substFix, substFVarList_case]
      refine Erases.cases (Γ := Γ) con us iid numParams pre
        (hc : Γ.casesOns con = some (iid, numParams))
        (hpre : Γ.casesDiscrPos con = some pre.length)
        (hnfs : Γ.ctorFields iid = some nfs)
        (ihd (hall _ (List.mem_cons_self ..)))
        (alts' := alts'.map (fun a => (a.1, substFix ids defs a.2)))
        (by simpa using hlen) (by simpa using hnlen)
        (fun j hj => by rw [List.getElem_map]; exact harity j (by simpa using hj))
        (fun j hj => ?_)
      rw [List.getElem_map]
      show Erases env Us Γ _ _ (mkLambdas (alts'[j]'(hlen ▸ hj)).1
        (substFix ids defs (alts'[j]'(hlen ▸ hj)).2))
      rw [← substFix_mkLambdas]
      exact ihalts j hj (hall _ (List.mem_cons_of_mem _ (List.getElem_mem hj)))
  | const_fix nm us hrec hctor hcases hshift hsubst htobv =>
      intro _
      rw [hinert _ _ htobv]
      exact .const_fix nm us hrec hctor hcases hshift hsubst htobv
  | @fix Δc idx nm' tty tb tbi nms srcs d' hidx hnlen hslen hsrc hreg hrarg
      hlift hinst habsl hshift hsubst htobv hbodies _ihb =>
      intro _
      rw [hinert _ _ htobv]
      exact hnest (.fix idx hidx hnlen hslen hsrc hreg hrarg hlift hinst habsl hshift hsubst
        htobv hbodies)
  | fixvar nm us x hfx hctor hcases hfresh =>
      -- The leaf the whole lemma exists for: the block-local fvar becomes the block.
      intro _
      obtain ⟨j, hj, rfl, hrec⟩ := hlink nm _ hfx
      rw [substFix_fvar_getElem hnd (fun y _ => hffvj y) j hj]
      exact .const_fix nm us hrec hctor hcases
        (fun d c => LBClosed.shift_eq (hfclj j) (Nat.zero_le c) d)
        (fun s d => LBClosed.subst_eq (hfclj j) (Nat.zero_le d) s)
        (fun y l => toBvar_eq_of_not_hasFVar y l _ (hffvj y j))

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

/-- **The `visitMutual` correspondence, packaged** (recursion wall, W3.1). Same conclusion
as `erases_fix_of_closed`, but the bodies premise is the one a run actually produces: each
sibling body erases *inside the block*, i.e. at `Γ.withFixvars fv`, with in-block
references still sitting as the run's fresh fvars. `Erases.instFixvars` closes the gap.

So the whole chain from a `visitMutual` run to `Erases.fix` is: `visitExpr` refines
`Erases` at the block-local `Γ` (the bridge's motive 4, whose fixvar branch W3.1 gave
content) ⟹ `instFixvars` instantiates the fixvars ⟹ `closeFix_substList_fixSubst` turns
`mkDef`'s closing into the dynamic unfolding ⟹ `Erases.fix`. What is *not* here is the
environment-level walk that supplies the per-sibling run facts: slice D6
(`ColdStartRun.run_rec_exit_siblings`) produces the runs, but at the block-local
`Γ.withFixvars fv`, so consuming them needs `Γ` inside the bridge's motives (§W3.2/D8) —
`ColdStartDelta`'s recursion section is the premise-by-premise ledger.

## The `hopen` repair (slice `rec`)

`hopen` used to quantify over **every** `Δf`, unrestricted, and in that form it is
**unsatisfiable for every self-referential block** — that is, for every real one. A body
that references a sibling `nm` must, at `Γ.withFixvars fv`, derive
`Erases … Δf (.const nm us) (.fvar x)`, and `Erases.fixvar` is the *only* rule with source
`.const` and target `.fvar` (the others give `.const kn`, `.construct …`, `.fix …` or
`.box`). Its `hfresh : x ∉ Δf.fvars` then fails the moment `Δf` mentions one of the block's
own ids. The theorem was therefore vacuous in its intended use, and nothing caught it
because it had **no non-vacuity guard**: this file's own fixture `gErasesOpenR` carries
precisely the missing side condition (`gIdR ∉ Δ.fvars`) and so could never feed the
theorem, which is why the guard chain went `gErasesOpenR → gInstFixvarsR → gErases_fix`
through `erases_fix_of_closed` instead. The absent guard was the tell.

`hopen` is now conditioned on `Δf` being fresh for `ids`, which is exactly what the run
establishes (`visitMutual` mints the block's fixvars *before* `visitExpr` opens any
binder — `BridgeInv.fixfresh`) and exactly what `gErasesOpenR` provides.

That leaves `Erases.fix`'s `hbodies` premise, which is genuinely `∀ Δf` with no side
condition, to be rebuilt. It is, and at the *outer* `Γ`, where the fixvar leaf is gone:
instantiate `hopen` at `Δf := []` (fresh outright, `VLCtx.fvars [] = []`), push it through
`Erases.instFixvars` — after which the block's fixvars have become `.fix defs j` nodes and
no `.fvar` survives — and re-widen with `ErasesStrengthen.erases_weak_any`, which
transports out of `[]` into *every* `VLCtx` for a closed, fvar-free source and a closed
target. Hence the two new premises: `hnfv` (the fixvar leaf is dead at the outer `Γ` —
the same scope restriction every top-level capstone already pins) and `hsclosed` (the
block's sources are closed, which for top-level recursive definitions they are, and which
`heclosed` already asserted for the `idx`-th one alone). `henv` is needed because
`erases_weak_any` weakens lean4lean witnesses.

## The `[]`-only form (slice δ-D8)

The proof below instantiates `hopen` at **exactly one** context, `Δf := []`, and nowhere
else — the freshness side condition exists to make *that* instantiation legal. So the
`∀ Δf` is not load-bearing, and `erases_fix_of_open_nil` states the premise where it is
actually consumed. That is a strictly weaker premise, hence a strictly stronger theorem,
and it is what a *run* can supply: `ColdStartRun.run_rec_exit_siblings` hands back one
`visitExpr` run per sibling, at one context, not a family of them.
`erases_fix_of_open` is now the corollary, kept verbatim in signature so its guard and
every other consumer are untouched. -/
theorem erases_fix_of_open_nil {env : VEnv} (henv : env.Ordered) {Us : List Name}
    {Γ : ErasureCtx} (hnfv : Γ.fixvars = fun _ => none)
    {fv : Name → Option FVarId}
    {Δ : VLCtx} {n : Name} {ty b : Expr} {bi : BinderInfo}
    {nms : List Name} {ids : List FVarId} {srcs : List Expr} {obodies : List LBTerm}
    {defs : List (@FixDef LBTerm)} {idx : Nat}
    (hidx : idx < defs.length)
    (hnlen : nms.length = defs.length)
    (hslen : srcs.length = defs.length)
    (hblen : obodies.length = defs.length)
    (hilen : ids.length = defs.length)
    (hnd : ids.Nodup)
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
    (hlink : ∀ (nm : Name) (x : FVarId), fv nm = some x →
      ∃ j, ∃ h : j < ids.length, (ids[j]'h) = x ∧ Γ.recBodies nm = some (defs, j))
    (hnest : ∀ {Δ' : VLCtx} {n' : Name} {ty' b' : Expr} {bi' : BinderInfo}
        {d' : List (@FixDef LBTerm)} {i' : Nat},
        Erases env Us (Γ.withFixvars fv) Δ' (.lam n' ty' b' bi') (.fix d' i') →
        Erases env Us Γ Δ' (.lam n' ty' b' bi') (.fix d' i'))
    (hsrcfv : ∀ j (h : j < defs.length),
        FVarsIn (fun _ => False) (srcs[j]'(hslen ▸ h)))
    (hsclosed : ∀ j (h : j < defs.length), Closed (srcs[j]'(hslen ▸ h)) 0)
    (hopen : ∀ j (h : j < defs.length),
        Erases env Us (Γ.withFixvars fv) [] (srcs[j]'(hslen ▸ h))
          (obodies[j]'(hblen ▸ h))) :
    Erases env Us Γ Δ (.lam n ty b bi) (.fix defs idx) :=
  erases_fix_of_closed hidx hnlen hslen hblen hilen hsrc hreg hrarg heclosed henofv
    hfclosed hffv hoclosed hclose
    (fun j h Δf =>
      -- The open premise fires at `[]`, which is fresh for the block outright
      -- (`VLCtx.fvars [] = []`). Instantiating there and re-widening afterwards is what
      -- makes the rebuilt `hbodies` unrestricted again — see the docstring.
      erases_weak_any henv hnfv (hsclosed j h) (hsrcfv j h)
        (LBClosed.substFVarList _
          (fun q hq => by obtain ⟨-, -, rfl⟩ := List.mem_map.mp hq; exact hfclosed)
          _ 0 (hoclosed j h))
        (Erases.instFixvars hnd hfclosed hffv hlink hnest (hopen j h)
          ((hsrcfv j h).mono (fun _ hf => hf.elim)))
        Δf)

/-- **The `∀`-fresh-`Δf` form**, unchanged in signature since slice `rec`: the corollary
of `erases_fix_of_open_nil` at `Δf := []`, which is fresh for the block outright. -/
theorem erases_fix_of_open {env : VEnv} (henv : env.Ordered) {Us : List Name}
    {Γ : ErasureCtx} (hnfv : Γ.fixvars = fun _ => none)
    {fv : Name → Option FVarId}
    {Δ : VLCtx} {n : Name} {ty b : Expr} {bi : BinderInfo}
    {nms : List Name} {ids : List FVarId} {srcs : List Expr} {obodies : List LBTerm}
    {defs : List (@FixDef LBTerm)} {idx : Nat}
    (hidx : idx < defs.length)
    (hnlen : nms.length = defs.length)
    (hslen : srcs.length = defs.length)
    (hblen : obodies.length = defs.length)
    (hilen : ids.length = defs.length)
    (hnd : ids.Nodup)
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
    (hlink : ∀ (nm : Name) (x : FVarId), fv nm = some x →
      ∃ j, ∃ h : j < ids.length, (ids[j]'h) = x ∧ Γ.recBodies nm = some (defs, j))
    (hnest : ∀ {Δ' : VLCtx} {n' : Name} {ty' b' : Expr} {bi' : BinderInfo}
        {d' : List (@FixDef LBTerm)} {i' : Nat},
        Erases env Us (Γ.withFixvars fv) Δ' (.lam n' ty' b' bi') (.fix d' i') →
        Erases env Us Γ Δ' (.lam n' ty' b' bi') (.fix d' i'))
    (hsrcfv : ∀ j (h : j < defs.length),
        FVarsIn (fun _ => False) (srcs[j]'(hslen ▸ h)))
    (hsclosed : ∀ j (h : j < defs.length), Closed (srcs[j]'(hslen ▸ h)) 0)
    (hopen : ∀ j (h : j < defs.length) (Δf : VLCtx),
        (∀ x ∈ ids, x ∉ Δf.fvars) →
        Erases env Us (Γ.withFixvars fv) Δf (srcs[j]'(hslen ▸ h))
          (obodies[j]'(hblen ▸ h))) :
    Erases env Us Γ Δ (.lam n ty b bi) (.fix defs idx) :=
  erases_fix_of_open_nil henv hnfv hidx hnlen hslen hblen hilen hnd hsrc hreg hrarg
    heclosed henofv hfclosed hffv hoclosed hclose hlink hnest hsrcfv hsclosed
    (fun j h => hopen j h [] (by simp))

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
free-`Δ` conclusion gives context-uniformity for free).

**Status after slice δ-D8: DEMOTED.** `ColdStartRun.run_rec_exit_siblings` (D6) walks the
`List.mapM` this record was standing in for and hands back the per-sibling runs plus
`mkDef`'s closing equation; `VisitExprRefines.visitExpr_refines_erases_block` (δ-D8)
supplies the per-sibling erasures at the block-local `Γ.withFixvars fv`, which is what the
`Γ`-inside-the-motives generalisation was wanted for and which the bridge turns out to
give for free — it is Γ-polymorphic as a statement, and exactly one of its premises breaks
at a block-local `Γ`. `ColdStartDelta.erases_rec_block_of_run` composes the two into this
record's `erase` field, and `ColdStartDelta.recEnvConsistent_of_block` into
`RecEnvConsistent` outright.

What survives is **not** a certificate about an erasure: it is the `Γ`↔run registration
agreement — "the `Γ` you supply names *this* block, under the map the run installed" —
which is irreducible at a parameter `Γ` (fixed before the run builds `defs`) and is
`BridgeInv.knames`-class, plus the standing `hnest` residue. This structure is kept as the
shape the *warm* theorems consume and as the record its own guards are stated at;
`ColdStartDelta`'s recursion section carries the premise-by-premise ledger and the note on
what still separates all this from the cold-start capstones. -/
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

/-! ### `Erases.instFixvars` fires on the same fixture (recursion wall, W3.1)

`gErases_fix` above starts from the *instantiated* body (`substFix [gIdR] gFixDefsR
gObodyR`), i.e. from the point where the sibling reference has already become the block.
The run produces the stage before that: the body erased **inside** the block, where the
sibling is still the fresh fvar `gIdR` and the derivation lives at a `Γ` carrying the
fixvar map. The two theorems below take that stage and walk it forward, so the
open→instantiated chain is witnessed on a genuinely recursive one-def block.

The guard is stated at `gΓOpenR = gΓR.withFixvars gFvR`, which is its own
`withFixvars gFvR` — so the `hnest` residue is discharged by `id` and nothing here is
assumed. That costs nothing on the content being checked: the fixvar → `const_fix`
conversion, which is what the lemma exists for, is identical at either `Γ`. -/

/-- The block-local fixvar map `visitMutual` installs while erasing `f`. -/
private def gFvR : Name → Option FVarId := fun n => if n = `f then some gIdR else none

/-- `gΓR` with that map installed — the reader `visitMutual` erases the block under. -/
private def gΓOpenR : ErasureCtx := gΓR.withFixvars gFvR

/-- The *open* stage: inside the block, `fun (a : Prop) => f a` erases to `λa. x #0`, with
the sibling `f` sent to its fixvar by the `Erases.fixvar` leaf. -/
theorem gErasesOpenR (env : VEnv) (Us : List Name) {Δ : VLCtx} (hx : gIdR ∉ Δ.fvars) :
    Erases env Us gΓOpenR Δ gLamR gObodyR :=
  .lam (ty' := .sort .zero) (.sort rfl)
    (.app (.fixvar `f [] gIdR (by simp [gΓOpenR, gΓR, gFvR]) rfl rfl (by simpa using hx))
      (.bvar 0))

/-- …and `Erases.instFixvars` carries it to the instantiated stage: the fixvar leaf
becomes `const_fix` and `.fvar x` becomes the block, giving exactly the `hbodies` premise
`erases_fix_of_closed` consumes — now *derived* from the run's own output shape instead of
built by hand. -/
theorem gInstFixvarsR (env : VEnv) (Us : List Name) {Δ : VLCtx} (hx : gIdR ∉ Δ.fvars) :
    Erases env Us gΓOpenR Δ gLamR (.lambda (nameToBinder `a) (.app gFixR (.bvar 0))) := by
  have h := Erases.instFixvars (Γ := gΓOpenR) (fv := gFvR) (ids := [gIdR]) (defs := gFixDefsR)
    (by simp) (by simp [gFixDefsR, LBClosedDefs])
    (fun x => by simp [gFixDefsR, hasFVarDefs])
    (fun nm x hnm => by
      refine ⟨0, by simp, ?_, ?_⟩ <;>
        · by_cases hf : nm = `f <;> simp_all [gFvR, gΓOpenR, gΓR])
    (fun H => H) (gErasesOpenR env Us hx) ⟨rfl, by simp [FVarsIn], trivial⟩
  rwa [gSubstFixR] at h

/-! ### The repaired `erases_fix_of_open` fires on the same fixture (slice `rec`)

The guard the theorem never had. Before the repair `hopen`'s unrestricted `∀ Δf` was
unsatisfiable here — `gErasesOpenR` needs `gIdR ∉ Δ.fvars`, and that is not optional: the
block body references its own sibling, so the derivation goes through `Erases.fixvar`,
whose `hfresh` is anti-monotone in `Δ`. Conditioned on freshness, the fixture feeds the
theorem directly, and the rebuilt `hbodies` comes out unrestricted on the far side.

One premise stays hypothetical, and it is not new: `hnest`. The earlier guards
(`gInstFixvarsR`) sidestepped it by taking the *outer* `Γ` to be `gΓOpenR` itself, where
`hnest` is `id`; that is no longer available, because the repaired theorem pins
`Γ.fixvars = ⊥` and `gΓOpenR`'s is `gFvR`. Discharging it needs a genuine `Γ`-transport
for a `.lam`-source that erases to a block, which is the `Γ`-inside-the-motives
generalisation the ledger already names as part of residue 1. Everything else here is
constructed, and the point of the guard — that a genuinely self-referential block
satisfies the repaired `hopen` and comes out the other side as `Erases.fix` — is
unaffected by it. -/

/-- **Non-vacuity for the repaired `erases_fix_of_open`**: the self-referential one-def
block `def f (a : Prop) := f a`, from the run's *open* stage all the way to the stored
`fix f. λa. f a`, through the theorem rather than around it. -/
theorem gErases_fix_of_open (env : VEnv) (henv : env.Ordered) (Us : List Name) {Δ : VLCtx}
    (hnest : ∀ {Δ' : VLCtx} {n' : Name} {ty' b' : Expr} {bi' : BinderInfo}
        {d' : List (@FixDef LBTerm)} {i' : Nat},
        Erases env Us (gΓR.withFixvars gFvR) Δ' (.lam n' ty' b' bi') (.fix d' i') →
        Erases env Us gΓR Δ' (.lam n' ty' b' bi') (.fix d' i')) :
    Erases env Us gΓR Δ gLamR gFixR := by
  have hrec : gΓR.recBodies `f = some (gFixDefsR, 0) := by simp [gΓR]
  refine erases_fix_of_open henv (Γ := gΓR) (by simp [gΓR]) (fv := gFvR) (nms := [`f])
    (ids := [gIdR]) (srcs := [gLamR]) (obodies := [gObodyR])
    Nat.zero_lt_one rfl rfl rfl rfl (by simp) rfl (fun j h => ?_) (fun d hd => ?_)
    ⟨trivial, trivial, Nat.zero_lt_one⟩ ⟨rfl, by simp [FVarsIn], trivial⟩ ?_ ?_
    (fun j h => ?_) (fun j h => ?_) (fun nm x hnm => ?_) hnest (fun j h => ?_)
    (fun j h => ?_) (fun j h Δf hfr => ?_)
  · -- hreg
    obtain rfl : j = 0 := by simp only [gFixDefsR, List.length_cons, List.length_nil] at h; omega
    exact hrec
  · -- hrarg
    simp only [gFixDefsR, List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd; rfl
  · -- LBClosed gFixR 0
    show LBClosed gFixR 0
    simp [gFixR, gFixDefsR, LBClosedDefs]
  · -- no fvars in gFixR
    intro x
    show ¬ hasFVar x gFixR
    simp [gFixR, gFixDefsR, hasFVarDefs]
  · -- hoclosed
    obtain rfl : j = 0 := by simp only [gFixDefsR, List.length_cons, List.length_nil] at h; omega
    show LBClosed gObodyR 0
    simp [gObodyR]
  · -- hclose
    obtain rfl : j = 0 := by simp only [gFixDefsR, List.length_cons, List.length_nil] at h; omega
    exact gCloseR
  · -- hlink: the block-local map names the block's own id, at index 0
    refine ⟨0, by simp, ?_, ?_⟩ <;>
      · by_cases hf : nm = `f <;> simp_all [gFvR, gΓR]
  · -- hsrcfv
    obtain rfl : j = 0 := by simp only [gFixDefsR, List.length_cons, List.length_nil] at h; omega
    exact ⟨rfl, by simp [FVarsIn], trivial⟩
  · -- hsclosed
    obtain rfl : j = 0 := by simp only [gFixDefsR, List.length_cons, List.length_nil] at h; omega
    exact ⟨trivial, trivial, Nat.zero_lt_one⟩
  · -- hopen, now at a *fresh* `Δf` — which is what makes it satisfiable at all
    obtain rfl : j = 0 := by simp only [gFixDefsR, List.length_cons, List.length_nil] at h; omega
    exact gErasesOpenR env Us (hfr gIdR (by simp))

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

/-! ## Part 5 — feeding the forward simulations (recursion wall, slice W2)

The simulations' new premise `RecEnvConsistent` (`ErasesCorrect.lean`) is this file's
`RegisteredClosureRec` **re-keyed on `Γ.recBodies`**: the registration record is indexed
by *source unfoldings* (`Esrc n = some body`, the direction a cold-start walk produces),
while the δ case of a simulation holds the `const_fix` leaf's witness
(`Γ.recBodies n = some (defs, idx)`) and must go the other way.

One fact bridges them and `RegisteredClosureRec` does not contain it: that `Γ`'s
registration for `n` names *the same* block `E` stores under `Γ.constants n`. That is a
statement about the run (`visitMutual` conses the decl and records the block in the same
breath), so it is taken here as the explicit `hkey` premise, in the shape the cold-start
walk will discharge. Given it, the block identity follows by injectivity of the stored
decl and the adapter is mechanical. -/

/-- **`RecEnvConsistent` from the recursive registration record.** `hkey` is the
`Γ.recBodies`-to-`Esrc`/`E` agreement the run establishes at `Erasure.visitMutual`'s
registration line; everything else comes from `RegisteredClosureRec`. -/
theorem recEnvConsistent_of_registeredClosureRec {env : VEnv} {Us : List Name}
    {Γ : ErasureCtx} {Esrc : SEnv} {E : GlobalDeclarations}
    (h : RegisteredClosureRec env Us Γ Esrc E)
    (hkey : ∀ {n : Name} {defs : List (@FixDef LBTerm)} {idx : Nat},
      Γ.recBodies n = some (defs, idx) →
        ∃ body, Esrc n = some body ∧
          LBTerm.envLookup E (Γ.constants n)
            = some (.constantDecl ⟨some (.fix defs idx)⟩)) :
    RecEnvConsistent env Us Γ Esrc E where
  reg := by
    intro n defs idx hreg
    obtain ⟨body, hunf, hlook⟩ := hkey hreg
    obtain ⟨defs', idx', hlook', her⟩ := h.erase hunf
    obtain ⟨rfl, rfl⟩ : defs' = defs ∧ idx' = idx := by
      rw [hlook] at hlook'
      have := (by simpa using hlook' : defs = defs' ∧ idx = idx')
      exact ⟨this.1.symm, this.2.symm⟩
    exact ⟨hlook, (h.disj hunf).1, (h.disj hunf).2, body, hunf, her⟩

/-! ### The W2 acceptance test: a `.fix`-headed application that really runs

The wall is only *witnessed* if the data simulation fires on a program whose target head
is a genuine `.fix` node and whose target step is therefore
`WcbvEval.fix_guarded` — the rule the whole slice exists to reach. Part 3's fixture
(`def f (a : Prop) := f a`) cannot serve: it diverges, so it has no `SEvalDataC`
derivation to feed the simulation. What is needed is a recursive *registration* over a
terminating program, and the shipping eraser produces exactly that whenever a **mutual
block has more than one name** — `visitMutual` takes the fix path on `single_decl` alone,
without checking self-reference (`Erasure.lean`'s `nonrecursive` conjunct), so a block
member that happens not to call itself is still stored as a `.fix` decl.

So: `f := fun (h : Prop → Prop) => h`, stored as the one-def block `fix f. λh. h`, applied
to `fun (a : Prop) => a`. The source is the already-typed redex `gCxApp` of Part 3b (the
counterexample's own term, reused: the *target* differs, and that is the point — Part 3b's
block was the contentless `fix f. f`, this one's body is the head's real erasure). The
target run is

    (fix f. λh. h) (λa. a)  --fix_guarded-->  (λh. h) (λa. a)  --beta-->  λa. a

with the source `SEvalDataC`-evaluating to `fun (a : Prop) => a`, which erases to the same
`λa. a`. Every premise of `erases_correct_data` is *constructed*, including
`RecEnvConsistent` at a `Γ` that genuinely registers recursion. -/

/-- The W2 guard's block: `fix f. λh. h` — a one-def block whose body is the head's real
erasure, not a self-loop. -/
private def gRecDefs : List (@FixDef LBTerm) :=
  [{ name := .named "f", body := .lambda (nameToBinder `h) (.bvar 0) }]

/-- Its stored decl body. -/
private def gRecFix : LBTerm := .fix gRecDefs 0

/-- A `Γ` that genuinely registers recursion: every name is bound to the block above
(as in Part 3's fixture, the maps are total so no case analysis is needed). -/
private def gRecΓ : ErasureCtx where
  inductives := fun _ => none
  constants := fun _ => rootKername "f"
  ctors := fun _ => none
  ctorArities := fun _ => none
  casesOns := fun _ => none
  recBodies := fun _ => some (gRecDefs, 0)

/-- The source environment: the constant unfolds to the head lambda. -/
private def gRecEsrc : SEnv := fun _ => some gCxHId

/-- The target environment: the kername is bound to the block. -/
private def gRecE : GlobalDeclarations :=
  [(rootKername "f", .constantDecl ⟨some gRecFix⟩)]

/-- The head erases to the block, at any context — through the Part 2 reconciliation, so
the guard exercises `erases_fix_of_closed` too. The `mkDef` closing is trivial here (the
body mentions no sibling), which is exactly what makes the program terminate. -/
private theorem gRecErasesHead {Δ : VLCtx} :
    Erases .empty [] gRecΓ Δ gCxHId gRecFix := by
  have hsort : ∀ {Γ : List VExpr},
      VEnv.HasType .empty 0 Γ (.sort .zero) (.sort (.succ .zero)) :=
    .sortDF trivial trivial rfl
  refine erases_fix_of_closed (nms := [`f]) (ids := [⟨`x⟩]) (srcs := [gCxHId])
    (obodies := [.lambda (nameToBinder `h) (.bvar 0)])
    Nat.zero_lt_one rfl rfl rfl rfl rfl (fun j h => ?_) (fun d hd => ?_)
    gCxHId_closed gCxHId_fvarFree ⟨Nat.zero_lt_two, trivial⟩ ?_
    (fun j h => ?_) (fun j h => ?_) (fun j h Δf => ?_)
  · obtain rfl : j = 0 := by simp only [gRecDefs, List.length_cons, List.length_nil] at h; omega
    rfl
  · simp only [gRecDefs, List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd; rfl
  · intro x; simp [gRecDefs, hasFVarDefs]
  · obtain rfl : j = 0 := by simp only [gRecDefs, List.length_cons, List.length_nil] at h; omega
    exact Nat.zero_lt_one
  · obtain rfl : j = 0 := by simp only [gRecDefs, List.length_cons, List.length_nil] at h; omega
    simp [gRecDefs, closeFix, closeFixFold, toBvar]
  · obtain rfl : j = 0 := by simp only [gRecDefs, List.length_cons, List.length_nil] at h; omega
    show Erases .empty [] gRecΓ Δf gCxHId (.lambda (nameToBinder `h) (.bvar 0))
    exact .lam (.forallE ⟨_, hsort⟩ ⟨_, hsort⟩ (.sort rfl) (.sort rfl)) (.bvar 0)

/-- The whole redex erases to `(fix f. λh. h) (λa. a)` — applied form. -/
private theorem gRecErases :
    Erases .empty [] gRecΓ [] gCxApp (.app gRecFix gCxId') :=
  .app gRecErasesHead (.lam (.sort rfl) (.bvar 0))

private theorem gRecNoBlock : NoBlock (.app gRecFix gCxId') := by
  refine ⟨?_, ?_⟩ <;> simp [gRecFix, gRecDefs, gCxId']

/-- `SEnvConsistent` holds **vacuously** at the empty `VEnv`: it fires only on a
`TrExprS` of a `.const`, and `.empty` declares nothing. So a genuinely non-`none` `Esrc`
costs the guard nothing. -/
private theorem gRecSEnvConsistent : SEnvConsistent .empty [] gRecEsrc := by
  intro Δ n us body cve _ htr
  cases htr with
  | const h1 _ _ => simp [VEnv.empty] at h1

private theorem gRecErasesEnvDeltaData :
    ErasesEnvDeltaData .empty [] gRecΓ gRecEsrc gRecE := by
  intro Δ n body hunf
  obtain rfl : body = gCxHId := by simpa [gRecEsrc] using hunf.symm
  exact ⟨rfl, rfl, gRecFix, rfl, gRecErasesHead, by simp [gRecFix, gRecDefs]⟩

private theorem gRecRecEnvConsistent :
    RecEnvConsistent .empty [] gRecΓ gRecEsrc gRecE where
  reg := by
    intro n defs idx hreg
    obtain ⟨rfl, rfl⟩ : defs = gRecDefs ∧ idx = 0 := by
      have h2 := (by simpa [gRecΓ] using hreg : gRecDefs = defs ∧ 0 = idx)
      exact ⟨h2.1.symm, h2.2.symm⟩
    exact ⟨rfl, rfl, rfl, gCxHId, rfl, fun {_} => gRecErasesHead⟩

/-- **The recursion wall fires end-to-end at the term level.** `erases_correct_data`,
with `NoFixEnv` gone and `RecEnvConsistent` in its place, delivers a target evaluation of
a `.fix`-headed application — so the new `fix_guarded` branch of the β case is on a real
execution path, not merely reachable in principle. Every premise is constructed. -/
theorem erases_correct_data_recursive_fires :
    ∃ t' vve, WcbvEval gRecE appliedFlags (.app gRecFix gCxId') t' ∧
      TrExprS .empty [] [] gCxId vve ∧
      Erases .empty [] gRecΓ [] gCxId t' ∧ NoBlock t' :=
  erases_correct_data (env := .empty) ⟨[], .empty⟩ (Us := []) (Δ := []) trivial
    gRecSEnvConsistent gRecErasesEnvDeltaData (fun h => by simp [gRecΓ] at h)
    (fun h => by simp [gRecΓ] at h) gRecRecEnvConsistent rfl
    gCxSEval gCxTrExprS gRecErases gRecNoBlock

/-- …and the value it produces is exactly the erasure of the source value: the run is
`(fix f. λh. h) (λa. a) ⇓ λa. a`, one `fix_guarded` and one `beta`. -/
theorem erases_correct_data_recursive_value :
    WcbvEval gRecE appliedFlags (.app gRecFix gCxId') gCxId' :=
  .fix_guarded (argsv := []) rfl (.fix_atom _ _) (.lam _ _) rfl rfl
    (.beta (.lam _ _) (.lam _ _) (.lam _ _))

end LeanToLambdaBox
