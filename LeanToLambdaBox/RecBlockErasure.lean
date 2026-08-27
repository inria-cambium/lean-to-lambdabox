import LeanToLambdaBox.FixUnfold
import LeanToLambdaBox.ErasesStrengthen
import LeanToLambdaBox.ErasureRun

/-!
# The recursive block, from open bodies to `Erases.fix`

Everything the bridge needs in order to *walk* `visitMutual`'s recursive exit, collected
below `VisitExprRefines.lean` so that the induction's step 6 can call it.

## Why this module exists

The results here were written where they were first needed and ended up in the wrong half
of the import graph. `Erases.instFixvars` and `erases_fix_of_open{,_nil}` were in
`EnvErasureRec.lean`; `blockReader`, the block-map inversions, `closeFix_eq_block_fold` and
`erases_rec_block_of_run` were in `ColdStartDelta.lean`. Both files sit **downstream** of
`VisitExprRefines.lean` —

    VisitExprRefines → EnvErasureNonrec → EnvErasureRec → ColdStartDelta

— so step 6 could never call them, however Γ-polymorphic they are. Slice Γ-W0 recorded that
obstruction when it placed `run_rec_exit_siblings_chained` in `ErasureRun.lean` rather than
in `ColdStartDelta.lean` for the same reason; slice Γ-W2 removes it for the rest.

**They were misplaced, not entangled.** The whole proof cone of `erases_fix_of_open_nil` —
`substFix_mkLambdas`, `Erases.instFixvars`, `hasFVar_mkLambdas`, `erases_target_fvars`,
`erases_fix_of_closed` — references nothing from `EnvErasureNonrec` or from any `Cold*`
module. It lives on `FixUnfold`, `ErasesStrengthen`, `Closed`, `Abstract`, `Erases`,
`FixMetatheory` and `ErasureContext`, every one of which `VisitExprRefines.lean` already
imported. `EnvErasureRec` was downstream only because its *Part 3* needs
`EnvErasureNonrec.RegisteredClosure`. Likewise `blockMap_getElem?_inv` is pure `Std`/`List`
and `closeFix_eq_block_fold` needs only `FixMetatheory` plus `Basic.toBvar`. So this module
adds **no** module to `VisitExprRefines`' import closure: it re-slices existing ones.

The move is verbatim — every name, statement and proof is unchanged, and no consumer was
edited. `EnvErasureRec` and `ColdStartDelta` re-acquire these names transitively, through
`EnvErasureNonrec → VisitExprRefines`.

## What did *not* move, and why

`recEnvConsistent_of_block` (`ColdStartDelta.lean`) stays where it is. It looked like a
step-6 input and is not: step 6's motive-6 conclusion is a `RunConclδ`, whose recursive
extension step is `DeltaHyps.RunConclδ.recBlock` — already upstream — fed by
`erases_rec_block_of_run`'s conclusion. `RecEnvConsistent` is a *capstone*-level record, and
keeping it downstream keeps `KeysDistinct` and the `ColdStartShape` env-lookup kit
downstream with it, which is where the remaining risk of this move would have lived.

`run_rec_exit_siblings_close` stays too: it is stated over `ColdStartRun`'s decomposition,
which is genuinely downstream of the bridge.
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
  | proj S i iid np nf hs hnfs hi _ ihd =>
      intro hsc
      simp only [substFix, substFVarList_proj]
      exact .proj S i iid np nf hs hnfs hi (ihd hsc)
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

/-! ### Where the target's free variables come from

`Erases.instFixvars` reads the fixvar leaf *forwards* — a block-local `.fvar` becomes the
block. The companion below reads it *backwards*, and is the only fact about `Erases` that
counts fvars: a derivation whose **source** is fvar-free has a **target** whose free
variables are all fixvars of `Γ`.

Fourteen of the fifteen rules make this trivial. Twelve are structural or have fvar-free
targets outright; `const_fix` and `fix` carry the inertness equality
`htobv : ∀ x l, toBvar x l (.fix defs idx) = .fix defs idx`, which
`not_hasFVar_of_toBvar_eq_self` (`FixUnfold`) converts into outright fvar-freeness of the
block they emit. The fifteenth, `Erases.fvar`, is the one rule that would manufacture a
target fvar out of nothing — and it is exactly the rule the source-side hypothesis kills,
since `FVarsIn (fun _ => False) (.fvar y)` *is* `False`.

Together with `not_hasFVar_closeFix` this is what makes the stored `.fix` node's
fvar-freeness a theorem rather than a premise: the block's opened bodies erase sources that
are closed, fvar-free `_unsafe_rec` bodies, so their targets mention only the run's own
fixvars — and `mkDef` abstracts precisely those. -/

/-- Re-wrapping an alternative as a lambda chain neither adds nor removes free variables
(`mkLambdas` only conses `.lambda` nodes, and `hasFVar` is transparent through them). The
`cases` arm below needs it because `Erases.cases`' induction hypothesis speaks about
`mkLambdas (alts'[j]).1 (alts'[j]).2` while `hasFVarAlts` speaks about `(alts'[j]).2`. -/
private theorem hasFVar_mkLambdas (x : FVarId) (ns : List BinderName) (b : LBTerm) :
    hasFVar x (mkLambdas ns b) ↔ hasFVar x b := by
  induction ns with
  | nil => exact Iff.rfl
  | cons n ns ih => rw [mkLambdas, hasFVar_lambda, ih]

/-- **An fvar-free source erases to a target whose free variables are fixvars.** Every
`.fvar` node the erasure puts in the target comes from the `Erases.fixvar` leaf, i.e. is
one of the fixvars `Γ` currently installs; at a top-level `Γ` (where `fixvars = fun _ =>
none`) the conclusion degenerates to outright fvar-freeness of the target. -/
theorem erases_target_fvars {env : VEnv} {Us : List Name} {Γ : ErasureCtx} :
    ∀ {Δ : VLCtx} {e : Expr} {t : LBTerm}, Erases env Us Γ Δ e t →
      FVarsIn (fun _ => False) e →
      ∀ {x : FVarId}, hasFVar x t → ∃ nm, Γ.fixvars nm = some x := by
  intro Δ e t h
  induction h with
  | box htr her => intro _ x hx; simp at hx
  | lit hcl _ ih => intro _ x hx; exact ih FVarsIn.toConstructor hx
  | proj S i iid np nf hs hnfs hi _ ihd =>
      intro hsc x hx; simp only [hasFVar_proj] at hx; exact ihd hsc hx
  | bvar i => intro _ x hx; simp at hx
  | fvar y =>
      -- the one rule that could invent a target fvar; its source is `.fvar y`, whose
      -- `FVarsIn (fun _ => False)` premise is `False` on the nose.
      intro hsc
      exact False.elim hsc
  | const n us kn hkn hctor hcases => intro _ x hx; simp at hx
  | app _ _ ihf iha =>
      intro hsc x hx
      simp only [hasFVar_app] at hx
      rcases hx with hx | hx
      · exact ihf hsc.1 hx
      · exact iha hsc.2 hx
  | lam hty _ ihb => intro hsc x hx; exact ihb hsc.2 hx
  | letE hty hval _ _ ihv ihb =>
      intro hsc x hx
      simp only [hasFVar_letIn] at hx
      rcases hx with hx | hx
      · exact ihv hsc.2.1 hx
      · exact ihb hsc.2.2 hx
  | ctor_head cn us iid cidx hc => intro _ x hx; simp [hasFVarArgs] at hx
  | @ctor _ cn us iid cidx args args' hc hlen _ ihargs =>
      intro hsc x hx
      obtain ⟨-, hall⟩ := fvarsIn_foldl_app hsc
      simp only [hasFVar_construct, hasFVarArgs_iff] at hx
      obtain ⟨u, hu, hxu⟩ := hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
      have hi' : i < args.length := by omega
      exact ihargs i hi' (hall _ (List.getElem_mem hi')) hxu
  | @cases _ con us iid numParams pre discr discr' minors alts' nfs hc hpre hnfs _
      hlen hnlen harity _ ihd ihalts =>
      intro hsc x hx
      obtain ⟨-, hall⟩ := fvarsIn_foldl_app hsc
      simp only [hasFVar_case, hasFVarAlts_iff] at hx
      rcases hx with hx | ⟨a, ha, hxa⟩
      · exact ihd (hall _ (List.mem_cons_self ..)) hx
      · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
        have hj' : j < minors.length := by omega
        refine ihalts j hj' (hall _ (List.mem_cons_of_mem _ (List.getElem_mem hj'))) ?_
        rw [hasFVar_mkLambdas]
        exact hxa
  | fixvar nm us y hfx hctor hcases hfresh =>
      -- the leaf the statement exists for: the target *is* `.fvar y`, and `Γ` names it.
      intro _ x hx
      simp only [hasFVar_fvar] at hx
      exact ⟨nm, hx ▸ hfx⟩
  | const_fix nm us hrec hctor hcases hshift hsubst htobv =>
      intro _ x hx
      exact absurd hx (not_hasFVar_of_toBvar_eq_self x _ 0 (htobv x 0))
  | @fix Δc idx nm' tty tb tbi nms srcs d' hidx hnlen' hslen' hsrc hreg hrarg
      hlift hinst habsl hshift hsubst htobv hbodies _ihb =>
      intro _ x hx
      exact absurd hx (not_hasFVar_of_toBvar_eq_self x _ 0 (htobv x 0))

/-! ### …and where the target's loose de-Bruijn indices come from

The closedness companion of `erases_target_fvars`, and the fact step 6 of the bridge
cannot get anywhere else. `erases_rec_block_of_run` needs each opened block body to be
de-Bruijn closed (`hoclosed`), and for a *run* of the shipping `visitExpr` that is
`ColdStartInduction.visitExpr_noFix_closed` — but inside `visitExpr_refines_erases_core`
the eraser is the induction's **abstract** fixpoint argument, about which only the motives
may be assumed, and no motive carries an output shape. So the fact has to come from the
one thing the motive does hand back: the `Erases` derivation itself.

It does. Erasure moves de-Bruijn indices around but never invents one: `Erases.bvar` is
the only rule with a loose-index target and it copies the source's index, every binder
rule extends `Δ` by a bvar entry exactly where its target extends its own scope, and the
two fix leaves carry their block's inertness (`hshift`), which `lbClosed_of_shift_eq`
reads back as closedness. (Recursion wall, slice Γ-W3.) -/

/-- `closed_foldl_app` (`ErasesAbstract`), replicated here rather than imported: slice
Γ-W2c's move added **zero** modules to the bridge's import closure, and one twelve-line
spine inversion is not worth spending that. -/
private theorem closed_foldl_app' {k : Nat} {args : List Expr} {f : Expr}
    (h : Closed (args.foldl Expr.app f) k) : Closed f k ∧ ∀ a ∈ args, Closed a k := by
  induction args generalizing f with
  | nil => exact ⟨h, by simp⟩
  | cons a as ih =>
    obtain ⟨hfa, hrest⟩ := ih (f := f.app a) h
    refine ⟨hfa.1, fun b hb => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hfa.2
    · exact hrest _ hb

/-- **A de-Bruijn-closed source erases to a de-Bruijn-closed target**, at the erasure
context's own bvar depth. At `Δ = []` — where the block's sibling bodies are erased once
`erases_strengthen_closed` has brought them down — this is outright `LBClosed t 0`. -/
theorem erases_target_lbClosed {env : VEnv} {Us : List Name} {Γ : ErasureCtx} :
    ∀ {Δ : VLCtx} {e : Expr} {t : LBTerm}, Erases env Us Γ Δ e t →
      Closed e Δ.bvars → LBClosed t Δ.bvars := by
  intro Δ e t h
  induction h with
  | box htr her => intro _; trivial
  | lit hcl _ ih => intro _; exact ih Closed.toConstructor
  | proj S i iid np nf hs hnfs hi _ ihd =>
      intro hc; rw [LBClosed_proj]; exact ihd hc
  | bvar i => intro hc; exact hc
  | fvar y => intro _; trivial
  | const n us kn hkn hctor hcases => intro _; trivial
  | app _ _ ihf iha => intro hc; exact ⟨ihf hc.1, iha hc.2⟩
  | lam hty _ ihb => intro hc; exact ihb hc.2
  | letE hty hval _ _ ihv ihb => intro hc; exact ⟨ihv hc.2.1, ihb hc.2.2⟩
  | ctor_head cn us iid cidx hc => intro _; trivial
  | @ctor _ cn us iid cidx args args' hc hlen _ ihargs =>
      intro hcl
      obtain ⟨-, hall⟩ := closed_foldl_app' hcl
      rw [LBClosed_construct, LBClosedArgs_iff]
      intro u hu
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
      have hi' : i < args.length := by omega
      exact ihargs i hi' (hall _ (List.getElem_mem hi'))
  | @cases _ con us iid numParams pre discr discr' minors alts' nfs hc hpre hnfs _
      hlen hnlen harity _ ihd ihalts =>
      intro hcl
      obtain ⟨-, hall⟩ := closed_foldl_app' hcl
      rw [LBClosed_case, LBClosedAlts_iff]
      refine ⟨ihd (hall _ (List.mem_cons_self ..)), fun a ha => ?_⟩
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
      have hj' : j < minors.length := by omega
      exact LBClosed.mkLambdas_inv
        (ihalts j hj' (hall _ (List.mem_cons_of_mem _ (List.getElem_mem hj'))))
  | fixvar nm us y hfx hctor hcases hfresh => intro _; trivial
  | const_fix nm us hrec hctor hcases hshift hsubst htobv =>
      intro _; exact lbClosed_of_shift_eq _ _ (hshift 1 _)
  | @fix Δc idx nm' tty tb tbi nms srcs d' hidx hnlen' hslen' hsrc hreg hrarg
      hlift hinst habsl hshift hsubst htobv hbodies _ihb =>
      intro _; exact lbClosed_of_shift_eq _ _ (hshift 1 _)

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
`Γ.withFixvars fv`. Slice δ-D8 consumed them with no motive change
(`VisitExprRefines.visitExpr_refines_erases_block`) — true of *that* route, from outside
the induction. Reaching it from **inside** step 6 did need the motives to quantify `Γ`
(slice Γ-W1), and since Γ-W3.6b step 6 walks the recursive exit itself: the capstone half
is no longer wanting, and what `ColdStart.lean`'s residue 1 now prices is
`RecBlockAgreement`'s outright discharge.
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

/-! ## Part 3 — the block's own reader, and its two lookups (from `ColdStartDelta.lean`) -/

/-- **The reader `visitMutual` installs while erasing a mutual block** — its
`withReader (fun env => { env with fixvars := fixvarnames.zip ids |> ofList |> some })`,
named so the block's two lookups (`mkDef`'s closing fold and the bridge's fixvar
agreement) can be stated about the same object. -/
def blockReader (fixnames : List Name) (ids : List FVarId) (ctx : ErasureContext) :
    ErasureContext :=
  { ctx with fixvars := some (Std.HashMap.ofList (fixnames.zip ids)) }

@[simp] theorem blockReader_fixvars (fixnames : List Name) (ids : List FVarId)
    (ctx : ErasureContext) :
    (blockReader fixnames ids ctx).fixvars
      = some (Std.HashMap.ofList (fixnames.zip ids)) := rfl
@[simp] theorem blockReader_lctx (fixnames : List Name) (ids : List FVarId)
    (ctx : ErasureContext) : (blockReader fixnames ids ctx).lctx = ctx.lctx := rfl
@[simp] theorem blockReader_lparams (fixnames : List Name) (ids : List FVarId)
    (ctx : ErasureContext) : (blockReader fixnames ids ctx).lparams = ctx.lparams := rfl
@[simp] theorem blockReader_config (fixnames : List Name) (ids : List FVarId)
    (ctx : ErasureContext) : (blockReader fixnames ids ctx).config = ctx.config := rfl

/-- Distinct block names give a `HashMap.ofList`-admissible association list. -/
theorem zip_pairwise_fst : ∀ {nms : List Name} {ids : List FVarId}, nms.Nodup →
    (nms.zip ids).Pairwise (fun a b => (a.1 == b.1) = false)
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | a :: l, b :: m, hnd => by
      rw [List.zip_cons_cons]
      refine List.Pairwise.cons ?_ (zip_pairwise_fst (List.nodup_cons.mp hnd).2)
      intro p hp
      have hmem : p.1 ∈ l := (List.of_mem_zip (a := p.1) (b := p.2) (by simpa using hp)).1
      have : a ≠ p.1 := fun h => (List.nodup_cons.mp hnd).1 (h ▸ hmem)
      simpa using this

/-- **The block map at a sibling's own name** — the lookup `mkDef`'s fold performs. -/
theorem blockMap_getElem! {nms : List Name} {ids : List FVarId}
    (hnd : nms.Nodup) (hlen : nms.length = ids.length)
    {k : Nat} (hk : k < nms.length) :
    (Std.HashMap.ofList (nms.zip ids))[nms[k]]! = ids[k]'(hlen ▸ hk) := by
  refine Std.HashMap.getElem!_ofList_of_mem (k := nms[k]) (by simp) (zip_pairwise_fst hnd) ?_
  have hz : (nms.zip ids)[k]'(by simp [← hlen]; omega) = (nms[k], ids[k]'(hlen ▸ hk)) := by
    simp
  exact hz ▸ List.getElem_mem _

/-- **…and the inverse**: a hit in the block map really is one of the block's own ids, at
the matching index. This is what supplies `erases_rec_block_of_run`'s `hfv` when `fv` is
read off the reader the run installed. -/
theorem blockMap_getElem?_inv {nms : List Name} {ids : List FVarId}
    (hnd : nms.Nodup) (hlen : nms.length = ids.length) {nm : Name} {x : FVarId}
    (h : (Std.HashMap.ofList (nms.zip ids))[nm]? = some x) :
    ∃ k, ∃ hk : k < nms.length, nms[k] = nm ∧ (ids[k]'(hlen ▸ hk)) = x := by
  by_cases hmem : nm ∈ nms
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hmem
    refine ⟨k, hk, rfl, ?_⟩
    have hz : (nms.zip ids)[k]'(by simp [← hlen]; omega) = (nms[k], ids[k]'(hlen ▸ hk)) := by
      simp
    have hget : (Std.HashMap.ofList (nms.zip ids))[nms[k]]? = some (ids[k]'(hlen ▸ hk)) :=
      Std.HashMap.getElem?_ofList_of_mem (by simp) (zip_pairwise_fst hnd)
        (hz ▸ List.getElem_mem _)
    rw [hget] at h
    exact Option.some.inj h
  · exfalso
    rw [Std.HashMap.getElem?_ofList_of_contains_eq_false ?_] at h
    · simp at h
    · rw [List.map_fst_zip (by omega)]
      simpa using hmem

/-- **`mkDef`'s binder fold *is* `closeFix ids 0`.** The shipping loop abstracts the
block's fvars by looking each sibling's name up in the reader's map; `closeFix` abstracts
the `ids` directly. `FixMetatheory` has always said the two agree "modulo the `fixvars`
lookup" — this is that modulo, discharged, and it needs exactly the block names' being
distinct. -/
theorem closeFix_eq_block_fold {nms : List Name} {ids : List FVarId}
    (hnd : nms.Nodup) (hlen : nms.length = ids.length) (t : LBTerm) :
    nms.reverse.zipIdx.foldl
        (fun b p => toBvar ((Std.HashMap.ofList (nms.zip ids))[p.1]!) p.2 b) t
      = closeFix ids 0 t := by
  have hids : ids.reverse
      = nms.reverse.map (fun nm => (Std.HashMap.ofList (nms.zip ids))[nm]!) := by
    rw [List.map_reverse]
    congr 1
    refine List.ext_getElem (by simp [hlen]) (fun k h1 h2 => ?_)
    rw [List.getElem_map]
    exact (blockMap_getElem! hnd hlen (by simpa [hlen] using h1)).symm
  rw [closeFix, closeFixFold_eq_foldl, hids, List.zipIdx_map, List.foldl_map]
  rfl

/-! ## Part 4 — the composition a run can feed (from `ColdStartDelta.lean`) -/

/-- **From the block's open erasures to `Erases.fix`.** The `hopen` slot is exactly what
`visitExpr_refines_erases_block` produces for one sibling; everything else is the run's
own output shape (`ColdStartRun.run_rec_exit_siblings{,_closed}`) or the `Γ`-side
agreement. The conclusion is context-uniform, which is what the environment-level records
need.

Fvar-freeness of the stored block is **derived** here rather than assumed: it is not an
independent fact about `defs` but a consequence of the block-local erasures plus the
closing — `erases_target_fvars` says every free variable of an opened body is a fixvar of
`Γ.withFixvars fv`, `hfv` identifies those with the run's own `ids`, and
`not_hasFVar_closeFix` observes that `closeFix ids 0` abstracts precisely the `ids`.

**The scope restriction the recursion feature makes is this theorem's `hopen`.** The
block's inner runs are taken at `known = ⊥`, so a sibling body's erasure is derivable only
while it stays inside the block: **a block's bodies call only its own siblings** (reached
through `Γ.withFixvars fv` rather than through the fragment), **registered constructors and
registered `casesOn`s** — an external constant is out of scope. That is the one restriction
recursion genuinely still costs, and it is *inside* a block rather than about the program;
`DeltaHyps`' scope-restriction list and `ColdStart`'s `Hβ` row both name this theorem for
it. -/
theorem erases_rec_block_of_run {env : VEnv} (henv : env.Ordered) {Us : List Name}
    {Γ : ErasureCtx} (hnfv : Γ.fixvars = fun _ => none)
    {fv : Name → Option FVarId}
    {fixnames : List Name} {ids : List FVarId} {srcs : List Expr} {obodies : List LBTerm}
    {defs : List (@FixDef LBTerm)}
    (hnlen : fixnames.length = defs.length)
    (hilen : ids.length = defs.length)
    (hslen : srcs.length = defs.length)
    (hblen : obodies.length = defs.length)
    (hnd : ids.Nodup)
    -- the one irreducible `Γ`↔run agreement, in two halves: the registration and the map
    (hreg : ∀ j (h : j < defs.length),
        Γ.recBodies (fixnames[j]'(hnlen ▸ h)) = some (defs, j))
    (hfv : ∀ (nm : Name) (x : FVarId), fv nm = some x →
        ∃ j, ∃ h : j < defs.length,
          (fixnames[j]'(hnlen ▸ h)) = nm ∧ (ids[j]'(hilen ▸ h)) = x)
    -- the block, as the run built it
    (hrarg : ∀ d ∈ defs, d.principalArgIdx = 0)
    (hfclosed : ∀ j : Nat, LBClosed (.fix defs j) 0)
    (hoclosed : ∀ j (h : j < defs.length), LBClosed (obodies[j]'(hblen ▸ h)) 0)
    (hclose : ∀ j (h : j < defs.length),
        (defs[j]'h).body = closeFix ids 0 (obodies[j]'(hblen ▸ h)))
    -- the block's sources: closed, fvar-free λ-telescopes, as a top-level def body is
    (hsrc : ∀ j (h : j < defs.length),
        ∃ n ty b bi, (srcs[j]'(hslen ▸ h)) = .lam n ty b bi)
    (hsclosed : ∀ j (h : j < defs.length), Closed (srcs[j]'(hslen ▸ h)) 0)
    (hsrcfv : ∀ j (h : j < defs.length),
        FVarsIn (fun _ => False) (srcs[j]'(hslen ▸ h)))
    -- the block-local erasures — the Γ'-instantiated bridge's output, one per sibling
    (hopen : ∀ j (h : j < defs.length),
        Erases env Us (Γ.withFixvars fv) [] (srcs[j]'(hslen ▸ h))
          (obodies[j]'(hblen ▸ h)))
    (hnest : ∀ {Δ' : VLCtx} {n' : Name} {ty' b' : Expr} {bi' : BinderInfo}
        {d' : List (@FixDef LBTerm)} {i' : Nat},
        Erases env Us (Γ.withFixvars fv) Δ' (.lam n' ty' b' bi') (.fix d' i') →
        Erases env Us Γ Δ' (.lam n' ty' b' bi') (.fix d' i')) :
    ∀ j (h : j < defs.length) (Δ : VLCtx),
      Erases env Us Γ Δ (srcs[j]'(hslen ▸ h)) (.fix defs j) := by
  intro j h Δ
  -- Fvar-freeness of the stored block, derived. Each def body is `closeFix ids 0` of the
  -- matching opened body (`hclose`); every free variable of that opened body is a fixvar
  -- of the block-local `Γ` (`erases_target_fvars` applied to `hopen`), hence one of the
  -- run's `ids` (`hfv`); and `closeFix ids 0` abstracts exactly those.
  have hffv : ∀ (x : FVarId) (k : Nat), ¬ hasFVar x (.fix defs k) := by
    intro x k hx
    rw [hasFVar_fix, hasFVarDefs_iff] at hx
    obtain ⟨d, hd, hxd⟩ := hx
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hd
    rw [hclose m hm] at hxd
    refine not_hasFVar_closeFix (fun z hz => ?_) 0 x hxd
    obtain ⟨nm, hnm⟩ := erases_target_fvars (hopen m hm) (hsrcfv m hm) hz
    rw [ErasureCtx.withFixvars_fixvars] at hnm
    obtain ⟨i, hi, -, rfl⟩ := hfv nm z hnm
    exact List.getElem_mem _
  obtain ⟨n, ty, b, bi, hsj⟩ := hsrc j h
  rw [hsj]
  refine erases_fix_of_open_nil henv hnfv (nms := fixnames) (ids := ids) (srcs := srcs)
    (obodies := obodies) h hnlen hslen hblen hilen hnd (hsj ▸ rfl) hreg hrarg
    (hsj ▸ hsclosed j h) (hsj ▸ hsrcfv j h) (hfclosed j) (fun x => hffv x j)
    hoclosed hclose ?_ hnest hsrcfv hsclosed hopen
  -- `hlink`: the block map names the block's own ids, and `Γ` records the block at the
  -- matching index. This is where the two halves of the agreement meet.
  intro nm x hx
  obtain ⟨k, hk, hnm, hid⟩ := hfv nm x hx
  exact ⟨k, hilen ▸ hk, hid, hnm ▸ hreg k hk⟩

end LeanToLambdaBox
