import LeanToLambdaBox.EnvErasureRec
import LeanToLambdaBox.FirstOrderShipping

/-!
# Env-consistency from registration: the D3 capstone with registration-sourced env
premises (P3-v2b composition)

This file composes the env-consistency **discharges** (`EnvErasureNonrec` for the
non-recursive/inductive fragment, `EnvErasureRec` for the recursive `.fix` fragment) with
the D3 shipping capstone `shipping_erase_correct_firstorder` (`FirstOrderShipping.lean`),
so the capstone's environment-consistency hypotheses (`ErasesEnvDeltaData`,
`ErasesEnvCtor`) become **derived from registration records** rather than assumed —
exactly P3's stated goal (`notes/P3_ENV_ERASURE_DESIGN.md` §5): "discharge the
environment-consistency hypotheses as theorems about the constructed global declarations
rather than as premises."

## What is proven here

`shipping_erase_correct_firstorder_registered`: the first-order shipping correctness
theorem with `hdelta`/`hctorenv` replaced by the clean `Prop` registration hypotheses
`RegisteredClosureData` / `RegisteredCtors`. The env-consistency is discharged internally
via `erasesEnvDeltaData_of_registeredClosureData` / `erasesEnvCtor_of_registeredCtors`.

The recursive fragment's env-consistency is *also* fully discharged at the env level
(`EnvErasureRec.erasesEnvDelta_of_registeredClosureRec`, via the `erases_fix_of_closed`
reconciliation), and `registeredClosure_of_registeredClosureRec` shows a recursive
constant slots into the same general `RegisteredClosure` machinery. So a cold-start
`RegisteredClosure` produced by a DAG walk may mix plain and `.fix` bodies, and its
`ErasesEnvDelta` follows uniformly.

## The honest trust bundle (proven vs. assumed)

This is **not yet** the fully cold-start `Erasure.erase e config` theorem. The precise
remaining gap:

* **DAG cold-start registration (P3.13, deferred).** The registration hypotheses
  (`RegisteredClosureData`/`RegisteredCtors`/…) are here *assumed* about the run's output
  env `E`; `ColdStartShape`/`ColdStartInduction` (slice S1) prove the *shape* half of them
  from a real run, and slice S2 widened the bridge's conclusion from `s' = s` to
  `Erasure.RunConcl` so the two can be composed at a growing state. What is still open is
  the `get_constant_kername` **miss** branch: `VisitExprRefines.BridgeInv.consts` is now
  soundness-flavoured, but its `known_dom` residue still forces the hit branch, because
  discharging the miss branch needs facts about `Compiler.LCNF.getDeclInfo?` that belong
  to the entry slice's `RegBridgeHyps` (see the note at motive 5). That branch is also
  what would supply the top-level term bridge (`hrun`/`hinv`), which is why the subject
  here is still `visitExpr e` under a registered state, not cold-start `erase`.
* **`visitConst`-fixvar bridge (P3.12, DONE at the term level — recursion wall, W3.1).**
  `visitConst`'s fixvar branch is no longer dead: `BridgeInv.fixvars` is an agreement
  between the reader's block-local map and `Γ.fixvars`, and motive 4 concludes
  `Erases.fixvar` there. What the recursive discharge's `hbodies` (each *opened* sibling
  body erases) still needs on top is the **environment**-level walk — `visitMutual`'s own
  motive, which stays `True` (W3.2, the cold-start/DAG slice) — so `hbodies` remains
  folded into `RegisteredClosureRec` for now.
* **`NoFixEnv` relaxation (item 2, DONE — recursion wall, slice W2).** D3 and the forward
  simulations no longer carry `NoFixEnv E`, and no longer conclude `NoFix t'`: they accept
  **recursive** environments. A recursive head in the β case unfolds through
  `erases_lam_head_step` (one source β-step ↔ the head's `WcbvEval.fix_guarded` stack + one
  `beta`), and a recursive constant in the δ case is a value on both sides (`fix_atom`).
  What is threaded in their place is one registration-level premise,
  `RecEnvConsistent env Us Γ Esrc E` (`ErasesCorrect.lean`): the block `Γ` records for a
  constant is what `E` stores, and the constant's source body erases to it. It is
  `RegisteredClosureRec` re-keyed on `Γ.recBodies`, so the recursive env-level discharge
  below feeds it directly — modulo the `Γ`↔`E` registration agreement the cold-start walk
  owes (`recEnvConsistent_of_registeredClosureRec`'s `hkey`).

`PrepareHyps` (csimp-off elaborator-transformation soundness) remains a `Prop` trust
class for the eventual `erase`-level statement (it links `prepare_erasure e`'s evaluation
to `e`'s). All new trust is `Prop` hypotheses — **never axioms of ours**.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure

/-- **D3 with δ-consistency sourced from registration.** The first-order shipping
correctness theorem (`shipping_erase_correct_firstorder`) restated with its
environment-δ-consistency premise `hdelta : ErasesEnvDeltaData` **replaced** by the
registration record `RegisteredClosureData` — the `Prop` hypothesis a cold-start DAG walk
(P3.13, deferred) would discharge from the actual `visitMutual` run. The δ-consistency is
discharged internally by `erasesEnvDeltaData_of_registeredClosureData`.

`ErasesEnvCtor`/`ErasesEnvCases` are likewise registration-derivable
(`erasesEnvCtor_of_registeredCtors`/`erasesEnvCases_of_registeredCases`, `EnvErasureNonrec`);
`hctorenv` is left as the direct env premise here so the composition stays focused on the
δ payoff and its non-vacuity guard reuses the existing `ΓFOd_envctor`. Everything else
(the run `hrun`, the invariant `hinv`, the trust bundles `H`/`HD`, the recursion premise
`RecEnvConsistent E`, the first-order value premise `hfo`) is threaded verbatim; the
conclusion is D3's — `t` `WcbvEval`-uates at `appliedFlags` to the unique applied erasure
of `v`. -/
theorem shipping_erase_correct_firstorder_registered
    {env : VEnv} (henv : env.WF) {Us : List Name}
    {known : Name → Prop} {Γ : ErasureCtx} {Esrc : SEnv} {E : GlobalDeclarations}
    (hcon : SEnvConsistent env Us Esrc)
    (hregdelta : RegisteredClosureData env Us Γ Esrc E)
    (hctorenv : ErasesEnvCtor Γ E)
    (hcc : ∀ {cn : Name} {iid : InductiveId} {cidx : Nat},
             Γ.ctors cn = some (iid, cidx) → Γ.casesOns cn = none)
    (hrec : RecEnvConsistent env Us Γ Esrc E)
    (hnfv : Γ.fixvars = fun _ => none)
    {gw : Void IO.RealWorld → NameGenerator}
    (H : BridgeHyps env Us Γ gw) (HD : DataBridgeHyps Γ gw) (C : CasesBridgeHyps Γ gw)
    {e v : Expr} {ve : VExpr} {t : LBTerm}
    {s s' : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    (hrun : Erasure.visitExpr e s ctx cctx ref w = .ok (t, s') w')
    (hinv : BridgeInv env Us known Γ (gw w) ctx s [])
    (hsup : Supported known Γ e)
    (htr : TrExprS env Us [] e ve)
    (hnb : NoBlock t)
    (hev : SEvalDataC Γ Esrc e v)
    (hfo : FirstOrderValue env Us Γ [] v) :
    ∃ t', WcbvEval E appliedFlags t t' ∧
      (∃ vve, TrExprS env Us [] v vve) ∧
      Erases env Us Γ [] v t' ∧ NoBlock t' ∧
      ∀ tu, Erases env Us Γ [] v tu → NoBlock tu → tu = t' :=
  shipping_erase_correct_firstorder henv hcon
    (erasesEnvDeltaData_of_registeredClosureData hregdelta)
    hctorenv hcc hrec hnfv H HD C hrun hinv hsup htr hnb hev hfo

/-! ## Non-vacuity guard

The concrete nullary first-order constructor `c : I` (`FirstOrder.lean`), reused from
D3's own guard: the registration records hold vacuously (`Esrc` is all-`none`, so
`RegisteredClosureData`/`RegisteredCtors` are trivially satisfied except the genuinely
firing `RegisteredCtors` on `c`'s inductive), and the theorem *fires* — producing `t'`
and its uniqueness. The run and the two trust bundles stay hypothetical. -/
example (harity : ¬ IsArityUpTo envFO 0 [] (.const `I []))
    (gw : Void IO.RealWorld → NameGenerator)
    (H : BridgeHyps envFO [] ΓFOd gw) (HD : DataBridgeHyps ΓFOd gw)
    (C : CasesBridgeHyps ΓFOd gw)
    (s s' : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w w' : Void IO.RealWorld) (t : LBTerm)
    (hrun : Erasure.visitExpr (.const `c []) s ctx cctx ref w = .ok (t, s') w')
    (hinv : BridgeInv envFO [] (fun _ => False) ΓFOd (gw w) ctx s [])
    (hsup : Supported (fun _ => False) ΓFOd (.const `c []))
    (hnb : NoBlock t) :
    ∃ t', WcbvEval EFOd appliedFlags t t' ∧
      (∃ vve, TrExprS envFO [] [] (.const `c []) vve) ∧
      Erases envFO [] ΓFOd [] (.const `c []) t' ∧ NoBlock t' ∧
      ∀ tu, Erases envFO [] ΓFOd [] (.const `c []) tu → NoBlock tu → tu = t' := by
  have heq : (.const `c [] : Expr) = ([] : List Expr).foldl Expr.app (.const `c []) := rfl
  refine shipping_erase_correct_firstorder_registered envFO_wf (Us := []) (Esrc := fun _ => none)
    (E := EFOd) ?_ ⟨?_, ?_⟩ ΓFOd_envctor ?_
    (recEnvConsistent_of_noRec (Γ := ΓFOd) rfl)        -- ΓFOd registers no recursion
    rfl                                                -- …and installs no fixvar map
    H HD C hrun hinv hsup envFO_trC hnb ?_
    (envFO_foC_d harity)
  · intro Δ n us body cve h; exact absurd h (by simp)   -- SEnvConsistent, vacuous
  · intro n body h; exact absurd h (by simp)            -- RegisteredClosureData.disj, vacuous
  · intro n body h; exact absurd h (by simp)            -- RegisteredClosureData.erase, vacuous
  · intro cn iid cidx hc                                -- hcc (ctors ⟹ casesOns = none)
    by_cases h : cn = `c
    · subst h; rfl
    · simp [ΓFOd, if_neg h] at hc
  · rw [heq]                                            -- SEvalDataC c → c
    exact .ctor_val ΓFOd_ctorsC ΓFOd_ctorAritiesC (by simp) rfl (fun i h => absurd h (by simp))

end LeanToLambdaBox
