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
  env `E`. A well-founded recursion over the acyclic cross-block dependency graph
  (relaxing `VisitExprRefines.BridgeInv.consts`, which currently forbids the cold-start
  `get_constant_kername` miss branch) would *prove* them from the actual `visitMutual`
  registration. This also supplies the top-level term bridge (`hrun`/`hinv`), which is why
  the subject here is still `visitExpr e` under a registered state, not cold-start `erase`.
* **`visitConst`-fixvar bridge (P3.12, deferred).** The recursive discharge's `hbodies`
  (each opened sibling body erases) is a bridge fact the fixvar branch of
  `visitExpr_refines_erases` would supply; it is folded into `RegisteredClosureRec`.
* **`NoFixEnv` relaxation (item 2, deferred).** D3 and both forward simulations
  (`erases_correct`, `erases_correct_data`) carry `NoFixEnv E` **and conclude `NoFix t'`**;
  their `.lam`-source fix disjunct is discharged by `hnfx.elim`. Consuming a *recursive*
  `.fix` constant body in the δ case requires simulating the guarded/unguarded fix
  unfolding (`WcbvEval` `fix_guarded`/`fix_unguarded`) *and* dropping `NoFix t'` from the
  conclusion (a fix value is not `NoFix`), which re-touches both forward sims — an XL piece
  deferred. Hence the composition here stays in the fix-free (first-order) fragment
  (`NoFixEnv E` retained), while the recursive env-level discharge stands ready for when
  the forward sims are relaxed. The forward-sim byte-set / D3 axioms are therefore
  **unchanged**.

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
(the run `hrun`, the invariant `hinv`, the trust bundles `H`/`HD`, the fix-free premise
`NoFixEnv E`, the first-order value premise `hfo`) is threaded verbatim; the conclusion is
D3's — `t` `WcbvEval`-uates at `appliedFlags` to the unique applied erasure of `v`. -/
theorem shipping_erase_correct_firstorder_registered
    {env : VEnv} (henv : env.WF) {Us : List Name}
    {known : Name → Prop} {Γ : ErasureCtx} {Esrc : SEnv} {E : GlobalDeclarations}
    (hcon : SEnvConsistent env Us Esrc)
    (hregdelta : RegisteredClosureData env Us Γ Esrc E)
    (hctorenv : ErasesEnvCtor Γ E)
    (hcc : ∀ {cn : Name} {iid : InductiveId} {cidx : Nat},
             Γ.ctors cn = some (iid, cidx) → Γ.casesOns cn = none)
    (hnfenv : NoFixEnv E)
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
    (hnfx : NoFix t)
    (hev : SEvalDataC Γ Esrc e v)
    (hfo : FirstOrderValue env Us Γ [] v) :
    ∃ t', WcbvEval E appliedFlags t t' ∧
      (∃ vve, TrExprS env Us [] v vve) ∧
      Erases env Us Γ [] v t' ∧ NoBlock t' ∧
      ∀ tu, Erases env Us Γ [] v tu → NoBlock tu → tu = t' :=
  shipping_erase_correct_firstorder henv hcon
    (erasesEnvDeltaData_of_registeredClosureData hregdelta)
    hctorenv hcc hnfenv H HD C hrun hinv hsup htr hnb hnfx hev hfo

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
    (hinv : BridgeInv envFO [] (fun _ => True) ΓFOd (gw w) ctx s [])
    (hsup : Supported (fun _ => True) ΓFOd (.const `c []))
    (hnb : NoBlock t) (hnfx : NoFix t) :
    ∃ t', WcbvEval EFOd appliedFlags t t' ∧
      (∃ vve, TrExprS envFO [] [] (.const `c []) vve) ∧
      Erases envFO [] ΓFOd [] (.const `c []) t' ∧ NoBlock t' ∧
      ∀ tu, Erases envFO [] ΓFOd [] (.const `c []) tu → NoBlock tu → tu = t' := by
  have heq : (.const `c [] : Expr) = ([] : List Expr).foldl Expr.app (.const `c []) := rfl
  refine shipping_erase_correct_firstorder_registered envFO_wf (Us := []) (Esrc := fun _ => none)
    (E := EFOd) ?_ ⟨?_, ?_⟩ ΓFOd_envctor ?_ ?_ H HD C hrun hinv hsup envFO_trC hnb hnfx ?_
    (envFO_foC_d harity)
  · intro Δ n us body cve h; exact absurd h (by simp)   -- SEnvConsistent, vacuous
  · intro n body h; exact absurd h (by simp)            -- RegisteredClosureData.disj, vacuous
  · intro n body h; exact absurd h (by simp)            -- RegisteredClosureData.erase, vacuous
  · intro cn iid cidx hc                                -- hcc (ctors ⟹ casesOns = none)
    by_cases h : cn = `c
    · subst h; rfl
    · simp [ΓFOd, if_neg h] at hc
  · intro kn body' h                                    -- NoFixEnv EFOd, vacuous
    simp only [EFOd, LBTerm.envLookup] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
  · rw [heq]                                            -- SEvalDataC c → c
    exact .ctor_val ΓFOd_ctorsC ΓFOd_ctorAritiesC (by simp) rfl (fun i h => absurd h (by simp))

end LeanToLambdaBox
