import LeanToLambdaBox.ErasureRun
import LeanToLambdaBox.Bridge
import LeanToLambdaBox.DataBridgeHyps
import LeanToLambdaBox.CasesBridgeHyps
import LeanToLambdaBox.ProjBridgeHyps
import LeanToLambdaBox.DeltaHyps
import LeanToLambdaBox.RecBlockErasure
import LeanToLambdaBox.EraseCore
import LeanToLambdaBox.CheckerAdequacy
-- Only for the projection guard (v): `ofNatBodyQ` and its `TrExprS` witness, the one
-- translation in the development that goes *through* a `TrProj`.
import LeanToLambdaBox.ProjPattern
import Lean4Lean.Verify.NameGenerator

/-!
# The bridge theorem: `Erasure.visitExpr` refines `Erases`

This file proves the crown theorem of the verification: on the supported
fragment (`Supported`, Bridge.lean), a **successful run of the shipping
erasure** `Erasure.visitExpr` produces a term related to its input by the
typed erasure relation `Erases` (Erases.lean) — by fixpoint induction
(`Erasure.visitExpr.mutual_fixpoint_induct`) over the 18-function erasure
family, using the run-lemma library of `ErasureRun.lean`.

## Architecture

* **`BridgeHyps`** / **`DataBridgeHyps`** / **`CasesBridgeHyps`** /
  **`ProjBridgeHyps`** — the four
  trust bundles. `BridgeHyps` carries Hoare-style hypotheses about the four
  opaque runtime primitives the bridge cannot compute with
  (`liftMetaM (isErasable e)`, `mkFreshFVarId`, `getCasesInfo?`,
  `getCtorArity?`), phrased against a ghost world-measure
  `gw : Void IO.RealWorld → NameGenerator` (the name-generator state as a
  function of the `EST` world token). These play the role `OracleSound`
  played for `eraseCore`: they are the bridge's honest assumptions, and their
  global satisfiability is *not* in-logic decidable — the primitives are
  opaque `ST`/`EIO` operations. This is the documented trust boundary.
  `DataBridgeHyps` (`DataBridgeHyps.lean`) adds the constructor data path's
  specs, `CasesBridgeHyps` (`CasesBridgeHyps.lean`) the ι (`casesOn`) path's and
  `ProjBridgeHyps` (`ProjBridgeHyps.lean`, slice proj-P8) the projection path's;
  all four are consumed by the single induction below. A fifth,
  `DeltaHyps` (`DeltaHyps.lean`), carries the δ (constant-unfolding) fragment's
  *scope* obligations — it is the scope-side half of the two-part contract whose
  state-side half is `BridgeInv` — and since slice D4a this induction consumes it
  too, in step 6 (see `BridgeInv`'s docstring for the field its arrival replaced).
  Walking step 6's *recursive* exit (slice Γ-W3.6b) added two more premises of the
  same class: `BlockHyps` (`DeltaHyps.lean`), the block-local companion keyed on the
  sibling fetch, and the named `RecBlockAgreement` below.
* **`BridgeInv`** — the induction invariant: the reader's `LocalContext`
  corresponds to the typing context `Δ` (lean4lean's `TrLCtx`), the reader's
  block-local `fixvars` map agrees with `Γ.fixvars` (and its ids are fresh for `Δ`),
  every fvar of `Δ` is reserved by the current generator, and every *registered*
  kername agrees with `Γ` (the soundness direction only — since slice D4a the
  invariant says nothing about `known`; see its docstring).
* **`visitExpr_refines_erases`** — the final export (the content half of
  motive 1 of the 18-motive induction `visitExpr_refines_erases_core`; the
  other half is the approximation conjunct of slice Γ-W3.5, a tautology at
  the fixpoint).

Trust boundary: since the lean4lean `trproj` re-pin the results are **`sorryAx`-free**
— `TrProj` has a real definition upstream, so nothing enters through the *type* of a
`TrExprS`-adjacent statement any more; the audit block at the foot of this file carries
the measurement. What remains is lean4lean's `Expr`/`PersistentHashMap` modeling axioms
(through `Bridge.lean`'s `find?` lemmas and `instantiate1_eq`), plus the trust bundles
above. No `sorry` of our own, no new axioms.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure
open Lean4Lean.TypeChecker (MLCtx kernelNGen)
-- the `⊑` of `Lean.Order`: the approximation conjunct every motive now carries (Γ-W3.5).
open scoped Lean.Order

/-! ## Pure helpers -/

/-- On a bvar-free context (all entries fvar-tagged, as produced by a real
`LocalContext`), de Bruijn lookups fail. Used to refute the `.bvar` case of
`visitExpr` from the term's own translation premise. -/
theorem VLCtx.find?_bvar_none_of_noBV :
    ∀ {Δ : VLCtx}, Δ.NoBV → ∀ i, Δ.find? (.inl i) = none := by
  intro Δ
  induction Δ with
  | nil => intro _ i; rfl
  | cons p Δ ih =>
    obtain ⟨ofv, d⟩ := p
    cases ofv with
    | none =>
      intro h
      simp [VLCtx.NoBV, VLCtx.bvars] at h
    | some fv =>
      intro h i
      have hΔ : VLCtx.NoBV Δ := h
      simp only [Lean4Lean.VLCtx.find?, Lean4Lean.VLCtx.next, ih hΔ i]
      rfl

/-- The head of an application spine peels through a `List.foldl Expr.app`. -/
theorem expr_getAppFn_foldl (f : Expr) (args : List Expr) :
    (args.foldl Expr.app f).getAppFn = f.getAppFn := by
  induction args generalizing f with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, ih]; rfl

/-- `getAppArgsList` of a `foldl`-spine peels the whole list onto the accumulator. -/
theorem getAppArgsList_foldl (head : Expr) : ∀ (l r : List Expr),
    (l.foldl Expr.app head).getAppArgsList r = head.getAppArgsList (l ++ r) := by
  intro l
  induction l generalizing head with
  | nil => intro r; rfl
  | cons a as ih => intro r; rw [List.foldl_cons, ih (head.app a) r]; rfl

/-- The argument list recovered from a `.const`-headed `foldl`-spine is the list. -/
theorem foldl_getAppArgs_toList (cn : Name) (us : List Level) (l : List Expr) :
    (l.foldl Expr.app (Expr.const cn us)).getAppArgs.toList = l := by
  rw [Lean.Expr.getAppArgs_toList,
    show (l.foldl Expr.app (Expr.const cn us)).getAppArgsList
      = (l.foldl Expr.app (Expr.const cn us)).getAppArgsList [] from rfl,
    getAppArgsList_foldl]
  simp [Lean.Expr.getAppArgsList]

/-! ### Inverting the supported fragment on constructor spines

The `Supported.ctorApp` rule (`Bridge.lean`) has a `List.foldl`-indexed conclusion,
so the auto-generated recursor cannot `cases`/`induction`-eliminate it when the goal
depends on the subject. The lemmas below invert it with an *`e`-free* goal (the same
device `Erases.app_inv_t` uses), then assemble the spine facts by strong induction on
the argument count. -/

/-- Full data carried by a supported constructor spine. -/
def CtorSpineData (known : Name → Prop) (Γ : ErasureCtx) (cn : Name) (args : List Expr) : Prop :=
  ∃ (iid : InductiveId) (cidx ar : Nat), Γ.ctors cn = some (iid, cidx) ∧
    Γ.ctorArities cn = some ar ∧ args.length = ar ∧ Γ.casesOns cn = none ∧
    cn ≠ ``Nat.zero ∧ cn ≠ ``Nat.succ ∧ ∀ i (hi : i < args.length), Supported known Γ (args[i])

/-- Full data carried by a supported (saturated, flat-alternative) `casesOn` spine.
Unlike `CtorSpineData` the facts are **position-dependent**: the `dp` dropped
prefix arguments (params/motive/indices) carry *no* obligation — `Erases.cases`
imposes none on `pre` and the eraser never visits it. -/
def CasesSpineData (known : Name → Prop) (Γ : ErasureCtx) (con : Name)
    (args : List Expr) : Prop :=
  ∃ (iid : InductiveId) (np dp : Nat) (nfs : List Nat),
    Γ.casesOns con = some (iid, np) ∧ Γ.casesDiscrPos con = some dp ∧
    Γ.ctorFields iid = some nfs ∧ args.length = dp + 1 + nfs.length ∧
    con.getPrefix ≠ ``Nat ∧ con.getPrefix ≠ ``Int ∧
    (∀ (h : dp < args.length), Supported known Γ (args[dp])) ∧
    (∀ j (hj : j < nfs.length) (h : dp + 1 + j < args.length),
      IsLamTelescope (nfs[j]'hj) (args[dp + 1 + j]) ∧ Supported known Γ (args[dp + 1 + j]))

/-- Reading off the discriminant slot of a `pre ++ discr :: minors` spine. -/
theorem getElem_append_cons_mid {α} (pre : List α) (d : α) (post : List α) :
    (pre ++ d :: post)[pre.length]'(by simp) = d := by
  rw [List.getElem_append_right (Nat.le_refl _)]
  simp

/-- Reading off minor `j` of a `pre ++ discr :: minors` spine. -/
theorem getElem_append_cons_add {α} (pre : List α) (d : α) (post : List α) (j : Nat)
    (hj : j < post.length) :
    (pre ++ d :: post)[pre.length + 1 + j]'(by simp; omega) = post[j] := by
  rw [List.getElem_append_right (by omega)]
  have h : pre.length + 1 + j - pre.length = j + 1 := by omega
  simp [h]

/-- Invert `Supported (.const cn us)`: either the plain-`const` rule (with the
`known`/`ctors = none`/`casesOns = none` witnesses) or a nullary `ctorApp`
(`args = []`). The `casesApp` rule cannot produce a bare `.const`: its spine
always contains the discriminant. -/
theorem Supported.const_inv' {known : Name → Prop} {Γ : ErasureCtx} {cn : Name}
    {us : List Level} (h : Supported known Γ (.const cn us)) :
    ((known cn ∨ Γ.fixvars cn ≠ none) ∧ Γ.ctors cn = none ∧ Γ.casesOns cn = none) ∨
      CtorSpineData known Γ cn [] := by
  generalize he : (Expr.const cn us) = e at h
  cases h with
  | const n us' hk hct hcs => cases he; exact .inl ⟨hk, hct, hcs⟩
  | @ctorApp cn' us' iid cidx ar args' hc' hcases' har' hsat' hz' hs' hargs' =>
      rcases List.eq_nil_or_concat args' with rfl | ⟨i', l', rfl⟩
      · simp only [List.foldl_nil] at he; cases he
        exact .inr ⟨iid, cidx, ar, hc', har', hsat', hcases', hz', hs', hargs'⟩
      · rw [List.concat_eq_append, List.foldl_append, List.foldl_cons, List.foldl_nil] at he
        exact absurd he (by simp)
  | @casesApp con us' iid np dp nfs pre minors discr hc hdp hnfs hpre hsat hnat hint
      hdiscr hlam hminors =>
      obtain ⟨g, a, hga⟩ := exists_app_of_foldl_app_ne_nil (Expr.const con us')
        (args := pre ++ discr :: minors) (by simp)
      rw [hga] at he; exact absurd he (by simp)
  | _ => exact absurd he (by simp)

/-- Invert `Supported (f.app a)`: either structural application, or the whole node
is a (saturated) `ctorApp` / `casesApp` with its full spine data. -/
theorem Supported.app_inv'' {known : Name → Prop} {Γ : ErasureCtx} {f a : Expr}
    (h : Supported known Γ (f.app a)) :
    (Supported known Γ f ∧ Supported known Γ a) ∨
    (∃ (cn : Name) (us : List Level) (args' : List Expr),
      f.app a = args'.foldl Expr.app (.const cn us) ∧ CtorSpineData known Γ cn args') ∨
    (∃ (con : Name) (us : List Level) (args' : List Expr),
      f.app a = args'.foldl Expr.app (.const con us) ∧ CasesSpineData known Γ con args') := by
  generalize he : (Expr.app f a) = e at h
  cases h with
  | app hf ha => cases he; exact .inl ⟨hf, ha⟩
  | @ctorApp cn' us' iid cidx ar args' hc' hcases' har' hsat' hz' hs' hargs' =>
      exact .inr (.inl ⟨cn', us', args', rfl, iid, cidx, ar, hc', har', hsat',
        hcases', hz', hs', hargs'⟩)
  | @casesApp con us' iid np dp nfs pre minors discr hc hdp hnfs hpre hsat hnat hint
      hdiscr hlam hminors =>
      subst hpre
      refine .inr (.inr ⟨con, us', pre ++ discr :: minors, rfl,
        iid, np, pre.length, nfs, hc, hdp, hnfs, by simp [hsat]; omega, hnat, hint,
        fun hlt => ?_, fun j hj hlt => ?_⟩)
      · rw [getElem_append_cons_mid]; exact hdiscr
      · rw [getElem_append_cons_add pre discr minors j (hsat ▸ hj)]
        exact ⟨hlam j (hsat ▸ hj), hminors j (hsat ▸ hj)⟩
  | _ => exact absurd he (by simp)

/-- Invert `Supported (.lam ..)` — neither spine rule can produce a `.lam`. -/
theorem Supported.lam_inv {known : Name → Prop} {Γ : ErasureCtx} {n : Name} {ty b : Expr}
    {bi : BinderInfo} (h : Supported known Γ (.lam n ty b bi)) : Supported known Γ b := by
  generalize he : (Expr.lam n ty b bi) = e at h
  cases h with
  | lam _ _ _ hb => cases he; exact hb
  | @ctorApp cn us iid cidx ar args hc hcases har hsat hz hs hargs =>
      rcases List.eq_nil_or_concat args with rfl | ⟨i, l, rfl⟩ <;>
        simp only [List.foldl_nil, List.concat_eq_append, List.foldl_append,
          List.foldl_cons, List.foldl_nil] at he <;> exact absurd he (by simp)
  | @casesApp con us iid np dp nfs pre minors discr hc hdp hnfs hpre hsat hnat hint
      hdiscr hlam hminors =>
      obtain ⟨g, a, hga⟩ := exists_app_of_foldl_app_ne_nil (Expr.const con us)
        (args := pre ++ discr :: minors) (by simp)
      rw [hga] at he; exact absurd he (by simp)
  | _ => exact absurd he (by simp)

/-- Invert `Supported (.letE ..)` — neither spine rule can produce a `.letE`. -/
theorem Supported.letE_inv {known : Name → Prop} {Γ : ErasureCtx} {n : Name}
    {ty v b : Expr} {nd : Bool} (h : Supported known Γ (.letE n ty v b nd)) :
    Supported known Γ v ∧ Supported known Γ b := by
  generalize he : (Expr.letE n ty v b nd) = e at h
  cases h with
  | letE _ _ _ hv hb => cases he; exact ⟨hv, hb⟩
  | @ctorApp cn us iid cidx ar args hc hcases har hsat hz hs hargs =>
      rcases List.eq_nil_or_concat args with rfl | ⟨i, l, rfl⟩ <;>
        simp only [List.foldl_nil, List.concat_eq_append, List.foldl_append,
          List.foldl_cons, List.foldl_nil] at he <;> exact absurd he (by simp)
  | @casesApp con us iid np dp nfs pre minors discr hc hdp hnfs hpre hsat hnat hint
      hdiscr hlam hminors =>
      obtain ⟨g, a, hga⟩ := exists_app_of_foldl_app_ne_nil (Expr.const con us)
        (args := pre ++ discr :: minors) (by simp)
      rw [hga] at he; exact absurd he (by simp)
  | _ => exact absurd he (by simp)

/-- A ctor-headed supported spine yields its full spine data, up to over-application
(the arity bound is `≤`; over-application is well-typedness-excluded downstream but
the fragment permits it syntactically). The `hncs` premise (`cn` is not *also* a
registered `casesOn` head) discriminates against the `casesApp` rule, whose spine
is likewise `.const`-headed; every call site has it from the head classification. -/
theorem Supported.ctorApp_inv {known : Name → Prop} {Γ : ErasureCtx} :
    ∀ (m : Nat) {args : List Expr} {cn : Name} {us : List Level} {iid : InductiveId} {cidx : Nat},
      args.length = m → Supported known Γ (args.foldl Expr.app (.const cn us)) →
      Γ.ctors cn = some (iid, cidx) → Γ.casesOns cn = none →
      ∃ ar, Γ.ctorArities cn = some ar ∧ ar ≤ args.length ∧
        Γ.casesOns cn = none ∧ cn ≠ ``Nat.zero ∧ cn ≠ ``Nat.succ ∧
        ∀ i (hi : i < args.length), Supported known Γ (args[i]) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro args cn us iid cidx hm h hc hncs
    rcases List.eq_nil_or_concat args with rfl | ⟨init, last, rfl⟩
    · simp only [List.foldl_nil] at h
      rcases h.const_inv' with ⟨_, hct, _⟩ | ⟨iid', cidx', ar, hc', har', hsat', hcs', hz', hs', hargs'⟩
      · rw [hct] at hc; exact absurd hc (by simp)
      · exact ⟨ar, har', by simp [← hsat'], hcs', hz', hs', hargs'⟩
    · rw [List.concat_eq_append, List.foldl_append, List.foldl_cons, List.foldl_nil] at h
      rcases h.app_inv'' with ⟨hf, ha⟩ | ⟨cn', us', args'', heq, hcd⟩ | ⟨con', us', args'', heq, hcd⟩
      · have hltm : init.length < m := by
          rw [← hm]; simp only [List.concat_eq_append, List.length_append, List.length_cons,
            List.length_nil]; omega
        obtain ⟨ar, har, hle, hcs, hz, hs, hargs⟩ := ih init.length hltm rfl hf hc hncs
        refine ⟨ar, har, ?_, hcs, hz, hs, fun i hi => ?_⟩
        · simp only [List.concat_eq_append, List.length_append, List.length_cons,
            List.length_nil]; omega
        · simp only [List.concat_eq_append, List.length_append, List.length_cons,
            List.length_nil] at hi ⊢
          by_cases hii : i < init.length
          · rw [List.getElem_append_left hii]; exact hargs i hii
          · have hieq : i = init.length := by omega
            subst hieq
            rw [List.getElem_append_right (by omega)]
            simp only [Nat.sub_self, List.getElem_cons_zero]
            exact ha
      · obtain ⟨iid', cidx', ar, hc', har', hsat', hcs', hz', hs', hargs'⟩ := hcd
        have hfn : (Expr.app (init.foldl Expr.app (.const cn us)) last).getAppFn
            = (args''.foldl Expr.app (.const cn' us')).getAppFn := by rw [heq]
        simp only [Expr.getAppFn] at hfn
        rw [expr_getAppFn_foldl, expr_getAppFn_foldl] at hfn
        simp only [Expr.getAppFn] at hfn
        obtain ⟨rfl, rfl⟩ := hfn
        have heq2 : (init ++ [last]).foldl Expr.app (Expr.const cn us)
            = args''.foldl Expr.app (Expr.const cn us) := by
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil]; exact heq
        have hargeq : (init ++ [last]) = args'' := by
          have h2 := congrArg (fun e => e.getAppArgs.toList) heq2
          simp only [foldl_getAppArgs_toList] at h2; exact h2
        rw [List.concat_eq_append, hargeq]
        exact ⟨ar, har', Nat.le_of_eq hsat'.symm, hcs', hz', hs', hargs'⟩
      · exfalso
        obtain ⟨iid', np', dp', nfs', hcs', _⟩ := hcd
        have hfn : (Expr.app (init.foldl Expr.app (.const cn us)) last).getAppFn
            = (args''.foldl Expr.app (.const con' us')).getAppFn := by rw [heq]
        simp only [Expr.getAppFn] at hfn
        rw [expr_getAppFn_foldl, expr_getAppFn_foldl] at hfn
        simp only [Expr.getAppFn] at hfn
        obtain ⟨rfl, rfl⟩ := hfn
        rw [hncs] at hcs'; exact absurd hcs' (by simp)

/-- `List.eq_nil_or_concat` with the tail spelled as an append, so that
`List.getElem_append_left/right` apply without a `concat`-normalisation detour
(the indexing in `Supported.casesApp_inv` is position-dependent, and rewriting a
`concat` under a dependent `getElem` proof breaks the motive). -/
theorem list_eq_nil_or_append_singleton {α} (l : List α) :
    l = [] ∨ ∃ (init : List α) (last : α), l = init ++ [last] := by
  rcases List.eq_nil_or_concat l with rfl | ⟨init, last, rfl⟩
  · exact .inl rfl
  · exact .inr ⟨init, last, by rw [List.concat_eq_append]⟩

/-- A `casesOn`-headed supported spine yields its full spine data, up to
over-application. Strong induction on the argument count, exactly like
`Supported.ctorApp_inv`; the `dp` dropped prefix arguments carry no obligation. -/
theorem Supported.casesApp_inv {known : Name → Prop} {Γ : ErasureCtx} :
    ∀ (m : Nat) {args : List Expr} {con : Name} {us : List Level} {iid : InductiveId} {np : Nat},
      args.length = m → Supported known Γ (args.foldl Expr.app (.const con us)) →
      Γ.casesOns con = some (iid, np) →
      ∃ dp nfs, Γ.casesDiscrPos con = some dp ∧ Γ.ctorFields iid = some nfs ∧
        dp + 1 + nfs.length ≤ args.length ∧
        con.getPrefix ≠ ``Nat ∧ con.getPrefix ≠ ``Int ∧
        (∀ (h : dp < args.length), Supported known Γ (args[dp])) ∧
        (∀ j (hj : j < nfs.length) (h : dp + 1 + j < args.length),
          IsLamTelescope (nfs[j]'hj) (args[dp + 1 + j])) ∧
        (∀ i (hi : i < args.length), dp + 1 ≤ i → Supported known Γ (args[i])) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro args con us iid np hm h hcs
    rcases list_eq_nil_or_append_singleton args with rfl | ⟨init, last, rfl⟩
    · exfalso
      simp only [List.foldl_nil] at h
      rcases h.const_inv' with ⟨_, _, hcs'⟩ | ⟨_, _, _, _, _, _, hcs', _⟩ <;>
        (rw [hcs] at hcs'; exact absurd hcs' (by simp))
    · rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at h
      have hlen : (init ++ [last]).length = init.length + 1 := by simp
      rcases h.app_inv'' with ⟨hf, ha⟩ | ⟨cn', us', args'', heq, hcd⟩ | ⟨con', us', args'', heq, hcd⟩
      · -- over-application: recurse on the initial segment
        have hltm : init.length < m := by rw [← hm, hlen]; omega
        obtain ⟨dp, nfs, hdp, hnfs, hle, hnat, hint, hd, hlam, hsupp⟩ :=
          ih init.length hltm rfl hf hcs
        refine ⟨dp, nfs, hdp, hnfs, by omega, hnat, hint, fun hlt => ?_,
          fun j hj hlt => ?_, fun i hi hile => ?_⟩
        · rw [List.getElem_append_left (show dp < init.length by omega)]
          exact hd (by omega)
        · rw [List.getElem_append_left (show dp + 1 + j < init.length by omega)]
          exact hlam j hj (by omega)
        · rw [hlen] at hi
          by_cases hii : i < init.length
          · rw [List.getElem_append_left hii]; exact hsupp i hii hile
          · have hieq : i = init.length := by omega
            subst hieq
            rw [List.getElem_append_right (Nat.le_refl _)]
            simp only [Nat.sub_self, List.getElem_cons_zero]
            exact ha
      · exfalso
        obtain ⟨iid', cidx', ar, hc', _, _, hcs', _⟩ := hcd
        have hfn : (Expr.app (init.foldl Expr.app (.const con us)) last).getAppFn
            = (args''.foldl Expr.app (.const cn' us')).getAppFn := by rw [heq]
        simp only [Expr.getAppFn] at hfn
        rw [expr_getAppFn_foldl, expr_getAppFn_foldl] at hfn
        simp only [Expr.getAppFn] at hfn
        obtain ⟨rfl, rfl⟩ := hfn
        rw [hcs] at hcs'; exact absurd hcs' (by simp)
      · -- exact saturation: the whole spine is the `casesApp` node
        obtain ⟨iid', np', dp, nfs, hcs', hdp, hnfs, hlen', hnat, hint, hd, hlam⟩ := hcd
        have hfn : (Expr.app (init.foldl Expr.app (.const con us)) last).getAppFn
            = (args''.foldl Expr.app (.const con' us')).getAppFn := by rw [heq]
        simp only [Expr.getAppFn] at hfn
        rw [expr_getAppFn_foldl, expr_getAppFn_foldl] at hfn
        simp only [Expr.getAppFn] at hfn
        obtain ⟨rfl, rfl⟩ := hfn
        obtain ⟨rfl, rfl⟩ : iid' = iid ∧ np' = np := by
          rw [hcs] at hcs'; simpa using hcs'.symm
        have heq2 : (init ++ [last]).foldl Expr.app (Expr.const con us)
            = args''.foldl Expr.app (Expr.const con us) := by
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil]; exact heq
        have hargeq : (init ++ [last]) = args'' := by
          have h2 := congrArg (fun e => e.getAppArgs.toList) heq2
          simp only [foldl_getAppArgs_toList] at h2; exact h2
        subst hargeq
        refine ⟨dp, nfs, hdp, hnfs, Nat.le_of_eq hlen'.symm, hnat, hint, hd,
          fun j hj hlt => (hlam j hj hlt).1, fun i hi hile => ?_⟩
        have hj : i - (dp + 1) < nfs.length := by omega
        have hii : dp + 1 + (i - (dp + 1)) = i := by omega
        have hres := (hlam (i - (dp + 1)) hj (by omega)).2
        simp only [hii] at hres
        exact hres

/-- Inversion of `Supported` along a `foldl`-spine with a head that is **neither a
registered constructor nor a registered `casesOn`** (`hnc`/`hncs`): the head and
every argument are supported. (For the two spine-shaped rules use
`Supported.ctorApp_inv` / `Supported.casesApp_inv`.) -/
theorem supported_foldl_app_inv {known : Name → Prop} {Γ : ErasureCtx} :
    ∀ {args : List Expr} {f : Expr},
      (∀ cn us, f.getAppFn = .const cn us → Γ.ctors cn = none) →
      (∀ cn us, f.getAppFn = .const cn us → Γ.casesOns cn = none) →
      Supported known Γ (args.foldl Expr.app f) →
      Supported known Γ f ∧ ∀ a ∈ args, Supported known Γ a := by
  intro args
  induction args with
  | nil => exact fun _ _ h => ⟨h, by simp⟩
  | cons a as ih =>
    intro f hnc hncs h
    simp only [List.foldl_cons] at h
    have hnc' : ∀ cn us, (f.app a).getAppFn = .const cn us → Γ.ctors cn = none := by
      intro cn us hfn; simp only [Expr.getAppFn] at hfn; exact hnc cn us hfn
    have hncs' : ∀ cn us, (f.app a).getAppFn = .const cn us → Γ.casesOns cn = none := by
      intro cn us hfn; simp only [Expr.getAppFn] at hfn; exact hncs cn us hfn
    obtain ⟨hfa, hrest⟩ := ih hnc' hncs' h
    rcases hfa.app_inv'' with ⟨hf, ha⟩ | ⟨cn', us', args', heq, hcd⟩ | ⟨con', us', args', heq, hcd⟩
    · refine ⟨hf, fun b hb => ?_⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ha
      · exact hrest _ hb
    · exfalso
      obtain ⟨iid, cidx, ar, hc', _⟩ := hcd
      have hfneq : (f.app a).getAppFn = .const cn' us' := by
        rw [heq]; exact expr_getAppFn_foldl _ _
      rw [hnc' cn' us' hfneq] at hc'; exact absurd hc' (by simp)
    · exfalso
      obtain ⟨iid, np, dp, nfs, hcs', _⟩ := hcd
      have hfneq : (f.app a).getAppFn = .const con' us' := by
        rw [heq]; exact expr_getAppFn_foldl _ _
      rw [hncs' con' us' hfneq] at hcs'; exact absurd hcs' (by simp)

/-- Spine reconstruction: folding `Expr.app` over `getAppArgs` from `getAppFn`
gives back the term (assembled from lean4lean's spine toolkit). -/
theorem getAppArgs_spine (e : Expr) :
    e.getAppArgs.toList.foldl Expr.app e.getAppFn = e := by
  rw [Lean.Expr.getAppArgs_toList, ← Lean.Expr.mkAppList_eq_foldl,
    Lean.Expr.mkAppList_getAppArgsList]

/-- Array-level spine reconstruction (the form `visitAppArgs`' motive uses). -/
theorem getAppArgs_spine' (e : Expr) :
    e.getAppArgs.foldl Expr.app e.getAppFn = e := by
  rw [← Array.foldl_toList]; exact getAppArgs_spine e

/-- `getAppFn` is idempotent (fully-peeled head). -/
theorem getAppFn_idem (e : Expr) : e.getAppFn.getAppFn = e.getAppFn := by
  induction e with
  | app f a ihf _ => rw [Expr.getAppFn]; exact ihf
  | _ => rfl

/-- Package the per-argument obligations of the `visitAppArgs` motive (plus the
head facts) from whole-term `Supported`/`TrExprS` facts, through the spine
reconstruction. -/
theorem spine_arg_facts {env : VEnv} {Us : List Name} {known : Name → Prop}
    {Γ : ErasureCtx} {Δ : VLCtx} {e : Expr}
    (hnc : ∀ cn us, e.getAppFn = .const cn us → Γ.ctors cn = none)
    (hncs : ∀ cn us, e.getAppFn = .const cn us → Γ.casesOns cn = none)
    (hsupp : Supported known Γ e) (hex : ∃ ve, TrExprS env Us Δ e ve) :
    (Supported known Γ e.getAppFn ∧ ∃ ve, TrExprS env Us Δ e.getAppFn ve) ∧
    ∀ i (hi : i < e.getAppArgs.size),
      Supported known Γ (e.getAppArgs[i]) ∧ ∃ ve, TrExprS env Us Δ (e.getAppArgs[i]) ve := by
  obtain ⟨ve, hve⟩ := hex
  have hveS : TrExprS env Us Δ (e.getAppArgs.toList.foldl Expr.app e.getAppFn) ve := by
    rw [getAppArgs_spine]; exact hve
  obtain ⟨⟨fve, htrfn⟩, hargtr⟩ := trExprS_appSpine_inv _ _ _ hveS
  have hsuppS : Supported known Γ (e.getAppArgs.toList.foldl Expr.app e.getAppFn) := by
    rw [getAppArgs_spine]; exact hsupp
  obtain ⟨hsuppfn, hsuppargs⟩ := supported_foldl_app_inv
    (fun cn us h => hnc cn us (by rw [← getAppFn_idem]; exact h))
    (fun cn us h => hncs cn us (by rw [← getAppFn_idem]; exact h)) hsuppS
  refine ⟨⟨hsuppfn, fve, htrfn⟩, fun i hi => ?_⟩
  have hi' : i < e.getAppArgs.toList.length := by simpa using hi
  constructor
  · have := hsuppargs _ (List.getElem_mem hi')
    simpa using this
  · obtain ⟨ave, hav⟩ := hargtr i hi'
    exact ⟨ave, by simpa using hav⟩

/-- Constructor-spine facts: for a supported, translatable term whose head is a
registered constructor, the arity bound, `casesOns`/`Nat`-freshness, and the
per-argument support + translation facts (combining `Supported.ctorApp_inv` with
`trExprS_appSpine_inv`). -/
theorem ctorApp_spine_facts {env : VEnv} {Us : List Name} {known : Name → Prop}
    {Γ : ErasureCtx} {Δ : VLCtx} {e : Expr} {cn : Name} {us : List Level}
    {iid : InductiveId} {cidx : Nat}
    (hsupp : Supported known Γ e) (hex : ∃ ve, TrExprS env Us Δ e ve)
    (hfn : e.getAppFn = .const cn us) (hct : Γ.ctors cn = some (iid, cidx))
    (hncs : Γ.casesOns cn = none) :
    ∃ ar, Γ.ctorArities cn = some ar ∧ ar ≤ e.getAppArgs.size ∧
      Γ.casesOns cn = none ∧ cn ≠ ``Nat.zero ∧ cn ≠ ``Nat.succ ∧
      ∀ i (hi : i < e.getAppArgs.size), Supported known Γ (e.getAppArgs[i]) ∧
        ∃ ve, TrExprS env Us Δ (e.getAppArgs[i]) ve := by
  have hsuppS : Supported known Γ (e.getAppArgs.toList.foldl Expr.app (.const cn us)) := by
    rw [← hfn, getAppArgs_spine]; exact hsupp
  obtain ⟨ar, har, hle, hcs, hz, hs, hsuppargs⟩ :=
    Supported.ctorApp_inv e.getAppArgs.toList.length rfl hsuppS hct hncs
  obtain ⟨ve, hve⟩ := hex
  have hveS : TrExprS env Us Δ (e.getAppArgs.toList.foldl Expr.app e.getAppFn) ve := by
    rw [getAppArgs_spine]; exact hve
  obtain ⟨_, hargtr⟩ := trExprS_appSpine_inv _ _ _ hveS
  refine ⟨ar, har, by simpa using hle, hcs, hz, hs, fun i hi => ?_⟩
  have hi' : i < e.getAppArgs.toList.length := by simpa using hi
  refine ⟨by simpa using hsuppargs i hi', ?_⟩
  obtain ⟨ave, hav⟩ := hargtr i hi'
  exact ⟨ave, by simpa using hav⟩

/-- The per-argument facts a supported, translatable `casesOn` spine supplies.
Position-dependent (see `CasesSpineData`): the `dp` dropped prefix arguments carry
no obligation, while the discriminant, the minors and the over-application tail
each carry their own. -/
def CasesSpineFacts (env : VEnv) (Us : List Name) (known : Name → Prop) (Γ : ErasureCtx)
    (Δ : VLCtx) (dp : Nat) (nfs : List Nat) (args : Array Expr) : Prop :=
  (∀ (h : dp < args.size),
      Supported known Γ (args[dp]) ∧ ∃ ve, TrExprS env Us Δ (args[dp]) ve) ∧
  (∀ j (hj : j < nfs.length) (h : dp + 1 + j < args.size),
      IsLamTelescope (nfs[j]'hj) (args[dp + 1 + j]) ∧
      Supported known Γ (args[dp + 1 + j]) ∧
      ∃ ve, TrExprS env Us Δ (args[dp + 1 + j]) ve) ∧
  (∀ i (h : i < args.size), dp + 1 + nfs.length ≤ i →
      Supported known Γ (args[i]) ∧ ∃ ve, TrExprS env Us Δ (args[i]) ve)

/-- `casesOn`-spine facts: for a supported, translatable term whose head is a
registered `casesOn`, the saturation bound, the flat-alternative and
`Nat`/`Int`-freshness side conditions, and the position-dependent support +
translation facts (combining `Supported.casesApp_inv` with
`trExprS_appSpine_inv`). Mirrors `ctorApp_spine_facts`. -/
theorem casesApp_spine_facts {env : VEnv} {Us : List Name} {known : Name → Prop}
    {Γ : ErasureCtx} {Δ : VLCtx} {e : Expr} {con : Name} {us : List Level}
    {iid : InductiveId} {np : Nat}
    (hsupp : Supported known Γ e) (hex : ∃ ve, TrExprS env Us Δ e ve)
    (hfn : e.getAppFn = .const con us) (hcs : Γ.casesOns con = some (iid, np)) :
    ∃ dp nfs, Γ.casesDiscrPos con = some dp ∧ Γ.ctorFields iid = some nfs ∧
      con.getPrefix ≠ ``Nat ∧ con.getPrefix ≠ ``Int ∧
      dp + 1 + nfs.length ≤ e.getAppArgs.size ∧
      CasesSpineFacts env Us known Γ Δ dp nfs e.getAppArgs := by
  have hsuppS : Supported known Γ (e.getAppArgs.toList.foldl Expr.app (.const con us)) := by
    rw [← hfn, getAppArgs_spine]; exact hsupp
  obtain ⟨dp, nfs, hdp, hnfs, hle, hnat, hint, hd, hlam, hsuppargs⟩ :=
    Supported.casesApp_inv e.getAppArgs.toList.length rfl hsuppS hcs
  obtain ⟨ve, hve⟩ := hex
  have hveS : TrExprS env Us Δ (e.getAppArgs.toList.foldl Expr.app e.getAppFn) ve := by
    rw [getAppArgs_spine]; exact hve
  obtain ⟨_, hargtr⟩ := trExprS_appSpine_inv _ _ _ hveS
  refine ⟨dp, nfs, hdp, hnfs, hnat, hint, by simpa using hle, ?_, ?_, ?_⟩
  · intro h
    have h' : dp < e.getAppArgs.toList.length := by simpa using h
    refine ⟨by simpa using hd h', ?_⟩
    obtain ⟨ave, hav⟩ := hargtr dp h'
    exact ⟨ave, by simpa using hav⟩
  · intro j hj h
    have h' : dp + 1 + j < e.getAppArgs.toList.length := by simpa using h
    refine ⟨by simpa using hlam j hj h', by simpa using hsuppargs _ h' (by omega), ?_⟩
    obtain ⟨ave, hav⟩ := hargtr (dp + 1 + j) h'
    exact ⟨ave, by simpa using hav⟩
  · intro i h hile
    have h' : i < e.getAppArgs.toList.length := by simpa using h
    refine ⟨by simpa using hsuppargs i h' (by omega), ?_⟩
    obtain ⟨ave, hav⟩ := hargtr i h'
    exact ⟨ave, by simpa using hav⟩

/-! ### Arithmetic of the `visitCases` loops

`visitCases` iterates over `casesInfo.altsRange.toArray` (a `Std.Rco` range) and,
for the over-application tail, over `Std.Slice.toArray (args.toSubarray arity)`.
Neither normalises by `simp`, so their length/indexing facts are packaged here. -/

/-- The alternatives range has one entry per alternative. -/
theorem rco_toArray_size (lo hi : Nat) : (Std.Rco.mk lo hi).toArray.size = hi - lo := by
  rw [Std.Rco.size_toArray]; exact Nat.size_rco ..

/-- …and its `j`-th entry is the `j`-th argument position after `lo`. -/
theorem rco_toArray_getElem (lo hi j : Nat) (h : j < (Std.Rco.mk lo hi).toArray.size) :
    (Std.Rco.mk lo hi).toArray[j] = lo + j := by
  rw [Std.Rco.getElem_toArray_eq]; simp

/-- The over-application tail slice is the argument list minus its first `k`
entries. (`Std.Slice.toArray (a.toSubarray k)` does not normalise by `simp`: it
leaves a `min k a.size` behind, which the case split here discharges.) -/
theorem slice_toArray_toList_drop {α} (a : Array α) (k : Nat) :
    (Std.Slice.toArray (a.toSubarray k)).toList = a.toList.drop k := by
  rw [← Subarray.toArray_toList]
  simp only [Subarray.toList_eq]
  simp
  rcases Nat.le_total k a.size with h | h
  · rw [Nat.min_eq_left h, List.take_of_length_le (by simp)]
  · rw [Nat.min_eq_right h, List.drop_eq_nil_of_le (by simp),
      List.drop_eq_nil_of_le (by simp; omega)]
    simp

/-- The alternatives stream starts at the beginning of `altNumParams`. -/
theorem toStream_array_array {α} (a : Array α) : (Std.toStream a).array = a := by
  show (a.toSubarray).array = a
  simp [Array.toSubarray]; rfl

theorem toStream_array_start {α} (a : Array α) : (Std.toStream a).start = 0 := by
  show (a.toSubarray).start = 0
  simp [Array.toSubarray]; rfl

theorem toStream_array_stop {α} (a : Array α) : (Std.toStream a).stop = a.size := by
  show (a.toSubarray).stop = a.size
  simp [Array.toSubarray]; rfl

/-- What a successful `Std.Stream.next?` on a `Subarray` tells us: the cursor was
in range, the produced element is the one under it, and the successor state is the
same array with the cursor advanced by one. -/
theorem subarray_next?_facts {α} (sa : Subarray α) (v : α) (sa' : Subarray α)
    (h : Std.Stream.next? sa = some (v, sa')) :
    ∃ hlt : sa.start < sa.stop,
      v = sa.array[sa.start]'(Nat.lt_of_lt_of_le hlt sa.stop_le_array_size) ∧
      sa'.array = sa.array ∧ sa'.start = sa.start + 1 ∧ sa'.stop = sa.stop := by
  replace h : (if _hh : sa.start < sa.stop then _ else _) = _ := h
  split at h
  · next hlt => cases h; exact ⟨hlt, rfl, rfl, rfl, rfl⟩
  · exact nomatch h

/-- …and an in-range cursor never reports exhaustion (this is what refutes the
`ForInStep.done` early-exit arm of `visitCases`' parallel alternatives loop). -/
theorem subarray_next?_ne_none {α} (sa : Subarray α) (h : sa.start < sa.stop) :
    Std.Stream.next? sa ≠ none := by
  show (if _hh : sa.start < sa.stop then _ else _) ≠ _
  rw [dif_pos h]
  simp

/-- **The machine-`Nat`/`Int` arms of `visitCases` are dead** on the supported
fragment. `visitCases` dispatches on `(casesInfo.declName.getPrefix,
config.nat)`; `Supported.casesApp` requires the prefix to be neither `Nat` nor
`Int`, which selects the general arm *purely* — no assumption needed, exactly as
`cn ≠ Nat.zero/succ` does for `visitConstructor`.

Stated against the elaborator-generated matcher `Erasure.visitCases.match_7`
(name-pattern matchers compile to `Name.rec` + `String` `dite`s, so neither
`split` nor `simp` reduces them under a partial application; the case analysis
here does it by hand). If the shipping `visitCases` match is edited, this
matcher's index moves — the failure mode is a build error, not unsoundness. -/
theorem visitCases_match_default (nm : Name) (cn : Erasure.Config.Nat)
    (hnat : nm ≠ ``Nat) (hint : nm ≠ ``Int)
    (A B : Unit → EraseM LBTerm) (G : Name → Erasure.Config.Nat → EraseM LBTerm) :
    Erasure.visitCases.match_7 (motive := fun _ _ => EraseM LBTerm) nm cn A B G = G nm cn := by
  unfold Erasure.visitCases.match_7
  cases nm with
  | anonymous => rfl
  | num p n => rfl
  | str p str =>
    cases p with
    | anonymous =>
      show (dite (str = "Nat") _ _) = _
      rw [dif_neg (show ¬ str = "Nat" from fun h => hnat (by subst h; rfl))]
      show (dite (str = "Int") _ _) = _
      rw [dif_neg (show ¬ str = "Int" from fun h => hint (by subst h; rfl))]
    | num p2 n2 => rfl
    | str p2 s2 => rfl

/-- Split a list into the `casesOn` spine shape `pre ++ discr :: minors ++ extra`
that `Erases.cases` (plus `Erases.app` for the tail) consumes. -/
theorem list_split_cases {α} (l : List α) (dp n : Nat)
    (h : dp + 1 + n ≤ l.length) :
    l = l.take dp ++ (l[dp]'(by omega) :: (l.drop (dp + 1)).take n) ++ l.drop (dp + 1 + n) := by
  have h2 : l.drop dp = l[dp]'(by omega) :: l.drop (dp + 1) :=
    List.drop_eq_getElem_cons (by omega)
  have h4 : (l.drop (dp + 1)).drop n = l.drop (dp + 1 + n) := by
    rw [List.drop_drop]
  calc l = l.take dp ++ l.drop dp := (List.take_append_drop dp l).symm
    _ = l.take dp ++ (l[dp]'(by omega) :: l.drop (dp + 1)) := by rw [h2]
    _ = l.take dp ++ (l[dp]'(by omega) :: (l.drop (dp + 1)).take n) ++ l.drop (dp + 1 + n) := by
        rw [← h4, List.append_assoc, List.cons_append, List.take_append_drop]

/-- `fvar_to_name` is pure: it always succeeds, does not touch state or world,
and returns `nameToBinder` of the found declaration's `userName`. -/
theorem run_fvar_to_name (x : FVarId) (nm : Name) (s : ErasureState)
    (ctx : ErasureContext) (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld)
    (hd : (ctx.lctx.fvarIdToDecl.find! x).userName = nm) :
    Erasure.fvar_to_name x s ctx cctx ref w = .ok (nameToBinder nm, s) w := by
  unfold Erasure.fvar_to_name
  rw [run_bind, run_read]
  simp only []
  rw [hd]
  unfold nameToBinder
  simp only []
  split <;> rfl

/-- A **trivial argmask** filters nothing: the list-level computation behind
`filter_replicate_keep`. -/
theorem filterMap_zip_replicate {α : Type} (n : Nat) : ∀ (l : List α), l.length = n →
    ((List.replicate n Erasure.ConstructorArgRelevance.keep).zip l).filterMap
      (fun x => match x.1 with
        | Erasure.ConstructorArgRelevance.erase => none
        | Erasure.ConstructorArgRelevance.keep => some x.2) = l := by
  induction n with
  | zero => intro l hl; rw [List.eq_nil_of_length_eq_zero hl]; rfl
  | succ n ih =>
    intro l hl
    match l with
    | a :: as =>
      simp only [List.replicate, List.zip_cons_cons, List.filterMap_cons]
      rw [ih as (by simpa using hl)]

/-- A trivial argmask of the right width is the identity on the field list. This is
what makes `Erasure.visitAlt`'s `filter argmask fvarids.toArray` disappear; the
argmask's triviality comes from `CasesBridgeHyps.casesreg_run`
(`remove_irrel_constr_args := false`, the shipping default). The model does not
represent argmask filtering at all (see `Erases.cases`' docstring), so this is
where that restriction is cashed in. -/
theorem filter_replicate_keep {α : Type} (n : Nat) (arr : Array α) (h : arr.size = n) :
    Erasure.filter (Array.replicate n Erasure.ConstructorArgRelevance.keep) arr = arr := by
  unfold Erasure.filter
  apply Array.toList_inj.mp
  rw [Array.toList_filterMap, Array.toList_zip, Array.toList_replicate]
  exact filterMap_zip_replicate n arr.toList (by rw [Array.length_toList]; exact h)

/-- `mkAlt`'s name pass is pure: it reads each binder's `userName` out of the
*current* local context. -/
theorem run_mapM_fvar_to_name_loop (xs : List FVarId) : ∀ (acc : List BinderName)
    (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld),
    List.mapM.loop Erasure.fvar_to_name xs acc s ctx cctx ref w
      = .ok (acc.reverse ++
          xs.map (fun x => nameToBinder ((ctx.lctx.fvarIdToDecl.find! x).userName)), s) w := by
  induction xs with
  | nil => intro acc s ctx cctx ref w; unfold List.mapM.loop; simp [run_pure]
  | cons x xs ih =>
    intro acc s ctx cctx ref w
    unfold List.mapM.loop
    rw [run_bind, run_fvar_to_name x _ s ctx cctx ref w rfl]
    simp only []
    rw [ih]
    simp

theorem run_mapM_fvar_to_name (xs : List FVarId) (s : ErasureState) (ctx : ErasureContext)
    (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) :
    (xs.mapM Erasure.fvar_to_name : EraseM (List BinderName)) s ctx cctx ref w
      = .ok (xs.map (fun x => nameToBinder ((ctx.lctx.fvarIdToDecl.find! x).userName)), s) w := by
  unfold List.mapM
  rw [run_mapM_fvar_to_name_loop]
  simp

/-- …and its `toBvar` pass is the pure `closeAlt` fold. -/
theorem run_forIn_toBvar (L : List (FVarId × Nat)) : ∀ (t : LBTerm) (s : ErasureState)
    (ctx : ErasureContext) (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld),
    (forIn L t (fun x b => pure (ForInStep.yield (toBvar x.1 x.2 b))) : EraseM LBTerm)
        s ctx cctx ref w
      = .ok (L.foldl (fun b p => toBvar p.1 p.2 b) t, s) w := by
  induction L with
  | nil => intro t s ctx cctx ref w; rw [List.forIn_nil, run_pure]; rfl
  | cons p ps ih =>
    intro t s ctx cctx ref w
    rw [List.forIn_cons, run_bind, run_pure]
    simp only []
    rw [ih]
    rfl

/-- **`mkAlt` is pure**: state- and world-preserving, and computed by `closeAlt`
plus the binders' `userName`s at the context it runs in. -/
theorem run_mkAlt (xs : List FVarId) (t : LBTerm) (s : ErasureState) (ctx : ErasureContext)
    (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) :
    Erasure.mkAlt xs t s ctx cctx ref w
      = .ok ((xs.map (fun x => nameToBinder ((ctx.lctx.fvarIdToDecl.find! x).userName)),
              closeAlt xs t), s) w := by
  unfold Erasure.mkAlt
  rw [run_bind, run_mapM_fvar_to_name]
  simp only []
  rw [run_bind, run_forIn_toBvar, closeAlt_foldl]
  rfl

/-! ## The trust bundle and the induction invariant -/

/-- Trust bundle: Hoare-style hypotheses about the opaque runtime primitives,
relative to a ghost world-measure `gw` (the name-generator state as a function
of the world token). These are the bridge's honest assumptions, playing the
role `OracleSound` played for `eraseCore`:

* `orc_run`: a successful run of the erasability oracle (`isErasable
  ctx.lparams e`, now threading the declaration's universe parameters) advances
  the generator monotonically, and a `true` verdict is *sound* — the term is
  `Erasable` in any ambient `MLCtx` `m` whose `m.lctx` is the local context the
  oracle ran in (phrased over `MLCtx` rather than a bare `TrLCtx` so the kernel
  path can be discharged by `kernel_isErasable_sound`, `OracleDischarge.lean`).
  (State-preservation is not assumed: it is derivable via `run_liftMetaM_state`.)

  **The scope guard is a prefix since slice Γ-U2**, and it is the one place that slice
  costs anything. The soundness clause fires under `ctx.lparams <+: Us` where it used to
  demand `ctx.lparams = Us`, because `BridgeInv.lparams` now carries the prefix and a
  dependency's sub-run reads its own `ci.levelParams`. That is a *strictly larger* trust
  item, and unlike the rest of Γ-U2 it is not served by the U1 kit: the clause is
  contravariant in `TrExprS` and covariant in `Erasable`, so neither
  `TrExprS.prefix_weaken` (which goes up) nor `Erasable.uvars_mono` (which also goes up)
  can move it — a hypothesis at the ambient `Us` would have to be *strengthened* to the
  run's own scope, and that direction is false in general. What it costs is measured
  where it is paid: `OracleDischarge`'s kernel branch discharges the clause only at
  `ctx.lparams = Us`, and the strict-prefix case falls to the assumed-sound fallback. At
  `Us = []` — every capstone in this development — `<+:` *is* `=`, so nothing moved.
* `fresh_run`: `mkFreshFVarId` returns a
  previously-unreserved id (both in the ghost measure `gw` and in the kernel's
  fixed `kernelNGen` — the latter because `CoreM`'s `mkFreshFVarId` mints
  `_uniq`-named ids, never `_kernel_fresh`-prefixed ones), reserves it, and
  advances the generator. (State-preservation is not assumed: it is the theorem
  `Erasure.run_mkFreshFVarId_state`.)
* `cases_run`/`ctor_run`: the `CoreM` classifiers agree with the static `Γ`
  on *negative* answers — a name `Γ` does not register as a `casesOn`
  (resp. constructor) is not classified as one — and advance the generator
  monotonically. (State-preservation is derivable via `run_liftCoreM_state`.)

Because these quantify over opaque primitives, their global satisfiability is
not in-logic decidable; this is the documented trust boundary of the bridge. -/
structure BridgeHyps (env : VEnv) (Us : List Name) (Γ : ErasureCtx)
    (gw : Void IO.RealWorld → NameGenerator) : Prop where
  orc_run : ∀ (e : Expr) (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (b : Bool)
    (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    Erasure.liftMetaM (Erasure.isErasable ctx.lparams e) s ctx cctx ref w = .ok (b, s₁) w₁ →
    gw w ≤ gw w₁ ∧
    (b = true → ctx.lparams <+: Us → ∀ (m : MLCtx) (ve : VExpr), m.WF env Us → m.lctx = ctx.lctx →
      (∀ fv ∈ m.vlctx.fvars, kernelNGen.Reserves fv) →
      TrExprS env Us m.vlctx e ve → Erasable env Us.length m.vlctx.toCtx ve)
  fresh_run : ∀ (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (x : FVarId)
    (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    (mkFreshFVarId : EraseM FVarId) s ctx cctx ref w = .ok (x, s₁) w₁ →
    ¬ (gw w).Reserves x ∧ (gw w₁).Reserves x ∧ gw w ≤ gw w₁ ∧
    kernelNGen.Reserves x
  cases_run : ∀ (n : Name) (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) (r : Option CasesInfo) (w₁ : Void IO.RealWorld),
    getCasesInfo? n cctx ref w = .ok r w₁ →
    gw w ≤ gw w₁ ∧ (Γ.casesOns n = none → r = none)
  ctor_run : ∀ (n : Name) (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) (r : Option Nat) (w₁ : Void IO.RealWorld),
    Lean.Compiler.LCNF.getCtorArity? n cctx ref w = .ok r w₁ →
    gw w ≤ gw w₁ ∧ (Γ.ctors n = none → r = none)

/-- The bridge invariant carried through the induction.

The old `trlctx : TrLCtx env Us ctx.lctx Δ` field is *replaced* by the stronger
`mlc` (an ambient `MLCtx` `m` witnessing that correspondence *and* recording
`m.lctx`/`m.vlctx`), from which `trlctx` is re-derived below (`BridgeInv.trlctx`),
so the ~20 downstream `hinv.trlctx` use-sites keep working. Two further fields
carry what the oracle discharge needs (`OracleDischarge.lean`): `lparams` pins
`ctx.lparams <+: Us` (an equation until slice Γ-U2), and `kfresh` says every `Δ`-fvar is reserved by the kernel's
fixed `kernelNGen` (so `kernel_isErasable_sound`'s freshness premise holds).

## The constant registry, after cold-start S2

The single field `consts : ∀ n, known n → s.constants.get? n = some (Γ.constants n)`
split into three, because the state is no longer constant along the induction and that
field was *not* preserved by state growth:

* `knames` — `Γ` files every constant under its canonical kername. The design's
  `hknames`: a side condition on the *parameter* `Γ`, satisfied by every concrete `Γ`
  in the repo (`ΓFOd`/`ΓFOι` set `constants := toKername`) and constructed in the
  guards below. It is what makes the registry's canonicity (which the run establishes,
  `Erasure.CanonicalConstants`) equal to `Γ`-agreement.
* `consts` — **soundness**: every *registered* kername agrees with `Γ`. This is
  `ColdStartShape.RegInvShape.kn`, and it is what survives state growth
  (`BridgeInv.mono_state`, via `Erasure.RunConcl.canon`).
## δ-inclusion, slice D4a: the field `known_dom` is gone

There used to be a third field here, the residue of the old `consts`' **completeness**
direction weakened to the domain:

```lean
  known_dom : ∀ n, known n → (s.constants.get? n).isSome
```

It said a `known` constant is *already registered*. That is a **state** fact about a
fragment a cold run has not reached yet, so at the entry configuration it was not merely
strong but false for every non-empty fragment (`old_known_dom_cold_refuted` below keeps
that on the record) — which is what forced every cold-start capstone to `known = ⊥`, and
hence made the cold-start fragment δ-free, since `Supported.const` needs `known n`.

The invariant therefore no longer mentions `known` at all: `known` survives as a
parameter, documenting that this is the *state-side* half of a two-part contract whose
*scope-side* half is `DeltaHyps` (`DeltaHyps.lean`) — fragment δ-closure, decl-fetch /
`Esrc` agreement, prepared dependency bodies `Supported` and translatable, `axiom_free`,
and the generator bookkeeping for the `visitMutual`-only primitives. `bridgeInv_cold_known`
below is the payoff: the invariant is now satisfiable at the empty state at a *non-empty*
fragment.

The field's job was to force `get_constant_kername`'s hit branch (motive 5). Its deletion
was **not separable** from giving `visitMutual`'s motive a registration conclusion: with
`known_dom` gone, motive 5's *miss* branch returns `s'.constants[n]!`, which is `default`
— not `Γ.constants n` — unless the intervening `visitMutual n` registered `n`
(`DeltaHyps.constants_get!_unregistered_ne` proves the inequality on real data). Inside
this induction the only handle on that call is the abstract `_vMut` and its motive, so the
field's death and motive 6's content are one change (this slice), not two. -/
structure BridgeInv (env : VEnv) (Us : List Name) (known : Name → Prop)
    (Γ : ErasureCtx) (cfg₀ : ErasureConfig) (gen : NameGenerator)
    (ctx : Erasure.ErasureContext) (s : Erasure.ErasureState) (Δ : VLCtx) : Prop where
  mlc : ∃ m : MLCtx, m.WF env Us ∧ m.lctx = ctx.lctx ∧ m.vlctx = Δ
  /-- **The reader's level scope is a prefix of the ambient one** (slice Γ-U2; it read
  `ctx.lparams = Us` until then).

  The ambient `Us` is a *parameter* of the bridge theorem and the conclusion `Erases env
  Us …` is stated at it; the reader's `lparams` is what the run actually installs, and
  `visitMutual`'s two `withReader`s move it to a dependency's / a sibling's own
  `ci.levelParams`. Pinning the two equal is what made
  `DeltaHyps.decl_run`/`BlockHyps.block_lparams` demand universe monomorphism of the whole
  dependency cone. A *prefix* is all the run needs: along `ctx.lparams <+: Us` no level
  index moves (`ErasesLevels.VLevel.ofLevel_prefix`), so every fact the sub-run produces
  at its own scope transports to `Us` on the nose — `TrExprS.prefix_weaken`,
  `Erases.prefix_weaken`, `Erasable.uvars_mono`.

  At `Us = []` this **is** the old equation (`List.prefix_nil`), so no existing
  instantiation weakened and nothing became vacuous; at `Us ≠ []` it admits a
  prefix-scoped dependency of a polymorphic subject. It does *not* admit a polymorphic
  dependency of a closed subject — `[u] <+: []` is false — which is the instantiation
  story Γ-U3/Γ-U4 owe. -/
  lparams : ctx.lparams <+: Us
  /-- **The run's config is the bridge's config** (recursion wall, slice Γ-W3.6a).

  The reader's `config` is a **run invariant**: of the five `withReader` sites in the
  shipping eraser (`Erasure.withLocalDecl`/`withLocalDef`, `visitMutual`'s non-recursive
  exit, its block entry and its per-sibling loop) not one touches `config`,
  `{ … with config := … }` occurs nowhere in the eraser, and the only reader built from
  scratch is `Erasure.run`'s own `{ config }`. The *motive*, however, quantifies the
  reader, so without this field the induction is stated at readers whose `config` is
  free — and `config` is what selects branches (`csimp` at `prepare_erasure`, `extern`
  and `remove_irrel_constr_args` and `nat` inside the term path). A premise about what a
  sub-run *builds* is then refutable by two configs, which is what kept step 6's
  recursive branch closed until this slice (`ColdStart`'s residue-1 row).

  Pinning it costs nothing: every transport below re-emits it unchanged
  (`mkLocalDecl`/`mkLetDecl` move `lctx` only, `mono`/`mono_state` keep the reader, and
  `withFixvars` already carried `hcfg : ctx'.config = ctx.config` as a premise, supplied
  by `rfl` at both call sites), and every construction site is a literal reader, so the
  field is `rfl` there. `natcfg` below becomes a corollary of it at any `cfg₀` whose
  `nat` is pinned Γ-side, and is kept because nothing yet relates `Γ.natPeano` to
  `cfg₀`. -/
  cfg : ctx.config = cfg₀
  /-- **The literal fragment's config pin** (Nat-literals wall, L3). `Supported` is purely
  syntactic in `(known, Γ)` and cannot see the reader's `ctx.config`; `Supported.natLit`
  therefore states peano-mode as the `Γ`-side flag `Γ.natPeano`, and *this* field is where
  the flag is cashed in against the run whose branch selection actually depends on it
  (`visitLiteral` matches on `(← read).config.nat`).

  Vacuous at `Γ.natPeano = false` — which is every machine-mode instance and every `Γ`
  that does not opt in — so the machine-mode bridge theorem stays exactly as strong as it
  was. Preservation is free: `mono`, `mono_state`, `mkLocalDecl` and `mkLetDecl` change
  only `gen`, `s` and `ctx.lctx`, never `ctx.config`. -/
  natcfg : Γ.natPeano = true → ctx.config.nat = .peano
  kfresh : ∀ fv ∈ Δ.fvars, kernelNGen.Reserves fv
  /-- **Fixvar agreement** (recursion wall, W3.1). The run's block-local map — the
  reader's `ErasureContext.fixvars`, installed by `visitMutual`'s `withReader` while the
  block is being erased — and `Γ.fixvars` name the same fvar for the same sibling. This
  *replaces* the pre-W3.1 exclusion `ctx.fixvars = none`, which is now the special case
  `Γ.fixvars = fun _ => none` (still what every top-level entry point supplies). It is
  exactly parallel to `consts`, and it is what turns `visitConst`'s fixvar branch — dead
  before — into an `Erases.fixvar` derivation. -/
  fixvars : ∀ (nm : Name) (x : FVarId),
    ctx.fixvars.bind (fun m => m[nm]?) = some x ↔ Γ.fixvars nm = some x
  /-- **Fixvar freshness**, the run's own discipline: `visitMutual` mints the block's
  fvars *before* `visitExpr` opens any binder, so a fixvar is reserved by the current
  generator and is never a `Δ` entry. The second conjunct discharges `Erases.fixvar`'s
  `hfresh`; the first is what preserves the second across a binder (`mkLocalDecl` /
  `mkLetDecl` extend `Δ` with an id `fresh_run` says the generator does *not* reserve). -/
  fixfresh : ∀ (nm : Name) (x : FVarId), Γ.fixvars nm = some x →
    gen.Reserves x ∧ x ∉ Δ.fvars
  reserved : ∀ fv ∈ Δ.fvars, gen.Reserves fv
  /-- `Γ` files every constant under its canonical kername (the design's `hknames`). -/
  knames : ∀ n : Name, Γ.constants n = toKername n
  /-- Registered kernames agree with `Γ` — SOUNDNESS. -/
  consts : ∀ {n : Name} {k : Kername}, s.constants.get? n = some k → k = Γ.constants n

/-- The `TrLCtx` correspondence, re-derived from the `mlc` witness (the old
`BridgeInv.trlctx` field). Keeps every downstream `hinv.trlctx` use-site valid. -/
theorem BridgeInv.trlctx {env : VEnv} {Us : List Name} {known : Name → Prop}
    {Γ : ErasureCtx} {cfg₀ : ErasureConfig} {gen : NameGenerator} {ctx : ErasureContext}
    {s : ErasureState} {Δ : VLCtx}
    (h : BridgeInv env Us known Γ cfg₀ gen ctx s Δ) : TrLCtx env Us ctx.lctx Δ := by
  obtain ⟨m, mwf, hlctx, hvlctx⟩ := h.mlc
  rw [← hlctx, ← hvlctx]; exact mwf.tr

/-- **The bridge's context is well-formed** — `TrLCtx.wf` on `trlctx`. What
`ErasesUniform.erases_uniform_closed` needs of the context a dependency was erased at. -/
theorem BridgeInv.vlctx_wf {env : VEnv} {Us : List Name} {known : Name → Prop}
    {Γ : ErasureCtx} {cfg₀ : ErasureConfig} {gen : NameGenerator} {ctx : ErasureContext}
    {s : ErasureState} {Δ : VLCtx}
    (h : BridgeInv env Us known Γ cfg₀ gen ctx s Δ) : VLCtx.WF env Us.length Δ :=
  h.trlctx.wf

/-- **The bridge's context has no bvar entries.** Every entry the run conses is
fvar-tagged — `BridgeInv.mkLocalDecl`/`mkLetDecl` cons `(some (x, _), _)` and the
cold-start entry is `[]` — which is `MLCtx.noBV` transported along `mlc`. It is what
turns the context into an `VLCtx.FVLift`-extension of `[]` (`VLCtx.FVLift.from_nil`),
the other half of what context-uniformity needs. -/
theorem BridgeInv.noBV {env : VEnv} {Us : List Name} {known : Name → Prop}
    {Γ : ErasureCtx} {cfg₀ : ErasureConfig} {gen : NameGenerator} {ctx : ErasureContext}
    {s : ErasureState} {Δ : VLCtx}
    (h : BridgeInv env Us known Γ cfg₀ gen ctx s Δ) : Δ.NoBV := by
  obtain ⟨m, -, -, hvlctx⟩ := h.mlc
  rw [← hvlctx]; exact m.noBV

/-- The invariant is monotone in the generator (fvar reservations survive
generator advancement). The `MLCtx`/`lparams`/`kfresh` data is generator-free. -/
theorem BridgeInv.mono {env : VEnv} {Us : List Name} {known : Name → Prop}
    {Γ : ErasureCtx} {cfg₀ : ErasureConfig} {gen gen' : NameGenerator} {ctx : ErasureContext}
    {s : ErasureState} {Δ : VLCtx}
    (h : BridgeInv env Us known Γ cfg₀ gen ctx s Δ) (hle : gen ≤ gen') :
    BridgeInv env Us known Γ cfg₀ gen' ctx s Δ where
  mlc := h.mlc
  lparams := h.lparams
  cfg := h.cfg
  natcfg := h.natcfg
  kfresh := h.kfresh
  fixvars := h.fixvars
  fixfresh := fun nm x hx => ⟨(h.fixfresh nm x hx).1.mono hle, (h.fixfresh nm x hx).2⟩
  reserved := fun fv hfv => (h.reserved fv hfv).mono hle
  knames := h.knames
  consts := h.consts

/-- **The invariant is monotone in the *state*** — the cold-start companion of
`BridgeInv.mono`. Only `consts` mentions `s`, and it is re-established from
`Erasure.RunConcl.canon` (canonicity of the registry survives every registration write)
together with `knames`. (Before slice D4a there was a second state field, `known_dom`,
carried across by `Erasure.StateLe`'s domain monotonicity; see the structure's docstring
for why it had to go.)

This is what makes the widened motive conclusion usable: after a sub-run has grown the
state, the invariant travels to the larger state and the next sub-run's IH applies. -/
theorem BridgeInv.mono_state {env : VEnv} {Us : List Name} {known : Name → Prop}
    {Γ : ErasureCtx} {cfg₀ : ErasureConfig} {gen : NameGenerator} {ctx : ErasureContext}
    {s s' : ErasureState} {Δ : VLCtx}
    (h : BridgeInv env Us known Γ cfg₀ gen ctx s Δ) (hrc : Erasure.RunConcl s s') :
    BridgeInv env Us known Γ cfg₀ gen ctx s' Δ where
  mlc := h.mlc
  lparams := h.lparams
  cfg := h.cfg
  natcfg := h.natcfg
  kfresh := h.kfresh
  fixvars := h.fixvars
  fixfresh := h.fixfresh
  reserved := h.reserved
  knames := h.knames
  consts := by
    intro n k hk
    rw [h.knames n]
    exact hrc.canon (fun {m} {k'} hm => (h.consts hm).trans (h.knames m)) hk

/-- **The bridge invariant enters a mutual block** (slice δ-D8). `visitMutual`'s recursive
exit erases each sibling body under `withReader (… fixvars := some (nms.zip ids) …)`; this
is the invariant at that reader, against the block-local `Γ.withFixvars fv`.

Seven of the ten fields are literally `Γ`'s — `withFixvars` moves *only* `fixvars`, so
`natPeano`/`constants` are `rfl` — and `mlc`/`lparams`/`kfresh`/`reserved` never mentioned
`Γ` at all. The two fixvar fields become claims about the block's own map: `hagree` is the
reader-vs-`fv` agreement the `withReader` establishes by construction, and `hfresh` is
`BridgeHyps.fresh_run` against `BridgeInv.reserved` — `visitMutual` mints the block's ids
*before* any binder is opened, so a block id is generator-reserved and is not a `Δ` entry.

The `cfg` field (Γ-W3.6a) travels on `hcfg`, which this theorem already demanded for
`natcfg` and which both call sites supply by `rfl`: the exit's two `withReader`s move
`fixvars` and `lparams`, never `config`.

The fragment is free to change (`known'` is unconstrained): `BridgeInv` has not mentioned
`known` since slice D4a retired `known_dom`, which is exactly what lets the block's inner
runs be taken at `known' = ⊥`.

The callee's reader is left abstract and pinned componentwise (`hlctx`/`hlp`/`hcfg`/`hfvm`)
rather than written as `{ ctx with … }`, because `visitMutual` installs it in *two* steps —
the block's `withReader … fixvars` and then the per-sibling `withReader … lparams`. -/
theorem BridgeInv.withFixvars {env : VEnv} {Us : List Name} {known known' : Name → Prop}
    {Γ : ErasureCtx} {cfg₀ : ErasureConfig} {gen : NameGenerator} {ctx ctx' : ErasureContext}
    {s : ErasureState} {Δ : VLCtx} {fv : Name → Option FVarId}
    {fvmap : Std.HashMap Name FVarId}
    (h : BridgeInv env Us known Γ cfg₀ gen ctx s Δ)
    (hlctx : ctx'.lctx = ctx.lctx) (hlp : ctx'.lparams <+: Us)
    (hcfg : ctx'.config = ctx.config) (hfvm : ctx'.fixvars = some fvmap)
    (hagree : ∀ (nm : Name) (x : FVarId), fvmap[nm]? = some x ↔ fv nm = some x)
    (hfresh : ∀ (nm : Name) (x : FVarId), fv nm = some x → gen.Reserves x ∧ x ∉ Δ.fvars) :
    BridgeInv env Us known' (Γ.withFixvars fv) cfg₀ gen ctx' s Δ where
  mlc := by
    obtain ⟨m, mwf, hml, hmv⟩ := h.mlc
    exact ⟨m, mwf, by rw [hlctx]; exact hml, hmv⟩
  lparams := hlp
  cfg := hcfg.trans h.cfg
  natcfg := by intro hp; rw [hcfg]; exact h.natcfg (by simpa using hp)
  kfresh := h.kfresh
  fixvars := by
    intro nm x
    rw [hfvm]
    show (some fvmap).bind (fun m => m[nm]?) = some x ↔ _
    simpa using hagree nm x
  fixfresh := by intro nm x hx; exact hfresh nm x (by simpa using hx)
  reserved := h.reserved
  knames := h.knames
  consts := h.consts

/-! ### The four trust bundles at a block-local `Γ`

`ErasureCtx.withFixvars` moves exactly one field, and none of `BridgeHyps`,
`DataBridgeHyps`, `CasesBridgeHyps`, `ProjBridgeHyps` reads it: they speak about
`Γ.ctors`, `Γ.casesOns`, `Γ.ctorArities`, `Γ.casesDiscrPos`, `Γ.ctorFields` and
`Γ.projs`, every one of which is `rfl` at `Γ.withFixvars fv`. So each transports
field-by-field, with no proof obligation at all — which is the concrete form of the
design's claim that the bundles are `rfl`-invariant under the block instantiation. -/

theorem BridgeHyps.withFixvars {env : VEnv} {Us : List Name} {Γ : ErasureCtx}
    {gw : Void IO.RealWorld → NameGenerator} (H : BridgeHyps env Us Γ gw)
    (fv : Name → Option FVarId) : BridgeHyps env Us (Γ.withFixvars fv) gw where
  orc_run := H.orc_run
  fresh_run := H.fresh_run
  cases_run := H.cases_run
  ctor_run := H.ctor_run

theorem DataBridgeHyps.withFixvars {Γ : ErasureCtx}
    {gw : Void IO.RealWorld → NameGenerator} (HD : DataBridgeHyps Γ gw)
    (fv : Name → Option FVarId) : DataBridgeHyps (Γ.withFixvars fv) gw where
  ctor_run := HD.ctor_run
  ctorinfo_run := HD.ctorinfo_run
  indinfo_run := HD.indinfo_run
  reg_run := HD.reg_run
  extern_run := HD.extern_run
  infer_run := HD.infer_run

theorem CasesBridgeHyps.withFixvars {Γ : ErasureCtx}
    {gw : Void IO.RealWorld → NameGenerator} (C : CasesBridgeHyps Γ gw)
    (fv : Name → Option FVarId) : CasesBridgeHyps (Γ.withFixvars fv) gw where
  cases_run_pos := C.cases_run_pos
  casesind_run := C.casesind_run
  casesreg_run := C.casesreg_run
  infer_lam_run := C.infer_lam_run

theorem ProjBridgeHyps.withFixvars {Γ : ErasureCtx}
    {gw : Void IO.RealWorld → NameGenerator} (P : ProjBridgeHyps Γ gw)
    (fv : Name → Option FVarId) : ProjBridgeHyps (Γ.withFixvars fv) gw where
  projind_run := P.projind_run
  projreg_run := P.projreg_run

/-! ### …and at a motive-local `Γ`

Each step of the induction below holds its own `Γ` together with the coherence equation
`hΓ : Γ = Γ₀.withFixvars Γ.fixvars` (slice Γ-W1), and re-derives its bundles from the
ambient ones in one line. The four transports are the ones above, composed with the
equation; there is still no proof obligation. -/

/-- The two registration projections a step has to read *across* the coherence equation:
`Γ` and `Γ₀` differ only in `fixvars`, so everything else is literally shared. Stated as
lemmas rather than left to `simp` because `hΓ`'s right-hand side mentions `Γ`, so it is not
a usable rewrite rule — `rw` (one pass) is, `simp` (to fixpoint) is not. -/
theorem ErasureCtx.coh_constants {Γ Γ₀ : ErasureCtx}
    (hΓ : Γ = Γ₀.withFixvars Γ.fixvars) : Γ.constants = Γ₀.constants := by
  rw [hΓ]; rfl

theorem ErasureCtx.coh_natPeano {Γ Γ₀ : ErasureCtx}
    (hΓ : Γ = Γ₀.withFixvars Γ.fixvars) : Γ.natPeano = Γ₀.natPeano := by
  rw [hΓ]; rfl

/-- **A step's own `Γ` and the ambient `Γ₀` install the same block** (recursion wall,
slice Γ-W3): `withFixvars` is idempotent in its argument, so a block entered from a
motive-local `Γ` lands at exactly the context the ambient premises speak about. This is
what lets the recursive exit's per-sibling invariant, rebuilt by `BridgeInv.withFixvars`
from the step's `Γ`, be handed to the erasure IH at `Γ₀.withFixvars fv` — the
instantiation guard (i''') exhibits. -/
theorem ErasureCtx.coh_withFixvars {Γ Γ₀ : ErasureCtx}
    (hΓ : Γ = Γ₀.withFixvars Γ.fixvars) (fv : Name → Option FVarId) :
    Γ.withFixvars fv = Γ₀.withFixvars fv := by
  rw [hΓ]; rfl

theorem BridgeHyps.of_coh {env : VEnv} {Us : List Name} {Γ Γ₀ : ErasureCtx}
    {gw : Void IO.RealWorld → NameGenerator} (H : BridgeHyps env Us Γ₀ gw)
    (hΓ : Γ = Γ₀.withFixvars Γ.fixvars) : BridgeHyps env Us Γ gw := by
  rw [hΓ]; exact H.withFixvars _

theorem DataBridgeHyps.of_coh {Γ Γ₀ : ErasureCtx}
    {gw : Void IO.RealWorld → NameGenerator} (HD : DataBridgeHyps Γ₀ gw)
    (hΓ : Γ = Γ₀.withFixvars Γ.fixvars) : DataBridgeHyps Γ gw := by
  rw [hΓ]; exact HD.withFixvars _

theorem CasesBridgeHyps.of_coh {Γ Γ₀ : ErasureCtx}
    {gw : Void IO.RealWorld → NameGenerator} (C : CasesBridgeHyps Γ₀ gw)
    (hΓ : Γ = Γ₀.withFixvars Γ.fixvars) : CasesBridgeHyps Γ gw := by
  rw [hΓ]; exact C.withFixvars _

theorem ProjBridgeHyps.of_coh {Γ Γ₀ : ErasureCtx}
    {gw : Void IO.RealWorld → NameGenerator} (P : ProjBridgeHyps Γ₀ gw)
    (hΓ : Γ = Γ₀.withFixvars Γ.fixvars) : ProjBridgeHyps Γ gw := by
  rw [hΓ]; exact P.withFixvars _

/-- Extend the invariant across `Erasure.withLocalDecl`'s context extension
(the `visitLambda` case). Needs the fresh fvar `x` reserved both by the target
generator (`hres`) and by the kernel generator (`hkres`, from `fresh_run`). -/
theorem BridgeInv.mkLocalDecl {env : VEnv} {Us : List Name} {known : Name → Prop}
    {Γ : ErasureCtx} {cfg₀ : ErasureConfig} {gen gen' : NameGenerator} {ctx : ErasureContext}
    {s : ErasureState} {Δ : VLCtx} {x : FVarId} {n : Name} {ty : Expr} {ty' : VExpr}
    {bi : BinderInfo}
    (hinv : BridgeInv env Us known Γ cfg₀ gen ctx s Δ)
    (hty : TrExprS env Us Δ ty ty') (hty' : env.IsType Us.length Δ.toCtx ty')
    (hx : x ∉ Δ.fvars) (hnres : ¬ gen.Reserves x)
    (hle : gen ≤ gen') (hres : gen'.Reserves x)
    (hkres : kernelNGen.Reserves x) :
    BridgeInv env Us known Γ cfg₀ gen'
      { ctx with lctx := ctx.lctx.mkLocalDecl x n ty bi } s
      ((some (x, ty.fvarsList), .vlam ty') :: Δ) where
  mlc := by
    obtain ⟨m, mwf, hlctx, hvlctx⟩ := hinv.mlc
    refine ⟨m.vlam x n ty ty' bi, ⟨mwf, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [hlctx]; exact hinv.trlctx.find?_eq_none.mpr hx
    · rw [hvlctx]; exact hty
    · rw [hvlctx]; exact hty'
    · show m.lctx.mkLocalDecl x n ty bi = _; rw [hlctx]
    · show (some (x, ty.fvarsList), VLocalDecl.vlam ty') :: m.vlctx = _; rw [hvlctx]
  lparams := hinv.lparams
  cfg := hinv.cfg
  natcfg := hinv.natcfg
  kfresh := by
    intro fv hfv
    have : fv = x ∨ fv ∈ Δ.fvars := by simpa using hfv
    rcases this with rfl | hfv'
    · exact hkres
    · exact hinv.kfresh fv hfv'
  fixvars := hinv.fixvars
  fixfresh := by
    -- The block's fixvars are reserved by `gen`; the binder's fvar is not (`hnres`), so
    -- the new `Δ` entry cannot be one of them.
    intro nm y hy
    obtain ⟨hres_y, hΔ_y⟩ := hinv.fixfresh nm y hy
    refine ⟨hres_y.mono hle, ?_⟩
    intro hmem
    have : y = x ∨ y ∈ Δ.fvars := by simpa using hmem
    rcases this with rfl | hmem'
    · exact hnres hres_y
    · exact hΔ_y hmem'
  reserved := by
    intro fv hfv
    have : fv = x ∨ fv ∈ Δ.fvars := by simpa using hfv
    rcases this with rfl | hfv'
    · exact hres
    · exact (hinv.reserved fv hfv').mono hle
  knames := hinv.knames
  consts := hinv.consts

/-- Extend the invariant across `Erasure.withLocalDef`'s context extension
(the `visitLet` case). The shipping `withLocalDef` builds the let-decl with the
default `nonDep` (`mkLetDecl x n ty v`), matching `MLCtx.vlet`'s `lctx`. -/
theorem BridgeInv.mkLetDecl {env : VEnv} {Us : List Name} {known : Name → Prop}
    {Γ : ErasureCtx} {cfg₀ : ErasureConfig} {gen gen' : NameGenerator} {ctx : ErasureContext}
    {s : ErasureState} {Δ : VLCtx} {x : FVarId} {n : Name} {ty v : Expr}
    {ty' val' : VExpr}
    (hinv : BridgeInv env Us known Γ cfg₀ gen ctx s Δ)
    (hty : TrExprS env Us Δ ty ty') (hval : TrExprS env Us Δ v val')
    (hvt : env.HasType Us.length Δ.toCtx val' ty')
    (hx : x ∉ Δ.fvars) (hnres : ¬ gen.Reserves x)
    (hle : gen ≤ gen') (hres : gen'.Reserves x)
    (hkres : kernelNGen.Reserves x) :
    BridgeInv env Us known Γ cfg₀ gen'
      { ctx with lctx := ctx.lctx.mkLetDecl x n ty v } s
      ((some (x, ty.fvarsList ++ v.fvarsList), .vlet ty' val') :: Δ) where
  mlc := by
    obtain ⟨m, mwf, hlctx, hvlctx⟩ := hinv.mlc
    refine ⟨m.vlet x n ty v ty' val', ⟨mwf, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [hlctx]; exact hinv.trlctx.find?_eq_none.mpr hx
    · rw [hvlctx]; exact hty
    · rw [hvlctx]; exact hval
    · rw [hvlctx]; exact hvt
    · show m.lctx.mkLetDecl x n ty v = _; rw [hlctx]
    · show (some (x, ty.fvarsList ++ v.fvarsList), VLocalDecl.vlet ty' val') :: m.vlctx = _
      rw [hvlctx]
  lparams := hinv.lparams
  cfg := hinv.cfg
  natcfg := hinv.natcfg
  kfresh := by
    intro fv hfv
    have : fv = x ∨ fv ∈ Δ.fvars := by simpa using hfv
    rcases this with rfl | hfv'
    · exact hkres
    · exact hinv.kfresh fv hfv'
  fixvars := hinv.fixvars
  fixfresh := by
    -- The block's fixvars are reserved by `gen`; the binder's fvar is not (`hnres`), so
    -- the new `Δ` entry cannot be one of them.
    intro nm y hy
    obtain ⟨hres_y, hΔ_y⟩ := hinv.fixfresh nm y hy
    refine ⟨hres_y.mono hle, ?_⟩
    intro hmem
    have : y = x ∨ y ∈ Δ.fvars := by simpa using hmem
    rcases this with rfl | hmem'
    · exact hnres hres_y
    · exact hΔ_y hmem'
  reserved := by
    intro fv hfv
    have : fv = x ∨ fv ∈ Δ.fvars := by simpa using hfv
    rcases this with rfl | hfv'
    · exact hres
    · exact (hinv.reserved fv hfv').mono hle
  knames := hinv.knames
  consts := hinv.consts

/-! ## Opening an alternative's λ-telescope -/

/-- **`Erasure.lambdaOrIntroToArity` on a manifest λ-telescope.** Peels `n` binders
through the *inferred type* (`forallMonocular` pushes the **∀**'s binder name and
domain, which `ForallMatchesLam` pins to the λ's own), extends the bridge invariant
at each level, and hands the continuation `K` the fully-opened body together with
the `n` fresh fvars — plus the two facts the caller needs:

* `hext` — the outer binders' declarations survive the inner `mkLocalDecl`s, so
  `Erasure.mkAlt`, which reads every binder's `userName` at the *innermost*
  context, still sees the source names;
* the **closing** property — any `Erases` fact about the opened body at the
  extended context re-closes to an `Erases` fact about the original λ-telescope
  against `mkLambdas … (closeAlt …)`, i.e. exactly the alternative
  `Erases.cases`' `halts` premise demands. It is `bridge_lam_case` iterated, with
  `mkLambdas_closeAlt_cons` doing the de Bruijn bookkeeping.

Nothing here mentions `visitAlt` or the fixpoint approximation: `K` is arbitrary,
so the lemma is reusable and the fixpoint step stays plumbing. -/
theorem bridge_alt_telescope {env : VEnv} {Us : List Name} {known : Name → Prop}
    {Γ : ErasureCtx} {cfg₀ : ErasureConfig}
    {gw : Void IO.RealWorld → NameGenerator}
    (H : BridgeHyps env Us Γ gw) (henv : env.Ordered)
    (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State) :
    ∀ (n : Nat) (e ty : Expr) (Δ : VLCtx)
      (K : Expr → List FVarId → EraseM (List BinderName × LBTerm))
      (s : ErasureState) (ctx : ErasureContext) (w : Void IO.RealWorld)
      (r : List BinderName × LBTerm) (s' : ErasureState) (w' : Void IO.RealWorld),
      Erasure.lambdaOrIntroToArity e ty n K s ctx cctx ref w = .ok (r, s') w' →
      BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ →
      IsLamTelescope n e → Supported known Γ e → (∃ ve, TrExprS env Us Δ e ve) →
      ForallMatchesLam ty e →
      ∃ (ys : List FVarId) (efin : Expr) (Δ' : VLCtx) (ctx' : ErasureContext)
        (w₁ : Void IO.RealWorld),
        ys.length = n ∧ gw w ≤ gw w₁ ∧
        BridgeInv env Us known Γ cfg₀ (gw w₁) ctx' s Δ' ∧
        Supported known Γ efin ∧ (∃ ve, TrExprS env Us Δ' efin ve) ∧
        (∀ y ∈ Δ.fvars, ctx'.lctx.fvarIdToDecl.find! y = ctx.lctx.fvarIdToDecl.find! y) ∧
        K efin ys s ctx' cctx ref w₁ = .ok (r, s') w' ∧
        (∀ t : LBTerm, Erases env Us Γ Δ' efin t →
           Erases env Us Γ Δ e
             (mkLambdas (ys.map fun y => nameToBinder ((ctx'.lctx.fvarIdToDecl.find! y).userName))
               (closeAlt ys t))) := by
  intro n
  induction n with
  | zero =>
    intro e ty Δ K s ctx w r s' w' hrun hinv _ hsupp hex _
    exact ⟨[], e, Δ, ctx, w, rfl, NameGenerator.LE.rfl, hinv, hsupp, hex,
      fun _ _ => rfl, hrun, fun _ het => het⟩
  | succ n ih =>
    intro e ty Δ K s ctx w r s' w' hrun hinv hlam hsupp hex hfml
    cases e with
    | lam nm A b bi =>
      cases ty with
      | forallE nm' A' Cc bi' =>
        obtain ⟨rfl, rfl, hfml'⟩ := hfml
        have hlam' : IsLamTelescope n b := hlam
        simp only [Erasure.lambdaOrIntroToArity, Erasure.lambdaMonocularOrIntro,
          Erasure.forallMonocular] at hrun
        unfold Erasure.withLocalDecl at hrun
        rw [run_bind_ok] at hrun
        obtain ⟨x, s₁, w₁, hfresh, hk⟩ := hrun
        obtain ⟨hnres, hres, hle₁, hkres⟩ := H.fresh_run _ _ _ _ _ _ _ _ hfresh
        have hs₁ : s₁ = s := run_mkFreshFVarId_state _ _ _ _ _ hfresh
        subst hs₁
        rw [run_withReader] at hk
        simp only [] at hk
        obtain ⟨ve, hve⟩ := hex
        cases hve with
        | lam hty' hty hbody =>
        have hx : x ∉ Δ.fvars := fun hmem => hnres (hinv.reserved x hmem)
        have hfind : ctx.lctx.find? x = none := hinv.trlctx.find?_eq_none.mpr hx
        have hΔ' := LeanToLambdaBox.TrLCtx.mkLocalDecl (n := nm') (bi := bi')
          hinv.trlctx hfind hty hty'
        have hinv' := hinv.mkLocalDecl (n := nm') (bi := bi') hty hty' hx hnres hle₁ hres hkres
        rw [Lean.Expr.instantiate1_eq, Lean.Expr.instantiate1_eq] at hk
        have hbext := TrExprS.inst_fvar henv hΔ'.wf hbody
        obtain ⟨ys, efin, Δ'', ctx'', w₂, hlen, hle₂, hinv'', hsupp'', hex'', hext'', hK,
          hclose⟩ :=
          ih (b.instantiate1' (.fvar x)) (Cc.instantiate1' (.fvar x)) _
            (fun e' fvs => K e' (x :: fvs)) _ _ _ _ _ _ hk hinv'
            (hlam'.instantiate1' 0) (hsupp.lam_inv.instantiate1' x 0) ⟨_, hbext⟩
            (ForallMatchesLam.instantiate1' x hfml' 0)
        have hNx : ctx''.lctx.fvarIdToDecl.find! x
            = .cdecl ctx.lctx.decls.size x nm' A' bi' .default := by
          rw [hext'' x (by simp)]
          exact LocalContext.fvarIdToDecl_find!_of_find?
            (LocalContext.find?_mkLocalDecl_self hinv.trlctx.1 hfind)
        refine ⟨x :: ys, efin, Δ'', ctx'', w₂, by simp [hlen],
          NameGenerator.LE.trans hle₁ hle₂, hinv'', hsupp'', hex'', ?_, hK, ?_⟩
        · intro y hy
          rw [hext'' y (by simpa using Or.inr hy)]
          exact LocalContext.fvarIdToDecl_find!_congr
            (LocalContext.find?_mkLocalDecl_of_ne hinv.trlctx.1 hfind
              (fun h => hx (h ▸ hy)))
        · intro t het
          rw [List.map_cons, mkLambdas_closeAlt_cons _ _ _ _ _ (by simp), hNx]
          exact bridge_lam_case hinv.trlctx.2.noBV hty hbody hx (hclose t het)
      | _ => exact absurd hfml id
    | _ => exact absurd hlam id

/-- A `Std.HashMap` `get!` at a key the `get?` finds: what turns the `panic!`-defaulting
lookup of `get_constant_kername`'s miss branch into the kername the registry holds. -/
theorem hashMap_get!_of_get? {m : Std.HashMap Name Kername} {k : Name} {v : Kername}
    (h : m.get? k = some v) : m[k]! = v := by
  rw [Std.HashMap.getElem!_eq_get!_getElem?, show m[k]? = some v from h]
  rfl

/-- `ConstantInfo.value!` is `value?` where the latter succeeds — what makes the shipping
`visitMutual`'s `.get!` on the declaration's value total on the fragment. -/
theorem constantInfo_value!_of_value? {ci : ConstantInfo} {v : Expr}
    (h : ci.value? (allowOpaque := true) = some v) :
    ci.value! (allowOpaque := true) = v := by
  cases ci <;> simp [ConstantInfo.value?, ConstantInfo.value!] at h ⊢ <;> simp [h]

/-! ## The recursive exit, walked

`visitMutual`'s recursive exit mints one fresh fvar per sibling, erases every sibling body
under a reader carrying the block's fixvar map, closes each result with `mkDef`, and
registers one `.fix` entry per name. The theorem below walks all four of those loops and
composes their outputs into the three conjuncts `visitMutual`'s motive reports, at an
**abstract** eraser `vE` and its motive-1 refinement hypothesis — which is the form step 6
of `visitExpr_refines_erases_core` consumes (slice Γ-W3.6b; before it, the form step 6
*would* have consumed), and which guard (iv') instantiates at the shipping
`Erasure.visitExpr`.

What each piece supplies (recursion wall, slice Γ-W3):

* **the id loop** — `Erasure.run_mkFreshFVarId_list` (Γ-W0) against `BridgeHyps.fresh_run`
  and `BridgeInv.reserved`. `ids.Nodup` is the payoff of the chaining and is what
  `closeFix_eq_block_fold` and `blockMap_getElem?_inv` both need;
* **the sibling loop** — `Erasure.run_rec_exit_siblings_chained` (Γ-W0), whose invariant
  carries the outer δ record and the generator together, so the ambient `BridgeInv` can be
  rebuilt *at each sibling* from the one the step entered with. The rebuild is
  `BridgeInv.withFixvars` at `Γ₀.withFixvars fv`, whose `hlp` slot is
  `BlockHyps.block_lparams` (the exit's inner `withReader … lparams` has to land back at
  the ambient `Us`) and whose freshness slot is the id loop's output;
* **the erasure IH at the block-local context** — the instantiation slice Γ-W1 bought and
  guard (i-triple-prime) exhibits. `Supported.withFixvars` carries the fragment into the
  block; `ErasureCtx.coh_withFixvars` says the step's own `Γ` enters the same block as `Γ₀`;
* **the context strengthening to `[]`** — the loop erases each sibling at the *call site's*
  context (`withReader` moves `fixvars` and `lparams` and leaves the `lctx` alone), while
  `erases_rec_block_of_run`'s `hopen` demands `[]`. `Erases.strengthen_fvlift` against
  `BlockHyps.strengthen` is the bridge, and it is the one place the development's single
  class-R residue enters the induction;
* **the block's closedness** — `erases_target_lbClosed` (Γ-W3a). Not
  `visitExpr_noFix_closed`: at an abstract eraser there is no output-shape fact to be had,
  so closedness is read off the `Erases` derivation instead;
* **the composition** — `RecBlockErasure.erases_rec_block_of_run`, then
  `DeltaHyps.RunConclδ.recBlock` for the record and `Erasure.recConstState_get?` for the
  registration conclusion.

**The one premise that is not discharged here, and why.** `hreg` — "`Γ₀` records *this*
block for each of its own names" — is `Erases.fix`'s own registration premise, and it
cannot be derived: `Γ₀` is fixed before the run builds `defs`. It is irreducible at a
parameter `Γ` (`ColdStartDelta`'s premise ledger says so), and it stays an explicit
hypothesis, discharged by whoever holds a concrete run.

**Where it is stated changed at Γ-W3.5.** Until then it was stated at the abstract eraser
`vE`, and *there* every phrasing is refuted, not merely strong: two erasers hand back two
blocks and `Γ₀.recBodies` records one
(`rec_exit_agreement_eraser_quantified_refuted`). It is now
`RecBlockRegistered Γ₀ cctx ref names ctx s₀` — keyed on the **shipping**
`Erasure.visitExpr` — and the walk still consumes it at an abstract eraser, because the new
premise `hle : vE ⊑ Erasure.visitExpr` (the approximation conjunct every motive carries)
plus `Erasure.run_rec_exit_siblings_le` transport the sibling loop's successful run from
one to the other. Guard (iv'') fires the whole thing at exactly the data step 6 holds.

**And step 6 does produce `hreg`, since Γ-W3.6b.** Its motive quantifies `ctx` and `s₀`, so
the premise has to be quantified over them as well — which is `RecBlockAgreement` below,
*gated* on the fragment and on `BridgeInv`. The gate is what makes the quantified form
safe: `BridgeInv.cfg` (Γ-W3.6a) pins the config, so the two-configs refutation cannot be
written, and `consts`/`knames` pin the registry. Step 6 hands the walk
`Hreg cctx ref hkn hnd hinv`. -/

/-- **The registration agreement the recursive exit needs, keyed on the shipping eraser**
(slice Γ-W3.5). `Erases.fix` asks that `Γ₀` record the block a run builds, under each of
the block's own names. `Γ₀` is fixed before the run builds `defs`, so this is an agreement
between the context and the eraser, not a fact about the run.

Until Γ-W3.5 `rec_exit_refines_erases` carried this premise at its *abstract* eraser `vE`,
and there every phrasing is **contradictory**: two erasers hand back two different blocks
and `Γ₀.recBodies` records one (`rec_exit_agreement_eraser_quantified_refuted`). Keyed on
`Erasure.visitExpr` there is one block per `(names, ids, ctx, s₀, wi)`, and a caller
holding a concrete run discharges it — while a walk at an abstract eraser can still *feed*
it, through the approximation conjunct the motives carry and
`Erasure.run_rec_exit_siblings_le`.

`ctx` and `s₀` are parameters here, deliberately: bare quantification over them would make
the premise speak about readers with different `Erasure.Config`s, which erase the same
block to different `defs`. The *gated* quantification a step can supply is
`RecBlockAgreement` below (Γ-W3.6b), which is this predicate under `BridgeInv`. See guards
(iv'')/(iv''') and `ColdStart`'s residue-1 row. -/
def RecBlockRegistered (Γ₀ : ErasureCtx) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (names : List Name)
    (ctx : ErasureContext) (s₀ : ErasureState) : Prop :=
  ∀ {ids : List FVarId} {defs : List (@FixDef LBTerm)} {sd : ErasureState}
    {wi wd : Void IO.RealWorld},
    ((names.mapM (fun m => do
        let cim ← getConstInfo m
        let t ← withReader (fun e => { e with lparams := cim.levelParams })
          (do let pe ← prepare_erasure (cim.value! (allowOpaque := true)); Erasure.visitExpr pe)
        mkDef (remove_unsafe_rec m) (names.map remove_unsafe_rec) t)) :
        EraseM (List (@FixDef LBTerm)))
      s₀ (blockReader (names.map remove_unsafe_rec) ids ctx) cctx ref wi = .ok (defs, sd) wd →
    ∀ (j : Nat), j < defs.length → ∃ h : j < (names.map remove_unsafe_rec).length,
      Γ₀.recBodies ((names.map remove_unsafe_rec)[j]'h) = some (defs, j)

/-- **The block a recursive exit stores is the block `Γ₀` records**, at the configurations
the bridge's induction quantifies (recursion wall, slice Γ-W3.6b) — `Erases.fix`'s own
registration premise, in the one shape a *step* of the induction can consume.

`RecBlockRegistered` above is stated at *a* reader and *a* state. Step 6's motive
quantifies both, so a premise handed to the induction from outside has to quantify them
too. Γ-W3.5 recorded that quantification as a second wall; this is the statement that
takes it down, and what makes it safe is that the quantifiers are **gated**, not bare:

* on the *fragment*, `∀ m ∈ names, known (remove_unsafe_rec m)` and the `Nodup` — the block
  is one the walk is allowed to be in, keyed the way `BlockHyps` is (`gBlockKeying`);
* on the *invariant*, `BridgeInv env Us known Γ cfg₀ gen ctx s Δ`. Two of its fields do the
  work. `cfg` (Γ-W3.6a) pins `ctx.config = cfg₀`, which is what rules out the only
  refutation anyone could write — two readers whose configs differ in `csimp`, `extern` or
  `remove_irrel_constr_args` erase the same block to different `defs`, and `Γ₀.recBodies`
  records one. `consts`/`knames` pin the registry to canonical kernames, which rules out
  the other — a state mapping some `g` to a garbage kername erases a sibling's reference
  differently.

What is left quantified is `ctx.lctx`, `s.inductives` and the world. That is exactly the
freedom the already-shipped run-keyed fields carry (`DeltaHyps.prep_esrc`,
`BlockHyps.block_esrc`, `BridgeHyps.fresh_run`), and for the same reason: they quantify
opaque runtime primitives, and `RecBlockRegistered`'s own `wi : Void IO.RealWorld` carries
the Core environment, so "`defs` is a function of the prepared bodies" is not merely
unproven but false as a statement over these quantifiers.

**It is not a theorem, and the honest reason.** `Γ₀` is fixed before the run builds
`defs`, so nothing inside the induction can pin it. The route that would make it a
theorem is `Esrc.walked`-style: read `Γ.recBodies` off the run's final `gdecls`, since
registration is cons-only and once-per-name. That re-indexes `Erases` at a state-dependent
`Γ`, and with it `RecEnvConsistent`, the source evaluation's δ-steps and all eighteen
motives — the price is "re-index the erasure relation", recorded here so the route stays
visible.

**Why a named premise and not a `BlockHyps` field.** `BlockHyps` lives in `DeltaHyps.lean`,
which this file imports, so a field there cannot mention `BridgeInv` or
`RecBlockRegistered` without moving `BridgeInv` below it. Promoting it is a file-surgery
slice of its own. Named premises of this class have precedent at the capstones (`hstr`,
`hnest`, `hcon`). -/
def RecBlockAgreement (env : VEnv) (Us : List Name) (known : Name → Prop)
    (Γ₀ : ErasureCtx) (cfg₀ : ErasureConfig) : Prop :=
  ∀ (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)
    {names : List Name} {Γ : ErasureCtx} {gen : NameGenerator}
    {ctx : ErasureContext} {s : ErasureState} {Δ : VLCtx},
    (∀ m ∈ names, known (remove_unsafe_rec m)) →
    (names.map remove_unsafe_rec).Nodup →
    BridgeInv env Us known Γ cfg₀ gen ctx s Δ →
    RecBlockRegistered Γ₀ cctx ref names ctx s

/-- **What the agreement costs at the empty fragment: nothing** — the mirror of
`DeltaHyps.of_bot`/`BlockHyps.of_bot`, and the reason the block instantiation
(`visitExpr_refines_erases_block`) picks the premise up for free.

At `known = ⊥` the gate `∀ m ∈ names, known (remove_unsafe_rec m)` forces `names = []`, the
sibling `mapM` returns `[]`, and the conclusion quantifies `j < [].length`. So this is a
*theorem*, not an assumption, exactly where the recursive walk's inner runs are taken. -/
theorem RecBlockAgreement.of_bot {env : VEnv} {Us : List Name} {Γ₀ : ErasureCtx}
    {cfg₀ : ErasureConfig} : RecBlockAgreement env Us (fun _ => False) Γ₀ cfg₀ := by
  intro cctx ref names Γ gen ctx s Δ hkn _ _ ids defs sd wi wd hrun j hj
  obtain rfl : names = [] := by
    cases names with
    | nil => rfl
    | cons a t => exact absurd (hkn a (by simp)) id
  rw [List.mapM_nil, run_pure] at hrun
  cases hrun
  simp at hj

/-- **The stored block carries no `FVarId`** (recursion wall, slice Γ-W3.6a) — the
measurement that says what the `∀ ids` quantifier in `RecBlockRegistered` costs, which is
nothing.

The premise above quantifies the block's fresh ids, so it is fair to ask whether the ids
the run happens to mint can be *read off* the block it stores. They cannot: `mkDef`
abstracts exactly the ids the block-local reader installed, so the stored body is
`FVarId`-free. Two machine-checked facts compose to it — `erases_target_fvars` (an
fvar-free source erases to a target whose free variables are fixvars of the context, since
`Erases.fvar` is the only rule that can invent one and its source-side premise is `False`)
and `not_hasFVar_closeFix` (a term whose free variables lie in `ids` closes to one with
none).

What it does **not** give, and the reason `RecBlockRegistered` stays an assumption rather
than becoming a theorem: fvar-freeness of the *output* is not equivariance of the
*function*. "No id occurs in the result" does not say two runs from different generator
states build the same `defs`, and the premise's world quantifier ranges over Core
environments in any case. The honest reading is the narrow one: the id quantifier is
harmless, the world one is the development's standing boundary. -/
theorem rec_exit_block_fvar_free {env : VEnv} {Us : List Name} {Γ₀ : ErasureCtx}
    {fvmap : Name → Option FVarId} {ids : List FVarId} {pe : Expr} {t : LBTerm}
    {d : @FixDef LBTerm}
    (hopen : Erases env Us (Γ₀.withFixvars fvmap) [] pe t)
    (hclpe : FVarsIn (fun _ => False) pe)
    (hfv : ∀ nm x, fvmap nm = some x → x ∈ ids)
    (hbody : d.body = closeFix ids 0 t) (x : FVarId) : ¬ hasFVar x d.body := by
  rw [hbody]
  refine not_hasFVar_closeFix (fun z hz => ?_) 0 x
  obtain ⟨nm, hnm⟩ := erases_target_fvars hopen hclpe hz
  exact hfv nm z hnm

set_option maxHeartbeats 1000000 in
theorem rec_exit_refines_erases {env : VEnv} {Us : List Name} {known : Name → Prop}
    {Γ₀ Γ : ErasureCtx} {cfg₀ : ErasureConfig} {Esrc : SEnv}
    {gw : Void IO.RealWorld → NameGenerator}
    {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    (H : BridgeHyps env Us Γ₀ gw)
    (Hδ : DeltaHyps env Us known Γ₀ cfg₀ Esrc gw cctx ref)
    (Hβ : BlockHyps env Us known Γ₀ cfg₀ Esrc cctx ref)
    (henv : env.Ordered)
    {vE : Expr → EraseM LBTerm}
    (ih1 : ∀ (e : Expr) (s : ErasureState) (ctx' : ErasureContext) (w' : Void IO.RealWorld)
        (t : LBTerm) (s' : ErasureState) (w'' : Void IO.RealWorld),
      vE e s ctx' cctx ref w' = .ok (t, s') w'' →
      ∀ (Γ' : ErasureCtx), Γ' = Γ₀.withFixvars Γ'.fixvars →
      ∀ (Δ' : VLCtx), BridgeInv env Us known Γ' cfg₀ (gw w') ctx' s Δ' → Supported known Γ' e →
      (∃ ve, TrExprS env Us Δ' e ve) →
      Erases env Us Γ' Δ' e t ∧ RunConclδ env Us Γ₀ Esrc s s' ∧ gw w' ≤ gw w'')
    (hle : vE ⊑ Erasure.visitExpr)
    (hΓ : Γ = Γ₀.withFixvars Γ.fixvars)
    {names : List Name} {ctx : ErasureContext} {s₀ s₁ : ErasureState} {Δ : VLCtx}
    {w w₁ : Void IO.RealWorld} {u₀ : Unit} {n : Name}
    (hkn : ∀ m ∈ names, known (remove_unsafe_rec m))
    (hnd : (names.map remove_unsafe_rec).Nodup)
    (hnmem : n ∈ names.map remove_unsafe_rec)
    (hinv : BridgeInv env Us known Γ cfg₀ (gw w) ctx s₀ Δ)
    (hreg : RecBlockRegistered Γ₀ cctx ref names ctx s₀)
    (hrun : (do
        let ids ← names.mapM (fun _ => (mkFreshFVarId : EraseM FVarId))
        withReader
            (fun e => { e with
              fixvars := some (Std.HashMap.ofList ((names.map remove_unsafe_rec).zip ids)) }) (do
          let defs ← names.mapM (fun m => do
            let cim ← getConstInfo m
            let t ← withReader (fun e => { e with lparams := cim.levelParams })
              (do let pe ← prepare_erasure (cim.value! (allowOpaque := true)); vE pe)
            mkDef (remove_unsafe_rec m) (names.map remove_unsafe_rec) t)
          for p in (names.map remove_unsafe_rec).zipIdx do
            modify (fun st => { st with
                constants := st.constants.insert p.1 (toKername p.1),
                gdecls := (toKername p.1, .constantDecl ⟨some (.fix defs p.2)⟩) :: st.gdecls })
          pure ()) : EraseM Unit) s₀ ctx cctx ref w = .ok (u₀, s₁) w₁) :
    RunConclδ env Us Γ₀ Esrc s₀ s₁ ∧ gw w ≤ gw w₁ ∧ (s₁.constants.get? n).isSome := by
  classical
  -- (1) the id-minting loop: the block's fvars come back `Nodup`, at an unchanged state,
  -- reserved by the generator and outside the ambient context.
  rw [run_bind_ok] at hrun
  obtain ⟨ids, sid, wid, hids, hrun⟩ := hrun
  obtain ⟨hidlen, hidnd, rfl, hleid, hidres⟩ :=
    run_mkFreshFVarId_list (gw := gw) (kgen := kernelNGen) (fvs := Δ.fvars)
      (fun s' ctx' cctx' ref' w' x s'' w'' hf => H.fresh_run s' ctx' cctx' ref' w' x s'' w'' hf)
      (fun x hx => hinv.reserved x hx) hids
  have hflen : (names.map remove_unsafe_rec).length = ids.length := by
    rw [List.length_map, hidlen]
  -- (2) the sibling loop, then (3) the registration `forIn` and the tail
  rw [run_withReader, run_bind_ok] at hrun
  obtain ⟨defs, sd, wd, hdefs, hrun⟩ := hrun
  rw [run_bind_ok] at hrun
  obtain ⟨u4, sf, wf, hloop, hrun⟩ := hrun
  obtain ⟨hsf, rfl⟩ := run_modify_forIn_ok hloop
  rw [run_pure] at hrun
  cases hrun
  -- the fragment pins the ambient context's fixvar map at ⊥ …
  have hnfv : Γ₀.fixvars = fun _ => none := by
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hnmem
    exact Hδ.nofixvars (hkn m hm)
  -- … and the step's own `Γ` enters the same block as `Γ₀` does
  have hcoh := ErasureCtx.coh_withFixvars (Γ₀ := Γ₀) hΓ
    (fun nm => (Std.HashMap.ofList ((names.map remove_unsafe_rec).zip ids))[nm]?)
  -- the block's ids are fresh for the ambient context, at every later world
  have hfresh : ∀ (w' : Void IO.RealWorld), gw wid ≤ gw w' → ∀ (nm : Name) (x : FVarId),
      (Std.HashMap.ofList ((names.map remove_unsafe_rec).zip ids))[nm]? = some x →
      (gw w').Reserves x ∧ x ∉ Δ.fvars := by
    intro w' hle' nm x hx
    obtain ⟨k, hk, -, rfl⟩ := blockMap_getElem?_inv hnd hflen hx
    exact ⟨((hidres _ (List.getElem_mem _)).1).mono hle',
      (hidres _ (List.getElem_mem _)).2.1⟩
  -- the sibling loop, with the caller's invariant threaded through state and world
  obtain ⟨hdlen, ⟨hrcd, hled⟩, hpkg⟩ :=
    run_rec_exit_siblings_chained (vE := vE) (names := names)
      (fixnames := names.map remove_unsafe_rec)
      (g := fun ci c => { c with lparams := ci.levelParams })
      (val := fun ci => ci.value! (allowOpaque := true))
      (ctx := blockReader (names.map remove_unsafe_rec) ids ctx)
      (P := fun s' w' => RunConclδ env Us Γ₀ Esrc sid s' ∧ gw wid ≤ gw w')
      (R := fun m d => ∃ (pe : Expr) (t : LBTerm),
        Esrc (remove_unsafe_rec m) = some pe ∧ d.body = closeFix ids 0 t ∧
          d.principalArgIdx = 0 ∧ LBClosed t 0 ∧
          Erases env Us (Γ₀.withFixvars
            (fun nm => (Std.HashMap.ofList ((names.map remove_unsafe_rec).zip ids))[nm]?)) [] pe t)
      (fun hmem hP hci hpr hvis hmk => by
        obtain ⟨hrcP, hleP⟩ := hP
        have hknm := hkn _ hmem
        obtain rfl := run_getConstInfo_state _ _ _ _ _ hci
        have hleci := Hδ.ci_run hci
        obtain ⟨hlepr, rfl⟩ := Hδ.prep_run hpr
        obtain ⟨hlink, hsupp, htr, hlam, hclpe, hfvpe, hnp, ve, hve⟩ :=
          Hβ.sibling_scope Hδ hknm hci hpr hinv.cfg
        have hlp := Hβ.block_lparams hknm hci
        have hlewc := NameGenerator.LE.trans hleP (NameGenerator.LE.trans hleci hlepr)
        -- the invariant travels to the block's reader, at the block-local context
        have hinvj := ((hinv.mono_state hrcP.rc).mono
            (NameGenerator.LE.trans hleid hlewc)).withFixvars
          (known' := known)
          (fvmap := Std.HashMap.ofList ((names.map remove_unsafe_rec).zip ids))
          (ctx' := { blockReader (names.map remove_unsafe_rec) ids ctx with
            lparams := ‹ConstantInfo›.levelParams })
          rfl hlp rfl rfl (fun nm x => Iff.rfl) (hfresh _ hlewc)
        rw [hcoh] at hinvj
        obtain ⟨her, hrcv, hlev⟩ := ih1 _ _ _ _ _ _ _ hvis _ rfl Δ hinvj
          (Supported.withFixvars hnfv hsupp _) (htr Δ)
        -- the sibling body is erased at the call site's `Δ`; the block needs it at `[]`
        have heropen : Erases env Us (Γ₀.withFixvars
            (fun nm => (Std.HashMap.ofList ((names.map remove_unsafe_rec).zip ids))[nm]?)) [] _ _ :=
          Erases.strengthen_fvlift henv Hβ.strengthen her
            (VLCtx.FVLift.from_nil hinv.noBV) hinv.vlctx_wf.fvwf hnp hve
        have hclt := erases_target_lbClosed heropen hclpe
        obtain ⟨-, hdbody, rfl, rfl⟩ := run_mkDef_ok hmk
        refine ⟨⟨hrcP.trans hrcv, NameGenerator.LE.trans hlewc hlev⟩,
          _, _, hlink, ?_, run_mkDef_rarg hmk, hclt, heropen⟩
        rw [hdbody]
        exact closeFix_eq_block_fold hnd hflen _)
      ⟨RunConclδ.rfl' _, NameGenerator.LE.rfl⟩ hdefs
  -- (4) the per-sibling packages, as the lists `erases_rec_block_of_run` consumes
  have hsel : ∀ (j : Nat) (hj : j < defs.length), ∃ (pe : Expr) (t : LBTerm),
      Esrc ((names.map remove_unsafe_rec)[j]'(by
        rw [List.length_map, ← hdlen]; exact hj)) = some pe ∧
      (defs[j]'hj).body = closeFix ids 0 t ∧ (defs[j]'hj).principalArgIdx = 0 ∧
      LBClosed t 0 ∧
      Erases env Us (Γ₀.withFixvars (fun nm =>
        (Std.HashMap.ofList ((names.map remove_unsafe_rec).zip ids))[nm]?)) [] pe t := by
    intro j hj
    obtain ⟨d, hd, hR⟩ := hpkg j (by omega)
    obtain rfl : d = defs[j]'hj := by
      rw [List.getElem?_eq_getElem hj] at hd; exact (Option.some.inj hd).symm
    rw [List.getElem_map]
    exact hR
  obtain ⟨srcf, objf, hspec⟩ : ∃ (srcf : ∀ (j : Nat), j < defs.length → Expr)
      (objf : ∀ (j : Nat), j < defs.length → LBTerm),
      ∀ (j : Nat) (hj : j < defs.length),
        Esrc ((names.map remove_unsafe_rec)[j]'(by
          rw [List.length_map, ← hdlen]; exact hj)) = some (srcf j hj) ∧
        (defs[j]'hj).body = closeFix ids 0 (objf j hj) ∧
        (defs[j]'hj).principalArgIdx = 0 ∧ LBClosed (objf j hj) 0 ∧
        Erases env Us (Γ₀.withFixvars (fun nm =>
          (Std.HashMap.ofList ((names.map remove_unsafe_rec).zip ids))[nm]?)) []
          (srcf j hj) (objf j hj) :=
    ⟨fun j hj => (hsel j hj).choose, fun j hj => ((hsel j hj).choose_spec).choose,
      fun j hj => ((hsel j hj).choose_spec).choose_spec⟩
  have hlinkf : ∀ (j : Nat) (hj : j < defs.length), _ := fun j hj => (hspec j hj).1
  have hclosef : ∀ (j : Nat) (hj : j < defs.length), _ := fun j hj => (hspec j hj).2.1
  have hrargf : ∀ (j : Nat) (hj : j < defs.length), _ := fun j hj => (hspec j hj).2.2.1
  have hclf : ∀ (j : Nat) (hj : j < defs.length), _ := fun j hj => (hspec j hj).2.2.2.1
  have hopenf : ∀ (j : Nat) (hj : j < defs.length), _ := fun j hj => (hspec j hj).2.2.2.2
  have hknames : ∀ m : Name, Γ₀.constants m = toKername m := by
    intro m; rw [← ErasureCtx.coh_constants hΓ]; exact hinv.knames m
  have hknfix : ∀ (j : Nat) (hj : j < (names.map remove_unsafe_rec).length),
      known ((names.map remove_unsafe_rec)[j]'hj) := by
    intro j hj
    rw [List.getElem_map]
    exact hkn _ (List.getElem_mem _)
  -- (5) the block's erasure, at the ambient context
  have hblock := erases_rec_block_of_run (env := env) henv (Γ := Γ₀) hnfv
    (fv := fun nm => (Std.HashMap.ofList ((names.map remove_unsafe_rec).zip ids))[nm]?)
    (fixnames := names.map remove_unsafe_rec) (ids := ids)
    (srcs := List.ofFn (fun j : Fin defs.length => srcf j.1 j.2))
    (obodies := List.ofFn (fun j : Fin defs.length => objf j.1 j.2))
    (defs := defs)
    (by rw [List.length_map, hdlen]) (by omega) (by simp) (by simp) hidnd
    (fun j h => by
      obtain ⟨h', hh⟩ := hreg (Erasure.run_rec_exit_siblings_le hle hdefs) j h
      exact hh)
    (fun nm x hx => by
      obtain ⟨k, hk, h1, h2⟩ := blockMap_getElem?_inv hnd hflen hx
      rw [List.length_map] at hk
      exact ⟨k, by omega, h1, h2⟩)
    (fun d hd => by obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hd; exact hrargf j hj)
    (fun j => lbClosed_fix_of_bodies (k := defs.length) rfl (fun d hd => by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
      rw [hclosef i hi, closeFix, closeFixFold_eq_foldl]
      have hcl := lbClosed_foldl_zipIdx ids (hclf i hi)
      rw [show ids.length = defs.length from by omega] at hcl
      exact hcl) j)
    (fun j h => by simp only [List.getElem_ofFn]; exact hclf j h)
    (fun j h => by simp only [List.getElem_ofFn]; exact hclosef j h)
    (fun j h => by
      simp only [List.getElem_ofFn]
      exact (Hβ.block_lam (hknfix j _) (hlinkf j h)).2)
    (fun j h => by
      simp only [List.getElem_ofFn]
      obtain ⟨-, ve, hve⟩ := Hδ.esrc_shape (hlinkf j h)
      simpa [VLCtx.bvars] using hve.closed)
    (fun j h => by
      simp only [List.getElem_ofFn]
      obtain ⟨-, ve, hve⟩ := Hδ.esrc_shape (hlinkf j h)
      exact hve.fvarsIn.mono (by simp))
    (fun j h => by simp only [List.getElem_ofFn]; exact hopenf j h)
    Hβ.nonest
  -- (6) the δ record grows by the whole block at once
  have hrecδ : RunConclδ env Us Γ₀ Esrc sd
      (Erasure.recConstState (names.map remove_unsafe_rec) defs sd) := by
    refine RunConclδ.recBlock (fun j hj => hknames _) (fun j hj m hm hEq => ?_)
      (fun j hj body hb => ?_)
    · exact Hδ.kinj (Hδ.esrc_sub hm) (hknfix j hj) hEq
    · have hj' : j < defs.length := by rw [List.length_map] at hj; omega
      obtain rfl : body = srcf j hj' := by
        rw [hlinkf j hj'] at hb; exact (Option.some.inj hb).symm
      refine ⟨[], trivial, rfl, ?_⟩
      have := hblock j hj' []
      simpa only [List.getElem_ofFn] using this
  refine ⟨?_, NameGenerator.LE.trans hleid hled, ?_⟩
  · rw [hsf]; exact hrcd.trans hrecδ
  · rw [hsf]; exact recConstState_get? hnmem

/-! ## The main induction -/

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 4000 in
/-- **The bridge, all 18 motives — and all 18 now carry content.** 1 (`visitExpr`),
2 (`visitLiteral`, the peano-`Nat` literal, slice nat-L3), 3 (`visitConstructor`),
4 (`visitConst`), 5 (`get_constant_kername`), 6 (`visitMutual`: the δ record and the
registration conclusion, slice D4a), 7 (`visitAppArgs`), 8 (`visitLet`),
9 (`visitLambda`), 10 (`visitProj`, slice proj-P8), 11 (`visitApp`),
12 (`visitConstApp`), 13/14 (`visitCtorEta`/`Go`) and — the ι fragment,
`Supported.casesApp` — 15/16 (`visitCasesEta`/`Go`), 17 (`visitCases`),
18 (`visitAlt`). No motive concludes `True` any more: motive 10 was the last one that
did — its branch was unreachable from the supported fragment until `Supported.proj`
arrived — and proj-P8 gave it the projection arm.

Motive 18 opens the alternative's full λ-telescope (`bridge_alt_telescope`),
so `Erases.cases`' `harity` premise is met at each constructor's real field
count.

## Every motive quantifies its own `Γ` (recursion wall, slice Γ-W1)

The erasure context is **not** fixed along the induction. Each motive binds, immediately
after its run hypothesis,

```lean
    ∀ (Γ : ErasureCtx) (hΓ : Γ = Γ₀.withFixvars Γ.fixvars) Δ, …
```

against the *ambient* `Γ₀` the theorem's premises are stated at. The reason is `visitMutual`'s
recursive exit: it erases each sibling body under a reader whose `fixvars` is the block's own
map, and `BridgeInv.fixvars` is an **iff** against `Γ.fixvars`, so the erasure IH is
inapplicable there at any fixed `Γ` (`bridgeInv_blockReader_refuted`). Four facts make the
change cheap:

* **only `Γ` moves.** `known`, `Esrc` and the four bundles stay outer. The bundles are
  re-derived per step in one line (`BridgeHyps.of_coh` and friends, no obligation);
* **`Γ` stays a variable literally named `Γ`**, so the ~135 `Erases env Us Γ`,
  `BridgeInv … Γ`, `Supported known Γ`, `Γ.…` mentions inside the step bodies are
  untouched — and, being a local constant rather than a `withFixvars` application, the goal
  terms do not grow, which is what keeps the elaboration budget where it was;
* **the binders sit after the run hypothesis**, i.e. inside the `Q` of
  `eraseM_admissible_ok₁`⁻⁵, so all 18 admissibility obligations are unchanged;
* **`RunConclδ` is re-indexed to `Γ₀`.** The δ record must be at the ambient context
  anyway — every registered body is erased at a context with `fixvars = ⊥` — and pinning it
  there is what makes the chaining compose with nothing to transport. It is also what
  forces step 6's callee invariant `hinv'` to be built at `Γ₀`: the non-recursive exit
  installs `fixvars := none`, and `DeltaHyps.nofixvars` pins `Γ₀.fixvars = ⊥`, whereas the
  motive-local `Γ` is arbitrary.

The bridge theorem below is the `Γ := Γ₀`, `hΓ := ` `withFixvars_self` corollary, so every
consumer is textually unchanged.

## Every motive carries its approximation (recursion wall, slice Γ-W3.5)

Each motive is a **conjunction**: the refinement statement above, and

```lean
    f ⊑ Erasure.visitXxx
```

— the induction's abstract eraser is below the shipping one, in `partial_fixpoint`'s own
order. Read at the fixpoint the second conjunct is a tautology, which is why the eighteen
`⊑` conjuncts in the conclusion carry no information *here*; read at a step it is what
lets `visitMutual`'s recursive exit speak about *the* block rather than about whichever
block an arbitrary point of the CCPO happens to build
(`rec_exit_agreement_eraser_quantified_refuted`). Three facts make it cheap:

* **admissibility is a conjunction of admissibles.** `Erasure.admissible_and_le` pairs
  the old `eraseM_admissible_ok₁`⁻⁵ obligation with `CCPO.csup_le` — a chain below the
  fixpoint has its supremum below the fixpoint — so the eighteen obligations are the
  eighteen old ones, wrapped;
* **the step obligations are the erasure functional's own monotonicity.**
  `Erasure.visitExpr.mutual._proof_1 : Lean.Order.monotone …` is in the environment,
  generated by `partial_fixpoint` itself; `Erasure.mutual_le_of` packs the step's
  hypotheses into the eighteen-slot `PProd` it is stated over, `Erasure.fix_step_le`
  reads `fix_eq` as an inequality, and one projection per slot lands the conjunct. Every
  step's approximation half is therefore four lines, and they are the same four;
* **the conjunct is `Γ`-free and `f`-shaped**, so it does not interact with Γ-W1's
  quantification: it sits outside the run hypothesis rather than inside the `Q`, and the
  content half of every step is textually the pre-Γ-W3.5 proof (modulo one
  `replace ih := ih.1` per induction hypothesis used).

Γ-W3c priced this conjunct in the run-ok form `f x … = .ok r → Erasure.visitExpr x … =
.ok r`. That form is admissible but **not step-provable**: run-ok agreement is strictly
weaker than `⊑` (`EST.bot` is an `.error`, so an eraser that errors where the fixpoint
succeeds satisfies it), and monotonicity gives `F x ⊑ F y` from `x ⊑ y` with no run-ok
analogue. The motives therefore carry `⊑`; `Erasure.run_ok_of_le` is the run-ok form, one
lemma wide, and is what consumers of the conjunct actually apply. -/
theorem visitExpr_refines_erases_core {env : VEnv} {Us : List Name}
    {known : Name → Prop} {Γ₀ : ErasureCtx} {cfg₀ : ErasureConfig} {Esrc : SEnv}
    {gw : Void IO.RealWorld → NameGenerator}
    (H : BridgeHyps env Us Γ₀ gw) (HD : DataBridgeHyps Γ₀ gw) (C : CasesBridgeHyps Γ₀ gw) (P : ProjBridgeHyps Γ₀ gw)
    (Hδ : ∀ (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State),
      DeltaHyps env Us known Γ₀ cfg₀ Esrc gw cctx ref)
    (Hβ : ∀ (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State),
      BlockHyps env Us known Γ₀ cfg₀ Esrc cctx ref)
    (Hreg : RecBlockAgreement env Us known Γ₀ cfg₀)
    (henv : env.Ordered) :
    ((∀ e s ctx cctx ref w t s' w', visitExpr e s ctx cctx ref w = .ok (t, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ, BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ → Supported known Γ e →
      (∃ ve, TrExprS env Us Δ e ve) →
      Erases env Us Γ Δ e t ∧ RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w') ∧
      Erasure.visitExpr ⊑ Erasure.visitExpr) ∧
    ((∀ l s ctx cctx ref w r s' w', visitLiteral l s ctx cctx ref w = .ok (r, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ (n : Nat) (iid : InductiveId),
        BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ →
        l = .natVal n → Γ.natPeano = true →
        Γ.ctors ``Nat.zero = some (iid, 0) → Γ.ctors ``Nat.succ = some (iid, 1) →
        (∃ ve, TrExprS env Us Δ (.lit l) ve) →
        Erases env Us Γ Δ (.lit l) r ∧ RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w') ∧
      Erasure.visitLiteral ⊑ Erasure.visitLiteral) ∧
    ((∀ cn args s ctx cctx ref w t s' w',
      visitConstructor cn args s ctx cctx ref w = .ok (t, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ (us : List Level) (iid : InductiveId) (cidx : Nat),
        BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ →
        Γ.ctors cn = some (iid, cidx) →
        (ctx.config.nat = .peano ∨ (cn ≠ ``Nat.zero ∧ cn ≠ ``Nat.succ)) →
        (∀ i (hi : i < args.size), Supported known Γ (args[i]) ∧
          ∃ ve, TrExprS env Us Δ (args[i]) ve) →
        Erases env Us Γ Δ (args.foldl Expr.app (.const cn us)) t ∧ RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w') ∧
      Erasure.visitConstructor ⊑ Erasure.visitConstructor) ∧
    ((∀ e s ctx cctx ref w t s' w', visitConst e s ctx cctx ref w = .ok (t, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ, BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ →
      ∀ n us, e = .const n us → (known n ∨ Γ.fixvars n ≠ none) →
      Γ.ctors n = none → Γ.casesOns n = none →
      Erases env Us Γ Δ e t ∧ RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w') ∧
      Erasure.visitConst ⊑ Erasure.visitConst) ∧
    ((∀ n s ctx cctx ref w kn s' w',
      get_constant_kername n s ctx cctx ref w = .ok (kn, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ, BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ → known n →
      kn = Γ.constants n ∧ RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w') ∧
      Erasure.get_constant_kername ⊑ Erasure.get_constant_kername) ∧
    ((∀ n s ctx cctx ref w r s' w', visitMutual n s ctx cctx ref w = .ok (r, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ, BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ → known n →
      RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w' ∧ (s'.constants.get? n).isSome) ∧
      Erasure.visitMutual ⊑ Erasure.visitMutual) ∧
    ((∀ f' args s ctx cctx ref w t s' w',
      visitAppArgs f' args s ctx cctx ref w = .ok (t, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ (hd : Expr), BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ →
      Erases env Us Γ Δ hd f' →
      (∀ i (hi : i < args.size), Supported known Γ (args[i]) ∧
        ∃ ve, TrExprS env Us Δ (args[i]) ve) →
      Erases env Us Γ Δ (args.foldl Expr.app hd) t ∧ RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w') ∧
      Erasure.visitAppArgs ⊑ Erasure.visitAppArgs) ∧
    ((∀ e s ctx cctx ref w t s' w', visitLet e s ctx cctx ref w = .ok (t, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ, BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ →
      ∀ n ty v b nd, e = .letE n ty v b nd → Supported known Γ e →
      (∃ ve, TrExprS env Us Δ e ve) →
      Erases env Us Γ Δ e t ∧ RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w') ∧
      Erasure.visitLet ⊑ Erasure.visitLet) ∧
    ((∀ e s ctx cctx ref w t s' w', visitLambda e s ctx cctx ref w = .ok (t, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ, BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ →
      ∀ n ty b bi, e = .lam n ty b bi → Supported known Γ e →
      (∃ ve, TrExprS env Us Δ e ve) →
      Erases env Us Γ Δ e t ∧ RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w') ∧
      Erasure.visitLambda ⊑ Erasure.visitLambda) ∧
    ((∀ tn i e s ctx cctx ref w r s' w',
      visitProj tn i e s ctx cctx ref w = .ok (r, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ (iid : InductiveId) (np nf : Nat),
        BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ →
        Γ.projs tn = some (iid, np) → Γ.ctorFields iid = some [nf] → i < nf →
        Supported known Γ e → (∃ ve, TrExprS env Us Δ e ve) →
        Erases env Us Γ Δ (.proj tn i e) r ∧ RunConclδ env Us Γ₀ Esrc s s' ∧
          gw w ≤ gw w') ∧
      Erasure.visitProj ⊑ Erasure.visitProj) ∧
    ((∀ e s ctx cctx ref w t s' w', visitApp e s ctx cctx ref w = .ok (t, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ, BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ → Supported known Γ e →
      (∃ ve, TrExprS env Us Δ e ve) →
      Erases env Us Γ Δ e t ∧ RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w') ∧
      Erasure.visitApp ⊑ Erasure.visitApp) ∧
    ((∀ e s ctx cctx ref w t s' w', visitConstApp e s ctx cctx ref w = .ok (t, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ, BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ → Supported known Γ e →
      (∃ ve, TrExprS env Us Δ e ve) →
      ∀ cn us, e.getAppFn = .const cn us →
      Erases env Us Γ Δ e t ∧ RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w') ∧
      Erasure.visitConstApp ⊑ Erasure.visitConstApp) ∧
    ((∀ cn ar e s ctx cctx ref w t s' w',
      visitCtorEta cn ar e s ctx cctx ref w = .ok (t, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ (us : List Level) (iid : InductiveId) (cidx : Nat),
        BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ →
        e.getAppFn = .const cn us → Γ.ctors cn = some (iid, cidx) →
        Γ.ctorArities cn = some ar → ar ≤ e.getAppArgs.size →
        cn ≠ ``Nat.zero → cn ≠ ``Nat.succ →
        (∀ i (hi : i < e.getAppArgs.size), Supported known Γ (e.getAppArgs[i]) ∧
          ∃ ve, TrExprS env Us Δ (e.getAppArgs[i]) ve) →
        Erases env Us Γ Δ e t ∧ RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w') ∧
      Erasure.visitCtorEta ⊑ Erasure.visitCtorEta) ∧
    ((∀ cn ar ty fe args s ctx cctx ref w t s' w',
      visitCtorEtaGo cn ar ty fe args s ctx cctx ref w = .ok (t, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ (us : List Level) (iid : InductiveId) (cidx : Nat),
        BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ →
        Γ.ctors cn = some (iid, cidx) → Γ.ctorArities cn = some ar → ar ≤ args.size →
        cn ≠ ``Nat.zero → cn ≠ ``Nat.succ →
        (∀ i (hi : i < args.size), Supported known Γ (args[i]) ∧
          ∃ ve, TrExprS env Us Δ (args[i]) ve) →
        Erases env Us Γ Δ (args.foldl Expr.app (.const cn us)) t ∧ RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w') ∧
      Erasure.visitCtorEtaGo ⊑ Erasure.visitCtorEtaGo) ∧
    ((∀ ci e s ctx cctx ref w t s' w',
      visitCasesEta ci e s ctx cctx ref w = .ok (t, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ (con : Name) (us : List Level) (iid : InductiveId) (np dp : Nat) (nfs : List Nat),
        BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ →
        e.getAppFn = .const con us →
        Γ.casesOns con = some (iid, np) → Γ.casesDiscrPos con = some dp →
        Γ.ctorFields iid = some nfs →
        CasesInfoAgrees ci con dp nfs →
        con.getPrefix ≠ ``Nat → con.getPrefix ≠ ``Int →
        dp + 1 + nfs.length ≤ e.getAppArgs.size →
        CasesSpineFacts env Us known Γ Δ dp nfs e.getAppArgs →
        Erases env Us Γ Δ e t ∧ RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w') ∧
      Erasure.visitCasesEta ⊑ Erasure.visitCasesEta) ∧
    ((∀ ci ty fe args s ctx cctx ref w t s' w',
      visitCasesEtaGo ci ty fe args s ctx cctx ref w = .ok (t, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ (con : Name) (us : List Level) (iid : InductiveId) (np dp : Nat) (nfs : List Nat),
        BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ →
        Γ.casesOns con = some (iid, np) → Γ.casesDiscrPos con = some dp →
        Γ.ctorFields iid = some nfs →
        CasesInfoAgrees ci con dp nfs →
        con.getPrefix ≠ ``Nat → con.getPrefix ≠ ``Int →
        dp + 1 + nfs.length ≤ args.size →
        CasesSpineFacts env Us known Γ Δ dp nfs args →
        Erases env Us Γ Δ (args.foldl Expr.app (.const con us)) t ∧ RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w') ∧
      Erasure.visitCasesEtaGo ⊑ Erasure.visitCasesEtaGo) ∧
    ((∀ ci args s ctx cctx ref w t s' w',
      visitCases ci args s ctx cctx ref w = .ok (t, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ (con : Name) (us : List Level) (iid : InductiveId) (np dp : Nat) (nfs : List Nat),
        BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ →
        Γ.casesOns con = some (iid, np) → Γ.casesDiscrPos con = some dp →
        Γ.ctorFields iid = some nfs →
        CasesInfoAgrees ci con dp nfs →
        con.getPrefix ≠ ``Nat → con.getPrefix ≠ ``Int →
        dp + 1 + nfs.length ≤ args.size →
        CasesSpineFacts env Us known Γ Δ dp nfs args →
        Erases env Us Γ Δ (args.foldl Expr.app (.const con us)) t ∧ RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w') ∧
      Erasure.visitCases ⊑ Erasure.visitCases) ∧
    ((∀ nf mask e s ctx cctx ref w r s' w',
      visitAlt nf mask e s ctx cctx ref w = .ok (r, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ, BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ →
        mask = Array.replicate nf .keep →
        IsLamTelescope nf e → Supported known Γ e →
        (∃ ve, TrExprS env Us Δ e ve) →
        r.1.length = nf ∧ Erases env Us Γ Δ e (mkLambdas r.1 r.2) ∧
          RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w') ∧
      Erasure.visitAlt ⊑ Erasure.visitAlt) := by
  apply visitExpr.mutual_fixpoint_induct
    (motive_1 := fun f => (∀ e s ctx cctx ref w t s' w',
      f e s ctx cctx ref w = .ok (t, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ, BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ → Supported known Γ e →
      (∃ ve, TrExprS env Us Δ e ve) →
      Erases env Us Γ Δ e t ∧ RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w') ∧
      f ⊑ Erasure.visitExpr)
    (motive_2 := fun f => (∀ l s ctx cctx ref w r s' w',
      f l s ctx cctx ref w = .ok (r, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ (n : Nat) (iid : InductiveId),
        BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ →
        l = .natVal n → Γ.natPeano = true →
        Γ.ctors ``Nat.zero = some (iid, 0) → Γ.ctors ``Nat.succ = some (iid, 1) →
        (∃ ve, TrExprS env Us Δ (.lit l) ve) →
        Erases env Us Γ Δ (.lit l) r ∧ RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w') ∧
      f ⊑ Erasure.visitLiteral)
    (motive_3 := fun f => (∀ cn args s ctx cctx ref w t s' w',
      f cn args s ctx cctx ref w = .ok (t, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ (us : List Level) (iid : InductiveId) (cidx : Nat),
        BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ →
        Γ.ctors cn = some (iid, cidx) →
        (ctx.config.nat = .peano ∨ (cn ≠ ``Nat.zero ∧ cn ≠ ``Nat.succ)) →
        (∀ i (hi : i < args.size), Supported known Γ (args[i]) ∧
          ∃ ve, TrExprS env Us Δ (args[i]) ve) →
        Erases env Us Γ Δ (args.foldl Expr.app (.const cn us)) t ∧ RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w') ∧
      f ⊑ Erasure.visitConstructor)
    (motive_4 := fun f => (∀ e s ctx cctx ref w t s' w',
      f e s ctx cctx ref w = .ok (t, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ, BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ →
      ∀ n us, e = .const n us → (known n ∨ Γ.fixvars n ≠ none) →
      Γ.ctors n = none → Γ.casesOns n = none →
      Erases env Us Γ Δ e t ∧ RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w') ∧
      f ⊑ Erasure.visitConst)
    (motive_5 := fun f => (∀ n s ctx cctx ref w kn s' w',
      f n s ctx cctx ref w = .ok (kn, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ, BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ → known n →
      kn = Γ.constants n ∧ RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w') ∧
      f ⊑ Erasure.get_constant_kername)
    (motive_6 := fun f => (∀ n s ctx cctx ref w r s' w',
      f n s ctx cctx ref w = .ok (r, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ, BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ → known n →
      RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w' ∧ (s'.constants.get? n).isSome) ∧
      f ⊑ Erasure.visitMutual)
    (motive_7 := fun f => (∀ f' args s ctx cctx ref w t s' w',
      f f' args s ctx cctx ref w = .ok (t, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ (hd : Expr), BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ →
      Erases env Us Γ Δ hd f' →
      (∀ i (hi : i < args.size), Supported known Γ (args[i]) ∧
        ∃ ve, TrExprS env Us Δ (args[i]) ve) →
      Erases env Us Γ Δ (args.foldl Expr.app hd) t ∧ RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w') ∧
      f ⊑ Erasure.visitAppArgs)
    (motive_8 := fun f => (∀ e s ctx cctx ref w t s' w',
      f e s ctx cctx ref w = .ok (t, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ, BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ →
      ∀ n ty v b nd, e = .letE n ty v b nd → Supported known Γ e →
      (∃ ve, TrExprS env Us Δ e ve) →
      Erases env Us Γ Δ e t ∧ RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w') ∧
      f ⊑ Erasure.visitLet)
    (motive_9 := fun f => (∀ e s ctx cctx ref w t s' w',
      f e s ctx cctx ref w = .ok (t, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ, BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ →
      ∀ n ty b bi, e = .lam n ty b bi → Supported known Γ e →
      (∃ ve, TrExprS env Us Δ e ve) →
      Erases env Us Γ Δ e t ∧ RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w') ∧
      f ⊑ Erasure.visitLambda)
    (motive_10 := fun f => (∀ tn i e s ctx cctx ref w r s' w',
      f tn i e s ctx cctx ref w = .ok (r, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ (iid : InductiveId) (np nf : Nat),
        BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ →
        Γ.projs tn = some (iid, np) → Γ.ctorFields iid = some [nf] → i < nf →
        Supported known Γ e → (∃ ve, TrExprS env Us Δ e ve) →
        Erases env Us Γ Δ (.proj tn i e) r ∧ RunConclδ env Us Γ₀ Esrc s s' ∧
          gw w ≤ gw w') ∧
      f ⊑ Erasure.visitProj)
    (motive_11 := fun f => (∀ e s ctx cctx ref w t s' w',
      f e s ctx cctx ref w = .ok (t, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ, BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ → Supported known Γ e →
      (∃ ve, TrExprS env Us Δ e ve) →
      Erases env Us Γ Δ e t ∧ RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w') ∧
      f ⊑ Erasure.visitApp)
    (motive_12 := fun f => (∀ e s ctx cctx ref w t s' w',
      f e s ctx cctx ref w = .ok (t, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ, BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ → Supported known Γ e →
      (∃ ve, TrExprS env Us Δ e ve) →
      ∀ cn us, e.getAppFn = .const cn us →
      Erases env Us Γ Δ e t ∧ RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w') ∧
      f ⊑ Erasure.visitConstApp)
    (motive_13 := fun f => (∀ cn ar e s ctx cctx ref w t s' w',
      f cn ar e s ctx cctx ref w = .ok (t, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ (us : List Level) (iid : InductiveId) (cidx : Nat),
        BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ →
        e.getAppFn = .const cn us → Γ.ctors cn = some (iid, cidx) →
        Γ.ctorArities cn = some ar → ar ≤ e.getAppArgs.size →
        cn ≠ ``Nat.zero → cn ≠ ``Nat.succ →
        (∀ i (hi : i < e.getAppArgs.size), Supported known Γ (e.getAppArgs[i]) ∧
          ∃ ve, TrExprS env Us Δ (e.getAppArgs[i]) ve) →
        Erases env Us Γ Δ e t ∧ RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w') ∧
      f ⊑ Erasure.visitCtorEta)
    (motive_14 := fun f => (∀ cn ar ty fe args s ctx cctx ref w t s' w',
      f cn ar ty fe args s ctx cctx ref w = .ok (t, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ (us : List Level) (iid : InductiveId) (cidx : Nat),
        BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ →
        Γ.ctors cn = some (iid, cidx) → Γ.ctorArities cn = some ar → ar ≤ args.size →
        cn ≠ ``Nat.zero → cn ≠ ``Nat.succ →
        (∀ i (hi : i < args.size), Supported known Γ (args[i]) ∧
          ∃ ve, TrExprS env Us Δ (args[i]) ve) →
        Erases env Us Γ Δ (args.foldl Expr.app (.const cn us)) t ∧ RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w') ∧
      f ⊑ Erasure.visitCtorEtaGo)
    (motive_15 := fun f => (∀ ci e s ctx cctx ref w t s' w',
      f ci e s ctx cctx ref w = .ok (t, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ (con : Name) (us : List Level) (iid : InductiveId) (np dp : Nat) (nfs : List Nat),
        BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ →
        e.getAppFn = .const con us →
        Γ.casesOns con = some (iid, np) → Γ.casesDiscrPos con = some dp →
        Γ.ctorFields iid = some nfs →
        CasesInfoAgrees ci con dp nfs →
        con.getPrefix ≠ ``Nat → con.getPrefix ≠ ``Int →
        dp + 1 + nfs.length ≤ e.getAppArgs.size →
        CasesSpineFacts env Us known Γ Δ dp nfs e.getAppArgs →
        Erases env Us Γ Δ e t ∧ RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w') ∧
      f ⊑ Erasure.visitCasesEta)
    (motive_16 := fun f => (∀ ci ty fe args s ctx cctx ref w t s' w',
      f ci ty fe args s ctx cctx ref w = .ok (t, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ (con : Name) (us : List Level) (iid : InductiveId) (np dp : Nat) (nfs : List Nat),
        BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ →
        Γ.casesOns con = some (iid, np) → Γ.casesDiscrPos con = some dp →
        Γ.ctorFields iid = some nfs →
        CasesInfoAgrees ci con dp nfs →
        con.getPrefix ≠ ``Nat → con.getPrefix ≠ ``Int →
        dp + 1 + nfs.length ≤ args.size →
        CasesSpineFacts env Us known Γ Δ dp nfs args →
        Erases env Us Γ Δ (args.foldl Expr.app (.const con us)) t ∧ RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w') ∧
      f ⊑ Erasure.visitCasesEtaGo)
    (motive_17 := fun f => (∀ ci args s ctx cctx ref w t s' w',
      f ci args s ctx cctx ref w = .ok (t, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ (con : Name) (us : List Level) (iid : InductiveId) (np dp : Nat) (nfs : List Nat),
        BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ →
        Γ.casesOns con = some (iid, np) → Γ.casesDiscrPos con = some dp →
        Γ.ctorFields iid = some nfs →
        CasesInfoAgrees ci con dp nfs →
        con.getPrefix ≠ ``Nat → con.getPrefix ≠ ``Int →
        dp + 1 + nfs.length ≤ args.size →
        CasesSpineFacts env Us known Γ Δ dp nfs args →
        Erases env Us Γ Δ (args.foldl Expr.app (.const con us)) t ∧ RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w') ∧
      f ⊑ Erasure.visitCases)
    (motive_18 := fun f => (∀ nf mask e s ctx cctx ref w r s' w',
      f nf mask e s ctx cctx ref w = .ok (r, s') w' →
      ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
      ∀ Δ, BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ →
        mask = Array.replicate nf .keep →
        IsLamTelescope nf e → Supported known Γ e →
        (∃ ve, TrExprS env Us Δ e ve) →
        r.1.length = nf ∧ Erases env Us Γ Δ e (mkLambdas r.1 r.2) ∧
          RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w') ∧
      f ⊑ Erasure.visitAlt)
  -- 18 admissibility obligations, one per motive, all from the toolkit.
  · exact admissible_and_le _ _ (eraseM_admissible_ok₁ _)
  · exact admissible_and_le _ _ (eraseM_admissible_ok₁ _)
  · exact admissible_and_le _ _ (eraseM_admissible_ok₂ _)
  · exact admissible_and_le _ _ (eraseM_admissible_ok₁ _)
  · exact admissible_and_le _ _ (eraseM_admissible_ok₁ _)
  · exact admissible_and_le _ _ (eraseM_admissible_ok₁ _)
  · exact admissible_and_le _ _ (eraseM_admissible_ok₂ _)
  · exact admissible_and_le _ _ (eraseM_admissible_ok₁ _)
  · exact admissible_and_le _ _ (eraseM_admissible_ok₁ _)
  · exact admissible_and_le _ _ (eraseM_admissible_ok₃ _)
  · exact admissible_and_le _ _ (eraseM_admissible_ok₁ _)
  · exact admissible_and_le _ _ (eraseM_admissible_ok₁ _)
  · exact admissible_and_le _ _ (eraseM_admissible_ok₃ _)
  · exact admissible_and_le _ _ (eraseM_admissible_ok₅ _)
  · exact admissible_and_le _ _ (eraseM_admissible_ok₂ _)
  · exact admissible_and_le _ _ (eraseM_admissible_ok₄ _)
  · exact admissible_and_le _ _ (eraseM_admissible_ok₂ _)
  · exact admissible_and_le _ _ (eraseM_admissible_ok₃ _)
  -- Step 1: visitExpr — the erasability guard, then dispatch on the fragment.
  · intro vE vLit vLet vLam vProj vApp _ih1 ih2 ih8 ih9 ih10 ih11
    refine ⟨?_, ?apx⟩
    case apx =>
      rw [Erasure.visitExpr_eq_mutual]
      exact (Erasure.fix_step_le Erasure.visitExpr.mutual._proof_1
        (Erasure.mutual_le_of
          _ih1.2 ih2.2 Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl ih8.2 ih9.2 ih10.2 ih11.2 Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl)).1
    replace ih2 := ih2.1
    replace ih8 := ih8.1
    replace ih9 := ih9.1
    replace ih10 := ih10.1
    replace ih11 := ih11.1
    intro e s ctx cctx ref w t s' w' hrun Γ hΓ Δ hinv hsupp hex
    replace H := H.of_coh hΓ
    simp only [] at hrun
    -- one extra step: `visitExpr` first `read`s `ctx.lparams` for the oracle.
    rw [run_read_bind] at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨c, s₁, w₁, horc, hk⟩ := hrun
    have hs₁ : s₁ = s := run_liftMetaM_state _ _ _ _ _ horc
    subst hs₁
    obtain ⟨hle₁, hsound⟩ := H.orc_run _ _ _ _ _ _ _ _ _ horc
    by_cases hc : c = true
    · -- the oracle says: box.
      rw [if_pos hc] at hk
      rw [run_pure] at hk
      cases hk
      obtain ⟨ve, hve⟩ := hex
      obtain ⟨m, mwf, hlctx, hvlctx⟩ := hinv.mlc
      subst hvlctx
      exact ⟨.box hve (hsound hc hinv.lparams m ve mwf hlctx hinv.kfresh hve),
        RunConclδ.rfl' _, hle₁⟩
    · rw [if_neg hc] at hk
      cases hsupp with
      | bvar i =>
        -- refuted: the translation premise cannot hold on a bvar-free context.
        obtain ⟨ve, hve⟩ := hex
        cases hve with
        | bvar hfind =>
          rw [VLCtx.find?_bvar_none_of_noBV hinv.trlctx.2.noBV] at hfind
          cases hfind
      | fvar x =>
        simp only [] at hk
        rw [run_pure] at hk; cases hk
        exact ⟨.fvar x, RunConclδ.rfl' _, hle₁⟩
      | const n us hkn hctor hcases =>
        simp only [] at hk
        obtain ⟨er, hs, hle₂⟩ := ih11 _ _ _ _ _ _ _ _ _ hk Γ hΓ Δ (hinv.mono hle₁)
          (.const n us hkn hctor hcases) hex
        exact ⟨er, hs, NameGenerator.LE.trans hle₁ hle₂⟩
      | app hf ha =>
        simp only [] at hk
        obtain ⟨er, hs, hle₂⟩ := ih11 _ _ _ _ _ _ _ _ _ hk Γ hΓ Δ (hinv.mono hle₁)
          (.app hf ha) hex
        exact ⟨er, hs, NameGenerator.LE.trans hle₁ hle₂⟩
      | lam n ty bi hb =>
        simp only [] at hk
        obtain ⟨er, hs, hle₂⟩ := ih9 _ _ _ _ _ _ _ _ _ hk Γ hΓ Δ (hinv.mono hle₁)
          n ty _ bi rfl (.lam n ty bi hb) hex
        exact ⟨er, hs, NameGenerator.LE.trans hle₁ hle₂⟩
      | letE n ty nd hv hb =>
        simp only [] at hk
        obtain ⟨er, hs, hle₂⟩ := ih8 _ _ _ _ _ _ _ _ _ hk Γ hΓ Δ (hinv.mono hle₁)
          n ty _ _ nd rfl (.letE n ty nd hv hb) hex
        exact ⟨er, hs, NameGenerator.LE.trans hle₁ hle₂⟩
      | @natLit n iid hpeano hz hs =>
        -- a peano-`Nat` literal: `visitExpr` hands it to `visitLiteral`, motive 2.
        simp only [] at hk
        obtain ⟨er, hrc, hle₂⟩ := ih2 _ _ _ _ _ _ _ _ _ hk Γ hΓ Δ n iid (hinv.mono hle₁)
          rfl hpeano hz hs hex
        exact ⟨er, hrc, NameGenerator.LE.trans hle₁ hle₂⟩
      | @proj S j d iid np nf hs hnfs hi hd =>
        -- a structure projection: `visitExpr` hands it to `visitProj`, motive 10.
        -- The discriminant's translation is the sub-witness of the whole node's, read
        -- straight off `TrExprS.proj` — a projection's discriminant is a subterm.
        simp only [] at hk
        have hexd : ∃ ve, TrExprS env Us Δ d ve := by
          obtain ⟨ve, hve⟩ := hex
          cases hve with | proj htrd _ => exact ⟨_, htrd⟩
        obtain ⟨er, hrc, hle₂⟩ := ih10 _ _ _ _ _ _ _ _ _ _ _ hk Γ hΓ Δ iid np nf
          (hinv.mono hle₁) hs hnfs hi hd hexd
        exact ⟨er, hrc, NameGenerator.LE.trans hle₁ hle₂⟩
      | @casesApp con us iid np dp nfs pre minors discr hc hdp hnfs hpre hsat hnat hint
          hdiscr hlam hminors =>
        -- a `casesOn` spine; always nonempty (it contains the discriminant), so
        -- `visitExpr` dispatches to `visitApp` and motive 11 handles it.
        have hsupp' : Supported known Γ ((pre ++ discr :: minors).foldl Expr.app (.const con us)) :=
          .casesApp hc hdp hnfs hpre hsat hnat hint hdiscr hlam hminors
        obtain ⟨g, a, hga⟩ := exists_app_of_foldl_app_ne_nil (Expr.const con us)
          (args := pre ++ discr :: minors) (by simp)
        rw [hga] at hk hsupp' hex ⊢
        simp only [] at hk
        obtain ⟨er, hs, hle₂⟩ := ih11 _ _ _ _ _ _ _ _ _ hk Γ hΓ Δ (hinv.mono hle₁) hsupp' hex
        exact ⟨er, hs, NameGenerator.LE.trans hle₁ hle₂⟩
      | @ctorApp cn us iid cidx ar args hc hcases har hsat hzero hsucc hargs =>
        -- a constructor spine; `visitExpr` dispatches both `.const` (args = [])
        -- and `.app` (args ≠ []) to `visitApp`, then motive 11 handles it.
        have hsupp' : Supported known Γ (args.foldl Expr.app (.const cn us)) :=
          .ctorApp hc hcases har hsat hzero hsucc hargs
        rcases List.eq_nil_or_concat args with rfl | ⟨init, last, rfl⟩
        · simp only [List.foldl_nil] at hk hsupp' hex ⊢
          obtain ⟨er, hs, hle₂⟩ := ih11 _ _ _ _ _ _ _ _ _ hk Γ hΓ Δ (hinv.mono hle₁) hsupp' hex
          exact ⟨er, hs, NameGenerator.LE.trans hle₁ hle₂⟩
        · rw [List.concat_eq_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
            at hk hsupp' hex ⊢
          simp only [] at hk
          obtain ⟨er, hs, hle₂⟩ := ih11 _ _ _ _ _ _ _ _ _ hk Γ hΓ Δ (hinv.mono hle₁) hsupp' hex
          exact ⟨er, hs, NameGenerator.LE.trans hle₁ hle₂⟩
  -- Step 2: visitLiteral — under peano the literal is rebuilt as the constructor tower,
  -- one `visitConstructor` per `succ`, which is *literally* lean4lean's
  -- `Literal.toConstructor` step; so the case is `Erases.lit` over motive 3, and the
  -- recursion `visitLiteral → visitConstructor → visitAppArgs → visitExpr → visitLiteral`
  -- is carried by the fixpoint induction (no measure on `n` is needed). `BridgeInv.natcfg`
  -- turns the `Γ`-side flag into the reader's config, which selects the branch; the
  -- machine arms are then unreachable and `.strVal` never enters (`Supported` excludes it).
  · intro vCtor ih3
    refine ⟨?_, ?apx⟩
    case apx =>
      rw [Erasure.visitLiteral_eq_mutual]
      exact (Erasure.fix_step_le Erasure.visitExpr.mutual._proof_1
        (Erasure.mutual_le_of
          Erasure.approx_rfl Erasure.approx_rfl ih3.2 Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl)).2.1
    replace ih3 := ih3.1
    intro l s ctx cctx ref w r s' w' hrun Γ hΓ Δ n iid hinv hl hpeano hz hs hex
    subst hl
    obtain ⟨ve, hve⟩ := hex
    obtain ⟨hcl, htrC⟩ := TrExprS.lit_inv' hve
    have hpe : ctx.config.nat = .peano := hinv.natcfg hpeano
    simp only [] at hrun
    rw [run_read_bind] at hrun
    cases n with
    | zero =>
      simp only [hpe] at hrun
      obtain ⟨er, hrc, hle⟩ := ih3 _ _ _ _ _ _ _ _ _ _ hrun Γ hΓ Δ [] iid 0 hinv hz
        (.inl hpe) (fun i hi => absurd hi (by simp))
      exact ⟨.lit hcl (by
        simpa [Literal.toConstructor, Expr.natLitToConstructor, Expr.natZero,
          Expr.natSucc] using er), hrc, hle⟩
    | succ m =>
      simp only [hpe] at hrun
      -- the residual literal `m` is itself supported (this is why motive 2 reads the
      -- `Γ`-side flag and not just the config), and its translation is the argument
      -- component of the unfolding's own `TrExprS.app`.
      have hinner : ∃ ve', TrExprS env Us Δ (.lit (.natVal m)) ve' := by
        cases htrC with | app _ _ _ htra => exact ⟨_, htra⟩
      obtain ⟨er, hrc, hle⟩ := ih3 _ _ _ _ _ _ _ _ _ _ hrun Γ hΓ Δ [] iid 1 hinv hs
        (.inl hpe) (fun i hi => by
          have hi0 : i = 0 := by simpa using hi
          subst hi0
          exact ⟨.natLit m hpeano hz hs, hinner⟩)
      exact ⟨.lit hcl (by
        simpa [Literal.toConstructor, Expr.natLitToConstructor, Expr.natZero,
          Expr.natSucc] using er), hrc, hle⟩
  -- Step 3: visitConstructor — via `DataBridgeHyps.constructor_run`, reduces to
  -- `visitAppArgs (.construct iid cidx []) args`; then motive 7 + `ctor_head`.
  · intro vLit vConst vAA ih2 ih4 ih7
    refine ⟨?_, ?apx⟩
    case apx =>
      rw [Erasure.visitConstructor_eq_mutual]
      exact (Erasure.fix_step_le Erasure.visitExpr.mutual._proof_1
        (Erasure.mutual_le_of
          Erasure.approx_rfl ih2.2 Erasure.approx_rfl ih4.2 Erasure.approx_rfl
          Erasure.approx_rfl ih7.2 Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl)).2.2.1
    replace ih2 := ih2.1
    replace ih4 := ih4.1
    replace ih7 := ih7.1
    intro cn args s ctx cctx ref w t s' w' hrun Γ hΓ Δ us iid cidx hinv hct hnatdead hargfacts
    replace HD := HD.of_coh hΓ
    simp only [] at hrun
    -- (1) getConstInfo cn → ctorInfo info  (state-preserving: `run_getConstInfo_state`)
    rw [run_bind_ok] at hrun
    obtain ⟨ci, s₁, w₁, hgc, hrun⟩ := hrun
    obtain ⟨hle1, info, rfl, hcidx⟩ :=
      HD.ctorinfo_run cn iid cidx s ctx cctx ref w ci s₁ w₁ hct hgc
    have hs₁ := run_getConstInfo_state _ _ _ _ _ hgc
    subst hs₁
    simp only [] at hrun
    -- (2) getConstInfo info.induct → inductInfo indinfo
    rw [run_bind_ok] at hrun
    obtain ⟨ci2, s₂, w₂, hgc2, hrun⟩ := hrun
    obtain ⟨hle2, indinfo, rfl⟩ :=
      HD.indinfo_run cn iid cidx info _ ctx cctx ref w₁ ci2 s₂ w₂ hct hgc2
    have hs₂ := run_getConstInfo_state _ _ _ _ _ hgc2
    subst hs₂
    simp only [] at hrun
    -- (3) register_inductive indinfo → (indid, argmasks); slice reconstructs args.
    -- This is a REGISTRATION site: the state genuinely grows on the miss branch, and
    -- `run_register_inductive_runConcl` is the proved replacement for the state clause
    -- `DataBridgeHyps.reg_run` used to assert.
    rw [run_bind_ok] at hrun
    obtain ⟨rr, s₃, w₃, hreg, hrun⟩ := hrun
    obtain ⟨hle3, hindid, hslice⟩ :=
      HD.reg_run indinfo info cn iid cidx args _ ctx cctx ref w₂ rr s₃ w₃ hct hcidx hreg
    have hrc3 : RunConclδ env Us Γ₀ Esrc _ _ :=
      RunConclδ.of_runConcl_gdecls (run_register_inductive_runConcl hreg)
        (run_register_inductive_gdeclsConst hreg)
    obtain ⟨indid, argmasks⟩ := rr
    simp only at hindid; subst indid
    simp only [] at hrun
    -- (4) getEnv → env (not extern)
    rw [run_bind_ok] at hrun
    obtain ⟨env, s₄, w₄, hgenv, hrun⟩ := hrun
    obtain ⟨hle4, hextern⟩ :=
      HD.extern_run cn iid cidx _ ctx cctx ref w₃ env s₄ w₄ hct hgenv
    have hs₄ := run_getEnv_state _ _ _ _ _ hgenv
    subst hs₄
    -- (5) read ctx
    rw [run_bind_ok] at hrun
    obtain ⟨ctx', s₅, w₅, hread, hrun⟩ := hrun
    rw [run_read] at hread; cases hread
    -- (6) extern check is false → else branch
    simp only [hextern, Bool.false_and, Bool.false_eq_true, if_false] at hrun
    -- (7) read config.nat, then the `Nat`-machine match (dead for cn ≠ zero/succ);
    -- both fall-throughs go to the final `visitAppArgs`.
    rw [run_bind_ok] at hrun
    obtain ⟨ctx'', s₇, w₇, hread2, hrun⟩ := hrun
    rw [run_read] at hread2; cases hread2
    have hmono : gw w ≤ gw w₄ :=
      NameGenerator.LE.trans hle1 (NameGenerator.LE.trans hle2
        (NameGenerator.LE.trans hle3 hle4))
    have hrun2 : vAA (.construct iid info.cidx []) args s₄ ctx cctx ref w₄ = .ok (t, s') w' := by
      simp only [← hcidx] at hslice
      -- Under `.peano` the machine-`Nat` arms are dead for EVERY `cn` (the config column
      -- alone selects the fall-through); under `.machine` they are dead because `cn` is
      -- neither `Nat` constructor, which is what `simp only` reads off the context.
      rcases hnatdead with hpe | ⟨hzero, hsucc⟩
      · simp only [hpe] at hrun
        rw [hslice] at hrun
        exact hrun
      · rcases hcnat : ctx.config.nat with _ | _ <;>
          simp only [hcnat] at hrun <;>
          · rw [hslice] at hrun
            exact hrun
    obtain ⟨erap, hs', hle⟩ := ih7 _ _ _ _ _ _ _ _ _ _ hrun2 Γ hΓ Δ (Expr.const cn us)
      ((hinv.mono_state hrc3.rc).mono hmono)
      (.ctor_head cn us iid info.cidx (by rw [hcidx]; exact hct)) hargfacts
    exact ⟨erap, hrc3.trans hs', NameGenerator.LE.trans hmono hle⟩
  -- Step 4: visitConst — BOTH branches (recursion wall, W3.1). The fixvar branch returns
  -- the block's fresh fvar and is `Erases.fixvar`, against `BridgeInv`'s fixvar
  -- agreement and freshness; the plain branch is `Erases.const` via motive 5. `hkn` is
  -- the disjunction `Supported.const` now carries: the constant is registered, or it is
  -- an in-block sibling — and in the latter case the agreement *forces* the fixvar
  -- branch, which is what makes the plain branch's `known n` recoverable.
  · intro gck ih5
    refine ⟨?_, ?apx⟩
    case apx =>
      rw [Erasure.visitConst_eq_mutual]
      exact (Erasure.fix_step_le Erasure.visitExpr.mutual._proof_1
        (Erasure.mutual_le_of
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl ih5.2
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl)).2.2.2.1
    replace ih5 := ih5.1
    intro e s ctx cctx ref w t s' w' hrun Γ hΓ Δ hinv n us he hkn hctor hcases
    subst he
    simp only [] at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨c, s₁, w₁, hrd, hk⟩ := hrun
    rw [run_read] at hrd
    cases hrd
    cases hopt : ctx.fixvars.bind (fun hmap => hmap[n]?) with
    | some id =>
      -- The sibling branch: `return .fvar id`, pure in state and world.
      rw [hopt] at hk
      simp only [] at hk
      rw [run_pure] at hk
      cases hk
      exact ⟨.fixvar n us id ((hinv.fixvars n id).mp hopt) hctor hcases
          (hinv.fixfresh n id ((hinv.fixvars n id).mp hopt)).2,
        RunConclδ.rfl' _, NameGenerator.LE.rfl⟩
    | none =>
      -- The registered branch. `Γ.fixvars n ≠ none` is refuted here by the agreement:
      -- it would make the run's own lookup a `some`.
      have hkn' : known n := by
        rcases hkn with hkn' | hfx
        · exact hkn'
        · obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hfx
          rw [(hinv.fixvars n x).mpr hx] at hopt
          exact absurd hopt (by simp)
      rw [hopt] at hk
      simp only [] at hk
      rw [run_bind_ok] at hk
      obtain ⟨kn, s₂, w₂, hgck, hp2⟩ := hk
      rw [run_pure] at hp2; cases hp2
      obtain ⟨hknE, hs, hle⟩ := ih5 _ _ _ _ _ _ _ _ _ hgck Γ hΓ Δ hinv hkn'
      exact ⟨.const n us kn hknE.symm hctor hcases, hs, hle⟩
  -- Step 5: get_constant_kername — BOTH branches (δ-inclusion, D4a). The hit branch
  -- reads the kername off the registry and is `Γ`-sound by `BridgeInv.consts`. The miss
  -- branch — the one a *cold* run actually takes, and the one the deleted
  -- `BridgeInv.known_dom` used to rule out by fiat — returns `s'.constants[n]!` after
  -- `visitMutual n`; it closes on motive 6's registration conclusion (which makes the
  -- `panic!`-defaulting lookup total) plus `RunConcl.canon` (which makes it canonical at
  -- the *post*-state, where `hinv.consts` no longer applies), exactly as
  -- `BridgeInv.mono_state` re-establishes soundness after a sub-run.
  · intro _vMut ih6
    refine ⟨?_, ?apx⟩
    case apx =>
      rw [Erasure.get_constant_kername_eq_mutual]
      exact (Erasure.fix_step_le Erasure.visitExpr.mutual._proof_1
        (Erasure.mutual_le_of
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl ih6.2 Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl)).2.2.2.2.1
    replace ih6 := ih6.1
    intro n s ctx cctx ref w kn s' w' hrun Γ hΓ Δ hinv hkn
    simp only [] at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨s₀, s₁, w₁, hget, hk⟩ := hrun
    rw [run_get] at hget
    cases hget
    cases hcs : s.constants.get? n with
    | some kn₀ =>
      rw [hcs] at hk
      simp only [] at hk
      rw [run_pure] at hk
      cases hk
      exact ⟨hinv.consts hcs, RunConclδ.rfl' _, NameGenerator.LE.rfl⟩
    | none =>
      rw [hcs] at hk
      simp only [] at hk
      rw [run_bind_ok] at hk
      obtain ⟨uu, s₂, w₂, hvm, hk2⟩ := hk
      rw [run_bind_ok] at hk2
      obtain ⟨s₃, s₄, w₄, hget2, hp⟩ := hk2
      rw [run_get] at hget2
      cases hget2
      rw [run_pure] at hp
      cases hp
      obtain ⟨hrc, hle, hdom⟩ := ih6 _ _ _ _ _ _ _ _ _ hvm Γ hΓ Δ hinv hkn
      obtain ⟨kn₀, hkn₀⟩ := Option.isSome_iff_exists.mp hdom
      refine ⟨?_, hrc, hle⟩
      rw [hashMap_get!_of_get? hkn₀, hinv.knames n]
      exact hrc.rc.canon (fun {m} {k'} hm => (hinv.consts hm).trans (hinv.knames m)) hkn₀
  -- Step 6: visitMutual — the δ-inclusion content (D4a), and the one genuinely new
  -- inductive argument of the slice. Its shape is `ColdStartInduction`'s step 6 (the
  -- output-shape induction walks the same four exits), with two differences forced by
  -- the conclusion: the world is indexed as well as the state, so every
  -- state-transparent primitive on the path still needs a generator clause
  -- (`DeltaHyps`' bookkeeping group — `BridgeHyps` specs the *term* path's primitives,
  -- not these); and the erasure IH is conditional, so the dependency's body has to
  -- arrive with a `BridgeInv`, a `Supported` and a `TrExprS`. The invariant is rebuilt
  -- field by field at the dependency's reader (`withReader` moves `fixvars` and
  -- `lparams` and nothing else, `Erasure.lean:889`), and the other two come from
  -- `DeltaHyps.prepared` — the fragment's defining scope statement.
  · intro vE ih1
    refine ⟨?_, ?apx⟩
    case apx =>
      rw [Erasure.visitMutual_eq_mutual]
      exact (Erasure.fix_step_le Erasure.visitExpr.mutual._proof_1
        (Erasure.mutual_le_of
          ih1.2 Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl)).2.2.2.2.2.1
    obtain ⟨ih1, _hap1⟩ := ih1
    intro n s ctx cctx ref w u s₁ w₁ hrun Γ hΓ Δ hinv hkn
    simp only [] at hrun
    -- (1) the declaration fetch. State-transparent; `DeltaHyps.decl_run` pins what it
    -- returns, and every branch below is a function of that.
    rw [run_bind_ok] at hrun
    obtain ⟨di, sa, wa, hdi, hrun⟩ := hrun
    have hsa := run_liftCoreM_state (x := (Compiler.LCNF.getDeclInfo? n : CoreM _))
      _ _ cctx ref _ hdi
    subst sa
    have hdiC := ((run_liftCoreM_ok _ _ cctx ref _).mp hdi).1
    obtain ⟨hled, ci, hci, hknall, hnd, hnmem, hlp⟩ := (Hδ cctx ref).decl_run hkn hdiC
    have hdg : di.get! = ci := by rw [hci]; rfl
    rw [hdg] at hrun
    -- (2) getEnv, for the `@[inline]` attribute lookup.
    rw [run_bind_ok] at hrun
    obtain ⟨env0, sb, wb, henv0, hrun⟩ := hrun
    have hsb := run_getEnv_state _ _ cctx ref _ henv0
    subst sb
    have hle : gw w ≤ gw wb :=
      NameGenerator.LE.trans hled ((Hδ cctx ref).env_run henv0)
    have hrc : RunConclδ env Us Γ₀ Esrc s s := RunConclδ.rfl' _
    clear hdi henv0
    -- (3) the run's own test, `ci.all.length == 1`, decides whether the axiom/inline
    -- prefix is entered at all. Both arms are walked since slice Γ-W5: `decl_run` no
    -- longer pins `ci.all` at one declaration, it pins the *block* against the fragment
    -- (`hknall`/`hnd`/`hnmem`), which is what the recursive exit consumes either way.
    split at hrun
    case isFalse hns =>
      -- (3b) **A GENUINE MUTUAL BLOCK** (slice Γ-W5). At `ci.all.length ≠ 1` the shipping
      -- eraser skips the whole `@[inline]`/`value?`/`isExtern` prefix — `single_decl` is
      -- the guard on all of it — and `nonrecursive`, being `single_decl && …`, is `false`
      -- too. So the run goes straight to the block exit, and the path here is *shorter*
      -- than the single-declaration one below: no inline prefix, no `getEnv`, no `logInfo`
      -- world steps, no axiom exits to discharge. The walk is the same
      -- `rec_exit_refines_erases` call as (6c), at the same three side conditions —
      -- which is the whole content of the slice: the walk was arity-general already, and
      -- what stood in the way was `decl_run`'s `ci.all = [m]`.
      split at hrun
      case isTrue hnr => exact absurd (Bool.and_eq_true .. |>.mp hnr).1 hns
      case isFalse =>
        have hinvr := (hinv.mono_state hrc.rc).mono hle
        obtain ⟨hrcb, hleb, hdom⟩ :=
          rec_exit_refines_erases H (Hδ cctx ref) (Hβ cctx ref) henv
            (fun e s' ctx' w' t s'' w'' hr => ih1 e s' ctx' cctx ref w' t s'' w'' hr)
            _hap1 hΓ hknall hnd hnmem hinvr
            (Hreg cctx ref hknall hnd hinvr) hrun
        exact ⟨hrc.trans hrcb, NameGenerator.LE.trans hle hleb, hdom⟩
    case isTrue =>
      -- (4) the `@[inline]` prefix: `inlinings` only, and one `logInfo` world step.
      obtain ⟨s₀, w₀, u₀, hpre, hrun⟩ := run_inline_prefix_decomp' hrun
      obtain ⟨hrc, hle⟩ : RunConclδ env Us Γ₀ Esrc s s₀ ∧ gw w ≤ gw w₀ := by
        rcases hpre with ⟨rfl, rfl⟩ | ⟨u', hlog, rfl⟩
        · exact ⟨hrc, hle⟩
        · exact ⟨hrc.trans (RunConclδ.of_runConcl_gdecls (runConcl_inlinings _ _) (fun h => h)),
            NameGenerator.LE.trans hle ((Hδ cctx ref).log_run hlog)⟩
      -- (5) the `value?` / `isExtern` / `config.extern` match.
      rw [run_bind_ok] at hrun
      obtain ⟨env2, se, we, henv2, hrun⟩ := hrun
      have hz := run_getEnv_state _ _ cctx ref _ henv2
      subst se
      replace hle := NameGenerator.LE.trans hle ((Hδ cctx ref).env_run henv2)
      rw [run_bind_ok] at hrun
      obtain ⟨c1, sr, wr, hread, hrun⟩ := hrun
      rw [run_read] at hread
      cases hread
      clear henv2
      -- The `value!`/`value?` reconciliation, and *only* that: until Γ-W3.6b this `have`
      -- also carried `DeltaHyps.nonrecursive`'s `name_occurs n v = false`, the field whose
      -- whole job was to refute the recursive branch below. The field is gone; the branch
      -- is walked.
      have hkey : ∀ v : Expr, ci.value? (allowOpaque := true) = some v →
          ci.value! (allowOpaque := true) = v :=
        fun v hv => constantInfo_value!_of_value? hv
      cases hval : ci.value? (allowOpaque := true) <;>
        cases hext : isExtern env2 n <;>
          cases hcfg : ctx.config.extern <;>
            simp only [hval, hext, hcfg] at hrun
      all_goals
        try
          (rw [run_bind_ok] at hrun
           obtain ⟨u3, s3, w3, hlog, hrun⟩ := hrun
           have hz2 := run_logInfo_state _ _ cctx ref _ hlog
           subst s3
           replace hle := NameGenerator.LE.trans hle ((Hδ cctx ref).log_run hlog))
      all_goals
        first
          -- (6a) the two axiom exits: the world does not move, and the registration is
          -- the `addAxiom` insert itself.
          | (obtain ⟨rfl, rfl⟩ := run_addAxiom_ok hrun
             exact ⟨hrc.trans (RunConclδ.addAxiom n _), hle, addAxiomState_get? n _⟩)
          | (split at hrun
             case isFalse _hnr =>
               -- (6c) **THE RECURSIVE EXIT, WALKED** (recursion wall, slice Γ-W3.6b).
               --
               -- Until this slice the branch was closed by `DeltaHyps.nonrecursive`, a
               -- fragment restriction whose only job was to make the run's `nonrecursive`
               -- test `true` so that the exit was unreachable. That field is deleted and
               -- this is what stands in its place: `rec_exit_refines_erases` takes an
               -- abstract eraser, its motive-1 refinement hypothesis and its approximation
               -- conjunct — precisely the pair `ih1` is here — and derives all three
               -- conjuncts of this motive from the block's four loops. Guard (iv'') is
               -- this composition, at exactly this data.
               --
               -- The two premises the walk does not derive are the ones the theorem now
               -- takes: `Hβ`, the block-local scope bundle (Γ-W2), and `Hreg`,
               -- `RecBlockAgreement` — `Erases.fix`'s own registration premise, gated on
               -- the fragment and on the invariant this step holds. Γ-W3.5 could not
               -- state `Hreg`, because its reader quantifier admitted two configs and two
               -- configs erase the same block to different `defs`; Γ-W3.6a's
               -- `BridgeInv.cfg` is what closes that, and `BridgeInv.consts`/`knames`
               -- close the registry half.
               --
               -- The block is `ci.all`, and the three side conditions the walk asks for
               -- are `decl_run`'s own three conjuncts since slice Γ-W5 — no longer
               -- derived from `ci.all = [mn]`, which is why the same four lines serve
               -- this arm and the multi-declaration one above.
               --
               -- WHAT REMAINS, precisely, now that the branch is walked:
               --   * `hnorec` at the *capstones* — **paid at slice Γ-W4**, and so no
               --     longer a remainder: `recEnvConsistent_of_noRec` gave way to
               --     `ColdStartDelta.recEnvConsistent_of_deltaMem_walked`, this exit's
               --     `.fix` registration travels in the cold-start δ record, and the
               --     restriction is deleted (`ColdStart`'s `hrec`/`hcov` rows);
               --   * the **single-declaration** scope — **paid at slice Γ-W5**. It was
               --     `DeltaHyps.decl_run`'s (`ci.all = [m]`), never this branch's, and the
               --     relaxation is the block-membership closure condition in its place;
               --   * nothing about arity. The walk and `RecBlockAgreement` were stated at
               --     an arbitrary `names` from the start.
               have hinvr := (hinv.mono_state hrc.rc).mono hle
               obtain ⟨hrcb, hleb, hdom⟩ :=
                 rec_exit_refines_erases H (Hδ cctx ref) (Hβ cctx ref) henv
                   (fun e s' ctx' w' t s'' w'' hr => ih1 e s' ctx' cctx ref w' t s'' w'' hr)
                   _hap1 hΓ hknall hnd hnmem hinvr
                   (Hreg cctx ref hknall hnd hinvr) hrun
               exact ⟨hrc.trans hrcb, NameGenerator.LE.trans hle hleb, hdom⟩
             case isTrue =>
               -- (6b) the non-recursive exit — the content arm.
               rw [run_bind_ok] at hrun
               obtain ⟨t, st, wt, hvis, hrun⟩ := hrun
               rw [run_withReader, run_bind_ok] at hvis
               obtain ⟨pe, sp, wp, hpr, hvis⟩ := hvis
               obtain ⟨hlep, hsp⟩ := (Hδ cctx ref).prep_run hpr
               subst sp
               replace hle := NameGenerator.LE.trans hle hlep
               -- the dependency's body is in the fragment: `Esrc` records its prepared
               -- form (`prep_esrc`, keyed on the same two runs we hold), and the
               -- fragment says that form is `Supported` and translatable.
               rw [(hkey _ hval)] at hpr
               have hlink : Esrc n = some pe :=
                 (Hδ cctx ref).prep_esrc hkn hdiC hci hval hpr hinv.cfg
               obtain ⟨hsupp, htr⟩ := (Hδ cctx ref).prepared hkn hlink hpr
               -- the invariant travels to the dependency's reader: `withReader` moves
               -- `fixvars` (to `none`, which `DeltaHyps.nofixvars` matches) and
               -- `lparams` (to the declaration's own, which `decl_run` pins at `Us`).
               -- Both fixvar slots are reached only under `hkn : known n`, which is why
               -- `nofixvars` can be — and since slice δ-D8 is — conditioned on the
               -- fragment.
               -- …and it lands at the **ambient** `Γ₀`, not at this step's own `Γ`
               -- (slice Γ-W1). The callee's reader carries `fixvars := none`, and the
               -- only context whose `fixvars` is provably `⊥` on the fragment is `Γ₀`:
               -- that is what `DeltaHyps.nofixvars` — retargeted to `Γ₀` — says. The
               -- motive-local `Γ` is arbitrary, so `BridgeInv.fixvars`' iff is simply
               -- false there. Every other field is `Γ₀`'s already, up to the two
               -- registration projections the coherence equation shares.
               have hinvb := (hinv.mono_state hrc.rc).mono hle
               have hinv' : BridgeInv env Us known Γ₀ cfg₀ (gw wp)
                   { ctx with fixvars := none, lparams := ci.levelParams } s₀ Δ :=
                 { mlc := hinvb.mlc
                   lparams := hlp
                   cfg := hinvb.cfg
                   natcfg := fun h => hinvb.natcfg ((ErasureCtx.coh_natPeano hΓ).trans h)
                   kfresh := hinvb.kfresh
                   fixvars := by
                     intro nm x
                     show (none : Option (Std.HashMap Name FVarId)).bind _ = _ ↔ _
                     rw [(Hδ cctx ref).nofixvars hkn]
                     simp
                   fixfresh := by
                     intro nm x hx
                     rw [(Hδ cctx ref).nofixvars hkn] at hx
                     simp at hx
                   reserved := hinvb.reserved
                   knames := by
                     intro m
                     rw [← ErasureCtx.coh_constants hΓ]
                     exact hinvb.knames m
                   consts := by
                     intro m k hk
                     rw [← ErasureCtx.coh_constants hΓ]
                     exact hinvb.consts hk }
               obtain ⟨herv, hrcv, hlev⟩ := ih1 _ _ _ _ _ _ _ _ _ hvis Γ₀ rfl Δ hinv' hsupp (htr Δ)
               replace hle := NameGenerator.LE.trans hle hlev
               replace hrc := hrc.trans hrcv
               -- the registration, then the inlining tail (which registers nothing).
               rw [run_bind_ok] at hrun
               obtain ⟨u2, sm, wm, hmod, hrun⟩ := hrun
               rw [run_modify] at hmod
               cases hmod
               rw [run_bind_ok] at hrun
               obtain ⟨c2, sc, wc, hread2, hrun⟩ := hrun
               rw [run_read] at hread2
               cases hread2
               refine run_inline_tail_ok'
                 (P := fun s' w' => RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w' ∧
                   (s'.constants.get? n).isSome)
                 (fun hP => ⟨hP.1.trans (RunConclδ.inlinings _ _), hP.2.1, hP.2.2⟩)
                 (fun hl hP => by
                   obtain rfl := run_logInfo_state _ _ cctx ref _ hl
                   exact ⟨hP.1, NameGenerator.LE.trans hP.2.1 ((Hδ cctx ref).log_run hl),
                     hP.2.2⟩)
                 (fun hi hP => by
                   obtain rfl := run_liftCoreM_state _ _ cctx ref _ hi
                   exact ⟨hP.1, NameGenerator.LE.trans hP.2.1 ((Hδ cctx ref).inst_run hi),
                     hP.2.2⟩)
                 ⟨hrc.trans (RunConclδ.nonrec (hinv'.knames n)
                     (fun {m} hm hkey' => (Hδ cctx ref).kinj
                       ((Hδ cctx ref).esrc_sub hm) hkn hkey')
                     (fun {body} hb => ⟨Δ, hinv'.vlctx_wf, hinv'.noBV, by
                       obtain rfl : body = pe := by
                         rw [hlink] at hb; exact (Option.some.inj hb).symm
                       exact herv⟩)),
                   hle, nonrecConstState_get? n t _⟩
                 hrun)
  -- Step 7: visitAppArgs — the Array.foldlM loop rule with the prefix-spine
  -- invariant.
  · intro vE ih1
    refine ⟨?_, ?apx⟩
    case apx =>
      rw [Erasure.visitAppArgs_eq_mutual]
      exact (Erasure.fix_step_le Erasure.visitExpr.mutual._proof_1
        (Erasure.mutual_le_of
          ih1.2 Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl)).2.2.2.2.2.2.1
    replace ih1 := ih1.1
    intro f' args s ctx cctx ref w t s' w' hrun Γ hΓ Δ hd hinv herf hargs
    simp only [] at hrun
    have hmem : ∀ a ∈ args.toList, Supported known Γ a ∧ ∃ ve, TrExprS env Us Δ a ve := by
      intro a ha
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
      have hi' : i < args.size := by simpa using hi
      have := hargs i hi'
      simpa using this
    have hP := run_array_foldlM_ok ctx cctx ref
      (P := fun pre acc s₁ w₁ =>
        Erases env Us Γ Δ (pre.foldl Expr.app hd) acc ∧ RunConclδ env Us Γ₀ Esrc s s₁ ∧ gw w ≤ gw w₁)
      ⟨herf, RunConclδ.rfl' _, NameGenerator.LE.rfl⟩
      (fun pre x post acc s₁ w₁ acc' s₂ w₂ hLpre hPacc hg => by
        rw [run_bind_ok] at hg
        obtain ⟨tx, s₃, w₃, hvx, hp⟩ := hg
        rw [run_pure] at hp
        cases hp
        obtain ⟨hErpre, hrc, hle⟩ := hPacc
        obtain ⟨hsx, hex⟩ := hmem x (by rw [hLpre]; exact List.mem_append_right _ List.mem_cons_self)
        obtain ⟨erx, hs₃, hle₂⟩ := ih1 _ _ _ _ _ _ _ _ _ hvx Γ hΓ Δ
          ((hinv.mono_state hrc.rc).mono hle) hsx hex
        refine ⟨?_, hrc.trans hs₃, NameGenerator.LE.trans hle hle₂⟩
        rw [List.foldl_append]
        exact .app hErpre erx)
      hrun
    obtain ⟨hEr, hs', hle⟩ := hP
    refine ⟨?_, hs', hle⟩
    rwa [Array.foldl_toList] at hEr
  -- Step 8: visitLet — open the binder, erase value and opened body in the
  -- extended context, close with `bridge_let_case`.
  · intro vE ih1
    refine ⟨?_, ?apx⟩
    case apx =>
      rw [Erasure.visitLet_eq_mutual]
      exact (Erasure.fix_step_le Erasure.visitExpr.mutual._proof_1
        (Erasure.mutual_le_of
          ih1.2 Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl)).2.2.2.2.2.2.2.1
    replace ih1 := ih1.1
    intro e s ctx cctx ref w t s' w' hrun Γ hΓ Δ hinv n ty v b nd he hsupp hex
    replace H := H.of_coh hΓ
    subst he
    simp only [] at hrun
    unfold Erasure.letMonocular at hrun
    simp only [] at hrun
    unfold Erasure.withLocalDef at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨x, s₁, w₁, hfresh, hk⟩ := hrun
    obtain ⟨hnres, hres, hle₁, hkres⟩ := H.fresh_run _ _ _ _ _ _ _ _ hfresh
    have hs₁ : s₁ = s := run_mkFreshFVarId_state _ _ _ _ _ hfresh
    subst hs₁
    rw [run_withReader] at hk
    rw [run_bind_ok] at hk
    obtain ⟨tv, s₂, w₂, hvv, hk2⟩ := hk
    rw [run_bind_ok] at hk2
    obtain ⟨tb, s₃, w₃, hvb, hm⟩ := hk2
    obtain ⟨hv, hb⟩ := hsupp.letE_inv
    obtain ⟨ve, hve⟩ := hex
    cases hve with
    | letE hvt hty hval hbody =>
    have hx : x ∉ Δ.fvars := fun hmem => hnres (hinv.reserved x hmem)
    have hΔ' := LeanToLambdaBox.TrLCtx.mkLetDecl (n := n) (nd := false) hinv.trlctx
      (hinv.trlctx.find?_eq_none.mpr hx) hty hval hvt
    have hinv' := hinv.mkLetDecl (n := n) hty hval hvt hx hnres hle₁ hres hkres
    -- the value, in the extended context
    have hvext := hval.weakFV henv (.skip_fvar _ _ .refl) hΔ'.wf
    obtain ⟨erv, hs₂, hle₂⟩ := ih1 _ _ _ _ _ _ _ _ _ hvv Γ hΓ _ hinv' hv ⟨_, hvext⟩
    -- the opened body, in the extended context
    rw [Lean.Expr.instantiate1_eq] at hvb
    have hbext := TrExprS.inst_fvar henv hΔ'.wf hbody
    obtain ⟨erb, hs₃, hle₃⟩ := ih1 _ _ _ _ _ _ _ _ _ hvb Γ hΓ _
      ((hinv'.mono_state hs₂.rc).mono hle₂) (hb.instantiate1' x 0) ⟨_, hbext⟩
    -- the mkLetIn tail
    unfold Erasure.mkLetIn at hm
    rw [run_bind_ok] at hm
    obtain ⟨bn, s₄, w₄, hf2n, hp⟩ := hm
    rw [run_pure] at hp
    cases hp
    have hdn : ((ctx.lctx.mkLetDecl x n ty v).fvarIdToDecl.find! x).userName = n := by
      rw [LocalContext.fvarIdToDecl_find!_of_find?
        (LocalContext.find?_mkLetDecl_self hinv.trlctx.1 (hinv.trlctx.find?_eq_none.mpr hx))]
      rfl
    cases (run_fvar_to_name x n _ { ctx with lctx := ctx.lctx.mkLetDecl x n ty v }
      cctx ref _ hdn).symm.trans hf2n
    refine ⟨?_, hs₂.trans hs₃, NameGenerator.LE.trans hle₁ (NameGenerator.LE.trans hle₂ hle₃)⟩
    rw [abstract_eq]
    exact bridge_let_case hinv.trlctx.2.noBV hty hval hbody hx erv erb
  -- Step 9: visitLambda — open the binder, erase the opened body in the
  -- extended context, close with `bridge_lam_case`.
  · intro vE ih1
    refine ⟨?_, ?apx⟩
    case apx =>
      rw [Erasure.visitLambda_eq_mutual]
      exact (Erasure.fix_step_le Erasure.visitExpr.mutual._proof_1
        (Erasure.mutual_le_of
          ih1.2 Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl)).2.2.2.2.2.2.2.2.1
    replace ih1 := ih1.1
    intro e s ctx cctx ref w t s' w' hrun Γ hΓ Δ hinv n ty b bi he hsupp hex
    replace H := H.of_coh hΓ
    subst he
    simp only [] at hrun
    unfold Erasure.lambdaMonocular at hrun
    simp only [] at hrun
    unfold Erasure.withLocalDecl at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨x, s₁, w₁, hfresh, hk⟩ := hrun
    obtain ⟨hnres, hres, hle₁, hkres⟩ := H.fresh_run _ _ _ _ _ _ _ _ hfresh
    have hs₁ : s₁ = s := run_mkFreshFVarId_state _ _ _ _ _ hfresh
    subst hs₁
    rw [run_withReader] at hk
    rw [run_bind_ok] at hk
    obtain ⟨tb, s₂, w₂, hvb, hm⟩ := hk
    have hb := hsupp.lam_inv
    obtain ⟨ve, hve⟩ := hex
    cases hve with
    | lam hty' hty hbody =>
    have hx : x ∉ Δ.fvars := fun hmem => hnres (hinv.reserved x hmem)
    have hΔ' := LeanToLambdaBox.TrLCtx.mkLocalDecl (n := n) (bi := bi) hinv.trlctx
      (hinv.trlctx.find?_eq_none.mpr hx) hty hty'
    have hinv' := hinv.mkLocalDecl (n := n) (bi := bi) hty hty' hx hnres hle₁ hres hkres
    rw [Lean.Expr.instantiate1_eq] at hvb
    have hbext := TrExprS.inst_fvar henv hΔ'.wf hbody
    obtain ⟨erb, hs₂, hle₂⟩ := ih1 _ _ _ _ _ _ _ _ _ hvb Γ hΓ _ hinv'
      (hb.instantiate1' x 0) ⟨_, hbext⟩
    unfold Erasure.mkLambda at hm
    rw [run_bind_ok] at hm
    obtain ⟨bn, s₃, w₃, hf2n, hp⟩ := hm
    rw [run_pure] at hp
    cases hp
    have hdn : ((ctx.lctx.mkLocalDecl x n ty bi).fvarIdToDecl.find! x).userName = n := by
      rw [LocalContext.fvarIdToDecl_find!_of_find?
        (LocalContext.find?_mkLocalDecl_self hinv.trlctx.1 (hinv.trlctx.find?_eq_none.mpr hx))]
      rfl
    cases (run_fvar_to_name x n _ { ctx with lctx := ctx.lctx.mkLocalDecl x n ty bi }
      cctx ref _ hdn).symm.trans hf2n
    refine ⟨?_, hs₂, NameGenerator.LE.trans hle₁ hle₂⟩
    rw [abstract_eq]
    exact bridge_lam_case hinv.trlctx.2.noBV hty hbody hx erb
  -- Step 10: visitProj — the structure-info fetch, the registration, the mask
  -- arithmetic, and the discriminant's own erasure.
  · intro vE ih1
    refine ⟨?_, ?apx⟩
    case apx =>
      rw [Erasure.visitProj_eq_mutual]
      exact (Erasure.fix_step_le Erasure.visitExpr.mutual._proof_1
        (Erasure.mutual_le_of
          ih1.2 Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl)).2.2.2.2.2.2.2.2.2.1
    replace ih1 := ih1.1
    intro tn i e s ctx cctx ref w r s' w' hrun Γ hΓ Δ iid np nf hinv hprojs hnfs hi hsupp hex
    replace P := P.of_coh hΓ
    simp only [] at hrun
    -- (1) `getConstInfo tn` → the structure's `inductInfo`; state-preserving by
    -- `run_getConstInfo_state`, so the `unreachable!` arm is dead and `np` is pinned.
    rw [run_bind_ok] at hrun
    obtain ⟨ci, s₁, w₁, hci, hrun⟩ := hrun
    obtain ⟨hle₁, indVal, rfl, hnp, hname⟩ :=
      P.projind_run tn iid np _ ctx cctx ref w _ s₁ w₁ hprojs hci
    have hs₁ := run_getConstInfo_state _ _ _ _ _ hci
    subst hs₁
    simp only [] at hrun
    -- (2) `register_inductive` → `Γ`'s `InductiveId` and the single trivial argmask.
    -- Its state effect is the *theorem* `run_register_inductive_runConcl`, not a clause.
    rw [run_bind_ok] at hrun
    obtain ⟨rr, s₂, w₂, hreg, hrun⟩ := hrun
    obtain ⟨hle₂, hindid, hmlen, hmask⟩ :=
      P.projreg_run indVal tn iid np nf _ ctx cctx ref w₁ rr s₂ w₂ hprojs hnfs hname hreg
    have hrc₂ : RunConclδ env Us Γ₀ Esrc _ _ :=
      RunConclδ.of_runConcl_gdecls (run_register_inductive_runConcl hreg)
        (run_register_inductive_gdeclsConst hreg)
    obtain ⟨indid, argmasks⟩ := rr
    simp only [] at hindid hmlen hmask
    subst hindid
    -- (3) the discriminant, by the one induction hypothesis this step has.
    rw [run_bind_ok] at hrun
    obtain ⟨tb, s₃, w₃, hvb, hp⟩ := hrun
    rw [run_pure] at hp
    cases hp
    obtain ⟨erd, hrc₃, hle₃⟩ := ih1 _ _ _ _ _ _ _ _ _ hvb Γ hΓ Δ
      ((hinv.mono_state hrc₂.rc).mono (NameGenerator.LE.trans hle₁ hle₂)) hsupp hex
    -- (4) the emitted `fieldIdx` is `i`: the mask is trivial of width `nf`, and `i < nf`.
    have hfield : Array.count ConstructorArgRelevance.keep
        (Std.Slice.toArray (Array.toSubarray argmasks[0]! 0 i)) = i := by
      rw [hmask]; exact count_keep_take_replicate (Nat.le_of_lt hi)
    rw [hfield, hnp]
    exact ⟨.proj tn i _ np nf hprojs hnfs hi erd, hrc₂.trans hrc₃,
      NameGenerator.LE.trans hle₁ (NameGenerator.LE.trans hle₂ hle₃)⟩
  -- Step 11: visitApp — dispatch on the head: const heads to visitConstApp,
  -- other heads through visitExpr + visitAppArgs and the spine reconstruction.
  · intro vE vAA vCA ih1 ih7 ih12
    refine ⟨?_, ?apx⟩
    case apx =>
      rw [Erasure.visitApp_eq_mutual]
      exact (Erasure.fix_step_le Erasure.visitExpr.mutual._proof_1
        (Erasure.mutual_le_of
          ih1.2 Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl ih7.2 Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl ih12.2 Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl)).2.2.2.2.2.2.2.2.2.2.1
    replace ih1 := ih1.1
    replace ih7 := ih7.1
    replace ih12 := ih12.1
    intro e s ctx cctx ref w t s' w' hrun Γ hΓ Δ hinv hsupp hex
    simp only [] at hrun
    cases hfn : e.getAppFn
    case const cn us =>
      rw [hfn] at hrun
      simp only [] at hrun
      exact ih12 _ _ _ _ _ _ _ _ _ hrun Γ hΓ Δ hinv hsupp hex cn us hfn
    all_goals (
      -- non-const head: `hsupp` is not a `ctorApp`, so `spine_arg_facts` applies
      have hnc : ∀ cn us, e.getAppFn = .const cn us → Γ.ctors cn = none := by
        intro cn us h; rw [hfn] at h; exact absurd h (by simp)
      have hncs : ∀ cn us, e.getAppFn = .const cn us → Γ.casesOns cn = none := by
        intro cn us h; rw [hfn] at h; exact absurd h (by simp)
      obtain ⟨⟨hsuppfn, fve, htrfn⟩, hargfacts⟩ := spine_arg_facts hnc hncs hsupp hex
      rw [hfn] at hrun
      simp only [] at hrun
      rw [expr_withApp_eq] at hrun
      rw [run_bind_ok] at hrun
      obtain ⟨tf, s₁, w₁, hvf, hk⟩ := hrun
      obtain ⟨erf, hs₁, hle₁⟩ := ih1 _ _ _ _ _ _ _ _ _ hvf Γ hΓ Δ hinv hsuppfn ⟨fve, htrfn⟩
      obtain ⟨erapp, hs', hle₂⟩ := ih7 _ _ _ _ _ _ _ _ _ _ hk Γ hΓ Δ e.getAppFn
        ((hinv.mono_state hs₁.rc).mono hle₁) erf hargfacts
      rw [getAppArgs_spine'] at erapp
      exact ⟨erapp, hs₁.trans hs', NameGenerator.LE.trans hle₁ hle₂⟩)
  -- Step 12: visitConstApp — a three-way split on the head's `Γ` classification
  -- (`casesOns` first, because `getCasesInfo?` is consulted before `getCtorArity?`):
  -- the ι path goes to motive 15, the constructor path to motive 13, and the plain
  -- path to motive 4 for the head + motive 7 for the spine.
  · intro vC vAA vCtE vCsE ih4 ih7 ih13 ih15
    refine ⟨?_, ?apx⟩
    case apx =>
      rw [Erasure.visitConstApp_eq_mutual]
      exact (Erasure.fix_step_le Erasure.visitExpr.mutual._proof_1
        (Erasure.mutual_le_of
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl ih4.2 Erasure.approx_rfl
          Erasure.approx_rfl ih7.2 Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl ih13.2 Erasure.approx_rfl ih15.2
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl)).2.2.2.2.2.2.2.2.2.2.2.1
    replace ih4 := ih4.1
    replace ih7 := ih7.1
    replace ih13 := ih13.1
    replace ih15 := ih15.1
    intro e s ctx cctx ref w t s' w' hrun Γ hΓ Δ hinv hsupp hex cn us hfn
    replace H := H.of_coh hΓ
    replace HD := HD.of_coh hΓ
    replace C := C.of_coh hΓ
    simp only [] at hrun
    rw [expr_withApp_eq] at hrun
    rw [hfn] at hrun
    simp only [] at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨o, s₁, w₁, hcs, hk⟩ := hrun
    rw [run_liftCoreM_ok] at hcs
    obtain ⟨hcs, rfl⟩ := hcs
    obtain ⟨hle₁, hnone₁⟩ := H.cases_run cn cctx ref w o w₁ hcs
    cases hcasesons : Γ.casesOns cn with
    | some p =>
      -- CASES path: `getCasesInfo?` is positive and agrees with `Γ`; `visitCasesEta`
      -- handles the spine.
      obtain ⟨iid, np⟩ := p
      obtain ⟨dp, nfs, hdp, hnfs, hnat, hint, hlesat, hfacts⟩ :=
        casesApp_spine_facts hsupp hex hfn hcasesons
      obtain ⟨hle₁', ci, rfl, hagree⟩ :=
        C.cases_run_pos cn iid np dp nfs cctx ref w o w₁ hcasesons hdp hnfs hcs
      simp only [] at hk
      obtain ⟨erap, hs', hle₂⟩ := ih15 _ _ _ _ _ _ _ _ _ _ hk Γ hΓ Δ cn us iid np dp nfs
        (hinv.mono hle₁) hfn hcasesons hdp hnfs hagree hnat hint hlesat hfacts
      exact ⟨erap, hs', NameGenerator.LE.trans hle₁ hle₂⟩
    | none =>
    cases hctors : Γ.ctors cn with
    | some p =>
      -- CTOR path: `getCtorArity?` is positive; `visitCtorEta` handles the spine.
      obtain ⟨iid, cidx⟩ := p
      obtain ⟨ar, har, hle, hcas, hz, hs, hargfacts⟩ :=
        ctorApp_spine_facts hsupp hex hfn hctors hcasesons
      have ho : o = none := hnone₁ hcas
      subst ho
      simp only [] at hk
      rw [run_bind_ok] at hk
      obtain ⟨o₂, s₂, w₂, hca, hk⟩ := hk
      rw [run_liftCoreM_ok] at hca
      obtain ⟨hca, rfl⟩ := hca
      obtain ⟨hle₂, hsome⟩ := HD.ctor_run cn cctx ref w₁ o₂ w₂ hca
      have ho₂ : o₂ = some ar := hsome iid cidx ar hctors har
      subst ho₂
      simp only [] at hk
      obtain ⟨erap, hs', hle₃⟩ := ih13 _ _ _ _ _ _ _ _ _ _ _ hk Γ hΓ Δ us iid cidx
        (hinv.mono (NameGenerator.LE.trans hle₁ hle₂)) hfn hctors har hle hz hs hargfacts
      exact ⟨erap, hs', NameGenerator.LE.trans hle₁ (NameGenerator.LE.trans hle₂ hle₃)⟩
    | none =>
      -- PLAIN path: a plain constant head; `getCtorArity?` fails, `visitConst` fires.
      have hnc : ∀ cn' us', e.getAppFn = .const cn' us' → Γ.ctors cn' = none := by
        intro cn' us' h; rw [hfn] at h; injection h with h1 _; subst h1; exact hctors
      have hncs : ∀ cn' us', e.getAppFn = .const cn' us' → Γ.casesOns cn' = none := by
        intro cn' us' h; rw [hfn] at h; injection h with h1 _; subst h1; exact hcasesons
      obtain ⟨⟨hheadsupp, _⟩, hargfacts⟩ := spine_arg_facts hnc hncs hsupp hex
      have hheadsupp' : Supported known Γ (Expr.const cn us) := by rw [← hfn]; exact hheadsupp
      rcases hheadsupp'.const_inv' with ⟨hkn, hctor, hcases⟩ | ⟨_, _, _, hc', _⟩
      · have ho : o = none := hnone₁ hcases
        subst ho
        simp only [] at hk
        rw [run_bind_ok] at hk
        obtain ⟨o₂, s₂, w₂, hca, hk⟩ := hk
        rw [run_liftCoreM_ok] at hca
        obtain ⟨hca, rfl⟩ := hca
        obtain ⟨hle₂, hnone₂⟩ := H.ctor_run cn cctx ref w₁ o₂ w₂ hca
        have ho₂ : o₂ = none := hnone₂ hctor
        subst ho₂
        simp only [] at hk
        rw [run_bind_ok] at hk
        obtain ⟨tc, s₃, w₃, hvc, hk⟩ := hk
        obtain ⟨erc, hs₃, hle₃⟩ := ih4 _ _ _ _ _ _ _ _ _ hvc Γ hΓ Δ
          (hinv.mono (NameGenerator.LE.trans hle₁ hle₂)) cn us rfl hkn hctor hcases
        have erfn : Erases env Us Γ Δ e.getAppFn tc := by rw [hfn]; exact erc
        obtain ⟨erapp, hs', hle₄⟩ := ih7 _ _ _ _ _ _ _ _ _ _ hk Γ hΓ Δ e.getAppFn
          ((hinv.mono_state hs₃.rc).mono
            (NameGenerator.LE.trans hle₁ (NameGenerator.LE.trans hle₂ hle₃)))
          erfn hargfacts
        rw [getAppArgs_spine'] at erapp
        exact ⟨erapp, hs₃.trans hs',
          NameGenerator.LE.trans hle₁ (NameGenerator.LE.trans hle₂
            (NameGenerator.LE.trans hle₃ hle₄))⟩
      · rw [hctors] at hc'; exact absurd hc' (by simp)
  -- Step 13: visitCtorEta — `inferType` (state-preserving, monotone), then the
  -- `withApp`-decomposed spine goes to `visitCtorEtaGo`.
  · intro vCtorEtaGo ih14
    refine ⟨?_, ?apx⟩
    case apx =>
      rw [Erasure.visitCtorEta_eq_mutual]
      exact (Erasure.fix_step_le Erasure.visitExpr.mutual._proof_1
        (Erasure.mutual_le_of
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl ih14.2 Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl)).2.2.2.2.2.2.2.2.2.2.2.2.1
    replace ih14 := ih14.1
    intro cn ar e s ctx cctx ref w t s' w' hrun Γ hΓ Δ us iid cidx hinv hfn hct har hle
      hzero hsucc hargfacts
    replace HD := HD.of_coh hΓ
    simp only [] at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨type, s₁, w₁, hinfer, hk⟩ := hrun
    have hs₁ : s₁ = s := run_liftMetaM_state _ _ _ _ _ hinfer
    have hlem := HD.infer_run e s ctx cctx ref w type s₁ w₁ hinfer
    subst hs₁
    rw [expr_withApp_eq] at hk
    obtain ⟨erap, hs', hle₂⟩ := ih14 _ _ _ _ _ _ _ _ _ _ _ _ _ hk Γ hΓ Δ us iid cidx
      (hinv.mono hlem) hct har hle hzero hsucc hargfacts
    have hspine : e.getAppArgs.foldl Expr.app (.const cn us) = e := by
      rw [← hfn]; exact getAppArgs_spine' e
    rw [hspine] at erap
    exact ⟨erap, hs', NameGenerator.LE.trans hlem hle₂⟩
  -- Step 14: visitCtorEtaGo — saturated (`ar ≤ args.size`), so it goes straight
  -- to `visitConstructor` (motive 3); the η-expansion branch is dead.
  · intro vConstructor vCtorEtaGo ih3 _ih14
    refine ⟨?_, ?apx⟩
    case apx =>
      rw [Erasure.visitCtorEtaGo_eq_mutual]
      exact (Erasure.fix_step_le Erasure.visitExpr.mutual._proof_1
        (Erasure.mutual_le_of
          Erasure.approx_rfl Erasure.approx_rfl ih3.2 Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl _ih14.2
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl)).2.2.2.2.2.2.2.2.2.2.2.2.2.1
    replace ih3 := ih3.1
    intro cn ar ty fe args s ctx cctx ref w t s' w' hrun Γ hΓ Δ us iid cidx hinv hct har hle
      hzero hsucc hargfacts
    simp only [] at hrun
    rw [if_pos hle] at hrun
    exact ih3 _ _ _ _ _ _ _ _ _ _ hrun Γ hΓ Δ us iid cidx hinv hct (.inr ⟨hzero, hsucc⟩) hargfacts
  -- Step 15: visitCasesEta — `inferType` (state-preserving, monotone; the type is
  -- discarded on the saturated path), then the `withApp`-decomposed spine goes to
  -- `visitCasesEtaGo`. Mirrors step 13.
  · intro vCasesEtaGo ih16
    refine ⟨?_, ?apx⟩
    case apx =>
      rw [Erasure.visitCasesEta_eq_mutual]
      exact (Erasure.fix_step_le Erasure.visitExpr.mutual._proof_1
        (Erasure.mutual_le_of
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl ih16.2 Erasure.approx_rfl
          Erasure.approx_rfl)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    replace ih16 := ih16.1
    intro ci e s ctx cctx ref w t s' w' hrun Γ hΓ Δ con us iid np dp nfs hinv hfn hcs hdp hnfs
      hagree hnat hint hle hfacts
    replace HD := HD.of_coh hΓ
    simp only [] at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨type, s₁, w₁, hinfer, hk⟩ := hrun
    have hs₁ : s₁ = s := run_liftMetaM_state _ _ _ _ _ hinfer
    have hlem := HD.infer_run e s ctx cctx ref w type s₁ w₁ hinfer
    subst hs₁
    rw [expr_withApp_eq] at hk
    obtain ⟨erap, hs', hle₂⟩ := ih16 _ _ _ _ _ _ _ _ _ _ _ _ hk Γ hΓ Δ con us iid np dp nfs
      (hinv.mono hlem) hcs hdp hnfs hagree hnat hint hle hfacts
    have hspine : e.getAppArgs.foldl Expr.app (.const con us) = e := by
      rw [← hfn]; exact getAppArgs_spine' e
    rw [hspine] at erap
    exact ⟨erap, hs', NameGenerator.LE.trans hlem hle₂⟩
  -- Step 16: visitCasesEtaGo — saturated (`ci.arity ≤ args.size`, by
  -- `CasesInfoAgrees.arity`), so it goes straight to `visitCases` (motive 17); the
  -- η-expansion branch is dead. Mirrors step 14.
  · intro vCasesEtaGo vCases _ih16 ih17
    refine ⟨?_, ?apx⟩
    case apx =>
      rw [Erasure.visitCasesEtaGo_eq_mutual]
      exact (Erasure.fix_step_le Erasure.visitExpr.mutual._proof_1
        (Erasure.mutual_le_of
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl _ih16.2 ih17.2
          Erasure.approx_rfl)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    replace ih17 := ih17.1
    intro ci ty fe args s ctx cctx ref w t s' w' hrun Γ hΓ Δ con us iid np dp nfs hinv hcs hdp
      hnfs hagree hnat hint hle hfacts
    simp only [] at hrun
    rw [if_pos (show ci.arity ≤ args.size by rw [hagree.arity]; exact hle)] at hrun
    exact ih17 _ _ _ _ _ _ _ _ _ _ hrun Γ hΓ Δ con us iid np dp nfs hinv hcs hdp hnfs
      hagree hnat hint hle hfacts
  -- Step 17: visitCases — the workhorse.
  · intro vE vAlt ih1 ih18
    refine ⟨?_, ?apx⟩
    case apx =>
      rw [Erasure.visitCases_eq_mutual]
      exact (Erasure.fix_step_le Erasure.visitExpr.mutual._proof_1
        (Erasure.mutual_le_of
          ih1.2 Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl ih18.2)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    replace ih1 := ih1.1
    replace ih18 := ih18.1
    intro ci args s ctx cctx ref w t s' w' hrun Γ hΓ Δ con us iid np dp nfs hinv hcs hdp hnfs
      hagree hnat hint hle hfacts
    replace C := C.of_coh hΓ
    obtain ⟨hfd, hfm, hfx⟩ := hfacts
    have hdplt : dp < args.size := by omega
    simp only [] at hrun
    -- (1) the discriminant
    rw [show args[ci.discrPos]! = args[dp]'hdplt from by
      rw [hagree.discrPos]; exact getElem!_pos args dp hdplt] at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨discr_nt, s₁, w₁, hdisc, hrun⟩ := hrun
    obtain ⟨hsd, hexd⟩ := hfd hdplt
    obtain ⟨erd, hrc₁, hle₁⟩ := ih1 _ _ _ _ _ _ _ _ _ hdisc Γ hΓ Δ hinv hsd hexd
    -- (2) `read`
    rw [run_bind_ok] at hrun
    obtain ⟨ctx', s₂, w₂, hrd, hrun⟩ := hrun
    rw [run_read] at hrd
    cases hrd
    -- (3) the machine-`Nat`/`Int` arms are dead (pure name side conditions)
    rw [run_bind_ok] at hrun
    obtain ⟨ret, s₃, w₃, hmatch, htail⟩ := hrun
    rw [hagree.declName] at hmatch
    rw [visitCases_match_default _ _ hnat hint] at hmatch
    -- (4) `getConstInfo con.getPrefix` → the inductive
    rw [run_bind_ok] at hmatch
    obtain ⟨cinfo, s₄, w₄, hgci, hmatch⟩ := hmatch
    obtain ⟨hle₄, indVal, rfl, hnp, hname⟩ :=
      C.casesind_run con iid np _ ctx cctx ref w₁ cinfo s₄ w₄ hcs hgci
    have hs₄ := run_getConstInfo_state _ _ _ _ _ hgci
    subst hs₄
    simp only [] at hmatch
    -- (5) `register_inductive` → `Γ`'s `InductiveId` and the (trivial) argmasks
    rw [run_bind_ok] at hmatch
    obtain ⟨rr, s₅, w₅, hreg, hmatch⟩ := hmatch
    obtain ⟨hle₅, hindid, hmlen, hmask⟩ :=
      C.casesreg_run indVal con iid np nfs _ ctx cctx ref w₄ rr s₅ w₅ hcs hnfs hname hreg
    -- the second registration site: `casesreg_run` no longer claims `s = s₁` (it was
    -- false); the proved state effect is `run_register_inductive_runConcl`.
    have hrc₅ : RunConclδ env Us Γ₀ Esrc _ _ :=
      RunConclδ.of_runConcl_gdecls (run_register_inductive_runConcl hreg)
        (run_register_inductive_gdeclsConst hreg)
    obtain ⟨indid, argmasks⟩ := rr
    simp only [] at hindid hmlen hmask
    subst hindid
    -- (6) the three-way parallel alternatives loop
    rw [run_bind_ok] at hmatch
    obtain ⟨accfin, s₆, w₆, hloop, hpure⟩ := hmatch
    rw [run_pure] at hpure
    cases hpure
    simp only [] at hloop
    have hRA : ci.altsRange.toArray = (Std.Rco.mk (dp + 1) (dp + 1 + nfs.length)).toArray := by
      rw [hagree.range, hagree.arity]
    rw [hRA] at hloop
    have hRsize : (Std.Rco.mk (dp + 1) (dp + 1 + nfs.length)).toArray.size = nfs.length := by
      rw [rco_toArray_size]; omega
    have hRlistlen :
        (Std.Rco.mk (dp + 1) (dp + 1 + nfs.length)).toArray.toList.length = nfs.length := by
      rw [Array.length_toList]; exact hRsize
    have hnalts : ci.altNumParams.size = nfs.length := hagree.numAlts
    have hle₆ : gw w ≤ gw w₅ :=
      NameGenerator.LE.trans hle₁ (NameGenerator.LE.trans hle₄ hle₅)
    have hloopP := run_array_forIn_ok' ctx cctx ref
      (P := fun pre acc s₇ w₇ =>
        RunConclδ env Us Γ₀ Esrc s₅ s₇ ∧ gw w ≤ gw w₇ ∧ acc.1.size = pre.length ∧
        acc.2.1.array = ci.altNumParams ∧ acc.2.1.start = pre.length ∧
        acc.2.1.stop = ci.altNumParams.size ∧ acc.2.2 = argmasks.drop pre.length ∧
        ∀ j (hj : j < acc.1.size),
          (acc.1[j]'hj).1.length = nfs[j]! ∧
          Erases env Us Γ Δ (args[dp + 1 + j]!)
            (mkLambdas (acc.1[j]'hj).1 (acc.1[j]'hj).2))
      ⟨RunConclδ.rfl' _, hle₆, rfl, toStream_array_array _, toStream_array_start _,
        toStream_array_stop _, by simp only [List.length_nil, List.drop_zero]; rfl,
        fun j hj => absurd hj (by simp)⟩
      -- the `yield` step: one alternative erased and pushed
      (fun pre x post acc s₇ w₇ bacc s₈ w₈ hL hP hbody => by
        obtain ⟨alts, sAlt, sMask⟩ := acc
        obtain ⟨hrcP, hlew, hsz, harr, hst, hsp, hsm, hpj⟩ := hP
        simp only [] at hsz harr hst hsp hsm hpj hbody
        have hLlen : pre.length < nfs.length := by
          have h0 : (pre ++ x :: post).length = nfs.length := by rw [← hL]; exact hRlistlen
          simp only [List.length_append, List.length_cons] at h0; omega
        have hx : x = dp + 1 + pre.length := by
          have h1 : (Std.Rco.mk (dp + 1) (dp + 1 + nfs.length)).toArray.toList[pre.length]?
              = some x := by rw [hL]; simp
          have h2 : (Std.Rco.mk (dp + 1) (dp + 1 + nfs.length)).toArray.toList[pre.length]?
              = some (dp + 1 + pre.length) := by
            rw [List.getElem?_eq_getElem (by rw [hRlistlen]; exact hLlen),
              Array.getElem_toList, rco_toArray_getElem]
          rw [h1] at h2; exact Option.some.inj h2
        subst hx
        have hxlt : dp + 1 + pre.length < args.size := by omega
        cases sMask with
        | nil =>
          exact absurd (List.drop_eq_nil_iff.mp hsm.symm) (by omega)
        | cons y rest =>
          rw [show Std.Stream.next? (y :: rest) = some (y, rest) from rfl] at hbody
          simp only [] at hbody
          have hstlt : sAlt.start < sAlt.stop := by rw [hst, hsp, hnalts]; exact hLlen
          cases hna : Std.Stream.next? sAlt with
          | none => exact absurd hna (subarray_next?_ne_none sAlt hstlt)
          | some p =>
            obtain ⟨altInfo, sAlt'⟩ := p
            rw [hna] at hbody
            simp only [] at hbody
            obtain ⟨hlt, hv, harr', hst', hsp'⟩ := subarray_next?_facts sAlt altInfo sAlt' hna
            -- the alternative descriptor: a `.ctor` alternative with zero retained fields
            have hna2 : pre.length < ci.altNumParams.size := by rw [hnalts]; exact hLlen
            have hai : sAlt.array[sAlt.start]'(Nat.lt_of_lt_of_le hlt sAlt.stop_le_array_size)
                = ci.altNumParams[pre.length]'hna2 := by
              have h? : sAlt.array[sAlt.start]? = ci.altNumParams[pre.length]? := by rw [harr, hst]
              rw [Array.getElem?_eq_getElem
                    (Nat.lt_of_lt_of_le hlt sAlt.stop_le_array_size),
                Array.getElem?_eq_getElem hna2] at h?
              exact Option.some.inj h?
            obtain ⟨cnm, hcnm⟩ := hagree.alts pre.length hLlen
            rw [getElem!_pos ci.altNumParams pre.length hna2] at hcnm
            have haltInfo : altInfo = .ctor cnm (nfs[pre.length]'hLlen) := by
              rw [hv, hai, hcnm]
            subst haltInfo
            simp only [] at hbody
            -- the argmask: `register_inductive` produced a trivial one
            have hml : pre.length < argmasks.length := by rw [hmlen]; exact hLlen
            rw [List.drop_eq_getElem_cons hml] at hsm
            injection hsm with hy hrest
            have hmy : y = Array.replicate (nfs[pre.length]'hLlen)
                (ConstructorArgRelevance.keep) := by
              rw [hy, ← getElem!_pos argmasks pre.length hml, hmask pre.length hLlen]
            -- the minor itself
            rw [getElem!_pos args (dp + 1 + pre.length) hxlt] at hbody
            rw [run_bind_ok] at hbody
            obtain ⟨alt, s₉, w₉, halt, hp2⟩ := hbody
            obtain ⟨hlamj, hsuppj, hexj⟩ := hfm pre.length hLlen hxlt
            obtain ⟨hlen0, eralt, hrc₉, hle₉⟩ :=
              ih18 (nfs[pre.length]'hLlen) y _ _ ctx cctx ref w₇ alt s₉ w₉ halt Γ hΓ Δ
                ((hinv.mono_state (hrc₁.trans (hrc₅.trans hrcP)).rc).mono hlew)
                hmy hlamj hsuppj hexj
            rw [run_pure] at hp2
            cases hp2
            refine ⟨hrcP.trans hrc₉, NameGenerator.LE.trans hlew hle₉, by simp [hsz],
              by rw [harr', harr],
              by rw [hst', hst]; simp, by rw [hsp', hsp], by rw [hrest]; simp, fun j hj => ?_⟩
            have hj' : j < alts.size + 1 := by simpa using hj
            rcases Nat.lt_or_ge j alts.size with hj2 | hj2
            · rw [Array.getElem_push_lt hj2]
              exact hpj j hj2
            · have hjeq : j = alts.size := by omega
              subst hjeq
              rw [Array.getElem_push_eq]
              refine ⟨?_, ?_⟩
              · rw [hsz, getElem!_pos nfs pre.length hLlen]; exact hlen0
              · rw [hsz, getElem!_pos args (dp + 1 + pre.length) hxlt]
                exact eralt)
      -- the `done` step: both `Std.Stream` early exits are refuted by the invariant
      (fun pre x post acc s₇ w₇ bacc s₈ w₈ hL hP hbody => by
        obtain ⟨alts, sAlt, sMask⟩ := acc
        obtain ⟨-, hlew, hsz, harr, hst, hsp, hsm, hpj⟩ := hP
        simp only [] at hsz harr hst hsp hsm hpj hbody
        have hLlen : pre.length < nfs.length := by
          have h0 : (pre ++ x :: post).length = nfs.length := by rw [← hL]; exact hRlistlen
          simp only [List.length_append, List.length_cons] at h0; omega
        cases sMask with
        | nil =>
          exact absurd (List.drop_eq_nil_iff.mp hsm.symm) (by omega)
        | cons y rest =>
          rw [show Std.Stream.next? (y :: rest) = some (y, rest) from rfl] at hbody
          simp only [] at hbody
          have hstlt : sAlt.start < sAlt.stop := by rw [hst, hsp, hnalts]; exact hLlen
          cases hna : Std.Stream.next? sAlt with
          | none => exact absurd hna (subarray_next?_ne_none sAlt hstlt)
          | some p =>
            obtain ⟨altInfo, sAlt'⟩ := p
            rw [hna] at hbody
            simp only [] at hbody
            rw [run_bind_ok] at hbody
            obtain ⟨alt, s₉, w₉, halt, hp2⟩ := hbody
            rw [run_pure] at hp2
            exact nomatch hp2)
      hloop
    obtain ⟨hrcfin, hle₇, hszfin, -, -, -, -, hpjfin⟩ := hloopP
    -- (7) assemble `Erases.cases` over the `pre ++ discr :: minors` prefix
    have hargsl : args.toList.length = args.size := Array.length_toList
    have hsize : accfin.1.size = nfs.length := by rw [hszfin, hRlistlen]
    have hAlen : (args.toList.take dp).length = dp := by
      rw [List.length_take, hargsl]; omega
    have hMlen : ((args.toList.drop (dp + 1)).take nfs.length).length = nfs.length := by
      rw [List.length_take, List.length_drop, hargsl]; omega
    have haltsl : accfin.1.toList.length = nfs.length := by rw [Array.length_toList, hsize]
    have hd : Erases env Us Γ Δ (args.toList[dp]'(by rw [hargsl]; exact hdplt)) discr_nt := by
      simpa using erd
    have ercases : Erases env Us Γ Δ
        (((args.toList[dp]'(by rw [hargsl]; exact hdplt)) ::
            ((args.toList.drop (dp + 1)).take nfs.length)).foldl Expr.app
          ((args.toList.take dp).foldl Expr.app (.const con us)))
        (.case (indid, np) discr_nt accfin.1.toList) := by
      refine Erases.cases con us indid np (args.toList.take dp) (nfs := nfs) hcs
        (by rw [hAlen]; exact hdp) hnfs hd (by rw [hMlen, haltsl]) (by rw [haltsl])
        (fun j hj => ?_) (fun j hj => ?_)
      · have hj' : j < nfs.length := by rw [haltsl] at hj; exact hj
        rw [Array.getElem_toList]
        have := (hpjfin j (by rw [hsize]; exact hj')).1
        rwa [getElem!_pos nfs j hj'] at this
      · have hj' : j < nfs.length := by rw [hMlen] at hj; exact hj
        have hxlt : dp + 1 + j < args.size := by omega
        have hmg : ((args.toList.drop (dp + 1)).take nfs.length)[j]'hj
            = args[dp + 1 + j]'hxlt := by
          rw [List.getElem_take, List.getElem_drop, Array.getElem_toList]
        rw [hmg, Array.getElem_toList]
        have := (hpjfin j (by rw [hsize]; exact hj')).2
        rwa [getElem!_pos args (dp + 1 + j) hxlt] at this
    rw [← List.foldl_append] at ercases
    -- (8) the over-application tail: fold `Erases.app` over the remaining arguments
    rw [run_bind_ok] at htail
    obtain ⟨tfin, s₉, w₉, hloop2, hpure2⟩ := htail
    rw [run_pure] at hpure2
    cases hpure2
    simp only [hagree.arity, hnp] at hloop2
    have htailP := run_array_forIn_ok' ctx cctx ref
      (P := fun pre acc s₁₀ w₁₀ => RunConclδ env Us Γ₀ Esrc s₃ s₁₀ ∧ gw w ≤ gw w₁₀ ∧
        Erases env Us Γ Δ
          (pre.foldl Expr.app
            ((args.toList.take dp ++ (args.toList[dp]'(by rw [hargsl]; exact hdplt)) ::
              ((args.toList.drop (dp + 1)).take nfs.length)).foldl Expr.app (.const con us)))
          acc)
      ⟨RunConclδ.rfl' _, hle₇, ercases⟩
      (fun pre x post acc s₁₀ w₁₀ b s₁₁ w₁₁ hL hP hbody => by
        obtain ⟨hrcT, hlew, herp⟩ := hP
        rw [slice_toArray_toList_drop] at hL
        have hXlen : (args.toList.drop (dp + 1 + nfs.length)).length
            = args.size - (dp + 1 + nfs.length) := by rw [List.length_drop, hargsl]
        have hplt : pre.length < args.size - (dp + 1 + nfs.length) := by
          have h0 : (pre ++ x :: post).length = args.size - (dp + 1 + nfs.length) := by
            rw [← hL]; exact hXlen
          simp only [List.length_append, List.length_cons] at h0; omega
        have hilt : dp + 1 + nfs.length + pre.length < args.size := by omega
        have hx : x = args[dp + 1 + nfs.length + pre.length]'hilt := by
          have h1 : (args.toList.drop (dp + 1 + nfs.length))[pre.length]? = some x := by
            rw [hL]; simp
          have h2 : (args.toList.drop (dp + 1 + nfs.length))[pre.length]?
              = some (args[dp + 1 + nfs.length + pre.length]'hilt) := by
            rw [List.getElem?_eq_getElem (by rw [hXlen]; exact hplt), List.getElem_drop,
              Array.getElem_toList]
          rw [h1] at h2; exact Option.some.inj h2
        subst hx
        obtain ⟨hsx, hex⟩ := hfx _ hilt (by omega)
        rw [run_bind_ok] at hbody
        obtain ⟨tx, s₁₂, w₁₂, hvx, hp3⟩ := hbody
        obtain ⟨erx, hrcX, hle₁₂⟩ := ih1 _ _ _ _ _ _ _ _ _ hvx Γ hΓ Δ
          ((hinv.mono_state (hrc₁.trans (hrc₅.trans (hrcfin.trans hrcT))).rc).mono hlew) hsx hex
        rw [run_pure] at hp3
        cases hp3
        refine ⟨hrcT.trans hrcX, NameGenerator.LE.trans hlew hle₁₂, ?_⟩
        rw [List.foldl_append]
        exact .app herp erx)
      (fun pre x post acc s₁₀ w₁₀ b s₁₁ w₁₁ hL hP hbody => by
        rw [run_bind_ok] at hbody
        obtain ⟨tx, s₁₂, w₁₂, hvx, hp3⟩ := hbody
        rw [run_pure] at hp3
        exact nomatch hp3)
      hloop2
    obtain ⟨hrcT, hle₈, ert⟩ := htailP
    refine ⟨?_, hrc₁.trans (hrc₅.trans (hrcfin.trans hrcT)), hle₈⟩
    rw [slice_toArray_toList_drop] at ert
    rw [← Array.foldl_toList]
    have hsp2 := list_split_cases args.toList dp nfs.length (by rw [hargsl]; exact hle)
    have hfin : (args.toList.drop (dp + 1 + nfs.length)).foldl Expr.app
          ((args.toList.take dp ++ (args.toList[dp]'(by rw [hargsl]; exact hdplt)) ::
            ((args.toList.drop (dp + 1)).take nfs.length)).foldl Expr.app (.const con us))
        = args.toList.foldl Expr.app (.const con us) := by
      rw [← List.foldl_append, ← hsp2]
    rw [← hfin]
    exact ert
  -- Step 18: visitAlt — with flat (zero-field) alternatives `lambdaOrIntroToArity`
  -- opens no binder: the continuation runs on `e` itself with an empty fvar list,
  -- `filter` is the identity on `#[]` (for *any* argmask), and `mkAlt [] t = ([], t)`,
  -- so the alternative's telescope degenerates and `mkLambdas [] t = t`.
  · intro vE ih1
    refine ⟨?_, ?apx⟩
    case apx =>
      rw [Erasure.visitAlt_eq_mutual]
      exact (Erasure.fix_step_le Erasure.visitExpr.mutual._proof_1
        (Erasure.mutual_le_of
          ih1.2 Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl Erasure.approx_rfl
          Erasure.approx_rfl)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    replace ih1 := ih1.1
    intro nf mask e s ctx cctx ref w r s' w' hrun Γ hΓ Δ hinv hmask hlam hsupp hex
    replace H := H.of_coh hΓ
    replace C := C.of_coh hΓ
    simp only [] at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨ty, s₁, w₁, hinfer, hk⟩ := hrun
    have hs₁ : s₁ = s := run_liftMetaM_state _ _ _ _ _ hinfer
    subst hs₁
    obtain ⟨hlem, hfml⟩ := C.infer_lam_run e _ ctx cctx ref w ty _ w₁ hinfer
    obtain ⟨ys, efin, Δ', ctx', w₂, hlen, hle₂, hinv', hsupp', hex', _hext, hK, hclose⟩ :=
      bridge_alt_telescope H henv cctx ref nf e ty Δ _ _ ctx w₁ r s' w' hk
        (hinv.mono hlem) hlam hsupp hex hfml
    rw [hmask, filter_replicate_keep nf ys.toArray (by simp [hlen]),
      List.toList_toArray] at hK
    rw [run_bind_ok] at hK
    obtain ⟨tb, s₂, w₃, hvb, hm⟩ := hK
    obtain ⟨erb, hs₂, hle₃⟩ := ih1 _ _ _ _ _ _ _ _ _ hvb Γ hΓ Δ' hinv' hsupp' hex'
    rw [run_mkAlt] at hm
    cases hm
    exact ⟨by simp [hlen], hclose tb erb, hs₂,
      NameGenerator.LE.trans hlem (NameGenerator.LE.trans hle₂ hle₃)⟩

/-! ## The exported theorem -/

/-- **The bridge theorem**: on the supported fragment, under the trust bundles
`BridgeHyps`/`DataBridgeHyps`/`CasesBridgeHyps`/`ProjBridgeHyps` and the invariant
`BridgeInv`,
a successful run of the shipping
erasure `Erasure.visitExpr` refines the typed erasure relation `Erases`;
moreover the `ErasureState` only *grows* (`Erasure.RunConcl`: the registries extend,
`gdecls` is only prepended to, and the constant registry stays canonical) and the ghost
name-generator measure advances monotonically.

The state conclusion widened from `s' = s` with cold-start slice S2: the warm shape was
an artefact of `DataBridgeHyps.reg_run`/`CasesBridgeHyps.casesreg_run` asserting that
`register_inductive` preserves the state, which is false about the real function
(`Erasure.run_register_inductive_cold_ok`). Those clauses are gone; this conclusion is
what the run actually does. -/
theorem visitExpr_refines_erases {env : VEnv} {Us : List Name}
    {known : Name → Prop} {Γ : ErasureCtx} {cfg₀ : ErasureConfig} {Esrc : SEnv}
    {gw : Void IO.RealWorld → NameGenerator}
    (H : BridgeHyps env Us Γ gw) (HD : DataBridgeHyps Γ gw) (C : CasesBridgeHyps Γ gw) (P : ProjBridgeHyps Γ gw)
    (Hδ : ∀ (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State),
      DeltaHyps env Us known Γ cfg₀ Esrc gw cctx ref)
    (Hβ : ∀ (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State),
      BlockHyps env Us known Γ cfg₀ Esrc cctx ref)
    (Hreg : RecBlockAgreement env Us known Γ cfg₀)
    (henv : env.Ordered) :
    ∀ e s ctx cctx ref w t s' w',
      Erasure.visitExpr e s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ, BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ →
        Supported known Γ e → (∃ ve, TrExprS env Us Δ e ve) →
        Erases env Us Γ Δ e t ∧ RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w' :=
  fun e s ctx cctx ref w t s' w' hrun Δ =>
    (visitExpr_refines_erases_core H HD C P Hδ Hβ Hreg henv).1.1
      e s ctx cctx ref w t s' w' hrun Γ (ErasureCtx.withFixvars_self Γ).symm Δ

/-- **The bridge, instantiated *inside* a mutual block** (slice δ-D8).

The theorem above binds `Γ` as a plain implicit and this file declares no `variable`, so
it is Γ-polymorphic **as a statement** and every application picks its own `Γ`. That is
what the recursive walk needs: `visitMutual` erases each sibling body under a reader
carrying the block's fixvar map, i.e. against `Γ.withFixvars fv`, not against the ambient
`Γ`. No motive changes; the whole question is which premises survive `Γ ↦ Γ.withFixvars fv`,
and the answer is *all but one*:

* `BridgeHyps`/`DataBridgeHyps`/`CasesBridgeHyps`/`ProjBridgeHyps` read only registration
  fields that `withFixvars` leaves alone — `withFixvars` above;
* `BridgeInv` is rebuilt by `BridgeInv.withFixvars`, whose two new obligations are the
  reader-vs-`fv` agreement the `withReader` establishes by construction and the block
  freshness `BridgeHyps.fresh_run` gives against `BridgeInv.reserved`;
* `Supported` transports and in fact *grows*: `Supported.const`'s `known n ∨ Γ.fixvars n ≠
  none` gains the whole block as its second disjunct, which is what makes a sibling
  reference derivable at `known = ⊥`;
* the `TrExprS` witness and `env.Ordered` never mentioned `Γ`;
* **`DeltaHyps` is the one break.** Its `nofixvars` field said `Γ.fixvars = ⊥`
  unconditionally, which is *false* at a block-local `Γ`. Slice δ-D8 conditions it on the
  fragment — the only thing its two consumption sites ever had in scope — after which the
  bundle is inhabitable at `Γ.withFixvars fv` with `known = ⊥`, which is what `Hδ'` here
  asks for.

The price is a scope restriction, and it is the `known = ⊥` in `Hδ'`/`hsupp`: a block body
may reference its own siblings (via `Γ.fixvars`), registered constructors and registered
`casesOn`s, but **not an external constant**.

**Two predictions in the paragraph above are now falsified** (slice Γ-W1), and are recorded
here rather than deleted because the correction is the interesting part. It used to read
"lifting it means giving `DeltaHyps` a second context parameter and quantifying `Γ` inside
motives 1/5/6, since a dependency reached from inside a block is genuinely erased at a
*third* `Γ` (`fixvars := none`)". Neither half survived contact:

* **no second parameter.** `DeltaHyps` is re-targeted to the ambient `Γ₀` and never mentions
  the motive-local `Γ`; the "third `Γ`" turns out to be `Γ₀` itself, because `nofixvars`
  pins `Γ₀.fixvars = ⊥` on the fragment and `Γ₀.withFixvars (fun _ => none)` *is* `Γ₀`;
* **not three motives but all seventeen with content.** The IH call graph is one strongly
  connected component (`1 → 11 → 12 → 4 → 5 → 6 → 1` closes it by itself), so a motive
  cannot quantify `Γ` unless every motive it dispatches to does. Only motive 10, whose
  conclusion was `True` and which nothing called, stayed fixed — and that exemption
  **expired at slice P8**, which gave motive 10 content in the shape recorded here (`Γ hΓ`
  immediately after the run hypothesis, `RunConclδ` re-indexed to `Γ₀`) and made step 1
  call it. All eighteen now carry `Γ`.

This theorem survives and keeps its callers, but it is now *subsumed*: the core proves the
block case directly, at the local `Γ` its motives carry. -/
theorem visitExpr_refines_erases_block {env : VEnv} {Us : List Name}
    {known : Name → Prop} {Γ : ErasureCtx} {cfg₀ : ErasureConfig} {Esrcb : SEnv}
    {gw : Void IO.RealWorld → NameGenerator}
    (H : BridgeHyps env Us Γ gw) (HD : DataBridgeHyps Γ gw) (C : CasesBridgeHyps Γ gw) (P : ProjBridgeHyps Γ gw)
    (Hδ' : ∀ (fv : Name → Option FVarId) (cc : Core.Context)
             (rf : ST.Ref IO.RealWorld Core.State),
      DeltaHyps env Us (fun _ => False) (Γ.withFixvars fv) cfg₀ Esrcb gw cc rf)
    (Hβ' : ∀ (fv : Name → Option FVarId) (cc : Core.Context)
             (rf : ST.Ref IO.RealWorld Core.State),
      BlockHyps env Us (fun _ => False) (Γ.withFixvars fv) cfg₀ Esrcb cc rf)
    (henv : env.Ordered)
    {fv : Name → Option FVarId} {fvmap : Std.HashMap Name FVarId}
    {ctx ctx' : ErasureContext} {gen : NameGenerator}
    {s s' : ErasureState} {Δ : VLCtx} {e : Expr} {t : LBTerm}
    {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld}
    (hinv : BridgeInv env Us known Γ cfg₀ gen ctx s Δ) (hgen : gen ≤ gw w)
    (hlctx : ctx'.lctx = ctx.lctx) (hlp : ctx'.lparams <+: Us)
    (hcfg : ctx'.config = ctx.config) (hfvm : ctx'.fixvars = some fvmap)
    (hagree : ∀ (nm : Name) (x : FVarId), fvmap[nm]? = some x ↔ fv nm = some x)
    (hfresh : ∀ (nm : Name) (x : FVarId), fv nm = some x →
      (gw w).Reserves x ∧ x ∉ Δ.fvars)
    (hsupp : Supported (fun _ => False) (Γ.withFixvars fv) e)
    (hex : ∃ ve, TrExprS env Us Δ e ve)
    (hrun : Erasure.visitExpr e s ctx' cctx ref w = .ok (t, s') w') :
    Erases env Us (Γ.withFixvars fv) Δ e t ∧ Erasure.RunConcl s s' ∧ gw w ≤ gw w' := by
  have hinv' : BridgeInv env Us (fun _ => False) (Γ.withFixvars fv) cfg₀ (gw w) ctx' s Δ :=
    (hinv.mono hgen).withFixvars hlctx hlp hcfg hfvm hagree hfresh
  have h := visitExpr_refines_erases (H.withFixvars fv) (HD.withFixvars fv)
    (C.withFixvars fv) (P.withFixvars fv) (Hδ' fv) (Hβ' fv) RecBlockAgreement.of_bot henv
    e s ctx' cctx ref w t s' w' hrun Δ hinv' hsupp hex
  exact ⟨h.1, h.2.1.rc, h.2.2⟩

/-! ## Non-vacuity guards

The `BridgeHyps`/`DataBridgeHyps`/`CasesBridgeHyps`/`ProjBridgeHyps` fields quantify
over opaque runtime primitives, so their global satisfiability is not in-logic decidable —
that is the documented trust boundary. Everything *else* is checked non-vacuous
here: `BridgeInv` is satisfiable, and the theorem's full non-run premise set is
jointly instantiable at a concrete context/term. (The ι fragment's own
non-vacuity lives at its definitions: `Supported.casesApp` in `Bridge.lean`,
`CasesInfoAgrees`/`ForallMatchesLam` in `CasesBridgeHyps.lean`.) -/

section NonVacuity

/-- (i) `BridgeInv` is satisfiable: the empty-context instance at `Δ = []`,
`known := fun _ => False`, `fixvars = none`. `hcfg` is the literal fragment's config pin
(L3), a side condition relating the *parameter* `Γ` to the run's config exactly the way
`hkn`/`hfv` relate it to the registry and the block; it is vacuous at the default
`Γ.natPeano = false`. -/
example (env : VEnv) (Us : List Name) (Γ : ErasureCtx) (gen : NameGenerator)
    (hkn : ∀ n : Name, Γ.constants n = toKername n) (hfv : Γ.fixvars = fun _ => none)
    (cfg : ErasureConfig) (hcfg : Γ.natPeano = true → cfg.nat = .peano) :
    BridgeInv env Us (fun _ => False) Γ cfg gen ⟨{}, none, Us, cfg⟩ {} [] where
  mlc := ⟨.nil, trivial, rfl, rfl⟩
  lparams := List.prefix_refl _
  cfg := rfl
  natcfg := hcfg
  kfresh := fun _ hfv => nomatch hfv
  fixvars := by intro nm x; rw [hfv]; simp
  fixfresh := by intro nm x hx; rw [hfv] at hx; simp at hx
  reserved := fun _ hfv => nomatch hfv
  knames := hkn
  consts := by intro n k hk; simp at hk

/-- (i') **The fixvar agreement is satisfiable at a genuinely *block-local*
configuration** (recursion wall, W3.1) — the guard that `BridgeInv.fixvars` is a real
agreement and not the old `ctx.fixvars = none` exclusion in disguise. The reader carries
the one-entry map `{f ↦ x}` that `visitMutual`'s `withReader` installs, `Γ` is
`ΓfixOpen x` (`Erases.lean`'s recursion fixture at its *open* stage), and `Δ = []` — the
context in which `visitMutual` starts each sibling body, where the freshness field
`fixfresh` is free. So `visitConst`'s fixvar branch is reachable under the invariant, and
motive 4's new branch is not vacuously discharged. -/
example (env : VEnv) (Us : List Name) (gen : NameGenerator) (x : FVarId)
    (hres : gen.Reserves x) (cfg : ErasureConfig) :
    BridgeInv env Us (fun _ => False) (ΓfixOpen x) cfg gen
      ⟨{}, some ((∅ : Std.HashMap Name FVarId).insert `f x), Us, cfg⟩ {} [] where
  mlc := ⟨.nil, trivial, rfl, rfl⟩
  lparams := List.prefix_refl _
  cfg := rfl
  natcfg := fun h => absurd h (by simp [ΓfixOpen])
  kfresh := fun _ hfv => nomatch hfv
  fixvars := by
    intro nm y
    show ((∅ : Std.HashMap Name FVarId).insert `f x)[nm]? = some y ↔ _
    rw [Std.HashMap.getElem?_insert]
    by_cases h : nm = `f
    · subst h; simp [ΓfixOpen]
    · simp [ΓfixOpen, h, Ne.symm h]
  fixfresh := by
    intro nm y hy
    have : y = x := by by_cases h : nm = `f <;> simp_all [ΓfixOpen]
    subst this; exact ⟨hres, fun hm => nomatch hm⟩
  reserved := fun _ hfv => nomatch hfv
  knames := fun _ => rfl
  consts := by intro n k hk; simp at hk

/-- (i'') **The block instantiation is jointly instantiable** (slice δ-D8) — the guard for
`visitExpr_refines_erases_block`, at the recursion fixture's two stages.

The ambient `Γ` is `ΓfixRec` (`Erases.lean`), which registers the one-def block for `f`
and leaves `fixvars` at its top-level `fun _ => none`; the block-local one is
`ΓfixRec.withFixvars {f ↦ x}`, which is `ΓfixOpen x` on the nose. The reader is the
one `visitMutual`'s `withReader` installs. Two things this checks that nothing else does:

* `Supported` really **grows** at the block-local `Γ`. The subject `.const f []` is
  supported at `known = ⊥` *only* through `Supported.const`'s second disjunct
  `Γ.fixvars n ≠ none` — at the ambient `ΓfixRec` the same term is not supported at all,
  which is what makes the block's `known = ⊥` bundle usable instead of vacuous;
* `DeltaHyps` at `ΓfixRec.withFixvars {f ↦ x}` is asked for, and it is inhabitable
  precisely because slice δ-D8 conditioned `nofixvars` — before that, this premise was
  false (`DeltaHyps.gNofixvars_blocklocal_refuted`).

Hypothetical: the run, the six bundle premises (four trust bundles plus the block-local
`Hδ'`/`Hβ'`), and the `TrExprS` witness (the fixture's `env`
is a parameter, so nothing here can declare `f`). -/
example (env : VEnv) (Us : List Name) (cfg : ErasureConfig)
    (gw : Void IO.RealWorld → NameGenerator) (w w' : Void IO.RealWorld)
    (x : FVarId) (hres : (gw w).Reserves x)
    (H : BridgeHyps env Us ΓfixRec gw) (HD : DataBridgeHyps ΓfixRec gw)
    (C : CasesBridgeHyps ΓfixRec gw) (P : ProjBridgeHyps ΓfixRec gw)
    (Hδ' : ∀ (fv : Name → Option FVarId) (cc : Core.Context)
             (rf : ST.Ref IO.RealWorld Core.State),
      DeltaHyps env Us (fun _ => False) (ΓfixRec.withFixvars fv) cfg (fun _ => none) gw cc rf)
    (Hβ' : ∀ (fv : Name → Option FVarId) (cc : Core.Context)
             (rf : ST.Ref IO.RealWorld Core.State),
      BlockHyps env Us (fun _ => False) (ΓfixRec.withFixvars fv) cfg (fun _ => none) cc rf)
    (henv : env.Ordered)
    (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)
    (ve : VExpr) (htr : TrExprS env Us [] (.const `f []) ve)
    (t : LBTerm) (s' : ErasureState)
    (hrun : Erasure.visitExpr (.const `f []) {}
      ⟨{}, some ((∅ : Std.HashMap Name FVarId).insert `f x), Us, cfg⟩ cctx ref w
      = .ok (t, s') w') :
    Erases env Us (ΓfixOpen x) [] (.const `f []) t ∧
      Erasure.RunConcl {} s' ∧ gw w ≤ gw w' :=
  visitExpr_refines_erases_block H HD C P Hδ' Hβ' henv
    (Γ := ΓfixRec) (fv := fun n => if n = `f then some x else none)
    (ctx := ⟨{}, none, Us, cfg⟩) (known := fun _ => False)
    (ctx' := ⟨{}, some ((∅ : Std.HashMap Name FVarId).insert `f x), Us, cfg⟩)
    (fvmap := (∅ : Std.HashMap Name FVarId).insert `f x)
    { mlc := ⟨.nil, trivial, rfl, rfl⟩
      lparams := List.prefix_refl _
      cfg := rfl
      natcfg := fun h => absurd h (by simp [ΓfixRec])
      kfresh := fun _ hfv => nomatch hfv
      fixvars := by intro nm y; simp [ΓfixRec]
      fixfresh := by intro nm y hy; simp [ΓfixRec] at hy
      reserved := fun _ hfv => nomatch hfv
      knames := fun _ => rfl
      consts := by intro n k hk; simp at hk }
    NameGenerator.LE.rfl rfl (List.prefix_refl _) rfl rfl
    (by
      intro nm y
      rw [Std.HashMap.getElem?_insert]
      by_cases h : nm = `f
      · subst h; simp
      · simp [h, Ne.symm h])
    (by
      intro nm y hy
      obtain rfl : y = x := by by_cases h : nm = `f <;> simp_all
      exact ⟨hres, fun hm => nomatch hm⟩)
    (.const `f [] (Or.inr (by simp)) rfl rfl)
    ⟨ve, htr⟩ hrun

/-- …and at the **ambient** `Γ` the same subject is *not* supported, which is what the
block instantiation buys. The fragment is `⊥` in both, so the only difference is the
fixvar map. -/
theorem supported_const_fixOpen_not_ambient :
    ¬ Supported (fun _ => False) ΓfixRec (.const `f []) := by
  intro h
  rcases h.const_inv' with ⟨hk, -, -⟩ | ⟨_, _, _, hc, _⟩
  · rcases hk with h' | h' <;> simp [ΓfixRec] at h'
  · simp [ΓfixRec] at hc

/-- (i''') **…and the same instantiation is *not* available inside the induction**
(slice δ-D8e) — the negative guard for `visitExpr_refines_erases_block`, and, when it was
written, the exact obstruction the cold-start `hnorec` premise was waiting on. Both ends of
that sentence have since been paid: step 6 walks the exit (Γ-W3.6b) and `hnorec` itself is
deleted (Γ-W4).

`visitExpr_refines_erases_block` reads the bridge theorem at a second `Γ`. That works
because the theorem binds `Γ` as a plain implicit, so it is Γ-polymorphic **as a
statement**. The motives of `visitExpr_refines_erases_core` are not: they fix one `Γ`, and
step 6's recursive exit erases each sibling body by calling the induction's *abstract*
fixpoint argument, about which only the motives may be assumed. So the erasure IH is
usable there only if its own premise, `BridgeInv env Us known Γ (gw w) ctx' s Δ`, holds at
the reader the exit installs.

It does not, and this is why: `BridgeInv.fixvars` is an **iff** between the reader's map
and `Γ.fixvars`, and `DeltaHyps.nofixvars` pins `Γ.fixvars = ⊥` for every fragment name —
which step 6 has in scope (`hkn : known n`). A reader whose map has any hit at all
therefore refutes the invariant outright. The block's map has exactly one hit per sibling,
by construction.

The consequence, stated plainly when this was written: removing `DeltaHyps.nonrecursive`
lets the run *reach* the recursive exit but does not let the bridge *walk* it. Walking it
needs the motives to quantify `Γ` (and the four trust bundles with it), which is a change
to all eighteen motives and every IH application site — not another premise.

**Status after slice Γ-W1.** The motives now do quantify `Γ`, and this theorem stays as the
record of *why*, plus the guard that the new `hΓ` binder is load-bearing: at `hΓ := rfl`,
i.e. at the motive-local `Γ` instantiated to the ambient `Γ₀` (where `nofixvars` applies),
the block reader is still refuted — which is exactly why the block instance must pass
`Γ₀.withFixvars fv` and not `Γ₀`. The prediction about the *bundles* did not hold: only `Γ`
moved, and the four bundles stayed outer (`BridgeHyps.of_coh` and friends re-derive them per
step, obligation-free).

**Status after slice Γ-W3.6b: the sentence above was right, and both halves were paid.**
`DeltaHyps.nonrecursive` is deleted and step 6 walks the exit. This theorem is unchanged
and still true — a reader carrying the block's map refutes the invariant *at the ambient*
`Γ₀` — and it is precisely why the walk rebuilds the per-sibling invariant at
`Γ₀.withFixvars fv` (`BridgeInv.withFixvars`) instead of trying to reuse the caller's. Read
today it is the statement of what the walk had to do, not of what it could not. -/
theorem bridgeInv_blockReader_refuted {env : VEnv} {Us : List Name} {known : Name → Prop}
    {Γ : ErasureCtx} {cfg₀ : ErasureConfig} {gen : NameGenerator}
    {ctx : ErasureContext} {s : ErasureState}
    {Δ : VLCtx} {fvmap : Std.HashMap Name FVarId} {nm : Name} {x : FVarId}
    (hnfv : Γ.fixvars = fun _ => none)
    (hfvm : ctx.fixvars = some fvmap) (hhit : fvmap[nm]? = some x) :
    ¬ BridgeInv env Us known Γ cfg₀ gen ctx s Δ := by
  intro h
  have hΓ := (h.fixvars nm x).mp (by rw [hfvm]; exact hhit)
  rw [hnfv] at hΓ
  simp at hΓ

/-- The instance: the reader `visitMutual`'s recursive exit installs for a one-name block
is `{ ctx with fixvars := some (HashMap.ofList (fixvarnames.zip ids)) }`, and at a single
sibling that map is `{n ↦ x}`. So the invariant is refuted at the very configuration the
recursive branch would have to run its IH in. -/
theorem bridgeInv_rec_exit_reader_refuted {env : VEnv} {Us : List Name} {known : Name → Prop}
    {Γ : ErasureCtx} {cfg₀ : ErasureConfig} {gen : NameGenerator}
    {ctx : ErasureContext} {s : ErasureState}
    {Δ : VLCtx} (n : Name) (x : FVarId) (hnfv : Γ.fixvars = fun _ => none) :
    ¬ BridgeInv env Us known Γ cfg₀ gen
        { ctx with fixvars := some (Std.HashMap.ofList ([n].zip [x])) } s Δ :=
  bridgeInv_blockReader_refuted (nm := n) (x := x) hnfv rfl (by simp)

/-- **(iv') The recursive exit's walk fires at the shipping eraser** (recursion wall,
slice Γ-W3), and this is the guard that says so: `rec_exit_refines_erases` is stated at an
abstract eraser and its motive-1 refinement hypothesis, and the induction's own conclusion
is exactly such a hypothesis. So the walk composes with `visitExpr_refines_erases_core`
into the three conjuncts `visitMutual`'s motive reports, with no premise left over except
the ones the file's other guards also leave hypothetical: the run and the trust bundles.

**And since Γ-W3.6b there is no separate `hreg` in the binder list.** The registration
agreement is `Hreg : RecBlockAgreement`, a premise of the core itself, and the walk's
`hreg` is *derived* from it here — `Hreg cctx ref hkn hnd hinv`, at exactly the fragment,
`Nodup` and invariant this guard already holds. That is the shape step 6 uses, so what
this guard now exhibits is the composition in the form the induction actually runs it.

Read together with the refutation beneath it, this is the exact statement of where the
recursion wall now stands: everything the composition needs is *derived* — the two loops,
the per-sibling invariant rebuild at the block-local context, the context strengthening,
the block's closedness, the δ record's extension step — and one registration agreement is
*assumed*, gated on the fragment and on `BridgeInv`.

Since Γ-W3.5 the walk also takes the eraser's **approximation** conjunct, and the induction
supplies it here as `.1.2` — trivially, at the fixpoint. Guard (iv'') below is the version
that is not trivial. -/
example {env : VEnv} {Us : List Name} {known : Name → Prop} {Γ₀ : ErasureCtx} {Esrc : SEnv}
    {cfg₀ : ErasureConfig} {gw : Void IO.RealWorld → NameGenerator}
    {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    (H : BridgeHyps env Us Γ₀ gw) (HD : DataBridgeHyps Γ₀ gw) (C : CasesBridgeHyps Γ₀ gw) (P : ProjBridgeHyps Γ₀ gw)
    (Hδ : ∀ (cc : Core.Context) (rf : ST.Ref IO.RealWorld Core.State),
      DeltaHyps env Us known Γ₀ cfg₀ Esrc gw cc rf)
    (Hβ : ∀ (cc : Core.Context) (rf : ST.Ref IO.RealWorld Core.State),
      BlockHyps env Us known Γ₀ cfg₀ Esrc cc rf)
    (Hreg : RecBlockAgreement env Us known Γ₀ cfg₀)
    (henv : env.Ordered)
    {names : List Name} {ctx : ErasureContext} {s₀ s₁ : ErasureState} {Δ : VLCtx}
    {w w₁ : Void IO.RealWorld} {u₀ : Unit} {n : Name}
    (hkn : ∀ m ∈ names, known (remove_unsafe_rec m))
    (hnd : (names.map remove_unsafe_rec).Nodup)
    (hnmem : n ∈ names.map remove_unsafe_rec)
    (hinv : BridgeInv env Us known Γ₀ cfg₀ (gw w) ctx s₀ Δ)
    (hrun : (do
        let ids ← names.mapM (fun _ => (mkFreshFVarId : EraseM FVarId))
        withReader
            (fun e => { e with
              fixvars := some (Std.HashMap.ofList ((names.map remove_unsafe_rec).zip ids)) }) (do
          let defs ← names.mapM (fun m => do
            let cim ← getConstInfo m
            let t ← withReader (fun e => { e with lparams := cim.levelParams })
              (do let pe ← prepare_erasure (cim.value! (allowOpaque := true)); Erasure.visitExpr pe)
            mkDef (remove_unsafe_rec m) (names.map remove_unsafe_rec) t)
          for p in (names.map remove_unsafe_rec).zipIdx do
            modify (fun st => { st with
                constants := st.constants.insert p.1 (toKername p.1),
                gdecls := (toKername p.1, .constantDecl ⟨some (.fix defs p.2)⟩) :: st.gdecls })
          pure ()) : EraseM Unit) s₀ ctx cctx ref w = .ok (u₀, s₁) w₁) :
    RunConclδ env Us Γ₀ Esrc s₀ s₁ ∧ gw w ≤ gw w₁ ∧ (s₁.constants.get? n).isSome :=
  rec_exit_refines_erases H (Hδ cctx ref) (Hβ cctx ref) henv
    (fun e s ctx' w' t s' w'' hr =>
      (visitExpr_refines_erases_core H HD C P Hδ Hβ Hreg henv).1.1
        e s ctx' cctx ref w' t s' w'' hr)
    (visitExpr_refines_erases_core (cfg₀ := cfg₀) H HD C P Hδ Hβ Hreg henv).1.2
    (ErasureCtx.withFixvars_self Γ₀).symm hkn hnd hnmem hinv
    (Hreg cctx ref hkn hnd hinv) hrun

/-- **(iv'') …and it fires at exactly the data a *step* holds** (recursion wall, slice
Γ-W3.5). Guard (iv') composes the walk with the induction's *conclusion*. Step 6 does not
have the conclusion; it has a motive, at the induction's abstract fixpoint argument. Since
Γ-W3.5 that motive is a **pair** — the refinement statement, and `vE ⊑ Erasure.visitExpr` —
and this guard says the pair is enough: the walk fires, at a registration premise keyed on
the *shipping* eraser, which is the phrasing `rec_exit_agreement_eraser_quantified_refuted`
below does **not** refute. This is the fixture Γ-W3 could not state: a block reached through
the walked exit, with the eraser left abstract.

**Γ-W3.6b: the last hypothetical binder in this list is gone too.** The guard used to
take `hreg : RecBlockRegistered Γ₀ cctx ref names ctx s₀` — stated at *this* `ctx` and
*this* `s₀`, which step 6's motive quantifies, so it was exactly the premise a step could
not have. It now takes `Hreg : RecBlockAgreement`, whose reader/state quantifier is gated
on `BridgeInv`, and derives the walk's `hreg` from it. Both remaining quantifiers behave:
the configs are pinned by `BridgeInv.cfg` (Γ-W3.6a), so the two-configs refutation cannot
be written, and the registry is canonical by `BridgeInv.consts`/`knames`. So this guard is
now step 6's proof, minus the decomposition of `visitMutual`'s prefix. -/
example {env : VEnv} {Us : List Name} {known : Name → Prop} {Γ₀ Γ : ErasureCtx} {Esrc : SEnv}
    {cfg₀ : ErasureConfig} {gw : Void IO.RealWorld → NameGenerator}
    {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    (H : BridgeHyps env Us Γ₀ gw)
    (Hδ : DeltaHyps env Us known Γ₀ cfg₀ Esrc gw cctx ref)
    (Hβ : BlockHyps env Us known Γ₀ cfg₀ Esrc cctx ref)
    (henv : env.Ordered)
    {vE : Expr → EraseM LBTerm}
    (ih1 : (∀ (e : Expr) (s : ErasureState) (ctx' : ErasureContext) (cc : Core.Context)
          (rf : ST.Ref IO.RealWorld Core.State) (w' : Void IO.RealWorld) (t : LBTerm)
          (s' : ErasureState) (w'' : Void IO.RealWorld),
        vE e s ctx' cc rf w' = .ok (t, s') w'' →
        ∀ (Γ' : ErasureCtx), Γ' = Γ₀.withFixvars Γ'.fixvars →
        ∀ (Δ' : VLCtx), BridgeInv env Us known Γ' cfg₀ (gw w') ctx' s Δ' → Supported known Γ' e →
        (∃ ve, TrExprS env Us Δ' e ve) →
        Erases env Us Γ' Δ' e t ∧ RunConclδ env Us Γ₀ Esrc s s' ∧ gw w' ≤ gw w'') ∧
      vE ⊑ Erasure.visitExpr)
    (Hreg : RecBlockAgreement env Us known Γ₀ cfg₀)
    (hΓ : Γ = Γ₀.withFixvars Γ.fixvars)
    {names : List Name} {ctx : ErasureContext} {s₀ s₁ : ErasureState} {Δ : VLCtx}
    {w w₁ : Void IO.RealWorld} {u₀ : Unit} {n : Name}
    (hkn : ∀ m ∈ names, known (remove_unsafe_rec m))
    (hnd : (names.map remove_unsafe_rec).Nodup)
    (hnmem : n ∈ names.map remove_unsafe_rec)
    (hinv : BridgeInv env Us known Γ cfg₀ (gw w) ctx s₀ Δ)
    (hrun : (do
        let ids ← names.mapM (fun _ => (mkFreshFVarId : EraseM FVarId))
        withReader
            (fun e => { e with
              fixvars := some (Std.HashMap.ofList ((names.map remove_unsafe_rec).zip ids)) }) (do
          let defs ← names.mapM (fun m => do
            let cim ← getConstInfo m
            let t ← withReader (fun e => { e with lparams := cim.levelParams })
              (do let pe ← prepare_erasure (cim.value! (allowOpaque := true)); vE pe)
            mkDef (remove_unsafe_rec m) (names.map remove_unsafe_rec) t)
          for p in (names.map remove_unsafe_rec).zipIdx do
            modify (fun st => { st with
                constants := st.constants.insert p.1 (toKername p.1),
                gdecls := (toKername p.1, .constantDecl ⟨some (.fix defs p.2)⟩) :: st.gdecls })
          pure ()) : EraseM Unit) s₀ ctx cctx ref w = .ok (u₀, s₁) w₁) :
    RunConclδ env Us Γ₀ Esrc s₀ s₁ ∧ gw w ≤ gw w₁ ∧ (s₁.constants.get? n).isSome :=
  rec_exit_refines_erases H Hδ Hβ henv
    (fun e s ctx' w' t s' w'' hr => ih1.1 e s ctx' cctx ref w' t s' w'' hr)
    ih1.2 hΓ hkn hnd hnmem hinv (Hreg cctx ref hkn hnd hinv) hrun

/-- **Why the walk's registration premise is keyed on the *shipping* eraser** (slice Γ-W3)
— the refutation, in the house style of `bridgeInv_blockReader_refuted`, and the reason
`RecBlockAgreement` is shaped the way it is.

Inside `visitExpr_refines_erases_core` the eraser is the induction's *abstract* fixpoint
argument, so a premise that pins the block the recursive exit builds must quantify over
that argument. Any such premise is **contradictory**, not merely strong: two erasers that
disagree on one sibling's target hand back two different blocks, and `Γ₀.recBodies` can
record only one of them. A `BlockHyps` field of that shape would therefore be vacuously
satisfiable exactly where the slice needs it — the failure mode slice S1e cost +776/−269
to repair, and the reason this premise is *not* in the bundle.

`P` is left abstract: the argument turns only on the agreement being a function of the
eraser, so it refutes every phrasing at once.

**And this is the shape the reader-quantified premise had to avoid** (slice Γ-W3.6b). The
same argument, with "two erasers" replaced by "two readers whose `Erasure.Config` differs",
is what kept `RecBlockAgreement` unwritable at Γ-W3.5. It cannot be run any more: the
premise is gated on `BridgeInv`, whose `cfg` field pins `ctx.config = cfg₀`, so there is no
pair of admissible readers to instantiate `P` at. The refutation is *closed by the config
gate*, not withdrawn — the instance below still exhibits the two blocks, and the theorem
still refutes any phrasing that quantifies the eraser. -/
theorem rec_exit_agreement_eraser_quantified_refuted {Γ₀ : ErasureCtx} {n : Name}
    {P : (Expr → EraseM LBTerm) → List (@FixDef LBTerm) → Prop}
    (hagree : ∀ (vE : Expr → EraseM LBTerm) (d : List (@FixDef LBTerm)), P vE d →
      Γ₀.recBodies n = some (d, 0))
    {vE₁ vE₂ : Expr → EraseM LBTerm} {d₁ d₂ : List (@FixDef LBTerm)}
    (h₁ : P vE₁ d₁) (h₂ : P vE₂ d₂) (hne : d₁ ≠ d₂) : False := by
  have e₁ := hagree _ _ h₁
  have e₂ := hagree _ _ h₂
  rw [e₁] at e₂
  exact hne (by simpa using Option.some.inj e₂)

/-- The instance: two erasers really do give different blocks. `mkDef` copies its body
argument through `closeFix`, and `closeFix` is the identity on the two closed leaves an
eraser can return, so a `.box`-returning eraser and a `.const`-returning one disagree on
the nose.

Kept, and worth keeping, because it is the *only* exhibited witness in this area. Since
Γ-W3.5 it no longer applies to the walk's premise — that is keyed on `Erasure.visitExpr`,
so there is one eraser — and since Γ-W3.6a it does not apply to the reader quantifier
either: the two-configs version of this witness would need two admissible readers, and
`BridgeInv.cfg` admits one. Closed by the config gate. -/
theorem rec_exit_block_ne_of_body_ne (x : FVarId) (kn : Kername) :
    closeFix [x] 0 (.box : LBTerm) ≠ closeFix [x] 0 (.const kn) := by
  simp [closeFix, closeFixFold, toBvar]

/-- **(i''') The new `Γ` binder is load-bearing** (slice Γ-W1), and this is the guard that
says so: the core's erasure conjunct is available at an arbitrary **block-local** context
`Γ₀.withFixvars fv`, with the δ conclusion still reported at the ambient `Γ₀`. That is
precisely the instantiation step 6's recursive exit needs and precisely what the two
theorems above show a *fixed*-`Γ` motive cannot supply — and the coherence hypothesis is
discharged by `rfl`, since `(Γ₀.withFixvars fv).fixvars` is `fv`.

Note what is *not* re-proved: the four trust bundles and `Hδ` are the ambient ones,
unchanged. Only `Γ` moved. -/
example {env : VEnv} {Us : List Name} {known : Name → Prop} {Γ₀ : ErasureCtx} {Esrc : SEnv}
    {cfg₀ : ErasureConfig} {gw : Void IO.RealWorld → NameGenerator}
    (H : BridgeHyps env Us Γ₀ gw) (HD : DataBridgeHyps Γ₀ gw) (C : CasesBridgeHyps Γ₀ gw) (P : ProjBridgeHyps Γ₀ gw)
    (Hδ : ∀ (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State),
      DeltaHyps env Us known Γ₀ cfg₀ Esrc gw cctx ref)
    (Hβ : ∀ (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State),
      BlockHyps env Us known Γ₀ cfg₀ Esrc cctx ref)
    (Hreg : RecBlockAgreement env Us known Γ₀ cfg₀)
    (henv : env.Ordered) (fv : Name → Option FVarId) :
    ∀ e s ctx cctx ref w t s' w',
      Erasure.visitExpr e s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ, BridgeInv env Us known (Γ₀.withFixvars fv) cfg₀ (gw w) ctx s Δ →
        Supported known (Γ₀.withFixvars fv) e → (∃ ve, TrExprS env Us Δ e ve) →
        Erases env Us (Γ₀.withFixvars fv) Δ e t ∧
          RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w' :=
  fun e s ctx cctx ref w t s' w' hrun Δ =>
    (visitExpr_refines_erases_core H HD C P Hδ Hβ Hreg henv).1.1
      e s ctx cctx ref w t s' w' hrun (Γ₀.withFixvars fv) rfl Δ

/-- (ii) The non-run premises of `visitExpr_refines_erases` are jointly
instantiable: a concrete one-fvar context (with `TrLCtx` *constructed*, not
assumed) and the supported term `.fvar x` satisfy every premise except the run
itself and the trust bundles, which stay hypothetical because the primitives
are opaque. The fifth bundle (`DeltaHyps`, slice D4a) is hypothetical for exactly the
same reason and no other: at this guard's `known = ⊥` its whole *scope* half is free
(`DeltaHyps.of_bot`), and what is left is the generator bookkeeping for the five
primitives only `visitMutual` reaches. -/
example (env : VEnv) (Us : List Name) (Γ : ErasureCtx) (cfg : ErasureConfig)
    (hkn : ∀ n : Name, Γ.constants n = toKername n) (hfv : Γ.fixvars = fun _ => none)
    (hcfg : Γ.natPeano = true → cfg.nat = .peano)
    (gw : Void IO.RealWorld → NameGenerator)
    (H : BridgeHyps env Us Γ gw) (HD : DataBridgeHyps Γ gw) (C : CasesBridgeHyps Γ gw) (P : ProjBridgeHyps Γ gw)
    (Hδ : ∀ (cc : Core.Context) (rf : ST.Ref IO.RealWorld Core.State),
      DeltaHyps env Us (fun _ => False) Γ cfg (fun _ => none) gw cc rf)
    (Hβ : ∀ (cc : Core.Context) (rf : ST.Ref IO.RealWorld Core.State),
      BlockHyps env Us (fun _ => False) Γ cfg (fun _ => none) cc rf)
    (henv : env.Ordered)
    (x : FVarId) (nm : Name) (bi : BinderInfo)
    (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)
    (w w' : Void IO.RealWorld) (t : LBTerm) (s' : ErasureState)
    (hres : (gw w).Reserves x) (hkfresh : kernelNGen.Reserves x)
    (hrun : Erasure.visitExpr (.fvar x) {}
      ⟨({} : LocalContext).mkLocalDecl x nm (.sort .zero) bi, none, Us, cfg⟩ cctx ref w
      = .ok (t, s') w') :
    Erases env Us Γ [(some (x, (Expr.sort .zero).fvarsList), .vlam (.sort .zero))]
      (.fvar x) t ∧ RunConclδ env Us Γ (fun _ => none) ({} : ErasureState) s' ∧
      gw w ≤ gw w' := by
  have hty : TrExprS env Us [] (.sort .zero) (.sort .zero) := .sort rfl
  have hty' : env.IsType Us.length (VLCtx.toCtx []) (.sort .zero) :=
    ⟨_, .sortDF trivial trivial rfl⟩
  have hfind : ({} : LocalContext).find? x = none :=
    (Lean4Lean.TrLCtx.nil (env := env) (Us := Us)).find?_eq_none.mpr (fun h => nomatch h)
  have hinv : BridgeInv env Us (fun _ => False) Γ cfg (gw w)
      ⟨({} : LocalContext).mkLocalDecl x nm (.sort .zero) bi, none, Us, cfg⟩ {}
      [(some (x, (Expr.sort .zero).fvarsList), .vlam (.sort .zero))] :=
    { mlc := ⟨(MLCtx.nil).vlam x nm (.sort .zero) (.sort .zero) bi,
        ⟨trivial, hfind, hty, hty'⟩, rfl, rfl⟩
      lparams := List.prefix_refl _
      cfg := rfl
      natcfg := hcfg
      kfresh := by
        intro fv hfv
        have : fv = x ∨ fv ∈ VLCtx.fvars [] := by simpa using hfv
        rcases this with rfl | h
        · exact hkfresh
        · exact nomatch h
      fixvars := by intro nm y; rw [hfv]; simp
      fixfresh := by intro nm y hy; rw [hfv] at hy; simp at hy
      reserved := by
        intro fv hfv
        have : fv = x ∨ fv ∈ VLCtx.fvars [] := by simpa using hfv
        rcases this with rfl | h
        · exact hres
        · exact nomatch h
      knames := hkn
      consts := by intro n k hk; simp at hk }
  have hfind2 : VLCtx.find?
      [(some (x, (Expr.sort .zero).fvarsList), .vlam (.sort .zero))] (.inr x)
      = some ((VLocalDecl.vlam (.sort .zero)).value, (VLocalDecl.vlam (.sort .zero)).type) := by
    simp [Lean4Lean.VLCtx.find?, Lean4Lean.VLCtx.next]
  have hex : ∃ ve, TrExprS env Us
      [(some (x, (Expr.sort .zero).fvarsList), .vlam (.sort .zero))] (.fvar x) ve :=
    ⟨_, .fvar hfind2⟩
  exact visitExpr_refines_erases H HD C P Hδ Hβ RecBlockAgreement.of_bot henv
    _ _ _ _ _ _ _ _ _ hrun _ hinv (.fvar x) hex


/-- (iii) **The bridge fires on a `Nat` literal** (Nat-literals wall, L4) — the literal
analogue of (ii), and the joint non-vacuity of everything L3 added. *Constructed* here:
the peano config; the context `ΓnatLit` (the same fixture at which `Erases.lean` derives
the tower and `ErasesCorrectData.lean` runs it on both sides); the `BridgeInv`, whose new
`natcfg` field is exactly the config pin and is discharged from `hcfg`; the
`Supported.natLit` derivation; and — the premise that made this guard worth building —
the source translation `∃ ve, TrExprS envNatT [] [] (.lit (.natVal 2)) ve`, at the
three-axiom `envNatT` in which `Nat`'s constructors are declared *and typed*
(`trExprS_natLit`, `Erases.lean`). *Hypothetical*, as in (ii) and for the same reason:
the run equation and the four trust bundles, which speak about opaque primitives.

So the shipping eraser, run on the raw literal node `2` in peano mode, lands inside
`Erases` — and by `Erases.lit_inv` only the box rule or `Erases.lit` can have put it
there. -/
example (cfg : ErasureConfig) (hcfg : cfg.nat = .peano)
    (gw : Void IO.RealWorld → NameGenerator)
    (H : BridgeHyps envNatT [] ΓnatLit gw) (HD : DataBridgeHyps ΓnatLit gw)
    (C : CasesBridgeHyps ΓnatLit gw) (P : ProjBridgeHyps ΓnatLit gw)
    (Hδ : ∀ (cc : Core.Context) (rf : ST.Ref IO.RealWorld Core.State),
      DeltaHyps envNatT [] (fun _ => False) ΓnatLit cfg (fun _ => none) gw cc rf)
    (Hβ : ∀ (cc : Core.Context) (rf : ST.Ref IO.RealWorld Core.State),
      BlockHyps envNatT [] (fun _ => False) ΓnatLit cfg (fun _ => none) cc rf)
    (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)
    (w w' : Void IO.RealWorld) (t : LBTerm) (s' : ErasureState)
    (hrun : Erasure.visitExpr (.lit (.natVal 2)) {} ⟨{}, none, [], cfg⟩ cctx ref w
      = .ok (t, s') w') :
    Erases envNatT [] ΓnatLit [] (.lit (.natVal 2)) t ∧
      RunConclδ envNatT [] ΓnatLit (fun _ => none) ({} : ErasureState) s' ∧
      gw w ≤ gw w' := by
  have hinv : BridgeInv envNatT [] (fun _ => False) ΓnatLit cfg (gw w)
      ⟨{}, none, [], cfg⟩ {} [] :=
    { mlc := ⟨.nil, trivial, rfl, rfl⟩
      lparams := List.prefix_refl _
      cfg := rfl
      natcfg := fun _ => hcfg
      kfresh := fun _ h => nomatch h
      fixvars := by intro nm x; simp [ΓnatLit]
      fixfresh := by intro nm x hx; simp [ΓnatLit] at hx
      reserved := fun _ h => nomatch h
      knames := fun _ => rfl
      consts := by intro n k hk; simp at hk }
  exact visitExpr_refines_erases H HD C P Hδ Hβ RecBlockAgreement.of_bot
    envNatT_wf.ordered _ _ _ _ _ _ _ _ _ hrun _ hinv
    (.natLit 2 (by simp [ΓnatLit]) ΓnatLit_zero ΓnatLit_succ)
    ⟨_, trExprS_natLit 2⟩

/-- (iv) **The cold-start wall, gone** (δ-inclusion, slice D4a) — the counterpart of (i)
at a *non-empty* fragment, and the guard the whole slice exists to make provable.

At the entry configuration the state is the empty one (`ColdStartRun.run_eq`:
`Erasure.run x cfg … = x {} { «config» := cfg } …`). Before this slice the invariant was
*refutable* there for every non-empty fragment, because `known_dom` asserted that a
`known` constant is already registered (`old_known_dom_cold_refuted`, next). Now the
invariant is `known`-blind, so the same configuration carries it at `known = (· = n)` —
and, with `gDeltaSupported` (`DeltaHyps.lean`) exhibiting `Supported known Γ (.const n [])`
at such a fragment, the two premises `visitExpr_refines_erases` needs at a δ-reference are
jointly satisfiable at the cold-start entry. That is δ-inclusion, at the invariant.

**The fragment is not mentioned in the proof, and that is worth stating separately**
(slice Γ-W5): `BridgeInv` takes `known` as a parameter but no field of it mentions the
fragment, so the cold-start instance holds at *any* `known` and the one-name form below is
a specialisation. The general form is what a **mutual** fragment needs — a two-member
block is `known` at two names, and `fun m => m = n` cannot say so. -/
theorem bridgeInv_cold_any (env : VEnv) (Us : List Name) (Γ : ErasureCtx)
    (known : Name → Prop)
    (hkn : ∀ m : Name, Γ.constants m = toKername m) (hfv : Γ.fixvars = fun _ => none)
    (gen : NameGenerator) (cfg : ErasureConfig)
    (hcfg : Γ.natPeano = true → cfg.nat = .peano) :
    BridgeInv env Us known Γ cfg gen ⟨{}, none, Us, cfg⟩ {} [] where
  mlc := ⟨.nil, trivial, rfl, rfl⟩
  lparams := List.prefix_refl _
  cfg := rfl
  natcfg := hcfg
  kfresh := fun _ hfv => nomatch hfv
  fixvars := by intro nm x; rw [hfv]; simp
  fixfresh := by intro nm x hx; rw [hfv] at hx; simp at hx
  reserved := fun _ hfv => nomatch hfv
  knames := hkn
  consts := by intro m k hk; simp at hk

/-- The one-name specialisation, and the form every pre-Γ-W5 consumer takes. -/
theorem bridgeInv_cold_known (env : VEnv) (Us : List Name) (Γ : ErasureCtx)
    (hkn : ∀ m : Name, Γ.constants m = toKername m) (hfv : Γ.fixvars = fun _ => none)
    (gen : NameGenerator) (cfg : ErasureConfig)
    (hcfg : Γ.natPeano = true → cfg.nat = .peano) (n : Name) :
    BridgeInv env Us (fun m => m = n) Γ cfg gen ⟨{}, none, Us, cfg⟩ {} [] :=
  bridgeInv_cold_any env Us Γ _ hkn hfv gen cfg hcfg

/-- (iv') **Why the deleted field could not simply be weakened** — the negative guard,
kept so that the reason `BridgeInv.known_dom` died stays on the record.

Its statement, at the cold-start configuration and any non-empty fragment, is refutable:
nothing is registered at `{}`. Together with `DeltaHyps.constants_get!_unregistered_ne`
(the *other* half: without a registration conclusion from `visitMutual`'s own motive, the
miss branch of `get_constant_kername` returns `default`, which is not the canonical
kername) this pins the shape of the fix that slice D4a implements — delete the field,
give motive 6 content, carry the fragment scope-side in `DeltaHyps`. -/
theorem old_known_dom_cold_refuted (n : Name) :
    ¬ (∀ m : Name, (fun k => k = n) m → ((({} : ErasureState)).constants.get? m).isSome) := by
  intro h
  have := h n rfl
  simp at this

/-- (v) **The bridge fires on a δ-reference, at the cold-start entry state** (δ-inclusion,
slice D4a) — the payoff guard, and the one the whole slice exists for.

Everything except the run, the four trust bundles and the δ/block/agreement premises
(`Hδ`/`Hβ`/`Hreg`) is *constructed*, at a genuinely
non-empty fragment: the invariant at the empty state and a `known` that holds of
`Nat.zero` (`bridgeInv_cold_known` — refutable before this slice,
`old_known_dom_cold_refuted`); the `Supported.const` derivation, whose `known n`
disjunct is what `known = ⊥` used to kill; and the source translation, at the
three-axiom `envNatT` where `Nat.zero` is declared *and typed*.

The run this fires on is one that takes `get_constant_kername`'s **miss** branch — the
constant is not registered at `{}` — so the conclusion is carried by motive 6's
registration content: `visitMutual` registers the name, `s'.constants[n]!` is therefore
the kername the registry holds, and `RunConcl.canon` makes it `Γ`'s. Before this slice
none of that existed and the branch was refuted by fiat. -/
example (cfg : ErasureConfig) (gw : Void IO.RealWorld → NameGenerator)
    (H : BridgeHyps envNatT [] gΓδ gw) (HD : DataBridgeHyps gΓδ gw)
    (C : CasesBridgeHyps gΓδ gw) (P : ProjBridgeHyps gΓδ gw)
    (Hδ : ∀ (cc : Core.Context) (rf : ST.Ref IO.RealWorld Core.State),
      DeltaHyps envNatT [] (fun m => m = ``Nat.zero) gΓδ cfg (fun _ => none) gw cc rf)
    (Hβ : ∀ (cc : Core.Context) (rf : ST.Ref IO.RealWorld Core.State),
      BlockHyps envNatT [] (fun m => m = ``Nat.zero) gΓδ cfg (fun _ => none) cc rf)
    (Hreg : RecBlockAgreement envNatT [] (fun m => m = ``Nat.zero) gΓδ cfg)
    (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)
    (w w' : Void IO.RealWorld) (t : LBTerm) (s' : ErasureState)
    (hrun : Erasure.visitExpr (.const ``Nat.zero []) {} ⟨{}, none, [], cfg⟩ cctx ref w
      = .ok (t, s') w') :
    Erases envNatT [] gΓδ [] (.const ``Nat.zero []) t ∧
      RunConclδ envNatT [] gΓδ (fun _ => none) ({} : ErasureState) s' ∧
      gw w ≤ gw w' :=
  visitExpr_refines_erases H HD C P Hδ Hβ Hreg envNatT_wf.ordered _ _ _ _ _ _ _ _ _ hrun _
    (bridgeInv_cold_known envNatT [] gΓδ (fun _ => rfl) rfl (gw w) cfg
      (fun h => absurd h (by decide)) ``Nat.zero)
    (.const ``Nat.zero [] (Or.inl rfl) rfl rfl)
    ⟨.const ``Nat.zero [], .const envNatT_zero (by simp) (by simp)⟩

/-- **(iv''') The walk's registration premise fires on the measured block shape, at the
cold-start entry configuration** (recursion wall, slice Γ-W3.6b) — the suppliability guard
for `RecBlockAgreement`, in the house style of `DeltaHyps.gBlockKeying`.

`RecBlockAgreement` itself is **taken hypothetically here, and that is the correct
outcome**: its hypothesis is a run of `getConstInfo`/`prepare_erasure`/`visitExpr` at an
abstract `Core.Context` and an opaque world, so no fixture can compute `defs` and compare
it to `ΓfixRec.recBodies `f`. This is exactly how `DeltaHyps.gBlockHyps` handles
`block_lparams` and `block_esrc`, with the same stated reason.

What *is* checked, and it is the thing that matters, is that the premise's **gate is
inhabited on real data** — the S1d/S1e failure mode is a premise satisfiable only
vacuously, precisely where the slice needs it, and this rules that out:

* the keying fires on the shape slice Γ-W0 measured: the block is `[f._unsafe_rec]`, the
  fragment holds the plain `f`, and `remove_unsafe_rec` bridges them (`gBlockKeying`);
* the `BridgeInv` gate is satisfied at the **cold-start entry configuration**
  (`bridgeInv_cold_known`, at a *non-empty* fragment), which is where a capstone stands;
* so the premise really delivers a `RecBlockRegistered` at a configuration the walk
  reaches, rather than being true because nothing satisfies its hypotheses.

And the two ways it could have been *contradictory* are closed by the gate, not by
assumption: `BridgeInv.cfg` (Γ-W3.6a) pins the config, so the two-configs witness — the
only refutation anyone could write, and the one `rec_exit_block_ne_of_body_ne` exhibits
against the *eraser*-quantified phrasing — has nowhere to live; `BridgeInv.consts` and
`knames` pin the registry. What is left is the world, and that is the development's
standing boundary, shared with every run-keyed field. -/
theorem gRecAgreement {env : VEnv} {Us : List Name} {cfg : ErasureConfig}
    (Hreg : RecBlockAgreement env Us (fun n => n = `f) ΓfixRec cfg)
    (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State) (gen : NameGenerator) :
    RecBlockRegistered ΓfixRec cctx ref [`f ++ `_unsafe_rec] ⟨{}, none, Us, cfg⟩ {} :=
  Hreg cctx ref
    (by
      intro m hm
      have hm' : m = `f ++ `_unsafe_rec := by simpa using hm
      subst hm'
      decide)
    (by simp)
    (bridgeInv_cold_known env Us ΓfixRec (fun _ => rfl) rfl gen cfg
      (by simp [ΓfixRec]) `f)

/-! ### (iv'''') The same three, at a genuine **mutual** block (slice Γ-W5)

`gRecAgreement` and every recursion guard before it stand on `ΓfixRec` — a *one*-definition
block, which is all `DeltaHyps.decl_run` admitted until Γ-W5. The three guards below are
their two-member twins, on `Erases.lean`'s `ΓfixMut` (`def f a := g a` / `def g a := f a`)
and `DeltaHyps.gMutualNames` (`[f._unsafe_rec, g._unsafe_rec]`, the measured fetch shape).

What they add over the single-block ones is *index* content: at arity one every ordering
convention agrees, so `hreg`, `closeFix` and `fixSubst` cannot be observed to disagree.
Here they can — `f`'s body erases to a call of `.fix fixMutDefs 1` and `g`'s to a call of
`.fix fixMutDefs 0` — and the registration has to line the fetched names up with the block
*in order*. -/

/-- **The registration conclusion, computed on the two-member block.** This is what
`RecBlockRegistered` delivers, at `ΓfixMut` and the fetched `gMutualNames`: each index of
the block is registered under the matching stripped name. Nothing is assumed — the
agreement is a premise about a *run*, but its conclusion is a `Γ`-side fact, and this is
that fact, true and non-degenerate at arity two. -/
theorem gRecBlockRegisteredMutual (j : Nat) (h : j < fixMutDefs.length) :
    ∃ h' : j < (gMutualNames.map remove_unsafe_rec).length,
      ΓfixMut.recBodies ((gMutualNames.map remove_unsafe_rec)[j]'h')
        = some (fixMutDefs, j) := by
  rw [gMutualNames_stripped]
  exact ⟨by simpa [fixMutNames, fixMutDefs] using h, ΓfixMut_recBodies j h⟩

/-- **…and the agreement's gate is inhabited at a two-name fragment**, so
`RecBlockAgreement` really delivers a `RecBlockRegistered` for the mutual block rather than
being true because nothing satisfies its hypotheses — `gRecAgreement`'s claim, at the arity
the old `decl_run` forbade.

The two fragment-side premises are the ones `DeltaHyps.gDeclRunMutual` checks: both
siblings are `known` at their stripped names, and the stripped names are `Nodup`. The
`BridgeInv` gate is the cold-start entry configuration at the *mutual* fragment, which is
what `bridgeInv_cold_any` is for — `bridgeInv_cold_known`'s `fun m => m = n` cannot express
a two-name fragment, and that limitation was invisible while the fragment could only ever
hold one recursive name at a time. -/
theorem gRecAgreementMutual {env : VEnv} {Us : List Name} {cfg : ErasureConfig}
    (Hreg : RecBlockAgreement env Us knownMutual ΓfixMut cfg)
    (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State) (gen : NameGenerator) :
    RecBlockRegistered ΓfixMut cctx ref gMutualNames ⟨{}, none, Us, cfg⟩ {} :=
  Hreg cctx ref
    (fun m hm => by
      simp only [gMutualNames, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact Or.inl (by decide)
      · exact Or.inr (by decide))
    (by rw [gMutualNames_stripped]; simp [fixMutNames])
    (bridgeInv_cold_any env Us ΓfixMut knownMutual (fun _ => rfl) rfl gen cfg
      (by simp [ΓfixMut]))

/-- **(iv'''') The walk itself, at the mutual block, asked for the *second* sibling.**

Everything the walk needs on the fragment side is discharged concretely: the block is
`gMutualNames`, both members are `known` at their stripped names, the stripped names are
distinct, and the name the caller asked for is `` `g `` — the sibling at index **1**, which
no single-declaration fixture can even name. What stays hypothetical is exactly what stays
hypothetical in guard (iv''): the run, the trust bundles and the registration agreement,
all for reasons that predate this slice and none of them arity-related.

Read with `gRecAgreementMutual` and `DeltaHyps.gDeclRunMutual`, this is the whole
non-vacuity story for the mutual slice: the fetch's report is satisfiable at a two-member
block, the agreement's gate is inhabited there, and the walk composes. -/
example {env : VEnv} {Us : List Name} {Esrc : SEnv} {cfg : ErasureConfig}
    {gw : Void IO.RealWorld → NameGenerator}
    {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    (H : BridgeHyps env Us ΓfixMut gw)
    (Hδ : DeltaHyps env Us knownMutual ΓfixMut cfg Esrc gw cctx ref)
    (Hβ : BlockHyps env Us knownMutual ΓfixMut cfg Esrc cctx ref)
    (henv : env.Ordered)
    {vE : Expr → EraseM LBTerm}
    (ih1 : (∀ (e : Expr) (s : ErasureState) (ctx' : ErasureContext)
          (w' : Void IO.RealWorld) (t : LBTerm) (s' : ErasureState) (w'' : Void IO.RealWorld),
        vE e s ctx' cctx ref w' = .ok (t, s') w'' →
        ∀ (Γ' : ErasureCtx), Γ' = ΓfixMut.withFixvars Γ'.fixvars →
        ∀ (Δ' : VLCtx), BridgeInv env Us knownMutual Γ' cfg (gw w') ctx' s Δ' →
        Supported knownMutual Γ' e → (∃ ve, TrExprS env Us Δ' e ve) →
        Erases env Us Γ' Δ' e t ∧ RunConclδ env Us ΓfixMut Esrc s s' ∧ gw w' ≤ gw w'') ∧
      vE ⊑ Erasure.visitExpr)
    (Hreg : RecBlockAgreement env Us knownMutual ΓfixMut cfg)
    {ctx : ErasureContext} {s₀ s₁ : ErasureState} {Δ : VLCtx}
    {w w₁ : Void IO.RealWorld} {u₀ : Unit}
    (hinv : BridgeInv env Us knownMutual ΓfixMut cfg (gw w) ctx s₀ Δ)
    (hrun : (do
        let ids ← gMutualNames.mapM (fun _ => (mkFreshFVarId : EraseM FVarId))
        withReader
            (fun e => { e with
              fixvars := some
                (Std.HashMap.ofList ((gMutualNames.map remove_unsafe_rec).zip ids)) }) (do
          let defs ← gMutualNames.mapM (fun m => do
            let cim ← getConstInfo m
            let t ← withReader (fun e => { e with lparams := cim.levelParams })
              (do let pe ← prepare_erasure (cim.value! (allowOpaque := true)); vE pe)
            mkDef (remove_unsafe_rec m) (gMutualNames.map remove_unsafe_rec) t)
          for p in (gMutualNames.map remove_unsafe_rec).zipIdx do
            modify (fun st => { st with
                constants := st.constants.insert p.1 (toKername p.1),
                gdecls := (toKername p.1, .constantDecl ⟨some (.fix defs p.2)⟩) :: st.gdecls })
          pure ()) : EraseM Unit) s₀ ctx cctx ref w = .ok (u₀, s₁) w₁) :
    RunConclδ env Us ΓfixMut Esrc s₀ s₁ ∧ gw w ≤ gw w₁ ∧
      (s₁.constants.get? `g).isSome := by
  have hkn : ∀ m ∈ gMutualNames, knownMutual (remove_unsafe_rec m) := fun m hm => by
    simp only [gMutualNames, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact Or.inl (by decide)
    · exact Or.inr (by decide)
  have hnd : (gMutualNames.map remove_unsafe_rec).Nodup := by
    rw [gMutualNames_stripped]; simp [fixMutNames]
  have hnmem : `g ∈ gMutualNames.map remove_unsafe_rec := by
    rw [gMutualNames_stripped]; simp [fixMutNames]
  exact rec_exit_refines_erases H Hδ Hβ henv
    (fun e s ctx' w' t s' w'' hr => ih1.1 e s ctx' w' t s' w'' hr)
    ih1.2 rfl hkn hnd hnmem hinv (Hreg cctx ref hkn hnd hinv) hrun

/-! ### (v) The projection fragment, end to end (projection round, slice P8) -/

/-- The `InductiveId` `register_inductive` would assign to `ProjPattern.lean`'s one-field
type class `MyOfNat`. -/
def qprojInd : InductiveId := ⟨toKername `MyOfNat, 0⟩

/-- A `Γ` registering `MyOfNat` as a **two-parameter, one-field** structure — the shape
`ProjPattern.envQ` gives it (`QN = MyOfNat N n0`, `mkappQ = MyOfNat.mk N n0 _`), and the
shape `register_inductive`'s `is_struct` gate admits (one constructor, one field, not
recursive). Non-degenerate in the way the projection round needs: `ctorArities = 3 =
2 params + 1 field`, so a bridge that confused `paramCount` with `fieldIdx` would emit a
different `ProjectionInfo`. -/
def ΓprojQ : ErasureCtx where
  inductives := fun n => if n = `MyOfNat then some qprojInd else none
  constants := toKername
  ctors := fun n => if n = `MyOfNat.mk then some (qprojInd, 0) else none
  ctorArities := fun n => if n = `MyOfNat.mk then some 3 else none
  ctorFields := fun _ => some [1]
  projs := fun n => if n = `MyOfNat then some (qprojInd, 2) else none

theorem ΓprojQ_projs : ΓprojQ.projs `MyOfNat = some (qprojInd, 2) := by simp [ΓprojQ]

/-- **`Supported.proj` is reachable at the payoff term** — the class method's prepared
body `fun (self : MyOfNat N n0) => self.ofNat`, which is what makes
`DeltaHyps.prepared`'s first conjunct satisfiable for the typeclass layer. Note the
`known` class is **empty**: the body references no constant at all, so the projection
node is the only thing the fragment has to admit. -/
theorem supported_ofNatBodyQ : Supported (fun _ => False) ΓprojQ ofNatBodyQ :=
  .lam `self _ .instImplicit (.proj ΓprojQ_projs rfl (by omega) (.bvar 0))

/-- **(v) The bridge fires on a term containing a projection** — the projection analogue
of guards (ii)/(iii), and the payoff shape of the whole round.

*Constructed* here, and each piece is the thing a vacuous guard would be missing: the
context `ΓprojQ`; the `BridgeInv` at the empty `VLCtx` (the body is closed, so guard (i)'s
instance applies); the `Supported` derivation, which is where the new `Supported.proj`
alternative — and hence motive 10, the arm that discharges it — is exercised; and the
source translation `TrExprS envQ [] [] ofNatBodyQ _` (`ProjPattern.lean`), the one
translation in the development that goes **through** a `TrProj`.

*Hypothetical*, and for reasons that all predate this slice: the run and the four trust
bundles (opaque runtime primitives — the standing boundary), `DeltaHyps`/`BlockHyps` (as
in (ii): at `known = ⊥` their whole scope half is free and what is left is the generator
bookkeeping for the primitives only `visitMutual` reaches), and `envQ.Ordered` — `envQ` is
built by `VEnv.addPat`, and `VEnv.Ordered` has no `addPat` clause at this pin, which
`ProjPattern.lean`'s own module note records. **No new class of hypothesis** is introduced
by the projection round: `ProjBridgeHyps` joins the three bundles already here, and is
`env`/`Us`-free. -/
example (cfg : ErasureConfig) (gw : Void IO.RealWorld → NameGenerator)
    (H : BridgeHyps envQ [] ΓprojQ gw) (HD : DataBridgeHyps ΓprojQ gw)
    (C : CasesBridgeHyps ΓprojQ gw) (P : ProjBridgeHyps ΓprojQ gw)
    (Hδ : ∀ (cc : Core.Context) (rf : ST.Ref IO.RealWorld Core.State),
      DeltaHyps envQ [] (fun _ => False) ΓprojQ cfg (fun _ => none) gw cc rf)
    (Hβ : ∀ (cc : Core.Context) (rf : ST.Ref IO.RealWorld Core.State),
      BlockHyps envQ [] (fun _ => False) ΓprojQ cfg (fun _ => none) cc rf)
    (henv : envQ.Ordered)
    (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)
    (w w' : Void IO.RealWorld) (t : LBTerm) (s' : ErasureState)
    (hrun : Erasure.visitExpr ofNatBodyQ {} ⟨{}, none, [], cfg⟩ cctx ref w
      = .ok (t, s') w') :
    Erases envQ [] ΓprojQ [] ofNatBodyQ t ∧
      RunConclδ envQ [] ΓprojQ (fun _ => none) ({} : ErasureState) s' ∧
      gw w ≤ gw w' :=
  visitExpr_refines_erases H HD C P Hδ Hβ RecBlockAgreement.of_bot henv
    _ _ _ _ _ _ _ _ _ hrun _
    { mlc := ⟨.nil, trivial, rfl, rfl⟩
      lparams := List.prefix_refl _
      cfg := rfl
      natcfg := fun h => absurd h (by simp [ΓprojQ])
      kfresh := fun _ hfv => nomatch hfv
      fixvars := by intro nm x; simp [ΓprojQ]
      fixfresh := by intro nm x hx; simp [ΓprojQ] at hx
      reserved := fun _ hfv => nomatch hfv
      knames := fun _ => rfl
      consts := by intro n k hk; simp at hk }
    supported_ofNatBodyQ ⟨_, trExprSQ_ofNatBody⟩

end NonVacuity

/- Axiom audit (2026-07-07, via temporary `#print axioms`, since removed;
re-checked 2026-08-10 after the ι widening, 2026-08-12 after the cold-start S2
widening and again after the Nat-literals L3 widening — **unchanged** every time.
Re-measured 2026-08-27, after the Γ-XL recursion wave, the projection round and
the two lean4lean re-pins: the lists below are current.
L3 added no axiom either: the literal path introduces no primitive and no trust
clause (`visitLiteral` calls `visitConstructor`, whose `DataBridgeHyps` clauses are
keyed on `Γ.ctors` and already cover `Nat.zero`/`Nat.succ`), and `BridgeInv.natcfg` is
a side condition on the parameter `Γ` — like S2's `knames` — discharged at every
construction site. S2 added no axiom: `Erasure.RunConcl` /
`Erasure.StateLe` / `Erasure.run_register_inductive_runConcl` are pure `EraseM` state
reasoning (`[propext, Classical.choice, Quot.sound]`), `BridgeInv.mono_state` inherits
only what `BridgeInv` already did, and the six deleted `s = s₁` bundle clauses were
assumptions, not axioms. Earlier: the `CasesBridgeHyps` trust is a `Prop` bundle, never
an axiom, and the pure helpers (`run_array_forIn_ok'`, `visitCases_match_default`,
`slice_toArray_toList_drop`, `list_split_cases`, `subarray_next?_facts`,
`rco_toArray_*`, `IsLamTelescope.instantiate1'`) are at most the four standard
axioms):
* `visitExpr_refines_erases` / `visitExpr_refines_erases_core` /
  `visitExpr_refines_erases_block`:
  `[propext, Classical.choice, Quot.sound, Expr.instantiate1_eq,
    PersistentArray.toList'_push, PersistentHashMap.WF.find?_eq,
    PersistentHashMap.WF.toList'_insert]`
* `rec_exit_refines_erases` (the walked recursive exit, Γ-W3/Γ-W3.6b): the same
  list one item smaller — no `Expr.instantiate1_eq`;
* pure helpers (`VLCtx.find?_bvar_none_of_noBV`, `Supported.getAppFn`,
  `supported_foldl_app_inv`, `getAppArgs_spine`, `run_fvar_to_name`):
  `[propext, Classical.choice, Quot.sound]` or less;
* `spine_arg_facts`, `BridgeInv`, `BridgeInv.mono`, `BridgeInv.mono_state`,
  `BridgeInv.withFixvars`: `[propext, Classical.choice, Quot.sound]`;
  `BridgeInv.mkLocalDecl`/`mkLetDecl` additionally carry the three
  `PersistentArray`/`PersistentHashMap` modeling axioms.

**No `sorryAx`, as of the `fee3ada` re-pin (2026-08-27) — and this is the
headline result of that re-pin.** Every entry above used to carry it. The
reason was never a gap in *this* proof: `TrProj` was a `sorry`-valued
definition upstream, so `sorryAx` entered through the very *type* of every
`TrExprS`-adjacent statement, proof or no proof. lean4lean's `trproj` round
gave `TrProj` a real definition (`#print axioms Lean4Lean.TrProj` is
`[propext]`), and the whole bridge came out clean with it — along with 110
other declarations in `scratch/final_audit.lean`. So the claim that the
shipping eraser refines `Erases` now rests on no lean4lean `sorry` at all.

What remains are lean4lean's *modeling* axioms for the untrusted-representation
surface — `Expr.instantiate1_eq` and the `PersistentArray`/`PersistentHashMap`
ones, entering via Bridge.lean's `find?` lemmas and the
`instantiate1 → instantiate1'` transport. The capstones downstream still report
`sorryAx`, but they get it from the *forward-simulation* half (unique typing:
`TrExprS.uniq` → `TrProj.uniq`, and `IsDefEq.uniqU`), not from here — see
`ColdStart.lean`'s inherited-boundary section. No `sorry` of our own, no new
axioms, no `native_decide`. -/

end LeanToLambdaBox
