import LeanToLambdaBox.ErasureRun
import LeanToLambdaBox.Bridge
import LeanToLambdaBox.DataBridgeHyps
import LeanToLambdaBox.CasesBridgeHyps
import LeanToLambdaBox.DeltaHyps
import LeanToLambdaBox.EraseCore
import LeanToLambdaBox.CheckerAdequacy
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

* **`BridgeHyps`** / **`DataBridgeHyps`** / **`CasesBridgeHyps`** — the three
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
  specs and `CasesBridgeHyps` (`CasesBridgeHyps.lean`) the ι (`casesOn`) path's;
  all three are consumed by the single induction below. A fourth,
  `DeltaHyps` (`DeltaHyps.lean`), carries the δ (constant-unfolding) fragment's
  *scope* obligations — it is the scope-side half of the two-part contract whose
  state-side half is `BridgeInv` — and since slice D4a this induction consumes it
  too, in step 6 (see `BridgeInv`'s docstring for the field its arrival replaced).
* **`BridgeInv`** — the induction invariant: the reader's `LocalContext`
  corresponds to the typing context `Δ` (lean4lean's `TrLCtx`), the reader's
  block-local `fixvars` map agrees with `Γ.fixvars` (and its ids are fresh for `Δ`),
  every fvar of `Δ` is reserved by the current generator, and every *registered*
  kername agrees with `Γ` (the soundness direction only — since slice D4a the
  invariant says nothing about `known`; see its docstring).
* **`visitExpr_refines_erases`** — the final export (motive 1 of the
  18-motive induction `visitExpr_refines_erases_core`).

Trust boundary: results inherit `sorryAx` through lean4lean's `TrExprS`
structural lemmas exactly as documented in `Erases.lean`, plus lean4lean's
`Expr`/`PersistentHashMap` modeling axioms (through `Bridge.lean`'s `find?`
lemmas and `instantiate1_eq`). No `sorry` of our own, no new axioms.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure
open Lean4Lean.TypeChecker (MLCtx kernelNGen)

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
    (b = true → ctx.lparams = Us → ∀ (m : MLCtx) (ve : VExpr), m.WF env Us → m.lctx = ctx.lctx →
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
`ctx.lparams = Us`, and `kfresh` says every `Δ`-fvar is reserved by the kernel's
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
    (Γ : ErasureCtx) (gen : NameGenerator)
    (ctx : Erasure.ErasureContext) (s : Erasure.ErasureState) (Δ : VLCtx) : Prop where
  mlc : ∃ m : MLCtx, m.WF env Us ∧ m.lctx = ctx.lctx ∧ m.vlctx = Δ
  lparams : ctx.lparams = Us
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
    {Γ : ErasureCtx} {gen : NameGenerator} {ctx : ErasureContext}
    {s : ErasureState} {Δ : VLCtx}
    (h : BridgeInv env Us known Γ gen ctx s Δ) : TrLCtx env Us ctx.lctx Δ := by
  obtain ⟨m, mwf, hlctx, hvlctx⟩ := h.mlc
  rw [← hlctx, ← hvlctx]; exact mwf.tr

/-- The invariant is monotone in the generator (fvar reservations survive
generator advancement). The `MLCtx`/`lparams`/`kfresh` data is generator-free. -/
theorem BridgeInv.mono {env : VEnv} {Us : List Name} {known : Name → Prop}
    {Γ : ErasureCtx} {gen gen' : NameGenerator} {ctx : ErasureContext}
    {s : ErasureState} {Δ : VLCtx}
    (h : BridgeInv env Us known Γ gen ctx s Δ) (hle : gen ≤ gen') :
    BridgeInv env Us known Γ gen' ctx s Δ where
  mlc := h.mlc
  lparams := h.lparams
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
    {Γ : ErasureCtx} {gen : NameGenerator} {ctx : ErasureContext}
    {s s' : ErasureState} {Δ : VLCtx}
    (h : BridgeInv env Us known Γ gen ctx s Δ) (hrc : Erasure.RunConcl s s') :
    BridgeInv env Us known Γ gen ctx s' Δ where
  mlc := h.mlc
  lparams := h.lparams
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

/-- Extend the invariant across `Erasure.withLocalDecl`'s context extension
(the `visitLambda` case). Needs the fresh fvar `x` reserved both by the target
generator (`hres`) and by the kernel generator (`hkres`, from `fresh_run`). -/
theorem BridgeInv.mkLocalDecl {env : VEnv} {Us : List Name} {known : Name → Prop}
    {Γ : ErasureCtx} {gen gen' : NameGenerator} {ctx : ErasureContext}
    {s : ErasureState} {Δ : VLCtx} {x : FVarId} {n : Name} {ty : Expr} {ty' : VExpr}
    {bi : BinderInfo}
    (hinv : BridgeInv env Us known Γ gen ctx s Δ)
    (hty : TrExprS env Us Δ ty ty') (hty' : env.IsType Us.length Δ.toCtx ty')
    (hx : x ∉ Δ.fvars) (hnres : ¬ gen.Reserves x)
    (hle : gen ≤ gen') (hres : gen'.Reserves x)
    (hkres : kernelNGen.Reserves x) :
    BridgeInv env Us known Γ gen'
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
    {Γ : ErasureCtx} {gen gen' : NameGenerator} {ctx : ErasureContext}
    {s : ErasureState} {Δ : VLCtx} {x : FVarId} {n : Name} {ty v : Expr}
    {ty' val' : VExpr}
    (hinv : BridgeInv env Us known Γ gen ctx s Δ)
    (hty : TrExprS env Us Δ ty ty') (hval : TrExprS env Us Δ v val')
    (hvt : env.HasType Us.length Δ.toCtx val' ty')
    (hx : x ∉ Δ.fvars) (hnres : ¬ gen.Reserves x)
    (hle : gen ≤ gen') (hres : gen'.Reserves x)
    (hkres : kernelNGen.Reserves x) :
    BridgeInv env Us known Γ gen'
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
    {Γ : ErasureCtx} {gw : Void IO.RealWorld → NameGenerator}
    (H : BridgeHyps env Us Γ gw) (henv : env.Ordered)
    (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State) :
    ∀ (n : Nat) (e ty : Expr) (Δ : VLCtx)
      (K : Expr → List FVarId → EraseM (List BinderName × LBTerm))
      (s : ErasureState) (ctx : ErasureContext) (w : Void IO.RealWorld)
      (r : List BinderName × LBTerm) (s' : ErasureState) (w' : Void IO.RealWorld),
      Erasure.lambdaOrIntroToArity e ty n K s ctx cctx ref w = .ok (r, s') w' →
      BridgeInv env Us known Γ (gw w) ctx s Δ →
      IsLamTelescope n e → Supported known Γ e → (∃ ve, TrExprS env Us Δ e ve) →
      ForallMatchesLam ty e →
      ∃ (ys : List FVarId) (efin : Expr) (Δ' : VLCtx) (ctx' : ErasureContext)
        (w₁ : Void IO.RealWorld),
        ys.length = n ∧ gw w ≤ gw w₁ ∧
        BridgeInv env Us known Γ (gw w₁) ctx' s Δ' ∧
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

/-! ## The main induction -/

set_option maxHeartbeats 1000000 in
/-- **The bridge, all 18 motives.** Content motives: 1 (`visitExpr`),
3 (`visitConstructor`), 4 (`visitConst`), 5 (`get_constant_kername`),
7 (`visitAppArgs`), 8 (`visitLet`), 9 (`visitLambda`), 11 (`visitApp`),
12 (`visitConstApp`), 13/14 (`visitCtorEta`/`Go`) and — the ι fragment,
`Supported.casesApp` — 15/16 (`visitCasesEta`/`Go`), 17 (`visitCases`),
18 (`visitAlt`); the remaining ones carry `True` conclusions in canonical run-ok
shape (their branches are unreachable from the supported fragment).

Motive 18 opens the alternative's full λ-telescope (`bridge_alt_telescope`),
so `Erases.cases`' `harity` premise is met at each constructor's real field
count. -/
theorem visitExpr_refines_erases_core {env : VEnv} {Us : List Name}
    {known : Name → Prop} {Γ : ErasureCtx} {Esrc : SEnv}
    {gw : Void IO.RealWorld → NameGenerator}
    (H : BridgeHyps env Us Γ gw) (HD : DataBridgeHyps Γ gw) (C : CasesBridgeHyps Γ gw)
    (Hδ : ∀ (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State),
      DeltaHyps env Us known Γ Esrc gw cctx ref)
    (henv : env.Ordered) :
    (∀ e s ctx cctx ref w t s' w', visitExpr e s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ, BridgeInv env Us known Γ (gw w) ctx s Δ → Supported known Γ e →
      (∃ ve, TrExprS env Us Δ e ve) →
      Erases env Us Γ Δ e t ∧ RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w') ∧
    (∀ l s ctx cctx ref w r s' w', visitLiteral l s ctx cctx ref w = .ok (r, s') w' →
      ∀ Δ (n : Nat) (iid : InductiveId),
        BridgeInv env Us known Γ (gw w) ctx s Δ →
        l = .natVal n → Γ.natPeano = true →
        Γ.ctors ``Nat.zero = some (iid, 0) → Γ.ctors ``Nat.succ = some (iid, 1) →
        (∃ ve, TrExprS env Us Δ (.lit l) ve) →
        Erases env Us Γ Δ (.lit l) r ∧ RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w') ∧
    (∀ cn args s ctx cctx ref w t s' w',
      visitConstructor cn args s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ (us : List Level) (iid : InductiveId) (cidx : Nat),
        BridgeInv env Us known Γ (gw w) ctx s Δ →
        Γ.ctors cn = some (iid, cidx) →
        (ctx.config.nat = .peano ∨ (cn ≠ ``Nat.zero ∧ cn ≠ ``Nat.succ)) →
        (∀ i (hi : i < args.size), Supported known Γ (args[i]) ∧
          ∃ ve, TrExprS env Us Δ (args[i]) ve) →
        Erases env Us Γ Δ (args.foldl Expr.app (.const cn us)) t ∧ RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w') ∧
    (∀ e s ctx cctx ref w t s' w', visitConst e s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ, BridgeInv env Us known Γ (gw w) ctx s Δ →
      ∀ n us, e = .const n us → (known n ∨ Γ.fixvars n ≠ none) →
      Γ.ctors n = none → Γ.casesOns n = none →
      Erases env Us Γ Δ e t ∧ RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w') ∧
    (∀ n s ctx cctx ref w kn s' w',
      get_constant_kername n s ctx cctx ref w = .ok (kn, s') w' →
      ∀ Δ, BridgeInv env Us known Γ (gw w) ctx s Δ → known n →
      kn = Γ.constants n ∧ RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w') ∧
    (∀ n s ctx cctx ref w r s' w', visitMutual n s ctx cctx ref w = .ok (r, s') w' →
      ∀ Δ, BridgeInv env Us known Γ (gw w) ctx s Δ → known n →
      RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w' ∧ (s'.constants.get? n).isSome) ∧
    (∀ f' args s ctx cctx ref w t s' w',
      visitAppArgs f' args s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ (hd : Expr), BridgeInv env Us known Γ (gw w) ctx s Δ →
      Erases env Us Γ Δ hd f' →
      (∀ i (hi : i < args.size), Supported known Γ (args[i]) ∧
        ∃ ve, TrExprS env Us Δ (args[i]) ve) →
      Erases env Us Γ Δ (args.foldl Expr.app hd) t ∧ RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w') ∧
    (∀ e s ctx cctx ref w t s' w', visitLet e s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ, BridgeInv env Us known Γ (gw w) ctx s Δ →
      ∀ n ty v b nd, e = .letE n ty v b nd → Supported known Γ e →
      (∃ ve, TrExprS env Us Δ e ve) →
      Erases env Us Γ Δ e t ∧ RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w') ∧
    (∀ e s ctx cctx ref w t s' w', visitLambda e s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ, BridgeInv env Us known Γ (gw w) ctx s Δ →
      ∀ n ty b bi, e = .lam n ty b bi → Supported known Γ e →
      (∃ ve, TrExprS env Us Δ e ve) →
      Erases env Us Γ Δ e t ∧ RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w') ∧
    (∀ tn i e s ctx cctx ref w r s' w',
      visitProj tn i e s ctx cctx ref w = .ok (r, s') w' → True) ∧
    (∀ e s ctx cctx ref w t s' w', visitApp e s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ, BridgeInv env Us known Γ (gw w) ctx s Δ → Supported known Γ e →
      (∃ ve, TrExprS env Us Δ e ve) →
      Erases env Us Γ Δ e t ∧ RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w') ∧
    (∀ e s ctx cctx ref w t s' w', visitConstApp e s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ, BridgeInv env Us known Γ (gw w) ctx s Δ → Supported known Γ e →
      (∃ ve, TrExprS env Us Δ e ve) →
      ∀ cn us, e.getAppFn = .const cn us →
      Erases env Us Γ Δ e t ∧ RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w') ∧
    (∀ cn ar e s ctx cctx ref w t s' w',
      visitCtorEta cn ar e s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ (us : List Level) (iid : InductiveId) (cidx : Nat),
        BridgeInv env Us known Γ (gw w) ctx s Δ →
        e.getAppFn = .const cn us → Γ.ctors cn = some (iid, cidx) →
        Γ.ctorArities cn = some ar → ar ≤ e.getAppArgs.size →
        cn ≠ ``Nat.zero → cn ≠ ``Nat.succ →
        (∀ i (hi : i < e.getAppArgs.size), Supported known Γ (e.getAppArgs[i]) ∧
          ∃ ve, TrExprS env Us Δ (e.getAppArgs[i]) ve) →
        Erases env Us Γ Δ e t ∧ RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w') ∧
    (∀ cn ar ty fe args s ctx cctx ref w t s' w',
      visitCtorEtaGo cn ar ty fe args s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ (us : List Level) (iid : InductiveId) (cidx : Nat),
        BridgeInv env Us known Γ (gw w) ctx s Δ →
        Γ.ctors cn = some (iid, cidx) → Γ.ctorArities cn = some ar → ar ≤ args.size →
        cn ≠ ``Nat.zero → cn ≠ ``Nat.succ →
        (∀ i (hi : i < args.size), Supported known Γ (args[i]) ∧
          ∃ ve, TrExprS env Us Δ (args[i]) ve) →
        Erases env Us Γ Δ (args.foldl Expr.app (.const cn us)) t ∧ RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w') ∧
    (∀ ci e s ctx cctx ref w t s' w',
      visitCasesEta ci e s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ (con : Name) (us : List Level) (iid : InductiveId) (np dp : Nat) (nfs : List Nat),
        BridgeInv env Us known Γ (gw w) ctx s Δ →
        e.getAppFn = .const con us →
        Γ.casesOns con = some (iid, np) → Γ.casesDiscrPos con = some dp →
        Γ.ctorFields iid = some nfs →
        CasesInfoAgrees ci con dp nfs →
        con.getPrefix ≠ ``Nat → con.getPrefix ≠ ``Int →
        dp + 1 + nfs.length ≤ e.getAppArgs.size →
        CasesSpineFacts env Us known Γ Δ dp nfs e.getAppArgs →
        Erases env Us Γ Δ e t ∧ RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w') ∧
    (∀ ci ty fe args s ctx cctx ref w t s' w',
      visitCasesEtaGo ci ty fe args s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ (con : Name) (us : List Level) (iid : InductiveId) (np dp : Nat) (nfs : List Nat),
        BridgeInv env Us known Γ (gw w) ctx s Δ →
        Γ.casesOns con = some (iid, np) → Γ.casesDiscrPos con = some dp →
        Γ.ctorFields iid = some nfs →
        CasesInfoAgrees ci con dp nfs →
        con.getPrefix ≠ ``Nat → con.getPrefix ≠ ``Int →
        dp + 1 + nfs.length ≤ args.size →
        CasesSpineFacts env Us known Γ Δ dp nfs args →
        Erases env Us Γ Δ (args.foldl Expr.app (.const con us)) t ∧ RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w') ∧
    (∀ ci args s ctx cctx ref w t s' w',
      visitCases ci args s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ (con : Name) (us : List Level) (iid : InductiveId) (np dp : Nat) (nfs : List Nat),
        BridgeInv env Us known Γ (gw w) ctx s Δ →
        Γ.casesOns con = some (iid, np) → Γ.casesDiscrPos con = some dp →
        Γ.ctorFields iid = some nfs →
        CasesInfoAgrees ci con dp nfs →
        con.getPrefix ≠ ``Nat → con.getPrefix ≠ ``Int →
        dp + 1 + nfs.length ≤ args.size →
        CasesSpineFacts env Us known Γ Δ dp nfs args →
        Erases env Us Γ Δ (args.foldl Expr.app (.const con us)) t ∧ RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w') ∧
    (∀ nf mask e s ctx cctx ref w r s' w',
      visitAlt nf mask e s ctx cctx ref w = .ok (r, s') w' →
      ∀ Δ, BridgeInv env Us known Γ (gw w) ctx s Δ →
        mask = Array.replicate nf .keep →
        IsLamTelescope nf e → Supported known Γ e →
        (∃ ve, TrExprS env Us Δ e ve) →
        r.1.length = nf ∧ Erases env Us Γ Δ e (mkLambdas r.1 r.2) ∧
          RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w') := by
  apply visitExpr.mutual_fixpoint_induct
    (motive_1 := fun f => ∀ e s ctx cctx ref w t s' w',
      f e s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ, BridgeInv env Us known Γ (gw w) ctx s Δ → Supported known Γ e →
      (∃ ve, TrExprS env Us Δ e ve) →
      Erases env Us Γ Δ e t ∧ RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w')
    (motive_2 := fun f => ∀ l s ctx cctx ref w r s' w',
      f l s ctx cctx ref w = .ok (r, s') w' →
      ∀ Δ (n : Nat) (iid : InductiveId),
        BridgeInv env Us known Γ (gw w) ctx s Δ →
        l = .natVal n → Γ.natPeano = true →
        Γ.ctors ``Nat.zero = some (iid, 0) → Γ.ctors ``Nat.succ = some (iid, 1) →
        (∃ ve, TrExprS env Us Δ (.lit l) ve) →
        Erases env Us Γ Δ (.lit l) r ∧ RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w')
    (motive_3 := fun f => ∀ cn args s ctx cctx ref w t s' w',
      f cn args s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ (us : List Level) (iid : InductiveId) (cidx : Nat),
        BridgeInv env Us known Γ (gw w) ctx s Δ →
        Γ.ctors cn = some (iid, cidx) →
        (ctx.config.nat = .peano ∨ (cn ≠ ``Nat.zero ∧ cn ≠ ``Nat.succ)) →
        (∀ i (hi : i < args.size), Supported known Γ (args[i]) ∧
          ∃ ve, TrExprS env Us Δ (args[i]) ve) →
        Erases env Us Γ Δ (args.foldl Expr.app (.const cn us)) t ∧ RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w')
    (motive_4 := fun f => ∀ e s ctx cctx ref w t s' w',
      f e s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ, BridgeInv env Us known Γ (gw w) ctx s Δ →
      ∀ n us, e = .const n us → (known n ∨ Γ.fixvars n ≠ none) →
      Γ.ctors n = none → Γ.casesOns n = none →
      Erases env Us Γ Δ e t ∧ RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w')
    (motive_5 := fun f => ∀ n s ctx cctx ref w kn s' w',
      f n s ctx cctx ref w = .ok (kn, s') w' →
      ∀ Δ, BridgeInv env Us known Γ (gw w) ctx s Δ → known n →
      kn = Γ.constants n ∧ RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w')
    (motive_6 := fun f => ∀ n s ctx cctx ref w r s' w',
      f n s ctx cctx ref w = .ok (r, s') w' →
      ∀ Δ, BridgeInv env Us known Γ (gw w) ctx s Δ → known n →
      RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w' ∧ (s'.constants.get? n).isSome)
    (motive_7 := fun f => ∀ f' args s ctx cctx ref w t s' w',
      f f' args s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ (hd : Expr), BridgeInv env Us known Γ (gw w) ctx s Δ →
      Erases env Us Γ Δ hd f' →
      (∀ i (hi : i < args.size), Supported known Γ (args[i]) ∧
        ∃ ve, TrExprS env Us Δ (args[i]) ve) →
      Erases env Us Γ Δ (args.foldl Expr.app hd) t ∧ RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w')
    (motive_8 := fun f => ∀ e s ctx cctx ref w t s' w',
      f e s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ, BridgeInv env Us known Γ (gw w) ctx s Δ →
      ∀ n ty v b nd, e = .letE n ty v b nd → Supported known Γ e →
      (∃ ve, TrExprS env Us Δ e ve) →
      Erases env Us Γ Δ e t ∧ RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w')
    (motive_9 := fun f => ∀ e s ctx cctx ref w t s' w',
      f e s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ, BridgeInv env Us known Γ (gw w) ctx s Δ →
      ∀ n ty b bi, e = .lam n ty b bi → Supported known Γ e →
      (∃ ve, TrExprS env Us Δ e ve) →
      Erases env Us Γ Δ e t ∧ RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w')
    (motive_10 := fun f => ∀ tn i e s ctx cctx ref w r s' w',
      f tn i e s ctx cctx ref w = .ok (r, s') w' → True)
    (motive_11 := fun f => ∀ e s ctx cctx ref w t s' w',
      f e s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ, BridgeInv env Us known Γ (gw w) ctx s Δ → Supported known Γ e →
      (∃ ve, TrExprS env Us Δ e ve) →
      Erases env Us Γ Δ e t ∧ RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w')
    (motive_12 := fun f => ∀ e s ctx cctx ref w t s' w',
      f e s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ, BridgeInv env Us known Γ (gw w) ctx s Δ → Supported known Γ e →
      (∃ ve, TrExprS env Us Δ e ve) →
      ∀ cn us, e.getAppFn = .const cn us →
      Erases env Us Γ Δ e t ∧ RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w')
    (motive_13 := fun f => ∀ cn ar e s ctx cctx ref w t s' w',
      f cn ar e s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ (us : List Level) (iid : InductiveId) (cidx : Nat),
        BridgeInv env Us known Γ (gw w) ctx s Δ →
        e.getAppFn = .const cn us → Γ.ctors cn = some (iid, cidx) →
        Γ.ctorArities cn = some ar → ar ≤ e.getAppArgs.size →
        cn ≠ ``Nat.zero → cn ≠ ``Nat.succ →
        (∀ i (hi : i < e.getAppArgs.size), Supported known Γ (e.getAppArgs[i]) ∧
          ∃ ve, TrExprS env Us Δ (e.getAppArgs[i]) ve) →
        Erases env Us Γ Δ e t ∧ RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w')
    (motive_14 := fun f => ∀ cn ar ty fe args s ctx cctx ref w t s' w',
      f cn ar ty fe args s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ (us : List Level) (iid : InductiveId) (cidx : Nat),
        BridgeInv env Us known Γ (gw w) ctx s Δ →
        Γ.ctors cn = some (iid, cidx) → Γ.ctorArities cn = some ar → ar ≤ args.size →
        cn ≠ ``Nat.zero → cn ≠ ``Nat.succ →
        (∀ i (hi : i < args.size), Supported known Γ (args[i]) ∧
          ∃ ve, TrExprS env Us Δ (args[i]) ve) →
        Erases env Us Γ Δ (args.foldl Expr.app (.const cn us)) t ∧ RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w')
    (motive_15 := fun f => ∀ ci e s ctx cctx ref w t s' w',
      f ci e s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ (con : Name) (us : List Level) (iid : InductiveId) (np dp : Nat) (nfs : List Nat),
        BridgeInv env Us known Γ (gw w) ctx s Δ →
        e.getAppFn = .const con us →
        Γ.casesOns con = some (iid, np) → Γ.casesDiscrPos con = some dp →
        Γ.ctorFields iid = some nfs →
        CasesInfoAgrees ci con dp nfs →
        con.getPrefix ≠ ``Nat → con.getPrefix ≠ ``Int →
        dp + 1 + nfs.length ≤ e.getAppArgs.size →
        CasesSpineFacts env Us known Γ Δ dp nfs e.getAppArgs →
        Erases env Us Γ Δ e t ∧ RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w')
    (motive_16 := fun f => ∀ ci ty fe args s ctx cctx ref w t s' w',
      f ci ty fe args s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ (con : Name) (us : List Level) (iid : InductiveId) (np dp : Nat) (nfs : List Nat),
        BridgeInv env Us known Γ (gw w) ctx s Δ →
        Γ.casesOns con = some (iid, np) → Γ.casesDiscrPos con = some dp →
        Γ.ctorFields iid = some nfs →
        CasesInfoAgrees ci con dp nfs →
        con.getPrefix ≠ ``Nat → con.getPrefix ≠ ``Int →
        dp + 1 + nfs.length ≤ args.size →
        CasesSpineFacts env Us known Γ Δ dp nfs args →
        Erases env Us Γ Δ (args.foldl Expr.app (.const con us)) t ∧ RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w')
    (motive_17 := fun f => ∀ ci args s ctx cctx ref w t s' w',
      f ci args s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ (con : Name) (us : List Level) (iid : InductiveId) (np dp : Nat) (nfs : List Nat),
        BridgeInv env Us known Γ (gw w) ctx s Δ →
        Γ.casesOns con = some (iid, np) → Γ.casesDiscrPos con = some dp →
        Γ.ctorFields iid = some nfs →
        CasesInfoAgrees ci con dp nfs →
        con.getPrefix ≠ ``Nat → con.getPrefix ≠ ``Int →
        dp + 1 + nfs.length ≤ args.size →
        CasesSpineFacts env Us known Γ Δ dp nfs args →
        Erases env Us Γ Δ (args.foldl Expr.app (.const con us)) t ∧ RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w')
    (motive_18 := fun f => ∀ nf mask e s ctx cctx ref w r s' w',
      f nf mask e s ctx cctx ref w = .ok (r, s') w' →
      ∀ Δ, BridgeInv env Us known Γ (gw w) ctx s Δ →
        mask = Array.replicate nf .keep →
        IsLamTelescope nf e → Supported known Γ e →
        (∃ ve, TrExprS env Us Δ e ve) →
        r.1.length = nf ∧ Erases env Us Γ Δ e (mkLambdas r.1 r.2) ∧
          RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w')
  -- 18 admissibility obligations, one per motive, all from the toolkit.
  · exact eraseM_admissible_ok₁ _
  · exact eraseM_admissible_ok₁ _
  · exact eraseM_admissible_ok₂ _
  · exact eraseM_admissible_ok₁ _
  · exact eraseM_admissible_ok₁ _
  · exact eraseM_admissible_ok₁ _
  · exact eraseM_admissible_ok₂ _
  · exact eraseM_admissible_ok₁ _
  · exact eraseM_admissible_ok₁ _
  · exact eraseM_admissible_ok₃ _
  · exact eraseM_admissible_ok₁ _
  · exact eraseM_admissible_ok₁ _
  · exact eraseM_admissible_ok₃ _
  · exact eraseM_admissible_ok₅ _
  · exact eraseM_admissible_ok₂ _
  · exact eraseM_admissible_ok₄ _
  · exact eraseM_admissible_ok₂ _
  · exact eraseM_admissible_ok₃ _
  -- Step 1: visitExpr — the erasability guard, then dispatch on the fragment.
  · intro vE vLit vLet vLam vProj vApp _ih1 ih2 ih8 ih9 _ih10 ih11
    intro e s ctx cctx ref w t s' w' hrun Δ hinv hsupp hex
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
        obtain ⟨er, hs, hle₂⟩ := ih11 _ _ _ _ _ _ _ _ _ hk Δ (hinv.mono hle₁)
          (.const n us hkn hctor hcases) hex
        exact ⟨er, hs, NameGenerator.LE.trans hle₁ hle₂⟩
      | app hf ha =>
        simp only [] at hk
        obtain ⟨er, hs, hle₂⟩ := ih11 _ _ _ _ _ _ _ _ _ hk Δ (hinv.mono hle₁)
          (.app hf ha) hex
        exact ⟨er, hs, NameGenerator.LE.trans hle₁ hle₂⟩
      | lam n ty bi hb =>
        simp only [] at hk
        obtain ⟨er, hs, hle₂⟩ := ih9 _ _ _ _ _ _ _ _ _ hk Δ (hinv.mono hle₁)
          n ty _ bi rfl (.lam n ty bi hb) hex
        exact ⟨er, hs, NameGenerator.LE.trans hle₁ hle₂⟩
      | letE n ty nd hv hb =>
        simp only [] at hk
        obtain ⟨er, hs, hle₂⟩ := ih8 _ _ _ _ _ _ _ _ _ hk Δ (hinv.mono hle₁)
          n ty _ _ nd rfl (.letE n ty nd hv hb) hex
        exact ⟨er, hs, NameGenerator.LE.trans hle₁ hle₂⟩
      | @natLit n iid hpeano hz hs =>
        -- a peano-`Nat` literal: `visitExpr` hands it to `visitLiteral`, motive 2.
        simp only [] at hk
        obtain ⟨er, hrc, hle₂⟩ := ih2 _ _ _ _ _ _ _ _ _ hk Δ n iid (hinv.mono hle₁)
          rfl hpeano hz hs hex
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
        obtain ⟨er, hs, hle₂⟩ := ih11 _ _ _ _ _ _ _ _ _ hk Δ (hinv.mono hle₁) hsupp' hex
        exact ⟨er, hs, NameGenerator.LE.trans hle₁ hle₂⟩
      | @ctorApp cn us iid cidx ar args hc hcases har hsat hzero hsucc hargs =>
        -- a constructor spine; `visitExpr` dispatches both `.const` (args = [])
        -- and `.app` (args ≠ []) to `visitApp`, then motive 11 handles it.
        have hsupp' : Supported known Γ (args.foldl Expr.app (.const cn us)) :=
          .ctorApp hc hcases har hsat hzero hsucc hargs
        rcases List.eq_nil_or_concat args with rfl | ⟨init, last, rfl⟩
        · simp only [List.foldl_nil] at hk hsupp' hex ⊢
          obtain ⟨er, hs, hle₂⟩ := ih11 _ _ _ _ _ _ _ _ _ hk Δ (hinv.mono hle₁) hsupp' hex
          exact ⟨er, hs, NameGenerator.LE.trans hle₁ hle₂⟩
        · rw [List.concat_eq_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
            at hk hsupp' hex ⊢
          simp only [] at hk
          obtain ⟨er, hs, hle₂⟩ := ih11 _ _ _ _ _ _ _ _ _ hk Δ (hinv.mono hle₁) hsupp' hex
          exact ⟨er, hs, NameGenerator.LE.trans hle₁ hle₂⟩
  -- Step 2: visitLiteral — under peano the literal is rebuilt as the constructor tower,
  -- one `visitConstructor` per `succ`, which is *literally* lean4lean's
  -- `Literal.toConstructor` step; so the case is `Erases.lit` over motive 3, and the
  -- recursion `visitLiteral → visitConstructor → visitAppArgs → visitExpr → visitLiteral`
  -- is carried by the fixpoint induction (no measure on `n` is needed). `BridgeInv.natcfg`
  -- turns the `Γ`-side flag into the reader's config, which selects the branch; the
  -- machine arms are then unreachable and `.strVal` never enters (`Supported` excludes it).
  · intro vCtor ih3
    intro l s ctx cctx ref w r s' w' hrun Δ n iid hinv hl hpeano hz hs hex
    subst hl
    obtain ⟨ve, hve⟩ := hex
    obtain ⟨hcl, htrC⟩ := TrExprS.lit_inv' hve
    have hpe : ctx.config.nat = .peano := hinv.natcfg hpeano
    simp only [] at hrun
    rw [run_read_bind] at hrun
    cases n with
    | zero =>
      simp only [hpe] at hrun
      obtain ⟨er, hrc, hle⟩ := ih3 _ _ _ _ _ _ _ _ _ _ hrun Δ [] iid 0 hinv hz
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
      obtain ⟨er, hrc, hle⟩ := ih3 _ _ _ _ _ _ _ _ _ _ hrun Δ [] iid 1 hinv hs
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
    intro cn args s ctx cctx ref w t s' w' hrun Δ us iid cidx hinv hct hnatdead hargfacts
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
    have hrc3 : RunConclδ env Us Γ Esrc _ _ :=
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
    obtain ⟨erap, hs', hle⟩ := ih7 _ _ _ _ _ _ _ _ _ _ hrun2 Δ (Expr.const cn us)
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
    intro e s ctx cctx ref w t s' w' hrun Δ hinv n us he hkn hctor hcases
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
      obtain ⟨hknE, hs, hle⟩ := ih5 _ _ _ _ _ _ _ _ _ hgck Δ hinv hkn'
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
    intro n s ctx cctx ref w kn s' w' hrun Δ hinv hkn
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
      obtain ⟨hrc, hle, hdom⟩ := ih6 _ _ _ _ _ _ _ _ _ hvm Δ hinv hkn
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
    intro n s ctx cctx ref w u s₁ w₁ hrun Δ hinv hkn
    simp only [] at hrun
    -- (1) the declaration fetch. State-transparent; `DeltaHyps.decl_run` pins what it
    -- returns, and every branch below is a function of that.
    rw [run_bind_ok] at hrun
    obtain ⟨di, sa, wa, hdi, hrun⟩ := hrun
    have hsa := run_liftCoreM_state (x := (Compiler.LCNF.getDeclInfo? n : CoreM _))
      _ _ cctx ref _ hdi
    subst sa
    have hdiC := ((run_liftCoreM_ok _ _ cctx ref _).mp hdi).1
    obtain ⟨hled, ci, hci, hall, hlp, hvalue⟩ := (Hδ cctx ref).decl_run hkn hdiC
    have hdg : di.get! = ci := by rw [hci]; rfl
    rw [hdg] at hrun
    -- (2) getEnv, for the `@[inline]` attribute lookup.
    rw [run_bind_ok] at hrun
    obtain ⟨env0, sb, wb, henv0, hrun⟩ := hrun
    have hsb := run_getEnv_state _ _ cctx ref _ henv0
    subst sb
    have hle : gw w ≤ gw wb :=
      NameGenerator.LE.trans hled ((Hδ cctx ref).env_run henv0)
    have hrc : RunConclδ env Us Γ Esrc s s := RunConclδ.rfl' _
    clear hdi henv0
    -- (3) the block is a single declaration (`decl_run`), so the prefix is entered.
    split at hrun
    case isFalse hns => exact absurd (by simp [hall]) hns
    case isTrue =>
      -- (4) the `@[inline]` prefix: `inlinings` only, and one `logInfo` world step.
      obtain ⟨s₀, w₀, u₀, hpre, hrun⟩ := run_inline_prefix_decomp' hrun
      obtain ⟨hrc, hle⟩ : RunConclδ env Us Γ Esrc s s₀ ∧ gw w ≤ gw w₀ := by
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
      have hkey : ∀ v : Expr, ci.value? (allowOpaque := true) = some v →
          ci.value! (allowOpaque := true) = v ∧ name_occurs n v = false :=
        fun v hv => ⟨constantInfo_value!_of_value? hv, hvalue v hv⟩
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
             case isFalse hnr =>
               -- (6c) the recursive exit is out of the fragment: `decl_run` says the
               -- value does not mention `n`, which forces `nonrecursive` true.
               exact absurd (by
                 simp [hall, (hkey _ hval).1, (hkey _ hval).2]) hnr
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
               rw [(hkey _ hval).1] at hpr
               have hlink : Esrc n = some pe :=
                 (Hδ cctx ref).prep_esrc hkn hdiC hci hval hpr
               obtain ⟨hsupp, htr⟩ := (Hδ cctx ref).prepared hkn hlink hpr
               -- the invariant travels to the dependency's reader: `withReader` moves
               -- `fixvars` (to `none`, which `DeltaHyps.nofixvars` matches) and
               -- `lparams` (to the declaration's own, which `decl_run` pins at `Us`).
               have hinvb := (hinv.mono_state hrc.rc).mono hle
               have hinv' : BridgeInv env Us known Γ (gw wp)
                   { ctx with fixvars := none, lparams := ci.levelParams } s₀ Δ :=
                 { mlc := hinvb.mlc
                   lparams := hlp
                   natcfg := hinvb.natcfg
                   kfresh := hinvb.kfresh
                   fixvars := by
                     intro nm x
                     show (none : Option (Std.HashMap Name FVarId)).bind _ = _ ↔ _
                     rw [(Hδ cctx ref).nofixvars]
                     simp
                   fixfresh := by
                     intro nm x hx
                     rw [(Hδ cctx ref).nofixvars] at hx
                     simp at hx
                   reserved := hinvb.reserved
                   knames := hinvb.knames
                   consts := hinvb.consts }
               obtain ⟨herv, hrcv, hlev⟩ := ih1 _ _ _ _ _ _ _ _ _ hvis Δ hinv' hsupp (htr Δ)
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
                 (P := fun s' w' => RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w' ∧
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
                 ⟨hrc.trans (RunConclδ.nonrec (hinv.knames n)
                     (fun {m} hm hkey' => (Hδ cctx ref).kinj
                       ((Hδ cctx ref).esrc_sub hm) hkn hkey')
                     (fun {body} hb => ⟨Δ, by
                       obtain rfl : body = pe := by
                         rw [hlink] at hb; exact (Option.some.inj hb).symm
                       exact herv⟩)),
                   hle, nonrecConstState_get? n t _⟩
                 hrun)
  -- Step 7: visitAppArgs — the Array.foldlM loop rule with the prefix-spine
  -- invariant.
  · intro vE ih1
    intro f' args s ctx cctx ref w t s' w' hrun Δ hd hinv herf hargs
    simp only [] at hrun
    have hmem : ∀ a ∈ args.toList, Supported known Γ a ∧ ∃ ve, TrExprS env Us Δ a ve := by
      intro a ha
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
      have hi' : i < args.size := by simpa using hi
      have := hargs i hi'
      simpa using this
    have hP := run_array_foldlM_ok ctx cctx ref
      (P := fun pre acc s₁ w₁ =>
        Erases env Us Γ Δ (pre.foldl Expr.app hd) acc ∧ RunConclδ env Us Γ Esrc s s₁ ∧ gw w ≤ gw w₁)
      ⟨herf, RunConclδ.rfl' _, NameGenerator.LE.rfl⟩
      (fun pre x post acc s₁ w₁ acc' s₂ w₂ hLpre hPacc hg => by
        rw [run_bind_ok] at hg
        obtain ⟨tx, s₃, w₃, hvx, hp⟩ := hg
        rw [run_pure] at hp
        cases hp
        obtain ⟨hErpre, hrc, hle⟩ := hPacc
        obtain ⟨hsx, hex⟩ := hmem x (by rw [hLpre]; exact List.mem_append_right _ List.mem_cons_self)
        obtain ⟨erx, hs₃, hle₂⟩ := ih1 _ _ _ _ _ _ _ _ _ hvx Δ
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
    intro e s ctx cctx ref w t s' w' hrun Δ hinv n ty v b nd he hsupp hex
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
    obtain ⟨erv, hs₂, hle₂⟩ := ih1 _ _ _ _ _ _ _ _ _ hvv _ hinv' hv ⟨_, hvext⟩
    -- the opened body, in the extended context
    rw [Lean.Expr.instantiate1_eq] at hvb
    have hbext := TrExprS.inst_fvar henv hΔ'.wf hbody
    obtain ⟨erb, hs₃, hle₃⟩ := ih1 _ _ _ _ _ _ _ _ _ hvb _
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
    intro e s ctx cctx ref w t s' w' hrun Δ hinv n ty b bi he hsupp hex
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
    obtain ⟨erb, hs₂, hle₂⟩ := ih1 _ _ _ _ _ _ _ _ _ hvb _ hinv'
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
  -- Step 10: visitProj (trivial conclusion).
  · intros; trivial
  -- Step 11: visitApp — dispatch on the head: const heads to visitConstApp,
  -- other heads through visitExpr + visitAppArgs and the spine reconstruction.
  · intro vE vAA vCA ih1 ih7 ih12
    intro e s ctx cctx ref w t s' w' hrun Δ hinv hsupp hex
    simp only [] at hrun
    cases hfn : e.getAppFn
    case const cn us =>
      rw [hfn] at hrun
      simp only [] at hrun
      exact ih12 _ _ _ _ _ _ _ _ _ hrun Δ hinv hsupp hex cn us hfn
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
      obtain ⟨erf, hs₁, hle₁⟩ := ih1 _ _ _ _ _ _ _ _ _ hvf Δ hinv hsuppfn ⟨fve, htrfn⟩
      obtain ⟨erapp, hs', hle₂⟩ := ih7 _ _ _ _ _ _ _ _ _ _ hk Δ e.getAppFn
        ((hinv.mono_state hs₁.rc).mono hle₁) erf hargfacts
      rw [getAppArgs_spine'] at erapp
      exact ⟨erapp, hs₁.trans hs', NameGenerator.LE.trans hle₁ hle₂⟩)
  -- Step 12: visitConstApp — a three-way split on the head's `Γ` classification
  -- (`casesOns` first, because `getCasesInfo?` is consulted before `getCtorArity?`):
  -- the ι path goes to motive 15, the constructor path to motive 13, and the plain
  -- path to motive 4 for the head + motive 7 for the spine.
  · intro vC vAA vCtE vCsE ih4 ih7 ih13 ih15
    intro e s ctx cctx ref w t s' w' hrun Δ hinv hsupp hex cn us hfn
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
      obtain ⟨erap, hs', hle₂⟩ := ih15 _ _ _ _ _ _ _ _ _ _ hk Δ cn us iid np dp nfs
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
      obtain ⟨erap, hs', hle₃⟩ := ih13 _ _ _ _ _ _ _ _ _ _ _ hk Δ us iid cidx
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
        obtain ⟨erc, hs₃, hle₃⟩ := ih4 _ _ _ _ _ _ _ _ _ hvc Δ
          (hinv.mono (NameGenerator.LE.trans hle₁ hle₂)) cn us rfl hkn hctor hcases
        have erfn : Erases env Us Γ Δ e.getAppFn tc := by rw [hfn]; exact erc
        obtain ⟨erapp, hs', hle₄⟩ := ih7 _ _ _ _ _ _ _ _ _ _ hk Δ e.getAppFn
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
    intro cn ar e s ctx cctx ref w t s' w' hrun Δ us iid cidx hinv hfn hct har hle
      hzero hsucc hargfacts
    simp only [] at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨type, s₁, w₁, hinfer, hk⟩ := hrun
    have hs₁ : s₁ = s := run_liftMetaM_state _ _ _ _ _ hinfer
    have hlem := HD.infer_run e s ctx cctx ref w type s₁ w₁ hinfer
    subst hs₁
    rw [expr_withApp_eq] at hk
    obtain ⟨erap, hs', hle₂⟩ := ih14 _ _ _ _ _ _ _ _ _ _ _ _ _ hk Δ us iid cidx
      (hinv.mono hlem) hct har hle hzero hsucc hargfacts
    have hspine : e.getAppArgs.foldl Expr.app (.const cn us) = e := by
      rw [← hfn]; exact getAppArgs_spine' e
    rw [hspine] at erap
    exact ⟨erap, hs', NameGenerator.LE.trans hlem hle₂⟩
  -- Step 14: visitCtorEtaGo — saturated (`ar ≤ args.size`), so it goes straight
  -- to `visitConstructor` (motive 3); the η-expansion branch is dead.
  · intro vConstructor vCtorEtaGo ih3 _ih14
    intro cn ar ty fe args s ctx cctx ref w t s' w' hrun Δ us iid cidx hinv hct har hle
      hzero hsucc hargfacts
    simp only [] at hrun
    rw [if_pos hle] at hrun
    exact ih3 _ _ _ _ _ _ _ _ _ _ hrun Δ us iid cidx hinv hct (.inr ⟨hzero, hsucc⟩) hargfacts
  -- Step 15: visitCasesEta — `inferType` (state-preserving, monotone; the type is
  -- discarded on the saturated path), then the `withApp`-decomposed spine goes to
  -- `visitCasesEtaGo`. Mirrors step 13.
  · intro vCasesEtaGo ih16
    intro ci e s ctx cctx ref w t s' w' hrun Δ con us iid np dp nfs hinv hfn hcs hdp hnfs
      hagree hnat hint hle hfacts
    simp only [] at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨type, s₁, w₁, hinfer, hk⟩ := hrun
    have hs₁ : s₁ = s := run_liftMetaM_state _ _ _ _ _ hinfer
    have hlem := HD.infer_run e s ctx cctx ref w type s₁ w₁ hinfer
    subst hs₁
    rw [expr_withApp_eq] at hk
    obtain ⟨erap, hs', hle₂⟩ := ih16 _ _ _ _ _ _ _ _ _ _ _ _ hk Δ con us iid np dp nfs
      (hinv.mono hlem) hcs hdp hnfs hagree hnat hint hle hfacts
    have hspine : e.getAppArgs.foldl Expr.app (.const con us) = e := by
      rw [← hfn]; exact getAppArgs_spine' e
    rw [hspine] at erap
    exact ⟨erap, hs', NameGenerator.LE.trans hlem hle₂⟩
  -- Step 16: visitCasesEtaGo — saturated (`ci.arity ≤ args.size`, by
  -- `CasesInfoAgrees.arity`), so it goes straight to `visitCases` (motive 17); the
  -- η-expansion branch is dead. Mirrors step 14.
  · intro vCasesEtaGo vCases _ih16 ih17
    intro ci ty fe args s ctx cctx ref w t s' w' hrun Δ con us iid np dp nfs hinv hcs hdp
      hnfs hagree hnat hint hle hfacts
    simp only [] at hrun
    rw [if_pos (show ci.arity ≤ args.size by rw [hagree.arity]; exact hle)] at hrun
    exact ih17 _ _ _ _ _ _ _ _ _ _ hrun Δ con us iid np dp nfs hinv hcs hdp hnfs
      hagree hnat hint hle hfacts
  -- Step 17: visitCases — the workhorse.
  · intro vE vAlt ih1 ih18
    intro ci args s ctx cctx ref w t s' w' hrun Δ con us iid np dp nfs hinv hcs hdp hnfs
      hagree hnat hint hle hfacts
    obtain ⟨hfd, hfm, hfx⟩ := hfacts
    have hdplt : dp < args.size := by omega
    simp only [] at hrun
    -- (1) the discriminant
    rw [show args[ci.discrPos]! = args[dp]'hdplt from by
      rw [hagree.discrPos]; exact getElem!_pos args dp hdplt] at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨discr_nt, s₁, w₁, hdisc, hrun⟩ := hrun
    obtain ⟨hsd, hexd⟩ := hfd hdplt
    obtain ⟨erd, hrc₁, hle₁⟩ := ih1 _ _ _ _ _ _ _ _ _ hdisc Δ hinv hsd hexd
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
    have hrc₅ : RunConclδ env Us Γ Esrc _ _ :=
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
        RunConclδ env Us Γ Esrc s₅ s₇ ∧ gw w ≤ gw w₇ ∧ acc.1.size = pre.length ∧
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
              ih18 (nfs[pre.length]'hLlen) y _ _ ctx cctx ref w₇ alt s₉ w₉ halt Δ
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
      (P := fun pre acc s₁₀ w₁₀ => RunConclδ env Us Γ Esrc s₃ s₁₀ ∧ gw w ≤ gw w₁₀ ∧
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
        obtain ⟨erx, hrcX, hle₁₂⟩ := ih1 _ _ _ _ _ _ _ _ _ hvx Δ
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
    intro nf mask e s ctx cctx ref w r s' w' hrun Δ hinv hmask hlam hsupp hex
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
    obtain ⟨erb, hs₂, hle₃⟩ := ih1 _ _ _ _ _ _ _ _ _ hvb Δ' hinv' hsupp' hex'
    rw [run_mkAlt] at hm
    cases hm
    exact ⟨by simp [hlen], hclose tb erb, hs₂,
      NameGenerator.LE.trans hlem (NameGenerator.LE.trans hle₂ hle₃)⟩

/-! ## The exported theorem -/

/-- **The bridge theorem**: on the supported fragment, under the trust bundles
`BridgeHyps`/`DataBridgeHyps`/`CasesBridgeHyps` and the invariant `BridgeInv`,
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
    {known : Name → Prop} {Γ : ErasureCtx} {Esrc : SEnv}
    {gw : Void IO.RealWorld → NameGenerator}
    (H : BridgeHyps env Us Γ gw) (HD : DataBridgeHyps Γ gw) (C : CasesBridgeHyps Γ gw)
    (Hδ : ∀ (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State),
      DeltaHyps env Us known Γ Esrc gw cctx ref)
    (henv : env.Ordered) :
    ∀ e s ctx cctx ref w t s' w',
      Erasure.visitExpr e s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ, BridgeInv env Us known Γ (gw w) ctx s Δ →
        Supported known Γ e → (∃ ve, TrExprS env Us Δ e ve) →
        Erases env Us Γ Δ e t ∧ RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w' :=
  (visitExpr_refines_erases_core H HD C Hδ henv).1

/-! ## Non-vacuity guards

The `BridgeHyps`/`DataBridgeHyps`/`CasesBridgeHyps` fields quantify over opaque
runtime primitives, so their global satisfiability is not in-logic decidable —
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
    BridgeInv env Us (fun _ => False) Γ gen ⟨{}, none, Us, cfg⟩ {} [] where
  mlc := ⟨.nil, trivial, rfl, rfl⟩
  lparams := rfl
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
    BridgeInv env Us (fun _ => False) (ΓfixOpen x) gen
      ⟨{}, some ((∅ : Std.HashMap Name FVarId).insert `f x), Us, cfg⟩ {} [] where
  mlc := ⟨.nil, trivial, rfl, rfl⟩
  lparams := rfl
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

/-- (ii) The non-run premises of `visitExpr_refines_erases` are jointly
instantiable: a concrete one-fvar context (with `TrLCtx` *constructed*, not
assumed) and the supported term `.fvar x` satisfy every premise except the run
itself and the trust bundles, which stay hypothetical because the primitives
are opaque. The fourth bundle (`DeltaHyps`, slice D4a) is hypothetical for exactly the
same reason and no other: at this guard's `known = ⊥` its whole *scope* half is free
(`DeltaHyps.of_bot`), and what is left is the generator bookkeeping for the five
primitives only `visitMutual` reaches. -/
example (env : VEnv) (Us : List Name) (Γ : ErasureCtx) (cfg : ErasureConfig)
    (hkn : ∀ n : Name, Γ.constants n = toKername n) (hfv : Γ.fixvars = fun _ => none)
    (hcfg : Γ.natPeano = true → cfg.nat = .peano)
    (gw : Void IO.RealWorld → NameGenerator)
    (H : BridgeHyps env Us Γ gw) (HD : DataBridgeHyps Γ gw) (C : CasesBridgeHyps Γ gw)
    (Hδ : ∀ (cc : Core.Context) (rf : ST.Ref IO.RealWorld Core.State),
      DeltaHyps env Us (fun _ => False) Γ (fun _ => none) gw cc rf)
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
  have hinv : BridgeInv env Us (fun _ => False) Γ (gw w)
      ⟨({} : LocalContext).mkLocalDecl x nm (.sort .zero) bi, none, Us, cfg⟩ {}
      [(some (x, (Expr.sort .zero).fvarsList), .vlam (.sort .zero))] :=
    { mlc := ⟨(MLCtx.nil).vlam x nm (.sort .zero) (.sort .zero) bi,
        ⟨trivial, hfind, hty, hty'⟩, rfl, rfl⟩
      lparams := rfl
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
  exact visitExpr_refines_erases H HD C Hδ henv _ _ _ _ _ _ _ _ _ hrun _ hinv (.fvar x) hex


/-- (iii) **The bridge fires on a `Nat` literal** (Nat-literals wall, L4) — the literal
analogue of (ii), and the joint non-vacuity of everything L3 added. *Constructed* here:
the peano config; the context `ΓnatLit` (the same fixture at which `Erases.lean` derives
the tower and `ErasesCorrectData.lean` runs it on both sides); the `BridgeInv`, whose new
`natcfg` field is exactly the config pin and is discharged from `hcfg`; the
`Supported.natLit` derivation; and — the premise that made this guard worth building —
the source translation `∃ ve, TrExprS envNatT [] [] (.lit (.natVal 2)) ve`, at the
three-axiom `envNatT` in which `Nat`'s constructors are declared *and typed*
(`trExprS_natLit`, `Erases.lean`). *Hypothetical*, as in (ii) and for the same reason:
the run equation and the three trust bundles, which speak about opaque primitives.

So the shipping eraser, run on the raw literal node `2` in peano mode, lands inside
`Erases` — and by `Erases.lit_inv` only the box rule or `Erases.lit` can have put it
there. -/
example (cfg : ErasureConfig) (hcfg : cfg.nat = .peano)
    (gw : Void IO.RealWorld → NameGenerator)
    (H : BridgeHyps envNatT [] ΓnatLit gw) (HD : DataBridgeHyps ΓnatLit gw)
    (C : CasesBridgeHyps ΓnatLit gw)
    (Hδ : ∀ (cc : Core.Context) (rf : ST.Ref IO.RealWorld Core.State),
      DeltaHyps envNatT [] (fun _ => False) ΓnatLit (fun _ => none) gw cc rf)
    (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)
    (w w' : Void IO.RealWorld) (t : LBTerm) (s' : ErasureState)
    (hrun : Erasure.visitExpr (.lit (.natVal 2)) {} ⟨{}, none, [], cfg⟩ cctx ref w
      = .ok (t, s') w') :
    Erases envNatT [] ΓnatLit [] (.lit (.natVal 2)) t ∧
      RunConclδ envNatT [] ΓnatLit (fun _ => none) ({} : ErasureState) s' ∧
      gw w ≤ gw w' := by
  have hinv : BridgeInv envNatT [] (fun _ => False) ΓnatLit (gw w)
      ⟨{}, none, [], cfg⟩ {} [] :=
    { mlc := ⟨.nil, trivial, rfl, rfl⟩
      lparams := rfl
      natcfg := fun _ => hcfg
      kfresh := fun _ h => nomatch h
      fixvars := by intro nm x; simp [ΓnatLit]
      fixfresh := by intro nm x hx; simp [ΓnatLit] at hx
      reserved := fun _ h => nomatch h
      knames := fun _ => rfl
      consts := by intro n k hk; simp at hk }
  exact visitExpr_refines_erases H HD C Hδ envNatT_wf.ordered _ _ _ _ _ _ _ _ _ hrun _ hinv
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
jointly satisfiable at the cold-start entry. That is δ-inclusion, at the invariant. -/
theorem bridgeInv_cold_known (env : VEnv) (Us : List Name) (Γ : ErasureCtx)
    (hkn : ∀ m : Name, Γ.constants m = toKername m) (hfv : Γ.fixvars = fun _ => none)
    (gen : NameGenerator) (cfg : ErasureConfig)
    (hcfg : Γ.natPeano = true → cfg.nat = .peano) (n : Name) :
    BridgeInv env Us (fun m => m = n) Γ gen ⟨{}, none, Us, cfg⟩ {} [] where
  mlc := ⟨.nil, trivial, rfl, rfl⟩
  lparams := rfl
  natcfg := hcfg
  kfresh := fun _ hfv => nomatch hfv
  fixvars := by intro nm x; rw [hfv]; simp
  fixfresh := by intro nm x hx; rw [hfv] at hx; simp at hx
  reserved := fun _ hfv => nomatch hfv
  knames := hkn
  consts := by intro m k hk; simp at hk

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

Everything except the run and the four trust bundles is *constructed*, at a genuinely
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
    (C : CasesBridgeHyps gΓδ gw)
    (Hδ : ∀ (cc : Core.Context) (rf : ST.Ref IO.RealWorld Core.State),
      DeltaHyps envNatT [] (fun m => m = ``Nat.zero) gΓδ (fun _ => none) gw cc rf)
    (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)
    (w w' : Void IO.RealWorld) (t : LBTerm) (s' : ErasureState)
    (hrun : Erasure.visitExpr (.const ``Nat.zero []) {} ⟨{}, none, [], cfg⟩ cctx ref w
      = .ok (t, s') w') :
    Erases envNatT [] gΓδ [] (.const ``Nat.zero []) t ∧
      RunConclδ envNatT [] gΓδ (fun _ => none) ({} : ErasureState) s' ∧
      gw w ≤ gw w' :=
  visitExpr_refines_erases H HD C Hδ envNatT_wf.ordered _ _ _ _ _ _ _ _ _ hrun _
    (bridgeInv_cold_known envNatT [] gΓδ (fun _ => rfl) rfl (gw w) cfg
      (fun h => absurd h (by decide)) ``Nat.zero)
    (.const ``Nat.zero [] (Or.inl rfl) rfl rfl)
    ⟨.const ``Nat.zero [], .const envNatT_zero (by simp) (by simp)⟩

end NonVacuity

/- Axiom audit (2026-07-07, via temporary `#print axioms`, since removed;
re-checked 2026-08-10 after the ι widening, 2026-08-12 after the cold-start S2
widening and again after the Nat-literals L3 widening — **unchanged** every time.
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
* `visitExpr_refines_erases` / `visitExpr_refines_erases_core`:
  `[propext, sorryAx, Classical.choice, Quot.sound, Expr.instantiate1_eq,
    PersistentArray.toList'_push, PersistentHashMap.WF.find?_eq,
    PersistentHashMap.WF.toList'_insert]`
* pure helpers (`VLCtx.find?_bvar_none_of_noBV`, `Supported.getAppFn`,
  `supported_foldl_app_inv`, `getAppArgs_spine`, `run_fvar_to_name`):
  `[propext, Classical.choice, Quot.sound]` or less;
* `spine_arg_facts`, `BridgeInv.mono`: `[propext, sorryAx, Classical.choice,
  Quot.sound]`; `BridgeInv.mkLocalDecl`/`mkLetDecl` additionally carry the
  three `PersistentArray`/`PersistentHashMap` modeling axioms.
The `sorryAx` is inherited from lean4lean (`TrProj` is a sorried definition,
so it enters through the very *type* of `TrExprS`-adjacent statements — see
the header of Erases.lean); `Expr.instantiate1_eq` and the
`PersistentArray`/`PersistentHashMap` axioms are lean4lean's modeling axioms
for the untrusted-representation surface (entering via Bridge.lean's `find?`
lemmas and the `instantiate1 → instantiate1'` transport). No `sorry` of our
own, no new axioms, no `native_decide`. -/

end LeanToLambdaBox
