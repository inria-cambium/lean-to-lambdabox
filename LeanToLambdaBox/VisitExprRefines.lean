import LeanToLambdaBox.ErasureRun
import LeanToLambdaBox.Bridge
import LeanToLambdaBox.EraseCore
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

* **`BridgeHyps`** — the trust bundle: Hoare-style hypotheses about the four
  opaque runtime primitives the bridge cannot compute with
  (`liftMetaM (isErasable e)`, `mkFreshFVarId`, `getCasesInfo?`,
  `getCtorArity?`), phrased against a ghost world-measure
  `gw : Void IO.RealWorld → NameGenerator` (the name-generator state as a
  function of the `EST` world token). These play the role `OracleSound`
  played for `eraseCore`: they are the bridge's honest assumptions, and their
  global satisfiability is *not* in-logic decidable — the primitives are
  opaque `ST`/`EIO` operations. This is the documented trust boundary.
* **`BridgeInv`** — the induction invariant: the reader's `LocalContext`
  corresponds to the typing context `Δ` (lean4lean's `TrLCtx`), no
  `fixvars` map is installed, every fvar of `Δ` is reserved by the current
  generator, and every `known` constant is pre-registered in the state with
  its `Γ`-kername.
* **`visitExpr_refines_erases`** — the final export (motive 1 of the
  18-motive induction `visitExpr_refines_erases_core`).

Trust boundary: results inherit `sorryAx` through lean4lean's `TrExprS`
structural lemmas exactly as documented in `Erases.lean`, plus lean4lean's
`Expr`/`PersistentHashMap` modeling axioms (through `Bridge.lean`'s `find?`
lemmas and `instantiate1_eq`). No `sorry` of our own, no new axioms.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure

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

/-- The head of an application spine of a supported term is supported. -/
theorem Supported.getAppFn {known : Name → Prop} {Γ : ErasureCtx} {e : Expr}
    (h : Supported known Γ e) : Supported known Γ e.getAppFn := by
  induction h with
  | bvar i => exact .bvar i
  | fvar x => exact .fvar x
  | const n us hk h1 h2 => exact .const n us hk h1 h2
  | app _ _ ihf _ => exact ihf
  | lam n ty bi hb _ => exact .lam n ty bi hb
  | letE n ty nd hv hb _ _ => exact .letE n ty nd hv hb

/-- Inversion of `Supported` along an application spine built by
`List.foldl Expr.app` (mirror of `closed_foldl_app`, ErasesAbstract.lean). -/
theorem supported_foldl_app_inv {known : Name → Prop} {Γ : ErasureCtx} :
    ∀ {args : List Expr} {f : Expr}, Supported known Γ (args.foldl Expr.app f) →
      Supported known Γ f ∧ ∀ a ∈ args, Supported known Γ a := by
  intro args
  induction args with
  | nil => exact fun h => ⟨h, by simp⟩
  | cons a as ih =>
    intro f h
    simp only [List.foldl_cons] at h
    obtain ⟨hfa, hrest⟩ := ih h
    cases hfa with
    | app hf ha =>
      refine ⟨hf, fun b hb => ?_⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ha
      · exact hrest _ hb

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

/-- Package the per-argument obligations of the `visitAppArgs` motive (plus the
head facts) from whole-term `Supported`/`TrExprS` facts, through the spine
reconstruction. -/
theorem spine_arg_facts {env : VEnv} {Us : List Name} {known : Name → Prop}
    {Γ : ErasureCtx} {Δ : VLCtx} {e : Expr}
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
  obtain ⟨hsuppfn, hsuppargs⟩ := supported_foldl_app_inv hsuppS
  refine ⟨⟨hsuppfn, fve, htrfn⟩, fun i hi => ?_⟩
  have hi' : i < e.getAppArgs.toList.length := by simpa using hi
  constructor
  · have := hsuppargs _ (List.getElem_mem hi')
    simpa using this
  · obtain ⟨ave, hav⟩ := hargtr i hi'
    exact ⟨ave, by simpa using hav⟩

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

/-! ## The trust bundle and the induction invariant -/

/-- Trust bundle: Hoare-style hypotheses about the opaque runtime primitives,
relative to a ghost world-measure `gw` (the name-generator state as a function
of the world token). These are the bridge's honest assumptions, playing the
role `OracleSound` played for `eraseCore`:

* `orc_run`: a successful run of the erasability oracle advances the generator
  monotonically, and a `true` verdict is *sound* — the term is `Erasable` in
  any typing context corresponding to the local context the oracle ran in.
  (State-preservation is not assumed: it is derivable via
  `run_liftMetaM_state`.)
* `fresh_run`: `mkFreshFVarId` preserves the `ErasureState`, returns a
  previously-unreserved id, reserves it, and advances the generator.
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
    Erasure.liftMetaM (Erasure.isErasable e) s ctx cctx ref w = .ok (b, s₁) w₁ →
    gw w ≤ gw w₁ ∧
    (b = true → ∀ (Δ : VLCtx) (ve : VExpr), TrLCtx env Us ctx.lctx Δ →
      TrExprS env Us Δ e ve → Erasable env Us.length Δ.toCtx ve)
  fresh_run : ∀ (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (x : FVarId)
    (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    (mkFreshFVarId : EraseM FVarId) s ctx cctx ref w = .ok (x, s₁) w₁ →
    s₁ = s ∧ ¬ (gw w).Reserves x ∧ (gw w₁).Reserves x ∧ gw w ≤ gw w₁
  cases_run : ∀ (n : Name) (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) (r : Option CasesInfo) (w₁ : Void IO.RealWorld),
    getCasesInfo? n cctx ref w = .ok r w₁ →
    gw w ≤ gw w₁ ∧ (Γ.casesOns n = none → r = none)
  ctor_run : ∀ (n : Name) (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) (r : Option Nat) (w₁ : Void IO.RealWorld),
    Lean.Compiler.LCNF.getCtorArity? n cctx ref w = .ok r w₁ →
    gw w ≤ gw w₁ ∧ (Γ.ctors n = none → r = none)

/-- The bridge invariant carried through the induction. -/
structure BridgeInv (env : VEnv) (Us : List Name) (known : Name → Prop)
    (Γ : ErasureCtx) (gen : NameGenerator)
    (ctx : Erasure.ErasureContext) (s : Erasure.ErasureState) (Δ : VLCtx) : Prop where
  trlctx : TrLCtx env Us ctx.lctx Δ
  fixvars : ctx.fixvars = none
  reserved : ∀ fv ∈ Δ.fvars, gen.Reserves fv
  consts : ∀ n, known n → s.constants.get? n = some (Γ.constants n)

/-- The invariant is monotone in the generator (fvar reservations survive
generator advancement). -/
theorem BridgeInv.mono {env : VEnv} {Us : List Name} {known : Name → Prop}
    {Γ : ErasureCtx} {gen gen' : NameGenerator} {ctx : ErasureContext}
    {s : ErasureState} {Δ : VLCtx}
    (h : BridgeInv env Us known Γ gen ctx s Δ) (hle : gen ≤ gen') :
    BridgeInv env Us known Γ gen' ctx s Δ where
  trlctx := h.trlctx
  fixvars := h.fixvars
  reserved := fun fv hfv => (h.reserved fv hfv).mono hle
  consts := h.consts

/-- Extend the invariant across `Erasure.withLocalDecl`'s context extension
(the `visitLambda` case). -/
theorem BridgeInv.mkLocalDecl {env : VEnv} {Us : List Name} {known : Name → Prop}
    {Γ : ErasureCtx} {gen gen' : NameGenerator} {ctx : ErasureContext}
    {s : ErasureState} {Δ : VLCtx} {x : FVarId} {n : Name} {ty : Expr} {ty' : VExpr}
    {bi : BinderInfo}
    (hinv : BridgeInv env Us known Γ gen ctx s Δ)
    (hty : TrExprS env Us Δ ty ty') (hty' : env.IsType Us.length Δ.toCtx ty')
    (hx : x ∉ Δ.fvars) (hle : gen ≤ gen') (hres : gen'.Reserves x) :
    BridgeInv env Us known Γ gen'
      { ctx with lctx := ctx.lctx.mkLocalDecl x n ty bi } s
      ((some (x, ty.fvarsList), .vlam ty') :: Δ) where
  trlctx := LeanToLambdaBox.TrLCtx.mkLocalDecl hinv.trlctx
    (hinv.trlctx.find?_eq_none.mpr hx) hty hty'
  fixvars := hinv.fixvars
  reserved := by
    intro fv hfv
    have : fv = x ∨ fv ∈ Δ.fvars := by simpa using hfv
    rcases this with rfl | hfv'
    · exact hres
    · exact (hinv.reserved fv hfv').mono hle
  consts := hinv.consts

/-- Extend the invariant across `Erasure.withLocalDef`'s context extension
(the `visitLet` case). -/
theorem BridgeInv.mkLetDecl {env : VEnv} {Us : List Name} {known : Name → Prop}
    {Γ : ErasureCtx} {gen gen' : NameGenerator} {ctx : ErasureContext}
    {s : ErasureState} {Δ : VLCtx} {x : FVarId} {n : Name} {ty v : Expr}
    {ty' val' : VExpr} {nd : Bool}
    (hinv : BridgeInv env Us known Γ gen ctx s Δ)
    (hty : TrExprS env Us Δ ty ty') (hval : TrExprS env Us Δ v val')
    (hvt : env.HasType Us.length Δ.toCtx val' ty')
    (hx : x ∉ Δ.fvars) (hle : gen ≤ gen') (hres : gen'.Reserves x) :
    BridgeInv env Us known Γ gen'
      { ctx with lctx := ctx.lctx.mkLetDecl x n ty v nd } s
      ((some (x, ty.fvarsList ++ v.fvarsList), .vlet ty' val') :: Δ) where
  trlctx := LeanToLambdaBox.TrLCtx.mkLetDecl hinv.trlctx
    (hinv.trlctx.find?_eq_none.mpr hx) hty hval hvt
  fixvars := hinv.fixvars
  reserved := by
    intro fv hfv
    have : fv = x ∨ fv ∈ Δ.fvars := by simpa using hfv
    rcases this with rfl | hfv'
    · exact hres
    · exact (hinv.reserved fv hfv').mono hle
  consts := hinv.consts

/-! ## The main induction -/

set_option maxHeartbeats 1000000 in
/-- **The bridge, all 18 motives.** Content motives: 1 (`visitExpr`),
4 (`visitConst`), 5 (`get_constant_kername`), 7 (`visitAppArgs`),
8 (`visitLet`), 9 (`visitLambda`), 11 (`visitApp`), 12 (`visitConstApp`);
the other ten carry `True` conclusions in canonical run-ok shape (their
branches are unreachable from the supported fragment). -/
theorem visitExpr_refines_erases_core {env : VEnv} {Us : List Name}
    {known : Name → Prop} {Γ : ErasureCtx} {gw : Void IO.RealWorld → NameGenerator}
    (H : BridgeHyps env Us Γ gw) (henv : env.Ordered) :
    (∀ e s ctx cctx ref w t s' w', visitExpr e s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ, BridgeInv env Us known Γ (gw w) ctx s Δ → Supported known Γ e →
      (∃ ve, TrExprS env Us Δ e ve) →
      Erases env Us Γ Δ e t ∧ s' = s ∧ gw w ≤ gw w') ∧
    (∀ l s ctx cctx ref w r s' w', visitLiteral l s ctx cctx ref w = .ok (r, s') w' →
      True) ∧
    (∀ cn args s ctx cctx ref w r s' w',
      visitConstructor cn args s ctx cctx ref w = .ok (r, s') w' → True) ∧
    (∀ e s ctx cctx ref w t s' w', visitConst e s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ, BridgeInv env Us known Γ (gw w) ctx s Δ →
      ∀ n us, e = .const n us → known n → Γ.ctors n = none → Γ.casesOns n = none →
      Erases env Us Γ Δ e t ∧ s' = s ∧ gw w ≤ gw w') ∧
    (∀ n s ctx cctx ref w kn s' w',
      get_constant_kername n s ctx cctx ref w = .ok (kn, s') w' →
      ∀ Δ, BridgeInv env Us known Γ (gw w) ctx s Δ → known n →
      kn = Γ.constants n ∧ s' = s ∧ gw w ≤ gw w') ∧
    (∀ n s ctx cctx ref w r s' w', visitMutual n s ctx cctx ref w = .ok (r, s') w' →
      True) ∧
    (∀ f' args s ctx cctx ref w t s' w',
      visitAppArgs f' args s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ (hd : Expr), BridgeInv env Us known Γ (gw w) ctx s Δ →
      Erases env Us Γ Δ hd f' →
      (∀ i (hi : i < args.size), Supported known Γ (args[i]) ∧
        ∃ ve, TrExprS env Us Δ (args[i]) ve) →
      Erases env Us Γ Δ (args.foldl Expr.app hd) t ∧ s' = s ∧ gw w ≤ gw w') ∧
    (∀ e s ctx cctx ref w t s' w', visitLet e s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ, BridgeInv env Us known Γ (gw w) ctx s Δ →
      ∀ n ty v b nd, e = .letE n ty v b nd → Supported known Γ e →
      (∃ ve, TrExprS env Us Δ e ve) →
      Erases env Us Γ Δ e t ∧ s' = s ∧ gw w ≤ gw w') ∧
    (∀ e s ctx cctx ref w t s' w', visitLambda e s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ, BridgeInv env Us known Γ (gw w) ctx s Δ →
      ∀ n ty b bi, e = .lam n ty b bi → Supported known Γ e →
      (∃ ve, TrExprS env Us Δ e ve) →
      Erases env Us Γ Δ e t ∧ s' = s ∧ gw w ≤ gw w') ∧
    (∀ tn i e s ctx cctx ref w r s' w',
      visitProj tn i e s ctx cctx ref w = .ok (r, s') w' → True) ∧
    (∀ e s ctx cctx ref w t s' w', visitApp e s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ, BridgeInv env Us known Γ (gw w) ctx s Δ → Supported known Γ e →
      (∃ ve, TrExprS env Us Δ e ve) →
      Erases env Us Γ Δ e t ∧ s' = s ∧ gw w ≤ gw w') ∧
    (∀ e s ctx cctx ref w t s' w', visitConstApp e s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ, BridgeInv env Us known Γ (gw w) ctx s Δ → Supported known Γ e →
      (∃ ve, TrExprS env Us Δ e ve) →
      ∀ cn us, e.getAppFn = .const cn us →
      Erases env Us Γ Δ e t ∧ s' = s ∧ gw w ≤ gw w') ∧
    (∀ cn ar e s ctx cctx ref w r s' w',
      visitCtorEta cn ar e s ctx cctx ref w = .ok (r, s') w' → True) ∧
    (∀ cn ar ty fe args s ctx cctx ref w r s' w',
      visitCtorEtaGo cn ar ty fe args s ctx cctx ref w = .ok (r, s') w' → True) ∧
    (∀ ci e s ctx cctx ref w r s' w',
      visitCasesEta ci e s ctx cctx ref w = .ok (r, s') w' → True) ∧
    (∀ ci ty fe args s ctx cctx ref w r s' w',
      visitCasesEtaGo ci ty fe args s ctx cctx ref w = .ok (r, s') w' → True) ∧
    (∀ ci args s ctx cctx ref w r s' w',
      visitCases ci args s ctx cctx ref w = .ok (r, s') w' → True) ∧
    (∀ nf mask e s ctx cctx ref w r s' w',
      visitAlt nf mask e s ctx cctx ref w = .ok (r, s') w' → True) := by
  apply visitExpr.mutual_fixpoint_induct
    (motive_1 := fun f => ∀ e s ctx cctx ref w t s' w',
      f e s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ, BridgeInv env Us known Γ (gw w) ctx s Δ → Supported known Γ e →
      (∃ ve, TrExprS env Us Δ e ve) →
      Erases env Us Γ Δ e t ∧ s' = s ∧ gw w ≤ gw w')
    (motive_2 := fun f => ∀ l s ctx cctx ref w r s' w',
      f l s ctx cctx ref w = .ok (r, s') w' → True)
    (motive_3 := fun f => ∀ cn args s ctx cctx ref w r s' w',
      f cn args s ctx cctx ref w = .ok (r, s') w' → True)
    (motive_4 := fun f => ∀ e s ctx cctx ref w t s' w',
      f e s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ, BridgeInv env Us known Γ (gw w) ctx s Δ →
      ∀ n us, e = .const n us → known n → Γ.ctors n = none → Γ.casesOns n = none →
      Erases env Us Γ Δ e t ∧ s' = s ∧ gw w ≤ gw w')
    (motive_5 := fun f => ∀ n s ctx cctx ref w kn s' w',
      f n s ctx cctx ref w = .ok (kn, s') w' →
      ∀ Δ, BridgeInv env Us known Γ (gw w) ctx s Δ → known n →
      kn = Γ.constants n ∧ s' = s ∧ gw w ≤ gw w')
    (motive_6 := fun f => ∀ n s ctx cctx ref w r s' w',
      f n s ctx cctx ref w = .ok (r, s') w' → True)
    (motive_7 := fun f => ∀ f' args s ctx cctx ref w t s' w',
      f f' args s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ (hd : Expr), BridgeInv env Us known Γ (gw w) ctx s Δ →
      Erases env Us Γ Δ hd f' →
      (∀ i (hi : i < args.size), Supported known Γ (args[i]) ∧
        ∃ ve, TrExprS env Us Δ (args[i]) ve) →
      Erases env Us Γ Δ (args.foldl Expr.app hd) t ∧ s' = s ∧ gw w ≤ gw w')
    (motive_8 := fun f => ∀ e s ctx cctx ref w t s' w',
      f e s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ, BridgeInv env Us known Γ (gw w) ctx s Δ →
      ∀ n ty v b nd, e = .letE n ty v b nd → Supported known Γ e →
      (∃ ve, TrExprS env Us Δ e ve) →
      Erases env Us Γ Δ e t ∧ s' = s ∧ gw w ≤ gw w')
    (motive_9 := fun f => ∀ e s ctx cctx ref w t s' w',
      f e s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ, BridgeInv env Us known Γ (gw w) ctx s Δ →
      ∀ n ty b bi, e = .lam n ty b bi → Supported known Γ e →
      (∃ ve, TrExprS env Us Δ e ve) →
      Erases env Us Γ Δ e t ∧ s' = s ∧ gw w ≤ gw w')
    (motive_10 := fun f => ∀ tn i e s ctx cctx ref w r s' w',
      f tn i e s ctx cctx ref w = .ok (r, s') w' → True)
    (motive_11 := fun f => ∀ e s ctx cctx ref w t s' w',
      f e s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ, BridgeInv env Us known Γ (gw w) ctx s Δ → Supported known Γ e →
      (∃ ve, TrExprS env Us Δ e ve) →
      Erases env Us Γ Δ e t ∧ s' = s ∧ gw w ≤ gw w')
    (motive_12 := fun f => ∀ e s ctx cctx ref w t s' w',
      f e s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ, BridgeInv env Us known Γ (gw w) ctx s Δ → Supported known Γ e →
      (∃ ve, TrExprS env Us Δ e ve) →
      ∀ cn us, e.getAppFn = .const cn us →
      Erases env Us Γ Δ e t ∧ s' = s ∧ gw w ≤ gw w')
    (motive_13 := fun f => ∀ cn ar e s ctx cctx ref w r s' w',
      f cn ar e s ctx cctx ref w = .ok (r, s') w' → True)
    (motive_14 := fun f => ∀ cn ar ty fe args s ctx cctx ref w r s' w',
      f cn ar ty fe args s ctx cctx ref w = .ok (r, s') w' → True)
    (motive_15 := fun f => ∀ ci e s ctx cctx ref w r s' w',
      f ci e s ctx cctx ref w = .ok (r, s') w' → True)
    (motive_16 := fun f => ∀ ci ty fe args s ctx cctx ref w r s' w',
      f ci ty fe args s ctx cctx ref w = .ok (r, s') w' → True)
    (motive_17 := fun f => ∀ ci args s ctx cctx ref w r s' w',
      f ci args s ctx cctx ref w = .ok (r, s') w' → True)
    (motive_18 := fun f => ∀ nf mask e s ctx cctx ref w r s' w',
      f nf mask e s ctx cctx ref w = .ok (r, s') w' → True)
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
  · intro vE vLit vLet vLam vProj vApp _ih1 _ih2 ih8 ih9 _ih10 ih11
    intro e s ctx cctx ref w t s' w' hrun Δ hinv hsupp hex
    simp only [] at hrun
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
      exact ⟨.box hve (hsound hc Δ ve hinv.trlctx hve), rfl, hle₁⟩
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
        rw [run_bind_ok] at hk
        obtain ⟨u, s₂, w₂, hp1, hp2⟩ := hk
        rw [run_pure] at hp1; cases hp1
        rw [run_pure] at hp2; cases hp2
        exact ⟨.fvar x, rfl, hle₁⟩
      | const n us hkn hctor hcases =>
        simp only [] at hk
        rw [run_bind_ok] at hk
        obtain ⟨u, s₂, w₂, hp1, hk⟩ := hk
        rw [run_pure] at hp1; cases hp1
        obtain ⟨er, hs, hle₂⟩ := ih11 _ _ _ _ _ _ _ _ _ hk Δ (hinv.mono hle₁)
          (.const n us hkn hctor hcases) hex
        exact ⟨er, hs, NameGenerator.LE.trans hle₁ hle₂⟩
      | app hf ha =>
        simp only [] at hk
        rw [run_bind_ok] at hk
        obtain ⟨u, s₂, w₂, hp1, hk⟩ := hk
        rw [run_pure] at hp1; cases hp1
        obtain ⟨er, hs, hle₂⟩ := ih11 _ _ _ _ _ _ _ _ _ hk Δ (hinv.mono hle₁)
          (.app hf ha) hex
        exact ⟨er, hs, NameGenerator.LE.trans hle₁ hle₂⟩
      | lam n ty bi hb =>
        simp only [] at hk
        rw [run_bind_ok] at hk
        obtain ⟨u, s₂, w₂, hp1, hk⟩ := hk
        rw [run_pure] at hp1; cases hp1
        obtain ⟨er, hs, hle₂⟩ := ih9 _ _ _ _ _ _ _ _ _ hk Δ (hinv.mono hle₁)
          n ty _ bi rfl (.lam n ty bi hb) hex
        exact ⟨er, hs, NameGenerator.LE.trans hle₁ hle₂⟩
      | letE n ty nd hv hb =>
        simp only [] at hk
        rw [run_bind_ok] at hk
        obtain ⟨u, s₂, w₂, hp1, hk⟩ := hk
        rw [run_pure] at hp1; cases hp1
        obtain ⟨er, hs, hle₂⟩ := ih8 _ _ _ _ _ _ _ _ _ hk Δ (hinv.mono hle₁)
          n ty _ _ nd rfl (.letE n ty nd hv hb) hex
        exact ⟨er, hs, NameGenerator.LE.trans hle₁ hle₂⟩
  -- Step 2: visitLiteral (trivial conclusion).
  · intros; trivial
  -- Step 3: visitConstructor (trivial conclusion).
  · intros; trivial
  -- Step 4: visitConst — the fixvars branch is dead; conclude by motive 5.
  · intro gck ih5
    intro e s ctx cctx ref w t s' w' hrun Δ hinv n us he hkn hctor hcases
    subst he
    simp only [] at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨c, s₁, w₁, hrd, hk⟩ := hrun
    rw [run_read] at hrd
    cases hrd
    rw [hinv.fixvars] at hk
    simp only [Option.bind] at hk
    rw [run_bind_ok] at hk
    obtain ⟨u, s₂, w₂, hp, hk⟩ := hk
    rw [run_pure] at hp; cases hp
    rw [run_bind_ok] at hk
    obtain ⟨kn, s₃, w₃, hgck, hp2⟩ := hk
    rw [run_pure] at hp2; cases hp2
    obtain ⟨hkn', hs, hle⟩ := ih5 _ _ _ _ _ _ _ _ _ hgck Δ hinv hkn
    exact ⟨.const n us kn hkn'.symm, hs, hle⟩
  -- Step 5: get_constant_kername — the hit branch is forced by the invariant.
  · intro _vMut _ih6
    intro n s ctx cctx ref w kn s' w' hrun Δ hinv hkn
    simp only [] at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨s₀, s₁, w₁, hget, hk⟩ := hrun
    rw [run_get] at hget
    cases hget
    rw [hinv.consts n hkn] at hk
    simp only [] at hk
    rw [run_pure] at hk
    cases hk
    exact ⟨rfl, rfl, NameGenerator.LE.rfl⟩
  -- Step 6: visitMutual (trivial conclusion).
  · intros; trivial
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
        Erases env Us Γ Δ (pre.foldl Expr.app hd) acc ∧ s₁ = s ∧ gw w ≤ gw w₁)
      ⟨herf, rfl, NameGenerator.LE.rfl⟩
      (fun pre x post acc s₁ w₁ acc' s₂ w₂ hLpre hPacc hg => by
        rw [run_bind_ok] at hg
        obtain ⟨tx, s₃, w₃, hvx, hp⟩ := hg
        rw [run_pure] at hp
        cases hp
        obtain ⟨hErpre, rfl, hle⟩ := hPacc
        obtain ⟨hsx, hex⟩ := hmem x (by rw [hLpre]; exact List.mem_append_right _ List.mem_cons_self)
        obtain ⟨erx, hs₃, hle₂⟩ := ih1 _ _ _ _ _ _ _ _ _ hvx Δ (hinv.mono hle) hsx hex
        refine ⟨?_, hs₃, NameGenerator.LE.trans hle hle₂⟩
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
    obtain ⟨hs₁, hnres, hres, hle₁⟩ := H.fresh_run _ _ _ _ _ _ _ _ hfresh
    subst hs₁
    rw [run_withReader] at hk
    rw [run_bind_ok] at hk
    obtain ⟨tv, s₂, w₂, hvv, hk2⟩ := hk
    rw [run_bind_ok] at hk2
    obtain ⟨tb, s₃, w₃, hvb, hm⟩ := hk2
    cases hsupp with
    | letE _ _ _ hv hb =>
    obtain ⟨ve, hve⟩ := hex
    cases hve with
    | letE hvt hty hval hbody =>
    have hx : x ∉ Δ.fvars := fun hmem => hnres (hinv.reserved x hmem)
    have hΔ' := LeanToLambdaBox.TrLCtx.mkLetDecl (n := n) (nd := nd) hinv.trlctx
      (hinv.trlctx.find?_eq_none.mpr hx) hty hval hvt
    have hinv' := hinv.mkLetDecl (n := n) (nd := nd) hty hval hvt hx hle₁ hres
    -- the value, in the extended context
    have hvext := hval.weakFV henv (.skip_fvar _ _ .refl) hΔ'.wf
    obtain ⟨erv, hs₂, hle₂⟩ := ih1 _ _ _ _ _ _ _ _ _ hvv _ hinv' hv ⟨_, hvext⟩
    subst hs₂
    -- the opened body, in the extended context
    rw [Lean.Expr.instantiate1_eq] at hvb
    have hbext := TrExprS.inst_fvar henv hΔ'.wf hbody
    obtain ⟨erb, hs₃, hle₃⟩ := ih1 _ _ _ _ _ _ _ _ _ hvb _ (hinv'.mono hle₂)
      (hb.instantiate1' x 0) ⟨_, hbext⟩
    subst hs₃
    -- the mkLetIn tail
    unfold Erasure.mkLetIn at hm
    rw [run_bind_ok] at hm
    obtain ⟨bn, s₄, w₄, hf2n, hp⟩ := hm
    rw [run_pure] at hp
    cases hp
    have hdn : ((ctx.lctx.mkLetDecl x n ty v nd).fvarIdToDecl.find! x).userName = n := by
      rw [LocalContext.fvarIdToDecl_find!_of_find?
        (LocalContext.find?_mkLetDecl_self hinv.trlctx.1 (hinv.trlctx.find?_eq_none.mpr hx))]
      rfl
    cases (run_fvar_to_name x n _ { ctx with lctx := ctx.lctx.mkLetDecl x n ty v nd }
      cctx ref _ hdn).symm.trans hf2n
    refine ⟨?_, rfl, NameGenerator.LE.trans hle₁ (NameGenerator.LE.trans hle₂ hle₃)⟩
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
    obtain ⟨hs₁, hnres, hres, hle₁⟩ := H.fresh_run _ _ _ _ _ _ _ _ hfresh
    subst hs₁
    rw [run_withReader] at hk
    rw [run_bind_ok] at hk
    obtain ⟨tb, s₂, w₂, hvb, hm⟩ := hk
    cases hsupp with
    | lam _ _ _ hb =>
    obtain ⟨ve, hve⟩ := hex
    cases hve with
    | lam hty' hty hbody =>
    have hx : x ∉ Δ.fvars := fun hmem => hnres (hinv.reserved x hmem)
    have hΔ' := LeanToLambdaBox.TrLCtx.mkLocalDecl (n := n) (bi := bi) hinv.trlctx
      (hinv.trlctx.find?_eq_none.mpr hx) hty hty'
    have hinv' := hinv.mkLocalDecl (n := n) (bi := bi) hty hty' hx hle₁ hres
    rw [Lean.Expr.instantiate1_eq] at hvb
    have hbext := TrExprS.inst_fvar henv hΔ'.wf hbody
    obtain ⟨erb, hs₂, hle₂⟩ := ih1 _ _ _ _ _ _ _ _ _ hvb _ hinv'
      (hb.instantiate1' x 0) ⟨_, hbext⟩
    subst hs₂
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
    refine ⟨?_, rfl, NameGenerator.LE.trans hle₁ hle₂⟩
    rw [abstract_eq]
    exact bridge_lam_case hinv.trlctx.2.noBV hty hbody hx erb
  -- Step 10: visitProj (trivial conclusion).
  · intros; trivial
  -- Step 11: visitApp — dispatch on the head: const heads to visitConstApp,
  -- other heads through visitExpr + visitAppArgs and the spine reconstruction.
  · intro vE vAA vCA ih1 ih7 ih12
    intro e s ctx cctx ref w t s' w' hrun Δ hinv hsupp hex
    simp only [] at hrun
    obtain ⟨⟨hsuppfn, fve, htrfn⟩, hargfacts⟩ := spine_arg_facts hsupp hex
    cases hfn : e.getAppFn
    case const cn us =>
      rw [hfn] at hrun
      simp only [] at hrun
      exact ih12 _ _ _ _ _ _ _ _ _ hrun Δ hinv hsupp hex cn us hfn
    all_goals (
      rw [hfn] at hrun
      simp only [] at hrun
      rw [expr_withApp_eq] at hrun
      rw [run_bind_ok] at hrun
      obtain ⟨tf, s₁, w₁, hvf, hk⟩ := hrun
      obtain ⟨erf, hs₁, hle₁⟩ := ih1 _ _ _ _ _ _ _ _ _ hvf Δ hinv hsuppfn ⟨fve, htrfn⟩
      subst hs₁
      obtain ⟨erapp, hs', hle₂⟩ := ih7 _ _ _ _ _ _ _ _ _ _ hk Δ e.getAppFn
        (hinv.mono hle₁) erf hargfacts
      rw [getAppArgs_spine'] at erapp
      exact ⟨erapp, hs', NameGenerator.LE.trans hle₁ hle₂⟩)
  -- Step 12: visitConstApp — the two eta branches are killed by the fragment's
  -- negative classifier facts; then motive 4 for the head and motive 7 for the
  -- spine.
  · intro vC vAA vCtE vCsE ih4 ih7 _ih13 _ih15
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
    have hsuppfn : Supported known Γ (Expr.const cn us) := by
      rw [← hfn]; exact hsupp.getAppFn
    cases hsuppfn with
    | const _ _ hkn hctor hcases =>
    have ho : o = none := hnone₁ hcases
    subst ho
    simp only [] at hk
    rw [run_bind_ok] at hk
    obtain ⟨o₂, s₂, w₂, hct, hk⟩ := hk
    rw [run_liftCoreM_ok] at hct
    obtain ⟨hct, rfl⟩ := hct
    obtain ⟨hle₂, hnone₂⟩ := H.ctor_run cn cctx ref w₁ o₂ w₂ hct
    have ho₂ : o₂ = none := hnone₂ hctor
    subst ho₂
    simp only [] at hk
    rw [run_bind_ok] at hk
    obtain ⟨tc, s₃, w₃, hvc, hk⟩ := hk
    obtain ⟨erc, hs₃, hle₃⟩ := ih4 _ _ _ _ _ _ _ _ _ hvc Δ
      (hinv.mono (NameGenerator.LE.trans hle₁ hle₂)) cn us rfl hkn hctor hcases
    subst hs₃
    obtain ⟨_, hargfacts⟩ := spine_arg_facts hsupp hex
    have erfn : Erases env Us Γ Δ e.getAppFn tc := by rw [hfn]; exact erc
    obtain ⟨erapp, hs', hle₄⟩ := ih7 _ _ _ _ _ _ _ _ _ _ hk Δ e.getAppFn
      (hinv.mono (NameGenerator.LE.trans hle₁ (NameGenerator.LE.trans hle₂ hle₃)))
      erfn hargfacts
    rw [getAppArgs_spine'] at erapp
    exact ⟨erapp, hs',
      NameGenerator.LE.trans hle₁ (NameGenerator.LE.trans hle₂
        (NameGenerator.LE.trans hle₃ hle₄))⟩
  -- Steps 13–18: trivial conclusions.
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial

/-! ## The exported theorem -/

/-- **The bridge theorem**: on the supported fragment, under the trust bundle
`BridgeHyps` and the invariant `BridgeInv`, a successful run of the shipping
erasure `Erasure.visitExpr` refines the typed erasure relation `Erases`;
moreover it leaves the `ErasureState` unchanged and advances the ghost
name-generator measure monotonically. -/
theorem visitExpr_refines_erases {env : VEnv} {Us : List Name}
    {known : Name → Prop} {Γ : ErasureCtx} {gw : Void IO.RealWorld → NameGenerator}
    (H : BridgeHyps env Us Γ gw) (henv : env.Ordered) :
    ∀ e s ctx cctx ref w t s' w',
      Erasure.visitExpr e s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ, BridgeInv env Us known Γ (gw w) ctx s Δ →
        Supported known Γ e → (∃ ve, TrExprS env Us Δ e ve) →
        Erases env Us Γ Δ e t ∧ s' = s ∧ gw w ≤ gw w' :=
  (visitExpr_refines_erases_core H henv).1

/-! ## Non-vacuity guards

The `BridgeHyps` fields quantify over opaque runtime primitives, so their
global satisfiability is not in-logic decidable — that is the documented trust
boundary. Everything *else* is checked non-vacuous here: `BridgeInv` is
satisfiable, and the theorem's full non-run premise set is jointly
instantiable at a concrete context/term. -/

section NonVacuity

/-- (i) `BridgeInv` is satisfiable: the empty-context instance at `Δ = []`,
`known := fun _ => False`, `fixvars = none`. -/
example (env : VEnv) (Us : List Name) (Γ : ErasureCtx) (gen : NameGenerator)
    (cfg : ErasureConfig) :
    BridgeInv env Us (fun _ => False) Γ gen ⟨{}, none, cfg⟩ {} [] where
  trlctx := Lean4Lean.TrLCtx.nil
  fixvars := rfl
  reserved := fun _ hfv => nomatch hfv
  consts := fun _ h => h.elim

/-- (ii) The non-run premises of `visitExpr_refines_erases` are jointly
instantiable: a concrete one-fvar context (with `TrLCtx` *constructed*, not
assumed) and the supported term `.fvar x` satisfy every premise except the run
itself and the trust bundle, which stay hypothetical because the primitives
are opaque. -/
example (env : VEnv) (Us : List Name) (Γ : ErasureCtx) (cfg : ErasureConfig)
    (gw : Void IO.RealWorld → NameGenerator)
    (H : BridgeHyps env Us Γ gw) (henv : env.Ordered)
    (x : FVarId) (nm : Name) (bi : BinderInfo)
    (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)
    (w w' : Void IO.RealWorld) (t : LBTerm) (s' : ErasureState)
    (hres : (gw w).Reserves x)
    (hrun : Erasure.visitExpr (.fvar x) {}
      ⟨({} : LocalContext).mkLocalDecl x nm (.sort .zero) bi, none, cfg⟩ cctx ref w
      = .ok (t, s') w') :
    Erases env Us Γ [(some (x, (Expr.sort .zero).fvarsList), .vlam (.sort .zero))]
      (.fvar x) t ∧ s' = ({} : ErasureState) ∧ gw w ≤ gw w' := by
  have hty : TrExprS env Us [] (.sort .zero) (.sort .zero) := .sort rfl
  have hty' : env.IsType Us.length (VLCtx.toCtx []) (.sort .zero) :=
    ⟨_, .sortDF trivial trivial rfl⟩
  have hfind : ({} : LocalContext).find? x = none :=
    (Lean4Lean.TrLCtx.nil (env := env) (Us := Us)).find?_eq_none.mpr (fun h => nomatch h)
  have htr : TrLCtx env Us (({} : LocalContext).mkLocalDecl x nm (.sort .zero) bi)
      [(some (x, (Expr.sort .zero).fvarsList), .vlam (.sort .zero))] :=
    LeanToLambdaBox.TrLCtx.mkLocalDecl Lean4Lean.TrLCtx.nil hfind hty hty'
  have hinv : BridgeInv env Us (fun _ => False) Γ (gw w)
      ⟨({} : LocalContext).mkLocalDecl x nm (.sort .zero) bi, none, cfg⟩ {}
      [(some (x, (Expr.sort .zero).fvarsList), .vlam (.sort .zero))] :=
    { trlctx := htr
      fixvars := rfl
      reserved := by
        intro fv hfv
        have : fv = x ∨ fv ∈ VLCtx.fvars [] := by simpa using hfv
        rcases this with rfl | h
        · exact hres
        · exact nomatch h
      consts := fun _ h => h.elim }
  have hfind2 : VLCtx.find?
      [(some (x, (Expr.sort .zero).fvarsList), .vlam (.sort .zero))] (.inr x)
      = some ((VLocalDecl.vlam (.sort .zero)).value, (VLocalDecl.vlam (.sort .zero)).type) := by
    simp [Lean4Lean.VLCtx.find?, Lean4Lean.VLCtx.next]
  have hex : ∃ ve, TrExprS env Us
      [(some (x, (Expr.sort .zero).fvarsList), .vlam (.sort .zero))] (.fvar x) ve :=
    ⟨_, .fvar hfind2⟩
  exact visitExpr_refines_erases H henv _ _ _ _ _ _ _ _ _ hrun _ hinv (.fvar x) hex

end NonVacuity

/- Axiom audit (2026-07-07, via temporary `#print axioms`, since removed):
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
