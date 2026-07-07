import LeanToLambdaBox.Erases
import LeanToLambdaBox.Abstract

/-!
# `Erases` transports along fvar→de-Bruijn closing (step A2.4: the bridge crux)

The shipping erasure (`Erasure.visitExpr`) processes a binder by *opening* it with a
fresh free variable, erasing the opened body, and *closing* the result again:
`visitLambda`/`visitLet` (Erasure.lean:608/:613) call `lambdaMonocular`/`letMonocular`
(Erasure.lean:289/:298), which `instantiate1` the body with `.fvar x`, and
`mkLambda`/`mkLetIn` (Erasure.lean:246/:248) close the erased body with
`abstract x = toBvar x 0` (Basic.lean). The pure model (`Erases`, `eraseCore`) never
leaves de Bruijn land. This file proves that the typed erasure relation `Erases`
transports along that closing, mirroring lean4lean's `TrExprS.abstract` /
`TrExprS.uninstantiate` (Verify/Typing/Lemmas.lean) — the missing link that lets the
`visitExpr`→`Erases` bridge treat "open with fresh `x`, recurse, `abstract x`" as the
binder rule of `Erases`.

## The key asymmetry, and why a closedness premise appears

`Expr.abstract1 v₀ dk` (lean4lean Verify/Axioms.lean) *shifts* loose bvars `≥ dk` up
by one: in a `VLCtx`, de Bruijn indices skip fvar-tagged entries, and
`VLCtx.Abstract` flips a `(some (v₀, deps), d₀)` entry into a `(none, d₀)` one, so
source indices past the insertion point must make room. `LBTerm.toBvar v₀ dk`
(Basic.lean) does **not** shift: `.bvar i ↦ .bvar i`. The two sides stay aligned only
because the bridge always abstracts a term with *no* loose bvars at or above `dk`
(the freshly opened body is closed below the insertion point), which makes the
source-side shift dead code. Hence `Erases.abstract` carries a `Closed e dk` premise
(lean4lean's closedness predicate, cf. `TrExprS.closed`), threaded `+1` under
binders.

Trust boundary: as everywhere in this development, results here may inherit
`sorryAx` through lean4lean's `TrExprS` lemmas (see the header of Erases.lean);
audited axiom sets are recorded next to each theorem.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-! ### Helpers: `abstract1`/`toBvar` bookkeeping

Mirrors the helper layer of `Erases.lean` (`instantiate1'_foldl_app`,
`shift_mkLambdas`, …) for the closing operation. -/

/-- `Expr.abstract1` distributes over an application spine built by
`args.foldl Expr.app` (mirror of `instantiate1'_foldl_app`, Erases.lean:75). Used by
the `ctor`/`cases` cases of `Erases.abstract`. -/
theorem abstract1_foldl_app (v : FVarId) (d : Nat) (f : Expr) (args : List Expr) :
    (args.foldl Expr.app f).abstract1 v d
      = (args.map (·.abstract1 v d)).foldl Expr.app (f.abstract1 v d) := by
  induction args generalizing f with
  | nil => rfl
  | cons a as ih => simp only [List.foldl, List.map, ih, Expr.abstract1]

/-- `toBvar` pushes under a re-wrapped `casesOn` alternative, bumping the insertion
level by the number of field binders (mirror of `shift_mkLambdas`, Erases.lean:101). -/
theorem toBvar_mkLambdas (x : FVarId) (lvl : Nat) (names : List BinderName) (body : LBTerm) :
    toBvar x lvl (mkLambdas names body)
      = mkLambdas names (toBvar x (lvl + names.length) body) := by
  induction names generalizing lvl with
  | nil => rfl
  | cons n ns ih =>
      have h : lvl + (ns.length + 1) = (lvl + 1) + ns.length := by omega
      simp only [mkLambdas, toBvar, List.length_cons, h, ih]

/-- `BEq` on `FVarId` is symmetric. Needed because `Expr.abstract1` tests `v₀ == y`
while `toBvar` tests `y == v₀`; proved from the local reflection lemma
`fvarId_beq_iff_eq` (Abstract.lean) since core ships no `LawfulBEq FVarId`. -/
theorem fvarId_beq_comm (x y : FVarId) : (x == y) = (y == x) := by
  cases hxy : (x == y) <;> cases hyx : (y == x) <;> try rfl
  · exact absurd (fvarId_beq_iff_eq.mpr (fvarId_beq_iff_eq.mp hyx).symm) (by simp [hxy])
  · exact absurd (fvarId_beq_iff_eq.mpr (fvarId_beq_iff_eq.mp hxy).symm) (by simp [hyx])

/-! ### Closedness inversion helpers

Small inversions of lean4lean's `Closed` that its library does not provide. -/

/-- Closedness of an application spine gives closedness of the head and of every
argument (inversion used by the `ctor`/`cases` cases of `Erases.abstract`). -/
theorem closed_foldl_app {k : Nat} {args : List Expr} {f : Expr}
    (h : Closed (args.foldl Expr.app f) k) : Closed f k ∧ ∀ a ∈ args, Closed a k := by
  induction args generalizing f with
  | nil => exact ⟨h, by simp⟩
  | cons a as ih =>
    obtain ⟨hfa, hrest⟩ := ih (f := f.app a) h
    refine ⟨hfa.1, fun b hb => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hfa.2
    · exact hrest _ hb

/-- Opening a binder body with a free variable eats one level of closedness: if `e`
is closed at `k + 1`, then `e.instantiate1' (.fvar v₀) k` is closed at `k`. This is
what turns the closedness of the *un-instantiated* body (the form `uninstantiateN`
receives) into the premise `Erases.abstract` needs. -/
theorem closed_instantiate1'_fvar {v₀ : FVarId} {e : Expr} {k : Nat}
    (h : Closed e (k + 1)) : Closed (Expr.instantiate1' e (.fvar v₀) k) k := by
  induction e generalizing k with simp_all [Expr.instantiate1', Closed]
  | bvar i =>
    split
    · exact ‹i < k›
    · split
      · exact True.intro
      · exfalso; omega

/-! ### The crux lemma: `Erases` transports along `abstract1`/`toBvar`

Mirror of lean4lean's `TrExprS.abstract` (Verify/Typing/Lemmas.lean:1530), with the
same context witness `VLCtx.Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ` (ibid.:479). The extra
index `k` measures the *semantic* (`VExpr`) depth skipped and has no `LBTerm`-side
counterpart — `toBvar` only tracks the syntactic insertion level `dk`. -/

/-- **Erasure commutes with fvar→de-Bruijn closing.** If `e` erases to `t` in a
context whose entry `dk` is the fvar `v₀`, and `e` has no loose bvars `≥ dk`, then
closing both sides over `v₀` at level `dk` preserves erasure, in the context with
that entry flipped to a de Bruijn binder.

The `box` case transports its `TrExprS`/`Erasable` witnesses via
`TrExprS.abstract`/`VLCtx.Abstract.toCtx`; `fvar` needs no context lookup (the
`Erases.fvar` rule is context-free, unlike `TrExprS.fvar`); everything else is
structural, with `hc` threaded `+1` under binders. -/
theorem Erases.abstract {env : VEnv} {Us : List Name} {Γ : ErasureCtx}
    {Δ₀ : VLCtx} {v₀ : FVarId} {d₀ : VLocalDecl} {dk k : Nat} {Δ₁ Δ : VLCtx}
    (W : VLCtx.Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ)
    {e : Expr} {t : LBTerm} (hc : Closed e dk) (H : Erases env Us Γ Δ₁ e t) :
    Erases env Us Γ Δ (e.abstract1 v₀ dk) (toBvar v₀ dk t) := by
  induction H generalizing Δ dk k with
  | box htr her => exact .box (htr.abstract W) (W.toCtx ▸ her)
  | bvar i =>
    have hi : i < dk := hc
    simp only [Expr.abstract1, if_pos hi, toBvar]
    exact .bvar i
  | fvar y =>
    simp only [Expr.abstract1, toBvar, fvarId_beq_comm v₀ y]
    cases hyx : (y == v₀)
    · simp only [Bool.false_eq_true, if_false]
      exact .fvar y
    · simp only [if_true]
      exact .bvar dk
  | const n us kn h => exact .const n us kn h
  | app _ _ ihf iha => exact .app (ihf W hc.1) (iha W hc.2)
  | lam hty _ ihb => exact .lam (hty.abstract W) (ihb W.succ hc.2)
  | letE hty hval _ _ ihv ihb =>
    exact .letE (hty.abstract W) (hval.abstract W) (ihv W hc.2.1) (ihb W.succ hc.2.2)
  | @ctor _ cn us iid cidx args args' hctor hlen _ ihargs =>
    obtain ⟨-, hargs_cl⟩ := closed_foldl_app hc
    simp only [abstract1_foldl_app, Expr.abstract1, toBvar, toBvarArgs_eq_map]
    refine .ctor cn us iid cidx hctor (by simp [hlen]) (fun i hi => ?_)
    have hi' : i < args.length := by simpa using hi
    rw [List.getElem_map, List.getElem_map]
    exact ihargs i hi' W (hargs_cl _ (List.getElem_mem hi'))
  | @cases _ con us iid numParams pre discr discr' minors alts' hcase _ hlen _ ihd ihalts =>
    obtain ⟨-, hall⟩ := closed_foldl_app hc
    simp only [abstract1_foldl_app, List.map_cons, Expr.abstract1, toBvar, toBvarAlts_eq_map]
    refine .cases con us iid numParams (pre.map (·.abstract1 v₀ dk)) hcase
      (ihd W (hall _ (List.mem_cons_self ..)))
      (minors := minors.map (·.abstract1 v₀ dk))
      (alts' := alts'.map (fun a => (a.1, toBvar v₀ (dk + a.1.length) a.2)))
      (by simpa using hlen) (fun j hj => ?_)
    have hj' : j < minors.length := by simpa using hj
    rw [List.getElem_map, List.getElem_map, ← toBvar_mkLambdas]
    exact ihalts j hj' W (hall _ (List.mem_cons_of_mem _ (List.getElem_mem hj')))

/-! ### The un-instantiation corollaries

Mirrors of lean4lean's `TrExprS.uninstantiateN`/`uninstantiate`
(Verify/Typing/Lemmas.lean:2035/:2050). These are exactly the form the
`visitExpr`→`Erases` bridge consumes at `visitLambda`/`visitLet`: the shipping
erasure holds `body.instantiate1 (.fvar x)` (as `instantiate1'`, lean4lean's pure
model of `Expr.instantiate1`) and closes the erased result with
`abstract x = toBvar x 0` (`abstract_eq`, Abstract.lean). -/

/-- If the body opened with fresh `v₀` erases to `t`, then the *un-opened* body
erases to `toBvar v₀ dk t`, flipping the fvar entry to a de Bruijn one.
Premises: `v₀` genuinely fresh for `e` (`sc`), and `e` closed at `dk + 1` (one loose
bvar allowed — the one being re-bound). -/
theorem Erases.uninstantiateN {env : VEnv} {Us : List Name} {Γ : ErasureCtx}
    {Δ₀ : VLCtx} {v₀ : FVarId} {d₀ : VLocalDecl} {dk k : Nat} {Δ₁ Δ : VLCtx}
    (W : VLCtx.Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ)
    {e : Expr} {t : LBTerm}
    (H : Erases env Us Γ Δ₁ (Expr.instantiate1' e (.fvar v₀) dk) t)
    (sc : FVarsIn (· ≠ v₀) e) (hc : Closed e (dk + 1)) :
    Erases env Us Γ Δ e (toBvar v₀ dk t) := by
  have h := Erases.abstract W (closed_instantiate1'_fvar hc) H
  rwa [sc.abstract_instantiate1] at h

/-- The `dk = 0` corollary, in the exact shape of the bridge's binder step
(`lambdaMonocular`/`letMonocular` + `mkLambda`/`mkLetIn`, Erasure.lean): open the
body with a fresh `v₀`, erase, close with `toBvar v₀ 0` (= `abstract v₀`,
`abstract_eq`). -/
theorem Erases.uninstantiate {env : VEnv} {Us : List Name} {Γ : ErasureCtx}
    {v₀ : FVarId} {deps : List FVarId} {d : VLocalDecl} {Δ : VLCtx}
    {e : Expr} {t : LBTerm}
    (H : Erases env Us Γ ((some (v₀, deps), d) :: Δ) (e.instantiate1' (.fvar v₀)) t)
    (sc : FVarsIn (· ≠ v₀) e) (hc : Closed e 1) :
    Erases env Us Γ ((none, d) :: Δ) e (toBvar v₀ 0 t) :=
  H.uninstantiateN .zero sc hc

/-! ### Positive sanity layer (non-vacuity checks)

The hypotheses of `Erases.uninstantiate` are jointly satisfiable and the conclusion
computes to the expected term — repo discipline: no lemma ships without a witness
that it fires. -/

/- (i)+(ii) The bvar round-trip: `(.bvar 0).instantiate1' (.fvar v₀) = .fvar v₀`, so
from the (context-free) `Erases.fvar` derivation for the opened body we conclude
`Erases … (.bvar 0) (.bvar 0)` — the closing really re-binds the variable. -/
example (env : VEnv) (Us : List Name) (Γ : ErasureCtx) (Δ : VLCtx)
    (v₀ : FVarId) (deps : List FVarId) (d : VLocalDecl) :
    Erases env Us Γ ((none, d) :: Δ) (.bvar 0) (.bvar 0) := by
  have H : Erases env Us Γ ((some (v₀, deps), d) :: Δ)
      ((Expr.bvar 0).instantiate1' (.fvar v₀)) (.fvar v₀) := .fvar v₀
  have h := H.uninstantiate (sc := True.intro) (hc := Nat.zero_lt_one)
  simpa [toBvar, fvarId_beq_iff_eq.mpr (rfl : v₀ = v₀)] using h

/- Same round-trip with a literal `FVarId`: everything, including the `v₀ == v₀`
test inside `toBvar`, computes by `rfl`. -/
example (env : VEnv) (Us : List Name) (Γ : ErasureCtx) (Δ : VLCtx)
    (deps : List FVarId) (d : VLocalDecl) :
    Erases env Us Γ ((none, d) :: Δ) (.bvar 0) (.bvar 0) :=
  have H : Erases env Us Γ ((some (⟨`x⟩, deps), d) :: Δ)
      ((Expr.bvar 0).instantiate1' (.fvar ⟨`x⟩)) (.fvar ⟨`x⟩) := .fvar _
  H.uninstantiate True.intro Nat.zero_lt_one

/- (i) A closed constant: instantiation and closing are both no-ops, and the
conclusion's `toBvar v₀ 0 (.const kn)` computes to `.const kn`. -/
example (env : VEnv) (Us : List Name) (Γ : ErasureCtx) (Δ : VLCtx)
    (v₀ : FVarId) (deps : List FVarId) (d : VLocalDecl)
    (n : Name) (kn : Kername) (h : Γ.constants n = kn) :
    Erases env Us Γ ((none, d) :: Δ) (.const n []) (.const kn) := by
  have H : Erases env Us Γ ((some (v₀, deps), d) :: Δ)
      ((Expr.const n []).instantiate1' (.fvar v₀)) (.const kn) := .const n [] kn h
  exact H.uninstantiate (sc := by intro u hu; cases hu) (hc := True.intro)

/- Axiom audit (2026-07-07, via temporary `#print axioms`, since removed):
* helpers (`abstract1_foldl_app`, `toBvar_mkLambdas`, `fvarId_beq_comm`,
  `closed_foldl_app`, `closed_instantiate1'_fvar`): `[propext, Quot.sound]` or less;
* `Erases.abstract`, `Erases.uninstantiateN`, `Erases.uninstantiate`:
  `[propext, sorryAx, Classical.choice, Quot.sound]`.
The `sorryAx` is inherited from lean4lean (`Lean4Lean.TrExprS.abstract` itself
reports the same set), entering through the `box` case exactly as documented in
Erases.lean's header; no new axioms, no `sorry` of our own, no `native_decide`. -/

end LeanToLambdaBox
