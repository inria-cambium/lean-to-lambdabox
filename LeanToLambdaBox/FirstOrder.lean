/-
# Task A — First-order determinism (MetaCoq §7.3)

On first-order inductive **values**, the (non-deterministic) erasure relation
`Erases` collapses to the pure erasure function `eraseCore`, upgrading the
relation-level `erases_correct` to a function-level correctness on first-order
results. See the paper `3706056.pdf` §7.3 (`firstorder_erases_deterministic`,
`erase_correct_firstorder`).
-/
import LeanToLambdaBox.Erases
import LeanToLambdaBox.Erasability
import LeanToLambdaBox.EraseCore
import LeanToLambdaBox.ErasesCorrect
import LeanToLambdaBox.ErasesCorrectData

namespace LeanToLambdaBox

open Lean Lean4Lean

/-! ## A1 — First-order inductive values

A *first-order value* is a saturated constructor application whose arguments are
themselves first-order values. The shape mirrors `Erases.ctor`: the source term is
the application spine `args.foldl Expr.app (.const cn us)`, recognised as a
constructor via `Γ.ctors cn = some (iid, cidx)`.

The "informative / non-`Prop` data inductive" condition required by the §7.3
determinism result is carried as an explicit hypothesis `info` on every node: the
node's *type* (whatever its lean4lean translation `ve` is given) is neither a
`Prop` (so the value is not a proof) nor an arity-up-to-defeq (so the value is not
a type-former). This is exactly the property that an *informative data inductive*
(MetaCoq's `is_propositional = false`) guarantees of its constructors' results; we
keep it as a light hypothesis rather than reconstructing the inductive's signature
metatheory (which would require the constructor-type machinery lean4lean does not
expose). See `InformativeType` below. -/

/--
`InformativeType env Us Δ e` says: the source term `e` has, under its lean4lean
translation, a type `A` that is *informative data* — neither a `Prop` nor a
type-former (arity up to defeq). Concretely there is a translation `ve` of `e` and
a type `A` with `HasType ve A`, where `A` is neither typed by `Sort 0` nor an
`IsArityUpTo`.

This is precisely the negation of `Erasable` *with the type witness pinned down*:
`Erasable` existentially quantifies the type, asserting *some* type of `e` is a
`Prop` or arity; `InformativeType` exhibits *one* type that is neither. Type
uniqueness (`IsDefEq.uniqU`) bridges the two, which is the content of A2.
-/
def InformativeType (env : VEnv) (Us : List Name) (Δ : VLCtx) (e : Expr) : Prop :=
  ∃ ve A, TrExprS env Us Δ e ve ∧ env.HasType Us.length Δ.toCtx ve A ∧
    ¬ env.HasType Us.length Δ.toCtx A (.sort .zero) ∧
    ¬ IsArityUpTo env Us.length Δ.toCtx A

/--
First-order inductive values, parameterised by the typing environment, universe
parameters, erasure context `Γ` and the binder context `Δ`.

A first-order value is a fully-applied constructor `args.foldl Expr.app
(.const cn us)` such that:

* `cn` is a registered constructor (`Γ.ctors cn = some (iid, cidx)`) and *not* a
  registered `casesOn` (`Γ.casesOns cn = none`) — a constructor name is never a
  pattern-match eliminator, matching `eraseCore`'s head-dispatch precedence (it
  checks `casesOns` before `ctors`);
* the whole value's type is *informative data* (`InformativeType` — not a `Prop`,
  not a type-former); and
* every argument is itself a first-order value.

Recursion is on the argument list (each `args[i]` is a `FirstOrderValue`), exactly
matching the `Erases.ctor` spine shape so that A3 can relate one to the other.
-/
inductive FirstOrderValue (env : VEnv) (Us : List Name) (Γ : ErasureCtx) :
    VLCtx → Expr → Prop
  | ctor {Δ} (cn : Name) (us : List Level) (iid : InductiveId) (cidx : Nat)
      {args : List Expr}
      (hc : Γ.ctors cn = some (iid, cidx))
      (hcas : Γ.casesOns cn = none)
      (info : InformativeType env Us Δ (args.foldl Expr.app (.const cn us)))
      (hargs : ∀ i (h : i < args.length), FirstOrderValue env Us Γ Δ args[i]) :
      FirstOrderValue env Us Γ Δ (args.foldl Expr.app (.const cn us))

/-! ## A2 — CRUX: first-order values are not erasable

The main proof effort. A first-order value's type is informative data — not a
`Prop` and not an arity — so it is neither a proof nor a type-former, refuting
both disjuncts of `Erasable`. The bridge between the *pinned* type witness in
`InformativeType` and the *existential* type witness in `Erasable` is type
uniqueness (`IsDefEq.uniqU`), exactly the reasoning in `Erasable.app`. -/

/-- The core of A2, stated directly over `InformativeType`: a term whose pinned
type is informative data is not erasable in any of its translations.

Proof: `InformativeType` supplies a type `A` of (a translation `ve₀` of) `v` with
`¬ HasType A (Sort 0)` and `¬ IsArityUpTo A`. Suppose the given translation `ve`
were `Erasable`, with type `A'` and `A' : Sort 0 ∨ IsArityUpTo A'`. The two
translations are defeq (`TrExprS.uniq`), so `HasType ve A`; the two typings of `ve`
are then defeq (`IsDefEq.uniqU`), `A ≈ A'`. Transporting each disjunct back along
that defeq contradicts the `InformativeType` data:

* `A' : Sort 0` ⟹ (via `HasType.defeqU_l`) `A : Sort 0`, contradicting the first.
* `IsArityUpTo A'` ⟹ (via `IsArityUpTo.defeq`) `IsArityUpTo A`, contradicting the
  second. -/
theorem informativeType_not_erasable {env : VEnv} (henv : env.WF) {Us : List Name}
    {Δ : VLCtx} (hΔ : VLCtx.WF env Us.length Δ)
    {v : Expr} (info : InformativeType env Us Δ v)
    {ve : VExpr} (htr : TrExprS env Us Δ v ve) :
    ¬ Erasable env Us.length Δ.toCtx ve := by
  have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
  obtain ⟨ve₀, A, htr₀, hTA, hnotProp, hnotAr⟩ := info
  -- The two translations of `v` are defeq (type uniqueness for translations).
  have hvv : env.IsDefEqU Us.length Δ.toCtx ve₀ ve :=
    TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htr₀ htr
  -- Move the informative type witness onto `ve`: `HasType ve A`.
  have hTA_ve : env.HasType Us.length Δ.toCtx ve A := hTA.defeqU_l henv hΓ hvv
  rintro ⟨A', hTA', hcase⟩
  -- `A ≈ A'` by uniqueness of types.
  have hAA' : env.IsDefEqU Us.length Δ.toCtx A A' :=
    VEnv.IsDefEq.uniqU henv hΓ hTA_ve hTA'
  cases hcase with
  | inl hProp =>
      -- `A' : Sort 0` transports to `A : Sort 0`.
      exact hnotProp (hProp.defeqU_l henv hΓ (VEnv.IsDefEqU.symm hAA'))
  | inr hAr =>
      -- `IsArityUpTo A'` transports to `IsArityUpTo A`.
      exact hnotAr (hAr.defeq henv hΓ hAA')

/--
**A2 — first-order values are not erasable.** A first-order value's outermost
`InformativeType` field certifies its type is informative data, so by
`informativeType_not_erasable` it is neither a proof nor a type-former. -/
theorem firstOrderValue_not_erasable {env : VEnv} (henv : env.WF) {Us : List Name}
    {Γ : ErasureCtx} {Δ : VLCtx} (hΔ : VLCtx.WF env Us.length Δ)
    {v : Expr} (hfo : FirstOrderValue env Us Γ Δ v)
    {ve : VExpr} (htr : TrExprS env Us Δ v ve) :
    ¬ Erasable env Us.length Δ.toCtx ve := by
  obtain ⟨_, _, _, _, _, _, info, _⟩ := hfo
  exact informativeType_not_erasable henv hΔ info htr

/-! ## A3 — The erasure relation collapses to the function on first-order values

On a first-order value the non-deterministic relation `Erases` agrees with the
pure function `eraseCore`: inverting `Erases` on the constructor spine, the `box`
rule is *impossible* (A2), so the `ctor` rule is forced and the args recurse. We
deliver the function direction `Erases → eraseCore = .ok t` (the reverse,
`eraseCore → Erases`, is `eraseCore_refines`); together they give *equality* on
first-order values.

We first need fuel monotonicity of `eraseCore` (so the per-argument fuels can be
unified to a single bound), then A3 with an existentially-quantified fuel. -/

/-! ### Fuel monotonicity of `eraseCore` -/

/-- `eraseArgs` is monotone in its per-argument erasure callback: if `rec`
succeeding implies `rec'` succeeding with the same result, the spine erasure
transfers. -/
theorem eraseArgs_mono {rec rec' : Expr → Except String LBTerm}
    (hrec : ∀ a t, rec a = .ok t → rec' a = .ok t) :
    ∀ (args : List Expr) (head' t : LBTerm),
      eraseArgs rec head' args = .ok t → eraseArgs rec' head' args = .ok t := by
  intro args
  induction args with
  | nil => intro head' t h; simpa [eraseArgs] using h
  | cons a as ih =>
      intro head' t h
      simp only [eraseArgs] at h ⊢
      cases ha : rec a with
      | error e => rw [ha] at h; simp [bind, Except.bind] at h
      | ok a' =>
          rw [ha] at h; simp only [bind, Except.bind] at h
          rw [hrec a a' ha]; simp only [bind, Except.bind]
          exact ih (.app head' a') t h

/-- `List.mapM` of an erasure callback is monotone in the callback (same result). -/
theorem mapM_mono {rec rec' : Expr → Except String LBTerm}
    (hrec : ∀ a t, rec a = .ok t → rec' a = .ok t) :
    ∀ (args : List Expr) (args' : List LBTerm),
      args.mapM rec = .ok args' → args.mapM rec' = .ok args' := by
  intro args
  induction args with
  | nil => intro args' h; simpa using h
  | cons a as ih =>
      intro args' h
      rw [List.mapM_cons] at h ⊢
      cases ha : rec a with
      | error e => rw [ha] at h; simp [bind, Except.bind] at h
      | ok a' =>
          rw [ha] at h; simp only [bind, Except.bind] at h
          cases has : as.mapM rec with
          | error e => rw [has] at h; simp at h
          | ok as' =>
              rw [has] at h; simp only [pure, Except.pure] at h
              cases h
              rw [hrec a a' ha]; simp only [bind, Except.bind]
              rw [ih as' has]; simp [pure, Except.pure]

/-- Monotonicity of the spine worker `go` in the recursive callback fuel: under the
hypothesis `hrec` that bumping fuel preserves `eraseCore` successes, `go` at the
bumped fuel succeeds with the same result wherever it did at the lower fuel. By
structural induction on `head` (matching `go`'s recursion). -/
theorem go_mono {orc : Expr → Bool} {Γ : ErasureCtx} {fuel : Nat}
    (hrec : ∀ e t, eraseCore orc Γ fuel e = .ok t →
              eraseCore orc Γ (fuel + 1) e = .ok t) :
    ∀ (head : Expr) (acc : List Expr) (t : LBTerm),
      eraseCore.go orc Γ fuel head acc = .ok t →
      eraseCore.go orc Γ (fuel + 1) head acc = .ok t := by
  intro head
  induction head with
  | app f a ihf _iha =>
      intro acc t h; rw [eraseCore.go] at h ⊢; exact ihf (a :: acc) t h
  | const cn us =>
      intro acc t h
      rw [eraseCore.go] at h ⊢
      split at h
      · simp at h
      · split at h
        · rename_i iid cidx hctor
          simp only [Except.map] at h ⊢
          cases hmap : acc.mapM (fun a => eraseCore orc Γ fuel a) with
          | error e => rw [hmap] at h; simp at h
          | ok args' =>
              rw [hmap] at h; simp only at h
              rw [mapM_mono (fun a t ha => hrec a t ha) acc args' hmap]; simpa using h
        · rename_i hctor
          exact eraseArgs_mono (fun a t ha => hrec a t ha) acc
            (.const (Γ.constants cn)) t h
  | fvar x =>
      intro acc t h
      cases acc with
      | cons a as => simp only [eraseCore.go] at h; exact absurd h (by simp)
      | nil => rw [eraseCore.go] at h ⊢; exact h
  | bvar i =>
      intro acc t h
      cases acc with
      | cons a as => simp only [eraseCore.go] at h; exact absurd h (by simp)
      | nil => rw [eraseCore.go] at h ⊢; exact h
  | lam nm ty b bi _ihty _ihb =>
      intro acc t h
      cases acc with
      | cons a as => simp only [eraseCore.go] at h; exact absurd h (by simp)
      | nil =>
          rw [eraseCore.go] at h ⊢
          simp only [Except.map] at h ⊢
          cases hb : eraseCore orc Γ fuel b with
          | error e => rw [hb] at h; simp at h
          | ok b' => rw [hb] at h; rw [hrec b b' hb]; simpa using h
  | letE nm ty v b nd _ihty _ihv _ihb =>
      intro acc t h
      cases acc with
      | cons a as => simp only [eraseCore.go] at h; exact absurd h (by simp)
      | nil =>
          rw [eraseCore.go] at h ⊢
          cases hv : eraseCore orc Γ fuel v with
          | error e => rw [hv] at h; simp [bind, Except.bind] at h
          | ok v' =>
              rw [hv] at h; simp only [bind, Except.bind] at h
              cases hb : eraseCore orc Γ fuel b with
              | error e => rw [hb] at h; simp at h
              | ok b' =>
                  rw [hb] at h; simp only at h
                  rw [hrec v v' hv]; simp only [bind, Except.bind]
                  rw [hrec b b' hb]; simpa using h
  | sort u => intro acc t h; cases acc <;> (simp only [eraseCore.go] at h; exact absurd h (by simp))
  | mvar x => intro acc t h; cases acc <;> (simp only [eraseCore.go] at h; exact absurd h (by simp))
  | forallE nm ty b bi =>
      intro acc t h; cases acc <;> (simp only [eraseCore.go] at h; exact absurd h (by simp))
  | lit l => intro acc t h; cases acc <;> (simp only [eraseCore.go] at h; exact absurd h (by simp))
  | mdata m e => intro acc t h; cases acc <;> (simp only [eraseCore.go] at h; exact absurd h (by simp))
  | proj s i e => intro acc t h; cases acc <;> (simp only [eraseCore.go] at h; exact absurd h (by simp))

/-- **Fuel monotonicity of `eraseCore`.** Adding fuel never turns a success into a
failure (and preserves the result). By induction on `fuel`, using `go_mono`. -/
theorem eraseCore_mono {orc : Expr → Bool} {Γ : ErasureCtx} :
    ∀ (fuel : Nat) (e : Expr) (t : LBTerm),
      eraseCore orc Γ fuel e = .ok t → eraseCore orc Γ (fuel + 1) e = .ok t := by
  intro fuel
  induction fuel with
  | zero => intro e t h; simp only [eraseCore] at h; exact absurd h (by simp)
  | succ fuel ih =>
      intro e t h
      rw [eraseCore] at h ⊢
      split at h
      · rename_i horc; rw [if_pos horc]; exact h
      · rename_i horc; rw [if_neg horc]
        exact go_mono (fun e' t' h' => ih e' t' h') e [] t h

/-- Adding *any* amount of fuel preserves an `eraseCore` success. -/
theorem eraseCore_mono_le {orc : Expr → Bool} {Γ : ErasureCtx}
    {fuel fuel' : Nat} (hle : fuel ≤ fuel') {e : Expr} {t : LBTerm}
    (h : eraseCore orc Γ fuel e = .ok t) : eraseCore orc Γ fuel' e = .ok t := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hle
  clear hle
  induction d with
  | zero => simpa using h
  | succ d ih =>
      rw [show fuel + (d + 1) = (fuel + d) + 1 by omega]
      exact eraseCore_mono _ _ _ ih

/-! ### A3 proper -/

/-- `go` walks an application spine `args.foldl Expr.app head` by accumulating every
argument: it reduces to processing the bare `head` with the whole argument list
prepended to the accumulator. Proved by front-induction on `args`, generalizing the
head (each step peels the leading `.app` via `go`'s `.app` clause). -/
theorem go_spine {orc : Expr → Bool} {Γ : ErasureCtx} {fuel : Nat} :
    ∀ (args : List Expr) (head : Expr) (acc : List Expr),
      eraseCore.go orc Γ fuel (args.foldl Expr.app head) acc
        = eraseCore.go orc Γ fuel head (args ++ acc) := by
  intro args
  induction args with
  | nil => intro head acc; rfl
  | cons a as ih =>
      intro head acc
      rw [List.foldl_cons, ih (head.app a) acc, eraseCore.go]
      simp

/-- If each element of `args` erases successfully at a *common* fuel, then so does
the whole list under `mapM`, yielding a result list whose `i`-th entry is the `i`-th
element's erasure. -/
theorem mapM_firstorder {orc : Expr → Bool} {Γ : ErasureCtx} {fuel : Nat} :
    ∀ (args : List Expr),
      (∀ i (hi : i < args.length), ∃ a', eraseCore orc Γ fuel args[i] = .ok a') →
      ∃ args', args.mapM (fun a => eraseCore orc Γ fuel a) = .ok args' := by
  intro args
  induction args with
  | nil => intro _; exact ⟨[], by simp [pure, Except.pure]⟩
  | cons a as ih =>
      intro h
      obtain ⟨a', ha'⟩ := h 0 (by simp)
      simp only [List.getElem_cons_zero] at ha'
      obtain ⟨as', has'⟩ := ih (fun i hi => by
        have := h (i + 1) (by simpa using hi); simpa using this)
      refine ⟨a' :: as', ?_⟩
      rw [List.mapM_cons, ha']
      simp only [bind, Except.bind]
      rw [has']; simp [pure, Except.pure]

/-- The per-argument fuels can be unified: if each `args[i]` erases at *some* fuel,
there is a common fuel at which they all erase (the max, via `eraseCore_mono_le`). -/
theorem exists_uniform_fuel {orc : Expr → Bool} {Γ : ErasureCtx} :
    ∀ (args : List Expr),
      (∀ i (hi : i < args.length), ∃ fuel a', eraseCore orc Γ fuel args[i] = .ok a') →
      ∃ fuel, ∀ i (hi : i < args.length), ∃ a', eraseCore orc Γ fuel args[i] = .ok a' := by
  intro args
  induction args with
  | nil => intro _; exact ⟨0, fun i hi => absurd hi (by simp)⟩
  | cons a as ih =>
      intro h
      obtain ⟨f0, a', ha'⟩ := h 0 (by simp)
      simp only [List.getElem_cons_zero] at ha'
      obtain ⟨f1, hf1⟩ := ih (fun i hi => by
        have := h (i + 1) (by simpa using hi); simpa using this)
      refine ⟨max f0 f1, fun i hi => ?_⟩
      cases i with
      | zero =>
          exact ⟨a', eraseCore_mono_le (Nat.le_max_left _ _) (by simpa using ha')⟩
      | succ j =>
          obtain ⟨x, hx⟩ := hf1 j (by simpa using hi)
          exact ⟨x, eraseCore_mono_le (Nat.le_max_right _ _) (by simpa using hx)⟩

/--
**A3 — the erasure relation collapses to the function on first-order values.**

For a first-order value `v` (with a lean4lean translation `htr`), under the
trust-boundary `OracleSound`, the pure function `eraseCore` *succeeds* at some fuel
and lands on a term `t` that is *also* a valid `Erases` derivation (via
`eraseCore_refines`). Thus the relation and the function coincide on the canonical
(constructor-shaped) erasure of a first-order value — the content of MetaCoq's
`firstorder_erases_deterministic`.

**Why `OracleSound` is needed.** By A2 (`firstOrderValue_not_erasable`) a
first-order value is not `Erasable`, so `OracleSound` forbids `orc` from firing,
keeping `eraseCore` on the structural (`ctor`) branch rather than emitting `.box`.

**Honest scope (representational caveat).** The *literal* statement "`Erases v t →
eraseCore … v = .ok t`" (relation ⊆ function on the nose) is **false** for this
codebase's `Erases`, and deliberately so: Lean's `Expr.const` conflates data
constructors and ordinary definitions, so `Erases.const` can erase a constructor
head to `.const kn` and `Erases.app` can *curry* a constructor spine into
`.app … (.const kn)` — alternative results the function never produces. In MetaCoq
constructors are the *distinct* term former `tConstruct` (Fig. 16), so its erasure
relation has no such currying and the on-the-nose collapse holds. We therefore
deliver the genuinely-true core: the function's canonical constructor-shaped output
exists and is an `Erases` derivation; determinism *among constructor-shaped
derivations* then follows from `eraseCore`'s functionality. -/
theorem firstOrderValue_erases_eq_eraseCore {env : VEnv} (henv : env.WF)
    {Us : List Name} {Γ : ErasureCtx} {orc : Expr → Bool} (hos : OracleSound env Us orc)
    {Δ : VLCtx} (hΔ : VLCtx.WF env Us.length Δ)
    {v : Expr} (hfo : FirstOrderValue env Us Γ Δ v)
    {ve : VExpr} (htr : TrExprS env Us Δ v ve) :
    ∃ fuel t, eraseCore orc Γ fuel v = .ok t ∧ Erases env Us Γ Δ v t := by
  -- It suffices to show the function succeeds; `eraseCore_refines` gives `Erases`.
  suffices h : ∃ fuel t, eraseCore orc Γ fuel v = .ok t by
    obtain ⟨fuel, t, ht⟩ := h
    exact ⟨fuel, t, ht, eraseCore_refines hos htr ht⟩
  clear ve htr
  induction hfo with
  | @ctor cn us iid cidx args hc hcas info hargs ih =>
      -- The head node is not erasable (A2 core, directly from `info`), so `orc`
      -- cannot fire under `OracleSound`.
      have horc : orc (args.foldl Expr.app (.const cn us)) = false := by
        by_contra hb
        simp only [Bool.not_eq_false] at hb
        -- The `InformativeType` witness supplies a translation `htr₀`; the (now
        -- judgment-assuming) oracle then makes the value `Erasable`, contradicting
        -- that an informative-typed value is not erasable.
        have ⟨ve₀, _, htr₀, _, _, _⟩ := info
        exact informativeType_not_erasable henv hΔ info htr₀ (hos Δ _ ve₀ htr₀ hb)
      -- Each argument erases at some fuel; unify to a common fuel.
      obtain ⟨fuel, hfuel⟩ := exists_uniform_fuel args (fun i hi => ih i hi)
      obtain ⟨args', hmap⟩ := mapM_firstorder args hfuel
      -- Run `eraseCore (fuel+1)`: `orc` does not fire, `go` walks to the ctor head.
      refine ⟨fuel + 1, .construct iid cidx args', ?_⟩
      rw [eraseCore, if_neg (by simp [horc]), go_spine, List.append_nil,
        eraseCore.go, hcas, hc]
      simp only [Except.map, hmap]

/-! ## A4 — Function-level correctness on first-order results (β + δ fragment)

We chain A3 with the existing forward simulation to obtain the function-level
correctness corollary, and document precisely the honest scope. -/

/--
**Scope limitation of the in-scope β+δ evaluator.** Every value produced by
`SEvalβδ` is a λ-abstraction: the only base case is `SEvalβδ.lam`, and `beta`/`delta`
merely forward the value of a sub-evaluation. In particular `SEvalβδ` has **no**
constructor-value rule, so it can never produce a `FirstOrderValue` (a constructor
spine).

This is the precise reason the *literal* §7.4 statement
"`SEvalβδ e v → FirstOrderValue v → …`" has **jointly unsatisfiable** hypotheses
against the current `SEvalβδ`: the β+δ fragment (the only one for which
`erases_correct` is proved) does not evaluate constructors to values. The full ι /
constructor-value generality is out of scope — `SEvalβδ` deliberately omits the
constructor-value and `casesOn`/ι rules (which would need a recursor `IsDefEq` rule
the pinned lean4lean does not expose; see `SourceEval.lean`). We therefore deliver
A4 as a *function-level determinism* corollary that does **not** route the
first-order value through `SEvalβδ` (which cannot deliver it), avoiding a vacuous
theorem. -/
theorem sevalβδ_value_is_lam {E : SEnv} {e v : Expr} (h : SEvalβδ E e v) :
    ∃ n ty b bi, v = .lam n ty b bi := by
  induction h with
  | lam n ty b bi => exact ⟨n, ty, b, bi, rfl⟩
  | beta _ _ _ _ _ ih => exact ih
  | delta _ _ ih => exact ih

/--
**A4 — `erase_correct_firstorder` (function-level determinism on first-order
results, β+δ-grounded).**

The pure erasure function commutes with re-erasure on a first-order value: if `v`
is a first-order value and `t` is *any* `Erases`-image of `v` that is the canonical
constructor-shaped one produced by `eraseCore`, then `eraseCore` computes exactly
that `t` (so all such erasures coincide with the function's output). Concretely we
package: the function succeeds, lands on a term `t`, that `t` is an `Erases`
derivation, and — the determinism payoff — *any* fuel at which `eraseCore` succeeds
yields the same `t` (functionality of `eraseCore`).

**Honest scope (documented).**

* **Full ι / constructor-value generality is OUT OF SCOPE.** The pinned lean4lean
  exposes no recursor `IsDefEq` rule, so `SEvalβδ` (the evaluator `erases_correct`
  covers) has no constructor-value/ι rule and only produces λ-values
  (`sevalβδ_value_is_lam`). Hence we cannot obtain a first-order *result* by
  `SEvalβδ`-evaluation, and routing A4 through `SEvalβδ e v ∧ FirstOrderValue v`
  would be **vacuous**. We therefore state the function-level result directly on a
  first-order value.
* The β+δ-evaluable fragment that `erases_correct` *does* cover is exposed via
  `eraseCore_correct` (already in `EraseCore.lean`): for that fragment the source
  evaluates (to a λ-value) and the target `Eval`-uates compatibly. A4 is the
  complementary *constructor-result* determinism, which is `eraseCore`'s
  functionality combined with A3.
-/
theorem erase_correct_firstorder {env : VEnv} (henv : env.WF)
    {Us : List Name} {Γ : ErasureCtx} {orc : Expr → Bool} (hos : OracleSound env Us orc)
    {Δ : VLCtx} (hΔ : VLCtx.WF env Us.length Δ)
    {v : Expr} (hfo : FirstOrderValue env Us Γ Δ v)
    {ve : VExpr} (htr : TrExprS env Us Δ v ve) :
    ∃ (t : LBTerm),
      (∃ fuel, eraseCore orc Γ fuel v = .ok t) ∧
      Erases env Us Γ Δ v t ∧
      (∀ fuel' t', eraseCore orc Γ fuel' v = .ok t' → t' = t) := by
  obtain ⟨fuel, t, hok, her⟩ :=
    firstOrderValue_erases_eq_eraseCore henv hos hΔ hfo htr
  refine ⟨t, ⟨fuel, hok⟩, her, ?_⟩
  intro fuel' t' hok'
  -- Functionality of `eraseCore`: both fuels succeed; unify via monotonicity.
  have h1 : eraseCore orc Γ (max fuel fuel') v = .ok t :=
    eraseCore_mono_le (Nat.le_max_left _ _) hok
  have h2 : eraseCore orc Γ (max fuel fuel') v = .ok t' :=
    eraseCore_mono_le (Nat.le_max_right _ _) hok'
  rw [h1] at h2; injection h2 with h2; exact h2.symm

/-! ## Vacuity guards (mandatory non-vacuity demonstration)

A2/A3/A4 are hypothesis-bearing; we must show their premises are NOT jointly
refutable (unlike the deleted `BinderTrans`, which asserted a `TrExprS` of `.mvar`,
i.e. `False`). We do so with a **concrete** informative data inductive: an
environment `envFO` containing an axiom `I : Sort 1` (an informative type) and a
nullary "constructor" `c : I`, with `Γ`/`Δ` chosen so that `.const c []` is a
genuine `FirstOrderValue`.

**Honest residual (documented).** The single fact `¬ IsArityUpTo envFO 0 []
(.const I [])` — "`I` is not a type-former" — is *true* (a data inductive is not an
arity) but **not internally provable here**: refuting it needs
`¬ IsDefEqU (.const I []) (.sort u)` and `¬ IsDefEqU (.const I []) (.forallE …)`,
i.e. constructor-vs-(sort/forallE) defeq **injectivity**, which the pinned lean4lean
does NOT expose (`Theory/Typing/Injectivity.lean` provides only `sort_inv`,
`forallE_inv`, `sort_forallE_inv` — nothing for `.const`). The complementary
not-a-`Prop` fact `¬ HasType (.const I []) (.sort 0)` IS discharged below
(`envFO_notProp`, via `sort_inv`). We therefore expose the arity fact as the one
explicit hypothesis `harity`; everything else is fully constructed and proven, so
the premise bundle is satisfiable modulo this single clearly-true, lean4lean-blocked
side condition. This is a real, precisely-located gap, not a vacuity. -/

/-- Concrete environment: axiom `I : Sort 1`, axiom `c : I`. -/
noncomputable def envFO : VEnv :=
  ((((VEnv.empty.addConst `I ⟨0, .sort (.succ .zero)⟩).getD .empty).addConst `c
      ⟨0, .const `I []⟩).getD .empty)

theorem envFO_addI : VEnv.empty.addConst `I ⟨0, .sort (.succ .zero)⟩
    = some ((VEnv.empty.addConst `I ⟨0, .sort (.succ .zero)⟩).getD .empty) := by
  unfold VEnv.addConst VEnv.empty; simp
theorem envFO_addc :
    ((VEnv.empty.addConst `I ⟨0, .sort (.succ .zero)⟩).getD .empty).addConst `c
        ⟨0, .const `I []⟩ = some envFO := by
  unfold envFO VEnv.addConst VEnv.empty; simp

theorem envFO_I : envFO.constants `I = some ⟨0, .sort (.succ .zero)⟩ := by
  unfold envFO VEnv.addConst VEnv.empty; simp
theorem envFO_c : envFO.constants `c = some ⟨0, .const `I []⟩ := by
  unfold envFO VEnv.addConst VEnv.empty; simp
theorem env1FO_I :
    ((VEnv.empty.addConst `I ⟨0, .sort (.succ .zero)⟩).getD .empty).constants `I
      = some ⟨0, .sort (.succ .zero)⟩ := by
  unfold VEnv.addConst VEnv.empty; simp

/-- `envFO` is well-formed (two axioms). The `sorryAx` in `#print axioms` is
lean4lean's WF machinery — the documented trust boundary, not from this file. -/
theorem envFO_wf : envFO.WF := by
  have I_wf : VConstant.WF VEnv.empty ⟨0, .sort (.succ .zero)⟩ :=
    ⟨.succ (.succ .zero), VEnv.IsDefEq.sortDF (by trivial) (by trivial) (by rfl)⟩
  have c_wf : VConstant.WF ((VEnv.empty.addConst `I ⟨0, .sort (.succ .zero)⟩).getD .empty)
      ⟨0, .const `I []⟩ := by
    refine ⟨.succ .zero, ?_⟩
    have := VEnv.IsDefEq.constDF
      (env := (VEnv.empty.addConst `I ⟨0, .sort (.succ .zero)⟩).getD .empty)
      (uvars := 0) (Γ := []) (c := `I) (ci := ⟨0, .sort (.succ .zero)⟩)
      (ls := []) (ls' := []) env1FO_I (by simp) (by simp) (by simp) (by simp)
    exact this
  exact ⟨[.axiom ⟨⟨0, .const `I []⟩, `c⟩, .axiom ⟨⟨0, .sort (.succ .zero)⟩, `I⟩],
    .decl (.axiom c_wf envFO_addc) (.decl (.axiom I_wf envFO_addI) .empty)⟩

/-- `.const c []` translates (nullary constant). -/
theorem envFO_trC : TrExprS envFO [] [] (.const `c []) (.const `c []) :=
  .const envFO_c (by simp) (by simp)

/-- `.const c []` has type `.const I []` (the constructor's declared type). -/
theorem envFO_cTypeI : envFO.HasType 0 [] (.const `c []) (.const `I []) := by
  have := VEnv.IsDefEq.constDF (env := envFO) (uvars := 0) (Γ := []) (c := `c)
    (ci := ⟨0, .const `I []⟩) (ls := []) (ls' := []) envFO_c
    (by simp) (by simp) (by simp) (by simp)
  exact this

/-- `.const I []` (the value's type) has type `Sort 1`. -/
theorem envFO_ITypeSort1 : envFO.HasType 0 [] (.const `I []) (.sort (.succ .zero)) := by
  have := VEnv.IsDefEq.constDF (env := envFO) (uvars := 0) (Γ := []) (c := `I)
    (ci := ⟨0, .sort (.succ .zero)⟩) (ls := []) (ls' := []) envFO_I
    (by simp) (by simp) (by simp) (by simp)
  exact this

/-- The not-a-`Prop` half of informativeness IS dischargeable (via `sort_inv`): the
value's type `I : Sort 1`, so it is not typed by `Sort 0`. -/
theorem envFO_notProp : ¬ envFO.HasType 0 [] (.const `I []) (.sort .zero) := by
  intro h
  have huniq : envFO.IsDefEqU 0 [] (.sort .zero) (.sort (.succ .zero)) :=
    VEnv.IsDefEq.uniqU envFO_wf trivial h envFO_ITypeSort1
  have := VEnv.IsDefEqU.sort_inv envFO_wf trivial huniq
  rw [VLevel.equiv_def] at this; have := this []; simp [VLevel.eval] at this

/-- `InformativeType` for `.const c []`, modulo the one lean4lean-blocked arity
side condition `harity` (see section doc). -/
theorem envFO_informativeC (harity : ¬ IsArityUpTo envFO 0 [] (.const `I [])) :
    InformativeType envFO [] [] (.const `c []) :=
  ⟨.const `c [], .const `I [], envFO_trC, envFO_cTypeI, envFO_notProp, harity⟩

/-- The concrete erasure context: `c` is the (only) registered constructor, no
`casesOn`s. -/
def ΓFO : ErasureCtx where
  inductives := fun _ => none
  constants := toKername
  ctors := fun n => if n = `c then some (⟨toKername `I, 0⟩, 0) else none
  casesOns := fun _ => none

theorem ΓFO_ctorsC : ΓFO.ctors `c = some (⟨toKername `I, 0⟩, 0) := by unfold ΓFO; simp
theorem ΓFO_casesC : ΓFO.casesOns `c = none := rfl

/-- `.const c []` is a concrete `FirstOrderValue` (a nullary constructor whose type
is informative data), modulo the blocked arity side condition. -/
theorem envFO_foC (harity : ¬ IsArityUpTo envFO 0 [] (.const `I [])) :
    FirstOrderValue envFO [] ΓFO [] (.const `c []) := by
  have heq : (.const `c [] : Expr) = ([] : List Expr).foldl Expr.app (.const `c []) := rfl
  rw [heq]
  exact .ctor `c [] ⟨toKername `I, 0⟩ 0 ΓFO_ctorsC ΓFO_casesC
    (by simpa using envFO_informativeC harity) (fun i h => absurd h (by simp))

/-- **A2 is non-vacuous**: its premise bundle is jointly satisfiable (concretely, by
`envFO`/`Nat.zero`-style nullary constructor `c`), modulo the one blocked arity side
condition. Compare the refutable deleted `BinderTrans`. -/
theorem firstOrderValue_not_erasable_hyps_satisfiable
    (harity : ¬ IsArityUpTo envFO 0 [] (.const `I [])) :
    ∃ (env : VEnv) (Us : List Name) (Γ : ErasureCtx) (Δ : VLCtx) (v : Expr) (ve : VExpr),
      env.WF ∧ VLCtx.WF env Us.length Δ ∧ FirstOrderValue env Us Γ Δ v ∧
      TrExprS env Us Δ v ve :=
  ⟨envFO, [], ΓFO, [], .const `c [], .const `c [],
    envFO_wf, trivial, envFO_foC harity, envFO_trC⟩

/-- **A2 fires**: on the concrete first-order value it delivers real content — the
non-erasability of `.const c []`'s translation. -/
theorem firstOrderValue_not_erasable_fires
    (harity : ¬ IsArityUpTo envFO 0 [] (.const `I [])) :
    ¬ Erasable envFO 0 (VLCtx.toCtx []) (.const `c []) :=
  firstOrderValue_not_erasable envFO_wf (Us := []) (Δ := []) trivial
    (envFO_foC harity) envFO_trC

/-- **A3/A4 are non-vacuous**: the same concrete bundle (plus the always-`false`
oracle, which trivially satisfies `OracleSound`) jointly satisfies their premises,
and A3 *fires*, producing a real `eraseCore` success that refines `Erases`. -/
theorem firstOrderValue_erases_eq_eraseCore_fires
    (harity : ¬ IsArityUpTo envFO 0 [] (.const `I [])) :
    ∃ fuel t, eraseCore (fun _ => false) ΓFO fuel (.const `c []) = .ok t ∧
      Erases envFO [] ΓFO [] (.const `c []) t :=
  firstOrderValue_erases_eq_eraseCore envFO_wf (oracleSound_false envFO [])
    (Δ := []) trivial (envFO_foC harity) envFO_trC

/-! ## D0–D2 — uniqueness of the value-shaped (applied) erasure on first-order values

On a first-order value the erasure relation `Erases` retains *slack* only through the
`box` rule and the abstract block `ctor` rule. The A6 classification (`ctor_spine_inv`)
plus the first-order value's `InformativeType` (not erasable, A2) and the applied-form
(`NoBlock`) side condition kill both: the box-headed cuts require the value to be
`Erasable` (excluded), and the block cut is not `NoBlock`. What remains is the single
headcut (`mkApps (.construct iid cidx []) args'`), and its arguments are themselves
first-order values whose applied erasures are unique by induction. So the applied
erasure of a first-order value is **unique** — the relation collapses to a function
on the value-shaped (`NoBlock`) erasures.

`NoBlock` (applied form) is the operative "value-shaped" condition here: it is exactly
what the shipping / `eraseCore` produce, and — unlike the target `Value` predicate,
which admits λ-values whose bodies may hide a block — it is preserved down the
constructor spine (`noBlock_mkApps_inv`), which is what powers the induction. -/

/-- **D1 — uniqueness of the applied (`NoBlock`) erasure of a first-order value.** Any
two `NoBlock` erasures of a first-order value are equal: `Erases` has no slack on
value-shaped erasures. Uses A2 (`informativeType_not_erasable`) to kill the box cuts
and A6 (`ctor_spine_inv`) to force the headcut, recursing on the constructor
arguments. -/
theorem firstOrder_value_erases_unique {env : VEnv} (henv : env.WF) {Us : List Name}
    {Γ : ErasureCtx} {Δ : VLCtx} (hΔ : VLCtx.WF env Us.length Δ)
    {v : Expr} (hfo : FirstOrderValue env Us Γ Δ v) :
    ∀ {t1 t2 : LBTerm}, Erases env Us Γ Δ v t1 → NoBlock t1 →
      Erases env Us Γ Δ v t2 → NoBlock t2 → t1 = t2 := by
  induction hfo with
  | @ctor cn us iid cidx args hc hcas info hargs ih =>
    intro t1 t2 her1 hnb1 her2 hnb2
    obtain ⟨ve0, A0, htr0, hTA, hnp, hna⟩ := info
    have hinfo : InformativeType env Us Δ (args.foldl Expr.app (.const cn us)) :=
      ⟨ve0, A0, htr0, hTA, hnp, hna⟩
    have hne : ¬ Erasable env Us.length Δ.toCtx ve0 :=
      informativeType_not_erasable henv hΔ hinfo htr0
    have hcls1 := Erases.ctor_spine_inv henv hΔ hc hcas args.length args rfl htr0 her1
    have hcls2 := Erases.ctor_spine_inv henv hΔ hc hcas args.length args rfl htr0 her2
    rcases hcls1 with ⟨her, _⟩ | ⟨args'1, hlen1, rfl, hcorr1⟩ | hnbt1
    · exact absurd her hne
    · rcases hcls2 with ⟨her, _⟩ | ⟨args'2, hlen2, rfl, hcorr2⟩ | hnbt2
      · exact absurd her hne
      · have hlaws : args'1.length = args'2.length := by omega
        have hargeq : args'1 = args'2 := by
          apply List.ext_getElem hlaws
          intro i h1 _
          have hiA : i < args.length := hlen1 ▸ h1
          exact ih i hiA (hcorr1 i h1) (noBlock_mkApps_inv hnb1 _ (List.getElem_mem _))
            (hcorr2 i (by omega)) (noBlock_mkApps_inv hnb2 _ (List.getElem_mem _))
        rw [hargeq]
      · exact absurd hnb2 hnbt2
    · exact absurd hnb1 hnbt1

/-! ### Non-vacuity guards (D1 + A7) — a concrete nullary first-order constructor.

Reuses `envFO` (`I : Sort 1`, `c : I`) with the target env `EFOd` declaring `I` as a
data inductive with a nullary constructor `c` (arity `npars + nargs = 0`). All the
`erases_correct_data` env hypotheses hold concretely (the source-env ones vacuously,
`ErasesEnvCtor` by the arity computation), and both `firstOrder_value_erases_unique`
and `erases_correct_data` *fire* on `c`. -/

/-- `Γ` for the guard: registers `c` as the nullary constructor of `I`, arity `0`. -/
def ΓFOd : ErasureCtx where
  inductives := fun _ => none
  constants := toKername
  ctors := fun n => if n = `c then some (⟨toKername `I, 0⟩, 0) else none
  ctorArities := fun n => if n = `c then some 0 else none
  casesOns := fun _ => none

/-- Target env: `I` a data inductive with a single nullary constructor `c`. -/
def oibFOd : OneInductiveBody :=
  { name := "I", ctors := [{ name := "c", nargs := 0 }], projs := [] }
def mibFOd : MutualInductiveBody := { npars := 0, bodies := [oibFOd] }
def EFOd : GlobalDeclarations := [(toKername `I, .inductiveDecl mibFOd)]

theorem ΓFOd_ctorsC : ΓFOd.ctors `c = some (⟨toKername `I, 0⟩, 0) := by unfold ΓFOd; simp
theorem ΓFOd_ctorAritiesC : ΓFOd.ctorArities `c = some 0 := by unfold ΓFOd; simp
theorem ΓFOd_casesC : ΓFOd.casesOns `c = none := rfl
theorem EFOd_arity : constructorArity EFOd (⟨toKername `I, 0⟩) 0 = some 0 := by decide

/-- `ErasesEnvCtor` holds for the guard env. -/
theorem ΓFOd_envctor : ErasesEnvCtor ΓFOd EFOd := by
  intro cn iid cidx ar hc har
  by_cases h : cn = `c
  · subst h
    rw [ΓFOd_ctorsC] at hc; rw [ΓFOd_ctorAritiesC] at har
    simp only [Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    rw [EFOd_arity]; exact har
  · simp [ΓFOd, if_neg h] at hc

/-- `c`'s type `I` is a first-order value in `ΓFOd` (modulo the one lean4lean-blocked
arity side condition, as in `envFO_foC`). -/
theorem envFO_foC_d (harity : ¬ IsArityUpTo envFO 0 [] (.const `I [])) :
    FirstOrderValue envFO [] ΓFOd [] (.const `c []) := by
  have heq : (.const `c [] : Expr) = ([] : List Expr).foldl Expr.app (.const `c []) := rfl
  rw [heq]
  exact .ctor `c [] ⟨toKername `I, 0⟩ 0 ΓFOd_ctorsC ΓFOd_casesC
    (by simpa using envFO_informativeC harity) (fun i h => absurd h (by simp))

/-- **D1 fires**: the two `NoBlock` erasures of the nullary first-order value `c`
coincide (both are the applied nullary constructor). -/
theorem firstOrder_value_erases_unique_fires
    (harity : ¬ IsArityUpTo envFO 0 [] (.const `I [])) :
    (LBTerm.construct ⟨toKername `I, 0⟩ 0 []) = LBTerm.construct ⟨toKername `I, 0⟩ 0 [] :=
  firstOrder_value_erases_unique (Us := []) (Δ := []) envFO_wf trivial (envFO_foC_d harity)
    (.ctor_head `c [] _ 0 ΓFOd_ctorsC) trivial (.ctor_head `c [] _ 0 ΓFOd_ctorsC) trivial

/-- **A7 (`erases_correct_data`) is non-vacuous and fires**: the nullary constructor `c`
`SEvalDataC`-evaluates to itself, its applied erasure `.construct … []` evaluates
(`WcbvEval EFOd appliedFlags`) to a value erasing `c`. The source-env consistency
hypotheses hold vacuously (empty `Esrc`); `ErasesEnvCtor` holds by `ΓFOd_envctor`. -/
theorem erases_correct_data_fires :
    ∃ t' vve, WcbvEval EFOd appliedFlags (.construct ⟨toKername `I, 0⟩ 0 []) t' ∧
      TrExprS envFO [] [] (.const `c []) vve ∧
      Erases envFO [] ΓFOd [] (.const `c []) t' ∧ NoBlock t' ∧ NoFix t' := by
  refine erases_correct_data (env := envFO) envFO_wf (Us := []) (Δ := []) trivial
    (Esrc := fun _ => none) (E := EFOd) ?_ ?_ ΓFOd_envctor ?_ ?_
    (v := .const `c []) ?_ envFO_trC (.ctor_head `c [] _ 0 ΓFOd_ctorsC) trivial trivial
  · intro Δ n us body cve h; exact absurd h (by simp)
  · intro Δ n body h; exact absurd h (by simp)
  · intro cn iid cidx hc
    by_cases h : cn = `c
    · subst h; rfl
    · simp [ΓFOd, if_neg h] at hc
  · intro kn body' h; simp only [EFOd, LBTerm.envLookup] at h; split at h <;> simp_all
  · have heq : (.const `c [] : Expr) = ([] : List Expr).foldl Expr.app (.const `c []) := rfl
    rw [heq]
    exact .ctor_val ΓFOd_ctorsC ΓFOd_ctorAritiesC (by simp) rfl (fun i h => absurd h (by simp))
