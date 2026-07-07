import LeanToLambdaBox.Erasure

/-!
# Run-level reasoning for `EraseM` (verification infrastructure)

This file provides the reusable library for reasoning about *runs* of the
`EraseM` monad, in preparation for the "`visitExpr` refines `Erases`" bridge
proof, which will proceed by `Erasure.visitExpr.mutual_fixpoint_induct` over
the 18-function erasure family in `LeanToLambdaBox/Erasure.lean`.

## The run-application spelling

`EraseM := StateT ErasureState (ReaderT ErasureContext CoreM)`, and
`CoreM = ReaderT Core.Context (StateRefT' IO.RealWorld Core.State (EIO Exception))`
with `EIO ε = EST ε IO.RealWorld` and `EST ε σ α = Void σ → EST.Out ε σ α`.
An `x : EraseM α` is therefore run by applying it, step by step, to

* `s    : ErasureState`                    (the `StateT` layer),
* `ctx  : ErasureContext`                  (the `ReaderT` layer),
* `cctx : Core.Context`                    (`CoreM`'s `ReaderT` layer),
* `ref  : ST.Ref IO.RealWorld Core.State`  (the `StateRefT'` layer),
* `w    : Void IO.RealWorld`               (the `EST` world token),

yielding an `EST.Out Exception IO.RealWorld (α × ErasureState)`, whose success
shape is `.ok (r, s') w'`. **We deliberately do not wrap this application in a
`def`/`abbrev`**: `rw`/`cases`/keyed matching operate on the raw application
spine (head `Bind.bind`, `Pure.pure`, …), and a wrapper constant would make
lemma statements and goals disagree about the head symbol. The spelling
`x s ctx cctx ref w = .ok (r, s') w'` is the canonical form used by every
lemma in this file and should be used by all bridge motives.

## Contents

* **Run lemmas** (`run_pure`, `run_bind`, `run_bind_ok`, …): step through
  `do`-blocks under a `= .ok` hypothesis. `do`-notation match-compilation and
  smart unfolding can block raw `rfl`/`decide`-style reasoning at the `EST`
  layer; the (one-time) workaround — `cases h : <effect> …` + `show EST.bind …`
  + `unfold`/`rw` — is distilled into `run_bind`/`run_liftCoreM` so client
  proofs never fight it again.
* **Admissibility toolkit** (`eraseM_admissible_ok` & the arity variants):
  the canonical "on a successful run, `Q` holds" motive is
  `Lean.Order.admissible` for every function signature in the erasure family,
  as required by `partial_fixpoint`'s fixpoint induction.
* **Hoare-style loop rules** for `List.forIn'`/`forIn`, `Array.forIn`,
  `List.foldlM`/`Array.foldlM` and `List.mapM`: if an invariant holds
  initially and is preserved by every loop-body run, it holds of the result
  of a successful run of the whole loop. The `Array.forIn` rule also covers
  the parallel-`for` shape (`for x in xs, y in ys do …`), which elaborates to
  an `Array.forIn` whose accumulator threads the `Std.Stream` state of the
  second iterator: instantiate the invariant with a predicate on the
  (stream × state) accumulator (see the examples section).
* **Scale check** (`visitExpr_run_shape`): a real (if modest) property of all
  18 functions proved by `Erasure.visitExpr.mutual_fixpoint_induct`,
  confirming that the admissibility obligations discharge with the toolkit and
  that the step goals are tractable with the run lemmas at full scale.
-/

open Lean

namespace Erasure

/-! ## Run lemmas -/

section RunLemmas

variable {α β : Type}
variable (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
  (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld)

/-- Running `pure`. -/
theorem run_pure (a : α) :
    (pure a : EraseM α) s ctx cctx ref w = .ok (a, s) w := rfl

/-- Running a bind: run the first action, and on success feed value and state
to the continuation. This is the one place where the `EST`-layer match
compilation is fought by hand (`show EST.bind …` + `unfold`); everything else
composes by `rw`. -/
theorem run_bind (x : EraseM α) (f : α → EraseM β) :
    (x >>= f) s ctx cctx ref w =
      match x s ctx cctx ref w with
      | .ok (a, s₁) w₁ => f a s₁ ctx cctx ref w₁
      | .error e w₁ => .error e w₁ := by
  cases hx : x s ctx cctx ref w with
  | ok p w₁ =>
    obtain ⟨a, s₁⟩ := p
    show EST.bind (x s ctx cctx ref) _ w = _
    unfold EST.bind
    rw [hx]
  | error e w₁ =>
    show EST.bind (x s ctx cctx ref) _ w = _
    unfold EST.bind
    rw [hx]

/-- Inversion for a successful bind: there is a successful intermediate run.
This is the workhorse for stepping through `do`-blocks, including
`liftMetaM`-shaped or otherwise opaque actions (instantiate `x` with the
opaque action and learn nothing more than the existence of its result). -/
theorem run_bind_ok {x : EraseM α} {f : α → EraseM β} {b : β} {s' : ErasureState}
    {w' : Void IO.RealWorld} :
    (x >>= f) s ctx cctx ref w = .ok (b, s') w' ↔
      ∃ a s₁ w₁, x s ctx cctx ref w = .ok (a, s₁) w₁ ∧
        f a s₁ ctx cctx ref w₁ = .ok (b, s') w' := by
  rw [run_bind]
  cases hx : x s ctx cctx ref w with
  | ok p w₁ =>
    obtain ⟨a, s₁⟩ := p
    constructor
    · intro h; exact ⟨a, s₁, w₁, rfl, h⟩
    · rintro ⟨a', s₁', w₁', hx', hf⟩
      cases hx'
      exact hf
  | error e w₁ =>
    constructor
    · intro h; exact nomatch h
    · rintro ⟨a', s₁', w₁', hx', hf⟩
      exact nomatch hx'

/-- A bind whose continuation never succeeds never succeeds. -/
theorem run_bind_ne_ok {x : EraseM α} {f : α → EraseM β}
    (hf : ∀ a s₁ w₁ (b : β) s₂ w₂, f a s₁ ctx cctx ref w₁ ≠ .ok (b, s₂) w₂) :
    ∀ (b : β) s' w', (x >>= f) s ctx cctx ref w ≠ .ok (b, s') w' := by
  intro b s' w' h
  rw [run_bind_ok] at h
  obtain ⟨a, s₁, w₁, -, hcont⟩ := h
  exact hf a s₁ w₁ b s' w' hcont

/-- Running `get`. -/
theorem run_get :
    (get : EraseM ErasureState) s ctx cctx ref w = .ok (s, s) w := rfl

/-- Running `set`. -/
theorem run_set (s₀ : ErasureState) :
    (set s₀ : EraseM Unit) s ctx cctx ref w = .ok ((), s₀) w := rfl

/-- Running `modify`. -/
theorem run_modify (g : ErasureState → ErasureState) :
    (modify g : EraseM Unit) s ctx cctx ref w = .ok ((), g s) w := rfl

/-- Running `modifyGet`. -/
theorem run_modifyGet (g : ErasureState → α × ErasureState) :
    (modifyGet g : EraseM α) s ctx cctx ref w = .ok (g s) w := rfl

/-- Running `read` (the `ErasureContext` reader layer). The inner
`Core.Context` layer is not directly readable in `EraseM` (no
`MonadReaderOf Core.Context EraseM` instance); it is reached only through
lifted `CoreM` actions, i.e. through `run_liftCoreM`. -/
theorem run_read :
    (read : EraseM ErasureContext) s ctx cctx ref w = .ok (ctx, s) w := rfl

/-- Running `withReader`: same computation under the modified context. -/
theorem run_withReader (f : ErasureContext → ErasureContext) (x : EraseM α) :
    (withReader f x : EraseM α) s ctx cctx ref w = x s (f ctx) cctx ref w := rfl

/-- Running `throw`. -/
theorem run_throw (e : Exception) :
    (throw e : EraseM α) s ctx cctx ref w = .error e w := rfl

/-- `throw` never succeeds. -/
theorem run_throw_ne_ok (e : Exception) :
    ∀ (b : α) s' w', (throw e : EraseM α) s ctx cctx ref w ≠ .ok (b, s') w' := by
  intro b s' w' h
  rw [run_throw] at h
  exact nomatch h

/-- `throwError` never succeeds (it is `getRef`/`addMessageContext` binds
ending in a `throw`; the intermediate actions are treated as opaque). -/
theorem run_throwError_ne_ok (msg : MessageData) :
    ∀ (b : α) s' w', (throwError msg : EraseM α) s ctx cctx ref w ≠ .ok (b, s') w' := by
  unfold Lean.throwError
  apply run_bind_ne_ok
  intro a s₁ w₁
  apply run_bind_ne_ok
  intro p s₂ w₂
  obtain ⟨r, m⟩ := p
  exact run_throw_ne_ok s₂ ctx cctx ref w₂ _

/-- Running a lifted `CoreM` action: the `ErasureState` is threaded through
unchanged. In the elaborated erasure family this covers actions that appear
as literal `liftM …` (e.g. `Compiler.LCNF.getDeclInfo?`); library actions
elaborated *at* `EraseM` (e.g. `getConstInfo`) are instead handled opaquely
via `run_bind_ok`. -/
theorem run_liftCoreM (x : CoreM α) :
    (liftM x : EraseM α) s ctx cctx ref w =
      match x cctx ref w with
      | .ok a w₁ => .ok (a, s) w₁
      | .error e w₁ => .error e w₁ := by
  cases hx : x cctx ref w with
  | ok a w₁ =>
    show EST.bind (x cctx ref) _ w = _
    unfold EST.bind
    rw [hx]
    rfl
  | error e w₁ =>
    show EST.bind (x cctx ref) _ w = _
    unfold EST.bind
    rw [hx]

/-- Success inversion for a lifted `CoreM` action. -/
theorem run_liftCoreM_ok {x : CoreM α} {a : α} {s₁ : ErasureState} {w₁ : Void IO.RealWorld} :
    (liftM x : EraseM α) s ctx cctx ref w = .ok (a, s₁) w₁ ↔
      x cctx ref w = .ok a w₁ ∧ s₁ = s := by
  rw [run_liftCoreM]
  cases hx : x cctx ref w with
  | ok b w₂ =>
    constructor
    · intro h; cases h; exact ⟨rfl, rfl⟩
    · rintro ⟨hx', rfl⟩; cases hx'; rfl
  | error e w₂ =>
    constructor
    · intro h; exact nomatch h
    · rintro ⟨hx', rfl⟩; exact nomatch hx'

/-- Lifted `CoreM` actions do not change the `ErasureState`. -/
theorem run_liftCoreM_state {x : CoreM α} {a : α} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (h : (liftM x : EraseM α) s ctx cctx ref w = .ok (a, s₁) w₁) : s₁ = s :=
  ((run_liftCoreM_ok s ctx cctx ref w).mp h).2

/-- Running `liftMetaM x`: run the `MetaM` action in `CoreM` with the local
context taken from the `ErasureContext`; the `ErasureState` is unchanged. -/
theorem run_liftMetaM (x : MetaM α) :
    liftMetaM x s ctx cctx ref w =
      match (x.run' { lctx := ctx.lctx } : CoreM α) cctx ref w with
      | .ok a w₁ => .ok (a, s) w₁
      | .error e w₁ => .error e w₁ := by
  unfold liftMetaM
  rw [run_bind, run_read]
  exact run_liftCoreM s ctx cctx ref w _

/-- Success inversion for `liftMetaM`. -/
theorem run_liftMetaM_ok {x : MetaM α} {a : α} {s₁ : ErasureState} {w₁ : Void IO.RealWorld} :
    liftMetaM x s ctx cctx ref w = .ok (a, s₁) w₁ ↔
      (x.run' { lctx := ctx.lctx } : CoreM α) cctx ref w = .ok a w₁ ∧ s₁ = s := by
  rw [run_liftMetaM]
  cases hx : (x.run' { lctx := ctx.lctx } : CoreM α) cctx ref w with
  | ok b w₂ =>
    constructor
    · intro h; cases h; exact ⟨rfl, rfl⟩
    · rintro ⟨hx', rfl⟩; cases hx'; rfl
  | error e w₂ =>
    constructor
    · intro h; exact nomatch h
    · rintro ⟨hx', rfl⟩; exact nomatch hx'

/-- `liftMetaM` does not change the `ErasureState`. -/
theorem run_liftMetaM_state {x : MetaM α} {a : α} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (h : liftMetaM x s ctx cctx ref w = .ok (a, s₁) w₁) : s₁ = s :=
  ((run_liftMetaM_ok s ctx cctx ref w).mp h).2

/-- Running `panic`: with the `instInhabitedOfMonad` instance that
`panic!`/`unreachable!` pick up at type `EraseM α`, a panic **succeeds** and
returns `default : α` with the state unchanged (it does *not* throw). -/
theorem run_panic [Inhabited α] (msg : String) :
    (panic msg : EraseM α) s ctx cctx ref w = .ok (default, s) w := rfl

/-- Running the elaborated form of `panic!`/`unreachable!` (as it appears in
the erasure family's bodies). -/
theorem run_panicWithPosWithDecl [Inhabited α] (mod decl : String) (line col : Nat)
    (msg : String) :
    (panicWithPosWithDecl mod decl line col msg : EraseM α) s ctx cctx ref w
      = .ok (default, s) w := rfl

end RunLemmas

/-! ## Admissibility toolkit -/

section Admissibility

open Lean.Order

/-- Admissibility of the run-ok motive at the `EST` leaf, for a single result
value. The proof works over the underlying `∀ w, FlatOrder (EST.bot w)`
pi-CCPO, to which `EST`'s own `CCPO` instance is definitionally equal; at the
flat order, the motive holds at bottom because `EST.bot` is an `.error`. -/
theorem est_admissible_ok {ε σ α : Type} [Nonempty ε]
    (Q : Void σ → α → Void σ → Prop) :
    admissible (α := EST ε σ α) (fun x => ∀ w a w', x w = .ok a w' → Q w a w') := by
  have h : admissible (α := (w : Void σ) → FlatOrder (EST.bot (ε := ε) w))
      (fun x => ∀ w a w', x w = .ok a w' → Q w a w') := by
    apply admissible_pi_apply
      (P := fun w (v : FlatOrder (EST.bot w)) => ∀ a w', v = .ok a w' → Q w a w')
    intro w
    apply admissible_pi; intro a
    apply admissible_pi; intro w'
    apply admissible_flatOrder
    intro h
    simp [EST.bot] at h
  exact h

/-- Admissibility of the run-ok motive at the `EST` leaf, with the result
split as a pair — the shape produced by running the `StateT` layer. -/
theorem est_admissible_ok_pair {ε σ : Type} [Nonempty ε] {α β : Type}
    (Q : Void σ → α → β → Void σ → Prop) :
    admissible (α := EST ε σ (α × β))
      (fun x => ∀ w a b w', x w = .ok (a, b) w' → Q w a b w') := by
  have h : admissible (α := (w : Void σ) → FlatOrder (EST.bot (ε := ε) w))
      (fun x => ∀ w a b w', x w = .ok (a, b) w' → Q w a b w') := by
    apply admissible_pi_apply
      (P := fun w (v : FlatOrder (EST.bot w)) => ∀ a b w', v = .ok (a, b) w' → Q w a b w')
    intro w
    apply admissible_pi; intro a
    apply admissible_pi; intro b
    apply admissible_pi; intro w'
    apply admissible_flatOrder
    intro h
    simp [EST.bot] at h
  exact h

/-- The canonical bridge motive is admissible for any `EraseM τ` computation:
"whenever the run succeeds, `Q` holds of inputs and outputs". The proof peels
the transformer stack layer by layer with `admissible_pi_apply`; the explicit
`P` at each layer matters — bare `apply` fails higher-order unification. -/
theorem eraseM_admissible_ok {τ : Type}
    (Q : ErasureState → ErasureContext → Core.Context → ST.Ref IO.RealWorld Core.State →
      Void IO.RealWorld → τ → ErasureState → Void IO.RealWorld → Prop) :
    admissible (α := EraseM τ)
      (fun x => ∀ s ctx cctx ref w r s' w',
        x s ctx cctx ref w = .ok (r, s') w' → Q s ctx cctx ref w r s' w') := by
  apply admissible_pi_apply
    (P := fun (s : ErasureState) (g : ReaderT ErasureContext CoreM (τ × ErasureState)) =>
      ∀ ctx cctx ref w r s' w', g ctx cctx ref w = .ok (r, s') w' → Q s ctx cctx ref w r s' w')
  intro s
  apply admissible_pi_apply
    (P := fun (ctx : ErasureContext) (g : CoreM (τ × ErasureState)) =>
      ∀ cctx ref w r s' w', g cctx ref w = .ok (r, s') w' → Q s ctx cctx ref w r s' w')
  intro ctx
  apply admissible_pi_apply
    (P := fun (cctx : Core.Context)
        (g : StateRefT' IO.RealWorld Core.State (EIO Exception) (τ × ErasureState)) =>
      ∀ ref w r s' w', g ref w = .ok (r, s') w' → Q s ctx cctx ref w r s' w')
  intro cctx
  apply admissible_pi_apply
    (P := fun (ref : ST.Ref IO.RealWorld Core.State) (g : EIO Exception (τ × ErasureState)) =>
      ∀ w r s' w', g w = .ok (r, s') w' → Q s ctx cctx ref w r s' w')
  intro ref
  exact est_admissible_ok_pair (fun w r s' w' => Q s ctx cctx ref w r s' w')

/-- Canonical motive admissibility for a 1-argument family member
(`visitExpr`, `visitLiteral`, `visitConst`, `get_constant_kername`,
`visitMutual`, `visitLet`, `visitLambda`, `visitApp`, `visitConstApp`). -/
theorem eraseM_admissible_ok₁ {γ₁ τ : Type}
    (Q : γ₁ → ErasureState → ErasureContext → Core.Context → ST.Ref IO.RealWorld Core.State →
      Void IO.RealWorld → τ → ErasureState → Void IO.RealWorld → Prop) :
    admissible (α := γ₁ → EraseM τ)
      (fun f => ∀ a₁ s ctx cctx ref w r s' w',
        f a₁ s ctx cctx ref w = .ok (r, s') w' → Q a₁ s ctx cctx ref w r s' w') := by
  apply admissible_pi_apply
    (P := fun (a₁ : γ₁) (g : EraseM τ) =>
      ∀ s ctx cctx ref w r s' w', g s ctx cctx ref w = .ok (r, s') w' →
        Q a₁ s ctx cctx ref w r s' w')
  intro a₁
  exact eraseM_admissible_ok (Q a₁)

/-- Canonical motive admissibility, 2 arguments (`visitConstructor`,
`visitAppArgs`, `visitCasesEta`, `visitCases`). -/
theorem eraseM_admissible_ok₂ {γ₁ γ₂ τ : Type}
    (Q : γ₁ → γ₂ → ErasureState → ErasureContext → Core.Context →
      ST.Ref IO.RealWorld Core.State → Void IO.RealWorld → τ → ErasureState →
      Void IO.RealWorld → Prop) :
    admissible (α := γ₁ → γ₂ → EraseM τ)
      (fun f => ∀ a₁ a₂ s ctx cctx ref w r s' w',
        f a₁ a₂ s ctx cctx ref w = .ok (r, s') w' → Q a₁ a₂ s ctx cctx ref w r s' w') := by
  apply admissible_pi_apply
    (P := fun (a₁ : γ₁) (g : γ₂ → EraseM τ) =>
      ∀ a₂ s ctx cctx ref w r s' w', g a₂ s ctx cctx ref w = .ok (r, s') w' →
        Q a₁ a₂ s ctx cctx ref w r s' w')
  intro a₁
  exact eraseM_admissible_ok₁ (Q a₁)

/-- Canonical motive admissibility, 3 arguments (`visitProj`, `visitCtorEta`,
`visitAlt`). -/
theorem eraseM_admissible_ok₃ {γ₁ γ₂ γ₃ τ : Type}
    (Q : γ₁ → γ₂ → γ₃ → ErasureState → ErasureContext → Core.Context →
      ST.Ref IO.RealWorld Core.State → Void IO.RealWorld → τ → ErasureState →
      Void IO.RealWorld → Prop) :
    admissible (α := γ₁ → γ₂ → γ₃ → EraseM τ)
      (fun f => ∀ a₁ a₂ a₃ s ctx cctx ref w r s' w',
        f a₁ a₂ a₃ s ctx cctx ref w = .ok (r, s') w' →
          Q a₁ a₂ a₃ s ctx cctx ref w r s' w') := by
  apply admissible_pi_apply
    (P := fun (a₁ : γ₁) (g : γ₂ → γ₃ → EraseM τ) =>
      ∀ a₂ a₃ s ctx cctx ref w r s' w', g a₂ a₃ s ctx cctx ref w = .ok (r, s') w' →
        Q a₁ a₂ a₃ s ctx cctx ref w r s' w')
  intro a₁
  exact eraseM_admissible_ok₂ (Q a₁)

set_option synthInstance.maxSize 512 in
/-- Canonical motive admissibility, 4 arguments (`visitCasesEtaGo`). -/
theorem eraseM_admissible_ok₄ {γ₁ γ₂ γ₃ γ₄ τ : Type}
    (Q : γ₁ → γ₂ → γ₃ → γ₄ → ErasureState → ErasureContext → Core.Context →
      ST.Ref IO.RealWorld Core.State → Void IO.RealWorld → τ → ErasureState →
      Void IO.RealWorld → Prop) :
    admissible (α := γ₁ → γ₂ → γ₃ → γ₄ → EraseM τ)
      (fun f => ∀ a₁ a₂ a₃ a₄ s ctx cctx ref w r s' w',
        f a₁ a₂ a₃ a₄ s ctx cctx ref w = .ok (r, s') w' →
          Q a₁ a₂ a₃ a₄ s ctx cctx ref w r s' w') := by
  apply admissible_pi_apply
    (P := fun (a₁ : γ₁) (g : γ₂ → γ₃ → γ₄ → EraseM τ) =>
      ∀ a₂ a₃ a₄ s ctx cctx ref w r s' w', g a₂ a₃ a₄ s ctx cctx ref w = .ok (r, s') w' →
        Q a₁ a₂ a₃ a₄ s ctx cctx ref w r s' w')
  intro a₁
  exact eraseM_admissible_ok₃ (Q a₁)

set_option synthInstance.maxSize 512 in
/-- Canonical motive admissibility, 5 arguments (`visitCtorEtaGo`). -/
theorem eraseM_admissible_ok₅ {γ₁ γ₂ γ₃ γ₄ γ₅ τ : Type}
    (Q : γ₁ → γ₂ → γ₃ → γ₄ → γ₅ → ErasureState → ErasureContext → Core.Context →
      ST.Ref IO.RealWorld Core.State → Void IO.RealWorld → τ → ErasureState →
      Void IO.RealWorld → Prop) :
    admissible (α := γ₁ → γ₂ → γ₃ → γ₄ → γ₅ → EraseM τ)
      (fun f => ∀ a₁ a₂ a₃ a₄ a₅ s ctx cctx ref w r s' w',
        f a₁ a₂ a₃ a₄ a₅ s ctx cctx ref w = .ok (r, s') w' →
          Q a₁ a₂ a₃ a₄ a₅ s ctx cctx ref w r s' w') := by
  apply admissible_pi_apply
    (P := fun (a₁ : γ₁) (g : γ₂ → γ₃ → γ₄ → γ₅ → EraseM τ) =>
      ∀ a₂ a₃ a₄ a₅ s ctx cctx ref w r s' w',
        g a₂ a₃ a₄ a₅ s ctx cctx ref w = .ok (r, s') w' →
          Q a₁ a₂ a₃ a₄ a₅ s ctx cctx ref w r s' w')
  intro a₁
  exact eraseM_admissible_ok₄ (Q a₁)

end Admissibility

/-! ## Hoare-style loop rules -/

section LoopRules

variable {γ β : Type}
variable (ctx : ErasureContext) (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)

/-- Hoare rule for `forIn'` over a `List`: an invariant `P` on
(accumulator, state, world) that holds initially and is preserved by every
successful body run (whether it `.yield`s or `.done`s) holds of the result of
a successful run of the loop. The body hypothesis additionally provides
membership of the element in the list. -/
theorem run_list_forIn'_ok (P : β → ErasureState → Void IO.RealWorld → Prop) :
    ∀ (l : List γ) (f : (a : γ) → a ∈ l → β → EraseM (ForInStep β)) (init : β)
      (s : ErasureState) (w : Void IO.RealWorld),
      P init s w →
      (∀ a (h : a ∈ l) acc s₁ w₁ st s₂ w₂, P acc s₁ w₁ →
        f a h acc s₁ ctx cctx ref w₁ = .ok (st, s₂) w₂ → P st.value s₂ w₂) →
      ∀ r s' w', forIn' l init f s ctx cctx ref w = .ok (r, s') w' → P r s' w' := by
  intro l
  induction l with
  | nil =>
    intro f init s w hinit _ r s' w' hrun
    rw [List.forIn'_nil, run_pure] at hrun
    cases hrun
    exact hinit
  | cons a as ih =>
    intro f init s w hinit hstep r s' w' hrun
    rw [List.forIn'_cons, run_bind_ok] at hrun
    obtain ⟨st, s₁, w₁, hf, hcont⟩ := hrun
    have hP := hstep a List.mem_cons_self init s w st s₁ w₁ hinit hf
    cases st with
    | done b =>
      have hcont' : (pure b : EraseM β) s₁ ctx cctx ref w₁ = .ok (r, s') w' := hcont
      rw [run_pure] at hcont'
      cases hcont'
      exact hP
    | yield b =>
      have hcont' : forIn' as b (fun a' m b => f a' (List.mem_cons_of_mem a m) b)
          s₁ ctx cctx ref w₁ = .ok (r, s') w' := hcont
      exact ih (fun a' m b => f a' (List.mem_cons_of_mem a m) b) b s₁ w₁ hP
        (fun a' h' acc s₂ w₂ st' s₃ w₃ hPa hfa =>
          hstep a' (List.mem_cons_of_mem a h') acc s₂ w₂ st' s₃ w₃ hPa hfa)
        r s' w' hcont'

/-- Hoare rule for `forIn` over a `List` (the shape produced by
`for x in (l : List _) do …`). -/
theorem run_list_forIn_ok (P : β → ErasureState → Void IO.RealWorld → Prop) :
    ∀ (l : List γ) (f : γ → β → EraseM (ForInStep β)) (init : β)
      (s : ErasureState) (w : Void IO.RealWorld),
      P init s w →
      (∀ a, a ∈ l → ∀ acc s₁ w₁ st s₂ w₂, P acc s₁ w₁ →
        f a acc s₁ ctx cctx ref w₁ = .ok (st, s₂) w₂ → P st.value s₂ w₂) →
      ∀ r s' w', forIn l init f s ctx cctx ref w = .ok (r, s') w' → P r s' w' := by
  intro l
  induction l with
  | nil =>
    intro f init s w hinit _ r s' w' hrun
    rw [List.forIn_nil, run_pure] at hrun
    cases hrun
    exact hinit
  | cons a as ih =>
    intro f init s w hinit hstep r s' w' hrun
    rw [List.forIn_cons, run_bind_ok] at hrun
    obtain ⟨st, s₁, w₁, hf, hcont⟩ := hrun
    have hP := hstep a List.mem_cons_self init s w st s₁ w₁ hinit hf
    cases st with
    | done b =>
      have hcont' : (pure b : EraseM β) s₁ ctx cctx ref w₁ = .ok (r, s') w' := hcont
      rw [run_pure] at hcont'
      cases hcont'
      exact hP
    | yield b =>
      have hcont' : forIn as b f s₁ ctx cctx ref w₁ = .ok (r, s') w' := hcont
      exact ih f b s₁ w₁ hP
        (fun a' h' => hstep a' (List.mem_cons_of_mem a h'))
        r s' w' hcont'

/-- Hoare rule for `forIn` over an `Array` (the shape produced by
`for x in (xs : Array _) do …`, including the parallel-`for` shape, whose
accumulator threads the `Std.Stream` state of the further iterators). -/
theorem run_array_forIn_ok (P : β → ErasureState → Void IO.RealWorld → Prop)
    (as : Array γ) (f : γ → β → EraseM (ForInStep β)) (init : β)
    (s : ErasureState) (w : Void IO.RealWorld)
    (hinit : P init s w)
    (hstep : ∀ a, a ∈ as → ∀ acc s₁ w₁ st s₂ w₂, P acc s₁ w₁ →
      f a acc s₁ ctx cctx ref w₁ = .ok (st, s₂) w₂ → P st.value s₂ w₂) :
    ∀ r s' w', forIn as init f s ctx cctx ref w = .ok (r, s') w' → P r s' w' := by
  intro r s' w' hrun
  rw [← Array.forIn_toList] at hrun
  exact run_list_forIn_ok ctx cctx ref P as.toList f init s w hinit
    (fun a ha => hstep a (Array.mem_toList_iff.mp ha)) r s' w' hrun

/-- Auxiliary induction for `run_list_foldlM_ok`, generalized over the
processed prefix. -/
theorem run_list_foldlM_ok_go (g : β → γ → EraseM β) (L : List γ)
    (P : List γ → β → ErasureState → Void IO.RealWorld → Prop)
    (hstep : ∀ pre x post acc s₁ w₁ acc' s₂ w₂, L = pre ++ x :: post →
      P pre acc s₁ w₁ → g acc x s₁ ctx cctx ref w₁ = .ok (acc', s₂) w₂ →
      P (pre ++ [x]) acc' s₂ w₂) :
    ∀ (todo pre : List γ), L = pre ++ todo →
      ∀ acc s₁ w₁, P pre acc s₁ w₁ →
      ∀ r s' w', List.foldlM g acc todo s₁ ctx cctx ref w₁ = .ok (r, s') w' →
      P L r s' w' := by
  intro todo
  induction todo with
  | nil =>
    intro pre hL acc s₁ w₁ hP r s' w' hrun
    rw [List.foldlM_nil, run_pure] at hrun
    cases hrun
    simpa [hL] using hP
  | cons x todo ih =>
    intro pre hL acc s₁ w₁ hP r s' w' hrun
    rw [List.foldlM_cons, run_bind_ok] at hrun
    obtain ⟨acc', s₂, w₂, hg, hrest⟩ := hrun
    have hP' := hstep pre x todo acc s₁ w₁ acc' s₂ w₂ hL hP hg
    exact ih (pre ++ [x]) (by rw [List.append_assoc, List.singleton_append]; exact hL)
      acc' s₂ w₂ hP' r s' w' hrest

/-- Hoare rule for `List.foldlM`, with the invariant indexed by the processed
prefix (so the step hypothesis knows *which* element is being processed and
that it comes from the list). -/
theorem run_list_foldlM_ok {g : β → γ → EraseM β} {L : List γ} {init : β}
    {s : ErasureState} {w : Void IO.RealWorld}
    (P : List γ → β → ErasureState → Void IO.RealWorld → Prop)
    (hinit : P [] init s w)
    (hstep : ∀ pre x post acc s₁ w₁ acc' s₂ w₂, L = pre ++ x :: post →
      P pre acc s₁ w₁ → g acc x s₁ ctx cctx ref w₁ = .ok (acc', s₂) w₂ →
      P (pre ++ [x]) acc' s₂ w₂)
    {r : β} {s' : ErasureState} {w' : Void IO.RealWorld}
    (hrun : List.foldlM g init L s ctx cctx ref w = .ok (r, s') w') :
    P L r s' w' :=
  run_list_foldlM_ok_go ctx cctx ref g L P hstep L [] rfl init s w hinit r s' w' hrun

/-- Hoare rule for `Array.foldlM` (the `visitAppArgs` shape), phrased on
`as.toList` so the prefix-indexed invariant of `run_list_foldlM_ok` carries
over unchanged. -/
theorem run_array_foldlM_ok {g : β → γ → EraseM β} {as : Array γ} {init : β}
    {s : ErasureState} {w : Void IO.RealWorld}
    (P : List γ → β → ErasureState → Void IO.RealWorld → Prop)
    (hinit : P [] init s w)
    (hstep : ∀ pre x post acc s₁ w₁ acc' s₂ w₂, as.toList = pre ++ x :: post →
      P pre acc s₁ w₁ → g acc x s₁ ctx cctx ref w₁ = .ok (acc', s₂) w₂ →
      P (pre ++ [x]) acc' s₂ w₂)
    {r : β} {s' : ErasureState} {w' : Void IO.RealWorld}
    (hrun : (as.foldlM g init : EraseM β) s ctx cctx ref w = .ok (r, s') w') :
    P as.toList r s' w' := by
  rw [← Array.foldlM_toList] at hrun
  exact run_list_foldlM_ok ctx cctx ref P hinit hstep hrun

/-- Auxiliary induction for `run_list_mapM_ok` over `List.mapM.loop`, whose
accumulator holds the produced outputs in reverse. -/
theorem run_list_mapM_ok_go (f : γ → EraseM β) (L : List γ)
    (P : List γ → List β → ErasureState → Void IO.RealWorld → Prop)
    (hstep : ∀ pre x post outs s₁ w₁ b s₂ w₂, L = pre ++ x :: post →
      P pre outs s₁ w₁ → f x s₁ ctx cctx ref w₁ = .ok (b, s₂) w₂ →
      P (pre ++ [x]) (outs ++ [b]) s₂ w₂) :
    ∀ (todo pre : List γ) (acc : List β), L = pre ++ todo →
      ∀ s₁ w₁, P pre acc.reverse s₁ w₁ →
      ∀ rs s' w', List.mapM.loop f todo acc s₁ ctx cctx ref w₁ = .ok (rs, s') w' →
      P L rs s' w' := by
  intro todo
  induction todo with
  | nil =>
    intro pre acc hL s₁ w₁ hP rs s' w' hrun
    unfold List.mapM.loop at hrun
    rw [run_pure] at hrun
    cases hrun
    simpa [hL] using hP
  | cons x todo ih =>
    intro pre acc hL s₁ w₁ hP rs s' w' hrun
    unfold List.mapM.loop at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨b, s₂, w₂, hf, hrest⟩ := hrun
    have hP' := hstep pre x todo acc.reverse s₁ w₁ b s₂ w₂ hL hP hf
    have hrev : P (pre ++ [x]) (b :: acc).reverse s₂ w₂ := by
      simpa [List.reverse_cons] using hP'
    exact ih (pre ++ [x]) (b :: acc)
      (by rw [List.append_assoc, List.singleton_append]; exact hL)
      s₂ w₂ hrev rs s' w' hrest

/-- Hoare rule for `List.mapM` (the `visitMutual` shape), with the invariant
indexed by the processed prefix and the produced outputs. -/
theorem run_list_mapM_ok {f : γ → EraseM β} {L : List γ}
    {s : ErasureState} {w : Void IO.RealWorld}
    (P : List γ → List β → ErasureState → Void IO.RealWorld → Prop)
    (hinit : P [] [] s w)
    (hstep : ∀ pre x post outs s₁ w₁ b s₂ w₂, L = pre ++ x :: post →
      P pre outs s₁ w₁ → f x s₁ ctx cctx ref w₁ = .ok (b, s₂) w₂ →
      P (pre ++ [x]) (outs ++ [b]) s₂ w₂)
    {rs : List β} {s' : ErasureState} {w' : Void IO.RealWorld}
    (hrun : List.mapM f L s ctx cctx ref w = .ok (rs, s') w') :
    P L rs s' w' := by
  unfold List.mapM at hrun
  exact run_list_mapM_ok_go ctx cctx ref f L P hstep L [] [] rfl s w
    (by simpa using hinit) rs s' w' hrun

end LoopRules

/-! ## Examples

One small example per lemma group, checking that the statements compose the
way the bridge proof will use them. -/

section Examples

variable {α : Type}
variable (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
  (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld)

-- `run_bind` + state primitives compose by `rw`.
example (s₀ : ErasureState) :
    (do set s₀; get : EraseM ErasureState) s ctx cctx ref w = .ok (s₀, s₀) w := by
  rw [run_bind, run_set]; rfl

example (g : ErasureState → ErasureState) :
    (do modify g; get : EraseM ErasureState) s ctx cctx ref w = .ok (g s, g s) w := by
  rw [run_bind, run_modify]; rfl

-- `run_bind_ok`: inversion through an opaque action.
example (x : EraseM Nat) (g : Nat → Nat) (r : Nat) (s' : ErasureState)
    (w' : Void IO.RealWorld)
    (h : (do let a ← x; pure (g a) : EraseM Nat) s ctx cctx ref w = .ok (r, s') w') :
    ∃ a, r = g a := by
  rw [run_bind_ok] at h
  obtain ⟨a, s₁, w₁, -, hp⟩ := h
  rw [run_pure] at hp
  cases hp
  exact ⟨a, rfl⟩

-- `run_withReader` + `run_read`.
example (f : ErasureContext → ErasureContext) :
    (withReader f read : EraseM ErasureContext) s ctx cctx ref w = .ok (f ctx, s) w := by
  rw [run_withReader, run_read]

-- `run_liftCoreM_state` / `run_liftMetaM_state`: lifted actions leave the
-- `ErasureState` alone.
example (x : CoreM Nat) (a : Nat) (s' : ErasureState) (w' : Void IO.RealWorld)
    (h : (liftM x : EraseM Nat) s ctx cctx ref w = .ok (a, s') w') : s' = s :=
  run_liftCoreM_state s ctx cctx ref w h

example (x : MetaM Nat) (a : Nat) (s' : ErasureState) (w' : Void IO.RealWorld)
    (h : liftMetaM x s ctx cctx ref w = .ok (a, s') w') : s' = s :=
  run_liftMetaM_state s ctx cctx ref w h

-- `run_throwError_ne_ok` under a bind (via `run_bind_ne_ok`).
example (x : EraseM Nat) (msg : MessageData) (r : Nat) (s' : ErasureState)
    (w' : Void IO.RealWorld) :
    (do let _ ← x; (throwError msg : EraseM Nat)) s ctx cctx ref w ≠ .ok (r, s') w' :=
  run_bind_ne_ok s ctx cctx ref w
    (fun _ s₁ w₁ => run_throwError_ne_ok s₁ ctx cctx ref w₁ msg) r s' w'

-- `panic!`/`unreachable!` at `EraseM` *succeeds* with `default`.
example : (unreachable! : EraseM LBTerm) s ctx cctx ref w = .ok (default, s) w :=
  run_panicWithPosWithDecl s ctx cctx ref w _ _ _ _ _

-- `run_modifyGet`.
example :
    (modifyGet (fun s => (s.gdecls, s)) : EraseM GlobalDeclarations) s ctx cctx ref w
      = .ok (s.gdecls, s) w :=
  run_modifyGet s ctx cctx ref w _

-- Loop rule for `List.forIn'`: the membership hypothesis is available to the
-- invariant-preservation proof.
example (l : List Nat) (init r : Nat) (s' : ErasureState) (w' : Void IO.RealWorld)
    (h : forIn' l init
        (fun x _ _ => pure (.yield x) : (a : Nat) → a ∈ l → Nat → EraseM (ForInStep Nat))
        s ctx cctx ref w = .ok (r, s') w') :
    r = init ∨ r ∈ l := by
  refine run_list_forIn'_ok ctx cctx ref (fun acc _ _ => acc = init ∨ acc ∈ l) l _ init s w
    (.inl rfl) ?_ r s' w' h
  intro a ha acc s₁ w₁ st s₂ w₂ _ hbody
  rw [run_pure] at hbody
  cases hbody
  exact .inr ha

-- Loop rule for `Array.forIn` (explicit `forIn` application): a body that
-- does not touch the state preserves it.
example (xs : Array Nat) (r : Nat) (s' : ErasureState) (w' : Void IO.RealWorld)
    (h : forIn xs 0 (fun x acc => pure (.yield (acc + x)) : Nat → Nat → EraseM (ForInStep Nat))
      s ctx cctx ref w = .ok (r, s') w') :
    s' = s := by
  refine run_array_forIn_ok ctx cctx ref (fun _ s₁ _ => s₁ = s) xs _ 0 s w rfl ?_ r s' w' h
  intro a _ acc s₁ w₁ st s₂ w₂ hP hbody
  rw [run_pure] at hbody
  cases hbody
  exact hP

-- Loop rule for `Array.foldlM`: same, plus a fact about the result shape.
example (xs : Array Nat) (r : Nat) (s' : ErasureState) (w' : Void IO.RealWorld)
    (h : (xs.foldlM (fun acc x => pure (acc + x)) 1 : EraseM Nat) s ctx cctx ref w
      = .ok (r, s') w') :
    0 < r ∧ s' = s := by
  have hP := run_array_foldlM_ok ctx cctx ref
    (P := fun _ acc s₁ _ => 0 < acc ∧ s₁ = s) ⟨Nat.one_pos, rfl⟩
    (fun pre x post acc s₁ w₁ acc' s₂ w₂ _ hacc hg => by
      rw [run_pure] at hg
      cases hg
      exact ⟨Nat.lt_of_lt_of_le hacc.1 (Nat.le_add_right ..), hacc.2⟩)
    h
  exact hP

-- Loop rule for `List.mapM`: as many outputs as inputs.
example (f : Nat → EraseM Nat) (L : List Nat) (rs : List Nat) (s' : ErasureState)
    (w' : Void IO.RealWorld)
    (h : (L.mapM f : EraseM (List Nat)) s ctx cctx ref w = .ok (rs, s') w') :
    rs.length = L.length := by
  have hP := run_list_mapM_ok ctx cctx ref
    (P := fun pre outs _ _ => outs.length = pre.length) rfl
    (fun pre x post outs s₁ w₁ b s₂ w₂ _ hlen _ => by simp [hlen])
    h
  exact hP

-- The parallel-`for` shape: `for x in xs, y in ys do …` elaborates to an
-- `Array.forIn` over `xs` whose accumulator threads the `Std.Stream` state of
-- `ys` (an `MProd`, with an early `.done` when the stream runs out);
-- `run_array_forIn_ok` applies with an invariant over that accumulator.
-- Here: a pure body preserves the state.
example (xs : Array Nat) (ys : List Nat) (r : Nat) (s' : ErasureState)
    (w' : Void IO.RealWorld)
    (h : (do
        let mut acc := 0
        for x in xs, y in ys do
          acc := acc + x + y
        pure acc : EraseM Nat) s ctx cctx ref w = .ok (r, s') w') :
    s' = s := by
  rw [run_bind_ok] at h
  obtain ⟨p, s₁, w₁, hloop, hp⟩ := h
  obtain ⟨ps, acc⟩ := p
  replace hp : (pure acc : EraseM Nat) s₁ ctx cctx ref w₁ = .ok (r, s') w' := hp
  rw [run_pure] at hp
  cases hp
  refine run_array_forIn_ok ctx cctx ref (fun _ s₂ _ => s₂ = s) xs _ _ s w rfl ?_ _ _ _ hloop
  intro a _ acc s₂ w₂ st s₃ w₃ hP hbody
  obtain ⟨sacc, nacc⟩ := acc
  simp only [] at hbody
  cases hnext : Std.Stream.next? sacc with
  | none =>
    rw [hnext] at hbody
    simp only [] at hbody
    rw [run_pure] at hbody
    cases hbody
    exact hP
  | some yp =>
    obtain ⟨y, ps'⟩ := yp
    rw [hnext] at hbody
    simp only [] at hbody
    rw [run_bind_ok] at hbody
    obtain ⟨u, s₄, w₄, hy, hbody⟩ := hbody
    rw [run_pure] at hy
    cases hy
    rw [run_pure] at hbody
    cases hbody
    exact hP

end Examples

/-! ## Scale check: fixpoint induction over the full 18-function family -/

/-- **Scale check** for the bridge machinery: a real (if modest) shape
property of the erasure family, proved by
`Erasure.visitExpr.mutual_fixpoint_induct` with all 18 motives in the
canonical run-ok form. Real content (per motive number):

* `visitExpr` (1): on a `.lam` input, a successful run returns `.box` or a
  `.lambda` (uses the `visitLambda` induction hypothesis);
* `visitConst` (4): on a `.const` input, returns a `.fvar` or a `.const`;
* `visitAppArgs` (7): on nonempty `args`, returns an `.app`
  (via the `Array.foldlM` loop rule);
* `visitLambda` (9): on a `.lam` input, returns a `.lambda`;
* the other 14 motives carry the trivial conclusion, so that every
  admissibility obligation and the sheer size of the step goals are still
  exercised at full scale.

This confirms: the 18 admissibility obligations discharge with
`eraseM_admissible_ok₁`–`₅`, the step goals are tractable with the run
lemmas, and elaboration time is acceptable. -/
theorem visitExpr_run_shape :
    (∀ e s ctx cctx ref w r s' w', visitExpr e s ctx cctx ref w = .ok (r, s') w' →
      ∀ bn ty bd bi, e = .lam bn ty bd bi → r = .box ∨ ∃ nm b, r = .lambda nm b) ∧
    (∀ l s ctx cctx ref w r s' w', visitLiteral l s ctx cctx ref w = .ok (r, s') w' →
      True) ∧
    (∀ cn args s ctx cctx ref w r s' w',
      visitConstructor cn args s ctx cctx ref w = .ok (r, s') w' → True) ∧
    (∀ e s ctx cctx ref w r s' w', visitConst e s ctx cctx ref w = .ok (r, s') w' →
      ∀ nm us, e = .const nm us → (∃ id, r = .fvar id) ∨ (∃ kn, r = .const kn)) ∧
    (∀ n s ctx cctx ref w r s' w',
      get_constant_kername n s ctx cctx ref w = .ok (r, s') w' → True) ∧
    (∀ n s ctx cctx ref w r s' w', visitMutual n s ctx cctx ref w = .ok (r, s') w' →
      True) ∧
    (∀ t args s ctx cctx ref w r s' w',
      visitAppArgs t args s ctx cctx ref w = .ok (r, s') w' →
      0 < args.size → ∃ u v, r = .app u v) ∧
    (∀ e s ctx cctx ref w r s' w', visitLet e s ctx cctx ref w = .ok (r, s') w' →
      True) ∧
    (∀ e s ctx cctx ref w r s' w', visitLambda e s ctx cctx ref w = .ok (r, s') w' →
      ∀ bn ty bd bi, e = .lam bn ty bd bi → ∃ nm b, r = .lambda nm b) ∧
    (∀ tn i e s ctx cctx ref w r s' w',
      visitProj tn i e s ctx cctx ref w = .ok (r, s') w' → True) ∧
    (∀ e s ctx cctx ref w r s' w', visitApp e s ctx cctx ref w = .ok (r, s') w' →
      True) ∧
    (∀ e s ctx cctx ref w r s' w', visitConstApp e s ctx cctx ref w = .ok (r, s') w' →
      True) ∧
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
    (motive_1 := fun f => ∀ e s ctx cctx ref w r s' w',
      f e s ctx cctx ref w = .ok (r, s') w' →
      ∀ bn ty bd bi, e = .lam bn ty bd bi → r = .box ∨ ∃ nm b, r = .lambda nm b)
    (motive_2 := fun f => ∀ l s ctx cctx ref w r s' w',
      f l s ctx cctx ref w = .ok (r, s') w' → True)
    (motive_3 := fun f => ∀ cn args s ctx cctx ref w r s' w',
      f cn args s ctx cctx ref w = .ok (r, s') w' → True)
    (motive_4 := fun f => ∀ e s ctx cctx ref w r s' w',
      f e s ctx cctx ref w = .ok (r, s') w' →
      ∀ nm us, e = .const nm us → (∃ id, r = .fvar id) ∨ (∃ kn, r = .const kn))
    (motive_5 := fun f => ∀ n s ctx cctx ref w r s' w',
      f n s ctx cctx ref w = .ok (r, s') w' → True)
    (motive_6 := fun f => ∀ n s ctx cctx ref w r s' w',
      f n s ctx cctx ref w = .ok (r, s') w' → True)
    (motive_7 := fun f => ∀ t args s ctx cctx ref w r s' w',
      f t args s ctx cctx ref w = .ok (r, s') w' → 0 < args.size → ∃ u v, r = .app u v)
    (motive_8 := fun f => ∀ e s ctx cctx ref w r s' w',
      f e s ctx cctx ref w = .ok (r, s') w' → True)
    (motive_9 := fun f => ∀ e s ctx cctx ref w r s' w',
      f e s ctx cctx ref w = .ok (r, s') w' →
      ∀ bn ty bd bi, e = .lam bn ty bd bi → ∃ nm b, r = .lambda nm b)
    (motive_10 := fun f => ∀ tn i e s ctx cctx ref w r s' w',
      f tn i e s ctx cctx ref w = .ok (r, s') w' → True)
    (motive_11 := fun f => ∀ e s ctx cctx ref w r s' w',
      f e s ctx cctx ref w = .ok (r, s') w' → True)
    (motive_12 := fun f => ∀ e s ctx cctx ref w r s' w',
      f e s ctx cctx ref w = .ok (r, s') w' → True)
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
  -- Step 1: visitExpr — dispatch through the erasability test to visitLambda.
  · intro vE vLit vLet vLam vProj vApp _ _ _ ih9 _ _
    intro e s ctx cctx ref w r s' w' hrun bn ty bd bi he
    subst he
    simp only [] at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨c, s₁, w₁, -, hk⟩ := hrun
    by_cases hc : c = true
    · rw [if_pos hc] at hk
      rw [run_pure] at hk
      cases hk
      exact .inl rfl
    · rw [if_neg hc] at hk
      rw [run_bind_ok] at hk
      obtain ⟨u, s₂, w₂, hp, hjp⟩ := hk
      rw [run_pure] at hp
      cases hp
      exact .inr (ih9 _ s₁ ctx cctx ref w₁ r s' w' hjp bn ty bd bi rfl)
  -- Step 2: visitLiteral (trivial conclusion).
  · intros; trivial
  -- Step 3: visitConstructor (trivial conclusion).
  · intros; trivial
  -- Step 4: visitConst — read the fixvars map, then either a fvar or a const.
  · intro gck _
    intro e s ctx cctx ref w r s' w' hrun nm us he
    subst he
    simp only [] at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨c, s₁, w₁, hr, hk⟩ := hrun
    rw [run_read] at hr
    cases hr
    cases hopt : ctx.fixvars.bind (fun hmap => hmap[nm]?) with
    | some id =>
      rw [hopt] at hk
      simp only [] at hk
      rw [run_pure] at hk
      cases hk
      exact .inl ⟨id, rfl⟩
    | none =>
      rw [hopt] at hk
      simp only [] at hk
      rw [run_bind_ok] at hk
      obtain ⟨u, s₂, w₂, hp, hjp⟩ := hk
      rw [run_pure] at hp
      cases hp
      rw [run_bind_ok] at hjp
      obtain ⟨kn, s₃, w₃, -, hp2⟩ := hjp
      rw [run_pure] at hp2
      cases hp2
      exact .inr ⟨kn, rfl⟩
  -- Step 5: get_constant_kername (trivial conclusion).
  · intros; trivial
  -- Step 6: visitMutual (trivial conclusion).
  · intros; trivial
  -- Step 7: visitAppArgs — the Array.foldlM loop rule.
  · intro vE _
    intro t args s ctx cctx ref w r s' w' hrun hpos
    simp only [] at hrun
    have hP := run_array_foldlM_ok ctx cctx ref
      (P := fun done acc _ _ => (∃ u v, acc = LBTerm.app u v) ∨ (done = [] ∧ acc = t))
      (Or.inr ⟨rfl, rfl⟩)
      (fun pre x post acc s₁ w₁ acc' s₂ w₂ _ _ hg => by
        rw [run_bind_ok] at hg
        obtain ⟨u, s₃, w₃, -, hp⟩ := hg
        rw [run_pure] at hp
        cases hp
        exact .inl ⟨acc, u, rfl⟩)
      hrun
    rcases hP with ⟨u, v, huv⟩ | ⟨hnil, -⟩
    · exact ⟨u, v, huv⟩
    · rw [Array.toList_eq_nil_iff] at hnil
      subst hnil
      simp at hpos
  -- Step 8: visitLet (trivial conclusion).
  · intros; trivial
  -- Step 9: visitLambda — through lambdaMonocular/withLocalDecl/mkLambda.
  · intro vE _
    intro e s ctx cctx ref w r s' w' hrun bn ty bd bi he
    subst he
    simp only [] at hrun
    unfold lambdaMonocular at hrun
    simp only [] at hrun
    unfold Erasure.withLocalDecl at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨fv, s₁, w₁, -, hk⟩ := hrun
    simp only [] at hk
    rw [run_withReader] at hk
    rw [run_bind_ok] at hk
    obtain ⟨t, s₂, w₂, -, hm⟩ := hk
    unfold Erasure.mkLambda at hm
    rw [run_bind_ok] at hm
    obtain ⟨nm', s₃, w₃, -, hp⟩ := hm
    rw [run_pure] at hp
    cases hp
    exact ⟨nm', _, rfl⟩
  -- Steps 10–18: trivial conclusions.
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial

end Erasure

