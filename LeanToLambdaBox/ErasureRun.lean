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

/-- Stepping a `read`-headed bind: `read` is pure (`run_read`), so `read >>= f`
runs as `f ctx` at the unchanged state/world. (Used where a `do`-block first
reads the `ErasureContext` — e.g. `visitExpr` reads `ctx.lparams` before
invoking the relevance oracle.) -/
theorem run_read_bind {β} (f : ErasureContext → EraseM β) :
    (read >>= f : EraseM β) s ctx cctx ref w = f ctx s ctx cctx ref w := by
  rw [run_bind, run_read]

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
  -- the pi-CCPO instance is no longer found by `infer_instance` (the pointwise
  -- `FlatOrder.instCCPO` is not synthesized under the `(w : Void σ)` binder), so
  -- supply it explicitly; it is the instance `CCPO (EST ε σ α)` is built from.
  letI : CCPO ((w : Void σ) → FlatOrder (EST.bot (ε := ε) (α := α) w)) :=
    @instCCPOPi _ _ (fun _ => FlatOrder.instCCPO)
  have h : admissible (α := (w : Void σ) → FlatOrder (EST.bot (ε := ε) w))
      (fun x => ∀ w a w', x w = .ok a w' → Q w a w') := by
    apply admissible_pi_apply
      (P := fun w (v : FlatOrder (EST.bot w)) => ∀ a w', v = .ok a w' → Q w a w')
    intro w
    apply admissible_pi; intro a
    apply admissible_pi; intro w'
    apply admissible_flatOrder
    intro h
    simp [EST.bot, FlatOrder.mk] at h
  exact h

/-- Admissibility of the run-ok motive at the `EST` leaf, with the result
split as a pair — the shape produced by running the `StateT` layer. -/
theorem est_admissible_ok_pair {ε σ : Type} [Nonempty ε] {α β : Type}
    (Q : Void σ → α → β → Void σ → Prop) :
    admissible (α := EST ε σ (α × β))
      (fun x => ∀ w a b w', x w = .ok (a, b) w' → Q w a b w') := by
  letI : CCPO ((w : Void σ) → FlatOrder (EST.bot (ε := ε) (α := α × β) w)) :=
    @instCCPOPi _ _ (fun _ => FlatOrder.instCCPO)
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
    simp [EST.bot, FlatOrder.mk] at h
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

/-- Auxiliary induction for `run_list_forIn_ok'`, generalized over the processed
prefix. -/
theorem run_list_forIn_ok'_go (f : γ → β → EraseM (ForInStep β)) (L : List γ)
    (P : List γ → β → ErasureState → Void IO.RealWorld → Prop)
    (hyield : ∀ pre x post acc s₁ w₁ b s₂ w₂, L = pre ++ x :: post →
      P pre acc s₁ w₁ → f x acc s₁ ctx cctx ref w₁ = .ok (.yield b, s₂) w₂ →
      P (pre ++ [x]) b s₂ w₂)
    (hdone : ∀ pre x post acc s₁ w₁ b s₂ w₂, L = pre ++ x :: post →
      P pre acc s₁ w₁ → f x acc s₁ ctx cctx ref w₁ = .ok (.done b, s₂) w₂ → False) :
    ∀ (todo pre : List γ), L = pre ++ todo →
      ∀ acc s₁ w₁, P pre acc s₁ w₁ →
      ∀ r s' w', forIn todo acc f s₁ ctx cctx ref w₁ = .ok (r, s') w' →
      P L r s' w' := by
  intro todo
  induction todo with
  | nil =>
    intro pre hL acc s₁ w₁ hP r s' w' hrun
    rw [List.forIn_nil, run_pure] at hrun
    cases hrun
    simpa [hL] using hP
  | cons x todo ih =>
    intro pre hL acc s₁ w₁ hP r s' w' hrun
    rw [List.forIn_cons, run_bind_ok] at hrun
    obtain ⟨st, s₂, w₂, hf, hcont⟩ := hrun
    cases st with
    | done b => exact (hdone pre x todo acc s₁ w₁ b s₂ w₂ hL hP hf).elim
    | yield b =>
      have hcont' : forIn todo b f s₂ ctx cctx ref w₂ = .ok (r, s') w' := hcont
      exact ih (pre ++ [x]) (by rw [List.append_assoc, List.singleton_append]; exact hL)
        b s₂ w₂ (hyield pre x todo acc s₁ w₁ b s₂ w₂ hL hP hf) r s' w' hcont'

/-- **Prefix-indexed** Hoare rule for `forIn` over a `List`: like
`run_list_forIn_ok`, but the invariant is indexed by the *processed prefix* (so
the step hypothesis knows exactly which element is being processed, and at which
position), and early exit is *refuted* rather than accommodated — the `.done`
hypothesis must derive `False`. Consequently the conclusion is the invariant at
the **whole** list, which is what a loop that fills one output slot per input
needs (`visitCases`' parallel alternatives `for`, whose two
`Std.Stream.next? = none` arms are `ForInStep.done`). -/
theorem run_list_forIn_ok' {f : γ → β → EraseM (ForInStep β)} {L : List γ} {init : β}
    {s : ErasureState} {w : Void IO.RealWorld}
    (P : List γ → β → ErasureState → Void IO.RealWorld → Prop)
    (hinit : P [] init s w)
    (hyield : ∀ pre x post acc s₁ w₁ b s₂ w₂, L = pre ++ x :: post →
      P pre acc s₁ w₁ → f x acc s₁ ctx cctx ref w₁ = .ok (.yield b, s₂) w₂ →
      P (pre ++ [x]) b s₂ w₂)
    (hdone : ∀ pre x post acc s₁ w₁ b s₂ w₂, L = pre ++ x :: post →
      P pre acc s₁ w₁ → f x acc s₁ ctx cctx ref w₁ = .ok (.done b, s₂) w₂ → False)
    {r : β} {s' : ErasureState} {w' : Void IO.RealWorld}
    (hrun : forIn L init f s ctx cctx ref w = .ok (r, s') w') :
    P L r s' w' :=
  run_list_forIn_ok'_go ctx cctx ref f L P hyield hdone L [] rfl init s w hinit r s' w' hrun

/-- Prefix-indexed Hoare rule for `forIn` over an `Array`, phrased on
`as.toList` (see `run_list_forIn_ok'`). This is the rule the `visitCases`
alternatives loop needs: the parallel-`for` accumulator threads two
`Std.Stream` states whose positions must be tied to the alternative index, which
only a prefix-indexed invariant can express. -/
theorem run_array_forIn_ok' {f : γ → β → EraseM (ForInStep β)} {as : Array γ} {init : β}
    {s : ErasureState} {w : Void IO.RealWorld}
    (P : List γ → β → ErasureState → Void IO.RealWorld → Prop)
    (hinit : P [] init s w)
    (hyield : ∀ pre x post acc s₁ w₁ b s₂ w₂, as.toList = pre ++ x :: post →
      P pre acc s₁ w₁ → f x acc s₁ ctx cctx ref w₁ = .ok (.yield b, s₂) w₂ →
      P (pre ++ [x]) b s₂ w₂)
    (hdone : ∀ pre x post acc s₁ w₁ b s₂ w₂, as.toList = pre ++ x :: post →
      P pre acc s₁ w₁ → f x acc s₁ ctx cctx ref w₁ = .ok (.done b, s₂) w₂ → False)
    {r : β} {s' : ErasureState} {w' : Void IO.RealWorld}
    (hrun : forIn as init f s ctx cctx ref w = .ok (r, s') w') :
    P as.toList r s' w' := by
  rw [← Array.forIn_toList] at hrun
  exact run_list_forIn_ok' ctx cctx ref P hinit hyield hdone hrun

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
-- `ys` (a pair `(user accumulator, stream state)`, with an early `.done` when
-- the stream runs out); `run_array_forIn_ok` applies with an invariant over
-- that accumulator. Here: a pure body preserves the state.
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
  obtain ⟨acc, ps⟩ := p
  replace hp : (pure acc : EraseM Nat) s₁ ctx cctx ref w₁ = .ok (r, s') w' := hp
  rw [run_pure] at hp
  cases hp
  refine run_array_forIn_ok ctx cctx ref (fun _ s₂ _ => s₂ = s) xs _ _ s w rfl ?_ _ _ _ hloop
  intro a _ acc s₂ w₂ st s₃ w₃ hP hbody
  obtain ⟨nacc, sacc⟩ := acc
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
    rw [run_pure] at hbody
    cases hbody
    exact hP

-- The prefix-indexed rule on the same parallel-`for` shape: the invariant now
-- ties the *second* iterator's stream state to the position in the first, so the
-- early-exit (`Std.Stream.next? = none`) arm is refutable whenever the second
-- iterator is long enough. Here: as many outputs as inputs.
example (xs : Array Nat) (ys : List Nat) (hlen : xs.size ≤ ys.length)
    (r : Array Nat) (s' : ErasureState) (w' : Void IO.RealWorld)
    (h : (do
        let mut acc := (#[] : Array Nat)
        for x in xs, y in ys do
          acc := acc.push (x + y)
        pure acc : EraseM (Array Nat)) s ctx cctx ref w = .ok (r, s') w') :
    r.size = xs.size := by
  rw [run_bind_ok] at h
  obtain ⟨p, s₁, w₁, hloop, hp⟩ := h
  obtain ⟨acc, ps⟩ := p
  replace hp : (pure acc : EraseM (Array Nat)) s₁ ctx cctx ref w₁ = .ok (r, s') w' := hp
  rw [run_pure] at hp
  cases hp
  have key := run_array_forIn_ok' ctx cctx ref
    (P := fun pre (a : Array Nat × List Nat) _ _ =>
      a.1.size = pre.length ∧ a.2 = ys.drop pre.length)
    ⟨rfl, rfl⟩
    (fun pre x post acc s₂ w₂ b s₃ w₃ hL hP hbody => by
      obtain ⟨nacc, sacc⟩ := acc
      obtain ⟨hsize, hdrop⟩ := hP
      simp only [] at hsize hdrop hbody
      have hlt : pre.length < ys.length := by
        have h1 : pre.length < xs.toList.length := by rw [hL]; simp
        simp only [Array.length_toList] at h1; omega
      cases sacc with
      | nil =>
        exact absurd (List.drop_eq_nil_iff.mp hdrop.symm) (by omega)
      | cons y rest =>
        replace hbody :
            (pure (ForInStep.yield (nacc.push (x + y), rest)) :
              EraseM (ForInStep (Array Nat × List Nat))) s₂ ctx cctx ref w₂
              = .ok (ForInStep.yield b, s₃) w₃ := hbody
        rw [run_pure] at hbody
        cases hbody
        refine ⟨by simp [hsize], ?_⟩
        show rest = ys.drop (pre ++ [x]).length
        have h2 : ys.drop (pre.length + 1) = (ys.drop pre.length).drop 1 := by
          rw [List.drop_drop]
        simp only [List.length_append, List.length_cons, List.length_nil, h2, ← hdrop]
        rfl)
    (fun pre x post acc s₂ w₂ b s₃ w₃ hL hP hbody => by
      obtain ⟨nacc, sacc⟩ := acc
      obtain ⟨hsize, hdrop⟩ := hP
      simp only [] at hsize hdrop hbody
      have hlt : pre.length < ys.length := by
        have h1 : pre.length < xs.toList.length := by rw [hL]; simp
        simp only [Array.length_toList] at h1; omega
      cases sacc with
      | nil =>
        exact absurd (List.drop_eq_nil_iff.mp hdrop.symm) (by omega)
      | cons y rest =>
        replace hbody :
            (pure (ForInStep.yield (nacc.push (x + y), rest)) :
              EraseM (ForInStep (Array Nat × List Nat))) s₂ ctx cctx ref w₂
              = .ok (ForInStep.done b, s₃) w₃ := hbody
        rw [run_pure] at hbody
        exact nomatch hbody)
    hloop
  simpa using key.1

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
    rw [run_read_bind] at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨c, s₁, w₁, -, hk⟩ := hrun
    by_cases hc : c = true
    · rw [if_pos hc] at hk
      rw [run_pure] at hk
      cases hk
      exact .inl rfl
    · rw [if_neg hc] at hk
      exact .inr (ih9 _ s₁ ctx cctx ref w₁ r s' w' hk bn ty bd bi rfl)
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
      obtain ⟨kn, s₂, w₂, -, hp2⟩ := hk
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

/-! ## Registration-path run lemmas (cold start, slice S1)

The `visitExpr` family is only half of what a cold `Erasure.erase` run does: the
other half is the *registration path* — `addAxiom`, `register_inductive`,
`get_constant_kername`, `visitMutual`, `mkDef` — which is what actually populates
`ErasureState.constants`, `ErasureState.inductives` and `ErasureState.gdecls`. The
warm bridge (`VisitExprRefines.lean`) never had to model it: its conclusion is
`s' = s` and its invariant demands every referenced constant be pre-registered.

This section proves the **true** state effects of those primitives, so that a
cold-start argument can carry a registry invariant through the run instead of
assuming one. Three facts here are load-bearing and worth flagging:

* `run_addAxiom_ok` models the **panic fall-through**: `addAxiom`'s
  "already defined" guard has no `return`, and `panic!` *succeeds* at `EraseM`
  (`run_panicWithPosWithDecl`), so the `modify` runs on both branches and a second
  entry is consed. The lemma states the post-state unconditionally.
* `run_register_inductive_cold_ok` (the miss branch) is **not** state-preserving:
  it conses one `.inductiveDecl` entry (plus one axiom entry per `@[extern]`
  constructor). Any spec asserting `s = s₁` for `register_inductive` over an
  arbitrary `s` is false about the real function.
* `run_getConstInfo_state` is a *theorem*, not an assumption: `getConstInfo`,
  `getEnv`, `mkFreshFVarId` and `logInfo` are all lifted `CoreM` actions and hence
  leave the `ErasureState` alone (`run_liftCoreM_state`).
-/

section Prims
variable (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
  (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld)

theorem run_monadRefWithRef {α : Type} (r : Syntax) (x : EraseM α) :
    (MonadRef.withRef r x : EraseM α) s ctx cctx ref w = x s ctx { cctx with ref := r } ref w :=
  rfl

theorem run_logInfo_state {m : MessageData} {u : Unit} {s₁ : ErasureState}
    {w₁ : Void IO.RealWorld}
    (h : (logInfo m : EraseM Unit) s ctx cctx ref w = .ok (u, s₁) w₁) : s₁ = s :=
  run_liftCoreM_state (x := (logInfo m : CoreM Unit)) s ctx cctx ref w h

theorem run_getEnv_state {e : Environment} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (h : (getEnv : EraseM Environment) s ctx cctx ref w = .ok (e, s₁) w₁) : s₁ = s :=
  run_liftCoreM_state (x := (getEnv : CoreM Environment)) s ctx cctx ref w h

theorem run_mkFreshFVarId_state {x : FVarId} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (h : (mkFreshFVarId : EraseM FVarId) s ctx cctx ref w = .ok (x, s₁) w₁) : s₁ = s :=
  run_liftCoreM_state (x := (mkFreshFVarId : CoreM FVarId)) s ctx cctx ref w h

set_option maxHeartbeats 1000000 in
theorem run_getConstInfo_state {nm : Name} {ci : ConstantInfo} {s₁ : ErasureState}
    {w₁ : Void IO.RealWorld}
    (h : (getConstInfo nm : EraseM ConstantInfo) s ctx cctx ref w = .ok (ci, s₁) w₁) :
    s₁ = s := by
  unfold Lean.getConstInfo at h
  rw [run_bind_ok] at h
  obtain ⟨e, s₂, w₂, henv, hk⟩ := h
  have hs2 : s₂ = s := run_getEnv_state s ctx cctx ref w henv
  subst hs2
  cases hfind : e.find? nm with
  | some info =>
    rw [hfind] at hk
    simp only [] at hk
    rw [run_pure] at hk
    cases hk
    rfl
  | none =>
    rw [hfind] at hk
    simp only [] at hk
    unfold Lean.throwUnknownConstant at hk
    refine absurd hk (run_bind_ne_ok _ ctx cctx ref w₂ ?_ _ _ _)
    intro a s₃ w₃ b s₄ w₄
    unfold Lean.throwUnknownConstantAt Lean.throwUnknownIdentifierAt
    refine run_bind_ne_ok _ ctx cctx ref w₃ ?_ _ _ _
    intro a' s₅ w₅ b' s₆ w₆
    unfold Lean.throwErrorAt Lean.withRef
    refine run_bind_ne_ok _ ctx cctx ref w₅ ?_ _ _ _
    intro a'' s₇ w₇ b'' s₈ w₈
    rw [run_monadRefWithRef]
    exact run_throwError_ne_ok s₇ ctx _ ref w₇ _ _ _ _

end Prims

/-! ### state deltas -/

def CanonicalConstants (s : ErasureState) : Prop :=
  ∀ {n : Name} {k : Kername}, s.constants.get? n = some k → k = toKername n

def addAxiomState (n : Name) (s : ErasureState) : ErasureState :=
  { s with
    constants := s.constants.insert n (toKername n),
    gdecls := (toKername n, .constantDecl ⟨none⟩) :: s.gdecls }

structure ConstExt (s s' : ErasureState) : Prop where
  canon : CanonicalConstants s → CanonicalConstants s'
  dom : ∀ {n : Name}, (s.constants.get? n).isSome → (s'.constants.get? n).isSome
  gdecls : ∃ pre : GlobalDeclarations, s'.gdecls = pre ++ s.gdecls ∧
    ∀ p ∈ pre, p.2 = GlobalDecl.constantDecl ⟨none⟩

structure AxiomExt (s s' : ErasureState) : Prop extends ConstExt s s' where
  inds : s'.inductives = s.inductives

theorem ConstExt.rfl' (s : ErasureState) : ConstExt s s where
  canon := id
  dom := id
  gdecls := ⟨[], rfl, by simp⟩

theorem ConstExt.of_same {s s' : ErasureState} (hc : s'.constants = s.constants)
    (hg : s'.gdecls = s.gdecls) : ConstExt s s' where
  canon := by intro h n k hk; rw [hc] at hk; exact h hk
  dom := by intro n hn; rw [hc]; exact hn
  gdecls := ⟨[], by simpa using hg, by simp⟩

theorem ConstExt.trans {s s' s'' : ErasureState} (h : ConstExt s s') (h' : ConstExt s' s'') :
    ConstExt s s'' where
  canon hc := h'.canon (h.canon hc)
  dom hd := h'.dom (h.dom hd)
  gdecls := by
    obtain ⟨pre, hpre, hax⟩ := h.gdecls
    obtain ⟨pre', hpre', hax'⟩ := h'.gdecls
    refine ⟨pre' ++ pre, ?_, ?_⟩
    · rw [hpre', hpre, List.append_assoc]
    · intro p hp
      rcases List.mem_append.mp hp with h1 | h1
      · exact hax' p h1
      · exact hax p h1

theorem AxiomExt.rfl' (s : ErasureState) : AxiomExt s s where
  toConstExt := ConstExt.rfl' s
  inds := rfl

theorem AxiomExt.trans {s s' s'' : ErasureState} (h : AxiomExt s s') (h' : AxiomExt s' s'') :
    AxiomExt s s'' where
  toConstExt := h.toConstExt.trans h'.toConstExt
  inds := h'.inds.trans h.inds

theorem AxiomExt.addAxiom (n : Name) (s : ErasureState) : AxiomExt s (addAxiomState n s) where
  inds := rfl
  canon := by
    intro hc m k hm
    simp only [addAxiomState] at hm
    rw [Std.HashMap.get?_insert] at hm
    split at hm
    · rename_i heq
      cases hm
      have : n = m := by simpa using heq
      subst this
      rfl
    · exact hc hm
  dom := by
    intro m hm
    simp only [addAxiomState]
    rw [Std.HashMap.get?_insert]
    split
    · simp
    · exact hm
  gdecls := ⟨[(toKername n, .constantDecl ⟨none⟩)], rfl, by simp⟩

/-! ### registration shapes -/

def mutualBlockKn (indinfo : InductiveVal) : Kername :=
  rootKername (String.join (indinfo.all.map toString))

def registerIndState (indinfo : InductiveVal) (bodies : List OneInductiveBody)
    (s : ErasureState) : ErasureState :=
  { s with
    gdecls := (mutualBlockKn indinfo,
      .inductiveDecl { npars := indinfo.numParams, bodies := bodies }) :: s.gdecls }

def RegisteredBodyAt (indinfo : InductiveVal) (bodies : List OneInductiveBody)
    (n : Name) (rc : InductiveId × InductiveArgMasks) : Prop :=
  ∃ oib : OneInductiveBody,
    rc.1.mutualBlockName = mutualBlockKn indinfo ∧
    bodies[rc.1.idx]? = some oib ∧
    oib.name = toString n ∧
    oib.ctors.map (·.nargs) = rc.2.map (fun m => Array.count ConstructorArgRelevance.keep m)

theorem RegisteredBodyAt.mono {indinfo : InductiveVal} {bodies more : List OneInductiveBody}
    {n : Name} {rc : InductiveId × InductiveArgMasks}
    (h : RegisteredBodyAt indinfo bodies n rc) :
    RegisteredBodyAt indinfo (bodies ++ more) n rc := by
  obtain ⟨oib, h1, h2, h3, h4⟩ := h
  refine ⟨oib, h1, ?_, h3, h4⟩
  have hlt : rc.1.idx < bodies.length := by
    rcases List.getElem?_eq_some_iff.mp h2 with ⟨hlt, -⟩
    exact hlt
  rw [List.getElem?_append_left hlt]
  exact h2

theorem zipIdx_split_snd {α : Type _} {l : List α} {pre post : List (α × Nat)} {x : α × Nat}
    (h : l.zipIdx = pre ++ x :: post) : x.2 = pre.length := by
  have hx : (l.zipIdx)[pre.length]? = some x := by
    rw [h]; simp
  rw [List.getElem?_zipIdx] at hx
  cases hl : l[pre.length]? with
  | none => rw [hl] at hx; simp at hx
  | some a =>
    rw [hl] at hx
    simp only [Option.map_some, Option.some.injEq] at hx
    rw [← hx]
    simp

/-! ### R3 / R5 -/

theorem run_addAxiom_ok {n : Name} {s : ErasureState} {ctx : ErasureContext}
    {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {u : Unit} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (hrun : addAxiom n s ctx cctx ref w = .ok (u, s₁) w₁) :
    s₁ = addAxiomState n s ∧ w₁ = w := by
  unfold addAxiom at hrun
  simp only [] at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨s0, sA, wA, hget, hk⟩ := hrun
  rw [run_get] at hget
  cases hget
  by_cases hc : s.constants.contains n = true
  · rw [if_pos hc, run_bind_ok] at hk
    obtain ⟨_, sB, wB, hpanic, hmod⟩ := hk
    rw [run_panicWithPosWithDecl] at hpanic
    cases hpanic
    rw [run_modify] at hmod
    cases hmod
    exact ⟨rfl, rfl⟩
  · rw [if_neg hc, run_modify] at hk
    cases hk
    exact ⟨rfl, rfl⟩

theorem run_register_inductive_hit_ok {indinfo : InductiveVal}
    {rc0 : InductiveId × InductiveArgMasks}
    {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {r : InductiveId × InductiveArgMasks} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (hhit : s.inductives.get? indinfo.name = some rc0)
    (hrun : register_inductive indinfo s ctx cctx ref w = .ok (r, s₁) w₁) :
    r = rc0 ∧ s₁ = s ∧ w₁ = w := by
  unfold register_inductive at hrun
  simp only [] at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨s0, sA, wA, hget, hk⟩ := hrun
  rw [run_get] at hget
  cases hget
  rw [hhit] at hk
  simp only [] at hk
  rw [run_pure] at hk
  cases hk
  exact ⟨rfl, rfl, rfl⟩

/-! ### R4 -/

set_option maxHeartbeats 2000000 in
theorem run_register_inductive_cold_ok
    {indinfo : InductiveVal} {s : ErasureState} {ctx : ErasureContext}
    {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {r : InductiveId × InductiveArgMasks} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (hmiss : s.inductives.get? indinfo.name = none)
    (hrun : register_inductive indinfo s ctx cctx ref w = .ok (r, s₁) w₁) :
    ∃ (bodies : List OneInductiveBody) (sM : ErasureState),
      s₁ = registerIndState indinfo bodies sM ∧
      r = sM.inductives[indinfo.name]! ∧
      bodies.length = indinfo.all.length ∧
      ConstExt s sM ∧
      (∀ {n : Name}, (s.inductives.get? n).isSome → (sM.inductives.get? n).isSome) ∧
      ∀ {n : Name} {rc : InductiveId × InductiveArgMasks}, sM.inductives.get? n = some rc →
        s.inductives.get? n = some rc ∨ RegisteredBodyAt indinfo bodies n rc := by
  unfold register_inductive at hrun
  simp only [] at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨s0, sA, wA, hget, hk⟩ := hrun
  rw [run_get] at hget
  cases hget
  rw [hmiss] at hk
  simp only [] at hk
  rw [run_bind_ok] at hk
  obtain ⟨bodies, sM, wM, hmap, htail⟩ := hk
  rw [run_bind_ok] at htail
  obtain ⟨u, sN, wN, hmod, htail2⟩ := htail
  rw [run_modify] at hmod
  cases hmod
  rw [run_bind_ok] at htail2
  obtain ⟨sX, sY, wY, hget2, hp⟩ := htail2
  rw [run_get] at hget2
  cases hget2
  rw [run_pure] at hp
  cases hp
  refine ⟨bodies, sM, rfl, rfl, ?_⟩
  have key := run_list_mapM_ok ctx cctx ref
    (P := fun (pre : List (Name × Nat)) (outs : List OneInductiveBody) s' _ =>
      outs.length = pre.length ∧ ConstExt s s' ∧
      (∀ {n : Name}, (s.inductives.get? n).isSome → (s'.inductives.get? n).isSome) ∧
      ∀ {n : Name} {rc : InductiveId × InductiveArgMasks}, s'.inductives.get? n = some rc →
        s.inductives.get? n = some rc ∨ RegisteredBodyAt indinfo outs n rc)
    ⟨rfl, ConstExt.rfl' s, id, fun h => Or.inl h⟩ ?step hmap
  · obtain ⟨hlen, hce, hgrow, hreg⟩ := key
    exact ⟨by rw [hlen, List.length_zipIdx], hce, hgrow, hreg⟩
  case step =>
    clear hmap
    intro pre x post outs sP wP b sQ wQ hL hP hbody
    obtain ⟨hlen, hce, hgrow, hreg⟩ := hP
    have hidx : x.2 = pre.length := zipIdx_split_snd hL
    -- the invariant when the step leaves the state alone
    have htriv : ∀ b' : OneInductiveBody,
        (outs ++ [b']).length = (pre ++ [x]).length ∧ ConstExt s sP ∧
        (∀ {n : Name}, (s.inductives.get? n).isSome → (sP.inductives.get? n).isSome) ∧
        ∀ {n : Name} {rc : InductiveId × InductiveArgMasks}, sP.inductives.get? n = some rc →
          s.inductives.get? n = some rc ∨ RegisteredBodyAt indinfo (outs ++ [b']) n rc := by
      intro b'
      refine ⟨by simp [hlen], hce, hgrow, ?_⟩
      intro n rc h
      rcases hreg h with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'.mono
    rw [run_bind_ok] at hbody
    obtain ⟨ci, sa, wa, hci, hrest⟩ := hbody
    have hsa : sa = sP := run_getConstInfo_state sP ctx cctx ref wP hci
    subst hsa
    clear hci
    split at hrest
    case _ inf _ =>
      rw [run_bind_ok] at hrest
      obtain ⟨res, sb, wb, hctors, hrest2⟩ := hrest
      have hQ := run_list_mapM_ok ctx cctx ref
        (P := fun (_ : List Name) (outs' : List (ConstructorBody × ConstructorArgMask)) s' _ =>
          (∀ p ∈ outs', p.1.nargs = Array.count ConstructorArgRelevance.keep p.2) ∧
            AxiomExt sa s')
        ⟨by simp, AxiomExt.rfl' sa⟩ ?inner hctors
      · obtain ⟨hnargs, hax⟩ := hQ
        have hmapeq : res.unzip.fst.map (·.nargs)
            = res.unzip.snd.map (fun m => Array.count ConstructorArgRelevance.keep m) := by
          rw [List.unzip_fst, List.unzip_snd, List.map_map, List.map_map]
          exact List.map_congr_left (fun p hp => hnargs p hp)
        split at hrest2
        all_goals
          rw [run_bind_ok] at hrest2
          obtain ⟨projs, sc, wc, hpr, hrest3⟩ := hrest2
          rw [run_pure] at hpr
          have hsc : sc = sb := by cases hpr; rfl
          have hwc : wc = wb := by cases hpr; rfl
          subst hsc
          subst hwc
          rw [run_bind_ok] at hrest3
          obtain ⟨uu, sd, wd, hmod2, hfin⟩ := hrest3
          rw [run_modify] at hmod2
          cases hmod2
          rw [run_pure] at hfin
          cases hfin
          refine ⟨by simp [hlen], hce.trans (hax.toConstExt.trans (ConstExt.of_same rfl rfl)),
            ?_, ?_⟩
          · intro n hn
            show (Std.HashMap.get? (Std.HashMap.insert _ _ _) n).isSome
            rw [Std.HashMap.get?_insert]
            split
            · simp
            · rw [hax.inds]
              exact hgrow hn
          intro n rc hn
          simp only [] at hn
          rw [Std.HashMap.get?_insert] at hn
          split at hn
          · rename_i heq
            cases hn
            refine Or.inr ⟨{ name := toString x.1, ctors := res.unzip.fst, projs := projs },
              rfl, ?_, ?_, hmapeq⟩
            · simp [hidx, hlen]
            · have : x.1 = n := by simpa using heq
              rw [this]
          · rw [hax.inds] at hn
            rcases hreg hn with h' | h'
            · exact Or.inl h'
            · exact Or.inr h'.mono
      case inner =>
        clear hctors
        intro pre' cn post' outs' sA' wA' bres sB' wB' hL' hP' hb
        obtain ⟨hn', hax'⟩ := hP'
        rw [run_bind_ok] at hb
        obtain ⟨envv, se, we, henv, h2⟩ := hb
        have hse : se = sA' := run_getEnv_state sA' ctx cctx ref wA' henv
        subst hse
        rw [run_bind_ok] at h2
        obtain ⟨c1, sr, wr, hread, h3⟩ := h2
        rw [run_read] at hread
        cases hread
        split at h3
        · -- @[extern] constructor: logInfo, addAxiom, then the ctor-info tail
          rw [run_bind_ok] at h3
          obtain ⟨u1, sl, wl, hlog, h4⟩ := h3
          have hsl := run_logInfo_state _ ctx cctx ref _ hlog
          subst hsl
          rw [run_bind_ok] at h4
          obtain ⟨u2, sax, wax, hadd, h5⟩ := h4
          obtain ⟨hst, hwt⟩ := run_addAxiom_ok hadd
          subst hst
          subst hwt
          rw [run_bind_ok] at h5
          obtain ⟨ci2, s6, w6, hci2, h6⟩ := h5
          have h6s := run_getConstInfo_state _ ctx cctx ref _ hci2
          subst h6s
          split at h6
          case _ cinf _ =>
            rw [run_bind_ok] at h6
            obtain ⟨c2, s7, w7, hread2, h7⟩ := h6
            rw [run_read] at hread2
            cases hread2
            split at h7
            all_goals
              rw [run_bind_ok] at h7
              obtain ⟨am, s8, w8, ham, h8⟩ := h7
              first
                | (have hs8 := run_liftMetaM_state _ ctx cctx ref _ ham; subst hs8)
                | (rw [run_pure] at ham; cases ham)
              rw [run_pure] at h8
              cases h8
              refine ⟨?_, hax'.trans (AxiomExt.addAxiom cn _)⟩
              intro p hp
              rcases List.mem_append.mp hp with hp' | hp'
              · exact hn' p hp'
              · simp only [List.mem_singleton] at hp'
                subst hp'
                first | rfl | simp
          all_goals
            rw [run_panicWithPosWithDecl] at h6
            cases h6
            refine ⟨?_, hax'.trans (AxiomExt.addAxiom cn _)⟩
            intro p hp
            rcases List.mem_append.mp hp with hp' | hp'
            · exact hn' p hp'
            · simp only [List.mem_singleton] at hp'
              subst hp'
              first | rfl | simp
        · -- plain constructor: just the ctor-info tail
          rw [run_bind_ok] at h3
          obtain ⟨ci2, s6, w6, hci2, h6⟩ := h3
          have h6s := run_getConstInfo_state _ ctx cctx ref _ hci2
          subst h6s
          split at h6
          case _ cinf _ =>
            rw [run_bind_ok] at h6
            obtain ⟨c2, s7, w7, hread2, h7⟩ := h6
            rw [run_read] at hread2
            cases hread2
            split at h7
            all_goals
              rw [run_bind_ok] at h7
              obtain ⟨am, s8, w8, ham, h8⟩ := h7
              first
                | (have hs8 := run_liftMetaM_state _ ctx cctx ref _ ham; subst hs8)
                | (rw [run_pure] at ham; cases ham)
              rw [run_pure] at h8
              cases h8
              refine ⟨?_, hax'⟩
              intro p hp
              rcases List.mem_append.mp hp with hp' | hp'
              · exact hn' p hp'
              · simp only [List.mem_singleton] at hp'
                subst hp'
                first | rfl | simp
          all_goals
            rw [run_panicWithPosWithDecl] at h6
            cases h6
            refine ⟨?_, hax'⟩
            intro p hp
            rcases List.mem_append.mp hp with hp' | hp'
            · exact hn' p hp'
            · simp only [List.mem_singleton] at hp'
              subst hp'
              first | rfl | simp
    all_goals
      rw [run_panicWithPosWithDecl] at hrest
      cases hrest
      exact htriv _

/-- **R9.** -/
theorem run_mkDef_ok {nm : Name} {fixvarnames : List Name} {body : LBTerm}
    {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {r : @FixDef LBTerm} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (hrun : mkDef nm fixvarnames body s ctx cctx ref w = .ok (r, s₁) w₁) :
    r.name = .named nm.toString ∧
    r.body = fixvarnames.reverse.zipIdx.foldl
      (fun b p => toBvar (ctx.fixvars.get![p.1]!) p.2 b) body ∧
    s₁ = s ∧ w₁ = w := by
  unfold mkDef at hrun
  simp only [] at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨acc, sa, wa, hloop, hp⟩ := hrun
  rw [run_pure] at hp
  cases hp
  have key := run_list_forIn_ok' ctx cctx ref
    (P := fun (pre : List (Name × Nat)) (b : LBTerm) s' w' =>
      b = pre.foldl (fun b p => toBvar (ctx.fixvars.get![p.1]!) p.2 b) body ∧ s' = s ∧ w' = w)
    ⟨rfl, rfl, rfl⟩ ?yield ?done hloop
  · obtain ⟨hb, hs, hw⟩ := key
    exact ⟨rfl, hb, hs, hw⟩
  case yield =>
    intro pre y post acc' sa' wa' b' sb' wb' hL ⟨hacc, hs, hw⟩ hbody
    subst hs
    subst hw
    rw [run_bind_ok] at hbody
    obtain ⟨c, sc, wc, hread, hp2⟩ := hbody
    rw [run_read] at hread
    cases hread
    rw [run_pure] at hp2
    cases hp2
    exact ⟨by rw [List.foldl_append, hacc]; rfl, rfl, rfl⟩
  case done =>
    intro pre y post acc' sa' wa' b' sb' wb' hL hP hbody
    rw [run_bind_ok] at hbody
    obtain ⟨c, sc, wc, hread, hp2⟩ := hbody
    rw [run_read] at hread
    cases hread
    rw [run_pure] at hp2
    exact nomatch hp2

/-- **R10.** -/
theorem run_modify_forIn_ok {γ : Type} {L : List γ} {g : γ → ErasureState → ErasureState}
    {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {u : PUnit} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (hrun : (forIn L PUnit.unit (fun x _ => do modify (g x); pure (.yield PUnit.unit)) :
        EraseM PUnit) s ctx cctx ref w = .ok (u, s₁) w₁) :
    s₁ = L.foldl (fun st x => g x st) s ∧ w₁ = w := by
  have key := run_list_forIn_ok' ctx cctx ref
    (P := fun (pre : List γ) (_ : PUnit) s' w' =>
      s' = pre.foldl (fun st x => g x st) s ∧ w' = w)
    ⟨rfl, rfl⟩ ?yield ?done hrun
  · exact key
  case yield =>
    intro pre y post acc' sa' wa' b' sb' wb' hL ⟨hs, hw⟩ hbody
    subst hs
    subst hw
    rw [run_bind_ok] at hbody
    obtain ⟨uu, sc, wc, hmod, hp2⟩ := hbody
    rw [run_modify] at hmod
    cases hmod
    rw [run_pure] at hp2
    cases hp2
    exact ⟨by rw [List.foldl_append]; rfl, rfl⟩
  case done =>
    intro pre y post acc' sa' wa' b' sb' wb' hL hP hbody
    rw [run_bind_ok] at hbody
    obtain ⟨uu, sc, wc, hmod, hp2⟩ := hbody
    rw [run_modify] at hmod
    cases hmod
    rw [run_pure] at hp2
    exact nomatch hp2

/-- **R6.** -/
theorem run_get_constant_kername_ok {n : Name}
    {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {r : Kername} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (hrun : get_constant_kername n s ctx cctx ref w = .ok (r, s₁) w₁) :
    (s.constants.get? n = some r ∧ s₁ = s ∧ w₁ = w) ∨
    (s.constants.get? n = none ∧ ∃ u : Unit,
      visitMutual n s ctx cctx ref w = .ok (u, s₁) w₁ ∧ r = s₁.constants[n]!) := by
  unfold get_constant_kername at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨s0, sa, wa, hget, hk⟩ := hrun
  rw [run_get] at hget
  cases hget
  cases hc : s.constants.get? n with
  | some kn =>
    rw [hc] at hk
    simp only [] at hk
    rw [run_pure] at hk
    cases hk
    exact Or.inl ⟨rfl, rfl, rfl⟩
  | none =>
    rw [hc] at hk
    simp only [] at hk
    rw [run_bind_ok] at hk
    obtain ⟨uu, sb, wb, hvm, hk2⟩ := hk
    rw [run_bind_ok] at hk2
    obtain ⟨sc, sd, wd, hget2, hp⟩ := hk2
    rw [run_get] at hget2
    cases hget2
    rw [run_pure] at hp
    cases hp
    exact Or.inr ⟨rfl, uu, hvm, rfl⟩

/-! ### R7 — `visitMutual`, the DAG engine

`visitMutual` is the only place the erasure family registers a *constant*, and the only
place a `.fix` body is stored. Its elaborated body is hostile to naive peeling: the
`@[inline]` prefix and the value/`@[extern]` match each duplicate the whole
non-recursive/recursive core, and the three-discriminant match defeats `split`
outright. The lemmas below tame that by abstracting every boolean test, log message and
reader update the core does not depend on, so each `split` runs on a small term.

`run_visitMutual_ok` is stated in **Hoare form** over a state predicate `Q`, taking the
`visitExpr` fact as a hypothesis (`hvE`). That is deliberate: inside
`Erasure.visitExpr.mutual_fixpoint_induct` the step goals are about an *abstract*
function, not the real `visitExpr`, so an exit-decomposition lemma about the real
`visitMutual` would be unusable there. In Hoare form the same lemma serves both the
inline (instantiate `hvE` with the motive-1 IH) and the standalone use.

One hypothesis is genuinely assumed rather than proved: `hprep`, that `prepare_erasure`
does not disturb `Q`. Its `csimp` branch runs `Lean.Core.transform` *at* `EraseM`
(through `MonadControlT`), so its state transparency does not follow from the `liftM`
lemmas; it belongs with `PrepareHyps`, the existing trust class for that function.
-/

def nonrecConstState (n : Name) (t : LBTerm) (s : ErasureState) : ErasureState :=
  { s with
    constants := s.constants.insert n (toKername n),
    gdecls := (toKername n, .constantDecl ⟨some t⟩) :: s.gdecls }

def recConstState (names : List Name) (defs : List (@FixDef LBTerm))
    (s : ErasureState) : ErasureState :=
  names.zipIdx.foldl
    (fun st p =>
      { st with
        constants := st.constants.insert p.1 (toKername p.1),
        gdecls := (toKername p.1, .constantDecl ⟨some (.fix defs p.2)⟩) :: st.gdecls }) s

/-- One step of the recursive block registration, named so that the `List.foldl`
induction that walks `recConstState` has something to generalize over. It is literally
the constant cons of the non-recursive exit at a `.fix` body. -/
def recConstStep (defs : List (@FixDef LBTerm)) (st : ErasureState) (p : Name × Nat) :
    ErasureState :=
  nonrecConstState p.1 (.fix defs p.2) st

theorem recConstState_eq (names : List Name) (defs : List (@FixDef LBTerm))
    (s : ErasureState) :
    recConstState names defs s = names.zipIdx.foldl (recConstStep defs) s := rfl

section Helpers

variable {Q : ErasureState → Prop} {Nf Cl : LBTerm → Prop} {n : Name}
  {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}

theorem run_inline_tail_ok {b1 b2 : Bool} {msg1 msg2 : MessageData}
    (hinl : ∀ {s' : ErasureState} {kn : Kername},
      Q s' → Q { s' with inlinings := kn :: s'.inlinings })
    {s : ErasureState} {ctx : ErasureContext} {w : Void IO.RealWorld}
    {u : Unit} {s₁ : ErasureState} {w₁ : Void IO.RealWorld} (hQ : Q s)
    (hrun : (if b1 = true then do
        let isInst ← liftM (Lean.Meta.isInstance n)
        if isInst = true then do
          logInfo msg1
          modify (fun s => { s with inlinings := toKername n :: s.inlinings })
        else if b2 = true then do
          logInfo msg2
          modify (fun s => { s with inlinings := toKername n :: s.inlinings })
        else pure ()
      else pure () : EraseM Unit) s ctx cctx ref w = .ok (u, s₁) w₁) : Q s₁ := by
  split at hrun
  · rw [run_bind_ok] at hrun
    obtain ⟨isInst, s2, w2, hinst, hrun⟩ := hrun
    have hz := run_liftCoreM_state (x := (Lean.Meta.isInstance n : CoreM Bool))
      _ _ cctx ref _ hinst
    subst hz
    split at hrun
    · rw [run_bind_ok] at hrun
      obtain ⟨u3, s3, w3, hlog, hrun⟩ := hrun
      have hz2 := run_logInfo_state _ _ cctx ref _ hlog
      subst hz2
      rw [run_modify] at hrun
      cases hrun
      exact hinl hQ
    · split at hrun
      · rw [run_bind_ok] at hrun
        obtain ⟨u3, s3, w3, hlog, hrun⟩ := hrun
        have hz2 := run_logInfo_state _ _ cctx ref _ hlog
        subst hz2
        rw [run_modify] at hrun
        cases hrun
        exact hinl hQ
      · rw [run_pure] at hrun
        cases hrun
        exact hQ
  · rw [run_pure] at hrun
    cases hrun
    exact hQ

/-- The `@[inline]`-attribute bookkeeping prefix: it conses at most one `inlinings`
entry and then runs the same continuation on either branch. Stated with the boolean,
the message and the continuation **abstract**. -/
theorem run_inline_prefix_ok {b : Bool} {msg : MessageData} {rest : EraseM Unit}
    (hinl : ∀ {s' : ErasureState} {kn : Kername},
      Q s' → Q { s' with inlinings := kn :: s'.inlinings })
    {s : ErasureState} {ctx : ErasureContext} {w : Void IO.RealWorld}
    {u : Unit} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (hrest : ∀ {s' : ErasureState} {w' : Void IO.RealWorld} {u' : Unit}
        {s'' : ErasureState} {w'' : Void IO.RealWorld},
      Q s' → rest s' ctx cctx ref w' = .ok (u', s'') w'' → Q s'')
    (hQ : Q s)
    (hrun : (if b = true then do
        logInfo msg
        modify (fun s => { s with inlinings := toKername n :: s.inlinings })
        rest
      else rest) s ctx cctx ref w = .ok (u, s₁) w₁) : Q s₁ := by
  split at hrun
  · rw [run_bind_ok] at hrun
    obtain ⟨u1, s2, w2, hlog, hrun⟩ := hrun
    have hz := run_logInfo_state _ _ cctx ref _ hlog
    subst hz
    rw [run_bind_ok] at hrun
    obtain ⟨u2, s3, w3, hmod, hrun⟩ := hrun
    rw [run_modify] at hmod
    cases hmod
    exact hrest (hinl hQ) hrun
  · exact hrest hQ hrun

/-- **The non-recursive exit.** Erase the (prepared) body under the declaration's
reader update, cons the constant, then the inlining bookkeeping. The reader update, the
source body and the tail's two tests / messages are abstract. -/
theorem run_nonrec_exit_ok {f : ErasureContext → ErasureContext} {e : Expr}
    {b1 b2 : ErasureContext → LBTerm → Bool} {msg1 msg2 : MessageData}
    (hinl : ∀ {s' : ErasureState} {kn : Kername},
      Q s' → Q { s' with inlinings := kn :: s'.inlinings })
    (hprep : ∀ {e' : Expr} {s' : ErasureState} {ctx' : ErasureContext}
        {w' : Void IO.RealWorld} {pe : Expr} {s'' : ErasureState} {w'' : Void IO.RealWorld},
      prepare_erasure e' s' ctx' cctx ref w' = .ok (pe, s'') w'' → Q s' → Q s'')
    (hvE : ∀ {e' : Expr} {s' : ErasureState} {ctx' : ErasureContext}
        {w' : Void IO.RealWorld} {t : LBTerm} {s'' : ErasureState} {w'' : Void IO.RealWorld},
      visitExpr e' s' ctx' cctx ref w' = .ok (t, s'') w'' → Q s' → Q s'' ∧ Nf t ∧ Cl t)
    (hnr : ∀ {s' : ErasureState} {t : LBTerm}, Q s' → Nf t → Cl t →
      Q (nonrecConstState n t s'))
    {s : ErasureState} {ctx : ErasureContext} {w : Void IO.RealWorld}
    {u : Unit} {s₁ : ErasureState} {w₁ : Void IO.RealWorld} (hQ : Q s)
    (hrun : (do
        let t ← withReader f (do let pe ← prepare_erasure e; visitExpr pe)
        modify (fun s => { s with
          constants := s.constants.insert n (toKername n),
          gdecls := (toKername n, .constantDecl ⟨some t⟩) :: s.gdecls })
        let c ← read
        if b1 c t = true then do
          let isInst ← liftM (Lean.Meta.isInstance n)
          if isInst = true then do
            logInfo msg1
            modify (fun s => { s with inlinings := toKername n :: s.inlinings })
          else if b2 c t = true then do
            logInfo msg2
            modify (fun s => { s with inlinings := toKername n :: s.inlinings })
          else pure ()
        else pure () : EraseM Unit) s ctx cctx ref w = .ok (u, s₁) w₁) : Q s₁ := by
  rw [run_bind_ok] at hrun
  obtain ⟨t, st, wt, hvis, hrun⟩ := hrun
  rw [run_withReader, run_bind_ok] at hvis
  obtain ⟨pe, sp, wp, hpr, hvis⟩ := hvis
  replace hQ := hprep hpr hQ
  obtain ⟨hQ', hnf, hcl⟩ := hvE hvis hQ
  rw [run_bind_ok] at hrun
  obtain ⟨u2, sm, wm, hmod, hrun⟩ := hrun
  rw [run_modify] at hmod
  cases hmod
  replace hQ' := hnr hQ' hnf hcl
  rw [run_bind_ok] at hrun
  obtain ⟨c2, sc, wc, hread, hrun⟩ := hrun
  rw [run_read] at hread
  cases hread
  exact run_inline_tail_ok hinl hQ' hrun

/-- **The recursive exit.** Fresh fvars, per-definition erasure under the fixvar
binding, then one `gdecls` cons per name. The two reader updates and the "value of a
declaration" projection are abstract. -/
theorem run_rec_exit_ok {names fixnames : List Name}
    {f : List FVarId → ErasureContext → ErasureContext}
    {g : ConstantInfo → ErasureContext → ErasureContext} {val : ConstantInfo → Expr}
    (hprep : ∀ {e' : Expr} {s' : ErasureState} {ctx' : ErasureContext}
        {w' : Void IO.RealWorld} {pe : Expr} {s'' : ErasureState} {w'' : Void IO.RealWorld},
      prepare_erasure e' s' ctx' cctx ref w' = .ok (pe, s'') w'' → Q s' → Q s'')
    (hvE : ∀ {e' : Expr} {s' : ErasureState} {ctx' : ErasureContext}
        {w' : Void IO.RealWorld} {t : LBTerm} {s'' : ErasureState} {w'' : Void IO.RealWorld},
      visitExpr e' s' ctx' cctx ref w' = .ok (t, s'') w'' → Q s' → Q s'' ∧ Nf t ∧ Cl t)
    (hrec : ∀ {s' : ErasureState} {defs : List (@FixDef LBTerm)},
      Q s' → Q (recConstState fixnames defs s'))
    {s : ErasureState} {ctx : ErasureContext} {w : Void IO.RealWorld}
    {u : Unit} {s₁ : ErasureState} {w₁ : Void IO.RealWorld} (hQ : Q s)
    (hrun : (do
        let ids ← names.mapM (fun _ => mkFreshFVarId)
        withReader (f ids) (do
          let defs ← names.mapM (fun m => do
            let ci ← getConstInfo m
            let t ← withReader (g ci) (do let pe ← prepare_erasure (val ci); visitExpr pe)
            mkDef (remove_unsafe_rec m) fixnames t)
          for p in fixnames.zipIdx do
            modify (fun s => { s with
              constants := s.constants.insert p.1 (toKername p.1),
              gdecls := (toKername p.1, .constantDecl ⟨some (.fix defs p.2)⟩) :: s.gdecls })
          pure ()) : EraseM Unit) s ctx cctx ref w = .ok (u, s₁) w₁) : Q s₁ := by
  rw [run_bind_ok] at hrun
  obtain ⟨ids, sid, wid, hids, hrun⟩ := hrun
  replace hQ := run_list_mapM_ok _ cctx ref
    (P := fun (_ : List Name) (_ : List FVarId) (s' : ErasureState)
        (_ : Void IO.RealWorld) => Q s')
    hQ
    (fun _ _ _ _ _ _ _ _ _ _ hQa hb => by
      have hz := run_mkFreshFVarId_state _ _ cctx ref _ hb
      subst hz
      exact hQa)
    hids
  rw [run_withReader, run_bind_ok] at hrun
  obtain ⟨defs, sd, wd, hdefs, hrun⟩ := hrun
  replace hQ := run_list_mapM_ok _ cctx ref
    (P := fun (_ : List Name) (_ : List (@FixDef LBTerm)) (s' : ErasureState)
        (_ : Void IO.RealWorld) => Q s')
    hQ
    (fun _ _ _ _ _ _ _ _ _ _ hQa hb => by
      rw [run_bind_ok] at hb
      obtain ⟨ci, s2, w2, hci, hb⟩ := hb
      have hz := run_getConstInfo_state _ _ cctx ref _ hci
      subst hz
      rw [run_bind_ok] at hb
      obtain ⟨t2, s4, w4, hvis2, hb⟩ := hb
      rw [run_withReader, run_bind_ok] at hvis2
      obtain ⟨pe2, s3, w3, hpr2, hvis2⟩ := hvis2
      replace hQa := hprep hpr2 hQa
      obtain ⟨hQ4, -, -⟩ := hvE hvis2 hQa
      obtain ⟨-, -, hs5, -⟩ := run_mkDef_ok hb
      subst hs5
      exact hQ4)
    hdefs
  rw [run_bind_ok] at hrun
  obtain ⟨u4, sf, wf, hloop, hrun⟩ := hrun
  obtain ⟨hsf, -⟩ := run_modify_forIn_ok hloop
  subst hsf
  rw [run_pure] at hrun
  cases hrun
  exact hrec hQ

set_option maxHeartbeats 1000000 in
/-- **R7 — `visitMutual`, Hoare form over its four exits.** -/
theorem run_visitMutual_ok {n : Name}
    {s : ErasureState} {ctx : ErasureContext} {w : Void IO.RealWorld}
    {u : Unit} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (hinl : ∀ {s' : ErasureState} {kn : Kername},
      Q s' → Q { s' with inlinings := kn :: s'.inlinings })
    (hax : ∀ {m : Name} {s' : ErasureState}, Q s' → Q (addAxiomState m s'))
    (hprep : ∀ {e' : Expr} {s' : ErasureState} {ctx' : ErasureContext}
        {w' : Void IO.RealWorld} {pe : Expr} {s'' : ErasureState} {w'' : Void IO.RealWorld},
      prepare_erasure e' s' ctx' cctx ref w' = .ok (pe, s'') w'' → Q s' → Q s'')
    (hvE : ∀ {e' : Expr} {s' : ErasureState} {ctx' : ErasureContext}
        {w' : Void IO.RealWorld} {t : LBTerm} {s'' : ErasureState} {w'' : Void IO.RealWorld},
      visitExpr e' s' ctx' cctx ref w' = .ok (t, s'') w'' → Q s' → Q s'' ∧ Nf t ∧ Cl t)
    (hnr : ∀ {s' : ErasureState} {t : LBTerm}, Q s' → Nf t → Cl t →
      Q (nonrecConstState n t s'))
    (hrec : ∀ {s' : ErasureState} {names : List Name} {defs : List (@FixDef LBTerm)},
      Q s' → Q (recConstState names defs s'))
    (hQ : Q s) (hrun : visitMutual n s ctx cctx ref w = .ok (u, s₁) w₁) : Q s₁ := by
  unfold visitMutual at hrun
  simp only [] at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨di, sa, wa, hdi, hrun⟩ := hrun
  have hsa := run_liftCoreM_state (x := (Compiler.LCNF.getDeclInfo? n : CoreM _))
    _ _ cctx ref _ hdi
  subst hsa
  rw [run_bind_ok] at hrun
  obtain ⟨env0, sb, wb, henv0, hrun⟩ := hrun
  have hsb := run_getEnv_state _ _ cctx ref _ henv0
  subst hsb
  clear hdi henv0
  split at hrun
  case isTrue =>
    refine run_inline_prefix_ok hinl ?_ hQ hrun
    intro s' w' u' s'' w'' hQ' hm
    rw [run_bind_ok] at hm
    obtain ⟨env2, se, we, henv2, hm⟩ := hm
    have hz := run_getEnv_state _ _ cctx ref _ henv2
    subst hz
    rw [run_bind_ok] at hm
    obtain ⟨c1, sr, wr, hread, hm⟩ := hm
    rw [run_read] at hread
    cases hread
    -- The value/`@[extern]`/config match has three discriminants; `split` cannot
    -- handle it, so resolve them by hand.
    cases hval : di.get!.value? (allowOpaque := true) <;>
      cases hext : isExtern env2 n <;>
        cases hcfg : ctx.config.extern <;>
          simp only [hval, hext, hcfg] at hm
    all_goals
      try
        (rw [run_bind_ok] at hm
         obtain ⟨u3, s3, w3, hlog, hm⟩ := hm
         have hz2 := run_logInfo_state _ _ cctx ref _ hlog
         subst hz2)
    all_goals
      first
        | (obtain ⟨hstA, -⟩ := run_addAxiom_ok hm
           subst hstA
           exact hax hQ')
        | (split at hm
           case isTrue => exact run_nonrec_exit_ok hinl hprep hvE hnr hQ' hm
           case isFalse => exact run_rec_exit_ok hprep hvE hrec hQ' hm)
  case isFalse =>
    split at hrun
    case isTrue => exact run_nonrec_exit_ok hinl hprep hvE hnr hQ hrun
    case isFalse => exact run_rec_exit_ok hprep hvE hrec hQ hrun

end Helpers

/-! ### Binder-helper run lemmas

The continuation-passing helpers (`withLocalDecl`, `lambdaMonocular`, `letMonocular`,
`forallMonocular`, `lambdaMonocularOrIntro`, `lambdaOrIntroToArity`) and the λ□-side
binder constructors (`fvar_to_name`, `mkLambda`, `mkLetIn`, `mkAlt`) sit between
`visitExpr` and every one of its binder cases, so any induction over the family's
*results* has to step through them.

Each destructuring helper `panic!`s when its argument has the wrong shape, and a panic
**succeeds** at `EraseM`, so every one of these lemmas carries a `r = default`
fall-through disjunct — that is the honest reading of the code, not a defect of the
statement. None of them touches the `ErasureState`: they move only the reader's local
context, which is why they all conclude `s' = s` on the fall-through and hand the
continuation back at an *unconstrained* `ctx'`.

`run_mkAlt_ok` is the one with content: it pins the produced binder list to the same
length as the closed-over fvars, and the produced body to the `toBvar` fold that
`LeanToLambdaBox.lbClosed_foldl_zipIdx` computes the closedness level of.
-/

section Binders

variable {α : Type} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}

/-- `withLocalDecl` allocates a fresh fvar (state-preserving) and runs the continuation
under an extended local context. -/
theorem run_withLocalDecl_ok {nm : Name} {ty : Expr} {bi : BinderInfo}
    {k : FVarId → EraseM α} {s : ErasureState} {ctx : ErasureContext}
    {w : Void IO.RealWorld} {r : α} {s' : ErasureState} {w' : Void IO.RealWorld}
    (hrun : withLocalDecl nm ty bi k s ctx cctx ref w = .ok (r, s') w') :
    ∃ (x : FVarId) (ctx' : ErasureContext) (w₀ : Void IO.RealWorld),
      k x s ctx' cctx ref w₀ = .ok (r, s') w' := by
  unfold withLocalDecl at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨x, sx, wx, hfv, hk⟩ := hrun
  have hz := run_mkFreshFVarId_state _ _ cctx ref _ hfv
  subst hz
  rw [run_withReader] at hk
  exact ⟨x, _, _, hk⟩

theorem run_withLocalDef_ok {nm : Name} {ty val : Expr} {nd : Bool}
    {k : FVarId → EraseM α} {s : ErasureState} {ctx : ErasureContext}
    {w : Void IO.RealWorld} {r : α} {s' : ErasureState} {w' : Void IO.RealWorld}
    (hrun : withLocalDef nm ty val nd k s ctx cctx ref w = .ok (r, s') w') :
    ∃ (x : FVarId) (ctx' : ErasureContext) (w₀ : Void IO.RealWorld),
      k x s ctx' cctx ref w₀ = .ok (r, s') w' := by
  unfold withLocalDef at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨x, sx, wx, hfv, hk⟩ := hrun
  have hz := run_mkFreshFVarId_state _ _ cctx ref _ hfv
  subst hz
  rw [run_withReader] at hk
  exact ⟨x, _, _, hk⟩

/-- `lambdaMonocular`: either the input was not a `.lam` (the `unreachable!` fall-through,
which *succeeds* at `EraseM` and returns `default`), or the continuation ran under one
extra local declaration. -/
theorem run_lambdaMonocular_ok [Inhabited α] {e : Expr} {k : FVarId → Expr → EraseM α}
    {s : ErasureState} {ctx : ErasureContext} {w : Void IO.RealWorld} {r : α}
    {s' : ErasureState} {w' : Void IO.RealWorld}
    (hrun : lambdaMonocular e k s ctx cctx ref w = .ok (r, s') w') :
    (r = default ∧ s' = s ∧ w' = w) ∨
    ∃ (x : FVarId) (b : Expr) (ctx' : ErasureContext) (w₀ : Void IO.RealWorld),
      k x b s ctx' cctx ref w₀ = .ok (r, s') w' := by
  unfold lambdaMonocular at hrun
  split at hrun
  · obtain ⟨x, ctx', w₀, hk⟩ := run_withLocalDecl_ok hrun
    exact Or.inr ⟨x, _, ctx', w₀, hk⟩
  · rw [run_panicWithPosWithDecl] at hrun
    cases hrun
    exact Or.inl ⟨rfl, rfl, rfl⟩

theorem run_letMonocular_ok [Inhabited α] {e : Expr} {k : FVarId → Expr → Expr → EraseM α}
    {s : ErasureState} {ctx : ErasureContext} {w : Void IO.RealWorld} {r : α}
    {s' : ErasureState} {w' : Void IO.RealWorld}
    (hrun : letMonocular e k s ctx cctx ref w = .ok (r, s') w') :
    (r = default ∧ s' = s ∧ w' = w) ∨
    ∃ (x : FVarId) (v b : Expr) (ctx' : ErasureContext) (w₀ : Void IO.RealWorld),
      k x v b s ctx' cctx ref w₀ = .ok (r, s') w' := by
  unfold letMonocular at hrun
  split at hrun
  · obtain ⟨x, ctx', w₀, hk⟩ := run_withLocalDef_ok hrun
    exact Or.inr ⟨x, _, _, ctx', w₀, hk⟩
  · rw [run_panicWithPosWithDecl] at hrun
    cases hrun
    exact Or.inl ⟨rfl, rfl, rfl⟩

theorem run_forallMonocular_ok [Inhabited α] {ty : Expr} {k : FVarId → Expr → EraseM α}
    {s : ErasureState} {ctx : ErasureContext} {w : Void IO.RealWorld} {r : α}
    {s' : ErasureState} {w' : Void IO.RealWorld}
    (hrun : forallMonocular ty k s ctx cctx ref w = .ok (r, s') w') :
    (r = default ∧ s' = s ∧ w' = w) ∨
    ∃ (x : FVarId) (bt : Expr) (ctx' : ErasureContext) (w₀ : Void IO.RealWorld),
      k x bt s ctx' cctx ref w₀ = .ok (r, s') w' := by
  unfold forallMonocular at hrun
  split at hrun
  · obtain ⟨x, ctx', w₀, hk⟩ := run_withLocalDecl_ok hrun
    exact Or.inr ⟨x, _, ctx', w₀, hk⟩
  · rw [run_panicWithPosWithDecl] at hrun
    cases hrun
    exact Or.inl ⟨rfl, rfl, rfl⟩

theorem run_lambdaMonocularOrIntro_ok [Inhabited α] {e ty : Expr}
    {k : Expr → Expr → FVarId → EraseM α}
    {s : ErasureState} {ctx : ErasureContext} {w : Void IO.RealWorld} {r : α}
    {s' : ErasureState} {w' : Void IO.RealWorld}
    (hrun : lambdaMonocularOrIntro e ty k s ctx cctx ref w = .ok (r, s') w') :
    (r = default ∧ s' = s ∧ w' = w) ∨
    ∃ (e' bt : Expr) (x : FVarId) (ctx' : ErasureContext) (w₀ : Void IO.RealWorld),
      k e' bt x s ctx' cctx ref w₀ = .ok (r, s') w' := by
  unfold lambdaMonocularOrIntro at hrun
  rcases run_forallMonocular_ok hrun with ⟨h1, h2, h3⟩ | ⟨x, bt, ctx', w₀, hk⟩
  · exact Or.inl ⟨h1, h2, h3⟩
  · split at hk
    · exact Or.inr ⟨_, bt, x, ctx', w₀, hk⟩
    · exact Or.inr ⟨_, bt, x, ctx', w₀, hk⟩

/-- `lambdaOrIntroToArity`: either the type was not a deep enough `∀`-telescope (a
panic fall-through), or the continuation ran on exactly `arity` fresh fvars. -/
theorem run_lambdaOrIntroToArity_ok [Inhabited α] :
    ∀ (arity : Nat) {e ty : Expr} {k : Expr → List FVarId → EraseM α}
      {s : ErasureState} {ctx : ErasureContext} {w : Void IO.RealWorld} {r : α}
      {s' : ErasureState} {w' : Void IO.RealWorld},
      lambdaOrIntroToArity e ty arity k s ctx cctx ref w = .ok (r, s') w' →
      (r = default ∧ s' = s) ∨
      ∃ (e' : Expr) (xs : List FVarId) (ctx' : ErasureContext) (w₀ : Void IO.RealWorld),
        xs.length = arity ∧ k e' xs s ctx' cctx ref w₀ = .ok (r, s') w'
  | 0, e, ty, k, s, ctx, w, r, s', w', hrun =>
    Or.inr ⟨e, [], ctx, w, rfl, hrun⟩
  | m + 1, e, ty, k, s, ctx, w, r, s', w', hrun => by
    unfold lambdaOrIntroToArity at hrun
    rcases run_lambdaMonocularOrIntro_ok hrun with ⟨h1, h2, -⟩ | ⟨e', bt, x, ctx', w₀, hk⟩
    · exact Or.inl ⟨h1, h2⟩
    · rcases run_lambdaOrIntroToArity_ok m hk with ⟨h1, h2⟩ | ⟨e'', xs, ctx'', w₁, hlen, hk'⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨e'', x :: xs, ctx'', w₁, by simp [hlen], hk'⟩

/-! ### The λ□-side binder constructors -/

theorem run_fvar_to_name_ok {x : FVarId} {s : ErasureState} {ctx : ErasureContext}
    {w : Void IO.RealWorld} {r : BinderName} {s' : ErasureState} {w' : Void IO.RealWorld}
    (hrun : fvar_to_name x s ctx cctx ref w = .ok (r, s') w') : s' = s ∧ w' = w := by
  unfold fvar_to_name at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨c, sc, wc, hread, hrun⟩ := hrun
  rw [run_read] at hread
  cases hread
  split at hrun <;> (rw [run_pure] at hrun; cases hrun; exact ⟨rfl, rfl⟩)

theorem run_mkLambda_ok {x : FVarId} {body : LBTerm} {s : ErasureState}
    {ctx : ErasureContext} {w : Void IO.RealWorld} {t : LBTerm} {s' : ErasureState}
    {w' : Void IO.RealWorld}
    (hrun : mkLambda x body s ctx cctx ref w = .ok (t, s') w') :
    s' = s ∧ w' = w ∧ ∃ nm, t = .lambda nm (toBvar x 0 body) := by
  unfold mkLambda at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨nm, sn, wn, hnm, hrun⟩ := hrun
  obtain ⟨hs, hw⟩ := run_fvar_to_name_ok hnm
  subst hs
  subst hw
  rw [run_pure] at hrun
  cases hrun
  exact ⟨rfl, rfl, nm, rfl⟩

theorem run_mkLetIn_ok {x : FVarId} {val body : LBTerm} {s : ErasureState}
    {ctx : ErasureContext} {w : Void IO.RealWorld} {t : LBTerm} {s' : ErasureState}
    {w' : Void IO.RealWorld}
    (hrun : mkLetIn x val body s ctx cctx ref w = .ok (t, s') w') :
    s' = s ∧ w' = w ∧ ∃ nm, t = .letIn nm val (toBvar x 0 body) := by
  unfold mkLetIn at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨nm, sn, wn, hnm, hrun⟩ := hrun
  obtain ⟨hs, hw⟩ := run_fvar_to_name_ok hnm
  subst hs
  subst hw
  rw [run_pure] at hrun
  cases hrun
  exact ⟨rfl, rfl, nm, rfl⟩

theorem run_mkAlt_ok {xs : List FVarId} {body : LBTerm} {s : ErasureState}
    {ctx : ErasureContext} {w : Void IO.RealWorld} {r : List BinderName × LBTerm}
    {s' : ErasureState} {w' : Void IO.RealWorld}
    (hrun : mkAlt xs body s ctx cctx ref w = .ok (r, s') w') :
    s' = s ∧ w' = w ∧ r.1.length = xs.length ∧
      r.2 = xs.reverse.zipIdx.foldl (fun b p => toBvar p.1 p.2 b) body := by
  unfold mkAlt at hrun
  simp only [] at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨names, sn, wn, hnames, hrun⟩ := hrun
  have hlen := run_list_mapM_ok _ cctx ref
    (P := fun (pre : List FVarId) (outs : List BinderName) (s₂ : ErasureState)
        (w₂ : Void IO.RealWorld) => outs.length = pre.length ∧ s₂ = s ∧ w₂ = w)
    ⟨rfl, rfl, rfl⟩
    (fun _ y _ outs s₂ w₂ b s₃ w₃ _ hP hb => by
      obtain ⟨hl, hs, hw⟩ := hP
      subst hs
      subst hw
      obtain ⟨hs2, hw2⟩ := run_fvar_to_name_ok hb
      exact ⟨by simp [hl], hs2, hw2⟩)
    hnames
  obtain ⟨hlen', hs, hw⟩ := hlen
  rw [hs, hw] at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨bfin, sb, wb, hloop, hrun⟩ := hrun
  have hfold := run_list_forIn_ok' _ cctx ref
    (P := fun (pre : List (FVarId × Nat)) (b : LBTerm) (s₂ : ErasureState)
        (w₂ : Void IO.RealWorld) =>
      b = pre.foldl (fun b p => toBvar p.1 p.2 b) body ∧ s₂ = s ∧ w₂ = w)
    ⟨rfl, rfl, rfl⟩
    (fun pre y post acc s₂ w₂ b s₃ w₃ _ hP hb => by
      obtain ⟨hacc, hs, hw⟩ := hP
      subst hs
      subst hw
      rw [run_pure] at hb
      cases hb
      exact ⟨by rw [List.foldl_append, hacc]; rfl, rfl, rfl⟩)
    (fun pre y post acc s₂ w₂ b s₃ w₃ _ hP hb => by
      rw [run_pure] at hb
      exact nomatch hb)
    hloop
  obtain ⟨hb, hs2, hw2⟩ := hfold
  rw [hs2, hw2] at hrun
  rw [run_pure] at hrun
  cases hrun
  exact ⟨rfl, rfl, hlen', hb⟩

end Binders

end Erasure

