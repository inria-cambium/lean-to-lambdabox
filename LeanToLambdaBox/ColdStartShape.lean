import LeanToLambdaBox.EnvErasureNonrec
import LeanToLambdaBox.ErasesCorrectIota

/-!
# The cold-start registry invariant — shape half (slices S1, S1e)

`EnvErasureNonrec`/`EnvErasureRec` discharge *env-consistency from registration*: given
`RegisteredCtors`/`RegisteredCases`/`RegisteredCtorFieldsAll`/`RegisteredClosure*`, the
forward simulations' environment hypotheses follow. Those registration records are
still bare `Prop` premises, because nothing relates them to an actual `Erasure.erase`
run from the empty state.

This file builds the **shape half** of the missing link: a state invariant
`RegInvShape` that

* is **vacuously true at the empty state** (`RegInvShape.empty`), so a cold run can
  start from it;
* is **preserved by the registration primitives** — `addAxiom` (`RegInvShape.addAxiom`)
  and the cold branch of `register_inductive` (`RegInvShape.registerInd`) — using the
  *true* run shapes proved in `ErasureRun.lean` (`run_addAxiom_ok`,
  `run_register_inductive_cold_ok`), not an assumed state-preservation;
* **collapses at saturation** to the unscoped `RegisteredCtors` / `RegisteredCases` /
  `RegisteredCtorFieldsAll` / `NoFixEnv` / `ClosedEnv` the capstones ask for.

## Three design points, fixed here rather than later

**Scoped records.** The registration records quantify over *all* of `Γ`; a run part-way
through has only registered some of it. The `…On` variants restrict the quantifier by a
`dom : InductiveId → Prop` and collapse to the unscoped forms once `dom` covers `Γ`.
`RegInvShape` instantiates `dom` to `BlockRegistered s` — "the block's kername already
resolves to an `.inductiveDecl` in `s.gdecls`" — which makes the scoping *self-*evident
from the state and needs no extra bookkeeping.

**Key *coverage* is part of the invariant; key *distinctness* is not.** `LBTerm.envLookup`
is first-match-wins and every writer *prepends*, so a later registration can silently
shadow an earlier one. Slice S1 carried `KeysDistinct s.gdecls` as a field and took
per-call freshness as a side condition; slice S1e removed it, because **no** side
condition can save it: `RunClosed.nrc` is a bare state closure, so a predicate containing
`KeysDistinct` is closed under `nonrecConstState n t ·` only if `toKername n` is fresh at
*every* state the predicate admits — which is false at the state one such cons produces.
`ColdStartInduction.runClosed_keysDistinct_refuted` proves exactly that, and
`addAxiom`'s panic fall-through (it conses a *second* entry when the constant is already
registered) is an independent reason.

What is maintainable is `ConstKeysCovered`: every `.constantDecl` entry is filed under the
canonical kername of a constant the registry knows. It is preserved at every registration
site with no side condition at all, and it *yields* freshness exactly where the walk has
the guard for it — `RegInvShape.fresh_of_unregistered` turns "`n` is not registered here"
into "`toKername n` is fresh among the constant keys", modulo the naming side condition
`hkinj` (`Erasure.toKername` is not injective: `Name.num p k` and `Name.str p (toString k)`
collide). Freshness against *block* keys is a different matter and provably not available
in that form — see `mutualBlockKn_eq_toKername` at the end of this file.

**The `nofix` field is disjunctive from day one.** `NoFixEnvD` allows each stored
constant body to be `NoFix` *or* a literal `.fix defs j` — the two shapes
`visitMutual`'s non-recursive and recursive branches produce. Under the fix-free scope
the right disjunct is dead and `noFixEnv_of_noFixEnvD` collapses `NoFixEnvD` to
`NoFixEnv`; the recursion wall *populated* the right disjunct exactly as designed, with no
change to this structure — `RegInvShape.recConst` (slice S1c) carries the invariant across
`recConstState`, and `Erasure.run_rec_exit_ok` (slice S1e) reports the stored block's shape
so `rec_block_closed` supplies its closedness. (The `visitConst` fixvar bridge case landed
with slice W3.1 — motive 4 now derives `Erases.fixvar` on that branch.)
-/

namespace LeanToLambdaBox

open Lean Erasure

/-! ## `envLookup` stability under prepending (R12) -/

/-- No two entries of `E` share a kername, **modulo `Kername.beq`** — the comparison
`LBTerm.envLookup` actually uses. Propositional `≠` on `Kername` would be too weak:
`envLookup` dispatches on `Kername.beq`, so shadowing is governed by `beq`. -/
def KeysDistinct (E : GlobalDeclarations) : Prop :=
  E.Pairwise (fun p q => Kername.beq p.1 q.1 = false)

theorem KeysDistinct.nil : KeysDistinct [] := List.Pairwise.nil

theorem KeysDistinct.cons {p : Kername × GlobalDecl} {E : GlobalDeclarations}
    (hfresh : ∀ q ∈ E, Kername.beq p.1 q.1 = false) (h : KeysDistinct E) :
    KeysDistinct (p :: E) :=
  List.Pairwise.cons hfresh h

theorem KeysDistinct.of_cons {p : Kername × GlobalDecl} {E : GlobalDeclarations}
    (h : KeysDistinct (p :: E)) : KeysDistinct E :=
  (List.pairwise_cons.mp h).2

/-- **R12 — lookup stability under prepending.** An established `envLookup` survives any
number of *fresh* entries being consed in front of it. This is the lemma that lifts a
registration record proved at an intermediate state of the run to the final state. -/
theorem envLookup_append_of_fresh {pre E : GlobalDeclarations} {kn : Kername}
    {d : GlobalDecl} (h : LBTerm.envLookup E kn = some d)
    (hfresh : ∀ p ∈ pre, Kername.beq p.1 kn = false) :
    LBTerm.envLookup (pre ++ E) kn = some d := by
  induction pre with
  | nil => simpa using h
  | cons p rest ih =>
    have hp : Kername.beq p.1 kn = false := hfresh p List.mem_cons_self
    simp only [List.cons_append, LBTerm.envLookup, hp, Bool.false_eq_true, if_false]
    exact ih (fun q hq => hfresh q (List.mem_cons_of_mem p hq))

/-- `ModPath.beq` is reflexive. -/
theorem ModPath.beq_refl : ∀ mp : ModPath, ModPath.beq mp mp = true
  | .MPfile _ => by simp [ModPath.beq]
  | .MPdot mp _ => by simp [ModPath.beq, ModPath.beq_refl mp]

/-- `Kername.beq` — the comparison `LBTerm.envLookup` dispatches on — is reflexive.
Consumers need this to *find* the entry a registration step has just consed. -/
@[simp] theorem Kername.beq_refl (kn : Kername) : Kername.beq kn kn = true := by
  simp [Kername.beq, ModPath.beq_refl]

/-- Looking up the entry just consed. -/
@[simp] theorem envLookup_cons_self (kn : Kername) (d : GlobalDecl)
    (E : GlobalDeclarations) : LBTerm.envLookup ((kn, d) :: E) kn = some d := by
  simp [LBTerm.envLookup]

/-- A successful `envLookup` is witnessed by a member of the list whose key is
`beq`-equal to the queried kername. -/
theorem envLookup_mem {E : GlobalDeclarations} {kn : Kername} {d : GlobalDecl}
    (h : LBTerm.envLookup E kn = some d) :
    ∃ k, (k, d) ∈ E ∧ Kername.beq k kn = true := by
  induction E with
  | nil => exact absurd h (by simp [LBTerm.envLookup])
  | cons p rest ih =>
    obtain ⟨k, dd⟩ := p
    cases hk : Kername.beq k kn with
    | true =>
      simp only [LBTerm.envLookup, hk, if_true] at h
      cases h
      exact ⟨k, List.mem_cons_self, hk⟩
    | false =>
      simp only [LBTerm.envLookup, hk, Bool.false_eq_true, if_false] at h
      obtain ⟨k', hmem, hbeq⟩ := ih h
      exact ⟨k', List.mem_cons_of_mem _ hmem, hbeq⟩

/-! ## State extension

`StateLe` (the registries only grow, `gdecls` only gets prepended to) and `RunConcl` moved
to `ErasureRun.lean` with the cold-start S2 slice: `VisitExprRefines` — which this file
transitively imports — concludes them in every motive of the bridge induction. -/

/-! ## Scoped registration records -/

/-- The mutual blocks `E` has already registered. Used as the scoping domain of the
`…On` records: a partial run has only registered part of `Γ`. -/
def BlockRegistered (E : GlobalDeclarations) (iid : InductiveId) : Prop :=
  ∃ body : MutualInductiveBody,
    LBTerm.envLookup E iid.mutualBlockName = some (.inductiveDecl body)

/-- `RegisteredCtors`, restricted to the blocks in `dom`. -/
def RegisteredCtorsOn (Γ : ErasureCtx) (E : GlobalDeclarations)
    (dom : InductiveId → Prop) : Prop :=
  ∀ {cn : Name} {iid : InductiveId} {cidx : Nat},
    dom iid → Γ.ctors cn = some (iid, cidx) → RegisteredCtor Γ E cn iid cidx

/-- `RegisteredCases`, restricted to the blocks in `dom`. -/
def RegisteredCasesOn (Γ : ErasureCtx) (E : GlobalDeclarations)
    (dom : InductiveId → Prop) : Prop :=
  ∀ {con : Name} {iid : InductiveId} {numParams : Nat},
    dom iid → Γ.casesOns con = some (iid, numParams) →
    ∃ (body : MutualInductiveBody) (oib : OneInductiveBody),
      LBTerm.envLookup E iid.mutualBlockName = some (.inductiveDecl body) ∧
      body.bodies[iid.idx]? = some oib ∧
      body.npars = numParams ∧
      oib.propositional = false

/-- `RegisteredCtorFieldsAll`, restricted to the blocks in `dom`. -/
def RegisteredCtorFieldsOn (Γ : ErasureCtx) (E : GlobalDeclarations)
    (dom : InductiveId → Prop) : Prop :=
  ∀ {con : Name} {iid : InductiveId} {np : Nat},
    dom iid → Γ.casesOns con = some (iid, np) → RegisteredCtorFields Γ E iid

/-- Saturation: once `dom` covers every block `Γ` knows, the scoped record is the
unscoped one. -/
theorem registeredCtors_of_on {Γ : ErasureCtx} {E : GlobalDeclarations}
    {dom : InductiveId → Prop} (h : RegisteredCtorsOn Γ E dom)
    (hsat : ∀ {cn iid cidx}, Γ.ctors cn = some (iid, cidx) → dom iid) :
    RegisteredCtors Γ E :=
  fun hc => h (hsat hc) hc

theorem registeredCases_of_on {Γ : ErasureCtx} {E : GlobalDeclarations}
    {dom : InductiveId → Prop} (h : RegisteredCasesOn Γ E dom)
    (hsat : ∀ {con iid np}, Γ.casesOns con = some (iid, np) → dom iid) :
    RegisteredCases Γ E :=
  fun hc => h (hsat hc) hc

theorem registeredCtorFieldsAll_of_on {Γ : ErasureCtx} {E : GlobalDeclarations}
    {dom : InductiveId → Prop} (h : RegisteredCtorFieldsOn Γ E dom)
    (hsat : ∀ {con iid np}, Γ.casesOns con = some (iid, np) → dom iid) :
    RegisteredCtorFieldsAll Γ E :=
  fun hc => h (hsat hc) hc

/-! ## The disjunctive `NoFixEnv` (the recursion-wall interface) -/

/-- **`NoFixEnv`, split by the two shapes `visitMutual` can store.** Its non-recursive
branch stores a plain `visitExpr` output (`NoFix`); its recursive branch stores exactly
`.fix defs j`. Carrying the disjunction means the recursion wall can populate the right
disjunct without restructuring `RegInvShape`. -/
def NoFixEnvD (E : GlobalDeclarations) : Prop :=
  ∀ {kn : Kername} {body' : LBTerm},
    LBTerm.envLookup E kn = some (.constantDecl ⟨some body'⟩) →
    NoFix body' ∨ ∃ (defs : List (@FixDef LBTerm)) (j : Nat), body' = .fix defs j

theorem NoFixEnvD.of_noFixEnv {E : GlobalDeclarations} (h : NoFixEnv E) : NoFixEnvD E :=
  fun hl => Or.inl (h hl)

/-- Collapse under the fix-free scope: if the run stored no `.fix` body, the disjunction
degenerates to `NoFixEnv`. -/
theorem noFixEnv_of_noFixEnvD {E : GlobalDeclarations} (h : NoFixEnvD E)
    (hnorec : ∀ {kn : Kername} {defs : List (@FixDef LBTerm)} {j : Nat},
      LBTerm.envLookup E kn ≠ some (.constantDecl ⟨some (.fix defs j)⟩)) :
    NoFixEnv E := by
  intro kn body' hl
  rcases h hl with hnf | ⟨defs, j, rfl⟩
  · exact hnf
  · exact absurd hl hnorec

/-! ## Constant-key coverage

The key discipline the walk really maintains. Every `.constantDecl` entry of `gdecls` was
consed by `addAxiom`, by `visitMutual`'s non-recursive exit, or by its recursive block
loop — and all three cons `(toKername n, …)` while inserting `n` into `constants`, in that
one step. So the constant keys are *covered* by the registry, with no side condition.

Coverage is what a freshness argument runs on: a name the registry does not know cannot
already own a constant key (`RegInvShape.fresh_of_unregistered`). -/

/-- Every `.constantDecl` entry of `s.gdecls` is filed under the canonical kername of a
constant `s.constants` knows. -/
def ConstKeysCovered (s : ErasureState) : Prop :=
  ∀ {kn : Kername} {cb : ConstantBody}, (kn, GlobalDecl.constantDecl cb) ∈ s.gdecls →
    ∃ m : Name, kn = toKername m ∧ (s.constants.get? m).isSome

/-- The key just inserted is known. -/
theorem constants_isSome_insert_self (mp : Std.HashMap Name Kername) (n : Name)
    (k : Kername) : ((mp.insert n k).get? n).isSome := by
  rw [Std.HashMap.get?_insert]
  simp

/-- Insertion does not forget. -/
theorem constants_isSome_insert {mp : Std.HashMap Name Kername} {n m : Name} {k : Kername}
    (h : (mp.get? m).isSome) : ((mp.insert n k).get? m).isSome := by
  rw [Std.HashMap.get?_insert]
  split
  · simp
  · exact h

/-- Coverage across a constant cons: the new entry is covered by the name being inserted,
the old ones survive because the registry only grows. -/
theorem ConstKeysCovered.cons {s : ErasureState} {n : Name} {cb : ConstantBody}
    (h : ConstKeysCovered s) :
    ConstKeysCovered { s with
      constants := s.constants.insert n (toKername n),
      gdecls := (toKername n, .constantDecl cb) :: s.gdecls } := by
  intro kn cb' hmem
  rcases List.mem_cons.mp hmem with heq | hmem'
  · cases heq
    exact ⟨n, rfl, constants_isSome_insert_self _ _ _⟩
  · obtain ⟨m, hk, hm⟩ := h hmem'
    exact ⟨m, hk, constants_isSome_insert hm⟩

/-! ## The invariant -/

/-- **The cold-start registry invariant, shape half.** Everything a partial
`Erasure.erase` run has registered is `Γ`-consistent, key-distinct, and target-shape
sound. Every field is *vacuous* at the empty state (`RegInvShape.empty`).

Deliberately absent: any `Erases` content. That is the δ half (`RegInvDelta`, slice S3),
kept separate so the shape argument is independent of the term bridge. -/
structure RegInvShape (Γ : ErasureCtx) (s : ErasureState) : Prop where
  /-- Registered kernames agree with `Γ` (SOUNDNESS — the relaxation of the warm
  bridge's once completeness-flavoured `BridgeInv.consts`, which slice S2 relaxed to
  exactly this statement). -/
  kn : ∀ {n : Name} {k : Kername}, s.constants.get? n = some k → k = Γ.constants n
  /-- Constant-key coverage — the maintainable key discipline, and what freshness for a
  not-yet-registered name is read off (`RegInvShape.fresh_of_unregistered`). It replaces
  slice S1's `keys : KeysDistinct s.gdecls`, which no state predicate can carry along the
  walk (`ColdStartInduction.runClosed_keysDistinct_refuted`). -/
  cover : ConstKeysCovered s
  /-- The three ι/data registration records, scoped to the blocks already registered. -/
  ctors : RegisteredCtorsOn Γ s.gdecls (BlockRegistered s.gdecls)
  cases : RegisteredCasesOn Γ s.gdecls (BlockRegistered s.gdecls)
  fields : RegisteredCtorFieldsOn Γ s.gdecls (BlockRegistered s.gdecls)
  /-- Target-body shape facts, currently premises of D3/D3ι. Disjunctive: see
  `NoFixEnvD`. -/
  nofix : NoFixEnvD s.gdecls
  closed : ClosedEnv s.gdecls

/-- **Cold start.** Every field is vacuous at the default `ErasureState`
(`Erasure.run`'s initial state: `constants := ∅`, `inductives := ∅`, `gdecls := []`). -/
theorem RegInvShape.empty (Γ : ErasureCtx) : RegInvShape Γ {} where
  kn := by intro n k hk; simp at hk
  cover := by intro kn cb hmem; simp at hmem
  ctors := by intro cn iid cidx hdom _; obtain ⟨body, hb⟩ := hdom; simp [LBTerm.envLookup] at hb
  cases := by intro con iid np hdom _; obtain ⟨body, hb⟩ := hdom; simp [LBTerm.envLookup] at hb
  fields := by intro con iid np hdom _; obtain ⟨body, hb⟩ := hdom; simp [LBTerm.envLookup] at hb
  nofix := by intro kn body' hl; simp [LBTerm.envLookup] at hl
  closed := by intro kn body hl; simp [LBTerm.envLookup] at hl

/-- The `Γ`-side saturation facts that turn the scoped invariant into the capstones'
unscoped premise set. -/
theorem RegInvShape.registeredCtors {Γ : ErasureCtx} {s : ErasureState}
    (h : RegInvShape Γ s)
    (hsat : ∀ {cn iid cidx}, Γ.ctors cn = some (iid, cidx) → BlockRegistered s.gdecls iid) :
    RegisteredCtors Γ s.gdecls :=
  registeredCtors_of_on h.ctors hsat

theorem RegInvShape.registeredCases {Γ : ErasureCtx} {s : ErasureState}
    (h : RegInvShape Γ s)
    (hsat : ∀ {con iid np}, Γ.casesOns con = some (iid, np) → BlockRegistered s.gdecls iid) :
    RegisteredCases Γ s.gdecls :=
  registeredCases_of_on h.cases hsat

theorem RegInvShape.registeredCtorFieldsAll {Γ : ErasureCtx} {s : ErasureState}
    (h : RegInvShape Γ s)
    (hsat : ∀ {con iid np}, Γ.casesOns con = some (iid, np) → BlockRegistered s.gdecls iid) :
    RegisteredCtorFieldsAll Γ s.gdecls :=
  registeredCtorFieldsAll_of_on h.fields hsat

theorem RegInvShape.closedEnv {Γ : ErasureCtx} {s : ErasureState} (h : RegInvShape Γ s) :
    ClosedEnv s.gdecls := h.closed

theorem RegInvShape.noFixEnv {Γ : ErasureCtx} {s : ErasureState} (h : RegInvShape Γ s)
    (hnorec : ∀ {kn : Kername} {defs : List (@FixDef LBTerm)} {j : Nat},
      LBTerm.envLookup s.gdecls kn ≠ some (.constantDecl ⟨some (.fix defs j)⟩)) :
    NoFixEnv s.gdecls :=
  noFixEnv_of_noFixEnvD h.nofix hnorec

/-! ## Step lemmas: the invariant travels along the registration primitives

These are the *from-the-run* half of slice S1: the environment plumbing (key coverage,
the target-body shape facts, and preservation of every already-established block record)
is **proved** from `ErasureRun.lean`'s run shapes. Note what is *not* needed: a freshness
side condition. A block record is scoped to `BlockRegistered s.gdecls`, which is
re-evaluated at the current state, so a `.constantDecl` cons cannot shadow a block it
still resolves (`blockRegistered_cons_constantDecl` reads the key inequality *off* the
scoping), and a second `.inductiveDecl` for the same block falls to the `hnew…` premises.
Freshness was only ever needed for the `keys` field slice S1e removed.

What each step lemma still takes as a premise, besides `hknames`, is one thing:

* **`Γ`-agreement for the newly registered block** — that `Γ`'s recorded
  arity/field/parameter data is the data the call computed. That is the
  `RegBridgeHyps` obligation of slice S4; nothing about the run can supply it, since
  `Γ` is a parameter.
-/

/-- Inversion for a lookup through one consed entry. -/
theorem envLookup_cons_inv {kn₀ : Kername} {d : GlobalDecl} {E : GlobalDeclarations}
    {kn : Kername} {dd : GlobalDecl}
    (h : LBTerm.envLookup ((kn₀, d) :: E) kn = some dd) :
    (Kername.beq kn₀ kn = true ∧ dd = d) ∨
    (Kername.beq kn₀ kn = false ∧ LBTerm.envLookup E kn = some dd) := by
  cases hk : Kername.beq kn₀ kn with
  | true =>
    simp only [LBTerm.envLookup, hk, if_true] at h
    exact Or.inl ⟨rfl, (Option.some.inj h).symm⟩
  | false =>
    simp only [LBTerm.envLookup, hk, Bool.false_eq_true, if_false] at h
    exact Or.inr ⟨rfl, h⟩

/-- Passing a lookup through one consed entry with a different key. -/
theorem envLookup_cons_of_ne {kn₀ : Kername} {d : GlobalDecl} {E : GlobalDeclarations}
    {kn : Kername} {dd : GlobalDecl} (hne : Kername.beq kn₀ kn = false)
    (h : LBTerm.envLookup E kn = some dd) :
    LBTerm.envLookup ((kn₀, d) :: E) kn = some dd :=
  envLookup_append_of_fresh (pre := [(kn₀, d)]) h (by simpa using hne)

/-- A `.constantDecl` entry can neither create nor disturb a block registration. -/
theorem blockRegistered_cons_constantDecl {kn₀ : Kername} {cb : ConstantBody}
    {E : GlobalDeclarations} {iid : InductiveId}
    (h : BlockRegistered ((kn₀, .constantDecl cb) :: E) iid) :
    Kername.beq kn₀ iid.mutualBlockName = false ∧ BlockRegistered E iid := by
  obtain ⟨body, hb⟩ := h
  rcases envLookup_cons_inv hb with ⟨-, hd⟩ | ⟨hne, hpass⟩
  · exact absurd hd (by simp)
  · exact ⟨hne, ⟨body, hpass⟩⟩

/-- Transport of a per-constructor registration record across one consed entry. -/
theorem RegisteredCtor.cons {Γ : ErasureCtx} {kn₀ : Kername} {d : GlobalDecl}
    {E : GlobalDeclarations} {cn : Name} {iid : InductiveId} {cidx : Nat}
    (hne : Kername.beq kn₀ iid.mutualBlockName = false)
    (h : RegisteredCtor Γ E cn iid cidx) :
    RegisteredCtor Γ ((kn₀, d) :: E) cn iid cidx := by
  obtain ⟨body, oib, cb, hlk, hbod, hctor, harity⟩ := h
  exact ⟨body, oib, cb, envLookup_cons_of_ne hne hlk, hbod, hctor, harity⟩

theorem RegisteredCtorFields.cons {Γ : ErasureCtx} {kn₀ : Kername} {d : GlobalDecl}
    {E : GlobalDeclarations} {iid : InductiveId}
    (hne : Kername.beq kn₀ iid.mutualBlockName = false)
    (h : RegisteredCtorFields Γ E iid) :
    RegisteredCtorFields Γ ((kn₀, d) :: E) iid := by
  obtain ⟨body, oib, hlk, hbod, hfields⟩ := h
  exact ⟨body, oib, envLookup_cons_of_ne hne hlk, hbod, hfields⟩

/-- **`RegInvShape` is preserved by `addAxiom`.** The post-state is the one
`Erasure.run_addAxiom_ok` computes — *including* the panic fall-through, so this holds
whether or not the constant was already registered. (With slice S1's `keys` field it did
*not*: on the panic path a second entry under the same key is consed. That is one of the
two reasons the field is gone.)

The only premise is `hΓ`: `Γ` files this constant under its canonical kername (the
`hknames` premise of the cold-start theorem). Every other field is discharged outright:
the new entry is a `.constantDecl` with a `none` body, so it can neither register a block
nor carry a `NoFix`/`LBClosed` obligation, and its key is covered by the very name being
inserted. -/
theorem RegInvShape.addAxiom {Γ : ErasureCtx} {s : ErasureState} {n : Name}
    (h : RegInvShape Γ s) (hΓ : Γ.constants n = toKername n) :
    RegInvShape Γ (addAxiomState n s) where
  kn := by
    intro m k hm
    simp only [addAxiomState] at hm
    rw [Std.HashMap.get?_insert] at hm
    split at hm
    · rename_i heq
      cases hm
      have hnm : n = m := by simpa using heq
      subst hnm
      exact hΓ.symm
    · exact h.kn hm
  cover := ConstKeysCovered.cons h.cover
  ctors := by
    intro cn iid cidx hdom hc
    obtain ⟨hne, hdom'⟩ := blockRegistered_cons_constantDecl hdom
    exact (h.ctors hdom' hc).cons hne
  cases := by
    intro con iid np hdom hc
    obtain ⟨hne, hdom'⟩ := blockRegistered_cons_constantDecl hdom
    obtain ⟨body, oib, hlk, hbod, hnp, hprop⟩ := h.cases hdom' hc
    exact ⟨body, oib, envLookup_cons_of_ne hne hlk, hbod, hnp, hprop⟩
  fields := by
    intro con iid np hdom hc
    obtain ⟨hne, hdom'⟩ := blockRegistered_cons_constantDecl hdom
    exact (h.fields hdom' hc).cons hne
  nofix := by
    intro kn body' hl
    rcases envLookup_cons_inv hl with ⟨-, hd⟩ | ⟨-, hpass⟩
    · exact absurd hd (by simp)
    · exact h.nofix hpass
  closed := by
    intro kn body hl
    rcases envLookup_cons_inv hl with ⟨-, hd⟩ | ⟨-, hpass⟩
    · exact absurd hd (by simp)
    · exact h.closed hpass

/-! ### Travelling along an axiom-only prefix

`register_inductive`'s cold branch may emit an `addAxiom` per `@[extern]` constructor
before consing the block. `Erasure.run_register_inductive_cold_ok` reports that as a
`ConstExt`, whose `gdecls` clause says the prefix consists entirely of axiom entries
**and names their keys** — the S1e strengthening of `ConstExt`, without which coverage
could not cross a `register_inductive` call. `RegInvShape.constExt` walks the invariant
across such a prefix in one step. -/

/-- Every entry of `pre` is an axiom declaration. -/
def AxiomPrefix (pre : GlobalDeclarations) : Prop :=
  ∀ p ∈ pre, p.2 = GlobalDecl.constantDecl ⟨none⟩

theorem blockRegistered_append_axioms {pre E : GlobalDeclarations} {iid : InductiveId}
    (hax : AxiomPrefix pre) (h : BlockRegistered (pre ++ E) iid) :
    (∀ p ∈ pre, Kername.beq p.1 iid.mutualBlockName = false) ∧ BlockRegistered E iid := by
  induction pre with
  | nil => exact ⟨by simp, by simpa using h⟩
  | cons p rest ih =>
    obtain ⟨k, d⟩ := p
    have hd : d = GlobalDecl.constantDecl ⟨none⟩ := hax _ List.mem_cons_self
    subst hd
    obtain ⟨hne, h'⟩ := blockRegistered_cons_constantDecl (by simpa using h)
    obtain ⟨hfr, hbr⟩ := ih (fun q hq => hax q (List.mem_cons_of_mem _ hq)) h'
    refine ⟨?_, hbr⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · exact hne
    · exact hfr q hq'

theorem envLookup_append_axioms_body {pre E : GlobalDeclarations} {kn : Kername}
    {body' : LBTerm} (hax : AxiomPrefix pre)
    (h : LBTerm.envLookup (pre ++ E) kn = some (.constantDecl ⟨some body'⟩)) :
    LBTerm.envLookup E kn = some (.constantDecl ⟨some body'⟩) := by
  induction pre with
  | nil => simpa using h
  | cons p rest ih =>
    obtain ⟨k, d⟩ := p
    have hd : d = GlobalDecl.constantDecl ⟨none⟩ := hax _ List.mem_cons_self
    subst hd
    rcases envLookup_cons_inv (by simpa using h) with ⟨-, hdd⟩ | ⟨-, hpass⟩
    · exact absurd hdd (by simp)
    · exact ih (fun q hq => hax q (List.mem_cons_of_mem _ hq)) hpass

/-- **`RegInvShape` travels along an axiom-only state extension** — the `ConstExt`
that `Erasure.run_register_inductive_cold_ok` (and `Erasure.run_addAxiom_ok`) report.

`hΓ` is `hknames`; canonicity of the extended constant registry comes from
`ConstExt.canon`, and coverage of the prefix's own keys from the strengthened
`ConstExt.gdecls`. No side condition. -/
theorem RegInvShape.constExt {Γ : ErasureCtx} {s s' : ErasureState}
    (h : RegInvShape Γ s) (hext : ConstExt s s')
    (hΓ : ∀ n : Name, Γ.constants n = toKername n) : RegInvShape Γ s' := by
  obtain ⟨pre, hpre, hax⟩ := hext.gdecls
  have haxp : AxiomPrefix pre := fun p hp => (hax p hp).1
  have hcanon : CanonicalConstants s' :=
    hext.canon (fun {n} {k} hk => (h.kn hk).trans (hΓ n))
  have hcover : ConstKeysCovered s' := by
    intro kn cb hmem
    rw [hpre] at hmem
    rcases List.mem_append.mp hmem with hp | hp
    · exact (hax _ hp).2
    · obtain ⟨m, hk, hm⟩ := h.cover hp
      exact ⟨m, hk, hext.dom hm⟩
  have hlift : ∀ {iid : InductiveId}, BlockRegistered s'.gdecls iid →
      (∀ p ∈ pre, Kername.beq p.1 iid.mutualBlockName = false) ∧
        BlockRegistered s.gdecls iid := by
    intro iid hd
    rw [hpre] at hd
    exact blockRegistered_append_axioms haxp hd
  refine ⟨fun {n} {k} hk => (hcanon hk).trans (hΓ n).symm, hcover, ?_, ?_, ?_, ?_, ?_⟩
  · intro cn iid cidx hdom hc
    obtain ⟨hfr, hdom'⟩ := hlift hdom
    obtain ⟨body, oib, cb, hlk, hbod, hctor, harity⟩ := h.ctors hdom' hc
    exact ⟨body, oib, cb, by rw [hpre]; exact envLookup_append_of_fresh hlk hfr,
      hbod, hctor, harity⟩
  · intro con iid np hdom hc
    obtain ⟨hfr, hdom'⟩ := hlift hdom
    obtain ⟨body, oib, hlk, hbod, hnp, hprop⟩ := h.cases hdom' hc
    exact ⟨body, oib, by rw [hpre]; exact envLookup_append_of_fresh hlk hfr, hbod, hnp, hprop⟩
  · intro con iid np hdom hc
    obtain ⟨hfr, hdom'⟩ := hlift hdom
    obtain ⟨body, oib, hlk, hbod, hfields⟩ := h.fields hdom' hc
    exact ⟨body, oib, by rw [hpre]; exact envLookup_append_of_fresh hlk hfr, hbod, hfields⟩
  · intro kn body' hl
    rw [hpre] at hl
    exact h.nofix (envLookup_append_axioms_body haxp hl)
  · intro kn body hl
    rw [hpre] at hl
    exact h.closed (envLookup_append_axioms_body haxp hl)

/-- **`RegInvShape` is preserved by the block cons of a cold `register_inductive`.**

The state is the one `Erasure.run_register_inductive_cold_ok` computes
(`registerIndState`), applied at the post-`ConstExt` state `sM`. Everything about the
*previously* registered blocks and about the target-body shape facts is discharged
outright — the new entry is an `.inductiveDecl`, so it carries no `NoFix`/`LBClosed`
obligation and no coverage obligation, and a block whose *current* registration goes
through the new entry is exactly a block the `hnew…` premises speak about. The three
`hnew…` premises are the `Γ`-agreement for the block just registered: slice S4's
`RegBridgeHyps` obligation, isolated here to exactly one place. -/
theorem RegInvShape.registerInd {Γ : ErasureCtx} {sM : ErasureState}
    {indinfo : InductiveVal} {bodies : List OneInductiveBody}
    (h : RegInvShape Γ sM)
    (hnewC : ∀ {cn : Name} {iid : InductiveId} {cidx : Nat},
      Kername.beq (mutualBlockKn indinfo) iid.mutualBlockName = true →
      Γ.ctors cn = some (iid, cidx) →
      RegisteredCtor Γ (registerIndState indinfo bodies sM).gdecls cn iid cidx)
    (hnewK : ∀ {con : Name} {iid : InductiveId} {np : Nat},
      Kername.beq (mutualBlockKn indinfo) iid.mutualBlockName = true →
      Γ.casesOns con = some (iid, np) →
      ∃ (body : MutualInductiveBody) (oib : OneInductiveBody),
        LBTerm.envLookup (registerIndState indinfo bodies sM).gdecls iid.mutualBlockName
          = some (.inductiveDecl body) ∧
        body.bodies[iid.idx]? = some oib ∧ body.npars = np ∧ oib.propositional = false)
    (hnewF : ∀ {con : Name} {iid : InductiveId} {np : Nat},
      Kername.beq (mutualBlockKn indinfo) iid.mutualBlockName = true →
      Γ.casesOns con = some (iid, np) →
      RegisteredCtorFields Γ (registerIndState indinfo bodies sM).gdecls iid) :
    RegInvShape Γ (registerIndState indinfo bodies sM) where
  kn := h.kn
  cover := by
    intro kn cb hmem
    rcases List.mem_cons.mp hmem with heq | hmem'
    · exact absurd heq (by simp)
    · exact h.cover hmem'
  ctors := by
    intro cn iid cidx hdom hc
    cases hb : Kername.beq (mutualBlockKn indinfo) iid.mutualBlockName with
    | true => exact hnewC hb hc
    | false =>
      obtain ⟨body, hlk⟩ := hdom
      rcases envLookup_cons_inv hlk with ⟨hb', -⟩ | ⟨-, hpass⟩
      · exact absurd (hb'.symm.trans hb) (by simp)
      · exact (h.ctors ⟨body, hpass⟩ hc).cons hb
  cases := by
    intro con iid np hdom hc
    cases hb : Kername.beq (mutualBlockKn indinfo) iid.mutualBlockName with
    | true => exact hnewK hb hc
    | false =>
      obtain ⟨body0, hlk⟩ := hdom
      rcases envLookup_cons_inv hlk with ⟨hb', -⟩ | ⟨-, hpass⟩
      · exact absurd (hb'.symm.trans hb) (by simp)
      · obtain ⟨body, oib, hlk', hbod, hnp, hprop⟩ := h.cases ⟨body0, hpass⟩ hc
        exact ⟨body, oib, envLookup_cons_of_ne hb hlk', hbod, hnp, hprop⟩
  fields := by
    intro con iid np hdom hc
    cases hb : Kername.beq (mutualBlockKn indinfo) iid.mutualBlockName with
    | true => exact hnewF hb hc
    | false =>
      obtain ⟨body, hlk⟩ := hdom
      rcases envLookup_cons_inv hlk with ⟨hb', -⟩ | ⟨-, hpass⟩
      · exact absurd (hb'.symm.trans hb) (by simp)
      · exact (h.fields ⟨body, hpass⟩ hc).cons hb
  nofix := by
    intro kn body' hl
    rcases envLookup_cons_inv hl with ⟨-, hd⟩ | ⟨-, hpass⟩
    · exact absurd hd (by simp)
    · exact h.nofix hpass
  closed := by
    intro kn body hl
    rcases envLookup_cons_inv hl with ⟨-, hd⟩ | ⟨-, hpass⟩
    · exact absurd hd (by simp)
    · exact h.closed hpass

/-! ## From the run

The two step lemmas above, driven by the real run shapes rather than by a
hand-supplied post-state. These are the S1 statements a cold-start argument consumes:
"if the invariant held before the call and the call succeeded, it holds after, and the
state only grew". -/

/-- **From the run — `addAxiom`.** -/
theorem RegInvShape.addAxiom_run {Γ : ErasureCtx} {n : Name} {s : ErasureState}
    {ctx : ErasureContext} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    {w : Void IO.RealWorld} {u : Unit} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (h : RegInvShape Γ s) (hΓ : Γ.constants n = toKername n)
    (hrun : Erasure.addAxiom n s ctx cctx ref w = .ok (u, s₁) w₁) :
    RegInvShape Γ s₁ ∧ StateLe s s₁ ∧ w₁ = w := by
  obtain ⟨hst, hw⟩ := run_addAxiom_ok hrun
  subst hst
  exact ⟨h.addAxiom hΓ,
    ⟨(AxiomExt.addAxiom n s).dom, id, ⟨[(toKername n, .constantDecl ⟨none⟩)], rfl⟩⟩, hw⟩

/-- **From the run — `register_inductive`, both branches.** The hit branch preserves
the state outright (`Erasure.run_register_inductive_hit_ok`); the cold branch is walked
by `RegInvShape.constExt` (over the `@[extern]`-constructor axiom prefix) followed by
`RegInvShape.registerInd` (the block cons).

`hΓ`/`hnew…` are as in the step lemmas; there is no freshness side condition left. -/
theorem RegInvShape.register_inductive_run {Γ : ErasureCtx} {indinfo : InductiveVal}
    {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {r : InductiveId × InductiveArgMasks} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (h : RegInvShape Γ s) (hΓ : ∀ n : Name, Γ.constants n = toKername n)
    (hnewC : ∀ {cn : Name} {iid : InductiveId} {cidx : Nat},
      Kername.beq (mutualBlockKn indinfo) iid.mutualBlockName = true →
      Γ.ctors cn = some (iid, cidx) → RegisteredCtor Γ s₁.gdecls cn iid cidx)
    (hnewK : ∀ {con : Name} {iid : InductiveId} {np : Nat},
      Kername.beq (mutualBlockKn indinfo) iid.mutualBlockName = true →
      Γ.casesOns con = some (iid, np) →
      ∃ (body : MutualInductiveBody) (oib : OneInductiveBody),
        LBTerm.envLookup s₁.gdecls iid.mutualBlockName = some (.inductiveDecl body) ∧
        body.bodies[iid.idx]? = some oib ∧ body.npars = np ∧ oib.propositional = false)
    (hnewF : ∀ {con : Name} {iid : InductiveId} {np : Nat},
      Kername.beq (mutualBlockKn indinfo) iid.mutualBlockName = true →
      Γ.casesOns con = some (iid, np) → RegisteredCtorFields Γ s₁.gdecls iid)
    (hrun : Erasure.register_inductive indinfo s ctx cctx ref w = .ok (r, s₁) w₁) :
    RegInvShape Γ s₁ ∧ StateLe s s₁ := by
  cases hi : s.inductives.get? indinfo.name with
  | some rc0 =>
    obtain ⟨-, hs, -⟩ := run_register_inductive_hit_ok hi hrun
    subst hs
    exact ⟨h, StateLe.rfl' _⟩
  | none =>
    obtain ⟨bodies, sM, hs1, hr, hlen, hext, hgrow, hreg⟩ :=
      run_register_inductive_cold_ok hi hrun
    clear hr hlen hreg
    subst hs1
    have hM : RegInvShape Γ sM := h.constExt hext hΓ
    refine ⟨hM.registerInd hnewC hnewK hnewF, ?_⟩
    obtain ⟨pre, hpre, -⟩ := hext.gdecls
    refine ⟨hext.dom, hgrow, ⟨(mutualBlockKn indinfo,
      GlobalDecl.inductiveDecl { npars := indinfo.numParams, bodies := bodies }) :: pre, ?_⟩⟩
    show ((mutualBlockKn indinfo, _) :: sM.gdecls) = _
    rw [List.cons_append, ← hpre]

/-! ## What the shape induction still owes: the output-shape motives

The one registration site slice S1 does **not** cover is `visitMutual`'s non-recursive
constant cons, `(toKername n, .constantDecl ⟨some t⟩) :: s.gdecls`, where `t` is the
sub-`visitExpr` output. The lemma below pins down exactly why: at that cons the
`nofix`/`closed` fields of `RegInvShape` are *equivalent* to the corresponding
output-shape facts about `t`, so they cannot be discharged by any amount of state
reasoning — they need an induction over the `visitExpr` family's *results*.

This corrects a scoping claim in the wall design, which lists those output-shape
motives (`NoBlock`/`NoFix`/`LBClosed` for every `visitExpr` output — "R11") as an
*optional* extra riding along with S1 or S2. They are a **prerequisite**: without
`NoFix t` the `nofix` field cannot be preserved, and the disjunctive form does not help,
because `visitExpr` never returns a `.fix` (so the right disjunct is unavailable and
`NoFix t` is forced). Likewise `closed` needs `LBClosed t 0`. -/

theorem regInvShape_nonrec_cons_iff {Γ : ErasureCtx} {s : ErasureState} {n : Name}
    {t : LBTerm} (h : RegInvShape Γ s) :
    (NoFixEnvD ((toKername n, .constantDecl ⟨some t⟩) :: s.gdecls) ↔
        (NoFix t ∨ ∃ (defs : List (@FixDef LBTerm)) (j : Nat), t = .fix defs j)) ∧
    (ClosedEnv ((toKername n, .constantDecl ⟨some t⟩) :: s.gdecls) ↔ LBClosed t 0) := by
  constructor
  · constructor
    · intro hd
      exact hd (envLookup_cons_self _ _ _)
    · intro ht kn body' hl
      rcases envLookup_cons_inv hl with ⟨-, hdd⟩ | ⟨-, hpass⟩
      · cases hdd; exact ht
      · exact h.nofix hpass
  · constructor
    · intro hd
      exact hd (envLookup_cons_self _ _ _)
    · intro ht kn body hl
      rcases envLookup_cons_inv hl with ⟨-, hdd⟩ | ⟨-, hpass⟩
      · cases hdd; exact ht
      · exact h.closed hpass

/-! ### The two remaining `visitMutual` exits

`Erasure.run_visitMutual_ok` (R7) discharges a state predicate through `visitMutual`
given one closure lemma per exit. Two of the four are already above (`addAxiom`, and
`register_inductive` is not on this path); the inlining-bookkeeping exit and the
non-recursive constant exit are here, and the recursive exit (`RegInvShape` under
`Erasure.recConstState`) closes the section. -/

/-- **The inlining-bookkeeping exit.** `RegInvShape` mentions only `constants` and
`gdecls`, so the `inlinings` cons is invisible to it — which is the formal counterpart
of `Program` dropping that field (`erase` returns `s.inlinings` separately). -/
theorem RegInvShape.inlinings {Γ : ErasureCtx} {s : ErasureState} {kn : Kername}
    (h : RegInvShape Γ s) : RegInvShape Γ { s with inlinings := kn :: s.inlinings } :=
  ⟨h.kn, h.cover, h.ctors, h.cases, h.fields, h.nofix, h.closed⟩

/-- **The non-recursive constant exit.** The stored body is a `visitExpr` output, so its
`NoFix`/`LBClosed` obligations (`regInvShape_nonrec_cons_iff`) must be supplied — that is
`hnf`/`hcl`, the output-shape facts `LeanToLambdaBox.OutputShape` and the (still open)
result induction produce. Everything else mirrors `RegInvShape.addAxiom`. -/
theorem RegInvShape.constCons {Γ : ErasureCtx} {s : ErasureState} {n : Name} {t : LBTerm}
    (h : RegInvShape Γ s) (hΓ : Γ.constants n = toKername n)
    (hnf : NoFix t ∨ ∃ (defs : List (@FixDef LBTerm)) (j : Nat), t = .fix defs j)
    (hcl : LBClosed t 0) :
    RegInvShape Γ (nonrecConstState n t s) where
  kn := by
    intro m k hm
    simp only [nonrecConstState] at hm
    rw [Std.HashMap.get?_insert] at hm
    split at hm
    · rename_i heq
      cases hm
      have hnm : n = m := by simpa using heq
      subst hnm
      exact hΓ.symm
    · exact h.kn hm
  cover := ConstKeysCovered.cons h.cover
  ctors := by
    intro cn iid cidx hdom hc
    obtain ⟨hne, hdom'⟩ := blockRegistered_cons_constantDecl hdom
    exact (h.ctors hdom' hc).cons hne
  cases := by
    intro con iid np hdom hc
    obtain ⟨hne, hdom'⟩ := blockRegistered_cons_constantDecl hdom
    obtain ⟨body, oib, hlk, hbod, hnp, hprop⟩ := h.cases hdom' hc
    exact ⟨body, oib, envLookup_cons_of_ne hne hlk, hbod, hnp, hprop⟩
  fields := by
    intro con iid np hdom hc
    obtain ⟨hne, hdom'⟩ := blockRegistered_cons_constantDecl hdom
    exact (h.fields hdom' hc).cons hne
  nofix := by
    intro kn body' hl
    rcases envLookup_cons_inv hl with ⟨-, hd⟩ | ⟨-, hpass⟩
    · cases hd; exact hnf
    · exact h.nofix hpass
  closed := by
    intro kn body hl
    rcases envLookup_cons_inv hl with ⟨-, hd⟩ | ⟨-, hpass⟩
    · cases hd; exact hcl
    · exact h.closed hpass

/-- The non-recursive exit proper: the stored body is a plain `visitExpr` output. -/
theorem RegInvShape.nonrecConst {Γ : ErasureCtx} {s : ErasureState} {n : Name} {t : LBTerm}
    (h : RegInvShape Γ s) (hΓ : Γ.constants n = toKername n)
    (hnf : NoFix t) (hcl : LBClosed t 0) :
    RegInvShape Γ (nonrecConstState n t s) :=
  h.constCons hΓ (Or.inl hnf) hcl

/-! ### The recursive exit

`Erasure.recConstState` conses one `.fix` body per name of the mutual block, left to
right — each cons is literally the non-recursive exit's cons at a `.fix` body
(`Erasure.recConstStep`), so the fold is a `List.foldl` induction over `constCons`.

Its one real input is `hcl`, the closedness of the stored node. Slice S1d asked for it
of an *arbitrary* `defs` and was refuted (`ColdStart.regShapeHyps_recClosed_refuted`:
`.fix [{body := .bvar 5}] 0` is not closed). Here it is a hypothesis of the fold, which
`RunClosed.rc` takes and `Erasure.run_rec_exit_ok` supplies from the shape of the block
it is actually storing. -/

/-- `recConstState` only prepends to `gdecls`. -/
theorem recConstFold_gdecls (defs : List (@FixDef LBTerm)) :
    ∀ (L : List (Name × Nat)) (s : ErasureState),
      ∃ pre, (L.foldl (Erasure.recConstStep defs) s).gdecls = pre ++ s.gdecls
  | [], s => ⟨[], rfl⟩
  | p :: rest, s => by
    obtain ⟨pre, hpre⟩ := recConstFold_gdecls defs rest (Erasure.recConstStep defs s p)
    refine ⟨pre ++ [(toKername p.1, .constantDecl ⟨some (.fix defs p.2)⟩)], ?_⟩
    rw [List.foldl_cons, hpre, List.append_assoc]
    rfl

/-- **`RegInvShape` travels along the recursive block registration.** -/
theorem RegInvShape.recConstFold {Γ : ErasureCtx} {defs : List (@FixDef LBTerm)}
    (hΓ : ∀ m : Name, Γ.constants m = toKername m)
    (hcl : ∀ j : Nat, LBClosed (LBTerm.fix defs j) 0) :
    ∀ (L : List (Name × Nat)) (s : ErasureState), RegInvShape Γ s →
      RegInvShape Γ (L.foldl (Erasure.recConstStep defs) s)
  | [], _, h => h
  | p :: rest, s, h => by
    rw [List.foldl_cons]
    exact RegInvShape.recConstFold hΓ hcl rest _
      (h.constCons (hΓ p.1) (Or.inr ⟨defs, p.2, rfl⟩) (hcl p.2))

/-- The form `Erasure.run_visitMutual_ok`'s `hrec` premise wants. -/
theorem RegInvShape.recConst {Γ : ErasureCtx} {names : List Name}
    {defs : List (@FixDef LBTerm)} {s : ErasureState}
    (hΓ : ∀ m : Name, Γ.constants m = toKername m)
    (hcl : ∀ j : Nat, LBClosed (LBTerm.fix defs j) 0)
    (h : RegInvShape Γ s) :
    RegInvShape Γ (recConstState names defs s) := by
  rw [recConstState_eq]
  exact RegInvShape.recConstFold hΓ hcl _ s h

/-! ### What coverage buys: freshness where the walk has a guard

The invariant no longer *asserts* key freshness, it *derives* it — from the one guard the
code really tests. `get_constant_kername` enters `visitMutual n` only on
`s.constants.get? n = none`, and coverage says the constant keys are exactly the
canonical kernames of registered constants; so an unregistered name owns no constant key.

Two side conditions are visible here and both are honest:

* `hkinj` — `Erasure.toKername` is not injective (`Name.num p k` and
  `Name.str p (toString k)` have the same image), so "distinct names, distinct keys" is a
  naming assumption about the program being erased, not a theorem;
* the conclusion is about the `.constantDecl` entries **only**. Freshness against block
  keys is *unavailable in this form*, and not for want of bookkeeping:
  `mutualBlockKn_eq_toKername` shows every block key is itself the canonical kername of a
  root-level name, so the two key spaces genuinely overlap. -/

/-- **An unregistered name owns no constant key.** -/
theorem RegInvShape.fresh_of_unregistered {Γ : ErasureCtx} {s : ErasureState} {n : Name}
    (h : RegInvShape Γ s)
    (hkinj : ∀ m : Name, Kername.beq (toKername n) (toKername m) = true → n = m)
    (hn : s.constants.get? n = none) {kn : Kername} {cb : ConstantBody}
    (hmem : (kn, GlobalDecl.constantDecl cb) ∈ s.gdecls) :
    Kername.beq (toKername n) kn = false := by
  obtain ⟨m, rfl, hm⟩ := h.cover hmem
  cases hb : Kername.beq (toKername n) (toKername m) with
  | false => rfl
  | true =>
    obtain rfl := hkinj m hb
    rw [hn] at hm
    simp at hm

/-- `Erasure.rootKername` is `Erasure.toKername` at a root-level name — definitionally,
both being `⟨.MPfile [], cleanIdent s⟩`. -/
theorem rootKername_eq_toKername (s : String) :
    rootKername s = toKername (.str .anonymous s) := rfl

/-- **The two key spaces are not disjoint — the block keys are *inside* the constant
keys.** `Erasure.mutualBlockKn` is `rootKername` of the block's printed names, hence the
canonical kername of a root-level name; for a one-name block `A` that name is `A` itself,
so the block entry and a constant entry for `A` collide in `gdecls`, where
`LBTerm.envLookup` is first-match-wins.

This is why coverage is stated about the `.constantDecl` entries: a "block keys are fresh
for constant names" side condition is *false*, not merely unproved. (Whether the
collision is reachable is a question about the shipping eraser, not about this invariant:
it needs a bare inductive type constant to survive the erasability gate into
`visitMutual`, where `addAxiom` would cons an axiom entry under the block's own key.) -/
theorem mutualBlockKn_eq_toKername (ii : InductiveVal) :
    mutualBlockKn ii = toKername (.str .anonymous (String.join (ii.all.map toString))) := rfl

/-! ### Non-vacuity

`RegInvShape.empty` is constructed, so the invariant is inhabited. The guards below add
the fact the design asks for: preservation is not vacuous *because nothing ever
registers* — a concrete `addAxiom` step really does extend `gdecls`, the invariant
survives it twice in a row, and coverage really does separate a fresh name from the keys
already there. -/

/-- A concrete `Γ` filing every constant under its canonical kername (`hknames`). -/
private def gΓcs : ErasureCtx where
  inductives := fun _ => none
  constants := toKername
  ctors := fun _ => none
  ctorArities := fun _ => none
  casesOns := fun _ => none

/-- Non-vacuity: one concrete `addAxiom` from the cold state preserves the invariant
and genuinely extends `gdecls`. -/
theorem gRegInvShape_addAxiom (n : Name) :
    RegInvShape gΓcs (addAxiomState n {}) ∧ (addAxiomState n {}).gdecls ≠ [] :=
  ⟨(RegInvShape.empty gΓcs).addAxiom rfl, by simp [addAxiomState]⟩

/-- Non-vacuity: two `addAxiom` steps in a row, at any two names. Slice S1d needed the
second step's key to be fresh; it no longer does, which is the point — the invariant
survives even the re-registration that refutes `KeysDistinct`. -/
theorem gRegInvShape_addAxiom₂ (n m : Name) :
    RegInvShape gΓcs (addAxiomState m (addAxiomState n {})) :=
  ((RegInvShape.empty gΓcs).addAxiom (n := n) rfl).addAxiom rfl

/-- Non-vacuity of coverage: at a state with a real entry, a name the registry does not
know is separated from the key that is there — so `fresh_of_unregistered` is not true
merely because `gdecls` is empty. -/
theorem gRegInvShape_fresh (n m : Name) (hne : n ≠ m)
    (hkinj : ∀ k : Name, Kername.beq (toKername n) (toKername k) = true → n = k) :
    Kername.beq (toKername n) (toKername m) = false := by
  have hn : (addAxiomState m {}).constants.get? n = none := by
    simp only [addAxiomState, Std.HashMap.get?_insert]
    split
    · rename_i heq
      exact absurd (by simpa using heq : m = n).symm hne
    · simp
  have hmem : (toKername m, GlobalDecl.constantDecl ⟨none⟩) ∈ (addAxiomState m {}).gdecls :=
    List.mem_cons_self
  exact (gRegInvShape_addAxiom m).1.fresh_of_unregistered hkinj hn hmem

end LeanToLambdaBox
