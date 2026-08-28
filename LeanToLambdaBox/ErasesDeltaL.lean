import LeanToLambdaBox.ErasesCorrectData
import LeanToLambdaBox.ErasesInstL

/-!
# The δ record at the call site's instantiation (slice Γ-U4)

Slice Γ-U4 restated the model's δ pair: `SEvalDataι.delta` unfolds a constant at
`body.instantiateLevelParams (Γ.lparams n) us`, and `SubjectReductionFull.SEnvConsistentL`
supplies the defeq at that same expression. The forward simulation's δ case needs a third
thing, on the *erasure* side rather than the model side: the target body the walk recorded
must erase the **instantiated** source body, not the recorded one.

`ErasesEnvDeltaData` (`ErasesCorrectData.lean`) does not say that. It says
`Erases env Us Γ Δ body body'` at the ambient scope `Us`, which is the right statement
exactly when the instantiation is the identity. `ErasesEnvDeltaL` below is the statement
the restated δ case consumes, and it has two implementations:

* `ErasesEnvDeltaData.toL` — the **monomorphic degeneracy**. At `Γ.lparams = fun _ => []`
  the instantiation is `rfl`-trivial, so the existing record *is* the new one. Every
  capstone in the development goes through this line, which is why the slice moved no
  discharge.
* `ErasesEnvDeltaL.of_ownScope` — the **content**, and `ErasesInstL.Erases.instL`'s first
  consumer outside its own guards. Given the dependency's erasure at *its own* level scope
  (`Erases env (Γ.lparams n) Γ [] body body'` — which is what `visitMutual` actually
  produces, under `withReader (… lparams := ci.levelParams)`), the strict transport carries
  it to the caller's scope at the caller's levels, **with the target body unchanged**.

## What each side condition is doing, and where it comes from

`Erases.instL` is scoped, and this file threads all three of its restrictions in the open
rather than hiding them in a bundle:

* **`NoMaxLevels body`** — the `max`/`imax`-free level fragment, which is where level
  substitution is strict rather than `≈`-loose (Γ-U3; the slack is manufactured by Lean's
  normalising `mkLevelMax'`, not by substitution). It is a property of the *dependency's
  body*, so it belongs on the own-scope record, which is where `of_ownScope` puts it. The
  typeclass-dispatch layer this whole campaign exists to admit is inside the fragment;
  a body with an explicit `Sort (max u v)` is not.

  **Measured on the benchmarks rather than asserted** (2026-08-28). Walking the
  value-cone of two `VerifyBench` programs together with the dispatch heads
  `OfNat.ofNat`, `HAdd.hAdd`, `Add.add`, `HPow.hPow`, `Nat.add`, `Nat.mul` and
  `List.range`: 52 constants have a value, and **48 of the 52 are `max`-free**. All four
  exceptions are the structural-recursion machinery — `Nat.below`, `List.below` (both
  `Sort`-valued, i.e. arities, so a use site is `Erases.box`, never a δ-unfolding) and
  `Nat.brecOn.go`, `List.brecOn.go` (which mention `max` only through `below`). And none
  of the four survives to the shipped fragment at all: the five committed
  `VerifyBench/ast/*.ast` files contain no occurrence of `brecOn` or `below`, because
  `prepare_erasure` reads the *compiler*'s definitions and not the kernel's `brecOn`
  chain. So on this sample the restriction is not a restriction.
* **`Γ.recBodies = fun _ => none`** — the non-recursive fragment. `Erases.instL` kills its
  two recursive arms by refutation, and Γ-U3 named the reason the arms are genuinely out:
  `Erases.fix`'s `hbodies` is stated `∀ Δf` while the induction hypothesis supplies
  instantiated bodies only at contexts in the image of `VLCtx.instL`.
* **the level arithmetic** — `us.mapM (VLevel.ofLevel Us) = some us'` and
  `(Γ.lparams n).length = us.length`. The first is *free*: it is a premise of the
  `TrExprS.const` the δ case already holds. The second is not, and it is the real coherence
  obligation this slice exposes: `LparamsArity` below, "the universe column declares the
  constant at the arity the environment does". A column that lies about a constant's arity
  makes the δ rule model an unfolding the kernel never performs, exactly as a lying
  `ctorArities` makes `ctor_val` model a saturation bound the kernel never checks.

## The context, and why the record is stated at `[]`

`Erases.instL` moves the context to `Δ.instL us'`, and `VLCtx.instL` is not surjective, so
there is no transport from an own-scope derivation at an arbitrary `Δ` to an instantiated
one at that same `Δ`. There does not need to be: a top-level constant's body is closed, its
erasure is context-independent, and the development already owns that fact
(`ErasesUniform.erases_uniform_closed`, the δ-D7b discharge). So `of_ownScope` takes the
own-scope record at `Δ = []` — where `[].instL us' = []` — and takes the widening to every
context as a supplied function, exactly as `registeredClosureData_of_deltaMem_walked` does.
The one place the ambient context enters is therefore the *same* place it entered before
this slice, and no new context obligation is created.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-! ## The coherence obligation the universe column carries -/

/-- **The universe column declares a constant at the arity the environment does** — the
coherence condition `ErasureCtx.lparams` needs and cannot state for itself (slice Γ-U4).

`TrExprS.const` pins `us.length = ci.uvars` for the call site's levels; the δ rule
instantiates `Γ.lparams n` by `us`, and `Expr.instantiateLevelParams` is only the kernel's
step when the two lists have the same length. This predicate is that agreement, phrased
through the translation rather than through `VConstant` directly so that it needs no
`VEnv`-side plumbing at its consumers: they all hold the `TrExprS` already.

Non-vacuous in both directions — `gLparamsArity_poly` constructs it at a `{u}`-declared
constant, and it is *not* implied by the monomorphic default column
(`gLparamsArity_bot_refuted`: a `⊥` column at a constant the environment declares with one
universe parameter fails it, which is precisely the situation the campaign is aimed at). -/
def LparamsArity (env : VEnv) (Us : List Name) (Γ : ErasureCtx) : Prop :=
  ∀ {Δ : VLCtx} {n : Name} {us : List Level} {cve : VExpr},
    TrExprS env Us Δ (.const n us) cve → (Γ.lparams n).length = us.length

/-! ## The record -/

/-- **The δ environment record, at the call site's universe instantiation** (slice Γ-U4).

The clause `erases_correct_dataι`'s δ case consumes: the target body the walk recorded for
`n` erases the source body **instantiated at the call site's levels**, which is the
expression `SEvalDataι.delta` now recurses on.

Three shape decisions, all load-bearing:

* the `TrExprS env Us Δ (.const n us) cve` hypothesis is what carries the level arithmetic
  `Erases.instL` needs (`us.mapM (VLevel.ofLevel Us)`), and the δ case holds it already.
  `ErasesEnvDeltaData`'s registration conjuncts (`Γ.ctors n = none`,
  `Γ.casesOns n = none`) are deliberately **not** duplicated here: they are consumed in
  places where no translation is in scope (the `hnf` refutation), so they stay on the
  existing record and this one is purely additive beside it;
* `body'` is quantified **outside** `us`, so the record asserts that *one* target body
  serves *every* instantiation. That is finding (a) of the Γ-U analysis — λ□ is level-free
  — cashed in as a statement rather than a hope, and it is what `Erases.instL`'s
  target-unchanged conclusion makes provable;
* it is stated at `∀ Δ`, like the record it sits beside, so the δ case can fire at any
  depth. `of_ownScope` pays that with the same context-uniformity theorem the existing
  record's discharge uses. -/
def ErasesEnvDeltaL (env : VEnv) (Us : List Name) (Γ : ErasureCtx)
    (Esrc : SEnv) (E : GlobalDeclarations) : Prop :=
  ∀ {Δ : VLCtx} {n : Name} {us : List Level} {body : Expr} {cve : VExpr},
    Esrc n = some body →
    TrExprS env Us Δ (.const n us) cve →
    ∃ body', LBTerm.envLookup E (Γ.constants n) = some (.constantDecl ⟨some body'⟩) ∧
      Erases env Us Γ Δ (body.instantiateLevelParams (Γ.lparams n) us) body' ∧ NoBlock body'

/-- **The monomorphic degeneracy** — the line every current capstone takes.

At a `Γ` whose universe column is `⊥` (every `ErasureCtx` in this development: the field's
default) the instantiation is the identity definitionally, so the record the walk already
produces *is* the record the restated δ case wants. This is the condition the Γ-U4 plan
attached to the restatement — that it must not cost a single existing discharge — and this
is where it is met. -/
theorem ErasesEnvDeltaData.toL {env : VEnv} {Us : List Name} {Γ : ErasureCtx}
    {Esrc : SEnv} {E : GlobalDeclarations} (h : ErasesEnvDeltaData env Us Γ Esrc E)
    (hlp : Γ.lparams = fun _ => []) : ErasesEnvDeltaL env Us Γ Esrc E := by
  intro Δ n us body cve hb _
  obtain ⟨-, -, body', hlook, her, hnb⟩ := h hb
  exact ⟨body', hlook, by rw [hlp]; simpa using her, hnb⟩

/-- **The universe-polymorphic implementation** (slice Γ-U4, and the content of it):
`ErasesInstL.Erases.instL`'s first consumer outside its own guards.

`hown` is the dependency's erasure **at its own level scope** and at the empty context —
which is exactly what `visitMutual` produces, since it erases a dependency's body under
`withReader (… lparams := ci.levelParams)` and at no local binders. The strict transport
carries it to the caller's scope `Us` at the caller's levels `us`, the target body
unchanged; `hunif` re-widens to every context, the same step the existing record's
discharge takes and for the same reason (a top-level body is closed).

The two scope restrictions travel in the open: `hnorec` (Γ-U3's named gap — `Erases.fix`'s
`∀ Δf` against `VLCtx.instL`'s non-surjectivity on contexts) and the per-body
`NoMaxLevels` (the fragment on which level substitution does not normalise). `hcoh` is the
coherence obligation the column carries. Nothing here needs `env.WF` or `VLCtx.WF`, which
is inherited from the transport and is what let it be threaded through `Erases` at all.

**What this does not yet do.** It is an implementation of the interface, not a discharge
from the walk: `ColdStartDelta`'s record is built at the *ambient* `Us`, so producing
`hown` from a cold start is the remaining step, and it is the campaign's completion
criterion rather than this slice's. -/
theorem ErasesEnvDeltaL.of_ownScope {env : VEnv} {Us : List Name} {Γ : ErasureCtx}
    {Esrc : SEnv} {E : GlobalDeclarations}
    (hnorec : Γ.recBodies = fun _ => none)
    (hcoh : LparamsArity env Us Γ)
    (hown : ∀ {n : Name} {body : Expr}, Esrc n = some body →
      NoMaxLevels body ∧
      ∃ body', LBTerm.envLookup E (Γ.constants n) = some (.constantDecl ⟨some body'⟩) ∧
        Erases env (Γ.lparams n) Γ [] body body' ∧ NoBlock body')
    (hunif : ∀ {Δ : VLCtx} {e : Expr} {t : LBTerm},
      Erases env Us Γ [] e t → Erases env Us Γ Δ e t) :
    ErasesEnvDeltaL env Us Γ Esrc E := by
  intro Δ n us body cve hb htr
  obtain ⟨hnm, body', hlook, her, hnb⟩ := hown hb
  -- The level arithmetic: `mapM` off the translation, the length off the coherence.
  obtain ⟨us', hmap⟩ : ∃ us', us.mapM (VLevel.ofLevel Us) = some us' := by
    cases htr with | const _ h2 _ => exact ⟨_, h2⟩
  refine ⟨body', hlook, hunif (Δ := Δ) ?_, hnb⟩
  -- `[].instL us' = []` on the nose, which is why the record is stated at the empty
  -- context: `VLCtx.instL` is not surjective, so there is no route at a general `Δ`.
  exact Erases.instL hmap (hcoh htr) hnorec her hnm

/-! ### Guards

Three, and they bound the claim from both sides: the transport really does fire at a
polymorphic dependency of a closed subject (the shape the typeclass layer needs and the
one Γ-U's analysis recorded as unavailable); the coherence obligation is constructible;
and it is *not* free at the default column, which is why it is a premise. -/

/-- The guard's environment: one constant `g`, declared with **one** universe parameter. -/
def envPolyδ : VEnv where
  constants n := if n = `g then some ⟨1, .sort .zero⟩ else none
  defeqs _ := False
  pats _ _ := False

/-- The guard's `Γ`: no recursion, no registrations, and a universe column that declares
`g` at `{u}` — the first `ErasureCtx` in the development whose `lparams` is not `⊥`. -/
def ΓPolyδ : ErasureCtx where
  inductives _ := none
  constants _ := ⟨.MPfile [], "g"⟩
  lparams n := if n = `g then [`u] else []

@[simp] theorem ΓPolyδ_lparams_g : ΓPolyδ.lparams `g = [`u] := rfl
@[simp] theorem ΓPolyδ_recBodies : ΓPolyδ.recBodies = fun _ => none := rfl

/-- Guard (positive): the coherence obligation is **constructible** at a genuinely
polymorphic constant. `TrExprS.const` can only fire at `g` in this environment, where it
pins `us.length = 1`, and the column's `[`u]` has length `1`. -/
theorem gLparamsArity_poly : LparamsArity envPolyδ [] ΓPolyδ := by
  intro Δ n us cve htr
  cases htr with
  | const h1 _ h3 =>
    simp only [envPolyδ] at h1
    split at h1
    · next h =>
      subst h
      obtain rfl := Option.some.inj h1
      simpa using h3.symm
    · exact absurd h1 (by simp)

/-- Guard (negative): the obligation is **not** free at the default column, and that is why
it is a premise rather than a theorem. A `Γ` that says `g` is monomorphic while the
environment declares it at one universe parameter fails `LparamsArity` — which is exactly
the configuration the whole Γ-U campaign is aimed at, and exactly the configuration in
which the *old*, level-blind δ rule silently modelled the wrong unfolding. -/
theorem gLparamsArity_bot_refuted :
    ¬ LparamsArity envPolyδ [] { ΓPolyδ with lparams := fun _ => [] } := by
  intro h
  have htr : TrExprS envPolyδ [] [] (.const `g [.zero]) (.const `g [.zero]) :=
    .const (show envPolyδ.constants `g = some ⟨1, .sort .zero⟩ from rfl) rfl rfl
  exact absurd (h htr) (by simp)

/-- Guard (positive, the shape slice Γ-U4 exists for): a `{u}`-polymorphic dependency body,
δ-unfolded at a **closed** instantiation inside a `Us = []` subject, erases at the
subject's scope — same target term, no residue.

This is `ErasesInstL`'s `gErasesInstLClosed` with the level list read off the universe
column instead of written by hand, i.e. it is the step the restated δ rule takes. Built at
an arbitrary `env`, so what it checks is the instantiation and nothing else. -/
theorem gErasesDeltaInstL (env : VEnv) (nm : Name) (bi : BinderInfo) :
    Erases env [] ΓPolyδ []
      ((Expr.lam nm (.sort (.param `u)) (.bvar 0) bi).instantiateLevelParams
        (ΓPolyδ.lparams `g) [Level.zero])
      (.lambda (nameToBinder nm) (.bvar 0)) := by
  have h := Erases.instL (env := env) (Us := []) (ps := [`u]) (ls := [Level.zero])
    (ls' := [VLevel.zero]) (Γ := ΓPolyδ) (Δ := [])
    (e := .lam nm (.sort (.param `u)) (.bvar 0) bi)
    (t := .lambda (nameToBinder nm) (.bvar 0)) gInstLClosed.1 gInstLClosed.2 rfl
    (.lam (ty' := .sort (.param 0)) (.sort rfl) (.bvar 0))
    (⟨trivial, trivial⟩ : NoMaxLevels (.lam nm (.sort (.param `u)) (.bvar 0) bi))
  simpa [VLCtx.instL] using h

/-- The guard's source environment: `g` unfolds to the `{u}`-polymorphic identity
`fun (x : Sort u) => x`. -/
def EsrcPolyδ : SEnv := fun n => if n = `g then some (.lam `x (.sort (.param `u)) (.bvar 0) .default) else none

/-- Guard (positive, the δ *step*): `g.{0}` evaluates to the identity **at `Sort 0`** —
the level-instantiated body — and `g.{1}` to the identity at `Sort 1`. The restated rule
keeps the two apart; the level-blind rule it replaced sent both to the uninstantiated
`fun (x : Sort u) => x`, which is not a value of the source language at `Us = []` at all.

This is what `SEvalDataι.delta_level_blind`'s `hlp` premise costs and buys, exhibited on
an actual evaluation rather than on the reducts alone. -/
theorem gSEvalDeltaPoly (ia : IotaArities) :
    SEvalDataι ΓPolyδ ia EsrcPolyδ (.const `g [Level.zero])
        (.lam `x (.sort .zero) (.bvar 0) .default) ∧
      SEvalDataι ΓPolyδ ia EsrcPolyδ (.const `g [Level.succ .zero])
        (.lam `x (.sort (.succ .zero)) (.bvar 0) .default) := by
  have hunf : EsrcPolyδ `g = some (.lam `x (.sort (.param `u)) (.bvar 0) .default) := by
    simp [EsrcPolyδ]
  refine ⟨.delta hunf ?_, .delta hunf ?_⟩ <;>
  · simp only [ΓPolyδ_lparams_g, Expr.instantiateLevelParams_eq,
      Expr.instantiateLevelParamsCore', Level.substParams', Level.hasParam_eq,
      Level.hasParam']
    exact .lam _ _ _ _

end LeanToLambdaBox
