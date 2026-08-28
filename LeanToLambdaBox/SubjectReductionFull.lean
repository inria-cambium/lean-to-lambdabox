import LeanToLambdaBox.SubjectReduction

/-!
# Subject reduction as definitional equality (β + ζ + δ fragment) — step A3.3′

This file generalizes `SEvalβ_defeq` (the β-only subject-reduction-as-defeq) to
the larger source evaluation relation `SEvalβζδι` (β + ζ + δ + ι). The conclusion
is the same shape: if `e` translates to `ve` and `e` big-step evaluates to `v`,
then `v` translates to some `vve` definitionally equal to `ve`.

## The four new cases

* **ζ (let).** At `VExpr` level there is *no* let node: `TrExprS.letE` translates
  `letE n ty val b` straight to the body's `VExpr` `body'`, in the extended context
  `(none, .vlet ty' val') :: Δ`. lean4lean's `TrExprS.inst_let` then says the
  *substituted* body `b.instantiate1' val` translates to the **same** `body'`. So
  the ζ defeq is essentially *reflexivity* of the translated body — modulo the IH
  on the body evaluation. No new hypotheses are needed.

* **δ (const).** A constant `n` unfolds to `body` (`E n = some body`). At `VExpr`
  level this is the defeq `.const n us' ≡ ⟦body⟧`, which holds because a real
  `VEnv` registers each definition as an `extra` defeq (`addDefEq ci.toDefEq`). We
  do not reconstruct that from the kernel translation; instead we **thread it as a
  hypothesis** via `SEnvConsistent`, asserting exactly the defeq facts the δ case
  needs. This is the source-env ↔ `VEnv` consistency the project notes call for.

* **ι (casesOn).** SCOPED OUT of this file — see the report. The pinned lean4lean
  fork *does* expose an ι/recursor rule (`IsDefEq.pat`, fed by `VEnv.pats` /
  `VEnv.addInduct`), but it is not yet chainable into a concrete instance, so the
  iota fact is threaded as a per-reduction defeq hypothesis (`IotaConsistent`,
  `SourceEvalData.lean`) whose *use* requires fully inverting the `casesOn`
  translation spine (a nested application of the translated `pre`/`discr`/`minors`).
  That is a substantial separate development, carried out in
  `SubjectReductionIota.lean`; we deliberately do not fake it here. `ctor_val` is
  handled (it is a value, structurally).

`SEvalβ`/`SEvalβ_defeq` and all their committed metatheory are left untouched.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-- **Source-env ↔ `VEnv` consistency for δ-unfolding, at the call site's universe
instantiation** — the corrected predicate (slice Γ-U4), and the fact a well-formed `VEnv`
actually supplies.

Whenever `Esrc n = some body` and the constant application `.const n us` translates to a
`VExpr` `cve`, the **instantiated** body `body.instantiateLevelParams (Ups n) us`
translates (to some `bve`) and the constant is definitionally equal to it.

This is `VEnv.IsDefEq.extra`'s conclusion transported to the source side. That rule reads

    Γ ⊢ df.lhs.instL ls ≡ df.rhs.instL ls : df.type.instL ls

— **both** sides instantiated at the call site's levels — so what a real `VEnv` gives at a
`{u}`-polymorphic `n` is `.const n us ≡ ⟦body⟧.instL us`, never `.const n us ≡ ⟦body⟧`.
`Ups` is the per-constant universe-parameter map; every consumer passes `Γ.lparams`
(`ErasureContext.lean`), which is where the map lives and where its coherence with the
kernel's `ci.levelParams` is stated.

`SEnvConsistent` below is this predicate at `Ups = fun _ => []`, definitionally
(`senvConsistent_iff_l`), and that is the exact sense in which the old premise was the
kernel fact: a *monomorphic* one. Everything the development ships runs there, because
`ErasureCtx.lparams` defaults to `fun _ => []`; what changed at Γ-U4 is that the
restriction is now a named, `rfl`-checkable equation on a `Γ` column instead of a
silent consequence of a quantifier that binds `us` and never uses it. -/
def SEnvConsistentL (env : VEnv) (Us : List Name) (Ups : Name → List Name)
    (Esrc : SEnv) : Prop :=
  ∀ {Δ : VLCtx} {n : Name} {us : List Level} {body : Expr} {cve : VExpr},
    Esrc n = some body →
    TrExprS env Us Δ (.const n us) cve →
    ∃ bve, TrExprS env Us Δ (body.instantiateLevelParams (Ups n) us) bve ∧
      env.IsDefEqU Us.length Δ.toCtx cve bve

/-- **Source-env ↔ `VEnv` consistency for δ-unfolding.**

The source environment `Esrc : SEnv` and the lean4lean `VEnv` `env` agree on
constant unfolding: whenever `Esrc n = some body` and the constant application
`.const n us` translates to a `VExpr` `cve`, the body `body` also translates (to
some `bve`) and the constant is definitionally equal to its unfolding
(`cve ≡ bve`).

This is exactly the δ fact a well-formed `VEnv` provides for every definition (it
registers `def n := body` as an `extra` defeq); we take it as a hypothesis rather
than reconstructing it from the kernel translation, since `SEnv` is an *opaque*
unfolding map with no a-priori link to `env.defeqs`.

`U` is the universe-parameter count and `Γ` the typing context at which the defeq
is required (the context is universally quantified so the predicate can be applied
under binders).

**⚠️ The `us` binder is discarded, and that is the development's universe
monomorphism** (slice Γ-U; provenance corrected 2026-08-27; **repaired at slice Γ-U4**,
2026-08-28, which is what the rest of this docstring now records). The docstring
used to say the `VEnv` registers `.const n us ≡ ⟦body⟧`. It does not: the rule is
`VEnv.IsDefEq.extra` (`Lean4Lean/Theory/Typing/Basic.lean`), whose conclusion is

    Γ ⊢ df.lhs.instL ls ≡ df.rhs.instL ls : df.type.instL ls

i.e. **both sides are instantiated** at the call site's levels. So the fact a real
`VEnv` supplies is `.const n us ≡ ⟦body⟧.instL us`, and this predicate —
which quantifies `us` and then never mentions it — is that fact only when
`instL us` is the identity, i.e. when `n` is universe-monomorphic. For a genuinely
polymorphic `n` the predicate is *stronger* than the kernel fact and collapses the
constant's instantiations to one another; `SEnvConsistent.levels_collapse` below
states that collapse as a theorem.

**What Γ-U4 did about it.** The corrected predicate is `SEnvConsistentL` above, at the
instantiated body; this one is *defined* to be its `Ups = fun _ => []` instance and is
proved to be (`senvConsistent_iff_l`, `Iff.rfl`). So the reading of this premise is now
exact and local: **it is the kernel fact restricted to a universe-monomorphic fragment**,
and the restriction is the `Γ.lparams = fun _ => []` equation the ι capstone carries
(`ColdStart`'s `hlp` row) rather than an unnamed consequence of a vacuous binder. The
predicate itself did not change a byte, which is why not one of its ~20 consumers or its
four discharges moved.

Consequence for scope, and it is the point of recording this: universe monomorphism
used to be pinned in **two** independent places, not one. `DeltaHyps.decl_run`'s scope
conjunct (scope restriction 1) makes the *bundle* uninhabited for a polymorphic
dependency — a named, documented failure. This predicate made the *simulation's premise*
false for one — an unnamed one, until Γ-U. Relaxing the former without repairing the
latter (and `SEvalDataι.delta`'s level-blindness, and `Erases`' lack of an `instL`
transport) would not widen the fragment; it would only move where the vacuity lives. See
`DeltaHyps`' Γ-U analysis for the full accounting.

**All three are now addressed.** The third went at slice Γ-U3
(`ErasesInstL.Erases.instL`, a strict level-instantiation transport for erasure on the
`max`/`imax`-free non-recursive fragment — the typeclass layer). The model pair went at
Γ-U4: `SEvalDataι.delta` unfolds at `body.instantiateLevelParams (Γ.lparams n) us`, and
`SEnvConsistentL` is stated to match, with `SEvalDataι_defeq` and `erases_correct_dataι`
consuming the general forms. What is *not* done, and is the campaign's completion
criterion rather than this slice's, is a capstone at `Us ≠ []` with a genuinely
polymorphic dependency: that needs the walk's δ record at the dependency's own scope
(`ErasesEnvDeltaL.of_ownScope` shows the step; `ColdStartDelta`'s record does not yet
supply its input) and, for a *recursive* dependency, it needs `Erases.instL`'s recursive
arms, which Γ-U3 named as out of scope.

**Slice Γ-U2 relaxed the first place and this one still did not move**, which is worth
recording because it is the case the warning above was written against. The relaxation is
to a *prefix* — `ci.levelParams <+: Us` — and the cold-start capstones pin `Us = []`
(`ColdStart`'s `hUs` row), where a prefix of the empty scope is the empty scope. So the
bundle is wider at a polymorphic subject, no capstone states one, and this predicate is
asked for at exactly the constants it was asked for before. -/
def SEnvConsistent (env : VEnv) (Us : List Name) (Esrc : SEnv) : Prop :=
  ∀ {Δ : VLCtx} {n : Name} {us : List Level} {body : Expr} {cve : VExpr},
    Esrc n = some body →
    TrExprS env Us Δ (.const n us) cve →
    ∃ bve, TrExprS env Us Δ body bve ∧ env.IsDefEqU Us.length Δ.toCtx cve bve

/-- **The old premise is the new one at `Ups = ⊥`, on the nose** (slice Γ-U4).

`Iff.rfl`: `Expr.instantiateLevelParams` short-circuits on `paramNames.isEmpty`, so
`body.instantiateLevelParams ((fun _ => []) n) us` reduces to `body` without looking at
`us`. This is the machine-checked form of the docstring's claim that `SEnvConsistent` is
the kernel fact *restricted to a monomorphic fragment*, and it is what lets both
directions below be one line each. -/
theorem senvConsistent_iff_l {env : VEnv} {Us : List Name} {Esrc : SEnv} :
    SEnvConsistent env Us Esrc ↔ SEnvConsistentL env Us (fun _ => []) Esrc := Iff.rfl

/-- **The monomorphic degeneracy, in the direction the simulations consume.** A `Γ` whose
universe column is `⊥` — every `ErasureCtx` this development builds, the field's default —
turns the old premise into the corrected one at that column. One line, which is the
requirement the Γ-U4 plan attached to the restatement: every current capstone stays green
without a new obligation. -/
theorem SEnvConsistent.toL {env : VEnv} {Us : List Name} {Ups : Name → List Name}
    {Esrc : SEnv} (h : SEnvConsistent env Us Esrc) (hlp : Ups = fun _ => []) :
    SEnvConsistentL env Us Ups Esrc := by subst hlp; exact h

/-- …and back, which is what the ι discharge route (`iotaConsistent_of_shape`, whose
`casesOn` unfolding is stated at the uninstantiated value) needs. -/
theorem SEnvConsistentL.toMono {env : VEnv} {Us : List Name} {Ups : Name → List Name}
    {Esrc : SEnv} (h : SEnvConsistentL env Us Ups Esrc) (hlp : Ups = fun _ => []) :
    SEnvConsistent env Us Esrc := by subst hlp; exact h

/-- **The collapse is driven by the monomorphism claim, not by the predicate** (slice
Γ-U4's restatement of Γ-U's guard).

If the universe column declares `n` monomorphic (`Ups n = []`), then the corrected
premise's conclusion stops mentioning `us`, and any two level instantiations of `n` are
forced definitionally equal to one another — both are defeq to the *one* translation of
the uninstantiated body, which `TrExprS.uniq` pins up to defeq. That is a genuine extra
demand at a genuinely polymorphic `n`, and one a well-formed `VEnv` does **not**
discharge: `VEnv.IsDefEq.extra` instantiates both sides of the defining equation, so it
relates `.const n us` to `⟦body⟧.instL us`, never two different `instL`s to each other.

Stated at `SEnvConsistentL` with `hlp` explicit, the theorem says exactly what the Γ-U4
repair is for: **the collapse is the price of the `Ups n = []` claim**, and a column that
tells the truth about a polymorphic constant does not pay it. Drop `hlp` and the proof
does not go through — `htrb`/`htrb'` are then translations of two *different* expressions
(`delta_level_polymorphic` exhibits the split at `Sort u`), so `TrExprS.uniq` has nothing
to say about them. -/
theorem SEnvConsistentL.levels_collapse {env : VEnv} (henv : env.WF) {Us : List Name}
    {Ups : Name → List Name} {Esrc : SEnv} (h : SEnvConsistentL env Us Ups Esrc)
    {Δ : VLCtx} (hΔ : VLCtx.WF env Us.length Δ)
    {n : Name} {us us' : List Level} {body : Expr} {cve cve' : VExpr}
    (hlp : Ups n = []) (hb : Esrc n = some body)
    (htr : TrExprS env Us Δ (.const n us) cve)
    (htr' : TrExprS env Us Δ (.const n us') cve') :
    env.IsDefEqU Us.length Δ.toCtx cve cve' := by
  obtain ⟨bve, htrb, hd⟩ := h hb htr
  obtain ⟨bve', htrb', hd'⟩ := h hb htr'
  rw [hlp] at htrb htrb'
  simp only [instantiateLevelParams_nil] at htrb htrb'
  have huniq : env.IsDefEqU Us.length Δ.toCtx bve bve' :=
    TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrb htrb'
  exact VEnv.IsDefEqU.trans henv hΔ.toCtx hd
    (VEnv.IsDefEqU.trans henv hΔ.toCtx huniq (VEnv.IsDefEqU.symm hd'))

/-- **`SEnvConsistent` collapses a fragment constant's universe instantiations** —
slice Γ-U's guard on the simulation side, and the companion of
`SEvalDataι.delta_level_blind` on the evaluation side.

Because the predicate quantifies `us` and its conclusion never mentions it, any two
level instantiations of the same `Esrc` constant are forced definitionally equal to
one another. For a monomorphic constant this is vacuous —
`us = []` is the only instantiation — which is exactly the scope
`DeltaHyps.decl_run` already pins. For a polymorphic one it is a genuine extra
demand, and one a well-formed `VEnv` does **not** discharge.

So this is the theorem behind the claim in `SEnvConsistent`'s docstring: a Γ-U slice
that relaxed `DeltaHyps.decl_run` and `BlockHyps.block_lparams` alone would leave the
capstones with a premise that is false at exactly the constants the relaxation was
meant to admit. Γ-U2 did relax those two — to a prefix — and escaped the conclusion
only because the capstones still pin `Us = []`, where the relaxation is the identity.

**Since slice Γ-U4 this is a corollary rather than a wall.** It is
`SEnvConsistentL.levels_collapse` at `Ups = fun _ => []`, i.e. it is what the *monomorphic
instance* costs; the corrected predicate at a truthful column does not collapse anything,
and the δ rule that consumes it unfolds at
`body.instantiateLevelParams (Γ.lparams n) us`. The theorem is kept, at its old
signature, because it is still the honest statement of what a capstone carrying
`hlp : Γ.lparams = ⊥` is assuming. -/
theorem SEnvConsistent.levels_collapse {env : VEnv} (henv : env.WF) {Us : List Name}
    {Esrc : SEnv} (h : SEnvConsistent env Us Esrc)
    {Δ : VLCtx} (hΔ : VLCtx.WF env Us.length Δ)
    {n : Name} {us us' : List Level} {body : Expr} {cve cve' : VExpr}
    (hb : Esrc n = some body)
    (htr : TrExprS env Us Δ (.const n us) cve)
    (htr' : TrExprS env Us Δ (.const n us') cve') :
    env.IsDefEqU Us.length Δ.toCtx cve cve' :=
  SEnvConsistentL.levels_collapse henv (senvConsistent_iff_l.1 h) hΔ rfl hb htr htr'

/-- **`SEnvConsistent` collapses a mutual block's two members** (slice Γ-W5) — the
sibling-side twin of `levels_collapse`, and the fact that stops the mutual cold-start guard
where `ColdStart`'s `MutualGuard` section stops it.

A mutual block's source is `def f a := g a` / `def g a := f a`: each member's recorded body
is the *other* member's η-expansion. Feed that to `SEnvConsistent` and the premise no
longer says "this constant equals its own body" — it says
`.const f [] ≡ .const g []`, a defeq **between the two siblings**. Two distinct axioms do
not satisfy it, so an environment that discharges `hcon` at a mutual block has to identify
the block's members (declare one as a kernel definition of the other, the `envδ`/`addDefEq`
pattern), which degenerates the source side of the very fixture the guard exists to build.

That is why the row's two existing discharges do not generalise. `envδ_senvConsistent` uses
the kernel's own defining equation, which a recursive constant does not have;
`envRec_senvConsistent` uses **η**, and η contracts `fun a => g a` to `g`, not to `f`. The
premise is *not* thereby false — it is a trust item about the elaborator, and at a mutual
block it is one relating two constants rather than one — but it is stronger than the
per-constant reading `SEnvConsistent`'s docstring gives, exactly as `levels_collapse` shows
it is stronger than the kernel fact at a polymorphic constant.

The body's translation is stipulated at the shape `TrExprS.lam`/`app`/`const` forces
(`ColdStart.envRec_trFixRecSrc` builds precisely it for the self-loop fixture), and `hty`
is the sibling's Pi typing, which any declared block member has. Everything else is
`levels_collapse`'s proof: `hcon`, `TrExprS.uniq`, and one `VEnv.IsDefEq.eta`. -/
theorem SEnvConsistent.siblings_collapse {env : VEnv} (henv : env.WF) {Us : List Name}
    {Esrc : SEnv} (h : SEnvConsistent env Us Esrc)
    {Δ : VLCtx} (hΔ : VLCtx.WF env Us.length Δ)
    {m m' : Name} {nm : Name} {ty : Expr} {bi : BinderInfo} {A B : VExpr} {cve : VExpr}
    (hb : Esrc m = some (.lam nm ty (.app (.const m' []) (.bvar 0)) bi))
    (htr : TrExprS env Us Δ (.const m []) cve)
    (htrb : TrExprS env Us Δ (.lam nm ty (.app (.const m' []) (.bvar 0)) bi)
      (.lam A (.app (.const m' []) (.bvar 0))))
    (hty : env.HasType Us.length Δ.toCtx (.const m' []) (.forallE A B)) :
    env.IsDefEqU Us.length Δ.toCtx cve (.const m' []) := by
  obtain ⟨bve, htrb₀, hd⟩ := h hb htr
  have huniq : env.IsDefEqU Us.length Δ.toCtx bve (.lam A (.app (.const m' []) (.bvar 0))) :=
    TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrb₀ htrb
  exact VEnv.IsDefEqU.trans henv hΔ.toCtx hd
    (VEnv.IsDefEqU.trans henv hΔ.toCtx huniq ⟨_, VEnv.IsDefEq.eta hty⟩)

/-- The head of a translated application spine itself translates. -/
theorem TrExprS_spine_head {env : VEnv} {Us : List Name} {Δ : VLCtx} :
    ∀ (args : List Expr) {head : Expr} {ve : VExpr},
      TrExprS env Us Δ (args.foldl Expr.app head) ve →
      ∃ hve, TrExprS env Us Δ head hve
  | [], _, _, htr => ⟨_, htr⟩
  | a :: as, head, ve, htr => by
      simp only [List.foldl_cons] at htr
      obtain ⟨hve', htr'⟩ := TrExprS_spine_head as htr
      cases htr' with
      | app _ _ htrhead _ => exact ⟨_, htrhead⟩

/-- **Subject reduction along a constructor application spine.**

If a head `head` translating to `hve` is defeq to `hve₂` (the value head's
translation), and each argument `args[i]` evaluates (in the subject-reduction
sense: translates to `a'`, the value `vs[i]` translates to some `v'`, and
`a' ≡ v'`) to `vs[i]`, then the whole spine `args.foldl Expr.app head` translating
to `ve` has its value `vs.foldl Expr.app head₂` translating to some `vve` defeq to
`ve`.

This is the spine-level congruence powering the `ctor_val` case: the head is a
`.const` (unchanged), and each argument reduces to a defeq value, so the whole
application is defeq to the application of the reduced arguments. -/
theorem SEvalβζδ_defeq_spine {env : VEnv} (henv : env.WF) {Us : List Name}
    {Δ : VLCtx} (hΔ : VLCtx.WF env Us.length Δ)
    (P : Expr → Expr → Prop)
    (hP : ∀ {e v : Expr} {ev : VExpr}, TrExprS env Us Δ e ev → P e v →
      ∃ vv, TrExprS env Us Δ v vv ∧ env.IsDefEqU Us.length Δ.toCtx ev vv) :
    ∀ (n : Nat) (args vs : List Expr) (head head₂ : Expr) (hve hve₂ : VExpr),
      args.length = n → vs.length = n →
      TrExprS env Us Δ head hve → TrExprS env Us Δ head₂ hve₂ →
      env.IsDefEqU Us.length Δ.toCtx hve hve₂ →
      (∀ i (h : i < args.length) (h2 : i < vs.length), P args[i] vs[i]) →
      ∀ {ve : VExpr}, TrExprS env Us Δ (args.foldl Expr.app head) ve →
        ∃ vve, TrExprS env Us Δ (vs.foldl Expr.app head₂) vve ∧
          env.IsDefEqU Us.length Δ.toCtx ve vve := by
  have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
  intro n
  -- Strong induction on the spine length, peeling the LAST argument (the outermost
  -- `.app` of the foldl spine), which `TrExprS.app` inverts directly.
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro args vs head head₂ hve hve₂ hlenA hlenV hh hh₂ hd hargs ve htr
    rcases List.eq_nil_or_concat args with rfl | ⟨init, last, rfl⟩
    · -- empty spine: `vs` empty too; value head is defeq to `head`'s translation.
      have : vs = [] := List.eq_nil_of_length_eq_zero (by simp_all)
      subst this
      simp only [List.foldl]
      simp only [List.foldl] at htr
      exact ⟨hve₂, hh₂,
        VEnv.IsDefEqU.trans henv hΓ (TrExprS.uniq henv
          (VLCtx.IsDefEq.refl henv.ordered hΔ) htr hh) hd⟩
    · -- `vs` must also be a snoc list `vinit ++ [vlast]` of matching length.
      rcases List.eq_nil_or_concat vs with rfl | ⟨vinit, vlast, rfl⟩
      · simp [List.concat_eq_append] at hlenA hlenV; omega
      · rw [List.concat_eq_append, List.length_append] at hlenA
        rw [List.concat_eq_append, List.length_append] at hlenV
        simp only [List.length_singleton] at hlenA hlenV
        have hlen : init.length = vinit.length := by omega
        -- Spine = `(init.foldl app head).app last`; invert the outer app.
        rw [List.concat_eq_append, List.foldl_append, List.foldl_cons,
          List.foldl_nil] at htr
        simp only [List.concat_eq_append] at hargs
        cases htr with
        | @app fve A B lastVE _Δ _f _a hTf hTa htrf htrlast =>
          -- IH on the init spine (strictly shorter).
          have hargsInit : ∀ i (h : i < init.length) (h2 : i < vinit.length),
              P init[i] vinit[i] := by
            intro i h h2
            have := hargs i (by simp; omega) (by simp; omega)
            rwa [List.getElem_append_left h, List.getElem_append_left h2] at this
          obtain ⟨fvv, htrfvv, hfdef⟩ :=
            ih init.length (by omega) init vinit head head₂ hve hve₂ rfl hlen.symm
              hh hh₂ hd hargsInit htrf
          -- The last argument: its value translates defeq (via P/hP).
          have hlastP : P last vlast := by
            have h := hargs init.length (by simp) (by simp [hlen])
            rw [List.getElem_append_right (Nat.le_refl _),
              List.getElem_append_right (hlen ▸ Nat.le_refl init.length)] at h
            simpa [hlen] using h
          obtain ⟨lvv, htrlvv, hldef⟩ := hP htrlast hlastP
          -- Reassemble the value spine `(vinit.foldl app head₂).app vlast`.
          refine ⟨.app fvv lvv, ?_, ?_⟩
          · rw [List.concat_eq_append, List.foldl_append, List.foldl_cons,
              List.foldl_nil]
            have hTfvv : env.HasType Us.length Δ.toCtx fvv (.forallE A B) :=
              hTf.defeqU_l henv hΓ hfdef
            have hTlvv : env.HasType Us.length Δ.toCtx lvv A :=
              hTa.defeqU_l henv hΓ hldef
            exact .app hTfvv hTlvv htrfvv htrlvv
          · have hfd : env.IsDefEq Us.length Δ.toCtx fve fvv (.forallE A B) :=
              VEnv.IsDefEqU.of_l henv hΓ hfdef hTf
            have hld : env.IsDefEq Us.length Δ.toCtx lastVE lvv A :=
              VEnv.IsDefEqU.of_l henv hΓ hldef hTa
            exact ⟨_, .appDF hfd hld⟩

/-- **Subject reduction as definitional equality (β + ζ + δ fragment).**

If `e` translates to `ve` and `e` evaluates to `v` under `SEvalβζδ`, then `v`
translates to some `vve` definitionally equal to `ve`.

Requires `env.WF`, `VLCtx.WF` of the context, and `SEnvConsistent` linking the
source unfolding map to the `VEnv` (for the δ case). -/
theorem SEvalβζδ_defeq {env : VEnv} (henv : env.WF) {Us : List Name} {Δ : VLCtx}
    (hΔ : VLCtx.WF env Us.length Δ) {Esrc : SEnv}
    (hcon : SEnvConsistent env Us Esrc) {e v : Expr} {ve : VExpr}
    (htr : TrExprS env Us Δ e ve)
    (hev : SEvalβζδ Esrc e v) :
    ∃ vve, TrExprS env Us Δ v vve ∧ env.IsDefEqU Us.length Δ.toCtx ve vve := by
  induction hev generalizing ve Δ with
  | lam n ty b bi =>
      exact ⟨ve, htr, VEnv.IsDefEqU.refl (htr.wf henv.ordered hΔ)⟩
  | @beta f a n ty b bi av r hf ha hbody ihf iha ihbody =>
      cases htr with
      | @app f' A B a' _Δ _f _a hTf hTa htrf htra =>
        obtain ⟨fv, htrfv, hfd⟩ := ihf hΔ htrf
        cases htrfv with
        | @lam ty' _Δ _ty _body body' _name _bi hty' htrty htrb =>
          obtain ⟨av_v, htrav, had⟩ := iha hΔ htra
          have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
          have hΔ' : VLCtx.WF env Us.length ((none, .vlam ty') :: Δ) := ⟨hΔ, nofun, hty'⟩
          obtain ⟨B'', hbodyT⟩ := htrb.wf henv.ordered hΔ'
          obtain ⟨u, hty'sort⟩ := hty'
          have lamT1 : env.HasType Us.length Δ.toCtx (.lam ty' body') (.forallE ty' B'') :=
            VEnv.HasType.lam hty'sort hbodyT
          have lamT2 : env.HasType Us.length Δ.toCtx (.lam ty' body') (.forallE A B) :=
            hTf.defeqU_l henv hΓ hfd
          have huForall : env.IsDefEqU Us.length Δ.toCtx (.forallE A B) (.forallE ty' B'') :=
            VEnv.IsDefEq.uniqU henv hΓ lamT2 lamT1
          obtain ⟨⟨w, hAty'⟩, _⟩ := VEnv.IsDefEqU.forallE_inv henv hΓ huForall
          have hadT : env.IsDefEq Us.length Δ.toCtx a' av_v A :=
            VEnv.IsDefEqU.of_l henv hΓ had hTa
          have havT : env.HasType Us.length Δ.toCtx av_v ty' :=
            (hadT.hasType.2).defeqU_r henv hΓ ⟨_, hAty'⟩
          have htrbody : TrExprS env Us Δ (b.instantiate1' av) (body'.inst av_v) :=
            TrExprS.inst henv.ordered havT htrb htrav
          obtain ⟨vve, htrr, hrd⟩ := ihbody hΔ htrbody
          refine ⟨vve, htrr, ?_⟩
          have hfdT : env.IsDefEq Us.length Δ.toCtx f' (.lam ty' body') (.forallE A B) :=
            VEnv.IsDefEqU.of_l henv hΓ hfd hTf
          have step1 : env.IsDefEq Us.length Δ.toCtx
              (.app f' a') (.app (.lam ty' body') av_v) (B.inst a') :=
            .appDF hfdT hadT
          have step2 : env.IsDefEq Us.length Δ.toCtx
              (.app (.lam ty' body') av_v) (body'.inst av_v) (B''.inst av_v) :=
            .beta hbodyT havT
          have hcong : env.IsDefEqU Us.length Δ.toCtx (.app f' a') (body'.inst av_v) :=
            VEnv.IsDefEqU.trans henv hΓ ⟨_, step1⟩ ⟨_, step2⟩
          exact VEnv.IsDefEqU.trans henv hΓ hcong hrd
  | @zeta n ty val b nd vv r hval hbody ihval ihbody =>
      -- ζ: `letE` translates straight to the body's VExpr `ve`; substituting the
      -- bound value into the body translates to the SAME `ve` (TrExprS.inst_let).
      cases htr with
      | @letE val' ty' _ _ _ _ body' _ _ hValT htrty htrval htrb =>
          have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
          -- Subject reduction on the bound value: `val` evaluates to `vv`; both
          -- translate, and `val' ≡ vvv`. So `vv` translates *up to defeq* to the
          -- let value `val'`, hence `b.instantiate1' vv` translates up to defeq to
          -- the SAME body VExpr `body' = ve` (TrExpr.inst_let).
          obtain ⟨vvv, htrvv, hvald⟩ := ihval hΔ htrval
          have hvvTrExpr : TrExpr env Us Δ vv val' :=
            ⟨vvv, htrvv, VEnv.IsDefEqU.symm hvald⟩
          have hΔlet : VLCtx.WF env Us.length ((none, .vlet ty' val') :: Δ) :=
            ⟨hΔ, nofun, hValT⟩
          have hbodyTrExpr : TrExpr env Us ((none, .vlet ty' val') :: Δ) b ve :=
            ⟨ve, htrb, VEnv.IsDefEqU.refl (htrb.wf henv.ordered hΔlet)⟩
          obtain ⟨sub', htrsub, hsubd⟩ :=
            TrExpr.inst_let henv hΔ hValT hbodyTrExpr hvvTrExpr
          -- IH on the body evaluation: `b.instantiate1' vv` evaluates to `r`.
          obtain ⟨vve, htrr, hrd⟩ := ihbody hΔ htrsub
          -- Assemble: `ve = body' ≡ sub' ≡ vve`.
          exact ⟨vve, htrr,
            VEnv.IsDefEqU.trans henv hΓ (VEnv.IsDefEqU.symm hsubd) hrd⟩
  | @delta n us body r hunf hbodyev ihbody =>
      obtain ⟨bve, htrb, hdefeq⟩ := hcon hunf htr
      obtain ⟨vve, htrr, hrd⟩ := ihbody hΔ htrb
      exact ⟨vve, htrr, VEnv.IsDefEqU.trans henv hΔ.toCtx hdefeq hrd⟩
  | @ctor_val cn us args vs hl hargs ihargs =>
      -- The head `.const cn us` is unchanged; each argument subject-reduces to a
      -- defeq value, so the whole application is defeq to the reduced application.
      obtain ⟨hve, htrhead⟩ := TrExprS_spine_head args htr
      refine SEvalβζδ_defeq_spine henv hΔ
        (fun e v => ∀ {ev}, TrExprS env Us Δ e ev →
          ∃ vv, TrExprS env Us Δ v vv ∧ env.IsDefEqU Us.length Δ.toCtx ev vv)
        (fun htr p => p htr)
        args.length args vs (Expr.const cn us) (Expr.const cn us) hve hve rfl hl.symm
        htrhead htrhead (VEnv.IsDefEqU.refl (htrhead.wf henv.ordered hΔ))
        (fun i h h2 => ihargs i h hΔ) htr
  | @lit l r hev ih =>
      -- Free: `TrExprS.lit` gives the literal and its unfolding the *same* `VExpr`,
      -- so no defeq step is needed at all — the IH is already the goal.
      cases htr with | lit _ htrC => exact ih hΔ htrC

end LeanToLambdaBox
