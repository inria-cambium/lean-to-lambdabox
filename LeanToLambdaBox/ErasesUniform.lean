import LeanToLambdaBox.ErasesStrengthen

/-!
# Context uniformity for `Erases`: strengthening to `[]`, and the two-sided composition

`DeltaHyps.uniform` *was* one of the three named residues of this development: it asserted
that a *constant body's* erasure does not depend on the `VLCtx` it was produced at,

```
uniform : Esrc n = some pe → Erases env Us Γ Δ pe t → Erases env Us Γ Δ' pe t
```

and it was believed, named, and unproved. This file retires it for the fragment the
consumers actually run in, by factoring the two-sided transport through the empty
context — `Δ → [] → Δ'` — and proving both halves. Since slice δ-D7b the field is
**deleted** from `DeltaHyps` and the capstones call `erases_uniform_closed` below; the
development's residue count is **one**, `ErasableStrengthen`, commissioned here and
tracked in `ColdStart.lean`'s trust ledger.

The **weakening** half (`[] → Δ'`) is done and lives in `ErasesStrengthen.lean`
(`erases_weakFV`, `erases_weakFV_nofvars`, `erases_weak_any`). This file supplies the
**strengthening** half (`Δ → []`) and the composition.

## Why a separate file rather than a section of `ErasesStrengthen.lean`

`ErasesStrengthen.lean` is *premise-free*: every declaration in it is unconditionally
proved, and the only thing its results cost is the ambient lean4lean trust boundary. The
strengthening direction is not free — it needs an inverse of `HasType.weakN` that lean4lean
does not have (`ErasableStrengthen`, commissioned below) and a source-side scope predicate
(`NoProj`, or since slice P2 the weaker `NoProjBinders`). Keeping the two apart keeps the
trust ledger legible: a reader who wants to know what *weakening* costs should not have to
page past a commissioned `Prop` to find out that the answer is "nothing".

## Trust boundary: inherited `sorryAx`

**Rewritten at the `fee3ada` re-pin, 2026-08-27.** This section used to say that
everything here carries `sorryAx` because `TrProj` is a `sorry`-valued *definition*
upstream, so that merely mentioning `TrExprS` was enough to inherit it. That is no longer
true, and the difference is visible in `#print axioms`:

* `TrProj` now has a real definition (`Lean4Lean/Verify/Typing/Expr.lean`: an ι-pattern
  membership in `env.pats` plus a `HasType` conjunct) and measures `[propext]`. The
  definitional taint is gone.
* `TrProj.weak'` came back **proved**, so `TrExprS.weakFV_fvwf` — the lemma every
  transport here routes through — is **sorryAx-free**, and so are
  `Erases.strengthen_fvlift` and `erases_uniform_of_nil`. The only cost A0 imposed
  downstream was an `Ordered env` premise, which `ErasesStrengthen.lean` supplies at its
  two `proj` arms.
* What still carries `sorryAx` in this file is `Erases.strengthen_fvlift_binders`,
  `erases_strengthen_closed` and `erases_uniform_closed`, and they earn it honestly: they
  are genuine consumers of `TrExprS.uniq`, which bottoms out in `TrProj.uniq` — still
  `PROJ-TODO` — and in `IsDefEq.uniqU`.

So the old caveat "**even though every source term in scope here is projection-free**" no
longer applies to the transport lemmas at all; for the strengthening lemmas the source
being projection-free is exactly what `NoProj` cashes in, via lean4lean's `sorry`-free
`TrExprS.unique`. Nothing new is trusted either way, but the boundary is narrower and
worth stating rather than discovering from an `#print axioms`.

**The P2 split (2026-08-27).** Slice P2 admits *projections* into the fragment, and it
cannot do so through `TrExprS.unique`: uniqueness at `.proj` is false, not unproved. So
this file now carries **two** strengthening inductions rather than one —
`Erases.strengthen_fvlift` at `NoProj`, `sorryAx`-free, `Ordered`+`FVWF`, and
`Erases.strengthen_fvlift_binders` at `NoProjBinders`, which trades the equation for a
definitional equality (`TrExprS.uniq` + `Erasable.defeq`) and therefore for the `TrProj.uniq`
`sorryAx`, and asks `WF`+`VLCtx.WF` for it. Keeping both is what makes the slice cost
*nothing*: the consumers of the weak one (`erases_strengthen_closed` downwards) carried
that `sorryAx` already, and the consumer of the strong one — the bridge's recursive exit,
via `DeltaHyps.BlockHyps.block_lam` — stays clean. The whole audit was
byte-identical across the slice, at its size then (750 entries; it has grown since).

## Shape of the strengthening argument, and why it is not lean4lean's `weakFV_inv`

The design of record routed the `box` arm through lean4lean's `TrExprS.weakFV_inv`
(`Verify/Typing/Lemmas.lean:1105`), recovering a small-context translation existentially
and reconciling it with the derivation's witness by `TrExprS.uniq` + `Erasable.defeq`. That
route **does not close**, for a reason that shows up first in `lam`, not in `box`:

* `weakFV_inv` yields only `∃ ve₀, TrExprS env Us [] e ve₀`, related to the derivation's
  `ve` by a *definitional equality*, never an equation. In `box` that is survivable
  (`Erasable.defeq` transports along it). In `lam` it is fatal: `Erases.lam`'s conclusion
  at the small context must be built with *some* binder-type witness `ty'₀`, and the
  induction hypothesis for the body then demands
  `VLCtx.FVLift ((none, .vlam ty'₀) :: []) ((none, .vlam ty') :: Δ) …`, i.e. exactly the
  equation `ty' = ty'₀.liftN n k` that `weakFV_inv` refuses to give.
* Absorbing that mismatch the way lean4lean does — carrying a `VLCtx.IsDefEq` slack through
  the induction — needs `env.IsType Us.length Δ.toCtx ty'` to extend the slack under the
  binder. `Erases.lam` carries only `TrExprS env Us Δ ty ty'`, **no `IsType`**. This is the
  same structural gap that forced `erases_weakFV` onto `VLCtx.FVWF` instead of `VLCtx.WF`
  (see that lemma's docstring), and here it cannot be sidestepped, because
  `weakFV_inv` genuinely consumes the typing half.

The route that does close inverts the direction of information flow: instead of *recovering*
a small-context translation from the big one, **assume** one (`hwt : TrExprS env Us Δ e ve`,
a real and dischargeable fact about any well-typed definition body), push it *outwards* with
the already-proved `TrExprS.weakFV_fvwf`, and identify it with the derivation's witness by
lean4lean's `TrExprS.unique` (`Verify/Typing/Lemmas.lean:1641`) — which is `sorry`-free and
gives **equality on the nose**, at the price of a projection-freeness side condition on the
source (`NoProj` below; `TrExprS.IsUnique` upstream). With the equation in hand every arm is
structural, no `VLCtx.WF` is needed anywhere in the induction, and the only genuinely
missing fact is the `VExpr`-level one: `ErasableStrengthen`.

**And where the `weakFV_inv` route was blocked, the P2 route is not.** The paragraph above
rejects recovering `ty'₀` existentially; `Erases.strengthen_fvlift_binders` does something
else: it keeps `hwt` as the source of the small-context witness — so the binder arms still
get their equation from `TrExprS.unique`, and the `lam` obstruction never arises — and
spends the definitional equality *only* in `box`, where the module's own verdict
("survivable, `Erasable.defeq` transports along it") applies. That is also where the
`VLCtx.WF` it asks for comes from: not from an `Erases` premise, which indeed has no
`IsType`, but from `hwt`, because lean4lean's `TrExprS.lam`/`TrExprS.letE` *do* record the
binder's `IsType`/`HasType`. So the "cannot survive this induction" verdict
`erases_weakFV` records for `VLCtx.WF` is about *that* induction; with a translation
premise in hand it does survive.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-! ## The commissioned `VExpr`-level obligation -/

/--
**`HasType.weakN_inv`, for `Erasable`** — the one fact this file does not prove.

`Erasable env U Γ e` (`Erasability.lean`) is `∃ A, HasType U Γ e A ∧ (HasType U Γ A (.sort 0)
∨ IsArityUpTo env U Γ A)`. It ships with `weakN`, `inst`, `defeq` and `defeqDFC`, and with
**no inverse of `weakN`**: nothing in the file, and nothing upstream, turns erasability of
`ve.liftN n k` in a larger context back into erasability of `ve` in the smaller one. That
inverse is what the `box` arm of `erases_strengthen_closed` needs, and it is stated here as
a named premise rather than assumed as an axiom or hidden in a `sorry`.

**Why it is commissioned upstream and not proved here.** It is the `Erasable`-shaped
instance of `VEnv.HasType.weakN_inv`, and the pinned lean4lean does not have that lemma for
the `VEnv.HasType` that `Verify/Typing` is stated over:

* the only *live* inverse is `VEnv.IsDefEqU.weakN_iff`
  (`.lake/packages/lean4lean/Lean4Lean/Theory/Typing/UniqueTyping.lean:172`), and its
  forward direction is literally `sorry` (line 174). Everything downstream of it —
  `IsDefEq.weakN_iff'`, `HasType.weakN_iff` (:216), `IsType.weakN_iff` (:221),
  `OnCtx.weakN_inv` (:198), `IsDefEq.skips` (:180) — inherits that;
* the *stratified* theories do state a real `IsDefEq.weakN_inv` / `HasType.weakN_inv`
  (`Lean4Lean/Experimental/Stratified.lean:290`/`:325`,
  `Lean4Lean/Experimental/StratifiedUntyped.lean:275`/`:310`), but both occurrences sit
  **inside a `/- depends on church-rosser … -/` comment block**
  (Stratified.lean:288-332, StratifiedUntyped.lean:273-317) and even the commented proofs
  leave `trans` and the catch-all case `sorry`. So the design note's "lean4lean proves this
  for the stratified theories" is, as of this pin, too generous: nobody proves it.

**How much of it is already reachable.** Granting the sorried `weakN_iff`, the *proof*
disjunct is a five-line derivation: `VExpr.WF.weakN_iff` recovers `∃ A₀, HasType U Γ₀ ve A₀`,
`uniqU` identifies `A` with `A₀.liftN n k`, and `HasType.weakN_iff` at `A := .sort 0`
(which is its own lift) strengthens `A₀ : Sort 0`. The *arity* disjunct is the real residue:
from `IsDefEqU U Γ₁ (A₀.liftN n k) A'` with `IsArity A'` one has to produce an arity at `Γ₀`,
and `A'` need not be a lift — that needs a `forallE` inversion through a lift, which is
exactly the church-rosser-flavoured fact the commented-out block is waiting on. So the
honest description is: **one obligation, whose hard half is `IsArityUpTo`**.

**Asked for, and answered in the negative — this premise STAYS (2026-08-27, pin
`fee3ada`).** The paragraph above used to end "expected to be a short discharge after a
re-pin that lands `weakN_inv`". That expectation is now retired: the forward direction of
`IsDefEqU.weakN_iff` was commissioned upstream as item C1 of the trproj round and **did
not close**. `UniqueTyping.lean:174` is byte-identical to the previous pin — the gap was
not reshaped, renamed, or re-exported as a fresh sorried `HasType.weakN_inv` for us to
consume. What came back instead is the sanctioned alternative, a written analysis of where
the proof breaks, and it argues the route is blocked rather than merely unfinished:

* the induction on `IsDefEq` carries every structural case, `defeqDF` included (`IsDefEqU`
  discards the type), and stalls on **`trans`** — the middle term of a conversion chain is
  an arbitrary `VExpr`, not a lift, so neither IH applies;
* eliminating `trans`-intermediates is exactly what confluence buys, and the confluence
  route is blocked **two independent ways**. (a) A **module import cycle**:
  `ChurchRosser.lean` *imports* `UniqueTyping.lean`, so `weakN_iff` sits structurally
  upstream of all reduction and normal-form machinery — it cannot call what would prove it.
  (b) A **same-measure logical cycle**: `weakN_iff` is itself a prerequisite of the
  confluence development, called non-reflexively at the same size, with no evident
  well-founded measure to fuse the two (`Prop`-impredicativity and `imax` defeat level
  measures).
* And a finding sharper than our own framing: closing the `church_rosser` `pat`
  `IOTA-TODO` is **necessary but not sufficient**. We had flagged the `pat` case as a
  possible prerequisite; landing ι-confluence would still leave C1 blocked.

So this premise is not waiting on a re-pin. Discharging it needs new metatheory upstream,
and until that exists, naming it here — visible, guarded, never an axiom — is the correct
posture, and it is now the recommendation from both sides rather than a choice of ours.
The trproj round *did* land `TrProj` as a real definition, which is why the rest of this
file's `Erases` transport lemmas are sorryAx-free; it left this one obligation exactly
where it was.

This is the established idiom for a named obligation in this development — same shape and
same guard discipline as `PatsIotaSpec` (`IotaPattern.lean`), which likewise names an
upstream fact and is carried as an explicit premise of its capstone. `PatsIotaSpec` was
retired by a re-pin rather than by an axiom; this one, on present evidence, will not be.
-/
def ErasableStrengthen (env : VEnv) (Us : List Name) : Prop :=
  ∀ {Γ₀ Γ₁ : List VExpr} {ve : VExpr} {n k : Nat},
    Ctx.LiftN n k Γ₀ Γ₁ → Erasable env Us.length Γ₁ (ve.liftN n k) →
    Erasable env Us.length Γ₀ ve

/-- A `Ctx.LiftN` that lifts by `0` is the identity on contexts. Auxiliary to the
non-vacuity guard below; also the reason the guard is honest rather than circular — the
identity instance is *derived* from `Ctx.LiftN`'s constructors, not assumed. -/
protected theorem Ctx.LiftN.zero_eq :
    ∀ {k : Nat} {Γ₀ Γ₁ : List VExpr}, Ctx.LiftN 0 k Γ₀ Γ₁ → Γ₀ = Γ₁
  | _, _, _, .zero As h => by cases List.eq_nil_of_length_eq_zero h; simp
  | _, _, _, .succ W => by rw [Ctx.LiftN.zero_eq W]; simp

/-- **Non-vacuity guard for `ErasableStrengthen`.** The property is not vacuously false:
at every `n = 0` lift it holds, and holds as the identity — `Ctx.LiftN 0 k` forces
`Γ₀ = Γ₁` and `ve.liftN 0 k = ve`, so the implication is `id`.

This is deliberately *not* a full instance (a full instance is the commissioned content).
What it rules out is the failure mode that makes a named `Prop` worthless: a statement
whose quantifier structure is subtly wrong, so that no `env`/`Us` could satisfy it and the
theorems taking it as a premise are vacuous. Together with the two `example`s at the end of
the file — which construct real `Erases` derivations and transport them — it pins the
statement to the intended content. -/
theorem erasableStrengthen_liftN_zero {env : VEnv} {U : Nat} {Γ₀ Γ₁ : List VExpr}
    {ve : VExpr} {k : Nat} (W : Ctx.LiftN 0 k Γ₀ Γ₁)
    (h : Erasable env U Γ₁ (ve.liftN 0 k)) : Erasable env U Γ₀ ve := by
  cases Ctx.LiftN.zero_eq W; simpa using h

/-! ## `NoProj`: the source-side scope condition

lean4lean's `TrExprS.unique` (`Verify/Typing/Lemmas.lean:1641`) is the only *equational*
handle on a `TrExprS` witness anywhere in the pinned tree — every other route
(`TrExprS.uniq`, `TrExpr`) delivers a definitional equality — and it is gated on
`TrExprS.IsUnique e`, i.e. "`e` contains no `.proj`". That is exactly the fragment this
development is scoped to (`Erases.lean`, "Projection-free"), so the gate is free.

`IsUnique` is very slightly too weak for us: it skips a `let`-binder's *type* annotation
(`IsUnique (.letE _ t v b _) = IsUnique v ∧ IsUnique b`), because the translation of `t`
does not affect the translation of the `let` — `VLCtx.toCtx` skips a `.vlet` and its
`find?` value component is the *value*, not the type. `Erases.letE` nevertheless *records*
the type's witness `ty'` in its premise `hty` and in the body's context entry
`(none, .vlet ty' val')`, so the strengthening does have to pin it. `NoProj` is `IsUnique`
plus that one clause.

The alternative — swapping the `.vlet` entry's type component after the fact, via a
depth-indexed context-surgery relation in the style of `ThinVLet` — was rejected: it is
another inductive relation plus a full `TrExprS` transport induction, to buy back a clause
that the intended scope already grants. -/

/-- Projection-freeness of a source `Lean.Expr`, at *every* subterm including a
`let`-binder's type annotation. Strictly stronger than lean4lean's `TrExprS.IsUnique`
(`NoProj.toIsUnique`), which omits the `letE` type; see the section note for why the
extra clause is needed here. -/
def NoProj : Expr → Prop
  | .bvar _ | .fvar _ | .sort _ | .const .. | .mvar .. | .lit _ => True
  | .app f a => NoProj f ∧ NoProj a
  | .lam _ t b _ => NoProj t ∧ NoProj b
  | .forallE _ t b _ => NoProj t ∧ NoProj b
  | .letE _ t v b _ => NoProj t ∧ NoProj v ∧ NoProj b
  | .mdata _ e => NoProj e
  | .proj .. => False

/-- `NoProj` implies lean4lean's `TrExprS.IsUnique`, which is what `TrExprS.unique`
consumes. The two agree everywhere except at `letE`, where `NoProj` additionally
constrains the type annotation. -/
theorem NoProj.toIsUnique : ∀ {e : Expr}, NoProj e → TrExprS.IsUnique e
  | .bvar _, _ | .fvar _, _ | .sort _, _ | .const .., _ | .mvar .., _ | .lit _, _ => ⟨⟩
  | .app .., h => ⟨h.1.toIsUnique, h.2.toIsUnique⟩
  | .lam .., h => ⟨h.1.toIsUnique, h.2.toIsUnique⟩
  | .forallE .., h => ⟨h.1.toIsUnique, h.2.toIsUnique⟩
  | .letE .., h => ⟨h.2.1.toIsUnique, h.2.2.toIsUnique⟩
  | .mdata _ e, h => NoProj.toIsUnique (e := e) h
  | .proj .., h => h.elim

/-- The peano unfolding of a `Nat` literal is projection-free. Mirrors
`TrExprS.IsUnique.natLitToConstructor`; needed for the `Erases.lit` arm, whose induction
hypothesis is about `l.toConstructor`. -/
theorem NoProj.natLitToConstructor : ∀ {n : Nat}, NoProj (.natLitToConstructor n)
  | 0 => ⟨⟩
  | _ + 1 => ⟨⟨⟩, ⟨⟩⟩

/-- The `List Char` unfolding of a string literal is projection-free. Mirrors
`TrExprS.IsUnique.strLitToConstructor`. (`.strVal` derivations are never *produced* — the
shipping eraser panics and `Supported` excludes them — but `Erases.lit` is
literal-agnostic, so the arm has to be discharged.) -/
theorem NoProj.strLitToConstructor {s : String} : NoProj (.strLitToConstructor s) := by
  refine ⟨⟨⟩, ?_⟩
  induction s.toList with simp
  | nil => exact ⟨⟨⟩, ⟨⟩⟩
  | cons _ _ ih => exact ⟨⟨⟨⟨⟩, ⟨⟩⟩, ⟨⟨⟩, ⟨⟩⟩⟩, ih⟩

/-- Every literal's one-step constructor unfolding is projection-free. -/
theorem NoProj.toConstructor : ∀ {l : Literal}, NoProj l.toConstructor
  | .natVal _ => .natLitToConstructor
  | .strVal _ => .strLitToConstructor

/-- `NoProj` restricted along an application spine built by `List.foldl Expr.app` — the
form `Erases.ctor`/`Erases.cases` use for their sources. Exact analogue of
`fvarsIn_foldl_app` (`ErasesStrengthen.lean`), same proof skeleton. -/
theorem noProj_foldl_app {args : List Expr} {f : Expr}
    (h : NoProj (args.foldl Expr.app f)) :
    NoProj f ∧ ∀ a ∈ args, NoProj a := by
  induction args generalizing f with
  | nil => exact ⟨h, nofun⟩
  | cons a as ih =>
    have ⟨hfa, has⟩ := ih h
    refine ⟨hfa.1, fun b hb => ?_⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · exact hfa.2
    · exact has _ hb

/-! ## `NoProjBinders`: the same condition, at the three positions that spend it

`NoProj` is **too strong for the payoff**. `NoProj (.proj ..) = False`, so a body with a
projection anywhere at all is outside it — and every typeclass method's prepared body is
exactly such a term (`OfNat.ofNat` is `fun α x self => self.1`). Since slice P1 `Erases`
has a `proj` rule, so the erasure *relation* covers those bodies; what still excluded them
was this predicate, through `DeltaHyps.esrc_shape`.

Reading `Erases.strengthen_fvlift` shows `NoProj` is *threaded* everywhere but *consumed*
at exactly three places — a boxed subterm (whole), a λ binder's type, and a `let`'s type
and value: the three positions at which `Erases` records a `VExpr` witness that an
`FVLift` has to match **on the nose**. `NoProjBinders` keeps the condition at the
binder-shaped ones and drops it everywhere computational.

The boxed-subterm position is the one that cannot simply be dropped; it is *paid for*
instead, in `Erases.strengthen_fvlift_binders`' box arm, which replaces the equation
`TrExprS.unique` gives by the definitional equality `TrExprS.uniq` gives and transports the
erasability witness along it (`Erasable.defeq`, the "box survives defeq" move this file's
module note already names). That trade is what costs the weaker lemma a `sorryAx` —
`TrExprS.uniq` bottoms out in `TrProj.uniq`, still `PROJ-TODO` — and it is why **both**
lemmas are kept rather than one: the equational lemma stays `sorryAx`-free and is what the
bridge's recursive exit runs on, and the defeq one is consumed only by
`erases_strengthen_closed`, which carries that `sorryAx` already. No declaration in the
development changes its axiom set on account of this section.

**Why the relaxation cannot go further.** Equational uniqueness at `.proj` is *false*, not
merely unproved: `TrProj` pins `params`/`fieldTys`/the motive only up to definitional
equality, which is why `TrProj.uniq` claims `IsDefEqU` and why upstream's `TrExprS.unique'`
refutes its `proj` arm outright (`| proj => cases H`). No re-pin can make the `lam`/`letE`
clauses below go away: under a binder the strengthening needs the equation, and at a
projection the equation does not exist. `NoProjBinders` is that boundary, exactly.

**The scope cut it leaves.** The `letE` clauses are the residue: `let y := self.1; …` is
still outside, because `Erases.letE` records *both* components of the `.vlet` entry and the
body's induction hypothesis runs at a context mentioning them. Lifting that needs the
depth-indexed `.vlet` surgery the `NoProj` section note above prices and rejects, and it is
a later slice rather than a blocker — a prepared class-method body is a λ telescope over a
projection, not a `let` over one. -/

/-- **Projection-freeness at the positions the strengthening lemma spends uniqueness on**:
a λ/∀ binder's type, and a `let`'s type and bound value. Projections are permitted
everywhere computational — λ and `let` bodies, application heads and arguments,
constructor arguments, `casesOn` minors, and under a projection.

Strictly weaker than `NoProj` (`NoProj.toNoProjBinders`), and — unlike `NoProj` —
satisfied by a typeclass method's prepared body (`noProjBinders_ofNatBody`, with the
companion refutation `noProj_ofNatBody_refuted`). -/
def NoProjBinders : Expr → Prop
  | .bvar _ | .fvar _ | .sort _ | .const .. | .mvar .. | .lit _ => True
  | .app f a => NoProjBinders f ∧ NoProjBinders a
  | .lam _ t b _ => NoProj t ∧ NoProjBinders b
  | .forallE _ t b _ => NoProj t ∧ NoProjBinders b
  | .letE _ t v b _ => NoProj t ∧ NoProj v ∧ NoProjBinders b
  | .mdata _ e => NoProjBinders e
  | .proj _ _ e => NoProjBinders e

/-- The weakening, so that every existing `NoProj` producer still discharges the new
predicate and no call site has to be re-proved. -/
theorem NoProj.toNoProjBinders : ∀ {e : Expr}, NoProj e → NoProjBinders e
  | .bvar _, _ | .fvar _, _ | .sort _, _ | .const .., _ | .mvar .., _ | .lit _, _ => ⟨⟩
  | .app .., h => ⟨h.1.toNoProjBinders, h.2.toNoProjBinders⟩
  | .lam .., h => ⟨h.1, h.2.toNoProjBinders⟩
  | .forallE .., h => ⟨h.1, h.2.toNoProjBinders⟩
  | .letE .., h => ⟨h.1, h.2.1, h.2.2.toNoProjBinders⟩
  | .mdata _ e, h => NoProj.toNoProjBinders (e := e) h
  | .proj .., h => h.elim

/-- Every literal's one-step constructor unfolding satisfies the weak predicate too — the
`Erases.lit` arm's induction hypothesis, as `NoProj.toConstructor` supplies it for the
strong one. -/
theorem NoProjBinders.toConstructor {l : Literal} : NoProjBinders l.toConstructor :=
  NoProj.toConstructor.toNoProjBinders

/-- `NoProjBinders` along an application spine — the `noProj_foldl_app` analogue the
`ctor`/`cases` arms need, same proof skeleton. -/
theorem noProjBinders_foldl_app {args : List Expr} {f : Expr}
    (h : NoProjBinders (args.foldl Expr.app f)) :
    NoProjBinders f ∧ ∀ a ∈ args, NoProjBinders a := by
  induction args generalizing f with
  | nil => exact ⟨h, nofun⟩
  | cons a as ih =>
    have ⟨hfa, has⟩ := ih h
    refine ⟨hfa.1, fun b hb => ?_⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · exact hfa.2
    · exact has _ hb

/-! ### Non-vacuity of the relaxation

The point of the weakening is a single term shape, so the guard is that term: a class
method's prepared body, in the `OfNat.ofNat` shape the projection round is aimed at.
`NoProjBinders` holds of it and `NoProj` is *refuted* on it — the two halves together are
what say the relaxation buys the thing it was built for rather than restating the old
predicate under a new name. (A genuine `TrExprS` witness for a body of this shape — the
other conjunct `DeltaHyps.esrc_shape` demands — is `ProjPattern.gEsrcShapeProj`.) -/

/-- `fun (α : Type) (x : Nat) (self : OfNat α x) => self.1` — `OfNat.ofNat`'s prepared
body, as a source `Expr`. -/
def ofNatBody : Expr :=
  .lam `α (.sort (.succ .zero))
    (.lam `x (.const `Nat [])
      (.lam `self (.app (.app (.const `OfNat []) (.bvar 1)) (.bvar 0))
        (.proj `OfNat 0 (.bvar 0)) .instImplicit)
      .default)
    .implicit

/-- The class method's body **satisfies** the weakened predicate: its three binder types
are `Type`, `Nat` and `OfNat α x`, all projection-free, and its projection sits in the
body. -/
theorem noProjBinders_ofNatBody : NoProjBinders ofNatBody :=
  ⟨⟨⟩, ⟨⟩, ⟨⟨⟨⟩, ⟨⟩⟩, ⟨⟩⟩, ⟨⟩⟩

/-- …and **fails** the old one, at the projection in its body. This is the wall slice P2
takes down: with `NoProj` in `DeltaHyps.esrc_shape` the entire typeclass-dispatch layer is
outside the fragment, no matter what `Erases` can derive. -/
theorem noProj_ofNatBody_refuted : ¬ NoProj ofNatBody := fun h => h.2.2.2

/-- Spine inversion for `TrExprS`, in the weak "each piece is translatable" form the
strengthening needs. `Erases.ctor`/`Erases.cases` relate a *source spine* to a single
target node, so their induction hypotheses are about the individual arguments; this
supplies the per-argument `TrExprS` witness the induction must feed them.

Only existence is claimed — the witnesses themselves are never used, they only unlock the
induction hypothesis — which is why this is three lines rather than a `Forall₂`-shaped
inversion in the style of `TrExprS.mkApps_inv` (`IotaPattern.lean`); reusing that one would
mean importing the ι pattern machinery for nothing. -/
theorem trExprS_foldl_app {env : VEnv} {Us : List Name} {Δ : VLCtx} :
    ∀ {args : List Expr} {f : Expr} {ve : VExpr},
      TrExprS env Us Δ (args.foldl Expr.app f) ve →
      (∃ vf, TrExprS env Us Δ f vf) ∧ ∀ a ∈ args, ∃ va, TrExprS env Us Δ a va
  | [], _, ve, h => ⟨⟨ve, h⟩, nofun⟩
  | a :: as, f, _, h => by
    obtain ⟨⟨_, hfa⟩, has⟩ := trExprS_foldl_app (args := as) (f := .app f a) h
    cases hfa with
    | app _ _ hf ha =>
      refine ⟨⟨_, hf⟩, fun b hb => ?_⟩
      rcases List.mem_cons.1 hb with rfl | hb
      · exact ⟨_, ha⟩
      · exact has _ hb

/-! ## Strengthening `Erases` along an `FVLift` -/

/--
**Strengthening for `Erases`, at depth** (the induction-ready form): an erasure derivation
at an fvar-extension `Δ'` of `Δ` also holds at `Δ`, provided the source is projection-free
and *already translatable at `Δ`*.

Read the three premises as one package:

* **`hwt : TrExprS env Us Δ e ve`** is the engine, not a technicality. Strengthening a
  `TrExprS` witness is a typing-inversion problem that lean4lean can only answer
  existentially (`TrExprS.weakFV_inv`), and existentially is not good enough under a binder
  (module docstring). Assuming the small-context translation instead turns the problem
  around: push `hwt` out to `Δ'` with `TrExprS.weakFV_fvwf` and let `TrExprS.unique` — which
  is `sorry`-free and *equational* — identify it with whatever witness the derivation is
  carrying. Every `TrExprS`-bearing arm (`box`, `lam`, `letE`) is then a rewrite. The
  premise is discharged at every intended call site by the source being a well-typed,
  closed, fvar-free definition body.
* **`hnp : NoProj e`** is what `TrExprS.unique` charges for the equation, plus one clause
  for `letE` types (see the `NoProj` section note). It is the development's documented
  scope, not a new restriction — and since slice P2 it is the *narrower* of the two
  scopes this file offers: `Erases.strengthen_fvlift_binders` runs at `NoProjBinders`,
  which admits projections, and pays for them. This lemma is the one that stays
  `sorryAx`-free, and it is what the recursive exit runs on.
* **`hΔ' : Δ'.FVWF`** is `TrExprS.weakFV_fvwf`'s premise and nothing more. Note what is
  *absent*: no `VLCtx.WF`, no `env.WF`, no closedness or fvar-freeness of `e` — closedness
  and fvar-freeness are consequences of `hwt` (`TrExprS.closed`, `TrExprS.fvarsIn`), and
  the typing half of `VLCtx.WF` is never touched, because the equation removes any need for
  a `VLCtx.IsDefEq` slack.

Two arms deserve a note:

* **`box`** is the only place `hstr` is spent, and it is spent exactly once, on the nose:
  `TrExprS.unique` rewrites the derivation's `Erasable env _ Δ'.toCtx ve✝` into
  `Erasable env _ Δ'.toCtx (ve.liftN n k)`, and `hstr W.toCtx` strengthens it to
  `Erasable env _ Δ.toCtx ve`. No `Erasable.defeq`, no `TrExprS.uniq`, no `OnCtx`.
* **`fixvar`** is free in this direction, and that is worth recording: it carries
  `hfresh : x ∉ Δ'.fvars`, strengthening *removes* fvars (`VLCtx.FVLift.fvars_suffix`), so
  freshness transports downwards for nothing. Weakening had to pay for this arm with a side
  condition (`erases_weakFV`'s `hfv`) or kill it outright (`erases_weakFV_nofvars`'s
  `hnfv`); strengthening needs neither, so no `Γ.fixvars = fun _ => none` premise appears.

The target `LBTerm` never moves: an `FVLift` re-lifts only the hidden `VExpr` witnesses, and
neither language's de Bruijn indices see fvar entries. So — unlike `erases_shift` — the
`ctor`/`cases` arms hold no spine bookkeeping at all.
-/
theorem Erases.strengthen_fvlift {env : VEnv} (henv : env.Ordered) {Us : List Name}
    {Γ : ErasureCtx} (hstr : ErasableStrengthen env Us)
    {Δ' : VLCtx} {e : Expr} {t : LBTerm} (h : Erases env Us Γ Δ' e t) :
    ∀ {Δ : VLCtx} {dk n k : Nat} {ve : VExpr}, VLCtx.FVLift Δ Δ' dk n k → Δ'.FVWF →
      NoProj e → TrExprS env Us Δ e ve → Erases env Us Γ Δ e t := by
  induction h with
  | @box _ _ _ htr her =>
      intro _ _ _ _ _ W hΔ' hnp hwt
      cases TrExprS.unique hnp.toIsUnique htr (TrExprS.weakFV_fvwf henv W hΔ' hwt)
      exact .box hwt (hstr W.toCtx her)
  | lit hcl _ ih =>
      intro _ _ _ _ _ W hΔ' _ hwt
      cases hwt with
      | lit _ h2 => exact .lit hcl (ih W hΔ' NoProj.toConstructor h2)
  | proj S i iid np nf hs hnfs hi _ _ =>
      -- **Vacuous, and deliberately so.** The scope predicate here is `NoProj`, and
      -- `NoProj (.proj ..) = False`, so this arm is unreachable — because the lemma's
      -- engine is `TrExprS.unique`, whose `proj` arm upstream is `cases H`, and
      -- equational uniqueness at `.proj` is *false*, not merely unproved (`TrProj` pins
      -- `params`/`fieldTys` only up to defeq). The **real** arm is
      -- `Erases.strengthen_fvlift_binders`' (slice P2), which runs at `NoProjBinders`
      -- and pays for the box arm with a definitional equality instead. This lemma stays
      -- because it stays `sorryAx`-free; see that one's docstring for the division.
      intro _ _ _ _ _ _ _ hnp _; exact absurd hnp id
  | bvar i => intro _ _ _ _ _ _ _ _ _; exact .bvar i
  | fvar x => intro _ _ _ _ _ _ _ _ _; exact .fvar x
  | const n us kn h hctor hcases =>
      intro _ _ _ _ _ _ _ _ _; exact .const n us kn h hctor hcases
  | app _ _ ihf iha =>
      intro _ _ _ _ _ W hΔ' hnp hwt
      cases hwt with
      | app _ _ hf ha => exact .app (ihf W hΔ' hnp.1 hf) (iha W hΔ' hnp.2 ha)
  | @lam _ _ _ _ _ _ ty' hty _ ihb =>
      intro _ _ _ _ _ W hΔ' hnp hwt
      cases hwt with
      | lam _ hty₀ hb₀ =>
        -- `TrExprS.unique` pins the derivation's binder-type witness to the lift of ours,
        -- which is exactly what makes `W.cons_bvar` typecheck against `hb`'s context.
        cases TrExprS.unique hnp.1.toIsUnique hty (TrExprS.weakFV_fvwf henv W hΔ' hty₀)
        exact .lam hty₀ (ihb (W.cons_bvar (.vlam _)) ⟨hΔ', nofun⟩ hnp.2 hb₀)
  | @letE _ _ _ _ _ _ _ _ ty' val' hty hval _ _ ihv ihb =>
      intro _ _ _ _ _ W hΔ' hnp hwt
      cases hwt with
      | letE _ hty₀ hval₀ hb₀ =>
        -- Both components of the `.vlet` entry have to be pinned: `hnp.1` (the `letE` type
        -- clause `TrExprS.IsUnique` omits) and `hnp.2.1` do it.
        cases TrExprS.unique hnp.1.toIsUnique hty (TrExprS.weakFV_fvwf henv W hΔ' hty₀)
        cases TrExprS.unique hnp.2.1.toIsUnique hval (TrExprS.weakFV_fvwf henv W hΔ' hval₀)
        exact .letE hty₀ hval₀ (ihv W hΔ' hnp.2.1 hval₀)
          (ihb (W.cons_bvar (.vlet ..)) ⟨hΔ', nofun⟩ hnp.2.2 hb₀)
  | ctor cn us iid cidx hc hlen _ ihargs =>
      intro _ _ _ _ _ W hΔ' hnp hwt
      have ⟨_, hallnp⟩ := noProj_foldl_app hnp
      have ⟨_, hallwt⟩ := trExprS_foldl_app hwt
      refine .ctor cn us iid cidx hc hlen fun i hi => ?_
      obtain ⟨_, hva⟩ := hallwt _ (List.getElem_mem hi)
      exact ihargs i hi W hΔ' (hallnp _ (List.getElem_mem hi)) hva
  | ctor_head cn us iid cidx hc =>
      intro _ _ _ _ _ _ _ _ _; exact .ctor_head cn us iid cidx hc
  | cases con us iid numParams pre hc hpre hnfs _ hlen hnlen harity _ ihd ihalts =>
      intro _ _ _ _ _ W hΔ' hnp hwt
      have ⟨_, hallnp⟩ := noProj_foldl_app hnp
      have ⟨_, hallwt⟩ := trExprS_foldl_app hwt
      obtain ⟨_, hvd⟩ := hallwt _ (.head _)
      refine .cases con us iid numParams pre hc hpre hnfs
        (ihd W hΔ' (hallnp _ (.head _)) hvd) hlen hnlen harity fun j hj => ?_
      obtain ⟨_, hvm⟩ := hallwt _ (.tail _ (List.getElem_mem hj))
      exact ihalts j hj W hΔ' (hallnp _ (.tail _ (List.getElem_mem hj))) hvm
  | fixvar nm us x hfx hctor hcases hfresh =>
      -- Strengthening removes fvars, so the rule's own freshness premise survives verbatim.
      intro _ _ _ _ _ W _ _ _
      exact .fixvar nm us x hfx hctor hcases fun hm => hfresh (W.fvars_suffix.subset hm)
  | const_fix nm us hrec hctor hcases hshift hsubst htobv =>
      intro _ _ _ _ _ _ _ _ _
      exact .const_fix nm us hrec hctor hcases hshift hsubst htobv
  | @fix Δc idx nm tty tb tbi nms srcs defs hidx hnlen hslen hsrc hreg hrarg
      hlift hinst habsl hshift hsubst htobv hbodies _ihb =>
      -- Only the conclusion context moves; the block and its `∀ Δf` bodies are untouched.
      intro _ _ _ _ _ _ _ _ _
      exact .fix idx hidx hnlen hslen hsrc hreg hrarg hlift hinst habsl hshift hsubst htobv
        hbodies

/--
**Strengthening for `Erases`, with projections allowed** (slice P2) — the same statement
at `NoProjBinders`, which is what makes the typeclass-dispatch layer reachable.

Three premises move, and each move is forced by the box arm:

* **`NoProj e` becomes `NoProjBinders e`.** That is the point; see the section note.
* **`Δ'.FVWF` becomes `VLCtx.WF env Us.length Δ'`.** `TrExprS.uniq` needs a
  `VLCtx.IsDefEq env Us.length Δ' Δ'` and `Erasable.defeq` an
  `OnCtx Δ'.toCtx (env.IsType Us.length)`; both are `VLCtx.WF` and neither is `FVWF`. The
  induction can carry it — which is *not* obvious, since `erases_weakFV`'s docstring
  records that `VLCtx.WF` "cannot survive this induction" — because this lemma also carries
  `hwt`, and lean4lean's `TrExprS.lam`/`TrExprS.letE` *do* record the binder's
  `IsType`/`HasType`. Weakening that witness along `W.toCtx` is exactly the `VLocalDecl.WF`
  the extended context needs. So the typing half is available here for a reason
  `erases_weakFV` has no analogue of: the small-context translation is a premise.
* **`env.Ordered` becomes `env.WF`.** `TrExprS.uniq` and `Erasable.defeq` both want it,
  and both consumers (`erases_strengthen_closed` and its callers) hold it already.

**Trust.** The box arm consumes `TrExprS.uniq`, hence `TrProj.uniq`, hence `sorryAx` —
the same single upstream `PROJ-TODO` channel `erases_strengthen_closed` and
`erases_uniform_closed` have carried since the `fee3ada` re-pin. Nothing else is added and
nothing else moves: the equational `Erases.strengthen_fvlift` above stays `sorryAx`-free
and keeps its consumer (the bridge's recursive exit), so no declaration that was clean
before this slice is clean no longer.
-/
theorem Erases.strengthen_fvlift_binders {env : VEnv} (henv : env.WF) {Us : List Name}
    {Γ : ErasureCtx} (hstr : ErasableStrengthen env Us)
    {Δ' : VLCtx} {e : Expr} {t : LBTerm} (h : Erases env Us Γ Δ' e t) :
    ∀ {Δ : VLCtx} {dk n k : Nat} {ve : VExpr}, VLCtx.FVLift Δ Δ' dk n k →
      VLCtx.WF env Us.length Δ' →
      NoProjBinders e → TrExprS env Us Δ e ve → Erases env Us Γ Δ e t := by
  induction h with
  | @box _ _ _ htr her =>
      -- The arm that pays for the relaxation. `TrExprS.unique` is unavailable (the boxed
      -- subterm may itself be a projection), so `TrExprS.uniq` supplies a definitional
      -- equality instead and `Erasable.defeq` transports the irrelevance witness along
      -- it — the "survivable in `box`, fatal in `lam`" split the module note describes.
      intro _ _ _ _ _ W hΔ' _ hwt
      refine .box hwt (hstr W.toCtx (her.defeq henv hΔ'.toCtx ?_))
      exact TrExprS.uniq henv (.refl henv.ordered hΔ') htr
        (TrExprS.weakFV_fvwf henv.ordered W hΔ'.fvwf hwt)
  | lit hcl _ ih =>
      intro _ _ _ _ _ W hΔ' _ hwt
      cases hwt with
      | lit _ h2 => exact .lit hcl (ih W hΔ' NoProjBinders.toConstructor h2)
  | proj S i iid np nf hs hnfs hi _ ih =>
      -- The arm slice P1 could only leave vacuous, and it is free: a projection records
      -- no `VExpr` witness of its own (`Erases.proj` has no `TrExprS` premise), so there
      -- is nothing for an `FVLift` to pin and the discriminant's IH is the whole proof.
      intro _ _ _ _ _ W hΔ' hnp hwt
      cases hwt with
      | proj hd _ => exact .proj S i iid np nf hs hnfs hi (ih W hΔ' hnp hd)
  | bvar i => intro _ _ _ _ _ _ _ _ _; exact .bvar i
  | fvar x => intro _ _ _ _ _ _ _ _ _; exact .fvar x
  | const n us kn h hctor hcases =>
      intro _ _ _ _ _ _ _ _ _; exact .const n us kn h hctor hcases
  | app _ _ ihf iha =>
      intro _ _ _ _ _ W hΔ' hnp hwt
      cases hwt with
      | app _ _ hf ha => exact .app (ihf W hΔ' hnp.1 hf) (iha W hΔ' hnp.2 ha)
  | @lam _ _ _ _ _ _ ty' hty _ ihb =>
      intro _ _ _ _ _ W hΔ' hnp hwt
      cases hwt with
      | lam hty₀ty hty₀ hb₀ =>
        -- Unchanged from the equational lemma: the binder type is projection-free by
        -- `hnp.1`, so `TrExprS.unique` still applies here. What is new is the third
        -- component of the extended `VLCtx.WF`, and `TrExprS.lam` is carrying it.
        cases TrExprS.unique hnp.1.toIsUnique hty
          (TrExprS.weakFV_fvwf henv.ordered W hΔ'.fvwf hty₀)
        exact .lam hty₀ (ihb (W.cons_bvar (.vlam _))
          ⟨hΔ', nofun, hty₀ty.weakN henv.ordered W.toCtx⟩ hnp.2 hb₀)
  | @letE _ _ _ _ _ _ _ _ ty' val' hty hval _ _ ihv ihb =>
      intro _ _ _ _ _ W hΔ' hnp hwt
      cases hwt with
      | letE hval₀ty hty₀ hval₀ hb₀ =>
        cases TrExprS.unique hnp.1.toIsUnique hty
          (TrExprS.weakFV_fvwf henv.ordered W hΔ'.fvwf hty₀)
        cases TrExprS.unique hnp.2.1.toIsUnique hval
          (TrExprS.weakFV_fvwf henv.ordered W hΔ'.fvwf hval₀)
        exact .letE hty₀ hval₀ (ihv W hΔ' hnp.2.1.toNoProjBinders hval₀)
          (ihb (W.cons_bvar (.vlet ..))
            ⟨hΔ', nofun, hval₀ty.weakN henv.ordered W.toCtx⟩ hnp.2.2 hb₀)
  | ctor cn us iid cidx hc hlen _ ihargs =>
      intro _ _ _ _ _ W hΔ' hnp hwt
      have ⟨_, hallnp⟩ := noProjBinders_foldl_app hnp
      have ⟨_, hallwt⟩ := trExprS_foldl_app hwt
      refine .ctor cn us iid cidx hc hlen fun i hi => ?_
      obtain ⟨_, hva⟩ := hallwt _ (List.getElem_mem hi)
      exact ihargs i hi W hΔ' (hallnp _ (List.getElem_mem hi)) hva
  | ctor_head cn us iid cidx hc =>
      intro _ _ _ _ _ _ _ _ _; exact .ctor_head cn us iid cidx hc
  | cases con us iid numParams pre hc hpre hnfs _ hlen hnlen harity _ ihd ihalts =>
      intro _ _ _ _ _ W hΔ' hnp hwt
      have ⟨_, hallnp⟩ := noProjBinders_foldl_app hnp
      have ⟨_, hallwt⟩ := trExprS_foldl_app hwt
      obtain ⟨_, hvd⟩ := hallwt _ (.head _)
      refine .cases con us iid numParams pre hc hpre hnfs
        (ihd W hΔ' (hallnp _ (.head _)) hvd) hlen hnlen harity fun j hj => ?_
      obtain ⟨_, hvm⟩ := hallwt _ (.tail _ (List.getElem_mem hj))
      exact ihalts j hj W hΔ' (hallnp _ (.tail _ (List.getElem_mem hj))) hvm
  | fixvar nm us x hfx hctor hcases hfresh =>
      intro _ _ _ _ _ W _ _ _
      exact .fixvar nm us x hfx hctor hcases fun hm => hfresh (W.fvars_suffix.subset hm)
  | const_fix nm us hrec hctor hcases hshift hsubst htobv =>
      intro _ _ _ _ _ _ _ _ _
      exact .const_fix nm us hrec hctor hcases hshift hsubst htobv
  | @fix Δc idx nm tty tb tbi nms srcs defs hidx hnlen hslen hsrc hreg hrarg
      hlift hinst habsl hshift hsubst htobv hbodies _ihb =>
      intro _ _ _ _ _ _ _ _ _
      exact .fix idx hidx hnlen hslen hsrc hreg hrarg hlift hinst habsl hshift hsubst htobv
        hbodies

/--
**Strengthening to the empty context** (the consumable form): an `Erases` derivation
produced at a run's fvar context `Δ` holds at `[]`.

`W : VLCtx.FVLift [] Δ 0 n k` is not a restriction one chooses — it is the only shape
available. `VLCtx.FVLift`'s `cons_bvar` needs a bvar entry on *both* sides, so a derivation
of `FVLift [] Δ dk n k` can only use `refl` and `skip_fvar`; hence `dk = 0`, `k = 0`, and
`Δ.NoBV`. That is exactly the situation the eraser is in: `visitMutual` erases a top-level
constant body under a context of opened fvars, never of bvars.

`hΔ : VLCtx.WF env Us.length Δ` and `henv : env.WF` are consumed in full since slice P2:
the scope predicate is `NoProjBinders`, so the route is
`Erases.strengthen_fvlift_binders`, whose box arm needs the typing half of both. (Before
P2 this lemma ran at `NoProj` and weakened them to `hΔ.fvwf`/`henv.ordered`. Callers are
unaffected — they held the strong forms all along and were throwing them away.)

`hcl`/`hfvf` are *not* premises: `hwt` implies both (`TrExprS.closed`, `TrExprS.fvarsIn`),
which is one of the ways the `hwt`-driven route pays for itself.
-/
theorem erases_strengthen_closed {env : VEnv} (henv : env.WF) {Us : List Name}
    {Γ : ErasureCtx} (hstr : ErasableStrengthen env Us)
    {Δ : VLCtx} {n k : Nat} (W : VLCtx.FVLift [] Δ 0 n k)
    (hΔ : VLCtx.WF env Us.length Δ)
    {e : Expr} {t : LBTerm} {ve : VExpr}
    (hnp : NoProjBinders e) (hwt : TrExprS env Us [] e ve)
    (h : Erases env Us Γ Δ e t) :
    Erases env Us Γ [] e t :=
  h.strengthen_fvlift_binders henv hstr W hΔ hnp hwt

/-! ## The two-sided composition -/

/--
**Context uniformity for a closed, fvar-free constant body whose *binders* are
projection-free** (`NoProjBinders`, since slice P2 — the typeclass layer's own bodies
qualify) — the statement `DeltaHyps.uniform` names, for the fragment the consumers run in.

The route is `Δ → [] → Δ'`: `erases_strengthen_closed` for the first leg,
`erases_weak_any` (`ErasesStrengthen.lean`) for the second.

**Why the second leg is `erases_weak_any` and not `erases_weakFV`.** The consumer is
`RegisteredClosure*.erase` (via `ColdStartDelta.registeredClosureData_step_nonrec`'s `huni`),
and it quantifies over *every* `Δ'` — contexts with bvar entries, and contexts whose fvar
entries shadow each other, included. `erases_weakFV` asks for `Δ'.FVWF` (which shadowing
breaks) and, to start from `[]`, for `Δ'.NoBV` via `VLCtx.FVLift.from_nil` (which bvar
entries break). Neither is available. `erases_weak_any` trades both hypotheses for the data
the recursive-definition setting already carries — `hcl`, `hfvf`, `hlb` — and so covers the
unrestricted `∀ Δ'` the consumer demands. The same asymmetry is why the two legs have
visibly different premise sets: strengthening is `FVLift`-shaped, weakening is not.

`hcl`/`hfvf` are derived from `hwt` rather than assumed; only `hlb : LBClosed t 0` — a fact
about the *target*, which no `TrExprS` premise can see — has to be supplied.
-/
theorem erases_uniform_closed {env : VEnv} (henv : env.WF) {Us : List Name} {Γ : ErasureCtx}
    (hnfv : Γ.fixvars = fun _ => none) (hstr : ErasableStrengthen env Us)
    {Δ : VLCtx} {n k : Nat}
    (W : VLCtx.FVLift [] Δ 0 n k) (hΔ : VLCtx.WF env Us.length Δ)
    {e : Expr} {t : LBTerm} {ve : VExpr}
    (hnp : NoProjBinders e) (hwt : TrExprS env Us [] e ve) (hlb : LBClosed t 0)
    (h : Erases env Us Γ Δ e t) (Δ' : VLCtx) : Erases env Us Γ Δ' e t :=
  erases_weak_any henv.ordered hnfv hwt.closed
    (hwt.fvarsIn.mono fun _ h => (by simp at h : False))
    hlb (erases_strengthen_closed henv hstr W hΔ hnp hwt h) Δ'

/--
**The one-sided corollary, at `Δ = []`** — and it needs **no `ErasableStrengthen` at all**.

This is `erases_weak_any` on the nose, restated under the `uniform` name because it is what
discharges `ColdStartDelta.registeredClosureData_step_nonrec`'s `huni` outright: that
premise is already `∀ {Δ}, Erases env Us Γ [] pe t → Erases env Us Γ Δ pe t`, i.e. the
weakening half alone. Only the *two-sided* transport `erases_uniform_closed` — which must
also come back down from the call site's `Δ`, and which is what replaced the deleted
`DeltaHyps.uniform` field — buys the commissioned obligation.

Recording this separately is the point: it isolates how much of the `uniform` residue was
ever a residue. The `[]`-shaped consumers cost nothing; the `∀ Δ Δ'` one costs
`ErasableStrengthen` plus `NoProjBinders` plus a small-context translation.
-/
theorem erases_uniform_of_nil {env : VEnv} (henv : env.Ordered) {Us : List Name}
    {Γ : ErasureCtx} (hnfv : Γ.fixvars = fun _ => none)
    {e : Expr} {t : LBTerm}
    (hcl : Closed e 0) (hfvf : FVarsIn (fun _ => False) e) (hlb : LBClosed t 0)
    (h : Erases env Us Γ [] e t) (Δ' : VLCtx) : Erases env Us Γ Δ' e t :=
  erases_weak_any henv hnfv hcl hfvf hlb h Δ'

/-! ### Non-vacuity

As in `ErasesStrengthen.lean`: the hypotheses are *constructed*, not assumed, so these also
witness joint satisfiability of the premise set (`FVLift` from `[]` + `VLCtx.WF` + `NoProj`
+ a real `TrExprS` at `[]`). `ErasableStrengthen` is the one thing still taken as a
hypothesis — it is the commissioned obligation — and the `box` arm is not exercised by these
examples, which is exactly why the guard `erasableStrengthen_liftN_zero` is stated above. -/

/-- Non-vacuity (strengthening): a real `lam` derivation, produced at a one-fvar context
`[(some (x, []), .vlam A)]`, transported back to the empty context. The `FVLift` is
`VLCtx.FVLift.from_nil` (the context has no bvar entries — the shape forced by the
statement), the `VLCtx.WF` is a genuine one built from `hA : env.IsType Us.length [] A`, and
the small-context translation is the same `TrExprS.sort` the derivation carries. -/
example (env : VEnv) (henv : env.WF) (Us : List Name) (Γ : ErasureCtx)
    (hstr : ErasableStrengthen env Us)
    (x : FVarId) (A : VExpr) (hA : env.IsType Us.length [] A)
    (name : Name) (bi : BinderInfo)
    (H : Erases env Us Γ [(some (x, []), .vlam A)]
      (.lam name (.sort .zero) (.bvar 0) bi) (.lambda (nameToBinder name) (.bvar 0))) :
    Erases env Us Γ [] (.lam name (.sort .zero) (.bvar 0) bi)
      (.lambda (nameToBinder name) (.bvar 0)) :=
  have hΔ : VLCtx.WF env Us.length [(some (x, []), .vlam A)] :=
    ⟨trivial, by rintro _ _ ⟨⟩; simp, hA⟩
  have hwt : TrExprS env Us [] (.lam name (.sort .zero) (.bvar 0) bi)
      (.lam (.sort .zero) (.bvar 0)) :=
    .lam ⟨_, .sort trivial⟩ (.sort rfl) (.bvar rfl)
  have hnp : NoProjBinders (.lam name (.sort .zero) (.bvar 0) bi) := ⟨trivial, trivial⟩
  erases_strengthen_closed henv hstr (VLCtx.FVLift.from_nil rfl) hΔ hnp hwt H

/-- Non-vacuity (two-sided): the same derivation, moved from the one-fvar context to a
context carrying **both** a bvar entry and a shadowing fvar entry — the shape the
`erases_weakFV` route cannot reach, and the reason the second leg is `erases_weak_any`. -/
example (env : VEnv) (henv : env.WF) (Us : List Name) (Γ : ErasureCtx)
    (hstr : ErasableStrengthen env Us)
    (x : FVarId) (A B : VExpr) (hA : env.IsType Us.length [] A)
    (name : Name) (bi : BinderInfo)
    (H : Erases env Us (Γ.withFixvars fun _ => none) [(some (x, []), .vlam A)]
      (.lam name (.sort .zero) (.bvar 0) bi) (.lambda (nameToBinder name) (.bvar 0))) :
    Erases env Us (Γ.withFixvars fun _ => none)
      [(none, .vlam B), (some (x, []), .vlam A)]
      (.lam name (.sort .zero) (.bvar 0) bi) (.lambda (nameToBinder name) (.bvar 0)) :=
  have hΔ : VLCtx.WF env Us.length [(some (x, []), .vlam A)] :=
    ⟨trivial, by rintro _ _ ⟨⟩; simp, hA⟩
  have hwt : TrExprS env Us [] (.lam name (.sort .zero) (.bvar 0) bi)
      (.lam (.sort .zero) (.bvar 0)) :=
    .lam ⟨_, .sort trivial⟩ (.sort rfl) (.bvar rfl)
  have hnp : NoProjBinders (.lam name (.sort .zero) (.bvar 0) bi) := ⟨trivial, trivial⟩
  have hlb : LBClosed (.lambda (nameToBinder name) (.bvar 0)) 0 := Nat.zero_lt_one
  erases_uniform_closed henv rfl hstr (VLCtx.FVLift.from_nil rfl) hΔ hnp hwt hlb H _

end LeanToLambdaBox
