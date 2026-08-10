import LeanToLambdaBox.Erases
import LeanToLambdaBox.ErasesCorrect

/-!
# A de-partialized, pure erasure core and its refinement of `Erases` (Half B)

This file builds the **implementation refinement bridge**: a *total, pure*
erasure function `eraseCore` that mirrors the branching of the shipping
`Erasure.visitExpr` on the supported fragment, together with a theorem that its
output **refines** the typed erasure relation `Erases`, and an end-to-end
corollary composing the refinement with `erases_correct`.

The shipping `Erasure.erase`/`visitExpr` is `partial def` in a `CoreM`-based monad
`EraseM`, and its relevance decision runs `Meta.isProp`/`Meta.isTypeFormerType` in
`MetaM`. Neither of those is reasoned about directly here. Instead:

* termination is made trivial by **fuel-indexing** (`Nat → …`);
* the monad is replaced by the pure `Except String` monad;
* the `MetaM` relevance oracle is **abstracted as a parameter** `orc : Expr → Bool`;
* the environment queries (`getCtorArity?`/`getCasesInfo?`/kername lookup) are
  replaced by the abstract `ErasureCtx` `Γ` (exactly as the `Erases` relation does).

The honest trust boundary is the predicate `OracleSound` (below): it states that
whenever `orc` fires `true` on a subterm *under the context the function reaches it
in*, that subterm really is irrelevant (`Erasable` over lean4lean's `VExpr` typing).
This is *stated as a hypothesis, not an axiom* — it is exactly the
`Meta.isProp`-↦-lean4lean bridge a full grounding would have to discharge. The
binder-type / constructor-argument translations the `lam`/`letE`/`app`/`ctor` rules
of `Erases` need are **not** a separate hypothesis: they are recovered by inverting
the *source term's own* `TrExprS` derivation, supplied as the premise
`htr : TrExprS env Us Δ e ve` of `eraseCore_refines`. (An earlier version packaged
them as a hypothesis `BinderTrans`, which was unsatisfiable — `TrExprS` has no `.mvar`
rule — and so made the refinement vacuously true; see `binderTrans_style_premise_refutable`
and the non-vacuity guard below.)

## Fragment covered by `eraseCore`

`box | bvar | fvar | const | app | lam | letE | ctor`. Concretely:

* `orc e = true` ⟹ `.box` (the relevance branch of `visitExpr`).
* `.bvar i`/`.fvar x`/`.const n us` map to themselves (`const` via `Γ.constants`,
  unless it is a registered *constructor* head — see below).
* `.app`/`.const` are routed through a spine decomposition mirroring
  `visitApp`/`visitConstApp`:
  - if the head is a `.const cn` with `Γ.ctors cn = some (iid, cidx)`, the whole
    application is a **constructor** spine `args.foldl Expr.app (.const cn us)` and
    erases to `.construct iid cidx args'` (recursing into `args`), matching
    `Erases.ctor`;
  - otherwise it is structural: `.app f a ↦ .app (eraseCore f) (eraseCore a)`,
    `.const n us ↦ .const (Γ.constants n)`, matching `Erases.app`/`Erases.const`.
* `.lam`/`.letE` recurse into the body (and value), matching `Erases.lam`/`letE`.
* everything else (incl. registered `casesOn` heads, `.proj`, `.lit`, `.mdata`,
  `.sort`, `.forallE`, `.mvar`) is `.error` — out of the refined fragment.

**`casesOn` is deliberately excluded** from `eraseCore`: the `Erases.cases` rule
re-wraps each minor function with `mkLambdas` and splits the spine into dropped
`pre` (params/motive/indices) and `discr :: minors`; reproducing that split purely
(it relies on `getCasesInfo?` arities the abstract `Γ` does not carry, e.g.
`discrPos`/`numParams` placement) does not stay clean. The `ctor` case *does* stay
clean and is included. `casesOn` heads route to `.error` rather than to the wrong
`Erases` shape — honest under-approximation.

See the feasibility probe at the bottom for what remains to connect this to the
*actual* `visitExpr`.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-! ## The pure erasure core -/

/-- Erase an application spine `args.foldl Expr.app head` given the erased head
`head'`, by erasing each argument left-to-right and re-applying via `LBTerm.app`.
Pure mirror of `Erasure.visitAppArgs`. -/
def eraseArgs (rec : Expr → Except String LBTerm) :
    LBTerm → List Expr → Except String LBTerm
  | head', [] => .ok head'
  | head', a :: as => do eraseArgs rec (.app head' (← rec a)) as

/-- The pure, total, fuel-indexed erasure core. `orc` is the abstract relevance
oracle (the `MetaM` `isErasable`), `Γ` the abstract erasure context. Returns
`.error` on fuel exhaustion or on any construct outside the supported fragment
(documented above).

`.app`/`.const` are handled by peeling the head off the application spine with an
explicit reverse accumulator `acc` (so the reconstructed source is *literally*
`acc.reverse.foldl Expr.app head` — matching the spine shape of `Erases.ctor`),
exactly mirroring `Erasure.visitApp`/`visitConstApp`. -/
def eraseCore (orc : Expr → Bool) (Γ : ErasureCtx) :
    Nat → Expr → Except String LBTerm
  | 0, _ => .error "out of fuel"
  | fuel + 1, e =>
    if orc e then
      .ok .box
    else
      go orc Γ fuel e []
where
  /-- `go fuel head acc`: erase `acc.foldl Expr.app head`, where `acc` is the argument
  spine peeled off so far (in forward order: `go (.app f a) acc = go f (a :: acc)` and
  `(a :: acc).foldl app f = acc.foldl app (f.app a)`). On a `.const`/applied head we
  decide ctor vs. plain-const; on a `.app f a` we peel `a` and recurse into `f`. -/
  go (orc : Expr → Bool) (Γ : ErasureCtx) (fuel : Nat) : Expr → List Expr → Except String LBTerm
  | .app f a, acc => go orc Γ fuel f (a :: acc)
  | .const cn _us, acc =>
    match Γ.casesOns cn with
    | some _ => .error "casesOn not modelled by eraseCore"
    | none =>
      match Γ.ctors cn with
      | some (iid, cidx) =>
        ((acc.mapM (fun a => eraseCore orc Γ fuel a)).map
          (fun args' => .construct iid cidx args'))
      | none =>
        eraseArgs (fun a => eraseCore orc Γ fuel a) (.const (Γ.constants cn)) acc
  | head, acc =>
    -- Non-const, non-app head: only valid with an empty spine.
    match acc with
    | _ :: _ => .error "non-const applied head"
    | [] =>
      match head with
      | .bvar i => .ok (.bvar i)
      | .fvar x => .ok (.fvar x)
      | .lam nm _ty b _bi =>
          (eraseCore orc Γ fuel b).map (fun b' => .lambda (nameToBinder nm) b')
      | .letE nm _ty v b _nd => do
          let v' ← eraseCore orc Γ fuel v
          let b' ← eraseCore orc Γ fuel b
          .ok (.letIn (nameToBinder nm) v' b')
      | _ => .error "unsupported construct"

/-! ## The oracle-soundness hypothesis (the trust boundary) -/

/--
**Oracle soundness — the relevance-decision correctness obligation.**

`OracleSound env Us orc` says: for *every* well-typed subterm `e'` (one that
translates to a `VExpr` `ve`, `TrExprS … Δ' e' ve`), if the oracle fires
(`orc e' = true`) then `ve` really is irrelevant (`Erasable`). This is precisely
what makes the `box` rule of `Erases` applicable wherever `eraseCore` emits `.box`.

Following the collaborators' guidance, the lean4lean typing judgment is **assumed**
(`TrExprS` is a premise) rather than produced by the oracle: the oracle's only job is
to *decide* relevance on already-well-typed terms. This is what makes `OracleSound`
*dischargeable* — by a relevance check reimplemented on lean4lean's verified checker
(`isProp ∨ isArity` on the inferred type), whose soundness against `Erasable` is a
theorem, not an axiom (see `isProp_refines_Erasable`/`isErasable_sound` — WIP). The
real `Meta.isProp ∘ inferType` / `Meta.isTypeFormerType ∘ inferType` is the shipping
instance of exactly this obligation.
-/
def OracleSound (env : VEnv) (Us : List Name) (orc : Expr → Bool) : Prop :=
  ∀ (Δ' : VLCtx) (e' : Expr) (ve : VExpr),
    TrExprS env Us Δ' e' ve → orc e' = true → Erasable env Us.length Δ'.toCtx ve

/-! ## Application-spine translation inversion

The spine helper `go` reconstructs a source `acc.foldl Expr.app head`. To supply
the per-argument `TrExprS` facts that `Erases.app`/`Erases.ctor` need, we invert
the *source term's own* translation through the spine: a translation of a
const-headed (or any-headed) application spine yields a translation of the head and
of every argument. This is the satisfiable replacement for the (vacuous) former
`BinderTrans` hypothesis — every fact comes from the input's `TrExprS` derivation,
which exists precisely because the input is well-typed. -/

/-- Translating an application spine `acc.foldl Expr.app head` yields a translation
of `head` and, pointwise, of every argument in `acc`. Inversion is by induction on
`acc`, peeling the outermost `TrExprS.app` at each step. -/
theorem trExprS_appSpine_inv {env : VEnv} {Us : List Name} {Δ : VLCtx} :
    ∀ (acc : List Expr) (head : Expr) (ve : VExpr),
      TrExprS env Us Δ (acc.foldl Expr.app head) ve →
      (∃ hve, TrExprS env Us Δ head hve) ∧
      (∀ i (h : i < acc.length), ∃ ave, TrExprS env Us Δ acc[i] ave) := by
  intro acc
  induction acc with
  | nil => intro head ve htr; exact ⟨⟨ve, htr⟩, fun i h => absurd h (by simp)⟩
  | cons a as ih =>
      intro head ve htr
      simp only [List.foldl_cons] at htr
      obtain ⟨⟨hve, htrapp⟩, hpt⟩ := ih (head.app a) ve htr
      cases htrapp with
      | @app f' A B a'' _Δ _f _a _hTf _hTa htrf htra =>
          refine ⟨⟨f', htrf⟩, fun i h => ?_⟩
          cases i with
          | zero => exact ⟨a'', htra⟩
          | succ j => exact hpt j (by simpa using h)

/-! ## Spine-combinator refinement helpers -/

/-- Helper: refinement for an application spine. If the erased head `head'` already
refines `head` under `Δ`, and the per-argument refinement IH holds, then erasing the
spine via `eraseArgs` refines the source spine `args.foldl Expr.app head`. -/
theorem eraseArgs_refines {env : VEnv} {Us : List Name} {Γ : ErasureCtx} {Δ : VLCtx}
    {rec : Expr → Except String LBTerm}
    (hrec : ∀ a (ave : VExpr) t, TrExprS env Us Δ a ave → rec a = .ok t → Erases env Us Γ Δ a t) :
    ∀ (args : List Expr) (head : Expr) (head' : LBTerm) (t : LBTerm),
      (∀ i (h : i < args.length), ∃ ave, TrExprS env Us Δ args[i] ave) →
      Erases env Us Γ Δ head head' →
      eraseArgs rec head' args = .ok t →
      Erases env Us Γ Δ (args.foldl Expr.app head) t := by
  intro args
  induction args with
  | nil => intro head head' t _htrs hhead heq; simp only [eraseArgs] at heq; cases heq; exact hhead
  | cons a as ih =>
      intro head head' t htrs hhead heq
      simp only [eraseArgs] at heq
      obtain ⟨ave, htra⟩ := htrs 0 (by simp)
      cases ha' : rec a with
      | error e => rw [ha'] at heq; simp [bind, Except.bind] at heq
      | ok a' =>
          rw [ha'] at heq
          refine ih (head.app a) (.app head' a') t
            (fun i h => by
              have := htrs (i + 1) (by simpa using h)
              rwa [List.getElem_cons_succ] at this)
            (.app hhead (hrec a ave a' (by simpa using htra) ha')) heq

/-- `mapM` of the per-element erasure over a list yields, on success, a result list
of the same length whose entries pointwise refine the source list. The combinatorial
core of the `ctor` case (constructor args translated independently). -/
theorem mapM_refines {env : VEnv} {Us : List Name} {Γ : ErasureCtx} {Δ : VLCtx}
    {rec : Expr → Except String LBTerm}
    (hrec : ∀ a (ave : VExpr) t, TrExprS env Us Δ a ave → rec a = .ok t → Erases env Us Γ Δ a t) :
    ∀ (args : List Expr) (args' : List LBTerm),
      (∀ i (h : i < args.length), ∃ ave, TrExprS env Us Δ args[i] ave) →
      args.mapM rec = .ok args' →
      ∃ (hlen : args.length = args'.length),
      ∀ i (h : i < args.length), Erases env Us Γ Δ args[i] (args'[i]'(hlen ▸ h)) := by
  intro args
  induction args with
  | nil =>
      intro args' _htrs heq
      simp only [List.mapM_nil, pure, Except.pure] at heq
      cases heq
      exact ⟨rfl, fun i h => absurd h (by simp)⟩
  | cons a as ih =>
      intro args' htrs heq
      rw [List.mapM_cons] at heq
      obtain ⟨ave, htra⟩ := htrs 0 (by simp)
      cases ha' : rec a with
      | error e => rw [ha'] at heq; simp [bind, Except.bind] at heq
      | ok a' =>
          rw [ha'] at heq
          simp only [bind, Except.bind] at heq
          cases has' : as.mapM rec with
          | error e => rw [has'] at heq; simp at heq
          | ok as' =>
              rw [has'] at heq
              simp only [pure, Except.pure] at heq
              cases heq
              obtain ⟨hlen, hpt⟩ := ih as'
                (fun i h => by
                  have := htrs (i + 1) (by simpa using h)
                  rwa [List.getElem_cons_succ] at this)
                has'
              refine ⟨by simp [hlen], fun i h => ?_⟩
              cases i with
              | zero => simpa using hrec a ave a' (by simpa using htra) ha'
              | succ j =>
                  have hj : j < as.length := by simpa using h
                  simpa using hpt j hj

/-! ## Refinement of the spine helper `go` -/

/-- **Refinement of `go`.** Under the fuel-`IH` `hrec` (which says the recursive
`eraseCore orc Γ fuel` already refines `Erases` *in every context*, **given** a
translation `TrExprS` of the subterm), the spine helper `go` refines `Erases` at the
reconstructed source `acc.foldl Expr.app head`, **given** a translation `htr` of that
whole source term.

The proof is by structural induction on `head` (matching `go`'s recursion: the
`.app` case peels an argument into `acc`, using `(a :: acc).foldl = acc.foldl ∘
(·.app a)` — the source, hence its translation `htr`, is unchanged); the `const`-head
ctor/plain cases invert `htr` through the spine (`trExprS_appSpine_inv`) to feed the
per-argument translations into `mapM_refines`/`eraseArgs_refines`; the binder cases
invert `htr` (via `TrExprS.lam`/`TrExprS.letE`) to obtain both the binder-type
translation that `Erases.lam`/`letE` need *and* the body translation threaded into
`hrec`. This replaces the former (vacuous) `BinderTrans` hypothesis: every translation
fact now comes from the input term's own `TrExprS` derivation. Note `go` itself never
sees the oracle — the `box` decision is made by `eraseCore` *before* calling `go`, so
`OracleSound` is consumed only in `eraseCore_refines`. -/
theorem go_refines {env : VEnv} {Us : List Name} {Γ : ErasureCtx}
    {orc : Expr → Bool} {fuel : Nat}
    (hrec : ∀ (Δ : VLCtx) (e : Expr) (ve : VExpr) (t : LBTerm),
              TrExprS env Us Δ e ve →
              eraseCore orc Γ fuel e = .ok t → Erases env Us Γ Δ e t) :
    ∀ (head : Expr) (Δ : VLCtx) (acc : List Expr) (ve : VExpr) (t : LBTerm),
      TrExprS env Us Δ (acc.foldl Expr.app head) ve →
      eraseCore.go orc Γ fuel head acc = .ok t →
      Erases env Us Γ Δ (acc.foldl Expr.app head) t := by
  intro head
  induction head with
  | app f a ihf _iha =>
      intro Δ acc ve t htr heq
      rw [eraseCore.go] at heq
      have htr' : TrExprS env Us Δ ((a :: acc).foldl Expr.app f) ve := by simpa using htr
      have := ihf Δ (a :: acc) ve t htr' heq
      simpa using this
  | const cn us =>
      intro Δ acc ve t htr heq
      obtain ⟨_, hptr⟩ := trExprS_appSpine_inv acc (.const cn us) ve htr
      rw [eraseCore.go] at heq
      split at heq
      · simp at heq
      · split at heq
        · rename_i iid cidx hctor
          simp only [Except.map] at heq
          split at heq
          · simp at heq
          · rename_i args' hmap
            injection heq with heq; subst heq
            obtain ⟨hlen, hpt⟩ := mapM_refines (Δ := Δ)
              (fun a ave ta htra hta => hrec Δ a ave ta htra hta)
              acc args' hptr hmap
            exact .ctor cn us iid cidx hctor hlen hpt
        · exact eraseArgs_refines (Δ := Δ)
            (fun a ave ta htra hta => hrec Δ a ave ta htra hta)
            acc (.const cn us) (.const (Γ.constants cn)) t
            hptr (.const cn us _ rfl (by assumption) (by assumption)) heq
  | fvar x =>
      intro Δ acc ve t htr heq
      cases acc with
      | cons a as => simp only [eraseCore.go] at heq; exact absurd heq (by simp)
      | nil => rw [eraseCore.go] at heq; injection heq with heq; subst heq; exact .fvar x
  | bvar i =>
      intro Δ acc ve t htr heq
      cases acc with
      | cons a as => simp only [eraseCore.go] at heq; exact absurd heq (by simp)
      | nil => rw [eraseCore.go] at heq; injection heq with heq; subst heq; exact .bvar i
  | lam nm ty b bi ihty ihb =>
      intro Δ acc ve t htr heq
      cases acc with
      | cons a as => simp only [eraseCore.go] at heq; exact absurd heq (by simp)
      | nil =>
          simp only [List.foldl_nil] at htr
          cases htr with
          | @lam ty' _Δ _ty _body body' _name _bi _hty htyTr htrb =>
            rw [eraseCore.go] at heq
            simp only [Except.map] at heq
            split at heq
            · simp at heq
            · rename_i b' hb'
              injection heq with heq; subst heq
              exact .lam htyTr (hrec ((none, .vlam ty') :: Δ) b body' b' htrb hb')
  | letE nm ty v b nd ihty ihv ihb =>
      intro Δ acc ve t htr heq
      cases acc with
      | cons a as => simp only [eraseCore.go] at heq; exact absurd heq (by simp)
      | nil =>
          simp only [List.foldl_nil] at htr
          cases htr with
          | @letE val' ty' _Δ _ty _val _body _body' _name _nd _hTval htyTr hvalTr htrb =>
            rw [eraseCore.go] at heq
            cases hv' : eraseCore orc Γ fuel v with
            | error e => rw [hv'] at heq; exact absurd heq (by simp [bind, Except.bind])
            | ok v' =>
                rw [hv'] at heq
                cases hb' : eraseCore orc Γ fuel b with
                | error e => rw [hb'] at heq; exact absurd heq (by simp [bind, Except.bind])
                | ok b' =>
                    rw [hb'] at heq
                    simp only [bind, Except.bind] at heq
                    injection heq with heq; subst heq
                    exact .letE htyTr hvalTr (hrec Δ v val' v' hvalTr hv')
                      (hrec ((none, .vlet ty' val') :: Δ) b ve b' htrb hb')
  | sort u =>
      intro Δ acc ve t htr heq
      cases acc <;> (simp only [eraseCore.go] at heq; exact absurd heq (by simp))
  | mvar x =>
      intro Δ acc ve t htr heq
      cases acc <;> (simp only [eraseCore.go] at heq; exact absurd heq (by simp))
  | forallE nm ty b bi =>
      intro Δ acc ve t htr heq
      cases acc <;> (simp only [eraseCore.go] at heq; exact absurd heq (by simp))
  | lit l =>
      intro Δ acc ve t htr heq
      cases acc <;> (simp only [eraseCore.go] at heq; exact absurd heq (by simp))
  | mdata m e =>
      intro Δ acc ve t htr heq
      cases acc <;> (simp only [eraseCore.go] at heq; exact absurd heq (by simp))
  | proj s i e =>
      intro Δ acc ve t htr heq
      cases acc <;> (simp only [eraseCore.go] at heq; exact absurd heq (by simp))

/-! ## The refinement theorem -/

/--
**`eraseCore` refines `Erases`.** Under the (satisfiable) trust-boundary hypothesis
`OracleSound` and **given a lean4lean translation of the source** (`htr : TrExprS env
Us Δ e ve`), whenever the pure core succeeds (`eraseCore orc Γ fuel e = .ok t`) the
typed erasure relation holds: the source `Lean.Expr` `e` erases to the target `LBTerm`
`t` (`Erases env Us Γ Δ e t`).

The proof is by induction on `fuel` (generalizing over `Δ`, `e`, `ve`, `t` and the
translation `htr`): the `0` case is vacuous (the core errors); the `fuel + 1` case
splits on the oracle. If `orc e = true`, `OracleSound` produces the `box` witness
(`TrExprS` + `Erasable`) and we apply `Erases.box`. Otherwise the result is
`go orc Γ fuel e []`, and `go_refines` finishes it — fed `htr` for `e` (`[].foldl =
e`) and the fuel-IH as its `hrec` (recursive calls erase with `eraseCore orc Γ fuel`,
each supplied the translation of *their* subterm, which `go_refines` extracts from the
spine/binder inversion of `htr`).

Replacing the former `BinderTrans` hypothesis by `htr` is what makes this theorem
**non-vacuous**: `BinderTrans` was refutable (`TrExprS` has no `.mvar` rule, so it
asserted a translation of `.mvar _`, i.e. `False`), whereas `htr` is satisfiable for
every well-typed source — see `eraseCore_refines_nonvacuous` below. -/
theorem eraseCore_refines {env : VEnv} {Us : List Name} {Γ : ErasureCtx}
    {orc : Expr → Bool} (hos : OracleSound env Us orc)
    {Δ : VLCtx} {e : Expr} {ve : VExpr} {t : LBTerm}
    (htr : TrExprS env Us Δ e ve) {fuel : Nat} :
      eraseCore orc Γ fuel e = .ok t → Erases env Us Γ Δ e t := by
  induction fuel generalizing Δ e ve t with
  | zero => intro heq; simp only [eraseCore] at heq; exact absurd heq (by simp)
  | succ fuel ih =>
      intro heq
      rw [eraseCore] at heq
      split at heq
      · -- oracle fired: box.
        rename_i horc
        injection heq with heq; subst heq
        -- The source's own translation `htr` supplies `TrExprS`; the oracle
        -- (assumed sound) supplies `Erasable`.
        exact .box htr (hos Δ e ve htr horc)
      · -- structural: hand off to `go_refines` with the fuel-IH.
        exact go_refines (fun Δ' e' ve' t' htr' h => ih htr' h) e Δ [] ve t htr heq

/-! ## End-to-end semantic correctness of the pure core -/

/--
**The de-partialized pure erasure is semantically correct (β + δ).**

Composes `eraseCore_refines` with the already-proven forward simulation
`erases_correct`: if the pure core erases the source `e` to `t`
(`eraseCore orc Γ fuel e = .ok t`) under the trust-boundary hypothesis `OracleSound`
and given a translation `htr : TrExprS env Us Δ e ve` of the source, and — with the
well-formedness/consistency premises of `erases_correct` — the source
`SEvalβδ`-evaluates to a value `v`, then the target `t` `Eval`-uates to some `t'` that
erases `v` (and `v` translates to some `vve`).

This is the end-to-end statement "the de-partialized pure erasure, *as specified*,
is semantically correct." The shape of the conclusion is exactly that of
`erases_correct`; the only new ingredient is that the `Erases` premise is now
*produced by the explicit pure function* `eraseCore` rather than assumed. The source
translation `htr` (already a premise of `erases_correct`) now also feeds
`eraseCore_refines`, which is what dispels the former vacuity. -/
theorem eraseCore_correct {env : VEnv} (henv : env.WF) {Us : List Name} {Δ : VLCtx}
    (hΔ : VLCtx.WF env Us.length Δ) {Γ : ErasureCtx} {Esrc : SEnv}
    {E : GlobalDeclarations}
    (hcon : SEnvConsistent env Us Esrc)
    (hdelta : ErasesEnvDelta env Us Γ Esrc E)
    (hnfenv : NoFixEnv E)
    {orc : Expr → Bool} (hos : OracleSound env Us orc)
    {fuel : Nat} {e v : Expr} {ve : VExpr} {t : LBTerm}
    (htr : TrExprS env Us Δ e ve)
    (herase : eraseCore orc Γ fuel e = .ok t)
    (hnfx : NoFix t)
    (hev : SEvalβδ Esrc e v) :
    ∃ t' vve, Eval E t t' ∧ TrExprS env Us Δ v vve ∧ Erases env Us Γ Δ v t' := by
  obtain ⟨t', vve, h1, h2, h3, _⟩ :=
    erases_correct henv hΔ hcon hdelta hnfenv htr
      (eraseCore_refines hos htr herase) hnfx hev
  exact ⟨t', vve, h1, h2, h3⟩

/-! ## Non-vacuity guard

The former `BinderTrans` hypothesis was **refutable**: `TrExprS` has no `.mvar` rule,
so `∀ Δ' ty, ∃ ty', TrExprS env Us Δ' ty ty'` instantiated at `ty := .mvar _` asserts a
translation that cannot exist. Hence the old `eraseCore_refines`/`eraseCore_correct`
were vacuously true. The checks below positively demonstrate that the **new** premise
set (`htr : TrExprS …` together with `OracleSound … (fun _ => false)`) is *jointly
satisfiable*, so the repaired theorems are non-vacuous. -/

/-- `OracleSound` for the always-`false` oracle holds for *any* `env`/`Us`: the
hypothesis `(fun _ => false) e' = true` is `false = true`, i.e. `False`. -/
theorem oracleSound_false (env : VEnv) (Us : List Name) :
    OracleSound env Us (fun _ => false) := by
  intro Δ' e' ve _ h; exact absurd h (by simp)

/-- A concrete, satisfiable `TrExprS` witness: `Sort 0` translates (no environment,
no universe params, empty context). This is exactly the kind of source `htr` the new
`eraseCore_refines` consumes — and it exists, unlike the impossible `.mvar` that
refuted `BinderTrans`. -/
theorem trExprS_sort_witness (env : VEnv) :
    TrExprS env [] [] (.sort .zero) (.sort .zero) :=
  .sort rfl

/-- **Joint satisfiability of the repaired hypothesis set.** There exist concrete
`env, Us, Δ, e, ve, orc` with both `TrExprS env Us Δ e ve` and `OracleSound env Us orc`
holding simultaneously (here `e = Sort 0`, `orc = fun _ => false`). Since the
hypotheses can be jointly met, `eraseCore_refines` is **not** vacuously true. -/
theorem eraseCore_refines_hyps_satisfiable :
    ∃ (env : VEnv) (Us : List Name) (Δ : VLCtx) (e : Expr) (ve : VExpr)
      (orc : Expr → Bool),
      TrExprS env Us Δ e ve ∧ OracleSound env Us orc :=
  ⟨.empty, [], [], .sort .zero, .sort .zero, (fun _ => false),
    trExprS_sort_witness .empty, oracleSound_false .empty []⟩

/-- Concrete confirmation that, with the satisfiable hypotheses in scope,
`eraseCore_refines` actually *fires* and produces a real `Erases` derivation (it is
not merely non-refutable in the abstract — it delivers content). With `orc` never
firing and one unit of fuel, `eraseCore` on `Sort 0` errors (`Sort` is outside the
fragment), so the refinement is witnessed on a term it *does* accept: a free
variable. `.fvar x` translates whenever the context resolves it, and erases to
`.fvar x`. -/
theorem eraseCore_refines_fires
    (env : VEnv) (Γ : ErasureCtx) (x : FVarId)
    {Δ : VLCtx} {ve : VExpr} (htr : TrExprS env [] Δ (.fvar x) ve) :
    Erases env [] Γ Δ (.fvar x) (.fvar x) :=
  eraseCore_refines (Γ := Γ) (oracleSound_false env []) htr (fuel := 1)
    (by simp [eraseCore, eraseCore.go])

/-! ## Feasibility probe — what remains to connect `eraseCore` to the *real* `visitExpr`

This documents, concretely and honestly, the gap between the verified `eraseCore`
above and the shipping `Erasure.erase`/`visitExpr`. Three independent obligations
remain; none is discharged here (and the first is *unprovable* inside Lean).

### (a) The `MetaM` relevance oracle must satisfy `OracleSound`.

`eraseCore` abstracts the relevance decision as a parameter `orc : Expr → Bool` with
the hypothesis `OracleSound`. The real `visitExpr` instantiates it with
`Erasure.isErasable := Meta.isProp (inferType e) ∨ Meta.isTypeFormerType (inferType e)`,
running in `MetaM`. To *discharge* `OracleSound` one would need:
`isErasable e = true → ∃ ve, TrExprS env Us Δ e ve ∧ Erasable env Us.length Δ.toCtx ve`.

* This is **not provable in Lean**: `Meta.isProp`/`inferType` are `MetaM` programs
  over Lean's *real* elaborator environment; there is no Lean-internal theorem
  relating their `Bool`/`Expr` output to lean4lean's `HasType` judgment. The honest
  options are exactly two:
  1. **Axiomatize** the bridge (an `axiom isErasable_sound : …`). This is the
     standard MetaCoq-style "trusted relevance oracle" assumption, but it is a *new
     axiom* — forbidden by this project's rules, so we keep `OracleSound` as a
     *stated hypothesis* (strictly weaker, and assumption-tracking: every use shows
     up in the theorem statement, not in `#print axioms`).
  2. **Route through lean4lean's pure `inferType`**: replace `Meta.inferType` by
     lean4lean's verified `TypeChecker.inferType` (which *does* have a soundness
     theorem against `HasType`), then prove `isProp`/`isArity` checks on its output
     refine `Erasable`. This needs (i) a `MetaM`↔lean4lean `inferType` agreement
     lemma and (ii) closing lean4lean's own `inferType.WF` (which still has
     `sorry`s in the pinned snapshot — see memory `lean4lean-sorry-boundary`). So it
     is *in principle* mechanizable but rests on currently-open lean4lean metatheory.

The binder-type / argument translations are *not* a separate trust obligation: they
are extracted by inverting the source term's own `TrExprS` premise `htr` (which holds
because `visitExpr` runs only on well-typed input, every subterm of which — binder
annotations included — has a `TrExprS` witness by lean4lean's translation totality on
well-typed terms). An earlier draft instead assumed them as a hypothesis `BinderTrans`,
but that predicate was *unsatisfiable* (`TrExprS` has no `.mvar` rule), making the
refinement vacuous; it has been removed in favour of inverting `htr`.

### (b) `visitExpr` is `partial def` in `CoreM`-based `EraseM` — is `partial_fixpoint` viable?

`eraseCore` sidesteps partiality by fuel-indexing. To instead reason about the
*actual* `visitExpr`, one would want equational lemmas for a `partial def`. I tested
`partial_fixpoint` empirically (Lean v4.29.0):

* On a **non-`partial` `def`** with self-recursion in `Except String`: `partial_fixpoint`
  succeeds and yields `…​.eq_def`. ✓
* On a **non-`partial` `def`** in `CoreM` (the actual `EraseM` base monad):
  `partial_fixpoint` **succeeds** and yields `…​.eq_def`. ✓  (CoreM admits the
  required monadic order/CCPO instance.)
* On **mutual** `def`s in `CoreM` (the shape of `visitExpr`/`visitApp`/`visitConstApp`/
  `visitAppArgs`): `partial_fixpoint` (one clause per function inside the `mutual`
  block) **succeeds** and yields per-function `…​.eq_def`. ✓
* On **higher-order monadic-combinator** recursion `args.foldlM (… visitC …) 0` in
  `CoreM` (exactly `visitAppArgs`): `partial_fixpoint` **succeeds**. ✓
* BUT: a function *already declared* `partial def` keeps its opaque partial
  semantics; `partial_fixpoint` on it is reported "unused, function is partial" and
  produces **no** equational lemmas.

**Conclusion:** `partial_fixpoint` is plausibly viable for the `visitExpr` family in
`CoreM` — but only if those defs are *re-declared without `partial`* (replacing
`partial` by a `partial_fixpoint` clause). Since `Erasure.lean` is read-only here,
that re-declaration is the concrete next step; it is mechanically promising (no monad
or higher-order-combinator obstruction was found empirically) rather than blocked.

### (c) Features `eraseCore` does not model.

* **de Bruijn (`VLCtx`) ↔ fvar (telescope) reconciliation.** `Erases`/`eraseCore`
  are locally-nameless over `bvar`/`fvar`, whereas `visitLambda`/`visitLet` use
  `lambdaMonocular`/`letMonocular` to open binders into *fresh `fvar`s*, recurse on
  the `fvar`-body, then `abstract`/`toBvar` back. Connecting the two requires a
  telescope-opening ↔ `VLCtx`-extension simulation lemma (the `fvar` introduced for a
  binder corresponds to the de Bruijn slot `eraseCore` recurses under). This is real
  bookkeeping work, untouched here.
* **`casesOn`.** Excluded from `eraseCore` (routes to `.error`): the `Erases.cases`
  shape needs the `getCasesInfo?` arity data (`discrPos`, param/motive/index counts,
  per-minor field arities) that the abstract `Γ` does not carry, plus the `mkLambdas`
  re-wrapping of minors. Modelling it purely is feasible but did not stay clean, so
  it is honestly under-approximated.
* **`prepare_erasure`** (the pre-pass run before `visitExpr`), **`@[csimp]`/`@[extern]`
  rewrites**, **machine-`Nat`/`Int` lowering** (`config.nat = .machine`, `.prim`
  literals, `Nat.succ`↦`+1`), **projections** (`.proj`, blocked by lean4lean's
  sorried `TrProj`), and **string literals** are all out of scope — `eraseCore`
  errors on them. These are exactly the "additional, unverified rewrites layered on
  top" — deliberately out of the verified subset.

In short: the refinement bridge is *complete and sorry-free for the supported
fragment*, and the remaining gap is precisely (a) one honest, Lean-unprovable oracle
assumption (kept as a hypothesis, not an axiom), (b) a re-declaration of `visitExpr`
as a `partial_fixpoint` def (empirically viable in `CoreM`), and (c) the
fvar↔de-Bruijn telescope simulation plus the deliberately-unmodelled rewrite passes.

### (d) 2026-07-07 addendum: `eraseCore` CANNOT be the bridge target (adversarially verified)

Obstacle (c) is worse than "real bookkeeping work": **no** instantiation of
`orc : Expr → Bool` makes `visitExpr` refine *this de-Bruijn* `eraseCore`.
Oracle-independent counterexample: with `g : Nat → True → Nat` and
`f : (Nat → True → Nat) → (True → Nat → Nat) → Nat`, the closed, fragment-internal
term `f (fun (n : Nat) (h : True) => g n h) (fun (h : True) (n : Nat) => g n h)`
has the de-Bruijn lambda bodies `g #1 #0` and `g #0 #1`. `visitExpr` opens all four
binders and its oracle (running in the ambient lctx) boxes exactly the proof-typed
occurrences — *different* bvar indices in the two lambdas — while `eraseCore`
queries `orc` on the raw de-Bruijn leaves and must treat the syntactically identical
`.bvar i` identically in both. So the outputs differ at ≥ 2 positions for **every**
`orc`: a function of the bare `Expr` cannot disambiguate occurrences of the same
bvar under different binder types. (Verified by a 4-lens adversarial review,
2026-07-07.)

Consequently the plan of record routes the bridge **directly to `Erases`** (which
threads the `VLCtx` and whose `box` rule consumes the typing judgment at the exact
fvar-opened context the shipping oracle decides): `visitExpr` —(fixpoint induction
over the now-`partial_fixpoint` family)→ `Erases` —(`erases_correct`)→ `Eval`, using
`Erases.abstract`/`Erases.uninstantiate` (`ErasesAbstract.lean`) at the binder cases.
`eraseCore` and the theorems in this file remain valid and are **re-scoped as the
pure specification model** (and the non-vacuity anchor for `Erases`); they are no
longer claimed as the stepping stone to the shipping function.
-/

/-- **Refutability of the deleted `BinderTrans`-style premise** (recorded as a proof
to document *why* the old theorems were vacuous). The premise asserted a `TrExprS`
translation of *every* `Expr` in every context; instantiated at the metavariable
`.mvar _` — for which `TrExprS` has no constructor — it yields `False`. Contrast with
`eraseCore_refines_hyps_satisfiable`: the *new* premise set is satisfiable, so no such
refutation exists for it (a `… : False` from `htr`/`OracleSound` leaves an unsolvable
`⊢ False`, verified out-of-band). -/
theorem binderTrans_style_premise_refutable {env : VEnv} {Us : List Name}
    (h : ∀ (Δ' : VLCtx) (ty : Expr), ∃ ty', TrExprS env Us Δ' ty ty') : False := by
  obtain ⟨_, htr⟩ := h [] (.mvar ⟨`x⟩); cases htr

end LeanToLambdaBox
