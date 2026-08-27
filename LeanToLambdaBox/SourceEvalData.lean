import LeanToLambdaBox.SourceEval
import LeanToLambdaBox.SubjectReduction

/-!
# Source-side evaluation with saturated constructor data (step A4)

`SEvalData Γ E` is the source big-step weak call-by-value evaluation for the **data
fragment**: the β + ζ + δ core (as in `SEvalβζδ`) plus a *saturated* constructor-value
rule `ctor_val` that carries the arity bound `args.length ≤ ar` in the eval node,
where `ar = Γ.ctorArities cn` is the constructor's declared arity. This is the source
relation over which `erases_correct_data` (the forward simulation at MetaRocq's
non-block `appliedFlags`) is proved.

Two design points:

* **The saturation bound lives here, on the source.** MetaRocq's `iota`/`proj`
  evaluation rules carry a `#args = pars + cstr_nargs` premise; the P0 `Semantics/`
  model deliberately does *not* replicate that on the target `WcbvEval` — instead the
  bound rides on the source `ctor_val` node (`hsat : args.length ≤ ar`), which is the
  right place for it (the source is where saturation is a real, checkable fact about
  the program).
* **It is a conservative extension of `SEvalβζδ`.** The forgetful map
  `SEvalData.toβζδ` drops the registration/arity data, so the β+ζ+δ subject reduction
  `SEvalβζδ_defeq` applies verbatim (via `toβζδ`) to any `SEvalData` evaluation — no
  new metatheory of `SEvalβζδ` is touched.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-- Weak call-by-value big-step evaluation of source `Expr`, the **data fragment**:
β + ζ + δ (as `SEvalβζδ`) plus a *saturated* `ctor_val` whose arity bound
`args.length ≤ ar` is recorded in the eval node (with `ar = Γ.ctorArities cn`).

The constructor spine encoding mirrors the `Erases` `ctor`/`ctor_head` rules exactly
(`args.foldl Expr.app (.const cn us)`), so values line up with the erasure relation. -/
inductive SEvalData (Γ : ErasureCtx) (E : SEnv) : Expr → Expr → Prop
  /-- λ-abstractions are values. -/
  | lam (n : Name) (ty b : Expr) (bi : BinderInfo) :
      SEvalData Γ E (.lam n ty b bi) (.lam n ty b bi)
  /-- β: function evaluates to a λ, argument to a value, then the substituted body. -/
  | beta {f a : Expr} {n : Name} {ty b : Expr} {bi : BinderInfo} {av r : Expr} :
      SEvalData Γ E f (.lam n ty b bi) → SEvalData Γ E a av →
      SEvalData Γ E (b.instantiate1' av 0) r →
      SEvalData Γ E (.app f a) r
  /-- ζ: let-binding evaluates the bound value then the substituted body. -/
  | zeta {n : Name} {ty v b : Expr} {nd : Bool} {vv r : Expr} :
      SEvalData Γ E v vv → SEvalData Γ E (b.instantiate1' vv 0) r →
      SEvalData Γ E (.letE n ty v b nd) r
  /-- δ: unfold a defined constant and evaluate its body. -/
  | delta {n : Name} {us : List Level} {body r : Expr} :
      E n = some body → SEvalData Γ E body r → SEvalData Γ E (.const n us) r
  /-- A **saturated** constructor application is a value; evaluate its arguments. The
      head `cn` is a registered constructor (`Γ.ctors cn = some (iid, cidx)`) with
      declared arity `ar` (`Γ.ctorArities cn = some ar`), and the number of supplied
      arguments does not exceed it (`args.length ≤ ar`). -/
  | ctor_val {cn : Name} {us : List Level} {iid : InductiveId} {cidx ar : Nat}
      {args vs : List Expr}
      (hc : Γ.ctors cn = some (iid, cidx))
      (har : Γ.ctorArities cn = some ar)
      (hsat : args.length ≤ ar)
      (hl : args.length = vs.length)
      (hargs : ∀ i (h : i < args.length), SEvalData Γ E args[i] (vs[i]'(hl ▸ h))) :
      SEvalData Γ E (args.foldl Expr.app (.const cn us))
        (vs.foldl Expr.app (.const cn us))
  /-- A **literal** evaluates by unfolding to its constructor form (see
      `SEvalβζδ.lit`). Under peano the reduct is the `Nat` tower, already a value of
      `ctor_val` and already a `FirstOrderValue`. -/
  | lit {l : Literal} {r : Expr} :
      SEvalData Γ E l.toConstructor r → SEvalData Γ E (.lit l) r

/-- **Forgetful map to the β+ζ+δ fragment.** Every `SEvalData` evaluation is an
`SEvalβζδ` evaluation (dropping the registration/arity data on `ctor_val`). This lets
the data-fragment simulation reuse the β+ζ+δ subject reduction `SEvalβζδ_defeq`
verbatim — `SEvalβζδ` and its committed metatheory are left untouched. -/
theorem SEvalData.toβζδ {Γ : ErasureCtx} {E : SEnv} {e v : Expr}
    (h : SEvalData Γ E e v) : SEvalβζδ E e v := by
  induction h with
  | lam n ty b bi => exact .lam n ty b bi
  | beta _ _ _ ihf iha ihb => exact .beta ihf iha ihb
  | zeta _ _ ihv ihb => exact .zeta ihv ihb
  | delta hu _ ih => exact .delta hu ih
  | ctor_val _ _ _ hl _ ihargs => exact .ctor_val hl (fun i h => ihargs i h)
  | lit _ ih => exact .lit ih

/-- **A registered-head spine never `SEvalData`-evaluates to a λ.** If `e` is a
`SEvalData`-evaluation whose source is a constructor/`casesOn`-headed application
spine `args.foldl Expr.app (.const cn us)` (with `cn` registered), its value `r` is
never a λ-abstraction.

The `hnf` premise (a registered head has no δ-unfolding — exactly the first component
of `ErasesEnvDelta`) blocks the `delta` rule on a registered head, so only `ctor_val`
fires and delivers a *const-spine* value; `beta` is impossible because the shorter
head spine would itself have to evaluate to a λ (refuted by the IH).

This is the data analogue of `SEvalβδ_const_spine_elim`; it discharges the
`ctor`/`cases` spine disjunct of `Erases.app_inv` in the `beta` case of
`erases_correct_data`. -/
theorem SEvalData_const_spine_lam_elim {Γ : ErasureCtx} {E : SEnv}
    (hnf : ∀ {n : Name} {body : Expr}, E n = some body →
              Γ.ctors n = none ∧ Γ.casesOns n = none)
    {e r : Expr} (hev : SEvalData Γ E e r) :
    ∀ {cn : Name} {us : List Level} {args : List Expr},
      e = args.foldl Expr.app (.const cn us) →
      (Γ.ctors cn ≠ none ∨ Γ.casesOns cn ≠ none) →
      ¬ ∃ (n : Name) (ty b : Expr) (bi : BinderInfo), r = .lam n ty b bi := by
  induction hev with
  | lam n ty b bi =>
      intro cn us args heq _
      exact absurd heq.symm foldl_app_const_ne_lam
  | @beta f a n ty b bi av r hf ha hbody ihf _ _ =>
      intro cn us args heq hreg
      rcases List.eq_nil_or_concat args with rfl | ⟨init, last, rfl⟩
      · exact absurd heq (by simp)
      · rw [List.concat_eq_append, List.foldl_append, List.foldl_cons,
          List.foldl_nil] at heq
        injection heq with hf_eq _
        exact absurd (ihf hf_eq hreg) (by exact fun h => h ⟨n, ty, b, bi, rfl⟩)
  | @zeta n ty v b nd vv r hval hbody _ _ =>
      intro cn us args heq _
      exact absurd heq.symm foldl_app_const_ne_letE
  | @delta n us body r hunf hbodyev _ =>
      intro cn us' args heq hreg
      rcases List.eq_nil_or_concat args with rfl | ⟨init, last, rfl⟩
      · simp only [List.foldl] at heq
        cases heq
        rcases hreg with h | h
        · exact absurd (hnf hunf).1 h
        · exact absurd (hnf hunf).2 h
      · rw [List.concat_eq_append, List.foldl_append, List.foldl_cons,
          List.foldl_nil] at heq
        exact absurd heq (by simp)
  | @ctor_val cn us iid cidx ar args vs hc har hsat hl hargs _ =>
      intro cn' us' args' _ _
      rintro ⟨n, ty, b, bi, hlam⟩
      exact foldl_app_const_ne_lam hlam
  | @lit l r hev _ =>
      -- a `.lit` source is never a `.const`-headed spine, so the premise is refuted
      intro cn us args heq _
      exact absurd heq.symm foldl_app_const_ne_lit

/-! ## C1 — the corrected ι-carrying data evaluation (`SEvalDataι`)

### Recursor arity data

`ErasureCtx` records, for a `casesOn`-like head, only its inductive and its
parameter count (`casesOns : Name → Option (InductiveId × Nat)`). The model ι rule
(`SimplePattern.iota`, `Pattern.Matches`) fires at **exact arity** — the recursor
spine must carry precisely `numParams + numMotives + numMinors + numIndices`
arguments and the constructor spine precisely `numParams + nfields` — so the ι
statements below need the three counts `ErasureCtx` does not carry. `IotaArities`
supplies them, per `casesOn` name; the constructor side reuses the existing
`Γ.ctorArities` (`= numParams + nfields`, `ErasureContext.lean`). -/

/-- **Recursor arity data for the registered `casesOn` heads.** Maps a `casesOn`-like
name to the underlying recursor's `(numMotives, numIndices, numMinors)`. Together
with `Γ.casesOns`' parameter count `np` and `Γ.ctorArities`' `numParams + nfields`,
this pins the exact arity at which the model ι rule fires (`np + nmot + nidx`
arguments before the major premise, then `nmin` minors). -/
abbrev IotaArities := Name → Option (Nat × Nat × Nat)

/-! ### The corrected relation

`SourceEval.SEvalβζδι.iota` is **under-constrained**: (i) it never ties the scrutinee's
constructor `ctor` to the `casesOn`'s inductive — a `casesOn` for inductive `A` may
match a constructor of an unrelated `B`; and (ii) it applies the selected branch
`minors[cidx]` to **all** of `cargs` (constructor arguments *including parameters*),
whereas MetaRocq's `iota_red np args br = substl (rev (skipn np args)) br.2` drops the
`np` parameters and applies to the **fields only**. `SEvalDataι` supersedes it:

* the head `con` is a registered `casesOn` of inductive `iid` with `np` parameters
  (`Γ.casesOns con = some (iid, np)`);
* the scrutinee's constructor is a registered constructor **of the same `iid`**
  (`Γ.ctors ctor = some (iid, cidx)`) — this ties them together;
* the branch is applied to the constructor's **fields only** `cargs.drop np`.

This is the β+δ+saturated-constructor+ι fragment (data `SEvalDataC` extended with the
corrected `iota`) — plus, since projection round slice P5, the `proj` arm below. -/
inductive SEvalDataι (Γ : ErasureCtx) (ia : IotaArities) (E : SEnv) : Expr → Expr → Prop
  | lam (n : Name) (ty b : Expr) (bi : BinderInfo) :
      SEvalDataι Γ ia E (.lam n ty b bi) (.lam n ty b bi)
  | beta {f a : Expr} {n : Name} {ty b : Expr} {bi : BinderInfo} {av r : Expr} :
      SEvalDataι Γ ia E f (.lam n ty b bi) → SEvalDataι Γ ia E a av →
      SEvalDataι Γ ia E (b.instantiate1' av 0) r → SEvalDataι Γ ia E (.app f a) r
  | delta {n : Name} {us : List Level} {body r : Expr} :
      E n = some body → SEvalDataι Γ ia E body r → SEvalDataι Γ ia E (.const n us) r
  | ctor_val {cn : Name} {us : List Level} {iid : InductiveId} {cidx ar : Nat}
      {args vs : List Expr}
      (hc : Γ.ctors cn = some (iid, cidx)) (har : Γ.ctorArities cn = some ar)
      (hsat : args.length ≤ ar) (hl : args.length = vs.length)
      (hargs : ∀ i (h : i < args.length), SEvalDataι Γ ia E args[i] (vs[i]'(hl ▸ h))) :
      SEvalDataι Γ ia E (args.foldl Expr.app (.const cn us)) (vs.foldl Expr.app (.const cn us))
  /-- ι (`casesOn`), **correctly constrained**. The scrutinee evaluates to a saturated
      constructor of the eliminee's inductive `iid`; the selected minor `minors[cidx]`
      is applied to the constructor's **fields only** (`cargs.drop np`, dropping the
      `np` parameters), matching MetaRocq's `iota_red`.

      The three arity premises (`hpre`/`hmin`/`hcargs`) pin the redex to **exactly**
      the shape the model ι rule fires on — see `IotaArities` and `IotaConsistent`. -/
  | iota {con : Name} {us cus : List Level} {pre minors cargs : List Expr}
      {discr : Expr} {ctor : Name} {iid : InductiveId} {np cidx : Nat}
      {nmot nidx nmin ar : Nat} {r : Expr}
      (hcases : Γ.casesOns con = some (iid, np))
      (hctor : Γ.ctors ctor = some (iid, cidx))
      (hia : ia con = some (nmot, nidx, nmin))
      (har : Γ.ctorArities ctor = some ar)
      (hpre : pre.length = np + nmot + nidx)
      (hmin : minors.length = nmin)
      (hcargs : cargs.length = ar)
      (hdiscr : SEvalDataι Γ ia E discr (cargs.foldl Expr.app (.const ctor cus)))
      (hidx : cidx < minors.length)
      (hbranch : SEvalDataι Γ ia E ((cargs.drop np).foldl Expr.app (minors[cidx]'hidx)) r) :
      SEvalDataι Γ ia E
        ((discr :: minors).foldl Expr.app (pre.foldl Expr.app (.const con us))) r
  /-- **Projection reduction** (`reduceProj`), projection round slice P5. The kernel
      rule being modelled is `TypeChecker.reduceProj`: the discriminant evaluates to a
      **saturated** constructor application of the structure's own single constructor,
      and the projection selects spine position `np + i` — `np` parameters skipped,
      then field `i` — and evaluates it.

      The premises mirror `SEvalDataι.iota`'s, one class lighter (a projection has no
      motive, no indices and no minors):

      * `hs` pins `S` as a registered structure with `np` parameters — the datum
        `visitProj` reads and the one `Erases.proj` carries;
      * `hctor` pins the constructor to `S`'s own inductive **at index `0`**, which is
        both `register_inductive`'s `is_struct` gate (`inf.ctors.length == 1`) and the
        target rule's hard-wired `.construct p.indType 0 []`;
      * `hnfs` is the same gate on the field side, and `hi` the range check;
      * `har`/`hcargs` pin **saturation** exactly as `iota`'s `hcargs` does, which is
        what makes the selection total.

      `hlt` and `hsel` are kept as *two* fields rather than one `∃ h, …` bundle. The
      design sketch bundled them; that would put the recursive occurrence under
      `Exists` and cost the arm its induction hypothesis. `iota` splits `hidx` from
      `hbranch` for the same reason, and this rule copies it. -/
  | proj {S ctor : Name} {cus : List Level} {cargs : List Expr}
      {iid : InductiveId} {np nf i ar : Nat} {discr r : Expr}
      (hs : Γ.projs S = some (iid, np))
      (hctor : Γ.ctors ctor = some (iid, 0))
      (hnfs : Γ.ctorFields iid = some [nf])
      (har : Γ.ctorArities ctor = some ar)
      (hcargs : cargs.length = ar)
      (hi : i < nf)
      (hdiscr : SEvalDataι Γ ia E discr (cargs.foldl Expr.app (.const ctor cus)))
      (hlt : np + i < cargs.length)
      (hsel : SEvalDataι Γ ia E (cargs[np + i]'hlt) r) :
      SEvalDataι Γ ia E (.proj S i discr) r
  /-- A **literal** evaluates by unfolding to its constructor form (see
      `SEvalβζδ.lit`). -/
  | lit {l : Literal} {r : Expr} :
      SEvalDataι Γ ia E l.toConstructor r → SEvalDataι Γ ia E (.lit l) r

/-- **The δ rule is universe-blind** — slice Γ-U's guard, and the reason a universe
relaxation of the *bundles* would be a change of model rather than a change of scope.

Every δ rule in this development — `SEval.delta`, `SEvalβδ.delta`, `SEvalβζδ.delta`,
`SEvalβζδι.delta`, `SEvalData.delta` and `SEvalDataι.delta` above — reads
`E n = some body → … E body r → … E (.const n us) r`: the level arguments `us` are
bound and then **discarded**, and the redex unfolds to the *uninstantiated* `body`.
The kernel's δ step is `body.instantiateLevelParams ci.levelParams us`, so the two
agree exactly when the instantiation is the identity, i.e. when `n` is universe-
monomorphic (`ci.levelParams = []`, so `us = []` and `instantiateLevelParams` is `id`).

This theorem is the machine-checked form of "discarded": **one** body evaluation
serves **every** level instantiation of the same constant. It is not a defect of the
model at the fragment this development ships — `DeltaHyps.decl_run` pins every
dependency at `ci.levelParams = Us` and the capstones run at `Us = []`, so the
identity is the only instantiation reachable — but it is what a Γ-U slice has to
repair *before* relaxing that pin, and it is why relaxing the pin alone would move
the fragment's vacuity from a named bundle field into an unnamed one
(`SEnvConsistent`; see `SEnvConsistent.levels_collapse`). -/
theorem SEvalDataι.delta_level_blind {Γ : ErasureCtx} {ia : IotaArities} {E : SEnv}
    {n : Name} {us us' : List Level} {body r : Expr}
    (hunf : E n = some body) (h : SEvalDataι Γ ia E body r) :
    SEvalDataι Γ ia E (.const n us) r ∧ SEvalDataι Γ ia E (.const n us') r :=
  ⟨.delta hunf h, .delta hunf h⟩

/-- **`IotaConsistent`** — the source-level ι (`casesOn`/recursor) reduction respects
lean4lean definitional equality: a `casesOn` spine's translation is defeq to the
translation of its ι-reduct (the selected branch applied to the constructor fields).

**This is the ONE premise this development does not discharge.** The pinned lean4lean
fork *does* expose an ι/recursor computation rule — `IsDefEq.pat`, fed by the new `VEnv`
rule registry `pats`, which a real (no longer `sorry`ed) `VEnv.addInduct` populates with
one `SimplePattern.iota` rule per recursor rule, alongside a real `VInductDecl.WF` and a
real `Verify.AddInduct` structure. So `IotaConsistent` is **unblocked, not discharged**:
an ambient `VEnv` can now carry ι-defeqs, and `TrEnv.pats_iota'` now hands back the rule
payload named (consumed as `PatsIotaSpec`, discharged by `PatsIotaSpec.of_trEnv`), but
the route from a `TrEnv` to a concrete `VEnv.WF` is still incomplete upstream
(`addInduct_WF` / `Aligned.addInduct` / `addDecl.WF`'s `inductDecl` case are `sorry`) —
see `SubjectReductionIota.lean`'s module docstring for the full accounting, and
`IotaPattern.lean` / `IotaDischarge.lean` for how far the pinned interface *does* reach.
It is stated as an explicit **hypothesis**, never an axiom.

**Exact arity.** The model ι rule matches `SimplePattern.iota r M c N`, which pins the
recursor spine to *exactly* `M = np + nmot + nmin + nidx` arguments and the constructor
spine to *exactly* `N = np + nfields`. The four premises `hia`/`har`/`hpre`/`hmin`/
`hcargs` record that; without them the statement quantifies over spines the ι rule
provably cannot fire on (over-applied `casesOn`s — precisely the C3 counterexample in
`SubjectReductionIota.lean` — and partial applications), and those cases are not merely
harder but *false* for the rule as modelled.

**Well-formed ambient context.** The `VLCtx.WF` premise is the same class of
correction: every typing fact the derivation needs about the redex (`TrExprS.wf`, and
the application generation that recovers the reduct spine's `HasType` nodes) is only
available at a well-formed local context, and every consumer already has one in scope
(`SEvalDataι_defeq` threads its own `hΔ`). -/
def IotaConsistent (env : VEnv) (Us : List Name) (Γ : ErasureCtx) (ia : IotaArities) : Prop :=
  ∀ {Δ : VLCtx} {con ctor : Name} {us cus : List Level} {pre minors cargs : List Expr}
    {iid : InductiveId} {np cidx nmot nidx nmin ar : Nat} {ve : VExpr},
    VLCtx.WF env Us.length Δ →
    Γ.casesOns con = some (iid, np) → Γ.ctors ctor = some (iid, cidx) →
    ia con = some (nmot, nidx, nmin) → Γ.ctorArities ctor = some ar →
    pre.length = np + nmot + nidx → minors.length = nmin → cargs.length = ar →
    (hidx : cidx < minors.length) →
    TrExprS env Us Δ
      (((cargs.foldl Expr.app (.const ctor cus)) :: minors).foldl Expr.app
        (pre.foldl Expr.app (.const con us))) ve →
    ∃ bve, TrExprS env Us Δ ((cargs.drop np).foldl Expr.app (minors[cidx]'hidx)) bve ∧
      env.IsDefEqU Us.length Δ.toCtx ve bve

/-- **`Γ`-internal constructor-arity coherence.** The per-name `ctorArities` (MetaRocq's
full `cstr_arity`) decomposes as `numParams + nfields`, with the field count read off the
per-inductive `ctorFields` list. This is the datum the ι simulation needs to turn
`(cargs.drop np).length` into the selected alternative's binder count: the source rule
pins `cargs.length = ar` while the erasure pins the alternative's telescope to
`nfs[cidx]`, and only this decomposition links them.

Kept *outside* the `Erases.cases` rule deliberately — `Erases.ctor` says nothing about
arity either; `ErasesEnvCtor` carries that link and `erases_correct_data` threads it.
`erases_correct_dataι` threads this one identically. Discharged at registration by
`ctorFieldsCoherent_of_registered` (`EnvErasureNonrec.lean`). -/
def CtorFieldsCoherent (Γ : ErasureCtx) : Prop :=
  ∀ {con cn : Name} {iid : InductiveId} {np cidx : Nat} {nfs : List Nat},
    Γ.casesOns con = some (iid, np) → Γ.ctorFields iid = some nfs →
    Γ.ctors cn = some (iid, cidx) →
    ∃ (h : cidx < nfs.length), Γ.ctorArities cn = some (np + nfs[cidx])


/-- **Projection reduction, as a definitional equality** — the `VEnv`-level interface of
the projection round (slice P4), and the source analogue of the kernel's `reduceProj`: a
projection whose discriminant is (translated as) a saturated constructor spine of `S`'s
single constructor is definitionally equal to the spine's `np + i`-th argument, and that
argument translates.

`IotaConsistent`'s shape, one arity premise lighter — a projection has no motive, no
indices and no minors, so there is no `IotaArities` analogue: everything it would carry is
`1`/`0` by `register_inductive`'s `is_struct` gate, and the shape is pinned by
`Γ.ctorFields iid = some [nf]` instead.

Like `IotaConsistent` this stays a **premise** even once derivable. That is not
timidity: it is what keeps `safety`/`kenv` out of every `VEnv`-level statement downstream,
the discipline `SEvalDataι_defeq`'s own docstring records. The implementation route is
`ProjDefeqSpec` + `ProjShape` (`ProjPattern.lean`), whose composition
`projConsistent_of_shape` is slice P5; that route is *structurally simpler* than the ι
one, because the reduct `cargs[np+i]` is a **subterm of the redex**, so its `TrExprS` is
read straight off `TrExprS.mkApps_inv`'s `Forall₂` rather than built by application
generation.

**The discriminant is the *unreduced* one, and its subject reduction arrives as a
function** (slice P6). The P4 statement quantified over `TrExprS Δ (.proj S i (ctor c̄))
ve`, i.e. over the *already reduced* redex; every consumer has `TrExprS Δ (.proj S i
discr) ve` instead, and bridging the two would need a `TrProj` congruence under a defeq
discriminant — which the design costed as a separate lemma. It is not needed, and the
reason is structural: `ProjDefeqSpec`/`TrEnv.proj_defeq` **already** takes its
discriminant up to definitional equality (`hd : IsDefEqU d ((const c cus).mkApps
(params ++ fields))`), so the congruence the design wanted to prove is exactly the
premise the upstream rule wants to be given. Threading `hdiscr` here — the same
"subject reduction as a function" device `SEvalDataι_iota_reduct` uses for the ι
discriminant — hands it over directly and removes the congruence obligation from the
round.

A `Prop` **hypothesis**, never an axiom. -/
def ProjConsistent (env : VEnv) (Us : List Name) (Γ : ErasureCtx) : Prop :=
  ∀ {Δ : VLCtx} {S ctor : Name} {cus : List Level} {cargs : List Expr}
    {iid : InductiveId} {np nf i ar : Nat} {discr : Expr} {ve : VExpr},
    VLCtx.WF env Us.length Δ →
    Γ.projs S = some (iid, np) → Γ.ctors ctor = some (iid, 0) →
    Γ.ctorFields iid = some [nf] → Γ.ctorArities ctor = some ar →
    cargs.length = ar → i < nf → (hlt : np + i < cargs.length) →
    TrExprS env Us Δ (.proj S i discr) ve →
    (∀ {dve : VExpr}, TrExprS env Us Δ discr dve →
      ∃ cve, TrExprS env Us Δ (cargs.foldl Expr.app (.const ctor cus)) cve ∧
        env.IsDefEqU Us.length Δ.toCtx dve cve) →
    ∃ fve, TrExprS env Us Δ (cargs[np + i]'hlt) fve ∧
      env.IsDefEqU Us.length Δ.toCtx ve fve

/-- **`ProjConsistent` is free at a `Γ` that registers no structure** (projection round,
slice P6). Every clause of the interface is keyed on `Γ.projs S = some _`, so at
`Γ.projs = ⊥` — every `Γ` in the tree that predates the projection round, including the
capstone guards' `ΓFOι` — it holds by refutation and needs no `VEnv` reasoning at all.

This is what makes the round *additive at the guards*: a projection-free capstone
instantiation discharges the new premise instead of assuming it. The `Γproj` fixture is
where the non-vacuous side lives. -/
theorem projConsistent_of_noProjs {env : VEnv} {Us : List Name} {Γ : ErasureCtx}
    (h : Γ.projs = fun _ => none) : ProjConsistent env Us Γ := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ hs
  rw [h] at hs; exact absurd hs (by simp)

/-- **`Γ`-internal projection-arity coherence** — `CtorFieldsCoherent`'s twin, keyed on
`Γ.projs` instead of `Γ.casesOns` (projection round, slice P0).

The projection simulation needs the same decomposition `ctorArities = numParams + fields`
that the ι one does, for the *same* reason and at the same inductive: `WcbvEval.proj`
selects `args[p.paramCount + p.fieldIdx]`, so the target index `np + i` must be in range
for a spine whose length the source rule pins to `Γ.ctorArities ctor`. Only this
decomposition links the two.

Stated as a twin rather than by widening `CtorFieldsCoherent`'s hypothesis to a
disjunction, which keeps that predicate's six existing call sites byte-unchanged. The
constructor index is hard-wired to `0` — `register_inductive`'s `is_struct` gate
(`inf.ctors.length == 1`) is what makes a structure's only constructor constructor `0`,
and it is the same `0` the target rule's `.construct p.indType 0 []` carries.

Discharged at registration by `projFieldsCoherent_of_registered`
(`EnvErasureNonrec.lean`). -/
def ProjFieldsCoherent (Γ : ErasureCtx) : Prop :=
  ∀ {S cn : Name} {iid : InductiveId} {np : Nat} {nfs : List Nat},
    Γ.projs S = some (iid, np) → Γ.ctorFields iid = some nfs →
    Γ.ctors cn = some (iid, 0) →
    ∃ (h : 0 < nfs.length), Γ.ctorArities cn = some (np + nfs[0])

/-- …and `ProjFieldsCoherent` is free at `Γ.projs = ⊥` for the same reason as
`projConsistent_of_noProjs`. -/
theorem projFieldsCoherent_of_noProjs {Γ : ErasureCtx} (h : Γ.projs = fun _ => none) :
    ProjFieldsCoherent Γ := by
  intro _ _ _ _ _ hs
  rw [h] at hs; exact absurd hs (by simp)

/-- **`IotaArities` ↔ `ErasureCtx` coherence.** `SEvalDataι.iota` pins its redex
*arithmetically*, through `ia` (`pre.length = np + nmot + nidx`, `minors.length = nmin`);
`Erases.cases` pins the same spine *through `Γ`* (`Γ.casesDiscrPos con = some pre.length`,
`Γ.ctorFields iid = some nfs` with one alternative per constructor). These are two
independent parses of one spine, and without a link the source relation and the erasure
relation may split the same `Expr` at two different places — the hazard the T1 arity pins
were introduced to close, in a new guise.

The link: the recursor's `numParams + numMotives + numIndices` **is** the `casesOn`'s
`CasesInfo.discrPos`, and its `numMinors` **is** the inductive's constructor count. Both
hold by construction for every real `casesOn` (`nmot = 1`, and
`discrPos = numParams + 1 + numIndices` — `Lean/Meta/CasesInfo.lean`); they are stated as
a predicate rather than proved because `ErasureCtx` and `IotaArities` are independent
parameters of the development. Discharged at registration alongside the inductive's field
data, and by `rfl` in the non-vacuity guards. -/
def IotaArityCoherent (Γ : ErasureCtx) (ia : IotaArities) : Prop :=
  ∀ {con : Name} {iid : InductiveId} {np nmot nidx nmin : Nat},
    Γ.casesOns con = some (iid, np) → ia con = some (nmot, nidx, nmin) →
    Γ.casesDiscrPos con = some (np + nmot + nidx) ∧
    ∃ nfs, Γ.ctorFields iid = some nfs ∧ nfs.length = nmin

/-! ### C2/C3 — where the ι theorems live.

Subject reduction over `SEvalDataι` is `SEvalDataι_defeq` (`SubjectReductionIota.lean`),
with `IotaConsistent` discharged by `SEvalDataι_defeq_of_shape`; the ι forward simulation
is `erases_correct_dataι` (`ErasesCorrectIota.lean`), which additionally consumes the
`casesOn`-spine erasure inversion (`Erases.cases_spine_inv` / `Erases.iota_redex_inv`,
`ErasesCorrectData.lean`) and — for field-carrying inductives — the β-chain ↔
reversing-`iota_red` bridge over the P0-corrected `iota_red`. The corrected relation
`SEvalDataι` (C1) supersedes `SEvalβζδι`. -/

end LeanToLambdaBox
