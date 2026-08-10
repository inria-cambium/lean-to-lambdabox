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
corrected `iota`). -/
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

/-- **`IotaConsistent`** — the source-level ι (`casesOn`/recursor) reduction respects
lean4lean definitional equality: a `casesOn` spine's translation is defeq to the
translation of its ι-reduct (the selected branch applied to the constructor fields).

**This is the ONE premise this development does not discharge.** The pinned lean4lean
fork *does* expose an ι/recursor computation rule — `IsDefEq.pat`, fed by the new `VEnv`
rule registry `pats`, which a real (no longer `sorry`ed) `VEnv.addInduct` populates with
one `SimplePattern.iota` rule per recursor rule, alongside a real `VInductDecl.WF` and a
real `Verify.AddInduct` structure. So `IotaConsistent` is **unblocked, not discharged**:
an ambient `VEnv` can now carry ι-defeqs, but the route from a `TrEnv` to a concrete one
is still incomplete upstream (`TrEnv.pats_iota` leaves the rule payload opaque;
`addInduct_WF` / `Aligned.addInduct` / `addDecl.WF`'s `inductDecl` case are `sorry`) —
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

/-! ### C2/C3 — subject reduction and the ι-simulation (remaining, documented).

`SEvalDataι_defeq` (subject reduction over `SEvalDataι`) and the ι case of the
data-fragment forward simulation reuse the β+ζ+δ chain for the non-ι rules; the ι case
is discharged **only** through `IotaConsistent` (the fork's ι-defeq route exists but is
not yet chainable, as documented above). Mechanising them additionally needs a
`casesOn`-spine translation
inversion (to expose the evaluated scrutinee's ctor-spine translation) and a
`β`-chain ↔ `iota_red`-substitution bridge over the P0-corrected reversing `iota_red`.
These are the remaining C2/C3 pieces; the corrected relation `SEvalDataι` and the honest
`IotaConsistent` premise (C1) are in place and supersede `SEvalβζδι`. -/

end LeanToLambdaBox
