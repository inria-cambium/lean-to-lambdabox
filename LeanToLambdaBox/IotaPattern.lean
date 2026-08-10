import Lean4Lean.Verify.Environment.Lemmas
import Lean4Lean.Verify.Typing.Lemmas

/-!
# The ι pattern interface: matching a recursor redex and computing its reduct

The pinned `barabbs/lean4lean` ι fork models ι-reduction as a *schematic rule*:
`VEnv.pats` is a registry of `(Pattern, Pattern.RHS × Pattern.Check)` pairs and
`VEnv.IsDefEq.pat` (wrapped as `TrEnv.iota_defeq`) turns a registered rule, matched
against a well-typed redex, into a definitional equality. `VEnv.addRecRule`
registers, per recursor rule, the pattern `SimplePattern.iota` and the reduct
`SimplePattern.iotaRHS`.

Consuming that interface needs three things the fork does **not** provide, and this
file provides them:

* **`matches_varN_const` / `matches_iota`** — a `Pattern.Matches` *introduction* rule
  for spines. `Pattern.Matches` has only its three constructors plus transports; the
  docstring of `Pattern.varN_pathOf` claims validation "against `Pattern.Matches`"
  but no such lemma exists. `matches_varN_const` builds the match of a
  `q.varN k` pattern against a `k`-ary constant spine *and* pins each hole:
  `m2 (varN_pathOf k i h) = args[i]`. `matches_iota` composes two of them through
  `Matches.app` into the ι redex shape
  `(rec a₀ … a_{M-1}) (ctor b₀ … b_{N-1})`.
* **`iotaRHS_apply`** — the reduct *calculation*. `SimplePattern.iotaRHS` is a
  `foldl` of `RHS.app` over two `pmap`-of-`range` hole lists; applied to a matcher it
  yields exactly
  `VExpr.mkApps (rhs.instL m1) (as.take (np+nm+nmin) ++ bs.drop np)`.
  The two slices are **not** symmetric and are the easiest thing in this development
  to get backwards: the rec-side holes are `range (np+nm+nmin)` over a spine of
  length `np+nm+nmin+nind`, i.e. a `take` that drops the **indices** (which sit
  *between* the minors and the major premise); the ctor-side holes are `range nf` at
  paths `np+j`, i.e. a `drop np` that keeps the **fields**. Getting either backwards
  silently produces a well-typed but wrong reduct, which is why `iotaRHS_apply` is
  stated with explicit `take`/`drop` and why the guard in `IotaDischarge.lean`
  exercises a shape with `np > 0` *and* `nind > 0` (with `np = nind = 0` both slices
  degenerate and a wrong convention still looks right).
* **`TrExprS.mkApps_inv`** — full spine inversion for `TrExprS`
  (`TrExprS_spine_head` in `SubjectReductionFull.lean` returns only the head).

On top of those, `PatsIotaSpec` names the *strengthened* rule-lookup lemma the fork
still owes us, and `iota_defeq_spine` is the payoff: on a translated exact-arity
recursor-applied-to-constructor redex, the ι rule **fires**.
-/

namespace Lean4Lean

open Lean

/-! ## List plumbing for the `pmap`-over-`range` hole lists -/

/-- `l.take k` as a `pmap` over `range k` — the shape `SimplePattern.iotaRHS`'s
rec-side hole list has. -/
theorem take_eq_range_pmap {α} (l : List α) (k : Nat) (hk : k ≤ l.length) :
    (List.range k).pmap (fun i (h : i < l.length) => l[i])
      (fun i hi => Nat.lt_of_lt_of_le (List.mem_range.1 hi) hk) = l.take k := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left hk]
  · intro n h1 h2
    simp

/-- `l.drop np` as a `pmap` over `range nf` — the shape `SimplePattern.iotaRHS`'s
ctor-side hole list has (holes at paths `np+j`, `j < nf`). -/
theorem drop_eq_range_pmap {α} (l : List α) (np nf : Nat) (hk : l.length = np + nf) :
    (List.range nf).pmap (fun j (h : np + j < l.length) => l[np+j])
      (fun j hj => by have := List.mem_range.1 hj; omega) = l.drop np := by
  apply List.ext_getElem
  · simp; omega
  · intro n h1 h2
    simp

/-- Snoc for `VExpr.mkApps` (`= List.foldl .app`). -/
theorem VExpr.mkApps_concat (f : VExpr) (l : List VExpr) (a : VExpr) :
    VExpr.mkApps f (l ++ [a]) = .app (VExpr.mkApps f l) a := by
  simp [VExpr.mkApps, List.foldl_append]

/-! ## `varN_pathOf` orientation

`Pattern.varN k` adds its `.var`s **outermost-last**, so the *last* argument of a
spine sits at path `none` and argument `i < k` at `someᵏ⁻¹⁻ⁱ none`. These two
lemmas are the only place that orientation is unfolded; `matches_varN_const` and
`iotaRHS_apply` both go through them, so they cannot disagree. -/

/-- The last argument of a `k+1`-ary spine sits at the outermost hole. -/
theorem Pattern.varN_pathOf_self {q : Pattern} {k : Nat} (h : k < k+1) :
    Pattern.varN_pathOf (q := q) (k+1) k h = (none : Option (q.varN k).Path) := dif_pos rfl

/-- An earlier argument sits one `.var` deeper. -/
theorem Pattern.varN_pathOf_lt {q : Pattern} {k i : Nat} (h : i < k+1) (hik : i ≠ k)
    (h' : i < k) :
    Pattern.varN_pathOf (q := q) (k+1) i h = some (Pattern.varN_pathOf (q := q) k i h') :=
  dif_neg hik

/-! ## `Matches` introduction for constant spines -/

/-- **A `k`-ary constant spine matches `(.const c).varN k`, with the holes named.**
The matcher's level list is the head's (`ls`) and hole `varN_pathOf k i` is the
`i`-th argument. This is the `Pattern.Matches` introduction rule the fork lacks. -/
theorem Pattern.matches_varN_const {c : Name} {ls : List VLevel} :
    ∀ (k : Nat) (args : List VExpr) (hlen : args.length = k),
      ∃ m2, Pattern.Matches ((Pattern.const c).varN k)
              (VExpr.mkApps (.const c ls) args) ls m2 ∧
            ∀ i (h : i < k), m2 (Pattern.varN_pathOf k i h) = args[i]'(hlen ▸ h)
  | 0, args, hlen => by
    obtain rfl : args = [] := List.eq_nil_of_length_eq_zero hlen
    exact ⟨nofun, .const, nofun⟩
  | k+1, args, hlen => by
    rcases List.eq_nil_or_concat args with rfl | ⟨init, last, rfl⟩
    · simp at hlen
    · simp only [List.concat_eq_append] at hlen ⊢
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      have hinit : init.length = k := by omega
      obtain ⟨m2, hm, hval⟩ := Pattern.matches_varN_const (c := c) (ls := ls) k init hinit
      refine ⟨fun p => Option.elim p last m2, ?_, ?_⟩
      · rw [VExpr.mkApps_concat]
        exact hm.var
      · intro i h
        show (Pattern.varN_pathOf (k+1) i h).elim last m2 = _
        by_cases hik : i = k
        · subst hik
          rw [Pattern.varN_pathOf_self]
          show last = _
          simp [hinit]
        · have h' : i < k := by omega
          rw [Pattern.varN_pathOf_lt h hik h']
          show m2 _ = _
          rw [hval i h', List.getElem_append_left (hinit ▸ h')]

/-- **The ι redex builder.** `(SimplePattern.iota r M c N).toPattern` matches exactly
`(r a₀ … a_{M-1}) (c b₀ … b_{N-1})`, at the *recursor's* level list (`Matches.app`
keeps only the left branch's levels — so `rhs.instL m1` below instantiates with the
recursor spine's universes, not the constructor's). -/
theorem Pattern.matches_iota {recName cName : Name} {ls ls' : List VLevel}
    (M N : Nat) (as bs : List VExpr) (has : as.length = M) (hbs : bs.length = N) :
    ∃ m2, ((SimplePattern.iota recName M cName N).toPattern).Matches
            (.app (VExpr.mkApps (.const recName ls) as) (VExpr.mkApps (.const cName ls') bs))
            ls m2 ∧
          (∀ i (h : i < M), m2 (.inl (Pattern.varN_pathOf M i h)) = as[i]'(has ▸ h)) ∧
          (∀ j (h : j < N), m2 (.inr (Pattern.varN_pathOf N j h)) = bs[j]'(hbs ▸ h)) := by
  obtain ⟨m2a, hma, hvala⟩ := Pattern.matches_varN_const (c := recName) (ls := ls) M as has
  obtain ⟨m2b, hmb, hvalb⟩ := Pattern.matches_varN_const (c := cName) (ls := ls') N bs hbs
  exact ⟨Sum.elim m2a m2b, hma.app hmb, hvala, hvalb⟩

/-! ## The reduct calculation -/

/-- `RHS.apply` turns a `foldl RHS.app` into a `VExpr.mkApps`. -/
theorem Pattern.RHS.apply_foldl {p : Pattern} {m1 m2} (base : p.RHS) :
    ∀ (l : List p.RHS),
      (l.foldl Pattern.RHS.app base).apply m1 m2
        = VExpr.mkApps (base.apply m1 m2) (l.map (Pattern.RHS.apply m1 m2))
  | [] => rfl
  | a :: as => by
    show ((as.foldl Pattern.RHS.app (base.app a)).apply m1 m2) = _
    rw [Pattern.RHS.apply_foldl (base.app a) as]
    rfl

/-- **The registered ι reduct, computed.** Applying `SimplePattern.iotaRHS` to a
matcher gives the rule template (level-instantiated at the *recursor's* universes)
applied to

* the recursor spine's **parameters, motives and minors** — `as.take (np+nm+nmin)`,
  dropping the `nind` indices, which sit between the minors and the major premise;
* the constructor spine's **fields** — `bs.drop np`, dropping its parameters,

in that order and *not* reversed. This is exactly `inductiveReduceRec`'s slicing and
exactly the argument list the source-side ι reduct
`(cargs.drop np).foldl Expr.app minors[cidx]` wants. -/
theorem SimplePattern.iotaRHS_apply {r c : Name} {np nm nmin nind nf : Nat}
    {rhs : VExpr} {hc : rhs.Closed} {m1 : List VLevel}
    {m2 : (SimplePattern.iota r (np+nm+nmin+nind) c (np+nf)).toPattern.Path → VExpr}
    {as bs : List VExpr}
    (has : as.length = np+nm+nmin+nind) (hbs : bs.length = np+nf)
    (hma : ∀ i (h : i < np+nm+nmin+nind),
      m2 (.inl (Pattern.varN_pathOf (np+nm+nmin+nind) i h)) = as[i]'(has ▸ h))
    (hmb : ∀ j (h : j < np+nf),
      m2 (.inr (Pattern.varN_pathOf (np+nf) j h)) = bs[j]'(hbs ▸ h)) :
    (SimplePattern.iotaRHS r c np nm nmin nind nf rhs hc).apply m1 m2
      = VExpr.mkApps (rhs.instL m1) (as.take (np+nm+nmin) ++ bs.drop np) := by
  rw [SimplePattern.iotaRHS, Pattern.RHS.apply_foldl]
  congr 1
  rw [List.map_append]
  congr 1
  · rw [List.map_pmap, ← take_eq_range_pmap as (np+nm+nmin) (by omega)]
    apply List.pmap_congr_left
    intro i hi h1 h2
    exact hma i _
  · rw [List.map_pmap, ← drop_eq_range_pmap bs np nf hbs]
    apply List.pmap_congr_left
    intro j hj h1 h2
    exact hmb (np+j) _

/-! ## `TrExprS` spine inversion -/

/-- **Full spine inversion.** A translated application spine decomposes into a
translated head, translated arguments, and a `VExpr.mkApps`. (`TrExprS_spine_head`
in `SubjectReductionFull.lean` gives only the head.) -/
theorem TrExprS.mkApps_inv {env : VEnv} {Us : List Name} {Δ : VLCtx} :
    ∀ {args : List Expr} {head : Expr} {ve : VExpr},
      TrExprS env Us Δ (args.foldl Expr.app head) ve →
      ∃ hve args', TrExprS env Us Δ head hve ∧
        List.Forall₂ (TrExprS env Us Δ) args args' ∧ ve = VExpr.mkApps hve args'
  | [], _, _, htr => ⟨_, [], htr, .nil, rfl⟩
  | _ :: as, head, ve, htr => by
    obtain ⟨hve, args', htrHead, hall, rfl⟩ :=
      TrExprS.mkApps_inv (args := as) (head := .app head _) htr
    cases htrHead with
    | @app f' A B a' _ _ _ hTf hTa htrf htra =>
      exact ⟨f', a' :: args', htrf, .cons htra hall, rfl⟩

/-- A translated constant is a constant (at some translated level list). -/
theorem TrExprS.const_inv {env : VEnv} {Us : List Name} {Δ : VLCtx} {c us ve}
    (h : TrExprS env Us Δ (.const c us) ve) : ∃ us', ve = .const c us' := by
  cases h with | const _ _ _ => exact ⟨_, rfl⟩

end Lean4Lean

namespace LeanToLambdaBox

open Lean Lean4Lean

/-! ## The named upstream spec

`TrEnv.pats_iota` (`Verify/Environment/Lemmas.lean`) concludes `∃ r, venv.pats P r`
with the rule payload `r` **existentially bound**, so `TrEnv.iota_defeq`'s `Realizes`
premise cannot be instantiated and the reduct cannot be matched against anything. The
fork's own proof does know the witness — its `induct` case ends in
`exact ⟨_, VEnv.addInduct_pat …⟩`, and `addInduct_pat` names the pair
`(SimplePattern.iotaRHS …, .true)` — so naming it is a pure statement strengthening
of already-proved content.

`PatsIotaSpec` states that strengthened lemma **verbatim as it landed on the fork's
`iota-consume` branch**, as a hypothesis structure in the repo's `BridgeHyps` /
`DataBridgeHyps` / `ResidualHyps` idiom. It bundles three fixes:

* **the witness is named** (`SimplePattern.iotaRHS …, .true`), so `iota_defeq` can be
  instantiated at `chk := []`, `hR := trivial`, `hall := nofun`;
* **the motives/minors/indices split is kernel-pinned.** `AddInduct.rec_find` relates
  only `getMajorIdx` (the *sum*) and `numParams`, but `iotaRHS` splits the rec-side
  holes at `np+nm+nmin`, so two model recursors with the same total and a different
  split register different reducts under the same pattern;
* **the reduct is tied to the kernel rule** (`TrExprS venv rval.levelParams []
  rule.rhs rhs`). Nothing in `AddInduct.rec_find` relates `ru.rhs` to `rule.rhs`, and
  the "a pattern determines its reduct" fact that would recover it
  (`VEnv.toParams.pat_uniq`) is not only `sorry` upstream but *documented as false*.

**Discharge.** This is not an axiom and not a `sorry`: once the fork's `pats_iota'`
is pushed and re-pinned, the whole structure is

```lean
theorem PatsIotaSpec.of_trEnv (H : TrEnv safety kenv venv) : PatsIotaSpec safety kenv venv :=
  ⟨fun hrec hrule hsafe => TrEnv.pats_iota' H hrec hrule hsafe⟩
```

and nothing else in this development changes. The field below is stated at the
*current* pin's types (`SimplePattern.iota` / `iotaRHS` / `VEnv.pats` all exist at
`7c5e652`; only the primed lemma is missing), so it elaborates today.

**Safety.** `TrEnv'.induct` fires only at `.safe`, and the lookup needs
`hsafe : safety ≤ (recInfo rval).safety`; anything built at another safety level
silently has no ι rules (`DefinitionSafety.le_safe` discharges it for safe
declarations). -/
structure PatsIotaSpec (safety : DefinitionSafety) (kenv : Lean.Environment) (venv : VEnv) :
    Prop where
  /-- The ι rule of a recursor rule resolvable in `kenv` is registered in `venv.pats`,
  **with its payload named**: the reduct is `SimplePattern.iotaRHS` over a closed
  translation `rhs` of the *kernel* rule's template `rule.rhs`, at the kernel's own
  `numParams`/`numMotives`/`numMinors`/`numIndices` split, and the side-condition
  check is the trivial one. -/
  pats_iota' : ∀ {recName cName : Name} {rval : RecursorVal} {rule : RecursorRule},
    kenv.find? recName = some (.recInfo rval) →
    rval.rules.find? (·.ctor == cName) = some rule →
    safety ≤ (Lean.ConstantInfo.recInfo rval).safety →
    ∃ (rhs : VExpr) (hc : rhs.Closed),
      TrExprS venv rval.levelParams [] rule.rhs rhs ∧
      venv.pats
        (SimplePattern.iota recName
          (rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices) cName
          (rval.numParams + rule.nfields)).toPattern
        (SimplePattern.iotaRHS recName cName rval.numParams rval.numMotives rval.numMinors
          rval.numIndices rule.nfields rhs hc, .true)

/-! ## The ι step: the rule fires on a translated redex -/

/-- **The ι rule fires.** Given the named spec, a translated **exact-arity** redex
`rec a₀ … a_{M-1} (ctor b₀ … b_{N-1})` — with `M = np+nm+nmin+nind` and
`N = np+nfields`, the only shape `SimplePattern.iota` matches — is definitionally
equal to the kernel rule's template applied to the recursor's
parameters/motives/minors and the constructor's fields.

Everything on the right-hand side is *named*: `rhs` is the translation of
`rule.rhs`, and the argument lists are the translations of the source spines'
arguments. The `hty` premise of `iota_defeq` comes from `TrExprS.wf`; the
`Realizes`/side-condition premises are discharged at `chk := []` because the
registered check is the literal `Pattern.Check.true`. -/
theorem iota_defeq_spine {safety : DefinitionSafety} {kenv : Lean.Environment} {venv : VEnv}
    (hspec : PatsIotaSpec safety kenv venv) (henv : venv.WF)
    {Us : List Name} {Δ : VLCtx} (hΔ : VLCtx.WF venv Us.length Δ)
    {recName cName : Name} {rval : RecursorVal} {rule : RecursorRule}
    (hrec : kenv.find? recName = some (.recInfo rval))
    (hrule : rval.rules.find? (·.ctor == cName) = some rule)
    (hsafe : safety ≤ (Lean.ConstantInfo.recInfo rval).safety)
    {recArgs ctorArgs : List Expr} {rus cus : List Level} {ve : VExpr}
    (hras : recArgs.length =
      rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices)
    (hcas : ctorArgs.length = rval.numParams + rule.nfields)
    (htr : TrExprS venv Us Δ
      (.app (recArgs.foldl Expr.app (.const recName rus))
            (ctorArgs.foldl Expr.app (.const cName cus))) ve) :
    ∃ (rhs : VExpr) (_ : rhs.Closed) (rus' : List VLevel) (recArgs' ctorArgs' : List VExpr),
      TrExprS venv rval.levelParams [] rule.rhs rhs ∧
      List.Forall₂ (TrExprS venv Us Δ) recArgs recArgs' ∧
      List.Forall₂ (TrExprS venv Us Δ) ctorArgs ctorArgs' ∧
      venv.IsDefEqU Us.length Δ.toCtx ve
        (VExpr.mkApps (rhs.instL rus')
          (recArgs'.take (rval.numParams + rval.numMotives + rval.numMinors)
            ++ ctorArgs'.drop rval.numParams)) := by
  obtain ⟨A, hty⟩ := htr.wf henv.ordered hΔ
  obtain ⟨rhs, hc, htrRhs, hpats⟩ := hspec.pats_iota' hrec hrule hsafe
  cases htr with
  | @app f' A₀ B a' _ _ _ hTf hTa htrf htra =>
    obtain ⟨hve1, recArgs', htrRecHead, hall1, rfl⟩ := TrExprS.mkApps_inv htrf
    obtain ⟨hve2, ctorArgs', htrCtorHead, hall2, rfl⟩ := TrExprS.mkApps_inv htra
    obtain ⟨rus', rfl⟩ := htrRecHead.const_inv
    obtain ⟨cus', rfl⟩ := htrCtorHead.const_inv
    have hras' : recArgs'.length =
        rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices := by
      rw [← Lean4Lean.List.Forall₂.length_eq hall1]; exact hras
    have hcas' : ctorArgs'.length = rval.numParams + rule.nfields := by
      rw [← Lean4Lean.List.Forall₂.length_eq hall2]; exact hcas
    obtain ⟨m2, hm, hva, hvb⟩ :=
      Pattern.matches_iota (recName := recName) (cName := cName) (ls := rus') (ls' := cus')
        _ _ recArgs' ctorArgs' hras' hcas'
    refine ⟨rhs, hc, rus', recArgs', ctorArgs', htrRhs, hall1, hall2, ?_⟩
    have := TrEnv.iota_defeq (chk := []) hpats hm hty trivial nofun
    rwa [SimplePattern.iotaRHS_apply hras' hcas' hva hvb] at this

end LeanToLambdaBox
