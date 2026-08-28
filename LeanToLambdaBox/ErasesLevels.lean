import LeanToLambdaBox.Erases

/-!
# Level-scope weakening along a prefix extension (slice Γ-U1)

The Γ-U analysis in `DeltaHyps` (module docstring, §Γ-U) costed the relaxation of the
universe-monomorphism scope restriction and found the transport it was supposed to rest
on — `TrExprS.instL` — to be the wall: level *substitution* lands in `TrExpr`, not
`TrExprS`, because it re-derives sort and const levels only up to `≈`, while
`Erases.box`/`lam`/`letE` record **strict** `TrExprS` witnesses and at `lam`/`letE` a
defeq-loose binder type breaks the context chain the sub-derivation runs in.

This file lands the half of the plan that *is* strict. Substitution is not the only way
to move between level scopes: a scope may simply be **extended on the right**. Along a
prefix extension `Us <+: Us'` no index moves — `VLevel.ofLevel` resolves a parameter by
`List.idxOf`, which finds the *first* occurrence, and a first occurrence inside the
prefix stays where it is when the list grows on the right. So the very same `VLevel` is
produced, the derivation transports on the nose, and the conclusion is a `TrExprS` and
not a `TrExpr`. That is the whole content of the slice, and it is why Γ-U2 can relax
`BridgeInv.lparams`/`decl_run`/`block_lparams` to `ci.levelParams <+: Us` where it could
not relax them to "any instantiation".

Two facts do the work, and they are independent:

* **Index stability** (`VLevel.ofLevel_prefix`): `ofLevel` succeeds at `Us'` wherever it
  succeeded at `Us`, with the *same* `VLevel`. This is the prefix-specific half; it is
  false for a permutation, which `ofLevel_perm_index_shifts` and
  `not_ofLevel_weaken_of_perm` exhibit at the bottom of the file. A permuted scope has
  the same *set* of parameters and the same length, and still breaks the lemma — so the
  restriction to prefixes is not slack in the statement.
* **Universe-count monotonicity** (`VEnv.IsDefEq.uvars_mono`): lean4lean's typing
  judgement mentions its `uvars` argument at exactly three constructors (`sortDF`,
  `constDF`, `extra`) and only through `VLevel.WF uvars`, which is monotone in the
  count. This is the half that carries the `env.HasType Us.length …` / `IsType` /
  `TrProj` side premises of `TrExprS`, and — one layer up — the `box` arm's
  `Erasable env Us.length Δ.toCtx ve`.

**The box arm resolves here, not at Γ-U3.** The plan flagged `Erases.box`'s
`Erasable env Us.length Δ.toCtx ve` as the place a `VExpr`-side wall might live, since
`Erasable` is stated at the level *count* rather than at the scope. It does not: unfolded,
`Erasable` is a `HasType` together with a `HasType`-or-`IsArityUpTo` disjunct, and every
one of those is `IsDefEq` at `U`. `Erasable.uvars_mono` is therefore a corollary of
`IsDefEq.uvars_mono` with no environment-side lift, no `env.WF` premise and no context
condition. The `VLCtx` side never enters at all: `Us` and `Δ` are orthogonal parameters
of `TrExprS`, `Δ.toCtx` does not mention `Us`, and the `bvar`/`fvar` arms are pure
`VLCtx.find?` lookups. So the whole family below is premise-free apart from the prefix.

What this slice deliberately does **not** do: relax any bundle field (that is Γ-U2, and
the analysis records why it must not ship alone), prove `Erases.instL` (Γ-U3, the wall),
or touch the δ rule's level blindness (Γ-U4, the content). It is a lemma kit, stated in
the general `Us <+: Us'` form its consumer instantiates at `ci.levelParams <+: Us`.
[**All three landed the same day, 2026-08-28.** `Erases.instL` exists and is strict
(`ErasesInstL.lean`) — the wall was normalisation, not substitution — and the δ rule
instantiates (`ErasesDeltaL.lean`, `SubjectReductionFull.SEnvConsistentL`). The paragraph
is kept because it is what this file was written against.]

**Consumed at Γ-U2** (2026-08-28), and not where the plan expected. The four scope pins —
`BridgeInv.lparams`, `DeltaHyps.decl_run`, `BlockHyps.block_lparams` and
`BridgeHyps.orc_run`'s guard — relaxed to `<+: Us` with no proof repair *in the bridge*:
the reader's `lparams` reaches its proof only through the oracle's guard, so nothing in
`VisitExprRefines` calls these lemmas. The oracle is where the repair did land, and it is
Γ-U2's one cost rather than a use of this kit — `ResidualHyps.orc_refl` gained a
`ctx.lparams = Us` conjunct and `toBridgeHyps` destructures it (`OracleDischarge.lean`),
because `orc_run` is contravariant in `TrExprS` and covariant in `Erasable` and these
lemmas transport upward only. What they are actually for is **satisfiability**:
`DeltaHyps.prepared` and
`esrc_shape` are stated at the ambient `Us`, and it is `TrExprS.prefix_weaken` that lets a
producer discharge them from the dependency's own scope, which is the correction to the
Γ-U analysis' finding (b) (`DeltaHyps.gPreparedAtPrefix`). The `Erases` half is the same
story one layer up (`DeltaHyps.gErasesDepPrefix`).
-/

namespace Lean4Lean

open Lean

/-- A first occurrence inside a prefix is not moved by appending on the right.

The `<` premise is exactly `VLevel.ofLevel`'s own membership test (`ls.idxOf n <
ls.length`), which is why the lemma is stated with it rather than with `n ∈ l`. -/
theorem List.idxOf_append_of_lt {l t : List Name} {n : Name} (h : l.idxOf n < l.length) :
    (l ++ t).idxOf n = l.idxOf n := by
  show List.findIdx _ (l ++ t) = _
  rw [List.findIdx_append, if_pos (show List.findIdx (fun x => x == n) l < l.length from h)]
  rfl

/-- **Index stability under a prefix extension.** `VLevel.ofLevel` succeeds at the longer
level scope wherever it succeeded at the prefix, and returns the *same* `VLevel` — not a
`≈`-equivalent one. This is the fact that makes the whole Γ-U1 family strict, and the one
that fails for a non-prefix rearrangement (see `not_ofLevel_weaken_of_perm`). -/
theorem VLevel.ofLevel_prefix {Us Us' : List Name} (hp : Us <+: Us') :
    ∀ {l : Level} {l' : VLevel},
      VLevel.ofLevel Us l = some l' → VLevel.ofLevel Us' l = some l' := by
  obtain ⟨t, rfl⟩ := hp
  intro l
  induction l with
  | zero => intro _ h; exact h
  | succ _ ih =>
    intro _ h; simp [VLevel.ofLevel, bind] at h ⊢
    obtain ⟨a, ha, rfl⟩ := h; exact ⟨a, ih ha, rfl⟩
  | max _ _ ih1 ih2 =>
    intro _ h; simp [VLevel.ofLevel, bind] at h ⊢
    obtain ⟨a, ha, b, hb, rfl⟩ := h; exact ⟨a, ih1 ha, b, ih2 hb, rfl⟩
  | imax _ _ ih1 ih2 =>
    intro _ h; simp [VLevel.ofLevel, bind] at h ⊢
    obtain ⟨a, ha, b, hb, rfl⟩ := h; exact ⟨a, ih1 ha, b, ih2 hb, rfl⟩
  | param n =>
    intro _ h
    simp [VLevel.ofLevel] at h ⊢
    obtain ⟨hlt, rfl⟩ := h
    rw [List.idxOf_append_of_lt hlt]
    exact ⟨by omega, rfl⟩
  | mvar _ => intro _ h; simp [VLevel.ofLevel] at h

/-- The spine form of `VLevel.ofLevel_prefix`, for `TrExprS.const`'s level list. -/
theorem VLevel.mapM_ofLevel_prefix {Us Us' : List Name} (hp : Us <+: Us')
    {us : List Level} {us' : List VLevel}
    (h : us.mapM (VLevel.ofLevel Us) = some us') :
    us.mapM (VLevel.ofLevel Us') = some us' := by
  rw [List.mapM_eq_some] at h ⊢
  exact List.Forall₂.imp (fun _ _ hl => VLevel.ofLevel_prefix hp hl) h

/-- `VLevel.WF` is monotone in the universe-parameter count: it is a conjunction of
`i < n` conditions on the `param` leaves. -/
theorem VLevel.WF.uvars_mono {n m : Nat} (hle : n ≤ m) :
    ∀ {l : VLevel}, l.WF n → l.WF m := by
  intro l
  induction l with
  | zero => exact fun _ => trivial
  | succ _ ih => exact ih
  | max _ _ ih1 ih2 => exact fun h => ⟨ih1 h.1, ih2 h.2⟩
  | imax _ _ ih1 ih2 => exact fun h => ⟨ih1 h.1, ih2 h.2⟩
  | param _ => exact fun h => Nat.lt_of_lt_of_le h hle

/-- **Universe-count monotonicity of the typing judgement.** `IsDefEq`'s `uvars`
parameter is consumed at exactly three constructors — `sortDF`, `constDF` and `extra` —
and in each only as `VLevel.WF uvars`, which `VLevel.WF.uvars_mono` widens. Every other
rule is `uvars`-blind, so the induction is structural.

This is the half of Γ-U1 that has nothing to do with prefixes: it is what carries the
`env.HasType Us.length Δ.toCtx …` side premises of `TrExprS.app`/`lam`/`forallE`/`letE`,
the `TrProj` arm, and the `Erasable` witness of `Erases.box`. -/
theorem VEnv.IsDefEq.uvars_mono {env : VEnv} {U U' : Nat} (hle : U ≤ U')
    {Γ : List VExpr} {e₁ e₂ A : VExpr} (H : env.IsDefEq U Γ e₁ e₂ A) :
    env.IsDefEq U' Γ e₁ e₂ A := by
  induction H with
  | bvar h => exact .bvar h
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | sortDF h1 h2 h3 =>
    exact .sortDF (VLevel.WF.uvars_mono hle h1) (VLevel.WF.uvars_mono hle h2) h3
  | constDF h1 h2 h3 h4 h5 =>
    exact .constDF h1 (fun _ hl => VLevel.WF.uvars_mono hle (h2 _ hl))
      (fun _ hl => VLevel.WF.uvars_mono hle (h3 _ hl)) h4 h5
  | appDF _ _ ih1 ih2 => exact .appDF ih1 ih2
  | lamDF _ _ ih1 ih2 => exact .lamDF ih1 ih2
  | forallEDF _ _ ih1 ih2 => exact .forallEDF ih1 ih2
  | defeqDF _ _ ih1 ih2 => exact .defeqDF ih1 ih2
  | beta _ _ ih1 ih2 => exact .beta ih1 ih2
  | eta _ ih => exact .eta ih
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 h3 => exact .extra h1 (fun _ hl => VLevel.WF.uvars_mono hle (h2 _ hl)) h3
  | pat h1 h2 _ h4 _ ih3 ih5 => exact .pat h1 h2 ih3 h4 ih5

theorem VEnv.HasType.uvars_mono {env : VEnv} {U U' : Nat} (hle : U ≤ U')
    {Γ : List VExpr} {e A : VExpr} (H : env.HasType U Γ e A) : env.HasType U' Γ e A :=
  VEnv.IsDefEq.uvars_mono hle H

theorem VEnv.IsType.uvars_mono {env : VEnv} {U U' : Nat} (hle : U ≤ U')
    {Γ : List VExpr} {A : VExpr} : env.IsType U Γ A → env.IsType U' Γ A
  | ⟨u, h⟩ => ⟨u, VEnv.IsDefEq.uvars_mono hle h⟩

theorem VEnv.IsDefEqU.uvars_mono {env : VEnv} {U U' : Nat} (hle : U ≤ U')
    {Γ : List VExpr} {e₁ e₂ : VExpr} : env.IsDefEqU U Γ e₁ e₂ → env.IsDefEqU U' Γ e₁ e₂
  | ⟨A, h⟩ => ⟨A, VEnv.IsDefEq.uvars_mono hle h⟩

/-- `TrProj` is a pattern lookup plus two typing derivations; the pattern is
`uvars`-free, so the whole predicate is monotone in the count. -/
theorem TrProj.uvars_mono {env : VEnv} {U U' : Nat} (hle : U ≤ U') {Γ : List VExpr}
    {S : Name} {i : Nat} {e e' : VExpr} (H : TrProj env U Γ S i e e') :
    TrProj env U' Γ S i e e' := by
  obtain ⟨recName, ctorName, us, params, fieldTys, np, structTy, fieldTy, r,
    h1, h2, h3, h4, h5, h6, h7⟩ := H
  exact ⟨recName, ctorName, us, params, fieldTys, np, structTy, fieldTy, r,
    h1, h2, h3, h4, VEnv.HasType.uvars_mono hle h5, h6, VEnv.HasType.uvars_mono hle h7⟩

/-- **The Γ-U1 lemma, strict.** A `TrExprS` derivation at a level scope `Us` is a
`TrExprS` derivation — same source, same `VExpr`, no `≈` residue — at any right
extension `Us'` of it.

Compare `TrExprS.instL` (upstream), which lands in `TrExpr`: level *substitution*
re-derives sort and const levels only up to equivalence, so the strict relation is not
preserved. A prefix *extension* substitutes nothing; it only makes more names resolvable,
and leaves the resolution of the old ones untouched (`VLevel.ofLevel_prefix`). The local
context `Δ` is untouched and unconstrained — `Us` and `Δ` are orthogonal parameters, and
`Δ.toCtx` does not mention `Us` — so no `VLCtx.WF`, `env.Ordered` or closedness premise is
needed anywhere. -/
theorem TrExprS.prefix_weaken {env : VEnv} {Us Us' : List Name} (hp : Us <+: Us')
    {Δ : VLCtx} {e : Expr} {e' : VExpr} (H : TrExprS env Us Δ e e') :
    TrExprS env Us' Δ e e' := by
  have hle : Us.length ≤ Us'.length := hp.length_le
  induction H with
  | bvar h => exact .bvar h
  | fvar h => exact .fvar h
  | sort h => exact .sort (VLevel.ofLevel_prefix hp h)
  | const h1 h2 h3 => exact .const h1 (VLevel.mapM_ofLevel_prefix hp h2) h3
  | app h1 h2 _ _ ih1 ih2 =>
    exact .app (VEnv.HasType.uvars_mono hle h1) (VEnv.HasType.uvars_mono hle h2) ih1 ih2
  | lam h1 _ _ ih1 ih2 => exact .lam (VEnv.IsType.uvars_mono hle h1) ih1 ih2
  | forallE h1 h2 _ _ ih1 ih2 =>
    exact .forallE (VEnv.IsType.uvars_mono hle h1) (VEnv.IsType.uvars_mono hle h2) ih1 ih2
  | letE h1 _ _ _ ih1 ih2 ih3 => exact .letE (VEnv.HasType.uvars_mono hle h1) ih1 ih2 ih3
  | lit h1 _ ih => exact .lit h1 ih
  | mdata _ ih => exact .mdata ih
  | proj _ h2 ih => exact .proj ih (TrProj.uvars_mono hle h2)

/-- The defeq-loose companion, free from the strict one: `TrExpr`'s residual
`IsDefEqU` travels by universe-count monotonicity. Stated for the case where an upstream
`instL` has already been applied and only a `TrExpr` survives; **Γ-U2 turned out not to
need it** — it relaxed the four pins with no proof repair — and Γ-U3 removed the residue it
was written for on the `max`/`imax`-free fragment, so at HEAD it has no consumer. Kept
because it is free from the strict lemma and is the statement any *loose* transport wants. -/
theorem TrExpr.prefix_weaken {env : VEnv} {Us Us' : List Name} (hp : Us <+: Us')
    {Δ : VLCtx} {e : Expr} {e' : VExpr} : TrExpr env Us Δ e e' → TrExpr env Us' Δ e e'
  | ⟨e₂, h1, h2⟩ =>
    ⟨e₂, TrExprS.prefix_weaken hp h1, VEnv.IsDefEqU.uvars_mono hp.length_le h2⟩

end Lean4Lean

namespace LeanToLambdaBox

open Lean Lean4Lean

/-- `IsArityUpTo` is a defeq to a syntactic arity; the arity is `uvars`-free. -/
theorem IsArityUpTo.uvars_mono {env : VEnv} {U U' : Nat} (hle : U ≤ U')
    {Γ : List VExpr} {A : VExpr} : IsArityUpTo env U Γ A → IsArityUpTo env U' Γ A
  | ⟨A', hd, har⟩ => ⟨A', VEnv.IsDefEqU.uvars_mono hle hd, har⟩

/-- **The box arm's obligation, discharged.** `Erasable` is monotone in the
universe-parameter count.

The Γ-U plan flagged this as the place a `VExpr`-side wall might live — `Erases.box`
records `Erasable env Us.length Δ.toCtx ve` at the level *count*, and the plan asked
whether widening it needs an environment-side lift. It does not. Unfolded, `Erasable` is
a `HasType` plus a `HasType`-or-`IsArityUpTo` disjunct; each is `IsDefEq` at `U`, and
`IsDefEq.uvars_mono` widens all three. No `env.WF`, no `OnCtx`, no lift. -/
theorem Erasable.uvars_mono {env : VEnv} {U U' : Nat} (hle : U ≤ U')
    {Γ : List VExpr} {e : VExpr} : Erasable env U Γ e → Erasable env U' Γ e
  | ⟨A, hA, h⟩ =>
    ⟨A, VEnv.HasType.uvars_mono hle hA,
      h.imp (VEnv.HasType.uvars_mono hle) (IsArityUpTo.uvars_mono hle)⟩

/-- **Erasure weakens along a prefix extension of the level scope.**

`Erases env Us Γ Δ e t` mentions `Us` at exactly three constructors — `box`'s
`TrExprS` + `Erasable`, and `lam`/`letE`'s binder `TrExprS` — and the target `t` never
mentions it at all (Γ-U analysis, finding (a)). Every one of those three transports
strictly along `Us <+: Us'`, so the derivation moves on the nose: same source, same
target, same `VExpr` witnesses. `Γ`, `Δ` and the target are untouched, and there are no
side conditions.

This is *not* `Erases.instL`, which the Γ-U analysis identified as the wall (Γ-U3):
level substitution was expected to hand `box`/`lam`/`letE` a `TrExpr` where those arms
record strict `TrExprS`. A prefix extension substitutes nothing, so that strictness costs
nothing here. [**Corrected at slice Γ-U3, 2026-08-28**, as the same paragraph in
`DeltaHyps` is: substitution is loose only because `Level.substParams'` **normalises**, so
on the `max`/`imax`-free fragment `TrExprS.instL_strict` lands in `TrExprS` after all and
`Erases.instL` exists. The two lemmas are still different — this one has no fragment
condition and no recursive-arm restriction — but "the wall" is now history.] -/
theorem Erases.prefix_weaken {env : VEnv} {Us Us' : List Name} (hp : Us <+: Us')
    {Γ : ErasureCtx} {Δ : VLCtx} {e : Expr} {t : LBTerm}
    (H : Erases env Us Γ Δ e t) : Erases env Us' Γ Δ e t := by
  have hle : Us.length ≤ Us'.length := hp.length_le
  induction H with
  | box htr her =>
    exact .box (TrExprS.prefix_weaken hp htr) (Erasable.uvars_mono hle her)
  | lit hcl _ ih => exact .lit hcl ih
  | proj S i iid np nf hs hnfs hi _ ihd => exact .proj S i iid np nf hs hnfs hi ihd
  | bvar i => exact .bvar i
  | fvar x => exact .fvar x
  | const n us kn h hctor hcases => exact .const n us kn h hctor hcases
  | app _ _ ihf iha => exact .app ihf iha
  | lam hty _ ihb => exact .lam (TrExprS.prefix_weaken hp hty) ihb
  | letE hty hval _ _ ihv ihb =>
    exact .letE (TrExprS.prefix_weaken hp hty) (TrExprS.prefix_weaken hp hval) ihv ihb
  | ctor cn us iid cidx hc hlen _ ihargs => exact .ctor cn us iid cidx hc hlen ihargs
  | ctor_head cn us iid cidx hc => exact .ctor_head cn us iid cidx hc
  | cases con us iid numParams pre hc hpre hnfs _ hlen hnlen harity _ ihd ihalts =>
    exact .cases con us iid numParams pre hc hpre hnfs ihd hlen hnlen harity ihalts
  | fixvar nm us x hfx hctor hcases hfresh => exact .fixvar nm us x hfx hctor hcases hfresh
  | const_fix nm us hrec hctor hcases hshift hsubst htobv =>
    exact .const_fix nm us hrec hctor hcases hshift hsubst htobv
  | fix idx hidx hnlen hslen hsrc hreg hrarg hlift hinst habsl hshift hsubst htobv
      _ ihb =>
    exact .fix idx hidx hnlen hslen hsrc hreg hrarg hlift hinst habsl hshift hsubst htobv
      ihb

/-! ### Guards

The positive one exhibits index stability on a concrete scope extension; the negative
ones show the prefix hypothesis is not slack — a *permutation* has the same parameter set
and the same length, and still moves the index. -/

/-- The fixture's scope extension: `[u]` is a prefix of `[u, v]`. -/
theorem guard_uv_prefix : ([`u] : List Name) <+: [`u, `v] := ⟨[`v], rfl⟩

/-- Guard (positive, the level layer): the parameter `u` resolves to `VLevel.param 0` at
`[u]` and to the **same** `VLevel.param 0` at `[u, v]`. -/
theorem ofLevel_prefix_index_stable :
    VLevel.ofLevel [`u] (.param `u) = some (.param 0) ∧
      VLevel.ofLevel [`u, `v] (.param `u) = some (.param 0) := ⟨rfl, rfl⟩

/-- Guard (positive, the `TrExprS` layer): a sort translated at `Us = [u]` is a
`TrExprS` — not merely a `TrExpr` — at `Us' = [u, v]`, at the same `VExpr`, over an
arbitrary environment and local context. -/
theorem trExprS_sort_prefix_weaken_guard (env : VEnv) (Δ : VLCtx) :
    TrExprS env [`u, `v] Δ (.sort (.param `u)) (.sort (.param 0)) :=
  TrExprS.prefix_weaken guard_uv_prefix (.sort ofLevel_prefix_index_stable.1)

/-- Guard (positive, the `Erases` layer): the binder type of a `lam` arm is a strict
`TrExprS` premise, and the whole derivation travels. Constructed at an arbitrary `env`
and `Γ`, so the guard is about the level scope and nothing else. -/
theorem erases_lam_prefix_weaken_guard (env : VEnv) (Γ : ErasureCtx) (nm : Name)
    (bi : BinderInfo) :
    Erases env [`u, `v] Γ [] (.lam nm (.sort (.param `u)) (.bvar 0) bi)
      (.lambda (nameToBinder nm) (.bvar 0)) :=
  Erases.prefix_weaken guard_uv_prefix
    (.lam (ty' := .sort (.param 0)) (.sort ofLevel_prefix_index_stable.1) (.bvar 0))

/-- Guard (negative): a permutation of the level scope **moves the index**. `u` sits at
position `0` in `[u, v]` and at position `1` in `[v, u]`, so the `VLevel` produced is a
different one. This is the concrete reason `VLevel.ofLevel_prefix` is stated for prefixes
and not for "any scope containing the same names". -/
theorem ofLevel_perm_index_shifts :
    VLevel.ofLevel [`u, `v] (.param `u) = some (.param 0) ∧
      VLevel.ofLevel [`v, `u] (.param `u) = some (.param 1) := ⟨rfl, rfl⟩

/-- Guard (negative, the refutation): the prefix hypothesis of `VLevel.ofLevel_prefix`
cannot be weakened to `List.Perm`, even though a permutation preserves both the
parameter set and the scope length. -/
theorem not_ofLevel_weaken_of_perm :
    ¬ ∀ (Us Us' : List Name), Us.Perm Us' →
        ∀ {l : Level} {l' : VLevel},
          VLevel.ofLevel Us l = some l' → VLevel.ofLevel Us' l = some l' := by
  intro H
  have h := H [`u, `v] [`v, `u] (List.Perm.swap _ _ []) ofLevel_perm_index_shifts.1
  rw [ofLevel_perm_index_shifts.2] at h
  simp at h

/-- Guard (negative, the `TrExprS` layer): the same shift refutes a permutation-indexed
`TrExprS.prefix_weaken`, at *every* environment. `TrExprS.sort` pins the `VLevel` on the
nose, so a scope permutation cannot preserve the *strict* relation at a fixed target —
which is exactly the failure mode `TrExprS.instL` exhibits generally and the prefix form
escapes. -/
theorem not_trExprS_weaken_of_perm (env : VEnv) :
    ¬ ∀ (Us Us' : List Name), Us.Perm Us' →
        ∀ {Δ : VLCtx} {e : Expr} {e' : VExpr},
          TrExprS env Us Δ e e' → TrExprS env Us' Δ e e' := by
  intro H
  have h := H [`u, `v] [`v, `u] (List.Perm.swap _ _ [])
    (Δ := []) (.sort ofLevel_perm_index_shifts.1)
  cases h with
  | sort h => rw [ofLevel_perm_index_shifts.2] at h; simp at h

end LeanToLambdaBox
