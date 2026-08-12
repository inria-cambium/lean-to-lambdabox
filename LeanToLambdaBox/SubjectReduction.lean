import LeanToLambdaBox.SourceEval
import LeanToLambdaBox.Erasability
import Lean4Lean.Verify.Typing.Expr
import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Theory.Typing.UniqueTyping
import Lean4Lean.Theory.Typing.Injectivity

/-!
# Subject reduction as definitional equality (β fragment) — step A3.3

This file proves the gating lemma for erasure correctness on the pure β
fragment: if a source `Expr` `e` translates to a `VExpr` `ve` (`TrExprS`) and `e`
big-step evaluates to a value `v` (under the β-only relation `SEvalβ`), then `v`
also translates to *some* `vve`, and `ve` is definitionally equal to `vve`.

The β case is the heart: inverting the redex translation gives translations of
the function and argument; the IH on the function evaluation gives a translated
λ defeq to `f'`; the IH on the argument gives the value's translation; and
`TrExprS.inst` + lean4lean's `IsDefEq` β-rule (`IsDefEq.beta`) + congruence
(`appDF`) + transitivity assemble the defeq, with the lambda-domain alignment
discharged by type uniqueness (`IsDefEq.uniqU` + `IsDefEqU.forallE_inv`).

We work with the β-only fragment `SEvalβ` (λ-abstractions are values; β-redexes
reduce). The full `SEval`'s `zeta`/`delta`/`ctor_val` cases are out of scope here
(`delta` would need source-env ↔ `VEnv` consistency); the priority is a complete,
sorry-free β-fragment result.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-- Weak call-by-value big-step evaluation, **β fragment only** (λ-values + β).
The pure functional core on which we prove subject-reduction-as-defeq. -/
inductive SEvalβ (E : SEnv) : Expr → Expr → Prop
  /-- λ-abstractions are values. -/
  | lam (n : Name) (ty b : Expr) (bi : BinderInfo) :
      SEvalβ E (.lam n ty b bi) (.lam n ty b bi)
  /-- β: function evaluates to a λ, argument to a value, then the substituted body. -/
  | beta {f a : Expr} {n : Name} {ty b : Expr} {bi : BinderInfo} {av r : Expr} :
      SEvalβ E f (.lam n ty b bi) → SEvalβ E a av →
      SEvalβ E (b.instantiate1' av 0) r →
      SEvalβ E (.app f a) r

/-- **Subject reduction as definitional equality (β fragment).**

If `e` translates to `ve` and `e` β-evaluates to `v`, then `v` translates to some
`vve` definitionally equal to `ve`.

Requires `env.WF` and `VLCtx.WF` of the translation context (to invoke type
uniqueness / well-formedness of the translated subterms). -/
theorem SEvalβ_defeq {env : VEnv} (henv : env.WF) {Us : List Name} {Δ : VLCtx}
    (hΔ : VLCtx.WF env Us.length Δ) {Esrc : SEnv} {e v : Expr} {ve : VExpr}
    (htr : TrExprS env Us Δ e ve)
    (hev : SEvalβ Esrc e v) :
    ∃ vve, TrExprS env Us Δ v vve ∧ env.IsDefEqU Us.length Δ.toCtx ve vve := by
  induction hev generalizing ve with
  | lam n ty b bi =>
      exact ⟨ve, htr, VEnv.IsDefEqU.refl (htr.wf henv.ordered hΔ)⟩
  | @beta f a n ty b bi av r hf ha hbody ihf iha ihbody =>
      -- Invert the redex translation: ve = .app f' a', with the typing premises.
      cases htr with
      | @app f' A B a' _Δ _f _a hTf hTa htrf htra =>
        -- IH on the function: f' is defeq to a translated λ.
        obtain ⟨fv, htrfv, hfd⟩ := ihf htrf
        cases htrfv with
        | @lam ty' _Δ _ty _body body' _name _bi hty' htrty htrb =>
          -- IH on the argument: a' is defeq to the translated value av_v.
          obtain ⟨av_v, htrav, had⟩ := iha htra
          -- The translation context for the body and its OnCtx form.
          have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
          -- Body type B'' from well-formedness of htrb (under the extended context).
          have hΔ' : VLCtx.WF env Us.length ((none, .vlam ty') :: Δ) := ⟨hΔ, nofun, hty'⟩
          obtain ⟨B'', hbodyT⟩ := htrb.wf henv.ordered hΔ'
          -- (lambda-domain bookkeeping below)
          -- The lambda has its own forallE type `.forallE ty' B''`.
          obtain ⟨u, hty'sort⟩ := hty'
          have lamT1 : env.HasType Us.length Δ.toCtx (.lam ty' body') (.forallE ty' B'') :=
            VEnv.HasType.lam hty'sort hbodyT
          -- … and also type `.forallE A B`, transported from f' via hfd.
          have lamT2 : env.HasType Us.length Δ.toCtx (.lam ty' body') (.forallE A B) :=
            hTf.defeqU_l henv hΓ hfd
          -- Type uniqueness ⟹ the two forallE types are defeq ⟹ A ≡ ty'.
          have huForall : env.IsDefEqU Us.length Δ.toCtx (.forallE A B) (.forallE ty' B'') :=
            VEnv.IsDefEq.uniqU henv hΓ lamT2 lamT1
          obtain ⟨⟨w, hAty'⟩, _⟩ := VEnv.IsDefEqU.forallE_inv henv hΓ huForall
          -- av_v has type A; coerce it to ty'.
          have hadT : env.IsDefEq Us.length Δ.toCtx a' av_v A :=
            VEnv.IsDefEqU.of_l henv hΓ had hTa
          have havT : env.HasType Us.length Δ.toCtx av_v ty' :=
            (hadT.hasType.2).defeqU_r henv hΓ ⟨_, hAty'⟩
          -- The body substituted translates, via TrExprS.inst.
          have htrbody : TrExprS env Us Δ (b.instantiate1' av) (body'.inst av_v) :=
            TrExprS.inst henv.ordered havT htrb htrav
          -- IH on the body evaluation gives the result translation + defeq.
          obtain ⟨vve, htrr, hrd⟩ := ihbody htrbody
          refine ⟨vve, htrr, ?_⟩
          -- Assemble: .app f' a' ≡ .app (.lam ty' body') av_v ≡ body'.inst av_v ≡ vve.
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

/-! ### Inversion of `Erases` on `.lam`/`.app` sources.

`Erases`'s `ctor`/`cases` rules index the source by an application *spine*
(`args.foldl Expr.app …`). To invert `Erases` on a literal `.lam`/`.app` we must
refute (resp. classify) those spine cases. We induct on the derivation (so the
spine equation is available) and use the shape lemma below. -/

/-- An application spine `args.foldl Expr.app head` is either `head` itself
(empty spine) or syntactically an `.app`. -/
theorem foldl_app_eq_or_isApp (head : Expr) :
    ∀ (args : List Expr),
      args.foldl Expr.app head = head ∨ (args.foldl Expr.app head).isApp = true
  | [] => .inl rfl
  | x :: xs => by
      simp only [List.foldl]
      rcases foldl_app_eq_or_isApp (head.app x) xs with h | h
      · exact .inr (by rw [h]; rfl)
      · exact .inr h

/-- A `.const`-headed spine is never a `.lam`. -/
theorem foldl_app_const_ne_lam {cn : Name} {us : List Level} {args : List Expr}
    {n : Name} {ty b : Expr} {bi : BinderInfo} :
    args.foldl Expr.app (.const cn us) ≠ .lam n ty b bi := by
  intro heq
  rcases foldl_app_eq_or_isApp (.const cn us) args with h | h
  · rw [heq] at h; simp at h
  · rw [heq] at h; simp [Expr.isApp] at h

/-- A spine `(discr :: minors).foldl Expr.app pre` is never a `.lam`
(it is a non-empty application spine). -/
theorem foldl_app_cons_ne_lam {pre : Expr} {discr : Expr} {minors : List Expr}
    {n : Name} {ty b : Expr} {bi : BinderInfo} :
    (discr :: minors).foldl Expr.app pre ≠ .lam n ty b bi := by
  intro heq
  simp only [List.foldl] at heq
  rcases foldl_app_eq_or_isApp (pre.app discr) minors with h | h
  · rw [heq] at h; simp at h
  · rw [heq] at h; simp [Expr.isApp] at h

/-- A `.const`-headed spine is never a `.lit`. -/
theorem foldl_app_const_ne_lit {cn : Name} {us : List Level} {args : List Expr}
    {l : Literal} :
    args.foldl Expr.app (.const cn us) ≠ .lit l := by
  intro heq
  rcases foldl_app_eq_or_isApp (.const cn us) args with h | h
  · rw [heq] at h; simp at h
  · rw [heq] at h; simp [Expr.isApp] at h

/-- A spine `(discr :: minors).foldl Expr.app pre` is never a `.lit`
(it is a non-empty application spine). -/
theorem foldl_app_cons_ne_lit {pre : Expr} {discr : Expr} {minors : List Expr}
    {l : Literal} :
    (discr :: minors).foldl Expr.app pre ≠ .lit l := by
  intro heq
  simp only [List.foldl] at heq
  rcases foldl_app_eq_or_isApp (pre.app discr) minors with h | h
  · rw [heq] at h; simp at h
  · rw [heq] at h; simp [Expr.isApp] at h

/-- **Inversion of `Erases` on a `.lit` source.** Only `box` and `lit` apply: the
`ctor`/`cases` rules need a `.const`-headed spine and `fix` a `.lam`. Sibling of
`Erases.const_inv`; the `lit` disjunct hands back the unfolding's erasure, which is what
turns the simulation's literal case into a plain appeal to the IH. -/
theorem Erases.lit_inv {env : VEnv} {Us : List Name} {Γ : ErasureCtx} {Δ : VLCtx}
    {l : Literal} {t : LBTerm} (h : Erases env Us Γ Δ (.lit l) t) :
    (∃ ve, TrExprS env Us Δ (.lit l) ve ∧
        Erasable env Us.length Δ.toCtx ve ∧ t = .box) ∨
    (env.ContainsLits l ∧ Erases env Us Γ Δ l.toConstructor t) := by
  generalize he : (Expr.lit l) = e₀ at h
  induction h with
  | box htr' her' => subst he; exact .inl ⟨_, htr', her', rfl⟩
  | lit hcl hC _ => cases he; exact .inr ⟨hcl, hC⟩
  | ctor cn us _ _ _ _ _ => exact absurd he.symm foldl_app_const_ne_lit
  | cases _ _ _ _ _ _ _ _ _ => exact absurd he.symm foldl_app_cons_ne_lit
  | _ => exact absurd he (by simp)

/-- **Inversion of `Erases` on a `.lam` source.** The `box` and `lam` rules apply, and
— since `Erases.fix`'s source is a syntactic `.lam` (P3) — the environment-level `fix`
rule too, giving a third disjunct `t = .fix defs idx`. This is the **only** inversion
that widens for `Erases.fix`: every other inversion's catch-all refutes a `.lam`-headed
source by head mismatch (`.app`/`.letE`/`.const`/spine ≠ `.lam`). Since the recursion
wall's slice W2 the forward simulations *handle* that disjunct rather than discharge it:
at a λ-value the target block is already a value (`WcbvEval.fix_atom`), and at a β-redex
head it is unfolded by `Erases.fix_unfold`/`erases_lam_head_step` (`ErasesCorrect`). -/
theorem Erases.lam_inv {env : VEnv} {Us : List Name} {Γ : ErasureCtx} {Δ : VLCtx}
    {n : Name} {ty b : Expr} {bi : BinderInfo} {t : LBTerm}
    (h : Erases env Us Γ Δ (.lam n ty b bi) t) :
    (∃ ve, TrExprS env Us Δ (.lam n ty b bi) ve ∧
        Erasable env Us.length Δ.toCtx ve ∧ t = .box) ∨
    (∃ ty' b', TrExprS env Us Δ ty ty' ∧
        Erases env Us Γ ((none, .vlam ty') :: Δ) b b' ∧
        t = .lambda (nameToBinder n) b') ∨
    (∃ (defs : List (@FixDef LBTerm)) (idx : Nat), t = .fix defs idx ∧
        Erases env Us Γ Δ (.lam n ty b bi) (.fix defs idx)) := by
  generalize he : (Expr.lam n ty b bi) = e₀ at h
  induction h with
  | box htr' her' => subst he; exact .inl ⟨_, htr', her', rfl⟩
  | lam hty hb => cases he; exact .inr (.inl ⟨_, _, hty, hb, rfl⟩)
  | ctor cn us _ _ _ _ _ => exact absurd he.symm foldl_app_const_ne_lam
  | cases _ _ _ _ _ _ _ _ _ => exact absurd he.symm foldl_app_cons_ne_lam
  | @fix Δc idx nm tty tb tbi nms srcs defs hidx hnlen hslen hsrc hreg hrarg
      hlift hinst habsl hshift hsubst htobv hbodies _ihb =>
      cases he
      exact .inr (.inr ⟨defs, idx, rfl,
        .fix idx hidx hnlen hslen hsrc hreg hrarg hlift hinst habsl hshift hsubst htobv
          hbodies⟩)
  | _ => exact absurd he (by simp)

/-- **Inversion of `Erases` on a `.lam` source at a `.fix` target** — `lam_inv`'s third
disjunct with the rule's premises *kept* (`lam_inv` hands back only the derivation). Only
`Erases.fix` can conclude a `.fix` target from a `.lam` source, so the inversion is total,
and it hands out exactly the three things a consumer of a recursive erasure wants:

* the block is non-degenerate at `idx` (`hidx`);
* every def's `principalArgIdx` is `0`, which is what makes one source β-step match one
  target `fix_guarded` + one `beta` (see the rule's docstring);
* **the source body erases to `defs[idx]`'s one-step unfolding**, at any context — i.e.
  `WcbvEval.fix_guarded`'s reduct is again an erasure of the same source. That is the
  statement the β case of the forward simulations needs, and it is available precisely
  because the re-founded rule states its bodies premise in unfolded form.

Plus the registration witness, which is what refutes a `.fix` erasure at a `Γ` that
records no recursion. -/
theorem Erases.fix_inv {env : VEnv} {Us : List Name} {Γ : ErasureCtx} {Δ : VLCtx}
    {n : Name} {ty b : Expr} {bi : BinderInfo}
    {defs : List (@FixDef LBTerm)} {idx : Nat}
    (h : Erases env Us Γ Δ (.lam n ty b bi) (.fix defs idx)) :
    ∃ hidx : idx < defs.length,
      (∀ d ∈ defs, d.principalArgIdx = 0) ∧
      (∃ nm : Name, Γ.recBodies nm = some (defs, idx)) ∧
      ∀ Δf : VLCtx, Erases env Us Γ Δf (.lam n ty b bi)
        (LBTerm.substList (LBTerm.fixSubst defs) (defs[idx]'hidx).body) := by
  generalize he : (Expr.lam n ty b bi) = e₀ at h
  generalize ht : (LBTerm.fix defs idx) = t₀ at h
  induction h with
  | @fix _ idx' _ _ _ _ nms srcs defs' hidx hnlen hslen hsrc hreg hrarg
      _ _ _ _ _ _ hbodies _ =>
      cases he
      injection ht with hdefs hidx'
      subst hdefs; subst hidx'
      exact ⟨hidx, hrarg, ⟨_, hreg _ hidx⟩, fun Δf => hsrc ▸ hbodies _ hidx Δf⟩
  | box _ _ => exact absurd ht (by simp)
  | lam _ _ _ => exact absurd ht (by simp)
  | ctor cn us _ _ _ _ _ => exact absurd he.symm foldl_app_const_ne_lam
  | cases _ _ _ _ _ _ _ _ _ => exact absurd he.symm foldl_app_cons_ne_lam
  | _ => exact absurd he (by simp)

/-- A `.const`-headed spine never reduces to a `.lam` under `SEvalβ`
(the head stays a `.const`; `SEvalβ` only produces a `.lam` from a `.lam`). This
rules out the `ctor` erasure of a β-redex in `erases_correct_beta`. -/
theorem SEvalβ_const_spine_elim {E : SEnv} {e r : Expr} (hev : SEvalβ E e r) :
    ∀ {cn : Name} {us : List Level} {args : List Expr},
      e ≠ args.foldl Expr.app (.const cn us) := by
  induction hev with
  | lam n ty b bi =>
      intro cn us args; exact (foldl_app_const_ne_lam (args := args)).symm
  | @beta f a n ty b bi av r hf ha hbody ihf iha ihbody =>
      intro cn us args h
      -- `.app f a = foldl .. const args` forces `args = init ++ [a]`, `f = foldl .. init`.
      rcases List.eq_nil_or_concat args with rfl | ⟨init, last, hcat⟩
      · exact absurd h (by simp)
      · rw [hcat] at h
        simp only [List.concat_eq_append, List.foldl_append, List.foldl] at h
        injection h with hf_eq ha_eq
        exact ihf hf_eq

/-- **Inversion of `Erases` on an `.app` source.** Either the application is
irrelevant (`box`), erased structurally (`app`), or it is (syntactically) a
`.const`-headed application spine — the latter covering the `ctor`/`cases` rules,
whose heads are `.const`s. In the pure-β setting the spine case is excluded by
`SEvalβ_const_spine_elim`. -/
theorem Erases.app_inv {env : VEnv} {Us : List Name} {Γ : ErasureCtx} {Δ : VLCtx}
    {f a : Expr} {t : LBTerm}
    (h : Erases env Us Γ Δ (.app f a) t) :
    (∃ ve, TrExprS env Us Δ (.app f a) ve ∧
        Erasable env Us.length Δ.toCtx ve ∧ t = .box) ∨
    (∃ f' a', Erases env Us Γ Δ f f' ∧ Erases env Us Γ Δ a a' ∧ t = .app f' a') ∨
    (∃ (cn : Name) (us : List Level) (args : List Expr),
        Expr.app f a = args.foldl Expr.app (.const cn us) ∧
        (Γ.ctors cn ≠ none ∨ Γ.casesOns cn ≠ none)) := by
  generalize he : (Expr.app f a) = e₀ at h
  induction h with
  | box htr' her' => subst he; exact .inl ⟨_, htr', her', rfl⟩
  | app hf ha => cases he; exact .inr (.inl ⟨_, _, hf, ha, rfl⟩)
  | @ctor _ cn us _ _ args _ hc _ _ _ =>
      exact .inr (.inr ⟨cn, us, args, rfl, .inl (by rw [hc]; simp)⟩)
  | @cases _ con us _ numParams pre discr _ minors _ _ hc _ _ _ _ _ _ =>
      exact .inr (.inr ⟨con, us, pre ++ discr :: minors, (List.foldl_append ..).symm,
        .inr (by rw [hc]; simp)⟩)
  | _ => exact absurd he (by simp)

/-! ### Inversion of `Erases` on `.letE`/`.const` sources (for ζ/δ correctness). -/

/-- A `.const`-headed spine is never a `.letE`. -/
theorem foldl_app_const_ne_letE {cn : Name} {us : List Level} {args : List Expr}
    {n : Name} {ty val b : Expr} {nd : Bool} :
    args.foldl Expr.app (.const cn us) ≠ .letE n ty val b nd := by
  intro heq
  rcases foldl_app_eq_or_isApp (.const cn us) args with h | h
  · rw [heq] at h; simp at h
  · rw [heq] at h; simp [Expr.isApp] at h

/-- A non-empty spine `(discr :: minors).foldl Expr.app pre` is never a `.letE`. -/
theorem foldl_app_cons_ne_letE {pre : Expr} {discr : Expr} {minors : List Expr}
    {n : Name} {ty val b : Expr} {nd : Bool} :
    (discr :: minors).foldl Expr.app pre ≠ .letE n ty val b nd := by
  intro heq
  simp only [List.foldl] at heq
  rcases foldl_app_eq_or_isApp (pre.app discr) minors with h | h
  · rw [heq] at h; simp at h
  · rw [heq] at h; simp [Expr.isApp] at h

/-- **Inversion of `Erases` on a `.letE` source.** Only `box` and `letE` apply. -/
theorem Erases.letE_inv {env : VEnv} {Us : List Name} {Γ : ErasureCtx} {Δ : VLCtx}
    {n : Name} {ty val b : Expr} {nd : Bool} {t : LBTerm}
    (h : Erases env Us Γ Δ (.letE n ty val b nd) t) :
    (∃ ve, TrExprS env Us Δ (.letE n ty val b nd) ve ∧
        Erasable env Us.length Δ.toCtx ve ∧ t = .box) ∨
    (∃ (ty' val' : VExpr) (v' b' : LBTerm),
        TrExprS env Us Δ ty ty' ∧ TrExprS env Us Δ val val' ∧
        Erases env Us Γ Δ val v' ∧
        Erases env Us Γ ((none, .vlet ty' val') :: Δ) b b' ∧
        t = .letIn (nameToBinder n) v' b') := by
  generalize he : (Expr.letE n ty val b nd) = e₀ at h
  induction h with
  | box htr' her' => subst he; exact .inl ⟨_, htr', her', rfl⟩
  | letE hty hval hv hb => cases he; exact .inr ⟨_, _, _, _, hty, hval, hv, hb, rfl⟩
  | ctor cn us _ _ _ _ _ => exact absurd he.symm foldl_app_const_ne_letE
  | cases _ _ _ _ _ _ _ _ _ => exact absurd he.symm foldl_app_cons_ne_letE
  | _ => exact absurd he (by simp)

/-- **Inversion of `Erases` on a `.const` source.** Either irrelevant (`box`),
the `const` rule (`t = .const kn`), a *nullary* `ctor` spine (`args = []`,
`t = .construct iid cidx []`), a **registered recursive constant** standing for its own
block (`t = .fix defs idx`, the recursion wall's `const_fix` leaf), or — since slice
W3.1 — an **in-block sibling** standing for its fixvar (`t = .fvar x`). The `cases` rule
needs a non-empty spine, so it is excluded; a non-nullary `ctor` would make the source an
`.app`, also excluded.

The last two disjuncts are the price of the two recursion leaves, and both are cheap:
the spine inversions kill them with their own `Γ.ctors`/`Γ.casesOns`-disjointness
witnesses (which `const_inv_full` keeps), the δ case of each forward simulation *uses*
`const_fix` — since slice W2, `RecEnvConsistent` turns the recorded block back into the
source body's erasure, and the target's own step is `WcbvEval.fix_atom` — and it kills
`fixvar` with its `hnfv : Γ.fixvars = fun _ => none` premise, since a *top-level*
evaluation never runs inside a block. -/
theorem Erases.const_inv {env : VEnv} {Us : List Name} {Γ : ErasureCtx} {Δ : VLCtx}
    {n : Name} {us : List Level} {t : LBTerm}
    (h : Erases env Us Γ Δ (.const n us) t) :
    (∃ ve, TrExprS env Us Δ (.const n us) ve ∧
        Erasable env Us.length Δ.toCtx ve ∧ t = .box) ∨
    (∃ kn, Γ.constants n = kn ∧ t = .const kn) ∨
    (∃ (iid : InductiveId) (cidx : Nat),
        Γ.ctors n = some (iid, cidx) ∧ t = .construct iid cidx []) ∨
    (∃ (defs : List (@FixDef LBTerm)) (idx : Nat),
        Γ.recBodies n = some (defs, idx) ∧ t = .fix defs idx) ∨
    (∃ x : FVarId, Γ.fixvars n = some x ∧ t = .fvar x) := by
  generalize he : (Expr.const n us) = e₀ at h
  induction h with
  | box htr' her' => subst he; exact .inl ⟨_, htr', her', rfl⟩
  | const m ms kn hkn _ _ => cases he; exact .inr (.inl ⟨_, hkn, rfl⟩)
  | ctor_head cn cus iid cidx hc => cases he; exact .inr (.inr (.inl ⟨iid, cidx, hc, rfl⟩))
  | const_fix m ms hrec _ _ _ _ _ =>
      cases he; exact .inr (.inr (.inr (.inl ⟨_, _, hrec, rfl⟩)))
  | fixvar m ms x hfx _ _ _ =>
      cases he; exact .inr (.inr (.inr (.inr ⟨_, hfx, rfl⟩)))
  | @ctor _ cn cus iid cidx args args' hc hlen _ _ =>
      -- The spine `args.foldl app (.const cn cus) = .const n us` forces `args = []`.
      rcases List.eq_nil_or_concat args with rfl | ⟨init, last, hcat⟩
      · simp only [List.foldl] at he
        cases he
        have hlen' : args'.length = 0 := by simpa using hlen.symm
        have : args' = [] := List.eq_nil_of_length_eq_zero hlen'
        subst this
        exact .inr (.inr (.inl ⟨iid, cidx, hc, rfl⟩))
      · subst hcat
        rw [List.concat_eq_append, List.foldl_append, List.foldl_cons,
          List.foldl_nil] at he
        exact absurd he (by simp)
  | @cases _ con cus _ numParams pre discr _ minors _ _ _ _ _ _ _ =>
      -- The non-empty cons spine is `.app`-shaped, never a `.const`.
      simp only [List.foldl_cons] at he
      rcases foldl_app_eq_or_isApp ((pre.foldl Expr.app (.const con cus)).app discr)
        minors with hh | hh
      · rw [← he] at hh; simp at hh
      · rw [← he] at hh; simp [Expr.isApp] at hh
  | _ => exact absurd he (by simp)

/-- **`hnfv` refutes a bare-fvar erasure of a constant** (recursion wall, W3.1). At a `Γ`
that installs no fixvar map — i.e. anywhere outside `visitMutual`'s block, which is where
every forward simulation lives — no constant erases to an `.fvar`: `Erases.fixvar` is the
only rule that could, and it needs the map. (Even the `box` rule cannot, its target being
`.box`.) This is exactly the refutation the δ case of `erases_correct`,
`erases_correct_data{,_zeta}` and `erases_correct_dataι` performs inline, and it is the
guard that the leaf's registration premise is load-bearing rather than decorative. -/
theorem Erases.const_fvar_elim {env : VEnv} {Us : List Name} {Γ : ErasureCtx} {Δ : VLCtx}
    {n : Name} {us : List Level} {x : FVarId} (hnfv : Γ.fixvars = fun _ => none) :
    ¬ Erases env Us Γ Δ (.const n us) (.fvar x) := by
  intro h
  rcases h.const_inv with ⟨_, _, _, hb⟩ | ⟨_, _, hb⟩ | ⟨_, _, _, hb⟩ | ⟨_, _, _, hb⟩
    | ⟨y, hfx, _⟩
  · exact absurd hb (by simp)
  · exact absurd hb (by simp)
  · exact absurd hb (by simp)
  · exact absurd hb (by simp)
  · rw [hnfv] at hfx; exact absurd hfx (by simp)

end LeanToLambdaBox
