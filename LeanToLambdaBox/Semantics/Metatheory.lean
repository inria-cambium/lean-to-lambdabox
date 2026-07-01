import LeanToLambdaBox.Semantics.Eval

/-!
# Metatheory of `WcbvEval` (target-side, lean4lean-free)

Faithful counterparts of MetaCoq's `EWcbvEval` metatheory. All results here are
pure target-side reasoning about `WcbvEval`/`Value` and **must be `sorryAx`-free**.

| here | MetaCoq |
|---|---|
| `value_final`       | `value_final` (`value v → eval v v`) |
| `eval_to_value`     | `eval_to_value` (`eval t v → value v`) |
| `WcbvEval.deterministic` | `eval_deterministic` |
| `WcbvEval.eval_value`    | `eval_value` |
| `WcbvEval.unique`        | `eval_unique` (free — `Prop`-valued) |
-/

namespace LeanToLambdaBox

open Lean

/-- Values evaluate to themselves. MetaCoq `value_final`. -/
theorem value_final {Γ : GlobalDeclarations} {fl : WcbvFlags} {v : LBTerm} :
    Value fl v → WcbvEval Γ fl v v := by
  intro hv
  induction hv with
  | @atom t h =>
      cases t with
      | box => exact .box
      | lambda n b => exact .lam n b
      | fvar x => exact .fvar x
      | prim p => exact .prim p
      | fix defs i => exact .fix_atom defs i
      | bvar i => simp only [atomValue] at h
      | letIn n v b => simp only [atomValue] at h
      | app f a => simp only [atomValue] at h
      | const kn => simp only [atomValue] at h
      | construct iid k args => simp only [atomValue] at h
      | case info d alts => simp only [atomValue] at h
      | proj p e => simp only [atomValue] at h
  | @construct iid k args hargs ih =>
      exact .construct rfl (fun i hi => ih i hi)
  | @app_stuck f a hf hstuck ha ihf iha =>
      exact .app_cong ihf hstuck iha
  | @fix_stuck hg defs i av ha hnc ih =>
      exact .fix_stuck hg (.fix_atom defs i) ih hnc

/-- Evaluation produces a value. MetaCoq `eval_to_value`. -/
theorem eval_to_value {Γ : GlobalDeclarations} {fl : WcbvFlags} {t v : LBTerm} :
    WcbvEval Γ fl t v → Value fl v := by
  intro h
  induction h with
  | box => exact .atom (by simp [atomValue])
  | lam n b => exact .atom (by simp [atomValue])
  | fvar x => exact .atom (by simp [atomValue])
  | prim p => exact .atom (by simp [atomValue])
  | fix_atom defs i => exact .atom (by simp [atomValue])
  | @beta f a n b av r hf ha hbody ihf iha ihbody => exact ihbody
  | @app_box f a av hf ha ihf iha => exact .atom (by simp [atomValue])
  | @zeta n v b vv r hv hbody ihv ihbody => exact ihbody
  | @delta kn body r hlk hbody ihbody => exact ihbody
  | @construct iid k args vs hl hargs ihargs =>
      refine .construct (fun i hi => ?_)
      exact ihargs i (hl ▸ hi)
  | @construct_app hb f a a' iid c args ar hf harity hlt ha ihf iha =>
      -- result `construct iid c (args ++ [a'])`; args are values (ihf), a' is a value (iha)
      cases ihf with
      | construct hargs =>
          refine .construct (fun i hi => ?_)
          rcases Nat.lt_or_ge i args.length with h | h
          · rw [List.getElem_append_left h]; exact hargs i h
          · have he : i = args.length := by
              rw [List.length_append, List.length_cons, List.length_nil] at hi; omega
            subst he
            rw [List.getElem_append_right (Nat.le_refl _)]
            simpa using iha
      | atom h => exact absurd h (by simp [atomValue])
  | @iota iid np k discr alts cargs names body r hnp hdiscr hsel hbodyev ihd ihbody =>
      exact ihbody
  | @iota_sing hpc iid np discr names body r hp hdiscr hbodyev ihd ihbody =>
      exact ihbody
  | @proj p discr iid k cargs v r hnp hdiscr hsel hvev ihd ihv => exact ihv
  | @proj_prop hpc p discr hp hdiscr ihd => exact .atom (by simp [atomValue])
  | @fix_guarded hg f arg defs i def_i argv r hf hsel harg hctor hunf ihf iharg ihunf =>
      exact ihunf
  | @fix_stuck hg f arg defs i argv hf harg hnc ihf iharg =>
      exact .fix_stuck hg iharg hnc
  | @fix_unguarded hg f arg defs i def_i argv r hf hsel harg hunf ihf iharg ihunf =>
      exact ihunf
  | @app_cong f a f' a' hf hstuck ha ihf iha =>
      exact .app_stuck ihf hstuck iha

/-- **Determinism** of `WcbvEval`. MetaCoq `eval_deterministic`. The `app`-node
    rules are kept mutually exclusive by the value-shape of the evaluated head and
    the `isStuckApp`/`isConstructorValue`/flag guards, so inversion is clean. -/
theorem eval_deterministic {Γ : GlobalDeclarations} {fl : WcbvFlags} {t v : LBTerm}
    (h1 : WcbvEval Γ fl t v) : ∀ {v'}, WcbvEval Γ fl t v' → v = v' := by
  induction h1 with
  | box => intro v' h2; cases h2; rfl
  | lam n b => intro v' h2; cases h2; rfl
  | fvar x => intro v' h2; cases h2; rfl
  | prim p => intro v' h2; cases h2; rfl
  | fix_atom defs i => intro v' h2; cases h2; rfl
  | @beta f a n b av r hf ha hbody ihf iha ihbody =>
      intro v' h2
      cases h2 with
      | beta hf2 ha2 hbody2 =>
          have he := ihf hf2; injection he with _ hb
          have hav := iha ha2
          rw [← hb, ← hav] at hbody2
          exact ihbody hbody2
      | app_box hf2 _ => have he := ihf hf2; simp at he
      | fix_guarded _ hf2 _ _ _ _ => have he := ihf hf2; simp at he
      | fix_stuck _ hf2 _ _ => have he := ihf hf2; simp at he
      | fix_unguarded _ hf2 _ _ _ => have he := ihf hf2; simp at he
      | app_cong hf2 hstuck2 _ => have he := ihf hf2; rw [← he] at hstuck2; simp [isStuckApp] at hstuck2
      | construct_app _ hf2 _ _ _ => have he := ihf hf2; simp at he
  | @app_box f a av hf ha ihf iha =>
      intro v' h2
      cases h2 with
      | beta hf2 _ _ => have he := ihf hf2; simp at he
      | app_box _ _ => rfl
      | fix_guarded _ hf2 _ _ _ _ => have he := ihf hf2; simp at he
      | fix_stuck _ hf2 _ _ => have he := ihf hf2; simp at he
      | fix_unguarded _ hf2 _ _ _ => have he := ihf hf2; simp at he
      | app_cong hf2 hstuck2 _ => have he := ihf hf2; rw [← he] at hstuck2; simp [isStuckApp] at hstuck2
      | construct_app _ hf2 _ _ _ => have he := ihf hf2; simp at he
  | @zeta n v b vv r hv hbody ihv ihbody =>
      intro v' h2
      cases h2 with
      | zeta hv2 hbody2 =>
          have hvv := ihv hv2
          rw [← hvv] at hbody2
          exact ihbody hbody2
  | @delta kn body r hlk hbody ihbody =>
      intro v' h2
      cases h2 with
      | @delta _ body2 _ hlk2 hbody2 =>
          rw [hlk] at hlk2; simp at hlk2; subst hlk2
          exact ihbody hbody2
  | @construct iid k args vs hl hargs ihargs =>
      intro v' h2
      cases h2 with
      | @construct _ _ _ vs2 hl2 hargs2 =>
          congr 1
          apply List.ext_getElem (by omega)
          intro i h_i _
          have hi : i < args.length := by omega
          exact ihargs i hi (hargs2 i hi)
  | @construct_app hb f a a' iid c args ar hf harity hlt ha ihf iha =>
      intro v' h2
      cases h2 with
      | beta hf2 _ _ => have he := ihf hf2; simp at he
      | app_box hf2 _ => have he := ihf hf2; simp at he
      | fix_guarded _ hf2 _ _ _ _ => have he := ihf hf2; simp at he
      | fix_stuck _ hf2 _ _ => have he := ihf hf2; simp at he
      | fix_unguarded _ hf2 _ _ _ => have he := ihf hf2; simp at he
      | app_cong hf2 hstuck2 _ => have he := ihf hf2; rw [← he] at hstuck2; simp [isStuckApp] at hstuck2
      | construct_app _ hf2 _ _ ha2 =>
          have he := ihf hf2
          rw [LBTerm.construct.injEq] at he
          obtain ⟨rfl, rfl, rfl⟩ := he
          rw [iha ha2]
  | @iota iid np k discr alts cargs names body r hnp hdiscr hsel hbodyev ihd ihbody =>
      intro v' h2
      cases h2 with
      | iota hnp2 hdiscr2 hsel2 hbodyev2 =>
          have hc := ihd hdiscr2
          rw [LBTerm.construct.injEq] at hc
          obtain ⟨_, rfl, rfl⟩ := hc
          rw [hsel] at hsel2; injection hsel2 with hnb; injection hnb with _ hbd
          rw [← hbd] at hbodyev2
          exact ihbody hbodyev2
      | iota_sing _ _ hdiscr2 _ => have hc := ihd hdiscr2; simp at hc
  | @iota_sing hpc iid np discr names body r hp hdiscr hbodyev ihd ihbody =>
      intro v' h2
      cases h2 with
      | iota _ hdiscr2 _ _ => have hc := ihd hdiscr2; simp at hc
      | iota_sing _ _ hdiscr2 hbodyev2 => exact ihbody hbodyev2
  | @proj p discr iid k cargs v0 r hnp hdiscr hsel hvev ihd ihv =>
      intro v' h2
      cases h2 with
      | proj hnp2 hdiscr2 hsel2 hvev2 =>
          have hc := ihd hdiscr2
          rw [LBTerm.construct.injEq] at hc
          obtain ⟨_, rfl, rfl⟩ := hc
          rw [hsel] at hsel2; injection hsel2 with hv0
          rw [← hv0] at hvev2
          exact ihv hvev2
      | proj_prop _ _ hdiscr2 => have hc := ihd hdiscr2; simp at hc
  | @proj_prop hpc p discr hp hdiscr ihd =>
      intro v' h2
      cases h2 with
      | proj _ hdiscr2 _ _ => have hc := ihd hdiscr2; simp at hc
      | proj_prop _ _ _ => rfl
  | @fix_guarded hg f arg defs i def_i argv r hf hsel harg hctor hunf ihf iharg ihunf =>
      intro v' h2
      cases h2 with
      | beta hf2 _ _ => have he := ihf hf2; simp at he
      | app_box hf2 _ => have he := ihf hf2; simp at he
      | fix_guarded _ hf2 hsel2 harg2 _ hunf2 =>
          have he := ihf hf2; injection he with hd hi
          subst hd; subst hi
          rw [hsel] at hsel2; injection hsel2 with hdi; subst hdi
          have hav := iharg harg2
          rw [← hav] at hunf2
          exact ihunf hunf2
      | fix_stuck _ hf2 harg2 hnc2 =>
          have hav := iharg harg2; rw [← hav, hctor] at hnc2; simp at hnc2
      | fix_unguarded hg2 _ _ _ _ => rw [hg] at hg2; simp at hg2
      | app_cong hf2 hstuck2 _ => have he := ihf hf2; rw [← he] at hstuck2; simp [isStuckApp] at hstuck2
      | construct_app _ hf2 _ _ _ => have he := ihf hf2; simp at he
  | @fix_stuck hg f arg defs i argv hf harg hnc ihf iharg =>
      intro v' h2
      cases h2 with
      | beta hf2 _ _ => have he := ihf hf2; simp at he
      | app_box hf2 _ => have he := ihf hf2; simp at he
      | fix_guarded _ hf2 _ harg2 hctor2 _ =>
          have hav := iharg harg2; rw [← hav, hnc] at hctor2; simp at hctor2
      | fix_stuck _ hf2 harg2 _ =>
          have he := ihf hf2; have hav := iharg harg2
          rw [← he, ← hav]
      | fix_unguarded hg2 _ _ _ _ => rw [hg] at hg2; simp at hg2
      | app_cong hf2 hstuck2 _ => have he := ihf hf2; rw [← he] at hstuck2; simp [isStuckApp] at hstuck2
      | construct_app _ hf2 _ _ _ => have he := ihf hf2; simp at he
  | @fix_unguarded hg f arg defs i def_i argv r hf hsel harg hunf ihf iharg ihunf =>
      intro v' h2
      cases h2 with
      | beta hf2 _ _ => have he := ihf hf2; simp at he
      | app_box hf2 _ => have he := ihf hf2; simp at he
      | fix_guarded hg2 _ _ _ _ _ => rw [hg] at hg2; simp at hg2
      | fix_stuck hg2 _ _ _ => rw [hg] at hg2; simp at hg2
      | fix_unguarded _ hf2 hsel2 harg2 hunf2 =>
          have he := ihf hf2; injection he with hd hi
          subst hd; subst hi
          rw [hsel] at hsel2; injection hsel2 with hdi; subst hdi
          have hav := iharg harg2
          rw [← hav] at hunf2
          exact ihunf hunf2
      | app_cong hf2 hstuck2 _ => have he := ihf hf2; rw [← he] at hstuck2; simp [isStuckApp] at hstuck2
      | construct_app _ hf2 _ _ _ => have he := ihf hf2; simp at he
  | @app_cong f a f' a' hf hstuck ha ihf iha =>
      intro v' h2
      cases h2 with
      | beta hf2 _ _ => have he := ihf hf2; rw [he] at hstuck; simp [isStuckApp] at hstuck
      | app_box hf2 _ => have he := ihf hf2; rw [he] at hstuck; simp [isStuckApp] at hstuck
      | fix_guarded _ hf2 _ _ _ _ => have he := ihf hf2; rw [he] at hstuck; simp [isStuckApp] at hstuck
      | fix_stuck _ hf2 _ _ => have he := ihf hf2; rw [he] at hstuck; simp [isStuckApp] at hstuck
      | fix_unguarded _ hf2 _ _ _ => have he := ihf hf2; rw [he] at hstuck; simp [isStuckApp] at hstuck
      | app_cong hf2 _ ha2 => rw [ihf hf2, iha ha2]
      | construct_app _ hf2 _ _ _ => have he := ihf hf2; rw [he] at hstuck; simp [isStuckApp] at hstuck

/-- A value has a unique evaluation image. MetaCoq `eval_value`. -/
theorem eval_value {Γ : GlobalDeclarations} {fl : WcbvFlags} {v v' : LBTerm}
    (hv : Value fl v) (h : WcbvEval Γ fl v v') : v = v' :=
  eval_deterministic (value_final hv) h

/-- Derivation irrelevance — free, because `WcbvEval` is `Prop`-valued. MetaCoq
    `eval_unique` (which there needs a `Type`-level argument). -/
theorem eval_unique {Γ : GlobalDeclarations} {fl : WcbvFlags} {t v : LBTerm}
    (h1 h2 : WcbvEval Γ fl t v) : h1 = h2 := rfl

/-! ## Non-vacuity witnesses for the metatheory

Every hypothesis-bearing lemma above (`value_final`, `eval_to_value`,
`eval_deterministic`, `eval_value`, `eval_unique`) is guarded against vacuous
truth: the hypotheses are satisfiable (`WcbvEval`/`Value` are inhabited by a
concrete non-trivial evaluation) and each lemma is shown to *fire* on it,
producing real content. In particular `eval_deterministic_fires` exercises the
β-redex `(λ. #0) □`, whose argument `□` genuinely evaluates — this is exactly the
premise the `app_box` fix restored, without which determinism would fail. -/

/-- A concrete non-trivial evaluation: `(λ. #0) □ ⇓ □`. -/
theorem wcbvEval_beta_box :
    WcbvEval [] optFlags (.app (.lambda .anon (.bvar 0)) .box) .box :=
  .beta (.lam .anon (.bvar 0)) .box .box

theorem value_box : Value optFlags (.box : LBTerm) := .atom (by simp [atomValue])

/-- `Value` is inhabited (⇒ `value_final` is not vacuous). -/
theorem value_final_hyps_satisfiable : ∃ (fl : WcbvFlags) (v : LBTerm), Value fl v :=
  ⟨optFlags, .box, value_box⟩

/-- `value_final` fires: `□` (a value) evaluates to itself. -/
theorem value_final_fires : WcbvEval [] optFlags .box .box := value_final value_box

/-- `WcbvEval` is inhabited (⇒ `eval_to_value`/`eval_deterministic` are not vacuous). -/
theorem eval_hyps_satisfiable :
    ∃ (Γ : GlobalDeclarations) (fl : WcbvFlags) (t v : LBTerm), WcbvEval Γ fl t v :=
  ⟨[], optFlags, _, _, wcbvEval_beta_box⟩

/-- `eval_to_value` fires: the redex's result `□` is a value. -/
theorem eval_to_value_fires : Value optFlags .box := eval_to_value wcbvEval_beta_box

/-- `eval_deterministic` fires on the β-redex `(λ. #0) □` (whose argument evaluates). -/
theorem eval_deterministic_fires : (.box : LBTerm) = .box :=
  eval_deterministic wcbvEval_beta_box wcbvEval_beta_box

/-- `eval_value` fires: the value `□` evaluates only to itself. -/
theorem eval_value_fires : (.box : LBTerm) = .box :=
  eval_value value_box (@WcbvEval.box [] optFlags)

/-- `eval_unique` fires: any two derivations of `□ ⇓ □` are equal. -/
theorem eval_unique_fires (h1 h2 : WcbvEval [] optFlags .box .box) : h1 = h2 :=
  eval_unique h1 h2

/-! ### Non-block (applied) constructors genuinely fire.

`construct_app` is guarded by `with_constructor_as_block = false`, so under the
block-form instances (`optFlags`/`defaultFlags`) it is unreachable. Under
`appliedFlags` it fires: an applied constructor `(.construct iid 0 []) □`
evaluates by accumulating `□` onto the constructor, up to its arity. -/

/-- Witness environment: one non-propositional inductive with a single unary constructor. -/
def acKn : Kername := { mp := .MPfile [], id := "AC" }
def acIid : InductiveId := { mutualBlockName := acKn, idx := 0 }
def acOIB : OneInductiveBody :=
  { name := "AC", propositional := false, kelim := .IntoAny,
    ctors := [{ name := "mk", nargs := 1 }], projs := [] }
def acΓ : GlobalDeclarations :=
  [(acKn, .inductiveDecl { finite := .finite, npars := 0, bodies := [acOIB] })]

theorem ac_arity : constructorArity acΓ acIid 0 = some 1 := rfl

/-- A nullary(-so-far) constructor head is a value. -/
theorem wcbv_construct_nil (Γ : GlobalDeclarations) (fl : WcbvFlags) (iid : InductiveId) (c : Nat) :
    WcbvEval Γ fl (.construct iid c []) (.construct iid c []) :=
  .construct rfl (fun i hi => absurd hi (Nat.not_lt_zero i))

/-- `construct_app` fires: the applied form `(construct AC.mk) □` evaluates to the
    block-form value `construct AC.mk [□]` under `appliedFlags`. -/
theorem construct_app_fires :
    WcbvEval acΓ appliedFlags (.app (.construct acIid 0 []) .box) (.construct acIid 0 [.box]) :=
  .construct_app rfl (wcbv_construct_nil acΓ appliedFlags acIid 0) ac_arity (by decide) .box

/-- The applied-constructor value is a genuine `Value` (via `eval_to_value`). -/
theorem construct_app_value : Value appliedFlags (.construct acIid 0 [.box]) :=
  eval_to_value construct_app_fires

end LeanToLambdaBox
