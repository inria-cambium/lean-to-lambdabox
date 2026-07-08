import LeanToLambdaBox.Semantics.Eval

/-!
# Metatheory of `WcbvEval` (target-side, lean4lean-free)

Faithful counterparts of MetaCoq's `EWcbvEval` metatheory, re-proved over the
flag-parametric, spine-form `WcbvEval`. All results here are pure target-side
reasoning about `WcbvEval`/`Value` and **must be `sorryAx`-free**.

| here | MetaCoq |
|---|---|
| `value_final`       | `value_final` (`value v → eval v v`) |
| `eval_to_value`     | `eval_to_value` (`eval t v → value v`) |
| `eval_deterministic` | `eval_deterministic` |
| `eval_value`    | `eval_value` |
| `eval_unique`   | `eval_unique` (free — `Prop`-valued) |
-/

namespace LeanToLambdaBox

open Lean

/-! ### `isStuckApp` on constructor / fix spines (keep `app_cong` disjoint). -/

/-- A non-block constructor spine is never a stuck-application head (`isConstructApp`
    excludes it). MetaCoq `~~ isConstructApp` in `eval_app_cong`. -/
theorem isStuckApp_construct_spine (fl : WcbvFlags) (iid : InductiveId) (c : Nat)
    (args : List LBTerm) : isStuckApp fl (LBTerm.mkApps (.construct iid c []) args) = false := by
  simp only [isStuckApp, isConstructApp, LBTerm.spineHead_mkApps, LBTerm.spineHead_construct,
    isConstruct, Bool.or_true, Bool.true_or, Bool.not_true]

/-- A guarded `fix` spine is never a stuck-application head (`isFixApp` excludes it
    under `with_guarded_fix`). MetaCoq `~~ isFixApp` in `eval_app_cong`. -/
theorem isStuckApp_fix_spine {fl : WcbvFlags} (hg : fl.with_guarded_fix = true)
    (defs : List (@FixDef LBTerm)) (idx : Nat) (argsv : List LBTerm) :
    isStuckApp fl (LBTerm.mkApps (.fix defs idx) argsv) = false := by
  simp only [isStuckApp, isFixApp, hg, if_true, LBTerm.spineHead_mkApps, LBTerm.spineHead_fix,
    isFix, Bool.or_true, Bool.true_or, Bool.not_true]

/-- A bare (block) constructor node is never a stuck-application head. -/
theorem isStuckApp_construct (fl : WcbvFlags) (iid : InductiveId) (c : Nat)
    (args : List LBTerm) : isStuckApp fl (.construct iid c args) = false := by
  simp only [isStuckApp, isConstructApp, LBTerm.spineHead_construct, isConstruct, Bool.or_true,
    Bool.true_or, Bool.not_true]

/-- A bare `fix` head is not stuck: guarded → `isFixApp`; unguarded → `isFix`. -/
theorem isStuckApp_fix_bare (fl : WcbvFlags) (defs : List (@FixDef LBTerm)) (idx : Nat) :
    isStuckApp fl (.fix defs idx) = false := by
  simp only [isStuckApp, isFixApp, isFix, LBTerm.spineHead_fix]
  cases fl.with_guarded_fix <;> simp

/-! ### `value_final` : values evaluate to themselves. -/

/-- Values evaluate to themselves. MetaCoq `value_final`. -/
theorem value_final {Γ : GlobalDeclarations} {fl : WcbvFlags} {v : LBTerm} :
    Value Γ fl v → WcbvEval Γ fl v v := by
  intro hv
  induction hv with
  | @atom t h =>
      cases t with
      | box => exact .box
      | lambda n b => exact .lam n b
      | fvar x => exact .fvar x
      | prim p => exact .prim p
      | fix defs i => exact .fix_atom defs i
      | bvar i => exact absurd h (by simp [atomValue])
      | letIn n v b => exact absurd h (by simp [atomValue])
      | app f a => exact absurd h (by simp [atomValue])
      | const kn => exact absurd h (by simp [atomValue])
      | construct iid k args => exact absurd h (by simp [atomValue])
      | case info d alts => exact absurd h (by simp [atomValue])
      | proj p e => exact absurd h (by simp [atomValue])
  | @construct_block hb iid k args hargs ih =>
      exact .construct hb rfl (fun i hi => ih i hi)
  | @construct_nil hb iid c ar harity =>
      exact .construct_atom hb harity
  | @construct_app_val hb hd a iid c ar args hval hd_eq harity hlt ha ihhd iha =>
      subst hd_eq
      exact .construct_app hb ihhd harity hlt iha
  | @app_stuck f a hf hstuck ha ihf iha =>
      exact .app_cong ihf hstuck iha
  | @fix_app_val hg hd a defs i rarg argsv hval hd_eq hrarg hlt ha ihhd iha =>
      subst hd_eq
      obtain ⟨def_i, hsel, hpai⟩ := Option.map_eq_some_iff.mp hrarg
      exact .fix_stuck hg ihhd iha hsel (by rw [hpai]; exact hlt)

/-! ### `eval_to_value` : evaluation produces a value. -/

/-- Evaluation produces a value. MetaCoq `eval_to_value`. -/
theorem eval_to_value {Γ : GlobalDeclarations} {fl : WcbvFlags} {t v : LBTerm} :
    WcbvEval Γ fl t v → Value Γ fl v := by
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
  | @construct hb iid k args vs hl hargs ihargs =>
      exact .construct_block hb (fun i hi => ihargs i (hl ▸ hi))
  | @construct_atom hb iid c ar harity =>
      exact .construct_nil hb harity
  | @construct_app hb f a a' iid c args ar hf harity hlt ha ihf iha =>
      exact .construct_app_val hb ihf rfl harity hlt iha
  | @iota hb iid np k discr alts args names body r hnp hdiscr hsel hlen hbodyev ihd ihbody =>
      exact ihbody
  | @iota_block hb iid np k discr alts cargs names body r hnp hdiscr hsel hlen hbodyev ihd ihbody =>
      exact ihbody
  | @iota_sing hpc iid np discr names body r hp hdiscr hbodyev ihd ihbody =>
      exact ihbody
  | @proj hb p discr args v r hnp hdiscr hsel hvev ihd ihv => exact ihv
  | @proj_block hb p discr cargs v r hnp hdiscr hsel hvev ihd ihv => exact ihv
  | @proj_prop hpc p discr hp hdiscr ihd => exact .atom (by simp [atomValue])
  | @fix_guarded hg f a av defs idx def_i argsv r hf ha hsel hrarg hunf ihf iha ihunf =>
      exact ihunf
  | @fix_stuck hg f a av defs idx def_i argsv hf ha hsel hlt ihf iha =>
      exact .fix_app_val hg ihf rfl (by rw [hsel]; rfl) hlt iha
  | @fix_unguarded hg f a av defs idx def_i r hf hsel ha hunf ihf iha ihunf =>
      exact ihunf
  | @app_cong f a f' a' hf hstuck ha ihf iha =>
      exact .app_stuck ihf hstuck iha

/-! ### Determinism.

The `app`-node rules (`beta`/`app_box`/`construct_app`/`fix_guarded`/`fix_stuck`/
`fix_unguarded`/`app_cong`) are kept mutually exclusive by the shape of the
evaluated head `f'` (λ / `box` / constructor-spine / `fix`-spine / bare `fix` /
stuck head) plus the flag guards; the head's value is pinned by the induction
hypothesis. Spine heads are discriminated with `spineHead` and the `mkApps`
injectivity lemmas; `app_cong` is separated from constructor/`fix` spines by
`isStuckApp_construct_spine`/`isStuckApp_fix_spine`/`isStuckApp_fix_bare`. -/

/-- **Determinism** of `WcbvEval`. MetaCoq `eval_deterministic`. -/
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
      | app_box hf2 _ => exact absurd (ihf hf2) (by simp)
      | construct_app _ hf2 _ _ _ =>
          exact absurd (congrArg LBTerm.spineHead (ihf hf2)) (by simp [LBTerm.spineHead_mkApps])
      | fix_guarded _ hf2 _ _ _ _ =>
          exact absurd (congrArg LBTerm.spineHead (ihf hf2)) (by simp [LBTerm.spineHead_mkApps])
      | fix_stuck _ hf2 _ _ _ =>
          exact absurd (congrArg LBTerm.spineHead (ihf hf2)) (by simp [LBTerm.spineHead_mkApps])
      | fix_unguarded _ hf2 _ _ _ => exact absurd (ihf hf2) (by simp)
      | app_cong hf2 hstuck2 _ =>
          have he := ihf hf2; rw [← he] at hstuck2
          simp [isStuckApp, isLambda] at hstuck2
  | @app_box f a av hf ha ihf iha =>
      intro v' h2
      cases h2 with
      | beta hf2 _ _ => exact absurd (ihf hf2) (by simp)
      | app_box _ _ => rfl
      | construct_app _ hf2 _ _ _ =>
          exact absurd (congrArg LBTerm.spineHead (ihf hf2)) (by simp [LBTerm.spineHead_mkApps])
      | fix_guarded _ hf2 _ _ _ _ =>
          exact absurd (congrArg LBTerm.spineHead (ihf hf2)) (by simp [LBTerm.spineHead_mkApps])
      | fix_stuck _ hf2 _ _ _ =>
          exact absurd (congrArg LBTerm.spineHead (ihf hf2)) (by simp [LBTerm.spineHead_mkApps])
      | fix_unguarded _ hf2 _ _ _ => exact absurd (ihf hf2) (by simp)
      | app_cong hf2 hstuck2 _ =>
          have he := ihf hf2; rw [← he] at hstuck2
          simp [isStuckApp, isBox] at hstuck2
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
  | @construct hb iid k args vs hl hargs ihargs =>
      intro v' h2
      cases h2 with
      | @construct hb2 _ _ _ vs2 hl2 hargs2 =>
          congr 1
          apply List.ext_getElem (by omega)
          intro i h_i _
          have hi : i < args.length := by omega
          exact ihargs i hi (hargs2 i hi)
      | construct_atom hb2 _ => rw [hb] at hb2; simp at hb2
  | @construct_atom hb iid c ar harity =>
      intro v' h2
      cases h2 with
      | construct hb2 _ _ => rw [hb] at hb2; simp at hb2
      | construct_atom _ _ => rfl
  | @construct_app hb f a a' iid c args ar hf harity hlt ha ihf iha =>
      intro v' h2
      cases h2 with
      | beta hf2 _ _ =>
          exact absurd (congrArg LBTerm.spineHead (ihf hf2)) (by simp [LBTerm.spineHead_mkApps])
      | app_box hf2 _ =>
          exact absurd (congrArg LBTerm.spineHead (ihf hf2)) (by simp [LBTerm.spineHead_mkApps])
      | construct_app _ hf2 _ _ ha2 =>
          have he := ihf hf2
          obtain ⟨rfl, rfl, rfl⟩ := LBTerm.mkApps_construct_inj he
          rw [iha ha2]
      | fix_guarded _ hf2 _ _ _ _ => exact absurd (ihf hf2) LBTerm.mkApps_construct_ne_fix
      | fix_stuck _ hf2 _ _ _ => exact absurd (ihf hf2) LBTerm.mkApps_construct_ne_fix
      | fix_unguarded _ hf2 _ _ _ =>
          exact absurd (congrArg LBTerm.spineHead (ihf hf2)) (by simp [LBTerm.spineHead_mkApps])
      | app_cong hf2 hstuck2 _ =>
          have he := ihf hf2; rw [← he] at hstuck2
          rw [isStuckApp_construct_spine] at hstuck2; simp at hstuck2
  | @iota hb iid np k discr alts args names body r hnp hdiscr hsel hlen hbodyev ihd ihbody =>
      intro v' h2
      cases h2 with
      | iota _ _ hdiscr2 hsel2 _ hbodyev2 =>
          have hc := ihd hdiscr2
          obtain ⟨_, rfl, rfl⟩ := LBTerm.mkApps_construct_inj hc
          rw [hsel] at hsel2; injection hsel2 with hnb; injection hnb with _ hbd
          rw [← hbd] at hbodyev2
          exact ihbody hbodyev2
      | iota_block hb2 _ _ _ _ _ => rw [hb] at hb2; simp at hb2
      | iota_sing _ _ hdiscr2 _ =>
          exact absurd (congrArg LBTerm.spineHead (ihd hdiscr2)) (by simp [LBTerm.spineHead_mkApps])
  | @iota_block hb iid np k discr alts cargs names body r hnp hdiscr hsel hlen hbodyev ihd ihbody =>
      intro v' h2
      cases h2 with
      | iota hb2 _ _ _ _ _ => rw [hb] at hb2; simp at hb2
      | iota_block _ _ hdiscr2 hsel2 _ hbodyev2 =>
          have hc := ihd hdiscr2
          rw [LBTerm.construct.injEq] at hc
          obtain ⟨_, rfl, rfl⟩ := hc
          rw [hsel] at hsel2; injection hsel2 with hnb; injection hnb with _ hbd
          rw [← hbd] at hbodyev2
          exact ihbody hbodyev2
      | iota_sing _ _ hdiscr2 _ => exact absurd (ihd hdiscr2) (by simp)
  | @iota_sing hpc iid np discr names body r hp hdiscr hbodyev ihd ihbody =>
      intro v' h2
      cases h2 with
      | iota _ _ hdiscr2 _ _ _ =>
          exact absurd (congrArg LBTerm.spineHead (ihd hdiscr2)) (by simp [LBTerm.spineHead_mkApps])
      | iota_block _ _ hdiscr2 _ _ _ => exact absurd (ihd hdiscr2) (by simp)
      | iota_sing _ _ hdiscr2 hbodyev2 => exact ihbody hbodyev2
  | @proj hb p discr args v0 r hnp hdiscr hsel hvev ihd ihv =>
      intro v' h2
      cases h2 with
      | proj _ _ hdiscr2 hsel2 hvev2 =>
          have hc := ihd hdiscr2
          obtain ⟨_, _, rfl⟩ := LBTerm.mkApps_construct_inj hc
          rw [hsel] at hsel2; injection hsel2 with hv0
          rw [← hv0] at hvev2
          exact ihv hvev2
      | proj_block hb2 _ _ _ _ => rw [hb] at hb2; simp at hb2
      | proj_prop _ _ hdiscr2 =>
          exact absurd (congrArg LBTerm.spineHead (ihd hdiscr2)) (by simp [LBTerm.spineHead_mkApps])
  | @proj_block hb p discr cargs v0 r hnp hdiscr hsel hvev ihd ihv =>
      intro v' h2
      cases h2 with
      | proj hb2 _ _ _ _ => rw [hb] at hb2; simp at hb2
      | proj_block _ _ hdiscr2 hsel2 hvev2 =>
          have hc := ihd hdiscr2
          rw [LBTerm.construct.injEq] at hc
          obtain ⟨_, _, rfl⟩ := hc
          rw [hsel] at hsel2; injection hsel2 with hv0
          rw [← hv0] at hvev2
          exact ihv hvev2
      | proj_prop _ _ hdiscr2 => exact absurd (ihd hdiscr2) (by simp)
  | @proj_prop hpc p discr hp hdiscr ihd =>
      intro v' h2
      cases h2 with
      | proj _ _ hdiscr2 _ _ =>
          exact absurd (congrArg LBTerm.spineHead (ihd hdiscr2)) (by simp [LBTerm.spineHead_mkApps])
      | proj_block _ _ hdiscr2 _ _ => exact absurd (ihd hdiscr2) (by simp)
      | proj_prop _ _ _ => rfl
  | @fix_guarded hg f a av defs idx def_i argsv r hf ha hsel hrarg hunf ihf iha ihunf =>
      intro v' h2
      cases h2 with
      | beta hf2 _ _ =>
          exact absurd (congrArg LBTerm.spineHead (ihf hf2)) (by simp [LBTerm.spineHead_mkApps])
      | app_box hf2 _ =>
          exact absurd (congrArg LBTerm.spineHead (ihf hf2)) (by simp [LBTerm.spineHead_mkApps])
      | construct_app _ hf2 _ _ _ =>
          exact absurd (ihf hf2).symm LBTerm.mkApps_construct_ne_fix
      | fix_guarded _ hf2 ha2 hsel2 hrarg2 hunf2 =>
          have he := ihf hf2
          obtain ⟨rfl, rfl, rfl⟩ := LBTerm.mkApps_fix_inj he
          rw [hsel] at hsel2; injection hsel2 with hdi; subst hdi
          have hav := iha ha2
          rw [← hav] at hunf2
          exact ihunf hunf2
      | fix_stuck _ hf2 _ hsel2 hlt2 =>
          have he := ihf hf2
          obtain ⟨rfl, rfl, rfl⟩ := LBTerm.mkApps_fix_inj he
          rw [hsel] at hsel2; injection hsel2 with hdi; subst hdi
          omega
      | fix_unguarded hg2 _ _ _ _ => rw [hg] at hg2; simp at hg2
      | app_cong hf2 hstuck2 _ =>
          have he := ihf hf2; rw [← he] at hstuck2
          rw [isStuckApp_fix_spine hg] at hstuck2; simp at hstuck2
  | @fix_stuck hg f a av defs idx def_i argsv hf ha hsel hlt ihf iha =>
      intro v' h2
      cases h2 with
      | beta hf2 _ _ =>
          exact absurd (congrArg LBTerm.spineHead (ihf hf2)) (by simp [LBTerm.spineHead_mkApps])
      | app_box hf2 _ =>
          exact absurd (congrArg LBTerm.spineHead (ihf hf2)) (by simp [LBTerm.spineHead_mkApps])
      | construct_app _ hf2 _ _ _ =>
          exact absurd (ihf hf2).symm LBTerm.mkApps_construct_ne_fix
      | fix_guarded _ hf2 _ hsel2 hrarg2 _ =>
          have he := ihf hf2
          obtain ⟨rfl, rfl, rfl⟩ := LBTerm.mkApps_fix_inj he
          rw [hsel] at hsel2; injection hsel2 with hdi; subst hdi
          omega
      | fix_stuck _ hf2 ha2 hsel2 hlt2 =>
          have he := ihf hf2
          obtain ⟨rfl, rfl, rfl⟩ := LBTerm.mkApps_fix_inj he
          have hav := iha ha2
          rw [← he, ← hav]
      | fix_unguarded hg2 _ _ _ _ => rw [hg] at hg2; simp at hg2
      | app_cong hf2 hstuck2 _ =>
          have he := ihf hf2; rw [← he] at hstuck2
          rw [isStuckApp_fix_spine hg] at hstuck2; simp at hstuck2
  | @fix_unguarded hg f a av defs idx def_i r hf hsel ha hunf ihf iha ihunf =>
      intro v' h2
      cases h2 with
      | beta hf2 _ _ => exact absurd (ihf hf2) (by simp)
      | app_box hf2 _ => exact absurd (ihf hf2) (by simp)
      | construct_app _ hf2 _ _ _ =>
          exact absurd (congrArg LBTerm.spineHead (ihf hf2)) (by simp [LBTerm.spineHead_mkApps])
      | fix_guarded hg2 _ _ _ _ _ => rw [hg] at hg2; simp at hg2
      | fix_stuck hg2 _ _ _ _ => rw [hg] at hg2; simp at hg2
      | fix_unguarded _ hf2 hsel2 ha2 hunf2 =>
          have he := ihf hf2; injection he with hd hi
          subst hd; subst hi
          rw [hsel] at hsel2; injection hsel2 with hdi; subst hdi
          have hav := iha ha2
          rw [← hav] at hunf2
          exact ihunf hunf2
      | app_cong hf2 hstuck2 _ =>
          have he := ihf hf2; rw [← he] at hstuck2
          rw [isStuckApp_fix_bare] at hstuck2; simp at hstuck2
  | @app_cong f a f' a' hf hstuck ha ihf iha =>
      intro v' h2
      cases h2 with
      | beta hf2 _ _ =>
          have he := ihf hf2; rw [he] at hstuck
          simp [isStuckApp, isLambda] at hstuck
      | app_box hf2 _ =>
          have he := ihf hf2; rw [he] at hstuck
          simp [isStuckApp, isBox] at hstuck
      | construct_app _ hf2 _ _ _ =>
          have he := ihf hf2; rw [he] at hstuck
          rw [isStuckApp_construct_spine] at hstuck; simp at hstuck
      | fix_guarded hg2 hf2 _ _ _ _ =>
          have he := ihf hf2; rw [he] at hstuck
          rw [isStuckApp_fix_spine hg2] at hstuck; simp at hstuck
      | fix_stuck hg2 hf2 _ _ _ =>
          have he := ihf hf2; rw [he] at hstuck
          rw [isStuckApp_fix_spine hg2] at hstuck; simp at hstuck
      | fix_unguarded _ hf2 _ _ _ =>
          have he := ihf hf2; rw [he] at hstuck
          rw [isStuckApp_fix_bare] at hstuck; simp at hstuck
      | app_cong hf2 _ ha2 => rw [ihf hf2, iha ha2]

/-- A value has a unique evaluation image. MetaCoq `eval_value`. -/
theorem eval_value {Γ : GlobalDeclarations} {fl : WcbvFlags} {v v' : LBTerm}
    (hv : Value Γ fl v) (h : WcbvEval Γ fl v v') : v = v' :=
  eval_deterministic (value_final hv) h

/-- Derivation irrelevance — free, because `WcbvEval` is `Prop`-valued. MetaCoq
    `eval_unique` (which there needs a `Type`-level argument). -/
theorem eval_unique {Γ : GlobalDeclarations} {fl : WcbvFlags} {t v : LBTerm}
    (h1 h2 : WcbvEval Γ fl t v) : h1 = h2 := rfl

/-! ## Non-vacuity witnesses for the metatheory

Every hypothesis-bearing lemma above is guarded against vacuous truth: the
hypotheses are satisfiable and each lemma is shown to *fire* on a concrete
non-trivial evaluation. -/

/-- A concrete non-trivial evaluation: `(λ. #0) □ ⇓ □`. -/
theorem wcbvEval_beta_box :
    WcbvEval [] optFlags (.app (.lambda .anon (.bvar 0)) .box) .box :=
  .beta (.lam .anon (.bvar 0)) .box .box

theorem value_box : Value [] optFlags (.box : LBTerm) := .atom (by simp [atomValue])

/-- `Value` is inhabited (⇒ `value_final` is not vacuous). -/
theorem value_final_hyps_satisfiable : ∃ (fl : WcbvFlags) (v : LBTerm), Value [] fl v :=
  ⟨optFlags, .box, value_box⟩

/-- `value_final` fires: `□` (a value) evaluates to itself. -/
theorem value_final_fires : WcbvEval [] optFlags .box .box := value_final value_box

/-- `WcbvEval` is inhabited (⇒ `eval_to_value`/`eval_deterministic` are not vacuous). -/
theorem eval_hyps_satisfiable :
    ∃ (Γ : GlobalDeclarations) (fl : WcbvFlags) (t v : LBTerm), WcbvEval Γ fl t v :=
  ⟨[], optFlags, _, _, wcbvEval_beta_box⟩

/-- `eval_to_value` fires: the redex's result `□` is a value. -/
theorem eval_to_value_fires : Value [] optFlags .box := eval_to_value wcbvEval_beta_box

/-- `eval_deterministic` fires on the β-redex `(λ. #0) □` (whose argument evaluates). -/
theorem eval_deterministic_fires : (.box : LBTerm) = .box :=
  eval_deterministic wcbvEval_beta_box wcbvEval_beta_box

/-- `eval_value` fires: the value `□` evaluates only to itself. -/
theorem eval_value_fires : (.box : LBTerm) = .box :=
  eval_value value_box (@WcbvEval.box [] optFlags)

/-- `eval_unique` fires: any two derivations of `□ ⇓ □` are equal. -/
theorem eval_unique_fires (h1 h2 : WcbvEval [] optFlags .box .box) : h1 = h2 :=
  eval_unique h1 h2

/-! ### Non-block (applied) constructors genuinely fire — with a **parameter**.

`appliedFlags` is MetaCoq's `opt_wcbv_flags` (`with_constructor_as_block = false`),
the validated target. The witness is a **one-parameter** constructor (`cstr_arity =
npars + cstr_nargs = 1 + 1 = 2`): a constructor spine `((mk) p) x` accumulates its
parameter `p` and then its field `x` before saturating, exercising the corrected
`constructorArity` (`+ npars`) and the spine-form `construct_atom`/`construct_app`
values. -/

/-- One inductive `AC` with a single **1-parameter, 1-field** constructor `mk`
    (`cstr_arity = 1 + 1 = 2`). -/
def acKn : Kername := { mp := .MPfile [], id := "AC" }
def acIid : InductiveId := { mutualBlockName := acKn, idx := 0 }
def acOIB : OneInductiveBody :=
  { name := "AC", propositional := false, kelim := .IntoAny,
    ctors := [{ name := "mk", nargs := 1 }], projs := [] }
def acΓ : GlobalDeclarations :=
  [(acKn, .inductiveDecl { finite := .finite, npars := 1, bodies := [acOIB] })]

/-- `constructorArity` now includes the parameter: `1 (npars) + 1 (nargs) = 2`. -/
theorem ac_arity : constructorArity acΓ acIid 0 = some 2 := rfl

/-- The nullary applied head is a value under `appliedFlags`. -/
theorem ac_nil : WcbvEval acΓ appliedFlags (.construct acIid 0 []) (.construct acIid 0 []) :=
  .construct_atom rfl ac_arity

/-- `construct_atom`/`construct_app` fire: `((mk) p) x` accumulates the parameter `p`
    then the field `x` into the two-argument spine `mkApps (mk) [p, x]` — a genuine
    non-block, parameter-carrying constructor value. -/
theorem construct_app_fires :
    WcbvEval acΓ appliedFlags
      (.app (.app (.construct acIid 0 []) .box) .box)
      (LBTerm.mkApps (.construct acIid 0 []) [.box, .box]) := by
  have h1 : WcbvEval acΓ appliedFlags (.app (.construct acIid 0 []) .box)
      (.app (LBTerm.mkApps (.construct acIid 0 []) []) .box) :=
    .construct_app rfl ac_nil ac_arity (by decide) .box
  have h2 := WcbvEval.construct_app (Γ := acΓ) (fl := appliedFlags) (a := .box)
    (args := [.box]) rfl h1 ac_arity (by decide) .box
  simpa [LBTerm.mkApps] using h2

/-- The two-argument applied-constructor spine is a genuine `Value` (via `eval_to_value`). -/
theorem construct_app_value :
    Value acΓ appliedFlags (LBTerm.mkApps (.construct acIid 0 []) [.box, .box]) :=
  eval_to_value construct_app_fires

/-! ### A mutual (`n ≥ 2`) `fix` block exercises the corrected `fixSubst` order.

`fixSubst defs = [fix defs (n-1); …; fix defs 0]` (reversed) matters for `n ≥ 2`. The
witness is a two-definition block; `fix_atom`/`fix_stuck` build a `fix`-spine value
whose unfolding (were it to fire) would substitute in the corrected order. -/

/-- A mutual block of two `fix` definitions (`n = 2`), each with recursive-argument
    index `1` (so a single applied argument leaves the spine stuck/under-applied). -/
def mfDefs : List (@FixDef LBTerm) :=
  [ { name := .anon, body := .bvar 0, principalArgIdx := 1 },
    { name := .anon, body := .bvar 1, principalArgIdx := 1 } ]

theorem mf_fixSubst : LBTerm.fixSubst mfDefs = [.fix mfDefs 1, .fix mfDefs 0] := rfl

/-- The second definition's `fix` head, applied to one argument, is stuck (under its
    `rarg = 1`), yielding the `fix`-spine value `(fix mfDefs 1) □`. Exercises the
    `n = 2` mutual block with the corrected `fixSubst`. -/
theorem mf_fix_stuck :
    WcbvEval [] optFlags (.app (.fix mfDefs 1) .box)
      (.app (LBTerm.mkApps (.fix mfDefs 1) []) .box) :=
  .fix_stuck rfl (.fix_atom mfDefs 1) .box rfl (by decide)

/-- That `fix`-spine is a genuine `Value` (via `eval_to_value`). -/
theorem mf_fix_value :
    Value [] optFlags (.app (LBTerm.mkApps (.fix mfDefs 1) []) .box) :=
  eval_to_value mf_fix_stuck

end LeanToLambdaBox
