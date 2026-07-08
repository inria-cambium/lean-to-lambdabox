import LeanToLambdaBox.Semantics.Eval

/-!
# `WcbvEvalT` — a `Type`-valued twin of `WcbvEval` for export to Rocq

`rocq-lean-import` maps a Lean `Prop`-valued inductive to a Rocq **`SProp`**-valued
one, which is *non-eliminable* into `Type`. The Rocq equivalence proof against
MetaRocq's `EWcbvEval.eval` (itself a `Set`-valued inductive) needs to eliminate a
Lean-side evaluation derivation into `Type`/`Set`. We therefore export a
**`Type`-valued** twin `WcbvEvalT` with rule-for-rule the *same* content as the
`Prop`-valued `WcbvEval` of `Semantics/Eval.lean`, and record — axiom-free — that
the two carry the same information:

`wcbvEvalT_iff : Nonempty (WcbvEvalT Γ fl t v) ↔ WcbvEval Γ fl t v`.

The Rocq development proves the equivalence against the imported `WcbvEvalT`; the
`Nonempty`-quotient of that result ties back to the `SProp`-image of `WcbvEval`
through the imported `wcbvEvalT_iff`.

Two phrasing choices make the exported cone clean to import:

* The block-constructor congruence (`WcbvEval.construct`) carries its per-argument
  evaluations as `∀ i (h : i < args.length), WcbvEval Γ fl args[i] (vs[i]'…)`, whose
  type contains an `Eq.rec`-transport (`hl ▸ h`) and `getElem` dependencies that are
  awkward for the importer. `WcbvEvalT.construct` uses the first-order **`All2T`**
  relation instead — the exact analogue of MetaRocq's `All2_Set eval args args'` used
  by `eval_construct_block`. `All2T` is exported alongside `WcbvEvalT`.
* Everything is `Type`-valued; the side conditions (`… = false`, `isProp… = false`,
  `envLookup … = some …`, arithmetic comparisons) stay `Prop`, which is fine as
  hypotheses of a `Type`-valued inductive.
-/

namespace LeanToLambdaBox

open Lean

/-- `Type`-valued pointwise relation on two lists — the analogue of `List.Forall₂`
    in `Type`, and of MetaRocq's `All2_Set`. Used by `WcbvEvalT.construct` for the
    block-constructor congruence (mirrors `All2_Set eval args args'`). -/
inductive All2T {α β : Type} (R : α → β → Type) : List α → List β → Type where
  | nil : All2T R [] []
  | cons {x : α} {y : β} {xs : List α} {ys : List β} :
      R x y → All2T R xs ys → All2T R (x :: xs) (y :: ys)

namespace All2T

/-- Length agreement extracted from an `All2T` witness. Kept `propext`/`simp`-free
    so `wcbvEvalT_iff` stays axiom-free. -/
theorem length_eq {α β : Type} {R : α → β → Type} :
    ∀ {xs : List α} {ys : List β}, All2T R xs ys → xs.length = ys.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ t => congrArg (· + 1) (length_eq t)

/-- Build an `All2T` witness (in `Prop`, wrapped in `Nonempty`) from pointwise
    `Nonempty`-evaluations plus length agreement. Used for the backward direction of
    `wcbvEvalT_iff` on the block-constructor congruence. Kept `propext`/`simp`-free
    (uses only structural `Nat`/`List` facts up to definitional equality). -/
theorem nonempty_of_pointwise {α β : Type} {R : α → β → Type} :
    ∀ {xs : List α} {ys : List β}, xs.length = ys.length →
      (∀ (i : Nat) (hx : i < xs.length) (hy : i < ys.length), Nonempty (R (xs[i]'hx) (ys[i]'hy))) →
      Nonempty (All2T R xs ys)
  | [], [], _, _ => ⟨.nil⟩
  | x :: xs, y :: ys, hl, hp => by
      obtain ⟨hhead⟩ := hp 0 (Nat.succ_pos _) (Nat.succ_pos _)
      obtain ⟨htail⟩ :=
        nonempty_of_pointwise (α := α) (β := β) (R := R) (xs := xs) (ys := ys)
          (Nat.succ.inj hl)
          (fun i hx hy => hp (i + 1) (Nat.succ_lt_succ hx) (Nat.succ_lt_succ hy))
      exact ⟨.cons hhead htail⟩

end All2T

/-- `Type`-valued weak call-by-value big-step evaluation of λ□ terms. Rule-for-rule
    identical to `WcbvEval` (`Semantics/Eval.lean`), except that it lives in `Type`
    and the block-constructor congruence uses `All2T`. Exported to Rocq via
    `lean4export` + `rocq-lean-import`. -/
inductive WcbvEvalT (Γ : GlobalDeclarations) (fl : WcbvFlags) : LBTerm → LBTerm → Type
  | box : WcbvEvalT Γ fl .box .box
  | lam (n : BinderName) (b : LBTerm) : WcbvEvalT Γ fl (.lambda n b) (.lambda n b)
  | fvar (x : FVarId) : WcbvEvalT Γ fl (.fvar x) (.fvar x)
  | prim (p : PrimVal) : WcbvEvalT Γ fl (.prim p) (.prim p)
  | fix_atom (defs : List (@FixDef LBTerm)) (i : Nat) : WcbvEvalT Γ fl (.fix defs i) (.fix defs i)
  | beta {f a : LBTerm} {n : BinderName} {b av r : LBTerm} :
      WcbvEvalT Γ fl f (.lambda n b) → WcbvEvalT Γ fl a av →
      WcbvEvalT Γ fl (LBTerm.subst1 av b) r →
      WcbvEvalT Γ fl (.app f a) r
  | app_box {f a av : LBTerm} :
      WcbvEvalT Γ fl f .box → WcbvEvalT Γ fl a av → WcbvEvalT Γ fl (.app f a) .box
  | zeta {n : BinderName} {v b vv r : LBTerm} :
      WcbvEvalT Γ fl v vv → WcbvEvalT Γ fl (LBTerm.subst1 vv b) r →
      WcbvEvalT Γ fl (.letIn n v b) r
  | delta {kn : Kername} {body r : LBTerm} :
      LBTerm.envLookup Γ kn = some (.constantDecl ⟨some body⟩) → WcbvEvalT Γ fl body r →
      WcbvEvalT Γ fl (.const kn) r
  | construct (hb : fl.with_constructor_as_block = true)
      {iid : InductiveId} {k : Nat} {args vs : List LBTerm}
      (hargs : All2T (WcbvEvalT Γ fl) args vs) :
      WcbvEvalT Γ fl (.construct iid k args) (.construct iid k vs)
  | construct_atom (hb : fl.with_constructor_as_block = false)
      {iid : InductiveId} {c ar : Nat} :
      constructorArity Γ iid c = some ar →
      WcbvEvalT Γ fl (.construct iid c []) (.construct iid c [])
  | construct_app (hb : fl.with_constructor_as_block = false)
      {f a a' : LBTerm} {iid : InductiveId} {c : Nat} {args : List LBTerm} {ar : Nat} :
      WcbvEvalT Γ fl f (LBTerm.mkApps (.construct iid c []) args) →
      constructorArity Γ iid c = some ar →
      args.length < ar →
      WcbvEvalT Γ fl a a' →
      WcbvEvalT Γ fl (.app f a) (.app (LBTerm.mkApps (.construct iid c []) args) a')
  | iota (hb : fl.with_constructor_as_block = false)
         {iid : InductiveId} {np k : Nat} {discr : LBTerm}
         {alts : List (List BinderName × LBTerm)} {args : List LBTerm}
         {names : List BinderName} {body r : LBTerm} :
      isPropositionalInductive Γ iid = false →
      WcbvEvalT Γ fl discr (LBTerm.mkApps (.construct iid k []) args) →
      alts[k]? = some (names, body) →
      (args.drop np).length = names.length →
      WcbvEvalT Γ fl (LBTerm.substList ((args.drop np).reverse) body) r →
      WcbvEvalT Γ fl (.case (iid, np) discr alts) r
  | iota_block (hb : fl.with_constructor_as_block = true)
         {iid : InductiveId} {np k : Nat} {discr : LBTerm}
         {alts : List (List BinderName × LBTerm)} {cargs : List LBTerm}
         {names : List BinderName} {body r : LBTerm} :
      isPropositionalInductive Γ iid = false →
      WcbvEvalT Γ fl discr (.construct iid k cargs) →
      alts[k]? = some (names, body) →
      (cargs.drop np).length = names.length →
      WcbvEvalT Γ fl (LBTerm.substList ((cargs.drop np).reverse) body) r →
      WcbvEvalT Γ fl (.case (iid, np) discr alts) r
  | iota_sing (hpc : fl.with_prop_case = true) {iid : InductiveId} {np : Nat} {discr : LBTerm}
              {names : List BinderName} {body r : LBTerm} :
      isPropositionalInductive Γ iid = true →
      WcbvEvalT Γ fl discr .box →
      WcbvEvalT Γ fl (LBTerm.substList (List.replicate names.length .box) body) r →
      WcbvEvalT Γ fl (.case (iid, np) discr [(names, body)]) r
  | proj (hb : fl.with_constructor_as_block = false)
         {p : ProjectionInfo} {discr : LBTerm} {args : List LBTerm} {v r : LBTerm} :
      isPropositionalInductive Γ p.indType = false →
      WcbvEvalT Γ fl discr (LBTerm.mkApps (.construct p.indType 0 []) args) →
      args[p.paramCount + p.fieldIdx]? = some v →
      WcbvEvalT Γ fl v r →
      WcbvEvalT Γ fl (.proj p discr) r
  | proj_block (hb : fl.with_constructor_as_block = true)
         {p : ProjectionInfo} {discr : LBTerm} {cargs : List LBTerm} {v r : LBTerm} :
      isPropositionalInductive Γ p.indType = false →
      WcbvEvalT Γ fl discr (.construct p.indType 0 cargs) →
      cargs[p.paramCount + p.fieldIdx]? = some v →
      WcbvEvalT Γ fl v r →
      WcbvEvalT Γ fl (.proj p discr) r
  | proj_prop (hpc : fl.with_prop_case = true) {p : ProjectionInfo} {discr : LBTerm} :
      isPropositionalInductive Γ p.indType = true →
      WcbvEvalT Γ fl discr .box →
      WcbvEvalT Γ fl (.proj p discr) .box
  | fix_guarded (hg : fl.with_guarded_fix = true) {f a av : LBTerm}
                {defs : List (@FixDef LBTerm)} {idx : Nat} {def_i : @FixDef LBTerm}
                {argsv : List LBTerm} {r : LBTerm} :
      WcbvEvalT Γ fl f (LBTerm.mkApps (.fix defs idx) argsv) →
      WcbvEvalT Γ fl a av →
      defs[idx]? = some def_i →
      def_i.principalArgIdx = argsv.length →
      WcbvEvalT Γ fl
        (.app (LBTerm.mkApps (LBTerm.substList (LBTerm.fixSubst defs) def_i.body) argsv) av) r →
      WcbvEvalT Γ fl (.app f a) r
  | fix_stuck (hg : fl.with_guarded_fix = true) {f a av : LBTerm}
              {defs : List (@FixDef LBTerm)} {idx : Nat} {def_i : @FixDef LBTerm}
              {argsv : List LBTerm} :
      WcbvEvalT Γ fl f (LBTerm.mkApps (.fix defs idx) argsv) →
      WcbvEvalT Γ fl a av →
      defs[idx]? = some def_i →
      argsv.length < def_i.principalArgIdx →
      WcbvEvalT Γ fl (.app f a) (.app (LBTerm.mkApps (.fix defs idx) argsv) av)
  | fix_unguarded (hg : fl.with_guarded_fix = false) {f a av : LBTerm}
                  {defs : List (@FixDef LBTerm)} {idx : Nat} {def_i : @FixDef LBTerm} {r : LBTerm} :
      WcbvEvalT Γ fl f (.fix defs idx) →
      defs[idx]? = some def_i →
      WcbvEvalT Γ fl a av →
      WcbvEvalT Γ fl (.app (LBTerm.substList (LBTerm.fixSubst defs) def_i.body) av) r →
      WcbvEvalT Γ fl (.app f a) r
  | app_cong {f a f' a' : LBTerm} :
      WcbvEvalT Γ fl f f' → isStuckApp fl f' = true → WcbvEvalT Γ fl a a' →
      WcbvEvalT Γ fl (.app f a) (.app f' a')

/- Forward direction: a `Type`-valued derivation forgets to a `Prop`-valued one.
   Structural recursion through the nested `All2T` via the mutual `getEv`, which
   reads out the pointwise `WcbvEval` from a nested `All2T (WcbvEvalT …)` witness
   (`induction` does not support the nested `WcbvEvalT`). -/
mutual
/-- A `Type`-valued λ□ evaluation derivation forgets to the `Prop`-valued one. -/
def WcbvEvalT.toWcbvEval {Γ : GlobalDeclarations} {fl : WcbvFlags} :
    {t v : LBTerm} → WcbvEvalT Γ fl t v → WcbvEval Γ fl t v
  | _, _, .box => .box
  | _, _, .lam n b => .lam n b
  | _, _, .fvar x => .fvar x
  | _, _, .prim p => .prim p
  | _, _, .fix_atom defs i => .fix_atom defs i
  | _, _, .beta hf ha hbody => .beta hf.toWcbvEval ha.toWcbvEval hbody.toWcbvEval
  | _, _, .app_box hf ha => .app_box hf.toWcbvEval ha.toWcbvEval
  | _, _, .zeta hv hbody => .zeta hv.toWcbvEval hbody.toWcbvEval
  | _, _, .delta hlk hbody => .delta hlk hbody.toWcbvEval
  | _, _, .construct hb hargs =>
      .construct hb (All2T.length_eq hargs)
        (fun i hi => WcbvEvalT.getEv hargs i hi (All2T.length_eq hargs ▸ hi))
  | _, _, .construct_atom hb harity => .construct_atom hb harity
  | _, _, .construct_app hb hf harity hlt ha =>
      .construct_app hb hf.toWcbvEval harity hlt ha.toWcbvEval
  | _, _, .iota hb hnp hd hsel hlen hbody =>
      .iota hb hnp hd.toWcbvEval hsel hlen hbody.toWcbvEval
  | _, _, .iota_block hb hnp hd hsel hlen hbody =>
      .iota_block hb hnp hd.toWcbvEval hsel hlen hbody.toWcbvEval
  | _, _, .iota_sing hpc hp hd hbody => .iota_sing hpc hp hd.toWcbvEval hbody.toWcbvEval
  | _, _, .proj hb hnp hd hsel hv => .proj hb hnp hd.toWcbvEval hsel hv.toWcbvEval
  | _, _, .proj_block hb hnp hd hsel hv => .proj_block hb hnp hd.toWcbvEval hsel hv.toWcbvEval
  | _, _, .proj_prop hpc hp hd => .proj_prop hpc hp hd.toWcbvEval
  | _, _, .fix_guarded hg hf ha hsel hrarg hunf =>
      .fix_guarded hg hf.toWcbvEval ha.toWcbvEval hsel hrarg hunf.toWcbvEval
  | _, _, .fix_stuck hg hf ha hsel hlt => .fix_stuck hg hf.toWcbvEval ha.toWcbvEval hsel hlt
  | _, _, .fix_unguarded hg hf hsel ha hunf =>
      .fix_unguarded hg hf.toWcbvEval hsel ha.toWcbvEval hunf.toWcbvEval
  | _, _, .app_cong hf hstuck ha => .app_cong hf.toWcbvEval hstuck ha.toWcbvEval

/-- Read out the pointwise `WcbvEval` from a nested `All2T (WcbvEvalT …)` witness,
    forgetting each element via `toWcbvEval` on a structural subterm. -/
def WcbvEvalT.getEv {Γ : GlobalDeclarations} {fl : WcbvFlags} :
    {args vs : List LBTerm} → All2T (WcbvEvalT Γ fl) args vs →
      ∀ (i : Nat) (hx : i < args.length) (hy : i < vs.length),
        WcbvEval Γ fl (args[i]'hx) (vs[i]'hy)
  | _ :: _, _ :: _, .cons r _, 0, _, _ => r.toWcbvEval
  | _ :: _, _ :: _, .cons _ t, i + 1, hx, hy =>
      WcbvEvalT.getEv t i (Nat.lt_of_succ_lt_succ hx) (Nat.lt_of_succ_lt_succ hy)
end

/-- Backward direction: a `Prop`-valued derivation is matched by a `Type`-valued
    one, `Nonempty`-wrapped so it stays a `Prop`-elimination of the `Prop`-valued
    `WcbvEval` (no `Classical.choice`, hence axiom-free). -/
theorem WcbvEval.nonempty_wcbvEvalT {Γ : GlobalDeclarations} {fl : WcbvFlags} :
    ∀ {t v : LBTerm}, WcbvEval Γ fl t v → Nonempty (WcbvEvalT Γ fl t v) := by
  intro t v h
  induction h with
  | box => exact ⟨.box⟩
  | lam n b => exact ⟨.lam n b⟩
  | fvar x => exact ⟨.fvar x⟩
  | prim p => exact ⟨.prim p⟩
  | fix_atom defs i => exact ⟨.fix_atom defs i⟩
  | beta _ _ _ ihf iha ihbody =>
      obtain ⟨ihf⟩ := ihf; obtain ⟨iha⟩ := iha; obtain ⟨ihbody⟩ := ihbody
      exact ⟨.beta ihf iha ihbody⟩
  | app_box _ _ ihf iha => obtain ⟨ihf⟩ := ihf; obtain ⟨iha⟩ := iha; exact ⟨.app_box ihf iha⟩
  | zeta _ _ ihv ihbody => obtain ⟨ihv⟩ := ihv; obtain ⟨ihbody⟩ := ihbody; exact ⟨.zeta ihv ihbody⟩
  | delta hlk _ ihbody => obtain ⟨ihbody⟩ := ihbody; exact ⟨.delta hlk ihbody⟩
  | @construct hb iid k args vs hl hargs ihargs =>
      have hall : Nonempty (All2T (WcbvEvalT Γ fl) args vs) :=
        All2T.nonempty_of_pointwise hl (fun i hx _ => ihargs i hx)
      obtain ⟨hall⟩ := hall
      exact ⟨.construct hb hall⟩
  | construct_atom hb harity => exact ⟨.construct_atom hb harity⟩
  | construct_app hb _ harity hlt _ ihf iha =>
      obtain ⟨ihf⟩ := ihf; obtain ⟨iha⟩ := iha
      exact ⟨.construct_app hb ihf harity hlt iha⟩
  | iota hb hnp _ hsel hlen _ ihd ihbody =>
      obtain ⟨ihd⟩ := ihd; obtain ⟨ihbody⟩ := ihbody
      exact ⟨.iota hb hnp ihd hsel hlen ihbody⟩
  | iota_block hb hnp _ hsel hlen _ ihd ihbody =>
      obtain ⟨ihd⟩ := ihd; obtain ⟨ihbody⟩ := ihbody
      exact ⟨.iota_block hb hnp ihd hsel hlen ihbody⟩
  | iota_sing hpc hp _ _ ihd ihbody =>
      obtain ⟨ihd⟩ := ihd; obtain ⟨ihbody⟩ := ihbody
      exact ⟨.iota_sing hpc hp ihd ihbody⟩
  | proj hb hnp _ hsel _ ihd ihv =>
      obtain ⟨ihd⟩ := ihd; obtain ⟨ihv⟩ := ihv
      exact ⟨.proj hb hnp ihd hsel ihv⟩
  | proj_block hb hnp _ hsel _ ihd ihv =>
      obtain ⟨ihd⟩ := ihd; obtain ⟨ihv⟩ := ihv
      exact ⟨.proj_block hb hnp ihd hsel ihv⟩
  | proj_prop hpc hp _ ihd => obtain ⟨ihd⟩ := ihd; exact ⟨.proj_prop hpc hp ihd⟩
  | fix_guarded hg _ _ hsel hrarg _ ihf iha ihunf =>
      obtain ⟨ihf⟩ := ihf; obtain ⟨iha⟩ := iha; obtain ⟨ihunf⟩ := ihunf
      exact ⟨.fix_guarded hg ihf iha hsel hrarg ihunf⟩
  | fix_stuck hg _ _ hsel hlt ihf iha =>
      obtain ⟨ihf⟩ := ihf; obtain ⟨iha⟩ := iha
      exact ⟨.fix_stuck hg ihf iha hsel hlt⟩
  | fix_unguarded hg _ hsel _ _ ihf iha ihunf =>
      obtain ⟨ihf⟩ := ihf; obtain ⟨iha⟩ := iha; obtain ⟨ihunf⟩ := ihunf
      exact ⟨.fix_unguarded hg ihf hsel iha ihunf⟩
  | app_cong _ hstuck _ ihf iha =>
      obtain ⟨ihf⟩ := ihf; obtain ⟨iha⟩ := iha
      exact ⟨.app_cong ihf hstuck iha⟩

/-- **Adequacy of the `Type`-valued twin.** The inhabitedness of `WcbvEvalT` is
    logically equivalent to the `Prop`-valued `WcbvEval`. Axiom-free (see
    `#print axioms wcbvEvalT_iff`), so the Rocq equivalence proved against the
    imported `WcbvEvalT` transfers to the `SProp`-image of `WcbvEval`. -/
theorem wcbvEvalT_iff {Γ : GlobalDeclarations} {fl : WcbvFlags} {t v : LBTerm} :
    Nonempty (WcbvEvalT Γ fl t v) ↔ WcbvEval Γ fl t v :=
  ⟨fun h => h.elim (·.toWcbvEval), WcbvEval.nonempty_wcbvEvalT⟩

end LeanToLambdaBox
