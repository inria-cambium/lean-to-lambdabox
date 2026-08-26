import LeanToLambdaBox.Erases
import LeanToLambdaBox.Closed

/-!
# Let-value thinning for `Erases` (visitExpr→Erases bridge support)

The shipping eraser's `visitLet` (`Erasure.lean`, via `letMonocular`/`withLocalDef`)
opens a let-binder into a fresh fvar `x` *before* erasing the let-**value**. So the
bridge's induction hands us an `Erases` derivation for the value at the context
extended with the fvar-tagged entry `(some (x, deps), .vlet A e₀)`, while
`Erases.letE` consumes the value's erasure at the *outer* context `Δ`. This file
proves the required strengthening ("thinning"): an unused fvar-tagged `.vlet`
entry can be dropped from the `VLCtx` without touching either the source `Expr`
or the target `LBTerm`.

Why the `.vlet` case is clean (unlike a hypothetical `.vlam` analogue):

* the dropped entry is **fvar-tagged** (`some _`), so `VLCtx.find?` passes source
  de Bruijn indices through it unchanged (`VLCtx.next (some _) (.inl i) = some (.inl i)`);
* it is a **`.vlet`**, so it contributes nothing to `VLCtx.toCtx` and has
  `VLocalDecl.depth = 0` — no `VExpr` lifting happens anywhere.

Consequently the strengthening holds *on the nose*: same target `t`, same `VExpr`
witnesses in every lean4lean side premise, and **no** `env.Ordered`/`VLCtx.WF`/
closedness premises are needed. This is why we do **not** route through lean4lean's
`TrExprS.weakFV_inv` (which produces only an existential witness at the smaller
context and would force a `TrExprS.uniq`/`Erasable.defeq` transport in the `box`
case): instead we mirror the proof skeleton of lean4lean's `TrExprS.abstract`
(`Verify/Typing/Lemmas.lean`), whose `VLCtx.Abstract` surgery is the closest
existing relative of ours.

Because binder cases (`lam`/`letE`) extend the context *above* the dropped entry,
the induction needs the surgery generalized to an arbitrary depth below a prefix
of bvar-tagged (`none`) entries — the `ThinVLet` relation, mirroring how
lean4lean's `VLCtx.InstLet`/`VLCtx.Abstract` are stated. The consumable
depth-0 corollary is `Erases.strengthen_vlet`.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/--
Context-surgery witness for let-value thinning: `ThinVLet x deps A e₀ Δ₁ Δ` holds
when `Δ₁` is `Δ` with the fvar-tagged let entry `(some (x, deps), .vlet A e₀)`
inserted somewhere below a (possibly empty) prefix of bvar-tagged (`none`)
entries — exactly the contexts reachable from
`(some (x, deps), .vlet A e₀) :: Δ` by the binder rules of `Erases`/`TrExprS`,
which only ever cons `none`-tagged entries.

Mirrors the shape of lean4lean's `VLCtx.InstLet`/`VLCtx.Abstract` (without
index bookkeeping: a `.vlet` has `depth = 0` and the entry keeps its fvar tag,
so neither source bvar indices nor target `VExpr`s shift).
-/
inductive ThinVLet (x : FVarId) (deps : List FVarId) (A e₀ : VExpr) :
    VLCtx → VLCtx → Prop where
  | zero : ThinVLet x deps A e₀ ((some (x, deps), .vlet A e₀) :: Δ) Δ
  | succ : ThinVLet x deps A e₀ Δ₁ Δ →
      ThinVLet x deps A e₀ ((none, d) :: Δ₁) ((none, d) :: Δ)

/-- Dropping a `.vlet` entry leaves the pure typing context untouched
(`VLCtx.toCtx` skips `.vlet` entries). This is what lets the `box` case
transport its `Erasable` witness verbatim. -/
protected theorem ThinVLet.toCtx {x : FVarId} {deps : List FVarId} {A e₀ : VExpr}
    {Δ₁ Δ : VLCtx} (W : ThinVLet x deps A e₀ Δ₁ Δ) :
    Δ₁.toCtx = Δ.toCtx := by
  induction W with
  | zero => rfl
  | @succ _ _ d _ ih =>
    match d with
    | .vlam ty => exact congrArg (ty :: ·) ih
    | .vlet _ _ => exact ih

/-- Dropping the entry removes exactly `x` from the fvar list (the surgery's `succ`
steps cons only `none`-tagged entries, which contribute no fvar). Mirror of
lean4lean's `VLCtx.Abstract.fvars_eq`; it is what carries the `Erases.fixvar` leaf's
`hfresh` premise across the thinning. -/
protected theorem ThinVLet.fvars_eq {x : FVarId} {deps : List FVarId} {A e₀ : VExpr}
    {Δ₁ Δ : VLCtx} (W : ThinVLet x deps A e₀ Δ₁ Δ) : Δ₁.fvars = x :: Δ.fvars := by
  induction W with
  | zero => rfl
  | succ _ ih => exact ih

/-- `VLCtx.find?` is unchanged by dropping the unused entry, for every variable
other than the dropped fvar itself: the fvar tag passes bvar lookups through
unshifted, and the `.vlet`'s `depth = 0` makes the result's `liftN` a no-op. -/
protected theorem ThinVLet.find? {x : FVarId} {deps : List FVarId} {A e₀ : VExpr}
    {Δ₁ Δ : VLCtx} (W : ThinVLet x deps A e₀ Δ₁ Δ)
    {v : Nat ⊕ FVarId} (hv : v ≠ .inr x) :
    Δ₁.find? v = Δ.find? v := by
  induction W generalizing v with
  | @zero Δ₀ =>
    have hnext : VLCtx.next (some (x, deps)) v = some v := by
      obtain i | fv := v
      · rfl
      · have hne : (x == fv) = false :=
          beq_eq_false_iff_ne.2 fun h => hv (by rw [h])
        simp [VLCtx.next, hne]
    simp only [VLCtx.find?, hnext, VLocalDecl.depth]
    cases h : VLCtx.find? Δ₀ v with
    | none => rfl
    | some p => obtain ⟨e', A'⟩ := p; simp
  | succ _ ih =>
    obtain (_ | i) | fv := v
    · rfl
    · simp only [VLCtx.find?, VLCtx.next]
      rw [ih (v := .inl i) (by nofun)]
    · simp only [VLCtx.find?, VLCtx.next]
      rw [ih (v := .inr fv) hv]

/--
Thinning for lean4lean's translation: a `TrExprS` derivation survives dropping
an unused fvar-tagged `.vlet` entry, **with the same `VExpr` witness** (nothing
shifts: `ThinVLet.find?` is an equality and `ThinVLet.toCtx` transports the
typing side premises verbatim). Structure mirrors lean4lean's `TrExprS.abstract`.

This discharges the lean4lean side premises of `Erases.thin_vlet`
(`box`'s translation witness, `lam`/`letE`'s `hty`/`hval`). Preserving the
witness on the nose is what keeps the binder cases of the `Erases` induction
closed under the *same* extended contexts, avoiding any
`TrExprS.uniq`/`Erasable.defeq` transport.
-/
theorem TrExprS.thin_vlet {env : VEnv} {Us : List Name}
    {x : FVarId} {deps : List FVarId} {A e₀ : VExpr} {Δ₁ Δ : VLCtx}
    (W : ThinVLet x deps A e₀ Δ₁ Δ)
    {e : Expr} {e' : VExpr} (H : TrExprS env Us Δ₁ e e')
    (hx : FVarsIn (· ≠ x) e) :
    TrExprS env Us Δ e e' := by
  induction H generalizing Δ with
  | @bvar _ _ _ i h1 => exact .bvar (W.find? (v := .inl i) (by nofun) ▸ h1)
  | @fvar _ _ _ fv h1 =>
    exact .fvar (W.find? (v := .inr fv) (fun h => hx (Sum.inr.inj h)) ▸ h1)
  | sort h1 => exact .sort h1
  | const h1 h2 h3 => exact .const h1 h2 h3
  | app h1 h2 _ _ ih1 ih2 =>
    exact .app (W.toCtx ▸ h1) (W.toCtx ▸ h2) (ih1 W hx.1) (ih2 W hx.2)
  | lam h1 _ _ ih1 ih2 =>
    exact .lam (W.toCtx ▸ h1) (ih1 W hx.1) (ih2 W.succ hx.2)
  | forallE h1 h2 _ _ ih1 ih2 =>
    exact .forallE (W.toCtx ▸ h1) (W.toCtx ▸ h2) (ih1 W hx.1) (ih2 W.succ hx.2)
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    exact .letE (W.toCtx ▸ h1) (ih1 W hx.1) (ih2 W hx.2.1) (ih3 W.succ hx.2.2)
  | lit h1 _ ih => exact .lit h1 (ih W .toConstructor)
  | mdata _ ih => exact .mdata (ih W hx)
  | proj _ h2 ih => exact .proj (ih W hx) (W.toCtx ▸ h2)

/-- `FVarsIn` restricted along an application spine built by `List.foldl Expr.app`
(the form the `ctor`/`cases` rules of `Erases` use for their sources). -/
theorem fvarsIn_foldl_app {P : FVarId → Prop} {args : List Expr} {f : Expr}
    (h : FVarsIn P (args.foldl Expr.app f)) :
    FVarsIn P f ∧ ∀ a ∈ args, FVarsIn P a := by
  induction args generalizing f with
  | nil => exact ⟨h, nofun⟩
  | cons a as ih =>
    have ⟨hfa, has⟩ := ih h
    refine ⟨hfa.1, fun b hb => ?_⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · exact hfa.2
    · exact has _ hb

/--
**Let-value thinning for `Erases`, at depth** (the induction-ready form): an
`Erases` derivation at a context containing an unused fvar-tagged `.vlet` entry
(below a prefix of bvar entries, per `ThinVLet`) also holds with that entry
dropped — same source, same target.

No `env.Ordered`/`VLCtx.WF`/closedness premises are needed: `Erases.bvar`/`.fvar`
are context-free rules, and every lean4lean side premise (`box`'s
`TrExprS`+`Erasable`, `lam`/`letE`'s `TrExprS`) transports on the nose via
`TrExprS.thin_vlet` and `ThinVLet.toCtx`.
-/
theorem Erases.thin_vlet {env : VEnv} {Us : List Name} {Γ : ErasureCtx}
    {x : FVarId} {deps : List FVarId} {A e₀ : VExpr} {Δ₁ Δ : VLCtx}
    (W : ThinVLet x deps A e₀ Δ₁ Δ)
    {e : Expr} {t : LBTerm} (H : Erases env Us Γ Δ₁ e t)
    (sc : FVarsIn (· ≠ x) e) :
    Erases env Us Γ Δ e t := by
  induction H generalizing Δ with
  | box htr her => exact .box (TrExprS.thin_vlet W htr sc) (W.toCtx ▸ her)
  | lit hcl _ ih => exact .lit hcl (ih W .toConstructor)
  | bvar i => exact .bvar i
  | fvar y => exact .fvar y
  | const n us kn h hctor hcases => exact .const n us kn h hctor hcases
  | app _ _ ihf iha => exact .app (ihf W sc.1) (iha W sc.2)
  | lam hty _ ihb => exact .lam (TrExprS.thin_vlet W hty sc.1) (ihb W.succ sc.2)
  | letE hty hval _ _ ihv ihb =>
    exact .letE (TrExprS.thin_vlet W hty sc.1) (TrExprS.thin_vlet W hval sc.2.1)
      (ihv W sc.2.1) (ihb W.succ sc.2.2)
  | ctor_head cn us iid cidx hc => exact .ctor_head cn us iid cidx hc
  | ctor cn us iid cidx hc hlen _ ihargs =>
    have ⟨_, hall⟩ := fvarsIn_foldl_app sc
    exact .ctor cn us iid cidx hc hlen fun i hi =>
      ihargs i hi W (hall _ (List.getElem_mem hi))
  | cases con us iid numParams pre hc hpre hnfs _ hlen hnlen harity _ ihd ihalts =>
    have ⟨_, hall⟩ := fvarsIn_foldl_app sc
    exact .cases con us iid numParams pre hc hpre hnfs (ihd W (hall _ (.head _))) hlen
      hnlen harity fun j hj => ihalts j hj W (hall _ (.tail _ (List.getElem_mem hj)))
  | fixvar nm us y hfx hctor hcases hfresh =>
    rw [W.fvars_eq] at hfresh
    exact .fixvar nm us y hfx hctor hcases fun hm => hfresh (List.mem_cons_of_mem _ hm)
  | const_fix nm us hrec hctor hcases hshift hsubst htobv =>
    exact .const_fix nm us hrec hctor hcases hshift hsubst htobv
  | @fix Δc idx nm tty tb tbi nms srcs defs hidx hnlen hslen hsrc hreg hrarg
      hlift hinst habsl hshift hsubst htobv hbodies _ihb =>
      -- Thinning changes only the (conclusion) context; the fix source/target and the
      -- fix bodies (context-uniform, `∀ Δf`) are untouched, so the rule re-applies.
      exact .fix idx hidx hnlen hslen hsrc hreg hrarg hlift hinst habsl hshift hsubst htobv
        hbodies

/--
**Let-value thinning** (the bridge-facing corollary): the shipping `visitLet`
opens the let-binder into a fresh fvar `x` *before* erasing the let-value, so the
bridge's induction yields `Erases` for the value at the `x`-extended context,
while `Erases.letE` needs it at the outer `Δ`. Since the value `e` cannot mention
the fresh `x` (`FVarsIn (· ≠ x) e`, available at the call site by freshness),
the entry can be dropped.

Both source `e` and target `t` are unchanged, and no well-formedness premises
are required — see `Erases.thin_vlet`.
-/
theorem Erases.strengthen_vlet {env : VEnv} {Us : List Name} {Γ : ErasureCtx}
    {x : FVarId} {deps : List FVarId} {A e₀ : VExpr} {Δ : VLCtx}
    {e : Expr} {t : LBTerm}
    (H : Erases env Us Γ ((some (x, deps), .vlet A e₀) :: Δ) e t)
    (sc : FVarsIn (· ≠ x) e) :
    Erases env Us Γ Δ e t :=
  H.thin_vlet .zero sc

/-! ### Non-vacuity

Concrete witnesses that the hypothesis set is jointly satisfiable and that the
lemma fires. The hypotheses are *constructed*, not assumed, so these also show
satisfiability (for arbitrary `env`/`Us`/`Γ`/`Δ` — no side conditions beyond
`y ≠ x`). -/

/-- Non-vacuity (fvar): from a real derivation
`Erases env Us Γ ((some (x, deps), .vlet A e₀) :: Δ) (.fvar y) (.fvar y)`
with `y ≠ x`, conclude the same at the outer `Δ`. -/
example (env : VEnv) (Us : List Name) (Γ : ErasureCtx) (Δ : VLCtx)
    (x y : FVarId) (deps : List FVarId) (A e₀ : VExpr) (hyx : y ≠ x) :
    Erases env Us Γ Δ (.fvar y) (.fvar y) :=
  have H : Erases env Us Γ ((some (x, deps), .vlet A e₀) :: Δ) (.fvar y) (.fvar y) :=
    .fvar y
  H.strengthen_vlet hyx

/-- Non-vacuity (binder + lean4lean side premise): a `lam` whose type erases via a
real `TrExprS` derivation (`.sort`), exercising both the `TrExprS.thin_vlet`
side-premise transport and the depth-generalization (`ThinVLet.succ`) under the
binder. -/
example (env : VEnv) (Us : List Name) (Γ : ErasureCtx) (Δ : VLCtx)
    (x : FVarId) (deps : List FVarId) (A e₀ : VExpr)
    (name : Name) (bi : BinderInfo) :
    Erases env Us Γ Δ (.lam name (.sort .zero) (.bvar 0) bi)
      (.lambda (nameToBinder name) (.bvar 0)) :=
  have H : Erases env Us Γ ((some (x, deps), .vlet A e₀) :: Δ)
      (.lam name (.sort .zero) (.bvar 0) bi) (.lambda (nameToBinder name) (.bvar 0)) :=
    .lam (ty' := .sort .zero) (.sort rfl) (.bvar 0)
  H.strengthen_vlet ⟨rfl, trivial⟩

/-! ## fvar weakening for `Erases`

The dual move to the thinning above: instead of *dropping* an unused entry, *add*
fvar entries. The bridge needs this whenever a sub-derivation was produced at the
run's context and has to be replayed at a later, larger one (`visitExpr` never
shrinks the local context, so every recursive call sits at an fvar-extension of
its caller's).

### Why the well-formedness premise is `VLCtx.FVWF`, not `VLCtx.WF`

The obvious route — mirror `erases_shift` and swap `TrExprS.weakBV` for
lean4lean's `TrExprS.weakFV` — **does not close**. `TrExprS.weakFV` demands
`VLCtx.WF env Us.length Δ'`, i.e. full typing well-formedness, and the binder
cases of the `Erases` induction descend to `(none, .vlam ty') :: Δ'`. Re-establishing
`VLCtx.WF` of that cons requires `env.IsType Us.length Δ'.toCtx ty'` — a *typing*
fact about the binder type. `Erases.lam` carries only `TrExprS env Us Δ ty ty'`, no
`IsType`, so the induction hypothesis cannot be fed and the proof dies under the
first `λ`.

The fix is to notice that `VLCtx.WF` is far more than the weakening actually uses.
Reading lean4lean's proofs: `VLCtx.FVLift'.find?` consumes `hΔ'` only as its tail
(`hΔ'.1`) and as `hΔ'.fvars_nodup`, and `TrExprS.weakFV'` consumes it only to feed
`find?` and to rebuild the extended-context well-formedness. All of that is
available from `VLCtx.FVWF` — the fvar-only half of `VLCtx.WF`, same `.1` shape,
same nodup consequence — and, crucially, `FVWF` extends **freely** under a
`(none, d)` cons (`⟨hΔ', nofun⟩`), with no typing obligation at all.

So the four declarations below are `FVWF`-only re-proofs of lean4lean's
`VLCtx.WF.fvars_nodup` / `VLCtx.FVLift'.find?` / `VLCtx.FVLift.find?` /
`TrExprS.weakFV'` / `TrExprS.weakFV` (`Lean4Lean/Verify/Typing/Lemmas.lean`),
near-verbatim copies with the `WF` hypothesis weakened to `FVWF`. They live in
`LeanToLambdaBox.VLCtx.*` / `LeanToLambdaBox.TrExprS.*`, so they do not clash with
the lean4lean originals. Call sites holding a real `VLCtx.WF` convert with
`VLCtx.WF.fvwf`.
-/

/-- The nodup half of `VLCtx.WF.fvars_nodup`, from the fvar-only `VLCtx.FVWF`.
This is one of exactly two things lean4lean's `VLCtx.FVLift'.find?` asks of its
well-formedness premise (the other is the tail, `hΔ'.1`), which is what lets the
whole `weakFV` chain run on `FVWF`. Mirrors `Lean4Lean.VLCtx.WF.fvars_nodup`. -/
theorem VLCtx.FVWF.fvars_nodup : ∀ {Δ : VLCtx}, Δ.FVWF → Δ.fvars.Nodup
  | [], _ => .nil
  | (none, _) :: Δ, ⟨hΔ, _⟩ => VLCtx.FVWF.fvars_nodup (Δ := Δ) hΔ
  | (some (fv, _), _) :: Δ, ⟨hΔ, h⟩ => by
    suffices fv ∉ VLCtx.fvars Δ from
      (VLCtx.FVWF.fvars_nodup hΔ).cons (fun _ h (e : fv = _) => this (e ▸ h))
    exact (h _ _ rfl).1

/-- `VLCtx.find?` transports along an `FVLift'`, on the `FVWF`-only premise.
Verbatim copy of lean4lean's `VLCtx.FVLift'.find?` with `(hΔ' : Δ'.WF env U)`
replaced by `(hΔ' : Δ'.FVWF)`: the original proof touches `hΔ'` only through
`hΔ'.1` and `hΔ'.fvars_nodup`, both of which `FVWF` supplies, so nothing else in
the argument changes. Dropping the typing half is what makes the binder cases of
`Erases.weakFV` re-establishable (see the section note). -/
protected theorem VLCtx.FVLift'.find?_fvwf {Δ Δ' : VLCtx} {dk : Nat} {n : Lift} {k : Nat}
    {v : Nat ⊕ FVarId} {e A : VExpr}
    (W : VLCtx.FVLift' Δ Δ' dk n k) (hΔ' : Δ'.FVWF)
    (H : VLCtx.find? Δ v = some (e, A)) :
    VLCtx.find? Δ' v = some (e.lift' (n.consN k), A.lift' (n.consN k)) := by
  induction W generalizing v e A with
  | refl => simp [H]
  | skip_fvar fv' _ W ih =>
    let (fv', deps) := fv'; simp [VLCtx.find?]
    cases v with simp [VLCtx.next]
    | inl =>
      refine ⟨_, _, ih hΔ'.1 H, ?_⟩
      simp [← VExpr.lift'_consN_skipN, ← VExpr.lift'_comp, Lift.comp_skipN]
    | inr fv =>
      cases eq : fv' == fv <;> simp
      · refine ⟨_, _, ih hΔ'.1 H, ?_⟩
        simp [← VExpr.lift'_consN_skipN, ← VExpr.lift'_comp, Lift.comp_skipN]
      · refine ((List.pairwise_cons.1 (VLCtx.FVWF.fvars_nodup hΔ')).1 fv' ?_ rfl).elim
        exact W.fvars_sublist.subset ((beq_iff_eq ..).1 eq ▸ VLCtx.find?_eq_some.1 ⟨_, H⟩)
  | cons_fvar fv' d _ W ih =>
    let (fv', deps) := fv'; revert H; simp [VLCtx.find?]
    obtain i | fv := v <;> simp [VLCtx.next] <;>
      [skip; cases eq : fv' == fv <;> simp] <;>
      [(rintro _ _ H rfl rfl; refine ⟨_, _, ih hΔ'.1 H, ?_⟩);
       (rintro _ _ H rfl rfl; refine ⟨_, _, ih (v := .inr fv) hΔ'.1 H, ?_⟩);
       rintro rfl rfl] <;>
      open VLocalDecl in
      cases d <;> simp [value, type, depth, lift', VExpr.lift,
        ← VExpr.lift'_consN_skipN, ← VExpr.lift'_comp]
  | cons_bvar d _ ih =>
    simp [VLCtx.find?] at H ⊢
    obtain ⟨_|i⟩ | fv := v <;> simp [VLCtx.next] at H ⊢ <;>
      [(obtain ⟨rfl, rfl⟩ := H);
       (obtain ⟨e, A, H, rfl, rfl⟩ := H
        refine ⟨_, _, ih (v := .inl i) hΔ'.1 H, ?_⟩);
       (obtain ⟨e, A, H, rfl, rfl⟩ := H
        refine ⟨_, _, ih (v := .inr fv) hΔ'.1 H, ?_⟩)] <;>
      open VLocalDecl in
      cases d <;> simp [value, type, depth, lift', VExpr.lift,
        ← VExpr.lift'_consN_skipN, ← VExpr.lift'_comp]

/-- The `FVLift` (plain `Nat` shift) form of `VLCtx.FVLift'.find?_fvwf`. Copy of
lean4lean's `VLCtx.FVLift.find?`, which is just the `FVLift'` lemma composed with
`FVLift.toFVLift'`; recorded here so the `FVWF` variants form the same pair the
originals do. -/
protected theorem VLCtx.FVLift.find?_fvwf {Δ Δ' : VLCtx} {dk n k : Nat}
    {v : Nat ⊕ FVarId} {e A : VExpr}
    (W : VLCtx.FVLift Δ Δ' dk n k) (hΔ' : Δ'.FVWF)
    (H : VLCtx.find? Δ v = some (e, A)) :
    VLCtx.find? Δ' v = some (e.liftN n k, A.liftN n k) := by
  simpa [VExpr.lift'_consN_skipN] using VLCtx.FVLift'.find?_fvwf W.toFVLift' hΔ' H

/-- lean4lean's `TrExprS.weakFV'`, re-proved on the `FVWF`-only premise: the
translation of a source `Expr` survives an fvar-extension of the `VLCtx`, with its
`VExpr` witness lifted by `n.consN k`.

The proof is lean4lean's verbatim, with two changes forced by the weaker premise:
`find?` is discharged by `VLCtx.FVLift'.find?_fvwf`, and the `lam`/`forallE`/`letE`
arms pass `⟨hΔ', nofun⟩` (an `FVWF` cons, which needs nothing about the binder
type) where the original passes `⟨hΔ', nofun, h1⟩` (a `WF` cons, which needs the
`IsType` witness `h1`). That second change is the whole point: `Erases.lam` has no
`IsType` to offer. -/
theorem TrExprS.weakFV'_fvwf {env : VEnv} (henv : env.Ordered) {Us : List Name}
    {Δ Δ' : VLCtx} {dk : Nat} {n : Lift} {k : Nat}
    (W : VLCtx.FVLift' Δ Δ' dk n k) (hΔ' : Δ'.FVWF)
    {e : Expr} {e' : VExpr} (H : TrExprS env Us Δ e e') :
    TrExprS env Us Δ' e (e'.lift' (n.consN k)) := by
  induction H generalizing Δ' dk k with
  | bvar h1 => exact .bvar (VLCtx.FVLift'.find?_fvwf W hΔ' h1)
  | fvar h1 => exact .fvar (VLCtx.FVLift'.find?_fvwf W hΔ' h1)
  | sort h1 => exact .sort h1
  | const h1 h2 h3 => exact .const h1 h2 h3
  | app h1 h2 _ _ ih1 ih2 =>
    exact .app (h1.weak' henv W.toCtx) (h2.weak' henv W.toCtx) (ih1 W hΔ') (ih2 W hΔ')
  | lam h1 _ _ ih1 ih2 =>
    have h1 := h1.weak' henv W.toCtx
    exact .lam h1 (ih1 W hΔ') (ih2 (W.cons_bvar _) ⟨hΔ', nofun⟩)
  | forallE h1 h2 _ _ ih1 ih2 =>
    have h1 := h1.weak' henv W.toCtx
    have h2 := h2.weak' henv W.toCtx.cons
    exact .forallE h1 h2 (ih1 W hΔ') (ih2 (W.cons_bvar _) ⟨hΔ', nofun⟩)
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    have h1 := h1.weak' henv W.toCtx
    exact .letE h1 (ih1 W hΔ') (ih2 W hΔ') (ih3 (W.cons_bvar _) ⟨hΔ', nofun⟩)
  | lit h1 _ ih => exact .lit h1 (ih W hΔ')
  | mdata _ ih => exact .mdata (ih W hΔ')
  | proj _ h2 ih => exact .proj (ih W hΔ') (h2.weak' W.toCtx)

/-- The `FVLift` form of `TrExprS.weakFV'_fvwf` — lean4lean's `TrExprS.weakFV` on the
`FVWF`-only premise. This is the exact shape the `box`/`lam`/`letE` cases of
`erases_weakFV` need for their lean4lean side premises. -/
theorem TrExprS.weakFV_fvwf {env : VEnv} (henv : env.Ordered) {Us : List Name}
    {Δ Δ' : VLCtx} {dk n k : Nat}
    (W : VLCtx.FVLift Δ Δ' dk n k) (hΔ' : Δ'.FVWF)
    {e : Expr} {e' : VExpr} (H : TrExprS env Us Δ e e') :
    TrExprS env Us Δ' e (e'.liftN n k) := by
  simpa [VExpr.lift'_consN_skipN] using TrExprS.weakFV'_fvwf henv W.toFVLift' hΔ' H

/--
**fvar weakening for `Erases`.** An erasure derivation replays verbatim at any
fvar-extension of its `VLCtx`.

Three things to note about the statement:

* **Nothing moves on either side.** Unlike `erases_shift` (which lifts the source
  by `liftLooseBVars'` and the target by `LBTerm.shift`), here the source `Expr`
  and the target `LBTerm` are *untouched*: an `FVLift` only inserts fvar-tagged
  entries and re-lifts the hidden `VExpr` witnesses, and neither language's
  de Bruijn indices see fvar entries. That is why the `ctor`/`cases` cases — the
  painful ones in `erases_shift`, where the `foldl Expr.app` spine had to be
  pushed through the lift — are here a plain appeal to the IH.

* **`hfv` and the `fixvar` leaf.** Every rule but one transports structurally.
  `Erases.fixvar` carries `hfresh : x ∉ Δ.fvars`, and weakening *adds* fvars, so
  freshness at `Δ` says nothing about `Δ'` — this is the one premise an
  fvar-extension can genuinely destroy. `hfv` is exactly the missing fact,
  demanded once for the whole derivation: no fixvar of `Γ` occurs in the target
  context. At a top-level `Γ` (where `Γ.fixvars = fun _ => none`) it is discharged
  by `simp`; inside a mutual block it is the run's own freshness discipline
  (`visitMutual` mints the block's fixvars before any binder is opened — the
  bridge invariant `BridgeInv.fixfresh`).

* **`FVWF`, not `VLCtx.WF`.** lean4lean's `TrExprS.weakFV` wants full typing
  well-formedness of `Δ'`, and that hypothesis cannot survive this induction:
  the `lam`/`letE` cases descend to `(none, .vlam ty') :: Δ'`, whose `VLCtx.WF`
  needs `env.IsType Us.length Δ'.toCtx ty'`, and `Erases.lam` carries only
  `TrExprS env Us Δ ty ty'` — no `IsType` anywhere. `VLCtx.FVWF` is all that
  lean4lean's `find?`/`weakFV` proofs actually consume (tail + `fvars` nodup) and
  it conses **freely** under a `(none, _)` entry, so the induction goes through.
  Callers holding a real `VLCtx.WF` convert with `VLCtx.WF.fvwf`.

`hfv` itself transports under binders for free, since
`VLCtx.fvars ((none, d) :: Δ') = VLCtx.fvars Δ'` definitionally.
-/
theorem erases_weakFV {env : VEnv} (henv : env.Ordered) {Us : List Name} {Γ : ErasureCtx}
    {Δ Δ' : VLCtx} {dk n k : Nat}
    (W : VLCtx.FVLift Δ Δ' dk n k) (hΔ' : Δ'.FVWF)
    (hfv : ∀ (nm : Name) (x : FVarId), Γ.fixvars nm = some x → x ∉ Δ'.fvars)
    {e : Expr} {t : LBTerm} (h : Erases env Us Γ Δ e t) :
    Erases env Us Γ Δ' e t := by
  induction h generalizing Δ' dk k with
  | box htr her => exact .box (TrExprS.weakFV_fvwf henv W hΔ' htr) (her.weakN henv W.toCtx)
  | lit hcl _ ih => exact .lit hcl (ih W hΔ' hfv)
  | bvar i => exact .bvar i
  | fvar x => exact .fvar x
  | const n us kn h hctor hcases => exact .const n us kn h hctor hcases
  | app _ _ ihf iha => exact .app (ihf W hΔ' hfv) (iha W hΔ' hfv)
  | lam hty _ ihb =>
      -- `(none, .vlam ty').liftN n k` is `.vlam (ty'.liftN n k)` on the nose, so the
      -- weakened `hty` is exactly the binder type the IH's context mentions.
      exact .lam (TrExprS.weakFV_fvwf henv W hΔ' hty) (ihb (W.cons_bvar _) ⟨hΔ', nofun⟩ hfv)
  | letE hty hval _ _ ihv ihb =>
      exact .letE (TrExprS.weakFV_fvwf henv W hΔ' hty) (TrExprS.weakFV_fvwf henv W hΔ' hval)
        (ihv W hΔ' hfv) (ihb (W.cons_bvar _) ⟨hΔ', nofun⟩ hfv)
  | ctor cn us iid cidx hc hlen _ ihargs =>
      -- The source spine is not rewritten (nothing lifts), so this is the IH and nothing else.
      exact .ctor cn us iid cidx hc hlen fun i hi => ihargs i hi W hΔ' hfv
  | ctor_head cn us iid cidx hc => exact .ctor_head cn us iid cidx hc
  | cases con us iid numParams pre hc hpre hnfs _ hlen hnlen harity _ ihd ihalts =>
      exact .cases con us iid numParams pre hc hpre hnfs (ihd W hΔ' hfv) hlen hnlen harity
        fun j hj => ihalts j hj W hΔ' hfv
  | fixvar nm us x hfx hctor hcases _ =>
      -- The one non-structural rule: weakening adds fvars, so the rule's own `hfresh` is
      -- useless at `Δ'` and `hfv` supplies the replacement.
      exact .fixvar nm us x hfx hctor hcases (hfv nm x hfx)
  | const_fix nm us hrec hctor hcases hshift hsubst htobv =>
      exact .const_fix nm us hrec hctor hcases hshift hsubst htobv
  | @fix Δc idx nm tty tb tbi nms srcs defs hidx hnlen hslen hsrc hreg hrarg
      hlift hinst habsl hshift hsubst htobv hbodies _ihb =>
      -- Only the (conclusion) context moves; the block and its `∀ Δf` bodies are untouched.
      exact .fix idx hidx hnlen hslen hsrc hreg hrarg hlift hinst habsl hshift hsubst htobv
        hbodies

/-! ### Non-vacuity (fvar weakening)

Same discipline as above: every hypothesis of `erases_weakFV` is *constructed*, so
the example also witnesses joint satisfiability of `FVLift` + `FVWF` + `hfv`. -/

/-- Non-vacuity: a real `lam` derivation at the empty `VLCtx` (its binder type
erasing via a genuine `TrExprS.sort`) transported to a one-fvar context
`[(some (x, []), .vlam A)]`. The `FVLift` is `VLCtx.FVLift.from_nil` (the context
has no bvar entries), the `FVWF` is the freeness of a single fvar over the empty
context, and `hfv` is discharged because `Γ.withFixvars (fun _ => none)` registers
no fixvar at all. -/
example (env : VEnv) (henv : env.Ordered) (Us : List Name) (Γ : ErasureCtx)
    (x : FVarId) (A : VExpr) (name : Name) (bi : BinderInfo) :
    Erases env Us (Γ.withFixvars fun _ => none) [(some (x, []), .vlam A)]
      (.lam name (.sort .zero) (.bvar 0) bi) (.lambda (nameToBinder name) (.bvar 0)) :=
  have H : Erases env Us (Γ.withFixvars fun _ => none) []
      (.lam name (.sort .zero) (.bvar 0) bi) (.lambda (nameToBinder name) (.bvar 0)) :=
    .lam (ty' := .sort .zero) (.sort rfl) (.bvar 0)
  have hΔ' : VLCtx.FVWF [(some (x, []), .vlam A)] := ⟨trivial, by rintro _ _ ⟨⟩; simp⟩
  erases_weakFV henv (VLCtx.FVLift.from_nil rfl) hΔ' (by simp) H

/-! ## Unrestricted weakening for closed, fvar-free terms

`erases_weakFV` still asks two things of the target context: `Δ'.FVWF`, and — when
one wants to start from the empty context — `Δ'.NoBV` (that is what
`VLCtx.FVLift.from_nil` needs). Neither is available where the metatheory actually
needs weakening: `Erases.fix`'s `hbodies` premise (`Erases.lean`) quantifies over
`∀ Δf : VLCtx`, *unrestricted* — bvar entries, and fvar entries that shadow each
other, included. So `erases_weakFV` alone cannot rebuild `hbodies`, which is the
concrete obstruction to `EnvErasureRec.erases_fix_of_open`.

What gets us there is the data the recursive-definition setting already carries:
top-level bodies are **closed** and **fvar-free** sources erasing to **`LBClosed`**
targets (`erases_fix_of_open`'s `heclosed`/`henofv`/`hsrcfv`). Under those two
conditions weakening holds at *every* `Δ`, with no context hypothesis whatsoever:

* a bvar-entry cons is already free — `erases_shift` takes no hypothesis on its
  target context at all, and on a closed source and an `LBClosed` target both of
  its lifts are the identity, so the conclusion lands back on the same `e`/`t`;
* an fvar-entry cons needed `FVWF` for exactly one reason: `VLCtx.FVLift'.find?`
  must rule out a *shadowing* fvar in its `.inr` branch, and nodup is what does
  that. A source with no free variables never performs an `.inr` lookup, so that
  branch is unreachable and the hypothesis is dead weight.

Hence the `_nofvars` chain below: the same three lemmas as the `_fvwf` chain, but
with the context hypothesis **dropped** rather than weakened, in exchange for
carrying `Lean.Expr.FVarsIn (fun _ => False)` on the source through the induction.
-/

/-- `VLCtx.find?` transports along an `FVLift'` for **bvar** lookups, with no
hypothesis on the target context at all.

This is lean4lean's `VLCtx.FVLift'.find?` restricted to `v = .inl i`, which is a
strictly easier statement: the `skip_fvar`/`cons_fvar` cases only ever needed
`fvars` nodup in their `.inr` branch (to refute a shadowing fvar), and `.inl`
lookups never reach it — `VLCtx.next` maps `.inl` to `.inl` past every fvar entry,
and `cons_bvar` either stops at the binder or recurses on `.inl`. Dropping the
hypothesis here is what makes the whole `_nofvars` chain context-free. -/
protected theorem VLCtx.FVLift'.find?_inl {Δ Δ' : VLCtx} {dk : Nat} {n : Lift} {k : Nat}
    {i : Nat} {e A : VExpr}
    (W : VLCtx.FVLift' Δ Δ' dk n k) (H : VLCtx.find? Δ (.inl i) = some (e, A)) :
    VLCtx.find? Δ' (.inl i) = some (e.lift' (n.consN k), A.lift' (n.consN k)) := by
  induction W generalizing i e A with
  | refl => simp [H]
  | skip_fvar fv' _ _ ih =>
    let (fv', deps) := fv'; simp [VLCtx.find?, VLCtx.next]
    refine ⟨_, _, ih H, ?_⟩
    simp [← VExpr.lift'_consN_skipN, ← VExpr.lift'_comp, Lift.comp_skipN]
  | cons_fvar fv' d _ _ ih =>
    let (fv', deps) := fv'; revert H; simp [VLCtx.find?, VLCtx.next]
    rintro _ _ H rfl rfl
    refine ⟨_, _, ih H, ?_⟩
    open VLocalDecl in
    cases d <;> simp [depth, ← VExpr.lift'_consN_skipN, ← VExpr.lift'_comp]
  | cons_bvar d _ ih =>
    simp [VLCtx.find?] at H ⊢
    obtain _ | i := i <;> simp [VLCtx.next] at H ⊢ <;>
      [(obtain ⟨rfl, rfl⟩ := H);
       (obtain ⟨e, A, H, rfl, rfl⟩ := H
        refine ⟨_, _, ih H, ?_⟩)] <;>
      open VLocalDecl in
      cases d <;> simp [value, type, depth, lift', VExpr.lift,
        ← VExpr.lift'_consN_skipN, ← VExpr.lift'_comp]

/-- lean4lean's `TrExprS.weakFV'` with the well-formedness premise on the target
context **removed entirely**, paid for by an fvar-freeness premise on the source.

Same proof as `TrExprS.weakFV'_fvwf`, with two arms changed: `bvar` goes through
`VLCtx.FVLift'.find?_inl` (no hypothesis), and `fvar` is now *impossible* — a
source with `FVarsIn (fun _ => False)` has no free variable to look up, which is
precisely why the shadowing side condition disappeared. Every other arm splits
`hfvf` structurally, exactly as `TrExprS.thin_vlet` above does with its own
`FVarsIn` premise; `lit` re-establishes it for the unfolding via
`FVarsIn.toConstructor` (which holds for *any* predicate). -/
theorem TrExprS.weakFV'_nofvars {env : VEnv} (henv : env.Ordered) {Us : List Name}
    {Δ Δ' : VLCtx} {dk : Nat} {n : Lift} {k : Nat}
    (W : VLCtx.FVLift' Δ Δ' dk n k)
    {e : Expr} {e' : VExpr} (H : TrExprS env Us Δ e e')
    (hfvf : FVarsIn (fun _ => False) e) :
    TrExprS env Us Δ' e (e'.lift' (n.consN k)) := by
  induction H generalizing Δ' dk k with
  | bvar h1 => exact .bvar (VLCtx.FVLift'.find?_inl W h1)
  | fvar _ => exact (hfvf : False).elim
  | sort h1 => exact .sort h1
  | const h1 h2 h3 => exact .const h1 h2 h3
  | app h1 h2 _ _ ih1 ih2 =>
    exact .app (h1.weak' henv W.toCtx) (h2.weak' henv W.toCtx) (ih1 W hfvf.1) (ih2 W hfvf.2)
  | lam h1 _ _ ih1 ih2 =>
    exact .lam (h1.weak' henv W.toCtx) (ih1 W hfvf.1) (ih2 (W.cons_bvar _) hfvf.2)
  | forallE h1 h2 _ _ ih1 ih2 =>
    exact .forallE (h1.weak' henv W.toCtx) (h2.weak' henv W.toCtx.cons)
      (ih1 W hfvf.1) (ih2 (W.cons_bvar _) hfvf.2)
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    exact .letE (h1.weak' henv W.toCtx) (ih1 W hfvf.1) (ih2 W hfvf.2.1)
      (ih3 (W.cons_bvar _) hfvf.2.2)
  | lit h1 _ ih => exact .lit h1 (ih W FVarsIn.toConstructor)
  | mdata _ ih => exact .mdata (ih W hfvf)
  | proj _ h2 ih => exact .proj (ih W hfvf) (h2.weak' W.toCtx)

/-- The `FVLift` form of `TrExprS.weakFV'_nofvars` — the shape the `box`/`lam`/`letE`
cases of `erases_weakFV_nofvars` consume. -/
theorem TrExprS.weakFV_nofvars {env : VEnv} (henv : env.Ordered) {Us : List Name}
    {Δ Δ' : VLCtx} {dk n k : Nat}
    (W : VLCtx.FVLift Δ Δ' dk n k)
    {e : Expr} {e' : VExpr} (H : TrExprS env Us Δ e e')
    (hfvf : FVarsIn (fun _ => False) e) :
    TrExprS env Us Δ' e (e'.liftN n k) := by
  simpa [VExpr.lift'_consN_skipN] using TrExprS.weakFV'_nofvars henv W.toFVLift' H hfvf

/--
**fvar weakening for an fvar-free source**, with no well-formedness premise on the
target context.

The `hΔ'` of `erases_weakFV` is traded for `hfvf`, and `hfv` (the fixvar-freshness
side condition) for the stronger, simpler `hnfv : Γ.fixvars = fun _ => none`:

* the lean4lean side premises now go through `TrExprS.weakFV_nofvars`, which needs
  nothing about `Δ'` because an fvar-free source never performs an `.inr` lookup;
* the `Erases.fixvar` leaf — the one rule `erases_weakFV` had to side-condition —
  is here *refuted outright*: its `Γ.fixvars nm = some x` contradicts `hnfv`. That
  is the same equation every forward simulation already carries as `hnfv`, and it
  holds at every top-level `Γ`.

Source and target are untouched, exactly as in `erases_weakFV`. `ctor`/`cases`
split their `foldl Expr.app` spine's fvar-freeness with `fvarsIn_foldl_app`.
-/
theorem erases_weakFV_nofvars {env : VEnv} (henv : env.Ordered) {Us : List Name}
    {Γ : ErasureCtx} (hnfv : Γ.fixvars = fun _ => none)
    {Δ Δ' : VLCtx} {dk n k : Nat}
    (W : VLCtx.FVLift Δ Δ' dk n k)
    {e : Expr} {t : LBTerm} (h : Erases env Us Γ Δ e t)
    (hfvf : FVarsIn (fun _ => False) e) :
    Erases env Us Γ Δ' e t := by
  induction h generalizing Δ' dk k with
  | box htr her =>
      exact .box (TrExprS.weakFV_nofvars henv W htr hfvf) (her.weakN henv W.toCtx)
  | lit hcl _ ih => exact .lit hcl (ih W FVarsIn.toConstructor)
  | bvar i => exact .bvar i
  | fvar x => exact .fvar x
  | const n us kn h hctor hcases => exact .const n us kn h hctor hcases
  | app _ _ ihf iha => exact .app (ihf W hfvf.1) (iha W hfvf.2)
  | lam hty _ ihb =>
      exact .lam (TrExprS.weakFV_nofvars henv W hty hfvf.1) (ihb (W.cons_bvar _) hfvf.2)
  | letE hty hval _ _ ihv ihb =>
      exact .letE (TrExprS.weakFV_nofvars henv W hty hfvf.1)
        (TrExprS.weakFV_nofvars henv W hval hfvf.2.1) (ihv W hfvf.2.1)
        (ihb (W.cons_bvar _) hfvf.2.2)
  | ctor cn us iid cidx hc hlen _ ihargs =>
      have ⟨_, hall⟩ := fvarsIn_foldl_app hfvf
      exact .ctor cn us iid cidx hc hlen fun i hi =>
        ihargs i hi W (hall _ (List.getElem_mem hi))
  | ctor_head cn us iid cidx hc => exact .ctor_head cn us iid cidx hc
  | cases con us iid numParams pre hc hpre hnfs _ hlen hnlen harity _ ihd ihalts =>
      have ⟨_, hall⟩ := fvarsIn_foldl_app hfvf
      exact .cases con us iid numParams pre hc hpre hnfs (ihd W (hall _ (.head _)))
        hlen hnlen harity
        fun j hj => ihalts j hj W (hall _ (.tail _ (List.getElem_mem hj)))
  | fixvar nm us x hfx hctor hcases _ =>
      -- No side condition needed any more: at a fixvar-free `Γ` the leaf cannot occur.
      simp [hnfv] at hfx
  | const_fix nm us hrec hctor hcases hshift hsubst htobv =>
      exact .const_fix nm us hrec hctor hcases hshift hsubst htobv
  | @fix Δc idx nm tty tb tbi nms srcs defs hidx hnlen hslen hsrc hreg hrarg
      hlift hinst habsl hshift hsubst htobv hbodies _ihb =>
      exact .fix idx hidx hnlen hslen hsrc hreg hrarg hlift hinst habsl hshift hsubst htobv
        hbodies

/--
**Weakening to an arbitrary `VLCtx`.** For a closed, fvar-free source erasing to an
`LBClosed` target, an `Erases` derivation at the empty context holds at *every*
context — no well-formedness, no `NoBV`, no shape restriction of any kind.

This is the shape `Erases.fix`'s `hbodies` premise demands. That premise is
`∀ Δf : VLCtx`, entirely unrestricted, so neither `erases_weakFV` (which wants
`Δ'.FVWF`) nor `VLCtx.FVLift.from_nil` (which wants `Δ'.NoBV`) can supply it;
this lemma is what unblocks rebuilding it, and hence
`EnvErasureRec.erases_fix_of_open`.

Why the three premises are exactly these, and where each is spent — the proof is an
induction on `Δ`, one entry at a time:

* a **bvar** entry is handled by `erases_shift`, which needs nothing about its
  target context. It lifts source by `liftLooseBVars' 0 1` and target by
  `LBTerm.shift 1 0`; `hcl` and `hlb` are precisely what make both of those the
  *identity* (`Expr.liftLooseBVars_eq_self` off `Closed.looseBVarRange_zero`, and
  `LBClosed.shift_eq`), so the conclusion lands back on the same `e` and `t`.
  Without them the statement would not even typecheck as stated — the term would
  drift under every cons.
* an **fvar** entry is handled by `erases_weakFV_nofvars`, where `hfvf` removes
  the context hypothesis outright: `VLCtx.FVLift'.find?`'s `.inr` branch (the only
  consumer of `fvars` nodup, there to refute a *shadowing* fvar) is unreachable
  for a source with no free variables. This is why an arbitrary `Δ` — which may
  well re-bind fvars already present — is safe here and is not safe for
  `erases_weakFV`.
* `hnfv` kills the `Erases.fixvar` leaf, the one rule that is not context-uniform.
-/
theorem erases_weak_any {env : VEnv} (henv : env.Ordered) {Us : List Name} {Γ : ErasureCtx}
    (hnfv : Γ.fixvars = fun _ => none)
    {e : Expr} {t : LBTerm}
    (hcl : Closed e 0) (hfvf : FVarsIn (fun _ => False) e) (hlb : LBClosed t 0)
    (h : Erases env Us Γ [] e t) (Δ : VLCtx) :
    Erases env Us Γ Δ e t := by
  induction Δ with
  | nil => exact h
  | cons hd Δ₀ ih =>
    obtain ⟨_ | fvd, d⟩ := hd
    · -- A bvar entry: `erases_shift` needs no hypothesis, and closedness makes both
      -- of its lifts the identity.
      have hs := erases_shift henv (VLCtx.BVLift.skip d .refl) ih
      rwa [Expr.liftLooseBVars_eq_self (Nat.le_of_eq hcl.looseBVarRange_zero),
        LBClosed.shift_eq hlb (Nat.zero_le 0) 1] at hs
    · -- An fvar entry, possibly shadowing: safe because the source is fvar-free.
      exact erases_weakFV_nofvars henv hnfv (VLCtx.FVLift.skip_fvar fvd d .refl) ih hfvf

/-! ### Non-vacuity (unrestricted weakening) -/

/-- Non-vacuity: the same hand-built closed, fvar-free `lam` derivation as above,
transported out of the empty context into one carrying **both** an fvar entry and a
bvar entry — the shape neither `erases_weakFV` (no `FVWF`) nor
`VLCtx.FVLift.from_nil` (no `NoBV`) can reach. All four premises are constructed. -/
example (env : VEnv) (henv : env.Ordered) (Us : List Name) (Γ : ErasureCtx)
    (x : FVarId) (A B : VExpr) (name : Name) (bi : BinderInfo) :
    Erases env Us (Γ.withFixvars fun _ => none)
      [(none, .vlam B), (some (x, []), .vlam A)]
      (.lam name (.sort .zero) (.bvar 0) bi) (.lambda (nameToBinder name) (.bvar 0)) :=
  have H : Erases env Us (Γ.withFixvars fun _ => none) []
      (.lam name (.sort .zero) (.bvar 0) bi) (.lambda (nameToBinder name) (.bvar 0)) :=
    .lam (ty' := .sort .zero) (.sort rfl) (.bvar 0)
  have hcl : Closed (.lam name (.sort .zero) (.bvar 0) bi) 0 := ⟨trivial, Nat.zero_lt_one⟩
  have hfvf : FVarsIn (fun _ => False) (.lam name (.sort .zero) (.bvar 0) bi) :=
    ⟨rfl, trivial⟩
  have hlb : LBClosed (.lambda (nameToBinder name) (.bvar 0)) 0 := Nat.zero_lt_one
  erases_weak_any henv rfl hcl hfvf hlb H _

end LeanToLambdaBox
