import LeanToLambdaBox.Erases

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
  | bvar i => exact .bvar i
  | fvar y => exact .fvar y
  | const n us kn h hctor hcases => exact .const n us kn h hctor hcases
  | app _ _ ihf iha => exact .app (ihf W sc.1) (iha W sc.2)
  | lam hty _ ihb => exact .lam (TrExprS.thin_vlet W hty sc.1) (ihb W.succ sc.2)
  | letE hty hval _ _ ihv ihb =>
    exact .letE (TrExprS.thin_vlet W hty sc.1) (TrExprS.thin_vlet W hval sc.2.1)
      (ihv W sc.2.1) (ihb W.succ sc.2.2)
  | ctor cn us iid cidx hc hlen _ ihargs =>
    have ⟨_, hall⟩ := fvarsIn_foldl_app sc
    exact .ctor cn us iid cidx hc hlen fun i hi =>
      ihargs i hi W (hall _ (List.getElem_mem hi))
  | cases con us iid numParams pre hc _ hlen _ ihd ihalts =>
    have ⟨_, hall⟩ := fvarsIn_foldl_app sc
    exact .cases con us iid numParams pre hc (ihd W (hall _ (.head _))) hlen
      fun j hj => ihalts j hj W (hall _ (.tail _ (List.getElem_mem hj)))

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

end LeanToLambdaBox
