import LeanToLambdaBox.Erases

/-!
# Level instantiation, strictly (slice Γ-U3)

The Γ-U analysis in `DeltaHyps` (module docstring, §Γ-U) named `Erases.instL` **the wall**:

> Upstream's `TrExprS.instL` lands in `TrExpr`, not `TrExprS` — level *substitution*
> re-derives sort and const levels only up to `≈` — while `Erases.box`/`lam`/`letE` record
> **strict** `TrExprS` witnesses, and at `lam`/`letE` a defeq-loose binder type breaks the
> context chain the sub-derivation runs in. […] inside an induction over contexts there is
> no such composition point. So `Erases.instL` is not a corollary — it is the wall.

That reading of *why* is correct and its diagnosis of *where* is not. This file locates the
slack exactly, and it is smaller than the wall suggests.

## Where the `≈` comes from

`TrExprS.instL`'s residue is manufactured by one lemma, `substParams_wf`, and that lemma is
strict at three of its five arms: `zero` and `param` produce their equivalence by `rfl`, and
`succ` is a congruence of the sub-residue. **Every non-trivial residue is produced by `max`
and `imax`** — and there only through `Level.substParams'`' call to Lean's *normalising*
smart constructors `mkLevelMax'`/`mkLevelIMax'`, which contract `max u u` to `u` and
`max 0 0` to `0`. Level substitution is not defeq-loose because it substitutes; it is
defeq-loose because it **normalises**, and it normalises only at a `max`/`imax` node.

So the cut that buys strictness is syntactic and it is on the *source's level syntax*:

* `NoMaxLevel` — a level built from `zero`, `succ` and `param`, with no `max`/`imax`;
* `NoMaxLevels` — every level in an `Expr`'s `sort` and `const` nodes is `NoMaxLevel`.

On that fragment `substParams_strict` replaces `substParams_wf`'s `≈` with `=`, and the
whole tower goes strict with it: `TrExprS.instL_strict` lands in `TrExprS`, and
`Erases.instL` follows by a plain structural induction. Nothing in this file needs
`VEnv.WF`, `VLCtx.WF`, `env.Ordered`, `TrExprS.uniq` or a context-defeq lemma — the
composition point the analysis went looking for is not needed, because with a strict
binder witness there is no residue to compose away.

**The fragment is the intended one.** `Sort u`, `Type u`, `List.{u}`, `Nat`,
`OfNat.ofNat.{u}`'s prepared body `fun α x self => self.1` — the typeclass-dispatch layer
Γ-U exists to admit — are all `max`/`imax`-free. What is outside is a term whose *own*
level annotations mention `max`, e.g. an explicit `Sort (max u v)` or a `Prod.{u,v}`
constructor spine.

## What the commission asked, and what the answer is

The plan's route (b) was to restrict to **closed** level instantiations, on the hypothesis
that `VLevel.ofLevel` on a closed level ignores `Us` and that the transport might then be
strict again. The first half is true and is `ofLevel_param_free` below. The second half is
**false**, and `instL_closed_not_strict` refutes it: normalisation fires on the shape of the
*source* level, not on the instantiation, so `max (param p) 0` instantiated at the closed
`0` still translates to `zero` where the strict conclusion would need `max zero zero`. The
two are `≈` and not `=`, exactly as `substParams_wf` says. Closedness is not the cut;
`max`-freeness is, and it is orthogonal to it.

## What is still out of scope, and why

`Erases.instL` below takes `Γ.recBodies = fun _ => none` — the non-recursive fragment. The
two recursive arms are not hard for a different reason than the rest: `Erases.fix`'s
`hbodies` premise is stated `∀ Δf`, and the induction hypothesis supplies the instantiated
body only at contexts **in the image of `VLCtx.instL`**, which is not every context. Closing
that needs the development's context-uniformity theorem (`erases_weak_any`) and its
premises (`Γ.fixvars = ⊥`, source closedness, target `LBClosed`) at each sibling body — a
composition this slice does not do. Named here rather than hidden in a `NoBlock`: the gap is
about `instL`'s non-surjectivity on contexts, and it is the one place where the analysis'
"no composition point" instinct really does bite.
-/

namespace Lean4Lean

open Lean

/-! ## The level layer: where the residue lives, and where it does not -/

/-- A level with no `max`/`imax` node — built from `zero`, `succ` and `param`. This is the
exact condition under which `Level.substParams'` performs no normalisation, and hence the
exact condition under which level substitution is *strict* rather than `≈`-loose. -/
def NoMaxLevel : Level → Prop
  | .zero => True
  | .param _ => True
  | .mvar _ => True
  | .succ u => NoMaxLevel u
  | .max _ _ => False
  | .imax _ _ => False

/-- Positional lookup through a successful `mapM (VLevel.ofLevel Us)`. -/
theorem mapM_ofLevel_getElem? {Us : List Name} {ls : List Level} {ls' : List VLevel}
    (Hls : ls.mapM (VLevel.ofLevel Us) = some ls') {n : Nat} {l : Level}
    (h : ls[n]? = some l) : ∃ v, ls'[n]? = some v ∧ VLevel.ofLevel Us l = some v := by
  rw [List.mapM_eq_some] at Hls
  induction Hls generalizing n with
  | nil => simp at h
  | cons hd _ ih =>
    cases n with
    | zero => simp at h; subst h; exact ⟨_, rfl, hd⟩
    | succ n => simpa using ih (by simpa using h)

/-- **Level substitution is strict on `max`-free levels.** The strict twin of upstream's
`substParams_wf`, whose conclusion is `u₁ ≈ u'.inst ls'`.

The comparison is the whole point of the slice. Upstream's proof produces its equivalence by
`rfl` at `zero` and `param`, and by congruence at `succ`; the only place a genuinely
non-trivial `≈` is manufactured is the `max`/`imax` pair, where `Level.substParams'` calls
`mkLevelMax'`/`mkLevelIMax'` — Lean's *normalising* smart constructors — as soon as either
operand mentions a parameter. Exclude those two nodes and the same induction yields an
equation. -/
theorem substParams_strict {Us ps : List Name} {ls : List Level} {ls' : List VLevel}
    (Hls : ls.mapM (VLevel.ofLevel Us) = some ls') (eq : ps.length = ls.length)
    {F : Name → Level}
    (eqF : (fun x => ((List.idxOf? x ps).bind fun i => ls[i]?).getD (Level.param x)) = F) :
    ∀ (red : Bool) {u : Level}, NoMaxLevel u → ∀ {u' : VLevel},
      VLevel.ofLevel ps u = some u' →
      VLevel.ofLevel Us (u.substParams' F red) = some (u'.inst ls') := by
  intro red u
  induction u generalizing red with
  | zero => intro _ u' H; simp [VLevel.ofLevel] at H; subst H; rfl
  | succ u ih =>
    intro hnm u' H
    simp [VLevel.ofLevel, bind] at H
    obtain ⟨a, ha, rfl⟩ := H
    simp [Level.substParams', VLevel.ofLevel, VLevel.inst, ih _ hnm ha]
  | max _ _ => intro hnm; exact hnm.elim
  | imax _ _ => intro hnm; exact hnm.elim
  | mvar => intro _ u' H; simp [VLevel.ofLevel] at H
  | param x =>
    intro _ u' H
    simp [VLevel.ofLevel] at H
    obtain ⟨hlt, rfl⟩ := H
    subst eqF
    have hidx : List.idxOf? x ps = some (List.idxOf x ps) := by
      have h := List.idxOf_eq_getD_idxOf? x ps
      cases hc : List.idxOf? x ps with
      | none => rw [hc] at h; simp at h; omega
      | some i => rw [hc] at h; simp at h; rw [h]
    have hlt' : List.idxOf x ps < ls.length := eq ▸ hlt
    have hget : ls[List.idxOf x ps]? = some ls[List.idxOf x ps] := by simp [hlt']
    obtain ⟨v, hv, hofl⟩ := mapM_ofLevel_getElem? Hls hget
    simp [Level.substParams', VLevel.inst, hidx, hget, hv, hofl]

/-- The spine form, for `TrExprS.const`'s level list. -/
theorem substParams_strict_list {Us ps : List Name} {ls : List Level} {ls' : List VLevel}
    (Hls : ls.mapM (VLevel.ofLevel Us) = some ls') (eq : ps.length = ls.length)
    {F : Name → Level}
    (eqF : (fun x => ((List.idxOf? x ps).bind fun i => ls[i]?).getD (Level.param x)) = F)
    (red : Bool) {us : List Level} {us' : List VLevel}
    (H : us.mapM (VLevel.ofLevel ps) = some us') :
    (∀ u ∈ us, NoMaxLevel u) →
      (us.map (Level.substParams' F red)).mapM (VLevel.ofLevel Us)
        = some (us'.map (·.inst ls')) := by
  rw [List.mapM_eq_some] at H
  rw [List.mapM_eq_some]
  induction H with
  | nil => exact fun _ => by simp
  | @cons a b l1 l2 h _ ih =>
    intro hnm
    simp only [List.map_cons]
    exact .cons (substParams_strict Hls eq eqF red (hnm a (by simp)) h)
      (ih (fun u hu => hnm u (by simp [hu])))

/-! ## The `Expr` layer -/

/-- Every level an `Expr` mentions — in its `sort` and `const` nodes — is `max`-free. -/
def NoMaxLevels : Expr → Prop
  | .sort u => NoMaxLevel u
  | .const _ us => ∀ u ∈ us, NoMaxLevel u
  | .app f a => NoMaxLevels f ∧ NoMaxLevels a
  | .lam _ t b _ => NoMaxLevels t ∧ NoMaxLevels b
  | .forallE _ t b _ => NoMaxLevels t ∧ NoMaxLevels b
  | .letE _ t v b _ => NoMaxLevels t ∧ NoMaxLevels v ∧ NoMaxLevels b
  | .mdata _ e => NoMaxLevels e
  | .proj _ _ e => NoMaxLevels e
  | .bvar _ => True
  | .fvar _ => True
  | .mvar _ => True
  | .lit _ => True

/-- A literal's constructor form mentions only `[]` and `[.zero]`, so it is in the
fragment. What `TrExprS.lit`/`Erases.lit`'s sub-derivation needs. -/
theorem noMaxLevels_toConstructor {l : Literal} : NoMaxLevels (Literal.toConstructor l) := by
  cases l with
  | natVal n =>
    cases n <;>
      simp [Literal.toConstructor, Expr.natLitToConstructor, NoMaxLevels, Expr.natZero,
        Expr.natSucc]
  | strVal s =>
    simp only [Literal.toConstructor, Expr.strLitToConstructor]
    refine ⟨by simp [NoMaxLevels], ?_⟩
    induction s.toList <;> simp_all [NoMaxLevels, NoMaxLevel]

/-- The fragment distributes over an application spine, which is the shape `Erases.ctor`
and `Erases.cases` state their sources in. -/
theorem noMaxLevels_foldl_app : ∀ {args : List Expr} {hd : Expr},
    NoMaxLevels (args.foldl Expr.app hd) ↔ NoMaxLevels hd ∧ ∀ a ∈ args, NoMaxLevels a
  | [], _ => by simp
  | a :: args, hd => by
    rw [List.foldl_cons, noMaxLevels_foldl_app]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      exacts [h2, h3 x hx]
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, h2 a (by simp)⟩, fun x hx => h2 x (by simp [hx])⟩

/-- …and level instantiation distributes over it too. -/
theorem instCore_foldl_app {red : Bool} {F : Name → Level} : ∀ {args : List Expr} {hd : Expr},
    Expr.instantiateLevelParamsCore' red F (args.foldl Expr.app hd)
      = (args.map (Expr.instantiateLevelParamsCore' red F)).foldl Expr.app
          (Expr.instantiateLevelParamsCore' red F hd)
  | [], _ => rfl
  | a :: args, hd => by
    rw [List.foldl_cons, instCore_foldl_app, List.map_cons, List.foldl_cons]
    rfl

/-- Instantiation moves no fvar: `VLCtx.instL` rewrites the declarations and keeps the
names. What `Erases.fixvar`'s freshness premise travels on. -/
theorem VLCtx.fvars_instL {ls : List VLevel} : ∀ {Δ : VLCtx}, (Δ.instL ls).fvars = Δ.fvars
  | [] => rfl
  | (none, _) :: Δ => by simp [VLCtx.instL, VLCtx.fvars_instL (Δ := Δ)]
  | (some _, _) :: Δ => by simp [VLCtx.instL, VLCtx.fvars_instL (Δ := Δ)]

/-- **The strict `TrExprS.instL`**, in the `instantiateLevelParamsCore'` form its `Erases`
consumer meets it in.

Compare upstream's `TrExprS.instL`, which concludes `TrExpr` and needs `VEnv.WF env` and
`VLCtx.WF env ls'.length Δ` — the latter to run the defeq-composing `TrExpr.app`/`.lam`/…
smart constructors. This one needs **neither**, and that is not an accident: with a strict
level transport every arm is the raw `TrExprS` constructor applied to `instL`-transported
side premises, and the only thing those need is `VLevel.WF` of the substituted levels
(`VEnv.HasType.instL`). The `VLCtx.WF` premise is what `Erases` could not have supplied
anyway — `Erases.lam` carries a `TrExprS` for its binder type, not an `IsType`, so the
extended context of its sub-derivation is not known to be well-formed. -/
theorem TrExprS.instL_core {env : VEnv} {Us ps : List Name} {ls : List Level}
    {ls' : List VLevel} {Δ : VLCtx} {e : Expr} {e' : VExpr} {F : Name → Level}
    (Hls : ls.mapM (VLevel.ofLevel Us) = some ls') (eq : ps.length = ls.length)
    (eqF : (fun x => ((List.idxOf? x ps).bind fun i => ls[i]?).getD (Level.param x)) = F)
    (red : Bool)
    (H : TrExprS env ps Δ e e') : NoMaxLevels e →
    TrExprS env Us (Δ.instL ls') (Expr.instantiateLevelParamsCore' red F e) (e'.instL ls') := by
  have Hls' := VLevel.WF.of_mapM_ofLevel Hls
  induction H with
  | bvar h1 => exact fun _ => .bvar (VLCtx.find?_instL h1)
  | fvar h1 => exact fun _ => .fvar (VLCtx.find?_instL h1)
  | sort h1 =>
    intro hnm
    exact .sort (substParams_strict Hls eq eqF red hnm h1)
  | const h1 h2 h3 =>
    intro hnm
    exact .const h1 (substParams_strict_list Hls eq eqF red h2 hnm) (by simp [h3])
  | app h1 h2 _ _ ih1 ih2 =>
    intro hnm
    exact .app (VLCtx.instL_toCtx _ ▸ h1.instL Hls') (VLCtx.instL_toCtx _ ▸ h2.instL Hls')
      (ih1 hnm.1) (ih2 hnm.2)
  | lam h1 _ _ ih1 ih2 =>
    intro hnm
    exact .lam (VLCtx.instL_toCtx _ ▸ h1.instL Hls') (ih1 hnm.1) (ih2 hnm.2)
  | forallE h1 h2 _ _ ih1 ih2 =>
    intro hnm
    exact .forallE (VLCtx.instL_toCtx _ ▸ h1.instL Hls')
      (VLCtx.instL_toCtx _ ▸ h2.instL Hls') (ih1 hnm.1) (ih2 hnm.2)
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    intro hnm
    exact .letE (VLCtx.instL_toCtx _ ▸ h1.instL Hls') (ih1 hnm.1) (ih2 hnm.2.1)
      (ih3 hnm.2.2)
  | lit h1 _ ih =>
    intro _
    refine .lit h1 (Expr.instantiateLevelParamsCore_eq_self ?_ ▸ ih ?_ :)
    · exact Literal.toConstructor_hasLevelParam
    · exact noMaxLevels_toConstructor
  | mdata _ ih => exact fun hnm => .mdata (ih hnm)
  | proj _ h2 ih =>
    intro hnm
    exact .proj (ih hnm) (VLCtx.instL_toCtx _ ▸ h2.instL Hls')

/-- The user-facing form, at `Expr.instantiateLevelParams`. -/
theorem TrExprS.instL_strict {env : VEnv} {Us ps : List Name} {ls : List Level}
    {ls' : List VLevel} {Δ : VLCtx} {e : Expr} {e' : VExpr}
    (Hls : ls.mapM (VLevel.ofLevel Us) = some ls') (eq : ps.length = ls.length)
    (H : TrExprS env ps Δ e e') (hnm : NoMaxLevels e) :
    TrExprS env Us (Δ.instL ls') (e.instantiateLevelParams ps ls) (e'.instL ls') := by
  rw [Expr.instantiateLevelParams_eq]
  exact TrExprS.instL_core Hls eq rfl _ H hnm

end Lean4Lean

namespace LeanToLambdaBox

open Lean Lean4Lean

/-! ## The `VExpr`-side obligations of `Erases.box` -/

/-- `IsArity` is a syntactic spine of `forallE`s ending in a `sort`; `instL` fixes both
constructors. -/
theorem IsArity.instL {ls : List VLevel} : ∀ {A : VExpr}, IsArity A → IsArity (A.instL ls)
  | _, .sort _ => .sort _
  | _, .forallE _ _ h => .forallE _ _ (IsArity.instL h)

theorem IsArityUpTo.instL {env : VEnv} {U U' : Nat} {ls : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U') {Γ : List VExpr} {A : VExpr}
    (h : IsArityUpTo env U Γ A) :
    IsArityUpTo env U' (Γ.map (VExpr.instL ls)) (A.instL ls) :=
  let ⟨A', hd, har⟩ := h
  ⟨A'.instL ls, VEnv.IsDefEqU.instL hls hd, har.instL⟩

/-- **The box arm's obligation under instantiation.** As at Γ-U1, no environment-side lift
is needed: `Erasable` unfolds to a `HasType` and a `HasType`-or-`IsArityUpTo` disjunct, and
`instL` transports each. The `.sort .zero` of the propositional disjunct is instantiation-
invariant, since `VLevel.inst` fixes `zero`. -/
theorem Erasable.instL {env : VEnv} {U U' : Nat} {ls : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U') {Γ : List VExpr} {e : VExpr}
    (h : Erasable env U Γ e) : Erasable env U' (Γ.map (VExpr.instL ls)) (e.instL ls) :=
  let ⟨A, hA, hd⟩ := h
  ⟨A.instL ls, VEnv.HasType.instL hls hA,
    hd.imp (fun h => VEnv.HasType.instL hls h) (fun h => IsArityUpTo.instL hls h)⟩

/-! ## `Erases.instL` -/

/-- **Erasure transports along a level instantiation** — the Γ-U3 statement, on the
`max`-free, non-recursive fragment.

The target `t` is **unchanged**: λ□ is level-free, which the Γ-U analysis' finding (a)
predicted and this is the proof. The source is instantiated, the context is instantiated,
and the derivation moves with no residue at all.

Three things about the shape:

* the binder arms are where the wall was, and they are the easy ones here. With
  `TrExprS.instL_strict` the binder witness of `Erases.lam` becomes exactly `ty'.instL ls'`,
  which is exactly the head of `((none, .vlam ty') :: Δ).instL ls'` — the context the
  sub-derivation's induction hypothesis is stated at. Nothing has to be composed away;
* `fixvar`'s freshness travels because `VLCtx.instL` does not touch fvar names;
* `hnorec` kills the two recursive arms. `Erases.const_fix` reads `Γ.recBodies nm = some …`
  directly, and `Erases.fix`'s `hreg` reads it at the block's own `idx`. See the module
  docstring for what the recursive arms would need — the obstruction there is
  `VLCtx.instL`'s non-surjectivity, not a defeq residue. -/
theorem Erases.instL_core {env : VEnv} {Us ps : List Name} {ls : List Level}
    {ls' : List VLevel} {Γ : ErasureCtx} {Δ : VLCtx} {e : Expr} {t : LBTerm}
    {F : Name → Level}
    (Hls : ls.mapM (VLevel.ofLevel Us) = some ls') (eq : ps.length = ls.length)
    (eqF : (fun x => ((List.idxOf? x ps).bind fun i => ls[i]?).getD (Level.param x)) = F)
    (red : Bool) (hnorec : Γ.recBodies = fun _ => none)
    (H : Erases env ps Γ Δ e t) : NoMaxLevels e →
    Erases env Us Γ (Δ.instL ls') (Expr.instantiateLevelParamsCore' red F e) t := by
  have Hls' := VLevel.WF.of_mapM_ofLevel Hls
  induction H with
  | box htr her =>
    intro hnm
    exact .box (htr.instL_core Hls eq eqF red hnm)
      (VLCtx.instL_toCtx _ ▸ Erasable.instL Hls' her)
  | lit hcl _ ih =>
    intro _
    exact .lit hcl (Expr.instantiateLevelParamsCore_eq_self
      Literal.toConstructor_hasLevelParam ▸ ih noMaxLevels_toConstructor :)
  | proj S i iid np nf hs hnfs hi _ ihd =>
    intro hnm; exact .proj S i iid np nf hs hnfs hi (ihd hnm)
  | bvar i => intro _; exact .bvar i
  | fvar x => intro _; exact .fvar x
  | const n us kn h hctor hcases => intro _; exact .const n _ kn h hctor hcases
  | app _ _ ihf iha => intro hnm; exact .app (ihf hnm.1) (iha hnm.2)
  | lam hty _ ihb =>
    intro hnm; exact .lam (hty.instL_core Hls eq eqF red hnm.1) (ihb hnm.2)
  | letE hty hval _ _ ihv ihb =>
    intro hnm
    exact .letE (hty.instL_core Hls eq eqF red hnm.1)
      (hval.instL_core Hls eq eqF red hnm.2.1) (ihv hnm.2.1) (ihb hnm.2.2)
  | @ctor Δ₀ cn us iid cidx args args' hc hlen _ ihargs =>
    intro hnm
    rw [instCore_foldl_app]
    obtain ⟨-, hargsnm⟩ := noMaxLevels_foldl_app.1 hnm
    refine .ctor cn _ iid cidx hc (by simp [hlen]) (fun i h => ?_)
    have h' : i < args.length := by simpa using h
    have := ihargs i h' (hargsnm _ (List.getElem_mem h'))
    simpa using this
  | ctor_head cn us iid cidx hc => intro _; exact .ctor_head cn _ iid cidx hc
  | @cases Δ₀ con us iid numParams pre discr discr' minors alts' nfs hc hpre hnfs _ hlen
      hnlen harity _ ihd ihalts =>
    intro hnm
    rw [instCore_foldl_app, instCore_foldl_app]
    obtain ⟨hhd, hspine⟩ := noMaxLevels_foldl_app.1 hnm
    refine .cases con _ iid numParams (pre.map (Expr.instantiateLevelParamsCore' red F))
      hc (by simpa using hpre) hnfs (ihd (hspine _ (by simp))) (by simp [hlen]) hnlen harity
      (fun j h => ?_)
    have h' : j < minors.length := by simpa using h
    have := ihalts j h' (hspine _ (by simp [List.getElem_mem h']))
    simpa using this
  | fixvar nm us x hfx hctor hcases hfresh =>
    intro _
    exact .fixvar nm _ x hfx hctor hcases (by rwa [VLCtx.fvars_instL])
  | const_fix nm us hrec hctor hcases hshift hsubst htobv =>
    intro _; rw [hnorec] at hrec; exact absurd hrec (by simp)
  | fix idx hidx hnlen hslen hsrc hreg hrarg hlift hinst habsl hshift hsubst htobv _ ihb =>
    intro _
    have := hreg idx hidx
    rw [hnorec] at this
    exact absurd this (by simp)

/-- The user-facing form, at `Expr.instantiateLevelParams`. -/
theorem Erases.instL {env : VEnv} {Us ps : List Name} {ls : List Level}
    {ls' : List VLevel} {Γ : ErasureCtx} {Δ : VLCtx} {e : Expr} {t : LBTerm}
    (Hls : ls.mapM (VLevel.ofLevel Us) = some ls') (eq : ps.length = ls.length)
    (hnorec : Γ.recBodies = fun _ => none)
    (H : Erases env ps Γ Δ e t) (hnm : NoMaxLevels e) :
    Erases env Us Γ (Δ.instL ls') (e.instantiateLevelParams ps ls) t := by
  rw [Expr.instantiateLevelParams_eq]
  exact Erases.instL_core Hls eq rfl _ hnorec H hnm

/-! ### Guards

The positive one is the shape Γ-U4 will consume: a `{u}`-polymorphic dependency body,
instantiated at a **closed** level, landing in a `Us = []` subject's scope. The negative
ones bound the claim: they refute the plan's route (b) — closedness is not the cut — and
exhibit the `max` node that route (b) would have had to survive. -/

/-- The fixture's instantiation: `[u] ↦ [0]`, read into the empty scope. Both sides are
`rfl`, which is the level layer's whole content at a closed instantiation. -/
theorem gInstLClosed :
    ([Level.zero].mapM (VLevel.ofLevel ([] : List Name)) = some [VLevel.zero]) ∧
      ([`u] : List Name).length = [Level.zero].length := ⟨rfl, rfl⟩

/-- Guard (positive): a `{u}`-polymorphic λ, erased at `Us = [u]`, is an `Erases`
derivation **at `Us = []`** once its level parameter is instantiated at `0` — same target,
no residue. This is exactly the step the typeclass layer needs and the one Γ-U's analysis
recorded as unavailable: a polymorphic dependency of a closed subject. Built at an arbitrary
`env` and at any `Γ` without recursive constants, so what it checks is the level
instantiation and nothing else. -/
theorem gErasesInstLClosed (env : VEnv) (Γ : ErasureCtx)
    (hnorec : Γ.recBodies = fun _ => none) (nm : Name) (bi : BinderInfo) :
    Erases env [] Γ [] (.lam nm (.sort .zero) (.bvar 0) bi)
      (.lambda (nameToBinder nm) (.bvar 0)) := by
  have h := Erases.instL (env := env) (Us := []) (ps := [`u]) (ls := [Level.zero])
    (ls' := [VLevel.zero]) (Γ := Γ) (Δ := [])
    (e := .lam nm (.sort (.param `u)) (.bvar 0) bi)
    (t := .lambda (nameToBinder nm) (.bvar 0)) gInstLClosed.1 gInstLClosed.2 hnorec
    (.lam (ty' := .sort (.param 0)) (.sort rfl) (.bvar 0))
    (⟨trivial, trivial⟩ : NoMaxLevels (.lam nm (.sort (.param `u)) (.bvar 0) bi))
  simpa [Expr.instantiateLevelParams_eq, Expr.instantiateLevelParamsCore',
    Level.substParams', VLCtx.instL] using h

/-- Guard (negative, the commission's hypothesis — **confirmed**): `VLevel.ofLevel` on a
parameter-free level does not look at the scope at all, at *any* two scopes. This is the
half of route (b) that is true. -/
theorem ofLevel_param_free {Us Us' : List Name} : ∀ {l : Level}, l.hasParam' = false →
    VLevel.ofLevel Us l = VLevel.ofLevel Us' l := by
  intro l
  induction l with
  | zero => intro; rfl
  | succ _ ih => intro h; simp [VLevel.ofLevel, ih (by simpa [Level.hasParam'] using h)]
  | max _ _ ih1 ih2 =>
    intro h
    simp [Level.hasParam'] at h
    simp [VLevel.ofLevel, ih1 h.1, ih2 h.2]
  | imax _ _ ih1 ih2 =>
    intro h
    simp [Level.hasParam'] at h
    simp [VLevel.ofLevel, ih1 h.1, ih2 h.2]
  | param n => intro h; simp [Level.hasParam'] at h
  | mvar => intro; rfl

/-- Lean's `max` smart constructor is *normalising*: it contracts `max 0 0` to `0`. Proved
through the `mkLevelMaxCore` if-chain `mkLevelMax'` unfolds to, exactly as lean4lean's own
`ofLevel_mkLevelMax'` does — the first test is `u == v`. -/
theorem mkLevelMax'_zero_zero : Lean.mkLevelMax' .zero .zero = .zero := by
  show (if ((Level.zero : Level) == Level.zero) then (Level.zero : Level) else
    if Level.zero.isZero then (Level.zero : Level) else Level.zero) = Level.zero
  simp

/-- Guard (negative, the commission's conclusion — **refuted**). Route (b) proposed
restricting to *closed* level instantiations, on the hypothesis that the transport might
then be strict. It is not, and this is the counterexample: at `ps = [p]`, `ls = [0]` — as
closed an instantiation as there is — the source level `max p 0` substitutes to `0`, while
the strict conclusion demands `(ofLevel [p] (max p 0)).inst [0] = max 0 0`. The two are
`≈` and not `=`, which is precisely `substParams_wf`'s conclusion.

So the slack is manufactured by **normalisation at a `max`/`imax` node**, not by the
instantiation being open. Closedness is not the cut; `NoMaxLevel` is, and the two are
orthogonal — this level is closed after substitution and still not strict. -/
theorem instL_closed_not_strict :
    (Level.max (.param `p) .zero).substParams' (fun _ => .zero) true = .zero ∧
      VLevel.ofLevel ([] : List Name) .zero = some .zero ∧
      VLevel.ofLevel [`p] (Level.max (.param `p) .zero) = some (.max (.param 0) .zero) ∧
      (VLevel.max (.param 0) .zero).inst [.zero] = .max .zero .zero ∧
      VLevel.max .zero .zero ≠ VLevel.zero := by
  refine ⟨?_, rfl, rfl, rfl, by simp⟩
  simp [Level.substParams', Level.hasParam_eq, Level.hasParam']
  exact mkLevelMax'_zero_zero

end LeanToLambdaBox
