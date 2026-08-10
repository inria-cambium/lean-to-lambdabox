import LeanToLambdaBox.Erases

/-!
# `LBClosed` + the de-Bruijn commutation kit for `LBTerm`

Target-side de-Bruijn metatheory, independent of the erasure relation: the
closedness predicate `LBClosed` (with its congruence/monotonicity/stability
lemmas) and the general `shift`/`subst` commutation laws.

**`LBClosed`.** `LBClosed t k` holds when `t` has no loose de-Bruijn index `≥ k`
(the `LBTerm` analogue of lean4lean's `Lean4Lean.Closed`). It is what makes
`shift`/`subst` the identity on a closed constructed `.fix` node (whose bodies live
under `defs.length` binders and are otherwise closed) — the six transport-inertness
equalities of `Erases.fix` are derived from it in `EnvErasureRec.lean`. Defined by the
same mutual recursion as `shift`/`hasFVar` (the per-list traversals factored into
helpers so the structural-recursion checker sees through the nested `List`
occurrences).

**The commutation kit.** `shift_shift`, `subst_shift_cancel`, `subst_shift_comm` and
their capstone `subst_subst` (the standard de-Bruijn distribution law
`σ ∘ [t] = [σ t] ∘ σ⁺`). These are the *general* forms; `Optimize.lean` has
`.box`-specialised siblings, which we deliberately do not depend on (that file sits in
a different branch of the import DAG).

Everything here is pure target-side reasoning — no lean4lean, hence `sorryAx`-free.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-! ## Part 1 — `LBClosed`: de-Bruijn closedness for `LBTerm` -/

mutual
/-- No loose de-Bruijn index `≥ k` occurs in `t`. -/
def LBClosed : LBTerm → Nat → Prop
  | .box, _ => True
  | .bvar i, k => i < k
  | .fvar _, _ => True
  | .lambda _ b, k => LBClosed b (k + 1)
  | .letIn _ v b, k => LBClosed v k ∧ LBClosed b (k + 1)
  | .app f a, k => LBClosed f k ∧ LBClosed a k
  | .const _, _ => True
  | .construct _ _ args, k => LBClosedArgs args k
  | .case _ discr alts, k => LBClosed discr k ∧ LBClosedAlts alts k
  | .proj _ e, k => LBClosed e k
  | .fix defs _, k => LBClosedDefs defs (k + defs.length)
  | .prim _, _ => True

/-- `LBClosed` over a `construct` argument list (each argument closed at `k`). -/
def LBClosedArgs : List LBTerm → Nat → Prop
  | [], _ => True
  | t :: rest, k => LBClosed t k ∧ LBClosedArgs rest k

/-- `LBClosed` over `case` alternatives (each branch body closed below its own field
binders). -/
def LBClosedAlts : List (List BinderName × LBTerm) → Nat → Prop
  | [], _ => True
  | (ns, b) :: rest, k => LBClosed b (k + ns.length) ∧ LBClosedAlts rest k

/-- `LBClosed` over `fix` definitions (each body closed at the shared level `k`, which
the caller sets to include the `defs.length` fix binders). -/
def LBClosedDefs : List (@FixDef LBTerm) → Nat → Prop
  | [], _ => True
  | fd :: rest, k => LBClosed fd.body k ∧ LBClosedDefs rest k
end

@[simp] theorem LBClosed_box (k : Nat) : LBClosed .box k ↔ True := Iff.rfl
@[simp] theorem LBClosed_bvar (i k : Nat) : LBClosed (.bvar i) k ↔ i < k := Iff.rfl
@[simp] theorem LBClosed_fvar (x : FVarId) (k : Nat) : LBClosed (.fvar x) k ↔ True := Iff.rfl
@[simp] theorem LBClosed_const (kn : Kername) (k : Nat) : LBClosed (.const kn) k ↔ True := Iff.rfl
@[simp] theorem LBClosed_prim (p : PrimVal) (k : Nat) : LBClosed (.prim p) k ↔ True := Iff.rfl
@[simp] theorem LBClosed_lambda (n : BinderName) (b : LBTerm) (k : Nat) :
    LBClosed (.lambda n b) k ↔ LBClosed b (k + 1) := Iff.rfl
@[simp] theorem LBClosed_letIn (n : BinderName) (v b : LBTerm) (k : Nat) :
    LBClosed (.letIn n v b) k ↔ LBClosed v k ∧ LBClosed b (k + 1) := Iff.rfl
@[simp] theorem LBClosed_app (f a : LBTerm) (k : Nat) :
    LBClosed (.app f a) k ↔ LBClosed f k ∧ LBClosed a k := Iff.rfl
@[simp] theorem LBClosed_construct (iid : InductiveId) (c : Nat) (args : List LBTerm) (k : Nat) :
    LBClosed (.construct iid c args) k ↔ LBClosedArgs args k := Iff.rfl
@[simp] theorem LBClosed_case (info : InductiveId × Nat) (discr : LBTerm)
    (alts : List (List BinderName × LBTerm)) (k : Nat) :
    LBClosed (.case info discr alts) k ↔ LBClosed discr k ∧ LBClosedAlts alts k := Iff.rfl
@[simp] theorem LBClosed_proj (p : ProjectionInfo) (e : LBTerm) (k : Nat) :
    LBClosed (.proj p e) k ↔ LBClosed e k := Iff.rfl
@[simp] theorem LBClosed_fix (defs : List (@FixDef LBTerm)) (i k : Nat) :
    LBClosed (.fix defs i) k ↔ LBClosedDefs defs (k + defs.length) := Iff.rfl

/-- `LBClosedArgs` in the natural per-element form. -/
theorem LBClosedArgs_iff (l : List LBTerm) (k : Nat) :
    LBClosedArgs l k ↔ ∀ t ∈ l, LBClosed t k := by
  induction l with
  | nil => simp [LBClosedArgs]
  | cons t rest ih => simp [LBClosedArgs, ih]

/-- `LBClosedAlts` in the natural per-element form. -/
theorem LBClosedAlts_iff (l : List (List BinderName × LBTerm)) (k : Nat) :
    LBClosedAlts l k ↔ ∀ a ∈ l, LBClosed a.2 (k + a.1.length) := by
  induction l with
  | nil => simp [LBClosedAlts]
  | cons a rest ih => obtain ⟨ns, b⟩ := a; simp [LBClosedAlts, ih]

/-- `LBClosedDefs` in the natural per-element form. -/
theorem LBClosedDefs_iff (l : List (@FixDef LBTerm)) (k : Nat) :
    LBClosedDefs l k ↔ ∀ d ∈ l, LBClosed d.body k := by
  induction l with
  | nil => simp [LBClosedDefs]
  | cons fd rest ih => simp [LBClosedDefs, ih]

/-! ### The `Defs` traversals in `List.map` form

`Erases.lean` exposes `shiftArgs`/`shiftAlts` (and their `subst` counterparts) as maps;
the `FixDef` traversals are missing there, and every `hfix` arm below needs them (both
for the elementwise comparison and for the `defs.length` bookkeeping). -/

theorem LBTerm.shiftDefs_eq_map (d c : Nat) (l : List (@FixDef LBTerm)) :
    LBTerm.shiftDefs d c l = l.map (fun fd => { fd with body := LBTerm.shift d c fd.body }) := by
  induction l with
  | nil => rfl
  | cons fd rest ih => simp only [LBTerm.shiftDefs, List.map, ih]

theorem LBTerm.substDefs_eq_map (s : LBTerm) (d : Nat) (l : List (@FixDef LBTerm)) :
    LBTerm.substDefs s d l = l.map (fun fd => { fd with body := LBTerm.subst s d fd.body }) := by
  induction l with
  | nil => rfl
  | cons fd rest ih => simp only [LBTerm.substDefs, List.map, ih]

/-! ### `shift`/`subst` are the identity on de-Bruijn-closed terms

If `t` is closed below `k` and the cutoff `c ≥ k`, then `shift`/`subst` at cutoff `c`
touch no index of `t` and return it unchanged. The single induction is over
`LBTerm.recData` (the `Prop`-motive recursor with per-list membership IHs), threading
`k ≤ c` under each binder. -/

theorem LBClosed.shift_eq {t : LBTerm} {k : Nat} (hc : LBClosed t k)
    {c : Nat} (hle : k ≤ c) (d : Nat) : LBTerm.shift d c t = t := by
  induction t using LBTerm.recData generalizing k c with
  | hbox | hfvar | hconst | hprim => rfl
  | hbvar i => simp only [LBClosed_bvar] at hc; simp only [LBTerm.shift]; rw [if_neg (by omega)]
  | hlam n b ih =>
      simp only [LBClosed_lambda] at hc
      simp only [LBTerm.shift, ih hc (Nat.succ_le_succ hle)]
  | hletIn n v b ihv ihb =>
      simp only [LBClosed_letIn] at hc
      simp only [LBTerm.shift, ihv hc.1 hle, ihb hc.2 (Nat.succ_le_succ hle)]
  | happ f a ihf iha =>
      simp only [LBClosed_app] at hc
      simp only [LBTerm.shift, ihf hc.1 hle, iha hc.2 hle]
  | hconstruct iid c' args ih =>
      simp only [LBClosed_construct, LBClosedArgs_iff] at hc
      simp only [LBTerm.shift, LBTerm.shiftArgs_eq_map]
      rw [List.map_congr_left (fun x hx => ih x hx (hc x hx) hle), List.map_id_fun', id_eq]
  | hcase info discr alts ihd iha =>
      simp only [LBClosed_case, LBClosedAlts_iff] at hc
      simp only [LBTerm.shift, ihd hc.1 hle, LBTerm.shiftAlts_eq_map]
      rw [List.map_congr_left (fun a ha => ?_), List.map_id_fun', id_eq]
      rw [iha a ha (hc.2 a ha) (Nat.add_le_add_right hle _)]
  | hproj p e ih => simp only [LBClosed_proj] at hc; simp only [LBTerm.shift, ih hc hle]
  | hfix defs i ih =>
      simp only [LBClosed_fix, LBClosedDefs_iff] at hc
      simp only [LBTerm.shift]
      congr 1
      have key : ∀ (l : List (@FixDef LBTerm)),
          (∀ x ∈ l, LBTerm.shift d (c + defs.length) x.body = x.body) →
          LBTerm.shiftDefs d (c + defs.length) l = l := by
        intro l hshl
        induction l with
        | nil => rfl
        | cons fd rest ihr =>
            simp only [LBTerm.shiftDefs, hshl fd (List.mem_cons_self ..),
              ihr (fun x hx => hshl x (List.mem_cons_of_mem _ hx))]
      exact key defs (fun x hx => ih x hx (hc x hx) (by omega))

theorem LBClosed.subst_eq {t : LBTerm} {k : Nat} (hc : LBClosed t k)
    {c : Nat} (hle : k ≤ c) (s : LBTerm) : LBTerm.subst s c t = t := by
  induction t using LBTerm.recData generalizing k c with
  | hbox | hfvar | hconst | hprim => rfl
  | hbvar i => simp only [LBClosed_bvar] at hc; simp only [LBTerm.subst]; rw [if_pos (by omega)]
  | hlam n b ih =>
      simp only [LBClosed_lambda] at hc
      simp only [LBTerm.subst, ih hc (Nat.succ_le_succ hle)]
  | hletIn n v b ihv ihb =>
      simp only [LBClosed_letIn] at hc
      simp only [LBTerm.subst, ihv hc.1 hle, ihb hc.2 (Nat.succ_le_succ hle)]
  | happ f a ihf iha =>
      simp only [LBClosed_app] at hc
      simp only [LBTerm.subst, ihf hc.1 hle, iha hc.2 hle]
  | hconstruct iid c' args ih =>
      simp only [LBClosed_construct, LBClosedArgs_iff] at hc
      simp only [LBTerm.subst, LBTerm.substArgs_eq_map]
      rw [List.map_congr_left (fun x hx => ih x hx (hc x hx) hle), List.map_id_fun', id_eq]
  | hcase info discr alts ihd iha =>
      simp only [LBClosed_case, LBClosedAlts_iff] at hc
      simp only [LBTerm.subst, ihd hc.1 hle, LBTerm.substAlts_eq_map]
      rw [List.map_congr_left (fun a ha => ?_), List.map_id_fun', id_eq]
      rw [iha a ha (hc.2 a ha) (Nat.add_le_add_right hle _)]
  | hproj p e ih => simp only [LBClosed_proj] at hc; simp only [LBTerm.subst, ih hc hle]
  | hfix defs i ih =>
      simp only [LBClosed_fix, LBClosedDefs_iff] at hc
      simp only [LBTerm.subst]
      congr 1
      have key : ∀ (l : List (@FixDef LBTerm)),
          (∀ x ∈ l, LBTerm.subst s (c + defs.length) x.body = x.body) →
          LBTerm.substDefs s (c + defs.length) l = l := by
        intro l hshl
        induction l with
        | nil => rfl
        | cons fd rest ihr =>
            simp only [LBTerm.substDefs, hshl fd (List.mem_cons_self ..),
              ihr (fun x hx => hshl x (List.mem_cons_of_mem _ hx))]
      exact key defs (fun x hx => ih x hx (hc x hx) (by omega))

/-! ## Part 2 — `LBClosed` under shift, subst, and the spine/telescope builders -/

/-- Closedness is monotone in the bound. -/
theorem LBClosed.mono {t : LBTerm} {k k' : Nat} (h : LBClosed t k) (hle : k ≤ k') :
    LBClosed t k' := by
  induction t using LBTerm.recData generalizing k k' with
  | hbox | hfvar | hconst | hprim => trivial
  | hbvar i => simp only [LBClosed_bvar] at h ⊢; omega
  | hlam n b ih =>
      simp only [LBClosed_lambda] at h ⊢
      exact ih h (Nat.succ_le_succ hle)
  | hletIn n v b ihv ihb =>
      simp only [LBClosed_letIn] at h ⊢
      exact ⟨ihv h.1 hle, ihb h.2 (Nat.succ_le_succ hle)⟩
  | happ f a ihf iha =>
      simp only [LBClosed_app] at h ⊢
      exact ⟨ihf h.1 hle, iha h.2 hle⟩
  | hconstruct iid ci args ih =>
      simp only [LBClosed_construct, LBClosedArgs_iff] at h ⊢
      exact fun x hx => ih x hx (h x hx) hle
  | hcase info discr alts ihd iha =>
      simp only [LBClosed_case, LBClosedAlts_iff] at h ⊢
      exact ⟨ihd h.1 hle, fun a ha => iha a ha (h.2 a ha) (Nat.add_le_add_right hle _)⟩
  | hproj p e ih => simp only [LBClosed_proj] at h ⊢; exact ih h hle
  | hfix defs i ih =>
      simp only [LBClosed_fix, LBClosedDefs_iff] at h ⊢
      exact fun fd hfd => ih fd hfd (h fd hfd) (Nat.add_le_add_right hle _)

/-- Shifting raises the closedness bound. -/
theorem LBClosed.shift {t : LBTerm} {k : Nat} (h : LBClosed t k) (d c : Nat) :
    LBClosed (LBTerm.shift d c t) (k + d) := by
  induction t using LBTerm.recData generalizing k c with
  | hbox | hfvar | hconst | hprim => trivial
  | hbvar i =>
      simp only [LBClosed_bvar] at h
      simp only [LBTerm.shift]
      split <;> simp only [LBClosed_bvar] <;> omega
  | hlam n b ih =>
      simp only [LBClosed_lambda] at h
      simp only [LBTerm.shift, LBClosed_lambda]
      exact (ih h (c + 1)).mono (by omega)
  | hletIn n v b ihv ihb =>
      simp only [LBClosed_letIn] at h
      simp only [LBTerm.shift, LBClosed_letIn]
      exact ⟨ihv h.1 c, (ihb h.2 (c + 1)).mono (by omega)⟩
  | happ f a ihf iha =>
      simp only [LBClosed_app] at h
      simp only [LBTerm.shift, LBClosed_app]
      exact ⟨ihf h.1 c, iha h.2 c⟩
  | hconstruct iid ci args ih =>
      simp only [LBClosed_construct, LBClosedArgs_iff] at h
      simp only [LBTerm.shift, LBClosed_construct, LBClosedArgs_iff, LBTerm.shiftArgs_eq_map]
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact ih y hy (h y hy) c
  | hcase info discr alts ihd iha =>
      simp only [LBClosed_case, LBClosedAlts_iff] at h
      simp only [LBTerm.shift, LBClosed_case, LBClosedAlts_iff, LBTerm.shiftAlts_eq_map]
      refine ⟨ihd h.1 c, fun a ha => ?_⟩
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
      show LBClosed (LBTerm.shift d (c + y.1.length) y.2) (k + d + y.1.length)
      exact (iha y hy (h.2 y hy) (c + y.1.length)).mono (by omega)
  | hproj p e ih => simp only [LBClosed_proj] at h ⊢; exact ih h c
  | hfix defs i ih =>
      simp only [LBClosed_fix, LBClosedDefs_iff] at h
      simp only [LBTerm.shift, LBClosed_fix, LBClosedDefs_iff, LBTerm.shiftDefs_eq_map,
        List.length_map]
      intro fd hfd
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hfd
      exact (ih y hy (h y hy) (c + defs.length)).mono (by omega)

/-- **The substitution bound law.** Substituting `s` (closed below `k`) at depth `d`
into a term closed below `k + d + 1` yields a term closed below `k + d`. The `d`
tracks the binders crossed; `subst`'s `bvar = d` case emits `shift d 0 s`, which is
why the substitutee's own bound `k` is *added* to `d` rather than compared to it. -/
theorem LBClosed.subst_gen {t : LBTerm} {k : Nat} (d : Nat) (ht : LBClosed t (k + d + 1))
    {s : LBTerm} (hs : LBClosed s k) : LBClosed (LBTerm.subst s d t) (k + d) := by
  induction t using LBTerm.recData generalizing d with
  | hbox | hfvar | hconst | hprim => trivial
  | hbvar i =>
      simp only [LBClosed_bvar] at ht
      simp only [LBTerm.subst]
      split
      · simp only [LBClosed_bvar]; omega
      · split
        · exact hs.shift d 0
        · simp only [LBClosed_bvar]; omega
  | hlam n b ih =>
      simp only [LBClosed_lambda] at ht
      simp only [LBTerm.subst, LBClosed_lambda]
      exact ih (d + 1) ht
  | hletIn n v b ihv ihb =>
      simp only [LBClosed_letIn] at ht
      simp only [LBTerm.subst, LBClosed_letIn]
      exact ⟨ihv d ht.1, ihb (d + 1) ht.2⟩
  | happ f a ihf iha =>
      simp only [LBClosed_app] at ht
      simp only [LBTerm.subst, LBClosed_app]
      exact ⟨ihf d ht.1, iha d ht.2⟩
  | hconstruct iid ci args ih =>
      simp only [LBClosed_construct, LBClosedArgs_iff] at ht
      simp only [LBTerm.subst, LBClosed_construct, LBClosedArgs_iff, LBTerm.substArgs_eq_map]
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact ih y hy d (ht y hy)
  | hcase info discr alts ihd iha =>
      simp only [LBClosed_case, LBClosedAlts_iff] at ht
      simp only [LBTerm.subst, LBClosed_case, LBClosedAlts_iff, LBTerm.substAlts_eq_map]
      refine ⟨ihd d ht.1, fun a ha => ?_⟩
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
      show LBClosed (LBTerm.subst s (d + y.1.length) y.2) (k + d + y.1.length)
      exact (iha y hy (d + y.1.length) ((ht.2 y hy).mono (by omega))).mono (by omega)
  | hproj p e ih => simp only [LBClosed_proj] at ht ⊢; exact ih d ht
  | hfix defs i ih =>
      simp only [LBClosed_fix, LBClosedDefs_iff] at ht
      simp only [LBTerm.subst, LBClosed_fix, LBClosedDefs_iff, LBTerm.substDefs_eq_map,
        List.length_map]
      intro fd hfd
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hfd
      exact (ih y hy (d + defs.length) ((ht y hy).mono (by omega))).mono (by omega)

/-- Substitution of a **closed** term at depth `k` lowers the bound from `k + 1` to `k`. -/
theorem LBClosed.subst {t : LBTerm} {k : Nat} (ht : LBClosed t (k + 1))
    {s : LBTerm} (hs : LBClosed s 0) : LBClosed (LBTerm.subst s k t) k := by
  have h := LBClosed.subst_gen (k := 0) k (by simpa using ht) hs
  simpa using h

/-- `subst1` of a closed term lowers the bound by one. -/
theorem LBClosed.subst1_gen {t : LBTerm} {k : Nat} (ht : LBClosed t (k + 1))
    {s : LBTerm} (hs : LBClosed s 0) : LBClosed (LBTerm.subst1 s t) k :=
  LBClosed.subst_gen (k := k) 0 ht (hs.mono (Nat.zero_le _))

theorem LBClosed.subst1 {t s : LBTerm} (ht : LBClosed t 1) (hs : LBClosed s 0) :
    LBClosed (LBTerm.subst1 s t) 0 := LBClosed.subst1_gen ht hs

/-- Simultaneous substitution of `ss.length` closed terms closes the term. -/
theorem LBClosed.substList {ss : List LBTerm} (hs : ∀ s ∈ ss, LBClosed s 0)
    {t : LBTerm} (ht : LBClosed t ss.length) : LBClosed (LBTerm.substList ss t) 0 := by
  induction ss generalizing t with
  | nil => exact ht
  | cons s0 rest ih =>
      simp only [List.length_cons] at ht
      exact ih (fun x hx => hs x (List.mem_cons_of_mem _ hx))
        (LBClosed.subst1_gen ht (hs s0 (List.mem_cons_self ..)))

/-- An application spine of closed pieces is closed. -/
theorem LBClosed.mkApps {hd : LBTerm} {k : Nat} (hhd : LBClosed hd k) {args : List LBTerm}
    (h : ∀ a ∈ args, LBClosed a k) : LBClosed (LBTerm.mkApps hd args) k := by
  induction args generalizing hd with
  | nil => exact hhd
  | cons a as ih =>
      rw [LBTerm.mkApps]
      exact ih ⟨hhd, h a (List.mem_cons_self ..)⟩ (fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- The head of a closed application spine is closed. -/
theorem LBClosed.mkApps_head {hd : LBTerm} {k : Nat} {args : List LBTerm}
    (h : LBClosed (LBTerm.mkApps hd args) k) : LBClosed hd k := by
  induction args generalizing hd with
  | nil => exact h
  | cons a as ih => exact (ih h).1

/-- The arguments of a closed application spine are closed. -/
theorem LBClosed.mkApps_inv {hd : LBTerm} {k : Nat} {args : List LBTerm}
    (h : LBClosed (LBTerm.mkApps hd args) k) : ∀ a ∈ args, LBClosed a k := by
  induction args generalizing hd with
  | nil => exact fun a ha => absurd ha (List.not_mem_nil)
  | cons a as ih =>
      rw [LBTerm.mkApps] at h
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact (LBClosed.mkApps_head h).2
      · exact ih h b hb

/-- A lambda telescope closes `names.length` levels. -/
theorem LBClosed.mkLambdas {names : List BinderName} {body : LBTerm} {k : Nat}
    (h : LBClosed body (k + names.length)) : LBClosed (mkLambdas names body) k := by
  induction names generalizing k with
  | nil => exact h
  | cons n ns ih =>
      simp only [LeanToLambdaBox.mkLambdas, LBClosed_lambda]
      exact ih (h.mono (by simp only [List.length_cons]; omega))

/-! ## Part 3 — the general de-Bruijn commutation kit

`shift`/`subst` interaction laws for arbitrary `LBTerm`s, culminating in
`LBTerm.subst_subst` (the standard distribution law). `Optimize.lean` proves
`.box`-specialised siblings of `subst_shift_cancel`/`subst_subst`; those live in a
different branch of the import DAG, so the general forms are re-derived here.

All the inductions are over `LBTerm.recData`, generalizing every cutoff. Arithmetic
side conditions are carried as *equations* (`hm : m = d + c`) rather than being baked
into the statement: crossing a binder turns `m + 1 = (d + 1) + c` into an `omega` step
instead of a rewrite, which is what keeps the `hcase`/`hfix` arms (where the cutoffs
move by a variable `ns.length`/`defs.length`) mechanical. -/

/-- `shift` on a variable, as a rewrite rule. -/
theorem LBTerm.shift_bvar (d c i : Nat) :
    LBTerm.shift d c (.bvar i) = if i ≥ c then .bvar (i + d) else .bvar i := by
  simp only [LBTerm.shift]

/-- `subst` on a variable, as a rewrite rule. -/
theorem LBTerm.subst_bvar (s : LBTerm) (d i : Nat) :
    LBTerm.subst s d (.bvar i)
      = if i < d then .bvar i else if i = d then LBTerm.shift d 0 s else .bvar (i - 1) := by
  simp only [LBTerm.subst]

/-- **Shift composition.** Two shifts collapse into one when the outer cutoff `c₂` lies
inside the band `[c₁, c₁ + d₁]` opened by the inner shift (so the outer shift moves
exactly the indices the inner one moved). -/
theorem LBTerm.shift_shift (d₁ d₂ : Nat) (c₁ c₂ : Nat) (h₁ : c₁ ≤ c₂) (h₂ : c₂ ≤ c₁ + d₁)
    (t : LBTerm) :
    LBTerm.shift d₂ c₂ (LBTerm.shift d₁ c₁ t) = LBTerm.shift (d₁ + d₂) c₁ t := by
  induction t using LBTerm.recData generalizing c₁ c₂ with
  | hbox | hfvar | hconst | hprim => rfl
  | hbvar i =>
      rw [LBTerm.shift_bvar d₁ c₁ i]
      by_cases hi : i ≥ c₁
      · rw [if_pos hi, LBTerm.shift_bvar, LBTerm.shift_bvar, if_pos (by omega), if_pos hi]
        congr 1; omega
      · rw [if_neg hi, LBTerm.shift_bvar, LBTerm.shift_bvar, if_neg (by omega), if_neg hi]
  | hlam n b ih => simp only [LBTerm.shift, ih (c₁ + 1) (c₂ + 1) (by omega) (by omega)]
  | hletIn n v b ihv ihb =>
      simp only [LBTerm.shift, ihv c₁ c₂ h₁ h₂, ihb (c₁ + 1) (c₂ + 1) (by omega) (by omega)]
  | happ f a ihf iha => simp only [LBTerm.shift, ihf c₁ c₂ h₁ h₂, iha c₁ c₂ h₁ h₂]
  | hproj p e ih => simp only [LBTerm.shift, ih c₁ c₂ h₁ h₂]
  | hconstruct iid ci args ih =>
      simp only [LBTerm.shift, LBTerm.shiftArgs_eq_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha; simp only [Function.comp]; exact ih a ha c₁ c₂ h₁ h₂
  | hcase info discr alts ihd iha =>
      simp only [LBTerm.shift, LBTerm.shiftAlts_eq_map, List.map_map, ihd c₁ c₂ h₁ h₂]
      congr 1
      apply List.map_congr_left
      intro a ha; simp only [Function.comp]
      rw [iha a ha (c₁ + a.1.length) (c₂ + a.1.length) (by omega) (by omega)]
  | hfix defs i ih =>
      simp only [LBTerm.shift, LBTerm.shiftDefs_eq_map, List.map_map, List.length_map]
      congr 1
      apply List.map_congr_left
      intro a ha; simp only [Function.comp]
      rw [ih a ha (c₁ + defs.length) (c₂ + defs.length) (by omega) (by omega)]

/-- **Substitution kills a shift.** Substituting *anything* at a depth `d` inside the
band `[c, c + n]` opened by a `shift (n+1) c` lowers that shift to `n` (no shifted
variable can land exactly on `d`). -/
theorem LBTerm.subst_shift_cancel (x : LBTerm) (n c d : Nat) (h₁ : c ≤ d) (h₂ : d ≤ c + n)
    (t : LBTerm) : LBTerm.subst x d (LBTerm.shift (n + 1) c t) = LBTerm.shift n c t := by
  induction t using LBTerm.recData generalizing c d with
  | hbox | hfvar | hconst | hprim => rfl
  | hbvar i =>
      rw [LBTerm.shift_bvar (n + 1) c i]
      by_cases hi : i ≥ c
      · rw [if_pos hi, LBTerm.subst_bvar, if_neg (by omega), if_neg (by omega),
          LBTerm.shift_bvar, if_pos hi]
        exact congrArg LBTerm.bvar (by omega)
      · rw [if_neg hi, LBTerm.subst_bvar, if_pos (by omega), LBTerm.shift_bvar, if_neg hi]
  | hlam nm b ih =>
      simp only [LBTerm.shift, LBTerm.subst, ih (c + 1) (d + 1) (by omega) (by omega)]
  | hletIn nm v b ihv ihb =>
      simp only [LBTerm.shift, LBTerm.subst, ihv c d h₁ h₂,
        ihb (c + 1) (d + 1) (by omega) (by omega)]
  | happ f a ihf iha => simp only [LBTerm.shift, LBTerm.subst, ihf c d h₁ h₂, iha c d h₁ h₂]
  | hproj p e ih => simp only [LBTerm.shift, LBTerm.subst, ih c d h₁ h₂]
  | hconstruct iid ci args ih =>
      simp only [LBTerm.shift, LBTerm.subst, LBTerm.shiftArgs_eq_map, LBTerm.substArgs_eq_map,
        List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha; simp only [Function.comp]; exact ih a ha c d h₁ h₂
  | hcase info discr alts ihd iha =>
      simp only [LBTerm.shift, LBTerm.subst, LBTerm.shiftAlts_eq_map, LBTerm.substAlts_eq_map,
        List.map_map, ihd c d h₁ h₂]
      congr 1
      apply List.map_congr_left
      intro a ha; simp only [Function.comp]
      rw [iha a ha (c + a.1.length) (d + a.1.length) (by omega) (by omega)]
  | hfix defs i ih =>
      simp only [LBTerm.shift, LBTerm.subst, LBTerm.shiftDefs_eq_map, LBTerm.substDefs_eq_map,
        List.map_map, List.length_map]
      congr 1
      apply List.map_congr_left
      intro a ha; simp only [Function.comp]
      rw [ih a ha (c + defs.length) (d + defs.length) (by omega) (by omega)]

/-- **Substitution commutes with an outer shift.** A `shift c b` (with `b ≤ d`, i.e. the
shift's cutoff is below the substitution depth) pushes the substitution depth from `d`
up to `m = d + c`. -/
theorem LBTerm.subst_shift_comm (s : LBTerm) (b d c m : Nat) (hb : b ≤ d) (hm : m = d + c)
    (t : LBTerm) :
    LBTerm.subst s m (LBTerm.shift c b t) = LBTerm.shift c b (LBTerm.subst s d t) := by
  induction t using LBTerm.recData generalizing b d m with
  | hbox | hfvar | hconst | hprim => rfl
  | hbvar i =>
      rw [LBTerm.shift_bvar c b i]
      by_cases hib : i ≥ b
      · rw [if_pos hib, LBTerm.subst_bvar, LBTerm.subst_bvar]
        rcases Nat.lt_trichotomy i d with hi | hi | hi
        · rw [if_pos (by omega), if_pos (by omega), LBTerm.shift_bvar, if_pos hib]
        · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega), hm,
            ← LBTerm.shift_shift d c 0 b (by omega) (by omega) s]
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
            LBTerm.shift_bvar, if_pos (by omega)]
          congr 1; omega
      · rw [if_neg hib, LBTerm.subst_bvar, LBTerm.subst_bvar, if_pos (by omega),
          if_pos (by omega), LBTerm.shift_bvar, if_neg hib]
  | hlam n b' ih =>
      simp only [LBTerm.shift, LBTerm.subst, ih (b + 1) (d + 1) (m + 1) (by omega) (by omega)]
  | hletIn n v b' ihv ihb =>
      simp only [LBTerm.shift, LBTerm.subst, ihv b d m hb hm,
        ihb (b + 1) (d + 1) (m + 1) (by omega) (by omega)]
  | happ f a ihf iha => simp only [LBTerm.shift, LBTerm.subst, ihf b d m hb hm, iha b d m hb hm]
  | hproj p e ih => simp only [LBTerm.shift, LBTerm.subst, ih b d m hb hm]
  | hconstruct iid ci args ih =>
      simp only [LBTerm.shift, LBTerm.subst, LBTerm.shiftArgs_eq_map, LBTerm.substArgs_eq_map,
        List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha; simp only [Function.comp]; exact ih a ha b d m hb hm
  | hcase info discr alts ihd iha =>
      simp only [LBTerm.shift, LBTerm.subst, LBTerm.shiftAlts_eq_map, LBTerm.substAlts_eq_map,
        List.map_map, ihd b d m hb hm]
      congr 1
      apply List.map_congr_left
      intro a ha; simp only [Function.comp]
      rw [iha a ha (b + a.1.length) (d + a.1.length) (m + a.1.length) (by omega) (by omega)]
  | hfix defs i ih =>
      simp only [LBTerm.shift, LBTerm.subst, LBTerm.shiftDefs_eq_map, LBTerm.substDefs_eq_map,
        List.map_map, List.length_map]
      congr 1
      apply List.map_congr_left
      intro a ha; simp only [Function.comp]
      rw [ih a ha (b + defs.length) (d + defs.length) (m + defs.length) (by omega) (by omega)]

/-- **Distribution of substitution over substitution**, with the number `e` of binders
crossed by the inner substitution kept general (`m = d + e`). -/
theorem LBTerm.subst_subst_gen (s t : LBTerm) (d e m : Nat) (hm : m = d + e) (u : LBTerm) :
    LBTerm.subst s m (LBTerm.subst t e u)
      = LBTerm.subst (LBTerm.subst s d t) e (LBTerm.subst s (m + 1) u) := by
  induction u using LBTerm.recData generalizing e m with
  | hbox | hfvar | hconst | hprim => rfl
  | hbvar i =>
      -- Resolve the two inner substitutions first; each `ite` is discharged as soon as it
      -- is introduced, so `rw` never has to pick between competing `ite`s.
      rw [LBTerm.subst_bvar t e i, LBTerm.subst_bvar s (m + 1) i]
      rcases Nat.lt_trichotomy i e with hi | hi | hi
      · -- `i < e`: untouched by both substitutions
        rw [if_pos hi, if_pos (by omega : i < m + 1),
          LBTerm.subst_bvar s m i, if_pos (by omega),
          LBTerm.subst_bvar (LBTerm.subst s d t) e i, if_pos hi]
      · -- `i = e`: the inner substitution fires; the outer one commutes past its shift
        rw [if_neg (by omega), if_pos hi, if_pos (by omega : i < m + 1),
          LBTerm.subst_bvar (LBTerm.subst s d t) e i, if_neg (by omega), if_pos hi]
        exact LBTerm.subst_shift_comm s 0 d e m (by omega) (by omega) t
      · -- `i > e`: the inner substitution decrements; split on the outer depth
        rw [if_neg (by omega), if_neg (by omega)]
        rcases Nat.lt_trichotomy i (m + 1) with hj | hj | hj
        · rw [if_pos hj, LBTerm.subst_bvar s m (i - 1), if_pos (by omega),
            LBTerm.subst_bvar (LBTerm.subst s d t) e i, if_neg (by omega), if_neg (by omega)]
        · -- `i = m + 1`: the outer substitution fires on both sides
          rw [if_neg (by omega), if_pos hj, LBTerm.subst_bvar s m (i - 1), if_neg (by omega),
            if_pos (by omega)]
          exact (LBTerm.subst_shift_cancel (LBTerm.subst s d t) m 0 e (by omega) (by omega) s).symm
        · rw [if_neg (by omega), if_neg (by omega), LBTerm.subst_bvar s m (i - 1),
            if_neg (by omega), if_neg (by omega),
            LBTerm.subst_bvar (LBTerm.subst s d t) e (i - 1), if_neg (by omega),
            if_neg (by omega)]
  | hlam n b ih =>
      simp only [LBTerm.subst, ih (e + 1) (m + 1) (by omega)]
  | hletIn n v b ihv ihb =>
      simp only [LBTerm.subst, ihv e m hm, ihb (e + 1) (m + 1) (by omega)]
  | happ f a ihf iha => simp only [LBTerm.subst, ihf e m hm, iha e m hm]
  | hproj p e' ih => simp only [LBTerm.subst, ih e m hm]
  | hconstruct iid ci args ih =>
      simp only [LBTerm.subst, LBTerm.substArgs_eq_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha; simp only [Function.comp]; exact ih a ha e m hm
  | hcase info discr alts ihd iha =>
      simp only [LBTerm.subst, LBTerm.substAlts_eq_map, List.map_map, ihd e m hm]
      congr 1
      apply List.map_congr_left
      intro a ha; simp only [Function.comp]
      rw [show m + 1 + a.1.length = m + a.1.length + 1 from by omega,
        iha a ha (e + a.1.length) (m + a.1.length) (by omega)]
  | hfix defs i ih =>
      simp only [LBTerm.subst, LBTerm.substDefs_eq_map, List.map_map, List.length_map]
      congr 1
      apply List.map_congr_left
      intro a ha; simp only [Function.comp]
      rw [show m + 1 + defs.length = m + defs.length + 1 from by omega,
        ih a ha (e + defs.length) (m + defs.length) (by omega)]

/-- Distribution of substitution over substitution (the standard de Bruijn law). -/
theorem LBTerm.subst_subst (s t u : LBTerm) (d : Nat) :
    LBTerm.subst s d (LBTerm.subst t 0 u)
      = LBTerm.subst (LBTerm.subst s d t) 0 (LBTerm.subst s (d + 1) u) :=
  LBTerm.subst_subst_gen s t d 0 d (by omega) u
