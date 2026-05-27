import LeanToLambdaBox.Proofs.Inductives

/-!
Stage 4 of the verified-erasure programme: add mutually-recursive fixpoints.

Beyond Stage 3, this stage handles:
  * the `.fix` CExpr constructor;
  * the `fixUnfold` rule of `CExpr.Step` / `LBTerm.Step`;
  * the simultaneous substitution that unfolds all mutual recursive
    references at once (`substList ((List.range n).map (CExpr.fix defs))`).

Mirrors MetaRocq's `EInduction` lemmas for `tFix`.

Stub: subset predicate and statement only.
-/

namespace ErasureProofs.Fix

inductive InSubset : CExpr → Prop
  | box                                           : InSubset .box
  | bvar (i)                                      : InSubset (.bvar i)
  | fvar (x)                                      : InSubset (.fvar x)
  | const (n)                                     : InSubset (.const n)
  | app  {f a} (hf : InSubset f) (ha : InSubset a) : InSubset (.app f a)
  | lam  (n) {b} (hb : InSubset b)                 : InSubset (.lam n b)
  | letE (n) {v b} (hv : InSubset v) (hb : InSubset b) : InSubset (.letE n v b)
  | ctor (tn) (k) {args} (hargs : ∀ i (h : i < args.length), InSubset args[i]) :
      InSubset (.ctor tn k args)
  | cases (tn) {discr} {alts} (hd : InSubset discr)
          (halts : ∀ i (h : i < alts.length), InSubset alts[i].2) :
      InSubset (.cases tn discr alts)
  | fix {defs} (i) (hdefs : ∀ j (h : j < defs.length), InSubset defs[j].2) :
      InSubset (.fix defs i)

open LBTerm CExpr ErasureProofs.Inductives

theorem preservation_fix
    {Γ : ErasureCtx} {Δ : CExpr.Env} {E : GlobalDeclarations}
    (hEnv : EnvConsistent Γ Δ E)
    {e e' : CExpr} {t : LBTerm}
    (hSub : InSubset e)
    (he   : Erases Γ e t)
    (hred : CExpr.Step Δ e e') :
    ∃ t', LBTerm.Steps E t t' ∧ Erases Γ e' t' := by
  induction he generalizing e' with
  | box                 => cases hred
  | bvar _              => cases hred
  | fvar _              => cases hred
  | lam _ _ _           => cases hred
  | const n_src kn hkn =>
    cases hred with
    | delta _ _ hΔ =>
      obtain ⟨body', henvLookup, herB⟩ := hEnv n_src e' hΔ
      refine ⟨body', LBTerm.Steps.single ?_, herB⟩
      have heq : LBTerm.envLookup E kn = some (.constantDecl ⟨some body'⟩) := by
        rw [← hkn]; exact henvLookup
      exact .delta _ _ heq
  | ctor _ _ _ _ _ _ _ =>
    cases hred
  | fix _ _ _ _ =>
    -- `.fix` does not step on its own; only when applied (handled in app case).
    cases hred
  | app hf ha ihf iha =>
    cases hSub with
    | app hSubf hSuba =>
      cases hred with
      | beta _ _ _ =>
        cases hf with
        | lam _ hb =>
          exact ⟨_, LBTerm.Steps.single (.beta _ _ _),
                 erases_subst_general ha 0 hb⟩
      | appLeft h =>
        obtain ⟨_, hsteps, hef'⟩ := ihf hSubf h
        exact ⟨_, LBTerm.Steps.appLeft hsteps, .app hef' ha⟩
      | appRight h =>
        obtain ⟨_, hsteps, hea'⟩ := iha hSuba h
        exact ⟨_, LBTerm.Steps.appRight hsteps, .app hf hea'⟩
      | fixUnfold defs i _ def_i h_def =>
        -- Source: e = .app (.fix defs i) arg, e' = .app (substList recCalls def_i.2) arg
        -- where recCalls = (List.range defs.length).map (fun j => .fix defs j)
        cases hf with
        | fix _ hl_defs hes_defs =>
          rename_i defs'
          obtain ⟨hi, hdef_eq⟩ := List.getElem?_eq_some_iff.mp h_def
          have hi' : i < defs'.length := hl_defs ▸ hi
          let recCallsC : List CExpr := (List.range defs.length).map (CExpr.fix defs)
          let recCallsL : List LBTerm := (List.range defs'.length).map (LBTerm.fix defs')
          have rl_len : recCallsC.length = recCallsL.length := by
            simp [recCallsC, recCallsL, List.length_map, List.length_range, hl_defs]
          have rl_pw : ∀ j (h : j < recCallsC.length),
                          Erases Γ recCallsC[j] (recCallsL[j]'(rl_len ▸ h)) := by
            intros j h
            have hjr : j < defs.length := by
              simp [recCallsC, List.length_map, List.length_range] at h; exact h
            have hjr' : j < defs'.length := hl_defs ▸ hjr
            have h_rangeC : j < (List.range defs.length).length := by
              simp [List.length_range]; exact hjr
            have h_rangeL : j < (List.range defs'.length).length := by
              simp [List.length_range]; exact hjr'
            have h_mapC : j < (List.map (CExpr.fix defs) (List.range defs.length)).length := by
              simp [List.length_map, List.length_range]; exact hjr
            have h_mapL : j < (List.map (LBTerm.fix defs') (List.range defs'.length)).length := by
              simp [List.length_map, List.length_range]; exact hjr'
            show Erases Γ
              ((List.map (CExpr.fix defs) (List.range defs.length))[j]'h_mapC)
              ((List.map (LBTerm.fix defs') (List.range defs'.length))[j]'h_mapL)
            rw [List.getElem_map, List.getElem_map,
                List.getElem_range, List.getElem_range]
            exact .fix j hl_defs hes_defs
          have hbody : Erases Γ def_i.2 defs'[i].body := by
            have := hes_defs i hi
            rw [hdef_eq] at this
            exact this
          have hi_def' : defs'[i]? = some defs'[i] := by
            simp [hi']
          exact ⟨_,
                 LBTerm.Steps.single (.fixUnfold defs' i _ defs'[i] hi_def'),
                 .app (erases_substList recCallsC recCallsL rl_len rl_pw hbody) ha⟩
  | letE _ hv hb _ihv _ihb =>
    cases hSub with
    | letE _ _ _ =>
      cases hred with
      | zeta _ _ _ =>
        exact ⟨_, LBTerm.Steps.single (.zeta _ _ _),
               erases_subst_general hv 0 hb⟩
  | cases tn iid np hi hd hl hns hes hd_ih _hes_ih =>
    rename_i alts alts'
    cases hSub with
    | cases _ hSubd _hSubalts =>
      cases hred with
      | iota _ k args _ names body h_alt =>
        cases hd with
        | ctor _ _ iid_some hi_some hl_args hes_args =>
          rename_i args'
          have hiid : iid_some = iid := Option.some.inj (hi_some.symm.trans hi)
          subst hiid
          obtain ⟨hk, halt_eq⟩ := List.getElem?_eq_some_iff.mp h_alt
          have hk' : k < alts'.length := hl ▸ hk
          have h_alt' : alts'[k]? = some (alts'[k].1, alts'[k].2) := by
            simp [hk']
          have hes_body : Erases Γ body alts'[k].2 := by
            have := hes k hk
            rw [halt_eq] at this
            exact this
          refine ⟨LBTerm.substList args' alts'[k].2,
                  LBTerm.Steps.single ?_,
                  erases_substList args args' hl_args hes_args hes_body⟩
          exact .iota (iid_some, np) k args' alts' alts'[k].1 alts'[k].2 h_alt'
      | casesDiscr h =>
        obtain ⟨discr_new', hsteps, herr_discr_new⟩ := hd_ih hSubd h
        refine ⟨_, LBTerm.Steps.caseDiscr hsteps, ?_⟩
        exact .cases tn iid np hi herr_discr_new hl hns hes

mutual
/-- `Fix.InSubset` is universal: every `CExpr` satisfies it.
This is the key bridge to the unrestricted `preservation_irrel` — Stage 5
will instantiate the InSubset hypothesis trivially. Defined via mutual
recursion across CExpr and its nested lists. -/
def InSubset.always : ∀ (e : CExpr), InSubset e
  | .box => .box
  | .bvar i => .bvar i
  | .fvar x => .fvar x
  | .const n => .const n
  | .app f a => .app (InSubset.always f) (InSubset.always a)
  | .lam n b => .lam n (InSubset.always b)
  | .letE n v b => .letE n (InSubset.always v) (InSubset.always b)
  | .ctor tn k args => .ctor tn k (InSubset.alwaysArgs args)
  | .cases tn discr alts =>
    .cases tn (InSubset.always discr) (InSubset.alwaysAlts alts)
  | .fix defs i => .fix i (InSubset.alwaysDefs defs)

def InSubset.alwaysArgs :
    ∀ (xs : List CExpr) (i : Nat) (h : i < xs.length), InSubset xs[i]
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | x :: _, 0, _ => InSubset.always x
  | _ :: rest, i + 1, h =>
    InSubset.alwaysArgs rest i (Nat.lt_of_succ_lt_succ h)

def InSubset.alwaysAlts :
    ∀ (alts : List (List Lean.Name × CExpr)) (i : Nat)
      (h : i < alts.length), InSubset alts[i].2
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | (_, b) :: _, 0, _ => InSubset.always b
  | _ :: rest, i + 1, h =>
    InSubset.alwaysAlts rest i (Nat.lt_of_succ_lt_succ h)

def InSubset.alwaysDefs :
    ∀ (defs : List (Lean.Name × CExpr)) (j : Nat)
      (h : j < defs.length), InSubset defs[j].2
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | (_, b) :: _, 0, _ => InSubset.always b
  | _ :: rest, j + 1, h =>
    InSubset.alwaysDefs rest j (Nat.lt_of_succ_lt_succ h)
end

end ErasureProofs.Fix
