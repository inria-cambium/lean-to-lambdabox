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

theorem preservation_fix
    {Γ : ErasureCtx} {Δ : CExpr.Env} {E : GlobalDeclarations}
    (hEnv : EnvConsistent Γ Δ E)
    {e e' : CExpr} {t : LBTerm}
    (hSub : InSubset e)
    (he   : Erases Γ e t)
    (hred : CExpr.Step Δ e e') :
    ∃ t', LBTerm.Steps E t t' ∧ Erases Γ e' t' := by
  sorry

end ErasureProofs.Fix
