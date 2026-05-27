import LeanToLambdaBox.Proofs.Constants

/-!
Stage 3 of the verified-erasure programme: add inductive constructors and
`casesOn` to the verified subset.

Beyond Stage 2, this stage handles:
  * the `.ctor` and `.cases` CExpr constructors;
  * the `iota` rule of `CExpr.Step` / `LBTerm.Step`;
  * the bookkeeping in the `Erases.ctor` / `Erases.cases` constructors,
    including the `InductiveId` lookup through `ErasureCtx.inductives`.

This is the largest single proof stage in the staged programme — case
analysis over reductions involving a possibly-mutual inductive type, plus
the bound-name handling in alternatives.

Stub: subset predicate and statement only. Proofs pending.
-/

namespace ErasureProofs.Inductives

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

theorem preservation_inductives
    {Γ : ErasureCtx} {Δ : CExpr.Env} {E : GlobalDeclarations}
    (hEnv : EnvConsistent Γ Δ E)
    {e e' : CExpr} {t : LBTerm}
    (hSub : InSubset e)
    (he   : Erases Γ e t)
    (hred : CExpr.Step Δ e e') :
    ∃ t', LBTerm.Steps E t t' ∧ Erases Γ e' t' := by
  sorry

end ErasureProofs.Inductives
