import LeanToLambdaBox.Proofs.Fix

/-!
Stage 5 of the verified-erasure programme: proof and type irrelevance.

This is the last stage and discharges the full `erase_preservation`
theorem from `Correctness.lean`. Conceptually it shows that erasing
irrelevant subterms (proofs and type formers) to `box` preserves the
operational behavior of the program.

Beyond Stage 4, this stage handles:
  * the universally-quantified `Erases.box` rule — every CExpr can erase
    to `.box` regardless of its shape, provided the source is irrelevant;
  * the requirement that `box` is a value on the LBTerm side and so
    contributes no further reduction obligation;
  * the elimination of `.box` arguments in `ctor`-application and
    `cases`-discriminee positions where the irrelevant-args pruning of
    the implementation can leave `.box`-tagged residue.

Once this lands, the staged programme replaces the `sorry` in
`Correctness.erase_preservation` by combining the five stage theorems.
-/

namespace ErasureProofs.Irrel

/-- Final stage: the full `CExpr`. -/
abbrev InSubset := fun (_ : CExpr) => True

/--
**Stage-5 / final preservation** — the statement targeted by the staged
programme. Stub at this point; the proof discharges by combining
`preservation_lambda`, `preservation_constants`, `preservation_inductives`,
and `preservation_fix`, plus a dedicated lemma showing that `.box` on the
target side absorbs any source-side reduction inside an irrelevant
subterm.
-/
theorem preservation_irrel
    {Γ : ErasureCtx} {Δ : CExpr.Env} {E : GlobalDeclarations}
    (hEnv : EnvConsistent Γ Δ E)
    {e e' : CExpr} {t : LBTerm}
    (he   : Erases Γ e t)
    (hred : CExpr.Step Δ e e') :
    ∃ t', LBTerm.Steps E t t' ∧ Erases Γ e' t' := by
  sorry

end ErasureProofs.Irrel
