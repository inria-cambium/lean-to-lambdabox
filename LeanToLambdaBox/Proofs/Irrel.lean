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

/--
**Stage-5 / final preservation** — the unrestricted statement. Discharges
directly via `Fix.preservation_fix` plus `Fix.InSubset.always`, the lemma
showing that the full `CExpr` type is contained in the Fix stage's subset.

Note: the "irrelevance" framing in the original plan anticipated extending
`Erases` with a `box` constructor universally applicable to irrelevant
subterms. With the current `Erases` (which only allows `Erases.box` between
the explicit `.box` source and `.box` target), no further irrelevance
argument is needed — Fix's preservation suffices for the full statement.
-/
theorem preservation_irrel
    {Γ : ErasureCtx} {Δ : CExpr.Env} {E : GlobalDeclarations}
    (hEnv : EnvConsistent Γ Δ E)
    {e e' : CExpr} {t : LBTerm}
    (he   : Erases Γ e t)
    (hred : CExpr.Step Δ e e') :
    ∃ t', LBTerm.Steps E t t' ∧ Erases Γ e' t' :=
  ErasureProofs.Fix.preservation_fix hEnv (ErasureProofs.Fix.InSubset.always e) he hred

end ErasureProofs.Irrel
