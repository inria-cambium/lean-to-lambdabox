(** * Equivalence.v — top-level equivalence (roadmap).

    IMPORTANT trust note. The intended result — validate the Lean λ□ semantics by
    *kernel-transporting* it into Rocq via rocq-lean-import and proving it equivalent
    to MetaRocq [EWcbvEval.eval] — is BLOCKED: the pinned rocq-lean-import 0.0.1
    cannot import Lean v4.29's [String]/[UInt32] (see Import.v / EQUIV_FINDINGS). The
    fallback taken here restates the Lean λ□ term language and semantics in Rocq
    (Translate.v [LBTerm]/[T], SubstAgree.v [shift]/[subst] agreement, and the
    Wf/EnvAgree/ValuesAgree/Backward/Forward roadmap), validated against the
    kernel-level export [rocq/export/semantics.out] + [LeanToLambdaBox/Semantics/*].
    The residual gap vs the intended result: the Lean side is transcribed by hand
    (eyeball-validated against the export), NOT transported by the trusted importer.

    Target theorem (fwd + bwd, on the wf fvar-free closed fragment,
    [with_constructor_as_block = false]):
      [WcbvEvalT-restated Γ fl t v  <->  eval (TEnv Γ) fl (T t) (T v)].
    Its [Nonempty]-image ties to the Lean [WcbvEval] via the exported (axiom-free
    mod propext) [wcbvEvalT_iff] (LeanToLambdaBox/Export/EvalT.lean). Combines
    Forward + Backward; records [Print Assumptions] (expected: only Rocq primitive
    types [PrimString]/[PrimInt63]/[PrimFloat], as for the landed SubstAgree lemmas).
    Not assembled yet; depends on Backward + Forward. *)
