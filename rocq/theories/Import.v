(** * Import.v

    MetaRocq λ□ import smoke test for the [LeanLambdaBoxEquiv] development.

    This file confirms that the target λ□ language (MetaRocq's untyped erasure
    calculus [EAst], its weak call-by-value semantics [EWcbvEval.eval], and the
    global-environment helpers [EGlobalEnv]) is reachable from this project's
    Rocq switch.  It is the anchor the equivalence proof builds on: the
    hand-written Lean λ□ semantics (imported via rocq-lean-import) will be shown
    equivalent to [EWcbvEval.eval] over [EAst.term]. *)

From MetaRocq.Erasure Require Import EWcbvEval EAst EGlobalEnv.

Check @EWcbvEval.eval.
Print EAst.term.
