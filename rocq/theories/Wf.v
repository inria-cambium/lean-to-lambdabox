(** * Wf.v — well-formedness fragment for the equivalence (roadmap).

    The equivalence targets [T]-image terms (Translate.v) that are fvar-free (by
    restatement: the restated [LBTerm] has no fvar), CLOSED ([ELiftSubst.closedn 0])
    and declared/saturated (constructors applied at most to [cstr_arity]; constants/
    inductives present in the translated env). Closedness is the load-bearing
    hypothesis: Lean [substList] folds the *lifting* [subst1] while MetaRocq [substl]
    folds the non-lifting [csubst], and the two agree only on closed substitutees
    ([ECSubst.closed_subst : closed t -> csubst t k u = subst [t] k u]) — so
    [SubstAgree.T_subst] (proved unconditionally for the lifting [subst [·]])
    upgrades to the [csubst]/[substl] that [eval] uses precisely on the closed
    fragment. To carry: an [LClosedn : nat -> LBTerm -> bool] transcribing the
    Lean-side closedness with [LClosedn n t = closedn n (T t)], and eval-closedness
    preservation (analogue of MetaRocq [eval_closed]) threaded through β/ζ/δ/ι/fix.
    No obligations discharged here yet; this is the continuation anchor. *)
