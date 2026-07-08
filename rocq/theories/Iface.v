(** * Iface.v — MetaRocq-side interface for the equivalence.

    Originally this was meant to collect the rocq-lean-import-*imported* Lean
    definitions ([LBTerm], [WcbvEval]/[WcbvEvalT], values, environments) under
    stable names. As [Import.v] establishes, the import genuinely fails (the
    [UInt32]/[String] version skew of rocq-lean-import 0.0.1 vs Lean v4.29), so
    none of those constants exist in Rocq. The equivalence therefore builds on a
    manual restatement of the Lean side ([Translate.v]) validated against the
    kernel export [rocq/export/semantics.out].

    What this file *can* pin is the MetaRocq target interface — the exact ground
    truth the restatement is checked against. Keeping the [Check]s here documents,
    against the installed [MetaRocq.Erasure 1.5.1+9.1], the shapes the translation
    and the agreement lemmas target. *)

From MetaRocq.Erasure Require Import EWcbvEval EAst EGlobalEnv ECSubst ELiftSubst.
From MetaRocq.Common Require Import BasicAst Kernames.

(** The target term language and its evaluation/value predicates. *)
Check EAst.term.
Check @EWcbvEval.eval    : forall {wfl : WcbvFlags}, global_declarations -> term -> term -> Set.
Check @EWcbvEval.value   : forall {wfl : WcbvFlags}, global_declarations -> term -> Type.
Check @EWcbvEval.atom    : forall {wfl : WcbvFlags}, global_declarations -> term -> bool.

(** The evaluation flags: the validated target is [with_constructor_as_block = false]
    (MetaRocq [default_wcbv_flags]/[opt_wcbv_flags]/[target_wcbv_flags]). *)
Check EWcbvEval.opt_wcbv_flags.
Check EWcbvEval.target_wcbv_flags.
Check EWcbvEval.default_wcbv_flags.

(** Substitution and the reduction helpers the Lean [subst]/[substList]/[iota_red]/
    [fixSubst]/[cunfold_fix] must agree with (see [SubstAgree.v]). *)
Check @ELiftSubst.lift   : nat -> nat -> term -> term.
Check @ELiftSubst.subst  : list term -> nat -> term -> term.
Check @ECSubst.csubst    : term -> nat -> term -> term.
Check @ECSubst.substl    : list term -> term -> term.
Check @EGlobalEnv.iota_red    : nat -> list term -> list BasicAst.name * term -> term.
Check @EGlobalEnv.fix_subst.
Check @EGlobalEnv.cunfold_fix.

(** Environment lookup and constructor arity (see [EnvAgree.v]). *)
Check @EGlobalEnv.lookup_env       : global_declarations -> kername -> option global_decl.
Check @EGlobalEnv.lookup_constructor.
Check @EGlobalEnv.constructor_isprop_pars_decl.
Check @EGlobalEnv.inductive_isprop_and_pars.
Check EAst.cstr_arity.
