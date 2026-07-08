(** * SubstAgree.v — the de-Bruijn substitution correspondence (fallback).

    The Lean-side [shift]/[subst] on the restated [LBTerm] (Translate.v) agree,
    under [T], with MetaRocq's [ELiftSubst.lift]/[ELiftSubst.subst]. This is the
    load-bearing crux of the equivalence (it feeds the β/ζ/δ/ι/fix cases). The Lean
    [shift]/[subst] here transcribe [LeanToLambdaBox/Semantics/Substitution.lean]
    (validated against [rocq/export/semantics.out]); the conventions match
    lean4lean's [liftLooseBVars']/[instantiate1'], i.e. MetaRocq [lift]/[subst [·]].

    Proved here (admitted-free): [T_shift] ([shift] ↔ [lift]) and [T_subst]
    ([subst] ↔ [subst [·]] on singletons). [substList]/[iota_red]/[fixSubst]
    agreement (which additionally need closedness, since Lean [substList] uses the
    lifting [subst] while MetaRocq [substl] uses the non-lifting [csubst], agreeing
    only on closed substitutees — [ECSubst.closed_subst]) are the documented
    continuation (see the roadmap at the end + [Wf.v]). *)

From MetaRocq.Common Require Import BasicAst Kernames.
From MetaRocq.Utils Require Import MRList All_Forall.
From MetaRocq.Erasure Require Import EAst ELiftSubst.
From Stdlib Require Import List Arith Lia.
Import ListNotations.
From LeanLambdaBoxEquiv Require Import Translate.

(** ** Lean [shift] on the restated [LBTerm] (Substitution.lean [shift d cutoff]). *)
Fixpoint Lshift (d c : nat) (t : LBTerm) : LBTerm :=
  match t with
  | LBox => LBox
  | LRel i => if Nat.leb c i then LRel (i + d) else LRel i
  | LLambda na b => LLambda na (Lshift d (S c) b)
  | LLetIn na v b => LLetIn na (Lshift d c v) (Lshift d (S c) b)
  | LApp f a => LApp (Lshift d c f) (Lshift d c a)
  | LConst kn => LConst kn
  | LConstruct ind k args => LConstruct ind k (map (Lshift d c) args)
  | LCase ci scr brs =>
      LCase ci (Lshift d c scr)
        (map (fun br => (fst br, Lshift d (length (fst br) + c) (snd br))) brs)
  | LProj p e => LProj p (Lshift d c e)
  | LFix defs i =>
      LFix (map (fun dd => (fst dd, (Lshift d (length defs + c) (fst (snd dd)), snd (snd dd)))) defs) i
  end.

(** ** [shift] ↔ [lift].

    Note MetaRocq [lift] on [tCase]/[tFix] shifts branch/def binders by
    [#|br.1| + k] / [#|mfix| + k]; the [map]/length bookkeeping below matches those
    to the Lean [length (fst br) + c] / [length defs + c]. *)
Lemma T_shift : forall t d k, T (Lshift d k t) = lift d k (T t).
Proof.
  intro t; induction t using LBTerm_ind'; intros d k; cbn.
  - reflexivity.
  - destruct (Nat.leb k n); cbn; [ rewrite Nat.add_comm | ]; reflexivity.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt1, IHt2.
  - reflexivity.
  - f_equal. rewrite !map_map. apply All_map_eq.
    eapply All_impl; [ exact X | ]. intros a Ha; exact (Ha d k).
  - rewrite IHt. f_equal. rewrite !map_map. apply All_map_eq.
    eapply All_impl; [ exact X | ]. intros br Hb; cbn. f_equal.
    exact (Hb d (length (fst br) + k)).
  - now rewrite IHt.
  - f_equal.
    rewrite !map_map. rewrite length_map. apply All_map_eq.
    eapply All_impl; [ exact X | ]. intros dd Hb; cbn. unfold map_def; cbn.
    now rewrite (Hb d (length defs + k)).
Qed.

(** ** Lean [subst] on the restated [LBTerm] (Substitution.lean [subst s d]).
    The matched index substitutes [Lshift d 0 s] — matching MetaRocq [subst [s'] k]
    which at the hit index yields [lift0 k s'] (= [lift k 0 s']). *)
Fixpoint Lsubst (s : LBTerm) (d : nat) (t : LBTerm) : LBTerm :=
  match t with
  | LBox => LBox
  | LRel i =>
      if Nat.ltb i d then LRel i
      else if Nat.eqb i d then Lshift d 0 s
      else LRel (i - 1)
  | LLambda na b => LLambda na (Lsubst s (S d) b)
  | LLetIn na v b => LLetIn na (Lsubst s d v) (Lsubst s (S d) b)
  | LApp f a => LApp (Lsubst s d f) (Lsubst s d a)
  | LConst kn => LConst kn
  | LConstruct ind k args => LConstruct ind k (map (Lsubst s d) args)
  | LCase ci scr brs =>
      LCase ci (Lsubst s d scr)
        (map (fun br => (fst br, Lsubst s (length (fst br) + d) (snd br))) brs)
  | LProj p e => LProj p (Lsubst s d e)
  | LFix defs i =>
      LFix (map (fun dd => (fst dd, (Lsubst s (length defs + d) (fst (snd dd)), snd (snd dd)))) defs) i
  end.

(** ** [subst] ↔ MetaRocq [subst [·]].

    Both operators substitute a single term and *lift* it by the crossed binder
    depth (Lean [shift d 0 s]; MetaRocq [lift0 k]); so no closedness is needed for
    this (singleton, lifting) form. [ECSubst.csubst] agreement (needed to line up
    with [eval]'s [csubst]/[substl]) then follows on closed substitutees via
    [ECSubst.closed_subst] — see the roadmap. *)
Lemma T_subst : forall t s d, T (Lsubst s d t) = subst [T s] d (T t).
Proof.
  intro t; induction t using LBTerm_ind'; intros s d.
  - reflexivity.
  - (* LRel n; keep the RHS [subst] intact and use the [subst_rel_*] lemmas *)
    cbn [T]. simpl Lsubst.
    destruct (Nat.ltb n d) eqn:Hlt.
    + (* n < d *) apply Nat.ltb_lt in Hlt.
      cbn [T]. rewrite subst_rel_lt by lia. reflexivity.
    + destruct (Nat.eqb n d) eqn:Heq.
      * (* n = d *) apply Nat.eqb_eq in Heq; subst d.
        rewrite T_shift.
        rewrite (subst_rel_eq [T s] n 0 (T s) n) by (reflexivity || lia).
        reflexivity.
      * (* n > d *) apply Nat.ltb_ge in Hlt. apply Nat.eqb_neq in Heq.
        cbn [T]. rewrite subst_rel_gt by (cbn [length]; lia).
        cbn [length]. reflexivity.
  - cbn. now rewrite IHt.
  - cbn. now rewrite IHt1, IHt2.
  - cbn. now rewrite IHt1, IHt2.
  - reflexivity.
  - cbn. f_equal. rewrite !map_map. apply All_map_eq.
    eapply All_impl; [ exact X | ]. intros a Ha; exact (Ha s d).
  - cbn. rewrite IHt. f_equal. rewrite !map_map. apply All_map_eq.
    eapply All_impl; [ exact X | ]. intros br Hb; cbn. f_equal.
    exact (Hb s (length (fst br) + d)).
  - cbn. now rewrite IHt.
  - cbn. f_equal. rewrite !map_map. rewrite length_map. apply All_map_eq.
    eapply All_impl; [ exact X | ]. intros dd Hb; cbn. unfold map_def; cbn.
    now rewrite (Hb s (length defs + d)).
Qed.

(** ROADMAP (continuation of the substitution agreement, needing closedness):
    - [T (substList ss t) = substl (map T ss) (T t)] when [Forall closedn0 (map T ss)]
      (Lean [substList] folds the lifting [subst1]; MetaRocq [substl] folds the
      non-lifting [csubst] — agree on closed elements via [ECSubst.closed_subst]).
    - [iota_red]: [T (substList ((skipn np args).rev) body)]
      = [iota_red np (map T args) (map fst brs, T body)] (immediate from the above +
      [map]/[rev]/[skipn] commuting with [map T]).
    - [fixSubst]/[cunfold_fix]: [map T (fixSubst defs) = fix_subst (T-defs)] and the
      [cunfold_fix] tuple agreement.
    These feed EnvAgree/ValuesAgree/Backward/Forward; see those files' headers. *)
