(** * Translate.v — the FALLBACK Lean λ□ restatement and its translation to EAst.

    The kernel-level import genuinely fails (see [Import.v] / [notes/EQUIV_FINDINGS.md]:
    rocq-lean-import 0.0.1 cannot import Lean v4.29's [String]/[UInt32]). Per the
    ranked fallback, we restate the Lean λ□ term language in Rocq and validate the
    restatement against the kernel export [rocq/export/semantics.out] +
    [LeanToLambdaBox/Basic.lean]. This file defines that restatement ([LBTerm]), the
    translation [T : LBTerm -> EAst.term] into MetaRocq's erasure calculus, a custom
    nested-induction principle, and [T]'s injectivity — the foundation the agreement
    lemmas build on.

    FRAGMENT. The restated [LBTerm] is the fvar-free, prim-free *core* of the Lean
    [LBTerm] (constructors [box bvar lambda letIn app const construct case proj fix]).
    This is exactly the fragment the equivalence targets: the Lean-specific [fvar]
    (locally-nameless free var; no [EAst] image beyond [tVar]) is excluded by the
    fvar-free hypothesis, and [prim] is a documented fragment restriction (as in the
    attack plan's exclusion list). Leaf payloads reuse MetaRocq's own [name]/
    [kername]/[inductive]/[projection], so [T] is the identity on them (matching the
    Lean [BinderName]/[Kername]/[InductiveId]/[ProjectionInfo] up to field renaming).

    A fix definition is encoded as [(dname, (dbody, rarg))] — mirroring Lean
    [FixDef {name; body; principalArgIdx}] and MetaRocq [def {dname; dbody; rarg}] —
    keeping the nested-induction bookkeeping first-order. *)

From MetaRocq.Common Require Import BasicAst Kernames.
From MetaRocq.Utils Require Import MRList All_Forall.
From MetaRocq.Erasure Require Import EAst.  (* imported last: its [def]/[dname] win the ambiguity *)
From Stdlib Require Import List.
Import ListNotations.

Inductive LBTerm : Set :=
| LBox
| LRel (n : nat)
| LLambda (na : name) (b : LBTerm)
| LLetIn (na : name) (v b : LBTerm)
| LApp (f a : LBTerm)
| LConst (kn : kername)
| LConstruct (ind : inductive) (c : nat) (args : list LBTerm)
| LCase (ci : inductive * nat) (discr : LBTerm) (brs : list (list name * LBTerm))
| LProj (p : projection) (e : LBTerm)
| LFix (defs : list (name * (LBTerm * nat))) (i : nat).

(** ** Translation into MetaRocq [EAst.term] (a structural map). *)
Fixpoint T (t : LBTerm) : term :=
  match t with
  | LBox => tBox
  | LRel n => tRel n
  | LLambda na b => tLambda na (T b)
  | LLetIn na v b => tLetIn na (T v) (T b)
  | LApp f a => tApp (T f) (T a)
  | LConst kn => tConst kn
  | LConstruct ind c args => tConstruct ind c (map T args)
  | LCase ci discr brs => tCase ci (T discr) (map (fun br => (fst br, T (snd br))) brs)
  | LProj p e => tProj p (T e)
  | LFix defs i =>
      tFix (map (fun d => ({| dname := fst d; dbody := T (fst (snd d)); rarg := snd (snd d) |} : def term)) defs) i
  end.

(** ** Custom nested-induction principle (mirrors [EInduction.term_forall_list_ind]);
    the default [LBTerm_ind] is too weak for the list payloads. *)
Lemma LBTerm_ind' (P : LBTerm -> Type) :
  P LBox ->
  (forall n, P (LRel n)) ->
  (forall na b, P b -> P (LLambda na b)) ->
  (forall na v b, P v -> P b -> P (LLetIn na v b)) ->
  (forall f a, P f -> P a -> P (LApp f a)) ->
  (forall kn, P (LConst kn)) ->
  (forall ind c args, All P args -> P (LConstruct ind c args)) ->
  (forall ci discr brs, P discr -> All (fun br => P (snd br)) brs -> P (LCase ci discr brs)) ->
  (forall p e, P e -> P (LProj p e)) ->
  (forall defs i, All (fun d => P (fst (snd d))) defs -> P (LFix defs i)) ->
  forall t, P t.
Proof.
  intros hBox hRel hLam hLet hApp hConst hConstruct hCase hProj hFix.
  fix aux 1.
  intro t; destruct t.
  - apply hBox.
  - apply hRel.
  - apply hLam; apply aux.
  - apply hLet; apply aux.
  - apply hApp; apply aux.
  - apply hConst.
  - apply hConstruct.
    revert args; fix auxl 1; intro l; destruct l; constructor; [ apply aux | apply auxl ].
  - apply hCase; [ apply aux | ].
    revert brs; fix auxl 1; intro l; destruct l; constructor; [ apply aux | apply auxl ].
  - apply hProj; apply aux.
  - apply hFix.
    revert defs; fix auxl 1; intro l; destruct l; constructor; [ apply aux | apply auxl ].
Defined.

(** ** Injectivity of [T]: every [EAst] term in the image of [T] comes from a unique
    [LBTerm] (feeds the backward simulation). *)
Lemma T_inj : forall t1 t2, T t1 = T t2 -> t1 = t2.
Proof.
  intro t1; induction t1 using LBTerm_ind'; intros t2 Heq;
    destruct t2; cbn in Heq; try discriminate.
  - reflexivity.
  - now injection Heq as ->.
  - injection Heq as -> Hb. now rewrite (IHt1 _ Hb).
  - injection Heq as -> Hv Hb. now rewrite (IHt1_1 _ Hv), (IHt1_2 _ Hb).
  - injection Heq as Hf Ha. now rewrite (IHt1_1 _ Hf), (IHt1_2 _ Ha).
  - now injection Heq as ->.
  - injection Heq as -> -> Hargs. f_equal.
    revert args0 Hargs; induction X as [|x l Hx Hl IH]; intros [|y l'] Hargs;
      cbn in Hargs; try discriminate; [ reflexivity | ].
    injection Hargs as Hxy Hll. now rewrite (Hx _ Hxy), (IH _ Hll).
  - injection Heq as -> Hd Hbrs. rewrite (IHt1 _ Hd). f_equal.
    revert brs0 Hbrs; induction X as [|[n b] l Hb Hl IH]; intros [|[n' b'] l'] Hbrs;
      cbn in Hbrs; try discriminate; [ reflexivity | ].
    injection Hbrs as Hn Hbb Hll. cbn in *. subst n'.
    now rewrite (Hb _ Hbb), (IH _ Hll).
  - injection Heq as -> He. now rewrite (IHt1 _ He).
  - injection Heq as Hdefs ->. f_equal.
    revert defs0 Hdefs; induction X as [|[n [b r]] l Hd Hl IH];
      intros [|[n' [b' r']] l'] Hdefs; cbn in Hdefs; try discriminate; [ reflexivity | ].
    injection Hdefs as Hn Hbb Hr Hll. cbn in *. subst n' r'.
    now rewrite (Hd _ Hbb), (IH _ Hll).
Qed.
