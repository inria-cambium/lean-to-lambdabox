From MetaCoq.Utils Require Import bytestring.
From MetaCoq.Erasure Require Import EAst EPretty.
From LambdaBox.serialization Require Import SerializeEAst.
Require Import String.

(* A dummy term returned in case there is a deserialization error. *)
Axiom ErrorTerm: term.
Definition unwrap (x: CeresDeserialize.error + term) :=
  match x with
  | inl err => ErrorTerm
  | inr t => t
  end
.

(* Setting up an environment in which nat is defined, for testing/pretty-printing purposes. *)
Definition empty_path: Kernames.modpath := Kernames.MPfile nil.

Definition O_body: constructor_body := {|
  cstr_name := "zero"%bs;
  cstr_nargs := 0;
|}.
Definition S_body: constructor_body := {|
  cstr_name := "succ"%bs;
  cstr_nargs := 1;
|}.
Definition nat_body: one_inductive_body := {|
  (* The name here is irrelevant, used only for pretty-printing afaict. *)
  ind_name := "Natbodyname"%bs;
  ind_propositional := false;
  ind_kelim := Universes.IntoAny;
  ind_ctors := cons O_body (cons S_body nil);
  ind_projs := nil;
|}.
Definition nat_decl: global_decl := InductiveDecl {|
  ind_finite := BasicAst.Finite;
  ind_npars := 0;
  ind_bodies := cons nat_body nil
|}.
(* It is important that the mutual block is named "Nat". *)
Definition nat_entry: Kernames.kername*global_decl := ((empty_path, "Nat"%bs), nat_decl).

Definition env: global_context := cons nat_entry nil.

Definition Sterm: string :=
"(tLambda (nNamed ""n"") (tLambda (nNamed ""zero_case"") (tLambda (nNamed ""succ_case"") (tCase ((inductive ((MPfile ()) ""Nat"") 0) 0) (tRel 2) ((() (tRel 1)) (((nNamed ""n"")) (tApp (tRel 1) (tRel 0))))))))"
.
Definition t := unwrap (term_of_string Sterm).

Eval cbv in (print_program (env, t)).
