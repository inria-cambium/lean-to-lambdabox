From MetaCoq.Utils Require Import bytestring.
From MetaCoq.Erasure Require Import EAst.

Import List.ListNotations.
Local Open Scope list_scope.

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
  ind_bodies := [nat_body]
|}.
(* It is important that the mutual block is named "Nat". *)
Definition nat_entry: Kernames.kername*global_decl := ((empty_path, "Nat"%bs), nat_decl).

Definition nat_env: global_context := [nat_entry].
