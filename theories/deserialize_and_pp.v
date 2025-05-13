From SimpleIO Require Import SimpleIO.
From LeanToLambdaBox Require Import NatEnv (nat_env).
From MetaCoq.Erasure Require Import EPretty (print_program).
From LambdaBox.serialization Require Import SerializeEAst (term_of_string).
From MetaCoq.Utils Require bytestring.
Require Import String.

Import IO.Notations.
Local Open Scope io_scope.

(* Print Visibility. *)
(* Print CeresDeserialize.error. *)

(* There is a coercion from string to ocaml_string. *)
Definition hw: ocaml_string := "Hello, World!"%string.
Definition main: IO unit :=
  sexp <- read_line;;
  let result := term_of_string (from_ostring sexp) in
  let out: String.string := match result with
    | inl err => "error"%string
    | inr term => bytestring.String.to_string (print_program (nat_env, term))
    end in
  print_string out
.

(*
   RunIO seems to be a hack using extraction to files in /tmp/coq_simple_io/.
   These lines copied from lambda-box-extraction/theories/Extraction.v are necessary
   to make the extraction work correctly. 
*)
From Coq Require Import ExtrOcamlBasic.
From Coq Require Import ExtrOCamlFloats.
From Coq Require Import ExtrOCamlInt63.

Extract Constant SerializePrimitives.string_of_prim_int =>
  "(fun s -> failwith ""string_of_prim_int not implemented"")".
Extract Constant SerializePrimitives.prim_int_of_string =>
  "(fun s -> failwith ""prim_int_of_string not implemented"")".

Extract Constant SerializePrimitives.string_of_prim_float =>
  "(fun s -> failwith ""string_of_prim_float not implemented"")".
Extract Constant SerializePrimitives.prim_float_of_string =>
  "(fun s -> failwith ""prim_float_of_string not implemented"")".

RunIO IOMode Forward.
(* Stepping to the line below in an interactive session will block. *)
RunIO main.
