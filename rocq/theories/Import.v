(** * Import.v — the rocq-lean-import feasibility gate for WS-R.

    Two halves:

    1. The MetaRocq ground truth is reachable (the target of the equivalence).
    2. The Lean λ□ semantics, kernel-exported by lean4export to
       [rocq/export/{lbterm.classic,semantics}.out], is fed to rocq-lean-import.

    ** Result of the gate (reproduced by compiling this file): the semantics cone
    does NOT import. ** The single decisive root cause is [UInt32.toBitVec]:
    rocq-lean-import 0.0.1 predeclares [UInt32] with a [Fin]-typed field
    ([Record UInt32 := UInt32_mk { val0 : Fin UInt32_size }], see the installed
    prelude [LeanImport/Lean.v] and [src/lean.ml]'s hardcoded
    [predeclared_ind_kind = … | UInt32 | Char]), i.e. the *pre-BitVec* Lean
    representation. Lean v4.29.0's [UInt32] is [BitVec 32]-backed, so the exported
    [UInt32.toBitVec := fun self => self.val0] has imported type
    [UInt32 -> Fin UInt32_size] but expected type [UInt32 -> BitVec (2^32)], which
    the tool cannot reconcile. Since v4.29 [String] is UTF-8/[ByteArray]-backed,
    [String]'s validity predicate pulls [UInt32.toBitVec] in, so [String] is
    skipped — and every [Kername]/[BinderName]/[LBTerm] carries a [String], so the
    ENTIRE semantics relation (LBTerm, WcbvEval, WcbvEvalT, All2T, GlobalDeclarations,
    wcbvEvalT_iff) is skipped in cascade. See [notes/EQUIV_FINDINGS.md].

    Consequence: the intended kernel-level *transport* of the Lean semantics is
    infeasible with the pinned tool; the equivalence falls back to a manual Rocq
    restatement validated against the kernel export (Translate.v onward). This file
    compiles under [Set Lean Error Mode "Skip"] (the importer reports [Done!] and
    skips the unimportable declarations), reproducing the finding on every build.

    NOTE: this gate deliberately does NOT [Require] MetaRocq. Co-loading MetaRocq's
    (very large) environment makes the [Lean Import] elaboration pathologically slow
    (per-step cost scales with the ambient environment); the MetaRocq target
    interface lives in [Iface.v] instead. *)

(* The Lean import gate. We import the minimal [Char] cone
   (rocq/export/char.classic.txt, ~856 lines) which isolates the *decisive* root
   error, [UInt32.toBitVec], in seconds. The larger committed exports exhibit the
   same failure at scale: rocq/export/lbterm.classic.txt (~9.3k lines) shows the
   full [UInt32.toBitVec] -> [String] -> [LBTerm] cascade (18 skips), and
   rocq/export/semantics.out (~41.8k lines) skips 146 including the entire
   WcbvEval/WcbvEvalT/All2T/wcbvEvalT_iff layer. [Skip] mode keeps this compiling
   (the importer prints [Done!] and skips the unimportable declarations). *)
From LeanImport Require Lean.
Set Lean Error Mode "Skip".
(* Path is relative to the build CWD (rocq/, where the Makefile runs coqc). *)
Lean Import "export/char.classic.txt".
(* [UInt32.toBitVec] is skipped here (its imported type [Fin UInt32_size] cannot be
   unified with the expected [BitVec (2^32)]); at scale this is what makes [String]
   -- hence [LBTerm] and the whole semantics relation -- unimportable. *)
