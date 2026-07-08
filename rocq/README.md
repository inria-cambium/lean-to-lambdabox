# WS-R: Lean λ□ ⟷ MetaRocq EWcbvEval equivalence — Rocq toolchain

This directory holds the Rocq-side workstream that will prove the repo's
hand-written Lean λ□ semantics (`LeanToLambdaBox/Basic.lean` `LBTerm` +
`LeanToLambdaBox/Semantics/*.lean` `WcbvEval`) equivalent to MetaRocq's
`EWcbvEval.eval` over `EAst.term`.

Pipeline: **Lean sources → `lean4export` (classic text export) → `Lean Import`
(rocq-lean-import) → Rocq `theories/` → equivalence proof against MetaRocq**.

This README is the handoff for the proof workstream. It records the exact,
verified-working toolchain. Everything below was smoke-tested end to end on
2026-07-08.

---

## 1. opam switch

- Active switch: **`peregrine`** (OCaml 4.14.2), **Rocq 9.1.1** (`rocq` / `coqc`).
- MetaRocq: `rocq-metarocq-erasure 1.5.1+9.1` (and the rest of the
  `rocq-metarocq-*` 1.5.1+9.1 stack), `rocq-certirocq 0.9.1+9.1`,
  `rocq-stdlib 9.0.0`.
- Everything here lives in this switch. No separate switch was needed
  (see §2).

## 2. rocq-lean-import

- **Version installed: `rocq-lean-import 0.0.1`** (from rocq-community,
  tag v0.0.1).
- **Install route: ADDITIVE into `peregrine`.** `opam install --show-actions
  rocq-lean-import` proposed installing *only* `rocq-lean-import 0.0.1` — no
  rebuild/downgrade/removal of `rocq-core`, `rocq-metarocq-*`,
  `rocq-certirocq`, or `rocq-stdlib`. So it was installed directly into
  `peregrine` (`opam install -y rocq-lean-import`). The separate-switch
  fallback was NOT needed.
- Installed files:
  - `~/.opam/peregrine/lib/coq/user-contrib/LeanImport/Lean.{v,vo,glob}`
    — the prelude module (registers `lean.Nat`, `lean.eq`, `lean.quot`, …,
    declares ML module `coq-lean-import.plugin`).
  - `~/.opam/peregrine/lib/coq-lean-import/lean_import.cmxs` — the plugin.
  - Source (for reference): `~/.opam/peregrine/.opam-switch/sources/rocq-lean-import.0.0.1/src/{g_lean.mlg,lean.ml}`.

### Working incantation

```coq
From LeanImport Require Lean.        (* loads the plugin + prelude; VERIFIED *)
Lean Import "/abs/path/to/export.txt".
```

### Command grammar (from `src/g_lean.mlg` + `src/lean.ml`)

The only vernacular command is:

```
Lean Import "<file>" [<from>] [<until>].
```

- `<file>` — path to a **classic text** export file (see §3 for the format
  contract; NDJSON and export-format-v2.0.0 are NOT supported by 0.0.1).
- `<from>`, `<until>` — optional **line numbers**; import only the slice
  `[from, until)` of the file (lines counted from the start; `until` stops
  processing when the line counter reaches it). Omit both to import the
  whole file.

Options (all `Set … .` / `Unset … .`, or `Set Lean … <value>.`):

| Option | Type | Default | Meaning |
|---|---|---|---|
| `Lean Error Mode` | string `"Skip"｜"Stop"｜"Fail"` | `Fail` | On a declaration error: skip it, stop gracefully, or raise. Use `"Skip"` for lenient bulk imports. |
| `Lean Fancy Universes` | bool | off | Fancier universe handling. |
| `Lean Skip Missing Quotient` | bool | off | Tolerate a missing `Quot` package. |
| `Lean Just Parsing` | bool | off | Parse the file but do not build Rocq terms (fast format check). |
| `Lean Upfront Instantiation` | bool | — | Instantiate universe-polymorphic consts upfront. |
| `Lean Lazy Instantiation` | bool | — | Instantiate lazily. |
| `Lean Print Squash Info` | bool | off | Print squash diagnostics. |
| `Lean Line Timeout` | int | — | Per-line timeout. |

### Parseable token set (what 0.0.1's parser accepts)

`#NS #NI` (names), `#US #UM #UIM #UP` (universes),
`#EV #ES #EC #EA #EL #EP #EZ #EJ #ELN #ELS` (exprs),
`#DEF #AX #IND #QUOT` (declarations), `#PREFIX #INFIX #POSTFIX` (notation).
Declaration lines have the **v1.x** layout:

- `#DEF <name> <type> <value> <univs…>`
- `#AX <name> <type> <univs…>`
- `#IND <nparams> <name> <type> <nctors> <ctor-name/ctor-type pairs…> <univs…>`
  — **constructors are inline in the `#IND` line**.
- `#QUOT` — **bare, no arguments**.

There is **no** handler for `#CTOR`, `#REC`, `#RR`, `#THM`, `#OPAQ`, and **no**
version-header line. This is what forces the lean4export choice in §3.

## 3. lean4export — CRITICAL: classic v1.x emitter, ported to v4.29.0

Clone: `rocq/lean4export/` (github.com/leanprover/lean4export).

### The two format breaks (why no release tag works)

lean4export's on-disk format changed **twice**:

1. **text v1.x → text v2.0.0** at commit **`aca5d12`** ("Move to v2.0.0 format",
   2025-06-01). v2.0.0 adds a `2.0.0` version-header line, splits inductives into
   separate `#CTOR`/`#REC`/`#RR` lines, adds `#THM`/`#OPAQ`, and adds a `hints`
   field to `#DEF`. **rocq-lean-import 0.0.1 cannot parse v2.0.0** (see §2).
2. **text → NDJSON** at commit **`c840756`** ("Transition to ndjson export
   format", 2026-01-02). Pure JSON; also unparseable.

**Every git tag in the repo (v4.15.0 … v4.32.0-rc1) postdates break #1** — the
version tags were (re-)created on 2026-04-30 on the v2.0.0/NDJSON line and all
contain `aca5d12`. So there is **no release tag that emits the v1.x format** that
0.0.1 needs. In particular the tag literally named `v4.26.0` is v2.0.0/NDJSON,
not classic — do not be fooled by the version number.

The last commit emitting the **v1.x** format is **`c9f8373`** (the parent of
`aca5d12`; native toolchain `leanprover/lean4:v4.20.0-rc5`, untagged).

### What was done

The v1.x emitter (`Export.lean` + `Main.lean` from `c9f8373`, ~144 lines total,
self-contained, stable kernel APIs) was **ported verbatim onto toolchain
v4.29.0** to match the repo's `lean-toolchain` (so the export is produced by the
SAME Lean that compiles our sources). Concretely, in `rocq/lean4export/`:

- `HEAD` = detached at **`9847384` (tag v4.27.0-rc1)** — chosen only as a v4.2x
  build skeleton (lakefile/CI).
- `Export.lean` and `Main.lean` **overwritten byte-identical to `c9f8373`**
  (verified with `diff`).
- `lean-toolchain` **overwritten to `leanprover/lean4:v4.29.0`**.
- **Zero source changes were needed** — the v1.x emitter compiles unmodified on
  v4.29.0 (no kernel-API drift v4.20→v4.29).

To rebuild from scratch:
```sh
cd rocq/lean4export
git switch --detach v4.27.0-rc1
git show c9f8373:Export.lean > Export.lean
git show c9f8373:Main.lean   > Main.lean
printf 'leanprover/lean4:v4.29.0\n' > lean-toolchain
lake build
```

### Binary + invocation

- Binary: `rocq/lean4export/.lake/build/bin/lean4export`
- Invoke through `lake env` (sets `LEAN_PATH`):
  ```sh
  lake env .lake/build/bin/lean4export <Module …> [--export-unsafe] [-- <decl …>]
  ```
  e.g. `lake env .lake/build/bin/lean4export Init -- Nat.add`
  (omit `-- <decls>` to export the whole module closure).
  Note: recursors/constructors named directly are not emitted standalone by the
  v1.x emitter (`.recInfo`/`.ctorInfo` → skipped); they appear via their
  inductive. Ask for a `def`/inductive to see output.

### Smoke output (classic v1.x confirmed)

`… -- Nat.add` produces 278 lines, first lines:
```
1 #NS 0 Nat
2 #NS 1 zero
0 #EC 1
3 #NS 1 succ
4 #NS 0 n
1 #EP #BD 4 0 0
...
#IND 0 1 2 2 2 0 3 1
...
#DEF ...
```
Confirmed: **no `2.0.0` header, no `#CTOR`/`#REC`/`#THM`, bare-arg `#IND` with
inline ctors, `#DEF` present, not JSON** — i.e. exactly the token set §2 parses.

### End-to-end round-trip (VERIFIED)

`rocq/export/nat_add.classic.txt` was produced by the ported binary and imported
in Rocq with:
```coq
From LeanImport Require Lean.
Set Lean Error Mode "Skip".
Lean Import "…/rocq/export/nat_add.classic.txt".
```
Result: `Done!` — imported `Nat`, `Nat.add`, `Nat.below`, `Nat.brecOn`,
`Nat.casesOn`, … (9 entries, 69 names, 194 expr nodes). The full chain works.

## 4. Rocq scaffold + MetaRocq import

- `_CoqProject`: `-R theories LeanLambdaBoxEquiv` + the 10 theory files.
- `Makefile`: generated with `rocq makefile -f _CoqProject -o Makefile`
  (falls back to `coq_makefile`).
- `theories/`: `Import.v` (smoke test, below) + 9 stub files with role headers:
  `Iface Translate Wf SubstAgree EnvAgree ValuesAgree Backward Forward
  Equivalence`.
- `export/`, `scripts/`: artifact/helper dirs (`export/nat_add.classic.txt`
  is the round-trip sample).

### MetaRocq import path — VERIFIED

Logical path is **`MetaRocq.Erasure`** (not `MetaCoq`). `theories/Import.v`:
```coq
From MetaRocq.Erasure Require Import EWcbvEval EAst EGlobalEnv.
Check @EWcbvEval.eval.
Print EAst.term.
```
`make theories/Import.vo` succeeds and prints:

```
@eval : WcbvFlags -> global_context -> term -> term -> Set
```
```
Inductive term : Set :=
    tBox
  | tRel (_ : nat)
  | tVar (_ : Kernames.ident)
  | tEvar (_ : nat) (_ : list term)
  | tLambda (_ : BasicAst.name) (_ : term)
  | tLetIn (_ : BasicAst.name) (_ _ : term)
  | tApp (_ _ : term)
  | tConst (_ : Kernames.kername)
  | tConstruct (_ : Kernames.inductive) (_ : nat) (_ : list term)   (* block form *)
  | tCase (_ : Kernames.inductive * nat) (_ : term)
          (_ : list (list BasicAst.name * term))
  | tProj (_ : Kernames.projection) (_ : term)
  | tFix (_ : mfixpoint term) (_ : nat)
  | tCoFix (_ : mfixpoint term) (_ : nat)
  | tPrim (_ : EPrimitive.prim_val term)
  | tLazy (_ : term)
  | tForce (_ : term).
```
Note `tConstruct` carries `list term` (block/CertiCoq form), and the calculus
includes `tLazy`/`tForce` and `tPrim` — relevant to the value/agreement lemmas.

---

## Open items for the proof workstream

- **Which λ□ fragment to target.** The full `EAst.term` above is large; the Lean
  `LBTerm` may cover a subset. Decide the common fragment in `Iface.v`/
  `Translate.v`.
- **`WcbvFlags`.** `EWcbvEval.eval` is parameterized by `WcbvFlags` (and block-vs
  -applied constructor mode). Pin the flags to match the Lean semantics
  (repo memory notes block-mode is pinned on the Lean side).
- **How to import the Lean semantics.** The plan is `lean4export` the relevant
  Lean modules and `Lean Import` them. Recursors are elaborated by
  rocq-lean-import from the inductive; the imported `WcbvEval` will land as an
  inductive relation to be related to `EWcbvEval.eval` in `Forward`/`Backward`.
- **Untagged emitter provenance.** The emitter is a verbatim port of untagged
  commit `c9f8373`; if lean4export upstream ever ships a v1.x-compatible tag or
  rocq-lean-import gains v2.0.0 support, revisit §3.

---

## 5. Import feasibility (WS-R): the semantics cone does NOT import; kernel-transport blocked

The `lean4export` side works perfectly: `export/semantics.out` (41838 lines, 76 IND,
565 DEF, 1 AX = `propext`, 0 dummies) is the faithful kernel emission of the Lean
semantics. But **`rocq-lean-import 0.0.1` cannot import it**, in two layers:

1. **Predeclared-core staleness (fixed by `lean-import-patch.diff`).** The plugin
   hardcodes predeclared core types (`src/lean.ml`: `Eq|Nat|Nat_le|Or|And|Fin|UInt32|
   Char`) modeling the *pre-BitVec* `UInt32 := {val0 : Fin UInt32_size}`. Lean v4.29's
   `UInt32` is `BitVec 32`-backed, so `UInt32.toBitVec` (`fun self => self.val0`) fails
   to typecheck (`Fin UInt32_size` vs `BitVec (2^32)`); since v4.29 `String` is
   UTF-8/`ByteArray`-backed, `String` — hence every `Kername`/`BinderName`/`LBTerm` —
   is skipped in cascade. `rocq/lean-import-patch.diff` (~6 functional lines) drops
   `UInt32`/`Char` from the predeclared set so they import structurally from the real
   v4.29 definitions; this FIXES `UInt32.toBitVec` (Char cone: 0 skips; full import:
   146→84 skips; `All2T` imports).

   To build + load the patched plugin **without touching the shared switch**:
   ```sh
   D=$(mktemp -d); cp -r ~/.opam/peregrine/.opam-switch/sources/rocq-lean-import.0.0.1 "$D/p"
   ( cd "$D/p" && patch -p1 < <abs>/rocq/lean-import-patch.diff && eval $(opam env --switch=peregrine) && make )
   mkdir -p "$D/findlib/coq-lean-import"
   cp ~/.opam/peregrine/lib/coq-lean-import/META "$D/findlib/coq-lean-import/"
   cp "$D/p/src/lean_import.cmxs" "$D/findlib/coq-lean-import/"
   coqc -I "$D/findlib" ...                # -I <PARENT of the package dir>
   ```
   NB: Rocq's ML-module loader ignores `OCAMLPATH`/`OCAMLFIND_CONF`; only `-I
   <parent-of-package-dir>` prepends to its findlib search path. (`opam reinstall`/
   overwriting the installed `.cmxs` also works but modifies the shared switch.)

2. **Deeper plugin bugs (NOT fixed; balloon + unsoundness risk).** Even patched,
   **`LBTerm` still does not import**: (a) an **Anomaly** `assert false` at
   `src/lean.ml:75` (`reorder_outside`, the eliminator-premise reordering) on LBTerm's
   **nested** recursion (`construct/case/fix` through `List LBTerm`) — the plan's
   anticipated Top Risk #1; the working `Nat.brecOn` case is non-nested; (b) a
   **Stack overflow** on the v4.29 `UInt32.isValidChar` match; plus `String.mk`/
   `Nat.repr`/`panic!` machinery gaps. These need a substantial importer enhancement
   (nested-inductive recursors + v4.29 String/panic), out of the minimal-patch scope.

**Consequence.** The intended kernel-transport of the Lean semantics is blocked at
LBTerm. The equivalence uses the committed **fallback** (`Translate.v` restated
`LBTerm`/`T` + `SubstAgree.v` `shift`/`subst` agreement, admitted-free; roadmap in
`Wf`/`EnvAgree`/`ValuesAgree`/`Backward`/`Forward`/`Equivalence`), validated against
`export/semantics.out` — a documented residual gap (transcription, not transport).
