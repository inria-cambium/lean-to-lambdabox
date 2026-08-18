# VerifyBench — the five `frontend_bench` programs, erased with `csimp := false`

Every correctness theorem in this repo requires `csimp := false` (finding D1: `csimp`
replacement is not kernel-semantics-preserving, so it can never sit inside a correctness
statement — see `LeanToLambdaBox/PrepareHyps.lean`). The benchmark programs erase with the
shipping default `csimp := true`. This directory removes that gap.

The five programs here are **duplicates**. The originals live in the sibling `benchmarks`
repo, are consumed by the cross-frontend suite, and stay byte-frozen:

    ../benchmarks/frontend_bench/lean/{Arith,Sieve,Quicksort,BinaryTrees,Fannkuch}.lean

Each copy is byte-identical to its original except for its single `#erase` line, which
gains `csimp := false` and writes into `VerifyBench/ast/`. Verify with:

    diff <(sed '$d' VerifyBench/Arith.lean) \
         <(sed '$d' ../benchmarks/frontend_bench/lean/Arith.lean)

`nat := .peano` and `extern := .preferLogical` were already in the originals; the
duplicates keep them. The programs are ours to edit — the originals are not.

## Building

    lake build VerifyBench          # from the repo root

`VerifyBench` is a separate `lean_lib` in the root `lakefile.toml`, deliberately outside
`defaultTargets`: plain `lake build` (and therefore CI) is unaffected, and elaborating
these roots writes `.ast` files, which CI should not do. The five modules are separate
roots and are never imported together — `Sieve` and `Quicksort` both declare `divmod` and
`modulo` at the root namespace, so an umbrella module would clash.

Outputs land in `VerifyBench/ast/` (gitignored, mirroring how the benchmarks treat `.ast`
artifacts). The directory itself is tracked because `#erase … to` does not create it.

## Erase runs (HEAD 9a10c12, Lean v4.33.0-rc2, lean4lean 1a1ebe8)

| Program | `.ast` written | Erasure clean |
|---|---|---|
| Arith | yes (14 KB) | yes |
| Sieve | yes (28 KB) | yes |
| Quicksort | yes (65 KB) | **no — panics, silently wrong output (see below)** |
| BinaryTrees | yes (29 KB) | yes |
| Fannkuch | yes (39 KB) | yes |

`csimp := false` broke nothing: all five erase exactly as far as they do with the shipping
default. The one failure below reproduces under both settings.

## FINDING — `visitCases` panics on Lean's sparse `casesOn`, and emits a wrong program

Erasing `Quicksort` prints

    PANIC at Erasure.visitCases LeanToLambdaBox.Erasure:817:55: unreachable code has been reached

and still exits 0 and still writes `Quicksort.ast`. **The written program is wrong.**

*Cause.* `visitCases` recovers the inductive type of a `casesOn`-like head with

    let typeName := casesInfo.declName.getPrefix           -- Erasure.lean:770

Since Lean v4.26 (absent in v4.24), `getCasesInfo?` also recognises **sparse `casesOn`**
declarations, which
Lean generates for a match that covers some constructors plus a catch-all. They are named
after the *enclosing function*, not after the inductive:

    quicksort_fuel._sparseCasesOn_1    indName = List    declName.getPrefix = quicksort_fuel

`getConstInfo quicksort_fuel` then returns a `defnInfo`, the `| unreachable!` fires, and
because `unreachable!` is `panic!` it returns `default : LBTerm` — which is `.box`, the
first constructor. The `match l with | [] | [x] | pivot :: rest` in `quicksort_fuel`
therefore erases to

    (tCase ((inductive List) 1) (tRel 5)
      ( (() (tApp (tRel 2) (tConst Unit.unit)))          -- nil alternative: fine
        ((head tail) tBox) ))                            -- cons alternative: box

so `quicksortBench` returns `□` on every non-empty list. `CasesInfo` already carries the
right answer in its `indName` field; `casesInfo.declName.getPrefix` is the only user of the
wrong one. Raised, not fixed — this is shipping code.

*Scope.* Toolchain drift, not `csimp`: sparse `casesOn` does not exist on the v4.22.0
toolchain the sibling benchmarks pin, and the panic reproduces with `csimp := true`. Only
`Quicksort` among the five hits it, through `quicksort_fuel`; `partition`, `divmod`,
`modulo`, `makeListAux`, `makeList` and `isSorted` all erase cleanly. Any silent `tBox`
substitution of this kind is invisible downstream: `peregrine` sees a well-formed program.

## Gap to the benchmarks, per program

Resolved for all five by the landed work and by this directory:

| Was a disqualifier | Status |
|---|---|
| `csimp := true` in the `#erase` lines (D1) | **resolved here** — these copies erase with `csimp := false` |
| pattern matching → ι | resolved (`erases_correct_dataι`, `Supported.casesApp`) |
| recursion → fix-unfolding | resolved *in the simulations* (W0–W3.1; `RecEnvConsistent` replaced `NoFixEnv`) |
| raw `Nat` literals | resolved (L1–L4: `Erases.lit` unfolds `.lit (.natVal n)` to the peano tower) |
| machine `Nat` | pre-dodged — the originals already pass `nat := .peano` |
| first-order result | holds — all five return `Nat` |

What remains, measured from the erased output rather than asserted:

| Program | Class projections (`tProj`) — hard blocker | Recursive deps (`tFix`) | Peano tower (`Nat.succ` nodes) | Axioms | Program-specific residue |
|---|---|---|---|---|---|
| Arith | 10: `OfNat.ofNat`, `HAdd.hAdd`/`Add.add`, `HSub.hSub`/`Sub.sub`, `HMul.hMul`/`Mul.mul`, `HPow.hPow`/`Pow.pow`/`NatPow.pow` | 4 | 19 | — | no `match` in the source, but `Nat.add/sub/mul/pow` bring four fixpoints and the whole `HAdd`-class tower |
| Sieve | 8: `OfNat.ofNat`, `HAdd`/`Add`, `HSub`/`Sub`, `HAppend`/`Append`, `BEq.beq` | 10 | 9 | — | higher-order: `List.filter` applied to a source lambda; `Decidable`/`Bool` dispatch through `instBEqOfDecidableEq` |
| Quicksort | 9: `OfNat.ofNat`, `HAdd`/`Add`, `HSub`/`Sub`, `HMul`/`Mul`, `HAppend`/`Append` | 11 | 638 | — | **the sparse-`casesOn` panic above**; `Prod` destructuring in `partition`; the numerals 42/49/12/214 expand to 638 unary constructor nodes |
| BinaryTrees | 9: `OfNat.ofNat`, `HAdd`/`Add`, `HSub`/`Sub`, `HPow`/`Pow`/`NatPow`, `Max.max` | 10 | 30 | — | custom `Tree` inductive (fine); `max` routes through `maxOfLe` → `instLENat` → `Nat.decLe`; `Prod` triple in `binaryTreesMain` |
| Fannkuch | 6: `OfNat.ofNat`, `HAdd`/`Add`, `HAppend`/`Append`, `Max.max` | 15 | 15 | **`Eq.rec`** | three `partial def`s (the `_unsafe_rec` stripping works — the erased env has plain `countFlipsAux`/`nextPerm`/`fannkuchLoop`); `Option`, `Prod`, polymorphic `reversePrefixAux`/`setAt`; `Eq.ndrec`/`Eq.ndrec_symm` force an axiomatised `Eq.rec` |

Reading the table:

- **The projection layer is the concrete, universal blocker.** Every `tProj` node in all
  five programs is a typeclass field projection, and `Erases` is projection-free by design
  (lean4lean's `TrProj` is a `sorry`). Six to ten of them per program, and no config
  removes them: a source numeral elaborates to `@OfNat.ofNat Nat (lit n) (instOfNatNat …)`,
  and every `+`, `-`, `*`, `^`, `++`, `max` goes through its class projection.
- **`@[extern]` arithmetic is *not* a blocker at these programs' own config.** With
  `extern := .preferLogical` the eraser reports `Nat.add is tagged @[extern] but has a
  value, using value` and erases the logical body; four of the five erased environments
  contain zero axioms. §H's reading — that the arithmetic leaves the fragment through
  `addAxiom` — holds only under `extern := .preferAxiom`. The single axiom anywhere in the
  five is `Eq.rec`, in Fannkuch.
- **Recursive dependencies at cold start (D8) still gate all five**, including Arith: even
  a program with no source-level recursion drags in four fixpoints through `Nat`
  arithmetic. §H's cold-start capstones still pin `Γ.recBodies = ⊥`; closing that is the
  `Γ`-inside-the-motives slice (§W3.2/D8).
- **Nothing exotic is in the way.** No program touches `String`, `Int`, `Array`, `Float`,
  `UInt*`, well-founded recursion, `brecOn` residue or `sorry`. The erased environments
  hold `Nat`, `List`, `Prod`, `Option`, `Bool`, `Decidable`, `PUnit` and Fannkuch's `Eq`,
  plus BinaryTrees' own `Tree` — all first-order data.

Priority order, unchanged from §H and confirmed by the measurements: (1) §W3.2/D8, which
gates all five; (2) the `OfNat`/class-projection route; (3) the `visitCases` `indName` bug,
which is cheap and blocks `Quicksort` outright.

## Refreshing

If the originals change, re-copy them and re-apply the one-line `#erase` edit. Keep the
copies byte-identical elsewhere so the `diff` above stays a single line.
