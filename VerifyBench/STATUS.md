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

## Erase runs (re-measured 2026-08-26 at HEAD 506d9c8; Lean v4.33.0-rc2, lean4lean 1a1ebe8)

| Program | `.ast` written | Erasure clean |
|---|---|---|
| Arith | yes (14 KB) | yes |
| Sieve | yes (28 KB) | yes |
| Quicksort | yes (65 KB) | **no — panics, silently wrong output (see below)** |
| BinaryTrees | yes (29 KB) | yes |
| Fannkuch | yes (39 KB) | yes |

`csimp := false` broke nothing: all five erase exactly as far as they do with the shipping
default. The one failure below reproduces under both settings.

These are a 2026-08-26 **record**, not a claim about the current pin: the `trproj` re-pins
moved lean4lean to `7a5e96d`, and the relevance oracle runs lean4lean's typechecker
(`Erasure.lean:178`), so the five runs would have to be repeated to be re-asserted.

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

*The `indName` swap is necessary and not sufficient*, measured 2026-08-26:
`getCasesInfo? quicksort_fuel._sparseCasesOn_1` reports `indName = List`, `arity = 5`,
`discrPos = 2` and **two** alternatives — `.ctor List.nil (numFields := 0)` and
`.default (numHyps := 1)`. With `indName` in place the panic goes away and the loop then
zips those two alternatives against `List`'s two argmasks, so the catch-all — which binds
the *whole discriminant*, one hypothesis — is emitted as the `List.cons` alternative, which
λ□ hands two fields. That is findings D4/D5 (`notes/EQUIV_FINDINGS.md`) firing on real code:
a wrong program instead of a panic. A complete fix has to either reject sparse `casesOn`
and unfold it, or expand the `.default` alternative per constructor and rebuild the
discriminant from the fields.

*Scope.* Toolchain drift, not `csimp`: sparse `casesOn` does not exist on the v4.22.0
toolchain the sibling benchmarks pin, and the panic reproduces with `csimp := true`. Only
`Quicksort` among the five hits it, through `quicksort_fuel`; `partition`, `divmod`,
`modulo`, `makeListAux`, `makeList` and `isSorted` all erase cleanly. Any silent `tBox`
substitution of this kind is invisible downstream: `peregrine` sees a well-formed program.

## Gap to the benchmarks, per program

Resolved for all five by the landed work and by this directory — except the last row, which
was not on this list at all until Γ-U named it:

| Was a disqualifier | Status |
|---|---|
| `csimp := true` in the `#erase` lines (D1) | **resolved here** — these copies erase with `csimp := false` |
| pattern matching → ι | resolved (`erases_correct_dataι`, `Supported.casesApp`) |
| recursion → fix-unfolding | resolved — *in the simulations* at W0–W3.1 (`RecEnvConsistent` replaced `NoFixEnv`), and *in the cold-start capstones* at Γ-W4, where the scope restriction `hnorec : Γ.recBodies = ⊥` was deleted. Γ-W5 removed the last arity restriction with it (`DeltaHyps.decl_run`'s `ci.all = [m]`, i.e. self-recursion only); it moves none of these five, see the measurement below |
| typeclass projections → `tProj` | resolved (P0–P9: `Erases.proj`, `Supported.proj`, the fourth trust bundle `ProjBridgeHyps`; the ι capstone's `hnoprojs : Γ.projs = ⊥` deleted) |
| raw `Nat` literals | resolved (L1–L4: `Erases.lit` unfolds `.lit (.natVal n)` to the peano tower) |
| machine `Nat` | pre-dodged — the originals already pass `nat := .peano` |
| first-order result | holds — all five return `Nat` |
| universe-polymorphic dependencies | **not resolved** — `hUs : Us = []`, and it is *doubly* pinned. The one scope restriction that still excludes all five outright; costed at Γ-U, plan of record Γ-U1–Γ-U4. See the reading below |

What remains, measured from the erased output rather than asserted:

| Program | Class projections (`tProj`) — in the relation since round P0–P9 | Recursive deps (`tFix`) — in the capstones since Γ-W4 | Peano tower (`Nat.succ` nodes) | Axioms | Program-specific residue |
|---|---|---|---|---|---|
| Arith | 10: `OfNat.ofNat`, `HAdd.hAdd`/`Add.add`, `HSub.hSub`/`Sub.sub`, `HMul.hMul`/`Mul.mul`, `HPow.hPow`/`Pow.pow`/`NatPow.pow` | 4 | 19 | — | no `match` in the source, but `Nat.add/sub/mul/pow` bring four fixpoints and the whole `HAdd`-class tower |
| Sieve | 8: `OfNat.ofNat`, `HAdd`/`Add`, `HSub`/`Sub`, `HAppend`/`Append`, `BEq.beq` | 10 | 9 | — | higher-order: `List.filter` applied to a source lambda; `Decidable`/`Bool` dispatch through `instBEqOfDecidableEq` |
| Quicksort | 9: `OfNat.ofNat`, `HAdd`/`Add`, `HSub`/`Sub`, `HMul`/`Mul`, `HAppend`/`Append` | 11 | 638 | — | **the sparse-`casesOn` panic above**; `Prod` destructuring in `partition`; the numerals 42/49/12/214 expand to 638 unary constructor nodes |
| BinaryTrees | 9: `OfNat.ofNat`, `HAdd`/`Add`, `HSub`/`Sub`, `HPow`/`Pow`/`NatPow`, `Max.max` | 10 | 30 | — | custom `Tree` inductive (fine); `max` routes through `maxOfLe` → `instLENat` → `Nat.decLe`; `Prod` triple in `binaryTreesMain` |
| Fannkuch | 6: `OfNat.ofNat`, `HAdd`/`Add`, `HAppend`/`Append`, `Max.max` | 15 | 15 | **`Eq.rec`** | three `partial def`s (the `_unsafe_rec` stripping works — the erased env has plain `countFlipsAux`/`nextPerm`/`fannkuchLoop`); `Option`, `Prod`, polymorphic `reversePrefixAux`/`setAt`; `Eq.ndrec`/`Eq.ndrec_symm` force an axiomatised `Eq.rec` |

Reading the table:

- **The projection layer was the concrete, universal blocker; it is now inside the
  relation.** Every `tProj` node in all five programs is a typeclass field projection —
  six to ten per program, and no config removes them: a source numeral elaborates to
  `@OfNat.ofNat Nat (lit n) (instOfNatNat …)`, and every `+`, `-`, `*`, `^`, `++`, `max`
  goes through its class projection. When this table was first measured `Erases` had no
  projection rule, because lean4lean's `TrProj` was a `sorry`-valued definition. The
  `trproj` pin fixed the definition and the **projection round P0–P9** built the layer out:
  `Erases.proj` (P1), `WcbvEval.proj` (P3), the source rule and its simulation (P5/P6/P7),
  the bridge arm and fourth trust bundle (P8), and the cold-start registry composition
  (P9), which deleted the ι capstone's `Γ.projs = ⊥`. What the layer costs now is two
  named `Prop` hypotheses, both upstream's and both on the commission: `ProjDefeqSpec`
  (`TrEnv.proj_defeq`, a real statement with a deferred proof) and `ProjCtorAgree`.
- **`@[extern]` arithmetic is *not* a blocker at these programs' own config.** With
  `extern := .preferLogical` the eraser reports `Nat.add is tagged @[extern] but has a
  value, using value` and erases the logical body; four of the five erased environments
  contain zero axioms. §H's reading — that the arithmetic leaves the fragment through
  `addAxiom` — holds only under `extern := .preferAxiom`. The single axiom anywhere in the
  five is `Eq.rec`, in Fannkuch.
- **Recursive dependencies at cold start no longer gate them.** Every one of the five
  drags in fixpoints — even Arith, with no source-level recursion, brings four through
  `Nat` arithmetic — and until Γ-W4 the cold-start capstones pinned `Γ.recBodies = ⊥`,
  which excluded all five outright. The Γ-XL wave took that down: the bridge walks
  `visitMutual`'s recursive exit (Γ-W3.6b) and the capstones take the coverage agreement
  `hcov` and the block-local bundle `Hβ` instead. The restriction that remains is *inside*
  a block rather than about the program: a walked block's bodies call only its own
  siblings, registered constructors and registered `casesOn`s.
- **Mutual blocks are in scope since Γ-W5, and it moves none of these five.** Until then
  `DeltaHyps.decl_run` pinned `ci.all = [m]` — self-recursion only, anywhere in a
  dependency cone — a restriction that never appeared in this table because it lived
  inside a five-conjunct field rather than in a named ledger row. Measured on the erased
  output rather than asserted: **every `tFix` block in all five programs holds exactly one
  definition** (Arith 4 blocks, Sieve 10, BinaryTrees 10, Quicksort 11, Fannkuch 15; the
  arity histogram is `{1: n}` in each case). So Γ-W5 is the Γ-U pattern in reverse — a
  restriction removed rather than costed, and zero programs moved either way. It is worth
  having anyway, and for a reason this table cannot show: the restriction was on the whole
  *dependency cone*, so a single mutual pair anywhere below a program would have excluded
  it outright, and nothing was checking.
- **Universes are what blocks all five now — and it is the `tProj` column read again.**
  Every class method in that column is universe-polymorphic, measured at this toolchain:
  `OfNat.ofNat.{u}`, `Add.add.{u}`, `Max.max.{u}`, `BEq.beq.{u}`, `HAdd.hAdd.{u,v,w}`,
  `HAppend.hAppend.{u,v,w}`, and beside them `List.filter.{u}`, `List.append.{u_1}`,
  `Prod.mk.{u,v}`; of the constants these programs lean on, only `Nat.add` and
  `instOfNatNat` come back with `levelParams = []`. The capstones take `hUs : Us = []`
  and `DeltaHyps.decl_run` demands `ci.levelParams = Us` of every *dependency*, so a
  polymorphic callee makes the bundle uninhabited — `Erases.proj` admits
  `OfNat.ofNat`'s **body** while `decl_run` keeps its **declaration** out. Γ-U costed the
  relaxation and found the restriction pinned in two independent places: `SEnvConsistent`
  quantifies the call site's levels and its conclusion never mentions them, so at a
  polymorphic constant it is a strictly stronger, *false* demand — it collapses the
  constant's instantiations (`SEnvConsistent.levels_collapse`) — and the model's δ step is
  universe-blind (`SEvalDataι.delta_level_blind`). Relaxing only the bundle would move the
  vacuity into an unnamed capstone premise rather than remove it. Plan of record
  Γ-U1–Γ-U4 (`LeanToLambdaBox/DeltaHyps.lean`), of which Γ-U3 (`Erases.instL`) is the risk
  and Γ-U4 the content.
- **Nothing exotic is in the way.** No program touches `String`, `Int`, `Array`, `Float`,
  `UInt*`, well-founded recursion, `brecOn` residue or `sorry`. The *data* inductives in the
  erased environments are `Nat`, `List`, `Prod`, `Option`, `Bool`, `Decidable`, `PUnit`,
  plus BinaryTrees' own `Tree` — all first-order. (`Eq` is **not** among them: Fannkuch
  reaches it only through the constants `Eq.ndrec`/`Eq.ndrec_symm` and the `Eq.rec` axiom.)
  The rest of each environment's inductives are the **class structures themselves** —
  `OfNat`, `Add`/`HAdd`, `Sub`/`HSub`, `Mul`/`HMul`, `Pow`/`HPow`/`NatPow`,
  `Append`/`HAppend`, `Max`, `LE`, `BEq` — which is the same fact as the `tProj` column,
  seen from the environment side: the classes are registered, and every class method erases
  to a projection out of one.

Priority order, re-read after the Γ-XL wave, the projection round and the Γ-U analysis
(2026-08-27). The two items that headed the 2026-08-26 list are **done**: the
class-projection route landed as P0–P9, and the `Γ`-inside-the-motives generalisation as
Γ-W0–Γ-W4. What is left, in order:
(1) **the universe restriction** — with recursion and projections both inside, `hUs : Us =
[]` is the one *scope* restriction that still excludes all five outright, and Γ-U measured
rather than guessed what lifting it costs: two pinned places, four slices, `Erases.instL`
the risk;
(2) `ProjDefeqSpec` — upstream's `TrEnv.proj_defeq`, the deferred proof the projection
layer rests on (`../lean4lean/trproj-commission.md`), with `ProjCtorAgree` beside it — the
*trust* item, where (1) is the scope one. Note it is a **statement** correction before it
is a proof: as written the lemma's two `ctorName`s are unrelated, so the standing
`PROJ-TODO` should not be attempted against it (commission §4.5);
(3) the `visitCases` sparse-`casesOn` bug, which blocks `Quicksort` outright and is cheap
only for the panic, not for the wrong output; (4) the per-program residue in the table —
Fannkuch's `Eq.rec` axiom, and the fragment-scope bundles each program's dependency cone
has to satisfy (`DeltaHyps`/`BlockHyps`), which is where "measured, not argued" has to be
re-run program by program rather than claimed from this table.

## Refreshing

If the originals change, re-copy them and re-apply the one-line `#erase` edit. Keep the
copies byte-identical elsewhere so the `diff` above stays a single line.
