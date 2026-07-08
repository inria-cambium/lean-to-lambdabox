#!/usr/bin/env bash
# Export the Lean λ□ semantics cone to the classic-v1.x text format that
# rocq-lean-import 0.0.1 parses, for the WS-R equivalence development.
#
# Pipeline: `lake build` (the repo library, so the oleans exist and are current)
# -> lean4export (the vendored classic-v1.x emitter, built separately in
# rocq/lean4export) -> rocq/export/semantics.out.
#
# Prerequisites (see rocq/README.md):
#   * elan/lake on PATH, repo on toolchain leanprover/lean4:v4.29.0.
#   * rocq/lean4export/.lake/build/bin/lean4export built
#     (cd rocq/lean4export && lake build).
#
# The roots exported are listed in rocq/scripts/decls.txt (LBTerm + the whole
# Semantics/ layer + WcbvEvalT/All2T/wcbvEvalT_iff); lean4export adds their full
# dependency closure. Run from the repo root:  bash rocq/scripts/export.sh
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$REPO_ROOT"

BIN="$REPO_ROOT/rocq/lean4export/.lake/build/bin/lean4export"
DECLS="$REPO_ROOT/rocq/scripts/decls.txt"
OUT="$REPO_ROOT/rocq/export/semantics.out"

if [ ! -x "$BIN" ]; then
  echo "lean4export binary not found at $BIN" >&2
  echo "Build it: (cd rocq/lean4export && lake build)" >&2
  exit 1
fi

# Collect the (comment-stripped) roots.
mapfile -t ROOTS < <(grep -vE '^\s*(#|$)' "$DECLS")

echo "[export.sh] lake build (ensuring oleans are current)..."
lake build >/dev/null

echo "[export.sh] exporting ${#ROOTS[@]} roots via lean4export -> $OUT"
lake env "$BIN" LeanToLambdaBox -- "${ROOTS[@]}" > "$OUT"

echo "[export.sh] done: $(wc -l < "$OUT") lines, $(du -h "$OUT" | cut -f1)"
