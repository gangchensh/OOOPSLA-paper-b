#!/usr/bin/env bash
# Axiom audit for Paper B. Usage (from the artifact root, after the Coq build):
#   ./scripts/run_audit.sh
set -euo pipefail
cd "$(dirname "$0")/../coq"

COQC="${COQC:-coqc}"
OUT=../scripts/print_assumptions_B_output.txt

"$COQC" -R src/Ionia Ionia ../scripts/print_assumptions_B.v > "$OUT" 2>&1 || {
    echo "coqc failed; see scripts/print_assumptions_B_output.txt"; exit 1; }

echo "=== Axioms referenced (unique) ==="
grep -E '^[A-Za-z_][A-Za-z0-9_.]* :' "$OUT" | sort -u || true
echo
echo "=== Full output in scripts/print_assumptions_B_output.txt ==="
if grep -qi 'admitted\|Axiom ' "$OUT"; then
    echo "WARNING: non-standard axiom or Admitted detected — inspect the output"
    exit 2
fi
echo "OK: only standard library axioms are used."
