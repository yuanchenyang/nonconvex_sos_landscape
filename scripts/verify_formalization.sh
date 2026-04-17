#!/usr/bin/env bash
set -euo pipefail

# This script is part of the root verification harness for the Lean project.
# Treat it as stable infrastructure and modify it only when explicitly
# requested.

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT_DIR"

THEOREM_NAME="TernaryQuartic.ternaryQuartic_rankFour_no_spurious_socp"

echo "[1/5] Building root Lean project"
lake build TernaryQuartic TernaryQuarticProof

echo "[2/5] Typechecking editable proof file"
lake env lean TernaryQuarticProof.lean

echo "[3/5] Checking theorem declaration is available from proof import"
DECL_CHECK="$(mktemp /tmp/tq_check_decl.XXXXXX.lean)"
cat > "$DECL_CHECK" <<'EOF'
import TernaryQuarticProof
#check TernaryQuartic.ternaryQuartic_rankFour_no_spurious_socp
EOF
lake env lean "$DECL_CHECK"

echo "[4/5] Checking theorem is defined in TernaryQuarticProof.lean"
rg -n '^theorem ternaryQuartic_rankFour_no_spurious_socp\b' TernaryQuarticProof.lean

echo "[5/5] Checking theorem depends on exactly the allowed axioms"
AXIOM_CHECK="$(mktemp /tmp/tq_check_axioms.XXXXXX.lean)"
cat > "$AXIOM_CHECK" <<'EOF'
import TernaryQuarticProof
#print axioms TernaryQuartic.ternaryQuartic_rankFour_no_spurious_socp
EOF
AXIOM_OUTPUT="$(mktemp /tmp/tq_axioms_output.XXXXXX.txt)"
lake env lean "$AXIOM_CHECK" >"$AXIOM_OUTPUT" 2>&1
cat "$AXIOM_OUTPUT"
EXPECTED_AXIOMS='[propext, Classical.choice, Quot.sound]'
AXIOM_LINE="$(grep -F "'$THEOREM_NAME' depends on axioms:" "$AXIOM_OUTPUT" || true)"
ACTUAL_AXIOMS="$(printf '%s\n' "$AXIOM_LINE" | sed -E "s/^'.*' depends on axioms: //")"
if [ -z "$AXIOM_LINE" ]; then
  echo "verification failed: could not extract theorem axioms from #print axioms output" >&2
  exit 1
fi
if [ "$ACTUAL_AXIOMS" != "$EXPECTED_AXIOMS" ]; then
  echo "verification failed: expected axioms $EXPECTED_AXIOMS but found $ACTUAL_AXIOMS" >&2
  exit 1
fi

echo
echo "verification succeeded: $THEOREM_NAME"
