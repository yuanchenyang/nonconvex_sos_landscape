#!/usr/bin/env bash
set -euo pipefail

# Generic verification harness for a Lean theorem/proof pair. Use the
# project-specific wrapper scripts for routine workflows when available.

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT_DIR"

usage() {
  cat <<'EOF'
Usage:
  ./scripts/verify_formalization.sh \
    --theorem <Namespace.theorem_name> \
    --proof-import <Import.Module> \
    --proof-file <path/to/Proof.lean> \
    [--build-target <LakeTarget>]... \
    [--declaration-name <local_theorem_name>] \

Checks that:
  1. the selected Lake targets build;
  2. the proof file typechecks;
  3. the theorem is available from the proof import;
  4. the proof file contains the theorem declaration; and
  5. '#print axioms' matches the expected axiom list exactly.

If '--build-target' is omitted, the script builds '--proof-import'.
EOF
}

THEOREM_NAME=""
PROOF_IMPORT=""
PROOF_FILE=""
DECLARATION_NAME=""
EXPECTED_AXIOMS='[propext, Classical.choice, Quot.sound]'
BUILD_TARGETS=()

while (($# > 0)); do
  case "$1" in
    --theorem)
      THEOREM_NAME="$2"
      shift 2
      ;;
    --proof-import)
      PROOF_IMPORT="$2"
      shift 2
      ;;
    --proof-file)
      PROOF_FILE="$2"
      shift 2
      ;;
    --declaration-name)
      DECLARATION_NAME="$2"
      shift 2
      ;;
    --build-target)
      BUILD_TARGETS+=("$2")
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "verification failed: unknown argument '$1'" >&2
      usage >&2
      exit 1
      ;;
  esac
done

if [ -z "$THEOREM_NAME" ] || [ -z "$PROOF_IMPORT" ] || [ -z "$PROOF_FILE" ]; then
  echo "verification failed: --theorem, --proof-import, and --proof-file are required" >&2
  usage >&2
  exit 1
fi

if [ ! -f "$PROOF_FILE" ]; then
  echo "verification failed: proof file '$PROOF_FILE' does not exist" >&2
  exit 1
fi

if [ "${#BUILD_TARGETS[@]}" -eq 0 ]; then
  BUILD_TARGETS=("$PROOF_IMPORT")
fi

if [ -z "$DECLARATION_NAME" ]; then
  DECLARATION_NAME="${THEOREM_NAME##*.}"
fi

DECL_CHECK="$(mktemp /tmp/verify_decl.XXXXXX.lean)"
AXIOM_CHECK="$(mktemp /tmp/verify_axioms.XXXXXX.lean)"
AXIOM_OUTPUT="$(mktemp /tmp/verify_axioms_output.XXXXXX.txt)"
cleanup() {
  rm -f "$DECL_CHECK" "$AXIOM_CHECK" "$AXIOM_OUTPUT"
}
trap cleanup EXIT

normalize_axioms() {
  printf '%s' "$1" | tr '\n' ' ' | sed -E 's/[[:space:]]+/ /g; s/\[ /[/g; s/ \]/]/g; s/^ //; s/ $//'
}

extract_axioms() {
  awk -v theorem="$THEOREM_NAME" '
    index($0, "'"'"'" theorem "'"'"' depends on axioms:") {
      sub("^'"'"'" theorem "'"'"' depends on axioms: ", "", $0)
      out = $0
      while (out !~ /\]/ && getline > 0) {
        out = out "\n" $0
      }
      print out
      exit
    }
  ' "$AXIOM_OUTPUT"
}

echo "[1/5] Building selected Lean targets"
lake build "${BUILD_TARGETS[@]}"

echo "[2/5] Typechecking editable proof file"
lake env lean "$PROOF_FILE"

echo "[3/5] Checking theorem declaration is available from proof import"
cat > "$DECL_CHECK" <<EOF
import $PROOF_IMPORT
#check $THEOREM_NAME
EOF
lake env lean "$DECL_CHECK"

echo "[4/5] Checking theorem is defined in $PROOF_FILE"
if ! grep -n -E "^[[:space:]]*theorem[[:space:]]+$DECLARATION_NAME\\b" "$PROOF_FILE"; then
  echo "verification failed: theorem $DECLARATION_NAME not found in $PROOF_FILE" >&2
  exit 1
fi

echo "[5/5] Checking theorem depends on exactly the allowed axioms"
cat > "$AXIOM_CHECK" <<EOF
import $PROOF_IMPORT
#print axioms $THEOREM_NAME
EOF
lake env lean "$AXIOM_CHECK" >"$AXIOM_OUTPUT" 2>&1
cat "$AXIOM_OUTPUT"
ACTUAL_AXIOMS_RAW="$(extract_axioms)"
if [ -z "$ACTUAL_AXIOMS_RAW" ]; then
  echo "verification failed: could not extract theorem axioms from #print axioms output" >&2
  exit 1
fi
ACTUAL_AXIOMS="$(normalize_axioms "$ACTUAL_AXIOMS_RAW")"
NORMALIZED_EXPECTED="$(normalize_axioms "$EXPECTED_AXIOMS")"
if [ "$ACTUAL_AXIOMS" != "$NORMALIZED_EXPECTED" ]; then
  echo "verification failed: expected axioms $NORMALIZED_EXPECTED but found $ACTUAL_AXIOMS" >&2
  exit 1
fi

echo
echo "verification succeeded: $THEOREM_NAME"
