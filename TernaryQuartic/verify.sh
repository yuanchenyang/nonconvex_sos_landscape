#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"

exec "$ROOT_DIR/scripts/verify_formalization.sh" \
  --build-target TernaryQuartic \
  --proof-import TernaryQuartic.TernaryQuarticProof \
  --proof-file TernaryQuartic/TernaryQuarticProof.lean \
  --theorem TernaryQuartic.ternaryQuartic_rankFour_no_spurious_socp
