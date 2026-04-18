#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

exec "$SCRIPT_DIR/verify_formalization.sh" \
  --build-target TernaryQuartic \
  --build-target TernaryQuarticProof \
  --proof-import TernaryQuarticProof \
  --proof-file TernaryQuarticProof.lean \
  --theorem TernaryQuartic.ternaryQuartic_rankFour_no_spurious_socp
