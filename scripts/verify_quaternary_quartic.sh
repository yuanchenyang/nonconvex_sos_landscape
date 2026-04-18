#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

exec "$SCRIPT_DIR/verify_formalization.sh" \
  --build-target QuaternaryQuartic \
  --build-target QuaternaryQuarticProof \
  --proof-import QuaternaryQuarticProof \
  --proof-file QuaternaryQuarticProof.lean \
  --theorem QuaternaryQuartic.quaternaryQuartic_rankSeven_no_spurious_socp
