#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"

exec "$ROOT_DIR/scripts/verify_formalization.sh" \
  --build-target QuaternaryQuartic \
  --proof-import QuaternaryQuartic.QuaternaryQuarticProof \
  --proof-file QuaternaryQuartic/QuaternaryQuarticProof.lean \
  --theorem QuaternaryQuartic.quaternaryQuartic_rankSeven_no_spurious_socp
