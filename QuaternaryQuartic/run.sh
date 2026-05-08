#!/bin/bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT_DIR"

export CODEX_KEEPALIVE=1
export CODEX_KEEPALIVE_PROMPT="Formalize QuaternaryQuarticRankSevenNoSpuriousSOCP, using the proof blueprint in writeup/quaternary_quartic/blueprint.tex. During each round, figure out the largest remaining gap and work to meaningfully reduce that gap. Add only proof-serving lemmas, keep the final theorem declaration in QuaternaryQuartic/QuaternaryQuarticProof.lean and added Lean code in QuaternaryQuartic/QuaternaryQuarticProof/, do not weaken or restate the target, do not touch QuaternaryQuartic/QuaternaryQuartic.lean. Treat the verification harnesses as stable, do not build or depend on low_rank_univariate_sos/, log all experiments and strategy changes in writeup/quaternary_quartic/exploration_log.tex, record numerical claims (if needed) in julia/quaternary_quartic_explorations/ and reference them in the .tex files, verify regularly with ./QuaternaryQuartic/verify.sh, commit each coherent round of progress, and do not stop until the Lean proof, verification, and final commit are all complete."
export CODEX_KEEPALIVE_SCRIPT=./QuaternaryQuartic/verify.sh

exec codex --yolo "$CODEX_KEEPALIVE_PROMPT"
