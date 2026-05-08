#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT_DIR"

export CODEX_KEEPALIVE=1
export CODEX_KEEPALIVE_PROMPT='Keep the goal fixed: prove TernaryQuartic.ternaryQuartic_rankFour_no_spurious_socp for TernaryQuarticRankFourNoSpuriousSOCP, using Julia SDP dual certificates only to generate and test proof ideas, then write the full argument in writeup/ternary_quartic/blueprint.tex before formalizing it in Lean; add only proof-serving lemmas, keep the final theorem declaration in TernaryQuartic/TernaryQuarticProof.lean, do not weaken or restate the target, do not touch TernaryQuartic/TernaryQuartic.lean, treat the verification harnesses as stable unless explicitly asked, do not build or depend on low_rank_univariate_sos/, log all experiments and strategy changes in writeup/ternary_quartic/exploration_log.tex, record numerical claims in julia/ternary_quartic_explorations/ and reference them in the .tex files, verify regularly with ./TernaryQuartic/verify.sh, commit each coherent round of progress, and do not stop until the Lean proof, blueprint, verification, and final commit are all complete.'
export CODEX_KEEPALIVE_SCRIPT=./TernaryQuartic/verify.sh

exec codex --yolo "$CODEX_KEEPALIVE_PROMPT"
