## Project Overview

This is a research project on **benign landscapes** in nonconvex optimization. It
uses computational search to find counterexamples and guide proof development
for analyzing the global landscape of Burer-Monteiro (B-M) factorizations
applied to sum-of-squares (SOS) optimization problems.

**Main Research Question**: For which factorization ranks $r$ do spurious
second-order critical points (SOCPs) exist in the B-M formulation of
sum-of-squares polynomials?

The methodology combines:
1. SDP-based computational search for counterexamples
2. Dual certificate construction from SDP solutions
3. Algebraic geometry analysis (base loci, syzygies) for general proofs

## Repository Structure

```
TernaryQuartic.lean              - Immutable statement file (read-only)
TernaryQuarticProof.lean         - Root import file for the proof
TernaryQuarticProof/             - All new Lean proof code goes here
prompts/                         - Task prompts and agent instructions
scripts/                         - Helper scripts (verification harnesses, Vagrant helpers, agent launcher)
julia/                           - Computational search code (Julia)
julia/ternary_quartic_explorations/ - Saved ternary-quartic Julia experiment scripts
low_rank_univariate_sos/         - Lean 4 + mathlib reference formalization (reference only; do not build it in this workspace)
writeup/                         - Mathematical proofs and writeups (LaTeX sources)
writeup/ternary_quartic/         - Ternary-quartic blueprint, summary, and exploration log
docs/                            - Guides and supporting documentation
```

## Detailed Guides

- **[docs/lean_guide.md](docs/lean_guide.md)** — Building and verifying the
  root Lean project, using the univariate reference without building it here,
  and building the LaTeX writeups
- **[docs/julia_guide.md](docs/julia_guide.md)** — Running Julia SDP searches,
  solver configuration, persistent REPL workflow, code architecture
- **[docs/vagrant_guide.md](docs/vagrant_guide.md)** — Vagrant + VirtualBox VM
  setup, synced folder, Lake bind mount, and common commands
- **[docs/univariate_proof_strategy.md](docs/univariate_proof_strategy.md)** —
  Mathematical proof strategy for the rank-2 univariate case
- **[docs/univariate_proof_formalization.md](docs/univariate_proof_formalization.md)** —
  Summary of the univariate Lean formalization module structure
