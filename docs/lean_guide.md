# Lean Build Guide

## Root Ternary-Quartic Project

The repository root contains the current ternary-quartic Lean 4 project. It
depends on mathlib (pinned in `lakefile.toml`) and is independent of the
univariate submodule.

### Project Layout

- `TernaryQuartic.lean` — Immutable statement file (read-only).
- `TernaryQuarticProof.lean` — Root import file; must keep the final theorem
  declaration.
- `TernaryQuarticProof/` — All helper lemmas and proof development go here.
- `lakefile.toml` — Lake build configuration (pinned mathlib `v4.29.0`).

### Build and Verify

```bash
lake build
./scripts/verify_formalization.sh
```

### Verification Harness Details

The script `scripts/verify_formalization.sh` is the root verification harness.
Treat it as stable infrastructure and modify it only when explicitly requested.
The formalization counts as successful only if all of the following hold:

- `./scripts/verify_formalization.sh` exits successfully;
- equivalently, commands 1, 2, 3, and 4 must succeed;
- command 5 must report exactly these axioms and no others:
  `propext`, `Classical.choice`, `Quot.sound`.

Both `TernaryQuartic.lean` and `TernaryQuarticProof.lean` set
`warningAsError = true`, so `sorry` is not allowed in a successful formalization.

### File-Scope Rules

- You may add new Lean files **only** inside `TernaryQuarticProof/`.
- You may modify `TernaryQuarticProof.lean` (root import file that must keep the
  final theorem declaration).
- You may **not** modify `TernaryQuartic.lean`.
- Do not modify `scripts/verify_formalization.sh` unless explicitly requested.
- Add `import TernaryQuarticProof.<Module>` lines to the root
  `TernaryQuarticProof.lean` as needed.

### Fixed Lean Target

- Fixed proposition: `TernaryQuartic.TernaryQuarticRankFourNoSpuriousSOCP`
- Required theorem name:
  `TernaryQuartic.ternaryQuartic_rankFour_no_spurious_socp`
- Do not weaken, rename, or restate the proposition. The statement lives in
  `TernaryQuartic.lean`; the proof must be added in `TernaryQuarticProof.lean`.

## Univariate Lean Reference Project

The `low_rank_univariate_sos/` folder is a standalone Lean 4 project managed by
`lake`, with mathlib pinned in `lakefile.toml`. This is the verified rank-2
univariate reference development; use it as a guide for the root ternary-quartic
project but do not make the root project depend on it.

### Workspace Policy

- Do **not** run `lake update`, `lake exe cache get`, `lake build`, or
  `lake env lean ...` inside `low_rank_univariate_sos/` from this workspace.
- Treat `low_rank_univariate_sos/` as a read-only reference for proof ideas and
  module structure.
- If you need a fresh build of that standalone project, do it from a separate
  clean clone outside this repository snapshot.

### Reference Files

- `LowRankUnivariateSOS/PolynomialModel.lean` — Core types and operations
- `LowRankUnivariateSOS/Socp.lean` — Abstract SOCP conditions
- `LowRankUnivariateSOS/RankTwoMain.lean` — Final theorem assembly

See `docs/univariate_proof_formalization.md` for a summary of the module
structure.

## LaTeX Writeups

The `writeup/` folder contains the project LaTeX sources:

- `writeup.tex`: General hidden convexity methodology
- `paper.tex`: Paper containing proof for univariate case

The Vagrant VM provisions `rubber` together with a lightweight TeX Live install
that is sufficient for `writeup.tex`:

```bash
cd writeup
make
make clean
```

`paper.tex` is not part of the default VM build flow in the current repo
snapshot: it expects `siamart220329.cls`, `iterations.pdf`, and a bibliography
resource path that are not available in this VM/worktree layout.
