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
- `prompts/ternary_quartic.md` — Ternary-quartic task prompt and workflow.
- `scripts/verify_formalization.sh` — Generic theorem/proof verification
  harness.
- `scripts/verify_ternary_quartic.sh` — Ternary-quartic wrapper around the
  generic verification harness.
- `lakefile.toml` — Lake build configuration (pinned mathlib `v4.29.0`).

### Build and Verify

```bash
lake build
./scripts/verify_ternary_quartic.sh
```

### Verification Harness Details

For the root ternary-quartic development, use
`scripts/verify_ternary_quartic.sh`. It calls the generic
`scripts/verify_formalization.sh` with the ternary-quartic theorem, proof
import, proof file, and expected axiom list.

The generic harness can also be used directly for other theorem/proof pairs:

```bash
./scripts/verify_formalization.sh \
  --theorem TernaryQuartic.ternaryQuartic_rankFour_no_spurious_socp \
  --proof-import TernaryQuarticProof \
  --proof-file TernaryQuarticProof.lean \
  --build-target TernaryQuartic \
  --build-target TernaryQuarticProof \
  --expected-axioms '[propext, Classical.choice, Quot.sound]'
```

The ternary-quartic formalization counts as successful only if all of the
following hold:

- `./scripts/verify_ternary_quartic.sh` exits successfully;
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
- Treat `scripts/verify_formalization.sh` and
  `scripts/verify_ternary_quartic.sh` as stable verification infrastructure
  unless explicitly requested to change them.
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

- `writeup.tex` — General hidden convexity methodology
- `univariate_paper.tex` — Univariate SOS paper draft
- `ternary_quartic/blueprint.tex` — Ternary-quartic proof blueprint
- `ternary_quartic/exploration_log.tex` — Ternary-quartic experiment log
- `ternary_quartic/summary.tex` — Ternary-quartic proof summary

The Vagrant VM provisions `rubber` together with a lightweight TeX Live install
that is sufficient for `writeup.tex`:

```bash
cd writeup
make
make clean
```

`writeup/Makefile` currently builds only `writeup.tex`. To build the
ternary-quartic blueprint directly, run:

```bash
cd writeup/ternary_quartic
rubber --pdf blueprint
rubber --clean blueprint
```

`univariate_paper.tex` is not part of the default VM build flow in the current
repo snapshot: it expects external paper resources such as
`siamart220329.cls`, `geometric_fig.tex`, `results_table.tex`, `r_table.tex`,
and `iterations.pdf` that are not vendored in this worktree.
