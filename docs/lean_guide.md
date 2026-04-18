# Lean Build Guide

## Root Lean Workspace

The repository root contains Lean 4 theorem families for multiple SOS proof
tracks. The workspace depends on mathlib (pinned in `lakefile.toml`) and is
independent of the univariate submodule.

### Project Layout

- `TernaryQuartic.lean` — Immutable statement file for the rank-4
  ternary-quartic theorem.
- `TernaryQuarticProof.lean` — Root import file for the ternary proof; must
  keep the final theorem declaration.
- `TernaryQuarticProof/` — Ternary helper lemmas and proof development.
- `QuaternaryQuartic.lean` — Immutable statement file for the rank-7
  quaternary-quartic theorem.
- `QuaternaryQuarticProof.lean` — Root import file for the quaternary proof.
- `QuaternaryQuarticProof/` — Quaternary helper lemmas and proof development.
- `program.md` — Active execution brief for the quaternary proof track.
- `prompts/ternary_quartic.md` — Ternary-quartic task prompt and workflow.
- `scripts/verify_formalization.sh` — Generic theorem/proof verification
  harness.
- `scripts/verify_ternary_quartic.sh` — Ternary-quartic wrapper around the
  generic verification harness.
- `scripts/verify_quaternary_quartic.sh` — Quaternary-quartic full verification
  script for the theorem scaffold.
- `lakefile.toml` — Lake build configuration (pinned mathlib `v4.29.0`).

### Build and Verify

```bash
lake build
./scripts/verify_ternary_quartic.sh
./scripts/verify_quaternary_quartic.sh
```

### Verification Harness Details

Use the project-specific verification scripts for routine workflows:

- `scripts/verify_ternary_quartic.sh` for the completed ternary-quartic target
- `scripts/verify_quaternary_quartic.sh` for the new quaternary-quartic track

The ternary script delegates to the generic harness. The quaternary script
also delegates to the generic harness. The generic harness now normalizes
multi-line `#print axioms` output before comparing it to the expected list.

The generic harness can also be used directly for other theorem/proof pairs:

```bash
./scripts/verify_formalization.sh \
  --theorem TernaryQuartic.ternaryQuartic_rankFour_no_spurious_socp \
  --proof-import TernaryQuarticProof \
  --proof-file TernaryQuarticProof.lean \
  --build-target TernaryQuartic \
  --build-target TernaryQuarticProof \
```

The ternary-quartic formalization counts as successful only if all of the
following hold:

- `./scripts/verify_ternary_quartic.sh` exits successfully;
- equivalently, commands 1, 2, 3, and 4 must succeed;
- command 5 must report exactly these axioms and no others:
  `propext`, `Classical.choice`, `Quot.sound`.

Both `TernaryQuartic.lean` and `TernaryQuarticProof.lean` set
`warningAsError = true`, so `sorry` is not allowed in a successful formalization.

For the quaternary-quartic track, the current wrapper is full-strength in the
same sense as the ternary wrapper: it targets the theorem
`QuaternaryQuartic.quaternaryQuartic_rankSeven_no_spurious_socp`, checks that the
theorem is defined in `QuaternaryQuarticProof.lean`, and enforces the same
default allowed axiom list used by the generic harness. Because the current
scaffold still depends on the temporary axiom
`QuaternaryQuartic.quaternaryQuartic_rankSeven_no_spurious_socp_placeholder`,
the quaternary verification script is expected to fail until that placeholder is
removed.

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

For the quaternary track:

- You may add new Lean files **only** inside `QuaternaryQuarticProof/`.
- You may modify `QuaternaryQuarticProof.lean` (root import file that must keep
  the final theorem declaration).
- You should treat `QuaternaryQuartic.lean` as the immutable statement file for
  this track.
- Add `import QuaternaryQuarticProof.<Module>` lines to the root
  `QuaternaryQuarticProof.lean` as needed.

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

There is no committed `writeup/quaternary_quartic/` folder in the current repo
snapshot yet. If the quaternary track grows a parallel writeup, add it under
`writeup/` explicitly rather than assuming those files already exist.

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
