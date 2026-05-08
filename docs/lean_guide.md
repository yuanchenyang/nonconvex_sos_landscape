# Lean Build Guide

## Root Lean Workspace

The repository root contains Lean 4 theorem families for multiple SOS proof
tracks. The workspace depends on mathlib (pinned in `lakefile.toml`) and is
independent of the univariate submodule.

### Project Layout

- `<Track>/<Track>.lean` — Immutable statement file for one SOS proof track.
- `<Track>/<Track>Proof.lean` — Root import file for the track proof; it must
  keep the final theorem declaration targeted by the verification wrapper.
- `<Track>/<Track>Proof/` — Track-local helper lemmas and proof development.
- `<Track>/prompt.md` — Track-specific proof prompt and workflow.
- `<Track>/verify.sh` — Track-specific wrapper around the generic verification
  harness.
- `<Track>/run.sh` — Track-specific agent launcher.
- `scripts/verify_formalization.sh` — Generic theorem/proof verification
  harness.
- `lakefile.toml` — Lake build configuration (pinned mathlib `v4.29.0`).

Current root tracks include:

- `TernaryQuartic/` — rank-4 ternary quartics.
- `QuaternaryQuartic/` — rank-7 quaternary quartics.

Future tracks, such as ternary sextics, should follow the same directory
pattern and add a corresponding `[[lean_lib]]` target to `lakefile.toml`.

### Build and Verify

```bash
lake build
./TernaryQuartic/verify.sh
./QuaternaryQuartic/verify.sh
```

### Verification Harness Details

Use the project-specific verification scripts for routine workflows:

- `TernaryQuartic/verify.sh` for the completed ternary-quartic target
- `QuaternaryQuartic/verify.sh` for the quaternary-quartic track
- `<Track>/verify.sh` for any future track

Track-specific scripts should delegate to the generic harness. The generic
harness normalizes multi-line `#print axioms` output before comparing it to the
expected list.

The generic harness can also be used directly for other theorem/proof pairs:

```bash
./scripts/verify_formalization.sh \
  --theorem TernaryQuartic.ternaryQuartic_rankFour_no_spurious_socp \
  --proof-import TernaryQuartic.TernaryQuarticProof \
  --proof-file TernaryQuartic/TernaryQuarticProof.lean \
  --build-target TernaryQuartic \
```

A track formalization counts as successful only if all of the following hold:

- its track-specific `verify.sh` exits successfully;
- the selected Lake targets build;
- the proof file typechecks;
- the theorem is available from the proof import;
- the proof file contains the theorem declaration; and
- the axiom check reports exactly these axioms and no others:
  `propext`, `Classical.choice`, `Quot.sound`.

Statement and root proof files should set `warningAsError = true`, so `sorry`
is not allowed in a successful formalization.

### File-Scope Rules

- For a given track, add new Lean files only inside `<Track>/<Track>Proof/`.
- Modify `<Track>/<Track>Proof.lean` only as needed to import modules and keep
  the final theorem declaration.
- Treat `<Track>/<Track>.lean` as the immutable statement file unless the user
  explicitly asks to change the theorem statement.
- Treat `scripts/verify_formalization.sh` and `<Track>/verify.sh` as stable
  verification infrastructure unless explicitly requested to change them.
- Add `import <Track>.<Track>Proof.<Module>` lines to the root
  `<Track>/<Track>Proof.lean` as needed.
- Do not weaken, rename, or restate the fixed proposition for the active track.

### Track Targets

Each track should document its fixed proposition and required theorem name in
its `prompt.md` and `verify.sh`. Current targets:

- `TernaryQuartic.TernaryQuarticRankFourNoSpuriousSOCP`, proved as
  `TernaryQuartic.ternaryQuartic_rankFour_no_spurious_socp`.
- `QuaternaryQuartic.QuaternaryQuarticRankSevenNoSpuriousSOCP`, proved as
  `QuaternaryQuartic.quaternaryQuartic_rankSeven_no_spurious_socp`.

## Univariate Lean Reference Project

The `low_rank_univariate_sos/` folder is a standalone Lean 4 project managed by
`lake`, with mathlib pinned in `lakefile.toml`. This is the verified rank-2
univariate reference development; use it as a guide for root SOS proof tracks
but do not make the root project depend on it.

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
- `quaternary_quartic/blueprint.tex` — Quaternary-quartic proof blueprint
- `quaternary_quartic/exploration_log.tex` — Quaternary-quartic experiment log

Future proof tracks should add their written proof blueprint and exploration log
under `writeup/<track>/`, using a lowercase descriptive directory name such as
`ternary_sextic/`.

The Vagrant VM provisions `rubber` together with a lightweight TeX Live install
that is sufficient for `writeup.tex`:

```bash
cd writeup
make
make clean
```

`writeup/Makefile` currently builds only `writeup.tex`. To build a track
blueprint directly, run the same pattern from that track's writeup directory,
for example:

```bash
cd writeup/ternary_quartic
rubber --pdf blueprint
rubber --clean blueprint
```

`univariate_paper.tex` is not part of the default VM build flow in the current
repo snapshot: it expects external paper resources such as
`siamart220329.cls`, `geometric_fig.tex`, `results_table.tex`, `r_table.tex`,
and `iterations.pdf` that are not vendored in this worktree.
