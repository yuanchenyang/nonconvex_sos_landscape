Ultrathink. You are an automated mathematician producing a formal Lean proof using Julia SDP dual certificates to guide the argument.

# Goal

Prove `QuaternaryQuarticRankSevenNoSpuriousSOCP` in Lean for the quaternary quartic rank-7 Burer-Monteiro problem. Use Julia dual certificates to generate hypotheses, narrow gaps, and validate strategies before formalizing. Every lemma must serve the main proof — do not add unnecessary abstractions or speculative generalizations.

# Strategy

Iterate until the theorem is proved:

1. **Julia exploration**: Run SDP searches (`julia/counter_poly.jl`) to generate dual certificates. Extract algebraic patterns, form hypotheses, and update the proof strategy. See [docs/julia_guide.md](docs/julia_guide.md) for setup and architecture.
2. **Proof in words first**: Before formalizing any subtheorem, write a complete mathematical proof in a quaternary blueprint under `writeup/` (for example `writeup/quaternary_quartic/blueprint.tex` once that folder exists). Only attempt Lean formalization once the argument is clear and correct.
3. **Lean formalization**: Translate the written proof into Lean files in `QuaternaryQuarticProof/`. One logical unit per file.
4. **Verify**: Run `./scripts/verify_quaternary_quartic.sh`. Update `.tex` documents. Commit.
5. **Reassess**: Find the next gap, repeat from step 1.

# Lean Target

See [docs/lean_guide.md](docs/lean_guide.md) for full build instructions.

- **Statement (read-only)**: `QuaternaryQuartic.lean`
- **Root proof file**: `QuaternaryQuarticProof.lean` — must contain the final theorem declaration
- **Proof modules**: `QuaternaryQuarticProof/` — all helper lemmas go here
- **Theorem**: `QuaternaryQuartic.quaternaryQuartic_rankSeven_no_spurious_socp`

**File-scope rules** (non-negotiable):

- Add new Lean files **only** inside `QuaternaryQuarticProof/`. Add `import QuaternaryQuarticProof.<Module>` to the root file as needed.
- You may modify `QuaternaryQuarticProof.lean` (root import file).
- You may **not** modify `QuaternaryQuartic.lean`, `scripts/verify_formalization.sh`, or `scripts/verify_quaternary_quartic.sh`.
- Do **not** weaken, rename, or restate `QuaternaryQuarticRankSevenNoSpuriousSOCP`.

Both `.lean` files set `warningAsError = true` — `sorry` is forbidden.

# Verification

Run the read-only verification harness:

```bash
./scripts/verify_quaternary_quartic.sh
```

The wrapper is intentionally full-strength. While the placeholder axiom remains,
this script should fail at the axiom check because it does **not** whitelist
`QuaternaryQuartic.quaternaryQuartic_rankSeven_no_spurious_socp_placeholder`.
Success requires removing that placeholder so the theorem verifies against the
default allowed axiom set (in particular, no `sorryAx`).

# Julia Dual Certificates

See [docs/julia_guide.md](docs/julia_guide.md) for solver config, persistent REPL workflow, and code architecture. Key functions in `julia/counter_poly.jl`:

- `find_counter(vars, u; ntrials=10, hess=true, verbose=true)`
- `counter_homogeneous(x, d, u, a; verbose=true)`
- `search_basis(n, d, r)` / `rand_u(vars, d, r)`

Use Julia to: generate dual certificates for specific `u`, extract algebraic patterns (divisibility, ideal membership), formulate hypotheses, and validate strategies numerically. Record every numerical claim in a quaternary exploration file under `julia/` (for example in `julia/quaternary_quartic_explorations/` once that folder exists) and reference it in the `.tex` files.

# Univariate Reference

The `low_rank_univariate_sos/` submodule is a reference only — do not depend on or build it. See [docs/univariate_proof_strategy.md](docs/univariate_proof_strategy.md) and [docs/univariate_proof_formalization.md](docs/univariate_proof_formalization.md).

# Ternary Quartic Reference

Use the completed ternary-quartic development as a structural reference for the
quaternary rank-7 proof track. Proof hints and reusable lemmas from the
ternary development should be reused wherever they transfer cleanly to the
quaternary setting:

- `writeup/ternary_quartic/blueprint.tex` — full written proof blueprint in the
  writeups folder
- `TernaryQuarticProof.lean` — root Lean theorem proof
- `TernaryQuarticProof/` — supporting Lean proof modules

# `.tex` Documents

Once quaternary-quartic writeups are created, maintain them in `writeup/quaternary_quartic/` (see [docs/lean_guide.md](docs/lean_guide.md) for LaTeX build):

**`exploration_log.tex`** — Running log of all explorations. Append to this single file. Must include: current proof strategy and how it evolved, every Julia experiment with commands/outputs, hypotheses from dual certificates, subgoal outcomes (proved/abandoned/open), remaining blockers.

**`blueprint.tex`** — Self-contained mathematical proof of the full theorem serving as the formalization blueprint. Each section maps to a `QuaternaryQuarticProof/` file. State every lemma with a complete written proof. Mark which lemmas are formalized vs. pending. Write the proof in words here **before** formalizing in Lean.

# Git Workflow

Start each exploration on a fresh branch (`git switch -c autoproof-qq-r7/<date>`). Commit after each coherent round of work (Julia campaign, proof idea, certificate derivation, or combined checkpoint). Do not leave major progress uncommitted.

# Termination

Stop only when **all** of the following hold:

1. `./scripts/verify_quaternary_quartic.sh` exits successfully (no `sorryAx`).
2. The theorem `QuaternaryQuartic.quaternaryQuartic_rankSeven_no_spurious_socp` is proved in `QuaternaryQuarticProof.lean`.
3. A quaternary blueprint under `writeup/` contains the complete mathematical proof matching the formalization.
4. The final state is committed.

**Do not terminate if the proof is incomplete.**
