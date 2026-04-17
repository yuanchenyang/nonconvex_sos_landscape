Ultrathink. You are an automated mathematician producing a formal Lean proof using Julia SDP dual certificates to guide the argument.

# Goal

Prove `TernaryQuarticRankFourNoSpuriousSOCP` in Lean for the ternary quartic rank-4 Burer-Monteiro problem. Use Julia dual certificates to generate hypotheses, narrow gaps, and validate strategies before formalizing. Every lemma must serve the main proof — do not add unnecessary abstractions or speculative generalizations.

# Strategy

Iterate until the theorem is proved:

1. **Julia exploration**: Run SDP searches (`julia/counter_poly.jl`) to generate dual certificates. Extract algebraic patterns, form hypotheses, and update the proof strategy. See [docs/julia_guide.md](docs/julia_guide.md) for setup and architecture.
2. **Proof in words first**: Before formalizing any subtheorem, write a complete mathematical proof in `writeup/blueprint.tex`. Only attempt Lean formalization once the argument is clear and correct.
3. **Lean formalization**: Translate the written proof into Lean files in `TernaryQuarticProof/`. One logical unit per file.
4. **Verify**: Run `./scripts/verify_formalization.sh`. Update `.tex` documents. Commit.
5. **Reassess**: Find the next gap, repeat from step 1.

# Lean Target

See [docs/lean_guide.md](docs/lean_guide.md) for full build instructions.

- **Statement (read-only)**: `TernaryQuartic.lean`
- **Root proof file**: `TernaryQuarticProof.lean` — must contain the final theorem declaration
- **Proof modules**: `TernaryQuarticProof/` — all helper lemmas go here
- **Theorem**: `TernaryQuartic.ternaryQuartic_rankFour_no_spurious_socp`

**File-scope rules** (non-negotiable):

- Add new Lean files **only** inside `TernaryQuarticProof/`. Add `import TernaryQuarticProof.<Module>` to the root file as needed.
- You may modify `TernaryQuarticProof.lean` (root import file).
- You may **not** modify `TernaryQuartic.lean` or `scripts/verify_formalization.sh`.
- Do **not** weaken, rename, or restate `TernaryQuarticRankFourNoSpuriousSOCP`.

Both `.lean` files set `warningAsError = true` — `sorry` is forbidden.

# Verification

Run the read-only verification harness:

```bash
./scripts/verify_formalization.sh
```

Success requires: the script exits 0 and the axiom check does not mention `sorryAx` (base axioms like `Propext` or `Classical.choice` are fine).

# Julia Dual Certificates

See [docs/julia_guide.md](docs/julia_guide.md) for solver config, persistent REPL workflow, and code architecture. Key functions in `julia/counter_poly.jl`:

- `find_counter(vars, u; ntrials=10, hess=true, verbose=true)`
- `counter_homogeneous(x, d, u, a; verbose=true)`
- `search_basis(n, d, r)` / `rand_u(vars, d, r)`

Use Julia to: generate dual certificates for specific `u`, extract algebraic patterns (divisibility, ideal membership), formulate hypotheses, and validate strategies numerically. Record every numerical claim in a `.jl` file in `julia/` and reference it in the `.tex` files.

# Univariate Reference

The `low_rank_univariate_sos/` submodule is a reference only — do not depend on or build it. See [docs/univariate_proof_strategy.md](docs/univariate_proof_strategy.md) and [docs/univariate_proof_formalization.md](docs/univariate_proof_formalization.md).

# `.tex` Documents

Maintain two documents in `writeup/` (see [docs/lean_guide.md](docs/lean_guide.md) for LaTeX build):

**`exploration_log.tex`** — Running log of all explorations. Append to this single file. Must include: current proof strategy and how it evolved, every Julia experiment with commands/outputs, hypotheses from dual certificates, subgoal outcomes (proved/abandoned/open), remaining blockers.

**`blueprint.tex`** — Self-contained mathematical proof of the full theorem serving as the formalization blueprint. Each section maps to a `TernaryQuarticProof/` file. State every lemma with a complete written proof. Mark which lemmas are formalized vs. pending. Write the proof in words here **before** formalizing in Lean.

# Git Workflow

Start each exploration on a fresh branch (`git switch -c autoproof-tq-r4/<date>`). Commit after each coherent round of work (Julia campaign, proof idea, certificate derivation, or combined checkpoint). Do not leave major progress uncommitted.

# Termination

Stop only when **all** of the following hold:

1. `./scripts/verify_formalization.sh` exits successfully (no `sorryAx`).
2. The theorem `TernaryQuartic.ternaryQuartic_rankFour_no_spurious_socp` is proved in `TernaryQuarticProof.lean`.
3. `writeup/blueprint.tex` contains the complete mathematical proof matching the formalization.
4. The final state is committed.

**Do not terminate if the proof is incomplete.**
