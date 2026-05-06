# Automatic Proof of a Benign Nonconvex Landscape Theorem

[![Read Blog Post](https://img.shields.io/badge/Read-Blog%20Post-blue?logo=readthedocs)](https://chenyang.co/blog/automatic-theorem-proving.html)

<img src="/imgs/loc_autoproof-tq-r4-apr9.png" alt="Successful Apr 9 run LOC">

This repository showcases an automatic theorem-proving run for a nonconvex
optimization problem: The rank-4 Burer-Monteiro factorization of ternary quartic
sum-of-squares (SOS) polynomials. Given just the [problem statement in
Lean](/TernaryQuartic.lean) , the proof agent autonomously used Julia to
formulate [semidefinite programs (SDPs)](/julia/counter_poly.jl) that search for
counterexamples and expose certificate structure, then used Lean 4 and mathlib
to produce the final machine-checked theorem.

The successful run was produced by a lightweight harness using Codex with GPT
5.4 (xhigh reasoning).

## What Was Proved

The main theorem is stated in [`TernaryQuartic.lean`](/TernaryQuartic.lean). Let
$\mathbb{R}[x_1,x_2,x_3]_d$ be the space of ternary forms of total degree
$d$, and

```math
  \mathbf{u} = [u_1,\ldots,u_4] \in \mathbb{R}[x_1,x_2,x_3]_2^4.
```
For any quartic sum-of-squares form
$p \in \Sigma[x_1,x_2,x_3]_4$, consider the following objective that finds a
factorization of $p$ as a sum of 4 squares:

```math
  f_p(\mathbf{u}) = \left\|\sum_{i=1}^4 u_i^2 - p\right\|^2,
```

where the norm is induced by any positive-definite inner product on
$\mathbb{R}[x_1,x_2,x_3]_4$.

The theorem states that for all $p \in \Sigma[x_1,x_2,x_3]_4$, if
$\mathbf{u}$ is a second-order critical point of $f_p$ satisfying the first- and
second-order conditions:

```math
  \nabla_{\mathbf{u}} f_p(\mathbf{u})(\mathbf{v}) = 0
  \quad \text{and} \quad
  \nabla_{\mathbf{u}}^2 f_p(\mathbf{u})(\mathbf{v},\mathbf{v})
  \ge 0
```
for every $\mathbf{v} \in \mathbb{R}[x_1, x_2, x_3]_2^4$, then

```math
  f_p(\mathbf{u}) = 0
  \qquad\text{and hence}\qquad
  p = \sum_{i=1}^4 u_i^2.
```

Although $f_p$ corresponds to a nonconvex rank-4 Burer-Monteiro factorization of
the sum-of-sqaures SDP, this theorem shows that $f_p$ has a benign
landscape: all of its local minima are also global minima.

## Methodology

The proof was built through an automated Julia-to-Lean loop:

1. **Julia SDP exploration** searched for spurious critical points and produced
   numerical evidence and dual-certificate structure.
2. **Mathematical blueprinting** translated the computational patterns into a
   proof strategy for the ternary-quartic case.
3. **Lean formalization** encoded the theorem and supporting algebraic lemmas in
   Lean 4.
4. **Verification harnessing** checked that the final theorem builds, is exposed
   under the required name, and depends only on the expected Lean axioms.

Julia was used for the experimental and certificate-discovery layer. Lean was
used for the final proof, so the theorem does not depend on numerical solver
trust.

## Agent Harness

The proof run was managed inside the repository's [Vagrant VM](docs/vagrant_guide.md),
which provides a reproducible Ubuntu environment with Lean, Julia, Lake caches,
and SDP solver dependencies available to the agent. The harness launches Codex
with a persistent keepalive prompt so the same high-level goal survives context
compaction and long-running work sessions; this is the "Codex continuation"
pattern described [here](https://www.chenyang.co/blog/agents/2026/04/16/codex-continuation.html).

For the ternary-quartic run, the entrypoint is
[`scripts/run_ternary_quartic.sh`](scripts/run_ternary_quartic.sh). It sets
`CODEX_KEEPALIVE=1`, supplies the fixed theorem-proving instructions through
`CODEX_KEEPALIVE_PROMPT`, and starts `codex --yolo` so the agent can iterate
through Julia exploration, LaTeX blueprinting, Lean formalization, verification,
and commits without losing the target.

## Run History

Earlier automatic proof attempts failed before the successful Apr 9 run.

### Apr 9: Successful Run

This run generated 58k lines of Lean code, 2k lines of Julia code and 7.5k lines
of LaTeX over 200 commits.

<img src="/imgs/loc_autoproof-tq-r4-apr9.png" alt="Successful Apr 9 run LOC" width="720">

It also produced the following commits over time (over 3 days of continuous work):

<img src="/imgs/commits_autoproof-tq-r4-apr9.png" alt="Successful Apr 9 commit history" width="720">

### Apr 6: Failed Previous Run

This run got stuck running too many Julia experiments and not coming up with proof ideas.

<img src="/imgs/loc_autoproof-tq-r4-apr6.png" alt="Failed Apr 6 run LOC" width="400">

### Apr 4: Failed Previous Run

This run got stuck iterating on a proof strategy that proved too difficult to formalize.

<img src="/imgs/loc_autoproof-tq-r4-apr4.png" alt="Failed Apr 4 run LOC" width="720">


## Julia and Lean

The Julia code in [`julia/`](julia/) implements SDP-based counterexample search
and certificate exploration using [JuMP](https://github.com/jump-dev/JuMP.jl),
[SumOfSquares.jl](https://github.com/jump-dev/SumOfSquares.jl),
[DynamicPolynomials.jl](https://github.com/JuliaAlgebra/DynamicPolynomials.jl),
and SDP solvers. See [`docs/julia_guide.md`](docs/julia_guide.md) for setup and
workflow details.

The Lean proof lives in [`TernaryQuarticProof/`](TernaryQuarticProof/) with the
fixed statement in [`TernaryQuartic.lean`](TernaryQuartic.lean) and root theorem
assembly in [`TernaryQuarticProof.lean`](TernaryQuarticProof.lean). See
[`docs/lean_guide.md`](docs/lean_guide.md) for build and verification details.

The original prover prompt and workflow are recorded in
[`prompts/ternary_quartic.md`](prompts/ternary_quartic.md). The mathematical
blueprint is in
[`writeup/ternary_quartic/blueprint.pdf`](writeup/ternary_quartic/blueprint.pdf).

## Reference

This ternary-quartic theorem builds on the univariate SOS landscape framework
and its Lean formalization. The related Lean repository is
[`yuanchenyang/lean_low_rank_univariate_sos`](https://github.com/yuanchenyang/lean_low_rank_univariate_sos).

Paper citation: Benoit Legat, Chenyang Yuan, and Pablo A. Parrilo,
[*Low-Rank Univariate Sum of Squares Has No Spurious Local Minima*](https://arxiv.org/abs/2205.11466),
*SIAM Journal on Optimization*, 33(3), 2023
([DOI: 10.1137/22M1516208](https://doi.org/10.1137/22M1516208)).

## Verification

Run the ternary-quartic verification harness:

```bash
./scripts/verify_ternary_quartic.sh
```

The harness builds the Lean targets, typechecks the proof file, confirms the
theorem declaration, and checks that the theorem depends exactly on:

```text
propext, Classical.choice, Quot.sound
```
