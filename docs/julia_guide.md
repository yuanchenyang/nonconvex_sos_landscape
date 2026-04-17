# Julia SDP Search Guide

## Environment Setup

The Vagrant VM provisions Julia `1.12.4` at `/usr/local/bin/julia` by default,
which matches the checked-in `julia/Manifest.toml`. If you override
`JULIA_VERSION` during provisioning, keep it on Julia `1.12.x` or intentionally
re-resolve the manifest before running with a different Julia version.

```bash
cd julia
julia --project=.
```

In Julia REPL:
```julia
using Pkg
Pkg.instantiate()  # Install dependencies from Project.toml
```

## Key Dependencies

- **JuMP**: Mathematical optimization modeling
- **SumOfSquares.jl**: SOS polynomial optimization
- **DynamicPolynomials.jl**: Polynomial manipulation
- **CSDP.jl / MosekTools.jl / SCS.jl**: SDP solvers
- **Combinatorics.jl**: For enumerating monomial combinations
- **AutoGrad.jl / Zygote.jl**: Automatic differentiation (used in experiments)

## Running Counterexample Searches

### Interactive Testing

```julia
include("counter_poly.jl")

@polyvar x[1:2]  # Bivariate polynomial variables

# Test univariate case (should find counterexamples at r=1, not at r≥2)
test_univariate(; d=5, ntrials=10, verbose=true)

# Random factorization at rank 4
u_random = rand_u(x, 2, 4)
find_counter(x, u_random; ntrials=5, verbose=true)
```

### Verified Smoke Test

Random dehomogenized ternary quartic rank 4:

```bash
cd /agent-workspace/julia
julia --project=. \
  -e 'include("counter_poly.jl"); @polyvar x[1:2]; err = find_counter(x, rand_u(x, 2, 4); ntrials=1, verbose=false); println(err)'
```

Observed output is solver- and seed-dependent. In this VM, a verified run
returned `1.84e-11`; values near numerical zero (for example `1e-11` to
`1e-9`) are the expected outcome for this smoke test. On a cold session, the
first run may spend tens of seconds in package loading and compilation before
printing the result.

### Recommended Workflow

Use Julia in this order:

1. Run a cheap smoke test.
2. Test candidate `u` with `find_counter`.
3. If needed, switch to `counter_homogeneous` and inspect dual variables.
4. Record every serious numerical claim in a `.jl` file in the `julia` folder
   with exact commands, and refer to it in the `.tex` file.

## Interpreting Solver Results

- `termination_status(model) == INFEASIBLE` — No counterexample found in that
  formulation.
- `termination_status(model) in [OPTIMAL, ALMOST_OPTIMAL]` — Counterexample
  candidate found.
- In `find_counter`, a returned error much larger than `1e-1` is strong evidence
  of a counterexample; a value near numerical zero is evidence against one for
  that fixed `u`.
- For homogeneous formulation: Check multiple random vectors `a` to ensure
  `c ≠ 0`.
- Numerical tolerance: Use `tol=1e-2` or `1e-3` for error thresholds (SDP
  solvers have limited precision).

## Persistent Julia REPL Workflow (Avoid Precompilation Costs)

Julia has significant precompilation overhead. To avoid paying this cost on
every run, keep a long-lived REPL open in a `tmux` session and send commands to
it. Do not do this if the scripts have an estimated runtime of more than 30
seconds.

### Setup

```bash
# Start a named tmux session with a Julia REPL
tmux new-session -d -s julia -x 220 -y 50
tmux send-keys -t julia "cd /agent-workspace/julia && julia --project=." Enter

# Wait for Julia to finish loading (watch for the julia> prompt)
sleep 10

# Install/instantiate packages on first use
tmux send-keys -t julia 'using Pkg; Pkg.instantiate()' Enter
sleep 60  # Allow time for precompilation
```

### Sending Commands

```bash
# Send a single expression and wait for it to finish
tmux send-keys -t julia 'include("counter_poly.jl")' Enter

# Helper: send a command and capture output by redirecting to a temp file
tmux send-keys -t julia 'open("/tmp/julia_out.txt","w") do f; redirect_stdout(f) do; include("counter_poly.jl"); end; end' Enter

# Poll until the julia> prompt reappears (command finished)
while ! tmux capture-pane -t julia -p | grep -q "^julia>"; do sleep 1; done
```

### Reloading Code After Edits

Because Julia caches compiled code, use `Revise.jl` for hot-reloading:

```julia
# In the REPL (send once after startup)
using Revise
includet("counter_poly.jl")   # 't' = tracked; changes auto-reload
```

Or simply `include()` again — Julia will reparse and recompile only the changed
functions.

### Checking REPL State

```bash
# See what's currently on screen
tmux capture-pane -t julia -p

# Scroll back through recent output
tmux capture-pane -t julia -p -S -100
```

### Teardown

```bash
# Kill the session when done
tmux kill-session -t julia
```

## Code Architecture (`counter_poly.jl`)

### Key Functions

- `feasiblep(model, vars, u; hess=true)` — Constructs SDP for finding spurious
  SOCPs
  - Variables: `p` (polynomial in SOS cone)
  - Constraints:
    - **Gradient**: $\langle A(UV^\top), p - u^\top u \rangle = 0$ for all $V$
    - **Hessian**: $\langle A(VV^\top), p - u^\top u \rangle + 2\|A(UV^\top)\|^2 \geq 0$ for all $V$ (PSD constraint)
    - **Feasibility**: $p \in \text{SOSCone}()$ (sum-of-squares cone)

- `find_counter(vars, u; ntrials=10)` — Search for counterexample by solving SDP
  with random objectives. Returns max error norm across trials. Error > 0.1
  indicates a counterexample exists; error ≈ 0 suggests no counterexample.

- `counter_homogeneous(x, d, u, a)` — Homogenized version using
  $U \to \sqrt{\gamma}U$ with constraint $a^\top c = 1$ to avoid trivial $c=0$
  solution.

- `search_basis(n, d, r)` — Exhaustive search over all $\binom{\dim}{r}$
  monomial basis combinations.

### Mathematical Objects

- $\mathbf{G}_A(U) = \ker(A_U^*)$: Gradient orthogonality subspace
- $\mathbf{H}_A(U)$: Hessian PSD halfspace
- $\mathbf{E}_A(U) = Q(U) - \mathbf{Q}_A$: Error feasibility set
- A spurious SOCP exists iff
  $\mathbf{G}_A(U) \cap \mathbf{H}_A(U) \cap \mathbf{E}_A(U) \neq \{0\}$

### SDP Solvers

The code uses three SDP solvers (configured in function calls):
- **CSDP**: Default solver, most reliable for this problem class
- **Mosek**: Commercial solver (requires license)
- **SCS**: Alternative open-source solver

To switch solvers, modify the `optimizer_with_attributes` call in
`find_counter()` or `counter_homogeneous()`.

### Polynomial Representation

Uses `DynamicPolynomials.jl` and `MultivariatePolynomials.jl`:
- `@polyvar x[1:n]` defines polynomial variables
- `monomials(x, 0:d)` generates monomial basis up to degree $d$
- `dotp(p1, p2)` computes coefficient-wise inner product
- For ternary quartics: $p \in \mathbb{R}[x_1, x_2]_{\leq 4}$ with
  $u_i \in \mathbb{R}[x_1, x_2]_{\leq 2}$

### Dual Certificate Extraction

When SDP is infeasible (no counterexample), the dual certificate proves no
spurious SOCP:
- `dual(grad_c)`: Lagrange multipliers $\lambda$ for gradient constraints
- `dual(psd_c)`: PSD matrix $P$ for Hessian constraint
- `dual(sos_c)`: SOS moment matrix for feasibility constraint

The dual variables satisfy:
$A(X) = c + A_U(\lambda) + H_A^*(P)$ with $X, P \succeq 0$.

### Current Branch Notes

- `counter_poly.jl` now imports `MathOptInterface` correctly; `find_counter` was
  broken before that fix.
- `test_ternary_quartic` is not present in the current file even though older
  docs mention it.
