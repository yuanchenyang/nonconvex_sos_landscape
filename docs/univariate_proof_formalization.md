# Univariate Lean Formalization Summary

The `low_rank_univariate_sos/` folder contains the verified Lean 4 formalization
that the rank-2 Burer–Monteiro factorization of the univariate SOS
decomposition problem has no spurious second-order critical points. This is the
reference development for the ternary-quartic project.

## Main Theorem

The final theorem lives in `RankTwoMain.lean` and states that for any positive-
definite bilinear form $B$, any SOS polynomial $p$, and any rank-2 factor
$\mathbf{u}$, if $\mathbf{u}$ is a second-order critical point of the
quadratic-penalty objective $f_p(\mathbf{u}) = \lVert\sigma(\mathbf{u}) - p\rVert_B^2$,
then $\sigma(\mathbf{u}) = p$ (no spurious SOCPs).

## Module Structure

The entry point is `LowRankUnivariateSOS.lean`, which imports all submodules.
The dependency chain (bottom-up):

| Module | Role |
|--------|------|
| `PolynomialModel` | Core types: `Poly` (= `Polynomial ℝ`), `UPair` (rank-2 factor pair), `sigma2`, `A`, `residual` |
| `Socp` | Abstract bilinear form `DotForm`, first/second-order conditions (`IsFOCP`, `IsSOCP`) |
| `Certificate` | `InImagePlusSigmaKerCone` — the paper's condition (C2): $p \in \operatorname{im}(\mathcal{A}_u) + \operatorname{cone}(\sigma(\ker \mathcal{A}_u))$ |
| `H1Case` | `scalePair`, `perpPair` — building blocks for the $h = 1$ (coprime GCD) case |
| `FactoredCase` | Converts explicit $h = 1$ decomposition into image-plus-cone form |
| `UnivariateAlgebraCore` | `ReducedFactorization`, `gcd_sigma_decomposition` — GCD-based canonical decomposition $u = a \cdot u_0$ |
| `UnivariateSOS` | SOS-specific algebra: `isSOS_mul` (two-squares identity), `hgroup_affine` (SOS multiplier modulo coprime factor) |
| `PeelingStep` | One step of complex-root peeling; iteratively replaces complex factors of $h$ with real ones |
| `UnivariateAlgebra` | Full factor-peeling reduction assembling all algebraic steps |
| `RankTwoMain` | Final theorem: combines factor peeling, hgroup, and SOCP conditions |

## Key Definitions

- **`UPair`**: Rank-2 factor variable $(u_1, u_2)$, represented as a structure
  with two `Poly` fields.
- **`sigma2 u`**: The quadratic map $\sigma(\mathbf{u}) = u_1^2 + u_2^2$.
- **`A u v`**: The bilinear map $\mathcal{A}_\mathbf{u}(\mathbf{v}) = u_1 v_1 + u_2 v_2$.
- **`residual p u`**: The residual $\sigma(\mathbf{u}) - p$.
- **`IsSOS p`**: Polynomial $p$ is a binary sum of two squares ($\exists a, b.\ p = a^2 + b^2$).
- **`scalePair g u`**: Multiply both coordinates by $g$: $(g u_1, g u_2)$.
- **`perpPair t u`**: Syzygy element $(-t u_2, t u_1) \in \ker \mathcal{A}_u$.
- **`ReducedFactorization u`**: Canonical decomposition $u = a \cdot u_0$ with
  $u_0$ coprime.

## Key Lemmas

- **`hgroup_affine`** (`UnivariateSOS`): If $p$ and $q$ are SOS and $g$ is
  coprime to $q$, then $p = g \cdot t + s \cdot q$ with $s$ SOS. Uses Bézout
  coefficients and the two-squares identity.
- **`isSOS_mul`** (`UnivariateSOS`): Product of two binary sums of squares is
  SOS (classical Brahmagupta–Fibonacci identity).
- **`factor_peeling_certificate_step`** (`RankTwoMain`): From a nonzero reduced
  factorization, obtains a coprime factor $g$ such that condition (C2) holds.

## Relation to Proof Strategy

See `docs/univariate_proof_strategy.md` for the mathematical proof summary
corresponding to this formalization. The three cases (C1: coprime, C2: shared
factor coprime with $\sigma(u')$, C3: general with complex-root peeling)
map directly to the module hierarchy above.

## Build Configuration

- Lean 4 with mathlib `v4.29.0` (pinned in `lakefile.toml`)
- Also depends on `checkdecls` for declaration checking
- Entry point: `LowRankUnivariateSOS` library target
