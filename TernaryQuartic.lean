import Mathlib

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace TernaryQuartic

open scoped BigOperators

/-
`TernaryQuartic.lean` is the immutable statement file for the root
formalization. Exploration agents may read this file but should treat it as
read-only. The only intended write target is `TernaryQuarticProof.lean`.
-/

/-- We work in dehomogenized coordinates: ternary quartics become quartics in
two affine variables. -/
abbrev Poly := MvPolynomial (Fin 2) ℝ

/-- The rank-4 Burer--Monteiro factor is a 4-tuple of quadratic polynomials. -/
abbrev RankFourVec := Fin 4 → Poly

/-- Degree bound for the quadratic factors in the ternary-quartic problem. -/
def IsQuadratic (p : Poly) : Prop :=
  p.totalDegree ≤ 2

/-- Degree bound for dehomogenized ternary quartics. -/
def IsQuartic (p : Poly) : Prop :=
  p.totalDegree ≤ 4

/-- Admissible rank-4 factor variables: every coordinate has degree at most 2. -/
def IsAdmissiblePoint (u : RankFourVec) : Prop :=
  ∀ i, IsQuadratic (u i)

/-- The same degree restriction is used for tangent directions. -/
def IsAdmissibleDirection (v : RankFourVec) : Prop :=
  IsAdmissiblePoint v

/-- The quadratic map `σ(u) = \sum_i u_i^2`. -/
def sigma (u : RankFourVec) : Poly :=
  ∑ i : Fin 4, (u i) ^ 2

/-- The linearization `A_u(v) = \sum_i u_i v_i`. -/
def A (u v : RankFourVec) : Poly :=
  ∑ i : Fin 4, u i * v i

/-- The residual `σ(u) - p`. Vanishing of this residual is the no-spurious-SOCP
conclusion. -/
def residual (p : Poly) (u : RankFourVec) : Poly :=
  sigma u - p

/-- SOS feasibility for the ternary-quartic target. We encode the target as a
quartic together with some finite SOS representation by quadratic summands. -/
def IsSOSQuartic (p : Poly) : Prop :=
  IsQuartic p ∧
    ∃ k : ℕ, ∃ qs : Fin k → Poly, (∀ i, IsQuadratic (qs i)) ∧ p = ∑ i : Fin k, (qs i) ^ 2

/-- The development is abstract over the bilinear form used to define the
quadratic penalty objective. -/
abbrev DotForm := LinearMap.BilinForm ℝ Poly

/-- Positive-definiteness of the bilinear form, matching the abstract setup in
the univariate formalization. -/
def IsPositiveDefinite (B : DotForm) : Prop :=
  B.toQuadraticMap.PosDef

/-- The quadratic-penalty objective `f_p(u) = ⟨σ(u)-p, σ(u)-p⟩`. -/
def objective (B : DotForm) (p : Poly) (u : RankFourVec) : ℝ :=
  B (residual p u) (residual p u)

/-- First-order criticality, restricted to quadratic directions. -/
def IsFOCP (B : DotForm) (p : Poly) (u : RankFourVec) : Prop :=
  ∀ v : RankFourVec, IsAdmissibleDirection v → B (A u v) (residual p u) = 0

/-- The Hessian quadratic form along an admissible direction. -/
def hessianTerm (B : DotForm) (p : Poly) (u v : RankFourVec) : ℝ :=
  B (sigma v) (residual p u) + 2 * B (A u v) (A u v)

/-- Second-order criticality for the rank-4 ternary-quartic problem. -/
def IsSOCP (B : DotForm) (p : Poly) (u : RankFourVec) : Prop :=
  IsFOCP B p u ∧ ∀ v : RankFourVec, IsAdmissibleDirection v → 0 ≤ hessianTerm B p u v

/-- Fixed target statement for the root Lean project. A successful
formalization should prove this exact proposition without weakening or renaming
it. -/
def TernaryQuarticRankFourNoSpuriousSOCP : Prop :=
  ∀ (B : DotForm) (p : Poly) (u : RankFourVec),
    B.IsSymm →
    IsPositiveDefinite B →
    IsSOSQuartic p →
    IsAdmissiblePoint u →
    IsSOCP B p u →
    residual p u = 0

end TernaryQuartic
