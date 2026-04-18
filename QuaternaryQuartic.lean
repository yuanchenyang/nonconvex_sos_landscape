import Mathlib

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace QuaternaryQuartic

open scoped BigOperators

/-
`QuaternaryQuartic.lean` is the immutable statement file for the rank-5
quaternary-quartic formalization. Exploration agents may read this file but
should treat it as read-only. The primary write target is
`QuaternaryQuarticProof.lean`.
-/

/-- We work in dehomogenized coordinates: quaternary quartics become quartics
in three affine variables. -/
abbrev Poly := MvPolynomial (Fin 3) ℝ

/-- The rank-5 Burer--Monteiro factor is a 5-tuple of quadratic polynomials. -/
abbrev RankFiveVec := Fin 5 → Poly

/-- Degree bound for the quadratic factors in the quaternary-quartic problem. -/
def IsQuadratic (p : Poly) : Prop :=
  p.totalDegree ≤ 2

/-- Degree bound for dehomogenized quaternary quartics. -/
def IsQuartic (p : Poly) : Prop :=
  p.totalDegree ≤ 4

/-- Admissible rank-5 factor variables: every coordinate has degree at most 2. -/
def IsAdmissiblePoint (u : RankFiveVec) : Prop :=
  ∀ i, IsQuadratic (u i)

/-- The same degree restriction is used for tangent directions. -/
def IsAdmissibleDirection (v : RankFiveVec) : Prop :=
  IsAdmissiblePoint v

/-- The quadratic map `σ(u) = \sum_i u_i^2`. -/
def sigma (u : RankFiveVec) : Poly :=
  ∑ i : Fin 5, (u i) ^ 2

/-- The linearization `A_u(v) = \sum_i u_i v_i`. -/
def A (u v : RankFiveVec) : Poly :=
  ∑ i : Fin 5, u i * v i

/-- The residual `σ(u) - p`. Vanishing of this residual is the no-spurious-SOCP
conclusion. -/
def residual (p : Poly) (u : RankFiveVec) : Poly :=
  sigma u - p

/-- SOS feasibility for the quaternary-quartic target. We encode the target as
a quartic together with some finite SOS representation by quadratic summands. -/
def IsSOSQuartic (p : Poly) : Prop :=
  IsQuartic p ∧
    ∃ k : ℕ, ∃ qs : Fin k → Poly, (∀ i, IsQuadratic (qs i)) ∧ p = ∑ i : Fin k, (qs i) ^ 2

/-- The development is abstract over the bilinear form used to define the
quadratic penalty objective. -/
abbrev DotForm := LinearMap.BilinForm ℝ Poly

/-- Positive-definiteness of the bilinear form, matching the abstract setup in
the existing project. -/
def IsPositiveDefinite (B : DotForm) : Prop :=
  B.toQuadraticMap.PosDef

/-- The quadratic-penalty objective `f_p(u) = ⟨σ(u)-p, σ(u)-p⟩`. -/
def objective (B : DotForm) (p : Poly) (u : RankFiveVec) : ℝ :=
  B (residual p u) (residual p u)

/-- First-order criticality, restricted to quadratic directions. -/
def IsFOCP (B : DotForm) (p : Poly) (u : RankFiveVec) : Prop :=
  ∀ v : RankFiveVec, IsAdmissibleDirection v → B (A u v) (residual p u) = 0

/-- The Hessian quadratic form along an admissible direction. -/
def hessianTerm (B : DotForm) (p : Poly) (u v : RankFiveVec) : ℝ :=
  B (sigma v) (residual p u) + 2 * B (A u v) (A u v)

/-- Second-order criticality for the rank-5 quaternary-quartic problem. -/
def IsSOCP (B : DotForm) (p : Poly) (u : RankFiveVec) : Prop :=
  IsFOCP B p u ∧ ∀ v : RankFiveVec, IsAdmissibleDirection v → 0 ≤ hessianTerm B p u v

/-- Fixed target statement for the quaternary-quartic proof track. -/
def QuaternaryQuarticRankFiveNoSpuriousSOCP : Prop :=
  ∀ (B : DotForm) (p : Poly) (u : RankFiveVec),
    IsPositiveDefinite B →
    IsSOSQuartic p →
    IsAdmissiblePoint u →
    IsSOCP B p u →
    residual p u = 0

end QuaternaryQuartic
