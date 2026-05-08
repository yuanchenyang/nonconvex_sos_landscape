import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import QuaternaryQuartic.QuaternaryQuartic

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace QuaternaryQuartic

section BilinearLemmas

variable {B : DotForm}

@[simp] theorem dot_add_left (p q r : Poly) :
    B (p + q) r = B p r + B q r := by
  simp

@[simp] theorem dot_add_right (p q r : Poly) :
    B p (q + r) = B p q + B p r := by
  simp

@[simp] theorem dot_smul_left (a : ℝ) (p q : Poly) :
    B (a • p) q = a * B p q := by
  simp [smul_eq_mul]

@[simp] theorem dot_smul_right (a : ℝ) (p q : Poly) :
    B p (a • q) = a * B p q := by
  simp [smul_eq_mul]

@[simp] theorem dot_zero_left (p : Poly) : B 0 p = 0 := by
  simp

@[simp] theorem dot_zero_right (p : Poly) : B p 0 = 0 := by
  simp

@[simp] theorem dot_neg_left (p q : Poly) :
    B (-p) q = -B p q := by
  simp

@[simp] theorem dot_neg_right (p q : Poly) :
    B p (-q) = -B p q := by
  simp

end BilinearLemmas

@[simp] theorem A_self_eq_sigma (u : RankSevenVec) : A u u = sigma u := by
  simp [A, sigma, pow_two]

theorem focp_sigma_residual_eq_zero {B : DotForm} {p : Poly} {u : RankSevenVec}
    (h : IsFOCP B p u) (hu : IsAdmissiblePoint u) :
    B (sigma u) (residual p u) = 0 := by
  simpa [A_self_eq_sigma, IsAdmissibleDirection] using h u hu

section Positivity

variable {B : DotForm} [Fact B.toQuadraticMap.PosDef]

theorem objective_nonneg (p : Poly) (u : RankSevenVec) : 0 ≤ objective B p u := by
  simpa [objective, LinearMap.BilinMap.toQuadraticMap_apply] using
    (Fact.out : B.toQuadraticMap.PosDef).nonneg (residual p u)

theorem objective_eq_zero_iff_residual_eq_zero {p : Poly} {u : RankSevenVec} :
    objective B p u = 0 ↔ residual p u = 0 := by
  have hani : B.toQuadraticMap.Anisotropic :=
    (Fact.out : B.toQuadraticMap.PosDef).anisotropic
  constructor
  · intro h
    exact (QuadraticMap.Anisotropic.eq_zero_iff hani).mp (by
      simpa [objective, LinearMap.BilinMap.toQuadraticMap_apply] using h)
  · intro h
    simp [objective, h]

end Positivity

end QuaternaryQuartic
