import TernaryQuarticProof.AffineSocpTransform
import TernaryQuarticProof.RepresentativeSurjective

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace TernaryQuartic

/-- Binary quadratic annihilator for the constant-containing mixed-affine branch. -/
def mixedAffineAnnihilator (a b c : ℝ) : Poly :=
  MvPolynomial.C a * x0 ^ 2 + MvPolynomial.C b * (x0 * x1) + MvPolynomial.C c * x1 ^ 2

/-- Shear fixing `x₀` and sending `x₁` to `t x₀ + x₁`. -/
def x1ShearMatrix (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; t, 1]

/-- Inverse shear fixing `x₀` and sending `x₁` to `-t x₀ + x₁`. -/
def x1ShearInvMatrix (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; -t, 1]

theorem x1Shear_mul_inv (t : ℝ) :
    x1ShearMatrix t * x1ShearInvMatrix t = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [x1ShearMatrix, x1ShearInvMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem x1Shear_inv_mul (t : ℝ) :
    x1ShearInvMatrix t * x1ShearMatrix t = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [x1ShearMatrix, x1ShearInvMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- Scaling fixing `x₀` and sending `x₁` to `s x₁`. -/
def x1ScaleMatrix (s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, s]

/-- Inverse scaling fixing `x₀` and sending `x₁` to `s⁻¹ x₁`. -/
def x1ScaleInvMatrix (s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, s⁻¹]

theorem x1Scale_mul_inv (s : ℝ) (hs : s ≠ 0) :
    x1ScaleMatrix s * x1ScaleInvMatrix s = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [x1ScaleMatrix, x1ScaleInvMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  · field_simp [hs]

theorem x1Scale_inv_mul (s : ℝ) (hs : s ≠ 0) :
    x1ScaleInvMatrix s * x1ScaleMatrix s = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [x1ScaleMatrix, x1ScaleInvMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  · field_simp [hs]

@[simp] theorem affineHom_x1Shear_x0 (t : ℝ) :
    affineHom (x1ShearMatrix t) 0 x0 = x0 := by
  simp [x0, affineImage, affineHom_X, x1ShearMatrix, Fin.sum_univ_two]

@[simp] theorem affineHom_x1Shear_x1 (t : ℝ) :
    affineHom (x1ShearMatrix t) 0 x1 = MvPolynomial.C t * x0 + x1 := by
  simp [x1, x0, affineImage, affineHom_X, x1ShearMatrix, Fin.sum_univ_two]

@[simp] theorem affineHom_x1Scale_x0 (s : ℝ) :
    affineHom (x1ScaleMatrix s) 0 x0 = x0 := by
  simp [x0, affineImage, affineHom_X, x1ScaleMatrix, Fin.sum_univ_two]

@[simp] theorem affineHom_x1Scale_x1 (s : ℝ) :
    affineHom (x1ScaleMatrix s) 0 x1 = MvPolynomial.C s * x1 := by
  simp [x1, affineImage, affineHom_X, x1ScaleMatrix, Fin.sum_univ_two]

theorem affineHom_x1Shear_mixedAffineAnnihilator
    (a b c t : ℝ) :
    affineHom (x1ShearMatrix t) 0 (mixedAffineAnnihilator a b c) =
      mixedAffineAnnihilator (a + b * t + c * t ^ 2) (b + 2 * c * t) c := by
  have hraw :
      affineHom (x1ShearMatrix t) 0 (mixedAffineAnnihilator a b c) =
        mixedAffineAnnihilator (a + b * t + c * t ^ 2) (b + (c + c) * t) c := by
    simp [mixedAffineAnnihilator, affineHom_x1Shear_x0, affineHom_x1Shear_x1]
    ring_nf
  simpa [two_mul] using hraw

theorem affineHom_x1Shear_mixedAffineAnnihilator_cancel_cross
    (a b c : ℝ) (hc : c ≠ 0) :
    affineHom (x1ShearMatrix (-(b / (2 * c)))) 0 (mixedAffineAnnihilator a b c) =
      mixedAffineAnnihilator (a - b ^ 2 / (4 * c)) 0 c := by
  rw [affineHom_x1Shear_mixedAffineAnnihilator]
  have hA :
      a + -(b * (b / (2 * c))) + c * (b / (2 * c)) ^ 2 = a - b ^ 2 / (4 * c) := by
    field_simp [hc]
    ring
  have hB : b + -(2 * c * (b / (2 * c))) = 0 := by
    field_simp [hc]
    ring
  simp [hA, hB]

theorem affineHom_x1Shear_mixedAffineAnnihilator_to_cross
    (a b : ℝ) (hb : b ≠ 0) :
    affineHom (x1ShearMatrix (-(a / b))) 0 (mixedAffineAnnihilator a b 0) =
      mixedAffineAnnihilator 0 b 0 := by
  rw [affineHom_x1Shear_mixedAffineAnnihilator]
  have hA : a + -(b * (a / b)) = 0 := by
    field_simp [hb]
    ring
  simp [hA]

theorem affineHom_x1Scale_mixedAffineAnnihilator
    (a b c s : ℝ) :
    affineHom (x1ScaleMatrix s) 0 (mixedAffineAnnihilator a b c) =
      mixedAffineAnnihilator a (b * s) (c * s ^ 2) := by
  simp [mixedAffineAnnihilator, affineHom_x1Scale_x0, affineHom_x1Scale_x1]
  ring

theorem affineHom_x1Scale_mixedAffineAnnihilator_to_sumsq
    (a c : ℝ) (hpos : 0 < a / c) :
    affineHom (x1ScaleMatrix (Real.sqrt (a / c))) 0 (mixedAffineAnnihilator a 0 c) =
      mixedAffineAnnihilator a 0 a := by
  rw [affineHom_x1Scale_mixedAffineAnnihilator]
  have hc : c ≠ 0 := by
    intro hc
    simp [hc] at hpos
  have hsq : (Real.sqrt (a / c)) ^ 2 = a / c := by
    rw [Real.sq_sqrt]
    exact le_of_lt hpos
  have hC : c * (Real.sqrt (a / c)) ^ 2 = a := by
    rw [hsq]
    field_simp [hc]
  simp [hC]

theorem affineHom_x1Scale_mixedAffineAnnihilator_to_diffsq
    (a c : ℝ) (hpos : 0 < (-a) / c) :
    affineHom (x1ScaleMatrix (Real.sqrt ((-a) / c))) 0 (mixedAffineAnnihilator a 0 c) =
      mixedAffineAnnihilator a 0 (-a) := by
  rw [affineHom_x1Scale_mixedAffineAnnihilator]
  have hc : c ≠ 0 := by
    intro hc
    simp [hc] at hpos
  have hsq : (Real.sqrt ((-a) / c)) ^ 2 = (-a) / c := by
    rw [Real.sq_sqrt]
    exact le_of_lt hpos
  have hC : c * (Real.sqrt ((-a) / c)) ^ 2 = -a := by
    rw [hsq]
    field_simp [hc]
  simp [hC]

theorem affineHom_x1ShearScale_mixedAffineAnnihilator_to_sumsq
    (a b c : ℝ) (hc : c ≠ 0)
    (hpos : 0 < (a - b ^ 2 / (4 * c)) / c) :
    affineHom (x1ScaleMatrix (Real.sqrt ((a - b ^ 2 / (4 * c)) / c))) 0
      (affineHom (x1ShearMatrix (-(b / (2 * c)))) 0 (mixedAffineAnnihilator a b c)) =
        mixedAffineAnnihilator (a - b ^ 2 / (4 * c)) 0 (a - b ^ 2 / (4 * c)) := by
  rw [affineHom_x1Shear_mixedAffineAnnihilator_cancel_cross a b c hc]
  exact affineHom_x1Scale_mixedAffineAnnihilator_to_sumsq
    (a - b ^ 2 / (4 * c)) c hpos

theorem affineHom_x1ShearScale_mixedAffineAnnihilator_to_diffsq
    (a b c : ℝ) (hc : c ≠ 0)
    (hpos : 0 < (-(a - b ^ 2 / (4 * c))) / c) :
    affineHom (x1ScaleMatrix (Real.sqrt ((-(a - b ^ 2 / (4 * c))) / c))) 0
      (affineHom (x1ShearMatrix (-(b / (2 * c)))) 0 (mixedAffineAnnihilator a b c)) =
        mixedAffineAnnihilator (a - b ^ 2 / (4 * c)) 0 (-(a - b ^ 2 / (4 * c))) := by
  rw [affineHom_x1Shear_mixedAffineAnnihilator_cancel_cross a b c hc]
  exact affineHom_x1Scale_mixedAffineAnnihilator_to_diffsq
    (a - b ^ 2 / (4 * c)) c hpos

theorem mixedAffineAnnihilator_normal_form_cases
    (a b c : ℝ) :
    (c = 0 ∧ b = 0 ∧
      mixedAffineAnnihilator a b c = mixedAffineAnnihilator a 0 0) ∨
    (c = 0 ∧ b ≠ 0 ∧
      affineHom (x1ShearMatrix (-(a / b))) 0 (mixedAffineAnnihilator a b c) =
        mixedAffineAnnihilator 0 b 0) ∨
    (c ≠ 0 ∧
      let d := a - b ^ 2 / (4 * c)
      (d = 0 ∧
        affineHom (x1ShearMatrix (-(b / (2 * c)))) 0 (mixedAffineAnnihilator a b c) =
          mixedAffineAnnihilator 0 0 c) ∨
      (0 < d / c ∧
        affineHom (x1ScaleMatrix (Real.sqrt (d / c))) 0
          (affineHom (x1ShearMatrix (-(b / (2 * c)))) 0 (mixedAffineAnnihilator a b c)) =
            mixedAffineAnnihilator d 0 d) ∨
      (0 < (-d) / c ∧
        affineHom (x1ScaleMatrix (Real.sqrt ((-d) / c))) 0
          (affineHom (x1ShearMatrix (-(b / (2 * c)))) 0 (mixedAffineAnnihilator a b c)) =
            mixedAffineAnnihilator d 0 (-d))) := by
  by_cases hc : c = 0
  · by_cases hb : b = 0
    · left
      constructor
      · exact hc
      constructor
      · exact hb
      · simp [mixedAffineAnnihilator, hc, hb]
    · right
      left
      constructor
      · exact hc
      constructor
      · exact hb
      · simpa [hc] using affineHom_x1Shear_mixedAffineAnnihilator_to_cross a b hb
  · right
    right
    constructor
    · exact hc
    let d : ℝ := a - b ^ 2 / (4 * c)
    by_cases hd : d = 0
    · left
      constructor
      · exact hd
      · simpa [d, hd] using affineHom_x1Shear_mixedAffineAnnihilator_cancel_cross a b c hc
    · have hdc0 : d / c ≠ 0 := by
        exact div_ne_zero hd hc
      rcases lt_or_gt_of_ne hdc0 with hneg | hpos
      · right
        right
        have hpos' : 0 < (-d) / c := by
          have hneg' : 0 < -(d / c) := by
            linarith
          simpa [neg_div] using hneg'
        constructor
        · exact hpos'
        · simpa [d] using affineHom_x1ShearScale_mixedAffineAnnihilator_to_diffsq a b c hc hpos'
      · right
        left
        constructor
        · exact hpos
        · simpa [d] using affineHom_x1ShearScale_mixedAffineAnnihilator_to_sumsq a b c hc hpos

/-- Polynomial equivalence induced by the `x₁`-shear preserving `x₀`. -/
def x1ShearEquiv (t : ℝ) : Poly ≃ₐ[ℝ] Poly :=
  affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
    (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp)

/-- Polynomial equivalence induced by the nonzero scaling `x₁ ↦ s x₁`. -/
def x1ScaleEquiv (s : ℝ) (hs : s ≠ 0) : Poly ≃ₐ[ℝ] Poly :=
  affineEquiv (x1ScaleMatrix s) (x1ScaleInvMatrix s) 0 0
    (x1Scale_mul_inv s hs) (x1Scale_inv_mul s hs) (by intro i; simp) (by intro i; simp)

end TernaryQuartic
