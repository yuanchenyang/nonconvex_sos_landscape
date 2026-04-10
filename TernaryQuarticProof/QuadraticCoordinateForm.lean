import TernaryQuarticProof.QuadraticNormalForm
import TernaryQuarticProof.MixedAffineNormalization

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace TernaryQuartic

@[simp] theorem m00_ne_m10 : (m00 : Fin 2 →₀ ℕ) ≠ m10 := by
  intro h
  have h0 := congrArg (fun s => s 0) h
  simp [m00, m10] at h0

@[simp] theorem m00_ne_m01 : (m00 : Fin 2 →₀ ℕ) ≠ m01 := by
  intro h
  have h1 := congrArg (fun s => s 1) h
  simp [m00, m01] at h1

@[simp] theorem m00_ne_m20 : (m00 : Fin 2 →₀ ℕ) ≠ m20 := by
  intro h
  have h0 := congrArg (fun s => s 0) h
  simp [m00, m20] at h0

@[simp] theorem m00_ne_m11 : (m00 : Fin 2 →₀ ℕ) ≠ m11 := by
  intro h
  have h0 := congrArg (fun s => s 0) h
  simp [m00, m11] at h0

@[simp] theorem m00_ne_m02 : (m00 : Fin 2 →₀ ℕ) ≠ m02 := by
  intro h
  have h1 := congrArg (fun s => s 1) h
  simp [m00, m02] at h1

@[simp] theorem m10_ne_m01 : (m10 : Fin 2 →₀ ℕ) ≠ m01 := by
  intro h
  have h0 := congrArg (fun s => s 0) h
  simp [m10, m01] at h0

@[simp] theorem m10_ne_m20 : (m10 : Fin 2 →₀ ℕ) ≠ m20 := by
  intro h
  have h0 := congrArg (fun s => s 0) h
  simp [m10, m20] at h0

@[simp] theorem m10_ne_m11 : (m10 : Fin 2 →₀ ℕ) ≠ m11 := by
  intro h
  have h1 := congrArg (fun s => s 1) h
  simp [m10, m11] at h1

@[simp] theorem m10_ne_m02 : (m10 : Fin 2 →₀ ℕ) ≠ m02 := by
  intro h
  have h0 := congrArg (fun s => s 0) h
  simp [m10, m02] at h0

@[simp] theorem m01_ne_m20 : (m01 : Fin 2 →₀ ℕ) ≠ m20 := by
  intro h
  have h0 := congrArg (fun s => s 0) h
  simp [m01, m20] at h0

@[simp] theorem m01_ne_m11 : (m01 : Fin 2 →₀ ℕ) ≠ m11 := by
  intro h
  have h0 := congrArg (fun s => s 0) h
  simp [m01, m11] at h0

@[simp] theorem m01_ne_m02 : (m01 : Fin 2 →₀ ℕ) ≠ m02 := by
  intro h
  have h1 := congrArg (fun s => s 1) h
  simp [m01, m02] at h1

@[simp] theorem m20_ne_m11 : (m20 : Fin 2 →₀ ℕ) ≠ m11 := by
  intro h
  have h1 := congrArg (fun s => s 1) h
  simp [m20, m11] at h1

@[simp] theorem m20_ne_m02 : (m20 : Fin 2 →₀ ℕ) ≠ m02 := by
  intro h
  have h0 := congrArg (fun s => s 0) h
  simp [m20, m02] at h0

@[simp] theorem m11_ne_m02 : (m11 : Fin 2 →₀ ℕ) ≠ m02 := by
  intro h
  have h0 := congrArg (fun s => s 0) h
  simp [m11, m02] at h0

@[simp] theorem m10_ne_m00 : (m10 : Fin 2 →₀ ℕ) ≠ m00 := by
  intro h
  exact m00_ne_m10 h.symm

@[simp] theorem m01_ne_m00 : (m01 : Fin 2 →₀ ℕ) ≠ m00 := by
  intro h
  exact m00_ne_m01 h.symm

@[simp] theorem m20_ne_m00 : (m20 : Fin 2 →₀ ℕ) ≠ m00 := by
  intro h
  exact m00_ne_m20 h.symm

@[simp] theorem m11_ne_m00 : (m11 : Fin 2 →₀ ℕ) ≠ m00 := by
  intro h
  exact m00_ne_m11 h.symm

@[simp] theorem m02_ne_m00 : (m02 : Fin 2 →₀ ℕ) ≠ m00 := by
  intro h
  exact m00_ne_m02 h.symm

@[simp] theorem m01_ne_m10 : (m01 : Fin 2 →₀ ℕ) ≠ m10 := by
  intro h
  exact m10_ne_m01 h.symm

@[simp] theorem m20_ne_m10 : (m20 : Fin 2 →₀ ℕ) ≠ m10 := by
  intro h
  exact m10_ne_m20 h.symm

@[simp] theorem m11_ne_m10 : (m11 : Fin 2 →₀ ℕ) ≠ m10 := by
  intro h
  exact m10_ne_m11 h.symm

@[simp] theorem m02_ne_m10 : (m02 : Fin 2 →₀ ℕ) ≠ m10 := by
  intro h
  exact m10_ne_m02 h.symm

@[simp] theorem m20_ne_m01 : (m20 : Fin 2 →₀ ℕ) ≠ m01 := by
  intro h
  exact m01_ne_m20 h.symm

@[simp] theorem m11_ne_m01 : (m11 : Fin 2 →₀ ℕ) ≠ m01 := by
  intro h
  exact m01_ne_m11 h.symm

@[simp] theorem m02_ne_m01 : (m02 : Fin 2 →₀ ℕ) ≠ m01 := by
  intro h
  exact m01_ne_m02 h.symm

@[simp] theorem m11_ne_m20 : (m11 : Fin 2 →₀ ℕ) ≠ m20 := by
  intro h
  exact m20_ne_m11 h.symm

@[simp] theorem m02_ne_m20 : (m02 : Fin 2 →₀ ℕ) ≠ m20 := by
  intro h
  exact m20_ne_m02 h.symm

@[simp] theorem m02_ne_m11 : (m02 : Fin 2 →₀ ℕ) ≠ m11 := by
  intro h
  exact m11_ne_m02 h.symm

/-- Explicit six-coordinate form for quadratics in `x₀,x₁`. -/
def quadForm (a00 a10 a01 a20 a11 a02 : ℝ) : Poly :=
  MvPolynomial.monomial m00 a00 +
    MvPolynomial.monomial m10 a10 +
    MvPolynomial.monomial m01 a01 +
    MvPolynomial.monomial m20 a20 +
    MvPolynomial.monomial m11 a11 +
    MvPolynomial.monomial m02 a02

theorem quadForm_eq_explicit
    (a00 a10 a01 a20 a11 a02 : ℝ) :
    quadForm a00 a10 a01 a20 a11 a02 =
      MvPolynomial.C a00
        + MvPolynomial.C a10 * x0
        + MvPolynomial.C a01 * x1
        + MvPolynomial.C a20 * x0 ^ 2
        + MvPolynomial.C a11 * (x0 * x1)
        + MvPolynomial.C a02 * x1 ^ 2 := by
  simp [quadForm, m00, m10, m01, m20, m11, m02, x0, x1, pow_two,
    MvPolynomial.monomial_eq]

@[simp] theorem coeff_m00_quadForm
    (a00 a10 a01 a20 a11 a02 : ℝ) :
    MvPolynomial.coeff m00 (quadForm a00 a10 a01 a20 a11 a02) = a00 := by
  simp [quadForm, m00, m10, m01, m20, m11, m02]

@[simp] theorem coeff_m10_quadForm
    (a00 a10 a01 a20 a11 a02 : ℝ) :
    MvPolynomial.coeff m10 (quadForm a00 a10 a01 a20 a11 a02) = a10 := by
  simp [quadForm, m00, m10, m01, m20, m11, m02]

@[simp] theorem coeff_m01_quadForm
    (a00 a10 a01 a20 a11 a02 : ℝ) :
    MvPolynomial.coeff m01 (quadForm a00 a10 a01 a20 a11 a02) = a01 := by
  simp [quadForm, m00, m10, m01, m20, m11, m02]

@[simp] theorem coeff_m20_quadForm
    (a00 a10 a01 a20 a11 a02 : ℝ) :
    MvPolynomial.coeff m20 (quadForm a00 a10 a01 a20 a11 a02) = a20 := by
  simp [quadForm, m00, m10, m01, m20, m11, m02]

@[simp] theorem coeff_m11_quadForm
    (a00 a10 a01 a20 a11 a02 : ℝ) :
    MvPolynomial.coeff m11 (quadForm a00 a10 a01 a20 a11 a02) = a11 := by
  simp [quadForm, m00, m10, m01, m20, m11, m02]

@[simp] theorem coeff_m02_quadForm
    (a00 a10 a01 a20 a11 a02 : ℝ) :
    MvPolynomial.coeff m02 (quadForm a00 a10 a01 a20 a11 a02) = a02 := by
  simp [quadForm, m00, m10, m01, m20, m11, m02]

theorem quadratic_eq_quadForm
    {q : Poly} (hq : IsQuadratic q) :
    q = quadForm
      (MvPolynomial.coeff m00 q)
      (MvPolynomial.coeff m10 q)
      (MvPolynomial.coeff m01 q)
      (MvPolynomial.coeff m20 q)
      (MvPolynomial.coeff m11 q)
      (MvPolynomial.coeff m02 q) := by
  calc
    q = ∑ d ∈ quadSupp, MvPolynomial.monomial d (MvPolynomial.coeff d q) := by
      exact quadratic_sum_formula hq
    _ = quadForm
          (MvPolynomial.coeff m00 q)
          (MvPolynomial.coeff m10 q)
          (MvPolynomial.coeff m01 q)
          (MvPolynomial.coeff m20 q)
          (MvPolynomial.coeff m11 q)
          (MvPolynomial.coeff m02 q) := by
            simp [quadForm, quadSupp, add_left_comm, add_comm]

/-- Translation fixing `x₀` and sending `x₁` to `x₁ + t`. -/
def x1TranslateVec (t : ℝ) : Fin 2 → ℝ := ![0, t]

@[simp] theorem affineHom_x1Translate_x0 (t : ℝ) :
    affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) x0 = x0 := by
  simp [x0, affineImage, affineHom_X, x1TranslateVec, Fin.sum_univ_two]

@[simp] theorem affineHom_x1Translate_x1 (t : ℝ) :
    affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) x1 = MvPolynomial.C t + x1 := by
  simp [x1, affineImage, affineHom_X, x1TranslateVec, Fin.sum_univ_two]

theorem affineHom_x1Translate_quadForm
    (a00 a10 a01 a20 a11 a02 t : ℝ) :
    affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t)
        (quadForm a00 a10 a01 a20 a11 a02) =
      quadForm
        (a00 + a01 * t + a02 * t ^ 2)
        (a10 + a11 * t)
        (a01 + 2 * a02 * t)
        a20
        a11
        a02 := by
  rw [quadForm_eq_explicit, quadForm_eq_explicit]
  simp [affineHom_x1Translate_x0, affineHom_x1Translate_x1]
  ring_nf
  have htwo : (MvPolynomial.C (2 : ℝ) : Poly) = 2 := by
    change (MvPolynomial.C (2 : ℝ) : Poly) = MvPolynomial.C 2
    rfl
  simp [htwo]

theorem affineHom_x1Shear_quadForm
    (a00 a10 a01 a20 a11 a02 t : ℝ) :
    affineHom (x1ShearMatrix t) 0 (quadForm a00 a10 a01 a20 a11 a02) =
      quadForm
        a00
        (a10 + a01 * t)
        a01
        (a20 + a11 * t + a02 * t ^ 2)
        (a11 + 2 * a02 * t)
        a02 := by
  rw [quadForm_eq_explicit, quadForm_eq_explicit]
  simp [affineHom_x1Shear_x0, affineHom_x1Shear_x1]
  ring_nf
  have htwo : (MvPolynomial.C (2 : ℝ) : Poly) = 2 := by
    change (MvPolynomial.C (2 : ℝ) : Poly) = MvPolynomial.C 2
    rfl
  simp [htwo]

theorem affineHom_x1Scale_quadForm
    (a00 a10 a01 a20 a11 a02 s : ℝ) :
    affineHom (x1ScaleMatrix s) 0 (quadForm a00 a10 a01 a20 a11 a02) =
      quadForm
        a00
        a10
        (a01 * s)
        a20
        (a11 * s)
        (a02 * s ^ 2) := by
  rw [quadForm_eq_explicit, quadForm_eq_explicit]
  simp [affineHom_x1Scale_x0, affineHom_x1Scale_x1]
  ring

theorem mixedAffineAnnihilator_eq_quadForm
    (a b c : ℝ) :
    mixedAffineAnnihilator a b c = quadForm 0 0 0 a b c := by
  rw [quadForm_eq_explicit]
  simp [mixedAffineAnnihilator]

end TernaryQuartic
