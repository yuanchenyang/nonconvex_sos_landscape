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

theorem homogeneousQuadratic_eq
    {q : Poly} (hq : IsQuadratic q)
    (h00 : MvPolynomial.coeff m00 q = 0)
    (h10 : MvPolynomial.coeff m10 q = 0)
    (h01 : MvPolynomial.coeff m01 q = 0) :
    q =
      MvPolynomial.coeff m20 q • (x0 ^ 2 : Poly) +
        MvPolynomial.coeff m11 q • (x0 * x1 : Poly) +
          MvPolynomial.coeff m02 q • (x1 ^ 2 : Poly) := by
  have hx0sq : (x0 ^ 2 : Poly) = MvPolynomial.monomial m20 (1 : ℝ) := by
    simp [x0, m20, MvPolynomial.monomial_eq]
  have hx0x1 : (x0 * x1 : Poly) = MvPolynomial.monomial m11 (1 : ℝ) := by
    simp [x0, x1, m11, MvPolynomial.monomial_eq]
  have hx1sq : (x1 ^ 2 : Poly) = MvPolynomial.monomial m02 (1 : ℝ) := by
    simp [x1, m02, MvPolynomial.monomial_eq]
  have hs20 :
      MvPolynomial.coeff m20 q • (x0 ^ 2 : Poly) =
        MvPolynomial.monomial m20 (MvPolynomial.coeff m20 q) := by
    rw [hx0sq, MvPolynomial.smul_eq_C_mul, MvPolynomial.C_mul_monomial]
    simp
  have hs11 :
      MvPolynomial.coeff m11 q • (x0 * x1 : Poly) =
        MvPolynomial.monomial m11 (MvPolynomial.coeff m11 q) := by
    rw [hx0x1, MvPolynomial.smul_eq_C_mul, MvPolynomial.C_mul_monomial]
    simp
  have hs02 :
      MvPolynomial.coeff m02 q • (x1 ^ 2 : Poly) =
        MvPolynomial.monomial m02 (MvPolynomial.coeff m02 q) := by
    rw [hx1sq, MvPolynomial.smul_eq_C_mul, MvPolynomial.C_mul_monomial]
    simp
  calc
    q = quadForm
          (MvPolynomial.coeff m00 q)
          (MvPolynomial.coeff m10 q)
          (MvPolynomial.coeff m01 q)
          (MvPolynomial.coeff m20 q)
          (MvPolynomial.coeff m11 q)
          (MvPolynomial.coeff m02 q) := quadratic_eq_quadForm hq
    _ =
        MvPolynomial.coeff m20 q • (x0 ^ 2 : Poly) +
          MvPolynomial.coeff m11 q • (x0 * x1 : Poly) +
            MvPolynomial.coeff m02 q • (x1 ^ 2 : Poly) := by
              rw [quadForm]
              rw [h00, h10, h01]
              rw [← hs20, ← hs11, ← hs02]
              simp

theorem homogeneousQuadratic_eq_x0x1_x1sq_of_coeff_m20_zero
    {q : Poly} (hq : IsQuadratic q)
    (h00 : MvPolynomial.coeff m00 q = 0)
    (h10 : MvPolynomial.coeff m10 q = 0)
    (h01 : MvPolynomial.coeff m01 q = 0)
    (h20 : MvPolynomial.coeff m20 q = 0) :
    q =
      MvPolynomial.coeff m11 q • (x0 * x1 : Poly) +
        MvPolynomial.coeff m02 q • (x1 ^ 2 : Poly) := by
  have hbase := homogeneousQuadratic_eq hq h00 h10 h01
  simpa [h20, add_assoc] using hbase

theorem homogeneousQuadratic_eq_x0sq_x0x1_of_coeff_m02_zero
    {q : Poly} (hq : IsQuadratic q)
    (h00 : MvPolynomial.coeff m00 q = 0)
    (h10 : MvPolynomial.coeff m10 q = 0)
    (h01 : MvPolynomial.coeff m01 q = 0)
    (h02 : MvPolynomial.coeff m02 q = 0) :
    q =
      MvPolynomial.coeff m20 q • (x0 ^ 2 : Poly) +
        MvPolynomial.coeff m11 q • (x0 * x1 : Poly) := by
  have hbase := homogeneousQuadratic_eq hq h00 h10 h01
  simpa [h02, add_assoc] using hbase

theorem homogeneousQuadratic_eq_x0sq_x1sq_of_coeff_m11_zero
    {q : Poly} (hq : IsQuadratic q)
    (h00 : MvPolynomial.coeff m00 q = 0)
    (h10 : MvPolynomial.coeff m10 q = 0)
    (h01 : MvPolynomial.coeff m01 q = 0)
    (h11 : MvPolynomial.coeff m11 q = 0) :
    q =
      MvPolynomial.coeff m20 q • (x0 ^ 2 : Poly) +
        MvPolynomial.coeff m02 q • (x1 ^ 2 : Poly) := by
  have hbase := homogeneousQuadratic_eq hq h00 h10 h01
  simpa [h11, add_assoc] using hbase

theorem homogeneousQuadratic_eq_x0x1_diffsq_of_diag_sum_zero
    {q : Poly} (hq : IsQuadratic q)
    (h00 : MvPolynomial.coeff m00 q = 0)
    (h10 : MvPolynomial.coeff m10 q = 0)
    (h01 : MvPolynomial.coeff m01 q = 0)
    (hdiag : MvPolynomial.coeff m20 q + MvPolynomial.coeff m02 q = 0) :
    q =
      MvPolynomial.coeff m11 q • (x0 * x1 : Poly) +
        MvPolynomial.coeff m20 q • (x0 ^ 2 - x1 ^ 2 : Poly) := by
  have h02 : MvPolynomial.coeff m02 q = -MvPolynomial.coeff m20 q := by
    linarith
  have hbase :
      q =
        MvPolynomial.coeff m20 q • (x0 ^ 2 : Poly) +
          MvPolynomial.coeff m11 q • (x0 * x1 : Poly) +
            (-MvPolynomial.coeff m20 q) • (x1 ^ 2 : Poly) := by
    simpa [h02] using homogeneousQuadratic_eq hq h00 h10 h01
  calc
    q =
        MvPolynomial.coeff m20 q • (x0 ^ 2 : Poly) +
          MvPolynomial.coeff m11 q • (x0 * x1 : Poly) +
            (-MvPolynomial.coeff m20 q) • (x1 ^ 2 : Poly) := hbase
    _ =
        MvPolynomial.coeff m11 q • (x0 * x1 : Poly) +
          MvPolynomial.coeff m20 q • (x0 ^ 2 - x1 ^ 2 : Poly) := by
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

theorem homogeneousQuadratic_eq_x0x1_sumsq_of_diag_diff_zero
    {q : Poly} (hq : IsQuadratic q)
    (h00 : MvPolynomial.coeff m00 q = 0)
    (h10 : MvPolynomial.coeff m10 q = 0)
    (h01 : MvPolynomial.coeff m01 q = 0)
    (hdiag : MvPolynomial.coeff m20 q - MvPolynomial.coeff m02 q = 0) :
    q =
      MvPolynomial.coeff m11 q • (x0 * x1 : Poly) +
        MvPolynomial.coeff m20 q • (x0 ^ 2 + x1 ^ 2 : Poly) := by
  have h02 : MvPolynomial.coeff m02 q = MvPolynomial.coeff m20 q := by
    linarith
  have hbase :
      q =
        MvPolynomial.coeff m20 q • (x0 ^ 2 : Poly) +
          MvPolynomial.coeff m11 q • (x0 * x1 : Poly) +
            MvPolynomial.coeff m20 q • (x1 ^ 2 : Poly) := by
    simpa [h02] using homogeneousQuadratic_eq hq h00 h10 h01
  calc
    q =
        MvPolynomial.coeff m20 q • (x0 ^ 2 : Poly) +
          MvPolynomial.coeff m11 q • (x0 * x1 : Poly) +
            MvPolynomial.coeff m20 q • (x1 ^ 2 : Poly) := hbase
    _ =
        MvPolynomial.coeff m11 q • (x0 * x1 : Poly) +
          MvPolynomial.coeff m20 q • (x0 ^ 2 + x1 ^ 2 : Poly) := by
            simp [smul_add, add_assoc, add_left_comm, add_comm]

/-- Canonical homogeneous quadratic extracted from a mixed-affine tail pair by
killing the `x₁` coefficient. -/
def mixedAffineTailHomLine (q2 q3 : Poly) : Poly :=
  MvPolynomial.coeff m01 q3 • q2 - MvPolynomial.coeff m01 q2 • q3

theorem coeff_m00_mixedAffineTailHomLine
    {q2 q3 : Poly} :
    MvPolynomial.coeff m00 (mixedAffineTailHomLine q2 q3) =
      MvPolynomial.coeff m01 q3 * MvPolynomial.coeff m00 q2 -
        MvPolynomial.coeff m01 q2 * MvPolynomial.coeff m00 q3 := by
  simp [mixedAffineTailHomLine, sub_eq_add_neg]

theorem coeff_m10_mixedAffineTailHomLine
    {q2 q3 : Poly} :
    MvPolynomial.coeff m10 (mixedAffineTailHomLine q2 q3) =
      MvPolynomial.coeff m01 q3 * MvPolynomial.coeff m10 q2 -
        MvPolynomial.coeff m01 q2 * MvPolynomial.coeff m10 q3 := by
  simp [mixedAffineTailHomLine, sub_eq_add_neg]

theorem coeff_m01_mixedAffineTailHomLine
    {q2 q3 : Poly} :
    MvPolynomial.coeff m01 (mixedAffineTailHomLine q2 q3) = 0 := by
  simp [mixedAffineTailHomLine, sub_eq_add_neg]
  ring

theorem coeff_m20_mixedAffineTailHomLine
    {q2 q3 : Poly} :
    MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) =
      MvPolynomial.coeff m01 q3 * MvPolynomial.coeff m20 q2 -
        MvPolynomial.coeff m01 q2 * MvPolynomial.coeff m20 q3 := by
  simp [mixedAffineTailHomLine, sub_eq_add_neg]

theorem coeff_m11_mixedAffineTailHomLine
    {q2 q3 : Poly} :
    MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) =
      MvPolynomial.coeff m01 q3 * MvPolynomial.coeff m11 q2 -
        MvPolynomial.coeff m01 q2 * MvPolynomial.coeff m11 q3 := by
  simp [mixedAffineTailHomLine, sub_eq_add_neg]

theorem coeff_m02_mixedAffineTailHomLine
    {q2 q3 : Poly} :
    MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) =
      MvPolynomial.coeff m01 q3 * MvPolynomial.coeff m02 q2 -
        MvPolynomial.coeff m01 q2 * MvPolynomial.coeff m02 q3 := by
  simp [mixedAffineTailHomLine, sub_eq_add_neg]

theorem isQuadratic_mixedAffineTailHomLine
    {q2 q3 : Poly} (hq2 : IsQuadratic q2) (hq3 : IsQuadratic q3) :
    IsQuadratic (mixedAffineTailHomLine q2 q3) := by
  calc
    (mixedAffineTailHomLine q2 q3).totalDegree ≤
        max ((MvPolynomial.coeff m01 q3) • q2).totalDegree
          (((-MvPolynomial.coeff m01 q2)) • q3).totalDegree := by
            simpa [mixedAffineTailHomLine, sub_eq_add_neg] using
              (MvPolynomial.totalDegree_add
                ((MvPolynomial.coeff m01 q3) • q2)
                (((-MvPolynomial.coeff m01 q2)) • q3))
    _ ≤ 2 := by
          exact max_le
            ((MvPolynomial.totalDegree_smul_le (MvPolynomial.coeff m01 q3) q2).trans hq2)
            ((MvPolynomial.totalDegree_smul_le (-MvPolynomial.coeff m01 q2) q3).trans hq3)

theorem homogeneousQuadratic_eq_mixedAffineTailHomLine
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0) :
    mixedAffineTailHomLine q2 q3 =
      (MvPolynomial.coeff m01 q3 * MvPolynomial.coeff m20 q2 -
          MvPolynomial.coeff m01 q2 * MvPolynomial.coeff m20 q3) • (x0 ^ 2 : Poly) +
        (MvPolynomial.coeff m01 q3 * MvPolynomial.coeff m11 q2 -
            MvPolynomial.coeff m01 q2 * MvPolynomial.coeff m11 q3) • (x0 * x1 : Poly) +
          (MvPolynomial.coeff m01 q3 * MvPolynomial.coeff m02 q2 -
              MvPolynomial.coeff m01 q2 * MvPolynomial.coeff m02 q3) • (x1 ^ 2 : Poly) := by
  have hq : IsQuadratic (mixedAffineTailHomLine q2 q3) :=
    isQuadratic_mixedAffineTailHomLine hq2 hq3
  have h00 : MvPolynomial.coeff m00 (mixedAffineTailHomLine q2 q3) = 0 := by
    rw [coeff_m00_mixedAffineTailHomLine, hq2_00, hq3_00]
    ring
  have h10 : MvPolynomial.coeff m10 (mixedAffineTailHomLine q2 q3) = 0 := by
    rw [coeff_m10_mixedAffineTailHomLine, hq2_10, hq3_10]
    ring
  have h01 : MvPolynomial.coeff m01 (mixedAffineTailHomLine q2 q3) = 0 :=
    coeff_m01_mixedAffineTailHomLine
  calc
    mixedAffineTailHomLine q2 q3 =
      MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) • (x0 ^ 2 : Poly) +
        MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) • (x0 * x1 : Poly) +
          MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) • (x1 ^ 2 : Poly) := by
            exact homogeneousQuadratic_eq hq h00 h10 h01
    _ =
      (MvPolynomial.coeff m01 q3 * MvPolynomial.coeff m20 q2 -
          MvPolynomial.coeff m01 q2 * MvPolynomial.coeff m20 q3) • (x0 ^ 2 : Poly) +
        (MvPolynomial.coeff m01 q3 * MvPolynomial.coeff m11 q2 -
            MvPolynomial.coeff m01 q2 * MvPolynomial.coeff m11 q3) • (x0 * x1 : Poly) +
          (MvPolynomial.coeff m01 q3 * MvPolynomial.coeff m02 q2 -
              MvPolynomial.coeff m01 q2 * MvPolynomial.coeff m02 q3) • (x1 ^ 2 : Poly) := by
            rw [coeff_m20_mixedAffineTailHomLine, coeff_m11_mixedAffineTailHomLine,
              coeff_m02_mixedAffineTailHomLine]

/-- Translation fixing `x₁` and sending `x₀` to `x₀ + t`. -/
def x0TranslateVec (t : ℝ) : Fin 2 → ℝ := ![t, 0]

/-- Inverse translation fixing `x₁` and sending `x₀` to `x₀ - t`. -/
def x0TranslateInvVec (t : ℝ) : Fin 2 → ℝ := ![-t, 0]

@[simp] theorem affineHom_x0Translate_x0 (t : ℝ) :
    affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec t) x0 = MvPolynomial.C t + x0 := by
  simp [x0, affineImage, affineHom_X, x0TranslateVec, Fin.sum_univ_two]

@[simp] theorem affineHom_x0Translate_x1 (t : ℝ) :
    affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec t) x1 = x1 := by
  simp [x1, affineImage, affineHom_X, x0TranslateVec, Fin.sum_univ_two]

theorem x0TranslateInv_add_mulVec (t : ℝ) :
    ∀ i, x0TranslateInvVec t i + Matrix.mulVec (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec t) i = 0 := by
  intro i
  rw [Matrix.one_mulVec]
  fin_cases i <;> simp [x0TranslateVec, x0TranslateInvVec]

theorem x0Translate_add_mulVec_inv (t : ℝ) :
    ∀ i, x0TranslateVec t i + Matrix.mulVec (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateInvVec t) i = 0 := by
  intro i
  rw [Matrix.one_mulVec]
  fin_cases i <;> simp [x0TranslateVec, x0TranslateInvVec]

/-- Polynomial equivalence induced by the translation `x₀ ↦ x₀ + t`. -/
def x0TranslateEquiv (t : ℝ) : Poly ≃ₐ[ℝ] Poly :=
  affineEquiv (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 (x0TranslateVec t) (x0TranslateInvVec t)
    (by simp) (by simp) (x0TranslateInv_add_mulVec t) (x0Translate_add_mulVec_inv t)

theorem affineHom_x0Translate_quadForm
    (a00 a10 a01 a20 a11 a02 t : ℝ) :
    affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec t)
        (quadForm a00 a10 a01 a20 a11 a02) =
      quadForm
        (a00 + a10 * t + a20 * t ^ 2)
        (a10 + 2 * a20 * t)
        (a01 + a11 * t)
        a20
        a11
        a02 := by
  rw [quadForm_eq_explicit, quadForm_eq_explicit]
  simp [affineHom_x0Translate_x0, affineHom_x0Translate_x1]
  ring_nf
  have htwo : (MvPolynomial.C (2 : ℝ) : Poly) = 2 := by
    change (MvPolynomial.C (2 : ℝ) : Poly) = MvPolynomial.C 2
    rfl
  simp [htwo]

/-- Translation fixing `x₀` and sending `x₁` to `x₁ + t`. -/
def x1TranslateVec (t : ℝ) : Fin 2 → ℝ := ![0, t]

/-- Inverse translation fixing `x₀` and sending `x₁` to `x₁ - t`. -/
def x1TranslateInvVec (t : ℝ) : Fin 2 → ℝ := ![0, -t]

@[simp] theorem affineHom_x1Translate_x0 (t : ℝ) :
    affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) x0 = x0 := by
  simp [x0, affineImage, affineHom_X, x1TranslateVec, Fin.sum_univ_two]

@[simp] theorem affineHom_x1Translate_x1 (t : ℝ) :
    affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) x1 = MvPolynomial.C t + x1 := by
  simp [x1, affineImage, affineHom_X, x1TranslateVec, Fin.sum_univ_two]

theorem x1TranslateInv_add_mulVec (t : ℝ) :
    ∀ i, x1TranslateInvVec t i + Matrix.mulVec (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) i = 0 := by
  intro i
  rw [Matrix.one_mulVec]
  fin_cases i <;> simp [x1TranslateVec, x1TranslateInvVec]

theorem x1Translate_add_mulVec_inv (t : ℝ) :
    ∀ i, x1TranslateVec t i + Matrix.mulVec (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateInvVec t) i = 0 := by
  intro i
  rw [Matrix.one_mulVec]
  fin_cases i <;> simp [x1TranslateVec, x1TranslateInvVec]

/-- Polynomial equivalence induced by the translation `x₁ ↦ x₁ + t`. -/
def x1TranslateEquiv (t : ℝ) : Poly ≃ₐ[ℝ] Poly :=
  affineEquiv (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 (x1TranslateVec t) (x1TranslateInvVec t)
    (by simp) (by simp) (x1TranslateInv_add_mulVec t) (x1Translate_add_mulVec_inv t)

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

theorem coeff_m01_affineHom_x1Translate
    {q : Poly} (hq : IsQuadratic q) (t : ℝ) :
    MvPolynomial.coeff m01 (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) q) =
      MvPolynomial.coeff m01 q + 2 * MvPolynomial.coeff m02 q * t := by
  rw [quadratic_eq_quadForm hq, affineHom_x1Translate_quadForm]
  simp [mul_comm]

theorem coeff_m00_affineHom_x1Translate
    {q : Poly} (hq : IsQuadratic q) (t : ℝ) :
    MvPolynomial.coeff m00 (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) q) =
      MvPolynomial.coeff m00 q +
        MvPolynomial.coeff m01 q * t +
          MvPolynomial.coeff m02 q * t ^ 2 := by
  rw [quadratic_eq_quadForm hq, affineHom_x1Translate_quadForm]
  simp [mul_comm, add_comm, add_left_comm]

theorem coeff_m10_affineHom_x1Translate
    {q : Poly} (hq : IsQuadratic q) (t : ℝ) :
    MvPolynomial.coeff m10 (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) q) =
      MvPolynomial.coeff m10 q + MvPolynomial.coeff m11 q * t := by
  rw [quadratic_eq_quadForm hq, affineHom_x1Translate_quadForm]
  simp [mul_comm, add_comm, add_left_comm]

theorem coeff_m01_affineHom_x0Translate
    {q : Poly} (hq : IsQuadratic q) (t : ℝ) :
    MvPolynomial.coeff m01 (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec t) q) =
      MvPolynomial.coeff m01 q + MvPolynomial.coeff m11 q * t := by
  rw [quadratic_eq_quadForm hq, affineHom_x0Translate_quadForm]
  simp [mul_comm, add_comm, add_left_comm]

theorem coeff_m02_affineHom_x0Translate
    {q : Poly} (hq : IsQuadratic q) (t : ℝ) :
    MvPolynomial.coeff m02 (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec t) q) =
      MvPolynomial.coeff m02 q := by
  rw [quadratic_eq_quadForm hq, affineHom_x0Translate_quadForm]
  simp

theorem coeff_m11_affineHom_x0Translate
    {q : Poly} (hq : IsQuadratic q) (t : ℝ) :
    MvPolynomial.coeff m11 (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec t) q) =
      MvPolynomial.coeff m11 q := by
  rw [quadratic_eq_quadForm hq, affineHom_x0Translate_quadForm]
  simp

theorem coeff_m00_affineHom_x0Translate
    {q : Poly} (hq : IsQuadratic q) (t : ℝ) :
    MvPolynomial.coeff m00 (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec t) q) =
      MvPolynomial.coeff m00 q +
        MvPolynomial.coeff m10 q * t +
          MvPolynomial.coeff m20 q * t ^ 2 := by
  rw [quadratic_eq_quadForm hq, affineHom_x0Translate_quadForm]
  simp [mul_comm, add_comm, add_left_comm]

theorem coeff_m10_affineHom_x0Translate
    {q : Poly} (hq : IsQuadratic q) (t : ℝ) :
    MvPolynomial.coeff m10 (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec t) q) =
      MvPolynomial.coeff m10 q + 2 * MvPolynomial.coeff m20 q * t := by
  rw [quadratic_eq_quadForm hq, affineHom_x0Translate_quadForm]
  simp [mul_comm, add_comm, add_left_comm]

theorem coeff_m01_affineHom_x1Translate_after_x0Translate
    {q : Poly} (hq : IsQuadratic q) (u v : ℝ) :
    MvPolynomial.coeff m01
        (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec v)
          (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec u) q)) =
      MvPolynomial.coeff m01 q + MvPolynomial.coeff m11 q * u + 2 * MvPolynomial.coeff m02 q * v := by
  rw [coeff_m01_affineHom_x1Translate
    (isQuadratic_affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec u) hq)]
  rw [coeff_m01_affineHom_x0Translate hq, coeff_m02_affineHom_x0Translate hq]

theorem coeff_m10_affineHom_x1Translate_after_x0Translate
    {q : Poly} (hq : IsQuadratic q) (u v : ℝ) :
    MvPolynomial.coeff m10
        (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec v)
          (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec u) q)) =
      MvPolynomial.coeff m10 q +
        2 * MvPolynomial.coeff m20 q * u +
          MvPolynomial.coeff m11 q * v := by
  rw [coeff_m10_affineHom_x1Translate
    (isQuadratic_affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec u) hq)]
  rw [coeff_m10_affineHom_x0Translate hq, coeff_m11_affineHom_x0Translate hq]

theorem coeff_m00_affineHom_x1Translate_after_x0Translate
    {q : Poly} (hq : IsQuadratic q) (u v : ℝ) :
    MvPolynomial.coeff m00
        (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec v)
          (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec u) q)) =
      MvPolynomial.coeff m00 q +
        MvPolynomial.coeff m10 q * u +
          MvPolynomial.coeff m20 q * u ^ 2 +
            (MvPolynomial.coeff m01 q + MvPolynomial.coeff m11 q * u) * v +
              MvPolynomial.coeff m02 q * v ^ 2 := by
  rw [coeff_m00_affineHom_x1Translate
    (isQuadratic_affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec u) hq)]
  rw [coeff_m00_affineHom_x0Translate hq, coeff_m01_affineHom_x0Translate hq,
    coeff_m02_affineHom_x0Translate hq]

theorem coeff_m01_affineHom_x1Translate_after_x0Translate_pair_kill
    {q2 q3 : Poly} (hq2 : IsQuadratic q2) (hq3 : IsQuadratic q3)
    (hdet :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 ≠ 0) :
    let det : ℝ :=
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3
    let u : ℝ :=
      (MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m01 q3 -
        MvPolynomial.coeff m02 q3 * MvPolynomial.coeff m01 q2) / det
    let v : ℝ :=
      (MvPolynomial.coeff m11 q3 * MvPolynomial.coeff m01 q2 -
        MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m01 q3) / (2 * det)
    MvPolynomial.coeff m01
        (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec v)
          (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec u) q2)) = 0 ∧
      MvPolynomial.coeff m01
        (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec v)
          (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec u) q3)) = 0 := by
  dsimp
  constructor
  · rw [coeff_m01_affineHom_x1Translate_after_x0Translate hq2]
    field_simp [hdet, two_ne_zero]
    ring
  · rw [coeff_m01_affineHom_x1Translate_after_x0Translate hq3]
    let det : ℝ :=
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3
    have hdet0 : det ≠ 0 := by
      simpa [det] using hdet
    calc
      MvPolynomial.coeff m01 q3 +
          MvPolynomial.coeff m11 q3 *
            ((MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m01 q3 -
                MvPolynomial.coeff m02 q3 * MvPolynomial.coeff m01 q2) / det) +
        2 * MvPolynomial.coeff m02 q3 *
          ((MvPolynomial.coeff m11 q3 * MvPolynomial.coeff m01 q2 -
              MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m01 q3) / (2 * det))
          =
            MvPolynomial.coeff m01 q3 +
              ((MvPolynomial.coeff m11 q3 * MvPolynomial.coeff m02 q2 -
                  MvPolynomial.coeff m02 q3 * MvPolynomial.coeff m11 q2) *
                MvPolynomial.coeff m01 q3) / det := by
                  field_simp [hdet0, two_ne_zero]
                  ring
      _ = MvPolynomial.coeff m01 q3 + (-det * MvPolynomial.coeff m01 q3) / det := by
            dsimp [det]
            ring
      _ = 0 := by
            field_simp [hdet0]
            ring

theorem coeff_m20_affineHom_x1Translate
    {q : Poly} (hq : IsQuadratic q) (t : ℝ) :
    MvPolynomial.coeff m20 (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) q) =
      MvPolynomial.coeff m20 q := by
  rw [quadratic_eq_quadForm hq, affineHom_x1Translate_quadForm]
  simp

theorem coeff_m11_affineHom_x1Translate
    {q : Poly} (hq : IsQuadratic q) (t : ℝ) :
    MvPolynomial.coeff m11 (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) q) =
      MvPolynomial.coeff m11 q := by
  rw [quadratic_eq_quadForm hq, affineHom_x1Translate_quadForm]
  simp

theorem coeff_m02_affineHom_x1Translate
    {q : Poly} (hq : IsQuadratic q) (t : ℝ) :
    MvPolynomial.coeff m02 (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) q) =
      MvPolynomial.coeff m02 q := by
  rw [quadratic_eq_quadForm hq, affineHom_x1Translate_quadForm]
  simp

theorem coeff_m01_affineHom_x1Translate_kill
    {q : Poly} (hq : IsQuadratic q)
    (h02 : MvPolynomial.coeff m02 q ≠ 0) :
    MvPolynomial.coeff m01
      (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ)
        (x1TranslateVec (-(MvPolynomial.coeff m01 q / (2 * MvPolynomial.coeff m02 q)))) q) = 0 := by
  rw [coeff_m01_affineHom_x1Translate hq]
  field_simp [h02]
  ring

theorem coeff_m20_affineHom_x1Shear
    {q : Poly} (hq : IsQuadratic q) (t : ℝ) :
    MvPolynomial.coeff m20 (affineHom (x1ShearMatrix t) 0 q) =
      MvPolynomial.coeff m20 q + MvPolynomial.coeff m11 q * t + MvPolynomial.coeff m02 q * t ^ 2 := by
  rw [quadratic_eq_quadForm hq, affineHom_x1Shear_quadForm]
  simp [mul_comm]

theorem coeff_m10_affineHom_x1Shear
    {q : Poly} (hq : IsQuadratic q) (t : ℝ) :
    MvPolynomial.coeff m10 (affineHom (x1ShearMatrix t) 0 q) =
      MvPolynomial.coeff m10 q + MvPolynomial.coeff m01 q * t := by
  rw [quadratic_eq_quadForm hq, affineHom_x1Shear_quadForm]
  simp [mul_comm]

theorem coeff_m11_affineHom_x1Shear
    {q : Poly} (hq : IsQuadratic q) (t : ℝ) :
    MvPolynomial.coeff m11 (affineHom (x1ShearMatrix t) 0 q) =
      MvPolynomial.coeff m11 q + 2 * MvPolynomial.coeff m02 q * t := by
  rw [quadratic_eq_quadForm hq, affineHom_x1Shear_quadForm]
  simp [mul_comm]

theorem coeff_m01_affineHom_x1Shear
    {q : Poly} (hq : IsQuadratic q) (t : ℝ) :
    MvPolynomial.coeff m01 (affineHom (x1ShearMatrix t) 0 q) =
      MvPolynomial.coeff m01 q := by
  rw [quadratic_eq_quadForm hq, affineHom_x1Shear_quadForm]
  simp

theorem coeff_m02_affineHom_x1Shear
    {q : Poly} (hq : IsQuadratic q) (t : ℝ) :
    MvPolynomial.coeff m02 (affineHom (x1ShearMatrix t) 0 q) =
      MvPolynomial.coeff m02 q := by
  rw [quadratic_eq_quadForm hq, affineHom_x1Shear_quadForm]
  simp

theorem coeff_m00_affineHom_x1Shear
    {q : Poly} (hq : IsQuadratic q) (t : ℝ) :
    MvPolynomial.coeff m00 (affineHom (x1ShearMatrix t) 0 q) =
      MvPolynomial.coeff m00 q := by
  rw [quadratic_eq_quadForm hq, affineHom_x1Shear_quadForm]
  simp

theorem coeff_m11_affineHom_x1Shear_kill
    {q : Poly} (hq : IsQuadratic q)
    (h02 : MvPolynomial.coeff m02 q ≠ 0) :
    MvPolynomial.coeff m11
      (affineHom (x1ShearMatrix (-(MvPolynomial.coeff m11 q / (2 * MvPolynomial.coeff m02 q)))) 0 q) = 0 := by
  rw [coeff_m11_affineHom_x1Shear hq]
  field_simp [h02]
  ring

theorem coeff_m20_affineHom_x1Shear_cancel_cross
    {q : Poly} (hq : IsQuadratic q)
    (h02 : MvPolynomial.coeff m02 q ≠ 0) :
    MvPolynomial.coeff m20
      (affineHom (x1ShearMatrix (-(MvPolynomial.coeff m11 q / (2 * MvPolynomial.coeff m02 q)))) 0 q) =
        MvPolynomial.coeff m20 q -
          (MvPolynomial.coeff m11 q) ^ 2 / (4 * MvPolynomial.coeff m02 q) := by
  rw [coeff_m20_affineHom_x1Shear hq]
  field_simp [h02]
  ring

theorem coeff_m20_affineHom_x1Shear_to_cross
    {q : Poly} (hq : IsQuadratic q)
    (h02 : MvPolynomial.coeff m02 q = 0)
    (h11 : MvPolynomial.coeff m11 q ≠ 0) :
    MvPolynomial.coeff m20
      (affineHom (x1ShearMatrix (-(MvPolynomial.coeff m20 q / MvPolynomial.coeff m11 q))) 0 q) = 0 := by
  rw [coeff_m20_affineHom_x1Shear hq, h02]
  field_simp [h11]
  ring

theorem coeff_m20_affineHom_x1Scale
    {q : Poly} (hq : IsQuadratic q) (s : ℝ) :
    MvPolynomial.coeff m20 (affineHom (x1ScaleMatrix s) 0 q) =
      MvPolynomial.coeff m20 q := by
  rw [quadratic_eq_quadForm hq, affineHom_x1Scale_quadForm]
  simp

theorem coeff_m10_affineHom_x1Scale
    {q : Poly} (hq : IsQuadratic q) (s : ℝ) :
    MvPolynomial.coeff m10 (affineHom (x1ScaleMatrix s) 0 q) =
      MvPolynomial.coeff m10 q := by
  rw [quadratic_eq_quadForm hq, affineHom_x1Scale_quadForm]
  simp

theorem coeff_m11_affineHom_x1Scale
    {q : Poly} (hq : IsQuadratic q) (s : ℝ) :
    MvPolynomial.coeff m11 (affineHom (x1ScaleMatrix s) 0 q) =
      MvPolynomial.coeff m11 q * s := by
  rw [quadratic_eq_quadForm hq, affineHom_x1Scale_quadForm]
  simp [mul_comm]

theorem coeff_m01_affineHom_x1Scale
    {q : Poly} (hq : IsQuadratic q) (s : ℝ) :
    MvPolynomial.coeff m01 (affineHom (x1ScaleMatrix s) 0 q) =
      MvPolynomial.coeff m01 q * s := by
  rw [quadratic_eq_quadForm hq, affineHom_x1Scale_quadForm]
  simp [mul_comm]

theorem coeff_m02_affineHom_x1Scale
    {q : Poly} (hq : IsQuadratic q) (s : ℝ) :
    MvPolynomial.coeff m02 (affineHom (x1ScaleMatrix s) 0 q) =
      MvPolynomial.coeff m02 q * s ^ 2 := by
  rw [quadratic_eq_quadForm hq, affineHom_x1Scale_quadForm]
  simp [mul_comm]

theorem coeff_m00_affineHom_x1Scale
    {q : Poly} (hq : IsQuadratic q) (s : ℝ) :
    MvPolynomial.coeff m00 (affineHom (x1ScaleMatrix s) 0 q) =
      MvPolynomial.coeff m00 q := by
  rw [quadratic_eq_quadForm hq, affineHom_x1Scale_quadForm]
  simp

theorem coeff_relation_affineHom_x1Shear_dual
    {q : Poly} (hq : IsQuadratic q)
    {a b c : ℝ}
    (hrel :
      a * MvPolynomial.coeff m20 q +
        b * MvPolynomial.coeff m11 q +
          c * MvPolynomial.coeff m02 q = 0)
    (t : ℝ) :
    a * MvPolynomial.coeff m20 (affineHom (x1ShearMatrix t) 0 q) +
      (b - a * t) * MvPolynomial.coeff m11 (affineHom (x1ShearMatrix t) 0 q) +
        (a * t ^ 2 - 2 * b * t + c) * MvPolynomial.coeff m02 (affineHom (x1ShearMatrix t) 0 q) = 0 := by
  rw [coeff_m20_affineHom_x1Shear hq, coeff_m11_affineHom_x1Shear hq,
    coeff_m02_affineHom_x1Shear hq]
  linarith

theorem coeff_relation_affineHom_x1Shear_dual_kill_cross
    {q : Poly} (hq : IsQuadratic q)
    {a b c : ℝ}
    (ha : a ≠ 0)
    (hrel :
      a * MvPolynomial.coeff m20 q +
        b * MvPolynomial.coeff m11 q +
          c * MvPolynomial.coeff m02 q = 0) :
    a * MvPolynomial.coeff m20 (affineHom (x1ShearMatrix (b / a)) 0 q) +
      (c - b ^ 2 / a) * MvPolynomial.coeff m02 (affineHom (x1ShearMatrix (b / a)) 0 q) = 0 := by
  rw [coeff_m20_affineHom_x1Shear hq, coeff_m02_affineHom_x1Shear hq]
  have hrel' := hrel
  field_simp [ha]
  ring_nf
  have hmul : a * (a * MvPolynomial.coeff m20 q + b * MvPolynomial.coeff m11 q +
      c * MvPolynomial.coeff m02 q) = 0 := by
    rw [hrel]
    ring
  ring_nf at hmul
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

theorem coeff_m11_affineHom_x1Shear_dual_to_cross
    {q : Poly} (hq : IsQuadratic q)
    {b c : ℝ}
    (hb : b ≠ 0)
    (hrel :
      b * MvPolynomial.coeff m11 q +
        c * MvPolynomial.coeff m02 q = 0) :
    MvPolynomial.coeff m11 (affineHom (x1ShearMatrix (c / (2 * b))) 0 q) = 0 := by
  rw [coeff_m11_affineHom_x1Shear hq]
  have hrel' := hrel
  field_simp [hb] at hrel'
  field_simp [hb]
  ring_nf
  nlinarith

theorem coeff_relation_affineHom_x1Scale_diag_sum_zero
    {q : Poly} (hq : IsQuadratic q)
    {a d : ℝ}
    (ha : a ≠ 0)
    (hrel :
      a * MvPolynomial.coeff m20 q +
        d * MvPolynomial.coeff m02 q = 0)
    (hpos : 0 < d / a) :
    MvPolynomial.coeff m20
        (affineHom (x1ScaleMatrix (Real.sqrt (d / a))) 0 q) +
      MvPolynomial.coeff m02
        (affineHom (x1ScaleMatrix (Real.sqrt (d / a))) 0 q) = 0 := by
  rw [coeff_m20_affineHom_x1Scale hq, coeff_m02_affineHom_x1Scale hq]
  have hs : (Real.sqrt (d / a)) ^ 2 = d / a := by
    rw [Real.sq_sqrt]
    exact le_of_lt hpos
  rw [hs]
  field_simp [ha]
  linarith

theorem coeff_relation_affineHom_x1Scale_diag_diff_zero
    {q : Poly} (hq : IsQuadratic q)
    {a d : ℝ}
    (ha : a ≠ 0)
    (hrel :
      a * MvPolynomial.coeff m20 q +
        d * MvPolynomial.coeff m02 q = 0)
    (hpos : 0 < (-d) / a) :
    MvPolynomial.coeff m20
        (affineHom (x1ScaleMatrix (Real.sqrt ((-d) / a))) 0 q) -
      MvPolynomial.coeff m02
        (affineHom (x1ScaleMatrix (Real.sqrt ((-d) / a))) 0 q) = 0 := by
  rw [coeff_m20_affineHom_x1Scale hq, coeff_m02_affineHom_x1Scale hq]
  have hs : (Real.sqrt ((-d) / a)) ^ 2 = (-d) / a := by
    rw [Real.sq_sqrt]
    exact le_of_lt hpos
  rw [hs]
  field_simp [ha]
  linarith

end TernaryQuartic
