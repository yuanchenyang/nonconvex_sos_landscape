import TernaryQuarticProof.RepresentativeSpanThree
import TernaryQuarticProof.RepresentativeMixedAffinePlane
import TernaryQuarticProof.RepresentativeLowAffine
import TernaryQuarticProof.RepresentativeAffineRankOne
import TernaryQuarticProof.QuadraticCoordinateForm

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace TernaryQuartic

open scoped BigOperators

private theorem affineHom_translate_affineLine_left
    (r0 r1 : ℝ) :
    affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] (affineLinePoly r0 1 0) = x0 := by
  simp [affineLinePoly, affineHom, affineImage, x0, x1, Fin.sum_univ_two]

private theorem affineHom_translate_affineLine_right
    (r0 r1 : ℝ) :
    affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] (affineLinePoly r1 0 1) = x1 := by
  simp [affineLinePoly, affineHom, affineImage, x0, x1, Fin.sum_univ_two]

private theorem isQuadratic_linearCombination_local
    {p q : Poly} (hp : IsQuadratic p) (hq : IsQuadratic q) (a b : ℝ) :
    IsQuadratic (a • p + b • q) := by
  calc
    (a • p + b • q).totalDegree ≤ max (a • p).totalDegree (b • q).totalDegree := by
      exact MvPolynomial.totalDegree_add _ _
    _ ≤ 2 := by
      exact max_le
        ((MvPolynomial.totalDegree_smul_le a p).trans hp)
        ((MvPolynomial.totalDegree_smul_le b q).trans hq)

private theorem isQuadratic_one_local : IsQuadratic (1 : Poly) := by
  change ((1 : Poly).totalDegree ≤ 2)
  simp

private theorem isQuadratic_x0_local : IsQuadratic x0 := by
  change (x0 : Poly).totalDegree ≤ 2
  simp [x0]

private theorem isQuadratic_x1_local : IsQuadratic x1 := by
  change (x1 : Poly).totalDegree ≤ 2
  simp [x1]

private theorem isQuadratic_affineLinePoly_local (r a b : ℝ) :
    IsQuadratic (affineLinePoly r a b) := by
  have hconst : IsQuadratic (r • (1 : Poly)) := by
    exact (MvPolynomial.totalDegree_smul_le r (1 : Poly)).trans isQuadratic_one_local
  have hx0 : IsQuadratic (a • x0) := by
    exact (MvPolynomial.totalDegree_smul_le a x0).trans isQuadratic_x0_local
  have hx1 : IsQuadratic (b • x1) := by
    exact (MvPolynomial.totalDegree_smul_le b x1).trans isQuadratic_x1_local
  simpa [affineLinePoly, MvPolynomial.smul_eq_C_mul, add_assoc, add_left_comm, add_comm] using
    isQuadratic_linearCombination_local
      (isQuadratic_linearCombination_local hconst hx0 1 1)
      hx1 1 1

/-- Homogeneous quadratic coefficients of a scalar relation. -/
def homCoeffMap (u : RankFourVec) :
    (Fin 4 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun c := ![
    MvPolynomial.coeff m20 (relationPoly u c),
    MvPolynomial.coeff m11 (relationPoly u c),
    MvPolynomial.coeff m02 (relationPoly u c)]
  map_add' c d := by
    ext j
    fin_cases j <;> simp [relationPoly_add, MvPolynomial.coeff_add]
  map_smul' a c := by
    ext j
    fin_cases j <;> simp [relationPoly_smul, MvPolynomial.coeff_smul]

/-- Affine coefficients of a scalar relation. -/
def affineCoeffMap (u : RankFourVec) :
    (Fin 4 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun c := ![
    MvPolynomial.coeff m00 (relationPoly u c),
    MvPolynomial.coeff m10 (relationPoly u c),
    MvPolynomial.coeff m01 (relationPoly u c)]
  map_add' c d := by
    ext j
    fin_cases j <;> simp [relationPoly_add, MvPolynomial.coeff_add]
  map_smul' a c := by
    ext j
    fin_cases j <;> simp [relationPoly_smul, MvPolynomial.coeff_smul]

/-- The exact affine relations inside the rank-4 span are the kernel of the
homogeneous coefficient map. -/
def exactAffineSubmodule (u : RankFourVec) : Submodule ℝ (Fin 4 → ℝ) :=
  LinearMap.ker (homCoeffMap u)

/-- Linear coefficients of a scalar relation. -/
def linearCoeffMap (u : RankFourVec) :
    (Fin 4 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun c := ![
    MvPolynomial.coeff m10 (relationPoly u c),
    MvPolynomial.coeff m01 (relationPoly u c)]
  map_add' c d := by
    ext j
    fin_cases j <;> simp [relationPoly_add, MvPolynomial.coeff_add]
  map_smul' a c := by
    ext j
    fin_cases j <;> simp [relationPoly_smul, MvPolynomial.coeff_smul]

/-- The `x₀`-linear coefficient of a scalar relation. -/
private def x0CoeffMap (u : RankFourVec) : (Fin 4 → ℝ) →ₗ[ℝ] ℝ where
  toFun c := MvPolynomial.coeff m10 (relationPoly u c)
  map_add' c d := by
    simp [relationPoly_add, MvPolynomial.coeff_add]
  map_smul' a c := by
    simp [relationPoly_smul, MvPolynomial.coeff_smul]

/-- The constant coefficient of a scalar relation. -/
private def constCoeffMap (u : RankFourVec) : (Fin 4 → ℝ) →ₗ[ℝ] ℝ where
  toFun c := MvPolynomial.coeff m00 (relationPoly u c)
  map_add' c d := by
    simp [relationPoly_add, MvPolynomial.coeff_add]
  map_smul' a c := by
    simp [relationPoly_smul, MvPolynomial.coeff_smul]

/-- Constant and `x₁` tail coefficients inside the kernel of the `x₀`-coefficient
map. -/
private def x0TailCoeffMap (u : RankFourVec) :
    (LinearMap.ker (x0CoeffMap u)) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun c := ![
    MvPolynomial.coeff m00 (relationPoly u (c : Fin 4 → ℝ)),
    MvPolynomial.coeff m01 (relationPoly u (c : Fin 4 → ℝ))]
  map_add' c d := by
    ext j
    fin_cases j <;> simp [relationPoly_add, MvPolynomial.coeff_add]
  map_smul' a c := by
    ext j
    fin_cases j <;> simp [relationPoly_smul, MvPolynomial.coeff_smul]

private theorem coeff_m10_x0sq : MvPolynomial.coeff m10 (x0 ^ 2 : Poly) = 0 := by
  rw [x0, MvPolynomial.coeff_X_pow]
  have h : Finsupp.single 0 2 ≠ m10 := by
    intro hs
    have h0 := congrArg (fun s : Fin 2 →₀ ℕ => s 0) hs
    simp [m10] at h0
  simp [h]

private theorem coeff_m10_one : MvPolynomial.coeff m10 (1 : Poly) = 0 := by
  rw [MvPolynomial.coeff_one]
  have h : (0 : Fin 2 →₀ ℕ) ≠ m10 := by
    intro hs
    have h0 := congrArg (fun s : Fin 2 →₀ ℕ => s 0) hs
    simp [m10] at h0
  simp [h]

private theorem coeff_m20_one : MvPolynomial.coeff m20 (1 : Poly) = 0 := by
  rw [MvPolynomial.coeff_one]
  have h : (0 : Fin 2 →₀ ℕ) ≠ m20 := by
    intro hs
    have h0 := congrArg (fun s : Fin 2 →₀ ℕ => s 0) hs
    simp [m20] at h0
  simp [h]

private theorem coeff_m11_one : MvPolynomial.coeff m11 (1 : Poly) = 0 := by
  rw [MvPolynomial.coeff_one]
  have h : (0 : Fin 2 →₀ ℕ) ≠ m11 := by
    intro hs
    have h0 := congrArg (fun s : Fin 2 →₀ ℕ => s 0) hs
    simp [m11] at h0
  simp [h]

private theorem coeff_m02_one : MvPolynomial.coeff m02 (1 : Poly) = 0 := by
  rw [MvPolynomial.coeff_one]
  have h : (0 : Fin 2 →₀ ℕ) ≠ m02 := by
    intro hs
    have h1 := congrArg (fun s : Fin 2 →₀ ℕ => s 1) hs
    simp [m02] at h1
  simp [h]

private theorem coeff_m00_x0sq : MvPolynomial.coeff m00 (x0 ^ 2 : Poly) = 0 := by
  rw [x0, MvPolynomial.coeff_X_pow]
  have h : Finsupp.single 0 2 ≠ m00 := by
    intro hs
    have h0 := congrArg (fun s : Fin 2 →₀ ℕ => s 0) hs
    simp [m00] at h0
  simp [h]

private theorem coeff_m01_x0sq : MvPolynomial.coeff m01 (x0 ^ 2 : Poly) = 0 := by
  rw [x0, MvPolynomial.coeff_X_pow]
  have h : Finsupp.single 0 2 ≠ m01 := by
    intro hs
    have h1 := congrArg (fun s : Fin 2 →₀ ℕ => s 1) hs
    simp [m01] at h1
  simp [h]

private theorem coeff_m20_x0sq : MvPolynomial.coeff m20 (x0 ^ 2 : Poly) = 1 := by
  rw [x0, MvPolynomial.coeff_X_pow]
  simp [m20]

private theorem coeff_m11_x0sq : MvPolynomial.coeff m11 (x0 ^ 2 : Poly) = 0 := by
  rw [x0, MvPolynomial.coeff_X_pow]
  have h : Finsupp.single 0 2 ≠ m11 := by
    intro hs
    have h1 := congrArg (fun s : Fin 2 →₀ ℕ => s 1) hs
    simp [m11] at h1
  simp [h]

private theorem coeff_m02_x0sq : MvPolynomial.coeff m02 (x0 ^ 2 : Poly) = 0 := by
  rw [x0, MvPolynomial.coeff_X_pow]
  have h : Finsupp.single 0 2 ≠ m02 := by
    intro hs
    have h1 := congrArg (fun s : Fin 2 →₀ ℕ => s 1) hs
    simp [m02] at h1
  simp [h]

private theorem coeff_m01_one : MvPolynomial.coeff m01 (1 : Poly) = 0 := by
  rw [MvPolynomial.coeff_one]
  have h : (0 : Fin 2 →₀ ℕ) ≠ m01 := by
    intro hs
    have h1 := congrArg (fun s : Fin 2 →₀ ℕ => s 1) hs
    simp [m01] at h1
  simp [h]

private theorem coeff_m20_x0 : MvPolynomial.coeff m20 (x0 : Poly) = 0 := by
  rw [x0, MvPolynomial.coeff_X']
  have h : (Finsupp.single 0 1 : Fin 2 →₀ ℕ) ≠ m20 := by
    intro hs
    have h0 := congrArg (fun s : Fin 2 →₀ ℕ => s 0) hs
    simp [m20] at h0
  simp [h]

private theorem coeff_m11_x0 : MvPolynomial.coeff m11 (x0 : Poly) = 0 := by
  rw [x0, MvPolynomial.coeff_X']
  have h : (Finsupp.single 0 1 : Fin 2 →₀ ℕ) ≠ m11 := by
    intro hs
    have h1 := congrArg (fun s : Fin 2 →₀ ℕ => s 1) hs
    simp [m11] at h1
  simp [h]

private theorem coeff_m02_x0 : MvPolynomial.coeff m02 (x0 : Poly) = 0 := by
  rw [x0, MvPolynomial.coeff_X']
  have h : (Finsupp.single 0 1 : Fin 2 →₀ ℕ) ≠ m02 := by
    intro hs
    have h1 := congrArg (fun s : Fin 2 →₀ ℕ => s 1) hs
    simp [m02] at h1
  simp [h]

private theorem coeff_m10_x0x1 : MvPolynomial.coeff m10 (x0 * x1 : Poly) = 0 := by
  have hmon : (x0 * x1 : Poly) = MvPolynomial.monomial m11 (1 : ℝ) := by
    simp [x0, x1, m11, MvPolynomial.monomial_eq]
  rw [hmon]
  simp [m10, m11]

private theorem coeff_m00_x0x1 : MvPolynomial.coeff m00 (x0 * x1 : Poly) = 0 := by
  have hmon : (x0 * x1 : Poly) = MvPolynomial.monomial m11 (1 : ℝ) := by
    simp [x0, x1, m11, MvPolynomial.monomial_eq]
  rw [hmon]
  simp [m00, m11]

private theorem coeff_m01_x0x1 : MvPolynomial.coeff m01 (x0 * x1 : Poly) = 0 := by
  have hmon : (x0 * x1 : Poly) = MvPolynomial.monomial m11 (1 : ℝ) := by
    simp [x0, x1, m11, MvPolynomial.monomial_eq]
  rw [hmon]
  simp [m01, m11]

private theorem coeff_m11_x0x1 : MvPolynomial.coeff m11 (x0 * x1 : Poly) = 1 := by
  have hmon : (x0 * x1 : Poly) = MvPolynomial.monomial m11 (1 : ℝ) := by
    simp [x0, x1, m11, MvPolynomial.monomial_eq]
  rw [hmon]
  simp [m11]

private theorem coeff_m02_x0x1 : MvPolynomial.coeff m02 (x0 * x1 : Poly) = 0 := by
  have hmon : (x0 * x1 : Poly) = MvPolynomial.monomial m11 (1 : ℝ) := by
    simp [x0, x1, m11, MvPolynomial.monomial_eq]
  rw [hmon]
  simp [m02, m11]

private theorem coeff_m20_x0x1 : MvPolynomial.coeff m20 (x0 * x1 : Poly) = 0 := by
  have hmon : (x0 * x1 : Poly) = MvPolynomial.monomial m11 (1 : ℝ) := by
    simp [x0, x1, m11, MvPolynomial.monomial_eq]
  rw [hmon]
  simp [m20, m11]

private theorem coeff_m10_x1sq : MvPolynomial.coeff m10 (x1 ^ 2 : Poly) = 0 := by
  rw [x1, MvPolynomial.coeff_X_pow]
  have h : Finsupp.single 1 2 ≠ m10 := by
    intro hs
    have h0 := congrArg (fun s : Fin 2 →₀ ℕ => s 0) hs
    simp [m10] at h0
  simp [h]

private theorem coeff_m10_x1 : MvPolynomial.coeff m10 (x1 : Poly) = 0 := by
  simp [x1, m10]

private theorem coeff_m20_x1 : MvPolynomial.coeff m20 (x1 : Poly) = 0 := by
  rw [x1, MvPolynomial.coeff_X']
  have h : (Finsupp.single 1 1 : Fin 2 →₀ ℕ) ≠ m20 := by
    intro hs
    have h0 := congrArg (fun s : Fin 2 →₀ ℕ => s 0) hs
    simp [m20] at h0
  simp [h]

private theorem coeff_m00_x1sq : MvPolynomial.coeff m00 (x1 ^ 2 : Poly) = 0 := by
  rw [x1, MvPolynomial.coeff_X_pow]
  have h : Finsupp.single 1 2 ≠ m00 := by
    intro hs
    have h1 := congrArg (fun s : Fin 2 →₀ ℕ => s 1) hs
    simp [m00] at h1
  simp [h]

private theorem coeff_m00_x1 : MvPolynomial.coeff m00 (x1 : Poly) = 0 := by
  simp [x1, m00]

private theorem coeff_m01_x1sq : MvPolynomial.coeff m01 (x1 ^ 2 : Poly) = 0 := by
  rw [x1, MvPolynomial.coeff_X_pow]
  have h : Finsupp.single 1 2 ≠ m01 := by
    intro hs
    have h1 := congrArg (fun s : Fin 2 →₀ ℕ => s 1) hs
    simp [m01] at h1
  simp [h]

private theorem coeff_m02_x1sq : MvPolynomial.coeff m02 (x1 ^ 2 : Poly) = 1 := by
  rw [x1, MvPolynomial.coeff_X_pow]
  simp [m02]

private theorem coeff_m11_x1sq : MvPolynomial.coeff m11 (x1 ^ 2 : Poly) = 0 := by
  rw [x1, MvPolynomial.coeff_X_pow]
  have h : Finsupp.single 1 2 ≠ m11 := by
    intro hs
    have h0 := congrArg (fun s : Fin 2 →₀ ℕ => s 0) hs
    simp [m11] at h0
  simp [h]

private theorem coeff_m20_x1sq : MvPolynomial.coeff m20 (x1 ^ 2 : Poly) = 0 := by
  rw [x1, MvPolynomial.coeff_X_pow]
  have h : Finsupp.single 1 2 ≠ m20 := by
    intro hs
    have h0 := congrArg (fun s : Fin 2 →₀ ℕ => s 0) hs
    simp [m20] at h0
  simp [h]

private theorem coeff_m01_x1 : MvPolynomial.coeff m01 (x1 : Poly) = 1 := by
  simp [x1, m01]

private theorem coeff_m11_x1 : MvPolynomial.coeff m11 (x1 : Poly) = 0 := by
  rw [x1, MvPolynomial.coeff_X']
  have h : (Finsupp.single 1 1 : Fin 2 →₀ ℕ) ≠ m11 := by
    intro hs
    have h0 := congrArg (fun s : Fin 2 →₀ ℕ => s 0) hs
    simp [m11] at h0
  simp [h]

private theorem coeff_m02_x1 : MvPolynomial.coeff m02 (x1 : Poly) = 0 := by
  rw [x1, MvPolynomial.coeff_X']
  have h : (Finsupp.single 1 1 : Fin 2 →₀ ℕ) ≠ m02 := by
    intro hs
    have h1 := congrArg (fun s : Fin 2 →₀ ℕ => s 1) hs
    simp [m02] at h1
  simp [h]

private theorem relationPoly_eq_affine_of_mem_exactAffineSubmodule
    {u : RankFourVec} (hu : IsAdmissiblePoint u) {c : Fin 4 → ℝ}
    (hc : c ∈ exactAffineSubmodule u) :
    relationPoly u c =
      MvPolynomial.coeff m00 (relationPoly u c) • (1 : Poly) +
        MvPolynomial.coeff m10 (relationPoly u c) • x0 +
          MvPolynomial.coeff m01 (relationPoly u c) • x1 := by
  have hq : IsQuadratic (relationPoly u c) := isQuadratic_relationPoly hu c
  have h20 : MvPolynomial.coeff m20 (relationPoly u c) = 0 := by
    have h := congrArg (fun z : Fin 3 → ℝ => z 0) hc
    simpa [exactAffineSubmodule, homCoeffMap] using h
  have h11 : MvPolynomial.coeff m11 (relationPoly u c) = 0 := by
    have h := congrArg (fun z : Fin 3 → ℝ => z 1) hc
    simpa [exactAffineSubmodule, homCoeffMap] using h
  have h02 : MvPolynomial.coeff m02 (relationPoly u c) = 0 := by
    have h := congrArg (fun z : Fin 3 → ℝ => z 2) hc
    simpa [exactAffineSubmodule, homCoeffMap] using h
  calc
    relationPoly u c =
      quadForm
        (MvPolynomial.coeff m00 (relationPoly u c))
        (MvPolynomial.coeff m10 (relationPoly u c))
        (MvPolynomial.coeff m01 (relationPoly u c))
        (MvPolynomial.coeff m20 (relationPoly u c))
        (MvPolynomial.coeff m11 (relationPoly u c))
        (MvPolynomial.coeff m02 (relationPoly u c)) := by
          exact quadratic_eq_quadForm hq
    _ =
      MvPolynomial.coeff m00 (relationPoly u c) • (1 : Poly) +
        MvPolynomial.coeff m10 (relationPoly u c) • x0 +
          MvPolynomial.coeff m01 (relationPoly u c) • x1 := by
            rw [quadForm_eq_explicit, h20, h11, h02]
            simp [MvPolynomial.smul_eq_C_mul, add_assoc]

private theorem relationPoly_zero_of_affineCoeff_zero
    {u : RankFourVec} (hu : IsAdmissiblePoint u) {c : Fin 4 → ℝ}
    (hc : c ∈ exactAffineSubmodule u)
    (hAff : affineCoeffMap u c = 0) :
    relationPoly u c = 0 := by
  rw [relationPoly_eq_affine_of_mem_exactAffineSubmodule hu hc]
  have h00 := congrArg (fun z : Fin 3 → ℝ => z 0) hAff
  have h10 := congrArg (fun z : Fin 3 → ℝ => z 1) hAff
  have h01 := congrArg (fun z : Fin 3 → ℝ => z 2) hAff
  simp [affineCoeffMap] at h00 h10 h01
  simp [h00, h10, h01]

private theorem exactAffineCoeffMap_injective
    {u : RankFourVec} (hu : IsAdmissiblePoint u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥) :
    Function.Injective
      ((affineCoeffMap u).comp (exactAffineSubmodule u).subtype) := by
  intro x y hxy
  have hxmem : ((x : exactAffineSubmodule u) : Fin 4 → ℝ) ∈ exactAffineSubmodule u := x.2
  have hymem : ((y : exactAffineSubmodule u) : Fin 4 → ℝ) ∈ exactAffineSubmodule u := y.2
  have hsubmem :
      (((x : exactAffineSubmodule u) : Fin 4 → ℝ) -
          ((y : exactAffineSubmodule u) : Fin 4 → ℝ)) ∈ exactAffineSubmodule u := by
    exact Submodule.sub_mem _ hxmem hymem
  have hAffZero :
      affineCoeffMap u
        (((x : exactAffineSubmodule u) : Fin 4 → ℝ) -
          ((y : exactAffineSubmodule u) : Fin 4 → ℝ)) = 0 := by
    have hxy0 :
        ((affineCoeffMap u).comp (exactAffineSubmodule u).subtype) x -
            ((affineCoeffMap u).comp (exactAffineSubmodule u).subtype) y = 0 := by
      exact sub_eq_zero.mpr hxy
    simpa [LinearMap.comp_apply, LinearMap.sub_apply] using hxy0
  have hpolyzero :
      relationPoly u
        (((x : exactAffineSubmodule u) : Fin 4 → ℝ) -
          ((y : exactAffineSubmodule u) : Fin 4 → ℝ)) = 0 := by
    exact relationPoly_zero_of_affineCoeff_zero hu hsubmem hAffZero
  have hlinzero :
      relationPolyLin u
        (((x : exactAffineSubmodule u) : Fin 4 → ℝ) -
          ((y : exactAffineSubmodule u) : Fin 4 → ℝ)) = 0 := by
    simpa [relationPolyLin] using hpolyzero
  have hrelInj : Function.Injective (relationPolyLin u) := LinearMap.ker_eq_bot.mp hrelker
  have hsubzero :
      (((x : exactAffineSubmodule u) : Fin 4 → ℝ) -
          ((y : exactAffineSubmodule u) : Fin 4 → ℝ)) = 0 := by
    exact hrelInj <| by simpa using hlinzero
  apply Subtype.ext
  exact sub_eq_zero.mp hsubzero

private theorem exactAffineLinearCoeffMap_injective_of_noConst
    {u : RankFourVec} (hu : IsAdmissiblePoint u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hnoConst : ¬ ∃ c ∈ exactAffineSubmodule u, relationPoly u c = (1 : Poly)) :
    Function.Injective
      ((linearCoeffMap u).comp (exactAffineSubmodule u).subtype) := by
  intro x y hxy
  let z : exactAffineSubmodule u := ⟨(x : Fin 4 → ℝ) - (y : Fin 4 → ℝ),
    Submodule.sub_mem _ x.2 y.2⟩
  have hzlin :
      ((linearCoeffMap u).comp (exactAffineSubmodule u).subtype) z = 0 := by
    have hsub :
        ((linearCoeffMap u).comp (exactAffineSubmodule u).subtype) x -
            ((linearCoeffMap u).comp (exactAffineSubmodule u).subtype) y = 0 := by
      exact sub_eq_zero.mpr hxy
    simpa [z, LinearMap.comp_apply, LinearMap.sub_apply] using hsub
  have hzAff :
      relationPoly u (z : Fin 4 → ℝ) =
        MvPolynomial.coeff m00 (relationPoly u (z : Fin 4 → ℝ)) • (1 : Poly) := by
    have hAff := relationPoly_eq_affine_of_mem_exactAffineSubmodule hu z.2
    have hz10 := congrArg (fun v : Fin 2 → ℝ => v 0) hzlin
    have hz01 := congrArg (fun v : Fin 2 → ℝ => v 1) hzlin
    rw [hAff]
    simp [linearCoeffMap] at hz10 hz01
    simp [hz10, hz01]
  let a : ℝ := MvPolynomial.coeff m00 (relationPoly u (z : Fin 4 → ℝ))
  by_cases ha : a = 0
  · have hzzero : relationPoly u (z : Fin 4 → ℝ) = 0 := by
      simpa [a, ha] using hzAff
    have hrelInj : Function.Injective (relationPolyLin u) := LinearMap.ker_eq_bot.mp hrelker
    have hzvec :
        ((z : exactAffineSubmodule u) : Fin 4 → ℝ) = 0 := by
      apply hrelInj
      simpa [relationPolyLin, relationPoly] using hzzero
    have hsub :
        ((x : exactAffineSubmodule u) : Fin 4 → ℝ) -
            ((y : exactAffineSubmodule u) : Fin 4 → ℝ) = 0 := by
      simpa [z] using hzvec
    apply Subtype.ext
    exact sub_eq_zero.mp hsub
  · have hzAff' : relationPoly u (z : Fin 4 → ℝ) = a • (1 : Poly) := by
      simpa [a] using hzAff
    have hzone :
      relationPoly u ((a⁻¹) • (z : Fin 4 → ℝ)) = (1 : Poly) := by
      calc
        relationPoly u ((a⁻¹) • (z : Fin 4 → ℝ)) = a⁻¹ • relationPoly u (z : Fin 4 → ℝ) := by
          simp [relationPoly_smul]
        _ = a⁻¹ • (a • (1 : Poly)) := by
          rw [hzAff']
        _ = (a⁻¹ * a) • (1 : Poly) := by rw [smul_smul]
        _ = (1 : ℝ) • (1 : Poly) := by
          congr 1
          field_simp [ha]
        _ = (1 : Poly) := by simp
    have hzmem : (a⁻¹) • (z : Fin 4 → ℝ) ∈ exactAffineSubmodule u := by
      exact Submodule.smul_mem _ _ z.2
    exact False.elim <| hnoConst ⟨(a⁻¹) • (z : Fin 4 → ℝ), hzmem, hzone⟩

private theorem relationPoly_eq_one_of_exactAffineCoeff_e0
    {u : RankFourVec} (hu : IsAdmissiblePoint u) {c : exactAffineSubmodule u}
    (hc : ((affineCoeffMap u).comp (exactAffineSubmodule u).subtype) c = ![1, 0, 0]) :
    relationPoly u (c : Fin 4 → ℝ) = (1 : Poly) := by
  have hAff0 := congrArg (fun z : Fin 3 → ℝ => z 0) hc
  have hAff1 := congrArg (fun z : Fin 3 → ℝ => z 1) hc
  have hAff2 := congrArg (fun z : Fin 3 → ℝ => z 2) hc
  rw [relationPoly_eq_affine_of_mem_exactAffineSubmodule hu c.2]
  simp [affineCoeffMap] at hAff0 hAff1 hAff2
  simp [hAff0, hAff1, hAff2]

private theorem relationPoly_eq_x0_of_exactAffineCoeff_e1
    {u : RankFourVec} (hu : IsAdmissiblePoint u) {c : exactAffineSubmodule u}
    (hc : ((affineCoeffMap u).comp (exactAffineSubmodule u).subtype) c = ![0, 1, 0]) :
    relationPoly u (c : Fin 4 → ℝ) = x0 := by
  have hAff0 := congrArg (fun z : Fin 3 → ℝ => z 0) hc
  have hAff1 := congrArg (fun z : Fin 3 → ℝ => z 1) hc
  have hAff2 := congrArg (fun z : Fin 3 → ℝ => z 2) hc
  rw [relationPoly_eq_affine_of_mem_exactAffineSubmodule hu c.2]
  simp [affineCoeffMap] at hAff0 hAff1 hAff2
  simp [hAff0, hAff1, hAff2]

private theorem relationPoly_eq_x1_of_exactAffineCoeff_e2
    {u : RankFourVec} (hu : IsAdmissiblePoint u) {c : exactAffineSubmodule u}
    (hc : ((affineCoeffMap u).comp (exactAffineSubmodule u).subtype) c = ![0, 0, 1]) :
    relationPoly u (c : Fin 4 → ℝ) = x1 := by
  have hAff0 := congrArg (fun z : Fin 3 → ℝ => z 0) hc
  have hAff1 := congrArg (fun z : Fin 3 → ℝ => z 1) hc
  have hAff2 := congrArg (fun z : Fin 3 → ℝ => z 2) hc
  rw [relationPoly_eq_affine_of_mem_exactAffineSubmodule hu c.2]
  simp [affineCoeffMap] at hAff0 hAff1 hAff2
  simp [hAff0, hAff1, hAff2]

/-- If the exact affine relations inside `span(u)` already have dimension three,
then `1`, `x₀`, and `x₁` lie in the span, so the span-three certificate closes
the SOCP branch. -/
theorem residual_eq_zero_of_exactAffineDimThree
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 3)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let affExact : exactAffineSubmodule u →ₗ[ℝ] (Fin 3 → ℝ) :=
    (affineCoeffMap u).comp (exactAffineSubmodule u).subtype
  have hAffInj : Function.Injective affExact :=
    exactAffineCoeffMap_injective hu hrelker
  have hfin : Module.finrank ℝ (exactAffineSubmodule u) = Module.finrank ℝ (Fin 3 → ℝ) := by
    rw [hdim, Module.finrank_fintype_fun_eq_card]
    decide
  have hAffSurj : Function.Surjective affExact :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hAffInj
  obtain ⟨c0, hc0⟩ := hAffSurj ![1, 0, 0]
  obtain ⟨c1, hc1⟩ := hAffSurj ![0, 1, 0]
  obtain ⟨c2, hc2⟩ := hAffSurj ![0, 0, 1]
  have h0 : ∑ i : Fin 4, (c0 : Fin 4 → ℝ) i • u i = (1 : Poly) := by
    simpa [relationPoly] using relationPoly_eq_one_of_exactAffineCoeff_e0 hu hc0
  have h1 : ∑ i : Fin 4, (c1 : Fin 4 → ℝ) i • u i = x0 := by
    simpa [relationPoly] using relationPoly_eq_x0_of_exactAffineCoeff_e1 hu hc1
  have h2 : ∑ i : Fin 4, (c2 : Fin 4 → ℝ) i • u i = x1 := by
    simpa [relationPoly] using relationPoly_eq_x1_of_exactAffineCoeff_e2 hu hc2
  exact residual_eq_zero_of_contains_aff1
    (B := B) (u := u) (c0 := c0) (c1 := c1) (c2 := c2) hu h0 h1 h2 hp hsocp

/-- If the exact affine relation space has dimension two and contains `1`,
then there is a second independent exact affine line. The mixed-affine coarse
certificate closes this whole branch directly. -/
theorem residual_eq_zero_of_exactAffineDimTwo_contains_one
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 2)
    {c0 : Fin 4 → ℝ}
    (hc0 : c0 ∈ exactAffineSubmodule u)
    (h0 : relationPoly u c0 = (1 : Poly))
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let affExact : exactAffineSubmodule u →ₗ[ℝ] (Fin 3 → ℝ) :=
    (affineCoeffMap u).comp (exactAffineSubmodule u).subtype
  have hAffInj : Function.Injective affExact :=
    exactAffineCoeffMap_injective hu hrelker
  have hkerAff : LinearMap.ker affExact = ⊥ := LinearMap.ker_eq_bot.mpr hAffInj
  have hrangeDim : Module.finrank ℝ (LinearMap.range affExact) = 2 := by
    have hsum := LinearMap.finrank_range_add_finrank_ker affExact
    rw [hkerAff, finrank_bot, add_zero] at hsum
    simpa [hdim] using hsum
  have hc0' : affExact ⟨c0, hc0⟩ = ![1, 0, 0] := by
    ext j
    fin_cases j
    · have hm00 := congrArg (MvPolynomial.coeff m00) h0
      simpa [affExact, affineCoeffMap, relationPoly] using hm00
    · have hm10 := congrArg (MvPolynomial.coeff m10) h0
      simpa [affExact, affineCoeffMap, relationPoly, x0, MvPolynomial.coeff_one] using hm10
    · have hm01 := congrArg (MvPolynomial.coeff m01) h0
      simpa [affExact, affineCoeffMap, relationPoly, x1, MvPolynomial.coeff_one] using hm01
  have hspan_le : Submodule.span ℝ ({![1, 0, 0]} : Set (Fin 3 → ℝ)) ≤ LinearMap.range affExact := by
    refine Submodule.span_le.2 ?_
    intro v hv
    rcases Set.mem_singleton_iff.mp hv with rfl
    exact ⟨⟨c0, hc0⟩, hc0'⟩
  have hrange_ne_span :
      LinearMap.range affExact ≠ Submodule.span ℝ ({![1, 0, 0]} : Set (Fin 3 → ℝ)) := by
    intro hEq
    have hfin1 :
        Module.finrank ℝ (Submodule.span ℝ ({![1, 0, 0]} : Set (Fin 3 → ℝ))) = 1 := by
      rw [finrank_span_singleton]
      intro hzero
      have hcoord := congrArg (fun z : Fin 3 → ℝ => z 0) hzero
      simp at hcoord
    rw [hEq, hfin1] at hrangeDim
    norm_num at hrangeDim
  have hnotAll :
      ¬ ∀ v ∈ LinearMap.range affExact,
          v ∈ Submodule.span ℝ ({![1, 0, 0]} : Set (Fin 3 → ℝ)) := by
    intro hall
    have hle :
        LinearMap.range affExact ≤ Submodule.span ℝ ({![1, 0, 0]} : Set (Fin 3 → ℝ)) := by
      intro v hv
      exact hall v hv
    exact hrange_ne_span (le_antisymm hle hspan_le)
  rcases not_forall.mp hnotAll with ⟨v, hv⟩
  rcases not_forall.mp hv with ⟨hvRange, hvNotSpan⟩
  rcases hvRange with ⟨c1, hc1⟩
  let r : ℝ := v 0
  let a : ℝ := v 1
  let b : ℝ := v 2
  have h1 :
      relationPoly u (c1 : Fin 4 → ℝ) = affineLinePoly r a b := by
    have hAff :
        relationPoly u (c1 : Fin 4 → ℝ) =
          MvPolynomial.coeff m00 (relationPoly u (c1 : Fin 4 → ℝ)) • (1 : Poly) +
            MvPolynomial.coeff m10 (relationPoly u (c1 : Fin 4 → ℝ)) • x0 +
              MvPolynomial.coeff m01 (relationPoly u (c1 : Fin 4 → ℝ)) • x1 := by
      exact relationPoly_eq_affine_of_mem_exactAffineSubmodule hu c1.2
    have hc10 := congrArg (fun z : Fin 3 → ℝ => z 0) hc1
    have hc11 := congrArg (fun z : Fin 3 → ℝ => z 1) hc1
    have hc12 := congrArg (fun z : Fin 3 → ℝ => z 2) hc1
    rw [hAff]
    simp [affExact, affineCoeffMap] at hc10 hc11 hc12
    simp [affineLinePoly, r, a, b, hc10, hc11, hc12, MvPolynomial.smul_eq_C_mul, add_assoc]
  have hs : a ^ 2 + b ^ 2 ≠ 0 := by
    intro hab
    have ha0 : a = 0 := by
      nlinarith
    have hb0 : b = 0 := by
      nlinarith
    have hvSpan :
        v ∈ Submodule.span ℝ ({![1, 0, 0]} : Set (Fin 3 → ℝ)) := by
      have hvEq : v = r • ![1, 0, 0] := by
        ext j
        fin_cases j <;> simp [r, a, b, ha0, hb0]
      rw [hvEq]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    exact hvNotSpan hvSpan
  exact residual_eq_zero_of_relations_const_affineLine
    (B := B) (u := u) (c0 := c0) (c1 := c1)
    hu (by simpa [relationPoly] using h0) (by simpa [relationPoly] using h1) hs hp hsocp

/-- If the exact affine relation space has dimension one and contains `1`, then
the zero-constant relations supply a full homogeneous quadratic basis with only
linear tails. The surjective-image certificate closes this branch directly. -/
theorem residual_eq_zero_of_exactAffineDimOne_contains_one
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (_hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 1)
    {c0 : Fin 4 → ℝ}
    (hc0 : c0 ∈ exactAffineSubmodule u)
    (h0 : relationPoly u c0 = (1 : Poly))
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have hc0ne : c0 ≠ 0 := by
    intro hc0zero
    have hcoeff := congrArg (MvPolynomial.coeff m00) h0
    simp [relationPoly, hc0zero] at hcoeff
  let c0E : exactAffineSubmodule u := ⟨c0, hc0⟩
  have hc0E_ne : c0E ≠ 0 := by
    intro hc0E
    exact hc0ne (Subtype.ext_iff.mp hc0E)
  let K : Submodule ℝ (Fin 4 → ℝ) := LinearMap.ker (constCoeffMap u)
  have hsurjConst : Function.Surjective (constCoeffMap u) := by
    intro t
    refine ⟨t • c0, ?_⟩
    have hc000 : constCoeffMap u c0 = 1 := by
      simpa [constCoeffMap] using congrArg (MvPolynomial.coeff m00) h0
    rw [LinearMap.map_smul, hc000]
    simp
  have hrangeTopConst : LinearMap.range (constCoeffMap u) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurjConst
  have hdom4 : Module.finrank ℝ (Fin 4 → ℝ) = 4 := by
    calc
      Module.finrank ℝ (Fin 4 → ℝ) = Fintype.card (Fin 4) :=
        Module.finrank_fintype_fun_eq_card (R := ℝ) (η := Fin 4)
      _ = 4 := by decide
  have hrangeConst : Module.finrank ℝ (LinearMap.range (constCoeffMap u)) = 1 := by
    rw [hrangeTopConst, finrank_top]
    simp
  have hKdim : Module.finrank ℝ K = 3 := by
    have hsum := LinearMap.finrank_range_add_finrank_ker (constCoeffMap u)
    have hsum' : 1 + Module.finrank ℝ K = 4 := by
      simpa [K, hrangeConst, hdom4] using hsum
    omega
  let homK : K →ₗ[ℝ] (Fin 3 → ℝ) := (homCoeffMap u).comp K.subtype
  have hhomKBot : LinearMap.ker homK = ⊥ := by
    ext x
    constructor
    · intro hx
      rw [Submodule.mem_bot]
      have hxHom : homCoeffMap u ((x : K) : Fin 4 → ℝ) = 0 := by
        simpa [homK] using hx
      have hxAff : ((x : K) : Fin 4 → ℝ) ∈ exactAffineSubmodule u := by
        simpa [exactAffineSubmodule] using hxHom
      obtain ⟨t, ht⟩ :=
        exists_smul_eq_of_finrank_eq_one hdim hc0E_ne ⟨((x : K) : Fin 4 → ℝ), hxAff⟩
      have htvec : t • c0 = ((x : K) : Fin 4 → ℝ) := by
        simpa using congrArg Subtype.val ht
      have hc000 : constCoeffMap u c0 = 1 := by
        simpa [constCoeffMap] using congrArg (MvPolynomial.coeff m00) h0
      have hxconstzero : constCoeffMap u ((x : K) : Fin 4 → ℝ) = 0 := by
        change ((x : K) : Fin 4 → ℝ) ∈ LinearMap.ker (constCoeffMap u)
        exact (x : K).2
      have htzero : t = 0 := by
        have htcoeff :
            constCoeffMap u (t • c0) = constCoeffMap u ((x : K) : Fin 4 → ℝ) := by
          exact congrArg (constCoeffMap u) htvec
        rw [LinearMap.map_smul, hc000] at htcoeff
        simp [hxconstzero] at htcoeff
        exact htcoeff
      apply Subtype.ext
      calc
        ((x : K) : Fin 4 → ℝ) = t • c0 := by simpa using htvec.symm
        _ = 0 := by simp [htzero]
    · intro hx
      rw [Submodule.mem_bot] at hx
      subst x
      simp [homK]
  have hhomKinj : Function.Injective homK := LinearMap.ker_eq_bot.mp hhomKBot
  have hrangeHomK : Module.finrank ℝ (LinearMap.range homK) = 3 := by
    simpa [hKdim] using LinearMap.finrank_range_of_inj hhomKinj
  have hcodom3 : Module.finrank ℝ (Fin 3 → ℝ) = 3 := by
    calc
      Module.finrank ℝ (Fin 3 → ℝ) = Fintype.card (Fin 3) :=
        Module.finrank_fintype_fun_eq_card (R := ℝ) (η := Fin 3)
      _ = 3 := by decide
  have hrangeTopHomK : LinearMap.range homK = ⊤ := by
    have hEq :
        Module.finrank ℝ (LinearMap.range homK) = Module.finrank ℝ (Fin 3 → ℝ) := by
      calc
        Module.finrank ℝ (LinearMap.range homK) = 3 := hrangeHomK
        _ = Module.finrank ℝ (Fin 3 → ℝ) := hcodom3.symm
    exact Submodule.eq_top_of_finrank_eq hEq
  obtain ⟨d20K, hd20K⟩ := LinearMap.range_eq_top.mp hrangeTopHomK ![1, 0, 0]
  obtain ⟨d11K, hd11K⟩ := LinearMap.range_eq_top.mp hrangeTopHomK ![0, 1, 0]
  obtain ⟨d02K, hd02K⟩ := LinearMap.range_eq_top.mp hrangeTopHomK ![0, 0, 1]
  let q20 : Poly := relationPoly u (d20K : Fin 4 → ℝ)
  let q11 : Poly := relationPoly u (d11K : Fin 4 → ℝ)
  let q02 : Poly := relationPoly u (d02K : Fin 4 → ℝ)
  let a20 : ℝ := MvPolynomial.coeff m10 q20
  let b20 : ℝ := MvPolynomial.coeff m01 q20
  let a11 : ℝ := MvPolynomial.coeff m10 q11
  let b11 : ℝ := MvPolynomial.coeff m01 q11
  let a02 : ℝ := MvPolynomial.coeff m10 q02
  let b02 : ℝ := MvPolynomial.coeff m01 q02
  have hq20 : IsQuadratic q20 := isQuadratic_relationPoly hu (d20K : Fin 4 → ℝ)
  have hq11 : IsQuadratic q11 := isQuadratic_relationPoly hu (d11K : Fin 4 → ℝ)
  have hq02 : IsQuadratic q02 := isQuadratic_relationPoly hu (d02K : Fin 4 → ℝ)
  have h20_00 : MvPolynomial.coeff m00 q20 = 0 := by
    change constCoeffMap u ((d20K : K) : Fin 4 → ℝ) = 0
    exact d20K.2
  have h20_20 : MvPolynomial.coeff m20 q20 = 1 := by
    have h := congrArg (fun z : Fin 3 → ℝ => z 0) hd20K
    simpa [homK, q20] using h
  have h20_11 : MvPolynomial.coeff m11 q20 = 0 := by
    have h := congrArg (fun z : Fin 3 → ℝ => z 1) hd20K
    simpa [homK, q20] using h
  have h20_02 : MvPolynomial.coeff m02 q20 = 0 := by
    have h := congrArg (fun z : Fin 3 → ℝ => z 2) hd20K
    simpa [homK, q20] using h
  have h11_00 : MvPolynomial.coeff m00 q11 = 0 := by
    change constCoeffMap u ((d11K : K) : Fin 4 → ℝ) = 0
    exact d11K.2
  have h11_20 : MvPolynomial.coeff m20 q11 = 0 := by
    have h := congrArg (fun z : Fin 3 → ℝ => z 0) hd11K
    simpa [homK, q11] using h
  have h11_11 : MvPolynomial.coeff m11 q11 = 1 := by
    have h := congrArg (fun z : Fin 3 → ℝ => z 1) hd11K
    simpa [homK, q11] using h
  have h11_02 : MvPolynomial.coeff m02 q11 = 0 := by
    have h := congrArg (fun z : Fin 3 → ℝ => z 2) hd11K
    simpa [homK, q11] using h
  have h02_00 : MvPolynomial.coeff m00 q02 = 0 := by
    change constCoeffMap u ((d02K : K) : Fin 4 → ℝ) = 0
    exact d02K.2
  have h02_20 : MvPolynomial.coeff m20 q02 = 0 := by
    have h := congrArg (fun z : Fin 3 → ℝ => z 0) hd02K
    simpa [homK, q02] using h
  have h02_11 : MvPolynomial.coeff m11 q02 = 0 := by
    have h := congrArg (fun z : Fin 3 → ℝ => z 1) hd02K
    simpa [homK, q02] using h
  have h02_02 : MvPolynomial.coeff m02 q02 = 1 := by
    have h := congrArg (fun z : Fin 3 → ℝ => z 2) hd02K
    simpa [homK, q02] using h
  have h20 :
      relationPoly u (d20K : Fin 4 → ℝ) = a20 • x0 + b20 • x1 + x0 ^ 2 := by
    calc
      relationPoly u (d20K : Fin 4 → ℝ)
          =
            quadForm
              (MvPolynomial.coeff m00 q20)
              (MvPolynomial.coeff m10 q20)
              (MvPolynomial.coeff m01 q20)
              (MvPolynomial.coeff m20 q20)
              (MvPolynomial.coeff m11 q20)
              (MvPolynomial.coeff m02 q20) := by
                exact quadratic_eq_quadForm hq20
      _ = a20 • x0 + b20 • x1 + x0 ^ 2 := by
            rw [quadForm_eq_explicit, h20_00, h20_20, h20_11, h20_02]
            simp [a20, b20, x0, x1, MvPolynomial.smul_eq_C_mul]
  have h11 :
      relationPoly u (d11K : Fin 4 → ℝ) = a11 • x0 + b11 • x1 + (x0 * x1 : Poly) := by
    calc
      relationPoly u (d11K : Fin 4 → ℝ)
          =
            quadForm
              (MvPolynomial.coeff m00 q11)
              (MvPolynomial.coeff m10 q11)
              (MvPolynomial.coeff m01 q11)
              (MvPolynomial.coeff m20 q11)
              (MvPolynomial.coeff m11 q11)
              (MvPolynomial.coeff m02 q11) := by
                exact quadratic_eq_quadForm hq11
      _ = a11 • x0 + b11 • x1 + (x0 * x1 : Poly) := by
            rw [quadForm_eq_explicit, h11_00, h11_20, h11_11, h11_02]
            simp [a11, b11, x0, x1, MvPolynomial.smul_eq_C_mul]
  have h02 :
      relationPoly u (d02K : Fin 4 → ℝ) = a02 • x0 + b02 • x1 + x1 ^ 2 := by
    calc
      relationPoly u (d02K : Fin 4 → ℝ)
          =
            quadForm
              (MvPolynomial.coeff m00 q02)
              (MvPolynomial.coeff m10 q02)
              (MvPolynomial.coeff m01 q02)
              (MvPolynomial.coeff m20 q02)
              (MvPolynomial.coeff m11 q02)
              (MvPolynomial.coeff m02 q02) := by
                exact quadratic_eq_quadForm hq02
      _ = a02 • x0 + b02 • x1 + x1 ^ 2 := by
            rw [quadForm_eq_explicit, h02_00, h02_20, h02_11, h02_02]
            simp [a02, b02, x0, x1, MvPolynomial.smul_eq_C_mul]
  exact residual_eq_zero_of_relations_const_affineTail_x0sq_affineTail_x0x1_affineTail_x1sq
    (B := B) (u := u) hu
    (by simpa [relationPoly] using h0)
    (by simpa [relationPoly] using h20)
    (by simpa [relationPoly] using h11)
    (by simpa [relationPoly] using h02)
    hp hsocp

/-- If the exact affine relation space has dimension two and contains no exact
constant relation, then it canonically supplies an affine pair with linear
coefficients `(1,0)` and `(0,1)`. -/
theorem exists_exactAffine_affinePair_of_dimTwo_noConst
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 2)
    (hnoConst : ¬ ∃ c ∈ exactAffineSubmodule u, relationPoly u c = (1 : Poly)) :
    ∃ c0 c1 : Fin 4 → ℝ, ∃ r0 r1 : ℝ,
      c0 ∈ exactAffineSubmodule u ∧
      c1 ∈ exactAffineSubmodule u ∧
      relationPoly u c0 = affineLinePoly r0 1 0 ∧
      relationPoly u c1 = affineLinePoly r1 0 1 := by
  let linExact : exactAffineSubmodule u →ₗ[ℝ] (Fin 2 → ℝ) :=
    (linearCoeffMap u).comp (exactAffineSubmodule u).subtype
  have hLinInj : Function.Injective linExact :=
    exactAffineLinearCoeffMap_injective_of_noConst hu hrelker hnoConst
  have hfin :
      Module.finrank ℝ (exactAffineSubmodule u) =
        Module.finrank ℝ (Fin 2 → ℝ) := by
    rw [hdim, Module.finrank_fintype_fun_eq_card]
    decide
  have hLinSurj : Function.Surjective linExact :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hLinInj
  obtain ⟨c0, hc0⟩ := hLinSurj ![1, 0]
  obtain ⟨c1, hc1⟩ := hLinSurj ![0, 1]
  let r0 : ℝ := MvPolynomial.coeff m00 (relationPoly u (c0 : Fin 4 → ℝ))
  let r1 : ℝ := MvPolynomial.coeff m00 (relationPoly u (c1 : Fin 4 → ℝ))
  refine ⟨c0, c1, r0, r1, c0.2, c1.2, ?_, ?_⟩
  · have hAff :
        relationPoly u (c0 : Fin 4 → ℝ) =
          MvPolynomial.coeff m00 (relationPoly u (c0 : Fin 4 → ℝ)) • (1 : Poly) +
            MvPolynomial.coeff m10 (relationPoly u (c0 : Fin 4 → ℝ)) • x0 +
              MvPolynomial.coeff m01 (relationPoly u (c0 : Fin 4 → ℝ)) • x1 := by
      exact relationPoly_eq_affine_of_mem_exactAffineSubmodule hu c0.2
    have hc10 := congrArg (fun z : Fin 2 → ℝ => z 0) hc0
    have hc11 := congrArg (fun z : Fin 2 → ℝ => z 1) hc0
    rw [hAff]
    simp [linExact, linearCoeffMap] at hc10 hc11
    simp [affineLinePoly, r0, hc10, hc11, MvPolynomial.smul_eq_C_mul]
  · have hAff :
        relationPoly u (c1 : Fin 4 → ℝ) =
          MvPolynomial.coeff m00 (relationPoly u (c1 : Fin 4 → ℝ)) • (1 : Poly) +
            MvPolynomial.coeff m10 (relationPoly u (c1 : Fin 4 → ℝ)) • x0 +
              MvPolynomial.coeff m01 (relationPoly u (c1 : Fin 4 → ℝ)) • x1 := by
      exact relationPoly_eq_affine_of_mem_exactAffineSubmodule hu c1.2
    have hc10 := congrArg (fun z : Fin 2 → ℝ => z 0) hc1
    have hc11 := congrArg (fun z : Fin 2 → ℝ => z 1) hc1
    rw [hAff]
    simp [linExact, linearCoeffMap] at hc10 hc11
    simp [affineLinePoly, r1, hc10, hc11, MvPolynomial.smul_eq_C_mul]

/-- After translating an affine pair `x₀ + r₀`, `x₁ + r₁` to `(x₀,x₁)`, the
resulting linear coefficient map is surjective. -/
theorem translatedLinearCoeffMap_surjective_of_affinePair
    {u : RankFourVec}
    {c0 c1 : Fin 4 → ℝ}
    {r0 r1 : ℝ}
    (h0 : relationPoly u c0 = affineLinePoly r0 1 0)
    (h1 : relationPoly u c1 = affineLinePoly r1 0 1) :
    Function.Surjective
      (linearCoeffMap
        (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u)) := by
  intro v
  let c : Fin 4 → ℝ := fun i => v 0 * c0 i + v 1 * c1 i
  refine ⟨c, ?_⟩
  have hc :
      c = v 0 • c0 + v 1 • c1 := by
    funext i
    simp [c]
  have h0' :
      relationPoly
        (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) c0 = x0 := by
    rw [relationPoly_map]
    rw [h0]
    exact affineHom_translate_affineLine_left r0 r1
  have h1' :
      relationPoly
        (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) c1 = x1 := by
    rw [relationPoly_map]
    rw [h1]
    exact affineHom_translate_affineLine_right r0 r1
  have hrel :
      relationPoly
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) c =
        v 0 • x0 + v 1 • x1 := by
    rw [hc, relationPoly_add, relationPoly_smul, relationPoly_smul, h0', h1']
  ext j
  fin_cases j
  · have hm10 := congrArg (MvPolynomial.coeff m10) hrel
    simpa [linearCoeffMap, x0, x1, MvPolynomial.coeff_add, MvPolynomial.coeff_smul] using hm10
  · have hm01 := congrArg (MvPolynomial.coeff m01) hrel
    simpa [linearCoeffMap, x0, x1, MvPolynomial.coeff_add, MvPolynomial.coeff_smul] using hm01

/-- The translated linear coefficient map above an affine pair has a
two-dimensional kernel. -/
theorem translatedLinearCoeffKernel_finrank_two_of_affinePair
    {u : RankFourVec}
    {c0 c1 : Fin 4 → ℝ}
    {r0 r1 : ℝ}
    (h0 : relationPoly u c0 = affineLinePoly r0 1 0)
    (h1 : relationPoly u c1 = affineLinePoly r1 0 1) :
    Module.finrank ℝ
      (LinearMap.ker
        (linearCoeffMap
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u))) = 2 := by
  let f :=
    linearCoeffMap
      (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u)
  have hsurj : Function.Surjective f :=
    translatedLinearCoeffMap_surjective_of_affinePair h0 h1
  have hrange : LinearMap.range f = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hdom : Module.finrank ℝ (Fin 4 → ℝ) = 4 := by
    calc
      Module.finrank ℝ (Fin 4 → ℝ) = Fintype.card (Fin 4) :=
        Module.finrank_fintype_fun_eq_card (R := ℝ) (η := Fin 4)
      _ = 4 := by decide
  have hrangeFin : Module.finrank ℝ (LinearMap.range f) = 2 := by
    rw [hrange, finrank_top]
    calc
      Module.finrank ℝ (Fin 2 → ℝ) = Fintype.card (Fin 2) :=
        Module.finrank_fintype_fun_eq_card (R := ℝ) (η := Fin 2)
      _ = 2 := by decide
  have hsum := LinearMap.finrank_range_add_finrank_ker f
  have hsum' : 2 + Module.finrank ℝ (LinearMap.ker f) = 4 := by
    simpa [hrangeFin, hdom] using hsum
  have hker : Module.finrank ℝ (LinearMap.ker f) = 2 := by
    omega
  exact hker

/-- If an affine pair is known exactly and every relation in the translated
zero-linear-tail kernel has zero translated constant term, then the no-constant
`dim = 2` branch closes through the low-affine homogeneous plane theorem. -/
theorem residual_eq_zero_of_relations_affinePair_translatedKernel_constZero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    {c0 c1 : Fin 4 → ℝ}
    {r0 r1 : ℝ}
    (h0 : relationPoly u c0 = affineLinePoly r0 1 0)
    (h1 : relationPoly u c1 = affineLinePoly r1 0 1)
    (hconstZero :
      ∀ c,
        c ∈ LinearMap.ker
          (linearCoeffMap
            (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u)) →
          MvPolynomial.coeff m00
            (relationPoly
              (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) c) = 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let b : Fin 2 → ℝ := ![-r0, -r1]
  let b' : Fin 2 → ℝ := ![r0, r1]
  let e : Poly ≃ₐ[ℝ] Poly :=
    affineEquiv (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
      (by simp) (by simp)
      (by
        intro i
        fin_cases i <;> simp [b, b'])
      (by
        intro i
        fin_cases i <;> simp [b, b'])
  let u' : RankFourVec := mapVec e.toAlgHom u
  let K : Submodule ℝ (Fin 4 → ℝ) := LinearMap.ker (linearCoeffMap u')
  have hKdim : Module.finrank ℝ K = 2 := by
    simpa [K, u', e, b] using translatedLinearCoeffKernel_finrank_two_of_affinePair h0 h1
  let basisK : Module.Basis (Fin 2) ℝ K := Module.finBasisOfFinrankEq ℝ K hKdim
  let d : Fin 2 → Fin 4 → ℝ := fun j => (basisK j : Fin 4 → ℝ)
  let q' : Fin 2 → Poly := fun j => relationPoly u' (d j)
  let relK : K →ₗ[ℝ] Poly := {
    toFun x := relationPoly u' (x : Fin 4 → ℝ)
    map_add' x y := by
      exact relationPoly_add u' (x : Fin 4 → ℝ) (y : Fin 4 → ℝ)
    map_smul' a x := by
      exact relationPoly_smul u' a (x : Fin 4 → ℝ) }
  have hrelKBot : LinearMap.ker relK = ⊥ := by
    ext x
    constructor
    · intro hx
      rw [Submodule.mem_bot]
      have hx0' : relationPoly u' (x : Fin 4 → ℝ) = 0 := by
        simpa [relK] using hx
      have hx0 : relationPoly u (x : Fin 4 → ℝ) = 0 := by
        apply e.injective
        simpa [u', e, relationPoly_map] using hx0'
      have hrelInj : Function.Injective (relationPolyLin u) := LinearMap.ker_eq_bot.mp hrelker
      have hxvec : (x : Fin 4 → ℝ) = 0 := by
        apply hrelInj
        simpa [relationPolyLin, relationPoly] using hx0
      exact Subtype.ext hxvec
    · intro hx
      rw [Submodule.mem_bot] at hx
      subst x
      simp [relK]
  have hq'ind : LinearIndependent ℝ q' := by
    simpa [q', d, relK] using basisK.linearIndependent.map' relK hrelKBot
  let q2 : Poly := relationPoly u (d 0)
  let q3 : Poly := relationPoly u (d 1)
  have h2 : relationPoly u (d 0) = q2 := by rfl
  have h3 : relationPoly u (d 1) = q3 := by rfl
  have hq2 : IsQuadratic q2 := by
    dsimp [q2]
    exact isQuadratic_relationPoly hu (d 0)
  have hq3 : IsQuadratic q3 := by
    dsimp [q3]
    exact isQuadratic_relationPoly hu (d 1)
  have hk0 : linearCoeffMap u' (d 0) = 0 := (basisK 0).2
  have hk1 : linearCoeffMap u' (d 1) = 0 := (basisK 1).2
  have hq2_00 : MvPolynomial.coeff m00 (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) b q2) = 0 := by
    simpa [u', e, b, q2, relationPoly_map] using hconstZero (d 0) (basisK 0).2
  have hq2_10 : MvPolynomial.coeff m10 (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) b q2) = 0 := by
    have h := congrArg (fun z : Fin 2 → ℝ => z 0) hk0
    simpa [u', e, b, q2, linearCoeffMap, relationPoly_map] using h
  have hq2_01 : MvPolynomial.coeff m01 (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) b q2) = 0 := by
    have h := congrArg (fun z : Fin 2 → ℝ => z 1) hk0
    simpa [u', e, b, q2, linearCoeffMap, relationPoly_map] using h
  have hq3_00 : MvPolynomial.coeff m00 (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) b q3) = 0 := by
    simpa [u', e, b, q3, relationPoly_map] using hconstZero (d 1) (basisK 1).2
  have hq3_10 : MvPolynomial.coeff m10 (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) b q3) = 0 := by
    have h := congrArg (fun z : Fin 2 → ℝ => z 0) hk1
    simpa [u', e, b, q3, linearCoeffMap, relationPoly_map] using h
  have hq3_01 : MvPolynomial.coeff m01 (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) b q3) = 0 := by
    have h := congrArg (fun z : Fin 2 → ℝ => z 1) hk1
    simpa [u', e, b, q3, linearCoeffMap, relationPoly_map] using h
  have hind' :
      LinearIndependent ℝ
        (fun j : Fin 2 => affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) b (relationPoly u (d j))) := by
    simpa [q', u', e, b, relationPoly_map] using hq'ind
  have hind :
      LinearIndependent ℝ
        ![affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) b q2,
          affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) b q3] := by
    convert hind' using 1
    funext j
    fin_cases j <;> simp [q2, q3, d]
  exact residual_eq_zero_of_relations_affinePair_homQuadratics_independent
    (B := B) (u := u) hu h0 h1 h2 h3 hq2 hq3
    hq2_00 hq2_10 hq2_01 hq3_00 hq3_10 hq3_01 hind hp hsocp

/-- If the translated zero-linear-tail kernel above an affine pair contains a
relation with nonzero constant term, then it has a normalized pair of
relations consisting of one relation with constant term `1` and one nonzero
relation with constant term `0`. -/
theorem exists_translatedKernel_constSplit_of_affinePair
    {u : RankFourVec}
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    {c0 c1 : Fin 4 → ℝ}
    {r0 r1 : ℝ}
    (h0 : relationPoly u c0 = affineLinePoly r0 1 0)
    (h1 : relationPoly u c1 = affineLinePoly r1 0 1)
    (hnonzero :
      ∃ c,
        c ∈ LinearMap.ker
          (linearCoeffMap
            (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u)) ∧
        MvPolynomial.coeff m00
          (relationPoly
            (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) c) ≠ 0) :
    ∃ d0 d1 : Fin 4 → ℝ,
      d0 ∈ LinearMap.ker
        (linearCoeffMap
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u)) ∧
      d1 ∈ LinearMap.ker
        (linearCoeffMap
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u)) ∧
      MvPolynomial.coeff m00
        (relationPoly
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d0) = 1 ∧
      MvPolynomial.coeff m00
        (relationPoly
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d1) = 0 ∧
      relationPoly
        (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d1 ≠ 0 := by
  let b : Fin 2 → ℝ := ![-r0, -r1]
  let b' : Fin 2 → ℝ := ![r0, r1]
  let e : Poly ≃ₐ[ℝ] Poly :=
    affineEquiv (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
      (by simp) (by simp)
      (by
        intro i
        fin_cases i <;> simp [b, b'])
      (by
        intro i
        fin_cases i <;> simp [b, b'])
  let u' : RankFourVec := mapVec e.toAlgHom u
  let K : Submodule ℝ (Fin 4 → ℝ) := LinearMap.ker (linearCoeffMap u')
  let constK : K →ₗ[ℝ] ℝ := {
    toFun x := MvPolynomial.coeff m00 (relationPoly u' (x : Fin 4 → ℝ))
    map_add' x y := by
      change MvPolynomial.coeff m00
          (relationPoly u' ((x : Fin 4 → ℝ) + (y : Fin 4 → ℝ))) =
        MvPolynomial.coeff m00 (relationPoly u' (x : Fin 4 → ℝ)) +
          MvPolynomial.coeff m00 (relationPoly u' (y : Fin 4 → ℝ))
      rw [relationPoly_add, MvPolynomial.coeff_add]
    map_smul' a x := by
      change MvPolynomial.coeff m00
          (relationPoly u' (a • (x : Fin 4 → ℝ))) =
        a * MvPolynomial.coeff m00 (relationPoly u' (x : Fin 4 → ℝ))
      rw [relationPoly_smul, MvPolynomial.coeff_smul]
      simp }
  obtain ⟨c, hcK, hc00⟩ := hnonzero
  let cK : K := ⟨c, by simpa [K, u', e, b] using hcK⟩
  have hcK_ne : constK cK ≠ 0 := by
    simpa [constK, cK, u', e, b] using hc00
  have hKdim : Module.finrank ℝ K = 2 := by
    simpa [K, u', e, b] using translatedLinearCoeffKernel_finrank_two_of_affinePair h0 h1
  have hconstSurj : Function.Surjective constK := by
    intro t
    refine ⟨(t / constK cK) • cK, ?_⟩
    rw [LinearMap.map_smul]
    have hmul : (t / constK cK) * constK cK = t := by
      field_simp [hcK_ne]
    simpa using hmul
  have hrangeTop : LinearMap.range constK = ⊤ := LinearMap.range_eq_top.mpr hconstSurj
  have hrangeDim : Module.finrank ℝ (LinearMap.range constK) = 1 := by
    rw [hrangeTop, finrank_top]
    simp
  have hsum := LinearMap.finrank_range_add_finrank_ker constK
  have hsum' : 1 + Module.finrank ℝ (LinearMap.ker constK) = 2 := by
    simpa [hKdim, hrangeDim] using hsum
  have hK0dim : Module.finrank ℝ (LinearMap.ker constK) = 1 := by
    omega
  let basisK0 : Module.Basis (Fin 1) ℝ (LinearMap.ker constK) :=
    Module.finBasisOfFinrankEq ℝ (LinearMap.ker constK) hK0dim
  let d0K : K := (constK cK)⁻¹ • cK
  let d1K0 : LinearMap.ker constK := basisK0 0
  let d1K : K := d1K0.1
  have hd0K : constK d0K = 1 := by
    rw [LinearMap.map_smul]
    have hmul : ((constK cK)⁻¹ : ℝ) * constK cK = 1 := by
      field_simp [hcK_ne]
    simpa using hmul
  have hd1K : constK d1K = 0 := d1K0.2
  have hd1K0_ne : d1K0 ≠ 0 := basisK0.ne_zero 0
  have hd1K_ne : d1K ≠ 0 := by
    intro hd1zero
    apply hd1K0_ne
    exact Subtype.ext hd1zero
  have hd0const : MvPolynomial.coeff m00 (relationPoly u' (d0K : Fin 4 → ℝ)) = 1 := by
    simpa [constK] using hd0K
  have hd1const : MvPolynomial.coeff m00 (relationPoly u' (d1K : Fin 4 → ℝ)) = 0 := by
    simpa [constK] using hd1K
  have hd1poly_ne : relationPoly u' (d1K : Fin 4 → ℝ) ≠ 0 := by
    intro hd1poly
    have hd1poly0 : relationPoly u ((d1K : K) : Fin 4 → ℝ) = 0 := by
      apply e.injective
      simpa [u', e, relationPoly_map] using hd1poly
    have hrelInj : Function.Injective (relationPolyLin u) := LinearMap.ker_eq_bot.mp hrelker
    have hd1vec : (((d1K : K) : Fin 4 → ℝ)) = 0 := by
      apply hrelInj
      simpa [relationPolyLin, relationPoly] using hd1poly0
    exact hd1K_ne (Subtype.ext hd1vec)
  refine ⟨d0K, d1K, d0K.2, d1K.2, ?_, ?_, ?_⟩
  · simpa [u', e, b] using hd0const
  · simpa [u', e, b] using hd1const
  · simpa [u', e, b] using hd1poly_ne

/-- If the translated zero-linear-tail kernel above an affine pair contains a
normalized constant/nonconstant pair whose quadratic parts are dependent, then
the translated branch already contains `1,x₀,x₁`, so the residual vanishes. -/
theorem residual_eq_zero_of_relations_affinePair_translatedKernel_constSplit_dependent
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 : Fin 4 → ℝ}
    {r0 r1 : ℝ}
    (h0 : relationPoly u c0 = affineLinePoly r0 1 0)
    (h1 : relationPoly u c1 = affineLinePoly r1 0 1)
    {d0 d1 : Fin 4 → ℝ}
    (hd0K :
      d0 ∈ LinearMap.ker
        (linearCoeffMap
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u)))
    (hd1K :
      d1 ∈ LinearMap.ker
        (linearCoeffMap
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u)))
    (hd0const :
      MvPolynomial.coeff m00
        (relationPoly
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d0) = 1)
    (hd1const :
      MvPolynomial.coeff m00
        (relationPoly
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d1) = 0)
    (hd1poly_ne :
      relationPoly
        (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d1 ≠ 0)
    (hA0 :
      lowHomQuadPlaneA
        (relationPoly
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d0)
        (relationPoly
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d1) = 0)
    (hB0 :
      lowHomQuadPlaneB
        (relationPoly
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d0)
        (relationPoly
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d1) = 0)
    (hC0 :
      lowHomQuadPlaneC
        (relationPoly
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d0)
        (relationPoly
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d1) = 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let b : Fin 2 → ℝ := ![-r0, -r1]
  let b' : Fin 2 → ℝ := ![r0, r1]
  let e : Poly ≃ₐ[ℝ] Poly :=
    affineEquiv (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
      (by simp) (by simp)
      (by
        intro i
        fin_cases i <;> simp [b, b'])
      (by
        intro i
        fin_cases i <;> simp [b, b'])
  let u' : RankFourVec := mapVec e.toAlgHom u
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  let B0 : DotForm := dotTransport e B
  have hB0pos : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0pos⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e)
      (heQuad := by
        intro q hq
        exact isQuadratic_affineEquiv
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
          (by simp) (by simp)
          (by intro i; fin_cases i <;> simp [b, b'])
          (by intro i; fin_cases i <;> simp [b, b']) hq)
      (heQuartic := by
        intro q hq
        exact isQuartic_affineEquiv
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
          (by simp) (by simp)
          (by intro i; fin_cases i <;> simp [b, b'])
          (by intro i; fin_cases i <;> simp [b, b']) hq)
      hp
  have hu0 : IsAdmissiblePoint u' := by
    exact isAdmissiblePoint_mapVec_of_equiv
      (e := e)
      (he := by
        intro q hq
        exact isQuadratic_affineEquiv
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
          (by simp) (by simp)
          (by intro i; fin_cases i <;> simp [b, b'])
          (by intro i; fin_cases i <;> simp [b, b']) hq)
      hu
  have hsocp0 : IsSOCP B0 (e p) u' := by
    dsimp [B0, u']
    exact isSOCP_mapVec_of_equiv
      (e := e)
      (heSymm := by
        intro q hq
        exact isQuadratic_affineEquiv_symm
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
          (by simp) (by simp)
          (by intro i; fin_cases i <;> simp [b, b'])
          (by intro i; fin_cases i <;> simp [b, b']) hq)
      hsocp
  have h0' : relationPoly u' c0 = x0 := by
    rw [relationPoly_map]
    rw [h0]
    exact affineHom_translate_affineLine_left r0 r1
  have h1' : relationPoly u' c1 = x1 := by
    rw [relationPoly_map]
    rw [h1]
    exact affineHom_translate_affineLine_right r0 r1
  have hq2 : IsQuadratic (relationPoly u' d0) := isQuadratic_relationPoly hu0 d0
  have hq3 : IsQuadratic (relationPoly u' d1) := isQuadratic_relationPoly hu0 d1
  have hq2_10 :
      MvPolynomial.coeff m10 (relationPoly u' d0) = 0 := by
    have h := congrArg (fun z : Fin 2 → ℝ => z 0) hd0K
    simpa [u', e, b, linearCoeffMap, relationPoly_map] using h
  have hq2_01 :
      MvPolynomial.coeff m01 (relationPoly u' d0) = 0 := by
    have h := congrArg (fun z : Fin 2 → ℝ => z 1) hd0K
    simpa [u', e, b, linearCoeffMap, relationPoly_map] using h
  have hq3_10 :
      MvPolynomial.coeff m10 (relationPoly u' d1) = 0 := by
    have h := congrArg (fun z : Fin 2 → ℝ => z 0) hd1K
    simpa [u', e, b, linearCoeffMap, relationPoly_map] using h
  have hq3_01 :
      MvPolynomial.coeff m01 (relationPoly u' d1) = 0 := by
    have h := congrArg (fun z : Fin 2 → ℝ => z 1) hd1K
    simpa [u', e, b, linearCoeffMap, relationPoly_map] using h
  have hres0 :
      residual (e p) u' = 0 := by
    exact residual_eq_zero_of_relations_x0_x1_onePlus_homQuadratics_dependent
      (B := B0) (u := u') hu0
      (by simpa [relationPoly] using h0')
      (by simpa [relationPoly] using h1')
      (by
        change relationPoly u' d0 = relationPoly u' d0
        rfl)
      (by
        change relationPoly u' d1 = relationPoly u' d1
        rfl)
      hq2 hq3 hd0const hq2_10 hq2_01 hd1const hq3_10 hq3_01
      hA0 hB0 hC0 hd1poly_ne hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

/-- The translated-kernel constant-split branch above an affine pair closes
directly as soon as the homogeneous pair is not linearly independent. -/
theorem residual_eq_zero_of_relations_affinePair_translatedKernel_constSplit_not_independent
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 : Fin 4 → ℝ}
    {r0 r1 : ℝ}
    (h0 : relationPoly u c0 = affineLinePoly r0 1 0)
    (h1 : relationPoly u c1 = affineLinePoly r1 0 1)
    {d0 d1 : Fin 4 → ℝ}
    (hd0K :
      d0 ∈ LinearMap.ker
        (linearCoeffMap
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u)))
    (hd1K :
      d1 ∈ LinearMap.ker
        (linearCoeffMap
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u)))
    (hd0const :
      MvPolynomial.coeff m00
        (relationPoly
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d0) = 1)
    (hd1const :
      MvPolynomial.coeff m00
        (relationPoly
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d1) = 0)
    (hd1poly_ne :
      relationPoly
        (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d1 ≠ 0)
    (hnotind :
      ¬ LinearIndependent ℝ
        ![
          relationPoly
              (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d0 -
            (1 : Poly),
          relationPoly
            (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d1])
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let b : Fin 2 → ℝ := ![-r0, -r1]
  let b' : Fin 2 → ℝ := ![r0, r1]
  let e : Poly ≃ₐ[ℝ] Poly :=
    affineEquiv (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
      (by simp) (by simp)
      (by
        intro i
        fin_cases i <;> simp [b, b'])
      (by
        intro i
        fin_cases i <;> simp [b, b'])
  let u' : RankFourVec := mapVec e.toAlgHom u
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  let B0 : DotForm := dotTransport e B
  have hB0pos : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0pos⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e)
      (heQuad := by
        intro q hq
        exact isQuadratic_affineEquiv
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
          (by simp) (by simp)
          (by intro i; fin_cases i <;> simp [b, b'])
          (by intro i; fin_cases i <;> simp [b, b']) hq)
      (heQuartic := by
        intro q hq
        exact isQuartic_affineEquiv
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
          (by simp) (by simp)
          (by intro i; fin_cases i <;> simp [b, b'])
          (by intro i; fin_cases i <;> simp [b, b']) hq)
      hp
  have hu0 : IsAdmissiblePoint u' := by
    exact isAdmissiblePoint_mapVec_of_equiv
      (e := e)
      (he := by
        intro q hq
        exact isQuadratic_affineEquiv
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
          (by simp) (by simp)
          (by intro i; fin_cases i <;> simp [b, b'])
          (by intro i; fin_cases i <;> simp [b, b']) hq)
      hu
  have hsocp0 : IsSOCP B0 (e p) u' := by
    dsimp [B0, u']
    exact isSOCP_mapVec_of_equiv
      (e := e)
      (heSymm := by
        intro q hq
        exact isQuadratic_affineEquiv_symm
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
          (by simp) (by simp)
          (by intro i; fin_cases i <;> simp [b, b'])
          (by intro i; fin_cases i <;> simp [b, b']) hq)
      hsocp
  have h0' : relationPoly u' c0 = x0 := by
    rw [relationPoly_map]
    rw [h0]
    exact affineHom_translate_affineLine_left r0 r1
  have h1' : relationPoly u' c1 = x1 := by
    rw [relationPoly_map]
    rw [h1]
    exact affineHom_translate_affineLine_right r0 r1
  have hq2 : IsQuadratic (relationPoly u' d0) := isQuadratic_relationPoly hu0 d0
  have hq3 : IsQuadratic (relationPoly u' d1) := isQuadratic_relationPoly hu0 d1
  have hq2_10 :
      MvPolynomial.coeff m10 (relationPoly u' d0) = 0 := by
    have h := congrArg (fun z : Fin 2 → ℝ => z 0) hd0K
    simpa [u', e, b, linearCoeffMap, relationPoly_map] using h
  have hq2_01 :
      MvPolynomial.coeff m01 (relationPoly u' d0) = 0 := by
    have h := congrArg (fun z : Fin 2 → ℝ => z 1) hd0K
    simpa [u', e, b, linearCoeffMap, relationPoly_map] using h
  have hq3_10 :
      MvPolynomial.coeff m10 (relationPoly u' d1) = 0 := by
    have h := congrArg (fun z : Fin 2 → ℝ => z 0) hd1K
    simpa [u', e, b, linearCoeffMap, relationPoly_map] using h
  have hq3_01 :
      MvPolynomial.coeff m01 (relationPoly u' d1) = 0 := by
    have h := congrArg (fun z : Fin 2 → ℝ => z 1) hd1K
    simpa [u', e, b, linearCoeffMap, relationPoly_map] using h
  have hres0 :
      residual (e p) u' = 0 := by
    exact residual_eq_zero_of_relations_x0_x1_onePlus_homQuadratics_not_independent
      (B := B0) (u := u') hu0
      (by simpa [relationPoly] using h0')
      (by simpa [relationPoly] using h1')
      (by
        change relationPoly u' d0 = relationPoly u' d0
        rfl)
      (by
        change relationPoly u' d1 = relationPoly u' d1
        rfl)
      hq2 hq3 hd0const hq2_10 hq2_01 hd1const hq3_10 hq3_01
      (by simpa [u', e, b] using hnotind)
      hd1poly_ne hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

/-- The translated-kernel constant-split branch above an affine pair closes
directly when the homogeneous part lands in the repeated-line/common-factor
chart. -/
theorem residual_eq_zero_of_relations_affinePair_translatedKernel_constSplit_commonFactorChart
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 : Fin 4 → ℝ}
    {r0 r1 : ℝ}
    (h0 : relationPoly u c0 = affineLinePoly r0 1 0)
    (h1 : relationPoly u c1 = affineLinePoly r1 0 1)
    {d0 d1 : Fin 4 → ℝ}
    (hd0K :
      d0 ∈ LinearMap.ker
        (linearCoeffMap
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u)))
    (hd1K :
      d1 ∈ LinearMap.ker
        (linearCoeffMap
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u)))
    (hd0const :
      MvPolynomial.coeff m00
        (relationPoly
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d0) = 1)
    (hd1const :
      MvPolynomial.coeff m00
        (relationPoly
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d1) = 0)
    (hA :
      MvPolynomial.coeff m11
          (relationPoly
            (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d0) *
          MvPolynomial.coeff m02
            (relationPoly
              (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d1) -
        MvPolynomial.coeff m02
            (relationPoly
              (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d0) *
          MvPolynomial.coeff m11
            (relationPoly
              (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d1) ≠ 0)
    (hdiag0 :
      lowHomQuadPlaneC
          (relationPoly
            (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d0)
          (relationPoly
            (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d1) -
        lowHomQuadPlaneB
            (relationPoly
              (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d0)
            (relationPoly
              (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d1) ^ 2 /
          lowHomQuadPlaneA
            (relationPoly
              (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d0)
            (relationPoly
              (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d1) = 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let b : Fin 2 → ℝ := ![-r0, -r1]
  let b' : Fin 2 → ℝ := ![r0, r1]
  let e : Poly ≃ₐ[ℝ] Poly :=
    affineEquiv (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
      (by simp) (by simp)
      (by
        intro i
        fin_cases i <;> simp [b, b'])
      (by
        intro i
        fin_cases i <;> simp [b, b'])
  let u' : RankFourVec := mapVec e.toAlgHom u
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  let B0 : DotForm := dotTransport e B
  have hB0pos : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0pos⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e)
      (heQuad := by
        intro q hq
        exact isQuadratic_affineEquiv
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
          (by simp) (by simp)
          (by intro i; fin_cases i <;> simp [b, b'])
          (by intro i; fin_cases i <;> simp [b, b']) hq)
      (heQuartic := by
        intro q hq
        exact isQuartic_affineEquiv
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
          (by simp) (by simp)
          (by intro i; fin_cases i <;> simp [b, b'])
          (by intro i; fin_cases i <;> simp [b, b']) hq)
      hp
  have hu0 : IsAdmissiblePoint u' := by
    exact isAdmissiblePoint_mapVec_of_equiv
      (e := e)
      (he := by
        intro q hq
        exact isQuadratic_affineEquiv
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
          (by simp) (by simp)
          (by intro i; fin_cases i <;> simp [b, b'])
          (by intro i; fin_cases i <;> simp [b, b']) hq)
      hu
  have hsocp0 : IsSOCP B0 (e p) u' := by
    dsimp [B0, u']
    exact isSOCP_mapVec_of_equiv
      (e := e)
      (heSymm := by
        intro q hq
        exact isQuadratic_affineEquiv_symm
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
          (by simp) (by simp)
          (by intro i; fin_cases i <;> simp [b, b'])
          (by intro i; fin_cases i <;> simp [b, b']) hq)
      hsocp
  have h0' : relationPoly u' c0 = x0 := by
    rw [relationPoly_map]
    rw [h0]
    exact affineHom_translate_affineLine_left r0 r1
  have h1' : relationPoly u' c1 = x1 := by
    rw [relationPoly_map]
    rw [h1]
    exact affineHom_translate_affineLine_right r0 r1
  have hq2 : IsQuadratic (relationPoly u' d0) := isQuadratic_relationPoly hu0 d0
  have hq3 : IsQuadratic (relationPoly u' d1) := isQuadratic_relationPoly hu0 d1
  have hq2_10 :
      MvPolynomial.coeff m10 (relationPoly u' d0) = 0 := by
    have h := congrArg (fun z : Fin 2 → ℝ => z 0) hd0K
    simpa [u', e, b, linearCoeffMap, relationPoly_map] using h
  have hq2_01 :
      MvPolynomial.coeff m01 (relationPoly u' d0) = 0 := by
    have h := congrArg (fun z : Fin 2 → ℝ => z 1) hd0K
    simpa [u', e, b, linearCoeffMap, relationPoly_map] using h
  have hq3_10 :
      MvPolynomial.coeff m10 (relationPoly u' d1) = 0 := by
    have h := congrArg (fun z : Fin 2 → ℝ => z 0) hd1K
    simpa [u', e, b, linearCoeffMap, relationPoly_map] using h
  have hq3_01 :
      MvPolynomial.coeff m01 (relationPoly u' d1) = 0 := by
    have h := congrArg (fun z : Fin 2 → ℝ => z 1) hd1K
    simpa [u', e, b, linearCoeffMap, relationPoly_map] using h
  have hres0 :
      residual (e p) u' = 0 := by
    exact residual_eq_zero_of_relations_x0_x1_onePlus_homQuadratics_commonFactorChart
      (B := B0) (u := u') hu0
      (by simpa [relationPoly] using h0')
      (by simpa [relationPoly] using h1')
      (by
        change relationPoly u' d0 = relationPoly u' d0
        rfl)
      (by
        change relationPoly u' d1 = relationPoly u' d1
        rfl)
      hq2 hq3 hd0const hq2_10 hq2_01 hd1const hq3_10 hq3_01
      (by simpa [u', e, b] using hA)
      (by simpa [u', e, b] using hdiag0)
      hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

/-- The translated-kernel constant-split branch above an affine pair closes
directly when the homogeneous part lands in the coprime cross-determinant-zero
chart. -/
theorem residual_eq_zero_of_relations_affinePair_translatedKernel_constSplit_crossDet_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 : Fin 4 → ℝ}
    {r0 r1 : ℝ}
    (h0 : relationPoly u c0 = affineLinePoly r0 1 0)
    (h1 : relationPoly u c1 = affineLinePoly r1 0 1)
    {d0 d1 : Fin 4 → ℝ}
    (hd0K :
      d0 ∈ LinearMap.ker
        (linearCoeffMap
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u)))
    (hd1K :
      d1 ∈ LinearMap.ker
        (linearCoeffMap
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u)))
    (hd0const :
      MvPolynomial.coeff m00
        (relationPoly
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d0) = 1)
    (hd1const :
      MvPolynomial.coeff m00
        (relationPoly
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d1) = 0)
    (hcross :
      lowHomQuadPlaneA
          (relationPoly
            (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d0)
          (relationPoly
            (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d1) = 0)
    (hdet :
      lowHomQuadPlaneB
          (relationPoly
            (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d0)
          (relationPoly
            (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d1) ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let b : Fin 2 → ℝ := ![-r0, -r1]
  let b' : Fin 2 → ℝ := ![r0, r1]
  let e : Poly ≃ₐ[ℝ] Poly :=
    affineEquiv (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
      (by simp) (by simp)
      (by
        intro i
        fin_cases i <;> simp [b, b'])
      (by
        intro i
        fin_cases i <;> simp [b, b'])
  let u' : RankFourVec := mapVec e.toAlgHom u
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  let B0 : DotForm := dotTransport e B
  have hB0pos : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0pos⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e)
      (heQuad := by
        intro q hq
        exact isQuadratic_affineEquiv
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
          (by simp) (by simp)
          (by intro i; fin_cases i <;> simp [b, b'])
          (by intro i; fin_cases i <;> simp [b, b']) hq)
      (heQuartic := by
        intro q hq
        exact isQuartic_affineEquiv
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
          (by simp) (by simp)
          (by intro i; fin_cases i <;> simp [b, b'])
          (by intro i; fin_cases i <;> simp [b, b']) hq)
      hp
  have hu0 : IsAdmissiblePoint u' := by
    exact isAdmissiblePoint_mapVec_of_equiv
      (e := e)
      (he := by
        intro q hq
        exact isQuadratic_affineEquiv
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
          (by simp) (by simp)
          (by intro i; fin_cases i <;> simp [b, b'])
          (by intro i; fin_cases i <;> simp [b, b']) hq)
      hu
  have hsocp0 : IsSOCP B0 (e p) u' := by
    dsimp [B0, u']
    exact isSOCP_mapVec_of_equiv
      (e := e)
      (heSymm := by
        intro q hq
        exact isQuadratic_affineEquiv_symm
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
          (by simp) (by simp)
          (by intro i; fin_cases i <;> simp [b, b'])
          (by intro i; fin_cases i <;> simp [b, b']) hq)
      hsocp
  have h0' : relationPoly u' c0 = x0 := by
    rw [relationPoly_map]
    rw [h0]
    exact affineHom_translate_affineLine_left r0 r1
  have h1' : relationPoly u' c1 = x1 := by
    rw [relationPoly_map]
    rw [h1]
    exact affineHom_translate_affineLine_right r0 r1
  have hq2 : IsQuadratic (relationPoly u' d0) := isQuadratic_relationPoly hu0 d0
  have hq3 : IsQuadratic (relationPoly u' d1) := isQuadratic_relationPoly hu0 d1
  have hq2_10 :
      MvPolynomial.coeff m10 (relationPoly u' d0) = 0 := by
    have h := congrArg (fun z : Fin 2 → ℝ => z 0) hd0K
    simpa [u', e, b, linearCoeffMap, relationPoly_map] using h
  have hq2_01 :
      MvPolynomial.coeff m01 (relationPoly u' d0) = 0 := by
    have h := congrArg (fun z : Fin 2 → ℝ => z 1) hd0K
    simpa [u', e, b, linearCoeffMap, relationPoly_map] using h
  have hq3_10 :
      MvPolynomial.coeff m10 (relationPoly u' d1) = 0 := by
    have h := congrArg (fun z : Fin 2 → ℝ => z 0) hd1K
    simpa [u', e, b, linearCoeffMap, relationPoly_map] using h
  have hq3_01 :
      MvPolynomial.coeff m01 (relationPoly u' d1) = 0 := by
    have h := congrArg (fun z : Fin 2 → ℝ => z 1) hd1K
    simpa [u', e, b, linearCoeffMap, relationPoly_map] using h
  have hres0 :
      residual (e p) u' = 0 := by
    exact residual_eq_zero_of_relations_x0_x1_onePlus_homQuadratics_crossDet_zero
      (B := B0) (u := u') hu0
      (by simpa [relationPoly] using h0')
      (by simpa [relationPoly] using h1')
      (by
        change relationPoly u' d0 = relationPoly u' d0
        rfl)
      (by
        change relationPoly u' d1 = relationPoly u' d1
        rfl)
      hq2 hq3 hd0const hq2_10 hq2_01 hd1const hq3_10 hq3_01
      (by simpa [u', e, b] using hcross)
      (by simpa [u', e, b] using hdet)
      hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

/-- The translated-kernel constant-split branch above an affine pair closes
directly when the homogeneous part lands in the diagonal-sum chart. -/
theorem residual_eq_zero_of_relations_affinePair_translatedKernel_constSplit_diagSumChart
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 : Fin 4 → ℝ}
    {r0 r1 : ℝ}
    (h0 : relationPoly u c0 = affineLinePoly r0 1 0)
    (h1 : relationPoly u c1 = affineLinePoly r1 0 1)
    {d0 d1 : Fin 4 → ℝ}
    (hd0K :
      d0 ∈ LinearMap.ker
        (linearCoeffMap
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u)))
    (hd1K :
      d1 ∈ LinearMap.ker
        (linearCoeffMap
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u)))
    (hd0const :
      MvPolynomial.coeff m00
        (relationPoly
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d0) = 1)
    (hd1const :
      MvPolynomial.coeff m00
        (relationPoly
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d1) = 0)
    (hA :
      lowHomQuadPlaneA
          (relationPoly
            (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d0)
          (relationPoly
            (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d1) ≠ 0)
    (hpos :
      0 <
        (lowHomQuadPlaneC
            (relationPoly
              (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d0)
            (relationPoly
              (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d1) -
          lowHomQuadPlaneB
              (relationPoly
                (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d0)
              (relationPoly
                (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d1) ^ 2 /
            lowHomQuadPlaneA
              (relationPoly
                (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d0)
              (relationPoly
                (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d1)) /
          lowHomQuadPlaneA
            (relationPoly
              (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d0)
            (relationPoly
              (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d1))
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let b : Fin 2 → ℝ := ![-r0, -r1]
  let b' : Fin 2 → ℝ := ![r0, r1]
  let e : Poly ≃ₐ[ℝ] Poly :=
    affineEquiv (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
      (by simp) (by simp)
      (by
        intro i
        fin_cases i <;> simp [b, b'])
      (by
        intro i
        fin_cases i <;> simp [b, b'])
  let u' : RankFourVec := mapVec e.toAlgHom u
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  let B0 : DotForm := dotTransport e B
  have hB0pos : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0pos⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e)
      (heQuad := by
        intro q hq
        exact isQuadratic_affineEquiv
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
          (by simp) (by simp)
          (by intro i; fin_cases i <;> simp [b, b'])
          (by intro i; fin_cases i <;> simp [b, b']) hq)
      (heQuartic := by
        intro q hq
        exact isQuartic_affineEquiv
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
          (by simp) (by simp)
          (by intro i; fin_cases i <;> simp [b, b'])
          (by intro i; fin_cases i <;> simp [b, b']) hq)
      hp
  have hu0 : IsAdmissiblePoint u' := by
    exact isAdmissiblePoint_mapVec_of_equiv
      (e := e)
      (he := by
        intro q hq
        exact isQuadratic_affineEquiv
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
          (by simp) (by simp)
          (by intro i; fin_cases i <;> simp [b, b'])
          (by intro i; fin_cases i <;> simp [b, b']) hq)
      hu
  have hsocp0 : IsSOCP B0 (e p) u' := by
    dsimp [B0, u']
    exact isSOCP_mapVec_of_equiv
      (e := e)
      (heSymm := by
        intro q hq
        exact isQuadratic_affineEquiv_symm
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
          (by simp) (by simp)
          (by intro i; fin_cases i <;> simp [b, b'])
          (by intro i; fin_cases i <;> simp [b, b']) hq)
      hsocp
  have h0' : relationPoly u' c0 = x0 := by
    rw [relationPoly_map]
    rw [h0]
    exact affineHom_translate_affineLine_left r0 r1
  have h1' : relationPoly u' c1 = x1 := by
    rw [relationPoly_map]
    rw [h1]
    exact affineHom_translate_affineLine_right r0 r1
  have hq2 : IsQuadratic (relationPoly u' d0) := isQuadratic_relationPoly hu0 d0
  have hq3 : IsQuadratic (relationPoly u' d1) := isQuadratic_relationPoly hu0 d1
  have hq2_10 :
      MvPolynomial.coeff m10 (relationPoly u' d0) = 0 := by
    have h := congrArg (fun z : Fin 2 → ℝ => z 0) hd0K
    simpa [u', e, b, linearCoeffMap, relationPoly_map] using h
  have hq2_01 :
      MvPolynomial.coeff m01 (relationPoly u' d0) = 0 := by
    have h := congrArg (fun z : Fin 2 → ℝ => z 1) hd0K
    simpa [u', e, b, linearCoeffMap, relationPoly_map] using h
  have hq3_10 :
      MvPolynomial.coeff m10 (relationPoly u' d1) = 0 := by
    have h := congrArg (fun z : Fin 2 → ℝ => z 0) hd1K
    simpa [u', e, b, linearCoeffMap, relationPoly_map] using h
  have hq3_01 :
      MvPolynomial.coeff m01 (relationPoly u' d1) = 0 := by
    have h := congrArg (fun z : Fin 2 → ℝ => z 1) hd1K
    simpa [u', e, b, linearCoeffMap, relationPoly_map] using h
  have hres0 :
      residual (e p) u' = 0 := by
    exact residual_eq_zero_of_relations_x0_x1_onePlus_homQuadratics_diagSumChart
      (B := B0) (u := u') hu0
      (by simpa [relationPoly] using h0')
      (by simpa [relationPoly] using h1')
      (by
        change relationPoly u' d0 = relationPoly u' d0
        rfl)
      (by
        change relationPoly u' d1 = relationPoly u' d1
        rfl)
      hq2 hq3 hd0const hq2_10 hq2_01 hd1const hq3_10 hq3_01
      (by simpa [u', e, b] using hA)
      (by simpa [u', e, b] using hpos)
      hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

/-- The translated-kernel constant-split branch above an affine pair closes
directly when the homogeneous part lands in the diagonal-difference chart. -/
theorem residual_eq_zero_of_relations_affinePair_translatedKernel_constSplit_diagDiffChart
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 : Fin 4 → ℝ}
    {r0 r1 : ℝ}
    (h0 : relationPoly u c0 = affineLinePoly r0 1 0)
    (h1 : relationPoly u c1 = affineLinePoly r1 0 1)
    {d0 d1 : Fin 4 → ℝ}
    (hd0K :
      d0 ∈ LinearMap.ker
        (linearCoeffMap
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u)))
    (hd1K :
      d1 ∈ LinearMap.ker
        (linearCoeffMap
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u)))
    (hd0const :
      MvPolynomial.coeff m00
        (relationPoly
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d0) = 1)
    (hd1const :
      MvPolynomial.coeff m00
        (relationPoly
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d1) = 0)
    (hA :
      lowHomQuadPlaneA
          (relationPoly
            (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d0)
          (relationPoly
            (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d1) ≠ 0)
    (hpos :
      0 <
        (-(lowHomQuadPlaneC
              (relationPoly
                (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d0)
              (relationPoly
                (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d1) -
            lowHomQuadPlaneB
                (relationPoly
                  (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d0)
                (relationPoly
                  (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d1) ^ 2 /
              lowHomQuadPlaneA
                (relationPoly
                  (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d0)
                (relationPoly
                  (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d1))) /
          lowHomQuadPlaneA
            (relationPoly
              (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d0)
            (relationPoly
              (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d1))
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let b : Fin 2 → ℝ := ![-r0, -r1]
  let b' : Fin 2 → ℝ := ![r0, r1]
  let e : Poly ≃ₐ[ℝ] Poly :=
    affineEquiv (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
      (by simp) (by simp)
      (by
        intro i
        fin_cases i <;> simp [b, b'])
      (by
        intro i
        fin_cases i <;> simp [b, b'])
  let u' : RankFourVec := mapVec e.toAlgHom u
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  let B0 : DotForm := dotTransport e B
  have hB0pos : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0pos⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e)
      (heQuad := by
        intro q hq
        exact isQuadratic_affineEquiv
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
          (by simp) (by simp)
          (by intro i; fin_cases i <;> simp [b, b'])
          (by intro i; fin_cases i <;> simp [b, b']) hq)
      (heQuartic := by
        intro q hq
        exact isQuartic_affineEquiv
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
          (by simp) (by simp)
          (by intro i; fin_cases i <;> simp [b, b'])
          (by intro i; fin_cases i <;> simp [b, b']) hq)
      hp
  have hu0 : IsAdmissiblePoint u' := by
    exact isAdmissiblePoint_mapVec_of_equiv
      (e := e)
      (he := by
        intro q hq
        exact isQuadratic_affineEquiv
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
          (by simp) (by simp)
          (by intro i; fin_cases i <;> simp [b, b'])
          (by intro i; fin_cases i <;> simp [b, b']) hq)
      hu
  have hsocp0 : IsSOCP B0 (e p) u' := by
    dsimp [B0, u']
    exact isSOCP_mapVec_of_equiv
      (e := e)
      (heSymm := by
        intro q hq
        exact isQuadratic_affineEquiv_symm
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
          (by simp) (by simp)
          (by intro i; fin_cases i <;> simp [b, b'])
          (by intro i; fin_cases i <;> simp [b, b']) hq)
      hsocp
  have h0' : relationPoly u' c0 = x0 := by
    rw [relationPoly_map]
    rw [h0]
    exact affineHom_translate_affineLine_left r0 r1
  have h1' : relationPoly u' c1 = x1 := by
    rw [relationPoly_map]
    rw [h1]
    exact affineHom_translate_affineLine_right r0 r1
  have hq2 : IsQuadratic (relationPoly u' d0) := isQuadratic_relationPoly hu0 d0
  have hq3 : IsQuadratic (relationPoly u' d1) := isQuadratic_relationPoly hu0 d1
  have hq2_10 :
      MvPolynomial.coeff m10 (relationPoly u' d0) = 0 := by
    have h := congrArg (fun z : Fin 2 → ℝ => z 0) hd0K
    simpa [u', e, b, linearCoeffMap, relationPoly_map] using h
  have hq2_01 :
      MvPolynomial.coeff m01 (relationPoly u' d0) = 0 := by
    have h := congrArg (fun z : Fin 2 → ℝ => z 1) hd0K
    simpa [u', e, b, linearCoeffMap, relationPoly_map] using h
  have hq3_10 :
      MvPolynomial.coeff m10 (relationPoly u' d1) = 0 := by
    have h := congrArg (fun z : Fin 2 → ℝ => z 0) hd1K
    simpa [u', e, b, linearCoeffMap, relationPoly_map] using h
  have hq3_01 :
      MvPolynomial.coeff m01 (relationPoly u' d1) = 0 := by
    have h := congrArg (fun z : Fin 2 → ℝ => z 1) hd1K
    simpa [u', e, b, linearCoeffMap, relationPoly_map] using h
  have hres0 :
      residual (e p) u' = 0 := by
    exact residual_eq_zero_of_relations_x0_x1_onePlus_homQuadratics_diagDiffChart
      (B := B0) (u := u') hu0
      (by simpa [relationPoly] using h0')
      (by simpa [relationPoly] using h1')
      (by
        change relationPoly u' d0 = relationPoly u' d0
        rfl)
      (by
        change relationPoly u' d1 = relationPoly u' d1
        rfl)
      hq2 hq3 hd0const hq2_10 hq2_01 hd1const hq3_10 hq3_01
      (by simpa [u', e, b] using hA)
      (by simpa [u', e, b] using hpos)
      hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

/-- The translated-kernel constant-split branch above an affine pair closes
directly once the translated constant-perturbed low-affine pair is linearly
independent. -/
theorem residual_eq_zero_of_relations_affinePair_translatedKernel_constSplit_independent
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 : Fin 4 → ℝ}
    {r0 r1 : ℝ}
    (h0 : relationPoly u c0 = affineLinePoly r0 1 0)
    (h1 : relationPoly u c1 = affineLinePoly r1 0 1)
    {d0 d1 : Fin 4 → ℝ}
    (hd0K :
      d0 ∈ LinearMap.ker
        (linearCoeffMap
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u)))
    (hd1K :
      d1 ∈ LinearMap.ker
        (linearCoeffMap
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u)))
    (hd0const :
      MvPolynomial.coeff m00
        (relationPoly
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d0) = 1)
    (hd1const :
      MvPolynomial.coeff m00
        (relationPoly
          (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d1) = 0)
    (hind :
      LinearIndependent ℝ
        ![
          relationPoly
              (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d0 -
            (1 : Poly),
          relationPoly
            (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d1])
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_relations_affinePair_onePlus_homQuadratics_independent
    (B := B) (u := u) hu h0 h1
    (by
      change relationPoly u d0 = relationPoly u d0
      rfl)
    (by
      change relationPoly u d1 = relationPoly u d1
      rfl)
    (isQuadratic_relationPoly hu d0)
    (isQuadratic_relationPoly hu d1)
    (by simpa [relationPoly_map] using hd0const)
    (by
      have h := congrArg (fun z : Fin 2 → ℝ => z 0) hd0K
      simpa [linearCoeffMap, relationPoly_map] using h)
    (by
      have h := congrArg (fun z : Fin 2 → ℝ => z 1) hd0K
      simpa [linearCoeffMap, relationPoly_map] using h)
    (by simpa [relationPoly_map] using hd1const)
    (by
      have h := congrArg (fun z : Fin 2 → ℝ => z 0) hd1K
      simpa [linearCoeffMap, relationPoly_map] using h)
    (by
      have h := congrArg (fun z : Fin 2 → ℝ => z 1) hd1K
      simpa [linearCoeffMap, relationPoly_map] using h)
    (by simpa [relationPoly_map] using hind)
    hp hsocp

/-- If the exact affine relation space has dimension two and contains no exact
constant relation, the whole branch closes by extracting an affine pair and
then splitting the translated zero-linear-tail kernel into the all-zero-constant
or constant-split cases. -/
theorem residual_eq_zero_of_exactAffineDimTwo_noConst
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 2)
    (hnoConst : ¬ ∃ c ∈ exactAffineSubmodule u, relationPoly u c = (1 : Poly))
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  obtain ⟨c0, c1, r0, r1, hc0, hc1, h0, h1⟩ :=
    exists_exactAffine_affinePair_of_dimTwo_noConst hu hrelker hdim hnoConst
  by_cases hconstAllZero :
      ∀ c,
        c ∈ LinearMap.ker
          (linearCoeffMap
            (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u)) →
          MvPolynomial.coeff m00
            (relationPoly
              (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) c) = 0
  · exact residual_eq_zero_of_relations_affinePair_translatedKernel_constZero
      (B := B) (u := u) hu hrelker h0 h1 hconstAllZero hp hsocp
  · have hnonzero :
        ∃ c,
          c ∈ LinearMap.ker
            (linearCoeffMap
              (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u)) ∧
          MvPolynomial.coeff m00
            (relationPoly
              (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) c) ≠ 0 := by
      by_contra hnonzero
      apply hconstAllZero
      intro c hc
      by_contra hcz
      exact hnonzero ⟨c, hc, hcz⟩
    obtain ⟨d0, d1, hd0K, hd1K, hd0const, hd1const, hd1poly_ne⟩ :=
      exists_translatedKernel_constSplit_of_affinePair hrelker h0 h1 hnonzero
    by_cases hnotind :
        ¬ LinearIndependent ℝ
          ![
            relationPoly
                (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d0 -
              (1 : Poly),
            relationPoly
              (mapVec (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1]) u) d1]
    · exact residual_eq_zero_of_relations_affinePair_translatedKernel_constSplit_not_independent
        (B := B) (u := u) hu h0 h1 hd0K hd1K hd0const hd1const hd1poly_ne
        hnotind hp hsocp
    · exact residual_eq_zero_of_relations_affinePair_translatedKernel_constSplit_independent
        (B := B) (u := u) hu h0 h1 hd0K hd1K hd0const hd1const
        (not_not.mp hnotind) hp hsocp

private theorem range_affineCoeff_eq_span_x0_of_finrank_one
    {u : RankFourVec}
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (hrange1 : Module.finrank ℝ (LinearMap.range (affineCoeffMap u)) = 1) :
    LinearMap.range (affineCoeffMap u) =
      Submodule.span ℝ ({![0, 1, 0]} : Set (Fin 3 → ℝ)) := by
  have hx0mem : (![0, 1, 0] : Fin 3 → ℝ) ∈ LinearMap.range (affineCoeffMap u) := by
    refine ⟨c0, ?_⟩
    ext j
    fin_cases j
    · simpa [affineCoeffMap, x0] using congrArg (MvPolynomial.coeff m00) h0
    · simpa [affineCoeffMap, x0] using congrArg (MvPolynomial.coeff m10) h0
    · simpa [affineCoeffMap, x0] using congrArg (MvPolynomial.coeff m01) h0
  let y0 : LinearMap.range (affineCoeffMap u) := ⟨![0, 1, 0], hx0mem⟩
  have hy0ne : y0 ≠ 0 := by
    intro hy0
    have hvec : (![0, 1, 0] : Fin 3 → ℝ) = 0 := by
      exact congrArg Subtype.val hy0
    have hcoord := congrArg (fun z : Fin 3 → ℝ => z 1) hvec
    simp at hcoord
  have hsurj :
      ∀ y : LinearMap.range (affineCoeffMap u), ∃ t : ℝ, t • y0 = y :=
    (finrank_eq_one_iff_of_nonzero' y0 hy0ne).mp hrange1
  ext y
  constructor
  · intro hy
    let y' : LinearMap.range (affineCoeffMap u) := ⟨y, hy⟩
    obtain ⟨t, ht⟩ := hsurj y'
    have htval : t • (![0, 1, 0] : Fin 3 → ℝ) = y := by
      simpa [y0, y'] using congrArg Subtype.val ht
    exact Submodule.mem_span_singleton.mpr ⟨t, htval⟩
  · intro hy
    rcases Submodule.mem_span_singleton.mp hy with ⟨t, rfl⟩
    exact Submodule.smul_mem _ _ hx0mem

/-- If the affine coefficient image is already one-dimensional and contains an
exact `x₀` relation, the whole branch closes through the affine-rank-one
theorem. -/
theorem residual_eq_zero_of_relations_x0_affineRankOne_of_finrank_range_one
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (hrange1 : Module.finrank ℝ (LinearMap.range (affineCoeffMap u)) = 1)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_relations_x0_affineRankOne
    (B := B) (u := u) hu h0
    (range_affineCoeff_eq_span_x0_of_finrank_one h0 hrange1)
    hp hsocp

/-- Under exact-affine dimension one, an exact `x₀` relation determines three
further relations whose homogeneous parts are exactly
`x₀²`, `x₀x₁`, and `x₁²`, with only constant and `x₁` tails remaining. -/
theorem exists_relations_x0_homQuadBasis_of_exactAffineDimOne
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 1)
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0) :
    ∃ c20 c11 c02 : Fin 4 → ℝ, ∃ α20 β20 α11 β11 α02 β02 : ℝ,
      relationPoly u c20 = α20 • (1 : Poly) + β20 • x1 + x0 ^ 2 ∧
      relationPoly u c11 = α11 • (1 : Poly) + β11 • x1 + (x0 * x1 : Poly) ∧
      relationPoly u c02 = α02 • (1 : Poly) + β02 • x1 + x1 ^ 2 := by
  have hc0mem : c0 ∈ exactAffineSubmodule u := by
    ext j
    fin_cases j
    · have h : MvPolynomial.coeff m20 (relationPoly u c0) = 0 := by
        simpa [x0] using congrArg (MvPolynomial.coeff m20) h0
      simpa [homCoeffMap] using h
    · have h := congrArg (MvPolynomial.coeff m11) h0
      have hx0m11 : MvPolynomial.coeff m11 (x0 : Poly) = 0 := by
        rw [x0, MvPolynomial.coeff_X']
        have hneq : (Finsupp.single 0 1 : Fin 2 →₀ ℕ) ≠ m11 := by
          intro hs
          have h1 := congrArg (fun s : Fin 2 →₀ ℕ => s 1) hs
          simp [m11] at h1
        simp [hneq]
      have h' : MvPolynomial.coeff m11 (relationPoly u c0) = 0 := by
        exact h.trans hx0m11
      simpa [homCoeffMap] using h'
    · have h := congrArg (MvPolynomial.coeff m02) h0
      have hx0m02 : MvPolynomial.coeff m02 (x0 : Poly) = 0 := by
        rw [x0, MvPolynomial.coeff_X']
        have hneq : (Finsupp.single 0 1 : Fin 2 →₀ ℕ) ≠ m02 := by
          intro hs
          have h1 := congrArg (fun s : Fin 2 →₀ ℕ => s 1) hs
          simp [m02] at h1
        simp [hneq]
      have h' : MvPolynomial.coeff m02 (relationPoly u c0) = 0 := by
        exact h.trans hx0m02
      simpa [homCoeffMap] using h'
  have hc0ne : c0 ≠ 0 := by
    intro hc0
    have hcoeff := congrArg (MvPolynomial.coeff m10) (by simpa [relationPoly, hc0] using h0)
    simp [x0] at hcoeff
  let c0E : exactAffineSubmodule u := ⟨c0, hc0mem⟩
  have hc0E_ne : c0E ≠ 0 := by
    intro hc0E
    apply hc0ne
    exact Subtype.ext_iff.mp hc0E
  let K : Submodule ℝ (Fin 4 → ℝ) := LinearMap.ker (x0CoeffMap u)
  have hsurjX0 : Function.Surjective (x0CoeffMap u) := by
    intro t
    refine ⟨t • c0, ?_⟩
    have hc010 : x0CoeffMap u c0 = 1 := by
      simpa [x0CoeffMap, x0] using congrArg (MvPolynomial.coeff m10) h0
    rw [LinearMap.map_smul, hc010]
    simp
  have hrangeTopX0 : LinearMap.range (x0CoeffMap u) = ⊤ := LinearMap.range_eq_top.mpr hsurjX0
  have hdom4 : Module.finrank ℝ (Fin 4 → ℝ) = 4 := by
    calc
      Module.finrank ℝ (Fin 4 → ℝ) = Fintype.card (Fin 4) :=
        Module.finrank_fintype_fun_eq_card (R := ℝ) (η := Fin 4)
      _ = 4 := by decide
  have hrangeX0 : Module.finrank ℝ (LinearMap.range (x0CoeffMap u)) = 1 := by
    rw [hrangeTopX0, finrank_top]
    simp
  have hKdim : Module.finrank ℝ K = 3 := by
    have hsum := LinearMap.finrank_range_add_finrank_ker (x0CoeffMap u)
    have hsum' : 1 + Module.finrank ℝ K = 4 := by
      simpa [K, hrangeX0, hdom4] using hsum
    omega
  let homK : K →ₗ[ℝ] (Fin 3 → ℝ) := (homCoeffMap u).comp K.subtype
  have hhomKBot : LinearMap.ker homK = ⊥ := by
    ext x
    constructor
    · intro hx
      rw [Submodule.mem_bot]
      have hxHom : homCoeffMap u ((x : K) : Fin 4 → ℝ) = 0 := by
        simpa [homK] using hx
      have hxAff : ((x : K) : Fin 4 → ℝ) ∈ exactAffineSubmodule u := by
        simpa [exactAffineSubmodule] using hxHom
      obtain ⟨t, ht⟩ :=
        exists_smul_eq_of_finrank_eq_one hdim hc0E_ne ⟨((x : K) : Fin 4 → ℝ), hxAff⟩
      have htvec : t • c0 = ((x : K) : Fin 4 → ℝ) := by
        simpa using congrArg Subtype.val ht
      have hc010 : x0CoeffMap u c0 = 1 := by
        simpa [x0CoeffMap, x0] using congrArg (MvPolynomial.coeff m10) h0
      have hx0zero : MvPolynomial.coeff m10 (relationPoly u ((x : K) : Fin 4 → ℝ)) = 0 := by
        change x0CoeffMap u ((x : K) : Fin 4 → ℝ) = 0
        exact (x : K).2
      have htzero : t = 0 := by
        have htcoeff :
            MvPolynomial.coeff m10 (relationPoly u (t • c0)) =
              MvPolynomial.coeff m10 (relationPoly u ((x : K) : Fin 4 → ℝ)) := by
          exact congrArg (fun v => MvPolynomial.coeff m10 (relationPoly u v)) htvec
        rw [relationPoly_smul, MvPolynomial.coeff_smul, h0] at htcoeff
        simp [x0, hx0zero] at htcoeff
        exact htcoeff
      apply Subtype.ext
      calc
        ((x : K) : Fin 4 → ℝ) = t • c0 := by simpa using htvec.symm
        _ = 0 := by simp [htzero]
    · intro hx
      rw [Submodule.mem_bot] at hx
      subst x
      simp [homK]
  have hhomKinj : Function.Injective homK := LinearMap.ker_eq_bot.mp hhomKBot
  have hrangeHomK : Module.finrank ℝ (LinearMap.range homK) = 3 := by
    simpa [hKdim] using LinearMap.finrank_range_of_inj hhomKinj
  have hcodom3 : Module.finrank ℝ (Fin 3 → ℝ) = 3 := by
    calc
      Module.finrank ℝ (Fin 3 → ℝ) = Fintype.card (Fin 3) :=
        Module.finrank_fintype_fun_eq_card (R := ℝ) (η := Fin 3)
      _ = 3 := by decide
  have hrangeTopHomK : LinearMap.range homK = ⊤ := by
    have hEq :
        Module.finrank ℝ (LinearMap.range homK) = Module.finrank ℝ (Fin 3 → ℝ) := by
      calc
        Module.finrank ℝ (LinearMap.range homK) = 3 := hrangeHomK
        _ = Module.finrank ℝ (Fin 3 → ℝ) := hcodom3.symm
    exact Submodule.eq_top_of_finrank_eq hEq
  obtain ⟨d20K, hd20K⟩ := LinearMap.range_eq_top.mp hrangeTopHomK ![1, 0, 0]
  obtain ⟨d11K, hd11K⟩ := LinearMap.range_eq_top.mp hrangeTopHomK ![0, 1, 0]
  obtain ⟨d02K, hd02K⟩ := LinearMap.range_eq_top.mp hrangeTopHomK ![0, 0, 1]
  let q20 : Poly := relationPoly u (d20K : Fin 4 → ℝ)
  let q11 : Poly := relationPoly u (d11K : Fin 4 → ℝ)
  let q02 : Poly := relationPoly u (d02K : Fin 4 → ℝ)
  let α20 : ℝ := MvPolynomial.coeff m00 q20
  let β20 : ℝ := MvPolynomial.coeff m01 q20
  let α11 : ℝ := MvPolynomial.coeff m00 q11
  let β11 : ℝ := MvPolynomial.coeff m01 q11
  let α02 : ℝ := MvPolynomial.coeff m00 q02
  let β02 : ℝ := MvPolynomial.coeff m01 q02
  have hq20 : IsQuadratic q20 := isQuadratic_relationPoly hu (d20K : Fin 4 → ℝ)
  have hq11 : IsQuadratic q11 := isQuadratic_relationPoly hu (d11K : Fin 4 → ℝ)
  have hq02 : IsQuadratic q02 := isQuadratic_relationPoly hu (d02K : Fin 4 → ℝ)
  have h20_10 : MvPolynomial.coeff m10 q20 = 0 := by
    change x0CoeffMap u ((d20K : K) : Fin 4 → ℝ) = 0
    exact d20K.2
  have h20_20 : MvPolynomial.coeff m20 q20 = 1 := by
    have h := congrArg (fun z : Fin 3 → ℝ => z 0) hd20K
    simpa [homK, q20] using h
  have h20_11 : MvPolynomial.coeff m11 q20 = 0 := by
    have h := congrArg (fun z : Fin 3 → ℝ => z 1) hd20K
    simpa [homK, q20] using h
  have h20_02 : MvPolynomial.coeff m02 q20 = 0 := by
    have h := congrArg (fun z : Fin 3 → ℝ => z 2) hd20K
    simpa [homK, q20] using h
  have h11_10 : MvPolynomial.coeff m10 q11 = 0 := by
    change x0CoeffMap u ((d11K : K) : Fin 4 → ℝ) = 0
    exact d11K.2
  have h11_20 : MvPolynomial.coeff m20 q11 = 0 := by
    have h := congrArg (fun z : Fin 3 → ℝ => z 0) hd11K
    simpa [homK, q11] using h
  have h11_11 : MvPolynomial.coeff m11 q11 = 1 := by
    have h := congrArg (fun z : Fin 3 → ℝ => z 1) hd11K
    simpa [homK, q11] using h
  have h11_02 : MvPolynomial.coeff m02 q11 = 0 := by
    have h := congrArg (fun z : Fin 3 → ℝ => z 2) hd11K
    simpa [homK, q11] using h
  have h02_10 : MvPolynomial.coeff m10 q02 = 0 := by
    change x0CoeffMap u ((d02K : K) : Fin 4 → ℝ) = 0
    exact d02K.2
  have h02_20 : MvPolynomial.coeff m20 q02 = 0 := by
    have h := congrArg (fun z : Fin 3 → ℝ => z 0) hd02K
    simpa [homK, q02] using h
  have h02_11 : MvPolynomial.coeff m11 q02 = 0 := by
    have h := congrArg (fun z : Fin 3 → ℝ => z 1) hd02K
    simpa [homK, q02] using h
  have h02_02 : MvPolynomial.coeff m02 q02 = 1 := by
    have h := congrArg (fun z : Fin 3 → ℝ => z 2) hd02K
    simpa [homK, q02] using h
  have hq20eq : q20 = α20 • (1 : Poly) + β20 • x1 + x0 ^ 2 := by
    calc
      q20 = quadForm α20 0 β20 1 0 0 := by
        rw [quadratic_eq_quadForm hq20]
        simp [α20, β20, q20, h20_10, h20_20, h20_11, h20_02]
      _ = α20 • (1 : Poly) + β20 • x1 + x0 ^ 2 := by
        rw [quadForm_eq_explicit]
        simp [MvPolynomial.smul_eq_C_mul, add_left_comm, add_comm]
  have hq11eq : q11 = α11 • (1 : Poly) + β11 • x1 + (x0 * x1 : Poly) := by
    calc
      q11 = quadForm α11 0 β11 0 1 0 := by
        rw [quadratic_eq_quadForm hq11]
        simp [α11, β11, q11, h11_10, h11_20, h11_11, h11_02]
      _ = α11 • (1 : Poly) + β11 • x1 + (x0 * x1 : Poly) := by
        rw [quadForm_eq_explicit]
        simp [MvPolynomial.smul_eq_C_mul, add_left_comm, add_comm]
  have hq02eq : q02 = α02 • (1 : Poly) + β02 • x1 + x1 ^ 2 := by
    calc
      q02 = quadForm α02 0 β02 0 0 1 := by
        rw [quadratic_eq_quadForm hq02]
        simp [α02, β02, q02, h02_10, h02_20, h02_11, h02_02]
      _ = α02 • (1 : Poly) + β02 • x1 + x1 ^ 2 := by
        rw [quadForm_eq_explicit]
        simp [MvPolynomial.smul_eq_C_mul, add_comm]
  exact ⟨d20K, d11K, d02K, α20, β20, α11, β11, α02, β02,
    by simpa [q20] using hq20eq,
    by simpa [q11] using hq11eq,
    by simpa [q02] using hq02eq⟩

/-- The kernel of the `x₀`-coefficient map has dimension three once an exact
`x₀` relation is fixed. -/
theorem x0CoeffKernel_finrank_three_of_relation_x0
    {u : RankFourVec}
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0) :
    Module.finrank ℝ (LinearMap.ker (x0CoeffMap u)) = 3 := by
  let f : (Fin 4 → ℝ) →ₗ[ℝ] ℝ := x0CoeffMap u
  have hsurj : Function.Surjective f := by
    intro t
    refine ⟨t • c0, ?_⟩
    have hc010 : f c0 = 1 := by
      simpa [f, x0CoeffMap, x0] using congrArg (MvPolynomial.coeff m10) h0
    rw [LinearMap.map_smul, hc010]
    simp
  have hrangeTop : LinearMap.range f = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hrangeFin : Module.finrank ℝ (LinearMap.range f) = 1 := by
    rw [hrangeTop, finrank_top]
    simp
  have hdom : Module.finrank ℝ (Fin 4 → ℝ) = 4 := by
    calc
      Module.finrank ℝ (Fin 4 → ℝ) = Fintype.card (Fin 4) :=
        Module.finrank_fintype_fun_eq_card (R := ℝ) (η := Fin 4)
      _ = 4 := by decide
  have hsum := LinearMap.finrank_range_add_finrank_ker f
  have hsum' : 1 + Module.finrank ℝ (LinearMap.ker f) = 4 := by
    simpa [hrangeFin, hdom] using hsum
  have hsum'' : 1 + Module.finrank ℝ (LinearMap.ker f) = 1 + 3 := by
    simpa using hsum'
  exact Nat.add_left_cancel hsum''

/-- If the residual tail map on the `x₀`-kernel has rank one, then the kernel
contains one relation with nonzero `(1,x₁)` tail together with two linearly
independent pure homogeneous relations. -/
theorem exists_x0_tail_nonzero_homPair_of_finrank_range_one
    {u : RankFourVec}
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (hrange1 : Module.finrank ℝ (LinearMap.range (x0TailCoeffMap u)) = 1) :
    ∃ d0 d1 d2 : Fin 4 → ℝ,
      d0 ∈ LinearMap.ker (x0CoeffMap u) ∧
      d1 ∈ LinearMap.ker (x0CoeffMap u) ∧
      d2 ∈ LinearMap.ker (x0CoeffMap u) ∧
      (MvPolynomial.coeff m00 (relationPoly u d0)) ^ 2 +
          (MvPolynomial.coeff m01 (relationPoly u d0)) ^ 2 ≠ 0 ∧
      MvPolynomial.coeff m00 (relationPoly u d1) = 0 ∧
      MvPolynomial.coeff m01 (relationPoly u d1) = 0 ∧
      MvPolynomial.coeff m00 (relationPoly u d2) = 0 ∧
      MvPolynomial.coeff m01 (relationPoly u d2) = 0 ∧
      LinearIndependent ℝ ![relationPoly u d1, relationPoly u d2] := by
  let K : Submodule ℝ (Fin 4 → ℝ) := LinearMap.ker (x0CoeffMap u)
  let tail : K →ₗ[ℝ] (Fin 2 → ℝ) := x0TailCoeffMap u
  have hKdim : Module.finrank ℝ K = 3 := by
    simpa [K] using x0CoeffKernel_finrank_three_of_relation_x0 h0
  have hrangeFin : Module.finrank ℝ (LinearMap.range tail) = 1 := by
    simpa [tail] using hrange1
  have hkerdim : Module.finrank ℝ (LinearMap.ker tail) = 2 := by
    have hsum := LinearMap.finrank_range_add_finrank_ker tail
    rw [hKdim, hrangeFin] at hsum
    omega
  have hrange_ne_bot : LinearMap.range tail ≠ ⊥ := by
    intro hrangeBot
    rw [hrangeBot, finrank_bot] at hrangeFin
    norm_num at hrangeFin
  rcases (Submodule.ne_bot_iff _).mp hrange_ne_bot with ⟨y0, hy0mem, hy0ne⟩
  obtain ⟨d0K, hd0K⟩ := hy0mem
  let basisK : Module.Basis (Fin 2) ℝ (LinearMap.ker tail) :=
    Module.finBasisOfFinrankEq ℝ (LinearMap.ker tail) hkerdim
  let d1K0 : LinearMap.ker tail := basisK 0
  let d2K0 : LinearMap.ker tail := basisK 1
  let d1K : K := d1K0.1
  let d2K : K := d2K0.1
  have hd1K0' : tail d1K = 0 := d1K0.2
  have hd2K0' : tail d2K = 0 := d2K0.2
  have h00_d1 : MvPolynomial.coeff m00 (relationPoly u (d1K : Fin 4 → ℝ)) = 0 := by
    have h := congrArg (fun z : Fin 2 → ℝ => z 0) hd1K0'
    simpa [tail, x0TailCoeffMap] using h
  have h01_d1 : MvPolynomial.coeff m01 (relationPoly u (d1K : Fin 4 → ℝ)) = 0 := by
    have h := congrArg (fun z : Fin 2 → ℝ => z 1) hd1K0'
    simpa [tail, x0TailCoeffMap] using h
  have h00_d2 : MvPolynomial.coeff m00 (relationPoly u (d2K : Fin 4 → ℝ)) = 0 := by
    have h := congrArg (fun z : Fin 2 → ℝ => z 0) hd2K0'
    simpa [tail, x0TailCoeffMap] using h
  have h01_d2 : MvPolynomial.coeff m01 (relationPoly u (d2K : Fin 4 → ℝ)) = 0 := by
    have h := congrArg (fun z : Fin 2 → ℝ => z 1) hd2K0'
    simpa [tail, x0TailCoeffMap] using h
  have hd0_00 :
      MvPolynomial.coeff m00 (relationPoly u (d0K : Fin 4 → ℝ)) = y0 0 := by
    have h := congrArg (fun z : Fin 2 → ℝ => z 0) hd0K
    simpa [tail, x0TailCoeffMap] using h
  have hd0_01 :
      MvPolynomial.coeff m01 (relationPoly u (d0K : Fin 4 → ℝ)) = y0 1 := by
    have h := congrArg (fun z : Fin 2 → ℝ => z 1) hd0K
    simpa [tail, x0TailCoeffMap] using h
  have htail0_ne :
      (MvPolynomial.coeff m00 (relationPoly u (d0K : Fin 4 → ℝ))) ^ 2 +
          (MvPolynomial.coeff m01 (relationPoly u (d0K : Fin 4 → ℝ))) ^ 2 ≠ 0 := by
    intro hsq
    have hcoord00 : MvPolynomial.coeff m00 (relationPoly u (d0K : Fin 4 → ℝ)) = 0 := by
      nlinarith
    have hcoord01 : MvPolynomial.coeff m01 (relationPoly u (d0K : Fin 4 → ℝ)) = 0 := by
      nlinarith
    have hy00 : y0 0 = 0 := by
      linarith [hd0_00, hcoord00]
    have hy01 : y0 1 = 0 := by
      linarith [hd0_01, hcoord01]
    apply hy0ne
    ext j
    fin_cases j
    · exact hy00
    · exact hy01
  let relTail : (LinearMap.ker tail) →ₗ[ℝ] Poly :=
    (relationPolyLin u).comp
      ((Submodule.subtype K).comp (Submodule.subtype (LinearMap.ker tail)))
  have hrelTailInj : Function.Injective relTail := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply (LinearMap.ker_eq_bot.mp hrelker)
    simpa [relTail, relationPolyLin, relationPoly] using hxy
  have hrelTailBot : LinearMap.ker relTail = ⊥ := LinearMap.ker_eq_bot.mpr hrelTailInj
  have hLI : LinearIndependent ℝ (fun i : Fin 2 => relTail (basisK i)) := by
    exact basisK.linearIndependent.map' relTail hrelTailBot
  refine ⟨(d0K : Fin 4 → ℝ), (d1K : Fin 4 → ℝ), (d2K : Fin 4 → ℝ),
    d0K.2, d1K.2, d2K.2, htail0_ne, h00_d1, h01_d1, h00_d2, h01_d2, ?_⟩
  convert hLI using 1
  ext i
  fin_cases i <;> rfl

/-- In the exact-affine `dim = 1` branch, if the residual tail map on the
`x₀`-kernel has full rank `2`, then there are exact relations carrying the
normalized tails `1`, `x₁`, and one further pure homogeneous relation. -/
theorem exists_x0_tail_const_x1_hom_of_exactAffineDimOne_rangeTwo
    {u : RankFourVec}
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (hrange2 : Module.finrank ℝ (LinearMap.range (x0TailCoeffMap u)) = 2) :
    ∃ d0 d1 d2 : Fin 4 → ℝ,
      d0 ∈ LinearMap.ker (x0CoeffMap u) ∧
      d1 ∈ LinearMap.ker (x0CoeffMap u) ∧
      d2 ∈ LinearMap.ker (x0CoeffMap u) ∧
      MvPolynomial.coeff m00 (relationPoly u d0) = 1 ∧
      MvPolynomial.coeff m01 (relationPoly u d0) = 0 ∧
      MvPolynomial.coeff m00 (relationPoly u d1) = 0 ∧
      MvPolynomial.coeff m01 (relationPoly u d1) = 1 ∧
      MvPolynomial.coeff m00 (relationPoly u d2) = 0 ∧
      MvPolynomial.coeff m01 (relationPoly u d2) = 0 ∧
      relationPoly u d2 ≠ 0 := by
  let K : Submodule ℝ (Fin 4 → ℝ) := LinearMap.ker (x0CoeffMap u)
  let tail : K →ₗ[ℝ] (Fin 2 → ℝ) := x0TailCoeffMap u
  have hKdim : Module.finrank ℝ K = 3 := by
    simpa [K] using x0CoeffKernel_finrank_three_of_relation_x0 h0
  have hrangeFin : Module.finrank ℝ (LinearMap.range tail) = 2 := by
    simpa [tail] using hrange2
  have hrangeTop : LinearMap.range tail = ⊤ := by
    have hEq :
        Module.finrank ℝ (LinearMap.range tail) = Module.finrank ℝ (Fin 2 → ℝ) := by
      calc
        Module.finrank ℝ (LinearMap.range tail) = 2 := hrangeFin
        _ = Module.finrank ℝ (Fin 2 → ℝ) := by
          rw [Module.finrank_fintype_fun_eq_card]
          decide
    exact Submodule.eq_top_of_finrank_eq hEq
  obtain ⟨d0K, hd0K⟩ := LinearMap.range_eq_top.mp hrangeTop ![1, 0]
  obtain ⟨d1K, hd1K⟩ := LinearMap.range_eq_top.mp hrangeTop ![0, 1]
  have hkerdim : Module.finrank ℝ (LinearMap.ker tail) = 1 := by
    have hsum := LinearMap.finrank_range_add_finrank_ker tail
    have hsum' : 2 + Module.finrank ℝ (LinearMap.ker tail) = 3 := by
      simpa [hKdim, hrangeFin] using hsum
    have hsum'' : 2 + Module.finrank ℝ (LinearMap.ker tail) = 2 + 1 := by
      simpa using hsum'
    exact Nat.add_left_cancel hsum''
  let basisK0 : Module.Basis (Fin 1) ℝ (LinearMap.ker tail) :=
    Module.finBasisOfFinrankEq ℝ (LinearMap.ker tail) hkerdim
  let d2K0 : LinearMap.ker tail := basisK0 0
  let d2K : K := d2K0.1
  have hd2K_ne : d2K ≠ 0 := by
    intro hd2K
    apply basisK0.ne_zero 0
    exact Subtype.ext hd2K
  have hd2poly_ne : relationPoly u (d2K : Fin 4 → ℝ) ≠ 0 := by
    intro hd2poly
    have hrelInj : Function.Injective (relationPolyLin u) := LinearMap.ker_eq_bot.mp hrelker
    have hd2vec : ((d2K : K) : Fin 4 → ℝ) = 0 := by
      apply hrelInj
      simpa [relationPolyLin, relationPoly] using hd2poly
    exact hd2K_ne (Subtype.ext hd2vec)
  refine ⟨(d0K : Fin 4 → ℝ), (d1K : Fin 4 → ℝ), (d2K : Fin 4 → ℝ),
    d0K.2, d1K.2, d2K.2, ?_, ?_, ?_, ?_, ?_, ?_, hd2poly_ne⟩
  · have h := congrArg (fun z : Fin 2 → ℝ => z 0) hd0K
    simpa [tail, x0TailCoeffMap] using h
  · have h := congrArg (fun z : Fin 2 → ℝ => z 1) hd0K
    simpa [tail, x0TailCoeffMap] using h
  · have h := congrArg (fun z : Fin 2 → ℝ => z 0) hd1K
    simpa [tail, x0TailCoeffMap] using h
  · have h := congrArg (fun z : Fin 2 → ℝ => z 1) hd1K
    simpa [tail, x0TailCoeffMap] using h
  · have hd2K0' : tail d2K = 0 := d2K0.2
    have h := congrArg (fun z : Fin 2 → ℝ => z 0) hd2K0'
    simpa [tail, x0TailCoeffMap] using h
  · have hd2K0' : tail d2K = 0 := d2K0.2
    have h := congrArg (fun z : Fin 2 → ℝ => z 1) hd2K0'
    simpa [tail, x0TailCoeffMap] using h

/-- Any exact relation equal to `1` lies in the exact-affine submodule. -/
private theorem mem_exactAffineSubmodule_of_relation_eq_one
    {u : RankFourVec} {c : Fin 4 → ℝ}
    (hc : relationPoly u c = (1 : Poly)) :
    c ∈ exactAffineSubmodule u := by
  ext j
  fin_cases j
  · simpa [exactAffineSubmodule, homCoeffMap, coeff_m20_one] using
      congrArg (MvPolynomial.coeff m20) hc
  · simpa [exactAffineSubmodule, homCoeffMap, coeff_m11_one] using
      congrArg (MvPolynomial.coeff m11) hc
  · simpa [exactAffineSubmodule, homCoeffMap, coeff_m02_one] using
      congrArg (MvPolynomial.coeff m02) hc

/-- Any exact relation equal to `x₁` lies in the exact-affine submodule. -/
private theorem mem_exactAffineSubmodule_of_relation_eq_x1
    {u : RankFourVec} {c : Fin 4 → ℝ}
    (hc : relationPoly u c = x1) :
    c ∈ exactAffineSubmodule u := by
  ext j
  fin_cases j
  · simpa [exactAffineSubmodule, homCoeffMap, coeff_m20_x1] using
      congrArg (MvPolynomial.coeff m20) hc
  · simpa [exactAffineSubmodule, homCoeffMap, coeff_m11_x1] using
      congrArg (MvPolynomial.coeff m11) hc
  · simpa [exactAffineSubmodule, homCoeffMap, coeff_m02_x1] using
      congrArg (MvPolynomial.coeff m02) hc

/-- Any exact affine relation lies in the exact-affine submodule. -/
private theorem mem_exactAffineSubmodule_of_relation_eq_affineLine
    {u : RankFourVec} {c : Fin 4 → ℝ} {r a b : ℝ}
    (hc : relationPoly u c = affineLinePoly r a b) :
    c ∈ exactAffineSubmodule u := by
  ext j
  fin_cases j
  · simpa [exactAffineSubmodule, homCoeffMap, affineLinePoly,
      coeff_m20_one, coeff_m20_x0, coeff_m20_x1] using
      congrArg (MvPolynomial.coeff m20) hc
  · simpa [exactAffineSubmodule, homCoeffMap, affineLinePoly,
      coeff_m11_one, coeff_m11_x0, coeff_m11_x1] using
      congrArg (MvPolynomial.coeff m11) hc
  · simpa [exactAffineSubmodule, homCoeffMap, affineLinePoly,
      coeff_m02_one, coeff_m02_x0, coeff_m02_x1] using
      congrArg (MvPolynomial.coeff m02) hc

/-- In an exact-affine space of dimension one already containing an exact
`x₀` relation, an exact affine relation with no `x₀` term must be zero. -/
private theorem eq_zero_of_exactAffine_relation_const_x1
    {u : RankFourVec}
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 1)
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    {c : Fin 4 → ℝ} {r b : ℝ}
    (hc_mem : c ∈ exactAffineSubmodule u)
    (hc : relationPoly u c = affineLinePoly r 0 b) :
    r = 0 ∧ b = 0 := by
  have hc0mem : c0 ∈ exactAffineSubmodule u := by
    ext j
    fin_cases j
    · simpa [exactAffineSubmodule, homCoeffMap, coeff_m20_x0] using
        congrArg (MvPolynomial.coeff m20) h0
    · simpa [exactAffineSubmodule, homCoeffMap, coeff_m11_x0] using
        congrArg (MvPolynomial.coeff m11) h0
    · simpa [exactAffineSubmodule, homCoeffMap, coeff_m02_x0] using
        congrArg (MvPolynomial.coeff m02) h0
  have hc0ne : c0 ≠ 0 := by
    intro hc0
    have hzero : (0 : Poly) = x0 := by
      simpa [hc0, relationPoly] using h0
    have hcoeff := congrArg (MvPolynomial.coeff m10) hzero
    simp [x0, m10] at hcoeff
  let c0E : exactAffineSubmodule u := ⟨c0, hc0mem⟩
  have hc0E_ne : c0E ≠ 0 := by
    intro hc0E
    exact hc0ne (Subtype.ext_iff.mp hc0E)
  let cE : exactAffineSubmodule u := ⟨c, hc_mem⟩
  obtain ⟨t, ht⟩ := exists_smul_eq_of_finrank_eq_one hdim hc0E_ne cE
  have htval : (c : Fin 4 → ℝ) = t • c0 := by
    simpa using (congrArg Subtype.val ht).symm
  have hcx0 : affineLinePoly r 0 b = t • x0 := by
    calc
      affineLinePoly r 0 b = relationPoly u c := hc.symm
      _ = relationPoly u (t • c0) := by rw [htval]
      _ = t • x0 := by rw [relationPoly_smul, h0]
  have hr : r = 0 := by
    have hcoeff := congrArg (MvPolynomial.coeff m00) hcx0
    simpa [affineLinePoly, coeff_m00_x1, x0, m00, MvPolynomial.smul_eq_C_mul] using hcoeff
  have hb : b = 0 := by
    have hcoeff := congrArg (MvPolynomial.coeff m01) hcx0
    simpa [affineLinePoly, coeff_m01_one, coeff_m01_x1, x0, m01,
      MvPolynomial.smul_eq_C_mul] using hcoeff
  exact ⟨hr, hb⟩

/-- In the tail-rank `1` exact-affine `dim = 1` branch, the tail-stripped
homogeneous part of the unique tailed relation is independent from the two pure
homogeneous relations. Otherwise one would recover an exact affine relation of
the form `r + b x₁`, impossible in a one-dimensional exact-affine space already
containing `x₀`. -/
theorem exists_x0_tail_nonzero_hom_basis_of_exactAffineDimOne_rangeOne
    {u : RankFourVec}
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 1)
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (hrange1 : Module.finrank ℝ (LinearMap.range (x0TailCoeffMap u)) = 1) :
    ∃ d0 d1 d2 : Fin 4 → ℝ,
      d0 ∈ LinearMap.ker (x0CoeffMap u) ∧
      d1 ∈ LinearMap.ker (x0CoeffMap u) ∧
      d2 ∈ LinearMap.ker (x0CoeffMap u) ∧
      (MvPolynomial.coeff m00 (relationPoly u d0)) ^ 2 +
          (MvPolynomial.coeff m01 (relationPoly u d0)) ^ 2 ≠ 0 ∧
      MvPolynomial.coeff m00 (relationPoly u d1) = 0 ∧
      MvPolynomial.coeff m01 (relationPoly u d1) = 0 ∧
      MvPolynomial.coeff m00 (relationPoly u d2) = 0 ∧
      MvPolynomial.coeff m01 (relationPoly u d2) = 0 ∧
      LinearIndependent ℝ
        ![relationPoly u d0 -
            affineLinePoly
              (MvPolynomial.coeff m00 (relationPoly u d0))
              0
              (MvPolynomial.coeff m01 (relationPoly u d0)),
          relationPoly u d1,
          relationPoly u d2] := by
  rcases exists_x0_tail_nonzero_homPair_of_finrank_range_one hrelker h0 hrange1 with
    ⟨d0, d1, d2, hd0K, hd1K, hd2K, htail0_ne, h00_d1, h01_d1, h00_d2, h01_d2, hLI⟩
  let r0 : ℝ := MvPolynomial.coeff m00 (relationPoly u d0)
  let b0 : ℝ := MvPolynomial.coeff m01 (relationPoly u d0)
  have hlin :
      LinearIndependent ℝ
        ![relationPoly u d0 - affineLinePoly r0 0 b0,
          relationPoly u d1,
          relationPoly u d2] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hg' :
        g 0 • (relationPoly u d0 - affineLinePoly r0 0 b0) +
          g 1 • relationPoly u d1 +
          g 2 • relationPoly u d2 = 0 := by
      simpa [Fin.sum_univ_three] using hg
    have hc :
        relationPoly u (g 0 • d0 + g 1 • d1 + g 2 • d2) =
          affineLinePoly (g 0 * r0) 0 (g 0 * b0) := by
      calc
        relationPoly u (g 0 • d0 + g 1 • d1 + g 2 • d2)
            = g 0 • relationPoly u d0 + g 1 • relationPoly u d1 + g 2 • relationPoly u d2 := by
                rw [relationPoly_add, relationPoly_add, relationPoly_smul, relationPoly_smul,
                  relationPoly_smul]
        _ =
            (g 0 • (relationPoly u d0 - affineLinePoly r0 0 b0) +
              g 1 • relationPoly u d1 +
              g 2 • relationPoly u d2) +
              g 0 • affineLinePoly r0 0 b0 := by
                rw [smul_sub]
                abel_nf
        _ = g 0 • affineLinePoly r0 0 b0 := by rw [hg']; abel
        _ = affineLinePoly (g 0 * r0) 0 (g 0 * b0) := by
              simp [affineLinePoly, MvPolynomial.smul_eq_C_mul, smul_add]
              ring
    have hcmem :
        g 0 • d0 + g 1 • d1 + g 2 • d2 ∈ exactAffineSubmodule u := by
      exact mem_exactAffineSubmodule_of_relation_eq_affineLine hc
    have hzero01 : g 0 * r0 = 0 ∧ g 0 * b0 = 0 := by
      exact eq_zero_of_exactAffine_relation_const_x1 hdim h0 hcmem hc
    have hg0zero : g 0 = 0 := by
      have hmulr : g 0 * r0 ^ 2 = 0 := by
        calc
          g 0 * r0 ^ 2 = (g 0 * r0) * r0 := by ring
          _ = 0 := by rw [hzero01.1, zero_mul]
      have hmulb : g 0 * b0 ^ 2 = 0 := by
        calc
          g 0 * b0 ^ 2 = (g 0 * b0) * b0 := by ring
          _ = 0 := by rw [hzero01.2, zero_mul]
      have hmul : g 0 * (r0 ^ 2 + b0 ^ 2) = 0 := by
        rw [mul_add, hmulr, hmulb, zero_add]
      have htail0_ne' : r0 ^ 2 + b0 ^ 2 ≠ 0 := by
        simpa [r0, b0] using htail0_ne
      exact (mul_eq_zero.mp hmul).resolve_right htail0_ne'
    have h12 :
        g 1 • relationPoly u d1 + g 2 • relationPoly u d2 = 0 := by
      simpa [hg0zero] using hg'
    have hLI' := Fintype.linearIndependent_iff.mp hLI
    have hcoeffs :
        ∀ j : Fin 2, (![g 1, g 2] : Fin 2 → ℝ) j = 0 := by
      exact hLI' (![g 1, g 2]) (by simpa [Fin.sum_univ_two] using h12)
    fin_cases i
    · exact hg0zero
    · simpa using hcoeffs 0
    · simpa using hcoeffs 1
  exact ⟨d0, d1, d2, hd0K, hd1K, hd2K, htail0_ne, h00_d1, h01_d1, h00_d2, h01_d2, by
    simpa [r0, b0] using hlin⟩

/-- The tail-rank `1` exact-affine `dim = 1` extractor can be packaged as a
homogeneous basis matrix in the canonical basis `(x₀², x₀x₁, x₁²)`. The unique
tailed relation is first stripped of its affine tail, and the resulting
homogeneous triple has invertible coefficient matrix. -/
theorem exists_x0_tail_nonzero_hom_basis_matrix_of_exactAffineDimOne_rangeOne
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 1)
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (hrange1 : Module.finrank ℝ (LinearMap.range (x0TailCoeffMap u)) = 1) :
    ∃ d0 d1 d2 : Fin 4 → ℝ, ∃ A : Matrix (Fin 3) (Fin 3) ℝ,
      d0 ∈ LinearMap.ker (x0CoeffMap u) ∧
      d1 ∈ LinearMap.ker (x0CoeffMap u) ∧
      d2 ∈ LinearMap.ker (x0CoeffMap u) ∧
      (MvPolynomial.coeff m00 (relationPoly u d0)) ^ 2 +
          (MvPolynomial.coeff m01 (relationPoly u d0)) ^ 2 ≠ 0 ∧
      MvPolynomial.coeff m00 (relationPoly u d1) = 0 ∧
      MvPolynomial.coeff m01 (relationPoly u d1) = 0 ∧
      MvPolynomial.coeff m00 (relationPoly u d2) = 0 ∧
      MvPolynomial.coeff m01 (relationPoly u d2) = 0 ∧
      (∀ j : Fin 3,
        (![relationPoly u d0 -
              affineLinePoly
                (MvPolynomial.coeff m00 (relationPoly u d0))
                0
                (MvPolynomial.coeff m01 (relationPoly u d0)),
            relationPoly u d1,
            relationPoly u d2] : Fin 3 → Poly) j =
          ∑ k : Fin 3, A j k • homQuadBasis k) ∧
      A.det ≠ 0 := by
  rcases exists_x0_tail_nonzero_hom_basis_of_exactAffineDimOne_rangeOne
      hrelker hdim h0 hrange1 with
    ⟨d0, d1, d2, hd0K, hd1K, hd2K, htail0_ne, h00_d1, h01_d1, h00_d2, h01_d2, hqind⟩
  let r0 : ℝ := MvPolynomial.coeff m00 (relationPoly u d0)
  let b0 : ℝ := MvPolynomial.coeff m01 (relationPoly u d0)
  let q : Fin 3 → Poly := ![
    relationPoly u d0 - affineLinePoly r0 0 b0,
    relationPoly u d1,
    relationPoly u d2]
  have hq : ∀ j : Fin 3, IsQuadratic (q j) := by
    intro j
    fin_cases j
    · dsimp [q]
      simpa [sub_eq_add_neg] using
        isQuadratic_linearCombination_local
          (isQuadratic_relationPoly hu d0)
          (isQuadratic_affineLinePoly_local r0 0 b0)
          1 (-1)
    · simpa [q] using isQuadratic_relationPoly hu d1
    · simpa [q] using isQuadratic_relationPoly hu d2
  have h00 : ∀ j : Fin 3, MvPolynomial.coeff m00 (q j) = 0 := by
    intro j
    fin_cases j
    · dsimp [q, r0, b0]
      rw [MvPolynomial.coeff_sub]
      simp [affineLinePoly, coeff_m00_x1]
    · simpa [q] using h00_d1
    · simpa [q] using h00_d2
  have h10 : ∀ j : Fin 3, MvPolynomial.coeff m10 (q j) = 0 := by
    intro j
    fin_cases j
    · have hd0_10 : MvPolynomial.coeff m10 (relationPoly u d0) = 0 := by
        change x0CoeffMap u d0 = 0
        exact hd0K
      dsimp [q]
      rw [MvPolynomial.coeff_sub]
      simp [affineLinePoly, hd0_10, coeff_m10_x1]
    · have hd1_10 : MvPolynomial.coeff m10 (relationPoly u d1) = 0 := by
        change x0CoeffMap u d1 = 0
        exact hd1K
      simpa [q] using hd1_10
    · have hd2_10 : MvPolynomial.coeff m10 (relationPoly u d2) = 0 := by
        change x0CoeffMap u d2 = 0
        exact hd2K
      simpa [q] using hd2_10
  have h01 : ∀ j : Fin 3, MvPolynomial.coeff m01 (q j) = 0 := by
    intro j
    fin_cases j
    · dsimp [q, r0, b0]
      rw [MvPolynomial.coeff_sub]
      simp [affineLinePoly, coeff_m01_x1]
    · simpa [q] using h01_d1
    · simpa [q] using h01_d2
  have hqind' : LinearIndependent ℝ q := by
    simpa [q, r0, b0] using hqind
  rcases exists_homQuadBasis_matrix_of_linearIndependent hq h00 h10 h01 hqind' with
    ⟨A, hA, hdet⟩
  exact ⟨d0, d1, d2, A, hd0K, hd1K, hd2K, htail0_ne, h00_d1, h01_d1, h00_d2, h01_d2, hA,
    hdet⟩

/-- In the tail-rank `2` exact-affine `dim = 1` branch, the normalized constant
and `x₁`-tail relations cannot collapse onto the unique pure homogeneous
direction. Otherwise one would recover an exact `1` or exact `x₁` relation. -/
theorem exists_x0_tail_const_x1_hom_independent_of_exactAffineDimOne_rangeTwo
    {u : RankFourVec}
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 1)
    (hnoConst : ¬ ∃ c ∈ exactAffineSubmodule u, relationPoly u c = (1 : Poly))
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (hrange2 : Module.finrank ℝ (LinearMap.range (x0TailCoeffMap u)) = 2) :
    ∃ d0 d1 d2 : Fin 4 → ℝ,
      d0 ∈ LinearMap.ker (x0CoeffMap u) ∧
      d1 ∈ LinearMap.ker (x0CoeffMap u) ∧
      d2 ∈ LinearMap.ker (x0CoeffMap u) ∧
      MvPolynomial.coeff m00 (relationPoly u d0) = 1 ∧
      MvPolynomial.coeff m01 (relationPoly u d0) = 0 ∧
      MvPolynomial.coeff m00 (relationPoly u d1) = 0 ∧
      MvPolynomial.coeff m01 (relationPoly u d1) = 1 ∧
      MvPolynomial.coeff m00 (relationPoly u d2) = 0 ∧
      MvPolynomial.coeff m01 (relationPoly u d2) = 0 ∧
      relationPoly u d2 ≠ 0 ∧
      LinearIndependent ℝ ![relationPoly u d0 - (1 : Poly), relationPoly u d2] ∧
      LinearIndependent ℝ ![relationPoly u d1 - x1, relationPoly u d2] := by
  rcases exists_x0_tail_const_x1_hom_of_exactAffineDimOne_rangeTwo hrelker h0 hrange2 with
    ⟨d0, d1, d2, hd0K, hd1K, hd2K, hd0_00, hd0_01, hd1_00, hd1_01, hd2_00, hd2_01,
      hd2_ne⟩
  have hc0mem : c0 ∈ exactAffineSubmodule u := by
    ext j
    fin_cases j
    · simpa [exactAffineSubmodule, homCoeffMap, coeff_m20_x0] using
        congrArg (MvPolynomial.coeff m20) h0
    · simpa [exactAffineSubmodule, homCoeffMap, coeff_m11_x0] using
        congrArg (MvPolynomial.coeff m11) h0
    · simpa [exactAffineSubmodule, homCoeffMap, coeff_m02_x0] using
        congrArg (MvPolynomial.coeff m02) h0
  have hc0ne : c0 ≠ 0 := by
    intro hc0
    have hzero : (0 : Poly) = x0 := by
      simpa [hc0, relationPoly] using h0
    have hcoeff := congrArg (MvPolynomial.coeff m10) hzero
    simp [x0, m10] at hcoeff
  let c0E : exactAffineSubmodule u := ⟨c0, hc0mem⟩
  have hc0E_ne : c0E ≠ 0 := by
    intro hc0E
    apply hc0ne
    exact Subtype.ext_iff.mp hc0E
  have hlin0 :
      LinearIndependent ℝ ![relationPoly u d0 - (1 : Poly), relationPoly u d2] := by
    rw [linearIndependent_fin2]
    refine ⟨hd2_ne, ?_⟩
    intro a ha
    have ha' : a • relationPoly u d2 = relationPoly u d0 - (1 : Poly) := by
      simpa using ha
    have hone :
        relationPoly u (d0 - a • d2) = (1 : Poly) := by
      calc
        relationPoly u (d0 - a • d2)
            = relationPoly u d0 + relationPoly u ((-a) • d2) := by
                simp [sub_eq_add_neg, relationPoly_add]
        _ = relationPoly u d0 + (-a) • relationPoly u d2 := by
              rw [relationPoly_smul]
        _ = relationPoly u d0 - a • relationPoly u d2 := by
              simp [sub_eq_add_neg]
        _ = (relationPoly u d0 - (1 : Poly)) + (1 : Poly) - a • relationPoly u d2 := by
              abel
        _ = a • relationPoly u d2 + (1 : Poly) - a • relationPoly u d2 := by
              rw [ha']
        _ = (1 : Poly) := by
              abel
    exact hnoConst ⟨d0 - a • d2, mem_exactAffineSubmodule_of_relation_eq_one hone, hone⟩
  have hlin1 :
      LinearIndependent ℝ ![relationPoly u d1 - x1, relationPoly u d2] := by
    rw [linearIndependent_fin2]
    refine ⟨hd2_ne, ?_⟩
    intro a ha
    have ha' : a • relationPoly u d2 = relationPoly u d1 - x1 := by
      simpa using ha
    have hx1rel :
        relationPoly u (d1 - a • d2) = x1 := by
      calc
        relationPoly u (d1 - a • d2)
            = relationPoly u d1 + relationPoly u ((-a) • d2) := by
                simp [sub_eq_add_neg, relationPoly_add]
        _ = relationPoly u d1 + (-a) • relationPoly u d2 := by
              rw [relationPoly_smul]
        _ = relationPoly u d1 - a • relationPoly u d2 := by
              simp [sub_eq_add_neg]
        _ = (relationPoly u d1 - x1) + x1 - a • relationPoly u d2 := by
              abel
        _ = a • relationPoly u d2 + x1 - a • relationPoly u d2 := by
              rw [ha']
        _ = x1 := by
              abel
    let c1E : exactAffineSubmodule u := ⟨d1 - a • d2, mem_exactAffineSubmodule_of_relation_eq_x1 hx1rel⟩
    obtain ⟨t, ht⟩ := exists_smul_eq_of_finrank_eq_one hdim hc0E_ne c1E
    have htval : ((c1E : exactAffineSubmodule u) : Fin 4 → ℝ) = t • c0 := by
      simpa using (congrArg Subtype.val ht).symm
    have hx1eq : x1 = t • x0 := by
      calc
        x1 = relationPoly u ((c1E : exactAffineSubmodule u) : Fin 4 → ℝ) := hx1rel.symm
        _ = relationPoly u (t • c0) := by rw [htval]
        _ = t • x0 := by rw [relationPoly_smul, h0]
    have hcoeff := congrArg (MvPolynomial.coeff m01) hx1eq
    simp [x0, x1, m01] at hcoeff
  exact ⟨d0, d1, d2, hd0K, hd1K, hd2K, hd0_00, hd0_01, hd1_00, hd1_01, hd2_00, hd2_01,
    hd2_ne, hlin0, hlin1⟩

/-- In the tail-rank `2` exact-affine `dim = 1` branch, the three homogeneous
parts carried by the normalized relations are linearly independent. If a
nontrivial linear combination vanished, the corresponding relation vector would
produce an exact affine relation of the form `r + b x₁`, impossible in a
one-dimensional exact-affine space already containing `x₀`. -/
theorem exists_x0_tail_const_x1_hom_basis_of_exactAffineDimOne_rangeTwo
    {u : RankFourVec}
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 1)
    (hnoConst : ¬ ∃ c ∈ exactAffineSubmodule u, relationPoly u c = (1 : Poly))
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (hrange2 : Module.finrank ℝ (LinearMap.range (x0TailCoeffMap u)) = 2) :
    ∃ d0 d1 d2 : Fin 4 → ℝ,
      d0 ∈ LinearMap.ker (x0CoeffMap u) ∧
      d1 ∈ LinearMap.ker (x0CoeffMap u) ∧
      d2 ∈ LinearMap.ker (x0CoeffMap u) ∧
      MvPolynomial.coeff m00 (relationPoly u d0) = 1 ∧
      MvPolynomial.coeff m01 (relationPoly u d0) = 0 ∧
      MvPolynomial.coeff m00 (relationPoly u d1) = 0 ∧
      MvPolynomial.coeff m01 (relationPoly u d1) = 1 ∧
      MvPolynomial.coeff m00 (relationPoly u d2) = 0 ∧
      MvPolynomial.coeff m01 (relationPoly u d2) = 0 ∧
      relationPoly u d2 ≠ 0 ∧
      LinearIndependent ℝ
        ![relationPoly u d0 - (1 : Poly), relationPoly u d1 - x1, relationPoly u d2] := by
  rcases exists_x0_tail_const_x1_hom_independent_of_exactAffineDimOne_rangeTwo
      hrelker hdim hnoConst h0 hrange2 with
    ⟨d0, d1, d2, hd0K, hd1K, hd2K, hd0_00, hd0_01, hd1_00, hd1_01,
      hd2_00, hd2_01, hd2_ne, hlin0, hlin1⟩
  have hli :
      LinearIndependent ℝ
        ![relationPoly u d0 - (1 : Poly), relationPoly u d1 - x1, relationPoly u d2] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hg' :
        g 0 • (relationPoly u d0 - (1 : Poly)) +
          g 1 • (relationPoly u d1 - x1) +
          g 2 • relationPoly u d2 = 0 := by
      simpa [Fin.sum_univ_three] using hg
    have hsum :
        relationPoly u (g 0 • d0 + g 1 • d1 + g 2 • d2) =
          affineLinePoly (g 0) 0 (g 1) := by
      calc
        relationPoly u (g 0 • d0 + g 1 • d1 + g 2 • d2)
            = g 0 • relationPoly u d0 + g 1 • relationPoly u d1 + g 2 • relationPoly u d2 := by
                rw [relationPoly_add, relationPoly_add, relationPoly_smul, relationPoly_smul,
                  relationPoly_smul]
        _ = (g 0 • (relationPoly u d0 - (1 : Poly)) +
              g 1 • (relationPoly u d1 - x1) +
              g 2 • relationPoly u d2) +
              (g 0 • (1 : Poly) + g 1 • x1) := by
                rw [smul_sub, smul_sub]
                abel_nf
        _ = affineLinePoly (g 0) 0 (g 1) := by
              rw [hg']
              simp [affineLinePoly, MvPolynomial.smul_eq_C_mul]
    have hmem :
        g 0 • d0 + g 1 • d1 + g 2 • d2 ∈ exactAffineSubmodule u := by
      exact mem_exactAffineSubmodule_of_relation_eq_affineLine hsum
    have hzero01 : g 0 = 0 ∧ g 1 = 0 := by
      exact eq_zero_of_exactAffine_relation_const_x1 hdim h0 hmem hsum
    have hg2zero : g 2 = 0 := by
      have hzero :
          g 2 • relationPoly u d2 = 0 := by
        simpa [hzero01.1, hzero01.2] using hg'
      exact by
        rcases smul_eq_zero.mp hzero with hg2 | h2zero
        · exact hg2
        · exact False.elim (hd2_ne h2zero)
    fin_cases i
    · exact hzero01.1
    · exact hzero01.2
    · exact hg2zero
  exact ⟨d0, d1, d2, hd0K, hd1K, hd2K, hd0_00, hd0_01, hd1_00, hd1_01,
    hd2_00, hd2_01, hd2_ne, hli⟩

/-- The tail-rank `2` exact-affine `dim = 1` extractor can also be packaged as
an invertible homogeneous coefficient matrix in the canonical basis
`(x₀², x₀x₁, x₁²)`, after stripping the normalized affine tails `1` and `x₁`
from the two tailed relations. -/
theorem exists_x0_tail_const_x1_hom_basis_matrix_of_exactAffineDimOne_rangeTwo
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 1)
    (hnoConst : ¬ ∃ c ∈ exactAffineSubmodule u, relationPoly u c = (1 : Poly))
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (hrange2 : Module.finrank ℝ (LinearMap.range (x0TailCoeffMap u)) = 2) :
    ∃ d0 d1 d2 : Fin 4 → ℝ, ∃ A : Matrix (Fin 3) (Fin 3) ℝ,
      d0 ∈ LinearMap.ker (x0CoeffMap u) ∧
      d1 ∈ LinearMap.ker (x0CoeffMap u) ∧
      d2 ∈ LinearMap.ker (x0CoeffMap u) ∧
      MvPolynomial.coeff m00 (relationPoly u d0) = 1 ∧
      MvPolynomial.coeff m01 (relationPoly u d0) = 0 ∧
      MvPolynomial.coeff m00 (relationPoly u d1) = 0 ∧
      MvPolynomial.coeff m01 (relationPoly u d1) = 1 ∧
      MvPolynomial.coeff m00 (relationPoly u d2) = 0 ∧
      MvPolynomial.coeff m01 (relationPoly u d2) = 0 ∧
      relationPoly u d2 ≠ 0 ∧
      (∀ j : Fin 3,
        (![relationPoly u d0 - (1 : Poly), relationPoly u d1 - x1, relationPoly u d2] :
              Fin 3 → Poly) j =
          ∑ k : Fin 3, A j k • homQuadBasis k) ∧
      A.det ≠ 0 := by
  rcases exists_x0_tail_const_x1_hom_basis_of_exactAffineDimOne_rangeTwo
      hrelker hdim hnoConst h0 hrange2 with
    ⟨d0, d1, d2, hd0K, hd1K, hd2K, hd0_00, hd0_01, hd1_00, hd1_01,
      hd2_00, hd2_01, hd2_ne, hqind⟩
  let q : Fin 3 → Poly := ![
    relationPoly u d0 - (1 : Poly),
    relationPoly u d1 - x1,
    relationPoly u d2]
  have hq : ∀ j : Fin 3, IsQuadratic (q j) := by
    intro j
    fin_cases j
    · dsimp [q]
      simpa [sub_eq_add_neg] using
        isQuadratic_linearCombination_local
          (isQuadratic_relationPoly hu d0) isQuadratic_one_local 1 (-1)
    · dsimp [q]
      simpa [sub_eq_add_neg] using
        isQuadratic_linearCombination_local
          (isQuadratic_relationPoly hu d1) isQuadratic_x1_local 1 (-1)
    · simpa [q] using isQuadratic_relationPoly hu d2
  have h00 : ∀ j : Fin 3, MvPolynomial.coeff m00 (q j) = 0 := by
    intro j
    fin_cases j
    · dsimp [q]
      rw [MvPolynomial.coeff_sub]
      simp [hd0_00]
    · dsimp [q]
      rw [MvPolynomial.coeff_sub]
      simp [hd1_00, coeff_m00_x1]
    · simpa [q] using hd2_00
  have h10 : ∀ j : Fin 3, MvPolynomial.coeff m10 (q j) = 0 := by
    intro j
    fin_cases j
    · have hd0_10 : MvPolynomial.coeff m10 (relationPoly u d0) = 0 := by
        change x0CoeffMap u d0 = 0
        exact hd0K
      dsimp [q]
      rw [MvPolynomial.coeff_sub]
      simp [hd0_10, coeff_m10_one]
    · have hd1_10 : MvPolynomial.coeff m10 (relationPoly u d1) = 0 := by
        change x0CoeffMap u d1 = 0
        exact hd1K
      dsimp [q]
      rw [MvPolynomial.coeff_sub]
      simp [hd1_10, coeff_m10_x1]
    · have hd2_10 : MvPolynomial.coeff m10 (relationPoly u d2) = 0 := by
        change x0CoeffMap u d2 = 0
        exact hd2K
      simpa [q] using hd2_10
  have h01 : ∀ j : Fin 3, MvPolynomial.coeff m01 (q j) = 0 := by
    intro j
    fin_cases j
    · dsimp [q]
      rw [MvPolynomial.coeff_sub]
      simp [hd0_01, coeff_m01_one]
    · dsimp [q]
      rw [MvPolynomial.coeff_sub]
      simp [hd1_01, coeff_m01_x1]
    · simpa [q] using hd2_01
  have hqind' : LinearIndependent ℝ q := by
    simpa [q] using hqind
  rcases exists_homQuadBasis_matrix_of_linearIndependent hq h00 h10 h01 hqind' with
    ⟨A, hA, hdet⟩
  exact ⟨d0, d1, d2, A, hd0K, hd1K, hd2K, hd0_00, hd0_01, hd1_00, hd1_01, hd2_00, hd2_01,
    hd2_ne, hA, hdet⟩

/-- Bundled homogeneous basis matrix data for the normalized `x₀` exact-affine
`dim = 1` tail-rank `2` branch. -/
structure X0TailConstX1HomBasisMatrixData (u : RankFourVec) where
  d0 : Fin 4 → ℝ
  d1 : Fin 4 → ℝ
  d2 : Fin 4 → ℝ
  A : Matrix (Fin 3) (Fin 3) ℝ
  hd0K : d0 ∈ LinearMap.ker (x0CoeffMap u)
  hd1K : d1 ∈ LinearMap.ker (x0CoeffMap u)
  hd2K : d2 ∈ LinearMap.ker (x0CoeffMap u)
  h00_d0 : MvPolynomial.coeff m00 (relationPoly u d0) = 1
  h01_d0 : MvPolynomial.coeff m01 (relationPoly u d0) = 0
  h00_d1 : MvPolynomial.coeff m00 (relationPoly u d1) = 0
  h01_d1 : MvPolynomial.coeff m01 (relationPoly u d1) = 1
  h00_d2 : MvPolynomial.coeff m00 (relationPoly u d2) = 0
  h01_d2 : MvPolynomial.coeff m01 (relationPoly u d2) = 0
  hd2_ne : relationPoly u d2 ≠ 0
  hA :
    ∀ j : Fin 3,
      (![relationPoly u d0 - (1 : Poly),
          relationPoly u d1 - x1,
          relationPoly u d2] : Fin 3 → Poly) j =
        ∑ k : Fin 3, A j k • homQuadBasis k
  hdet : A.det ≠ 0

/-- Bundled homogeneous basis matrix data for the normalized `x₀` exact-affine
`dim = 1` tail-rank `1` branch. -/
structure X0TailHomBasisMatrixData (u : RankFourVec) where
  d0 : Fin 4 → ℝ
  d1 : Fin 4 → ℝ
  d2 : Fin 4 → ℝ
  A : Matrix (Fin 3) (Fin 3) ℝ
  hd0K : d0 ∈ LinearMap.ker (x0CoeffMap u)
  hd1K : d1 ∈ LinearMap.ker (x0CoeffMap u)
  hd2K : d2 ∈ LinearMap.ker (x0CoeffMap u)
  htail0_ne :
    (MvPolynomial.coeff m00 (relationPoly u d0)) ^ 2 +
        (MvPolynomial.coeff m01 (relationPoly u d0)) ^ 2 ≠ 0
  h00_d1 : MvPolynomial.coeff m00 (relationPoly u d1) = 0
  h01_d1 : MvPolynomial.coeff m01 (relationPoly u d1) = 0
  h00_d2 : MvPolynomial.coeff m00 (relationPoly u d2) = 0
  h01_d2 : MvPolynomial.coeff m01 (relationPoly u d2) = 0
  hA :
    ∀ j : Fin 3,
      (![relationPoly u d0 -
            affineLinePoly
              (MvPolynomial.coeff m00 (relationPoly u d0))
              0
              (MvPolynomial.coeff m01 (relationPoly u d0)),
          relationPoly u d1,
          relationPoly u d2] : Fin 3 → Poly) j =
        ∑ k : Fin 3, A j k • homQuadBasis k
  hdet : A.det ≠ 0

private theorem homQuadBasis_eq_sum_inv_mul_of_matrix
    {A : Matrix (Fin 3) (Fin 3) ℝ}
    {q : Fin 3 → Poly}
    (hA : ∀ j : Fin 3, q j = ∑ k : Fin 3, A j k • homQuadBasis k)
    (hdet : A.det ≠ 0) :
    ∀ k : Fin 3, homQuadBasis k = ∑ j : Fin 3, A⁻¹ k j • q j := by
  intro k
  have hAunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  have hmul : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hAunit
  symm
  calc
    ∑ j : Fin 3, A⁻¹ k j • q j
        = ∑ j : Fin 3, A⁻¹ k j • (∑ l : Fin 3, A j l • homQuadBasis l) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [hA j]
    _ = ∑ j : Fin 3, ∑ l : Fin 3, (A⁻¹ k j * A j l) • homQuadBasis l := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl ?_
          intro l hl
          rw [smul_smul]
    _ = ∑ l : Fin 3, (∑ j : Fin 3, A⁻¹ k j * A j l) • homQuadBasis l := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro l hl
          simpa using
            (Finset.sum_smul
              (s := (Finset.univ : Finset (Fin 3)))
              (f := fun j : Fin 3 => A⁻¹ k j * A j l)
              (x := homQuadBasis l)).symm
    _ = ∑ l : Fin 3, (A⁻¹ * A) k l • homQuadBasis l := by
          refine Finset.sum_congr rfl ?_
          intro l hl
          rw [Matrix.mul_apply]
    _ = homQuadBasis k := by
          rw [hmul]
          simp [Matrix.one_apply]

private theorem homQuadBasis_linearIndependent :
    LinearIndependent ℝ homQuadBasis := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  fin_cases i
  · have hcoeff := congrArg (MvPolynomial.coeff m20) hg
    simpa [homQuadBasis, Fin.sum_univ_three, MvPolynomial.coeff_add,
      MvPolynomial.coeff_smul, coeff_m20_x0sq, coeff_m20_x0x1, coeff_m20_x1sq] using hcoeff
  · have hcoeff := congrArg (MvPolynomial.coeff m11) hg
    simpa [homQuadBasis, Fin.sum_univ_three, MvPolynomial.coeff_add,
      MvPolynomial.coeff_smul, coeff_m11_x0sq, coeff_m11_x0x1, coeff_m11_x1sq] using hcoeff
  · have hcoeff := congrArg (MvPolynomial.coeff m02) hg
    simpa [homQuadBasis, Fin.sum_univ_three, MvPolynomial.coeff_add,
      MvPolynomial.coeff_smul, coeff_m02_x0sq, coeff_m02_x0x1, coeff_m02_x1sq] using hcoeff

private def rowToHomQuad : (Fin 3 → ℝ) →ₗ[ℝ] Poly where
  toFun v := ∑ k : Fin 3, v k • homQuadBasis k
  map_add' x y := by
    simp [Finset.sum_add_distrib, add_smul]
  map_smul' a v := by
    dsimp
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [smul_smul]

private theorem rowToHomQuad_injective :
    Function.Injective rowToHomQuad := by
  intro v w hvw
  ext i
  fin_cases i
  · have hcoeff := congrArg (MvPolynomial.coeff m20) hvw
    simpa [rowToHomQuad, homQuadBasis, Fin.sum_univ_three, MvPolynomial.coeff_add,
      MvPolynomial.coeff_smul, coeff_m20_x0sq, coeff_m20_x0x1, coeff_m20_x1sq] using hcoeff
  · have hcoeff := congrArg (MvPolynomial.coeff m11) hvw
    simpa [rowToHomQuad, homQuadBasis, Fin.sum_univ_three, MvPolynomial.coeff_add,
      MvPolynomial.coeff_smul, coeff_m11_x0sq, coeff_m11_x0x1, coeff_m11_x1sq] using hcoeff
  · have hcoeff := congrArg (MvPolynomial.coeff m02) hvw
    simpa [rowToHomQuad, homQuadBasis, Fin.sum_univ_three, MvPolynomial.coeff_add,
      MvPolynomial.coeff_smul, coeff_m02_x0sq, coeff_m02_x0x1, coeff_m02_x1sq] using hcoeff

private theorem not_linearIndependent_of_all_coeff_m20_zero
    {q : Fin 3 → Poly}
    (hq : ∀ j : Fin 3, IsQuadratic (q j))
    (h00 : ∀ j : Fin 3, MvPolynomial.coeff m00 (q j) = 0)
    (h10 : ∀ j : Fin 3, MvPolynomial.coeff m10 (q j) = 0)
    (h01 : ∀ j : Fin 3, MvPolynomial.coeff m01 (q j) = 0)
    (h20 : ∀ j : Fin 3, MvPolynomial.coeff m20 (q j) = 0) :
    ¬ LinearIndependent ℝ q := by
  intro hli
  rcases exists_homQuadBasis_matrix_of_linearIndependent hq h00 h10 h01 hli with
    ⟨A, hA, hdet⟩
  have hcol0 : ∀ j : Fin 3, A j 0 = 0 := by
    intro j
    have hcoeff := congrArg (MvPolynomial.coeff m20) (hA j)
    simpa [homQuadBasis, Fin.sum_univ_three, MvPolynomial.coeff_add,
      MvPolynomial.coeff_smul, coeff_m20_x0sq, coeff_m20_x0x1, coeff_m20_x1sq,
      h20 j] using hcoeff.symm
  have hdet0 : A.det = 0 := by
    simp [Matrix.det_fin_three, hcol0 0, hcol0 1, hcol0 2]
  exact hdet hdet0

private theorem not_linearIndependent_of_all_coeff_m02_zero
    {q : Fin 3 → Poly}
    (hq : ∀ j : Fin 3, IsQuadratic (q j))
    (h00 : ∀ j : Fin 3, MvPolynomial.coeff m00 (q j) = 0)
    (h10 : ∀ j : Fin 3, MvPolynomial.coeff m10 (q j) = 0)
    (h01 : ∀ j : Fin 3, MvPolynomial.coeff m01 (q j) = 0)
    (h02 : ∀ j : Fin 3, MvPolynomial.coeff m02 (q j) = 0) :
    ¬ LinearIndependent ℝ q := by
  intro hli
  rcases exists_homQuadBasis_matrix_of_linearIndependent hq h00 h10 h01 hli with
    ⟨A, hA, hdet⟩
  have hcol2 : ∀ j : Fin 3, A j 2 = 0 := by
    intro j
    have hcoeff := congrArg (MvPolynomial.coeff m02) (hA j)
    simpa [homQuadBasis, Fin.sum_univ_three, MvPolynomial.coeff_add,
      MvPolynomial.coeff_smul, coeff_m02_x0sq, coeff_m02_x0x1, coeff_m02_x1sq,
      h02 j] using hcoeff.symm
  have hdet0 : A.det = 0 := by
    simp [Matrix.det_fin_three, hcol2 0, hcol2 1, hcol2 2]
  exact hdet hdet0

namespace X0TailConstX1HomBasisMatrixData

/-- Tail-stripped homogeneous basis returned by the tail-rank `2` extractor. -/
def q {u : RankFourVec} (D : X0TailConstX1HomBasisMatrixData u) : Fin 3 → Poly :=
  ![relationPoly u D.d0 - (1 : Poly),
    relationPoly u D.d1 - x1,
    relationPoly u D.d2]

/-- Canonical reconstructed `x₀²` relation from the inverse homogeneous matrix. -/
def c20 {u : RankFourVec} (D : X0TailConstX1HomBasisMatrixData u) : Fin 4 → ℝ :=
  fun i => (D.A⁻¹ 0 0) * D.d0 i + (D.A⁻¹ 0 1) * D.d1 i + (D.A⁻¹ 0 2) * D.d2 i

/-- Canonical reconstructed `x₀x₁` relation from the inverse homogeneous matrix. -/
def c11 {u : RankFourVec} (D : X0TailConstX1HomBasisMatrixData u) : Fin 4 → ℝ :=
  fun i => (D.A⁻¹ 1 0) * D.d0 i + (D.A⁻¹ 1 1) * D.d1 i + (D.A⁻¹ 1 2) * D.d2 i

/-- Canonical reconstructed `x₁²` relation from the inverse homogeneous matrix. -/
def c02 {u : RankFourVec} (D : X0TailConstX1HomBasisMatrixData u) : Fin 4 → ℝ :=
  fun i => (D.A⁻¹ 2 0) * D.d0 i + (D.A⁻¹ 2 1) * D.d1 i + (D.A⁻¹ 2 2) * D.d2 i

private theorem q_eq_sum_homQuadBasis
    {u : RankFourVec} (D : X0TailConstX1HomBasisMatrixData u) :
    ∀ j : Fin 3, D.q j = ∑ k : Fin 3, D.A j k • homQuadBasis k := by
  intro j
  simpa [q] using D.hA j

private theorem hd0split
    {u : RankFourVec} (D : X0TailConstX1HomBasisMatrixData u) :
    relationPoly u D.d0 = D.q 0 + (1 : Poly) := by
  dsimp [q]
  abel

private theorem hd1split
    {u : RankFourVec} (D : X0TailConstX1HomBasisMatrixData u) :
    relationPoly u D.d1 = D.q 1 + x1 := by
  dsimp [q]
  abel

theorem q_isQuadratic
    {u : RankFourVec} (hu : IsAdmissiblePoint u) (D : X0TailConstX1HomBasisMatrixData u) :
    ∀ j : Fin 3, IsQuadratic (D.q j) := by
  intro j
  fin_cases j
  · dsimp [q]
    simpa [sub_eq_add_neg] using
      isQuadratic_linearCombination_local
        (isQuadratic_relationPoly hu D.d0) isQuadratic_one_local 1 (-1)
  · dsimp [q]
    simpa [sub_eq_add_neg] using
      isQuadratic_linearCombination_local
        (isQuadratic_relationPoly hu D.d1) isQuadratic_x1_local 1 (-1)
  · simpa [q] using isQuadratic_relationPoly hu D.d2

theorem q_coeff_m00_zero
    {u : RankFourVec} (D : X0TailConstX1HomBasisMatrixData u) :
    ∀ j : Fin 3, MvPolynomial.coeff m00 (D.q j) = 0 := by
  intro j
  fin_cases j
  · dsimp [q]
    rw [MvPolynomial.coeff_sub]
    simp [D.h00_d0]
  · dsimp [q]
    rw [MvPolynomial.coeff_sub]
    simp [D.h00_d1, coeff_m00_x1]
  · simpa [q] using D.h00_d2

theorem q_coeff_m10_zero
    {u : RankFourVec} (D : X0TailConstX1HomBasisMatrixData u) :
    ∀ j : Fin 3, MvPolynomial.coeff m10 (D.q j) = 0 := by
  intro j
  fin_cases j
  · have hd0_10 : MvPolynomial.coeff m10 (relationPoly u D.d0) = 0 := by
      change x0CoeffMap u D.d0 = 0
      exact D.hd0K
    dsimp [q]
    rw [MvPolynomial.coeff_sub]
    simp [hd0_10, coeff_m10_one]
  · have hd1_10 : MvPolynomial.coeff m10 (relationPoly u D.d1) = 0 := by
      change x0CoeffMap u D.d1 = 0
      exact D.hd1K
    dsimp [q]
    rw [MvPolynomial.coeff_sub]
    simp [hd1_10, coeff_m10_x1]
  · have hd2_10 : MvPolynomial.coeff m10 (relationPoly u D.d2) = 0 := by
      change x0CoeffMap u D.d2 = 0
      exact D.hd2K
    simpa [q] using hd2_10

theorem q_coeff_m01_zero
    {u : RankFourVec} (D : X0TailConstX1HomBasisMatrixData u) :
    ∀ j : Fin 3, MvPolynomial.coeff m01 (D.q j) = 0 := by
  intro j
  fin_cases j
  · dsimp [q]
    rw [MvPolynomial.coeff_sub]
    simp [D.h01_d0, coeff_m01_one]
  · dsimp [q]
    rw [MvPolynomial.coeff_sub]
    simp [D.h01_d1, coeff_m01_x1]
  · simpa [q] using D.h01_d2

/-- The tail-stripped homogeneous triple packaged by the tail-rank `2`
extractor is linearly independent. Equivalently, the extracted homogeneous
matrix data really is a basis of the three-dimensional homogeneous quadratic
space. -/
theorem q_linearIndependent
    {u : RankFourVec} (D : X0TailConstX1HomBasisMatrixData u) :
    LinearIndependent ℝ D.q := by
  have hrows : LinearIndependent ℝ (fun i : Fin 3 => D.A i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero D.hdet
  have hmap :
      LinearIndependent ℝ
        (fun i : Fin 3 => rowToHomQuad (D.A i)) := by
    exact hrows.map' rowToHomQuad (LinearMap.ker_eq_bot.mpr rowToHomQuad_injective)
  have hqeq : (fun i : Fin 3 => rowToHomQuad (D.A i)) = D.q := by
    funext i
    simp [rowToHomQuad, D.q_eq_sum_homQuadBasis]
  simpa [hqeq] using hmap

/-- In the normalized tail-rank `2` package, at least one tail-stripped
homogeneous relation has a nonzero `x₀²` coefficient. Otherwise the triple
would lie in the two-dimensional span of `x₀x₁` and `x₁²`, contradicting the
invertibility of the extracted homogeneous-basis matrix. -/
theorem exists_q_coeff_m20_ne_zero
    {u : RankFourVec} (hu : IsAdmissiblePoint u) (D : X0TailConstX1HomBasisMatrixData u) :
    ∃ j : Fin 3, MvPolynomial.coeff m20 (D.q j) ≠ 0 := by
  by_contra hnone
  apply
    not_linearIndependent_of_all_coeff_m20_zero
      (hq := D.q_isQuadratic hu)
      (h00 := D.q_coeff_m00_zero)
      (h10 := D.q_coeff_m10_zero)
      (h01 := D.q_coeff_m01_zero)
      (h20 := fun j => by
        by_contra hj
        exact hnone ⟨j, hj⟩)
  exact D.q_linearIndependent

/-- In the normalized tail-rank `2` package, at least one tail-stripped
homogeneous relation has a nonzero `x₁²` coefficient. Otherwise the triple
would lie in the two-dimensional span of `x₀²` and `x₀x₁`, again contradicting
the invertibility of the extracted homogeneous-basis matrix. -/
theorem exists_q_coeff_m02_ne_zero
    {u : RankFourVec} (hu : IsAdmissiblePoint u) (D : X0TailConstX1HomBasisMatrixData u) :
    ∃ j : Fin 3, MvPolynomial.coeff m02 (D.q j) ≠ 0 := by
  by_contra hnone
  apply
    not_linearIndependent_of_all_coeff_m02_zero
      (hq := D.q_isQuadratic hu)
      (h00 := D.q_coeff_m00_zero)
      (h10 := D.q_coeff_m10_zero)
      (h01 := D.q_coeff_m01_zero)
      (h02 := fun j => by
        by_contra hj
        exact hnone ⟨j, hj⟩)
  exact D.q_linearIndependent

/-- The pure pair `(q₀,q₂)` extracted from the normalized range-two data is
linearly independent. -/
theorem q02_linearIndependent
    {u : RankFourVec} (D : X0TailConstX1HomBasisMatrixData u) :
    LinearIndependent ℝ ![D.q 0, D.q 2] := by
  have hli := Fintype.linearIndependent_iff.mp D.q_linearIndependent
  rw [linearIndependent_fin2]
  constructor
  · exact (D.q_linearIndependent.ne_zero 2)
  · intro a ha
    have ha' : a • D.q 2 = D.q 0 := by
      simpa using ha
    have hzero :
        ∑ j : Fin 3, (![-1, 0, a] : Fin 3 → ℝ) j • D.q j = 0 := by
      have : (-1 : ℝ) • D.q 0 + a • D.q 2 = 0 := by
        rw [ha']
        simp
      simpa [Fin.sum_univ_three, add_assoc] using this
    have hcoeffs := hli (![-1, 0, a]) hzero
    have h0 := hcoeffs 0
    norm_num at h0

/-- The pure pair `(q₁,q₂)` extracted from the normalized range-two data is
linearly independent. -/
theorem q12_linearIndependent
    {u : RankFourVec} (D : X0TailConstX1HomBasisMatrixData u) :
    LinearIndependent ℝ ![D.q 1, D.q 2] := by
  have hli := Fintype.linearIndependent_iff.mp D.q_linearIndependent
  rw [linearIndependent_fin2]
  constructor
  · exact (D.q_linearIndependent.ne_zero 2)
  · intro a ha
    have ha' : a • D.q 2 = D.q 1 := by
      simpa using ha
    have hzero :
        ∑ j : Fin 3, (![0, -1, a] : Fin 3 → ℝ) j • D.q j = 0 := by
      have : (-1 : ℝ) • D.q 1 + a • D.q 2 = 0 := by
        rw [ha']
        simp
      simpa [Fin.sum_univ_three, add_assoc] using this
    have hcoeffs := hli (![0, -1, a]) hzero
    have h1 := hcoeffs 1
    norm_num at h1

/-- The pure pair `(q₀,q₂)` spans a genuine low-homogeneous plane. This is the
constant-tail range-two plane that will later feed the affine-rank-one
classifier routing. -/
theorem q02_plane_nontrivial
    {u : RankFourVec} (hu : IsAdmissiblePoint u) (D : X0TailConstX1HomBasisMatrixData u) :
    lowHomQuadPlaneA (D.q 0) (D.q 2) ≠ 0 ∨
      lowHomQuadPlaneB (D.q 0) (D.q 2) ≠ 0 ∨
        lowHomQuadPlaneC (D.q 0) (D.q 2) ≠ 0 := by
  have hq := D.q_isQuadratic hu
  have h00 := D.q_coeff_m00_zero
  have h10 := D.q_coeff_m10_zero
  have h01 := D.q_coeff_m01_zero
  exact lowHomQuadPlane_nontrivial_of_independent_pair
    (hq 0) (hq 2) (h00 0) (h10 0) (h01 0) (h00 2) (h10 2) (h01 2) D.q02_linearIndependent

/-- The pure pair `(q₁,q₂)` spans a genuine low-homogeneous plane. This is the
`x₁`-tail range-two plane that will later feed the affine-rank-one classifier
routing. -/
theorem q12_plane_nontrivial
    {u : RankFourVec} (hu : IsAdmissiblePoint u) (D : X0TailConstX1HomBasisMatrixData u) :
    lowHomQuadPlaneA (D.q 1) (D.q 2) ≠ 0 ∨
      lowHomQuadPlaneB (D.q 1) (D.q 2) ≠ 0 ∨
        lowHomQuadPlaneC (D.q 1) (D.q 2) ≠ 0 := by
  have hq := D.q_isQuadratic hu
  have h00 := D.q_coeff_m00_zero
  have h10 := D.q_coeff_m10_zero
  have h01 := D.q_coeff_m01_zero
  exact lowHomQuadPlane_nontrivial_of_independent_pair
    (hq 1) (hq 2) (h00 1) (h10 1) (h01 1) (h00 2) (h10 2) (h01 2) D.q12_linearIndependent

/-- The canonical reconstructed `x₀²` relation has homogeneous part exactly
`x₀²`, and its affine tail is read directly from the first two inverse-matrix
columns. -/
theorem relation_c20
    {u : RankFourVec} (D : X0TailConstX1HomBasisMatrixData u) :
    relationPoly u D.c20 =
      (D.A⁻¹ 0 0) • (1 : Poly) + (D.A⁻¹ 0 1) • x1 + x0 ^ 2 := by
  have hhom := homQuadBasis_eq_sum_inv_mul_of_matrix (q_eq_sum_homQuadBasis D) D.hdet
  calc
    relationPoly u D.c20
        = (D.A⁻¹ 0 0) • relationPoly u D.d0 +
            (D.A⁻¹ 0 1) • relationPoly u D.d1 + (D.A⁻¹ 0 2) • relationPoly u D.d2 := by
            rw [show D.c20 = (D.A⁻¹ 0 0) • D.d0 + (D.A⁻¹ 0 1) • D.d1 + (D.A⁻¹ 0 2) • D.d2 by
              funext i
              simp [c20]
            , relationPoly_add, relationPoly_add, relationPoly_smul, relationPoly_smul,
              relationPoly_smul]
    _ = (D.A⁻¹ 0 0) • (1 : Poly) + (D.A⁻¹ 0 1) • x1 + ∑ j : Fin 3, D.A⁻¹ 0 j • D.q j := by
          rw [hd0split D, hd1split D]
          rw [smul_add, smul_add]
          simp [q, Fin.sum_univ_three]
          abel
    _ = (D.A⁻¹ 0 0) • (1 : Poly) + (D.A⁻¹ 0 1) • x1 + x0 ^ 2 := by
          simpa [q] using
            congrArg
              (fun z : Poly => (D.A⁻¹ 0 0) • (1 : Poly) + (D.A⁻¹ 0 1) • x1 + z)
              (hhom 0).symm

/-- The canonical reconstructed `x₀x₁` relation has homogeneous part exactly
`x₀x₁`, and its affine tail is read directly from the first two inverse-matrix
columns. -/
theorem relation_c11
    {u : RankFourVec} (D : X0TailConstX1HomBasisMatrixData u) :
    relationPoly u D.c11 =
      (D.A⁻¹ 1 0) • (1 : Poly) + (D.A⁻¹ 1 1) • x1 + (x0 * x1 : Poly) := by
  have hhom := homQuadBasis_eq_sum_inv_mul_of_matrix (q_eq_sum_homQuadBasis D) D.hdet
  calc
    relationPoly u D.c11
        = (D.A⁻¹ 1 0) • relationPoly u D.d0 +
            (D.A⁻¹ 1 1) • relationPoly u D.d1 + (D.A⁻¹ 1 2) • relationPoly u D.d2 := by
            rw [show D.c11 = (D.A⁻¹ 1 0) • D.d0 + (D.A⁻¹ 1 1) • D.d1 + (D.A⁻¹ 1 2) • D.d2 by
              funext i
              simp [c11]
            , relationPoly_add, relationPoly_add, relationPoly_smul, relationPoly_smul,
              relationPoly_smul]
    _ = (D.A⁻¹ 1 0) • (1 : Poly) + (D.A⁻¹ 1 1) • x1 + ∑ j : Fin 3, D.A⁻¹ 1 j • D.q j := by
          rw [hd0split D, hd1split D]
          rw [smul_add, smul_add]
          simp [q, Fin.sum_univ_three]
          abel
    _ = (D.A⁻¹ 1 0) • (1 : Poly) + (D.A⁻¹ 1 1) • x1 + (x0 * x1 : Poly) := by
          simpa [q] using
            congrArg
              (fun z : Poly => (D.A⁻¹ 1 0) • (1 : Poly) + (D.A⁻¹ 1 1) • x1 + z)
              (hhom 1).symm

/-- The canonical reconstructed `x₁²` relation has homogeneous part exactly
`x₁²`, and its affine tail is read directly from the first two inverse-matrix
columns. -/
theorem relation_c02
    {u : RankFourVec} (D : X0TailConstX1HomBasisMatrixData u) :
    relationPoly u D.c02 =
      (D.A⁻¹ 2 0) • (1 : Poly) + (D.A⁻¹ 2 1) • x1 + x1 ^ 2 := by
  have hhom := homQuadBasis_eq_sum_inv_mul_of_matrix (q_eq_sum_homQuadBasis D) D.hdet
  calc
    relationPoly u D.c02
        = (D.A⁻¹ 2 0) • relationPoly u D.d0 +
            (D.A⁻¹ 2 1) • relationPoly u D.d1 + (D.A⁻¹ 2 2) • relationPoly u D.d2 := by
            rw [show D.c02 = (D.A⁻¹ 2 0) • D.d0 + (D.A⁻¹ 2 1) • D.d1 + (D.A⁻¹ 2 2) • D.d2 by
              funext i
              simp [c02]
            , relationPoly_add, relationPoly_add, relationPoly_smul, relationPoly_smul,
              relationPoly_smul]
    _ = (D.A⁻¹ 2 0) • (1 : Poly) + (D.A⁻¹ 2 1) • x1 + ∑ j : Fin 3, D.A⁻¹ 2 j • D.q j := by
          rw [hd0split D, hd1split D]
          rw [smul_add, smul_add]
          simp [q, Fin.sum_univ_three]
          abel
    _ = (D.A⁻¹ 2 0) • (1 : Poly) + (D.A⁻¹ 2 1) • x1 + x1 ^ 2 := by
          simpa [q] using
            congrArg
              (fun z : Poly => (D.A⁻¹ 2 0) • (1 : Poly) + (D.A⁻¹ 2 1) • x1 + z)
              (hhom 2).symm

end X0TailConstX1HomBasisMatrixData

namespace X0TailHomBasisMatrixData

/-- The affine tail lands on exactly one canonical quadratic direction. -/
def SingleSupport {u : RankFourVec} (D : X0TailHomBasisMatrixData u) : Prop :=
  (D.A⁻¹ 0 0 ≠ 0 ∧ D.A⁻¹ 1 0 = 0 ∧ D.A⁻¹ 2 0 = 0) ∨
    (D.A⁻¹ 0 0 = 0 ∧ D.A⁻¹ 1 0 ≠ 0 ∧ D.A⁻¹ 2 0 = 0) ∨
      (D.A⁻¹ 0 0 = 0 ∧ D.A⁻¹ 1 0 = 0 ∧ D.A⁻¹ 2 0 ≠ 0)

/-- The affine tail has no `x₀²` component but is still nontrivial. -/
def M20Zero {u : RankFourVec} (D : X0TailHomBasisMatrixData u) : Prop :=
  D.A⁻¹ 0 0 = 0 ∧ (D.A⁻¹ 1 0 ≠ 0 ∨ D.A⁻¹ 2 0 ≠ 0)

/-- The already-solved tail-rank `1` matrix branches: either exact
single-support, or the whole `m20 = 0` slice. -/
def SimpleBranch {u : RankFourVec} (D : X0TailHomBasisMatrixData u) : Prop :=
  D.SingleSupport ∨ D.M20Zero

/-- Constant coefficient of the unique tailed relation in the extracted basis. -/
def r0 {u : RankFourVec} (D : X0TailHomBasisMatrixData u) : ℝ :=
  MvPolynomial.coeff m00 (relationPoly u D.d0)

/-- `x₁` coefficient of the unique tailed relation in the extracted basis. -/
def b0 {u : RankFourVec} (D : X0TailHomBasisMatrixData u) : ℝ :=
  MvPolynomial.coeff m01 (relationPoly u D.d0)

/-- Tail-stripped homogeneous basis returned by the extractor. -/
def q {u : RankFourVec} (D : X0TailHomBasisMatrixData u) : Fin 3 → Poly :=
  ![relationPoly u D.d0 - affineLinePoly D.r0 0 D.b0,
    relationPoly u D.d1,
    relationPoly u D.d2]

/-- Canonical reconstructed `x₀²` relation from the inverse homogeneous matrix. -/
def c20 {u : RankFourVec} (D : X0TailHomBasisMatrixData u) : Fin 4 → ℝ :=
  fun i => (D.A⁻¹ 0 0) * D.d0 i + (D.A⁻¹ 0 1) * D.d1 i + (D.A⁻¹ 0 2) * D.d2 i

/-- Canonical reconstructed `x₀x₁` relation from the inverse homogeneous matrix. -/
def c11 {u : RankFourVec} (D : X0TailHomBasisMatrixData u) : Fin 4 → ℝ :=
  fun i => (D.A⁻¹ 1 0) * D.d0 i + (D.A⁻¹ 1 1) * D.d1 i + (D.A⁻¹ 1 2) * D.d2 i

/-- Canonical reconstructed `x₁²` relation from the inverse homogeneous matrix. -/
def c02 {u : RankFourVec} (D : X0TailHomBasisMatrixData u) : Fin 4 → ℝ :=
  fun i => (D.A⁻¹ 2 0) * D.d0 i + (D.A⁻¹ 2 1) * D.d1 i + (D.A⁻¹ 2 2) * D.d2 i

/-- Common affine-tail scale obtained by pairing the first inverse column with
itself. -/
def tailScale {u : RankFourVec} (D : X0TailHomBasisMatrixData u) : ℝ :=
  (D.A⁻¹ 0 0) ^ 2 + (D.A⁻¹ 1 0) ^ 2 + (D.A⁻¹ 2 0) ^ 2

/-- Tailed annihilator quadratic built from the first inverse-matrix column. -/
def ann {u : RankFourVec} (D : X0TailHomBasisMatrixData u) : Fin 4 → ℝ :=
  fun i =>
    (D.A⁻¹ 0 0) * D.c20 i + (D.A⁻¹ 1 0) * D.c11 i + (D.A⁻¹ 2 0) * D.c02 i

/-- First pure homogeneous complement to the annihilator quadratic. -/
def comp11 {u : RankFourVec} (D : X0TailHomBasisMatrixData u) : Fin 4 → ℝ :=
  fun i => (D.A⁻¹ 1 0) * D.c20 i - (D.A⁻¹ 0 0) * D.c11 i

/-- Second pure homogeneous complement to the annihilator quadratic. -/
def comp02 {u : RankFourVec} (D : X0TailHomBasisMatrixData u) : Fin 4 → ℝ :=
  fun i => (D.A⁻¹ 2 0) * D.c20 i - (D.A⁻¹ 0 0) * D.c02 i

private theorem q_eq_sum_homQuadBasis
    {u : RankFourVec} (D : X0TailHomBasisMatrixData u) :
    ∀ j : Fin 3, D.q j = ∑ k : Fin 3, D.A j k • homQuadBasis k := by
  intro j
  simpa [q, r0, b0] using D.hA j

private theorem hd0split
    {u : RankFourVec} (D : X0TailHomBasisMatrixData u) :
    relationPoly u D.d0 = D.q 0 + affineLinePoly D.r0 0 D.b0 := by
  dsimp [q, r0, b0]
  abel

/-- The canonical reconstructed `x₀²` relation has homogeneous part exactly
`x₀²`, and its affine tail lies on the same extracted affine line. -/
theorem relation_c20
    {u : RankFourVec} (D : X0TailHomBasisMatrixData u) :
    relationPoly u D.c20 =
      (D.A⁻¹ 0 0 * D.r0) • (1 : Poly) + (D.A⁻¹ 0 0 * D.b0) • x1 + x0 ^ 2 := by
  have hhom := homQuadBasis_eq_sum_inv_mul_of_matrix (q_eq_sum_homQuadBasis D) D.hdet
  calc
    relationPoly u D.c20
        = (D.A⁻¹ 0 0) • relationPoly u D.d0 +
            (D.A⁻¹ 0 1) • relationPoly u D.d1 + (D.A⁻¹ 0 2) • relationPoly u D.d2 := by
            rw [show D.c20 = (D.A⁻¹ 0 0) • D.d0 + (D.A⁻¹ 0 1) • D.d1 + (D.A⁻¹ 0 2) • D.d2 by
              funext i
              simp [c20]
            , relationPoly_add, relationPoly_add, relationPoly_smul, relationPoly_smul,
              relationPoly_smul]
    _ = (D.A⁻¹ 0 0) • affineLinePoly D.r0 0 D.b0 + ∑ j : Fin 3, D.A⁻¹ 0 j • D.q j := by
          rw [hd0split D]
          rw [smul_add]
          simp [q, Fin.sum_univ_three]
          abel
    _ = (D.A⁻¹ 0 0) • affineLinePoly D.r0 0 D.b0 + x0 ^ 2 := by
          simpa [q] using
            congrArg (fun z : Poly => (D.A⁻¹ 0 0) • affineLinePoly D.r0 0 D.b0 + z) (hhom 0).symm
    _ = (D.A⁻¹ 0 0 * D.r0) • (1 : Poly) + (D.A⁻¹ 0 0 * D.b0) • x1 + x0 ^ 2 := by
          simp [affineLinePoly, MvPolynomial.smul_eq_C_mul, mul_comm, mul_left_comm, add_assoc]

/-- The canonical reconstructed `x₀x₁` relation has homogeneous part exactly
`x₀x₁`, and its affine tail lies on the same extracted affine line. -/
theorem relation_c11
    {u : RankFourVec} (D : X0TailHomBasisMatrixData u) :
    relationPoly u D.c11 =
      (D.A⁻¹ 1 0 * D.r0) • (1 : Poly) + (D.A⁻¹ 1 0 * D.b0) • x1 + (x0 * x1 : Poly) := by
  have hhom := homQuadBasis_eq_sum_inv_mul_of_matrix (q_eq_sum_homQuadBasis D) D.hdet
  calc
    relationPoly u D.c11
        = (D.A⁻¹ 1 0) • relationPoly u D.d0 +
            (D.A⁻¹ 1 1) • relationPoly u D.d1 + (D.A⁻¹ 1 2) • relationPoly u D.d2 := by
            rw [show D.c11 = (D.A⁻¹ 1 0) • D.d0 + (D.A⁻¹ 1 1) • D.d1 + (D.A⁻¹ 1 2) • D.d2 by
              funext i
              simp [c11]
            , relationPoly_add, relationPoly_add, relationPoly_smul, relationPoly_smul,
              relationPoly_smul]
    _ = (D.A⁻¹ 1 0) • affineLinePoly D.r0 0 D.b0 + ∑ j : Fin 3, D.A⁻¹ 1 j • D.q j := by
          rw [hd0split D]
          rw [smul_add]
          simp [q, Fin.sum_univ_three]
          abel
    _ = (D.A⁻¹ 1 0) • affineLinePoly D.r0 0 D.b0 + (x0 * x1 : Poly) := by
          simpa [q] using
            congrArg (fun z : Poly => (D.A⁻¹ 1 0) • affineLinePoly D.r0 0 D.b0 + z) (hhom 1).symm
    _ = (D.A⁻¹ 1 0 * D.r0) • (1 : Poly) + (D.A⁻¹ 1 0 * D.b0) • x1 + (x0 * x1 : Poly) := by
          simp [affineLinePoly, MvPolynomial.smul_eq_C_mul, mul_comm, mul_left_comm, add_assoc]

/-- The canonical reconstructed `x₁²` relation has homogeneous part exactly
`x₁²`, and its affine tail lies on the same extracted affine line. -/
theorem relation_c02
    {u : RankFourVec} (D : X0TailHomBasisMatrixData u) :
    relationPoly u D.c02 =
      (D.A⁻¹ 2 0 * D.r0) • (1 : Poly) + (D.A⁻¹ 2 0 * D.b0) • x1 + x1 ^ 2 := by
  have hhom := homQuadBasis_eq_sum_inv_mul_of_matrix (q_eq_sum_homQuadBasis D) D.hdet
  calc
    relationPoly u D.c02
        = (D.A⁻¹ 2 0) • relationPoly u D.d0 +
            (D.A⁻¹ 2 1) • relationPoly u D.d1 + (D.A⁻¹ 2 2) • relationPoly u D.d2 := by
            rw [show D.c02 = (D.A⁻¹ 2 0) • D.d0 + (D.A⁻¹ 2 1) • D.d1 + (D.A⁻¹ 2 2) • D.d2 by
              funext i
              simp [c02]
            , relationPoly_add, relationPoly_add, relationPoly_smul, relationPoly_smul,
              relationPoly_smul]
    _ = (D.A⁻¹ 2 0) • affineLinePoly D.r0 0 D.b0 + ∑ j : Fin 3, D.A⁻¹ 2 j • D.q j := by
          rw [hd0split D]
          rw [smul_add]
          simp [q, Fin.sum_univ_three]
          abel
    _ = (D.A⁻¹ 2 0) • affineLinePoly D.r0 0 D.b0 + x1 ^ 2 := by
          simpa [q] using
            congrArg (fun z : Poly => (D.A⁻¹ 2 0) • affineLinePoly D.r0 0 D.b0 + z) (hhom 2).symm
    _ = (D.A⁻¹ 2 0 * D.r0) • (1 : Poly) + (D.A⁻¹ 2 0 * D.b0) • x1 + x1 ^ 2 := by
          simp [affineLinePoly, MvPolynomial.smul_eq_C_mul, mul_comm, mul_left_comm, add_assoc]

/-- In the `A⁻¹₂₀ = 0` cross-complement branch, the canonical reconstructed
`x₁²` relation is already pure. -/
theorem relation_c02_of_h20_zero
    {u : RankFourVec} (D : X0TailHomBasisMatrixData u)
    (h20 : D.A⁻¹ 2 0 = 0) :
    relationPoly u D.c02 = x1 ^ 2 := by
  rw [relation_c02, h20]
  simp

/-- In the `A⁻¹₂₀ = 0`, `r₀ = 0` branch, the canonical `x₀²` relation
normalizes to a pure `x₁` tail plus an `x₀²` term. -/
theorem relation_c20_normalized_x1Tail_of_h20_zero_r0_zero
    {u : RankFourVec} (D : X0TailHomBasisMatrixData u)
    (h00_ne : D.A⁻¹ 0 0 ≠ 0)
    (_h20 : D.A⁻¹ 2 0 = 0)
    (hr0 : D.r0 = 0) :
    relationPoly u (((D.A⁻¹ 0 0 * D.b0)⁻¹) • D.c20) =
      x1 + ((D.A⁻¹ 0 0 * D.b0)⁻¹) • (x0 ^ 2 : Poly) := by
  have hb0 : D.b0 ≠ 0 := by
    have htail0_ne' : D.r0 ^ 2 + D.b0 ^ 2 ≠ 0 := by
      simpa [X0TailHomBasisMatrixData.r0, X0TailHomBasisMatrixData.b0] using D.htail0_ne
    intro hb0
    apply htail0_ne'
    simp [hr0, hb0]
  calc
    relationPoly u (((D.A⁻¹ 0 0 * D.b0)⁻¹) • D.c20)
        = ((D.A⁻¹ 0 0 * D.b0)⁻¹) • relationPoly u D.c20 := by
            rw [relationPoly_smul]
    _ = ((D.A⁻¹ 0 0 * D.b0)⁻¹) •
          ((D.A⁻¹ 0 0 * D.r0) • (1 : Poly) + (D.A⁻¹ 0 0 * D.b0) • x1 + x0 ^ 2) := by
          rw [relation_c20]
    _ = ((D.A⁻¹ 0 0 * D.b0)⁻¹) • ((D.A⁻¹ 0 0 * D.b0) • x1) +
          ((D.A⁻¹ 0 0 * D.b0)⁻¹) • (x0 ^ 2 : Poly) := by
          rw [hr0]
          simp [smul_add]
    _ = x1 + ((D.A⁻¹ 0 0 * D.b0)⁻¹) • (x0 ^ 2 : Poly) := by
          rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero h00_ne hb0), one_smul]

/-- In the `A⁻¹₂₀ = 0`, `r₀ = 0` branch, the canonical `x₀x₁` relation
normalizes to the same pure `x₁` tail plus an `x₀x₁` term. -/
theorem relation_c11_normalized_x1Tail_of_h20_zero_r0_zero
    {u : RankFourVec} (D : X0TailHomBasisMatrixData u)
    (h10_ne : D.A⁻¹ 1 0 ≠ 0)
    (hr0 : D.r0 = 0) :
    relationPoly u (((D.A⁻¹ 1 0 * D.b0)⁻¹) • D.c11) =
      x1 + ((D.A⁻¹ 1 0 * D.b0)⁻¹) • (x0 * x1 : Poly) := by
  have hb0 : D.b0 ≠ 0 := by
    have htail0_ne' : D.r0 ^ 2 + D.b0 ^ 2 ≠ 0 := by
      simpa [X0TailHomBasisMatrixData.r0, X0TailHomBasisMatrixData.b0] using D.htail0_ne
    intro hb0
    apply htail0_ne'
    simp [hr0, hb0]
  calc
    relationPoly u (((D.A⁻¹ 1 0 * D.b0)⁻¹) • D.c11)
        = ((D.A⁻¹ 1 0 * D.b0)⁻¹) • relationPoly u D.c11 := by
            rw [relationPoly_smul]
    _ = ((D.A⁻¹ 1 0 * D.b0)⁻¹) •
          ((D.A⁻¹ 1 0 * D.r0) • (1 : Poly) + (D.A⁻¹ 1 0 * D.b0) • x1 + (x0 * x1 : Poly)) := by
          rw [relation_c11]
    _ = ((D.A⁻¹ 1 0 * D.b0)⁻¹) • ((D.A⁻¹ 1 0 * D.b0) • x1) +
          ((D.A⁻¹ 1 0 * D.b0)⁻¹) • (x0 * x1 : Poly) := by
          rw [hr0]
          simp [smul_add]
    _ = x1 + ((D.A⁻¹ 1 0 * D.b0)⁻¹) • (x0 * x1 : Poly) := by
          rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero h10_ne hb0), one_smul]

/-- In the `A⁻¹₂₀ = 0`, `r₀ ≠ 0` branch, the canonical `x₀²` relation
normalizes to a mixed constant-plus-`x₁` tail plus an `x₀²` term. -/
theorem relation_c20_normalized_onePlusBX1_of_h20_zero_r0_ne_zero
    {u : RankFourVec} (D : X0TailHomBasisMatrixData u)
    (h00_ne : D.A⁻¹ 0 0 ≠ 0)
    (_h20 : D.A⁻¹ 2 0 = 0)
    (hr0 : D.r0 ≠ 0) :
    relationPoly u (((D.A⁻¹ 0 0 * D.r0)⁻¹) • D.c20) =
      (1 : Poly) + (D.b0 / D.r0) • x1 +
        ((D.A⁻¹ 0 0 * D.r0)⁻¹) • (x0 ^ 2 : Poly) := by
  calc
    relationPoly u (((D.A⁻¹ 0 0 * D.r0)⁻¹) • D.c20)
        = ((D.A⁻¹ 0 0 * D.r0)⁻¹) • relationPoly u D.c20 := by
            rw [relationPoly_smul]
    _ = ((D.A⁻¹ 0 0 * D.r0)⁻¹) •
          ((D.A⁻¹ 0 0 * D.r0) • (1 : Poly) + (D.A⁻¹ 0 0 * D.b0) • x1 + x0 ^ 2) := by
          rw [relation_c20]
    _ = ((D.A⁻¹ 0 0 * D.r0)⁻¹) • ((D.A⁻¹ 0 0 * D.r0) • (1 : Poly)) +
          ((D.A⁻¹ 0 0 * D.r0)⁻¹) • ((D.A⁻¹ 0 0 * D.b0) • x1) +
          ((D.A⁻¹ 0 0 * D.r0)⁻¹) • (x0 ^ 2 : Poly) := by
          simp [smul_add, add_assoc]
    _ = (1 : Poly) + (D.b0 / D.r0) • x1 +
          ((D.A⁻¹ 0 0 * D.r0)⁻¹) • (x0 ^ 2 : Poly) := by
          rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero h00_ne hr0), one_smul, smul_smul]
          have hlin :
              ((D.A⁻¹ 0 0 * D.r0)⁻¹ * (D.A⁻¹ 0 0 * D.b0)) • x1 =
                (D.b0 / D.r0) • x1 := by
            congr 1
            field_simp [h00_ne, hr0]
          rw [hlin]

/-- In the `A⁻¹₂₀ = 0`, `r₀ ≠ 0` branch, the canonical `x₀x₁` relation
normalizes to the same mixed constant-plus-`x₁` tail plus an `x₀x₁` term. -/
theorem relation_c11_normalized_onePlusBX1_of_h20_zero_r0_ne_zero
    {u : RankFourVec} (D : X0TailHomBasisMatrixData u)
    (h10_ne : D.A⁻¹ 1 0 ≠ 0)
    (hr0 : D.r0 ≠ 0) :
    relationPoly u (((D.A⁻¹ 1 0 * D.r0)⁻¹) • D.c11) =
      (1 : Poly) + (D.b0 / D.r0) • x1 +
        ((D.A⁻¹ 1 0 * D.r0)⁻¹) • (x0 * x1 : Poly) := by
  calc
    relationPoly u (((D.A⁻¹ 1 0 * D.r0)⁻¹) • D.c11)
        = ((D.A⁻¹ 1 0 * D.r0)⁻¹) • relationPoly u D.c11 := by
            rw [relationPoly_smul]
    _ = ((D.A⁻¹ 1 0 * D.r0)⁻¹) •
          ((D.A⁻¹ 1 0 * D.r0) • (1 : Poly) + (D.A⁻¹ 1 0 * D.b0) • x1 + (x0 * x1 : Poly)) := by
          rw [relation_c11]
    _ = ((D.A⁻¹ 1 0 * D.r0)⁻¹) • ((D.A⁻¹ 1 0 * D.r0) • (1 : Poly)) +
          ((D.A⁻¹ 1 0 * D.r0)⁻¹) • ((D.A⁻¹ 1 0 * D.b0) • x1) +
          ((D.A⁻¹ 1 0 * D.r0)⁻¹) • (x0 * x1 : Poly) := by
          simp [smul_add, add_assoc]
    _ = (1 : Poly) + (D.b0 / D.r0) • x1 +
          ((D.A⁻¹ 1 0 * D.r0)⁻¹) • (x0 * x1 : Poly) := by
          rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero h10_ne hr0), one_smul, smul_smul]
          have hlin :
              ((D.A⁻¹ 1 0 * D.r0)⁻¹ * (D.A⁻¹ 1 0 * D.b0)) • x1 =
                (D.b0 / D.r0) • x1 := by
            congr 1
            field_simp [h10_ne, hr0]
          rw [hlin]

/-- The first complementary relation is pure homogeneous in the plane
`span(x₀²,x₀x₁)`. -/
theorem relation_comp11
    {u : RankFourVec} (D : X0TailHomBasisMatrixData u) :
    relationPoly u D.comp11 =
      (D.A⁻¹ 1 0) • (x0 ^ 2 : Poly) - (D.A⁻¹ 0 0) • (x0 * x1 : Poly) := by
  calc
    relationPoly u D.comp11
        = (D.A⁻¹ 1 0) • relationPoly u D.c20 + (-(D.A⁻¹ 0 0)) • relationPoly u D.c11 := by
            rw [show D.comp11 = (D.A⁻¹ 1 0) • D.c20 + (-(D.A⁻¹ 0 0)) • D.c11 by
                funext i
                simp [comp11, sub_eq_add_neg]
              , relationPoly_add, relationPoly_smul, relationPoly_smul]
    _ =
        (D.A⁻¹ 1 0) • ((D.A⁻¹ 0 0 * D.r0) • (1 : Poly) + (D.A⁻¹ 0 0 * D.b0) • x1 + x0 ^ 2) +
          (-(D.A⁻¹ 0 0)) •
            ((D.A⁻¹ 1 0 * D.r0) • (1 : Poly) + (D.A⁻¹ 1 0 * D.b0) • x1 + (x0 * x1 : Poly)) := by
          rw [relation_c20, relation_c11]
    _ = (D.A⁻¹ 1 0) • (x0 ^ 2 : Poly) - (D.A⁻¹ 0 0) • (x0 * x1 : Poly) := by
          simp [smul_add, smul_smul, sub_eq_add_neg, mul_left_comm, add_assoc,
            add_left_comm, add_comm]

/-- The second complementary relation is pure homogeneous in the plane
`span(x₀²,x₁²)`. -/
theorem relation_comp02
    {u : RankFourVec} (D : X0TailHomBasisMatrixData u) :
    relationPoly u D.comp02 =
      (D.A⁻¹ 2 0) • (x0 ^ 2 : Poly) - (D.A⁻¹ 0 0) • (x1 ^ 2 : Poly) := by
  calc
    relationPoly u D.comp02
        = (D.A⁻¹ 2 0) • relationPoly u D.c20 + (-(D.A⁻¹ 0 0)) • relationPoly u D.c02 := by
            rw [show D.comp02 = (D.A⁻¹ 2 0) • D.c20 + (-(D.A⁻¹ 0 0)) • D.c02 by
                funext i
                simp [comp02, sub_eq_add_neg]
              , relationPoly_add, relationPoly_smul, relationPoly_smul]
    _ =
        (D.A⁻¹ 2 0) • ((D.A⁻¹ 0 0 * D.r0) • (1 : Poly) + (D.A⁻¹ 0 0 * D.b0) • x1 + x0 ^ 2) +
          (-(D.A⁻¹ 0 0)) •
            ((D.A⁻¹ 2 0 * D.r0) • (1 : Poly) + (D.A⁻¹ 2 0 * D.b0) • x1 + x1 ^ 2) := by
          rw [relation_c20, relation_c02]
    _ = (D.A⁻¹ 2 0) • (x0 ^ 2 : Poly) - (D.A⁻¹ 0 0) • (x1 ^ 2 : Poly) := by
          simp [smul_add, smul_smul, sub_eq_add_neg, mul_left_comm, add_assoc,
            add_left_comm, add_comm]

theorem coeff_m20_relation_comp11
    {u : RankFourVec} (D : X0TailHomBasisMatrixData u) :
    MvPolynomial.coeff m20 (relationPoly u D.comp11) = D.A⁻¹ 1 0 := by
  rw [relation_comp11, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
    MvPolynomial.coeff_smul, coeff_m20_x0sq, coeff_m20_x0x1]
  simp

theorem coeff_m11_relation_comp11
    {u : RankFourVec} (D : X0TailHomBasisMatrixData u) :
    MvPolynomial.coeff m11 (relationPoly u D.comp11) = -D.A⁻¹ 0 0 := by
  rw [relation_comp11, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
    MvPolynomial.coeff_smul, coeff_m11_x0sq, coeff_m11_x0x1]
  simp

theorem coeff_m02_relation_comp11
    {u : RankFourVec} (D : X0TailHomBasisMatrixData u) :
    MvPolynomial.coeff m02 (relationPoly u D.comp11) = 0 := by
  rw [relation_comp11, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
    MvPolynomial.coeff_smul, coeff_m02_x0sq, coeff_m02_x0x1]
  simp

theorem coeff_m20_relation_comp02
    {u : RankFourVec} (D : X0TailHomBasisMatrixData u) :
    MvPolynomial.coeff m20 (relationPoly u D.comp02) = D.A⁻¹ 2 0 := by
  rw [relation_comp02, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
    MvPolynomial.coeff_smul, coeff_m20_x0sq, coeff_m20_x1sq]
  simp

theorem coeff_m11_relation_comp02
    {u : RankFourVec} (D : X0TailHomBasisMatrixData u) :
    MvPolynomial.coeff m11 (relationPoly u D.comp02) = 0 := by
  rw [relation_comp02, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
    MvPolynomial.coeff_smul, coeff_m11_x0sq, coeff_m11_x1sq]
  simp

theorem coeff_m02_relation_comp02
    {u : RankFourVec} (D : X0TailHomBasisMatrixData u) :
    MvPolynomial.coeff m02 (relationPoly u D.comp02) = -D.A⁻¹ 0 0 := by
  rw [relation_comp02, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
    MvPolynomial.coeff_smul, coeff_m02_x0sq, coeff_m02_x1sq]
  simp

theorem lowHomQuadPlaneA_comp11_comp02
    {u : RankFourVec} (D : X0TailHomBasisMatrixData u) :
    lowHomQuadPlaneA (relationPoly u D.comp11) (relationPoly u D.comp02) =
      (D.A⁻¹ 0 0) ^ 2 := by
  rw [lowHomQuadPlaneA, coeff_m11_relation_comp11, coeff_m02_relation_comp02,
    coeff_m02_relation_comp11, coeff_m11_relation_comp02]
  ring

theorem lowHomQuadPlaneB_comp11_comp02
    {u : RankFourVec} (D : X0TailHomBasisMatrixData u) :
    lowHomQuadPlaneB (relationPoly u D.comp11) (relationPoly u D.comp02) =
      -(D.A⁻¹ 0 0) * D.A⁻¹ 1 0 := by
  rw [lowHomQuadPlaneB, coeff_m20_relation_comp11, coeff_m02_relation_comp02,
    coeff_m02_relation_comp11, coeff_m20_relation_comp02]
  ring

theorem lowHomQuadPlaneC_comp11_comp02
    {u : RankFourVec} (D : X0TailHomBasisMatrixData u) :
    lowHomQuadPlaneC (relationPoly u D.comp11) (relationPoly u D.comp02) =
      D.A⁻¹ 0 0 * D.A⁻¹ 2 0 := by
  rw [lowHomQuadPlaneC, coeff_m20_relation_comp11, coeff_m11_relation_comp02,
    coeff_m11_relation_comp11, coeff_m20_relation_comp02]
  ring

theorem lowHomQuadPlaneA_comp11_comp02_ne_zero_of_h00_ne
    {u : RankFourVec} (D : X0TailHomBasisMatrixData u)
    (h00_ne : D.A⁻¹ 0 0 ≠ 0) :
    lowHomQuadPlaneA (relationPoly u D.comp11) (relationPoly u D.comp02) ≠ 0 := by
  rw [lowHomQuadPlaneA_comp11_comp02]
  exact pow_ne_zero 2 h00_ne

theorem comp11_comp02_diagTerm_eq
    {u : RankFourVec} (D : X0TailHomBasisMatrixData u)
    (h00_ne : D.A⁻¹ 0 0 ≠ 0) :
    lowHomQuadPlaneC (relationPoly u D.comp11) (relationPoly u D.comp02) -
        lowHomQuadPlaneB (relationPoly u D.comp11) (relationPoly u D.comp02) ^ 2 /
          lowHomQuadPlaneA (relationPoly u D.comp11) (relationPoly u D.comp02) =
      D.A⁻¹ 0 0 * D.A⁻¹ 2 0 - (D.A⁻¹ 1 0) ^ 2 := by
  have hfrac :
      (-(D.A⁻¹ 0 0) * D.A⁻¹ 1 0) ^ 2 / (D.A⁻¹ 0 0) ^ 2 = (D.A⁻¹ 1 0) ^ 2 := by
    apply (div_eq_iff (pow_ne_zero 2 h00_ne)).2
    ring
  rw [lowHomQuadPlaneC_comp11_comp02, lowHomQuadPlaneB_comp11_comp02,
    lowHomQuadPlaneA_comp11_comp02, hfrac]

/-- The annihilator quadratic built from the first inverse homogeneous column
has homogeneous part exactly `mixedAffineAnnihilator`, with the common affine
tail scaled by the squared column norm. -/
theorem relation_ann
    {u : RankFourVec} (D : X0TailHomBasisMatrixData u) :
    relationPoly u D.ann =
      D.tailScale • affineLinePoly D.r0 0 D.b0 +
        mixedAffineAnnihilator (D.A⁻¹ 0 0) (D.A⁻¹ 1 0) (D.A⁻¹ 2 0) := by
  calc
    relationPoly u D.ann
        = (D.A⁻¹ 0 0) • relationPoly u D.c20 +
            (D.A⁻¹ 1 0) • relationPoly u D.c11 +
            (D.A⁻¹ 2 0) • relationPoly u D.c02 := by
            rw [show D.ann =
                (D.A⁻¹ 0 0) • D.c20 + (D.A⁻¹ 1 0) • D.c11 + (D.A⁻¹ 2 0) • D.c02 by
                  funext i
                  simp [ann]
                , relationPoly_add, relationPoly_add, relationPoly_smul,
                  relationPoly_smul, relationPoly_smul]
    _ =
        (D.A⁻¹ 0 0) •
            ((D.A⁻¹ 0 0 * D.r0) • (1 : Poly) + (D.A⁻¹ 0 0 * D.b0) • x1 + x0 ^ 2) +
          (D.A⁻¹ 1 0) •
            ((D.A⁻¹ 1 0 * D.r0) • (1 : Poly) + (D.A⁻¹ 1 0 * D.b0) • x1 +
              (x0 * x1 : Poly)) +
          (D.A⁻¹ 2 0) •
            ((D.A⁻¹ 2 0 * D.r0) • (1 : Poly) + (D.A⁻¹ 2 0 * D.b0) • x1 + x1 ^ 2) := by
          rw [relation_c20, relation_c11, relation_c02]
    _ =
        ((D.A⁻¹ 0 0) ^ 2 + (D.A⁻¹ 1 0) ^ 2 + (D.A⁻¹ 2 0) ^ 2) • affineLinePoly D.r0 0 D.b0 +
          mixedAffineAnnihilator (D.A⁻¹ 0 0) (D.A⁻¹ 1 0) (D.A⁻¹ 2 0) := by
          set a : ℝ := D.A⁻¹ 0 0
          set b : ℝ := D.A⁻¹ 1 0
          set c : ℝ := D.A⁻¹ 2 0
          have hCr0 : MvPolynomial.C D.r0 = D.r0 • (1 : Poly) := by
            simpa using
              (show MvPolynomial.C D.r0 * (1 : Poly) = D.r0 • (1 : Poly) from
                MvPolynomial.C_mul')
          have hAff :
              affineLinePoly D.r0 0 D.b0 = D.r0 • (1 : Poly) + D.b0 • x1 := by
            simp [affineLinePoly, hCr0, MvPolynomial.C_mul']
          have hQuad :
              mixedAffineAnnihilator a b c =
                a • (x0 ^ 2 : Poly) + b • (x0 * x1 : Poly) + c • (x1 ^ 2 : Poly) := by
            simp [mixedAffineAnnihilator, MvPolynomial.C_mul', add_assoc]
          have hConst :
              a • ((a * D.r0) • (1 : Poly)) +
                  b • ((b * D.r0) • (1 : Poly)) +
                  c • ((c * D.r0) • (1 : Poly)) =
                (a ^ 2 + b ^ 2 + c ^ 2) • (D.r0 • (1 : Poly)) := by
            rw [smul_smul, smul_smul, smul_smul, smul_smul, ← add_smul, ← add_smul]
            congr 1
            ring
          have hX1 :
              a • ((a * D.b0) • x1) +
                  b • ((b * D.b0) • x1) +
                  c • ((c * D.b0) • x1) =
                (a ^ 2 + b ^ 2 + c ^ 2) • (D.b0 • x1) := by
            rw [smul_smul, smul_smul, smul_smul, smul_smul, ← add_smul, ← add_smul]
            congr 1
            ring
          calc
            a • ((a * D.r0) • (1 : Poly) + (a * D.b0) • x1 + x0 ^ 2) +
                b • ((b * D.r0) • (1 : Poly) + (b * D.b0) • x1 + (x0 * x1 : Poly)) +
                c • ((c * D.r0) • (1 : Poly) + (c * D.b0) • x1 + x1 ^ 2)
                =
                  (a • ((a * D.r0) • (1 : Poly)) +
                      b • ((b * D.r0) • (1 : Poly)) +
                      c • ((c * D.r0) • (1 : Poly))) +
                    (a • ((a * D.b0) • x1) +
                      b • ((b * D.b0) • x1) +
                      c • ((c * D.b0) • x1)) +
                    (a • (x0 ^ 2 : Poly) +
                      b • (x0 * x1 : Poly) +
                      c • (x1 ^ 2 : Poly)) := by
                    rw [smul_add, smul_add, smul_add, smul_add, smul_add, smul_add]
                    abel_nf
            _ =
                  (a ^ 2 + b ^ 2 + c ^ 2) • (D.r0 • (1 : Poly)) +
                    (a ^ 2 + b ^ 2 + c ^ 2) • (D.b0 • x1) +
                    (a • (x0 ^ 2 : Poly) +
                      b • (x0 * x1 : Poly) +
                      c • (x1 ^ 2 : Poly)) := by
                    rw [hConst, hX1]
            _ =
                  (a ^ 2 + b ^ 2 + c ^ 2) • (D.r0 • (1 : Poly) + D.b0 • x1) +
                    (a • (x0 ^ 2 : Poly) +
                      b • (x0 * x1 : Poly) +
                      c • (x1 ^ 2 : Poly)) := by
                    rw [← smul_add]
            _ =
                  (a ^ 2 + b ^ 2 + c ^ 2) • affineLinePoly D.r0 0 D.b0 +
                    mixedAffineAnnihilator a b c := by
                    rw [← hAff, ← hQuad]

/-- The common affine-tail scale is automatically nonzero whenever the `x₀²`
entry of the first inverse homogeneous column is nonzero. -/
theorem tailScale_ne_zero_of_h00_ne
    {u : RankFourVec} (D : X0TailHomBasisMatrixData u)
    (h00_ne : D.A⁻¹ 0 0 ≠ 0) :
    D.tailScale ≠ 0 := by
  dsimp [tailScale]
  intro hzero
  have hsq0 : (D.A⁻¹ 0 0) ^ 2 = 0 := by
    nlinarith
  exact h00_ne (eq_zero_of_pow_eq_zero hsq0)

/-- If the extracted affine tail has zero constant term, its `x₁` coefficient
is automatically nonzero. -/
theorem b0_ne_zero_of_r0_zero
    {u : RankFourVec} (D : X0TailHomBasisMatrixData u)
    (hr0 : D.r0 = 0) :
    D.b0 ≠ 0 := by
  have htail0_ne' : D.r0 ^ 2 + D.b0 ^ 2 ≠ 0 := by
    simpa [X0TailHomBasisMatrixData.r0, X0TailHomBasisMatrixData.b0] using D.htail0_ne
  intro hb0
  apply htail0_ne'
  simp [hr0, hb0]

/-- In the `r₀ = 0` branch, the canonical annihilator normalizes to a pure
`x₁`-tail relation. -/
theorem relation_ann_normalized_x1Tail
    {u : RankFourVec} (D : X0TailHomBasisMatrixData u)
    (h00_ne : D.A⁻¹ 0 0 ≠ 0)
    (hr0 : D.r0 = 0) :
    relationPoly u (((D.tailScale * D.b0)⁻¹) • D.ann) =
      x1 + ((D.tailScale * D.b0)⁻¹) •
        mixedAffineAnnihilator (D.A⁻¹ 0 0) (D.A⁻¹ 1 0) (D.A⁻¹ 2 0) := by
  have hs_ne : D.tailScale ≠ 0 := tailScale_ne_zero_of_h00_ne D h00_ne
  have hb0 : D.b0 ≠ 0 := b0_ne_zero_of_r0_zero D hr0
  calc
    relationPoly u (((D.tailScale * D.b0)⁻¹) • D.ann)
        = ((D.tailScale * D.b0)⁻¹) • relationPoly u D.ann := by
            rw [relationPoly_smul]
    _ = ((D.tailScale * D.b0)⁻¹) •
          (D.tailScale • affineLinePoly D.r0 0 D.b0 +
            mixedAffineAnnihilator (D.A⁻¹ 0 0) (D.A⁻¹ 1 0) (D.A⁻¹ 2 0)) := by
          rw [relation_ann]
    _ = ((D.tailScale * D.b0)⁻¹) • (D.tailScale • affineLinePoly D.r0 0 D.b0) +
          ((D.tailScale * D.b0)⁻¹) •
            mixedAffineAnnihilator (D.A⁻¹ 0 0) (D.A⁻¹ 1 0) (D.A⁻¹ 2 0) := by
          rw [smul_add]
    _ = ((D.tailScale * D.b0)⁻¹) • ((D.tailScale * D.b0) • x1) +
          ((D.tailScale * D.b0)⁻¹) •
            mixedAffineAnnihilator (D.A⁻¹ 0 0) (D.A⁻¹ 1 0) (D.A⁻¹ 2 0) := by
          rw [hr0]
          simp [affineLinePoly, MvPolynomial.C_mul', smul_smul, mul_assoc]
    _ = x1 + ((D.tailScale * D.b0)⁻¹) •
          mixedAffineAnnihilator (D.A⁻¹ 0 0) (D.A⁻¹ 1 0) (D.A⁻¹ 2 0) := by
          rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero hs_ne hb0), one_smul]

/-- In the `r₀ ≠ 0` branch, the canonical annihilator normalizes to a mixed
constant-plus-`x₁` tail relation. -/
theorem relation_ann_normalized_onePlusBX1
    {u : RankFourVec} (D : X0TailHomBasisMatrixData u)
    (h00_ne : D.A⁻¹ 0 0 ≠ 0)
    (hr0 : D.r0 ≠ 0) :
    relationPoly u (((D.tailScale * D.r0)⁻¹) • D.ann) =
      (1 : Poly) + (D.b0 / D.r0) • x1 +
        ((D.tailScale * D.r0)⁻¹) •
          mixedAffineAnnihilator (D.A⁻¹ 0 0) (D.A⁻¹ 1 0) (D.A⁻¹ 2 0) := by
  have hs_ne : D.tailScale ≠ 0 := tailScale_ne_zero_of_h00_ne D h00_ne
  calc
    relationPoly u (((D.tailScale * D.r0)⁻¹) • D.ann)
        = ((D.tailScale * D.r0)⁻¹) • relationPoly u D.ann := by
            rw [relationPoly_smul]
    _ = ((D.tailScale * D.r0)⁻¹) •
          (D.tailScale • affineLinePoly D.r0 0 D.b0 +
            mixedAffineAnnihilator (D.A⁻¹ 0 0) (D.A⁻¹ 1 0) (D.A⁻¹ 2 0)) := by
          rw [relation_ann]
    _ = ((D.tailScale * D.r0)⁻¹) • (D.tailScale • affineLinePoly D.r0 0 D.b0) +
          ((D.tailScale * D.r0)⁻¹) •
            mixedAffineAnnihilator (D.A⁻¹ 0 0) (D.A⁻¹ 1 0) (D.A⁻¹ 2 0) := by
          rw [smul_add]
    _ = ((D.tailScale * D.r0)⁻¹) •
          ((D.tailScale * D.r0) • (1 : Poly) + (D.tailScale * D.b0) • x1) +
          ((D.tailScale * D.r0)⁻¹) •
            mixedAffineAnnihilator (D.A⁻¹ 0 0) (D.A⁻¹ 1 0) (D.A⁻¹ 2 0) := by
          simp [affineLinePoly, MvPolynomial.smul_eq_C_mul, mul_assoc]
    _ = (1 : Poly) + (D.b0 / D.r0) • x1 +
          ((D.tailScale * D.r0)⁻¹) •
            mixedAffineAnnihilator (D.A⁻¹ 0 0) (D.A⁻¹ 1 0) (D.A⁻¹ 2 0) := by
          rw [smul_add, smul_smul, smul_smul]
          have hconst : ((D.tailScale * D.r0)⁻¹ * (D.tailScale * D.r0)) • (1 : Poly) = (1 : Poly) := by
            rw [inv_mul_cancel₀ (mul_ne_zero hs_ne hr0), one_smul]
          have hlin :
              ((D.tailScale * D.r0)⁻¹ * (D.tailScale * D.b0)) • x1 =
                (D.b0 / D.r0) • x1 := by
            congr 1
            have hcancel : (D.tailScale * D.r0)⁻¹ * D.tailScale = D.r0⁻¹ := by
              field_simp [hs_ne, hr0]
            calc
              (D.tailScale * D.r0)⁻¹ * (D.tailScale * D.b0)
                  = ((D.tailScale * D.r0)⁻¹ * D.tailScale) * D.b0 := by ring
              _ = D.r0⁻¹ * D.b0 := by rw [hcancel]
              _ = D.b0 / D.r0 := by rw [div_eq_mul_inv, mul_comm]
          rw [hconst, hlin]

/-- Specialization of `mixedAffineAnnihilator_normal_form_cases` to the first
inverse homogeneous column of the exact-affine tail-rank `1` extractor, with
the already-solved pure `x₀²` support removed. This is the remaining normal
form split for the mixed-support `A⁻¹₀₀ ≠ 0` branch. -/
theorem mixedAffineAnnihilator_normal_form_cases_of_h00_ne_hmixed
    {u : RankFourVec} (D : X0TailHomBasisMatrixData u)
    (_h00_ne : D.A⁻¹ 0 0 ≠ 0)
    (hmixed : D.A⁻¹ 1 0 ≠ 0 ∨ D.A⁻¹ 2 0 ≠ 0) :
    (D.A⁻¹ 2 0 = 0 ∧ D.A⁻¹ 1 0 ≠ 0 ∧
      affineHom (x1ShearMatrix (-(D.A⁻¹ 0 0 / D.A⁻¹ 1 0))) 0
        (mixedAffineAnnihilator (D.A⁻¹ 0 0) (D.A⁻¹ 1 0) (D.A⁻¹ 2 0)) =
          mixedAffineAnnihilator 0 (D.A⁻¹ 1 0) 0) ∨
    (D.A⁻¹ 2 0 ≠ 0 ∧
      let d := D.A⁻¹ 0 0 - (D.A⁻¹ 1 0) ^ 2 / (4 * D.A⁻¹ 2 0)
      (d = 0 ∧
        affineHom (x1ShearMatrix (-(D.A⁻¹ 1 0 / (2 * D.A⁻¹ 2 0)))) 0
          (mixedAffineAnnihilator (D.A⁻¹ 0 0) (D.A⁻¹ 1 0) (D.A⁻¹ 2 0)) =
            mixedAffineAnnihilator 0 0 (D.A⁻¹ 2 0)) ∨
      (0 < d / D.A⁻¹ 2 0 ∧
        affineHom (x1ScaleMatrix (Real.sqrt (d / D.A⁻¹ 2 0))) 0
          (affineHom (x1ShearMatrix (-(D.A⁻¹ 1 0 / (2 * D.A⁻¹ 2 0)))) 0
            (mixedAffineAnnihilator (D.A⁻¹ 0 0) (D.A⁻¹ 1 0) (D.A⁻¹ 2 0))) =
              mixedAffineAnnihilator d 0 d) ∨
      (0 < (-d) / D.A⁻¹ 2 0 ∧
        affineHom (x1ScaleMatrix (Real.sqrt ((-d) / D.A⁻¹ 2 0))) 0
          (affineHom (x1ShearMatrix (-(D.A⁻¹ 1 0 / (2 * D.A⁻¹ 2 0)))) 0
            (mixedAffineAnnihilator (D.A⁻¹ 0 0) (D.A⁻¹ 1 0) (D.A⁻¹ 2 0))) =
              mixedAffineAnnihilator d 0 (-d))) := by
  rcases mixedAffineAnnihilator_normal_form_cases
      (D.A⁻¹ 0 0) (D.A⁻¹ 1 0) (D.A⁻¹ 2 0) with
    hsingle | hrest
  · rcases hsingle with ⟨h20, h11, _⟩
    exfalso
    rcases hmixed with h10_ne | h20_ne
    · exact h10_ne h11
    · exact h20_ne h20
  · rcases hrest with hcross | hdiag
    · left
      rcases hcross with ⟨h20, h10_ne, hcross⟩
      exact ⟨h20, h10_ne, hcross⟩
    · right
      rcases hdiag with ⟨h20_ne, hdiag⟩
      exact ⟨h20_ne, hdiag⟩

end X0TailHomBasisMatrixData

/-- Canonical choice of the tail-rank `2` homogeneous basis matrix data in the
normalized `x₀` exact-affine `dim = 1` branch. -/
noncomputable def exactAffineDimOneRangeTwoData
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 1)
    (hnoConst : ¬ ∃ c ∈ exactAffineSubmodule u, relationPoly u c = (1 : Poly))
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (hrange2 : Module.finrank ℝ (LinearMap.range (x0TailCoeffMap u)) = 2) :
    X0TailConstX1HomBasisMatrixData u := by
  classical
  let h :=
    exists_x0_tail_const_x1_hom_basis_matrix_of_exactAffineDimOne_rangeTwo
      hu hrelker hdim hnoConst h0 hrange2
  let d0 := Classical.choose h
  let h1 := Classical.choose_spec h
  let d1 := Classical.choose h1
  let h2 := Classical.choose_spec h1
  let d2 := Classical.choose h2
  let h3 := Classical.choose_spec h2
  let A := Classical.choose h3
  let hAdata := Classical.choose_spec h3
  have hd0K : d0 ∈ LinearMap.ker (x0CoeffMap u) := hAdata.1
  have hd1K : d1 ∈ LinearMap.ker (x0CoeffMap u) := hAdata.2.1
  have hd2K : d2 ∈ LinearMap.ker (x0CoeffMap u) := hAdata.2.2.1
  have h00_d0 : MvPolynomial.coeff m00 (relationPoly u d0) = 1 := hAdata.2.2.2.1
  have h01_d0 : MvPolynomial.coeff m01 (relationPoly u d0) = 0 := hAdata.2.2.2.2.1
  have h00_d1 : MvPolynomial.coeff m00 (relationPoly u d1) = 0 := hAdata.2.2.2.2.2.1
  have h01_d1 : MvPolynomial.coeff m01 (relationPoly u d1) = 1 := hAdata.2.2.2.2.2.2.1
  have h00_d2 : MvPolynomial.coeff m00 (relationPoly u d2) = 0 := hAdata.2.2.2.2.2.2.2.1
  have h01_d2 : MvPolynomial.coeff m01 (relationPoly u d2) = 0 := hAdata.2.2.2.2.2.2.2.2.1
  have hd2_ne : relationPoly u d2 ≠ 0 := hAdata.2.2.2.2.2.2.2.2.2.1
  have hA :
      ∀ j : Fin 3,
        (![relationPoly u d0 - (1 : Poly),
            relationPoly u d1 - x1,
            relationPoly u d2] : Fin 3 → Poly) j =
          ∑ k : Fin 3, A j k • homQuadBasis k := hAdata.2.2.2.2.2.2.2.2.2.2.1
  have hdet : A.det ≠ 0 := hAdata.2.2.2.2.2.2.2.2.2.2.2
  exact
    { d0 := d0
      d1 := d1
      d2 := d2
      A := A
      hd0K := hd0K
      hd1K := hd1K
      hd2K := hd2K
      h00_d0 := h00_d0
      h01_d0 := h01_d0
      h00_d1 := h00_d1
      h01_d1 := h01_d1
      h00_d2 := h00_d2
      h01_d2 := h01_d2
      hd2_ne := hd2_ne
      hA := hA
      hdet := hdet }

/-- In the exact-affine `dim = 1`, tail-rank `2` branch, if the affine tails on
the reconstructed `x₀²` and `x₀x₁` relations are independent, the branch closes
by the direct affine-tail image theorem. -/
theorem residual_eq_zero_of_relations_x0_tail_const_x1_hom_basis_matrix_generic
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (D : X0TailConstX1HomBasisMatrixData u)
    (hdetTail :
      D.A⁻¹ 0 0 * D.A⁻¹ 1 1 - D.A⁻¹ 0 1 * D.A⁻¹ 1 0 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact
    residual_eq_zero_of_relations_x0_affineTail_x0sq_affineTail_x0x1_affineTail_x1sq
      (B := B) (u := u) hu
      (c0 := c0) (c1 := D.c20) (c2 := D.c11) (c3 := D.c02)
      (a := D.A⁻¹ 0 0) (b := D.A⁻¹ 0 1) (c := D.A⁻¹ 1 0) (d := D.A⁻¹ 1 1)
      (e := D.A⁻¹ 2 0) (f := D.A⁻¹ 2 1)
      hdetTail
      (by simpa [relationPoly] using h0)
      (by simpa [relationPoly] using X0TailConstX1HomBasisMatrixData.relation_c20 D)
      (by simpa [relationPoly] using X0TailConstX1HomBasisMatrixData.relation_c11 D)
      (by simpa [relationPoly] using X0TailConstX1HomBasisMatrixData.relation_c02 D)
      hp hsocp

/-- Generic tail-rank `2` closure above the normalized exact-affine `dim = 1`
extractor: if the reconstructed `x₀²` and `x₀x₁` affine tails are independent,
Lean now closes directly from the extracted matrix data. -/
theorem residual_eq_zero_of_exactAffineDimOne_tailRangeTwo_generic
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 1)
    (hnoConst : ¬ ∃ c ∈ exactAffineSubmodule u, relationPoly u c = (1 : Poly))
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (hrange2 : Module.finrank ℝ (LinearMap.range (x0TailCoeffMap u)) = 2)
    (hdetTail :
      (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 0 0 *
          (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 1 1 -
        (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 0 1 *
          (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 1 0 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let D := exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2
  exact residual_eq_zero_of_relations_x0_tail_const_x1_hom_basis_matrix_generic
    (B := B) (u := u) hu h0 D hdetTail hp hsocp

/-- In the complementary determinant-zero tail-rank `2` branch, if the
reconstructed `x₀²` tail is nontrivial, the bundled matrix data already yields
an exact shared-tail representative family after an internal `x₁`-shear. This
packages the representative normalization theorem at the extractor level. -/
theorem exists_relations_x0_tail_const_x1_hom_basis_matrix_sharedTail_shear_normalized
    {u : RankFourVec}
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (D : X0TailConstX1HomBasisMatrixData u)
    (hdetTail : D.A⁻¹ 0 0 * D.A⁻¹ 1 1 - D.A⁻¹ 0 1 * D.A⁻¹ 1 0 = 0)
    (htail : D.A⁻¹ 0 0 ≠ 0 ∨ D.A⁻¹ 0 1 ≠ 0) :
    ∃ g : ℝ, ∃ c20' c11' c02' : Fin 4 → ℝ,
      relationPoly (mapVec (x1ShearEquiv g).toAlgHom u) c0 = x0 ∧
      relationPoly (mapVec (x1ShearEquiv g).toAlgHom u) c20' =
        (D.A⁻¹ 0 0) • (1 : Poly) + (D.A⁻¹ 0 1) • x1 + x0 ^ 2 ∧
      relationPoly (mapVec (x1ShearEquiv g).toAlgHom u) c11' = x0 * x1 ∧
      relationPoly (mapVec (x1ShearEquiv g).toAlgHom u) c02' =
        (D.A⁻¹ 2 0 - g ^ 2 * D.A⁻¹ 0 0) • (1 : Poly) +
          (D.A⁻¹ 2 1 - g ^ 2 * D.A⁻¹ 0 1) • x1 + x1 ^ 2 := by
  rcases htail with h00 | h01
  · let g : ℝ := D.A⁻¹ 1 0 / D.A⁻¹ 0 0
    have hg10 : D.A⁻¹ 1 0 = g * D.A⁻¹ 0 0 := by
      dsimp [g]
      field_simp [h00]
    have hg11 : D.A⁻¹ 1 1 = g * D.A⁻¹ 0 1 := by
      apply mul_right_cancel₀ h00
      dsimp [g]
      field_simp [h00]
      nlinarith [hdetTail]
    rcases
        relations_x0_affineTail_x0sq_sharedTail_x0x1_affineTail_x1sq_shear_normalized
          (u := u) (c0 := c0) (c1 := D.c20) (c2 := D.c11) (c3 := D.c02)
          (a := D.A⁻¹ 0 0) (b := D.A⁻¹ 0 1) (e := D.A⁻¹ 2 0) (f := D.A⁻¹ 2 1) (g := g)
          (by simpa [relationPoly] using h0)
          (by simpa [relationPoly] using X0TailConstX1HomBasisMatrixData.relation_c20 D)
          (by simpa [hg10, hg11, relationPoly] using
            X0TailConstX1HomBasisMatrixData.relation_c11 D)
          (by simpa [relationPoly] using X0TailConstX1HomBasisMatrixData.relation_c02 D)
      with ⟨c20', c11', c02', h0', h20', h11', h02'⟩
    exact ⟨g, c20', c11', c02', h0', h20', h11', h02'⟩
  · let g : ℝ := D.A⁻¹ 1 1 / D.A⁻¹ 0 1
    have hg11 : D.A⁻¹ 1 1 = g * D.A⁻¹ 0 1 := by
      dsimp [g]
      field_simp [h01]
    have hg10 : D.A⁻¹ 1 0 = g * D.A⁻¹ 0 0 := by
      apply mul_right_cancel₀ h01
      dsimp [g]
      field_simp [h01]
      nlinarith [hdetTail]
    rcases
        relations_x0_affineTail_x0sq_sharedTail_x0x1_affineTail_x1sq_shear_normalized
          (u := u) (c0 := c0) (c1 := D.c20) (c2 := D.c11) (c3 := D.c02)
          (a := D.A⁻¹ 0 0) (b := D.A⁻¹ 0 1) (e := D.A⁻¹ 2 0) (f := D.A⁻¹ 2 1) (g := g)
          (by simpa [relationPoly] using h0)
          (by simpa [relationPoly] using X0TailConstX1HomBasisMatrixData.relation_c20 D)
          (by simpa [hg10, hg11, relationPoly] using
            X0TailConstX1HomBasisMatrixData.relation_c11 D)
          (by simpa [relationPoly] using X0TailConstX1HomBasisMatrixData.relation_c02 D)
      with ⟨c20', c11', c02', h0', h20', h11', h02'⟩
    exact ⟨g, c20', c11', c02', h0', h20', h11', h02'⟩

/-- In the exact-affine `dim = 1`, tail-rank `2` determinant-zero branch, if
the normalized discriminant
\[
  a^2 - a b f + b^2 e
\]
is nonzero, the shared-tail normalization theorem reduces directly to the new
representative full-image theorem for
\[
  x_0,\ a+b x_1+x_0^2,\ x_0x_1,\ e+f x_1+x_1^2.
\]
-/
theorem residual_eq_zero_of_relations_x0_tail_const_x1_hom_basis_matrix_sharedTail_disc_ne_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (D : X0TailConstX1HomBasisMatrixData u)
    (hdetTail : D.A⁻¹ 0 0 * D.A⁻¹ 1 1 - D.A⁻¹ 0 1 * D.A⁻¹ 1 0 = 0)
    (hdisc :
      D.A⁻¹ 0 0 ^ 2 - D.A⁻¹ 0 0 * D.A⁻¹ 0 1 * D.A⁻¹ 2 1 + D.A⁻¹ 0 1 ^ 2 * D.A⁻¹ 2 0 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have htail : D.A⁻¹ 0 0 ≠ 0 ∨ D.A⁻¹ 0 1 ≠ 0 := by
    by_contra htail
    have htail' := not_or.mp htail
    have h00 : D.A⁻¹ 0 0 = 0 := not_not.mp htail'.1
    have h01 : D.A⁻¹ 0 1 = 0 := not_not.mp htail'.2
    apply hdisc
    simp [h00, h01]
  rcases
      exists_relations_x0_tail_const_x1_hom_basis_matrix_sharedTail_shear_normalized
        (u := u) (c0 := c0) h0 D hdetTail htail
    with ⟨g, c20', c11', c02', h0', h20', h11', h02'⟩
  let e : Poly ≃ₐ[ℝ] Poly := x1ShearEquiv g
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q) := by
    intro q hq
    exact isQuadratic_affineEquiv (x1ShearMatrix g) (x1ShearInvMatrix g) 0 0
      (x1Shear_mul_inv g) (x1Shear_inv_mul g) (by intro i; simp) (by intro i; simp) hq
  have heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q) := by
    intro q hq
    exact isQuadratic_affineEquiv_symm (x1ShearMatrix g) (x1ShearInvMatrix g) 0 0
      (x1Shear_mul_inv g) (x1Shear_inv_mul g) (by intro i; simp) (by intro i; simp) hq
  have heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q) := by
    intro q hq
    exact isQuartic_affineEquiv (x1ShearMatrix g) (x1ShearInvMatrix g) 0 0
      (x1Shear_mul_inv g) (x1Shear_inv_mul g) (by intro i; simp) (by intro i; simp) hq
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hdisc0 :
      D.A⁻¹ 0 0 ^ 2 -
          D.A⁻¹ 0 0 * D.A⁻¹ 0 1 * (D.A⁻¹ 2 1 - g ^ 2 * D.A⁻¹ 0 1) +
            D.A⁻¹ 0 1 ^ 2 * (D.A⁻¹ 2 0 - g ^ 2 * D.A⁻¹ 0 0) ≠ 0 := by
    have hEq :
        D.A⁻¹ 0 0 ^ 2 -
            D.A⁻¹ 0 0 * D.A⁻¹ 0 1 * (D.A⁻¹ 2 1 - g ^ 2 * D.A⁻¹ 0 1) +
              D.A⁻¹ 0 1 ^ 2 * (D.A⁻¹ 2 0 - g ^ 2 * D.A⁻¹ 0 0) =
          D.A⁻¹ 0 0 ^ 2 -
            D.A⁻¹ 0 0 * D.A⁻¹ 0 1 * D.A⁻¹ 2 1 +
              D.A⁻¹ 0 1 ^ 2 * D.A⁻¹ 2 0 := by
      ring
    exact hEq.symm ▸ hdisc
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact
      residual_eq_zero_of_relations_x0_affineTail_x0sq_x0x1_affineTail_x1sq_disc_ne_zero
        (B := B0) (u := mapVec e.toAlgHom u) hu0
        (a := D.A⁻¹ 0 0) (b := D.A⁻¹ 0 1)
        (e := D.A⁻¹ 2 0 - g ^ 2 * D.A⁻¹ 0 0) (f := D.A⁻¹ 2 1 - g ^ 2 * D.A⁻¹ 0 1)
        hdisc0 h0' h20' h11' h02' hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

/-- Classifier-facing wrapper for the determinant-zero, nonzero-discriminant
range-two exact-affine branch. Once the normalized tail matrix satisfies
\[
  \alpha_{20}\beta_{11}-\beta_{20}\alpha_{11}=0,\qquad
  \alpha_{20}^2-\alpha_{20}\beta_{20}\beta_{02}+\beta_{20}^2\alpha_{02}\neq 0,
\]
Lean normalizes internally to the exact representative family and closes by the
new direct image theorem. -/
theorem residual_eq_zero_of_exactAffineDimOne_tailRangeTwo_sharedTail_disc_ne_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 1)
    (hnoConst : ¬ ∃ c ∈ exactAffineSubmodule u, relationPoly u c = (1 : Poly))
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (hrange2 : Module.finrank ℝ (LinearMap.range (x0TailCoeffMap u)) = 2)
    (hdetTail :
      (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 0 0 *
          (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 1 1 -
        (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 0 1 *
          (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 1 0 = 0)
    (hdisc :
      (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 0 0 ^ 2 -
          (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 0 0 *
            (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 0 1 *
            (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 2 1 +
        (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 0 1 ^ 2 *
          (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 2 0 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let D := exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2
  exact
    residual_eq_zero_of_relations_x0_tail_const_x1_hom_basis_matrix_sharedTail_disc_ne_zero
      (B := B) (u := u) hu h0 D hdetTail hdisc hp hsocp

/-- In the exact-affine `dim = 1`, tail-rank `2` determinant-zero branch, the
codimension-one discriminant-zero shared-tail slice also reduces directly to
the representative family
\[
  x_0,\ a+b x_1+x_0^2,\ x_0x_1,\ e+f x_1+x_1^2
\]
after the same internal `x₁`-shear normalization. -/
theorem residual_eq_zero_of_relations_x0_tail_const_x1_hom_basis_matrix_sharedTail_disc_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (D : X0TailConstX1HomBasisMatrixData u)
    (hdetTail : D.A⁻¹ 0 0 * D.A⁻¹ 1 1 - D.A⁻¹ 0 1 * D.A⁻¹ 1 0 = 0)
    (htail : D.A⁻¹ 0 0 ≠ 0 ∨ D.A⁻¹ 0 1 ≠ 0)
    (hdisc :
      D.A⁻¹ 0 0 ^ 2 - D.A⁻¹ 0 0 * D.A⁻¹ 0 1 * D.A⁻¹ 2 1 + D.A⁻¹ 0 1 ^ 2 * D.A⁻¹ 2 0 = 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  rcases
      exists_relations_x0_tail_const_x1_hom_basis_matrix_sharedTail_shear_normalized
        (u := u) (c0 := c0) h0 D hdetTail htail
    with ⟨g, c20', c11', c02', h0', h20', h11', h02'⟩
  let e : Poly ≃ₐ[ℝ] Poly := x1ShearEquiv g
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q) := by
    intro q hq
    exact isQuadratic_affineEquiv (x1ShearMatrix g) (x1ShearInvMatrix g) 0 0
      (x1Shear_mul_inv g) (x1Shear_inv_mul g) (by intro i; simp) (by intro i; simp) hq
  have heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q) := by
    intro q hq
    exact isQuadratic_affineEquiv_symm (x1ShearMatrix g) (x1ShearInvMatrix g) 0 0
      (x1Shear_mul_inv g) (x1Shear_inv_mul g) (by intro i; simp) (by intro i; simp) hq
  have heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q) := by
    intro q hq
    exact isQuartic_affineEquiv (x1ShearMatrix g) (x1ShearInvMatrix g) 0 0
      (x1Shear_mul_inv g) (x1Shear_inv_mul g) (by intro i; simp) (by intro i; simp) hq
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hdisc0 :
      D.A⁻¹ 0 0 ^ 2 -
          D.A⁻¹ 0 0 * D.A⁻¹ 0 1 * (D.A⁻¹ 2 1 - g ^ 2 * D.A⁻¹ 0 1) +
            D.A⁻¹ 0 1 ^ 2 * (D.A⁻¹ 2 0 - g ^ 2 * D.A⁻¹ 0 0) = 0 := by
    have hEq :
        D.A⁻¹ 0 0 ^ 2 -
            D.A⁻¹ 0 0 * D.A⁻¹ 0 1 * (D.A⁻¹ 2 1 - g ^ 2 * D.A⁻¹ 0 1) +
              D.A⁻¹ 0 1 ^ 2 * (D.A⁻¹ 2 0 - g ^ 2 * D.A⁻¹ 0 0) =
          D.A⁻¹ 0 0 ^ 2 -
            D.A⁻¹ 0 0 * D.A⁻¹ 0 1 * D.A⁻¹ 2 1 +
              D.A⁻¹ 0 1 ^ 2 * D.A⁻¹ 2 0 := by
      ring
    exact hEq.trans hdisc
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact
      residual_eq_zero_of_relations_x0_affineTail_x0sq_x0x1_affineTail_x1sq_disc_zero
        (B := B0) (u := mapVec e.toAlgHom u) hu0
        (a := D.A⁻¹ 0 0) (b := D.A⁻¹ 0 1)
        (e := D.A⁻¹ 2 0 - g ^ 2 * D.A⁻¹ 0 0) (f := D.A⁻¹ 2 1 - g ^ 2 * D.A⁻¹ 0 1)
        hdisc0 h0' h20' h11' h02' hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

/-- Classifier-facing wrapper for the determinant-zero, discriminant-zero
shared-tail range-two exact-affine branch. -/
theorem residual_eq_zero_of_exactAffineDimOne_tailRangeTwo_sharedTail_disc_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 1)
    (hnoConst : ¬ ∃ c ∈ exactAffineSubmodule u, relationPoly u c = (1 : Poly))
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (hrange2 : Module.finrank ℝ (LinearMap.range (x0TailCoeffMap u)) = 2)
    (hdetTail :
      (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 0 0 *
          (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 1 1 -
        (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 0 1 *
          (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 1 0 = 0)
    (htail :
      (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 0 0 ≠ 0 ∨
        (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 0 1 ≠ 0)
    (hdisc :
      (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 0 0 ^ 2 -
          (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 0 0 *
            (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 0 1 *
            (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 2 1 +
        (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 0 1 ^ 2 *
          (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 2 0 = 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let D := exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2
  exact
    residual_eq_zero_of_relations_x0_tail_const_x1_hom_basis_matrix_sharedTail_disc_zero
      (B := B) (u := u) hu h0 D hdetTail htail hdisc hp hsocp

/-- In the determinant-zero tail-rank `2` branch, if the reconstructed `x₀²`
tail vanishes entirely, then `c20` is already an exact `x₀²` relation. The
remaining affine tails live only on the reconstructed `x₀x₁` and `x₁²`
relations, so a nonzero discriminant reduces directly to the exact-`x₀²`
representative family. -/
theorem residual_eq_zero_of_relations_x0_tail_const_x1_hom_basis_matrix_x0sq_disc_ne_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (D : X0TailConstX1HomBasisMatrixData u)
    (h00 : D.A⁻¹ 0 0 = 0)
    (h01 : D.A⁻¹ 0 1 = 0)
    (hdisc :
      D.A⁻¹ 1 0 ^ 2 - D.A⁻¹ 1 0 * D.A⁻¹ 1 1 * D.A⁻¹ 2 1 + D.A⁻¹ 1 1 ^ 2 * D.A⁻¹ 2 0 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have h20 : relationPoly u D.c20 = x0 ^ 2 := by
    rw [X0TailConstX1HomBasisMatrixData.relation_c20]
    simp [h00, h01]
  exact
    residual_eq_zero_of_relations_x0_x0sq_affineTail_x0x1_affineTail_x1sq_disc_ne_zero
      (B := B) (u := u) hu
      (c0 := c0) (c1 := D.c20) (c2 := D.c11) (c3 := D.c02)
      (c := D.A⁻¹ 1 0) (d := D.A⁻¹ 1 1) (e := D.A⁻¹ 2 0) (f := D.A⁻¹ 2 1)
      hdisc
      (by simpa [relationPoly] using h0)
      (by simpa [relationPoly] using h20)
      (by simpa [relationPoly] using X0TailConstX1HomBasisMatrixData.relation_c11 D)
      (by simpa [relationPoly] using X0TailConstX1HomBasisMatrixData.relation_c02 D)
      hp hsocp

/-- Classifier-facing wrapper for the determinant-zero range-two branch with
`(A^{-1})_{00} = (A^{-1})_{01} = 0`. In this chart the extracted `c20`
relation is already exact `x₀²`, so a nonzero discriminant on the remaining
two affine tails closes directly by the new exact-`x₀²` representative
theorem. -/
theorem residual_eq_zero_of_exactAffineDimOne_tailRangeTwo_x0sq_disc_ne_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 1)
    (hnoConst : ¬ ∃ c ∈ exactAffineSubmodule u, relationPoly u c = (1 : Poly))
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (hrange2 : Module.finrank ℝ (LinearMap.range (x0TailCoeffMap u)) = 2)
    (h00 :
      (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 0 0 = 0)
    (h01 :
      (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 0 1 = 0)
    (hdisc :
      (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 1 0 ^ 2 -
          (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 1 0 *
            (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 1 1 *
            (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 2 1 +
        (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 1 1 ^ 2 *
          (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 2 0 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let D := exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2
  exact
    residual_eq_zero_of_relations_x0_tail_const_x1_hom_basis_matrix_x0sq_disc_ne_zero
      (B := B) (u := u) hu h0 D h00 h01 hdisc hp hsocp

/-- In the complementary determinant-zero range-two branch with
`(A^{-1})_{00} = (A^{-1})_{01} = 0`, the codimension-one discriminant-zero
slice on the remaining affine `x₀x₁` and `x₁²` tails reduces directly to the
new exact-`x₀²` discriminant-zero representative family. -/
theorem residual_eq_zero_of_relations_x0_tail_const_x1_hom_basis_matrix_x0sq_disc_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (D : X0TailConstX1HomBasisMatrixData u)
    (h00 : D.A⁻¹ 0 0 = 0)
    (h01 : D.A⁻¹ 0 1 = 0)
    (hdisc :
      D.A⁻¹ 1 0 ^ 2 - D.A⁻¹ 1 0 * D.A⁻¹ 1 1 * D.A⁻¹ 2 1 + D.A⁻¹ 1 1 ^ 2 * D.A⁻¹ 2 0 = 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have h20 : relationPoly u D.c20 = x0 ^ 2 := by
    rw [X0TailConstX1HomBasisMatrixData.relation_c20]
    simp [h00, h01]
  exact
    residual_eq_zero_of_relations_x0_x0sq_affineTail_x0x1_affineTail_x1sq_disc_zero
      (B := B) (u := u) hu
      (c0 := c0) (c1 := D.c20) (c2 := D.c11) (c3 := D.c02)
      (c := D.A⁻¹ 1 0) (d := D.A⁻¹ 1 1) (e := D.A⁻¹ 2 0) (f := D.A⁻¹ 2 1)
      hdisc
      (by simpa [relationPoly] using h0)
      (by simpa [relationPoly] using h20)
      (by simpa [relationPoly] using X0TailConstX1HomBasisMatrixData.relation_c11 D)
      (by simpa [relationPoly] using X0TailConstX1HomBasisMatrixData.relation_c02 D)
      hp hsocp

/-- Classifier-facing wrapper for the determinant-zero range-two branch with
`(A^{-1})_{00} = (A^{-1})_{01} = 0` and discriminant zero on the remaining
affine tails. -/
theorem residual_eq_zero_of_exactAffineDimOne_tailRangeTwo_x0sq_disc_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 1)
    (hnoConst : ¬ ∃ c ∈ exactAffineSubmodule u, relationPoly u c = (1 : Poly))
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (hrange2 : Module.finrank ℝ (LinearMap.range (x0TailCoeffMap u)) = 2)
    (h00 :
      (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 0 0 = 0)
    (h01 :
      (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 0 1 = 0)
    (hdisc :
      (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 1 0 ^ 2 -
          (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 1 0 *
            (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 1 1 *
            (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 2 1 +
        (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 1 1 ^ 2 *
          (exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2).A⁻¹ 2 0 = 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let D := exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2
  exact
    residual_eq_zero_of_relations_x0_tail_const_x1_hom_basis_matrix_x0sq_disc_zero
      (B := B) (u := u) hu h0 D h00 h01 hdisc hp hsocp

/-- Full closure of the normalized exact-affine `dim = 1`, tail-rank `2`
branch. The extracted matrix data now routes into one of four already-solved
surfaces: generic determinant-nondegenerate tails, the shared-tail
discriminant-nonzero slice, the shared-tail discriminant-zero slice, or the
exact-`x₀²` complement with zero/nonzero discriminant. -/
theorem residual_eq_zero_of_exactAffineDimOne_tailRangeTwo
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 1)
    (hnoConst : ¬ ∃ c ∈ exactAffineSubmodule u, relationPoly u c = (1 : Poly))
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (hrange2 : Module.finrank ℝ (LinearMap.range (x0TailCoeffMap u)) = 2)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let D := exactAffineDimOneRangeTwoData hu hrelker hdim hnoConst h0 hrange2
  by_cases hdetTail :
      D.A⁻¹ 0 0 * D.A⁻¹ 1 1 - D.A⁻¹ 0 1 * D.A⁻¹ 1 0 = 0
  · by_cases htail : D.A⁻¹ 0 0 ≠ 0 ∨ D.A⁻¹ 0 1 ≠ 0
    · by_cases hdisc :
          D.A⁻¹ 0 0 ^ 2 - D.A⁻¹ 0 0 * D.A⁻¹ 0 1 * D.A⁻¹ 2 1 +
              D.A⁻¹ 0 1 ^ 2 * D.A⁻¹ 2 0 = 0
      · exact
          residual_eq_zero_of_exactAffineDimOne_tailRangeTwo_sharedTail_disc_zero
            (B := B) (u := u) hu hrelker hdim hnoConst h0 hrange2 hdetTail htail hdisc hp hsocp
      · exact
          residual_eq_zero_of_exactAffineDimOne_tailRangeTwo_sharedTail_disc_ne_zero
            (B := B) (u := u) hu hrelker hdim hnoConst h0 hrange2 hdetTail hdisc hp hsocp
    · have htail' := not_or.mp htail
      have h00 : D.A⁻¹ 0 0 = 0 := not_not.mp htail'.1
      have h01 : D.A⁻¹ 0 1 = 0 := not_not.mp htail'.2
      by_cases hdisc :
          D.A⁻¹ 1 0 ^ 2 - D.A⁻¹ 1 0 * D.A⁻¹ 1 1 * D.A⁻¹ 2 1 +
              D.A⁻¹ 1 1 ^ 2 * D.A⁻¹ 2 0 = 0
      · exact
          residual_eq_zero_of_exactAffineDimOne_tailRangeTwo_x0sq_disc_zero
            (B := B) (u := u) hu hrelker hdim hnoConst h0 hrange2 h00 h01 hdisc hp hsocp
      · exact
          residual_eq_zero_of_exactAffineDimOne_tailRangeTwo_x0sq_disc_ne_zero
            (B := B) (u := u) hu hrelker hdim hnoConst h0 hrange2 h00 h01 hdisc hp hsocp
  · exact
      residual_eq_zero_of_exactAffineDimOne_tailRangeTwo_generic
        (B := B) (u := u) hu hrelker hdim hnoConst h0 hrange2 hdetTail hp hsocp

/-- Canonical choice of the tail-rank `1` homogeneous basis matrix data in the
normalized `x₀` exact-affine `dim = 1` branch. -/
noncomputable def exactAffineDimOneRangeOneData
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 1)
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (hrange1 : Module.finrank ℝ (LinearMap.range (x0TailCoeffMap u)) = 1) :
    X0TailHomBasisMatrixData u := by
  classical
  let h :=
    exists_x0_tail_nonzero_hom_basis_matrix_of_exactAffineDimOne_rangeOne
      hu hrelker hdim h0 hrange1
  let d0 := Classical.choose h
  let h1 := Classical.choose_spec h
  let d1 := Classical.choose h1
  let h2 := Classical.choose_spec h1
  let d2 := Classical.choose h2
  let h3 := Classical.choose_spec h2
  let A := Classical.choose h3
  let hAdata := Classical.choose_spec h3
  have hd0K : d0 ∈ LinearMap.ker (x0CoeffMap u) := hAdata.1
  have hd1K : d1 ∈ LinearMap.ker (x0CoeffMap u) := hAdata.2.1
  have hd2K : d2 ∈ LinearMap.ker (x0CoeffMap u) := hAdata.2.2.1
  have htail0_ne :
      (MvPolynomial.coeff m00 (relationPoly u d0)) ^ 2 +
          (MvPolynomial.coeff m01 (relationPoly u d0)) ^ 2 ≠ 0 := hAdata.2.2.2.1
  have h00_d1 : MvPolynomial.coeff m00 (relationPoly u d1) = 0 := hAdata.2.2.2.2.1
  have h01_d1 : MvPolynomial.coeff m01 (relationPoly u d1) = 0 := hAdata.2.2.2.2.2.1
  have h00_d2 : MvPolynomial.coeff m00 (relationPoly u d2) = 0 := hAdata.2.2.2.2.2.2.1
  have h01_d2 : MvPolynomial.coeff m01 (relationPoly u d2) = 0 := hAdata.2.2.2.2.2.2.2.1
  have hA :
      ∀ j : Fin 3,
        (![relationPoly u d0 -
              affineLinePoly
                (MvPolynomial.coeff m00 (relationPoly u d0))
                0
                (MvPolynomial.coeff m01 (relationPoly u d0)),
            relationPoly u d1,
            relationPoly u d2] : Fin 3 → Poly) j =
          ∑ k : Fin 3, A j k • homQuadBasis k := hAdata.2.2.2.2.2.2.2.2.1
  have hdet : A.det ≠ 0 := hAdata.2.2.2.2.2.2.2.2.2
  exact ⟨d0, d1, d2, A, hd0K, hd1K, hd2K, htail0_ne, h00_d1, h01_d1, h00_d2, h01_d2, hA,
    hdet⟩

/-- If the exact-affine `dim = 1` branch normalized by an exact `x₀` relation
has zero tail map, the three residual quadratic relations are already exactly
`x₀²`, `x₀x₁`, and `x₁²`. -/
theorem residual_eq_zero_of_exactAffineDimOne_tailRangeZero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 1)
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (hrange0 : Module.finrank ℝ (LinearMap.range (x0TailCoeffMap u)) = 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  rcases exists_relations_x0_homQuadBasis_of_exactAffineDimOne hu hdim h0 with
    ⟨c20, c11, c02, α20, β20, α11, β11, α02, β02, h20, h11, h02⟩
  have hrangeBot : LinearMap.range (x0TailCoeffMap u) = ⊥ := by
    exact Submodule.finrank_eq_zero.mp hrange0
  have hc20x0 : x0CoeffMap u c20 = 0 := by
    simpa [x0CoeffMap, coeff_m10_one, coeff_m10_x1, coeff_m10_x0sq] using
      congrArg (MvPolynomial.coeff m10) h20
  have hc11x0 : x0CoeffMap u c11 = 0 := by
    simpa [x0CoeffMap, coeff_m10_one, coeff_m10_x1, coeff_m10_x0x1] using
      congrArg (MvPolynomial.coeff m10) h11
  have hc02x0 : x0CoeffMap u c02 = 0 := by
    simpa [x0CoeffMap, coeff_m10_one, coeff_m10_x1, coeff_m10_x1sq] using
      congrArg (MvPolynomial.coeff m10) h02
  let c20K : LinearMap.ker (x0CoeffMap u) := ⟨c20, hc20x0⟩
  let c11K : LinearMap.ker (x0CoeffMap u) := ⟨c11, hc11x0⟩
  let c02K : LinearMap.ker (x0CoeffMap u) := ⟨c02, hc02x0⟩
  have htail20 : x0TailCoeffMap u c20K = 0 := by
    have hmem : x0TailCoeffMap u c20K ∈ LinearMap.range (x0TailCoeffMap u) := ⟨c20K, rfl⟩
    rw [hrangeBot] at hmem
    simpa using hmem
  have htail11 : x0TailCoeffMap u c11K = 0 := by
    have hmem : x0TailCoeffMap u c11K ∈ LinearMap.range (x0TailCoeffMap u) := ⟨c11K, rfl⟩
    rw [hrangeBot] at hmem
    simpa using hmem
  have htail02 : x0TailCoeffMap u c02K = 0 := by
    have hmem : x0TailCoeffMap u c02K ∈ LinearMap.range (x0TailCoeffMap u) := ⟨c02K, rfl⟩
    rw [hrangeBot] at hmem
    simpa using hmem
  have hα20 : α20 = 0 := by
    have hcoeff : MvPolynomial.coeff m00 (relationPoly u c20) = 0 := by
      have h := congrArg (fun z : Fin 2 → ℝ => z 0) htail20
      simpa [x0TailCoeffMap, c20K] using h
    have hcoeff' : MvPolynomial.coeff m00 (relationPoly u c20) = α20 := by
      simpa [coeff_m00_x1, coeff_m00_x0sq] using congrArg (MvPolynomial.coeff m00) h20
    exact hcoeff'.symm.trans hcoeff
  have hβ20 : β20 = 0 := by
    have hcoeff : MvPolynomial.coeff m01 (relationPoly u c20) = 0 := by
      have h := congrArg (fun z : Fin 2 → ℝ => z 1) htail20
      simpa [x0TailCoeffMap, c20K] using h
    have hcoeff' : MvPolynomial.coeff m01 (relationPoly u c20) = β20 := by
      simpa [coeff_m01_one, coeff_m01_x1, coeff_m01_x0sq] using
        congrArg (MvPolynomial.coeff m01) h20
    exact hcoeff'.symm.trans hcoeff
  have hα11 : α11 = 0 := by
    have hcoeff : MvPolynomial.coeff m00 (relationPoly u c11) = 0 := by
      have h := congrArg (fun z : Fin 2 → ℝ => z 0) htail11
      simpa [x0TailCoeffMap, c11K] using h
    have hcoeff' : MvPolynomial.coeff m00 (relationPoly u c11) = α11 := by
      simpa [coeff_m00_x1, coeff_m00_x0x1] using congrArg (MvPolynomial.coeff m00) h11
    exact hcoeff'.symm.trans hcoeff
  have hβ11 : β11 = 0 := by
    have hcoeff : MvPolynomial.coeff m01 (relationPoly u c11) = 0 := by
      have h := congrArg (fun z : Fin 2 → ℝ => z 1) htail11
      simpa [x0TailCoeffMap, c11K] using h
    have hcoeff' : MvPolynomial.coeff m01 (relationPoly u c11) = β11 := by
      simpa [coeff_m01_one, coeff_m01_x1, coeff_m01_x0x1] using
        congrArg (MvPolynomial.coeff m01) h11
    exact hcoeff'.symm.trans hcoeff
  have hα02 : α02 = 0 := by
    have hcoeff : MvPolynomial.coeff m00 (relationPoly u c02) = 0 := by
      have h := congrArg (fun z : Fin 2 → ℝ => z 0) htail02
      simpa [x0TailCoeffMap, c02K] using h
    have hcoeff' : MvPolynomial.coeff m00 (relationPoly u c02) = α02 := by
      simpa [coeff_m00_x1, coeff_m00_x1sq] using congrArg (MvPolynomial.coeff m00) h02
    exact hcoeff'.symm.trans hcoeff
  have hβ02 : β02 = 0 := by
    have hcoeff : MvPolynomial.coeff m01 (relationPoly u c02) = 0 := by
      have h := congrArg (fun z : Fin 2 → ℝ => z 1) htail02
      simpa [x0TailCoeffMap, c02K] using h
    have hcoeff' : MvPolynomial.coeff m01 (relationPoly u c02) = β02 := by
      simpa [coeff_m01_one, coeff_m01_x1, coeff_m01_x1sq] using
        congrArg (MvPolynomial.coeff m01) h02
    exact hcoeff'.symm.trans hcoeff
  have h20' : relationPoly u c20 = x0 ^ 2 := by simpa [hα20, hβ20] using h20
  have h11' : relationPoly u c11 = (x0 * x1 : Poly) := by simpa [hα11, hβ11] using h11
  have h02' : relationPoly u c02 = x1 ^ 2 := by simpa [hα02, hβ02] using h02
  exact residual_eq_zero_of_relations_x0_x0sq_x0x1_x1sq
    (B := B) (u := u) hu h0 h20' h11' h02' hp hsocp

/-- In the exact-affine `dim = 1` branch, if only one canonical homogeneous
relation carries a constant tail, the branch closes by direct normalization to
the corresponding affine-rank-one endpoint. -/
theorem residual_eq_zero_of_relations_x0_homQuadBasis_singleConstTail
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c20 c11 c02 : Fin 4 → ℝ}
    {a20 a11 a02 : ℝ}
    (h0 : relationPoly u c0 = x0)
    (h20 : relationPoly u c20 = a20 • (1 : Poly) + x0 ^ 2)
    (h11 : relationPoly u c11 = a11 • (1 : Poly) + (x0 * x1 : Poly))
    (h02 : relationPoly u c02 = a02 • (1 : Poly) + x1 ^ 2)
    (hsupp :
      (a20 ≠ 0 ∧ a11 = 0 ∧ a02 = 0) ∨
      (a20 = 0 ∧ a11 ≠ 0 ∧ a02 = 0) ∨
      (a20 = 0 ∧ a11 = 0 ∧ a02 ≠ 0))
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  rcases hsupp with h20case | h11case | h02case
  · rcases h20case with ⟨ha20, ha11, ha02⟩
    have h20' : relationPoly u (a20⁻¹ • c20) =
        (1 : Poly) + a20⁻¹ • (x0 ^ 2 : Poly) + (0 : ℝ) • (x1 ^ 2 : Poly) := by
      calc
        relationPoly u (a20⁻¹ • c20) = a20⁻¹ • relationPoly u c20 := by
          rw [relationPoly_smul]
        _ = a20⁻¹ • (a20 • (1 : Poly) + x0 ^ 2) := by rw [h20]
        _ = (1 : Poly) + a20⁻¹ • (x0 ^ 2 : Poly) + (0 : ℝ) • (x1 ^ 2 : Poly) := by
          simp [ha20]
    have h11' : relationPoly u c11 = (x0 * x1 : Poly) := by
      simpa [ha11] using h11
    have h02' : relationPoly u c02 = x1 ^ 2 := by
      simpa [ha02] using h02
    exact residual_eq_zero_of_relations_x0_onePlusAX0sqBX1sq_x0x1_x1sq
      (B := B) (u := u) hu (a := a20⁻¹) (b := 0) (inv_ne_zero ha20)
      (by simpa [relationPoly] using h0)
      (by simpa [relationPoly] using h20')
      (by simpa [relationPoly] using h11')
      (by simpa [relationPoly] using h02')
      hp hsocp
  · rcases h11case with ⟨ha20, ha11, ha02⟩
    have h20' : relationPoly u c20 = x0 ^ 2 := by
      simpa [ha20] using h20
    have h11' :
        relationPoly u (a11⁻¹ • c11) = (1 : Poly) + a11⁻¹ • (x0 * x1 : Poly) := by
      calc
        relationPoly u (a11⁻¹ • c11) = a11⁻¹ • relationPoly u c11 := by
          rw [relationPoly_smul]
        _ = a11⁻¹ • (a11 • (1 : Poly) + (x0 * x1 : Poly)) := by rw [h11]
        _ = (1 : Poly) + a11⁻¹ • (x0 * x1 : Poly) := by
          simp [ha11]
    have h02' : relationPoly u c02 = x1 ^ 2 := by
      simpa [ha02] using h02
    exact residual_eq_zero_of_relations_x0_onePlusAX0x1_x0sq_x1sq
      (B := B) (u := u) hu
      (by simpa [relationPoly] using h0)
      (by simpa [relationPoly] using h11')
      (by simpa [relationPoly] using h20')
      (by simpa [relationPoly] using h02')
      hp hsocp
  · rcases h02case with ⟨ha20, ha11, ha02⟩
    let q1 : Poly := relationPoly u (a02⁻¹ • c02)
    have h20' : relationPoly u c20 = x0 ^ 2 := by
      simpa [ha20] using h20
    have h11' : relationPoly u c11 = (x0 * x1 : Poly) := by
      simpa [ha11] using h11
    have hq1 :
        q1 = (1 : Poly) + a02⁻¹ • (x1 ^ 2 : Poly) := by
      calc
        q1 = relationPoly u (a02⁻¹ • c02) := by rfl
        _ = a02⁻¹ • relationPoly u c02 := by rw [relationPoly_smul]
        _ = a02⁻¹ • (a02 • (1 : Poly) + x1 ^ 2) := by rw [h02]
        _ = (1 : Poly) + a02⁻¹ • (x1 ^ 2 : Poly) := by
          simp [ha02]
    have hq1Quad : IsQuadratic q1 := by
      dsimp [q1]
      exact isQuadratic_relationPoly hu (a02⁻¹ • c02)
    have hq1_00 : MvPolynomial.coeff m00 q1 = 1 := by
      simpa [q1, coeff_m00_x1sq] using congrArg (MvPolynomial.coeff m00) hq1
    have hq1_10 : MvPolynomial.coeff m10 q1 = 0 := by
      simpa [q1, coeff_m10_one, coeff_m10_x1sq] using congrArg (MvPolynomial.coeff m10) hq1
    have hq1_01 : MvPolynomial.coeff m01 q1 = 0 := by
      simpa [q1, coeff_m01_one, coeff_m01_x1sq] using congrArg (MvPolynomial.coeff m01) hq1
    have htail : MvPolynomial.coeff m02 q1 ≠ 0 := by
      have hcoeff : MvPolynomial.coeff m02 q1 = a02⁻¹ := by
        simpa [q1, coeff_m02_one, coeff_m02_x1sq] using congrArg (MvPolynomial.coeff m02) hq1
      rw [hcoeff]
      exact inv_ne_zero ha02
    exact residual_eq_zero_of_relations_x0_onePlus_homQuadratics_x0sq_x0x1Plane
      (B := B) (u := u) hu
      (by simpa [relationPoly] using h0)
      (c1 := a02⁻¹ • c02) (q1 := q1) (by simp [q1, relationPoly]) hq1Quad
      hq1_00 hq1_10 hq1_01
      (r := 1) (s := 0) (t := 0) (w := 1)
      (by simpa [relationPoly] using h20')
      (by simpa [relationPoly] using h11')
      htail (by norm_num)
      hp hsocp

/-- In the exact-affine `dim = 1` branch, if only one canonical homogeneous
relation carries an `x₁` tail, the branch closes by direct normalization to the
corresponding affine-rank-one endpoint. -/
theorem residual_eq_zero_of_relations_x0_homQuadBasis_singleX1Tail
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c20 c11 c02 : Fin 4 → ℝ}
    {b20 b11 b02 : ℝ}
    (h0 : relationPoly u c0 = x0)
    (h20 : relationPoly u c20 = b20 • x1 + x0 ^ 2)
    (h11 : relationPoly u c11 = b11 • x1 + (x0 * x1 : Poly))
    (h02 : relationPoly u c02 = b02 • x1 + x1 ^ 2)
    (hsupp :
      (b20 ≠ 0 ∧ b11 = 0 ∧ b02 = 0) ∨
      (b20 = 0 ∧ b11 ≠ 0 ∧ b02 = 0) ∨
      (b20 = 0 ∧ b11 = 0 ∧ b02 ≠ 0))
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  rcases hsupp with h20case | h11case | h02case
  · rcases h20case with ⟨hb20, hb11, hb02⟩
    have h20' :
        relationPoly u (b20⁻¹ • c20) = x1 + b20⁻¹ • (x0 ^ 2 : Poly) := by
      calc
        relationPoly u (b20⁻¹ • c20) = b20⁻¹ • relationPoly u c20 := by
          rw [relationPoly_smul]
        _ = b20⁻¹ • (b20 • x1 + x0 ^ 2) := by rw [h20]
        _ = x1 + b20⁻¹ • (x0 ^ 2 : Poly) := by
          simp [hb20]
    have h11' : relationPoly u c11 = (x0 * x1 : Poly) := by
      simpa [hb11] using h11
    have h02' : relationPoly u c02 = x1 ^ 2 := by
      simpa [hb02] using h02
    exact residual_eq_zero_of_relations_x0_x1PlusAX0sq_x0x1_x1sq
      (B := B) (u := u) hu (a := b20⁻¹) (inv_ne_zero hb20)
      (by simpa [relationPoly] using h0)
      (by simpa [relationPoly] using h20')
      (by simpa [relationPoly] using h11')
      (by simpa [relationPoly] using h02')
      hp hsocp
  · rcases h11case with ⟨hb20, hb11, hb02⟩
    have h20' : relationPoly u c20 = x0 ^ 2 := by
      simpa [hb20] using h20
    have h11' :
        relationPoly u (b11⁻¹ • c11) = x1 + b11⁻¹ • (x0 * x1 : Poly) := by
      calc
        relationPoly u (b11⁻¹ • c11) = b11⁻¹ • relationPoly u c11 := by
          rw [relationPoly_smul]
        _ = b11⁻¹ • (b11 • x1 + (x0 * x1 : Poly)) := by rw [h11]
        _ = x1 + b11⁻¹ • (x0 * x1 : Poly) := by
          simp [hb11]
    have h02' : relationPoly u c02 = x1 ^ 2 := by
      simpa [hb02] using h02
    exact residual_eq_zero_of_relations_x0_x1PlusAX0x1_x0sq_x1sq
      (B := B) (u := u) hu
      (by simpa [relationPoly] using h0)
      (by simpa [relationPoly] using h11')
      (by simpa [relationPoly] using h20')
      (by simpa [relationPoly] using h02')
      hp hsocp
  · rcases h02case with ⟨hb20, hb11, hb02⟩
    have h20' : relationPoly u c20 = x0 ^ 2 := by
      simpa [hb20] using h20
    have h11' : relationPoly u c11 = (x0 * x1 : Poly) := by
      simpa [hb11] using h11
    have h02' :
        relationPoly u (b02⁻¹ • c02) = x1 + b02⁻¹ • (x1 ^ 2 : Poly) := by
      calc
        relationPoly u (b02⁻¹ • c02) = b02⁻¹ • relationPoly u c02 := by
          rw [relationPoly_smul]
        _ = b02⁻¹ • (b02 • x1 + x1 ^ 2) := by rw [h02]
        _ = x1 + b02⁻¹ • (x1 ^ 2 : Poly) := by
          simp [hb02]
    exact residual_eq_zero_of_relations_x0_x1PlusAX1sq_x0sq_x0x1
      (B := B) (u := u) hu (a := b02⁻¹) (inv_ne_zero hb02)
      (by simpa [relationPoly] using h0)
      (by simpa [relationPoly] using h02')
      (by simpa [relationPoly] using h20')
      (by simpa [relationPoly] using h11')
      hp hsocp

/-- In the exact-affine `dim = 1` branch, if only the `x₁²`-direction carries
both constant and `x₁` tails, the branch closes by the translated repeated-line
affine-rank-one theorem. -/
theorem residual_eq_zero_of_relations_x0_homQuadBasis_singleMixedTail_x1sq
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c20 c11 c02 : Fin 4 → ℝ}
    {a20 b20 a11 b11 a02 b02 : ℝ}
    (h0 : relationPoly u c0 = x0)
    (h20 : relationPoly u c20 = a20 • (1 : Poly) + b20 • x1 + x0 ^ 2)
    (h11 : relationPoly u c11 = a11 • (1 : Poly) + b11 • x1 + (x0 * x1 : Poly))
    (h02 : relationPoly u c02 = a02 • (1 : Poly) + b02 • x1 + x1 ^ 2)
    (ha20 : a20 = 0) (hb20 : b20 = 0)
    (ha11 : a11 = 0) (hb11 : b11 = 0)
    (ha02 : a02 ≠ 0) (hb02 : b02 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have _ : b02 / a02 ≠ 0 := by
    exact div_ne_zero hb02 ha02
  have h20' : relationPoly u c20 = x0 ^ 2 := by
    simpa [ha20, hb20] using h20
  have h11' : relationPoly u c11 = (x0 * x1 : Poly) := by
    simpa [ha11, hb11] using h11
  have h02' :
      relationPoly u (a02⁻¹ • c02) =
        (1 : Poly) + (b02 / a02) • x1 + a02⁻¹ • (x1 ^ 2 : Poly) := by
    calc
      relationPoly u (a02⁻¹ • c02) = a02⁻¹ • relationPoly u c02 := by
        rw [relationPoly_smul]
      _ = a02⁻¹ • (a02 • (1 : Poly) + b02 • x1 + x1 ^ 2) := by
        rw [h02]
      _ = (1 : Poly) + (b02 / a02) • x1 + a02⁻¹ • (x1 ^ 2 : Poly) := by
        rw [smul_add, smul_add, smul_smul, smul_smul]
        have hconst : (a02⁻¹ * a02) • (1 : Poly) = (1 : Poly) := by
          rw [inv_mul_cancel₀ ha02, one_smul]
        have hlin : (a02⁻¹ * b02) • x1 = (b02 / a02) • x1 := by
          congr 1
          simp [div_eq_mul_inv, mul_comm]
        rw [hconst, hlin]
  exact residual_eq_zero_of_relations_x0_onePlusBX1PlusAX1sq_x0sq_x0x1
    (B := B) (u := u) hu (a := a02⁻¹) (b := b02 / a02) (inv_ne_zero ha02)
    (by simpa [relationPoly] using h0)
    (by simpa [relationPoly] using h02')
    (by simpa [relationPoly] using h20')
    (by simpa [relationPoly] using h11')
    hp hsocp

/-- In the exact-affine `dim = 1` branch, if only the `x₀²`-direction carries
both constant and `x₁` tails, the branch closes by the mixed constant
repeated-line affine-rank-one theorem. -/
theorem residual_eq_zero_of_relations_x0_homQuadBasis_singleMixedTail_x0sq
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c20 c11 c02 : Fin 4 → ℝ}
    {a20 b20 a11 b11 a02 b02 : ℝ}
    (h0 : relationPoly u c0 = x0)
    (h20 : relationPoly u c20 = a20 • (1 : Poly) + b20 • x1 + x0 ^ 2)
    (h11 : relationPoly u c11 = a11 • (1 : Poly) + b11 • x1 + (x0 * x1 : Poly))
    (h02 : relationPoly u c02 = a02 • (1 : Poly) + b02 • x1 + x1 ^ 2)
    (ha20 : a20 ≠ 0) (hb20 : b20 ≠ 0)
    (ha11 : a11 = 0) (hb11 : b11 = 0)
    (ha02 : a02 = 0) (hb02 : b02 = 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have _ : b20 ≠ 0 := hb20
  have h20' :
      relationPoly u (a20⁻¹ • c20) =
        (1 : Poly) + (b20 / a20) • x1 + a20⁻¹ • (x0 ^ 2 : Poly) := by
    calc
      relationPoly u (a20⁻¹ • c20) = a20⁻¹ • relationPoly u c20 := by
        rw [relationPoly_smul]
      _ = a20⁻¹ • (a20 • (1 : Poly) + b20 • x1 + x0 ^ 2) := by
        rw [h20]
      _ = (a20⁻¹ * a20) • (1 : Poly) + (a20⁻¹ * b20) • x1 + a20⁻¹ • (x0 ^ 2 : Poly) := by
        rw [smul_add, smul_add, smul_smul, smul_smul]
      _ = (1 : Poly) + (b20 / a20) • x1 + a20⁻¹ • (x0 ^ 2 : Poly) := by
        simp [ha20, div_eq_mul_inv, mul_comm, add_assoc]
  have h11' : relationPoly u c11 = (x0 * x1 : Poly) := by
    simpa [ha11, hb11] using h11
  have h02' : relationPoly u c02 = x1 ^ 2 := by
    simpa [ha02, hb02] using h02
  exact residual_eq_zero_of_relations_x0_onePlusBX1PlusAX0sq_x0x1_x1sq
    (B := B) (u := u) hu (a := a20⁻¹) (b := b20 / a20) (inv_ne_zero ha20)
    (by simpa [relationPoly] using h0)
    (by simpa [relationPoly] using h20')
    (by simpa [relationPoly] using h11')
    (by simpa [relationPoly] using h02')
    hp hsocp

/-- In the exact-affine `dim = 1` branch, if only the `x₀x₁`-direction carries
both constant and `x₁` tails, the branch closes by the mixed cross affine-rank-one
theorem. -/
theorem residual_eq_zero_of_relations_x0_homQuadBasis_singleMixedTail_x0x1
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c20 c11 c02 : Fin 4 → ℝ}
    {a20 b20 a11 b11 a02 b02 : ℝ}
    (h0 : relationPoly u c0 = x0)
    (h20 : relationPoly u c20 = a20 • (1 : Poly) + b20 • x1 + x0 ^ 2)
    (h11 : relationPoly u c11 = a11 • (1 : Poly) + b11 • x1 + (x0 * x1 : Poly))
    (h02 : relationPoly u c02 = a02 • (1 : Poly) + b02 • x1 + x1 ^ 2)
    (ha20 : a20 = 0) (hb20 : b20 = 0)
    (ha11 : a11 ≠ 0) (hb11 : b11 ≠ 0)
    (ha02 : a02 = 0) (hb02 : b02 = 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have _ : b11 ≠ 0 := hb11
  have h20' : relationPoly u c20 = x0 ^ 2 := by
    simpa [ha20, hb20] using h20
  have h11' :
      relationPoly u (a11⁻¹ • c11) =
        (1 : Poly) + (b11 / a11) • x1 + a11⁻¹ • (x0 * x1 : Poly) := by
    calc
      relationPoly u (a11⁻¹ • c11) = a11⁻¹ • relationPoly u c11 := by
        rw [relationPoly_smul]
      _ = a11⁻¹ • (a11 • (1 : Poly) + b11 • x1 + (x0 * x1 : Poly)) := by
        rw [h11]
      _ = (1 : Poly) + (b11 / a11) • x1 + a11⁻¹ • (x0 * x1 : Poly) := by
        rw [smul_add, smul_add, smul_smul, smul_smul]
        have hconst : (a11⁻¹ * a11) • (1 : Poly) = (1 : Poly) := by
          rw [inv_mul_cancel₀ ha11, one_smul]
        have hlin : (a11⁻¹ * b11) • x1 = (b11 / a11) • x1 := by
          congr 1
          simp [div_eq_mul_inv, mul_comm]
        rw [hconst, hlin]
  have h02' : relationPoly u c02 = x1 ^ 2 := by
    simpa [ha02, hb02] using h02
  exact residual_eq_zero_of_relations_x0_onePlusBX1PlusAX0x1_x0sq_x1sq
    (B := B) (u := u) hu (a := a11⁻¹) (b := b11 / a11)
    (by simpa [relationPoly] using h0)
    (by simpa [relationPoly] using h11')
    (by simpa [relationPoly] using h20')
    (by simpa [relationPoly] using h02')
    hp hsocp

/-- In the exact-affine `dim = 1` branch, if only the `x₁²`-direction carries
tails, then all pure-constant, pure-`x₁`, and mixed repeated-line subcases are
already covered. -/
theorem residual_eq_zero_of_relations_x0_homQuadBasis_tailOnX1sq
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c20 c11 c02 : Fin 4 → ℝ}
    {a20 b20 a11 b11 a02 b02 : ℝ}
    (h0 : relationPoly u c0 = x0)
    (h20 : relationPoly u c20 = a20 • (1 : Poly) + b20 • x1 + x0 ^ 2)
    (h11 : relationPoly u c11 = a11 • (1 : Poly) + b11 • x1 + (x0 * x1 : Poly))
    (h02 : relationPoly u c02 = a02 • (1 : Poly) + b02 • x1 + x1 ^ 2)
    (ha20 : a20 = 0) (hb20 : b20 = 0)
    (ha11 : a11 = 0) (hb11 : b11 = 0)
    (htail : a02 ≠ 0 ∨ b02 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  by_cases ha02 : a02 = 0
  · have hb02 : b02 ≠ 0 := by
      rcases htail with ha | hb
      · exact False.elim (ha ha02)
      · exact hb
    have h20' : relationPoly u c20 = x0 ^ 2 := by
      simpa [ha20, hb20] using h20
    have h11' : relationPoly u c11 = (x0 * x1 : Poly) := by
      simpa [ha11, hb11] using h11
    have h02' :
        relationPoly u (b02⁻¹ • c02) = x1 + b02⁻¹ • (x1 ^ 2 : Poly) := by
      calc
        relationPoly u (b02⁻¹ • c02) = b02⁻¹ • relationPoly u c02 := by
          rw [relationPoly_smul]
        _ = b02⁻¹ • (b02 • x1 + x1 ^ 2) := by
          rw [h02, ha02, zero_smul, zero_add]
        _ = x1 + b02⁻¹ • (x1 ^ 2 : Poly) := by
          simp [hb02]
    exact residual_eq_zero_of_relations_x0_x1PlusAX1sq_x0sq_x0x1
      (B := B) (u := u) hu (a := b02⁻¹) (inv_ne_zero hb02)
      (by simpa [relationPoly] using h0)
      (by simpa [relationPoly] using h02')
      (by simpa [relationPoly] using h20')
      (by simpa [relationPoly] using h11')
      hp hsocp
  · by_cases hb02 : b02 = 0
    · have ha02' : a02 ≠ 0 := ha02
      have h20' : relationPoly u c20 = x0 ^ 2 := by
        simpa [ha20, hb20] using h20
      have h11' : relationPoly u c11 = (x0 * x1 : Poly) := by
        simpa [ha11, hb11] using h11
      have h02' :
          relationPoly u (a02⁻¹ • c02) = (1 : Poly) + a02⁻¹ • (x1 ^ 2 : Poly) := by
        calc
          relationPoly u (a02⁻¹ • c02) = a02⁻¹ • relationPoly u c02 := by
            rw [relationPoly_smul]
          _ = a02⁻¹ • (a02 • (1 : Poly) + x1 ^ 2) := by
            rw [h02, hb02, zero_smul, add_zero]
          _ = (1 : Poly) + a02⁻¹ • (x1 ^ 2 : Poly) := by
            simp [ha02']
      exact residual_eq_zero_of_relations_x0_onePlusAX1sq_x0sq_x0x1
        (B := B) (u := u) hu
        (by simpa [relationPoly] using h0)
        (by simpa [relationPoly] using h02')
        (by simpa [relationPoly] using h20')
        (by simpa [relationPoly] using h11')
        hp hsocp
    · exact residual_eq_zero_of_relations_x0_homQuadBasis_singleMixedTail_x1sq
        (B := B) (u := u) hu h0 h20 h11 h02 ha20 hb20 ha11 hb11 ha02 hb02 hp hsocp

theorem residual_eq_zero_of_equiv_relations_x0_homQuadBasis_tailOnX1sq
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c20 c11 c02 : Fin 4 → ℝ}
    {a20 b20 a11 b11 a02 b02 : ℝ}
    (h0 : relationPoly (mapVec e.toAlgHom u) c0 = x0)
    (h20 : relationPoly (mapVec e.toAlgHom u) c20 = a20 • (1 : Poly) + b20 • x1 + x0 ^ 2)
    (h11 : relationPoly (mapVec e.toAlgHom u) c11 = a11 • (1 : Poly) + b11 • x1 + (x0 * x1 : Poly))
    (h02 : relationPoly (mapVec e.toAlgHom u) c02 = a02 • (1 : Poly) + b02 • x1 + x1 ^ 2)
    (ha20 : a20 = 0) (hb20 : b20 = 0)
    (ha11 : a11 = 0) (hb11 : b11 = 0)
    (htail : a02 ≠ 0 ∨ b02 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e)
      (heQuad := fun {_} hpq => heQuad hpq)
      (heQuartic := fun {_} hpq => heQuartic hpq)
      hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_x0_homQuadBasis_tailOnX1sq
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0 h20 h11 h02 ha20 hb20 ha11 hb11 htail hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

/-- In the exact-affine `dim = 1` branch, if only the `x₀²`-direction carries
tails, Lean now closes the pure constant-tail, pure `x₁`-tail, and mixed
repeated-line subcases internally. -/
theorem residual_eq_zero_of_relations_x0_homQuadBasis_tailOnX0sq
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c20 c11 c02 : Fin 4 → ℝ}
    {a20 b20 a11 b11 a02 b02 : ℝ}
    (h0 : relationPoly u c0 = x0)
    (h20 : relationPoly u c20 = a20 • (1 : Poly) + b20 • x1 + x0 ^ 2)
    (h11 : relationPoly u c11 = a11 • (1 : Poly) + b11 • x1 + (x0 * x1 : Poly))
    (h02 : relationPoly u c02 = a02 • (1 : Poly) + b02 • x1 + x1 ^ 2)
    (ha11 : a11 = 0) (hb11 : b11 = 0)
    (ha02 : a02 = 0) (hb02 : b02 = 0)
    (htail : a20 ≠ 0 ∨ b20 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  by_cases ha20 : a20 = 0
  · have hb20 : b20 ≠ 0 := by
      rcases htail with ha | hb
      · exact False.elim (ha ha20)
      · exact hb
    have h20' : relationPoly u c20 = b20 • x1 + x0 ^ 2 := by
      simpa [ha20] using h20
    have h11' : relationPoly u c11 = (0 : ℝ) • x1 + (x0 * x1 : Poly) := by
      simpa [ha11, hb11] using h11
    have h02' : relationPoly u c02 = (0 : ℝ) • x1 + x1 ^ 2 := by
      simpa [ha02, hb02] using h02
    exact residual_eq_zero_of_relations_x0_homQuadBasis_singleX1Tail
      (B := B) (u := u)
      (c0 := c0) (c20 := c20) (c11 := c11) (c02 := c02)
      (b20 := b20) (b11 := 0) (b02 := 0)
      hu h0 h20' h11' h02'
      (Or.inl ⟨hb20, rfl, rfl⟩) hp hsocp
  · by_cases hb20 : b20 = 0
    · have h20' : relationPoly u c20 = a20 • (1 : Poly) + x0 ^ 2 := by
        simpa [hb20] using h20
      have h11' : relationPoly u c11 = (0 : ℝ) • (1 : Poly) + (x0 * x1 : Poly) := by
        simpa [ha11, hb11] using h11
      have h02' : relationPoly u c02 = (0 : ℝ) • (1 : Poly) + x1 ^ 2 := by
        simpa [ha02, hb02] using h02
      exact residual_eq_zero_of_relations_x0_homQuadBasis_singleConstTail
        (B := B) (u := u)
        (c0 := c0) (c20 := c20) (c11 := c11) (c02 := c02)
        (a20 := a20) (a11 := 0) (a02 := 0)
        hu h0 h20' h11' h02'
        (Or.inl ⟨ha20, rfl, rfl⟩) hp hsocp
    · exact residual_eq_zero_of_relations_x0_homQuadBasis_singleMixedTail_x0sq
        (B := B) (u := u) hu h0 h20 h11 h02 ha20 hb20 ha11 hb11 ha02 hb02 hp hsocp

theorem residual_eq_zero_of_equiv_relations_x0_homQuadBasis_tailOnX0sq
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c20 c11 c02 : Fin 4 → ℝ}
    {a20 b20 a11 b11 a02 b02 : ℝ}
    (h0 : relationPoly (mapVec e.toAlgHom u) c0 = x0)
    (h20 : relationPoly (mapVec e.toAlgHom u) c20 = a20 • (1 : Poly) + b20 • x1 + x0 ^ 2)
    (h11 : relationPoly (mapVec e.toAlgHom u) c11 = a11 • (1 : Poly) + b11 • x1 + (x0 * x1 : Poly))
    (h02 : relationPoly (mapVec e.toAlgHom u) c02 = a02 • (1 : Poly) + b02 • x1 + x1 ^ 2)
    (ha11 : a11 = 0) (hb11 : b11 = 0)
    (ha02 : a02 = 0) (hb02 : b02 = 0)
    (htail : a20 ≠ 0 ∨ b20 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e)
      (heQuad := fun {_} hpq => heQuad hpq)
      (heQuartic := fun {_} hpq => heQuartic hpq)
      hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_x0_homQuadBasis_tailOnX0sq
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0 h20 h11 h02 ha11 hb11 ha02 hb02 htail hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

/-- In the exact-affine `dim = 1` branch, if only the `x₀x₁`-direction carries
tails, Lean now closes the pure constant-tail, pure `x₁`-tail, and mixed cross
subcases internally. -/
theorem residual_eq_zero_of_relations_x0_homQuadBasis_tailOnX0x1
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c20 c11 c02 : Fin 4 → ℝ}
    {a20 b20 a11 b11 a02 b02 : ℝ}
    (h0 : relationPoly u c0 = x0)
    (h20 : relationPoly u c20 = a20 • (1 : Poly) + b20 • x1 + x0 ^ 2)
    (h11 : relationPoly u c11 = a11 • (1 : Poly) + b11 • x1 + (x0 * x1 : Poly))
    (h02 : relationPoly u c02 = a02 • (1 : Poly) + b02 • x1 + x1 ^ 2)
    (ha20 : a20 = 0) (hb20 : b20 = 0)
    (ha02 : a02 = 0) (hb02 : b02 = 0)
    (htail : a11 ≠ 0 ∨ b11 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  by_cases ha11 : a11 = 0
  · have hb11 : b11 ≠ 0 := by
      rcases htail with ha | hb
      · exact False.elim (ha ha11)
      · exact hb
    have h20' : relationPoly u c20 = (0 : ℝ) • x1 + x0 ^ 2 := by
      simpa [ha20, hb20] using h20
    have h11' : relationPoly u c11 = b11 • x1 + (x0 * x1 : Poly) := by
      simpa [ha11] using h11
    have h02' : relationPoly u c02 = (0 : ℝ) • x1 + x1 ^ 2 := by
      simpa [ha02, hb02] using h02
    exact residual_eq_zero_of_relations_x0_homQuadBasis_singleX1Tail
      (B := B) (u := u)
      (c0 := c0) (c20 := c20) (c11 := c11) (c02 := c02)
      (b20 := 0) (b11 := b11) (b02 := 0)
      hu h0 h20' h11' h02'
      (Or.inr <| Or.inl ⟨rfl, hb11, rfl⟩) hp hsocp
  · by_cases hb11 : b11 = 0
    · have h20' : relationPoly u c20 = (0 : ℝ) • (1 : Poly) + x0 ^ 2 := by
        simpa [ha20, hb20] using h20
      have h11' : relationPoly u c11 = a11 • (1 : Poly) + (x0 * x1 : Poly) := by
        simpa [hb11] using h11
      have h02' : relationPoly u c02 = (0 : ℝ) • (1 : Poly) + x1 ^ 2 := by
        simpa [ha02, hb02] using h02
      exact residual_eq_zero_of_relations_x0_homQuadBasis_singleConstTail
        (B := B) (u := u)
        (c0 := c0) (c20 := c20) (c11 := c11) (c02 := c02)
        (a20 := 0) (a11 := a11) (a02 := 0)
        hu h0 h20' h11' h02'
        (Or.inr <| Or.inl ⟨rfl, ha11, rfl⟩) hp hsocp
    · exact residual_eq_zero_of_relations_x0_homQuadBasis_singleMixedTail_x0x1
        (B := B) (u := u) hu h0 h20 h11 h02 ha20 hb20 ha11 hb11 ha02 hb02 hp hsocp

theorem residual_eq_zero_of_equiv_relations_x0_homQuadBasis_tailOnX0x1
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c20 c11 c02 : Fin 4 → ℝ}
    {a20 b20 a11 b11 a02 b02 : ℝ}
    (h0 : relationPoly (mapVec e.toAlgHom u) c0 = x0)
    (h20 : relationPoly (mapVec e.toAlgHom u) c20 = a20 • (1 : Poly) + b20 • x1 + x0 ^ 2)
    (h11 : relationPoly (mapVec e.toAlgHom u) c11 = a11 • (1 : Poly) + b11 • x1 + (x0 * x1 : Poly))
    (h02 : relationPoly (mapVec e.toAlgHom u) c02 = a02 • (1 : Poly) + b02 • x1 + x1 ^ 2)
    (ha20 : a20 = 0) (hb20 : b20 = 0)
    (ha02 : a02 = 0) (hb02 : b02 = 0)
    (htail : a11 ≠ 0 ∨ b11 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e)
      (heQuad := fun {_} hpq => heQuad hpq)
      (heQuartic := fun {_} hpq => heQuartic hpq)
      hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_x0_homQuadBasis_tailOnX0x1
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0 h20 h11 h02 ha20 hb20 ha02 hb02 htail hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

/-- Tail-rank `1` exact-affine data closes immediately when the inverse
homogeneous basis matrix shows that only the `x₁²` direction carries the affine
tail. The two remaining canonical homogeneous directions are reconstructed from
the pure relations, while the tailed direction is rebuilt from the unique
tailed relation plus those pure corrections. -/
theorem residual_eq_zero_of_relations_x0_tail_hom_basis_matrix_tailOnX1sq
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 d0 d1 d2 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (hd0K : d0 ∈ LinearMap.ker (x0CoeffMap u))
    (hd1K : d1 ∈ LinearMap.ker (x0CoeffMap u))
    (hd2K : d2 ∈ LinearMap.ker (x0CoeffMap u))
    (htail0_ne :
      (MvPolynomial.coeff m00 (relationPoly u d0)) ^ 2 +
          (MvPolynomial.coeff m01 (relationPoly u d0)) ^ 2 ≠ 0)
    (_h00_d1 : MvPolynomial.coeff m00 (relationPoly u d1) = 0)
    (_h01_d1 : MvPolynomial.coeff m01 (relationPoly u d1) = 0)
    (_h00_d2 : MvPolynomial.coeff m00 (relationPoly u d2) = 0)
    (_h01_d2 : MvPolynomial.coeff m01 (relationPoly u d2) = 0)
    {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hA :
      ∀ j : Fin 3,
        (![relationPoly u d0 -
              affineLinePoly
                (MvPolynomial.coeff m00 (relationPoly u d0))
                0
                (MvPolynomial.coeff m01 (relationPoly u d0)),
            relationPoly u d1,
            relationPoly u d2] : Fin 3 → Poly) j =
          ∑ k : Fin 3, A j k • homQuadBasis k)
    (hdet : A.det ≠ 0)
    (h20_0 : A⁻¹ 0 0 = 0)
    (h11_0 : A⁻¹ 1 0 = 0)
    (h02_0 : A⁻¹ 2 0 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let r0 : ℝ := MvPolynomial.coeff m00 (relationPoly u d0)
  let b0 : ℝ := MvPolynomial.coeff m01 (relationPoly u d0)
  let q : Fin 3 → Poly := ![
    relationPoly u d0 - affineLinePoly r0 0 b0,
    relationPoly u d1,
    relationPoly u d2]
  have hhom := homQuadBasis_eq_sum_inv_mul_of_matrix hA hdet
  have hd0_10 : MvPolynomial.coeff m10 (relationPoly u d0) = 0 := by
    change x0CoeffMap u d0 = 0
    exact hd0K
  have hd1_10 : MvPolynomial.coeff m10 (relationPoly u d1) = 0 := by
    change x0CoeffMap u d1 = 0
    exact hd1K
  have hd2_10 : MvPolynomial.coeff m10 (relationPoly u d2) = 0 := by
    change x0CoeffMap u d2 = 0
    exact hd2K
  let c20 : Fin 4 → ℝ := fun i => (A⁻¹ 0 1) * d1 i + (A⁻¹ 0 2) * d2 i
  let c11 : Fin 4 → ℝ := fun i => (A⁻¹ 1 1) * d1 i + (A⁻¹ 1 2) * d2 i
  let c02 : Fin 4 → ℝ := fun i => (A⁻¹ 2 0) * d0 i + (A⁻¹ 2 1) * d1 i + (A⁻¹ 2 2) * d2 i
  have hd0split : relationPoly u d0 = q 0 + affineLinePoly r0 0 b0 := by
    dsimp [q, r0, b0]
    abel
  have h20 :
      relationPoly u c20 = x0 ^ 2 := by
    have hsum20 : ∑ j : Fin 3, A⁻¹ 0 j • q j = relationPoly u c20 := by
      calc
        ∑ j : Fin 3, A⁻¹ 0 j • q j
            = A⁻¹ 0 0 • q 0 + (A⁻¹ 0 1 • q 1 + A⁻¹ 0 2 • q 2) := by
                simp [Fin.sum_univ_three]
                abel
        _ = A⁻¹ 0 1 • relationPoly u d1 + A⁻¹ 0 2 • relationPoly u d2 := by
              rw [h20_0]
              simp [q]
        _ = relationPoly u c20 := by
              rw [show c20 = (A⁻¹ 0 1) • d1 + (A⁻¹ 0 2) • d2 by
                funext i
                simp [c20]
              , relationPoly_add, relationPoly_smul, relationPoly_smul]
    calc
      relationPoly u c20
          = ∑ j : Fin 3, A⁻¹ 0 j • q j := hsum20.symm
      _ = x0 ^ 2 := by
            simpa using (hhom 0).symm
  have h11 :
      relationPoly u c11 = (x0 * x1 : Poly) := by
    have hsum11 : ∑ j : Fin 3, A⁻¹ 1 j • q j = relationPoly u c11 := by
      calc
        ∑ j : Fin 3, A⁻¹ 1 j • q j
            = A⁻¹ 1 0 • q 0 + (A⁻¹ 1 1 • q 1 + A⁻¹ 1 2 • q 2) := by
                simp [Fin.sum_univ_three]
                abel
        _ = A⁻¹ 1 1 • relationPoly u d1 + A⁻¹ 1 2 • relationPoly u d2 := by
              rw [h11_0]
              simp [q]
        _ = relationPoly u c11 := by
              rw [show c11 = (A⁻¹ 1 1) • d1 + (A⁻¹ 1 2) • d2 by
                funext i
                simp [c11]
              , relationPoly_add, relationPoly_smul, relationPoly_smul]
    calc
      relationPoly u c11
          = ∑ j : Fin 3, A⁻¹ 1 j • q j := hsum11.symm
      _ = x0 * x1 := by
            simpa using (hhom 1).symm
  have h02 :
      relationPoly u c02 = (A⁻¹ 2 0 * r0) • (1 : Poly) + (A⁻¹ 2 0 * b0) • x1 + x1 ^ 2 := by
    calc
      relationPoly u c02
          = (A⁻¹ 2 0) • relationPoly u d0 +
              (A⁻¹ 2 1) • relationPoly u d1 + (A⁻¹ 2 2) • relationPoly u d2 := by
              rw [show c02 = (A⁻¹ 2 0) • d0 + (A⁻¹ 2 1) • d1 + (A⁻¹ 2 2) • d2 by
                funext i
                simp [c02]
              , relationPoly_add, relationPoly_add, relationPoly_smul, relationPoly_smul,
                relationPoly_smul]
      _ = (A⁻¹ 2 0) • affineLinePoly r0 0 b0 +
            ∑ j : Fin 3, A⁻¹ 2 j • q j := by
            rw [hd0split]
            rw [smul_add]
            simp [q, Fin.sum_univ_three]
            abel
      _ = (A⁻¹ 2 0) • affineLinePoly r0 0 b0 + x1 ^ 2 := by
            simpa [q] using congrArg (fun z : Poly => (A⁻¹ 2 0) • affineLinePoly r0 0 b0 + z)
              (hhom 2).symm
      _ = (A⁻¹ 2 0 * r0) • (1 : Poly) + (A⁻¹ 2 0 * b0) • x1 + x1 ^ 2 := by
            simp [affineLinePoly, MvPolynomial.smul_eq_C_mul, mul_comm, mul_left_comm,
              add_assoc]
  have ha20 : (0 : ℝ) = 0 := rfl
  have hb20 : (0 : ℝ) = 0 := rfl
  have ha11 : (0 : ℝ) = 0 := rfl
  have hb11 : (0 : ℝ) = 0 := rfl
  have htail : A⁻¹ 2 0 * r0 ≠ 0 ∨ A⁻¹ 2 0 * b0 ≠ 0 := by
    by_cases hr0 : r0 = 0
    · right
      have hb0 : b0 ≠ 0 := by
        intro hb0
        apply htail0_ne
        simp [r0, b0, hr0, hb0]
      exact mul_ne_zero h02_0 hb0
    · left
      exact mul_ne_zero h02_0 hr0
  exact residual_eq_zero_of_relations_x0_homQuadBasis_tailOnX1sq
    (B := B) (u := u) hu
    (c0 := c0) (c20 := c20) (c11 := c11) (c02 := c02)
    (a20 := 0) (b20 := 0) (a11 := 0) (b11 := 0) (a02 := A⁻¹ 2 0 * r0) (b02 := A⁻¹ 2 0 * b0)
    h0
    (by simpa [zero_smul] using h20)
    (by simpa [zero_smul] using h11)
    h02
    ha20 hb20 ha11 hb11 htail hp hsocp

/-- Tail-rank `1` exact-affine data closes immediately when the inverse
homogeneous basis matrix shows that only the `x₀²` direction carries the affine
tail. -/
theorem residual_eq_zero_of_relations_x0_tail_hom_basis_matrix_tailOnX0sq
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 d0 d1 d2 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (_hd0K : d0 ∈ LinearMap.ker (x0CoeffMap u))
    (_hd1K : d1 ∈ LinearMap.ker (x0CoeffMap u))
    (_hd2K : d2 ∈ LinearMap.ker (x0CoeffMap u))
    (htail0_ne :
      (MvPolynomial.coeff m00 (relationPoly u d0)) ^ 2 +
          (MvPolynomial.coeff m01 (relationPoly u d0)) ^ 2 ≠ 0)
    (_h00_d1 : MvPolynomial.coeff m00 (relationPoly u d1) = 0)
    (_h01_d1 : MvPolynomial.coeff m01 (relationPoly u d1) = 0)
    (_h00_d2 : MvPolynomial.coeff m00 (relationPoly u d2) = 0)
    (_h01_d2 : MvPolynomial.coeff m01 (relationPoly u d2) = 0)
    {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hA :
      ∀ j : Fin 3,
        (![relationPoly u d0 -
              affineLinePoly
                (MvPolynomial.coeff m00 (relationPoly u d0))
                0
                (MvPolynomial.coeff m01 (relationPoly u d0)),
            relationPoly u d1,
            relationPoly u d2] : Fin 3 → Poly) j =
          ∑ k : Fin 3, A j k • homQuadBasis k)
    (hdet : A.det ≠ 0)
    (h20_0 : A⁻¹ 0 0 ≠ 0)
    (h11_0 : A⁻¹ 1 0 = 0)
    (h02_0 : A⁻¹ 2 0 = 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let r0 : ℝ := MvPolynomial.coeff m00 (relationPoly u d0)
  let b0 : ℝ := MvPolynomial.coeff m01 (relationPoly u d0)
  let q : Fin 3 → Poly := ![
    relationPoly u d0 - affineLinePoly r0 0 b0,
    relationPoly u d1,
    relationPoly u d2]
  have hhom := homQuadBasis_eq_sum_inv_mul_of_matrix hA hdet
  let c20 : Fin 4 → ℝ :=
    fun i => (A⁻¹ 0 0) * d0 i + (A⁻¹ 0 1) * d1 i + (A⁻¹ 0 2) * d2 i
  let c11 : Fin 4 → ℝ := fun i => (A⁻¹ 1 1) * d1 i + (A⁻¹ 1 2) * d2 i
  let c02 : Fin 4 → ℝ := fun i => (A⁻¹ 2 1) * d1 i + (A⁻¹ 2 2) * d2 i
  have hd0split : relationPoly u d0 = q 0 + affineLinePoly r0 0 b0 := by
    dsimp [q, r0, b0]
    abel
  have h20 :
      relationPoly u c20 = (A⁻¹ 0 0 * r0) • (1 : Poly) + (A⁻¹ 0 0 * b0) • x1 + x0 ^ 2 := by
    calc
      relationPoly u c20
          = (A⁻¹ 0 0) • relationPoly u d0 +
              (A⁻¹ 0 1) • relationPoly u d1 + (A⁻¹ 0 2) • relationPoly u d2 := by
              rw [show c20 = (A⁻¹ 0 0) • d0 + (A⁻¹ 0 1) • d1 + (A⁻¹ 0 2) • d2 by
                funext i
                simp [c20]
              , relationPoly_add, relationPoly_add, relationPoly_smul, relationPoly_smul,
                relationPoly_smul]
      _ = (A⁻¹ 0 0) • affineLinePoly r0 0 b0 +
            ∑ j : Fin 3, A⁻¹ 0 j • q j := by
            rw [hd0split]
            rw [smul_add]
            simp [q, Fin.sum_univ_three]
            abel
      _ = (A⁻¹ 0 0) • affineLinePoly r0 0 b0 + x0 ^ 2 := by
            simpa [q] using congrArg (fun z : Poly => (A⁻¹ 0 0) • affineLinePoly r0 0 b0 + z)
              (hhom 0).symm
      _ = (A⁻¹ 0 0 * r0) • (1 : Poly) + (A⁻¹ 0 0 * b0) • x1 + x0 ^ 2 := by
            simp [affineLinePoly, MvPolynomial.smul_eq_C_mul, mul_comm, mul_left_comm,
              add_assoc]
  have h11 :
      relationPoly u c11 = (x0 * x1 : Poly) := by
    have hsum11 : ∑ j : Fin 3, A⁻¹ 1 j • q j = relationPoly u c11 := by
      calc
        ∑ j : Fin 3, A⁻¹ 1 j • q j
            = A⁻¹ 1 0 • q 0 + (A⁻¹ 1 1 • q 1 + A⁻¹ 1 2 • q 2) := by
                simp [Fin.sum_univ_three]
                abel
        _ = A⁻¹ 1 1 • relationPoly u d1 + A⁻¹ 1 2 • relationPoly u d2 := by
              rw [h11_0]
              simp [q]
        _ = relationPoly u c11 := by
              rw [show c11 = (A⁻¹ 1 1) • d1 + (A⁻¹ 1 2) • d2 by
                funext i
                simp [c11]
              , relationPoly_add, relationPoly_smul, relationPoly_smul]
    calc
      relationPoly u c11
          = ∑ j : Fin 3, A⁻¹ 1 j • q j := hsum11.symm
      _ = x0 * x1 := by
            simpa using (hhom 1).symm
  have h02 :
      relationPoly u c02 = x1 ^ 2 := by
    have hsum02 : ∑ j : Fin 3, A⁻¹ 2 j • q j = relationPoly u c02 := by
      calc
        ∑ j : Fin 3, A⁻¹ 2 j • q j
            = A⁻¹ 2 0 • q 0 + (A⁻¹ 2 1 • q 1 + A⁻¹ 2 2 • q 2) := by
                simp [Fin.sum_univ_three]
                abel
        _ = A⁻¹ 2 1 • relationPoly u d1 + A⁻¹ 2 2 • relationPoly u d2 := by
              rw [h02_0]
              simp [q]
        _ = relationPoly u c02 := by
              rw [show c02 = (A⁻¹ 2 1) • d1 + (A⁻¹ 2 2) • d2 by
                funext i
                simp [c02]
              , relationPoly_add, relationPoly_smul, relationPoly_smul]
    calc
      relationPoly u c02
          = ∑ j : Fin 3, A⁻¹ 2 j • q j := hsum02.symm
      _ = x1 ^ 2 := by
            simpa using (hhom 2).symm
  have ha11 : (0 : ℝ) = 0 := rfl
  have hb11 : (0 : ℝ) = 0 := rfl
  have ha02 : (0 : ℝ) = 0 := rfl
  have hb02 : (0 : ℝ) = 0 := rfl
  have htail : A⁻¹ 0 0 * r0 ≠ 0 ∨ A⁻¹ 0 0 * b0 ≠ 0 := by
    by_cases hr0 : r0 = 0
    · right
      have hb0 : b0 ≠ 0 := by
        intro hb0
        apply htail0_ne
        simp [r0, b0, hr0, hb0]
      exact mul_ne_zero h20_0 hb0
    · left
      exact mul_ne_zero h20_0 hr0
  exact residual_eq_zero_of_relations_x0_homQuadBasis_tailOnX0sq
    (B := B) (u := u) hu
    (c0 := c0) (c20 := c20) (c11 := c11) (c02 := c02)
    (a20 := A⁻¹ 0 0 * r0) (b20 := A⁻¹ 0 0 * b0) (a11 := 0) (b11 := 0) (a02 := 0) (b02 := 0)
    h0
    h20
    (by simpa [zero_smul] using h11)
    (by simpa [zero_smul] using h02)
    ha11 hb11 ha02 hb02 htail hp hsocp

/-- Tail-rank `1` exact-affine data closes immediately when the inverse
homogeneous basis matrix shows that only the `x₀x₁` direction carries the affine
tail. -/
theorem residual_eq_zero_of_relations_x0_tail_hom_basis_matrix_tailOnX0x1
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 d0 d1 d2 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (_hd0K : d0 ∈ LinearMap.ker (x0CoeffMap u))
    (_hd1K : d1 ∈ LinearMap.ker (x0CoeffMap u))
    (_hd2K : d2 ∈ LinearMap.ker (x0CoeffMap u))
    (htail0_ne :
      (MvPolynomial.coeff m00 (relationPoly u d0)) ^ 2 +
          (MvPolynomial.coeff m01 (relationPoly u d0)) ^ 2 ≠ 0)
    (_h00_d1 : MvPolynomial.coeff m00 (relationPoly u d1) = 0)
    (_h01_d1 : MvPolynomial.coeff m01 (relationPoly u d1) = 0)
    (_h00_d2 : MvPolynomial.coeff m00 (relationPoly u d2) = 0)
    (_h01_d2 : MvPolynomial.coeff m01 (relationPoly u d2) = 0)
    {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hA :
      ∀ j : Fin 3,
        (![relationPoly u d0 -
              affineLinePoly
                (MvPolynomial.coeff m00 (relationPoly u d0))
                0
                (MvPolynomial.coeff m01 (relationPoly u d0)),
            relationPoly u d1,
            relationPoly u d2] : Fin 3 → Poly) j =
          ∑ k : Fin 3, A j k • homQuadBasis k)
    (hdet : A.det ≠ 0)
    (h20_0 : A⁻¹ 0 0 = 0)
    (h11_0 : A⁻¹ 1 0 ≠ 0)
    (h02_0 : A⁻¹ 2 0 = 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let r0 : ℝ := MvPolynomial.coeff m00 (relationPoly u d0)
  let b0 : ℝ := MvPolynomial.coeff m01 (relationPoly u d0)
  let q : Fin 3 → Poly := ![
    relationPoly u d0 - affineLinePoly r0 0 b0,
    relationPoly u d1,
    relationPoly u d2]
  have hhom := homQuadBasis_eq_sum_inv_mul_of_matrix hA hdet
  let c20 : Fin 4 → ℝ := fun i => (A⁻¹ 0 1) * d1 i + (A⁻¹ 0 2) * d2 i
  let c11 : Fin 4 → ℝ :=
    fun i => (A⁻¹ 1 0) * d0 i + (A⁻¹ 1 1) * d1 i + (A⁻¹ 1 2) * d2 i
  let c02 : Fin 4 → ℝ := fun i => (A⁻¹ 2 1) * d1 i + (A⁻¹ 2 2) * d2 i
  have hd0split : relationPoly u d0 = q 0 + affineLinePoly r0 0 b0 := by
    dsimp [q, r0, b0]
    abel
  have h20 :
      relationPoly u c20 = x0 ^ 2 := by
    have hsum20 : ∑ j : Fin 3, A⁻¹ 0 j • q j = relationPoly u c20 := by
      calc
        ∑ j : Fin 3, A⁻¹ 0 j • q j
            = A⁻¹ 0 0 • q 0 + (A⁻¹ 0 1 • q 1 + A⁻¹ 0 2 • q 2) := by
                simp [Fin.sum_univ_three]
                abel
        _ = A⁻¹ 0 1 • relationPoly u d1 + A⁻¹ 0 2 • relationPoly u d2 := by
              rw [h20_0]
              simp [q]
        _ = relationPoly u c20 := by
              rw [show c20 = (A⁻¹ 0 1) • d1 + (A⁻¹ 0 2) • d2 by
                funext i
                simp [c20]
              , relationPoly_add, relationPoly_smul, relationPoly_smul]
    calc
      relationPoly u c20
          = ∑ j : Fin 3, A⁻¹ 0 j • q j := hsum20.symm
      _ = x0 ^ 2 := by
            simpa using (hhom 0).symm
  have h11 :
      relationPoly u c11 = (A⁻¹ 1 0 * r0) • (1 : Poly) + (A⁻¹ 1 0 * b0) • x1 + (x0 * x1 : Poly) := by
    calc
      relationPoly u c11
          = (A⁻¹ 1 0) • relationPoly u d0 +
              (A⁻¹ 1 1) • relationPoly u d1 + (A⁻¹ 1 2) • relationPoly u d2 := by
              rw [show c11 = (A⁻¹ 1 0) • d0 + (A⁻¹ 1 1) • d1 + (A⁻¹ 1 2) • d2 by
                funext i
                simp [c11]
              , relationPoly_add, relationPoly_add, relationPoly_smul, relationPoly_smul,
                relationPoly_smul]
      _ = (A⁻¹ 1 0) • affineLinePoly r0 0 b0 +
            ∑ j : Fin 3, A⁻¹ 1 j • q j := by
            rw [hd0split]
            rw [smul_add]
            simp [q, Fin.sum_univ_three]
            abel
      _ = (A⁻¹ 1 0) • affineLinePoly r0 0 b0 + (x0 * x1 : Poly) := by
            simpa [q] using congrArg (fun z : Poly => (A⁻¹ 1 0) • affineLinePoly r0 0 b0 + z)
              (hhom 1).symm
      _ = (A⁻¹ 1 0 * r0) • (1 : Poly) + (A⁻¹ 1 0 * b0) • x1 + (x0 * x1 : Poly) := by
            simp [affineLinePoly, MvPolynomial.smul_eq_C_mul, mul_comm, mul_left_comm,
              add_assoc]
  have h02 :
      relationPoly u c02 = x1 ^ 2 := by
    have hsum02 : ∑ j : Fin 3, A⁻¹ 2 j • q j = relationPoly u c02 := by
      calc
        ∑ j : Fin 3, A⁻¹ 2 j • q j
            = A⁻¹ 2 0 • q 0 + (A⁻¹ 2 1 • q 1 + A⁻¹ 2 2 • q 2) := by
                simp [Fin.sum_univ_three]
                abel
        _ = A⁻¹ 2 1 • relationPoly u d1 + A⁻¹ 2 2 • relationPoly u d2 := by
              rw [h02_0]
              simp [q]
        _ = relationPoly u c02 := by
              rw [show c02 = (A⁻¹ 2 1) • d1 + (A⁻¹ 2 2) • d2 by
                funext i
                simp [c02]
              , relationPoly_add, relationPoly_smul, relationPoly_smul]
    calc
      relationPoly u c02
          = ∑ j : Fin 3, A⁻¹ 2 j • q j := hsum02.symm
      _ = x1 ^ 2 := by
            simpa using (hhom 2).symm
  have ha20 : (0 : ℝ) = 0 := rfl
  have hb20 : (0 : ℝ) = 0 := rfl
  have ha02 : (0 : ℝ) = 0 := rfl
  have hb02 : (0 : ℝ) = 0 := rfl
  have htail : A⁻¹ 1 0 * r0 ≠ 0 ∨ A⁻¹ 1 0 * b0 ≠ 0 := by
    by_cases hr0 : r0 = 0
    · right
      have hb0 : b0 ≠ 0 := by
        intro hb0
        apply htail0_ne
        simp [r0, b0, hr0, hb0]
      exact mul_ne_zero h11_0 hb0
    · left
      exact mul_ne_zero h11_0 hr0
  exact residual_eq_zero_of_relations_x0_homQuadBasis_tailOnX0x1
    (B := B) (u := u) hu
    (c0 := c0) (c20 := c20) (c11 := c11) (c02 := c02)
    (a20 := 0) (b20 := 0) (a11 := A⁻¹ 1 0 * r0) (b11 := A⁻¹ 1 0 * b0) (a02 := 0) (b02 := 0)
    h0
    (by simpa [zero_smul] using h20)
    h11
    (by simpa [zero_smul] using h02)
    ha20 hb20 ha02 hb02 htail hp hsocp

set_option maxHeartbeats 600000 in
/-- Tail-rank `1` exact-affine matrix data also closes across the whole
`m20 = 0`, `m11 ≠ 0` branch. After reconstructing the canonical tailed
`x₀x₁` relation, any residual `x₁²` tail component is cancelled by subtracting
the matching multiple of that tailed relation from the third quadratic, which
reduces directly to the affine-rank-one cross chart. -/
theorem residual_eq_zero_of_relations_x0_tail_hom_basis_matrix_m20_zero_m11_nonzero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 d0 d1 d2 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (_hd0K : d0 ∈ LinearMap.ker (x0CoeffMap u))
    (_hd1K : d1 ∈ LinearMap.ker (x0CoeffMap u))
    (_hd2K : d2 ∈ LinearMap.ker (x0CoeffMap u))
    (htail0_ne :
      (MvPolynomial.coeff m00 (relationPoly u d0)) ^ 2 +
          (MvPolynomial.coeff m01 (relationPoly u d0)) ^ 2 ≠ 0)
    (_h00_d1 : MvPolynomial.coeff m00 (relationPoly u d1) = 0)
    (_h01_d1 : MvPolynomial.coeff m01 (relationPoly u d1) = 0)
    (_h00_d2 : MvPolynomial.coeff m00 (relationPoly u d2) = 0)
    (_h01_d2 : MvPolynomial.coeff m01 (relationPoly u d2) = 0)
    {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hA :
      ∀ j : Fin 3,
        (![relationPoly u d0 -
              affineLinePoly
                (MvPolynomial.coeff m00 (relationPoly u d0))
                0
                (MvPolynomial.coeff m01 (relationPoly u d0)),
            relationPoly u d1,
            relationPoly u d2] : Fin 3 → Poly) j =
          ∑ k : Fin 3, A j k • homQuadBasis k)
    (hdet : A.det ≠ 0)
    (h20_0 : A⁻¹ 0 0 = 0)
    (h11_0 : A⁻¹ 1 0 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let r0 : ℝ := MvPolynomial.coeff m00 (relationPoly u d0)
  let b0 : ℝ := MvPolynomial.coeff m01 (relationPoly u d0)
  let q : Fin 3 → Poly := ![
    relationPoly u d0 - affineLinePoly r0 0 b0,
    relationPoly u d1,
    relationPoly u d2]
  have hhom := homQuadBasis_eq_sum_inv_mul_of_matrix hA hdet
  let c20 : Fin 4 → ℝ := fun i => (A⁻¹ 0 1) * d1 i + (A⁻¹ 0 2) * d2 i
  let c11 : Fin 4 → ℝ :=
    fun i => (A⁻¹ 1 0) * d0 i + (A⁻¹ 1 1) * d1 i + (A⁻¹ 1 2) * d2 i
  let c02 : Fin 4 → ℝ :=
    fun i => (A⁻¹ 2 0) * d0 i + (A⁻¹ 2 1) * d1 i + (A⁻¹ 2 2) * d2 i
  let μ : ℝ := A⁻¹ 2 0 * (A⁻¹ 1 0)⁻¹
  have hd0split : relationPoly u d0 = q 0 + affineLinePoly r0 0 b0 := by
    dsimp [q, r0, b0]
    abel
  have h20 :
      relationPoly u c20 = x0 ^ 2 := by
    have hsum20 : ∑ j : Fin 3, A⁻¹ 0 j • q j = relationPoly u c20 := by
      calc
        ∑ j : Fin 3, A⁻¹ 0 j • q j
            = A⁻¹ 0 0 • q 0 + (A⁻¹ 0 1 • q 1 + A⁻¹ 0 2 • q 2) := by
                simp [Fin.sum_univ_three]
                abel
        _ = A⁻¹ 0 1 • relationPoly u d1 + A⁻¹ 0 2 • relationPoly u d2 := by
              rw [h20_0]
              simp [q]
        _ = relationPoly u c20 := by
              rw [show c20 = (A⁻¹ 0 1) • d1 + (A⁻¹ 0 2) • d2 by
                funext i
                simp [c20]
              , relationPoly_add, relationPoly_smul, relationPoly_smul]
    calc
      relationPoly u c20
          = ∑ j : Fin 3, A⁻¹ 0 j • q j := hsum20.symm
      _ = x0 ^ 2 := by
            simpa using (hhom 0).symm
  have h11 :
      relationPoly u c11 =
        (A⁻¹ 1 0 * r0) • (1 : Poly) + (A⁻¹ 1 0 * b0) • x1 + (x0 * x1 : Poly) := by
    calc
      relationPoly u c11
          = (A⁻¹ 1 0) • relationPoly u d0 +
              (A⁻¹ 1 1) • relationPoly u d1 + (A⁻¹ 1 2) • relationPoly u d2 := by
              rw [show c11 = (A⁻¹ 1 0) • d0 + (A⁻¹ 1 1) • d1 + (A⁻¹ 1 2) • d2 by
                funext i
                simp [c11]
              , relationPoly_add, relationPoly_add, relationPoly_smul, relationPoly_smul,
                relationPoly_smul]
      _ = (A⁻¹ 1 0) • affineLinePoly r0 0 b0 +
            ∑ j : Fin 3, A⁻¹ 1 j • q j := by
            rw [hd0split]
            rw [smul_add]
            simp [q, Fin.sum_univ_three]
            abel
      _ = (A⁻¹ 1 0) • affineLinePoly r0 0 b0 + (x0 * x1 : Poly) := by
            simpa [q] using congrArg (fun z : Poly => (A⁻¹ 1 0) • affineLinePoly r0 0 b0 + z)
              (hhom 1).symm
      _ = (A⁻¹ 1 0 * r0) • (1 : Poly) + (A⁻¹ 1 0 * b0) • x1 + (x0 * x1 : Poly) := by
            simp [affineLinePoly, MvPolynomial.smul_eq_C_mul, mul_comm, mul_left_comm,
              add_assoc]
  have h02 :
      relationPoly u c02 =
        (A⁻¹ 2 0 * r0) • (1 : Poly) + (A⁻¹ 2 0 * b0) • x1 + x1 ^ 2 := by
    calc
      relationPoly u c02
          = (A⁻¹ 2 0) • relationPoly u d0 +
              (A⁻¹ 2 1) • relationPoly u d1 + (A⁻¹ 2 2) • relationPoly u d2 := by
              rw [show c02 = (A⁻¹ 2 0) • d0 + (A⁻¹ 2 1) • d1 + (A⁻¹ 2 2) • d2 by
                funext i
                simp [c02]
              , relationPoly_add, relationPoly_add, relationPoly_smul, relationPoly_smul,
                relationPoly_smul]
      _ = (A⁻¹ 2 0) • affineLinePoly r0 0 b0 +
            ∑ j : Fin 3, A⁻¹ 2 j • q j := by
            rw [hd0split]
            rw [smul_add]
            simp [q, Fin.sum_univ_three]
            abel
      _ = (A⁻¹ 2 0) • affineLinePoly r0 0 b0 + x1 ^ 2 := by
            simpa [q] using congrArg (fun z : Poly => (A⁻¹ 2 0) • affineLinePoly r0 0 b0 + z)
              (hhom 2).symm
      _ = (A⁻¹ 2 0 * r0) • (1 : Poly) + (A⁻¹ 2 0 * b0) • x1 + x1 ^ 2 := by
            simp [affineLinePoly, MvPolynomial.smul_eq_C_mul, mul_comm, mul_left_comm,
              add_assoc]
  let c3 : Fin 4 → ℝ := c02 + (-μ) • c11
  have h3 :
      relationPoly u c3 = (-μ) • (x0 * x1 : Poly) + x1 ^ 2 := by
    calc
      relationPoly u c3
          = relationPoly u c02 + relationPoly u ((-μ) • c11) := by
              rw [show c3 = c02 + (-μ) • c11 by
                funext i
                simp [c3]
              , relationPoly_add]
      _ = relationPoly u c02 + (-μ) • relationPoly u c11 := by
            rw [relationPoly_smul]
      _ = ((A⁻¹ 2 0 * r0) • (1 : Poly) + (A⁻¹ 2 0 * b0) • x1 + x1 ^ 2) +
            (-μ) • ((A⁻¹ 1 0 * r0) • (1 : Poly) + (A⁻¹ 1 0 * b0) • x1 + (x0 * x1 : Poly)) := by
            rw [h02, h11]
      _ = (-μ) • (x0 * x1 : Poly) + x1 ^ 2 := by
            simp [μ, h11_0, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_left_comm,
              add_comm, smul_add, smul_smul]
  have hq20 : IsQuadratic (relationPoly u c20) := isQuadratic_relationPoly hu c20
  have hq11 : IsQuadratic (relationPoly u c11) := isQuadratic_relationPoly hu c11
  have hq3 : IsQuadratic (relationPoly u c3) := isQuadratic_relationPoly hu c3
  have h20_00 : MvPolynomial.coeff m00 (relationPoly u c20) = 0 := by
    simpa [coeff_m00_x0sq] using congrArg (MvPolynomial.coeff m00) h20
  have h20_10 : MvPolynomial.coeff m10 (relationPoly u c20) = 0 := by
    simpa [coeff_m10_x0sq] using congrArg (MvPolynomial.coeff m10) h20
  have h20_01 : MvPolynomial.coeff m01 (relationPoly u c20) = 0 := by
    simpa [coeff_m01_x0sq] using congrArg (MvPolynomial.coeff m01) h20
  have h3_00 : MvPolynomial.coeff m00 (relationPoly u c3) = 0 := by
    simpa [coeff_m00_x0x1, coeff_m00_x1sq] using congrArg (MvPolynomial.coeff m00) h3
  have h3_10 : MvPolynomial.coeff m10 (relationPoly u c3) = 0 := by
    simpa [coeff_m10_x0x1, coeff_m10_x1sq] using congrArg (MvPolynomial.coeff m10) h3
  have h3_01 : MvPolynomial.coeff m01 (relationPoly u c3) = 0 := by
    simpa [coeff_m01_x0x1, coeff_m01_x1sq] using congrArg (MvPolynomial.coeff m01) h3
  have h20_11' : MvPolynomial.coeff m11 (relationPoly u c20) = 0 := by
    simpa [coeff_m11_x0sq] using congrArg (MvPolynomial.coeff m11) h20
  have h20_02' : MvPolynomial.coeff m02 (relationPoly u c20) = 0 := by
    simpa [coeff_m02_x0sq] using congrArg (MvPolynomial.coeff m02) h20
  have h20_20' : MvPolynomial.coeff m20 (relationPoly u c20) = 1 := by
    simpa [coeff_m20_x0sq] using congrArg (MvPolynomial.coeff m20) h20
  have h3_11' : MvPolynomial.coeff m11 (relationPoly u c3) = -μ := by
    have hcoeff := congrArg (MvPolynomial.coeff m11) h3
    simpa [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, coeff_m11_x0x1, coeff_m11_x1sq]
      using hcoeff
  have h3_02' : MvPolynomial.coeff m02 (relationPoly u c3) = 1 := by
    have hcoeff := congrArg (MvPolynomial.coeff m02) h3
    simpa [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, coeff_m02_x0x1, coeff_m02_x1sq]
      using hcoeff
  have h3_20' : MvPolynomial.coeff m20 (relationPoly u c3) = 0 := by
    have hcoeff := congrArg (MvPolynomial.coeff m20) h3
    simpa [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, coeff_m20_x0x1, coeff_m20_x1sq]
      using hcoeff
  have hcross :
      MvPolynomial.coeff m11 (relationPoly u c20) *
          MvPolynomial.coeff m02 (relationPoly u c3) -
        MvPolynomial.coeff m02 (relationPoly u c20) *
          MvPolynomial.coeff m11 (relationPoly u c3) = 0 := by
    rw [h20_11', h3_02', h20_02', h3_11']
    ring
  have hdetCross :
      MvPolynomial.coeff m20 (relationPoly u c20) *
          MvPolynomial.coeff m02 (relationPoly u c3) -
        MvPolynomial.coeff m02 (relationPoly u c20) *
          MvPolynomial.coeff m20 (relationPoly u c3) ≠ 0 := by
    rw [h20_20', h3_02', h20_02', h3_20']
    norm_num
  by_cases hr0 : r0 = 0
  · have hb0 : b0 ≠ 0 := by
      intro hb0
      apply htail0_ne
      simp [r0, b0, hr0, hb0]
    have h11x1 :
        relationPoly u c11 = (A⁻¹ 1 0 * b0) • x1 + (x0 * x1 : Poly) := by
      simpa [hr0, zero_smul, zero_add] using h11
    let c1 : Fin 4 → ℝ := ((A⁻¹ 1 0 * b0)⁻¹) • c11
    have hc1 :
        relationPoly u c1 =
          (A⁻¹ 1 0 * b0)⁻¹ • ((A⁻¹ 1 0 * b0) • x1 + (x0 * x1 : Poly)) := by
      rw [relationPoly_smul, h11x1]
    have h1_00 : MvPolynomial.coeff m00 (relationPoly u c1) = 0 := by
      have hcoeff := congrArg (MvPolynomial.coeff m00) hc1
      simpa [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, coeff_m00_x1, coeff_m00_x0x1]
        using hcoeff
    have h1_10 : MvPolynomial.coeff m10 (relationPoly u c1) = 0 := by
      have hcoeff := congrArg (MvPolynomial.coeff m10) hc1
      simpa [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, coeff_m10_x1, coeff_m10_x0x1]
        using hcoeff
    have h1_01 : MvPolynomial.coeff m01 (relationPoly u c1) = 1 := by
      have hcoeff := congrArg (MvPolynomial.coeff m01) hc1
      have hne : A⁻¹ 1 0 * b0 ≠ 0 := mul_ne_zero h11_0 hb0
      have hcoeff' :
          MvPolynomial.coeff m01 (relationPoly u c1) =
            (A⁻¹ 1 0 * b0)⁻¹ * ((A⁻¹ 1 0 * b0) * 1 + 0) := by
        simpa [smul_eq_mul, MvPolynomial.coeff_add, MvPolynomial.coeff_smul,
          coeff_m01_x1, coeff_m01_x0x1] using hcoeff
      calc
        MvPolynomial.coeff m01 (relationPoly u c1) = (A⁻¹ 1 0 * b0)⁻¹ * (A⁻¹ 1 0 * b0) := by
          simpa using hcoeff'
        _ = 1 := inv_mul_cancel₀ hne
    have h1_02 : MvPolynomial.coeff m02 (relationPoly u c1) = 0 := by
      have hcoeff := congrArg (MvPolynomial.coeff m02) hc1
      simpa [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, coeff_m02_x1, coeff_m02_x0x1]
        using hcoeff
    have htail :
        MvPolynomial.coeff m11
            (affineHom
              (x1ShearMatrix
                (lowHomQuadPlaneC (relationPoly u c20) (relationPoly u c3) /
                  (-(2 * lowHomQuadPlaneB (relationPoly u c20) (relationPoly u c3)))))
              0
              (relationPoly u c1)) ≠ 0 := by
      have hq1 : IsQuadratic (relationPoly u c1) := isQuadratic_relationPoly hu c1
      rw [coeff_m11_affineHom_x1Shear hq1, h1_02]
      simp
      have h1_11 :
          MvPolynomial.coeff m11 (relationPoly u c1) = (A⁻¹ 1 0 * b0)⁻¹ := by
        have hcoeff := congrArg (MvPolynomial.coeff m11) hc1
        simpa [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, coeff_m11_x1, coeff_m11_x0x1]
          using hcoeff
      rw [h1_11]
      exact inv_ne_zero (mul_ne_zero h11_0 hb0)
    exact residual_eq_zero_of_relations_x0_x1Plus_homQuadratics_crossDet_zero
      (B := B) (u := u) hu
      (by simpa [relationPoly] using h0)
      (c1 := c1) (q1 := relationPoly u c1) (by rfl)
      (c2 := c20) (q2 := relationPoly u c20) (by rfl)
      (c3 := c3) (q3 := relationPoly u c3) (by rfl)
      (isQuadratic_relationPoly hu c1) hq20 hq3
      h1_00 h1_10 h1_01
      h20_00 h20_10 h20_01
      h3_00 h3_10 h3_01
      hcross hdetCross htail hp hsocp
  · by_cases hb0 : b0 = 0
    · let c1 : Fin 4 → ℝ := ((A⁻¹ 1 0 * r0)⁻¹) • c11
      have h11const :
          relationPoly u c11 = (A⁻¹ 1 0 * r0) • (1 : Poly) + (x0 * x1 : Poly) := by
        simpa [hb0, zero_smul, add_assoc] using h11
      have h1' :
          relationPoly u c1 = (1 : Poly) + (A⁻¹ 1 0 * r0)⁻¹ • (x0 * x1 : Poly) := by
        have hscale : (A⁻¹ 1 0 * r0)⁻¹ • ((A⁻¹ 1 0 * r0) • (1 : Poly)) = (1 : Poly) := by
          have hne : A⁻¹ 1 0 * r0 ≠ 0 := mul_ne_zero h11_0 hr0
          have hmul : (A⁻¹ 1 0 * r0)⁻¹ * (A⁻¹ 1 0 * r0) = 1 := inv_mul_cancel₀ hne
          rw [smul_smul, hmul, one_smul]
        calc
          relationPoly u c1 = (A⁻¹ 1 0 * r0)⁻¹ • relationPoly u c11 := by
            rw [relationPoly_smul]
          _ = (A⁻¹ 1 0 * r0)⁻¹ • ((A⁻¹ 1 0 * r0) • (1 : Poly) + (x0 * x1 : Poly)) := by
                rw [h11const]
          _ = (A⁻¹ 1 0 * r0)⁻¹ • ((A⁻¹ 1 0 * r0) • (1 : Poly)) +
                (A⁻¹ 1 0 * r0)⁻¹ • (x0 * x1 : Poly) := by
                rw [smul_add]
          _ = (1 : Poly) + (A⁻¹ 1 0 * r0)⁻¹ • (x0 * x1 : Poly) := by
                rw [hscale]
      have h1_00 : MvPolynomial.coeff m00 (relationPoly u c1) = 1 := by
        simpa [coeff_m00_x0x1] using congrArg (MvPolynomial.coeff m00) h1'
      have h1_10 : MvPolynomial.coeff m10 (relationPoly u c1) = 0 := by
        simpa [coeff_m10_one, coeff_m10_x0x1] using congrArg (MvPolynomial.coeff m10) h1'
      have h1_01 : MvPolynomial.coeff m01 (relationPoly u c1) = 0 := by
        simpa [coeff_m01_one, coeff_m01_x0x1] using congrArg (MvPolynomial.coeff m01) h1'
      exact residual_eq_zero_of_relations_x0_onePlus_homQuadratics_crossDet_zero
        (B := B) (u := u) hu
        (by simpa [relationPoly] using h0)
        (c1 := c1) (q1 := relationPoly u c1) (by rfl)
        (c2 := c20) (q2 := relationPoly u c20) (by rfl)
        (c3 := c3) (q3 := relationPoly u c3) (by rfl)
        (isQuadratic_relationPoly hu c1) hq20 hq3
        h1_00 h1_10 h1_01
        h20_00 h20_10 h20_01
        h3_00 h3_10 h3_01
        hcross hdetCross hp hsocp
    · let c1 : Fin 4 → ℝ := ((A⁻¹ 1 0 * r0)⁻¹) • c11
      have h1' :
          relationPoly u c1 =
            (1 : Poly) + (b0 / r0) • x1 + (A⁻¹ 1 0 * r0)⁻¹ • (x0 * x1 : Poly) := by
        have hscale : (A⁻¹ 1 0 * r0)⁻¹ • ((A⁻¹ 1 0 * r0) • (1 : Poly)) = (1 : Poly) := by
          have hne : A⁻¹ 1 0 * r0 ≠ 0 := mul_ne_zero h11_0 hr0
          have hmul : (A⁻¹ 1 0 * r0)⁻¹ * (A⁻¹ 1 0 * r0) = 1 := inv_mul_cancel₀ hne
          rw [smul_smul, hmul, one_smul]
        have hscalex1 :
            (A⁻¹ 1 0 * r0)⁻¹ • ((A⁻¹ 1 0 * b0) • x1) = (b0 / r0) • x1 := by
          rw [smul_smul]
          have hmul :
              (A⁻¹ 1 0 * r0)⁻¹ * (A⁻¹ 1 0 * b0) = b0 / r0 := by
            field_simp [h11_0, hr0]
          rw [hmul]
        calc
          relationPoly u c1 = (A⁻¹ 1 0 * r0)⁻¹ • relationPoly u c11 := by
            rw [relationPoly_smul]
          _ = (A⁻¹ 1 0 * r0)⁻¹ • ((A⁻¹ 1 0 * r0) • (1 : Poly) + (A⁻¹ 1 0 * b0) • x1 +
                (x0 * x1 : Poly)) := by
                rw [h11]
          _ = (A⁻¹ 1 0 * r0)⁻¹ • ((A⁻¹ 1 0 * r0) • (1 : Poly)) +
                (A⁻¹ 1 0 * r0)⁻¹ • ((A⁻¹ 1 0 * b0) • x1) +
                (A⁻¹ 1 0 * r0)⁻¹ • (x0 * x1 : Poly) := by
                simp [smul_add, add_assoc]
          _ = (1 : Poly) + (b0 / r0) • x1 + (A⁻¹ 1 0 * r0)⁻¹ • (x0 * x1 : Poly) := by
                rw [hscale, hscalex1]
      have h1_00 : MvPolynomial.coeff m00 (relationPoly u c1) = 1 := by
        simpa [coeff_m00_x1, coeff_m00_x0x1] using congrArg (MvPolynomial.coeff m00) h1'
      have h1_10 : MvPolynomial.coeff m10 (relationPoly u c1) = 0 := by
        simpa [coeff_m10_one, coeff_m10_x1, coeff_m10_x0x1] using
          congrArg (MvPolynomial.coeff m10) h1'
      exact residual_eq_zero_of_relations_x0_onePlusBX1Plus_homQuadratics_crossDet_zero
        (B := B) (u := u) hu
        (by simpa [relationPoly] using h0)
        (c1 := c1) (q1 := relationPoly u c1) (by rfl)
        (c2 := c20) (q2 := relationPoly u c20) (by rfl)
        (c3 := c3) (q3 := relationPoly u c3) (by rfl)
        (isQuadratic_relationPoly hu c1) hq20 hq3
        h1_00 h1_10
        h20_00 h20_10 h20_01
        h3_00 h3_10 h3_01
        hcross hdetCross hp hsocp

/-- Tail-rank `1` exact-affine matrix data already closes across the whole
`m20 = 0` branch. If the tailed inverse-matrix column has nonzero `m11`
component, Lean uses the mixed-support cross-chart theorem above; otherwise the
tail is supported only on `x₁²` and falls back to the corresponding
support-one theorem. -/
theorem residual_eq_zero_of_relations_x0_tail_hom_basis_matrix_m20_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 d0 d1 d2 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (hd0K : d0 ∈ LinearMap.ker (x0CoeffMap u))
    (hd1K : d1 ∈ LinearMap.ker (x0CoeffMap u))
    (hd2K : d2 ∈ LinearMap.ker (x0CoeffMap u))
    (htail0_ne :
      (MvPolynomial.coeff m00 (relationPoly u d0)) ^ 2 +
          (MvPolynomial.coeff m01 (relationPoly u d0)) ^ 2 ≠ 0)
    (h00_d1 : MvPolynomial.coeff m00 (relationPoly u d1) = 0)
    (h01_d1 : MvPolynomial.coeff m01 (relationPoly u d1) = 0)
    (h00_d2 : MvPolynomial.coeff m00 (relationPoly u d2) = 0)
    (h01_d2 : MvPolynomial.coeff m01 (relationPoly u d2) = 0)
    {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hA :
      ∀ j : Fin 3,
        (![relationPoly u d0 -
              affineLinePoly
                (MvPolynomial.coeff m00 (relationPoly u d0))
                0
                (MvPolynomial.coeff m01 (relationPoly u d0)),
            relationPoly u d1,
            relationPoly u d2] : Fin 3 → Poly) j =
          ∑ k : Fin 3, A j k • homQuadBasis k)
    (hdet : A.det ≠ 0)
    (h20_0 : A⁻¹ 0 0 = 0)
    (htail_ne : A⁻¹ 1 0 ≠ 0 ∨ A⁻¹ 2 0 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  by_cases h11_0 : A⁻¹ 1 0 = 0
  · have h02_0 : A⁻¹ 2 0 ≠ 0 := by
      rcases htail_ne with h11 | h02
      · exact False.elim (h11 h11_0)
      · exact h02
    exact residual_eq_zero_of_relations_x0_tail_hom_basis_matrix_tailOnX1sq
      (B := B) (u := u) hu h0 hd0K hd1K hd2K htail0_ne h00_d1 h01_d1 h00_d2 h01_d2
      hA hdet h20_0 h11_0 h02_0 hp hsocp
  · exact residual_eq_zero_of_relations_x0_tail_hom_basis_matrix_m20_zero_m11_nonzero
      (B := B) (u := u) hu h0 hd0K hd1K hd2K htail0_ne h00_d1 h01_d1 h00_d2 h01_d2
      hA hdet h20_0 h11_0 hp hsocp

/-- Tail-rank `1` exact-affine matrix data closes as soon as the inverse
homogeneous basis matrix shows that the affine tail lands on exactly one of the
three canonical quadratic directions. -/
theorem residual_eq_zero_of_relations_x0_tail_hom_basis_matrix_singleSupport
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 d0 d1 d2 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (hd0K : d0 ∈ LinearMap.ker (x0CoeffMap u))
    (hd1K : d1 ∈ LinearMap.ker (x0CoeffMap u))
    (hd2K : d2 ∈ LinearMap.ker (x0CoeffMap u))
    (htail0_ne :
      (MvPolynomial.coeff m00 (relationPoly u d0)) ^ 2 +
          (MvPolynomial.coeff m01 (relationPoly u d0)) ^ 2 ≠ 0)
    (h00_d1 : MvPolynomial.coeff m00 (relationPoly u d1) = 0)
    (h01_d1 : MvPolynomial.coeff m01 (relationPoly u d1) = 0)
    (h00_d2 : MvPolynomial.coeff m00 (relationPoly u d2) = 0)
    (h01_d2 : MvPolynomial.coeff m01 (relationPoly u d2) = 0)
    {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hA :
      ∀ j : Fin 3,
        (![relationPoly u d0 -
              affineLinePoly
                (MvPolynomial.coeff m00 (relationPoly u d0))
                0
                (MvPolynomial.coeff m01 (relationPoly u d0)),
            relationPoly u d1,
            relationPoly u d2] : Fin 3 → Poly) j =
          ∑ k : Fin 3, A j k • homQuadBasis k)
    (hdet : A.det ≠ 0)
    (hsupport :
      (A⁻¹ 0 0 ≠ 0 ∧ A⁻¹ 1 0 = 0 ∧ A⁻¹ 2 0 = 0) ∨
        (A⁻¹ 0 0 = 0 ∧ A⁻¹ 1 0 ≠ 0 ∧ A⁻¹ 2 0 = 0) ∨
          (A⁻¹ 0 0 = 0 ∧ A⁻¹ 1 0 = 0 ∧ A⁻¹ 2 0 ≠ 0))
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  rcases hsupport with h0only | hrest
  · exact residual_eq_zero_of_relations_x0_tail_hom_basis_matrix_tailOnX0sq
      (B := B) (u := u) hu h0 hd0K hd1K hd2K htail0_ne h00_d1 h01_d1 h00_d2 h01_d2
      hA hdet h0only.1 h0only.2.1 h0only.2.2 hp hsocp
  rcases hrest with h1only | h2only
  · exact residual_eq_zero_of_relations_x0_tail_hom_basis_matrix_tailOnX0x1
      (B := B) (u := u) hu h0 hd0K hd1K hd2K htail0_ne h00_d1 h01_d1 h00_d2 h01_d2
      hA hdet h1only.1 h1only.2.1 h1only.2.2 hp hsocp
  · exact residual_eq_zero_of_relations_x0_tail_hom_basis_matrix_tailOnX1sq
      (B := B) (u := u) hu h0 hd0K hd1K hd2K htail0_ne h00_d1 h01_d1 h00_d2 h01_d2
      hA hdet h2only.1 h2only.2.1 h2only.2.2 hp hsocp

/-- Above the normalized `x₀` exact-affine `dim = 1`, tail-rank `1` extractor,
the entire already-solved matrix region closes in one step: either the affine
tail lands on a single canonical quadratic direction, or the inverse-matrix
column lies in the resolved `m20 = 0` slice. The only remaining tail-rank `1`
gap is therefore the complementary mixed-support `m20 ≠ 0` branch. -/
theorem residual_eq_zero_of_exactAffineDimOne_tailRangeOne_simpleBranch
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 1)
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (hrange1 : Module.finrank ℝ (LinearMap.range (x0TailCoeffMap u)) = 1)
    (hbranch :
      (exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1).SimpleBranch)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  classical
  let D : X0TailHomBasisMatrixData u := exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1
  rcases hbranch with hsingle | hm20
  · exact residual_eq_zero_of_relations_x0_tail_hom_basis_matrix_singleSupport
      (B := B) (u := u) hu h0
      D.hd0K D.hd1K D.hd2K D.htail0_ne
      D.h00_d1 D.h01_d1 D.h00_d2 D.h01_d2
      D.hA D.hdet hsingle hp hsocp
  · exact residual_eq_zero_of_relations_x0_tail_hom_basis_matrix_m20_zero
      (B := B) (u := u) hu h0
      D.hd0K D.hd1K D.hd2K D.htail0_ne
      D.h00_d1 D.h01_d1 D.h00_d2 D.h01_d2
      D.hA D.hdet hm20.1 hm20.2 hp hsocp

/-- In the complementary tail-rank `1` range-one branch, the repeated-line
subcase closes directly from the packaged common-tail triple `c20/c11/c02` and
the pure complementary plane `comp11/comp02`. The only extra input is the
repeated-line discriminant relation
`(A⁻¹)₀₀ * (A⁻¹)₂₀ - ((A⁻¹)₁₀)^2 = 0`, which is exactly the
`lowHomQuadPlaneC - lowHomQuadPlaneB^2 / lowHomQuadPlaneA = 0` condition for
that complementary plane. -/
theorem residual_eq_zero_of_relations_x0_tail_hom_basis_matrix_commonFactorComplement
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (D : X0TailHomBasisMatrixData u)
    (h00_ne : D.A⁻¹ 0 0 ≠ 0)
    (hdisc0 : D.A⁻¹ 0 0 * D.A⁻¹ 2 0 - (D.A⁻¹ 1 0) ^ 2 = 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let l0 : ℝ := D.A⁻¹ 0 0
  let l1 : ℝ := D.A⁻¹ 1 0
  let l2 : ℝ := D.A⁻¹ 2 0
  have h0' : ∑ i : Fin 4, c0 i • u i = x0 := by
    simpa [relationPoly] using h0
  have hq20 : IsQuadratic (relationPoly u D.c20) := isQuadratic_relationPoly hu D.c20
  have hq11 : IsQuadratic (relationPoly u D.comp11) := isQuadratic_relationPoly hu D.comp11
  have hq02 : IsQuadratic (relationPoly u D.comp02) := isQuadratic_relationPoly hu D.comp02
  have hc11 :
      relationPoly u D.comp11 = l1 • (x0 ^ 2 : Poly) - l0 • (x0 * x1 : Poly) := by
    simpa [l0, l1] using X0TailHomBasisMatrixData.relation_comp11 D
  have hc02 :
      relationPoly u D.comp02 = l2 • (x0 ^ 2 : Poly) - l0 • (x1 ^ 2 : Poly) := by
    simpa [l0, l2] using X0TailHomBasisMatrixData.relation_comp02 D
  have hc11_00 : MvPolynomial.coeff m00 (relationPoly u D.comp11) = 0 := by
    rw [hc11, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul,
      coeff_m00_x0sq, coeff_m00_x0x1]
    simp
  have hc11_10 : MvPolynomial.coeff m10 (relationPoly u D.comp11) = 0 := by
    rw [hc11, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul,
      coeff_m10_x0sq, coeff_m10_x0x1]
    simp
  have hc11_01 : MvPolynomial.coeff m01 (relationPoly u D.comp11) = 0 := by
    rw [hc11, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul,
      coeff_m01_x0sq, coeff_m01_x0x1]
    simp
  have hc11_20 : MvPolynomial.coeff m20 (relationPoly u D.comp11) = l1 := by
    rw [hc11, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul,
      coeff_m20_x0sq, coeff_m20_x0x1]
    simp
  have hc11_11 : MvPolynomial.coeff m11 (relationPoly u D.comp11) = -l0 := by
    rw [hc11, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul,
      coeff_m11_x0sq, coeff_m11_x0x1]
    simp
  have hc11_02 : MvPolynomial.coeff m02 (relationPoly u D.comp11) = 0 := by
    rw [hc11, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul,
      coeff_m02_x0sq, coeff_m02_x0x1]
    simp
  have hc02_00 : MvPolynomial.coeff m00 (relationPoly u D.comp02) = 0 := by
    rw [hc02, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul,
      coeff_m00_x0sq, coeff_m00_x1sq]
    simp
  have hc02_10 : MvPolynomial.coeff m10 (relationPoly u D.comp02) = 0 := by
    rw [hc02, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul,
      coeff_m10_x0sq, coeff_m10_x1sq]
    simp
  have hc02_01 : MvPolynomial.coeff m01 (relationPoly u D.comp02) = 0 := by
    rw [hc02, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul,
      coeff_m01_x0sq, coeff_m01_x1sq]
    simp
  have hc02_20 : MvPolynomial.coeff m20 (relationPoly u D.comp02) = l2 := by
    rw [hc02, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul,
      coeff_m20_x0sq, coeff_m20_x1sq]
    simp
  have hc02_11 : MvPolynomial.coeff m11 (relationPoly u D.comp02) = 0 := by
    rw [hc02, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul,
      coeff_m11_x0sq, coeff_m11_x1sq]
    simp
  have hc02_02 : MvPolynomial.coeff m02 (relationPoly u D.comp02) = -l0 := by
    rw [hc02, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul,
      coeff_m02_x0sq, coeff_m02_x1sq]
    simp
  have hAeq :
      lowHomQuadPlaneA (relationPoly u D.comp11) (relationPoly u D.comp02) = l0 ^ 2 := by
    rw [lowHomQuadPlaneA, hc11_11, hc02_02, hc11_02, hc02_11]
    ring
  have hBeq :
      lowHomQuadPlaneB (relationPoly u D.comp11) (relationPoly u D.comp02) = -l0 * l1 := by
    rw [lowHomQuadPlaneB, hc11_20, hc02_02, hc11_02, hc02_20]
    ring
  have hCeq :
      lowHomQuadPlaneC (relationPoly u D.comp11) (relationPoly u D.comp02) = l0 * l2 := by
    rw [lowHomQuadPlaneC, hc11_20, hc02_11, hc11_11, hc02_20]
    ring
  have hA :
      lowHomQuadPlaneA (relationPoly u D.comp11) (relationPoly u D.comp02) ≠ 0 := by
    rw [hAeq]
    exact pow_ne_zero 2 h00_ne
  have hdiag0 :
      lowHomQuadPlaneC (relationPoly u D.comp11) (relationPoly u D.comp02) -
          lowHomQuadPlaneB (relationPoly u D.comp11) (relationPoly u D.comp02) ^ 2 /
            lowHomQuadPlaneA (relationPoly u D.comp11) (relationPoly u D.comp02) = 0 := by
    have hdisc0' : l0 * l2 - l1 ^ 2 = 0 := by
      simpa [l0, l1, l2] using hdisc0
    have hfrac : (-l0 * l1) ^ 2 / l0 ^ 2 = l1 ^ 2 := by
      apply (div_eq_iff (pow_ne_zero 2 h00_ne)).2
      ring
    rw [hCeq, hBeq, hAeq, hfrac]
    exact hdisc0'
  by_cases hr0 : D.r0 = 0
  · have hb0 : D.b0 ≠ 0 := by
      have htail0_ne' : D.r0 ^ 2 + D.b0 ^ 2 ≠ 0 := by
        simpa [X0TailHomBasisMatrixData.r0, X0TailHomBasisMatrixData.b0] using D.htail0_ne
      intro hb0
      apply htail0_ne'
      simp [hr0, hb0]
    let c1 : Fin 4 → ℝ := ((l0 * D.b0)⁻¹) • D.c20
    have h1 :
        relationPoly u c1 = x1 + (l0 * D.b0)⁻¹ • (x0 ^ 2 : Poly) := by
      have hscale : (l0 * D.b0)⁻¹ • ((l0 * D.b0) • x1) = x1 := by
        rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero h00_ne hb0), one_smul]
      calc
        relationPoly u c1 = (l0 * D.b0)⁻¹ • relationPoly u D.c20 := by
          rw [show c1 = ((l0 * D.b0)⁻¹) • D.c20 by
            funext i
            simp [c1]
          , relationPoly_smul]
        _ = (l0 * D.b0)⁻¹ • ((l0 * D.b0) • x1 + x0 ^ 2) := by
              rw [X0TailHomBasisMatrixData.relation_c20, hr0]
              simp [l0]
        _ = (l0 * D.b0)⁻¹ • ((l0 * D.b0) • x1) + (l0 * D.b0)⁻¹ • (x0 ^ 2 : Poly) := by
              rw [smul_add]
        _ = x1 + (l0 * D.b0)⁻¹ • (x0 ^ 2 : Poly) := by
              rw [hscale]
    have hq1 : IsQuadratic (relationPoly u c1) := isQuadratic_relationPoly hu c1
    have hq1_00 : MvPolynomial.coeff m00 (relationPoly u c1) = 0 := by
      simpa [coeff_m00_x1, coeff_m00_x0sq]
        using congrArg (MvPolynomial.coeff m00) h1
    have hq1_10 : MvPolynomial.coeff m10 (relationPoly u c1) = 0 := by
      simpa [coeff_m10_x1, coeff_m10_x0sq]
        using congrArg (MvPolynomial.coeff m10) h1
    have hq1_01 : MvPolynomial.coeff m01 (relationPoly u c1) = 1 := by
      simpa [coeff_m01_x1, coeff_m01_x0sq]
        using congrArg (MvPolynomial.coeff m01) h1
    have hq1_11 : MvPolynomial.coeff m11 (relationPoly u c1) = 0 := by
      simpa [coeff_m11_x1, coeff_m11_x0sq]
        using congrArg (MvPolynomial.coeff m11) h1
    have hq1_02 : MvPolynomial.coeff m02 (relationPoly u c1) = 0 := by
      simpa [coeff_m02_x1, coeff_m02_x0sq]
        using congrArg (MvPolynomial.coeff m02) h1
    have htail :
        MvPolynomial.coeff m20
            (affineHom
              (x1ShearMatrix
                (-lowHomQuadPlaneB (relationPoly u D.comp11) (relationPoly u D.comp02) /
                  lowHomQuadPlaneA (relationPoly u D.comp11) (relationPoly u D.comp02)))
              0
              (relationPoly u c1)) ≠ 0 := by
      have hq1_20 :
          MvPolynomial.coeff m20 (relationPoly u c1) = (l0 * D.b0)⁻¹ := by
        simpa [coeff_m20_x1, coeff_m20_x0sq]
          using congrArg (MvPolynomial.coeff m20) h1
      rw [coeff_m20_affineHom_x1Shear hq1, hq1_11, hq1_02, hq1_20]
      simpa [l0] using (inv_ne_zero (mul_ne_zero h00_ne hb0))
    exact residual_eq_zero_of_relations_x0_x1Plus_homQuadratics_commonFactorChart
      (B := B) (u := u) hu h0'
      (c1 := c1) (q1 := relationPoly u c1) (by rfl)
      (c2 := D.comp11) (q2 := relationPoly u D.comp11) (by rfl)
      (c3 := D.comp02) (q3 := relationPoly u D.comp02) (by rfl)
      hq1 hq11 hq02
      hq1_00 hq1_10 hq1_01
      hc11_00 hc11_10 hc11_01
      hc02_00 hc02_10 hc02_01
      hA hdiag0 htail hp hsocp
  · let c1 : Fin 4 → ℝ := ((l0 * D.r0)⁻¹) • D.c20
    have h1 :
        relationPoly u c1 =
          (1 : Poly) + (D.b0 / D.r0) • x1 + (l0 * D.r0)⁻¹ • (x0 ^ 2 : Poly) := by
      have hscale : (l0 * D.r0)⁻¹ • ((l0 * D.r0) • (1 : Poly)) = (1 : Poly) := by
        rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero h00_ne hr0), one_smul]
      have hscalex1 :
          (l0 * D.r0)⁻¹ • ((l0 * D.b0) • x1) = (D.b0 / D.r0) • x1 := by
        rw [smul_smul]
        have hmul : (l0 * D.r0)⁻¹ * (l0 * D.b0) = D.b0 / D.r0 := by
          have hcancel : (l0 * D.r0)⁻¹ * l0 = D.r0⁻¹ := by
            field_simp [h00_ne, hr0]
            exact div_self h00_ne
          calc
            (l0 * D.r0)⁻¹ * (l0 * D.b0) = ((l0 * D.r0)⁻¹ * l0) * D.b0 := by ring
            _ = D.r0⁻¹ * D.b0 := by rw [hcancel]
            _ = D.b0 / D.r0 := by rw [div_eq_mul_inv, mul_comm]
        rw [hmul]
      calc
        relationPoly u c1 = (l0 * D.r0)⁻¹ • relationPoly u D.c20 := by
          rw [show c1 = ((l0 * D.r0)⁻¹) • D.c20 by
            funext i
            simp [c1]
          , relationPoly_smul]
        _ = (l0 * D.r0)⁻¹ •
              ((l0 * D.r0) • (1 : Poly) + (l0 * D.b0) • x1 + x0 ^ 2) := by
              rw [X0TailHomBasisMatrixData.relation_c20]
        _ = (l0 * D.r0)⁻¹ • ((l0 * D.r0) • (1 : Poly)) +
              (l0 * D.r0)⁻¹ • ((l0 * D.b0) • x1) +
              (l0 * D.r0)⁻¹ • (x0 ^ 2 : Poly) := by
              simp [smul_add, add_assoc]
        _ = (1 : Poly) + (D.b0 / D.r0) • x1 + (l0 * D.r0)⁻¹ • (x0 ^ 2 : Poly) := by
              rw [hscale, hscalex1]
    have hq1 : IsQuadratic (relationPoly u c1) := isQuadratic_relationPoly hu c1
    have hq1_00 : MvPolynomial.coeff m00 (relationPoly u c1) = 1 := by
      simpa [coeff_m00_x1, coeff_m00_x0sq]
        using congrArg (MvPolynomial.coeff m00) h1
    have hq1_10 : MvPolynomial.coeff m10 (relationPoly u c1) = 0 := by
      simpa [coeff_m10_one, coeff_m10_x1, coeff_m10_x0sq]
        using congrArg (MvPolynomial.coeff m10) h1
    have hq1_11 : MvPolynomial.coeff m11 (relationPoly u c1) = 0 := by
      simpa [coeff_m11_one, coeff_m11_x1, coeff_m11_x0sq]
        using congrArg (MvPolynomial.coeff m11) h1
    have hq1_02 : MvPolynomial.coeff m02 (relationPoly u c1) = 0 := by
      simpa [coeff_m02_one, coeff_m02_x1, coeff_m02_x0sq]
        using congrArg (MvPolynomial.coeff m02) h1
    have htail :
        MvPolynomial.coeff m20
            (affineHom
              (x1ShearMatrix
                (-lowHomQuadPlaneB (relationPoly u D.comp11) (relationPoly u D.comp02) /
                  lowHomQuadPlaneA (relationPoly u D.comp11) (relationPoly u D.comp02)))
              0
              (relationPoly u c1)) ≠ 0 := by
      have hq1_20 :
          MvPolynomial.coeff m20 (relationPoly u c1) = (l0 * D.r0)⁻¹ := by
        simpa [coeff_m20_one, coeff_m20_x1, coeff_m20_x0sq]
          using congrArg (MvPolynomial.coeff m20) h1
      rw [coeff_m20_affineHom_x1Shear hq1, hq1_11, hq1_02, hq1_20]
      simpa [l0] using (inv_ne_zero (mul_ne_zero h00_ne hr0))
    exact residual_eq_zero_of_relations_x0_onePlusBX1Plus_homQuadratics_commonFactorChart
      (B := B) (u := u) hu h0'
      (c1 := c1) (q1 := relationPoly u c1) (by rfl)
      (c2 := D.comp11) (q2 := relationPoly u D.comp11) (by rfl)
      (c3 := D.comp02) (q3 := relationPoly u D.comp02) (by rfl)
      hq1 hq11 hq02
      hq1_00 hq1_10
      hc11_00 hc11_10 hc11_01
      hc02_00 hc02_10 hc02_01
      hA hdiag0 htail hp hsocp

/-- Classifier-level wrapper for the repeated-line subcase of the exact-affine
`dim = 1`, tail-rank `1` range-one branch. Once the extracted inverse
homogeneous-basis matrix has nonzero `x₀²` coordinate and repeated-line
discriminant zero, Lean closes the branch directly through the affine-rank-one
common-factor chart. -/
theorem residual_eq_zero_of_exactAffineDimOne_tailRangeOne_commonFactorComplement
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 1)
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (hrange1 : Module.finrank ℝ (LinearMap.range (x0TailCoeffMap u)) = 1)
    (h00_ne : (exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1).A⁻¹ 0 0 ≠ 0)
    (hdisc0 :
      (exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1).A⁻¹ 0 0 *
          (exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1).A⁻¹ 2 0 -
        ((exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1).A⁻¹ 1 0) ^ 2 = 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  classical
  let D : X0TailHomBasisMatrixData u := exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1
  exact residual_eq_zero_of_relations_x0_tail_hom_basis_matrix_commonFactorComplement
    (B := B) (u := u) hu h0 D h00_ne hdisc0 hp hsocp

/-- In the exact-affine `dim = 1`, tail-rank `1` mixed-support branch, the
subcase `(A⁻¹)₂₀ = 0` and `r₀ = 0` produces the exact shared-`x₁`-tail
relations
`x₁ + a x₀²`, `x₁ + b x₀x₁`, and `x₁²`, so it now closes directly through the
dedicated affine-rank-one endpoint theorem. -/
theorem residual_eq_zero_of_relations_x0_tail_hom_basis_matrix_h20_zero_r0_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (D : X0TailHomBasisMatrixData u)
    (h00_ne : D.A⁻¹ 0 0 ≠ 0)
    (h20 : D.A⁻¹ 2 0 = 0)
    (h10_ne : D.A⁻¹ 1 0 ≠ 0)
    (hr0 : D.r0 = 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let a : ℝ := (D.A⁻¹ 0 0 * D.b0)⁻¹
  let b : ℝ := (D.A⁻¹ 1 0 * D.b0)⁻¹
  have h0' : ∑ i : Fin 4, c0 i • u i = x0 := by
    simpa [relationPoly] using h0
  have hb0 : D.b0 ≠ 0 := X0TailHomBasisMatrixData.b0_ne_zero_of_r0_zero D hr0
  have ha : a ≠ 0 := by
    simp [a, h00_ne, hb0]
  have hb : b ≠ 0 := by
    simp [b, h10_ne, hb0]
  have h1 :
      ∑ i : Fin 4, (a • D.c20) i • u i =
        x1 + a • (x0 ^ 2 : Poly) := by
    simpa [relationPoly, a] using
      X0TailHomBasisMatrixData.relation_c20_normalized_x1Tail_of_h20_zero_r0_zero
        D h00_ne h20 hr0
  have h2 :
      ∑ i : Fin 4, (b • D.c11) i • u i =
        x1 + b • (x0 * x1 : Poly) := by
    simpa [relationPoly, b] using
      X0TailHomBasisMatrixData.relation_c11_normalized_x1Tail_of_h20_zero_r0_zero
        D h10_ne hr0
  have h3 :
      ∑ i : Fin 4, D.c02 i • u i = x1 ^ 2 := by
    simpa [relationPoly] using
      X0TailHomBasisMatrixData.relation_c02_of_h20_zero D h20
  exact residual_eq_zero_of_relations_x0_x1PlusAX0sq_x1PlusBX0x1_x1sq
    (B := B) (u := u) hu ha hb h0' h1 h2 h3 hp hsocp

/-- Classifier-level wrapper for the exact-affine `dim = 1`, tail-rank `1`
subcase `(A⁻¹)₂₀ = 0`, `(A⁻¹)₁₀ ≠ 0`, `r₀ = 0`. -/
theorem residual_eq_zero_of_exactAffineDimOne_tailRangeOne_h20_zero_r0_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 1)
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (hrange1 : Module.finrank ℝ (LinearMap.range (x0TailCoeffMap u)) = 1)
    (h00_ne : (exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1).A⁻¹ 0 0 ≠ 0)
    (h20 : (exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1).A⁻¹ 2 0 = 0)
    (h10_ne : (exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1).A⁻¹ 1 0 ≠ 0)
    (hr0 : (exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1).r0 = 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  classical
  let D : X0TailHomBasisMatrixData u := exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1
  exact residual_eq_zero_of_relations_x0_tail_hom_basis_matrix_h20_zero_r0_zero
    (B := B) (u := u) hu h0 D h00_ne h20 h10_ne hr0 hp hsocp

/-- In the exact-affine `dim = 1`, tail-rank `1` mixed-support branch, the
subcase `(A⁻¹)₂₀ = 0` and `r₀ ≠ 0` produces the exact shared-tail relations
`1 + b x₁ + a x₀²`, `1 + b x₁ + c x₀x₁`, and `x₁²`, so it closes directly
through the dedicated affine-rank-one endpoint theorem. -/
theorem residual_eq_zero_of_relations_x0_tail_hom_basis_matrix_h20_zero_r0_ne_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (D : X0TailHomBasisMatrixData u)
    (h00_ne : D.A⁻¹ 0 0 ≠ 0)
    (h20 : D.A⁻¹ 2 0 = 0)
    (h10_ne : D.A⁻¹ 1 0 ≠ 0)
    (hr0 : D.r0 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let a : ℝ := (D.A⁻¹ 0 0 * D.r0)⁻¹
  let c : ℝ := (D.A⁻¹ 1 0 * D.r0)⁻¹
  let b : ℝ := D.b0 / D.r0
  have h0' : ∑ i : Fin 4, c0 i • u i = x0 := by
    simpa [relationPoly] using h0
  have ha : a ≠ 0 := by
    simp [a, h00_ne, hr0]
  have hc : c ≠ 0 := by
    simp [c, h10_ne, hr0]
  have h1 :
      ∑ i : Fin 4, (a • D.c20) i • u i =
        (1 : Poly) + b • x1 + a • (x0 ^ 2 : Poly) := by
    simpa [relationPoly, a, b] using
      X0TailHomBasisMatrixData.relation_c20_normalized_onePlusBX1_of_h20_zero_r0_ne_zero
        D h00_ne h20 hr0
  have h2 :
      ∑ i : Fin 4, (c • D.c11) i • u i =
        (1 : Poly) + b • x1 + c • (x0 * x1 : Poly) := by
    simpa [relationPoly, b, c] using
      X0TailHomBasisMatrixData.relation_c11_normalized_onePlusBX1_of_h20_zero_r0_ne_zero
        D h10_ne hr0
  have h3 :
      ∑ i : Fin 4, D.c02 i • u i = x1 ^ 2 := by
    simpa [relationPoly] using
      X0TailHomBasisMatrixData.relation_c02_of_h20_zero D h20
  exact residual_eq_zero_of_relations_x0_onePlusBX1PlusAX0sq_onePlusBX1PlusCX0x1_x1sq
    (B := B) (u := u) hu ha hc h0' h1 h2 h3 hp hsocp

/-- Classifier-level wrapper for the exact-affine `dim = 1`, tail-rank `1`
subcase `(A⁻¹)₂₀ = 0`, `(A⁻¹)₁₀ ≠ 0`, `r₀ ≠ 0`. -/
theorem residual_eq_zero_of_exactAffineDimOne_tailRangeOne_h20_zero_r0_ne_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 1)
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (hrange1 : Module.finrank ℝ (LinearMap.range (x0TailCoeffMap u)) = 1)
    (h00_ne : (exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1).A⁻¹ 0 0 ≠ 0)
    (h20 : (exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1).A⁻¹ 2 0 = 0)
    (h10_ne : (exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1).A⁻¹ 1 0 ≠ 0)
    (hr0 : (exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1).r0 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  classical
  let D : X0TailHomBasisMatrixData u := exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1
  exact residual_eq_zero_of_relations_x0_tail_hom_basis_matrix_h20_zero_r0_ne_zero
    (B := B) (u := u) hu h0 D h00_ne h20 h10_ne hr0 hp hsocp

/-- In the exact-affine `dim = 1`, tail-rank `1` mixed-support branch, if the
inverse homogeneous column has vanishing `x₀x₁` entry, nonzero `x₁²` entry,
and zero constant tail, then the extracted basis closes through the exact
shared pure-`x₁` diagonal affine-rank-one endpoint. -/
theorem residual_eq_zero_of_relations_x0_tail_hom_basis_matrix_h10_zero_h20_ne_r0_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (D : X0TailHomBasisMatrixData u)
    (h00_ne : D.A⁻¹ 0 0 ≠ 0)
    (h10 : D.A⁻¹ 1 0 = 0)
    (h20_ne : D.A⁻¹ 2 0 ≠ 0)
    (hr0 : D.r0 = 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let a : ℝ := (D.A⁻¹ 0 0 * D.b0)⁻¹
  let d : ℝ := (D.A⁻¹ 2 0 * D.b0)⁻¹
  have h0' : ∑ i : Fin 4, c0 i • u i = x0 := by
    simpa [relationPoly] using h0
  have hb0 : D.b0 ≠ 0 := X0TailHomBasisMatrixData.b0_ne_zero_of_r0_zero D hr0
  have ha : a ≠ 0 := by
    simp [a, h00_ne, hb0]
  have hd : d ≠ 0 := by
    simp [d, h20_ne, hb0]
  have h1 :
      ∑ i : Fin 4, (a • D.c20) i • u i =
        x1 + a • (x0 ^ 2 : Poly) := by
    change relationPoly u (a • D.c20) = x1 + a • (x0 ^ 2 : Poly)
    rw [relationPoly_smul, X0TailHomBasisMatrixData.relation_c20, hr0]
    have hne : D.A⁻¹ 0 0 * D.b0 ≠ 0 := mul_ne_zero h00_ne hb0
    have hscale : a * (D.A⁻¹ 0 0 * D.b0) = 1 := by
      rw [show a = (D.A⁻¹ 0 0 * D.b0)⁻¹ by rfl]
      exact inv_mul_cancel₀ hne
    rw [smul_add, smul_add, smul_smul, smul_smul, hscale]
    simp
  have h2 :
      ∑ i : Fin 4, D.c11 i • u i = x0 * x1 := by
    change relationPoly u D.c11 = x0 * x1
    rw [X0TailHomBasisMatrixData.relation_c11, h10, hr0]
    simp
  have h3 :
      ∑ i : Fin 4, (d • D.c02) i • u i =
        x1 + d • (x1 ^ 2 : Poly) := by
    change relationPoly u (d • D.c02) = x1 + d • (x1 ^ 2 : Poly)
    rw [relationPoly_smul, X0TailHomBasisMatrixData.relation_c02, hr0]
    have hne : D.A⁻¹ 2 0 * D.b0 ≠ 0 := mul_ne_zero h20_ne hb0
    have hscale : d * (D.A⁻¹ 2 0 * D.b0) = 1 := by
      rw [show d = (D.A⁻¹ 2 0 * D.b0)⁻¹ by rfl]
      exact inv_mul_cancel₀ hne
    rw [smul_add, smul_add, smul_smul, smul_smul, hscale]
    simp
  exact residual_eq_zero_of_relations_x0_x1PlusAX0sq_x0x1_x1PlusDX1sq
    (B := B) (u := u) hu ha hd h0' h1 h2 h3 hp hsocp

/-- Classifier-level wrapper for the exact-affine `dim = 1`, tail-rank `1`
subcase where the extracted inverse homogeneous column satisfies
`A⁻¹₀₀ ≠ 0`, `A⁻¹₁₀ = 0`, `A⁻¹₂₀ ≠ 0`, and the constant tail vanishes. -/
theorem residual_eq_zero_of_exactAffineDimOne_tailRangeOne_h10_zero_h20_ne_r0_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 1)
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (hrange1 : Module.finrank ℝ (LinearMap.range (x0TailCoeffMap u)) = 1)
    (h00_ne : (exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1).A⁻¹ 0 0 ≠ 0)
    (h10 : (exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1).A⁻¹ 1 0 = 0)
    (h20_ne : (exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1).A⁻¹ 2 0 ≠ 0)
    (hr0 : (exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1).r0 = 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  classical
  let D : X0TailHomBasisMatrixData u := exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1
  exact residual_eq_zero_of_relations_x0_tail_hom_basis_matrix_h10_zero_h20_ne_r0_zero
    (B := B) (u := u) hu h0 D h00_ne h10 h20_ne hr0 hp hsocp

/-- In the exact-affine `dim = 1`, tail-rank `1` mixed-support branch, if the
inverse homogeneous column has vanishing `x₀x₁` entry, nonzero `x₁²` entry,
and nonzero constant tail, then the extracted basis closes through the exact
shared constant-plus-`x₁` diagonal affine-rank-one endpoint. -/
theorem residual_eq_zero_of_relations_x0_tail_hom_basis_matrix_h10_zero_h20_ne_r0_ne_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (D : X0TailHomBasisMatrixData u)
    (h00_ne : D.A⁻¹ 0 0 ≠ 0)
    (h10 : D.A⁻¹ 1 0 = 0)
    (h20_ne : D.A⁻¹ 2 0 ≠ 0)
    (hr0 : D.r0 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let a : ℝ := (D.A⁻¹ 0 0 * D.r0)⁻¹
  let d : ℝ := (D.A⁻¹ 2 0 * D.r0)⁻¹
  let b : ℝ := D.b0 / D.r0
  have h0' : ∑ i : Fin 4, c0 i • u i = x0 := by
    simpa [relationPoly] using h0
  have ha : a ≠ 0 := by
    simp [a, h00_ne, hr0]
  have hd : d ≠ 0 := by
    simp [d, h20_ne, hr0]
  have h1 :
      ∑ i : Fin 4, (a • D.c20) i • u i =
        (1 : Poly) + b • x1 + a • (x0 ^ 2 : Poly) := by
    change relationPoly u (a • D.c20) =
      (1 : Poly) + b • x1 + a • (x0 ^ 2 : Poly)
    rw [relationPoly_smul, X0TailHomBasisMatrixData.relation_c20]
    have hne : D.A⁻¹ 0 0 * D.r0 ≠ 0 := mul_ne_zero h00_ne hr0
    have hscale : a * (D.A⁻¹ 0 0 * D.r0) = 1 := by
      rw [show a = (D.A⁻¹ 0 0 * D.r0)⁻¹ by rfl]
      exact inv_mul_cancel₀ hne
    have hscalex1 : a * (D.A⁻¹ 0 0 * D.b0) = b := by
      dsimp [a, b]
      field_simp [h00_ne, hr0]
    rw [smul_add, smul_add, smul_smul, smul_smul, hscale, hscalex1]
    simp
  have h2 :
      ∑ i : Fin 4, D.c11 i • u i = x0 * x1 := by
    change relationPoly u D.c11 = x0 * x1
    rw [X0TailHomBasisMatrixData.relation_c11, h10]
    simp
  have h3 :
      ∑ i : Fin 4, (d • D.c02) i • u i =
        (1 : Poly) + b • x1 + d • (x1 ^ 2 : Poly) := by
    change relationPoly u (d • D.c02) =
      (1 : Poly) + b • x1 + d • (x1 ^ 2 : Poly)
    rw [relationPoly_smul, X0TailHomBasisMatrixData.relation_c02]
    have hne : D.A⁻¹ 2 0 * D.r0 ≠ 0 := mul_ne_zero h20_ne hr0
    have hscale : d * (D.A⁻¹ 2 0 * D.r0) = 1 := by
      rw [show d = (D.A⁻¹ 2 0 * D.r0)⁻¹ by rfl]
      exact inv_mul_cancel₀ hne
    have hscalex1 : d * (D.A⁻¹ 2 0 * D.b0) = b := by
      dsimp [b, d]
      field_simp [h20_ne, hr0]
    rw [smul_add, smul_add, smul_smul, smul_smul, hscale, hscalex1]
    simp
  exact residual_eq_zero_of_relations_x0_onePlusBX1PlusAX0sq_x0x1_onePlusBX1PlusDX1sq
    (B := B) (u := u) hu ha hd h0' h1 h2 h3 hp hsocp

/-- Classifier-level wrapper for the exact-affine `dim = 1`, tail-rank `1`
subcase where the extracted inverse homogeneous column satisfies
`A⁻¹₀₀ ≠ 0`, `A⁻¹₁₀ = 0`, `A⁻¹₂₀ ≠ 0`, and the constant tail is nonzero. -/
theorem residual_eq_zero_of_exactAffineDimOne_tailRangeOne_h10_zero_h20_ne_r0_ne_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 1)
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (hrange1 : Module.finrank ℝ (LinearMap.range (x0TailCoeffMap u)) = 1)
    (h00_ne : (exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1).A⁻¹ 0 0 ≠ 0)
    (h10 : (exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1).A⁻¹ 1 0 = 0)
    (h20_ne : (exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1).A⁻¹ 2 0 ≠ 0)
    (hr0 : (exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1).r0 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  classical
  let D : X0TailHomBasisMatrixData u := exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1
  exact residual_eq_zero_of_relations_x0_tail_hom_basis_matrix_h10_zero_h20_ne_r0_ne_zero
    (B := B) (u := u) hu h0 D h00_ne h10 h20_ne hr0 hp hsocp

/-- In the exact-affine `dim = 1`, tail-rank `1` mixed-support branch, if all
three canonical quadratics `c20/c11/c02` carry the same nonzero
constant-plus-`x₁` tail, then the branch closes directly through the exact
shared-tail affine-rank-one endpoint. -/
theorem residual_eq_zero_of_relations_x0_tail_hom_basis_matrix_h10_ne_h20_ne_r0_ne_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (D : X0TailHomBasisMatrixData u)
    (h00_ne : D.A⁻¹ 0 0 ≠ 0)
    (h10_ne : D.A⁻¹ 1 0 ≠ 0)
    (h20_ne : D.A⁻¹ 2 0 ≠ 0)
    (hr0 : D.r0 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let a : ℝ := (D.A⁻¹ 0 0 * D.r0)⁻¹
  let c : ℝ := (D.A⁻¹ 1 0 * D.r0)⁻¹
  let d : ℝ := (D.A⁻¹ 2 0 * D.r0)⁻¹
  let b : ℝ := D.b0 / D.r0
  have h0' : ∑ i : Fin 4, c0 i • u i = x0 := by
    simpa [relationPoly] using h0
  have ha : a ≠ 0 := by
    simp [a, h00_ne, hr0]
  have hc : c ≠ 0 := by
    simp [c, h10_ne, hr0]
  have hd : d ≠ 0 := by
    simp [d, h20_ne, hr0]
  have h1 :
      ∑ i : Fin 4, (a • D.c20) i • u i =
        (1 : Poly) + b • x1 + a • (x0 ^ 2 : Poly) := by
    change relationPoly u (a • D.c20) =
      (1 : Poly) + b • x1 + a • (x0 ^ 2 : Poly)
    rw [relationPoly_smul, X0TailHomBasisMatrixData.relation_c20]
    have hne : D.A⁻¹ 0 0 * D.r0 ≠ 0 := mul_ne_zero h00_ne hr0
    have hscale : a * (D.A⁻¹ 0 0 * D.r0) = 1 := by
      rw [show a = (D.A⁻¹ 0 0 * D.r0)⁻¹ by rfl]
      exact inv_mul_cancel₀ hne
    have hscalex1 : a * (D.A⁻¹ 0 0 * D.b0) = b := by
      dsimp [a, b]
      field_simp [h00_ne, hr0]
    rw [smul_add, smul_add, smul_smul, smul_smul, hscale, hscalex1]
    simp
  have h2 :
      ∑ i : Fin 4, (c • D.c11) i • u i =
        (1 : Poly) + b • x1 + c • (x0 * x1 : Poly) := by
    change relationPoly u (c • D.c11) =
      (1 : Poly) + b • x1 + c • (x0 * x1 : Poly)
    rw [relationPoly_smul, X0TailHomBasisMatrixData.relation_c11]
    have hne : D.A⁻¹ 1 0 * D.r0 ≠ 0 := mul_ne_zero h10_ne hr0
    have hscale : c * (D.A⁻¹ 1 0 * D.r0) = 1 := by
      rw [show c = (D.A⁻¹ 1 0 * D.r0)⁻¹ by rfl]
      exact inv_mul_cancel₀ hne
    have hscalex1 : c * (D.A⁻¹ 1 0 * D.b0) = b := by
      dsimp [b, c]
      field_simp [h10_ne, hr0]
    rw [smul_add, smul_add, smul_smul, smul_smul, hscale, hscalex1]
    simp
  have h3 :
      ∑ i : Fin 4, (d • D.c02) i • u i =
        (1 : Poly) + b • x1 + d • (x1 ^ 2 : Poly) := by
    change relationPoly u (d • D.c02) =
      (1 : Poly) + b • x1 + d • (x1 ^ 2 : Poly)
    rw [relationPoly_smul, X0TailHomBasisMatrixData.relation_c02]
    have hne : D.A⁻¹ 2 0 * D.r0 ≠ 0 := mul_ne_zero h20_ne hr0
    have hscale : d * (D.A⁻¹ 2 0 * D.r0) = 1 := by
      rw [show d = (D.A⁻¹ 2 0 * D.r0)⁻¹ by rfl]
      exact inv_mul_cancel₀ hne
    have hscalex1 : d * (D.A⁻¹ 2 0 * D.b0) = b := by
      dsimp [b, d]
      field_simp [h20_ne, hr0]
    rw [smul_add, smul_add, smul_smul, smul_smul, hscale, hscalex1]
    simp
  exact residual_eq_zero_of_relations_x0_onePlusBX1PlusAX0sq_onePlusBX1PlusCX0x1_onePlusBX1PlusDX1sq
    (B := B) (u := u) hu ha hc hd h0' h1 h2 h3 hp hsocp

/-- Classifier-level wrapper for the exact-affine `dim = 1`, tail-rank `1`
subcase where the extracted inverse homogeneous column has nonzero
`x₀²/x₀x₁/x₁²` entries and nonzero constant tail. -/
theorem residual_eq_zero_of_exactAffineDimOne_tailRangeOne_h10_ne_h20_ne_r0_ne_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 1)
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (hrange1 : Module.finrank ℝ (LinearMap.range (x0TailCoeffMap u)) = 1)
    (h00_ne : (exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1).A⁻¹ 0 0 ≠ 0)
    (h10_ne : (exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1).A⁻¹ 1 0 ≠ 0)
    (h20_ne : (exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1).A⁻¹ 2 0 ≠ 0)
    (hr0 : (exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1).r0 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  classical
  let D : X0TailHomBasisMatrixData u := exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1
  exact residual_eq_zero_of_relations_x0_tail_hom_basis_matrix_h10_ne_h20_ne_r0_ne_zero
    (B := B) (u := u) hu h0 D h00_ne h10_ne h20_ne hr0 hp hsocp

/-- In the exact-affine `dim = 1`, tail-rank `1` mixed-support branch, if all
three canonical quadratics `c20/c11/c02` carry the same pure `x₁` tail, then
the branch closes directly through the exact shared-tail affine-rank-one
endpoint with three tailed relations. -/
theorem residual_eq_zero_of_relations_x0_tail_hom_basis_matrix_h10_ne_h20_ne_r0_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (D : X0TailHomBasisMatrixData u)
    (h00_ne : D.A⁻¹ 0 0 ≠ 0)
    (h10_ne : D.A⁻¹ 1 0 ≠ 0)
    (h20_ne : D.A⁻¹ 2 0 ≠ 0)
    (hr0 : D.r0 = 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let a : ℝ := (D.A⁻¹ 0 0 * D.b0)⁻¹
  let b : ℝ := (D.A⁻¹ 1 0 * D.b0)⁻¹
  let d : ℝ := (D.A⁻¹ 2 0 * D.b0)⁻¹
  have h0' : ∑ i : Fin 4, c0 i • u i = x0 := by
    simpa [relationPoly] using h0
  have hb0 : D.b0 ≠ 0 := X0TailHomBasisMatrixData.b0_ne_zero_of_r0_zero D hr0
  have ha : a ≠ 0 := by
    simp [a, h00_ne, hb0]
  have hb : b ≠ 0 := by
    simp [b, h10_ne, hb0]
  have hd : d ≠ 0 := by
    simp [d, h20_ne, hb0]
  have h1 :
      ∑ i : Fin 4, (a • D.c20) i • u i =
        x1 + a • (x0 ^ 2 : Poly) := by
    change relationPoly u (a • D.c20) = x1 + a • (x0 ^ 2 : Poly)
    rw [relationPoly_smul, X0TailHomBasisMatrixData.relation_c20, hr0]
    have hne : D.A⁻¹ 0 0 * D.b0 ≠ 0 := mul_ne_zero h00_ne hb0
    have hscale : a * (D.A⁻¹ 0 0 * D.b0) = 1 := by
      rw [show a = (D.A⁻¹ 0 0 * D.b0)⁻¹ by rfl]
      exact inv_mul_cancel₀ hne
    rw [smul_add, smul_add, smul_smul, smul_smul, hscale]
    simp
  have h2 :
      ∑ i : Fin 4, (b • D.c11) i • u i =
        x1 + b • (x0 * x1 : Poly) := by
    simpa [relationPoly, b] using
      X0TailHomBasisMatrixData.relation_c11_normalized_x1Tail_of_h20_zero_r0_zero
        D h10_ne hr0
  have h3 :
      ∑ i : Fin 4, (d • D.c02) i • u i =
        x1 + d • (x1 ^ 2 : Poly) := by
    change relationPoly u (d • D.c02) = x1 + d • (x1 ^ 2 : Poly)
    rw [relationPoly_smul, X0TailHomBasisMatrixData.relation_c02, hr0]
    have hne : D.A⁻¹ 2 0 * D.b0 ≠ 0 := mul_ne_zero h20_ne hb0
    have hscale : d * (D.A⁻¹ 2 0 * D.b0) = 1 := by
      rw [show d = (D.A⁻¹ 2 0 * D.b0)⁻¹ by rfl]
      exact inv_mul_cancel₀ hne
    rw [smul_add, smul_add, smul_smul, smul_smul, hscale]
    simp
  exact residual_eq_zero_of_relations_x0_x1PlusAX0sq_x1PlusBX0x1_x1PlusDX1sq
    (B := B) (u := u) hu ha hb hd h0' h1 h2 h3 hp hsocp

/-- Classifier-level wrapper for the exact-affine `dim = 1`, tail-rank `1`
subcase where the extracted inverse homogeneous column has nonzero
`x₀²/x₀x₁/x₁²` entries and zero constant tail. -/
theorem residual_eq_zero_of_exactAffineDimOne_tailRangeOne_h10_ne_h20_ne_r0_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 1)
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (hrange1 : Module.finrank ℝ (LinearMap.range (x0TailCoeffMap u)) = 1)
    (h00_ne : (exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1).A⁻¹ 0 0 ≠ 0)
    (h10_ne : (exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1).A⁻¹ 1 0 ≠ 0)
    (h20_ne : (exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1).A⁻¹ 2 0 ≠ 0)
    (hr0 : (exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1).r0 = 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  classical
  let D : X0TailHomBasisMatrixData u := exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1
  exact residual_eq_zero_of_relations_x0_tail_hom_basis_matrix_h10_ne_h20_ne_r0_zero
    (B := B) (u := u) hu h0 D h00_ne h10_ne h20_ne hr0 hp hsocp

/-- The exact-affine `dim = 1`, tail-rank `1` branch is now completely closed.
Once the unique exact affine line has been normalized to `x₀`, Lean performs a
finite case split on the first inverse homogeneous-basis column and the common
affine tail, routing every output to one of the already-formalized
affine-rank-one endpoint theorems. -/
theorem residual_eq_zero_of_exactAffineDimOne_tailRangeOne
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 1)
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (hrange1 : Module.finrank ℝ (LinearMap.range (x0TailCoeffMap u)) = 1)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  classical
  let D : X0TailHomBasisMatrixData u := exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1
  by_cases hsimple : D.SimpleBranch
  · exact residual_eq_zero_of_exactAffineDimOne_tailRangeOne_simpleBranch
      (B := B) (u := u) hu hrelker hdim h0 hrange1 hsimple hp hsocp
  have h00_ne : D.A⁻¹ 0 0 ≠ 0 := by
    by_contra h00
    have htail_ne : D.A⁻¹ 1 0 ≠ 0 ∨ D.A⁻¹ 2 0 ≠ 0 := by
      by_contra htail_ne
      have h10 : D.A⁻¹ 1 0 = 0 := by
        by_contra h10
        exact htail_ne (Or.inl h10)
      have h20 : D.A⁻¹ 2 0 = 0 := by
        by_contra h20
        exact htail_ne (Or.inr h20)
      have hunit : IsUnit D.A.det := isUnit_iff_ne_zero.mpr D.hdet
      have hdetInv_ne : D.A⁻¹.det ≠ 0 := by
        intro hdetInv0
        have hmul : D.A⁻¹.det * D.A.det = 1 := Matrix.det_nonsing_inv_mul_det (A := D.A) hunit
        rw [hdetInv0, zero_mul] at hmul
        norm_num at hmul
      have hdetInv0 : D.A⁻¹.det = 0 := by
        apply Matrix.det_eq_zero_of_column_eq_zero (j := 0)
        intro i
        fin_cases i <;> simp [h00, h10, h20]
      exact hdetInv_ne hdetInv0
    exact hsimple (Or.inr ⟨h00, htail_ne⟩)
  by_cases h20 : D.A⁻¹ 2 0 = 0
  · have h10_ne : D.A⁻¹ 1 0 ≠ 0 := by
      by_contra h10
      exact hsimple (Or.inl (Or.inl ⟨h00_ne, h10, h20⟩))
    by_cases hr0 : D.r0 = 0
    · exact residual_eq_zero_of_exactAffineDimOne_tailRangeOne_h20_zero_r0_zero
        (B := B) (u := u) hu hrelker hdim h0 hrange1 h00_ne h20 h10_ne hr0 hp hsocp
    · exact residual_eq_zero_of_exactAffineDimOne_tailRangeOne_h20_zero_r0_ne_zero
        (B := B) (u := u) hu hrelker hdim h0 hrange1 h00_ne h20 h10_ne hr0 hp hsocp
  · by_cases h10 : D.A⁻¹ 1 0 = 0
    · by_cases hr0 : D.r0 = 0
      · exact residual_eq_zero_of_exactAffineDimOne_tailRangeOne_h10_zero_h20_ne_r0_zero
          (B := B) (u := u) hu hrelker hdim h0 hrange1 h00_ne h10 h20 hr0 hp hsocp
      · exact residual_eq_zero_of_exactAffineDimOne_tailRangeOne_h10_zero_h20_ne_r0_ne_zero
          (B := B) (u := u) hu hrelker hdim h0 hrange1 h00_ne h10 h20 hr0 hp hsocp
    · by_cases hr0 : D.r0 = 0
      · exact residual_eq_zero_of_exactAffineDimOne_tailRangeOne_h10_ne_h20_ne_r0_zero
          (B := B) (u := u) hu hrelker hdim h0 hrange1 h00_ne h10 h20 hr0 hp hsocp
      · exact residual_eq_zero_of_exactAffineDimOne_tailRangeOne_h10_ne_h20_ne_r0_ne_zero
          (B := B) (u := u) hu hrelker hdim h0 hrange1 h00_ne h10 h20 hr0 hp hsocp

/-- Backward-compatible corollary of the full tail-rank `1` exact-affine
closure theorem. -/
theorem residual_eq_zero_of_exactAffineDimOne_tailRangeOne_resolvedRegion
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 1)
    {c0 : Fin 4 → ℝ}
    (h0 : relationPoly u c0 = x0)
    (hrange1 : Module.finrank ℝ (LinearMap.range (x0TailCoeffMap u)) = 1)
    (_hresolved :
      (exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1).SimpleBranch ∨
        ((exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1).A⁻¹ 0 0 ≠ 0 ∧
          (exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1).A⁻¹ 0 0 *
              (exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1).A⁻¹ 2 0 -
            ((exactAffineDimOneRangeOneData hu hrelker hdim h0 hrange1).A⁻¹ 1 0) ^ 2 = 0))
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_exactAffineDimOne_tailRangeOne
    (B := B) (u := u) hu hrelker hdim h0 hrange1 hp hsocp

/-- If the exact affine relation space has dimension one and contains no exact
constant relation, then it contains a genuine nonconstant affine line. -/
theorem exists_exactAffine_affineLine_of_dimOne_noConst
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 1)
    (hnoConst : ¬ ∃ c ∈ exactAffineSubmodule u, relationPoly u c = (1 : Poly)) :
    ∃ c : Fin 4 → ℝ, ∃ r a b : ℝ,
      c ∈ exactAffineSubmodule u ∧
      relationPoly u c = affineLinePoly r a b ∧
      a ^ 2 + b ^ 2 ≠ 0 := by
  have hnebot : exactAffineSubmodule u ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hdim
    norm_num at hdim
  rcases (Submodule.ne_bot_iff _).mp hnebot with ⟨c, hc_mem, hc_ne⟩
  let q : Poly := relationPoly u c
  let r : ℝ := MvPolynomial.coeff m00 q
  let a : ℝ := MvPolynomial.coeff m10 q
  let b : ℝ := MvPolynomial.coeff m01 q
  have hqaff : q = affineLinePoly r a b := by
    have hAff := relationPoly_eq_affine_of_mem_exactAffineSubmodule hu hc_mem
    simpa [q, r, a, b, affineLinePoly, MvPolynomial.smul_eq_C_mul, add_assoc] using hAff
  have hrelInj : Function.Injective (relationPolyLin u) := LinearMap.ker_eq_bot.mp hrelker
  have hqne : q ≠ 0 := by
    intro hq0
    apply hc_ne
    have hc0 : relationPolyLin u c = relationPolyLin u 0 := by
      simpa [relationPolyLin, relationPoly, hq0]
    exact hrelInj hc0
  have hab : a ^ 2 + b ^ 2 ≠ 0 := by
    intro hab0
    have ha0 : a = 0 := by nlinarith
    have hb0 : b = 0 := by nlinarith
    have hqconst : q = MvPolynomial.C r := by
      simp [hqaff, affineLinePoly, a, b, ha0, hb0]
    have hrne : r ≠ 0 := by
      intro hr0
      apply hqne
      simp [hqconst, hr0]
    have hone :
        relationPoly u (r⁻¹ • c) = (1 : Poly) := by
      calc
        relationPoly u (r⁻¹ • c) = r⁻¹ • relationPoly u c := by
          exact relationPoly_smul u r⁻¹ c
        _ = r⁻¹ • MvPolynomial.C r := by simpa [q] using congrArg (fun z => r⁻¹ • z) hqconst
        _ = (r⁻¹ * r) • (1 : Poly) := by
          simp [MvPolynomial.smul_eq_C_mul]
        _ = (1 : ℝ) • (1 : Poly) := by
          congr 1
          field_simp [hrne]
        _ = (1 : Poly) := by simp
    exact hnoConst ⟨r⁻¹ • c, Submodule.smul_mem _ _ hc_mem, hone⟩
  exact ⟨c, r, a, b, hc_mem, by simpa [q] using hqaff, hab⟩

private theorem affineLineEquiv_symm_affineLinePoly
    (c a b : ℝ) (hs : a ^ 2 + b ^ 2 ≠ 0) (r u v : ℝ) :
    (affineLineEquiv c a b hs).symm (affineLinePoly r u v) =
      affineLinePoly (r + u * c) (u * a - v * b) (u * b + v * a) := by
  change
    affineHom (affineLineInvMatrix a b) (affineLineInvVec c) (affineLinePoly r u v) =
      affineLinePoly (r + u * c) (u * a - v * b) (u * b + v * a)
  simp [affineLinePoly, affineLineInvMatrix, affineLineInvVec, affineImage, x0, x1,
    Fin.sum_univ_two]
  ring

private theorem mem_exactAffineSubmodule_of_mem_mapVec_affineLineEquiv
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c a b : ℝ}
    (hs : a ^ 2 + b ^ 2 ≠ 0)
    {d : Fin 4 → ℝ}
    (hd :
      d ∈ exactAffineSubmodule
        (mapVec (affineLineEquiv c a b hs).toAlgHom u)) :
    d ∈ exactAffineSubmodule u := by
  let e : Poly ≃ₐ[ℝ] Poly := affineLineEquiv c a b hs
  let u' : RankFourVec := mapVec e.toAlgHom u
  have hu' : IsAdmissiblePoint u' := by
    exact isAdmissiblePoint_mapVec_of_equiv
      (e := e)
      (he := by
        intro q hq
        exact isQuadratic_affineEquiv
          (affineLineMatrix a b) (affineLineInvMatrix a b)
          (affineLineVec c a b) (affineLineInvVec c)
          (affineLine_mul_inv a b hs) (affineLine_inv_mul a b hs)
          (affineLineInv_add_mulVec c a b hs) (affineLine_add_mulVec_inv c a b hs)
          hq)
      hu
  let r : ℝ := MvPolynomial.coeff m00 (relationPoly u' d)
  let u0 : ℝ := MvPolynomial.coeff m10 (relationPoly u' d)
  let v0 : ℝ := MvPolynomial.coeff m01 (relationPoly u' d)
  have hd_aff :
      relationPoly u' d = affineLinePoly r u0 v0 := by
    have hAff := relationPoly_eq_affine_of_mem_exactAffineSubmodule hu' hd
    simpa [r, u0, v0, affineLinePoly, MvPolynomial.smul_eq_C_mul, add_assoc] using hAff
  have hmap : relationPoly u' d = e (relationPoly u d) := by
    simpa [u', e] using (relationPoly_map (φ := e.toAlgHom) (u := u) (c := d))
  have hpre :
      relationPoly u d =
        affineLinePoly (r + u0 * c) (u0 * a - v0 * b) (u0 * b + v0 * a) := by
    calc
      relationPoly u d = e.symm (relationPoly u' d) := by
        rw [hmap]
        simp
      _ = e.symm (affineLinePoly r u0 v0) := by rw [hd_aff]
      _ = affineLinePoly (r + u0 * c) (u0 * a - v0 * b) (u0 * b + v0 * a) := by
            simpa [e] using affineLineEquiv_symm_affineLinePoly c a b hs r u0 v0
  exact mem_exactAffineSubmodule_of_relation_eq_affineLine hpre

private theorem exactAffineDimOne_mapVec_affineLineEquiv
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 1)
    {c0 : Fin 4 → ℝ}
    {c a b : ℝ}
    (h0 : relationPoly u c0 = affineLinePoly c a b)
    (hs : a ^ 2 + b ^ 2 ≠ 0) :
    Module.finrank ℝ
      (exactAffineSubmodule
        (mapVec (affineLineEquiv c a b hs).toAlgHom u)) = 1 := by
  let e : Poly ≃ₐ[ℝ] Poly := affineLineEquiv c a b hs
  let u' : RankFourVec := mapVec e.toAlgHom u
  have hsub :
      exactAffineSubmodule u' ≤ exactAffineSubmodule u := by
    intro d hd
    exact mem_exactAffineSubmodule_of_mem_mapVec_affineLineEquiv hu hs hd
  have hle : Module.finrank ℝ (exactAffineSubmodule u') ≤ 1 := by
    calc
      Module.finrank ℝ (exactAffineSubmodule u') ≤ Module.finrank ℝ (exactAffineSubmodule u) := by
        exact Submodule.finrank_mono hsub
      _ = 1 := hdim
  have h0' : relationPoly u' c0 = x0 := by
    rw [relationPoly_map]
    rw [h0]
    simpa [e] using affineHom_affineLinePoly c a b hs
  have hc0mem : c0 ∈ exactAffineSubmodule u' := by
    have h0aff : relationPoly u' c0 = affineLinePoly 0 1 0 := by
      simpa [affineLinePoly, x0, MvPolynomial.smul_eq_C_mul] using h0'
    exact mem_exactAffineSubmodule_of_relation_eq_affineLine
      h0aff
  have hc0ne : c0 ≠ 0 := by
    intro hc0
    have hzero : (0 : Poly) = x0 := by
      simpa [hc0, relationPoly] using h0'
    have hcoeff := congrArg (MvPolynomial.coeff m10) hzero
    simp [x0, m10] at hcoeff
  have hfin_ne_zero : Module.finrank ℝ (exactAffineSubmodule u') ≠ 0 := by
    intro hzero
    have hbot : exactAffineSubmodule u' = ⊥ := Submodule.finrank_eq_zero.mp hzero
    have : c0 ∈ (⊥ : Submodule ℝ (Fin 4 → ℝ)) := by simpa [hbot] using hc0mem
    exact hc0ne (by simpa using this)
  have hge : 1 ≤ Module.finrank ℝ (exactAffineSubmodule u') := by
    exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hfin_ne_zero)
  exact le_antisymm hle hge

private theorem relationPolyLin_ker_eq_bot_mapVec_affineLineEquiv
    {u : RankFourVec}
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    {c a b : ℝ}
    (hs : a ^ 2 + b ^ 2 ≠ 0) :
    LinearMap.ker
        (relationPolyLin
          (mapVec (affineLineEquiv c a b hs).toAlgHom u)) = ⊥ := by
  let e : Poly ≃ₐ[ℝ] Poly := affineLineEquiv c a b hs
  ext x
  constructor
  · intro hx
    rw [Submodule.mem_bot]
    have hx0' :
        relationPoly (mapVec e.toAlgHom u) x = 0 := by
      simpa [relationPolyLin, relationPoly] using hx
    have hx0 : relationPoly u x = 0 := by
      apply e.injective
      simpa [e, relationPoly_map] using hx0'
    have hrelInj : Function.Injective (relationPolyLin u) :=
      LinearMap.ker_eq_bot.mp hrelker
    exact hrelInj (by simpa [relationPolyLin, relationPoly] using hx0)
  · intro hx
    rw [Submodule.mem_bot] at hx
    subst x
    simp [relationPolyLin]

/-- The tail-rank `0` exact-affine `dim = 1` branch now closes from an
arbitrary exact affine line, not only after the classifier has already
normalized that line to `x₀`. -/
theorem residual_eq_zero_of_exactAffineDimOne_affineLine_tailRangeZero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 1)
    {c0 : Fin 4 → ℝ}
    {r a b : ℝ}
    (h0 : relationPoly u c0 = affineLinePoly r a b)
    (hs : a ^ 2 + b ^ 2 ≠ 0)
    (hrange0 :
      Module.finrank ℝ
        (LinearMap.range
          (x0TailCoeffMap
            (mapVec (affineLineEquiv r a b hs).toAlgHom u))) = 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let e : Poly ≃ₐ[ℝ] Poly := affineLineEquiv r a b hs
  let u' : RankFourVec := mapVec e.toAlgHom u
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  let B0 : DotForm := dotTransport e B
  have hB0pos : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0pos⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e)
      (heQuad := by
        intro q hq
        exact isQuadratic_affineEquiv
          (affineLineMatrix a b) (affineLineInvMatrix a b)
          (affineLineVec r a b) (affineLineInvVec r)
          (affineLine_mul_inv a b hs) (affineLine_inv_mul a b hs)
          (affineLineInv_add_mulVec r a b hs) (affineLine_add_mulVec_inv r a b hs)
          hq)
      (heQuartic := by
        intro q hq
        exact isQuartic_affineEquiv
          (affineLineMatrix a b) (affineLineInvMatrix a b)
          (affineLineVec r a b) (affineLineInvVec r)
          (affineLine_mul_inv a b hs) (affineLine_inv_mul a b hs)
          (affineLineInv_add_mulVec r a b hs) (affineLine_add_mulVec_inv r a b hs)
          hq)
      hp
  have hu0 : IsAdmissiblePoint u' := by
    exact isAdmissiblePoint_mapVec_of_equiv
      (e := e)
      (he := by
        intro q hq
        exact isQuadratic_affineEquiv
          (affineLineMatrix a b) (affineLineInvMatrix a b)
          (affineLineVec r a b) (affineLineInvVec r)
          (affineLine_mul_inv a b hs) (affineLine_inv_mul a b hs)
          (affineLineInv_add_mulVec r a b hs) (affineLine_add_mulVec_inv r a b hs)
          hq)
      hu
  have hsocp0 : IsSOCP B0 (e p) u' := by
    dsimp [B0, u']
    exact isSOCP_mapVec_of_equiv
      (e := e)
      (heSymm := by
        intro q hq
        exact isQuadratic_affineEquiv_symm
          (affineLineMatrix a b) (affineLineInvMatrix a b)
          (affineLineVec r a b) (affineLineInvVec r)
          (affineLine_mul_inv a b hs) (affineLine_inv_mul a b hs)
          (affineLineInv_add_mulVec r a b hs) (affineLine_add_mulVec_inv r a b hs)
          hq)
      hsocp
  have h0' : relationPoly u' c0 = x0 := by
    rw [relationPoly_map]
    rw [h0]
    simpa [e] using affineHom_affineLinePoly r a b hs
  have hdim0 :
      Module.finrank ℝ (exactAffineSubmodule u') = 1 := by
    exact exactAffineDimOne_mapVec_affineLineEquiv hu hdim h0 hs
  have hres0 : residual (e p) u' = 0 := by
    exact residual_eq_zero_of_exactAffineDimOne_tailRangeZero
      (B := B0) (u := u') hu0 hdim0 h0' hrange0 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

/-- The tail-rank `1` exact-affine `dim = 1` branch also transports from an
arbitrary exact affine line to normalized `x₀` coordinates. -/
theorem residual_eq_zero_of_exactAffineDimOne_affineLine_tailRangeOne
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 1)
    {c0 : Fin 4 → ℝ}
    {r a b : ℝ}
    (h0 : relationPoly u c0 = affineLinePoly r a b)
    (hs : a ^ 2 + b ^ 2 ≠ 0)
    (hrange1 :
      Module.finrank ℝ
        (LinearMap.range
          (x0TailCoeffMap
            (mapVec (affineLineEquiv r a b hs).toAlgHom u))) = 1)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let e : Poly ≃ₐ[ℝ] Poly := affineLineEquiv r a b hs
  let u' : RankFourVec := mapVec e.toAlgHom u
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  let B0 : DotForm := dotTransport e B
  have hB0pos : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0pos⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e)
      (heQuad := by
        intro q hq
        exact isQuadratic_affineEquiv
          (affineLineMatrix a b) (affineLineInvMatrix a b)
          (affineLineVec r a b) (affineLineInvVec r)
          (affineLine_mul_inv a b hs) (affineLine_inv_mul a b hs)
          (affineLineInv_add_mulVec r a b hs) (affineLine_add_mulVec_inv r a b hs)
          hq)
      (heQuartic := by
        intro q hq
        exact isQuartic_affineEquiv
          (affineLineMatrix a b) (affineLineInvMatrix a b)
          (affineLineVec r a b) (affineLineInvVec r)
          (affineLine_mul_inv a b hs) (affineLine_inv_mul a b hs)
          (affineLineInv_add_mulVec r a b hs) (affineLine_add_mulVec_inv r a b hs)
          hq)
      hp
  have hu0 : IsAdmissiblePoint u' := by
    exact isAdmissiblePoint_mapVec_of_equiv
      (e := e)
      (he := by
        intro q hq
        exact isQuadratic_affineEquiv
          (affineLineMatrix a b) (affineLineInvMatrix a b)
          (affineLineVec r a b) (affineLineInvVec r)
          (affineLine_mul_inv a b hs) (affineLine_inv_mul a b hs)
          (affineLineInv_add_mulVec r a b hs) (affineLine_add_mulVec_inv r a b hs)
          hq)
      hu
  have hsocp0 : IsSOCP B0 (e p) u' := by
    dsimp [B0, u']
    exact isSOCP_mapVec_of_equiv
      (e := e)
      (heSymm := by
        intro q hq
        exact isQuadratic_affineEquiv_symm
          (affineLineMatrix a b) (affineLineInvMatrix a b)
          (affineLineVec r a b) (affineLineInvVec r)
          (affineLine_mul_inv a b hs) (affineLine_inv_mul a b hs)
          (affineLineInv_add_mulVec r a b hs) (affineLine_add_mulVec_inv r a b hs)
          hq)
      hsocp
  have hrelker0 :
      LinearMap.ker (relationPolyLin u') = ⊥ := by
    simpa [u', e] using relationPolyLin_ker_eq_bot_mapVec_affineLineEquiv hrelker hs
  have h0' : relationPoly u' c0 = x0 := by
    rw [relationPoly_map]
    rw [h0]
    simpa [e] using affineHom_affineLinePoly r a b hs
  have hdim0 :
      Module.finrank ℝ (exactAffineSubmodule u') = 1 := by
    exact exactAffineDimOne_mapVec_affineLineEquiv hu hdim h0 hs
  have hres0 : residual (e p) u' = 0 := by
    exact residual_eq_zero_of_exactAffineDimOne_tailRangeOne
      (B := B0) (u := u') hu0 hrelker0 hdim0 h0' hrange1 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

/-- The tail-rank `2` exact-affine `dim = 1` branch transports from an
arbitrary exact affine line to normalized `x₀` coordinates. -/
theorem residual_eq_zero_of_exactAffineDimOne_affineLine_tailRangeTwo
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 1)
    (hnoConst : ¬ ∃ c ∈ exactAffineSubmodule u, relationPoly u c = (1 : Poly))
    {c0 : Fin 4 → ℝ}
    {r a b : ℝ}
    (h0 : relationPoly u c0 = affineLinePoly r a b)
    (hs : a ^ 2 + b ^ 2 ≠ 0)
    (hrange2 :
      Module.finrank ℝ
        (LinearMap.range
          (x0TailCoeffMap
            (mapVec (affineLineEquiv r a b hs).toAlgHom u))) = 2)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let e : Poly ≃ₐ[ℝ] Poly := affineLineEquiv r a b hs
  let u' : RankFourVec := mapVec e.toAlgHom u
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  let B0 : DotForm := dotTransport e B
  have hB0pos : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0pos⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e)
      (heQuad := by
        intro q hq
        exact isQuadratic_affineEquiv
          (affineLineMatrix a b) (affineLineInvMatrix a b)
          (affineLineVec r a b) (affineLineInvVec r)
          (affineLine_mul_inv a b hs) (affineLine_inv_mul a b hs)
          (affineLineInv_add_mulVec r a b hs) (affineLine_add_mulVec_inv r a b hs)
          hq)
      (heQuartic := by
        intro q hq
        exact isQuartic_affineEquiv
          (affineLineMatrix a b) (affineLineInvMatrix a b)
          (affineLineVec r a b) (affineLineInvVec r)
          (affineLine_mul_inv a b hs) (affineLine_inv_mul a b hs)
          (affineLineInv_add_mulVec r a b hs) (affineLine_add_mulVec_inv r a b hs)
          hq)
      hp
  have hu0 : IsAdmissiblePoint u' := by
    exact isAdmissiblePoint_mapVec_of_equiv
      (e := e)
      (he := by
        intro q hq
        exact isQuadratic_affineEquiv
          (affineLineMatrix a b) (affineLineInvMatrix a b)
          (affineLineVec r a b) (affineLineInvVec r)
          (affineLine_mul_inv a b hs) (affineLine_inv_mul a b hs)
          (affineLineInv_add_mulVec r a b hs) (affineLine_add_mulVec_inv r a b hs)
          hq)
      hu
  have hsocp0 : IsSOCP B0 (e p) u' := by
    dsimp [B0, u']
    exact isSOCP_mapVec_of_equiv
      (e := e)
      (heSymm := by
        intro q hq
        exact isQuadratic_affineEquiv_symm
          (affineLineMatrix a b) (affineLineInvMatrix a b)
          (affineLineVec r a b) (affineLineInvVec r)
          (affineLine_mul_inv a b hs) (affineLine_inv_mul a b hs)
          (affineLineInv_add_mulVec r a b hs) (affineLine_add_mulVec_inv r a b hs)
          hq)
      hsocp
  have hrelker0 :
      LinearMap.ker (relationPolyLin u') = ⊥ := by
    simpa [u', e] using relationPolyLin_ker_eq_bot_mapVec_affineLineEquiv hrelker hs
  have h0' : relationPoly u' c0 = x0 := by
    rw [relationPoly_map]
    rw [h0]
    simpa [e] using affineHom_affineLinePoly r a b hs
  have hdim0 :
      Module.finrank ℝ (exactAffineSubmodule u') = 1 := by
    exact exactAffineDimOne_mapVec_affineLineEquiv hu hdim h0 hs
  have hnoConst0 :
      ¬ ∃ c ∈ exactAffineSubmodule u', relationPoly u' c = (1 : Poly) := by
    intro hconst0
    rcases hconst0 with ⟨c, hc, hc1⟩
    have hc' : c ∈ exactAffineSubmodule u :=
      mem_exactAffineSubmodule_of_mem_mapVec_affineLineEquiv hu hs hc
    have hc1' : relationPoly u c = (1 : Poly) := by
      calc
        relationPoly u c = e.symm (relationPoly u' c) := by
          rw [relationPoly_map]
          simp [e]
        _ = (1 : Poly) := by simp [hc1]
    exact hnoConst ⟨c, hc', hc1'⟩
  have hres0 : residual (e p) u' = 0 := by
    exact residual_eq_zero_of_exactAffineDimOne_tailRangeTwo
      (B := B0) (u := u') hu0 hrelker0 hdim0 hnoConst0 h0' hrange2 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

/-- The whole exact-affine `dim = 1`, no-constant branch closes once one
nonconstant affine line is extracted and the transformed tail map is split by
its only possible ranks `0`, `1`, or `2`. -/
theorem residual_eq_zero_of_exactAffineDimOne_noConst
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hdim : Module.finrank ℝ (exactAffineSubmodule u) = 1)
    (hnoConst : ¬ ∃ c ∈ exactAffineSubmodule u, relationPoly u c = (1 : Poly))
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  obtain ⟨c0, r, a, b, _, h0, hs⟩ :=
    exists_exactAffine_affineLine_of_dimOne_noConst hu hrelker hdim hnoConst
  let u' := mapVec (affineLineEquiv r a b hs).toAlgHom u
  have hrange_le :
      Module.finrank ℝ (LinearMap.range (x0TailCoeffMap u')) ≤ 2 := by
    simpa [u', finrank_top, Module.finrank_fintype_fun_eq_card] using
      (Submodule.finrank_le (LinearMap.range (x0TailCoeffMap u')))
  let n := Module.finrank ℝ (LinearMap.range (x0TailCoeffMap u'))
  have hn_le : n ≤ 2 := hrange_le
  have hn_lt_two_or_eq : n < 2 ∨ n = 2 := Nat.lt_or_eq_of_le hn_le
  rcases hn_lt_two_or_eq with hn_lt_two | hn_two
  · have hn_le_one : n ≤ 1 := Nat.le_of_lt_succ hn_lt_two
    have hn_lt_one_or_eq : n < 1 ∨ n = 1 := Nat.lt_or_eq_of_le hn_le_one
    rcases hn_lt_one_or_eq with hn_lt_one | hn_one
    · have hn_zero : n = 0 := by
        exact Nat.eq_zero_of_not_pos (by
          intro hn_pos
          exact Nat.not_lt_of_ge (Nat.succ_le_of_lt hn_pos) hn_lt_one)
      exact residual_eq_zero_of_exactAffineDimOne_affineLine_tailRangeZero
        (B := B) (u := u) hu hdim h0 hs (by simpa only [n] using hn_zero) hp hsocp
    · exact residual_eq_zero_of_exactAffineDimOne_affineLine_tailRangeOne
        (B := B) (u := u) hu hrelker hdim h0 hs (by simpa only [n] using hn_one) hp hsocp
  · exact residual_eq_zero_of_exactAffineDimOne_affineLine_tailRangeTwo
      (B := B) (u := u) hu hrelker hdim hnoConst h0 hs (by simpa only [n] using hn_two) hp hsocp

/-- Once the four coordinates are linearly independent, the exact-affine
relation space has dimension `1`, `2`, or `3`; the previously formalized
exact-affine branches cover every case. -/
theorem residual_eq_zero_of_relationPolyLin_ker_eq_bot
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let affExact : exactAffineSubmodule u →ₗ[ℝ] (Fin 3 → ℝ) :=
    (affineCoeffMap u).comp (exactAffineSubmodule u).subtype
  have hAffInj : Function.Injective affExact :=
    exactAffineCoeffMap_injective hu hrelker
  have hdom4 : Module.finrank ℝ (Fin 4 → ℝ) = 4 := by
    calc
      Module.finrank ℝ (Fin 4 → ℝ) = Fintype.card (Fin 4) :=
        Module.finrank_fintype_fun_eq_card (R := ℝ) (η := Fin 4)
      _ = 4 := by decide
  let n := Module.finrank ℝ (exactAffineSubmodule u)
  have hn_ge : 1 ≤ n := by
    have hsum := LinearMap.finrank_range_add_finrank_ker (homCoeffMap u)
    have hrange_le :
        Module.finrank ℝ (LinearMap.range (homCoeffMap u)) ≤ 3 := by
      calc
        Module.finrank ℝ (LinearMap.range (homCoeffMap u)) ≤ Module.finrank ℝ (Fin 3 → ℝ) :=
          Submodule.finrank_le (LinearMap.range (homCoeffMap u))
        _ = 3 := by
          rw [Module.finrank_fintype_fun_eq_card]
          decide
    have hsum' :
        Module.finrank ℝ (LinearMap.range (homCoeffMap u)) + n = 4 := by
      simpa [n, exactAffineSubmodule, hdom4] using hsum
    omega
  have hn_le : n ≤ 3 := by
    have hrange :
        Module.finrank ℝ (LinearMap.range affExact) = n := by
      simpa [n] using LinearMap.finrank_range_of_inj hAffInj
    calc
      n = Module.finrank ℝ (LinearMap.range affExact) := hrange.symm
      _ ≤ Module.finrank ℝ (Fin 3 → ℝ) := Submodule.finrank_le (LinearMap.range affExact)
      _ = 3 := by
        rw [Module.finrank_fintype_fun_eq_card]
        decide
  have hn_cases : n = 1 ∨ n = 2 ∨ n = 3 := by
    omega
  rcases hn_cases with hn_one | hn_two | hn_three
  · by_cases hconst : ∃ c ∈ exactAffineSubmodule u, relationPoly u c = (1 : Poly)
    · rcases hconst with ⟨c0, hc0, hc0rel⟩
      exact residual_eq_zero_of_exactAffineDimOne_contains_one
        (B := B) (u := u) hu hrelker (by simpa only [n] using hn_one) hc0 hc0rel hp hsocp
    · exact residual_eq_zero_of_exactAffineDimOne_noConst
        (B := B) (u := u) hu hrelker (by simpa only [n] using hn_one) hconst hp hsocp
  · by_cases hconst : ∃ c ∈ exactAffineSubmodule u, relationPoly u c = (1 : Poly)
    · rcases hconst with ⟨c0, hc0, hc0rel⟩
      exact residual_eq_zero_of_exactAffineDimTwo_contains_one
        (B := B) (u := u) hu hrelker (by simpa only [n] using hn_two) hc0 hc0rel hp hsocp
    · exact residual_eq_zero_of_exactAffineDimTwo_noConst
        (B := B) (u := u) hu hrelker (by simpa only [n] using hn_two) hconst hp hsocp
  · exact residual_eq_zero_of_exactAffineDimThree
      (B := B) (u := u) hu hrelker (by simpa only [n] using hn_three) hp hsocp

end TernaryQuartic
