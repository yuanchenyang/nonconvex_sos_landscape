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

/-- The polynomial corresponding to a scalar relation vector on a rank-4 point. -/
def relationPoly (u : RankFourVec) (c : Fin 4 → ℝ) : Poly :=
  ∑ i : Fin 4, c i • u i

private theorem relationPoly_add
    (u : RankFourVec) (c d : Fin 4 → ℝ) :
    relationPoly u (c + d) = relationPoly u c + relationPoly u d := by
  simp [relationPoly, Fin.sum_univ_four, add_smul, add_assoc, add_left_comm]

private theorem relationPoly_smul
    (u : RankFourVec) (a : ℝ) (c : Fin 4 → ℝ) :
    relationPoly u (a • c) = a • relationPoly u c := by
  simp [relationPoly, Fin.sum_univ_four, smul_smul]

private theorem relationPoly_map
    (φ : Poly →ₐ[ℝ] Poly) (u : RankFourVec) (c : Fin 4 → ℝ) :
    relationPoly (mapVec φ u) c = φ (relationPoly u c) := by
  simp [relationPoly, mapVec, Fin.sum_univ_four]

private theorem affineHom_translate_affineLine_left
    (r0 r1 : ℝ) :
    affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] (affineLinePoly r0 1 0) = x0 := by
  simp [affineLinePoly, affineHom, affineImage, x0, x1, Fin.sum_univ_two]

private theorem affineHom_translate_affineLine_right
    (r0 r1 : ℝ) :
    affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] (affineLinePoly r1 0 1) = x1 := by
  simp [affineLinePoly, affineHom, affineImage, x0, x1, Fin.sum_univ_two]

/-- Linear map version of `relationPoly`. -/
def relationPolyLin (u : RankFourVec) : (Fin 4 → ℝ) →ₗ[ℝ] Poly where
  toFun := relationPoly u
  map_add' := relationPoly_add u
  map_smul' := relationPoly_smul u

private theorem isQuadratic_relationPoly
    {u : RankFourVec} (hu : IsAdmissiblePoint u) (c : Fin 4 → ℝ) :
    IsQuadratic (relationPoly u c) := by
  have h0 : IsQuadratic (c 0 • u 0) := by
    exact (MvPolynomial.totalDegree_smul_le (c 0) (u 0)).trans (hu 0)
  have h1 : IsQuadratic (c 1 • u 1) := by
    exact (MvPolynomial.totalDegree_smul_le (c 1) (u 1)).trans (hu 1)
  have h2 : IsQuadratic (c 2 • u 2) := by
    exact (MvPolynomial.totalDegree_smul_le (c 2) (u 2)).trans (hu 2)
  have h3 : IsQuadratic (c 3 • u 3) := by
    exact (MvPolynomial.totalDegree_smul_le (c 3) (u 3)).trans (hu 3)
  have h01 : IsQuadratic (c 0 • u 0 + c 1 • u 1) := by
    calc
      (c 0 • u 0 + c 1 • u 1).totalDegree ≤
          max (c 0 • u 0).totalDegree (c 1 • u 1).totalDegree := by
            exact MvPolynomial.totalDegree_add _ _
      _ ≤ 2 := max_le h0 h1
  have h23 : IsQuadratic (c 2 • u 2 + c 3 • u 3) := by
    calc
      (c 2 • u 2 + c 3 • u 3).totalDegree ≤
          max (c 2 • u 2).totalDegree (c 3 • u 3).totalDegree := by
            exact MvPolynomial.totalDegree_add _ _
      _ ≤ 2 := max_le h2 h3
  have hsplit :
      relationPoly u c =
        (c 0 • u 0 + c 1 • u 1) + (c 2 • u 2 + c 3 • u 3) := by
    simp [relationPoly, Fin.sum_univ_four, add_assoc]
  calc
    (relationPoly u c).totalDegree ≤
        max (c 0 • u 0 + c 1 • u 1).totalDegree
          (c 2 • u 2 + c 3 • u 3).totalDegree := by
            rw [hsplit]
            exact MvPolynomial.totalDegree_add _ _
    _ ≤ 2 := max_le h01 h23

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

private theorem coeff_m01_one : MvPolynomial.coeff m01 (1 : Poly) = 0 := by
  rw [MvPolynomial.coeff_one]
  have h : (0 : Fin 2 →₀ ℕ) ≠ m01 := by
    intro hs
    have h1 := congrArg (fun s : Fin 2 →₀ ℕ => s 1) hs
    simp [m01] at h1
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

private theorem coeff_m10_x1sq : MvPolynomial.coeff m10 (x1 ^ 2 : Poly) = 0 := by
  rw [x1, MvPolynomial.coeff_X_pow]
  have h : Finsupp.single 1 2 ≠ m10 := by
    intro hs
    have h0 := congrArg (fun s : Fin 2 →₀ ℕ => s 0) hs
    simp [m10] at h0
  simp [h]

private theorem coeff_m10_x1 : MvPolynomial.coeff m10 (x1 : Poly) = 0 := by
  simp [x1, m10]

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

private theorem coeff_m01_x1 : MvPolynomial.coeff m01 (x1 : Poly) = 1 := by
  simp [x1, m01]

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

end TernaryQuartic
