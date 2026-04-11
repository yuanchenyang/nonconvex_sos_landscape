import TernaryQuarticProof.RepresentativeSpanThree
import TernaryQuarticProof.RepresentativeMixedAffinePlane
import TernaryQuarticProof.RepresentativeLowAffine
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

end TernaryQuartic
