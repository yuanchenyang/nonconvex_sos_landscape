import TernaryQuarticProof.RepresentativeSpanThree
import TernaryQuarticProof.RepresentativeMixedAffinePlane
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

end TernaryQuartic
