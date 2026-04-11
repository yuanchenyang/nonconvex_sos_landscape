import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import TernaryQuarticProof.Certificate
import TernaryQuarticProof.AffineSocpTransform
import TernaryQuarticProof.RepresentativeTransport
import TernaryQuarticProof.RepresentativeMixedAffine
import TernaryQuarticProof.MixedAffineNormalization
import TernaryQuarticProof.RepresentativeSpanThree
import TernaryQuarticProof.QuadraticCoordinateForm

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace TernaryQuartic

open scoped BigOperators

/-- Re-expand a two-variable monomial into the fixed `x₀,x₁` basis. -/
private theorem monomial_fin2_eq (s : Fin 2 →₀ ℕ) (a : ℝ) :
    MvPolynomial.monomial s a = (MvPolynomial.C a * x0 ^ s 0) * x1 ^ s 1 := by
  simp [x0, x1, MvPolynomial.monomial_eq, mul_assoc]

/-- Quadratic degree bound for a scalar times `x₀^m x₁^n`. -/
private theorem isQuadratic_C_mul_pow_pow (a : ℝ) (m n : ℕ) (h : m + n ≤ 2) :
    IsQuadratic ((MvPolynomial.C a * x0 ^ m) * x1 ^ n) := by
  calc
    (((MvPolynomial.C a * x0 ^ m) * x1 ^ n) : Poly).totalDegree ≤
        (MvPolynomial.C a * x0 ^ m).totalDegree + (x1 ^ n).totalDegree := by
          exact MvPolynomial.totalDegree_mul _ _
    _ ≤ (MvPolynomial.C a).totalDegree + (x0 ^ m).totalDegree + (x1 ^ n).totalDegree := by
          gcongr
          exact MvPolynomial.totalDegree_mul _ _
    _ = m + n := by simp [x0, x1, MvPolynomial.totalDegree_X_pow]
    _ ≤ 2 := h

private theorem isQuadratic_smul_local (a : ℝ) {q : Poly}
    (hq : IsQuadratic q) :
    IsQuadratic (a • q) := by
  exact (MvPolynomial.totalDegree_smul_le a q).trans hq

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

/-- Turn any explicit scalar relation `∑ cᵢ uᵢ = r` into an admissible image
statement for `r * q`. -/
theorem inAdmissibleImage_of_relation_mul
    {u : RankFourVec} {c : Fin 4 → ℝ} {r q : Poly}
    (hc : ∑ i : Fin 4, c i • u i = r)
    (hq : IsQuadratic q) :
    InAdmissibleImage u (r * q) := by
  refine ⟨relationDirection c q, relationDirection_admissible c hq, ?_⟩
  rw [A_relationDirection, hc]

/-- Linear combination of two explicit scalar relations. -/
private theorem relation_linearCombination
    {u : RankFourVec} {c d : Fin 4 → ℝ} {r s : Poly}
    (hc : ∑ i : Fin 4, c i • u i = r)
    (hd : ∑ i : Fin 4, d i • u i = s)
    (a b : ℝ) :
    ∑ i : Fin 4, (a * c i + b * d i) • u i = a • r + b • s := by
  calc
    ∑ i : Fin 4, (a * c i + b * d i) • u i
        = ∑ i : Fin 4, (a * c i) • u i + ∑ i : Fin 4, (b * d i) • u i := by
            simp [Finset.sum_add_distrib, add_smul]
    _ = a • (∑ i : Fin 4, c i • u i) + b • (∑ i : Fin 4, d i • u i) := by
          simp [Finset.smul_sum, smul_smul]
    _ = a • r + b • s := by rw [hc, hd]

/-- Scalar multiple of an explicit scalar relation. -/
private theorem relation_smul
    {u : RankFourVec} {c : Fin 4 → ℝ} {r : Poly}
    (hc : ∑ i : Fin 4, c i • u i = r)
    (a : ℝ) :
    ∑ i : Fin 4, (a * c i) • u i = a • r := by
  calc
    ∑ i : Fin 4, (a * c i) • u i = a • (∑ i : Fin 4, c i • u i) := by
      simp [Finset.smul_sum, smul_smul]
    _ = a • r := by rw [hc]

/-- Transport an explicit scalar relation through an algebra homomorphism. -/
private theorem relation_map
    (φ : Poly →ₐ[ℝ] Poly)
    {u : RankFourVec} {c : Fin 4 → ℝ} {r : Poly}
    (hc : ∑ i : Fin 4, c i • u i = r) :
    ∑ i : Fin 4, c i • mapVec φ u i = φ r := by
  have hmap := congrArg φ hc
  simpa [mapVec, Fin.sum_univ_four] using hmap

/-- Correct a quadratic relation by subtracting its affine `1,x0` tail. -/
private theorem relation_sub_const_x0
    {u : RankFourVec}
    {c0 c1 c2 : Fin 4 → ℝ} {r : Poly}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    (h2 : ∑ i : Fin 4, c2 i • u i = r)
    (a b : ℝ) :
    ∑ i : Fin 4, (c2 i + (-a) * c1 i + (-b) * c0 i) • u i =
      r - a • (x0 : Poly) - b • (1 : Poly) := by
  have htmp :
      ∑ i : Fin 4, (c2 i + (-a) * c1 i) • u i = r + (-a) • (x0 : Poly) := by
    simpa [add_assoc, add_left_comm, add_comm, mul_comm, mul_left_comm, mul_assoc]
      using relation_linearCombination h2 h1 1 (-a)
  calc
    ∑ i : Fin 4, (c2 i + (-a) * c1 i + (-b) * c0 i) • u i
        = (r + (-a) • (x0 : Poly)) + (-b) • (1 : Poly) := by
            simpa [add_assoc, add_left_comm, add_comm, mul_comm, mul_left_comm, mul_assoc]
              using relation_linearCombination htmp h0 1 (-b)
    _ = r - a • (x0 : Poly) - b • (1 : Poly) := by
          simp [sub_eq_add_neg, add_assoc]

theorem relation_mixedAffineTailHomLine
    {u : RankFourVec} {c2 c3 : Fin 4 → ℝ} {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3) :
    ∑ i : Fin 4,
        (MvPolynomial.coeff m01 q3 * c2 i - MvPolynomial.coeff m01 q2 * c3 i) • u i =
      mixedAffineTailHomLine q2 q3 := by
  simpa [mixedAffineTailHomLine, sub_eq_add_neg, smul_smul, mul_comm, mul_left_comm, mul_assoc]
    using relation_linearCombination h2 h3
      (MvPolynomial.coeff m01 q3) (-MvPolynomial.coeff m01 q2)

private theorem affineX1_eq_of_quadratic_coeffs_zero
    {q : Poly}
    (hq : IsQuadratic q)
    (h20 : MvPolynomial.coeff m20 q = 0)
    (h11 : MvPolynomial.coeff m11 q = 0)
    (h02 : MvPolynomial.coeff m02 q = 0) :
    q =
      MvPolynomial.coeff m00 q • (1 : Poly) +
        MvPolynomial.coeff m10 q • x0 +
          MvPolynomial.coeff m01 q • x1 := by
  calc
    q =
      quadForm
        (MvPolynomial.coeff m00 q)
        (MvPolynomial.coeff m10 q)
        (MvPolynomial.coeff m01 q)
        (MvPolynomial.coeff m20 q)
        (MvPolynomial.coeff m11 q)
        (MvPolynomial.coeff m02 q) := quadratic_eq_quadForm hq
    _ =
      MvPolynomial.coeff m00 q • (1 : Poly) +
        MvPolynomial.coeff m10 q • x0 +
          MvPolynomial.coeff m01 q • x1 := by
            rw [quadForm_eq_explicit, h20, h11, h02]
            simp [MvPolynomial.smul_eq_C_mul, add_comm]

theorem relation_x1_of_affineTail
    {u : RankFourVec} {c0 c1 c2 : Fin 4 → ℝ} {q : Poly}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    (h2 : ∑ i : Fin 4, c2 i • u i = q)
    (hq : IsQuadratic q)
    (h20 : MvPolynomial.coeff m20 q = 0)
    (h11 : MvPolynomial.coeff m11 q = 0)
    (h02 : MvPolynomial.coeff m02 q = 0)
    (h01 : MvPolynomial.coeff m01 q ≠ 0) :
    ∑ i : Fin 4,
        ((1 / MvPolynomial.coeff m01 q) * c2 i
          + (-(MvPolynomial.coeff m00 q / MvPolynomial.coeff m01 q)) * c0 i
          + (-(MvPolynomial.coeff m10 q / MvPolynomial.coeff m01 q)) * c1 i) • u i = x1 := by
  let a00 : ℝ := MvPolynomial.coeff m00 q
  let a10 : ℝ := MvPolynomial.coeff m10 q
  let a01 : ℝ := MvPolynomial.coeff m01 q
  have ha01 : a01 ≠ 0 := by
    simpa [a01] using h01
  have hqaff :
      q = a00 • (1 : Poly) + a10 • x0 + a01 • x1 := by
    simpa [a00, a10, a01] using affineX1_eq_of_quadratic_coeffs_zero hq h20 h11 h02
  have htmp :
      ∑ i : Fin 4,
          ((-(a00 / a01)) * c0 i + (-(a10 / a01)) * c1 i) • u i =
        (-(a00 / a01)) • (1 : Poly) + (-(a10 / a01)) • x0 := by
    simpa using relation_linearCombination h0 h1 (-(a00 / a01)) (-(a10 / a01))
  have hcomb :
      ∑ i : Fin 4,
          ((1 / a01) * c2 i + (((-(a00 / a01)) * c0 i + (-(a10 / a01)) * c1 i))) • u i =
        (1 / a01) • q + ((-(a00 / a01)) • (1 : Poly) + (-(a10 / a01)) • x0) := by
    simpa using relation_linearCombination h2 htmp (1 / a01) 1
  calc
    ∑ i : Fin 4,
        ((1 / MvPolynomial.coeff m01 q) * c2 i
          + (-(MvPolynomial.coeff m00 q / MvPolynomial.coeff m01 q)) * c0 i
          + (-(MvPolynomial.coeff m10 q / MvPolynomial.coeff m01 q)) * c1 i) • u i
        =
      ∑ i : Fin 4,
        ((1 / a01) * c2 i + (((-(a00 / a01)) * c0 i + (-(a10 / a01)) * c1 i))) • u i := by
          simp [a00, a10, a01, add_left_comm, add_comm]
    _ = (1 / a01) • q + ((-(a00 / a01)) • (1 : Poly) + (-(a10 / a01)) • x0) := hcomb
    _ = x1 := by
          rw [hqaff]
          have h00c : (1 / a01) * a00 + (-(a00 / a01)) = 0 := by
            field_simp [ha01]
            ring
          have h10c : (1 / a01) * a10 + (-(a10 / a01)) = 0 := by
            field_simp [ha01]
            ring
          have h01c : (1 / a01) * a01 = 1 := by
            field_simp [ha01]
          have h00c' : a01⁻¹ * a00 + (-(a00 / a01)) = 0 := by
            simpa [one_div] using h00c
          have h10c' : a01⁻¹ * a10 + (-(a10 / a01)) = 0 := by
            simpa [one_div] using h10c
          have h01c' : a01⁻¹ * a01 = 1 := by
            simpa [one_div] using h01c
          calc
            (1 / a01) • (a00 • (1 : Poly) + a10 • x0 + a01 • x1) +
                ((-(a00 / a01)) • (1 : Poly) + (-(a10 / a01)) • x0)
                =
              ((a01⁻¹ * a00) • (1 : Poly) + (-(a00 / a01)) • (1 : Poly)) +
                (((a01⁻¹ * a10) • x0 + (-(a10 / a01)) • x0) +
                  ((a01⁻¹ * a01) • x1)) := by
                    simp [smul_add, smul_smul, add_assoc, add_left_comm, add_comm]
            _ =
              ((a01⁻¹ * a00 + (-(a00 / a01))) • (1 : Poly)) +
                (((a01⁻¹ * a10 + (-(a10 / a01))) • x0) +
                  ((a01⁻¹ * a01) • x1)) := by
                    rw [← add_smul, ← add_smul]
            _ = x1 := by
                  rw [h00c', h10c', h01c']
                  simp

theorem residual_eq_zero_of_relations_const_x0_affineTail
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 : Fin 4 → ℝ} {q : Poly}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    (h2 : ∑ i : Fin 4, c2 i • u i = q)
    (hq : IsQuadratic q)
    (h20 : MvPolynomial.coeff m20 q = 0)
    (h11 : MvPolynomial.coeff m11 q = 0)
    (h02 : MvPolynomial.coeff m02 q = 0)
    (h01 : MvPolynomial.coeff m01 q ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have hx1 :=
    relation_x1_of_affineTail (u := u) h0 h1 h2 hq h20 h11 h02 h01
  exact residual_eq_zero_of_contains_aff1 (B := B) hu h0 h1 hx1 hp hsocp

theorem residual_eq_zero_of_equiv_relations_const_x0_affineTail
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 : Fin 4 → ℝ} {q : Poly}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x0)
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = q)
    (hq : IsQuadratic q)
    (h20 : MvPolynomial.coeff m20 q = 0)
    (h11 : MvPolynomial.coeff m11 q = 0)
    (h02 : MvPolynomial.coeff m02 q = 0)
    (h01 : MvPolynomial.coeff m01 q ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_affineTail
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0 h1 h2 hq h20 h11 h02 h01 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_const_x0_crossTail
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq2_20 : MvPolynomial.coeff m20 q2 = 0)
    (hq2_02 : MvPolynomial.coeff m02 q2 = 0)
    (hq2_11 : MvPolynomial.coeff m11 q2 ≠ 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_02 : MvPolynomial.coeff m02 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (hq3_20 : MvPolynomial.coeff m20 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let b2 : ℝ := MvPolynomial.coeff m11 q2
  let a20 : ℝ := MvPolynomial.coeff m20 q3
  let b3 : ℝ := MvPolynomial.coeff m11 q3
  let a01 : ℝ := MvPolynomial.coeff m01 q3
  have hb2 : b2 ≠ 0 := by
    simpa [b2] using hq2_11
  have ha01 : a01 ≠ 0 := by
    simpa [a01] using hq3_01
  have ha20 : a20 ≠ 0 := by
    simpa [a20] using hq3_20
  have hq2eq : q2 = b2 • (x0 * x1 : Poly) := by
    calc
      q2 =
        b2 • (x0 * x1 : Poly) +
          MvPolynomial.coeff m02 q2 • (x1 ^ 2 : Poly) := by
            simpa using
              homogeneousQuadratic_eq_x0x1_x1sq_of_coeff_m20_zero
                hq2 hq2_00 hq2_10 hq2_01 hq2_20
      _ = b2 • (x0 * x1 : Poly) := by
            rw [hq2_02]
            simp
  have hq3eq :
      q3 =
        a20 • (x0 ^ 2 : Poly) +
          b3 • (x0 * x1 : Poly) +
            a01 • x1 := by
    have hm01 : MvPolynomial.monomial m01 a01 = a01 • x1 := by
      simp [a01, m01, x1, MvPolynomial.monomial_eq, MvPolynomial.smul_eq_C_mul]
    have hm20 : MvPolynomial.monomial m20 a20 = a20 • (x0 ^ 2 : Poly) := by
      simp [a20, m20, x0, MvPolynomial.monomial_eq, MvPolynomial.smul_eq_C_mul]
    have hm11 : MvPolynomial.monomial m11 b3 = b3 • (x0 * x1 : Poly) := by
      simp [b3, m11, x0, x1, MvPolynomial.monomial_eq, MvPolynomial.smul_eq_C_mul]
    calc
      q3 = quadForm 0 0 a01 a20 b3 0 := by
        rw [quadratic_eq_quadForm hq3, hq3_00, hq3_10, hq3_02]
      _ = MvPolynomial.monomial m01 a01 +
            MvPolynomial.monomial m20 a20 +
              MvPolynomial.monomial m11 b3 := by
            simp [quadForm]
      _ = a20 • (x0 ^ 2 : Poly) + b3 • (x0 * x1 : Poly) + a01 • x1 := by
            rw [hm01, hm20, hm11]
            ac_rfl
  let c2' : Fin 4 → ℝ := fun i => (1 / b2) * c2 i
  have h2' : ∑ i : Fin 4, c2' i • u i = x0 * x1 := by
    calc
      ∑ i : Fin 4, c2' i • u i = (1 / b2) • q2 := by
        simpa [c2'] using relation_smul h2 (1 / MvPolynomial.coeff m11 q2)
      _ = (1 / b2) • (b2 • (x0 * x1 : Poly)) := by
            rw [hq2eq]
      _ = x0 * x1 := by
            rw [smul_smul]
            have hscalar : (1 / b2) * b2 = 1 := by
              field_simp [hb2]
            rw [hscalar, one_smul]
  have h3raw :
      ∑ i : Fin 4, (c3 i + (-b3) * c2' i) • u i =
        a20 • (x0 ^ 2 : Poly) + a01 • x1 := by
    calc
      ∑ i : Fin 4, (c3 i + (-b3) * c2' i) • u i
          = 1 • q3 + (-b3) • (x0 * x1 : Poly) := by
              simpa [c2', b3] using relation_linearCombination h3 h2' 1 (-b3)
      _ = a20 • (x0 ^ 2 : Poly) + a01 • x1 := by
              rw [one_smul, hq3eq]
              calc
                a20 • (x0 ^ 2 : Poly) + b3 • (x0 * x1 : Poly) + a01 • x1 +
                    (-b3) • (x0 * x1 : Poly)
                    =
                  a20 • (x0 ^ 2 : Poly) + a01 • x1 +
                    (b3 • (x0 * x1 : Poly) + (-b3) • (x0 * x1 : Poly)) := by
                      ac_rfl
                _ = a20 • (x0 ^ 2 : Poly) + a01 • x1 := by
                      rw [← add_smul]
                      simp
  let c3' : Fin 4 → ℝ := fun i => (1 / a01) * (c3 i + (-b3) * c2' i)
  let a : ℝ := a20 / a01
  have ha : a ≠ 0 := div_ne_zero ha20 ha01
  have h3' :
      ∑ i : Fin 4, c3' i • u i = x1 + a • (x0 ^ 2 : Poly) := by
    calc
      ∑ i : Fin 4, c3' i • u i
          = (1 / a01) • (a20 • (x0 ^ 2 : Poly) + a01 • x1) := by
                  simpa [c3'] using relation_smul h3raw (1 / MvPolynomial.coeff m01 q3)
      _ = x1 + a • (x0 ^ 2 : Poly) := by
            rw [smul_add, smul_smul, smul_smul]
            have h01scalar : (1 / a01) * a01 = 1 := by
              field_simp [ha01]
            have h20scalar : (1 / a01) * a20 = a := by
              dsimp [a]
              rw [one_div, mul_comm, div_eq_mul_inv]
            rw [h01scalar, h20scalar, one_smul]
            ac_rfl
  exact residual_eq_zero_of_relations_const_x0_x0x1_x1PlusX0sq
    (B := B) (u := u) hu h0 h1 h2' h3' ha hp hsocp

theorem residual_eq_zero_of_equiv_relations_const_x0_crossTail
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq2_20 : MvPolynomial.coeff m20 q2 = 0)
    (hq2_02 : MvPolynomial.coeff m02 q2 = 0)
    (hq2_11 : MvPolynomial.coeff m11 q2 ≠ 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_02 : MvPolynomial.coeff m02 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (hq3_20 : MvPolynomial.coeff m20 q3 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_crossTail
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0 h1 h2 h3 hq2 hq3
      hq2_00 hq2_10 hq2_01 hq2_20 hq2_02 hq2_11
      hq3_00 hq3_10 hq3_02 hq3_01 hq3_20 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_const_x0_x1sqTail
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq2_20 : MvPolynomial.coeff m20 q2 = 0)
    (hq2_11 : MvPolynomial.coeff m11 q2 = 0)
    (hq2_02 : MvPolynomial.coeff m02 q2 ≠ 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_11 : MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (hq3_20 : MvPolynomial.coeff m20 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let b2 : ℝ := MvPolynomial.coeff m02 q2
  let a20 : ℝ := MvPolynomial.coeff m20 q3
  let b3 : ℝ := MvPolynomial.coeff m02 q3
  let a01 : ℝ := MvPolynomial.coeff m01 q3
  have hb2 : b2 ≠ 0 := by
    simpa [b2] using hq2_02
  have ha01 : a01 ≠ 0 := by
    simpa [a01] using hq3_01
  have ha20 : a20 ≠ 0 := by
    simpa [a20] using hq3_20
  have hq2eq : q2 = b2 • (x1 ^ 2 : Poly) := by
    calc
      q2 =
        MvPolynomial.coeff m11 q2 • (x0 * x1 : Poly) +
          b2 • (x1 ^ 2 : Poly) := by
            simpa [b2] using
              homogeneousQuadratic_eq_x0x1_x1sq_of_coeff_m20_zero
                hq2 hq2_00 hq2_10 hq2_01 hq2_20
      _ = b2 • (x1 ^ 2 : Poly) := by
            rw [hq2_11]
            simp
  have hq3eq :
      q3 =
        a20 • (x0 ^ 2 : Poly) +
          b3 • (x1 ^ 2 : Poly) +
            a01 • x1 := by
    have hm01 : MvPolynomial.monomial m01 a01 = a01 • x1 := by
      simp [a01, m01, x1, MvPolynomial.monomial_eq, MvPolynomial.smul_eq_C_mul]
    have hm20 : MvPolynomial.monomial m20 a20 = a20 • (x0 ^ 2 : Poly) := by
      simp [a20, m20, x0, MvPolynomial.monomial_eq, MvPolynomial.smul_eq_C_mul]
    have hm02 : MvPolynomial.monomial m02 b3 = b3 • (x1 ^ 2 : Poly) := by
      simp [b3, m02, x1, MvPolynomial.monomial_eq, MvPolynomial.smul_eq_C_mul]
    calc
      q3 = quadForm 0 0 a01 a20 0 b3 := by
        rw [quadratic_eq_quadForm hq3, hq3_00, hq3_10, hq3_11]
      _ = MvPolynomial.monomial m01 a01 +
            MvPolynomial.monomial m20 a20 +
              MvPolynomial.monomial m02 b3 := by
            simp [quadForm]
      _ = a20 • (x0 ^ 2 : Poly) + b3 • (x1 ^ 2 : Poly) + a01 • x1 := by
            rw [hm01, hm20, hm02]
            ac_rfl
  let c2' : Fin 4 → ℝ := fun i => (1 / b2) * c2 i
  have h2' : ∑ i : Fin 4, c2' i • u i = x1 ^ 2 := by
    calc
      ∑ i : Fin 4, c2' i • u i = (1 / b2) • q2 := by
        simpa [c2'] using relation_smul h2 (1 / b2)
      _ = (1 / b2) • (b2 • (x1 ^ 2 : Poly)) := by
            rw [hq2eq]
      _ = x1 ^ 2 := by
            rw [smul_smul]
            have hscalar : (1 / b2) * b2 = 1 := by
              field_simp [hb2]
            rw [hscalar, one_smul]
  have h3raw :
      ∑ i : Fin 4, (c3 i + (-b3) * c2' i) • u i =
        a20 • (x0 ^ 2 : Poly) + a01 • x1 := by
    calc
      ∑ i : Fin 4, (c3 i + (-b3) * c2' i) • u i
          = 1 • q3 + (-b3) • (x1 ^ 2 : Poly) := by
              simpa [c2', b3] using relation_linearCombination h3 h2' 1 (-b3)
      _ = a20 • (x0 ^ 2 : Poly) + a01 • x1 := by
              rw [one_smul, hq3eq]
              calc
                a20 • (x0 ^ 2 : Poly) + b3 • (x1 ^ 2 : Poly) + a01 • x1 +
                    (-b3) • (x1 ^ 2 : Poly)
                    =
                  a20 • (x0 ^ 2 : Poly) + a01 • x1 +
                    (b3 • (x1 ^ 2 : Poly) + (-b3) • (x1 ^ 2 : Poly)) := by
                      ac_rfl
                _ = a20 • (x0 ^ 2 : Poly) + a01 • x1 := by
                      rw [← add_smul]
                      simp
  let c3' : Fin 4 → ℝ := fun i => (1 / a01) * (c3 i + (-b3) * c2' i)
  let a : ℝ := a20 / a01
  have ha : a ≠ 0 := div_ne_zero ha20 ha01
  have h3' :
      ∑ i : Fin 4, c3' i • u i = x1 + a • (x0 ^ 2 : Poly) := by
    calc
      ∑ i : Fin 4, c3' i • u i
          = (1 / a01) • (a20 • (x0 ^ 2 : Poly) + a01 • x1) := by
                  simpa [c3'] using relation_smul h3raw (1 / a01)
      _ = x1 + a • (x0 ^ 2 : Poly) := by
            rw [smul_add, smul_smul, smul_smul]
            have h01scalar : (1 / a01) * a01 = 1 := by
              field_simp [ha01]
            have h20scalar : (1 / a01) * a20 = a := by
              dsimp [a]
              rw [one_div, mul_comm, div_eq_mul_inv]
            rw [h01scalar, h20scalar, one_smul]
            ac_rfl
  exact residual_eq_zero_of_relations_const_x0_x1sq_x1PlusX0sq
    (B := B) (u := u) hu h0 h1 h2' h3' ha hp hsocp

theorem residual_eq_zero_of_equiv_relations_const_x0_x1sqTail
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq2_20 : MvPolynomial.coeff m20 q2 = 0)
    (hq2_11 : MvPolynomial.coeff m11 q2 = 0)
    (hq2_02 : MvPolynomial.coeff m02 q2 ≠ 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_11 : MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (hq3_20 : MvPolynomial.coeff m20 q3 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_x1sqTail
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0 h1 h2 h3 hq2 hq3
      hq2_00 hq2_10 hq2_01 hq2_20 hq2_11 hq2_02
      hq3_00 hq3_10 hq3_11 hq3_01 hq3_20 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_const_x0_diagX1sqTail
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq2_11 : MvPolynomial.coeff m11 q2 = 0)
    (hq2_02 : MvPolynomial.coeff m02 q2 ≠ 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_11 : MvPolynomial.coeff m11 q3 = 0)
    (hq3_02 : MvPolynomial.coeff m02 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (hq3_20 : MvPolynomial.coeff m20 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let b20 : ℝ := MvPolynomial.coeff m20 q2
  let b02 : ℝ := MvPolynomial.coeff m02 q2
  let a20 : ℝ := MvPolynomial.coeff m20 q3
  let a01 : ℝ := MvPolynomial.coeff m01 q3
  have hb02 : b02 ≠ 0 := by
    simpa [b02] using hq2_02
  have ha01 : a01 ≠ 0 := by
    simpa [a01] using hq3_01
  have ha20 : a20 ≠ 0 := by
    simpa [a20] using hq3_20
  have hq2eq : q2 = b20 • (x0 ^ 2 : Poly) + b02 • (x1 ^ 2 : Poly) := by
    simpa [b20, b02] using
      homogeneousQuadratic_eq_x0sq_x1sq_of_coeff_m11_zero
        hq2 hq2_00 hq2_10 hq2_01 hq2_11
  have hq3eq :
      q3 = a20 • (x0 ^ 2 : Poly) + a01 • x1 := by
    have hm01 : MvPolynomial.monomial m01 a01 = a01 • x1 := by
      simp [a01, m01, x1, MvPolynomial.monomial_eq, MvPolynomial.smul_eq_C_mul]
    have hm20 : MvPolynomial.monomial m20 a20 = a20 • (x0 ^ 2 : Poly) := by
      simp [a20, m20, x0, MvPolynomial.monomial_eq, MvPolynomial.smul_eq_C_mul]
    calc
      q3 = quadForm 0 0 a01 a20 0 0 := by
        rw [quadratic_eq_quadForm hq3, hq3_00, hq3_10, hq3_11, hq3_02]
      _ = MvPolynomial.monomial m01 a01 + MvPolynomial.monomial m20 a20 := by
            simp [quadForm]
      _ = a20 • (x0 ^ 2 : Poly) + a01 • x1 := by
            rw [hm01, hm20]
            ac_rfl
  let c2' : Fin 4 → ℝ := fun i => (1 / b02) * c2 i
  let d : ℝ := b20 / b02
  have h2' : ∑ i : Fin 4, c2' i • u i = d • (x0 ^ 2 : Poly) + x1 ^ 2 := by
    calc
      ∑ i : Fin 4, c2' i • u i = (1 / b02) • q2 := by
        simpa [c2'] using relation_smul h2 (1 / b02)
      _ = (1 / b02) • (b20 • (x0 ^ 2 : Poly) + b02 • (x1 ^ 2 : Poly)) := by
            rw [hq2eq]
      _ = d • (x0 ^ 2 : Poly) + x1 ^ 2 := by
            rw [smul_add, smul_smul, smul_smul]
            have h02scalar : (1 / b02) * b02 = 1 := by
              field_simp [hb02]
            have h20scalar : (1 / b02) * b20 = d := by
              dsimp [d]
              rw [one_div, mul_comm, div_eq_mul_inv]
            rw [h02scalar, h20scalar, one_smul]
  let c3' : Fin 4 → ℝ := fun i => (1 / a01) * c3 i
  let a : ℝ := a20 / a01
  have ha : a ≠ 0 := div_ne_zero ha20 ha01
  have h3' :
      ∑ i : Fin 4, c3' i • u i = x1 + a • (x0 ^ 2 : Poly) := by
    calc
      ∑ i : Fin 4, c3' i • u i = (1 / a01) • q3 := by
        simpa [c3'] using relation_smul h3 (1 / a01)
      _ = (1 / a01) • (a20 • (x0 ^ 2 : Poly) + a01 • x1) := by
            rw [hq3eq]
      _ = x1 + a • (x0 ^ 2 : Poly) := by
            rw [smul_add, smul_smul, smul_smul]
            have h01scalar : (1 / a01) * a01 = 1 := by
              field_simp [ha01]
            have h20scalar : (1 / a01) * a20 = a := by
              dsimp [a]
              rw [one_div, mul_comm, div_eq_mul_inv]
            rw [h01scalar, h20scalar, one_smul]
            ac_rfl
  exact residual_eq_zero_of_relations_const_x0_diagX1sq_x1PlusX0sq
    (B := B) (u := u) hu h0 h1 h2' h3' ha hp hsocp

theorem residual_eq_zero_of_equiv_relations_const_x0_diagX1sqTail
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq2_11 : MvPolynomial.coeff m11 q2 = 0)
    (hq2_02 : MvPolynomial.coeff m02 q2 ≠ 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_11 : MvPolynomial.coeff m11 q3 = 0)
    (hq3_02 : MvPolynomial.coeff m02 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (hq3_20 : MvPolynomial.coeff m20 q3 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_diagX1sqTail
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0 h1 h2 h3 hq2 hq3
      hq2_00 hq2_10 hq2_01 hq2_11 hq2_02
      hq3_00 hq3_10 hq3_11 hq3_02 hq3_01 hq3_20 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_const_x0_diagX1sqTail_det
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq2_11 : MvPolynomial.coeff m11 q2 = 0)
    (hq2_02 : MvPolynomial.coeff m02 q2 ≠ 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_11 : MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (hdet :
      MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3 -
        MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m02 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let t : ℝ := MvPolynomial.coeff m02 q3 / MvPolynomial.coeff m02 q2
  let c3' : Fin 4 → ℝ := fun i => c3 i + (-t) * c2 i
  let q3' : Poly := q3 + (-t) • q2
  have hq3' : IsQuadratic q3' := by
    dsimp [q3']
    simpa using isQuadratic_linearCombination_local hq3 hq2 1 (-t)
  have h3' : ∑ i : Fin 4, c3' i • u i = q3' := by
    dsimp [c3', q3']
    simpa using relation_linearCombination h3 h2 1 (-t)
  have hq3'_00 : MvPolynomial.coeff m00 q3' = 0 := by
    dsimp [q3']
    simp [hq2_00, hq3_00]
  have hq3'_10 : MvPolynomial.coeff m10 q3' = 0 := by
    dsimp [q3']
    simp [hq2_10, hq3_10]
  have hq3'_11 : MvPolynomial.coeff m11 q3' = 0 := by
    dsimp [q3']
    simp [hq2_11, hq3_11]
  have hq3'_02 : MvPolynomial.coeff m02 q3' = 0 := by
    dsimp [q3', t]
    have hscalar : MvPolynomial.coeff m02 q3 -
        (MvPolynomial.coeff m02 q3 / MvPolynomial.coeff m02 q2) *
          MvPolynomial.coeff m02 q2 = 0 := by
      field_simp [hq2_02]
      ring
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hscalar
  have hq3'_01 : MvPolynomial.coeff m01 q3' ≠ 0 := by
    dsimp [q3']
    simpa [hq2_01, add_comm, add_left_comm, add_assoc] using hq3_01
  have hq3'_20 : MvPolynomial.coeff m20 q3' ≠ 0 := by
    have hscale :
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3' =
          MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3 -
            MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m02 q3 := by
      dsimp [q3', t]
      simp [sub_eq_add_neg]
      field_simp [hq2_02]
    intro hz
    have hz' :
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3 -
          MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m02 q3 = 0 := by
      rw [← hscale, hz]
      ring
    exact hdet hz'
  exact residual_eq_zero_of_relations_const_x0_diagX1sqTail
    (B := B) (u := u) hu h0 h1 h2 h3' hq2 hq3'
    hq2_00 hq2_10 hq2_01 hq2_11 hq2_02
    hq3'_00 hq3'_10 hq3'_11 hq3'_02 hq3'_01 hq3'_20 hp hsocp

theorem residual_eq_zero_of_equiv_relations_const_x0_diagX1sqTail_det
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq2_11 : MvPolynomial.coeff m11 q2 = 0)
    (hq2_02 : MvPolynomial.coeff m02 q2 ≠ 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_11 : MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (hdet :
      MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3 -
        MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m02 q3 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_diagX1sqTail_det
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0 h1 h2 h3 hq2 hq3
      hq2_00 hq2_10 hq2_01 hq2_11 hq2_02
      hq3_00 hq3_10 hq3_11 hq3_01 hdet hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_crossTail
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_20 : MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hq3_02 : MvPolynomial.coeff m02 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (hq3_20 : MvPolynomial.coeff m20 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let cH : Fin 4 → ℝ :=
    fun i => MvPolynomial.coeff m01 q3 * c2 i - MvPolynomial.coeff m01 q2 * c3 i
  have hH :
      ∑ i : Fin 4, cH i • u i = mixedAffineTailHomLine q2 q3 := by
    simpa [cH] using relation_mixedAffineTailHomLine (u := u) h2 h3
  have hHq : IsQuadratic (mixedAffineTailHomLine q2 q3) :=
    isQuadratic_mixedAffineTailHomLine hq2 hq3
  have hH_00 : MvPolynomial.coeff m00 (mixedAffineTailHomLine q2 q3) = 0 := by
    rw [coeff_m00_mixedAffineTailHomLine, hq2_00, hq3_00]
    ring
  have hH_10 : MvPolynomial.coeff m10 (mixedAffineTailHomLine q2 q3) = 0 := by
    rw [coeff_m10_mixedAffineTailHomLine, hq2_10, hq3_10]
    ring
  have hH_01 : MvPolynomial.coeff m01 (mixedAffineTailHomLine q2 q3) = 0 :=
    coeff_m01_mixedAffineTailHomLine
  exact residual_eq_zero_of_relations_const_x0_crossTail
    (B := B) (u := u) hu h0 h1 hH h3 hHq hq3
    hH_00 hH_10 hH_01 hline_20 hline_02 hline_11
    hq3_00 hq3_10 hq3_02 hq3_01 hq3_20 hp hsocp

theorem residual_eq_zero_of_equiv_relations_const_x0_mixedAffineTailHomLine_crossTail
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_20 : MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hq3_02 : MvPolynomial.coeff m02 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (hq3_20 : MvPolynomial.coeff m20 q3 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_crossTail
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0 h1 h2 h3 hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
      hline_20 hline_02 hline_11 hq3_02 hq3_01 hq3_20 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_crossTail_det
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_20 : MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hdet0 :
      MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (hq3_20 : MvPolynomial.coeff m20 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have hq3_02 : MvPolynomial.coeff m02 q3 = 0 := by
    have hmul :
        MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m02 q3 = 0 := by
      simpa [hline_02] using hdet0
    exact (mul_eq_zero.mp hmul).resolve_left hline_11
  exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_crossTail
    (B := B) (u := u) hu h0 h1 h2 h3 hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
    hline_20 hline_02 hline_11 hq3_02 hq3_01 hq3_20 hp hsocp

theorem residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_crossTail_origDetZero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_20 : MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hqdet0 :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (hq3_20 : MvPolynomial.coeff m20 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have hdet0 :
      MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m11 q3 = 0 := by
    rw [det_m11_m02_mixedAffineTailHomLine]
    simp [hqdet0]
  exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_crossTail_det
    (B := B) (u := u) hu h0 h1 h2 h3 hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
    hline_20 hline_02 hline_11 hdet0 hq3_01 hq3_20 hp hsocp

theorem residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_crossTail_origDetZero_cases
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_20 : MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hqdet0 :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  by_cases hq3_20 : MvPolynomial.coeff m20 q3 = 0
  · have hq3_02 : MvPolynomial.coeff m02 q3 = 0 := by
      have hdet0 :
          MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m02 q3 -
            MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m11 q3 = 0 := by
        rw [det_m11_m02_mixedAffineTailHomLine]
        simp [hqdet0]
      have hmul :
          MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m02 q3 = 0 := by
        simpa [hline_02] using hdet0
      exact (mul_eq_zero.mp hmul).resolve_left hline_11
    let cH : Fin 4 → ℝ :=
      fun i => MvPolynomial.coeff m01 q3 * c2 i - MvPolynomial.coeff m01 q2 * c3 i
    have hH :
        ∑ i : Fin 4, cH i • u i = mixedAffineTailHomLine q2 q3 := by
      simpa [cH] using relation_mixedAffineTailHomLine (u := u) h2 h3
    have hHq : IsQuadratic (mixedAffineTailHomLine q2 q3) :=
      isQuadratic_mixedAffineTailHomLine hq2 hq3
    have hH_00 : MvPolynomial.coeff m00 (mixedAffineTailHomLine q2 q3) = 0 := by
      rw [coeff_m00_mixedAffineTailHomLine, hq2_00, hq3_00]
      ring
    have hH_10 : MvPolynomial.coeff m10 (mixedAffineTailHomLine q2 q3) = 0 := by
      rw [coeff_m10_mixedAffineTailHomLine, hq2_10, hq3_10]
      ring
    have hH_01 : MvPolynomial.coeff m01 (mixedAffineTailHomLine q2 q3) = 0 :=
      coeff_m01_mixedAffineTailHomLine
    let t : ℝ :=
      MvPolynomial.coeff m11 q3 / MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3)
    let c3' : Fin 4 → ℝ := fun i => c3 i + (-t) * cH i
    let q3' : Poly := q3 + (-t) • mixedAffineTailHomLine q2 q3
    have h3' : ∑ i : Fin 4, c3' i • u i = q3' := by
      dsimp [c3', q3']
      simpa using relation_linearCombination h3 hH 1 (-t)
    have hq3' : IsQuadratic q3' := by
      dsimp [q3']
      simpa using isQuadratic_linearCombination_local hq3 hHq 1 (-t)
    have hq3'_00 : MvPolynomial.coeff m00 q3' = 0 := by
      dsimp [q3']
      simp [hq3_00, hH_00]
    have hq3'_10 : MvPolynomial.coeff m10 q3' = 0 := by
      dsimp [q3']
      simp [hq3_10, hH_10]
    have hq3'_20 : MvPolynomial.coeff m20 q3' = 0 := by
      dsimp [q3']
      simp [hq3_20, hline_20]
    have hq3'_02 : MvPolynomial.coeff m02 q3' = 0 := by
      dsimp [q3']
      simp [hq3_02, hline_02]
    have hq3'_11 : MvPolynomial.coeff m11 q3' = 0 := by
      dsimp [q3', t]
      have hscalar :
          MvPolynomial.coeff m11 q3 -
            (MvPolynomial.coeff m11 q3 /
              MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3)) *
              MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) = 0 := by
        field_simp [hline_11]
        ring
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hscalar
    have hq3'_01 : MvPolynomial.coeff m01 q3' ≠ 0 := by
      dsimp [q3']
      simpa [hH_01, add_comm, add_left_comm, add_assoc] using hq3_01
    exact residual_eq_zero_of_relations_const_x0_affineTail
      (B := B) (u := u) hu h0 h1 h3' hq3'
      hq3'_20 hq3'_11 hq3'_02 hq3'_01 hp hsocp
  · exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_crossTail_origDetZero
      (B := B) (u := u) hu h0 h1 h2 h3 hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
      hline_20 hline_02 hline_11 hqdet0 hq3_01 hq3_20 hp hsocp

theorem residual_eq_zero_of_equiv_relations_const_x0_mixedAffineTailHomLine_crossTail_det
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_20 : MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hdet0 :
      MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (hq3_20 : MvPolynomial.coeff m20 q3 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_crossTail_det
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0 h1 h2 h3 hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
      hline_20 hline_02 hline_11 hdet0 hq3_01 hq3_20 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_equiv_relations_const_x0_mixedAffineTailHomLine_crossTail_origDetZero
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_20 : MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hqdet0 :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (hq3_20 : MvPolynomial.coeff m20 q3 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_crossTail_origDetZero
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0 h1 h2 h3 hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
      hline_20 hline_02 hline_11 hqdet0 hq3_01 hq3_20 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_equiv_relations_const_x0_mixedAffineTailHomLine_crossTail_origDetZero_cases
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_20 : MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hqdet0 :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_crossTail_origDetZero_cases
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0 h1 h2 h3 hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
      hline_20 hline_02 hline_11 hqdet0 hq3_01 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

private theorem admissiblePoint_const_x0_pair
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3) :
    IsAdmissiblePoint (![(1 : Poly), x0, q2, q3] : RankFourVec) := by
  intro i
  fin_cases i
  · simp [IsQuadratic]
  · simpa [x0] using (show IsQuadratic (MvPolynomial.X 0 : Poly) by
      simp [IsQuadratic])
  · simpa using hq2
  · simpa using hq3

private def stdRel0 : Fin 4 → ℝ
  | 0 => 1
  | 1 => 0
  | 2 => 0
  | 3 => 0

private def stdRel1 : Fin 4 → ℝ
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 0

private def stdRel2 : Fin 4 → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 0

private def stdRel3 : Fin 4 → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 1

private theorem stdRel23_gram_ne_zero :
    (∑ i : Fin 4, (stdRel2 i) ^ 2) * (∑ i : Fin 4, (stdRel3 i) ^ 2) -
      (∑ i : Fin 4, stdRel2 i * stdRel3 i) ^ 2 ≠ 0 := by
  have hsum2 : ∑ i : Fin 4, (stdRel2 i) ^ 2 = 1 := by
    rw [Fin.sum_univ_four]
    norm_num [stdRel2]
  have hsum3 : ∑ i : Fin 4, (stdRel3 i) ^ 2 = 1 := by
    rw [Fin.sum_univ_four]
    norm_num [stdRel3]
  have hdot : ∑ i : Fin 4, stdRel2 i * stdRel3 i = 0 := by
    rw [Fin.sum_univ_four]
    norm_num [stdRel2, stdRel3]
  rw [hsum2, hsum3, hdot]
  norm_num

theorem residual_eq_zero_of_equiv_const_x0_mixedAffineTailHomLine_crossTail_origDetZero_cases
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {q2 q3 : Poly}
    (h0 : mapVec e.toAlgHom u 0 = (1 : Poly))
    (h1 : mapVec e.toAlgHom u 1 = x0)
    (h2 : mapVec e.toAlgHom u 2 = q2)
    (h3 : mapVec e.toAlgHom u 3 = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_20 : MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hqdet0 :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_crossTail_origDetZero_cases
      (c0 := stdRel0) (c1 := stdRel1) (c2 := stdRel2) (c3 := stdRel3)
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      (h0 := by simpa [stdRel0, Fin.sum_univ_four] using h0)
      (h1 := by simpa [stdRel1, Fin.sum_univ_four] using h1)
      (h2 := by simpa [stdRel2, Fin.sum_univ_four] using h2)
      (h3 := by simpa [stdRel3, Fin.sum_univ_four] using h3)
      hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
      hline_20 hline_02 hline_11 hqdet0 hq3_01 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_socp_of_eq_mix_mapVec_const_x0_mixedAffineTailHomLine_crossTail_origDetZero_cases
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuarticSymm : ∀ {p : Poly}, IsQuartic p → IsQuartic (e.symm p))
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hMtM : M.transpose * M = 1)
    (hMMt : M * M.transpose = 1)
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_20 : MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hqdet0 :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (huRep : mix M.transpose (mapVec e.symm.toAlgHom u) = ![(1 : Poly), x0, q2, q3])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have huRepAdmissible : IsAdmissiblePoint (![(1 : Poly), x0, q2, q3] : RankFourVec) :=
    admissiblePoint_const_x0_pair hq2 hq3
  have hRep :
      ∀ {B0 : DotForm} [Fact B0.toQuadraticMap.PosDef] {p0 : Poly},
        IsSOSQuartic p0 → IsSOCP B0 p0 (![(1 : Poly), x0, q2, q3] : RankFourVec) →
          residual p0 (![(1 : Poly), x0, q2, q3] : RankFourVec) = 0 := by
    intro B0 _ p0 hp0 hsocp0
    exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_crossTail_origDetZero_cases
      (c0 := stdRel0) (c1 := stdRel1) (c2 := stdRel2) (c3 := stdRel3)
      (B := B0) (u := ![(1 : Poly), x0, q2, q3]) huRepAdmissible
      (h0 := by simp [stdRel0, Fin.sum_univ_four])
      (h1 := by simp [stdRel1, Fin.sum_univ_four, x0])
      (h2 := by simp [stdRel2, Fin.sum_univ_four])
      (h3 := by simp [stdRel3, Fin.sum_univ_four])
      hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
      hline_20 hline_02 hline_11 hqdet0 hq3_01 hp0 hsocp0
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec
    (![(1 : Poly), x0, q2, q3])
    hRep e heQuad heQuadSymm heQuarticSymm M hMtM hMMt hB hp huRep hsocp

theorem residual_eq_zero_of_socp_of_eq_mix_affineEquiv_const_x0_mixedAffineTailHomLine_crossTail_origDetZero_cases
    (A A' : Matrix (Fin 2) (Fin 2) ℝ) (b b' : Fin 2 → ℝ)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (hb : ∀ i, b' i + Matrix.mulVec A' b i = 0)
    (hb' : ∀ i, b i + Matrix.mulVec A b' i = 0)
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hMtM : M.transpose * M = 1)
    (hMMt : M * M.transpose = 1)
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_20 : MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hqdet0 :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (huRep :
      mix M.transpose
        (mapVec (affineEquiv A A' b b' hAA' hA'A hb hb').symm.toAlgHom u) =
          ![(1 : Poly), x0, q2, q3])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec_const_x0_mixedAffineTailHomLine_crossTail_origDetZero_cases
    (e := affineEquiv A A' b b' hAA' hA'A hb hb')
    (heQuad := fun {_} hpq => isQuadratic_affineEquiv A A' b b' hAA' hA'A hb hb' hpq)
    (heQuadSymm := fun {_} hpq => isQuadratic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (heQuarticSymm := fun {_} hpq => isQuartic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (M := M) hMtM hMMt hB hp
    hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
    hline_20 hline_02 hline_11 hqdet0 hq3_01 huRep hsocp

theorem residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_crossShear_origDetZero_cases
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hqdet0 :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let hLine : Poly := mixedAffineTailHomLine q2 q3
  let t : ℝ := -(MvPolynomial.coeff m20 hLine / MvPolynomial.coeff m11 hLine)
  let e : Poly ≃ₐ[ℝ] Poly := x1ShearEquiv t
  have h0' : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly) := by
    calc
      ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = e (∑ i : Fin 4, c0 i • u i) := by
        simp [mapVec, map_sum]
      _ = 1 := by rw [h0]; simp
  have h1' : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x0 := by
    calc
      ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = e (∑ i : Fin 4, c1 i • u i) := by
        simp [mapVec, map_sum]
      _ = e x0 := by rw [h1]
      _ = x0 := by
        rw [show e x0 = affineHom (x1ShearMatrix t) 0 x0 by rfl]
        simp [affineHom_x1Shear_x0]
  have h2e : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = e q2 := by
    calc
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = e (∑ i : Fin 4, c2 i • u i) := by
        simp [mapVec, map_sum]
      _ = e q2 := by rw [h2]
  have h3e : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = e q3 := by
    calc
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = e (∑ i : Fin 4, c3 i • u i) := by
        simp [mapVec, map_sum]
      _ = e q3 := by rw [h3]
  have hq2e : IsQuadratic (e q2) := by
    exact isQuadratic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
      (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq2
  have hq3e : IsQuadratic (e q3) := by
    exact isQuadratic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
      (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq3
  let a2 : ℝ := MvPolynomial.coeff m10 (e q2)
  let a3 : ℝ := MvPolynomial.coeff m10 (e q3)
  let c2' : Fin 4 → ℝ := fun i => c2 i + (-a2) * c1 i
  let c3' : Fin 4 → ℝ := fun i => c3 i + (-a3) * c1 i
  let q2' : Poly := e q2 + (-a2) • x0
  let q3' : Poly := e q3 + (-a3) • x0
  have h2' : ∑ i : Fin 4, c2' i • mapVec e.toAlgHom u i = q2' := by
    dsimp [c2', q2']
    simpa using relation_linearCombination h2e h1' 1 (-a2)
  have h3' : ∑ i : Fin 4, c3' i • mapVec e.toAlgHom u i = q3' := by
    dsimp [c3', q3']
    simpa using relation_linearCombination h3e h1' 1 (-a3)
  have hu' : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv
      (e := e)
      (he := fun {_} hpq =>
        isQuadratic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
          (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hpq)
      hu
  have hq2' : IsQuadratic q2' := by
    dsimp [q2']
    simpa [x0] using isQuadratic_linearCombination_local hq2e
      (show IsQuadratic (x0 : Poly) by simp [x0, IsQuadratic]) 1 (-a2)
  have hq3' : IsQuadratic q3' := by
    dsimp [q3']
    simpa [x0] using isQuadratic_linearCombination_local hq3e
      (show IsQuadratic (x0 : Poly) by simp [x0, IsQuadratic]) 1 (-a3)
  have hcoeff01_e_q2 :
      MvPolynomial.coeff m01 (e q2) = MvPolynomial.coeff m01 q2 := by
    change MvPolynomial.coeff m01 (affineHom (x1ShearMatrix t) 0 q2) =
      MvPolynomial.coeff m01 q2
    rw [coeff_m01_affineHom_x1Shear hq2]
  have hcoeff20_e_q2 :
      MvPolynomial.coeff m20 (e q2) =
        MvPolynomial.coeff m20 q2 + MvPolynomial.coeff m11 q2 * t +
          MvPolynomial.coeff m02 q2 * t ^ 2 := by
    change MvPolynomial.coeff m20 (affineHom (x1ShearMatrix t) 0 q2) =
      MvPolynomial.coeff m20 q2 + MvPolynomial.coeff m11 q2 * t +
        MvPolynomial.coeff m02 q2 * t ^ 2
    rw [coeff_m20_affineHom_x1Shear hq2]
  have hcoeff11_e_q2 :
      MvPolynomial.coeff m11 (e q2) =
        MvPolynomial.coeff m11 q2 + 2 * MvPolynomial.coeff m02 q2 * t := by
    change MvPolynomial.coeff m11 (affineHom (x1ShearMatrix t) 0 q2) =
      MvPolynomial.coeff m11 q2 + 2 * MvPolynomial.coeff m02 q2 * t
    rw [coeff_m11_affineHom_x1Shear hq2]
  have hcoeff02_e_q2 :
      MvPolynomial.coeff m02 (e q2) = MvPolynomial.coeff m02 q2 := by
    change MvPolynomial.coeff m02 (affineHom (x1ShearMatrix t) 0 q2) =
      MvPolynomial.coeff m02 q2
    rw [coeff_m02_affineHom_x1Shear hq2]
  have hcoeff00_e_q2 :
      MvPolynomial.coeff m00 (e q2) = 0 := by
    change MvPolynomial.coeff m00 (affineHom (x1ShearMatrix t) 0 q2) = 0
    rw [coeff_m00_affineHom_x1Shear hq2, hq2_00]
  have hcoeff10_e_q2 :
      MvPolynomial.coeff m10 (e q2) =
        MvPolynomial.coeff m10 q2 + MvPolynomial.coeff m01 q2 * t := by
    change MvPolynomial.coeff m10 (affineHom (x1ShearMatrix t) 0 q2) =
      MvPolynomial.coeff m10 q2 + MvPolynomial.coeff m01 q2 * t
    rw [coeff_m10_affineHom_x1Shear hq2]
  have hcoeff01_e_q3 :
      MvPolynomial.coeff m01 (e q3) = MvPolynomial.coeff m01 q3 := by
    change MvPolynomial.coeff m01 (affineHom (x1ShearMatrix t) 0 q3) =
      MvPolynomial.coeff m01 q3
    rw [coeff_m01_affineHom_x1Shear hq3]
  have hcoeff20_e_q3 :
      MvPolynomial.coeff m20 (e q3) =
        MvPolynomial.coeff m20 q3 + MvPolynomial.coeff m11 q3 * t +
          MvPolynomial.coeff m02 q3 * t ^ 2 := by
    change MvPolynomial.coeff m20 (affineHom (x1ShearMatrix t) 0 q3) =
      MvPolynomial.coeff m20 q3 + MvPolynomial.coeff m11 q3 * t +
        MvPolynomial.coeff m02 q3 * t ^ 2
    rw [coeff_m20_affineHom_x1Shear hq3]
  have hcoeff11_e_q3 :
      MvPolynomial.coeff m11 (e q3) =
        MvPolynomial.coeff m11 q3 + 2 * MvPolynomial.coeff m02 q3 * t := by
    change MvPolynomial.coeff m11 (affineHom (x1ShearMatrix t) 0 q3) =
      MvPolynomial.coeff m11 q3 + 2 * MvPolynomial.coeff m02 q3 * t
    rw [coeff_m11_affineHom_x1Shear hq3]
  have hcoeff02_e_q3 :
      MvPolynomial.coeff m02 (e q3) = MvPolynomial.coeff m02 q3 := by
    change MvPolynomial.coeff m02 (affineHom (x1ShearMatrix t) 0 q3) =
      MvPolynomial.coeff m02 q3
    rw [coeff_m02_affineHom_x1Shear hq3]
  have hcoeff00_e_q3 :
      MvPolynomial.coeff m00 (e q3) = 0 := by
    change MvPolynomial.coeff m00 (affineHom (x1ShearMatrix t) 0 q3) = 0
    rw [coeff_m00_affineHom_x1Shear hq3, hq3_00]
  have hcoeff10_e_q3 :
      MvPolynomial.coeff m10 (e q3) =
        MvPolynomial.coeff m10 q3 + MvPolynomial.coeff m01 q3 * t := by
    change MvPolynomial.coeff m10 (affineHom (x1ShearMatrix t) 0 q3) =
      MvPolynomial.coeff m10 q3 + MvPolynomial.coeff m01 q3 * t
    rw [coeff_m10_affineHom_x1Shear hq3]
  have hline_02eq :
      MvPolynomial.coeff m01 q3 * MvPolynomial.coeff m02 q2 -
        MvPolynomial.coeff m01 q2 * MvPolynomial.coeff m02 q3 = 0 := by
    simpa [hLine, coeff_m02_mixedAffineTailHomLine] using hline_02
  have hq2'_01 :
      MvPolynomial.coeff m01 q2' = MvPolynomial.coeff m01 q2 := by
    dsimp [q2', a2]
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, hcoeff01_e_q2]
    simp [x0, m01]
  have hq2'_20 :
      MvPolynomial.coeff m20 q2' =
        MvPolynomial.coeff m20 q2 + MvPolynomial.coeff m11 q2 * t +
          MvPolynomial.coeff m02 q2 * t ^ 2 := by
    dsimp [q2', a2]
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, hcoeff20_e_q2]
    have hx0_20 : MvPolynomial.coeff m20 (x0 : Poly) = 0 := by
      change MvPolynomial.coeff m20 (MvPolynomial.X 0 : Poly) = 0
      rw [MvPolynomial.coeff_X']
      simp [m20]
    simp [hx0_20]
  have hq2'_11 :
      MvPolynomial.coeff m11 q2' =
        MvPolynomial.coeff m11 q2 + 2 * MvPolynomial.coeff m02 q2 * t := by
    dsimp [q2', a2]
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, hcoeff11_e_q2]
    have hx0_11 : MvPolynomial.coeff m11 (x0 : Poly) = 0 := by
      simpa [x0, m11] using (MvPolynomial.coeff_X' (σ := Fin 2) (R := ℝ) 0 m11)
    rw [hx0_11]
    simp
  have hq2'_02 :
      MvPolynomial.coeff m02 q2' = MvPolynomial.coeff m02 q2 := by
    dsimp [q2', a2]
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, hcoeff02_e_q2]
    simp [x0, m02]
  have hq2'_00 : MvPolynomial.coeff m00 q2' = 0 := by
    dsimp [q2', a2]
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, hcoeff00_e_q2]
    simp [x0, m00]
  have hq2'_10 : MvPolynomial.coeff m10 q2' = 0 := by
    dsimp [q2', a2]
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, hcoeff10_e_q2]
    have hx0_10 : MvPolynomial.coeff m10 (x0 : Poly) = 1 := by
      simp [x0, m10]
    rw [hx0_10]
    simp [hq2_10]
  have hq3'_01 :
      MvPolynomial.coeff m01 q3' = MvPolynomial.coeff m01 q3 := by
    dsimp [q3', a3]
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, hcoeff01_e_q3]
    simp [x0, m01]
  have hq3'_20 :
      MvPolynomial.coeff m20 q3' =
        MvPolynomial.coeff m20 q3 + MvPolynomial.coeff m11 q3 * t +
          MvPolynomial.coeff m02 q3 * t ^ 2 := by
    dsimp [q3', a3]
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, hcoeff20_e_q3]
    have hx0_20 : MvPolynomial.coeff m20 (x0 : Poly) = 0 := by
      change MvPolynomial.coeff m20 (MvPolynomial.X 0 : Poly) = 0
      rw [MvPolynomial.coeff_X']
      simp [m20]
    simp [hx0_20]
  have hq3'_11 :
      MvPolynomial.coeff m11 q3' =
        MvPolynomial.coeff m11 q3 + 2 * MvPolynomial.coeff m02 q3 * t := by
    dsimp [q3', a3]
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, hcoeff11_e_q3]
    have hx0_11 : MvPolynomial.coeff m11 (x0 : Poly) = 0 := by
      simpa [x0, m11] using (MvPolynomial.coeff_X' (σ := Fin 2) (R := ℝ) 0 m11)
    rw [hx0_11]
    simp
  have hq3'_02 :
      MvPolynomial.coeff m02 q3' = MvPolynomial.coeff m02 q3 := by
    dsimp [q3', a3]
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, hcoeff02_e_q3]
    simp [x0, m02]
  have hq3'_00 : MvPolynomial.coeff m00 q3' = 0 := by
    dsimp [q3', a3]
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, hcoeff00_e_q3]
    simp [x0, m00]
  have hq3'_10 : MvPolynomial.coeff m10 q3' = 0 := by
    dsimp [q3', a3]
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, hcoeff10_e_q3]
    have hx0_10 : MvPolynomial.coeff m10 (x0 : Poly) = 1 := by
      simp [x0, m10]
    rw [hx0_10]
    simp [hq3_10]
  have hqdet0' :
      MvPolynomial.coeff m11 q2' * MvPolynomial.coeff m02 q3' -
        MvPolynomial.coeff m02 q2' * MvPolynomial.coeff m11 q3' = 0 := by
    rw [hq2'_11, hq3'_02, hq2'_02, hq3'_11]
    ring_nf
    exact hqdet0
  have hq3'_01ne : MvPolynomial.coeff m01 q3' ≠ 0 := by
    rw [hq3'_01]
    exact hq3_01
  have hline_20' :
      MvPolynomial.coeff m20 (mixedAffineTailHomLine q2' q3') = 0 := by
    rw [coeff_m20_mixedAffineTailHomLine, hq3'_01, hq2'_20, hq2'_01, hq3'_20]
    have hline_20e :
        MvPolynomial.coeff m20 (affineHom (x1ShearMatrix t) 0 hLine) = 0 := by
      exact coeff_m20_affineHom_x1Shear_to_cross
        (isQuadratic_mixedAffineTailHomLine hq2 hq3) hline_02 hline_11
    rw [coeff_m20_affineHom_x1Shear (isQuadratic_mixedAffineTailHomLine hq2 hq3) t] at hline_20e
    have hline_20e' :
        MvPolynomial.coeff m01 q3 * MvPolynomial.coeff m20 q2 -
            MvPolynomial.coeff m01 q2 * MvPolynomial.coeff m20 q3 +
              (MvPolynomial.coeff m01 q3 * MvPolynomial.coeff m11 q2 -
                  MvPolynomial.coeff m01 q2 * MvPolynomial.coeff m11 q3) * t +
                MvPolynomial.coeff m02 hLine * t ^ 2 = 0 := by
      simpa [hLine, coeff_m20_mixedAffineTailHomLine, coeff_m11_mixedAffineTailHomLine] using hline_20e
    have hline_20e'' :
        MvPolynomial.coeff m01 q3 * MvPolynomial.coeff m20 q2 -
            MvPolynomial.coeff m01 q2 * MvPolynomial.coeff m20 q3 +
              (MvPolynomial.coeff m01 q3 * MvPolynomial.coeff m11 q2 -
                  MvPolynomial.coeff m01 q2 * MvPolynomial.coeff m11 q3) * t = 0 := by
      rw [hline_02] at hline_20e'
      simpa using hline_20e'
    calc
      MvPolynomial.coeff m01 q3 *
            (MvPolynomial.coeff m20 q2 + MvPolynomial.coeff m11 q2 * t +
                MvPolynomial.coeff m02 q2 * t ^ 2) -
          MvPolynomial.coeff m01 q2 *
            (MvPolynomial.coeff m20 q3 + MvPolynomial.coeff m11 q3 * t +
                MvPolynomial.coeff m02 q3 * t ^ 2)
          =
            (MvPolynomial.coeff m01 q3 * MvPolynomial.coeff m20 q2 -
                MvPolynomial.coeff m01 q2 * MvPolynomial.coeff m20 q3) +
              (MvPolynomial.coeff m01 q3 * MvPolynomial.coeff m11 q2 -
                  MvPolynomial.coeff m01 q2 * MvPolynomial.coeff m11 q3) * t +
                (MvPolynomial.coeff m01 q3 * MvPolynomial.coeff m02 q2 -
                    MvPolynomial.coeff m01 q2 * MvPolynomial.coeff m02 q3) * t ^ 2 := by
              ring
      _ = 0 := by
            rw [hline_20e'', hline_02eq]
            ring
  have hline_02' :
      MvPolynomial.coeff m02 (mixedAffineTailHomLine q2' q3') = 0 := by
    rw [coeff_m02_mixedAffineTailHomLine, hq3'_01, hq2'_02, hq2'_01, hq3'_02]
    simpa [hLine, coeff_m02_mixedAffineTailHomLine] using hline_02
  have hline_11' :
      MvPolynomial.coeff m11 (mixedAffineTailHomLine q2' q3') ≠ 0 := by
    rw [coeff_m11_mixedAffineTailHomLine, hq3'_01, hq2'_11, hq2'_01, hq3'_11]
    have hEq :
        MvPolynomial.coeff m01 q3 * (MvPolynomial.coeff m11 q2 + 2 * MvPolynomial.coeff m02 q2 * t) -
            MvPolynomial.coeff m01 q2 * (MvPolynomial.coeff m11 q3 + 2 * MvPolynomial.coeff m02 q3 * t) =
          MvPolynomial.coeff m11 hLine := by
      calc
        MvPolynomial.coeff m01 q3 * (MvPolynomial.coeff m11 q2 + 2 * MvPolynomial.coeff m02 q2 * t) -
            MvPolynomial.coeff m01 q2 * (MvPolynomial.coeff m11 q3 + 2 * MvPolynomial.coeff m02 q3 * t)
            =
              (MvPolynomial.coeff m01 q3 * MvPolynomial.coeff m11 q2 -
                  MvPolynomial.coeff m01 q2 * MvPolynomial.coeff m11 q3) +
                2 * t *
                  (MvPolynomial.coeff m01 q3 * MvPolynomial.coeff m02 q2 -
                    MvPolynomial.coeff m01 q2 * MvPolynomial.coeff m02 q3) := by
                  ring
        _ = MvPolynomial.coeff m01 q3 * MvPolynomial.coeff m11 q2 -
              MvPolynomial.coeff m01 q2 * MvPolynomial.coeff m11 q3 := by
              simp [hline_02eq]
        _ = MvPolynomial.coeff m11 hLine := by
              simp [hLine, coeff_m11_mixedAffineTailHomLine]
    rw [hEq]
    exact hline_11
  have hBpos : IsPositiveDefinite B := by
    exact (Fact.out : B.toQuadraticMap.PosDef)
  exact residual_eq_zero_of_equiv_relations_const_x0_mixedAffineTailHomLine_crossTail_origDetZero_cases
    (e := e)
    (heQuad := fun {_} hpq =>
      isQuadratic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
        (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hpq)
    (heQuadSymm := fun {_} hpq =>
      isQuadratic_affineEquiv_symm (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
        (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hpq)
    (heQuartic := fun {_} hpq =>
      isQuartic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
        (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hpq)
    (B := B) (p := p) (u := u)
    (hB := hBpos) hp hu hsocp
    (c0 := c0) (c1 := c1) (c2 := c2') (c3 := c3')
    h0' h1' h2' h3' hq2' hq3' hq2'_00 hq2'_10 hq3'_00 hq3'_10
    hline_20' hline_02' hline_11' hqdet0' hq3'_01ne

theorem residual_eq_zero_of_equiv_const_x0_mixedAffineTailHomLine_crossShear_origDetZero_cases
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {q2 q3 : Poly}
    (h0 : mapVec e.toAlgHom u 0 = (1 : Poly))
    (h1 : mapVec e.toAlgHom u 1 = x0)
    (h2 : mapVec e.toAlgHom u 2 = q2)
    (h3 : mapVec e.toAlgHom u 3 = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hqdet0 :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_crossShear_origDetZero_cases
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      (c0 := stdRel0) (c1 := stdRel1) (c2 := stdRel2) (c3 := stdRel3)
      (h0 := by simpa [stdRel0, Fin.sum_univ_four] using h0)
      (h1 := by simpa [stdRel1, Fin.sum_univ_four] using h1)
      (h2 := by simpa [stdRel2, Fin.sum_univ_four] using h2)
      (h3 := by simpa [stdRel3, Fin.sum_univ_four] using h3)
      hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
      hline_02 hline_11 hqdet0 hq3_01 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_socp_of_eq_mix_mapVec_const_x0_mixedAffineTailHomLine_crossShear_origDetZero_cases
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuarticSymm : ∀ {p : Poly}, IsQuartic p → IsQuartic (e.symm p))
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hMtM : M.transpose * M = 1)
    (hMMt : M * M.transpose = 1)
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hqdet0 :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (huRep : mix M.transpose (mapVec e.symm.toAlgHom u) = ![(1 : Poly), x0, q2, q3])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have huRepAdmissible : IsAdmissiblePoint (![(1 : Poly), x0, q2, q3] : RankFourVec) :=
    admissiblePoint_const_x0_pair hq2 hq3
  have hRep :
      ∀ {B0 : DotForm} [Fact B0.toQuadraticMap.PosDef] {p0 : Poly},
        IsSOSQuartic p0 → IsSOCP B0 p0 (![(1 : Poly), x0, q2, q3] : RankFourVec) →
          residual p0 (![(1 : Poly), x0, q2, q3] : RankFourVec) = 0 := by
    intro B0 _ p0 hp0 hsocp0
    exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_crossShear_origDetZero_cases
      (B := B0) (u := ![(1 : Poly), x0, q2, q3]) huRepAdmissible
      (c0 := stdRel0) (c1 := stdRel1) (c2 := stdRel2) (c3 := stdRel3)
      (h0 := by simp [stdRel0, Fin.sum_univ_four])
      (h1 := by simp [stdRel1, Fin.sum_univ_four, x0])
      (h2 := by simp [stdRel2, Fin.sum_univ_four])
      (h3 := by simp [stdRel3, Fin.sum_univ_four])
      hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
      hline_02 hline_11 hqdet0 hq3_01 hp0 hsocp0
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec
    (![(1 : Poly), x0, q2, q3])
    hRep e heQuad heQuadSymm heQuarticSymm M hMtM hMMt hB hp huRep hsocp

theorem residual_eq_zero_of_socp_of_eq_mix_affineEquiv_const_x0_mixedAffineTailHomLine_crossShear_origDetZero_cases
    (A A' : Matrix (Fin 2) (Fin 2) ℝ) (b b' : Fin 2 → ℝ)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (hb : ∀ i, b' i + Matrix.mulVec A' b i = 0)
    (hb' : ∀ i, b i + Matrix.mulVec A b' i = 0)
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hMtM : M.transpose * M = 1)
    (hMMt : M * M.transpose = 1)
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hqdet0 :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (huRep :
      mix M.transpose
        (mapVec (affineEquiv A A' b b' hAA' hA'A hb hb').symm.toAlgHom u) =
          ![(1 : Poly), x0, q2, q3])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec_const_x0_mixedAffineTailHomLine_crossShear_origDetZero_cases
    (e := affineEquiv A A' b b' hAA' hA'A hb hb')
    (heQuad := fun {_} hpq => isQuadratic_affineEquiv A A' b b' hAA' hA'A hb hb' hpq)
    (heQuadSymm := fun {_} hpq => isQuadratic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (heQuarticSymm := fun {_} hpq => isQuartic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (M := M) hMtM hMMt hB hp
    hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
    hline_02 hline_11 hqdet0 hq3_01 huRep hsocp

theorem residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_diagShear_origDetZero_cases
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hqdet0 :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let hLine : Poly := mixedAffineTailHomLine q2 q3
  let t : ℝ := -(MvPolynomial.coeff m11 hLine / (2 * MvPolynomial.coeff m02 hLine))
  let e : Poly ≃ₐ[ℝ] Poly := x1ShearEquiv t
  have h0' : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly) := by
    calc
      ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = e (∑ i : Fin 4, c0 i • u i) := by
        simp [mapVec, map_sum]
      _ = 1 := by rw [h0]; simp
  have h1' : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x0 := by
    calc
      ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = e (∑ i : Fin 4, c1 i • u i) := by
        simp [mapVec, map_sum]
      _ = e x0 := by rw [h1]
      _ = x0 := by
        rw [show e x0 = affineHom (x1ShearMatrix t) 0 x0 by rfl]
        simp [affineHom_x1Shear_x0]
  have h2e : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = e q2 := by
    calc
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = e (∑ i : Fin 4, c2 i • u i) := by
        simp [mapVec, map_sum]
      _ = e q2 := by rw [h2]
  have h3e : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = e q3 := by
    calc
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = e (∑ i : Fin 4, c3 i • u i) := by
        simp [mapVec, map_sum]
      _ = e q3 := by rw [h3]
  have hq2e : IsQuadratic (e q2) := by
    exact isQuadratic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
      (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq2
  have hq3e : IsQuadratic (e q3) := by
    exact isQuadratic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
      (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq3
  let a2 : ℝ := MvPolynomial.coeff m10 (e q2)
  let a3 : ℝ := MvPolynomial.coeff m10 (e q3)
  let c2' : Fin 4 → ℝ := fun i => c2 i + (-a2) * c1 i
  let c3' : Fin 4 → ℝ := fun i => c3 i + (-a3) * c1 i
  let q2' : Poly := e q2 + (-a2) • x0
  let q3' : Poly := e q3 + (-a3) • x0
  have h2' : ∑ i : Fin 4, c2' i • mapVec e.toAlgHom u i = q2' := by
    dsimp [c2', q2']
    simpa using relation_linearCombination h2e h1' 1 (-a2)
  have h3' : ∑ i : Fin 4, c3' i • mapVec e.toAlgHom u i = q3' := by
    dsimp [c3', q3']
    simpa using relation_linearCombination h3e h1' 1 (-a3)
  have hu' : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv
      (e := e)
      (he := fun {_} hpq =>
        isQuadratic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
          (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hpq)
      hu
  have hq2' : IsQuadratic q2' := by
    dsimp [q2']
    simpa [x0] using isQuadratic_linearCombination_local hq2e
      (show IsQuadratic (x0 : Poly) by simp [x0, IsQuadratic]) 1 (-a2)
  have hq3' : IsQuadratic q3' := by
    dsimp [q3']
    simpa [x0] using isQuadratic_linearCombination_local hq3e
      (show IsQuadratic (x0 : Poly) by simp [x0, IsQuadratic]) 1 (-a3)
  have hcoeff01_e_q2 :
      MvPolynomial.coeff m01 (e q2) = MvPolynomial.coeff m01 q2 := by
    change MvPolynomial.coeff m01 (affineHom (x1ShearMatrix t) 0 q2) =
      MvPolynomial.coeff m01 q2
    rw [coeff_m01_affineHom_x1Shear hq2]
  have hcoeff20_e_q2 :
      MvPolynomial.coeff m20 (e q2) =
        MvPolynomial.coeff m20 q2 + MvPolynomial.coeff m11 q2 * t +
          MvPolynomial.coeff m02 q2 * t ^ 2 := by
    change MvPolynomial.coeff m20 (affineHom (x1ShearMatrix t) 0 q2) =
      MvPolynomial.coeff m20 q2 + MvPolynomial.coeff m11 q2 * t +
        MvPolynomial.coeff m02 q2 * t ^ 2
    rw [coeff_m20_affineHom_x1Shear hq2]
  have hcoeff11_e_q2 :
      MvPolynomial.coeff m11 (e q2) =
        MvPolynomial.coeff m11 q2 + 2 * MvPolynomial.coeff m02 q2 * t := by
    change MvPolynomial.coeff m11 (affineHom (x1ShearMatrix t) 0 q2) =
      MvPolynomial.coeff m11 q2 + 2 * MvPolynomial.coeff m02 q2 * t
    rw [coeff_m11_affineHom_x1Shear hq2]
  have hcoeff02_e_q2 :
      MvPolynomial.coeff m02 (e q2) = MvPolynomial.coeff m02 q2 := by
    change MvPolynomial.coeff m02 (affineHom (x1ShearMatrix t) 0 q2) =
      MvPolynomial.coeff m02 q2
    rw [coeff_m02_affineHom_x1Shear hq2]
  have hcoeff00_e_q2 :
      MvPolynomial.coeff m00 (e q2) = 0 := by
    change MvPolynomial.coeff m00 (affineHom (x1ShearMatrix t) 0 q2) = 0
    rw [coeff_m00_affineHom_x1Shear hq2, hq2_00]
  have hcoeff10_e_q2 :
      MvPolynomial.coeff m10 (e q2) =
        MvPolynomial.coeff m10 q2 + MvPolynomial.coeff m01 q2 * t := by
    change MvPolynomial.coeff m10 (affineHom (x1ShearMatrix t) 0 q2) =
      MvPolynomial.coeff m10 q2 + MvPolynomial.coeff m01 q2 * t
    rw [coeff_m10_affineHom_x1Shear hq2]
  have hcoeff01_e_q3 :
      MvPolynomial.coeff m01 (e q3) = MvPolynomial.coeff m01 q3 := by
    change MvPolynomial.coeff m01 (affineHom (x1ShearMatrix t) 0 q3) =
      MvPolynomial.coeff m01 q3
    rw [coeff_m01_affineHom_x1Shear hq3]
  have hcoeff20_e_q3 :
      MvPolynomial.coeff m20 (e q3) =
        MvPolynomial.coeff m20 q3 + MvPolynomial.coeff m11 q3 * t +
          MvPolynomial.coeff m02 q3 * t ^ 2 := by
    change MvPolynomial.coeff m20 (affineHom (x1ShearMatrix t) 0 q3) =
      MvPolynomial.coeff m20 q3 + MvPolynomial.coeff m11 q3 * t +
        MvPolynomial.coeff m02 q3 * t ^ 2
    rw [coeff_m20_affineHom_x1Shear hq3]
  have hcoeff11_e_q3 :
      MvPolynomial.coeff m11 (e q3) =
        MvPolynomial.coeff m11 q3 + 2 * MvPolynomial.coeff m02 q3 * t := by
    change MvPolynomial.coeff m11 (affineHom (x1ShearMatrix t) 0 q3) =
      MvPolynomial.coeff m11 q3 + 2 * MvPolynomial.coeff m02 q3 * t
    rw [coeff_m11_affineHom_x1Shear hq3]
  have hcoeff02_e_q3 :
      MvPolynomial.coeff m02 (e q3) = MvPolynomial.coeff m02 q3 := by
    change MvPolynomial.coeff m02 (affineHom (x1ShearMatrix t) 0 q3) =
      MvPolynomial.coeff m02 q3
    rw [coeff_m02_affineHom_x1Shear hq3]
  have hcoeff00_e_q3 :
      MvPolynomial.coeff m00 (e q3) = 0 := by
    change MvPolynomial.coeff m00 (affineHom (x1ShearMatrix t) 0 q3) = 0
    rw [coeff_m00_affineHom_x1Shear hq3, hq3_00]
  have hcoeff10_e_q3 :
      MvPolynomial.coeff m10 (e q3) =
        MvPolynomial.coeff m10 q3 + MvPolynomial.coeff m01 q3 * t := by
    change MvPolynomial.coeff m10 (affineHom (x1ShearMatrix t) 0 q3) =
      MvPolynomial.coeff m10 q3 + MvPolynomial.coeff m01 q3 * t
    rw [coeff_m10_affineHom_x1Shear hq3]
  have hq2'_01 :
      MvPolynomial.coeff m01 q2' = MvPolynomial.coeff m01 q2 := by
    dsimp [q2', a2]
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, hcoeff01_e_q2]
    simp [x0, m01]
  have hq2'_11 :
      MvPolynomial.coeff m11 q2' =
        MvPolynomial.coeff m11 q2 + 2 * MvPolynomial.coeff m02 q2 * t := by
    dsimp [q2', a2]
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, hcoeff11_e_q2]
    have hx0_11 : MvPolynomial.coeff m11 (x0 : Poly) = 0 := by
      simpa [x0, m11] using (MvPolynomial.coeff_X' (σ := Fin 2) (R := ℝ) 0 m11)
    rw [hx0_11]
    simp
  have hq2'_02 :
      MvPolynomial.coeff m02 q2' = MvPolynomial.coeff m02 q2 := by
    dsimp [q2', a2]
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, hcoeff02_e_q2]
    simp [x0, m02]
  have hq2'_00 : MvPolynomial.coeff m00 q2' = 0 := by
    dsimp [q2', a2]
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, hcoeff00_e_q2]
    simp [x0, m00]
  have hq2'_10 : MvPolynomial.coeff m10 q2' = 0 := by
    dsimp [q2', a2]
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, hcoeff10_e_q2]
    have hx0_10 : MvPolynomial.coeff m10 (x0 : Poly) = 1 := by
      simp [x0, m10]
    rw [hx0_10]
    simp [hq2_10]
  have hq3'_01 :
      MvPolynomial.coeff m01 q3' = MvPolynomial.coeff m01 q3 := by
    dsimp [q3', a3]
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, hcoeff01_e_q3]
    simp [x0, m01]
  have hq3'_11 :
      MvPolynomial.coeff m11 q3' =
        MvPolynomial.coeff m11 q3 + 2 * MvPolynomial.coeff m02 q3 * t := by
    dsimp [q3', a3]
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, hcoeff11_e_q3]
    have hx0_11 : MvPolynomial.coeff m11 (x0 : Poly) = 0 := by
      simpa [x0, m11] using (MvPolynomial.coeff_X' (σ := Fin 2) (R := ℝ) 0 m11)
    rw [hx0_11]
    simp
  have hq3'_02 :
      MvPolynomial.coeff m02 q3' = MvPolynomial.coeff m02 q3 := by
    dsimp [q3', a3]
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, hcoeff02_e_q3]
    simp [x0, m02]
  have hq3'_00 : MvPolynomial.coeff m00 q3' = 0 := by
    dsimp [q3', a3]
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, hcoeff00_e_q3]
    simp [x0, m00]
  have hq3'_10 : MvPolynomial.coeff m10 q3' = 0 := by
    dsimp [q3', a3]
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, hcoeff10_e_q3]
    have hx0_10 : MvPolynomial.coeff m10 (x0 : Poly) = 1 := by
      simp [x0, m10]
    rw [hx0_10]
    simp [hq3_10]
  have hqdet0' :
      MvPolynomial.coeff m11 q2' * MvPolynomial.coeff m02 q3' -
        MvPolynomial.coeff m02 q2' * MvPolynomial.coeff m11 q3' = 0 := by
    rw [hq2'_11, hq3'_02, hq2'_02, hq3'_11]
    ring_nf
    exact hqdet0
  have hq3'_01ne : MvPolynomial.coeff m01 q3' ≠ 0 := by
    rw [hq3'_01]
    exact hq3_01
  have hline_11' :
      MvPolynomial.coeff m11 (mixedAffineTailHomLine q2' q3') = 0 := by
    rw [coeff_m11_mixedAffineTailHomLine, hq3'_01, hq2'_11, hq2'_01, hq3'_11]
    have hEq :
        MvPolynomial.coeff m01 q3 * (MvPolynomial.coeff m11 q2 + 2 * MvPolynomial.coeff m02 q2 * t) -
            MvPolynomial.coeff m01 q2 * (MvPolynomial.coeff m11 q3 + 2 * MvPolynomial.coeff m02 q3 * t) =
          MvPolynomial.coeff m11 hLine + 2 * MvPolynomial.coeff m02 hLine * t := by
      calc
        MvPolynomial.coeff m01 q3 * (MvPolynomial.coeff m11 q2 + 2 * MvPolynomial.coeff m02 q2 * t) -
            MvPolynomial.coeff m01 q2 * (MvPolynomial.coeff m11 q3 + 2 * MvPolynomial.coeff m02 q3 * t)
            =
              (MvPolynomial.coeff m01 q3 * MvPolynomial.coeff m11 q2 -
                  MvPolynomial.coeff m01 q2 * MvPolynomial.coeff m11 q3) +
                2 * t *
                  (MvPolynomial.coeff m01 q3 * MvPolynomial.coeff m02 q2 -
                    MvPolynomial.coeff m01 q2 * MvPolynomial.coeff m02 q3) := by
                  ring_nf
        _ = MvPolynomial.coeff m11 hLine + 2 * MvPolynomial.coeff m02 hLine * t := by
              calc
                (MvPolynomial.coeff m01 q3 * MvPolynomial.coeff m11 q2 -
                      MvPolynomial.coeff m01 q2 * MvPolynomial.coeff m11 q3) +
                    2 * t *
                      (MvPolynomial.coeff m01 q3 * MvPolynomial.coeff m02 q2 -
                        MvPolynomial.coeff m01 q2 * MvPolynomial.coeff m02 q3)
                    =
                  MvPolynomial.coeff m11 hLine + 2 * t * MvPolynomial.coeff m02 hLine := by
                    simp [hLine, coeff_m11_mixedAffineTailHomLine, coeff_m02_mixedAffineTailHomLine]
                _ = MvPolynomial.coeff m11 hLine + 2 * MvPolynomial.coeff m02 hLine * t := by
                    ring
    rw [hEq]
    dsimp [t]
    field_simp [hline_02]
    rw [div_self hline_02]
    ring
  have hline_02' :
      MvPolynomial.coeff m02 (mixedAffineTailHomLine q2' q3') ≠ 0 := by
    rw [coeff_m02_mixedAffineTailHomLine, hq3'_01, hq2'_02, hq2'_01, hq3'_02]
    simpa [hLine, coeff_m02_mixedAffineTailHomLine] using hline_02
  let H' : Poly := mixedAffineTailHomLine q2' q3'
  let cH' : Fin 4 → ℝ :=
    fun i => MvPolynomial.coeff m01 q3' * c2' i - MvPolynomial.coeff m01 q2' * c3' i
  have hH' : ∑ i : Fin 4, cH' i • mapVec e.toAlgHom u i = H' := by
    simpa [H', cH'] using relation_mixedAffineTailHomLine (u := mapVec e.toAlgHom u) h2' h3'
  have hHq' : IsQuadratic H' := by
    dsimp [H']
    exact isQuadratic_mixedAffineTailHomLine hq2' hq3'
  have hH'_00 : MvPolynomial.coeff m00 H' = 0 := by
    dsimp [H']
    rw [coeff_m00_mixedAffineTailHomLine, hq2'_00, hq3'_00]
    ring
  have hH'_10 : MvPolynomial.coeff m10 H' = 0 := by
    dsimp [H']
    rw [coeff_m10_mixedAffineTailHomLine, hq2'_10, hq3'_10]
    ring
  have hH'_01 : MvPolynomial.coeff m01 H' = 0 := by
    dsimp [H']
    exact coeff_m01_mixedAffineTailHomLine
  have hH'_11 : MvPolynomial.coeff m11 H' = 0 := by
    simpa [H'] using hline_11'
  have hH'_02 : MvPolynomial.coeff m02 H' ≠ 0 := by
    simpa [H'] using hline_02'
  have hq3'_11_zero : MvPolynomial.coeff m11 q3' = 0 := by
    have hdet0H' :
        MvPolynomial.coeff m11 H' * MvPolynomial.coeff m02 q3' -
          MvPolynomial.coeff m02 H' * MvPolynomial.coeff m11 q3' = 0 := by
      dsimp [H']
      rw [det_m11_m02_mixedAffineTailHomLine]
      simp [hqdet0']
    have hneg :
        -(MvPolynomial.coeff m02 H' * MvPolynomial.coeff m11 q3') = 0 := by
      simpa [hH'_11] using hdet0H'
    have hmul :
        MvPolynomial.coeff m02 H' * MvPolynomial.coeff m11 q3' = 0 := by
      have hmul' := congrArg Neg.neg hneg
      simpa using hmul'
    exact (mul_eq_zero.mp hmul).resolve_left hH'_02
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := by
    exact isPositiveDefinite_dotTransport e (Fact.out : B.toQuadraticMap.PosDef)
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e)
      (heQuad := fun {_} hpq =>
        isQuadratic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
          (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hpq)
      (heQuartic := fun {_} hpq =>
        isQuartic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
          (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hpq)
      hp
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv
      (e := e)
      (heSymm := fun {_} hpq =>
        isQuadratic_affineEquiv_symm (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
          (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hpq)
      hsocp
  have hres0 : residual (e p) (mapVec e.toAlgHom u) = 0 := by
    by_cases hqdet2' :
        MvPolynomial.coeff m02 q2' * MvPolynomial.coeff m20 q3' -
          MvPolynomial.coeff m20 q2' * MvPolynomial.coeff m02 q3' = 0
    · have hdet2H' :
          MvPolynomial.coeff m02 H' * MvPolynomial.coeff m20 q3' -
            MvPolynomial.coeff m20 H' * MvPolynomial.coeff m02 q3' = 0 := by
        dsimp [H']
        rw [det_m02_m20_mixedAffineTailHomLine]
        simp [hqdet2']
      let t' : ℝ := MvPolynomial.coeff m02 q3' / MvPolynomial.coeff m02 H'
      let c3'' : Fin 4 → ℝ := fun i => c3' i + (-t') * cH' i
      let q3'' : Poly := q3' + (-t') • H'
      have h3'' : ∑ i : Fin 4, c3'' i • mapVec e.toAlgHom u i = q3'' := by
        dsimp [c3'', q3'']
        simpa using relation_linearCombination h3' hH' 1 (-t')
      have hq3'' : IsQuadratic q3'' := by
        dsimp [q3'']
        simpa using isQuadratic_linearCombination_local hq3' hHq' 1 (-t')
      have hq3''_00 : MvPolynomial.coeff m00 q3'' = 0 := by
        dsimp [q3'']
        simp [hq3'_00, hH'_00]
      have hq3''_10 : MvPolynomial.coeff m10 q3'' = 0 := by
        dsimp [q3'']
        simp [hq3'_10, hH'_10]
      have hq3''_11 : MvPolynomial.coeff m11 q3'' = 0 := by
        dsimp [q3'']
        simp [hq3'_11_zero, hH'_11]
      have hq3''_02 : MvPolynomial.coeff m02 q3'' = 0 := by
        rw [show q3'' = q3' + (-t') • H' by rfl, MvPolynomial.coeff_add, MvPolynomial.coeff_smul]
        dsimp [t']
        have hscalar :
            MvPolynomial.coeff m02 q3' +
              -(MvPolynomial.coeff m02 q3' / MvPolynomial.coeff m02 H') *
                MvPolynomial.coeff m02 H' = 0 := by
          field_simp [hH'_02]
          ring
        exact hscalar
      have hq3''_20 : MvPolynomial.coeff m20 q3'' = 0 := by
        have hscale :
            MvPolynomial.coeff m02 H' * MvPolynomial.coeff m20 q3'' =
              MvPolynomial.coeff m02 H' * MvPolynomial.coeff m20 q3' -
                MvPolynomial.coeff m20 H' * MvPolynomial.coeff m02 q3' := by
          dsimp [q3'', t']
          simp [sub_eq_add_neg]
          field_simp [hH'_02]
        have hmul : MvPolynomial.coeff m02 H' * MvPolynomial.coeff m20 q3'' = 0 := by
          rw [hscale, hdet2H']
        exact (mul_eq_zero.mp hmul).resolve_left hH'_02
      have hq3''_01 : MvPolynomial.coeff m01 q3'' ≠ 0 := by
        rw [show q3'' = q3' + (-t') • H' by rfl, MvPolynomial.coeff_add, MvPolynomial.coeff_smul, hH'_01]
        simpa using hq3'_01ne
      exact residual_eq_zero_of_relations_const_x0_affineTail
        (B := B0) (u := mapVec e.toAlgHom u) hu'
        h0' h1' h3'' hq3''
        hq3''_20 hq3''_11 hq3''_02 hq3''_01
        hp0 hsocp0
    · have hdetH' :
          MvPolynomial.coeff m02 H' * MvPolynomial.coeff m20 q3' -
            MvPolynomial.coeff m20 H' * MvPolynomial.coeff m02 q3' ≠ 0 := by
        dsimp [H']
        rw [det_m02_m20_mixedAffineTailHomLine]
        exact mul_ne_zero hq3'_01ne hqdet2'
      exact residual_eq_zero_of_relations_const_x0_diagX1sqTail_det
        (B := B0) (u := mapVec e.toAlgHom u) hu'
        h0' h1' hH' h3' hHq' hq3'
        hH'_00 hH'_10 hH'_01 hH'_11 hH'_02
        hq3'_00 hq3'_10 hq3'_11_zero hq3'_01ne
        hdetH' hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_equiv_const_x0_mixedAffineTailHomLine_diagShear_origDetZero_cases
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {q2 q3 : Poly}
    (h0 : mapVec e.toAlgHom u 0 = (1 : Poly))
    (h1 : mapVec e.toAlgHom u 1 = x0)
    (h2 : mapVec e.toAlgHom u 2 = q2)
    (h3 : mapVec e.toAlgHom u 3 = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hqdet0 :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_diagShear_origDetZero_cases
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      (c0 := stdRel0) (c1 := stdRel1) (c2 := stdRel2) (c3 := stdRel3)
      (h0 := by simpa [stdRel0, Fin.sum_univ_four] using h0)
      (h1 := by simpa [stdRel1, Fin.sum_univ_four] using h1)
      (h2 := by simpa [stdRel2, Fin.sum_univ_four] using h2)
      (h3 := by simpa [stdRel3, Fin.sum_univ_four] using h3)
      hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
      hline_02 hqdet0 hq3_01 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_socp_of_eq_mix_mapVec_const_x0_mixedAffineTailHomLine_diagShear_origDetZero_cases
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuarticSymm : ∀ {p : Poly}, IsQuartic p → IsQuartic (e.symm p))
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hMtM : M.transpose * M = 1)
    (hMMt : M * M.transpose = 1)
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hqdet0 :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (huRep : mix M.transpose (mapVec e.symm.toAlgHom u) = ![(1 : Poly), x0, q2, q3])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have huRepAdmissible : IsAdmissiblePoint (![(1 : Poly), x0, q2, q3] : RankFourVec) :=
    admissiblePoint_const_x0_pair hq2 hq3
  have hRep :
      ∀ {B0 : DotForm} [Fact B0.toQuadraticMap.PosDef] {p0 : Poly},
        IsSOSQuartic p0 → IsSOCP B0 p0 (![(1 : Poly), x0, q2, q3] : RankFourVec) →
          residual p0 (![(1 : Poly), x0, q2, q3] : RankFourVec) = 0 := by
    intro B0 _ p0 hp0 hsocp0
    exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_diagShear_origDetZero_cases
      (B := B0) (u := ![(1 : Poly), x0, q2, q3]) huRepAdmissible
      (c0 := stdRel0) (c1 := stdRel1) (c2 := stdRel2) (c3 := stdRel3)
      (h0 := by simp [stdRel0, Fin.sum_univ_four])
      (h1 := by simp [stdRel1, Fin.sum_univ_four, x0])
      (h2 := by simp [stdRel2, Fin.sum_univ_four])
      (h3 := by simp [stdRel3, Fin.sum_univ_four])
      hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
      hline_02 hqdet0 hq3_01 hp0 hsocp0
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec
    (![(1 : Poly), x0, q2, q3])
    hRep e heQuad heQuadSymm heQuarticSymm M hMtM hMMt hB hp huRep hsocp

theorem residual_eq_zero_of_socp_of_eq_mix_affineEquiv_const_x0_mixedAffineTailHomLine_diagShear_origDetZero_cases
    (A A' : Matrix (Fin 2) (Fin 2) ℝ) (b b' : Fin 2 → ℝ)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (hb : ∀ i, b' i + Matrix.mulVec A' b i = 0)
    (hb' : ∀ i, b i + Matrix.mulVec A b' i = 0)
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hMtM : M.transpose * M = 1)
    (hMMt : M * M.transpose = 1)
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hqdet0 :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (huRep :
      mix M.transpose
        (mapVec (affineEquiv A A' b b' hAA' hA'A hb hb').symm.toAlgHom u) =
          ![(1 : Poly), x0, q2, q3])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec_const_x0_mixedAffineTailHomLine_diagShear_origDetZero_cases
    (e := affineEquiv A A' b b' hAA' hA'A hb hb')
    (heQuad := fun {_} hpq => isQuadratic_affineEquiv A A' b b' hAA' hA'A hb hb' hpq)
    (heQuadSymm := fun {_} hpq => isQuadratic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (heQuarticSymm := fun {_} hpq => isQuartic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (M := M) hMtM hMMt hB hp
    hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
    hline_02 hqdet0 hq3_01 huRep hsocp

theorem residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_x1sqTail
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_20 : MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hq3_11 : MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (hq3_20 : MvPolynomial.coeff m20 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let cH : Fin 4 → ℝ :=
    fun i => MvPolynomial.coeff m01 q3 * c2 i - MvPolynomial.coeff m01 q2 * c3 i
  have hH :
      ∑ i : Fin 4, cH i • u i = mixedAffineTailHomLine q2 q3 := by
    simpa [cH] using relation_mixedAffineTailHomLine (u := u) h2 h3
  have hHq : IsQuadratic (mixedAffineTailHomLine q2 q3) :=
    isQuadratic_mixedAffineTailHomLine hq2 hq3
  have hH_00 : MvPolynomial.coeff m00 (mixedAffineTailHomLine q2 q3) = 0 := by
    rw [coeff_m00_mixedAffineTailHomLine, hq2_00, hq3_00]
    ring
  have hH_10 : MvPolynomial.coeff m10 (mixedAffineTailHomLine q2 q3) = 0 := by
    rw [coeff_m10_mixedAffineTailHomLine, hq2_10, hq3_10]
    ring
  have hH_01 : MvPolynomial.coeff m01 (mixedAffineTailHomLine q2 q3) = 0 :=
    coeff_m01_mixedAffineTailHomLine
  exact residual_eq_zero_of_relations_const_x0_x1sqTail
    (B := B) (u := u) hu h0 h1 hH h3 hHq hq3
    hH_00 hH_10 hH_01 hline_20 hline_11 hline_02
    hq3_00 hq3_10 hq3_11 hq3_01 hq3_20 hp hsocp

theorem residual_eq_zero_of_equiv_relations_const_x0_mixedAffineTailHomLine_x1sqTail
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_20 : MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hq3_11 : MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (hq3_20 : MvPolynomial.coeff m20 q3 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_x1sqTail
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0 h1 h2 h3 hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
      hline_20 hline_11 hline_02 hq3_11 hq3_01 hq3_20 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_x1sqTail_det
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_20 : MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hdet0 :
      MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (hq3_20 : MvPolynomial.coeff m20 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have hq3_11 : MvPolynomial.coeff m11 q3 = 0 := by
    have hneg :
        -(MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m11 q3) = 0 := by
      simpa [hline_11] using hdet0
    have hmul :
        MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m11 q3 = 0 := by
      nlinarith [hneg]
    exact (mul_eq_zero.mp hmul).resolve_left hline_02
  exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_x1sqTail
    (B := B) (u := u) hu h0 h1 h2 h3 hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
    hline_20 hline_11 hline_02 hq3_11 hq3_01 hq3_20 hp hsocp

theorem residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_x1sqTail_origDetZero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_20 : MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hqdet0 :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (hq3_20 : MvPolynomial.coeff m20 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have hdet0 :
      MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m11 q3 = 0 := by
    rw [det_m11_m02_mixedAffineTailHomLine]
    simp [hqdet0]
  exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_x1sqTail_det
    (B := B) (u := u) hu h0 h1 h2 h3 hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
    hline_20 hline_11 hline_02 hdet0 hq3_01 hq3_20 hp hsocp

theorem residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_x1sqTail_origDetZero_cases
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_20 : MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hqdet0 :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  by_cases hq3_20 : MvPolynomial.coeff m20 q3 = 0
  · have hq3_11 : MvPolynomial.coeff m11 q3 = 0 := by
      have hdet0 :
          MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m02 q3 -
            MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m11 q3 = 0 := by
        rw [det_m11_m02_mixedAffineTailHomLine]
        simp [hqdet0]
      have hneg :
          -(MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m11 q3) = 0 := by
        simpa [hline_11] using hdet0
      have hmul :
          MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m11 q3 = 0 := by
        nlinarith [hneg]
      exact (mul_eq_zero.mp hmul).resolve_left hline_02
    let cH : Fin 4 → ℝ :=
      fun i => MvPolynomial.coeff m01 q3 * c2 i - MvPolynomial.coeff m01 q2 * c3 i
    have hH :
        ∑ i : Fin 4, cH i • u i = mixedAffineTailHomLine q2 q3 := by
      simpa [cH] using relation_mixedAffineTailHomLine (u := u) h2 h3
    have hHq : IsQuadratic (mixedAffineTailHomLine q2 q3) :=
      isQuadratic_mixedAffineTailHomLine hq2 hq3
    have hH_00 : MvPolynomial.coeff m00 (mixedAffineTailHomLine q2 q3) = 0 := by
      rw [coeff_m00_mixedAffineTailHomLine, hq2_00, hq3_00]
      ring
    have hH_10 : MvPolynomial.coeff m10 (mixedAffineTailHomLine q2 q3) = 0 := by
      rw [coeff_m10_mixedAffineTailHomLine, hq2_10, hq3_10]
      ring
    have hH_01 : MvPolynomial.coeff m01 (mixedAffineTailHomLine q2 q3) = 0 :=
      coeff_m01_mixedAffineTailHomLine
    let t : ℝ :=
      MvPolynomial.coeff m02 q3 / MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3)
    let c3' : Fin 4 → ℝ := fun i => c3 i + (-t) * cH i
    let q3' : Poly := q3 + (-t) • mixedAffineTailHomLine q2 q3
    have h3' : ∑ i : Fin 4, c3' i • u i = q3' := by
      dsimp [c3', q3']
      simpa using relation_linearCombination h3 hH 1 (-t)
    have hq3' : IsQuadratic q3' := by
      dsimp [q3']
      simpa using isQuadratic_linearCombination_local hq3 hHq 1 (-t)
    have hq3'_00 : MvPolynomial.coeff m00 q3' = 0 := by
      dsimp [q3']
      simp [hq3_00, hH_00]
    have hq3'_10 : MvPolynomial.coeff m10 q3' = 0 := by
      dsimp [q3']
      simp [hq3_10, hH_10]
    have hq3'_20 : MvPolynomial.coeff m20 q3' = 0 := by
      dsimp [q3']
      simp [hq3_20, hline_20]
    have hq3'_11 : MvPolynomial.coeff m11 q3' = 0 := by
      dsimp [q3']
      simp [hq3_11, hline_11]
    have hq3'_02 : MvPolynomial.coeff m02 q3' = 0 := by
      dsimp [q3', t]
      have hscalar :
          MvPolynomial.coeff m02 q3 -
            (MvPolynomial.coeff m02 q3 /
              MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3)) *
              MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) = 0 := by
        field_simp [hline_02]
        ring
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hscalar
    have hq3'_01 : MvPolynomial.coeff m01 q3' ≠ 0 := by
      dsimp [q3']
      simpa [hH_01, add_comm, add_left_comm, add_assoc] using hq3_01
    exact residual_eq_zero_of_relations_const_x0_affineTail
      (B := B) (u := u) hu h0 h1 h3' hq3'
      hq3'_20 hq3'_11 hq3'_02 hq3'_01 hp hsocp
  · exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_x1sqTail_origDetZero
      (B := B) (u := u) hu h0 h1 h2 h3 hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
      hline_20 hline_11 hline_02 hqdet0 hq3_01 hq3_20 hp hsocp

theorem residual_eq_zero_of_equiv_relations_const_x0_mixedAffineTailHomLine_x1sqTail_det
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_20 : MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hdet0 :
      MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (hq3_20 : MvPolynomial.coeff m20 q3 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_x1sqTail_det
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0 h1 h2 h3 hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
      hline_20 hline_11 hline_02 hdet0 hq3_01 hq3_20 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_equiv_relations_const_x0_mixedAffineTailHomLine_x1sqTail_origDetZero
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_20 : MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hqdet0 :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (hq3_20 : MvPolynomial.coeff m20 q3 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_x1sqTail_origDetZero
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0 h1 h2 h3 hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
      hline_20 hline_11 hline_02 hqdet0 hq3_01 hq3_20 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_equiv_relations_const_x0_mixedAffineTailHomLine_x1sqTail_origDetZero_cases
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_20 : MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hqdet0 :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_x1sqTail_origDetZero_cases
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0 h1 h2 h3 hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
      hline_20 hline_11 hline_02 hqdet0 hq3_01 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_equiv_const_x0_mixedAffineTailHomLine_x1sqTail_origDetZero_cases
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {q2 q3 : Poly}
    (h0 : mapVec e.toAlgHom u 0 = (1 : Poly))
    (h1 : mapVec e.toAlgHom u 1 = x0)
    (h2 : mapVec e.toAlgHom u 2 = q2)
    (h3 : mapVec e.toAlgHom u 3 = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_20 : MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hqdet0 :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_x1sqTail_origDetZero_cases
      (c0 := stdRel0) (c1 := stdRel1) (c2 := stdRel2) (c3 := stdRel3)
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      (h0 := by simpa [stdRel0, Fin.sum_univ_four] using h0)
      (h1 := by simpa [stdRel1, Fin.sum_univ_four] using h1)
      (h2 := by simpa [stdRel2, Fin.sum_univ_four] using h2)
      (h3 := by simpa [stdRel3, Fin.sum_univ_four] using h3)
      hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
      hline_20 hline_11 hline_02 hqdet0 hq3_01 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_socp_of_eq_mix_mapVec_const_x0_mixedAffineTailHomLine_x1sqTail_origDetZero_cases
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuarticSymm : ∀ {p : Poly}, IsQuartic p → IsQuartic (e.symm p))
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hMtM : M.transpose * M = 1)
    (hMMt : M * M.transpose = 1)
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_20 : MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hqdet0 :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (huRep : mix M.transpose (mapVec e.symm.toAlgHom u) = ![(1 : Poly), x0, q2, q3])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have huRepAdmissible : IsAdmissiblePoint (![(1 : Poly), x0, q2, q3] : RankFourVec) :=
    admissiblePoint_const_x0_pair hq2 hq3
  have hRep :
      ∀ {B0 : DotForm} [Fact B0.toQuadraticMap.PosDef] {p0 : Poly},
        IsSOSQuartic p0 → IsSOCP B0 p0 (![(1 : Poly), x0, q2, q3] : RankFourVec) →
          residual p0 (![(1 : Poly), x0, q2, q3] : RankFourVec) = 0 := by
    intro B0 _ p0 hp0 hsocp0
    exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_x1sqTail_origDetZero_cases
      (c0 := stdRel0) (c1 := stdRel1) (c2 := stdRel2) (c3 := stdRel3)
      (B := B0) (u := ![(1 : Poly), x0, q2, q3]) huRepAdmissible
      (h0 := by simp [stdRel0, Fin.sum_univ_four])
      (h1 := by simp [stdRel1, Fin.sum_univ_four, x0])
      (h2 := by simp [stdRel2, Fin.sum_univ_four])
      (h3 := by simp [stdRel3, Fin.sum_univ_four])
      hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
      hline_20 hline_11 hline_02 hqdet0 hq3_01 hp0 hsocp0
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec
    (![(1 : Poly), x0, q2, q3])
    hRep e heQuad heQuadSymm heQuarticSymm M hMtM hMMt hB hp huRep hsocp

theorem residual_eq_zero_of_socp_of_eq_mix_affineEquiv_const_x0_mixedAffineTailHomLine_x1sqTail_origDetZero_cases
    (A A' : Matrix (Fin 2) (Fin 2) ℝ) (b b' : Fin 2 → ℝ)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (hb : ∀ i, b' i + Matrix.mulVec A' b i = 0)
    (hb' : ∀ i, b i + Matrix.mulVec A b' i = 0)
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hMtM : M.transpose * M = 1)
    (hMMt : M * M.transpose = 1)
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_20 : MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hqdet0 :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (huRep :
      mix M.transpose
        (mapVec (affineEquiv A A' b b' hAA' hA'A hb hb').symm.toAlgHom u) =
          ![(1 : Poly), x0, q2, q3])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec_const_x0_mixedAffineTailHomLine_x1sqTail_origDetZero_cases
    (e := affineEquiv A A' b b' hAA' hA'A hb hb')
    (heQuad := fun {_} hpq => isQuadratic_affineEquiv A A' b b' hAA' hA'A hb hb' hpq)
    (heQuadSymm := fun {_} hpq => isQuadratic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (heQuarticSymm := fun {_} hpq => isQuartic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (M := M) hMtM hMMt hB hp
    hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
    hline_20 hline_11 hline_02 hqdet0 hq3_01 huRep hsocp

theorem residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_diagX1sqTail
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hq3_11 : MvPolynomial.coeff m11 q3 = 0)
    (hq3_02 : MvPolynomial.coeff m02 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (hq3_20 : MvPolynomial.coeff m20 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let cH : Fin 4 → ℝ :=
    fun i => MvPolynomial.coeff m01 q3 * c2 i - MvPolynomial.coeff m01 q2 * c3 i
  have hH :
      ∑ i : Fin 4, cH i • u i = mixedAffineTailHomLine q2 q3 := by
    simpa [cH] using relation_mixedAffineTailHomLine (u := u) h2 h3
  have hHq : IsQuadratic (mixedAffineTailHomLine q2 q3) :=
    isQuadratic_mixedAffineTailHomLine hq2 hq3
  have hH_00 : MvPolynomial.coeff m00 (mixedAffineTailHomLine q2 q3) = 0 := by
    rw [coeff_m00_mixedAffineTailHomLine, hq2_00, hq3_00]
    ring
  have hH_10 : MvPolynomial.coeff m10 (mixedAffineTailHomLine q2 q3) = 0 := by
    rw [coeff_m10_mixedAffineTailHomLine, hq2_10, hq3_10]
    ring
  have hH_01 : MvPolynomial.coeff m01 (mixedAffineTailHomLine q2 q3) = 0 :=
    coeff_m01_mixedAffineTailHomLine
  exact residual_eq_zero_of_relations_const_x0_diagX1sqTail
    (B := B) (u := u) hu h0 h1 hH h3 hHq hq3
    hH_00 hH_10 hH_01 hline_11 hline_02
    hq3_00 hq3_10 hq3_11 hq3_02 hq3_01 hq3_20 hp hsocp

theorem residual_eq_zero_of_equiv_relations_const_x0_mixedAffineTailHomLine_diagX1sqTail
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hq3_11 : MvPolynomial.coeff m11 q3 = 0)
    (hq3_02 : MvPolynomial.coeff m02 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (hq3_20 : MvPolynomial.coeff m20 q3 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_diagX1sqTail
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0 h1 h2 h3 hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
      hline_11 hline_02 hq3_11 hq3_02 hq3_01 hq3_20 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_diagX1sqTail_det
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hdet0 :
      MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (hdet2 :
      MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m20 q3 -
        MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m02 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have hq3_11 : MvPolynomial.coeff m11 q3 = 0 := by
    have hneg :
        -(MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m11 q3) = 0 := by
      simpa [hline_11] using hdet0
    have hmul :
        MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m11 q3 = 0 := by
      nlinarith [hneg]
    exact (mul_eq_zero.mp hmul).resolve_left hline_02
  let cH : Fin 4 → ℝ :=
    fun i => MvPolynomial.coeff m01 q3 * c2 i - MvPolynomial.coeff m01 q2 * c3 i
  have hH :
      ∑ i : Fin 4, cH i • u i = mixedAffineTailHomLine q2 q3 := by
    simpa [cH] using relation_mixedAffineTailHomLine (u := u) h2 h3
  have hHq : IsQuadratic (mixedAffineTailHomLine q2 q3) :=
    isQuadratic_mixedAffineTailHomLine hq2 hq3
  have hH_00 : MvPolynomial.coeff m00 (mixedAffineTailHomLine q2 q3) = 0 := by
    rw [coeff_m00_mixedAffineTailHomLine, hq2_00, hq3_00]
    ring
  have hH_10 : MvPolynomial.coeff m10 (mixedAffineTailHomLine q2 q3) = 0 := by
    rw [coeff_m10_mixedAffineTailHomLine, hq2_10, hq3_10]
    ring
  have hH_01 : MvPolynomial.coeff m01 (mixedAffineTailHomLine q2 q3) = 0 :=
    coeff_m01_mixedAffineTailHomLine
  exact residual_eq_zero_of_relations_const_x0_diagX1sqTail_det
    (B := B) (u := u) hu h0 h1 hH h3 hHq hq3
    hH_00 hH_10 hH_01 hline_11 hline_02
    hq3_00 hq3_10 hq3_11 hq3_01 hdet2 hp hsocp

theorem residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_diagX1sqTail_origDetZero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hqdet0 :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (hqdet2 :
      MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3 -
        MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m02 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have hdet0 :
      MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m11 q3 = 0 := by
    rw [det_m11_m02_mixedAffineTailHomLine]
    simp [hqdet0]
  have hdet2 :
      MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m20 q3 -
        MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m02 q3 ≠ 0 := by
    rw [det_m02_m20_mixedAffineTailHomLine]
    exact mul_ne_zero hq3_01 hqdet2
  exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_diagX1sqTail_det
    (B := B) (u := u) hu h0 h1 h2 h3 hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
    hline_11 hline_02 hdet0 hq3_01 hdet2 hp hsocp

theorem residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_diagX1sqTail_origDetZero_cases
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hqdet0 :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  by_cases hqdet2 :
      MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3 -
        MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m02 q3 = 0
  · have hq3_11 : MvPolynomial.coeff m11 q3 = 0 := by
      have hdet0 :
          MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m02 q3 -
            MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m11 q3 = 0 := by
        rw [det_m11_m02_mixedAffineTailHomLine]
        simp [hqdet0]
      have hneg :
          -(MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m11 q3) = 0 := by
        simpa [hline_11] using hdet0
      have hmul :
          MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m11 q3 = 0 := by
        nlinarith [hneg]
      exact (mul_eq_zero.mp hmul).resolve_left hline_02
    let cH : Fin 4 → ℝ :=
      fun i => MvPolynomial.coeff m01 q3 * c2 i - MvPolynomial.coeff m01 q2 * c3 i
    have hH :
        ∑ i : Fin 4, cH i • u i = mixedAffineTailHomLine q2 q3 := by
      simpa [cH] using relation_mixedAffineTailHomLine (u := u) h2 h3
    have hHq : IsQuadratic (mixedAffineTailHomLine q2 q3) :=
      isQuadratic_mixedAffineTailHomLine hq2 hq3
    have hH_00 : MvPolynomial.coeff m00 (mixedAffineTailHomLine q2 q3) = 0 := by
      rw [coeff_m00_mixedAffineTailHomLine, hq2_00, hq3_00]
      ring
    have hH_10 : MvPolynomial.coeff m10 (mixedAffineTailHomLine q2 q3) = 0 := by
      rw [coeff_m10_mixedAffineTailHomLine, hq2_10, hq3_10]
      ring
    have hH_01 : MvPolynomial.coeff m01 (mixedAffineTailHomLine q2 q3) = 0 :=
      coeff_m01_mixedAffineTailHomLine
    have hdet2 :
        MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m20 q3 -
          MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m02 q3 = 0 := by
      rw [det_m02_m20_mixedAffineTailHomLine]
      simp [hqdet2]
    let t : ℝ :=
      MvPolynomial.coeff m02 q3 / MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3)
    let c3' : Fin 4 → ℝ := fun i => c3 i + (-t) * cH i
    let q3' : Poly := q3 + (-t) • mixedAffineTailHomLine q2 q3
    have h3' : ∑ i : Fin 4, c3' i • u i = q3' := by
      dsimp [c3', q3']
      simpa using relation_linearCombination h3 hH 1 (-t)
    have hq3' : IsQuadratic q3' := by
      dsimp [q3']
      simpa using isQuadratic_linearCombination_local hq3 hHq 1 (-t)
    have hq3'_00 : MvPolynomial.coeff m00 q3' = 0 := by
      dsimp [q3']
      simp [hq3_00, hH_00]
    have hq3'_10 : MvPolynomial.coeff m10 q3' = 0 := by
      dsimp [q3']
      simp [hq3_10, hH_10]
    have hq3'_11 : MvPolynomial.coeff m11 q3' = 0 := by
      dsimp [q3']
      simp [hq3_11, hline_11]
    have hq3'_02 : MvPolynomial.coeff m02 q3' = 0 := by
      dsimp [q3', t]
      have hscalar :
          MvPolynomial.coeff m02 q3 -
            (MvPolynomial.coeff m02 q3 /
              MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3)) *
              MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) = 0 := by
        field_simp [hline_02]
        ring
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hscalar
    have hq3'_20 : MvPolynomial.coeff m20 q3' = 0 := by
      have hscale :
          MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m20 q3' =
            MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m20 q3 -
              MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m02 q3 := by
        dsimp [q3', t]
        simp [sub_eq_add_neg]
        field_simp [hline_02]
      have hmul :
          MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m20 q3' = 0 := by
        rw [hscale, hdet2]
      exact (mul_eq_zero.mp hmul).resolve_left hline_02
    have hq3'_01 : MvPolynomial.coeff m01 q3' ≠ 0 := by
      dsimp [q3']
      simpa [hH_01, add_comm, add_left_comm, add_assoc] using hq3_01
    exact residual_eq_zero_of_relations_const_x0_affineTail
      (B := B) (u := u) hu h0 h1 h3' hq3'
      hq3'_20 hq3'_11 hq3'_02 hq3'_01 hp hsocp
  · exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_diagX1sqTail_origDetZero
      (B := B) (u := u) hu h0 h1 h2 h3 hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
      hline_11 hline_02 hqdet0 hq3_01 hqdet2 hp hsocp

theorem residual_eq_zero_of_equiv_relations_const_x0_mixedAffineTailHomLine_diagX1sqTail_det
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hdet0 :
      MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (hdet2 :
      MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m20 q3 -
        MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) * MvPolynomial.coeff m02 q3 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_diagX1sqTail_det
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0 h1 h2 h3 hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
      hline_11 hline_02 hdet0 hq3_01 hdet2 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_equiv_relations_const_x0_mixedAffineTailHomLine_diagX1sqTail_origDetZero
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hqdet0 :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (hqdet2 :
      MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3 -
        MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m02 q3 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_diagX1sqTail_origDetZero
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0 h1 h2 h3 hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
      hline_11 hline_02 hqdet0 hq3_01 hqdet2 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_equiv_relations_const_x0_mixedAffineTailHomLine_diagX1sqTail_origDetZero_cases
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hqdet0 :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_diagX1sqTail_origDetZero_cases
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0 h1 h2 h3 hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
      hline_11 hline_02 hqdet0 hq3_01 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_equiv_const_x0_mixedAffineTailHomLine_diagX1sqTail_origDetZero_cases
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {q2 q3 : Poly}
    (h0 : mapVec e.toAlgHom u 0 = (1 : Poly))
    (h1 : mapVec e.toAlgHom u 1 = x0)
    (h2 : mapVec e.toAlgHom u 2 = q2)
    (h3 : mapVec e.toAlgHom u 3 = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hqdet0 :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_diagX1sqTail_origDetZero_cases
      (c0 := stdRel0) (c1 := stdRel1) (c2 := stdRel2) (c3 := stdRel3)
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      (h0 := by simpa [stdRel0, Fin.sum_univ_four] using h0)
      (h1 := by simpa [stdRel1, Fin.sum_univ_four] using h1)
      (h2 := by simpa [stdRel2, Fin.sum_univ_four] using h2)
      (h3 := by simpa [stdRel3, Fin.sum_univ_four] using h3)
      hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
      hline_11 hline_02 hqdet0 hq3_01 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_socp_of_eq_mix_mapVec_const_x0_mixedAffineTailHomLine_diagX1sqTail_origDetZero_cases
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuarticSymm : ∀ {p : Poly}, IsQuartic p → IsQuartic (e.symm p))
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hMtM : M.transpose * M = 1)
    (hMMt : M * M.transpose = 1)
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hqdet0 :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (huRep : mix M.transpose (mapVec e.symm.toAlgHom u) = ![(1 : Poly), x0, q2, q3])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have huRepAdmissible : IsAdmissiblePoint (![(1 : Poly), x0, q2, q3] : RankFourVec) :=
    admissiblePoint_const_x0_pair hq2 hq3
  have hRep :
      ∀ {B0 : DotForm} [Fact B0.toQuadraticMap.PosDef] {p0 : Poly},
        IsSOSQuartic p0 → IsSOCP B0 p0 (![(1 : Poly), x0, q2, q3] : RankFourVec) →
          residual p0 (![(1 : Poly), x0, q2, q3] : RankFourVec) = 0 := by
    intro B0 _ p0 hp0 hsocp0
    exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_diagX1sqTail_origDetZero_cases
      (c0 := stdRel0) (c1 := stdRel1) (c2 := stdRel2) (c3 := stdRel3)
      (B := B0) (u := ![(1 : Poly), x0, q2, q3]) huRepAdmissible
      (h0 := by simp [stdRel0, Fin.sum_univ_four])
      (h1 := by simp [stdRel1, Fin.sum_univ_four, x0])
      (h2 := by simp [stdRel2, Fin.sum_univ_four])
      (h3 := by simp [stdRel3, Fin.sum_univ_four])
      hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
      hline_11 hline_02 hqdet0 hq3_01 hp0 hsocp0
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec
    (![(1 : Poly), x0, q2, q3])
    hRep e heQuad heQuadSymm heQuarticSymm M hMtM hMMt hB hp huRep hsocp

theorem residual_eq_zero_of_socp_of_eq_mix_affineEquiv_const_x0_mixedAffineTailHomLine_diagX1sqTail_origDetZero_cases
    (A A' : Matrix (Fin 2) (Fin 2) ℝ) (b b' : Fin 2 → ℝ)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (hb : ∀ i, b' i + Matrix.mulVec A' b i = 0)
    (hb' : ∀ i, b i + Matrix.mulVec A b' i = 0)
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hMtM : M.transpose * M = 1)
    (hMMt : M * M.transpose = 1)
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hqdet0 :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (huRep :
      mix M.transpose
        (mapVec (affineEquiv A A' b b' hAA' hA'A hb hb').symm.toAlgHom u) =
          ![(1 : Poly), x0, q2, q3])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec_const_x0_mixedAffineTailHomLine_diagX1sqTail_origDetZero_cases
    (e := affineEquiv A A' b b' hAA' hA'A hb hb')
    (heQuad := fun {_} hpq => isQuadratic_affineEquiv A A' b b' hAA' hA'A hb hb' hpq)
    (heQuadSymm := fun {_} hpq => isQuadratic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (heQuarticSymm := fun {_} hpq => isQuartic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (M := M) hMtM hMMt hB hp
    hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
    hline_11 hline_02 hqdet0 hq3_01 huRep hsocp

/-- Exact surjective plane theorem for the mixed-affine model with quadratic
plane `span(x₀², x₁²)`. -/
theorem quartic_in_image_of_relations_const_x0sq_x1sq
    {u : RankFourVec}
    {c0 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 ^ 2)
    (h3 : ∑ i : Fin 4, c3 i • u i = x1 ^ 2)
    {p : Poly} (hp : IsQuartic p) :
    InAdmissibleImage u p := by
  classical
  rw [← MvPolynomial.support_sum_monomial_coeff p]
  let P : Finset (Fin 2 →₀ ℕ) → Prop := fun S =>
    (∀ s ∈ S, s ∈ p.support) →
      InAdmissibleImage u
        (∑ s ∈ S, MvPolynomial.monomial s (MvPolynomial.coeff s p))
  have hP : P p.support := by
    refine Finset.induction_on p.support ?_ ?_
    · intro hsub
      simpa using inAdmissibleImage_zero u
    · intro s ss hsnot ih hsub
      rw [Finset.sum_insert hsnot]
      refine inAdmissibleImage_add u ?_ (ih ?_)
      · let e0 := s 0
        let e1 := s 1
        have hsum : s.sum (fun _ e => e) = s 0 + s 1 := by
          rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
        have hsdeg : e0 + e1 ≤ 4 := by
          have hsdeg0 : s.sum (fun _ e => e) ≤ 4 :=
            (MvPolynomial.le_totalDegree (hsub s (by simp))).trans hp
          simpa [e0, e1, hsum] using hsdeg0
        by_cases hsmall : e0 + e1 ≤ 2
        · simpa [monomial_fin2_eq, e0, e1, one_mul] using
            (inAdmissibleImage_of_relation_mul
              (u := u) (c := c0) (r := (1 : Poly))
              (q := (MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ e0) * x1 ^ e1)
              h0 (isQuadratic_C_mul_pow_pow (MvPolynomial.coeff s p) e0 e1 hsmall))
        · by_cases hx2 : 2 ≤ e0
          · have hs2 : (e0 - 2) + e1 ≤ 2 := by omega
            have himg :=
              inAdmissibleImage_of_relation_mul
                (u := u) (c := c2) (r := x0 ^ 2)
                (q := (MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ (e0 - 2)) * x1 ^ e1)
                h2 (isQuadratic_C_mul_pow_pow (MvPolynomial.coeff s p) (e0 - 2) e1 hs2)
            rw [monomial_fin2_eq]
            simp [e0, e1] at himg ⊢
            have hmul : x0 ^ 2 * ((MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ (e0 - 2)) * x1 ^ e1)
                = (MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ e0) * x1 ^ e1 := by
              calc
                x0 ^ 2 * ((MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ (e0 - 2)) * x1 ^ e1)
                    = MvPolynomial.C (MvPolynomial.coeff s p) * (x0 ^ 2 * x0 ^ (e0 - 2)) * x1 ^ e1 := by
                        ring_nf
                _ = (MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ e0) * x1 ^ e1 := by
                      rw [← pow_add, Nat.add_sub_of_le hx2]
            simpa [e0, e1, hmul] using himg
          · have hy2 : 2 ≤ e1 := by omega
            have hs2 : e0 + (e1 - 2) ≤ 2 := by omega
            have himg :=
              inAdmissibleImage_of_relation_mul
                (u := u) (c := c3) (r := x1 ^ 2)
                (q := (MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ e0) * x1 ^ (e1 - 2))
                h3 (isQuadratic_C_mul_pow_pow (MvPolynomial.coeff s p) e0 (e1 - 2) hs2)
            rw [monomial_fin2_eq]
            simp [e0, e1] at himg ⊢
            have hmul : x1 ^ 2 * ((MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ e0) * x1 ^ (e1 - 2))
                = (MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ e0) * x1 ^ e1 := by
              calc
                x1 ^ 2 * ((MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ e0) * x1 ^ (e1 - 2))
                    = MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ e0 * (x1 ^ 2 * x1 ^ (e1 - 2)) := by
                        ring_nf
                _ = (MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ e0) * x1 ^ e1 := by
                      rw [← pow_add, Nat.add_sub_of_le hy2]
            simpa [e0, e1, hmul] using himg
      · intro t ht
        exact hsub t (by simp [ht])
  exact hP (fun s hs => hs)

theorem residual_eq_zero_of_relations_const_x0sq_x1sq
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 ^ 2)
    (h3 : ∑ i : Fin 4, c3 i • u i = x1 ^ 2)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_in_admissible_image
    (B := B) hu hsocp (quartic_in_image_of_relations_const_x0sq_x1sq h0 h2 h3 hp.1)

/-- If the quadratic relation plane is any invertible basis of
`span(x₀², x₁²)`, we can reconstruct the exact monomial relations and use the
surjective image theorem above. -/
theorem residual_eq_zero_of_relations_const_x0sq_x1sqPlane
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    {a b c d : ℝ}
    (h2 : ∑ i : Fin 4, c2 i • u i = a • (x0 ^ 2 : Poly) + b • (x1 ^ 2 : Poly))
    (h3 : ∑ i : Fin 4, c3 i • u i = c • (x0 ^ 2 : Poly) + d • (x1 ^ 2 : Poly))
    (hdet : a * d - b * c ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let det : ℝ := a * d - b * c
  have hdet0 : det ≠ 0 := by
    simpa [det] using hdet
  let c2' : Fin 4 → ℝ := fun i => (d / det) * c2 i + (-b / det) * c3 i
  let c3' : Fin 4 → ℝ := fun i => (-c / det) * c2 i + (a / det) * c3 i
  have hcoeff20 : (d / det) * a + (-b / det) * c = 1 := by
    field_simp [det, hdet0]
    ring
  have hcoeff21 : (d / det) * b + (-b / det) * d = 0 := by
    field_simp [det, hdet0]
    ring
  have hcoeff30 : (-c / det) * a + (a / det) * c = 0 := by
    field_simp [det, hdet0]
    ring
  have hcoeff31 : (-c / det) * b + (a / det) * d = 1 := by
    field_simp [det, hdet0]
    ring
  have h2' : ∑ i : Fin 4, c2' i • u i = x0 ^ 2 := by
    calc
      ∑ i : Fin 4, c2' i • u i
          = (d / det) • (a • (x0 ^ 2 : Poly) + b • (x1 ^ 2 : Poly)) +
              (-b / det) • (c • (x0 ^ 2 : Poly) + d • (x1 ^ 2 : Poly)) := by
                simp [c2', det, relation_linearCombination, h2, h3]
      _ = ((d / det) * a + (-b / det) * c) • (x0 ^ 2 : Poly) +
            ((d / det) * b + (-b / det) * d) • (x1 ^ 2 : Poly) := by
              simp [smul_add, smul_smul, add_smul, add_assoc, add_left_comm, mul_comm]
      _ = x0 ^ 2 := by
            rw [hcoeff20, hcoeff21]
            simp
  have h3' : ∑ i : Fin 4, c3' i • u i = x1 ^ 2 := by
    calc
      ∑ i : Fin 4, c3' i • u i
          = (-c / det) • (a • (x0 ^ 2 : Poly) + b • (x1 ^ 2 : Poly)) +
              (a / det) • (c • (x0 ^ 2 : Poly) + d • (x1 ^ 2 : Poly)) := by
                simp [c3', det, relation_linearCombination, h2, h3]
      _ = ((-c / det) * a + (a / det) * c) • (x0 ^ 2 : Poly) +
            ((-c / det) * b + (a / det) * d) • (x1 ^ 2 : Poly) := by
              simp [smul_add, smul_smul, add_smul, add_assoc, add_left_comm, add_comm,
                mul_comm]
      _ = x1 ^ 2 := by
            rw [hcoeff30, hcoeff31]
            simp
  exact residual_eq_zero_of_relations_const_x0sq_x1sq
    (B := B) (u := u) hu h0 h2' h3' hp hsocp

/-- Transport the surjective `span(x₀²,x₁²)` mixed-affine plane theorem across
an algebra equivalence. -/
theorem residual_eq_zero_of_equiv_relations_const_x0sq_x1sqPlane
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly))
    {a b c d : ℝ}
    (h2 :
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i =
        a • (x0 ^ 2 : Poly) + b • (x1 ^ 2 : Poly))
    (h3 :
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i =
        c • (x0 ^ 2 : Poly) + d • (x1 ^ 2 : Poly))
    (hdet : a * d - b * c ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0sq_x1sqPlane
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0 h2 h3 hdet hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

/-- Linear change of variables sending `(x₀,x₁)` to `(x₀+x₁,x₀-x₁)`. -/
private def splitDiagMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 1; 1, -1]

/-- Inverse of `splitDiagMatrix`. -/
private def splitDiagInvMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1 / 2 : ℝ), (1 / 2 : ℝ); (1 / 2 : ℝ), (-1 / 2 : ℝ)]

private theorem splitDiag_mul_inv :
    splitDiagMatrix * splitDiagInvMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitDiagMatrix, splitDiagInvMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals norm_num

private theorem splitDiag_inv_mul :
    splitDiagInvMatrix * splitDiagMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitDiagMatrix, splitDiagInvMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals norm_num

private def splitDiagEquiv : Poly ≃ₐ[ℝ] Poly :=
  affineEquiv splitDiagMatrix splitDiagInvMatrix 0 0
    splitDiag_mul_inv splitDiag_inv_mul (by intro i; simp) (by intro i; simp)

@[simp] private theorem affineHom_splitDiag_x0 :
    affineHom splitDiagMatrix 0 x0 = x0 + x1 := by
  simp [x0, x1, affineImage, affineHom_X, splitDiagMatrix, Fin.sum_univ_two]

@[simp] private theorem affineHom_splitDiag_x1 :
    affineHom splitDiagMatrix 0 x1 = x0 - x1 := by
  simp [x0, x1, affineImage, affineHom_X, splitDiagMatrix, Fin.sum_univ_two, sub_eq_add_neg]

private theorem affineHom_splitDiag_x0x1 :
    affineHom splitDiagMatrix 0 (x0 * x1 : Poly) = x0 ^ 2 - x1 ^ 2 := by
  simp [affineHom_splitDiag_x0, affineHom_splitDiag_x1]
  ring

private theorem affineHom_splitDiag_sumsq :
    affineHom splitDiagMatrix 0 (x0 ^ 2 + x1 ^ 2 : Poly) = 2 • (x0 ^ 2 + x1 ^ 2 : Poly) := by
  simp [affineHom_splitDiag_x0, affineHom_splitDiag_x1]
  ring

private theorem affineHom_splitDiag_x0x1_sumsq
    (a b : ℝ) :
    affineHom splitDiagMatrix 0 (a • (x0 * x1 : Poly) + b • (x0 ^ 2 + x1 ^ 2 : Poly)) =
      (a + 2 * b) • (x0 ^ 2 : Poly) + (-a + 2 * b) • (x1 ^ 2 : Poly) := by
  simp [affineHom_splitDiag_x0, affineHom_splitDiag_x1, sub_eq_add_neg, MvPolynomial.smul_eq_C_mul]
  have htwo : (MvPolynomial.C (2 : ℝ) : Poly) = 2 := by
    change (MvPolynomial.C (2 : ℝ) : Poly) = MvPolynomial.C 2
    rfl
  simp [htwo]
  ring_nf

@[simp] private theorem splitDiagEquiv_apply_one :
    splitDiagEquiv (1 : Poly) = 1 := by
  simp [splitDiagEquiv]

@[simp] private theorem splitDiagEquiv_apply_x0x1_sumsq
    (a b : ℝ) :
    splitDiagEquiv (a • (x0 * x1 : Poly) + b • (x0 ^ 2 + x1 ^ 2 : Poly)) =
      (a + 2 * b) • (x0 ^ 2 : Poly) + (-a + 2 * b) • (x1 ^ 2 : Poly) := by
  exact affineHom_splitDiag_x0x1_sumsq a b

/-- Any invertible basis of `span(x₀x₁, x₀² + x₁²)` is surjective, via the
fixed linear equivalence sending this split-diagonal plane to `span(x₀²,x₁²)`. -/
theorem residual_eq_zero_of_relations_const_x0x1_sumsqPlane
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    {a b c d : ℝ}
    (h2 : ∑ i : Fin 4, c2 i • u i = a • (x0 * x1 : Poly) + b • (x0 ^ 2 + x1 ^ 2 : Poly))
    (h3 : ∑ i : Fin 4, c3 i • u i = c • (x0 * x1 : Poly) + d • (x0 ^ 2 + x1 ^ 2 : Poly))
    (hdet : a * d - b * c ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have hB : IsPositiveDefinite B := (Fact.out : B.toQuadraticMap.PosDef)
  have h0' : ∑ i : Fin 4, c0 i • mapVec splitDiagEquiv.toAlgHom u i = (1 : Poly) := by
    calc
      ∑ i : Fin 4, c0 i • mapVec splitDiagEquiv.toAlgHom u i
          = splitDiagEquiv (∑ i : Fin 4, c0 i • u i) := by
              simp [mapVec, map_sum]
      _ = 1 := by simp [h0]
  have h2' :
      ∑ i : Fin 4, c2 i • mapVec splitDiagEquiv.toAlgHom u i =
        (a + 2 * b) • (x0 ^ 2 : Poly) + (-a + 2 * b) • (x1 ^ 2 : Poly) := by
    calc
      ∑ i : Fin 4, c2 i • mapVec splitDiagEquiv.toAlgHom u i
          = splitDiagEquiv (∑ i : Fin 4, c2 i • u i) := by
              simp [mapVec, map_sum]
      _ = splitDiagEquiv (a • (x0 * x1 : Poly) + b • (x0 ^ 2 + x1 ^ 2 : Poly)) := by
            rw [h2]
      _ = (a + 2 * b) • (x0 ^ 2 : Poly) + (-a + 2 * b) • (x1 ^ 2 : Poly) := by
            simpa using splitDiagEquiv_apply_x0x1_sumsq a b
  have h3' :
      ∑ i : Fin 4, c3 i • mapVec splitDiagEquiv.toAlgHom u i =
        (c + 2 * d) • (x0 ^ 2 : Poly) + (-c + 2 * d) • (x1 ^ 2 : Poly) := by
    calc
      ∑ i : Fin 4, c3 i • mapVec splitDiagEquiv.toAlgHom u i
          = splitDiagEquiv (∑ i : Fin 4, c3 i • u i) := by
              simp [mapVec, map_sum]
      _ = splitDiagEquiv (c • (x0 * x1 : Poly) + d • (x0 ^ 2 + x1 ^ 2 : Poly)) := by
            rw [h3]
      _ = (c + 2 * d) • (x0 ^ 2 : Poly) + (-c + 2 * d) • (x1 ^ 2 : Poly) := by
            simpa using splitDiagEquiv_apply_x0x1_sumsq c d
  have hdet' : (a + 2 * b) * (-c + 2 * d) - (-a + 2 * b) * (c + 2 * d) ≠ 0 := by
    intro h
    apply hdet
    nlinarith
  exact residual_eq_zero_of_equiv_relations_const_x0sq_x1sqPlane
    (e := splitDiagEquiv)
    (heQuad := fun {_} hpq =>
      isQuadratic_affineEquiv splitDiagMatrix splitDiagInvMatrix 0 0
        splitDiag_mul_inv splitDiag_inv_mul (by intro i; simp) (by intro i; simp) hpq)
    (heQuadSymm := fun {_} hpq =>
      isQuadratic_affineEquiv_symm splitDiagMatrix splitDiagInvMatrix 0 0
        splitDiag_mul_inv splitDiag_inv_mul (by intro i; simp) (by intro i; simp) hpq)
    (heQuartic := fun {_} hpq =>
      isQuartic_affineEquiv splitDiagMatrix splitDiagInvMatrix 0 0
        splitDiag_mul_inv splitDiag_inv_mul (by intro i; simp) (by intro i; simp) hpq)
    (B := B) (p := p) (u := u)
    hB hp hu hsocp
    h0' h2' h3' hdet'

/-- Transport the split-diagonal surjective mixed-affine plane theorem across
an algebra equivalence. -/
theorem residual_eq_zero_of_equiv_relations_const_x0x1_sumsqPlane
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly))
    {a b c d : ℝ}
    (h2 :
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i =
        a • (x0 * x1 : Poly) + b • (x0 ^ 2 + x1 ^ 2 : Poly))
    (h3 :
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i =
        c • (x0 * x1 : Poly) + d • (x0 ^ 2 + x1 ^ 2 : Poly))
    (hdet : a * d - b * c ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0x1_sumsqPlane
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0 h2 h3 hdet hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

/-- Exact surjective plane theorem for the definite mixed-affine model with
quadratic plane `span(x₀x₁, x₀² - x₁²)`. -/
theorem quartic_in_image_of_relations_const_x0x1_diffsq
    {u : RankFourVec}
    {c0 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 * x1)
    (h3 : ∑ i : Fin 4, c3 i • u i = x0 ^ 2 - x1 ^ 2)
    {p : Poly} (hp : IsQuartic p) :
    InAdmissibleImage u p := by
  classical
  let hx1cub : InAdmissibleImage u (x1 ^ 3) := by
    have himg1 :=
      inAdmissibleImage_of_relation_mul (u := u) (c := c2) (r := x0 * x1) (q := x0)
        h2 (by simp [x0, IsQuadratic])
    have himg2 :=
      inAdmissibleImage_of_relation_mul (u := u) (c := c3) (r := x0 ^ 2 - x1 ^ 2) (q := -x1)
        h3 (by
          calc
            (-x1 : Poly).totalDegree = x1.totalDegree := by rw [MvPolynomial.totalDegree_neg]
            _ ≤ 2 := by simp [x1])
    have hsum := inAdmissibleImage_add u himg1 himg2
    convert hsum using 1
    ring
  let hx0cub : InAdmissibleImage u (x0 ^ 3) := by
    have himg1 :=
      inAdmissibleImage_of_relation_mul (u := u) (c := c2) (r := x0 * x1) (q := x1)
        h2 (by simp [x1, IsQuadratic])
    have himg2 :=
      inAdmissibleImage_of_relation_mul (u := u) (c := c3) (r := x0 ^ 2 - x1 ^ 2) (q := x0)
        h3 (by simp [x0, IsQuadratic])
    have hsum := inAdmissibleImage_add u himg1 himg2
    convert hsum using 1
    ring
  let hx1quart : InAdmissibleImage u (x1 ^ 4) := by
    have himg1 :=
      inAdmissibleImage_of_relation_mul (u := u) (c := c2) (r := x0 * x1) (q := x0 * x1)
        h2 (by
          calc
            (x0 * x1 : Poly).totalDegree ≤ x0.totalDegree + x1.totalDegree := by
              exact MvPolynomial.totalDegree_mul _ _
            _ = 2 := by simp [x0, x1])
    have himg2 :=
      inAdmissibleImage_of_relation_mul
        (u := u) (c := c3) (r := x0 ^ 2 - x1 ^ 2) (q := -(x1 ^ 2 : Poly))
        h3 (by
          calc
            (-(x1 ^ 2 : Poly)).totalDegree = (x1 ^ 2 : Poly).totalDegree := by
              rw [MvPolynomial.totalDegree_neg]
            _ ≤ 2 := by simp [x1, MvPolynomial.totalDegree_X_pow])
    have hsum := inAdmissibleImage_add u himg1 himg2
    convert hsum using 1
    ring
  let hx0quart : InAdmissibleImage u (x0 ^ 4) := by
    have himg1 :=
      inAdmissibleImage_of_relation_mul (u := u) (c := c2) (r := x0 * x1) (q := x0 * x1)
        h2 (by
          calc
            (x0 * x1 : Poly).totalDegree ≤ x0.totalDegree + x1.totalDegree := by
              exact MvPolynomial.totalDegree_mul _ _
            _ = 2 := by simp [x0, x1])
    have himg2 :=
      inAdmissibleImage_of_relation_mul
        (u := u) (c := c3) (r := x0 ^ 2 - x1 ^ 2) (q := x0 ^ 2)
        h3 (by simp [IsQuadratic, x0, MvPolynomial.totalDegree_X_pow])
    have hsum := inAdmissibleImage_add u himg1 himg2
    convert hsum using 1
    ring
  rw [← MvPolynomial.support_sum_monomial_coeff p]
  let P : Finset (Fin 2 →₀ ℕ) → Prop := fun S =>
    (∀ s ∈ S, s ∈ p.support) →
      InAdmissibleImage u
        (∑ s ∈ S, MvPolynomial.monomial s (MvPolynomial.coeff s p))
  have hP : P p.support := by
    refine Finset.induction_on p.support ?_ ?_
    · intro hsub
      simpa using inAdmissibleImage_zero u
    · intro s ss hsnot ih hsub
      rw [Finset.sum_insert hsnot]
      refine inAdmissibleImage_add u ?_ (ih ?_)
      · let e0 := s 0
        let e1 := s 1
        have hsum : s.sum (fun _ e => e) = s 0 + s 1 := by
          rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
        have hsdeg : e0 + e1 ≤ 4 := by
          have hsdeg0 : s.sum (fun _ e => e) ≤ 4 :=
            (MvPolynomial.le_totalDegree (hsub s (by simp))).trans hp
          simpa [e0, e1, hsum] using hsdeg0
        by_cases hsmall : e0 + e1 ≤ 2
        · simpa [monomial_fin2_eq, e0, e1, one_mul] using
            (inAdmissibleImage_of_relation_mul
              (u := u) (c := c0) (r := (1 : Poly))
              (q := (MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ e0) * x1 ^ e1)
              h0 (isQuadratic_C_mul_pow_pow (MvPolynomial.coeff s p) e0 e1 hsmall))
        · by_cases hxy : 1 ≤ e0 ∧ 1 ≤ e1
          · rcases hxy with ⟨hx1, hy1⟩
            have hs2 : (e0 - 1) + (e1 - 1) ≤ 2 := by omega
            have himg :=
              inAdmissibleImage_of_relation_mul
                (u := u) (c := c2) (r := x0 * x1)
                (q := (MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1))
                h2 (isQuadratic_C_mul_pow_pow (MvPolynomial.coeff s p) (e0 - 1) (e1 - 1) hs2)
            rw [monomial_fin2_eq]
            simp [e0, e1] at himg ⊢
            have hxpow : x0 * x0 ^ (e0 - 1) = x0 ^ e0 := by
              simpa [Nat.sub_add_cancel hx1] using (pow_succ' x0 (e0 - 1)).symm
            have hypow : x1 * x1 ^ (e1 - 1) = x1 ^ e1 := by
              simpa [Nat.sub_add_cancel hy1] using (pow_succ' x1 (e1 - 1)).symm
            have hmul :
                (x0 * x1) * ((MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1))
                  = (MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ e0) * x1 ^ e1 := by
              calc
                (x0 * x1) * ((MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1))
                    = MvPolynomial.C (MvPolynomial.coeff s p) *
                        (x0 * x0 ^ (e0 - 1)) * (x1 * x1 ^ (e1 - 1)) := by
                            ring_nf
                _ = (MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ e0) * x1 ^ e1 := by
                      simp [hxpow, hypow, mul_assoc]
            simpa [e0, e1, hmul] using himg
          · have hpure : e0 = 0 ∨ e1 = 0 := by omega
            rcases hpure with hx0 | hy0
            · have hy3or4 : e1 = 3 ∨ e1 = 4 := by omega
              rcases hy3or4 with hy3 | hy4
              · have hmon :
                    MvPolynomial.monomial s (MvPolynomial.coeff s p) =
                      MvPolynomial.coeff s p • x1 ^ 3 := by
                  rw [monomial_fin2_eq]
                  simp [e0, e1, hx0, hy3, MvPolynomial.smul_eq_C_mul]
                simpa [hmon] using (show InAdmissibleImage u ((MvPolynomial.coeff s p) • x1 ^ 3) from
                  by
                    rcases hx1cub with ⟨v, hv, hvA⟩
                    exact ⟨(MvPolynomial.coeff s p) • v, isAdmissibleDirection_smul _ hv, by
                      simp [A_smul_right, hvA]⟩)
              · have hmon :
                    MvPolynomial.monomial s (MvPolynomial.coeff s p) =
                      MvPolynomial.coeff s p • x1 ^ 4 := by
                  rw [monomial_fin2_eq]
                  simp [e0, e1, hx0, hy4, MvPolynomial.smul_eq_C_mul]
                simpa [hmon] using (show InAdmissibleImage u ((MvPolynomial.coeff s p) • x1 ^ 4) from
                  by
                    rcases hx1quart with ⟨v, hv, hvA⟩
                    exact ⟨(MvPolynomial.coeff s p) • v, isAdmissibleDirection_smul _ hv, by
                      simp [A_smul_right, hvA]⟩)
            · have hx3or4 : e0 = 3 ∨ e0 = 4 := by omega
              rcases hx3or4 with hx3 | hx4
              · have hmon :
                    MvPolynomial.monomial s (MvPolynomial.coeff s p) =
                      MvPolynomial.coeff s p • x0 ^ 3 := by
                  rw [monomial_fin2_eq]
                  simp [e0, e1, hx3, hy0, MvPolynomial.smul_eq_C_mul]
                simpa [hmon] using (show InAdmissibleImage u ((MvPolynomial.coeff s p) • x0 ^ 3) from
                  by
                    rcases hx0cub with ⟨v, hv, hvA⟩
                    exact ⟨(MvPolynomial.coeff s p) • v, isAdmissibleDirection_smul _ hv, by
                      simp [A_smul_right, hvA]⟩)
              · have hmon :
                    MvPolynomial.monomial s (MvPolynomial.coeff s p) =
                      MvPolynomial.coeff s p • x0 ^ 4 := by
                  rw [monomial_fin2_eq]
                  simp [e0, e1, hx4, hy0, MvPolynomial.smul_eq_C_mul]
                simpa [hmon] using (show InAdmissibleImage u ((MvPolynomial.coeff s p) • x0 ^ 4) from
                  by
                    rcases hx0quart with ⟨v, hv, hvA⟩
                    exact ⟨(MvPolynomial.coeff s p) • v, isAdmissibleDirection_smul _ hv, by
                      simp [A_smul_right, hvA]⟩)
      · intro t ht
        exact hsub t (by simp [ht])
  exact hP (fun s hs => hs)

theorem residual_eq_zero_of_relations_const_x0x1_diffsq
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 * x1)
    (h3 : ∑ i : Fin 4, c3 i • u i = x0 ^ 2 - x1 ^ 2)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_in_admissible_image
    (B := B) hu hsocp (quartic_in_image_of_relations_const_x0x1_diffsq h0 h2 h3 hp.1)

/-- If the quadratic relation plane is any invertible basis of
`span(x₀x₁, x₀² - x₁²)`, we can reconstruct the canonical basis and use the
surjective theorem above. -/
theorem residual_eq_zero_of_relations_const_x0x1_diffsqPlane
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    {a b c d : ℝ}
    (h2 : ∑ i : Fin 4, c2 i • u i = a • (x0 * x1 : Poly) + b • (x0 ^ 2 - x1 ^ 2))
    (h3 : ∑ i : Fin 4, c3 i • u i = c • (x0 * x1 : Poly) + d • (x0 ^ 2 - x1 ^ 2))
    (hdet : a * d - b * c ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let det : ℝ := a * d - b * c
  have hdet0 : det ≠ 0 := by
    simpa [det] using hdet
  let c2' : Fin 4 → ℝ := fun i => (d / det) * c2 i + (-b / det) * c3 i
  let c3' : Fin 4 → ℝ := fun i => (-c / det) * c2 i + (a / det) * c3 i
  have hcoeff20 : (d / det) * a + (-b / det) * c = 1 := by
    field_simp [det, hdet0]
    ring
  have hcoeff21 : (d / det) * b + (-b / det) * d = 0 := by
    field_simp [det, hdet0]
    ring
  have hcoeff30 : (-c / det) * a + (a / det) * c = 0 := by
    field_simp [det, hdet0]
    ring
  have hcoeff31 : (-c / det) * b + (a / det) * d = 1 := by
    field_simp [det, hdet0]
    ring
  have h2' : ∑ i : Fin 4, c2' i • u i = x0 * x1 := by
    calc
      ∑ i : Fin 4, c2' i • u i
          = (d / det) • (a • (x0 * x1 : Poly) + b • (x0 ^ 2 - x1 ^ 2)) +
              (-b / det) • (c • (x0 * x1 : Poly) + d • (x0 ^ 2 - x1 ^ 2)) := by
                simp [c2', det, relation_linearCombination, h2, h3]
      _ = ((d / det) * a + (-b / det) * c) • (x0 * x1 : Poly) +
            ((d / det) * b + (-b / det) * d) • (x0 ^ 2 - x1 ^ 2) := by
              simp [smul_add, smul_smul, add_smul, add_assoc, add_left_comm, mul_comm]
      _ = x0 * x1 := by
            rw [hcoeff20, hcoeff21]
            simp
  have h3' : ∑ i : Fin 4, c3' i • u i = x0 ^ 2 - x1 ^ 2 := by
    calc
      ∑ i : Fin 4, c3' i • u i
          = (-c / det) • (a • (x0 * x1 : Poly) + b • (x0 ^ 2 - x1 ^ 2)) +
              (a / det) • (c • (x0 * x1 : Poly) + d • (x0 ^ 2 - x1 ^ 2)) := by
                simp [c3', det, relation_linearCombination, h2, h3]
      _ = ((-c / det) * a + (a / det) * c) • (x0 * x1 : Poly) +
            ((-c / det) * b + (a / det) * d) • (x0 ^ 2 - x1 ^ 2) := by
              simp [smul_add, smul_smul, add_smul, add_assoc, add_left_comm, add_comm,
                mul_comm]
      _ = x0 ^ 2 - x1 ^ 2 := by
            rw [hcoeff30, hcoeff31]
            simp
  exact residual_eq_zero_of_relations_const_x0x1_diffsq
    (B := B) (u := u) hu h0 h2' h3' hp hsocp

/-- Transport the surjective definite mixed-affine plane theorem across an
algebra equivalence. -/
theorem residual_eq_zero_of_equiv_relations_const_x0x1_diffsqPlane
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly))
    {a b c d : ℝ}
    (h2 :
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i =
        a • (x0 * x1 : Poly) + b • (x0 ^ 2 - x1 ^ 2))
    (h3 :
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i =
        c • (x0 * x1 : Poly) + d • (x0 ^ 2 - x1 ^ 2))
    (hdet : a * d - b * c ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0x1_diffsqPlane
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0 h2 h3 hdet hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

/-- Linearity of `A` in the left slot. -/
private theorem A_add_left_local (u v w : RankFourVec) :
    A (u + v) w = A u w + A v w := by
  simp [A, Finset.sum_add_distrib, add_mul]

/-- Linearity of `A` in the right slot. -/
private theorem A_add_right_local (u v w : RankFourVec) :
    A u (v + w) = A u v + A u w := by
  simp [A, Finset.sum_add_distrib, mul_add]

/-- Pairing formula for two scalar relation directions. -/
private theorem A_relationDirection_pair
    (c d : Fin 4 → ℝ) (p q : Poly) :
    A (relationDirection c p) (relationDirection d q)
      = (∑ i : Fin 4, c i * d i) • (p * q) := by
  calc
    A (relationDirection c p) (relationDirection d q)
        = ∑ i : Fin 4, d i • (c i • (p * q)) := by
            simp [A, relationDirection, mul_comm]
    _ = ∑ i : Fin 4, ((d i * c i) : ℝ) • (p * q) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp [smul_smul]
    _ = ∑ i : Fin 4, ((c i * d i) : ℝ) • (p * q) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp [mul_comm]
    _ = (∑ i : Fin 4, c i * d i) • (p * q) := by
      rw [Finset.sum_smul]

private theorem sum_sq_linearCombination
    (c d : Fin 4 → ℝ) (a b : ℝ) :
    ∑ i : Fin 4, (a * c i + b * d i) ^ 2 =
      a ^ 2 * (∑ i : Fin 4, (c i) ^ 2) +
        (2 * a * b) * (∑ i : Fin 4, c i * d i) +
          b ^ 2 * (∑ i : Fin 4, (d i) ^ 2) := by
  rw [Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four]
  ring

private theorem sum_mul_linearCombination
    (c d : Fin 4 → ℝ) (a b a' b' : ℝ) :
    ∑ i : Fin 4, (a * c i + b * d i) * (a' * c i + b' * d i) =
      (a * a') * (∑ i : Fin 4, (c i) ^ 2) +
        (a * b' + b * a') * (∑ i : Fin 4, c i * d i) +
          (b * b') * (∑ i : Fin 4, (d i) ^ 2) := by
  rw [Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four]
  ring

private theorem eq_zero_of_sum_sq_eq_zero {c : Fin 4 → ℝ}
    (h : ∑ i : Fin 4, (c i) ^ 2 = 0) (i : Fin 4) :
    c i = 0 := by
  have hzero :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => sq_nonneg (c j))).mp h
  exact sq_eq_zero_iff.mp (hzero i (by simp))

private theorem coordTailCorrectedGram_ne_zero
    (β2 a2 β3 a3 : ℝ) :
    ((β2 ^ 2 + a2 ^ 2 + 1) * (β3 ^ 2 + a3 ^ 2 + 1) -
        (β2 * β3 + a2 * a3) ^ 2) ≠ 0 := by
  have hEq :
      (β2 ^ 2 + a2 ^ 2 + 1) * (β3 ^ 2 + a3 ^ 2 + 1) -
          (β2 * β3 + a2 * a3) ^ 2 =
        1 + β2 ^ 2 + a2 ^ 2 + β3 ^ 2 + a3 ^ 2 + (β2 * a3 - a2 * β3) ^ 2 := by
    ring
  have hpos :
      0 <
        (β2 ^ 2 + a2 ^ 2 + 1) * (β3 ^ 2 + a3 ^ 2 + 1) -
          (β2 * β3 + a2 * a3) ^ 2 := by
    rw [hEq]
    positivity
  exact ne_of_gt hpos

private theorem gram_det_zero_imp_linearRelation
    (c d : Fin 4 → ℝ)
    (hgram :
      (∑ i : Fin 4, (c i) ^ 2) * (∑ i : Fin 4, (d i) ^ 2) -
        (∑ i : Fin 4, c i * d i) ^ 2 = 0) :
    ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ i : Fin 4, a * c i + b * d i = 0 := by
  let sc : ℝ := ∑ i : Fin 4, (c i) ^ 2
  let cd : ℝ := ∑ i : Fin 4, c i * d i
  by_cases hsc : sc = 0
  · refine ⟨1, 0, Or.inl one_ne_zero, ?_⟩
    intro i
    have hc0 : c i = 0 := by
      exact eq_zero_of_sum_sq_eq_zero (c := c) (by simpa [sc] using hsc) i
    simp [hc0]
  · refine ⟨cd, -sc, Or.inr ?_, ?_⟩
    · simpa [sc] using hsc
    · let w : Fin 4 → ℝ := fun i => cd * c i + (-sc) * d i
      have hw :
          ∑ i : Fin 4, (w i) ^ 2 = 0 := by
        rw [sum_sq_linearCombination]
        dsimp [w, sc, cd]
        have hEq :
            cd ^ 2 * (∑ i : Fin 4, (c i) ^ 2) +
                (2 * cd * (-∑ i : Fin 4, (c i) ^ 2)) * (∑ i : Fin 4, c i * d i) +
                  (-∑ i : Fin 4, (c i) ^ 2) ^ 2 * (∑ i : Fin 4, (d i) ^ 2) =
              (∑ i : Fin 4, (c i) ^ 2) *
                ((∑ i : Fin 4, (c i) ^ 2) * (∑ i : Fin 4, (d i) ^ 2) -
                  (∑ i : Fin 4, c i * d i) ^ 2) := by
          ring
        rw [hEq, hgram]
        ring
      intro i
      have hw0 : w i = 0 := eq_zero_of_sum_sq_eq_zero (c := w) hw i
      simpa [w, sc, cd] using hw0

private theorem gram_det_eq_sum_sq_minors
    (c d : Fin 4 → ℝ) :
    (∑ i : Fin 4, (c i) ^ 2) * (∑ i : Fin 4, (d i) ^ 2) -
        (∑ i : Fin 4, c i * d i) ^ 2 =
      (c 0 * d 1 - c 1 * d 0) ^ 2 +
        (c 0 * d 2 - c 2 * d 0) ^ 2 +
          (c 0 * d 3 - c 3 * d 0) ^ 2 +
            (c 1 * d 2 - c 2 * d 1) ^ 2 +
              (c 1 * d 3 - c 3 * d 1) ^ 2 +
                (c 2 * d 3 - c 3 * d 2) ^ 2 := by
  rw [Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four]
  ring

private theorem gram_det_zero_of_linearRelation
    (c d : Fin 4 → ℝ) {a b : ℝ}
    (hab : a ≠ 0 ∨ b ≠ 0)
    (hlin : ∀ i : Fin 4, a * c i + b * d i = 0) :
    (∑ i : Fin 4, (c i) ^ 2) * (∑ i : Fin 4, (d i) ^ 2) -
        (∑ i : Fin 4, c i * d i) ^ 2 = 0 := by
  rw [gram_det_eq_sum_sq_minors]
  rcases hab with ha | hb
  · have hc : ∀ i : Fin 4, c i = (-(b / a)) * d i := by
      intro i
      have hi := hlin i
      have hmul : a * (c i - (-(b / a)) * d i) = 0 := by
        field_simp [ha]
        linarith
      have hzero : c i - (-(b / a)) * d i = 0 := by
        exact (mul_eq_zero.mp hmul).resolve_left ha
      linarith
    have h01 : c 0 * d 1 - c 1 * d 0 = 0 := by simp [hc 0, hc 1]; ring
    have h02 : c 0 * d 2 - c 2 * d 0 = 0 := by simp [hc 0, hc 2]; ring
    have h03 : c 0 * d 3 - c 3 * d 0 = 0 := by simp [hc 0, hc 3]; ring
    have h12 : c 1 * d 2 - c 2 * d 1 = 0 := by simp [hc 1, hc 2]; ring
    have h13 : c 1 * d 3 - c 3 * d 1 = 0 := by simp [hc 1, hc 3]; ring
    have h23 : c 2 * d 3 - c 3 * d 2 = 0 := by simp [hc 2, hc 3]; ring
    simp [h01, h02, h03, h12, h13, h23]
  · have hd : ∀ i : Fin 4, d i = (-(a / b)) * c i := by
      intro i
      have hi := hlin i
      have hmul : b * (d i - (-(a / b)) * c i) = 0 := by
        field_simp [hb]
        linarith
      have hzero : d i - (-(a / b)) * c i = 0 := by
        exact (mul_eq_zero.mp hmul).resolve_left hb
      linarith
    have h01 : c 0 * d 1 - c 1 * d 0 = 0 := by simp [hd 0, hd 1]; ring
    have h02 : c 0 * d 2 - c 2 * d 0 = 0 := by simp [hd 0, hd 2]; ring
    have h03 : c 0 * d 3 - c 3 * d 0 = 0 := by simp [hd 0, hd 3]; ring
    have h12 : c 1 * d 2 - c 2 * d 1 = 0 := by simp [hd 1, hd 2]; ring
    have h13 : c 1 * d 3 - c 3 * d 1 = 0 := by simp [hd 1, hd 3]; ring
    have h23 : c 2 * d 3 - c 3 * d 2 = 0 := by simp [hd 2, hd 3]; ring
    simp [h01, h02, h03, h12, h13, h23]

private def homQuadPlaneA (q2 q3 : Poly) : ℝ :=
  MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
    MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3

private def homQuadPlaneB (q2 q3 : Poly) : ℝ :=
  MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m02 q3 -
    MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3

private def homQuadPlaneC (q2 q3 : Poly) : ℝ :=
  MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m11 q3 -
    MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m20 q3

private theorem homQuadPlane_relation_left (q2 q3 : Poly) :
    homQuadPlaneA q2 q3 * MvPolynomial.coeff m20 q2 +
      (-homQuadPlaneB q2 q3) * MvPolynomial.coeff m11 q2 +
        homQuadPlaneC q2 q3 * MvPolynomial.coeff m02 q2 = 0 := by
  simp [homQuadPlaneA, homQuadPlaneB, homQuadPlaneC]
  ring

private theorem homQuadPlane_relation_right (q2 q3 : Poly) :
    homQuadPlaneA q2 q3 * MvPolynomial.coeff m20 q3 +
      (-homQuadPlaneB q2 q3) * MvPolynomial.coeff m11 q3 +
        homQuadPlaneC q2 q3 * MvPolynomial.coeff m02 q3 = 0 := by
  simp [homQuadPlaneA, homQuadPlaneB, homQuadPlaneC]
  ring

/-- Sigma of two coefficient-space relation directions with orthogonal
coefficients. This is the clean quadratic identity needed for the planned
basis-invariant mixed-affine plane theorems. -/
theorem sigma_add_relationDirections_of_orthonormal
    (c d : Fin 4 → ℝ) (p q : Poly)
    (hcc : ∑ i : Fin 4, (c i) ^ 2 = 1)
    (hdd : ∑ i : Fin 4, (d i) ^ 2 = 1)
    (hcd : ∑ i : Fin 4, c i * d i = 0) :
    sigma (relationDirection c p + relationDirection d q) = p ^ 2 + q ^ 2 := by
  have hcc' : ∑ i : Fin 4, c i * c i = 1 := by
    simpa [pow_two] using hcc
  have hdd' : ∑ i : Fin 4, d i * d i = 1 := by
    simpa [pow_two] using hdd
  have hdc : ∑ i : Fin 4, d i * c i = 0 := by
    simpa [mul_comm] using hcd
  calc
    sigma (relationDirection c p + relationDirection d q)
        = A (relationDirection c p + relationDirection d q)
            (relationDirection c p + relationDirection d q) := by
              rw [A_self_eq_sigma]
    _ = A (relationDirection c p) (relationDirection c p)
          + A (relationDirection c p) (relationDirection d q)
          + (A (relationDirection d q) (relationDirection c p)
            + A (relationDirection d q) (relationDirection d q)) := by
          rw [A_add_left_local, A_add_right_local, A_add_right_local]
    _ = (∑ i : Fin 4, (c i) ^ 2) • (p * p)
          + (∑ i : Fin 4, c i * d i) • (p * q)
          + ((∑ i : Fin 4, d i * c i) • (q * p)
            + (∑ i : Fin 4, (d i) ^ 2) • (q * q)) := by
          rw [A_relationDirection_pair, A_relationDirection_pair,
            A_relationDirection_pair, A_relationDirection_pair]
          simp [pow_two]
    _ = p ^ 2 + q ^ 2 := by
          rw [hcd, hdc, hcc, hdd]
          simp [pow_two, mul_comm]

/-- Sigma identity for two orthogonal relation directions with arbitrary
coefficient norms. -/
theorem sigma_add_relationDirections_of_orthogonal
    (c d : Fin 4 → ℝ) (p q : Poly)
    {rc rd : ℝ}
    (hcc : ∑ i : Fin 4, (c i) ^ 2 = rc)
    (hdd : ∑ i : Fin 4, (d i) ^ 2 = rd)
    (hcd : ∑ i : Fin 4, c i * d i = 0) :
    sigma (relationDirection c p + relationDirection d q) = rc • (p ^ 2) + rd • (q ^ 2) := by
  have hdc : ∑ i : Fin 4, d i * c i = 0 := by
    simpa [mul_comm] using hcd
  calc
    sigma (relationDirection c p + relationDirection d q)
        = A (relationDirection c p + relationDirection d q)
            (relationDirection c p + relationDirection d q) := by
              rw [A_self_eq_sigma]
    _ = A (relationDirection c p) (relationDirection c p)
          + A (relationDirection c p) (relationDirection d q)
          + (A (relationDirection d q) (relationDirection c p)
            + A (relationDirection d q) (relationDirection d q)) := by
          rw [A_add_left_local, A_add_right_local, A_add_right_local]
    _ = (∑ i : Fin 4, (c i) ^ 2) • (p * p)
          + (∑ i : Fin 4, c i * d i) • (p * q)
          + ((∑ i : Fin 4, d i * c i) • (q * p)
            + (∑ i : Fin 4, (d i) ^ 2) • (q * q)) := by
          rw [A_relationDirection_pair, A_relationDirection_pair,
            A_relationDirection_pair, A_relationDirection_pair]
          simp [pow_two]
    _ = rc • (p ^ 2) + rd • (q ^ 2) := by
          rw [hcc, hcd, hdc, hdd]
          simp [pow_two, mul_comm]

/-- Sign-flipped version of the orthonormal sigma identity. This is the exact
shape used by kernel syzygies of the form `(-d₂)·(bℓ) + d₃·(aℓ)`. -/
theorem sigma_sub_add_relationDirections_of_orthonormal
    (c d : Fin 4 → ℝ) (p q : Poly)
    (hcc : ∑ i : Fin 4, (c i) ^ 2 = 1)
    (hdd : ∑ i : Fin 4, (d i) ^ 2 = 1)
    (hcd : ∑ i : Fin 4, c i * d i = 0) :
    sigma (relationDirection (-c) p + relationDirection d q) = p ^ 2 + q ^ 2 := by
  have hneg : ∑ i : Fin 4, ((-c) i) * d i = 0 := by
    simpa [Pi.neg_apply] using congrArg Neg.neg hcd
  have hcc' : ∑ i : Fin 4, (((-c) i) ^ 2) = 1 := by
    simpa [Pi.neg_apply] using hcc
  simpa [Pi.neg_apply] using
    sigma_add_relationDirections_of_orthonormal (-c) d p q hcc' hdd hneg

/-- Sign-flipped sigma identity for orthogonal relation directions with
arbitrary coefficient norms. -/
theorem sigma_sub_add_relationDirections_of_orthogonal
    (c d : Fin 4 → ℝ) (p q : Poly)
    {rc rd : ℝ}
    (hcc : ∑ i : Fin 4, (c i) ^ 2 = rc)
    (hdd : ∑ i : Fin 4, (d i) ^ 2 = rd)
    (hcd : ∑ i : Fin 4, c i * d i = 0) :
    sigma (relationDirection (-c) p + relationDirection d q) =
      rc • (p ^ 2) + rd • (q ^ 2) := by
  have hneg : ∑ i : Fin 4, ((-c) i) * d i = 0 := by
    simpa [Pi.neg_apply] using congrArg Neg.neg hcd
  have hcc' : ∑ i : Fin 4, (((-c) i) ^ 2) = rc := by
    simpa [Pi.neg_apply] using hcc
  simpa [Pi.neg_apply] using
    sigma_add_relationDirections_of_orthogonal (-c) d p q hcc' hdd hneg

/-- Any quartic with zero `x₀⁴` coefficient lies in the image once the factor
coordinates admit explicit scalar relations for the canonical mixed-affine
generators `1, x₀, x₀x₁, x₁²`. This abstracts the image part of the rank-14
representative proof away from the concrete choice of factor coordinates. -/
theorem quartic_in_image_of_relations_const_x0_x0x1_x1sq
    {u : RankFourVec}
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 * x1)
    (h3 : ∑ i : Fin 4, c3 i • u i = x1 ^ 2)
    {p : Poly} (hp : IsQuartic p)
    (h40 : MvPolynomial.coeff m40 p = 0) :
    InAdmissibleImage u p := by
  classical
  let monomialImage : ∀ (s : Fin 2 →₀ ℕ) (a : ℝ),
      s.sum (fun _ e => e) ≤ 4 →
      s ≠ m40 →
      InAdmissibleImage u (MvPolynomial.monomial s a) := by
    intro s a hdeg hne
    let e0 := s 0
    let e1 := s 1
    have hsum : s.sum (fun _ e => e) = s 0 + s 1 := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
    have hs0 : s 0 + s 1 ≤ 4 := by
      simpa [hsum] using hdeg
    have hs : e0 + e1 ≤ 4 := by
      simpa [e0, e1] using hs0
    by_cases hsmall : e0 + e1 ≤ 2
    · simpa [monomial_fin2_eq, e0, e1, one_mul] using
        (inAdmissibleImage_of_relation_mul
          (u := u) (c := c0) (r := (1 : Poly))
          (q := (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1)
          h0 (isQuadratic_C_mul_pow_pow a e0 e1 hsmall))
    · by_cases hy2 : 2 ≤ e1
      · have hs2 : e0 + (e1 - 2) ≤ 2 := by omega
        have himg :=
          inAdmissibleImage_of_relation_mul
            (u := u) (c := c3) (r := x1 ^ 2)
            (q := (MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 2))
            h3 (isQuadratic_C_mul_pow_pow a e0 (e1 - 2) hs2)
        rw [monomial_fin2_eq]
        simp [e0, e1] at himg ⊢
        have hmul : x1 ^ 2 * ((MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 2))
            = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
          calc
            x1 ^ 2 * ((MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 2))
                = MvPolynomial.C a * x0 ^ e0 * (x1 ^ 2 * x1 ^ (e1 - 2)) := by
                    ring_nf
            _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                  rw [← pow_add, Nat.add_sub_of_le hy2]
        simpa [e0, e1, hmul] using himg
      · by_cases hxy : 1 ≤ e0 ∧ 1 ≤ e1
        · rcases hxy with ⟨hx1, hy1⟩
          have hs2 : (e0 - 1) + (e1 - 1) ≤ 2 := by omega
          have himg :=
            inAdmissibleImage_of_relation_mul
              (u := u) (c := c2) (r := x0 * x1)
              (q := (MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1))
              h2 (isQuadratic_C_mul_pow_pow a (e0 - 1) (e1 - 1) hs2)
          rw [monomial_fin2_eq]
          simp [e0, e1] at himg ⊢
          have hxpow : x0 * x0 ^ (e0 - 1) = x0 ^ e0 := by
            simpa [Nat.sub_add_cancel hx1] using (pow_succ' x0 (e0 - 1)).symm
          have hypow : x1 * x1 ^ (e1 - 1) = x1 ^ e1 := by
            simpa [Nat.sub_add_cancel hy1] using (pow_succ' x1 (e1 - 1)).symm
          have hmul :
              (x0 * x1) * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1))
                = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
            calc
              (x0 * x1) * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1))
                  = MvPolynomial.C a *
                      (x0 * x0 ^ (e0 - 1)) * (x1 * x1 ^ (e1 - 1)) := by
                          ring_nf
              _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                    simp [hxpow, hypow, mul_assoc]
          simpa [e0, e1, hmul] using himg
        · have hx1 : 1 ≤ e0 := by omega
          have hy0 : e1 = 0 := by omega
          have hx4ne : e0 ≠ 4 := by
            intro hx4
            apply hne
            ext i
            fin_cases i <;> simp [m40, e0, e1, hx4, hy0]
          have hs2 : (e0 - 1) + e1 ≤ 2 := by omega
          have himg :=
            inAdmissibleImage_of_relation_mul
              (u := u) (c := c1) (r := x0)
              (q := (MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1)
              h1 (isQuadratic_C_mul_pow_pow a (e0 - 1) e1 hs2)
          rw [monomial_fin2_eq]
          simp [e0, e1] at himg ⊢
          have hxpow : x0 * x0 ^ (e0 - 1) = x0 ^ e0 := by
            simpa [Nat.sub_add_cancel hx1] using (pow_succ' x0 (e0 - 1)).symm
          have hmul : x0 * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1)
              = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
            calc
              x0 * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1)
                  = MvPolynomial.C a * (x0 * x0 ^ (e0 - 1)) * x1 ^ e1 := by
                      ring_nf
              _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                    simp [hxpow, mul_assoc]
          simpa [e0, e1, hmul] using himg
  rw [← MvPolynomial.support_sum_monomial_coeff p]
  let P : Finset (Fin 2 →₀ ℕ) → Prop := fun S =>
    (∀ s ∈ S, s ∈ p.support) →
      InAdmissibleImage u (∑ s ∈ S, MvPolynomial.monomial s (MvPolynomial.coeff s p))
  have hP : P p.support := by
    refine Finset.induction_on p.support ?_ ?_
    · intro hsub
      simpa using inAdmissibleImage_zero u
    · intro s ss hsnot ih hsub
      rw [Finset.sum_insert hsnot]
      refine inAdmissibleImage_add u ?_ (ih ?_)
      · have hsdeg : s.sum (fun _ e => e) ≤ 4 :=
          (MvPolynomial.le_totalDegree (hsub s (by simp))).trans hp
        have hscoeff : MvPolynomial.coeff s p ≠ 0 :=
          MvPolynomial.mem_support_iff.mp (hsub s (by simp))
        have hsne : s ≠ m40 := by
          intro hs
          apply hscoeff
          simpa [hs] using h40
        exact monomialImage s (MvPolynomial.coeff s p) hsdeg hsne
      · intro t ht
        exact hsub t (by simp [ht])
  exact hP (fun s hs => hs)

private theorem isQuadratic_x0_mul_x1_local : IsQuadratic (x0 * x1 : Poly) := by
  calc
    (x0 * x1).totalDegree ≤ x0.totalDegree + x1.totalDegree := by
      exact MvPolynomial.totalDegree_mul _ _
    _ = 2 := by simp [x0, x1]

private theorem isQuadratic_smul_x0_mul_x1_local (t : ℝ) :
    IsQuadratic (t • (x0 * x1 : Poly)) := by
  exact (MvPolynomial.totalDegree_smul_le t (x0 * x1 : Poly)).trans
    isQuadratic_x0_mul_x1_local

private theorem isQuadratic_smul_x0_sq_local (t : ℝ) :
    IsQuadratic (t • (x0 ^ 2 : Poly)) := by
  exact (MvPolynomial.totalDegree_smul_le t (x0 ^ 2 : Poly)).trans <|
    by simp [x0, MvPolynomial.totalDegree_X_pow]

private theorem coeff_m20_smul_x0_mul_x1_local (t : ℝ) :
    MvPolynomial.coeff m20 (t • (x0 * x1 : Poly)) = 0 := by
  rw [MvPolynomial.coeff_smul]
  have hx : MvPolynomial.coeff m20 (x0 * x1 : Poly) = 0 := by
    rw [show (x0 * x1 : Poly) = MvPolynomial.monomial m11 (1 : ℝ) by
      simp [x0, x1, m11, MvPolynomial.monomial_eq]]
    rw [MvPolynomial.coeff_monomial]
    split_ifs with h
    · exfalso
      have := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h.symm
      simp [m11, m20] at this
    · rfl
  simp [hx]

private theorem coeff_m20_smul_x0_sq_local (t : ℝ) :
    MvPolynomial.coeff m20 (t • (x0 ^ 2 : Poly)) = t := by
  rw [MvPolynomial.coeff_smul]
  have hx : MvPolynomial.coeff m20 (x0 ^ 2 : Poly) = 1 := by
    simp [x0, m20, MvPolynomial.coeff_X_pow]
  simp [hx]

/-- Homogeneous linear form `a x₀ + b x₁`. -/
private def homLine (a b : ℝ) : Poly :=
  MvPolynomial.C a * x0 + MvPolynomial.C b * x1

private theorem totalDegree_homLine_le (a b : ℝ) :
    (homLine a b).totalDegree ≤ 1 := by
  unfold homLine
  calc
    (MvPolynomial.C a * x0 + MvPolynomial.C b * x1 : Poly).totalDegree ≤
        max (MvPolynomial.C a * x0).totalDegree (MvPolynomial.C b * x1).totalDegree := by
          exact MvPolynomial.totalDegree_add _ _
    _ ≤ 1 := by
      refine max_le ?_ ?_
      · calc
          (MvPolynomial.C a * x0 : Poly).totalDegree ≤
              (MvPolynomial.C a).totalDegree + x0.totalDegree := by
                exact MvPolynomial.totalDegree_mul _ _
          _ = 1 := by simp [x0]
      · calc
          (MvPolynomial.C b * x1 : Poly).totalDegree ≤
              (MvPolynomial.C b).totalDegree + x1.totalDegree := by
                exact MvPolynomial.totalDegree_mul _ _
          _ = 1 := by simp [x1]

private theorem isQuadratic_smul_x0_mul_homLine (a b t : ℝ) :
    IsQuadratic (t • (x0 * homLine a b : Poly)) := by
  have hx0 : x0.totalDegree ≤ 1 := by simp [x0]
  calc
    (t • (x0 * homLine a b : Poly)).totalDegree ≤ (x0 * homLine a b : Poly).totalDegree := by
      exact MvPolynomial.totalDegree_smul_le t _
    _ ≤ x0.totalDegree + (homLine a b).totalDegree := by
      exact MvPolynomial.totalDegree_mul _ _
    _ ≤ 1 + 1 := by
      exact add_le_add hx0 (totalDegree_homLine_le a b)
    _ = 2 := by norm_num

private theorem coeff_m20_smul_x0_mul_homLine (a b t : ℝ) :
    MvPolynomial.coeff m20 (t • (x0 * homLine a b : Poly)) = t * a := by
  rw [MvPolynomial.coeff_smul]
  have hEq : (x0 * homLine a b : Poly) = a • (x0 ^ 2 : Poly) + b • (x0 * x1 : Poly) := by
    unfold homLine
    calc
      (x0 * (MvPolynomial.C a * x0 + MvPolynomial.C b * x1) : Poly)
          = x0 * (MvPolynomial.C a * x0) + x0 * (MvPolynomial.C b * x1) := by
              ring
      _ = MvPolynomial.C a * (x0 ^ 2 : Poly) + MvPolynomial.C b * (x0 * x1 : Poly) := by
            ring
      _ = a • (x0 ^ 2 : Poly) + b • (x0 * x1 : Poly) := by
            simp [MvPolynomial.smul_eq_C_mul]
  have hx0sq : MvPolynomial.coeff m20 (x0 ^ 2 : Poly) = 1 := by
    simpa using coeff_m20_smul_x0_sq_local (1 : ℝ)
  have hx0x1 : MvPolynomial.coeff m20 (x0 * x1 : Poly) = 0 := by
    simpa using coeff_m20_smul_x0_mul_x1_local (1 : ℝ)
  rw [hEq, MvPolynomial.coeff_add, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul, hx0sq, hx0x1]
  simp [smul_eq_mul]

/-- Rank-14 kernel built from an arbitrary basis of `span(x₀x₁,x₁²)`. -/
private def rank14PlaneKerDet (c2 c3 : Fin 4 → ℝ)
    (a b c d t : ℝ) : RankFourVec :=
  relationDirection (-c2) (t • (x0 * homLine c d : Poly)) +
    relationDirection c3 (t • (x0 * homLine a b : Poly))

private theorem rank14PlaneKerDet_admissible
    (c2 c3 : Fin 4 → ℝ) (a b c d t : ℝ) :
    IsAdmissibleDirection (rank14PlaneKerDet c2 c3 a b c d t) := by
  refine isAdmissibleDirection_add
    (relationDirection_admissible (-c2) (isQuadratic_smul_x0_mul_homLine c d t))
    (relationDirection_admissible c3 (isQuadratic_smul_x0_mul_homLine a b t))

private theorem rank14PlaneKerDet_inKer
    {u : RankFourVec} {c2 c3 : Fin 4 → ℝ}
    {a b c d t : ℝ}
    (h2 : ∑ i : Fin 4, c2 i • u i = a • (x0 * x1 : Poly) + b • (x1 ^ 2 : Poly))
    (h3 : ∑ i : Fin 4, c3 i • u i = c • (x0 * x1 : Poly) + d • (x1 ^ 2 : Poly)) :
    InAdmissibleKer u (rank14PlaneKerDet c2 c3 a b c d t) := by
  refine ⟨rank14PlaneKerDet_admissible c2 c3 a b c d t, ?_⟩
  have hh2 : a • (x0 * x1 : Poly) + b • (x1 ^ 2 : Poly) = x1 * homLine a b := by
    unfold homLine
    calc
      (a • (x0 * x1 : Poly) + b • (x1 ^ 2 : Poly))
          = MvPolynomial.C a * (x0 * x1 : Poly) + MvPolynomial.C b * (x1 ^ 2 : Poly) := by
              simp [MvPolynomial.smul_eq_C_mul]
      _ = x1 * (MvPolynomial.C a * x0) + x1 * (MvPolynomial.C b * x1) := by
            ring
      _ = x1 * (MvPolynomial.C a * x0 + MvPolynomial.C b * x1) := by ring
  have hh3 : c • (x0 * x1 : Poly) + d • (x1 ^ 2 : Poly) = x1 * homLine c d := by
    unfold homLine
    calc
      (c • (x0 * x1 : Poly) + d • (x1 ^ 2 : Poly))
          = MvPolynomial.C c * (x0 * x1 : Poly) + MvPolynomial.C d * (x1 ^ 2 : Poly) := by
              simp [MvPolynomial.smul_eq_C_mul]
      _ = x1 * (MvPolynomial.C c * x0) + x1 * (MvPolynomial.C d * x1) := by
            ring
      _ = x1 * (MvPolynomial.C c * x0 + MvPolynomial.C d * x1) := by ring
  rw [rank14PlaneKerDet, A_add_right_local, A_relationDirection, A_relationDirection]
  simp [Pi.neg_apply, h2, h3, hh2, hh3, homLine, mul_assoc, mul_left_comm,
    mul_comm]

private theorem coeff_m40_sigma_rank14PlaneKerDet
    (c2 c3 : Fin 4 → ℝ) (a b c d t : ℝ)
    (h22 : ∑ i : Fin 4, (c2 i) ^ 2 = 1)
    (h33 : ∑ i : Fin 4, (c3 i) ^ 2 = 1)
    (h23 : ∑ i : Fin 4, c2 i * c3 i = 0) :
    MvPolynomial.coeff m40 (sigma (rank14PlaneKerDet c2 c3 a b c d t)) =
      (a ^ 2 + c ^ 2) * t ^ 2 := by
  rw [rank14PlaneKerDet, sigma_sub_add_relationDirections_of_orthonormal c2 c3
    (t • (x0 * homLine c d : Poly)) (t • (x0 * homLine a b : Poly)) h22 h33 h23]
  have h2sq :
      MvPolynomial.coeff m40 ((t • (x0 * homLine c d : Poly)) ^ 2) = (t * c) ^ 2 := by
    rw [coeff_m40_sq_of_quadratic_eq _ (isQuadratic_smul_x0_mul_homLine c d t)]
    rw [coeff_m20_smul_x0_mul_homLine]
  have h3sq :
      MvPolynomial.coeff m40 ((t • (x0 * homLine a b : Poly)) ^ 2) = (t * a) ^ 2 := by
    rw [coeff_m40_sq_of_quadratic_eq _ (isQuadratic_smul_x0_mul_homLine a b t)]
    rw [coeff_m20_smul_x0_mul_homLine]
  rw [MvPolynomial.coeff_add, h2sq, h3sq]
  ring

/-- The abstract rank-14 kernel built from relation data for `x₀x₁` and
`x₁²`. -/
private def rank14PlaneKer (c2 c3 : Fin 4 → ℝ) (t : ℝ) : RankFourVec :=
  relationDirection (-c2) (t • (x0 * x1 : Poly)) +
    relationDirection c3 (t • (x0 ^ 2 : Poly))

private theorem rank14PlaneKer_admissible (c2 c3 : Fin 4 → ℝ) (t : ℝ) :
    IsAdmissibleDirection (rank14PlaneKer c2 c3 t) := by
  refine isAdmissibleDirection_add
    (relationDirection_admissible (-c2) (isQuadratic_smul_x0_mul_x1_local t))
    (relationDirection_admissible c3 (isQuadratic_smul_x0_sq_local t))

private theorem rank14PlaneKer_inKer
    {u : RankFourVec} {c2 c3 : Fin 4 → ℝ} {t : ℝ}
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 * x1)
    (h3 : ∑ i : Fin 4, c3 i • u i = x1 ^ 2) :
    InAdmissibleKer u (rank14PlaneKer c2 c3 t) := by
  refine ⟨rank14PlaneKer_admissible c2 c3 t, ?_⟩
  rw [rank14PlaneKer, A_add_right_local, A_relationDirection, A_relationDirection]
  simp [Pi.neg_apply, h2, h3]
  ring_nf

private theorem coeff_m40_sigma_rank14PlaneKer
    (c2 c3 : Fin 4 → ℝ) (t : ℝ)
    (h22 : ∑ i : Fin 4, (c2 i) ^ 2 = 1)
    (h33 : ∑ i : Fin 4, (c3 i) ^ 2 = 1)
    (h23 : ∑ i : Fin 4, c2 i * c3 i = 0) :
    MvPolynomial.coeff m40 (sigma (rank14PlaneKer c2 c3 t)) = t ^ 2 := by
  rw [rank14PlaneKer, sigma_sub_add_relationDirections_of_orthonormal c2 c3
    (t • (x0 * x1 : Poly)) (t • (x0 ^ 2 : Poly)) h22 h33 h23]
  have hxy :
      MvPolynomial.coeff m40 ((t • (x0 * x1 : Poly)) ^ 2) = 0 := by
    rw [coeff_m40_sq_of_quadratic_eq _ (isQuadratic_smul_x0_mul_x1_local t)]
    rw [coeff_m20_smul_x0_mul_x1_local]
    ring
  have hx0 :
      MvPolynomial.coeff m40 ((t • (x0 ^ 2 : Poly)) ^ 2) = t ^ 2 := by
    rw [coeff_m40_sq_of_quadratic_eq _ (isQuadratic_smul_x0_sq_local t)]
    rw [coeff_m20_smul_x0_sq_local]
  rw [MvPolynomial.coeff_add, hxy, hx0]
  ring

private theorem coeff_m40_sigma_rank14PlaneKer_of_orthogonal
    (c2 c3 : Fin 4 → ℝ) (t : ℝ)
    {r2 r3 : ℝ}
    (h22 : ∑ i : Fin 4, (c2 i) ^ 2 = r2)
    (h33 : ∑ i : Fin 4, (c3 i) ^ 2 = r3)
    (h23 : ∑ i : Fin 4, c2 i * c3 i = 0) :
    MvPolynomial.coeff m40 (sigma (rank14PlaneKer c2 c3 t)) = r3 * t ^ 2 := by
  rw [rank14PlaneKer, sigma_sub_add_relationDirections_of_orthogonal c2 c3
    (t • (x0 * x1 : Poly)) (t • (x0 ^ 2 : Poly)) h22 h33 h23]
  have hxy :
      MvPolynomial.coeff m40 ((t • (x0 * x1 : Poly)) ^ 2) = 0 := by
    rw [coeff_m40_sq_of_quadratic_eq _ (isQuadratic_smul_x0_mul_x1_local t)]
    rw [coeff_m20_smul_x0_mul_x1_local]
    ring
  have hx0 :
      MvPolynomial.coeff m40 ((t • (x0 ^ 2 : Poly)) ^ 2) = t ^ 2 := by
    rw [coeff_m40_sq_of_quadratic_eq _ (isQuadratic_smul_x0_sq_local t)]
    rw [coeff_m20_smul_x0_sq_local]
  rw [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul, hxy, hx0]
  simp [smul_eq_mul]

/-- Rank-14 mixed-affine certificate with orthogonal, not necessarily unit,
coefficient directions. -/
theorem residual_eq_zero_of_relations_const_x0_x0x1_x1sq_of_orthogonal
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 * x1)
    (h3 : ∑ i : Fin 4, c3 i • u i = x1 ^ 2)
    {r2 r3 : ℝ}
    (h22 : ∑ i : Fin 4, (c2 i) ^ 2 = r2)
    (h33 : ∑ i : Fin 4, (c3 i) ^ 2 = r3)
    (h23 : ∑ i : Fin 4, c2 i * c3 i = 0)
    (hr3 : r3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  rcases hp with ⟨hpquartic, k, qs, hqdeg, hpq⟩
  let s : ℝ := ∑ i : Fin k, (MvPolynomial.coeff m20 (qs i)) ^ 2
  let t : ℝ := Real.sqrt (s / r3)
  let w : RankFourVec := rank14PlaneKer c2 c3 t
  have hsnonneg : 0 ≤ s := by
    dsimp [s]
    positivity
  have hr3_nonneg : 0 ≤ r3 := by
    rw [← h33]
    positivity
  have hr3_pos : 0 < r3 := lt_of_le_of_ne hr3_nonneg hr3.symm
  have hsdiv_nonneg : 0 ≤ s / r3 := by positivity
  have hp40 : MvPolynomial.coeff m40 p = s := by
    rw [hpq, MvPolynomial.coeff_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact coeff_m40_sq_of_quadratic_eq (qs i) (hqdeg i)
  have hwker : InAdmissibleKer u w := by
    dsimp [w]
    exact rank14PlaneKer_inKer h2 h3
  have hw40 : MvPolynomial.coeff m40 (sigma w) = s := by
    change MvPolynomial.coeff m40 (sigma (rank14PlaneKer c2 c3 t)) = s
    calc
      MvPolynomial.coeff m40 (sigma (rank14PlaneKer c2 c3 t)) = r3 * t ^ 2 := by
        exact coeff_m40_sigma_rank14PlaneKer_of_orthogonal c2 c3 t h22 h33 h23
      _ = r3 * (s / r3) := by
        dsimp [t]
        rw [Real.sq_sqrt hsdiv_nonneg]
      _ = s := by
        field_simp [hr3]
  have hquartic_sub : IsQuartic (p - sigma w) := by
    calc
      (p - sigma w).totalDegree ≤ max p.totalDegree (sigma w).totalDegree := by
        exact MvPolynomial.totalDegree_sub _ _
      _ ≤ 4 := by
        exact max_le hpquartic (isQuartic_sigma_of_admissible hwker.1)
  have h40_sub : MvPolynomial.coeff m40 (p - sigma w) = 0 := by
    rw [MvPolynomial.coeff_sub, hp40, hw40]
    ring
  have himg : InAdmissibleImage u (p - sigma w) :=
    quartic_in_image_of_relations_const_x0_x0x1_x1sq h0 h1 h2 h3 hquartic_sub h40_sub
  refine admissible_image_plus_cone_residual_eq_zero (B := B)
    (u := u) (uImg := u)
    hu hsocp
    (imageOrthogonalResidual_self (B := B) hsocp.1) ?_
  refine ⟨p - sigma w, {w}, himg, ?_, ?_⟩
  · intro w' hw'
    have hw' : w' = w := by simpa using hw'
    subst hw'
    exact hwker
  · simp [w, sub_eq_add_neg]

/-- Abstract rank-14 mixed-affine certificate: once the factor admits explicit
relations for `1`, `x₀`, `x₀x₁`, and `x₁²`, and the last two relation vectors
are orthonormal in coefficient space, every SOCP has zero residual. -/
theorem residual_eq_zero_of_relations_const_x0_x0x1_x1sq
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 * x1)
    (h3 : ∑ i : Fin 4, c3 i • u i = x1 ^ 2)
    (h22 : ∑ i : Fin 4, (c2 i) ^ 2 = 1)
    (h33 : ∑ i : Fin 4, (c3 i) ^ 2 = 1)
    (h23 : ∑ i : Fin 4, c2 i * c3 i = 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  rcases hp with ⟨hpquartic, k, qs, hqdeg, hpq⟩
  let s : ℝ := ∑ i : Fin k, (MvPolynomial.coeff m20 (qs i)) ^ 2
  let t : ℝ := Real.sqrt s
  let w : RankFourVec := rank14PlaneKer c2 c3 t
  have hsnonneg : 0 ≤ s := by
    dsimp [s]
    positivity
  have hp40 : MvPolynomial.coeff m40 p = s := by
    rw [hpq, MvPolynomial.coeff_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact coeff_m40_sq_of_quadratic_eq (qs i) (hqdeg i)
  have hwker : InAdmissibleKer u w := by
    dsimp [w]
    exact rank14PlaneKer_inKer h2 h3
  have hw40 : MvPolynomial.coeff m40 (sigma w) = s := by
    change MvPolynomial.coeff m40 (sigma (rank14PlaneKer c2 c3 t)) = s
    calc
      MvPolynomial.coeff m40 (sigma (rank14PlaneKer c2 c3 t)) = t ^ 2 := by
        exact coeff_m40_sigma_rank14PlaneKer c2 c3 t h22 h33 h23
      _ = s := by
        dsimp [t]
        rw [Real.sq_sqrt hsnonneg]
  have hquartic_sub : IsQuartic (p - sigma w) := by
    calc
      (p - sigma w).totalDegree ≤ max p.totalDegree (sigma w).totalDegree := by
        exact MvPolynomial.totalDegree_sub _ _
      _ ≤ 4 := by
        exact max_le hpquartic (isQuartic_sigma_of_admissible hwker.1)
  have h40_sub : MvPolynomial.coeff m40 (p - sigma w) = 0 := by
    rw [MvPolynomial.coeff_sub, hp40, hw40]
    ring
  have himg : InAdmissibleImage u (p - sigma w) :=
    quartic_in_image_of_relations_const_x0_x0x1_x1sq h0 h1 h2 h3 hquartic_sub h40_sub
  refine admissible_image_plus_cone_residual_eq_zero (B := B)
    (u := u) (uImg := u)
    hu hsocp
    (imageOrthogonalResidual_self (B := B) hsocp.1) ?_
  refine ⟨p - sigma w, {w}, himg, ?_, ?_⟩
  · intro w' hw'
    have hw' : w' = w := by simpa using hw'
    subst hw'
    exact hwker
  · simp [w, sub_eq_add_neg]

/-- Orthogonal change of basis inside `span(x₀x₁, x₁²)` reduces to the exact
rank-14 mixed-affine plane theorem. -/
theorem residual_eq_zero_of_relations_const_x0_x1Plane
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {a b c d : ℝ}
    (h2 : ∑ i : Fin 4, c2 i • u i = a • (x0 * x1 : Poly) + b • (x1 ^ 2 : Poly))
    (h3 : ∑ i : Fin 4, c3 i • u i = c • (x0 * x1 : Poly) + d • (x1 ^ 2 : Poly))
    (h22 : ∑ i : Fin 4, (c2 i) ^ 2 = 1)
    (h33 : ∑ i : Fin 4, (c3 i) ^ 2 = 1)
    (h23 : ∑ i : Fin 4, c2 i * c3 i = 0)
    (hcol0 : a ^ 2 + c ^ 2 = 1)
    (hcol1 : b ^ 2 + d ^ 2 = 1)
    (hcol01 : a * b + c * d = 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let c2' : Fin 4 → ℝ := fun i => a * c2 i + c * c3 i
  let c3' : Fin 4 → ℝ := fun i => b * c2 i + d * c3 i
  have h2' : ∑ i : Fin 4, c2' i • u i = x0 * x1 := by
    calc
      ∑ i : Fin 4, c2' i • u i
          = a • (a • (x0 * x1 : Poly) + b • (x1 ^ 2 : Poly)) +
              c • (c • (x0 * x1 : Poly) + d • (x1 ^ 2 : Poly)) := by
                simp [c2', relation_linearCombination, h2, h3]
      _ = (a ^ 2 + c ^ 2) • (x0 * x1 : Poly) + (a * b + c * d) • (x1 ^ 2 : Poly) := by
            rw [add_smul, add_smul]
            simp [smul_add, smul_smul, pow_two, add_assoc, add_left_comm]
      _ = x0 * x1 := by simp [hcol0, hcol01]
  have h3' : ∑ i : Fin 4, c3' i • u i = x1 ^ 2 := by
    calc
      ∑ i : Fin 4, c3' i • u i
          = b • (a • (x0 * x1 : Poly) + b • (x1 ^ 2 : Poly)) +
              d • (c • (x0 * x1 : Poly) + d • (x1 ^ 2 : Poly)) := by
                simp [c3', relation_linearCombination, h2, h3]
      _ = (a * b + c * d) • (x0 * x1 : Poly) + (b ^ 2 + d ^ 2) • (x1 ^ 2 : Poly) := by
            rw [add_smul, add_smul]
            simp [smul_add, smul_smul, pow_two, add_assoc, add_left_comm, mul_comm]
      _ = x1 ^ 2 := by simp [hcol1, hcol01]
  have h22' : ∑ i : Fin 4, (c2' i) ^ 2 = 1 := by
    calc
      ∑ i : Fin 4, (c2' i) ^ 2
          = a ^ 2 * (∑ i : Fin 4, (c2 i) ^ 2) +
              (2 * a * c) * (∑ i : Fin 4, c2 i * c3 i) +
                c ^ 2 * (∑ i : Fin 4, (c3 i) ^ 2) := by
                  simpa [c2'] using sum_sq_linearCombination c2 c3 a c
      _ = 1 := by rw [h22, h23, h33]; nlinarith [hcol0]
  have h33' : ∑ i : Fin 4, (c3' i) ^ 2 = 1 := by
    calc
      ∑ i : Fin 4, (c3' i) ^ 2
          = b ^ 2 * (∑ i : Fin 4, (c2 i) ^ 2) +
              (2 * b * d) * (∑ i : Fin 4, c2 i * c3 i) +
                d ^ 2 * (∑ i : Fin 4, (c3 i) ^ 2) := by
                  simpa [c3'] using sum_sq_linearCombination c2 c3 b d
      _ = 1 := by rw [h22, h23, h33]; nlinarith [hcol1]
  have h23' : ∑ i : Fin 4, c2' i * c3' i = 0 := by
    calc
      ∑ i : Fin 4, c2' i * c3' i
          = (a * b) * (∑ i : Fin 4, (c2 i) ^ 2) +
              (a * d + c * b) * (∑ i : Fin 4, c2 i * c3 i) +
                (c * d) * (∑ i : Fin 4, (c3 i) ^ 2) := by
                  simpa [c2', c3'] using sum_mul_linearCombination c2 c3 a c b d
      _ = 0 := by rw [h22, h23, h33]; nlinarith [hcol01]
  exact residual_eq_zero_of_relations_const_x0_x0x1_x1sq
    (B := B) (u := u) hu h0 h1 h2' h3' h22' h33' h23' hp hsocp

/-- Rank-14 plane theorem with orthogonal but not necessarily unit column
coefficients in the canonical plane. -/
theorem residual_eq_zero_of_relations_const_x0_x1Plane_scaled
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {a b c d : ℝ}
    (h2 : ∑ i : Fin 4, c2 i • u i = a • (x0 * x1 : Poly) + b • (x1 ^ 2 : Poly))
    (h3 : ∑ i : Fin 4, c3 i • u i = c • (x0 * x1 : Poly) + d • (x1 ^ 2 : Poly))
    (h22 : ∑ i : Fin 4, (c2 i) ^ 2 = 1)
    (h33 : ∑ i : Fin 4, (c3 i) ^ 2 = 1)
    (h23 : ∑ i : Fin 4, c2 i * c3 i = 0)
    (hcol01 : a * b + c * d = 0)
    (hcol0nz : a ^ 2 + c ^ 2 ≠ 0)
    (hcol1nz : b ^ 2 + d ^ 2 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let n0 : ℝ := a ^ 2 + c ^ 2
  let n1 : ℝ := b ^ 2 + d ^ 2
  let c2' : Fin 4 → ℝ := fun i => (a / n0) * c2 i + (c / n0) * c3 i
  let c3' : Fin 4 → ℝ := fun i => (b / n1) * c2 i + (d / n1) * c3 i
  have hn0 : n0 ≠ 0 := by simpa [n0] using hcol0nz
  have hn1 : n1 ≠ 0 := by simpa [n1] using hcol1nz
  have h2' : ∑ i : Fin 4, c2' i • u i = x0 * x1 := by
    calc
      ∑ i : Fin 4, c2' i • u i
          = (a / n0) • (a • (x0 * x1 : Poly) + b • (x1 ^ 2 : Poly)) +
              (c / n0) • (c • (x0 * x1 : Poly) + d • (x1 ^ 2 : Poly)) := by
                simp [c2', n0, relation_linearCombination, h2, h3]
      _ = (a / n0) • (a • (x0 * x1 : Poly)) + (a / n0) • (b • (x1 ^ 2 : Poly)) +
            ((c / n0) • (c • (x0 * x1 : Poly)) + (c / n0) • (d • (x1 ^ 2 : Poly))) := by
              rw [smul_add, smul_add, add_assoc]
      _ = (((a / n0) * a + (c / n0) * c) • (x0 * x1 : Poly)) +
            (((a / n0) * b + (c / n0) * d) • (x1 ^ 2 : Poly)) := by
              rw [smul_smul, smul_smul, smul_smul, smul_smul]
              calc
                (a / n0 * a) • (x0 * x1 : Poly) + (a / n0 * b) • (x1 ^ 2 : Poly) +
                    ((c / n0 * c) • (x0 * x1 : Poly) + (c / n0 * d) • (x1 ^ 2 : Poly))
                    =
                    ((a / n0 * a) • (x0 * x1 : Poly) + (c / n0 * c) • (x0 * x1 : Poly)) +
                      ((a / n0 * b) • (x1 ^ 2 : Poly) + (c / n0 * d) • (x1 ^ 2 : Poly)) := by
                        abel_nf
                _ = (((a / n0) * a + (c / n0) * c) • (x0 * x1 : Poly)) +
                      (((a / n0) * b + (c / n0) * d) • (x1 ^ 2 : Poly)) := by
                        rw [← add_smul, ← add_smul]
      _ = ((a ^ 2 + c ^ 2) / n0) • (x0 * x1 : Poly) +
            ((a * b + c * d) / n0) • (x1 ^ 2 : Poly) := by
              have hs0 : (a / n0) * a + (c / n0) * c = (a ^ 2 + c ^ 2) / n0 := by
                field_simp [hn0]
              have hs1 : (a / n0) * b + (c / n0) * d = (a * b + c * d) / n0 := by
                field_simp [hn0]
              simp [hs0, hs1]
      _ = x0 * x1 := by
            rw [hcol01]
            simp [n0, hn0]
  have h3' : ∑ i : Fin 4, c3' i • u i = x1 ^ 2 := by
    calc
      ∑ i : Fin 4, c3' i • u i
          = (b / n1) • (a • (x0 * x1 : Poly) + b • (x1 ^ 2 : Poly)) +
              (d / n1) • (c • (x0 * x1 : Poly) + d • (x1 ^ 2 : Poly)) := by
                simp [c3', n1, relation_linearCombination, h2, h3]
      _ = (b / n1) • (a • (x0 * x1 : Poly)) + (b / n1) • (b • (x1 ^ 2 : Poly)) +
            ((d / n1) • (c • (x0 * x1 : Poly)) + (d / n1) • (d • (x1 ^ 2 : Poly))) := by
              rw [smul_add, smul_add, add_assoc]
      _ = (((b / n1) * a + (d / n1) * c) • (x0 * x1 : Poly)) +
            (((b / n1) * b + (d / n1) * d) • (x1 ^ 2 : Poly)) := by
              rw [smul_smul, smul_smul, smul_smul, smul_smul]
              calc
                (b / n1 * a) • (x0 * x1 : Poly) + (b / n1 * b) • (x1 ^ 2 : Poly) +
                    ((d / n1 * c) • (x0 * x1 : Poly) + (d / n1 * d) • (x1 ^ 2 : Poly))
                    =
                    ((b / n1 * a) • (x0 * x1 : Poly) + (d / n1 * c) • (x0 * x1 : Poly)) +
                      ((b / n1 * b) • (x1 ^ 2 : Poly) + (d / n1 * d) • (x1 ^ 2 : Poly)) := by
                        abel_nf
                _ = (((b / n1) * a + (d / n1) * c) • (x0 * x1 : Poly)) +
                      (((b / n1) * b + (d / n1) * d) • (x1 ^ 2 : Poly)) := by
                        rw [← add_smul, ← add_smul]
      _ = ((a * b + c * d) / n1) • (x0 * x1 : Poly) +
            ((b ^ 2 + d ^ 2) / n1) • (x1 ^ 2 : Poly) := by
              have hs0 : (b / n1) * a + (d / n1) * c = (a * b + c * d) / n1 := by
                field_simp [hn1]
              have hs1 : (b / n1) * b + (d / n1) * d = (b ^ 2 + d ^ 2) / n1 := by
                field_simp [hn1]
              simp [hs0, hs1]
      _ = x1 ^ 2 := by
            rw [hcol01]
            simp [n1, hn1]
  have h22' : ∑ i : Fin 4, (c2' i) ^ 2 = 1 / n0 := by
    calc
      ∑ i : Fin 4, (c2' i) ^ 2
          = (a / n0) ^ 2 * (∑ i : Fin 4, (c2 i) ^ 2) +
              (2 * (a / n0) * (c / n0)) * (∑ i : Fin 4, c2 i * c3 i) +
                (c / n0) ^ 2 * (∑ i : Fin 4, (c3 i) ^ 2) := by
                  simpa [c2'] using sum_sq_linearCombination c2 c3 (a / n0) (c / n0)
      _ = 1 / n0 := by
            rw [h22, h23, h33]
            field_simp [hn0]
            ring
  have h33' : ∑ i : Fin 4, (c3' i) ^ 2 = 1 / n1 := by
    calc
      ∑ i : Fin 4, (c3' i) ^ 2
          = (b / n1) ^ 2 * (∑ i : Fin 4, (c2 i) ^ 2) +
              (2 * (b / n1) * (d / n1)) * (∑ i : Fin 4, c2 i * c3 i) +
                (d / n1) ^ 2 * (∑ i : Fin 4, (c3 i) ^ 2) := by
                  simpa [c3'] using sum_sq_linearCombination c2 c3 (b / n1) (d / n1)
      _ = 1 / n1 := by
            rw [h22, h23, h33]
            field_simp [hn1]
            ring
  have h23' : ∑ i : Fin 4, c2' i * c3' i = 0 := by
    calc
      ∑ i : Fin 4, c2' i * c3' i
          = ((a / n0) * (b / n1)) * (∑ i : Fin 4, (c2 i) ^ 2) +
              ((a / n0) * (d / n1) + (c / n0) * (b / n1)) * (∑ i : Fin 4, c2 i * c3 i) +
                ((c / n0) * (d / n1)) * (∑ i : Fin 4, (c3 i) ^ 2) := by
                  simpa [c2', c3'] using
                    sum_mul_linearCombination c2 c3 (a / n0) (c / n0) (b / n1) (d / n1)
      _ = 0 := by
            rw [h22, h23, h33]
            field_simp [hn0, hn1]
            ring_nf
            nlinarith [hcol01]
  exact residual_eq_zero_of_relations_const_x0_x0x1_x1sq_of_orthogonal
    (B := B) (u := u) hu h0 h1 h2' h3' h22' h33' h23' (by simpa [n1] using one_div_ne_zero hn1) hp hsocp

/-- Rank-14 plane theorem with an arbitrary invertible basis of
`span(x₀x₁, x₁²)`. The kernel certificate works directly with determinant data,
so no polynomial-column orthogonality is required. -/
theorem residual_eq_zero_of_relations_const_x0_x1Plane_det
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {a b c d : ℝ}
    (h2 : ∑ i : Fin 4, c2 i • u i = a • (x0 * x1 : Poly) + b • (x1 ^ 2 : Poly))
    (h3 : ∑ i : Fin 4, c3 i • u i = c • (x0 * x1 : Poly) + d • (x1 ^ 2 : Poly))
    (h22 : ∑ i : Fin 4, (c2 i) ^ 2 = 1)
    (h33 : ∑ i : Fin 4, (c3 i) ^ 2 = 1)
    (h23 : ∑ i : Fin 4, c2 i * c3 i = 0)
    (hdet : a * d - b * c ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  rcases hp with ⟨hpquartic, k, qs, hqdeg, hpq⟩
  let det : ℝ := a * d - b * c
  let n : ℝ := a ^ 2 + c ^ 2
  let c2' : Fin 4 → ℝ := fun i => (d / det) * c2 i + (-b / det) * c3 i
  let c3' : Fin 4 → ℝ := fun i => (-c / det) * c2 i + (a / det) * c3 i
  let s : ℝ := ∑ i : Fin k, (MvPolynomial.coeff m20 (qs i)) ^ 2
  let t : ℝ := Real.sqrt (s / n)
  let w : RankFourVec := rank14PlaneKerDet c2 c3 a b c d t
  have hdet0 : det ≠ 0 := by
    simpa [det] using hdet
  have hn : n ≠ 0 := by
    intro hn0
    have hn0' : a ^ 2 + c ^ 2 = 0 := by
      simpa [n] using hn0
    have hsqa : a ^ 2 = 0 := by
      nlinarith [sq_nonneg c, hn0']
    have hsqc : c ^ 2 = 0 := by
      nlinarith [sq_nonneg a, hn0']
    have ha0 : a = 0 := by
      nlinarith [sq_nonneg a, hsqa]
    have hc0 : c = 0 := by
      nlinarith [sq_nonneg c, hsqc]
    exact hdet (by simp [ha0, hc0])
  have hsnonneg : 0 ≤ s := by
    dsimp [s]
    positivity
  have hnnonneg : 0 ≤ n := by
    dsimp [n]
    positivity
  have hsdiv_nonneg : 0 ≤ s / n := by
    exact div_nonneg hsnonneg hnnonneg
  have hcoeff20 : (d / det) * a + (-b / det) * c = 1 := by
    field_simp [det, hdet0]
    ring
  have hcoeff21 : (d / det) * b + (-b / det) * d = 0 := by
    field_simp [det, hdet0]
    ring
  have hcoeff30 : (-c / det) * a + (a / det) * c = 0 := by
    field_simp [det, hdet0]
    ring
  have hcoeff31 : (-c / det) * b + (a / det) * d = 1 := by
    field_simp [det, hdet0]
    ring
  have h2' : ∑ i : Fin 4, c2' i • u i = x0 * x1 := by
    calc
      ∑ i : Fin 4, c2' i • u i
          = (d / det) • (a • (x0 * x1 : Poly) + b • (x1 ^ 2 : Poly)) +
              (-b / det) • (c • (x0 * x1 : Poly) + d • (x1 ^ 2 : Poly)) := by
                simp [c2', det, relation_linearCombination, h2, h3]
      _ = ((d / det) * a + (-b / det) * c) • (x0 * x1 : Poly) +
            ((d / det) * b + (-b / det) * d) • (x1 ^ 2 : Poly) := by
              simp [smul_add, smul_smul, add_smul, add_assoc, add_left_comm, mul_comm]
      _ = x0 * x1 := by
            rw [hcoeff20, hcoeff21]
            simp
  have h3' : ∑ i : Fin 4, c3' i • u i = x1 ^ 2 := by
    calc
      ∑ i : Fin 4, c3' i • u i
          = (-c / det) • (a • (x0 * x1 : Poly) + b • (x1 ^ 2 : Poly)) +
              (a / det) • (c • (x0 * x1 : Poly) + d • (x1 ^ 2 : Poly)) := by
                simp [c3', det, relation_linearCombination, h2, h3]
      _ = ((-c / det) * a + (a / det) * c) • (x0 * x1 : Poly) +
            ((-c / det) * b + (a / det) * d) • (x1 ^ 2 : Poly) := by
              simp [smul_add, smul_smul, add_smul, add_assoc, add_left_comm, add_comm,
                mul_comm]
      _ = x1 ^ 2 := by
            rw [hcoeff30, hcoeff31]
            simp
  have hp40 : MvPolynomial.coeff m40 p = s := by
    rw [hpq, MvPolynomial.coeff_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact coeff_m40_sq_of_quadratic_eq (qs i) (hqdeg i)
  have hwker : InAdmissibleKer u w := by
    dsimp [w, t]
    exact rank14PlaneKerDet_inKer h2 h3
  have hw40 : MvPolynomial.coeff m40 (sigma w) = s := by
    change MvPolynomial.coeff m40 (sigma (rank14PlaneKerDet c2 c3 a b c d t)) = s
    calc
      MvPolynomial.coeff m40 (sigma (rank14PlaneKerDet c2 c3 a b c d t))
          = (a ^ 2 + c ^ 2) * t ^ 2 := by
              exact coeff_m40_sigma_rank14PlaneKerDet c2 c3 a b c d t h22 h33 h23
      _ = n * (s / n) := by
            dsimp [t, n]
            rw [Real.sq_sqrt hsdiv_nonneg]
      _ = s := by
            field_simp [n, hn]
  have hquartic_sub : IsQuartic (p - sigma w) := by
    calc
      (p - sigma w).totalDegree ≤ max p.totalDegree (sigma w).totalDegree := by
        exact MvPolynomial.totalDegree_sub _ _
      _ ≤ 4 := by
        exact max_le hpquartic (isQuartic_sigma_of_admissible hwker.1)
  have h40_sub : MvPolynomial.coeff m40 (p - sigma w) = 0 := by
    rw [MvPolynomial.coeff_sub, hp40, hw40]
    ring
  have himg : InAdmissibleImage u (p - sigma w) :=
    quartic_in_image_of_relations_const_x0_x0x1_x1sq h0 h1 h2' h3' hquartic_sub h40_sub
  refine admissible_image_plus_cone_residual_eq_zero (B := B)
    (u := u) (uImg := u)
    hu hsocp
    (imageOrthogonalResidual_self (B := B) hsocp.1) ?_
  refine ⟨p - sigma w, {w}, himg, ?_, ?_⟩
  · intro w' hw'
    have hw' : w' = w := by simpa using hw'
    subst hw'
    exact hwker
  · simp [w, sub_eq_add_neg]

/-- Any quartic with zero `x₁³` and `x₁⁴` coefficients lies in the image once
the factor admits explicit scalar relations for `1`, `x₀²`, and `x₀x₁`. This
abstracts the image part of the rank-13 mixed-affine representative proof. -/
theorem quartic_in_image_of_relations_const_x0sq_x0x1
    {u : RankFourVec}
    {c0 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 ^ 2)
    (h3 : ∑ i : Fin 4, c3 i • u i = x0 * x1)
    {p : Poly} (hp : IsQuartic p)
    (h03 : MvPolynomial.coeff m03 p = 0)
    (h04 : MvPolynomial.coeff m04 p = 0) :
    InAdmissibleImage u p := by
  classical
  let monomialImage : ∀ (s : Fin 2 →₀ ℕ) (a : ℝ),
      s.sum (fun _ e => e) ≤ 4 →
      s ≠ m03 →
      s ≠ m04 →
      InAdmissibleImage u (MvPolynomial.monomial s a) := by
    intro s a hdeg hne3 hne4
    let e0 := s 0
    let e1 := s 1
    have hsum : s.sum (fun _ e => e) = s 0 + s 1 := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
    have hs0 : s 0 + s 1 ≤ 4 := by
      simpa [hsum] using hdeg
    have hs : e0 + e1 ≤ 4 := by
      simpa [e0, e1] using hs0
    by_cases hsmall : e0 + e1 ≤ 2
    · simpa [monomial_fin2_eq, e0, e1, one_mul] using
        (inAdmissibleImage_of_relation_mul
          (u := u) (c := c0) (r := (1 : Poly))
          (q := (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1)
          h0 (isQuadratic_C_mul_pow_pow a e0 e1 hsmall))
    · by_cases hxy : 1 ≤ e0 ∧ 1 ≤ e1
      · rcases hxy with ⟨hx1, hy1⟩
        have hs2 : (e0 - 1) + (e1 - 1) ≤ 2 := by omega
        have himg :=
          inAdmissibleImage_of_relation_mul
            (u := u) (c := c3) (r := x0 * x1)
            (q := (MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1))
            h3 (isQuadratic_C_mul_pow_pow a (e0 - 1) (e1 - 1) hs2)
        rw [monomial_fin2_eq]
        simp [e0, e1] at himg ⊢
        have hxpow : x0 * x0 ^ (e0 - 1) = x0 ^ e0 := by
          simpa [Nat.sub_add_cancel hx1] using (pow_succ' x0 (e0 - 1)).symm
        have hypow : x1 * x1 ^ (e1 - 1) = x1 ^ e1 := by
          simpa [Nat.sub_add_cancel hy1] using (pow_succ' x1 (e1 - 1)).symm
        have hmul :
            (x0 * x1) * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1))
              = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
          calc
            (x0 * x1) * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1))
                = MvPolynomial.C a *
                    (x0 * x0 ^ (e0 - 1)) * (x1 * x1 ^ (e1 - 1)) := by
                        ring_nf
            _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                  simp [hxpow, hypow, mul_assoc]
        simpa [e0, e1, hmul] using himg
      · by_cases hx2 : 2 ≤ e0
        · have hs2 : (e0 - 2) + e1 ≤ 2 := by omega
          have himg :=
            inAdmissibleImage_of_relation_mul
              (u := u) (c := c2) (r := x0 ^ 2)
              (q := (MvPolynomial.C a * x0 ^ (e0 - 2)) * x1 ^ e1)
              h2 (isQuadratic_C_mul_pow_pow a (e0 - 2) e1 hs2)
          rw [monomial_fin2_eq]
          simp [e0, e1] at himg ⊢
          have hmul : x0 ^ 2 * ((MvPolynomial.C a * x0 ^ (e0 - 2)) * x1 ^ e1)
              = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
            calc
              x0 ^ 2 * ((MvPolynomial.C a * x0 ^ (e0 - 2)) * x1 ^ e1)
                  = MvPolynomial.C a * (x0 ^ 2 * x0 ^ (e0 - 2)) * x1 ^ e1 := by
                      ring_nf
              _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                    rw [← pow_add, Nat.add_sub_of_le hx2]
          simpa [e0, e1, hmul] using himg
        · have hx0 : e0 = 0 := by omega
          have hy34 : e1 = 3 ∨ e1 = 4 := by omega
          rcases hy34 with hy3 | hy4
          · exfalso
            apply hne3
            ext i
            fin_cases i <;> simp [m03, e0, e1, hx0, hy3]
          · exfalso
            apply hne4
            ext i
            fin_cases i <;> simp [m04, e0, e1, hx0, hy4]
  rw [← MvPolynomial.support_sum_monomial_coeff p]
  let P : Finset (Fin 2 →₀ ℕ) → Prop := fun S =>
    (∀ s ∈ S, s ∈ p.support) →
      InAdmissibleImage u (∑ s ∈ S, MvPolynomial.monomial s (MvPolynomial.coeff s p))
  have hP : P p.support := by
    refine Finset.induction_on p.support ?_ ?_
    · intro hsub
      simpa using inAdmissibleImage_zero u
    · intro s ss hsnot ih hsub
      rw [Finset.sum_insert hsnot]
      refine inAdmissibleImage_add u ?_ (ih ?_)
      · have hsdeg : s.sum (fun _ e => e) ≤ 4 :=
          (MvPolynomial.le_totalDegree (hsub s (by simp))).trans hp
        have hscoeff : MvPolynomial.coeff s p ≠ 0 :=
          MvPolynomial.mem_support_iff.mp (hsub s (by simp))
        have hsne3 : s ≠ m03 := by
          intro hs'
          apply hscoeff
          simpa [hs'] using h03
        have hsne4 : s ≠ m04 := by
          intro hs'
          apply hscoeff
          simpa [hs'] using h04
        exact monomialImage s (MvPolynomial.coeff s p) hsdeg hsne3 hsne4
      · intro t ht
        exact hsub t (by simp [ht])
  exact hP (fun s hs => hs)

private theorem totalDegree_mixedAffineRank13Line_le_local (b c : ℝ) :
    (mixedAffineRank13Line b c).totalDegree ≤ 1 := by
  unfold mixedAffineRank13Line
  calc
    (MvPolynomial.C b + MvPolynomial.C c * x1).totalDegree ≤
        max (MvPolynomial.C b).totalDegree ((MvPolynomial.C c * x1).totalDegree) := by
          exact MvPolynomial.totalDegree_add _ _
    _ ≤ 1 := by
      apply max_le
      · simp
      · calc
          (MvPolynomial.C c * x1).totalDegree ≤ (MvPolynomial.C c).totalDegree + x1.totalDegree := by
            exact MvPolynomial.totalDegree_mul _ _
          _ = 1 := by simp [x1]

private theorem isQuadratic_x1_mul_mixedAffineRank13Line_local (b c : ℝ) :
    IsQuadratic (x1 * mixedAffineRank13Line b c) := by
  have hx1 : x1.totalDegree ≤ 1 := by simp [x1]
  calc
    (x1 * mixedAffineRank13Line b c).totalDegree ≤
        x1.totalDegree + (mixedAffineRank13Line b c).totalDegree := by
          exact MvPolynomial.totalDegree_mul _ _
    _ ≤ 1 + 1 := by
          exact add_le_add hx1 (totalDegree_mixedAffineRank13Line_le_local b c)
    _ = 2 := by norm_num

private theorem isQuadratic_x0_mul_mixedAffineRank13Line_local (b c : ℝ) :
    IsQuadratic (x0 * mixedAffineRank13Line b c) := by
  have hx0 : x0.totalDegree ≤ 1 := by simp [x0]
  calc
    (x0 * mixedAffineRank13Line b c).totalDegree ≤
        x0.totalDegree + (mixedAffineRank13Line b c).totalDegree := by
          exact MvPolynomial.totalDegree_mul _ _
    _ ≤ 1 + 1 := by
          exact add_le_add hx0 (totalDegree_mixedAffineRank13Line_le_local b c)
    _ = 2 := by norm_num

private theorem coeff_m00_mixedAffineRank13Line_local (b c : ℝ) :
    MvPolynomial.coeff m00 (mixedAffineRank13Line b c) = b := by
  unfold mixedAffineRank13Line
  simp [m00, x1]

private theorem coeff_m01_mixedAffineRank13Line_local (b c : ℝ) :
    MvPolynomial.coeff m01 (mixedAffineRank13Line b c) = c := by
  unfold mixedAffineRank13Line
  rw [MvPolynomial.coeff_add]
  have hC : MvPolynomial.coeff m01 (MvPolynomial.C b : Poly) = 0 := by
    rw [MvPolynomial.coeff_C]
    split_ifs with h
    · exfalso
      have := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h.symm
      simp [m01] at this
    · rfl
  have hmul : MvPolynomial.coeff m01 (MvPolynomial.C c * x1 : Poly) = c := by
    rw [show x1 = MvPolynomial.monomial m01 (1 : ℝ) by
      simp [x1, m01, MvPolynomial.monomial_eq]]
    rw [MvPolynomial.coeff_mul_monomial']
    have hsub : m01 - m01 = m00 := by
      ext i
      fin_cases i <;> simp [m00, m01]
    rw [if_pos le_rfl, hsub]
    simp [m00]
  simp [hC, hmul]

private theorem coeff_m01_x1_mul_mixedAffineRank13Line_local (b c : ℝ) :
    MvPolynomial.coeff m01 (x1 * mixedAffineRank13Line b c) = b := by
  rw [show x1 = MvPolynomial.monomial m01 (1 : ℝ) by
    simp [x1, m01, MvPolynomial.monomial_eq]]
  rw [MvPolynomial.coeff_monomial_mul']
  have hsub : m01 - m01 = m00 := by
    ext i
    fin_cases i <;> simp [m00, m01]
  rw [if_pos le_rfl, hsub, coeff_m00_mixedAffineRank13Line_local]
  simp

private theorem coeff_m02_x1_mul_mixedAffineRank13Line_local (b c : ℝ) :
    MvPolynomial.coeff m02 (x1 * mixedAffineRank13Line b c) = c := by
  rw [show x1 = MvPolynomial.monomial m01 (1 : ℝ) by
    simp [x1, m01, MvPolynomial.monomial_eq]]
  rw [MvPolynomial.coeff_monomial_mul']
  have hmle : m01 ≤ m02 := by
    intro i
    fin_cases i <;> simp [m01, m02]
  have hsub : m02 - m01 = m01 := by
    ext i
    fin_cases i <;> simp [m01, m02]
  rw [if_pos hmle, hsub, coeff_m01_mixedAffineRank13Line_local]
  simp

private theorem coeff_m01_x0_mul_mixedAffineRank13Line_local (b c : ℝ) :
    MvPolynomial.coeff m01 (x0 * mixedAffineRank13Line b c) = 0 := by
  rw [show x0 = MvPolynomial.monomial m10 (1 : ℝ) by
    simp [x0, m10, MvPolynomial.monomial_eq]]
  rw [MvPolynomial.coeff_monomial_mul']
  have hnot : ¬ m10 ≤ m01 := by
    intro h
    have := h 0
    simp [m10, m01] at this
  rw [if_neg hnot]

private theorem coeff_m02_x0_mul_mixedAffineRank13Line_local (b c : ℝ) :
    MvPolynomial.coeff m02 (x0 * mixedAffineRank13Line b c) = 0 := by
  rw [show x0 = MvPolynomial.monomial m10 (1 : ℝ) by
    simp [x0, m10, MvPolynomial.monomial_eq]]
  rw [MvPolynomial.coeff_monomial_mul']
  have hnot : ¬ m10 ≤ m02 := by
    intro h
    have := h 0
    simp [m10, m02] at this
  rw [if_neg hnot]

private theorem isQuadratic_homLine_mul_mixedAffineRank13Line_local
    (a b beta gamma : ℝ) :
    IsQuadratic (homLine a b * mixedAffineRank13Line beta gamma) := by
  calc
    (homLine a b * mixedAffineRank13Line beta gamma).totalDegree ≤
        (homLine a b).totalDegree + (mixedAffineRank13Line beta gamma).totalDegree := by
          exact MvPolynomial.totalDegree_mul _ _
    _ ≤ 1 + 1 := by
          exact add_le_add (totalDegree_homLine_le a b)
            (totalDegree_mixedAffineRank13Line_le_local beta gamma)
    _ = 2 := by norm_num

private theorem coeff_m01_homLine_mul_mixedAffineRank13Line_local
    (a b beta gamma : ℝ) :
    MvPolynomial.coeff m01 (homLine a b * mixedAffineRank13Line beta gamma) = b * beta := by
  have hEq :
      (homLine a b * mixedAffineRank13Line beta gamma : Poly) =
        a • (x0 * mixedAffineRank13Line beta gamma) +
          b • (x1 * mixedAffineRank13Line beta gamma) := by
    unfold homLine
    calc
      ((MvPolynomial.C a * x0 + MvPolynomial.C b * x1) * mixedAffineRank13Line beta gamma : Poly)
          = (MvPolynomial.C a * x0) * mixedAffineRank13Line beta gamma +
              (MvPolynomial.C b * x1) * mixedAffineRank13Line beta gamma := by
                ring
      _ = MvPolynomial.C a * (x0 * mixedAffineRank13Line beta gamma) +
            MvPolynomial.C b * (x1 * mixedAffineRank13Line beta gamma) := by
              ring
      _ = a • (x0 * mixedAffineRank13Line beta gamma) +
            b • (x1 * mixedAffineRank13Line beta gamma) := by
              simp [MvPolynomial.smul_eq_C_mul]
  rw [hEq, MvPolynomial.coeff_add, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul,
    coeff_m01_x0_mul_mixedAffineRank13Line_local, coeff_m01_x1_mul_mixedAffineRank13Line_local]
  simp [smul_eq_mul]

private theorem coeff_m02_homLine_mul_mixedAffineRank13Line_local
    (a b beta gamma : ℝ) :
    MvPolynomial.coeff m02 (homLine a b * mixedAffineRank13Line beta gamma) = b * gamma := by
  have hEq :
      (homLine a b * mixedAffineRank13Line beta gamma : Poly) =
        a • (x0 * mixedAffineRank13Line beta gamma) +
          b • (x1 * mixedAffineRank13Line beta gamma) := by
    unfold homLine
    calc
      ((MvPolynomial.C a * x0 + MvPolynomial.C b * x1) * mixedAffineRank13Line beta gamma : Poly)
          = (MvPolynomial.C a * x0) * mixedAffineRank13Line beta gamma +
              (MvPolynomial.C b * x1) * mixedAffineRank13Line beta gamma := by
                ring
      _ = MvPolynomial.C a * (x0 * mixedAffineRank13Line beta gamma) +
            MvPolynomial.C b * (x1 * mixedAffineRank13Line beta gamma) := by
              ring
      _ = a • (x0 * mixedAffineRank13Line beta gamma) +
            b • (x1 * mixedAffineRank13Line beta gamma) := by
              simp [MvPolynomial.smul_eq_C_mul]
  rw [hEq, MvPolynomial.coeff_add, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul,
    coeff_m02_x0_mul_mixedAffineRank13Line_local, coeff_m02_x1_mul_mixedAffineRank13Line_local]
  simp [smul_eq_mul]

/-- Rank-13 kernel built from an arbitrary basis of `span(x₀²,x₀x₁)`. -/
private def rank13PlaneKerDet (c2 c3 : Fin 4 → ℝ)
    (a b c d beta gamma : ℝ) : RankFourVec :=
  relationDirection (-c2) (homLine c d * mixedAffineRank13Line beta gamma) +
    relationDirection c3 (homLine a b * mixedAffineRank13Line beta gamma)

private theorem rank13PlaneKerDet_admissible
    (c2 c3 : Fin 4 → ℝ) (a b c d beta gamma : ℝ) :
    IsAdmissibleDirection (rank13PlaneKerDet c2 c3 a b c d beta gamma) := by
  refine isAdmissibleDirection_add
    (relationDirection_admissible (-c2)
      (isQuadratic_homLine_mul_mixedAffineRank13Line_local c d beta gamma))
    (relationDirection_admissible c3
      (isQuadratic_homLine_mul_mixedAffineRank13Line_local a b beta gamma))

private theorem rank13PlaneKerDet_inKer
    {u : RankFourVec} {c2 c3 : Fin 4 → ℝ}
    {a b c d beta gamma : ℝ}
    (h2 : ∑ i : Fin 4, c2 i • u i = a • (x0 ^ 2 : Poly) + b • (x0 * x1 : Poly))
    (h3 : ∑ i : Fin 4, c3 i • u i = c • (x0 ^ 2 : Poly) + d • (x0 * x1 : Poly)) :
    InAdmissibleKer u (rank13PlaneKerDet c2 c3 a b c d beta gamma) := by
  refine ⟨rank13PlaneKerDet_admissible c2 c3 a b c d beta gamma, ?_⟩
  have hh2 : a • (x0 ^ 2 : Poly) + b • (x0 * x1 : Poly) = x0 * homLine a b := by
    unfold homLine
    calc
      (a • (x0 ^ 2 : Poly) + b • (x0 * x1 : Poly))
          = MvPolynomial.C a * (x0 ^ 2 : Poly) + MvPolynomial.C b * (x0 * x1 : Poly) := by
              simp [MvPolynomial.smul_eq_C_mul]
      _ = x0 * (MvPolynomial.C a * x0) + x0 * (MvPolynomial.C b * x1) := by
            ring
      _ = x0 * (MvPolynomial.C a * x0 + MvPolynomial.C b * x1) := by ring
  have hh3 : c • (x0 ^ 2 : Poly) + d • (x0 * x1 : Poly) = x0 * homLine c d := by
    unfold homLine
    calc
      (c • (x0 ^ 2 : Poly) + d • (x0 * x1 : Poly))
          = MvPolynomial.C c * (x0 ^ 2 : Poly) + MvPolynomial.C d * (x0 * x1 : Poly) := by
              simp [MvPolynomial.smul_eq_C_mul]
      _ = x0 * (MvPolynomial.C c * x0) + x0 * (MvPolynomial.C d * x1) := by
            ring
      _ = x0 * (MvPolynomial.C c * x0 + MvPolynomial.C d * x1) := by ring
  rw [rank13PlaneKerDet, A_add_right_local, A_relationDirection, A_relationDirection]
  simp [Pi.neg_apply, h2, h3, hh2, hh3, homLine, mixedAffineRank13Line, mul_assoc,
    mul_left_comm, mul_comm]

private theorem coeff_m03_sigma_rank13PlaneKerDet
    (c2 c3 : Fin 4 → ℝ) (a b c d beta gamma : ℝ)
    (h22 : ∑ i : Fin 4, (c2 i) ^ 2 = 1)
    (h33 : ∑ i : Fin 4, (c3 i) ^ 2 = 1)
    (h23 : ∑ i : Fin 4, c2 i * c3 i = 0) :
    MvPolynomial.coeff m03 (sigma (rank13PlaneKerDet c2 c3 a b c d beta gamma)) =
      (b ^ 2 + d ^ 2) * (2 * beta * gamma) := by
  rw [rank13PlaneKerDet, sigma_sub_add_relationDirections_of_orthonormal c2 c3
    (homLine c d * mixedAffineRank13Line beta gamma)
    (homLine a b * mixedAffineRank13Line beta gamma) h22 h33 h23]
  have h1 :
      MvPolynomial.coeff m03
          ((homLine c d * mixedAffineRank13Line beta gamma) ^ 2) =
        2 * (d * beta) * (d * gamma) := by
    rw [coeff_m03_sq_of_quadratic_eq _
      (isQuadratic_homLine_mul_mixedAffineRank13Line_local c d beta gamma)]
    rw [coeff_m01_homLine_mul_mixedAffineRank13Line_local,
      coeff_m02_homLine_mul_mixedAffineRank13Line_local]
  have h0 :
      MvPolynomial.coeff m03
          ((homLine a b * mixedAffineRank13Line beta gamma) ^ 2) =
        2 * (b * beta) * (b * gamma) := by
    rw [coeff_m03_sq_of_quadratic_eq _
      (isQuadratic_homLine_mul_mixedAffineRank13Line_local a b beta gamma)]
    rw [coeff_m01_homLine_mul_mixedAffineRank13Line_local,
      coeff_m02_homLine_mul_mixedAffineRank13Line_local]
  rw [MvPolynomial.coeff_add, h1, h0]
  ring

private theorem coeff_m04_sigma_rank13PlaneKerDet
    (c2 c3 : Fin 4 → ℝ) (a b c d beta gamma : ℝ)
    (h22 : ∑ i : Fin 4, (c2 i) ^ 2 = 1)
    (h33 : ∑ i : Fin 4, (c3 i) ^ 2 = 1)
    (h23 : ∑ i : Fin 4, c2 i * c3 i = 0) :
    MvPolynomial.coeff m04 (sigma (rank13PlaneKerDet c2 c3 a b c d beta gamma)) =
      (b ^ 2 + d ^ 2) * gamma ^ 2 := by
  rw [rank13PlaneKerDet, sigma_sub_add_relationDirections_of_orthonormal c2 c3
    (homLine c d * mixedAffineRank13Line beta gamma)
    (homLine a b * mixedAffineRank13Line beta gamma) h22 h33 h23]
  have h1 :
      MvPolynomial.coeff m04
          ((homLine c d * mixedAffineRank13Line beta gamma) ^ 2) =
        (d * gamma) ^ 2 := by
    rw [coeff_m04_sq_of_quadratic_eq _
      (isQuadratic_homLine_mul_mixedAffineRank13Line_local c d beta gamma)]
    rw [coeff_m02_homLine_mul_mixedAffineRank13Line_local]
  have h0 :
      MvPolynomial.coeff m04
          ((homLine a b * mixedAffineRank13Line beta gamma) ^ 2) =
        (b * gamma) ^ 2 := by
    rw [coeff_m04_sq_of_quadratic_eq _
      (isQuadratic_homLine_mul_mixedAffineRank13Line_local a b beta gamma)]
    rw [coeff_m02_homLine_mul_mixedAffineRank13Line_local]
  rw [MvPolynomial.coeff_add, h1, h0]
  ring

/-- The abstract rank-13 kernel built from relation data for `x₀²` and
`x₀x₁`. -/
private def rank13PlaneKer (c2 c3 : Fin 4 → ℝ) (b c : ℝ) : RankFourVec :=
  relationDirection (-c2) (x1 * mixedAffineRank13Line b c) +
    relationDirection c3 (x0 * mixedAffineRank13Line b c)

private theorem rank13PlaneKer_admissible (c2 c3 : Fin 4 → ℝ) (b c : ℝ) :
    IsAdmissibleDirection (rank13PlaneKer c2 c3 b c) := by
  refine isAdmissibleDirection_add
    (relationDirection_admissible (-c2) (isQuadratic_x1_mul_mixedAffineRank13Line_local b c))
    (relationDirection_admissible c3 (isQuadratic_x0_mul_mixedAffineRank13Line_local b c))

private theorem rank13PlaneKer_inKer
    {u : RankFourVec} {c2 c3 : Fin 4 → ℝ} {b c : ℝ}
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 ^ 2)
    (h3 : ∑ i : Fin 4, c3 i • u i = x0 * x1) :
    InAdmissibleKer u (rank13PlaneKer c2 c3 b c) := by
  refine ⟨rank13PlaneKer_admissible c2 c3 b c, ?_⟩
  rw [rank13PlaneKer, A_add_right_local, A_relationDirection, A_relationDirection]
  simp [Pi.neg_apply, h2, h3]
  ring_nf

private theorem coeff_m03_sigma_rank13PlaneKer
    (c2 c3 : Fin 4 → ℝ) (b c : ℝ)
    (h22 : ∑ i : Fin 4, (c2 i) ^ 2 = 1)
    (h33 : ∑ i : Fin 4, (c3 i) ^ 2 = 1)
    (h23 : ∑ i : Fin 4, c2 i * c3 i = 0) :
    MvPolynomial.coeff m03 (sigma (rank13PlaneKer c2 c3 b c)) = 2 * b * c := by
  rw [rank13PlaneKer, sigma_sub_add_relationDirections_of_orthonormal c2 c3
    (x1 * mixedAffineRank13Line b c) (x0 * mixedAffineRank13Line b c) h22 h33 h23]
  have h1 :
      MvPolynomial.coeff m03 ((x1 * mixedAffineRank13Line b c) ^ 2) = 2 * b * c := by
    rw [coeff_m03_sq_of_quadratic_eq _ (isQuadratic_x1_mul_mixedAffineRank13Line_local b c)]
    rw [coeff_m01_x1_mul_mixedAffineRank13Line_local, coeff_m02_x1_mul_mixedAffineRank13Line_local]
  have h0 :
      MvPolynomial.coeff m03 ((x0 * mixedAffineRank13Line b c) ^ 2) = 0 := by
    rw [coeff_m03_sq_of_quadratic_eq _ (isQuadratic_x0_mul_mixedAffineRank13Line_local b c)]
    rw [coeff_m01_x0_mul_mixedAffineRank13Line_local, coeff_m02_x0_mul_mixedAffineRank13Line_local]
    ring
  rw [MvPolynomial.coeff_add, h1, h0]
  ring

private theorem coeff_m04_sigma_rank13PlaneKer
    (c2 c3 : Fin 4 → ℝ) (b c : ℝ)
    (h22 : ∑ i : Fin 4, (c2 i) ^ 2 = 1)
    (h33 : ∑ i : Fin 4, (c3 i) ^ 2 = 1)
    (h23 : ∑ i : Fin 4, c2 i * c3 i = 0) :
    MvPolynomial.coeff m04 (sigma (rank13PlaneKer c2 c3 b c)) = c ^ 2 := by
  rw [rank13PlaneKer, sigma_sub_add_relationDirections_of_orthonormal c2 c3
    (x1 * mixedAffineRank13Line b c) (x0 * mixedAffineRank13Line b c) h22 h33 h23]
  have h1 :
      MvPolynomial.coeff m04 ((x1 * mixedAffineRank13Line b c) ^ 2) = c ^ 2 := by
    rw [coeff_m04_sq_of_quadratic_eq _ (isQuadratic_x1_mul_mixedAffineRank13Line_local b c)]
    rw [coeff_m02_x1_mul_mixedAffineRank13Line_local]
  have h0 :
      MvPolynomial.coeff m04 ((x0 * mixedAffineRank13Line b c) ^ 2) = 0 := by
    rw [coeff_m04_sq_of_quadratic_eq _ (isQuadratic_x0_mul_mixedAffineRank13Line_local b c)]
    rw [coeff_m02_x0_mul_mixedAffineRank13Line_local]
    ring
  rw [MvPolynomial.coeff_add, h1, h0]
  ring

private theorem coeff_m03_sigma_rank13PlaneKer_of_orthogonal
    (c2 c3 : Fin 4 → ℝ) (b c : ℝ)
    {r2 r3 : ℝ}
    (h22 : ∑ i : Fin 4, (c2 i) ^ 2 = r2)
    (h33 : ∑ i : Fin 4, (c3 i) ^ 2 = r3)
    (h23 : ∑ i : Fin 4, c2 i * c3 i = 0) :
    MvPolynomial.coeff m03 (sigma (rank13PlaneKer c2 c3 b c)) = r2 * (2 * b * c) := by
  rw [rank13PlaneKer, sigma_sub_add_relationDirections_of_orthogonal c2 c3
    (x1 * mixedAffineRank13Line b c) (x0 * mixedAffineRank13Line b c) h22 h33 h23]
  have h1 :
      MvPolynomial.coeff m03 ((x1 * mixedAffineRank13Line b c) ^ 2) = 2 * b * c := by
    rw [coeff_m03_sq_of_quadratic_eq _ (isQuadratic_x1_mul_mixedAffineRank13Line_local b c)]
    rw [coeff_m01_x1_mul_mixedAffineRank13Line_local, coeff_m02_x1_mul_mixedAffineRank13Line_local]
  have h0 :
      MvPolynomial.coeff m03 ((x0 * mixedAffineRank13Line b c) ^ 2) = 0 := by
    rw [coeff_m03_sq_of_quadratic_eq _ (isQuadratic_x0_mul_mixedAffineRank13Line_local b c)]
    rw [coeff_m01_x0_mul_mixedAffineRank13Line_local, coeff_m02_x0_mul_mixedAffineRank13Line_local]
    ring
  rw [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul, h1, h0]
  simp [smul_eq_mul]

private theorem coeff_m04_sigma_rank13PlaneKer_of_orthogonal
    (c2 c3 : Fin 4 → ℝ) (b c : ℝ)
    {r2 r3 : ℝ}
    (h22 : ∑ i : Fin 4, (c2 i) ^ 2 = r2)
    (h33 : ∑ i : Fin 4, (c3 i) ^ 2 = r3)
    (h23 : ∑ i : Fin 4, c2 i * c3 i = 0) :
    MvPolynomial.coeff m04 (sigma (rank13PlaneKer c2 c3 b c)) = r2 * c ^ 2 := by
  rw [rank13PlaneKer, sigma_sub_add_relationDirections_of_orthogonal c2 c3
    (x1 * mixedAffineRank13Line b c) (x0 * mixedAffineRank13Line b c) h22 h33 h23]
  have h1 :
      MvPolynomial.coeff m04 ((x1 * mixedAffineRank13Line b c) ^ 2) = c ^ 2 := by
    rw [coeff_m04_sq_of_quadratic_eq _ (isQuadratic_x1_mul_mixedAffineRank13Line_local b c)]
    rw [coeff_m02_x1_mul_mixedAffineRank13Line_local]
  have h0 :
      MvPolynomial.coeff m04 ((x0 * mixedAffineRank13Line b c) ^ 2) = 0 := by
    rw [coeff_m04_sq_of_quadratic_eq _ (isQuadratic_x0_mul_mixedAffineRank13Line_local b c)]
    rw [coeff_m02_x0_mul_mixedAffineRank13Line_local]
    ring
  rw [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul, h1, h0]
  simp [smul_eq_mul]

/-- Rank-13 mixed-affine certificate with orthogonal, not necessarily unit,
coefficient directions. -/
theorem residual_eq_zero_of_relations_const_x0sq_x0x1_of_orthogonal
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 ^ 2)
    (h3 : ∑ i : Fin 4, c3 i • u i = x0 * x1)
    {r2 r3 : ℝ}
    (h22 : ∑ i : Fin 4, (c2 i) ^ 2 = r2)
    (h33 : ∑ i : Fin 4, (c3 i) ^ 2 = r3)
    (h23 : ∑ i : Fin 4, c2 i * c3 i = 0)
    (hr2 : r2 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  rcases hp with ⟨hpquartic, k, qs, hqdeg, hpq⟩
  let s3 : ℝ := ∑ i : Fin k, MvPolynomial.coeff m01 (qs i) * MvPolynomial.coeff m02 (qs i)
  let s4 : ℝ := ∑ i : Fin k, (MvPolynomial.coeff m02 (qs i)) ^ 2
  let c : ℝ := Real.sqrt (s4 / r2)
  let b : ℝ := s3 / (r2 * c)
  let w : RankFourVec := rank13PlaneKer c2 c3 b c
  have hs4_nonneg : 0 ≤ s4 := by
    dsimp [s4]
    positivity
  have hr2_nonneg : 0 ≤ r2 := by
    rw [← h22]
    positivity
  have hr2_pos : 0 < r2 := lt_of_le_of_ne hr2_nonneg hr2.symm
  have hsdiv_nonneg : 0 ≤ s4 / r2 := by positivity
  have hp03 : MvPolynomial.coeff m03 p = 2 * s3 := by
    calc
      MvPolynomial.coeff m03 p = ∑ i : Fin k, MvPolynomial.coeff m03 ((qs i) ^ 2) := by
        rw [hpq, MvPolynomial.coeff_sum]
      _ = ∑ i : Fin k, 2 * MvPolynomial.coeff m01 (qs i) * MvPolynomial.coeff m02 (qs i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact coeff_m03_sq_of_quadratic_eq (qs i) (hqdeg i)
      _ = 2 * s3 := by
        dsimp [s3]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i hi
        ring
  have hp04 : MvPolynomial.coeff m04 p = s4 := by
    calc
      MvPolynomial.coeff m04 p = ∑ i : Fin k, MvPolynomial.coeff m04 ((qs i) ^ 2) := by
        rw [hpq, MvPolynomial.coeff_sum]
      _ = ∑ i : Fin k, (MvPolynomial.coeff m02 (qs i)) ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact coeff_m04_sq_of_quadratic_eq (qs i) (hqdeg i)
      _ = s4 := by
        rfl
  have hc_sq : c ^ 2 = s4 / r2 := by
    dsimp [c]
    rw [Real.sq_sqrt hsdiv_nonneg]
  have hs3_zero_of_c_zero (hc0 : c = 0) : s3 = 0 := by
    have hs4_zero : s4 = 0 := by
      have hdiv0 : s4 / r2 = 0 := by simpa [hc0] using hc_sq.symm
      exact ((div_eq_zero_iff).mp hdiv0).resolve_right hr2
    have htermzero :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => sq_nonneg (MvPolynomial.coeff m02 (qs i)))).mp hs4_zero
    dsimp [s3]
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hi0 : MvPolynomial.coeff m02 (qs i) = 0 := by
      exact sq_eq_zero_iff.mp (htermzero i (by simp))
    simp [hi0]
  have hwker : InAdmissibleKer u w := by
    dsimp [w]
    exact rank13PlaneKer_inKer h2 h3
  have hw03 : MvPolynomial.coeff m03 (sigma w) = 2 * s3 := by
    change MvPolynomial.coeff m03 (sigma (rank13PlaneKer c2 c3 b c)) = 2 * s3
    rw [coeff_m03_sigma_rank13PlaneKer_of_orthogonal c2 c3 b c h22 h33 h23]
    by_cases hc0 : c = 0
    · have hs3zero : s3 = 0 := hs3_zero_of_c_zero hc0
      simp [b, hc0, hs3zero]
    · dsimp [b]
      field_simp [hc0, hr2]
  have hw04 : MvPolynomial.coeff m04 (sigma w) = s4 := by
    change MvPolynomial.coeff m04 (sigma (rank13PlaneKer c2 c3 b c)) = s4
    rw [coeff_m04_sigma_rank13PlaneKer_of_orthogonal c2 c3 b c h22 h33 h23, hc_sq]
    field_simp [hr2]
  have hquartic_sub : IsQuartic (p - sigma w) := by
    calc
      (p - sigma w).totalDegree ≤ max p.totalDegree (sigma w).totalDegree := by
        exact MvPolynomial.totalDegree_sub _ _
      _ ≤ 4 := by
        exact max_le hpquartic (isQuartic_sigma_of_admissible hwker.1)
  have h03_sub : MvPolynomial.coeff m03 (p - sigma w) = 0 := by
    rw [MvPolynomial.coeff_sub, hp03, hw03]
    ring
  have h04_sub : MvPolynomial.coeff m04 (p - sigma w) = 0 := by
    rw [MvPolynomial.coeff_sub, hp04, hw04]
    ring
  have himg : InAdmissibleImage u (p - sigma w) :=
    quartic_in_image_of_relations_const_x0sq_x0x1 h0 h2 h3 hquartic_sub h03_sub h04_sub
  refine admissible_image_plus_cone_residual_eq_zero (B := B)
    (u := u) (uImg := u)
    hu hsocp
    (imageOrthogonalResidual_self (B := B) hsocp.1) ?_
  refine ⟨p - sigma w, {w}, himg, ?_, ?_⟩
  · intro w' hw'
    have hw' : w' = w := by simpa using hw'
    subst hw'
    exact hwker
  · simp [w, sub_eq_add_neg]

/-- Abstract rank-13 mixed-affine certificate: if a factor admits explicit
relations for `1`, `x₀²`, and `x₀x₁`, and the last two relation vectors are
orthonormal in coefficient space, every SOCP has zero residual. -/
theorem residual_eq_zero_of_relations_const_x0sq_x0x1
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 ^ 2)
    (h3 : ∑ i : Fin 4, c3 i • u i = x0 * x1)
    (h22 : ∑ i : Fin 4, (c2 i) ^ 2 = 1)
    (h33 : ∑ i : Fin 4, (c3 i) ^ 2 = 1)
    (h23 : ∑ i : Fin 4, c2 i * c3 i = 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  rcases hp with ⟨hpquartic, k, qs, hqdeg, hpq⟩
  let s3 : ℝ := ∑ i : Fin k, MvPolynomial.coeff m01 (qs i) * MvPolynomial.coeff m02 (qs i)
  let s4 : ℝ := ∑ i : Fin k, (MvPolynomial.coeff m02 (qs i)) ^ 2
  let c : ℝ := Real.sqrt s4
  let b : ℝ := s3 / c
  let w : RankFourVec := rank13PlaneKer c2 c3 b c
  have hs4_nonneg : 0 ≤ s4 := by
    dsimp [s4]
    positivity
  have hp03 : MvPolynomial.coeff m03 p = 2 * s3 := by
    calc
      MvPolynomial.coeff m03 p = ∑ i : Fin k, MvPolynomial.coeff m03 ((qs i) ^ 2) := by
        rw [hpq, MvPolynomial.coeff_sum]
      _ = ∑ i : Fin k, 2 * MvPolynomial.coeff m01 (qs i) * MvPolynomial.coeff m02 (qs i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact coeff_m03_sq_of_quadratic_eq (qs i) (hqdeg i)
      _ = 2 * s3 := by
        dsimp [s3]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i hi
        ring
  have hp04 : MvPolynomial.coeff m04 p = s4 := by
    calc
      MvPolynomial.coeff m04 p = ∑ i : Fin k, MvPolynomial.coeff m04 ((qs i) ^ 2) := by
        rw [hpq, MvPolynomial.coeff_sum]
      _ = ∑ i : Fin k, (MvPolynomial.coeff m02 (qs i)) ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact coeff_m04_sq_of_quadratic_eq (qs i) (hqdeg i)
      _ = s4 := by
        rfl
  have hc_sq : c ^ 2 = s4 := by
    dsimp [c]
    rw [Real.sq_sqrt hs4_nonneg]
  have hs3_zero_of_c_zero (hc0 : c = 0) : s3 = 0 := by
    have hs4_zero : s4 = 0 := by
      simpa [hc0] using hc_sq.symm
    have htermzero :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => sq_nonneg (MvPolynomial.coeff m02 (qs i)))).mp hs4_zero
    dsimp [s3]
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hi0 : MvPolynomial.coeff m02 (qs i) = 0 := by
      exact sq_eq_zero_iff.mp (htermzero i (by simp))
    simp [hi0]
  have hwker : InAdmissibleKer u w := by
    dsimp [w]
    exact rank13PlaneKer_inKer h2 h3
  have hw03 : MvPolynomial.coeff m03 (sigma w) = 2 * s3 := by
    change MvPolynomial.coeff m03 (sigma (rank13PlaneKer c2 c3 b c)) = 2 * s3
    rw [coeff_m03_sigma_rank13PlaneKer c2 c3 b c h22 h33 h23]
    by_cases hc0 : c = 0
    · have hs3zero : s3 = 0 := hs3_zero_of_c_zero hc0
      simp [b, hc0, hs3zero]
    · dsimp [b]
      field_simp [hc0]
  have hw04 : MvPolynomial.coeff m04 (sigma w) = s4 := by
    change MvPolynomial.coeff m04 (sigma (rank13PlaneKer c2 c3 b c)) = s4
    rw [coeff_m04_sigma_rank13PlaneKer c2 c3 b c h22 h33 h23, hc_sq]
  have hquartic_sub : IsQuartic (p - sigma w) := by
    calc
      (p - sigma w).totalDegree ≤ max p.totalDegree (sigma w).totalDegree := by
        exact MvPolynomial.totalDegree_sub _ _
      _ ≤ 4 := by
        exact max_le hpquartic (isQuartic_sigma_of_admissible hwker.1)
  have h03_sub : MvPolynomial.coeff m03 (p - sigma w) = 0 := by
    rw [MvPolynomial.coeff_sub, hp03, hw03]
    ring
  have h04_sub : MvPolynomial.coeff m04 (p - sigma w) = 0 := by
    rw [MvPolynomial.coeff_sub, hp04, hw04]
    ring
  have himg : InAdmissibleImage u (p - sigma w) :=
    quartic_in_image_of_relations_const_x0sq_x0x1 h0 h2 h3 hquartic_sub h03_sub h04_sub
  refine admissible_image_plus_cone_residual_eq_zero (B := B)
    (u := u) (uImg := u)
    hu hsocp
    (imageOrthogonalResidual_self (B := B) hsocp.1) ?_
  refine ⟨p - sigma w, {w}, himg, ?_, ?_⟩
  · intro w' hw'
    have hw' : w' = w := by simpa using hw'
    subst hw'
    exact hwker
  · simp [w, sub_eq_add_neg]

/-- Orthogonal change of basis inside `span(x₀², x₀x₁)` reduces to the exact
rank-13 mixed-affine plane theorem. -/
theorem residual_eq_zero_of_relations_const_x0Plane
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    {a b c d : ℝ}
    (h2 : ∑ i : Fin 4, c2 i • u i = a • (x0 ^ 2 : Poly) + b • (x0 * x1 : Poly))
    (h3 : ∑ i : Fin 4, c3 i • u i = c • (x0 ^ 2 : Poly) + d • (x0 * x1 : Poly))
    (h22 : ∑ i : Fin 4, (c2 i) ^ 2 = 1)
    (h33 : ∑ i : Fin 4, (c3 i) ^ 2 = 1)
    (h23 : ∑ i : Fin 4, c2 i * c3 i = 0)
    (hcol0 : a ^ 2 + c ^ 2 = 1)
    (hcol1 : b ^ 2 + d ^ 2 = 1)
    (hcol01 : a * b + c * d = 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let c2' : Fin 4 → ℝ := fun i => a * c2 i + c * c3 i
  let c3' : Fin 4 → ℝ := fun i => b * c2 i + d * c3 i
  have h2' : ∑ i : Fin 4, c2' i • u i = x0 ^ 2 := by
    calc
      ∑ i : Fin 4, c2' i • u i
          = a • (a • (x0 ^ 2 : Poly) + b • (x0 * x1 : Poly)) +
              c • (c • (x0 ^ 2 : Poly) + d • (x0 * x1 : Poly)) := by
                simp [c2', relation_linearCombination, h2, h3]
      _ = (a ^ 2 + c ^ 2) • (x0 ^ 2 : Poly) + (a * b + c * d) • (x0 * x1 : Poly) := by
            rw [add_smul, add_smul]
            simp [smul_add, smul_smul, pow_two, add_assoc, add_left_comm]
      _ = x0 ^ 2 := by simp [hcol0, hcol01]
  have h3' : ∑ i : Fin 4, c3' i • u i = x0 * x1 := by
    calc
      ∑ i : Fin 4, c3' i • u i
          = b • (a • (x0 ^ 2 : Poly) + b • (x0 * x1 : Poly)) +
              d • (c • (x0 ^ 2 : Poly) + d • (x0 * x1 : Poly)) := by
                simp [c3', relation_linearCombination, h2, h3]
      _ = (a * b + c * d) • (x0 ^ 2 : Poly) + (b ^ 2 + d ^ 2) • (x0 * x1 : Poly) := by
            rw [add_smul, add_smul]
            simp [smul_add, smul_smul, pow_two, add_assoc, add_left_comm, mul_comm]
      _ = x0 * x1 := by simp [hcol1, hcol01]
  have h22' : ∑ i : Fin 4, (c2' i) ^ 2 = 1 := by
    calc
      ∑ i : Fin 4, (c2' i) ^ 2
          = a ^ 2 * (∑ i : Fin 4, (c2 i) ^ 2) +
              (2 * a * c) * (∑ i : Fin 4, c2 i * c3 i) +
                c ^ 2 * (∑ i : Fin 4, (c3 i) ^ 2) := by
                  simpa [c2'] using sum_sq_linearCombination c2 c3 a c
      _ = 1 := by rw [h22, h23, h33]; nlinarith [hcol0]
  have h33' : ∑ i : Fin 4, (c3' i) ^ 2 = 1 := by
    calc
      ∑ i : Fin 4, (c3' i) ^ 2
          = b ^ 2 * (∑ i : Fin 4, (c2 i) ^ 2) +
              (2 * b * d) * (∑ i : Fin 4, c2 i * c3 i) +
                d ^ 2 * (∑ i : Fin 4, (c3 i) ^ 2) := by
                  simpa [c3'] using sum_sq_linearCombination c2 c3 b d
      _ = 1 := by rw [h22, h23, h33]; nlinarith [hcol1]
  have h23' : ∑ i : Fin 4, c2' i * c3' i = 0 := by
    calc
      ∑ i : Fin 4, c2' i * c3' i
          = (a * b) * (∑ i : Fin 4, (c2 i) ^ 2) +
              (a * d + c * b) * (∑ i : Fin 4, c2 i * c3 i) +
                (c * d) * (∑ i : Fin 4, (c3 i) ^ 2) := by
                  simpa [c2', c3'] using sum_mul_linearCombination c2 c3 a c b d
      _ = 0 := by rw [h22, h23, h33]; nlinarith [hcol01]
  exact residual_eq_zero_of_relations_const_x0sq_x0x1
    (B := B) (u := u) hu h0 h2' h3' h22' h33' h23' hp hsocp

/-- Rank-13 plane theorem with orthogonal but not necessarily unit column
coefficients in the canonical plane. -/
theorem residual_eq_zero_of_relations_const_x0Plane_scaled
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    {a b c d : ℝ}
    (h2 : ∑ i : Fin 4, c2 i • u i = a • (x0 ^ 2 : Poly) + b • (x0 * x1 : Poly))
    (h3 : ∑ i : Fin 4, c3 i • u i = c • (x0 ^ 2 : Poly) + d • (x0 * x1 : Poly))
    (h22 : ∑ i : Fin 4, (c2 i) ^ 2 = 1)
    (h33 : ∑ i : Fin 4, (c3 i) ^ 2 = 1)
    (h23 : ∑ i : Fin 4, c2 i * c3 i = 0)
    (hcol01 : a * b + c * d = 0)
    (hcol0nz : a ^ 2 + c ^ 2 ≠ 0)
    (hcol1nz : b ^ 2 + d ^ 2 ≠ 0) : 
    {p : Poly} → IsSOSQuartic p → IsSOCP B p u → residual p u = 0 := by
  intro p hp hsocp
  let n0 : ℝ := a ^ 2 + c ^ 2
  let n1 : ℝ := b ^ 2 + d ^ 2
  let c2' : Fin 4 → ℝ := fun i => (a / n0) * c2 i + (c / n0) * c3 i
  let c3' : Fin 4 → ℝ := fun i => (b / n1) * c2 i + (d / n1) * c3 i
  have hn0 : n0 ≠ 0 := by simpa [n0] using hcol0nz
  have hn1 : n1 ≠ 0 := by simpa [n1] using hcol1nz
  have h2' : ∑ i : Fin 4, c2' i • u i = x0 ^ 2 := by
    calc
      ∑ i : Fin 4, c2' i • u i
          = (a / n0) • (a • (x0 ^ 2 : Poly) + b • (x0 * x1 : Poly)) +
              (c / n0) • (c • (x0 ^ 2 : Poly) + d • (x0 * x1 : Poly)) := by
                simp [c2', n0, relation_linearCombination, h2, h3]
      _ = (a / n0) • (a • (x0 ^ 2 : Poly)) + (a / n0) • (b • (x0 * x1 : Poly)) +
            ((c / n0) • (c • (x0 ^ 2 : Poly)) + (c / n0) • (d • (x0 * x1 : Poly))) := by
              rw [smul_add, smul_add, add_assoc]
      _ = (((a / n0) * a + (c / n0) * c) • (x0 ^ 2 : Poly)) +
            (((a / n0) * b + (c / n0) * d) • (x0 * x1 : Poly)) := by
              rw [smul_smul, smul_smul, smul_smul, smul_smul]
              calc
                (a / n0 * a) • (x0 ^ 2 : Poly) + (a / n0 * b) • (x0 * x1 : Poly) +
                    ((c / n0 * c) • (x0 ^ 2 : Poly) + (c / n0 * d) • (x0 * x1 : Poly))
                    =
                    ((a / n0 * a) • (x0 ^ 2 : Poly) + (c / n0 * c) • (x0 ^ 2 : Poly)) +
                      ((a / n0 * b) • (x0 * x1 : Poly) + (c / n0 * d) • (x0 * x1 : Poly)) := by
                        abel_nf
                _ = (((a / n0) * a + (c / n0) * c) • (x0 ^ 2 : Poly)) +
                      (((a / n0) * b + (c / n0) * d) • (x0 * x1 : Poly)) := by
                        rw [← add_smul, ← add_smul]
      _ = ((a ^ 2 + c ^ 2) / n0) • (x0 ^ 2 : Poly) +
            ((a * b + c * d) / n0) • (x0 * x1 : Poly) := by
              have hs0 : (a / n0) * a + (c / n0) * c = (a ^ 2 + c ^ 2) / n0 := by
                field_simp [hn0]
              have hs1 : (a / n0) * b + (c / n0) * d = (a * b + c * d) / n0 := by
                field_simp [hn0]
              simp [hs0, hs1]
      _ = x0 ^ 2 := by
            rw [hcol01]
            simp [n0, hn0]
  have h3' : ∑ i : Fin 4, c3' i • u i = x0 * x1 := by
    calc
      ∑ i : Fin 4, c3' i • u i
          = (b / n1) • (a • (x0 ^ 2 : Poly) + b • (x0 * x1 : Poly)) +
              (d / n1) • (c • (x0 ^ 2 : Poly) + d • (x0 * x1 : Poly)) := by
                simp [c3', n1, relation_linearCombination, h2, h3]
      _ = (b / n1) • (a • (x0 ^ 2 : Poly)) + (b / n1) • (b • (x0 * x1 : Poly)) +
            ((d / n1) • (c • (x0 ^ 2 : Poly)) + (d / n1) • (d • (x0 * x1 : Poly))) := by
              rw [smul_add, smul_add, add_assoc]
      _ = (((b / n1) * a + (d / n1) * c) • (x0 ^ 2 : Poly)) +
            (((b / n1) * b + (d / n1) * d) • (x0 * x1 : Poly)) := by
              rw [smul_smul, smul_smul, smul_smul, smul_smul]
              calc
                (b / n1 * a) • (x0 ^ 2 : Poly) + (b / n1 * b) • (x0 * x1 : Poly) +
                    ((d / n1 * c) • (x0 ^ 2 : Poly) + (d / n1 * d) • (x0 * x1 : Poly))
                    =
                    ((b / n1 * a) • (x0 ^ 2 : Poly) + (d / n1 * c) • (x0 ^ 2 : Poly)) +
                      ((b / n1 * b) • (x0 * x1 : Poly) + (d / n1 * d) • (x0 * x1 : Poly)) := by
                        abel_nf
                _ = (((b / n1) * a + (d / n1) * c) • (x0 ^ 2 : Poly)) +
                      (((b / n1) * b + (d / n1) * d) • (x0 * x1 : Poly)) := by
                        rw [← add_smul, ← add_smul]
      _ = ((a * b + c * d) / n1) • (x0 ^ 2 : Poly) +
            ((b ^ 2 + d ^ 2) / n1) • (x0 * x1 : Poly) := by
              have hs0 : (b / n1) * a + (d / n1) * c = (a * b + c * d) / n1 := by
                field_simp [hn1]
              have hs1 : (b / n1) * b + (d / n1) * d = (b ^ 2 + d ^ 2) / n1 := by
                field_simp [hn1]
              simp [hs0, hs1]
      _ = x0 * x1 := by
            rw [hcol01]
            simp [n1, hn1]
  have h22' : ∑ i : Fin 4, (c2' i) ^ 2 = 1 / n0 := by
    calc
      ∑ i : Fin 4, (c2' i) ^ 2
          = (a / n0) ^ 2 * (∑ i : Fin 4, (c2 i) ^ 2) +
              (2 * (a / n0) * (c / n0)) * (∑ i : Fin 4, c2 i * c3 i) +
                (c / n0) ^ 2 * (∑ i : Fin 4, (c3 i) ^ 2) := by
                  simpa [c2'] using sum_sq_linearCombination c2 c3 (a / n0) (c / n0)
      _ = 1 / n0 := by
            rw [h22, h23, h33]
            field_simp [hn0]
            ring
  have h33' : ∑ i : Fin 4, (c3' i) ^ 2 = 1 / n1 := by
    calc
      ∑ i : Fin 4, (c3' i) ^ 2
          = (b / n1) ^ 2 * (∑ i : Fin 4, (c2 i) ^ 2) +
              (2 * (b / n1) * (d / n1)) * (∑ i : Fin 4, c2 i * c3 i) +
                (d / n1) ^ 2 * (∑ i : Fin 4, (c3 i) ^ 2) := by
                  simpa [c3'] using sum_sq_linearCombination c2 c3 (b / n1) (d / n1)
      _ = 1 / n1 := by
            rw [h22, h23, h33]
            field_simp [hn1]
            ring
  have h23' : ∑ i : Fin 4, c2' i * c3' i = 0 := by
    calc
      ∑ i : Fin 4, c2' i * c3' i
          = ((a / n0) * (b / n1)) * (∑ i : Fin 4, (c2 i) ^ 2) +
              ((a / n0) * (d / n1) + (c / n0) * (b / n1)) * (∑ i : Fin 4, c2 i * c3 i) +
                ((c / n0) * (d / n1)) * (∑ i : Fin 4, (c3 i) ^ 2) := by
                  simpa [c2', c3'] using
                    sum_mul_linearCombination c2 c3 (a / n0) (c / n0) (b / n1) (d / n1)
      _ = 0 := by
            rw [h22, h23, h33]
            field_simp [hn0, hn1]
            ring_nf
            nlinarith [hcol01]
  exact residual_eq_zero_of_relations_const_x0sq_x0x1_of_orthogonal
    (B := B) (u := u) hu h0 h2' h3' h22' h33' h23' (by simpa [n0] using one_div_ne_zero hn0) hp hsocp

/-- Rank-13 plane theorem with an arbitrary invertible basis of
`span(x₀²,x₀x₁)`. The kernel certificate works directly with determinant data,
so no polynomial-column orthogonality is required. -/
theorem residual_eq_zero_of_relations_const_x0Plane_det
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    {a b c d : ℝ}
    (h2 : ∑ i : Fin 4, c2 i • u i = a • (x0 ^ 2 : Poly) + b • (x0 * x1 : Poly))
    (h3 : ∑ i : Fin 4, c3 i • u i = c • (x0 ^ 2 : Poly) + d • (x0 * x1 : Poly))
    (h22 : ∑ i : Fin 4, (c2 i) ^ 2 = 1)
    (h33 : ∑ i : Fin 4, (c3 i) ^ 2 = 1)
    (h23 : ∑ i : Fin 4, c2 i * c3 i = 0)
    (hdet : a * d - b * c ≠ 0) :
    {p : Poly} → IsSOSQuartic p → IsSOCP B p u → residual p u = 0 := by
  intro p hp hsocp
  rcases hp with ⟨hpquartic, k, qs, hqdeg, hpq⟩
  let det : ℝ := a * d - b * c
  let n1 : ℝ := b ^ 2 + d ^ 2
  let c2' : Fin 4 → ℝ := fun i => (d / det) * c2 i + (-b / det) * c3 i
  let c3' : Fin 4 → ℝ := fun i => (-c / det) * c2 i + (a / det) * c3 i
  let s3 : ℝ := ∑ i : Fin k, MvPolynomial.coeff m01 (qs i) * MvPolynomial.coeff m02 (qs i)
  let s4 : ℝ := ∑ i : Fin k, (MvPolynomial.coeff m02 (qs i)) ^ 2
  let gamma : ℝ := Real.sqrt (s4 / n1)
  let beta : ℝ := s3 / (n1 * gamma)
  let w : RankFourVec := rank13PlaneKerDet c2 c3 a b c d beta gamma
  have hdet0 : det ≠ 0 := by
    simpa [det] using hdet
  have hn1 : n1 ≠ 0 := by
    intro hn10
    have hn10' : b ^ 2 + d ^ 2 = 0 := by
      simpa [n1] using hn10
    have hsqb : b ^ 2 = 0 := by
      nlinarith [sq_nonneg d, hn10']
    have hsqd : d ^ 2 = 0 := by
      nlinarith [sq_nonneg b, hn10']
    have hb0 : b = 0 := by
      nlinarith [sq_nonneg b, hsqb]
    have hd0 : d = 0 := by
      nlinarith [sq_nonneg d, hsqd]
    exact hdet (by simp [hb0, hd0])
  have hs4_nonneg : 0 ≤ s4 := by
    dsimp [s4]
    positivity
  have hn1_nonneg : 0 ≤ n1 := by
    dsimp [n1]
    positivity
  have hsdiv_nonneg : 0 ≤ s4 / n1 := by
    exact div_nonneg hs4_nonneg hn1_nonneg
  have hcoeff20 : (d / det) * a + (-b / det) * c = 1 := by
    field_simp [det, hdet0]
    ring
  have hcoeff21 : (d / det) * b + (-b / det) * d = 0 := by
    field_simp [det, hdet0]
    ring
  have hcoeff30 : (-c / det) * a + (a / det) * c = 0 := by
    field_simp [det, hdet0]
    ring
  have hcoeff31 : (-c / det) * b + (a / det) * d = 1 := by
    field_simp [det, hdet0]
    ring
  have h2' : ∑ i : Fin 4, c2' i • u i = x0 ^ 2 := by
    calc
      ∑ i : Fin 4, c2' i • u i
          = (d / det) • (a • (x0 ^ 2 : Poly) + b • (x0 * x1 : Poly)) +
              (-b / det) • (c • (x0 ^ 2 : Poly) + d • (x0 * x1 : Poly)) := by
                simp [c2', det, relation_linearCombination, h2, h3]
      _ = ((d / det) * a + (-b / det) * c) • (x0 ^ 2 : Poly) +
            ((d / det) * b + (-b / det) * d) • (x0 * x1 : Poly) := by
              simp [smul_add, smul_smul, add_smul, add_assoc, add_left_comm, mul_comm]
      _ = x0 ^ 2 := by
            rw [hcoeff20, hcoeff21]
            simp
  have h3' : ∑ i : Fin 4, c3' i • u i = x0 * x1 := by
    calc
      ∑ i : Fin 4, c3' i • u i
          = (-c / det) • (a • (x0 ^ 2 : Poly) + b • (x0 * x1 : Poly)) +
              (a / det) • (c • (x0 ^ 2 : Poly) + d • (x0 * x1 : Poly)) := by
                simp [c3', det, relation_linearCombination, h2, h3]
      _ = ((-c / det) * a + (a / det) * c) • (x0 ^ 2 : Poly) +
            ((-c / det) * b + (a / det) * d) • (x0 * x1 : Poly) := by
              simp [smul_add, smul_smul, add_smul, add_assoc, add_left_comm, add_comm,
                mul_comm]
      _ = x0 * x1 := by
            rw [hcoeff30, hcoeff31]
            simp
  have hp03 : MvPolynomial.coeff m03 p = 2 * s3 := by
    calc
      MvPolynomial.coeff m03 p = ∑ i : Fin k, MvPolynomial.coeff m03 ((qs i) ^ 2) := by
        rw [hpq, MvPolynomial.coeff_sum]
      _ = ∑ i : Fin k, 2 * MvPolynomial.coeff m01 (qs i) * MvPolynomial.coeff m02 (qs i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact coeff_m03_sq_of_quadratic_eq (qs i) (hqdeg i)
      _ = 2 * s3 := by
        dsimp [s3]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i hi
        ring
  have hp04 : MvPolynomial.coeff m04 p = s4 := by
    calc
      MvPolynomial.coeff m04 p = ∑ i : Fin k, MvPolynomial.coeff m04 ((qs i) ^ 2) := by
        rw [hpq, MvPolynomial.coeff_sum]
      _ = ∑ i : Fin k, (MvPolynomial.coeff m02 (qs i)) ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact coeff_m04_sq_of_quadratic_eq (qs i) (hqdeg i)
      _ = s4 := by
        rfl
  have hgamma_sq : gamma ^ 2 = s4 / n1 := by
    dsimp [gamma]
    rw [Real.sq_sqrt hsdiv_nonneg]
  have hs3_zero_of_gamma_zero (hgamma0 : gamma = 0) : s3 = 0 := by
    have hs4_zero : s4 = 0 := by
      have hdiv0 : s4 / n1 = 0 := by simpa [hgamma0] using hgamma_sq.symm
      exact ((div_eq_zero_iff).mp hdiv0).resolve_right hn1
    have htermzero :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => sq_nonneg (MvPolynomial.coeff m02 (qs i)))).mp hs4_zero
    dsimp [s3]
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hi0 : MvPolynomial.coeff m02 (qs i) = 0 := by
      exact sq_eq_zero_iff.mp (htermzero i (by simp))
    simp [hi0]
  have hwker : InAdmissibleKer u w := by
    dsimp [w]
    exact rank13PlaneKerDet_inKer h2 h3
  have hw03 : MvPolynomial.coeff m03 (sigma w) = 2 * s3 := by
    change MvPolynomial.coeff m03 (sigma (rank13PlaneKerDet c2 c3 a b c d beta gamma)) = 2 * s3
    rw [coeff_m03_sigma_rank13PlaneKerDet c2 c3 a b c d beta gamma h22 h33 h23]
    by_cases hgamma0 : gamma = 0
    · have hs3zero : s3 = 0 := hs3_zero_of_gamma_zero hgamma0
      simp [beta, hgamma0, hs3zero]
    · dsimp [beta]
      field_simp [hgamma0, hn1]
      simp [n1, mul_comm]
  have hw04 : MvPolynomial.coeff m04 (sigma w) = s4 := by
    change MvPolynomial.coeff m04 (sigma (rank13PlaneKerDet c2 c3 a b c d beta gamma)) = s4
    rw [coeff_m04_sigma_rank13PlaneKerDet c2 c3 a b c d beta gamma h22 h33 h23, hgamma_sq]
    field_simp [hn1]
    simp [n1, mul_comm]
  have hquartic_sub : IsQuartic (p - sigma w) := by
    calc
      (p - sigma w).totalDegree ≤ max p.totalDegree (sigma w).totalDegree := by
        exact MvPolynomial.totalDegree_sub _ _
      _ ≤ 4 := by
        exact max_le hpquartic (isQuartic_sigma_of_admissible hwker.1)
  have h03_sub : MvPolynomial.coeff m03 (p - sigma w) = 0 := by
    rw [MvPolynomial.coeff_sub, hp03, hw03]
    ring
  have h04_sub : MvPolynomial.coeff m04 (p - sigma w) = 0 := by
    rw [MvPolynomial.coeff_sub, hp04, hw04]
    ring
  have himg : InAdmissibleImage u (p - sigma w) :=
    quartic_in_image_of_relations_const_x0sq_x0x1 h0 h2' h3' hquartic_sub h03_sub h04_sub
  refine admissible_image_plus_cone_residual_eq_zero (B := B)
    (u := u) (uImg := u)
    hu hsocp
    (imageOrthogonalResidual_self (B := B) hsocp.1) ?_
  refine ⟨p - sigma w, {w}, himg, ?_, ?_⟩
  · intro w' hw'
    have hw' : w' = w := by simpa using hw'
    subst hw'
    exact hwker
  · simp [w, sub_eq_add_neg]

/-- Transport the strengthened rank-14 mixed-affine plane certificate across
an algebra equivalence. This is the affine-normalization wrapper needed later:
it is enough to produce the orthogonal in-plane relation data after
normalizing the variables. -/
theorem residual_eq_zero_of_equiv_relations_const_x0_x1Plane
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x0)
    {a b c d : ℝ}
    (h2 :
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i =
        a • (x0 * x1 : Poly) + b • (x1 ^ 2 : Poly))
    (h3 :
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i =
        c • (x0 * x1 : Poly) + d • (x1 ^ 2 : Poly))
    (h22 : ∑ i : Fin 4, (c2 i) ^ 2 = 1)
    (h33 : ∑ i : Fin 4, (c3 i) ^ 2 = 1)
    (h23 : ∑ i : Fin 4, c2 i * c3 i = 0)
    (hcol0 : a ^ 2 + c ^ 2 = 1)
    (hcol1 : b ^ 2 + d ^ 2 = 1)
    (hcol01 : a * b + c * d = 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_x1Plane
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0 h1 h2 h3 h22 h33 h23 hcol0 hcol1 hcol01
      hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

/-- Transport the scaled rank-14 mixed-affine plane certificate across
an algebra equivalence. This lets the affine-normalization step feed
non-unit orthogonal plane data directly to the mixed-affine theorem. -/
theorem residual_eq_zero_of_equiv_relations_const_x0_x1Plane_scaled
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x0)
    {a b c d : ℝ}
    (h2 :
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i =
        a • (x0 * x1 : Poly) + b • (x1 ^ 2 : Poly))
    (h3 :
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i =
        c • (x0 * x1 : Poly) + d • (x1 ^ 2 : Poly))
    (h22 : ∑ i : Fin 4, (c2 i) ^ 2 = 1)
    (h33 : ∑ i : Fin 4, (c3 i) ^ 2 = 1)
    (h23 : ∑ i : Fin 4, c2 i * c3 i = 0)
    (hcol01 : a * b + c * d = 0)
    (hcol0nz : a ^ 2 + c ^ 2 ≠ 0)
    (hcol1nz : b ^ 2 + d ^ 2 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_x1Plane_scaled
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0 h1 h2 h3 h22 h33 h23 hcol01 hcol0nz hcol1nz
      hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

/-- Transport the determinant-based rank-14 mixed-affine plane certificate
across an algebra equivalence. -/
theorem residual_eq_zero_of_equiv_relations_const_x0_x1Plane_det
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x0)
    {a b c d : ℝ}
    (h2 :
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i =
        a • (x0 * x1 : Poly) + b • (x1 ^ 2 : Poly))
    (h3 :
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i =
        c • (x0 * x1 : Poly) + d • (x1 ^ 2 : Poly))
    (h22 : ∑ i : Fin 4, (c2 i) ^ 2 = 1)
    (h33 : ∑ i : Fin 4, (c3 i) ^ 2 = 1)
    (h23 : ∑ i : Fin 4, c2 i * c3 i = 0)
    (hdet : a * d - b * c ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_x1Plane_det
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0 h1 h2 h3 h22 h33 h23 hdet hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

/-- Transport the strengthened rank-13 mixed-affine plane certificate across
an algebra equivalence. -/
theorem residual_eq_zero_of_equiv_relations_const_x0Plane
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly))
    {a b c d : ℝ}
    (h2 :
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i =
        a • (x0 ^ 2 : Poly) + b • (x0 * x1 : Poly))
    (h3 :
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i =
        c • (x0 ^ 2 : Poly) + d • (x0 * x1 : Poly))
    (h22 : ∑ i : Fin 4, (c2 i) ^ 2 = 1)
    (h33 : ∑ i : Fin 4, (c3 i) ^ 2 = 1)
    (h23 : ∑ i : Fin 4, c2 i * c3 i = 0)
    (hcol0 : a ^ 2 + c ^ 2 = 1)
    (hcol1 : b ^ 2 + d ^ 2 = 1)
    (hcol01 : a * b + c * d = 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0Plane
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0 h2 h3 h22 h33 h23 hcol0 hcol1 hcol01
      hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

/-- Transport the scaled rank-13 mixed-affine plane certificate across
an algebra equivalence. -/
theorem residual_eq_zero_of_equiv_relations_const_x0Plane_scaled
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly))
    {a b c d : ℝ}
    (h2 :
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i =
        a • (x0 ^ 2 : Poly) + b • (x0 * x1 : Poly))
    (h3 :
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i =
        c • (x0 ^ 2 : Poly) + d • (x0 * x1 : Poly))
    (h22 : ∑ i : Fin 4, (c2 i) ^ 2 = 1)
    (h33 : ∑ i : Fin 4, (c3 i) ^ 2 = 1)
    (h23 : ∑ i : Fin 4, c2 i * c3 i = 0)
    (hcol01 : a * b + c * d = 0)
    (hcol0nz : a ^ 2 + c ^ 2 ≠ 0)
    (hcol1nz : b ^ 2 + d ^ 2 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0Plane_scaled
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0 h2 h3 h22 h33 h23 hcol01 hcol0nz hcol1nz
      hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

/-- Transport the determinant-based rank-13 mixed-affine plane certificate
across an algebra equivalence. -/
theorem residual_eq_zero_of_equiv_relations_const_x0Plane_det
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly))
    {a b c d : ℝ}
    (h2 :
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i =
        a • (x0 ^ 2 : Poly) + b • (x0 * x1 : Poly))
    (h3 :
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i =
        c • (x0 ^ 2 : Poly) + d • (x0 * x1 : Poly))
    (h22 : ∑ i : Fin 4, (c2 i) ^ 2 = 1)
    (h33 : ∑ i : Fin 4, (c3 i) ^ 2 = 1)
    (h23 : ∑ i : Fin 4, c2 i * c3 i = 0)
    (hdet : a * d - b * c ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0Plane_det
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0 h2 h3 h22 h33 h23 hdet hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_const_x0_homQuadratics_coeff_m11_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq2_11 : MvPolynomial.coeff m11 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 = 0)
    (hq3_11 : MvPolynomial.coeff m11 q3 = 0)
    (hdet :
      MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have h2' :
      ∑ i : Fin 4, c2 i • u i =
        MvPolynomial.coeff m20 q2 • (x0 ^ 2 : Poly) +
          MvPolynomial.coeff m02 q2 • (x1 ^ 2 : Poly) := by
    calc
      ∑ i : Fin 4, c2 i • u i = q2 := h2
      _ =
          MvPolynomial.coeff m20 q2 • (x0 ^ 2 : Poly) +
            MvPolynomial.coeff m02 q2 • (x1 ^ 2 : Poly) := by
              simpa using
                homogeneousQuadratic_eq_x0sq_x1sq_of_coeff_m11_zero
                  hq2 hq2_00 hq2_10 hq2_01 hq2_11
  have h3' :
      ∑ i : Fin 4, c3 i • u i =
        MvPolynomial.coeff m20 q3 • (x0 ^ 2 : Poly) +
          MvPolynomial.coeff m02 q3 • (x1 ^ 2 : Poly) := by
    calc
      ∑ i : Fin 4, c3 i • u i = q3 := h3
      _ =
          MvPolynomial.coeff m20 q3 • (x0 ^ 2 : Poly) +
            MvPolynomial.coeff m02 q3 • (x1 ^ 2 : Poly) := by
              simpa using
                homogeneousQuadratic_eq_x0sq_x1sq_of_coeff_m11_zero
                  hq3 hq3_00 hq3_10 hq3_01 hq3_11
  exact residual_eq_zero_of_relations_const_x0sq_x1sqPlane
    (B := B) (u := u) hu h0 h2' h3' hdet hp hsocp

theorem residual_eq_zero_of_relations_const_x0_homQuadratics_diag_diff_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq2_diag : MvPolynomial.coeff m20 q2 - MvPolynomial.coeff m02 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 = 0)
    (hq3_diag : MvPolynomial.coeff m20 q3 - MvPolynomial.coeff m02 q3 = 0)
    (hdet :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m20 q3 -
        MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m11 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have h2' :
      ∑ i : Fin 4, c2 i • u i =
        MvPolynomial.coeff m11 q2 • (x0 * x1 : Poly) +
          MvPolynomial.coeff m20 q2 • (x0 ^ 2 + x1 ^ 2 : Poly) := by
    calc
      ∑ i : Fin 4, c2 i • u i = q2 := h2
      _ =
          MvPolynomial.coeff m11 q2 • (x0 * x1 : Poly) +
            MvPolynomial.coeff m20 q2 • (x0 ^ 2 + x1 ^ 2 : Poly) := by
              simpa using
                homogeneousQuadratic_eq_x0x1_sumsq_of_diag_diff_zero
                  hq2 hq2_00 hq2_10 hq2_01 hq2_diag
  have h3' :
      ∑ i : Fin 4, c3 i • u i =
        MvPolynomial.coeff m11 q3 • (x0 * x1 : Poly) +
          MvPolynomial.coeff m20 q3 • (x0 ^ 2 + x1 ^ 2 : Poly) := by
    calc
      ∑ i : Fin 4, c3 i • u i = q3 := h3
      _ =
          MvPolynomial.coeff m11 q3 • (x0 * x1 : Poly) +
            MvPolynomial.coeff m20 q3 • (x0 ^ 2 + x1 ^ 2 : Poly) := by
              simpa using
                homogeneousQuadratic_eq_x0x1_sumsq_of_diag_diff_zero
                  hq3 hq3_00 hq3_10 hq3_01 hq3_diag
  exact residual_eq_zero_of_relations_const_x0x1_sumsqPlane
    (B := B) (u := u) hu h0 h2' h3' hdet hp hsocp

theorem residual_eq_zero_of_relations_const_x0_homQuadratics_diag_sum_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq2_diag : MvPolynomial.coeff m20 q2 + MvPolynomial.coeff m02 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 = 0)
    (hq3_diag : MvPolynomial.coeff m20 q3 + MvPolynomial.coeff m02 q3 = 0)
    (hdet :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m20 q3 -
        MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m11 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have h2' :
      ∑ i : Fin 4, c2 i • u i =
        MvPolynomial.coeff m11 q2 • (x0 * x1 : Poly) +
          MvPolynomial.coeff m20 q2 • (x0 ^ 2 - x1 ^ 2 : Poly) := by
    calc
      ∑ i : Fin 4, c2 i • u i = q2 := h2
      _ =
          MvPolynomial.coeff m11 q2 • (x0 * x1 : Poly) +
            MvPolynomial.coeff m20 q2 • (x0 ^ 2 - x1 ^ 2 : Poly) := by
              simpa using
                homogeneousQuadratic_eq_x0x1_diffsq_of_diag_sum_zero
                  hq2 hq2_00 hq2_10 hq2_01 hq2_diag
  have h3' :
      ∑ i : Fin 4, c3 i • u i =
        MvPolynomial.coeff m11 q3 • (x0 * x1 : Poly) +
          MvPolynomial.coeff m20 q3 • (x0 ^ 2 - x1 ^ 2 : Poly) := by
    calc
      ∑ i : Fin 4, c3 i • u i = q3 := h3
      _ =
          MvPolynomial.coeff m11 q3 • (x0 * x1 : Poly) +
            MvPolynomial.coeff m20 q3 • (x0 ^ 2 - x1 ^ 2 : Poly) := by
              simpa using
                homogeneousQuadratic_eq_x0x1_diffsq_of_diag_sum_zero
                  hq3 hq3_00 hq3_10 hq3_01 hq3_diag
  exact residual_eq_zero_of_relations_const_x0x1_diffsqPlane
    (B := B) (u := u) hu h0 h2' h3' hdet hp hsocp

theorem residual_eq_zero_of_relations_const_x0_homQuadratics_coeff_m20_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq2_20 : MvPolynomial.coeff m20 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 = 0)
    (hq3_20 : MvPolynomial.coeff m20 q3 = 0)
    (h22 : ∑ i : Fin 4, (c2 i) ^ 2 = 1)
    (h33 : ∑ i : Fin 4, (c3 i) ^ 2 = 1)
    (h23 : ∑ i : Fin 4, c2 i * c3 i = 0)
    (hdet :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have h2' :
      ∑ i : Fin 4, c2 i • u i =
        MvPolynomial.coeff m11 q2 • (x0 * x1 : Poly) +
          MvPolynomial.coeff m02 q2 • (x1 ^ 2 : Poly) := by
    calc
      ∑ i : Fin 4, c2 i • u i = q2 := h2
      _ =
          MvPolynomial.coeff m11 q2 • (x0 * x1 : Poly) +
            MvPolynomial.coeff m02 q2 • (x1 ^ 2 : Poly) := by
              simpa using
                homogeneousQuadratic_eq_x0x1_x1sq_of_coeff_m20_zero
                  hq2 hq2_00 hq2_10 hq2_01 hq2_20
  have h3' :
      ∑ i : Fin 4, c3 i • u i =
        MvPolynomial.coeff m11 q3 • (x0 * x1 : Poly) +
          MvPolynomial.coeff m02 q3 • (x1 ^ 2 : Poly) := by
    calc
      ∑ i : Fin 4, c3 i • u i = q3 := h3
      _ =
          MvPolynomial.coeff m11 q3 • (x0 * x1 : Poly) +
            MvPolynomial.coeff m02 q3 • (x1 ^ 2 : Poly) := by
              simpa using
                homogeneousQuadratic_eq_x0x1_x1sq_of_coeff_m20_zero
                  hq3 hq3_00 hq3_10 hq3_01 hq3_20
  exact residual_eq_zero_of_relations_const_x0_x1Plane_det
    (B := B) (u := u) hu h0 h1 h2' h3' h22 h33 h23 hdet hp hsocp

theorem residual_eq_zero_of_relations_const_x0_homQuadratics_coeff_m20_zero_gram
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq2_20 : MvPolynomial.coeff m20 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 = 0)
    (hq3_20 : MvPolynomial.coeff m20 q3 = 0)
    (hgram :
      (∑ i : Fin 4, (c2 i) ^ 2) * (∑ i : Fin 4, (c3 i) ^ 2) -
        (∑ i : Fin 4, c2 i * c3 i) ^ 2 ≠ 0)
    (hdet :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let n2 : ℝ := ∑ i : Fin 4, (c2 i) ^ 2
  let n3 : ℝ := ∑ i : Fin 4, (c3 i) ^ 2
  let m23 : ℝ := ∑ i : Fin 4, c2 i * c3 i
  let g : ℝ := n2 * n3 - m23 ^ 2
  have hg : g ≠ 0 := by
    simpa [g, n2, n3, m23] using hgram
  have hn2_nonneg : 0 ≤ n2 := by
    dsimp [n2]
    positivity
  have hn2 : n2 ≠ 0 := by
    intro hn20
    have hc20 : ∀ i : Fin 4, c2 i = 0 := by
      intro i
      exact eq_zero_of_sum_sq_eq_zero (by simpa [n2] using hn20) i
    have hm23 : m23 = 0 := by
      dsimp [m23]
      refine Finset.sum_eq_zero ?_
      intro i hi
      simp [hc20 i]
    have : g = 0 := by
      simp [g, n2, hn20, hm23]
    exact hg this
  let o3 : ℝ := g / n2
  let s2 : ℝ := Real.sqrt n2
  let s3 : ℝ := Real.sqrt o3
  let c2' : Fin 4 → ℝ := fun i => (1 / s2) * c2 i
  let c3' : Fin 4 → ℝ := fun i => (((-m23 / n2) / s3) * c2 i) + ((1 / s3) * c3 i)
  let q2' : Poly := (1 / s2) • q2
  let q3' : Poly := (((-m23 / n2) / s3) • q2) + ((1 / s3) • q3)
  have ho3_formula : o3 = n3 - m23 ^ 2 / n2 := by
    dsimp [o3, g]
    field_simp [hn2]
  have ho3_eq :
      ∑ i : Fin 4, ((-m23 / n2) * c2 i + c3 i) ^ 2 = o3 := by
    calc
      ∑ i : Fin 4, ((-m23 / n2) * c2 i + c3 i) ^ 2
          = (-m23 / n2) ^ 2 * (∑ i : Fin 4, (c2 i) ^ 2) +
              (2 * (-m23 / n2) * 1) * (∑ i : Fin 4, c2 i * c3 i) +
                1 ^ 2 * (∑ i : Fin 4, (c3 i) ^ 2) := by
                  simpa using sum_sq_linearCombination c2 c3 (-m23 / n2) 1
      _ = n3 - m23 ^ 2 / n2 := by
            dsimp [n2, n3, m23]
            field_simp [hn2]
            ring
      _ = o3 := by exact ho3_formula.symm
  have ho3_nonneg : 0 ≤ o3 := by
    have hs : 0 ≤ ∑ i : Fin 4, ((-m23 / n2) * c2 i + c3 i) ^ 2 := by
      positivity
    simpa [ho3_eq] using hs
  have ho3 : o3 ≠ 0 := by
    intro ho30
    have hg0 : g = 0 := by
      have hdiv0 : g / n2 = 0 := by simpa [o3] using ho30
      exact ((div_eq_zero_iff).mp hdiv0).resolve_right hn2
    exact hg hg0
  have hs2 : s2 ≠ 0 := by
    exact Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne hn2_nonneg hn2.symm)
  have hs3 : s3 ≠ 0 := by
    exact Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne ho3_nonneg ho3.symm)
  have h2' :
      ∑ i : Fin 4, c2' i • u i = q2' := by
    calc
      ∑ i : Fin 4, c2' i • u i = (1 / s2) • (∑ i : Fin 4, c2 i • u i) := by
        simp [c2', Finset.smul_sum, smul_smul]
      _ = q2' := by
        rw [h2]
  have h3' :
      ∑ i : Fin 4, c3' i • u i = q3' := by
    calc
      ∑ i : Fin 4, c3' i • u i
          = ((-m23 / n2) / s3) • (∑ i : Fin 4, c2 i • u i) +
              (1 / s3) • (∑ i : Fin 4, c3 i • u i) := by
                simp [c3', Finset.sum_add_distrib, Finset.smul_sum, add_smul, smul_smul]
      _ = q3' := by
        rw [h2, h3]
  have hq2' : IsQuadratic q2' := by
    exact isQuadratic_smul_local (1 / s2) hq2
  have hq3' : IsQuadratic q3' := by
    exact isQuadratic_linearCombination_local hq2 hq3 (((-m23 / n2) / s3)) (1 / s3)
  have hq2_00' : MvPolynomial.coeff m00 q2' = 0 := by
    simp [q2', hq2_00]
  have hq2_10' : MvPolynomial.coeff m10 q2' = 0 := by
    simp [q2', hq2_10]
  have hq2_01' : MvPolynomial.coeff m01 q2' = 0 := by
    simp [q2', hq2_01]
  have hq2_20' : MvPolynomial.coeff m20 q2' = 0 := by
    simp [q2', hq2_20]
  have hq3_00' : MvPolynomial.coeff m00 q3' = 0 := by
    simp [q3', hq2_00, hq3_00]
  have hq3_10' : MvPolynomial.coeff m10 q3' = 0 := by
    simp [q3', hq2_10, hq3_10]
  have hq3_01' : MvPolynomial.coeff m01 q3' = 0 := by
    simp [q3', hq2_01, hq3_01]
  have hq3_20' : MvPolynomial.coeff m20 q3' = 0 := by
    simp [q3', hq2_20, hq3_20]
  have h22' : ∑ i : Fin 4, (c2' i) ^ 2 = 1 := by
    let z : Fin 4 → ℝ := fun _ => 0
    have hs2sq : s2 ^ 2 = n2 := by
      dsimp [s2]
      rw [Real.sq_sqrt hn2_nonneg]
    calc
      ∑ i : Fin 4, (c2' i) ^ 2
          = (1 / s2) ^ 2 * (∑ i : Fin 4, (c2 i) ^ 2) := by
              simpa [c2', z] using sum_sq_linearCombination c2 z (1 / s2) 0
      _ = (1 / s2) ^ 2 * s2 ^ 2 := by
            rw [show ∑ i : Fin 4, (c2 i) ^ 2 = s2 ^ 2 by simpa [n2] using hs2sq.symm]
      _ = 1 := by
            field_simp [hs2]
  have h33' : ∑ i : Fin 4, (c3' i) ^ 2 = 1 := by
    let v3 : Fin 4 → ℝ := fun i => (-m23 / n2) * c2 i + c3 i
    let z : Fin 4 → ℝ := fun _ => 0
    have hc3' : ∀ i : Fin 4, c3' i = (1 / s3) * v3 i := by
      intro i
      simp [c3', v3]
      ring
    have hv3sq : ∑ i : Fin 4, (v3 i) ^ 2 = o3 := by
      simpa [v3] using ho3_eq
    have hs3sq : s3 ^ 2 = o3 := by
      dsimp [s3]
      rw [Real.sq_sqrt ho3_nonneg]
    calc
      ∑ i : Fin 4, (c3' i) ^ 2
          = ∑ i : Fin 4, (((1 / s3) * v3 i) + 0 * z i) ^ 2 := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [hc3' i]
              ring
      _ 
          = (1 / s3) ^ 2 * (∑ i : Fin 4, (v3 i) ^ 2) := by
              simpa [z] using sum_sq_linearCombination v3 z (1 / s3) 0
      _ = (1 / s3) ^ 2 * o3 := by rw [hv3sq]
      _ = (1 / s3) ^ 2 * s3 ^ 2 := by rw [← hs3sq]
      _ = 1 := by
            field_simp [hs3]
  have h23' : ∑ i : Fin 4, c2' i * c3' i = 0 := by
    let v3 : Fin 4 → ℝ := fun i => (-m23 / n2) * c2 i + c3 i
    have hc3' : ∀ i : Fin 4, c3' i = (1 / s3) * v3 i := by
      intro i
      simp [c3', v3]
      ring
    have hdotv3 : ∑ i : Fin 4, c2 i * v3 i = 0 := by
      calc
        ∑ i : Fin 4, c2 i * v3 i
            = ∑ i : Fin 4, (1 * c2 i + 0 * c3 i) * ((-m23 / n2) * c2 i + 1 * c3 i) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                simp [v3]
        _ = (-m23 / n2) * (∑ i : Fin 4, (c2 i) ^ 2) + ∑ i : Fin 4, c2 i * c3 i := by
              simpa using sum_mul_linearCombination c2 c3 1 0 (-m23 / n2) 1
        _ = (-m23 / n2) * n2 + m23 := by rfl
        _ = 0 := by
              field_simp [hn2]
              ring
    calc
      ∑ i : Fin 4, c2' i * c3' i
          = ∑ i : Fin 4, (((1 / s2) * c2 i + 0 * v3 i) * (0 * c2 i + (1 / s3) * v3 i)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [hc3' i]
              simp [c2']
      _ = ((1 / s2) * (1 / s3)) * (∑ i : Fin 4, c2 i * v3 i) := by
              simpa using sum_mul_linearCombination c2 v3 (1 / s2) 0 0 (1 / s3)
      _ = 0 := by rw [hdotv3]; ring
  have hdet' :
      MvPolynomial.coeff m11 q2' * MvPolynomial.coeff m02 q3' -
        MvPolynomial.coeff m02 q2' * MvPolynomial.coeff m11 q3' ≠ 0 := by
    have hEq :
        MvPolynomial.coeff m11 q2' * MvPolynomial.coeff m02 q3' -
          MvPolynomial.coeff m02 q2' * MvPolynomial.coeff m11 q3' =
        (1 / (s2 * s3)) *
          (MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
            MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3) := by
      simp [q2', q3']
      ring
    intro hz
    have hmul :
        (1 / (s2 * s3)) *
          (MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
            MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3) = 0 := by
      simpa [hEq] using hz
    have hscale : 1 / (s2 * s3) ≠ 0 := by
      exact one_div_ne_zero (mul_ne_zero hs2 hs3)
    have hdet0 :
        MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
          MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0 := by
      exact (mul_eq_zero.mp hmul).resolve_left hscale
    exact hdet hdet0
  exact residual_eq_zero_of_relations_const_x0_homQuadratics_coeff_m20_zero
    (B := B) (u := u) hu h0 h1 h2' h3' hq2' hq3'
    hq2_00' hq2_10' hq2_01' hq2_20'
    hq3_00' hq3_10' hq3_01' hq3_20'
    h22' h33' h23' hdet' hp hsocp

theorem residual_eq_zero_of_relations_const_x0_homQuadratics_coeff_m02_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq2_02 : MvPolynomial.coeff m02 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 = 0)
    (hq3_02 : MvPolynomial.coeff m02 q3 = 0)
    (h22 : ∑ i : Fin 4, (c2 i) ^ 2 = 1)
    (h33 : ∑ i : Fin 4, (c3 i) ^ 2 = 1)
    (h23 : ∑ i : Fin 4, c2 i * c3 i = 0)
    (hdet :
      MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m11 q3 -
        MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m20 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have h2' :
      ∑ i : Fin 4, c2 i • u i =
        MvPolynomial.coeff m20 q2 • (x0 ^ 2 : Poly) +
          MvPolynomial.coeff m11 q2 • (x0 * x1 : Poly) := by
    calc
      ∑ i : Fin 4, c2 i • u i = q2 := h2
      _ =
          MvPolynomial.coeff m20 q2 • (x0 ^ 2 : Poly) +
            MvPolynomial.coeff m11 q2 • (x0 * x1 : Poly) := by
              simpa using
                homogeneousQuadratic_eq_x0sq_x0x1_of_coeff_m02_zero
                  hq2 hq2_00 hq2_10 hq2_01 hq2_02
  have h3' :
      ∑ i : Fin 4, c3 i • u i =
        MvPolynomial.coeff m20 q3 • (x0 ^ 2 : Poly) +
          MvPolynomial.coeff m11 q3 • (x0 * x1 : Poly) := by
    calc
      ∑ i : Fin 4, c3 i • u i = q3 := h3
      _ =
          MvPolynomial.coeff m20 q3 • (x0 ^ 2 : Poly) +
            MvPolynomial.coeff m11 q3 • (x0 * x1 : Poly) := by
              simpa using
                homogeneousQuadratic_eq_x0sq_x0x1_of_coeff_m02_zero
                  hq3 hq3_00 hq3_10 hq3_01 hq3_02
  exact residual_eq_zero_of_relations_const_x0Plane_det
    (B := B) (u := u) hu h0 h2' h3' h22 h33 h23 hdet hp hsocp

theorem residual_eq_zero_of_relations_const_homQuadratics_coeff_m02_zero_gram
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq2_02 : MvPolynomial.coeff m02 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 = 0)
    (hq3_02 : MvPolynomial.coeff m02 q3 = 0)
    (hgram :
      (∑ i : Fin 4, (c2 i) ^ 2) * (∑ i : Fin 4, (c3 i) ^ 2) -
        (∑ i : Fin 4, c2 i * c3 i) ^ 2 ≠ 0)
    (hdet :
      MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m11 q3 -
        MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m20 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let n2 : ℝ := ∑ i : Fin 4, (c2 i) ^ 2
  let n3 : ℝ := ∑ i : Fin 4, (c3 i) ^ 2
  let m23 : ℝ := ∑ i : Fin 4, c2 i * c3 i
  let g : ℝ := n2 * n3 - m23 ^ 2
  have hg : g ≠ 0 := by
    simpa [g, n2, n3, m23] using hgram
  have hn2_nonneg : 0 ≤ n2 := by
    dsimp [n2]
    positivity
  have hn2 : n2 ≠ 0 := by
    intro hn20
    have hc20 : ∀ i : Fin 4, c2 i = 0 := by
      intro i
      exact eq_zero_of_sum_sq_eq_zero (by simpa [n2] using hn20) i
    have hm23 : m23 = 0 := by
      dsimp [m23]
      refine Finset.sum_eq_zero ?_
      intro i hi
      simp [hc20 i]
    have : g = 0 := by
      simp [g, n2, hn20, hm23]
    exact hg this
  let o3 : ℝ := g / n2
  let s2 : ℝ := Real.sqrt n2
  let s3 : ℝ := Real.sqrt o3
  let c2' : Fin 4 → ℝ := fun i => (1 / s2) * c2 i
  let c3' : Fin 4 → ℝ := fun i => (((-m23 / n2) / s3) * c2 i) + ((1 / s3) * c3 i)
  let q2' : Poly := (1 / s2) • q2
  let q3' : Poly := (((-m23 / n2) / s3) • q2) + ((1 / s3) • q3)
  have ho3_formula : o3 = n3 - m23 ^ 2 / n2 := by
    dsimp [o3, g]
    field_simp [hn2]
  have ho3_eq :
      ∑ i : Fin 4, ((-m23 / n2) * c2 i + c3 i) ^ 2 = o3 := by
    calc
      ∑ i : Fin 4, ((-m23 / n2) * c2 i + c3 i) ^ 2
          = (-m23 / n2) ^ 2 * (∑ i : Fin 4, (c2 i) ^ 2) +
              (2 * (-m23 / n2) * 1) * (∑ i : Fin 4, c2 i * c3 i) +
                1 ^ 2 * (∑ i : Fin 4, (c3 i) ^ 2) := by
                  simpa using sum_sq_linearCombination c2 c3 (-m23 / n2) 1
      _ = n3 - m23 ^ 2 / n2 := by
            dsimp [n2, n3, m23]
            field_simp [hn2]
            ring
      _ = o3 := by exact ho3_formula.symm
  have ho3_nonneg : 0 ≤ o3 := by
    have hs : 0 ≤ ∑ i : Fin 4, ((-m23 / n2) * c2 i + c3 i) ^ 2 := by
      positivity
    simpa [ho3_eq] using hs
  have ho3 : o3 ≠ 0 := by
    intro ho30
    have hg0 : g = 0 := by
      have hdiv0 : g / n2 = 0 := by simpa [o3] using ho30
      exact ((div_eq_zero_iff).mp hdiv0).resolve_right hn2
    exact hg hg0
  have hs2 : s2 ≠ 0 := by
    exact Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne hn2_nonneg hn2.symm)
  have hs3 : s3 ≠ 0 := by
    exact Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne ho3_nonneg ho3.symm)
  have h2' :
      ∑ i : Fin 4, c2' i • u i = q2' := by
    calc
      ∑ i : Fin 4, c2' i • u i = (1 / s2) • (∑ i : Fin 4, c2 i • u i) := by
        simp [c2', Finset.smul_sum, smul_smul]
      _ = q2' := by
        rw [h2]
  have h3' :
      ∑ i : Fin 4, c3' i • u i = q3' := by
    calc
      ∑ i : Fin 4, c3' i • u i
          = ((-m23 / n2) / s3) • (∑ i : Fin 4, c2 i • u i) +
              (1 / s3) • (∑ i : Fin 4, c3 i • u i) := by
                simp [c3', Finset.sum_add_distrib, Finset.smul_sum, add_smul, smul_smul]
      _ = q3' := by
        rw [h2, h3]
  have hq2' : IsQuadratic q2' := by
    exact isQuadratic_smul_local (1 / s2) hq2
  have hq3' : IsQuadratic q3' := by
    exact isQuadratic_linearCombination_local hq2 hq3 (((-m23 / n2) / s3)) (1 / s3)
  have hq2_00' : MvPolynomial.coeff m00 q2' = 0 := by
    simp [q2', hq2_00]
  have hq2_10' : MvPolynomial.coeff m10 q2' = 0 := by
    simp [q2', hq2_10]
  have hq2_01' : MvPolynomial.coeff m01 q2' = 0 := by
    simp [q2', hq2_01]
  have hq2_02' : MvPolynomial.coeff m02 q2' = 0 := by
    simp [q2', hq2_02]
  have hq3_00' : MvPolynomial.coeff m00 q3' = 0 := by
    simp [q3', hq2_00, hq3_00]
  have hq3_10' : MvPolynomial.coeff m10 q3' = 0 := by
    simp [q3', hq2_10, hq3_10]
  have hq3_01' : MvPolynomial.coeff m01 q3' = 0 := by
    simp [q3', hq2_01, hq3_01]
  have hq3_02' : MvPolynomial.coeff m02 q3' = 0 := by
    simp [q3', hq2_02, hq3_02]
  have h22' : ∑ i : Fin 4, (c2' i) ^ 2 = 1 := by
    let z : Fin 4 → ℝ := fun _ => 0
    have hs2sq : s2 ^ 2 = n2 := by
      dsimp [s2]
      rw [Real.sq_sqrt hn2_nonneg]
    calc
      ∑ i : Fin 4, (c2' i) ^ 2
          = (1 / s2) ^ 2 * (∑ i : Fin 4, (c2 i) ^ 2) := by
              simpa [c2', z] using sum_sq_linearCombination c2 z (1 / s2) 0
      _ = (1 / s2) ^ 2 * s2 ^ 2 := by
            rw [show ∑ i : Fin 4, (c2 i) ^ 2 = s2 ^ 2 by simpa [n2] using hs2sq.symm]
      _ = 1 := by
            field_simp [hs2]
  have h33' : ∑ i : Fin 4, (c3' i) ^ 2 = 1 := by
    let v3 : Fin 4 → ℝ := fun i => (-m23 / n2) * c2 i + c3 i
    let z : Fin 4 → ℝ := fun _ => 0
    have hc3' : ∀ i : Fin 4, c3' i = (1 / s3) * v3 i := by
      intro i
      simp [c3', v3]
      ring
    have hv3sq : ∑ i : Fin 4, (v3 i) ^ 2 = o3 := by
      simpa [v3] using ho3_eq
    have hs3sq : s3 ^ 2 = o3 := by
      dsimp [s3]
      rw [Real.sq_sqrt ho3_nonneg]
    calc
      ∑ i : Fin 4, (c3' i) ^ 2
          = ∑ i : Fin 4, (((1 / s3) * v3 i) + 0 * z i) ^ 2 := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [hc3' i]
              ring
      _ 
          = (1 / s3) ^ 2 * (∑ i : Fin 4, (v3 i) ^ 2) := by
              simpa [z] using sum_sq_linearCombination v3 z (1 / s3) 0
      _ = (1 / s3) ^ 2 * o3 := by rw [hv3sq]
      _ = (1 / s3) ^ 2 * s3 ^ 2 := by rw [← hs3sq]
      _ = 1 := by
            field_simp [hs3]
  have h23' : ∑ i : Fin 4, c2' i * c3' i = 0 := by
    let v3 : Fin 4 → ℝ := fun i => (-m23 / n2) * c2 i + c3 i
    have hc3' : ∀ i : Fin 4, c3' i = (1 / s3) * v3 i := by
      intro i
      simp [c3', v3]
      ring
    have hdotv3 : ∑ i : Fin 4, c2 i * v3 i = 0 := by
      calc
        ∑ i : Fin 4, c2 i * v3 i
            = ∑ i : Fin 4, (1 * c2 i + 0 * c3 i) * ((-m23 / n2) * c2 i + 1 * c3 i) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                simp [v3]
        _ = (-m23 / n2) * (∑ i : Fin 4, (c2 i) ^ 2) + ∑ i : Fin 4, c2 i * c3 i := by
              simpa using sum_mul_linearCombination c2 c3 1 0 (-m23 / n2) 1
        _ = (-m23 / n2) * n2 + m23 := by rfl
        _ = 0 := by
              field_simp [hn2]
              ring
    calc
      ∑ i : Fin 4, c2' i * c3' i
          = ∑ i : Fin 4, (((1 / s2) * c2 i + 0 * v3 i) * (0 * c2 i + (1 / s3) * v3 i)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [hc3' i]
              simp [c2']
      _ = ((1 / s2) * (1 / s3)) * (∑ i : Fin 4, c2 i * v3 i) := by
              simpa using sum_mul_linearCombination c2 v3 (1 / s2) 0 0 (1 / s3)
      _ = 0 := by rw [hdotv3]; ring
  have hdet' :
      MvPolynomial.coeff m20 q2' * MvPolynomial.coeff m11 q3' -
        MvPolynomial.coeff m11 q2' * MvPolynomial.coeff m20 q3' ≠ 0 := by
    have hEq :
        MvPolynomial.coeff m20 q2' * MvPolynomial.coeff m11 q3' -
          MvPolynomial.coeff m11 q2' * MvPolynomial.coeff m20 q3' =
        (1 / (s2 * s3)) *
          (MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m11 q3 -
            MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m20 q3) := by
      simp [q2', q3']
      ring
    intro hz
    have hmul :
        (1 / (s2 * s3)) *
          (MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m11 q3 -
            MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m20 q3) = 0 := by
      simpa [hEq] using hz
    have hscale : 1 / (s2 * s3) ≠ 0 := by
      exact one_div_ne_zero (mul_ne_zero hs2 hs3)
    have hdet0 :
        MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m11 q3 -
          MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m20 q3 = 0 := by
      exact (mul_eq_zero.mp hmul).resolve_left hscale
    exact hdet hdet0
  exact residual_eq_zero_of_relations_const_x0_homQuadratics_coeff_m02_zero
    (B := B) (u := u) hu h0 h2' h3' hq2' hq3'
    hq2_00' hq2_10' hq2_01' hq2_02'
    hq3_00' hq3_10' hq3_01' hq3_02'
    h22' h33' h23' hdet' hp hsocp

theorem residual_eq_zero_of_equiv_relations_const_homQuadratics_crossAnnihilator
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 = 0)
    {b c : ℝ}
    (hb : b ≠ 0)
    (hrel2 :
      b * MvPolynomial.coeff m11 q2 +
        c * MvPolynomial.coeff m02 q2 = 0)
    (hrel3 :
      b * MvPolynomial.coeff m11 q3 +
        c * MvPolynomial.coeff m02 q3 = 0)
    (hdet :
      MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let t : ℝ := c / (2 * b)
  let e : Poly ≃ₐ[ℝ] Poly := x1ShearEquiv t
  let B0 : DotForm := dotTransport e B
  have hB : IsPositiveDefinite B := (Fact.out : B.toQuadraticMap.PosDef)
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e)
      (heQuad := fun {_} hpq =>
        isQuadratic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
          (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hpq)
      (heQuartic := fun {_} hpq =>
        isQuartic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
          (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hpq)
      hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv
      (e := e)
      (he := fun {_} hpq =>
        isQuadratic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
          (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hpq)
      hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv
      (e := e)
      (heSymm := fun {_} hpq =>
        isQuadratic_affineEquiv_symm (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
          (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hpq)
      hsocp
  have h0' : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly) := by
    calc
      ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = e (∑ i : Fin 4, c0 i • u i) := by
        simp [mapVec, map_sum]
      _ = 1 := by rw [h0]; simp
  have h2' : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = e q2 := by
    calc
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = e (∑ i : Fin 4, c2 i • u i) := by
        simp [mapVec, map_sum]
      _ = e q2 := by rw [h2]
  have h3' : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = e q3 := by
    calc
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = e (∑ i : Fin 4, c3 i • u i) := by
        simp [mapVec, map_sum]
      _ = e q3 := by rw [h3]
  have hq2' : IsQuadratic (e q2) := by
    exact isQuadratic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
      (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq2
  have hq3' : IsQuadratic (e q3) := by
    exact isQuadratic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
      (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq3
  have hq2_00' : MvPolynomial.coeff m00 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl, coeff_m00_affineHom_x1Shear hq2]
    simpa using hq2_00
  have hq2_10' : MvPolynomial.coeff m10 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl, coeff_m10_affineHom_x1Shear hq2]
    simp [t, hq2_10, hq2_01]
  have hq2_01' : MvPolynomial.coeff m01 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl, coeff_m01_affineHom_x1Shear hq2]
    simpa using hq2_01
  have hq3_00' : MvPolynomial.coeff m00 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl, coeff_m00_affineHom_x1Shear hq3]
    simpa using hq3_00
  have hq3_10' : MvPolynomial.coeff m10 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl, coeff_m10_affineHom_x1Shear hq3]
    simp [t, hq3_10, hq3_01]
  have hq3_01' : MvPolynomial.coeff m01 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl, coeff_m01_affineHom_x1Shear hq3]
    simpa using hq3_01
  have hq2_11' : MvPolynomial.coeff m11 (e q2) = 0 := by
    simpa [e, t] using coeff_m11_affineHom_x1Shear_dual_to_cross hq2 hb hrel2
  have hq3_11' : MvPolynomial.coeff m11 (e q3) = 0 := by
    simpa [e, t] using coeff_m11_affineHom_x1Shear_dual_to_cross hq3 hb hrel3
  have hdet' :
      MvPolynomial.coeff m20 (e q2) * MvPolynomial.coeff m02 (e q3) -
        MvPolynomial.coeff m02 (e q2) * MvPolynomial.coeff m20 (e q3) ≠ 0 := by
    have hcross :
        MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
          MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0 := by
      have hmul :
          b * (MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
            MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3) = 0 := by
        calc
          b * (MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
              MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3) =
              (b * MvPolynomial.coeff m11 q2 + c * MvPolynomial.coeff m02 q2) *
                  MvPolynomial.coeff m02 q3 -
                MvPolynomial.coeff m02 q2 *
                  (b * MvPolynomial.coeff m11 q3 + c * MvPolynomial.coeff m02 q3) := by
            ring
          _ = 0 := by rw [hrel2, hrel3]; ring
      exact (mul_eq_zero.mp hmul).resolve_left hb
    have hdetEq :
        MvPolynomial.coeff m20 (e q2) * MvPolynomial.coeff m02 (e q3) -
          MvPolynomial.coeff m02 (e q2) * MvPolynomial.coeff m20 (e q3) =
        MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m02 q3 -
          MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3 := by
      rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl,
        show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl,
        coeff_m20_affineHom_x1Shear hq2, coeff_m20_affineHom_x1Shear hq3,
        coeff_m02_affineHom_x1Shear hq2, coeff_m02_affineHom_x1Shear hq3]
      calc
        (MvPolynomial.coeff m20 q2 + MvPolynomial.coeff m11 q2 * t + MvPolynomial.coeff m02 q2 * t ^ 2) *
              MvPolynomial.coeff m02 q3 -
            MvPolynomial.coeff m02 q2 *
              (MvPolynomial.coeff m20 q3 + MvPolynomial.coeff m11 q3 * t +
                MvPolynomial.coeff m02 q3 * t ^ 2) =
            (MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m02 q3 -
                MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3) +
              t * (MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
                MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3) := by
          ring
        _ = MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m02 q3 -
              MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3 := by
          rw [hcross]
          ring
    intro hz
    apply hdet
    simpa [hdetEq] using hz
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_homQuadratics_coeff_m11_zero
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0' h2' h3' hq2' hq3' hq2_00' hq2_10' hq2_01' hq2_11'
      hq3_00' hq3_10' hq3_01' hq3_11' hdet' hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_equiv_relations_const_x0_homQuadratics_annihilator_disc_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 = 0)
    (hgram :
      (∑ i : Fin 4, (c2 i) ^ 2) * (∑ i : Fin 4, (c3 i) ^ 2) -
        (∑ i : Fin 4, c2 i * c3 i) ^ 2 ≠ 0)
    {a b c : ℝ}
    (ha : a ≠ 0)
    (hrel2 :
      a * MvPolynomial.coeff m20 q2 +
        b * MvPolynomial.coeff m11 q2 +
          c * MvPolynomial.coeff m02 q2 = 0)
    (hrel3 :
      a * MvPolynomial.coeff m20 q3 +
        b * MvPolynomial.coeff m11 q3 +
          c * MvPolynomial.coeff m02 q3 = 0)
    (hdisc : c - b ^ 2 / a = 0)
    (hdet :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let t : ℝ := b / a
  let e : Poly ≃ₐ[ℝ] Poly := x1ShearEquiv t
  let B0 : DotForm := dotTransport e B
  have hB : IsPositiveDefinite B := (Fact.out : B.toQuadraticMap.PosDef)
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e)
      (heQuad := fun {_} hpq =>
        isQuadratic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
          (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hpq)
      (heQuartic := fun {_} hpq =>
        isQuartic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
          (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hpq)
      hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv
      (e := e)
      (he := fun {_} hpq =>
        isQuadratic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
          (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hpq)
      hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv
      (e := e)
      (heSymm := fun {_} hpq =>
        isQuadratic_affineEquiv_symm (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
          (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hpq)
      hsocp
  have h0' : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly) := by
    calc
      ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = e (∑ i : Fin 4, c0 i • u i) := by
        simp [mapVec, map_sum]
      _ = 1 := by rw [h0]; simp
  have h1' : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x0 := by
    calc
      ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = e (∑ i : Fin 4, c1 i • u i) := by
        simp [mapVec, map_sum]
      _ = e x0 := by rw [h1]
      _ = x0 := by
        rw [show e x0 = affineHom (x1ShearMatrix t) 0 x0 by rfl]
        simp [affineHom_x1Shear_x0]
  have h2' : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = e q2 := by
    calc
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = e (∑ i : Fin 4, c2 i • u i) := by
        simp [mapVec, map_sum]
      _ = e q2 := by rw [h2]
  have h3' : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = e q3 := by
    calc
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = e (∑ i : Fin 4, c3 i • u i) := by
        simp [mapVec, map_sum]
      _ = e q3 := by rw [h3]
  have hq2' : IsQuadratic (e q2) := by
    exact isQuadratic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
      (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq2
  have hq3' : IsQuadratic (e q3) := by
    exact isQuadratic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
      (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq3
  have hq2_00' : MvPolynomial.coeff m00 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl, coeff_m00_affineHom_x1Shear hq2]
    simpa using hq2_00
  have hq2_10' : MvPolynomial.coeff m10 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl, coeff_m10_affineHom_x1Shear hq2]
    simp [t, hq2_10, hq2_01]
  have hq2_01' : MvPolynomial.coeff m01 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl, coeff_m01_affineHom_x1Shear hq2]
    simpa using hq2_01
  have hq3_00' : MvPolynomial.coeff m00 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl, coeff_m00_affineHom_x1Shear hq3]
    simpa using hq3_00
  have hq3_10' : MvPolynomial.coeff m10 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl, coeff_m10_affineHom_x1Shear hq3]
    simp [t, hq3_10, hq3_01]
  have hq3_01' : MvPolynomial.coeff m01 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl, coeff_m01_affineHom_x1Shear hq3]
    simpa using hq3_01
  have hq2_20' : MvPolynomial.coeff m20 (e q2) = 0 := by
    have hrel2' :
        a * MvPolynomial.coeff m20 (e q2) +
          (c - b ^ 2 / a) * MvPolynomial.coeff m02 (e q2) = 0 := by
      simpa [e, t] using coeff_relation_affineHom_x1Shear_dual_kill_cross hq2 ha hrel2
    rw [hdisc, zero_mul, add_zero] at hrel2'
    exact (mul_eq_zero.mp hrel2').resolve_left ha
  have hq3_20' : MvPolynomial.coeff m20 (e q3) = 0 := by
    have hrel3' :
        a * MvPolynomial.coeff m20 (e q3) +
          (c - b ^ 2 / a) * MvPolynomial.coeff m02 (e q3) = 0 := by
      simpa [e, t] using coeff_relation_affineHom_x1Shear_dual_kill_cross hq3 ha hrel3
    rw [hdisc, zero_mul, add_zero] at hrel3'
    exact (mul_eq_zero.mp hrel3').resolve_left ha
  have hdet' :
      MvPolynomial.coeff m11 (e q2) * MvPolynomial.coeff m02 (e q3) -
        MvPolynomial.coeff m02 (e q2) * MvPolynomial.coeff m11 (e q3) ≠ 0 := by
    have hdetEq :
        MvPolynomial.coeff m11 (e q2) * MvPolynomial.coeff m02 (e q3) -
          MvPolynomial.coeff m02 (e q2) * MvPolynomial.coeff m11 (e q3) =
        MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
          MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 := by
      rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl,
        show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl,
        coeff_m11_affineHom_x1Shear hq2, coeff_m11_affineHom_x1Shear hq3,
        coeff_m02_affineHom_x1Shear hq2, coeff_m02_affineHom_x1Shear hq3]
      ring
    intro hz
    apply hdet
    simpa [hdetEq] using hz
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_homQuadratics_coeff_m20_zero_gram
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0' h1' h2' h3' hq2' hq3' hq2_00' hq2_10' hq2_01' hq2_20'
      hq3_00' hq3_10' hq3_01' hq3_20' hgram hdet' hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_equiv_relations_const_homQuadratics_diagAnnihilator_sum
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 = 0)
    {a d : ℝ}
    (ha : a ≠ 0)
    (hrel2 :
      a * MvPolynomial.coeff m20 q2 +
        d * MvPolynomial.coeff m02 q2 = 0)
    (hrel3 :
      a * MvPolynomial.coeff m20 q3 +
        d * MvPolynomial.coeff m02 q3 = 0)
    (hpos : 0 < d / a)
    (hdet :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m20 q3 -
        MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m11 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let s : ℝ := Real.sqrt (d / a)
  have hs : s ≠ 0 := by
    dsimp [s]
    exact Real.sqrt_ne_zero'.mpr hpos
  let e : Poly ≃ₐ[ℝ] Poly := x1ScaleEquiv s hs
  let B0 : DotForm := dotTransport e B
  have hB : IsPositiveDefinite B := (Fact.out : B.toQuadraticMap.PosDef)
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e)
      (heQuad := fun {_} hpq =>
        isQuadratic_affineEquiv (x1ScaleMatrix s) (x1ScaleInvMatrix s) 0 0
          (x1Scale_mul_inv s hs) (x1Scale_inv_mul s hs) (by intro i; simp) (by intro i; simp) hpq)
      (heQuartic := fun {_} hpq =>
        isQuartic_affineEquiv (x1ScaleMatrix s) (x1ScaleInvMatrix s) 0 0
          (x1Scale_mul_inv s hs) (x1Scale_inv_mul s hs) (by intro i; simp) (by intro i; simp) hpq)
      hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv
      (e := e)
      (he := fun {_} hpq =>
        isQuadratic_affineEquiv (x1ScaleMatrix s) (x1ScaleInvMatrix s) 0 0
          (x1Scale_mul_inv s hs) (x1Scale_inv_mul s hs) (by intro i; simp) (by intro i; simp) hpq)
      hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv
      (e := e)
      (heSymm := fun {_} hpq =>
        isQuadratic_affineEquiv_symm (x1ScaleMatrix s) (x1ScaleInvMatrix s) 0 0
          (x1Scale_mul_inv s hs) (x1Scale_inv_mul s hs) (by intro i; simp) (by intro i; simp) hpq)
      hsocp
  have h0' : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly) := by
    calc
      ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = e (∑ i : Fin 4, c0 i • u i) := by
        simp [mapVec, map_sum]
      _ = 1 := by rw [h0]; simp
  have h2' : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = e q2 := by
    calc
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = e (∑ i : Fin 4, c2 i • u i) := by
        simp [mapVec, map_sum]
      _ = e q2 := by rw [h2]
  have h3' : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = e q3 := by
    calc
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = e (∑ i : Fin 4, c3 i • u i) := by
        simp [mapVec, map_sum]
      _ = e q3 := by rw [h3]
  have hq2' : IsQuadratic (e q2) := by
    exact isQuadratic_affineEquiv (x1ScaleMatrix s) (x1ScaleInvMatrix s) 0 0
      (x1Scale_mul_inv s hs) (x1Scale_inv_mul s hs) (by intro i; simp) (by intro i; simp) hq2
  have hq3' : IsQuadratic (e q3) := by
    exact isQuadratic_affineEquiv (x1ScaleMatrix s) (x1ScaleInvMatrix s) 0 0
      (x1Scale_mul_inv s hs) (x1Scale_inv_mul s hs) (by intro i; simp) (by intro i; simp) hq3
  have hq2_00' : MvPolynomial.coeff m00 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ScaleMatrix s) 0 q2 by rfl, coeff_m00_affineHom_x1Scale hq2]
    simpa using hq2_00
  have hq2_10' : MvPolynomial.coeff m10 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ScaleMatrix s) 0 q2 by rfl, coeff_m10_affineHom_x1Scale hq2]
    simpa using hq2_10
  have hq2_01' : MvPolynomial.coeff m01 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ScaleMatrix s) 0 q2 by rfl, coeff_m01_affineHom_x1Scale hq2]
    simp [hq2_01]
  have hq3_00' : MvPolynomial.coeff m00 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ScaleMatrix s) 0 q3 by rfl, coeff_m00_affineHom_x1Scale hq3]
    simpa using hq3_00
  have hq3_10' : MvPolynomial.coeff m10 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ScaleMatrix s) 0 q3 by rfl, coeff_m10_affineHom_x1Scale hq3]
    simpa using hq3_10
  have hq3_01' : MvPolynomial.coeff m01 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ScaleMatrix s) 0 q3 by rfl, coeff_m01_affineHom_x1Scale hq3]
    simp [hq3_01]
  have hq2_diag' :
      MvPolynomial.coeff m20 (e q2) + MvPolynomial.coeff m02 (e q2) = 0 := by
    simpa [e, s] using coeff_relation_affineHom_x1Scale_diag_sum_zero hq2 ha hrel2 hpos
  have hq3_diag' :
      MvPolynomial.coeff m20 (e q3) + MvPolynomial.coeff m02 (e q3) = 0 := by
    simpa [e, s] using coeff_relation_affineHom_x1Scale_diag_sum_zero hq3 ha hrel3 hpos
  have hdet' :
      MvPolynomial.coeff m11 (e q2) * MvPolynomial.coeff m20 (e q3) -
        MvPolynomial.coeff m20 (e q2) * MvPolynomial.coeff m11 (e q3) ≠ 0 := by
    have hdetEq :
        MvPolynomial.coeff m11 (e q2) * MvPolynomial.coeff m20 (e q3) -
          MvPolynomial.coeff m20 (e q2) * MvPolynomial.coeff m11 (e q3) =
        s * (MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m20 q3 -
          MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m11 q3) := by
      rw [show e q2 = affineHom (x1ScaleMatrix s) 0 q2 by rfl,
        show e q3 = affineHom (x1ScaleMatrix s) 0 q3 by rfl,
        coeff_m11_affineHom_x1Scale hq2, coeff_m11_affineHom_x1Scale hq3,
        coeff_m20_affineHom_x1Scale hq2, coeff_m20_affineHom_x1Scale hq3]
      ring
    intro hz
    have hmul :
        s * (MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m20 q3 -
          MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m11 q3) = 0 := by
      simpa [hdetEq] using hz
    have hdet0 :
        MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m20 q3 -
          MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m11 q3 = 0 := by
      exact (mul_eq_zero.mp hmul).resolve_left hs
    exact hdet hdet0
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_homQuadratics_diag_sum_zero
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0' h2' h3' hq2' hq3' hq2_00' hq2_10' hq2_01' hq2_diag'
      hq3_00' hq3_10' hq3_01' hq3_diag' hdet' hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_equiv_relations_const_homQuadratics_diagAnnihilator_diff
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 = 0)
    {a d : ℝ}
    (ha : a ≠ 0)
    (hrel2 :
      a * MvPolynomial.coeff m20 q2 +
        d * MvPolynomial.coeff m02 q2 = 0)
    (hrel3 :
      a * MvPolynomial.coeff m20 q3 +
        d * MvPolynomial.coeff m02 q3 = 0)
    (hpos : 0 < (-d) / a)
    (hdet :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m20 q3 -
        MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m11 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let s : ℝ := Real.sqrt ((-d) / a)
  have hs : s ≠ 0 := by
    dsimp [s]
    exact Real.sqrt_ne_zero'.mpr hpos
  let e : Poly ≃ₐ[ℝ] Poly := x1ScaleEquiv s hs
  let B0 : DotForm := dotTransport e B
  have hB : IsPositiveDefinite B := (Fact.out : B.toQuadraticMap.PosDef)
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e)
      (heQuad := fun {_} hpq =>
        isQuadratic_affineEquiv (x1ScaleMatrix s) (x1ScaleInvMatrix s) 0 0
          (x1Scale_mul_inv s hs) (x1Scale_inv_mul s hs) (by intro i; simp) (by intro i; simp) hpq)
      (heQuartic := fun {_} hpq =>
        isQuartic_affineEquiv (x1ScaleMatrix s) (x1ScaleInvMatrix s) 0 0
          (x1Scale_mul_inv s hs) (x1Scale_inv_mul s hs) (by intro i; simp) (by intro i; simp) hpq)
      hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv
      (e := e)
      (he := fun {_} hpq =>
        isQuadratic_affineEquiv (x1ScaleMatrix s) (x1ScaleInvMatrix s) 0 0
          (x1Scale_mul_inv s hs) (x1Scale_inv_mul s hs) (by intro i; simp) (by intro i; simp) hpq)
      hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv
      (e := e)
      (heSymm := fun {_} hpq =>
        isQuadratic_affineEquiv_symm (x1ScaleMatrix s) (x1ScaleInvMatrix s) 0 0
          (x1Scale_mul_inv s hs) (x1Scale_inv_mul s hs) (by intro i; simp) (by intro i; simp) hpq)
      hsocp
  have h0' : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly) := by
    calc
      ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = e (∑ i : Fin 4, c0 i • u i) := by
        simp [mapVec, map_sum]
      _ = 1 := by rw [h0]; simp
  have h2' : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = e q2 := by
    calc
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = e (∑ i : Fin 4, c2 i • u i) := by
        simp [mapVec, map_sum]
      _ = e q2 := by rw [h2]
  have h3' : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = e q3 := by
    calc
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = e (∑ i : Fin 4, c3 i • u i) := by
        simp [mapVec, map_sum]
      _ = e q3 := by rw [h3]
  have hq2' : IsQuadratic (e q2) := by
    exact isQuadratic_affineEquiv (x1ScaleMatrix s) (x1ScaleInvMatrix s) 0 0
      (x1Scale_mul_inv s hs) (x1Scale_inv_mul s hs) (by intro i; simp) (by intro i; simp) hq2
  have hq3' : IsQuadratic (e q3) := by
    exact isQuadratic_affineEquiv (x1ScaleMatrix s) (x1ScaleInvMatrix s) 0 0
      (x1Scale_mul_inv s hs) (x1Scale_inv_mul s hs) (by intro i; simp) (by intro i; simp) hq3
  have hq2_00' : MvPolynomial.coeff m00 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ScaleMatrix s) 0 q2 by rfl, coeff_m00_affineHom_x1Scale hq2]
    simpa using hq2_00
  have hq2_10' : MvPolynomial.coeff m10 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ScaleMatrix s) 0 q2 by rfl, coeff_m10_affineHom_x1Scale hq2]
    simpa using hq2_10
  have hq2_01' : MvPolynomial.coeff m01 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ScaleMatrix s) 0 q2 by rfl, coeff_m01_affineHom_x1Scale hq2]
    simp [hq2_01]
  have hq3_00' : MvPolynomial.coeff m00 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ScaleMatrix s) 0 q3 by rfl, coeff_m00_affineHom_x1Scale hq3]
    simpa using hq3_00
  have hq3_10' : MvPolynomial.coeff m10 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ScaleMatrix s) 0 q3 by rfl, coeff_m10_affineHom_x1Scale hq3]
    simpa using hq3_10
  have hq3_01' : MvPolynomial.coeff m01 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ScaleMatrix s) 0 q3 by rfl, coeff_m01_affineHom_x1Scale hq3]
    simp [hq3_01]
  have hq2_diag' :
      MvPolynomial.coeff m20 (e q2) - MvPolynomial.coeff m02 (e q2) = 0 := by
    simpa [e, s] using coeff_relation_affineHom_x1Scale_diag_diff_zero hq2 ha hrel2 hpos
  have hq3_diag' :
      MvPolynomial.coeff m20 (e q3) - MvPolynomial.coeff m02 (e q3) = 0 := by
    simpa [e, s] using coeff_relation_affineHom_x1Scale_diag_diff_zero hq3 ha hrel3 hpos
  have hdet' :
      MvPolynomial.coeff m11 (e q2) * MvPolynomial.coeff m20 (e q3) -
        MvPolynomial.coeff m20 (e q2) * MvPolynomial.coeff m11 (e q3) ≠ 0 := by
    have hdetEq :
        MvPolynomial.coeff m11 (e q2) * MvPolynomial.coeff m20 (e q3) -
          MvPolynomial.coeff m20 (e q2) * MvPolynomial.coeff m11 (e q3) =
        s * (MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m20 q3 -
          MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m11 q3) := by
      rw [show e q2 = affineHom (x1ScaleMatrix s) 0 q2 by rfl,
        show e q3 = affineHom (x1ScaleMatrix s) 0 q3 by rfl,
        coeff_m11_affineHom_x1Scale hq2, coeff_m11_affineHom_x1Scale hq3,
        coeff_m20_affineHom_x1Scale hq2, coeff_m20_affineHom_x1Scale hq3]
      ring
    intro hz
    have hmul :
        s * (MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m20 q3 -
          MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m11 q3) = 0 := by
      simpa [hdetEq] using hz
    have hdet0 :
        MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m20 q3 -
          MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m11 q3 = 0 := by
      exact (mul_eq_zero.mp hmul).resolve_left hs
    exact hdet hdet0
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_homQuadratics_diag_diff_zero
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0' h2' h3' hq2' hq3' hq2_00' hq2_10' hq2_01' hq2_diag'
      hq3_00' hq3_10' hq3_01' hq3_diag' hdet' hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_equiv_relations_const_homQuadratics_annihilator_sum
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 = 0)
    {a b c : ℝ}
    (ha : a ≠ 0)
    (hrel2 :
      a * MvPolynomial.coeff m20 q2 +
        b * MvPolynomial.coeff m11 q2 +
          c * MvPolynomial.coeff m02 q2 = 0)
    (hrel3 :
      a * MvPolynomial.coeff m20 q3 +
        b * MvPolynomial.coeff m11 q3 +
          c * MvPolynomial.coeff m02 q3 = 0)
    (hpos : 0 < (c - b ^ 2 / a) / a)
    (hdet :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let t : ℝ := b / a
  let d : ℝ := c - b ^ 2 / a
  let e : Poly ≃ₐ[ℝ] Poly := x1ShearEquiv t
  let B0 : DotForm := dotTransport e B
  have hB : IsPositiveDefinite B := (Fact.out : B.toQuadraticMap.PosDef)
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e)
      (heQuad := fun {_} hpq =>
        isQuadratic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
          (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hpq)
      (heQuartic := fun {_} hpq =>
        isQuartic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
          (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hpq)
      hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv
      (e := e)
      (he := fun {_} hpq =>
        isQuadratic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
          (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hpq)
      hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv
      (e := e)
      (heSymm := fun {_} hpq =>
        isQuadratic_affineEquiv_symm (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
          (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hpq)
      hsocp
  have h0' : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly) := by
    calc
      ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = e (∑ i : Fin 4, c0 i • u i) := by
        simp [mapVec, map_sum]
      _ = 1 := by rw [h0]; simp
  have h2' : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = e q2 := by
    calc
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = e (∑ i : Fin 4, c2 i • u i) := by
        simp [mapVec, map_sum]
      _ = e q2 := by rw [h2]
  have h3' : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = e q3 := by
    calc
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = e (∑ i : Fin 4, c3 i • u i) := by
        simp [mapVec, map_sum]
      _ = e q3 := by rw [h3]
  have hq2' : IsQuadratic (e q2) := by
    exact isQuadratic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
      (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq2
  have hq3' : IsQuadratic (e q3) := by
    exact isQuadratic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
      (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq3
  have hq2_00' : MvPolynomial.coeff m00 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl, coeff_m00_affineHom_x1Shear hq2]
    simpa using hq2_00
  have hq2_10' : MvPolynomial.coeff m10 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl, coeff_m10_affineHom_x1Shear hq2]
    simp [t, hq2_10, hq2_01]
  have hq2_01' : MvPolynomial.coeff m01 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl, coeff_m01_affineHom_x1Shear hq2]
    simpa using hq2_01
  have hq3_00' : MvPolynomial.coeff m00 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl, coeff_m00_affineHom_x1Shear hq3]
    simpa using hq3_00
  have hq3_10' : MvPolynomial.coeff m10 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl, coeff_m10_affineHom_x1Shear hq3]
    simp [t, hq3_10, hq3_01]
  have hq3_01' : MvPolynomial.coeff m01 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl, coeff_m01_affineHom_x1Shear hq3]
    simpa using hq3_01
  have hrel2' :
      a * MvPolynomial.coeff m20 (e q2) + d * MvPolynomial.coeff m02 (e q2) = 0 := by
    simpa [e, t, d] using coeff_relation_affineHom_x1Shear_dual_kill_cross hq2 ha hrel2
  have hrel3' :
      a * MvPolynomial.coeff m20 (e q3) + d * MvPolynomial.coeff m02 (e q3) = 0 := by
    simpa [e, t, d] using coeff_relation_affineHom_x1Shear_dual_kill_cross hq3 ha hrel3
  have hcrossEq :
      MvPolynomial.coeff m11 (e q2) * MvPolynomial.coeff m02 (e q3) -
        MvPolynomial.coeff m02 (e q2) * MvPolynomial.coeff m11 (e q3) =
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 := by
    rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl,
      show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl,
      coeff_m11_affineHom_x1Shear hq2, coeff_m11_affineHom_x1Shear hq3,
      coeff_m02_affineHom_x1Shear hq2, coeff_m02_affineHom_x1Shear hq3]
    ring
  have hx2 :
      MvPolynomial.coeff m20 (e q2) = -(d / a) * MvPolynomial.coeff m02 (e q2) := by
    field_simp [ha]
    linarith [hrel2']
  have hx3 :
      MvPolynomial.coeff m20 (e q3) = -(d / a) * MvPolynomial.coeff m02 (e q3) := by
    field_simp [ha]
    linarith [hrel3']
  have hfactor : -(d / a) ≠ 0 := by
    have : 0 < d / a := by simpa [d] using hpos
    nlinarith
  have hdet' :
      MvPolynomial.coeff m11 (e q2) * MvPolynomial.coeff m20 (e q3) -
        MvPolynomial.coeff m20 (e q2) * MvPolynomial.coeff m11 (e q3) ≠ 0 := by
    have hdetEq :
        MvPolynomial.coeff m11 (e q2) * MvPolynomial.coeff m20 (e q3) -
          MvPolynomial.coeff m20 (e q2) * MvPolynomial.coeff m11 (e q3) =
        (-(d / a)) * (MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
          MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3) := by
      rw [hx2, hx3]
      calc
        MvPolynomial.coeff m11 (e q2) * (-(d / a) * MvPolynomial.coeff m02 (e q3)) -
              (-(d / a) * MvPolynomial.coeff m02 (e q2)) * MvPolynomial.coeff m11 (e q3) =
            (-(d / a)) * (MvPolynomial.coeff m11 (e q2) * MvPolynomial.coeff m02 (e q3) -
              MvPolynomial.coeff m02 (e q2) * MvPolynomial.coeff m11 (e q3)) := by
          ring
        _ = (-(d / a)) * (MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
              MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3) := by
          rw [hcrossEq]
    intro hz
    have hmul :
        (-(d / a)) * (MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
          MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3) = 0 := by
      simpa [hdetEq] using hz
    have hdet0 :
        MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
          MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0 := by
      exact (mul_eq_zero.mp hmul).resolve_left hfactor
    exact hdet hdet0
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_equiv_relations_const_homQuadratics_diagAnnihilator_sum
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0' h2' h3' hq2' hq3' hq2_00' hq2_10' hq2_01' hq3_00' hq3_10' hq3_01'
      ha hrel2' hrel3' (by simpa [d] using hpos) hdet' hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_equiv_relations_const_homQuadratics_annihilator_diff
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 = 0)
    {a b c : ℝ}
    (ha : a ≠ 0)
    (hrel2 :
      a * MvPolynomial.coeff m20 q2 +
        b * MvPolynomial.coeff m11 q2 +
          c * MvPolynomial.coeff m02 q2 = 0)
    (hrel3 :
      a * MvPolynomial.coeff m20 q3 +
        b * MvPolynomial.coeff m11 q3 +
          c * MvPolynomial.coeff m02 q3 = 0)
    (hpos : 0 < (-(c - b ^ 2 / a)) / a)
    (hdet :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let t : ℝ := b / a
  let d : ℝ := c - b ^ 2 / a
  let e : Poly ≃ₐ[ℝ] Poly := x1ShearEquiv t
  let B0 : DotForm := dotTransport e B
  have hB : IsPositiveDefinite B := (Fact.out : B.toQuadraticMap.PosDef)
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e)
      (heQuad := fun {_} hpq =>
        isQuadratic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
          (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hpq)
      (heQuartic := fun {_} hpq =>
        isQuartic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
          (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hpq)
      hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv
      (e := e)
      (he := fun {_} hpq =>
        isQuadratic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
          (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hpq)
      hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv
      (e := e)
      (heSymm := fun {_} hpq =>
        isQuadratic_affineEquiv_symm (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
          (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hpq)
      hsocp
  have h0' : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly) := by
    calc
      ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = e (∑ i : Fin 4, c0 i • u i) := by
        simp [mapVec, map_sum]
      _ = 1 := by rw [h0]; simp
  have h2' : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = e q2 := by
    calc
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = e (∑ i : Fin 4, c2 i • u i) := by
        simp [mapVec, map_sum]
      _ = e q2 := by rw [h2]
  have h3' : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = e q3 := by
    calc
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = e (∑ i : Fin 4, c3 i • u i) := by
        simp [mapVec, map_sum]
      _ = e q3 := by rw [h3]
  have hq2' : IsQuadratic (e q2) := by
    exact isQuadratic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
      (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq2
  have hq3' : IsQuadratic (e q3) := by
    exact isQuadratic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
      (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq3
  have hq2_00' : MvPolynomial.coeff m00 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl, coeff_m00_affineHom_x1Shear hq2]
    simpa using hq2_00
  have hq2_10' : MvPolynomial.coeff m10 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl, coeff_m10_affineHom_x1Shear hq2]
    simp [t, hq2_10, hq2_01]
  have hq2_01' : MvPolynomial.coeff m01 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl, coeff_m01_affineHom_x1Shear hq2]
    simpa using hq2_01
  have hq3_00' : MvPolynomial.coeff m00 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl, coeff_m00_affineHom_x1Shear hq3]
    simpa using hq3_00
  have hq3_10' : MvPolynomial.coeff m10 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl, coeff_m10_affineHom_x1Shear hq3]
    simp [t, hq3_10, hq3_01]
  have hq3_01' : MvPolynomial.coeff m01 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl, coeff_m01_affineHom_x1Shear hq3]
    simpa using hq3_01
  have hrel2' :
      a * MvPolynomial.coeff m20 (e q2) + d * MvPolynomial.coeff m02 (e q2) = 0 := by
    simpa [e, t, d] using coeff_relation_affineHom_x1Shear_dual_kill_cross hq2 ha hrel2
  have hrel3' :
      a * MvPolynomial.coeff m20 (e q3) + d * MvPolynomial.coeff m02 (e q3) = 0 := by
    simpa [e, t, d] using coeff_relation_affineHom_x1Shear_dual_kill_cross hq3 ha hrel3
  have hcrossEq :
      MvPolynomial.coeff m11 (e q2) * MvPolynomial.coeff m02 (e q3) -
        MvPolynomial.coeff m02 (e q2) * MvPolynomial.coeff m11 (e q3) =
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 := by
    rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl,
      show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl,
      coeff_m11_affineHom_x1Shear hq2, coeff_m11_affineHom_x1Shear hq3,
      coeff_m02_affineHom_x1Shear hq2, coeff_m02_affineHom_x1Shear hq3]
    ring
  have hx2 :
      MvPolynomial.coeff m20 (e q2) = -(d / a) * MvPolynomial.coeff m02 (e q2) := by
    field_simp [ha]
    linarith [hrel2']
  have hx3 :
      MvPolynomial.coeff m20 (e q3) = -(d / a) * MvPolynomial.coeff m02 (e q3) := by
    field_simp [ha]
    linarith [hrel3']
  have hfactorPos : 0 < -(d / a) := by
    dsimp [d]
    have hEq : (-(c - b ^ 2 / a)) / a = -((c - b ^ 2 / a) / a) := by
      ring
    have hpos0 := hpos
    rw [hEq] at hpos0
    simpa using hpos0
  have hfactor : -(d / a) ≠ 0 := ne_of_gt hfactorPos
  have hdet' :
      MvPolynomial.coeff m11 (e q2) * MvPolynomial.coeff m20 (e q3) -
        MvPolynomial.coeff m20 (e q2) * MvPolynomial.coeff m11 (e q3) ≠ 0 := by
    have hdetEq :
        MvPolynomial.coeff m11 (e q2) * MvPolynomial.coeff m20 (e q3) -
          MvPolynomial.coeff m20 (e q2) * MvPolynomial.coeff m11 (e q3) =
        (-(d / a)) * (MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
          MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3) := by
      rw [hx2, hx3]
      calc
        MvPolynomial.coeff m11 (e q2) * (-(d / a) * MvPolynomial.coeff m02 (e q3)) -
              (-(d / a) * MvPolynomial.coeff m02 (e q2)) * MvPolynomial.coeff m11 (e q3) =
            (-(d / a)) * (MvPolynomial.coeff m11 (e q2) * MvPolynomial.coeff m02 (e q3) -
              MvPolynomial.coeff m02 (e q2) * MvPolynomial.coeff m11 (e q3)) := by
          ring
        _ = (-(d / a)) * (MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
              MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3) := by
          rw [hcrossEq]
    intro hz
    have hmul :
        (-(d / a)) * (MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
          MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3) = 0 := by
      simpa [hdetEq] using hz
    have hdet0 :
        MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
          MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0 := by
      exact (mul_eq_zero.mp hmul).resolve_left hfactor
    exact hdet hdet0
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    have hpos' : 0 < (-d) / a := by
      dsimp [d]
      simpa using hpos
    exact residual_eq_zero_of_equiv_relations_const_homQuadratics_diagAnnihilator_diff
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0' h2' h3' hq2' hq3' hq2_00' hq2_10' hq2_01' hq3_00' hq3_10' hq3_01'
      ha hrel2' hrel3' hpos' hdet' hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_const_x0_homQuadratics_plane_nontrivial
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 = 0)
    (hgram :
      (∑ i : Fin 4, (c2 i) ^ 2) * (∑ i : Fin 4, (c3 i) ^ 2) -
        (∑ i : Fin 4, c2 i * c3 i) ^ 2 ≠ 0)
    (hplane :
      homQuadPlaneA q2 q3 ≠ 0 ∨
        homQuadPlaneB q2 q3 ≠ 0 ∨
          homQuadPlaneC q2 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let a : ℝ := homQuadPlaneA q2 q3
  let b : ℝ := homQuadPlaneB q2 q3
  let c : ℝ := homQuadPlaneC q2 q3
  have hplane' : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 := by
    simpa [a, b, c] using hplane
  have hrel2 :
      a * MvPolynomial.coeff m20 q2 +
        (-b) * MvPolynomial.coeff m11 q2 +
          c * MvPolynomial.coeff m02 q2 = 0 := by
    simpa [a, b, c] using homQuadPlane_relation_left q2 q3
  have hrel3 :
      a * MvPolynomial.coeff m20 q3 +
        (-b) * MvPolynomial.coeff m11 q3 +
          c * MvPolynomial.coeff m02 q3 = 0 := by
    simpa [a, b, c] using homQuadPlane_relation_right q2 q3
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · have hc : c ≠ 0 := by
        rcases hplane' with hA | hB | hC
        · exact (hA ha).elim
        · exact (hB hb).elim
        · exact hC
      have hq2_02 : MvPolynomial.coeff m02 q2 = 0 := by
        have h : c = 0 ∨ MvPolynomial.coeff m02 q2 = 0 := by
          simpa [ha, hb] using hrel2
        exact h.resolve_left hc
      have hq3_02 : MvPolynomial.coeff m02 q3 = 0 := by
        have h : c = 0 ∨ MvPolynomial.coeff m02 q3 = 0 := by
          simpa [ha, hb] using hrel3
        exact h.resolve_left hc
      have hdet :
          MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m11 q3 -
            MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m20 q3 ≠ 0 := by
        simpa [c] using hc
      exact residual_eq_zero_of_relations_const_homQuadratics_coeff_m02_zero_gram
        (B := B) (u := u) hu h0 h2 h3 hq2 hq3
        hq2_00 hq2_10 hq2_01 hq2_02
        hq3_00 hq3_10 hq3_01 hq3_02
        hgram hdet hp hsocp
    · have hdet :
          MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m02 q3 -
            MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3 ≠ 0 := by
        simpa [b] using hb
      exact residual_eq_zero_of_equiv_relations_const_homQuadratics_crossAnnihilator
        (B := B) (u := u) hu h0 h2 h3 hq2 hq3
        hq2_00 hq2_10 hq2_01 hq3_00 hq3_10 hq3_01
        (b := -b) (c := c) (neg_ne_zero.mpr hb)
        (by simpa [ha] using hrel2) (by simpa [ha] using hrel3)
        hdet hp hsocp
  · have hdet :
        MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
          MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 ≠ 0 := by
      simpa [a] using ha
    by_cases hdisc : c - b ^ 2 / a = 0
    · exact residual_eq_zero_of_equiv_relations_const_x0_homQuadratics_annihilator_disc_zero
        (B := B) (u := u) hu h0 h1 h2 h3 hq2 hq3
        hq2_00 hq2_10 hq2_01 hq3_00 hq3_10 hq3_01
        hgram (a := a) (b := -b) (c := c) ha
        hrel2 hrel3 (by simpa using hdisc) hdet hp hsocp
    · by_cases hpos : 0 < (c - b ^ 2 / a) / a
      · exact
          (residual_eq_zero_of_equiv_relations_const_homQuadratics_annihilator_sum
            (B := B) (u := u) hu h0 h2 h3 hq2 hq3
            hq2_00 hq2_10 hq2_01 hq3_00 hq3_10 hq3_01
            (a := a) (b := -b) (c := c) ha
            hrel2 hrel3 (by simpa using hpos) hdet hp hsocp)
      · have hdivne : (c - b ^ 2 / a) / a ≠ 0 := by
          exact div_ne_zero hdisc ha
        have hlt : (c - b ^ 2 / a) / a < 0 := by
          exact lt_of_le_of_ne (le_of_not_gt hpos) hdivne
        have hpos' : 0 < (-(c - (-b) ^ 2 / a)) / a := by
          have hEq : (-(c - (-b) ^ 2 / a)) / a = -((c - b ^ 2 / a) / a) := by
            ring
          rw [hEq]
          linarith
        exact
          (residual_eq_zero_of_equiv_relations_const_homQuadratics_annihilator_diff
            (B := B) (u := u) hu h0 h2 h3 hq2 hq3
            hq2_00 hq2_10 hq2_01 hq3_00 hq3_10 hq3_01
            (a := a) (b := -b) (c := c) ha
            hrel2 hrel3 hpos' hdet hp hsocp)

theorem residual_eq_zero_of_equiv_const_x0_homQuadratics_plane_nontrivial
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {q2 q3 : Poly}
    (h0 : mapVec e.toAlgHom u 0 = (1 : Poly))
    (h1 : mapVec e.toAlgHom u 1 = x0)
    (h2 : mapVec e.toAlgHom u 2 = q2)
    (h3 : mapVec e.toAlgHom u 3 = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 = 0)
    (hplane :
      homQuadPlaneA q2 q3 ≠ 0 ∨
        homQuadPlaneB q2 q3 ≠ 0 ∨
          homQuadPlaneC q2 q3 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_homQuadratics_plane_nontrivial
      (c0 := stdRel0) (c1 := stdRel1) (c2 := stdRel2) (c3 := stdRel3)
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      (h0 := by simpa [stdRel0, Fin.sum_univ_four] using h0)
      (h1 := by simpa [stdRel1, Fin.sum_univ_four] using h1)
      (h2 := by simpa [stdRel2, Fin.sum_univ_four] using h2)
      (h3 := by simpa [stdRel3, Fin.sum_univ_four] using h3)
      hq2 hq3 hq2_00 hq2_10 hq2_01 hq3_00 hq3_10 hq3_01
      (hgram := stdRel23_gram_ne_zero)
      hplane hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_socp_of_eq_mix_mapVec_const_x0_homQuadratics_plane_nontrivial
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuarticSymm : ∀ {p : Poly}, IsQuartic p → IsQuartic (e.symm p))
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hMtM : M.transpose * M = 1)
    (hMMt : M * M.transpose = 1)
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 = 0)
    (hplane :
      homQuadPlaneA q2 q3 ≠ 0 ∨
        homQuadPlaneB q2 q3 ≠ 0 ∨
          homQuadPlaneC q2 q3 ≠ 0)
    (huRep : mix M.transpose (mapVec e.symm.toAlgHom u) = ![(1 : Poly), x0, q2, q3])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have huRepAdmissible : IsAdmissiblePoint (![(1 : Poly), x0, q2, q3] : RankFourVec) := by
    exact admissiblePoint_const_x0_pair hq2 hq3
  have hRep :
      ∀ {B0 : DotForm} [Fact B0.toQuadraticMap.PosDef] {p0 : Poly},
        IsSOSQuartic p0 → IsSOCP B0 p0 (![(1 : Poly), x0, q2, q3] : RankFourVec) →
          residual p0 (![(1 : Poly), x0, q2, q3] : RankFourVec) = 0 := by
    intro B0 _ p0 hp0 hsocp0
    exact residual_eq_zero_of_relations_const_x0_homQuadratics_plane_nontrivial
      (c0 := stdRel0) (c1 := stdRel1) (c2 := stdRel2) (c3 := stdRel3)
      (B := B0) (u := ![(1 : Poly), x0, q2, q3]) huRepAdmissible
      (h0 := by simp [stdRel0, Fin.sum_univ_four])
      (h1 := by simp [stdRel1, Fin.sum_univ_four, x0])
      (h2 := by simp [stdRel2, Fin.sum_univ_four])
      (h3 := by simp [stdRel3, Fin.sum_univ_four])
      hq2 hq3 hq2_00 hq2_10 hq2_01 hq3_00 hq3_10 hq3_01
      (hgram := stdRel23_gram_ne_zero)
      hplane hp0 hsocp0
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec
    (![(1 : Poly), x0, q2, q3])
    hRep e heQuad heQuadSymm heQuarticSymm M hMtM hMMt hB hp huRep hsocp

theorem residual_eq_zero_of_socp_of_eq_mix_affineEquiv_const_x0_homQuadratics_plane_nontrivial
    (A A' : Matrix (Fin 2) (Fin 2) ℝ) (b b' : Fin 2 → ℝ)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (hb : ∀ i, b' i + Matrix.mulVec A' b i = 0)
    (hb' : ∀ i, b i + Matrix.mulVec A b' i = 0)
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hMtM : M.transpose * M = 1)
    (hMMt : M * M.transpose = 1)
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 = 0)
    (hplane :
      homQuadPlaneA q2 q3 ≠ 0 ∨
        homQuadPlaneB q2 q3 ≠ 0 ∨
          homQuadPlaneC q2 q3 ≠ 0)
    (huRep :
      mix M.transpose
        (mapVec (affineEquiv A A' b b' hAA' hA'A hb hb').symm.toAlgHom u) =
          ![(1 : Poly), x0, q2, q3])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec_const_x0_homQuadratics_plane_nontrivial
    (e := affineEquiv A A' b b' hAA' hA'A hb hb')
    (heQuad := fun {_} hpq => isQuadratic_affineEquiv A A' b b' hAA' hA'A hb hb' hpq)
    (heQuadSymm := fun {_} hpq => isQuadratic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (heQuarticSymm := fun {_} hpq => isQuartic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (M := M) hMtM hMMt hB hp
    hq2 hq3 hq2_00 hq2_10 hq2_01 hq3_00 hq3_10 hq3_01
    hplane huRep hsocp

theorem residual_eq_zero_of_const_x0_x0sqTail_m02_nonzero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {q2 q3 : Poly}
    (h0 : u 0 = (1 : Poly))
    (h1 : u 1 = x0)
    (h2 : u 2 = q2)
    (h3 : u 3 = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq2_11 : MvPolynomial.coeff m11 q2 = 0)
    (hq2_02 : MvPolynomial.coeff m02 q2 = 0)
    (hq2_20 : MvPolynomial.coeff m20 q2 ≠ 0)
    (hq3_02 : MvPolynomial.coeff m02 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let t : ℝ := -(MvPolynomial.coeff m01 q3 / (2 * MvPolynomial.coeff m02 q3))
  let e : Poly ≃ₐ[ℝ] Poly := x1TranslateEquiv t
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := by
    exact isPositiveDefinite_dotTransport e (Fact.out : B.toQuadraticMap.PosDef)
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e)
      (heQuad := fun {_} hpq =>
        isQuadratic_affineEquiv
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1
          (x1TranslateVec t) (x1TranslateInvVec t)
          (by simp) (by simp)
          (x1TranslateInv_add_mulVec t) (x1Translate_add_mulVec_inv t)
          hpq)
      (heQuartic := fun {_} hpq =>
        isQuartic_affineEquiv
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1
          (x1TranslateVec t) (x1TranslateInvVec t)
          (by simp) (by simp)
          (x1TranslateInv_add_mulVec t) (x1Translate_add_mulVec_inv t)
          hpq)
      hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv
      (e := e)
      (he := fun {_} hpq =>
        isQuadratic_affineEquiv
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1
          (x1TranslateVec t) (x1TranslateInvVec t)
          (by simp) (by simp)
          (x1TranslateInv_add_mulVec t) (x1Translate_add_mulVec_inv t)
          hpq)
      hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv
      (e := e)
      (heSymm := fun {_} hpq =>
        isQuadratic_affineEquiv_symm
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1
          (x1TranslateVec t) (x1TranslateInvVec t)
          (by simp) (by simp)
          (x1TranslateInv_add_mulVec t) (x1Translate_add_mulVec_inv t)
          hpq)
      hsocp
  have he_one : e (1 : Poly) = (1 : Poly) := by
    simp [e]
  have he_x0 : e x0 = x0 := by
    rw [show e x0 = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) x0 by rfl]
    simp [affineHom_x1Translate_x0]
  let q2t : Poly := e q2
  let q3t : Poly := e q3
  let a3 : ℝ := MvPolynomial.coeff m10 q3t
  let b3q : ℝ := MvPolynomial.coeff m00 q3t
  let c3h : Fin 4 → ℝ := ![-b3q, -a3, 0, 1]
  let q3h : Poly := q3t - a3 • (x0 : Poly) - b3q • (1 : Poly)
  have h0' : ∑ i : Fin 4, stdRel0 i • mapVec e.toAlgHom u i = (1 : Poly) := by
    rw [Fin.sum_univ_four]
    simp [stdRel0, mapVec, h0, he_one]
  have h1' : ∑ i : Fin 4, stdRel1 i • mapVec e.toAlgHom u i = x0 := by
    calc
      ∑ i : Fin 4, stdRel1 i • mapVec e.toAlgHom u i = mapVec e.toAlgHom u 1 := by
        rw [Fin.sum_univ_four]
        simp [stdRel1]
      _ = e (u 1) := by simp [mapVec]
      _ = e x0 := by rw [h1]
      _ = x0 := he_x0
  have h2' : ∑ i : Fin 4, stdRel2 i • mapVec e.toAlgHom u i = q2t := by
    calc
      ∑ i : Fin 4, stdRel2 i • mapVec e.toAlgHom u i = mapVec e.toAlgHom u 2 := by
        rw [Fin.sum_univ_four]
        simp [stdRel2]
      _ = e (u 2) := by simp [mapVec]
      _ = q2t := by simp [q2t, h2]
  have h3' : ∑ i : Fin 4, c3h i • mapVec e.toAlgHom u i = q3h := by
    rw [Fin.sum_univ_four]
    have hu0' : mapVec e.toAlgHom u 0 = (1 : Poly) := by
      simp [mapVec, h0, he_one]
    have hu1' : mapVec e.toAlgHom u 1 = x0 := by
      simp [mapVec, h1, he_x0]
    have hu3' : mapVec e.toAlgHom u 3 = q3t := by
      simp [mapVec, h3, q3t]
    calc
      (-b3q) • mapVec e.toAlgHom u 0 + (-a3) • mapVec e.toAlgHom u 1 +
          (0 : ℝ) • mapVec e.toAlgHom u 2 + (1 : ℝ) • mapVec e.toAlgHom u 3
          = (-b3q) • (1 : Poly) + (-a3) • x0 + q3t := by
              rw [hu0', hu1', hu3']
              simp
      _ = q3h := by
            dsimp [q3h]
            rw [sub_eq_add_neg, sub_eq_add_neg]
            rw [show -(a3 • (x0 : Poly)) = (-a3) • x0 by simp,
              show -(b3q • (1 : Poly)) = (-b3q) • (1 : Poly) by simp]
            ac_rfl
  have hq2t : IsQuadratic q2t := by
    dsimp [q2t, e]
    change IsQuadratic
      (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) q2)
    exact isQuadratic_affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) hq2
  have hq3t : IsQuadratic q3t := by
    dsimp [q3t, e]
    change IsQuadratic
      (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) q3)
    exact isQuadratic_affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) hq3
  have hq3h : IsQuadratic q3h := by
    dsimp [q3h]
    have hx0 : IsQuadratic (x0 : Poly) := by
      simpa [x0] using (show IsQuadratic (MvPolynomial.X 0 : Poly) by
        simp [IsQuadratic])
    have h1poly : IsQuadratic (1 : Poly) := by
      simp [IsQuadratic]
    have htmp : IsQuadratic (q3t + (-a3) • (x0 : Poly)) := by
      simpa [a3] using isQuadratic_linearCombination_local hq3t hx0 1 (-a3)
    simpa [sub_eq_add_neg, add_assoc, b3q] using
      (isQuadratic_linearCombination_local htmp h1poly 1 (-b3q))
  have hq2t_00 : MvPolynomial.coeff m00 q2t = 0 := by
    dsimp [q2t]
    rw [show e q2 = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) q2 by rfl]
    rw [coeff_m00_affineHom_x1Translate hq2, hq2_00, hq2_01, hq2_02]
    ring
  have hq2t_10 : MvPolynomial.coeff m10 q2t = 0 := by
    dsimp [q2t]
    rw [show e q2 = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) q2 by rfl]
    rw [coeff_m10_affineHom_x1Translate hq2, hq2_10, hq2_11]
    ring
  have hq2t_01 : MvPolynomial.coeff m01 q2t = 0 := by
    dsimp [q2t]
    rw [show e q2 = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) q2 by rfl]
    rw [coeff_m01_affineHom_x1Translate hq2, hq2_01, hq2_02]
    ring
  have hq2t_11 : MvPolynomial.coeff m11 q2t = 0 := by
    dsimp [q2t]
    rw [show e q2 = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) q2 by rfl]
    rw [coeff_m11_affineHom_x1Translate hq2, hq2_11]
  have hq2t_02 : MvPolynomial.coeff m02 q2t = 0 := by
    dsimp [q2t]
    rw [show e q2 = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) q2 by rfl]
    rw [coeff_m02_affineHom_x1Translate hq2, hq2_02]
  have hq2t_20 : MvPolynomial.coeff m20 q2t ≠ 0 := by
    dsimp [q2t]
    rw [show e q2 = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) q2 by rfl]
    rw [coeff_m20_affineHom_x1Translate hq2]
    exact hq2_20
  have hq3t_01 : MvPolynomial.coeff m01 q3t = 0 := by
    dsimp [q3t, t]
    rw [show e q3 = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (x1TranslateVec (-(MvPolynomial.coeff m01 q3 / (2 * MvPolynomial.coeff m02 q3)))) q3 by rfl]
    exact coeff_m01_affineHom_x1Translate_kill hq3 hq3_02
  have hq3t_02 : MvPolynomial.coeff m02 q3t ≠ 0 := by
    dsimp [q3t]
    rw [show e q3 = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) q3 by rfl]
    rw [coeff_m02_affineHom_x1Translate hq3]
    exact hq3_02
  have hcoeff_x0_00 : MvPolynomial.coeff m00 (x0 : Poly) = 0 := by simp [x0, m00]
  have hcoeff_x0_10 : MvPolynomial.coeff m10 (x0 : Poly) = 1 := by simp [x0, m10]
  have hcoeff_x0_01 : MvPolynomial.coeff m01 (x0 : Poly) = 0 := by simp [x0, m01]
  have hcoeff_x0_02 : MvPolynomial.coeff m02 (x0 : Poly) = 0 := by simp [x0, m02]
  have hcoeff_one_00 : MvPolynomial.coeff m00 (1 : Poly) = 1 := by simp [m00]
  have hcoeff_one_10 : MvPolynomial.coeff m10 (1 : Poly) = 0 := by
    change MvPolynomial.coeff m10 (MvPolynomial.C (1 : ℝ)) = 0
    simpa [m10] using (MvPolynomial.coeff_C (σ := Fin 2) (R := ℝ) m10 (1 : ℝ))
  have hcoeff_one_01 : MvPolynomial.coeff m01 (1 : Poly) = 0 := by
    change MvPolynomial.coeff m01 (MvPolynomial.C (1 : ℝ)) = 0
    simpa [m01] using (MvPolynomial.coeff_C (σ := Fin 2) (R := ℝ) m01 (1 : ℝ))
  have hcoeff_one_02 : MvPolynomial.coeff m02 (1 : Poly) = 0 := by
    change MvPolynomial.coeff m02 (MvPolynomial.C (1 : ℝ)) = 0
    simpa [m02] using (MvPolynomial.coeff_C (σ := Fin 2) (R := ℝ) m02 (1 : ℝ))
  have hq3h_00 : MvPolynomial.coeff m00 q3h = 0 := by
    dsimp [q3h, a3, b3q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hcoeff_x0_00, hcoeff_one_00]
    simp
  have hq3h_10 : MvPolynomial.coeff m10 q3h = 0 := by
    dsimp [q3h, a3, b3q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hcoeff_x0_10, hcoeff_one_10]
    simp
  have hq3h_01 : MvPolynomial.coeff m01 q3h = 0 := by
    dsimp [q3h, a3, b3q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hq3t_01, hcoeff_x0_01, hcoeff_one_01]
    simp
  have hq3h_02 : MvPolynomial.coeff m02 q3h ≠ 0 := by
    dsimp [q3h, a3, b3q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hcoeff_x0_02, hcoeff_one_02]
    simpa using hq3t_02
  have hgram :
      (∑ i : Fin 4, (stdRel2 i) ^ 2) * (∑ i : Fin 4, (c3h i) ^ 2) -
        (∑ i : Fin 4, stdRel2 i * c3h i) ^ 2 ≠ 0 := by
    rw [Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four]
    have hpos : 0 < b3q ^ 2 + a3 ^ 2 + 1 := by
      positivity
    simp [stdRel2, c3h, pow_two]
    linarith
  have hplane :
      homQuadPlaneA q2t q3h ≠ 0 ∨
        homQuadPlaneB q2t q3h ≠ 0 ∨
          homQuadPlaneC q2t q3h ≠ 0 := by
    right
    left
    simpa [homQuadPlaneB, hq2t_02] using mul_ne_zero hq2t_20 hq3h_02
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_homQuadratics_plane_nontrivial
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      (c0 := stdRel0) (c1 := stdRel1) (c2 := stdRel2) (c3 := c3h)
      h0' h1' h2' h3' hq2t hq3h
      hq2t_00 hq2t_10 hq2t_01
      hq3h_00 hq3h_10 hq3h_01
      hgram hplane hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_equiv_const_x0_x0sqTail_m02_nonzero
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {q2 q3 : Poly}
    (h0 : mapVec e.toAlgHom u 0 = (1 : Poly))
    (h1 : mapVec e.toAlgHom u 1 = x0)
    (h2 : mapVec e.toAlgHom u 2 = q2)
    (h3 : mapVec e.toAlgHom u 3 = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq2_11 : MvPolynomial.coeff m11 q2 = 0)
    (hq2_02 : MvPolynomial.coeff m02 q2 = 0)
    (hq2_20 : MvPolynomial.coeff m20 q2 ≠ 0)
    (hq3_02 : MvPolynomial.coeff m02 q3 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_const_x0_x0sqTail_m02_nonzero
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0 h1 h2 h3 hq2 hq3
      hq2_00 hq2_10 hq2_01 hq2_11 hq2_02 hq2_20
      hq3_02 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_socp_of_eq_mix_mapVec_const_x0_x0sqTail_m02_nonzero
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuarticSymm : ∀ {p : Poly}, IsQuartic p → IsQuartic (e.symm p))
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hMtM : M.transpose * M = 1)
    (hMMt : M * M.transpose = 1)
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq2_11 : MvPolynomial.coeff m11 q2 = 0)
    (hq2_02 : MvPolynomial.coeff m02 q2 = 0)
    (hq2_20 : MvPolynomial.coeff m20 q2 ≠ 0)
    (hq3_02 : MvPolynomial.coeff m02 q3 ≠ 0)
    (huRep : mix M.transpose (mapVec e.symm.toAlgHom u) = ![(1 : Poly), x0, q2, q3])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have huRepAdmissible : IsAdmissiblePoint (![(1 : Poly), x0, q2, q3] : RankFourVec) := by
    exact admissiblePoint_const_x0_pair hq2 hq3
  have hRep :
      ∀ {B0 : DotForm} [Fact B0.toQuadraticMap.PosDef] {p0 : Poly},
        IsSOSQuartic p0 → IsSOCP B0 p0 (![(1 : Poly), x0, q2, q3] : RankFourVec) →
          residual p0 (![(1 : Poly), x0, q2, q3] : RankFourVec) = 0 := by
    intro B0 _ p0 hp0 hsocp0
    exact residual_eq_zero_of_const_x0_x0sqTail_m02_nonzero
      (B := B0) (u := ![(1 : Poly), x0, q2, q3]) huRepAdmissible
      (by simp) (by simp [x0]) (by simp) (by simp)
      hq2 hq3
      hq2_00 hq2_10 hq2_01 hq2_11 hq2_02 hq2_20
      hq3_02 hp0 hsocp0
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec
    (![(1 : Poly), x0, q2, q3])
    hRep e heQuad heQuadSymm heQuarticSymm M hMtM hMMt hB hp huRep hsocp

theorem residual_eq_zero_of_socp_of_eq_mix_affineEquiv_const_x0_x0sqTail_m02_nonzero
    (A A' : Matrix (Fin 2) (Fin 2) ℝ) (b b' : Fin 2 → ℝ)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (hb : ∀ i, b' i + Matrix.mulVec A' b i = 0)
    (hb' : ∀ i, b i + Matrix.mulVec A b' i = 0)
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hMtM : M.transpose * M = 1)
    (hMMt : M * M.transpose = 1)
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq2_11 : MvPolynomial.coeff m11 q2 = 0)
    (hq2_02 : MvPolynomial.coeff m02 q2 = 0)
    (hq2_20 : MvPolynomial.coeff m20 q2 ≠ 0)
    (hq3_02 : MvPolynomial.coeff m02 q3 ≠ 0)
    (huRep :
      mix M.transpose
        (mapVec (affineEquiv A A' b b' hAA' hA'A hb hb').symm.toAlgHom u) =
          ![(1 : Poly), x0, q2, q3])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec_const_x0_x0sqTail_m02_nonzero
    (e := affineEquiv A A' b b' hAA' hA'A hb hb')
    (heQuad := fun {_} hpq => isQuadratic_affineEquiv A A' b b' hAA' hA'A hb hb' hpq)
    (heQuadSymm := fun {_} hpq => isQuadratic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (heQuarticSymm := fun {_} hpq => isQuartic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (M := M) hMtM hMMt hB hp
    hq2 hq3 hq2_00 hq2_10 hq2_01 hq2_11 hq2_02 hq2_20
    hq3_02 huRep hsocp

theorem residual_eq_zero_of_const_x0_x0sqTail_m11_nonzero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {q2 q3 : Poly}
    (h0 : u 0 = (1 : Poly))
    (h1 : u 1 = x0)
    (h2 : u 2 = q2)
    (h3 : u 3 = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq2_11 : MvPolynomial.coeff m11 q2 = 0)
    (hq2_02 : MvPolynomial.coeff m02 q2 = 0)
    (hq2_20 : MvPolynomial.coeff m20 q2 ≠ 0)
    (hq3_11 : MvPolynomial.coeff m11 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let t : ℝ := -(MvPolynomial.coeff m01 q3 / MvPolynomial.coeff m11 q3)
  let e : Poly ≃ₐ[ℝ] Poly := x0TranslateEquiv t
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := by
    exact isPositiveDefinite_dotTransport e (Fact.out : B.toQuadraticMap.PosDef)
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e)
      (heQuad := fun {_} hpq =>
        isQuadratic_affineEquiv
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1
          (x0TranslateVec t) (x0TranslateInvVec t)
          (by simp) (by simp)
          (x0TranslateInv_add_mulVec t) (x0Translate_add_mulVec_inv t)
          hpq)
      (heQuartic := fun {_} hpq =>
        isQuartic_affineEquiv
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1
          (x0TranslateVec t) (x0TranslateInvVec t)
          (by simp) (by simp)
          (x0TranslateInv_add_mulVec t) (x0Translate_add_mulVec_inv t)
          hpq)
      hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv
      (e := e)
      (he := fun {_} hpq =>
        isQuadratic_affineEquiv
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1
          (x0TranslateVec t) (x0TranslateInvVec t)
          (by simp) (by simp)
          (x0TranslateInv_add_mulVec t) (x0Translate_add_mulVec_inv t)
          hpq)
      hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv
      (e := e)
      (heSymm := fun {_} hpq =>
        isQuadratic_affineEquiv_symm
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1
          (x0TranslateVec t) (x0TranslateInvVec t)
          (by simp) (by simp)
          (x0TranslateInv_add_mulVec t) (x0Translate_add_mulVec_inv t)
          hpq)
      hsocp
  have he_one : e (1 : Poly) = (1 : Poly) := by
    simp [e]
  have he_x0 : e x0 = MvPolynomial.C t + x0 := by
    rw [show e x0 = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec t) x0 by rfl]
    simp [affineHom_x0Translate_x0]
  let q2t : Poly := e q2
  let q3t : Poly := e q3
  let a2 : ℝ := MvPolynomial.coeff m10 q2t
  let b2q : ℝ := MvPolynomial.coeff m00 q2t
  let a3 : ℝ := MvPolynomial.coeff m10 q3t
  let b3q : ℝ := MvPolynomial.coeff m00 q3t
  let q2h : Poly := q2t - a2 • (x0 : Poly) - b2q • (1 : Poly)
  let q3h : Poly := q3t - a3 • (x0 : Poly) - b3q • (1 : Poly)
  let c0' : Fin 4 → ℝ := ![1, 0, 0, 0]
  let c1' : Fin 4 → ℝ := ![-t, 1, 0, 0]
  let c2' : Fin 4 → ℝ := ![t * a2 - b2q, -a2, 1, 0]
  let c3' : Fin 4 → ℝ := ![t * a3 - b3q, -a3, 0, 1]
  have h0' : ∑ i : Fin 4, c0' i • mapVec e.toAlgHom u i = (1 : Poly) := by
    rw [Fin.sum_univ_four]
    simp [c0', mapVec, h0, he_one]
  have h1' : ∑ i : Fin 4, c1' i • mapVec e.toAlgHom u i = x0 := by
    rw [Fin.sum_univ_four]
    change (-t) • mapVec e.toAlgHom u 0 + (1 : ℝ) • mapVec e.toAlgHom u 1 +
        (0 : ℝ) • mapVec e.toAlgHom u 2 + (0 : ℝ) • mapVec e.toAlgHom u 3 = x0
    calc
      (-t) • mapVec e.toAlgHom u 0 + (1 : ℝ) • mapVec e.toAlgHom u 1 +
          (0 : ℝ) • mapVec e.toAlgHom u 2 + (0 : ℝ) • mapVec e.toAlgHom u 3
          = -(t • (1 : Poly)) + (MvPolynomial.C t + x0) := by
              simp [mapVec, h0, h1, he_one, he_x0]
      _ = x0 := by
            simp [MvPolynomial.smul_eq_C_mul]
  have hq2t : IsQuadratic q2t := by
    dsimp [q2t, e]
    change IsQuadratic
      (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec t) q2)
    exact isQuadratic_affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec t) hq2
  have hq3t : IsQuadratic q3t := by
    dsimp [q3t, e]
    change IsQuadratic
      (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec t) q3)
    exact isQuadratic_affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec t) hq3
  have hq2t_11 :
      MvPolynomial.coeff m11 q2t = 0 := by
    dsimp [q2t]
    rw [show e q2 = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec t) q2 by rfl]
    rw [coeff_m11_affineHom_x0Translate hq2, hq2_11]
  have hq2t_02 :
      MvPolynomial.coeff m02 q2t = 0 := by
    dsimp [q2t]
    rw [show e q2 = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec t) q2 by rfl]
    rw [coeff_m02_affineHom_x0Translate hq2, hq2_02]
  have hq2t_01 :
      MvPolynomial.coeff m01 q2t = 0 := by
    dsimp [q2t]
    rw [show e q2 = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec t) q2 by rfl]
    rw [coeff_m01_affineHom_x0Translate hq2, hq2_01, hq2_11]
    ring
  have hq2t_20 :
      MvPolynomial.coeff m20 q2t = MvPolynomial.coeff m20 q2 := by
    dsimp [q2t]
    rw [show e q2 = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec t) q2 by rfl]
    rw [quadratic_eq_quadForm hq2, affineHom_x0Translate_quadForm]
    simp
  have hq3t_01 :
      MvPolynomial.coeff m01 q3t = 0 := by
    dsimp [q3t, t]
    rw [show e q3 = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (x0TranslateVec (-(MvPolynomial.coeff m01 q3 / MvPolynomial.coeff m11 q3))) q3 by rfl]
    rw [coeff_m01_affineHom_x0Translate hq3]
    field_simp [hq3_11]
    ring
  have hq2' : ∑ i : Fin 4, c2' i • mapVec e.toAlgHom u i = q2h := by
    rw [Fin.sum_univ_four]
    have hu0' : mapVec e.toAlgHom u 0 = (1 : Poly) := by
      simp [mapVec, h0, he_one]
    have hu1' : mapVec e.toAlgHom u 1 = MvPolynomial.C t + x0 := by
      simp [mapVec, h1, he_x0]
    have hu2' : mapVec e.toAlgHom u 2 = q2t := by
      simp [mapVec, h2, q2t]
    calc
      (t * a2 - b2q) • mapVec e.toAlgHom u 0 + (-a2) • mapVec e.toAlgHom u 1 +
          (1 : ℝ) • mapVec e.toAlgHom u 2 + (0 : ℝ) • mapVec e.toAlgHom u 3
          = (t * a2 - b2q) • (1 : Poly) + (-a2) • (MvPolynomial.C t + x0) + q2t := by
              rw [hu0', hu1', hu2']
              simp
      _ = q2h := by
            dsimp [q2h]
            have hC :
                (-a2) • (MvPolynomial.C t : Poly) = (-a2 * t) • (1 : Poly) := by
              calc
                (-a2) • (MvPolynomial.C t : Poly) = MvPolynomial.C (-a2) * MvPolynomial.C t := by
                  rw [MvPolynomial.smul_eq_C_mul]
                _ = MvPolynomial.C (-a2 * t) := by rw [← MvPolynomial.C_mul]
                _ = (-a2 * t) • (1 : Poly) := by
                  rw [MvPolynomial.smul_eq_C_mul, mul_one]
            have hconst :
                (t * a2 - b2q) • (1 : Poly) + (-a2 * t) • (1 : Poly) =
                  (-b2q) • (1 : Poly) := by
              rw [← add_smul]
              congr 1
              ring
            calc
              (t * a2 - b2q) • (1 : Poly) + (-a2) • (MvPolynomial.C t + x0) + q2t
                  =
                    (t * a2 - b2q) • (1 : Poly) +
                      ((-a2 * t) • (1 : Poly) + (-a2) • x0) + q2t := by
                        rw [smul_add, hC]
              _ = ((t * a2 - b2q) • (1 : Poly) + (-a2 * t) • (1 : Poly)) +
                    ((-a2) • x0 + q2t) := by
                      rw [← add_assoc, add_assoc]
              _ = (-b2q) • (1 : Poly) + (-a2) • x0 + q2t := by
                    rw [hconst, add_assoc]
              _ = q2t - a2 • (x0 : Poly) - b2q • (1 : Poly) := by
                    rw [sub_eq_add_neg, sub_eq_add_neg]
                    rw [show -(a2 • (x0 : Poly)) = (-a2) • x0 by simp,
                      show -(b2q • (1 : Poly)) = (-b2q) • (1 : Poly) by simp]
                    ac_rfl
              _ = q2h := by rfl
  have hq3' : ∑ i : Fin 4, c3' i • mapVec e.toAlgHom u i = q3h := by
    rw [Fin.sum_univ_four]
    have hu0' : mapVec e.toAlgHom u 0 = (1 : Poly) := by
      simp [mapVec, h0, he_one]
    have hu1' : mapVec e.toAlgHom u 1 = MvPolynomial.C t + x0 := by
      simp [mapVec, h1, he_x0]
    have hu3' : mapVec e.toAlgHom u 3 = q3t := by
      simp [mapVec, h3, q3t]
    calc
      (t * a3 - b3q) • mapVec e.toAlgHom u 0 + (-a3) • mapVec e.toAlgHom u 1 +
          (0 : ℝ) • mapVec e.toAlgHom u 2 + (1 : ℝ) • mapVec e.toAlgHom u 3
          = (t * a3 - b3q) • (1 : Poly) + (-a3) • (MvPolynomial.C t + x0) + q3t := by
              rw [hu0', hu1', hu3']
              simp
      _ = q3h := by
            dsimp [q3h]
            have hC :
                (-a3) • (MvPolynomial.C t : Poly) = (-a3 * t) • (1 : Poly) := by
              calc
                (-a3) • (MvPolynomial.C t : Poly) = MvPolynomial.C (-a3) * MvPolynomial.C t := by
                  rw [MvPolynomial.smul_eq_C_mul]
                _ = MvPolynomial.C (-a3 * t) := by rw [← MvPolynomial.C_mul]
                _ = (-a3 * t) • (1 : Poly) := by
                  rw [MvPolynomial.smul_eq_C_mul, mul_one]
            have hconst :
                (t * a3 - b3q) • (1 : Poly) + (-a3 * t) • (1 : Poly) =
                  (-b3q) • (1 : Poly) := by
              rw [← add_smul]
              congr 1
              ring
            calc
              (t * a3 - b3q) • (1 : Poly) + (-a3) • (MvPolynomial.C t + x0) + q3t
                  =
                    (t * a3 - b3q) • (1 : Poly) +
                      ((-a3 * t) • (1 : Poly) + (-a3) • x0) + q3t := by
                        rw [smul_add, hC]
              _ = ((t * a3 - b3q) • (1 : Poly) + (-a3 * t) • (1 : Poly)) +
                    ((-a3) • x0 + q3t) := by
                      rw [← add_assoc, add_assoc]
              _ = (-b3q) • (1 : Poly) + (-a3) • x0 + q3t := by
                    rw [hconst, add_assoc]
              _ = q3t - a3 • (x0 : Poly) - b3q • (1 : Poly) := by
                    rw [sub_eq_add_neg, sub_eq_add_neg]
                    rw [show -(a3 • (x0 : Poly)) = (-a3) • x0 by simp,
                      show -(b3q • (1 : Poly)) = (-b3q) • (1 : Poly) by simp]
                    ac_rfl
              _ = q3h := by rfl
  have hq2h : IsQuadratic q2h := by
    dsimp [q2h]
    have hx0 : IsQuadratic (x0 : Poly) := by
      simpa [x0] using (show IsQuadratic (MvPolynomial.X 0 : Poly) by
        simp [IsQuadratic])
    have h1poly : IsQuadratic (1 : Poly) := by
      simp [IsQuadratic]
    have htmp : IsQuadratic (q2t + (-a2) • (x0 : Poly)) := by
      simpa using isQuadratic_linearCombination_local hq2t hx0 1 (-a2)
    simpa [sub_eq_add_neg, add_assoc] using
      (isQuadratic_linearCombination_local htmp h1poly 1 (-b2q))
  have hq3h : IsQuadratic q3h := by
    dsimp [q3h]
    have hx0 : IsQuadratic (x0 : Poly) := by
      simpa [x0] using (show IsQuadratic (MvPolynomial.X 0 : Poly) by
        simp [IsQuadratic])
    have h1poly : IsQuadratic (1 : Poly) := by
      simp [IsQuadratic]
    have htmp : IsQuadratic (q3t + (-a3) • (x0 : Poly)) := by
      simpa using isQuadratic_linearCombination_local hq3t hx0 1 (-a3)
    simpa [sub_eq_add_neg, add_assoc] using
      (isQuadratic_linearCombination_local htmp h1poly 1 (-b3q))
  have hcoeff_x0_00 : MvPolynomial.coeff m00 (x0 : Poly) = 0 := by simp [x0, m00]
  have hcoeff_x0_10 : MvPolynomial.coeff m10 (x0 : Poly) = 1 := by simp [x0, m10]
  have hcoeff_x0_01 : MvPolynomial.coeff m01 (x0 : Poly) = 0 := by simp [x0, m01]
  have hcoeff_x0_11 : MvPolynomial.coeff m11 (x0 : Poly) = 0 := by
    simpa [x0, m10] using (MvPolynomial.coeff_X' (σ := Fin 2) (R := ℝ) 0 m11)
  have hcoeff_x0_02 : MvPolynomial.coeff m02 (x0 : Poly) = 0 := by simp [x0, m02]
  have hcoeff_x0_20 : MvPolynomial.coeff m20 (x0 : Poly) = 0 := by simp [x0, m20]
  have hcoeff_one_00 : MvPolynomial.coeff m00 (1 : Poly) = 1 := by simp [m00]
  have hcoeff_one_10 : MvPolynomial.coeff m10 (1 : Poly) = 0 := by
    change MvPolynomial.coeff m10 (MvPolynomial.C (1 : ℝ)) = 0
    simpa [m10] using (MvPolynomial.coeff_C (σ := Fin 2) (R := ℝ) m10 (1 : ℝ))
  have hcoeff_one_01 : MvPolynomial.coeff m01 (1 : Poly) = 0 := by
    change MvPolynomial.coeff m01 (MvPolynomial.C (1 : ℝ)) = 0
    simpa [m01] using (MvPolynomial.coeff_C (σ := Fin 2) (R := ℝ) m01 (1 : ℝ))
  have hcoeff_one_11 : MvPolynomial.coeff m11 (1 : Poly) = 0 := by
    change MvPolynomial.coeff m11 (MvPolynomial.C (1 : ℝ)) = 0
    simpa [m11] using (MvPolynomial.coeff_C (σ := Fin 2) (R := ℝ) m11 (1 : ℝ))
  have hcoeff_one_02 : MvPolynomial.coeff m02 (1 : Poly) = 0 := by
    change MvPolynomial.coeff m02 (MvPolynomial.C (1 : ℝ)) = 0
    simpa [m02] using (MvPolynomial.coeff_C (σ := Fin 2) (R := ℝ) m02 (1 : ℝ))
  have hcoeff_one_20 : MvPolynomial.coeff m20 (1 : Poly) = 0 := by
    change MvPolynomial.coeff m20 (MvPolynomial.C (1 : ℝ)) = 0
    simpa [m20] using (MvPolynomial.coeff_C (σ := Fin 2) (R := ℝ) m20 (1 : ℝ))
  have hq2h_00 : MvPolynomial.coeff m00 q2h = 0 := by
    dsimp [q2h, a2, b2q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hcoeff_x0_00, hcoeff_one_00]
    simp
  have hq2h_10 : MvPolynomial.coeff m10 q2h = 0 := by
    dsimp [q2h, a2, b2q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hcoeff_x0_10, hcoeff_one_10]
    simp
  have hq2h_01 : MvPolynomial.coeff m01 q2h = 0 := by
    dsimp [q2h, a2, b2q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hq2t_01, hcoeff_x0_01, hcoeff_one_01]
    simp
  have hq2h_11 : MvPolynomial.coeff m11 q2h = 0 := by
    dsimp [q2h, a2, b2q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hq2t_11, hcoeff_x0_11, hcoeff_one_11]
    simp
  have hq3h_00 : MvPolynomial.coeff m00 q3h = 0 := by
    dsimp [q3h, a3, b3q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hcoeff_x0_00, hcoeff_one_00]
    simp
  have hq3h_10 : MvPolynomial.coeff m10 q3h = 0 := by
    dsimp [q3h, a3, b3q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hcoeff_x0_10, hcoeff_one_10]
    simp
  have hq3h_01 : MvPolynomial.coeff m01 q3h = 0 := by
    dsimp [q3h, a3, b3q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hq3t_01, hcoeff_x0_01, hcoeff_one_01]
    simp
  have hq2h_20 :
      MvPolynomial.coeff m20 q2h = MvPolynomial.coeff m20 q2 := by
    dsimp [q2h, a2, b2q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hq2t_20, hcoeff_x0_20, hcoeff_one_20]
    simp
  have hq3h_11 :
      MvPolynomial.coeff m11 q3h = MvPolynomial.coeff m11 q3 := by
    dsimp [q3h, a3, b3q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul]
    have hq3t_11 :
        MvPolynomial.coeff m11 q3t = MvPolynomial.coeff m11 q3 := by
      dsimp [q3t]
      rw [show e q3 = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec t) q3 by rfl]
      rw [coeff_m11_affineHom_x0Translate hq3]
    rw [hq3t_11, hcoeff_x0_11, hcoeff_one_11]
    simp
  have hgram :
      (∑ i : Fin 4, (c2' i) ^ 2) * (∑ i : Fin 4, (c3' i) ^ 2) -
        (∑ i : Fin 4, c2' i * c3' i) ^ 2 ≠ 0 := by
    have hEq :
        (∑ i : Fin 4, (c2' i) ^ 2) * (∑ i : Fin 4, (c3' i) ^ 2) -
            (∑ i : Fin 4, c2' i * c3' i) ^ 2 =
          ((t * a2 - b2q) ^ 2 + a2 ^ 2 + 1) *
              ((t * a3 - b3q) ^ 2 + a3 ^ 2 + 1) -
            ((t * a2 - b2q) * (t * a3 - b3q) + a2 * a3) ^ 2 := by
      rw [Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four]
      simp [c2', c3', pow_two]
    rw [hEq]
    exact coordTailCorrectedGram_ne_zero (t * a2 - b2q) a2 (t * a3 - b3q) a3
  have hplane :
      homQuadPlaneA q2h q3h ≠ 0 ∨
        homQuadPlaneB q2h q3h ≠ 0 ∨
          homQuadPlaneC q2h q3h ≠ 0 := by
    right
    right
    have h20 :
        MvPolynomial.coeff m20 q2h ≠ 0 := by
      rw [hq2h_20]
      exact hq2_20
    have h11 :
        MvPolynomial.coeff m11 q3h ≠ 0 := by
      rw [hq3h_11]
      exact hq3_11
    simpa [homQuadPlaneC, hq2h_11] using mul_ne_zero h20 h11
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_homQuadratics_plane_nontrivial
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      (c0 := c0') (c1 := c1') (c2 := c2') (c3 := c3')
      h0' h1' hq2' hq3' hq2h hq3h
      hq2h_00 hq2h_10 hq2h_01
      hq3h_00 hq3h_10 hq3h_01
      hgram hplane hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_equiv_const_x0_x0sqTail_m11_nonzero
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {q2 q3 : Poly}
    (h0 : mapVec e.toAlgHom u 0 = (1 : Poly))
    (h1 : mapVec e.toAlgHom u 1 = x0)
    (h2 : mapVec e.toAlgHom u 2 = q2)
    (h3 : mapVec e.toAlgHom u 3 = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq2_11 : MvPolynomial.coeff m11 q2 = 0)
    (hq2_02 : MvPolynomial.coeff m02 q2 = 0)
    (hq2_20 : MvPolynomial.coeff m20 q2 ≠ 0)
    (hq3_11 : MvPolynomial.coeff m11 q3 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_const_x0_x0sqTail_m11_nonzero
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0 h1 h2 h3 hq2 hq3
      hq2_01 hq2_11 hq2_02 hq2_20 hq3_11 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_socp_of_eq_mix_mapVec_const_x0_x0sqTail_m11_nonzero
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuarticSymm : ∀ {p : Poly}, IsQuartic p → IsQuartic (e.symm p))
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hMtM : M.transpose * M = 1)
    (hMMt : M * M.transpose = 1)
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq2_11 : MvPolynomial.coeff m11 q2 = 0)
    (hq2_02 : MvPolynomial.coeff m02 q2 = 0)
    (hq2_20 : MvPolynomial.coeff m20 q2 ≠ 0)
    (hq3_11 : MvPolynomial.coeff m11 q3 ≠ 0)
    (huRep : mix M.transpose (mapVec e.symm.toAlgHom u) = ![(1 : Poly), x0, q2, q3])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have huRepAdmissible : IsAdmissiblePoint (![(1 : Poly), x0, q2, q3] : RankFourVec) := by
    exact admissiblePoint_const_x0_pair hq2 hq3
  have hRep :
      ∀ {B0 : DotForm} [Fact B0.toQuadraticMap.PosDef] {p0 : Poly},
        IsSOSQuartic p0 → IsSOCP B0 p0 (![(1 : Poly), x0, q2, q3] : RankFourVec) →
          residual p0 (![(1 : Poly), x0, q2, q3] : RankFourVec) = 0 := by
    intro B0 _ p0 hp0 hsocp0
    exact residual_eq_zero_of_const_x0_x0sqTail_m11_nonzero
      (B := B0) (u := ![(1 : Poly), x0, q2, q3]) huRepAdmissible
      (by simp) (by simp [x0]) (by simp) (by simp)
      hq2 hq3 hq2_01 hq2_11 hq2_02 hq2_20 hq3_11 hp0 hsocp0
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec
    (![(1 : Poly), x0, q2, q3])
    hRep e heQuad heQuadSymm heQuarticSymm M hMtM hMMt hB hp huRep hsocp

theorem residual_eq_zero_of_socp_of_eq_mix_affineEquiv_const_x0_x0sqTail_m11_nonzero
    (A A' : Matrix (Fin 2) (Fin 2) ℝ) (b b' : Fin 2 → ℝ)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (hb : ∀ i, b' i + Matrix.mulVec A' b i = 0)
    (hb' : ∀ i, b i + Matrix.mulVec A b' i = 0)
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hMtM : M.transpose * M = 1)
    (hMMt : M * M.transpose = 1)
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq2_11 : MvPolynomial.coeff m11 q2 = 0)
    (hq2_02 : MvPolynomial.coeff m02 q2 = 0)
    (hq2_20 : MvPolynomial.coeff m20 q2 ≠ 0)
    (hq3_11 : MvPolynomial.coeff m11 q3 ≠ 0)
    (huRep :
      mix M.transpose
        (mapVec (affineEquiv A A' b b' hAA' hA'A hb hb').symm.toAlgHom u) =
          ![(1 : Poly), x0, q2, q3])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec_const_x0_x0sqTail_m11_nonzero
    (e := affineEquiv A A' b b' hAA' hA'A hb hb')
    (heQuad := fun {_} hpq => isQuadratic_affineEquiv A A' b b' hAA' hA'A hb hb' hpq)
    (heQuadSymm := fun {_} hpq => isQuadratic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (heQuarticSymm := fun {_} hpq => isQuartic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (M := M) hMtM hMMt hB hp
    hq2 hq3 hq2_01 hq2_11 hq2_02 hq2_20 hq3_11 huRep hsocp

theorem residual_eq_zero_of_const_x0_x0sqTail_m11_m02_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {q2 q3 : Poly}
    (h0 : u 0 = (1 : Poly))
    (h1 : u 1 = x0)
    (h2 : u 2 = q2)
    (h3 : u 3 = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq2_11 : MvPolynomial.coeff m11 q2 = 0)
    (hq2_02 : MvPolynomial.coeff m02 q2 = 0)
    (hq2_20 : MvPolynomial.coeff m20 q2 ≠ 0)
    (hq3_11 : MvPolynomial.coeff m11 q3 = 0)
    (hq3_02 : MvPolynomial.coeff m02 q3 = 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let a : ℝ := MvPolynomial.coeff m20 q3 / MvPolynomial.coeff m20 q2
  let q : Poly := q3 - a • q2
  have hq : IsQuadratic q := by
    dsimp [q]
    simpa [sub_eq_add_neg, add_comm] using isQuadratic_linearCombination_local hq3 hq2 1 (-a)
  have hq_20 : MvPolynomial.coeff m20 q = 0 := by
    dsimp [q, a]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_smul]
    have hmul :
        (MvPolynomial.coeff m20 q3 / MvPolynomial.coeff m20 q2) •
            MvPolynomial.coeff m20 q2 =
          MvPolynomial.coeff m20 q3 := by
      simpa [smul_eq_mul] using
        (show
          (MvPolynomial.coeff m20 q3 / MvPolynomial.coeff m20 q2) *
              MvPolynomial.coeff m20 q2 =
            MvPolynomial.coeff m20 q3 by
              field_simp [hq2_20])
    rw [hmul]
    simp
  have hq_11 : MvPolynomial.coeff m11 q = 0 := by
    dsimp [q, a]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, hq3_11, hq2_11]
    simp
  have hq_02 : MvPolynomial.coeff m02 q = 0 := by
    dsimp [q, a]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, hq3_02, hq2_02]
    simp
  have hq_01 :
      MvPolynomial.coeff m01 q = MvPolynomial.coeff m01 q3 := by
    dsimp [q, a]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, hq2_01]
    simp
  have hqrel :
      ∑ i : Fin 4, (![0, 0, -a, 1] : Fin 4 → ℝ) i • u i = q := by
    rw [Fin.sum_univ_four]
    simpa [q, a, sub_eq_add_neg, add_comm] using
      (show (0 : ℝ) • u 0 + (0 : ℝ) • u 1 + (-a) • u 2 + (1 : ℝ) • u 3 = q by
        simp [h2, h3, q, sub_eq_add_neg, add_comm])
  by_cases hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0
  · exact residual_eq_zero_of_relations_const_x0_affineTail
      (B := B) (u := u) hu
      (c0 := stdRel0) (c1 := stdRel1)
      (c2 := ![0, 0, -a, 1])
      (h0 := by simpa [stdRel0, Fin.sum_univ_four] using h0)
      (h1 := by simpa [stdRel1, Fin.sum_univ_four] using h1)
      (h2 := hqrel)
      hq hq_20 hq_11 hq_02 (by simpa [hq_01] using hq3_01) hp hsocp
  · have hq_01_zero : MvPolynomial.coeff m01 q = 0 := by
      have hq3_01_zero : MvPolynomial.coeff m01 q3 = 0 := by
        by_contra hne
        exact hq3_01 hne
      rw [hq_01, hq3_01_zero]
    have hq_aff :
        q =
          MvPolynomial.coeff m00 q • (1 : Poly) +
            MvPolynomial.coeff m10 q • x0 := by
      have hbase := affineX1_eq_of_quadratic_coeffs_zero hq hq_20 hq_11 hq_02
      rw [hq_01_zero] at hbase
      simpa [add_assoc] using hbase
    let c : Fin 4 → ℝ :=
      ![-MvPolynomial.coeff m00 q, -MvPolynomial.coeff m10 q, -a, 1]
    have hrel : ∑ i : Fin 4, c i • u i = 0 := by
      have h0rel : ∑ i : Fin 4, stdRel0 i • u i = (1 : Poly) := by
        simpa [stdRel0, Fin.sum_univ_four] using h0
      have h1rel : ∑ i : Fin 4, stdRel1 i • u i = x0 := by
        simpa [stdRel1, Fin.sum_univ_four] using h1
      have htmp :
          ∑ i : Fin 4,
              ((-(MvPolynomial.coeff m00 q)) * stdRel0 i +
                (-(MvPolynomial.coeff m10 q)) * stdRel1 i) • u i =
            (-(MvPolynomial.coeff m00 q)) • (1 : Poly) +
              (-(MvPolynomial.coeff m10 q)) • x0 := by
        simpa using relation_linearCombination h0rel h1rel
          (-(MvPolynomial.coeff m00 q)) (-(MvPolynomial.coeff m10 q))
      have hcomb :
          ∑ i : Fin 4,
              ((![0, 0, -a, 1] : Fin 4 → ℝ) i +
                ((-(MvPolynomial.coeff m00 q)) * stdRel0 i +
                  (-(MvPolynomial.coeff m10 q)) * stdRel1 i)) • u i =
            q + ((-(MvPolynomial.coeff m00 q)) • (1 : Poly) +
              (-(MvPolynomial.coeff m10 q)) • x0) := by
        simpa using relation_linearCombination hqrel htmp 1 1
      calc
        ∑ i : Fin 4, c i • u i
            = ∑ i : Fin 4,
                ((![0, 0, -a, 1] : Fin 4 → ℝ) i +
                  ((-(MvPolynomial.coeff m00 q)) * stdRel0 i +
                    (-(MvPolynomial.coeff m10 q)) * stdRel1 i)) • u i := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  fin_cases i <;> simp [c, stdRel0, stdRel1]
        _ = q + ((-(MvPolynomial.coeff m00 q)) • (1 : Poly) +
              (-(MvPolynomial.coeff m10 q)) • x0) := hcomb
        _ = 0 := by
              nth_rewrite 1 [hq_aff]
              calc
                (MvPolynomial.coeff m00 q • (1 : Poly) + MvPolynomial.coeff m10 q • x0) +
                    ((-(MvPolynomial.coeff m00 q)) • (1 : Poly) +
                      (-(MvPolynomial.coeff m10 q)) • x0)
                    =
                  ((MvPolynomial.coeff m00 q • (1 : Poly) + (-(MvPolynomial.coeff m00 q)) • (1 : Poly)) +
                    (MvPolynomial.coeff m10 q • x0 + (-(MvPolynomial.coeff m10 q)) • x0)) := by
                      abel_nf
                _ = 0 := by
                      rw [← add_smul, ← add_smul]
                      simp
    have hc : c ≠ 0 := by
      intro hc0
      have hc3 := congrArg (fun z : Fin 4 → ℝ => z 3) hc0
      simp [c] at hc3
    exact residual_eq_zero_of_constant_relation (B := B) (u := u) hu hrel hc hp hsocp

theorem residual_eq_zero_of_equiv_const_x0_x0sqTail_m11_m02_zero
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {q2 q3 : Poly}
    (h0 : mapVec e.toAlgHom u 0 = (1 : Poly))
    (h1 : mapVec e.toAlgHom u 1 = x0)
    (h2 : mapVec e.toAlgHom u 2 = q2)
    (h3 : mapVec e.toAlgHom u 3 = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq2_11 : MvPolynomial.coeff m11 q2 = 0)
    (hq2_02 : MvPolynomial.coeff m02 q2 = 0)
    (hq2_20 : MvPolynomial.coeff m20 q2 ≠ 0)
    (hq3_11 : MvPolynomial.coeff m11 q3 = 0)
    (hq3_02 : MvPolynomial.coeff m02 q3 = 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_const_x0_x0sqTail_m11_m02_zero
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0 h1 h2 h3 hq2 hq3
      hq2_01 hq2_11 hq2_02 hq2_20 hq3_11 hq3_02 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_socp_of_eq_mix_mapVec_const_x0_x0sqTail_m11_m02_zero
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuarticSymm : ∀ {p : Poly}, IsQuartic p → IsQuartic (e.symm p))
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hMtM : M.transpose * M = 1)
    (hMMt : M * M.transpose = 1)
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq2_11 : MvPolynomial.coeff m11 q2 = 0)
    (hq2_02 : MvPolynomial.coeff m02 q2 = 0)
    (hq2_20 : MvPolynomial.coeff m20 q2 ≠ 0)
    (hq3_11 : MvPolynomial.coeff m11 q3 = 0)
    (hq3_02 : MvPolynomial.coeff m02 q3 = 0)
    (huRep : mix M.transpose (mapVec e.symm.toAlgHom u) = ![(1 : Poly), x0, q2, q3])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have huRepAdmissible : IsAdmissiblePoint (![(1 : Poly), x0, q2, q3] : RankFourVec) := by
    exact admissiblePoint_const_x0_pair hq2 hq3
  have hRep :
      ∀ {B0 : DotForm} [Fact B0.toQuadraticMap.PosDef] {p0 : Poly},
        IsSOSQuartic p0 → IsSOCP B0 p0 (![(1 : Poly), x0, q2, q3] : RankFourVec) →
          residual p0 (![(1 : Poly), x0, q2, q3] : RankFourVec) = 0 := by
    intro B0 _ p0 hp0 hsocp0
    exact residual_eq_zero_of_const_x0_x0sqTail_m11_m02_zero
      (B := B0) (u := ![(1 : Poly), x0, q2, q3]) huRepAdmissible
      (by simp) (by simp [x0]) (by simp) (by simp)
      hq2 hq3 hq2_01 hq2_11 hq2_02 hq2_20 hq3_11 hq3_02 hp0 hsocp0
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec
    (![(1 : Poly), x0, q2, q3])
    hRep e heQuad heQuadSymm heQuarticSymm M hMtM hMMt hB hp huRep hsocp

theorem residual_eq_zero_of_socp_of_eq_mix_affineEquiv_const_x0_x0sqTail_m11_m02_zero
    (A A' : Matrix (Fin 2) (Fin 2) ℝ) (b b' : Fin 2 → ℝ)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (hb : ∀ i, b' i + Matrix.mulVec A' b i = 0)
    (hb' : ∀ i, b i + Matrix.mulVec A b' i = 0)
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hMtM : M.transpose * M = 1)
    (hMMt : M * M.transpose = 1)
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq2_11 : MvPolynomial.coeff m11 q2 = 0)
    (hq2_02 : MvPolynomial.coeff m02 q2 = 0)
    (hq2_20 : MvPolynomial.coeff m20 q2 ≠ 0)
    (hq3_11 : MvPolynomial.coeff m11 q3 = 0)
    (hq3_02 : MvPolynomial.coeff m02 q3 = 0)
    (huRep :
      mix M.transpose
        (mapVec (affineEquiv A A' b b' hAA' hA'A hb hb').symm.toAlgHom u) =
          ![(1 : Poly), x0, q2, q3])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec_const_x0_x0sqTail_m11_m02_zero
    (e := affineEquiv A A' b b' hAA' hA'A hb hb')
    (heQuad := fun {_} hpq => isQuadratic_affineEquiv A A' b b' hAA' hA'A hb hb' hpq)
    (heQuadSymm := fun {_} hpq => isQuadratic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (heQuarticSymm := fun {_} hpq => isQuartic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (M := M) hMtM hMMt hB hp
    hq2 hq3 hq2_01 hq2_11 hq2_02 hq2_20 hq3_11 hq3_02 huRep hsocp

theorem residual_eq_zero_of_const_x0_x0sqTail_m02_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {q2 q3 : Poly}
    (h0 : u 0 = (1 : Poly))
    (h1 : u 1 = x0)
    (h2 : u 2 = q2)
    (h3 : u 3 = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq2_11 : MvPolynomial.coeff m11 q2 = 0)
    (hq2_02 : MvPolynomial.coeff m02 q2 = 0)
    (hq2_20 : MvPolynomial.coeff m20 q2 ≠ 0)
    (hq3_02 : MvPolynomial.coeff m02 q3 = 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  by_cases hq3_11 : MvPolynomial.coeff m11 q3 = 0
  · exact residual_eq_zero_of_const_x0_x0sqTail_m11_m02_zero
      (B := B) (u := u) hu
      h0 h1 h2 h3 hq2 hq3
      hq2_01 hq2_11 hq2_02 hq2_20 hq3_11 hq3_02 hp hsocp
  · exact residual_eq_zero_of_const_x0_x0sqTail_m11_nonzero
      (B := B) (u := u) hu
      h0 h1 h2 h3 hq2 hq3
      hq2_01 hq2_11 hq2_02 hq2_20 hq3_11 hp hsocp

theorem residual_eq_zero_of_equiv_const_x0_x0sqTail_m02_zero
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {q2 q3 : Poly}
    (h0 : mapVec e.toAlgHom u 0 = (1 : Poly))
    (h1 : mapVec e.toAlgHom u 1 = x0)
    (h2 : mapVec e.toAlgHom u 2 = q2)
    (h3 : mapVec e.toAlgHom u 3 = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq2_11 : MvPolynomial.coeff m11 q2 = 0)
    (hq2_02 : MvPolynomial.coeff m02 q2 = 0)
    (hq2_20 : MvPolynomial.coeff m20 q2 ≠ 0)
    (hq3_02 : MvPolynomial.coeff m02 q3 = 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_const_x0_x0sqTail_m02_zero
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0 h1 h2 h3 hq2 hq3
      hq2_01 hq2_11 hq2_02 hq2_20 hq3_02 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_socp_of_eq_mix_mapVec_const_x0_x0sqTail_m02_zero
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuarticSymm : ∀ {p : Poly}, IsQuartic p → IsQuartic (e.symm p))
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hMtM : M.transpose * M = 1)
    (hMMt : M * M.transpose = 1)
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq2_11 : MvPolynomial.coeff m11 q2 = 0)
    (hq2_02 : MvPolynomial.coeff m02 q2 = 0)
    (hq2_20 : MvPolynomial.coeff m20 q2 ≠ 0)
    (hq3_02 : MvPolynomial.coeff m02 q3 = 0)
    (huRep : mix M.transpose (mapVec e.symm.toAlgHom u) = ![(1 : Poly), x0, q2, q3])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have huRepAdmissible : IsAdmissiblePoint (![(1 : Poly), x0, q2, q3] : RankFourVec) := by
    exact admissiblePoint_const_x0_pair hq2 hq3
  have hRep :
      ∀ {B0 : DotForm} [Fact B0.toQuadraticMap.PosDef] {p0 : Poly},
        IsSOSQuartic p0 → IsSOCP B0 p0 (![(1 : Poly), x0, q2, q3] : RankFourVec) →
          residual p0 (![(1 : Poly), x0, q2, q3] : RankFourVec) = 0 := by
    intro B0 _ p0 hp0 hsocp0
    exact residual_eq_zero_of_const_x0_x0sqTail_m02_zero
      (B := B0) (u := ![(1 : Poly), x0, q2, q3]) huRepAdmissible
      (by simp) (by simp [x0]) (by simp) (by simp)
      hq2 hq3 hq2_01 hq2_11 hq2_02 hq2_20 hq3_02 hp0 hsocp0
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec
    (![(1 : Poly), x0, q2, q3])
    hRep e heQuad heQuadSymm heQuarticSymm M hMtM hMMt hB hp huRep hsocp

theorem residual_eq_zero_of_socp_of_eq_mix_affineEquiv_const_x0_x0sqTail_m02_zero
    (A A' : Matrix (Fin 2) (Fin 2) ℝ) (b b' : Fin 2 → ℝ)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (hb : ∀ i, b' i + Matrix.mulVec A' b i = 0)
    (hb' : ∀ i, b i + Matrix.mulVec A b' i = 0)
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hMtM : M.transpose * M = 1)
    (hMMt : M * M.transpose = 1)
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq2_11 : MvPolynomial.coeff m11 q2 = 0)
    (hq2_02 : MvPolynomial.coeff m02 q2 = 0)
    (hq2_20 : MvPolynomial.coeff m20 q2 ≠ 0)
    (hq3_02 : MvPolynomial.coeff m02 q3 = 0)
    (huRep :
      mix M.transpose
        (mapVec (affineEquiv A A' b b' hAA' hA'A hb hb').symm.toAlgHom u) =
          ![(1 : Poly), x0, q2, q3])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec_const_x0_x0sqTail_m02_zero
    (e := affineEquiv A A' b b' hAA' hA'A hb hb')
    (heQuad := fun {_} hpq => isQuadratic_affineEquiv A A' b b' hAA' hA'A hb hb' hpq)
    (heQuadSymm := fun {_} hpq => isQuadratic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (heQuarticSymm := fun {_} hpq => isQuartic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (M := M) hMtM hMMt hB hp
    hq2 hq3 hq2_01 hq2_11 hq2_02 hq2_20 hq3_02 huRep hsocp

theorem residual_eq_zero_of_const_x0_tailedPair_det
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {q2 q3 : Poly}
    (h0 : u 0 = (1 : Poly))
    (h1 : u 1 = x0)
    (h2 : u 2 = q2)
    (h3 : u 3 = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hdet :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let det : ℝ :=
    MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
      MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3
  let tx : ℝ :=
    (MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m01 q3 -
      MvPolynomial.coeff m02 q3 * MvPolynomial.coeff m01 q2) / det
  let ty : ℝ :=
    (MvPolynomial.coeff m11 q3 * MvPolynomial.coeff m01 q2 -
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m01 q3) / (2 * det)
  let b : Fin 2 → ℝ := ![tx, ty]
  let b' : Fin 2 → ℝ := ![-tx, -ty]
  have hb : ∀ i, b' i + Matrix.mulVec (1 : Matrix (Fin 2) (Fin 2) ℝ) b i = 0 := by
    intro i
    rw [Matrix.one_mulVec]
    fin_cases i <;> simp [b, b']
  have hb' : ∀ i, b i + Matrix.mulVec (1 : Matrix (Fin 2) (Fin 2) ℝ) b' i = 0 := by
    intro i
    rw [Matrix.one_mulVec]
    fin_cases i <;> simp [b, b']
  let e : Poly ≃ₐ[ℝ] Poly :=
    affineEquiv (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b' (by simp) (by simp) hb hb'
  let B0 : DotForm := dotTransport e B
  have hB : IsPositiveDefinite B := (Fact.out : B.toQuadraticMap.PosDef)
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_affineEquiv
      (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b' (by simp) (by simp) hb hb' hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_affineEquiv
      (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b' (by simp) (by simp) hb hb' hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_affineEquiv
      (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b' (by simp) (by simp) hb hb' hsocp
  have he_apply (q : Poly) :
      e q =
        affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec ty)
          (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec tx) q) := by
    have hcomp :
        affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec ty)
            (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec tx) q) =
          affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ)
            (fun i => x0TranslateVec tx i +
              Matrix.mulVec (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec ty) i) q := by
      simpa [AlgHom.comp_apply] using
        congrArg (fun f => f q)
          (affineHom_comp
            (1 : Matrix (Fin 2) (Fin 2) ℝ)
            (1 : Matrix (Fin 2) (Fin 2) ℝ)
            (x1TranslateVec ty)
            (x0TranslateVec tx))
    have hbEq :
        (fun i => x0TranslateVec tx i +
          Matrix.mulVec (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec ty) i) = b := by
      funext i
      rw [Matrix.one_mulVec]
      fin_cases i <;> simp [b, x0TranslateVec, x1TranslateVec]
    calc
      e q = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) b q := by rfl
      _ = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ)
            (fun i => x0TranslateVec tx i +
              Matrix.mulVec (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec ty) i) q := by
            rw [hbEq]
      _ = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec ty)
            (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec tx) q) := by
            exact hcomp.symm
  have he_one : e (1 : Poly) = (1 : Poly) := by
    simp [e]
  have he_x0 : e x0 = MvPolynomial.C tx + x0 := by
    rw [he_apply x0, affineHom_x0Translate_x0]
    simp [affineHom_x1Translate_x0]
  let q2t : Poly := e q2
  let q3t : Poly := e q3
  have hq2t : IsQuadratic q2t := by
    dsimp [q2t, e]
    change IsQuadratic (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) b q2)
    exact isQuadratic_affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) b hq2
  have hq3t : IsQuadratic q3t := by
    dsimp [q3t, e]
    change IsQuadratic (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) b q3)
    exact isQuadratic_affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) b hq3
  have hpairkill :=
    coeff_m01_affineHom_x1Translate_after_x0Translate_pair_kill hq2 hq3 hdet
  have hq2t_01 : MvPolynomial.coeff m01 q2t = 0 := by
    dsimp [q2t]
    rw [he_apply q2]
    simpa [det, tx, ty] using hpairkill.1
  have hq3t_01 : MvPolynomial.coeff m01 q3t = 0 := by
    dsimp [q3t]
    rw [he_apply q3]
    simpa [det, tx, ty] using hpairkill.2
  have hq2t_11 :
      MvPolynomial.coeff m11 q2t = MvPolynomial.coeff m11 q2 := by
    dsimp [q2t]
    rw [he_apply q2]
    rw [coeff_m11_affineHom_x1Translate
      (isQuadratic_affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec tx) hq2)]
    rw [coeff_m11_affineHom_x0Translate hq2]
  have hq2t_02 :
      MvPolynomial.coeff m02 q2t = MvPolynomial.coeff m02 q2 := by
    dsimp [q2t]
    rw [he_apply q2]
    rw [coeff_m02_affineHom_x1Translate
      (isQuadratic_affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec tx) hq2)]
    rw [coeff_m02_affineHom_x0Translate hq2]
  have hq3t_11 :
      MvPolynomial.coeff m11 q3t = MvPolynomial.coeff m11 q3 := by
    dsimp [q3t]
    rw [he_apply q3]
    rw [coeff_m11_affineHom_x1Translate
      (isQuadratic_affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec tx) hq3)]
    rw [coeff_m11_affineHom_x0Translate hq3]
  have hq3t_02 :
      MvPolynomial.coeff m02 q3t = MvPolynomial.coeff m02 q3 := by
    dsimp [q3t]
    rw [he_apply q3]
    rw [coeff_m02_affineHom_x1Translate
      (isQuadratic_affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec tx) hq3)]
    rw [coeff_m02_affineHom_x0Translate hq3]
  let a2 : ℝ := MvPolynomial.coeff m10 q2t
  let b2q : ℝ := MvPolynomial.coeff m00 q2t
  let a3 : ℝ := MvPolynomial.coeff m10 q3t
  let b3q : ℝ := MvPolynomial.coeff m00 q3t
  let q2h : Poly := q2t - a2 • (x0 : Poly) - b2q • (1 : Poly)
  let q3h : Poly := q3t - a3 • (x0 : Poly) - b3q • (1 : Poly)
  let c0' : Fin 4 → ℝ := ![1, 0, 0, 0]
  let c1' : Fin 4 → ℝ := ![-tx, 1, 0, 0]
  let c2' : Fin 4 → ℝ := ![tx * a2 - b2q, -a2, 1, 0]
  let c3' : Fin 4 → ℝ := ![tx * a3 - b3q, -a3, 0, 1]
  have h0' : ∑ i : Fin 4, c0' i • mapVec e.toAlgHom u i = (1 : Poly) := by
    rw [Fin.sum_univ_four]
    simp [c0', mapVec, h0, he_one]
  have h1std : ∑ i : Fin 4, (![0, 1, 0, 0] : Fin 4 → ℝ) i • mapVec e.toAlgHom u i =
      MvPolynomial.C tx + x0 := by
    rw [Fin.sum_univ_four]
    simp [mapVec, h0, h1, he_one, he_x0]
  have h1' : ∑ i : Fin 4, c1' i • mapVec e.toAlgHom u i = x0 := by
    rw [Fin.sum_univ_four]
    change (-tx) • mapVec e.toAlgHom u 0 + (1 : ℝ) • mapVec e.toAlgHom u 1 + (0 : ℝ) • mapVec e.toAlgHom u 2 +
        (0 : ℝ) • mapVec e.toAlgHom u 3 = x0
    calc
      (-tx) • mapVec e.toAlgHom u 0 + (1 : ℝ) • mapVec e.toAlgHom u 1 + (0 : ℝ) • mapVec e.toAlgHom u 2 +
          (0 : ℝ) • mapVec e.toAlgHom u 3
          = -(tx • (1 : Poly)) + (MvPolynomial.C tx + x0) := by
              simp [mapVec, h0, h1, he_one, he_x0]
      _ = x0 := by
            simp [MvPolynomial.smul_eq_C_mul]
  have h2std : ∑ i : Fin 4, (![0, 0, 1, 0] : Fin 4 → ℝ) i • mapVec e.toAlgHom u i = q2t := by
    rw [Fin.sum_univ_four]
    simp [mapVec, h2, q2t]
  have h3std : ∑ i : Fin 4, (![0, 0, 0, 1] : Fin 4 → ℝ) i • mapVec e.toAlgHom u i = q3t := by
    rw [Fin.sum_univ_four]
    simp [mapVec, h3, q3t]
  have h2' : ∑ i : Fin 4, c2' i • mapVec e.toAlgHom u i = q2h := by
    rw [Fin.sum_univ_four]
    have hu0' : mapVec e.toAlgHom u 0 = (1 : Poly) := by
      simp [mapVec, h0, he_one]
    have hu1' : mapVec e.toAlgHom u 1 = MvPolynomial.C tx + x0 := by
      simp [mapVec, h1, he_x0]
    have hu2' : mapVec e.toAlgHom u 2 = q2t := by
      simp [mapVec, h2, q2t]
    calc
      (tx * a2 - b2q) • mapVec e.toAlgHom u 0 + (-a2) • mapVec e.toAlgHom u 1 +
          (1 : ℝ) • mapVec e.toAlgHom u 2 + (0 : ℝ) • mapVec e.toAlgHom u 3
          =
            (tx * a2 - b2q) • (1 : Poly) + (-a2) • (MvPolynomial.C tx + x0) + q2t := by
              rw [hu0', hu1', hu2']
              simp
      _ = q2h := by
            dsimp [q2h]
            have hC :
                (-a2) • (MvPolynomial.C tx : Poly) = (-a2 * tx) • (1 : Poly) := by
              calc
                (-a2) • (MvPolynomial.C tx : Poly) = MvPolynomial.C (-a2) * MvPolynomial.C tx := by
                  rw [MvPolynomial.smul_eq_C_mul]
                _ = MvPolynomial.C (-a2 * tx) := by rw [← MvPolynomial.C_mul]
                _ = (-a2 * tx) • (1 : Poly) := by
                  rw [MvPolynomial.smul_eq_C_mul, mul_one]
            have hconst :
                (tx * a2 - b2q) • (1 : Poly) + (-a2 * tx) • (1 : Poly) =
                  (-b2q) • (1 : Poly) := by
              rw [← add_smul]
              congr 1
              ring
            calc
              (tx * a2 - b2q) • (1 : Poly) + (-a2) • (MvPolynomial.C tx + x0) + q2t
                  =
                    (tx * a2 - b2q) • (1 : Poly) +
                      ((-a2 * tx) • (1 : Poly) + (-a2) • x0) + q2t := by
                        rw [smul_add, hC]
              _ = ((tx * a2 - b2q) • (1 : Poly) + (-a2 * tx) • (1 : Poly)) +
                    ((-a2) • x0 + q2t) := by
                      rw [← add_assoc, add_assoc]
              _ = (-b2q) • (1 : Poly) + (-a2) • x0 + q2t := by
                    rw [hconst, add_assoc]
              _ = q2t - a2 • (x0 : Poly) - b2q • (1 : Poly) := by
                    rw [sub_eq_add_neg, sub_eq_add_neg]
                    rw [show -(a2 • (x0 : Poly)) = (-a2) • x0 by simp,
                      show -(b2q • (1 : Poly)) = (-b2q) • (1 : Poly) by simp]
                    ac_rfl
  have h3' : ∑ i : Fin 4, c3' i • mapVec e.toAlgHom u i = q3h := by
    rw [Fin.sum_univ_four]
    have hu0' : mapVec e.toAlgHom u 0 = (1 : Poly) := by
      simp [mapVec, h0, he_one]
    have hu1' : mapVec e.toAlgHom u 1 = MvPolynomial.C tx + x0 := by
      simp [mapVec, h1, he_x0]
    have hu3' : mapVec e.toAlgHom u 3 = q3t := by
      simp [mapVec, h3, q3t]
    calc
      (tx * a3 - b3q) • mapVec e.toAlgHom u 0 + (-a3) • mapVec e.toAlgHom u 1 +
          (0 : ℝ) • mapVec e.toAlgHom u 2 + (1 : ℝ) • mapVec e.toAlgHom u 3
          =
            (tx * a3 - b3q) • (1 : Poly) + (-a3) • (MvPolynomial.C tx + x0) + q3t := by
              rw [hu0', hu1', hu3']
              simp
      _ = q3h := by
            dsimp [q3h]
            have hC :
                (-a3) • (MvPolynomial.C tx : Poly) = (-a3 * tx) • (1 : Poly) := by
              calc
                (-a3) • (MvPolynomial.C tx : Poly) = MvPolynomial.C (-a3) * MvPolynomial.C tx := by
                  rw [MvPolynomial.smul_eq_C_mul]
                _ = MvPolynomial.C (-a3 * tx) := by rw [← MvPolynomial.C_mul]
                _ = (-a3 * tx) • (1 : Poly) := by
                  rw [MvPolynomial.smul_eq_C_mul, mul_one]
            have hconst :
                (tx * a3 - b3q) • (1 : Poly) + (-a3 * tx) • (1 : Poly) =
                  (-b3q) • (1 : Poly) := by
              rw [← add_smul]
              congr 1
              ring
            calc
              (tx * a3 - b3q) • (1 : Poly) + (-a3) • (MvPolynomial.C tx + x0) + q3t
                  =
                    (tx * a3 - b3q) • (1 : Poly) +
                      ((-a3 * tx) • (1 : Poly) + (-a3) • x0) + q3t := by
                        rw [smul_add, hC]
              _ = ((tx * a3 - b3q) • (1 : Poly) + (-a3 * tx) • (1 : Poly)) +
                    ((-a3) • x0 + q3t) := by
                      rw [← add_assoc, add_assoc]
              _ = (-b3q) • (1 : Poly) + (-a3) • x0 + q3t := by
                    rw [hconst, add_assoc]
              _ = q3t - a3 • (x0 : Poly) - b3q • (1 : Poly) := by
                    rw [sub_eq_add_neg, sub_eq_add_neg]
                    rw [show -(a3 • (x0 : Poly)) = (-a3) • x0 by simp,
                      show -(b3q • (1 : Poly)) = (-b3q) • (1 : Poly) by simp]
                    ac_rfl
  have hq2h : IsQuadratic q2h := by
    dsimp [q2h]
    have hx0 : IsQuadratic (x0 : Poly) := by
      simpa [x0] using (show IsQuadratic (MvPolynomial.X 0 : Poly) by
        simp [IsQuadratic])
    have h1poly : IsQuadratic (1 : Poly) := by
      simp [IsQuadratic]
    have htmp : IsQuadratic (q2t + (-a2) • (x0 : Poly)) := by
      simpa using isQuadratic_linearCombination_local hq2t hx0 1 (-a2)
    simpa [sub_eq_add_neg, add_assoc] using
      (isQuadratic_linearCombination_local htmp h1poly 1 (-b2q))
  have hq3h : IsQuadratic q3h := by
    dsimp [q3h]
    have hx0 : IsQuadratic (x0 : Poly) := by
      simpa [x0] using (show IsQuadratic (MvPolynomial.X 0 : Poly) by
        simp [IsQuadratic])
    have h1poly : IsQuadratic (1 : Poly) := by
      simp [IsQuadratic]
    have htmp : IsQuadratic (q3t + (-a3) • (x0 : Poly)) := by
      simpa using isQuadratic_linearCombination_local hq3t hx0 1 (-a3)
    simpa [sub_eq_add_neg, add_assoc] using
      (isQuadratic_linearCombination_local htmp h1poly 1 (-b3q))
  have hcoeff_x0_00 : MvPolynomial.coeff m00 (x0 : Poly) = 0 := by simp [x0, m00]
  have hcoeff_x0_10 : MvPolynomial.coeff m10 (x0 : Poly) = 1 := by simp [x0, m10]
  have hcoeff_x0_01 : MvPolynomial.coeff m01 (x0 : Poly) = 0 := by simp [x0, m01]
  have hcoeff_x0_11 : MvPolynomial.coeff m11 (x0 : Poly) = 0 := by
    simpa [x0, m10] using (MvPolynomial.coeff_X' (σ := Fin 2) (R := ℝ) 0 m11)
  have hcoeff_x0_02 : MvPolynomial.coeff m02 (x0 : Poly) = 0 := by simp [x0, m02]
  have hcoeff_one_00 : MvPolynomial.coeff m00 (1 : Poly) = 1 := by simp [m00]
  have hcoeff_one_10 : MvPolynomial.coeff m10 (1 : Poly) = 0 := by
    change MvPolynomial.coeff m10 (MvPolynomial.C (1 : ℝ)) = 0
    simpa [m10] using (MvPolynomial.coeff_C (σ := Fin 2) (R := ℝ) m10 (1 : ℝ))
  have hcoeff_one_01 : MvPolynomial.coeff m01 (1 : Poly) = 0 := by
    change MvPolynomial.coeff m01 (MvPolynomial.C (1 : ℝ)) = 0
    simpa [m01] using (MvPolynomial.coeff_C (σ := Fin 2) (R := ℝ) m01 (1 : ℝ))
  have hcoeff_one_11 : MvPolynomial.coeff m11 (1 : Poly) = 0 := by
    change MvPolynomial.coeff m11 (MvPolynomial.C (1 : ℝ)) = 0
    simpa [m11] using (MvPolynomial.coeff_C (σ := Fin 2) (R := ℝ) m11 (1 : ℝ))
  have hcoeff_one_02 : MvPolynomial.coeff m02 (1 : Poly) = 0 := by
    change MvPolynomial.coeff m02 (MvPolynomial.C (1 : ℝ)) = 0
    simpa [m02] using (MvPolynomial.coeff_C (σ := Fin 2) (R := ℝ) m02 (1 : ℝ))
  have hq2h_00 : MvPolynomial.coeff m00 q2h = 0 := by
    dsimp [q2h, a2, b2q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hcoeff_x0_00, hcoeff_one_00]
    dsimp [b2q]
    ring_nf
  have hq2h_10 : MvPolynomial.coeff m10 q2h = 0 := by
    dsimp [q2h, a2, b2q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hcoeff_x0_10, hcoeff_one_10]
    dsimp [a2]
    ring_nf
  have hq2h_01 : MvPolynomial.coeff m01 q2h = 0 := by
    dsimp [q2h]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hq2t_01, hcoeff_x0_01, hcoeff_one_01]
    simp
  have hq3h_00 : MvPolynomial.coeff m00 q3h = 0 := by
    dsimp [q3h, a3, b3q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hcoeff_x0_00, hcoeff_one_00]
    dsimp [b3q]
    ring_nf
  have hq3h_10 : MvPolynomial.coeff m10 q3h = 0 := by
    dsimp [q3h, a3, b3q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hcoeff_x0_10, hcoeff_one_10]
    dsimp [a3]
    ring_nf
  have hq3h_01 : MvPolynomial.coeff m01 q3h = 0 := by
    dsimp [q3h]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hq3t_01, hcoeff_x0_01, hcoeff_one_01]
    simp
  have hq2h_11 :
      MvPolynomial.coeff m11 q2h = MvPolynomial.coeff m11 q2 := by
    dsimp [q2h, a2, b2q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hq2t_11, hcoeff_x0_11, hcoeff_one_11]
    simp
  have hq2h_02 :
      MvPolynomial.coeff m02 q2h = MvPolynomial.coeff m02 q2 := by
    dsimp [q2h, a2, b2q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hq2t_02, hcoeff_x0_02, hcoeff_one_02]
    simp
  have hq3h_11 :
      MvPolynomial.coeff m11 q3h = MvPolynomial.coeff m11 q3 := by
    dsimp [q3h, a3, b3q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hq3t_11, hcoeff_x0_11, hcoeff_one_11]
    simp
  have hq3h_02 :
      MvPolynomial.coeff m02 q3h = MvPolynomial.coeff m02 q3 := by
    dsimp [q3h, a3, b3q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hq3t_02, hcoeff_x0_02, hcoeff_one_02]
    simp
  have hgram :
      (∑ i : Fin 4, (c2' i) ^ 2) * (∑ i : Fin 4, (c3' i) ^ 2) -
        (∑ i : Fin 4, c2' i * c3' i) ^ 2 ≠ 0 := by
    have hEq :
        (∑ i : Fin 4, (c2' i) ^ 2) * (∑ i : Fin 4, (c3' i) ^ 2) -
            (∑ i : Fin 4, c2' i * c3' i) ^ 2 =
          ((tx * a2 - b2q) ^ 2 + a2 ^ 2 + 1) *
              ((tx * a3 - b3q) ^ 2 + a3 ^ 2 + 1) -
            ((tx * a2 - b2q) * (tx * a3 - b3q) + a2 * a3) ^ 2 := by
      rw [Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four]
      simp [c2', c3', pow_two]
    rw [hEq]
    exact coordTailCorrectedGram_ne_zero (tx * a2 - b2q) a2 (tx * a3 - b3q) a3
  have hplane :
      homQuadPlaneA q2h q3h ≠ 0 ∨
        homQuadPlaneB q2h q3h ≠ 0 ∨
          homQuadPlaneC q2h q3h ≠ 0 := by
    left
    simpa [homQuadPlaneA, hq2h_11, hq2h_02, hq3h_11, hq3h_02] using hdet
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_homQuadratics_plane_nontrivial
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0' h1' h2' h3' hq2h hq3h
      hq2h_00 hq2h_10 hq2h_01
      hq3h_00 hq3h_10 hq3h_01
      hgram hplane hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_equiv_const_x0_tailedPair_det
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {q2 q3 : Poly}
    (h0 : mapVec e.toAlgHom u 0 = (1 : Poly))
    (h1 : mapVec e.toAlgHom u 1 = x0)
    (h2 : mapVec e.toAlgHom u 2 = q2)
    (h3 : mapVec e.toAlgHom u 3 = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hdet :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_const_x0_tailedPair_det
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0 h1 h2 h3 hq2 hq3 hdet hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_socp_of_eq_mix_mapVec_const_x0_tailedPair_det
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuarticSymm : ∀ {p : Poly}, IsQuartic p → IsQuartic (e.symm p))
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hMtM : M.transpose * M = 1)
    (hMMt : M * M.transpose = 1)
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hdet :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 ≠ 0)
    (huRep : mix M.transpose (mapVec e.symm.toAlgHom u) = ![(1 : Poly), x0, q2, q3])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have huRepAdmissible : IsAdmissiblePoint (![(1 : Poly), x0, q2, q3] : RankFourVec) := by
    intro i
    fin_cases i
    · simp [IsQuadratic]
    · simpa [x0] using (show IsQuadratic (MvPolynomial.X 0 : Poly) by
        simp [IsQuadratic])
    · simpa using hq2
    · simpa using hq3
  have hRep :
      ∀ {B0 : DotForm} [Fact B0.toQuadraticMap.PosDef] {p0 : Poly},
        IsSOSQuartic p0 → IsSOCP B0 p0 (![(1 : Poly), x0, q2, q3] : RankFourVec) →
          residual p0 (![(1 : Poly), x0, q2, q3] : RankFourVec) = 0 := by
    intro B0 _ p0 hp0 hsocp0
    exact residual_eq_zero_of_const_x0_tailedPair_det
      (B := B0) (u := ![(1 : Poly), x0, q2, q3]) huRepAdmissible
      (by simp) (by simp [x0]) (by simp) (by simp)
      hq2 hq3 hdet hp0 hsocp0
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec
    (![(1 : Poly), x0, q2, q3])
    hRep e heQuad heQuadSymm heQuarticSymm M hMtM hMMt hB hp huRep hsocp

theorem residual_eq_zero_of_socp_of_eq_mix_affineEquiv_const_x0_tailedPair_det
    (A A' : Matrix (Fin 2) (Fin 2) ℝ) (b b' : Fin 2 → ℝ)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (hb : ∀ i, b' i + Matrix.mulVec A' b i = 0)
    (hb' : ∀ i, b i + Matrix.mulVec A b' i = 0)
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hMtM : M.transpose * M = 1)
    (hMMt : M * M.transpose = 1)
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hdet :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 ≠ 0)
    (huRep :
      mix M.transpose
        (mapVec (affineEquiv A A' b b' hAA' hA'A hb hb').symm.toAlgHom u) =
          ![(1 : Poly), x0, q2, q3])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec_const_x0_tailedPair_det
    (e := affineEquiv A A' b b' hAA' hA'A hb hb')
    (heQuad := fun {_} hpq => isQuadratic_affineEquiv A A' b b' hAA' hA'A hb hb' hpq)
    (heQuadSymm := fun {_} hpq => isQuadratic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (heQuarticSymm := fun {_} hpq => isQuartic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (M := M) hMtM hMMt hB hp hq2 hq3 hdet huRep hsocp

set_option maxHeartbeats 800000 in
theorem residual_eq_zero_of_relations_const_x0_tailedPair_det_general
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hdet :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let det : ℝ :=
    MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
      MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3
  let tx : ℝ :=
    (MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m01 q3 -
      MvPolynomial.coeff m02 q3 * MvPolynomial.coeff m01 q2) / det
  let ty : ℝ :=
    (MvPolynomial.coeff m11 q3 * MvPolynomial.coeff m01 q2 -
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m01 q3) / (2 * det)
  let b : Fin 2 → ℝ := ![tx, ty]
  let b' : Fin 2 → ℝ := ![-tx, -ty]
  have hb : ∀ i, b' i + Matrix.mulVec (1 : Matrix (Fin 2) (Fin 2) ℝ) b i = 0 := by
    intro i
    rw [Matrix.one_mulVec]
    fin_cases i <;> simp [b, b']
  have hb' : ∀ i, b i + Matrix.mulVec (1 : Matrix (Fin 2) (Fin 2) ℝ) b' i = 0 := by
    intro i
    rw [Matrix.one_mulVec]
    fin_cases i <;> simp [b, b']
  let e : Poly ≃ₐ[ℝ] Poly :=
    affineEquiv (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b' (by simp) (by simp) hb hb'
  let B0 : DotForm := dotTransport e B
  have hB : IsPositiveDefinite B := (Fact.out : B.toQuadraticMap.PosDef)
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_affineEquiv
      (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b' (by simp) (by simp) hb hb' hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_affineEquiv
      (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b' (by simp) (by simp) hb hb' hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_affineEquiv
      (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b' (by simp) (by simp) hb hb' hsocp
  have he_apply (q : Poly) :
      e q =
        affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec ty)
          (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec tx) q) := by
    have hcomp :
        affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec ty)
            (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec tx) q) =
          affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ)
            (fun i => x0TranslateVec tx i +
              Matrix.mulVec (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec ty) i) q := by
      simpa [AlgHom.comp_apply] using
        congrArg (fun f => f q)
          (affineHom_comp
            (1 : Matrix (Fin 2) (Fin 2) ℝ)
            (1 : Matrix (Fin 2) (Fin 2) ℝ)
            (x1TranslateVec ty)
            (x0TranslateVec tx))
    have hbEq :
        (fun i => x0TranslateVec tx i +
          Matrix.mulVec (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec ty) i) = b := by
      funext i
      rw [Matrix.one_mulVec]
      fin_cases i <;> simp [b, x0TranslateVec, x1TranslateVec]
    calc
      e q = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) b q := by rfl
      _ = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ)
            (fun i => x0TranslateVec tx i +
              Matrix.mulVec (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec ty) i) q := by
            rw [hbEq]
      _ = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec ty)
            (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec tx) q) := by
            exact hcomp.symm
  have he_one : e (1 : Poly) = (1 : Poly) := by
    simp [e]
  have he_x0 : e x0 = MvPolynomial.C tx + x0 := by
    rw [he_apply x0, affineHom_x0Translate_x0]
    simp [affineHom_x1Translate_x0]
  let q2t : Poly := e q2
  let q3t : Poly := e q3
  have h0e : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly) := by
    simpa [he_one] using relation_map e.toAlgHom h0
  have h1e :
      ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = MvPolynomial.C tx + x0 := by
    simpa [he_x0] using relation_map e.toAlgHom h1
  have h2e : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = q2t := by
    simpa [q2t] using relation_map e.toAlgHom h2
  have h3e : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = q3t := by
    simpa [q3t] using relation_map e.toAlgHom h3
  have hq2t : IsQuadratic q2t := by
    dsimp [q2t, e]
    change IsQuadratic (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) b q2)
    exact isQuadratic_affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) b hq2
  have hq3t : IsQuadratic q3t := by
    dsimp [q3t, e]
    change IsQuadratic (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) b q3)
    exact isQuadratic_affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) b hq3
  have hpairkill :=
    coeff_m01_affineHom_x1Translate_after_x0Translate_pair_kill hq2 hq3 hdet
  have hq2t_01 : MvPolynomial.coeff m01 q2t = 0 := by
    dsimp [q2t]
    rw [he_apply q2]
    simpa [det, tx, ty] using hpairkill.1
  have hq3t_01 : MvPolynomial.coeff m01 q3t = 0 := by
    dsimp [q3t]
    rw [he_apply q3]
    simpa [det, tx, ty] using hpairkill.2
  have hq2t_11 :
      MvPolynomial.coeff m11 q2t = MvPolynomial.coeff m11 q2 := by
    dsimp [q2t]
    rw [he_apply q2]
    rw [coeff_m11_affineHom_x1Translate
      (isQuadratic_affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec tx) hq2)]
    rw [coeff_m11_affineHom_x0Translate hq2]
  have hq2t_02 :
      MvPolynomial.coeff m02 q2t = MvPolynomial.coeff m02 q2 := by
    dsimp [q2t]
    rw [he_apply q2]
    rw [coeff_m02_affineHom_x1Translate
      (isQuadratic_affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec tx) hq2)]
    rw [coeff_m02_affineHom_x0Translate hq2]
  have hq3t_11 :
      MvPolynomial.coeff m11 q3t = MvPolynomial.coeff m11 q3 := by
    dsimp [q3t]
    rw [he_apply q3]
    rw [coeff_m11_affineHom_x1Translate
      (isQuadratic_affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec tx) hq3)]
    rw [coeff_m11_affineHom_x0Translate hq3]
  have hq3t_02 :
      MvPolynomial.coeff m02 q3t = MvPolynomial.coeff m02 q3 := by
    dsimp [q3t]
    rw [he_apply q3]
    rw [coeff_m02_affineHom_x1Translate
      (isQuadratic_affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec tx) hq3)]
    rw [coeff_m02_affineHom_x0Translate hq3]
  let a2 : ℝ := MvPolynomial.coeff m10 q2t
  let b2q : ℝ := MvPolynomial.coeff m00 q2t
  let a3 : ℝ := MvPolynomial.coeff m10 q3t
  let b3q : ℝ := MvPolynomial.coeff m00 q3t
  let q2h : Poly := q2t - a2 • (x0 : Poly) - b2q • (1 : Poly)
  let q3h : Poly := q3t - a3 • (x0 : Poly) - b3q • (1 : Poly)
  let c1' : Fin 4 → ℝ := fun i => c1 i + (-tx) * c0 i
  have h1' : ∑ i : Fin 4, c1' i • mapVec e.toAlgHom u i = x0 := by
    calc
      ∑ i : Fin 4, c1' i • mapVec e.toAlgHom u i
          = (1 : ℝ) • (MvPolynomial.C tx + x0) + (-tx) • (1 : Poly) := by
              simpa [c1'] using relation_linearCombination h1e h0e 1 (-tx)
      _ = x0 := by
            simp [MvPolynomial.smul_eq_C_mul]
  let c2' : Fin 4 → ℝ := fun i => c2 i + (-a2) * c1' i + (-b2q) * c0 i
  let c3' : Fin 4 → ℝ := fun i => c3 i + (-a3) * c1' i + (-b3q) * c0 i
  have h2' : ∑ i : Fin 4, c2' i • mapVec e.toAlgHom u i = q2h := by
    simpa [c2', q2h, sub_eq_add_neg, add_assoc] using
      relation_sub_const_x0 h0e h1' h2e a2 b2q
  have h3' : ∑ i : Fin 4, c3' i • mapVec e.toAlgHom u i = q3h := by
    simpa [c3', q3h, sub_eq_add_neg, add_assoc] using
      relation_sub_const_x0 h0e h1' h3e a3 b3q
  have hq2h : IsQuadratic q2h := by
    dsimp [q2h]
    have hx0 : IsQuadratic (x0 : Poly) := by
      simpa [x0] using (show IsQuadratic (MvPolynomial.X 0 : Poly) by
        simp [IsQuadratic])
    have h1poly : IsQuadratic (1 : Poly) := by
      simp [IsQuadratic]
    have htmp : IsQuadratic (q2t + (-a2) • (x0 : Poly)) := by
      simpa using isQuadratic_linearCombination_local hq2t hx0 1 (-a2)
    simpa [sub_eq_add_neg, add_assoc] using
      (isQuadratic_linearCombination_local htmp h1poly 1 (-b2q))
  have hq3h : IsQuadratic q3h := by
    dsimp [q3h]
    have hx0 : IsQuadratic (x0 : Poly) := by
      simpa [x0] using (show IsQuadratic (MvPolynomial.X 0 : Poly) by
        simp [IsQuadratic])
    have h1poly : IsQuadratic (1 : Poly) := by
      simp [IsQuadratic]
    have htmp : IsQuadratic (q3t + (-a3) • (x0 : Poly)) := by
      simpa using isQuadratic_linearCombination_local hq3t hx0 1 (-a3)
    simpa [sub_eq_add_neg, add_assoc] using
      (isQuadratic_linearCombination_local htmp h1poly 1 (-b3q))
  have hcoeff_x0_00 : MvPolynomial.coeff m00 (x0 : Poly) = 0 := by simp [x0, m00]
  have hcoeff_x0_10 : MvPolynomial.coeff m10 (x0 : Poly) = 1 := by simp [x0, m10]
  have hcoeff_x0_01 : MvPolynomial.coeff m01 (x0 : Poly) = 0 := by simp [x0, m01]
  have hcoeff_x0_11 : MvPolynomial.coeff m11 (x0 : Poly) = 0 := by
    simpa [x0, m10] using (MvPolynomial.coeff_X' (σ := Fin 2) (R := ℝ) 0 m11)
  have hcoeff_x0_02 : MvPolynomial.coeff m02 (x0 : Poly) = 0 := by simp [x0, m02]
  have hcoeff_one_00 : MvPolynomial.coeff m00 (1 : Poly) = 1 := by simp [m00]
  have hcoeff_one_10 : MvPolynomial.coeff m10 (1 : Poly) = 0 := by
    change MvPolynomial.coeff m10 (MvPolynomial.C (1 : ℝ)) = 0
    simpa [m10] using (MvPolynomial.coeff_C (σ := Fin 2) (R := ℝ) m10 (1 : ℝ))
  have hcoeff_one_01 : MvPolynomial.coeff m01 (1 : Poly) = 0 := by
    change MvPolynomial.coeff m01 (MvPolynomial.C (1 : ℝ)) = 0
    simpa [m01] using (MvPolynomial.coeff_C (σ := Fin 2) (R := ℝ) m01 (1 : ℝ))
  have hcoeff_one_11 : MvPolynomial.coeff m11 (1 : Poly) = 0 := by
    change MvPolynomial.coeff m11 (MvPolynomial.C (1 : ℝ)) = 0
    simpa [m11] using (MvPolynomial.coeff_C (σ := Fin 2) (R := ℝ) m11 (1 : ℝ))
  have hcoeff_one_02 : MvPolynomial.coeff m02 (1 : Poly) = 0 := by
    change MvPolynomial.coeff m02 (MvPolynomial.C (1 : ℝ)) = 0
    simpa [m02] using (MvPolynomial.coeff_C (σ := Fin 2) (R := ℝ) m02 (1 : ℝ))
  have hq2h_00 : MvPolynomial.coeff m00 q2h = 0 := by
    dsimp [q2h, a2, b2q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hcoeff_x0_00, hcoeff_one_00]
    dsimp [b2q]
    ring_nf
  have hq2h_10 : MvPolynomial.coeff m10 q2h = 0 := by
    dsimp [q2h, a2, b2q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hcoeff_x0_10, hcoeff_one_10]
    dsimp [a2]
    ring_nf
  have hq2h_01 : MvPolynomial.coeff m01 q2h = 0 := by
    dsimp [q2h]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hq2t_01, hcoeff_x0_01, hcoeff_one_01]
    simp
  have hq3h_00 : MvPolynomial.coeff m00 q3h = 0 := by
    dsimp [q3h, a3, b3q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hcoeff_x0_00, hcoeff_one_00]
    dsimp [b3q]
    ring_nf
  have hq3h_10 : MvPolynomial.coeff m10 q3h = 0 := by
    dsimp [q3h, a3, b3q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hcoeff_x0_10, hcoeff_one_10]
    dsimp [a3]
    ring_nf
  have hq3h_01 : MvPolynomial.coeff m01 q3h = 0 := by
    dsimp [q3h]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hq3t_01, hcoeff_x0_01, hcoeff_one_01]
    simp
  have hq2h_11 :
      MvPolynomial.coeff m11 q2h = MvPolynomial.coeff m11 q2 := by
    dsimp [q2h, a2, b2q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hq2t_11, hcoeff_x0_11, hcoeff_one_11]
    simp
  have hq2h_02 :
      MvPolynomial.coeff m02 q2h = MvPolynomial.coeff m02 q2 := by
    dsimp [q2h, a2, b2q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hq2t_02, hcoeff_x0_02, hcoeff_one_02]
    simp
  have hq3h_11 :
      MvPolynomial.coeff m11 q3h = MvPolynomial.coeff m11 q3 := by
    dsimp [q3h, a3, b3q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hq3t_11, hcoeff_x0_11, hcoeff_one_11]
    simp
  have hq3h_02 :
      MvPolynomial.coeff m02 q3h = MvPolynomial.coeff m02 q3 := by
    dsimp [q3h, a3, b3q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hq3t_02, hcoeff_x0_02, hcoeff_one_02]
    simp
  have hgram :
      (∑ i : Fin 4, (c2' i) ^ 2) * (∑ i : Fin 4, (c3' i) ^ 2) -
        (∑ i : Fin 4, c2' i * c3' i) ^ 2 ≠ 0 := by
    intro hgram0
    rcases gram_det_zero_imp_linearRelation c2' c3' hgram0 with ⟨a, b, hab, hlin⟩
    have hrel0 :
        ∑ i : Fin 4, (a * c2' i + b * c3' i) • mapVec e.toAlgHom u i = 0 := by
      rw [Fin.sum_univ_four]
      simp [hlin]
    have hpoly :
        a • q2h + b • q3h = 0 := by
      calc
        a • q2h + b • q3h
            = ∑ i : Fin 4, (a * c2' i + b * c3' i) • mapVec e.toAlgHom u i := by
                symm
                exact relation_linearCombination h2' h3' a b
        _ = 0 := hrel0
    have hm11 :
        a * MvPolynomial.coeff m11 q2h + b * MvPolynomial.coeff m11 q3h = 0 := by
      simpa [MvPolynomial.coeff_add, MvPolynomial.coeff_smul] using
        congrArg (MvPolynomial.coeff m11) hpoly
    have hm02 :
        a * MvPolynomial.coeff m02 q2h + b * MvPolynomial.coeff m02 q3h = 0 := by
      simpa [MvPolynomial.coeff_add, MvPolynomial.coeff_smul] using
        congrArg (MvPolynomial.coeff m02) hpoly
    have hdeth :
        MvPolynomial.coeff m11 q2h * MvPolynomial.coeff m02 q3h -
          MvPolynomial.coeff m02 q2h * MvPolynomial.coeff m11 q3h ≠ 0 := by
      simpa [hq2h_11, hq2h_02, hq3h_11, hq3h_02] using hdet
    have hdeta :
        a *
          (MvPolynomial.coeff m11 q2h * MvPolynomial.coeff m02 q3h -
            MvPolynomial.coeff m02 q2h * MvPolynomial.coeff m11 q3h) = 0 := by
      calc
        a *
            (MvPolynomial.coeff m11 q2h * MvPolynomial.coeff m02 q3h -
              MvPolynomial.coeff m02 q2h * MvPolynomial.coeff m11 q3h)
            =
          MvPolynomial.coeff m02 q3h *
              (a * MvPolynomial.coeff m11 q2h + b * MvPolynomial.coeff m11 q3h) -
            MvPolynomial.coeff m11 q3h *
              (a * MvPolynomial.coeff m02 q2h + b * MvPolynomial.coeff m02 q3h) := by
                ring
        _ = 0 := by rw [hm11, hm02]; ring
    have hdetb :
        b *
          (MvPolynomial.coeff m11 q2h * MvPolynomial.coeff m02 q3h -
            MvPolynomial.coeff m02 q2h * MvPolynomial.coeff m11 q3h) = 0 := by
      calc
        b *
            (MvPolynomial.coeff m11 q2h * MvPolynomial.coeff m02 q3h -
              MvPolynomial.coeff m02 q2h * MvPolynomial.coeff m11 q3h)
            =
          MvPolynomial.coeff m11 q2h *
              (a * MvPolynomial.coeff m02 q2h + b * MvPolynomial.coeff m02 q3h) -
            MvPolynomial.coeff m02 q2h *
              (a * MvPolynomial.coeff m11 q2h + b * MvPolynomial.coeff m11 q3h) := by
                ring
        _ = 0 := by rw [hm11, hm02]; ring
    have ha0 : a = 0 := (mul_eq_zero.mp hdeta).resolve_right hdeth
    have hb0 : b = 0 := (mul_eq_zero.mp hdetb).resolve_right hdeth
    rcases hab with ha | hb
    · exact ha ha0
    · exact hb hb0
  have hplane :
      homQuadPlaneA q2h q3h ≠ 0 ∨
        homQuadPlaneB q2h q3h ≠ 0 ∨
          homQuadPlaneC q2h q3h ≠ 0 := by
    left
    simpa [homQuadPlaneA, hq2h_11, hq2h_02, hq3h_11, hq3h_02] using hdet
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_homQuadratics_plane_nontrivial
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0e h1' h2' h3' hq2h hq3h
      hq2h_00 hq2h_10 hq2h_01
      hq3h_00 hq3h_10 hq3h_01
      hgram hplane hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_equiv_relations_const_x0_tailedPair_det_general
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hdet :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_tailedPair_det_general
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0 h1 h2 h3 hq2 hq3 hdet hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

private theorem homQuadPlane_nontrivial_linearIndependent
    {q2 q3 : Poly}
    (hplane :
      homQuadPlaneA q2 q3 ≠ 0 ∨
        homQuadPlaneB q2 q3 ≠ 0 ∨
          homQuadPlaneC q2 q3 ≠ 0)
    {a b : ℝ}
    (hrel : a • q2 + b • q3 = 0) :
    a = 0 ∧ b = 0 := by
  have hm20 :
      a * MvPolynomial.coeff m20 q2 + b * MvPolynomial.coeff m20 q3 = 0 := by
    simpa [MvPolynomial.coeff_add, MvPolynomial.coeff_smul] using
      congrArg (MvPolynomial.coeff m20) hrel
  have hm11 :
      a * MvPolynomial.coeff m11 q2 + b * MvPolynomial.coeff m11 q3 = 0 := by
    simpa [MvPolynomial.coeff_add, MvPolynomial.coeff_smul] using
      congrArg (MvPolynomial.coeff m11) hrel
  have hm02 :
      a * MvPolynomial.coeff m02 q2 + b * MvPolynomial.coeff m02 q3 = 0 := by
    simpa [MvPolynomial.coeff_add, MvPolynomial.coeff_smul] using
      congrArg (MvPolynomial.coeff m02) hrel
  rcases hplane with hA | hBC
  · have hdeta :
        a *
          (MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
            MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3) = 0 := by
      calc
        a *
            (MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
              MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3)
            =
          MvPolynomial.coeff m02 q3 *
              (a * MvPolynomial.coeff m11 q2 + b * MvPolynomial.coeff m11 q3) -
            MvPolynomial.coeff m11 q3 *
              (a * MvPolynomial.coeff m02 q2 + b * MvPolynomial.coeff m02 q3) := by
                ring
        _ = 0 := by rw [hm11, hm02]; ring
    have hdetb :
        b *
          (MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
            MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3) = 0 := by
      calc
        b *
            (MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
              MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3)
            =
          MvPolynomial.coeff m11 q2 *
              (a * MvPolynomial.coeff m02 q2 + b * MvPolynomial.coeff m02 q3) -
            MvPolynomial.coeff m02 q2 *
              (a * MvPolynomial.coeff m11 q2 + b * MvPolynomial.coeff m11 q3) := by
                ring
        _ = 0 := by rw [hm11, hm02]; ring
    have ha0 : a = 0 := (mul_eq_zero.mp hdeta).resolve_right hA
    have hb0 : b = 0 := (mul_eq_zero.mp hdetb).resolve_right hA
    exact ⟨ha0, hb0⟩
  · rcases hBC with hB | hC
    · have hdeta :
          a *
            (MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m02 q3 -
              MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3) = 0 := by
        calc
          a *
              (MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m02 q3 -
                MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3)
              =
            MvPolynomial.coeff m02 q3 *
                (a * MvPolynomial.coeff m20 q2 + b * MvPolynomial.coeff m20 q3) -
              MvPolynomial.coeff m20 q3 *
                (a * MvPolynomial.coeff m02 q2 + b * MvPolynomial.coeff m02 q3) := by
                  ring
          _ = 0 := by rw [hm20, hm02]; ring
      have hdetb :
          b *
            (MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m02 q3 -
              MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3) = 0 := by
        calc
          b *
              (MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m02 q3 -
                MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3)
              =
            MvPolynomial.coeff m20 q2 *
                (a * MvPolynomial.coeff m02 q2 + b * MvPolynomial.coeff m02 q3) -
              MvPolynomial.coeff m02 q2 *
                (a * MvPolynomial.coeff m20 q2 + b * MvPolynomial.coeff m20 q3) := by
                  ring
          _ = 0 := by rw [hm20, hm02]; ring
      have ha0 : a = 0 := (mul_eq_zero.mp hdeta).resolve_right hB
      have hb0 : b = 0 := (mul_eq_zero.mp hdetb).resolve_right hB
      exact ⟨ha0, hb0⟩
    · have hdeta :
          a *
            (MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m11 q3 -
              MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m20 q3) = 0 := by
        calc
          a *
              (MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m11 q3 -
                MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m20 q3)
              =
            MvPolynomial.coeff m11 q3 *
                (a * MvPolynomial.coeff m20 q2 + b * MvPolynomial.coeff m20 q3) -
              MvPolynomial.coeff m20 q3 *
                (a * MvPolynomial.coeff m11 q2 + b * MvPolynomial.coeff m11 q3) := by
                  ring
          _ = 0 := by rw [hm20, hm11]; ring
      have hdetb :
          b *
            (MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m11 q3 -
              MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m20 q3) = 0 := by
        calc
          b *
              (MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m11 q3 -
                MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m20 q3)
              =
            MvPolynomial.coeff m20 q2 *
                (a * MvPolynomial.coeff m11 q2 + b * MvPolynomial.coeff m11 q3) -
              MvPolynomial.coeff m11 q2 *
                (a * MvPolynomial.coeff m20 q2 + b * MvPolynomial.coeff m20 q3) := by
                  ring
          _ = 0 := by rw [hm20, hm11]; ring
      have ha0 : a = 0 := (mul_eq_zero.mp hdeta).resolve_right hC
      have hb0 : b = 0 := (mul_eq_zero.mp hdetb).resolve_right hC
      exact ⟨ha0, hb0⟩

private theorem gram_ne_zero_of_relations_const_x0_homQuadratics_plane_nontrivial
    {u : RankFourVec} {c2 c3 : Fin 4 → ℝ} {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hplane :
      homQuadPlaneA q2 q3 ≠ 0 ∨
        homQuadPlaneB q2 q3 ≠ 0 ∨
          homQuadPlaneC q2 q3 ≠ 0) :
    (∑ i : Fin 4, (c2 i) ^ 2) * (∑ i : Fin 4, (c3 i) ^ 2) -
      (∑ i : Fin 4, c2 i * c3 i) ^ 2 ≠ 0 := by
  intro hgram0
  rcases gram_det_zero_imp_linearRelation c2 c3 hgram0 with ⟨a, b, hab, hlin⟩
  have hrel0 : ∑ i : Fin 4, (a * c2 i + b * c3 i) • u i = 0 := by
    rw [Fin.sum_univ_four]
    simp [hlin]
  have hpoly : a • q2 + b • q3 = 0 := by
    calc
      a • q2 + b • q3
          = ∑ i : Fin 4, (a * c2 i + b * c3 i) • u i := by
              symm
              exact relation_linearCombination h2 h3 a b
      _ = 0 := hrel0
  rcases homQuadPlane_nontrivial_linearIndependent hplane hpoly with ⟨ha0, hb0⟩
  rcases hab with ha | hb
  · exact ha ha0
  · exact hb hb0

theorem residual_eq_zero_of_relations_const_x0_homQuadratics_plane_nontrivial_noGram
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 = 0)
    (hplane :
      homQuadPlaneA q2 q3 ≠ 0 ∨
        homQuadPlaneB q2 q3 ≠ 0 ∨
          homQuadPlaneC q2 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_relations_const_x0_homQuadratics_plane_nontrivial
    (B := B) (u := u) hu
    h0 h1 h2 h3 hq2 hq3 hq2_00 hq2_10 hq2_01 hq3_00 hq3_10 hq3_01
    (gram_ne_zero_of_relations_const_x0_homQuadratics_plane_nontrivial h2 h3 hplane)
    hplane hp hsocp

theorem residual_eq_zero_of_relations_const_x0_x0sqTail_m02_nonzero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq2_11 : MvPolynomial.coeff m11 q2 = 0)
    (hq2_02 : MvPolynomial.coeff m02 q2 = 0)
    (hq2_20 : MvPolynomial.coeff m20 q2 ≠ 0)
    (hq3_02 : MvPolynomial.coeff m02 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let t : ℝ := -(MvPolynomial.coeff m01 q3 / (2 * MvPolynomial.coeff m02 q3))
  let e : Poly ≃ₐ[ℝ] Poly := x1TranslateEquiv t
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := by
    exact isPositiveDefinite_dotTransport e (Fact.out : B.toQuadraticMap.PosDef)
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e)
      (heQuad := fun {_} hpq =>
        isQuadratic_affineEquiv
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1
          (x1TranslateVec t) (x1TranslateInvVec t)
          (by simp) (by simp)
          (x1TranslateInv_add_mulVec t) (x1Translate_add_mulVec_inv t)
          hpq)
      (heQuartic := fun {_} hpq =>
        isQuartic_affineEquiv
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1
          (x1TranslateVec t) (x1TranslateInvVec t)
          (by simp) (by simp)
          (x1TranslateInv_add_mulVec t) (x1Translate_add_mulVec_inv t)
          hpq)
      hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv
      (e := e)
      (he := fun {_} hpq =>
        isQuadratic_affineEquiv
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1
          (x1TranslateVec t) (x1TranslateInvVec t)
          (by simp) (by simp)
          (x1TranslateInv_add_mulVec t) (x1Translate_add_mulVec_inv t)
          hpq)
      hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv
      (e := e)
      (heSymm := fun {_} hpq =>
        isQuadratic_affineEquiv_symm
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1
          (x1TranslateVec t) (x1TranslateInvVec t)
          (by simp) (by simp)
          (x1TranslateInv_add_mulVec t) (x1Translate_add_mulVec_inv t)
          hpq)
      hsocp
  have he_one : e (1 : Poly) = (1 : Poly) := by
    simp [e]
  have he_x0 : e x0 = x0 := by
    rw [show e x0 = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) x0 by rfl]
    simp [affineHom_x1Translate_x0]
  let q2t : Poly := e q2
  let q3t : Poly := e q3
  let a3 : ℝ := MvPolynomial.coeff m10 q3t
  let b3q : ℝ := MvPolynomial.coeff m00 q3t
  let c3h : Fin 4 → ℝ := fun i => c3 i + (-a3) * c1 i + (-b3q) * c0 i
  let q3h : Poly := q3t - a3 • (x0 : Poly) - b3q • (1 : Poly)
  have h0e : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly) := by
    simpa [he_one] using relation_map e.toAlgHom h0
  have h1e : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x0 := by
    simpa [he_x0] using relation_map e.toAlgHom h1
  have h2e : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = q2t := by
    simpa [q2t] using relation_map e.toAlgHom h2
  have h3e : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = q3t := by
    simpa [q3t] using relation_map e.toAlgHom h3
  have h3' : ∑ i : Fin 4, c3h i • mapVec e.toAlgHom u i = q3h := by
    simpa [c3h, q3h, sub_eq_add_neg, add_assoc] using
      relation_sub_const_x0 h0e h1e h3e a3 b3q
  have hq2t : IsQuadratic q2t := by
    dsimp [q2t, e]
    change IsQuadratic
      (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) q2)
    exact isQuadratic_affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) hq2
  have hq3t : IsQuadratic q3t := by
    dsimp [q3t, e]
    change IsQuadratic
      (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) q3)
    exact isQuadratic_affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) hq3
  have hq3h : IsQuadratic q3h := by
    dsimp [q3h]
    have hx0 : IsQuadratic (x0 : Poly) := by
      simpa [x0] using (show IsQuadratic (MvPolynomial.X 0 : Poly) by
        simp [IsQuadratic])
    have h1poly : IsQuadratic (1 : Poly) := by
      simp [IsQuadratic]
    have htmp : IsQuadratic (q3t + (-a3) • (x0 : Poly)) := by
      simpa [a3] using isQuadratic_linearCombination_local hq3t hx0 1 (-a3)
    simpa [sub_eq_add_neg, add_assoc, b3q] using
      (isQuadratic_linearCombination_local htmp h1poly 1 (-b3q))
  have hq2t_00 : MvPolynomial.coeff m00 q2t = 0 := by
    dsimp [q2t]
    rw [show e q2 = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) q2 by rfl]
    rw [coeff_m00_affineHom_x1Translate hq2, hq2_00, hq2_01, hq2_02]
    ring
  have hq2t_10 : MvPolynomial.coeff m10 q2t = 0 := by
    dsimp [q2t]
    rw [show e q2 = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) q2 by rfl]
    rw [coeff_m10_affineHom_x1Translate hq2, hq2_10, hq2_11]
    ring
  have hq2t_01 : MvPolynomial.coeff m01 q2t = 0 := by
    dsimp [q2t]
    rw [show e q2 = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) q2 by rfl]
    rw [coeff_m01_affineHom_x1Translate hq2, hq2_01, hq2_02]
    ring
  have hq2t_11 : MvPolynomial.coeff m11 q2t = 0 := by
    dsimp [q2t]
    rw [show e q2 = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) q2 by rfl]
    rw [coeff_m11_affineHom_x1Translate hq2, hq2_11]
  have hq2t_02 : MvPolynomial.coeff m02 q2t = 0 := by
    dsimp [q2t]
    rw [show e q2 = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) q2 by rfl]
    rw [coeff_m02_affineHom_x1Translate hq2, hq2_02]
  have hq2t_20 : MvPolynomial.coeff m20 q2t ≠ 0 := by
    dsimp [q2t]
    rw [show e q2 = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) q2 by rfl]
    rw [coeff_m20_affineHom_x1Translate hq2]
    exact hq2_20
  have hq3t_01 : MvPolynomial.coeff m01 q3t = 0 := by
    dsimp [q3t, t]
    rw [show e q3 = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (x1TranslateVec (-(MvPolynomial.coeff m01 q3 / (2 * MvPolynomial.coeff m02 q3)))) q3 by rfl]
    exact coeff_m01_affineHom_x1Translate_kill hq3 hq3_02
  have hq3t_02 : MvPolynomial.coeff m02 q3t ≠ 0 := by
    dsimp [q3t]
    rw [show e q3 = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) q3 by rfl]
    rw [coeff_m02_affineHom_x1Translate hq3]
    exact hq3_02
  have hcoeff_x0_00 : MvPolynomial.coeff m00 (x0 : Poly) = 0 := by simp [x0, m00]
  have hcoeff_x0_10 : MvPolynomial.coeff m10 (x0 : Poly) = 1 := by simp [x0, m10]
  have hcoeff_x0_01 : MvPolynomial.coeff m01 (x0 : Poly) = 0 := by simp [x0, m01]
  have hcoeff_x0_02 : MvPolynomial.coeff m02 (x0 : Poly) = 0 := by simp [x0, m02]
  have hcoeff_one_00 : MvPolynomial.coeff m00 (1 : Poly) = 1 := by simp [m00]
  have hcoeff_one_10 : MvPolynomial.coeff m10 (1 : Poly) = 0 := by
    change MvPolynomial.coeff m10 (MvPolynomial.C (1 : ℝ)) = 0
    simpa [m10] using (MvPolynomial.coeff_C (σ := Fin 2) (R := ℝ) m10 (1 : ℝ))
  have hcoeff_one_01 : MvPolynomial.coeff m01 (1 : Poly) = 0 := by
    change MvPolynomial.coeff m01 (MvPolynomial.C (1 : ℝ)) = 0
    simpa [m01] using (MvPolynomial.coeff_C (σ := Fin 2) (R := ℝ) m01 (1 : ℝ))
  have hcoeff_one_02 : MvPolynomial.coeff m02 (1 : Poly) = 0 := by
    change MvPolynomial.coeff m02 (MvPolynomial.C (1 : ℝ)) = 0
    simpa [m02] using (MvPolynomial.coeff_C (σ := Fin 2) (R := ℝ) m02 (1 : ℝ))
  have hq3h_00 : MvPolynomial.coeff m00 q3h = 0 := by
    dsimp [q3h, a3, b3q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hcoeff_x0_00, hcoeff_one_00]
    simp
  have hq3h_10 : MvPolynomial.coeff m10 q3h = 0 := by
    dsimp [q3h, a3, b3q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hcoeff_x0_10, hcoeff_one_10]
    simp
  have hq3h_01 : MvPolynomial.coeff m01 q3h = 0 := by
    dsimp [q3h, a3, b3q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hq3t_01, hcoeff_x0_01, hcoeff_one_01]
    simp
  have hq3h_02 : MvPolynomial.coeff m02 q3h ≠ 0 := by
    dsimp [q3h, a3, b3q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hcoeff_x0_02, hcoeff_one_02]
    simpa using hq3t_02
  have hplane :
      homQuadPlaneA q2t q3h ≠ 0 ∨
        homQuadPlaneB q2t q3h ≠ 0 ∨
          homQuadPlaneC q2t q3h ≠ 0 := by
    right
    left
    simpa [homQuadPlaneB, hq2t_02] using mul_ne_zero hq2t_20 hq3h_02
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_homQuadratics_plane_nontrivial_noGram
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0e h1e h2e h3' hq2t hq3h
      hq2t_00 hq2t_10 hq2t_01
      hq3h_00 hq3h_10 hq3h_01
      hplane hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_const_x0_x0sqTail_m11_nonzero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq2_11 : MvPolynomial.coeff m11 q2 = 0)
    (hq2_02 : MvPolynomial.coeff m02 q2 = 0)
    (hq2_20 : MvPolynomial.coeff m20 q2 ≠ 0)
    (hq3_11 : MvPolynomial.coeff m11 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let t : ℝ := -(MvPolynomial.coeff m01 q3 / MvPolynomial.coeff m11 q3)
  let e : Poly ≃ₐ[ℝ] Poly := x0TranslateEquiv t
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := by
    exact isPositiveDefinite_dotTransport e (Fact.out : B.toQuadraticMap.PosDef)
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e)
      (heQuad := fun {_} hpq =>
        isQuadratic_affineEquiv
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1
          (x0TranslateVec t) (x0TranslateInvVec t)
          (by simp) (by simp)
          (x0TranslateInv_add_mulVec t) (x0Translate_add_mulVec_inv t)
          hpq)
      (heQuartic := fun {_} hpq =>
        isQuartic_affineEquiv
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1
          (x0TranslateVec t) (x0TranslateInvVec t)
          (by simp) (by simp)
          (x0TranslateInv_add_mulVec t) (x0Translate_add_mulVec_inv t)
          hpq)
      hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv
      (e := e)
      (he := fun {_} hpq =>
        isQuadratic_affineEquiv
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1
          (x0TranslateVec t) (x0TranslateInvVec t)
          (by simp) (by simp)
          (x0TranslateInv_add_mulVec t) (x0Translate_add_mulVec_inv t)
          hpq)
      hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv
      (e := e)
      (heSymm := fun {_} hpq =>
        isQuadratic_affineEquiv_symm
          (1 : Matrix (Fin 2) (Fin 2) ℝ) 1
          (x0TranslateVec t) (x0TranslateInvVec t)
          (by simp) (by simp)
          (x0TranslateInv_add_mulVec t) (x0Translate_add_mulVec_inv t)
          hpq)
      hsocp
  have he_one : e (1 : Poly) = (1 : Poly) := by
    simp [e]
  have he_x0 : e x0 = MvPolynomial.C t + x0 := by
    rw [show e x0 = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec t) x0 by rfl]
    simp [affineHom_x0Translate_x0]
  let q2t : Poly := e q2
  let q3t : Poly := e q3
  have h0e : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly) := by
    simpa [he_one] using relation_map e.toAlgHom h0
  have h1e :
      ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = MvPolynomial.C t + x0 := by
    simpa [he_x0] using relation_map e.toAlgHom h1
  have h2e : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = q2t := by
    simpa [q2t] using relation_map e.toAlgHom h2
  have h3e : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = q3t := by
    simpa [q3t] using relation_map e.toAlgHom h3
  have hq2t : IsQuadratic q2t := by
    dsimp [q2t, e]
    change IsQuadratic
      (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec t) q2)
    exact isQuadratic_affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec t) hq2
  have hq3t : IsQuadratic q3t := by
    dsimp [q3t, e]
    change IsQuadratic
      (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec t) q3)
    exact isQuadratic_affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec t) hq3
  have hq2t_11 :
      MvPolynomial.coeff m11 q2t = 0 := by
    dsimp [q2t]
    rw [show e q2 = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec t) q2 by rfl]
    rw [coeff_m11_affineHom_x0Translate hq2, hq2_11]
  have hq2t_02 :
      MvPolynomial.coeff m02 q2t = 0 := by
    dsimp [q2t]
    rw [show e q2 = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec t) q2 by rfl]
    rw [coeff_m02_affineHom_x0Translate hq2, hq2_02]
  have hq2t_01 :
      MvPolynomial.coeff m01 q2t = 0 := by
    dsimp [q2t]
    rw [show e q2 = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec t) q2 by rfl]
    rw [coeff_m01_affineHom_x0Translate hq2, hq2_01, hq2_11]
    ring
  have hq2t_20 :
      MvPolynomial.coeff m20 q2t = MvPolynomial.coeff m20 q2 := by
    dsimp [q2t]
    rw [show e q2 = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec t) q2 by rfl]
    rw [quadratic_eq_quadForm hq2, affineHom_x0Translate_quadForm]
    simp
  have hq3t_01 :
      MvPolynomial.coeff m01 q3t = 0 := by
    dsimp [q3t, t]
    rw [show e q3 = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (x0TranslateVec (-(MvPolynomial.coeff m01 q3 / MvPolynomial.coeff m11 q3))) q3 by rfl]
    rw [coeff_m01_affineHom_x0Translate hq3]
    field_simp [hq3_11]
    ring
  let a2 : ℝ := MvPolynomial.coeff m10 q2t
  let b2q : ℝ := MvPolynomial.coeff m00 q2t
  let a3 : ℝ := MvPolynomial.coeff m10 q3t
  let b3q : ℝ := MvPolynomial.coeff m00 q3t
  let q2h : Poly := q2t - a2 • (x0 : Poly) - b2q • (1 : Poly)
  let q3h : Poly := q3t - a3 • (x0 : Poly) - b3q • (1 : Poly)
  let c1' : Fin 4 → ℝ := fun i => c1 i + (-t) * c0 i
  have h1' : ∑ i : Fin 4, c1' i • mapVec e.toAlgHom u i = x0 := by
    calc
      ∑ i : Fin 4, c1' i • mapVec e.toAlgHom u i
          = (1 : ℝ) • (MvPolynomial.C t + x0) + (-t) • (1 : Poly) := by
              simpa [c1'] using relation_linearCombination h1e h0e 1 (-t)
      _ = x0 := by
            simp [MvPolynomial.smul_eq_C_mul]
  let c2' : Fin 4 → ℝ := fun i => c2 i + (-a2) * c1' i + (-b2q) * c0 i
  let c3' : Fin 4 → ℝ := fun i => c3 i + (-a3) * c1' i + (-b3q) * c0 i
  have h2' : ∑ i : Fin 4, c2' i • mapVec e.toAlgHom u i = q2h := by
    simpa [c2', q2h, sub_eq_add_neg, add_assoc] using
      relation_sub_const_x0 h0e h1' h2e a2 b2q
  have h3' : ∑ i : Fin 4, c3' i • mapVec e.toAlgHom u i = q3h := by
    simpa [c3', q3h, sub_eq_add_neg, add_assoc] using
      relation_sub_const_x0 h0e h1' h3e a3 b3q
  have hq2h : IsQuadratic q2h := by
    dsimp [q2h]
    have hx0 : IsQuadratic (x0 : Poly) := by
      simpa [x0] using (show IsQuadratic (MvPolynomial.X 0 : Poly) by
        simp [IsQuadratic])
    have h1poly : IsQuadratic (1 : Poly) := by
      simp [IsQuadratic]
    have htmp : IsQuadratic (q2t + (-a2) • (x0 : Poly)) := by
      simpa using isQuadratic_linearCombination_local hq2t hx0 1 (-a2)
    simpa [sub_eq_add_neg, add_assoc] using
      (isQuadratic_linearCombination_local htmp h1poly 1 (-b2q))
  have hq3h : IsQuadratic q3h := by
    dsimp [q3h]
    have hx0 : IsQuadratic (x0 : Poly) := by
      simpa [x0] using (show IsQuadratic (MvPolynomial.X 0 : Poly) by
        simp [IsQuadratic])
    have h1poly : IsQuadratic (1 : Poly) := by
      simp [IsQuadratic]
    have htmp : IsQuadratic (q3t + (-a3) • (x0 : Poly)) := by
      simpa using isQuadratic_linearCombination_local hq3t hx0 1 (-a3)
    simpa [sub_eq_add_neg, add_assoc] using
      (isQuadratic_linearCombination_local htmp h1poly 1 (-b3q))
  have hcoeff_x0_00 : MvPolynomial.coeff m00 (x0 : Poly) = 0 := by simp [x0, m00]
  have hcoeff_x0_10 : MvPolynomial.coeff m10 (x0 : Poly) = 1 := by simp [x0, m10]
  have hcoeff_x0_01 : MvPolynomial.coeff m01 (x0 : Poly) = 0 := by simp [x0, m01]
  have hcoeff_x0_11 : MvPolynomial.coeff m11 (x0 : Poly) = 0 := by
    simpa [x0, m10] using (MvPolynomial.coeff_X' (σ := Fin 2) (R := ℝ) 0 m11)
  have hcoeff_one_00 : MvPolynomial.coeff m00 (1 : Poly) = 1 := by simp [m00]
  have hcoeff_one_10 : MvPolynomial.coeff m10 (1 : Poly) = 0 := by
    change MvPolynomial.coeff m10 (MvPolynomial.C (1 : ℝ)) = 0
    simpa [m10] using (MvPolynomial.coeff_C (σ := Fin 2) (R := ℝ) m10 (1 : ℝ))
  have hcoeff_one_01 : MvPolynomial.coeff m01 (1 : Poly) = 0 := by
    change MvPolynomial.coeff m01 (MvPolynomial.C (1 : ℝ)) = 0
    simpa [m01] using (MvPolynomial.coeff_C (σ := Fin 2) (R := ℝ) m01 (1 : ℝ))
  have hcoeff_one_11 : MvPolynomial.coeff m11 (1 : Poly) = 0 := by
    change MvPolynomial.coeff m11 (MvPolynomial.C (1 : ℝ)) = 0
    simpa [m11] using (MvPolynomial.coeff_C (σ := Fin 2) (R := ℝ) m11 (1 : ℝ))
  have hcoeff_one_02 : MvPolynomial.coeff m02 (1 : Poly) = 0 := by
    change MvPolynomial.coeff m02 (MvPolynomial.C (1 : ℝ)) = 0
    simpa [m02] using (MvPolynomial.coeff_C (σ := Fin 2) (R := ℝ) m02 (1 : ℝ))
  have hq2h_00 : MvPolynomial.coeff m00 q2h = 0 := by
    dsimp [q2h, a2, b2q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hcoeff_x0_00, hcoeff_one_00]
    dsimp [b2q]
    ring_nf
  have hq2h_10 : MvPolynomial.coeff m10 q2h = 0 := by
    dsimp [q2h, a2, b2q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hcoeff_x0_10, hcoeff_one_10]
    dsimp [a2]
    ring_nf
  have hq2h_01 : MvPolynomial.coeff m01 q2h = 0 := by
    dsimp [q2h, a2, b2q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hq2t_01, hcoeff_x0_01, hcoeff_one_01]
    simp
  have hq2h_11 : MvPolynomial.coeff m11 q2h = 0 := by
    dsimp [q2h, a2, b2q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hq2t_11, hcoeff_x0_11, hcoeff_one_11]
    simp
  have hq3h_00 : MvPolynomial.coeff m00 q3h = 0 := by
    dsimp [q3h, a3, b3q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hcoeff_x0_00, hcoeff_one_00]
    simp
  have hq3h_10 : MvPolynomial.coeff m10 q3h = 0 := by
    dsimp [q3h, a3, b3q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hcoeff_x0_10, hcoeff_one_10]
    simp
  have hq3h_01 : MvPolynomial.coeff m01 q3h = 0 := by
    dsimp [q3h, a3, b3q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, hq3t_01, hcoeff_x0_01, hcoeff_one_01]
    simp
  have hq2h_20 :
      MvPolynomial.coeff m20 q2h = MvPolynomial.coeff m20 q2 := by
    dsimp [q2h, a2, b2q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul]
    have hcoeff_x0_20 : MvPolynomial.coeff m20 (x0 : Poly) = 0 := by simp [x0, m20]
    have hcoeff_one_20 : MvPolynomial.coeff m20 (1 : Poly) = 0 := by
      change MvPolynomial.coeff m20 (MvPolynomial.C (1 : ℝ)) = 0
      simpa [m20] using (MvPolynomial.coeff_C (σ := Fin 2) (R := ℝ) m20 (1 : ℝ))
    rw [hq2t_20, hcoeff_x0_20, hcoeff_one_20]
    simp
  have hq3h_11 :
      MvPolynomial.coeff m11 q3h = MvPolynomial.coeff m11 q3 := by
    dsimp [q3h, a3, b3q]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul]
    have hq3t_11 :
        MvPolynomial.coeff m11 q3t = MvPolynomial.coeff m11 q3 := by
      dsimp [q3t]
      rw [show e q3 = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x0TranslateVec t) q3 by rfl]
      rw [coeff_m11_affineHom_x0Translate hq3]
    rw [hq3t_11, hcoeff_x0_11, hcoeff_one_11]
    simp
  have hplane :
      homQuadPlaneA q2h q3h ≠ 0 ∨
        homQuadPlaneB q2h q3h ≠ 0 ∨
          homQuadPlaneC q2h q3h ≠ 0 := by
    right
    right
    have h20 :
        MvPolynomial.coeff m20 q2h ≠ 0 := by
      rw [hq2h_20]
      exact hq2_20
    have h11 :
        MvPolynomial.coeff m11 q3h ≠ 0 := by
      rw [hq3h_11]
      exact hq3_11
    simpa [homQuadPlaneC, hq2h_11] using mul_ne_zero h20 h11
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_homQuadratics_plane_nontrivial_noGram
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0e h1' h2' h3' hq2h hq3h
      hq2h_00 hq2h_10 hq2h_01
      hq3h_00 hq3h_10 hq3h_01
      hplane hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_const_x0_x0sqTail_m11_m02_zero_of_m01_nonzero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq2_11 : MvPolynomial.coeff m11 q2 = 0)
    (hq2_02 : MvPolynomial.coeff m02 q2 = 0)
    (hq2_20 : MvPolynomial.coeff m20 q2 ≠ 0)
    (hq3_11 : MvPolynomial.coeff m11 q3 = 0)
    (hq3_02 : MvPolynomial.coeff m02 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let a : ℝ := MvPolynomial.coeff m20 q3 / MvPolynomial.coeff m20 q2
  let q : Poly := q3 - a • q2
  let cq : Fin 4 → ℝ := fun i => (-a) * c2 i + c3 i
  have hq : IsQuadratic q := by
    dsimp [q]
    simpa [sub_eq_add_neg, add_comm] using isQuadratic_linearCombination_local hq3 hq2 1 (-a)
  have hq_20 : MvPolynomial.coeff m20 q = 0 := by
    dsimp [q, a]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_smul]
    have hmul :
        (MvPolynomial.coeff m20 q3 / MvPolynomial.coeff m20 q2) •
            MvPolynomial.coeff m20 q2 =
          MvPolynomial.coeff m20 q3 := by
      simpa [smul_eq_mul] using
        (show
          (MvPolynomial.coeff m20 q3 / MvPolynomial.coeff m20 q2) *
              MvPolynomial.coeff m20 q2 =
            MvPolynomial.coeff m20 q3 by
              field_simp [hq2_20])
    rw [hmul]
    simp
  have hq_11 : MvPolynomial.coeff m11 q = 0 := by
    dsimp [q, a]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, hq3_11, hq2_11]
    simp
  have hq_02 : MvPolynomial.coeff m02 q = 0 := by
    dsimp [q, a]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, hq3_02, hq2_02]
    simp
  have hq_01 :
      MvPolynomial.coeff m01 q = MvPolynomial.coeff m01 q3 := by
    dsimp [q, a]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, hq2_01]
    simp
  have hqrel : ∑ i : Fin 4, cq i • u i = q := by
    calc
      ∑ i : Fin 4, cq i • u i
          = (-a) • q2 + (1 : ℝ) • q3 := by
              simpa [cq] using relation_linearCombination h2 h3 (-a) 1
      _ = q := by
            simp [q, sub_eq_add_neg, add_comm]
  have hq_01_ne : MvPolynomial.coeff m01 q ≠ 0 := by
    simpa [hq_01] using hq3_01
  exact residual_eq_zero_of_relations_const_x0_affineTail
    (B := B) (u := u) hu
    h0 h1 hqrel hq hq_20 hq_11 hq_02 hq_01_ne hp hsocp

theorem residual_eq_zero_of_relations_const_x0_x0sqTail_m02_zero_of_m01_nonzero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq2_11 : MvPolynomial.coeff m11 q2 = 0)
    (hq2_02 : MvPolynomial.coeff m02 q2 = 0)
    (hq2_20 : MvPolynomial.coeff m20 q2 ≠ 0)
    (hq3_02 : MvPolynomial.coeff m02 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  by_cases hq3_11 : MvPolynomial.coeff m11 q3 = 0
  · exact residual_eq_zero_of_relations_const_x0_x0sqTail_m11_m02_zero_of_m01_nonzero
      (B := B) (u := u) hu
      h0 h1 h2 h3 hq2 hq3
      hq2_01 hq2_11 hq2_02 hq2_20 hq3_11 hq3_02 hq3_01 hp hsocp
  · exact residual_eq_zero_of_relations_const_x0_x0sqTail_m11_nonzero
      (B := B) (u := u) hu
      h0 h1 h2 h3 hq2 hq3
      hq2_01 hq2_11 hq2_02 hq2_20 hq3_11 hp hsocp

theorem residual_eq_zero_of_relations_const_x0_homQuadratics_dependent_gram
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c2 c3 : Fin 4 → ℝ} {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 = 0)
    (hA0 : homQuadPlaneA q2 q3 = 0)
    (hB0 : homQuadPlaneB q2 q3 = 0)
    (hC0 : homQuadPlaneC q2 q3 = 0)
    (hgram :
      (∑ i : Fin 4, (c2 i) ^ 2) * (∑ i : Fin 4, (c3 i) ^ 2) -
        (∑ i : Fin 4, c2 i * c3 i) ^ 2 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  by_cases hq2zero : q2 = 0
  · have hrel : ∑ i : Fin 4, c2 i • u i = 0 := by simpa [hq2zero] using h2
    have hc : c2 ≠ 0 := by
      intro hc0
      have hgram0 := gram_det_zero_of_linearRelation c2 c3 (a := 1) (b := 0)
        (Or.inl one_ne_zero) (by
          intro i
          have hci := congrArg (fun z : Fin 4 → ℝ => z i) hc0
          simpa using hci)
      exact hgram hgram0
    exact residual_eq_zero_of_constant_relation (B := B) (u := u) hu hrel hc hp hsocp
  · by_cases h20 : MvPolynomial.coeff m20 q2 ≠ 0
    · let c : Fin 4 → ℝ := fun i =>
        MvPolynomial.coeff m20 q3 * c2 i + (-MvPolynomial.coeff m20 q2) * c3 i
      have hBswap :
          MvPolynomial.coeff m20 q3 * MvPolynomial.coeff m02 q2 -
            MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m02 q3 = 0 := by
        dsimp [homQuadPlaneB] at hB0
        linarith
      have hCswap :
          MvPolynomial.coeff m20 q3 * MvPolynomial.coeff m11 q2 -
            MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m11 q3 = 0 := by
        dsimp [homQuadPlaneC] at hC0
        linarith
      have hrel : ∑ i : Fin 4, c i • u i = 0 := by
        calc
          ∑ i : Fin 4, c i • u i
              = ∑ i : Fin 4,
                  (MvPolynomial.coeff m20 q3 * c2 i + (-MvPolynomial.coeff m20 q2) * c3 i) • u i := by
                    simp [c]
          _ = MvPolynomial.coeff m20 q3 • q2 +
                  (-MvPolynomial.coeff m20 q2) • q3 := by
                exact relation_linearCombination h2 h3 _ _
          _ = 0 := by
            have hcombq :
                IsQuadratic
                  (MvPolynomial.coeff m20 q3 • q2 +
                    (-MvPolynomial.coeff m20 q2) • q3) := by
              exact isQuadratic_linearCombination_local hq2 hq3 _ _
            have hcomb00 :
                MvPolynomial.coeff m00
                  (MvPolynomial.coeff m20 q3 • q2 +
                    (-MvPolynomial.coeff m20 q2) • q3) = 0 := by
              simp [hq2_00, hq3_00]
            have hcomb10 :
                MvPolynomial.coeff m10
                  (MvPolynomial.coeff m20 q3 • q2 +
                    (-MvPolynomial.coeff m20 q2) • q3) = 0 := by
              simp [hq2_10, hq3_10]
            have hcomb01 :
                MvPolynomial.coeff m01
                  (MvPolynomial.coeff m20 q3 • q2 +
                    (-MvPolynomial.coeff m20 q2) • q3) = 0 := by
              simp [hq2_01, hq3_01]
            have hcomb20 :
                MvPolynomial.coeff m20
                  (MvPolynomial.coeff m20 q3 • q2 +
                    (-MvPolynomial.coeff m20 q2) • q3) = 0 := by
              simp
              ring
            have hcomb11 :
                MvPolynomial.coeff m11
                  (MvPolynomial.coeff m20 q3 • q2 +
                    (-MvPolynomial.coeff m20 q2) • q3) = 0 := by
              simpa [sub_eq_add_neg] using hCswap
            have hcomb02 :
                MvPolynomial.coeff m02
                  (MvPolynomial.coeff m20 q3 • q2 +
                    (-MvPolynomial.coeff m20 q2) • q3) = 0 := by
              simpa [sub_eq_add_neg] using hBswap
            rw [quadratic_eq_quadForm hcombq, hcomb00, hcomb10, hcomb01,
              hcomb20, hcomb11, hcomb02]
            simp [quadForm]
      have hc : c ≠ 0 := by
        intro hc0
        have hgram0 := gram_det_zero_of_linearRelation c2 c3
          (a := MvPolynomial.coeff m20 q3) (b := -MvPolynomial.coeff m20 q2)
          (Or.inr (neg_ne_zero.mpr h20)) (by
            intro i
            have hci := congrArg (fun z : Fin 4 → ℝ => z i) hc0
            simpa [c] using hci)
        exact hgram hgram0
      exact residual_eq_zero_of_constant_relation (B := B) (u := u) hu hrel hc hp hsocp
    · by_cases h11 : MvPolynomial.coeff m11 q2 ≠ 0
      · let c : Fin 4 → ℝ := fun i =>
          MvPolynomial.coeff m11 q3 * c2 i + (-MvPolynomial.coeff m11 q2) * c3 i
        have hAswap :
            MvPolynomial.coeff m11 q3 * MvPolynomial.coeff m02 q2 -
              MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 = 0 := by
          dsimp [homQuadPlaneA] at hA0
          linarith
        have hCswap :
            MvPolynomial.coeff m11 q3 * MvPolynomial.coeff m20 q2 -
              MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m20 q3 = 0 := by
          dsimp [homQuadPlaneC] at hC0
          linarith
        have hrel : ∑ i : Fin 4, c i • u i = 0 := by
          calc
            ∑ i : Fin 4, c i • u i
                = ∑ i : Fin 4,
                    (MvPolynomial.coeff m11 q3 * c2 i + (-MvPolynomial.coeff m11 q2) * c3 i) • u i := by
                      simp [c]
            _ = MvPolynomial.coeff m11 q3 • q2 +
                    (-MvPolynomial.coeff m11 q2) • q3 := by
                  exact relation_linearCombination h2 h3 _ _
            _ = 0 := by
              have hcombq :
                  IsQuadratic
                    (MvPolynomial.coeff m11 q3 • q2 +
                      (-MvPolynomial.coeff m11 q2) • q3) := by
                exact isQuadratic_linearCombination_local hq2 hq3 _ _
              have hcomb00 :
                  MvPolynomial.coeff m00
                    (MvPolynomial.coeff m11 q3 • q2 +
                      (-MvPolynomial.coeff m11 q2) • q3) = 0 := by
                simp [hq2_00, hq3_00]
              have hcomb10 :
                  MvPolynomial.coeff m10
                    (MvPolynomial.coeff m11 q3 • q2 +
                      (-MvPolynomial.coeff m11 q2) • q3) = 0 := by
                simp [hq2_10, hq3_10]
              have hcomb01 :
                  MvPolynomial.coeff m01
                    (MvPolynomial.coeff m11 q3 • q2 +
                      (-MvPolynomial.coeff m11 q2) • q3) = 0 := by
                simp [hq2_01, hq3_01]
              have hcomb20 :
                  MvPolynomial.coeff m20
                    (MvPolynomial.coeff m11 q3 • q2 +
                      (-MvPolynomial.coeff m11 q2) • q3) = 0 := by
                simpa [sub_eq_add_neg] using hCswap
              have hcomb11 :
                  MvPolynomial.coeff m11
                    (MvPolynomial.coeff m11 q3 • q2 +
                      (-MvPolynomial.coeff m11 q2) • q3) = 0 := by
                simp
                ring
              have hcomb02 :
                  MvPolynomial.coeff m02
                    (MvPolynomial.coeff m11 q3 • q2 +
                      (-MvPolynomial.coeff m11 q2) • q3) = 0 := by
                simpa [sub_eq_add_neg] using hAswap
              rw [quadratic_eq_quadForm hcombq, hcomb00, hcomb10, hcomb01,
                hcomb20, hcomb11, hcomb02]
              simp [quadForm]
        have hc : c ≠ 0 := by
          intro hc0
          have hgram0 := gram_det_zero_of_linearRelation c2 c3
            (a := MvPolynomial.coeff m11 q3) (b := -MvPolynomial.coeff m11 q2)
            (Or.inr (neg_ne_zero.mpr h11)) (by
              intro i
              have hci := congrArg (fun z : Fin 4 → ℝ => z i) hc0
              simpa [c] using hci)
          exact hgram hgram0
        exact residual_eq_zero_of_constant_relation (B := B) (u := u) hu hrel hc hp hsocp
      · have h20z : MvPolynomial.coeff m20 q2 = 0 := by
          by_contra h20z
          exact h20 h20z
        have h11z : MvPolynomial.coeff m11 q2 = 0 := by
          by_contra h11z
          exact h11 h11z
        have h02 : MvPolynomial.coeff m02 q2 ≠ 0 := by
          intro h02z
          have hq2zero' : q2 = 0 := by
            rw [quadratic_eq_quadForm hq2, quadForm_eq_explicit]
            simp [hq2_00, hq2_10, hq2_01, h20z, h11z, h02z]
          exact hq2zero hq2zero'
        have h20q3z : MvPolynomial.coeff m20 q3 = 0 := by
          have hB0' : MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m02 q3 -
              MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3 = 0 := by
            simpa [homQuadPlaneB] using hB0
          rw [h20z] at hB0'
          have : -(MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3) = 0 := by
            simpa using hB0'
          have : MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3 = 0 := by
            linarith
          by_cases h20q3 : MvPolynomial.coeff m20 q3 = 0
          · exact h20q3
          · exfalso
            rcases mul_eq_zero.mp this with h02z | h20q3z
            · exact h02 h02z
            · exact h20q3 h20q3z
        have h11q3z : MvPolynomial.coeff m11 q3 = 0 := by
          have hA0' : MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
              MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0 := by
            simpa [homQuadPlaneA] using hA0
          rw [h11z] at hA0'
          have : -(MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3) = 0 := by
            simpa using hA0'
          have : MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0 := by
            linarith
          by_cases h11q3 : MvPolynomial.coeff m11 q3 = 0
          · exact h11q3
          · exfalso
            rcases mul_eq_zero.mp this with h02z | h11q3z
            · exact h02 h02z
            · exact h11q3 h11q3z
        let c : Fin 4 → ℝ := fun i =>
          MvPolynomial.coeff m02 q3 * c2 i + (-MvPolynomial.coeff m02 q2) * c3 i
        have hrel : ∑ i : Fin 4, c i • u i = 0 := by
          calc
            ∑ i : Fin 4, c i • u i
                = ∑ i : Fin 4,
                    (MvPolynomial.coeff m02 q3 * c2 i + (-MvPolynomial.coeff m02 q2) * c3 i) • u i := by
                      simp [c]
            _ = MvPolynomial.coeff m02 q3 • q2 +
                    (-MvPolynomial.coeff m02 q2) • q3 := by
                  exact relation_linearCombination h2 h3 _ _
            _ = 0 := by
              have hcombq :
                  IsQuadratic
                    (MvPolynomial.coeff m02 q3 • q2 +
                      (-MvPolynomial.coeff m02 q2) • q3) := by
                exact isQuadratic_linearCombination_local hq2 hq3 _ _
              have hcomb00 :
                  MvPolynomial.coeff m00
                    (MvPolynomial.coeff m02 q3 • q2 +
                      (-MvPolynomial.coeff m02 q2) • q3) = 0 := by
                simp [hq2_00, hq3_00]
              have hcomb10 :
                  MvPolynomial.coeff m10
                    (MvPolynomial.coeff m02 q3 • q2 +
                      (-MvPolynomial.coeff m02 q2) • q3) = 0 := by
                simp [hq2_10, hq3_10]
              have hcomb01 :
                  MvPolynomial.coeff m01
                    (MvPolynomial.coeff m02 q3 • q2 +
                      (-MvPolynomial.coeff m02 q2) • q3) = 0 := by
                simp [hq2_01, hq3_01]
              have hcomb20 :
                  MvPolynomial.coeff m20
                    (MvPolynomial.coeff m02 q3 • q2 +
                      (-MvPolynomial.coeff m02 q2) • q3) = 0 := by
                simp [h20z, h20q3z]
              have hcomb11 :
                  MvPolynomial.coeff m11
                    (MvPolynomial.coeff m02 q3 • q2 +
                      (-MvPolynomial.coeff m02 q2) • q3) = 0 := by
                simp [h11z, h11q3z]
              have hcomb02 :
                  MvPolynomial.coeff m02
                    (MvPolynomial.coeff m02 q3 • q2 +
                      (-MvPolynomial.coeff m02 q2) • q3) = 0 := by
                simp
                ring
              rw [quadratic_eq_quadForm hcombq, hcomb00, hcomb10, hcomb01,
                hcomb20, hcomb11, hcomb02]
              simp [quadForm]
        have hc : c ≠ 0 := by
          intro hc0
          have hgram0 := gram_det_zero_of_linearRelation c2 c3
            (a := MvPolynomial.coeff m02 q3) (b := -MvPolynomial.coeff m02 q2)
            (Or.inr (neg_ne_zero.mpr h02)) (by
              intro i
              have hci := congrArg (fun z : Fin 4 → ℝ => z i) hc0
              simpa [c] using hci)
          exact hgram hgram0
        exact residual_eq_zero_of_constant_relation (B := B) (u := u) hu hrel hc hp hsocp

theorem residual_eq_zero_of_relations_const_x0_homQuadratics_cases
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 = 0)
    (hgram :
      (∑ i : Fin 4, (c2 i) ^ 2) * (∑ i : Fin 4, (c3 i) ^ 2) -
        (∑ i : Fin 4, c2 i * c3 i) ^ 2 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  by_cases hplane :
      homQuadPlaneA q2 q3 ≠ 0 ∨
        homQuadPlaneB q2 q3 ≠ 0 ∨
          homQuadPlaneC q2 q3 ≠ 0
  · exact residual_eq_zero_of_relations_const_x0_homQuadratics_plane_nontrivial_noGram
      (B := B) (u := u) hu
      h0 h1 h2 h3 hq2 hq3 hq2_00 hq2_10 hq2_01 hq3_00 hq3_10 hq3_01
      hplane hp hsocp
  · push Not at hplane
    rcases hplane with ⟨hA0, hB0, hC0⟩
    exact residual_eq_zero_of_relations_const_x0_homQuadratics_dependent_gram
      (B := B) (u := u) hu
      h2 h3 hq2 hq3 hq2_00 hq2_10 hq2_01 hq3_00 hq3_10 hq3_01
      hA0 hB0 hC0 hgram hp hsocp

private def relationColsMatrix
    (c0 c1 c2 c3 : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j =>
    match j with
    | 0 => c0 i
    | 1 => c1 i
    | 2 => c2 i
    | 3 => c3 i

private theorem mix_relationColsMatrix_transpose
    (u : RankFourVec) (c0 c1 c2 c3 : Fin 4 → ℝ) :
    mix (relationColsMatrix c0 c1 c2 c3).transpose u =
      ![∑ i : Fin 4, c0 i • u i,
        ∑ i : Fin 4, c1 i • u i,
        ∑ i : Fin 4, c2 i • u i,
        ∑ i : Fin 4, c3 i • u i] := by
  funext i
  fin_cases i <;> simp [mix, relationColsMatrix, Matrix.transpose_apply, Fin.sum_univ_four]

private theorem relationColsMatrix_transpose_mul_self_eq_one
    (c0 c1 c2 c3 : Fin 4 → ℝ)
    (h00 : ∑ i : Fin 4, (c0 i) ^ 2 = 1)
    (h11 : ∑ i : Fin 4, (c1 i) ^ 2 = 1)
    (h22 : ∑ i : Fin 4, (c2 i) ^ 2 = 1)
    (h33 : ∑ i : Fin 4, (c3 i) ^ 2 = 1)
    (h01 : ∑ i : Fin 4, c0 i * c1 i = 0)
    (h02 : ∑ i : Fin 4, c0 i * c2 i = 0)
    (h03 : ∑ i : Fin 4, c0 i * c3 i = 0)
    (h12 : ∑ i : Fin 4, c1 i * c2 i = 0)
    (h13 : ∑ i : Fin 4, c1 i * c3 i = 0)
    (h23 : ∑ i : Fin 4, c2 i * c3 i = 0) :
    (relationColsMatrix c0 c1 c2 c3).transpose * relationColsMatrix c0 c1 c2 c3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [relationColsMatrix, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Fin.sum_univ_four, pow_two] using h00
  · simpa [relationColsMatrix, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Fin.sum_univ_four] using h01
  · simpa [relationColsMatrix, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Fin.sum_univ_four] using h02
  · simpa [relationColsMatrix, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Fin.sum_univ_four] using h03
  · simpa [relationColsMatrix, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Fin.sum_univ_four, mul_comm] using h01
  · simpa [relationColsMatrix, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Fin.sum_univ_four, pow_two] using h11
  · simpa [relationColsMatrix, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Fin.sum_univ_four] using h12
  · simpa [relationColsMatrix, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Fin.sum_univ_four] using h13
  · simpa [relationColsMatrix, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Fin.sum_univ_four, mul_comm] using h02
  · simpa [relationColsMatrix, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Fin.sum_univ_four, mul_comm] using h12
  · simpa [relationColsMatrix, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Fin.sum_univ_four, pow_two] using h22
  · simpa [relationColsMatrix, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Fin.sum_univ_four] using h23
  · simpa [relationColsMatrix, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Fin.sum_univ_four, mul_comm] using h03
  · simpa [relationColsMatrix, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Fin.sum_univ_four, mul_comm] using h13
  · simpa [relationColsMatrix, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Fin.sum_univ_four, mul_comm] using h23
  · simpa [relationColsMatrix, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Fin.sum_univ_four, pow_two] using h33

private theorem self_mul_transpose_eq_one_of_transpose_mul_self_eq_one
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hMtM : M.transpose * M = 1) :
    M * M.transpose = 1 := by
  have hdetSq : M.det * M.det = 1 := by
    have hdetEq := congrArg Matrix.det hMtM
    simpa [Matrix.det_mul, Matrix.det_transpose] using hdetEq
  have hdetUnit : IsUnit M.det := by
    refine ⟨⟨M.det, M.det, hdetSq, ?_⟩, rfl⟩
    simpa [mul_comm] using hdetSq
  have hInv : M⁻¹ = M.transpose := by
    exact Matrix.right_inv_eq_left_inv (Matrix.mul_nonsing_inv M hdetUnit) hMtM
  rw [← hInv]
  exact Matrix.mul_nonsing_inv M hdetUnit

theorem residual_eq_zero_of_relations_const_x0_tailedPair_det
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (h00 : ∑ i : Fin 4, (c0 i) ^ 2 = 1)
    (h11 : ∑ i : Fin 4, (c1 i) ^ 2 = 1)
    (h22 : ∑ i : Fin 4, (c2 i) ^ 2 = 1)
    (h33 : ∑ i : Fin 4, (c3 i) ^ 2 = 1)
    (h01 : ∑ i : Fin 4, c0 i * c1 i = 0)
    (h02 : ∑ i : Fin 4, c0 i * c2 i = 0)
    (h03 : ∑ i : Fin 4, c0 i * c3 i = 0)
    (h12 : ∑ i : Fin 4, c1 i * c2 i = 0)
    (h13 : ∑ i : Fin 4, c1 i * c3 i = 0)
    (h23 : ∑ i : Fin 4, c2 i * c3 i = 0)
    (hdet :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let M : Matrix (Fin 4) (Fin 4) ℝ := relationColsMatrix c0 c1 c2 c3
  have hMtM : M.transpose * M = 1 := by
    dsimp [M]
    exact relationColsMatrix_transpose_mul_self_eq_one c0 c1 c2 c3
      h00 h11 h22 h33 h01 h02 h03 h12 h13 h23
  have hMMt : M * M.transpose = 1 := by
    exact self_mul_transpose_eq_one_of_transpose_mul_self_eq_one M hMtM
  have huRep :
      mix M.transpose u = ![(1 : Poly), x0, q2, q3] := by
    rw [mix_relationColsMatrix_transpose]
    simp [h0, h1, h2, h3]
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec_const_x0_tailedPair_det
    (e := AlgEquiv.refl)
    (heQuad := fun {_} hq => hq)
    (heQuadSymm := fun {_} hq => hq)
    (heQuarticSymm := fun {_} hq => hq)
    (M := M) hMtM hMMt
    (hB := (Fact.out : B.toQuadraticMap.PosDef))
    hp hq2 hq3 hdet huRep hsocp

theorem residual_eq_zero_of_equiv_relations_const_x0_tailedPair_det
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (h00 : ∑ i : Fin 4, (c0 i) ^ 2 = 1)
    (h11 : ∑ i : Fin 4, (c1 i) ^ 2 = 1)
    (h22 : ∑ i : Fin 4, (c2 i) ^ 2 = 1)
    (h33 : ∑ i : Fin 4, (c3 i) ^ 2 = 1)
    (h01 : ∑ i : Fin 4, c0 i * c1 i = 0)
    (h02 : ∑ i : Fin 4, c0 i * c2 i = 0)
    (h03 : ∑ i : Fin 4, c0 i * c3 i = 0)
    (h12 : ∑ i : Fin 4, c1 i * c2 i = 0)
    (h13 : ∑ i : Fin 4, c1 i * c3 i = 0)
    (h23 : ∑ i : Fin 4, c2 i * c3 i = 0)
    (hdet :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_tailedPair_det
      (B := B0) (u := mapVec e.toAlgHom u)
      h0 h1 h2 h3 hq2 hq3
      h00 h11 h22 h33 h01 h02 h03 h12 h13 h23 hdet hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0


theorem residual_eq_zero_of_const_x0_mixedAffineTailHomLine_x0sqTail_cases
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (_hu : IsAdmissiblePoint u)
    {q2 q3 : Poly}
    (h0 : u 0 = (1 : Poly))
    (h1 : u 1 = x0)
    (h2 : u 2 = q2)
    (h3 : u 3 = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_20 : MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let a2 : ℝ := MvPolynomial.coeff m01 q2
  let a3 : ℝ := MvPolynomial.coeff m01 q3
  let alpha : ℝ := Real.sqrt (a2 ^ 2 + a3 ^ 2)
  let cH : Fin 4 → ℝ
    | 0 => 0
    | 1 => 0
    | 2 => a3 / alpha
    | 3 => -a2 / alpha
  let cP : Fin 4 → ℝ
    | 0 => 0
    | 1 => 0
    | 2 => a2 / alpha
    | 3 => a3 / alpha
  let qH : Poly := (1 / alpha) • mixedAffineTailHomLine q2 q3
  let qP : Poly := (a2 / alpha) • q2 + (a3 / alpha) • q3
  have halpha_sq : alpha ^ 2 = a2 ^ 2 + a3 ^ 2 := by
    have hnonneg : 0 ≤ a2 ^ 2 + a3 ^ 2 := by positivity
    dsimp [alpha]
    nlinarith [Real.sq_sqrt hnonneg]
  have halpha_pos : 0 < alpha := by
    dsimp [alpha, a2, a3]
    apply Real.sqrt_pos.mpr
    nlinarith [sq_pos_of_ne_zero hq3_01]
  have halpha_ne : alpha ≠ 0 := halpha_pos.ne'
  have hqH : IsQuadratic qH := by
    dsimp [qH]
    exact isQuadratic_smul_local (1 / alpha) (isQuadratic_mixedAffineTailHomLine hq2 hq3)
  have hqP : IsQuadratic qP := by
    dsimp [qP]
    exact isQuadratic_linearCombination_local hq2 hq3 (a2 / alpha) (a3 / alpha)
  have h00rel : ∑ i : Fin 4, (stdRel0 i) ^ 2 = 1 := by
    rw [Fin.sum_univ_four]
    norm_num [stdRel0]
  have h11rel : ∑ i : Fin 4, (stdRel1 i) ^ 2 = 1 := by
    rw [Fin.sum_univ_four]
    norm_num [stdRel1]
  have h22rel : ∑ i : Fin 4, (cH i) ^ 2 = 1 := by
    rw [Fin.sum_univ_four]
    dsimp [cH, alpha, a2, a3]
    field_simp [halpha_ne]
    nlinarith [halpha_sq]
  have h33rel : ∑ i : Fin 4, (cP i) ^ 2 = 1 := by
    rw [Fin.sum_univ_four]
    dsimp [cP, alpha, a2, a3]
    field_simp [halpha_ne]
    nlinarith [halpha_sq]
  have h01rel : ∑ i : Fin 4, stdRel0 i * stdRel1 i = 0 := by
    rw [Fin.sum_univ_four]
    norm_num [stdRel0, stdRel1]
  have h02rel : ∑ i : Fin 4, stdRel0 i * cH i = 0 := by
    rw [Fin.sum_univ_four]
    simp [stdRel0, cH]
  have h03rel : ∑ i : Fin 4, stdRel0 i * cP i = 0 := by
    rw [Fin.sum_univ_four]
    simp [stdRel0, cP]
  have h12rel : ∑ i : Fin 4, stdRel1 i * cH i = 0 := by
    rw [Fin.sum_univ_four]
    simp [stdRel1, cH]
  have h13rel : ∑ i : Fin 4, stdRel1 i * cP i = 0 := by
    rw [Fin.sum_univ_four]
    simp [stdRel1, cP]
  have h23rel : ∑ i : Fin 4, cH i * cP i = 0 := by
    rw [Fin.sum_univ_four]
    dsimp [cH, cP]
    field_simp [halpha_ne]
    ring
  let M : Matrix (Fin 4) (Fin 4) ℝ := relationColsMatrix stdRel0 stdRel1 cH cP
  have hMtM : M.transpose * M = 1 := by
    dsimp [M]
    exact relationColsMatrix_transpose_mul_self_eq_one stdRel0 stdRel1 cH cP
      h00rel h11rel h22rel h33rel h01rel h02rel h03rel h12rel h13rel h23rel
  have hMMt : M * M.transpose = 1 := by
    exact self_mul_transpose_eq_one_of_transpose_mul_self_eq_one M hMtM
  have h0rel : ∑ i : Fin 4, stdRel0 i • u i = (1 : Poly) := by
    simpa [stdRel0, Fin.sum_univ_four] using h0
  have h1rel : ∑ i : Fin 4, stdRel1 i • u i = x0 := by
    simpa [stdRel1, Fin.sum_univ_four] using h1
  have h2rel : ∑ i : Fin 4, stdRel2 i • u i = q2 := by
    simpa [stdRel2, Fin.sum_univ_four] using h2
  have h3rel : ∑ i : Fin 4, stdRel3 i • u i = q3 := by
    simpa [stdRel3, Fin.sum_univ_four] using h3
  have hHrel : ∑ i : Fin 4, cH i • u i = qH := by
    rw [Fin.sum_univ_four]
    dsimp [cH, qH, a2, a3]
    simp [h2, h3, mixedAffineTailHomLine, sub_eq_add_neg, smul_smul, div_eq_mul_inv, mul_comm]
  have hPrel : ∑ i : Fin 4, cP i • u i = qP := by
    rw [Fin.sum_univ_four]
    dsimp [cP, qP, a2, a3]
    simp [h2, h3, div_eq_mul_inv]
  have huRep : mix M.transpose u = ![(1 : Poly), x0, qH, qP] := by
    rw [mix_relationColsMatrix_transpose]
    simp [h0rel, h1rel, hHrel, hPrel]
  have hqH_00 : MvPolynomial.coeff m00 qH = 0 := by
    dsimp [qH]
    rw [MvPolynomial.coeff_smul, coeff_m00_mixedAffineTailHomLine, hq2_00, hq3_00]
    simp
  have hqH_10 : MvPolynomial.coeff m10 qH = 0 := by
    dsimp [qH]
    rw [MvPolynomial.coeff_smul, coeff_m10_mixedAffineTailHomLine, hq2_10, hq3_10]
    simp
  have hqH_01 : MvPolynomial.coeff m01 qH = 0 := by
    dsimp [qH]
    rw [MvPolynomial.coeff_smul, coeff_m01_mixedAffineTailHomLine]
    simp
  have hqH_11 : MvPolynomial.coeff m11 qH = 0 := by
    dsimp [qH]
    rw [MvPolynomial.coeff_smul, hline_11]
    simp
  have hqH_02 : MvPolynomial.coeff m02 qH = 0 := by
    dsimp [qH]
    rw [MvPolynomial.coeff_smul, hline_02]
    simp
  have hqH_20 : MvPolynomial.coeff m20 qH ≠ 0 := by
    dsimp [qH]
    rw [MvPolynomial.coeff_smul]
    simpa [smul_eq_mul, one_div] using mul_ne_zero (inv_ne_zero halpha_ne) hline_20
  by_cases hqP_02 : MvPolynomial.coeff m02 qP = 0
  · exact residual_eq_zero_of_socp_of_eq_mix_mapVec_const_x0_x0sqTail_m02_zero
      (e := AlgEquiv.refl)
      (heQuad := fun {_} hq => hq)
      (heQuadSymm := fun {_} hq => hq)
      (heQuarticSymm := fun {_} hq => hq)
      (M := M) hMtM hMMt
      (hB := (Fact.out : B.toQuadraticMap.PosDef))
      hp hqH hqP hqH_01 hqH_11 hqH_02 hqH_20 hqP_02 huRep hsocp
  · exact residual_eq_zero_of_socp_of_eq_mix_mapVec_const_x0_x0sqTail_m02_nonzero
      (e := AlgEquiv.refl)
      (heQuad := fun {_} hq => hq)
      (heQuadSymm := fun {_} hq => hq)
      (heQuarticSymm := fun {_} hq => hq)
      (M := M) hMtM hMMt
      (hB := (Fact.out : B.toQuadraticMap.PosDef))
      hp hqH hqP hqH_00 hqH_10 hqH_01 hqH_11 hqH_02 hqH_20 hqP_02 huRep hsocp

theorem residual_eq_zero_of_equiv_const_x0_mixedAffineTailHomLine_x0sqTail_cases
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {q2 q3 : Poly}
    (h0 : mapVec e.toAlgHom u 0 = (1 : Poly))
    (h1 : mapVec e.toAlgHom u 1 = x0)
    (h2 : mapVec e.toAlgHom u 2 = q2)
    (h3 : mapVec e.toAlgHom u 3 = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_20 : MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_const_x0_mixedAffineTailHomLine_x0sqTail_cases
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0 h1 h2 h3 hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
      hline_20 hline_11 hline_02 hq3_01 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_socp_of_eq_mix_mapVec_const_x0_mixedAffineTailHomLine_x0sqTail_cases
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuarticSymm : ∀ {p : Poly}, IsQuartic p → IsQuartic (e.symm p))
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hMtM : M.transpose * M = 1)
    (hMMt : M * M.transpose = 1)
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_20 : MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (huRep : mix M.transpose (mapVec e.symm.toAlgHom u) = ![(1 : Poly), x0, q2, q3])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have huRepAdmissible : IsAdmissiblePoint (![(1 : Poly), x0, q2, q3] : RankFourVec) := by
    exact admissiblePoint_const_x0_pair hq2 hq3
  have hRep :
      ∀ {B0 : DotForm} [Fact B0.toQuadraticMap.PosDef] {p0 : Poly},
        IsSOSQuartic p0 → IsSOCP B0 p0 (![(1 : Poly), x0, q2, q3] : RankFourVec) →
          residual p0 (![(1 : Poly), x0, q2, q3] : RankFourVec) = 0 := by
    intro B0 _ p0 hp0 hsocp0
    exact residual_eq_zero_of_const_x0_mixedAffineTailHomLine_x0sqTail_cases
      (B := B0) (u := ![(1 : Poly), x0, q2, q3]) huRepAdmissible
      (by simp) (by simp [x0]) (by simp) (by simp)
      hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
      hline_20 hline_11 hline_02 hq3_01 hp0 hsocp0
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec
    (![(1 : Poly), x0, q2, q3])
    hRep e heQuad heQuadSymm heQuarticSymm M hMtM hMMt hB hp huRep hsocp

theorem residual_eq_zero_of_socp_of_eq_mix_affineEquiv_const_x0_mixedAffineTailHomLine_x0sqTail_cases
    (A A' : Matrix (Fin 2) (Fin 2) ℝ) (b b' : Fin 2 → ℝ)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (hb : ∀ i, b' i + Matrix.mulVec A' b i = 0)
    (hb' : ∀ i, b i + Matrix.mulVec A b' i = 0)
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hMtM : M.transpose * M = 1)
    (hMMt : M * M.transpose = 1)
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_20 : MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (huRep :
      mix M.transpose
        (mapVec (affineEquiv A A' b b' hAA' hA'A hb hb').symm.toAlgHom u) =
          ![(1 : Poly), x0, q2, q3])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec_const_x0_mixedAffineTailHomLine_x0sqTail_cases
    (e := affineEquiv A A' b b' hAA' hA'A hb hb')
    (heQuad := fun {_} hpq => isQuadratic_affineEquiv A A' b b' hAA' hA'A hb hb' hpq)
    (heQuadSymm := fun {_} hpq => isQuadratic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (heQuarticSymm := fun {_} hpq => isQuartic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (M := M) hMtM hMMt hB hp
    hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
    hline_20 hline_11 hline_02 hq3_01 huRep hsocp

theorem residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_x0sqTail_cases
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_20 : MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let a2 : ℝ := MvPolynomial.coeff m01 q2
  let a3 : ℝ := MvPolynomial.coeff m01 q3
  let alpha : ℝ := Real.sqrt (a2 ^ 2 + a3 ^ 2)
  let cH : Fin 4 → ℝ := fun i => (a3 / alpha) * c2 i + (-(a2 / alpha)) * c3 i
  let cP : Fin 4 → ℝ := fun i => (a2 / alpha) * c2 i + (a3 / alpha) * c3 i
  let qH : Poly := (1 / alpha) • mixedAffineTailHomLine q2 q3
  let qP : Poly := (a2 / alpha) • q2 + (a3 / alpha) • q3
  have halpha_sq : alpha ^ 2 = a2 ^ 2 + a3 ^ 2 := by
    have hnonneg : 0 ≤ a2 ^ 2 + a3 ^ 2 := by positivity
    dsimp [alpha]
    nlinarith [Real.sq_sqrt hnonneg]
  have halpha_pos : 0 < alpha := by
    dsimp [alpha, a2, a3]
    apply Real.sqrt_pos.mpr
    nlinarith [sq_pos_of_ne_zero hq3_01]
  have halpha_ne : alpha ≠ 0 := halpha_pos.ne'
  have hqH : IsQuadratic qH := by
    dsimp [qH]
    exact isQuadratic_smul_local (1 / alpha) (isQuadratic_mixedAffineTailHomLine hq2 hq3)
  have hqP : IsQuadratic qP := by
    dsimp [qP]
    exact isQuadratic_linearCombination_local hq2 hq3 (a2 / alpha) (a3 / alpha)
  have hHrel : ∑ i : Fin 4, cH i • u i = qH := by
    calc
      ∑ i : Fin 4, cH i • u i
          = (a3 / alpha) • q2 + (-(a2 / alpha)) • q3 := by
              simpa [cH] using relation_linearCombination h2 h3 (a3 / alpha) (-(a2 / alpha))
      _ = qH := by
            simp [qH, mixedAffineTailHomLine, a2, a3, sub_eq_add_neg,
              smul_smul, div_eq_mul_inv, mul_comm]
  have hPrel : ∑ i : Fin 4, cP i • u i = qP := by
    calc
      ∑ i : Fin 4, cP i • u i
          = (a2 / alpha) • q2 + (a3 / alpha) • q3 := by
              simpa [cP] using relation_linearCombination h2 h3 (a2 / alpha) (a3 / alpha)
      _ = qP := by simp [qP]
  have hqH_00 : MvPolynomial.coeff m00 qH = 0 := by
    dsimp [qH]
    rw [MvPolynomial.coeff_smul, coeff_m00_mixedAffineTailHomLine, hq2_00, hq3_00]
    simp
  have hqH_10 : MvPolynomial.coeff m10 qH = 0 := by
    dsimp [qH]
    rw [MvPolynomial.coeff_smul, coeff_m10_mixedAffineTailHomLine, hq2_10, hq3_10]
    simp
  have hqH_01 : MvPolynomial.coeff m01 qH = 0 := by
    dsimp [qH]
    rw [MvPolynomial.coeff_smul, coeff_m01_mixedAffineTailHomLine]
    simp
  have hqH_11 : MvPolynomial.coeff m11 qH = 0 := by
    dsimp [qH]
    rw [MvPolynomial.coeff_smul, hline_11]
    simp
  have hqH_02 : MvPolynomial.coeff m02 qH = 0 := by
    dsimp [qH]
    rw [MvPolynomial.coeff_smul, hline_02]
    simp
  have hqH_20 : MvPolynomial.coeff m20 qH ≠ 0 := by
    dsimp [qH]
    rw [MvPolynomial.coeff_smul]
    simpa [smul_eq_mul, one_div] using mul_ne_zero (inv_ne_zero halpha_ne) hline_20
  have hqP_01 : MvPolynomial.coeff m01 qP = alpha := by
    calc
      MvPolynomial.coeff m01 qP
          = (a2 / alpha) * MvPolynomial.coeff m01 q2 +
              (a3 / alpha) * MvPolynomial.coeff m01 q3 := by
                dsimp [qP, a2, a3]
                rw [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul]
                simp [smul_eq_mul]
      _ = (a2 ^ 2 + a3 ^ 2) / alpha := by
            field_simp [halpha_ne]
            dsimp [a2, a3]
            ring
      _ = alpha := by
            apply (div_eq_iff halpha_ne).2
            nlinarith [halpha_sq]
  have hqP_01_ne : MvPolynomial.coeff m01 qP ≠ 0 := by
    rw [hqP_01]
    exact halpha_ne
  by_cases hqP_02 : MvPolynomial.coeff m02 qP = 0
  · exact residual_eq_zero_of_relations_const_x0_x0sqTail_m02_zero_of_m01_nonzero
      (B := B) (u := u) hu
      h0 h1 hHrel hPrel hqH hqP
      hqH_01 hqH_11 hqH_02 hqH_20 hqP_02 hqP_01_ne hp hsocp
  · exact residual_eq_zero_of_relations_const_x0_x0sqTail_m02_nonzero
      (B := B) (u := u) hu
      h0 h1 hHrel hPrel hqH hqP
      hqH_00 hqH_10 hqH_01 hqH_11 hqH_02 hqH_20 hqP_02 hp hsocp

theorem residual_eq_zero_of_equiv_relations_const_x0_mixedAffineTailHomLine_x0sqTail_cases
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hline_20 : MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) ≠ 0)
    (hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) = 0)
    (hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_x0sqTail_cases
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0 h1 h2 h3 hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
      hline_20 hline_11 hline_02 hq3_01 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_origDetZero_cases_gram
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hqdet0 :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (hgram :
      (∑ i : Fin 4, (c2 i) ^ 2) * (∑ i : Fin 4, (c3 i) ^ 2) -
        (∑ i : Fin 4, c2 i * c3 i) ^ 2 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  by_cases hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) = 0
  · by_cases hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) = 0
    · by_cases hline_20 : MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) = 0
      · let cH : Fin 4 → ℝ := fun i =>
          MvPolynomial.coeff m01 q3 * c2 i + (-MvPolynomial.coeff m01 q2) * c3 i
        have hrelH :
            ∑ i : Fin 4, cH i • u i = mixedAffineTailHomLine q2 q3 := by
          simpa [cH] using relation_mixedAffineTailHomLine (u := u) h2 h3
        have hHzero : mixedAffineTailHomLine q2 q3 = 0 := by
          rw [homogeneousQuadratic_eq_mixedAffineTailHomLine hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10]
          rw [← coeff_m20_mixedAffineTailHomLine, ← coeff_m11_mixedAffineTailHomLine,
            ← coeff_m02_mixedAffineTailHomLine, hline_20, hline_11, hline_02]
          simp
        have hrel : ∑ i : Fin 4, cH i • u i = 0 := by
          rw [hrelH, hHzero]
        have hcH : cH ≠ 0 := by
          intro hc0
          have hgram0 := gram_det_zero_of_linearRelation c2 c3
            (a := MvPolynomial.coeff m01 q3) (b := -MvPolynomial.coeff m01 q2)
            (Or.inl hq3_01) (by
              intro i
              have hci := congrArg (fun z : Fin 4 → ℝ => z i) hc0
              simpa [cH] using hci)
          exact hgram hgram0
        exact residual_eq_zero_of_constant_relation (B := B) (u := u) hu hrel hcH hp hsocp
      · exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_x0sqTail_cases
          (B := B) (u := u) hu
          h0 h1 h2 h3 hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
          hline_20 hline_11 hline_02 hq3_01 hp hsocp
    · exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_crossShear_origDetZero_cases
        (B := B) (u := u) hu
        h0 h1 h2 h3 hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
        hline_02 hline_11 hqdet0 hq3_01 hp hsocp
  · exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_diagShear_origDetZero_cases
      (B := B) (u := u) hu
      h0 h1 h2 h3 hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
      hline_02 hqdet0 hq3_01 hp hsocp

theorem residual_eq_zero_of_equiv_relations_const_x0_mixedAffineTailHomLine_origDetZero_cases_gram
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hqdet0 :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (hgram :
      (∑ i : Fin 4, (c2 i) ^ 2) * (∑ i : Fin 4, (c3 i) ^ 2) -
        (∑ i : Fin 4, c2 i * c3 i) ^ 2 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_origDetZero_cases_gram
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0 h1 h2 h3 hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
      hqdet0 hq3_01 hgram hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_const_x0_pair_coeff_m00_m10_zero_gram
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hgram :
      (∑ i : Fin 4, (c2 i) ^ 2) * (∑ i : Fin 4, (c3 i) ^ 2) -
        (∑ i : Fin 4, c2 i * c3 i) ^ 2 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  by_cases hdet :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 ≠ 0
  · exact residual_eq_zero_of_relations_const_x0_tailedPair_det_general
      (B := B) (u := u) hu
      h0 h1 h2 h3 hq2 hq3 hdet hp hsocp
  · have hdet0 :
        MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
          MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0 := by
      by_contra hdet0
      exact hdet hdet0
    by_cases hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0
    · exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_origDetZero_cases_gram
        (B := B) (u := u) hu
        h0 h1 h2 h3 hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
        hdet0 hq3_01 hgram hp hsocp
    · by_cases hq2_01 : MvPolynomial.coeff m01 q2 ≠ 0
      · have hdet0swap :
            MvPolynomial.coeff m11 q3 * MvPolynomial.coeff m02 q2 -
              MvPolynomial.coeff m02 q3 * MvPolynomial.coeff m11 q2 = 0 := by
          linarith
        have hgramSwap :
            (∑ i : Fin 4, (c3 i) ^ 2) * (∑ i : Fin 4, (c2 i) ^ 2) -
              (∑ i : Fin 4, c3 i * c2 i) ^ 2 ≠ 0 := by
          simpa [mul_comm] using hgram
        exact residual_eq_zero_of_relations_const_x0_mixedAffineTailHomLine_origDetZero_cases_gram
          (B := B) (u := u) hu
          h0 h1 h3 h2 hq3 hq2 hq3_00 hq3_10 hq2_00 hq2_10
          hdet0swap hq2_01 hgramSwap hp hsocp
      · have hq2_01z : MvPolynomial.coeff m01 q2 = 0 := by
          by_contra hq2_01z
          exact hq2_01 hq2_01z
        have hq3_01z : MvPolynomial.coeff m01 q3 = 0 := by
          by_contra hq3_01z
          exact hq3_01 hq3_01z
        exact residual_eq_zero_of_relations_const_x0_homQuadratics_cases
          (B := B) (u := u) hu
          h0 h1 h2 h3 hq2 hq3
          hq2_00 hq2_10 hq2_01z hq3_00 hq3_10 hq3_01z
          hgram hp hsocp

theorem residual_eq_zero_of_equiv_relations_const_x0_pair_coeff_m00_m10_zero_gram
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hgram :
      (∑ i : Fin 4, (c2 i) ^ 2) * (∑ i : Fin 4, (c3 i) ^ 2) -
        (∑ i : Fin 4, c2 i * c3 i) ^ 2 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_pair_coeff_m00_m10_zero_gram
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0 h1 h2 h3 hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
      hgram hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_const_affineLine_pair_coeff_m00_m10_zero_gram
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    {r a b : ℝ}
    (h1 : ∑ i : Fin 4, c1 i • u i = affineLinePoly r a b)
    (hs : a ^ 2 + b ^ 2 ≠ 0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 ((affineLineEquiv r a b hs) q2) = 0)
    (hq2_10 : MvPolynomial.coeff m10 ((affineLineEquiv r a b hs) q2) = 0)
    (hq3_00 : MvPolynomial.coeff m00 ((affineLineEquiv r a b hs) q3) = 0)
    (hq3_10 : MvPolynomial.coeff m10 ((affineLineEquiv r a b hs) q3) = 0)
    (hgram :
      (∑ i : Fin 4, (c2 i) ^ 2) * (∑ i : Fin 4, (c3 i) ^ 2) -
        (∑ i : Fin 4, c2 i * c3 i) ^ 2 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let e : Poly ≃ₐ[ℝ] Poly := affineLineEquiv r a b hs
  have heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q) := by
    intro q hq
    exact isQuadratic_affineEquiv
      (affineLineMatrix a b) (affineLineInvMatrix a b)
      (affineLineVec r a b) (affineLineInvVec r)
      (affineLine_mul_inv a b hs) (affineLine_inv_mul a b hs)
      (affineLineInv_add_mulVec r a b hs) (affineLine_add_mulVec_inv r a b hs) hq
  have heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q) := by
    intro q hq
    exact isQuadratic_affineEquiv_symm
      (affineLineMatrix a b) (affineLineInvMatrix a b)
      (affineLineVec r a b) (affineLineInvVec r)
      (affineLine_mul_inv a b hs) (affineLine_inv_mul a b hs)
      (affineLineInv_add_mulVec r a b hs) (affineLine_add_mulVec_inv r a b hs) hq
  have heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q) := by
    intro q hq
    exact isQuartic_affineEquiv
      (affineLineMatrix a b) (affineLineInvMatrix a b)
      (affineLineVec r a b) (affineLineInvVec r)
      (affineLine_mul_inv a b hs) (affineLine_inv_mul a b hs)
      (affineLineInv_add_mulVec r a b hs) (affineLine_add_mulVec_inv r a b hs) hq
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  have h0' : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly) := by
    simpa [e] using relation_map e.toAlgHom h0
  have h1' : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x0 := by
    simpa [e, affineLineEquiv] using
      (relation_map e.toAlgHom h1).trans (affineHom_affineLinePoly r a b hs)
  have h2' : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = e q2 := by
    simpa [e] using relation_map e.toAlgHom h2
  have h3' : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = e q3 := by
    simpa [e] using relation_map e.toAlgHom h3
  exact residual_eq_zero_of_equiv_relations_const_x0_pair_coeff_m00_m10_zero_gram
    (e := e) (heQuad := fun {_} hq => heQuad hq) (heQuadSymm := fun {_} hq => heQuadSymm hq)
    (heQuartic := fun {_} hq => heQuartic hq)
    hB hp hu hsocp h0' h1' h2' h3'
    (heQuad hq2) (heQuad hq3)
    (by simpa [e] using hq2_00) (by simpa [e] using hq2_10)
    (by simpa [e] using hq3_00) (by simpa [e] using hq3_10)
    hgram

theorem residual_eq_zero_of_const_x0_mixedAffineTailHomLine_origDetZero_cases
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {q2 q3 : Poly}
    (h0 : u 0 = (1 : Poly))
    (h1 : u 1 = x0)
    (h2 : u 2 = q2)
    (h3 : u 3 = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hqdet0 :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  by_cases hline_02 : MvPolynomial.coeff m02 (mixedAffineTailHomLine q2 q3) = 0
  · by_cases hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) = 0
    · by_cases hline_20 : MvPolynomial.coeff m20 (mixedAffineTailHomLine q2 q3) = 0
      · let c : Fin 4 → ℝ
          | 0 => 0
          | 1 => 0
          | 2 => MvPolynomial.coeff m01 q3
          | 3 => -MvPolynomial.coeff m01 q2
        have hrelH :
            ∑ i : Fin 4, c i • u i = mixedAffineTailHomLine q2 q3 := by
          calc
            ∑ i : Fin 4, c i • u i
                = MvPolynomial.coeff m01 q3 • q2 +
                    (-MvPolynomial.coeff m01 q2) • q3 := by
                      simp [c, Fin.sum_univ_four, h2, h3]
            _ = mixedAffineTailHomLine q2 q3 := by
                  simp [mixedAffineTailHomLine, sub_eq_add_neg]
        have hHzero : mixedAffineTailHomLine q2 q3 = 0 := by
          rw [homogeneousQuadratic_eq_mixedAffineTailHomLine hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10]
          rw [← coeff_m20_mixedAffineTailHomLine, ← coeff_m11_mixedAffineTailHomLine,
            ← coeff_m02_mixedAffineTailHomLine, hline_20, hline_11, hline_02]
          simp
        have hrel : ∑ i : Fin 4, c i • u i = 0 := by
          rw [hrelH, hHzero]
        have hc : c ≠ 0 := by
          intro hc0
          have hc2 := congrArg (fun z : Fin 4 → ℝ => z 2) hc0
          exact hq3_01 (by simpa [c] using hc2)
        exact residual_eq_zero_of_constant_relation (B := B) (u := u) hu hrel hc hp hsocp
      · exact residual_eq_zero_of_const_x0_mixedAffineTailHomLine_x0sqTail_cases
          (B := B) (u := u) hu
          h0 h1 h2 h3 hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
          hline_20 hline_11 hline_02 hq3_01 hp hsocp
    · exact residual_eq_zero_of_equiv_const_x0_mixedAffineTailHomLine_crossShear_origDetZero_cases
        (e := AlgEquiv.refl)
        (heQuad := fun {_} hq => hq)
        (heQuadSymm := fun {_} hq => hq)
        (heQuartic := fun {_} hq => hq)
        (hB := (Fact.out : B.toQuadraticMap.PosDef))
        hp hu hsocp
        (h0 := by simpa using h0)
        (h1 := by simpa using h1)
        (h2 := by simpa using h2)
        (h3 := by simpa using h3)
        hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
        hline_02 hline_11 hqdet0 hq3_01
  · by_cases hline_11 : MvPolynomial.coeff m11 (mixedAffineTailHomLine q2 q3) = 0
    · exact residual_eq_zero_of_equiv_const_x0_mixedAffineTailHomLine_diagX1sqTail_origDetZero_cases
        (e := AlgEquiv.refl)
        (heQuad := fun {_} hq => hq)
        (heQuadSymm := fun {_} hq => hq)
        (heQuartic := fun {_} hq => hq)
        (hB := (Fact.out : B.toQuadraticMap.PosDef))
        hp hu hsocp
        (h0 := by simpa using h0)
        (h1 := by simpa using h1)
        (h2 := by simpa using h2)
        (h3 := by simpa using h3)
        hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
        hline_11 hline_02 hqdet0 hq3_01
    · exact residual_eq_zero_of_equiv_const_x0_mixedAffineTailHomLine_diagShear_origDetZero_cases
        (e := AlgEquiv.refl)
        (heQuad := fun {_} hq => hq)
        (heQuadSymm := fun {_} hq => hq)
        (heQuartic := fun {_} hq => hq)
        (hB := (Fact.out : B.toQuadraticMap.PosDef))
        hp hu hsocp
        (h0 := by simpa using h0)
        (h1 := by simpa using h1)
        (h2 := by simpa using h2)
        (h3 := by simpa using h3)
        hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10
        hline_02 hqdet0 hq3_01

theorem residual_eq_zero_of_equiv_const_x0_mixedAffineTailHomLine_origDetZero_cases
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {q2 q3 : Poly}
    (h0 : mapVec e.toAlgHom u 0 = (1 : Poly))
    (h1 : mapVec e.toAlgHom u 1 = x0)
    (h2 : mapVec e.toAlgHom u 2 = q2)
    (h3 : mapVec e.toAlgHom u 3 = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hqdet0 :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_const_x0_mixedAffineTailHomLine_origDetZero_cases
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0 h1 h2 h3 hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10 hqdet0 hq3_01 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_socp_of_eq_mix_mapVec_const_x0_mixedAffineTailHomLine_origDetZero_cases
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuarticSymm : ∀ {p : Poly}, IsQuartic p → IsQuartic (e.symm p))
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hMtM : M.transpose * M = 1)
    (hMMt : M * M.transpose = 1)
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hqdet0 :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (huRep : mix M.transpose (mapVec e.symm.toAlgHom u) = ![(1 : Poly), x0, q2, q3])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have huRepAdmissible : IsAdmissiblePoint (![(1 : Poly), x0, q2, q3] : RankFourVec) := by
    exact admissiblePoint_const_x0_pair hq2 hq3
  have hRep :
      ∀ {B0 : DotForm} [Fact B0.toQuadraticMap.PosDef] {p0 : Poly},
        IsSOSQuartic p0 → IsSOCP B0 p0 (![(1 : Poly), x0, q2, q3] : RankFourVec) →
          residual p0 (![(1 : Poly), x0, q2, q3] : RankFourVec) = 0 := by
    intro B0 _ p0 hp0 hsocp0
    exact residual_eq_zero_of_const_x0_mixedAffineTailHomLine_origDetZero_cases
      (B := B0) (u := ![(1 : Poly), x0, q2, q3]) huRepAdmissible
      (by simp) (by simp [x0]) (by simp) (by simp)
      hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10 hqdet0 hq3_01 hp0 hsocp0
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec
    (![(1 : Poly), x0, q2, q3])
    hRep e heQuad heQuadSymm heQuarticSymm M hMtM hMMt hB hp huRep hsocp

theorem residual_eq_zero_of_socp_of_eq_mix_affineEquiv_const_x0_mixedAffineTailHomLine_origDetZero_cases
    (A A' : Matrix (Fin 2) (Fin 2) ℝ) (b b' : Fin 2 → ℝ)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (hb : ∀ i, b' i + Matrix.mulVec A' b i = 0)
    (hb' : ∀ i, b i + Matrix.mulVec A b' i = 0)
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hMtM : M.transpose * M = 1)
    (hMMt : M * M.transpose = 1)
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hqdet0 :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0)
    (huRep :
      mix M.transpose
        (mapVec (affineEquiv A A' b b' hAA' hA'A hb hb').symm.toAlgHom u) =
          ![(1 : Poly), x0, q2, q3])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec_const_x0_mixedAffineTailHomLine_origDetZero_cases
    (e := affineEquiv A A' b b' hAA' hA'A hb hb')
    (heQuad := fun {_} hpq => isQuadratic_affineEquiv A A' b b' hAA' hA'A hb hb' hpq)
    (heQuadSymm := fun {_} hpq => isQuadratic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (heQuarticSymm := fun {_} hpq => isQuartic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (M := M) hMtM hMMt hB hp
    hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10 hqdet0 hq3_01 huRep hsocp

theorem residual_eq_zero_of_const_x0_pair_coeff_m00_m10_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {q2 q3 : Poly}
    (h0 : u 0 = (1 : Poly))
    (h1 : u 1 = x0)
    (h2 : u 2 = q2)
    (h3 : u 3 = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  by_cases hdet :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 ≠ 0
  · exact residual_eq_zero_of_const_x0_tailedPair_det
      (B := B) (u := u) hu h0 h1 h2 h3 hq2 hq3 hdet hp hsocp
  · have hdet0 :
        MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
          MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0 := by
      by_contra hdet0
      exact hdet hdet0
    by_cases hq3_01 : MvPolynomial.coeff m01 q3 ≠ 0
    · exact residual_eq_zero_of_const_x0_mixedAffineTailHomLine_origDetZero_cases
        (B := B) (u := u) hu
        h0 h1 h2 h3 hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10 hdet0 hq3_01 hp hsocp
    · by_cases hq2_01 : MvPolynomial.coeff m01 q2 ≠ 0
      · let Mswap : Matrix (Fin 4) (Fin 4) ℝ := relationColsMatrix stdRel0 stdRel1 stdRel3 stdRel2
        have hMtM : Mswap.transpose * Mswap = 1 := by
          dsimp [Mswap]
          exact relationColsMatrix_transpose_mul_self_eq_one stdRel0 stdRel1 stdRel3 stdRel2
            (by simp [stdRel0, Fin.sum_univ_four, pow_two])
            (by simp [stdRel1, Fin.sum_univ_four, pow_two])
            (by simp [stdRel3, Fin.sum_univ_four, pow_two])
            (by simp [stdRel2, Fin.sum_univ_four, pow_two])
            (by simp [stdRel0, stdRel1, Fin.sum_univ_four])
            (by simp [stdRel0, stdRel3, Fin.sum_univ_four])
            (by simp [stdRel0, stdRel2, Fin.sum_univ_four])
            (by simp [stdRel1, stdRel3, Fin.sum_univ_four])
            (by simp [stdRel1, stdRel2, Fin.sum_univ_four])
            (by simp [stdRel3, stdRel2, Fin.sum_univ_four])
        have hMMt : Mswap * Mswap.transpose = 1 := by
          exact self_mul_transpose_eq_one_of_transpose_mul_self_eq_one Mswap hMtM
        have huRep : mix Mswap.transpose u = ![(1 : Poly), x0, q3, q2] := by
          rw [mix_relationColsMatrix_transpose]
          simp [stdRel0, stdRel1, stdRel2, stdRel3, Fin.sum_univ_four, h0, h1, h2, h3]
        have hdet0swap :
            MvPolynomial.coeff m11 q3 * MvPolynomial.coeff m02 q2 -
              MvPolynomial.coeff m02 q3 * MvPolynomial.coeff m11 q2 = 0 := by
          linarith
        exact residual_eq_zero_of_socp_of_eq_mix_mapVec_const_x0_mixedAffineTailHomLine_origDetZero_cases
          (e := AlgEquiv.refl)
          (heQuad := fun {_} hq => hq)
          (heQuadSymm := fun {_} hq => hq)
          (heQuarticSymm := fun {_} hq => hq)
          (M := Mswap) hMtM hMMt
          (hB := (Fact.out : B.toQuadraticMap.PosDef)) hp
          (hq2 := hq3) (hq3 := hq2)
          hq3_00 hq3_10 hq2_00 hq2_10 hdet0swap hq2_01 huRep hsocp
      · have hq2_01z : MvPolynomial.coeff m01 q2 = 0 := by
          by_contra hq2_01z
          exact hq2_01 hq2_01z
        have hq3_01z : MvPolynomial.coeff m01 q3 = 0 := by
          by_contra hq3_01z
          exact hq3_01 hq3_01z
        exact residual_eq_zero_of_relations_const_x0_homQuadratics_cases
          (c0 := stdRel0) (c1 := stdRel1) (c2 := stdRel2) (c3 := stdRel3)
          (B := B) (u := u) hu
          (h0 := by simpa [stdRel0, Fin.sum_univ_four] using h0)
          (h1 := by simpa [stdRel1, Fin.sum_univ_four] using h1)
          (h2 := by simpa [stdRel2, Fin.sum_univ_four] using h2)
          (h3 := by simpa [stdRel3, Fin.sum_univ_four] using h3)
          hq2 hq3 hq2_00 hq2_10 hq2_01z hq3_00 hq3_10 hq3_01z
          stdRel23_gram_ne_zero hp hsocp

theorem residual_eq_zero_of_equiv_const_x0_pair_coeff_m00_m10_zero
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {q2 q3 : Poly}
    (h0 : mapVec e.toAlgHom u 0 = (1 : Poly))
    (h1 : mapVec e.toAlgHom u 1 = x0)
    (h2 : mapVec e.toAlgHom u 2 = q2)
    (h3 : mapVec e.toAlgHom u 3 = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_const_x0_pair_coeff_m00_m10_zero
      (B := B0) (u := mapVec e.toAlgHom u) hu0
      h0 h1 h2 h3 hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_socp_of_eq_mix_mapVec_const_x0_pair_coeff_m00_m10_zero
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuarticSymm : ∀ {p : Poly}, IsQuartic p → IsQuartic (e.symm p))
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hMtM : M.transpose * M = 1)
    (hMMt : M * M.transpose = 1)
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (huRep : mix M.transpose (mapVec e.symm.toAlgHom u) = ![(1 : Poly), x0, q2, q3])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have huRepAdmissible : IsAdmissiblePoint (![(1 : Poly), x0, q2, q3] : RankFourVec) := by
    exact admissiblePoint_const_x0_pair hq2 hq3
  have hRep :
      ∀ {B0 : DotForm} [Fact B0.toQuadraticMap.PosDef] {p0 : Poly},
        IsSOSQuartic p0 → IsSOCP B0 p0 (![(1 : Poly), x0, q2, q3] : RankFourVec) →
          residual p0 (![(1 : Poly), x0, q2, q3] : RankFourVec) = 0 := by
    intro B0 _ p0 hp0 hsocp0
    exact residual_eq_zero_of_const_x0_pair_coeff_m00_m10_zero
      (B := B0) (u := ![(1 : Poly), x0, q2, q3]) huRepAdmissible
      (by simp) (by simp [x0]) (by simp) (by simp)
      hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10 hp0 hsocp0
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec
    (![(1 : Poly), x0, q2, q3])
    hRep e heQuad heQuadSymm heQuarticSymm M hMtM hMMt hB hp huRep hsocp

theorem residual_eq_zero_of_socp_of_eq_mix_affineEquiv_const_x0_pair_coeff_m00_m10_zero
    (A A' : Matrix (Fin 2) (Fin 2) ℝ) (b b' : Fin 2 → ℝ)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (hb : ∀ i, b' i + Matrix.mulVec A' b i = 0)
    (hb' : ∀ i, b i + Matrix.mulVec A b' i = 0)
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hMtM : M.transpose * M = 1)
    (hMMt : M * M.transpose = 1)
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (huRep :
      mix M.transpose
        (mapVec (affineEquiv A A' b b' hAA' hA'A hb hb').symm.toAlgHom u) =
          ![(1 : Poly), x0, q2, q3])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec_const_x0_pair_coeff_m00_m10_zero
    (e := affineEquiv A A' b b' hAA' hA'A hb hb')
    (heQuad := fun {_} hpq => isQuadratic_affineEquiv A A' b b' hAA' hA'A hb hb' hpq)
    (heQuadSymm := fun {_} hpq => isQuadratic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (heQuarticSymm := fun {_} hpq => isQuartic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (M := M) hMtM hMMt hB hp
    hq2 hq3 hq2_00 hq2_10 hq3_00 hq3_10 huRep hsocp

theorem residual_eq_zero_of_relations_const_x0_x0x1_x1PlusX0sq_orthonormal
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 * x1)
    {a : ℝ}
    (h3 : ∑ i : Fin 4, c3 i • u i = x1 + a • (x0 ^ 2 : Poly))
    (ha : a ≠ 0)
    (h00 : ∑ i : Fin 4, (c0 i) ^ 2 = 1)
    (h11 : ∑ i : Fin 4, (c1 i) ^ 2 = 1)
    (h22 : ∑ i : Fin 4, (c2 i) ^ 2 = 1)
    (h33 : ∑ i : Fin 4, (c3 i) ^ 2 = 1)
    (h01 : ∑ i : Fin 4, c0 i * c1 i = 0)
    (h02 : ∑ i : Fin 4, c0 i * c2 i = 0)
    (h03 : ∑ i : Fin 4, c0 i * c3 i = 0)
    (h12 : ∑ i : Fin 4, c1 i * c2 i = 0)
    (h13 : ∑ i : Fin 4, c1 i * c3 i = 0)
    (h23 : ∑ i : Fin 4, c2 i * c3 i = 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let M : Matrix (Fin 4) (Fin 4) ℝ := relationColsMatrix c0 c1 c2 c3
  have hMtM : M.transpose * M = 1 := by
    dsimp [M]
    exact relationColsMatrix_transpose_mul_self_eq_one c0 c1 c2 c3
      h00 h11 h22 h33 h01 h02 h03 h12 h13 h23
  have hMMt : M * M.transpose = 1 := by
    exact self_mul_transpose_eq_one_of_transpose_mul_self_eq_one M hMtM
  have huRep :
      mix M.transpose u = mixedAffineTailCrossRep a := by
    rw [mix_relationColsMatrix_transpose]
    simp [h0, h1, h2, h3, mixedAffineTailCrossRep]
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec
    (uRep := mixedAffineTailCrossRep a)
    (hRep := fun {B} [_] {p} hp hsocp => residual_eq_zero_mixedAffineTailCrossRep a ha hp hsocp)
    (e := AlgEquiv.refl)
    (heQuad := fun {_} hq => hq)
    (heQuadSymm := fun {_} hq => hq)
    (heQuarticSymm := fun {_} hq => hq)
    (M := M) hMtM hMMt
    (hB := (Fact.out : B.toQuadraticMap.PosDef))
    hp huRep hsocp

theorem residual_eq_zero_of_equiv_relations_const_x0_x0x1_x1PlusX0sq_orthonormal
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x0)
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = x0 * x1)
    {a : ℝ}
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = x1 + a • (x0 ^ 2 : Poly))
    (ha : a ≠ 0)
    (h00 : ∑ i : Fin 4, (c0 i) ^ 2 = 1)
    (h11 : ∑ i : Fin 4, (c1 i) ^ 2 = 1)
    (h22 : ∑ i : Fin 4, (c2 i) ^ 2 = 1)
    (h33 : ∑ i : Fin 4, (c3 i) ^ 2 = 1)
    (h01 : ∑ i : Fin 4, c0 i * c1 i = 0)
    (h02 : ∑ i : Fin 4, c0 i * c2 i = 0)
    (h03 : ∑ i : Fin 4, c0 i * c3 i = 0)
    (h12 : ∑ i : Fin 4, c1 i * c2 i = 0)
    (h13 : ∑ i : Fin 4, c1 i * c3 i = 0)
    (h23 : ∑ i : Fin 4, c2 i * c3 i = 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e) (heQuad := fun {_} hpq => heQuad hpq) (heQuartic := fun {_} hpq => heQuartic hpq) hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_const_x0_x0x1_x1PlusX0sq_orthonormal
      (B := B0) (u := mapVec e.toAlgHom u)
      h0 h1 h2 h3 ha
      h00 h11 h22 h33 h01 h02 h03 h12 h13 h23 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

end TernaryQuartic
