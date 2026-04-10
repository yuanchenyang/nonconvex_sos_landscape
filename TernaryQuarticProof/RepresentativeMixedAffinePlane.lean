import TernaryQuarticProof.Certificate
import TernaryQuarticProof.AffineSocpTransform
import TernaryQuarticProof.RepresentativeMixedAffine
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

end TernaryQuartic
