import TernaryQuarticProof.QuadraticNormalForm
import TernaryQuarticProof.RepresentativeSurjective

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace TernaryQuartic

open scoped BigOperators

/-- The quartic monomial `x₀⁴`. -/
abbrev m40 : Fin 2 →₀ ℕ := Finsupp.single 0 4

/-- The rank-4 mixed-affine representative with image codimension one. -/
def mixedAffineRank14Rep : RankFourVec := ![(1 : Poly), x0, x0 * x1, x1 ^ 2]

private theorem monomial_fin2_eq (s : Fin 2 →₀ ℕ) (a : ℝ) :
    MvPolynomial.monomial s a = (MvPolynomial.C a * x0 ^ s 0) * x1 ^ s 1 := by
  simp [x0, x1, MvPolynomial.monomial_eq, mul_assoc]

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

/-- The surjective mixed-affine representative. -/
def mixedAffineRank15Rep : RankFourVec := ![(1 : Poly), x0, x0 ^ 2, x1 ^ 2]

/-- Every quartic lies in the image for the rank-15 mixed-affine representative. -/
theorem quartic_in_image_mixedAffineRank15Rep
    {p : Poly} (hp : IsQuartic p) :
    InAdmissibleImage mixedAffineRank15Rep p := by
  classical
  rw [← MvPolynomial.support_sum_monomial_coeff p]
  let P : Finset (Fin 2 →₀ ℕ) → Prop := fun S =>
    (∀ s ∈ S, s ∈ p.support) →
      InAdmissibleImage mixedAffineRank15Rep
        (∑ s ∈ S, MvPolynomial.monomial s (MvPolynomial.coeff s p))
  have hP : P p.support := by
    refine Finset.induction_on p.support ?_ ?_
    · intro hsub
      simpa using inAdmissibleImage_zero mixedAffineRank15Rep
    · intro s ss hsnot ih hsub
      rw [Finset.sum_insert hsnot]
      refine inAdmissibleImage_add mixedAffineRank15Rep ?_ (ih ?_)
      · let e0 := s 0
        let e1 := s 1
        have hsum : s.sum (fun _ e => e) = s 0 + s 1 := by
          rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
        have hsdeg : e0 + e1 ≤ 4 := by
          have hsdeg0 : s.sum (fun _ e => e) ≤ 4 :=
            (MvPolynomial.le_totalDegree (hsub s (by simp))).trans hp
          simpa [e0, e1, hsum] using hsdeg0
        by_cases hsmall : e0 + e1 ≤ 2
        · refine ⟨![(MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ e0) * x1 ^ e1, 0, 0, 0], ?_, ?_⟩
          · intro i
            fin_cases i
            · exact isQuadratic_C_mul_pow_pow (MvPolynomial.coeff s p) e0 e1 hsmall
            · simp [IsQuadratic]
            · simp [IsQuadratic]
            · simp [IsQuadratic]
          · rw [monomial_fin2_eq]
            simp [A, mixedAffineRank15Rep, e0, e1, Fin.sum_univ_four, x0, x1]
        · by_cases hx2 : 2 ≤ e0
          · refine ⟨![0, 0,
                (MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ (e0 - 2)) * x1 ^ e1, 0], ?_, ?_⟩
            · intro i
              fin_cases i
              · simp [IsQuadratic]
              · simp [IsQuadratic]
              · have hs2 : (e0 - 2) + e1 ≤ 2 := by omega
                exact isQuadratic_C_mul_pow_pow (MvPolynomial.coeff s p) (e0 - 2) e1 hs2
              · simp [IsQuadratic]
            · rw [monomial_fin2_eq]
              simp [e0, e1]
              calc
                A mixedAffineRank15Rep
                    ![0, 0, (MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ (e0 - 2)) * x1 ^ e1, 0]
                    = x0 ^ 2 * ((MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ (e0 - 2)) * x1 ^ e1) := by
                        simp [A, mixedAffineRank15Rep, Fin.sum_univ_four, x0, x1]
                _ = (MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ e0) * x1 ^ e1 := by
                      calc
                        x0 ^ 2 * ((MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ (e0 - 2)) * x1 ^ e1)
                            = MvPolynomial.C (MvPolynomial.coeff s p) *
                                (x0 ^ 2 * x0 ^ (e0 - 2)) * x1 ^ e1 := by
                                  ring_nf
                        _ = (MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ e0) * x1 ^ e1 := by
                              rw [← pow_add, Nat.add_sub_of_le hx2]
          · have hy2 : 2 ≤ e1 := by omega
            refine ⟨![0, 0, 0,
                  (MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ e0) * x1 ^ (e1 - 2)], ?_, ?_⟩
            · intro i
              fin_cases i
              · simp [IsQuadratic]
              · simp [IsQuadratic]
              · simp [IsQuadratic]
              · have hs2 : e0 + (e1 - 2) ≤ 2 := by omega
                exact isQuadratic_C_mul_pow_pow (MvPolynomial.coeff s p) e0 (e1 - 2) hs2
            · rw [monomial_fin2_eq]
              simp [e0, e1]
              calc
                A mixedAffineRank15Rep
                    ![0, 0, 0, (MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ e0) * x1 ^ (e1 - 2)]
                    = x1 ^ 2 * ((MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ e0) * x1 ^ (e1 - 2)) := by
                        simp [A, mixedAffineRank15Rep, Fin.sum_univ_four, x0, x1]
                _ = (MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ e0) * x1 ^ e1 := by
                      calc
                        x1 ^ 2 * ((MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ e0) * x1 ^ (e1 - 2))
                            = MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ e0 *
                                (x1 ^ 2 * x1 ^ (e1 - 2)) := by
                                  ring_nf
                        _ = (MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ e0) * x1 ^ e1 := by
                              rw [← pow_add, Nat.add_sub_of_le hy2]
      · intro t ht
        exact hsub t (by simp [ht])
  exact hP (fun s hs => hs)

theorem mixedAffineRank15Rep_admissible : IsAdmissiblePoint mixedAffineRank15Rep := by
  intro i
  fin_cases i
  · simp [mixedAffineRank15Rep, IsQuadratic]
  · simp [mixedAffineRank15Rep, x0, x1, IsQuadratic]
  · simp [mixedAffineRank15Rep, x0, x1, IsQuadratic, MvPolynomial.totalDegree_X_pow]
  · simp [mixedAffineRank15Rep, x0, x1, IsQuadratic, MvPolynomial.totalDegree_X_pow]

theorem residual_eq_zero_mixedAffineRank15Rep
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p mixedAffineRank15Rep) :
    residual p mixedAffineRank15Rep = 0 := by
  exact residual_eq_zero_of_in_admissible_image
    (B := B) mixedAffineRank15Rep_admissible hsocp
    (quartic_in_image_mixedAffineRank15Rep hp.1)

private theorem monomial_image_mixedAffineRank14Rep
    (s : Fin 2 →₀ ℕ) (a : ℝ)
    (hdeg : s.sum (fun _ e => e) ≤ 4)
    (hne : s ≠ m40) :
    InAdmissibleImage mixedAffineRank14Rep (MvPolynomial.monomial s a) := by
  let e0 := s 0
  let e1 := s 1
  have hsum : s.sum (fun _ e => e) = s 0 + s 1 := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
  have hs0 : s 0 + s 1 ≤ 4 := by
    simpa [hsum] using hdeg
  have hs : e0 + e1 ≤ 4 := by
    simpa [e0, e1] using hs0
  by_cases hsmall : e0 + e1 ≤ 2
  · refine ⟨![(MvPolynomial.C a * x0 ^ e0) * x1 ^ e1, 0, 0, 0], ?_, ?_⟩
    · intro i
      fin_cases i
      · exact isQuadratic_C_mul_pow_pow a e0 e1 hsmall
      · simp [IsQuadratic]
      · simp [IsQuadratic]
      · simp [IsQuadratic]
    · rw [monomial_fin2_eq]
      simp [A, mixedAffineRank14Rep, e0, e1, Fin.sum_univ_four, x0, x1]
  · by_cases hy2 : 2 ≤ e1
    · refine ⟨![0, 0, 0, (MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 2)], ?_, ?_⟩
      · intro i
        fin_cases i
        · simp [IsQuadratic]
        · simp [IsQuadratic]
        · simp [IsQuadratic]
        · have hs2 : e0 + (e1 - 2) ≤ 2 := by omega
          exact isQuadratic_C_mul_pow_pow a e0 (e1 - 2) hs2
      · rw [monomial_fin2_eq]
        simp [e0, e1]
        calc
          A mixedAffineRank14Rep ![0, 0, 0, (MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 2)]
              = x1 ^ 2 * ((MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 2)) := by
                  simp [A, mixedAffineRank14Rep, Fin.sum_univ_four, x0, x1]
          _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                calc
                  x1 ^ 2 * ((MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 2))
                      = MvPolynomial.C a * x0 ^ e0 * (x1 ^ 2 * x1 ^ (e1 - 2)) := by
                          ring_nf
                  _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                        rw [← pow_add, Nat.add_sub_of_le hy2]
    · by_cases hxy : 1 ≤ e0 ∧ 1 ≤ e1
      · refine ⟨![0, 0, (MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1), 0], ?_, ?_⟩
        · intro i
          fin_cases i
          · simp [IsQuadratic]
          · simp [IsQuadratic]
          · have hs2 : (e0 - 1) + (e1 - 1) ≤ 2 := by omega
            exact isQuadratic_C_mul_pow_pow a (e0 - 1) (e1 - 1) hs2
          · simp [IsQuadratic]
        · rw [monomial_fin2_eq]
          simp [e0, e1]
          calc
            A mixedAffineRank14Rep ![0, 0, (MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1), 0]
                = (x0 * x1) * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1)) := by
                    simp [A, mixedAffineRank14Rep, Fin.sum_univ_four, x0, x1]
            _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                  rcases hxy with ⟨hx1, hy1⟩
                  have hxpow : x0 * x0 ^ (e0 - 1) = x0 ^ e0 := by
                    simpa [Nat.sub_add_cancel hx1] using (pow_succ' x0 (e0 - 1)).symm
                  have hypow : x1 * x1 ^ (e1 - 1) = x1 ^ e1 := by
                    simpa [Nat.sub_add_cancel hy1] using (pow_succ' x1 (e1 - 1)).symm
                  calc
                    (x0 * x1) * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1))
                        = MvPolynomial.C a * (x0 * x0 ^ (e0 - 1)) * (x1 * x1 ^ (e1 - 1)) := by
                            ring_nf
                    _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                          simp [hxpow, hypow, mul_assoc]
      · have hx1 : 1 ≤ e0 := by omega
        have hy0 : e1 = 0 := by omega
        have hx4ne : e0 ≠ 4 := by
          intro hx4
          apply hne
          ext i
          fin_cases i <;> simp [m40, e0, e1, hx4, hy0]
        have hx3 : e0 = 3 := by omega
        refine ⟨![0, (MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1, 0, 0], ?_, ?_⟩
        · intro i
          fin_cases i
          · simp [IsQuadratic]
          · have hs2 : (e0 - 1) + e1 ≤ 2 := by omega
            exact isQuadratic_C_mul_pow_pow a (e0 - 1) e1 hs2
          · simp [IsQuadratic]
          · simp [IsQuadratic]
        · rw [monomial_fin2_eq]
          simp [e0, e1]
          calc
            A mixedAffineRank14Rep ![0, (MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1, 0, 0]
                = x0 * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1) := by
                    simp [A, mixedAffineRank14Rep, Fin.sum_univ_four, x0, x1]
            _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                  have hxpow : x0 * x0 ^ (e0 - 1) = x0 ^ e0 := by
                    simpa [Nat.sub_add_cancel hx1] using (pow_succ' x0 (e0 - 1)).symm
                  calc
                    x0 * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1)
                        = MvPolynomial.C a * (x0 * x0 ^ (e0 - 1)) * x1 ^ e1 := by
                            ring_nf
                    _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                          simp [hxpow, mul_assoc]

private theorem coord0_le_one_of_mem_quadSupp_erase_m20 {d : Fin 2 →₀ ℕ}
    (hd : d ∈ quadSupp.erase m20) (h1 : d 1 = 0) : d 0 ≤ 1 := by
  simp [quadSupp, m00, m10, m01, m20, m11, m02] at hd
  rcases hd with ⟨hd20, rfl | rfl | rfl | rfl | rfl | rfl⟩
  · simp
  · simp
  · simp at h1
  · contradiction
  · simp at h1
  · simp at h1

private theorem not_sum_m40_of_mem_quadSupp_erase_m20 {d1 d2 : Fin 2 →₀ ℕ}
    (hd1 : d1 ∈ quadSupp.erase m20) (hd2 : d2 ∈ quadSupp.erase m20) :
    d1 + d2 ≠ m40 := by
  intro hsum
  have hcoord1 : d1 1 + d2 1 = 0 := by
    have := congrArg (fun e : Fin 2 →₀ ℕ => e 1) hsum
    simpa [m40] using this
  have hd11 : d1 1 = 0 := by omega
  have hd21 : d2 1 = 0 := by omega
  have h01 : d1 0 ≤ 1 := coord0_le_one_of_mem_quadSupp_erase_m20 hd1 hd11
  have h02 : d2 0 ≤ 1 := coord0_le_one_of_mem_quadSupp_erase_m20 hd2 hd21
  have hcoord0 : d1 0 + d2 0 = 4 := by
    have := congrArg (fun e : Fin 2 →₀ ℕ => e 0) hsum
    simpa [m40] using this
  omega

private theorem coeff_qRest (q : Poly) (d : Fin 2 →₀ ℕ) :
    MvPolynomial.coeff d
      (∑ e ∈ quadSupp.erase m20, MvPolynomial.monomial e (MvPolynomial.coeff e q)) =
      if d ∈ quadSupp.erase m20 then MvPolynomial.coeff d q else 0 := by
  simp [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]

private theorem quadratic_split_m20 (q : Poly) (hq : IsQuadratic q) :
    q =
      (∑ e ∈ quadSupp.erase m20, MvPolynomial.monomial e (MvPolynomial.coeff e q)) +
      MvPolynomial.monomial m20 (MvPolynomial.coeff m20 q) := by
  calc
    q = ∑ d ∈ quadSupp, MvPolynomial.monomial d (MvPolynomial.coeff d q) := quadratic_sum_formula hq
    _ =
      (∑ e ∈ quadSupp.erase m20, MvPolynomial.monomial e (MvPolynomial.coeff e q)) +
      MvPolynomial.monomial m20 (MvPolynomial.coeff m20 q) := by
        symm
        have hm20 : m20 ∈ quadSupp := by simp [quadSupp]
        exact Finset.sum_erase_add (s := quadSupp) (a := m20)
          (f := fun e => MvPolynomial.monomial e (MvPolynomial.coeff e q)) hm20

private theorem coeff_m20_qRest_zero (q : Poly) :
    MvPolynomial.coeff m20
      (∑ e ∈ quadSupp.erase m20, MvPolynomial.monomial e (MvPolynomial.coeff e q)) = 0 := by
  rw [coeff_qRest]
  simp

private theorem coeff_m40_qRest_sq_zero (q : Poly) :
    MvPolynomial.coeff m40
      ((∑ e ∈ quadSupp.erase m20, MvPolynomial.monomial e (MvPolynomial.coeff e q)) ^ 2) = 0 := by
  rw [pow_two, MvPolynomial.coeff_mul]
  refine Finset.sum_eq_zero ?_
  intro x hx
  have hxsum : x.1 + x.2 = m40 := Finset.mem_antidiagonal.mp hx
  by_cases hx1 : x.1 ∈ quadSupp.erase m20
  · by_cases hx2 : x.2 ∈ quadSupp.erase m20
    · exfalso
      exact not_sum_m40_of_mem_quadSupp_erase_m20 hx1 hx2 hxsum
    · simp [coeff_qRest, hx1, hx2]
  · simp [coeff_qRest, hx1]

private theorem coeff_m40_qRest_mul_m20_zero (q : Poly) (c : ℝ) :
    MvPolynomial.coeff m40
      ((∑ e ∈ quadSupp.erase m20, MvPolynomial.monomial e (MvPolynomial.coeff e q)) *
        MvPolynomial.monomial m20 c) = 0 := by
  rw [MvPolynomial.coeff_mul_monomial']
  have hmle : m20 ≤ m40 := by
    intro i
    fin_cases i <;> simp [m20, m40]
  have hsub : m40 - m20 = m20 := by
    ext i
    fin_cases i <;> simp [m20, m40]
  simp [hmle, hsub, coeff_m20_qRest_zero]

private theorem coeff_m40_m20_mul_qRest_zero (q : Poly) (c : ℝ) :
    MvPolynomial.coeff m40
      (MvPolynomial.monomial m20 c *
        (∑ e ∈ quadSupp.erase m20, MvPolynomial.monomial e (MvPolynomial.coeff e q))) = 0 := by
  rw [MvPolynomial.coeff_monomial_mul']
  have hmle : m20 ≤ m40 := by
    intro i
    fin_cases i <;> simp [m20, m40]
  have hsub : m40 - m20 = m20 := by
    ext i
    fin_cases i <;> simp [m20, m40]
  simp [hmle, hsub, coeff_m20_qRest_zero]

private theorem coeff_m40_sq_of_quadratic (q : Poly) (hq : IsQuadratic q) :
    MvPolynomial.coeff m40 (q ^ 2) = (MvPolynomial.coeff m20 q) ^ 2 := by
  let qRest := ∑ e ∈ quadSupp.erase m20, MvPolynomial.monomial e (MvPolynomial.coeff e q)
  let c := MvPolynomial.coeff m20 q
  have hsplit : q = qRest + MvPolynomial.monomial m20 c := by
    dsimp [qRest, c]
    exact quadratic_split_m20 q hq
  have hsum20 : m20 + m20 = m40 := by
    ext i
    fin_cases i <;> simp [m20, m40]
  have hrestsq : MvPolynomial.coeff m40 (qRest * qRest) = 0 := by
    dsimp [qRest]
    simpa [pow_two] using coeff_m40_qRest_sq_zero q
  have hrestmul : MvPolynomial.coeff m40 (qRest * MvPolynomial.monomial m20 c) = 0 := by
    dsimp [qRest]
    exact coeff_m40_qRest_mul_m20_zero q c
  have hmulrest : MvPolynomial.coeff m40 (MvPolynomial.monomial m20 c * qRest) = 0 := by
    dsimp [qRest]
    exact coeff_m40_m20_mul_qRest_zero q c
  have hsq :
      MvPolynomial.coeff m40
        (MvPolynomial.monomial m20 c * MvPolynomial.monomial m20 c) = c * c := by
    rw [← hsum20, MvPolynomial.coeff_monomial_mul]
    simp [MvPolynomial.coeff_monomial]
  calc
    MvPolynomial.coeff m40 (q ^ 2)
        = MvPolynomial.coeff m40
            (qRest * qRest + qRest * MvPolynomial.monomial m20 c +
              MvPolynomial.monomial m20 c * qRest +
              MvPolynomial.monomial m20 c * MvPolynomial.monomial m20 c) := by
                rw [pow_two, hsplit]
                ring_nf
    _ = c ^ 2 := by
          rw [MvPolynomial.coeff_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add]
          rw [hrestsq, hrestmul, hmulrest, hsq]
          ring

theorem coeff_m40_sq_of_quadratic_eq (q : Poly) (hq : IsQuadratic q) :
    MvPolynomial.coeff m40 (q ^ 2) = (MvPolynomial.coeff m20 q) ^ 2 :=
  coeff_m40_sq_of_quadratic q hq

theorem quartic_in_image_mixedAffineRank14Rep_of_coeff_m40_zero
    {p : Poly} (hp : IsQuartic p)
    (h40 : MvPolynomial.coeff m40 p = 0) :
    InAdmissibleImage mixedAffineRank14Rep p := by
  classical
  rw [← MvPolynomial.support_sum_monomial_coeff p]
  let P : Finset (Fin 2 →₀ ℕ) → Prop := fun S =>
    (∀ s ∈ S, s ∈ p.support) →
      InAdmissibleImage mixedAffineRank14Rep
        (∑ s ∈ S, MvPolynomial.monomial s (MvPolynomial.coeff s p))
  have hP : P p.support := by
    refine Finset.induction_on p.support ?_ ?_
    · intro hsub
      simpa using inAdmissibleImage_zero mixedAffineRank14Rep
    · intro s ss hsnot ih hsub
      rw [Finset.sum_insert hsnot]
      refine inAdmissibleImage_add mixedAffineRank14Rep ?_ (ih ?_)
      · have hsdeg : s.sum (fun _ e => e) ≤ 4 :=
          (MvPolynomial.le_totalDegree (hsub s (by simp))).trans hp
        have hscoeff : MvPolynomial.coeff s p ≠ 0 :=
          MvPolynomial.mem_support_iff.mp (hsub s (by simp))
        have hsne : s ≠ m40 := by
          intro hs
          apply hscoeff
          simpa [hs] using h40
        exact monomial_image_mixedAffineRank14Rep s (MvPolynomial.coeff s p) hsdeg hsne
      · intro t ht
        exact hsub t (by simp [ht])
  exact hP (fun s hs => hs)

/-- A fixed kernel generator for the missing `x₀⁴` class in the rank-14
mixed-affine representative. -/
def mixedAffineRank14KerBase : RankFourVec := ![0, 0, -(x0 * x1), x0 ^ 2]

private theorem isQuadratic_x0_mul_x1 : IsQuadratic (x0 * x1 : Poly) := by
  calc
    (x0 * x1).totalDegree ≤ x0.totalDegree + x1.totalDegree := by
      exact MvPolynomial.totalDegree_mul _ _
    _ = 2 := by simp [x0, x1]

theorem mixedAffineRank14Rep_admissible : IsAdmissiblePoint mixedAffineRank14Rep := by
  intro i
  fin_cases i
  · simp [mixedAffineRank14Rep, IsQuadratic]
  · simp [mixedAffineRank14Rep, x0, x1, IsQuadratic]
  · simpa [mixedAffineRank14Rep] using isQuadratic_x0_mul_x1
  · simp [mixedAffineRank14Rep, x0, x1, IsQuadratic, MvPolynomial.totalDegree_X_pow]

theorem mixedAffineRank14KerBase_admissible : IsAdmissibleDirection mixedAffineRank14KerBase := by
  intro i
  fin_cases i
  · simp [mixedAffineRank14KerBase, IsQuadratic]
  · simp [mixedAffineRank14KerBase, IsQuadratic]
  · simpa [mixedAffineRank14KerBase, IsQuadratic] using isQuadratic_x0_mul_x1
  · simp [mixedAffineRank14KerBase, x0, x1, IsQuadratic, MvPolynomial.totalDegree_X_pow]

private theorem A_smul_right_local (u v : RankFourVec) (t : ℝ) :
    A u (t • v) = t • A u v := by
  calc
    A u (t • v) = ∑ i : Fin 4, t • (u i * v i) := by
      unfold A
      refine Finset.sum_congr rfl ?_
      intro i hi
      change u i * (t • v i) = t • (u i * v i)
      exact mul_smul_comm t (u i) (v i)
    _ = t • ∑ i : Fin 4, u i * v i := by
      rw [← Finset.smul_sum]
    _ = t • A u v := by
      simp [A]

private theorem isAdmissibleDirection_smul_local (t : ℝ) {v : RankFourVec}
    (hv : IsAdmissibleDirection v) :
    IsAdmissibleDirection (t • v) := by
  intro i
  exact (MvPolynomial.totalDegree_smul_le t (v i)).trans (hv i)

theorem mixedAffineRank14KerBase_inKer :
    InAdmissibleKer mixedAffineRank14Rep mixedAffineRank14KerBase := by
  refine ⟨mixedAffineRank14KerBase_admissible, ?_⟩
  simp [A, mixedAffineRank14Rep, mixedAffineRank14KerBase, Fin.sum_univ_four, x0, x1]
  ring

theorem mixedAffineRank14Ker_scaled_inKer (t : ℝ) :
    InAdmissibleKer mixedAffineRank14Rep (t • mixedAffineRank14KerBase) := by
  refine ⟨isAdmissibleDirection_smul_local t mixedAffineRank14KerBase_admissible, ?_⟩
  rw [A_smul_right_local, mixedAffineRank14KerBase_inKer.2]
  simp

private theorem isQuadratic_smul_x0_mul_x1 (t : ℝ) :
    IsQuadratic (t • (x0 * x1 : Poly)) := by
  exact (MvPolynomial.totalDegree_smul_le t (x0 * x1 : Poly)).trans isQuadratic_x0_mul_x1

private theorem isQuadratic_smul_x0_sq (t : ℝ) :
    IsQuadratic (t • (x0 ^ 2 : Poly)) := by
  exact (MvPolynomial.totalDegree_smul_le t (x0 ^ 2 : Poly)).trans <|
    by simp [x0, MvPolynomial.totalDegree_X_pow]

private theorem coeff_m20_smul_x0_mul_x1 (t : ℝ) :
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

private theorem coeff_m20_smul_x0_sq (t : ℝ) :
    MvPolynomial.coeff m20 (t • (x0 ^ 2 : Poly)) = t := by
  rw [MvPolynomial.coeff_smul]
  have hx : MvPolynomial.coeff m20 (x0 ^ 2 : Poly) = 1 := by
    simp [x0, m20, MvPolynomial.coeff_X_pow]
  simp [hx]

theorem coeff_m40_sigma_mixedAffineRank14KerScaled (t : ℝ) :
    MvPolynomial.coeff m40 (sigma (t • mixedAffineRank14KerBase)) = t ^ 2 := by
  have hxy :
      MvPolynomial.coeff m40 ((t • (x0 * x1 : Poly)) ^ 2) = 0 := by
    rw [coeff_m40_sq_of_quadratic _ (isQuadratic_smul_x0_mul_x1 t)]
    rw [coeff_m20_smul_x0_mul_x1]
    ring
  have hx0 :
      MvPolynomial.coeff m40 ((t • (x0 ^ 2 : Poly)) ^ 2) = t ^ 2 := by
    rw [coeff_m40_sq_of_quadratic _ (isQuadratic_smul_x0_sq t)]
    rw [coeff_m20_smul_x0_sq]
  rw [sigma, Fin.sum_univ_four]
  simp [mixedAffineRank14KerBase, hxy, hx0]

private theorem isQuartic_sigma_of_admissible_local {u : RankFourVec}
    (hu : IsAdmissibleDirection u) :
    IsQuartic (sigma u) := by
  unfold sigma IsQuartic
  refine MvPolynomial.totalDegree_finsetSum_le ?_
  intro i hi
  have hpow : ((u i) ^ 2).totalDegree ≤ 2 * (u i).totalDegree := by
    simpa using MvPolynomial.totalDegree_pow (u i) 2
  have hi2 : (u i).totalDegree ≤ 2 := hu i
  omega

theorem residual_eq_zero_mixedAffineRank14Rep
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p mixedAffineRank14Rep) :
    residual p mixedAffineRank14Rep = 0 := by
  rcases hp with ⟨hpquartic, k, qs, hqdeg, hpq⟩
  let s : ℝ := ∑ i : Fin k, (MvPolynomial.coeff m20 (qs i)) ^ 2
  let t : ℝ := Real.sqrt s
  let w : RankFourVec := t • mixedAffineRank14KerBase
  have hsnonneg : 0 ≤ s := by
    dsimp [s]
    positivity
  have hp40 : MvPolynomial.coeff m40 p = s := by
    rw [hpq, MvPolynomial.coeff_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact coeff_m40_sq_of_quadratic (qs i) (hqdeg i)
  have hwker : InAdmissibleKer mixedAffineRank14Rep w := mixedAffineRank14Ker_scaled_inKer t
  have hw40 : MvPolynomial.coeff m40 (sigma w) = s := by
    change MvPolynomial.coeff m40 (sigma (t • mixedAffineRank14KerBase)) = s
    calc
      MvPolynomial.coeff m40 (sigma (t • mixedAffineRank14KerBase)) = t ^ 2 := by
        exact coeff_m40_sigma_mixedAffineRank14KerScaled t
      _ = s := by
        dsimp [t]
        rw [Real.sq_sqrt hsnonneg]
  have hquartic_sub : IsQuartic (p - sigma w) := by
    calc
      (p - sigma w).totalDegree ≤ max p.totalDegree (sigma w).totalDegree := by
        exact MvPolynomial.totalDegree_sub _ _
      _ ≤ 4 := by
        exact max_le hpquartic (isQuartic_sigma_of_admissible_local hwker.1)
  have h40_sub : MvPolynomial.coeff m40 (p - sigma w) = 0 := by
    rw [MvPolynomial.coeff_sub, hp40, hw40]
    ring
  have himg : InAdmissibleImage mixedAffineRank14Rep (p - sigma w) :=
    quartic_in_image_mixedAffineRank14Rep_of_coeff_m40_zero hquartic_sub h40_sub
  refine admissible_image_plus_cone_residual_eq_zero (B := B)
    (u := mixedAffineRank14Rep) (uImg := mixedAffineRank14Rep)
    mixedAffineRank14Rep_admissible hsocp
    (imageOrthogonalResidual_self (B := B) hsocp.1) ?_
  refine ⟨p - sigma w, {w}, himg, ?_, ?_⟩
  · intro w' hw'
    have hw' : w' = w := by simpa using hw'
    subst hw'
    exact hwker
  · simp [w, sub_eq_add_neg]

/-- The quartic monomials `x₁³` and `x₁⁴` in the `(x₀,x₁)` coordinates. -/
abbrev m03 : Fin 2 →₀ ℕ := Finsupp.single 1 3

abbrev m04 : Fin 2 →₀ ℕ := Finsupp.single 1 4

/-- The rank-4 mixed-affine representative with image codimension two. -/
def mixedAffineRank13Rep : RankFourVec := ![(1 : Poly), x0, x0 ^ 2, x0 * x1]

private theorem monomial_image_mixedAffineRank13Rep
    (s : Fin 2 →₀ ℕ) (a : ℝ)
    (hdeg : s.sum (fun _ e => e) ≤ 4)
    (hne3 : s ≠ m03) (hne4 : s ≠ m04) :
    InAdmissibleImage mixedAffineRank13Rep (MvPolynomial.monomial s a) := by
  let e0 := s 0
  let e1 := s 1
  have hsum : s.sum (fun _ e => e) = s 0 + s 1 := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
  have hs0 : s 0 + s 1 ≤ 4 := by
    simpa [hsum] using hdeg
  have hs : e0 + e1 ≤ 4 := by
    simpa [e0, e1] using hs0
  by_cases hsmall : e0 + e1 ≤ 2
  · refine ⟨![(MvPolynomial.C a * x0 ^ e0) * x1 ^ e1, 0, 0, 0], ?_, ?_⟩
    · intro i
      fin_cases i
      · exact isQuadratic_C_mul_pow_pow a e0 e1 hsmall
      · simp [IsQuadratic]
      · simp [IsQuadratic]
      · simp [IsQuadratic]
    · rw [monomial_fin2_eq]
      simp [A, mixedAffineRank13Rep, e0, e1, Fin.sum_univ_four, x0, x1]
  · by_cases hxy : 1 ≤ e0 ∧ 1 ≤ e1
    · refine ⟨![0, 0, 0, (MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1)], ?_, ?_⟩
      · intro i
        fin_cases i
        · simp [IsQuadratic]
        · simp [IsQuadratic]
        · simp [IsQuadratic]
        · have hs2 : (e0 - 1) + (e1 - 1) ≤ 2 := by omega
          exact isQuadratic_C_mul_pow_pow a (e0 - 1) (e1 - 1) hs2
      · rw [monomial_fin2_eq]
        simp [e0, e1]
        calc
          A mixedAffineRank13Rep ![0, 0, 0, (MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1)]
              = (x0 * x1) * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1)) := by
                  simp [A, mixedAffineRank13Rep, Fin.sum_univ_four, x0, x1]
          _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                rcases hxy with ⟨hx1, hy1⟩
                have hxpow : x0 * x0 ^ (e0 - 1) = x0 ^ e0 := by
                  simpa [Nat.sub_add_cancel hx1] using (pow_succ' x0 (e0 - 1)).symm
                have hypow : x1 * x1 ^ (e1 - 1) = x1 ^ e1 := by
                  simpa [Nat.sub_add_cancel hy1] using (pow_succ' x1 (e1 - 1)).symm
                calc
                  (x0 * x1) * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1))
                      = MvPolynomial.C a * (x0 * x0 ^ (e0 - 1)) * (x1 * x1 ^ (e1 - 1)) := by
                          ring_nf
                  _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                        simp [hxpow, hypow, mul_assoc]
    · by_cases hx2 : 2 ≤ e0
      · refine ⟨![0, 0, (MvPolynomial.C a * x0 ^ (e0 - 2)) * x1 ^ e1, 0], ?_, ?_⟩
        · intro i
          fin_cases i
          · simp [IsQuadratic]
          · simp [IsQuadratic]
          · have hs2 : (e0 - 2) + e1 ≤ 2 := by omega
            exact isQuadratic_C_mul_pow_pow a (e0 - 2) e1 hs2
          · simp [IsQuadratic]
        · rw [monomial_fin2_eq]
          simp [e0, e1]
          calc
            A mixedAffineRank13Rep ![0, 0, (MvPolynomial.C a * x0 ^ (e0 - 2)) * x1 ^ e1, 0]
                = x0 ^ 2 * ((MvPolynomial.C a * x0 ^ (e0 - 2)) * x1 ^ e1) := by
                    simp [A, mixedAffineRank13Rep, Fin.sum_univ_four, x0, x1]
            _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                  calc
                    x0 ^ 2 * ((MvPolynomial.C a * x0 ^ (e0 - 2)) * x1 ^ e1)
                        = MvPolynomial.C a * (x0 ^ 2 * x0 ^ (e0 - 2)) * x1 ^ e1 := by
                            ring_nf
                    _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                          rw [← pow_add, Nat.add_sub_of_le hx2]
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

theorem quartic_in_image_mixedAffineRank13Rep_of_coeff_m03_m04_zero
    {p : Poly} (hp : IsQuartic p)
    (h03 : MvPolynomial.coeff m03 p = 0)
    (h04 : MvPolynomial.coeff m04 p = 0) :
    InAdmissibleImage mixedAffineRank13Rep p := by
  classical
  rw [← MvPolynomial.support_sum_monomial_coeff p]
  let P : Finset (Fin 2 →₀ ℕ) → Prop := fun S =>
    (∀ s ∈ S, s ∈ p.support) →
      InAdmissibleImage mixedAffineRank13Rep
        (∑ s ∈ S, MvPolynomial.monomial s (MvPolynomial.coeff s p))
  have hP : P p.support := by
    refine Finset.induction_on p.support ?_ ?_
    · intro hsub
      simpa using inAdmissibleImage_zero mixedAffineRank13Rep
    · intro s ss hsnot ih hsub
      rw [Finset.sum_insert hsnot]
      refine inAdmissibleImage_add mixedAffineRank13Rep ?_ (ih ?_)
      · have hsdeg : s.sum (fun _ e => e) ≤ 4 :=
          (MvPolynomial.le_totalDegree (hsub s (by simp))).trans hp
        have hscoeff : MvPolynomial.coeff s p ≠ 0 :=
          MvPolynomial.mem_support_iff.mp (hsub s (by simp))
        have hsne3 : s ≠ m03 := by
          intro hs
          apply hscoeff
          simpa [hs] using h03
        have hsne4 : s ≠ m04 := by
          intro hs
          apply hscoeff
          simpa [hs] using h04
        exact monomial_image_mixedAffineRank13Rep s (MvPolynomial.coeff s p) hsdeg hsne3 hsne4
      · intro t ht
        exact hsub t (by simp [ht])
  exact hP (fun s hs => hs)

private abbrev quadSuppNo_m01_m02 : Finset (Fin 2 →₀ ℕ) := (quadSupp.erase m01).erase m02

private theorem coord1_le_one_of_mem_quadSupp_erase_m01_m02 {d : Fin 2 →₀ ℕ}
    (hd : d ∈ quadSuppNo_m01_m02) : d 1 ≤ 1 := by
  have hd0 : d ∈ quadSupp.erase m01 := Finset.mem_of_mem_erase hd
  have hdQ : d ∈ quadSupp := Finset.mem_of_mem_erase hd0
  have hne02 : d ≠ m02 := (Finset.mem_erase.mp hd).1
  have hne01 : d ≠ m01 := (Finset.mem_erase.mp hd0).1
  simp [quadSupp] at hdQ
  rcases hdQ with rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · simp
  · exfalso
    exact hne01 rfl
  · simp
  · simp
  · exfalso
    exact hne02 rfl

private theorem not_sum_m03_of_mem_quadSupp_erase_m01_m02 {d1 d2 : Fin 2 →₀ ℕ}
    (hd1 : d1 ∈ quadSuppNo_m01_m02)
    (hd2 : d2 ∈ quadSuppNo_m01_m02) :
    d1 + d2 ≠ m03 := by
  intro hsum
  have hcoord1 : d1 1 + d2 1 = 3 := by
    have := congrArg (fun e : Fin 2 →₀ ℕ => e 1) hsum
    simpa [m03] using this
  have h11 : d1 1 ≤ 1 := coord1_le_one_of_mem_quadSupp_erase_m01_m02 hd1
  have h21 : d2 1 ≤ 1 := coord1_le_one_of_mem_quadSupp_erase_m01_m02 hd2
  omega

private theorem not_sum_m04_of_mem_quadSupp_erase_m01_m02 {d1 d2 : Fin 2 →₀ ℕ}
    (hd1 : d1 ∈ quadSuppNo_m01_m02)
    (hd2 : d2 ∈ quadSuppNo_m01_m02) :
    d1 + d2 ≠ m04 := by
  intro hsum
  have hcoord1 : d1 1 + d2 1 = 4 := by
    have := congrArg (fun e : Fin 2 →₀ ℕ => e 1) hsum
    simpa [m04] using this
  have h11 : d1 1 ≤ 1 := coord1_le_one_of_mem_quadSupp_erase_m01_m02 hd1
  have h21 : d2 1 ≤ 1 := coord1_le_one_of_mem_quadSupp_erase_m01_m02 hd2
  omega

private theorem coeff_qRest_m01_m02 (q : Poly) (d : Fin 2 →₀ ℕ) :
    MvPolynomial.coeff d
      (∑ e ∈ quadSuppNo_m01_m02, MvPolynomial.monomial e (MvPolynomial.coeff e q)) =
      if d ∈ quadSuppNo_m01_m02 then MvPolynomial.coeff d q else 0 := by
  simp [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]

private theorem quadratic_split_m01_m02 (q : Poly) (hq : IsQuadratic q) :
    q =
      (∑ e ∈ quadSuppNo_m01_m02, MvPolynomial.monomial e (MvPolynomial.coeff e q)) +
      MvPolynomial.monomial m01 (MvPolynomial.coeff m01 q) +
      MvPolynomial.monomial m02 (MvPolynomial.coeff m02 q) := by
  let f : (Fin 2 →₀ ℕ) → Poly := fun e => MvPolynomial.monomial e (MvPolynomial.coeff e q)
  calc
    q = ∑ d ∈ quadSupp, f d := quadratic_sum_formula hq
    _ = (∑ e ∈ quadSupp.erase m01, f e) + f m01 := by
          symm
          exact Finset.sum_erase_add (s := quadSupp) (a := m01) (f := f)
            (by simp [quadSupp])
    _ = ((∑ e ∈ quadSuppNo_m01_m02, f e) + f m02) + f m01 := by
          have hm02 : m02 ∈ quadSupp.erase m01 := by
            refine Finset.mem_erase.mpr ?_
            constructor
            · intro h
              have := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h
              simp [m01, m02] at this
            · simp [quadSupp]
          have hsum02 : ∑ e ∈ quadSupp.erase m01, f e =
              (∑ e ∈ quadSuppNo_m01_m02, f e) + f m02 := by
            symm
            exact Finset.sum_erase_add (s := quadSupp.erase m01) (a := m02) (f := f) hm02
          rw [hsum02]
    _ =
      (∑ e ∈ quadSuppNo_m01_m02, f e) + f m01 + f m02 := by
        ring
    _ =
      (∑ e ∈ quadSuppNo_m01_m02, MvPolynomial.monomial e (MvPolynomial.coeff e q)) +
      MvPolynomial.monomial m01 (MvPolynomial.coeff m01 q) +
      MvPolynomial.monomial m02 (MvPolynomial.coeff m02 q) := by
        simp [f]

private theorem coeff_m01_qRest_zero (q : Poly) :
    MvPolynomial.coeff m01
      (∑ e ∈ quadSuppNo_m01_m02, MvPolynomial.monomial e (MvPolynomial.coeff e q)) = 0 := by
  rw [coeff_qRest_m01_m02]
  simp

private theorem coeff_m02_qRest_zero (q : Poly) :
    MvPolynomial.coeff m02
      (∑ e ∈ quadSuppNo_m01_m02, MvPolynomial.monomial e (MvPolynomial.coeff e q)) = 0 := by
  rw [coeff_qRest_m01_m02]
  simp

private theorem coeff_m03_qRest_zero (q : Poly) :
    MvPolynomial.coeff m03
      (∑ e ∈ quadSuppNo_m01_m02, MvPolynomial.monomial e (MvPolynomial.coeff e q)) = 0 := by
  rw [coeff_qRest_m01_m02]
  have hm03 : m03 ∉ quadSuppNo_m01_m02 := by
    intro h
    have : m03 ∈ quadSupp := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h)
    simp [quadSupp, m03] at this
    rcases this with h | h | h | h | h
    · have := congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
      simp [m10] at this
    · have := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h
      simp [m01] at this
    · have := congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
      simp [m20] at this
    · have := congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
      simp [m11] at this
    · have := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h
      simp [m02] at this
  simp [hm03]

private theorem coeff_m04_qRest_zero (q : Poly) :
    MvPolynomial.coeff m04
      (∑ e ∈ quadSuppNo_m01_m02, MvPolynomial.monomial e (MvPolynomial.coeff e q)) = 0 := by
  rw [coeff_qRest_m01_m02]
  have hm04 : m04 ∉ quadSuppNo_m01_m02 := by
    intro h
    have : m04 ∈ quadSupp := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h)
    simp [quadSupp, m04] at this
    rcases this with h | h | h | h | h
    · have := congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
      simp [m10] at this
    · have := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h
      simp [m01] at this
    · have := congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
      simp [m20] at this
    · have := congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
      simp [m11] at this
    · have := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h
      simp [m02] at this
  simp [hm04]

private theorem coeff_m03_qRest_sq_zero (q : Poly) :
    MvPolynomial.coeff m03
      ((∑ e ∈ quadSuppNo_m01_m02, MvPolynomial.monomial e (MvPolynomial.coeff e q)) ^ 2) = 0 := by
  rw [pow_two, MvPolynomial.coeff_mul]
  refine Finset.sum_eq_zero ?_
  intro x hx
  have hxsum : x.1 + x.2 = m03 := Finset.mem_antidiagonal.mp hx
  by_cases hx1 : x.1 ∈ quadSuppNo_m01_m02
  · by_cases hx2 : x.2 ∈ quadSuppNo_m01_m02
    · exfalso
      exact not_sum_m03_of_mem_quadSupp_erase_m01_m02 hx1 hx2 hxsum
    · simp [coeff_qRest_m01_m02, hx1, hx2]
  · simp [coeff_qRest_m01_m02, hx1]

private theorem coeff_m04_qRest_sq_zero (q : Poly) :
    MvPolynomial.coeff m04
      ((∑ e ∈ quadSuppNo_m01_m02, MvPolynomial.monomial e (MvPolynomial.coeff e q)) ^ 2) = 0 := by
  rw [pow_two, MvPolynomial.coeff_mul]
  refine Finset.sum_eq_zero ?_
  intro x hx
  have hxsum : x.1 + x.2 = m04 := Finset.mem_antidiagonal.mp hx
  by_cases hx1 : x.1 ∈ quadSuppNo_m01_m02
  · by_cases hx2 : x.2 ∈ quadSuppNo_m01_m02
    · exfalso
      exact not_sum_m04_of_mem_quadSupp_erase_m01_m02 hx1 hx2 hxsum
    · simp [coeff_qRest_m01_m02, hx1, hx2]
  · simp [coeff_qRest_m01_m02, hx1]

private theorem coeff_m03_qRest_mul_m01_zero (q : Poly) (b : ℝ) :
    MvPolynomial.coeff m03
      ((∑ e ∈ quadSuppNo_m01_m02, MvPolynomial.monomial e (MvPolynomial.coeff e q)) *
        MvPolynomial.monomial m01 b) = 0 := by
  rw [MvPolynomial.coeff_mul_monomial']
  have hmle : m01 ≤ m03 := by
    intro i
    fin_cases i <;> simp [m01, m03]
  have hsub : m03 - m01 = m02 := by
    ext i
    fin_cases i <;> simp [m01, m02, m03]
  rw [if_pos hmle, hsub, coeff_m02_qRest_zero]
  simp

private theorem coeff_m03_qRest_mul_m02_zero (q : Poly) (c : ℝ) :
    MvPolynomial.coeff m03
      ((∑ e ∈ quadSuppNo_m01_m02, MvPolynomial.monomial e (MvPolynomial.coeff e q)) *
        MvPolynomial.monomial m02 c) = 0 := by
  rw [MvPolynomial.coeff_mul_monomial']
  have hmle : m02 ≤ m03 := by
    intro i
    fin_cases i <;> simp [m02, m03]
  have hsub : m03 - m02 = m01 := by
    ext i
    fin_cases i <;> simp [m01, m02, m03]
  rw [if_pos hmle, hsub, coeff_m01_qRest_zero]
  simp

private theorem coeff_m03_m01_mul_qRest_zero (q : Poly) (b : ℝ) :
    MvPolynomial.coeff m03
      (MvPolynomial.monomial m01 b *
        (∑ e ∈ quadSuppNo_m01_m02, MvPolynomial.monomial e (MvPolynomial.coeff e q))) = 0 := by
  rw [MvPolynomial.coeff_monomial_mul']
  have hmle : m01 ≤ m03 := by
    intro i
    fin_cases i <;> simp [m01, m03]
  have hsub : m03 - m01 = m02 := by
    ext i
    fin_cases i <;> simp [m01, m02, m03]
  rw [if_pos hmle, hsub, coeff_m02_qRest_zero]
  simp

private theorem coeff_m03_m02_mul_qRest_zero (q : Poly) (c : ℝ) :
    MvPolynomial.coeff m03
      (MvPolynomial.monomial m02 c *
        (∑ e ∈ quadSuppNo_m01_m02, MvPolynomial.monomial e (MvPolynomial.coeff e q))) = 0 := by
  rw [MvPolynomial.coeff_monomial_mul']
  have hmle : m02 ≤ m03 := by
    intro i
    fin_cases i <;> simp [m02, m03]
  have hsub : m03 - m02 = m01 := by
    ext i
    fin_cases i <;> simp [m01, m02, m03]
  rw [if_pos hmle, hsub, coeff_m01_qRest_zero]
  simp

private theorem coeff_m04_qRest_mul_m01_zero (q : Poly) (b : ℝ) :
    MvPolynomial.coeff m04
      ((∑ e ∈ quadSuppNo_m01_m02, MvPolynomial.monomial e (MvPolynomial.coeff e q)) *
        MvPolynomial.monomial m01 b) = 0 := by
  rw [MvPolynomial.coeff_mul_monomial']
  have hmle : m01 ≤ m04 := by
    intro i
    fin_cases i <;> simp [m01, m04]
  have hsub : m04 - m01 = m03 := by
    ext i
    fin_cases i <;> simp [m01, m03, m04]
  rw [if_pos hmle, hsub, coeff_m03_qRest_zero]
  simp

private theorem coeff_m04_qRest_mul_m02_zero (q : Poly) (c : ℝ) :
    MvPolynomial.coeff m04
      ((∑ e ∈ quadSuppNo_m01_m02, MvPolynomial.monomial e (MvPolynomial.coeff e q)) *
        MvPolynomial.monomial m02 c) = 0 := by
  rw [MvPolynomial.coeff_mul_monomial']
  have hmle : m02 ≤ m04 := by
    intro i
    fin_cases i <;> simp [m02, m04]
  have hsub : m04 - m02 = m02 := by
    ext i
    fin_cases i <;> simp [m02, m04]
  rw [if_pos hmle, hsub, coeff_m02_qRest_zero]
  simp

private theorem coeff_m04_m01_mul_qRest_zero (q : Poly) (b : ℝ) :
    MvPolynomial.coeff m04
      (MvPolynomial.monomial m01 b *
        (∑ e ∈ quadSuppNo_m01_m02, MvPolynomial.monomial e (MvPolynomial.coeff e q))) = 0 := by
  rw [MvPolynomial.coeff_monomial_mul']
  have hmle : m01 ≤ m04 := by
    intro i
    fin_cases i <;> simp [m01, m04]
  have hsub : m04 - m01 = m03 := by
    ext i
    fin_cases i <;> simp [m01, m03, m04]
  rw [if_pos hmle, hsub, coeff_m03_qRest_zero]
  simp

private theorem coeff_m04_m02_mul_qRest_zero (q : Poly) (c : ℝ) :
    MvPolynomial.coeff m04
      (MvPolynomial.monomial m02 c *
        (∑ e ∈ quadSuppNo_m01_m02, MvPolynomial.monomial e (MvPolynomial.coeff e q))) = 0 := by
  rw [MvPolynomial.coeff_monomial_mul']
  have hmle : m02 ≤ m04 := by
    intro i
    fin_cases i <;> simp [m02, m04]
  have hsub : m04 - m02 = m02 := by
    ext i
    fin_cases i <;> simp [m02, m04]
  rw [if_pos hmle, hsub, coeff_m02_qRest_zero]
  simp

private theorem coeff_m03_sq_of_quadratic (q : Poly) (hq : IsQuadratic q) :
    MvPolynomial.coeff m03 (q ^ 2) =
      2 * MvPolynomial.coeff m01 q * MvPolynomial.coeff m02 q := by
  let qRest := ∑ e ∈ quadSuppNo_m01_m02, MvPolynomial.monomial e (MvPolynomial.coeff e q)
  let b := MvPolynomial.coeff m01 q
  let c := MvPolynomial.coeff m02 q
  have hsplit : q = qRest + MvPolynomial.monomial m01 b + MvPolynomial.monomial m02 c := by
    dsimp [qRest, b, c]
    exact quadratic_split_m01_m02 q hq
  have h12 : m01 + m02 = m03 := by
    ext i
    fin_cases i <;> simp [m01, m02, m03]
  have h11 :
      MvPolynomial.coeff m03 (MvPolynomial.monomial m01 b * MvPolynomial.monomial m01 b) = 0 := by
    rw [MvPolynomial.coeff_monomial_mul']
    have hmle : m01 ≤ m03 := by
      intro i
      fin_cases i <;> simp [m01, m03]
    have hsub : m03 - m01 = m02 := by
      ext i
      fin_cases i <;> simp [m01, m02, m03]
    rw [if_pos hmle, hsub]
    have hne : m01 ≠ m02 := by
      intro h
      have := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h
      simp [m01, m02] at this
    simp [hne]
  have h12c :
      MvPolynomial.coeff m03 (MvPolynomial.monomial m01 b * MvPolynomial.monomial m02 c) = b * c := by
    rw [MvPolynomial.coeff_monomial_mul']
    have hmle : m01 ≤ m03 := by
      intro i
      fin_cases i <;> simp [m01, m03]
    have hsub : m03 - m01 = m02 := by
      ext i
      fin_cases i <;> simp [m01, m02, m03]
    rw [if_pos hmle, hsub]
    simp
  have h21c :
      MvPolynomial.coeff m03 (MvPolynomial.monomial m02 c * MvPolynomial.monomial m01 b) = c * b := by
    rw [MvPolynomial.coeff_monomial_mul']
    have hmle : m02 ≤ m03 := by
      intro i
      fin_cases i <;> simp [m02, m03]
    have hsub : m03 - m02 = m01 := by
      ext i
      fin_cases i <;> simp [m01, m02, m03]
    rw [if_pos hmle, hsub]
    simp
  have h22 :
      MvPolynomial.coeff m03 (MvPolynomial.monomial m02 c * MvPolynomial.monomial m02 c) = 0 := by
    rw [MvPolynomial.coeff_monomial_mul']
    have hmle : m02 ≤ m03 := by
      intro i
      fin_cases i <;> simp [m02, m03]
    have hsub : m03 - m02 = m01 := by
      ext i
      fin_cases i <;> simp [m01, m02, m03]
    rw [if_pos hmle, hsub]
    have hne : m02 ≠ m01 := by
      intro h
      have := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h
      simp [m01, m02] at this
    simp [hne]
  have hrestsq : MvPolynomial.coeff m03 (qRest * qRest) = 0 := by
    dsimp [qRest]
    simpa [pow_two] using coeff_m03_qRest_sq_zero q
  have hrest1 : MvPolynomial.coeff m03 (qRest * MvPolynomial.monomial m01 b) = 0 := by
    dsimp [qRest]
    exact coeff_m03_qRest_mul_m01_zero q b
  have hrest2 : MvPolynomial.coeff m03 (qRest * MvPolynomial.monomial m02 c) = 0 := by
    dsimp [qRest]
    exact coeff_m03_qRest_mul_m02_zero q c
  have h1rest : MvPolynomial.coeff m03 (MvPolynomial.monomial m01 b * qRest) = 0 := by
    dsimp [qRest]
    exact coeff_m03_m01_mul_qRest_zero q b
  have h2rest : MvPolynomial.coeff m03 (MvPolynomial.monomial m02 c * qRest) = 0 := by
    dsimp [qRest]
    exact coeff_m03_m02_mul_qRest_zero q c
  calc
    MvPolynomial.coeff m03 (q ^ 2)
        = MvPolynomial.coeff m03
            (qRest * qRest + qRest * MvPolynomial.monomial m01 b +
              qRest * MvPolynomial.monomial m02 c +
              MvPolynomial.monomial m01 b * qRest +
              MvPolynomial.monomial m01 b * MvPolynomial.monomial m01 b +
              MvPolynomial.monomial m01 b * MvPolynomial.monomial m02 c +
              MvPolynomial.monomial m02 c * qRest +
              MvPolynomial.monomial m02 c * MvPolynomial.monomial m01 b +
              MvPolynomial.monomial m02 c * MvPolynomial.monomial m02 c) := by
                rw [pow_two, hsplit]
                ring_nf
    _ = 2 * b * c := by
          repeat rw [MvPolynomial.coeff_add]
          rw [hrestsq, hrest1, hrest2, h1rest, h11, h12c, h2rest, h21c, h22]
          ring

private theorem coeff_m04_sq_of_quadratic (q : Poly) (hq : IsQuadratic q) :
    MvPolynomial.coeff m04 (q ^ 2) = (MvPolynomial.coeff m02 q) ^ 2 := by
  let qRest := ∑ e ∈ quadSuppNo_m01_m02, MvPolynomial.monomial e (MvPolynomial.coeff e q)
  let b := MvPolynomial.coeff m01 q
  let c := MvPolynomial.coeff m02 q
  have hsplit : q = qRest + MvPolynomial.monomial m01 b + MvPolynomial.monomial m02 c := by
    dsimp [qRest, b, c]
    exact quadratic_split_m01_m02 q hq
  have h22 : m02 + m02 = m04 := by
    ext i
    fin_cases i <;> simp [m02, m04]
  have h11 :
      MvPolynomial.coeff m04 (MvPolynomial.monomial m01 b * MvPolynomial.monomial m01 b) = 0 := by
    rw [MvPolynomial.coeff_monomial_mul']
    have hmle : m01 ≤ m04 := by
      intro i
      fin_cases i <;> simp [m01, m04]
    have hsub : m04 - m01 = m03 := by
      ext i
      fin_cases i <;> simp [m01, m03, m04]
    rw [if_pos hmle, hsub]
    have hne : m01 ≠ m03 := by
      intro h
      have := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h
      simp [m01, m03] at this
    simp [hne]
  have h12 :
      MvPolynomial.coeff m04 (MvPolynomial.monomial m01 b * MvPolynomial.monomial m02 c) = 0 := by
    rw [MvPolynomial.coeff_monomial_mul']
    have hmle : m01 ≤ m04 := by
      intro i
      fin_cases i <;> simp [m01, m04]
    have hsub : m04 - m01 = m03 := by
      ext i
      fin_cases i <;> simp [m01, m03, m04]
    rw [if_pos hmle, hsub]
    have hne : m02 ≠ m03 := by
      intro h
      have := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h
      simp [m02, m03] at this
    simp [hne]
  have h21 :
      MvPolynomial.coeff m04 (MvPolynomial.monomial m02 c * MvPolynomial.monomial m01 b) = 0 := by
    rw [MvPolynomial.coeff_monomial_mul']
    have hmle : m02 ≤ m04 := by
      intro i
      fin_cases i <;> simp [m02, m04]
    have hsub : m04 - m02 = m02 := by
      ext i
      fin_cases i <;> simp [m02, m04]
    rw [if_pos hmle, hsub]
    have hne : m01 ≠ m02 := by
      intro h
      have := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h
      simp [m01, m02] at this
    simp [hne]
  have h22c :
      MvPolynomial.coeff m04 (MvPolynomial.monomial m02 c * MvPolynomial.monomial m02 c) = c * c := by
    rw [MvPolynomial.coeff_monomial_mul']
    have hmle : m02 ≤ m04 := by
      intro i
      fin_cases i <;> simp [m02, m04]
    have hsub : m04 - m02 = m02 := by
      ext i
      fin_cases i <;> simp [m02, m04]
    rw [if_pos hmle, hsub]
    simp
  have hrestsq : MvPolynomial.coeff m04 (qRest * qRest) = 0 := by
    dsimp [qRest]
    simpa [pow_two] using coeff_m04_qRest_sq_zero q
  have hrest1 : MvPolynomial.coeff m04 (qRest * MvPolynomial.monomial m01 b) = 0 := by
    dsimp [qRest]
    exact coeff_m04_qRest_mul_m01_zero q b
  have hrest2 : MvPolynomial.coeff m04 (qRest * MvPolynomial.monomial m02 c) = 0 := by
    dsimp [qRest]
    exact coeff_m04_qRest_mul_m02_zero q c
  have h1rest : MvPolynomial.coeff m04 (MvPolynomial.monomial m01 b * qRest) = 0 := by
    dsimp [qRest]
    exact coeff_m04_m01_mul_qRest_zero q b
  have h2rest : MvPolynomial.coeff m04 (MvPolynomial.monomial m02 c * qRest) = 0 := by
    dsimp [qRest]
    exact coeff_m04_m02_mul_qRest_zero q c
  calc
    MvPolynomial.coeff m04 (q ^ 2)
        = MvPolynomial.coeff m04
            (qRest * qRest + qRest * MvPolynomial.monomial m01 b +
              qRest * MvPolynomial.monomial m02 c +
              MvPolynomial.monomial m01 b * qRest +
              MvPolynomial.monomial m01 b * MvPolynomial.monomial m01 b +
              MvPolynomial.monomial m01 b * MvPolynomial.monomial m02 c +
              MvPolynomial.monomial m02 c * qRest +
              MvPolynomial.monomial m02 c * MvPolynomial.monomial m01 b +
              MvPolynomial.monomial m02 c * MvPolynomial.monomial m02 c) := by
                rw [pow_two, hsplit]
                ring_nf
    _ = c ^ 2 := by
          repeat rw [MvPolynomial.coeff_add]
          rw [hrestsq, hrest1, hrest2, h1rest, h11, h12, h2rest, h21, h22c]
          ring

/-- The affine linear polynomial `b + c x₁` used in the rank-13 kernel line. -/
def mixedAffineRank13Line (b c : ℝ) : Poly := MvPolynomial.C b + MvPolynomial.C c * x1

/-- The explicit kernel family for the rank-13 mixed-affine representative. -/
def mixedAffineRank13KerLine (b c : ℝ) : RankFourVec :=
  ![0, 0, -(x1 * mixedAffineRank13Line b c), x0 * mixedAffineRank13Line b c]

theorem mixedAffineRank13Rep_admissible : IsAdmissiblePoint mixedAffineRank13Rep := by
  intro i
  fin_cases i
  · simp [mixedAffineRank13Rep, IsQuadratic]
  · simp [mixedAffineRank13Rep, x0, x1, IsQuadratic]
  · simp [mixedAffineRank13Rep, x0, x1, IsQuadratic, MvPolynomial.totalDegree_X_pow]
  · simpa [mixedAffineRank13Rep] using isQuadratic_x0_mul_x1

private theorem totalDegree_mixedAffineRank13Line_le (b c : ℝ) :
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

private theorem isQuadratic_x1_mul_mixedAffineRank13Line (b c : ℝ) :
    IsQuadratic (x1 * mixedAffineRank13Line b c) := by
  have hx1 : x1.totalDegree ≤ 1 := by simp [x1]
  calc
    (x1 * mixedAffineRank13Line b c).totalDegree ≤
        x1.totalDegree + (mixedAffineRank13Line b c).totalDegree := by
          exact MvPolynomial.totalDegree_mul _ _
    _ ≤ 1 + 1 := by
          exact add_le_add hx1 (totalDegree_mixedAffineRank13Line_le b c)
    _ = 2 := by norm_num

private theorem isQuadratic_x0_mul_mixedAffineRank13Line (b c : ℝ) :
    IsQuadratic (x0 * mixedAffineRank13Line b c) := by
  have hx0 : x0.totalDegree ≤ 1 := by simp [x0]
  calc
    (x0 * mixedAffineRank13Line b c).totalDegree ≤
        x0.totalDegree + (mixedAffineRank13Line b c).totalDegree := by
          exact MvPolynomial.totalDegree_mul _ _
    _ ≤ 1 + 1 := by
          exact add_le_add hx0 (totalDegree_mixedAffineRank13Line_le b c)
    _ = 2 := by norm_num

private theorem coeff_m00_mixedAffineRank13Line (b c : ℝ) :
    MvPolynomial.coeff m00 (mixedAffineRank13Line b c) = b := by
  unfold mixedAffineRank13Line
  simp [m00, x1]

private theorem coeff_m01_mixedAffineRank13Line (b c : ℝ) :
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

private theorem coeff_m01_x1_mul_mixedAffineRank13Line (b c : ℝ) :
    MvPolynomial.coeff m01 (x1 * mixedAffineRank13Line b c) = b := by
  rw [show x1 = MvPolynomial.monomial m01 (1 : ℝ) by
    simp [x1, m01, MvPolynomial.monomial_eq]]
  rw [MvPolynomial.coeff_monomial_mul']
  have hsub : m01 - m01 = m00 := by
    ext i
    fin_cases i <;> simp [m00, m01]
  rw [if_pos le_rfl, hsub, coeff_m00_mixedAffineRank13Line]
  simp

private theorem coeff_m02_x1_mul_mixedAffineRank13Line (b c : ℝ) :
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
  rw [if_pos hmle, hsub, coeff_m01_mixedAffineRank13Line]
  simp

private theorem coeff_m01_x0_mul_mixedAffineRank13Line (b c : ℝ) :
    MvPolynomial.coeff m01 (x0 * mixedAffineRank13Line b c) = 0 := by
  rw [show x0 = MvPolynomial.monomial m10 (1 : ℝ) by
    simp [x0, m10, MvPolynomial.monomial_eq]]
  rw [MvPolynomial.coeff_monomial_mul']
  have hnot : ¬ m10 ≤ m01 := by
    intro h
    have := h 0
    simp [m10, m01] at this
  rw [if_neg hnot]

private theorem coeff_m02_x0_mul_mixedAffineRank13Line (b c : ℝ) :
    MvPolynomial.coeff m02 (x0 * mixedAffineRank13Line b c) = 0 := by
  rw [show x0 = MvPolynomial.monomial m10 (1 : ℝ) by
    simp [x0, m10, MvPolynomial.monomial_eq]]
  rw [MvPolynomial.coeff_monomial_mul']
  have hnot : ¬ m10 ≤ m02 := by
    intro h
    have := h 0
    simp [m10, m02] at this
  rw [if_neg hnot]

theorem mixedAffineRank13KerLine_inKer (b c : ℝ) :
    InAdmissibleKer mixedAffineRank13Rep (mixedAffineRank13KerLine b c) := by
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i
    · simp [mixedAffineRank13KerLine, IsQuadratic]
    · simp [mixedAffineRank13KerLine, IsQuadratic]
    ·
      calc
        (-(x1 * mixedAffineRank13Line b c) : Poly).totalDegree
            = (x1 * mixedAffineRank13Line b c).totalDegree := by
                rw [MvPolynomial.totalDegree_neg]
        _ ≤ 2 := isQuadratic_x1_mul_mixedAffineRank13Line b c
    · exact isQuadratic_x0_mul_mixedAffineRank13Line b c
  · simp [A, mixedAffineRank13Rep, mixedAffineRank13KerLine, mixedAffineRank13Line,
      Fin.sum_univ_four, x0, x1]
    ring

theorem coeff_m03_sigma_mixedAffineRank13KerLine (b c : ℝ) :
    MvPolynomial.coeff m03 (sigma (mixedAffineRank13KerLine b c)) = 2 * b * c := by
  have h1 :
      MvPolynomial.coeff m03 ((x1 * mixedAffineRank13Line b c) ^ 2) = 2 * b * c := by
    rw [coeff_m03_sq_of_quadratic _ (isQuadratic_x1_mul_mixedAffineRank13Line b c)]
    rw [coeff_m01_x1_mul_mixedAffineRank13Line, coeff_m02_x1_mul_mixedAffineRank13Line]
  have h0 :
      MvPolynomial.coeff m03 ((x0 * mixedAffineRank13Line b c) ^ 2) = 0 := by
    rw [coeff_m03_sq_of_quadratic _ (isQuadratic_x0_mul_mixedAffineRank13Line b c)]
    rw [coeff_m01_x0_mul_mixedAffineRank13Line, coeff_m02_x0_mul_mixedAffineRank13Line]
    ring
  rw [sigma, Fin.sum_univ_four]
  simp [mixedAffineRank13KerLine, h1, h0]

theorem coeff_m04_sigma_mixedAffineRank13KerLine (b c : ℝ) :
    MvPolynomial.coeff m04 (sigma (mixedAffineRank13KerLine b c)) = c ^ 2 := by
  have h1 :
      MvPolynomial.coeff m04 ((x1 * mixedAffineRank13Line b c) ^ 2) = c ^ 2 := by
    rw [coeff_m04_sq_of_quadratic _ (isQuadratic_x1_mul_mixedAffineRank13Line b c)]
    rw [coeff_m02_x1_mul_mixedAffineRank13Line]
  have h0 :
      MvPolynomial.coeff m04 ((x0 * mixedAffineRank13Line b c) ^ 2) = 0 := by
    rw [coeff_m04_sq_of_quadratic _ (isQuadratic_x0_mul_mixedAffineRank13Line b c)]
    rw [coeff_m02_x0_mul_mixedAffineRank13Line]
    ring
  rw [sigma, Fin.sum_univ_four]
  simp [mixedAffineRank13KerLine, h1, h0]

theorem coeff_m03_sq_of_quadratic_eq (q : Poly) (hq : IsQuadratic q) :
    MvPolynomial.coeff m03 (q ^ 2) =
      2 * MvPolynomial.coeff m01 q * MvPolynomial.coeff m02 q :=
  coeff_m03_sq_of_quadratic q hq

theorem coeff_m04_sq_of_quadratic_eq (q : Poly) (hq : IsQuadratic q) :
    MvPolynomial.coeff m04 (q ^ 2) = (MvPolynomial.coeff m02 q) ^ 2 :=
  coeff_m04_sq_of_quadratic q hq

theorem residual_eq_zero_mixedAffineRank13Rep
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p mixedAffineRank13Rep) :
    residual p mixedAffineRank13Rep = 0 := by
  rcases hp with ⟨hpquartic, k, qs, hqdeg, hpq⟩
  let s3 : ℝ := ∑ i : Fin k, MvPolynomial.coeff m01 (qs i) * MvPolynomial.coeff m02 (qs i)
  let s4 : ℝ := ∑ i : Fin k, (MvPolynomial.coeff m02 (qs i)) ^ 2
  let c : ℝ := Real.sqrt s4
  let b : ℝ := s3 / c
  let w : RankFourVec := mixedAffineRank13KerLine b c
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
        exact coeff_m03_sq_of_quadratic (qs i) (hqdeg i)
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
        exact coeff_m04_sq_of_quadratic (qs i) (hqdeg i)
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
  have hwker : InAdmissibleKer mixedAffineRank13Rep w := by
    dsimp [w]
    exact mixedAffineRank13KerLine_inKer b c
  have hw03 : MvPolynomial.coeff m03 (sigma w) = 2 * s3 := by
    change MvPolynomial.coeff m03 (sigma (mixedAffineRank13KerLine b c)) = 2 * s3
    rw [coeff_m03_sigma_mixedAffineRank13KerLine]
    by_cases hc0 : c = 0
    · have hs3zero : s3 = 0 := hs3_zero_of_c_zero hc0
      simp [b, hc0, hs3zero]
    · dsimp [b]
      field_simp [hc0]
  have hw04 : MvPolynomial.coeff m04 (sigma w) = s4 := by
    change MvPolynomial.coeff m04 (sigma (mixedAffineRank13KerLine b c)) = s4
    rw [coeff_m04_sigma_mixedAffineRank13KerLine, hc_sq]
  have hquartic_sub : IsQuartic (p - sigma w) := by
    calc
      (p - sigma w).totalDegree ≤ max p.totalDegree (sigma w).totalDegree := by
        exact MvPolynomial.totalDegree_sub _ _
      _ ≤ 4 := by
        exact max_le hpquartic (isQuartic_sigma_of_admissible_local hwker.1)
  have h03_sub : MvPolynomial.coeff m03 (p - sigma w) = 0 := by
    rw [MvPolynomial.coeff_sub, hp03, hw03]
    ring
  have h04_sub : MvPolynomial.coeff m04 (p - sigma w) = 0 := by
    rw [MvPolynomial.coeff_sub, hp04, hw04]
    ring
  have himg : InAdmissibleImage mixedAffineRank13Rep (p - sigma w) :=
    quartic_in_image_mixedAffineRank13Rep_of_coeff_m03_m04_zero hquartic_sub h03_sub h04_sub
  refine admissible_image_plus_cone_residual_eq_zero (B := B)
    (u := mixedAffineRank13Rep) (uImg := mixedAffineRank13Rep)
    mixedAffineRank13Rep_admissible hsocp
    (imageOrthogonalResidual_self (B := B) hsocp.1) ?_
  refine ⟨p - sigma w, {w}, himg, ?_, ?_⟩
  · intro w' hw'
    have hw' : w' = w := by simpa using hw'
    subst hw'
    exact hwker
  · simp [w, sub_eq_add_neg]

end TernaryQuartic
