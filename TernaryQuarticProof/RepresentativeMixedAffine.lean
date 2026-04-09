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

private theorem A_smul_right (u v : RankFourVec) (t : ℝ) :
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

private theorem isAdmissibleDirection_smul (t : ℝ) {v : RankFourVec}
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
  refine ⟨isAdmissibleDirection_smul t mixedAffineRank14KerBase_admissible, ?_⟩
  rw [A_smul_right, mixedAffineRank14KerBase_inKer.2]
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

private theorem isQuartic_sigma_of_admissible {u : RankFourVec}
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
        exact max_le hpquartic (isQuartic_sigma_of_admissible hwker.1)
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

end TernaryQuartic
