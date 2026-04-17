import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finsupp.Fin
import TernaryQuarticProof.AffineSocpTransform
import TernaryQuarticProof.RepresentativeTransport

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace TernaryQuartic

open scoped BigOperators

def x0 : Poly := MvPolynomial.X 0

def x1 : Poly := MvPolynomial.X 1

/-- The rank-4 representative for the `dim(W ∩ Aff₁)=1` constant case. -/
def constQuadRep : RankFourVec := ![(1 : Poly), x0 ^ 2, x0 * x1, x1 ^ 2]

/-- The canonical homogeneous quadratic basis. -/
def homQuadBasis : Fin 3 → Poly
  | 0 => x0 ^ 2
  | 1 => x0 * x1
  | 2 => x1 ^ 2

/-- Turn any explicit scalar relation `∑ cᵢ uᵢ = r` into an admissible image
statement for `r * q`. -/
theorem inAdmissibleImage_of_relation_mul_const
    {u : RankFourVec} {c : Fin 4 → ℝ} {r q : Poly}
    (hc : ∑ i : Fin 4, c i • u i = r)
    (hq : IsQuadratic q) :
    InAdmissibleImage u (r * q) := by
  refine ⟨relationDirection c q, relationDirection_admissible c hq, ?_⟩
  rw [A_relationDirection, relationPoly]
  rw [hc]

private theorem relation_linearCombination_three
    {u : RankFourVec} {c : Fin 3 → Fin 4 → ℝ} {q : Fin 3 → Poly}
    (hc : ∀ j : Fin 3, ∑ i : Fin 4, c j i • u i = q j)
    (r : Fin 3 → ℝ) :
    ∑ i : Fin 4, (∑ j : Fin 3, r j * c j i) • u i = ∑ j : Fin 3, r j • q j := by
  calc
    ∑ i : Fin 4, (∑ j : Fin 3, r j * c j i) • u i
        = ∑ i : Fin 4, ∑ j : Fin 3, (r j * c j i) • u i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            change (∑ j : Fin 3, r j * c j i) • u i = ∑ j : Fin 3, (r j * c j i) • u i
            exact (Finset.sum_smul
                (s := (Finset.univ : Finset (Fin 3)))
                (f := fun j : Fin 3 => r j * c j i)
                (x := u i))
    _ = ∑ j : Fin 3, ∑ i : Fin 4, (r j * c j i) • u i := by
          rw [Finset.sum_comm]
    _ = ∑ j : Fin 3, r j • (∑ i : Fin 4, c j i • u i) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          simp [Finset.smul_sum, smul_smul]
    _ = ∑ j : Fin 3, r j • q j := by
          simp [hc]

/-- Reconstruct exact `x₀²,x₀x₁,x₁²` relations from any invertible `3 × 3`
homogeneous-quadratic relation matrix. -/
theorem exact_relations_of_homQuadBasis_det
    {u : RankFourVec}
    {c : Fin 3 → Fin 4 → ℝ} {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hc :
      ∀ j : Fin 3,
        ∑ i : Fin 4, c j i • u i = ∑ k : Fin 3, A j k • homQuadBasis k)
    (hdet : A.det ≠ 0) :
    ∃ d : Fin 3 → Fin 4 → ℝ,
      ∀ k : Fin 3, ∑ i : Fin 4, d k i • u i = homQuadBasis k := by
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  letI : Invertible A := Classical.choice ((A.isUnit_iff_isUnit_det.mpr hunit).nonempty_invertible)
  let d : Fin 3 → Fin 4 → ℝ := fun k i => ∑ j : Fin 3, A⁻¹ k j * c j i
  refine ⟨d, ?_⟩
  intro k
  have hlin :=
    relation_linearCombination_three
      (u := u)
      (c := c)
      (q := fun j => ∑ l : Fin 3, A j l • homQuadBasis l)
      hc
      (fun j => A⁻¹ k j)
  calc
    ∑ i : Fin 4, d k i • u i
        = ∑ j : Fin 3, A⁻¹ k j • (∑ l : Fin 3, A j l • homQuadBasis l) := by
            simpa [d] using hlin
    _ = ∑ l : Fin 3, ((A⁻¹ * A) k l) • homQuadBasis l := by
          calc
            ∑ j : Fin 3, A⁻¹ k j • (∑ l : Fin 3, A j l • homQuadBasis l)
                = ∑ j : Fin 3, ∑ l : Fin 3, (A⁻¹ k j * A j l) • homQuadBasis l := by
                    simp [Finset.smul_sum, smul_smul]
            _ = ∑ l : Fin 3, ∑ j : Fin 3, (A⁻¹ k j * A j l) • homQuadBasis l := by
                  rw [Finset.sum_comm]
            _ = ∑ l : Fin 3, (∑ j : Fin 3, A⁻¹ k j * A j l) • homQuadBasis l := by
                  refine Finset.sum_congr rfl ?_
                  intro l hl
                  simpa [smul_smul] using
                    (Finset.sum_smul
                      (s := (Finset.univ : Finset (Fin 3)))
                      (f := fun j : Fin 3 => A⁻¹ k j * A j l)
                      (x := homQuadBasis l)).symm
            _ = ∑ l : Fin 3, ((A⁻¹ * A) k l) • homQuadBasis l := by
                  simp [Matrix.mul_apply]
    _ = homQuadBasis k := by
          rw [Matrix.inv_mul_of_invertible]
          fin_cases k <;> simp [Matrix.one_apply, homQuadBasis]

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

private theorem monomial_image_constQuadRep (s : Fin 2 →₀ ℕ) (a : ℝ)
    (hdeg : s.sum (fun _ e => e) ≤ 4) :
    InAdmissibleImage constQuadRep (MvPolynomial.monomial s a) := by
  let e0 := s 0
  let e1 := s 1
  have hsum : s.sum (fun _ e => e) = s 0 + s 1 := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
  have hs0 : s 0 + s 1 ≤ 4 := by
    simpa [hsum] using hdeg
  have hs : e0 + e1 ≤ 4 := by simpa [e0, e1] using hs0
  by_cases hsmall : e0 + e1 ≤ 2
  · refine ⟨![(MvPolynomial.C a * x0 ^ e0) * x1 ^ e1, 0, 0, 0], ?_, ?_⟩
    · intro i
      fin_cases i
      · exact isQuadratic_C_mul_pow_pow a e0 e1 hsmall
      · simp [IsQuadratic]
      · simp [IsQuadratic]
      · simp [IsQuadratic]
    · rw [monomial_fin2_eq]
      simp [e0, e1]
      simp [A, constQuadRep, Fin.sum_univ_four, x0, x1]
  · by_cases hx2 : 2 ≤ e0
    · refine ⟨![0, (MvPolynomial.C a * x0 ^ (e0 - 2)) * x1 ^ e1, 0, 0], ?_, ?_⟩
      · intro i
        fin_cases i
        · simp [IsQuadratic]
        · have hs2 : (e0 - 2) + e1 ≤ 2 := by omega
          exact isQuadratic_C_mul_pow_pow a (e0 - 2) e1 hs2
        · simp [IsQuadratic]
        · simp [IsQuadratic]
      · rw [monomial_fin2_eq]
        simp [e0, e1]
        calc
          A constQuadRep ![0, (MvPolynomial.C a * x0 ^ (e0 - 2)) * x1 ^ e1, 0, 0]
              = x0 ^ 2 * ((MvPolynomial.C a * x0 ^ (e0 - 2)) * x1 ^ e1) := by
                  simp [A, constQuadRep, Fin.sum_univ_four, x0, x1]
          _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                calc
                  x0 ^ 2 * ((MvPolynomial.C a * x0 ^ (e0 - 2)) * x1 ^ e1)
                      = MvPolynomial.C a * (x0 ^ 2 * x0 ^ (e0 - 2)) * x1 ^ e1 := by
                          ring_nf
                  _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                        rw [← pow_add, Nat.add_sub_of_le hx2]
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
            A constQuadRep ![0, 0, 0, (MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 2)]
                = x1 ^ 2 * ((MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 2)) := by
                    simp [A, constQuadRep, Fin.sum_univ_four, x0, x1]
            _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                  calc
                    x1 ^ 2 * ((MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 2))
                        = MvPolynomial.C a * x0 ^ e0 * (x1 ^ 2 * x1 ^ (e1 - 2)) := by
                            ring_nf
                    _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                          rw [← pow_add, Nat.add_sub_of_le hy2]
      · have hs1 : s 0 = 1 := by omega
        have hs2 : s 1 = 1 := by omega
        refine ⟨![0, 0, MvPolynomial.C a, 0], ?_, ?_⟩
        · intro i
          fin_cases i <;> simp [IsQuadratic]
        · rw [monomial_fin2_eq]
          simp [A, constQuadRep, Fin.sum_univ_four, x0, x1, hs1, hs2,
            mul_comm, mul_left_comm, mul_assoc]

theorem quartic_in_image_of_relations_const_x0sq_x0x1_x1sq
    {u : RankFourVec}
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0 ^ 2)
    (_h2 : ∑ i : Fin 4, c2 i • u i = x0 * x1)
    (h3 : ∑ i : Fin 4, c3 i • u i = x1 ^ 2)
    {p : Poly} (hp : IsQuartic p) :
    InAdmissibleImage u p := by
  classical
  rw [← MvPolynomial.support_sum_monomial_coeff p]
  let P : Finset (Fin 2 →₀ ℕ) → Prop := fun S =>
    (∀ s ∈ S, s ∈ p.support) →
      InAdmissibleImage u (∑ s ∈ S, MvPolynomial.monomial s (MvPolynomial.coeff s p))
  have hP : P p.support := by
    refine Finset.induction_on p.support ?base ?step
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
            (inAdmissibleImage_of_relation_mul_const
              (u := u) (c := c0) (r := (1 : Poly))
              (q := (MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ e0) * x1 ^ e1)
              h0 (isQuadratic_C_mul_pow_pow (MvPolynomial.coeff s p) e0 e1 hsmall))
        · by_cases hx2 : 2 ≤ e0
          · have hs2 : (e0 - 2) + e1 ≤ 2 := by omega
            have himg :=
              inAdmissibleImage_of_relation_mul_const
                (u := u) (c := c1) (r := x0 ^ 2)
                (q := (MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ (e0 - 2)) * x1 ^ e1)
                h1 (isQuadratic_C_mul_pow_pow (MvPolynomial.coeff s p) (e0 - 2) e1 hs2)
            rw [monomial_fin2_eq]
            simp [e0, e1] at himg ⊢
            have hmul :
                x0 ^ 2 * ((MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ (e0 - 2)) * x1 ^ e1) =
                  (MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ e0) * x1 ^ e1 := by
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
              inAdmissibleImage_of_relation_mul_const
                (u := u) (c := c3) (r := x1 ^ 2)
                (q := (MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ e0) * x1 ^ (e1 - 2))
                h3 (isQuadratic_C_mul_pow_pow (MvPolynomial.coeff s p) e0 (e1 - 2) hs2)
            rw [monomial_fin2_eq]
            simp [e0, e1] at himg ⊢
            have hmul :
                x1 ^ 2 * ((MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ e0) * x1 ^ (e1 - 2)) =
                  (MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ e0) * x1 ^ e1 := by
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
theorem residual_eq_zero_of_relations_const_x0sq_x0x1_x1sq
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0 ^ 2)
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 * x1)
    (h3 : ∑ i : Fin 4, c3 i • u i = x1 ^ 2)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_in_admissible_image
    (B := B) hu hsocp
    (quartic_in_image_of_relations_const_x0sq_x0x1_x1sq h0 h1 h2 h3 hp.1)

theorem quartic_in_image_of_relations_const_affineTail_x0sq_affineTail_x0x1_affineTail_x1sq
    {u : RankFourVec}
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {a b c d e f : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = a • x0 + b • x1 + x0 ^ 2)
    (h2 : ∑ i : Fin 4, c2 i • u i = c • x0 + d • x1 + (x0 * x1 : Poly))
    (h3 : ∑ i : Fin 4, c3 i • u i = e • x0 + f • x1 + x1 ^ 2)
    {p : Poly} (hp : IsQuartic p) :
    InAdmissibleImage u p := by
  classical
  have honeImg : InAdmissibleImage u (1 : Poly) := by
    simpa [one_mul] using
      (inAdmissibleImage_of_relation_mul_const
        (u := u) (c := c0) (r := (1 : Poly)) (q := (1 : Poly))
        h0 (by simp [IsQuadratic]))
  have hx0Img : InAdmissibleImage u x0 := by
    simpa [one_mul] using
      (inAdmissibleImage_of_relation_mul_const
        (u := u) (c := c0) (r := (1 : Poly)) (q := x0)
        h0 (by simp [x0, IsQuadratic]))
  have hx1Img : InAdmissibleImage u x1 := by
    simpa [one_mul] using
      (inAdmissibleImage_of_relation_mul_const
        (u := u) (c := c0) (r := (1 : Poly)) (q := x1)
        h0 (by simp [x1, IsQuadratic]))
  have hx0sqImg : InAdmissibleImage u (x0 ^ 2 : Poly) := by
    simpa [one_mul] using
      (inAdmissibleImage_of_relation_mul_const
        (u := u) (c := c0) (r := (1 : Poly)) (q := x0 ^ 2)
        h0 (by simp [x0, IsQuadratic]))
  have hx0x1Img : InAdmissibleImage u (x0 * x1 : Poly) := by
    simpa [one_mul] using
      (inAdmissibleImage_of_relation_mul_const
        (u := u) (c := c0) (r := (1 : Poly)) (q := (x0 * x1 : Poly))
        h0 (by
          calc
            (x0 * x1 : Poly).totalDegree ≤ x0.totalDegree + x1.totalDegree := by
              exact MvPolynomial.totalDegree_mul _ _
            _ ≤ 2 := by simp [x0, x1]))
  have hx1sqImg : InAdmissibleImage u (x1 ^ 2 : Poly) := by
    simpa [one_mul] using
      (inAdmissibleImage_of_relation_mul_const
        (u := u) (c := c0) (r := (1 : Poly)) (q := x1 ^ 2)
        h0 (by simp [x1, IsQuadratic]))
  have hq1Img : InAdmissibleImage u (a • x0 + b • x1 + x0 ^ 2) := by
    simpa [one_mul] using
      (inAdmissibleImage_of_relation_mul_const
        (u := u) (c := c1)
        (r := a • x0 + b • x1 + x0 ^ 2) (q := (1 : Poly))
        h1 (by simp [IsQuadratic]))
  have hq2Img : InAdmissibleImage u (c • x0 + d • x1 + (x0 * x1 : Poly)) := by
    simpa [one_mul] using
      (inAdmissibleImage_of_relation_mul_const
        (u := u) (c := c2)
        (r := c • x0 + d • x1 + (x0 * x1 : Poly)) (q := (1 : Poly))
        h2 (by simp [IsQuadratic]))
  have hq3Img : InAdmissibleImage u (e • x0 + f • x1 + x1 ^ 2) := by
    simpa [one_mul] using
      (inAdmissibleImage_of_relation_mul_const
        (u := u) (c := c3)
        (r := e • x0 + f • x1 + x1 ^ 2) (q := (1 : Poly))
        h3 (by simp [IsQuadratic]))
  have hx0cub : InAdmissibleImage u (x0 ^ 3 : Poly) := by
    have himg :
        InAdmissibleImage u ((a • x0 + b • x1 + x0 ^ 2) * x0) := by
      exact inAdmissibleImage_of_relation_mul_const
        (u := u) (c := c1) (r := a • x0 + b • x1 + x0 ^ 2) (q := x0)
        h1 (by simp [x0, IsQuadratic])
    have hEq :
        (a • x0 + b • x1 + x0 ^ 2) * x0 - a • (x0 ^ 2 : Poly) -
            b • (x0 * x1 : Poly) = (x0 ^ 3 : Poly) := by
      simp [MvPolynomial.smul_eq_C_mul]
      ring
    exact hEq ▸ inAdmissibleImage_sub u
      (inAdmissibleImage_sub u himg (inAdmissibleImage_smul u a hx0sqImg))
      (inAdmissibleImage_smul u b hx0x1Img)
  have hx0sqx1 : InAdmissibleImage u ((x0 ^ 2 : Poly) * x1) := by
    have himg :
        InAdmissibleImage u ((a • x0 + b • x1 + x0 ^ 2) * x1) := by
      exact inAdmissibleImage_of_relation_mul_const
        (u := u) (c := c1) (r := a • x0 + b • x1 + x0 ^ 2) (q := x1)
        h1 (by simp [x1, IsQuadratic])
    have hEq :
        (a • x0 + b • x1 + x0 ^ 2) * x1 - a • (x0 * x1 : Poly) -
            b • (x1 ^ 2 : Poly) = ((x0 ^ 2 : Poly) * x1) := by
      simp [MvPolynomial.smul_eq_C_mul]
      ring
    exact hEq ▸ inAdmissibleImage_sub u
      (inAdmissibleImage_sub u himg (inAdmissibleImage_smul u a hx0x1Img))
      (inAdmissibleImage_smul u b hx1sqImg)
  have hx0x1sq : InAdmissibleImage u (x0 * x1 ^ 2 : Poly) := by
    have himg :
        InAdmissibleImage u ((e • x0 + f • x1 + x1 ^ 2) * x0) := by
      exact inAdmissibleImage_of_relation_mul_const
        (u := u) (c := c3) (r := e • x0 + f • x1 + x1 ^ 2) (q := x0)
        h3 (by simp [x0, IsQuadratic])
    have hEq :
        (e • x0 + f • x1 + x1 ^ 2) * x0 - e • (x0 ^ 2 : Poly) -
            f • (x0 * x1 : Poly) = (x0 * x1 ^ 2 : Poly) := by
      simp [MvPolynomial.smul_eq_C_mul]
      ring
    exact hEq ▸ inAdmissibleImage_sub u
      (inAdmissibleImage_sub u himg (inAdmissibleImage_smul u e hx0sqImg))
      (inAdmissibleImage_smul u f hx0x1Img)
  have hx1cub : InAdmissibleImage u (x1 ^ 3 : Poly) := by
    have himg :
        InAdmissibleImage u ((e • x0 + f • x1 + x1 ^ 2) * x1) := by
      exact inAdmissibleImage_of_relation_mul_const
        (u := u) (c := c3) (r := e • x0 + f • x1 + x1 ^ 2) (q := x1)
        h3 (by simp [x1, IsQuadratic])
    have hEq :
        (e • x0 + f • x1 + x1 ^ 2) * x1 - e • (x0 * x1 : Poly) -
            f • (x1 ^ 2 : Poly) = (x1 ^ 3 : Poly) := by
      simp [MvPolynomial.smul_eq_C_mul]
      ring
    exact hEq ▸ inAdmissibleImage_sub u
      (inAdmissibleImage_sub u himg (inAdmissibleImage_smul u e hx0x1Img))
      (inAdmissibleImage_smul u f hx1sqImg)
  have hx0quart : InAdmissibleImage u (x0 ^ 4 : Poly) := by
    have himg :
        InAdmissibleImage u ((a • x0 + b • x1 + x0 ^ 2) * x0 ^ 2) := by
      exact inAdmissibleImage_of_relation_mul_const
        (u := u) (c := c1) (r := a • x0 + b • x1 + x0 ^ 2) (q := x0 ^ 2)
        h1 (by simp [x0, IsQuadratic])
    have hEq :
        (a • x0 + b • x1 + x0 ^ 2) * x0 ^ 2 - a • (x0 ^ 3 : Poly) -
            b • (((x0 ^ 2 : Poly) * x1)) = (x0 ^ 4 : Poly) := by
      simp [MvPolynomial.smul_eq_C_mul]
      ring
    exact hEq ▸ inAdmissibleImage_sub u
      (inAdmissibleImage_sub u himg (inAdmissibleImage_smul u a hx0cub))
      (inAdmissibleImage_smul u b hx0sqx1)
  have hx0cubx1 : InAdmissibleImage u ((x0 ^ 3 : Poly) * x1) := by
    have himg :
        InAdmissibleImage u ((c • x0 + d • x1 + (x0 * x1 : Poly)) * x0 ^ 2) := by
      exact inAdmissibleImage_of_relation_mul_const
        (u := u) (c := c2) (r := c • x0 + d • x1 + (x0 * x1 : Poly)) (q := x0 ^ 2)
        h2 (by simp [x0, IsQuadratic])
    have hEq :
        (c • x0 + d • x1 + (x0 * x1 : Poly)) * x0 ^ 2 - c • (x0 ^ 3 : Poly) -
            d • (((x0 ^ 2 : Poly) * x1)) = ((x0 ^ 3 : Poly) * x1) := by
      simp [MvPolynomial.smul_eq_C_mul]
      ring
    exact hEq ▸ inAdmissibleImage_sub u
      (inAdmissibleImage_sub u himg (inAdmissibleImage_smul u c hx0cub))
      (inAdmissibleImage_smul u d hx0sqx1)
  have hx0sqx1sq : InAdmissibleImage u ((x0 ^ 2 : Poly) * x1 ^ 2) := by
    have himg :
        InAdmissibleImage u ((c • x0 + d • x1 + (x0 * x1 : Poly)) * (x0 * x1 : Poly)) := by
      exact inAdmissibleImage_of_relation_mul_const
        (u := u) (c := c2) (r := c • x0 + d • x1 + (x0 * x1 : Poly)) (q := (x0 * x1 : Poly))
        h2 (by
          calc
            (x0 * x1 : Poly).totalDegree ≤ x0.totalDegree + x1.totalDegree := by
              exact MvPolynomial.totalDegree_mul _ _
            _ ≤ 2 := by simp [x0, x1])
    have hEq :
        (c • x0 + d • x1 + (x0 * x1 : Poly)) * (x0 * x1 : Poly) -
            c • (((x0 ^ 2 : Poly) * x1)) - d • (x0 * x1 ^ 2 : Poly) =
          ((x0 ^ 2 : Poly) * x1 ^ 2) := by
      simp [MvPolynomial.smul_eq_C_mul]
      ring
    exact hEq ▸ inAdmissibleImage_sub u
      (inAdmissibleImage_sub u himg (inAdmissibleImage_smul u c hx0sqx1))
      (inAdmissibleImage_smul u d hx0x1sq)
  have hx0x1cub : InAdmissibleImage u (x0 * x1 ^ 3 : Poly) := by
    have himg :
        InAdmissibleImage u ((c • x0 + d • x1 + (x0 * x1 : Poly)) * x1 ^ 2) := by
      exact inAdmissibleImage_of_relation_mul_const
        (u := u) (c := c2) (r := c • x0 + d • x1 + (x0 * x1 : Poly)) (q := x1 ^ 2)
        h2 (by simp [x1, IsQuadratic])
    have hEq :
        (c • x0 + d • x1 + (x0 * x1 : Poly)) * x1 ^ 2 -
            c • (x0 * x1 ^ 2 : Poly) - d • (x1 ^ 3 : Poly) =
          (x0 * x1 ^ 3 : Poly) := by
      simp [MvPolynomial.smul_eq_C_mul]
      ring
    exact hEq ▸ inAdmissibleImage_sub u
      (inAdmissibleImage_sub u himg (inAdmissibleImage_smul u c hx0x1sq))
      (inAdmissibleImage_smul u d hx1cub)
  have hx1quart : InAdmissibleImage u (x1 ^ 4 : Poly) := by
    have himg :
        InAdmissibleImage u ((e • x0 + f • x1 + x1 ^ 2) * x1 ^ 2) := by
      exact inAdmissibleImage_of_relation_mul_const
        (u := u) (c := c3) (r := e • x0 + f • x1 + x1 ^ 2) (q := x1 ^ 2)
        h3 (by simp [x1, IsQuadratic])
    have hEq :
        (e • x0 + f • x1 + x1 ^ 2) * x1 ^ 2 - e • (x0 * x1 ^ 2 : Poly) -
            f • (x1 ^ 3 : Poly) = (x1 ^ 4 : Poly) := by
      simp [MvPolynomial.smul_eq_C_mul]
      ring
    exact hEq ▸ inAdmissibleImage_sub u
      (inAdmissibleImage_sub u himg (inAdmissibleImage_smul u e hx0x1sq))
      (inAdmissibleImage_smul u f hx1cub)
  let monomialImage :
      ∀ (s : Fin 2 →₀ ℕ) (r : ℝ),
        s.sum (fun _ n => n) ≤ 4 →
        InAdmissibleImage u (MvPolynomial.monomial s r) := by
    intro s r hdeg
    let e0 := s 0
    let e1 := s 1
    have hsum : s.sum (fun _ n => n) = s 0 + s 1 := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
    have hs : e0 + e1 ≤ 4 := by
      simpa [e0, e1, hsum] using hdeg
    by_cases hsmall : e0 + e1 ≤ 2
    · by_cases he2 : 2 ≤ e1
      · have he0 : e0 = 0 := by omega
        have he1 : e1 = 2 := by omega
        rw [monomial_fin2_eq]
        simpa [MvPolynomial.smul_eq_C_mul, e0, e1, he0, he1] using
          (inAdmissibleImage_smul u r hx1sqImg)
      · have he1le : e1 ≤ 1 := by omega
        by_cases he1 : e1 = 1
        · by_cases hx0 : e0 = 0
          · rw [monomial_fin2_eq]
            simpa [MvPolynomial.smul_eq_C_mul, e0, e1, hx0, he1, x1,
              mul_comm, mul_left_comm, mul_assoc] using
              (inAdmissibleImage_smul u r hx1Img)
          · have hx1 : e0 = 1 := by omega
            rw [monomial_fin2_eq]
            simpa [MvPolynomial.smul_eq_C_mul, e0, e1, hx1, he1,
              mul_assoc, mul_left_comm, mul_comm] using
              (inAdmissibleImage_smul u r hx0x1Img)
        · have he0 : e1 = 0 := by omega
          by_cases hx0 : e0 = 0
          · rw [monomial_fin2_eq]
            simpa [MvPolynomial.smul_eq_C_mul, e0, e1, hx0, he0] using
              (inAdmissibleImage_smul u r honeImg)
          · by_cases hx1 : e0 = 1
            · rw [monomial_fin2_eq]
              simpa [MvPolynomial.smul_eq_C_mul, e0, e1, hx1, he0, x0,
                mul_assoc, mul_left_comm, mul_comm] using
                (inAdmissibleImage_smul u r hx0Img)
            · have hx2 : e0 = 2 := by omega
              rw [monomial_fin2_eq]
              simpa [MvPolynomial.smul_eq_C_mul, e0, e1, hx2, he0] using
                (inAdmissibleImage_smul u r hx0sqImg)
    · by_cases hxy : 1 ≤ e0 ∧ 1 ≤ e1
      · have hcases :
            (e0 = 2 ∧ e1 = 1) ∨ (e0 = 1 ∧ e1 = 2) ∨
              (e0 = 3 ∧ e1 = 1) ∨ (e0 = 2 ∧ e1 = 2) ∨ (e0 = 1 ∧ e1 = 3) := by
          omega
        rcases hcases with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
        · rw [monomial_fin2_eq]
          simpa [MvPolynomial.smul_eq_C_mul, e0, e1, hx, hy, mul_assoc, mul_left_comm, mul_comm]
            using (inAdmissibleImage_smul u r hx0sqx1)
        · rw [monomial_fin2_eq]
          simpa [MvPolynomial.smul_eq_C_mul, e0, e1, hx, hy, mul_assoc, mul_left_comm, mul_comm]
            using (inAdmissibleImage_smul u r hx0x1sq)
        · rw [monomial_fin2_eq]
          simpa [MvPolynomial.smul_eq_C_mul, e0, e1, hx, hy, mul_assoc, mul_left_comm, mul_comm]
            using (inAdmissibleImage_smul u r hx0cubx1)
        · rw [monomial_fin2_eq]
          simpa [MvPolynomial.smul_eq_C_mul, e0, e1, hx, hy, mul_assoc, mul_left_comm, mul_comm]
            using (inAdmissibleImage_smul u r hx0sqx1sq)
        · rw [monomial_fin2_eq]
          simpa [MvPolynomial.smul_eq_C_mul, e0, e1, hx, hy, mul_assoc, mul_left_comm, mul_comm]
            using (inAdmissibleImage_smul u r hx0x1cub)
      · have hpure : e0 = 0 ∨ e1 = 0 := by omega
        rcases hpure with hx0 | hy0
        · have hy3or4 : e1 = 3 ∨ e1 = 4 := by omega
          rcases hy3or4 with hy3 | hy4
          · have hmon :
              MvPolynomial.monomial s r = r • x1 ^ 3 := by
              rw [monomial_fin2_eq]
              simp [MvPolynomial.smul_eq_C_mul, e0, e1, hx0, hy3]
            simpa [hmon] using inAdmissibleImage_smul u r hx1cub
          · have hmon :
              MvPolynomial.monomial s r = r • x1 ^ 4 := by
              rw [monomial_fin2_eq]
              simp [MvPolynomial.smul_eq_C_mul, e0, e1, hx0, hy4]
            simpa [hmon] using inAdmissibleImage_smul u r hx1quart
        · have hx3or4 : e0 = 3 ∨ e0 = 4 := by omega
          rcases hx3or4 with hx3 | hx4
          · have hmon :
              MvPolynomial.monomial s r = r • x0 ^ 3 := by
              rw [monomial_fin2_eq]
              simp [MvPolynomial.smul_eq_C_mul, e0, e1, hx3, hy0]
            simpa [hmon] using inAdmissibleImage_smul u r hx0cub
          · have hmon :
              MvPolynomial.monomial s r = r • x0 ^ 4 := by
              rw [monomial_fin2_eq]
              simp [MvPolynomial.smul_eq_C_mul, e0, e1, hx4, hy0]
            simpa [hmon] using inAdmissibleImage_smul u r hx0quart
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
      · have hsdeg : s.sum (fun _ n => n) ≤ 4 :=
          (MvPolynomial.le_totalDegree (hsub s (by simp))).trans hp
        exact monomialImage s (MvPolynomial.coeff s p) hsdeg
      · intro t ht
        exact hsub t (by simp [ht])
  exact hP (fun s hs => hs)

theorem residual_eq_zero_of_relations_const_affineTail_x0sq_affineTail_x0x1_affineTail_x1sq
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {a b c d e f : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = a • x0 + b • x1 + x0 ^ 2)
    (h2 : ∑ i : Fin 4, c2 i • u i = c • x0 + d • x1 + (x0 * x1 : Poly))
    (h3 : ∑ i : Fin 4, c3 i • u i = e • x0 + f • x1 + x1 ^ 2)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_in_admissible_image
    (B := B) hu hsocp
    (quartic_in_image_of_relations_const_affineTail_x0sq_affineTail_x0x1_affineTail_x1sq
      h0 h1 h2 h3 hp.1)

theorem quartic_in_image_of_relations_constX0_x0sq_x0x1_x1sq
    {u : RankFourVec}
    {α : ℝ}
    (hα : α ≠ 0)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (MvPolynomial.C α : Poly) + x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x0 ^ 2)
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 * x1)
    (h3 : ∑ i : Fin 4, c3 i • u i = x1 ^ 2)
    {p : Poly} (hp : IsQuartic p) :
    InAdmissibleImage u p := by
  classical
  have himgX0sq : InAdmissibleImage u (x0 ^ 2 : Poly) := by
    simpa [one_mul] using
      (inAdmissibleImage_of_relation_mul_const
        (u := u) (c := c1) (r := x0 ^ 2) (q := (1 : Poly))
        h1 (by simp [IsQuadratic]))
  have himgX0x1 : InAdmissibleImage u (x0 * x1 : Poly) := by
    simpa [one_mul] using
      (inAdmissibleImage_of_relation_mul_const
        (u := u) (c := c2) (r := x0 * x1) (q := (1 : Poly))
        h2 (by simp [IsQuadratic]))
  have himgX1sq : InAdmissibleImage u (x1 ^ 2 : Poly) := by
    simpa [one_mul] using
      (inAdmissibleImage_of_relation_mul_const
        (u := u) (c := c3) (r := x1 ^ 2) (q := (1 : Poly))
        h3 (by simp [IsQuadratic]))
  have himgAlphaX0 : InAdmissibleImage u ((α : ℝ) • x0) := by
    have himgMul :
        InAdmissibleImage u (((MvPolynomial.C α : Poly) + x0) * x0) := by
      exact inAdmissibleImage_of_relation_mul_const
        (u := u) (c := c0) (r := (MvPolynomial.C α : Poly) + x0)
        (q := x0) h0 (by simp [x0, IsQuadratic])
    have hEq : ((MvPolynomial.C α : Poly) + x0) * x0 - x0 ^ 2 = (α : ℝ) • x0 := by
      simp [MvPolynomial.smul_eq_C_mul, x0]
      ring
    rw [← hEq]
    exact inAdmissibleImage_sub u himgMul himgX0sq
  have himgX0 : InAdmissibleImage u x0 := by
    simpa [smul_smul, hα] using inAdmissibleImage_smul u α⁻¹ himgAlphaX0
  have himgOne : InAdmissibleImage u (1 : Poly) := by
    have himgLine :
        InAdmissibleImage u ((MvPolynomial.C α : Poly) + x0) := by
      simpa [one_mul] using
        (inAdmissibleImage_of_relation_mul_const
          (u := u) (c := c0) (r := (MvPolynomial.C α : Poly) + x0) (q := (1 : Poly))
          h0 (by simp [IsQuadratic]))
    have hEq : ((MvPolynomial.C α : Poly) + x0) - x0 = (α : ℝ) • (1 : Poly) := by
      simp [MvPolynomial.smul_eq_C_mul, x0]
    have himgAlphaOne : InAdmissibleImage u ((α : ℝ) • (1 : Poly)) := by
      rw [← hEq]
      exact inAdmissibleImage_sub u himgLine himgX0
    simpa [smul_smul, hα] using inAdmissibleImage_smul u α⁻¹ himgAlphaOne
  have himgAlphaX1 : InAdmissibleImage u ((α : ℝ) • x1) := by
    have himgMul :
        InAdmissibleImage u (((MvPolynomial.C α : Poly) + x0) * x1) := by
      exact inAdmissibleImage_of_relation_mul_const
        (u := u) (c := c0) (r := (MvPolynomial.C α : Poly) + x0)
        (q := x1) h0 (by simp [x1, IsQuadratic])
    have hEq : ((MvPolynomial.C α : Poly) + x0) * x1 - x0 * x1 = (α : ℝ) • x1 := by
      simp [MvPolynomial.smul_eq_C_mul, x0, x1]
      ring
    rw [← hEq]
    exact inAdmissibleImage_sub u himgMul himgX0x1
  have himgX1 : InAdmissibleImage u x1 := by
    simpa [smul_smul, hα] using inAdmissibleImage_smul u α⁻¹ himgAlphaX1
  let monomialImage : ∀ (s : Fin 2 →₀ ℕ) (r : ℝ),
      s.sum (fun _ e => e) ≤ 4 →
      InAdmissibleImage u (MvPolynomial.monomial s r) := by
    intro s r hdeg
    let e0 := s 0
    let e1 := s 1
    have hsum : s.sum (fun _ e => e) = s 0 + s 1 := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
    have hs : e0 + e1 ≤ 4 := by simpa [e0, e1, hsum] using hdeg
    by_cases hdeg1 : e0 + e1 ≤ 1
    · have hcases :
          (e0 = 0 ∧ e1 = 0) ∨ (e0 = 1 ∧ e1 = 0) ∨ (e0 = 0 ∧ e1 = 1) := by
        omega
      rcases hcases with ⟨hx0, hy0⟩ | ⟨hx1, hy0⟩ | ⟨hx0, hy1⟩
      · simpa [monomial_fin2_eq, e0, e1, hx0, hy0, MvPolynomial.smul_eq_C_mul] using
          (inAdmissibleImage_smul u r himgOne)
      · simpa [monomial_fin2_eq, e0, e1, hx1, hy0, MvPolynomial.smul_eq_C_mul] using
          (inAdmissibleImage_smul u r himgX0)
      · simpa [monomial_fin2_eq, e0, e1, hx0, hy1, MvPolynomial.smul_eq_C_mul] using
          (inAdmissibleImage_smul u r himgX1)
    · by_cases hy2 : 2 ≤ e1
      · have hs2 : e0 + (e1 - 2) ≤ 2 := by omega
        have himg :=
          inAdmissibleImage_of_relation_mul_const
            (u := u) (c := c3) (r := x1 ^ 2)
            (q := (MvPolynomial.C r * x0 ^ e0) * x1 ^ (e1 - 2))
            h3 (isQuadratic_C_mul_pow_pow r e0 (e1 - 2) hs2)
        rw [monomial_fin2_eq]
        simp [e0, e1] at himg ⊢
        have hmul :
            x1 ^ 2 * ((MvPolynomial.C r * x0 ^ e0) * x1 ^ (e1 - 2)) =
              (MvPolynomial.C r * x0 ^ e0) * x1 ^ e1 := by
          calc
            x1 ^ 2 * ((MvPolynomial.C r * x0 ^ e0) * x1 ^ (e1 - 2))
                = MvPolynomial.C r * x0 ^ e0 * (x1 ^ 2 * x1 ^ (e1 - 2)) := by
                    ring_nf
            _ = (MvPolynomial.C r * x0 ^ e0) * x1 ^ e1 := by
                  rw [← pow_add, Nat.add_sub_of_le hy2]
        simpa [e0, e1, hmul] using himg
      · by_cases hx2 : 2 ≤ e0
        · have hs2 : (e0 - 2) + e1 ≤ 2 := by omega
          have himg :=
            inAdmissibleImage_of_relation_mul_const
              (u := u) (c := c1) (r := x0 ^ 2)
              (q := (MvPolynomial.C r * x0 ^ (e0 - 2)) * x1 ^ e1)
              h1 (isQuadratic_C_mul_pow_pow r (e0 - 2) e1 hs2)
          rw [monomial_fin2_eq]
          simp [e0, e1] at himg ⊢
          have hmul :
              x0 ^ 2 * ((MvPolynomial.C r * x0 ^ (e0 - 2)) * x1 ^ e1) =
                (MvPolynomial.C r * x0 ^ e0) * x1 ^ e1 := by
            calc
              x0 ^ 2 * ((MvPolynomial.C r * x0 ^ (e0 - 2)) * x1 ^ e1)
                  = MvPolynomial.C r * (x0 ^ 2 * x0 ^ (e0 - 2)) * x1 ^ e1 := by
                      ring_nf
              _ = (MvPolynomial.C r * x0 ^ e0) * x1 ^ e1 := by
                    rw [← pow_add, Nat.add_sub_of_le hx2]
          simpa [e0, e1, hmul] using himg
        · have hxy : e0 = 1 ∧ e1 = 1 := by omega
          rcases hxy with ⟨hx1, hy1⟩
          simpa [monomial_fin2_eq, e0, e1, hx1, hy1, MvPolynomial.smul_eq_C_mul, mul_assoc] using
            (inAdmissibleImage_smul u r himgX0x1)
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
      · have hsdeg : s.sum (fun _ e => e) ≤ 4 :=
          (MvPolynomial.le_totalDegree (hsub s (by simp))).trans hp
        exact monomialImage s (MvPolynomial.coeff s p) hsdeg
      · intro t ht
        exact hsub t (by simp [ht])
  exact hP (fun s hs => hs)

theorem residual_eq_zero_of_relations_constX0_x0sq_x0x1_x1sq
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    {α : ℝ}
    (hα : α ≠ 0)
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (MvPolynomial.C α : Poly) + x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x0 ^ 2)
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 * x1)
    (h3 : ∑ i : Fin 4, c3 i • u i = x1 ^ 2)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_in_admissible_image
    (B := B) hu hsocp
    (quartic_in_image_of_relations_constX0_x0sq_x0x1_x1sq hα h0 h1 h2 h3 hp.1)

theorem residual_eq_zero_of_relations_constX0_homQuadBasis_det
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    {α : ℝ}
    (hα : α ≠ 0)
    (hu : IsAdmissiblePoint u)
    {c0 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (MvPolynomial.C α : Poly) + x0)
    {c : Fin 3 → Fin 4 → ℝ} {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hc :
      ∀ j : Fin 3,
        ∑ i : Fin 4, c j i • u i = ∑ k : Fin 3, A j k • homQuadBasis k)
    (hdet : A.det ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  rcases exact_relations_of_homQuadBasis_det (u := u) hc hdet with ⟨d, hd⟩
  exact residual_eq_zero_of_relations_constX0_x0sq_x0x1_x1sq
    (B := B) (u := u) hα hu h0 (hd 0) (hd 1) (hd 2) hp hsocp

theorem residual_eq_zero_of_relations_const_homQuadBasis_det
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    {c : Fin 3 → Fin 4 → ℝ} {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hc :
      ∀ j : Fin 3,
        ∑ i : Fin 4, c j i • u i = ∑ k : Fin 3, A j k • homQuadBasis k)
    (hdet : A.det ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  rcases exact_relations_of_homQuadBasis_det (u := u) hc hdet with ⟨d, hd⟩
  exact residual_eq_zero_of_relations_const_x0sq_x0x1_x1sq
    (B := B) (u := u) hu h0 (hd 0) (hd 1) (hd 2) hp hsocp
