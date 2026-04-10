import TernaryQuarticProof.Certificate
import TernaryQuarticProof.RepresentativeMixedAffine

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

end TernaryQuartic
