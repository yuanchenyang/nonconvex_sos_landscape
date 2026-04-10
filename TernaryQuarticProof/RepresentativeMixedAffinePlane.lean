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

end TernaryQuartic
