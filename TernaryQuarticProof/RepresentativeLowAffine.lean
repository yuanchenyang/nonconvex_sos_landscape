import TernaryQuarticProof.QuadraticNormalForm
import TernaryQuarticProof.QuadraticCoordinateForm
import TernaryQuarticProof.AffineSocpTransform
import TernaryQuarticProof.MixedAffineNormalization
import TernaryQuarticProof.RepresentativeTransport
import TernaryQuarticProof.RepresentativeMixedAffine
import TernaryQuarticProof.RepresentativeSpanThree
import TernaryQuarticProof.RepresentativeSurjective

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace TernaryQuartic

open scoped BigOperators

/-- The rank-4 coprime low-affine representative. -/
def coprimeAffineRep : RankFourVec := ![x0, x1, x0 ^ 2, x1 ^ 2]

private theorem monomial_fin2_eq (s : Fin 2 →₀ ℕ) (a : ℝ) :
    MvPolynomial.monomial s a = (MvPolynomial.C a * x0 ^ s 0) * x1 ^ s 1 := by
  simp [x0, x1, MvPolynomial.monomial_eq, mul_assoc]

private theorem relation_map
    (φ : Poly →ₐ[ℝ] Poly)
    {u : RankFourVec} {c : Fin 4 → ℝ} {r : Poly}
    (hc : ∑ i : Fin 4, c i • u i = r) :
    ∑ i : Fin 4, c i • mapVec φ u i = φ r := by
  have hmap := congrArg φ hc
  simpa [mapVec, Fin.sum_univ_four] using hmap

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

theorem inAdmissibleImage_of_relation_mul_low
    {u : RankFourVec} {c : Fin 4 → ℝ} {r q : Poly}
    (hc : ∑ i : Fin 4, c i • u i = r)
    (hq : IsQuadratic q) :
    InAdmissibleImage u (r * q) := by
  refine ⟨relationDirection c q, relationDirection_admissible c hq, ?_⟩
  rw [A_relationDirection, hc]

private theorem relation_linearCombination_low
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

private theorem det_inv_smul_C_det_mul
    {det : ℝ} (hdet : det ≠ 0) (q : Poly) :
    (det⁻¹ : ℝ) • (MvPolynomial.C det * q) = q := by
  have hC : (MvPolynomial.C det⁻¹ : Poly) * MvPolynomial.C det = (1 : Poly) := by
    calc
      (MvPolynomial.C det⁻¹ : Poly) * MvPolynomial.C det = MvPolynomial.C (det⁻¹ * det) := by
        rw [← MvPolynomial.C_mul]
      _ = (1 : Poly) := by
        have hmul : det⁻¹ * det = 1 := by
          field_simp [hdet]
        simp [hmul]
  calc
    (det⁻¹ : ℝ) • (MvPolynomial.C det * q)
        = (MvPolynomial.C det⁻¹ : Poly) * (MvPolynomial.C det * q) := by
            simp [MvPolynomial.smul_eq_C_mul]
    _ = ((MvPolynomial.C det⁻¹ : Poly) * MvPolynomial.C det) * q := by
          ring
    _ = q := by
          rw [hC]
          simp

/-- Linearity of `A` in the right slot. -/
private theorem A_add_right_local (u v w : RankFourVec) :
    A u (v + w) = A u v + A u w := by
  simp [A, Finset.sum_add_distrib, mul_add]

private theorem monomial_image_coprimeAffineRep
    (s : Fin 2 →₀ ℕ) (a : ℝ)
    (hdeg : s.sum (fun _ e => e) ≤ 4)
    (hne : s ≠ m00) :
    InAdmissibleImage coprimeAffineRep (MvPolynomial.monomial s a) := by
  let e0 := s 0
  let e1 := s 1
  have hsum : s.sum (fun _ e => e) = s 0 + s 1 := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
  have hs0 : s 0 + s 1 ≤ 4 := by
    simpa [hsum] using hdeg
  have hs : e0 + e1 ≤ 4 := by
    simpa [e0, e1] using hs0
  by_cases hsmall : e0 + e1 ≤ 3
  · by_cases hx1 : 1 ≤ e0
    · refine ⟨![(MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1, 0, 0, 0], ?_, ?_⟩
      · intro i
        fin_cases i
        · have hs2 : (e0 - 1) + e1 ≤ 2 := by omega
          exact isQuadratic_C_mul_pow_pow a (e0 - 1) e1 hs2
        · simp [IsQuadratic]
        · simp [IsQuadratic]
        · simp [IsQuadratic]
      · rw [monomial_fin2_eq]
        simp [e0, e1]
        calc
          A coprimeAffineRep ![(MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1, 0, 0, 0]
              = x0 * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1) := by
                  simp [A, coprimeAffineRep, Fin.sum_univ_four, x0, x1]
          _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                have hxpow : x0 * x0 ^ (e0 - 1) = x0 ^ e0 := by
                  simpa [Nat.sub_add_cancel hx1] using (pow_succ' x0 (e0 - 1)).symm
                calc
                  x0 * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1)
                      = MvPolynomial.C a * (x0 * x0 ^ (e0 - 1)) * x1 ^ e1 := by
                          ring_nf
                  _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                        simp [hxpow, mul_assoc]
    · have hy1 : 1 ≤ e1 := by
        by_contra hy1
        have hx0 : e0 = 0 := by omega
        have hy0 : e1 = 0 := by omega
        apply hne
        ext i
        fin_cases i <;> simp [m00, e0, e1, hx0, hy0]
      refine ⟨![0, (MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 1), 0, 0], ?_, ?_⟩
      · intro i
        fin_cases i
        · simp [IsQuadratic]
        · have hs2 : e0 + (e1 - 1) ≤ 2 := by omega
          exact isQuadratic_C_mul_pow_pow a e0 (e1 - 1) hs2
        · simp [IsQuadratic]
        · simp [IsQuadratic]
      · rw [monomial_fin2_eq]
        simp [e0, e1]
        calc
          A coprimeAffineRep ![0, (MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 1), 0, 0]
              = x1 * ((MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 1)) := by
                  simp [A, coprimeAffineRep, Fin.sum_univ_four, x0, x1]
          _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                have hypow : x1 * x1 ^ (e1 - 1) = x1 ^ e1 := by
                  simpa [Nat.sub_add_cancel hy1] using (pow_succ' x1 (e1 - 1)).symm
                calc
                  x1 * ((MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 1))
                      = MvPolynomial.C a * x0 ^ e0 * (x1 * x1 ^ (e1 - 1)) := by
                          ring_nf
                  _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                        simp [hypow, mul_assoc]
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
          A coprimeAffineRep ![0, 0, (MvPolynomial.C a * x0 ^ (e0 - 2)) * x1 ^ e1, 0]
              = x0 ^ 2 * ((MvPolynomial.C a * x0 ^ (e0 - 2)) * x1 ^ e1) := by
                  simp [A, coprimeAffineRep, Fin.sum_univ_four, x0, x1]
          _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                calc
                  x0 ^ 2 * ((MvPolynomial.C a * x0 ^ (e0 - 2)) * x1 ^ e1)
                      = MvPolynomial.C a * (x0 ^ 2 * x0 ^ (e0 - 2)) * x1 ^ e1 := by
                          ring_nf
                  _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                        rw [← pow_add, Nat.add_sub_of_le hx2]
    · have hy2 : 2 ≤ e1 := by omega
      refine ⟨![0, 0, 0, (MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 2)], ?_, ?_⟩
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
          A coprimeAffineRep ![0, 0, 0, (MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 2)]
              = x1 ^ 2 * ((MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 2)) := by
                  simp [A, coprimeAffineRep, Fin.sum_univ_four, x0, x1]
          _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                calc
                  x1 ^ 2 * ((MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 2))
                      = MvPolynomial.C a * x0 ^ e0 * (x1 ^ 2 * x1 ^ (e1 - 2)) := by
                          ring_nf
                  _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                        rw [← pow_add, Nat.add_sub_of_le hy2]

theorem quartic_in_image_coprimeAffineRep_of_coeff_m00_zero
    {p : Poly} (hp : IsQuartic p)
    (h00 : MvPolynomial.coeff m00 p = 0) :
    InAdmissibleImage coprimeAffineRep p := by
  classical
  rw [← MvPolynomial.support_sum_monomial_coeff p]
  let P : Finset (Fin 2 →₀ ℕ) → Prop := fun S =>
    (∀ s ∈ S, s ∈ p.support) →
      InAdmissibleImage coprimeAffineRep
        (∑ s ∈ S, MvPolynomial.monomial s (MvPolynomial.coeff s p))
  have hP : P p.support := by
    refine Finset.induction_on p.support ?_ ?_
    · intro hsub
      simpa using inAdmissibleImage_zero coprimeAffineRep
    · intro s ss hsnot ih hsub
      rw [Finset.sum_insert hsnot]
      refine inAdmissibleImage_add coprimeAffineRep ?_ (ih ?_)
      · have hsdeg : s.sum (fun _ e => e) ≤ 4 :=
          (MvPolynomial.le_totalDegree (hsub s (by simp))).trans hp
        have hscoeff : MvPolynomial.coeff s p ≠ 0 :=
          MvPolynomial.mem_support_iff.mp (hsub s (by simp))
        have hsne : s ≠ m00 := by
          intro hs
          apply hscoeff
          simpa [hs] using h00
        exact monomial_image_coprimeAffineRep s (MvPolynomial.coeff s p) hsdeg hsne
      · intro t ht
        exact hsub t (by simp [ht])
  exact hP (fun s hs => hs)

theorem coprimeAffineRep_admissible : IsAdmissiblePoint coprimeAffineRep := by
  intro i
  fin_cases i
  · simp [coprimeAffineRep, x0, x1, IsQuadratic]
  · simp [coprimeAffineRep, x0, x1, IsQuadratic]
  · simp [coprimeAffineRep, x0, x1, IsQuadratic, MvPolynomial.totalDegree_X_pow]
  · simp [coprimeAffineRep, x0, x1, IsQuadratic, MvPolynomial.totalDegree_X_pow]

/-- The constant-class kernel generator for the coprime low-affine representative. -/
def coprimeAffineConstKerBase : RankFourVec := ![-x0, 0, (1 : Poly), 0]

theorem coprimeAffineConstKerBase_inKer :
    InAdmissibleKer coprimeAffineRep coprimeAffineConstKerBase := by
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i
    · simp [coprimeAffineConstKerBase, x0, IsQuadratic]
    · simp [coprimeAffineConstKerBase, IsQuadratic]
    · simp [coprimeAffineConstKerBase, IsQuadratic]
    · simp [coprimeAffineConstKerBase, IsQuadratic]
  · simp [A, coprimeAffineRep, coprimeAffineConstKerBase, Fin.sum_univ_four, x0, x1]
    ring

theorem coprimeAffineConstKer_scaled_inKer (t : ℝ) :
    InAdmissibleKer coprimeAffineRep (t • coprimeAffineConstKerBase) := by
  refine ⟨isAdmissibleDirection_smul t coprimeAffineConstKerBase_inKer.1, ?_⟩
  rw [A_smul_right, coprimeAffineConstKerBase_inKer.2]
  simp

private theorem coeff_m00_sq (q : Poly) :
    MvPolynomial.coeff m00 (q ^ 2) = (MvPolynomial.coeff m00 q) ^ 2 := by
  change MvPolynomial.constantCoeff (q ^ 2) = (MvPolynomial.constantCoeff q) ^ 2
  rw [pow_two, RingHom.map_mul]
  ring

theorem coeff_m00_sigma_coprimeAffineConstKerScaled (t : ℝ) :
    MvPolynomial.coeff m00 (sigma (t • coprimeAffineConstKerBase)) = t ^ 2 := by
  have hx0 :
      MvPolynomial.coeff m00 ((t • (x0 : Poly)) ^ 2) = 0 := by
    rw [coeff_m00_sq]
    simp [m00, x0]
  have h1 :
      MvPolynomial.coeff m00 ((t • (1 : Poly)) ^ 2) = t ^ 2 := by
    rw [coeff_m00_sq]
    simp [m00]
  rw [sigma, Fin.sum_univ_four]
  simp [coprimeAffineConstKerBase, hx0, h1]

theorem residual_eq_zero_coprimeAffineRep
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p coprimeAffineRep) :
    residual p coprimeAffineRep = 0 := by
  rcases hp with ⟨hpquartic, k, qs, hqdeg, hpq⟩
  let s : ℝ := ∑ i : Fin k, (MvPolynomial.coeff m00 (qs i)) ^ 2
  let t : ℝ := Real.sqrt s
  let w : RankFourVec := t • coprimeAffineConstKerBase
  have hsnonneg : 0 ≤ s := by
    dsimp [s]
    positivity
  have hp00 : MvPolynomial.coeff m00 p = s := by
    rw [hpq, MvPolynomial.coeff_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact coeff_m00_sq (qs i)
  have hwker : InAdmissibleKer coprimeAffineRep w := coprimeAffineConstKer_scaled_inKer t
  have hw00 : MvPolynomial.coeff m00 (sigma w) = s := by
    change MvPolynomial.coeff m00 (sigma (t • coprimeAffineConstKerBase)) = s
    calc
      MvPolynomial.coeff m00 (sigma (t • coprimeAffineConstKerBase)) = t ^ 2 := by
        exact coeff_m00_sigma_coprimeAffineConstKerScaled t
      _ = s := by
        dsimp [t]
        rw [Real.sq_sqrt hsnonneg]
  have hquartic_sub : IsQuartic (p - sigma w) := by
    calc
      (p - sigma w).totalDegree ≤ max p.totalDegree (sigma w).totalDegree := by
        exact MvPolynomial.totalDegree_sub _ _
      _ ≤ 4 := by
        exact max_le hpquartic (isQuartic_sigma_of_admissible hwker.1)
  have h00_sub : MvPolynomial.coeff m00 (p - sigma w) = 0 := by
    rw [MvPolynomial.coeff_sub, hp00, hw00]
    ring
  have himg : InAdmissibleImage coprimeAffineRep (p - sigma w) :=
    quartic_in_image_coprimeAffineRep_of_coeff_m00_zero hquartic_sub h00_sub
  refine admissible_image_plus_cone_residual_eq_zero (B := B)
    (u := coprimeAffineRep) (uImg := coprimeAffineRep)
    coprimeAffineRep_admissible hsocp
    (imageOrthogonalResidual_self (B := B) hsocp.1) ?_
  refine ⟨p - sigma w, {w}, himg, ?_, ?_⟩
  · intro w' hw'
    have hw' : w' = w := by simpa using hw'
    subst hw'
    exact hwker
  · simp [w, sub_eq_add_neg]

theorem quartic_in_image_of_relations_x0_x1_x0sq_x1sq_of_coeff_m00_zero
    {u : RankFourVec}
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 ^ 2)
    (h3 : ∑ i : Fin 4, c3 i • u i = x1 ^ 2)
    {p : Poly} (hp : IsQuartic p)
    (h00 : MvPolynomial.coeff m00 p = 0) :
    InAdmissibleImage u p := by
  classical
  let monomialImage : ∀ (s : Fin 2 →₀ ℕ) (a : ℝ),
      s.sum (fun _ e => e) ≤ 4 →
      s ≠ m00 →
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
    by_cases hsmall : e0 + e1 ≤ 3
    · by_cases hx1 : 1 ≤ e0
      · have hxpow : x0 * x0 ^ (e0 - 1) = x0 ^ e0 := by
          simpa [Nat.sub_add_cancel hx1] using (pow_succ' x0 (e0 - 1)).symm
        have hmul :
            x0 * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1)
              = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
          calc
            x0 * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1)
                = MvPolynomial.C a * (x0 * x0 ^ (e0 - 1)) * x1 ^ e1 := by
                    ring_nf
            _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                  simp [hxpow, mul_assoc]
        simpa [monomial_fin2_eq, e0, e1, hmul] using
          (inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c0) (r := x0)
            (q := (MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1)
            h0 (isQuadratic_C_mul_pow_pow a (e0 - 1) e1 (by omega)))
      · have hy1 : 1 ≤ e1 := by
          by_contra hy1
          have hx0 : e0 = 0 := by omega
          have hy0 : e1 = 0 := by omega
          apply hne
          ext i
          fin_cases i <;> simp [m00, e0, e1, hx0, hy0]
        have hypow : x1 * x1 ^ (e1 - 1) = x1 ^ e1 := by
          simpa [Nat.sub_add_cancel hy1] using (pow_succ' x1 (e1 - 1)).symm
        have hmul :
            x1 * ((MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 1))
              = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
          calc
            x1 * ((MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 1))
                = MvPolynomial.C a * x0 ^ e0 * (x1 * x1 ^ (e1 - 1)) := by
                    ring_nf
            _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                  simp [hypow, mul_assoc]
        simpa [monomial_fin2_eq, e0, e1, hmul] using
          (inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c1) (r := x1)
            (q := (MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 1))
            h1 (isQuadratic_C_mul_pow_pow a e0 (e1 - 1) (by omega)))
    · by_cases hx2 : 2 ≤ e0
      · have hmul :
            x0 ^ 2 * ((MvPolynomial.C a * x0 ^ (e0 - 2)) * x1 ^ e1)
              = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
          calc
            x0 ^ 2 * ((MvPolynomial.C a * x0 ^ (e0 - 2)) * x1 ^ e1)
                = MvPolynomial.C a * (x0 ^ 2 * x0 ^ (e0 - 2)) * x1 ^ e1 := by
                    ring_nf
            _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                  rw [← pow_add, Nat.add_sub_of_le hx2]
        simpa [monomial_fin2_eq, e0, e1, hmul] using
          (inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c2) (r := x0 ^ 2)
            (q := (MvPolynomial.C a * x0 ^ (e0 - 2)) * x1 ^ e1)
            h2 (isQuadratic_C_mul_pow_pow a (e0 - 2) e1 (by omega)))
      · have hy2 : 2 ≤ e1 := by omega
        have hmul :
            x1 ^ 2 * ((MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 2))
              = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
          calc
            x1 ^ 2 * ((MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 2))
                = MvPolynomial.C a * x0 ^ e0 * (x1 ^ 2 * x1 ^ (e1 - 2)) := by
                    ring_nf
            _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                  rw [← pow_add, Nat.add_sub_of_le hy2]
        simpa [monomial_fin2_eq, e0, e1, hmul] using
          (inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c3) (r := x1 ^ 2)
            (q := (MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 2))
            h3 (isQuadratic_C_mul_pow_pow a e0 (e1 - 2) (by omega)))
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
        have hscoeff : MvPolynomial.coeff s p ≠ 0 :=
          MvPolynomial.mem_support_iff.mp (hsub s (by simp))
        have hsne : s ≠ m00 := by
          intro hs'
          apply hscoeff
          simpa [hs'] using h00
        exact monomialImage s (MvPolynomial.coeff s p) hsdeg hsne
      · intro t ht
        exact hsub t (by simp [ht])
  exact hP (fun s hs => hs)

private def coprimeAffineConstKer
    (c0 c2 : Fin 4 → ℝ) (t : ℝ) : RankFourVec :=
  relationDirection (-c0) (t • x0) + relationDirection c2 (t • (1 : Poly))

private theorem coprimeAffineConstKer_admissible
    (c0 c2 : Fin 4 → ℝ) (t : ℝ) :
    IsAdmissibleDirection (coprimeAffineConstKer c0 c2 t) := by
  refine isAdmissibleDirection_add
    (relationDirection_admissible (-c0) ((MvPolynomial.totalDegree_smul_le t x0).trans (by simp [x0])))
    (relationDirection_admissible c2 ((MvPolynomial.totalDegree_smul_le t (1 : Poly)).trans (by simp)))

private theorem coprimeAffineConstKer_inKer
    {u : RankFourVec} {c0 c2 : Fin 4 → ℝ} {t : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 ^ 2) :
    InAdmissibleKer u (coprimeAffineConstKer c0 c2 t) := by
  refine ⟨coprimeAffineConstKer_admissible c0 c2 t, ?_⟩
  rw [coprimeAffineConstKer, A_add_right_local, A_relationDirection, A_relationDirection]
  simp [Pi.neg_apply, h0, h2]
  ring_nf

private theorem coeff_m00_sigma_coprimeAffineConstKer
    (c0 c2 : Fin 4 → ℝ) (t : ℝ) :
    MvPolynomial.coeff m00 (sigma (coprimeAffineConstKer c0 c2 t)) =
      (∑ i : Fin 4, (c2 i) ^ 2) * t ^ 2 := by
  have hcoord : ∀ i : Fin 4,
      MvPolynomial.coeff m00 ((coprimeAffineConstKer c0 c2 t i) ^ 2) = ((c2 i) * t) ^ 2 := by
    intro i
    rw [coeff_m00_sq]
    rw [coprimeAffineConstKer]
    simp [relationDirection, m00, x0]
  rw [sigma, Fin.sum_univ_four]
  repeat' rw [MvPolynomial.coeff_add]
  rw [hcoord 0, hcoord 1, hcoord 2, hcoord 3]
  rw [Fin.sum_univ_four]
  ring_nf

theorem residual_eq_zero_of_relations_x0_x1_x0sq_x1sq
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 ^ 2)
    (h3 : ∑ i : Fin 4, c3 i • u i = x1 ^ 2)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  rcases hp with ⟨hpquartic, k, qs, hqdeg, hpq⟩
  let s : ℝ := ∑ i : Fin k, (MvPolynomial.coeff m00 (qs i)) ^ 2
  let alpha : ℝ := ∑ i : Fin 4, (c2 i) ^ 2
  let t : ℝ := Real.sqrt (s / alpha)
  let w : RankFourVec := coprimeAffineConstKer c0 c2 t
  have hsnonneg : 0 ≤ s := by
    dsimp [s]
    positivity
  have hc2_ne : c2 ≠ 0 := by
    intro hc2
    have : (0 : Poly) = x0 ^ 2 := by
      simpa [hc2] using h2
    have hcoeff := congrArg (MvPolynomial.coeff m20) this
    simp [x0, m20, MvPolynomial.coeff_X_pow] at hcoeff
  have halpha_pos : 0 < alpha := sum_sq_pos_of_ne_zero c2 hc2_ne
  have halpha_nonneg : 0 ≤ alpha := le_of_lt halpha_pos
  have hsdiv_nonneg : 0 ≤ s / alpha := by
    exact div_nonneg hsnonneg halpha_nonneg
  have hp00 : MvPolynomial.coeff m00 p = s := by
    rw [hpq, MvPolynomial.coeff_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact coeff_m00_sq (qs i)
  have hwker : InAdmissibleKer u w := by
    dsimp [w]
    exact coprimeAffineConstKer_inKer h0 h2
  have hw00 : MvPolynomial.coeff m00 (sigma w) = s := by
    change MvPolynomial.coeff m00 (sigma (coprimeAffineConstKer c0 c2 t)) = s
    calc
      MvPolynomial.coeff m00 (sigma (coprimeAffineConstKer c0 c2 t)) = alpha * t ^ 2 := by
        exact coeff_m00_sigma_coprimeAffineConstKer c0 c2 t
      _ = alpha * (s / alpha) := by
            dsimp [t]
            rw [Real.sq_sqrt hsdiv_nonneg]
      _ = s := by
            field_simp [alpha, halpha_pos.ne']
  have hquartic_sub : IsQuartic (p - sigma w) := by
    calc
      (p - sigma w).totalDegree ≤ max p.totalDegree (sigma w).totalDegree := by
        exact MvPolynomial.totalDegree_sub _ _
      _ ≤ 4 := by
        exact max_le hpquartic (isQuartic_sigma_of_admissible hwker.1)
  have h00_sub : MvPolynomial.coeff m00 (p - sigma w) = 0 := by
    rw [MvPolynomial.coeff_sub, hp00, hw00]
    ring
  have himg : InAdmissibleImage u (p - sigma w) :=
    quartic_in_image_of_relations_x0_x1_x0sq_x1sq_of_coeff_m00_zero h0 h1 h2 h3 hquartic_sub h00_sub
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

theorem quartic_in_image_of_relations_x0_x1_onePlusAX0sq_x1sq
    {u : RankFourVec}
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {α : ℝ}
    (hα : α ≠ 0)
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
    (h2 : ∑ i : Fin 4, c2 i • u i = (1 : Poly) + α • (x0 ^ 2 : Poly))
    (h3 : ∑ i : Fin 4, c3 i • u i = x1 ^ 2)
    {p : Poly} (hp : IsQuartic p) :
    InAdmissibleImage u p := by
  classical
  let monomialImage : ∀ (s : Fin 2 →₀ ℕ) (r : ℝ),
      s.sum (fun _ e => e) ≤ 4 →
      InAdmissibleImage u (MvPolynomial.monomial s r) := by
    intro s r hdeg
    let e0 := s 0
    let e1 := s 1
    have hsum : s.sum (fun _ e => e) = s 0 + s 1 := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
    have hs0 : s 0 + s 1 ≤ 4 := by
      simpa [hsum] using hdeg
    have hs : e0 + e1 ≤ 4 := by
      simpa [e0, e1] using hs0
    by_cases hsmall : e0 + e1 ≤ 3
    · by_cases hx1 : 1 ≤ e0
      · have hxpow : x0 * x0 ^ (e0 - 1) = x0 ^ e0 := by
          simpa [Nat.sub_add_cancel hx1] using (pow_succ' x0 (e0 - 1)).symm
        have hmul :
            x0 * ((MvPolynomial.C r * x0 ^ (e0 - 1)) * x1 ^ e1)
              = (MvPolynomial.C r * x0 ^ e0) * x1 ^ e1 := by
          calc
            x0 * ((MvPolynomial.C r * x0 ^ (e0 - 1)) * x1 ^ e1)
                = MvPolynomial.C r * (x0 * x0 ^ (e0 - 1)) * x1 ^ e1 := by
                    ring_nf
            _ = (MvPolynomial.C r * x0 ^ e0) * x1 ^ e1 := by
                  simp [hxpow, mul_assoc]
        simpa [monomial_fin2_eq, e0, e1, hmul] using
          (inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c0) (r := x0)
            (q := (MvPolynomial.C r * x0 ^ (e0 - 1)) * x1 ^ e1)
            h0 (isQuadratic_C_mul_pow_pow r (e0 - 1) e1 (by omega)))
      · by_cases hy1 : 1 ≤ e1
        · have hypow : x1 * x1 ^ (e1 - 1) = x1 ^ e1 := by
            simpa [Nat.sub_add_cancel hy1] using (pow_succ' x1 (e1 - 1)).symm
          have hmul :
              x1 * ((MvPolynomial.C r * x0 ^ e0) * x1 ^ (e1 - 1))
                = (MvPolynomial.C r * x0 ^ e0) * x1 ^ e1 := by
            calc
              x1 * ((MvPolynomial.C r * x0 ^ e0) * x1 ^ (e1 - 1))
                  = MvPolynomial.C r * x0 ^ e0 * (x1 * x1 ^ (e1 - 1)) := by
                      ring_nf
              _ = (MvPolynomial.C r * x0 ^ e0) * x1 ^ e1 := by
                    simp [hypow, mul_assoc]
          simpa [monomial_fin2_eq, e0, e1, hmul] using
            (inAdmissibleImage_of_relation_mul_low
              (u := u) (c := c1) (r := x1)
              (q := (MvPolynomial.C r * x0 ^ e0) * x1 ^ (e1 - 1))
              h1 (isQuadratic_C_mul_pow_pow r e0 (e1 - 1) (by omega)))
        · have hx0 : e0 = 0 := by omega
          have hy0 : e1 = 0 := by omega
          rw [monomial_fin2_eq]
          simp [e0, e1, hx0, hy0]
          have himg1 :
              InAdmissibleImage u
                (((1 : Poly) + α • (x0 ^ 2 : Poly)) * ((MvPolynomial.C r * x0 ^ 0) * x1 ^ 0)) := by
            exact inAdmissibleImage_of_relation_mul_low
              (u := u) (c := c2) (r := (1 : Poly) + α • (x0 ^ 2 : Poly))
              (q := (MvPolynomial.C r * x0 ^ 0) * x1 ^ 0)
              h2 (isQuadratic_C_mul_pow_pow r 0 0 (by omega))
          have himg2 :
              InAdmissibleImage u
                (x0 * ((MvPolynomial.C (-α * r) * x0 ^ 1) * x1 ^ 0)) := by
            exact inAdmissibleImage_of_relation_mul_low
              (u := u) (c := c0) (r := x0)
              (q := (MvPolynomial.C (-α * r) * x0 ^ 1) * x1 ^ 0)
              h0 (isQuadratic_C_mul_pow_pow (-α * r) 1 0 (by omega))
          have hEq :
              ((1 : Poly) + α • (x0 ^ 2 : Poly)) * ((MvPolynomial.C r * x0 ^ 0) * x1 ^ 0) +
                  x0 * ((MvPolynomial.C (-α * r) * x0 ^ 1) * x1 ^ 0) =
                (MvPolynomial.C r : Poly) := by
            simp [MvPolynomial.smul_eq_C_mul]
            ring
          rw [← hEq]
          exact inAdmissibleImage_add u himg1 himg2
    · have hfour : e0 + e1 = 4 := by omega
      by_cases hy2 : 2 ≤ e1
      · have hmul :
            x1 ^ 2 * ((MvPolynomial.C r * x0 ^ e0) * x1 ^ (e1 - 2))
              = (MvPolynomial.C r * x0 ^ e0) * x1 ^ e1 := by
          calc
            x1 ^ 2 * ((MvPolynomial.C r * x0 ^ e0) * x1 ^ (e1 - 2))
                = MvPolynomial.C r * x0 ^ e0 * (x1 ^ 2 * x1 ^ (e1 - 2)) := by
                    ring_nf
            _ = MvPolynomial.C r * x0 ^ e0 * x1 ^ e1 := by
                  rw [← pow_add, Nat.add_sub_of_le hy2]
            _ = (MvPolynomial.C r * x0 ^ e0) * x1 ^ e1 := by
                  ring
        have himg :
            InAdmissibleImage u
              (x1 ^ 2 * ((MvPolynomial.C r * x0 ^ e0) * x1 ^ (e1 - 2))) := by
          exact inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c3) (r := x1 ^ 2)
            (q := (MvPolynomial.C r * x0 ^ e0) * x1 ^ (e1 - 2))
            h3 (isQuadratic_C_mul_pow_pow r e0 (e1 - 2) (by omega))
        have himg' :
            InAdmissibleImage u ((MvPolynomial.C r * x0 ^ e0) * x1 ^ e1) := by
          rw [← hmul]
          exact himg
        simpa [monomial_fin2_eq, e0, e1] using himg'
      · have hx4_or_hx3 :
            (e0 = 4 ∧ e1 = 0) ∨ (e0 = 3 ∧ e1 = 1) := by
          omega
        rcases hx4_or_hx3 with ⟨hx4, hy0⟩ | ⟨hx3, hy1⟩
        · rw [monomial_fin2_eq]
          simp [e0, e1, hx4, hy0]
          have himg1 :
              InAdmissibleImage u
                (((1 : Poly) + α • (x0 ^ 2 : Poly)) *
                  ((MvPolynomial.C (r / α) * x0 ^ 2) * x1 ^ 0)) := by
            exact inAdmissibleImage_of_relation_mul_low
              (u := u) (c := c2) (r := (1 : Poly) + α • (x0 ^ 2 : Poly))
              (q := (MvPolynomial.C (r / α) * x0 ^ 2) * x1 ^ 0)
              h2 (isQuadratic_C_mul_pow_pow (r / α) 2 0 (by omega))
          have himg2 :
              InAdmissibleImage u
                (x0 * ((MvPolynomial.C (-(r / α)) * x0 ^ 1) * x1 ^ 0)) := by
            exact inAdmissibleImage_of_relation_mul_low
              (u := u) (c := c0) (r := x0)
              (q := (MvPolynomial.C (-(r / α)) * x0 ^ 1) * x1 ^ 0)
              h0 (isQuadratic_C_mul_pow_pow (-(r / α)) 1 0 (by omega))
          have hEq :
              ((1 : Poly) + α • (x0 ^ 2 : Poly)) * ((MvPolynomial.C (r / α) * x0 ^ 2) * x1 ^ 0) +
                  x0 * ((MvPolynomial.C (-(r / α)) * x0 ^ 1) * x1 ^ 0) =
                (MvPolynomial.C r * x0 ^ 4 : Poly) := by
            have hC :
                (MvPolynomial.C α : Poly) * MvPolynomial.C r * MvPolynomial.C α⁻¹ =
                  MvPolynomial.C r := by
              rw [← MvPolynomial.C_mul, ← MvPolynomial.C_mul]
              congr 1
              field_simp [hα]
            simp [MvPolynomial.smul_eq_C_mul, pow_succ, div_eq_mul_inv]
            ring_nf
            calc
              MvPolynomial.C α * x0 ^ 4 * MvPolynomial.C r * MvPolynomial.C α⁻¹
                  = x0 ^ 4 * ((MvPolynomial.C α : Poly) * MvPolynomial.C r * MvPolynomial.C α⁻¹) := by
                      ring
              _ = x0 ^ 4 * MvPolynomial.C r := by rw [hC]
          rw [← hEq]
          exact inAdmissibleImage_add u himg1 himg2
        · rw [monomial_fin2_eq]
          simp [e0, e1, hx3, hy1]
          have himg1 :
              InAdmissibleImage u
                (((1 : Poly) + α • (x0 ^ 2 : Poly)) *
                  ((MvPolynomial.C (r / α) * x0 ^ 1) * x1 ^ 1)) := by
            exact inAdmissibleImage_of_relation_mul_low
              (u := u) (c := c2) (r := (1 : Poly) + α • (x0 ^ 2 : Poly))
              (q := (MvPolynomial.C (r / α) * x0 ^ 1) * x1 ^ 1)
              h2 (isQuadratic_C_mul_pow_pow (r / α) 1 1 (by omega))
          have himg2 :
              InAdmissibleImage u
                (x1 * ((MvPolynomial.C (-(r / α)) * x0 ^ 1) * x1 ^ 0)) := by
            exact inAdmissibleImage_of_relation_mul_low
              (u := u) (c := c1) (r := x1)
              (q := (MvPolynomial.C (-(r / α)) * x0 ^ 1) * x1 ^ 0)
              h1 (isQuadratic_C_mul_pow_pow (-(r / α)) 1 0 (by omega))
          have hEq :
              ((1 : Poly) + α • (x0 ^ 2 : Poly)) * ((MvPolynomial.C (r / α) * x0 ^ 1) * x1 ^ 1) +
                  x1 * ((MvPolynomial.C (-(r / α)) * x0 ^ 1) * x1 ^ 0) =
                (MvPolynomial.C r * x0 ^ 3 * x1 : Poly) := by
            have hC :
                (MvPolynomial.C α : Poly) * MvPolynomial.C r * MvPolynomial.C α⁻¹ =
                  MvPolynomial.C r := by
              rw [← MvPolynomial.C_mul, ← MvPolynomial.C_mul]
              congr 1
              field_simp [hα]
            simp [MvPolynomial.smul_eq_C_mul, pow_succ, div_eq_mul_inv]
            ring_nf
            calc
              MvPolynomial.C α * x0 ^ 3 * MvPolynomial.C r * MvPolynomial.C α⁻¹ * x1
                  = x0 ^ 3 * ((MvPolynomial.C α : Poly) * MvPolynomial.C r * MvPolynomial.C α⁻¹) * x1 := by
                      ring
              _ = x0 ^ 3 * MvPolynomial.C r * x1 := by rw [hC]
          rw [← hEq]
          exact inAdmissibleImage_add u himg1 himg2
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

theorem residual_eq_zero_of_relations_x0_x1_onePlusAX0sq_x1sq
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    {α : ℝ}
    (hα : α ≠ 0)
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
    (h2 : ∑ i : Fin 4, c2 i • u i = (1 : Poly) + α • (x0 ^ 2 : Poly))
    (h3 : ∑ i : Fin 4, c3 i • u i = x1 ^ 2)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_in_admissible_image
    (B := B) hu hsocp
    (quartic_in_image_of_relations_x0_x1_onePlusAX0sq_x1sq hα h0 h1 h2 h3 hp.1)

theorem residual_eq_zero_of_relations_x0_x1_onePlusX0sq_x1sq
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
    (h2 : ∑ i : Fin 4, c2 i • u i = (1 : Poly) + x0 ^ 2)
    (h3 : ∑ i : Fin 4, c3 i • u i = x1 ^ 2)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_relations_x0_x1_onePlusAX0sq_x1sq
    (α := 1) (by norm_num) hu h0 h1 (by simpa using h2) h3 hp hsocp

theorem residual_eq_zero_of_equiv_relations_x0_x1_onePlusAX0sq_x1sq
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    {α : ℝ}
    (hα : α ≠ 0)
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1)
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = (1 : Poly) + α • (x0 ^ 2 : Poly))
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = x1 ^ 2) :
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
    exact residual_eq_zero_of_relations_x0_x1_onePlusAX0sq_x1sq
      (B := B0) (u := mapVec e.toAlgHom u) hα hu0 h0 h1 h2 h3 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_equiv_relations_x0_x1_onePlusX0sq_x1sq
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
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1)
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = (1 : Poly) + x0 ^ 2)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = x1 ^ 2) :
    residual p u = 0 := by
  exact residual_eq_zero_of_equiv_relations_x0_x1_onePlusAX0sq_x1sq
    (e := e) (heQuad := heQuad) (heQuadSymm := heQuadSymm) (heQuartic := heQuartic)
    (α := 1) (by norm_num) hB hp hu hsocp h0 h1 (by simpa using h2) h3

theorem residual_eq_zero_of_relations_affinePair_onePlusAX0sq_x1sq
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    {α : ℝ}
    (hα : α ≠ 0)
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {r0 r1 : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = affineLinePoly r0 1 0)
    (h1 : ∑ i : Fin 4, c1 i • u i = affineLinePoly r1 0 1)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q2 =
      (1 : Poly) + α • (x0 ^ 2 : Poly))
    (hq3 : affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q3 = x1 ^ 2)
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
  have heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q) := by
    intro q hq
    exact isQuadratic_affineEquiv
      (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
      (by simp) (by simp)
      (by
        intro i
        fin_cases i <;> simp [b, b'])
      (by
        intro i
        fin_cases i <;> simp [b, b']) hq
  have heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q) := by
    intro q hq
    exact isQuadratic_affineEquiv_symm
      (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
      (by simp) (by simp)
      (by
        intro i
        fin_cases i <;> simp [b, b'])
      (by
        intro i
        fin_cases i <;> simp [b, b']) hq
  have heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q) := by
    intro q hq
    exact isQuartic_affineEquiv
      (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
      (by simp) (by simp)
      (by
        intro i
        fin_cases i <;> simp [b, b'])
      (by
        intro i
        fin_cases i <;> simp [b, b']) hq
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  have h0trans : e (affineLinePoly r0 1 0) = x0 := by
    simp [e, b, b', affineLinePoly, affineEquiv, affineHom, affineImage, x0, x1,
      Fin.sum_univ_two]
  have h1trans : e (affineLinePoly r1 0 1) = x1 := by
    simp [e, b, b', affineLinePoly, affineEquiv, affineHom, affineImage, x0, x1,
      Fin.sum_univ_two]
  have h0' :
      ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0 := by
    simpa [e] using (relation_map e.toAlgHom h0).trans h0trans
  have h1' :
      ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1 := by
    simpa [e] using (relation_map e.toAlgHom h1).trans h1trans
  have h2' :
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = (1 : Poly) + α • (x0 ^ 2 : Poly) := by
    simpa [e, b] using (relation_map e.toAlgHom h2).trans hq2
  have h3' :
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = x1 ^ 2 := by
    simpa [e, b] using (relation_map e.toAlgHom h3).trans hq3
  exact residual_eq_zero_of_equiv_relations_x0_x1_onePlusAX0sq_x1sq
    (e := e) (heQuad := fun {_} hq => heQuad hq) (heQuadSymm := fun {_} hq => heQuadSymm hq)
    (heQuartic := fun {_} hq => heQuartic hq)
    hα hB hp hu hsocp h0' h1' h2' h3'

theorem residual_eq_zero_of_relations_affinePair_onePlusX0sq_x1sq
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {r0 r1 : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = affineLinePoly r0 1 0)
    (h1 : ∑ i : Fin 4, c1 i • u i = affineLinePoly r1 0 1)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q2 = (1 : Poly) + x0 ^ 2)
    (hq3 : affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q3 = x1 ^ 2)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_relations_affinePair_onePlusAX0sq_x1sq
    (α := 1) (by norm_num) hu h0 h1 h2 h3 (by simpa using hq2) hq3 hp hsocp

theorem quartic_in_image_of_relations_x0_x1_onePlusAX0sq_x1sqPlane
    {u : RankFourVec}
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {a b c d : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
    (h2 :
      ∑ i : Fin 4, c2 i • u i =
        (1 : Poly) + a • (x0 ^ 2 : Poly) + b • (x1 ^ 2 : Poly))
    (h3 :
      ∑ i : Fin 4, c3 i • u i =
        c • (x0 ^ 2 : Poly) + d • (x1 ^ 2 : Poly))
    (hdet : a * d - b * c ≠ 0)
    {p : Poly} (hp : IsQuartic p) :
    InAdmissibleImage u p := by
  classical
  let det : ℝ := a * d - b * c
  have hdet0 : det ≠ 0 := by
    simpa [det] using hdet
  let cX : Fin 4 → ℝ := fun i => d * c2 i + (-b) * c3 i
  let cY : Fin 4 → ℝ := fun i => (-c) * c2 i + a * c3 i
  have hX :
      ∑ i : Fin 4, cX i • u i = d • (1 : Poly) + det • (x0 ^ 2 : Poly) := by
    calc
      ∑ i : Fin 4, cX i • u i
          = d • ((1 : Poly) + a • (x0 ^ 2 : Poly) + b • (x1 ^ 2 : Poly)) +
              (-b) • (c • (x0 ^ 2 : Poly) + d • (x1 ^ 2 : Poly)) := by
                simpa [cX] using relation_linearCombination_low h2 h3 d (-b)
      _ = (a * d) • (x0 ^ 2 : Poly) - (b * c) • (x0 ^ 2 : Poly) + d • (1 : Poly) := by
            simp [smul_add, smul_smul, add_assoc, add_left_comm, add_comm, mul_comm, sub_eq_add_neg]
            ring_nf
      _ = d • (1 : Poly) + det • (x0 ^ 2 : Poly) := by
            have hxcoef :
                (a * d) • (x0 ^ 2 : Poly) + -((b * c) • (x0 ^ 2 : Poly)) =
                  ((a * d - b * c) : ℝ) • (x0 ^ 2 : Poly) := by
              simp [sub_eq_add_neg, add_smul]
            calc
              (a * d) • (x0 ^ 2 : Poly) - (b * c) • (x0 ^ 2 : Poly) + d • (1 : Poly)
                  = ((a * d - b * c) : ℝ) • (x0 ^ 2 : Poly) + d • (1 : Poly) := by
                      rw [sub_eq_add_neg, hxcoef]
              _ = d • (1 : Poly) + det • (x0 ^ 2 : Poly) := by
                    simp [det, add_comm]
  have hY :
      ∑ i : Fin 4, cY i • u i = (-c) • (1 : Poly) + det • (x1 ^ 2 : Poly) := by
    calc
      ∑ i : Fin 4, cY i • u i
          = (-c) • ((1 : Poly) + a • (x0 ^ 2 : Poly) + b • (x1 ^ 2 : Poly)) +
              a • (c • (x0 ^ 2 : Poly) + d • (x1 ^ 2 : Poly)) := by
                simpa [cY] using relation_linearCombination_low h2 h3 (-c) a
      _ = (a * d) • (x1 ^ 2 : Poly) - (c * b) • (x1 ^ 2 : Poly) - c • (1 : Poly) := by
            simp [smul_add, smul_smul, add_assoc, add_left_comm, add_comm, mul_comm, sub_eq_add_neg]
            ring_nf
      _ = (-c) • (1 : Poly) + det • (x1 ^ 2 : Poly) := by
            have hycoef :
                (a * d) • (x1 ^ 2 : Poly) + -((c * b) • (x1 ^ 2 : Poly)) =
                  ((a * d - c * b) : ℝ) • (x1 ^ 2 : Poly) := by
              simp [sub_eq_add_neg, add_smul]
            calc
              (a * d) • (x1 ^ 2 : Poly) - (c * b) • (x1 ^ 2 : Poly) - c • (1 : Poly)
                  = ((a * d - c * b) : ℝ) • (x1 ^ 2 : Poly) + (-c) • (1 : Poly) := by
                      have hneg : -(c • (1 : Poly)) = (-c) • (1 : Poly) := by
                        simp
                      rw [sub_eq_add_neg, sub_eq_add_neg, hycoef, hneg]
              _ = (-c) • (1 : Poly) + det • (x1 ^ 2 : Poly) := by
                    simp [det, add_comm, mul_comm, sub_eq_add_neg]
  let monomialImage : ∀ (s : Fin 2 →₀ ℕ) (r : ℝ),
      s.sum (fun _ e => e) ≤ 4 →
      InAdmissibleImage u (MvPolynomial.monomial s r) := by
    intro s r hdeg
    let e0 := s 0
    let e1 := s 1
    have hsum : s.sum (fun _ e => e) = s 0 + s 1 := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
    have hs0 : s 0 + s 1 ≤ 4 := by
      simpa [hsum] using hdeg
    have hs : e0 + e1 ≤ 4 := by
      simpa [e0, e1] using hs0
    by_cases hsmall : e0 + e1 ≤ 3
    · by_cases hx1 : 1 ≤ e0
      · have hxpow : x0 * x0 ^ (e0 - 1) = x0 ^ e0 := by
          simpa [Nat.sub_add_cancel hx1] using (pow_succ' x0 (e0 - 1)).symm
        have hmul :
            x0 * ((MvPolynomial.C r * x0 ^ (e0 - 1)) * x1 ^ e1)
              = (MvPolynomial.C r * x0 ^ e0) * x1 ^ e1 := by
          calc
            x0 * ((MvPolynomial.C r * x0 ^ (e0 - 1)) * x1 ^ e1)
                = MvPolynomial.C r * (x0 * x0 ^ (e0 - 1)) * x1 ^ e1 := by
                    ring_nf
            _ = (MvPolynomial.C r * x0 ^ e0) * x1 ^ e1 := by
                  simp [hxpow, mul_assoc]
        simpa [monomial_fin2_eq, e0, e1, hmul] using
          (inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c0) (r := x0)
            (q := (MvPolynomial.C r * x0 ^ (e0 - 1)) * x1 ^ e1)
            h0 (isQuadratic_C_mul_pow_pow r (e0 - 1) e1 (by omega)))
      · by_cases hy1 : 1 ≤ e1
        · have hypow : x1 * x1 ^ (e1 - 1) = x1 ^ e1 := by
            simpa [Nat.sub_add_cancel hy1] using (pow_succ' x1 (e1 - 1)).symm
          have hmul :
              x1 * ((MvPolynomial.C r * x0 ^ e0) * x1 ^ (e1 - 1))
                = (MvPolynomial.C r * x0 ^ e0) * x1 ^ e1 := by
            calc
              x1 * ((MvPolynomial.C r * x0 ^ e0) * x1 ^ (e1 - 1))
                  = MvPolynomial.C r * x0 ^ e0 * (x1 * x1 ^ (e1 - 1)) := by
                      ring_nf
              _ = (MvPolynomial.C r * x0 ^ e0) * x1 ^ e1 := by
                    simp [hypow, mul_assoc]
          simpa [monomial_fin2_eq, e0, e1, hmul] using
            (inAdmissibleImage_of_relation_mul_low
              (u := u) (c := c1) (r := x1)
              (q := (MvPolynomial.C r * x0 ^ e0) * x1 ^ (e1 - 1))
              h1 (isQuadratic_C_mul_pow_pow r e0 (e1 - 1) (by omega)))
        · have hx0 : e0 = 0 := by omega
          have hy0 : e1 = 0 := by omega
          rw [monomial_fin2_eq]
          simp [e0, e1, hx0, hy0]
          have himg2 :
              InAdmissibleImage u
                (((1 : Poly) + a • (x0 ^ 2 : Poly) + b • (x1 ^ 2 : Poly)) *
                  ((MvPolynomial.C r * x0 ^ 0) * x1 ^ 0)) := by
            exact inAdmissibleImage_of_relation_mul_low
              (u := u) (c := c2)
              (r := (1 : Poly) + a • (x0 ^ 2 : Poly) + b • (x1 ^ 2 : Poly))
              (q := (MvPolynomial.C r * x0 ^ 0) * x1 ^ 0)
              h2 (isQuadratic_C_mul_pow_pow r 0 0 (by omega))
          have himg0 :
              InAdmissibleImage u
                (x0 * ((MvPolynomial.C (-a * r) * x0 ^ 1) * x1 ^ 0)) := by
            exact inAdmissibleImage_of_relation_mul_low
              (u := u) (c := c0) (r := x0)
              (q := (MvPolynomial.C (-a * r) * x0 ^ 1) * x1 ^ 0)
              h0 (isQuadratic_C_mul_pow_pow (-a * r) 1 0 (by omega))
          have himg1 :
              InAdmissibleImage u
                (x1 * ((MvPolynomial.C (-b * r) * x0 ^ 0) * x1 ^ 1)) := by
            exact inAdmissibleImage_of_relation_mul_low
              (u := u) (c := c1) (r := x1)
              (q := (MvPolynomial.C (-b * r) * x0 ^ 0) * x1 ^ 1)
              h1 (isQuadratic_C_mul_pow_pow (-b * r) 0 1 (by omega))
          have hEq :
              (((1 : Poly) + a • (x0 ^ 2 : Poly) + b • (x1 ^ 2 : Poly)) *
                  ((MvPolynomial.C r * x0 ^ 0) * x1 ^ 0)) +
                (x0 * ((MvPolynomial.C (-a * r) * x0 ^ 1) * x1 ^ 0) +
                  x1 * ((MvPolynomial.C (-b * r) * x0 ^ 0) * x1 ^ 1)) =
                (MvPolynomial.C r : Poly) := by
            simp [MvPolynomial.smul_eq_C_mul]
            ring
          rw [← hEq]
          exact inAdmissibleImage_add u himg2 (inAdmissibleImage_add u himg0 himg1)
    · have hfour : e0 + e1 = 4 := by omega
      have he0le : e0 ≤ 4 := by omega
      interval_cases hcase : e0
      · have he1 : e1 = 4 := by omega
        rw [monomial_fin2_eq]
        simp [e0, e1, hcase, he1]
        have himgY :
            InAdmissibleImage u
              ((((-c) • (1 : Poly) + det • (x1 ^ 2 : Poly)) *
                ((MvPolynomial.C r * x0 ^ 0) * x1 ^ 2))) := by
          exact inAdmissibleImage_of_relation_mul_low
            (u := u) (c := cY)
            (r := (-c) • (1 : Poly) + det • (x1 ^ 2 : Poly))
            (q := (MvPolynomial.C r * x0 ^ 0) * x1 ^ 2)
            hY (isQuadratic_C_mul_pow_pow r 0 2 (by omega))
        have himg1 :
            InAdmissibleImage u
              (x1 * ((MvPolynomial.C (c * r) * x0 ^ 0) * x1 ^ 1)) := by
          exact inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c1) (r := x1)
            (q := (MvPolynomial.C (c * r) * x0 ^ 0) * x1 ^ 1)
            h1 (isQuadratic_C_mul_pow_pow (c * r) 0 1 (by omega))
        have hEq :
            (((-c) • (1 : Poly) + det • (x1 ^ 2 : Poly)) *
                ((MvPolynomial.C r * x0 ^ 0) * x1 ^ 2)) +
                x1 * ((MvPolynomial.C (c * r) * x0 ^ 0) * x1 ^ 1) =
              (MvPolynomial.C (det * r) * x1 ^ 4 : Poly) := by
          simp [MvPolynomial.smul_eq_C_mul, pow_succ]
          ring
        have himgDet :
            InAdmissibleImage u (MvPolynomial.C (det * r) * x1 ^ 4) := by
          rw [← hEq]
          exact inAdmissibleImage_add u himgY himg1
        have himg :
            InAdmissibleImage u ((det⁻¹ : ℝ) • (MvPolynomial.C (det * r) * x1 ^ 4)) := by
          exact inAdmissibleImage_smul u det⁻¹ himgDet
        have hscale :
            (det⁻¹ : ℝ) • (MvPolynomial.C (det * r) * x1 ^ 4) =
              (MvPolynomial.C r * x1 ^ 4 : Poly) := by
          rw [show (MvPolynomial.C (det * r) : Poly) = MvPolynomial.C det * MvPolynomial.C r by
                rw [← MvPolynomial.C_mul]]
          simpa [mul_assoc] using det_inv_smul_C_det_mul hdet0 (MvPolynomial.C r * x1 ^ 4)
        rwa [hscale] at himg
      · have he1 : e1 = 3 := by omega
        rw [monomial_fin2_eq]
        simp [e0, e1, hcase, he1]
        have himgY :
            InAdmissibleImage u
              ((((-c) • (1 : Poly) + det • (x1 ^ 2 : Poly)) *
                ((MvPolynomial.C r * x0 ^ 1) * x1 ^ 1))) := by
          exact inAdmissibleImage_of_relation_mul_low
            (u := u) (c := cY)
            (r := (-c) • (1 : Poly) + det • (x1 ^ 2 : Poly))
            (q := (MvPolynomial.C r * x0 ^ 1) * x1 ^ 1)
            hY (isQuadratic_C_mul_pow_pow r 1 1 (by omega))
        have himg0 :
            InAdmissibleImage u
              (x0 * ((MvPolynomial.C (c * r) * x0 ^ 0) * x1 ^ 1)) := by
          exact inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c0) (r := x0)
            (q := (MvPolynomial.C (c * r) * x0 ^ 0) * x1 ^ 1)
            h0 (isQuadratic_C_mul_pow_pow (c * r) 0 1 (by omega))
        have hEq :
            (((-c) • (1 : Poly) + det • (x1 ^ 2 : Poly)) *
                ((MvPolynomial.C r * x0 ^ 1) * x1 ^ 1)) +
                x0 * ((MvPolynomial.C (c * r) * x0 ^ 0) * x1 ^ 1) =
              (MvPolynomial.C (det * r) * x0 * x1 ^ 3 : Poly) := by
          simp [MvPolynomial.smul_eq_C_mul, pow_succ]
          ring
        have himgDet :
            InAdmissibleImage u (MvPolynomial.C (det * r) * x0 * x1 ^ 3) := by
          rw [← hEq]
          exact inAdmissibleImage_add u himgY himg0
        have himg :
            InAdmissibleImage u ((det⁻¹ : ℝ) • (MvPolynomial.C (det * r) * x0 * x1 ^ 3)) := by
          exact inAdmissibleImage_smul u det⁻¹ himgDet
        have hscale :
            (det⁻¹ : ℝ) • (MvPolynomial.C (det * r) * x0 * x1 ^ 3) =
              (MvPolynomial.C r * x0 * x1 ^ 3 : Poly) := by
          rw [show (MvPolynomial.C (det * r) : Poly) = MvPolynomial.C det * MvPolynomial.C r by
                rw [← MvPolynomial.C_mul]]
          simpa [mul_assoc] using det_inv_smul_C_det_mul hdet0 (MvPolynomial.C r * (x0 * x1 ^ 3))
        rwa [hscale] at himg
      · have he1 : e1 = 2 := by omega
        rw [monomial_fin2_eq]
        simp [e0, e1, hcase, he1]
        have himgY :
            InAdmissibleImage u
              ((((-c) • (1 : Poly) + det • (x1 ^ 2 : Poly)) *
                ((MvPolynomial.C r * x0 ^ 2) * x1 ^ 0))) := by
          exact inAdmissibleImage_of_relation_mul_low
            (u := u) (c := cY)
            (r := (-c) • (1 : Poly) + det • (x1 ^ 2 : Poly))
            (q := (MvPolynomial.C r * x0 ^ 2) * x1 ^ 0)
            hY (isQuadratic_C_mul_pow_pow r 2 0 (by omega))
        have himg0 :
            InAdmissibleImage u
              (x0 * ((MvPolynomial.C (c * r) * x0 ^ 1) * x1 ^ 0)) := by
          exact inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c0) (r := x0)
            (q := (MvPolynomial.C (c * r) * x0 ^ 1) * x1 ^ 0)
            h0 (isQuadratic_C_mul_pow_pow (c * r) 1 0 (by omega))
        have hEq :
            (((-c) • (1 : Poly) + det • (x1 ^ 2 : Poly)) *
                ((MvPolynomial.C r * x0 ^ 2) * x1 ^ 0)) +
                x0 * ((MvPolynomial.C (c * r) * x0 ^ 1) * x1 ^ 0) =
              (MvPolynomial.C (det * r) * x0 ^ 2 * x1 ^ 2 : Poly) := by
          simp [MvPolynomial.smul_eq_C_mul, pow_succ]
          ring
        have himgDet :
            InAdmissibleImage u (MvPolynomial.C (det * r) * x0 ^ 2 * x1 ^ 2) := by
          rw [← hEq]
          exact inAdmissibleImage_add u himgY himg0
        have himg :
            InAdmissibleImage u ((det⁻¹ : ℝ) • (MvPolynomial.C (det * r) * x0 ^ 2 * x1 ^ 2)) := by
          exact inAdmissibleImage_smul u det⁻¹ himgDet
        have hscale :
            (det⁻¹ : ℝ) • (MvPolynomial.C (det * r) * x0 ^ 2 * x1 ^ 2) =
              (MvPolynomial.C r * x0 ^ 2 * x1 ^ 2 : Poly) := by
          rw [show (MvPolynomial.C (det * r) : Poly) = MvPolynomial.C det * MvPolynomial.C r by
                rw [← MvPolynomial.C_mul]]
          simpa [mul_assoc] using det_inv_smul_C_det_mul hdet0 (MvPolynomial.C r * (x0 ^ 2 * x1 ^ 2))
        rwa [hscale] at himg
      · have he1 : e1 = 1 := by omega
        rw [monomial_fin2_eq]
        simp [e0, e1, hcase, he1]
        have himgX :
            InAdmissibleImage u
              (((d • (1 : Poly) + det • (x0 ^ 2 : Poly)) *
                ((MvPolynomial.C r * x0 ^ 1) * x1 ^ 1))) := by
          exact inAdmissibleImage_of_relation_mul_low
            (u := u) (c := cX)
            (r := d • (1 : Poly) + det • (x0 ^ 2 : Poly))
            (q := (MvPolynomial.C r * x0 ^ 1) * x1 ^ 1)
            hX (isQuadratic_C_mul_pow_pow r 1 1 (by omega))
        have himg0 :
            InAdmissibleImage u
              (x0 * ((MvPolynomial.C (-d * r) * x0 ^ 0) * x1 ^ 1)) := by
          exact inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c0) (r := x0)
            (q := (MvPolynomial.C (-d * r) * x0 ^ 0) * x1 ^ 1)
            h0 (isQuadratic_C_mul_pow_pow (-d * r) 0 1 (by omega))
        have hEq :
            ((d • (1 : Poly) + det • (x0 ^ 2 : Poly)) *
                ((MvPolynomial.C r * x0 ^ 1) * x1 ^ 1)) +
                x0 * ((MvPolynomial.C (-d * r) * x0 ^ 0) * x1 ^ 1) =
              (MvPolynomial.C (det * r) * x0 ^ 3 * x1 : Poly) := by
          simp [MvPolynomial.smul_eq_C_mul, pow_succ]
          ring
        have himgDet :
            InAdmissibleImage u (MvPolynomial.C (det * r) * x0 ^ 3 * x1) := by
          rw [← hEq]
          exact inAdmissibleImage_add u himgX himg0
        have himg :
            InAdmissibleImage u ((det⁻¹ : ℝ) • (MvPolynomial.C (det * r) * x0 ^ 3 * x1)) := by
          exact inAdmissibleImage_smul u det⁻¹ himgDet
        have hscale :
            (det⁻¹ : ℝ) • (MvPolynomial.C (det * r) * x0 ^ 3 * x1) =
              (MvPolynomial.C r * x0 ^ 3 * x1 : Poly) := by
          rw [show (MvPolynomial.C (det * r) : Poly) = MvPolynomial.C det * MvPolynomial.C r by
                rw [← MvPolynomial.C_mul]]
          simpa [mul_assoc] using det_inv_smul_C_det_mul hdet0 (MvPolynomial.C r * (x0 ^ 3 * x1))
        rwa [hscale] at himg
      · have he1 : e1 = 0 := by omega
        rw [monomial_fin2_eq]
        simp [e0, e1, hcase, he1]
        have himgX :
            InAdmissibleImage u
              (((d • (1 : Poly) + det • (x0 ^ 2 : Poly)) *
                ((MvPolynomial.C r * x0 ^ 2) * x1 ^ 0))) := by
          exact inAdmissibleImage_of_relation_mul_low
            (u := u) (c := cX)
            (r := d • (1 : Poly) + det • (x0 ^ 2 : Poly))
            (q := (MvPolynomial.C r * x0 ^ 2) * x1 ^ 0)
            hX (isQuadratic_C_mul_pow_pow r 2 0 (by omega))
        have himg0 :
            InAdmissibleImage u
              (x0 * ((MvPolynomial.C (-d * r) * x0 ^ 1) * x1 ^ 0)) := by
          exact inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c0) (r := x0)
            (q := (MvPolynomial.C (-d * r) * x0 ^ 1) * x1 ^ 0)
            h0 (isQuadratic_C_mul_pow_pow (-d * r) 1 0 (by omega))
        have hEq :
            ((d • (1 : Poly) + det • (x0 ^ 2 : Poly)) *
                ((MvPolynomial.C r * x0 ^ 2) * x1 ^ 0)) +
                x0 * ((MvPolynomial.C (-d * r) * x0 ^ 1) * x1 ^ 0) =
              (MvPolynomial.C (det * r) * x0 ^ 4 : Poly) := by
          simp [MvPolynomial.smul_eq_C_mul, pow_succ]
          ring
        have himgDet :
            InAdmissibleImage u (MvPolynomial.C (det * r) * x0 ^ 4) := by
          rw [← hEq]
          exact inAdmissibleImage_add u himgX himg0
        have himg :
            InAdmissibleImage u ((det⁻¹ : ℝ) • (MvPolynomial.C (det * r) * x0 ^ 4)) := by
          exact inAdmissibleImage_smul u det⁻¹ himgDet
        have hscale :
            (det⁻¹ : ℝ) • (MvPolynomial.C (det * r) * x0 ^ 4) =
              (MvPolynomial.C r * x0 ^ 4 : Poly) := by
          rw [show (MvPolynomial.C (det * r) : Poly) = MvPolynomial.C det * MvPolynomial.C r by
                rw [← MvPolynomial.C_mul]]
          simpa [mul_assoc] using det_inv_smul_C_det_mul hdet0 (MvPolynomial.C r * x0 ^ 4)
        rwa [hscale] at himg
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

theorem residual_eq_zero_of_relations_x0_x1_onePlusAX0sq_x1sqPlane
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {a b c d : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
    (h2 :
      ∑ i : Fin 4, c2 i • u i =
        (1 : Poly) + a • (x0 ^ 2 : Poly) + b • (x1 ^ 2 : Poly))
    (h3 :
      ∑ i : Fin 4, c3 i • u i =
        c • (x0 ^ 2 : Poly) + d • (x1 ^ 2 : Poly))
    (hdet : a * d - b * c ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_in_admissible_image
    (B := B) hu hsocp
    (quartic_in_image_of_relations_x0_x1_onePlusAX0sq_x1sqPlane
      h0 h1 h2 h3 hdet hp.1)

theorem quartic_in_image_of_relations_x0_x1_onePlusX0x1_diffsq
    {u : RankFourVec}
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
    (h2 : ∑ i : Fin 4, c2 i • u i = (1 : Poly) + x0 * x1)
    (h3 : ∑ i : Fin 4, c3 i • u i = x0 ^ 2 - x1 ^ 2)
    {p : Poly} (hp : IsQuartic p) :
    InAdmissibleImage u p := by
  classical
  let monomialImage : ∀ (s : Fin 2 →₀ ℕ) (a : ℝ),
      s.sum (fun _ e => e) ≤ 4 →
      InAdmissibleImage u (MvPolynomial.monomial s a) := by
    intro s a hdeg
    let e0 := s 0
    let e1 := s 1
    have hsum : s.sum (fun _ e => e) = s 0 + s 1 := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
    have hs0 : s 0 + s 1 ≤ 4 := by
      simpa [hsum] using hdeg
    have hs : e0 + e1 ≤ 4 := by
      simpa [e0, e1] using hs0
    by_cases hsmall : e0 + e1 ≤ 3
    · by_cases hx1 : 1 ≤ e0
      · have hxpow : x0 * x0 ^ (e0 - 1) = x0 ^ e0 := by
          simpa [Nat.sub_add_cancel hx1] using (pow_succ' x0 (e0 - 1)).symm
        have hmul :
            x0 * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1)
              = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
          calc
            x0 * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1)
                = MvPolynomial.C a * (x0 * x0 ^ (e0 - 1)) * x1 ^ e1 := by
                    ring_nf
            _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                  simp [hxpow, mul_assoc]
        simpa [monomial_fin2_eq, e0, e1, hmul] using
          (inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c0) (r := x0)
            (q := (MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1)
            h0 (isQuadratic_C_mul_pow_pow a (e0 - 1) e1 (by omega)))
      · by_cases hy1 : 1 ≤ e1
        · have hypow : x1 * x1 ^ (e1 - 1) = x1 ^ e1 := by
            simpa [Nat.sub_add_cancel hy1] using (pow_succ' x1 (e1 - 1)).symm
          have hmul :
              x1 * ((MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 1))
                = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
            calc
              x1 * ((MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 1))
                  = MvPolynomial.C a * x0 ^ e0 * (x1 * x1 ^ (e1 - 1)) := by
                      ring_nf
              _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                    simp [hypow, mul_assoc]
          simpa [monomial_fin2_eq, e0, e1, hmul] using
            (inAdmissibleImage_of_relation_mul_low
              (u := u) (c := c1) (r := x1)
              (q := (MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 1))
              h1 (isQuadratic_C_mul_pow_pow a e0 (e1 - 1) (by omega)))
        · have hx0 : e0 = 0 := by omega
          have hy0 : e1 = 0 := by omega
          rw [monomial_fin2_eq]
          simp [e0, e1, hx0, hy0]
          have himg2 :
              InAdmissibleImage u
                (((1 : Poly) + x0 * x1) * ((MvPolynomial.C a * x0 ^ 0) * x1 ^ 0)) := by
            exact inAdmissibleImage_of_relation_mul_low
              (u := u) (c := c2) (r := (1 : Poly) + x0 * x1)
              (q := (MvPolynomial.C a * x0 ^ 0) * x1 ^ 0)
              h2 (isQuadratic_C_mul_pow_pow a 0 0 (by omega))
          have himg0 :
              InAdmissibleImage u
                (x0 * ((MvPolynomial.C (-a) * x0 ^ 0) * x1 ^ 1)) := by
            exact inAdmissibleImage_of_relation_mul_low
              (u := u) (c := c0) (r := x0)
              (q := (MvPolynomial.C (-a) * x0 ^ 0) * x1 ^ 1)
              h0 (isQuadratic_C_mul_pow_pow (-a) 0 1 (by omega))
          have hEq :
              ((1 : Poly) + x0 * x1) * ((MvPolynomial.C a * x0 ^ 0) * x1 ^ 0) +
                  x0 * ((MvPolynomial.C (-a) * x0 ^ 0) * x1 ^ 1) =
                (MvPolynomial.C a : Poly) := by
            simp
            ring
          rw [← hEq]
          exact inAdmissibleImage_add u himg2 himg0
    · have hfour : e0 + e1 = 4 := by omega
      have he0le : e0 ≤ 4 := by omega
      interval_cases hcase : e0
      · have he1 : e1 = 4 := by omega
        rw [monomial_fin2_eq]
        simp [e0, e1, hcase, he1]
        have himg0 :
            InAdmissibleImage u
              (x0 * ((MvPolynomial.C (-a) * x0 ^ 0) * x1 ^ 1)) := by
          exact inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c0) (r := x0)
            (q := (MvPolynomial.C (-a) * x0 ^ 0) * x1 ^ 1)
            h0 (isQuadratic_C_mul_pow_pow (-a) 0 1 (by omega))
        have himg2 :
            InAdmissibleImage u
              (((1 : Poly) + x0 * x1) * ((MvPolynomial.C a * x0 ^ 1) * x1 ^ 1)) := by
          exact inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c2) (r := (1 : Poly) + x0 * x1)
            (q := (MvPolynomial.C a * x0 ^ 1) * x1 ^ 1)
            h2 (isQuadratic_C_mul_pow_pow a 1 1 (by omega))
        have himg3 :
            InAdmissibleImage u
              ((x0 ^ 2 - x1 ^ 2) * ((MvPolynomial.C (-a) * x0 ^ 0) * x1 ^ 2)) := by
          exact inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c3) (r := x0 ^ 2 - x1 ^ 2)
            (q := (MvPolynomial.C (-a) * x0 ^ 0) * x1 ^ 2)
            h3 (isQuadratic_C_mul_pow_pow (-a) 0 2 (by omega))
        have hEq :
            x0 * ((MvPolynomial.C (-a) * x0 ^ 0) * x1 ^ 1) +
                (((1 : Poly) + x0 * x1) * ((MvPolynomial.C a * x0 ^ 1) * x1 ^ 1) +
                  (x0 ^ 2 - x1 ^ 2) * ((MvPolynomial.C (-a) * x0 ^ 0) * x1 ^ 2)) =
              (MvPolynomial.C a * x0 ^ 0 * x1 ^ 4 : Poly) := by
          simp [pow_succ]
          ring
        have hEq' :
            x0 * ((MvPolynomial.C (-a) * x0 ^ 0) * x1 ^ 1) +
                (((1 : Poly) + x0 * x1) * ((MvPolynomial.C a * x0 ^ 1) * x1 ^ 1) +
                  (x0 ^ 2 - x1 ^ 2) * ((MvPolynomial.C (-a) * x0 ^ 0) * x1 ^ 2)) =
              (MvPolynomial.C a * x1 ^ 4 : Poly) := by
          simpa using hEq
        rw [← hEq']
        exact inAdmissibleImage_add u himg0 (inAdmissibleImage_add u himg2 himg3)
      · have he1 : e1 = 3 := by omega
        rw [monomial_fin2_eq]
        simp [e0, e1, hcase, he1]
        have himg1 :
            InAdmissibleImage u
              (x1 * ((MvPolynomial.C (-a) * x0 ^ 0) * x1 ^ 1)) := by
          exact inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c1) (r := x1)
            (q := (MvPolynomial.C (-a) * x0 ^ 0) * x1 ^ 1)
            h1 (isQuadratic_C_mul_pow_pow (-a) 0 1 (by omega))
        have himg2 :
            InAdmissibleImage u
              (((1 : Poly) + x0 * x1) * ((MvPolynomial.C a * x0 ^ 0) * x1 ^ 2)) := by
          exact inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c2) (r := (1 : Poly) + x0 * x1)
            (q := (MvPolynomial.C a * x0 ^ 0) * x1 ^ 2)
            h2 (isQuadratic_C_mul_pow_pow a 0 2 (by omega))
        have hEq :
            x1 * ((MvPolynomial.C (-a) * x0 ^ 0) * x1 ^ 1) +
                ((1 : Poly) + x0 * x1) * ((MvPolynomial.C a * x0 ^ 0) * x1 ^ 2) =
              (MvPolynomial.C a * x0 ^ 1 * x1 ^ 3 : Poly) := by
          simp [pow_succ]
          ring
        have hEq' :
            x1 * ((MvPolynomial.C (-a) * x0 ^ 0) * x1 ^ 1) +
                ((1 : Poly) + x0 * x1) * ((MvPolynomial.C a * x0 ^ 0) * x1 ^ 2) =
              (MvPolynomial.C a * x0 * x1 ^ 3 : Poly) := by
          simpa using hEq
        rw [← hEq']
        exact inAdmissibleImage_add u himg1 himg2
      · have he1 : e1 = 2 := by omega
        rw [monomial_fin2_eq]
        simp [e0, e1, hcase, he1]
        have himg0 :
            InAdmissibleImage u
              (x0 * ((MvPolynomial.C (-a) * x0 ^ 0) * x1 ^ 1)) := by
          exact inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c0) (r := x0)
            (q := (MvPolynomial.C (-a) * x0 ^ 0) * x1 ^ 1)
            h0 (isQuadratic_C_mul_pow_pow (-a) 0 1 (by omega))
        have himg2 :
            InAdmissibleImage u
              (((1 : Poly) + x0 * x1) * ((MvPolynomial.C a * x0 ^ 1) * x1 ^ 1)) := by
          exact inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c2) (r := (1 : Poly) + x0 * x1)
            (q := (MvPolynomial.C a * x0 ^ 1) * x1 ^ 1)
            h2 (isQuadratic_C_mul_pow_pow a 1 1 (by omega))
        have hEq :
            x0 * ((MvPolynomial.C (-a) * x0 ^ 0) * x1 ^ 1) +
                ((1 : Poly) + x0 * x1) * ((MvPolynomial.C a * x0 ^ 1) * x1 ^ 1) =
              (MvPolynomial.C a * x0 ^ 2 * x1 ^ 2 : Poly) := by
          simp [pow_succ]
          ring
        rw [← hEq]
        exact inAdmissibleImage_add u himg0 himg2
      · have he1 : e1 = 1 := by omega
        rw [monomial_fin2_eq]
        simp [e0, e1, hcase, he1]
        have himg0 :
            InAdmissibleImage u
              (x0 * ((MvPolynomial.C (-a) * x0 ^ 1) * x1 ^ 0)) := by
          exact inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c0) (r := x0)
            (q := (MvPolynomial.C (-a) * x0 ^ 1) * x1 ^ 0)
            h0 (isQuadratic_C_mul_pow_pow (-a) 1 0 (by omega))
        have himg2 :
            InAdmissibleImage u
              (((1 : Poly) + x0 * x1) * ((MvPolynomial.C a * x0 ^ 2) * x1 ^ 0)) := by
          exact inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c2) (r := (1 : Poly) + x0 * x1)
            (q := (MvPolynomial.C a * x0 ^ 2) * x1 ^ 0)
            h2 (isQuadratic_C_mul_pow_pow a 2 0 (by omega))
        have hEq :
            x0 * ((MvPolynomial.C (-a) * x0 ^ 1) * x1 ^ 0) +
                ((1 : Poly) + x0 * x1) * ((MvPolynomial.C a * x0 ^ 2) * x1 ^ 0) =
              (MvPolynomial.C a * x0 ^ 3 * x1 : Poly) := by
          simp [pow_succ]
          ring
        rw [← hEq]
        exact inAdmissibleImage_add u himg0 himg2
      · have he1 : e1 = 0 := by omega
        rw [monomial_fin2_eq]
        simp [e0, e1, hcase, he1]
        have himg0 :
            InAdmissibleImage u
              (x0 * ((MvPolynomial.C (-a) * x0 ^ 0) * x1 ^ 1)) := by
          exact inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c0) (r := x0)
            (q := (MvPolynomial.C (-a) * x0 ^ 0) * x1 ^ 1)
            h0 (isQuadratic_C_mul_pow_pow (-a) 0 1 (by omega))
        have himg2 :
            InAdmissibleImage u
              (((1 : Poly) + x0 * x1) * ((MvPolynomial.C a * x0 ^ 1) * x1 ^ 1)) := by
          exact inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c2) (r := (1 : Poly) + x0 * x1)
            (q := (MvPolynomial.C a * x0 ^ 1) * x1 ^ 1)
            h2 (isQuadratic_C_mul_pow_pow a 1 1 (by omega))
        have himg3 :
            InAdmissibleImage u
              ((x0 ^ 2 - x1 ^ 2) * ((MvPolynomial.C a * x0 ^ 2) * x1 ^ 0)) := by
          exact inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c3) (r := x0 ^ 2 - x1 ^ 2)
            (q := (MvPolynomial.C a * x0 ^ 2) * x1 ^ 0)
            h3 (isQuadratic_C_mul_pow_pow a 2 0 (by omega))
        have hEq :
            x0 * ((MvPolynomial.C (-a) * x0 ^ 0) * x1 ^ 1) +
                (((1 : Poly) + x0 * x1) * ((MvPolynomial.C a * x0 ^ 1) * x1 ^ 1) +
                  (x0 ^ 2 - x1 ^ 2) * ((MvPolynomial.C a * x0 ^ 2) * x1 ^ 0)) =
              (MvPolynomial.C a * x0 ^ 4 * x1 ^ 0 : Poly) := by
          simp [pow_succ]
          ring
        have hEq' :
            x0 * ((MvPolynomial.C (-a) * x0 ^ 0) * x1 ^ 1) +
                (((1 : Poly) + x0 * x1) * ((MvPolynomial.C a * x0 ^ 1) * x1 ^ 1) +
                  (x0 ^ 2 - x1 ^ 2) * ((MvPolynomial.C a * x0 ^ 2) * x1 ^ 0)) =
              (MvPolynomial.C a * x0 ^ 4 : Poly) := by
          simpa using hEq
        rw [← hEq']
        exact inAdmissibleImage_add u himg0 (inAdmissibleImage_add u himg2 himg3)
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

theorem residual_eq_zero_of_relations_x0_x1_onePlusX0x1_diffsq
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
    (h2 : ∑ i : Fin 4, c2 i • u i = (1 : Poly) + x0 * x1)
    (h3 : ∑ i : Fin 4, c3 i • u i = x0 ^ 2 - x1 ^ 2)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_in_admissible_image
    (B := B) hu hsocp
    (quartic_in_image_of_relations_x0_x1_onePlusX0x1_diffsq h0 h1 h2 h3 hp.1)

theorem residual_eq_zero_of_equiv_relations_x0_x1_onePlusX0x1_diffsq
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
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1)
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = (1 : Poly) + x0 * x1)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = x0 ^ 2 - x1 ^ 2) :
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
    exact residual_eq_zero_of_relations_x0_x1_onePlusX0x1_diffsq
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0 h1 h2 h3 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_affinePair_onePlusX0x1_diffsq
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {r0 r1 : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = affineLinePoly r0 1 0)
    (h1 : ∑ i : Fin 4, c1 i • u i = affineLinePoly r1 0 1)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q2 = (1 : Poly) + x0 * x1)
    (hq3 : affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q3 = x0 ^ 2 - x1 ^ 2)
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
  have heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q) := by
    intro q hq
    exact isQuadratic_affineEquiv
      (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
      (by simp) (by simp)
      (by
        intro i
        fin_cases i <;> simp [b, b'])
      (by
        intro i
        fin_cases i <;> simp [b, b']) hq
  have heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q) := by
    intro q hq
    exact isQuadratic_affineEquiv_symm
      (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
      (by simp) (by simp)
      (by
        intro i
        fin_cases i <;> simp [b, b'])
      (by
        intro i
        fin_cases i <;> simp [b, b']) hq
  have heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q) := by
    intro q hq
    exact isQuartic_affineEquiv
      (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
      (by simp) (by simp)
      (by
        intro i
        fin_cases i <;> simp [b, b'])
      (by
        intro i
        fin_cases i <;> simp [b, b']) hq
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  have h0trans : e (affineLinePoly r0 1 0) = x0 := by
    simp [e, b, b', affineLinePoly, affineEquiv, affineHom, affineImage, x0, x1,
      Fin.sum_univ_two]
  have h1trans : e (affineLinePoly r1 0 1) = x1 := by
    simp [e, b, b', affineLinePoly, affineEquiv, affineHom, affineImage, x0, x1,
      Fin.sum_univ_two]
  have h0' :
      ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0 := by
    simpa [e] using (relation_map e.toAlgHom h0).trans h0trans
  have h1' :
      ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1 := by
    simpa [e] using (relation_map e.toAlgHom h1).trans h1trans
  have h2' :
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = (1 : Poly) + x0 * x1 := by
    simpa [e, b] using (relation_map e.toAlgHom h2).trans hq2
  have h3' :
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = x0 ^ 2 - x1 ^ 2 := by
    simpa [e, b] using (relation_map e.toAlgHom h3).trans hq3
  exact residual_eq_zero_of_equiv_relations_x0_x1_onePlusX0x1_diffsq
    (e := e) (heQuad := fun {_} hq => heQuad hq) (heQuadSymm := fun {_} hq => heQuadSymm hq)
    (heQuartic := fun {_} hq => heQuartic hq)
    hB hp hu hsocp h0' h1' h2' h3'

theorem residual_eq_zero_of_relations_x0_x1_x0sq_x1sqPlane
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
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
                simp [c2', det, relation_linearCombination_low, h2, h3]
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
                simp [c3', det, relation_linearCombination_low, h2, h3]
      _ = ((-c / det) * a + (a / det) * c) • (x0 ^ 2 : Poly) +
            ((-c / det) * b + (a / det) * d) • (x1 ^ 2 : Poly) := by
              simp [smul_add, smul_smul, add_smul, add_assoc, add_left_comm, add_comm, mul_comm]
      _ = x1 ^ 2 := by
            rw [hcoeff30, hcoeff31]
            simp
  exact residual_eq_zero_of_relations_x0_x1_x0sq_x1sq
    (B := B) (u := u) hu h0 h1 h2' h3' hp hsocp

theorem residual_eq_zero_of_equiv_relations_x0_x1_x0sq_x1sqPlane
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
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1)
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
    exact residual_eq_zero_of_relations_x0_x1_x0sq_x1sqPlane
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0 h1 h2 h3 hdet hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_linearPair_x0sq_x1sqPlane
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {a b c d : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = linearForm a b)
    (h1 : ∑ i : Fin 4, c1 i • u i = linearForm c d)
    (hdetLin : a * d - b * c ≠ 0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    {r s t w : ℝ}
    (hq2 : linearPairEquiv a b c d hdetLin q2 = r • (x0 ^ 2 : Poly) + s • (x1 ^ 2 : Poly))
    (hq3 : linearPairEquiv a b c d hdetLin q3 = t • (x0 ^ 2 : Poly) + w • (x1 ^ 2 : Poly))
    (hdetPlane : r * w - s * t ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let e : Poly ≃ₐ[ℝ] Poly := linearPairEquiv a b c d hdetLin
  have heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q) := by
    intro q hq
    exact isQuadratic_affineEquiv
      (linearPairMatrix a b c d) (linearPairInvMatrix a b c d) 0 0
      (linearPair_mul_inv a b c d hdetLin) (linearPair_inv_mul a b c d hdetLin)
      (by intro i; simp) (by intro i; simp) hq
  have heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q) := by
    intro q hq
    exact isQuadratic_affineEquiv_symm
      (linearPairMatrix a b c d) (linearPairInvMatrix a b c d) 0 0
      (linearPair_mul_inv a b c d hdetLin) (linearPair_inv_mul a b c d hdetLin)
      (by intro i; simp) (by intro i; simp) hq
  have heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q) := by
    intro q hq
    exact isQuartic_affineEquiv
      (linearPairMatrix a b c d) (linearPairInvMatrix a b c d) 0 0
      (linearPair_mul_inv a b c d hdetLin) (linearPair_inv_mul a b c d hdetLin)
      (by intro i; simp) (by intro i; simp) hq
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  have h0' : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0 := by
    simpa [e, linearPairEquiv] using
      (relation_map e.toAlgHom h0).trans (affineHom_linearPair_left a b c d hdetLin)
  have h1' : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1 := by
    simpa [e, linearPairEquiv] using
      (relation_map e.toAlgHom h1).trans (affineHom_linearPair_right a b c d hdetLin)
  have h2' : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = r • (x0 ^ 2 : Poly) + s • (x1 ^ 2 : Poly) := by
    simpa [e] using (relation_map e.toAlgHom h2).trans hq2
  have h3' : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = t • (x0 ^ 2 : Poly) + w • (x1 ^ 2 : Poly) := by
    simpa [e] using (relation_map e.toAlgHom h3).trans hq3
  exact residual_eq_zero_of_equiv_relations_x0_x1_x0sq_x1sqPlane
    (e := e) (heQuad := fun {_} hq => heQuad hq) (heQuadSymm := fun {_} hq => heQuadSymm hq)
    (heQuartic := fun {_} hq => heQuartic hq)
    hB hp hu hsocp h0' h1' h2' h3' hdetPlane

theorem quartic_in_image_of_relations_x0_x1_x0x1_diffsq_of_coeff_m00_zero
    {u : RankFourVec}
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 * x1)
    (h3 : ∑ i : Fin 4, c3 i • u i = x0 ^ 2 - x1 ^ 2)
    {p : Poly} (hp : IsQuartic p)
    (h00 : MvPolynomial.coeff m00 p = 0) :
    InAdmissibleImage u p := by
  classical
  let monomialImage : ∀ (s : Fin 2 →₀ ℕ) (a : ℝ),
      s.sum (fun _ e => e) ≤ 4 →
      s ≠ m00 →
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
    by_cases hsmall : e0 + e1 ≤ 3
    · by_cases hx1 : 1 ≤ e0
      · have hxpow : x0 * x0 ^ (e0 - 1) = x0 ^ e0 := by
          simpa [Nat.sub_add_cancel hx1] using (pow_succ' x0 (e0 - 1)).symm
        have hmul :
            x0 * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1)
              = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
          calc
            x0 * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1)
                = MvPolynomial.C a * (x0 * x0 ^ (e0 - 1)) * x1 ^ e1 := by
                    ring_nf
            _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                  simp [hxpow, mul_assoc]
        simpa [monomial_fin2_eq, e0, e1, hmul] using
          (inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c0) (r := x0)
            (q := (MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1)
            h0 (isQuadratic_C_mul_pow_pow a (e0 - 1) e1 (by omega)))
      · have hy1 : 1 ≤ e1 := by
          by_contra hy1
          have hx0 : e0 = 0 := by omega
          have hy0 : e1 = 0 := by omega
          apply hne
          ext i
          fin_cases i <;> simp [m00, e0, e1, hx0, hy0]
        have hypow : x1 * x1 ^ (e1 - 1) = x1 ^ e1 := by
          simpa [Nat.sub_add_cancel hy1] using (pow_succ' x1 (e1 - 1)).symm
        have hmul :
            x1 * ((MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 1))
              = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
          calc
            x1 * ((MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 1))
                = MvPolynomial.C a * x0 ^ e0 * (x1 * x1 ^ (e1 - 1)) := by
                    ring_nf
            _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                  simp [hypow, mul_assoc]
        simpa [monomial_fin2_eq, e0, e1, hmul] using
          (inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c1) (r := x1)
            (q := (MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 1))
            h1 (isQuadratic_C_mul_pow_pow a e0 (e1 - 1) (by omega)))
    · have hsEq : e0 + e1 = 4 := by omega
      have he0le : e0 ≤ 4 := by omega
      interval_cases hcase : e0
      · have he1 : e1 = 4 := by omega
        have hs0' : s 0 = 0 := by simpa [e0] using hcase
        have hs1' : s 1 = 4 := by simpa [e1] using he1
        let q3 : Poly := ((-MvPolynomial.C a) * x0 ^ 0) * x1 ^ 2
        let q2 : Poly := (MvPolynomial.C a * x0 ^ 1) * x1 ^ 1
        let p3 : Poly := (x0 ^ 2 - x1 ^ 2) * q3
        let p2 : Poly := (x0 * x1) * q2
        have himg3 : InAdmissibleImage u p3 := by
          dsimp [p3, q3]
          exact inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c3) (r := x0 ^ 2 - x1 ^ 2)
            (q := q3)
            h3 (by simpa [q3, pow_zero, one_mul, mul_assoc] using
              isQuadratic_C_mul_pow_pow (-a) 0 2 (by omega))
        have himg2 : InAdmissibleImage u p2 := by
          dsimp [p2, q2]
          exact inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c2) (r := x0 * x1)
            (q := q2)
            h2 (by simpa [q2, pow_one, mul_assoc] using
              isQuadratic_C_mul_pow_pow a 1 1 (by omega))
        have hsum : p3 + p2 = MvPolynomial.monomial s a := by
          dsimp [p3, p2, q3, q2]
          rw [monomial_fin2_eq]
          simp [hs0', hs1', pow_zero, pow_one]
          ring_nf
        rw [← hsum]
        exact inAdmissibleImage_add u himg3 himg2
      · have he1 : e1 = 3 := by omega
        have hs0' : s 0 = 1 := by simpa [e0] using hcase
        have hs1' : s 1 = 3 := by simpa [e1] using he1
        let q2 : Poly := (MvPolynomial.C a * x0 ^ 0) * x1 ^ 2
        have himg2 : InAdmissibleImage u ((x0 * x1) * q2) := by
          exact inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c2) (r := x0 * x1)
            (q := q2)
            h2 (by simpa [q2, pow_zero, pow_one, mul_assoc] using
              isQuadratic_C_mul_pow_pow a 0 2 (by omega))
        have hmul : (x0 * x1) * q2 = MvPolynomial.monomial s a := by
          dsimp [q2]
          rw [monomial_fin2_eq]
          simp [hs0', hs1', pow_zero, pow_one]
          ring_nf
        rw [← hmul]
        exact himg2
      · have he1 : e1 = 2 := by omega
        have hs0' : s 0 = 2 := by simpa [e0] using hcase
        have hs1' : s 1 = 2 := by simpa [e1] using he1
        let q2 : Poly := (MvPolynomial.C a * x0 ^ 1) * x1 ^ 1
        have himg2 : InAdmissibleImage u ((x0 * x1) * q2) := by
          exact inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c2) (r := x0 * x1)
            (q := q2)
            h2 (by simpa [q2, pow_one, mul_assoc] using
              isQuadratic_C_mul_pow_pow a 1 1 (by omega))
        have hmul : (x0 * x1) * q2 = MvPolynomial.monomial s a := by
          dsimp [q2]
          rw [monomial_fin2_eq]
          simp [hs0', hs1', pow_one]
          ring_nf
        rw [← hmul]
        exact himg2
      · have he1 : e1 = 1 := by omega
        have hs0' : s 0 = 3 := by simpa [e0] using hcase
        have hs1' : s 1 = 1 := by simpa [e1] using he1
        let q2 : Poly := (MvPolynomial.C a * x0 ^ 2) * x1 ^ 0
        have himg2 : InAdmissibleImage u ((x0 * x1) * q2) := by
          exact inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c2) (r := x0 * x1)
            (q := q2)
            h2 (by simpa [q2, pow_zero, pow_one, mul_assoc] using
              isQuadratic_C_mul_pow_pow a 2 0 (by omega))
        have hmul : (x0 * x1) * q2 = MvPolynomial.monomial s a := by
          dsimp [q2]
          rw [monomial_fin2_eq]
          simp [hs0', hs1', pow_zero, pow_one]
          ring_nf
        rw [← hmul]
        exact himg2
      · have he1 : e1 = 0 := by omega
        have hs0' : s 0 = 4 := by simpa [e0] using hcase
        have hs1' : s 1 = 0 := by simpa [e1] using he1
        let q3 : Poly := (MvPolynomial.C a * x0 ^ 2) * x1 ^ 0
        let q2 : Poly := (MvPolynomial.C a * x0 ^ 1) * x1 ^ 1
        let p3 : Poly := (x0 ^ 2 - x1 ^ 2) * q3
        let p2 : Poly := (x0 * x1) * q2
        have himg3 : InAdmissibleImage u p3 := by
          dsimp [p3, q3]
          exact inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c3) (r := x0 ^ 2 - x1 ^ 2)
            (q := q3)
            h3 (by simpa [q3, pow_zero, pow_one, mul_assoc] using
              isQuadratic_C_mul_pow_pow a 2 0 (by omega))
        have himg2 : InAdmissibleImage u p2 := by
          dsimp [p2, q2]
          exact inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c2) (r := x0 * x1)
            (q := q2)
            h2 (by simpa [q2, pow_one, mul_assoc] using
              isQuadratic_C_mul_pow_pow a 1 1 (by omega))
        have hsum : p3 + p2 = MvPolynomial.monomial s a := by
          dsimp [p3, p2, q3, q2]
          rw [monomial_fin2_eq]
          simp [hs0', hs1', pow_zero, pow_one]
          ring_nf
        rw [← hsum]
        exact inAdmissibleImage_add u himg3 himg2
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
        have hscoeff : MvPolynomial.coeff s p ≠ 0 :=
          MvPolynomial.mem_support_iff.mp (hsub s (by simp))
        have hsne : s ≠ m00 := by
          intro hs'
          apply hscoeff
          simpa [hs'] using h00
        exact monomialImage s (MvPolynomial.coeff s p) hsdeg hsne
      · intro t ht
        exact hsub t (by simp [ht])
  exact hP (fun s hs => hs)

private def diffSqAffineConstKer
    (c0 c2 : Fin 4 → ℝ) (t : ℝ) : RankFourVec :=
  relationDirection (-c0) (t • x1) + relationDirection c2 (t • (1 : Poly))

private theorem diffSqAffineConstKer_admissible
    (c0 c2 : Fin 4 → ℝ) (t : ℝ) :
    IsAdmissibleDirection (diffSqAffineConstKer c0 c2 t) := by
  refine isAdmissibleDirection_add
    (relationDirection_admissible (-c0) ((MvPolynomial.totalDegree_smul_le t x1).trans (by simp [x1])))
    (relationDirection_admissible c2 ((MvPolynomial.totalDegree_smul_le t (1 : Poly)).trans (by simp)))

private theorem diffSqAffineConstKer_inKer
    {u : RankFourVec} {c0 c2 : Fin 4 → ℝ} {t : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 * x1) :
    InAdmissibleKer u (diffSqAffineConstKer c0 c2 t) := by
  refine ⟨diffSqAffineConstKer_admissible c0 c2 t, ?_⟩
  rw [diffSqAffineConstKer, A_add_right_local, A_relationDirection, A_relationDirection]
  simp [Pi.neg_apply, h0, h2]

private theorem coeff_m00_sigma_diffSqAffineConstKer
    (c0 c2 : Fin 4 → ℝ) (t : ℝ) :
    MvPolynomial.coeff m00 (sigma (diffSqAffineConstKer c0 c2 t)) =
      (∑ i : Fin 4, (c2 i) ^ 2) * t ^ 2 := by
  have hcoord : ∀ i : Fin 4,
      MvPolynomial.coeff m00 ((diffSqAffineConstKer c0 c2 t i) ^ 2) = ((c2 i) * t) ^ 2 := by
    intro i
    rw [coeff_m00_sq]
    rw [diffSqAffineConstKer]
    simp [relationDirection, m00, x1]
  rw [sigma, Fin.sum_univ_four]
  repeat' rw [MvPolynomial.coeff_add]
  rw [hcoord 0, hcoord 1, hcoord 2, hcoord 3]
  rw [Fin.sum_univ_four]
  ring_nf

theorem residual_eq_zero_of_relations_x0_x1_x0x1_diffsq
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 * x1)
    (h3 : ∑ i : Fin 4, c3 i • u i = x0 ^ 2 - x1 ^ 2)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  rcases hp with ⟨hpquartic, k, qs, hqdeg, hpq⟩
  let s : ℝ := ∑ i : Fin k, (MvPolynomial.coeff m00 (qs i)) ^ 2
  let alpha : ℝ := ∑ i : Fin 4, (c2 i) ^ 2
  let t : ℝ := Real.sqrt (s / alpha)
  let w : RankFourVec := diffSqAffineConstKer c0 c2 t
  have hsnonneg : 0 ≤ s := by
    dsimp [s]
    positivity
  have hc2_ne : c2 ≠ 0 := by
    intro hc2
    have : (0 : Poly) = x0 * x1 := by
      simpa [hc2] using h2
    have hcoeff := congrArg (MvPolynomial.coeff m11) this
    simp [x0, x1, m11] at hcoeff
  have halpha_pos : 0 < alpha := sum_sq_pos_of_ne_zero c2 hc2_ne
  have halpha_nonneg : 0 ≤ alpha := le_of_lt halpha_pos
  have hsdiv_nonneg : 0 ≤ s / alpha := by
    exact div_nonneg hsnonneg halpha_nonneg
  have hp00 : MvPolynomial.coeff m00 p = s := by
    rw [hpq, MvPolynomial.coeff_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact coeff_m00_sq (qs i)
  have hwker : InAdmissibleKer u w := by
    dsimp [w]
    exact diffSqAffineConstKer_inKer h0 h2
  have hw00 : MvPolynomial.coeff m00 (sigma w) = s := by
    change MvPolynomial.coeff m00 (sigma (diffSqAffineConstKer c0 c2 t)) = s
    calc
      MvPolynomial.coeff m00 (sigma (diffSqAffineConstKer c0 c2 t)) = alpha * t ^ 2 := by
        exact coeff_m00_sigma_diffSqAffineConstKer c0 c2 t
      _ = alpha * (s / alpha) := by
            dsimp [t]
            rw [Real.sq_sqrt hsdiv_nonneg]
      _ = s := by
            field_simp [alpha, halpha_pos.ne']
  have hquartic_sub : IsQuartic (p - sigma w) := by
    calc
      (p - sigma w).totalDegree ≤ max p.totalDegree (sigma w).totalDegree := by
        exact MvPolynomial.totalDegree_sub _ _
      _ ≤ 4 := by
        exact max_le hpquartic (isQuartic_sigma_of_admissible hwker.1)
  have h00_sub : MvPolynomial.coeff m00 (p - sigma w) = 0 := by
    rw [MvPolynomial.coeff_sub, hp00, hw00]
    ring
  have himg : InAdmissibleImage u (p - sigma w) :=
    quartic_in_image_of_relations_x0_x1_x0x1_diffsq_of_coeff_m00_zero
      h0 h1 h2 h3 hquartic_sub h00_sub
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

theorem residual_eq_zero_of_relations_x0_x1_x0x1_diffsqPlane
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
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
                simp [c2', det, relation_linearCombination_low, h2, h3]
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
                simp [c3', det, relation_linearCombination_low, h2, h3]
      _ = ((-c / det) * a + (a / det) * c) • (x0 * x1 : Poly) +
            ((-c / det) * b + (a / det) * d) • (x0 ^ 2 - x1 ^ 2) := by
              simp [smul_add, smul_smul, add_smul, add_assoc, add_left_comm, add_comm, mul_comm]
      _ = x0 ^ 2 - x1 ^ 2 := by
            rw [hcoeff30, hcoeff31]
            simp
  exact residual_eq_zero_of_relations_x0_x1_x0x1_diffsq
    (B := B) (u := u) hu h0 h1 h2' h3' hp hsocp

theorem residual_eq_zero_of_equiv_relations_x0_x1_x0x1_diffsqPlane
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
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1)
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
    exact residual_eq_zero_of_relations_x0_x1_x0x1_diffsqPlane
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0 h1 h2 h3 hdet hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_linearPair_x0x1_diffsqPlane
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {a b c d : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = linearForm a b)
    (h1 : ∑ i : Fin 4, c1 i • u i = linearForm c d)
    (hdetLin : a * d - b * c ≠ 0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    {r s t w : ℝ}
    (hq2 :
      linearPairEquiv a b c d hdetLin q2 =
        r • (x0 * x1 : Poly) + s • (x0 ^ 2 - x1 ^ 2))
    (hq3 :
      linearPairEquiv a b c d hdetLin q3 =
        t • (x0 * x1 : Poly) + w • (x0 ^ 2 - x1 ^ 2))
    (hdetPlane : r * w - s * t ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let e : Poly ≃ₐ[ℝ] Poly := linearPairEquiv a b c d hdetLin
  have heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q) := by
    intro q hq
    exact isQuadratic_affineEquiv
      (linearPairMatrix a b c d) (linearPairInvMatrix a b c d) 0 0
      (linearPair_mul_inv a b c d hdetLin) (linearPair_inv_mul a b c d hdetLin)
      (by intro i; simp) (by intro i; simp) hq
  have heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q) := by
    intro q hq
    exact isQuadratic_affineEquiv_symm
      (linearPairMatrix a b c d) (linearPairInvMatrix a b c d) 0 0
      (linearPair_mul_inv a b c d hdetLin) (linearPair_inv_mul a b c d hdetLin)
      (by intro i; simp) (by intro i; simp) hq
  have heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q) := by
    intro q hq
    exact isQuartic_affineEquiv
      (linearPairMatrix a b c d) (linearPairInvMatrix a b c d) 0 0
      (linearPair_mul_inv a b c d hdetLin) (linearPair_inv_mul a b c d hdetLin)
      (by intro i; simp) (by intro i; simp) hq
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  have h0' : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0 := by
    simpa [e, linearPairEquiv] using
      (relation_map e.toAlgHom h0).trans (affineHom_linearPair_left a b c d hdetLin)
  have h1' : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1 := by
    simpa [e, linearPairEquiv] using
      (relation_map e.toAlgHom h1).trans (affineHom_linearPair_right a b c d hdetLin)
  have h2' :
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i =
        r • (x0 * x1 : Poly) + s • (x0 ^ 2 - x1 ^ 2) := by
    simpa [e] using (relation_map e.toAlgHom h2).trans hq2
  have h3' :
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i =
        t • (x0 * x1 : Poly) + w • (x0 ^ 2 - x1 ^ 2) := by
    simpa [e] using (relation_map e.toAlgHom h3).trans hq3
  exact residual_eq_zero_of_equiv_relations_x0_x1_x0x1_diffsqPlane
    (e := e) (heQuad := fun {_} hq => heQuad hq) (heQuadSymm := fun {_} hq => heQuadSymm hq)
    (heQuartic := fun {_} hq => heQuartic hq)
    hB hp hu hsocp h0' h1' h2' h3' hdetPlane

/-- Linear change of variables sending `(x₀,x₁)` to `(x₀+x₁,x₀-x₁)`. -/
private def lowAffineSplitDiagMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 1; 1, -1]

/-- Inverse of `lowAffineSplitDiagMatrix`. -/
private def lowAffineSplitDiagInvMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1 / 2 : ℝ), (1 / 2 : ℝ); (1 / 2 : ℝ), (-1 / 2 : ℝ)]

private theorem lowAffineSplitDiag_mul_inv :
    lowAffineSplitDiagMatrix * lowAffineSplitDiagInvMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowAffineSplitDiagMatrix, lowAffineSplitDiagInvMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals norm_num

private theorem lowAffineSplitDiag_inv_mul :
    lowAffineSplitDiagInvMatrix * lowAffineSplitDiagMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowAffineSplitDiagMatrix, lowAffineSplitDiagInvMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals norm_num

private def lowAffineSplitDiagEquiv : Poly ≃ₐ[ℝ] Poly :=
  affineEquiv lowAffineSplitDiagMatrix lowAffineSplitDiagInvMatrix 0 0
    lowAffineSplitDiag_mul_inv lowAffineSplitDiag_inv_mul
    (by intro i; simp) (by intro i; simp)

@[simp] private theorem affineHom_lowAffineSplitDiag_x0 :
    affineHom lowAffineSplitDiagMatrix 0 x0 = x0 + x1 := by
  simp [x0, x1, affineImage, affineHom_X, lowAffineSplitDiagMatrix, Fin.sum_univ_two]

@[simp] private theorem affineHom_lowAffineSplitDiag_x1 :
    affineHom lowAffineSplitDiagMatrix 0 x1 = x0 - x1 := by
  simp [x0, x1, affineImage, affineHom_X, lowAffineSplitDiagMatrix, Fin.sum_univ_two, sub_eq_add_neg]

private theorem affineHom_lowAffineSplitDiag_x0x1_sumsq
    (a b : ℝ) :
    affineHom lowAffineSplitDiagMatrix 0
        (a • (x0 * x1 : Poly) + b • (x0 ^ 2 + x1 ^ 2 : Poly)) =
      (a + 2 * b) • (x0 ^ 2 : Poly) + (-a + 2 * b) • (x1 ^ 2 : Poly) := by
  simp [affineHom_lowAffineSplitDiag_x0, affineHom_lowAffineSplitDiag_x1,
    sub_eq_add_neg, MvPolynomial.smul_eq_C_mul]
  have htwo : (MvPolynomial.C (2 : ℝ) : Poly) = 2 := by
    change (MvPolynomial.C (2 : ℝ) : Poly) = MvPolynomial.C 2
    rfl
  simp [htwo]
  ring_nf

@[simp] private theorem lowAffineSplitDiagEquiv_apply_x0 :
    lowAffineSplitDiagEquiv x0 = x0 + x1 := by
  exact affineHom_lowAffineSplitDiag_x0

@[simp] private theorem lowAffineSplitDiagEquiv_apply_x1 :
    lowAffineSplitDiagEquiv x1 = x0 - x1 := by
  exact affineHom_lowAffineSplitDiag_x1

@[simp] private theorem lowAffineSplitDiagEquiv_apply_x0x1_sumsq
    (a b : ℝ) :
    lowAffineSplitDiagEquiv (a • (x0 * x1 : Poly) + b • (x0 ^ 2 + x1 ^ 2 : Poly)) =
      (a + 2 * b) • (x0 ^ 2 : Poly) + (-a + 2 * b) • (x1 ^ 2 : Poly) := by
  exact affineHom_lowAffineSplitDiag_x0x1_sumsq a b

theorem residual_eq_zero_of_relations_x0_x1_x0x1_sumsqPlane
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
    {a b c d : ℝ}
    (h2 : ∑ i : Fin 4, c2 i • u i = a • (x0 * x1 : Poly) + b • (x0 ^ 2 + x1 ^ 2))
    (h3 : ∑ i : Fin 4, c3 i • u i = c • (x0 * x1 : Poly) + d • (x0 ^ 2 + x1 ^ 2))
    (hdet : a * d - b * c ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have hB : IsPositiveDefinite B := (Fact.out : B.toQuadraticMap.PosDef)
  let c0' : Fin 4 → ℝ := fun i => (1 / 2 : ℝ) * c0 i + (1 / 2 : ℝ) * c1 i
  let c1' : Fin 4 → ℝ := fun i => (1 / 2 : ℝ) * c0 i + (-1 / 2 : ℝ) * c1 i
  have h0m : ∑ i : Fin 4, c0 i • mapVec lowAffineSplitDiagEquiv.toAlgHom u i = x0 + x1 := by
    calc
      ∑ i : Fin 4, c0 i • mapVec lowAffineSplitDiagEquiv.toAlgHom u i
          = lowAffineSplitDiagEquiv (∑ i : Fin 4, c0 i • u i) := by
              simp [mapVec, map_sum]
      _ = x0 + x1 := by simp [h0]
  have h1m : ∑ i : Fin 4, c1 i • mapVec lowAffineSplitDiagEquiv.toAlgHom u i = x0 - x1 := by
    calc
      ∑ i : Fin 4, c1 i • mapVec lowAffineSplitDiagEquiv.toAlgHom u i
          = lowAffineSplitDiagEquiv (∑ i : Fin 4, c1 i • u i) := by
              simp [mapVec, map_sum]
      _ = x0 - x1 := by simp [h1]
  have h0' : ∑ i : Fin 4, c0' i • mapVec lowAffineSplitDiagEquiv.toAlgHom u i = x0 := by
    calc
      ∑ i : Fin 4, c0' i • mapVec lowAffineSplitDiagEquiv.toAlgHom u i
          = (1 / 2 : ℝ) • (x0 + x1 : Poly) + (1 / 2 : ℝ) • (x0 - x1 : Poly) := by
              simpa [c0'] using
                (relation_linearCombination_low
                  (u := mapVec lowAffineSplitDiagEquiv.toAlgHom u)
                  (c := c0) (d := c1) (r := x0 + x1) (s := x0 - x1)
                  h0m h1m (1 / 2 : ℝ) (1 / 2 : ℝ))
      _ = x0 := by
            ext s
            simp [sub_eq_add_neg, smul_add, MvPolynomial.smul_eq_C_mul]
            ring
  have h1' : ∑ i : Fin 4, c1' i • mapVec lowAffineSplitDiagEquiv.toAlgHom u i = x1 := by
    calc
      ∑ i : Fin 4, c1' i • mapVec lowAffineSplitDiagEquiv.toAlgHom u i
          = (1 / 2 : ℝ) • (x0 + x1 : Poly) + (-1 / 2 : ℝ) • (x0 - x1 : Poly) := by
              simpa [c1'] using
                (relation_linearCombination_low
                  (u := mapVec lowAffineSplitDiagEquiv.toAlgHom u)
                  (c := c0) (d := c1) (r := x0 + x1) (s := x0 - x1)
                  h0m h1m (1 / 2 : ℝ) (-1 / 2 : ℝ))
      _ = x1 := by
            ext s
            simp [sub_eq_add_neg, smul_add, MvPolynomial.smul_eq_C_mul]
            ring
  have h2' :
      ∑ i : Fin 4, c2 i • mapVec lowAffineSplitDiagEquiv.toAlgHom u i =
        (a + 2 * b) • (x0 ^ 2 : Poly) + (-a + 2 * b) • (x1 ^ 2 : Poly) := by
    calc
      ∑ i : Fin 4, c2 i • mapVec lowAffineSplitDiagEquiv.toAlgHom u i
          = lowAffineSplitDiagEquiv (∑ i : Fin 4, c2 i • u i) := by
              simp [mapVec, map_sum]
      _ = lowAffineSplitDiagEquiv (a • (x0 * x1 : Poly) + b • (x0 ^ 2 + x1 ^ 2 : Poly)) := by
            rw [h2]
      _ = (a + 2 * b) • (x0 ^ 2 : Poly) + (-a + 2 * b) • (x1 ^ 2 : Poly) := by
            simpa using lowAffineSplitDiagEquiv_apply_x0x1_sumsq a b
  have h3' :
      ∑ i : Fin 4, c3 i • mapVec lowAffineSplitDiagEquiv.toAlgHom u i =
        (c + 2 * d) • (x0 ^ 2 : Poly) + (-c + 2 * d) • (x1 ^ 2 : Poly) := by
    calc
      ∑ i : Fin 4, c3 i • mapVec lowAffineSplitDiagEquiv.toAlgHom u i
          = lowAffineSplitDiagEquiv (∑ i : Fin 4, c3 i • u i) := by
              simp [mapVec, map_sum]
      _ = lowAffineSplitDiagEquiv (c • (x0 * x1 : Poly) + d • (x0 ^ 2 + x1 ^ 2 : Poly)) := by
            rw [h3]
      _ = (c + 2 * d) • (x0 ^ 2 : Poly) + (-c + 2 * d) • (x1 ^ 2 : Poly) := by
            simpa using lowAffineSplitDiagEquiv_apply_x0x1_sumsq c d
  have hdet' : (a + 2 * b) * (-c + 2 * d) - (-a + 2 * b) * (c + 2 * d) ≠ 0 := by
    intro h
    apply hdet
    nlinarith
  exact residual_eq_zero_of_equiv_relations_x0_x1_x0sq_x1sqPlane
    (e := lowAffineSplitDiagEquiv)
    (heQuad := fun {_} hpq =>
      isQuadratic_affineEquiv lowAffineSplitDiagMatrix lowAffineSplitDiagInvMatrix 0 0
        lowAffineSplitDiag_mul_inv lowAffineSplitDiag_inv_mul
        (by intro i; simp) (by intro i; simp) hpq)
    (heQuadSymm := fun {_} hpq =>
      isQuadratic_affineEquiv_symm lowAffineSplitDiagMatrix lowAffineSplitDiagInvMatrix 0 0
        lowAffineSplitDiag_mul_inv lowAffineSplitDiag_inv_mul
        (by intro i; simp) (by intro i; simp) hpq)
    (heQuartic := fun {_} hpq =>
      isQuartic_affineEquiv lowAffineSplitDiagMatrix lowAffineSplitDiagInvMatrix 0 0
        lowAffineSplitDiag_mul_inv lowAffineSplitDiag_inv_mul
        (by intro i; simp) (by intro i; simp) hpq)
    (B := B) (p := p) (u := u)
    hB hp hu hsocp
    h0' h1' h2' h3' hdet'

theorem residual_eq_zero_of_equiv_relations_x0_x1_x0x1_sumsqPlane
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
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1)
    {a b c d : ℝ}
    (h2 :
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i =
        a • (x0 * x1 : Poly) + b • (x0 ^ 2 + x1 ^ 2))
    (h3 :
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i =
        c • (x0 * x1 : Poly) + d • (x0 ^ 2 + x1 ^ 2))
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
    exact residual_eq_zero_of_relations_x0_x1_x0x1_sumsqPlane
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0 h1 h2 h3 hdet hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_linearPair_x0x1_sumsqPlane
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {a b c d : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = linearForm a b)
    (h1 : ∑ i : Fin 4, c1 i • u i = linearForm c d)
    (hdetLin : a * d - b * c ≠ 0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    {r s t w : ℝ}
    (hq2 :
      linearPairEquiv a b c d hdetLin q2 =
        r • (x0 * x1 : Poly) + s • (x0 ^ 2 + x1 ^ 2))
    (hq3 :
      linearPairEquiv a b c d hdetLin q3 =
        t • (x0 * x1 : Poly) + w • (x0 ^ 2 + x1 ^ 2))
    (hdetPlane : r * w - s * t ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let e : Poly ≃ₐ[ℝ] Poly := linearPairEquiv a b c d hdetLin
  have heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q) := by
    intro q hq
    exact isQuadratic_affineEquiv
      (linearPairMatrix a b c d) (linearPairInvMatrix a b c d) 0 0
      (linearPair_mul_inv a b c d hdetLin) (linearPair_inv_mul a b c d hdetLin)
      (by intro i; simp) (by intro i; simp) hq
  have heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q) := by
    intro q hq
    exact isQuadratic_affineEquiv_symm
      (linearPairMatrix a b c d) (linearPairInvMatrix a b c d) 0 0
      (linearPair_mul_inv a b c d hdetLin) (linearPair_inv_mul a b c d hdetLin)
      (by intro i; simp) (by intro i; simp) hq
  have heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q) := by
    intro q hq
    exact isQuartic_affineEquiv
      (linearPairMatrix a b c d) (linearPairInvMatrix a b c d) 0 0
      (linearPair_mul_inv a b c d hdetLin) (linearPair_inv_mul a b c d hdetLin)
      (by intro i; simp) (by intro i; simp) hq
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  have h0' : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0 := by
    simpa [e, linearPairEquiv] using
      (relation_map e.toAlgHom h0).trans (affineHom_linearPair_left a b c d hdetLin)
  have h1' : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1 := by
    simpa [e, linearPairEquiv] using
      (relation_map e.toAlgHom h1).trans (affineHom_linearPair_right a b c d hdetLin)
  have h2' :
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i =
        r • (x0 * x1 : Poly) + s • (x0 ^ 2 + x1 ^ 2) := by
    simpa [e] using (relation_map e.toAlgHom h2).trans hq2
  have h3' :
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i =
        t • (x0 * x1 : Poly) + w • (x0 ^ 2 + x1 ^ 2) := by
    simpa [e] using (relation_map e.toAlgHom h3).trans hq3
  exact residual_eq_zero_of_equiv_relations_x0_x1_x0x1_sumsqPlane
    (e := e) (heQuad := fun {_} hq => heQuad hq) (heQuadSymm := fun {_} hq => heQuadSymm hq)
    (heQuartic := fun {_} hq => heQuartic hq)
    hB hp hu hsocp h0' h1' h2' h3' hdetPlane

theorem residual_eq_zero_of_relations_x0_x1_onePlusX0x1_sumsqPlane
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
    {a b c d : ℝ}
    (h2 :
      ∑ i : Fin 4, c2 i • u i =
        (1 : Poly) + a • (x0 * x1 : Poly) + b • (x0 ^ 2 + x1 ^ 2 : Poly))
    (h3 :
      ∑ i : Fin 4, c3 i • u i =
        c • (x0 * x1 : Poly) + d • (x0 ^ 2 + x1 ^ 2 : Poly))
    (hdet : a * d - b * c ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have hB : IsPositiveDefinite B := (Fact.out : B.toQuadraticMap.PosDef)
  let c0' : Fin 4 → ℝ := fun i => (1 / 2 : ℝ) * c0 i + (1 / 2 : ℝ) * c1 i
  let c1' : Fin 4 → ℝ := fun i => (1 / 2 : ℝ) * c0 i + (-1 / 2 : ℝ) * c1 i
  have h0m : ∑ i : Fin 4, c0 i • mapVec lowAffineSplitDiagEquiv.toAlgHom u i = x0 + x1 := by
    calc
      ∑ i : Fin 4, c0 i • mapVec lowAffineSplitDiagEquiv.toAlgHom u i
          = lowAffineSplitDiagEquiv (∑ i : Fin 4, c0 i • u i) := by
              simp [mapVec, map_sum]
      _ = x0 + x1 := by simp [h0]
  have h1m : ∑ i : Fin 4, c1 i • mapVec lowAffineSplitDiagEquiv.toAlgHom u i = x0 - x1 := by
    calc
      ∑ i : Fin 4, c1 i • mapVec lowAffineSplitDiagEquiv.toAlgHom u i
          = lowAffineSplitDiagEquiv (∑ i : Fin 4, c1 i • u i) := by
              simp [mapVec, map_sum]
      _ = x0 - x1 := by simp [h1]
  have h0' : ∑ i : Fin 4, c0' i • mapVec lowAffineSplitDiagEquiv.toAlgHom u i = x0 := by
    calc
      ∑ i : Fin 4, c0' i • mapVec lowAffineSplitDiagEquiv.toAlgHom u i
          = (1 / 2 : ℝ) • (x0 + x1 : Poly) + (1 / 2 : ℝ) • (x0 - x1 : Poly) := by
              simpa [c0'] using
                (relation_linearCombination_low
                  (u := mapVec lowAffineSplitDiagEquiv.toAlgHom u)
                  (c := c0) (d := c1) (r := x0 + x1) (s := x0 - x1)
                  h0m h1m (1 / 2 : ℝ) (1 / 2 : ℝ))
      _ = x0 := by
            ext s
            simp [sub_eq_add_neg, smul_add, MvPolynomial.smul_eq_C_mul]
            ring
  have h1' : ∑ i : Fin 4, c1' i • mapVec lowAffineSplitDiagEquiv.toAlgHom u i = x1 := by
    calc
      ∑ i : Fin 4, c1' i • mapVec lowAffineSplitDiagEquiv.toAlgHom u i
          = (1 / 2 : ℝ) • (x0 + x1 : Poly) + (-1 / 2 : ℝ) • (x0 - x1 : Poly) := by
              simpa [c1'] using
                (relation_linearCombination_low
                  (u := mapVec lowAffineSplitDiagEquiv.toAlgHom u)
                  (c := c0) (d := c1) (r := x0 + x1) (s := x0 - x1)
                  h0m h1m (1 / 2 : ℝ) (-1 / 2 : ℝ))
      _ = x1 := by
            ext s
            simp [sub_eq_add_neg, smul_add, MvPolynomial.smul_eq_C_mul]
            ring
  have h2' :
      ∑ i : Fin 4, c2 i • mapVec lowAffineSplitDiagEquiv.toAlgHom u i =
        (1 : Poly) +
          (a + 2 * b) • (x0 ^ 2 : Poly) + (-a + 2 * b) • (x1 ^ 2 : Poly) := by
    calc
      ∑ i : Fin 4, c2 i • mapVec lowAffineSplitDiagEquiv.toAlgHom u i
          = lowAffineSplitDiagEquiv (∑ i : Fin 4, c2 i • u i) := by
              simp [mapVec, map_sum]
      _ = lowAffineSplitDiagEquiv
            ((1 : Poly) + a • (x0 * x1 : Poly) + b • (x0 ^ 2 + x1 ^ 2 : Poly)) := by
            rw [h2]
      _ = (1 : Poly) +
            (a + 2 * b) • (x0 ^ 2 : Poly) + (-a + 2 * b) • (x1 ^ 2 : Poly) := by
            have hsplit :
                ((1 : Poly) + a • (x0 * x1 : Poly) + b • (x0 ^ 2 + x1 ^ 2 : Poly)) =
                  (1 : Poly) + (a • (x0 * x1 : Poly) + b • (x0 ^ 2 + x1 ^ 2 : Poly)) := by
              abel
            rw [hsplit, map_add, lowAffineSplitDiagEquiv_apply_x0x1_sumsq]
            simp [add_assoc]
  have h3' :
      ∑ i : Fin 4, c3 i • mapVec lowAffineSplitDiagEquiv.toAlgHom u i =
        (c + 2 * d) • (x0 ^ 2 : Poly) + (-c + 2 * d) • (x1 ^ 2 : Poly) := by
    calc
      ∑ i : Fin 4, c3 i • mapVec lowAffineSplitDiagEquiv.toAlgHom u i
          = lowAffineSplitDiagEquiv (∑ i : Fin 4, c3 i • u i) := by
              simp [mapVec, map_sum]
      _ = lowAffineSplitDiagEquiv (c • (x0 * x1 : Poly) + d • (x0 ^ 2 + x1 ^ 2 : Poly)) := by
            rw [h3]
      _ = (c + 2 * d) • (x0 ^ 2 : Poly) + (-c + 2 * d) • (x1 ^ 2 : Poly) := by
            simpa using lowAffineSplitDiagEquiv_apply_x0x1_sumsq c d
  have hdet' : (a + 2 * b) * (-c + 2 * d) - (-a + 2 * b) * (c + 2 * d) ≠ 0 := by
    intro h
    apply hdet
    nlinarith
  let B0 : DotForm := dotTransport lowAffineSplitDiagEquiv B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport lowAffineSplitDiagEquiv hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (lowAffineSplitDiagEquiv p) := by
    exact isSOSQuartic_map_of_equiv
      (e := lowAffineSplitDiagEquiv)
      (heQuad := by
        intro q hq
        exact isQuadratic_affineEquiv
          lowAffineSplitDiagMatrix lowAffineSplitDiagInvMatrix 0 0
          lowAffineSplitDiag_mul_inv lowAffineSplitDiag_inv_mul
          (by intro i; simp) (by intro i; simp) hq)
      (heQuartic := by
        intro q hq
        exact isQuartic_affineEquiv
          lowAffineSplitDiagMatrix lowAffineSplitDiagInvMatrix 0 0
          lowAffineSplitDiag_mul_inv lowAffineSplitDiag_inv_mul
          (by intro i; simp) (by intro i; simp) hq)
      hp
  have hu0 : IsAdmissiblePoint (mapVec lowAffineSplitDiagEquiv.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv
      (e := lowAffineSplitDiagEquiv)
      (he := by
        intro q hq
        exact isQuadratic_affineEquiv
          lowAffineSplitDiagMatrix lowAffineSplitDiagInvMatrix 0 0
          lowAffineSplitDiag_mul_inv lowAffineSplitDiag_inv_mul
          (by intro i; simp) (by intro i; simp) hq)
      hu
  have hsocp0 : IsSOCP B0 (lowAffineSplitDiagEquiv p) (mapVec lowAffineSplitDiagEquiv.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv
      (e := lowAffineSplitDiagEquiv)
      (heSymm := by
        intro q hq
        exact isQuadratic_affineEquiv_symm
          lowAffineSplitDiagMatrix lowAffineSplitDiagInvMatrix 0 0
          lowAffineSplitDiag_mul_inv lowAffineSplitDiag_inv_mul
          (by intro i; simp) (by intro i; simp) hq)
      hsocp
  have hres0 :
      residual (lowAffineSplitDiagEquiv p) (mapVec lowAffineSplitDiagEquiv.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_x0_x1_onePlusAX0sq_x1sqPlane
      (B := B0) (u := mapVec lowAffineSplitDiagEquiv.toAlgHom u) hu0
      h0' h1' h2' h3' hdet' hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv lowAffineSplitDiagEquiv p u).mp hres0

/-- The rank-4 common-factor low-affine representative. -/
def commonFactorAffineRep : RankFourVec := ![x0, x1, x0 ^ 2, x0 * x1]

private theorem isQuadratic_x0_mul_x1 : IsQuadratic (x0 * x1 : Poly) := by
  calc
    (x0 * x1).totalDegree ≤ x0.totalDegree + x1.totalDegree := by
      exact MvPolynomial.totalDegree_mul _ _
    _ = 2 := by simp [x0, x1]

private theorem monomial_image_commonFactorAffineRep
    (s : Fin 2 →₀ ℕ) (a : ℝ)
    (hdeg : s.sum (fun _ e => e) ≤ 4)
    (hne0 : s ≠ m00) (hne4 : s ≠ m04) :
    InAdmissibleImage commonFactorAffineRep (MvPolynomial.monomial s a) := by
  let e0 := s 0
  let e1 := s 1
  have hsum : s.sum (fun _ e => e) = s 0 + s 1 := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
  have hs0 : s 0 + s 1 ≤ 4 := by
    simpa [hsum] using hdeg
  have hs : e0 + e1 ≤ 4 := by
    simpa [e0, e1] using hs0
  by_cases hsmall : e0 + e1 ≤ 3
  · by_cases hx1 : 1 ≤ e0
    · refine ⟨![(MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1, 0, 0, 0], ?_, ?_⟩
      · intro i
        fin_cases i
        · have hs2 : (e0 - 1) + e1 ≤ 2 := by omega
          exact isQuadratic_C_mul_pow_pow a (e0 - 1) e1 hs2
        · simp [IsQuadratic]
        · simp [IsQuadratic]
        · simp [IsQuadratic]
      · rw [monomial_fin2_eq]
        simp [e0, e1]
        calc
          A commonFactorAffineRep ![(MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1, 0, 0, 0]
              = x0 * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1) := by
                  simp [A, commonFactorAffineRep, Fin.sum_univ_four, x0, x1]
          _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                have hxpow : x0 * x0 ^ (e0 - 1) = x0 ^ e0 := by
                  simpa [Nat.sub_add_cancel hx1] using (pow_succ' x0 (e0 - 1)).symm
                calc
                  x0 * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1)
                      = MvPolynomial.C a * (x0 * x0 ^ (e0 - 1)) * x1 ^ e1 := by
                          ring_nf
                  _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                        simp [hxpow, mul_assoc]
    · have hy1 : 1 ≤ e1 := by
        by_contra hy1
        have hx0 : e0 = 0 := by omega
        have hy0 : e1 = 0 := by omega
        apply hne0
        ext i
        fin_cases i <;> simp [m00, e0, e1, hx0, hy0]
      refine ⟨![0, (MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 1), 0, 0], ?_, ?_⟩
      · intro i
        fin_cases i
        · simp [IsQuadratic]
        · have hs2 : e0 + (e1 - 1) ≤ 2 := by omega
          exact isQuadratic_C_mul_pow_pow a e0 (e1 - 1) hs2
        · simp [IsQuadratic]
        · simp [IsQuadratic]
      · rw [monomial_fin2_eq]
        simp [e0, e1]
        calc
          A commonFactorAffineRep ![0, (MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 1), 0, 0]
              = x1 * ((MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 1)) := by
                  simp [A, commonFactorAffineRep, Fin.sum_univ_four, x0, x1]
          _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                have hypow : x1 * x1 ^ (e1 - 1) = x1 ^ e1 := by
                  simpa [Nat.sub_add_cancel hy1] using (pow_succ' x1 (e1 - 1)).symm
                calc
                  x1 * ((MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 1))
                      = MvPolynomial.C a * x0 ^ e0 * (x1 * x1 ^ (e1 - 1)) := by
                          ring_nf
                  _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                        simp [hypow, mul_assoc]
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
          A commonFactorAffineRep ![0, 0, 0, (MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1)]
              = (x0 * x1) * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1)) := by
                  simp [A, commonFactorAffineRep, Fin.sum_univ_four, x0, x1]
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
    · have hx2 : 2 ≤ e0 := by
        by_contra hx2
        have hx0 : e0 = 0 := by omega
        have hy4 : e1 = 4 := by omega
        apply hne4
        ext i
        fin_cases i <;> simp [m04, e0, e1, hx0, hy4]
      refine ⟨![0, 0, (MvPolynomial.C a * x0 ^ (e0 - 2)) * x1 ^ e1, 0], ?_, ?_⟩
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
          A commonFactorAffineRep ![0, 0, (MvPolynomial.C a * x0 ^ (e0 - 2)) * x1 ^ e1, 0]
              = x0 ^ 2 * ((MvPolynomial.C a * x0 ^ (e0 - 2)) * x1 ^ e1) := by
                  simp [A, commonFactorAffineRep, Fin.sum_univ_four, x0, x1]
          _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                calc
                  x0 ^ 2 * ((MvPolynomial.C a * x0 ^ (e0 - 2)) * x1 ^ e1)
                      = MvPolynomial.C a * (x0 ^ 2 * x0 ^ (e0 - 2)) * x1 ^ e1 := by
                          ring_nf
                  _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                        rw [← pow_add, Nat.add_sub_of_le hx2]

theorem quartic_in_image_commonFactorAffineRep_of_coeff_m00_m04_zero
    {p : Poly} (hp : IsQuartic p)
    (h00 : MvPolynomial.coeff m00 p = 0)
    (h04 : MvPolynomial.coeff m04 p = 0) :
    InAdmissibleImage commonFactorAffineRep p := by
  classical
  rw [← MvPolynomial.support_sum_monomial_coeff p]
  let P : Finset (Fin 2 →₀ ℕ) → Prop := fun S =>
    (∀ s ∈ S, s ∈ p.support) →
      InAdmissibleImage commonFactorAffineRep
        (∑ s ∈ S, MvPolynomial.monomial s (MvPolynomial.coeff s p))
  have hP : P p.support := by
    refine Finset.induction_on p.support ?_ ?_
    · intro hsub
      simpa using inAdmissibleImage_zero commonFactorAffineRep
    · intro s ss hsnot ih hsub
      rw [Finset.sum_insert hsnot]
      refine inAdmissibleImage_add commonFactorAffineRep ?_ (ih ?_)
      · have hsdeg : s.sum (fun _ e => e) ≤ 4 :=
          (MvPolynomial.le_totalDegree (hsub s (by simp))).trans hp
        have hscoeff : MvPolynomial.coeff s p ≠ 0 :=
          MvPolynomial.mem_support_iff.mp (hsub s (by simp))
        have hsne0 : s ≠ m00 := by
          intro hs
          apply hscoeff
          simpa [hs] using h00
        have hsne4 : s ≠ m04 := by
          intro hs
          apply hscoeff
          simpa [hs] using h04
        exact monomial_image_commonFactorAffineRep s (MvPolynomial.coeff s p) hsdeg hsne0 hsne4
      · intro t ht
        exact hsub t (by simp [ht])
  exact hP (fun s hs => hs)

theorem commonFactorAffineRep_admissible : IsAdmissiblePoint commonFactorAffineRep := by
  intro i
  fin_cases i
  · simp [commonFactorAffineRep, x0, x1, IsQuadratic]
  · simp [commonFactorAffineRep, x0, x1, IsQuadratic]
  · simp [commonFactorAffineRep, x0, x1, IsQuadratic, MvPolynomial.totalDegree_X_pow]
  · simpa [commonFactorAffineRep] using isQuadratic_x0_mul_x1

def commonFactorAffineConstKerBase : RankFourVec := ![-((2 : ℝ) • x1), x0, 0, (1 : Poly)]

def commonFactorAffineQuarticKerBase : RankFourVec := ![-(x1 ^ 2), x0 * x1, 0, 0]

theorem commonFactorAffineConstKerBase_inKer :
    InAdmissibleKer commonFactorAffineRep commonFactorAffineConstKerBase := by
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i
    ·
      calc
        (-((2 : ℝ) • x1) : Poly).totalDegree = ((2 : ℝ) • x1 : Poly).totalDegree := by
          rw [MvPolynomial.totalDegree_neg]
        _ ≤ x1.totalDegree := by
          exact MvPolynomial.totalDegree_smul_le (2 : ℝ) x1
        _ ≤ 2 := by simp [x1]
    · simp [commonFactorAffineConstKerBase, x0, x1, IsQuadratic]
    · simp [commonFactorAffineConstKerBase, IsQuadratic]
    · simp [commonFactorAffineConstKerBase, IsQuadratic]
  · simp [A, commonFactorAffineRep, commonFactorAffineConstKerBase,
      Fin.sum_univ_four, x0, x1]
    rw [two_smul]
    ring

theorem commonFactorAffineQuarticKerBase_inKer :
    InAdmissibleKer commonFactorAffineRep commonFactorAffineQuarticKerBase := by
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i
    · simp [commonFactorAffineQuarticKerBase, x0, x1, IsQuadratic, MvPolynomial.totalDegree_X_pow]
    · simpa [commonFactorAffineQuarticKerBase] using isQuadratic_x0_mul_x1
    · simp [commonFactorAffineQuarticKerBase, IsQuadratic]
    · simp [commonFactorAffineQuarticKerBase, IsQuadratic]
  · simp [A, commonFactorAffineRep, commonFactorAffineQuarticKerBase,
      Fin.sum_univ_four, x0, x1]
    ring

theorem commonFactorAffineConstKer_scaled_inKer (t : ℝ) :
    InAdmissibleKer commonFactorAffineRep (t • commonFactorAffineConstKerBase) := by
  refine ⟨isAdmissibleDirection_smul t commonFactorAffineConstKerBase_inKer.1, ?_⟩
  rw [A_smul_right, commonFactorAffineConstKerBase_inKer.2]
  simp

theorem commonFactorAffineQuarticKer_scaled_inKer (t : ℝ) :
    InAdmissibleKer commonFactorAffineRep (t • commonFactorAffineQuarticKerBase) := by
  refine ⟨isAdmissibleDirection_smul t commonFactorAffineQuarticKerBase_inKer.1, ?_⟩
  rw [A_smul_right, commonFactorAffineQuarticKerBase_inKer.2]
  simp

private theorem coeff_m02_smul_x1_sq (t : ℝ) :
    MvPolynomial.coeff m02 (t • (x1 ^ 2 : Poly)) = t := by
  rw [MvPolynomial.coeff_smul]
  have hx : MvPolynomial.coeff m02 (x1 ^ 2 : Poly) = 1 := by
    simp [x1, m02, MvPolynomial.coeff_X_pow]
  simp [hx]

private theorem coeff_m02_smul_x0_mul_x1 (t : ℝ) :
    MvPolynomial.coeff m02 (t • (x0 * x1 : Poly)) = 0 := by
  rw [MvPolynomial.coeff_smul]
  have hx : MvPolynomial.coeff m02 (x0 * x1 : Poly) = 0 := by
    rw [show (x0 * x1 : Poly) = MvPolynomial.monomial m11 (1 : ℝ) by
      simp [x0, x1, m11, MvPolynomial.monomial_eq]]
    rw [MvPolynomial.coeff_monomial]
    split_ifs with h
    · exfalso
      have := congrArg (fun e : Fin 2 →₀ ℕ => e 0) h.symm
      simp [m11, m02] at this
    · rfl
  simp [hx]

private theorem coeff_m20_smul_x0_sq (t : ℝ) :
    MvPolynomial.coeff m20 (t • (x0 ^ 2 : Poly)) = t := by
  rw [MvPolynomial.coeff_smul]
  have hx : MvPolynomial.coeff m20 (x0 ^ 2 : Poly) = 1 := by
    simp [x0, m20, MvPolynomial.coeff_X_pow]
  simp [hx]

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

theorem coeff_m00_sigma_commonFactorAffineConstKerScaled (t : ℝ) :
    MvPolynomial.coeff m00 (sigma (t • commonFactorAffineConstKerBase)) = t ^ 2 := by
  have hx2 :
      MvPolynomial.coeff m00 ((t • ((2 : ℝ) • x1 : Poly)) ^ 2) = 0 := by
    rw [coeff_m00_sq]
    simp [m00, x1]
  have hx1 :
      MvPolynomial.coeff m00 ((t • x0 : Poly) ^ 2) = 0 := by
    rw [coeff_m00_sq]
    simp [m00, x0]
  have h1 :
      MvPolynomial.coeff m00 ((t • (1 : Poly)) ^ 2) = t ^ 2 := by
    rw [coeff_m00_sq]
    simp [m00]
  rw [sigma, Fin.sum_univ_four]
  simp [commonFactorAffineConstKerBase, hx2, hx1, h1, smul_neg]

theorem coeff_m04_sigma_commonFactorAffineConstKerScaled (t : ℝ) :
    MvPolynomial.coeff m04 (sigma (t • commonFactorAffineConstKerBase)) = 0 := by
  have hx2quad : IsQuadratic ((t • ((2 : ℝ) • x1 : Poly)) : Poly) := by
    calc
      ((t • ((2 : ℝ) • x1 : Poly)) : Poly).totalDegree ≤ (((2 : ℝ) • x1 : Poly)).totalDegree := by
        exact MvPolynomial.totalDegree_smul_le t (((2 : ℝ) • x1 : Poly))
      _ ≤ x1.totalDegree := by
        exact MvPolynomial.totalDegree_smul_le (2 : ℝ) x1
      _ ≤ 2 := by simp [x1]
  have hx2 :
      MvPolynomial.coeff m04 ((t • ((2 : ℝ) • x1 : Poly)) ^ 2) = 0 := by
    rw [coeff_m04_sq_of_quadratic_eq _ hx2quad]
    rw [MvPolynomial.coeff_smul]
    have h02 : MvPolynomial.coeff m02 (x1 : Poly) = 0 := by
      simp [m02, x1]
    simp [h02]
  have hx1quad : IsQuadratic ((t • x0 : Poly) : Poly) := by
    calc
      ((t • x0 : Poly) : Poly).totalDegree ≤ x0.totalDegree := by
        exact MvPolynomial.totalDegree_smul_le t x0
      _ ≤ 2 := by simp [x0]
  have hx1 :
      MvPolynomial.coeff m04 ((t • x0 : Poly) ^ 2) = 0 := by
    rw [coeff_m04_sq_of_quadratic_eq _ hx1quad]
    rw [MvPolynomial.coeff_smul]
    have h02 : MvPolynomial.coeff m02 (x0 : Poly) = 0 := by
      simp [m02, x0]
    simp [h02]
  have h1 :
      MvPolynomial.coeff m04 ((t • (1 : Poly)) ^ 2) = 0 := by
    have hC : (t • (1 : Poly) : Poly) = MvPolynomial.C t := by
      ext s
      rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_C]
      by_cases hs : s = 0
      · subst hs
        simp
      · have hs0 : (0 : Fin 2 →₀ ℕ) ≠ s := by simpa [eq_comm] using hs
        have h1coeff : MvPolynomial.coeff s (1 : Poly) = 0 := by
          rw [show (1 : Poly) = MvPolynomial.C (1 : ℝ) by simp, MvPolynomial.coeff_C]
          split_ifs with h
          · exfalso
            exact hs h.symm
          · rfl
        simp [h1coeff, hs0]
    rw [hC]
    rw [show ((MvPolynomial.C t : Poly) ^ 2) = MvPolynomial.C (t ^ 2) by simp [pow_two]]
    rw [MvPolynomial.coeff_C]
    split_ifs with h
    · exfalso
      have := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h.symm
      simp [m04] at this
    · rfl
  rw [sigma, Fin.sum_univ_four]
  simp [commonFactorAffineConstKerBase, hx2, hx1, h1, smul_neg]

theorem coeff_m00_sigma_commonFactorAffineQuarticKerScaled (t : ℝ) :
    MvPolynomial.coeff m00 (sigma (t • commonFactorAffineQuarticKerBase)) = 0 := by
  have hx1 :
      MvPolynomial.coeff m00 ((t • (x1 ^ 2 : Poly)) ^ 2) = 0 := by
    rw [coeff_m00_sq, MvPolynomial.coeff_smul]
    have h00 : MvPolynomial.coeff m00 (x1 ^ 2 : Poly) = 0 := by
      rw [show (x1 ^ 2 : Poly) = MvPolynomial.monomial m02 (1 : ℝ) by
        simp [x1, m02, MvPolynomial.monomial_eq]]
      rw [MvPolynomial.coeff_monomial]
      split_ifs with h
      · exfalso
        have := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h.symm
        simp [m00, m02] at this
      · rfl
    simp [h00]
  have hxy :
      MvPolynomial.coeff m00 ((t • (x0 * x1 : Poly)) ^ 2) = 0 := by
    rw [coeff_m00_sq, MvPolynomial.coeff_smul]
    have h00 : MvPolynomial.coeff m00 (x0 * x1 : Poly) = 0 := by
      rw [show (x0 * x1 : Poly) = MvPolynomial.monomial m11 (1 : ℝ) by
        simp [x0, x1, m11, MvPolynomial.monomial_eq]]
      rw [MvPolynomial.coeff_monomial]
      split_ifs with h
      · exfalso
        have := congrArg (fun e : Fin 2 →₀ ℕ => e 0) h.symm
        simp [m00, m11] at this
      · rfl
    simp [h00]
  rw [sigma, Fin.sum_univ_four]
  simp [commonFactorAffineQuarticKerBase, hx1, hxy]

theorem coeff_m04_sigma_commonFactorAffineQuarticKerScaled (t : ℝ) :
    MvPolynomial.coeff m04 (sigma (t • commonFactorAffineQuarticKerBase)) = t ^ 2 := by
  have hx1 :
      MvPolynomial.coeff m04 ((t • (x1 ^ 2 : Poly)) ^ 2) = t ^ 2 := by
    rw [coeff_m04_sq_of_quadratic_eq _ (by
      exact (MvPolynomial.totalDegree_smul_le t (x1 ^ 2 : Poly)).trans <|
        by simp [x1])]
    rw [coeff_m02_smul_x1_sq]
  have hxy :
      MvPolynomial.coeff m04 ((t • (x0 * x1 : Poly)) ^ 2) = 0 := by
    rw [coeff_m04_sq_of_quadratic_eq _ ((MvPolynomial.totalDegree_smul_le t (x0 * x1 : Poly)).trans
      isQuadratic_x0_mul_x1)]
    rw [coeff_m02_smul_x0_mul_x1]
    ring
  rw [sigma, Fin.sum_univ_four]
  simp [commonFactorAffineQuarticKerBase, hx1, hxy]

theorem residual_eq_zero_commonFactorAffineRep
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p commonFactorAffineRep) :
    residual p commonFactorAffineRep = 0 := by
  rcases hp with ⟨hpquartic, k, qs, hqdeg, hpq⟩
  let s0 : ℝ := ∑ i : Fin k, (MvPolynomial.coeff m00 (qs i)) ^ 2
  let s4 : ℝ := ∑ i : Fin k, (MvPolynomial.coeff m02 (qs i)) ^ 2
  let t0 : ℝ := Real.sqrt s0
  let t4 : ℝ := Real.sqrt s4
  let w0 : RankFourVec := t0 • commonFactorAffineConstKerBase
  let w4 : RankFourVec := t4 • commonFactorAffineQuarticKerBase
  have hs0_nonneg : 0 ≤ s0 := by
    dsimp [s0]
    positivity
  have hs4_nonneg : 0 ≤ s4 := by
    dsimp [s4]
    positivity
  have hp00 : MvPolynomial.coeff m00 p = s0 := by
    rw [hpq, MvPolynomial.coeff_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact coeff_m00_sq (qs i)
  have hp04 : MvPolynomial.coeff m04 p = s4 := by
    rw [hpq, MvPolynomial.coeff_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact coeff_m04_sq_of_quadratic_eq (qs i) (hqdeg i)
  have hw0ker : InAdmissibleKer commonFactorAffineRep w0 :=
    commonFactorAffineConstKer_scaled_inKer t0
  have hw4ker : InAdmissibleKer commonFactorAffineRep w4 :=
    commonFactorAffineQuarticKer_scaled_inKer t4
  have hw00 : MvPolynomial.coeff m00 (sigma w0) = s0 := by
    change MvPolynomial.coeff m00 (sigma (t0 • commonFactorAffineConstKerBase)) = s0
    rw [coeff_m00_sigma_commonFactorAffineConstKerScaled]
    dsimp [t0]
    rw [Real.sq_sqrt hs0_nonneg]
  have hw04 : MvPolynomial.coeff m04 (sigma w4) = s4 := by
    change MvPolynomial.coeff m04 (sigma (t4 • commonFactorAffineQuarticKerBase)) = s4
    rw [coeff_m04_sigma_commonFactorAffineQuarticKerScaled]
    dsimp [t4]
    rw [Real.sq_sqrt hs4_nonneg]
  have hquartic_sub : IsQuartic (p - sigma w0 - sigma w4) := by
    calc
      (p - sigma w0 - sigma w4).totalDegree ≤ max (p - sigma w0).totalDegree (sigma w4).totalDegree := by
        exact MvPolynomial.totalDegree_sub _ _
      _ ≤ 4 := by
        apply max_le
        · calc
            (p - sigma w0).totalDegree ≤ max p.totalDegree (sigma w0).totalDegree := by
              exact MvPolynomial.totalDegree_sub _ _
            _ ≤ 4 := by
              exact max_le hpquartic (isQuartic_sigma_of_admissible hw0ker.1)
        · exact isQuartic_sigma_of_admissible hw4ker.1
  have h00_sub : MvPolynomial.coeff m00 (p - sigma w0 - sigma w4) = 0 := by
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, hp00, hw00]
    have hzero4 : MvPolynomial.coeff m00 (sigma w4) = 0 := by
      change MvPolynomial.coeff m00 (sigma (t4 • commonFactorAffineQuarticKerBase)) = 0
      exact coeff_m00_sigma_commonFactorAffineQuarticKerScaled t4
    rw [hzero4]
    ring
  have h04_sub : MvPolynomial.coeff m04 (p - sigma w0 - sigma w4) = 0 := by
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, hp04, hw04]
    have hzero0 : MvPolynomial.coeff m04 (sigma w0) = 0 := by
      change MvPolynomial.coeff m04 (sigma (t0 • commonFactorAffineConstKerBase)) = 0
      exact coeff_m04_sigma_commonFactorAffineConstKerScaled t0
    rw [hzero0]
    ring
  have himg : InAdmissibleImage commonFactorAffineRep (p - sigma w0 - sigma w4) :=
    quartic_in_image_commonFactorAffineRep_of_coeff_m00_m04_zero hquartic_sub h00_sub h04_sub
  refine admissible_image_plus_cone_residual_eq_zero (B := B)
    (u := commonFactorAffineRep) (uImg := commonFactorAffineRep)
    commonFactorAffineRep_admissible hsocp
    (imageOrthogonalResidual_self (B := B) hsocp.1) ?_
  refine ⟨p - sigma w0 - sigma w4, {w0, w4}, himg, ?_, ?_⟩
  · intro w hw
    simp at hw
    rcases hw with rfl | rfl
    · exact hw0ker
    · exact hw4ker
  · have hsum : ({w0, w4} : Finset RankFourVec).sum sigma = sigma w0 + sigma w4 := by
      by_cases h : w0 = w4
      · have ht0 : t0 = 0 := by
          have hcoeff :=
            congrArg (MvPolynomial.coeff m00) (congrArg (fun z : RankFourVec => z 3) h)
          simp [w0, w4, commonFactorAffineConstKerBase, commonFactorAffineQuarticKerBase, m00] at hcoeff
          exact hcoeff
        have ht4 : t4 = 0 := by
          have hcoeff :=
            congrArg (MvPolynomial.coeff m11) (congrArg (fun z : RankFourVec => z 1) h)
          simp [w0, w4, commonFactorAffineConstKerBase, commonFactorAffineQuarticKerBase,
            x0, x1, m11, ht0] at hcoeff
          exact hcoeff.symm
        have hw0zero : w0 = 0 := by
          ext i
          fin_cases i <;> simp [w0, commonFactorAffineConstKerBase, ht0]
        have hw4zero : w4 = 0 := by
          ext i
          fin_cases i <;> simp [w4, commonFactorAffineQuarticKerBase, ht4]
        have hsigma0 : sigma (0 : RankFourVec) = 0 := by
          rw [sigma, Fin.sum_univ_four]
          simp
        rw [hw0zero, hw4zero]
        simp [hsigma0]
      · simp [h]
    rw [hsum]
    ring

private theorem coeff_m10_x0 :
    MvPolynomial.coeff m10 (x0 : Poly) = 1 := by
  rw [show (x0 : Poly) = MvPolynomial.monomial m10 (1 : ℝ) by
    simp [x0, m10, MvPolynomial.monomial_eq]]
  rw [MvPolynomial.coeff_monomial]
  simp

private theorem coeff_m11_x0_mul_x1 :
    MvPolynomial.coeff m11 (x0 * x1 : Poly) = 1 := by
  rw [show (x0 * x1 : Poly) = MvPolynomial.monomial m11 (1 : ℝ) by
    simp [x0, x1, m11, MvPolynomial.monomial_eq]]
  rw [MvPolynomial.coeff_monomial]
  simp

theorem quartic_in_image_of_relations_x0_x1_x0sq_x0x1_of_coeff_m00_m04_zero
    {u : RankFourVec}
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 ^ 2)
    (h3 : ∑ i : Fin 4, c3 i • u i = x0 * x1)
    {p : Poly} (hp : IsQuartic p)
    (h00 : MvPolynomial.coeff m00 p = 0)
    (h04 : MvPolynomial.coeff m04 p = 0) :
    InAdmissibleImage u p := by
  classical
  let monomialImage : ∀ (s : Fin 2 →₀ ℕ) (a : ℝ),
      s.sum (fun _ e => e) ≤ 4 →
      s ≠ m00 →
      s ≠ m04 →
      InAdmissibleImage u (MvPolynomial.monomial s a) := by
    intro s a hdeg hne0 hne4
    let e0 := s 0
    let e1 := s 1
    have hsum : s.sum (fun _ e => e) = s 0 + s 1 := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
    have hs0 : s 0 + s 1 ≤ 4 := by
      simpa [hsum] using hdeg
    have hs : e0 + e1 ≤ 4 := by
      simpa [e0, e1] using hs0
    by_cases hsmall : e0 + e1 ≤ 3
    · by_cases hx1 : 1 ≤ e0
      · have hxpow : x0 * x0 ^ (e0 - 1) = x0 ^ e0 := by
          simpa [Nat.sub_add_cancel hx1] using (pow_succ' x0 (e0 - 1)).symm
        have hmul :
            x0 * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1)
              = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
          calc
            x0 * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1)
                = MvPolynomial.C a * (x0 * x0 ^ (e0 - 1)) * x1 ^ e1 := by
                    ring_nf
            _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                  simp [hxpow, mul_assoc]
        simpa [monomial_fin2_eq, e0, e1, hmul] using
          (inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c0) (r := x0)
            (q := (MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1)
            h0 (isQuadratic_C_mul_pow_pow a (e0 - 1) e1 (by omega)))
      · have hy1 : 1 ≤ e1 := by
          by_contra hy1
          have hx0 : e0 = 0 := by omega
          have hy0 : e1 = 0 := by omega
          apply hne0
          ext i
          fin_cases i <;> simp [m00, e0, e1, hx0, hy0]
        have hypow : x1 * x1 ^ (e1 - 1) = x1 ^ e1 := by
          simpa [Nat.sub_add_cancel hy1] using (pow_succ' x1 (e1 - 1)).symm
        have hmul :
            x1 * ((MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 1))
              = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
          calc
            x1 * ((MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 1))
                = MvPolynomial.C a * x0 ^ e0 * (x1 * x1 ^ (e1 - 1)) := by
                    ring_nf
            _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                  simp [hypow, mul_assoc]
        simpa [monomial_fin2_eq, e0, e1, hmul] using
          (inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c1) (r := x1)
            (q := (MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 1))
            h1 (isQuadratic_C_mul_pow_pow a e0 (e1 - 1) (by omega)))
    · by_cases hxy : 1 ≤ e0 ∧ 1 ≤ e1
      · rcases hxy with ⟨hx1, hy1⟩
        have hxpow : x0 * x0 ^ (e0 - 1) = x0 ^ e0 := by
          simpa [Nat.sub_add_cancel hx1] using (pow_succ' x0 (e0 - 1)).symm
        have hypow : x1 * x1 ^ (e1 - 1) = x1 ^ e1 := by
          simpa [Nat.sub_add_cancel hy1] using (pow_succ' x1 (e1 - 1)).symm
        have hmul :
            (x0 * x1) * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1))
              = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
          calc
            (x0 * x1) * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1))
                = MvPolynomial.C a * (x0 * x0 ^ (e0 - 1)) * (x1 * x1 ^ (e1 - 1)) := by
                    ring_nf
            _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                  simp [hxpow, hypow, mul_assoc]
        simpa [monomial_fin2_eq, e0, e1, hmul] using
          (inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c3) (r := x0 * x1)
            (q := (MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1))
            h3 (isQuadratic_C_mul_pow_pow a (e0 - 1) (e1 - 1) (by omega)))
      · have hx2 : 2 ≤ e0 := by
          by_contra hx2
          have hx0 : e0 = 0 := by omega
          have hy4 : e1 = 4 := by omega
          apply hne4
          ext i
          fin_cases i <;> simp [m04, e0, e1, hx0, hy4]
        have hmul :
            x0 ^ 2 * ((MvPolynomial.C a * x0 ^ (e0 - 2)) * x1 ^ e1)
              = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
          calc
            x0 ^ 2 * ((MvPolynomial.C a * x0 ^ (e0 - 2)) * x1 ^ e1)
                = MvPolynomial.C a * (x0 ^ 2 * x0 ^ (e0 - 2)) * x1 ^ e1 := by
                    ring_nf
            _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                  rw [← pow_add, Nat.add_sub_of_le hx2]
        simpa [monomial_fin2_eq, e0, e1, hmul] using
          (inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c2) (r := x0 ^ 2)
            (q := (MvPolynomial.C a * x0 ^ (e0 - 2)) * x1 ^ e1)
            h2 (isQuadratic_C_mul_pow_pow a (e0 - 2) e1 (by omega)))
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
        have hscoeff : MvPolynomial.coeff s p ≠ 0 :=
          MvPolynomial.mem_support_iff.mp (hsub s (by simp))
        have hsne0 : s ≠ m00 := by
          intro hs'
          apply hscoeff
          simpa [hs'] using h00
        have hsne4 : s ≠ m04 := by
          intro hs'
          apply hscoeff
          simpa [hs'] using h04
        exact monomialImage s (MvPolynomial.coeff s p) hsdeg hsne0 hsne4
      · intro t ht
        exact hsub t (by simp [ht])
  exact hP (fun s hs => hs)

private def commonFactorAffineConstKer
    (c0 c1 c3 : Fin 4 → ℝ) (t : ℝ) : RankFourVec :=
  relationDirection (fun i => -((2 : ℝ) * c0 i)) (t • x1) +
    (relationDirection c1 (t • x0) + relationDirection c3 (t • (1 : Poly)))

private theorem commonFactorAffineConstKer_admissible
    (c0 c1 c3 : Fin 4 → ℝ) (t : ℝ) :
    IsAdmissibleDirection (commonFactorAffineConstKer c0 c1 c3 t) := by
  refine isAdmissibleDirection_add
    (relationDirection_admissible (fun i => -((2 : ℝ) * c0 i))
      ((MvPolynomial.totalDegree_smul_le t x1).trans (by simp [x1]))) ?_
  exact isAdmissibleDirection_add
    (relationDirection_admissible c1 ((MvPolynomial.totalDegree_smul_le t x0).trans (by simp [x0])))
    (relationDirection_admissible c3 ((MvPolynomial.totalDegree_smul_le t (1 : Poly)).trans (by simp)))

private theorem commonFactorAffineConstKer_inKer
    {u : RankFourVec} {c0 c1 c3 : Fin 4 → ℝ} {t : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
    (h3 : ∑ i : Fin 4, c3 i • u i = x0 * x1) :
    InAdmissibleKer u (commonFactorAffineConstKer c0 c1 c3 t) := by
  have h0two : ∑ i : Fin 4, ((2 : ℝ) * c0 i) • u i = (2 : ℝ) • x0 := by
    calc
      ∑ i : Fin 4, ((2 : ℝ) * c0 i) • u i = (2 : ℝ) • (∑ i : Fin 4, c0 i • u i) := by
        simp [Finset.smul_sum, smul_smul]
      _ = (2 : ℝ) • x0 := by rw [h0]
  have h0neg : ∑ i : Fin 4, (fun i => -((2 : ℝ) * c0 i)) i • u i = -((2 : ℝ) • x0) := by
    calc
      ∑ i : Fin 4, (fun i => -((2 : ℝ) * c0 i)) i • u i
          = - ∑ i : Fin 4, ((2 : ℝ) * c0 i) • u i := by
              simp
      _ = -((2 : ℝ) • x0) := by rw [h0two]
  refine ⟨commonFactorAffineConstKer_admissible c0 c1 c3 t, ?_⟩
  rw [commonFactorAffineConstKer, A_add_right_local, A_add_right_local,
    A_relationDirection, A_relationDirection, A_relationDirection]
  rw [h0neg, h1, h3]
  have hgoal :
      -(((2 : ℝ) • x0) * (t • x1)) + (x1 * (t • x0) + (x1 * x0) * (t • (1 : Poly))) = 0 := by
    have hmul0 : ((2 : ℝ) • x0) * (t • x1) = (2 : ℝ) • (t • (x0 * x1)) := by
      calc
        ((2 : ℝ) • x0) * (t • x1) = (2 : ℝ) • (x0 * (t • x1)) := by
          exact smul_mul_assoc (2 : ℝ) x0 (t • x1)
        _ = (2 : ℝ) • (t • (x0 * x1)) := by
          congr 1
          exact mul_smul_comm t x0 x1
    have hmul1 : x1 * (t • x0) = t • (x0 * x1) := by
      calc
        x1 * (t • x0) = t • (x1 * x0) := by
          exact mul_smul_comm t x1 x0
        _ = t • (x0 * x1) := by rw [mul_comm]
    have hmul2 : (x1 * x0) * (t • (1 : Poly)) = t • (x0 * x1) := by
      calc
        (x1 * x0) * (t • (1 : Poly)) = (t • (1 : Poly)) * (x1 * x0) := by ring
        _ = t • ((1 : Poly) * (x1 * x0)) := by
          exact smul_mul_assoc t (1 : Poly) (x1 * x0)
        _ = t • (x0 * x1) := by simp [mul_comm]
    rw [hmul0, hmul1, hmul2]
    simp [two_smul, add_assoc]
  simpa [add_assoc, mul_assoc, mul_comm] using hgoal

private theorem coeff_m00_sigma_commonFactorAffineConstKer
    (c0 c1 c3 : Fin 4 → ℝ) (t : ℝ) :
    MvPolynomial.coeff m00 (sigma (commonFactorAffineConstKer c0 c1 c3 t)) =
      (∑ i : Fin 4, (c3 i) ^ 2) * t ^ 2 := by
  have hcoord : ∀ i : Fin 4,
      MvPolynomial.coeff m00 ((commonFactorAffineConstKer c0 c1 c3 t i) ^ 2) = ((c3 i) * t) ^ 2 := by
    intro i
    rw [coeff_m00_sq]
    rw [commonFactorAffineConstKer]
    simp [relationDirection, m00, x0, x1]
  rw [sigma, Fin.sum_univ_four]
  repeat' rw [MvPolynomial.coeff_add]
  rw [hcoord 0, hcoord 1, hcoord 2, hcoord 3]
  rw [Fin.sum_univ_four]
  ring_nf

private theorem coeff_m04_sigma_commonFactorAffineConstKer
    (c0 c1 c3 : Fin 4 → ℝ) (t : ℝ) :
    MvPolynomial.coeff m04 (sigma (commonFactorAffineConstKer c0 c1 c3 t)) = 0 := by
  have hcoord : ∀ i : Fin 4,
      MvPolynomial.coeff m04 ((commonFactorAffineConstKer c0 c1 c3 t i) ^ 2) = 0 := by
    intro i
    rw [coeff_m04_sq_of_quadratic_eq _ ((commonFactorAffineConstKer_admissible c0 c1 c3 t) i)]
    change (MvPolynomial.coeff m02
      (relationDirection (fun j => -((2 : ℝ) * c0 j)) (t • x1) i +
        (relationDirection c1 (t • x0) i + relationDirection c3 (t • (1 : Poly)) i))) ^ 2 = 0
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_add]
    have hx1 :
        MvPolynomial.coeff m02 (relationDirection (fun j => -((2 : ℝ) * c0 j)) (t • x1) i) = 0 := by
      rw [relationDirection, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul]
      simp [m02, x1]
    have hx0 :
        MvPolynomial.coeff m02 (relationDirection c1 (t • x0) i) = 0 := by
      rw [relationDirection, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul]
      simp [m02, x0]
    have hconst :
        MvPolynomial.coeff m02 (relationDirection c3 (t • (1 : Poly)) i) = 0 := by
      rw [relationDirection, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul]
      have h1coeff : MvPolynomial.coeff m02 (1 : Poly) = 0 := by
        rw [show (1 : Poly) = MvPolynomial.C (1 : ℝ) by simp, MvPolynomial.coeff_C]
        split_ifs with h
        · exfalso
          have := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h.symm
          simp [m02] at this
        · rfl
      simp [h1coeff]
    rw [hx1, hx0, hconst]
    ring
  rw [sigma, Fin.sum_univ_four]
  repeat' rw [MvPolynomial.coeff_add]
  rw [hcoord 0, hcoord 1, hcoord 2, hcoord 3]
  ring

private def commonFactorAffineQuarticKer
    (c0 c1 : Fin 4 → ℝ) (t : ℝ) : RankFourVec :=
  relationDirection (-c0) (t • (x1 ^ 2)) +
    relationDirection c1 (t • (x0 * x1))

private theorem commonFactorAffineQuarticKer_admissible
    (c0 c1 : Fin 4 → ℝ) (t : ℝ) :
    IsAdmissibleDirection (commonFactorAffineQuarticKer c0 c1 t) := by
  refine isAdmissibleDirection_add
    (relationDirection_admissible (-c0)
      ((MvPolynomial.totalDegree_smul_le t (x1 ^ 2 : Poly)).trans (by simp [x1]))) ?_
  exact relationDirection_admissible c1
    ((MvPolynomial.totalDegree_smul_le t (x0 * x1 : Poly)).trans isQuadratic_x0_mul_x1)

private theorem commonFactorAffineQuarticKer_inKer
    {u : RankFourVec} {c0 c1 : Fin 4 → ℝ} {t : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1) :
    InAdmissibleKer u (commonFactorAffineQuarticKer c0 c1 t) := by
  refine ⟨commonFactorAffineQuarticKer_admissible c0 c1 t, ?_⟩
  rw [commonFactorAffineQuarticKer, A_add_right_local, A_relationDirection, A_relationDirection]
  simp [Pi.neg_apply, h0, h1]
  ring_nf

private theorem coeff_m00_sigma_commonFactorAffineQuarticKer
    (c0 c1 : Fin 4 → ℝ) (t : ℝ) :
    MvPolynomial.coeff m00 (sigma (commonFactorAffineQuarticKer c0 c1 t)) = 0 := by
  have hcoord : ∀ i : Fin 4,
      MvPolynomial.coeff m00 ((commonFactorAffineQuarticKer c0 c1 t i) ^ 2) = 0 := by
    intro i
    rw [coeff_m00_sq]
    change (MvPolynomial.coeff m00
      (relationDirection (-c0) (t • (x1 ^ 2)) i + relationDirection c1 (t • (x0 * x1)) i)) ^ 2 = 0
    rw [MvPolynomial.coeff_add]
    have hx1 :
        MvPolynomial.coeff m00 (relationDirection (-c0) (t • (x1 ^ 2)) i) = 0 := by
      have h00x1sq : MvPolynomial.coeff m00 (x1 ^ 2 : Poly) = 0 := by
        rw [show (x1 ^ 2 : Poly) = MvPolynomial.monomial m02 (1 : ℝ) by
          simp [x1, m02, MvPolynomial.monomial_eq]]
        rw [MvPolynomial.coeff_monomial]
        split_ifs with h
        · exfalso
          simp [m00, m02] at h
        · rfl
      rw [relationDirection, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul]
      simp [h00x1sq]
    have hxy :
        MvPolynomial.coeff m00 (relationDirection c1 (t • (x0 * x1)) i) = 0 := by
      rw [relationDirection, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul]
      rw [show (x0 * x1 : Poly) = MvPolynomial.monomial m11 (1 : ℝ) by
        simp [x0, x1, m11, MvPolynomial.monomial_eq]]
      rw [MvPolynomial.coeff_monomial]
      split_ifs with h
      · exfalso
        have := congrArg (fun e : Fin 2 →₀ ℕ => e 0) h.symm
        simp [m00, m11] at this
      · simp
    rw [hx1, hxy]
    ring
  rw [sigma, Fin.sum_univ_four]
  repeat' rw [MvPolynomial.coeff_add]
  rw [hcoord 0, hcoord 1, hcoord 2, hcoord 3]
  ring

private theorem coeff_m04_sigma_commonFactorAffineQuarticKer
    (c0 c1 : Fin 4 → ℝ) (t : ℝ) :
    MvPolynomial.coeff m04 (sigma (commonFactorAffineQuarticKer c0 c1 t)) =
      (∑ i : Fin 4, (c0 i) ^ 2) * t ^ 2 := by
  have hcoord : ∀ i : Fin 4,
      MvPolynomial.coeff m04 ((commonFactorAffineQuarticKer c0 c1 t i) ^ 2) = ((c0 i) * t) ^ 2 := by
    intro i
    rw [coeff_m04_sq_of_quadratic_eq _ ((commonFactorAffineQuarticKer_admissible c0 c1 t) i)]
    change (MvPolynomial.coeff m02
      (relationDirection (-c0) (t • (x1 ^ 2)) i + relationDirection c1 (t • (x0 * x1)) i)) ^ 2
        = ((c0 i) * t) ^ 2
    rw [MvPolynomial.coeff_add]
    have hx1sq :
        MvPolynomial.coeff m02 (relationDirection (-c0) (t • (x1 ^ 2)) i) = -(c0 i) * t := by
      calc
        MvPolynomial.coeff m02 (relationDirection (-c0) (t • (x1 ^ 2)) i)
            = MvPolynomial.coeff m02 (((-(c0 i)) * t) • (x1 ^ 2 : Poly)) := by
                simp [relationDirection, smul_smul]
        _ = -(c0 i) * t := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using coeff_m02_smul_x1_sq ((-(c0 i)) * t)
    have hxy :
        MvPolynomial.coeff m02 (relationDirection c1 (t • (x0 * x1)) i) = 0 := by
      calc
        MvPolynomial.coeff m02 (relationDirection c1 (t • (x0 * x1)) i)
            = MvPolynomial.coeff m02 (((c1 i) * t) • (x0 * x1 : Poly)) := by
                simp [relationDirection, smul_smul]
        _ = 0 := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using coeff_m02_smul_x0_mul_x1 ((c1 i) * t)
    rw [hx1sq, hxy]
    ring
  rw [sigma, Fin.sum_univ_four]
  repeat' rw [MvPolynomial.coeff_add]
  rw [hcoord 0, hcoord 1, hcoord 2, hcoord 3]
  rw [Fin.sum_univ_four]
  ring_nf

theorem residual_eq_zero_of_relations_x0_x1_x0sq_x0x1
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 ^ 2)
    (h3 : ∑ i : Fin 4, c3 i • u i = x0 * x1)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  rcases hp with ⟨hpquartic, k, qs, hqdeg, hpq⟩
  let s0 : ℝ := ∑ i : Fin k, (MvPolynomial.coeff m00 (qs i)) ^ 2
  let s4 : ℝ := ∑ i : Fin k, (MvPolynomial.coeff m02 (qs i)) ^ 2
  let alpha0 : ℝ := ∑ i : Fin 4, (c3 i) ^ 2
  let alpha4 : ℝ := ∑ i : Fin 4, (c0 i) ^ 2
  let t0 : ℝ := Real.sqrt (s0 / alpha0)
  let t4 : ℝ := Real.sqrt (s4 / alpha4)
  let w0 : RankFourVec := commonFactorAffineConstKer c0 c1 c3 t0
  let w4 : RankFourVec := commonFactorAffineQuarticKer c0 c1 t4
  have hs0_nonneg : 0 ≤ s0 := by
    dsimp [s0]
    positivity
  have hs4_nonneg : 0 ≤ s4 := by
    dsimp [s4]
    positivity
  have hc3_ne : c3 ≠ 0 := by
    intro hc3
    have : (0 : Poly) = x0 * x1 := by
      simpa [hc3] using h3
    have hcoeff := congrArg (MvPolynomial.coeff m11) this
    simp [coeff_m11_x0_mul_x1] at hcoeff
  have hc0_ne : c0 ≠ 0 := by
    intro hc0
    have : (0 : Poly) = x0 := by
      simpa [hc0] using h0
    have hcoeff := congrArg (MvPolynomial.coeff m10) this
    simp [coeff_m10_x0] at hcoeff
  have halpha0_pos : 0 < alpha0 := sum_sq_pos_of_ne_zero c3 hc3_ne
  have halpha4_pos : 0 < alpha4 := sum_sq_pos_of_ne_zero c0 hc0_ne
  have halpha0_nonneg : 0 ≤ alpha0 := le_of_lt halpha0_pos
  have halpha4_nonneg : 0 ≤ alpha4 := le_of_lt halpha4_pos
  have hsdiv0_nonneg : 0 ≤ s0 / alpha0 := by
    exact div_nonneg hs0_nonneg halpha0_nonneg
  have hsdiv4_nonneg : 0 ≤ s4 / alpha4 := by
    exact div_nonneg hs4_nonneg halpha4_nonneg
  have hp00 : MvPolynomial.coeff m00 p = s0 := by
    rw [hpq, MvPolynomial.coeff_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact coeff_m00_sq (qs i)
  have hp04 : MvPolynomial.coeff m04 p = s4 := by
    rw [hpq, MvPolynomial.coeff_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact coeff_m04_sq_of_quadratic_eq (qs i) (hqdeg i)
  have hw0ker : InAdmissibleKer u w0 := by
    dsimp [w0]
    exact commonFactorAffineConstKer_inKer h0 h1 h3
  have hw4ker : InAdmissibleKer u w4 := by
    dsimp [w4]
    exact commonFactorAffineQuarticKer_inKer h0 h1
  have hw00 : MvPolynomial.coeff m00 (sigma w0) = s0 := by
    change MvPolynomial.coeff m00 (sigma (commonFactorAffineConstKer c0 c1 c3 t0)) = s0
    calc
      MvPolynomial.coeff m00 (sigma (commonFactorAffineConstKer c0 c1 c3 t0)) = alpha0 * t0 ^ 2 := by
        exact coeff_m00_sigma_commonFactorAffineConstKer c0 c1 c3 t0
      _ = alpha0 * (s0 / alpha0) := by
            dsimp [t0]
            rw [Real.sq_sqrt hsdiv0_nonneg]
      _ = s0 := by
            field_simp [alpha0, halpha0_pos.ne']
  have hw04 : MvPolynomial.coeff m04 (sigma w4) = s4 := by
    change MvPolynomial.coeff m04 (sigma (commonFactorAffineQuarticKer c0 c1 t4)) = s4
    calc
      MvPolynomial.coeff m04 (sigma (commonFactorAffineQuarticKer c0 c1 t4)) = alpha4 * t4 ^ 2 := by
        exact coeff_m04_sigma_commonFactorAffineQuarticKer c0 c1 t4
      _ = alpha4 * (s4 / alpha4) := by
            dsimp [t4]
            rw [Real.sq_sqrt hsdiv4_nonneg]
      _ = s4 := by
            field_simp [alpha4, halpha4_pos.ne']
  have hquartic_sub : IsQuartic (p - sigma w0 - sigma w4) := by
    calc
      (p - sigma w0 - sigma w4).totalDegree ≤ max (p - sigma w0).totalDegree (sigma w4).totalDegree := by
        exact MvPolynomial.totalDegree_sub _ _
      _ ≤ 4 := by
        apply max_le
        · calc
            (p - sigma w0).totalDegree ≤ max p.totalDegree (sigma w0).totalDegree := by
              exact MvPolynomial.totalDegree_sub _ _
            _ ≤ 4 := by
              exact max_le hpquartic (isQuartic_sigma_of_admissible hw0ker.1)
        · exact isQuartic_sigma_of_admissible hw4ker.1
  have h00_sub : MvPolynomial.coeff m00 (p - sigma w0 - sigma w4) = 0 := by
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, hp00, hw00]
    have hzero4 : MvPolynomial.coeff m00 (sigma w4) = 0 := by
      change MvPolynomial.coeff m00 (sigma (commonFactorAffineQuarticKer c0 c1 t4)) = 0
      exact coeff_m00_sigma_commonFactorAffineQuarticKer c0 c1 t4
    rw [hzero4]
    ring
  have h04_sub : MvPolynomial.coeff m04 (p - sigma w0 - sigma w4) = 0 := by
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, hp04, hw04]
    have hzero0 : MvPolynomial.coeff m04 (sigma w0) = 0 := by
      change MvPolynomial.coeff m04 (sigma (commonFactorAffineConstKer c0 c1 c3 t0)) = 0
      exact coeff_m04_sigma_commonFactorAffineConstKer c0 c1 c3 t0
    rw [hzero0]
    ring
  have himg : InAdmissibleImage u (p - sigma w0 - sigma w4) :=
    quartic_in_image_of_relations_x0_x1_x0sq_x0x1_of_coeff_m00_m04_zero
      h0 h1 h2 h3 hquartic_sub h00_sub h04_sub
  refine admissible_image_plus_cone_residual_eq_zero (B := B)
    (u := u) (uImg := u)
    hu hsocp
    (imageOrthogonalResidual_self (B := B) hsocp.1) ?_
  refine ⟨p - sigma w0 - sigma w4, {w0, w4}, himg, ?_, ?_⟩
  · intro w hw
    simp at hw
    rcases hw with rfl | rfl
    · exact hw0ker
    · exact hw4ker
  · have hsum : ({w0, w4} : Finset RankFourVec).sum sigma = sigma w0 + sigma w4 := by
      by_cases h : w0 = w4
      · have ht0 : t0 = 0 := by
          have hcoeff := congrArg (MvPolynomial.coeff m00) (congrArg sigma h)
          have hw0m00 :
              MvPolynomial.coeff m00 (sigma w0) = alpha0 * t0 ^ 2 := by
            dsimp [w0]
            exact coeff_m00_sigma_commonFactorAffineConstKer c0 c1 c3 t0
          have hw4m00 : MvPolynomial.coeff m00 (sigma w4) = 0 := by
            dsimp [w4]
            exact coeff_m00_sigma_commonFactorAffineQuarticKer c0 c1 t4
          rw [hw0m00, hw4m00] at hcoeff
          have ht0sq : t0 ^ 2 = 0 := by nlinarith [halpha0_pos]
          exact sq_eq_zero_iff.mp ht0sq
        have ht4 : t4 = 0 := by
          have hcoeff := congrArg (MvPolynomial.coeff m04) (congrArg sigma h)
          have hw0m04 : MvPolynomial.coeff m04 (sigma w0) = 0 := by
            dsimp [w0]
            exact coeff_m04_sigma_commonFactorAffineConstKer c0 c1 c3 t0
          have hw4m04 :
              MvPolynomial.coeff m04 (sigma w4) = alpha4 * t4 ^ 2 := by
            dsimp [w4]
            exact coeff_m04_sigma_commonFactorAffineQuarticKer c0 c1 t4
          rw [hw0m04, hw4m04] at hcoeff
          have ht4sq : t4 ^ 2 = 0 := by nlinarith [halpha4_pos]
          exact sq_eq_zero_iff.mp ht4sq
        have hw0zero : w0 = 0 := by
          ext i
          simp [w0, commonFactorAffineConstKer, relationDirection, ht0]
        have hw4zero : w4 = 0 := by
          ext i
          simp [w4, commonFactorAffineQuarticKer, relationDirection, ht4]
        have hsigma0 : sigma (0 : RankFourVec) = 0 := by
          rw [sigma, Fin.sum_univ_four]
          simp
        rw [hw0zero, hw4zero]
        simp [hsigma0]
      · simp [h]
    rw [hsum]
    ring

theorem quartic_in_image_of_relations_x0_x1_onePlusAX0sq_x0x1_of_coeff_m04_zero
    {u : RankFourVec}
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {α : ℝ}
    (hα : α ≠ 0)
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
    (h2 : ∑ i : Fin 4, c2 i • u i = (1 : Poly) + α • (x0 ^ 2 : Poly))
    (h3 : ∑ i : Fin 4, c3 i • u i = x0 * x1)
    {p : Poly} (hp : IsQuartic p)
    (h04 : MvPolynomial.coeff m04 p = 0) :
    InAdmissibleImage u p := by
  classical
  let monomialImage : ∀ (s : Fin 2 →₀ ℕ) (a : ℝ),
      s.sum (fun _ e => e) ≤ 4 →
      s ≠ m04 →
      InAdmissibleImage u (MvPolynomial.monomial s a) := by
    intro s a hdeg hne4
    let e0 := s 0
    let e1 := s 1
    have hsum : s.sum (fun _ e => e) = s 0 + s 1 := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
    have hs0 : s 0 + s 1 ≤ 4 := by
      simpa [hsum] using hdeg
    have hs : e0 + e1 ≤ 4 := by
      simpa [e0, e1] using hs0
    by_cases hsmall : e0 + e1 ≤ 3
    · by_cases hx1 : 1 ≤ e0
      · have hxpow : x0 * x0 ^ (e0 - 1) = x0 ^ e0 := by
          simpa [Nat.sub_add_cancel hx1] using (pow_succ' x0 (e0 - 1)).symm
        have hmul :
            x0 * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1)
              = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
          calc
            x0 * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1)
                = MvPolynomial.C a * (x0 * x0 ^ (e0 - 1)) * x1 ^ e1 := by
                    ring_nf
            _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                  simp [hxpow, mul_assoc]
        simpa [monomial_fin2_eq, e0, e1, hmul] using
          (inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c0) (r := x0)
            (q := (MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1)
            h0 (isQuadratic_C_mul_pow_pow a (e0 - 1) e1 (by omega)))
      · by_cases hy1 : 1 ≤ e1
        · have hypow : x1 * x1 ^ (e1 - 1) = x1 ^ e1 := by
            simpa [Nat.sub_add_cancel hy1] using (pow_succ' x1 (e1 - 1)).symm
          have hmul :
              x1 * ((MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 1))
                = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
            calc
              x1 * ((MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 1))
                  = MvPolynomial.C a * x0 ^ e0 * (x1 * x1 ^ (e1 - 1)) := by
                      ring_nf
              _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                    simp [hypow, mul_assoc]
          simpa [monomial_fin2_eq, e0, e1, hmul] using
            (inAdmissibleImage_of_relation_mul_low
              (u := u) (c := c1) (r := x1)
              (q := (MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 1))
              h1 (isQuadratic_C_mul_pow_pow a e0 (e1 - 1) (by omega)))
        · have hx0 : e0 = 0 := by omega
          have hy0 : e1 = 0 := by omega
          rw [monomial_fin2_eq]
          simp [e0, e1, hx0, hy0]
          have himg2 :
              InAdmissibleImage u
                (((1 : Poly) + α • (x0 ^ 2 : Poly)) * ((MvPolynomial.C a * x0 ^ 0) * x1 ^ 0)) := by
            exact inAdmissibleImage_of_relation_mul_low
              (u := u) (c := c2) (r := (1 : Poly) + α • (x0 ^ 2 : Poly))
              (q := (MvPolynomial.C a * x0 ^ 0) * x1 ^ 0)
              h2 (isQuadratic_C_mul_pow_pow a 0 0 (by omega))
          have himg0 :
              InAdmissibleImage u
                (x0 * ((MvPolynomial.C (-α * a) * x0 ^ 1) * x1 ^ 0)) := by
            exact inAdmissibleImage_of_relation_mul_low
              (u := u) (c := c0) (r := x0)
              (q := (MvPolynomial.C (-α * a) * x0 ^ 1) * x1 ^ 0)
              h0 (isQuadratic_C_mul_pow_pow (-α * a) 1 0 (by omega))
          have hEq :
              ((1 : Poly) + α • (x0 ^ 2 : Poly)) * ((MvPolynomial.C a * x0 ^ 0) * x1 ^ 0) +
                  x0 * ((MvPolynomial.C (-α * a) * x0 ^ 1) * x1 ^ 0) =
                (MvPolynomial.C a : Poly) := by
            simp [MvPolynomial.smul_eq_C_mul]
            ring
          rw [← hEq]
          exact inAdmissibleImage_add u himg2 himg0
    · have hfour : e0 + e1 = 4 := by omega
      by_cases hxy : 1 ≤ e0 ∧ 1 ≤ e1
      · rcases hxy with ⟨hx1, hy1⟩
        have hxpow : x0 * x0 ^ (e0 - 1) = x0 ^ e0 := by
          simpa [Nat.sub_add_cancel hx1] using (pow_succ' x0 (e0 - 1)).symm
        have hypow : x1 * x1 ^ (e1 - 1) = x1 ^ e1 := by
          simpa [Nat.sub_add_cancel hy1] using (pow_succ' x1 (e1 - 1)).symm
        have hmul :
            (x0 * x1) * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1))
              = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
          calc
            (x0 * x1) * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1))
                = MvPolynomial.C a * (x0 * x0 ^ (e0 - 1)) * (x1 * x1 ^ (e1 - 1)) := by
                    ring_nf
            _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                  simp [hxpow, hypow, mul_assoc]
        simpa [monomial_fin2_eq, e0, e1, hmul] using
          (inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c3) (r := x0 * x1)
            (q := (MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1))
            h3 (isQuadratic_C_mul_pow_pow a (e0 - 1) (e1 - 1) (by omega)))
      · have hy0 : e1 = 0 := by
          by_contra hy0
          have hy1 : 1 ≤ e1 := by omega
          by_cases hx0 : e0 = 0
          · have hy4 : e1 = 4 := by omega
            apply hne4
            ext i
            fin_cases i <;> simp [m04, e0, e1, hx0, hy4]
          · have hx1 : 1 ≤ e0 := by omega
            exact hxy ⟨hx1, hy1⟩
        have hx4 : e0 = 4 := by omega
        rw [monomial_fin2_eq]
        simp [e0, e1, hx4, hy0]
        have himg2 :
            InAdmissibleImage u
              (((1 : Poly) + α • (x0 ^ 2 : Poly)) * ((MvPolynomial.C (a / α) * x0 ^ 2) * x1 ^ 0)) := by
          exact inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c2) (r := (1 : Poly) + α • (x0 ^ 2 : Poly))
            (q := (MvPolynomial.C (a / α) * x0 ^ 2) * x1 ^ 0)
            h2 (isQuadratic_C_mul_pow_pow (a / α) 2 0 (by omega))
        have himg0 :
            InAdmissibleImage u
              (x0 * ((MvPolynomial.C (-(a / α)) * x0 ^ 1) * x1 ^ 0)) := by
          exact inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c0) (r := x0)
            (q := (MvPolynomial.C (-(a / α)) * x0 ^ 1) * x1 ^ 0)
            h0 (isQuadratic_C_mul_pow_pow (-(a / α)) 1 0 (by omega))
        have hEq :
            ((1 : Poly) + α • (x0 ^ 2 : Poly)) *
                ((MvPolynomial.C (a / α) * x0 ^ 2) * x1 ^ 0) +
                x0 * ((MvPolynomial.C (-(a / α)) * x0 ^ 1) * x1 ^ 0) =
              (MvPolynomial.C a * x0 ^ 4 : Poly) := by
          have hC :
              (MvPolynomial.C α : Poly) * MvPolynomial.C a * MvPolynomial.C α⁻¹ =
                MvPolynomial.C a := by
            rw [← MvPolynomial.C_mul, ← MvPolynomial.C_mul]
            congr 1
            field_simp [hα]
          simp [MvPolynomial.smul_eq_C_mul, pow_succ, div_eq_mul_inv]
          ring_nf
          calc
            MvPolynomial.C α * x0 ^ 4 * MvPolynomial.C a * MvPolynomial.C α⁻¹
                = x0 ^ 4 * ((MvPolynomial.C α : Poly) * MvPolynomial.C a * MvPolynomial.C α⁻¹) := by
                    ring
            _ = x0 ^ 4 * MvPolynomial.C a := by rw [hC]
        rw [← hEq]
        exact inAdmissibleImage_add u himg2 himg0
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
        have hscoeff : MvPolynomial.coeff s p ≠ 0 :=
          MvPolynomial.mem_support_iff.mp (hsub s (by simp))
        have hsne4 : s ≠ m04 := by
          intro hs'
          apply hscoeff
          simpa [hs'] using h04
        exact monomialImage s (MvPolynomial.coeff s p) hsdeg hsne4
      · intro t ht
        exact hsub t (by simp [ht])
  exact hP (fun s hs => hs)

theorem quartic_in_image_of_relations_x0_x1_onePlusX0sq_x0x1_of_coeff_m04_zero
    {u : RankFourVec}
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
    (h2 : ∑ i : Fin 4, c2 i • u i = (1 : Poly) + x0 ^ 2)
    (h3 : ∑ i : Fin 4, c3 i • u i = x0 * x1)
    {p : Poly} (hp : IsQuartic p)
    (h04 : MvPolynomial.coeff m04 p = 0) :
    InAdmissibleImage u p := by
  exact quartic_in_image_of_relations_x0_x1_onePlusAX0sq_x0x1_of_coeff_m04_zero
    (α := 1) (by norm_num) h0 h1 (by simpa using h2) h3 hp h04

theorem residual_eq_zero_of_relations_x0_x1_onePlusAX0sq_x0x1
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    {α : ℝ}
    (hα : α ≠ 0)
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
    (h2 : ∑ i : Fin 4, c2 i • u i = (1 : Poly) + α • (x0 ^ 2 : Poly))
    (h3 : ∑ i : Fin 4, c3 i • u i = x0 * x1)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  rcases hp with ⟨hpquartic, k, qs, hqdeg, hpq⟩
  let s4 : ℝ := ∑ i : Fin k, (MvPolynomial.coeff m02 (qs i)) ^ 2
  let alpha4 : ℝ := ∑ i : Fin 4, (c0 i) ^ 2
  let t4 : ℝ := Real.sqrt (s4 / alpha4)
  let w4 : RankFourVec := commonFactorAffineQuarticKer c0 c1 t4
  have hs4_nonneg : 0 ≤ s4 := by
    dsimp [s4]
    positivity
  have hc0_ne : c0 ≠ 0 := by
    intro hc0
    have : (0 : Poly) = x0 := by
      simpa [hc0] using h0
    have hcoeff := congrArg (MvPolynomial.coeff m10) this
    simp [coeff_m10_x0] at hcoeff
  have halpha4_pos : 0 < alpha4 := sum_sq_pos_of_ne_zero c0 hc0_ne
  have halpha4_nonneg : 0 ≤ alpha4 := le_of_lt halpha4_pos
  have hsdiv4_nonneg : 0 ≤ s4 / alpha4 := by
    exact div_nonneg hs4_nonneg halpha4_nonneg
  have hp04 : MvPolynomial.coeff m04 p = s4 := by
    rw [hpq, MvPolynomial.coeff_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact coeff_m04_sq_of_quadratic_eq (qs i) (hqdeg i)
  have hw4ker : InAdmissibleKer u w4 := by
    dsimp [w4]
    exact commonFactorAffineQuarticKer_inKer h0 h1
  have hw04 : MvPolynomial.coeff m04 (sigma w4) = s4 := by
    change MvPolynomial.coeff m04 (sigma (commonFactorAffineQuarticKer c0 c1 t4)) = s4
    calc
      MvPolynomial.coeff m04 (sigma (commonFactorAffineQuarticKer c0 c1 t4)) = alpha4 * t4 ^ 2 := by
        exact coeff_m04_sigma_commonFactorAffineQuarticKer c0 c1 t4
      _ = alpha4 * (s4 / alpha4) := by
            dsimp [t4]
            rw [Real.sq_sqrt hsdiv4_nonneg]
      _ = s4 := by
            field_simp [alpha4, halpha4_pos.ne']
  have hquartic_sub : IsQuartic (p - sigma w4) := by
    calc
      (p - sigma w4).totalDegree ≤ max p.totalDegree (sigma w4).totalDegree := by
        exact MvPolynomial.totalDegree_sub _ _
      _ ≤ 4 := by
        exact max_le hpquartic (isQuartic_sigma_of_admissible hw4ker.1)
  have h04_sub : MvPolynomial.coeff m04 (p - sigma w4) = 0 := by
    rw [MvPolynomial.coeff_sub, hp04, hw04]
    ring
  have himg : InAdmissibleImage u (p - sigma w4) :=
    quartic_in_image_of_relations_x0_x1_onePlusAX0sq_x0x1_of_coeff_m04_zero
      hα h0 h1 h2 h3 hquartic_sub h04_sub
  refine admissible_image_plus_cone_residual_eq_zero (B := B)
    (u := u) (uImg := u)
    hu hsocp
    (imageOrthogonalResidual_self (B := B) hsocp.1) ?_
  refine ⟨p - sigma w4, {w4}, himg, ?_, ?_⟩
  · intro w hw
    simp at hw
    subst hw
    exact hw4ker
  · simp

theorem residual_eq_zero_of_relations_x0_x1_onePlusX0sq_x0x1
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
    (h2 : ∑ i : Fin 4, c2 i • u i = (1 : Poly) + x0 ^ 2)
    (h3 : ∑ i : Fin 4, c3 i • u i = x0 * x1)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_relations_x0_x1_onePlusAX0sq_x0x1
    (α := 1) (by norm_num) hu h0 h1 (by simpa using h2) h3 hp hsocp

theorem residual_eq_zero_of_equiv_relations_x0_x1_onePlusAX0sq_x0x1
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    {α : ℝ}
    (hα : α ≠ 0)
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1)
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = (1 : Poly) + α • (x0 ^ 2 : Poly))
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = x0 * x1) :
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
    exact residual_eq_zero_of_relations_x0_x1_onePlusAX0sq_x0x1
      (B := B0) (u := mapVec e.toAlgHom u) hα hu0 h0 h1 h2 h3 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_equiv_relations_x0_x1_onePlusX0sq_x0x1
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
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1)
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = (1 : Poly) + x0 ^ 2)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = x0 * x1) :
    residual p u = 0 := by
  exact residual_eq_zero_of_equiv_relations_x0_x1_onePlusAX0sq_x0x1
    (e := e) (heQuad := heQuad) (heQuadSymm := heQuadSymm) (heQuartic := heQuartic)
    (α := 1) (by norm_num) hB hp hu hsocp h0 h1 (by simpa using h2) h3

theorem residual_eq_zero_of_relations_affinePair_onePlusAX0sq_x0x1
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    {α : ℝ}
    (hα : α ≠ 0)
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {r0 r1 : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = affineLinePoly r0 1 0)
    (h1 : ∑ i : Fin 4, c1 i • u i = affineLinePoly r1 0 1)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q2 =
      (1 : Poly) + α • (x0 ^ 2 : Poly))
    (hq3 : affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q3 = x0 * x1)
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
  have heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q) := by
    intro q hq
    exact isQuadratic_affineEquiv
      (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
      (by simp) (by simp)
      (by
        intro i
        fin_cases i <;> simp [b, b'])
      (by
        intro i
        fin_cases i <;> simp [b, b']) hq
  have heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q) := by
    intro q hq
    exact isQuadratic_affineEquiv_symm
      (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
      (by simp) (by simp)
      (by
        intro i
        fin_cases i <;> simp [b, b'])
      (by
        intro i
        fin_cases i <;> simp [b, b']) hq
  have heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q) := by
    intro q hq
    exact isQuartic_affineEquiv
      (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
      (by simp) (by simp)
      (by
        intro i
        fin_cases i <;> simp [b, b'])
      (by
        intro i
        fin_cases i <;> simp [b, b']) hq
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  have h0trans : e (affineLinePoly r0 1 0) = x0 := by
    simp [e, b, b', affineLinePoly, affineEquiv, affineHom, affineImage, x0, x1,
      Fin.sum_univ_two]
  have h1trans : e (affineLinePoly r1 0 1) = x1 := by
    simp [e, b, b', affineLinePoly, affineEquiv, affineHom, affineImage, x0, x1,
      Fin.sum_univ_two]
  have h0' :
      ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0 := by
    simpa [e] using (relation_map e.toAlgHom h0).trans h0trans
  have h1' :
      ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1 := by
    simpa [e] using (relation_map e.toAlgHom h1).trans h1trans
  have h2' :
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = (1 : Poly) + α • (x0 ^ 2 : Poly) := by
    simpa [e, b] using (relation_map e.toAlgHom h2).trans hq2
  have h3' :
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = x0 * x1 := by
    simpa [e, b] using (relation_map e.toAlgHom h3).trans hq3
  exact residual_eq_zero_of_equiv_relations_x0_x1_onePlusAX0sq_x0x1
    (e := e) (heQuad := fun {_} hq => heQuad hq) (heQuadSymm := fun {_} hq => heQuadSymm hq)
    (heQuartic := fun {_} hq => heQuartic hq)
    hα hB hp hu hsocp h0' h1' h2' h3'

theorem residual_eq_zero_of_relations_affinePair_onePlusX0sq_x0x1
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {r0 r1 : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = affineLinePoly r0 1 0)
    (h1 : ∑ i : Fin 4, c1 i • u i = affineLinePoly r1 0 1)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q2 = (1 : Poly) + x0 ^ 2)
    (hq3 : affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q3 = x0 * x1)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_relations_affinePair_onePlusAX0sq_x0x1
    (α := 1) (by norm_num) hu h0 h1 h2 h3 (by simpa using hq2) hq3 hp hsocp

theorem quartic_in_image_of_relations_x0_x1_onePlusBX0x1_x1sq_of_coeff_m40_zero
    {u : RankFourVec}
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {β : ℝ}
    (hβ : β ≠ 0)
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
    (h2 : ∑ i : Fin 4, c2 i • u i = (1 : Poly) + β • (x0 * x1 : Poly))
    (h3 : ∑ i : Fin 4, c3 i • u i = x1 ^ 2)
    {p : Poly} (hp : IsQuartic p)
    (h40 : MvPolynomial.coeff m40 p = 0) :
    InAdmissibleImage u p := by
  classical
  let monomialImage : ∀ (s : Fin 2 →₀ ℕ) (a : ℝ),
      s.sum (fun _ e => e) ≤ 4 →
      s ≠ m40 →
      InAdmissibleImage u (MvPolynomial.monomial s a) := by
    intro s a hdeg hne40
    let e0 := s 0
    let e1 := s 1
    have hsum : s.sum (fun _ e => e) = s 0 + s 1 := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
    have hs0 : s 0 + s 1 ≤ 4 := by
      simpa [hsum] using hdeg
    have hs : e0 + e1 ≤ 4 := by
      simpa [e0, e1] using hs0
    by_cases hsmall : e0 + e1 ≤ 3
    · by_cases hx1 : 1 ≤ e0
      · have hxpow : x0 * x0 ^ (e0 - 1) = x0 ^ e0 := by
          simpa [Nat.sub_add_cancel hx1] using (pow_succ' x0 (e0 - 1)).symm
        have hmul :
            x0 * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1)
              = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
          calc
            x0 * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1)
                = MvPolynomial.C a * (x0 * x0 ^ (e0 - 1)) * x1 ^ e1 := by
                    ring_nf
            _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                  simp [hxpow, mul_assoc]
        simpa [monomial_fin2_eq, e0, e1, hmul] using
          (inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c0) (r := x0)
            (q := (MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1)
            h0 (isQuadratic_C_mul_pow_pow a (e0 - 1) e1 (by omega)))
      · by_cases hy1 : 1 ≤ e1
        · have hypow : x1 * x1 ^ (e1 - 1) = x1 ^ e1 := by
            simpa [Nat.sub_add_cancel hy1] using (pow_succ' x1 (e1 - 1)).symm
          have hmul :
              x1 * ((MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 1))
                = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
            calc
              x1 * ((MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 1))
                  = MvPolynomial.C a * x0 ^ e0 * (x1 * x1 ^ (e1 - 1)) := by
                      ring_nf
              _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                    simp [hypow, mul_assoc]
          simpa [monomial_fin2_eq, e0, e1, hmul] using
            (inAdmissibleImage_of_relation_mul_low
              (u := u) (c := c1) (r := x1)
              (q := (MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 1))
              h1 (isQuadratic_C_mul_pow_pow a e0 (e1 - 1) (by omega)))
        · have hx0 : e0 = 0 := by omega
          have hy0 : e1 = 0 := by omega
          rw [monomial_fin2_eq]
          simp [e0, e1, hx0, hy0]
          have himg2 :
              InAdmissibleImage u
                (((1 : Poly) + β • (x0 * x1 : Poly)) * ((MvPolynomial.C a * x0 ^ 0) * x1 ^ 0)) := by
            exact inAdmissibleImage_of_relation_mul_low
              (u := u) (c := c2) (r := (1 : Poly) + β • (x0 * x1 : Poly))
              (q := (MvPolynomial.C a * x0 ^ 0) * x1 ^ 0)
              h2 (isQuadratic_C_mul_pow_pow a 0 0 (by omega))
          have himg1 :
              InAdmissibleImage u
                (x1 * ((MvPolynomial.C (-β * a) * x0 ^ 1) * x1 ^ 0)) := by
            exact inAdmissibleImage_of_relation_mul_low
              (u := u) (c := c1) (r := x1)
              (q := (MvPolynomial.C (-β * a) * x0 ^ 1) * x1 ^ 0)
              h1 (isQuadratic_C_mul_pow_pow (-β * a) 1 0 (by omega))
          have hEq :
              ((1 : Poly) + β • (x0 * x1 : Poly)) * ((MvPolynomial.C a * x0 ^ 0) * x1 ^ 0) +
                  x1 * ((MvPolynomial.C (-β * a) * x0 ^ 1) * x1 ^ 0) =
                (MvPolynomial.C a : Poly) := by
            simp [MvPolynomial.smul_eq_C_mul]
            ring
          rw [← hEq]
          exact inAdmissibleImage_add u himg2 himg1
    · have hfour : e0 + e1 = 4 := by omega
      by_cases hy2 : 2 ≤ e1
      · have hmul :
            x1 ^ 2 * ((MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 2))
              = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
          calc
            x1 ^ 2 * ((MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 2))
                = MvPolynomial.C a * x0 ^ e0 * (x1 ^ 2 * x1 ^ (e1 - 2)) := by
                    ring_nf
            _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                  rw [← pow_add, Nat.add_sub_of_le hy2]
        simpa [monomial_fin2_eq, e0, e1, hmul] using
          (inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c3) (r := x1 ^ 2)
            (q := (MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 2))
            h3 (isQuadratic_C_mul_pow_pow a e0 (e1 - 2) (by omega)))
      · have hy1 : e1 = 1 := by
          have hyle : e1 ≤ 1 := by omega
          by_cases hy0 : e1 = 0
          · have hx4 : e0 = 4 := by omega
            apply False.elim
            apply hne40
            ext i
            fin_cases i <;> simp [m40, e0, e1, hx4, hy0]
          · omega
        have hx3 : e0 = 3 := by omega
        rw [monomial_fin2_eq]
        simp [e0, e1, hx3, hy1]
        have himg2 :
            InAdmissibleImage u
              (((1 : Poly) + β • (x0 * x1 : Poly)) * ((MvPolynomial.C (a / β) * x0 ^ 2) * x1 ^ 0)) := by
          exact inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c2) (r := (1 : Poly) + β • (x0 * x1 : Poly))
            (q := (MvPolynomial.C (a / β) * x0 ^ 2) * x1 ^ 0)
            h2 (isQuadratic_C_mul_pow_pow (a / β) 2 0 (by omega))
        have himg0 :
            InAdmissibleImage u
              (x0 * ((MvPolynomial.C (-(a / β)) * x0 ^ 1) * x1 ^ 0)) := by
            exact inAdmissibleImage_of_relation_mul_low
              (u := u) (c := c0) (r := x0)
              (q := (MvPolynomial.C (-(a / β)) * x0 ^ 1) * x1 ^ 0)
              h0 (isQuadratic_C_mul_pow_pow (-(a / β)) 1 0 (by omega))
        have hEq :
            ((1 : Poly) + β • (x0 * x1 : Poly)) *
                ((MvPolynomial.C (a / β) * x0 ^ 2) * x1 ^ 0) +
                x0 * ((MvPolynomial.C (-(a / β)) * x0 ^ 1) * x1 ^ 0) =
              (MvPolynomial.C a * x0 ^ 3 * x1 : Poly) := by
          have hC :
              (MvPolynomial.C β : Poly) * MvPolynomial.C a * MvPolynomial.C β⁻¹ =
                MvPolynomial.C a := by
            rw [← MvPolynomial.C_mul, ← MvPolynomial.C_mul]
            congr 1
            field_simp [hβ]
          simp [MvPolynomial.smul_eq_C_mul, pow_succ, div_eq_mul_inv]
          ring_nf
          have hMain :
              MvPolynomial.C β * x0 ^ 3 * x1 * MvPolynomial.C a * MvPolynomial.C β⁻¹ =
                (x0 ^ 3 * x1 * MvPolynomial.C a : Poly) := by
            calc
              MvPolynomial.C β * x0 ^ 3 * x1 * MvPolynomial.C a * MvPolynomial.C β⁻¹
                  = x0 ^ 3 * x1 * ((MvPolynomial.C β : Poly) * MvPolynomial.C a * MvPolynomial.C β⁻¹) := by
                      ring
              _ = x0 ^ 3 * x1 * MvPolynomial.C a := by rw [hC]
          simpa using hMain
        rw [← hEq]
        exact inAdmissibleImage_add u himg2 himg0
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
        have hscoeff : MvPolynomial.coeff s p ≠ 0 :=
          MvPolynomial.mem_support_iff.mp (hsub s (by simp))
        have hsne40 : s ≠ m40 := by
          intro hs'
          apply hscoeff
          simpa [hs'] using h40
        exact monomialImage s (MvPolynomial.coeff s p) hsdeg hsne40
      · intro t ht
        exact hsub t (by simp [ht])
  exact hP (fun s hs => hs)

theorem quartic_in_image_of_relations_x0_x1_onePlusX0x1_x1sq_of_coeff_m40_zero
    {u : RankFourVec}
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
    (h2 : ∑ i : Fin 4, c2 i • u i = (1 : Poly) + x0 * x1)
    (h3 : ∑ i : Fin 4, c3 i • u i = x1 ^ 2)
    {p : Poly} (hp : IsQuartic p)
    (h40 : MvPolynomial.coeff m40 p = 0) :
    InAdmissibleImage u p := by
  exact quartic_in_image_of_relations_x0_x1_onePlusBX0x1_x1sq_of_coeff_m40_zero
    (β := 1) (by norm_num) h0 h1 (by simpa using h2) h3 hp h40

private def commonFactorAffineQuarticKerLeft
    (c0 c1 : Fin 4 → ℝ) (t : ℝ) : RankFourVec :=
  relationDirection (-c1) (t • (x0 ^ 2)) +
    relationDirection c0 (t • (x0 * x1))

private theorem commonFactorAffineQuarticKerLeft_admissible
    (c0 c1 : Fin 4 → ℝ) (t : ℝ) :
    IsAdmissibleDirection (commonFactorAffineQuarticKerLeft c0 c1 t) := by
  refine isAdmissibleDirection_add
    (relationDirection_admissible (-c1)
      ((MvPolynomial.totalDegree_smul_le t (x0 ^ 2 : Poly)).trans (by simp [x0]))) ?_
  exact relationDirection_admissible c0
    ((MvPolynomial.totalDegree_smul_le t (x0 * x1 : Poly)).trans isQuadratic_x0_mul_x1)

private theorem commonFactorAffineQuarticKerLeft_inKer
    {u : RankFourVec} {c0 c1 : Fin 4 → ℝ} {t : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1) :
    InAdmissibleKer u (commonFactorAffineQuarticKerLeft c0 c1 t) := by
  refine ⟨commonFactorAffineQuarticKerLeft_admissible c0 c1 t, ?_⟩
  rw [commonFactorAffineQuarticKerLeft, A_add_right_local, A_relationDirection, A_relationDirection]
  simp [Pi.neg_apply, h0, h1]
  ring_nf

private theorem coeff_m40_sigma_commonFactorAffineQuarticKerLeft
    (c0 c1 : Fin 4 → ℝ) (t : ℝ) :
    MvPolynomial.coeff m40 (sigma (commonFactorAffineQuarticKerLeft c0 c1 t)) =
      (∑ i : Fin 4, (c1 i) ^ 2) * t ^ 2 := by
  have hcoord : ∀ i : Fin 4,
      MvPolynomial.coeff m40 ((commonFactorAffineQuarticKerLeft c0 c1 t i) ^ 2) = ((c1 i) * t) ^ 2 := by
    intro i
    rw [coeff_m40_sq_of_quadratic_eq _ ((commonFactorAffineQuarticKerLeft_admissible c0 c1 t) i)]
    change (MvPolynomial.coeff m20
      (relationDirection (-c1) (t • (x0 ^ 2)) i + relationDirection c0 (t • (x0 * x1)) i)) ^ 2
        = ((c1 i) * t) ^ 2
    rw [MvPolynomial.coeff_add]
    have hx0sq :
        MvPolynomial.coeff m20 (relationDirection (-c1) (t • (x0 ^ 2)) i) = -(c1 i) * t := by
      calc
        MvPolynomial.coeff m20 (relationDirection (-c1) (t • (x0 ^ 2)) i)
            = MvPolynomial.coeff m20 (((-(c1 i)) * t) • (x0 ^ 2 : Poly)) := by
                simp [relationDirection, smul_smul]
        _ = -(c1 i) * t := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using coeff_m20_smul_x0_sq ((-(c1 i)) * t)
    have hxy :
        MvPolynomial.coeff m20 (relationDirection c0 (t • (x0 * x1)) i) = 0 := by
      calc
        MvPolynomial.coeff m20 (relationDirection c0 (t • (x0 * x1)) i)
            = MvPolynomial.coeff m20 (((c0 i) * t) • (x0 * x1 : Poly)) := by
                simp [relationDirection, smul_smul]
        _ = 0 := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using coeff_m20_smul_x0_mul_x1 ((c0 i) * t)
    rw [hx0sq, hxy]
    ring
  rw [sigma, Fin.sum_univ_four]
  repeat' rw [MvPolynomial.coeff_add]
  rw [hcoord 0, hcoord 1, hcoord 2, hcoord 3]
  rw [Fin.sum_univ_four]
  ring_nf

theorem residual_eq_zero_of_relations_x0_x1_onePlusBX0x1_x1sq
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    {β : ℝ}
    (hβ : β ≠ 0)
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
    (h2 : ∑ i : Fin 4, c2 i • u i = (1 : Poly) + β • (x0 * x1 : Poly))
    (h3 : ∑ i : Fin 4, c3 i • u i = x1 ^ 2)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  rcases hp with ⟨hpquartic, k, qs, hqdeg, hpq⟩
  let s40 : ℝ := ∑ i : Fin k, (MvPolynomial.coeff m20 (qs i)) ^ 2
  let alpha40 : ℝ := ∑ i : Fin 4, (c1 i) ^ 2
  let t40 : ℝ := Real.sqrt (s40 / alpha40)
  let w40 : RankFourVec := commonFactorAffineQuarticKerLeft c0 c1 t40
  have hs40_nonneg : 0 ≤ s40 := by
    dsimp [s40]
    positivity
  have hc1_ne : c1 ≠ 0 := by
    intro hc1
    have : (0 : Poly) = x1 := by
      simpa [hc1] using h1
    have hcoeff := congrArg (MvPolynomial.coeff m01) this
    simp [x1, m01] at hcoeff
  have halpha40_pos : 0 < alpha40 := sum_sq_pos_of_ne_zero c1 hc1_ne
  have halpha40_nonneg : 0 ≤ alpha40 := le_of_lt halpha40_pos
  have hsdiv40_nonneg : 0 ≤ s40 / alpha40 := by
    exact div_nonneg hs40_nonneg halpha40_nonneg
  have hp40 : MvPolynomial.coeff m40 p = s40 := by
    rw [hpq, MvPolynomial.coeff_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact coeff_m40_sq_of_quadratic_eq (qs i) (hqdeg i)
  have hw40ker : InAdmissibleKer u w40 := by
    dsimp [w40]
    exact commonFactorAffineQuarticKerLeft_inKer h0 h1
  have hw40 : MvPolynomial.coeff m40 (sigma w40) = s40 := by
    change MvPolynomial.coeff m40 (sigma (commonFactorAffineQuarticKerLeft c0 c1 t40)) = s40
    calc
      MvPolynomial.coeff m40 (sigma (commonFactorAffineQuarticKerLeft c0 c1 t40)) =
          alpha40 * t40 ^ 2 := by
            exact coeff_m40_sigma_commonFactorAffineQuarticKerLeft c0 c1 t40
      _ = alpha40 * (s40 / alpha40) := by
            dsimp [t40]
            rw [Real.sq_sqrt hsdiv40_nonneg]
      _ = s40 := by
            field_simp [alpha40, halpha40_pos.ne']
  have hquartic_sub : IsQuartic (p - sigma w40) := by
    calc
      (p - sigma w40).totalDegree ≤ max p.totalDegree (sigma w40).totalDegree := by
        exact MvPolynomial.totalDegree_sub _ _
      _ ≤ 4 := by
        exact max_le hpquartic (isQuartic_sigma_of_admissible hw40ker.1)
  have h40_sub : MvPolynomial.coeff m40 (p - sigma w40) = 0 := by
    rw [MvPolynomial.coeff_sub, hp40, hw40]
    ring
  have himg : InAdmissibleImage u (p - sigma w40) :=
    quartic_in_image_of_relations_x0_x1_onePlusBX0x1_x1sq_of_coeff_m40_zero
      hβ h0 h1 h2 h3 hquartic_sub h40_sub
  refine admissible_image_plus_cone_residual_eq_zero (B := B)
    (u := u) (uImg := u)
    hu hsocp
    (imageOrthogonalResidual_self (B := B) hsocp.1) ?_
  refine ⟨p - sigma w40, {w40}, himg, ?_, ?_⟩
  · intro w hw
    simp at hw
    subst hw
    exact hw40ker
  · simp

theorem residual_eq_zero_of_relations_x0_x1_onePlusX0x1_x1sq
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
    (h2 : ∑ i : Fin 4, c2 i • u i = (1 : Poly) + x0 * x1)
    (h3 : ∑ i : Fin 4, c3 i • u i = x1 ^ 2)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_relations_x0_x1_onePlusBX0x1_x1sq
    (β := 1) (by norm_num) hu h0 h1 (by simpa using h2) h3 hp hsocp

theorem residual_eq_zero_of_equiv_relations_x0_x1_onePlusBX0x1_x1sq
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    {β : ℝ}
    (hβ : β ≠ 0)
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1)
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = (1 : Poly) + β • (x0 * x1 : Poly))
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = x1 ^ 2) :
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
    exact residual_eq_zero_of_relations_x0_x1_onePlusBX0x1_x1sq
      (B := B0) (u := mapVec e.toAlgHom u) hβ hu0 h0 h1 h2 h3 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_equiv_relations_x0_x1_onePlusX0x1_x1sq
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
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1)
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = (1 : Poly) + x0 * x1)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = x1 ^ 2) :
    residual p u = 0 := by
  exact residual_eq_zero_of_equiv_relations_x0_x1_onePlusBX0x1_x1sq
    (e := e) (heQuad := heQuad) (heQuadSymm := heQuadSymm) (heQuartic := heQuartic)
    (β := 1) (by norm_num) hB hp hu hsocp h0 h1 (by simpa using h2) h3

theorem residual_eq_zero_of_relations_affinePair_onePlusBX0x1_x1sq
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    {β : ℝ}
    (hβ : β ≠ 0)
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {r0 r1 : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = affineLinePoly r0 1 0)
    (h1 : ∑ i : Fin 4, c1 i • u i = affineLinePoly r1 0 1)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q2 =
      (1 : Poly) + β • (x0 * x1 : Poly))
    (hq3 : affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q3 = x1 ^ 2)
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
  have heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q) := by
    intro q hq
    exact isQuadratic_affineEquiv
      (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
      (by simp) (by simp)
      (by
        intro i
        fin_cases i <;> simp [b, b'])
      (by
        intro i
        fin_cases i <;> simp [b, b']) hq
  have heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q) := by
    intro q hq
    exact isQuadratic_affineEquiv_symm
      (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
      (by simp) (by simp)
      (by
        intro i
        fin_cases i <;> simp [b, b'])
      (by
        intro i
        fin_cases i <;> simp [b, b']) hq
  have heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q) := by
    intro q hq
    exact isQuartic_affineEquiv
      (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
      (by simp) (by simp)
      (by
        intro i
        fin_cases i <;> simp [b, b'])
      (by
        intro i
        fin_cases i <;> simp [b, b']) hq
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  have h0trans : e (affineLinePoly r0 1 0) = x0 := by
    simp [e, b, b', affineLinePoly, affineEquiv, affineHom, affineImage, x0, x1,
      Fin.sum_univ_two]
  have h1trans : e (affineLinePoly r1 0 1) = x1 := by
    simp [e, b, b', affineLinePoly, affineEquiv, affineHom, affineImage, x0, x1,
      Fin.sum_univ_two]
  have h0' :
      ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0 := by
    simpa [e] using (relation_map e.toAlgHom h0).trans h0trans
  have h1' :
      ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1 := by
    simpa [e] using (relation_map e.toAlgHom h1).trans h1trans
  have h2' :
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = (1 : Poly) + β • (x0 * x1 : Poly) := by
    simpa [e, b] using (relation_map e.toAlgHom h2).trans hq2
  have h3' :
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = x1 ^ 2 := by
    simpa [e, b] using (relation_map e.toAlgHom h3).trans hq3
  exact residual_eq_zero_of_equiv_relations_x0_x1_onePlusBX0x1_x1sq
    (e := e) (heQuad := fun {_} hq => heQuad hq) (heQuadSymm := fun {_} hq => heQuadSymm hq)
    (heQuartic := fun {_} hq => heQuartic hq)
    hβ hB hp hu hsocp h0' h1' h2' h3'

theorem residual_eq_zero_of_relations_affinePair_onePlusX0x1_x1sq
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {r0 r1 : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = affineLinePoly r0 1 0)
    (h1 : ∑ i : Fin 4, c1 i • u i = affineLinePoly r1 0 1)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q2 = (1 : Poly) + x0 * x1)
    (hq3 : affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q3 = x1 ^ 2)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_relations_affinePair_onePlusBX0x1_x1sq
    (β := 1) (by norm_num) hu h0 h1 h2 h3 (by simpa using hq2) hq3 hp hsocp

theorem residual_eq_zero_of_relations_x0_x1_x0sq_x0x1Plane
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
    {a b c d : ℝ}
    (h2 : ∑ i : Fin 4, c2 i • u i = a • (x0 ^ 2 : Poly) + b • (x0 * x1))
    (h3 : ∑ i : Fin 4, c3 i • u i = c • (x0 ^ 2 : Poly) + d • (x0 * x1))
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
          = (d / det) • (a • (x0 ^ 2 : Poly) + b • (x0 * x1)) +
              (-b / det) • (c • (x0 ^ 2 : Poly) + d • (x0 * x1)) := by
                simp [c2', det, relation_linearCombination_low, h2, h3]
      _ = ((d / det) * a + (-b / det) * c) • (x0 ^ 2 : Poly) +
            ((d / det) * b + (-b / det) * d) • (x0 * x1) := by
              simp [smul_add, smul_smul, add_smul, add_assoc, add_left_comm, mul_comm]
      _ = x0 ^ 2 := by
            rw [hcoeff20, hcoeff21]
            simp
  have h3' : ∑ i : Fin 4, c3' i • u i = x0 * x1 := by
    calc
      ∑ i : Fin 4, c3' i • u i
          = (-c / det) • (a • (x0 ^ 2 : Poly) + b • (x0 * x1)) +
              (a / det) • (c • (x0 ^ 2 : Poly) + d • (x0 * x1)) := by
                simp [c3', det, relation_linearCombination_low, h2, h3]
      _ = ((-c / det) * a + (a / det) * c) • (x0 ^ 2 : Poly) +
            ((-c / det) * b + (a / det) * d) • (x0 * x1) := by
              simp [smul_add, smul_smul, add_smul, add_assoc, add_left_comm, add_comm, mul_comm]
      _ = x0 * x1 := by
            rw [hcoeff30, hcoeff31]
            simp
  exact residual_eq_zero_of_relations_x0_x1_x0sq_x0x1
    (B := B) (u := u) hu h0 h1 h2' h3' hp hsocp

theorem residual_eq_zero_of_equiv_relations_x0_x1_x0sq_x0x1Plane
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
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1)
    {a b c d : ℝ}
    (h2 :
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i =
        a • (x0 ^ 2 : Poly) + b • (x0 * x1))
    (h3 :
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i =
        c • (x0 ^ 2 : Poly) + d • (x0 * x1))
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
    exact residual_eq_zero_of_relations_x0_x1_x0sq_x0x1Plane
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0 h1 h2 h3 hdet hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_linearPair_x0sq_x0x1Plane
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {a b c d : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = linearForm a b)
    (h1 : ∑ i : Fin 4, c1 i • u i = linearForm c d)
    (hdetLin : a * d - b * c ≠ 0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    {r s t w : ℝ}
    (hq2 :
      linearPairEquiv a b c d hdetLin q2 =
        r • (x0 ^ 2 : Poly) + s • (x0 * x1 : Poly))
    (hq3 :
      linearPairEquiv a b c d hdetLin q3 =
        t • (x0 ^ 2 : Poly) + w • (x0 * x1 : Poly))
    (hdetPlane : r * w - s * t ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let e : Poly ≃ₐ[ℝ] Poly := linearPairEquiv a b c d hdetLin
  have heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q) := by
    intro q hq
    exact isQuadratic_affineEquiv
      (linearPairMatrix a b c d) (linearPairInvMatrix a b c d) 0 0
      (linearPair_mul_inv a b c d hdetLin) (linearPair_inv_mul a b c d hdetLin)
      (by intro i; simp) (by intro i; simp) hq
  have heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q) := by
    intro q hq
    exact isQuadratic_affineEquiv_symm
      (linearPairMatrix a b c d) (linearPairInvMatrix a b c d) 0 0
      (linearPair_mul_inv a b c d hdetLin) (linearPair_inv_mul a b c d hdetLin)
      (by intro i; simp) (by intro i; simp) hq
  have heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q) := by
    intro q hq
    exact isQuartic_affineEquiv
      (linearPairMatrix a b c d) (linearPairInvMatrix a b c d) 0 0
      (linearPair_mul_inv a b c d hdetLin) (linearPair_inv_mul a b c d hdetLin)
      (by intro i; simp) (by intro i; simp) hq
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  have h0' : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0 := by
    simpa [e, linearPairEquiv] using
      (relation_map e.toAlgHom h0).trans (affineHom_linearPair_left a b c d hdetLin)
  have h1' : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1 := by
    simpa [e, linearPairEquiv] using
      (relation_map e.toAlgHom h1).trans (affineHom_linearPair_right a b c d hdetLin)
  have h2' :
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i =
        r • (x0 ^ 2 : Poly) + s • (x0 * x1 : Poly) := by
    simpa [e] using (relation_map e.toAlgHom h2).trans hq2
  have h3' :
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i =
        t • (x0 ^ 2 : Poly) + w • (x0 * x1 : Poly) := by
    simpa [e] using (relation_map e.toAlgHom h3).trans hq3
  exact residual_eq_zero_of_equiv_relations_x0_x1_x0sq_x0x1Plane
    (e := e) (heQuad := fun {_} hq => heQuad hq) (heQuadSymm := fun {_} hq => heQuadSymm hq)
    (heQuartic := fun {_} hq => heQuartic hq)
    hB hp hu hsocp h0' h1' h2' h3' hdetPlane

private def lowAffineSwapEquiv : Poly ≃ₐ[ℝ] Poly :=
  linearPairEquiv 0 1 1 0 (by norm_num)

@[simp] private theorem lowAffineSwapEquiv_apply_x0 :
    lowAffineSwapEquiv x0 = x1 := by
  simp [lowAffineSwapEquiv, linearPairEquiv, affineEquiv, affineHom, affineImage,
    linearPairMatrix, linearPairInvMatrix, x0, x1, Fin.sum_univ_two]

@[simp] private theorem lowAffineSwapEquiv_apply_x1 :
    lowAffineSwapEquiv x1 = x0 := by
  simp [lowAffineSwapEquiv, linearPairEquiv, affineEquiv, affineHom, affineImage,
    linearPairMatrix, linearPairInvMatrix, x0, x1, Fin.sum_univ_two]

@[simp] private theorem lowAffineSwapEquiv_apply_x0x1 :
    lowAffineSwapEquiv (x0 * x1 : Poly) = x0 * x1 := by
  simp [lowAffineSwapEquiv_apply_x0, lowAffineSwapEquiv_apply_x1, mul_comm]

@[simp] private theorem lowAffineSwapEquiv_apply_x1sq :
    lowAffineSwapEquiv (x1 ^ 2 : Poly) = x0 ^ 2 := by
  simp [lowAffineSwapEquiv_apply_x1]

@[simp] private theorem lowAffineSwapEquiv_apply_x0sq :
    lowAffineSwapEquiv (x0 ^ 2 : Poly) = x1 ^ 2 := by
  simp [lowAffineSwapEquiv_apply_x0]

private theorem affineHom_x1Shear_x0sq_x0x1_plane
    (t a b : ℝ) :
    affineHom (x1ShearMatrix t) 0
      (a • (x0 ^ 2 : Poly) + b • (x0 * x1)) =
        (a + b * t) • (x0 ^ 2 : Poly) + b • (x0 * x1) := by
  simp [affineHom_x1Shear_x0, affineHom_x1Shear_x1, MvPolynomial.smul_eq_C_mul]
  ring_nf

theorem residual_eq_zero_of_relations_x0_x1_onePlusAX0sq_x0x1Plane
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
    {a b c d : ℝ}
    (h2 :
      ∑ i : Fin 4, c2 i • u i =
        (1 : Poly) + a • (x0 ^ 2 : Poly) + b • (x0 * x1))
    (h3 :
      ∑ i : Fin 4, c3 i • u i =
        c • (x0 ^ 2 : Poly) + d • (x0 * x1))
    (hdet : a * d - b * c ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  by_cases hd : d = 0
  · have hc : c ≠ 0 := by
      intro hc
      apply hdet
      simp [hd, hc]
    have hb : b ≠ 0 := by
      intro hb
      apply hdet
      simp [hd, hb]
    let c2' : Fin 4 → ℝ := fun i => c2 i + (-(a / c)) * c3 i
    let c3' : Fin 4 → ℝ := fun i => (1 / c) * c3 i
    have h2' :
        ∑ i : Fin 4, c2' i • u i = (1 : Poly) + b • (x0 * x1) := by
      have h2lin :
          ∑ i : Fin 4, c2' i • u i =
            (∑ i : Fin 4, c2 i • u i) + (-(a / c)) • (∑ i : Fin 4, c3 i • u i) := by
        simp [c2', Finset.sum_add_distrib, add_smul, Finset.smul_sum, smul_smul]
      calc
        ∑ i : Fin 4, c2' i • u i
            = ((1 : Poly) + a • (x0 ^ 2 : Poly) + b • (x0 * x1)) +
                (-(a / c)) • (c • (x0 ^ 2 : Poly) + d • (x0 * x1)) := by
                  rw [h2lin, h2, h3]
        _ = (1 : Poly) + (a + (-(a / c)) * c) • (x0 ^ 2 : Poly) +
              (b + (-(a / c)) * d) • (x0 * x1) := by
                calc
                  ((1 : Poly) + a • (x0 ^ 2 : Poly) + b • (x0 * x1)) +
                      (-(a / c)) • (c • (x0 ^ 2 : Poly) + d • (x0 * x1))
                      =
                      (1 : Poly) + a • (x0 ^ 2 : Poly) + ((-(a / c)) * c) • (x0 ^ 2 : Poly) +
                        (b • (x0 * x1) + ((-(a / c)) * d) • (x0 * x1)) := by
                          simp [smul_add, smul_smul, add_assoc, add_left_comm, add_comm]
                  _ = (1 : Poly) + (a + (-(a / c)) * c) • (x0 ^ 2 : Poly) +
                        (b + (-(a / c)) * d) • (x0 * x1) := by
                          have hsq :
                              a • (x0 ^ 2 : Poly) + ((-(a / c)) * c) • (x0 ^ 2 : Poly) =
                                (a + (-(a / c)) * c) • (x0 ^ 2 : Poly) := by
                            rw [← add_smul]
                          have hxy :
                              b • (x0 * x1 : Poly) + ((-(a / c)) * d) • (x0 * x1) =
                                (b + (-(a / c)) * d) • (x0 * x1 : Poly) := by
                            rw [← add_smul]
                          calc
                            (1 : Poly) + a • (x0 ^ 2 : Poly) + ((-(a / c)) * c) • (x0 ^ 2 : Poly) +
                                (b • (x0 * x1) + ((-(a / c)) * d) • (x0 * x1))
                                =
                                (1 : Poly) +
                                  (a • (x0 ^ 2 : Poly) + ((-(a / c)) * c) • (x0 ^ 2 : Poly)) +
                                  (b • (x0 * x1) + ((-(a / c)) * d) • (x0 * x1)) := by
                                    abel
                            _ = (1 : Poly) +
                                  (a + (-(a / c)) * c) • (x0 ^ 2 : Poly) +
                                  (b • (x0 * x1) + ((-(a / c)) * d) • (x0 * x1)) := by
                                    rw [hsq]
                            _ = (1 : Poly) + (a + (-(a / c)) * c) • (x0 ^ 2 : Poly) +
                                  (b + (-(a / c)) * d) • (x0 * x1) := by
                                    rw [hxy]
        _ = (1 : Poly) + b • (x0 * x1) := by
              have hcoef0 : a + (-(a / c)) * c = 0 := by
                field_simp [hc]
                ring
              have hcoef1 : b + (-(a / c)) * d = b := by
                simp [hd]
              rw [hcoef0, hcoef1]
              simp
    have h3' : ∑ i : Fin 4, c3' i • u i = x0 ^ 2 := by
      have h3lin :
          ∑ i : Fin 4, c3' i • u i = (1 / c) • (∑ i : Fin 4, c3 i • u i) := by
        simp [c3', Finset.smul_sum, smul_smul]
      calc
        ∑ i : Fin 4, c3' i • u i
            = (1 / c) • (c • (x0 ^ 2 : Poly) + d • (x0 * x1)) := by
                rw [h3lin, h3]
        _ = ((1 / c) * c) • (x0 ^ 2 : Poly) + ((1 / c) * d) • (x0 * x1) := by
              simp [smul_add, smul_smul]
        _ = x0 ^ 2 := by
              have hcoef0 : (1 / c) * c = 1 := by
                field_simp [hc]
              have hcoef1 : (1 / c) * d = 0 := by
                simp [hd]
              rw [hcoef0, hcoef1]
              simp
    exact residual_eq_zero_of_equiv_relations_x0_x1_onePlusBX0x1_x1sq
      (e := lowAffineSwapEquiv)
      (heQuad := fun {_} hpq =>
        isQuadratic_affineEquiv
          (linearPairMatrix 0 1 1 0) (linearPairInvMatrix 0 1 1 0) 0 0
          (linearPair_mul_inv 0 1 1 0 (by norm_num))
          (linearPair_inv_mul 0 1 1 0 (by norm_num))
          (by intro i; simp) (by intro i; simp) hpq)
      (heQuadSymm := fun {_} hpq =>
        isQuadratic_affineEquiv_symm
          (linearPairMatrix 0 1 1 0) (linearPairInvMatrix 0 1 1 0) 0 0
          (linearPair_mul_inv 0 1 1 0 (by norm_num))
          (linearPair_inv_mul 0 1 1 0 (by norm_num))
          (by intro i; simp) (by intro i; simp) hpq)
      (heQuartic := fun {_} hpq =>
        isQuartic_affineEquiv
          (linearPairMatrix 0 1 1 0) (linearPairInvMatrix 0 1 1 0) 0 0
          (linearPair_mul_inv 0 1 1 0 (by norm_num))
          (linearPair_inv_mul 0 1 1 0 (by norm_num))
          (by intro i; simp) (by intro i; simp) hpq)
      (β := b) hb hB hp hu hsocp
      ((relation_map lowAffineSwapEquiv.toAlgHom h1).trans lowAffineSwapEquiv_apply_x1)
      ((relation_map lowAffineSwapEquiv.toAlgHom h0).trans lowAffineSwapEquiv_apply_x0)
      (by
        calc
          ∑ i : Fin 4, c2' i • mapVec lowAffineSwapEquiv.toAlgHom u i
              = lowAffineSwapEquiv (∑ i : Fin 4, c2' i • u i) := by
                  simp [mapVec, map_sum]
          _ = lowAffineSwapEquiv ((1 : Poly) + b • (x0 * x1)) := by rw [h2']
          _ = (1 : Poly) + b • (x0 * x1) := by
                simp [add_comm])
      (by
        calc
          ∑ i : Fin 4, c3' i • mapVec lowAffineSwapEquiv.toAlgHom u i
              = lowAffineSwapEquiv (∑ i : Fin 4, c3' i • u i) := by
                  simp [mapVec, map_sum]
          _ = lowAffineSwapEquiv (x0 ^ 2 : Poly) := by rw [h3']
          _ = x1 ^ 2 := by simp)
  · have hd0 : d ≠ 0 := hd
    let t : ℝ := -(c / d)
    let e : Poly ≃ₐ[ℝ] Poly := x1ShearEquiv t
    let c1' : Fin 4 → ℝ := fun i => c1 i + (-t) * c0 i
    let c2' : Fin 4 → ℝ := fun i => c2 i + (-(b / d)) * c3 i
    let c3' : Fin 4 → ℝ := fun i => (1 / d) * c3 i
    let α : ℝ := a - b * c / d
    have hα : α ≠ 0 := by
      intro hα0
      apply hdet
      have hmul : a * d - b * c = α * d := by
        dsimp [α]
        field_simp [hd0]
      rw [hmul, hα0]
      simp
    have heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q) := by
      intro q hq
      exact isQuadratic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
        (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq
    have heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q) := by
      intro q hq
      exact isQuadratic_affineEquiv_symm (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
        (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq
    have heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q) := by
      intro q hq
      exact isQuartic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
        (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq
    have h0' : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0 := by
      simpa [e] using (relation_map e.toAlgHom h0).trans (affineHom_x1Shear_x0 t)
    have h1e : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = MvPolynomial.C t * x0 + x1 := by
      simpa [e] using (relation_map e.toAlgHom h1).trans (affineHom_x1Shear_x1 t)
    have h1' : ∑ i : Fin 4, c1' i • mapVec e.toAlgHom u i = x1 := by
      calc
        ∑ i : Fin 4, c1' i • mapVec e.toAlgHom u i
            = 1 • (MvPolynomial.C t * x0 + x1) + (-t) • x0 := by
                simpa [c1'] using relation_linearCombination_low h1e h0' (1 : ℝ) (-t)
        _ = x1 := by
              simp [x0, MvPolynomial.smul_eq_C_mul, add_assoc, add_left_comm]
    have h2e :
        ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i =
          (1 : Poly) + (a + b * t) • (x0 ^ 2 : Poly) + b • (x0 * x1) := by
      calc
        ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = e ((1 : Poly) + a • (x0 ^ 2 : Poly) + b • (x0 * x1)) := by
            simpa using relation_map e.toAlgHom h2
        _ = affineHom (x1ShearMatrix t) 0 ((1 : Poly) + a • (x0 ^ 2 : Poly) + b • (x0 * x1)) := by
            rfl
        _ = affineHom (x1ShearMatrix t) 0 (1 : Poly) +
              affineHom (x1ShearMatrix t) 0 (a • (x0 ^ 2 : Poly) + b • (x0 * x1)) := by
            simp [add_assoc]
        _ = (1 : Poly) + (a + b * t) • (x0 ^ 2 : Poly) + b • (x0 * x1) := by
            rw [affineHom_x1Shear_x0sq_x0x1_plane]
            simp [add_assoc]
    have h3e :
        ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i =
          (c + d * t) • (x0 ^ 2 : Poly) + d • (x0 * x1) := by
      calc
        ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = e (c • (x0 ^ 2 : Poly) + d • (x0 * x1)) := by
            simpa using relation_map e.toAlgHom h3
        _ = affineHom (x1ShearMatrix t) 0 (c • (x0 ^ 2 : Poly) + d • (x0 * x1)) := by
            rfl
        _ = (c + d * t) • (x0 ^ 2 : Poly) + d • (x0 * x1) := by
            rw [affineHom_x1Shear_x0sq_x0x1_plane]
    have h2'' :
        ∑ i : Fin 4, c2' i • mapVec e.toAlgHom u i = (1 : Poly) + α • (x0 ^ 2 : Poly) := by
      have h2lin :
          ∑ i : Fin 4, c2' i • mapVec e.toAlgHom u i =
            (∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i) +
              (-(b / d)) • (∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i) := by
        simp [c2', Finset.sum_add_distrib, add_smul, Finset.smul_sum, smul_smul]
      calc
        ∑ i : Fin 4, c2' i • mapVec e.toAlgHom u i
            = ((1 : Poly) + (a + b * t) • (x0 ^ 2 : Poly) + b • (x0 * x1)) +
                (-(b / d)) • ((c + d * t) • (x0 ^ 2 : Poly) + d • (x0 * x1)) := by
                  rw [h2lin, h2e, h3e]
        _ = (1 : Poly) +
              ((a + b * t) + (-(b / d)) * (c + d * t)) • (x0 ^ 2 : Poly) +
              (b + (-(b / d)) * d) • (x0 * x1) := by
                calc
                  ((1 : Poly) + (a + b * t) • (x0 ^ 2 : Poly) + b • (x0 * x1)) +
                      (-(b / d)) • ((c + d * t) • (x0 ^ 2 : Poly) + d • (x0 * x1))
                      =
                      (1 : Poly) + (a + b * t) • (x0 ^ 2 : Poly) +
                        ((-(b / d)) * (c + d * t)) • (x0 ^ 2 : Poly) +
                        (b • (x0 * x1) + ((-(b / d)) * d) • (x0 * x1)) := by
                          simp [smul_add, smul_smul, add_assoc, add_left_comm, add_comm]
                  _ = (1 : Poly) +
                        ((a + b * t) + (-(b / d)) * (c + d * t)) • (x0 ^ 2 : Poly) +
                        (b + (-(b / d)) * d) • (x0 * x1) := by
                          have hsq :
                              (a + b * t) • (x0 ^ 2 : Poly) +
                                  ((-(b / d)) * (c + d * t)) • (x0 ^ 2 : Poly) =
                                ((a + b * t) + (-(b / d)) * (c + d * t)) • (x0 ^ 2 : Poly) := by
                            rw [← add_smul]
                          have hxy :
                              b • (x0 * x1 : Poly) + ((-(b / d)) * d) • (x0 * x1) =
                                (b + (-(b / d)) * d) • (x0 * x1 : Poly) := by
                            rw [← add_smul]
                          calc
                            (1 : Poly) + (a + b * t) • (x0 ^ 2 : Poly) +
                                ((-(b / d)) * (c + d * t)) • (x0 ^ 2 : Poly) +
                                (b • (x0 * x1) + ((-(b / d)) * d) • (x0 * x1))
                                =
                                (1 : Poly) +
                                  ((a + b * t) • (x0 ^ 2 : Poly) +
                                    ((-(b / d)) * (c + d * t)) • (x0 ^ 2 : Poly)) +
                                  (b • (x0 * x1) + ((-(b / d)) * d) • (x0 * x1)) := by
                                    abel
                            _ = (1 : Poly) +
                                  ((a + b * t) + (-(b / d)) * (c + d * t)) • (x0 ^ 2 : Poly) +
                                  (b • (x0 * x1) + ((-(b / d)) * d) • (x0 * x1)) := by
                                    rw [hsq]
                            _ = (1 : Poly) +
                                  ((a + b * t) + (-(b / d)) * (c + d * t)) • (x0 ^ 2 : Poly) +
                                  (b + (-(b / d)) * d) • (x0 * x1) := by
                                    rw [hxy]
        _ = (1 : Poly) + α • (x0 ^ 2 : Poly) := by
              have hcoef0 :
                  (a + b * t) + (-(b / d)) * (c + d * t) = α := by
                dsimp [α, t]
                field_simp [hd0]
                ring
              have hcoef1 : b + (-(b / d)) * d = 0 := by
                field_simp [hd0]
                ring
              rw [hcoef0, hcoef1]
              simp
    have h3'' : ∑ i : Fin 4, c3' i • mapVec e.toAlgHom u i = x0 * x1 := by
      have h3lin :
          ∑ i : Fin 4, c3' i • mapVec e.toAlgHom u i =
            (1 / d) • (∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i) := by
        simp [c3', Finset.smul_sum, smul_smul]
      calc
        ∑ i : Fin 4, c3' i • mapVec e.toAlgHom u i
            = (1 / d) • ((c + d * t) • (x0 ^ 2 : Poly) + d • (x0 * x1)) := by
                rw [h3lin, h3e]
        _ = ((1 / d) * (c + d * t)) • (x0 ^ 2 : Poly) + ((1 / d) * d) • (x0 * x1) := by
              simp [smul_add, smul_smul]
        _ = x0 * x1 := by
              have hcoef0 : (1 / d) * (c + d * t) = 0 := by
                dsimp [t]
                field_simp [hd0]
                ring
              have hcoef1 : (1 / d) * d = 1 := by
                field_simp [hd0]
              rw [hcoef0, hcoef1]
              simp
    exact residual_eq_zero_of_equiv_relations_x0_x1_onePlusAX0sq_x0x1
      (e := e) (heQuad := fun {_} hq => heQuad hq) (heQuadSymm := fun {_} hq => heQuadSymm hq)
      (heQuartic := fun {_} hq => heQuartic hq)
      (α := α) hα hB hp hu hsocp h0' h1' h2'' h3''

theorem residual_eq_zero_of_equiv_relations_x0_x1_onePlusAX0sq_x0x1Plane
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
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1)
    {a b c d : ℝ}
    (h2 :
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i =
        (1 : Poly) + a • (x0 ^ 2 : Poly) + b • (x0 * x1))
    (h3 :
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i =
        c • (x0 ^ 2 : Poly) + d • (x0 * x1))
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
    exact residual_eq_zero_of_relations_x0_x1_onePlusAX0sq_x0x1Plane
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0 h1 h2 h3 hdet hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_x0_x1_onePlusBX0x1_x1sqPlane
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
    {a b c d : ℝ}
    (h2 :
      ∑ i : Fin 4, c2 i • u i =
        (1 : Poly) + a • (x0 * x1 : Poly) + b • (x1 ^ 2 : Poly))
    (h3 :
      ∑ i : Fin 4, c3 i • u i =
        c • (x0 * x1 : Poly) + d • (x1 ^ 2 : Poly))
    (hdet : a * d - b * c ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  have h0' : ∑ i : Fin 4, c1 i • mapVec lowAffineSwapEquiv.toAlgHom u i = x0 := by
    exact (relation_map lowAffineSwapEquiv.toAlgHom h1).trans lowAffineSwapEquiv_apply_x1
  have h1' : ∑ i : Fin 4, c0 i • mapVec lowAffineSwapEquiv.toAlgHom u i = x1 := by
    exact (relation_map lowAffineSwapEquiv.toAlgHom h0).trans lowAffineSwapEquiv_apply_x0
  have h2' :
      ∑ i : Fin 4, c2 i • mapVec lowAffineSwapEquiv.toAlgHom u i =
        (1 : Poly) + b • (x0 ^ 2 : Poly) + a • (x0 * x1) := by
    calc
      ∑ i : Fin 4, c2 i • mapVec lowAffineSwapEquiv.toAlgHom u i
          = lowAffineSwapEquiv (∑ i : Fin 4, c2 i • u i) := by
              simp [mapVec, map_sum]
      _ = lowAffineSwapEquiv
            ((1 : Poly) + a • (x0 * x1 : Poly) + b • (x1 ^ 2 : Poly)) := by
            rw [h2]
      _ = (1 : Poly) + b • (x0 ^ 2 : Poly) + a • (x0 * x1) := by
            simp [add_comm, add_left_comm]
  have h3' :
      ∑ i : Fin 4, c3 i • mapVec lowAffineSwapEquiv.toAlgHom u i =
        d • (x0 ^ 2 : Poly) + c • (x0 * x1) := by
    calc
      ∑ i : Fin 4, c3 i • mapVec lowAffineSwapEquiv.toAlgHom u i
          = lowAffineSwapEquiv (∑ i : Fin 4, c3 i • u i) := by
              simp [mapVec, map_sum]
      _ = lowAffineSwapEquiv (c • (x0 * x1 : Poly) + d • (x1 ^ 2 : Poly)) := by
            rw [h3]
      _ = d • (x0 ^ 2 : Poly) + c • (x0 * x1) := by
            simp [add_comm]
  have hdet' : b * c - a * d ≠ 0 := by
    intro hdet'
    apply hdet
    linarith
  exact residual_eq_zero_of_equiv_relations_x0_x1_onePlusAX0sq_x0x1Plane
    (e := lowAffineSwapEquiv)
    (heQuad := fun {_} hpq =>
      isQuadratic_affineEquiv
        (linearPairMatrix 0 1 1 0) (linearPairInvMatrix 0 1 1 0) 0 0
        (linearPair_mul_inv 0 1 1 0 (by norm_num))
        (linearPair_inv_mul 0 1 1 0 (by norm_num))
        (by intro i; simp) (by intro i; simp) hpq)
    (heQuadSymm := fun {_} hpq =>
      isQuadratic_affineEquiv_symm
        (linearPairMatrix 0 1 1 0) (linearPairInvMatrix 0 1 1 0) 0 0
        (linearPair_mul_inv 0 1 1 0 (by norm_num))
        (linearPair_inv_mul 0 1 1 0 (by norm_num))
        (by intro i; simp) (by intro i; simp) hpq)
    (heQuartic := fun {_} hpq =>
      isQuartic_affineEquiv
        (linearPairMatrix 0 1 1 0) (linearPairInvMatrix 0 1 1 0) 0 0
        (linearPair_mul_inv 0 1 1 0 (by norm_num))
        (linearPair_inv_mul 0 1 1 0 (by norm_num))
        (by intro i; simp) (by intro i; simp) hpq)
    (B := B) (p := p) (u := u)
    hB hp hu hsocp h0' h1' h2' h3' hdet'

theorem residual_eq_zero_of_relations_x0_x1_x0x1_x1sqPlane
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
    {a b c d : ℝ}
    (h2 : ∑ i : Fin 4, c2 i • u i = a • (x0 * x1 : Poly) + b • (x1 ^ 2 : Poly))
    (h3 : ∑ i : Fin 4, c3 i • u i = c • (x0 * x1 : Poly) + d • (x1 ^ 2 : Poly))
    (hdet : a * d - b * c ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  have h0' : ∑ i : Fin 4, c1 i • mapVec lowAffineSwapEquiv.toAlgHom u i = x0 := by
    exact (relation_map lowAffineSwapEquiv.toAlgHom h1).trans lowAffineSwapEquiv_apply_x1
  have h1' : ∑ i : Fin 4, c0 i • mapVec lowAffineSwapEquiv.toAlgHom u i = x1 := by
    exact (relation_map lowAffineSwapEquiv.toAlgHom h0).trans lowAffineSwapEquiv_apply_x0
  have h2' :
      ∑ i : Fin 4, c2 i • mapVec lowAffineSwapEquiv.toAlgHom u i =
        b • (x0 ^ 2 : Poly) + a • (x0 * x1) := by
    calc
      ∑ i : Fin 4, c2 i • mapVec lowAffineSwapEquiv.toAlgHom u i
          = lowAffineSwapEquiv (∑ i : Fin 4, c2 i • u i) := by
              simp [mapVec, map_sum]
      _ = lowAffineSwapEquiv (a • (x0 * x1 : Poly) + b • (x1 ^ 2 : Poly)) := by
            rw [h2]
      _ = b • (x0 ^ 2 : Poly) + a • (x0 * x1) := by
            simp [add_comm]
  have h3' :
      ∑ i : Fin 4, c3 i • mapVec lowAffineSwapEquiv.toAlgHom u i =
        d • (x0 ^ 2 : Poly) + c • (x0 * x1) := by
    calc
      ∑ i : Fin 4, c3 i • mapVec lowAffineSwapEquiv.toAlgHom u i
          = lowAffineSwapEquiv (∑ i : Fin 4, c3 i • u i) := by
              simp [mapVec, map_sum]
      _ = lowAffineSwapEquiv (c • (x0 * x1 : Poly) + d • (x1 ^ 2 : Poly)) := by
            rw [h3]
      _ = d • (x0 ^ 2 : Poly) + c • (x0 * x1) := by
            simp [add_comm]
  have hdet' : b * c - a * d ≠ 0 := by
    intro hdet'
    apply hdet
    linarith
  exact residual_eq_zero_of_equiv_relations_x0_x1_x0sq_x0x1Plane
    (e := lowAffineSwapEquiv)
    (heQuad := fun {_} hpq =>
      isQuadratic_affineEquiv
        (linearPairMatrix 0 1 1 0) (linearPairInvMatrix 0 1 1 0) 0 0
        (linearPair_mul_inv 0 1 1 0 (by norm_num))
        (linearPair_inv_mul 0 1 1 0 (by norm_num))
        (by intro i; simp) (by intro i; simp) hpq)
    (heQuadSymm := fun {_} hpq =>
      isQuadratic_affineEquiv_symm
        (linearPairMatrix 0 1 1 0) (linearPairInvMatrix 0 1 1 0) 0 0
        (linearPair_mul_inv 0 1 1 0 (by norm_num))
        (linearPair_inv_mul 0 1 1 0 (by norm_num))
        (by intro i; simp) (by intro i; simp) hpq)
    (heQuartic := fun {_} hpq =>
      isQuartic_affineEquiv
        (linearPairMatrix 0 1 1 0) (linearPairInvMatrix 0 1 1 0) 0 0
        (linearPair_mul_inv 0 1 1 0 (by norm_num))
        (linearPair_inv_mul 0 1 1 0 (by norm_num))
        (by intro i; simp) (by intro i; simp) hpq)
    (B := B) (p := p) (u := u)
    hB hp hu hsocp h0' h1' h2' h3' hdet'

theorem residual_eq_zero_of_equiv_relations_x0_x1_x0x1_x1sqPlane
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
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1)
    {a b c d : ℝ}
    (h2 :
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i =
        a • (x0 * x1 : Poly) + b • (x1 ^ 2 : Poly))
    (h3 :
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i =
        c • (x0 * x1 : Poly) + d • (x1 ^ 2 : Poly))
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
    exact residual_eq_zero_of_relations_x0_x1_x0x1_x1sqPlane
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0 h1 h2 h3 hdet hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_linearPair_x0x1_x1sqPlane
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {a b c d : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = linearForm a b)
    (h1 : ∑ i : Fin 4, c1 i • u i = linearForm c d)
    (hdetLin : a * d - b * c ≠ 0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    {r s t w : ℝ}
    (hq2 :
      linearPairEquiv a b c d hdetLin q2 =
        r • (x0 * x1 : Poly) + s • (x1 ^ 2 : Poly))
    (hq3 :
      linearPairEquiv a b c d hdetLin q3 =
        t • (x0 * x1 : Poly) + w • (x1 ^ 2 : Poly))
    (hdetPlane : r * w - s * t ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let e : Poly ≃ₐ[ℝ] Poly := linearPairEquiv a b c d hdetLin
  have heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q) := by
    intro q hq
    exact isQuadratic_affineEquiv
      (linearPairMatrix a b c d) (linearPairInvMatrix a b c d) 0 0
      (linearPair_mul_inv a b c d hdetLin) (linearPair_inv_mul a b c d hdetLin)
      (by intro i; simp) (by intro i; simp) hq
  have heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q) := by
    intro q hq
    exact isQuadratic_affineEquiv_symm
      (linearPairMatrix a b c d) (linearPairInvMatrix a b c d) 0 0
      (linearPair_mul_inv a b c d hdetLin) (linearPair_inv_mul a b c d hdetLin)
      (by intro i; simp) (by intro i; simp) hq
  have heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q) := by
    intro q hq
    exact isQuartic_affineEquiv
      (linearPairMatrix a b c d) (linearPairInvMatrix a b c d) 0 0
      (linearPair_mul_inv a b c d hdetLin) (linearPair_inv_mul a b c d hdetLin)
      (by intro i; simp) (by intro i; simp) hq
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  have h0' : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0 := by
    simpa [e, linearPairEquiv] using
      (relation_map e.toAlgHom h0).trans (affineHom_linearPair_left a b c d hdetLin)
  have h1' : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1 := by
    simpa [e, linearPairEquiv] using
      (relation_map e.toAlgHom h1).trans (affineHom_linearPair_right a b c d hdetLin)
  have h2' :
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i =
        r • (x0 * x1 : Poly) + s • (x1 ^ 2 : Poly) := by
    simpa [e] using (relation_map e.toAlgHom h2).trans hq2
  have h3' :
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i =
        t • (x0 * x1 : Poly) + w • (x1 ^ 2 : Poly) := by
    simpa [e] using (relation_map e.toAlgHom h3).trans hq3
  exact residual_eq_zero_of_equiv_relations_x0_x1_x0x1_x1sqPlane
    (e := e) (heQuad := fun {_} hq => heQuad hq) (heQuadSymm := fun {_} hq => heQuadSymm hq)
    (heQuartic := fun {_} hq => heQuartic hq)
    hB hp hu hsocp h0' h1' h2' h3' hdetPlane

def lowHomQuadPlaneA (q2 q3 : Poly) : ℝ :=
  MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
    MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3

def lowHomQuadPlaneB (q2 q3 : Poly) : ℝ :=
  MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m02 q3 -
    MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3

def lowHomQuadPlaneC (q2 q3 : Poly) : ℝ :=
  MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m11 q3 -
    MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m20 q3

/-- A pair of homogeneous quadratics spans a genuine low-affine plane as soon as
it is linearly independent. -/
theorem lowHomQuadPlane_nontrivial_of_independent_pair
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 = 0)
    (hind : LinearIndependent ℝ ![q2, q3]) :
    lowHomQuadPlaneA q2 q3 ≠ 0 ∨
      lowHomQuadPlaneB q2 q3 ≠ 0 ∨ lowHomQuadPlaneC q2 q3 ≠ 0 := by
  by_contra hplane
  push Not at hplane
  rcases hplane with ⟨hA0, hB0, hC0⟩
  have hq2_ne : q2 ≠ 0 := by
    exact hind.ne_zero 0
  by_cases h20 : MvPolynomial.coeff m20 q2 = 0
  · by_cases h11 : MvPolynomial.coeff m11 q2 = 0
    · have h02 : MvPolynomial.coeff m02 q2 ≠ 0 := by
        intro h02'
        have hq2_zero : q2 = 0 := by
          rw [homogeneousQuadratic_eq hq2 hq2_00 hq2_10 hq2_01]
          simp [h20, h11, h02']
        exact hq2_ne hq2_zero
      let t : ℝ := MvPolynomial.coeff m02 q3 / MvPolynomial.coeff m02 q2
      have h20q3 : MvPolynomial.coeff m20 q3 = 0 := by
        have hrel : MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m02 q3 -
            MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3 = 0 := by
          simpa [lowHomQuadPlaneB] using hB0
        rw [h20] at hrel
        have : MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3 = 0 := by
          linarith
        exact (mul_eq_zero.mp this).resolve_left h02
      have h11q3 : MvPolynomial.coeff m11 q3 = 0 := by
        have hrel : MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
            MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0 := by
          simpa [lowHomQuadPlaneA] using hA0
        rw [h11] at hrel
        have : MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0 := by
          linarith
        exact (mul_eq_zero.mp this).resolve_left h02
      have h02q3 : MvPolynomial.coeff m02 q3 = t * MvPolynomial.coeff m02 q2 := by
        unfold t
        field_simp [h02]
      have hq3_eq : q3 = t • q2 := by
        rw [homogeneousQuadratic_eq hq3 hq3_00 hq3_10 hq3_01]
        rw [homogeneousQuadratic_eq hq2 hq2_00 hq2_10 hq2_01]
        rw [h20q3, h11q3, h02q3, h20, h11]
        simp [smul_smul]
      have hbad : (-t) • q2 + (1 : ℝ) • q3 = 0 := by
        simp [hq3_eq]
      have hpair := LinearIndependent.eq_zero_of_pair hind hbad
      have hone : (1 : ℝ) = 0 := hpair.2
      norm_num at hone
    · let t : ℝ := MvPolynomial.coeff m11 q3 / MvPolynomial.coeff m11 q2
      have h20q3 : MvPolynomial.coeff m20 q3 = 0 := by
        have hrel : MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m11 q3 -
            MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m20 q3 = 0 := by
          simpa [lowHomQuadPlaneC] using hC0
        rw [h20] at hrel
        have : MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m20 q3 = 0 := by
          linarith
        exact (mul_eq_zero.mp this).resolve_left h11
      have h02q3 :
          MvPolynomial.coeff m02 q3 = t * MvPolynomial.coeff m02 q2 := by
        have hrel : MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
            MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0 := by
          simpa [lowHomQuadPlaneA] using hA0
        have hdiv :
            MvPolynomial.coeff m02 q3 =
              (MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3) /
                MvPolynomial.coeff m11 q2 := by
          apply (eq_div_iff h11).2
          linarith
        calc
          MvPolynomial.coeff m02 q3 =
              (MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3) /
                MvPolynomial.coeff m11 q2 := hdiv
          _ = (MvPolynomial.coeff m11 q3 / MvPolynomial.coeff m11 q2) *
                MvPolynomial.coeff m02 q2 := by
                field_simp [h11]
          _ = t * MvPolynomial.coeff m02 q2 := by rfl
      have h11q3 : MvPolynomial.coeff m11 q3 = t * MvPolynomial.coeff m11 q2 := by
        unfold t
        field_simp [h11]
      have hq3_eq : q3 = t • q2 := by
        rw [homogeneousQuadratic_eq hq3 hq3_00 hq3_10 hq3_01]
        rw [homogeneousQuadratic_eq hq2 hq2_00 hq2_10 hq2_01]
        rw [h20q3, h02q3, h11q3, h20]
        simp [smul_add, smul_smul]
      have hbad : (-t) • q2 + (1 : ℝ) • q3 = 0 := by
        simp [hq3_eq]
      have hpair := LinearIndependent.eq_zero_of_pair hind hbad
      have hone : (1 : ℝ) = 0 := hpair.2
      norm_num at hone
  · let t : ℝ := MvPolynomial.coeff m20 q3 / MvPolynomial.coeff m20 q2
    have h11 :
        MvPolynomial.coeff m11 q3 = t * MvPolynomial.coeff m11 q2 := by
      have hrel : MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m11 q3 -
          MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m20 q3 = 0 := by
        simpa [lowHomQuadPlaneC] using hC0
      have hdiv :
          MvPolynomial.coeff m11 q3 =
            (MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m20 q3) /
              MvPolynomial.coeff m20 q2 := by
        apply (eq_div_iff h20).2
        linarith
      calc
        MvPolynomial.coeff m11 q3 =
            (MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m20 q3) /
              MvPolynomial.coeff m20 q2 := hdiv
        _ = (MvPolynomial.coeff m20 q3 / MvPolynomial.coeff m20 q2) *
              MvPolynomial.coeff m11 q2 := by
              field_simp [h20]
        _ = t * MvPolynomial.coeff m11 q2 := by rfl
    have h02 :
        MvPolynomial.coeff m02 q3 = t * MvPolynomial.coeff m02 q2 := by
      have hrel : MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m02 q3 -
          MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3 = 0 := by
        simpa [lowHomQuadPlaneB] using hB0
      have hdiv :
          MvPolynomial.coeff m02 q3 =
            (MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3) /
              MvPolynomial.coeff m20 q2 := by
        apply (eq_div_iff h20).2
        linarith
      calc
        MvPolynomial.coeff m02 q3 =
            (MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3) /
              MvPolynomial.coeff m20 q2 := hdiv
        _ = (MvPolynomial.coeff m20 q3 / MvPolynomial.coeff m20 q2) *
              MvPolynomial.coeff m02 q2 := by
              field_simp [h20]
        _ = t * MvPolynomial.coeff m02 q2 := by rfl
    have h20q3 : MvPolynomial.coeff m20 q3 = t * MvPolynomial.coeff m20 q2 := by
      unfold t
      field_simp [h20]
    have hq3_eq : q3 = t • q2 := by
      rw [homogeneousQuadratic_eq hq3 hq3_00 hq3_10 hq3_01]
      rw [homogeneousQuadratic_eq hq2 hq2_00 hq2_10 hq2_01]
      rw [h20q3, h11, h02]
      simp [smul_add, smul_smul]
    have hbad : (-t) • q2 + (1 : ℝ) • q3 = 0 := by
      simp [hq3_eq]
    have hpair := LinearIndependent.eq_zero_of_pair hind hbad
    have hone : (1 : ℝ) = 0 := hpair.2
    norm_num at hone

private theorem lowHomQuadPlane_zero_imp_smul
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 = 0)
    (hq2_ne : q2 ≠ 0)
    (hA0 : lowHomQuadPlaneA q2 q3 = 0)
    (hB0 : lowHomQuadPlaneB q2 q3 = 0)
    (hC0 : lowHomQuadPlaneC q2 q3 = 0) :
    ∃ t : ℝ, q3 = t • q2 := by
  by_cases h20 : MvPolynomial.coeff m20 q2 = 0
  · by_cases h11 : MvPolynomial.coeff m11 q2 = 0
    · have h02 : MvPolynomial.coeff m02 q2 ≠ 0 := by
        intro h02'
        have hq2_zero : q2 = 0 := by
          rw [homogeneousQuadratic_eq hq2 hq2_00 hq2_10 hq2_01]
          simp [h20, h11, h02']
        exact hq2_ne hq2_zero
      let t : ℝ := MvPolynomial.coeff m02 q3 / MvPolynomial.coeff m02 q2
      have h20q3 : MvPolynomial.coeff m20 q3 = 0 := by
        have hrel :
            MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m02 q3 -
              MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3 = 0 := by
          simpa [lowHomQuadPlaneB] using hB0
        rw [h20] at hrel
        have : MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3 = 0 := by
          linarith
        exact (mul_eq_zero.mp this).resolve_left h02
      have h11q3 : MvPolynomial.coeff m11 q3 = 0 := by
        have hrel :
            MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
              MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0 := by
          simpa [lowHomQuadPlaneA] using hA0
        rw [h11] at hrel
        have : MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0 := by
          linarith
        exact (mul_eq_zero.mp this).resolve_left h02
      have h02q3 : MvPolynomial.coeff m02 q3 = t * MvPolynomial.coeff m02 q2 := by
        unfold t
        field_simp [h02]
      refine ⟨t, ?_⟩
      rw [homogeneousQuadratic_eq hq3 hq3_00 hq3_10 hq3_01]
      rw [homogeneousQuadratic_eq hq2 hq2_00 hq2_10 hq2_01]
      rw [h20q3, h11q3, h02q3, h20, h11]
      simp [smul_smul]
    · let t : ℝ := MvPolynomial.coeff m11 q3 / MvPolynomial.coeff m11 q2
      have h20q3 : MvPolynomial.coeff m20 q3 = 0 := by
        have hrel :
            MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m11 q3 -
              MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m20 q3 = 0 := by
          simpa [lowHomQuadPlaneC] using hC0
        rw [h20] at hrel
        have : MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m20 q3 = 0 := by
          linarith
        exact (mul_eq_zero.mp this).resolve_left h11
      have h02q3 :
          MvPolynomial.coeff m02 q3 = t * MvPolynomial.coeff m02 q2 := by
        have hrel :
            MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
              MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0 := by
          simpa [lowHomQuadPlaneA] using hA0
        have hdiv :
            MvPolynomial.coeff m02 q3 =
              (MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3) /
                MvPolynomial.coeff m11 q2 := by
          apply (eq_div_iff h11).2
          linarith
        calc
          MvPolynomial.coeff m02 q3 =
              (MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3) /
                MvPolynomial.coeff m11 q2 := hdiv
          _ = (MvPolynomial.coeff m11 q3 / MvPolynomial.coeff m11 q2) *
                MvPolynomial.coeff m02 q2 := by
                field_simp [h11]
          _ = t * MvPolynomial.coeff m02 q2 := by rfl
      have h11q3 : MvPolynomial.coeff m11 q3 = t * MvPolynomial.coeff m11 q2 := by
        unfold t
        field_simp [h11]
      refine ⟨t, ?_⟩
      rw [homogeneousQuadratic_eq hq3 hq3_00 hq3_10 hq3_01]
      rw [homogeneousQuadratic_eq hq2 hq2_00 hq2_10 hq2_01]
      rw [h20q3, h02q3, h11q3, h20]
      simp [smul_add, smul_smul]
  · let t : ℝ := MvPolynomial.coeff m20 q3 / MvPolynomial.coeff m20 q2
    have h11q3 :
        MvPolynomial.coeff m11 q3 = t * MvPolynomial.coeff m11 q2 := by
      have hrel :
          MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m11 q3 -
            MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m20 q3 = 0 := by
        simpa [lowHomQuadPlaneC] using hC0
      have hdiv :
          MvPolynomial.coeff m11 q3 =
            (MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m20 q3) /
              MvPolynomial.coeff m20 q2 := by
        apply (eq_div_iff h20).2
        linarith
      calc
        MvPolynomial.coeff m11 q3 =
            (MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m20 q3) /
              MvPolynomial.coeff m20 q2 := hdiv
        _ = (MvPolynomial.coeff m20 q3 / MvPolynomial.coeff m20 q2) *
              MvPolynomial.coeff m11 q2 := by
              field_simp [h20]
        _ = t * MvPolynomial.coeff m11 q2 := by rfl
    have h02q3 :
        MvPolynomial.coeff m02 q3 = t * MvPolynomial.coeff m02 q2 := by
      have hrel :
          MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m02 q3 -
            MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3 = 0 := by
        simpa [lowHomQuadPlaneB] using hB0
      have hdiv :
          MvPolynomial.coeff m02 q3 =
            (MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3) /
              MvPolynomial.coeff m20 q2 := by
        apply (eq_div_iff h20).2
        linarith
      calc
        MvPolynomial.coeff m02 q3 =
            (MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3) /
              MvPolynomial.coeff m20 q2 := hdiv
        _ = (MvPolynomial.coeff m20 q3 / MvPolynomial.coeff m20 q2) *
              MvPolynomial.coeff m02 q2 := by
              field_simp [h20]
        _ = t * MvPolynomial.coeff m02 q2 := by rfl
    have h20q3 : MvPolynomial.coeff m20 q3 = t * MvPolynomial.coeff m20 q2 := by
      unfold t
      field_simp [h20]
    refine ⟨t, ?_⟩
    rw [homogeneousQuadratic_eq hq3 hq3_00 hq3_10 hq3_01]
    rw [homogeneousQuadratic_eq hq2 hq2_00 hq2_10 hq2_01]
    rw [h20q3, h11q3, h02q3]
    simp [smul_add, smul_smul]

private theorem lowHomQuadPlane_zero_of_smul_left
    {q : Poly} (t : ℝ) :
    lowHomQuadPlaneA (t • q) q = 0 ∧
      lowHomQuadPlaneB (t • q) q = 0 ∧
      lowHomQuadPlaneC (t • q) q = 0 := by
  constructor
  · simp [lowHomQuadPlaneA, MvPolynomial.coeff_smul]
    ring
  constructor
  · simp [lowHomQuadPlaneB, MvPolynomial.coeff_smul]
    ring
  · simp [lowHomQuadPlaneC, MvPolynomial.coeff_smul]
    ring

private theorem lowHomQuadPlane_relation_left (q2 q3 : Poly) :
    lowHomQuadPlaneA q2 q3 * MvPolynomial.coeff m20 q2 +
      (-lowHomQuadPlaneB q2 q3) * MvPolynomial.coeff m11 q2 +
        lowHomQuadPlaneC q2 q3 * MvPolynomial.coeff m02 q2 = 0 := by
  simp [lowHomQuadPlaneA, lowHomQuadPlaneB, lowHomQuadPlaneC]
  ring

private theorem lowHomQuadPlane_relation_right (q2 q3 : Poly) :
    lowHomQuadPlaneA q2 q3 * MvPolynomial.coeff m20 q3 +
      (-lowHomQuadPlaneB q2 q3) * MvPolynomial.coeff m11 q3 +
        lowHomQuadPlaneC q2 q3 * MvPolynomial.coeff m02 q3 = 0 := by
  simp [lowHomQuadPlaneA, lowHomQuadPlaneB, lowHomQuadPlaneC]
  ring

private theorem coeff_m11_affineHom_x1Shear_lowHomQuadPlaneA_zero
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hA0 : lowHomQuadPlaneA q2 q3 = 0)
    (hB : lowHomQuadPlaneB q2 q3 ≠ 0) :
    let t : ℝ := lowHomQuadPlaneC q2 q3 / (-(2 * lowHomQuadPlaneB q2 q3))
    MvPolynomial.coeff m11 (affineHom (x1ShearMatrix t) 0 q2) = 0 ∧
      MvPolynomial.coeff m11 (affineHom (x1ShearMatrix t) 0 q3) = 0 := by
  let t : ℝ := lowHomQuadPlaneC q2 q3 / (-(2 * lowHomQuadPlaneB q2 q3))
  have hrel2 :
      (-lowHomQuadPlaneB q2 q3) * MvPolynomial.coeff m11 q2 +
        lowHomQuadPlaneC q2 q3 * MvPolynomial.coeff m02 q2 = 0 := by
    simpa [hA0] using lowHomQuadPlane_relation_left q2 q3
  have hrel3 :
      (-lowHomQuadPlaneB q2 q3) * MvPolynomial.coeff m11 q3 +
        lowHomQuadPlaneC q2 q3 * MvPolynomial.coeff m02 q3 = 0 := by
    simpa [hA0] using lowHomQuadPlane_relation_right q2 q3
  constructor
  · simpa [t] using coeff_m11_affineHom_x1Shear_dual_to_cross
      hq2 (b := -lowHomQuadPlaneB q2 q3) (c := lowHomQuadPlaneC q2 q3)
      (neg_ne_zero.mpr hB) hrel2
  · simpa [t] using coeff_m11_affineHom_x1Shear_dual_to_cross
      hq3 (b := -lowHomQuadPlaneB q2 q3) (c := lowHomQuadPlaneC q2 q3)
      (neg_ne_zero.mpr hB) hrel3

private theorem det_x0sq_x1sq_affineHom_x1Shear_lowHomQuadPlaneA_zero
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hA0 : lowHomQuadPlaneA q2 q3 = 0) :
    let t : ℝ := lowHomQuadPlaneC q2 q3 / (-(2 * lowHomQuadPlaneB q2 q3))
    MvPolynomial.coeff m20 (affineHom (x1ShearMatrix t) 0 q2) *
        MvPolynomial.coeff m02 (affineHom (x1ShearMatrix t) 0 q3) -
      MvPolynomial.coeff m02 (affineHom (x1ShearMatrix t) 0 q2) *
        MvPolynomial.coeff m20 (affineHom (x1ShearMatrix t) 0 q3) =
      lowHomQuadPlaneB q2 q3 := by
  let t : ℝ := lowHomQuadPlaneC q2 q3 / (-(2 * lowHomQuadPlaneB q2 q3))
  change
    MvPolynomial.coeff m20 (affineHom (x1ShearMatrix t) 0 q2) *
        MvPolynomial.coeff m02 (affineHom (x1ShearMatrix t) 0 q3) -
      MvPolynomial.coeff m02 (affineHom (x1ShearMatrix t) 0 q2) *
        MvPolynomial.coeff m20 (affineHom (x1ShearMatrix t) 0 q3) =
      lowHomQuadPlaneB q2 q3
  rw [coeff_m20_affineHom_x1Shear hq2, coeff_m20_affineHom_x1Shear hq3,
    coeff_m02_affineHom_x1Shear hq2, coeff_m02_affineHom_x1Shear hq3]
  have hcross :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0 := by
    simpa [lowHomQuadPlaneA] using hA0
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
    _ = lowHomQuadPlaneB q2 q3 := by
      simp [lowHomQuadPlaneB]

theorem residual_eq_zero_of_relations_x0_x1_homQuadratics_crossDet_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
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
    (hcross :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hdet :
      MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let t : ℝ := lowHomQuadPlaneC q2 q3 / (-(2 * lowHomQuadPlaneB q2 q3))
  let e : Poly ≃ₐ[ℝ] Poly := x1ShearEquiv t
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  have heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q) := by
    intro q hq
    exact isQuadratic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
      (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq
  have heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q) := by
    intro q hq
    exact isQuadratic_affineEquiv_symm (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
      (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq
  have heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q) := by
    intro q hq
    exact isQuartic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
      (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq
  have h0' : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0 := by
    simpa [e] using (relation_map e.toAlgHom h0).trans (affineHom_x1Shear_x0 t)
  have h1e : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = MvPolynomial.C t * x0 + x1 := by
    simpa [e] using (relation_map e.toAlgHom h1).trans (affineHom_x1Shear_x1 t)
  let c1' : Fin 4 → ℝ := fun i => c1 i + (-t) * c0 i
  have h1' : ∑ i : Fin 4, c1' i • mapVec e.toAlgHom u i = x1 := by
    calc
      ∑ i : Fin 4, c1' i • mapVec e.toAlgHom u i
          = 1 • (MvPolynomial.C t * x0 + x1) + (-t) • x0 := by
              simpa [c1'] using relation_linearCombination_low h1e h0' (1 : ℝ) (-t)
      _ = x1 := by
            simp [MvPolynomial.smul_eq_C_mul, x0, x1]
  have h2e : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = e q2 := by
    simpa [e] using relation_map e.toAlgHom h2
  have h3e : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = e q3 := by
    simpa [e] using relation_map e.toAlgHom h3
  have hA0 : lowHomQuadPlaneA q2 q3 = 0 := by
    simpa [lowHomQuadPlaneA] using hcross
  have hB0 : lowHomQuadPlaneB q2 q3 ≠ 0 := by
    simpa [lowHomQuadPlaneB] using hdet
  have hq2' : IsQuadratic (e q2) := heQuad hq2
  have hq3' : IsQuadratic (e q3) := heQuad hq3
  have hq2_00' : MvPolynomial.coeff m00 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl, coeff_m00_affineHom_x1Shear hq2]
    simpa using hq2_00
  have hq2_10' : MvPolynomial.coeff m10 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl, coeff_m10_affineHom_x1Shear hq2]
    simp [hq2_10, hq2_01]
  have hq2_01' : MvPolynomial.coeff m01 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl, coeff_m01_affineHom_x1Shear hq2]
    simpa using hq2_01
  have hq3_00' : MvPolynomial.coeff m00 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl, coeff_m00_affineHom_x1Shear hq3]
    simpa using hq3_00
  have hq3_10' : MvPolynomial.coeff m10 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl, coeff_m10_affineHom_x1Shear hq3]
    simp [hq3_10, hq3_01]
  have hq3_01' : MvPolynomial.coeff m01 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl, coeff_m01_affineHom_x1Shear hq3]
    simpa using hq3_01
  have h11' :
      MvPolynomial.coeff m11 (e q2) = 0 ∧
        MvPolynomial.coeff m11 (e q3) = 0 := by
    simpa [e] using
      coeff_m11_affineHom_x1Shear_lowHomQuadPlaneA_zero hq2 hq3 hA0 hB0
  have hq2_11' : MvPolynomial.coeff m11 (e q2) = 0 := h11'.1
  have hq3_11' : MvPolynomial.coeff m11 (e q3) = 0 := h11'.2
  have hdet' :
      MvPolynomial.coeff m20 (e q2) * MvPolynomial.coeff m02 (e q3) -
        MvPolynomial.coeff m02 (e q2) * MvPolynomial.coeff m20 (e q3) ≠ 0 := by
    have hdetEq :
        MvPolynomial.coeff m20 (e q2) * MvPolynomial.coeff m02 (e q3) -
          MvPolynomial.coeff m02 (e q2) * MvPolynomial.coeff m20 (e q3) =
        lowHomQuadPlaneB q2 q3 := by
      simpa [e] using det_x0sq_x1sq_affineHom_x1Shear_lowHomQuadPlaneA_zero hq2 hq3 hA0
    intro hz
    apply hB0
    simpa [hdetEq] using hz
  have h2' :
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i =
        MvPolynomial.coeff m20 (e q2) • (x0 ^ 2 : Poly) +
          MvPolynomial.coeff m02 (e q2) • (x1 ^ 2 : Poly) := by
    refine h2e.trans ?_
    exact homogeneousQuadratic_eq_x0sq_x1sq_of_coeff_m11_zero
      hq2' hq2_00' hq2_10' hq2_01' hq2_11'
  have h3' :
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i =
        MvPolynomial.coeff m20 (e q3) • (x0 ^ 2 : Poly) +
          MvPolynomial.coeff m02 (e q3) • (x1 ^ 2 : Poly) := by
    refine h3e.trans ?_
    exact homogeneousQuadratic_eq_x0sq_x1sq_of_coeff_m11_zero
      hq3' hq3_00' hq3_10' hq3_01' hq3_11'
  exact residual_eq_zero_of_equiv_relations_x0_x1_x0sq_x1sqPlane
    (e := e) (heQuad := fun {_} hq => heQuad hq) (heQuadSymm := fun {_} hq => heQuadSymm hq)
    (heQuartic := fun {_} hq => heQuartic hq)
    hB hp hu hsocp h0' h1' h2' h3' hdet'

theorem residual_eq_zero_of_equiv_relations_x0_x1_homQuadratics_crossDet_zero
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q))
    (heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q))
    (heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 = 0)
    (hcross :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hdet :
      MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3 ≠ 0) :
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
    exact residual_eq_zero_of_relations_x0_x1_homQuadratics_crossDet_zero
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0 h1 h2 h3
      hq2 hq3 hq2_00 hq2_10 hq2_01 hq3_00 hq3_10 hq3_01 hcross hdet hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

private theorem quadratic_eq_one_plus_x0sq_x1sq_of_coeff_m11_zero
    {q : Poly}
    (hq : IsQuadratic q)
    (h00 : MvPolynomial.coeff m00 q = 1)
    (h10 : MvPolynomial.coeff m10 q = 0)
    (h01 : MvPolynomial.coeff m01 q = 0)
    (h11 : MvPolynomial.coeff m11 q = 0) :
    q = (1 : Poly) +
      MvPolynomial.coeff m20 q • (x0 ^ 2 : Poly) +
      MvPolynomial.coeff m02 q • (x1 ^ 2 : Poly) := by
  calc
    q =
      quadForm
        (MvPolynomial.coeff m00 q)
        (MvPolynomial.coeff m10 q)
        (MvPolynomial.coeff m01 q)
        (MvPolynomial.coeff m20 q)
        (MvPolynomial.coeff m11 q)
        (MvPolynomial.coeff m02 q) := by
          exact quadratic_eq_quadForm hq
    _ = (1 : Poly) +
          MvPolynomial.coeff m20 q • (x0 ^ 2 : Poly) +
          MvPolynomial.coeff m02 q • (x1 ^ 2 : Poly) := by
            rw [quadForm_eq_explicit, h00, h10, h01, h11]
            simp [add_assoc, MvPolynomial.smul_eq_C_mul]

theorem residual_eq_zero_of_relations_x0_x1_onePlus_homQuadratics_crossDet_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 1)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 = 0)
    (hcross :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hdet :
      MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let t : ℝ := lowHomQuadPlaneC q2 q3 / (-(2 * lowHomQuadPlaneB q2 q3))
  let e : Poly ≃ₐ[ℝ] Poly := x1ShearEquiv t
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  have heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q) := by
    intro q hq
    exact isQuadratic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
      (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq
  have heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q) := by
    intro q hq
    exact isQuadratic_affineEquiv_symm (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
      (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq
  have heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q) := by
    intro q hq
    exact isQuartic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
      (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq
  have h0' : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0 := by
    simpa [e] using (relation_map e.toAlgHom h0).trans (affineHom_x1Shear_x0 t)
  have h1e : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = MvPolynomial.C t * x0 + x1 := by
    simpa [e] using (relation_map e.toAlgHom h1).trans (affineHom_x1Shear_x1 t)
  let c1' : Fin 4 → ℝ := fun i => c1 i + (-t) * c0 i
  have h1' : ∑ i : Fin 4, c1' i • mapVec e.toAlgHom u i = x1 := by
    calc
      ∑ i : Fin 4, c1' i • mapVec e.toAlgHom u i
          = 1 • (MvPolynomial.C t * x0 + x1) + (-t) • x0 := by
              simpa [c1'] using relation_linearCombination_low h1e h0' (1 : ℝ) (-t)
      _ = x1 := by
            simp [MvPolynomial.smul_eq_C_mul, x0, x1]
  have h2e : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = e q2 := by
    simpa [e] using relation_map e.toAlgHom h2
  have h3e : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = e q3 := by
    simpa [e] using relation_map e.toAlgHom h3
  have hA0 : lowHomQuadPlaneA q2 q3 = 0 := by
    simpa [lowHomQuadPlaneA] using hcross
  have hB0 : lowHomQuadPlaneB q2 q3 ≠ 0 := by
    simpa [lowHomQuadPlaneB] using hdet
  have hq2' : IsQuadratic (e q2) := heQuad hq2
  have hq3' : IsQuadratic (e q3) := heQuad hq3
  have hq2_00' : MvPolynomial.coeff m00 (e q2) = 1 := by
    rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl, coeff_m00_affineHom_x1Shear hq2]
    simpa using hq2_00
  have hq2_10' : MvPolynomial.coeff m10 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl, coeff_m10_affineHom_x1Shear hq2]
    simp [hq2_10, hq2_01]
  have hq2_01' : MvPolynomial.coeff m01 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl, coeff_m01_affineHom_x1Shear hq2]
    simpa using hq2_01
  have hq3_00' : MvPolynomial.coeff m00 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl, coeff_m00_affineHom_x1Shear hq3]
    simpa using hq3_00
  have hq3_10' : MvPolynomial.coeff m10 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl, coeff_m10_affineHom_x1Shear hq3]
    simp [hq3_10, hq3_01]
  have hq3_01' : MvPolynomial.coeff m01 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl, coeff_m01_affineHom_x1Shear hq3]
    simpa using hq3_01
  have h11' :
      MvPolynomial.coeff m11 (e q2) = 0 ∧
        MvPolynomial.coeff m11 (e q3) = 0 := by
    simpa [e] using
      coeff_m11_affineHom_x1Shear_lowHomQuadPlaneA_zero hq2 hq3 hA0 hB0
  have hq2_11' : MvPolynomial.coeff m11 (e q2) = 0 := h11'.1
  have hq3_11' : MvPolynomial.coeff m11 (e q3) = 0 := h11'.2
  have hdet' :
      MvPolynomial.coeff m20 (e q2) * MvPolynomial.coeff m02 (e q3) -
        MvPolynomial.coeff m02 (e q2) * MvPolynomial.coeff m20 (e q3) ≠ 0 := by
    have hdetEq :
        MvPolynomial.coeff m20 (e q2) * MvPolynomial.coeff m02 (e q3) -
          MvPolynomial.coeff m02 (e q2) * MvPolynomial.coeff m20 (e q3) =
        lowHomQuadPlaneB q2 q3 := by
      simpa [e] using det_x0sq_x1sq_affineHom_x1Shear_lowHomQuadPlaneA_zero hq2 hq3 hA0
    intro hz
    apply hB0
    simpa [hdetEq] using hz
  have h2' :
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i =
        (1 : Poly) +
          MvPolynomial.coeff m20 (e q2) • (x0 ^ 2 : Poly) +
          MvPolynomial.coeff m02 (e q2) • (x1 ^ 2 : Poly) := by
    refine h2e.trans ?_
    exact quadratic_eq_one_plus_x0sq_x1sq_of_coeff_m11_zero
      hq2' hq2_00' hq2_10' hq2_01' hq2_11'
  have h3' :
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i =
        MvPolynomial.coeff m20 (e q3) • (x0 ^ 2 : Poly) +
          MvPolynomial.coeff m02 (e q3) • (x1 ^ 2 : Poly) := by
    refine h3e.trans ?_
    exact homogeneousQuadratic_eq_x0sq_x1sq_of_coeff_m11_zero
      hq3' hq3_00' hq3_10' hq3_01' hq3_11'
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
    exact residual_eq_zero_of_relations_x0_x1_onePlusAX0sq_x1sqPlane
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0' h1' h2' h3' hdet' hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_equiv_relations_x0_x1_onePlus_homQuadratics_crossDet_zero
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q))
    (heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q))
    (heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 1)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 = 0)
    (hcross :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 = 0)
    (hdet :
      MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3 ≠ 0) :
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
    exact residual_eq_zero_of_relations_x0_x1_onePlus_homQuadratics_crossDet_zero
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0 h1 h2 h3
      hq2 hq3 hq2_00 hq2_10 hq2_01 hq3_00 hq3_10 hq3_01 hcross hdet hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_affinePair_onePlus_homQuadratics_crossDet_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {r0 r1 : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = affineLinePoly r0 1 0)
    (h1 : ∑ i : Fin 4, c1 i • u i = affineLinePoly r1 0 1)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 :
      MvPolynomial.coeff m00
        (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q2) = 1)
    (hq2_10 :
      MvPolynomial.coeff m10
        (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q2) = 0)
    (hq2_01 :
      MvPolynomial.coeff m01
        (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q2) = 0)
    (hq3_00 :
      MvPolynomial.coeff m00
        (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q3) = 0)
    (hq3_10 :
      MvPolynomial.coeff m10
        (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q3) = 0)
    (hq3_01 :
      MvPolynomial.coeff m01
        (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q3) = 0)
    (hcross :
      MvPolynomial.coeff m11
          (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q2) *
          MvPolynomial.coeff m02
            (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q3) -
        MvPolynomial.coeff m02
            (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q2) *
          MvPolynomial.coeff m11
            (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q3) = 0)
    (hdet :
      MvPolynomial.coeff m20
          (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q2) *
          MvPolynomial.coeff m02
            (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q3) -
        MvPolynomial.coeff m02
            (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q2) *
          MvPolynomial.coeff m20
            (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q3) ≠ 0)
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
  have heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q) := by
    intro q hq
    exact isQuadratic_affineEquiv
      (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
      (by simp) (by simp)
      (by intro i; fin_cases i <;> simp [b, b'])
      (by intro i; fin_cases i <;> simp [b, b']) hq
  have heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q) := by
    intro q hq
    exact isQuadratic_affineEquiv_symm
      (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
      (by simp) (by simp)
      (by intro i; fin_cases i <;> simp [b, b'])
      (by intro i; fin_cases i <;> simp [b, b']) hq
  have heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q) := by
    intro q hq
    exact isQuartic_affineEquiv
      (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
      (by simp) (by simp)
      (by intro i; fin_cases i <;> simp [b, b'])
      (by intro i; fin_cases i <;> simp [b, b']) hq
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  have h0' : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0 := by
    calc
      ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = e (affineLinePoly r0 1 0) := by
        simpa [e] using relation_map e.toAlgHom h0
      _ = x0 := by
        simp [e, b, b', affineLinePoly, affineEquiv, affineHom, affineImage, x0, x1,
          Fin.sum_univ_two]
  have h1' : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1 := by
    calc
      ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = e (affineLinePoly r1 0 1) := by
        simpa [e] using relation_map e.toAlgHom h1
      _ = x1 := by
        simp [e, b, b', affineLinePoly, affineEquiv, affineHom, affineImage, x0, x1,
          Fin.sum_univ_two]
  have h2' :
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i =
        affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) b q2 := by
    simpa [e, b] using relation_map e.toAlgHom h2
  have h3' :
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i =
        affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) b q3 := by
    simpa [e, b] using relation_map e.toAlgHom h3
  exact residual_eq_zero_of_equiv_relations_x0_x1_onePlus_homQuadratics_crossDet_zero
    (e := e) (heQuad := fun {_} hq => heQuad hq) (heQuadSymm := fun {_} hq => heQuadSymm hq)
    (heQuartic := fun {_} hq => heQuartic hq)
    hB hp hu hsocp h0' h1' h2' h3'
    (heQuad hq2) (heQuad hq3)
    hq2_00 hq2_10 hq2_01 hq3_00 hq3_10 hq3_01 hcross hdet

theorem residual_eq_zero_of_relations_linearPair_homQuadratics_crossDet_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {a b c d : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = linearForm a b)
    (h1 : ∑ i : Fin 4, c1 i • u i = linearForm c d)
    (hdetLin : a * d - b * c ≠ 0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 (linearPairEquiv a b c d hdetLin q2) = 0)
    (hq2_10 : MvPolynomial.coeff m10 (linearPairEquiv a b c d hdetLin q2) = 0)
    (hq2_01 : MvPolynomial.coeff m01 (linearPairEquiv a b c d hdetLin q2) = 0)
    (hq3_00 : MvPolynomial.coeff m00 (linearPairEquiv a b c d hdetLin q3) = 0)
    (hq3_10 : MvPolynomial.coeff m10 (linearPairEquiv a b c d hdetLin q3) = 0)
    (hq3_01 : MvPolynomial.coeff m01 (linearPairEquiv a b c d hdetLin q3) = 0)
    (hcross :
      MvPolynomial.coeff m11 (linearPairEquiv a b c d hdetLin q2) *
          MvPolynomial.coeff m02 (linearPairEquiv a b c d hdetLin q3) -
        MvPolynomial.coeff m02 (linearPairEquiv a b c d hdetLin q2) *
          MvPolynomial.coeff m11 (linearPairEquiv a b c d hdetLin q3) = 0)
    (hdet :
      MvPolynomial.coeff m20 (linearPairEquiv a b c d hdetLin q2) *
          MvPolynomial.coeff m02 (linearPairEquiv a b c d hdetLin q3) -
        MvPolynomial.coeff m02 (linearPairEquiv a b c d hdetLin q2) *
          MvPolynomial.coeff m20 (linearPairEquiv a b c d hdetLin q3) ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let e : Poly ≃ₐ[ℝ] Poly := linearPairEquiv a b c d hdetLin
  have heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q) := by
    intro q hq
    exact isQuadratic_affineEquiv
      (linearPairMatrix a b c d) (linearPairInvMatrix a b c d) 0 0
      (linearPair_mul_inv a b c d hdetLin) (linearPair_inv_mul a b c d hdetLin)
      (by intro i; simp) (by intro i; simp) hq
  have heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q) := by
    intro q hq
    exact isQuadratic_affineEquiv_symm
      (linearPairMatrix a b c d) (linearPairInvMatrix a b c d) 0 0
      (linearPair_mul_inv a b c d hdetLin) (linearPair_inv_mul a b c d hdetLin)
      (by intro i; simp) (by intro i; simp) hq
  have heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q) := by
    intro q hq
    exact isQuartic_affineEquiv
      (linearPairMatrix a b c d) (linearPairInvMatrix a b c d) 0 0
      (linearPair_mul_inv a b c d hdetLin) (linearPair_inv_mul a b c d hdetLin)
      (by intro i; simp) (by intro i; simp) hq
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  have h0' : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0 := by
    simpa [e, linearPairEquiv] using
      (relation_map e.toAlgHom h0).trans (affineHom_linearPair_left a b c d hdetLin)
  have h1' : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1 := by
    simpa [e, linearPairEquiv] using
      (relation_map e.toAlgHom h1).trans (affineHom_linearPair_right a b c d hdetLin)
  have h2' : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = e q2 := by
    simpa [e] using relation_map e.toAlgHom h2
  have h3' : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = e q3 := by
    simpa [e] using relation_map e.toAlgHom h3
  exact residual_eq_zero_of_equiv_relations_x0_x1_homQuadratics_crossDet_zero
    (e := e) (heQuad := fun {_} hq => heQuad hq) (heQuadSymm := fun {_} hq => heQuadSymm hq)
    (heQuartic := fun {_} hq => heQuartic hq)
    hB hp hu hsocp h0' h1' h2' h3'
    (heQuad hq2) (heQuad hq3) hq2_00 hq2_10 hq2_01 hq3_00 hq3_10 hq3_01 hcross hdet

theorem residual_eq_zero_of_relations_x0_x1_homQuadratics_commonFactorChart
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
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
    (hA :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 ≠ 0)
    (hdiag0 :
      lowHomQuadPlaneC q2 q3 -
        lowHomQuadPlaneB q2 q3 ^ 2 / lowHomQuadPlaneA q2 q3 = 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let t : ℝ := -lowHomQuadPlaneB q2 q3 / lowHomQuadPlaneA q2 q3
  let e : Poly ≃ₐ[ℝ] Poly := x1ShearEquiv t
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  have heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q) := by
    intro q hq
    exact isQuadratic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
      (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq
  have heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q) := by
    intro q hq
    exact isQuadratic_affineEquiv_symm (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
      (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq
  have heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q) := by
    intro q hq
    exact isQuartic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
      (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq
  have h0' : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0 := by
    simpa [e] using (relation_map e.toAlgHom h0).trans (affineHom_x1Shear_x0 t)
  have h1e : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = MvPolynomial.C t * x0 + x1 := by
    simpa [e] using (relation_map e.toAlgHom h1).trans (affineHom_x1Shear_x1 t)
  let c1' : Fin 4 → ℝ := fun i => c1 i + (-t) * c0 i
  have h1' : ∑ i : Fin 4, c1' i • mapVec e.toAlgHom u i = x1 := by
    calc
      ∑ i : Fin 4, c1' i • mapVec e.toAlgHom u i
          = 1 • (MvPolynomial.C t * x0 + x1) + (-t) • x0 := by
              simpa [c1'] using relation_linearCombination_low h1e h0' (1 : ℝ) (-t)
      _ = x1 := by
            simp [MvPolynomial.smul_eq_C_mul, x0, x1]
  have h2e : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = e q2 := by
    simpa [e] using relation_map e.toAlgHom h2
  have h3e : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = e q3 := by
    simpa [e] using relation_map e.toAlgHom h3
  have hA0 : lowHomQuadPlaneA q2 q3 ≠ 0 := by
    simpa [lowHomQuadPlaneA] using hA
  have hrel2 :
      lowHomQuadPlaneA q2 q3 * MvPolynomial.coeff m20 q2 +
        (-lowHomQuadPlaneB q2 q3) * MvPolynomial.coeff m11 q2 +
          lowHomQuadPlaneC q2 q3 * MvPolynomial.coeff m02 q2 = 0 := by
    exact lowHomQuadPlane_relation_left q2 q3
  have hrel3 :
      lowHomQuadPlaneA q2 q3 * MvPolynomial.coeff m20 q3 +
        (-lowHomQuadPlaneB q2 q3) * MvPolynomial.coeff m11 q3 +
          lowHomQuadPlaneC q2 q3 * MvPolynomial.coeff m02 q3 = 0 := by
    exact lowHomQuadPlane_relation_right q2 q3
  have hq2' : IsQuadratic (e q2) := heQuad hq2
  have hq3' : IsQuadratic (e q3) := heQuad hq3
  have hq2_00' : MvPolynomial.coeff m00 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl, coeff_m00_affineHom_x1Shear hq2]
    simpa using hq2_00
  have hq2_10' : MvPolynomial.coeff m10 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl, coeff_m10_affineHom_x1Shear hq2]
    simp [hq2_10, hq2_01]
  have hq2_01' : MvPolynomial.coeff m01 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl, coeff_m01_affineHom_x1Shear hq2]
    simpa using hq2_01
  have hq3_00' : MvPolynomial.coeff m00 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl, coeff_m00_affineHom_x1Shear hq3]
    simpa using hq3_00
  have hq3_10' : MvPolynomial.coeff m10 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl, coeff_m10_affineHom_x1Shear hq3]
    simp [hq3_10, hq3_01]
  have hq3_01' : MvPolynomial.coeff m01 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl, coeff_m01_affineHom_x1Shear hq3]
    simpa using hq3_01
  have hq2_20_aux :
      lowHomQuadPlaneA q2 q3 * MvPolynomial.coeff m20 (e q2) +
        (lowHomQuadPlaneC q2 q3 - lowHomQuadPlaneB q2 q3 ^ 2 / lowHomQuadPlaneA q2 q3) *
          MvPolynomial.coeff m02 (e q2) = 0 := by
    simpa [e, t, pow_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      coeff_relation_affineHom_x1Shear_dual_kill_cross
        hq2 (a := lowHomQuadPlaneA q2 q3) (b := -lowHomQuadPlaneB q2 q3)
        (c := lowHomQuadPlaneC q2 q3) hA0 hrel2
  have hq3_20_aux :
      lowHomQuadPlaneA q2 q3 * MvPolynomial.coeff m20 (e q3) +
        (lowHomQuadPlaneC q2 q3 - lowHomQuadPlaneB q2 q3 ^ 2 / lowHomQuadPlaneA q2 q3) *
          MvPolynomial.coeff m02 (e q3) = 0 := by
    simpa [e, t, pow_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      coeff_relation_affineHom_x1Shear_dual_kill_cross
        hq3 (a := lowHomQuadPlaneA q2 q3) (b := -lowHomQuadPlaneB q2 q3)
        (c := lowHomQuadPlaneC q2 q3) hA0 hrel3
  have hq2_20' : MvPolynomial.coeff m20 (e q2) = 0 := by
    have hmul : lowHomQuadPlaneA q2 q3 * MvPolynomial.coeff m20 (e q2) = 0 := by
      simpa [hdiag0] using hq2_20_aux
    exact (mul_eq_zero.mp hmul).resolve_left hA0
  have hq3_20' : MvPolynomial.coeff m20 (e q3) = 0 := by
    have hmul : lowHomQuadPlaneA q2 q3 * MvPolynomial.coeff m20 (e q3) = 0 := by
      simpa [hdiag0] using hq3_20_aux
    exact (mul_eq_zero.mp hmul).resolve_left hA0
  have hdet' :
      MvPolynomial.coeff m11 (e q2) * MvPolynomial.coeff m02 (e q3) -
        MvPolynomial.coeff m02 (e q2) * MvPolynomial.coeff m11 (e q3) ≠ 0 := by
    have hdetEq :
        MvPolynomial.coeff m11 (e q2) * MvPolynomial.coeff m02 (e q3) -
          MvPolynomial.coeff m02 (e q2) * MvPolynomial.coeff m11 (e q3) =
        lowHomQuadPlaneA q2 q3 := by
      rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl,
        show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl,
        coeff_m11_affineHom_x1Shear hq2, coeff_m11_affineHom_x1Shear hq3,
        coeff_m02_affineHom_x1Shear hq2, coeff_m02_affineHom_x1Shear hq3]
      calc
        (MvPolynomial.coeff m11 q2 + 2 * MvPolynomial.coeff m02 q2 * t) *
              MvPolynomial.coeff m02 q3 -
            MvPolynomial.coeff m02 q2 *
              (MvPolynomial.coeff m11 q3 + 2 * MvPolynomial.coeff m02 q3 * t) =
            MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
              MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 := by
          ring
        _ = lowHomQuadPlaneA q2 q3 := by
          simp [lowHomQuadPlaneA]
    intro hz
    apply hA0
    simpa [hdetEq] using hz
  have h2' :
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i =
        MvPolynomial.coeff m11 (e q2) • (x0 * x1 : Poly) +
          MvPolynomial.coeff m02 (e q2) • (x1 ^ 2 : Poly) := by
    refine h2e.trans ?_
    exact homogeneousQuadratic_eq_x0x1_x1sq_of_coeff_m20_zero
      hq2' hq2_00' hq2_10' hq2_01' hq2_20'
  have h3' :
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i =
        MvPolynomial.coeff m11 (e q3) • (x0 * x1 : Poly) +
          MvPolynomial.coeff m02 (e q3) • (x1 ^ 2 : Poly) := by
    refine h3e.trans ?_
    exact homogeneousQuadratic_eq_x0x1_x1sq_of_coeff_m20_zero
      hq3' hq3_00' hq3_10' hq3_01' hq3_20'
  exact residual_eq_zero_of_equiv_relations_x0_x1_x0x1_x1sqPlane
    (e := e) (heQuad := fun {_} hq => heQuad hq) (heQuadSymm := fun {_} hq => heQuadSymm hq)
    (heQuartic := fun {_} hq => heQuartic hq)
    hB hp hu hsocp h0' h1' h2' h3' hdet'

private theorem quadratic_eq_one_plus_x0x1_x1sq_of_coeff_m20_zero
    {q : Poly}
    (hq : IsQuadratic q)
    (h00 : MvPolynomial.coeff m00 q = 1)
    (h10 : MvPolynomial.coeff m10 q = 0)
    (h01 : MvPolynomial.coeff m01 q = 0)
    (h20 : MvPolynomial.coeff m20 q = 0) :
    q = (1 : Poly) +
      MvPolynomial.coeff m11 q • (x0 * x1 : Poly) +
      MvPolynomial.coeff m02 q • (x1 ^ 2 : Poly) := by
  calc
    q =
      quadForm
        (MvPolynomial.coeff m00 q)
        (MvPolynomial.coeff m10 q)
        (MvPolynomial.coeff m01 q)
        (MvPolynomial.coeff m20 q)
        (MvPolynomial.coeff m11 q)
        (MvPolynomial.coeff m02 q) := by
          exact quadratic_eq_quadForm hq
    _ = (1 : Poly) +
          MvPolynomial.coeff m11 q • (x0 * x1 : Poly) +
          MvPolynomial.coeff m02 q • (x1 ^ 2 : Poly) := by
            rw [quadForm_eq_explicit, h00, h10, h01, h20]
            simp [add_assoc, MvPolynomial.smul_eq_C_mul]

theorem residual_eq_zero_of_relations_x0_x1_onePlus_homQuadratics_commonFactorChart
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 1)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 = 0)
    (hA :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 ≠ 0)
    (hdiag0 :
      lowHomQuadPlaneC q2 q3 -
        lowHomQuadPlaneB q2 q3 ^ 2 / lowHomQuadPlaneA q2 q3 = 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let t : ℝ := -lowHomQuadPlaneB q2 q3 / lowHomQuadPlaneA q2 q3
  let e : Poly ≃ₐ[ℝ] Poly := x1ShearEquiv t
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  have heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q) := by
    intro q hq
    exact isQuadratic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
      (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq
  have heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q) := by
    intro q hq
    exact isQuadratic_affineEquiv_symm (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
      (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq
  have heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q) := by
    intro q hq
    exact isQuartic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
      (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq
  have h0' : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0 := by
    simpa [e] using (relation_map e.toAlgHom h0).trans (affineHom_x1Shear_x0 t)
  have h1e : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = MvPolynomial.C t * x0 + x1 := by
    simpa [e] using (relation_map e.toAlgHom h1).trans (affineHom_x1Shear_x1 t)
  let c1' : Fin 4 → ℝ := fun i => c1 i + (-t) * c0 i
  have h1' : ∑ i : Fin 4, c1' i • mapVec e.toAlgHom u i = x1 := by
    calc
      ∑ i : Fin 4, c1' i • mapVec e.toAlgHom u i
          = 1 • (MvPolynomial.C t * x0 + x1) + (-t) • x0 := by
              simpa [c1'] using relation_linearCombination_low h1e h0' (1 : ℝ) (-t)
      _ = x1 := by
            simp [MvPolynomial.smul_eq_C_mul, x0, x1]
  have h2e : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = e q2 := by
    simpa [e] using relation_map e.toAlgHom h2
  have h3e : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = e q3 := by
    simpa [e] using relation_map e.toAlgHom h3
  have hA0 : lowHomQuadPlaneA q2 q3 ≠ 0 := by
    simpa [lowHomQuadPlaneA] using hA
  have hrel2 :
      lowHomQuadPlaneA q2 q3 * MvPolynomial.coeff m20 q2 +
        (-lowHomQuadPlaneB q2 q3) * MvPolynomial.coeff m11 q2 +
          lowHomQuadPlaneC q2 q3 * MvPolynomial.coeff m02 q2 = 0 := by
    exact lowHomQuadPlane_relation_left q2 q3
  have hrel3 :
      lowHomQuadPlaneA q2 q3 * MvPolynomial.coeff m20 q3 +
        (-lowHomQuadPlaneB q2 q3) * MvPolynomial.coeff m11 q3 +
          lowHomQuadPlaneC q2 q3 * MvPolynomial.coeff m02 q3 = 0 := by
    exact lowHomQuadPlane_relation_right q2 q3
  have hq2' : IsQuadratic (e q2) := heQuad hq2
  have hq3' : IsQuadratic (e q3) := heQuad hq3
  have hq2_00' : MvPolynomial.coeff m00 (e q2) = 1 := by
    rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl, coeff_m00_affineHom_x1Shear hq2]
    simpa using hq2_00
  have hq2_10' : MvPolynomial.coeff m10 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl, coeff_m10_affineHom_x1Shear hq2]
    simp [hq2_10, hq2_01]
  have hq2_01' : MvPolynomial.coeff m01 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl, coeff_m01_affineHom_x1Shear hq2]
    simpa using hq2_01
  have hq3_00' : MvPolynomial.coeff m00 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl, coeff_m00_affineHom_x1Shear hq3]
    simpa using hq3_00
  have hq3_10' : MvPolynomial.coeff m10 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl, coeff_m10_affineHom_x1Shear hq3]
    simp [hq3_10, hq3_01]
  have hq3_01' : MvPolynomial.coeff m01 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl, coeff_m01_affineHom_x1Shear hq3]
    simpa using hq3_01
  have hq2_20_aux :
      lowHomQuadPlaneA q2 q3 * MvPolynomial.coeff m20 (e q2) +
        (lowHomQuadPlaneC q2 q3 - lowHomQuadPlaneB q2 q3 ^ 2 / lowHomQuadPlaneA q2 q3) *
          MvPolynomial.coeff m02 (e q2) = 0 := by
    simpa [e, t, pow_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      coeff_relation_affineHom_x1Shear_dual_kill_cross
        hq2 (a := lowHomQuadPlaneA q2 q3) (b := -lowHomQuadPlaneB q2 q3)
        (c := lowHomQuadPlaneC q2 q3) hA0 hrel2
  have hq3_20_aux :
      lowHomQuadPlaneA q2 q3 * MvPolynomial.coeff m20 (e q3) +
        (lowHomQuadPlaneC q2 q3 - lowHomQuadPlaneB q2 q3 ^ 2 / lowHomQuadPlaneA q2 q3) *
          MvPolynomial.coeff m02 (e q3) = 0 := by
    simpa [e, t, pow_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      coeff_relation_affineHom_x1Shear_dual_kill_cross
        hq3 (a := lowHomQuadPlaneA q2 q3) (b := -lowHomQuadPlaneB q2 q3)
        (c := lowHomQuadPlaneC q2 q3) hA0 hrel3
  have hq2_20' : MvPolynomial.coeff m20 (e q2) = 0 := by
    have hmul : lowHomQuadPlaneA q2 q3 * MvPolynomial.coeff m20 (e q2) = 0 := by
      simpa [hdiag0] using hq2_20_aux
    exact (mul_eq_zero.mp hmul).resolve_left hA0
  have hq3_20' : MvPolynomial.coeff m20 (e q3) = 0 := by
    have hmul : lowHomQuadPlaneA q2 q3 * MvPolynomial.coeff m20 (e q3) = 0 := by
      simpa [hdiag0] using hq3_20_aux
    exact (mul_eq_zero.mp hmul).resolve_left hA0
  have hdet' :
      MvPolynomial.coeff m11 (e q2) * MvPolynomial.coeff m02 (e q3) -
        MvPolynomial.coeff m02 (e q2) * MvPolynomial.coeff m11 (e q3) ≠ 0 := by
    have hdetEq :
        MvPolynomial.coeff m11 (e q2) * MvPolynomial.coeff m02 (e q3) -
          MvPolynomial.coeff m02 (e q2) * MvPolynomial.coeff m11 (e q3) =
        lowHomQuadPlaneA q2 q3 := by
      rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl,
        show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl,
        coeff_m11_affineHom_x1Shear hq2, coeff_m11_affineHom_x1Shear hq3,
        coeff_m02_affineHom_x1Shear hq2, coeff_m02_affineHom_x1Shear hq3]
      calc
        (MvPolynomial.coeff m11 q2 + 2 * MvPolynomial.coeff m02 q2 * t) *
              MvPolynomial.coeff m02 q3 -
            MvPolynomial.coeff m02 q2 *
              (MvPolynomial.coeff m11 q3 + 2 * MvPolynomial.coeff m02 q3 * t) =
            MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
              MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 := by
          ring
        _ = lowHomQuadPlaneA q2 q3 := by
          simp [lowHomQuadPlaneA]
    intro hz
    apply hA0
    simpa [hdetEq] using hz
  have h2' :
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i =
        (1 : Poly) +
          MvPolynomial.coeff m11 (e q2) • (x0 * x1 : Poly) +
          MvPolynomial.coeff m02 (e q2) • (x1 ^ 2 : Poly) := by
    refine h2e.trans ?_
    exact quadratic_eq_one_plus_x0x1_x1sq_of_coeff_m20_zero
      hq2' hq2_00' hq2_10' hq2_01' hq2_20'
  have h3' :
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i =
        MvPolynomial.coeff m11 (e q3) • (x0 * x1 : Poly) +
          MvPolynomial.coeff m02 (e q3) • (x1 ^ 2 : Poly) := by
    refine h3e.trans ?_
    exact homogeneousQuadratic_eq_x0x1_x1sq_of_coeff_m20_zero
      hq3' hq3_00' hq3_10' hq3_01' hq3_20'
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
    exact residual_eq_zero_of_relations_x0_x1_onePlusBX0x1_x1sqPlane
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0' h1' h2' h3' hdet' hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_equiv_relations_x0_x1_onePlus_homQuadratics_commonFactorChart
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q))
    (heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q))
    (heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 1)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 = 0)
    (hA :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 ≠ 0)
    (hdiag0 :
      lowHomQuadPlaneC q2 q3 -
        lowHomQuadPlaneB q2 q3 ^ 2 / lowHomQuadPlaneA q2 q3 = 0) :
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
    exact residual_eq_zero_of_relations_x0_x1_onePlus_homQuadratics_commonFactorChart
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0 h1 h2 h3
      hq2 hq3 hq2_00 hq2_10 hq2_01 hq3_00 hq3_10 hq3_01 hA hdiag0 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_affinePair_onePlus_homQuadratics_commonFactorChart
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {r0 r1 : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = affineLinePoly r0 1 0)
    (h1 : ∑ i : Fin 4, c1 i • u i = affineLinePoly r1 0 1)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 :
      MvPolynomial.coeff m00
        (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q2) = 1)
    (hq2_10 :
      MvPolynomial.coeff m10
        (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q2) = 0)
    (hq2_01 :
      MvPolynomial.coeff m01
        (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q2) = 0)
    (hq3_00 :
      MvPolynomial.coeff m00
        (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q3) = 0)
    (hq3_10 :
      MvPolynomial.coeff m10
        (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q3) = 0)
    (hq3_01 :
      MvPolynomial.coeff m01
        (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q3) = 0)
    (hA :
      MvPolynomial.coeff m11
          (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q2) *
          MvPolynomial.coeff m02
            (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q3) -
        MvPolynomial.coeff m02
            (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q2) *
          MvPolynomial.coeff m11
            (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q3) ≠ 0)
    (hdiag0 :
      lowHomQuadPlaneC
          (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q2)
          (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q3) -
        lowHomQuadPlaneB
            (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q2)
            (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q3) ^ 2 /
          lowHomQuadPlaneA
            (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q2)
            (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q3) = 0)
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
  have heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q) := by
    intro q hq
    exact isQuadratic_affineEquiv
      (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
      (by simp) (by simp)
      (by
        intro i
        fin_cases i <;> simp [b, b'])
      (by
        intro i
        fin_cases i <;> simp [b, b']) hq
  have heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q) := by
    intro q hq
    exact isQuadratic_affineEquiv_symm
      (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
      (by simp) (by simp)
      (by
        intro i
        fin_cases i <;> simp [b, b'])
      (by
        intro i
        fin_cases i <;> simp [b, b']) hq
  have heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q) := by
    intro q hq
    exact isQuartic_affineEquiv
      (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
      (by simp) (by simp)
      (by
        intro i
        fin_cases i <;> simp [b, b'])
      (by
        intro i
        fin_cases i <;> simp [b, b']) hq
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  have h0trans : e (affineLinePoly r0 1 0) = x0 := by
    simp [e, b, b', affineLinePoly, affineEquiv, affineHom, affineImage, x0, x1,
      Fin.sum_univ_two]
  have h1trans : e (affineLinePoly r1 0 1) = x1 := by
    simp [e, b, b', affineLinePoly, affineEquiv, affineHom, affineImage, x0, x1,
      Fin.sum_univ_two]
  have h0' :
      ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0 := by
    simpa [e] using (relation_map e.toAlgHom h0).trans h0trans
  have h1' :
      ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1 := by
    simpa [e] using (relation_map e.toAlgHom h1).trans h1trans
  have h2' :
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) b q2 := by
    simpa [e, b] using relation_map e.toAlgHom h2
  have h3' :
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) b q3 := by
    simpa [e, b] using relation_map e.toAlgHom h3
  exact residual_eq_zero_of_equiv_relations_x0_x1_onePlus_homQuadratics_commonFactorChart
    (e := e) (heQuad := fun {_} hq => heQuad hq) (heQuadSymm := fun {_} hq => heQuadSymm hq)
    (heQuartic := fun {_} hq => heQuartic hq)
    hB hp hu hsocp h0' h1' h2' h3'
    (heQuad hq2) (heQuad hq3)
    hq2_00 hq2_10 hq2_01 hq3_00 hq3_10 hq3_01 hA hdiag0

theorem residual_eq_zero_of_equiv_relations_x0_x1_homQuadratics_commonFactorChart
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q))
    (heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q))
    (heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 = 0)
    (hA :
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 ≠ 0)
    (hdiag0 :
      lowHomQuadPlaneC q2 q3 -
        lowHomQuadPlaneB q2 q3 ^ 2 / lowHomQuadPlaneA q2 q3 = 0) :
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
    exact residual_eq_zero_of_relations_x0_x1_homQuadratics_commonFactorChart
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0 h1 h2 h3
      hq2 hq3 hq2_00 hq2_10 hq2_01 hq3_00 hq3_10 hq3_01 hA hdiag0 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_linearPair_homQuadratics_commonFactorChart
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {a b c d : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = linearForm a b)
    (h1 : ∑ i : Fin 4, c1 i • u i = linearForm c d)
    (hdetLin : a * d - b * c ≠ 0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 (linearPairEquiv a b c d hdetLin q2) = 0)
    (hq2_10 : MvPolynomial.coeff m10 (linearPairEquiv a b c d hdetLin q2) = 0)
    (hq2_01 : MvPolynomial.coeff m01 (linearPairEquiv a b c d hdetLin q2) = 0)
    (hq3_00 : MvPolynomial.coeff m00 (linearPairEquiv a b c d hdetLin q3) = 0)
    (hq3_10 : MvPolynomial.coeff m10 (linearPairEquiv a b c d hdetLin q3) = 0)
    (hq3_01 : MvPolynomial.coeff m01 (linearPairEquiv a b c d hdetLin q3) = 0)
    (hA :
      MvPolynomial.coeff m11 (linearPairEquiv a b c d hdetLin q2) *
          MvPolynomial.coeff m02 (linearPairEquiv a b c d hdetLin q3) -
        MvPolynomial.coeff m02 (linearPairEquiv a b c d hdetLin q2) *
          MvPolynomial.coeff m11 (linearPairEquiv a b c d hdetLin q3) ≠ 0)
    (hdiag0 :
      lowHomQuadPlaneC (linearPairEquiv a b c d hdetLin q2)
          (linearPairEquiv a b c d hdetLin q3) -
        lowHomQuadPlaneB (linearPairEquiv a b c d hdetLin q2)
            (linearPairEquiv a b c d hdetLin q3) ^ 2 /
          lowHomQuadPlaneA (linearPairEquiv a b c d hdetLin q2)
            (linearPairEquiv a b c d hdetLin q3) = 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let e : Poly ≃ₐ[ℝ] Poly := linearPairEquiv a b c d hdetLin
  have heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q) := by
    intro q hq
    exact isQuadratic_affineEquiv
      (linearPairMatrix a b c d) (linearPairInvMatrix a b c d) 0 0
      (linearPair_mul_inv a b c d hdetLin) (linearPair_inv_mul a b c d hdetLin)
      (by intro i; simp) (by intro i; simp) hq
  have heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q) := by
    intro q hq
    exact isQuadratic_affineEquiv_symm
      (linearPairMatrix a b c d) (linearPairInvMatrix a b c d) 0 0
      (linearPair_mul_inv a b c d hdetLin) (linearPair_inv_mul a b c d hdetLin)
      (by intro i; simp) (by intro i; simp) hq
  have heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q) := by
    intro q hq
    exact isQuartic_affineEquiv
      (linearPairMatrix a b c d) (linearPairInvMatrix a b c d) 0 0
      (linearPair_mul_inv a b c d hdetLin) (linearPair_inv_mul a b c d hdetLin)
      (by intro i; simp) (by intro i; simp) hq
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  have h0' : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0 := by
    simpa [e, linearPairEquiv] using
      (relation_map e.toAlgHom h0).trans (affineHom_linearPair_left a b c d hdetLin)
  have h1' : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1 := by
    simpa [e, linearPairEquiv] using
      (relation_map e.toAlgHom h1).trans (affineHom_linearPair_right a b c d hdetLin)
  have h2' : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = e q2 := by
    simpa [e] using relation_map e.toAlgHom h2
  have h3' : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = e q3 := by
    simpa [e] using relation_map e.toAlgHom h3
  exact residual_eq_zero_of_equiv_relations_x0_x1_homQuadratics_commonFactorChart
    (e := e) (heQuad := fun {_} hq => heQuad hq) (heQuadSymm := fun {_} hq => heQuadSymm hq)
    (heQuartic := fun {_} hq => heQuartic hq)
    hB hp hu hsocp h0' h1' h2' h3'
    (heQuad hq2) (heQuad hq3) hq2_00 hq2_10 hq2_01 hq3_00 hq3_10 hq3_01 hA hdiag0

theorem residual_eq_zero_of_relations_x0_x1_homQuadratics_diag_sum_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
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
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  have heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q) := by
    intro q hq
    exact isQuadratic_affineEquiv (x1ScaleMatrix s) (x1ScaleInvMatrix s) 0 0
      (x1Scale_mul_inv s hs) (x1Scale_inv_mul s hs) (by intro i; simp) (by intro i; simp) hq
  have heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q) := by
    intro q hq
    exact isQuadratic_affineEquiv_symm (x1ScaleMatrix s) (x1ScaleInvMatrix s) 0 0
      (x1Scale_mul_inv s hs) (x1Scale_inv_mul s hs) (by intro i; simp) (by intro i; simp) hq
  have heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q) := by
    intro q hq
    exact isQuartic_affineEquiv (x1ScaleMatrix s) (x1ScaleInvMatrix s) 0 0
      (x1Scale_mul_inv s hs) (x1Scale_inv_mul s hs) (by intro i; simp) (by intro i; simp) hq
  have h0' : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0 := by
    simpa [e] using (relation_map e.toAlgHom h0).trans (affineHom_x1Scale_x0 s)
  have h1e : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = MvPolynomial.C s * x1 := by
    simpa [e] using (relation_map e.toAlgHom h1).trans (affineHom_x1Scale_x1 s)
  let c1' : Fin 4 → ℝ := fun i => (1 / s) * c1 i
  have h1' : ∑ i : Fin 4, c1' i • mapVec e.toAlgHom u i = x1 := by
    calc
      ∑ i : Fin 4, c1' i • mapVec e.toAlgHom u i
          = (1 / s) • (∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i) := by
              simp [c1', Finset.smul_sum, smul_smul, mul_comm]
      _ = (1 / s) • (MvPolynomial.C s * x1) := by rw [h1e]
      _ = x1 := by
            rw [MvPolynomial.smul_eq_C_mul, x1, ← mul_assoc, ← MvPolynomial.C_mul]
            simp [one_div, hs]
  have h2' : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = e q2 := by
    simpa [e] using relation_map e.toAlgHom h2
  have h3' : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = e q3 := by
    simpa [e] using relation_map e.toAlgHom h3
  have hq2' : IsQuadratic (e q2) := heQuad hq2
  have hq3' : IsQuadratic (e q3) := heQuad hq3
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
  have h2'' :
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i =
        MvPolynomial.coeff m11 (e q2) • (x0 * x1 : Poly) +
          MvPolynomial.coeff m20 (e q2) • (x0 ^ 2 - x1 ^ 2 : Poly) := by
    refine h2'.trans ?_
    exact homogeneousQuadratic_eq_x0x1_diffsq_of_diag_sum_zero
      hq2' hq2_00' hq2_10' hq2_01' hq2_diag'
  have h3'' :
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i =
        MvPolynomial.coeff m11 (e q3) • (x0 * x1 : Poly) +
          MvPolynomial.coeff m20 (e q3) • (x0 ^ 2 - x1 ^ 2 : Poly) := by
    refine h3'.trans ?_
    exact homogeneousQuadratic_eq_x0x1_diffsq_of_diag_sum_zero
      hq3' hq3_00' hq3_10' hq3_01' hq3_diag'
  exact residual_eq_zero_of_equiv_relations_x0_x1_x0x1_diffsqPlane
    (e := e) (heQuad := fun {_} hq => heQuad hq) (heQuadSymm := fun {_} hq => heQuadSymm hq)
    (heQuartic := fun {_} hq => heQuartic hq)
    hB hp hu hsocp h0' h1' h2'' h3'' hdet'

theorem residual_eq_zero_of_equiv_relations_x0_x1_homQuadratics_diag_sum_zero
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q))
    (heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q))
    (heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = q3)
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
        MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m11 q3 ≠ 0) :
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
    exact residual_eq_zero_of_relations_x0_x1_homQuadratics_diag_sum_zero
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0 h1 h2 h3
      hq2 hq3 hq2_00 hq2_10 hq2_01 hq3_00 hq3_10 hq3_01
      ha hrel2 hrel3 hpos hdet hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_linearPair_homQuadratics_diag_sum_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {a b c d : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = linearForm a b)
    (h1 : ∑ i : Fin 4, c1 i • u i = linearForm c d)
    (hdetLin : a * d - b * c ≠ 0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 (linearPairEquiv a b c d hdetLin q2) = 0)
    (hq2_10 : MvPolynomial.coeff m10 (linearPairEquiv a b c d hdetLin q2) = 0)
    (hq2_01 : MvPolynomial.coeff m01 (linearPairEquiv a b c d hdetLin q2) = 0)
    (hq3_00 : MvPolynomial.coeff m00 (linearPairEquiv a b c d hdetLin q3) = 0)
    (hq3_10 : MvPolynomial.coeff m10 (linearPairEquiv a b c d hdetLin q3) = 0)
    (hq3_01 : MvPolynomial.coeff m01 (linearPairEquiv a b c d hdetLin q3) = 0)
    {u0 d0 : ℝ}
    (ha :
      u0 ≠ 0)
    (hrel2 :
      u0 * MvPolynomial.coeff m20 (linearPairEquiv a b c d hdetLin q2) +
        d0 * MvPolynomial.coeff m02 (linearPairEquiv a b c d hdetLin q2) = 0)
    (hrel3 :
      u0 * MvPolynomial.coeff m20 (linearPairEquiv a b c d hdetLin q3) +
        d0 * MvPolynomial.coeff m02 (linearPairEquiv a b c d hdetLin q3) = 0)
    (hpos : 0 < d0 / u0)
    (hdet :
      MvPolynomial.coeff m11 (linearPairEquiv a b c d hdetLin q2) *
          MvPolynomial.coeff m20 (linearPairEquiv a b c d hdetLin q3) -
        MvPolynomial.coeff m20 (linearPairEquiv a b c d hdetLin q2) *
          MvPolynomial.coeff m11 (linearPairEquiv a b c d hdetLin q3) ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let e : Poly ≃ₐ[ℝ] Poly := linearPairEquiv a b c d hdetLin
  have heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q) := by
    intro q hq
    exact isQuadratic_affineEquiv
      (linearPairMatrix a b c d) (linearPairInvMatrix a b c d) 0 0
      (linearPair_mul_inv a b c d hdetLin) (linearPair_inv_mul a b c d hdetLin)
      (by intro i; simp) (by intro i; simp) hq
  have heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q) := by
    intro q hq
    exact isQuadratic_affineEquiv_symm
      (linearPairMatrix a b c d) (linearPairInvMatrix a b c d) 0 0
      (linearPair_mul_inv a b c d hdetLin) (linearPair_inv_mul a b c d hdetLin)
      (by intro i; simp) (by intro i; simp) hq
  have heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q) := by
    intro q hq
    exact isQuartic_affineEquiv
      (linearPairMatrix a b c d) (linearPairInvMatrix a b c d) 0 0
      (linearPair_mul_inv a b c d hdetLin) (linearPair_inv_mul a b c d hdetLin)
      (by intro i; simp) (by intro i; simp) hq
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  have h0' : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0 := by
    simpa [e, linearPairEquiv] using
      (relation_map e.toAlgHom h0).trans (affineHom_linearPair_left a b c d hdetLin)
  have h1' : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1 := by
    simpa [e, linearPairEquiv] using
      (relation_map e.toAlgHom h1).trans (affineHom_linearPair_right a b c d hdetLin)
  have h2' : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = e q2 := by
    simpa [e] using relation_map e.toAlgHom h2
  have h3' : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = e q3 := by
    simpa [e] using relation_map e.toAlgHom h3
  exact residual_eq_zero_of_equiv_relations_x0_x1_homQuadratics_diag_sum_zero
    (e := e) (heQuad := fun {_} hq => heQuad hq) (heQuadSymm := fun {_} hq => heQuadSymm hq)
    (heQuartic := fun {_} hq => heQuartic hq)
    hB hp hu hsocp h0' h1' h2' h3'
    (heQuad hq2) (heQuad hq3) hq2_00 hq2_10 hq2_01 hq3_00 hq3_10 hq3_01
    ha hrel2 hrel3 hpos hdet

theorem residual_eq_zero_of_relations_x0_x1_homQuadratics_diag_diff_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
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
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  have heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q) := by
    intro q hq
    exact isQuadratic_affineEquiv (x1ScaleMatrix s) (x1ScaleInvMatrix s) 0 0
      (x1Scale_mul_inv s hs) (x1Scale_inv_mul s hs) (by intro i; simp) (by intro i; simp) hq
  have heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q) := by
    intro q hq
    exact isQuadratic_affineEquiv_symm (x1ScaleMatrix s) (x1ScaleInvMatrix s) 0 0
      (x1Scale_mul_inv s hs) (x1Scale_inv_mul s hs) (by intro i; simp) (by intro i; simp) hq
  have heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q) := by
    intro q hq
    exact isQuartic_affineEquiv (x1ScaleMatrix s) (x1ScaleInvMatrix s) 0 0
      (x1Scale_mul_inv s hs) (x1Scale_inv_mul s hs) (by intro i; simp) (by intro i; simp) hq
  have h0' : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0 := by
    simpa [e] using (relation_map e.toAlgHom h0).trans (affineHom_x1Scale_x0 s)
  have h1e : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = MvPolynomial.C s * x1 := by
    simpa [e] using (relation_map e.toAlgHom h1).trans (affineHom_x1Scale_x1 s)
  let c1' : Fin 4 → ℝ := fun i => (1 / s) * c1 i
  have h1' : ∑ i : Fin 4, c1' i • mapVec e.toAlgHom u i = x1 := by
    calc
      ∑ i : Fin 4, c1' i • mapVec e.toAlgHom u i
          = (1 / s) • (∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i) := by
              simp [c1', Finset.smul_sum, smul_smul, mul_comm]
      _ = (1 / s) • (MvPolynomial.C s * x1) := by rw [h1e]
      _ = x1 := by
            rw [MvPolynomial.smul_eq_C_mul, x1, ← mul_assoc, ← MvPolynomial.C_mul]
            simp [one_div, hs]
  have h2' : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = e q2 := by
    simpa [e] using relation_map e.toAlgHom h2
  have h3' : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = e q3 := by
    simpa [e] using relation_map e.toAlgHom h3
  have hq2' : IsQuadratic (e q2) := heQuad hq2
  have hq3' : IsQuadratic (e q3) := heQuad hq3
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
  have h2'' :
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i =
        MvPolynomial.coeff m11 (e q2) • (x0 * x1 : Poly) +
          MvPolynomial.coeff m20 (e q2) • (x0 ^ 2 + x1 ^ 2 : Poly) := by
    refine h2'.trans ?_
    exact homogeneousQuadratic_eq_x0x1_sumsq_of_diag_diff_zero
      hq2' hq2_00' hq2_10' hq2_01' hq2_diag'
  have h3'' :
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i =
        MvPolynomial.coeff m11 (e q3) • (x0 * x1 : Poly) +
          MvPolynomial.coeff m20 (e q3) • (x0 ^ 2 + x1 ^ 2 : Poly) := by
    refine h3'.trans ?_
    exact homogeneousQuadratic_eq_x0x1_sumsq_of_diag_diff_zero
      hq3' hq3_00' hq3_10' hq3_01' hq3_diag'
  exact residual_eq_zero_of_equiv_relations_x0_x1_x0x1_sumsqPlane
    (e := e) (heQuad := fun {_} hq => heQuad hq) (heQuadSymm := fun {_} hq => heQuadSymm hq)
    (heQuartic := fun {_} hq => heQuartic hq)
    hB hp hu hsocp h0' h1' h2'' h3'' hdet'

theorem residual_eq_zero_of_equiv_relations_x0_x1_homQuadratics_diag_diff_zero
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q))
    (heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q))
    (heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = q3)
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
        MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m11 q3 ≠ 0) :
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
    exact residual_eq_zero_of_relations_x0_x1_homQuadratics_diag_diff_zero
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0 h1 h2 h3
      hq2 hq3 hq2_00 hq2_10 hq2_01 hq3_00 hq3_10 hq3_01
      ha hrel2 hrel3 hpos hdet hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_linearPair_homQuadratics_diag_diff_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {a b c d : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = linearForm a b)
    (h1 : ∑ i : Fin 4, c1 i • u i = linearForm c d)
    (hdetLin : a * d - b * c ≠ 0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 (linearPairEquiv a b c d hdetLin q2) = 0)
    (hq2_10 : MvPolynomial.coeff m10 (linearPairEquiv a b c d hdetLin q2) = 0)
    (hq2_01 : MvPolynomial.coeff m01 (linearPairEquiv a b c d hdetLin q2) = 0)
    (hq3_00 : MvPolynomial.coeff m00 (linearPairEquiv a b c d hdetLin q3) = 0)
    (hq3_10 : MvPolynomial.coeff m10 (linearPairEquiv a b c d hdetLin q3) = 0)
    (hq3_01 : MvPolynomial.coeff m01 (linearPairEquiv a b c d hdetLin q3) = 0)
    {u0 d0 : ℝ}
    (ha :
      u0 ≠ 0)
    (hrel2 :
      u0 * MvPolynomial.coeff m20 (linearPairEquiv a b c d hdetLin q2) +
        d0 * MvPolynomial.coeff m02 (linearPairEquiv a b c d hdetLin q2) = 0)
    (hrel3 :
      u0 * MvPolynomial.coeff m20 (linearPairEquiv a b c d hdetLin q3) +
        d0 * MvPolynomial.coeff m02 (linearPairEquiv a b c d hdetLin q3) = 0)
    (hpos : 0 < (-d0) / u0)
    (hdet :
      MvPolynomial.coeff m11 (linearPairEquiv a b c d hdetLin q2) *
          MvPolynomial.coeff m20 (linearPairEquiv a b c d hdetLin q3) -
        MvPolynomial.coeff m20 (linearPairEquiv a b c d hdetLin q2) *
          MvPolynomial.coeff m11 (linearPairEquiv a b c d hdetLin q3) ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let e : Poly ≃ₐ[ℝ] Poly := linearPairEquiv a b c d hdetLin
  have heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q) := by
    intro q hq
    exact isQuadratic_affineEquiv
      (linearPairMatrix a b c d) (linearPairInvMatrix a b c d) 0 0
      (linearPair_mul_inv a b c d hdetLin) (linearPair_inv_mul a b c d hdetLin)
      (by intro i; simp) (by intro i; simp) hq
  have heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q) := by
    intro q hq
    exact isQuadratic_affineEquiv_symm
      (linearPairMatrix a b c d) (linearPairInvMatrix a b c d) 0 0
      (linearPair_mul_inv a b c d hdetLin) (linearPair_inv_mul a b c d hdetLin)
      (by intro i; simp) (by intro i; simp) hq
  have heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q) := by
    intro q hq
    exact isQuartic_affineEquiv
      (linearPairMatrix a b c d) (linearPairInvMatrix a b c d) 0 0
      (linearPair_mul_inv a b c d hdetLin) (linearPair_inv_mul a b c d hdetLin)
      (by intro i; simp) (by intro i; simp) hq
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  have h0' : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0 := by
    simpa [e, linearPairEquiv] using
      (relation_map e.toAlgHom h0).trans (affineHom_linearPair_left a b c d hdetLin)
  have h1' : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1 := by
    simpa [e, linearPairEquiv] using
      (relation_map e.toAlgHom h1).trans (affineHom_linearPair_right a b c d hdetLin)
  have h2' : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = e q2 := by
    simpa [e] using relation_map e.toAlgHom h2
  have h3' : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = e q3 := by
    simpa [e] using relation_map e.toAlgHom h3
  exact residual_eq_zero_of_equiv_relations_x0_x1_homQuadratics_diag_diff_zero
    (e := e) (heQuad := fun {_} hq => heQuad hq) (heQuadSymm := fun {_} hq => heQuadSymm hq)
    (heQuartic := fun {_} hq => heQuartic hq)
    hB hp hu hsocp h0' h1' h2' h3'
    (heQuad hq2) (heQuad hq3) hq2_00 hq2_10 hq2_01 hq3_00 hq3_10 hq3_01
    ha hrel2 hrel3 hpos hdet

private theorem coeff_m02_zero_of_lowHomQuadPlaneA_B_zero_C_ne_zero
    {q2 q3 : Poly}
    (hA0 : lowHomQuadPlaneA q2 q3 = 0)
    (hB0 : lowHomQuadPlaneB q2 q3 = 0)
    (hC : lowHomQuadPlaneC q2 q3 ≠ 0) :
    MvPolynomial.coeff m02 q2 = 0 ∧ MvPolynomial.coeff m02 q3 = 0 := by
  have hAeq :
      MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 =
        MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 := by
    have h := hA0
    dsimp [lowHomQuadPlaneA] at h
    linarith
  have hBeq :
      MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3 =
        MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m02 q3 := by
    have h := hB0
    dsimp [lowHomQuadPlaneB] at h
    linarith
  have hmul2 :
      MvPolynomial.coeff m02 q2 * lowHomQuadPlaneC q2 q3 = 0 := by
    calc
      MvPolynomial.coeff m02 q2 * lowHomQuadPlaneC q2 q3
          =
            MvPolynomial.coeff m20 q2 *
                (MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3) -
              MvPolynomial.coeff m11 q2 *
                (MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3) := by
              simp [lowHomQuadPlaneC]
              ring
      _ =
            MvPolynomial.coeff m20 q2 *
                (MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3) -
              MvPolynomial.coeff m11 q2 *
                (MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m02 q3) := by
              rw [hAeq, hBeq]
      _ = 0 := by ring
  have hmul3 :
      MvPolynomial.coeff m02 q3 * lowHomQuadPlaneC q2 q3 = 0 := by
    calc
      MvPolynomial.coeff m02 q3 * lowHomQuadPlaneC q2 q3
          =
            (MvPolynomial.coeff m20 q2 * MvPolynomial.coeff m02 q3) *
                MvPolynomial.coeff m11 q3 -
              (MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3) *
                MvPolynomial.coeff m20 q3 := by
              simp [lowHomQuadPlaneC]
              ring
      _ =
            (MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m20 q3) *
                MvPolynomial.coeff m11 q3 -
              (MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3) *
                MvPolynomial.coeff m20 q3 := by
              rw [← hBeq, ← hAeq]
      _ = 0 := by ring
  constructor
  · exact (mul_eq_zero.mp hmul2).resolve_right hC
  · exact (mul_eq_zero.mp hmul3).resolve_right hC

private theorem det_x0x1_x1sq_affineHom_x1Shear
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (t : ℝ) :
    MvPolynomial.coeff m11 (affineHom (x1ShearMatrix t) 0 q2) *
        MvPolynomial.coeff m02 (affineHom (x1ShearMatrix t) 0 q3) -
      MvPolynomial.coeff m02 (affineHom (x1ShearMatrix t) 0 q2) *
        MvPolynomial.coeff m11 (affineHom (x1ShearMatrix t) 0 q3) =
      lowHomQuadPlaneA q2 q3 := by
  rw [coeff_m11_affineHom_x1Shear hq2, coeff_m11_affineHom_x1Shear hq3,
    coeff_m02_affineHom_x1Shear hq2, coeff_m02_affineHom_x1Shear hq3]
  calc
    (MvPolynomial.coeff m11 q2 + 2 * MvPolynomial.coeff m02 q2 * t) *
          MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 *
          (MvPolynomial.coeff m11 q3 + 2 * MvPolynomial.coeff m02 q3 * t) =
      MvPolynomial.coeff m11 q2 * MvPolynomial.coeff m02 q3 -
        MvPolynomial.coeff m02 q2 * MvPolynomial.coeff m11 q3 := by
          ring
    _ = lowHomQuadPlaneA q2 q3 := by
          simp [lowHomQuadPlaneA]

private theorem det_x0x1_x0sq_affineHom_x1Shear_kill_cross
    {q2 q3 : Poly}
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hA : lowHomQuadPlaneA q2 q3 ≠ 0) :
    MvPolynomial.coeff m11
        (affineHom
          (x1ShearMatrix (-lowHomQuadPlaneB q2 q3 / lowHomQuadPlaneA q2 q3)) 0 q2) *
        MvPolynomial.coeff m20
          (affineHom
            (x1ShearMatrix (-lowHomQuadPlaneB q2 q3 / lowHomQuadPlaneA q2 q3)) 0 q3) -
      MvPolynomial.coeff m20
          (affineHom
            (x1ShearMatrix (-lowHomQuadPlaneB q2 q3 / lowHomQuadPlaneA q2 q3)) 0 q2) *
        MvPolynomial.coeff m11
          (affineHom
            (x1ShearMatrix (-lowHomQuadPlaneB q2 q3 / lowHomQuadPlaneA q2 q3)) 0 q3) =
      -(lowHomQuadPlaneC q2 q3 -
          lowHomQuadPlaneB q2 q3 ^ 2 / lowHomQuadPlaneA q2 q3) := by
  let t : ℝ := -lowHomQuadPlaneB q2 q3 / lowHomQuadPlaneA q2 q3
  rw [coeff_m11_affineHom_x1Shear hq2, coeff_m11_affineHom_x1Shear hq3,
    coeff_m20_affineHom_x1Shear hq2, coeff_m20_affineHom_x1Shear hq3]
  field_simp [hA]
  simp [lowHomQuadPlaneA, lowHomQuadPlaneB, lowHomQuadPlaneC]
  ring

theorem residual_eq_zero_of_relations_x0_x1_homQuadratics_diagSumChart
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
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
    (hA : lowHomQuadPlaneA q2 q3 ≠ 0)
    (hpos :
      0 <
        (lowHomQuadPlaneC q2 q3 -
            lowHomQuadPlaneB q2 q3 ^ 2 / lowHomQuadPlaneA q2 q3) /
          lowHomQuadPlaneA q2 q3)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let d : ℝ :=
    lowHomQuadPlaneC q2 q3 -
      lowHomQuadPlaneB q2 q3 ^ 2 / lowHomQuadPlaneA q2 q3
  let t : ℝ := -lowHomQuadPlaneB q2 q3 / lowHomQuadPlaneA q2 q3
  let e : Poly ≃ₐ[ℝ] Poly := x1ShearEquiv t
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  have heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q) := by
    intro q hq
    exact isQuadratic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
      (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq
  have heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q) := by
    intro q hq
    exact isQuadratic_affineEquiv_symm (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
      (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq
  have heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q) := by
    intro q hq
    exact isQuartic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
      (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq
  have h0' : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0 := by
    simpa [e] using (relation_map e.toAlgHom h0).trans (affineHom_x1Shear_x0 t)
  have h1e : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = MvPolynomial.C t * x0 + x1 := by
    simpa [e] using (relation_map e.toAlgHom h1).trans (affineHom_x1Shear_x1 t)
  let c1' : Fin 4 → ℝ := fun i => c1 i + (-t) * c0 i
  have h1' : ∑ i : Fin 4, c1' i • mapVec e.toAlgHom u i = x1 := by
    calc
      ∑ i : Fin 4, c1' i • mapVec e.toAlgHom u i
          = 1 • (MvPolynomial.C t * x0 + x1) + (-t) • x0 := by
              simpa [c1'] using relation_linearCombination_low h1e h0' (1 : ℝ) (-t)
      _ = x1 := by
            simp [MvPolynomial.smul_eq_C_mul, x0, x1]
  have h2' : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = e q2 := by
    simpa [e] using relation_map e.toAlgHom h2
  have h3' : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = e q3 := by
    simpa [e] using relation_map e.toAlgHom h3
  have hrel2 :
      lowHomQuadPlaneA q2 q3 * MvPolynomial.coeff m20 q2 +
        (-lowHomQuadPlaneB q2 q3) * MvPolynomial.coeff m11 q2 +
          lowHomQuadPlaneC q2 q3 * MvPolynomial.coeff m02 q2 = 0 := by
    exact lowHomQuadPlane_relation_left q2 q3
  have hrel3 :
      lowHomQuadPlaneA q2 q3 * MvPolynomial.coeff m20 q3 +
        (-lowHomQuadPlaneB q2 q3) * MvPolynomial.coeff m11 q3 +
          lowHomQuadPlaneC q2 q3 * MvPolynomial.coeff m02 q3 = 0 := by
    exact lowHomQuadPlane_relation_right q2 q3
  have hq2e : IsQuadratic (e q2) := heQuad hq2
  have hq3e : IsQuadratic (e q3) := heQuad hq3
  have hq2_00' : MvPolynomial.coeff m00 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl, coeff_m00_affineHom_x1Shear hq2]
    simpa using hq2_00
  have hq2_10' : MvPolynomial.coeff m10 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl, coeff_m10_affineHom_x1Shear hq2]
    simp [hq2_10, hq2_01]
  have hq2_01' : MvPolynomial.coeff m01 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl, coeff_m01_affineHom_x1Shear hq2]
    simpa using hq2_01
  have hq3_00' : MvPolynomial.coeff m00 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl, coeff_m00_affineHom_x1Shear hq3]
    simpa using hq3_00
  have hq3_10' : MvPolynomial.coeff m10 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl, coeff_m10_affineHom_x1Shear hq3]
    simp [hq3_10, hq3_01]
  have hq3_01' : MvPolynomial.coeff m01 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl, coeff_m01_affineHom_x1Shear hq3]
    simpa using hq3_01
  have hq2_diag :
      lowHomQuadPlaneA q2 q3 * MvPolynomial.coeff m20 (e q2) +
        d * MvPolynomial.coeff m02 (e q2) = 0 := by
    simpa [e, t, d, pow_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      coeff_relation_affineHom_x1Shear_dual_kill_cross
        hq2 (a := lowHomQuadPlaneA q2 q3) (b := -lowHomQuadPlaneB q2 q3)
        (c := lowHomQuadPlaneC q2 q3) hA hrel2
  have hq3_diag :
      lowHomQuadPlaneA q2 q3 * MvPolynomial.coeff m20 (e q3) +
        d * MvPolynomial.coeff m02 (e q3) = 0 := by
    simpa [e, t, d, pow_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      coeff_relation_affineHom_x1Shear_dual_kill_cross
        hq3 (a := lowHomQuadPlaneA q2 q3) (b := -lowHomQuadPlaneB q2 q3)
        (c := lowHomQuadPlaneC q2 q3) hA hrel3
  have hd : d ≠ 0 := by
    intro hd0
    have : d / lowHomQuadPlaneA q2 q3 = 0 := by
      simp [d, hd0]
    exact (ne_of_gt hpos) this
  have hdet' :
      MvPolynomial.coeff m11 (e q2) * MvPolynomial.coeff m20 (e q3) -
        MvPolynomial.coeff m20 (e q2) * MvPolynomial.coeff m11 (e q3) ≠ 0 := by
    have hdetEq :
        MvPolynomial.coeff m11 (e q2) * MvPolynomial.coeff m20 (e q3) -
          MvPolynomial.coeff m20 (e q2) * MvPolynomial.coeff m11 (e q3) =
        -d := by
      simpa [e, d] using det_x0x1_x0sq_affineHom_x1Shear_kill_cross hq2 hq3 hA
    intro hz
    apply hd
    linarith [hdetEq, hz]
  exact residual_eq_zero_of_equiv_relations_x0_x1_homQuadratics_diag_sum_zero
    (e := e) (heQuad := fun {_} hq => heQuad hq) (heQuadSymm := fun {_} hq => heQuadSymm hq)
    (heQuartic := fun {_} hq => heQuartic hq)
    hB hp hu hsocp h0' h1' h2' h3'
    hq2e hq3e hq2_00' hq2_10' hq2_01' hq3_00' hq3_10' hq3_01'
    hA hq2_diag hq3_diag hpos hdet'

theorem residual_eq_zero_of_relations_x0_x1_homQuadratics_diagDiffChart
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
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
    (hA : lowHomQuadPlaneA q2 q3 ≠ 0)
    (hpos :
      0 <
        (-(lowHomQuadPlaneC q2 q3 -
            lowHomQuadPlaneB q2 q3 ^ 2 / lowHomQuadPlaneA q2 q3)) /
          lowHomQuadPlaneA q2 q3)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let d : ℝ :=
    lowHomQuadPlaneC q2 q3 -
      lowHomQuadPlaneB q2 q3 ^ 2 / lowHomQuadPlaneA q2 q3
  let t : ℝ := -lowHomQuadPlaneB q2 q3 / lowHomQuadPlaneA q2 q3
  let e : Poly ≃ₐ[ℝ] Poly := x1ShearEquiv t
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  have heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q) := by
    intro q hq
    exact isQuadratic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
      (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq
  have heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q) := by
    intro q hq
    exact isQuadratic_affineEquiv_symm (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
      (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq
  have heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q) := by
    intro q hq
    exact isQuartic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
      (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq
  have h0' : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0 := by
    simpa [e] using (relation_map e.toAlgHom h0).trans (affineHom_x1Shear_x0 t)
  have h1e : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = MvPolynomial.C t * x0 + x1 := by
    simpa [e] using (relation_map e.toAlgHom h1).trans (affineHom_x1Shear_x1 t)
  let c1' : Fin 4 → ℝ := fun i => c1 i + (-t) * c0 i
  have h1' : ∑ i : Fin 4, c1' i • mapVec e.toAlgHom u i = x1 := by
    calc
      ∑ i : Fin 4, c1' i • mapVec e.toAlgHom u i
          = 1 • (MvPolynomial.C t * x0 + x1) + (-t) • x0 := by
              simpa [c1'] using relation_linearCombination_low h1e h0' (1 : ℝ) (-t)
      _ = x1 := by
            simp [MvPolynomial.smul_eq_C_mul, x0, x1]
  have h2' : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = e q2 := by
    simpa [e] using relation_map e.toAlgHom h2
  have h3' : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = e q3 := by
    simpa [e] using relation_map e.toAlgHom h3
  have hrel2 :
      lowHomQuadPlaneA q2 q3 * MvPolynomial.coeff m20 q2 +
        (-lowHomQuadPlaneB q2 q3) * MvPolynomial.coeff m11 q2 +
          lowHomQuadPlaneC q2 q3 * MvPolynomial.coeff m02 q2 = 0 := by
    exact lowHomQuadPlane_relation_left q2 q3
  have hrel3 :
      lowHomQuadPlaneA q2 q3 * MvPolynomial.coeff m20 q3 +
        (-lowHomQuadPlaneB q2 q3) * MvPolynomial.coeff m11 q3 +
          lowHomQuadPlaneC q2 q3 * MvPolynomial.coeff m02 q3 = 0 := by
    exact lowHomQuadPlane_relation_right q2 q3
  have hq2e : IsQuadratic (e q2) := heQuad hq2
  have hq3e : IsQuadratic (e q3) := heQuad hq3
  have hq2_00' : MvPolynomial.coeff m00 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl, coeff_m00_affineHom_x1Shear hq2]
    simpa using hq2_00
  have hq2_10' : MvPolynomial.coeff m10 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl, coeff_m10_affineHom_x1Shear hq2]
    simp [hq2_10, hq2_01]
  have hq2_01' : MvPolynomial.coeff m01 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl, coeff_m01_affineHom_x1Shear hq2]
    simpa using hq2_01
  have hq3_00' : MvPolynomial.coeff m00 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl, coeff_m00_affineHom_x1Shear hq3]
    simpa using hq3_00
  have hq3_10' : MvPolynomial.coeff m10 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl, coeff_m10_affineHom_x1Shear hq3]
    simp [hq3_10, hq3_01]
  have hq3_01' : MvPolynomial.coeff m01 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl, coeff_m01_affineHom_x1Shear hq3]
    simpa using hq3_01
  have hq2_diag :
      lowHomQuadPlaneA q2 q3 * MvPolynomial.coeff m20 (e q2) +
        d * MvPolynomial.coeff m02 (e q2) = 0 := by
    simpa [e, t, d, pow_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      coeff_relation_affineHom_x1Shear_dual_kill_cross
        hq2 (a := lowHomQuadPlaneA q2 q3) (b := -lowHomQuadPlaneB q2 q3)
        (c := lowHomQuadPlaneC q2 q3) hA hrel2
  have hq3_diag :
      lowHomQuadPlaneA q2 q3 * MvPolynomial.coeff m20 (e q3) +
        d * MvPolynomial.coeff m02 (e q3) = 0 := by
    simpa [e, t, d, pow_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      coeff_relation_affineHom_x1Shear_dual_kill_cross
        hq3 (a := lowHomQuadPlaneA q2 q3) (b := -lowHomQuadPlaneB q2 q3)
        (c := lowHomQuadPlaneC q2 q3) hA hrel3
  have hd : d ≠ 0 := by
    intro hd0
    have : (-d) / lowHomQuadPlaneA q2 q3 = 0 := by
      simp [d, hd0]
    exact (ne_of_gt hpos) this
  have hdet' :
      MvPolynomial.coeff m11 (e q2) * MvPolynomial.coeff m20 (e q3) -
        MvPolynomial.coeff m20 (e q2) * MvPolynomial.coeff m11 (e q3) ≠ 0 := by
    have hdetEq :
        MvPolynomial.coeff m11 (e q2) * MvPolynomial.coeff m20 (e q3) -
          MvPolynomial.coeff m20 (e q2) * MvPolynomial.coeff m11 (e q3) =
        -d := by
      simpa [e, d] using det_x0x1_x0sq_affineHom_x1Shear_kill_cross hq2 hq3 hA
    intro hz
    apply hd
    linarith [hdetEq, hz]
  exact residual_eq_zero_of_equiv_relations_x0_x1_homQuadratics_diag_diff_zero
    (e := e) (heQuad := fun {_} hq => heQuad hq) (heQuadSymm := fun {_} hq => heQuadSymm hq)
    (heQuartic := fun {_} hq => heQuartic hq)
    hB hp hu hsocp h0' h1' h2' h3'
    hq2e hq3e hq2_00' hq2_10' hq2_01' hq3_00' hq3_10' hq3_01'
    hA hq2_diag hq3_diag hpos hdet'

private theorem quadratic_eq_one_plus_x0x1_sumsq_of_diag_diff_zero
    {q : Poly}
    (hq : IsQuadratic q)
    (h00 : MvPolynomial.coeff m00 q = 1)
    (h10 : MvPolynomial.coeff m10 q = 0)
    (h01 : MvPolynomial.coeff m01 q = 0)
    (hdiag : MvPolynomial.coeff m20 q - MvPolynomial.coeff m02 q = 0) :
    q = (1 : Poly) +
      MvPolynomial.coeff m11 q • (x0 * x1 : Poly) +
      MvPolynomial.coeff m20 q • (x0 ^ 2 + x1 ^ 2 : Poly) := by
  have h02 : MvPolynomial.coeff m02 q = MvPolynomial.coeff m20 q := by
    linarith
  calc
    q =
      quadForm
        (MvPolynomial.coeff m00 q)
        (MvPolynomial.coeff m10 q)
        (MvPolynomial.coeff m01 q)
        (MvPolynomial.coeff m20 q)
        (MvPolynomial.coeff m11 q)
        (MvPolynomial.coeff m02 q) := by
          exact quadratic_eq_quadForm hq
    _ = (1 : Poly) +
          MvPolynomial.coeff m11 q • (x0 * x1 : Poly) +
          MvPolynomial.coeff m20 q • (x0 ^ 2 + x1 ^ 2 : Poly) := by
            rw [quadForm_eq_explicit, h00, h10, h01, h02]
            simp [add_assoc, add_left_comm, MvPolynomial.smul_eq_C_mul]

theorem residual_eq_zero_of_relations_x0_x1_onePlus_homQuadratics_diag_diff_zero
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 1)
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
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  have heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q) := by
    intro q hq
    exact isQuadratic_affineEquiv (x1ScaleMatrix s) (x1ScaleInvMatrix s) 0 0
      (x1Scale_mul_inv s hs) (x1Scale_inv_mul s hs) (by intro i; simp) (by intro i; simp) hq
  have heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q) := by
    intro q hq
    exact isQuadratic_affineEquiv_symm (x1ScaleMatrix s) (x1ScaleInvMatrix s) 0 0
      (x1Scale_mul_inv s hs) (x1Scale_inv_mul s hs) (by intro i; simp) (by intro i; simp) hq
  have heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q) := by
    intro q hq
    exact isQuartic_affineEquiv (x1ScaleMatrix s) (x1ScaleInvMatrix s) 0 0
      (x1Scale_mul_inv s hs) (x1Scale_inv_mul s hs) (by intro i; simp) (by intro i; simp) hq
  have h0' : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0 := by
    simpa [e] using (relation_map e.toAlgHom h0).trans (affineHom_x1Scale_x0 s)
  have h1e : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = MvPolynomial.C s * x1 := by
    simpa [e] using (relation_map e.toAlgHom h1).trans (affineHom_x1Scale_x1 s)
  let c1' : Fin 4 → ℝ := fun i => (1 / s) * c1 i
  have h1' : ∑ i : Fin 4, c1' i • mapVec e.toAlgHom u i = x1 := by
    calc
      ∑ i : Fin 4, c1' i • mapVec e.toAlgHom u i
          = (1 / s) • (∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i) := by
              simp [c1', Finset.smul_sum, smul_smul, mul_comm]
      _ = (1 / s) • (MvPolynomial.C s * x1) := by rw [h1e]
      _ = x1 := by
            rw [MvPolynomial.smul_eq_C_mul, x1, ← mul_assoc, ← MvPolynomial.C_mul]
            simp [one_div, hs]
  have h2' : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = e q2 := by
    simpa [e] using relation_map e.toAlgHom h2
  have h3' : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = e q3 := by
    simpa [e] using relation_map e.toAlgHom h3
  have hq2' : IsQuadratic (e q2) := heQuad hq2
  have hq3' : IsQuadratic (e q3) := heQuad hq3
  have hq2_00' : MvPolynomial.coeff m00 (e q2) = 1 := by
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
  have h2'' :
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i =
        (1 : Poly) +
          MvPolynomial.coeff m11 (e q2) • (x0 * x1 : Poly) +
          MvPolynomial.coeff m20 (e q2) • (x0 ^ 2 + x1 ^ 2 : Poly) := by
    refine h2'.trans ?_
    exact quadratic_eq_one_plus_x0x1_sumsq_of_diag_diff_zero
      hq2' hq2_00' hq2_10' hq2_01' hq2_diag'
  have h3'' :
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i =
        MvPolynomial.coeff m11 (e q3) • (x0 * x1 : Poly) +
          MvPolynomial.coeff m20 (e q3) • (x0 ^ 2 + x1 ^ 2 : Poly) := by
    refine h3'.trans ?_
    exact homogeneousQuadratic_eq_x0x1_sumsq_of_diag_diff_zero
      hq3' hq3_00' hq3_10' hq3_01' hq3_diag'
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
    exact residual_eq_zero_of_relations_x0_x1_onePlusX0x1_sumsqPlane
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0' h1' h2'' h3'' hdet' hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_x0_x1_onePlus_homQuadratics_diagDiffChart
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 1)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 = 0)
    (hA : lowHomQuadPlaneA q2 q3 ≠ 0)
    (hpos :
      0 <
        (-(lowHomQuadPlaneC q2 q3 -
            lowHomQuadPlaneB q2 q3 ^ 2 / lowHomQuadPlaneA q2 q3)) /
          lowHomQuadPlaneA q2 q3)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let d : ℝ :=
    lowHomQuadPlaneC q2 q3 -
      lowHomQuadPlaneB q2 q3 ^ 2 / lowHomQuadPlaneA q2 q3
  let t : ℝ := -lowHomQuadPlaneB q2 q3 / lowHomQuadPlaneA q2 q3
  let e : Poly ≃ₐ[ℝ] Poly := x1ShearEquiv t
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  have heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q) := by
    intro q hq
    exact isQuadratic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
      (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq
  have heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q) := by
    intro q hq
    exact isQuadratic_affineEquiv_symm (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
      (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq
  have heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q) := by
    intro q hq
    exact isQuartic_affineEquiv (x1ShearMatrix t) (x1ShearInvMatrix t) 0 0
      (x1Shear_mul_inv t) (x1Shear_inv_mul t) (by intro i; simp) (by intro i; simp) hq
  have h0' : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0 := by
    simpa [e] using (relation_map e.toAlgHom h0).trans (affineHom_x1Shear_x0 t)
  have h1e : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = MvPolynomial.C t * x0 + x1 := by
    simpa [e] using (relation_map e.toAlgHom h1).trans (affineHom_x1Shear_x1 t)
  let c1' : Fin 4 → ℝ := fun i => c1 i + (-t) * c0 i
  have h1' : ∑ i : Fin 4, c1' i • mapVec e.toAlgHom u i = x1 := by
    calc
      ∑ i : Fin 4, c1' i • mapVec e.toAlgHom u i
          = 1 • (MvPolynomial.C t * x0 + x1) + (-t) • x0 := by
              simpa [c1'] using relation_linearCombination_low h1e h0' (1 : ℝ) (-t)
      _ = x1 := by
            simp [MvPolynomial.smul_eq_C_mul, x0, x1]
  have h2' : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = e q2 := by
    simpa [e] using relation_map e.toAlgHom h2
  have h3' : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = e q3 := by
    simpa [e] using relation_map e.toAlgHom h3
  have hrel2 :
      lowHomQuadPlaneA q2 q3 * MvPolynomial.coeff m20 q2 +
        (-lowHomQuadPlaneB q2 q3) * MvPolynomial.coeff m11 q2 +
          lowHomQuadPlaneC q2 q3 * MvPolynomial.coeff m02 q2 = 0 := by
    exact lowHomQuadPlane_relation_left q2 q3
  have hrel3 :
      lowHomQuadPlaneA q2 q3 * MvPolynomial.coeff m20 q3 +
        (-lowHomQuadPlaneB q2 q3) * MvPolynomial.coeff m11 q3 +
          lowHomQuadPlaneC q2 q3 * MvPolynomial.coeff m02 q3 = 0 := by
    exact lowHomQuadPlane_relation_right q2 q3
  have hq2e : IsQuadratic (e q2) := heQuad hq2
  have hq3e : IsQuadratic (e q3) := heQuad hq3
  have hq2_00' : MvPolynomial.coeff m00 (e q2) = 1 := by
    rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl, coeff_m00_affineHom_x1Shear hq2]
    simpa using hq2_00
  have hq2_10' : MvPolynomial.coeff m10 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl, coeff_m10_affineHom_x1Shear hq2]
    simp [hq2_10, hq2_01]
  have hq2_01' : MvPolynomial.coeff m01 (e q2) = 0 := by
    rw [show e q2 = affineHom (x1ShearMatrix t) 0 q2 by rfl, coeff_m01_affineHom_x1Shear hq2]
    simpa using hq2_01
  have hq3_00' : MvPolynomial.coeff m00 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl, coeff_m00_affineHom_x1Shear hq3]
    simpa using hq3_00
  have hq3_10' : MvPolynomial.coeff m10 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl, coeff_m10_affineHom_x1Shear hq3]
    simp [hq3_10, hq3_01]
  have hq3_01' : MvPolynomial.coeff m01 (e q3) = 0 := by
    rw [show e q3 = affineHom (x1ShearMatrix t) 0 q3 by rfl, coeff_m01_affineHom_x1Shear hq3]
    simpa using hq3_01
  have hq2_diag :
      lowHomQuadPlaneA q2 q3 * MvPolynomial.coeff m20 (e q2) +
        d * MvPolynomial.coeff m02 (e q2) = 0 := by
    simpa [e, t, d, pow_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      coeff_relation_affineHom_x1Shear_dual_kill_cross
        hq2 (a := lowHomQuadPlaneA q2 q3) (b := -lowHomQuadPlaneB q2 q3)
        (c := lowHomQuadPlaneC q2 q3) hA hrel2
  have hq3_diag :
      lowHomQuadPlaneA q2 q3 * MvPolynomial.coeff m20 (e q3) +
        d * MvPolynomial.coeff m02 (e q3) = 0 := by
    simpa [e, t, d, pow_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      coeff_relation_affineHom_x1Shear_dual_kill_cross
        hq3 (a := lowHomQuadPlaneA q2 q3) (b := -lowHomQuadPlaneB q2 q3)
        (c := lowHomQuadPlaneC q2 q3) hA hrel3
  have hd : d ≠ 0 := by
    intro hd0
    have : (-d) / lowHomQuadPlaneA q2 q3 = 0 := by
      simp [d, hd0]
    exact (ne_of_gt hpos) this
  have hdet' :
      MvPolynomial.coeff m11 (e q2) * MvPolynomial.coeff m20 (e q3) -
        MvPolynomial.coeff m20 (e q2) * MvPolynomial.coeff m11 (e q3) ≠ 0 := by
    have hdetEq :
        MvPolynomial.coeff m11 (e q2) * MvPolynomial.coeff m20 (e q3) -
          MvPolynomial.coeff m20 (e q2) * MvPolynomial.coeff m11 (e q3) =
        -d := by
      simpa [e, d] using det_x0x1_x0sq_affineHom_x1Shear_kill_cross hq2 hq3 hA
    intro hz
    apply hd
    linarith [hdetEq, hz]
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
    exact residual_eq_zero_of_relations_x0_x1_onePlus_homQuadratics_diag_diff_zero
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0' h1' h2' h3'
      hq2e hq3e hq2_00' hq2_10' hq2_01' hq3_00' hq3_10' hq3_01'
      hA hq2_diag hq3_diag hpos hdet' hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_x0_x1_homQuadratics_plane_nontrivial
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
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
      lowHomQuadPlaneA q2 q3 ≠ 0 ∨
        lowHomQuadPlaneB q2 q3 ≠ 0 ∨ lowHomQuadPlaneC q2 q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  by_cases hA : lowHomQuadPlaneA q2 q3 = 0
  · by_cases hB : lowHomQuadPlaneB q2 q3 = 0
    · have hC : lowHomQuadPlaneC q2 q3 ≠ 0 := by
        rcases hplane with hA' | hrest
        · exact False.elim (hA' hA)
        · rcases hrest with hB' | hC'
          · exact False.elim (hB' hB)
          · exact hC'
      have h02 : MvPolynomial.coeff m02 q2 = 0 ∧ MvPolynomial.coeff m02 q3 = 0 := by
        exact coeff_m02_zero_of_lowHomQuadPlaneA_B_zero_C_ne_zero hA hB hC
      have h2' :
          ∑ i : Fin 4, c2 i • u i =
            MvPolynomial.coeff m20 q2 • (x0 ^ 2 : Poly) +
              MvPolynomial.coeff m11 q2 • (x0 * x1 : Poly) := by
        refine h2.trans ?_
        exact homogeneousQuadratic_eq_x0sq_x0x1_of_coeff_m02_zero
          hq2 hq2_00 hq2_10 hq2_01 h02.1
      have h3' :
          ∑ i : Fin 4, c3 i • u i =
            MvPolynomial.coeff m20 q3 • (x0 ^ 2 : Poly) +
              MvPolynomial.coeff m11 q3 • (x0 * x1 : Poly) := by
        refine h3.trans ?_
        exact homogeneousQuadratic_eq_x0sq_x0x1_of_coeff_m02_zero
          hq3 hq3_00 hq3_10 hq3_01 h02.2
      exact residual_eq_zero_of_relations_x0_x1_x0sq_x0x1Plane
        (B := B) (u := u) hu h0 h1 h2' h3'
        (by simpa [lowHomQuadPlaneC] using hC) hp hsocp
    · exact residual_eq_zero_of_relations_x0_x1_homQuadratics_crossDet_zero
        (B := B) (u := u) hu h0 h1 h2 h3
        hq2 hq3 hq2_00 hq2_10 hq2_01 hq3_00 hq3_10 hq3_01
        (by simpa [lowHomQuadPlaneA] using hA)
        (by simpa [lowHomQuadPlaneB] using hB) hp hsocp
  · let d : ℝ :=
      lowHomQuadPlaneC q2 q3 -
        lowHomQuadPlaneB q2 q3 ^ 2 / lowHomQuadPlaneA q2 q3
    by_cases hd : d = 0
    · exact residual_eq_zero_of_relations_x0_x1_homQuadratics_commonFactorChart
        (B := B) (u := u) hu h0 h1 h2 h3
        hq2 hq3 hq2_00 hq2_10 hq2_01 hq3_00 hq3_10 hq3_01
        (by simpa [lowHomQuadPlaneA] using hA)
        (by simpa [d] using hd) hp hsocp
    · have hsgn :
          d / lowHomQuadPlaneA q2 q3 < 0 ∨
            0 < d / lowHomQuadPlaneA q2 q3 := by
        exact lt_or_gt_of_ne (div_ne_zero hd hA)
      rcases hsgn with hneg | hpos
      · have hpos' : 0 < (-d) / lowHomQuadPlaneA q2 q3 := by
          simpa [neg_div] using (neg_pos.mpr hneg)
        exact residual_eq_zero_of_relations_x0_x1_homQuadratics_diagDiffChart
          (B := B) (u := u) hu h0 h1 h2 h3
          hq2 hq3 hq2_00 hq2_10 hq2_01 hq3_00 hq3_10 hq3_01
          hA hpos' hp hsocp
      · exact residual_eq_zero_of_relations_x0_x1_homQuadratics_diagSumChart
          (B := B) (u := u) hu h0 h1 h2 h3
          hq2 hq3 hq2_00 hq2_10 hq2_01 hq3_00 hq3_10 hq3_01
          hA hpos hp hsocp

theorem residual_eq_zero_of_relations_x0_x1_homQuadratics_independent
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
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
    (hind : LinearIndependent ℝ ![q2, q3])
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_relations_x0_x1_homQuadratics_plane_nontrivial
    (B := B) (u := u) hu h0 h1 h2 h3 hq2 hq3
    hq2_00 hq2_10 hq2_01 hq3_00 hq3_10 hq3_01
    (lowHomQuadPlane_nontrivial_of_independent_pair
      hq2 hq3 hq2_00 hq2_10 hq2_01 hq3_00 hq3_10 hq3_01 hind)
    hp hsocp

private theorem coeff_m10_one_lowAffine :
    MvPolynomial.coeff m10 (1 : Poly) = 0 := by
  rw [show (1 : Poly) = MvPolynomial.C (1 : ℝ) by simp, MvPolynomial.coeff_C]
  split_ifs with h
  · exfalso
    have h0 := congrArg (fun s : Fin 2 →₀ ℕ => s 0) h.symm
    simp [m10] at h0
  · rfl

private theorem coeff_m01_one_lowAffine :
    MvPolynomial.coeff m01 (1 : Poly) = 0 := by
  rw [show (1 : Poly) = MvPolynomial.C (1 : ℝ) by simp, MvPolynomial.coeff_C]
  split_ifs with h
  · exfalso
    have h1 := congrArg (fun s : Fin 2 →₀ ℕ => s 1) h.symm
    simp [m01] at h1
  · rfl

private theorem coeff_m20_one_lowAffine :
    MvPolynomial.coeff m20 (1 : Poly) = 0 := by
  rw [show (1 : Poly) = MvPolynomial.C (1 : ℝ) by simp, MvPolynomial.coeff_C]
  split_ifs with h
  · exfalso
    have h0 := congrArg (fun s : Fin 2 →₀ ℕ => s 0) h.symm
    simp [m20] at h0
  · rfl

private theorem coeff_m11_one_lowAffine :
    MvPolynomial.coeff m11 (1 : Poly) = 0 := by
  rw [show (1 : Poly) = MvPolynomial.C (1 : ℝ) by simp, MvPolynomial.coeff_C]
  split_ifs with h
  · exfalso
    have h0 := congrArg (fun s : Fin 2 →₀ ℕ => s 0) h.symm
    simp [m11] at h0
  · rfl

private theorem coeff_m02_one_lowAffine :
    MvPolynomial.coeff m02 (1 : Poly) = 0 := by
  rw [show (1 : Poly) = MvPolynomial.C (1 : ℝ) by simp, MvPolynomial.coeff_C]
  split_ifs with h
  · exfalso
    have h1 := congrArg (fun s : Fin 2 →₀ ℕ => s 1) h.symm
    simp [m02] at h1
  · rfl

theorem residual_eq_zero_of_relations_x0_x1_onePlus_homQuadratics_dependent
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 1)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 = 0)
    (hA0 : lowHomQuadPlaneA q2 q3 = 0)
    (hB0 : lowHomQuadPlaneB q2 q3 = 0)
    (hC0 : lowHomQuadPlaneC q2 q3 = 0)
    (hq3_ne : q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let q2h : Poly := q2 - 1
  have hq2h : IsQuadratic q2h := by
    dsimp [q2h]
    simpa [sub_eq_add_neg] using
      isQuadratic_linearCombination_local hq2 (by
        change ((1 : Poly).totalDegree ≤ 2)
        simp) 1 (-1)
  have hq2h_00 : MvPolynomial.coeff m00 q2h = 0 := by
    dsimp [q2h]
    rw [MvPolynomial.coeff_sub, hq2_00]
    simp
  have hm10_one : MvPolynomial.coeff m10 (1 : Poly) = 0 := by
    rw [show (1 : Poly) = MvPolynomial.C (1 : ℝ) by simp, MvPolynomial.coeff_C]
    split_ifs with h
    · exfalso
      have h0 := congrArg (fun s : Fin 2 →₀ ℕ => s 0) h.symm
      simp [m10] at h0
    · rfl
  have hm01_one : MvPolynomial.coeff m01 (1 : Poly) = 0 := by
    rw [show (1 : Poly) = MvPolynomial.C (1 : ℝ) by simp, MvPolynomial.coeff_C]
    split_ifs with h
    · exfalso
      have h1' := congrArg (fun s : Fin 2 →₀ ℕ => s 1) h.symm
      simp [m01] at h1'
    · rfl
  have hm20_one : MvPolynomial.coeff m20 (1 : Poly) = 0 := by
    rw [show (1 : Poly) = MvPolynomial.C (1 : ℝ) by simp, MvPolynomial.coeff_C]
    split_ifs with h
    · exfalso
      have h0 := congrArg (fun s : Fin 2 →₀ ℕ => s 0) h.symm
      simp [m20] at h0
    · rfl
  have hm11_one : MvPolynomial.coeff m11 (1 : Poly) = 0 := by
    rw [show (1 : Poly) = MvPolynomial.C (1 : ℝ) by simp, MvPolynomial.coeff_C]
    split_ifs with h
    · exfalso
      have h0 := congrArg (fun s : Fin 2 →₀ ℕ => s 0) h.symm
      simp [m11] at h0
    · rfl
  have hm02_one : MvPolynomial.coeff m02 (1 : Poly) = 0 := by
    rw [show (1 : Poly) = MvPolynomial.C (1 : ℝ) by simp, MvPolynomial.coeff_C]
    split_ifs with h
    · exfalso
      have h1' := congrArg (fun s : Fin 2 →₀ ℕ => s 1) h.symm
      simp [m02] at h1'
    · rfl
  have hq2h_10 : MvPolynomial.coeff m10 q2h = 0 := by
    dsimp [q2h]
    rw [MvPolynomial.coeff_sub, hq2_10]
    simp [hm10_one]
  have hq2h_01 : MvPolynomial.coeff m01 q2h = 0 := by
    dsimp [q2h]
    rw [MvPolynomial.coeff_sub, hq2_01]
    simp [hm01_one]
  have hA0h : lowHomQuadPlaneA q2h q3 = 0 := by
    dsimp [lowHomQuadPlaneA, q2h]
    simpa [MvPolynomial.coeff_sub, hm11_one, hm02_one] using hA0
  have hB0h : lowHomQuadPlaneB q2h q3 = 0 := by
    dsimp [lowHomQuadPlaneB, q2h]
    simpa [MvPolynomial.coeff_sub, hm20_one, hm02_one] using hB0
  have hC0h : lowHomQuadPlaneC q2h q3 = 0 := by
    dsimp [lowHomQuadPlaneC, q2h]
    simpa [MvPolynomial.coeff_sub, hm20_one, hm11_one] using hC0
  by_cases hq2h_zero : q2h = 0
  · have hconst : ∑ i : Fin 4, c2 i • u i = (1 : Poly) := by
      have hq2_const : q2 = (1 : Poly) := by
        exact sub_eq_zero.mp hq2h_zero
      exact h2.trans hq2_const
    exact residual_eq_zero_of_contains_aff1
      (B := B) (u := u) (c0 := c2) (c1 := c0) (c2 := c1)
      hu hconst h0 h1 hp hsocp
  · obtain ⟨t, hq3_eq⟩ :=
      lowHomQuadPlane_zero_imp_smul
        hq2h hq3 hq2h_00 hq2h_10 hq2h_01 hq3_00 hq3_10 hq3_01 hq2h_zero
        hA0h hB0h hC0h
    have ht_ne : t ≠ 0 := by
      intro ht
      apply hq3_ne
      rw [hq3_eq, ht]
      simp
    let cconst : Fin 4 → ℝ := fun i => c2 i + (-(t⁻¹)) * c3 i
    have hq2_split : q2 = (1 : Poly) + q2h := by
      dsimp [q2h]
      ring
    have hconst : ∑ i : Fin 4, cconst i • u i = (1 : Poly) := by
      calc
        ∑ i : Fin 4, cconst i • u i = 1 • q2 + (-(t⁻¹)) • q3 := by
          simpa [cconst] using relation_linearCombination_low h2 h3 (1 : ℝ) (-(t⁻¹))
        _ = (1 : Poly) + q2h + (-(t⁻¹ * t)) • q2h := by
          rw [hq2_split, hq3_eq]
          simp [smul_smul]
        _ = (1 : Poly) := by
          have hmul : t⁻¹ * t = 1 := by
            field_simp [ht_ne]
          simp [hmul]
    exact residual_eq_zero_of_contains_aff1
      (B := B) (u := u) (c0 := cconst) (c1 := c0) (c2 := c1)
      hu hconst h0 h1 hp hsocp

theorem residual_eq_zero_of_relations_x0_x1_onePlus_homQuadratics_not_independent
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 1)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 = 0)
    (hnotind : ¬ LinearIndependent ℝ ![q2 - (1 : Poly), q3])
    (hq3_ne : q3 ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let q2h : Poly := q2 - 1
  have hnotind' : ¬ LinearIndependent ℝ ![q2h, q3] := by
    simpa [q2h] using hnotind
  have hsmul : ∃ t : ℝ, t • q3 = q2h := by
    rw [linearIndependent_fin2] at hnotind'
    by_contra hno
    have hall : ∀ a : ℝ, a • q3 ≠ q2h := by
      intro a ha
      exact hno ⟨a, ha⟩
    exact hnotind' ⟨hq3_ne, hall⟩
  rcases hsmul with ⟨t, ht⟩
  have hA0h : lowHomQuadPlaneA q2h q3 = 0 := by
    simpa [ht] using (lowHomQuadPlane_zero_of_smul_left (q := q3) t).1
  have hB0h : lowHomQuadPlaneB q2h q3 = 0 := by
    simpa [ht] using (lowHomQuadPlane_zero_of_smul_left (q := q3) t).2.1
  have hC0h : lowHomQuadPlaneC q2h q3 = 0 := by
    simpa [ht] using (lowHomQuadPlane_zero_of_smul_left (q := q3) t).2.2
  have hA0 : lowHomQuadPlaneA q2 q3 = 0 := by
    dsimp [q2h, lowHomQuadPlaneA] at hA0h ⊢
    simpa [MvPolynomial.coeff_sub, coeff_m11_one_lowAffine, coeff_m02_one_lowAffine] using hA0h
  have hB0 : lowHomQuadPlaneB q2 q3 = 0 := by
    dsimp [q2h, lowHomQuadPlaneB] at hB0h ⊢
    simpa [MvPolynomial.coeff_sub, coeff_m20_one_lowAffine, coeff_m02_one_lowAffine] using hB0h
  have hC0 : lowHomQuadPlaneC q2 q3 = 0 := by
    dsimp [q2h, lowHomQuadPlaneC] at hC0h ⊢
    simpa [MvPolynomial.coeff_sub, coeff_m20_one_lowAffine, coeff_m11_one_lowAffine] using hC0h
  exact residual_eq_zero_of_relations_x0_x1_onePlus_homQuadratics_dependent
    (B := B) (u := u) hu h0 h1 h2 h3 hq2 hq3
    hq2_00 hq2_10 hq2_01 hq3_00 hq3_10 hq3_01
    hA0 hB0 hC0 hq3_ne hp hsocp

theorem residual_eq_zero_of_relations_affinePair_homQuadratics_independent
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {r0 r1 : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = affineLinePoly r0 1 0)
    (h1 : ∑ i : Fin 4, c1 i • u i = affineLinePoly r1 0 1)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q2) = 0)
    (hq2_10 : MvPolynomial.coeff m10 (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q2) = 0)
    (hq2_01 : MvPolynomial.coeff m01 (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q2) = 0)
    (hq3_00 : MvPolynomial.coeff m00 (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q3) = 0)
    (hq3_10 : MvPolynomial.coeff m10 (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q3) = 0)
    (hq3_01 : MvPolynomial.coeff m01 (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q3) = 0)
    (hind :
      LinearIndependent ℝ
        ![affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q2,
          affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-r0, -r1] q3])
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
  have heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q) := by
    intro q hq
    exact isQuadratic_affineEquiv
      (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
      (by simp) (by simp)
      (by intro i; fin_cases i <;> simp [b, b'])
      (by intro i; fin_cases i <;> simp [b, b']) hq
  have heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q) := by
    intro q hq
    exact isQuadratic_affineEquiv_symm
      (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
      (by simp) (by simp)
      (by intro i; fin_cases i <;> simp [b, b'])
      (by intro i; fin_cases i <;> simp [b, b']) hq
  have heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q) := by
    intro q hq
    exact isQuartic_affineEquiv
      (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 b b'
      (by simp) (by simp)
      (by intro i; fin_cases i <;> simp [b, b'])
      (by intro i; fin_cases i <;> simp [b, b']) hq
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  have h0' : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0 := by
    calc
      ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = e (affineLinePoly r0 1 0) := by
        simpa [e] using relation_map e.toAlgHom h0
      _ = x0 := by
        simp [e, b, b', affineLinePoly, affineEquiv, affineHom, affineImage, x0, x1,
          Fin.sum_univ_two]
  have h1' : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1 := by
    calc
      ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = e (affineLinePoly r1 0 1) := by
        simpa [e] using relation_map e.toAlgHom h1
      _ = x1 := by
        simp [e, b, b', affineLinePoly, affineEquiv, affineHom, affineImage, x0, x1,
          Fin.sum_univ_two]
  have h2' : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) b q2 := by
    simpa [e, b] using relation_map e.toAlgHom h2
  have h3' : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) b q3 := by
    simpa [e, b] using relation_map e.toAlgHom h3
  have hq2' : IsQuadratic (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) b q2) := by
    simpa [b] using isQuadratic_affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) b hq2
  have hq3' : IsQuadratic (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) b q3) := by
    simpa [b] using isQuadratic_affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) b hq3
  have hplane :
      lowHomQuadPlaneA (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) b q2)
          (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) b q3) ≠ 0 ∨
        lowHomQuadPlaneB (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) b q2)
            (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) b q3) ≠ 0 ∨
          lowHomQuadPlaneC (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) b q2)
            (affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) b q3) ≠ 0 := by
    exact lowHomQuadPlane_nontrivial_of_independent_pair
      hq2' hq3' (by simpa [b] using hq2_00) (by simpa [b] using hq2_10) (by simpa [b] using hq2_01)
      (by simpa [b] using hq3_00) (by simpa [b] using hq3_10) (by simpa [b] using hq3_01)
      (by simpa [b] using hind)
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
    exact residual_eq_zero_of_relations_x0_x1_homQuadratics_plane_nontrivial
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0' h1' h2' h3' hq2' hq3'
      (by simpa [b] using hq2_00) (by simpa [b] using hq2_10) (by simpa [b] using hq2_01)
      (by simpa [b] using hq3_00) (by simpa [b] using hq3_10) (by simpa [b] using hq3_01)
      hplane hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_equiv_relations_x0_x1_homQuadratics_plane_nontrivial
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q))
    (heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q))
    (heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 q2 = 0)
    (hq2_10 : MvPolynomial.coeff m10 q2 = 0)
    (hq2_01 : MvPolynomial.coeff m01 q2 = 0)
    (hq3_00 : MvPolynomial.coeff m00 q3 = 0)
    (hq3_10 : MvPolynomial.coeff m10 q3 = 0)
    (hq3_01 : MvPolynomial.coeff m01 q3 = 0)
    (hplane :
      lowHomQuadPlaneA q2 q3 ≠ 0 ∨
        lowHomQuadPlaneB q2 q3 ≠ 0 ∨ lowHomQuadPlaneC q2 q3 ≠ 0) :
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
    exact residual_eq_zero_of_relations_x0_x1_homQuadratics_plane_nontrivial
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0 h1 h2 h3
      hq2 hq3 hq2_00 hq2_10 hq2_01 hq3_00 hq3_10 hq3_01 hplane hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_linearPair_homQuadratics_plane_nontrivial
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {a b c d : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = linearForm a b)
    (h1 : ∑ i : Fin 4, c1 i • u i = linearForm c d)
    (hdetLin : a * d - b * c ≠ 0)
    {q2 q3 : Poly}
    (h2 : ∑ i : Fin 4, c2 i • u i = q2)
    (h3 : ∑ i : Fin 4, c3 i • u i = q3)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    (hq2_00 : MvPolynomial.coeff m00 (linearPairEquiv a b c d hdetLin q2) = 0)
    (hq2_10 : MvPolynomial.coeff m10 (linearPairEquiv a b c d hdetLin q2) = 0)
    (hq2_01 : MvPolynomial.coeff m01 (linearPairEquiv a b c d hdetLin q2) = 0)
    (hq3_00 : MvPolynomial.coeff m00 (linearPairEquiv a b c d hdetLin q3) = 0)
    (hq3_10 : MvPolynomial.coeff m10 (linearPairEquiv a b c d hdetLin q3) = 0)
    (hq3_01 : MvPolynomial.coeff m01 (linearPairEquiv a b c d hdetLin q3) = 0)
    (hplane :
      lowHomQuadPlaneA (linearPairEquiv a b c d hdetLin q2)
          (linearPairEquiv a b c d hdetLin q3) ≠ 0 ∨
        lowHomQuadPlaneB (linearPairEquiv a b c d hdetLin q2)
            (linearPairEquiv a b c d hdetLin q3) ≠ 0 ∨
          lowHomQuadPlaneC (linearPairEquiv a b c d hdetLin q2)
            (linearPairEquiv a b c d hdetLin q3) ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let e : Poly ≃ₐ[ℝ] Poly := linearPairEquiv a b c d hdetLin
  have heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q) := by
    intro q hq
    exact isQuadratic_affineEquiv
      (linearPairMatrix a b c d) (linearPairInvMatrix a b c d) 0 0
      (linearPair_mul_inv a b c d hdetLin) (linearPair_inv_mul a b c d hdetLin)
      (by intro i; simp) (by intro i; simp) hq
  have heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q) := by
    intro q hq
    exact isQuadratic_affineEquiv_symm
      (linearPairMatrix a b c d) (linearPairInvMatrix a b c d) 0 0
      (linearPair_mul_inv a b c d hdetLin) (linearPair_inv_mul a b c d hdetLin)
      (by intro i; simp) (by intro i; simp) hq
  have heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q) := by
    intro q hq
    exact isQuartic_affineEquiv
      (linearPairMatrix a b c d) (linearPairInvMatrix a b c d) 0 0
      (linearPair_mul_inv a b c d hdetLin) (linearPair_inv_mul a b c d hdetLin)
      (by intro i; simp) (by intro i; simp) hq
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  have h0' : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0 := by
    simpa [e, linearPairEquiv] using
      (relation_map e.toAlgHom h0).trans (affineHom_linearPair_left a b c d hdetLin)
  have h1' : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1 := by
    simpa [e, linearPairEquiv] using
      (relation_map e.toAlgHom h1).trans (affineHom_linearPair_right a b c d hdetLin)
  have h2' : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = e q2 := by
    simpa [e] using relation_map e.toAlgHom h2
  have h3' : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = e q3 := by
    simpa [e] using relation_map e.toAlgHom h3
  exact residual_eq_zero_of_equiv_relations_x0_x1_homQuadratics_plane_nontrivial
    (e := e) (heQuad := fun {_} hq => heQuad hq) (heQuadSymm := fun {_} hq => heQuadSymm hq)
    (heQuartic := fun {_} hq => heQuartic hq)
    hB hp hu hsocp h0' h1' h2' h3'
    (heQuad hq2) (heQuad hq3) hq2_00 hq2_10 hq2_01 hq3_00 hq3_10 hq3_01 hplane

theorem residual_eq_zero_of_socp_of_eq_mix_mapVec_x0_x1_homQuadratics_plane_nontrivial
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
      lowHomQuadPlaneA q2 q3 ≠ 0 ∨
        lowHomQuadPlaneB q2 q3 ≠ 0 ∨ lowHomQuadPlaneC q2 q3 ≠ 0)
    (huRep : mix M.transpose (mapVec e.symm.toAlgHom u) = ![x0, x1, q2, q3])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have huRepAdmissible : IsAdmissiblePoint (![x0, x1, q2, q3] : RankFourVec) := by
    intro i
    fin_cases i
    · simpa [x0] using (show IsQuadratic (MvPolynomial.X 0 : Poly) by simp [IsQuadratic])
    · simpa [x1] using (show IsQuadratic (MvPolynomial.X 1 : Poly) by simp [IsQuadratic])
    · simpa using hq2
    · simpa using hq3
  have hRep :
      ∀ {B0 : DotForm} [Fact B0.toQuadraticMap.PosDef] {p0 : Poly},
        IsSOSQuartic p0 → IsSOCP B0 p0 (![x0, x1, q2, q3] : RankFourVec) →
          residual p0 (![x0, x1, q2, q3] : RankFourVec) = 0 := by
    intro B0 _ p0 hp0 hsocp0
    exact residual_eq_zero_of_relations_x0_x1_homQuadratics_plane_nontrivial
      (c0 := ![1, 0, 0, 0]) (c1 := ![0, 1, 0, 0])
      (c2 := ![0, 0, 1, 0]) (c3 := ![0, 0, 0, 1])
      (B := B0) (u := ![x0, x1, q2, q3]) huRepAdmissible
      (h0 := by simp [Fin.sum_univ_four, x0])
      (h1 := by simp [Fin.sum_univ_four, x1])
      (h2 := by simp [Fin.sum_univ_four])
      (h3 := by simp [Fin.sum_univ_four])
      hq2 hq3 hq2_00 hq2_10 hq2_01 hq3_00 hq3_10 hq3_01 hplane hp0 hsocp0
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec
    (![x0, x1, q2, q3])
    hRep e heQuad heQuadSymm heQuarticSymm M hMtM hMMt hB hp huRep hsocp

theorem residual_eq_zero_of_socp_of_eq_mix_affineEquiv_x0_x1_homQuadratics_plane_nontrivial
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
      lowHomQuadPlaneA q2 q3 ≠ 0 ∨
        lowHomQuadPlaneB q2 q3 ≠ 0 ∨ lowHomQuadPlaneC q2 q3 ≠ 0)
    (huRep :
      mix M.transpose
        (mapVec (affineEquiv A A' b b' hAA' hA'A hb hb').symm.toAlgHom u) =
          ![x0, x1, q2, q3])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec_x0_x1_homQuadratics_plane_nontrivial
    (e := affineEquiv A A' b b' hAA' hA'A hb hb')
    (heQuad := fun {_} hpq => isQuadratic_affineEquiv A A' b b' hAA' hA'A hb hb' hpq)
    (heQuadSymm := fun {_} hpq => isQuadratic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (heQuarticSymm := fun {_} hpq => isQuartic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (M := M) hMtM hMMt hB hp
    hq2 hq3 hq2_00 hq2_10 hq2_01 hq3_00 hq3_10 hq3_01 hplane huRep hsocp


/-- The rank-4 linear low-affine representative. -/
def linearAffineRep : RankFourVec := ![x0, x0 ^ 2, x0 * x1, x1 ^ 2]

private theorem monomial_image_linearAffineRep
    (s : Fin 2 →₀ ℕ) (a : ℝ)
    (hdeg : s.sum (fun _ e => e) ≤ 4)
    (hne0 : s ≠ m00) (hne1 : s ≠ m01) :
    InAdmissibleImage linearAffineRep (MvPolynomial.monomial s a) := by
  let e0 := s 0
  let e1 := s 1
  have hsum : s.sum (fun _ e => e) = s 0 + s 1 := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
  have hs0 : s 0 + s 1 ≤ 4 := by
    simpa [hsum] using hdeg
  have hs : e0 + e1 ≤ 4 := by
    simpa [e0, e1] using hs0
  by_cases hsmall : e0 + e1 ≤ 3
  · by_cases hx1 : 1 ≤ e0
    · refine ⟨![(MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1, 0, 0, 0], ?_, ?_⟩
      · intro i
        fin_cases i
        · have hs2 : (e0 - 1) + e1 ≤ 2 := by omega
          exact isQuadratic_C_mul_pow_pow a (e0 - 1) e1 hs2
        · simp [IsQuadratic]
        · simp [IsQuadratic]
        · simp [IsQuadratic]
      · rw [monomial_fin2_eq]
        simp [e0, e1]
        calc
          A linearAffineRep ![(MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1, 0, 0, 0]
              = x0 * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1) := by
                  simp [A, linearAffineRep, Fin.sum_univ_four, x0, x1]
          _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                have hxpow : x0 * x0 ^ (e0 - 1) = x0 ^ e0 := by
                  simpa [Nat.sub_add_cancel hx1] using (pow_succ' x0 (e0 - 1)).symm
                calc
                  x0 * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1)
                      = MvPolynomial.C a * (x0 * x0 ^ (e0 - 1)) * x1 ^ e1 := by
                          ring_nf
                  _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                        simp [hxpow, mul_assoc]
    · have hy2 : 2 ≤ e1 := by
        by_contra hy2
        have hx0 : e0 = 0 := by omega
        have hy0 : e1 = 0 ∨ e1 = 1 := by omega
        rcases hy0 with hy0 | hy1
        · apply hne0
          ext i
          fin_cases i <;> simp [m00, e0, e1, hx0, hy0]
        · apply hne1
          ext i
          fin_cases i <;> simp [m01, e0, e1, hx0, hy1]
      refine ⟨![0, 0, 0, (MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 2)], ?_, ?_⟩
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
          A linearAffineRep ![0, 0, 0, (MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 2)]
              = x1 ^ 2 * ((MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 2)) := by
                  simp [A, linearAffineRep, Fin.sum_univ_four, x0, x1]
          _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                calc
                  x1 ^ 2 * ((MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 2))
                      = MvPolynomial.C a * x0 ^ e0 * (x1 ^ 2 * x1 ^ (e1 - 2)) := by
                          ring_nf
                  _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                        rw [← pow_add, Nat.add_sub_of_le hy2]
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
          A linearAffineRep ![0, (MvPolynomial.C a * x0 ^ (e0 - 2)) * x1 ^ e1, 0, 0]
              = x0 ^ 2 * ((MvPolynomial.C a * x0 ^ (e0 - 2)) * x1 ^ e1) := by
                  simp [A, linearAffineRep, Fin.sum_univ_four, x0, x1]
          _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                calc
                  x0 ^ 2 * ((MvPolynomial.C a * x0 ^ (e0 - 2)) * x1 ^ e1)
                      = MvPolynomial.C a * (x0 ^ 2 * x0 ^ (e0 - 2)) * x1 ^ e1 := by
                          ring_nf
                  _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                        rw [← pow_add, Nat.add_sub_of_le hx2]
    · by_cases h0 : e0 = 0
      · have hy4 : e1 = 4 := by omega
        refine ⟨![0, 0, 0, (MvPolynomial.C a * x1 ^ 2)], ?_, ?_⟩
        · intro i
          fin_cases i
          · simp [IsQuadratic]
          · simp [IsQuadratic]
          · simp [IsQuadratic]
          · simpa [x0, x1] using isQuadratic_C_mul_pow_pow a 0 2 (by norm_num)
        · rw [monomial_fin2_eq]
          have hs0' : s 0 = 0 := by simpa [e0] using h0
          have hs1' : s 1 = 4 := by simpa [e1] using hy4
          rw [hs0', hs1']
          simp
          calc
            A linearAffineRep ![0, 0, 0, (MvPolynomial.C a * x1 ^ 2)]
                = x1 ^ 2 * (MvPolynomial.C a * x1 ^ 2) := by
                    simp [A, linearAffineRep, Fin.sum_univ_four, x0, x1]
            _ = MvPolynomial.C a * x1 ^ 4 := by
                  calc
                    x1 ^ 2 * (MvPolynomial.C a * x1 ^ 2)
                        = MvPolynomial.C a * (x1 ^ 2 * x1 ^ 2) := by
                            ring_nf
                    _ = MvPolynomial.C a * x1 ^ 4 := by
                          rw [← pow_add]
      · have hx1 : 1 ≤ e0 := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero h0)
        have hy1 : 1 ≤ e1 := by omega
        refine ⟨![0, 0, (MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1), 0], ?_, ?_⟩
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
            A linearAffineRep ![0, 0, (MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1), 0]
                = (x0 * x1) * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1)) := by
                    simp [A, linearAffineRep, Fin.sum_univ_four, x0, x1]
            _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
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

theorem quartic_in_image_of_relations_x0_x0sq_x0x1_x1sq_of_coeff_m00_m01_zero
    {u : RankFourVec}
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x0 ^ 2)
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 * x1)
    (h3 : ∑ i : Fin 4, c3 i • u i = x1 ^ 2)
    {p : Poly} (hp : IsQuartic p)
    (h00 : MvPolynomial.coeff m00 p = 0)
    (h01 : MvPolynomial.coeff m01 p = 0) :
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
        have hscoeff : MvPolynomial.coeff s p ≠ 0 :=
          MvPolynomial.mem_support_iff.mp (hsub s (by simp))
        have hsne0 : s ≠ m00 := by
          intro hs
          apply hscoeff
          simpa [hs] using h00
        have hsne1 : s ≠ m01 := by
          intro hs
          apply hscoeff
          simpa [hs] using h01
        by_cases hsmall : e0 + e1 ≤ 3
        · by_cases hx1 : 1 ≤ e0
          · have himg :=
              inAdmissibleImage_of_relation_mul_low
                (u := u) (c := c0) (r := x0)
                (q := (MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ (e0 - 1)) * x1 ^ e1)
                h0 (isQuadratic_C_mul_pow_pow (MvPolynomial.coeff s p) (e0 - 1) e1 (by omega))
            rw [monomial_fin2_eq]
            simp [e0, e1] at himg ⊢
            have hmul :
                x0 * ((MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ (e0 - 1)) * x1 ^ e1) =
                  (MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ e0) * x1 ^ e1 := by
              have hxpow : x0 * x0 ^ (e0 - 1) = x0 ^ e0 := by
                simpa [Nat.sub_add_cancel hx1] using (pow_succ' x0 (e0 - 1)).symm
              calc
                x0 * ((MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ (e0 - 1)) * x1 ^ e1)
                    = MvPolynomial.C (MvPolynomial.coeff s p) * (x0 * x0 ^ (e0 - 1)) * x1 ^ e1 := by
                        ring_nf
                _ = (MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ e0) * x1 ^ e1 := by
                      simp [hxpow, mul_assoc]
            simpa [e0, e1, hmul] using himg
          · have hy2 : 2 ≤ e1 := by
              by_contra hy2
              have hx0 : e0 = 0 := by omega
              have hy0 : e1 = 0 ∨ e1 = 1 := by omega
              rcases hy0 with hy0 | hy1
              · apply hsne0
                ext i
                fin_cases i <;> simp [m00, e0, e1, hx0, hy0]
              · apply hsne1
                ext i
                fin_cases i <;> simp [m01, e0, e1, hx0, hy1]
            have hs2 : e0 + (e1 - 2) ≤ 2 := by omega
            have himg :=
              inAdmissibleImage_of_relation_mul_low
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
        · by_cases hx2 : 2 ≤ e0
          · have hs2 : (e0 - 2) + e1 ≤ 2 := by omega
            have himg :=
              inAdmissibleImage_of_relation_mul_low
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
          · by_cases h0e : e0 = 0
            · have hy4 : e1 = 4 := by omega
              have himg :=
                inAdmissibleImage_of_relation_mul_low
                  (u := u) (c := c3) (r := x1 ^ 2)
                  (q := (MvPolynomial.C (MvPolynomial.coeff s p) * x1 ^ 2))
                  h3 (by
                    simpa [x0, x1] using
                      isQuadratic_C_mul_pow_pow (MvPolynomial.coeff s p) 0 2 (by norm_num))
              rw [monomial_fin2_eq]
              have hs0' : s 0 = 0 := by simpa [e0] using h0e
              have hs1' : s 1 = 4 := by simpa [e1] using hy4
              rw [hs0', hs1']
              simp at himg ⊢
              have hmul :
                  x1 ^ 2 * (MvPolynomial.C (MvPolynomial.coeff s p) * x1 ^ 2) =
                    MvPolynomial.C (MvPolynomial.coeff s p) * x1 ^ 4 := by
                calc
                  x1 ^ 2 * (MvPolynomial.C (MvPolynomial.coeff s p) * x1 ^ 2)
                      = MvPolynomial.C (MvPolynomial.coeff s p) * (x1 ^ 2 * x1 ^ 2) := by
                          ring_nf
                  _ = MvPolynomial.C (MvPolynomial.coeff s p) * x1 ^ 4 := by
                        rw [← pow_add]
              simpa [hmul] using himg
            · have hx1 : 1 ≤ e0 := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero h0e)
              have hy1 : 1 ≤ e1 := by omega
              have hs2 : (e0 - 1) + (e1 - 1) ≤ 2 := by omega
              have himg :=
                inAdmissibleImage_of_relation_mul_low
                  (u := u) (c := c2) (r := x0 * x1)
                  (q := (MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1))
                  h2 (isQuadratic_C_mul_pow_pow (MvPolynomial.coeff s p) (e0 - 1) (e1 - 1) hs2)
              rw [monomial_fin2_eq]
              simp [e0, e1] at himg ⊢
              have hmul :
                  (x0 * x1) * ((MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1)) =
                    (MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ e0) * x1 ^ e1 := by
                have hxpow : x0 * x0 ^ (e0 - 1) = x0 ^ e0 := by
                  simpa [Nat.sub_add_cancel hx1] using (pow_succ' x0 (e0 - 1)).symm
                have hypow : x1 * x1 ^ (e1 - 1) = x1 ^ e1 := by
                  simpa [Nat.sub_add_cancel hy1] using (pow_succ' x1 (e1 - 1)).symm
                calc
                  (x0 * x1) * ((MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1))
                      = MvPolynomial.C (MvPolynomial.coeff s p) * (x0 * x0 ^ (e0 - 1)) * (x1 * x1 ^ (e1 - 1)) := by
                          ring_nf
                  _ = (MvPolynomial.C (MvPolynomial.coeff s p) * x0 ^ e0) * x1 ^ e1 := by
                        simp [hxpow, hypow, mul_assoc]
              simpa [e0, e1, hmul] using himg
      · intro t ht
        exact hsub t (by simp [ht])
  exact hP (fun s hs => hs)

theorem quartic_in_image_linearAffineRep_of_coeff_m00_m01_zero
    {p : Poly} (hp : IsQuartic p)
    (h00 : MvPolynomial.coeff m00 p = 0)
    (h01 : MvPolynomial.coeff m01 p = 0) :
    InAdmissibleImage linearAffineRep p := by
  classical
  rw [← MvPolynomial.support_sum_monomial_coeff p]
  let P : Finset (Fin 2 →₀ ℕ) → Prop := fun S =>
    (∀ s ∈ S, s ∈ p.support) →
      InAdmissibleImage linearAffineRep
        (∑ s ∈ S, MvPolynomial.monomial s (MvPolynomial.coeff s p))
  have hP : P p.support := by
    refine Finset.induction_on p.support ?_ ?_
    · intro hsub
      simpa using inAdmissibleImage_zero linearAffineRep
    · intro s ss hsnot ih hsub
      rw [Finset.sum_insert hsnot]
      refine inAdmissibleImage_add linearAffineRep ?_ (ih ?_)
      · have hsdeg : s.sum (fun _ e => e) ≤ 4 :=
          (MvPolynomial.le_totalDegree (hsub s (by simp))).trans hp
        have hscoeff : MvPolynomial.coeff s p ≠ 0 :=
          MvPolynomial.mem_support_iff.mp (hsub s (by simp))
        have hsne0 : s ≠ m00 := by
          intro hs
          apply hscoeff
          simpa [hs] using h00
        have hsne1 : s ≠ m01 := by
          intro hs
          apply hscoeff
          simpa [hs] using h01
        exact monomial_image_linearAffineRep s (MvPolynomial.coeff s p) hsdeg hsne0 hsne1
      · intro t ht
        exact hsub t (by simp [ht])
  exact hP (fun s hs => hs)

theorem linearAffineRep_admissible : IsAdmissiblePoint linearAffineRep := by
  intro i
  fin_cases i
  · simp [linearAffineRep, x0, x1, IsQuadratic]
  · simp [linearAffineRep, x0, x1, IsQuadratic, MvPolynomial.totalDegree_X_pow]
  · simpa [linearAffineRep] using isQuadratic_x0_mul_x1
  · simp [linearAffineRep, x0, x1, IsQuadratic, MvPolynomial.totalDegree_X_pow]

private def linearAffineLine (c d : ℝ) : Poly := MvPolynomial.C c + MvPolynomial.C d * x1

/-- Kernel line for the linear low-affine representative. -/
def linearAffineKerLine (c d : ℝ) : RankFourVec := ![-(x1 * linearAffineLine c d), 0, linearAffineLine c d, 0]

private theorem totalDegree_linearAffineLine_le (c d : ℝ) :
    (linearAffineLine c d).totalDegree ≤ 1 := by
  unfold linearAffineLine
  calc
    (MvPolynomial.C c + MvPolynomial.C d * x1).totalDegree ≤
        max (MvPolynomial.C c).totalDegree ((MvPolynomial.C d * x1).totalDegree) := by
          exact MvPolynomial.totalDegree_add _ _
    _ ≤ 1 := by
          apply max_le
          · simp
          · calc
              (MvPolynomial.C d * x1).totalDegree ≤ (MvPolynomial.C d).totalDegree + x1.totalDegree := by
                exact MvPolynomial.totalDegree_mul _ _
              _ = 1 := by simp [x1]

private theorem isQuadratic_linearAffineLine (c d : ℝ) :
    IsQuadratic (linearAffineLine c d) := by
  exact (totalDegree_linearAffineLine_le c d).trans (by norm_num)

private theorem isQuadratic_x1_mul_linearAffineLine (c d : ℝ) :
    IsQuadratic (x1 * linearAffineLine c d) := by
  have hx1 : x1.totalDegree ≤ 1 := by simp [x1]
  calc
    (x1 * linearAffineLine c d).totalDegree ≤
        x1.totalDegree + (linearAffineLine c d).totalDegree := by
          exact MvPolynomial.totalDegree_mul _ _
    _ ≤ 1 + 1 := by
          exact add_le_add hx1 (totalDegree_linearAffineLine_le c d)
    _ = 2 := by norm_num

theorem linearAffineKerLine_inKer (c d : ℝ) :
    InAdmissibleKer linearAffineRep (linearAffineKerLine c d) := by
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i
    ·
      calc
        (-(x1 * linearAffineLine c d) : Poly).totalDegree = (x1 * linearAffineLine c d).totalDegree := by
          rw [MvPolynomial.totalDegree_neg]
        _ ≤ 2 := isQuadratic_x1_mul_linearAffineLine c d
    · simp [linearAffineKerLine, IsQuadratic]
    · exact isQuadratic_linearAffineLine c d
    · simp [linearAffineKerLine, IsQuadratic]
  · simp [A, linearAffineRep, linearAffineKerLine, linearAffineLine, Fin.sum_univ_four, x0, x1]
    ring

private theorem coeff_m00_linearAffineLine (c d : ℝ) :
    MvPolynomial.coeff m00 (linearAffineLine c d) = c := by
  unfold linearAffineLine
  rw [MvPolynomial.coeff_add]
  have hmul : MvPolynomial.coeff m00 (MvPolynomial.C d * x1 : Poly) = 0 := by
    rw [show x1 = MvPolynomial.monomial m01 (1 : ℝ) by
      simp [x1, m01, MvPolynomial.monomial_eq]]
    rw [MvPolynomial.coeff_mul_monomial']
    have hnot : ¬ m01 ≤ m00 := by
      intro h
      have := h 1
      simp [m00, m01] at this
    rw [if_neg hnot]
  simp [hmul, m00]

private theorem coeff_m01_linearAffineLine (c d : ℝ) :
    MvPolynomial.coeff m01 (linearAffineLine c d) = d := by
  unfold linearAffineLine
  rw [MvPolynomial.coeff_add]
  have hC : MvPolynomial.coeff m01 (MvPolynomial.C c : Poly) = 0 := by
    rw [MvPolynomial.coeff_C]
    split_ifs with h
    · exfalso
      have := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h.symm
      simp [m01] at this
    · rfl
  have hmul : MvPolynomial.coeff m01 (MvPolynomial.C d * x1 : Poly) = d := by
    rw [show x1 = MvPolynomial.monomial m01 (1 : ℝ) by
      simp [x1, m01, MvPolynomial.monomial_eq]]
    rw [MvPolynomial.coeff_mul_monomial']
    have hsub : m01 - m01 = m00 := by
      ext i
      fin_cases i <;> simp [m00, m01]
    rw [if_pos le_rfl, hsub]
    simp [m00]
  simp [hC, hmul]

private theorem coeff_m00_x1_mul_linearAffineLine_zero (c d : ℝ) :
    MvPolynomial.coeff m00 (x1 * linearAffineLine c d) = 0 := by
  rw [show x1 = MvPolynomial.monomial m01 (1 : ℝ) by
    simp [x1, m01, MvPolynomial.monomial_eq]]
  rw [MvPolynomial.coeff_monomial_mul']
  have hnot : ¬ m01 ≤ m00 := by
    intro h
    have := h 1
    simp [m00, m01] at this
  rw [if_neg hnot]

private abbrev quadSuppNo_m00_m01 : Finset (Fin 2 →₀ ℕ) := (quadSupp.erase m00).erase m01

private theorem coeff_qRest_m00_m01 (q : Poly) (d : Fin 2 →₀ ℕ) :
    MvPolynomial.coeff d
      (∑ e ∈ quadSuppNo_m00_m01, MvPolynomial.monomial e (MvPolynomial.coeff e q)) =
      if d ∈ quadSuppNo_m00_m01 then MvPolynomial.coeff d q else 0 := by
  simp [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]

private theorem quadratic_split_m00_m01 (q : Poly) (hq : IsQuadratic q) :
    q =
      (∑ e ∈ quadSuppNo_m00_m01, MvPolynomial.monomial e (MvPolynomial.coeff e q)) +
      MvPolynomial.monomial m00 (MvPolynomial.coeff m00 q) +
      MvPolynomial.monomial m01 (MvPolynomial.coeff m01 q) := by
  let f : (Fin 2 →₀ ℕ) → Poly := fun e => MvPolynomial.monomial e (MvPolynomial.coeff e q)
  calc
    q = ∑ d ∈ quadSupp, f d := quadratic_sum_formula hq
    _ = (∑ e ∈ quadSupp.erase m00, f e) + f m00 := by
          symm
          exact Finset.sum_erase_add (s := quadSupp) (a := m00) (f := f)
            (by simp [quadSupp])
    _ = ((∑ e ∈ quadSuppNo_m00_m01, f e) + f m01) + f m00 := by
          have hm01 : m01 ∈ quadSupp.erase m00 := by
            refine Finset.mem_erase.mpr ?_
            constructor
            · intro h
              have := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h
              simp [m00, m01] at this
            · simp [quadSupp]
          have hsum01 : ∑ e ∈ quadSupp.erase m00, f e =
              (∑ e ∈ quadSuppNo_m00_m01, f e) + f m01 := by
            symm
            exact Finset.sum_erase_add (s := quadSupp.erase m00) (a := m01) (f := f) hm01
          rw [hsum01]
    _ =
      (∑ e ∈ quadSuppNo_m00_m01, MvPolynomial.monomial e (MvPolynomial.coeff e q)) +
      MvPolynomial.monomial m00 (MvPolynomial.coeff m00 q) +
      MvPolynomial.monomial m01 (MvPolynomial.coeff m01 q) := by
        simp [f]
        ring

private theorem coeff_m00_qRest_zero (q : Poly) :
    MvPolynomial.coeff m00
      (∑ e ∈ quadSuppNo_m00_m01, MvPolynomial.monomial e (MvPolynomial.coeff e q)) = 0 := by
  rw [coeff_qRest_m00_m01]
  simp

private theorem coeff_m01_qRest_zero (q : Poly) :
    MvPolynomial.coeff m01
      (∑ e ∈ quadSuppNo_m00_m01, MvPolynomial.monomial e (MvPolynomial.coeff e q)) = 0 := by
  rw [coeff_qRest_m00_m01]
  simp

private theorem coord_sum_ge_one_of_mem_quadSuppNo_m00_m01 {d : Fin 2 →₀ ℕ}
    (hd : d ∈ quadSuppNo_m00_m01) :
    1 ≤ d 0 + d 1 := by
  have hd0 : d ∈ quadSupp.erase m00 := Finset.mem_of_mem_erase hd
  have hne01 : d ≠ m01 := (Finset.mem_erase.mp hd).1
  have hne00 : d ≠ m00 := (Finset.mem_erase.mp hd0).1
  have hdquad : d ∈ quadSupp := (Finset.mem_erase.mp hd0).2
  simp [quadSupp] at hdquad
  rcases hdquad with rfl | rfl | rfl | rfl | rfl | rfl
  · contradiction
  · simp [m10]
  · contradiction
  · simp [m20]
  · simp [m11]
  · simp [m02]

private theorem not_sum_m01_of_mem_quadSuppNo_m00_m01 {d1 d2 : Fin 2 →₀ ℕ}
    (hd1 : d1 ∈ quadSuppNo_m00_m01)
    (hd2 : d2 ∈ quadSuppNo_m00_m01) :
    d1 + d2 ≠ m01 := by
  intro hsum
  have hdeg1 : 1 ≤ d1 0 + d1 1 := coord_sum_ge_one_of_mem_quadSuppNo_m00_m01 hd1
  have hdeg2 : 1 ≤ d2 0 + d2 1 := coord_sum_ge_one_of_mem_quadSuppNo_m00_m01 hd2
  have h0 : d1 0 + d2 0 = 0 := by
    simpa [m01] using congrArg (fun e : Fin 2 →₀ ℕ => e 0) hsum
  have h1 : d1 1 + d2 1 = 1 := by
    simpa [m01] using congrArg (fun e : Fin 2 →₀ ℕ => e 1) hsum
  omega

private theorem coeff_m01_qRest_sq_zero (q : Poly) :
    MvPolynomial.coeff m01
      ((∑ e ∈ quadSuppNo_m00_m01, MvPolynomial.monomial e (MvPolynomial.coeff e q)) ^ 2) = 0 := by
  rw [pow_two, MvPolynomial.coeff_mul]
  refine Finset.sum_eq_zero ?_
  intro x hx
  have hxsum : x.1 + x.2 = m01 := Finset.mem_antidiagonal.mp hx
  by_cases hx1 : x.1 ∈ quadSuppNo_m00_m01
  · by_cases hx2 : x.2 ∈ quadSuppNo_m00_m01
    · exfalso
      exact not_sum_m01_of_mem_quadSuppNo_m00_m01 hx1 hx2 hxsum
    · simp [coeff_qRest_m00_m01, hx1, hx2]
  · simp [coeff_qRest_m00_m01, hx1]

private theorem coeff_m01_qRest_mul_m00_zero (q : Poly) (a : ℝ) :
    MvPolynomial.coeff m01
      ((∑ e ∈ quadSuppNo_m00_m01, MvPolynomial.monomial e (MvPolynomial.coeff e q)) *
        MvPolynomial.monomial m00 a) = 0 := by
  rw [MvPolynomial.coeff_mul_monomial']
  rw [if_pos (by intro i; simp [m00])]
  have hsub : m01 - m00 = m01 := by
    ext i
    fin_cases i <;> simp [m00, m01]
  rw [hsub]
  rw [coeff_m01_qRest_zero]
  simp

private theorem coeff_m01_qRest_mul_m01_zero (q : Poly) (b : ℝ) :
    MvPolynomial.coeff m01
      ((∑ e ∈ quadSuppNo_m00_m01, MvPolynomial.monomial e (MvPolynomial.coeff e q)) *
        MvPolynomial.monomial m01 b) = 0 := by
  rw [MvPolynomial.coeff_mul_monomial']
  rw [if_pos le_rfl]
  have hsub : m01 - m01 = m00 := by
    ext i
    fin_cases i <;> simp [m00, m01]
  rw [hsub, coeff_m00_qRest_zero]
  simp

private theorem coeff_m01_m00_mul_qRest_zero (q : Poly) (a : ℝ) :
    MvPolynomial.coeff m01
      (MvPolynomial.monomial m00 a *
        (∑ e ∈ quadSuppNo_m00_m01, MvPolynomial.monomial e (MvPolynomial.coeff e q))) = 0 := by
  rw [MvPolynomial.coeff_monomial_mul']
  rw [if_pos (by intro i; simp [m00])]
  have hsub : m01 - m00 = m01 := by
    ext i
    fin_cases i <;> simp [m00, m01]
  rw [hsub]
  rw [coeff_m01_qRest_zero]
  simp

private theorem coeff_m01_m01_mul_qRest_zero (q : Poly) (b : ℝ) :
    MvPolynomial.coeff m01
      (MvPolynomial.monomial m01 b *
        (∑ e ∈ quadSuppNo_m00_m01, MvPolynomial.monomial e (MvPolynomial.coeff e q))) = 0 := by
  rw [MvPolynomial.coeff_monomial_mul']
  rw [if_pos le_rfl]
  have hsub : m01 - m01 = m00 := by
    ext i
    fin_cases i <;> simp [m00, m01]
  rw [hsub, coeff_m00_qRest_zero]
  simp

private theorem coeff_m01_sq_of_quadratic (q : Poly) (hq : IsQuadratic q) :
    MvPolynomial.coeff m01 (q ^ 2) =
      2 * MvPolynomial.coeff m00 q * MvPolynomial.coeff m01 q := by
  let qRest := ∑ e ∈ quadSuppNo_m00_m01, MvPolynomial.monomial e (MvPolynomial.coeff e q)
  let a := MvPolynomial.coeff m00 q
  let b := MvPolynomial.coeff m01 q
  have hsplit : q = qRest + MvPolynomial.monomial m00 a + MvPolynomial.monomial m01 b := by
    dsimp [qRest, a, b]
    exact quadratic_split_m00_m01 q hq
  have h00 :
      MvPolynomial.coeff m01 (MvPolynomial.monomial m00 a * MvPolynomial.monomial m00 a) = 0 := by
    rw [MvPolynomial.coeff_monomial_mul']
    rw [if_pos (by intro i; simp [m00])]
    have hsub : m01 - m00 = m01 := by
      ext i
      fin_cases i <;> simp [m00, m01]
    rw [hsub]
    have hne : m00 ≠ m01 := by
      intro h
      have := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h
      simp [m00, m01] at this
    simp [m00, hne]
  have h01 :
      MvPolynomial.coeff m01 (MvPolynomial.monomial m00 a * MvPolynomial.monomial m01 b) = a * b := by
    rw [MvPolynomial.coeff_monomial_mul']
    rw [if_pos (by intro i; fin_cases i <;> simp [m00, m01])]
    simp [m00]
  have h10 :
      MvPolynomial.coeff m01 (MvPolynomial.monomial m01 b * MvPolynomial.monomial m00 a) = b * a := by
    rw [MvPolynomial.coeff_monomial_mul']
    rw [if_pos le_rfl]
    have hsub : m01 - m01 = m00 := by
      ext i
      fin_cases i <;> simp [m00, m01]
    rw [hsub]
    simp [m00]
  have h11 :
      MvPolynomial.coeff m01 (MvPolynomial.monomial m01 b * MvPolynomial.monomial m01 b) = 0 := by
    rw [MvPolynomial.coeff_monomial_mul']
    rw [if_pos le_rfl]
    have hsub : m01 - m01 = m00 := by
      ext i
      fin_cases i <;> simp [m00, m01]
    rw [hsub]
    have hne : m01 ≠ m00 := by
      intro h
      have := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h
      simp [m00, m01] at this
    simp [hne, m00]
  have hqRestC :
      MvPolynomial.coeff m01 (qRest * MvPolynomial.C a) = 0 := by
    simpa [m00] using coeff_m01_qRest_mul_m00_zero q a
  have hCqRest :
      MvPolynomial.coeff m01 (MvPolynomial.C a * qRest) = 0 := by
    simpa [m00] using coeff_m01_m00_mul_qRest_zero q a
  have hCC :
      MvPolynomial.coeff m01 (MvPolynomial.C a * MvPolynomial.C a) = 0 := by
    exact h00
  have hC01 :
      MvPolynomial.coeff m01 (MvPolynomial.C a * MvPolynomial.monomial m01 b) = a * b := by
    exact h01
  have h01C :
      MvPolynomial.coeff m01 (MvPolynomial.monomial m01 b * MvPolynomial.C a) = b * a := by
    exact h10
  have hqRestSq :
      MvPolynomial.coeff m01 (qRest * qRest) = 0 := by
    simpa [qRest, pow_two] using coeff_m01_qRest_sq_zero q
  have hqRest01 :
      MvPolynomial.coeff m01 (qRest * MvPolynomial.monomial m01 b) = 0 := by
    simpa [qRest, b] using coeff_m01_qRest_mul_m01_zero q b
  have h01qRest :
      MvPolynomial.coeff m01 (MvPolynomial.monomial m01 b * qRest) = 0 := by
    simpa [qRest, b] using coeff_m01_m01_mul_qRest_zero q b
  calc
    MvPolynomial.coeff m01 (q ^ 2)
        = MvPolynomial.coeff m01
            ((qRest + MvPolynomial.monomial m00 a + MvPolynomial.monomial m01 b) ^
              2) := by rw [hsplit]
    _ =
      MvPolynomial.coeff m01
          (qRest * qRest + qRest * MvPolynomial.monomial m00 a +
            qRest * MvPolynomial.monomial m01 b +
            MvPolynomial.monomial m00 a * qRest +
            MvPolynomial.monomial m00 a * MvPolynomial.monomial m00 a +
            MvPolynomial.monomial m00 a * MvPolynomial.monomial m01 b +
            MvPolynomial.monomial m01 b * qRest +
            MvPolynomial.monomial m01 b * MvPolynomial.monomial m00 a +
            MvPolynomial.monomial m01 b * MvPolynomial.monomial m01 b) := by
          ring_nf
    _ = 0 + 0 + 0 + 0 + 0 + a * b + 0 + b * a + 0 := by
          have hne : (0 : Fin 2 →₀ ℕ) ≠ m01 := by
            intro h
            have := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h
            simp [m01] at this
          simp [MvPolynomial.coeff_add, hqRestSq, hqRestC, hqRest01,
            hCqRest, hCC, hC01, h01qRest, h01C, qRest, a, b]
    _ = 2 * MvPolynomial.coeff m00 q * MvPolynomial.coeff m01 q := by
          dsimp [a, b]
          ring

theorem coeff_m01_sq_of_quadratic_eq (q : Poly) (hq : IsQuadratic q) :
    MvPolynomial.coeff m01 (q ^ 2) =
      2 * MvPolynomial.coeff m00 q * MvPolynomial.coeff m01 q :=
  coeff_m01_sq_of_quadratic q hq

private theorem coeff_m01_x1_mul_linearAffineLine (c d : ℝ) :
    MvPolynomial.coeff m01 (x1 * linearAffineLine c d) = c := by
  have hrewrite :
      x1 * linearAffineLine c d = MvPolynomial.C c * x1 + MvPolynomial.C d * x1 ^ 2 := by
    unfold linearAffineLine
    ring
  rw [hrewrite, MvPolynomial.coeff_add]
  have hcx1 : MvPolynomial.coeff m01 (MvPolynomial.C c * x1 : Poly) = c := by
    rw [show x1 = MvPolynomial.monomial m01 (1 : ℝ) by
      simp [x1, m01, MvPolynomial.monomial_eq]]
    rw [MvPolynomial.coeff_mul_monomial']
    have hsub : m01 - m01 = m00 := by
      ext i
      fin_cases i <;> simp [m00, m01]
    rw [if_pos le_rfl, hsub]
    simp [m00]
  have hdx1 : MvPolynomial.coeff m01 (MvPolynomial.C d * x1 ^ 2 : Poly) = 0 := by
    rw [show (x1 ^ 2 : Poly) = MvPolynomial.monomial m02 (1 : ℝ) by
      simp [x1, m02, MvPolynomial.monomial_eq]]
    rw [MvPolynomial.coeff_mul_monomial']
    have hnot : ¬ m02 ≤ m01 := by
      intro h
      have := h 1
      simp [m01, m02] at this
    rw [if_neg hnot]
  simp [hcx1, hdx1]

private def relationLinearAffineKerLine
    (c0 c2 : Fin 4 → ℝ) (c d : ℝ) : RankFourVec :=
  relationDirection (-c0) (x1 * linearAffineLine c d) +
    relationDirection c2 (linearAffineLine c d)

private theorem relationLinearAffineKerLine_admissible
    (c0 c2 : Fin 4 → ℝ) (c d : ℝ) :
    IsAdmissibleDirection (relationLinearAffineKerLine c0 c2 c d) := by
  refine isAdmissibleDirection_add
    (relationDirection_admissible (-c0) (isQuadratic_x1_mul_linearAffineLine c d))
    (relationDirection_admissible c2 (isQuadratic_linearAffineLine c d))

private theorem relationLinearAffineKerLine_inKer
    {u : RankFourVec} {c0 c2 : Fin 4 → ℝ} {c d : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 * x1) :
    InAdmissibleKer u (relationLinearAffineKerLine c0 c2 c d) := by
  refine ⟨relationLinearAffineKerLine_admissible c0 c2 c d, ?_⟩
  rw [relationLinearAffineKerLine, A_add_right_local, A_relationDirection, A_relationDirection]
  simp [Pi.neg_apply, h0, h2]
  ring_nf

private theorem coeff_m00_relationLinearAffineKerLine
    (c0 c2 : Fin 4 → ℝ) (c d : ℝ) :
    MvPolynomial.coeff m00 (sigma (relationLinearAffineKerLine c0 c2 c d)) =
      (∑ i : Fin 4, (c2 i) ^ 2) * c ^ 2 := by
  have hcoord0 : ∀ i : Fin 4,
      MvPolynomial.coeff m00 (relationLinearAffineKerLine c0 c2 c d i) = c2 i * c := by
    intro i
    rw [relationLinearAffineKerLine, Pi.add_apply, relationDirection, relationDirection,
      Pi.neg_apply, MvPolynomial.coeff_add, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul,
      coeff_m00_x1_mul_linearAffineLine_zero, coeff_m00_linearAffineLine]
    simp [smul_eq_mul]
  have hcoord : ∀ i : Fin 4,
      MvPolynomial.coeff m00 ((relationLinearAffineKerLine c0 c2 c d i) ^ 2) =
        (c2 i * c) ^ 2 := by
    intro i
    rw [coeff_m00_sq, hcoord0]
  rw [sigma, Fin.sum_univ_four]
  repeat' rw [MvPolynomial.coeff_add]
  rw [hcoord 0, hcoord 1, hcoord 2, hcoord 3]
  simp [Fin.sum_univ_four]
  ring

private theorem coeff_m01_relationLinearAffineKerLine
    (c0 c2 : Fin 4 → ℝ) (c d : ℝ) :
    MvPolynomial.coeff m01 (sigma (relationLinearAffineKerLine c0 c2 c d)) =
      2 * c * ((d * ∑ i : Fin 4, (c2 i) ^ 2) - c * ∑ i : Fin 4, c0 i * c2 i) := by
  have hcoord0 : ∀ i : Fin 4,
      MvPolynomial.coeff m00 (relationLinearAffineKerLine c0 c2 c d i) = c2 i * c := by
    intro i
    rw [relationLinearAffineKerLine, Pi.add_apply, relationDirection, relationDirection,
      Pi.neg_apply, MvPolynomial.coeff_add, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul,
      coeff_m00_x1_mul_linearAffineLine_zero, coeff_m00_linearAffineLine]
    simp [smul_eq_mul]
  have hcoord1 : ∀ i : Fin 4,
      MvPolynomial.coeff m01 (relationLinearAffineKerLine c0 c2 c d i) = c2 i * d - c0 i * c := by
    intro i
    rw [relationLinearAffineKerLine, Pi.add_apply, relationDirection, relationDirection,
      Pi.neg_apply, MvPolynomial.coeff_add, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul,
      coeff_m01_x1_mul_linearAffineLine, coeff_m01_linearAffineLine]
    simp [smul_eq_mul, sub_eq_add_neg, add_comm, mul_comm]
  have hcoord : ∀ i : Fin 4,
      MvPolynomial.coeff m01 ((relationLinearAffineKerLine c0 c2 c d i) ^ 2) =
        2 * (c2 i * c) * (c2 i * d - c0 i * c) := by
    intro i
    rw [coeff_m01_sq_of_quadratic_eq _ ((relationLinearAffineKerLine_admissible c0 c2 c d) i),
      hcoord0, hcoord1]
  rw [sigma, Fin.sum_univ_four]
  repeat' rw [MvPolynomial.coeff_add]
  rw [hcoord 0, hcoord 1, hcoord 2, hcoord 3]
  simp [Fin.sum_univ_four]
  ring

theorem coeff_m00_sigma_linearAffineKerLine (c d : ℝ) :
    MvPolynomial.coeff m00 (sigma (linearAffineKerLine c d)) = c ^ 2 := by
  have hx :
      MvPolynomial.coeff m00 ((x1 * linearAffineLine c d) ^ 2) = 0 := by
    rw [coeff_m00_sq]
    rw [coeff_m00_x1_mul_linearAffineLine_zero]
    simp
  have hline :
      MvPolynomial.coeff m00 ((linearAffineLine c d) ^ 2) = c ^ 2 := by
    rw [coeff_m00_sq, coeff_m00_linearAffineLine]
  rw [sigma, Fin.sum_univ_four]
  simp [linearAffineKerLine, hx, hline]

theorem coeff_m01_sigma_linearAffineKerLine (c d : ℝ) :
    MvPolynomial.coeff m01 (sigma (linearAffineKerLine c d)) = 2 * c * d := by
  have hx :
      MvPolynomial.coeff m01 ((x1 * linearAffineLine c d) ^ 2) = 0 := by
    rw [coeff_m01_sq_of_quadratic_eq _ (isQuadratic_x1_mul_linearAffineLine c d)]
    rw [coeff_m00_x1_mul_linearAffineLine_zero]
    ring
  have hline :
      MvPolynomial.coeff m01 ((linearAffineLine c d) ^ 2) = 2 * c * d := by
    rw [coeff_m01_sq_of_quadratic_eq _ (isQuadratic_linearAffineLine c d)]
    rw [coeff_m00_linearAffineLine, coeff_m01_linearAffineLine]
  rw [sigma, Fin.sum_univ_four]
  simp [linearAffineKerLine, hx, hline]

theorem residual_eq_zero_linearAffineRep
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p linearAffineRep) :
    residual p linearAffineRep = 0 := by
  rcases hp with ⟨hpquartic, k, qs, hqdeg, hpq⟩
  let s0 : ℝ := ∑ i : Fin k, (MvPolynomial.coeff m00 (qs i)) ^ 2
  let s1 : ℝ := ∑ i : Fin k, MvPolynomial.coeff m00 (qs i) * MvPolynomial.coeff m01 (qs i)
  let c : ℝ := Real.sqrt s0
  let d : ℝ := s1 / c
  let w : RankFourVec := linearAffineKerLine c d
  have hs0_nonneg : 0 ≤ s0 := by
    dsimp [s0]
    positivity
  have hp00 : MvPolynomial.coeff m00 p = s0 := by
    rw [hpq, MvPolynomial.coeff_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact coeff_m00_sq (qs i)
  have hp01 : MvPolynomial.coeff m01 p = 2 * s1 := by
    calc
      MvPolynomial.coeff m01 p = ∑ i : Fin k, MvPolynomial.coeff m01 ((qs i) ^ 2) := by
        rw [hpq, MvPolynomial.coeff_sum]
      _ = ∑ i : Fin k, 2 * MvPolynomial.coeff m00 (qs i) * MvPolynomial.coeff m01 (qs i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact coeff_m01_sq_of_quadratic_eq (qs i) (hqdeg i)
      _ = 2 * s1 := by
        dsimp [s1]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i hi
        ring
  have hc_sq : c ^ 2 = s0 := by
    dsimp [c]
    rw [Real.sq_sqrt hs0_nonneg]
  have hs1_zero_of_c_zero (hc0 : c = 0) : s1 = 0 := by
    have hs0_zero : s0 = 0 := by
      simpa [hc0] using hc_sq.symm
    have htermzero :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => sq_nonneg (MvPolynomial.coeff m00 (qs i)))).mp hs0_zero
    dsimp [s1]
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hi0 : MvPolynomial.coeff m00 (qs i) = 0 := by
      exact sq_eq_zero_iff.mp (htermzero i (by simp))
    simp [hi0]
  have hwker : InAdmissibleKer linearAffineRep w := by
    dsimp [w]
    exact linearAffineKerLine_inKer c d
  have hw00 : MvPolynomial.coeff m00 (sigma w) = s0 := by
    change MvPolynomial.coeff m00 (sigma (linearAffineKerLine c d)) = s0
    rw [coeff_m00_sigma_linearAffineKerLine, hc_sq]
  have hw01 : MvPolynomial.coeff m01 (sigma w) = 2 * s1 := by
    change MvPolynomial.coeff m01 (sigma (linearAffineKerLine c d)) = 2 * s1
    rw [coeff_m01_sigma_linearAffineKerLine]
    by_cases hc0 : c = 0
    · have hs1zero : s1 = 0 := hs1_zero_of_c_zero hc0
      simp [d, hc0, hs1zero]
    · dsimp [d]
      field_simp [hc0]
  have hquartic_sub : IsQuartic (p - sigma w) := by
    calc
      (p - sigma w).totalDegree ≤ max p.totalDegree (sigma w).totalDegree := by
        exact MvPolynomial.totalDegree_sub _ _
      _ ≤ 4 := by
        exact max_le hpquartic (isQuartic_sigma_of_admissible hwker.1)
  have h00_sub : MvPolynomial.coeff m00 (p - sigma w) = 0 := by
    rw [MvPolynomial.coeff_sub, hp00, hw00]
    ring
  have h01_sub : MvPolynomial.coeff m01 (p - sigma w) = 0 := by
    rw [MvPolynomial.coeff_sub, hp01, hw01]
    ring
  have himg : InAdmissibleImage linearAffineRep (p - sigma w) :=
    quartic_in_image_linearAffineRep_of_coeff_m00_m01_zero hquartic_sub h00_sub h01_sub
  refine admissible_image_plus_cone_residual_eq_zero (B := B)
    (u := linearAffineRep) (uImg := linearAffineRep)
    linearAffineRep_admissible hsocp
    (imageOrthogonalResidual_self (B := B) hsocp.1) ?_
  refine ⟨p - sigma w, {w}, himg, ?_, ?_⟩
  · intro w' hw'
    have hw' : w' = w := by simpa using hw'
    subst hw'
    exact hwker
  · simp [w, sub_eq_add_neg]

theorem residual_eq_zero_of_relations_x0_x0sq_x0x1_x1sq
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x0 ^ 2)
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 * x1)
    (h3 : ∑ i : Fin 4, c3 i • u i = x1 ^ 2)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  rcases hp with ⟨hpquartic, k, qs, hqdeg, hpq⟩
  let s0 : ℝ := ∑ i : Fin k, (MvPolynomial.coeff m00 (qs i)) ^ 2
  let s1 : ℝ := ∑ i : Fin k, MvPolynomial.coeff m00 (qs i) * MvPolynomial.coeff m01 (qs i)
  let alpha : ℝ := ∑ i : Fin 4, (c2 i) ^ 2
  let beta : ℝ := ∑ i : Fin 4, c0 i * c2 i
  let c : ℝ := Real.sqrt (s0 / alpha)
  let d : ℝ := if hc : c = 0 then 0 else s1 / (c * alpha) + c * beta / alpha
  let w : RankFourVec := relationLinearAffineKerLine c0 c2 c d
  have hs0_nonneg : 0 ≤ s0 := by
    dsimp [s0]
    positivity
  have hc2_ne : c2 ≠ 0 := by
    intro hc2
    have : (0 : Poly) = x0 * x1 := by
      simpa [hc2] using h2
    have hcoeff := congrArg (MvPolynomial.coeff m11) this
    simp [coeff_m11_x0_mul_x1] at hcoeff
  have halpha_pos : 0 < alpha := sum_sq_pos_of_ne_zero c2 hc2_ne
  have halpha_nonneg : 0 ≤ alpha := le_of_lt halpha_pos
  have hsdiv_nonneg : 0 ≤ s0 / alpha := by
    exact div_nonneg hs0_nonneg halpha_nonneg
  have hp00 : MvPolynomial.coeff m00 p = s0 := by
    rw [hpq, MvPolynomial.coeff_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact coeff_m00_sq (qs i)
  have hp01 : MvPolynomial.coeff m01 p = 2 * s1 := by
    calc
      MvPolynomial.coeff m01 p = ∑ i : Fin k, MvPolynomial.coeff m01 ((qs i) ^ 2) := by
        rw [hpq, MvPolynomial.coeff_sum]
      _ = ∑ i : Fin k, 2 * MvPolynomial.coeff m00 (qs i) * MvPolynomial.coeff m01 (qs i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact coeff_m01_sq_of_quadratic_eq (qs i) (hqdeg i)
      _ = 2 * s1 := by
          dsimp [s1]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
  have hc_sq : c ^ 2 = s0 / alpha := by
    dsimp [c]
    rw [Real.sq_sqrt hsdiv_nonneg]
  have hs1_zero_of_c_zero (hc0 : c = 0) : s1 = 0 := by
    have hs0_zero : s0 = 0 := by
      have : s0 / alpha = 0 := by simpa [hc0] using hc_sq.symm
      by_contra hs0_ne
      have hs0_pos : 0 < s0 := lt_of_le_of_ne hs0_nonneg (Ne.symm hs0_ne)
      have hsdiv_pos : 0 < s0 / alpha := div_pos hs0_pos halpha_pos
      linarith
    have htermzero :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => sq_nonneg (MvPolynomial.coeff m00 (qs i)))).mp hs0_zero
    dsimp [s1]
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hi0 : MvPolynomial.coeff m00 (qs i) = 0 := by
      exact sq_eq_zero_iff.mp (htermzero i (by simp))
    simp [hi0]
  have hwker : InAdmissibleKer u w := by
    dsimp [w]
    exact relationLinearAffineKerLine_inKer h0 h2
  have hw00 : MvPolynomial.coeff m00 (sigma w) = s0 := by
    change MvPolynomial.coeff m00 (sigma (relationLinearAffineKerLine c0 c2 c d)) = s0
    calc
      MvPolynomial.coeff m00 (sigma (relationLinearAffineKerLine c0 c2 c d)) = alpha * c ^ 2 := by
        exact coeff_m00_relationLinearAffineKerLine c0 c2 c d
      _ = alpha * (s0 / alpha) := by rw [hc_sq]
      _ = s0 := by
            field_simp [alpha, halpha_pos.ne']
  have hw01 : MvPolynomial.coeff m01 (sigma w) = 2 * s1 := by
    change MvPolynomial.coeff m01 (sigma (relationLinearAffineKerLine c0 c2 c d)) = 2 * s1
    rw [coeff_m01_relationLinearAffineKerLine]
    by_cases hc0 : c = 0
    · have hs1zero : s1 = 0 := hs1_zero_of_c_zero hc0
      simp [d, hc0, hs1zero]
    · have halpha_ne : alpha ≠ 0 := halpha_pos.ne'
      simp [d, hc0]
      field_simp [hc0, halpha_ne]
      ring
  have hquartic_sub : IsQuartic (p - sigma w) := by
    calc
      (p - sigma w).totalDegree ≤ max p.totalDegree (sigma w).totalDegree := by
        exact MvPolynomial.totalDegree_sub _ _
      _ ≤ 4 := by
        exact max_le hpquartic (isQuartic_sigma_of_admissible hwker.1)
  have h00_sub : MvPolynomial.coeff m00 (p - sigma w) = 0 := by
    rw [MvPolynomial.coeff_sub, hp00, hw00]
    ring
  have h01_sub : MvPolynomial.coeff m01 (p - sigma w) = 0 := by
    rw [MvPolynomial.coeff_sub, hp01, hw01]
    ring
  have himg : InAdmissibleImage u (p - sigma w) :=
    quartic_in_image_of_relations_x0_x0sq_x0x1_x1sq_of_coeff_m00_m01_zero
      h0 h1 h2 h3 hquartic_sub h00_sub h01_sub
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

theorem residual_eq_zero_of_relations_x0_homQuadBasis_det
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
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
  exact residual_eq_zero_of_relations_x0_x0sq_x0x1_x1sq
    (B := B) (u := u) hu h0 (hd 0) (hd 1) (hd 2) hp hsocp

theorem residual_eq_zero_of_equiv_relations_x0_x0sq_x0x1_x1sq
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
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x0 ^ 2)
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = x0 * x1)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = x1 ^ 2) :
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
    exact residual_eq_zero_of_relations_x0_x0sq_x0x1_x1sq
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0 h1 h2 h3 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_equiv_relations_x0_homQuadBasis_det
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0)
    {c : Fin 3 → Fin 4 → ℝ} {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hc :
      ∀ j : Fin 3,
        ∑ i : Fin 4, c j i • mapVec e.toAlgHom u i = ∑ k : Fin 3, A j k • homQuadBasis k)
    (hdet : A.det ≠ 0) :
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
    exact residual_eq_zero_of_relations_x0_homQuadBasis_det
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0 hc hdet hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_linearForm_homQuadBasis_det
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 : Fin 4 → ℝ} {a b : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = linearForm a b)
    (hs : a ^ 2 + b ^ 2 ≠ 0)
    {c : Fin 3 → Fin 4 → ℝ} {q : Fin 3 → Poly} {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hc : ∀ j : Fin 3, ∑ i : Fin 4, c j i • u i = q j)
    (hq :
      ∀ j : Fin 3,
        affineLineEquiv 0 a b hs (q j) = ∑ k : Fin 3, A j k • homQuadBasis k)
    (hdet : A.det ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let e : Poly ≃ₐ[ℝ] Poly := affineLineEquiv 0 a b hs
  have heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q) := by
    intro q hq'
    exact isQuadratic_affineEquiv
      (affineLineMatrix a b) (affineLineInvMatrix a b)
      (affineLineVec 0 a b) (affineLineInvVec 0)
      (affineLine_mul_inv a b hs) (affineLine_inv_mul a b hs)
      (affineLineInv_add_mulVec 0 a b hs) (affineLine_add_mulVec_inv 0 a b hs) hq'
  have heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q) := by
    intro q hq'
    exact isQuadratic_affineEquiv_symm
      (affineLineMatrix a b) (affineLineInvMatrix a b)
      (affineLineVec 0 a b) (affineLineInvVec 0)
      (affineLine_mul_inv a b hs) (affineLine_inv_mul a b hs)
      (affineLineInv_add_mulVec 0 a b hs) (affineLine_add_mulVec_inv 0 a b hs) hq'
  have heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q) := by
    intro q hq'
    exact isQuartic_affineEquiv
      (affineLineMatrix a b) (affineLineInvMatrix a b)
      (affineLineVec 0 a b) (affineLineInvVec 0)
      (affineLine_mul_inv a b hs) (affineLine_inv_mul a b hs)
      (affineLineInv_add_mulVec 0 a b hs) (affineLine_add_mulVec_inv 0 a b hs) hq'
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  have h0' : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0 := by
    simpa [e, affineLineEquiv, linearForm] using
      (relation_map e.toAlgHom h0).trans (affineHom_affineLinePoly 0 a b hs)
  have hc' :
      ∀ j : Fin 3,
        ∑ i : Fin 4, c j i • mapVec e.toAlgHom u i = ∑ k : Fin 3, A j k • homQuadBasis k := by
    intro j
    simpa [e] using (relation_map e.toAlgHom (hc j)).trans (hq j)
  exact residual_eq_zero_of_equiv_relations_x0_homQuadBasis_det
    (e := e) (heQuad := fun {_} hq' => heQuad hq') (heQuadSymm := fun {_} hq' => heQuadSymm hq')
    (heQuartic := fun {_} hq' => heQuartic hq')
    hB hp hu hsocp h0' hc' hdet

theorem residual_eq_zero_of_socp_of_eq_mix_mapVec_linearForm_homQuadBasis_det
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
    {a b : ℝ}
    (hs : a ^ 2 + b ^ 2 ≠ 0)
    {q1 q2 q3 : Poly}
    (hq1 : IsQuadratic q1)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    {C : Matrix (Fin 3) (Fin 3) ℝ}
    (hq1_basis : affineLineEquiv 0 a b hs q1 = ∑ k : Fin 3, C 0 k • homQuadBasis k)
    (hq2_basis : affineLineEquiv 0 a b hs q2 = ∑ k : Fin 3, C 1 k • homQuadBasis k)
    (hq3_basis : affineLineEquiv 0 a b hs q3 = ∑ k : Fin 3, C 2 k • homQuadBasis k)
    (hdet : C.det ≠ 0)
    (huRep : mix M.transpose (mapVec e.symm.toAlgHom u) = ![linearForm a b, q1, q2, q3])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have huRepAdmissible : IsAdmissiblePoint (![linearForm a b, q1, q2, q3] : RankFourVec) := by
    intro i
    fin_cases i
    · have hx0a : IsQuadratic ((a : ℝ) • x0 : Poly) := by
          exact (MvPolynomial.totalDegree_smul_le a x0).trans (by simp [x0])
      have hx1b : IsQuadratic ((b : ℝ) • x1 : Poly) := by
          exact (MvPolynomial.totalDegree_smul_le b x1).trans (by simp [x1])
      simpa [linearForm, affineLinePoly, MvPolynomial.smul_eq_C_mul, add_assoc] using
        (isQuadratic_linearCombination_local hx0a hx1b 1 1)
    · simpa using hq1
    · simpa using hq2
    · simpa using hq3
  have hRep :
      ∀ {B0 : DotForm} [Fact B0.toQuadraticMap.PosDef] {p0 : Poly},
        IsSOSQuartic p0 → IsSOCP B0 p0 (![linearForm a b, q1, q2, q3] : RankFourVec) →
          residual p0 (![linearForm a b, q1, q2, q3] : RankFourVec) = 0 := by
    intro B0 _ p0 hp0 hsocp0
    exact residual_eq_zero_of_relations_linearForm_homQuadBasis_det
      (c0 := ![1, 0, 0, 0])
      (c := fun j =>
        match j with
        | 0 => ![0, 1, 0, 0]
        | 1 => ![0, 0, 1, 0]
        | 2 => ![0, 0, 0, 1])
      (q := ![q1, q2, q3])
      (B := B0) (u := ![linearForm a b, q1, q2, q3]) huRepAdmissible
      (h0 := by simp [Fin.sum_univ_four, linearForm])
      (hs := hs)
      (hc := by
        intro j
        fin_cases j <;> simp [Fin.sum_univ_four])
      (hq := by
        intro j
        fin_cases j
        · simpa [Fin.sum_univ_four] using hq1_basis
        · simpa [Fin.sum_univ_four] using hq2_basis
        · simpa [Fin.sum_univ_four] using hq3_basis)
      hdet hp0 hsocp0
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec
    (![linearForm a b, q1, q2, q3])
    hRep e heQuad heQuadSymm heQuarticSymm M hMtM hMMt hB hp huRep hsocp

theorem residual_eq_zero_of_socp_of_eq_mix_affineEquiv_linearForm_homQuadBasis_det
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
    {a c : ℝ}
    (hs : a ^ 2 + c ^ 2 ≠ 0)
    {q1 q2 q3 : Poly}
    (hq1 : IsQuadratic q1)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    {C : Matrix (Fin 3) (Fin 3) ℝ}
    (hq1_basis : affineLineEquiv 0 a c hs q1 = ∑ k : Fin 3, C 0 k • homQuadBasis k)
    (hq2_basis : affineLineEquiv 0 a c hs q2 = ∑ k : Fin 3, C 1 k • homQuadBasis k)
    (hq3_basis : affineLineEquiv 0 a c hs q3 = ∑ k : Fin 3, C 2 k • homQuadBasis k)
    (hdet : C.det ≠ 0)
    (huRep :
      mix M.transpose
        (mapVec (affineEquiv A A' b b' hAA' hA'A hb hb').symm.toAlgHom u) =
          ![linearForm a c, q1, q2, q3])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec_linearForm_homQuadBasis_det
    (e := affineEquiv A A' b b' hAA' hA'A hb hb')
    (heQuad := fun {_} hpq => isQuadratic_affineEquiv A A' b b' hAA' hA'A hb hb' hpq)
    (heQuadSymm := fun {_} hpq => isQuadratic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (heQuarticSymm := fun {_} hpq => isQuartic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (M := M) hMtM hMMt hB hp hs hq1 hq2 hq3
    hq1_basis hq2_basis hq3_basis hdet huRep hsocp

theorem residual_eq_zero_of_socp_of_eq_mix_mapVec_x0_homQuadBasis_det
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
    {q1 q2 q3 : Poly}
    (hq1 : IsQuadratic q1)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hq1_basis : q1 = ∑ k : Fin 3, A 0 k • homQuadBasis k)
    (hq2_basis : q2 = ∑ k : Fin 3, A 1 k • homQuadBasis k)
    (hq3_basis : q3 = ∑ k : Fin 3, A 2 k • homQuadBasis k)
    (hdet : A.det ≠ 0)
    (huRep : mix M.transpose (mapVec e.symm.toAlgHom u) = ![x0, q1, q2, q3])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have huRepAdmissible : IsAdmissiblePoint (![x0, q1, q2, q3] : RankFourVec) := by
    intro i
    fin_cases i
    · simpa [x0] using (show IsQuadratic (MvPolynomial.X 0 : Poly) by simp [IsQuadratic])
    · simpa using hq1
    · simpa using hq2
    · simpa using hq3
  have hRep :
      ∀ {B0 : DotForm} [Fact B0.toQuadraticMap.PosDef] {p0 : Poly},
        IsSOSQuartic p0 → IsSOCP B0 p0 (![x0, q1, q2, q3] : RankFourVec) →
          residual p0 (![x0, q1, q2, q3] : RankFourVec) = 0 := by
    intro B0 _ p0 hp0 hsocp0
    exact residual_eq_zero_of_relations_x0_homQuadBasis_det
      (c0 := ![1, 0, 0, 0])
      (c := fun j =>
        match j with
        | 0 => ![0, 1, 0, 0]
        | 1 => ![0, 0, 1, 0]
        | 2 => ![0, 0, 0, 1])
      (B := B0) (u := ![x0, q1, q2, q3]) huRepAdmissible
      (h0 := by simp [Fin.sum_univ_four, x0])
      (hc := by
        intro j
        fin_cases j <;> simp [Fin.sum_univ_four, hq1_basis, hq2_basis, hq3_basis])
      hdet hp0 hsocp0
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec
    (![x0, q1, q2, q3])
    hRep e heQuad heQuadSymm heQuarticSymm M hMtM hMMt hB hp huRep hsocp

theorem residual_eq_zero_of_socp_of_eq_mix_affineEquiv_x0_homQuadBasis_det
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
    {q1 q2 q3 : Poly}
    (hq1 : IsQuadratic q1)
    (hq2 : IsQuadratic q2)
    (hq3 : IsQuadratic q3)
    {C : Matrix (Fin 3) (Fin 3) ℝ}
    (hq1_basis : q1 = ∑ k : Fin 3, C 0 k • homQuadBasis k)
    (hq2_basis : q2 = ∑ k : Fin 3, C 1 k • homQuadBasis k)
    (hq3_basis : q3 = ∑ k : Fin 3, C 2 k • homQuadBasis k)
    (hdet : C.det ≠ 0)
    (huRep :
      mix M.transpose
        (mapVec (affineEquiv A A' b b' hAA' hA'A hb hb').symm.toAlgHom u) =
          ![x0, q1, q2, q3])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec_x0_homQuadBasis_det
    (e := affineEquiv A A' b b' hAA' hA'A hb hb')
    (heQuad := fun {_} hpq => isQuadratic_affineEquiv A A' b b' hAA' hA'A hb hb' hpq)
    (heQuadSymm := fun {_} hpq => isQuadratic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (heQuarticSymm := fun {_} hpq => isQuartic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (M := M) hMtM hMMt hB hp hq1 hq2 hq3
    hq1_basis hq2_basis hq3_basis hdet huRep hsocp

end TernaryQuartic
