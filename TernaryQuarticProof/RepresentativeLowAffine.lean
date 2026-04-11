import TernaryQuarticProof.QuadraticNormalForm
import TernaryQuarticProof.AffineSocpTransform
import TernaryQuarticProof.MixedAffineNormalization
import TernaryQuarticProof.RepresentativeTransport
import TernaryQuarticProof.RepresentativeMixedAffine
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
    simpa [m00] using h00
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
