import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finsupp.Fin
import TernaryQuarticProof.AffineSocpTransform

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
  rw [A_relationDirection, hc]

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

theorem quartic_in_image_constQuadRep {p : Poly} (hp : IsQuartic p) :
    InAdmissibleImage constQuadRep p := by
  classical
  rw [← MvPolynomial.support_sum_monomial_coeff p]
  let P : Finset (Fin 2 →₀ ℕ) → Prop := fun S =>
    (∀ s ∈ S, s ∈ p.support) →
      InAdmissibleImage constQuadRep (∑ s ∈ S, MvPolynomial.monomial s (MvPolynomial.coeff s p))
  have hP : P p.support := by
    refine Finset.induction_on p.support ?base ?step
    · intro hsub
      simpa using inAdmissibleImage_zero constQuadRep
    · intro s ss hsnot ih hsub
      rw [Finset.sum_insert hsnot]
      refine inAdmissibleImage_add constQuadRep ?_ (ih ?_)
      · have hsdeg : s.sum (fun _ e => e) ≤ 4 :=
          (MvPolynomial.le_totalDegree (hsub s (by simp))).trans hp
        exact monomial_image_constQuadRep s (MvPolynomial.coeff s p) hsdeg
      · intro t ht
        exact hsub t (by simp [ht])
  exact hP (fun s hs => hs)

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

theorem residual_eq_zero_constQuadRep
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p constQuadRep) :
    residual p constQuadRep = 0 := by
  refine residual_eq_zero_of_in_admissible_image (B := B)
    (u := constQuadRep) ?_ hsocp ?_
  · intro i
    fin_cases i
    · simp [constQuadRep, x0, x1, IsQuadratic]
    · simp [constQuadRep, x0, x1, IsQuadratic, MvPolynomial.totalDegree_X_pow]
    ·
      calc
        (x0 * x1).totalDegree ≤ x0.totalDegree + x1.totalDegree := by
          exact MvPolynomial.totalDegree_mul _ _
        _ = 2 := by simp [x0, x1]
    · simp [constQuadRep, x0, x1, IsQuadratic, MvPolynomial.totalDegree_X_pow]
  · exact quartic_in_image_constQuadRep hp.1

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

theorem residual_eq_zero_of_equiv_relations_const_homQuadBasis_det
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
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = (1 : Poly))
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
    exact residual_eq_zero_of_relations_const_homQuadBasis_det
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0 hc hdet hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

end TernaryQuartic
