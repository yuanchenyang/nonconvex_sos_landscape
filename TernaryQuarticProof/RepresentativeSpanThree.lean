import TernaryQuarticProof.QuadraticNormalForm
import TernaryQuarticProof.RepresentativeTransport
import TernaryQuarticProof.RepresentativeSurjective

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace TernaryQuartic

open scoped BigOperators

/-- The generic `dim(W ∩ Aff₁)=3` representative. -/
def spanThreeRep (h : Poly) : RankFourVec := ![(1 : Poly), x0, x1, h]

theorem spanThreeRep_admissible {h : Poly} (hh : IsQuadratic h) :
    IsAdmissiblePoint (spanThreeRep h) := by
  intro i
  fin_cases i
  · simp [spanThreeRep, IsQuadratic]
  · simp [spanThreeRep, x0, IsQuadratic]
  · simp [spanThreeRep, x1, IsQuadratic]
  · simpa [spanThreeRep] using hh

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

private theorem monomial_m00_eq_C (a : ℝ) :
    MvPolynomial.monomial m00 a = MvPolynomial.C a := by
  simp [m00]

private theorem monomial_m10_eq (a : ℝ) :
    MvPolynomial.monomial m10 a = MvPolynomial.C a * x0 := by
  simp [m10, x0, MvPolynomial.monomial_eq]

private theorem monomial_m01_eq (a : ℝ) :
    MvPolynomial.monomial m01 a = MvPolynomial.C a * x1 := by
  simp [m01, x1, MvPolynomial.monomial_eq]

private theorem monomial_m20_eq (a : ℝ) :
    MvPolynomial.monomial m20 a = MvPolynomial.C a * x0 ^ 2 := by
  simp [m20, x0, MvPolynomial.monomial_eq]

private theorem monomial_m11_eq (a : ℝ) :
    MvPolynomial.monomial m11 a = MvPolynomial.C a * (x0 * x1) := by
  simp [m11, x0, x1, MvPolynomial.monomial_eq]

private theorem monomial_m02_eq (a : ℝ) :
    MvPolynomial.monomial m02 a = MvPolynomial.C a * x1 ^ 2 := by
  simp [m02, x1, MvPolynomial.monomial_eq]

private theorem m10_ne_m00 : m10 ≠ m00 := by
  intro h
  have := congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
  simp [m10, m00] at this

private theorem m01_ne_m00 : m01 ≠ m00 := by
  intro h
  have := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h
  simp [m01, m00] at this

private theorem m20_ne_m00 : m20 ≠ m00 := by
  intro h
  have := congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
  simp [m20, m00] at this

private theorem m20_ne_m10 : m20 ≠ m10 := by
  intro h
  have := congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
  simp [m20, m10] at this

private theorem m20_ne_m01 : m20 ≠ m01 := by
  intro h
  have := congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
  simp [m20, m01] at this

private theorem m11_ne_m00 : m11 ≠ m00 := by
  intro h
  have := congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
  simp [m11, m00] at this

private theorem m11_ne_m10 : m11 ≠ m10 := by
  intro h
  have := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h
  simp [m11, m10] at this

private theorem m11_ne_m01 : m11 ≠ m01 := by
  intro h
  have := congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
  simp [m11, m01] at this

private theorem m20_ne_m11 : m20 ≠ m11 := by
  intro h
  have := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h
  simp [m20, m11] at this

private theorem m02_ne_m00 : m02 ≠ m00 := by
  intro h
  have := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h
  simp [m02, m00] at this

private theorem m02_ne_m10 : m02 ≠ m10 := by
  intro h
  have := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h
  simp [m02, m10] at this

private theorem m02_ne_m01 : m02 ≠ m01 := by
  intro h
  have := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h
  simp [m02, m01] at this

private theorem m20_ne_m02 : m20 ≠ m02 := by
  intro h
  have := congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
  simp [m20, m02] at this

private theorem m11_ne_m02 : m11 ≠ m02 := by
  intro h
  have := congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
  simp [m11, m02] at this

private theorem m11_ne_m20 : m11 ≠ m20 := m20_ne_m11.symm

private theorem m02_ne_m20 : m02 ≠ m20 := m20_ne_m02.symm

private theorem m02_ne_m11 : m02 ≠ m11 := m11_ne_m02.symm

private theorem monomial_image_spanThreeRep
    {h : Poly} (s : Fin 2 →₀ ℕ) (a : ℝ)
    (hdeg : s.sum (fun _ e => e) ≤ 3) :
    InAdmissibleImage (spanThreeRep h) (MvPolynomial.monomial s a) := by
  let e0 := s 0
  let e1 := s 1
  have hsum : s.sum (fun _ e => e) = s 0 + s 1 := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
  have hs0 : s 0 + s 1 ≤ 3 := by
    simpa [hsum] using hdeg
  have hs : e0 + e1 ≤ 3 := by
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
      simp [e0, e1]
      calc
        A (spanThreeRep h) ![(MvPolynomial.C a * x0 ^ e0) * x1 ^ e1, 0, 0, 0]
            = ((1 : Poly)) * ((MvPolynomial.C a * x0 ^ e0) * x1 ^ e1) := by
                simp [A, spanThreeRep, Fin.sum_univ_four, x0, x1]
        _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by simp
  · by_cases hx1 : 1 ≤ e0
    · refine ⟨![0, (MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1, 0, 0], ?_, ?_⟩
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
          A (spanThreeRep h) ![0, (MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1, 0, 0]
              = x0 * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1) := by
                  simp [A, spanThreeRep, Fin.sum_univ_four, x0, x1]
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
        omega
      refine ⟨![0, 0, (MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 1), 0], ?_, ?_⟩
      · intro i
        fin_cases i
        · simp [IsQuadratic]
        · simp [IsQuadratic]
        · have hs2 : e0 + (e1 - 1) ≤ 2 := by omega
          exact isQuadratic_C_mul_pow_pow a e0 (e1 - 1) hs2
        · simp [IsQuadratic]
      · rw [monomial_fin2_eq]
        simp [e0, e1]
        calc
          A (spanThreeRep h) ![0, 0, (MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 1), 0]
              = x1 * ((MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 1)) := by
                  simp [A, spanThreeRep, Fin.sum_univ_four, x0, x1]
          _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                have hypow : x1 * x1 ^ (e1 - 1) = x1 ^ e1 := by
                  simpa [Nat.sub_add_cancel hy1] using (pow_succ' x1 (e1 - 1)).symm
                calc
                  x1 * ((MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 1))
                      = MvPolynomial.C a * x0 ^ e0 * (x1 * x1 ^ (e1 - 1)) := by
                          ring_nf
                  _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
                        simp [hypow, mul_assoc]

theorem cubic_in_image_spanThreeRep
    {h p : Poly} (hp : p.totalDegree ≤ 3) :
    InAdmissibleImage (spanThreeRep h) p := by
  classical
  rw [← MvPolynomial.support_sum_monomial_coeff p]
  let P : Finset (Fin 2 →₀ ℕ) → Prop := fun S =>
    (∀ s ∈ S, s ∈ p.support) →
      InAdmissibleImage (spanThreeRep h)
        (∑ s ∈ S, MvPolynomial.monomial s (MvPolynomial.coeff s p))
  have hP : P p.support := by
    refine Finset.induction_on p.support ?_ ?_
    · intro hsub
      simpa using inAdmissibleImage_zero (spanThreeRep h)
    · intro s ss hsnot ih hsub
      rw [Finset.sum_insert hsnot]
      refine inAdmissibleImage_add (spanThreeRep h) ?_ (ih ?_)
      · have hsdeg : s.sum (fun _ e => e) ≤ 3 :=
          (MvPolynomial.le_totalDegree (hsub s (by simp))).trans hp
        exact monomial_image_spanThreeRep s (MvPolynomial.coeff s p) hsdeg
      · intro t ht
        exact hsub t (by simp [ht])
  exact hP (fun s hs => hs)

private def lowPart (q : Poly) : Poly :=
  MvPolynomial.C (MvPolynomial.coeff m00 q) +
    MvPolynomial.C (MvPolynomial.coeff m10 q) * x0 +
    MvPolynomial.C (MvPolynomial.coeff m01 q) * x1

private def homPart (q : Poly) : Poly :=
  MvPolynomial.C (MvPolynomial.coeff m20 q) * x0 ^ 2 +
    MvPolynomial.C (MvPolynomial.coeff m11 q) * (x0 * x1) +
    MvPolynomial.C (MvPolynomial.coeff m02 q) * x1 ^ 2

private def homPartA (q : Poly) : Poly :=
  MvPolynomial.C (MvPolynomial.coeff m20 q) * x0 +
    MvPolynomial.C (MvPolynomial.coeff m11 q) * x1

private def homPartB (q : Poly) : Poly :=
  MvPolynomial.C (MvPolynomial.coeff m02 q) * x1

private theorem quadratic_split_low_hom {q : Poly} (hq : IsQuadratic q) :
    q = lowPart q + homPart q := by
  let f : (Fin 2 →₀ ℕ) → Poly := fun e => MvPolynomial.monomial e (MvPolynomial.coeff e q)
  calc
    q = ∑ d ∈ quadSupp, f d := quadratic_sum_formula hq
    _ = (∑ e ∈ quadSupp.erase m00, f e) + f m00 := by
          symm
          exact Finset.sum_erase_add (s := quadSupp) (a := m00) (f := f) (by simp [quadSupp])
    _ = ((∑ e ∈ (quadSupp.erase m00).erase m10, f e) + f m10) + f m00 := by
          have hm10 : m10 ∈ quadSupp.erase m00 := by
            refine Finset.mem_erase.mpr ?_
            constructor
            · intro h
              have := congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
              simp [m00, m10] at this
            · simp [quadSupp]
          have hsum10 : ∑ e ∈ quadSupp.erase m00, f e =
              (∑ e ∈ (quadSupp.erase m00).erase m10, f e) + f m10 := by
            symm
            exact Finset.sum_erase_add (s := quadSupp.erase m00) (a := m10) (f := f) hm10
          rw [hsum10]
    _ = (((∑ e ∈ ((quadSupp.erase m00).erase m10).erase m01, f e) + f m01) + f m10) + f m00 := by
          have hm01 : m01 ∈ (quadSupp.erase m00).erase m10 := by
            refine Finset.mem_erase.mpr ?_
            constructor
            · intro h
              have := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h
              simp [m01, m10] at this
            · refine Finset.mem_erase.mpr ?_
              constructor
              · intro h
                have := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h
                simp [m00, m01] at this
              · simp [quadSupp]
          have hsum01 : ∑ e ∈ (quadSupp.erase m00).erase m10, f e =
              (∑ e ∈ ((quadSupp.erase m00).erase m10).erase m01, f e) + f m01 := by
            symm
            exact Finset.sum_erase_add (s := (quadSupp.erase m00).erase m10) (a := m01) (f := f)
              hm01
          rw [hsum01]
    _ = (((f m20 + f m11 + f m02) + f m01) + f m10) + f m00 := by
          have hset : (((quadSupp.erase m00).erase m10).erase m01) =
              ({m20, m11, m02} : Finset (Fin 2 →₀ ℕ)) := by
            ext d
            constructor
            · intro hd
              have hd0 : d ∈ (quadSupp.erase m00).erase m10 := Finset.mem_of_mem_erase hd
              have hdQ : d ∈ quadSupp := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hd0)
              have hne01 : d ≠ m01 := (Finset.mem_erase.mp hd).1
              have hne10 : d ≠ m10 := (Finset.mem_erase.mp hd0).1
              have hne00 : d ≠ m00 := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hd0)).1
              simp [quadSupp] at hdQ
              rcases hdQ with rfl | rfl | rfl | rfl | rfl | rfl
              · contradiction
              · contradiction
              · contradiction
              · simp
              · simp
              · simp
            · intro hd
              simp at hd
              rcases hd with rfl | rfl | rfl
              · refine Finset.mem_erase.mpr ?_
                constructor
                · exact m20_ne_m01
                · refine Finset.mem_erase.mpr ?_
                  constructor
                  · exact m20_ne_m10
                  · refine Finset.mem_erase.mpr ?_
                    constructor
                    · exact m20_ne_m00
                    · simp [quadSupp]
              · refine Finset.mem_erase.mpr ?_
                constructor
                · exact m11_ne_m01
                · refine Finset.mem_erase.mpr ?_
                  constructor
                  · exact m11_ne_m10
                  · refine Finset.mem_erase.mpr ?_
                    constructor
                    · exact m11_ne_m00
                    · simp [quadSupp]
              · refine Finset.mem_erase.mpr ?_
                constructor
                · exact m02_ne_m01
                · refine Finset.mem_erase.mpr ?_
                  constructor
                  · exact m02_ne_m10
                  · refine Finset.mem_erase.mpr ?_
                    constructor
                    · exact m02_ne_m00
                    · simp [quadSupp]
          have hsum3 :
              ∑ e ∈ ({m20, m11, m02} : Finset (Fin 2 →₀ ℕ)), f e = f m20 + (f m02 + f m11) := by
            have hErase20 :
                ({m20, m11, m02} : Finset (Fin 2 →₀ ℕ)).erase m20 = ({m11, m02} : Finset _) := by
              simp [m20_ne_m11, m20_ne_m02]
            have hErase11 :
                ({m11, m02} : Finset (Fin 2 →₀ ℕ)).erase m11 = ({m02} : Finset _) := by
              simp [m11_ne_m02]
            calc
              ∑ e ∈ ({m20, m11, m02} : Finset (Fin 2 →₀ ℕ)), f e
                  = (∑ e ∈ ({m20, m11, m02} : Finset (Fin 2 →₀ ℕ)).erase m20, f e) + f m20 := by
                      symm
                      exact Finset.sum_erase_add
                        (s := ({m20, m11, m02} : Finset (Fin 2 →₀ ℕ))) (a := m20) (f := f)
                        (by simp)
              _ = (∑ e ∈ ({m11, m02} : Finset (Fin 2 →₀ ℕ)), f e) + f m20 := by
                    rw [hErase20]
              _ = ((∑ e ∈ ({m11, m02} : Finset (Fin 2 →₀ ℕ)).erase m11, f e) + f m11) + f m20 := by
                    congr 1
                    symm
                    exact Finset.sum_erase_add
                      (s := ({m11, m02} : Finset (Fin 2 →₀ ℕ))) (a := m11) (f := f)
                      (by simp [m11_ne_m02])
              _ = ((∑ e ∈ ({m02} : Finset (Fin 2 →₀ ℕ)), f e) + f m11) + f m20 := by
                    rw [hErase11]
              _ = f m20 + (f m02 + f m11) := by
                    simp [f]
                    ac_rfl
          rw [hset]
          rw [hsum3]
          ac_rfl
    _ = lowPart q + homPart q := by
          simp [f, lowPart, homPart, monomial_m00_eq_C, monomial_m10_eq, monomial_m01_eq,
            monomial_m20_eq, monomial_m11_eq, monomial_m02_eq]
          ring

private theorem lowPart_totalDegree_le_one (q : Poly) :
    (lowPart q).totalDegree ≤ 1 := by
  let a : Poly := MvPolynomial.C (MvPolynomial.coeff m00 q)
  let b : Poly := MvPolynomial.C (MvPolynomial.coeff m10 q) * x0
  let c : Poly := MvPolynomial.C (MvPolynomial.coeff m01 q) * x1
  have ha : a.totalDegree ≤ 1 := by
    simp [a]
  have hb : b.totalDegree ≤ 1 := by
    calc
      b.totalDegree ≤ (MvPolynomial.C (MvPolynomial.coeff m10 q) : Poly).totalDegree + x0.totalDegree := by
            exact MvPolynomial.totalDegree_mul _ _
      _ = 1 := by simp [x0]
  have hc : c.totalDegree ≤ 1 := by
    calc
      c.totalDegree ≤ (MvPolynomial.C (MvPolynomial.coeff m01 q) : Poly).totalDegree + x1.totalDegree := by
            exact MvPolynomial.totalDegree_mul _ _
      _ = 1 := by simp [x1]
  have hab : (a + b).totalDegree ≤ 1 := by
    calc
      (a + b).totalDegree ≤ max a.totalDegree b.totalDegree := by
        exact MvPolynomial.totalDegree_add _ _
      _ ≤ 1 := max_le ha hb
  change ((a + b) + c).totalDegree ≤ 1
  calc
    ((a + b) + c).totalDegree ≤ max (a + b).totalDegree c.totalDegree := by
      exact MvPolynomial.totalDegree_add _ _
    _ ≤ 1 := by
      exact max_le hab hc

private theorem homPart_totalDegree_le_two (q : Poly) :
    (homPart q).totalDegree ≤ 2 := by
  let a : Poly := MvPolynomial.C (MvPolynomial.coeff m20 q) * x0 ^ 2
  let b : Poly := MvPolynomial.C (MvPolynomial.coeff m11 q) * (x0 * x1)
  let c : Poly := MvPolynomial.C (MvPolynomial.coeff m02 q) * x1 ^ 2
  have ha : a.totalDegree ≤ 2 := by
    calc
      a.totalDegree ≤ (MvPolynomial.C (MvPolynomial.coeff m20 q) : Poly).totalDegree + (x0 ^ 2).totalDegree := by
            exact MvPolynomial.totalDegree_mul _ _
      _ = 2 := by simp [x0]
  have hxy : (x0 * x1 : Poly).totalDegree ≤ 2 := by
    calc
      (x0 * x1 : Poly).totalDegree ≤ x0.totalDegree + x1.totalDegree := by
        exact MvPolynomial.totalDegree_mul _ _
      _ = 2 := by simp [x0, x1]
  have hb : b.totalDegree ≤ 2 := by
    calc
      b.totalDegree ≤ (MvPolynomial.C (MvPolynomial.coeff m11 q) : Poly).totalDegree + (x0 * x1).totalDegree := by
            exact MvPolynomial.totalDegree_mul _ _
      _ ≤ 2 := by simpa using hxy
  have hc : c.totalDegree ≤ 2 := by
    calc
      c.totalDegree ≤ (MvPolynomial.C (MvPolynomial.coeff m02 q) : Poly).totalDegree + (x1 ^ 2).totalDegree := by
            exact MvPolynomial.totalDegree_mul _ _
      _ = 2 := by simp [x1]
  have hab : (a + b).totalDegree ≤ 2 := by
    calc
      (a + b).totalDegree ≤ max a.totalDegree b.totalDegree := by
        exact MvPolynomial.totalDegree_add _ _
      _ ≤ 2 := max_le ha hb
  change ((a + b) + c).totalDegree ≤ 2
  calc
    ((a + b) + c).totalDegree ≤ max (a + b).totalDegree c.totalDegree := by
      exact MvPolynomial.totalDegree_add _ _
    _ ≤ 2 := by
      exact max_le hab hc

private theorem homPartA_totalDegree_le_one (q : Poly) :
    (homPartA q).totalDegree ≤ 1 := by
  let a : Poly := MvPolynomial.C (MvPolynomial.coeff m20 q) * x0
  let b : Poly := MvPolynomial.C (MvPolynomial.coeff m11 q) * x1
  have ha : a.totalDegree ≤ 1 := by
    calc
      a.totalDegree ≤ (MvPolynomial.C (MvPolynomial.coeff m20 q) : Poly).totalDegree + x0.totalDegree := by
            exact MvPolynomial.totalDegree_mul _ _
      _ = 1 := by simp [x0]
  have hb : b.totalDegree ≤ 1 := by
    calc
      b.totalDegree ≤ (MvPolynomial.C (MvPolynomial.coeff m11 q) : Poly).totalDegree + x1.totalDegree := by
            exact MvPolynomial.totalDegree_mul _ _
      _ = 1 := by simp [x1]
  change (a + b).totalDegree ≤ 1
  calc
    (a + b).totalDegree ≤ max a.totalDegree b.totalDegree := by
      exact MvPolynomial.totalDegree_add _ _
    _ ≤ 1 := by
      exact max_le ha hb

private theorem homPartB_totalDegree_le_one (q : Poly) :
    (homPartB q).totalDegree ≤ 1 := by
  unfold homPartB
  calc
    (MvPolynomial.C (MvPolynomial.coeff m02 q) * x1).totalDegree
        ≤ (MvPolynomial.C (MvPolynomial.coeff m02 q)).totalDegree + x1.totalDegree := by
          exact MvPolynomial.totalDegree_mul _ _
    _ = 1 := by simp [x1]

private theorem homPart_eq_x0_mul_A_add_x1_mul_B (q : Poly) :
    homPart q = x0 * homPartA q + x1 * homPartB q := by
  unfold homPart homPartA homPartB
  ring_nf

/-- The kernel direction attached to the homogeneous quadratic part of `q`. -/
def spanThreeKer (q : Poly) : RankFourVec :=
  ![-homPart q, homPartA q, homPartB q, 0]

theorem spanThreeKer_inKer {h q : Poly} :
    InAdmissibleKer (spanThreeRep h) (spanThreeKer q) := by
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i
    ·
      calc
        (-(homPart q) : Poly).totalDegree = (homPart q).totalDegree := by
          rw [MvPolynomial.totalDegree_neg]
        _ ≤ 2 := homPart_totalDegree_le_two q
    · exact (homPartA_totalDegree_le_one q).trans (by norm_num)
    · exact (homPartB_totalDegree_le_one q).trans (by norm_num)
    · simp [spanThreeKer, IsQuadratic]
  · simp [A, spanThreeRep, spanThreeKer, Fin.sum_univ_four, x0, x1]
    rw [homPart_eq_x0_mul_A_add_x1_mul_B]
    rw [x0, x1]
    rw [mul_comm (MvPolynomial.X 0) (homPartA q), mul_comm (MvPolynomial.X 1) (homPartB q)]
    ring_nf

private theorem sigma_spanThreeKer (q : Poly) :
    sigma (spanThreeKer q) = (homPart q) ^ 2 + (homPartA q) ^ 2 + (homPartB q) ^ 2 := by
  simp [sigma, spanThreeKer, Fin.sum_univ_four, pow_two]

private theorem square_sub_sigma_spanThreeKer_eq {q : Poly} (hq : IsQuadratic q) :
    q ^ 2 - sigma (spanThreeKer q) =
      (((lowPart q) ^ 2 + lowPart q * homPart q) + homPart q * lowPart q) +
        (-((homPartA q) ^ 2)) + (-((homPartB q) ^ 2)) := by
  nth_rewrite 1 [quadratic_split_low_hom hq]
  rw [sigma_spanThreeKer]
  ring

private theorem spanThreeKerRemainder_totalDegree_le_three {q : Poly} (hq : IsQuadratic q) :
    (q ^ 2 - sigma (spanThreeKer q)).totalDegree ≤ 3 := by
  have hlow : (lowPart q).totalDegree ≤ 1 := lowPart_totalDegree_le_one q
  have hhom : (homPart q).totalDegree ≤ 2 := homPart_totalDegree_le_two q
  have hA : (homPartA q).totalDegree ≤ 1 := homPartA_totalDegree_le_one q
  have hB : (homPartB q).totalDegree ≤ 1 := homPartB_totalDegree_le_one q
  have ha : ((lowPart q) ^ 2).totalDegree ≤ 3 := by
    calc
      ((lowPart q) ^ 2).totalDegree ≤ 2 * (lowPart q).totalDegree := by
        simpa using MvPolynomial.totalDegree_pow (lowPart q) 2
      _ ≤ 2 := by omega
      _ ≤ 3 := by omega
  have hb : (lowPart q * homPart q).totalDegree ≤ 3 := by
    calc
      (lowPart q * homPart q).totalDegree ≤ (lowPart q).totalDegree + (homPart q).totalDegree := by
        exact MvPolynomial.totalDegree_mul _ _
      _ ≤ 3 := by omega
  have hc : (homPart q * lowPart q).totalDegree ≤ 3 := by
    calc
      (homPart q * lowPart q).totalDegree ≤ (homPart q).totalDegree + (lowPart q).totalDegree := by
        exact MvPolynomial.totalDegree_mul _ _
      _ ≤ 3 := by omega
  have hA2 : ((homPartA q) ^ 2).totalDegree ≤ 2 := by
    calc
      ((homPartA q) ^ 2).totalDegree ≤ 2 * (homPartA q).totalDegree := by
        simpa using MvPolynomial.totalDegree_pow (homPartA q) 2
      _ ≤ 2 := by omega
  have hB2 : ((homPartB q) ^ 2).totalDegree ≤ 2 := by
    calc
      ((homPartB q) ^ 2).totalDegree ≤ 2 * (homPartB q).totalDegree := by
        simpa using MvPolynomial.totalDegree_pow (homPartB q) 2
      _ ≤ 2 := by omega
  have hd : (-((homPartA q) ^ 2) : Poly).totalDegree ≤ 3 := by
    calc
      (-((homPartA q) ^ 2) : Poly).totalDegree = ((homPartA q) ^ 2).totalDegree := by
        rw [MvPolynomial.totalDegree_neg]
      _ ≤ 2 := hA2
      _ ≤ 3 := by omega
  have he : (-((homPartB q) ^ 2) : Poly).totalDegree ≤ 3 := by
    calc
      (-((homPartB q) ^ 2) : Poly).totalDegree = ((homPartB q) ^ 2).totalDegree := by
        rw [MvPolynomial.totalDegree_neg]
      _ ≤ 2 := hB2
      _ ≤ 3 := by omega
  let a : Poly := (lowPart q) ^ 2
  let b : Poly := lowPart q * homPart q
  let c : Poly := homPart q * lowPart q
  let d : Poly := -((homPartA q) ^ 2)
  let e : Poly := -((homPartB q) ^ 2)
  have hab : (a + b).totalDegree ≤ 3 := by
    calc
      (a + b).totalDegree ≤ max a.totalDegree b.totalDegree := by
        exact MvPolynomial.totalDegree_add _ _
      _ ≤ 3 := max_le (by simpa [a] using ha) (by simpa [b] using hb)
  have habc : ((a + b) + c).totalDegree ≤ 3 := by
    calc
      ((a + b) + c).totalDegree ≤ max (a + b).totalDegree c.totalDegree := by
        exact MvPolynomial.totalDegree_add _ _
      _ ≤ 3 := max_le hab (by simpa [c] using hc)
  have habcd : (((a + b) + c) + d).totalDegree ≤ 3 := by
    calc
      (((a + b) + c) + d).totalDegree ≤ max ((a + b) + c).totalDegree d.totalDegree := by
        exact MvPolynomial.totalDegree_add _ _
      _ ≤ 3 := max_le habc (by simpa [d] using hd)
  rw [square_sub_sigma_spanThreeKer_eq hq]
  change ((((a + b) + c) + d) + e).totalDegree ≤ 3
  calc
    ((((a + b) + c) + d) + e).totalDegree ≤ max (((a + b) + c) + d).totalDegree e.totalDegree := by
      exact MvPolynomial.totalDegree_add _ _
    _ ≤ 3 := max_le habcd (by simpa [e] using he)

private theorem cubic_remainder_in_image_spanThreeRep {h q : Poly} (hq : IsQuadratic q) :
    InAdmissibleImage (spanThreeRep h) (q ^ 2 - sigma (spanThreeKer q)) := by
  exact cubic_in_image_spanThreeRep (h := h) (spanThreeKerRemainder_totalDegree_le_three hq)

theorem residual_eq_zero_spanThreeRep
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {h p : Poly}
    (hh : IsQuadratic h)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p (spanThreeRep h)) :
    residual p (spanThreeRep h) = 0 := by
  have hu : IsAdmissiblePoint (spanThreeRep h) := spanThreeRep_admissible hh
  rcases hp with ⟨_, k, qs, hqdeg, hpq⟩
  let imgPart : Poly := ∑ i : Fin k, ((qs i) ^ 2 - sigma (spanThreeKer (qs i)))
  let w : Fin k → RankFourVec := fun i => spanThreeKer (qs i)
  have himgDeg : imgPart.totalDegree ≤ 3 := by
    unfold imgPart
    refine MvPolynomial.totalDegree_finsetSum_le ?_
    intro i hi
    exact spanThreeKerRemainder_totalDegree_le_three (hqdeg i)
  have himgPart : InAdmissibleImage (spanThreeRep h) imgPart := by
    exact cubic_in_image_spanThreeRep (h := h) himgDeg
  have hker : ∀ i ∈ (Finset.univ : Finset (Fin k)), InAdmissibleKer (spanThreeRep h) (w i) := by
    intro i hi
    exact spanThreeKer_inKer
  have hdecomp : p = imgPart + Finset.sum (Finset.univ : Finset (Fin k)) (fun i => sigma (w i)) := by
    calc
      p = ∑ i : Fin k, (qs i) ^ 2 := hpq
      _ = ∑ i : Fin k, (((qs i) ^ 2 - sigma (spanThreeKer (qs i))) + sigma (spanThreeKer (qs i))) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
      _ = imgPart + Finset.sum (Finset.univ : Finset (Fin k)) (fun i => sigma (w i)) := by
            simp [imgPart, w]
  exact admissible_image_plus_indexed_sigma_family_residual_eq_zero
    (B := B) (u := spanThreeRep h) (uImg := spanThreeRep h) hu hsocp
    (imageOrthogonalResidual_self (B := B) hsocp.1)
    himgPart hker hdecomp

private theorem monomial_image_of_contains_aff1
    {u : RankFourVec} {c0 c1 c2 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    (h2 : ∑ i : Fin 4, c2 i • u i = x1)
    (s : Fin 2 →₀ ℕ) (a : ℝ)
    (hdeg : s.sum (fun _ e => e) ≤ 3) :
    InAdmissibleImage u (MvPolynomial.monomial s a) := by
  let e0 := s 0
  let e1 := s 1
  have hsum : s.sum (fun _ e => e) = s 0 + s 1 := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
  have hs : e0 + e1 ≤ 3 := by
    simpa [e0, e1, hsum] using hdeg
  by_cases hsmall : e0 + e1 ≤ 2
  · refine ⟨relationDirection c0 ((MvPolynomial.C a * x0 ^ e0) * x1 ^ e1),
      relationDirection_admissible c0 (isQuadratic_C_mul_pow_pow a e0 e1 hsmall), ?_⟩
    rw [A_relationDirection, h0, monomial_fin2_eq]
    simp [e0, e1]
  · by_cases hx1 : 1 ≤ e0
    · refine ⟨relationDirection c1 ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1),
        relationDirection_admissible c1
          (isQuadratic_C_mul_pow_pow a (e0 - 1) e1 (by omega)), ?_⟩
      rw [A_relationDirection, h1, monomial_fin2_eq]
      simp [e0, e1]
      calc
        x0 * ((MvPolynomial.C a * x0 ^ (e0 - 1)) * x1 ^ e1)
            = MvPolynomial.C a * (x0 * x0 ^ (e0 - 1)) * x1 ^ e1 := by
                ring_nf
        _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
              have hxpow : x0 * x0 ^ (e0 - 1) = x0 ^ e0 := by
                simpa [Nat.sub_add_cancel hx1] using (pow_succ' x0 (e0 - 1)).symm
              simp [hxpow, mul_assoc]
    · have hy1 : 1 ≤ e1 := by omega
      refine ⟨relationDirection c2 ((MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 1)),
        relationDirection_admissible c2
          (isQuadratic_C_mul_pow_pow a e0 (e1 - 1) (by omega)), ?_⟩
      rw [A_relationDirection, h2, monomial_fin2_eq]
      simp [e0, e1]
      calc
        x1 * ((MvPolynomial.C a * x0 ^ e0) * x1 ^ (e1 - 1))
            = MvPolynomial.C a * x0 ^ e0 * (x1 * x1 ^ (e1 - 1)) := by
                ring_nf
        _ = (MvPolynomial.C a * x0 ^ e0) * x1 ^ e1 := by
              have hypow : x1 * x1 ^ (e1 - 1) = x1 ^ e1 := by
                simpa [Nat.sub_add_cancel hy1] using (pow_succ' x1 (e1 - 1)).symm
              simp [hypow, mul_assoc]

private theorem cubic_in_image_of_contains_aff1
    {u : RankFourVec} {c0 c1 c2 : Fin 4 → ℝ} {p : Poly}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    (h2 : ∑ i : Fin 4, c2 i • u i = x1)
    (hp : p.totalDegree ≤ 3) :
    InAdmissibleImage u p := by
  classical
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
      · exact monomial_image_of_contains_aff1 h0 h1 h2 s (MvPolynomial.coeff s p)
          ((MvPolynomial.le_totalDegree (hsub s (by simp))).trans hp)
      · intro t ht
        exact hsub t (by simp [ht])
  exact hP (fun s hs => hs)

private theorem A_add_right_local (u v w : RankFourVec) :
    A u (v + w) = A u v + A u w := by
  simp [A, Finset.sum_add_distrib, mul_add]

private theorem sigma_smul_local (t : ℝ) (v : RankFourVec) :
    sigma (t • v) = (t ^ 2) • sigma v := by
  simp [sigma, Fin.sum_univ_four, pow_two, smul_smul]

private def spanThreeAff1KerRaw
    (c0 c1 c2 : Fin 4 → ℝ) (q : Poly) : RankFourVec :=
  relationDirection (-c0) (homPart q) +
    (relationDirection c1 (homPartA q) + relationDirection c2 (homPartB q))

private def spanThreeAff1KerScale (c0 : Fin 4 → ℝ) : ℝ :=
  (Real.sqrt (∑ i : Fin 4, (c0 i) ^ 2))⁻¹

private def spanThreeAff1Ker
    (c0 c1 c2 : Fin 4 → ℝ) (q : Poly) : RankFourVec :=
  spanThreeAff1KerScale c0 • spanThreeAff1KerRaw c0 c1 c2 q

private theorem spanThreeAff1KerRaw_admissible
    (c0 c1 c2 : Fin 4 → ℝ) (q : Poly) :
    IsAdmissibleDirection (spanThreeAff1KerRaw c0 c1 c2 q) := by
  refine isAdmissibleDirection_add
    (relationDirection_admissible (-c0) (homPart_totalDegree_le_two q)) ?_
  exact isAdmissibleDirection_add
    (relationDirection_admissible c1 ((homPartA_totalDegree_le_one q).trans (by norm_num)))
    (relationDirection_admissible c2 ((homPartB_totalDegree_le_one q).trans (by norm_num)))

private theorem spanThreeAff1KerRaw_inKer
    {u : RankFourVec} {c0 c1 c2 : Fin 4 → ℝ} {q : Poly}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    (h2 : ∑ i : Fin 4, c2 i • u i = x1) :
    InAdmissibleKer u (spanThreeAff1KerRaw c0 c1 c2 q) := by
  refine ⟨spanThreeAff1KerRaw_admissible c0 c1 c2 q, ?_⟩
  rw [spanThreeAff1KerRaw, A_add_right_local, A_add_right_local,
    A_relationDirection, A_relationDirection, A_relationDirection]
  simp [Pi.neg_apply, h0, h1, h2, homPart_eq_x0_mul_A_add_x1_mul_B]

private theorem spanThreeAff1Ker_component_remainder_totalDegree_le_three
    (c0 c1 c2 : Fin 4 → ℝ) (q : Poly) (i : Fin 4) :
    (((spanThreeAff1KerRaw c0 c1 c2 q i) ^ 2) - ((c0 i) ^ 2) • ((homPart q) ^ 2)).totalDegree ≤ 3 := by
  let a : Poly := (-(c0 i)) • homPart q
  let b : Poly := (c1 i) • homPartA q + (c2 i) • homPartB q
  have ha : a.totalDegree ≤ 2 := by
    dsimp [a]
    exact (MvPolynomial.totalDegree_smul_le (-(c0 i)) (homPart q)).trans (homPart_totalDegree_le_two q)
  have hb1 : (((c1 i) : ℝ) • homPartA q : Poly).totalDegree ≤ 1 := by
    exact (MvPolynomial.totalDegree_smul_le (c1 i) (homPartA q)).trans (homPartA_totalDegree_le_one q)
  have hb2 : (((c2 i) : ℝ) • homPartB q : Poly).totalDegree ≤ 1 := by
    exact (MvPolynomial.totalDegree_smul_le (c2 i) (homPartB q)).trans (homPartB_totalDegree_le_one q)
  have hb : b.totalDegree ≤ 1 := by
    dsimp [b]
    exact (MvPolynomial.totalDegree_add _ _).trans (max_le hb1 hb2)
  have hab : (a * b).totalDegree ≤ 3 := by
    calc
      (a * b).totalDegree ≤ a.totalDegree + b.totalDegree := by
        exact MvPolynomial.totalDegree_mul _ _
      _ ≤ 3 := by omega
  have hba : (b * a).totalDegree ≤ 3 := by
    calc
      (b * a).totalDegree ≤ b.totalDegree + a.totalDegree := by
        exact MvPolynomial.totalDegree_mul _ _
      _ ≤ 3 := by omega
  have hb2deg : (b ^ 2).totalDegree ≤ 3 := by
    calc
      (b ^ 2).totalDegree ≤ 2 * b.totalDegree := by
        simpa using MvPolynomial.totalDegree_pow b 2
      _ ≤ 2 := by omega
      _ ≤ 3 := by omega
  have habba : (a * b + b * a).totalDegree ≤ 3 := by
    calc
      (a * b + b * a).totalDegree ≤ max (a * b).totalDegree (b * a).totalDegree := by
        exact MvPolynomial.totalDegree_add _ _
      _ ≤ 3 := max_le hab hba
  dsimp [spanThreeAff1KerRaw]
  change (((a + b) ^ 2) - ((c0 i) ^ 2) • ((homPart q) ^ 2)).totalDegree ≤ 3
  have ha2 : a ^ 2 = ((c0 i) ^ 2) • ((homPart q) ^ 2) := by
    dsimp [a]
    simp [pow_two, smul_smul]
  have hsquare :
      (((a + b) ^ 2) - ((c0 i) ^ 2) • ((homPart q) ^ 2)) =
        (a * b + b * a) + b ^ 2 := by
    rw [← ha2]
    ring_nf
  rw [hsquare]
  calc
    ((a * b + b * a) + b ^ 2).totalDegree ≤ max (a * b + b * a).totalDegree (b ^ 2).totalDegree := by
      exact MvPolynomial.totalDegree_add _ _
    _ ≤ 3 := max_le habba hb2deg

private theorem spanThreeAff1KerRaw_sigma_sub_totalDegree_le_three
    (c0 c1 c2 : Fin 4 → ℝ) (q : Poly) :
    (sigma (spanThreeAff1KerRaw c0 c1 c2 q) -
      (∑ i : Fin 4, (c0 i) ^ 2) • ((homPart q) ^ 2)).totalDegree ≤ 3 := by
  have hsum :
      sigma (spanThreeAff1KerRaw c0 c1 c2 q) -
        (∑ i : Fin 4, (c0 i) ^ 2) • ((homPart q) ^ 2) =
      ∑ i : Fin 4,
        (((spanThreeAff1KerRaw c0 c1 c2 q i) ^ 2) - ((c0 i) ^ 2) • ((homPart q) ^ 2)) := by
    rw [sigma, Finset.sum_smul, ← Finset.sum_sub_distrib]
  rw [hsum]
  refine MvPolynomial.totalDegree_finsetSum_le ?_
  intro i hi
  exact spanThreeAff1Ker_component_remainder_totalDegree_le_three c0 c1 c2 q i

private theorem square_sub_homPart_sq_totalDegree_le_three {q : Poly} (hq : IsQuadratic q) :
    (q ^ 2 - (homPart q) ^ 2).totalDegree ≤ 3 := by
  have hlow : (lowPart q).totalDegree ≤ 1 := lowPart_totalDegree_le_one q
  have hhom : (homPart q).totalDegree ≤ 2 := homPart_totalDegree_le_two q
  have hlow2 : ((lowPart q) ^ 2).totalDegree ≤ 3 := by
    calc
      ((lowPart q) ^ 2).totalDegree ≤ 2 * (lowPart q).totalDegree := by
        simpa using MvPolynomial.totalDegree_pow (lowPart q) 2
      _ ≤ 2 := by omega
      _ ≤ 3 := by omega
  have hcross1 : (lowPart q * homPart q).totalDegree ≤ 3 := by
    calc
      (lowPart q * homPart q).totalDegree ≤ (lowPart q).totalDegree + (homPart q).totalDegree := by
        exact MvPolynomial.totalDegree_mul _ _
      _ ≤ 3 := by omega
  have hcross2 : (homPart q * lowPart q).totalDegree ≤ 3 := by
    calc
      (homPart q * lowPart q).totalDegree ≤ (homPart q).totalDegree + (lowPart q).totalDegree := by
        exact MvPolynomial.totalDegree_mul _ _
      _ ≤ 3 := by omega
  have hsplit :
      q ^ 2 - (homPart q) ^ 2 =
        (lowPart q) ^ 2 + lowPart q * homPart q + homPart q * lowPart q := by
    nth_rewrite 1 [quadratic_split_low_hom hq]
    ring
  rw [hsplit]
  have h12 : (((lowPart q) ^ 2) + lowPart q * homPart q).totalDegree ≤ 3 := by
    calc
      (((lowPart q) ^ 2) + lowPart q * homPart q).totalDegree
          ≤ max ((lowPart q) ^ 2).totalDegree (lowPart q * homPart q).totalDegree := by
            exact MvPolynomial.totalDegree_add _ _
      _ ≤ 3 := max_le hlow2 hcross1
  calc
    (((lowPart q) ^ 2 + lowPart q * homPart q) + homPart q * lowPart q).totalDegree
        ≤ max (((lowPart q) ^ 2) + lowPart q * homPart q).totalDegree
            (homPart q * lowPart q).totalDegree := by
              exact MvPolynomial.totalDegree_add _ _
    _ ≤ 3 := max_le h12 hcross2

private theorem spanThreeAff1KerRemainder_totalDegree_le_three
    {c0 c1 c2 : Fin 4 → ℝ} {q : Poly} (hq : IsQuadratic q)
    (hc0 : c0 ≠ 0) :
    (q ^ 2 - sigma (spanThreeAff1Ker c0 c1 c2 q)).totalDegree ≤ 3 := by
  let s0 : ℝ := ∑ i : Fin 4, (c0 i) ^ 2
  have hs0pos : 0 < s0 := sum_sq_pos_of_ne_zero c0 hc0
  have hs0ne : s0 ≠ 0 := ne_of_gt hs0pos
  have h1 : (q ^ 2 - (homPart q) ^ 2).totalDegree ≤ 3 := square_sub_homPart_sq_totalDegree_le_three hq
  have h2 :
      (((homPart q) ^ 2) - sigma (spanThreeAff1Ker c0 c1 c2 q)).totalDegree ≤ 3 := by
    have hscale :
        sigma (spanThreeAff1Ker c0 c1 c2 q) =
          (1 / s0) • sigma (spanThreeAff1KerRaw c0 c1 c2 q) := by
      unfold spanThreeAff1Ker spanThreeAff1KerScale
      rw [sigma_smul_local]
      have hsqrtne : Real.sqrt s0 ≠ 0 := by
        exact Real.sqrt_ne_zero'.mpr hs0pos
      have hsq : ((Real.sqrt s0)⁻¹ : ℝ) ^ 2 = 1 / s0 := by
        calc
          ((Real.sqrt s0)⁻¹ : ℝ) ^ 2 = ((Real.sqrt s0) ^ 2)⁻¹ := by
            field_simp [pow_two, hsqrtne]
          _ = 1 / s0 := by
            rw [Real.sq_sqrt (le_of_lt hs0pos)]
            field_simp [hs0ne]
      simp [hsq, s0]
    have hraw :
        (sigma (spanThreeAff1KerRaw c0 c1 c2 q) - s0 • ((homPart q) ^ 2)).totalDegree ≤ 3 := by
      simpa [s0] using spanThreeAff1KerRaw_sigma_sub_totalDegree_le_three c0 c1 c2 q
    have hscaled :
        ((1 / s0) • sigma (spanThreeAff1KerRaw c0 c1 c2 q) - (homPart q) ^ 2).totalDegree ≤ 3 := by
      have hEq :
          ((1 / s0) : ℝ) • sigma (spanThreeAff1KerRaw c0 c1 c2 q) - (homPart q) ^ 2 =
            (1 / s0) • (sigma (spanThreeAff1KerRaw c0 c1 c2 q) - s0 • ((homPart q) ^ 2)) := by
        have hs0inv : ((1 / s0 : ℝ) * s0) = 1 := by
          field_simp [hs0ne]
        calc
          ((1 / s0) : ℝ) • sigma (spanThreeAff1KerRaw c0 c1 c2 q) - (homPart q) ^ 2
              = ((1 / s0) : ℝ) • sigma (spanThreeAff1KerRaw c0 c1 c2 q) -
                  (((1 / s0 : ℝ)) • (s0 • ((homPart q) ^ 2))) := by
                    rw [smul_smul, hs0inv, one_smul]
          _ = (1 / s0) • (sigma (spanThreeAff1KerRaw c0 c1 c2 q) - s0 • ((homPart q) ^ 2)) := by
                simp [sub_eq_add_neg, smul_add, smul_neg, smul_smul]
      rw [hEq]
      exact (MvPolynomial.totalDegree_smul_le (1 / s0)
        (sigma (spanThreeAff1KerRaw c0 c1 c2 q) - s0 • ((homPart q) ^ 2))).trans hraw
    have hscaled' :
        (((homPart q) ^ 2) - (1 / s0) • sigma (spanThreeAff1KerRaw c0 c1 c2 q)).totalDegree ≤ 3 := by
      calc
        (((homPart q) ^ 2) - (1 / s0) • sigma (spanThreeAff1KerRaw c0 c1 c2 q)).totalDegree
            = (-(((1 / s0) • sigma (spanThreeAff1KerRaw c0 c1 c2 q)) - (homPart q) ^ 2)).totalDegree := by
                ring_nf
        _ = (((1 / s0) • sigma (spanThreeAff1KerRaw c0 c1 c2 q)) - (homPart q) ^ 2).totalDegree := by
              rw [MvPolynomial.totalDegree_neg]
        _ ≤ 3 := hscaled
    rw [hscale]
    simpa using hscaled'
  calc
    (q ^ 2 - sigma (spanThreeAff1Ker c0 c1 c2 q)).totalDegree
        ≤ max (q ^ 2 - (homPart q) ^ 2).totalDegree
            (((homPart q) ^ 2) - sigma (spanThreeAff1Ker c0 c1 c2 q)).totalDegree := by
              have hEq :
                  q ^ 2 - sigma (spanThreeAff1Ker c0 c1 c2 q) =
                    (q ^ 2 - (homPart q) ^ 2) +
                      (((homPart q) ^ 2) - sigma (spanThreeAff1Ker c0 c1 c2 q)) := by
                ring
              rw [hEq]
              exact MvPolynomial.totalDegree_add _ _
    _ ≤ 3 := max_le h1 h2

theorem residual_eq_zero_of_contains_aff1
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec} {p : Poly} {c0 c1 c2 : Fin 4 → ℝ}
    (hu : IsAdmissiblePoint u)
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (h1 : ∑ i : Fin 4, c1 i • u i = x0)
    (h2 : ∑ i : Fin 4, c2 i • u i = x1)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have hc0 : c0 ≠ 0 := by
    intro hc0
    have hbad := h0
    simp [hc0] at hbad
  rcases hp with ⟨_, k, qs, hqdeg, hpq⟩
  let imgPart : Poly := ∑ i : Fin k, ((qs i) ^ 2 - sigma (spanThreeAff1Ker c0 c1 c2 (qs i)))
  let w : Fin k → RankFourVec := fun i => spanThreeAff1Ker c0 c1 c2 (qs i)
  have himgDeg : imgPart.totalDegree ≤ 3 := by
    unfold imgPart
    refine MvPolynomial.totalDegree_finsetSum_le ?_
    intro i hi
    exact spanThreeAff1KerRemainder_totalDegree_le_three (hqdeg i) hc0
  have himgPart : InAdmissibleImage u imgPart := by
    exact cubic_in_image_of_contains_aff1 h0 h1 h2 himgDeg
  have hker : ∀ i ∈ (Finset.univ : Finset (Fin k)), InAdmissibleKer u (w i) := by
    intro i hi
    rcases spanThreeAff1KerRaw_inKer (u := u) (q := qs i) h0 h1 h2 with ⟨hwadm, hwker⟩
    refine ⟨isAdmissibleDirection_smul (spanThreeAff1KerScale c0) hwadm, ?_⟩
    change A u ((spanThreeAff1KerScale c0) • spanThreeAff1KerRaw c0 c1 c2 (qs i)) = 0
    rw [A_smul_right, hwker]
    simp
  have hdecomp : p = imgPart + Finset.sum (Finset.univ : Finset (Fin k)) (fun i => sigma (w i)) := by
    calc
      p = ∑ i : Fin k, (qs i) ^ 2 := hpq
      _ = ∑ i : Fin k, (((qs i) ^ 2 - sigma (spanThreeAff1Ker c0 c1 c2 (qs i))) +
            sigma (spanThreeAff1Ker c0 c1 c2 (qs i))) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
      _ = imgPart + Finset.sum (Finset.univ : Finset (Fin k)) (fun i => sigma (w i)) := by
            simp [imgPart, w]
  exact admissible_image_plus_indexed_sigma_family_residual_eq_zero
    (B := B) (u := u) (uImg := u) hu hsocp
    (imageOrthogonalResidual_self (B := B) hsocp.1)
    himgPart hker hdecomp

theorem residual_eq_zero_of_socp_of_eq_mix_mapVec_contains_aff1
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
    {q : Poly}
    (hq : IsQuadratic q)
    (huRep : mix M.transpose (mapVec e.symm.toAlgHom u) = ![(1 : Poly), x0, x1, q])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  have huRepAdmissible : IsAdmissiblePoint (![(1 : Poly), x0, x1, q] : RankFourVec) := by
    intro i
    fin_cases i
    · simp [IsQuadratic]
    · simpa [x0] using (show IsQuadratic (MvPolynomial.X 0 : Poly) by simp [IsQuadratic])
    · simpa [x1] using (show IsQuadratic (MvPolynomial.X 1 : Poly) by simp [IsQuadratic])
    · simpa using hq
  have hRep :
      ∀ {B0 : DotForm} [Fact B0.toQuadraticMap.PosDef] {p0 : Poly},
        IsSOSQuartic p0 → IsSOCP B0 p0 (![(1 : Poly), x0, x1, q] : RankFourVec) →
          residual p0 (![(1 : Poly), x0, x1, q] : RankFourVec) = 0 := by
    intro B0 _ p0 hp0 hsocp0
    exact residual_eq_zero_of_contains_aff1
      (c0 := ![1, 0, 0, 0]) (c1 := ![0, 1, 0, 0]) (c2 := ![0, 0, 1, 0])
      (B := B0) (u := ![(1 : Poly), x0, x1, q]) huRepAdmissible
      (h0 := by simp [Fin.sum_univ_four])
      (h1 := by simp [Fin.sum_univ_four, x0])
      (h2 := by simp [Fin.sum_univ_four, x1])
      hp0 hsocp0
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec
    (![(1 : Poly), x0, x1, q])
    hRep e heQuad heQuadSymm heQuarticSymm M hMtM hMMt hB hp huRep hsocp

theorem residual_eq_zero_of_socp_of_eq_mix_affineEquiv_contains_aff1
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
    {q : Poly}
    (hq : IsQuadratic q)
    (huRep :
      mix M.transpose
        (mapVec (affineEquiv A A' b b' hAA' hA'A hb hb').symm.toAlgHom u) =
          ![(1 : Poly), x0, x1, q])
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec_contains_aff1
    (e := affineEquiv A A' b b' hAA' hA'A hb hb')
    (heQuad := fun {_} hpq => isQuadratic_affineEquiv A A' b b' hAA' hA'A hb hb' hpq)
    (heQuadSymm := fun {_} hpq => isQuadratic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (heQuarticSymm := fun {_} hpq => isQuartic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (M := M) hMtM hMMt hB hp hq huRep hsocp

end TernaryQuartic
