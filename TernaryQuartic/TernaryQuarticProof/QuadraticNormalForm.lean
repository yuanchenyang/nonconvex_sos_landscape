import Mathlib
import TernaryQuartic.TernaryQuartic

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace TernaryQuartic

open scoped BigOperators

/-- The constant monomial in the dehomogenized two-variable quadratic space. -/
abbrev m00 : Fin 2 →₀ ℕ := 0

/-- The `x₀` monomial. -/
abbrev m10 : Fin 2 →₀ ℕ := Finsupp.single 0 1

/-- The `x₁` monomial. -/
abbrev m01 : Fin 2 →₀ ℕ := Finsupp.single 1 1

/-- The `x₀²` monomial. -/
abbrev m20 : Fin 2 →₀ ℕ := Finsupp.single 0 2

/-- The `x₀x₁` monomial. -/
abbrev m11 : Fin 2 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 1

/-- The `x₁²` monomial. -/
abbrev m02 : Fin 2 →₀ ℕ := Finsupp.single 1 2

/-- The six possible monomial supports of a quadratic in two variables. -/
def quadSupp : Finset (Fin 2 →₀ ℕ) := {m00, m10, m01, m20, m11, m02}

/-- Any finitely supported exponent vector on two variables of total degree at
most `2` is one of the six quadratic monomials. -/
theorem quad_case (d : Fin 2 →₀ ℕ) (h : d.sum (fun _ e => e) ≤ 2) :
    d = m00 ∨ d = m10 ∨ d = m01 ∨ d = m20 ∨ d = m11 ∨ d = m02 := by
  have hd : d 0 + d 1 ≤ 2 := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at h
    simpa using h
  have h0 : d 0 ≤ 2 := by
    omega
  have h1 : d 1 ≤ 2 := by
    omega
  interval_cases hx : d 0 <;> interval_cases hy : d 1
  · left
    ext i
    fin_cases i <;> simp [m00, hx, hy]
  · right
    right
    left
    ext i
    fin_cases i <;> simp [m01, hx, hy]
  · right
    right
    right
    right
    right
    ext i
    fin_cases i <;> simp [m02, hx, hy]
  · right
    left
    ext i
    fin_cases i <;> simp [m10, hx, hy]
  · right
    right
    right
    right
    left
    ext i
    fin_cases i <;> simp [m11, hx, hy]
  · exfalso
    omega
  · right
    right
    right
    left
    ext i
    fin_cases i <;> simp [m20, hx, hy]
  · exfalso
    omega
  · exfalso
    omega

/-- A quadratic polynomial in two variables has support contained in the six
quadratic monomials. -/
theorem quadratic_support_subset {q : Poly} (hq : IsQuadratic q) :
    q.support ⊆ quadSupp := by
  intro d hdq
  have hdeg : d.sum (fun _ e => e) ≤ 2 :=
    (MvPolynomial.le_totalDegree hdq).trans hq
  rcases quad_case d hdeg with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [quadSupp]

/-- Six-monomial normal form for quadratic polynomials in two variables. -/
theorem quadratic_sum_formula {q : Poly} (hq : IsQuadratic q) :
    q = ∑ d ∈ quadSupp, MvPolynomial.monomial d (MvPolynomial.coeff d q) := by
  calc
    q = ∑ d ∈ q.support, MvPolynomial.monomial d (MvPolynomial.coeff d q) := by
      exact (MvPolynomial.support_sum_monomial_coeff q).symm
    _ = ∑ d ∈ quadSupp, MvPolynomial.monomial d (MvPolynomial.coeff d q) := by
      exact Finset.sum_subset (s₁ := q.support) (s₂ := quadSupp)
        (f := fun d => MvPolynomial.monomial d (MvPolynomial.coeff d q))
        (quadratic_support_subset hq) (by
          intro d hd hdn
          have hcoeff : MvPolynomial.coeff d q = 0 :=
            MvPolynomial.notMem_support_iff.mp hdn
          simp [hcoeff])

end TernaryQuartic
