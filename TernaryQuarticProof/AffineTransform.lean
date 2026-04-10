import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import TernaryQuarticProof.Certificate

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace TernaryQuartic

open scoped BigOperators

/-- The affine-linear image of the variable `X i` under the change of variables
`x ↦ A x + b`. -/
def affineImage (A : Matrix (Fin 2) (Fin 2) ℝ) (b : Fin 2 → ℝ) (i : Fin 2) : Poly :=
  MvPolynomial.C (b i) + ∑ j : Fin 2, MvPolynomial.C (A i j) * MvPolynomial.X j

/-- The algebra homomorphism on polynomials induced by `x ↦ A x + b`. -/
def affineHom (A : Matrix (Fin 2) (Fin 2) ℝ) (b : Fin 2 → ℝ) : Poly →ₐ[ℝ] Poly :=
  MvPolynomial.aeval (affineImage A b)

@[simp] theorem affineHom_X
    (A : Matrix (Fin 2) (Fin 2) ℝ) (b : Fin 2 → ℝ) (i : Fin 2) :
    affineHom A b (MvPolynomial.X i) = affineImage A b i := by
  simp [affineHom]

@[simp] theorem affineHom_C
    (A : Matrix (Fin 2) (Fin 2) ℝ) (b : Fin 2 → ℝ) (r : ℝ) :
    affineHom A b (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [affineHom]

private theorem totalDegree_affineImage_le_one
    (A : Matrix (Fin 2) (Fin 2) ℝ) (b : Fin 2 → ℝ) (i : Fin 2) :
    (affineImage A b i).totalDegree ≤ 1 := by
  have hsum :
      (∑ j : Fin 2, MvPolynomial.C (A i j) * MvPolynomial.X j : Poly).totalDegree ≤ 1 := by
    refine MvPolynomial.totalDegree_finsetSum_le ?_
    intro j hj
    calc
      (MvPolynomial.C (A i j) * MvPolynomial.X j : Poly).totalDegree
          ≤ (MvPolynomial.C (A i j) : Poly).totalDegree + (MvPolynomial.X j : Poly).totalDegree := by
            exact MvPolynomial.totalDegree_mul _ _
      _ = 1 := by simp
  unfold affineImage
  calc
    (MvPolynomial.C (b i) + ∑ j : Fin 2, MvPolynomial.C (A i j) * MvPolynomial.X j : Poly).totalDegree
        ≤ max (MvPolynomial.C (b i) : Poly).totalDegree
            (∑ j : Fin 2, MvPolynomial.C (A i j) * MvPolynomial.X j : Poly).totalDegree := by
              exact MvPolynomial.totalDegree_add _ _
    _ ≤ 1 := by
          apply max_le
          · simp
          · exact hsum

private theorem totalDegree_affineHom_monomial_le
    (A : Matrix (Fin 2) (Fin 2) ℝ) (b : Fin 2 → ℝ)
    (d : Fin 2 →₀ ℕ) (r : ℝ) :
    (affineHom A b (MvPolynomial.monomial d r)).totalDegree ≤ d.sum (fun _ e => e) := by
  rw [affineHom, MvPolynomial.aeval_monomial, Finsupp.prod]
  let prodPart : Poly := d.support.prod fun i => affineImage A b i ^ (d i)
  have hprod :
      prodPart.totalDegree ≤ d.support.sum (fun i => (affineImage A b i ^ d i).totalDegree) := by
    simpa [prodPart] using (MvPolynomial.totalDegree_finset_prod d.support fun i => affineImage A b i ^ d i)
  have hsumle :
      d.support.sum (fun i => (affineImage A b i ^ d i).totalDegree) ≤ d.support.sum (fun i => d i) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    calc
      (affineImage A b i ^ d i).totalDegree ≤ d i * (affineImage A b i).totalDegree := by
        simpa using MvPolynomial.totalDegree_pow (affineImage A b i) (d i)
      _ ≤ d i * 1 := by
            gcongr
            exact totalDegree_affineImage_le_one A b i
      _ = d i := by ring
  calc
    (MvPolynomial.C r * prodPart).totalDegree
        ≤ (MvPolynomial.C r : Poly).totalDegree + prodPart.totalDegree := by
              exact MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + prodPart.totalDegree := by simp [prodPart]
    _ ≤ 0 + d.support.sum (fun i => (affineImage A b i ^ d i).totalDegree) := by
          simpa [zero_add] using add_le_add_left hprod 0
    _ ≤ 0 + d.support.sum (fun i => d i) := by
          simpa [zero_add] using add_le_add_left hsumle 0
    _ = d.sum (fun _ e => e) := by
          rw [Finsupp.sum]
          ring

/-- Affine changes of variables do not increase total degree. -/
theorem totalDegree_affineHom_le
    (A : Matrix (Fin 2) (Fin 2) ℝ) (b : Fin 2 → ℝ) (p : Poly) :
    (affineHom A b p).totalDegree ≤ p.totalDegree := by
  have hp' :
      affineHom A b p =
        ∑ d ∈ p.support, affineHom A b (MvPolynomial.monomial d (MvPolynomial.coeff d p)) := by
    have hmap :
        affineHom A b p =
          affineHom A b (∑ d ∈ p.support, MvPolynomial.monomial d (MvPolynomial.coeff d p)) := by
      exact congrArg (affineHom A b) (MvPolynomial.support_sum_monomial_coeff p).symm
    calc
      affineHom A b p =
          affineHom A b (∑ d ∈ p.support, MvPolynomial.monomial d (MvPolynomial.coeff d p)) := hmap
      _ = ∑ d ∈ p.support, affineHom A b (MvPolynomial.monomial d (MvPolynomial.coeff d p)) := by
            rw [map_sum]
  calc
    (affineHom A b p).totalDegree
        = (∑ d ∈ p.support, affineHom A b (MvPolynomial.monomial d (MvPolynomial.coeff d p))).totalDegree := by
            rw [hp']
    _ ≤ p.totalDegree := by
          refine MvPolynomial.totalDegree_finsetSum_le ?_
          intro d hd
          exact (totalDegree_affineHom_monomial_le A b d (MvPolynomial.coeff d p)).trans
            (MvPolynomial.le_totalDegree hd)

theorem isQuadratic_affineHom
    (A : Matrix (Fin 2) (Fin 2) ℝ) (b : Fin 2 → ℝ) {p : Poly}
    (hp : IsQuadratic p) :
    IsQuadratic (affineHom A b p) :=
  (totalDegree_affineHom_le A b p).trans hp

theorem isQuartic_affineHom
    (A : Matrix (Fin 2) (Fin 2) ℝ) (b : Fin 2 → ℝ) {p : Poly}
    (hp : IsQuartic p) :
    IsQuartic (affineHom A b p) :=
  (totalDegree_affineHom_le A b p).trans hp

/-- Apply a polynomial algebra homomorphism coordinatewise to a rank-4 vector. -/
def mapVec (φ : Poly →ₐ[ℝ] Poly) (u : RankFourVec) : RankFourVec :=
  fun i => φ (u i)

@[simp] theorem mapVec_apply (φ : Poly →ₐ[ℝ] Poly) (u : RankFourVec) (i : Fin 4) :
    mapVec φ u i = φ (u i) :=
  rfl

theorem isAdmissiblePoint_mapVec_affineHom
    (A : Matrix (Fin 2) (Fin 2) ℝ) (b : Fin 2 → ℝ) {u : RankFourVec}
    (hu : IsAdmissiblePoint u) :
    IsAdmissiblePoint (mapVec (affineHom A b) u) := by
  intro i
  exact isQuadratic_affineHom A b (hu i)

theorem A_mapVec
    (φ : Poly →ₐ[ℝ] Poly) (u v : RankFourVec) :
    A (mapVec φ u) (mapVec φ v) = φ (A u v) := by
  simp [A, mapVec, map_mul, map_sum]

theorem sigma_mapVec
    (φ : Poly →ₐ[ℝ] Poly) (u : RankFourVec) :
    sigma (mapVec φ u) = φ (sigma u) := by
  simp [sigma, mapVec, map_sum]

theorem residual_mapVec
    (φ : Poly →ₐ[ℝ] Poly) (p : Poly) (u : RankFourVec) :
    residual (φ p) (mapVec φ u) = φ (residual p u) := by
  simp [residual, sigma_mapVec, sub_eq_add_neg]

theorem affineHom_one_zero :
    affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 = AlgHom.id ℝ Poly := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [affineHom, affineImage, Matrix.one_apply]

theorem affineHom_affineImage
    (A A' : Matrix (Fin 2) (Fin 2) ℝ) (b b' : Fin 2 → ℝ) (i : Fin 2) :
    affineHom A b (affineImage A' b' i) =
      affineImage (A' * A) (fun j => b' j + Matrix.mulVec A' b j) i := by
  fin_cases i
  · change affineHom A b (affineImage A' b' 0) =
        affineImage (A' * A) (fun j => b' j + Matrix.mulVec A' b j) 0
    rw [show affineImage A' b' 0 =
        MvPolynomial.C (b' 0) + MvPolynomial.C (A' 0 0) * MvPolynomial.X 0 +
          MvPolynomial.C (A' 0 1) * MvPolynomial.X 1 by
          simp [affineImage, Fin.sum_univ_two, add_assoc]]
    simp [affineHom, affineImage, Matrix.mul_apply, Matrix.mulVec, Fin.sum_univ_two]
    ring_nf
  · change affineHom A b (affineImage A' b' 1) =
        affineImage (A' * A) (fun j => b' j + Matrix.mulVec A' b j) 1
    rw [show affineImage A' b' 1 =
        MvPolynomial.C (b' 1) + MvPolynomial.C (A' 1 0) * MvPolynomial.X 0 +
          MvPolynomial.C (A' 1 1) * MvPolynomial.X 1 by
          simp [affineImage, Fin.sum_univ_two, add_assoc]]
    simp [affineHom, affineImage, Matrix.mul_apply, Matrix.mulVec, Fin.sum_univ_two]
    ring_nf

theorem affineHom_comp
    (A A' : Matrix (Fin 2) (Fin 2) ℝ) (b b' : Fin 2 → ℝ) :
    (affineHom A b).comp (affineHom A' b') =
      affineHom (A' * A) (fun i => b' i + Matrix.mulVec A' b i) := by
  apply MvPolynomial.algHom_ext
  intro i
  simpa [AlgHom.comp_apply] using affineHom_affineImage A A' b b' i

/-- Affine change of variables with explicit inverse data. -/
def affineEquiv
    (A A' : Matrix (Fin 2) (Fin 2) ℝ) (b b' : Fin 2 → ℝ)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (hb : ∀ i, b' i + Matrix.mulVec A' b i = 0)
    (hb' : ∀ i, b i + Matrix.mulVec A b' i = 0) :
    Poly ≃ₐ[ℝ] Poly :=
  AlgEquiv.ofAlgHom (affineHom A b) (affineHom A' b') (by
    have hzero : (fun i => b' i + Matrix.mulVec A' b i) = 0 := by
      funext i
      exact hb i
    rw [affineHom_comp, hA'A, hzero, affineHom_one_zero])
    (by
      have hzero : (fun i => b i + Matrix.mulVec A b' i) = 0 := by
        funext i
        exact hb' i
      rw [affineHom_comp, hAA', hzero, affineHom_one_zero])

end TernaryQuartic
