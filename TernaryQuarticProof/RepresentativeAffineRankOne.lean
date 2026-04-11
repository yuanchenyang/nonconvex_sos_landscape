import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import TernaryQuarticProof.RepresentativeLowAffine
import TernaryQuarticProof.RepresentativeSurjective
import TernaryQuarticProof.QuadraticCoordinateForm

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace TernaryQuartic

open scoped BigOperators

/-- The polynomial obtained from a scalar relation vector. -/
private def relationPoly (u : RankFourVec) (c : Fin 4 → ℝ) : Poly :=
  ∑ i : Fin 4, c i • u i

private theorem relationPoly_add
    (u : RankFourVec) (c d : Fin 4 → ℝ) :
    relationPoly u (c + d) = relationPoly u c + relationPoly u d := by
  simp [relationPoly, Fin.sum_univ_four, add_smul, add_assoc, add_left_comm]

private theorem relationPoly_smul
    (u : RankFourVec) (a : ℝ) (c : Fin 4 → ℝ) :
    relationPoly u (a • c) = a • relationPoly u c := by
  simp [relationPoly, Fin.sum_univ_four, smul_smul]

/-- The linear map sending a scalar relation vector to the corresponding
quadratic polynomial. -/
private def relationPolyLin (u : RankFourVec) : (Fin 4 → ℝ) →ₗ[ℝ] Poly where
  toFun := relationPoly u
  map_add' := relationPoly_add u
  map_smul' := relationPoly_smul u

private theorem isQuadratic_relationPoly
    {u : RankFourVec} (hu : IsAdmissiblePoint u) (c : Fin 4 → ℝ) :
    IsQuadratic (relationPoly u c) := by
  have h0 : IsQuadratic (c 0 • u 0) := by
    exact (MvPolynomial.totalDegree_smul_le (c 0) (u 0)).trans (hu 0)
  have h1 : IsQuadratic (c 1 • u 1) := by
    exact (MvPolynomial.totalDegree_smul_le (c 1) (u 1)).trans (hu 1)
  have h2 : IsQuadratic (c 2 • u 2) := by
    exact (MvPolynomial.totalDegree_smul_le (c 2) (u 2)).trans (hu 2)
  have h3 : IsQuadratic (c 3 • u 3) := by
    exact (MvPolynomial.totalDegree_smul_le (c 3) (u 3)).trans (hu 3)
  have h01 : IsQuadratic (c 0 • u 0 + c 1 • u 1) := by
    calc
      (c 0 • u 0 + c 1 • u 1).totalDegree ≤
          max (c 0 • u 0).totalDegree (c 1 • u 1).totalDegree :=
        MvPolynomial.totalDegree_add _ _
      _ ≤ 2 := max_le h0 h1
  have h23 : IsQuadratic (c 2 • u 2 + c 3 • u 3) := by
    calc
      (c 2 • u 2 + c 3 • u 3).totalDegree ≤
          max (c 2 • u 2).totalDegree (c 3 • u 3).totalDegree :=
        MvPolynomial.totalDegree_add _ _
      _ ≤ 2 := max_le h2 h3
  have hsplit :
      relationPoly u c =
        (c 0 • u 0 + c 1 • u 1) + (c 2 • u 2 + c 3 • u 3) := by
    simp [relationPoly, Fin.sum_univ_four, add_assoc]
  calc
    (relationPoly u c).totalDegree
        ≤ max (c 0 • u 0 + c 1 • u 1).totalDegree
            (c 2 • u 2 + c 3 • u 3).totalDegree := by
              rw [hsplit]
              exact MvPolynomial.totalDegree_add _ _
    _ ≤ 2 := max_le h01 h23

/-- Constant, `x₀`, and `x₁` coefficients of a scalar relation. -/
private def affineCoeffMap (u : RankFourVec) :
    (Fin 4 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun c := ![
    MvPolynomial.coeff m00 (relationPoly u c),
    MvPolynomial.coeff m10 (relationPoly u c),
    MvPolynomial.coeff m01 (relationPoly u c)]
  map_add' c d := by
    ext j
    fin_cases j <;>
      simp [relationPoly_add, MvPolynomial.coeff_add]
  map_smul' a c := by
    ext j
    fin_cases j <;>
      simp [relationPoly_smul, MvPolynomial.coeff_smul]

/-- Coefficient matrix of three homogeneous quadratics in the
`(x₀², x₀x₁, x₁²)` basis. -/
private def homCoeffMatrix (q : Fin 3 → Poly) : Matrix (Fin 3) (Fin 3) ℝ
  | j, 0 => MvPolynomial.coeff m20 (q j)
  | j, 1 => MvPolynomial.coeff m11 (q j)
  | j, 2 => MvPolynomial.coeff m02 (q j)

private theorem sum_homCoeffMatrix_basis (q : Fin 3 → Poly) (j : Fin 3) :
    ∑ k : Fin 3, homCoeffMatrix q j k • homQuadBasis k =
      MvPolynomial.coeff m20 (q j) • (x0 ^ 2 : Poly) +
        MvPolynomial.coeff m11 (q j) • (x0 * x1 : Poly) +
          MvPolynomial.coeff m02 (q j) • (x1 ^ 2 : Poly) := by
  fin_cases j <;> simp [homCoeffMatrix, homQuadBasis, Fin.sum_univ_three]

private theorem det_ne_zero_of_homCoeffMatrix
    {q : Fin 3 → Poly}
    (hq : ∀ j : Fin 3, IsQuadratic (q j))
    (h00 : ∀ j : Fin 3, MvPolynomial.coeff m00 (q j) = 0)
    (h10 : ∀ j : Fin 3, MvPolynomial.coeff m10 (q j) = 0)
    (h01 : ∀ j : Fin 3, MvPolynomial.coeff m01 (q j) = 0)
    (hqind : LinearIndependent ℝ q) :
    (homCoeffMatrix q).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hvne, hvzero⟩ :=
    Matrix.exists_mulVec_eq_zero_iff (M := (homCoeffMatrix q).transpose) |>.mpr (by simpa using hdet)
  have hk0 : ∀ k : Fin 3, ∑ j : Fin 3, v j * homCoeffMatrix q j k = 0 := by
    intro k
    have hk := congrArg (fun z : Fin 3 → ℝ => z k) hvzero
    simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm, mul_assoc] using hk
  have hcomb :
      ∑ j : Fin 3, v j • q j = 0 := by
    calc
      ∑ j : Fin 3, v j • q j
          = ∑ j : Fin 3, v j • (∑ k : Fin 3, homCoeffMatrix q j k • homQuadBasis k) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [homogeneousQuadratic_eq (hq j) (h00 j) (h10 j) (h01 j)]
              rw [sum_homCoeffMatrix_basis]
      _ = ∑ j : Fin 3, ∑ k : Fin 3, (v j * homCoeffMatrix q j k) • homQuadBasis k := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [Finset.smul_sum, smul_smul]
      _ = ∑ k : Fin 3, (∑ j : Fin 3, v j * homCoeffMatrix q j k) • homQuadBasis k := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro k hk
            simpa [smul_smul] using
              (Finset.sum_smul
                (s := (Finset.univ : Finset (Fin 3)))
                (f := fun j : Fin 3 => v j * homCoeffMatrix q j k)
                (x := homQuadBasis k)).symm
      _ = 0 := by
            simp [hk0]
  have hvj : ∀ j : Fin 3, v j = 0 := by
    intro j
    exact LinearIndependent.eq_coords_of_eq hqind
      (f := v) (g := 0) (by simpa using hcomb) j
  apply hvne
  funext j
  exact hvj j

theorem residual_eq_zero_of_relations_const_affineRankOne
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (1 : Poly))
    (hrange :
      LinearMap.range (affineCoeffMap u) =
        Submodule.span ℝ ({![1, 0, 0]} : Set (Fin 3 → ℝ)))
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let rel : (Fin 4 → ℝ) →ₗ[ℝ] Poly := relationPolyLin u
  by_cases hrelker : LinearMap.ker rel = ⊥
  · let L : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) := affineCoeffMap u
    have hfinrange : Module.finrank ℝ (LinearMap.range L) = 1 := by
      rw [hrange, finrank_span_singleton]
      intro hzero
      have h0coord := congrArg (fun z : Fin 3 → ℝ => z 0) hzero
      simp at h0coord
    have hfinder : Module.finrank ℝ (Fin 4 → ℝ) = 4 := by
      calc
        Module.finrank ℝ (Fin 4 → ℝ) = Fintype.card (Fin 4) :=
          Module.finrank_fintype_fun_eq_card (R := ℝ) (η := Fin 4)
        _ = 4 := by decide
    have hkerdim : Module.finrank ℝ (LinearMap.ker L) = 3 := by
      have hsum := LinearMap.finrank_range_add_finrank_ker L
      omega
    let b : Module.Basis (Fin 3) ℝ (LinearMap.ker L) :=
      Module.finBasisOfFinrankEq ℝ (LinearMap.ker L) hkerdim
    let c : Fin 3 → Fin 4 → ℝ := fun j => (b j : Fin 4 → ℝ)
    let q : Fin 3 → Poly := fun j => relationPoly u (c j)
    have hc : ∀ j : Fin 3, ∑ i : Fin 4, c j i • u i = q j := by
      intro j
      rfl
    have hq : ∀ j : Fin 3, IsQuadratic (q j) := by
      intro j
      dsimp [q]
      exact isQuadratic_relationPoly hu (c j)
    have h00 : ∀ j : Fin 3, MvPolynomial.coeff m00 (q j) = 0 := by
      intro j
      have hj0 : L (c j) = 0 := (b j).2
      have hj := congrArg (fun z : Fin 3 → ℝ => z 0) hj0
      have hj' : MvPolynomial.coeff m00 (relationPoly u (c j)) = 0 := by
        simpa [L, affineCoeffMap] using hj
      simpa [q] using hj'
    have h10 : ∀ j : Fin 3, MvPolynomial.coeff m10 (q j) = 0 := by
      intro j
      have hj0 : L (c j) = 0 := (b j).2
      have hj := congrArg (fun z : Fin 3 → ℝ => z 1) hj0
      have hj' : MvPolynomial.coeff m10 (relationPoly u (c j)) = 0 := by
        simpa [L, affineCoeffMap] using hj
      simpa [q] using hj'
    have h01 : ∀ j : Fin 3, MvPolynomial.coeff m01 (q j) = 0 := by
      intro j
      have hj0 : L (c j) = 0 := (b j).2
      have hj := congrArg (fun z : Fin 3 → ℝ => z 2) hj0
      have hj' : MvPolynomial.coeff m01 (relationPoly u (c j)) = 0 := by
        simpa [L, affineCoeffMap] using hj
      simpa [q] using hj'
    let relKer : (LinearMap.ker L) →ₗ[ℝ] Poly := {
      toFun := fun x => relationPoly u (x : Fin 4 → ℝ)
      map_add' x y := by
        simp [relationPoly, Fin.sum_univ_four, add_smul, add_assoc, add_left_comm]
      map_smul' a x := by
        simp [relationPoly, Fin.sum_univ_four, smul_smul]
    }
    have hrelKerBot : LinearMap.ker relKer = ⊥ := by
      ext x
      constructor
      · intro hx
        rw [Submodule.mem_bot]
        have hrelInj : Function.Injective rel := LinearMap.ker_eq_bot.mp hrelker
        have hxrel : rel x.1 = 0 := by
          simpa [rel, relationPolyLin, relKer] using hx
        have hx0 : x.1 = 0 := by
          have hxrel0 : rel x.1 = rel 0 := by
            simpa [rel, relationPolyLin, relationPoly, Fin.sum_univ_four] using hxrel
          exact hrelInj hxrel0
        exact Subtype.ext hx0
      · intro hx
        rw [Submodule.mem_bot] at hx
        subst x
        simp [relKer]
    have hqind : LinearIndependent ℝ q := by
      simpa [q, c, relKer, rel] using b.linearIndependent.map' relKer hrelKerBot
    let A : Matrix (Fin 3) (Fin 3) ℝ := homCoeffMatrix q
    have hA : ∀ j : Fin 3, q j = ∑ k : Fin 3, A j k • homQuadBasis k := by
      intro j
      rw [homogeneousQuadratic_eq (hq j) (h00 j) (h10 j) (h01 j)]
      rw [sum_homCoeffMatrix_basis]
    have hdet : A.det ≠ 0 := det_ne_zero_of_homCoeffMatrix hq h00 h10 h01 hqind
    exact residual_eq_zero_of_relations_const_homQuadBasis_det
      (B := B) (u := u) hu h0
      (c := c) (A := A)
      (hc := by
        intro j
        exact (hc j).trans (hA j))
      hdet hp hsocp
  · have hnebot : LinearMap.ker rel ≠ ⊥ := hrelker
    rcases (Submodule.ne_bot_iff _).mp hnebot with ⟨c, hc_mem, hc_ne⟩
    have hzero : relationPoly u c = 0 := by
      simp [rel, relationPolyLin, relationPoly] at hc_mem
      simpa using hc_mem
    exact residual_eq_zero_of_constant_relation
      (B := B) (u := u) hu hzero hc_ne hp hsocp

theorem residual_eq_zero_of_relations_constX0_affineRankOne
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    {α : ℝ}
    (hα : α ≠ 0)
    (hu : IsAdmissiblePoint u)
    {c0 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = (MvPolynomial.C α : Poly) + x0)
    (hrange :
      LinearMap.range (affineCoeffMap u) =
        Submodule.span ℝ ({![α, 1, 0]} : Set (Fin 3 → ℝ)))
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let rel : (Fin 4 → ℝ) →ₗ[ℝ] Poly := relationPolyLin u
  by_cases hrelker : LinearMap.ker rel = ⊥
  · let L : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) := affineCoeffMap u
    have hfinrange : Module.finrank ℝ (LinearMap.range L) = 1 := by
      rw [hrange, finrank_span_singleton]
      intro hzero
      have h1coord := congrArg (fun z : Fin 3 → ℝ => z 1) hzero
      simp at h1coord
    have hfinder : Module.finrank ℝ (Fin 4 → ℝ) = 4 := by
      calc
        Module.finrank ℝ (Fin 4 → ℝ) = Fintype.card (Fin 4) :=
          Module.finrank_fintype_fun_eq_card (R := ℝ) (η := Fin 4)
        _ = 4 := by decide
    have hkerdim : Module.finrank ℝ (LinearMap.ker L) = 3 := by
      have hsum := LinearMap.finrank_range_add_finrank_ker L
      omega
    let b : Module.Basis (Fin 3) ℝ (LinearMap.ker L) :=
      Module.finBasisOfFinrankEq ℝ (LinearMap.ker L) hkerdim
    let c : Fin 3 → Fin 4 → ℝ := fun j => (b j : Fin 4 → ℝ)
    let q : Fin 3 → Poly := fun j => relationPoly u (c j)
    have hc : ∀ j : Fin 3, ∑ i : Fin 4, c j i • u i = q j := by
      intro j
      rfl
    have hq : ∀ j : Fin 3, IsQuadratic (q j) := by
      intro j
      dsimp [q]
      exact isQuadratic_relationPoly hu (c j)
    have h00 : ∀ j : Fin 3, MvPolynomial.coeff m00 (q j) = 0 := by
      intro j
      have hj0 : L (c j) = 0 := (b j).2
      have hj := congrArg (fun z : Fin 3 → ℝ => z 0) hj0
      have hj' : MvPolynomial.coeff m00 (relationPoly u (c j)) = 0 := by
        simpa [L, affineCoeffMap] using hj
      simpa [q] using hj'
    have h10 : ∀ j : Fin 3, MvPolynomial.coeff m10 (q j) = 0 := by
      intro j
      have hj0 : L (c j) = 0 := (b j).2
      have hj := congrArg (fun z : Fin 3 → ℝ => z 1) hj0
      have hj' : MvPolynomial.coeff m10 (relationPoly u (c j)) = 0 := by
        simpa [L, affineCoeffMap] using hj
      simpa [q] using hj'
    have h01 : ∀ j : Fin 3, MvPolynomial.coeff m01 (q j) = 0 := by
      intro j
      have hj0 : L (c j) = 0 := (b j).2
      have hj := congrArg (fun z : Fin 3 → ℝ => z 2) hj0
      have hj' : MvPolynomial.coeff m01 (relationPoly u (c j)) = 0 := by
        simpa [L, affineCoeffMap] using hj
      simpa [q] using hj'
    let relKer : (LinearMap.ker L) →ₗ[ℝ] Poly := {
      toFun := fun x => relationPoly u (x : Fin 4 → ℝ)
      map_add' x y := by
        simp [relationPoly, Fin.sum_univ_four, add_smul, add_assoc, add_left_comm]
      map_smul' a x := by
        simp [relationPoly, Fin.sum_univ_four, smul_smul]
    }
    have hrelKerBot : LinearMap.ker relKer = ⊥ := by
      ext x
      constructor
      · intro hx
        rw [Submodule.mem_bot]
        have hrelInj : Function.Injective rel := LinearMap.ker_eq_bot.mp hrelker
        have hxrel : rel x.1 = 0 := by
          simpa [rel, relationPolyLin, relKer] using hx
        have hx0 : x.1 = 0 := by
          have hxrel0 : rel x.1 = rel 0 := by
            simpa [rel, relationPolyLin, relationPoly, Fin.sum_univ_four] using hxrel
          exact hrelInj hxrel0
        exact Subtype.ext hx0
      · intro hx
        rw [Submodule.mem_bot] at hx
        subst x
        simp [relKer]
    have hqind : LinearIndependent ℝ q := by
      simpa [q, c, relKer, rel] using b.linearIndependent.map' relKer hrelKerBot
    let A : Matrix (Fin 3) (Fin 3) ℝ := homCoeffMatrix q
    have hA : ∀ j : Fin 3, q j = ∑ k : Fin 3, A j k • homQuadBasis k := by
      intro j
      rw [homogeneousQuadratic_eq (hq j) (h00 j) (h10 j) (h01 j)]
      rw [sum_homCoeffMatrix_basis]
    have hdet : A.det ≠ 0 := det_ne_zero_of_homCoeffMatrix hq h00 h10 h01 hqind
    exact residual_eq_zero_of_relations_constX0_homQuadBasis_det
      (B := B) (u := u) hα hu h0
      (c := c) (A := A)
      (hc := by
        intro j
        exact (hc j).trans (hA j))
      hdet hp hsocp
  · have hnebot : LinearMap.ker rel ≠ ⊥ := hrelker
    rcases (Submodule.ne_bot_iff _).mp hnebot with ⟨c, hc_mem, hc_ne⟩
    have hzero : relationPoly u c = 0 := by
      simp [rel, relationPolyLin, relationPoly] at hc_mem
      simpa using hc_mem
    exact residual_eq_zero_of_constant_relation
      (B := B) (u := u) hu hzero hc_ne hp hsocp

theorem residual_eq_zero_of_relations_x0_affineRankOne
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (hrange :
      LinearMap.range (affineCoeffMap u) =
        Submodule.span ℝ ({![0, 1, 0]} : Set (Fin 3 → ℝ)))
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let rel : (Fin 4 → ℝ) →ₗ[ℝ] Poly := relationPolyLin u
  by_cases hrelker : LinearMap.ker rel = ⊥
  · let L : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) := affineCoeffMap u
    have hfinrange : Module.finrank ℝ (LinearMap.range L) = 1 := by
      rw [hrange, finrank_span_singleton]
      intro hzero
      have h1coord := congrArg (fun z : Fin 3 → ℝ => z 1) hzero
      simp at h1coord
    have hfinder : Module.finrank ℝ (Fin 4 → ℝ) = 4 := by
      calc
        Module.finrank ℝ (Fin 4 → ℝ) = Fintype.card (Fin 4) :=
          Module.finrank_fintype_fun_eq_card (R := ℝ) (η := Fin 4)
        _ = 4 := by decide
    have hkerdim : Module.finrank ℝ (LinearMap.ker L) = 3 := by
      have hsum := LinearMap.finrank_range_add_finrank_ker L
      omega
    let b : Module.Basis (Fin 3) ℝ (LinearMap.ker L) :=
      Module.finBasisOfFinrankEq ℝ (LinearMap.ker L) hkerdim
    let c : Fin 3 → Fin 4 → ℝ := fun j => (b j : Fin 4 → ℝ)
    let q : Fin 3 → Poly := fun j => relationPoly u (c j)
    have hc : ∀ j : Fin 3, ∑ i : Fin 4, c j i • u i = q j := by
      intro j
      rfl
    have hq : ∀ j : Fin 3, IsQuadratic (q j) := by
      intro j
      dsimp [q]
      exact isQuadratic_relationPoly hu (c j)
    have h00 : ∀ j : Fin 3, MvPolynomial.coeff m00 (q j) = 0 := by
      intro j
      have hj0 : L (c j) = 0 := (b j).2
      have hj := congrArg (fun z : Fin 3 → ℝ => z 0) hj0
      have hj' : MvPolynomial.coeff m00 (relationPoly u (c j)) = 0 := by
        simpa [L, affineCoeffMap] using hj
      simpa [q] using hj'
    have h10 : ∀ j : Fin 3, MvPolynomial.coeff m10 (q j) = 0 := by
      intro j
      have hj0 : L (c j) = 0 := (b j).2
      have hj := congrArg (fun z : Fin 3 → ℝ => z 1) hj0
      have hj' : MvPolynomial.coeff m10 (relationPoly u (c j)) = 0 := by
        simpa [L, affineCoeffMap] using hj
      simpa [q] using hj'
    have h01 : ∀ j : Fin 3, MvPolynomial.coeff m01 (q j) = 0 := by
      intro j
      have hj0 : L (c j) = 0 := (b j).2
      have hj := congrArg (fun z : Fin 3 → ℝ => z 2) hj0
      have hj' : MvPolynomial.coeff m01 (relationPoly u (c j)) = 0 := by
        simpa [L, affineCoeffMap] using hj
      simpa [q] using hj'
    let relKer : (LinearMap.ker L) →ₗ[ℝ] Poly := {
      toFun := fun x => relationPoly u (x : Fin 4 → ℝ)
      map_add' x y := by
        simp [relationPoly, Fin.sum_univ_four, add_smul, add_assoc, add_left_comm]
      map_smul' a x := by
        simp [relationPoly, Fin.sum_univ_four, smul_smul]
    }
    have hrelKerBot : LinearMap.ker relKer = ⊥ := by
      ext x
      constructor
      · intro hx
        rw [Submodule.mem_bot]
        have hrelInj : Function.Injective rel := LinearMap.ker_eq_bot.mp hrelker
        have hxrel : rel x.1 = 0 := by
          simpa [rel, relationPolyLin, relKer] using hx
        have hx0 : x.1 = 0 := by
          have hxrel0 : rel x.1 = rel 0 := by
            simpa [rel, relationPolyLin, relationPoly, Fin.sum_univ_four] using hxrel
          exact hrelInj hxrel0
        exact Subtype.ext hx0
      · intro hx
        rw [Submodule.mem_bot] at hx
        subst x
        simp [relKer]
    have hqind : LinearIndependent ℝ q := by
      simpa [q, c, relKer, rel] using b.linearIndependent.map' relKer hrelKerBot
    let A : Matrix (Fin 3) (Fin 3) ℝ := homCoeffMatrix q
    have hA : ∀ j : Fin 3, q j = ∑ k : Fin 3, A j k • homQuadBasis k := by
      intro j
      rw [homogeneousQuadratic_eq (hq j) (h00 j) (h10 j) (h01 j)]
      rw [sum_homCoeffMatrix_basis]
    have hdet : A.det ≠ 0 := det_ne_zero_of_homCoeffMatrix hq h00 h10 h01 hqind
    exact residual_eq_zero_of_relations_x0_homQuadBasis_det
      (B := B) (u := u) hu h0
      (c := c) (A := A)
      (hc := by
        intro j
        exact (hc j).trans (hA j))
      hdet hp hsocp
  · have hnebot : LinearMap.ker rel ≠ ⊥ := hrelker
    rcases (Submodule.ne_bot_iff _).mp hnebot with ⟨c, hc_mem, hc_ne⟩
    have hzero : relationPoly u c = 0 := by
      simp [rel, relationPolyLin, relationPoly] at hc_mem
      simpa using hc_mem
    exact residual_eq_zero_of_constant_relation
      (B := B) (u := u) hu hzero hc_ne hp hsocp
