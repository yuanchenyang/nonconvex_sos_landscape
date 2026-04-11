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

/-- Map an exact scalar relation through an algebra equivalence coordinatewise on
the factor tuple. -/
private theorem relation_map
    (φ : Poly →ₐ[ℝ] Poly)
    {u : RankFourVec} {c : Fin 4 → ℝ} {r : Poly}
    (hc : ∑ i : Fin 4, c i • u i = r) :
    ∑ i : Fin 4, c i • mapVec φ u i = φ r := by
  have hmap := congrArg φ hc
  simpa [mapVec, Fin.sum_univ_four] using hmap

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

private theorem coeff_m00_sq (q : Poly) :
    MvPolynomial.coeff m00 (q ^ 2) = (MvPolynomial.coeff m00 q) ^ 2 := by
  change MvPolynomial.constantCoeff (q ^ 2) = (MvPolynomial.constantCoeff q) ^ 2
  rw [pow_two, RingHom.map_mul]
  ring

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

theorem quartic_in_image_of_relations_x0_onePlusAX0sqBX1sq_x0x1_x1sq
    {u : RankFourVec}
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {a b : ℝ}
    (ha : a ≠ 0)
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = (1 : Poly) + a • (x0 ^ 2 : Poly) + b • (x1 ^ 2 : Poly))
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 * x1)
    (h3 : ∑ i : Fin 4, c3 i • u i = x1 ^ 2)
    {p : Poly} (hp : IsQuartic p) :
    InAdmissibleImage u p := by
  classical
  have honeImg : InAdmissibleImage u (1 : Poly) := by
    have himg1 :
        InAdmissibleImage u
          (((1 : Poly) + a • (x0 ^ 2 : Poly) + b • (x1 ^ 2 : Poly)) *
            ((MvPolynomial.C 1 * x0 ^ 0) * x1 ^ 0)) := by
      exact inAdmissibleImage_of_relation_mul_low
        (u := u) (c := c1)
        (r := (1 : Poly) + a • (x0 ^ 2 : Poly) + b • (x1 ^ 2 : Poly))
        (q := (MvPolynomial.C 1 * x0 ^ 0) * x1 ^ 0)
        h1 (isQuadratic_C_mul_pow_pow 1 0 0 (by omega))
    have himg0 :
        InAdmissibleImage u
          (x0 * ((MvPolynomial.C (-a) * x0 ^ 1) * x1 ^ 0)) := by
      exact inAdmissibleImage_of_relation_mul_low
        (u := u) (c := c0) (r := x0)
        (q := (MvPolynomial.C (-a) * x0 ^ 1) * x1 ^ 0)
        h0 (isQuadratic_C_mul_pow_pow (-a) 1 0 (by omega))
    have himg3 :
        InAdmissibleImage u
          ((x1 ^ 2 : Poly) * ((MvPolynomial.C (-b) * x0 ^ 0) * x1 ^ 0)) := by
      exact inAdmissibleImage_of_relation_mul_low
        (u := u) (c := c3) (r := x1 ^ 2)
        (q := (MvPolynomial.C (-b) * x0 ^ 0) * x1 ^ 0)
        h3 (isQuadratic_C_mul_pow_pow (-b) 0 0 (by omega))
    have hEq :
        (((1 : Poly) + a • (x0 ^ 2 : Poly) + b • (x1 ^ 2 : Poly)) *
            ((MvPolynomial.C 1 * x0 ^ 0) * x1 ^ 0)) +
          (x0 * ((MvPolynomial.C (-a) * x0 ^ 1) * x1 ^ 0) +
            (x1 ^ 2 : Poly) * ((MvPolynomial.C (-b) * x0 ^ 0) * x1 ^ 0)) =
          (1 : Poly) := by
      simp [MvPolynomial.smul_eq_C_mul]
      ring
    rw [← hEq]
    exact inAdmissibleImage_add u himg1 (inAdmissibleImage_add u himg0 himg3)
  have hx1Img : InAdmissibleImage u x1 := by
    have himg1 :
        InAdmissibleImage u
          (((1 : Poly) + a • (x0 ^ 2 : Poly) + b • (x1 ^ 2 : Poly)) *
            ((MvPolynomial.C 1 * x0 ^ 0) * x1 ^ 1)) := by
      exact inAdmissibleImage_of_relation_mul_low
        (u := u) (c := c1)
        (r := (1 : Poly) + a • (x0 ^ 2 : Poly) + b • (x1 ^ 2 : Poly))
        (q := (MvPolynomial.C 1 * x0 ^ 0) * x1 ^ 1)
        h1 (isQuadratic_C_mul_pow_pow 1 0 1 (by omega))
    have himg2 :
        InAdmissibleImage u
          ((x0 * x1 : Poly) * ((MvPolynomial.C (-a) * x0 ^ 1) * x1 ^ 0)) := by
      exact inAdmissibleImage_of_relation_mul_low
        (u := u) (c := c2) (r := (x0 * x1 : Poly))
        (q := (MvPolynomial.C (-a) * x0 ^ 1) * x1 ^ 0)
        h2 (isQuadratic_C_mul_pow_pow (-a) 1 0 (by omega))
    have himg3 :
        InAdmissibleImage u
          ((x1 ^ 2 : Poly) * ((MvPolynomial.C (-b) * x0 ^ 0) * x1 ^ 1)) := by
      exact inAdmissibleImage_of_relation_mul_low
        (u := u) (c := c3) (r := x1 ^ 2)
        (q := (MvPolynomial.C (-b) * x0 ^ 0) * x1 ^ 1)
        h3 (isQuadratic_C_mul_pow_pow (-b) 0 1 (by omega))
    have hEq :
        (((1 : Poly) + a • (x0 ^ 2 : Poly) + b • (x1 ^ 2 : Poly)) *
            ((MvPolynomial.C 1 * x0 ^ 0) * x1 ^ 1)) +
          ((x0 * x1 : Poly) * ((MvPolynomial.C (-a) * x0 ^ 1) * x1 ^ 0) +
            (x1 ^ 2 : Poly) * ((MvPolynomial.C (-b) * x0 ^ 0) * x1 ^ 1)) =
          x1 := by
      simp [MvPolynomial.smul_eq_C_mul]
      ring
    rw [← hEq]
    exact inAdmissibleImage_add u himg1 (inAdmissibleImage_add u himg2 himg3)
  let monomialImage : ∀ (s : Fin 2 →₀ ℕ) (r : ℝ),
      s.sum (fun _ e => e) ≤ 4 →
      InAdmissibleImage u (MvPolynomial.monomial s r) := by
    intro s r hdeg
    let e0 := s 0
    let e1 := s 1
    have hsum : s.sum (fun _ e => e) = s 0 + s 1 := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
    have hs : e0 + e1 ≤ 4 := by
      simpa [e0, e1, hsum] using hdeg
    by_cases he2 : 2 ≤ e1
    · have hq :
          IsQuadratic ((MvPolynomial.C r * x0 ^ e0) * x1 ^ (e1 - 2)) := by
        exact isQuadratic_C_mul_pow_pow r e0 (e1 - 2) (by omega)
      have hmul :
          (x1 ^ 2 : Poly) * ((MvPolynomial.C r * x0 ^ e0) * x1 ^ (e1 - 2)) =
            (MvPolynomial.C r * x0 ^ e0) * x1 ^ e1 := by
        calc
          (x1 ^ 2 : Poly) * ((MvPolynomial.C r * x0 ^ e0) * x1 ^ (e1 - 2))
              = MvPolynomial.C r * x0 ^ e0 * (x1 ^ 2 * x1 ^ (e1 - 2)) := by
                  ring_nf
          _ = (MvPolynomial.C r * x0 ^ e0) * x1 ^ e1 := by
                rw [← pow_add, Nat.add_sub_of_le he2]
      simpa [monomial_fin2_eq, e0, e1, hmul] using
        (inAdmissibleImage_of_relation_mul_low
          (u := u) (c := c3) (r := x1 ^ 2)
          (q := (MvPolynomial.C r * x0 ^ e0) * x1 ^ (e1 - 2))
          h3 hq)
    · have he1le : e1 ≤ 1 := by omega
      by_cases he1 : e1 = 1
      · by_cases hx0 : e0 = 0
        · rw [monomial_fin2_eq]
          have himg : InAdmissibleImage u (r • x1) := inAdmissibleImage_smul u r hx1Img
          simpa [MvPolynomial.smul_eq_C_mul, e0, e1, hx0, he1, x1,
            mul_comm, mul_left_comm, mul_assoc] using himg
        · have hx1 : 1 ≤ e0 := by omega
          have hq :
              IsQuadratic (MvPolynomial.C r * x0 ^ (e0 - 1)) := by
            simpa using isQuadratic_C_mul_pow_pow r (e0 - 1) 0 (by omega)
          have hmul :
              (x0 * x1 : Poly) * (MvPolynomial.C r * x0 ^ (e0 - 1)) =
                (MvPolynomial.C r * x0 ^ e0) * x1 := by
            calc
              (x0 * x1 : Poly) * (MvPolynomial.C r * x0 ^ (e0 - 1))
                  = MvPolynomial.C r * (x0 * x0 ^ (e0 - 1)) * x1 := by
                      ring_nf
              _ = (MvPolynomial.C r * x0 ^ e0) * x1 := by
                    rw [show x0 * x0 ^ (e0 - 1) = x0 ^ e0 by
                      simpa [Nat.sub_add_cancel hx1] using (pow_succ' x0 (e0 - 1)).symm]
          exact
            (by
              simpa [monomial_fin2_eq, e0, e1, he1, hmul] using
              (inAdmissibleImage_of_relation_mul_low
                (u := u) (c := c2) (r := (x0 * x1 : Poly))
                (q := MvPolynomial.C r * x0 ^ (e0 - 1))
                h2 hq))
      · have he0 : e1 = 0 := by omega
        by_cases hx0 : e0 = 0
        · rw [monomial_fin2_eq]
          have himg : InAdmissibleImage u (r • (1 : Poly)) := inAdmissibleImage_smul u r honeImg
          simpa [MvPolynomial.smul_eq_C_mul, e0, e1, hx0, he0] using himg
        · by_cases hx1 : e0 = 1
          · have himg : InAdmissibleImage u (x0 * MvPolynomial.C r) := by
              exact inAdmissibleImage_of_relation_mul_low
                (u := u) (c := c0) (r := x0)
                (q := (MvPolynomial.C r)) h0 (by
                  change ((MvPolynomial.C r : Poly).totalDegree ≤ 2)
                  simp)
            have hmul : x0 * MvPolynomial.C r = MvPolynomial.C r * x0 := by
              ring_nf
            simpa [monomial_fin2_eq, e0, e1, hx1, he0, hmul] using himg
          · by_cases hx2 : e0 = 2
            · have himg1 :
                InAdmissibleImage u
                  (((1 : Poly) + a • (x0 ^ 2 : Poly) + b • (x1 ^ 2 : Poly)) *
                    ((MvPolynomial.C (r / a) * x0 ^ 0) * x1 ^ 0)) := by
                exact inAdmissibleImage_of_relation_mul_low
                  (u := u) (c := c1)
                  (r := (1 : Poly) + a • (x0 ^ 2 : Poly) + b • (x1 ^ 2 : Poly))
                  (q := (MvPolynomial.C (r / a) * x0 ^ 0) * x1 ^ 0)
                  h1 (isQuadratic_C_mul_pow_pow (r / a) 0 0 (by omega))
              have himgConst : InAdmissibleImage u (((-r / a) : ℝ) • (1 : Poly)) := by
                exact inAdmissibleImage_smul u (-r / a) honeImg
              have himg3 :
                  InAdmissibleImage u
                    ((x1 ^ 2 : Poly) * ((MvPolynomial.C (-(b * (r / a))) * x0 ^ 0) * x1 ^ 0)) := by
                exact inAdmissibleImage_of_relation_mul_low
                  (u := u) (c := c3) (r := x1 ^ 2)
                  (q := (MvPolynomial.C (-(b * (r / a))) * x0 ^ 0) * x1 ^ 0)
                  h3 (isQuadratic_C_mul_pow_pow (-(b * (r / a))) 0 0 (by omega))
              have hEq :
                  (((1 : Poly) + a • (x0 ^ 2 : Poly) + b • (x1 ^ 2 : Poly)) *
                      ((MvPolynomial.C (r / a) * x0 ^ 0) * x1 ^ 0)) +
                    (((-r / a) : ℝ) • (1 : Poly) +
                      (x1 ^ 2 : Poly) * ((MvPolynomial.C (-(b * (r / a))) * x0 ^ 0) * x1 ^ 0)) =
                    (MvPolynomial.C r * x0 ^ 2 : Poly) := by
                have hEq1 :
                    (((1 : Poly) + a • (x0 ^ 2 : Poly) + b • (x1 ^ 2 : Poly)) *
                        ((MvPolynomial.C (r / a) * x0 ^ 0) * x1 ^ 0)) +
                      (((-r / a) : ℝ) • (1 : Poly) +
                        (x1 ^ 2 : Poly) * ((MvPolynomial.C (-(b * (r / a))) * x0 ^ 0) * x1 ^ 0)) =
                      MvPolynomial.C a * x0 ^ 2 * MvPolynomial.C (r * a⁻¹) := by
                  simp [MvPolynomial.smul_eq_C_mul, div_eq_mul_inv]
                  field_simp [ha]
                  rw [← MvPolynomial.C_mul]
                  ring_nf
                have hEq2 :
                    MvPolynomial.C a * x0 ^ 2 * MvPolynomial.C (r * a⁻¹) =
                      MvPolynomial.C r * x0 ^ 2 := by
                  calc
                    MvPolynomial.C a * x0 ^ 2 * MvPolynomial.C (r * a⁻¹)
                        = x0 ^ 2 * (MvPolynomial.C a * MvPolynomial.C (r * a⁻¹)) := by
                            ring_nf
                    _ = x0 ^ 2 * MvPolynomial.C (a * (r * a⁻¹)) := by
                          rw [← MvPolynomial.C_mul]
                    _ = x0 ^ 2 * MvPolynomial.C r := by
                          congr 1
                          field_simp [ha]
                    _ = MvPolynomial.C r * x0 ^ 2 := by
                          ring_nf
                exact hEq1.trans hEq2
              have himg :
                  InAdmissibleImage u (MvPolynomial.C r * x0 ^ 2 : Poly) := by
                exact hEq.symm ▸
                  inAdmissibleImage_add u himg1 (inAdmissibleImage_add u himgConst himg3)
              simpa [monomial_fin2_eq, e0, e1, hx2, he0] using himg
            · have hx3 : e0 = 3 ∨ e0 = 4 := by omega
              cases hx3 with
              | inl hx3 =>
                  have hq :
                      IsQuadratic (MvPolynomial.C r * x0 ^ 2) := by
                    simpa using isQuadratic_C_mul_pow_pow r 2 0 (by omega)
                  have hmul :
                      x0 * (MvPolynomial.C r * x0 ^ 2) =
                        MvPolynomial.C r * x0 ^ 3 := by
                    ring_nf
                  simpa [monomial_fin2_eq, e0, e1, hx3, he0, hmul] using
                    (inAdmissibleImage_of_relation_mul_low
                      (u := u) (c := c0) (r := x0)
                      (q := MvPolynomial.C r * x0 ^ 2)
                      h0 hq)
              | inr hx4 =>
                  have himg1 :
                      InAdmissibleImage u
                        (((1 : Poly) + a • (x0 ^ 2 : Poly) + b • (x1 ^ 2 : Poly)) *
                          ((MvPolynomial.C (r / a) * x0 ^ 2) * x1 ^ 0)) := by
                    exact inAdmissibleImage_of_relation_mul_low
                      (u := u) (c := c1)
                      (r := (1 : Poly) + a • (x0 ^ 2 : Poly) + b • (x1 ^ 2 : Poly))
                      (q := (MvPolynomial.C (r / a) * x0 ^ 2) * x1 ^ 0)
                      h1 (isQuadratic_C_mul_pow_pow (r / a) 2 0 (by omega))
                  have himg0 :
                      InAdmissibleImage u
                        (x0 * ((MvPolynomial.C (-(r / a)) * x0 ^ 1) * x1 ^ 0)) := by
                    exact inAdmissibleImage_of_relation_mul_low
                      (u := u) (c := c0) (r := x0)
                      (q := (MvPolynomial.C (-(r / a)) * x0 ^ 1) * x1 ^ 0)
                      h0 (isQuadratic_C_mul_pow_pow (-(r / a)) 1 0 (by omega))
                  have himg3 :
                      InAdmissibleImage u
                        ((x1 ^ 2 : Poly) * ((MvPolynomial.C (-(b * (r / a))) * x0 ^ 2) * x1 ^ 0)) := by
                    exact inAdmissibleImage_of_relation_mul_low
                      (u := u) (c := c3) (r := x1 ^ 2)
                      (q := (MvPolynomial.C (-(b * (r / a))) * x0 ^ 2) * x1 ^ 0)
                      h3 (isQuadratic_C_mul_pow_pow (-(b * (r / a))) 2 0 (by omega))
                  have hEq :
                      (((1 : Poly) + a • (x0 ^ 2 : Poly) + b • (x1 ^ 2 : Poly)) *
                          ((MvPolynomial.C (r / a) * x0 ^ 2) * x1 ^ 0)) +
                        (x0 * ((MvPolynomial.C (-(r / a)) * x0 ^ 1) * x1 ^ 0) +
                          (x1 ^ 2 : Poly) * ((MvPolynomial.C (-(b * (r / a))) * x0 ^ 2) * x1 ^ 0)) =
                        (MvPolynomial.C r * x0 ^ 4 : Poly) := by
                    have hEq1 :
                        (((1 : Poly) + a • (x0 ^ 2 : Poly) + b • (x1 ^ 2 : Poly)) *
                            ((MvPolynomial.C (r / a) * x0 ^ 2) * x1 ^ 0)) +
                          (x0 * ((MvPolynomial.C (-(r / a)) * x0 ^ 1) * x1 ^ 0) +
                            (x1 ^ 2 : Poly) * ((MvPolynomial.C (-(b * (r / a))) * x0 ^ 2) * x1 ^ 0)) =
                          MvPolynomial.C a * x0 ^ 4 * MvPolynomial.C (r * a⁻¹) := by
                      simp [MvPolynomial.smul_eq_C_mul, div_eq_mul_inv]
                      field_simp [ha]
                      rw [← MvPolynomial.C_mul]
                      ring_nf
                    have hEq2 :
                        MvPolynomial.C a * x0 ^ 4 * MvPolynomial.C (r * a⁻¹) =
                          MvPolynomial.C r * x0 ^ 4 := by
                      calc
                        MvPolynomial.C a * x0 ^ 4 * MvPolynomial.C (r * a⁻¹)
                            = x0 ^ 4 * (MvPolynomial.C a * MvPolynomial.C (r * a⁻¹)) := by
                                ring_nf
                        _ = x0 ^ 4 * MvPolynomial.C (a * (r * a⁻¹)) := by
                              rw [← MvPolynomial.C_mul]
                        _ = x0 ^ 4 * MvPolynomial.C r := by
                              congr 1
                              field_simp [ha]
                        _ = MvPolynomial.C r * x0 ^ 4 := by
                              ring_nf
                    exact hEq1.trans hEq2
                  have himg :
                      InAdmissibleImage u (MvPolynomial.C r * x0 ^ 4 : Poly) := by
                    exact hEq.symm ▸
                      inAdmissibleImage_add u himg1 (inAdmissibleImage_add u himg0 himg3)
                  simpa [monomial_fin2_eq, e0, e1, hx4, he0] using himg
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

theorem residual_eq_zero_of_relations_x0_onePlusAX0sqBX1sq_x0x1_x1sq
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {a b : ℝ}
    (ha : a ≠ 0)
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = (1 : Poly) + a • (x0 ^ 2 : Poly) + b • (x1 ^ 2 : Poly))
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 * x1)
    (h3 : ∑ i : Fin 4, c3 i • u i = x1 ^ 2)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_in_admissible_image
    (B := B) hu hsocp
    (quartic_in_image_of_relations_x0_onePlusAX0sqBX1sq_x0x1_x1sq
      ha h0 h1 h2 h3 hp.1)

theorem quartic_in_image_of_relations_x0_onePlusAX0x1_x0sq_x1sq
    {u : RankFourVec}
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {a : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = (1 : Poly) + a • (x0 * x1 : Poly))
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 ^ 2)
    (h3 : ∑ i : Fin 4, c3 i • u i = x1 ^ 2)
    {p : Poly} (hp : IsQuartic p) :
    InAdmissibleImage u p := by
  classical
  have hx1Img : InAdmissibleImage u x1 := by
    have himg1 :
        InAdmissibleImage u
          (((1 : Poly) + a • (x0 * x1 : Poly)) * x1) := by
      exact inAdmissibleImage_of_relation_mul_low
        (u := u) (c := c1)
        (r := (1 : Poly) + a • (x0 * x1 : Poly))
        (q := x1) h1 <| by
          change (x1 : Poly).totalDegree ≤ 2
          simp [x1]
    have himg2 :
        InAdmissibleImage u (x0 * (a • (x1 ^ 2 : Poly))) := by
      exact inAdmissibleImage_of_relation_mul_low
        (u := u) (c := c0) (r := x0)
        (q := a • (x1 ^ 2 : Poly)) h0 <| by
          exact (MvPolynomial.totalDegree_smul_le a (x1 ^ 2 : Poly)).trans (by simp [x1])
    have hEq :
        ((1 : Poly) + a • (x0 * x1 : Poly)) * x1 - x0 * (a • (x1 ^ 2 : Poly)) = x1 := by
      simp [MvPolynomial.smul_eq_C_mul]
      ring
    exact hEq ▸ inAdmissibleImage_sub u himg1 himg2
  have hx0x1Img : InAdmissibleImage u (x0 * x1 : Poly) := by
    exact inAdmissibleImage_of_relation_mul_low
      (u := u) (c := c0) (r := x0)
      (q := x1) h0 <| by
        change (x1 : Poly).totalDegree ≤ 2
        simp [x1]
  have honeImg : InAdmissibleImage u (1 : Poly) := by
    have himg1 :
        InAdmissibleImage u ((1 : Poly) + a • (x0 * x1 : Poly)) := by
      simpa using inAdmissibleImage_of_relation_mul_low
        (u := u) (c := c1)
        (r := (1 : Poly) + a • (x0 * x1 : Poly))
        (q := (1 : Poly)) h1 <| by
          change ((1 : Poly).totalDegree ≤ 2)
          simp
    have himg2 : InAdmissibleImage u (a • (x0 * x1 : Poly)) := by
      exact inAdmissibleImage_smul u a hx0x1Img
    have hEq :
        ((1 : Poly) + a • (x0 * x1 : Poly)) - a • (x0 * x1 : Poly) = (1 : Poly) := by
      simp
    exact hEq ▸ inAdmissibleImage_sub u himg1 himg2
  let monomialImage : ∀ (s : Fin 2 →₀ ℕ) (r : ℝ),
      s.sum (fun _ e => e) ≤ 4 →
      InAdmissibleImage u (MvPolynomial.monomial s r) := by
    intro s r hdeg
    let e0 := s 0
    let e1 := s 1
    have hsum : s.sum (fun _ e => e) = s 0 + s 1 := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
    have hs : e0 + e1 ≤ 4 := by
      simpa [e0, e1, hsum] using hdeg
    by_cases he2 : 2 ≤ e1
    · have hq :
          IsQuadratic ((MvPolynomial.C r * x0 ^ e0) * x1 ^ (e1 - 2)) := by
        exact isQuadratic_C_mul_pow_pow r e0 (e1 - 2) (by omega)
      have hmul :
          (x1 ^ 2 : Poly) * ((MvPolynomial.C r * x0 ^ e0) * x1 ^ (e1 - 2)) =
            (MvPolynomial.C r * x0 ^ e0) * x1 ^ e1 := by
        calc
          (x1 ^ 2 : Poly) * ((MvPolynomial.C r * x0 ^ e0) * x1 ^ (e1 - 2))
              = MvPolynomial.C r * x0 ^ e0 * (x1 ^ 2 * x1 ^ (e1 - 2)) := by
                  ring_nf
          _ = (MvPolynomial.C r * x0 ^ e0) * x1 ^ e1 := by
                rw [← pow_add, Nat.add_sub_of_le he2]
      simpa [monomial_fin2_eq, e0, e1, hmul] using
        (inAdmissibleImage_of_relation_mul_low
          (u := u) (c := c3) (r := x1 ^ 2)
          (q := (MvPolynomial.C r * x0 ^ e0) * x1 ^ (e1 - 2))
          h3 hq)
    · have he1le : e1 ≤ 1 := by omega
      by_cases he1 : e1 = 1
      · by_cases hx0 : e0 = 0
        · rw [monomial_fin2_eq]
          have himg : InAdmissibleImage u (r • x1) := inAdmissibleImage_smul u r hx1Img
          simpa [MvPolynomial.smul_eq_C_mul, e0, e1, hx0, he1, x1,
            mul_comm, mul_left_comm, mul_assoc] using himg
        · by_cases hx1 : e0 = 1
          · have himg :
                InAdmissibleImage u (x0 * (MvPolynomial.C r * x1)) := by
              exact inAdmissibleImage_of_relation_mul_low
                (u := u) (c := c0) (r := x0)
                (q := MvPolynomial.C r * x1) h0 <| by
                  simpa using isQuadratic_C_mul_pow_pow r 0 1 (by omega)
            have hmul :
                x0 * (MvPolynomial.C r * x1) = (MvPolynomial.C r * x0) * x1 := by
              ring_nf
            simpa [monomial_fin2_eq, e0, e1, hx1, he1, hmul] using himg
          · have hx2 : 2 ≤ e0 := by omega
            have hq :
                IsQuadratic ((MvPolynomial.C r * x0 ^ (e0 - 2)) * x1) := by
              simpa [pow_one] using isQuadratic_C_mul_pow_pow r (e0 - 2) 1 (by omega)
            have hmul :
                x0 ^ 2 * ((MvPolynomial.C r * x0 ^ (e0 - 2)) * x1) =
                  (MvPolynomial.C r * x0 ^ e0) * x1 := by
              calc
                x0 ^ 2 * ((MvPolynomial.C r * x0 ^ (e0 - 2)) * x1)
                    = MvPolynomial.C r * (x0 ^ 2 * x0 ^ (e0 - 2)) * x1 := by
                        ring_nf
                _ = (MvPolynomial.C r * x0 ^ e0) * x1 := by
                      rw [← pow_add, Nat.add_sub_of_le hx2]
            simpa [monomial_fin2_eq, e0, e1, he1, hmul] using
              (inAdmissibleImage_of_relation_mul_low
                (u := u) (c := c2) (r := x0 ^ 2)
                (q := (MvPolynomial.C r * x0 ^ (e0 - 2)) * x1)
                h2 hq)
      · have he0 : e1 = 0 := by omega
        by_cases hx0 : e0 = 0
        · rw [monomial_fin2_eq]
          have himg : InAdmissibleImage u (r • (1 : Poly)) := inAdmissibleImage_smul u r honeImg
          simpa [MvPolynomial.smul_eq_C_mul, e0, e1, hx0, he0] using himg
        · by_cases hx1 : e0 = 1
          · have himg : InAdmissibleImage u (x0 * MvPolynomial.C r) := by
              exact inAdmissibleImage_of_relation_mul_low
                (u := u) (c := c0) (r := x0)
                (q := (MvPolynomial.C r)) h0 <| by
                  change ((MvPolynomial.C r : Poly).totalDegree ≤ 2)
                  simp
            have hmul : x0 * MvPolynomial.C r = MvPolynomial.C r * x0 := by
              ring_nf
            simpa [monomial_fin2_eq, e0, e1, hx1, he0, hmul] using himg
          · have hx2 : 2 ≤ e0 := by omega
            have hq :
                IsQuadratic (MvPolynomial.C r * x0 ^ (e0 - 2)) := by
              simpa using isQuadratic_C_mul_pow_pow r (e0 - 2) 0 (by omega)
            have hmul :
                x0 ^ 2 * (MvPolynomial.C r * x0 ^ (e0 - 2)) =
                  MvPolynomial.C r * x0 ^ e0 := by
              calc
                x0 ^ 2 * (MvPolynomial.C r * x0 ^ (e0 - 2))
                    = MvPolynomial.C r * (x0 ^ 2 * x0 ^ (e0 - 2)) := by
                        ring_nf
                _ = MvPolynomial.C r * x0 ^ e0 := by
                      rw [← pow_add, Nat.add_sub_of_le hx2]
            simpa [monomial_fin2_eq, e0, e1, he0, hmul] using
              (inAdmissibleImage_of_relation_mul_low
                (u := u) (c := c2) (r := x0 ^ 2)
                (q := MvPolynomial.C r * x0 ^ (e0 - 2))
                h2 hq)
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
        exact monomialImage s (MvPolynomial.coeff s p) hsdeg
      · intro t ht
        exact hsub t (by simp [ht])
  exact hP (fun s hs => hs)

theorem residual_eq_zero_of_relations_x0_onePlusAX0x1_x0sq_x1sq
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {a : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = (1 : Poly) + a • (x0 * x1 : Poly))
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 ^ 2)
    (h3 : ∑ i : Fin 4, c3 i • u i = x1 ^ 2)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_in_admissible_image
    (B := B) hu hsocp
    (quartic_in_image_of_relations_x0_onePlusAX0x1_x0sq_x1sq
      h0 h1 h2 h3 hp.1)

theorem residual_eq_zero_of_equiv_relations_x0_onePlusAX0x1_x0sq_x1sq
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    {a : ℝ}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = (1 : Poly) + a • (x0 * x1 : Poly))
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = x0 ^ 2)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = x1 ^ 2) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e)
      (heQuad := fun {_} hpq => heQuad hpq)
      (heQuartic := fun {_} hpq => heQuartic hpq)
      hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_x0_onePlusAX0x1_x0sq_x1sq
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0 h1 h2 h3 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_x0_onePlusAX0x1_x0sq_x1sqPlane
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {a r s t w : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = (1 : Poly) + a • (x0 * x1 : Poly))
    (h2 : ∑ i : Fin 4, c2 i • u i = r • (x0 ^ 2 : Poly) + s • (x1 ^ 2 : Poly))
    (h3 : ∑ i : Fin 4, c3 i • u i = t • (x0 ^ 2 : Poly) + w • (x1 ^ 2 : Poly))
    (hdet : r * w - s * t ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let det : ℝ := r * w - s * t
  have hdet0 : det ≠ 0 := by
    simpa [det] using hdet
  let c2' : Fin 4 → ℝ := fun i => (w / det) * c2 i + (-s / det) * c3 i
  let c3' : Fin 4 → ℝ := fun i => (-t / det) * c2 i + (r / det) * c3 i
  have hcoeff20 : (w / det) * r + (-s / det) * t = 1 := by
    field_simp [det, hdet0]
    ring
  have hcoeff21 : (w / det) * s + (-s / det) * w = 0 := by
    field_simp [det, hdet0]
    ring
  have hcoeff30 : (-t / det) * r + (r / det) * t = 0 := by
    field_simp [det, hdet0]
    ring
  have hcoeff31 : (-t / det) * s + (r / det) * w = 1 := by
    field_simp [det, hdet0]
    ring
  have h2' : ∑ i : Fin 4, c2' i • u i = x0 ^ 2 := by
    change relationPoly u c2' = x0 ^ 2
    calc
      relationPoly u c2'
          = relationPoly u ((w / det) • c2) + relationPoly u ((-s / det) • c3) := by
              rw [show c2' = (w / det) • c2 + (-s / det) • c3 by
                funext i
                simp [c2']
              , relationPoly_add]
      _ = (w / det) • relationPoly u c2 + (-s / det) • relationPoly u c3 := by
            rw [relationPoly_smul, relationPoly_smul]
      _ = (w / det) • (r • (x0 ^ 2 : Poly) + s • (x1 ^ 2 : Poly)) +
            (-s / det) • (t • (x0 ^ 2 : Poly) + w • (x1 ^ 2 : Poly)) := by
              rw [show relationPoly u c2 = ∑ i : Fin 4, c2 i • u i by rfl,
                show relationPoly u c3 = ∑ i : Fin 4, c3 i • u i by rfl,
                h2, h3]
      _ = ((w / det) * r + (-s / det) * t) • (x0 ^ 2 : Poly) +
            ((w / det) * s + (-s / det) * w) • (x1 ^ 2 : Poly) := by
              simp [smul_add, smul_smul, add_smul, add_assoc, add_left_comm, mul_comm]
      _ = x0 ^ 2 := by
            rw [hcoeff20, hcoeff21]
            simp
  have h3' : ∑ i : Fin 4, c3' i • u i = x1 ^ 2 := by
    change relationPoly u c3' = x1 ^ 2
    calc
      relationPoly u c3'
          = relationPoly u ((-t / det) • c2) + relationPoly u ((r / det) • c3) := by
              rw [show c3' = (-t / det) • c2 + (r / det) • c3 by
                funext i
                simp [c3']
              , relationPoly_add]
      _ = (-t / det) • relationPoly u c2 + (r / det) • relationPoly u c3 := by
            rw [relationPoly_smul, relationPoly_smul]
      _ = (-t / det) • (r • (x0 ^ 2 : Poly) + s • (x1 ^ 2 : Poly)) +
            (r / det) • (t • (x0 ^ 2 : Poly) + w • (x1 ^ 2 : Poly)) := by
              rw [show relationPoly u c2 = ∑ i : Fin 4, c2 i • u i by rfl,
                show relationPoly u c3 = ∑ i : Fin 4, c3 i • u i by rfl,
                h2, h3]
      _ = ((-t / det) * r + (r / det) * t) • (x0 ^ 2 : Poly) +
            ((-t / det) * s + (r / det) * w) • (x1 ^ 2 : Poly) := by
              simp [smul_add, smul_smul, add_smul, add_assoc, add_left_comm, add_comm, mul_comm]
      _ = x1 ^ 2 := by
            rw [hcoeff30, hcoeff31]
            simp
  exact residual_eq_zero_of_relations_x0_onePlusAX0x1_x0sq_x1sq
    (B := B) (u := u) hu h0 h1 h2' h3' hp hsocp

theorem residual_eq_zero_of_equiv_relations_x0_onePlusAX0x1_x0sq_x1sqPlane
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    {a r s t w : ℝ}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = (1 : Poly) + a • (x0 * x1 : Poly))
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = r • (x0 ^ 2 : Poly) + s • (x1 ^ 2 : Poly))
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = t • (x0 ^ 2 : Poly) + w • (x1 ^ 2 : Poly))
    (hdet : r * w - s * t ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e)
      (heQuad := fun {_} hpq => heQuad hpq)
      (heQuartic := fun {_} hpq => heQuartic hpq)
      hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_x0_onePlusAX0x1_x0sq_x1sqPlane
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0 h1 h2 h3 hdet hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

/-- Linearity of `A` in the right slot. -/
private theorem A_add_right_local (u v w : RankFourVec) :
    A u (v + w) = A u v + A u w := by
  simp [A, Finset.sum_add_distrib, mul_add]

private def affineDimOneCrossKer
    (c0 c2 : Fin 4 → ℝ) (t : ℝ) : RankFourVec :=
  relationDirection (-c0) (t • x0) + relationDirection c2 (t • (1 : Poly))

private theorem affineDimOneCrossKer_admissible
    (c0 c2 : Fin 4 → ℝ) (t : ℝ) :
    IsAdmissibleDirection (affineDimOneCrossKer c0 c2 t) := by
  refine isAdmissibleDirection_add
    (relationDirection_admissible (-c0)
      ((MvPolynomial.totalDegree_smul_le t x0).trans (by simp [x0])))
    (relationDirection_admissible c2
      ((MvPolynomial.totalDegree_smul_le t (1 : Poly)).trans (by simp)))

private theorem affineDimOneCrossKer_inKer
    {u : RankFourVec} {c0 c2 : Fin 4 → ℝ} {t : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 ^ 2) :
    InAdmissibleKer u (affineDimOneCrossKer c0 c2 t) := by
  refine ⟨affineDimOneCrossKer_admissible c0 c2 t, ?_⟩
  rw [affineDimOneCrossKer, A_add_right_local, A_relationDirection, A_relationDirection]
  simp [Pi.neg_apply, h0, h2]
  ring_nf

private theorem coeff_m00_sigma_affineDimOneCrossKer
    (c0 c2 : Fin 4 → ℝ) (t : ℝ) :
    MvPolynomial.coeff m00 (sigma (affineDimOneCrossKer c0 c2 t)) =
      (∑ i : Fin 4, (c2 i) ^ 2) * t ^ 2 := by
  have hcoord : ∀ i : Fin 4,
      MvPolynomial.coeff m00 ((affineDimOneCrossKer c0 c2 t i) ^ 2) = ((c2 i) * t) ^ 2 := by
    intro i
    rw [coeff_m00_sq]
    rw [affineDimOneCrossKer]
    simp [relationDirection, m00, x0]
  rw [sigma, Fin.sum_univ_four]
  repeat' rw [MvPolynomial.coeff_add]
  rw [hcoord 0, hcoord 1, hcoord 2, hcoord 3]
  rw [Fin.sum_univ_four]
  ring_nf

theorem quartic_in_image_of_relations_x0_x1PlusAX0x1_x0sq_x1sq_of_coeff_m00_zero
    {u : RankFourVec}
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {a : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1 + a • (x0 * x1 : Poly))
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 ^ 2)
    (h3 : ∑ i : Fin 4, c3 i • u i = x1 ^ 2)
    {p : Poly} (hp : IsQuartic p)
    (h00 : MvPolynomial.coeff m00 p = 0) :
    InAdmissibleImage u p := by
  classical
  have hx1img : InAdmissibleImage u x1 := by
    have himg1 :
        InAdmissibleImage u ((x1 + a • (x0 * x1 : Poly)) * ((1 : Poly) - a • x0)) := by
      exact inAdmissibleImage_of_relation_mul_low
        (u := u) (c := c1) (r := x1 + a • (x0 * x1 : Poly))
        (q := (1 : Poly) - a • x0) h1 <| by
          calc
            (((1 : Poly) - a • x0) : Poly).totalDegree ≤
                max (1 : Poly).totalDegree (a • x0).totalDegree := by
                  exact MvPolynomial.totalDegree_sub _ _
            _ ≤ 2 := by
                  refine max_le ?_ ?_
                  · simp
                  · exact (MvPolynomial.totalDegree_smul_le a x0).trans (by simp [x0])
    have himg2 :
        InAdmissibleImage u ((x0 ^ 2 : Poly) * ((a ^ 2 : ℝ) • x1)) := by
      exact inAdmissibleImage_of_relation_mul_low
        (u := u) (c := c2) (r := x0 ^ 2)
        (q := (a ^ 2 : ℝ) • x1) h2 <| by
          exact (MvPolynomial.totalDegree_smul_le (a ^ 2) x1).trans (by simp [x1])
    have hEq :
        (x1 + a • (x0 * x1 : Poly)) * ((1 : Poly) - a • x0) +
            (x0 ^ 2 : Poly) * ((a ^ 2 : ℝ) • x1) = x1 := by
      simp [MvPolynomial.smul_eq_C_mul]
      ring_nf
    exact hEq ▸ inAdmissibleImage_add u himg1 himg2
  let monomialImage : ∀ (s : Fin 2 →₀ ℕ) (r : ℝ),
      s.sum (fun _ e => e) ≤ 4 →
      s ≠ m00 →
      InAdmissibleImage u (MvPolynomial.monomial s r) := by
    intro s r hdeg hne
    let e0 := s 0
    let e1 := s 1
    have hsum : s.sum (fun _ e => e) = s 0 + s 1 := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
    have hs0 : s 0 + s 1 ≤ 4 := by
      simpa [hsum] using hdeg
    have hs : e0 + e1 ≤ 4 := by
      simpa [e0, e1] using hs0
    by_cases he1zero : e1 = 0
    · have he0pos : 1 ≤ e0 := by
        by_contra he0pos
        have he00 : e0 = 0 := by omega
        apply hne
        ext i
        fin_cases i <;> simp [m00, e0, e1, he00, he1zero]
      by_cases he0small : e0 ≤ 3
      · have hq :
            IsQuadratic (MvPolynomial.C r * x0 ^ (e0 - 1)) := by
          simpa using isQuadratic_C_mul_pow_pow r (e0 - 1) 0 (by omega)
        have hmul :
            x0 * (MvPolynomial.C r * x0 ^ (e0 - 1)) =
              MvPolynomial.C r * x0 ^ e0 := by
          have hxpow : x0 * x0 ^ (e0 - 1) = x0 ^ e0 := by
            simpa [Nat.sub_add_cancel he0pos] using (pow_succ' x0 (e0 - 1)).symm
          calc
            x0 * (MvPolynomial.C r * x0 ^ (e0 - 1))
                = MvPolynomial.C r * (x0 * x0 ^ (e0 - 1)) := by
                    ring_nf
            _ = MvPolynomial.C r * x0 ^ e0 := by
                  simp [hxpow]
        simpa [monomial_fin2_eq, e0, e1, he1zero, hmul] using
          (inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c0) (r := x0)
            (q := MvPolynomial.C r * x0 ^ (e0 - 1))
            h0 hq)
      · have he0ge : 4 ≤ e0 := by omega
        have he0eq : e0 = 4 := by omega
        have hq :
            IsQuadratic (MvPolynomial.C r * x0 ^ 2) := by
          simpa using isQuadratic_C_mul_pow_pow r 2 0 (by omega)
        have hmul :
            x0 ^ 2 * (MvPolynomial.C r * x0 ^ 2) =
              MvPolynomial.C r * x0 ^ 4 := by
          calc
            x0 ^ 2 * (MvPolynomial.C r * x0 ^ 2)
                = MvPolynomial.C r * (x0 ^ 2 * x0 ^ 2) := by
                    ring_nf
            _ = MvPolynomial.C r * x0 ^ 4 := by
                  rw [← pow_add]
        simpa [monomial_fin2_eq, e0, e1, he0eq, he1zero, hmul] using
          (inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c2) (r := x0 ^ 2)
            (q := MvPolynomial.C r * x0 ^ 2)
            h2 hq)
    · have he1pos : 1 ≤ e1 := by omega
      by_cases he1one : e1 = 1
      · by_cases he0zero : e0 = 0
        · simpa [monomial_fin2_eq, e0, e1, he0zero, he1one, x1,
            MvPolynomial.smul_eq_C_mul, mul_comm] using
            inAdmissibleImage_smul u r hx1img
        · have he0pos : 1 ≤ e0 := by omega
          by_cases he0one : e0 = 1
          · have hq1 :
                IsQuadratic (MvPolynomial.C r * x1) := by
              simpa using isQuadratic_C_mul_pow_pow r 0 1 (by omega)
            have hmul1 :
                x0 * (MvPolynomial.C r * x1) = MvPolynomial.C r * x0 * x1 := by
                ring_nf
            simpa [monomial_fin2_eq, e0, e1, he0one, he1one, hmul1] using
              (inAdmissibleImage_of_relation_mul_low
                (u := u) (c := c0) (r := x0)
                (q := MvPolynomial.C r * x1)
                h0 hq1)
          · have he0ge : 2 ≤ e0 := by omega
            have he0le : e0 ≤ 3 := by omega
            have hq2 :
                IsQuadratic ((MvPolynomial.C r * x0 ^ (e0 - 2)) * x1) := by
              simpa using isQuadratic_C_mul_pow_pow r (e0 - 2) 1 (by omega)
            have hmul2 :
                x0 ^ 2 * ((MvPolynomial.C r * x0 ^ (e0 - 2)) * x1) =
                  (MvPolynomial.C r * x0 ^ e0) * x1 := by
              calc
                x0 ^ 2 * ((MvPolynomial.C r * x0 ^ (e0 - 2)) * x1)
                    = MvPolynomial.C r * (x0 ^ 2 * x0 ^ (e0 - 2)) * x1 := by
                        ring_nf
                _ = (MvPolynomial.C r * x0 ^ e0) * x1 := by
                      rw [← pow_add, Nat.add_sub_of_le he0ge]
            simpa [monomial_fin2_eq, e0, e1, he1one, hmul2] using
              (inAdmissibleImage_of_relation_mul_low
                (u := u) (c := c2) (r := x0 ^ 2)
                (q := (MvPolynomial.C r * x0 ^ (e0 - 2)) * x1)
                h2 hq2)
      · have he1ge : 2 ≤ e1 := by omega
        have hq :
            IsQuadratic ((MvPolynomial.C r * x0 ^ e0) * x1 ^ (e1 - 2)) := by
          exact isQuadratic_C_mul_pow_pow r e0 (e1 - 2) (by omega)
        have hmul :
            x1 ^ 2 * ((MvPolynomial.C r * x0 ^ e0) * x1 ^ (e1 - 2)) =
              (MvPolynomial.C r * x0 ^ e0) * x1 ^ e1 := by
          calc
            x1 ^ 2 * ((MvPolynomial.C r * x0 ^ e0) * x1 ^ (e1 - 2))
                = MvPolynomial.C r * x0 ^ e0 * (x1 ^ 2 * x1 ^ (e1 - 2)) := by
                    ring_nf
            _ = (MvPolynomial.C r * x0 ^ e0) * x1 ^ e1 := by
                  rw [← pow_add, Nat.add_sub_of_le he1ge]
        simpa [monomial_fin2_eq, e0, e1, hmul] using
          (inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c3) (r := x1 ^ 2)
            (q := (MvPolynomial.C r * x0 ^ e0) * x1 ^ (e1 - 2))
            h3 hq)
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

theorem residual_eq_zero_of_relations_x0_x1PlusAX0x1_x0sq_x1sq
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {a : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1 + a • (x0 * x1 : Poly))
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
  let w : RankFourVec := affineDimOneCrossKer c0 c2 t
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
    exact affineDimOneCrossKer_inKer h0 h2
  have hw00 : MvPolynomial.coeff m00 (sigma w) = s := by
    change MvPolynomial.coeff m00 (sigma (affineDimOneCrossKer c0 c2 t)) = s
    calc
      MvPolynomial.coeff m00 (sigma (affineDimOneCrossKer c0 c2 t)) = alpha * t ^ 2 := by
        exact coeff_m00_sigma_affineDimOneCrossKer c0 c2 t
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
    quartic_in_image_of_relations_x0_x1PlusAX0x1_x0sq_x1sq_of_coeff_m00_zero
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

theorem residual_eq_zero_of_equiv_relations_x0_x1PlusAX0x1_x0sq_x1sq
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    {a : ℝ}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1 + a • (x0 * x1 : Poly))
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = x0 ^ 2)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = x1 ^ 2) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e)
      (heQuad := fun {_} hpq => heQuad hpq)
      (heQuartic := fun {_} hpq => heQuartic hpq)
      hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_x0_x1PlusAX0x1_x0sq_x1sq
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0 h1 h2 h3 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_x0_x1PlusAX0x1_x0sq_x1sqPlane
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {a r s t w : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1 + a • (x0 * x1 : Poly))
    (h2 : ∑ i : Fin 4, c2 i • u i = r • (x0 ^ 2 : Poly) + s • (x1 ^ 2 : Poly))
    (h3 : ∑ i : Fin 4, c3 i • u i = t • (x0 ^ 2 : Poly) + w • (x1 ^ 2 : Poly))
    (hdet : r * w - s * t ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let det : ℝ := r * w - s * t
  have hdet0 : det ≠ 0 := by
    simpa [det] using hdet
  let c2' : Fin 4 → ℝ := fun i => (w / det) * c2 i + (-s / det) * c3 i
  let c3' : Fin 4 → ℝ := fun i => (-t / det) * c2 i + (r / det) * c3 i
  have hcoeff20 : (w / det) * r + (-s / det) * t = 1 := by
    field_simp [det, hdet0]
    ring
  have hcoeff21 : (w / det) * s + (-s / det) * w = 0 := by
    field_simp [det, hdet0]
    ring
  have hcoeff30 : (-t / det) * r + (r / det) * t = 0 := by
    field_simp [det, hdet0]
    ring
  have hcoeff31 : (-t / det) * s + (r / det) * w = 1 := by
    field_simp [det, hdet0]
    ring
  have h2' : ∑ i : Fin 4, c2' i • u i = x0 ^ 2 := by
    change relationPoly u c2' = x0 ^ 2
    calc
      relationPoly u c2'
          = relationPoly u ((w / det) • c2) + relationPoly u ((-s / det) • c3) := by
              rw [show c2' = (w / det) • c2 + (-s / det) • c3 by
                funext i
                simp [c2']
              , relationPoly_add]
      _ = (w / det) • relationPoly u c2 + (-s / det) • relationPoly u c3 := by
            rw [relationPoly_smul, relationPoly_smul]
      _ = (w / det) • (r • (x0 ^ 2 : Poly) + s • (x1 ^ 2 : Poly)) +
            (-s / det) • (t • (x0 ^ 2 : Poly) + w • (x1 ^ 2 : Poly)) := by
              rw [show relationPoly u c2 = ∑ i : Fin 4, c2 i • u i by rfl,
                show relationPoly u c3 = ∑ i : Fin 4, c3 i • u i by rfl,
                h2, h3]
      _ = ((w / det) * r + (-s / det) * t) • (x0 ^ 2 : Poly) +
            ((w / det) * s + (-s / det) * w) • (x1 ^ 2 : Poly) := by
              simp [smul_add, smul_smul, add_smul, add_assoc, add_left_comm, mul_comm]
      _ = x0 ^ 2 := by
            rw [hcoeff20, hcoeff21]
            simp
  have h3' : ∑ i : Fin 4, c3' i • u i = x1 ^ 2 := by
    change relationPoly u c3' = x1 ^ 2
    calc
      relationPoly u c3'
          = relationPoly u ((-t / det) • c2) + relationPoly u ((r / det) • c3) := by
              rw [show c3' = (-t / det) • c2 + (r / det) • c3 by
                funext i
                simp [c3']
              , relationPoly_add]
      _ = (-t / det) • relationPoly u c2 + (r / det) • relationPoly u c3 := by
            rw [relationPoly_smul, relationPoly_smul]
      _ = (-t / det) • (r • (x0 ^ 2 : Poly) + s • (x1 ^ 2 : Poly)) +
            (r / det) • (t • (x0 ^ 2 : Poly) + w • (x1 ^ 2 : Poly)) := by
              rw [show relationPoly u c2 = ∑ i : Fin 4, c2 i • u i by rfl,
                show relationPoly u c3 = ∑ i : Fin 4, c3 i • u i by rfl,
                h2, h3]
      _ = ((-t / det) * r + (r / det) * t) • (x0 ^ 2 : Poly) +
            ((-t / det) * s + (r / det) * w) • (x1 ^ 2 : Poly) := by
              simp [smul_add, smul_smul, add_smul, add_assoc, add_left_comm, add_comm, mul_comm]
      _ = x1 ^ 2 := by
            rw [hcoeff30, hcoeff31]
            simp
  exact residual_eq_zero_of_relations_x0_x1PlusAX0x1_x0sq_x1sq
    (B := B) (u := u) hu h0 h1 h2' h3' hp hsocp

theorem residual_eq_zero_of_equiv_relations_x0_x1PlusAX0x1_x0sq_x1sqPlane
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    {a r s t w : ℝ}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1 + a • (x0 * x1 : Poly))
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = r • (x0 ^ 2 : Poly) + s • (x1 ^ 2 : Poly))
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = t • (x0 ^ 2 : Poly) + w • (x1 ^ 2 : Poly))
    (hdet : r * w - s * t ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e)
      (heQuad := fun {_} hpq => heQuad hpq)
      (heQuartic := fun {_} hpq => heQuartic hpq)
      hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_x0_x1PlusAX0x1_x0sq_x1sqPlane
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0 h1 h2 h3 hdet hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

private def affineDimOneX0sqTailKer
    (c0 c2 : Fin 4 → ℝ) (t : ℝ) : RankFourVec :=
  relationDirection (-c0) (t • x1) + relationDirection c2 (t • (1 : Poly))

private theorem affineDimOneX0sqTailKer_admissible
    (c0 c2 : Fin 4 → ℝ) (t : ℝ) :
    IsAdmissibleDirection (affineDimOneX0sqTailKer c0 c2 t) := by
  refine isAdmissibleDirection_add
    (relationDirection_admissible (-c0)
      ((MvPolynomial.totalDegree_smul_le t x1).trans (by simp [x1])))
    (relationDirection_admissible c2
      ((MvPolynomial.totalDegree_smul_le t (1 : Poly)).trans (by simp)))

private theorem affineDimOneX0sqTailKer_inKer
    {u : RankFourVec} {c0 c2 : Fin 4 → ℝ} {t : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 * x1) :
    InAdmissibleKer u (affineDimOneX0sqTailKer c0 c2 t) := by
  refine ⟨affineDimOneX0sqTailKer_admissible c0 c2 t, ?_⟩
  rw [affineDimOneX0sqTailKer, A_add_right_local, A_relationDirection, A_relationDirection]
  simp [Pi.neg_apply, h0, h2]

private theorem coeff_m00_sigma_affineDimOneX0sqTailKer
    (c0 c2 : Fin 4 → ℝ) (t : ℝ) :
    MvPolynomial.coeff m00 (sigma (affineDimOneX0sqTailKer c0 c2 t)) =
      (∑ i : Fin 4, (c2 i) ^ 2) * t ^ 2 := by
  have hcoord : ∀ i : Fin 4,
      MvPolynomial.coeff m00 ((affineDimOneX0sqTailKer c0 c2 t i) ^ 2) = ((c2 i) * t) ^ 2 := by
    intro i
    rw [coeff_m00_sq]
    rw [affineDimOneX0sqTailKer]
    simp [relationDirection, m00, x1]
  rw [sigma, Fin.sum_univ_four]
  repeat' rw [MvPolynomial.coeff_add]
  rw [hcoord 0, hcoord 1, hcoord 2, hcoord 3]
  rw [Fin.sum_univ_four]
  ring_nf

theorem quartic_in_image_of_relations_x0_x1PlusAX0sq_x0x1_x1sq_of_coeff_m00_zero
    {u : RankFourVec}
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {a : ℝ}
    (ha : a ≠ 0)
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1 + a • (x0 ^ 2 : Poly))
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 * x1)
    (h3 : ∑ i : Fin 4, c3 i • u i = x1 ^ 2)
    {p : Poly} (hp : IsQuartic p)
    (h00 : MvPolynomial.coeff m00 p = 0) :
    InAdmissibleImage u p := by
  classical
  have hx0quad : IsQuadratic x0 := by
    change x0.totalDegree ≤ 2
    simp [x0]
  have honequad : IsQuadratic (1 : Poly) := by
    change (1 : Poly).totalDegree ≤ 2
    simp
  have hx0sqimg : InAdmissibleImage u (x0 ^ 2 : Poly) := by
    simpa [pow_two] using inAdmissibleImage_of_relation_mul_low
      (u := u) (c := c0) (r := x0)
      (q := x0) h0 hx0quad
  have hx1PlusImg : InAdmissibleImage u (x1 + a • (x0 ^ 2 : Poly)) := by
    simpa using inAdmissibleImage_of_relation_mul_low
      (u := u) (c := c1) (r := x1 + a • (x0 ^ 2 : Poly))
      (q := (1 : Poly)) h1 honequad
  have hx1img : InAdmissibleImage u x1 := by
    have hneg : InAdmissibleImage u (-(a • (x0 ^ 2 : Poly))) := by
      exact inAdmissibleImage_neg u (inAdmissibleImage_smul u a hx0sqimg)
    have hEq : (x1 + a • (x0 ^ 2 : Poly)) + (-(a • (x0 ^ 2 : Poly))) = x1 := by
      simp
    exact hEq ▸ inAdmissibleImage_add u hx1PlusImg hneg
  let monomialImage : ∀ (s : Fin 2 →₀ ℕ) (r : ℝ),
      s.sum (fun _ e => e) ≤ 4 →
      s ≠ m00 →
      InAdmissibleImage u (MvPolynomial.monomial s r) := by
    intro s r hdeg hne
    let e0 := s 0
    let e1 := s 1
    have hsum : s.sum (fun _ e => e) = s 0 + s 1 := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
    have hs0 : s 0 + s 1 ≤ 4 := by
      simpa [hsum] using hdeg
    have hs : e0 + e1 ≤ 4 := by
      simpa [e0, e1] using hs0
    by_cases he1zero : e1 = 0
    · have he0pos : 1 ≤ e0 := by
        by_contra he0pos
        have he00 : e0 = 0 := by omega
        apply hne
        ext i
        fin_cases i <;> simp [m00, e0, e1, he00, he1zero]
      by_cases he0small : e0 ≤ 3
      · have hq :
            IsQuadratic (MvPolynomial.C r * x0 ^ (e0 - 1)) := by
          simpa using isQuadratic_C_mul_pow_pow r (e0 - 1) 0 (by omega)
        have hmul :
            x0 * (MvPolynomial.C r * x0 ^ (e0 - 1)) =
              MvPolynomial.C r * x0 ^ e0 := by
          have hxpow : x0 * x0 ^ (e0 - 1) = x0 ^ e0 := by
            simpa [Nat.sub_add_cancel he0pos] using (pow_succ' x0 (e0 - 1)).symm
          calc
            x0 * (MvPolynomial.C r * x0 ^ (e0 - 1))
                = MvPolynomial.C r * (x0 * x0 ^ (e0 - 1)) := by
                    ring_nf
            _ = MvPolynomial.C r * x0 ^ e0 := by
                  simp [hxpow]
        simpa [monomial_fin2_eq, e0, e1, he1zero, hmul] using
          (inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c0) (r := x0)
            (q := MvPolynomial.C r * x0 ^ (e0 - 1))
            h0 hq)
      · have he0eq : e0 = 4 := by omega
        have hq1 : IsQuadratic ((MvPolynomial.C (r / a) * x0 ^ 2) : Poly) := by
          simpa using isQuadratic_C_mul_pow_pow (r / a) 2 0 (by omega)
        have hq2 : IsQuadratic ((MvPolynomial.C (r / a) * x0) : Poly) := by
          simpa using isQuadratic_C_mul_pow_pow (r / a) 1 0 (by omega)
        have himg1 :
            InAdmissibleImage u ((x1 + a • (x0 ^ 2 : Poly)) * (MvPolynomial.C (r / a) * x0 ^ 2)) := by
          exact inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c1) (r := x1 + a • (x0 ^ 2 : Poly))
            (q := MvPolynomial.C (r / a) * x0 ^ 2) h1 hq1
        have himg2 :
            InAdmissibleImage u ((x0 * x1 : Poly) * (MvPolynomial.C (r / a) * x0)) := by
          exact inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c2) (r := x0 * x1)
            (q := MvPolynomial.C (r / a) * x0) h2 hq2
        have hEq :
            (x1 + a • (x0 ^ 2 : Poly)) * (MvPolynomial.C (r / a) * x0 ^ 2) -
                (x0 * x1 : Poly) * (MvPolynomial.C (r / a) * x0) =
              MvPolynomial.C r * x0 ^ 4 := by
          have hEq1 :
              (x1 + a • (x0 ^ 2 : Poly)) * (MvPolynomial.C (r / a) * x0 ^ 2) -
                  (x0 * x1 : Poly) * (MvPolynomial.C (r / a) * x0) =
                MvPolynomial.C a * x0 ^ 4 * MvPolynomial.C (r * a⁻¹) := by
            simp [MvPolynomial.smul_eq_C_mul]
            field_simp [ha]
            rw [← MvPolynomial.C_mul]
            ring_nf
          have hEq2 :
              MvPolynomial.C a * x0 ^ 4 * MvPolynomial.C (r * a⁻¹) =
                MvPolynomial.C r * x0 ^ 4 := by
            calc
              MvPolynomial.C a * x0 ^ 4 * MvPolynomial.C (r * a⁻¹)
                  = x0 ^ 4 * (MvPolynomial.C a * MvPolynomial.C (r * a⁻¹)) := by
                      ring_nf
              _ = x0 ^ 4 * MvPolynomial.C (a * (r * a⁻¹)) := by
                    rw [← MvPolynomial.C_mul]
              _ = x0 ^ 4 * MvPolynomial.C r := by
                    congr 1
                    field_simp [ha]
              _ = MvPolynomial.C r * x0 ^ 4 := by
                    ring_nf
          exact hEq1.trans hEq2
        have himg :
            InAdmissibleImage u (MvPolynomial.C r * x0 ^ 4) := by
          exact hEq ▸ inAdmissibleImage_sub u himg1 himg2
        simpa [monomial_fin2_eq, e0, e1, he0eq, he1zero] using himg
    · by_cases he1one : e1 = 1
      · by_cases he0zero : e0 = 0
        · simpa [monomial_fin2_eq, e0, e1, he0zero, he1one, x1,
            MvPolynomial.smul_eq_C_mul, mul_comm] using
            inAdmissibleImage_smul u r hx1img
        · have he0pos : 1 ≤ e0 := by omega
          have hq :
              IsQuadratic (MvPolynomial.C r * x0 ^ (e0 - 1)) := by
            simpa using isQuadratic_C_mul_pow_pow r (e0 - 1) 0 (by omega)
          have hmul :
              (x0 * x1 : Poly) * (MvPolynomial.C r * x0 ^ (e0 - 1)) =
                (MvPolynomial.C r * x0 ^ e0) * x1 := by
            calc
              (x0 * x1 : Poly) * (MvPolynomial.C r * x0 ^ (e0 - 1))
                  = MvPolynomial.C r * (x0 * x0 ^ (e0 - 1)) * x1 := by
                      ring_nf
              _ = (MvPolynomial.C r * x0 ^ e0) * x1 := by
                    rw [show x0 * x0 ^ (e0 - 1) = x0 ^ e0 by
                      simpa [Nat.sub_add_cancel he0pos] using (pow_succ' x0 (e0 - 1)).symm]
          simpa [monomial_fin2_eq, e0, e1, he1one, hmul] using
            (inAdmissibleImage_of_relation_mul_low
              (u := u) (c := c2) (r := x0 * x1)
              (q := MvPolynomial.C r * x0 ^ (e0 - 1))
              h2 hq)
      · have he1ge : 2 ≤ e1 := by omega
        have hq :
            IsQuadratic ((MvPolynomial.C r * x0 ^ e0) * x1 ^ (e1 - 2)) := by
          exact isQuadratic_C_mul_pow_pow r e0 (e1 - 2) (by omega)
        have hmul :
            x1 ^ 2 * ((MvPolynomial.C r * x0 ^ e0) * x1 ^ (e1 - 2)) =
              (MvPolynomial.C r * x0 ^ e0) * x1 ^ e1 := by
          calc
            x1 ^ 2 * ((MvPolynomial.C r * x0 ^ e0) * x1 ^ (e1 - 2))
                = MvPolynomial.C r * x0 ^ e0 * (x1 ^ 2 * x1 ^ (e1 - 2)) := by
                    ring_nf
            _ = (MvPolynomial.C r * x0 ^ e0) * x1 ^ e1 := by
                  rw [← pow_add, Nat.add_sub_of_le he1ge]
        simpa [monomial_fin2_eq, e0, e1, hmul] using
          (inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c3) (r := x1 ^ 2)
            (q := (MvPolynomial.C r * x0 ^ e0) * x1 ^ (e1 - 2))
            h3 hq)
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

theorem residual_eq_zero_of_relations_x0_x1PlusAX0sq_x0x1_x1sq
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {a : ℝ}
    (ha : a ≠ 0)
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1 + a • (x0 ^ 2 : Poly))
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 * x1)
    (h3 : ∑ i : Fin 4, c3 i • u i = x1 ^ 2)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  rcases hp with ⟨hpquartic, k, qs, hqdeg, hpq⟩
  let s : ℝ := ∑ i : Fin k, (MvPolynomial.coeff m00 (qs i)) ^ 2
  let alpha : ℝ := ∑ i : Fin 4, (c2 i) ^ 2
  let t : ℝ := Real.sqrt (s / alpha)
  let w : RankFourVec := affineDimOneX0sqTailKer c0 c2 t
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
    exact affineDimOneX0sqTailKer_inKer h0 h2
  have hw00 : MvPolynomial.coeff m00 (sigma w) = s := by
    change MvPolynomial.coeff m00 (sigma (affineDimOneX0sqTailKer c0 c2 t)) = s
    calc
      MvPolynomial.coeff m00 (sigma (affineDimOneX0sqTailKer c0 c2 t)) = alpha * t ^ 2 := by
        exact coeff_m00_sigma_affineDimOneX0sqTailKer c0 c2 t
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
    quartic_in_image_of_relations_x0_x1PlusAX0sq_x0x1_x1sq_of_coeff_m00_zero
      ha h0 h1 h2 h3 hquartic_sub h00_sub
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

theorem residual_eq_zero_of_equiv_relations_x0_x1PlusAX0sq_x0x1_x1sq
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    {a : ℝ}
    (ha : a ≠ 0)
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1 + a • (x0 ^ 2 : Poly))
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = x0 * x1)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = x1 ^ 2) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e)
      (heQuad := fun {_} hpq => heQuad hpq)
      (heQuartic := fun {_} hpq => heQuartic hpq)
      hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_x0_x1PlusAX0sq_x0x1_x1sq
      (B := B0) (u := mapVec e.toAlgHom u) hu0 ha h0 h1 h2 h3 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_x0_x1PlusAX0sq_x0x1_x1sqPlane
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {a r s t w : ℝ}
    (ha : a ≠ 0)
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1 + a • (x0 ^ 2 : Poly))
    (h2 : ∑ i : Fin 4, c2 i • u i = r • (x0 * x1 : Poly) + s • (x1 ^ 2 : Poly))
    (h3 : ∑ i : Fin 4, c3 i • u i = t • (x0 * x1 : Poly) + w • (x1 ^ 2 : Poly))
    (hdet : r * w - s * t ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let det : ℝ := r * w - s * t
  have hdet0 : det ≠ 0 := by
    simpa [det] using hdet
  let c2' : Fin 4 → ℝ := fun i => (w / det) * c2 i + (-s / det) * c3 i
  let c3' : Fin 4 → ℝ := fun i => (-t / det) * c2 i + (r / det) * c3 i
  have hcoeff20 : (w / det) * r + (-s / det) * t = 1 := by
    field_simp [det, hdet0]
    ring
  have hcoeff21 : (w / det) * s + (-s / det) * w = 0 := by
    field_simp [det, hdet0]
    ring
  have hcoeff30 : (-t / det) * r + (r / det) * t = 0 := by
    field_simp [det, hdet0]
    ring
  have hcoeff31 : (-t / det) * s + (r / det) * w = 1 := by
    field_simp [det, hdet0]
    ring
  have h2' : ∑ i : Fin 4, c2' i • u i = x0 * x1 := by
    change relationPoly u c2' = x0 * x1
    calc
      relationPoly u c2'
          = relationPoly u ((w / det) • c2) + relationPoly u ((-s / det) • c3) := by
              rw [show c2' = (w / det) • c2 + (-s / det) • c3 by
                funext i
                simp [c2']
              , relationPoly_add]
      _ = (w / det) • relationPoly u c2 + (-s / det) • relationPoly u c3 := by
            rw [relationPoly_smul, relationPoly_smul]
      _ = (w / det) • (r • (x0 * x1 : Poly) + s • (x1 ^ 2 : Poly)) +
            (-s / det) • (t • (x0 * x1 : Poly) + w • (x1 ^ 2 : Poly)) := by
              rw [show relationPoly u c2 = ∑ i : Fin 4, c2 i • u i by rfl,
                show relationPoly u c3 = ∑ i : Fin 4, c3 i • u i by rfl,
                h2, h3]
      _ = ((w / det) * r + (-s / det) * t) • (x0 * x1 : Poly) +
            ((w / det) * s + (-s / det) * w) • (x1 ^ 2 : Poly) := by
              simp [smul_add, smul_smul, add_smul, add_assoc, add_left_comm, mul_comm]
      _ = x0 * x1 := by
            rw [hcoeff20, hcoeff21]
            simp
  have h3' : ∑ i : Fin 4, c3' i • u i = x1 ^ 2 := by
    change relationPoly u c3' = x1 ^ 2
    calc
      relationPoly u c3'
          = relationPoly u ((-t / det) • c2) + relationPoly u ((r / det) • c3) := by
              rw [show c3' = (-t / det) • c2 + (r / det) • c3 by
                funext i
                simp [c3']
              , relationPoly_add]
      _ = (-t / det) • relationPoly u c2 + (r / det) • relationPoly u c3 := by
            rw [relationPoly_smul, relationPoly_smul]
      _ = (-t / det) • (r • (x0 * x1 : Poly) + s • (x1 ^ 2 : Poly)) +
            (r / det) • (t • (x0 * x1 : Poly) + w • (x1 ^ 2 : Poly)) := by
              rw [show relationPoly u c2 = ∑ i : Fin 4, c2 i • u i by rfl,
                show relationPoly u c3 = ∑ i : Fin 4, c3 i • u i by rfl,
                h2, h3]
      _ = ((-t / det) * r + (r / det) * t) • (x0 * x1 : Poly) +
            ((-t / det) * s + (r / det) * w) • (x1 ^ 2 : Poly) := by
              simp [smul_add, smul_smul, add_smul, add_assoc, add_left_comm, add_comm, mul_comm]
      _ = x1 ^ 2 := by
            rw [hcoeff30, hcoeff31]
            simp
  exact residual_eq_zero_of_relations_x0_x1PlusAX0sq_x0x1_x1sq
    (B := B) (u := u) hu ha h0 h1 h2' h3' hp hsocp

theorem residual_eq_zero_of_equiv_relations_x0_x1PlusAX0sq_x0x1_x1sqPlane
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    {a r s t w : ℝ}
    (ha : a ≠ 0)
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1 + a • (x0 ^ 2 : Poly))
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = r • (x0 * x1 : Poly) + s • (x1 ^ 2 : Poly))
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = t • (x0 * x1 : Poly) + w • (x1 ^ 2 : Poly))
    (hdet : r * w - s * t ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e)
      (heQuad := fun {_} hpq => heQuad hpq)
      (heQuartic := fun {_} hpq => heQuartic hpq)
      hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_x0_x1PlusAX0sq_x0x1_x1sqPlane
      (B := B0) (u := mapVec e.toAlgHom u) hu0 ha h0 h1 h2 h3 hdet hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

private theorem coeff_m02_sq_of_quadratic
    (q : Poly) (hq : IsQuadratic q) :
    MvPolynomial.coeff m02 (q ^ 2) =
      (MvPolynomial.coeff m01 q) ^ 2 +
        2 * MvPolynomial.coeff m00 q * MvPolynomial.coeff m02 q := by
  rw [pow_two, MvPolynomial.coeff_mul, quadratic_eq_quadForm hq]
  have hdiag :
      Finset.antidiagonal m02 = {(m00, m02), (m01, m01), (m02, m00)} := by
    ext x
    constructor
    · intro hx
      have hxsum : x.1 + x.2 = m02 := Finset.mem_antidiagonal.mp hx
      have hx0 : x.1 0 = 0 := by
        have h0 : x.1 0 + x.2 0 = 0 := by
          simpa [m02] using congrArg (fun e : Fin 2 →₀ ℕ => e 0) hxsum
        omega
      have hx1le : x.1 1 ≤ 2 := by
        have h1 : x.1 1 + x.2 1 = 2 := by
          simpa [m02] using congrArg (fun e : Fin 2 →₀ ℕ => e 1) hxsum
        omega
      interval_cases h11 : x.1 1
      · have hx1 : x.1 = m00 := by
          ext i
          fin_cases i <;> simp [m00, hx0, h11]
        have hx2 : x.2 = m02 := by
          ext i
          fin_cases i
          · have h0 : x.2 0 = 0 := by
              have h0sum : x.1 0 + x.2 0 = 0 := by
                simpa [m02] using congrArg (fun e : Fin 2 →₀ ℕ => e 0) hxsum
              omega
            simp [m02, h0]
          · have h1 : x.2 1 = 2 := by
              have h1sum : x.1 1 + x.2 1 = 2 := by
                simpa [m02] using congrArg (fun e : Fin 2 →₀ ℕ => e 1) hxsum
              omega
            simp [m02, h1]
        refine Finset.mem_insert.mpr ?_
        left
        exact Prod.ext_iff.mpr ⟨hx1, hx2⟩
      · have hx1 : x.1 = m01 := by
          ext i
          fin_cases i <;> simp [m01, hx0, h11]
        have hx2 : x.2 = m01 := by
          ext i
          fin_cases i
          · have h0 : x.2 0 = 0 := by
              have h0sum : x.1 0 + x.2 0 = 0 := by
                simpa [m02] using congrArg (fun e : Fin 2 →₀ ℕ => e 0) hxsum
              omega
            simp [m01, h0]
          · have h1 : x.2 1 = 1 := by
              have h1sum : x.1 1 + x.2 1 = 2 := by
                simpa [m02] using congrArg (fun e : Fin 2 →₀ ℕ => e 1) hxsum
              omega
            simp [m01, h1]
        refine Finset.mem_insert.mpr ?_
        right
        refine Finset.mem_insert.mpr ?_
        left
        exact Prod.ext_iff.mpr ⟨hx1, hx2⟩
      · have hx1 : x.1 = m02 := by
          ext i
          fin_cases i <;> simp [m02, hx0, h11]
        have hx2 : x.2 = m00 := by
          ext i
          fin_cases i
          · have h0 : x.2 0 = 0 := by
              have h0sum : x.1 0 + x.2 0 = 0 := by
                simpa [m02] using congrArg (fun e : Fin 2 →₀ ℕ => e 0) hxsum
              omega
            simp [m00, h0]
          · have h1 : x.2 1 = 0 := by
              have h1sum : x.1 1 + x.2 1 = 2 := by
                simpa [m02] using congrArg (fun e : Fin 2 →₀ ℕ => e 1) hxsum
              omega
            simp [m00, h1]
        refine Finset.mem_insert.mpr ?_
        right
        refine Finset.mem_insert.mpr ?_
        right
        simpa using (Prod.ext_iff.mpr ⟨hx1, hx2⟩ : x = (m02, m00))
    · intro hx
      simp at hx
      rcases hx with rfl | rfl | rfl
      · exact Finset.mem_antidiagonal.mpr (by
          ext i
          fin_cases i <;> simp [m00, m02])
      · exact Finset.mem_antidiagonal.mpr (by
          ext i
          fin_cases i <;> simp [m01, m02])
      · exact Finset.mem_antidiagonal.mpr (by
          ext i
          fin_cases i <;> simp [m00, m02])
  rw [hdiag]
  simp [quadForm, m00, m01, m02]
  ring

private theorem coeff_m02_sq_of_quadratic_eq
    (q : Poly) (hq : IsQuadratic q) :
    MvPolynomial.coeff m02 (q ^ 2) =
      (MvPolynomial.coeff m01 q) ^ 2 +
        2 * MvPolynomial.coeff m00 q * MvPolynomial.coeff m02 q :=
  coeff_m02_sq_of_quadratic q hq

private theorem coeff_m00_X0_mul_X1 :
    MvPolynomial.coeff m00 ((MvPolynomial.X 0 : Poly) * MvPolynomial.X 1) = 0 := by
  have hmon :
      ((MvPolynomial.X 0 : Poly) * MvPolynomial.X 1) = MvPolynomial.monomial m11 (1 : ℝ) := by
    simp [m11, MvPolynomial.monomial_eq]
  rw [hmon]
  simp [m00, m11]

private theorem coeff_m01_X0_mul_X1 :
    MvPolynomial.coeff m01 ((MvPolynomial.X 0 : Poly) * MvPolynomial.X 1) = 0 := by
  have hmon :
      ((MvPolynomial.X 0 : Poly) * MvPolynomial.X 1) = MvPolynomial.monomial m11 (1 : ℝ) := by
    simp [m11, MvPolynomial.monomial_eq]
  rw [hmon]
  simp [m01, m11]

private theorem coeff_m02_X0_mul_X1 :
    MvPolynomial.coeff m02 ((MvPolynomial.X 0 : Poly) * MvPolynomial.X 1) = 0 := by
  have hmon :
      ((MvPolynomial.X 0 : Poly) * MvPolynomial.X 1) = MvPolynomial.monomial m11 (1 : ℝ) := by
    simp [m11, MvPolynomial.monomial_eq]
  rw [hmon]
  simp [m02, m11]

private theorem coeff_m00_X0_mul_x1 :
    MvPolynomial.coeff m00 ((MvPolynomial.X 0 : Poly) * x1) = 0 := by
  simpa [x1] using coeff_m00_X0_mul_X1

private theorem coeff_m01_X0_mul_x1 :
    MvPolynomial.coeff m01 ((MvPolynomial.X 0 : Poly) * x1) = 0 := by
  simpa [x1] using coeff_m01_X0_mul_X1

private theorem coeff_m02_X0_mul_x1 :
    MvPolynomial.coeff m02 ((MvPolynomial.X 0 : Poly) * x1) = 0 := by
  simpa [x1] using coeff_m02_X0_mul_X1

private theorem coeff_m00_x0_mul_x1 :
    MvPolynomial.coeff m00 (x0 * x1 : Poly) = 0 := by
  simpa [x0] using coeff_m00_X0_mul_X1

private theorem coeff_m01_x0_mul_x1 :
    MvPolynomial.coeff m01 (x0 * x1 : Poly) = 0 := by
  simpa [x0] using coeff_m01_X0_mul_X1

private theorem coeff_m02_x0_mul_x1 :
    MvPolynomial.coeff m02 (x0 * x1 : Poly) = 0 := by
  simpa [x0] using coeff_m02_X0_mul_X1

private theorem coeff_m01_one :
    MvPolynomial.coeff m01 (1 : Poly) = 0 := by
  rw [MvPolynomial.coeff_one]
  have h : (0 : Fin 2 →₀ ℕ) ≠ m01 := by
    intro h0
    have h1 := congrArg (fun s : Fin 2 →₀ ℕ => s 1) h0
    simp [m01] at h1
  simp [h]

private theorem coeff_m02_one :
    MvPolynomial.coeff m02 (1 : Poly) = 0 := by
  rw [MvPolynomial.coeff_one]
  have h : (0 : Fin 2 →₀ ℕ) ≠ m02 := by
    intro h0
    have h1 := congrArg (fun s : Fin 2 →₀ ℕ => s 1) h0
    simp [m02] at h1
  simp [h]

private theorem coeff_m00_x1 : MvPolynomial.coeff m00 (x1 : Poly) = 0 := by
  simp [x1, m00]

private theorem coeff_m00_x1sq : MvPolynomial.coeff m00 (x1 ^ 2 : Poly) = 0 := by
  rw [x1, MvPolynomial.coeff_X_pow]
  have h : Finsupp.single 1 2 ≠ m00 := by
    intro hs
    have h1 := congrArg (fun s : Fin 2 →₀ ℕ => s 1) hs
    simp [m00] at h1
  simp [h]

private theorem coeff_m00_x1cb : MvPolynomial.coeff m00 (x1 ^ 3 : Poly) = 0 := by
  rw [x1, MvPolynomial.coeff_X_pow]
  have h : Finsupp.single 1 3 ≠ m00 := by
    intro hs
    have h1 := congrArg (fun s : Fin 2 →₀ ℕ => s 1) hs
    simp [m00] at h1
  simp [h]

private theorem coeff_m00_x1qt : MvPolynomial.coeff m00 (x1 ^ 4 : Poly) = 0 := by
  rw [x1, MvPolynomial.coeff_X_pow]
  have h : Finsupp.single 1 4 ≠ m00 := by
    intro hs
    have h1 := congrArg (fun s : Fin 2 →₀ ℕ => s 1) hs
    simp [m00] at h1
  simp [h]

private theorem coeff_m01_x1 : MvPolynomial.coeff m01 (x1 : Poly) = 1 := by
  simp [x1, m01]

private theorem coeff_m01_x1sq : MvPolynomial.coeff m01 (x1 ^ 2 : Poly) = 0 := by
  rw [x1, MvPolynomial.coeff_X_pow]
  have h : Finsupp.single 1 2 ≠ m01 := by
    intro hs
    have h1 := congrArg (fun s : Fin 2 →₀ ℕ => s 1) hs
    simp [m01] at h1
  simp [h]

private theorem coeff_m01_x1cb : MvPolynomial.coeff m01 (x1 ^ 3 : Poly) = 0 := by
  rw [x1, MvPolynomial.coeff_X_pow]
  have h : Finsupp.single 1 3 ≠ m01 := by
    intro hs
    have h1 := congrArg (fun s : Fin 2 →₀ ℕ => s 1) hs
    simp [m01] at h1
  simp [h]

private theorem coeff_m01_x1qt : MvPolynomial.coeff m01 (x1 ^ 4 : Poly) = 0 := by
  rw [x1, MvPolynomial.coeff_X_pow]
  have h : Finsupp.single 1 4 ≠ m01 := by
    intro hs
    have h1 := congrArg (fun s : Fin 2 →₀ ℕ => s 1) hs
    simp [m01] at h1
  simp [h]

private theorem coeff_m02_x1 : MvPolynomial.coeff m02 (x1 : Poly) = 0 := by
  simp [x1, m02]

private theorem coeff_m02_x1sq : MvPolynomial.coeff m02 (x1 ^ 2 : Poly) = 1 := by
  rw [x1, MvPolynomial.coeff_X_pow]
  simp [m02]

private theorem coeff_m02_x1cb : MvPolynomial.coeff m02 (x1 ^ 3 : Poly) = 0 := by
  rw [x1, MvPolynomial.coeff_X_pow]
  have h : Finsupp.single 1 3 ≠ m02 := by
    intro hs
    have h1 := congrArg (fun s : Fin 2 →₀ ℕ => s 1) hs
    simp [m02] at h1
  simp [h]

private theorem coeff_m02_x1qt : MvPolynomial.coeff m02 (x1 ^ 4 : Poly) = 0 := by
  rw [x1, MvPolynomial.coeff_X_pow]
  have h : Finsupp.single 1 4 ≠ m02 := by
    intro hs
    have h1 := congrArg (fun s : Fin 2 →₀ ℕ => s 1) hs
    simp [m02] at h1
  simp [h]

private theorem coeff_m03_x1 : MvPolynomial.coeff m03 (x1 : Poly) = 0 := by
  simp [x1, m03]

private theorem coeff_m03_x1sq : MvPolynomial.coeff m03 (x1 ^ 2 : Poly) = 0 := by
  rw [x1, MvPolynomial.coeff_X_pow]
  have h : Finsupp.single 1 2 ≠ m03 := by
    intro hs
    have h1 := congrArg (fun s : Fin 2 →₀ ℕ => s 1) hs
    simp [m03] at h1
  simp [h]

private theorem coeff_m03_x1cb : MvPolynomial.coeff m03 (x1 ^ 3 : Poly) = 1 := by
  rw [x1, MvPolynomial.coeff_X_pow]
  simp [m03]

private theorem coeff_m03_x1qt : MvPolynomial.coeff m03 (x1 ^ 4 : Poly) = 0 := by
  rw [x1, MvPolynomial.coeff_X_pow]
  have h : Finsupp.single 1 4 ≠ m03 := by
    intro hs
    have h1 := congrArg (fun s : Fin 2 →₀ ℕ => s 1) hs
    simp [m03] at h1
  simp [h]

private theorem coeff_m04_x1 : MvPolynomial.coeff m04 (x1 : Poly) = 0 := by
  simp [x1, m04]

private theorem coeff_m04_x1sq : MvPolynomial.coeff m04 (x1 ^ 2 : Poly) = 0 := by
  rw [x1, MvPolynomial.coeff_X_pow]
  have h : Finsupp.single 1 2 ≠ m04 := by
    intro hs
    have h1 := congrArg (fun s : Fin 2 →₀ ℕ => s 1) hs
    simp [m04] at h1
  simp [h]

private theorem coeff_m04_x1cb : MvPolynomial.coeff m04 (x1 ^ 3 : Poly) = 0 := by
  rw [x1, MvPolynomial.coeff_X_pow]
  have h : Finsupp.single 1 3 ≠ m04 := by
    intro hs
    have h1 := congrArg (fun s : Fin 2 →₀ ℕ => s 1) hs
    simp [m04] at h1
  simp [h]

private theorem coeff_m04_x1qt : MvPolynomial.coeff m04 (x1 ^ 4 : Poly) = 1 := by
  rw [x1, MvPolynomial.coeff_X_pow]
  simp [m04]

private def x1sqTailFunctional (a : ℝ) (p : Poly) : ℝ :=
  MvPolynomial.coeff m04 p
    - a * MvPolynomial.coeff m03 p
    + a ^ 2 * MvPolynomial.coeff m02 p
    - a ^ 3 * MvPolynomial.coeff m01 p
    + a ^ 4 * MvPolynomial.coeff m00 p

private theorem x1sqTailFunctional_sq_of_quadratic_eq
    (a : ℝ) (q : Poly) (hq : IsQuadratic q) :
    x1sqTailFunctional a (q ^ 2) =
      (MvPolynomial.coeff m02 q
        - a * MvPolynomial.coeff m01 q
        + a ^ 2 * MvPolynomial.coeff m00 q) ^ 2 := by
  rw [x1sqTailFunctional, coeff_m04_sq_of_quadratic_eq q hq,
    coeff_m03_sq_of_quadratic_eq q hq, coeff_m02_sq_of_quadratic_eq q hq,
    coeff_m01_sq_of_quadratic_eq q hq, coeff_m00_sq]
  ring

private theorem pureX1Quartic_eq_x1PlusAX1sq_mul
    (a b1 b2 b3 b4 : ℝ)
    (htail : b4 - a * b3 + a ^ 2 * b2 - a ^ 3 * b1 = 0) :
    b1 • x1 + b2 • (x1 ^ 2 : Poly) + b3 • (x1 ^ 3 : Poly) + b4 • (x1 ^ 4 : Poly) =
      (x1 + a • (x1 ^ 2 : Poly)) *
        (MvPolynomial.C b1 +
          (MvPolynomial.C b2 - MvPolynomial.C a * MvPolynomial.C b1) * x1 +
          (MvPolynomial.C b3 - MvPolynomial.C a * MvPolynomial.C b2 +
            MvPolynomial.C a ^ 2 * MvPolynomial.C b1) * (x1 ^ 2)) := by
  have hb4 : b4 = a * b3 - a ^ 2 * b2 + a ^ 3 * b1 := by
    linarith
  rw [hb4]
  simp [MvPolynomial.smul_eq_C_mul]
  ring

private theorem inAdmissibleImage_pureX1Quartic_of_x1sqTailFunctional_zero
    {u : RankFourVec}
    {c1 : Fin 4 → ℝ}
    {a : ℝ}
    (h1 : ∑ i : Fin 4, c1 i • u i = x1 + a • (x1 ^ 2 : Poly))
    {b1 b2 b3 b4 : ℝ}
    (htail : b4 - a * b3 + a ^ 2 * b2 - a ^ 3 * b1 = 0) :
    InAdmissibleImage u
      (b1 • x1 + b2 • (x1 ^ 2 : Poly) + b3 • (x1 ^ 3 : Poly) + b4 • (x1 ^ 4 : Poly)) := by
  let q : Poly :=
    MvPolynomial.C b1 +
      (MvPolynomial.C b2 - MvPolynomial.C a * MvPolynomial.C b1) * x1 +
      (MvPolynomial.C b3 - MvPolynomial.C a * MvPolynomial.C b2 +
        MvPolynomial.C a ^ 2 * MvPolynomial.C b1) * (x1 ^ 2)
  have hq : IsQuadratic q := by
    have hq0 : IsQuadratic (MvPolynomial.C b1) := by
      change (MvPolynomial.C b1 : Poly).totalDegree ≤ 2
      simp
    have hq1 : IsQuadratic ((MvPolynomial.C b2 - MvPolynomial.C a * MvPolynomial.C b1) * x1) := by
      simpa using isQuadratic_C_mul_pow_pow (b2 - a * b1) 0 1 (by omega)
    have hq2 :
        IsQuadratic
          ((MvPolynomial.C b3 - MvPolynomial.C a * MvPolynomial.C b2 +
            MvPolynomial.C a ^ 2 * MvPolynomial.C b1) * (x1 ^ 2)) := by
      have hq2' := isQuadratic_C_mul_pow_pow (b3 - a * b2 + a ^ 2 * b1) 0 2 (by omega)
      have hpow0 :
          (MvPolynomial.C (b3 - a * b2 + a ^ 2 * b1) * x0 ^ 0 * x1 ^ 2 : Poly) =
            ((MvPolynomial.C (b3 - a * b2 + a ^ 2 * b1) : Poly) * (x1 ^ 2)) := by
        simp [x0]
      have hq2'' :
          IsQuadratic ((MvPolynomial.C (b3 - a * b2 + a ^ 2 * b1) : Poly) * (x1 ^ 2)) := by
        exact hpow0 ▸ hq2'
      have hcoef2 :
          (MvPolynomial.C (b3 - a * b2 + a ^ 2 * b1) : Poly) =
            MvPolynomial.C b3 - MvPolynomial.C a * MvPolynomial.C b2 +
              MvPolynomial.C a ^ 2 * MvPolynomial.C b1 := by
        simp [sub_eq_add_neg, pow_two, mul_left_comm, mul_comm]
      have hmul :
          ((MvPolynomial.C (b3 - a * b2 + a ^ 2 * b1) : Poly) * (x1 ^ 2)) =
            ((MvPolynomial.C b3 - MvPolynomial.C a * MvPolynomial.C b2 +
              MvPolynomial.C a ^ 2 * MvPolynomial.C b1) * (x1 ^ 2)) := by
        rw [hcoef2]
      exact hmul.symm ▸ hq2''
    have hq01 :
        IsQuadratic
          (MvPolynomial.C b1 + (MvPolynomial.C b2 - MvPolynomial.C a * MvPolynomial.C b1) * x1) := by
      exact (MvPolynomial.totalDegree_add _ _).trans <| max_le hq0 hq1
    dsimp [q]
    exact (MvPolynomial.totalDegree_add _ _).trans <| max_le hq01 hq2
  have himg :
      InAdmissibleImage u ((x1 + a • (x1 ^ 2 : Poly)) * q) := by
    exact inAdmissibleImage_of_relation_mul_low
      (u := u) (c := c1) (r := x1 + a • (x1 ^ 2 : Poly))
      (q := q) h1 hq
  dsimp [q] at himg ⊢
  exact (pureX1Quartic_eq_x1PlusAX1sq_mul a b1 b2 b3 b4 htail).symm ▸ himg

private theorem x1sqTailFunctional_add
    (a : ℝ) (p q : Poly) :
    x1sqTailFunctional a (p + q) =
      x1sqTailFunctional a p + x1sqTailFunctional a q := by
  unfold x1sqTailFunctional
  repeat' rw [MvPolynomial.coeff_add]
  ring

private theorem x1sqTailFunctional_sub
    (a : ℝ) (p q : Poly) :
    x1sqTailFunctional a (p - q) =
      x1sqTailFunctional a p - x1sqTailFunctional a q := by
  unfold x1sqTailFunctional
  repeat' rw [MvPolynomial.coeff_sub]
  ring

private def affineDimOneX1sqTailKer
    (c0 c2 : Fin 4 → ℝ) (β γ : ℝ) : RankFourVec :=
  relationDirection (-c0) (β • x0 + γ • (x0 * x1 : Poly)) +
    relationDirection c2 (β • (1 : Poly) + γ • x1)

private theorem affineDimOneX1sqTailKer_admissible
    (c0 c2 : Fin 4 → ℝ) (β γ : ℝ) :
    IsAdmissibleDirection (affineDimOneX1sqTailKer c0 c2 β γ) := by
  refine isAdmissibleDirection_add ?_ ?_
  · refine relationDirection_admissible (-c0) ?_
    have h0 : IsQuadratic (β • x0) := by
      exact (MvPolynomial.totalDegree_smul_le β x0).trans (by simp [x0])
    have hcross : IsQuadratic (x0 * x1 : Poly) := by
      calc
        (x0 * x1 : Poly).totalDegree ≤ x0.totalDegree + x1.totalDegree := by
          exact MvPolynomial.totalDegree_mul _ _
        _ ≤ 2 := by
          simp [x0, x1]
    have h1 : IsQuadratic (γ • (x0 * x1 : Poly)) := by
      exact (MvPolynomial.totalDegree_smul_le γ (x0 * x1 : Poly)).trans hcross
    calc
      (β • x0 + γ • (x0 * x1 : Poly)).totalDegree ≤
          max (β • x0).totalDegree (γ • (x0 * x1 : Poly)).totalDegree := by
            exact MvPolynomial.totalDegree_add _ _
      _ ≤ 2 := max_le h0 h1
  · refine relationDirection_admissible c2 ?_
    have h0 : IsQuadratic (β • (1 : Poly)) := by
      exact (MvPolynomial.totalDegree_smul_le β (1 : Poly)).trans (by simp)
    have h1 : IsQuadratic (γ • x1) := by
      exact (MvPolynomial.totalDegree_smul_le γ x1).trans (by simp [x1])
    calc
      (β • (1 : Poly) + γ • x1).totalDegree ≤
          max (β • (1 : Poly)).totalDegree (γ • x1).totalDegree := by
            exact MvPolynomial.totalDegree_add _ _
      _ ≤ 2 := max_le h0 h1

private theorem affineDimOneX1sqTailKer_inKer
    {u : RankFourVec} {c0 c2 : Fin 4 → ℝ} {β γ : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 ^ 2) :
    InAdmissibleKer u (affineDimOneX1sqTailKer c0 c2 β γ) := by
  refine ⟨affineDimOneX1sqTailKer_admissible c0 c2 β γ, ?_⟩
  rw [affineDimOneX1sqTailKer, A_add_right_local, A_relationDirection, A_relationDirection]
  have h0neg : ∑ i : Fin 4, (-c0 i) • u i = -(x0 : Poly) := by
    simpa using congrArg (fun q : Poly => -q) h0
  have h0neg' : ∑ i : Fin 4, (-c0) i • u i = -(x0 : Poly) := by
    simpa using h0neg
  rw [h0neg', h2]
  simp [MvPolynomial.smul_eq_C_mul]
  ring_nf

private theorem coeff_m00_sigma_affineDimOneX1sqTailKer
    (c0 c2 : Fin 4 → ℝ) (β γ : ℝ) :
    MvPolynomial.coeff m00 (sigma (affineDimOneX1sqTailKer c0 c2 β γ)) =
      (∑ i : Fin 4, (c2 i) ^ 2) * β ^ 2 := by
  have hcoord : ∀ i : Fin 4,
      MvPolynomial.coeff m00 ((affineDimOneX1sqTailKer c0 c2 β γ i) ^ 2) =
        ((c2 i) * β) ^ 2 := by
    intro i
    rw [coeff_m00_sq, affineDimOneX1sqTailKer]
    simp [relationDirection, m00, x0, x1, coeff_m00_X0_mul_X1]
  rw [sigma, Fin.sum_univ_four]
  repeat' rw [MvPolynomial.coeff_add]
  rw [hcoord 0, hcoord 1, hcoord 2, hcoord 3]
  rw [Fin.sum_univ_four]
  ring_nf

private theorem x1sqTailFunctional_sigma_affineDimOneX1sqTailKer
    (a : ℝ) (c0 c2 : Fin 4 → ℝ) (β γ : ℝ) :
    x1sqTailFunctional a (sigma (affineDimOneX1sqTailKer c0 c2 β γ)) =
      (∑ i : Fin 4, (c2 i) ^ 2) * (a ^ 2 * β - a * γ) ^ 2 := by
  have hcoord : ∀ i : Fin 4,
      x1sqTailFunctional a ((affineDimOneX1sqTailKer c0 c2 β γ i) ^ 2) =
        ((c2 i) * (a ^ 2 * β - a * γ)) ^ 2 := by
    intro i
    rw [x1sqTailFunctional_sq_of_quadratic_eq a
      (affineDimOneX1sqTailKer c0 c2 β γ i)
      ((affineDimOneX1sqTailKer_admissible c0 c2 β γ) i)]
    have hm00 :
        MvPolynomial.coeff m00 (affineDimOneX1sqTailKer c0 c2 β γ i) = (c2 i) * β := by
      rw [affineDimOneX1sqTailKer]
      simp [relationDirection, m00, x0, x1, coeff_m00_X0_mul_X1]
    have hm01 :
        MvPolynomial.coeff m01 (affineDimOneX1sqTailKer c0 c2 β γ i) = (c2 i) * γ := by
      rw [affineDimOneX1sqTailKer]
      simp [relationDirection, m01, x0, x1, coeff_m01_X0_mul_X1, coeff_m01_one]
    have hm02 :
        MvPolynomial.coeff m02 (affineDimOneX1sqTailKer c0 c2 β γ i) = 0 := by
      rw [affineDimOneX1sqTailKer]
      simp [relationDirection, m02, x0, x1, coeff_m02_X0_mul_X1, coeff_m02_one]
    rw [hm00, hm01, hm02]
    ring
  rw [sigma, Fin.sum_univ_four]
  repeat' rw [x1sqTailFunctional_add]
  rw [hcoord 0, hcoord 1, hcoord 2, hcoord 3]
  rw [Fin.sum_univ_four]
  ring_nf

theorem quartic_in_image_of_relations_x0_x1PlusAX1sq_x0sq_x0x1_of_coeff_m00_x1sqTail_zero
    {u : RankFourVec}
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {a : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1 + a • (x1 ^ 2 : Poly))
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 ^ 2)
    (h3 : ∑ i : Fin 4, c3 i • u i = x0 * x1)
    {p : Poly} (hp : IsQuartic p)
    (h00 : MvPolynomial.coeff m00 p = 0)
    (htail : x1sqTailFunctional a p = 0) :
    InAdmissibleImage u p := by
  classical
  let purePart : Poly :=
    MvPolynomial.coeff m01 p • x1 +
      MvPolynomial.coeff m02 p • (x1 ^ 2 : Poly) +
        MvPolynomial.coeff m03 p • (x1 ^ 3 : Poly) +
          MvPolynomial.coeff m04 p • (x1 ^ 4 : Poly)
  have hpureQuartic : IsQuartic purePart := by
    change purePart.totalDegree ≤ 4
    have h1deg : IsQuartic (MvPolynomial.coeff m01 p • x1) := by
      exact (MvPolynomial.totalDegree_smul_le _ x1).trans (by simp [x1])
    have h2deg : IsQuartic (MvPolynomial.coeff m02 p • (x1 ^ 2 : Poly)) := by
      exact (MvPolynomial.totalDegree_smul_le _ (x1 ^ 2 : Poly)).trans (by simp [x1])
    have h3deg : IsQuartic (MvPolynomial.coeff m03 p • (x1 ^ 3 : Poly)) := by
      exact (MvPolynomial.totalDegree_smul_le _ (x1 ^ 3 : Poly)).trans (by simp [x1])
    have h4deg : IsQuartic (MvPolynomial.coeff m04 p • (x1 ^ 4 : Poly)) := by
      exact (MvPolynomial.totalDegree_smul_le _ (x1 ^ 4 : Poly)).trans (by simp [x1])
    have h12 :
        IsQuartic
          (MvPolynomial.coeff m01 p • x1 +
            MvPolynomial.coeff m02 p • (x1 ^ 2 : Poly)) := by
      calc
        (MvPolynomial.coeff m01 p • x1 +
            MvPolynomial.coeff m02 p • (x1 ^ 2 : Poly)).totalDegree ≤
            max (MvPolynomial.coeff m01 p • x1).totalDegree
              (MvPolynomial.coeff m02 p • (x1 ^ 2 : Poly)).totalDegree := by
                exact MvPolynomial.totalDegree_add _ _
        _ ≤ 4 := max_le h1deg h2deg
    have h34 :
        IsQuartic
          (MvPolynomial.coeff m03 p • (x1 ^ 3 : Poly) +
            MvPolynomial.coeff m04 p • (x1 ^ 4 : Poly)) := by
      calc
        (MvPolynomial.coeff m03 p • (x1 ^ 3 : Poly) +
            MvPolynomial.coeff m04 p • (x1 ^ 4 : Poly)).totalDegree ≤
            max (MvPolynomial.coeff m03 p • (x1 ^ 3 : Poly)).totalDegree
              (MvPolynomial.coeff m04 p • (x1 ^ 4 : Poly)).totalDegree := by
                exact MvPolynomial.totalDegree_add _ _
        _ ≤ 4 := max_le h3deg h4deg
    have h123 :
        IsQuartic
          ((MvPolynomial.coeff m01 p • x1 +
              MvPolynomial.coeff m02 p • (x1 ^ 2 : Poly)) +
            MvPolynomial.coeff m03 p • (x1 ^ 3 : Poly)) := by
      calc
        ((MvPolynomial.coeff m01 p • x1 +
            MvPolynomial.coeff m02 p • (x1 ^ 2 : Poly)) +
            MvPolynomial.coeff m03 p • (x1 ^ 3 : Poly)).totalDegree ≤
            max (MvPolynomial.coeff m01 p • x1 +
                MvPolynomial.coeff m02 p • (x1 ^ 2 : Poly)).totalDegree
              (MvPolynomial.coeff m03 p • (x1 ^ 3 : Poly)).totalDegree := by
                exact MvPolynomial.totalDegree_add _ _
        _ ≤ 4 := max_le h12 h3deg
    dsimp [purePart]
    calc
      (((MvPolynomial.coeff m01 p • x1 +
            MvPolynomial.coeff m02 p • (x1 ^ 2 : Poly)) +
            MvPolynomial.coeff m03 p • (x1 ^ 3 : Poly)) +
            MvPolynomial.coeff m04 p • (x1 ^ 4 : Poly)).totalDegree ≤
          max (((MvPolynomial.coeff m01 p • x1 +
                MvPolynomial.coeff m02 p • (x1 ^ 2 : Poly)) +
                MvPolynomial.coeff m03 p • (x1 ^ 3 : Poly)).totalDegree)
            (MvPolynomial.coeff m04 p • (x1 ^ 4 : Poly)).totalDegree := by
                exact MvPolynomial.totalDegree_add _ _
      _ ≤ 4 := max_le h123 h4deg
  have htailPure :
      MvPolynomial.coeff m04 p - a * MvPolynomial.coeff m03 p +
          a ^ 2 * MvPolynomial.coeff m02 p - a ^ 3 * MvPolynomial.coeff m01 p = 0 := by
    unfold x1sqTailFunctional at htail
    rw [h00] at htail
    simpa using htail
  have hpureImg : InAdmissibleImage u purePart := by
    dsimp [purePart]
    exact inAdmissibleImage_pureX1Quartic_of_x1sqTailFunctional_zero h1 htailPure
  let r : Poly := p - purePart
  have hpure00 : MvPolynomial.coeff m00 purePart = 0 := by
    dsimp [purePart]
    simp [coeff_m00_x1, coeff_m00_x1sq, coeff_m00_x1cb, coeff_m00_x1qt]
  have hpure01 : MvPolynomial.coeff m01 purePart = MvPolynomial.coeff m01 p := by
    dsimp [purePart]
    simp [coeff_m01_x1, coeff_m01_x1sq, coeff_m01_x1cb, coeff_m01_x1qt]
  have hpure02 : MvPolynomial.coeff m02 purePart = MvPolynomial.coeff m02 p := by
    dsimp [purePart]
    simp [coeff_m02_x1, coeff_m02_x1sq, coeff_m02_x1cb, coeff_m02_x1qt]
  have hpure03 : MvPolynomial.coeff m03 purePart = MvPolynomial.coeff m03 p := by
    dsimp [purePart]
    simp [coeff_m03_x1, coeff_m03_x1sq, coeff_m03_x1cb, coeff_m03_x1qt]
  have hpure04 : MvPolynomial.coeff m04 purePart = MvPolynomial.coeff m04 p := by
    dsimp [purePart]
    simp [coeff_m04_x1, coeff_m04_x1sq, coeff_m04_x1cb, coeff_m04_x1qt]
  have hrQuartic : IsQuartic r := by
    calc
      r.totalDegree ≤ max p.totalDegree purePart.totalDegree := by
        dsimp [r]
        exact MvPolynomial.totalDegree_sub _ _
      _ ≤ 4 := max_le hp hpureQuartic
  have hr00 : MvPolynomial.coeff m00 r = 0 := by
    dsimp [r, purePart]
    rw [MvPolynomial.coeff_sub, h00, hpure00]
    ring
  have hr01 : MvPolynomial.coeff m01 r = 0 := by
    dsimp [r, purePart]
    rw [MvPolynomial.coeff_sub, hpure01]
    ring
  have hr02 : MvPolynomial.coeff m02 r = 0 := by
    dsimp [r, purePart]
    rw [MvPolynomial.coeff_sub, hpure02]
    ring
  have hr03 : MvPolynomial.coeff m03 r = 0 := by
    dsimp [r, purePart]
    rw [MvPolynomial.coeff_sub, hpure03]
    ring
  have hr04 : MvPolynomial.coeff m04 r = 0 := by
    dsimp [r, purePart]
    rw [MvPolynomial.coeff_sub, hpure04]
    ring
  let monomialImage : ∀ (s : Fin 2 →₀ ℕ) (rcoeff : ℝ),
      s.sum (fun _ e => e) ≤ 4 →
      1 ≤ s 0 →
      InAdmissibleImage u (MvPolynomial.monomial s rcoeff) := by
    intro s rcoeff hdeg hx0pos
    let e0 := s 0
    let e1 := s 1
    have hsum : s.sum (fun _ e => e) = s 0 + s 1 := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
    have hs : e0 + e1 ≤ 4 := by
      simpa [e0, e1, hsum] using hdeg
    by_cases he1zero : e1 = 0
    · by_cases he0one : e0 = 1
      · have hq : IsQuadratic (MvPolynomial.C rcoeff) := by
          change (MvPolynomial.C rcoeff : Poly).totalDegree ≤ 2
          simp
        have hmul : x0 * MvPolynomial.C rcoeff = MvPolynomial.C rcoeff * x0 := by
          ring_nf
        simpa [monomial_fin2_eq, e0, e1, he0one, he1zero, hmul] using
          (inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c0) (r := x0) (q := MvPolynomial.C rcoeff) h0 hq)
      · have he0ge : 2 ≤ e0 := by omega
        have hq : IsQuadratic (MvPolynomial.C rcoeff * x0 ^ (e0 - 2)) := by
          simpa using isQuadratic_C_mul_pow_pow rcoeff (e0 - 2) 0 (by omega)
        have hmul :
            x0 ^ 2 * (MvPolynomial.C rcoeff * x0 ^ (e0 - 2)) =
              MvPolynomial.C rcoeff * x0 ^ e0 := by
          calc
            x0 ^ 2 * (MvPolynomial.C rcoeff * x0 ^ (e0 - 2))
                = MvPolynomial.C rcoeff * (x0 ^ 2 * x0 ^ (e0 - 2)) := by
                    ring_nf
            _ = MvPolynomial.C rcoeff * x0 ^ e0 := by
                  rw [← pow_add, Nat.add_sub_of_le he0ge]
        simpa [monomial_fin2_eq, e0, e1, he1zero, hmul] using
          (inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c2) (r := x0 ^ 2)
            (q := MvPolynomial.C rcoeff * x0 ^ (e0 - 2)) h2 hq)
    · have he1pos : 1 ≤ e1 := by omega
      have hq :
          IsQuadratic ((MvPolynomial.C rcoeff * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1)) := by
        exact isQuadratic_C_mul_pow_pow rcoeff (e0 - 1) (e1 - 1) (by omega)
      have hmul :
          (x0 * x1 : Poly) * ((MvPolynomial.C rcoeff * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1)) =
            (MvPolynomial.C rcoeff * x0 ^ e0) * x1 ^ e1 := by
        calc
          (x0 * x1 : Poly) * ((MvPolynomial.C rcoeff * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1))
              = MvPolynomial.C rcoeff * (x0 * x0 ^ (e0 - 1)) * (x1 * x1 ^ (e1 - 1)) := by
                  ring_nf
          _ = MvPolynomial.C rcoeff * x0 ^ e0 * x1 ^ e1 := by
                have hx0pos' : 1 ≤ e0 := by simpa [e0] using hx0pos
                have hxpow : x0 * x0 ^ (e0 - 1) = x0 ^ e0 := by
                  simpa [Nat.sub_add_cancel hx0pos'] using (pow_succ' x0 (e0 - 1)).symm
                have hypow : x1 * x1 ^ (e1 - 1) = x1 ^ e1 := by
                  simpa [Nat.sub_add_cancel he1pos] using (pow_succ' x1 (e1 - 1)).symm
                simp [hxpow, hypow, mul_assoc]
      simpa [monomial_fin2_eq, e0, e1, hmul] using
        (inAdmissibleImage_of_relation_mul_low
          (u := u) (c := c3) (r := x0 * x1)
          (q := (MvPolynomial.C rcoeff * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1)) h3 hq)
  have himgR : InAdmissibleImage u r := by
    rw [← MvPolynomial.support_sum_monomial_coeff r]
    let P : Finset (Fin 2 →₀ ℕ) → Prop := fun S =>
      (∀ s ∈ S, s ∈ r.support) →
        InAdmissibleImage u (∑ s ∈ S, MvPolynomial.monomial s (MvPolynomial.coeff s r))
    have hP : P r.support := by
      refine Finset.induction_on r.support ?_ ?_
      · intro hsub
        simpa using inAdmissibleImage_zero u
      · intro s ss hsnot ih hsub
        rw [Finset.sum_insert hsnot]
        refine inAdmissibleImage_add u ?_ (ih ?_)
        · have hsdeg : s.sum (fun _ e => e) ≤ 4 :=
            (MvPolynomial.le_totalDegree (hsub s (by simp))).trans hrQuartic
          have hscoeff : MvPolynomial.coeff s r ≠ 0 :=
            MvPolynomial.mem_support_iff.mp (hsub s (by simp))
          have hs0pos : 1 ≤ s 0 := by
            by_contra hs0pos
            have hs0 : s 0 = 0 := by omega
            have hs1le : s 1 ≤ 4 := by
              have hs' : s 0 + s 1 ≤ 4 := by
                rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at hsdeg
                simpa [hs0] using hsdeg
              omega
            interval_cases hs1 : s 1
            · apply hscoeff
              have hsEq : s = m00 := by
                ext i
                fin_cases i <;> simp [m00, hs0, hs1]
              simpa [hsEq] using hr00
            · apply hscoeff
              have hsEq : s = m01 := by
                ext i
                fin_cases i <;> simp [m01, hs0, hs1]
              simpa [hsEq] using hr01
            · apply hscoeff
              have hsEq : s = m02 := by
                ext i
                fin_cases i <;> simp [m02, hs0, hs1]
              simpa [hsEq] using hr02
            · apply hscoeff
              have hsEq : s = m03 := by
                ext i
                fin_cases i <;> simp [m03, hs0, hs1]
              simpa [hsEq] using hr03
            · apply hscoeff
              have hsEq : s = m04 := by
                ext i
                fin_cases i <;> simp [m04, hs0, hs1]
              simpa [hsEq] using hr04
          exact monomialImage s (MvPolynomial.coeff s r) hsdeg hs0pos
        · intro t ht
          exact hsub t (by simp [ht])
    exact hP (fun s hs => hs)
  have hdecomp : p = purePart + r := by
    dsimp [r]
    ring
  exact hdecomp ▸ inAdmissibleImage_add u hpureImg himgR

theorem residual_eq_zero_of_relations_x0_x1PlusAX1sq_x0sq_x0x1
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {a : ℝ}
    (ha : a ≠ 0)
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1 + a • (x1 ^ 2 : Poly))
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 ^ 2)
    (h3 : ∑ i : Fin 4, c3 i • u i = x0 * x1)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  rcases hp with ⟨hpquartic, k, qs, hqdeg, hpq⟩
  let alpha : ℝ := ∑ i : Fin 4, (c2 i) ^ 2
  have hc2_ne : c2 ≠ 0 := by
    intro hc2
    have : (0 : Poly) = x0 ^ 2 := by
      simpa [hc2] using h2
    have hcoeff := congrArg (MvPolynomial.coeff m20) this
    simp [x0, m20, MvPolynomial.coeff_X_pow] at hcoeff
  have halpha_pos : 0 < alpha := sum_sq_pos_of_ne_zero c2 hc2_ne
  have halpha_nonneg : 0 ≤ alpha := le_of_lt halpha_pos
  let beta : Fin k → ℝ := fun i =>
    Real.sqrt (((MvPolynomial.coeff m00 (qs i)) ^ 2) / alpha)
  let delta : Fin k → ℝ := fun i =>
    Real.sqrt
      (((MvPolynomial.coeff m02 (qs i)
          - a * MvPolynomial.coeff m01 (qs i)
          + a ^ 2 * MvPolynomial.coeff m00 (qs i)) ^ 2) / alpha)
  let gamma : Fin k → ℝ := fun i => a * beta i - delta i / a
  let w : Fin k → RankFourVec := fun i =>
    affineDimOneX1sqTailKer c0 c2 (beta i) (gamma i)
  let imgPart : Poly := ∑ i : Fin k, ((qs i) ^ 2 - sigma (w i))
  have himgTerm :
      ∀ i : Fin k, InAdmissibleImage u ((qs i) ^ 2 - sigma (w i)) := by
    intro i
    have hquartic_i : IsQuartic ((qs i) ^ 2 - sigma (w i)) := by
      have hsqQuartic : IsQuartic ((qs i) ^ 2) := by
        calc
          ((qs i) ^ 2).totalDegree ≤ (qs i).totalDegree + (qs i).totalDegree := by
            simpa [pow_two] using MvPolynomial.totalDegree_mul (qs i) (qs i)
          _ ≤ (2 : ℕ) + 2 := add_le_add (hqdeg i) (hqdeg i)
          _ = 4 := by norm_num
      have hsigQuartic : IsQuartic (sigma (w i)) := by
        exact isQuartic_sigma_of_admissible ((affineDimOneX1sqTailKer_admissible c0 c2 (beta i) (gamma i)))
      calc
        (((qs i) ^ 2 - sigma (w i)) : Poly).totalDegree ≤
            max ((qs i) ^ 2).totalDegree (sigma (w i)).totalDegree := by
              exact MvPolynomial.totalDegree_sub _ _
        _ ≤ 4 := max_le hsqQuartic hsigQuartic
    have h00_i : MvPolynomial.coeff m00 ((qs i) ^ 2 - sigma (w i)) = 0 := by
      have hsdiv :
          0 ≤ ((MvPolynomial.coeff m00 (qs i)) ^ 2) / alpha := by
        positivity
      have hsig00 :
          MvPolynomial.coeff m00 (sigma (w i)) =
            (MvPolynomial.coeff m00 (qs i)) ^ 2 := by
        calc
          MvPolynomial.coeff m00 (sigma (w i))
              = alpha * (beta i) ^ 2 := by
                  dsimp [w]
                  exact coeff_m00_sigma_affineDimOneX1sqTailKer c0 c2 (beta i) (gamma i)
          _ = alpha * (((MvPolynomial.coeff m00 (qs i)) ^ 2) / alpha) := by
                rw [show (beta i) ^ 2 =
                    (((MvPolynomial.coeff m00 (qs i)) ^ 2) / alpha) by
                      dsimp [beta]
                      rw [Real.sq_sqrt hsdiv]]
          _ = (MvPolynomial.coeff m00 (qs i)) ^ 2 := by
                field_simp [alpha, halpha_pos.ne']
      calc
        MvPolynomial.coeff m00 ((qs i) ^ 2 - sigma (w i))
            = MvPolynomial.coeff m00 ((qs i) ^ 2) - MvPolynomial.coeff m00 (sigma (w i)) := by
                rw [MvPolynomial.coeff_sub]
        _ = (MvPolynomial.coeff m00 (qs i)) ^ 2 - MvPolynomial.coeff m00 (sigma (w i)) := by
              rw [coeff_m00_sq]
        _ = 0 := by simp [hsig00]
    have htail_i : x1sqTailFunctional a ((qs i) ^ 2 - sigma (w i)) = 0 := by
      have hsdiv :
          0 ≤ ((MvPolynomial.coeff m02 (qs i)
              - a * MvPolynomial.coeff m01 (qs i)
              + a ^ 2 * MvPolynomial.coeff m00 (qs i)) ^ 2) / alpha := by
        positivity
      have hsigTail :
          x1sqTailFunctional a (sigma (w i)) =
            (MvPolynomial.coeff m02 (qs i)
              - a * MvPolynomial.coeff m01 (qs i)
              + a ^ 2 * MvPolynomial.coeff m00 (qs i)) ^ 2 := by
        calc
          x1sqTailFunctional a (sigma (w i))
              = alpha * (a ^ 2 * beta i - a * gamma i) ^ 2 := by
                  dsimp [w]
                  exact x1sqTailFunctional_sigma_affineDimOneX1sqTailKer
                    a c0 c2 (beta i) (gamma i)
          _ = alpha *
              ((((MvPolynomial.coeff m02 (qs i)
                  - a * MvPolynomial.coeff m01 (qs i)
                  + a ^ 2 * MvPolynomial.coeff m00 (qs i)) ^ 2) / alpha)) := by
                have hinner :
                    a ^ 2 * beta i - a * gamma i = delta i := by
                  dsimp [gamma]
                  field_simp [ha]
                  ring
                rw [hinner, show (delta i) ^ 2 =
                    (((MvPolynomial.coeff m02 (qs i)
                        - a * MvPolynomial.coeff m01 (qs i)
                        + a ^ 2 * MvPolynomial.coeff m00 (qs i)) ^ 2) / alpha) by
                      dsimp [delta]
                      rw [Real.sq_sqrt hsdiv]]
          _ = (MvPolynomial.coeff m02 (qs i)
                - a * MvPolynomial.coeff m01 (qs i)
                + a ^ 2 * MvPolynomial.coeff m00 (qs i)) ^ 2 := by
                field_simp [alpha, halpha_pos.ne']
      calc
        x1sqTailFunctional a ((qs i) ^ 2 - sigma (w i))
            = x1sqTailFunctional a ((qs i) ^ 2) - x1sqTailFunctional a (sigma (w i)) := by
                rw [x1sqTailFunctional_sub]
        _ = (MvPolynomial.coeff m02 (qs i)
              - a * MvPolynomial.coeff m01 (qs i)
              + a ^ 2 * MvPolynomial.coeff m00 (qs i)) ^ 2
            - x1sqTailFunctional a (sigma (w i)) := by
              rw [x1sqTailFunctional_sq_of_quadratic_eq a (qs i) (hqdeg i)]
        _ = 0 := by simp [hsigTail]
    exact quartic_in_image_of_relations_x0_x1PlusAX1sq_x0sq_x0x1_of_coeff_m00_x1sqTail_zero
      h0 h1 h2 h3 hquartic_i h00_i htail_i
  have himgPart : InAdmissibleImage u imgPart := by
    classical
    unfold imgPart
    refine Finset.induction_on (Finset.univ : Finset (Fin k)) ?_ ?_
    · simpa using inAdmissibleImage_zero u
    · intro i s hi ih
      rw [Finset.sum_insert hi]
      exact inAdmissibleImage_add u (himgTerm i) ih
  have hker : ∀ i ∈ (Finset.univ : Finset (Fin k)), InAdmissibleKer u (w i) := by
    intro i hi
    dsimp [w]
    exact affineDimOneX1sqTailKer_inKer h0 h2
  have hdecomp :
      p = imgPart + Finset.sum (Finset.univ : Finset (Fin k)) (fun i => sigma (w i)) := by
    calc
      p = ∑ i : Fin k, (qs i) ^ 2 := hpq
      _ = ∑ i : Fin k, (((qs i) ^ 2 - sigma (w i)) + sigma (w i)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
      _ = imgPart + Finset.sum (Finset.univ : Finset (Fin k)) (fun i => sigma (w i)) := by
            simp [imgPart]
  exact admissible_image_plus_indexed_sigma_family_residual_eq_zero
    (B := B) (u := u) (uImg := u) hu hsocp
    (imageOrthogonalResidual_self (B := B) hsocp.1)
    himgPart hker hdecomp

theorem residual_eq_zero_of_equiv_relations_x0_x1PlusAX1sq_x0sq_x0x1
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    {a : ℝ}
    (ha : a ≠ 0)
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1 + a • (x1 ^ 2 : Poly))
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = x0 ^ 2)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = x0 * x1) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e)
      (heQuad := fun {_} hpq => heQuad hpq)
      (heQuartic := fun {_} hpq => heQuartic hpq)
      hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_x0_x1PlusAX1sq_x0sq_x0x1
      (B := B0) (u := mapVec e.toAlgHom u) hu0 ha h0 h1 h2 h3 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_x0_x1PlusAX1sq_x0sq_x0x1Plane
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {a r s t w : ℝ}
    (ha : a ≠ 0)
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = x1 + a • (x1 ^ 2 : Poly))
    (h2 : ∑ i : Fin 4, c2 i • u i = r • (x0 ^ 2 : Poly) + s • (x0 * x1))
    (h3 : ∑ i : Fin 4, c3 i • u i = t • (x0 ^ 2 : Poly) + w • (x0 * x1))
    (hdet : r * w - s * t ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let det : ℝ := r * w - s * t
  have hdet0 : det ≠ 0 := by
    simpa [det] using hdet
  let c2' : Fin 4 → ℝ := fun i => (w / det) * c2 i + (-s / det) * c3 i
  let c3' : Fin 4 → ℝ := fun i => (-t / det) * c2 i + (r / det) * c3 i
  have hcoeff20 : (w / det) * r + (-s / det) * t = 1 := by
    field_simp [det, hdet0]
    ring
  have hcoeff21 : (w / det) * s + (-s / det) * w = 0 := by
    field_simp [det, hdet0]
    ring
  have hcoeff30 : (-t / det) * r + (r / det) * t = 0 := by
    field_simp [det, hdet0]
    ring
  have hcoeff31 : (-t / det) * s + (r / det) * w = 1 := by
    field_simp [det, hdet0]
    ring
  have h2' : ∑ i : Fin 4, c2' i • u i = x0 ^ 2 := by
    change relationPoly u c2' = x0 ^ 2
    calc
      relationPoly u c2'
          = relationPoly u ((w / det) • c2) + relationPoly u ((-s / det) • c3) := by
              rw [show c2' = (w / det) • c2 + (-s / det) • c3 by
                funext i
                simp [c2']
              , relationPoly_add]
      _ = (w / det) • relationPoly u c2 + (-s / det) • relationPoly u c3 := by
            rw [relationPoly_smul, relationPoly_smul]
      _ = (w / det) • (r • (x0 ^ 2 : Poly) + s • (x0 * x1)) +
            (-s / det) • (t • (x0 ^ 2 : Poly) + w • (x0 * x1)) := by
              rw [show relationPoly u c2 = ∑ i : Fin 4, c2 i • u i by rfl,
                show relationPoly u c3 = ∑ i : Fin 4, c3 i • u i by rfl,
                h2, h3]
      _ = ((w / det) * r + (-s / det) * t) • (x0 ^ 2 : Poly) +
            ((w / det) * s + (-s / det) * w) • (x0 * x1) := by
              simp [smul_add, smul_smul, add_smul, add_assoc, add_left_comm, mul_comm]
      _ = x0 ^ 2 := by
            rw [hcoeff20, hcoeff21]
            simp
  have h3' : ∑ i : Fin 4, c3' i • u i = x0 * x1 := by
    change relationPoly u c3' = x0 * x1
    calc
      relationPoly u c3'
          = relationPoly u ((-t / det) • c2) + relationPoly u ((r / det) • c3) := by
              rw [show c3' = (-t / det) • c2 + (r / det) • c3 by
                funext i
                simp [c3']
              , relationPoly_add]
      _ = (-t / det) • relationPoly u c2 + (r / det) • relationPoly u c3 := by
            rw [relationPoly_smul, relationPoly_smul]
      _ = (-t / det) • (r • (x0 ^ 2 : Poly) + s • (x0 * x1)) +
            (r / det) • (t • (x0 ^ 2 : Poly) + w • (x0 * x1)) := by
              rw [show relationPoly u c2 = ∑ i : Fin 4, c2 i • u i by rfl,
                show relationPoly u c3 = ∑ i : Fin 4, c3 i • u i by rfl,
                h2, h3]
      _ = ((-t / det) * r + (r / det) * t) • (x0 ^ 2 : Poly) +
            ((-t / det) * s + (r / det) * w) • (x0 * x1) := by
              simp [smul_add, smul_smul, add_smul, add_assoc, add_left_comm, add_comm, mul_comm]
      _ = x0 * x1 := by
            rw [hcoeff30, hcoeff31]
            simp
  exact residual_eq_zero_of_relations_x0_x1PlusAX1sq_x0sq_x0x1
    (B := B) (u := u) hu ha h0 h1 h2' h3' hp hsocp

theorem residual_eq_zero_of_equiv_relations_x0_x1PlusAX1sq_x0sq_x0x1Plane
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    {a r s t w : ℝ}
    (ha : a ≠ 0)
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = x1 + a • (x1 ^ 2 : Poly))
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = r • (x0 ^ 2 : Poly) + s • (x0 * x1))
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = t • (x0 ^ 2 : Poly) + w • (x0 * x1))
    (hdet : r * w - s * t ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e)
      (heQuad := fun {_} hpq => heQuad hpq)
      (heQuartic := fun {_} hpq => heQuartic hpq)
      hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_x0_x1PlusAX1sq_x0sq_x0x1Plane
      (B := B0) (u := mapVec e.toAlgHom u) hu0 ha h0 h1 h2 h3 hdet hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

private theorem coeff_m00_one :
    MvPolynomial.coeff m00 (1 : Poly) = 1 := by
  simp [m00]

private theorem coeff_m03_one :
    MvPolynomial.coeff m03 (1 : Poly) = 0 := by
  rw [MvPolynomial.coeff_one]
  have h : (0 : Fin 2 →₀ ℕ) ≠ m03 := by
    intro h0
    have h1 := congrArg (fun s : Fin 2 →₀ ℕ => s 1) h0
    simp [m03] at h1
  simp [h]

private theorem coeff_m04_one :
    MvPolynomial.coeff m04 (1 : Poly) = 0 := by
  rw [MvPolynomial.coeff_one]
  have h : (0 : Fin 2 →₀ ℕ) ≠ m04 := by
    intro h0
    have h1 := congrArg (fun s : Fin 2 →₀ ℕ => s 1) h0
    simp [m04] at h1
  simp [h]

private def onePlusX1sqFunctional1 (a : ℝ) (p : Poly) : ℝ :=
  MvPolynomial.coeff m03 p - a * MvPolynomial.coeff m01 p

private def onePlusX1sqFunctional2 (a : ℝ) (p : Poly) : ℝ :=
  MvPolynomial.coeff m04 p - a * MvPolynomial.coeff m02 p + a ^ 2 * MvPolynomial.coeff m00 p

private theorem onePlusX1sqFunctional1_sq_of_quadratic_eq
    (a : ℝ) (q : Poly) (hq : IsQuadratic q) :
    onePlusX1sqFunctional1 a (q ^ 2) =
      2 * MvPolynomial.coeff m01 q * (MvPolynomial.coeff m02 q - a * MvPolynomial.coeff m00 q) := by
  rw [onePlusX1sqFunctional1, coeff_m03_sq_of_quadratic_eq q hq,
    coeff_m01_sq_of_quadratic_eq q hq]
  ring

private theorem onePlusX1sqFunctional2_sq_of_quadratic_eq
    (a : ℝ) (q : Poly) (hq : IsQuadratic q) :
    onePlusX1sqFunctional2 a (q ^ 2) =
      (MvPolynomial.coeff m02 q - a * MvPolynomial.coeff m00 q) ^ 2 -
        a * (MvPolynomial.coeff m01 q) ^ 2 := by
  rw [onePlusX1sqFunctional2, coeff_m04_sq_of_quadratic_eq q hq,
    coeff_m02_sq_of_quadratic_eq q hq, coeff_m00_sq]
  ring

private theorem pureX1Quartic_eq_onePlusAX1sq_mul
    (a b0 b1 b2 b3 b4 : ℝ)
    (h13 : b3 - a * b1 = 0)
    (h24 : b4 - a * b2 + a ^ 2 * b0 = 0) :
    b0 • (1 : Poly) + b1 • x1 + b2 • (x1 ^ 2 : Poly) + b3 • (x1 ^ 3 : Poly) + b4 • (x1 ^ 4 : Poly) =
      ((1 : Poly) + a • (x1 ^ 2 : Poly)) *
        (MvPolynomial.C b0 +
          MvPolynomial.C b1 * x1 +
          (MvPolynomial.C b2 - MvPolynomial.C a * MvPolynomial.C b0) * (x1 ^ 2)) := by
  have hb3 : b3 = a * b1 := by linarith
  have hb4 : b4 = a * b2 - a ^ 2 * b0 := by linarith
  rw [hb3, hb4]
  simp [MvPolynomial.smul_eq_C_mul]
  ring

private theorem inAdmissibleImage_pureX1Quartic_of_onePlusX1sqFunctional_zero
    {u : RankFourVec}
    {c1 : Fin 4 → ℝ}
    {a : ℝ}
    (h1 : ∑ i : Fin 4, c1 i • u i = (1 : Poly) + a • (x1 ^ 2 : Poly))
    {b0 b1 b2 b3 b4 : ℝ}
    (h13 : b3 - a * b1 = 0)
    (h24 : b4 - a * b2 + a ^ 2 * b0 = 0) :
    InAdmissibleImage u
      (b0 • (1 : Poly) + b1 • x1 + b2 • (x1 ^ 2 : Poly) + b3 • (x1 ^ 3 : Poly) + b4 • (x1 ^ 4 : Poly)) := by
  let q : Poly :=
    MvPolynomial.C b0 +
      MvPolynomial.C b1 * x1 +
      (MvPolynomial.C b2 - MvPolynomial.C a * MvPolynomial.C b0) * (x1 ^ 2)
  have hq : IsQuadratic q := by
    have hq0 : IsQuadratic (MvPolynomial.C b0) := by
      change (MvPolynomial.C b0 : Poly).totalDegree ≤ 2
      simp
    have hq1 : IsQuadratic (MvPolynomial.C b1 * x1) := by
      simpa using isQuadratic_C_mul_pow_pow b1 0 1 (by omega)
    have hq2 :
        IsQuadratic ((MvPolynomial.C b2 - MvPolynomial.C a * MvPolynomial.C b0) * (x1 ^ 2)) := by
      have hq2' := isQuadratic_C_mul_pow_pow (b2 - a * b0) 0 2 (by omega)
      have hpow0 :
          (MvPolynomial.C (b2 - a * b0) * x0 ^ 0 * x1 ^ 2 : Poly) =
            ((MvPolynomial.C (b2 - a * b0) : Poly) * (x1 ^ 2)) := by
        simp [x0]
      have hq2'' :
          IsQuadratic ((MvPolynomial.C (b2 - a * b0) : Poly) * (x1 ^ 2)) := by
        exact hpow0 ▸ hq2'
      have hcoef :
          (MvPolynomial.C (b2 - a * b0) : Poly) =
            MvPolynomial.C b2 - MvPolynomial.C a * MvPolynomial.C b0 := by
        simp [sub_eq_add_neg]
      have hmul :
          ((MvPolynomial.C (b2 - a * b0) : Poly) * (x1 ^ 2)) =
            ((MvPolynomial.C b2 - MvPolynomial.C a * MvPolynomial.C b0) * (x1 ^ 2)) := by
        rw [hcoef]
      exact hmul.symm ▸ hq2''
    have hq01 :
        IsQuadratic (MvPolynomial.C b0 + MvPolynomial.C b1 * x1) := by
      calc
        (MvPolynomial.C b0 + MvPolynomial.C b1 * x1).totalDegree ≤
            max (MvPolynomial.C b0).totalDegree (MvPolynomial.C b1 * x1).totalDegree := by
              exact MvPolynomial.totalDegree_add _ _
        _ ≤ 2 := max_le hq0 hq1
    dsimp [q]
    calc
      (MvPolynomial.C b0 + MvPolynomial.C b1 * x1 +
          (MvPolynomial.C b2 - MvPolynomial.C a * MvPolynomial.C b0) * (x1 ^ 2)).totalDegree ≤
          max (MvPolynomial.C b0 + MvPolynomial.C b1 * x1).totalDegree
            ((MvPolynomial.C b2 - MvPolynomial.C a * MvPolynomial.C b0) * (x1 ^ 2)).totalDegree := by
              exact MvPolynomial.totalDegree_add _ _
      _ ≤ 2 := max_le hq01 hq2
  have himg :
      InAdmissibleImage u (((1 : Poly) + a • (x1 ^ 2 : Poly)) * q) := by
    exact inAdmissibleImage_of_relation_mul_low
      (u := u) (c := c1) (r := (1 : Poly) + a • (x1 ^ 2 : Poly))
      (q := q) h1 hq
  dsimp [q] at himg ⊢
  exact (pureX1Quartic_eq_onePlusAX1sq_mul a b0 b1 b2 b3 b4 h13 h24).symm ▸ himg

private theorem onePlusX1sqFunctional1_add
    (a : ℝ) (p q : Poly) :
    onePlusX1sqFunctional1 a (p + q) =
      onePlusX1sqFunctional1 a p + onePlusX1sqFunctional1 a q := by
  unfold onePlusX1sqFunctional1
  repeat' rw [MvPolynomial.coeff_add]
  ring

private theorem onePlusX1sqFunctional1_sub
    (a : ℝ) (p q : Poly) :
    onePlusX1sqFunctional1 a (p - q) =
      onePlusX1sqFunctional1 a p - onePlusX1sqFunctional1 a q := by
  unfold onePlusX1sqFunctional1
  repeat' rw [MvPolynomial.coeff_sub]
  ring

private theorem onePlusX1sqFunctional2_add
    (a : ℝ) (p q : Poly) :
    onePlusX1sqFunctional2 a (p + q) =
      onePlusX1sqFunctional2 a p + onePlusX1sqFunctional2 a q := by
  unfold onePlusX1sqFunctional2
  repeat' rw [MvPolynomial.coeff_add]
  ring

private theorem onePlusX1sqFunctional2_sub
    (a : ℝ) (p q : Poly) :
    onePlusX1sqFunctional2 a (p - q) =
      onePlusX1sqFunctional2 a p - onePlusX1sqFunctional2 a q := by
  unfold onePlusX1sqFunctional2
  repeat' rw [MvPolynomial.coeff_sub]
  ring

private def affineDimOneConstX1sqKer
    (c2 c3 : Fin 4 → ℝ) (β γ : ℝ) : RankFourVec :=
  relationDirection (-c3) (β • x0 + γ • (x0 * x1 : Poly)) +
    relationDirection c2 (β • x1 + γ • (x1 ^ 2 : Poly))

private theorem affineDimOneConstX1sqKer_admissible
    (c2 c3 : Fin 4 → ℝ) (β γ : ℝ) :
    IsAdmissibleDirection (affineDimOneConstX1sqKer c2 c3 β γ) := by
  refine isAdmissibleDirection_add ?_ ?_
  · refine relationDirection_admissible (-c3) ?_
    have h0 : IsQuadratic (β • x0) := by
      exact (MvPolynomial.totalDegree_smul_le β x0).trans (by simp [x0])
    have hcross : IsQuadratic (x0 * x1 : Poly) := by
      calc
        (x0 * x1 : Poly).totalDegree ≤ x0.totalDegree + x1.totalDegree := by
          exact MvPolynomial.totalDegree_mul _ _
        _ ≤ 2 := by simp [x0, x1]
    have h1 : IsQuadratic (γ • (x0 * x1 : Poly)) := by
      exact (MvPolynomial.totalDegree_smul_le γ (x0 * x1 : Poly)).trans hcross
    calc
      (β • x0 + γ • (x0 * x1 : Poly)).totalDegree ≤
          max (β • x0).totalDegree (γ • (x0 * x1 : Poly)).totalDegree := by
            exact MvPolynomial.totalDegree_add _ _
      _ ≤ 2 := max_le h0 h1
  · refine relationDirection_admissible c2 ?_
    have h0 : IsQuadratic (β • x1) := by
      exact (MvPolynomial.totalDegree_smul_le β x1).trans (by simp [x1])
    have h1 : IsQuadratic (γ • (x1 ^ 2 : Poly)) := by
      exact (MvPolynomial.totalDegree_smul_le γ (x1 ^ 2 : Poly)).trans (by simp [x1])
    calc
      (β • x1 + γ • (x1 ^ 2 : Poly)).totalDegree ≤
          max (β • x1).totalDegree (γ • (x1 ^ 2 : Poly)).totalDegree := by
            exact MvPolynomial.totalDegree_add _ _
      _ ≤ 2 := max_le h0 h1

private theorem affineDimOneConstX1sqKer_inKer
    {u : RankFourVec} {c2 c3 : Fin 4 → ℝ} {β γ : ℝ}
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 ^ 2)
    (h3 : ∑ i : Fin 4, c3 i • u i = x0 * x1) :
    InAdmissibleKer u (affineDimOneConstX1sqKer c2 c3 β γ) := by
  refine ⟨affineDimOneConstX1sqKer_admissible c2 c3 β γ, ?_⟩
  rw [affineDimOneConstX1sqKer, A_add_right_local, A_relationDirection, A_relationDirection]
  have h3neg : ∑ i : Fin 4, (-c3 i) • u i = -(x0 * x1 : Poly) := by
    simpa using congrArg (fun q : Poly => -q) h3
  have h3neg' : ∑ i : Fin 4, (-c3) i • u i = -(x0 * x1 : Poly) := by
    simpa using h3neg
  rw [h3neg', h2]
  simp [MvPolynomial.smul_eq_C_mul]
  ring_nf

private theorem onePlusX1sqFunctional1_sigma_affineDimOneConstX1sqKer
    (a : ℝ) (c2 c3 : Fin 4 → ℝ) (β γ : ℝ) :
    onePlusX1sqFunctional1 a (sigma (affineDimOneConstX1sqKer c2 c3 β γ)) =
      (∑ i : Fin 4, (c2 i) ^ 2) * (2 * β * γ) := by
  have hcoord : ∀ i : Fin 4,
      onePlusX1sqFunctional1 a ((affineDimOneConstX1sqKer c2 c3 β γ i) ^ 2) =
        (c2 i) ^ 2 * (2 * β * γ) := by
    intro i
    rw [onePlusX1sqFunctional1_sq_of_quadratic_eq a
      (affineDimOneConstX1sqKer c2 c3 β γ i)
      ((affineDimOneConstX1sqKer_admissible c2 c3 β γ) i)]
    have hm00 :
        MvPolynomial.coeff m00 (affineDimOneConstX1sqKer c2 c3 β γ i) = 0 := by
      rw [affineDimOneConstX1sqKer]
      simp [relationDirection, m00, x0, coeff_m00_x1, coeff_m00_x1sq, coeff_m00_X0_mul_x1]
    have hm01 :
        MvPolynomial.coeff m01 (affineDimOneConstX1sqKer c2 c3 β γ i) = (c2 i) * β := by
      rw [affineDimOneConstX1sqKer]
      simp [relationDirection, m01, x0, coeff_m01_x1, coeff_m01_x1sq, coeff_m01_X0_mul_x1]
    have hm02 :
        MvPolynomial.coeff m02 (affineDimOneConstX1sqKer c2 c3 β γ i) = (c2 i) * γ := by
      rw [affineDimOneConstX1sqKer]
      simp [relationDirection, m02, x0, coeff_m02_x1, coeff_m02_x1sq, coeff_m02_X0_mul_x1]
    rw [hm00, hm01, hm02]
    ring
  rw [sigma, Fin.sum_univ_four]
  repeat' rw [onePlusX1sqFunctional1_add]
  rw [hcoord 0, hcoord 1, hcoord 2, hcoord 3]
  rw [Fin.sum_univ_four]
  ring_nf

private theorem onePlusX1sqFunctional2_sigma_affineDimOneConstX1sqKer
    (a : ℝ) (c2 c3 : Fin 4 → ℝ) (β γ : ℝ) :
    onePlusX1sqFunctional2 a (sigma (affineDimOneConstX1sqKer c2 c3 β γ)) =
      (∑ i : Fin 4, (c2 i) ^ 2) * (γ ^ 2 - a * β ^ 2) := by
  have hcoord : ∀ i : Fin 4,
      onePlusX1sqFunctional2 a ((affineDimOneConstX1sqKer c2 c3 β γ i) ^ 2) =
        (c2 i) ^ 2 * (γ ^ 2 - a * β ^ 2) := by
    intro i
    rw [onePlusX1sqFunctional2_sq_of_quadratic_eq a
      (affineDimOneConstX1sqKer c2 c3 β γ i)
      ((affineDimOneConstX1sqKer_admissible c2 c3 β γ) i)]
    have hm00 :
        MvPolynomial.coeff m00 (affineDimOneConstX1sqKer c2 c3 β γ i) = 0 := by
      rw [affineDimOneConstX1sqKer]
      simp [relationDirection, m00, x0, coeff_m00_x1, coeff_m00_x1sq, coeff_m00_X0_mul_x1]
    have hm01 :
        MvPolynomial.coeff m01 (affineDimOneConstX1sqKer c2 c3 β γ i) = (c2 i) * β := by
      rw [affineDimOneConstX1sqKer]
      simp [relationDirection, m01, x0, coeff_m01_x1, coeff_m01_x1sq, coeff_m01_X0_mul_x1]
    have hm02 :
        MvPolynomial.coeff m02 (affineDimOneConstX1sqKer c2 c3 β γ i) = (c2 i) * γ := by
      rw [affineDimOneConstX1sqKer]
      simp [relationDirection, m02, x0, coeff_m02_x1, coeff_m02_x1sq, coeff_m02_X0_mul_x1]
    rw [hm00, hm01, hm02]
    ring
  rw [sigma, Fin.sum_univ_four]
  repeat' rw [onePlusX1sqFunctional2_add]
  rw [hcoord 0, hcoord 1, hcoord 2, hcoord 3]
  rw [Fin.sum_univ_four]
  ring_nf

theorem quartic_in_image_of_relations_x0_onePlusAX1sq_x0sq_x0x1_of_tail_zero
    {u : RankFourVec}
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {a : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = (1 : Poly) + a • (x1 ^ 2 : Poly))
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 ^ 2)
    (h3 : ∑ i : Fin 4, c3 i • u i = x0 * x1)
    {p : Poly} (hp : IsQuartic p)
    (htail1 : onePlusX1sqFunctional1 a p = 0)
    (htail2 : onePlusX1sqFunctional2 a p = 0) :
    InAdmissibleImage u p := by
  classical
  let purePart : Poly :=
    MvPolynomial.coeff m00 p • (1 : Poly) +
      MvPolynomial.coeff m01 p • x1 +
        MvPolynomial.coeff m02 p • (x1 ^ 2 : Poly) +
          MvPolynomial.coeff m03 p • (x1 ^ 3 : Poly) +
            MvPolynomial.coeff m04 p • (x1 ^ 4 : Poly)
  have hpureQuartic : IsQuartic purePart := by
    change purePart.totalDegree ≤ 4
    have h0deg : IsQuartic (MvPolynomial.coeff m00 p • (1 : Poly)) := by
      exact (MvPolynomial.totalDegree_smul_le _ (1 : Poly)).trans (by simp)
    have h1deg : IsQuartic (MvPolynomial.coeff m01 p • x1) := by
      exact (MvPolynomial.totalDegree_smul_le _ x1).trans (by simp [x1])
    have h2deg : IsQuartic (MvPolynomial.coeff m02 p • (x1 ^ 2 : Poly)) := by
      exact (MvPolynomial.totalDegree_smul_le _ (x1 ^ 2 : Poly)).trans (by simp [x1])
    have h3deg : IsQuartic (MvPolynomial.coeff m03 p • (x1 ^ 3 : Poly)) := by
      exact (MvPolynomial.totalDegree_smul_le _ (x1 ^ 3 : Poly)).trans (by simp [x1])
    have h4deg : IsQuartic (MvPolynomial.coeff m04 p • (x1 ^ 4 : Poly)) := by
      exact (MvPolynomial.totalDegree_smul_le _ (x1 ^ 4 : Poly)).trans (by simp [x1])
    have h01 :
        IsQuartic
          (MvPolynomial.coeff m00 p • (1 : Poly) + MvPolynomial.coeff m01 p • x1) := by
      calc
        (MvPolynomial.coeff m00 p • (1 : Poly) + MvPolynomial.coeff m01 p • x1).totalDegree ≤
            max (MvPolynomial.coeff m00 p • (1 : Poly)).totalDegree
              (MvPolynomial.coeff m01 p • x1).totalDegree := by
                exact MvPolynomial.totalDegree_add _ _
        _ ≤ 4 := max_le h0deg h1deg
    have h23 :
        IsQuartic
          (MvPolynomial.coeff m02 p • (x1 ^ 2 : Poly) +
            MvPolynomial.coeff m03 p • (x1 ^ 3 : Poly)) := by
      calc
        (MvPolynomial.coeff m02 p • (x1 ^ 2 : Poly) +
            MvPolynomial.coeff m03 p • (x1 ^ 3 : Poly)).totalDegree ≤
            max (MvPolynomial.coeff m02 p • (x1 ^ 2 : Poly)).totalDegree
              (MvPolynomial.coeff m03 p • (x1 ^ 3 : Poly)).totalDegree := by
                exact MvPolynomial.totalDegree_add _ _
        _ ≤ 4 := max_le h2deg h3deg
    have h012 :
        IsQuartic
          ((MvPolynomial.coeff m00 p • (1 : Poly) + MvPolynomial.coeff m01 p • x1) +
            MvPolynomial.coeff m02 p • (x1 ^ 2 : Poly)) := by
      calc
        ((MvPolynomial.coeff m00 p • (1 : Poly) + MvPolynomial.coeff m01 p • x1) +
            MvPolynomial.coeff m02 p • (x1 ^ 2 : Poly)).totalDegree ≤
            max (MvPolynomial.coeff m00 p • (1 : Poly) + MvPolynomial.coeff m01 p • x1).totalDegree
              (MvPolynomial.coeff m02 p • (x1 ^ 2 : Poly)).totalDegree := by
                exact MvPolynomial.totalDegree_add _ _
        _ ≤ 4 := max_le h01 h2deg
    have h0123 :
        IsQuartic
          (((MvPolynomial.coeff m00 p • (1 : Poly) + MvPolynomial.coeff m01 p • x1) +
              MvPolynomial.coeff m02 p • (x1 ^ 2 : Poly)) +
            MvPolynomial.coeff m03 p • (x1 ^ 3 : Poly)) := by
      calc
        (((MvPolynomial.coeff m00 p • (1 : Poly) + MvPolynomial.coeff m01 p • x1) +
              MvPolynomial.coeff m02 p • (x1 ^ 2 : Poly)) +
            MvPolynomial.coeff m03 p • (x1 ^ 3 : Poly)).totalDegree ≤
            max ((MvPolynomial.coeff m00 p • (1 : Poly) + MvPolynomial.coeff m01 p • x1) +
                MvPolynomial.coeff m02 p • (x1 ^ 2 : Poly)).totalDegree
              (MvPolynomial.coeff m03 p • (x1 ^ 3 : Poly)).totalDegree := by
                exact MvPolynomial.totalDegree_add _ _
        _ ≤ 4 := max_le h012 h3deg
    dsimp [purePart]
    calc
      ((((MvPolynomial.coeff m00 p • (1 : Poly) + MvPolynomial.coeff m01 p • x1) +
              MvPolynomial.coeff m02 p • (x1 ^ 2 : Poly)) +
            MvPolynomial.coeff m03 p • (x1 ^ 3 : Poly)) +
            MvPolynomial.coeff m04 p • (x1 ^ 4 : Poly)).totalDegree ≤
          max (((MvPolynomial.coeff m00 p • (1 : Poly) + MvPolynomial.coeff m01 p • x1) +
                MvPolynomial.coeff m02 p • (x1 ^ 2 : Poly)) +
                MvPolynomial.coeff m03 p • (x1 ^ 3 : Poly)).totalDegree
            (MvPolynomial.coeff m04 p • (x1 ^ 4 : Poly)).totalDegree := by
              exact MvPolynomial.totalDegree_add _ _
      _ ≤ 4 := max_le h0123 h4deg
  have htail1Pure :
      MvPolynomial.coeff m03 p - a * MvPolynomial.coeff m01 p = 0 := by
    simpa [onePlusX1sqFunctional1] using htail1
  have htail2Pure :
      MvPolynomial.coeff m04 p - a * MvPolynomial.coeff m02 p + a ^ 2 * MvPolynomial.coeff m00 p = 0 := by
    simpa [onePlusX1sqFunctional2] using htail2
  have hpureImg : InAdmissibleImage u purePart := by
    dsimp [purePart]
    exact inAdmissibleImage_pureX1Quartic_of_onePlusX1sqFunctional_zero h1 htail1Pure htail2Pure
  let r : Poly := p - purePart
  have hpure00 : MvPolynomial.coeff m00 purePart = MvPolynomial.coeff m00 p := by
    dsimp [purePart]
    simp [coeff_m00_x1, coeff_m00_x1sq, coeff_m00_x1cb, coeff_m00_x1qt]
  have hpure01 : MvPolynomial.coeff m01 purePart = MvPolynomial.coeff m01 p := by
    dsimp [purePart]
    simp [coeff_m01_one, coeff_m01_x1, coeff_m01_x1sq, coeff_m01_x1cb, coeff_m01_x1qt]
  have hpure02 : MvPolynomial.coeff m02 purePart = MvPolynomial.coeff m02 p := by
    dsimp [purePart]
    simp [coeff_m02_one, coeff_m02_x1, coeff_m02_x1sq, coeff_m02_x1cb, coeff_m02_x1qt]
  have hpure03 : MvPolynomial.coeff m03 purePart = MvPolynomial.coeff m03 p := by
    dsimp [purePart]
    simp [coeff_m03_one, coeff_m03_x1, coeff_m03_x1sq, coeff_m03_x1cb, coeff_m03_x1qt]
  have hpure04 : MvPolynomial.coeff m04 purePart = MvPolynomial.coeff m04 p := by
    dsimp [purePart]
    simp [coeff_m04_one, coeff_m04_x1, coeff_m04_x1sq, coeff_m04_x1cb, coeff_m04_x1qt]
  have hrQuartic : IsQuartic r := by
    calc
      r.totalDegree ≤ max p.totalDegree purePart.totalDegree := by
        dsimp [r]
        exact MvPolynomial.totalDegree_sub _ _
      _ ≤ 4 := max_le hp hpureQuartic
  have hr00 : MvPolynomial.coeff m00 r = 0 := by
    dsimp [r, purePart]
    rw [MvPolynomial.coeff_sub, hpure00]
    ring
  have hr01 : MvPolynomial.coeff m01 r = 0 := by
    dsimp [r, purePart]
    rw [MvPolynomial.coeff_sub, hpure01]
    ring
  have hr02 : MvPolynomial.coeff m02 r = 0 := by
    dsimp [r, purePart]
    rw [MvPolynomial.coeff_sub, hpure02]
    ring
  have hr03 : MvPolynomial.coeff m03 r = 0 := by
    dsimp [r, purePart]
    rw [MvPolynomial.coeff_sub, hpure03]
    ring
  have hr04 : MvPolynomial.coeff m04 r = 0 := by
    dsimp [r, purePart]
    rw [MvPolynomial.coeff_sub, hpure04]
    ring
  let monomialImage : ∀ (s : Fin 2 →₀ ℕ) (rcoeff : ℝ),
      s.sum (fun _ e => e) ≤ 4 →
      1 ≤ s 0 →
      InAdmissibleImage u (MvPolynomial.monomial s rcoeff) := by
    intro s rcoeff hdeg hx0pos
    let e0 := s 0
    let e1 := s 1
    have hsum : s.sum (fun _ e => e) = s 0 + s 1 := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
    have hs : e0 + e1 ≤ 4 := by
      simpa [e0, e1, hsum] using hdeg
    by_cases he1zero : e1 = 0
    · by_cases he0one : e0 = 1
      · have hq : IsQuadratic (MvPolynomial.C rcoeff) := by
          change (MvPolynomial.C rcoeff : Poly).totalDegree ≤ 2
          simp
        have hmul : x0 * MvPolynomial.C rcoeff = MvPolynomial.C rcoeff * x0 := by
          ring_nf
        simpa [monomial_fin2_eq, e0, e1, he0one, he1zero, hmul] using
          (inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c0) (r := x0) (q := MvPolynomial.C rcoeff) h0 hq)
      · have he0ge : 2 ≤ e0 := by omega
        have hq : IsQuadratic (MvPolynomial.C rcoeff * x0 ^ (e0 - 2)) := by
          simpa using isQuadratic_C_mul_pow_pow rcoeff (e0 - 2) 0 (by omega)
        have hmul :
            x0 ^ 2 * (MvPolynomial.C rcoeff * x0 ^ (e0 - 2)) =
              MvPolynomial.C rcoeff * x0 ^ e0 := by
          calc
            x0 ^ 2 * (MvPolynomial.C rcoeff * x0 ^ (e0 - 2))
                = MvPolynomial.C rcoeff * (x0 ^ 2 * x0 ^ (e0 - 2)) := by
                    ring_nf
            _ = MvPolynomial.C rcoeff * x0 ^ e0 := by
                  rw [← pow_add, Nat.add_sub_of_le he0ge]
        simpa [monomial_fin2_eq, e0, e1, he1zero, hmul] using
          (inAdmissibleImage_of_relation_mul_low
            (u := u) (c := c2) (r := x0 ^ 2)
            (q := MvPolynomial.C rcoeff * x0 ^ (e0 - 2)) h2 hq)
    · have he1pos : 1 ≤ e1 := by omega
      have hq :
          IsQuadratic ((MvPolynomial.C rcoeff * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1)) := by
        exact isQuadratic_C_mul_pow_pow rcoeff (e0 - 1) (e1 - 1) (by omega)
      have hmul :
          (x0 * x1 : Poly) * ((MvPolynomial.C rcoeff * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1)) =
            (MvPolynomial.C rcoeff * x0 ^ e0) * x1 ^ e1 := by
        calc
          (x0 * x1 : Poly) * ((MvPolynomial.C rcoeff * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1))
              = MvPolynomial.C rcoeff * (x0 * x0 ^ (e0 - 1)) * (x1 * x1 ^ (e1 - 1)) := by
                  ring_nf
          _ = MvPolynomial.C rcoeff * x0 ^ e0 * x1 ^ e1 := by
                have hx0pos' : 1 ≤ e0 := by simpa [e0] using hx0pos
                have hxpow : x0 * x0 ^ (e0 - 1) = x0 ^ e0 := by
                  simpa [Nat.sub_add_cancel hx0pos'] using (pow_succ' x0 (e0 - 1)).symm
                have hypow : x1 * x1 ^ (e1 - 1) = x1 ^ e1 := by
                  simpa [Nat.sub_add_cancel he1pos] using (pow_succ' x1 (e1 - 1)).symm
                simp [hxpow, hypow, mul_assoc]
      simpa [monomial_fin2_eq, e0, e1, hmul] using
        (inAdmissibleImage_of_relation_mul_low
          (u := u) (c := c3) (r := x0 * x1)
          (q := (MvPolynomial.C rcoeff * x0 ^ (e0 - 1)) * x1 ^ (e1 - 1)) h3 hq)
  have himgR : InAdmissibleImage u r := by
    rw [← MvPolynomial.support_sum_monomial_coeff r]
    let P : Finset (Fin 2 →₀ ℕ) → Prop := fun S =>
      (∀ s ∈ S, s ∈ r.support) →
        InAdmissibleImage u (∑ s ∈ S, MvPolynomial.monomial s (MvPolynomial.coeff s r))
    have hP : P r.support := by
      refine Finset.induction_on r.support ?_ ?_
      · intro hsub
        simpa using inAdmissibleImage_zero u
      · intro s ss hsnot ih hsub
        rw [Finset.sum_insert hsnot]
        refine inAdmissibleImage_add u ?_ (ih ?_)
        · have hsdeg : s.sum (fun _ e => e) ≤ 4 :=
            (MvPolynomial.le_totalDegree (hsub s (by simp))).trans hrQuartic
          have hscoeff : MvPolynomial.coeff s r ≠ 0 :=
            MvPolynomial.mem_support_iff.mp (hsub s (by simp))
          have hs0pos : 1 ≤ s 0 := by
            by_contra hs0pos
            have hs0 : s 0 = 0 := by omega
            have hs1le : s 1 ≤ 4 := by
              have hs' : s 0 + s 1 ≤ 4 := by
                rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at hsdeg
                simpa [hs0] using hsdeg
              omega
            interval_cases hs1 : s 1
            · apply hscoeff
              have hsEq : s = m00 := by
                ext i
                fin_cases i <;> simp [m00, hs0, hs1]
              simpa [hsEq] using hr00
            · apply hscoeff
              have hsEq : s = m01 := by
                ext i
                fin_cases i <;> simp [m01, hs0, hs1]
              simpa [hsEq] using hr01
            · apply hscoeff
              have hsEq : s = m02 := by
                ext i
                fin_cases i <;> simp [m02, hs0, hs1]
              simpa [hsEq] using hr02
            · apply hscoeff
              have hsEq : s = m03 := by
                ext i
                fin_cases i <;> simp [m03, hs0, hs1]
              simpa [hsEq] using hr03
            · apply hscoeff
              have hsEq : s = m04 := by
                ext i
                fin_cases i <;> simp [m04, hs0, hs1]
              simpa [hsEq] using hr04
          exact monomialImage s (MvPolynomial.coeff s r) hsdeg hs0pos
        · intro t ht
          exact hsub t (by simp [ht])
    exact hP (fun s hs => hs)
  have hdecomp : p = purePart + r := by
    dsimp [r]
    ring
  exact hdecomp ▸ inAdmissibleImage_add u hpureImg himgR

theorem residual_eq_zero_of_relations_x0_onePlusAX1sq_x0sq_x0x1
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {a : ℝ}
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = (1 : Poly) + a • (x1 ^ 2 : Poly))
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 ^ 2)
    (h3 : ∑ i : Fin 4, c3 i • u i = x0 * x1)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  rcases hp with ⟨hpquartic, k, qs, hqdeg, hpq⟩
  let alpha : ℝ := ∑ i : Fin 4, (c2 i) ^ 2
  have hc2_ne : c2 ≠ 0 := by
    intro hc2
    have : (0 : Poly) = x0 ^ 2 := by
      simpa [hc2] using h2
    have hcoeff := congrArg (MvPolynomial.coeff m20) this
    simp [x0, m20, MvPolynomial.coeff_X_pow] at hcoeff
  have halpha_pos : 0 < alpha := sum_sq_pos_of_ne_zero c2 hc2_ne
  have halpha_nonneg : 0 ≤ alpha := le_of_lt halpha_pos
  have hsqrt_ne : Real.sqrt alpha ≠ 0 := by
    intro hsqrt0
    apply halpha_pos.ne'
    calc
      alpha = (Real.sqrt alpha) ^ 2 := by rw [Real.sq_sqrt halpha_nonneg]
      _ = 0 := by simp [hsqrt0]
  let beta : Fin k → ℝ := fun i => MvPolynomial.coeff m01 (qs i) / Real.sqrt alpha
  let gamma : Fin k → ℝ := fun i =>
    (MvPolynomial.coeff m02 (qs i) - a * MvPolynomial.coeff m00 (qs i)) / Real.sqrt alpha
  let w : Fin k → RankFourVec := fun i =>
    affineDimOneConstX1sqKer c2 c3 (beta i) (gamma i)
  let imgPart : Poly := ∑ i : Fin k, ((qs i) ^ 2 - sigma (w i))
  have himgTerm :
      ∀ i : Fin k, InAdmissibleImage u ((qs i) ^ 2 - sigma (w i)) := by
    intro i
    have hquartic_i : IsQuartic ((qs i) ^ 2 - sigma (w i)) := by
      have hsqQuartic : IsQuartic ((qs i) ^ 2) := by
        calc
          ((qs i) ^ 2).totalDegree ≤ (qs i).totalDegree + (qs i).totalDegree := by
            simpa [pow_two] using MvPolynomial.totalDegree_mul (qs i) (qs i)
          _ ≤ (2 : ℕ) + 2 := add_le_add (hqdeg i) (hqdeg i)
          _ = 4 := by norm_num
      have hsigQuartic : IsQuartic (sigma (w i)) := by
        exact isQuartic_sigma_of_admissible
          ((affineDimOneConstX1sqKer_admissible c2 c3 (beta i) (gamma i)))
      calc
        (((qs i) ^ 2 - sigma (w i)) : Poly).totalDegree ≤
            max ((qs i) ^ 2).totalDegree (sigma (w i)).totalDegree := by
              exact MvPolynomial.totalDegree_sub _ _
        _ ≤ 4 := max_le hsqQuartic hsigQuartic
    have htail1_i : onePlusX1sqFunctional1 a ((qs i) ^ 2 - sigma (w i)) = 0 := by
      have hsig1 :
          onePlusX1sqFunctional1 a (sigma (w i)) =
            2 * MvPolynomial.coeff m01 (qs i) *
              (MvPolynomial.coeff m02 (qs i) - a * MvPolynomial.coeff m00 (qs i)) := by
        have hsq2 : (Real.sqrt alpha) ^ 2 = alpha := by
          rw [Real.sq_sqrt halpha_nonneg]
        calc
          onePlusX1sqFunctional1 a (sigma (w i))
              = alpha * (2 * beta i * gamma i) := by
                  dsimp [w]
                  exact onePlusX1sqFunctional1_sigma_affineDimOneConstX1sqKer
                    a c2 c3 (beta i) (gamma i)
          _ = alpha *
              (2 * (MvPolynomial.coeff m01 (qs i) / Real.sqrt alpha) *
                ((MvPolynomial.coeff m02 (qs i) - a * MvPolynomial.coeff m00 (qs i)) /
                  Real.sqrt alpha)) := by
                simp [beta, gamma]
          _ = 2 * MvPolynomial.coeff m01 (qs i) *
                (MvPolynomial.coeff m02 (qs i) - a * MvPolynomial.coeff m00 (qs i)) := by
                field_simp [hsqrt_ne]
                rw [hsq2]
                ring
      calc
        onePlusX1sqFunctional1 a ((qs i) ^ 2 - sigma (w i))
            = onePlusX1sqFunctional1 a ((qs i) ^ 2) -
                onePlusX1sqFunctional1 a (sigma (w i)) := by
                  rw [onePlusX1sqFunctional1_sub]
        _ = 2 * MvPolynomial.coeff m01 (qs i) *
              (MvPolynomial.coeff m02 (qs i) - a * MvPolynomial.coeff m00 (qs i)) -
              onePlusX1sqFunctional1 a (sigma (w i)) := by
                rw [onePlusX1sqFunctional1_sq_of_quadratic_eq a (qs i) (hqdeg i)]
        _ = 0 := by simp [hsig1]
    have htail2_i : onePlusX1sqFunctional2 a ((qs i) ^ 2 - sigma (w i)) = 0 := by
      have hsig2 :
          onePlusX1sqFunctional2 a (sigma (w i)) =
            (MvPolynomial.coeff m02 (qs i) - a * MvPolynomial.coeff m00 (qs i)) ^ 2 -
              a * (MvPolynomial.coeff m01 (qs i)) ^ 2 := by
        have hsq2 : (Real.sqrt alpha) ^ 2 = alpha := by
          rw [Real.sq_sqrt halpha_nonneg]
        calc
          onePlusX1sqFunctional2 a (sigma (w i))
              = alpha * (gamma i ^ 2 - a * beta i ^ 2) := by
                  dsimp [w]
                  exact onePlusX1sqFunctional2_sigma_affineDimOneConstX1sqKer
                    a c2 c3 (beta i) (gamma i)
          _ = alpha *
              (((MvPolynomial.coeff m02 (qs i) - a * MvPolynomial.coeff m00 (qs i)) /
                    Real.sqrt alpha) ^ 2 -
                a * (MvPolynomial.coeff m01 (qs i) / Real.sqrt alpha) ^ 2) := by
                simp [beta, gamma]
          _ = (MvPolynomial.coeff m02 (qs i) - a * MvPolynomial.coeff m00 (qs i)) ^ 2 -
                a * (MvPolynomial.coeff m01 (qs i)) ^ 2 := by
                field_simp [hsqrt_ne]
                rw [hsq2]
      calc
        onePlusX1sqFunctional2 a ((qs i) ^ 2 - sigma (w i))
            = onePlusX1sqFunctional2 a ((qs i) ^ 2) -
                onePlusX1sqFunctional2 a (sigma (w i)) := by
                  rw [onePlusX1sqFunctional2_sub]
        _ = ((MvPolynomial.coeff m02 (qs i) - a * MvPolynomial.coeff m00 (qs i)) ^ 2 -
                a * (MvPolynomial.coeff m01 (qs i)) ^ 2) -
                onePlusX1sqFunctional2 a (sigma (w i)) := by
              rw [onePlusX1sqFunctional2_sq_of_quadratic_eq a (qs i) (hqdeg i)]
        _ = 0 := by simp [hsig2]
    exact quartic_in_image_of_relations_x0_onePlusAX1sq_x0sq_x0x1_of_tail_zero
      h0 h1 h2 h3 hquartic_i htail1_i htail2_i
  have himgPart : InAdmissibleImage u imgPart := by
    classical
    unfold imgPart
    refine Finset.induction_on (Finset.univ : Finset (Fin k)) ?_ ?_
    · simpa using inAdmissibleImage_zero u
    · intro i s hi ih
      rw [Finset.sum_insert hi]
      exact inAdmissibleImage_add u (himgTerm i) ih
  have hker : ∀ i ∈ (Finset.univ : Finset (Fin k)), InAdmissibleKer u (w i) := by
    intro i hi
    dsimp [w]
    exact affineDimOneConstX1sqKer_inKer h2 h3
  have hdecomp :
      p = imgPart + Finset.sum (Finset.univ : Finset (Fin k)) (fun i => sigma (w i)) := by
    calc
      p = ∑ i : Fin k, (qs i) ^ 2 := hpq
      _ = ∑ i : Fin k, (((qs i) ^ 2 - sigma (w i)) + sigma (w i)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
      _ = imgPart + Finset.sum (Finset.univ : Finset (Fin k)) (fun i => sigma (w i)) := by
            simp [imgPart]
  exact admissible_image_plus_indexed_sigma_family_residual_eq_zero
    (B := B) (u := u) (uImg := u) hu hsocp
    (imageOrthogonalResidual_self (B := B) hsocp.1)
    himgPart hker hdecomp

theorem residual_eq_zero_of_equiv_relations_x0_onePlusAX1sq_x0sq_x0x1
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    {a : ℝ}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = (1 : Poly) + a • (x1 ^ 2 : Poly))
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = x0 ^ 2)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = x0 * x1) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e)
      (heQuad := fun {_} hpq => heQuad hpq)
      (heQuartic := fun {_} hpq => heQuartic hpq)
      hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_x0_onePlusAX1sq_x0sq_x0x1
      (B := B0) (u := mapVec e.toAlgHom u) hu0 h0 h1 h2 h3 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_x0_onePlusBX1PlusAX1sq_x0sq_x0x1
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {a b : ℝ}
    (ha : a ≠ 0)
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = (1 : Poly) + b • x1 + a • (x1 ^ 2 : Poly))
    (h2 : ∑ i : Fin 4, c2 i • u i = x0 ^ 2)
    (h3 : ∑ i : Fin 4, c3 i • u i = x0 * x1)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let t : ℝ := -(b / (2 * a))
  let lam : ℝ := 1 - b ^ 2 / (4 * a)
  let e : Poly ≃ₐ[ℝ] Poly := x1TranslateEquiv t
  have heQuad : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e q) := by
    intro q hq
    exact isQuadratic_affineEquiv
      (1 : Matrix (Fin 2) (Fin 2) ℝ) 1
      (x1TranslateVec t) (x1TranslateInvVec t)
      (by simp) (by simp)
      (x1TranslateInv_add_mulVec t) (x1Translate_add_mulVec_inv t)
      hq
  have heQuadSymm : ∀ {q : Poly}, IsQuadratic q → IsQuadratic (e.symm q) := by
    intro q hq
    exact isQuadratic_affineEquiv_symm
      (1 : Matrix (Fin 2) (Fin 2) ℝ) 1
      (x1TranslateVec t) (x1TranslateInvVec t)
      (by simp) (by simp)
      (x1TranslateInv_add_mulVec t) (x1Translate_add_mulVec_inv t)
      hq
  have heQuartic : ∀ {q : Poly}, IsQuartic q → IsQuartic (e q) := by
    intro q hq
    exact isQuartic_affineEquiv
      (1 : Matrix (Fin 2) (Fin 2) ℝ) 1
      (x1TranslateVec t) (x1TranslateInvVec t)
      (by simp) (by simp)
      (x1TranslateInv_add_mulVec t) (x1Translate_add_mulVec_inv t)
      hq
  have hB : IsPositiveDefinite B := by
    simpa [IsPositiveDefinite] using (show B.toQuadraticMap.PosDef from Fact.out)
  have he_x0 : e x0 = x0 := by
    change affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) x0 = x0
    simp [affineHom_x1Translate_x0]
  have he_x1 : e x1 = MvPolynomial.C t + x1 := by
    change affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t) x1 =
      MvPolynomial.C t + x1
    simp [affineHom_x1Translate_x1]
  have h0' : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0 := by
    simpa [he_x0] using relation_map e.toAlgHom h0
  have h2' : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = x0 ^ 2 := by
    calc
      ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = e (x0 ^ 2 : Poly) := by
        simpa [e] using relation_map e.toAlgHom h2
      _ = x0 ^ 2 := by
        rw [show (x0 ^ 2 : Poly) = x0 * x0 by simp [pow_two]]
        simp [he_x0]
  have h3e : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = MvPolynomial.C t * x0 + x0 * x1 := by
    calc
      ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = e (x0 * x1 : Poly) := by
        simpa [e] using relation_map e.toAlgHom h3
      _ = MvPolynomial.C t * x0 + x0 * x1 := by
        calc
          e (x0 * x1 : Poly) = e x0 * e x1 := by simp
          _ = x0 * (MvPolynomial.C t + x1) := by rw [he_x0, he_x1]
          _ = MvPolynomial.C t * x0 + x0 * x1 := by
                ring
  let c3' : Fin 4 → ℝ := c3 + (-t) • c0
  have h3' : ∑ i : Fin 4, c3' i • mapVec e.toAlgHom u i = x0 * x1 := by
    change relationPoly (mapVec e.toAlgHom u) c3' = x0 * x1
    calc
      relationPoly (mapVec e.toAlgHom u) c3'
          = relationPoly (mapVec e.toAlgHom u) c3 +
              relationPoly (mapVec e.toAlgHom u) ((-t) • c0) := by
                rw [show c3' = c3 + (-t) • c0 by rfl, relationPoly_add]
      _ = (MvPolynomial.C t * x0 + x0 * x1) + (-t) • x0 := by
            rw [relationPoly_smul]
            rw [show relationPoly (mapVec e.toAlgHom u) c3 =
                ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i by rfl]
            rw [show relationPoly (mapVec e.toAlgHom u) c0 =
                ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i by rfl]
            rw [h3e, h0']
      _ = x0 * x1 := by
            simp [MvPolynomial.smul_eq_C_mul]
  have h1e :
      ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i =
        (MvPolynomial.C lam : Poly) + a • (x1 ^ 2 : Poly) := by
    calc
      ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = e ((1 : Poly) + b • x1 + a • (x1 ^ 2 : Poly)) := by
        simpa [e] using relation_map e.toAlgHom h1
      _ = (MvPolynomial.C lam : Poly) + a • (x1 ^ 2 : Poly) := by
        change affineHom (1 : Matrix (Fin 2) (Fin 2) ℝ) (x1TranslateVec t)
          ((1 : Poly) + b • x1 + a • (x1 ^ 2 : Poly)) =
            (MvPolynomial.C lam : Poly) + a • (x1 ^ 2 : Poly)
        rw [show (1 : Poly) + b • x1 + a • (x1 ^ 2 : Poly) = quadForm 1 0 b 0 0 a by
          rw [quadForm_eq_explicit]
          simp [MvPolynomial.smul_eq_C_mul, add_left_comm, add_comm]]
        rw [affineHom_x1Translate_quadForm]
        rw [quadForm_eq_explicit]
        have hconst : 1 + b * (-(b / (2 * a))) + a * (-(b / (2 * a))) ^ 2 = lam := by
          dsimp [lam, t]
          field_simp [ha]
          ring
        have hlin : b + 2 * a * (-(b / (2 * a))) = 0 := by
          dsimp [t]
          field_simp [ha]
          ring
        rw [hconst, hlin]
        simp [MvPolynomial.smul_eq_C_mul, add_comm]
  by_cases hlam : lam = 0
  · let c1' : Fin 4 → ℝ := a⁻¹ • c1
    have h1' : ∑ i : Fin 4, c1' i • mapVec e.toAlgHom u i = x1 ^ 2 := by
      change relationPoly (mapVec e.toAlgHom u) c1' = x1 ^ 2
      calc
        relationPoly (mapVec e.toAlgHom u) c1' = a⁻¹ • relationPoly (mapVec e.toAlgHom u) c1 := by
          rw [show c1' = a⁻¹ • c1 by rfl, relationPoly_smul]
        _ = a⁻¹ • ((MvPolynomial.C lam : Poly) + a • (x1 ^ 2 : Poly)) := by
              rw [show relationPoly (mapVec e.toAlgHom u) c1 =
                ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i by rfl, h1e]
        _ = x1 ^ 2 := by
              rw [hlam]
              simp [smul_smul, ha]
    exact residual_eq_zero_of_equiv_relations_x0_x0sq_x0x1_x1sq
      (e := e)
      (heQuad := fun {_} hq => heQuad hq)
      (heQuadSymm := fun {_} hq => heQuadSymm hq)
      (heQuartic := fun {_} hq => heQuartic hq)
      hB hp hu hsocp h0' h2' h3' h1'
  · let c1' : Fin 4 → ℝ := lam⁻¹ • c1
    have h1' :
        ∑ i : Fin 4, c1' i • mapVec e.toAlgHom u i =
          (1 : Poly) + (a / lam) • (x1 ^ 2 : Poly) := by
      change relationPoly (mapVec e.toAlgHom u) c1' =
        (1 : Poly) + (a / lam) • (x1 ^ 2 : Poly)
      calc
        relationPoly (mapVec e.toAlgHom u) c1' = lam⁻¹ • relationPoly (mapVec e.toAlgHom u) c1 := by
          rw [show c1' = lam⁻¹ • c1 by rfl, relationPoly_smul]
        _ = lam⁻¹ • ((MvPolynomial.C lam : Poly) + a • (x1 ^ 2 : Poly)) := by
              rw [show relationPoly (mapVec e.toAlgHom u) c1 =
                ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i by rfl, h1e]
        _ = (1 : Poly) + (a / lam) • (x1 ^ 2 : Poly) := by
              rw [smul_add, smul_smul]
              have hconst : lam⁻¹ • (MvPolynomial.C lam : Poly) = (1 : Poly) := by
                rw [MvPolynomial.smul_eq_C_mul, ← MvPolynomial.C_mul, inv_mul_cancel₀ hlam]
                simp
              have hquad : (lam⁻¹ * a) • (x1 ^ 2 : Poly) = (a / lam) • (x1 ^ 2 : Poly) := by
                congr 1
                simp [div_eq_mul_inv, mul_comm]
              rw [hconst, hquad]
    exact residual_eq_zero_of_equiv_relations_x0_onePlusAX1sq_x0sq_x0x1
      (e := e)
      (heQuad := fun {_} hq => heQuad hq)
      (heQuadSymm := fun {_} hq => heQuadSymm hq)
      (heQuartic := fun {_} hq => heQuartic hq)
      hB hp hu hsocp h0' h1' h2' h3'

theorem residual_eq_zero_of_equiv_relations_x0_onePlusBX1PlusAX1sq_x0sq_x0x1
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    {a b : ℝ}
    (ha : a ≠ 0)
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = (1 : Poly) + b • x1 + a • (x1 ^ 2 : Poly))
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = x0 ^ 2)
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = x0 * x1) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e)
      (heQuad := fun {_} hpq => heQuad hpq)
      (heQuartic := fun {_} hpq => heQuartic hpq)
      hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_x0_onePlusBX1PlusAX1sq_x0sq_x0x1
      (B := B0) (u := mapVec e.toAlgHom u) hu0 ha h0 h1 h2 h3 hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0

theorem residual_eq_zero_of_relations_x0_onePlusBX1PlusAX1sq_x0sq_x0x1Plane
    {B : DotForm} [Fact B.toQuadraticMap.PosDef]
    {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    {a b r s t w : ℝ}
    (ha : a ≠ 0)
    (h0 : ∑ i : Fin 4, c0 i • u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • u i = (1 : Poly) + b • x1 + a • (x1 ^ 2 : Poly))
    (h2 : ∑ i : Fin 4, c2 i • u i = r • (x0 ^ 2 : Poly) + s • (x0 * x1))
    (h3 : ∑ i : Fin 4, c3 i • u i = t • (x0 ^ 2 : Poly) + w • (x0 * x1))
    (hdet : r * w - s * t ≠ 0)
    {p : Poly}
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let det : ℝ := r * w - s * t
  have hdet0 : det ≠ 0 := by
    simpa [det] using hdet
  let c2' : Fin 4 → ℝ := fun i => (w / det) * c2 i + (-s / det) * c3 i
  let c3' : Fin 4 → ℝ := fun i => (-t / det) * c2 i + (r / det) * c3 i
  have hcoeff20 : (w / det) * r + (-s / det) * t = 1 := by
    field_simp [det, hdet0]
    ring
  have hcoeff21 : (w / det) * s + (-s / det) * w = 0 := by
    field_simp [det, hdet0]
    ring
  have hcoeff30 : (-t / det) * r + (r / det) * t = 0 := by
    field_simp [det, hdet0]
    ring
  have hcoeff31 : (-t / det) * s + (r / det) * w = 1 := by
    field_simp [det, hdet0]
    ring
  have h2' : ∑ i : Fin 4, c2' i • u i = x0 ^ 2 := by
    change relationPoly u c2' = x0 ^ 2
    calc
      relationPoly u c2'
          = relationPoly u ((w / det) • c2) + relationPoly u ((-s / det) • c3) := by
              rw [show c2' = (w / det) • c2 + (-s / det) • c3 by
                funext i
                simp [c2']
              , relationPoly_add]
      _ = (w / det) • relationPoly u c2 + (-s / det) • relationPoly u c3 := by
            rw [relationPoly_smul, relationPoly_smul]
      _ = (w / det) • (r • (x0 ^ 2 : Poly) + s • (x0 * x1)) +
            (-s / det) • (t • (x0 ^ 2 : Poly) + w • (x0 * x1)) := by
              rw [show relationPoly u c2 = ∑ i : Fin 4, c2 i • u i by rfl,
                show relationPoly u c3 = ∑ i : Fin 4, c3 i • u i by rfl,
                h2, h3]
      _ = ((w / det) * r + (-s / det) * t) • (x0 ^ 2 : Poly) +
            ((w / det) * s + (-s / det) * w) • (x0 * x1) := by
              simp [smul_add, smul_smul, add_smul, add_assoc, add_left_comm, mul_comm]
      _ = x0 ^ 2 := by
            rw [hcoeff20, hcoeff21]
            simp
  have h3' : ∑ i : Fin 4, c3' i • u i = x0 * x1 := by
    change relationPoly u c3' = x0 * x1
    calc
      relationPoly u c3'
          = relationPoly u ((-t / det) • c2) + relationPoly u ((r / det) • c3) := by
              rw [show c3' = (-t / det) • c2 + (r / det) • c3 by
                funext i
                simp [c3']
              , relationPoly_add]
      _ = (-t / det) • relationPoly u c2 + (r / det) • relationPoly u c3 := by
            rw [relationPoly_smul, relationPoly_smul]
      _ = (-t / det) • (r • (x0 ^ 2 : Poly) + s • (x0 * x1)) +
            (r / det) • (t • (x0 ^ 2 : Poly) + w • (x0 * x1)) := by
              rw [show relationPoly u c2 = ∑ i : Fin 4, c2 i • u i by rfl,
                show relationPoly u c3 = ∑ i : Fin 4, c3 i • u i by rfl,
                h2, h3]
      _ = ((-t / det) * r + (r / det) * t) • (x0 ^ 2 : Poly) +
            ((-t / det) * s + (r / det) * w) • (x0 * x1) := by
              simp [smul_add, smul_smul, add_smul, add_assoc, add_left_comm, add_comm, mul_comm]
      _ = x0 * x1 := by
            rw [hcoeff30, hcoeff31]
            simp
  exact residual_eq_zero_of_relations_x0_onePlusBX1PlusAX1sq_x0sq_x0x1
    (B := B) (u := u) hu ha h0 h1 h2' h3' hp hsocp

theorem residual_eq_zero_of_equiv_relations_x0_onePlusBX1PlusAX1sq_x0sq_x0x1Plane
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    {a b r s t w : ℝ}
    (ha : a ≠ 0)
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    {c0 c1 c2 c3 : Fin 4 → ℝ}
    (h0 : ∑ i : Fin 4, c0 i • mapVec e.toAlgHom u i = x0)
    (h1 : ∑ i : Fin 4, c1 i • mapVec e.toAlgHom u i = (1 : Poly) + b • x1 + a • (x1 ^ 2 : Poly))
    (h2 : ∑ i : Fin 4, c2 i • mapVec e.toAlgHom u i = r • (x0 ^ 2 : Poly) + s • (x0 * x1))
    (h3 : ∑ i : Fin 4, c3 i • mapVec e.toAlgHom u i = t • (x0 ^ 2 : Poly) + w • (x0 * x1))
    (hdet : r * w - s * t ≠ 0) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e B
  have hB0 : IsPositiveDefinite B0 := isPositiveDefinite_dotTransport e hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e)
      (heQuad := fun {_} hpq => heQuad hpq)
      (heQuartic := fun {_} hpq => heQuartic hpq)
      hp
  have hu0 : IsAdmissiblePoint (mapVec e.toAlgHom u) := by
    exact isAdmissiblePoint_mapVec_of_equiv (e := e) (he := fun {_} hpq => heQuad hpq) hu
  have hsocp0 : IsSOCP B0 (e p) (mapVec e.toAlgHom u) := by
    dsimp [B0]
    exact isSOCP_mapVec_of_equiv (e := e) (heSymm := fun {_} hpq => heQuadSymm hpq) hsocp
  have hres0 :
      residual (e p) (mapVec e.toAlgHom u) = 0 := by
    exact residual_eq_zero_of_relations_x0_onePlusBX1PlusAX1sq_x0sq_x0x1Plane
      (B := B0) (u := mapVec e.toAlgHom u) hu0 ha h0 h1 h2 h3 hdet hp0 hsocp0
  exact (residual_eq_zero_mapVec_iff_of_equiv e p u).mp hres0
