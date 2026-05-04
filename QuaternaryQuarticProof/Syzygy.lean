import QuaternaryQuarticProof.Catalecticant

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace QuaternaryQuartic

open scoped BigOperators

def syzygyDirection {ι : Type*} [Fintype ι]
    (α : ι → Fin 7 → ℝ) (n : ι → Poly) (β : Fin 7 → ℝ) (q : Poly) :
    RankSevenVec :=
  fun i => (∑ j : ι, α j i • n j) - β i • q

theorem syzygyDirection_admissible {ι : Type*} [Fintype ι]
    (α : ι → Fin 7 → ℝ) {n : ι → Poly} (β : Fin 7 → ℝ) {q : Poly}
    (hn : ∀ j, IsQuadratic (n j)) (hq : IsQuadratic q) :
    IsAdmissibleDirection (syzygyDirection α n β q) := by
  intro i
  unfold syzygyDirection IsQuadratic
  refine (MvPolynomial.totalDegree_sub _ _).trans ?_
  refine max_le ?_ ?_
  · refine MvPolynomial.totalDegree_finsetSum_le ?_
    intro j _hj
    exact (MvPolynomial.totalDegree_smul_le (α j i) (n j)).trans (hn j)
  · exact (MvPolynomial.totalDegree_smul_le (β i) q).trans hq

private theorem sum_mul_sum_comm {ι : Type*} [Fintype ι]
    (α : ι → Fin 7 → ℝ) (u : RankSevenVec) (n : ι → Poly) :
    (∑ i : Fin 7, ∑ j : ι, (α j i • u i) * n j) =
      ∑ j : ι, relationPoly u (α j) * n j := by
  classical
  calc
    (∑ i : Fin 7, ∑ j : ι, (α j i • u i) * n j) =
        ∑ j : ι, ∑ i : Fin 7, (α j i • u i) * n j := by
          rw [Finset.sum_comm]
    _ = ∑ j : ι, relationPoly u (α j) * n j := by
      refine Finset.sum_congr rfl ?_
      intro j _hj
      rw [relationPoly, Finset.sum_mul]

theorem A_syzygyDirection {ι : Type*} [Fintype ι]
    (u : RankSevenVec) (α : ι → Fin 7 → ℝ) (n : ι → Poly)
    (β : Fin 7 → ℝ) (q : Poly) :
    A u (syzygyDirection α n β q) =
      (∑ j : ι, relationPoly u (α j) * n j) - relationPoly u β * q := by
  classical
  unfold A syzygyDirection
  calc
    (∑ i : Fin 7, u i * ((∑ j : ι, α j i • n j) - β i • q)) =
        (∑ i : Fin 7, ∑ j : ι, (α j i • u i) * n j) -
          ∑ i : Fin 7, (β i • u i) * q := by
            simp [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
    _ = (∑ j : ι, relationPoly u (α j) * n j) - relationPoly u β * q := by
      rw [sum_mul_sum_comm, relationPoly, Finset.sum_mul]

theorem A_syzygyDirection_eq_zero {ι : Type*} [Fintype ι]
    {u : RankSevenVec} {α : ι → Fin 7 → ℝ} {n : ι → Poly}
    {β : Fin 7 → ℝ} {q : Poly}
    (hsyzygy : (∑ j : ι, relationPoly u (α j) * n j) = relationPoly u β * q) :
    A u (syzygyDirection α n β q) = 0 := by
  rw [A_syzygyDirection, hsyzygy, sub_self]

end QuaternaryQuartic
