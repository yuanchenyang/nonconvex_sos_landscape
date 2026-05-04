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

private theorem kernel_linear_combo_mem {ι : Type*} [Fintype ι]
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (α : ι → ℝ) {n : ι → Poly}
    (hnK : ∀ j, n j ∈ catalecticantKernel B p u) :
    (∑ j : ι, α j • n j) ∈ catalecticantKernel B p u := by
  exact Submodule.sum_mem _ fun j _hj =>
    Submodule.smul_mem _ (α j) (hnK j)

private theorem dot_sigma_sum_left {B : DotForm} (v : RankSevenVec) (r : Poly) :
    B (sigma v) r = ∑ i : Fin 7, B ((v i)^2) r := by
  classical
  unfold sigma
  refine Finset.induction_on (Finset.univ : Finset (Fin 7)) ?_ ?_
  · simp
  · intro i s hi ih
    calc
      B ((insert i s).sum fun i => (v i)^2) r =
          B ((v i)^2 + s.sum fun i => (v i)^2) r := by
            simp [hi]
      _ = B ((v i)^2) r + B (s.sum fun i => (v i)^2) r := by
        simp
      _ = B ((v i)^2) r + s.sum (fun i => B ((v i)^2) r) := by
        rw [ih]
      _ = (insert i s).sum fun i => B ((v i)^2) r := by
        simp [hi]

private theorem dot_syzygyDirection_coord_sq
    {ι : Type*} [Fintype ι] {B : DotForm} {p : Poly} {u : RankSevenVec}
    (α : ι → ℝ) {n : ι → Poly} (β : ℝ) {q : Poly}
    (hnK : ∀ j, n j ∈ catalecticantKernel B p u)
    (hq : IsQuadratic q) :
    B (((∑ j : ι, α j • n j) - β • q)^2) (residual p u) =
      β^2 * B (q^2) (residual p u) := by
  let N : Poly := ∑ j : ι, α j • n j
  have hNK : N ∈ catalecticantKernel B p u :=
    kernel_linear_combo_mem α hnK
  have hN_N : B (N * N) (residual p u) = 0 :=
    hNK.2 N hNK.1
  have hN_q : B (N * q) (residual p u) = 0 :=
    hNK.2 q hq
  have hq_N : B (q * N) (residual p u) = 0 := by
    rw [mul_comm]
    exact hN_q
  have hsquare :
      (N - β • q)^2 =
        N * N - N * (β • q) - (β • q) * N + (β^2) • (q^2) := by
    rw [pow_two]
    simp [MvPolynomial.smul_eq_C_mul]
    ring
  calc
    B (((∑ j : ι, α j • n j) - β • q)^2) (residual p u) =
        B ((N - β • q)^2) (residual p u) := by rfl
    _ = B (N * N - N * (β • q) - (β • q) * N + (β^2) • (q^2))
          (residual p u) := by
      rw [hsquare]
    _ = β^2 * B (q^2) (residual p u) := by
      simp [sub_eq_add_neg, hN_N, hN_q, hq_N]

theorem dot_sigma_syzygyDirection
    {ι : Type*} [Fintype ι] {B : DotForm} {p : Poly} {u : RankSevenVec}
    (α : ι → Fin 7 → ℝ) {n : ι → Poly} (β : Fin 7 → ℝ) {q : Poly}
    (hnK : ∀ j, n j ∈ catalecticantKernel B p u)
    (hq : IsQuadratic q) :
    B (sigma (syzygyDirection α n β q)) (residual p u) =
      (∑ i : Fin 7, (β i)^2) * B (q^2) (residual p u) := by
  classical
  rw [dot_sigma_sum_left]
  calc
    (∑ i : Fin 7,
        B ((syzygyDirection α n β q i)^2) (residual p u)) =
        ∑ i : Fin 7, (β i)^2 * B (q^2) (residual p u) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          exact dot_syzygyDirection_coord_sq (fun j => α j i) (β i) hnK hq
    _ = (∑ i : Fin 7, (β i)^2) * B (q^2) (residual p u) := by
      rw [Finset.sum_mul]

theorem false_of_syzygy_negative_curvature
    {ι : Type*} [Fintype ι] {B : DotForm} {p : Poly} {u : RankSevenVec}
    {α : ι → Fin 7 → ℝ} {n : ι → Poly} {β : Fin 7 → ℝ} {q : Poly}
    (hsocp : IsSOCP B p u)
    (hnK : ∀ j, n j ∈ catalecticantKernel B p u)
    (hq : IsQuadratic q)
    (hsyzygy : (∑ j : ι, relationPoly u (α j) * n j) = relationPoly u β * q)
    (hβ : β ≠ 0)
    (hnegq : B (q^2) (residual p u) < 0) :
    False := by
  let v : RankSevenVec := syzygyDirection α n β q
  have hnquad : ∀ j, IsQuadratic (n j) := fun j => (hnK j).1
  have hvadm : IsAdmissibleDirection v :=
    syzygyDirection_admissible α β hnquad hq
  have hA : A u v = 0 := by
    exact A_syzygyDirection_eq_zero hsyzygy
  have hsum_pos : 0 < ∑ i : Fin 7, (β i)^2 :=
    sum_sq_pos_of_ne_zero β hβ
  have hsigma :
      B (sigma v) (residual p u) =
        (∑ i : Fin 7, (β i)^2) * B (q^2) (residual p u) := by
    exact dot_sigma_syzygyDirection α β hnK hq
  have hneg_sigma : B (sigma v) (residual p u) < 0 := by
    rw [hsigma]
    nlinarith
  exact false_of_negative_curvature_direction hsocp hvadm hA hneg_sigma

end QuaternaryQuartic
