import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import TernaryQuarticProof.Certificate

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace TernaryQuartic

open scoped BigOperators

/-- Linear recombination of the four factor coordinates by a real matrix. -/
def mix (M : Matrix (Fin 4) (Fin 4) ℝ) (u : RankFourVec) : RankFourVec :=
  fun i => ∑ j : Fin 4, M i j • u j

@[simp] theorem mix_apply (M : Matrix (Fin 4) (Fin 4) ℝ) (u : RankFourVec) (i : Fin 4) :
    mix M u i = ∑ j : Fin 4, M i j • u j :=
  rfl

@[simp] theorem mix_zero (M : Matrix (Fin 4) (Fin 4) ℝ) :
    mix M (0 : RankFourVec) = 0 := by
  funext i
  simp [mix]

@[simp] theorem mix_one (u : RankFourVec) :
    mix (1 : Matrix (Fin 4) (Fin 4) ℝ) u = u := by
  funext i
  simp [mix, Matrix.one_apply]

theorem isAdmissiblePoint_mix (M : Matrix (Fin 4) (Fin 4) ℝ) {u : RankFourVec}
    (hu : IsAdmissiblePoint u) :
    IsAdmissiblePoint (mix M u) := by
  intro i
  calc
    (mix M u i).totalDegree ≤
        (Finset.univ.sup fun j : Fin 4 => (M i j • u j).totalDegree) := by
      exact MvPolynomial.totalDegree_finset_sum _ _
    _ ≤ 2 := by
      refine Finset.sup_le ?_
      intro j hj
      exact (MvPolynomial.totalDegree_smul_le (M i j) (u j)).trans (hu j)

@[simp] theorem mix_mul (M N : Matrix (Fin 4) (Fin 4) ℝ) (u : RankFourVec) :
    mix M (mix N u) = mix (M * N) u := by
  funext i
  calc
    ∑ j : Fin 4, M i j • ∑ k : Fin 4, N j k • u k
        = ∑ j : Fin 4, ∑ k : Fin 4, (M i j * N j k) • u k := by
            simp [Finset.smul_sum, smul_smul]
    _ = ∑ k : Fin 4, ∑ j : Fin 4, (M i j * N j k) • u k := by
          rw [Finset.sum_comm]
    _ = ∑ k : Fin 4, (∑ j : Fin 4, M i j * N j k) • u k := by
          simp [Finset.sum_smul]
    _ = ∑ k : Fin 4, (M * N) i k • u k := by
          simp [Matrix.mul_apply]

theorem A_mix_left (M : Matrix (Fin 4) (Fin 4) ℝ) (u v : RankFourVec) :
    A (mix M u) v = A u (mix M.transpose v) := by
  calc
    A (mix M u) v
        = ∑ i : Fin 4, (∑ j : Fin 4, M i j • u j) * v i := by
            simp [A, mix]
    _ = ∑ i : Fin 4, ∑ j : Fin 4, M i j • (u j * v i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro j hj
          exact smul_mul_assoc (M i j) (u j) (v i)
    _ = ∑ j : Fin 4, ∑ i : Fin 4, M i j • (u j * v i) := by
          rw [Finset.sum_comm]
    _ = ∑ j : Fin 4, ∑ i : Fin 4, u j * (M i j • v i) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp
    _ = ∑ j : Fin 4, u j * ∑ i : Fin 4, M i j • v i := by
          simp [Finset.mul_sum]
    _ = A u (mix M.transpose v) := by
          simp [A, mix, Matrix.transpose_apply]

theorem sigma_mix_of_transpose_mul_self_eq_one
    (M : Matrix (Fin 4) (Fin 4) ℝ) (u : RankFourVec)
    (hM : M.transpose * M = 1) :
    sigma (mix M u) = sigma u := by
  calc
    sigma (mix M u) = A (mix M u) (mix M u) := by simp [A_self_eq_sigma]
    _ = A u (mix M.transpose (mix M u)) := A_mix_left M u (mix M u)
    _ = A u (mix (M.transpose * M) u) := by rw [mix_mul]
    _ = A u u := by simp [hM]
    _ = sigma u := by simp [A_self_eq_sigma]

theorem residual_mix_of_transpose_mul_self_eq_one
    (M : Matrix (Fin 4) (Fin 4) ℝ) {p : Poly} {u : RankFourVec}
    (hM : M.transpose * M = 1) :
    residual p (mix M u) = residual p u := by
  simp [residual, sigma_mix_of_transpose_mul_self_eq_one, hM]

theorem isFOCP_mix_of_orthogonal
    (M : Matrix (Fin 4) (Fin 4) ℝ) {B : DotForm} {p : Poly} {u : RankFourVec}
    (hMtM : M.transpose * M = 1)
    (hfocp : IsFOCP B p u) :
    IsFOCP B p (mix M u) := by
  intro v hv
  rw [A_mix_left, residual_mix_of_transpose_mul_self_eq_one M hMtM]
  exact hfocp (mix M.transpose v) (isAdmissiblePoint_mix M.transpose hv)

theorem sigma_mix_of_self_mul_transpose_eq_one
    (M : Matrix (Fin 4) (Fin 4) ℝ) (u : RankFourVec)
    (hM : M * M.transpose = 1) :
    sigma (mix M.transpose u) = sigma u := by
  simpa [Matrix.transpose_transpose] using
    sigma_mix_of_transpose_mul_self_eq_one M.transpose u (by simpa using hM)

theorem isSOCP_mix_of_orthogonal
    (M : Matrix (Fin 4) (Fin 4) ℝ) {B : DotForm} {p : Poly} {u : RankFourVec}
    (hMtM : M.transpose * M = 1)
    (hMMt : M * M.transpose = 1)
    (hsocp : IsSOCP B p u) :
    IsSOCP B p (mix M u) := by
  refine ⟨isFOCP_mix_of_orthogonal M hMtM hsocp.1, ?_⟩
  intro v hv
  have hv' : IsAdmissibleDirection (mix M.transpose v) :=
    isAdmissiblePoint_mix M.transpose hv
  have hh := hsocp.2 (mix M.transpose v) hv'
  simpa [hessianTerm, A_mix_left, residual_mix_of_transpose_mul_self_eq_one M hMtM,
    sigma_mix_of_self_mul_transpose_eq_one M (u := v) hMMt] using hh

end TernaryQuartic
