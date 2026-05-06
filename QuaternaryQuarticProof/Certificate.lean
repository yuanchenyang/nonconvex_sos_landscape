import Mathlib.Tactic.Linarith
import QuaternaryQuarticProof.Socp

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace QuaternaryQuartic

/-- An admissible quartic in the image of `A_u`. The witness is explicit
because the SOCP hypotheses only apply to admissible directions. -/
def InAdmissibleImage (u : RankSevenVec) (q : Poly) : Prop :=
  ∃ v : RankSevenVec, IsAdmissibleDirection v ∧ A u v = q

/-- An admissible kernel direction for `A_u`. -/
def InAdmissibleKer (u w : RankSevenVec) : Prop :=
  IsAdmissibleDirection w ∧ A u w = 0

/-- The residual at `u` is orthogonal to the admissible image of `uImg`. -/
def ImageOrthogonalResidual (B : DotForm) (p : Poly) (u uImg : RankSevenVec) : Prop :=
  ∀ q : Poly, InAdmissibleImage uImg q → B q (residual p u) = 0

/-- Constant-coefficient scaling of a single quadratic polynomial into a
rank-7 direction. This is the kernel family used for linearly dependent
rank-seven points. -/
def relationDirection (c : Fin 7 → ℝ) (q : Poly) : RankSevenVec :=
  fun i => c i • q

/-- The polynomial produced by a scalar relation vector on a rank-7 point. -/
def relationPoly (u : RankSevenVec) (c : Fin 7 → ℝ) : Poly :=
  ∑ i : Fin 7, c i • u i

theorem relationPoly_add (u : RankSevenVec) (c d : Fin 7 → ℝ) :
    relationPoly u (c + d) = relationPoly u c + relationPoly u d := by
  simp [relationPoly, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem relationPoly_smul (u : RankSevenVec) (a : ℝ) (c : Fin 7 → ℝ) :
    relationPoly u (a • c) = a • relationPoly u c := by
  simp [relationPoly, Pi.smul_apply, smul_smul, Finset.smul_sum]

/-- Linear map version of `relationPoly`. Its kernel is the space of scalar
linear dependencies among the seven quadratic coordinates. -/
def relationPolyLin (u : RankSevenVec) : (Fin 7 → ℝ) →ₗ[ℝ] Poly where
  toFun := relationPoly u
  map_add' := relationPoly_add u
  map_smul' := relationPoly_smul u

theorem isQuadratic_relationPoly {u : RankSevenVec}
    (hu : IsAdmissiblePoint u) (c : Fin 7 → ℝ) :
    IsQuadratic (relationPoly u c) := by
  unfold relationPoly IsQuadratic
  refine MvPolynomial.totalDegree_finsetSum_le ?_
  intro i _hi
  exact (MvPolynomial.totalDegree_smul_le (c i) (u i)).trans (hu i)

section Elementary

variable {B : DotForm}

theorem isAdmissibleDirection_zero : IsAdmissibleDirection (0 : RankSevenVec) := by
  intro i
  simp [IsQuadratic]

theorem isAdmissibleDirection_add {v w : RankSevenVec}
    (hv : IsAdmissibleDirection v) (hw : IsAdmissibleDirection w) :
    IsAdmissibleDirection (v + w) := by
  intro i
  exact (MvPolynomial.totalDegree_add _ _).trans <| max_le (hv i) (hw i)

theorem isAdmissibleDirection_smul (t : ℝ) {v : RankSevenVec}
    (hv : IsAdmissibleDirection v) :
    IsAdmissibleDirection (t • v) := by
  intro i
  exact (MvPolynomial.totalDegree_smul_le t (v i)).trans (hv i)

theorem A_smul_right (u v : RankSevenVec) (t : ℝ) :
    A u (t • v) = t • A u v := by
  calc
    A u (t • v) = ∑ i : Fin 7, t • (u i * v i) := by
      unfold A
      refine Finset.sum_congr rfl ?_
      intro i _hi
      change u i * (t • v i) = t • (u i * v i)
      exact mul_smul_comm t (u i) (v i)
    _ = t • ∑ i : Fin 7, u i * v i := by
      rw [← Finset.smul_sum]
    _ = t • A u v := by
      simp [A]

theorem relationDirection_admissible (c : Fin 7 → ℝ) {q : Poly}
    (hq : IsQuadratic q) :
    IsAdmissibleDirection (relationDirection c q) := by
  intro i
  exact (MvPolynomial.totalDegree_smul_le (c i) q).trans hq

theorem A_relationDirection (u : RankSevenVec) (c : Fin 7 → ℝ) (q : Poly) :
    A u (relationDirection c q) = relationPoly u c * q := by
  calc
    A u (relationDirection c q) = ∑ i : Fin 7, (c i • u i) * q := by
      simp [A, relationDirection, mul_comm]
    _ = relationPoly u c * q := by
      rw [relationPoly, Finset.sum_mul]

theorem A_relationDirection_eq_zero (u : RankSevenVec) (c : Fin 7 → ℝ) (q : Poly)
    (hrel : relationPoly u c = 0) :
    A u (relationDirection c q) = 0 := by
  rw [A_relationDirection, hrel]
  simp

theorem sigma_relationDirection (c : Fin 7 → ℝ) (q : Poly) :
    sigma (relationDirection c q) = (∑ i : Fin 7, (c i)^2) • (q ^ 2) := by
  calc
    sigma (relationDirection c q) = ∑ i : Fin 7, c i • c i • (q ^ 2) := by
      simp [sigma, relationDirection, pow_two]
    _ = ∑ i : Fin 7, ((c i)^2) • (q ^ 2) := by
      simp [pow_two, smul_smul]
    _ = (∑ i : Fin 7, (c i)^2) • (q ^ 2) := by
      rw [Finset.sum_smul]

theorem sum_sq_pos_of_ne_zero (c : Fin 7 → ℝ) (hc : c ≠ 0) :
    0 < ∑ i : Fin 7, (c i)^2 := by
  have hsnonneg : 0 ≤ ∑ i : Fin 7, (c i)^2 := by positivity
  have hsne : (∑ i : Fin 7, (c i)^2) ≠ 0 := by
    intro hs
    apply hc
    funext i
    have hzero :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (c j))).mp hs i (by simp)
    exact sq_eq_zero_iff.mp hzero
  exact lt_of_le_of_ne hsnonneg (by simpa using hsne.symm)

end Elementary

theorem false_of_negative_curvature_direction
    {B : DotForm} {p : Poly} {u v : RankSevenVec}
    (hsocp : IsSOCP B p u)
    (hvadm : IsAdmissibleDirection v)
    (hA : A u v = 0)
    (hneg : B (sigma v) (residual p u) < 0) :
    False := by
  have hhess : 0 ≤ hessianTerm B p u v := hsocp.2 v hvadm
  have hAterm : B (A u v) (A u v) = 0 := by
    rw [hA]
    simp
  have hsigma_nonneg : 0 ≤ B (sigma v) (residual p u) := by
    simpa [hessianTerm, hAterm] using hhess
  linarith

section Positivity

variable {B : DotForm} [Fact B.toQuadraticMap.PosDef]

/-- Rank-deficient factor points are not spurious: a nonzero scalar relation
among the seven coordinates lets every SOS summand be tested in a kernel
direction, forcing the residual to vanish. This formalizes the
rank-deficient branch of the blueprint. -/
theorem residual_eq_zero_of_constant_relation
    {p : Poly} {u : RankSevenVec} {c : Fin 7 → ℝ}
    (hu : IsAdmissiblePoint u)
    (hrel : relationPoly u c = 0)
    (hc : c ≠ 0)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let r := residual p u
  rcases hp with ⟨_, k, qs, hqdeg, hpq⟩
  let s : ℝ := ∑ i : Fin 7, (c i)^2
  have hspos : 0 < s := sum_sq_pos_of_ne_zero c hc
  have hsum_ge : 0 ≤ ∑ i : Fin k, B ((qs i)^2) r := by
    refine Finset.sum_nonneg ?_
    intro i _hi
    let w : RankSevenVec := relationDirection c (qs i)
    have hwadm : IsAdmissibleDirection w :=
      relationDirection_admissible c (hqdeg i)
    have hwA : A u w = 0 := A_relationDirection_eq_zero u c (qs i) hrel
    have hhess : 0 ≤ hessianTerm B p u w := hsocp.2 w hwadm
    have hsqi : 0 ≤ s * B ((qs i)^2) r := by
      simpa [w, s, r, hessianTerm, hwA, sigma_relationDirection] using hhess
    have : 0 ≤ B ((qs i)^2) (residual p u) := by
      nlinarith
    exact this
  have hp_ge : 0 ≤ B p r := by
    rw [hpq]
    simpa [r] using hsum_ge
  have hsigma_zero : B (sigma u) r = 0 :=
    focp_sigma_residual_eq_zero (B := B) hsocp.1 hu
  have hobj_formula : objective B p u = -(B p r) := by
    subst r
    have hsigma_zero' : B (sigma u) (sigma u - p) = 0 := by
      simpa [residual] using hsigma_zero
    calc
      objective B p u = B (sigma u - p) (sigma u - p) := by
        simp [objective, residual]
      _ = B (sigma u) (sigma u - p) - B p (sigma u - p) := by
        simp only [sub_eq_add_neg, dot_add_left, dot_neg_left]
      _ = -B p (sigma u - p) := by
        rw [hsigma_zero', zero_sub]
      _ = -(B p (residual p u)) := by
        simp [residual]
  have hle : objective B p u ≤ 0 := by
    rw [hobj_formula]
    linarith
  have hge : 0 ≤ objective B p u := objective_nonneg (B := B) p u
  have hobj : objective B p u = 0 := by
    linarith
  exact (objective_eq_zero_iff_residual_eq_zero (B := B)).mp hobj

theorem residual_eq_zero_of_relationPolyLin_ker_ne_bot
    {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hrelker : LinearMap.ker (relationPolyLin u) ≠ ⊥) :
    residual p u = 0 := by
  rcases Submodule.exists_mem_ne_zero_of_ne_bot hrelker with ⟨c, hc, hcne⟩
  have hrel : relationPoly u c = 0 := by
    simpa [relationPolyLin] using hc
  exact residual_eq_zero_of_constant_relation
    (B := B) (u := u) hu hrel hcne hp hsocp

theorem residual_eq_zero_or_relationPolyLin_ker_eq_bot
    {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 ∨ LinearMap.ker (relationPolyLin u) = ⊥ := by
  by_cases hrelker : LinearMap.ker (relationPolyLin u) = ⊥
  · exact Or.inr hrelker
  · exact Or.inl
      (residual_eq_zero_of_relationPolyLin_ker_ne_bot
        (B := B) hu hp hsocp hrelker)

end Positivity

end QuaternaryQuartic
