import Mathlib.Tactic.Linarith
import TernaryQuarticProof.Socp

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace TernaryQuartic

/-- An admissible quartic in the image of `A_u`. The witness is kept explicit
because admissibility matters in the ternary-quartic model. -/
def InAdmissibleImage (u : RankFourVec) (q : Poly) : Prop :=
  ∃ v : RankFourVec, IsAdmissibleDirection v ∧ A u v = q

/-- An admissible kernel direction for `A_u`. -/
def InAdmissibleKer (u w : RankFourVec) : Prop :=
  IsAdmissibleDirection w ∧ A u w = 0

/-- The admissible image-plus-cone condition needed by the SOCP certificate
argument. Unlike the univariate reference, every witness here must remain
quadratic. -/
def InAdmissibleImagePlusSigmaKerCone (u : RankFourVec) (q : Poly) : Prop :=
  ∃ v : RankFourVec, ∃ ws : Finset RankFourVec,
    IsAdmissibleDirection v ∧
      (∀ w ∈ ws, InAdmissibleKer u w) ∧
      q = A u v + ws.sum sigma

/-- The residual at `u` is orthogonal to the admissible image of `uImg`. -/
def ImageOrthogonalResidual (B : DotForm) (p : Poly) (u uImg : RankFourVec) : Prop :=
  ∀ q : Poly, InAdmissibleImage uImg q → B q (residual p u) = 0

/-- Constant-coefficient scaling of a single quadratic polynomial into a
rank-4 direction. This is the basic kernel family used in the linearly
dependent case. -/
def relationDirection (c : Fin 4 → ℝ) (q : Poly) : RankFourVec :=
  fun i => c i • q

private theorem dot_sum_left {B : DotForm} (ws : Finset RankFourVec) (p : Poly) :
    B (ws.sum sigma) p = ws.sum (fun w => B (sigma w) p) := by
  classical
  refine Finset.induction_on ws ?_ ?_
  · simp
  · intro w ws hw ih
    calc
      B ((insert w ws).sum sigma) p = B (sigma w + ws.sum sigma) p := by
        simp [hw]
      _ = B (sigma w) p + B (ws.sum sigma) p := by
        simp
      _ = B (sigma w) p + ws.sum (fun w => B (sigma w) p) := by
        rw [ih]
      _ = (insert w ws).sum (fun w => B (sigma w) p) := by
        simp [hw]

section Positivity

variable {B : DotForm} [Fact B.toQuadraticMap.PosDef]

/-- Admissible transformed image-plus-cone data: the image term is taken with
respect to `uImg`, while the kernel directions are taken with respect to the
actual SOCP point `u`. -/
def InAdmissibleTransformedImagePlusSigmaKerCone
    (u uImg : RankFourVec) (q : Poly) : Prop :=
  ∃ imgPart : Poly, ∃ ws : Finset RankFourVec,
    InAdmissibleImage uImg imgPart ∧
      (∀ w ∈ ws, InAdmissibleKer u w) ∧
      q = imgPart + ws.sum sigma

/-- Abstract admissible image-plus-cone certificate. Once an SOS target admits
this decomposition relative to `u`, the SOCP conditions force zero residual. -/
theorem admissible_image_plus_cone_implies_objective_eq_zero
    {p : Poly} {u uImg : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    (himg : ImageOrthogonalResidual B p u uImg)
    (hdecomp : InAdmissibleTransformedImagePlusSigmaKerCone u uImg p) :
    objective B p u = 0 := by
  rcases hdecomp with ⟨imgPart, ws, himgPart, hker, hp⟩
  let r := residual p u
  have hImg : B imgPart r = 0 := himg _ himgPart
  have hsum_ge : 0 ≤ ws.sum (fun w => B (sigma w) r) := by
    refine Finset.sum_nonneg ?_
    intro w hw
    rcases hker w hw with ⟨hwadm, hwker⟩
    have hhess : 0 ≤ hessianTerm B p u w := hsocp.2 w hwadm
    have hAu : B (A u w) (A u w) = 0 := by
      rw [hwker]
      simp
    have hhess' : 0 ≤ B (sigma w) (residual p u) := by
      simpa [hessianTerm, hAu] using hhess
    exact hhess'
  have hp_ge : 0 ≤ B p r := by
    rw [hp, dot_add_left, dot_sum_left]
    linarith
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
  linarith

theorem admissible_image_plus_cone_residual_eq_zero
    {p : Poly} {u uImg : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    (himg : ImageOrthogonalResidual B p u uImg)
    (hdecomp : InAdmissibleTransformedImagePlusSigmaKerCone u uImg p) :
    residual p u = 0 := by
  exact (objective_eq_zero_iff_residual_eq_zero (B := B)).mp
    (admissible_image_plus_cone_implies_objective_eq_zero (B := B) hu hsocp himg hdecomp)

end Positivity

section Elementary

variable {B : DotForm}

theorem isAdmissibleDirection_zero : IsAdmissibleDirection (0 : RankFourVec) := by
  intro i
  simp [IsQuadratic]

theorem isAdmissibleDirection_add {v w : RankFourVec}
    (hv : IsAdmissibleDirection v) (hw : IsAdmissibleDirection w) :
    IsAdmissibleDirection (v + w) := by
  intro i
  exact (MvPolynomial.totalDegree_add _ _).trans <| max_le (hv i) (hw i)

theorem imageOrthogonalResidual_self {p : Poly} {u : RankFourVec}
    (hfocp : IsFOCP B p u) :
    ImageOrthogonalResidual B p u u := by
  intro q hq
  rcases hq with ⟨v, hv, rfl⟩
  exact hfocp v hv

theorem inAdmissibleImage_zero (u : RankFourVec) :
    InAdmissibleImage u 0 := by
  exact ⟨0, isAdmissibleDirection_zero, by simp [A]⟩

theorem inAdmissibleImage_add (u : RankFourVec) {p q : Poly}
    (hp : InAdmissibleImage u p) (hq : InAdmissibleImage u q) :
    InAdmissibleImage u (p + q) := by
  rcases hp with ⟨vp, hvp, rfl⟩
  rcases hq with ⟨vq, hvq, rfl⟩
  refine ⟨vp + vq, isAdmissibleDirection_add hvp hvq, ?_⟩
  simp [A, Finset.sum_add_distrib, mul_add]

theorem relationDirection_admissible (c : Fin 4 → ℝ) {q : Poly}
    (hq : IsQuadratic q) :
    IsAdmissibleDirection (relationDirection c q) := by
  intro i
  exact (MvPolynomial.totalDegree_smul_le (c i) q).trans hq

theorem A_relationDirection (u : RankFourVec) (c : Fin 4 → ℝ) (q : Poly) :
    A u (relationDirection c q) = (∑ i : Fin 4, c i • u i) * q := by
  calc
    A u (relationDirection c q) = ∑ i : Fin 4, (c i • u i) * q := by
      simp [A, relationDirection, mul_comm]
    _ = (∑ i : Fin 4, c i • u i) * q := by
      rw [Finset.sum_mul]

theorem A_relationDirection_eq_zero (u : RankFourVec) (c : Fin 4 → ℝ) (q : Poly)
    (hrel : ∑ i : Fin 4, c i • u i = 0) :
    A u (relationDirection c q) = 0 := by
  rw [A_relationDirection, hrel]
  simp

theorem sigma_relationDirection (c : Fin 4 → ℝ) (q : Poly) :
    sigma (relationDirection c q) = (∑ i : Fin 4, (c i)^2) • (q ^ 2) := by
  calc
    sigma (relationDirection c q) = ∑ i : Fin 4, c i • c i • (q ^ 2) := by
      simp [sigma, relationDirection, pow_two]
    _ = ∑ i : Fin 4, ((c i)^2) • (q ^ 2) := by
      simp [pow_two, smul_smul]
    _ = (∑ i : Fin 4, (c i)^2) • (q ^ 2) := by
      rw [Finset.sum_smul]

theorem sum_sq_pos_of_ne_zero (c : Fin 4 → ℝ) (hc : c ≠ 0) :
    0 < ∑ i : Fin 4, (c i)^2 := by
  have hsnonneg : 0 ≤ ∑ i : Fin 4, (c i)^2 := by positivity
  have hsne : (∑ i : Fin 4, (c i)^2) ≠ 0 := by
    intro hs
    apply hc
    funext i
    have hzero :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (c j))).mp hs i (by simp)
    exact sq_eq_zero_iff.mp hzero
  exact lt_of_le_of_ne hsnonneg (by simpa using hsne.symm)

end Elementary

section Positivity

variable {B : DotForm} [Fact B.toQuadraticMap.PosDef]

theorem residual_eq_zero_of_in_admissible_image
    {p : Poly} {u : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    (hpimg : InAdmissibleImage u p) :
    residual p u = 0 := by
  refine admissible_image_plus_cone_residual_eq_zero (B := B) hu hsocp
    (imageOrthogonalResidual_self (B := B) hsocp.1) ?_
  refine ⟨p, ∅, hpimg, ?_, by simp⟩
  intro w hw
  simp at hw

theorem residual_eq_zero_of_constant_relation
    {p : Poly} {u : RankFourVec} {c : Fin 4 → ℝ}
    (hu : IsAdmissiblePoint u)
    (hrel : ∑ i : Fin 4, c i • u i = 0)
    (hc : c ≠ 0)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let r := residual p u
  rcases hp with ⟨_, k, qs, hqdeg, hpq⟩
  let s : ℝ := ∑ i : Fin 4, (c i)^2
  have hspos : 0 < s := sum_sq_pos_of_ne_zero c hc
  have hsum_ge : 0 ≤ ∑ i : Fin k, B ((qs i)^2) r := by
    refine Finset.sum_nonneg ?_
    intro i hi
    let w : RankFourVec := relationDirection c (qs i)
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

end Positivity

end TernaryQuartic
