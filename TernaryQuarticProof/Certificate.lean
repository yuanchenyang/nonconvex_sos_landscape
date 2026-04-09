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

end TernaryQuartic
