import Mathlib.Tactic.Linarith
import TernaryQuartic.TernaryQuarticProof.Socp

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
/-- The residual at `u` is orthogonal to the admissible image of `uImg`. -/
def ImageOrthogonalResidual (B : DotForm) (p : Poly) (u uImg : RankFourVec) : Prop :=
  ∀ q : Poly, InAdmissibleImage uImg q → B q (residual p u) = 0

/-- Constant-coefficient scaling of a single quadratic polynomial into a
rank-4 direction. This is the basic kernel family used in the linearly
dependent case. -/
def relationDirection (c : Fin 4 → ℝ) (q : Poly) : RankFourVec :=
  fun i => c i • q

/-- The polynomial produced by a scalar relation vector on a rank-4 point. -/
def relationPoly (u : RankFourVec) (c : Fin 4 → ℝ) : Poly :=
  ∑ i : Fin 4, c i • u i

theorem relationPoly_add
    (u : RankFourVec) (c d : Fin 4 → ℝ) :
    relationPoly u (c + d) = relationPoly u c + relationPoly u d := by
  simp [relationPoly, Fin.sum_univ_four, add_smul, add_assoc, add_left_comm]

theorem relationPoly_smul
    (u : RankFourVec) (a : ℝ) (c : Fin 4 → ℝ) :
    relationPoly u (a • c) = a • relationPoly u c := by
  simp [relationPoly, Fin.sum_univ_four, smul_smul]

theorem relationPoly_eq_of_sum
    {u : RankFourVec} {c : Fin 4 → ℝ} {r : Poly}
    (hc : ∑ i : Fin 4, c i • u i = r) :
    relationPoly u c = r := by
  simpa [relationPoly] using hc

theorem relationPoly_neg
    (u : RankFourVec) (c : Fin 4 → ℝ) :
    relationPoly u (-c) = -relationPoly u c := by
  calc
    relationPoly u (-c) = relationPoly u ((-1 : ℝ) • c) := by simp
    _ = (-1 : ℝ) • relationPoly u c := relationPoly_smul u (-1) c
    _ = -relationPoly u c := by simp

/-- Linear map version of `relationPoly`. -/
def relationPolyLin (u : RankFourVec) : (Fin 4 → ℝ) →ₗ[ℝ] Poly where
  toFun := relationPoly u
  map_add' := relationPoly_add u
  map_smul' := relationPoly_smul u

theorem isQuadratic_relationPoly
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

omit [Fact B.toQuadraticMap.PosDef] in
private theorem dot_biSum_left {ι : Type*} (s : Finset ι) (w : ι → RankFourVec) (p : Poly) :
    B (Finset.sum s (fun i => sigma (w i))) p = Finset.sum s (fun i => B (sigma (w i)) p) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s hi ih
    calc
      B (Finset.sum (insert i s) (fun j => sigma (w j))) p
          = B (sigma (w i) + Finset.sum s (fun j => sigma (w j))) p := by
        simp [hi]
      _ = B (sigma (w i)) p + B (Finset.sum s (fun j => sigma (w j))) p := by
        simp
      _ = B (sigma (w i)) p + Finset.sum s (fun j => B (sigma (w j)) p) := by
        rw [ih]
      _ = Finset.sum (insert i s) (fun j => B (sigma (w j)) p) := by
        simp [hi]

theorem admissible_image_plus_indexed_sigma_family_residual_eq_zero
    {ι : Type*} {p : Poly} {u uImg : RankFourVec}
    (hu : IsAdmissiblePoint u)
    (hsocp : IsSOCP B p u)
    (himg : ImageOrthogonalResidual B p u uImg)
    {imgPart : Poly} {s : Finset ι} {w : ι → RankFourVec}
    (himgPart : InAdmissibleImage uImg imgPart)
    (hker : ∀ i ∈ s, InAdmissibleKer u (w i))
    (hdecomp : p = imgPart + Finset.sum s (fun i => sigma (w i))) :
    residual p u = 0 := by
  let r := residual p u
  have hImg : B imgPart r = 0 := himg _ himgPart
  have hsum_ge : 0 ≤ Finset.sum s (fun i => B (sigma (w i)) r) := by
    refine Finset.sum_nonneg ?_
    intro i hi
    rcases hker i hi with ⟨hwadm, hwker⟩
    have hhess : 0 ≤ hessianTerm B p u (w i) := hsocp.2 (w i) hwadm
    have hAu : B (A u (w i)) (A u (w i)) = 0 := by
      rw [hwker]
      simp
    have hhess' : 0 ≤ B (sigma (w i)) (residual p u) := by
      simpa [hessianTerm, hAu] using hhess
    exact hhess'
  have hp_ge : 0 ≤ B p r := by
    rw [hdecomp, dot_add_left, dot_biSum_left]
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
  exact (objective_eq_zero_iff_residual_eq_zero (B := B)).mp (by linarith)

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

theorem isAdmissibleDirection_smul (t : ℝ) {v : RankFourVec}
    (hv : IsAdmissibleDirection v) :
    IsAdmissibleDirection (t • v) := by
  intro i
  exact (MvPolynomial.totalDegree_smul_le t (v i)).trans (hv i)

theorem A_smul_right (u v : RankFourVec) (t : ℝ) :
    A u (t • v) = t • A u v := by
  calc
    A u (t • v) = ∑ i : Fin 4, t • (u i * v i) := by
      unfold A
      refine Finset.sum_congr rfl ?_
      intro i hi
      change u i * (t • v i) = t • (u i * v i)
      exact mul_smul_comm t (u i) (v i)
    _ = t • ∑ i : Fin 4, u i * v i := by
      rw [← Finset.smul_sum]
    _ = t • A u v := by
      simp [A]

theorem isQuartic_sigma_of_admissible {u : RankFourVec}
    (hu : IsAdmissibleDirection u) :
    IsQuartic (sigma u) := by
  unfold sigma IsQuartic
  refine MvPolynomial.totalDegree_finsetSum_le ?_
  intro i hi
  have hpow : ((u i) ^ 2).totalDegree ≤ 2 * (u i).totalDegree := by
    simpa using MvPolynomial.totalDegree_pow (u i) 2
  have hi2 : (u i).totalDegree ≤ 2 := hu i
  omega

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

theorem inAdmissibleImage_smul (u : RankFourVec) (t : ℝ) {p : Poly}
    (hp : InAdmissibleImage u p) :
    InAdmissibleImage u (t • p) := by
  rcases hp with ⟨v, hv, rfl⟩
  refine ⟨t • v, isAdmissibleDirection_smul t hv, ?_⟩
  rw [A_smul_right]

theorem inAdmissibleImage_neg (u : RankFourVec) {p : Poly}
    (hp : InAdmissibleImage u p) :
    InAdmissibleImage u (-p) := by
  simpa using inAdmissibleImage_smul u (-1) hp

theorem inAdmissibleImage_sub (u : RankFourVec) {p q : Poly}
    (hp : InAdmissibleImage u p) (hq : InAdmissibleImage u q) :
    InAdmissibleImage u (p - q) := by
  simpa [sub_eq_add_neg] using inAdmissibleImage_add u hp (inAdmissibleImage_neg u hq)

theorem inAdmissibleKer_add (u : RankFourVec) {w z : RankFourVec}
    (hw : InAdmissibleKer u w) (hz : InAdmissibleKer u z) :
    InAdmissibleKer u (w + z) := by
  rcases hw with ⟨hwad, hwA⟩
  rcases hz with ⟨hzad, hzA⟩
  refine ⟨isAdmissibleDirection_add hwad hzad, ?_⟩
  calc
    A u (w + z) = A u w + A u z := by
      simp [A, Finset.sum_add_distrib, mul_add]
    _ = 0 := by simp [hwA, hzA]

theorem inAdmissibleKer_smul (u : RankFourVec) (t : ℝ) {w : RankFourVec}
    (hw : InAdmissibleKer u w) :
    InAdmissibleKer u (t • w) := by
  rcases hw with ⟨hwad, hwA⟩
  refine ⟨isAdmissibleDirection_smul t hwad, ?_⟩
  rw [A_smul_right, hwA]
  simp

theorem inAdmissibleKer_neg (u : RankFourVec) {w : RankFourVec}
    (hw : InAdmissibleKer u w) :
    InAdmissibleKer u (-w) := by
  simpa using inAdmissibleKer_smul u (-1) hw
theorem relationDirection_admissible (c : Fin 4 → ℝ) {q : Poly}
    (hq : IsQuadratic q) :
    IsAdmissibleDirection (relationDirection c q) := by
  intro i
  exact (MvPolynomial.totalDegree_smul_le (c i) q).trans hq

theorem A_relationDirection (u : RankFourVec) (c : Fin 4 → ℝ) (q : Poly) :
    A u (relationDirection c q) = relationPoly u c * q := by
  calc
    A u (relationDirection c q) = ∑ i : Fin 4, (c i • u i) * q := by
      simp [A, relationDirection, mul_comm]
    _ = relationPoly u c * q := by
      rw [relationPoly]
      rw [Finset.sum_mul]

theorem A_relationDirection_eq_zero (u : RankFourVec) (c : Fin 4 → ℝ) (q : Poly)
    (hrel : relationPoly u c = 0) :
    A u (relationDirection c q) = 0 := by
  rw [A_relationDirection, hrel]
  simp

theorem inAdmissibleImage_of_relation_mul
    {u : RankFourVec} {c : Fin 4 → ℝ} {r q : Poly}
    (hc : ∑ i : Fin 4, c i • u i = r)
    (hq : IsQuadratic q) :
    InAdmissibleImage u (r * q) := by
  refine ⟨relationDirection c q, relationDirection_admissible c hq, ?_⟩
  rw [A_relationDirection, relationPoly]
  rw [hc]

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
