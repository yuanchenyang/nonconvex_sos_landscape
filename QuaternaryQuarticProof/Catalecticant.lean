import QuaternaryQuarticProof.Certificate

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace QuaternaryQuartic

/-- The submodule of affine-chart polynomials of total degree at most two. -/
def quadSubmodule : Submodule ℝ Poly where
  carrier := {q | IsQuadratic q}
  zero_mem' := by
    simp [IsQuadratic]
  add_mem' := by
    intro p q hp hq
    exact (MvPolynomial.totalDegree_add p q).trans (max_le hp hq)
  smul_mem' := by
    intro a q hq
    exact (MvPolynomial.totalDegree_smul_le a q).trans hq

@[simp] theorem mem_quadSubmodule {q : Poly} :
    q ∈ quadSubmodule ↔ IsQuadratic q := Iff.rfl

/-- Span of the seven quadratic coordinates of a rank-seven point. -/
def spanU (u : RankSevenVec) : Submodule ℝ Poly :=
  Submodule.span ℝ (Set.range u)

/-- Degree-two catalecticant kernel of the residual functional
`λ(f) = B(f, residual p u)`, kept as a submodule of `Poly` with the quadratic
degree bound in its carrier. -/
def catalecticantKernel (B : DotForm) (p : Poly) (u : RankSevenVec) :
    Submodule ℝ Poly where
  carrier :=
    {q | IsQuadratic q ∧
      ∀ r : Poly, IsQuadratic r → B (q * r) (residual p u) = 0}
  zero_mem' := by
    constructor
    · simp [IsQuadratic]
    · intro r _hr
      simp
  add_mem' := by
    intro q₁ q₂ hq₁ hq₂
    constructor
    · exact (MvPolynomial.totalDegree_add q₁ q₂).trans (max_le hq₁.1 hq₂.1)
    · intro r hr
      simp [add_mul, hq₁.2 r hr, hq₂.2 r hr]
  smul_mem' := by
    intro a q hq
    constructor
    · exact (MvPolynomial.totalDegree_smul_le a q).trans hq.1
    · intro r hr
      simp [hq.2 r hr]

@[simp] theorem mem_catalecticantKernel {B : DotForm} {p q : Poly} {u : RankSevenVec} :
    q ∈ catalecticantKernel B p u ↔
      IsQuadratic q ∧ ∀ r : Poly, IsQuadratic r → B (q * r) (residual p u) = 0 :=
  Iff.rfl

theorem singleDirection_admissible (i : Fin 7) {q : Poly}
    (hq : IsQuadratic q) :
    IsAdmissibleDirection (Pi.single i q : RankSevenVec) := by
  intro j
  by_cases hji : j = i
  · subst hji
    simpa using hq
  · simp [Pi.single_eq_of_ne hji, IsQuadratic]

theorem A_singleDirection (u : RankSevenVec) (i : Fin 7) (q : Poly) :
    A u (Pi.single i q) = u i * q := by
  classical
  unfold A
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    simp [Pi.single_eq_of_ne hji]
  · intro hi
    simp at hi

/-- FOCP implies every coordinate of `u`, and hence their span, lies in the
catalecticant kernel of the residual functional. -/
theorem spanU_le_catalecticantKernel {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hfocp : IsFOCP B p u) :
    spanU u ≤ catalecticantKernel B p u := by
  refine Submodule.span_le.mpr ?_
  rintro q ⟨i, rfl⟩
  constructor
  · exact hu i
  · intro r hr
    have hdir : IsAdmissibleDirection (Pi.single i r : RankSevenVec) :=
      singleDirection_admissible i hr
    simpa [A_singleDirection] using hfocp (Pi.single i r) hdir

section ResidualFunctional

variable {B : DotForm} [Fact B.toQuadraticMap.PosDef]

/-- Under nonzero residual, FOCP at `u` makes the residual functional negative
on the SOS target. -/
theorem target_dot_residual_negative {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hfocp : IsFOCP B p u)
    (hres : residual p u ≠ 0) :
    B p (residual p u) < 0 := by
  let r := residual p u
  have hsigma_zero : B (sigma u) r = 0 :=
    focp_sigma_residual_eq_zero (B := B) hfocp hu
  have hobj_ne : objective B p u ≠ 0 := by
    intro hobj
    exact hres ((objective_eq_zero_iff_residual_eq_zero (B := B)).mp hobj)
  have hobj_nonneg : 0 ≤ objective B p u := objective_nonneg (B := B) p u
  have hobj_pos : 0 < objective B p u :=
    lt_of_le_of_ne hobj_nonneg (by exact hobj_ne.symm)
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
  nlinarith

omit [Fact B.toQuadraticMap.PosDef] in
private theorem dot_finset_sum_left {ι : Type*} (s : Finset ι) (f : ι → Poly)
    (r : Poly) :
    B (∑ i ∈ s, f i) r = ∑ i ∈ s, B (f i) r := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s hi ih
    calc
      B (∑ j ∈ insert i s, f j) r = B (f i + ∑ j ∈ s, f j) r := by
        simp [hi]
      _ = B (f i) r + B (∑ j ∈ s, f j) r := by
        simp
      _ = B (f i) r + ∑ j ∈ s, B (f j) r := by
        rw [ih]
      _ = ∑ j ∈ insert i s, B (f j) r := by
        simp [hi]

omit [Fact B.toQuadraticMap.PosDef] in
/-- A negative value of the residual functional on an SOS target is witnessed
by one quadratic SOS summand. -/
theorem exists_negative_sos_summand {p : Poly} {u : RankSevenVec}
    (hp : IsSOSQuartic p)
    (hneg : B p (residual p u) < 0) :
    ∃ q : Poly, IsQuadratic q ∧ B (q ^ 2) (residual p u) < 0 := by
  rcases hp with ⟨_hpquartic, k, qs, hqdeg, hpq⟩
  by_contra hnone
  push Not at hnone
  have hsum_nonneg : 0 ≤ ∑ i : Fin k, B ((qs i)^2) (residual p u) := by
    exact Finset.sum_nonneg (fun i _hi => hnone (qs i) (hqdeg i))
  have hp_sum :
      B p (residual p u) = ∑ i : Fin k, B ((qs i)^2) (residual p u) := by
    calc
      B p (residual p u) = B (∑ i : Fin k, (qs i)^2) (residual p u) := by
        rw [hpq]
      _ = ∑ i : Fin k, B ((qs i)^2) (residual p u) := by
        exact dot_finset_sum_left (B := B) Finset.univ (fun i : Fin k => (qs i)^2)
          (residual p u)
  have hp_nonneg : 0 ≤ B p (residual p u) := by
    rw [hp_sum]
    exact hsum_nonneg
  linarith

theorem exists_negative_sos_summand_of_nonzero_residual {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u)
    (hres : residual p u ≠ 0) :
    ∃ q : Poly, IsQuadratic q ∧ B (q ^ 2) (residual p u) < 0 :=
  exists_negative_sos_summand (B := B) hp
    (target_dot_residual_negative (B := B) hu hfocp hres)

end ResidualFunctional

end QuaternaryQuartic
