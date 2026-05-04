import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.Finsupp.Order
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fintype.Pi
import QuaternaryQuarticProof.Certificate

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace QuaternaryQuartic

open scoped BigOperators

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

theorem quadSubmodule_eq_restrictTotalDegree :
    quadSubmodule = MvPolynomial.restrictTotalDegree (Fin 3) ℝ 2 := by
  ext q
  simp [quadSubmodule, IsQuadratic, MvPolynomial.mem_restrictTotalDegree]

instance instModuleFiniteQuadSubmodule : Module.Finite ℝ quadSubmodule := by
  rw [quadSubmodule_eq_restrictTotalDegree]
  infer_instance

private abbrev QuadExponentSet :=
  {s : Fin 3 →₀ ℕ // s.sum (fun _ e => e) ≤ 2}

private abbrev BoundedFinTriple :=
  {f : Fin 3 → Fin 3 // (∑ i, (f i).val) ≤ 2}

private theorem finsupp_value_lt_three (s : Fin 3 →₀ ℕ)
    (hs : s.sum (fun _ e => e) ≤ 2) (i : Fin 3) :
    s i < 3 := by
  have hle_sum : s i ≤ s.sum (fun _ e => e) := by
    simpa using
      (Finsupp.single_eval_le_sum (f := s) (g := fun n : ℕ => n)
        (by simp) (fun n => Nat.zero_le n) i)
  omega

private theorem finsupp_sum_eq_finset_sum (s : Fin 3 →₀ ℕ) :
    s.sum (fun _ e => e) = ∑ i, s i := by
  rw [Finsupp.sum_fintype]
  intro i
  simp

private theorem equivFunOnFinite_symm_sum_finTriple (f : Fin 3 → Fin 3) :
    (Finsupp.equivFunOnFinite.symm (fun i => (f i).val)).sum (fun _ e => e) =
      ∑ i, (f i).val := by
  simpa using
    (Finsupp.equivFunOnFinite_symm_sum (f := fun i : Fin 3 => (f i).val))

private def quadExponentEquivBoundedFinTriple :
    QuadExponentSet ≃ BoundedFinTriple where
  toFun s := ⟨fun i => ⟨s.1 i, finsupp_value_lt_three s.1 s.2 i⟩, by
    simpa [finsupp_sum_eq_finset_sum s.1] using s.2⟩
  invFun f := ⟨Finsupp.equivFunOnFinite.symm (fun i => (f.1 i).val), by
    simpa [equivFunOnFinite_symm_sum_finTriple f.1] using f.2⟩
  left_inv := by
    intro s
    apply Subtype.ext
    ext i
    simp
  right_inv := by
    intro f
    apply Subtype.ext
    ext i
    simp

private theorem natCard_quadExponentSet :
    Nat.card QuadExponentSet = 10 := by
  rw [Nat.card_congr quadExponentEquivBoundedFinTriple]
  rw [Nat.card_eq_fintype_card]
  decide

theorem finrank_quadSubmodule_eq_ten :
    Module.finrank ℝ quadSubmodule = 10 := by
  rw [quadSubmodule_eq_restrictTotalDegree]
  change Module.finrank ℝ
    (MvPolynomial.restrictSupport ℝ {n : Fin 3 →₀ ℕ | n.sum (fun _ e => e) ≤ 2}) = 10
  rw [Module.finrank_eq_nat_card_basis
    (MvPolynomial.basisRestrictSupport ℝ
      {n : Fin 3 →₀ ℕ | n.sum (fun _ e => e) ≤ 2})]
  exact natCard_quadExponentSet

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

theorem spanU_le_quadSubmodule {u : RankSevenVec}
    (hu : IsAdmissiblePoint u) :
    spanU u ≤ quadSubmodule := by
  refine Submodule.span_le.mpr ?_
  rintro q ⟨i, rfl⟩
  exact hu i

/-- Trivial kernel of the scalar-relation map is the full-rank condition for
the seven quadratic coordinates. -/
theorem linearIndependent_u_of_relationPolyLin_ker_eq_bot {u : RankSevenVec}
    (hker : LinearMap.ker (relationPolyLin u) = ⊥) :
    LinearIndependent ℝ u := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hgker : g ∈ LinearMap.ker (relationPolyLin u) := by
    change relationPolyLin u g = 0
    simpa [relationPolyLin, relationPoly] using hg
  have hgzero : g = 0 := by
    have : g ∈ (⊥ : Submodule ℝ (Fin 7 → ℝ)) := by
      simpa [hker] using hgker
    simpa using this
  exact congrFun hgzero i

theorem finrank_spanU_eq_seven_of_relationPolyLin_ker_eq_bot {u : RankSevenVec}
    (hker : LinearMap.ker (relationPolyLin u) = ⊥) :
    Module.finrank ℝ (spanU u) = 7 := by
  have hli : LinearIndependent ℝ u :=
    linearIndependent_u_of_relationPolyLin_ker_eq_bot hker
  calc
    Module.finrank ℝ (spanU u) =
        Module.finrank ℝ (Submodule.span ℝ (Set.range u)) := rfl
    _ = Fintype.card (Fin 7) := finrank_span_eq_card hli
    _ = 7 := by simp

def spanUQuad {u : RankSevenVec} (hu : IsAdmissiblePoint u) :
    Submodule ℝ quadSubmodule :=
  Submodule.span ℝ (Set.range fun i : Fin 7 => (⟨u i, hu i⟩ : quadSubmodule))

theorem exists_relationPoly_eq_of_mem_spanUQuad {u : RankSevenVec}
    {hu : IsAdmissiblePoint u} {x : quadSubmodule}
    (hx : x ∈ spanUQuad hu) :
    ∃ c : Fin 7 → ℝ, relationPoly u c = x.1 := by
  rcases (Submodule.mem_span_range_iff_exists_fun (R := ℝ)).mp hx with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  have hval := congrArg Subtype.val hc
  simpa [spanUQuad, relationPoly] using hval

theorem exists_relationPoly_eq_of_mem_spanU {u : RankSevenVec} {x : Poly}
    (hx : x ∈ spanU u) :
    ∃ c : Fin 7 → ℝ, relationPoly u c = x := by
  rcases (Submodule.mem_span_range_iff_exists_fun (R := ℝ)).mp hx with ⟨c, hc⟩
  exact ⟨c, by simpa [spanU, relationPoly] using hc⟩

theorem linearIndependent_uQuad_of_relationPolyLin_ker_eq_bot {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hker : LinearMap.ker (relationPolyLin u) = ⊥) :
    LinearIndependent ℝ (fun i : Fin 7 => (⟨u i, hu i⟩ : quadSubmodule)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hli : LinearIndependent ℝ u :=
    linearIndependent_u_of_relationPolyLin_ker_eq_bot hker
  have hsum_poly : ∑ i : Fin 7, g i • u i = 0 := by
    have hcongr := congrArg Subtype.val hg
    simpa using hcongr
  exact (Fintype.linearIndependent_iff.mp hli g hsum_poly i)

theorem finrank_spanUQuad_eq_seven_of_relationPolyLin_ker_eq_bot {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hker : LinearMap.ker (relationPolyLin u) = ⊥) :
    Module.finrank ℝ (spanUQuad hu) = 7 := by
  have hli : LinearIndependent ℝ (fun i : Fin 7 => (⟨u i, hu i⟩ : quadSubmodule)) :=
    linearIndependent_uQuad_of_relationPolyLin_ker_eq_bot hu hker
  calc
    Module.finrank ℝ (spanUQuad hu) =
        Module.finrank ℝ
          (Submodule.span ℝ
            (Set.range fun i : Fin 7 => (⟨u i, hu i⟩ : quadSubmodule))) := rfl
    _ = Fintype.card (Fin 7) := finrank_span_eq_card hli
    _ = 7 := by simp

def catalecticantMap (B : DotForm) (p : Poly) (u : RankSevenVec) :
    quadSubmodule →ₗ[ℝ] Module.Dual ℝ quadSubmodule where
  toFun q := {
    toFun := fun r => B (q.1 * r.1) (residual p u)
    map_add' := by
      intro r s
      simp [mul_add]
    map_smul' := by
      intro a r
      simp }
  map_add' q r := by
    ext s
    simp [add_mul]
  map_smul' a q := by
    ext r
    simp

@[simp] theorem catalecticantMap_apply
    (B : DotForm) (p : Poly) (u : RankSevenVec) (q r : quadSubmodule) :
    catalecticantMap B p u q r = B (q.1 * r.1) (residual p u) :=
  rfl

theorem spanUQuad_le_ker_catalecticantMap {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hfocp : IsFOCP B p u) :
    spanUQuad hu ≤ LinearMap.ker (catalecticantMap B p u) := by
  refine Submodule.span_le.mpr ?_
  rintro q ⟨i, rfl⟩
  change catalecticantMap B p u (⟨u i, hu i⟩ : quadSubmodule) = 0
  ext r
  have hdir : IsAdmissibleDirection (Pi.single i r.1 : RankSevenVec) :=
    singleDirection_admissible i r.2
  simpa [A_singleDirection] using hfocp (Pi.single i r.1) hdir

theorem catalecticantMap_rank_le_three_of_relationPolyLin_ker_eq_bot
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hfocp : IsFOCP B p u)
    (hker : LinearMap.ker (relationPolyLin u) = ⊥) :
    Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) ≤ 3 := by
  have hspan_le :
      spanUQuad hu ≤ LinearMap.ker (catalecticantMap B p u) :=
    spanUQuad_le_ker_catalecticantMap hu hfocp
  have hspan_finrank :
      Module.finrank ℝ (spanUQuad hu) = 7 :=
    finrank_spanUQuad_eq_seven_of_relationPolyLin_ker_eq_bot hu hker
  have hker_ge : 7 ≤ Module.finrank ℝ (LinearMap.ker (catalecticantMap B p u)) := by
    rw [← hspan_finrank]
    exact Submodule.finrank_mono hspan_le
  have hnullity :=
    LinearMap.finrank_range_add_finrank_ker (catalecticantMap B p u)
  have hquad : Module.finrank ℝ quadSubmodule = 10 :=
    finrank_quadSubmodule_eq_ten
  omega

theorem catalecticantMap_rank_pos_of_negative_square
    {B : DotForm} {p : Poly} {u : RankSevenVec} {q : Poly}
    (hq : IsQuadratic q)
    (hneg : B (q^2) (residual p u) < 0) :
    0 < Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) := by
  rw [Nat.pos_iff_ne_zero]
  intro hrank_zero
  have hrange_bot : LinearMap.range (catalecticantMap B p u) = ⊥ := by
    exact Submodule.finrank_eq_zero.mp hrank_zero
  let qQuad : quadSubmodule := ⟨q, hq⟩
  have hmap_mem : catalecticantMap B p u qQuad ∈
      LinearMap.range (catalecticantMap B p u) := by
    exact ⟨qQuad, rfl⟩
  have hmap_zero : catalecticantMap B p u qQuad = 0 := by
    have : catalecticantMap B p u qQuad ∈ (⊥ : Submodule ℝ (Module.Dual ℝ quadSubmodule)) := by
      simpa [hrange_bot] using hmap_mem
    simpa using this
  have hval_zero :
      B (q * q) (residual p u) = 0 := by
    have hcongr := congrArg (fun φ : Module.Dual ℝ quadSubmodule => φ qQuad) hmap_zero
    simpa [qQuad] using hcongr
  have : B (q^2) (residual p u) = 0 := by
    simpa [pow_two] using hval_zero
  linarith

theorem catalecticantMap_rank_eq_one_or_two_or_three
    {B : DotForm} {p : Poly} {u : RankSevenVec} {q : Poly}
    (hu : IsAdmissiblePoint u)
    (hfocp : IsFOCP B p u)
    (hker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hq : IsQuadratic q)
    (hneg : B (q^2) (residual p u) < 0) :
    Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 ∨
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 ∨
        Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 := by
  have hpos :
      0 < Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) :=
    catalecticantMap_rank_pos_of_negative_square hq hneg
  have hle :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) ≤ 3 :=
    catalecticantMap_rank_le_three_of_relationPolyLin_ker_eq_bot hu hfocp hker
  omega

theorem spanUQuad_eq_ker_catalecticantMap_of_rank_three
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hfocp : IsFOCP B p u)
    (hker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3) :
    spanUQuad hu = LinearMap.ker (catalecticantMap B p u) := by
  have hle : spanUQuad hu ≤ LinearMap.ker (catalecticantMap B p u) :=
    spanUQuad_le_ker_catalecticantMap hu hfocp
  have hspan : Module.finrank ℝ (spanUQuad hu) = 7 :=
    finrank_spanUQuad_eq_seven_of_relationPolyLin_ker_eq_bot hu hker
  have hnullity :=
    LinearMap.finrank_range_add_finrank_ker (catalecticantMap B p u)
  have hquad : Module.finrank ℝ quadSubmodule = 10 :=
    finrank_quadSubmodule_eq_ten
  have hker_finrank :
      Module.finrank ℝ (LinearMap.ker (catalecticantMap B p u)) = 7 := by
    omega
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hspan, hker_finrank])

theorem finrank_ker_catalecticantMap_eq_nine_of_rank_one
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1) :
    Module.finrank ℝ (LinearMap.ker (catalecticantMap B p u)) = 9 := by
  have hnullity :=
    LinearMap.finrank_range_add_finrank_ker (catalecticantMap B p u)
  have hquad : Module.finrank ℝ quadSubmodule = 10 :=
    finrank_quadSubmodule_eq_ten
  omega

theorem finrank_ker_catalecticantMap_eq_eight_of_rank_two
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2) :
    Module.finrank ℝ (LinearMap.ker (catalecticantMap B p u)) = 8 := by
  have hnullity :=
    LinearMap.finrank_range_add_finrank_ker (catalecticantMap B p u)
  have hquad : Module.finrank ℝ quadSubmodule = 10 :=
    finrank_quadSubmodule_eq_ten
  omega

theorem finrank_ker_catalecticantMap_eq_seven_of_rank_three
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3) :
    Module.finrank ℝ (LinearMap.ker (catalecticantMap B p u)) = 7 := by
  have hnullity :=
    LinearMap.finrank_range_add_finrank_ker (catalecticantMap B p u)
  have hquad : Module.finrank ℝ quadSubmodule = 10 :=
    finrank_quadSubmodule_eq_ten
  omega

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
