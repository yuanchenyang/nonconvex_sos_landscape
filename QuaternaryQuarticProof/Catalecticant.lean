import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Finsupp.Order
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fintype.Pi
import QuaternaryQuarticProof.Certificate
import QuaternaryQuarticProof.Dimension

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace QuaternaryQuartic

open scoped BigOperators

/-- The submodule of affine-chart polynomials of total degree at most one. -/
def linSubmodule : Submodule ℝ Poly where
  carrier := {q | q.totalDegree ≤ 1}
  zero_mem' := by
    simp
  add_mem' := by
    intro p q hp hq
    exact (MvPolynomial.totalDegree_add p q).trans (max_le hp hq)
  smul_mem' := by
    intro a q hq
    exact (MvPolynomial.totalDegree_smul_le a q).trans hq

@[simp] theorem mem_linSubmodule {q : Poly} :
    q ∈ linSubmodule ↔ q.totalDegree ≤ 1 := Iff.rfl

theorem linSubmodule_eq_restrictTotalDegree :
    linSubmodule = MvPolynomial.restrictTotalDegree (Fin 3) ℝ 1 := by
  ext q
  simp [linSubmodule, MvPolynomial.mem_restrictTotalDegree]

instance instModuleFiniteLinSubmodule : Module.Finite ℝ linSubmodule := by
  rw [linSubmodule_eq_restrictTotalDegree]
  infer_instance

private abbrev LinExponentSet :=
  {s : Fin 3 →₀ ℕ // s.sum (fun _ e => e) ≤ 1}

private abbrev BoundedFinTripleOne :=
  {f : Fin 3 → Fin 2 // (∑ i, (f i).val) ≤ 1}

private theorem finsupp_sum_eq_finset_sum (s : Fin 3 →₀ ℕ) :
    s.sum (fun _ e => e) = ∑ i, s i := by
  rw [Finsupp.sum_fintype]
  intro i
  simp

private theorem finsupp_value_lt_two (s : Fin 3 →₀ ℕ)
    (hs : s.sum (fun _ e => e) ≤ 1) (i : Fin 3) :
    s i < 2 := by
  have hle_sum : s i ≤ s.sum (fun _ e => e) := by
    simpa using
      (Finsupp.single_eval_le_sum (f := s) (g := fun n : ℕ => n)
        (by simp) (fun n => Nat.zero_le n) i)
  omega

private theorem equivFunOnFinite_symm_sum_finTripleOne (f : Fin 3 → Fin 2) :
    (Finsupp.equivFunOnFinite.symm (fun i => (f i).val)).sum (fun _ e => e) =
      ∑ i, (f i).val := by
  simpa using
    (Finsupp.equivFunOnFinite_symm_sum (f := fun i : Fin 3 => (f i).val))

private def linExponentEquivBoundedFinTripleOne :
    LinExponentSet ≃ BoundedFinTripleOne where
  toFun s := ⟨fun i => ⟨s.1 i, finsupp_value_lt_two s.1 s.2 i⟩, by
    simpa [finsupp_sum_eq_finset_sum s.1] using s.2⟩
  invFun f := ⟨Finsupp.equivFunOnFinite.symm (fun i => (f.1 i).val), by
    simpa [equivFunOnFinite_symm_sum_finTripleOne f.1] using f.2⟩
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

private theorem natCard_linExponentSet :
    Nat.card LinExponentSet = 4 := by
  rw [Nat.card_congr linExponentEquivBoundedFinTripleOne]
  rw [Nat.card_eq_fintype_card]
  decide

theorem finrank_linSubmodule_eq_four :
    Module.finrank ℝ linSubmodule = 4 := by
  rw [linSubmodule_eq_restrictTotalDegree]
  change Module.finrank ℝ
    (MvPolynomial.restrictSupport ℝ {n : Fin 3 →₀ ℕ | n.sum (fun _ e => e) ≤ 1}) = 4
  rw [Module.finrank_eq_nat_card_basis
    (MvPolynomial.basisRestrictSupport ℝ
      {n : Fin 3 →₀ ℕ | n.sum (fun _ e => e) ≤ 1})]
  exact natCard_linExponentSet

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

theorem mul_lin_lin_mem_quad {p q : Poly}
    (hp : p ∈ linSubmodule) (hq : q ∈ linSubmodule) :
    p * q ∈ quadSubmodule := by
  have hmul : (p * q).totalDegree ≤ p.totalDegree + q.totalDegree :=
    MvPolynomial.totalDegree_mul p q
  have hp1 : p.totalDegree ≤ 1 := hp
  have hq1 : q.totalDegree ≤ 1 := hq
  change (p * q).totalDegree ≤ 2
  omega

def linOne : linSubmodule :=
  ⟨1, by simp⟩

@[simp] theorem linOne_val : (linOne : Poly) = 1 := rfl

def linVar (i : Fin 3) : linSubmodule :=
  ⟨MvPolynomial.X i, (MvPolynomial.isHomogeneous_X (R := ℝ) i).totalDegree_le⟩

@[simp] theorem linVar_val (i : Fin 3) : (linVar i : Poly) = MvPolynomial.X i := rfl

def linProduct (a b : linSubmodule) : quadSubmodule :=
  ⟨a.1 * b.1, mul_lin_lin_mem_quad a.2 b.2⟩

@[simp] theorem linProduct_val (a b : linSubmodule) :
    (linProduct a b : Poly) = a.1 * b.1 := rfl

@[simp] theorem linProduct_add_left (a b c : linSubmodule) :
    linProduct (a + b) c = linProduct a c + linProduct b c := by
  ext
  simp [linProduct, add_mul]

@[simp] theorem linProduct_add_right (a b c : linSubmodule) :
    linProduct a (b + c) = linProduct a b + linProduct a c := by
  ext
  simp [linProduct, mul_add]

@[simp] theorem linProduct_smul_left (a : ℝ) (b c : linSubmodule) :
    linProduct (a • b) c = a • linProduct b c := by
  ext
  simp [linProduct]

@[simp] theorem linProduct_smul_right (a : ℝ) (b c : linSubmodule) :
    linProduct b (a • c) = a • linProduct b c := by
  ext
  simp [linProduct]

@[simp] theorem linProduct_zero_left (a : linSubmodule) :
    linProduct 0 a = 0 := by
  ext
  simp [linProduct]

@[simp] theorem linProduct_zero_right (a : linSubmodule) :
    linProduct a 0 = 0 := by
  ext
  simp [linProduct]

theorem linProduct_comm (a b : linSubmodule) :
    linProduct a b = linProduct b a := by
  ext
  simp [linProduct, mul_comm]

def linProductSubmodule (U V : Submodule ℝ linSubmodule) :
    Submodule ℝ quadSubmodule :=
  Submodule.span ℝ (Set.range fun x : U × V => linProduct x.1.1 x.2.1)

def symSquareSubmodule (U : Submodule ℝ linSubmodule) :
    Submodule ℝ quadSubmodule :=
  linProductSubmodule U U

theorem linProduct_mem_linProductSubmodule
    {U V : Submodule ℝ linSubmodule} (a : U) (b : V) :
    linProduct a.1 b.1 ∈ linProductSubmodule U V := by
  exact Submodule.subset_span ⟨(a, b), rfl⟩

theorem linProductSubmodule_mono
    {U₁ U₂ V₁ V₂ : Submodule ℝ linSubmodule}
    (hU : U₁ ≤ U₂) (hV : V₁ ≤ V₂) :
    linProductSubmodule U₁ V₁ ≤ linProductSubmodule U₂ V₂ := by
  refine Submodule.span_le.mpr ?_
  rintro q ⟨x, rfl⟩
  exact linProduct_mem_linProductSubmodule
    (⟨x.1.1, hU x.1.2⟩ : U₂) (⟨x.2.1, hV x.2.2⟩ : V₂)

theorem linProductSubmodule_comm (U V : Submodule ℝ linSubmodule) :
    linProductSubmodule U V = linProductSubmodule V U := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro q ⟨x, rfl⟩
    change linProduct x.1.1 x.2.1 ∈ linProductSubmodule V U
    rw [linProduct_comm]
    exact linProduct_mem_linProductSubmodule x.2 x.1
  · refine Submodule.span_le.mpr ?_
    rintro q ⟨x, rfl⟩
    change linProduct x.1.1 x.2.1 ∈ linProductSubmodule U V
    rw [linProduct_comm]
    exact linProduct_mem_linProductSubmodule x.2 x.1

theorem linProductSubmodule_le_of_generators
    {U V : Submodule ℝ linSubmodule} {W : Submodule ℝ quadSubmodule}
    (hgen : ∀ (a : U) (b : V), linProduct a.1 b.1 ∈ W) :
    linProductSubmodule U V ≤ W := by
  refine Submodule.span_le.mpr ?_
  rintro q ⟨x, rfl⟩
  exact hgen x.1 x.2

theorem linOne_mul_linOne_mem_linProductSubmodule_top_top :
    linProduct linOne linOne ∈
      linProductSubmodule (⊤ : Submodule ℝ linSubmodule) ⊤ := by
  exact linProduct_mem_linProductSubmodule
    (⟨linOne, trivial⟩ : (⊤ : Submodule ℝ linSubmodule))
    (⟨linOne, trivial⟩ : (⊤ : Submodule ℝ linSubmodule))

theorem linVar_mul_linOne_mem_linProductSubmodule_top_top (i : Fin 3) :
    linProduct (linVar i) linOne ∈
      linProductSubmodule (⊤ : Submodule ℝ linSubmodule) ⊤ := by
  exact linProduct_mem_linProductSubmodule
    (⟨linVar i, trivial⟩ : (⊤ : Submodule ℝ linSubmodule))
    (⟨linOne, trivial⟩ : (⊤ : Submodule ℝ linSubmodule))

theorem linVar_mul_linVar_mem_linProductSubmodule_top_top (i j : Fin 3) :
    linProduct (linVar i) (linVar j) ∈
      linProductSubmodule (⊤ : Submodule ℝ linSubmodule) ⊤ := by
  exact linProduct_mem_linProductSubmodule
    (⟨linVar i, trivial⟩ : (⊤ : Submodule ℝ linSubmodule))
    (⟨linVar j, trivial⟩ : (⊤ : Submodule ℝ linSubmodule))

def linProductLeftMap (a : linSubmodule) : linSubmodule →ₗ[ℝ] quadSubmodule where
  toFun b := linProduct a b
  map_add' b c := linProduct_add_right a b c
  map_smul' r b := linProduct_smul_right r a b

@[simp] theorem linProductLeftMap_apply (a b : linSubmodule) :
    linProductLeftMap a b = linProduct a b := rfl

def linProductLeftMapOn (a : linSubmodule) (A : Submodule ℝ linSubmodule) :
    A →ₗ[ℝ] quadSubmodule :=
  (linProductLeftMap a).comp A.subtype

@[simp] theorem linProductLeftMapOn_apply
    (a : linSubmodule) (A : Submodule ℝ linSubmodule) (b : A) :
    linProductLeftMapOn a A b = linProduct a b.1 := rfl

def linProductLeftPreimage (a : linSubmodule) (P : Submodule ℝ quadSubmodule) :
    Submodule ℝ linSubmodule :=
  P.comap (linProductLeftMap a)

@[simp] theorem mem_linProductLeftPreimage
    {a : linSubmodule} {P : Submodule ℝ quadSubmodule} {b : linSubmodule} :
    b ∈ linProductLeftPreimage a P ↔ linProduct a b ∈ P :=
  Iff.rfl

def linProductLeftPreimageOn
    (a : linSubmodule) (A : Submodule ℝ linSubmodule)
    (P : Submodule ℝ quadSubmodule) : Submodule ℝ A :=
  P.comap (linProductLeftMapOn a A)

@[simp] theorem mem_linProductLeftPreimageOn
    {a : linSubmodule} {A : Submodule ℝ linSubmodule}
    {P : Submodule ℝ quadSubmodule} {b : A} :
    b ∈ linProductLeftPreimageOn a A P ↔ linProduct a b.1 ∈ P :=
  Iff.rfl

def linProductLeftPreimageWithin
    (a : linSubmodule) (A : Submodule ℝ linSubmodule)
    (P : Submodule ℝ quadSubmodule) : Submodule ℝ linSubmodule :=
  A ⊓ linProductLeftPreimage a P

@[simp] theorem mem_linProductLeftPreimageWithin
    {a : linSubmodule} {A : Submodule ℝ linSubmodule}
    {P : Submodule ℝ quadSubmodule} {b : linSubmodule} :
    b ∈ linProductLeftPreimageWithin a A P ↔ b ∈ A ∧ linProduct a b ∈ P :=
  Iff.rfl

theorem linProductLeftPreimageWithin_le_left
    (a : linSubmodule) (A : Submodule ℝ linSubmodule)
    (P : Submodule ℝ quadSubmodule) :
    linProductLeftPreimageWithin a A P ≤ A :=
  inf_le_left

theorem linProduct_mem_of_mem_linProductLeftPreimageWithin
    {a : linSubmodule} {A : Submodule ℝ linSubmodule}
    {P : Submodule ℝ quadSubmodule} {b : linSubmodule}
    (hb : b ∈ linProductLeftPreimageWithin a A P) :
    linProduct a b ∈ P :=
  hb.2

theorem linProductLeftPreimageWithin_ne_bot_of_on_ne_bot
    {a : linSubmodule} {A : Submodule ℝ linSubmodule}
    {P : Submodule ℝ quadSubmodule}
    (hM : linProductLeftPreimageOn a A P ≠ ⊥) :
    linProductLeftPreimageWithin a A P ≠ ⊥ := by
  rcases Submodule.exists_mem_ne_zero_of_ne_bot hM with ⟨b, hbM, hbne⟩
  intro hbot
  apply hbne
  apply Subtype.ext
  have hbWithin : (b.1 : linSubmodule) ∈ linProductLeftPreimageWithin a A P := by
    exact ⟨b.2, hbM⟩
  have hbzero : (b.1 : linSubmodule) = 0 := by
    simpa [hbot] using hbWithin
  exact hbzero

theorem linProductLeftMap_ker_eq_bot_of_ne_zero {a : linSubmodule}
    (ha : (a : Poly) ≠ 0) :
    LinearMap.ker (linProductLeftMap a) = ⊥ := by
  ext b
  constructor
  · intro hb
    rw [Submodule.mem_bot]
    apply Subtype.ext
    have hprod : (a : Poly) * (b : Poly) = 0 := by
      have hbzero := congrArg (fun q : quadSubmodule => (q : Poly)) hb
      simpa [linProductLeftMap, linProduct] using hbzero
    simpa using (mul_eq_zero.mp hprod).resolve_left ha
  · intro hb
    rw [hb]
    simp

theorem linProductLeftMapOn_ker_eq_bot_of_ne_zero
    {a : linSubmodule} {A : Submodule ℝ linSubmodule}
    (ha : (a : Poly) ≠ 0) :
    LinearMap.ker (linProductLeftMapOn a A) = ⊥ := by
  ext b
  constructor
  · intro hb
    rw [Submodule.mem_bot]
    apply Subtype.ext
    have hprod : (a : Poly) * (b.1 : Poly) = 0 := by
      have hbzero := congrArg (fun q : quadSubmodule => (q : Poly)) hb
      simpa [linProductLeftMapOn, linProductLeftMap, linProduct] using hbzero
    simpa using (mul_eq_zero.mp hprod).resolve_left ha
  · intro hb
    rw [hb]
    simp

def linProductLeftPreimageOnToInfRange
    (a : linSubmodule) (A : Submodule ℝ linSubmodule)
    (P : Submodule ℝ quadSubmodule) :
    linProductLeftPreimageOn a A P →ₗ[ℝ]
      ↥(P ⊓ LinearMap.range (linProductLeftMapOn a A)) :=
  ((linProductLeftMapOn a A).comp (linProductLeftPreimageOn a A P).subtype).codRestrict
    (P ⊓ LinearMap.range (linProductLeftMapOn a A))
    (fun b => ⟨b.2, ⟨b.1, rfl⟩⟩)

@[simp] theorem linProductLeftPreimageOnToInfRange_apply
    (a : linSubmodule) (A : Submodule ℝ linSubmodule)
    (P : Submodule ℝ quadSubmodule)
    (b : linProductLeftPreimageOn a A P) :
    (linProductLeftPreimageOnToInfRange a A P b : quadSubmodule) =
      linProduct a b.1.1 := rfl

theorem finrank_linProductLeftPreimageOn_eq_inf_range_of_ne_zero
    {a : linSubmodule} {A : Submodule ℝ linSubmodule}
    {P : Submodule ℝ quadSubmodule}
    (ha : (a : Poly) ≠ 0) :
    Module.finrank ℝ (linProductLeftPreimageOn a A P) =
      Module.finrank ℝ ↥(P ⊓ LinearMap.range (linProductLeftMapOn a A)) := by
  let f := linProductLeftPreimageOnToInfRange a A P
  have hinj : Function.Injective f := by
    intro b c hbc
    apply Subtype.ext
    apply Subtype.ext
    have hprod : (a : Poly) * (b.1.1 : Poly) = (a : Poly) * (c.1.1 : Poly) := by
      have hbcval := congrArg (fun q :
        ↥(P ⊓ LinearMap.range (linProductLeftMapOn a A)) => (q : quadSubmodule)) hbc
      have hbcpoly := congrArg (fun q : quadSubmodule => (q : Poly)) hbcval
      change (a : Poly) * (b.1.1 : Poly) = (a : Poly) * (c.1.1 : Poly) at hbcpoly
      exact hbcpoly
    simpa using mul_left_cancel₀ ha hprod
  have hsurj : Function.Surjective f := by
    intro y
    rcases y.2.2 with ⟨b, hb⟩
    refine ⟨⟨b, ?_⟩, ?_⟩
    · change linProduct a b.1 ∈ P
      have hyP : (y : quadSubmodule) ∈ P := y.2.1
      rwa [← hb] at hyP
    · apply Subtype.ext
      exact hb
  exact (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).finrank_eq

theorem exists_mem_linProductLeftPreimageOn_ne_zero_of_mem_inf_range_ne_zero
    {a : linSubmodule} {A : Submodule ℝ linSubmodule}
    {P : Submodule ℝ quadSubmodule} {y : quadSubmodule}
    (hyP : y ∈ P)
    (hyrange : y ∈ LinearMap.range (linProductLeftMapOn a A))
    (hyne : y ≠ 0) :
    ∃ b : A, b ∈ linProductLeftPreimageOn a A P ∧ b ≠ 0 := by
  rcases hyrange with ⟨b, hb⟩
  refine ⟨b, ?_, ?_⟩
  · change linProduct a b.1 ∈ P
    rwa [← hb] at hyP
  · intro hbzero
    apply hyne
    rw [← hb, hbzero]
    simp

theorem linProductLeftPreimageOn_ne_bot_of_inf_range_ne_bot
    {a : linSubmodule} {A : Submodule ℝ linSubmodule}
    {P : Submodule ℝ quadSubmodule}
    (hinter :
      P ⊓ LinearMap.range (linProductLeftMapOn a A) ≠ ⊥) :
    linProductLeftPreimageOn a A P ≠ ⊥ := by
  rcases Submodule.exists_mem_ne_zero_of_ne_bot hinter with ⟨y, hy, hyne⟩
  rcases exists_mem_linProductLeftPreimageOn_ne_zero_of_mem_inf_range_ne_zero
      hy.1 hy.2 hyne with ⟨b, hbM, hbne⟩
  intro hbot
  exact hbne (by simpa [hbot] using hbM)

theorem finrank_range_linProductLeftMapOn_eq
    {a : linSubmodule} {A : Submodule ℝ linSubmodule}
    (ha : (a : Poly) ≠ 0) :
    Module.finrank ℝ (LinearMap.range (linProductLeftMapOn a A)) =
      Module.finrank ℝ A := by
  refine LinearMap.finrank_range_of_inj ?_
  intro b c hbc
  apply Subtype.ext
  have hprod : (a : Poly) * (b.1 : Poly) = (a : Poly) * (c.1 : Poly) := by
    have hbcval := congrArg (fun q : quadSubmodule => (q : Poly)) hbc
    simpa [linProductLeftMapOn, linProductLeftMap, linProduct] using hbcval
  simpa using mul_left_cancel₀ ha hprod

theorem linProductLeftPreimageOn_ne_bot_of_finrank_lt_add
    {a : linSubmodule} {A : Submodule ℝ linSubmodule}
    {P W : Submodule ℝ quadSubmodule}
    (ha : (a : Poly) ≠ 0)
    (hPW : P ≤ W)
    (hrangeW : LinearMap.range (linProductLeftMapOn a A) ≤ W)
    {pdim adim wdim : ℕ}
    (hPdim : pdim ≤ Module.finrank ℝ P)
    (hAdim : adim ≤ Module.finrank ℝ A)
    (hWdim : Module.finrank ℝ W = wdim)
    (hgt : wdim < pdim + adim) :
    linProductLeftPreimageOn a A P ≠ ⊥ := by
  have hrangeDim :
      adim ≤ Module.finrank ℝ (LinearMap.range (linProductLeftMapOn a A)) := by
    rw [finrank_range_linProductLeftMapOn_eq ha]
    exact hAdim
  have hinter_exists :
      ∃ y : quadSubmodule,
        y ∈ P ∧ y ∈ LinearMap.range (linProductLeftMapOn a A) ∧ y ≠ 0 := by
    refine exists_mem_inf_ne_zero_of_finrank_eq_and_lt_add
      (K := ℝ) (V := quadSubmodule) hPW hrangeW hPdim ?_ hWdim hgt
    exact hrangeDim
  rcases hinter_exists with ⟨y, hyP, hyrange, hyne⟩
  rcases exists_mem_linProductLeftPreimageOn_ne_zero_of_mem_inf_range_ne_zero
      hyP hyrange hyne with ⟨b, hbM, hbne⟩
  intro hbot
  exact hbne (by simpa [hbot] using hbM)

theorem linProductLeftPreimageWithin_ne_bot_of_finrank_lt_add
    {a : linSubmodule} {A : Submodule ℝ linSubmodule}
    {P W : Submodule ℝ quadSubmodule}
    (ha : (a : Poly) ≠ 0)
    (hPW : P ≤ W)
    (hrangeW : LinearMap.range (linProductLeftMapOn a A) ≤ W)
    {pdim adim wdim : ℕ}
    (hPdim : pdim ≤ Module.finrank ℝ P)
    (hAdim : adim ≤ Module.finrank ℝ A)
    (hWdim : Module.finrank ℝ W = wdim)
    (hgt : wdim < pdim + adim) :
    linProductLeftPreimageWithin a A P ≠ ⊥ :=
  linProductLeftPreimageWithin_ne_bot_of_on_ne_bot
    (linProductLeftPreimageOn_ne_bot_of_finrank_lt_add
      ha hPW hrangeW hPdim hAdim hWdim hgt)

theorem range_linProductLeftMapOn_le_linProductSubmodule
    {M A : Submodule ℝ linSubmodule} (m : M) :
    LinearMap.range (linProductLeftMapOn m.1 A) ≤ linProductSubmodule M A := by
  rintro q ⟨a, rfl⟩
  exact linProduct_mem_linProductSubmodule m a

theorem finrank_right_le_finrank_linProductSubmodule_of_mem_ne_zero
    {M A : Submodule ℝ linSubmodule} (m : M)
    (hmne : ((m : linSubmodule) : Poly) ≠ 0) :
    Module.finrank ℝ A ≤ Module.finrank ℝ (linProductSubmodule M A) := by
  rw [← finrank_range_linProductLeftMapOn_eq (a := m.1) (A := A) hmne]
  exact Submodule.finrank_mono (range_linProductLeftMapOn_le_linProductSubmodule m)

theorem finrank_right_le_finrank_linProductSubmodule_of_left_ne_bot
    {M A : Submodule ℝ linSubmodule}
    (hM : M ≠ ⊥) :
    Module.finrank ℝ A ≤ Module.finrank ℝ (linProductSubmodule M A) := by
  rcases Submodule.exists_mem_ne_zero_of_ne_bot hM with ⟨m, hmM, hmne⟩
  let mM : M := ⟨m, hmM⟩
  refine finrank_right_le_finrank_linProductSubmodule_of_mem_ne_zero mM ?_
  intro hpoly
  exact hmne (Subtype.ext hpoly)

theorem finrank_left_le_finrank_linProductSubmodule_of_right_ne_bot
    {M A : Submodule ℝ linSubmodule}
    (hA : A ≠ ⊥) :
    Module.finrank ℝ M ≤ Module.finrank ℝ (linProductSubmodule M A) := by
  rw [linProductSubmodule_comm]
  exact finrank_right_le_finrank_linProductSubmodule_of_left_ne_bot hA

theorem exists_mem_inf_linProductSubmodule_ne_zero_of_finrank_lt_add
    {N W : Submodule ℝ quadSubmodule} {M A : Submodule ℝ linSubmodule}
    (hNW : N ≤ W)
    (hMAW : linProductSubmodule M A ≤ W)
    (hM : M ≠ ⊥)
    {n a c : ℕ}
    (hN : n ≤ Module.finrank ℝ N)
    (hA : a ≤ Module.finrank ℝ A)
    (hW : Module.finrank ℝ W = c)
    (hgt : c < n + a) :
    ∃ x : quadSubmodule, x ∈ N ∧ x ∈ linProductSubmodule M A ∧ x ≠ 0 := by
  have hprod :
      a ≤ Module.finrank ℝ (linProductSubmodule M A) :=
    hA.trans (finrank_right_le_finrank_linProductSubmodule_of_left_ne_bot hM)
  exact exists_mem_inf_ne_zero_of_finrank_eq_and_lt_add
    (K := ℝ) (V := quadSubmodule) hNW hMAW hN hprod hW hgt

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

theorem catalecticantMap_pair_comm
    (B : DotForm) (p : Poly) (u : RankSevenVec) (q r : quadSubmodule) :
    catalecticantMap B p u q r = catalecticantMap B p u r q := by
  simp [mul_comm]

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

theorem mem_ker_catalecticantMap_iff {B : DotForm} {p : Poly} {u : RankSevenVec}
    {q : quadSubmodule} :
    q ∈ LinearMap.ker (catalecticantMap B p u) ↔
      q.1 ∈ catalecticantKernel B p u := by
  constructor
  · intro hq
    constructor
    · exact q.2
    · intro r hr
      let rQuad : quadSubmodule := ⟨r, hr⟩
      have hmap : catalecticantMap B p u q = 0 := hq
      have hval := congrArg (fun φ : Module.Dual ℝ quadSubmodule => φ rQuad) hmap
      simpa [rQuad] using hval
  · intro hq
    change catalecticantMap B p u q = 0
    ext r
    exact hq.2 r.1 r.2

theorem catalecticantKernel_pair_comm {B : DotForm} {p : Poly} {u : RankSevenVec}
    {q r : Poly} :
    B (q * r) (residual p u) = B (r * q) (residual p u) := by
  rw [mul_comm]

theorem linProductSubmodule_le_ker_catalecticantMap_of_generators
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {U V : Submodule ℝ linSubmodule}
    (hgen : ∀ (a : U) (b : V),
      linProduct a.1 b.1 ∈ LinearMap.ker (catalecticantMap B p u)) :
    linProductSubmodule U V ≤ LinearMap.ker (catalecticantMap B p u) :=
  linProductSubmodule_le_of_generators hgen

/-- Affine-linear forms whose product with every affine-linear form lies in
the degree-two catalecticant kernel.  This is the Lean analogue of
`Ann_1(lambda)` in the blueprint. -/
def linearAnnihilator (B : DotForm) (p : Poly) (u : RankSevenVec) :
    Submodule ℝ linSubmodule where
  carrier := {a | ∀ e : linSubmodule,
    linProduct a e ∈ LinearMap.ker (catalecticantMap B p u)}
  zero_mem' := by
    intro e
    change linProduct (0 : linSubmodule) e ∈ LinearMap.ker (catalecticantMap B p u)
    simp
  add_mem' := by
    intro a b ha hb e
    rw [linProduct_add_left]
    exact Submodule.add_mem _ (ha e) (hb e)
  smul_mem' := by
    intro r a ha e
    rw [linProduct_smul_left]
    exact Submodule.smul_mem _ r (ha e)

@[simp] theorem mem_linearAnnihilator {B : DotForm} {p : Poly} {u : RankSevenVec}
    {a : linSubmodule} :
    a ∈ linearAnnihilator B p u ↔
      ∀ e : linSubmodule,
        linProduct a e ∈ LinearMap.ker (catalecticantMap B p u) :=
  Iff.rfl

theorem linProductSubmodule_linearAnnihilator_top_le_ker
    {B : DotForm} {p : Poly} {u : RankSevenVec} :
    linProductSubmodule (linearAnnihilator B p u) ⊤ ≤
      LinearMap.ker (catalecticantMap B p u) := by
  refine linProductSubmodule_le_ker_catalecticantMap_of_generators ?_
  intro a e
  exact a.2 e.1

theorem linProductSubmodule_le_ker_of_le_linearAnnihilator
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {A : Submodule ℝ linSubmodule}
    (hA : A ≤ linearAnnihilator B p u) :
    linProductSubmodule A ⊤ ≤ LinearMap.ker (catalecticantMap B p u) :=
  linProductSubmodule_mono hA le_rfl |>.trans
    linProductSubmodule_linearAnnihilator_top_le_ker

theorem linProduct_mem_catalecticantKernel_of_mem_linearAnnihilator
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {a : linSubmodule}
    (ha : a ∈ linearAnnihilator B p u)
    (e : linSubmodule) :
    (linProduct a e : quadSubmodule).1 ∈ catalecticantKernel B p u := by
  exact mem_ker_catalecticantMap_iff.mp (ha e)

theorem linProduct_mem_catalecticantKernel_of_le_linearAnnihilator
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {A : Submodule ℝ linSubmodule}
    (hA : A ≤ linearAnnihilator B p u)
    (a : A) (e : linSubmodule) :
    (linProduct a.1 e : quadSubmodule).1 ∈ catalecticantKernel B p u :=
  linProduct_mem_catalecticantKernel_of_mem_linearAnnihilator (hA a.2) e

theorem linProduct_comm_mem_catalecticantKernel_of_mem_linearAnnihilator
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {a : linSubmodule}
    (ha : a ∈ linearAnnihilator B p u)
    (e : linSubmodule) :
    (linProduct e a : quadSubmodule).1 ∈ catalecticantKernel B p u := by
  rw [linProduct_comm]
  exact linProduct_mem_catalecticantKernel_of_mem_linearAnnihilator ha e

theorem linProduct_comm_mem_catalecticantKernel_of_le_linearAnnihilator
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {A : Submodule ℝ linSubmodule}
    (hA : A ≤ linearAnnihilator B p u)
    (e : linSubmodule) (a : A) :
    (linProduct e a.1 : quadSubmodule).1 ∈ catalecticantKernel B p u :=
  linProduct_comm_mem_catalecticantKernel_of_mem_linearAnnihilator (hA a.2) e

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
