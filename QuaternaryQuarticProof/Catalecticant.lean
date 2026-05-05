import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Finsupp.Order
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.LinearAlgebra.Basis.Bilinear
import QuaternaryQuarticProof.Certificate
import QuaternaryQuarticProof.Dimension

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace QuaternaryQuartic

open scoped BigOperators Pointwise

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

private instance instFintypeLinExponentSet : Fintype LinExponentSet :=
  Fintype.ofEquiv BoundedFinTripleOne linExponentEquivBoundedFinTripleOne.symm

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

private instance instFintypeQuadExponentSet : Fintype QuadExponentSet :=
  Fintype.ofEquiv BoundedFinTriple quadExponentEquivBoundedFinTriple.symm

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

/-- The submodule of affine-chart polynomials of total degree at most three. -/
def cubicSubmodule : Submodule ℝ Poly where
  carrier := {q | q.totalDegree ≤ 3}
  zero_mem' := by
    simp
  add_mem' := by
    intro p q hp hq
    exact (MvPolynomial.totalDegree_add p q).trans (max_le hp hq)
  smul_mem' := by
    intro a q hq
    exact (MvPolynomial.totalDegree_smul_le a q).trans hq

@[simp] theorem mem_cubicSubmodule {q : Poly} :
    q ∈ cubicSubmodule ↔ q.totalDegree ≤ 3 := Iff.rfl

theorem cubicSubmodule_eq_restrictTotalDegree :
    cubicSubmodule = MvPolynomial.restrictTotalDegree (Fin 3) ℝ 3 := by
  ext q
  simp [cubicSubmodule, MvPolynomial.mem_restrictTotalDegree]

instance instModuleFiniteCubicSubmodule : Module.Finite ℝ cubicSubmodule := by
  rw [cubicSubmodule_eq_restrictTotalDegree]
  infer_instance

private abbrev CubicExponentSet :=
  {s : Fin 3 →₀ ℕ // s.sum (fun _ e => e) ≤ 3}

private abbrev BoundedFinTripleThree :=
  {f : Fin 3 → Fin 4 // (∑ i, (f i).val) ≤ 3}

private theorem finsupp_value_lt_four (s : Fin 3 →₀ ℕ)
    (hs : s.sum (fun _ e => e) ≤ 3) (i : Fin 3) :
    s i < 4 := by
  have hle_sum : s i ≤ s.sum (fun _ e => e) := by
    simpa using
      (Finsupp.single_eval_le_sum (f := s) (g := fun n : ℕ => n)
        (by simp) (fun n => Nat.zero_le n) i)
  omega

private theorem equivFunOnFinite_symm_sum_finTripleThree (f : Fin 3 → Fin 4) :
    (Finsupp.equivFunOnFinite.symm (fun i => (f i).val)).sum (fun _ e => e) =
      ∑ i, (f i).val := by
  simpa using
    (Finsupp.equivFunOnFinite_symm_sum (f := fun i : Fin 3 => (f i).val))

private def cubicExponentEquivBoundedFinTripleThree :
    CubicExponentSet ≃ BoundedFinTripleThree where
  toFun s := ⟨fun i => ⟨s.1 i, finsupp_value_lt_four s.1 s.2 i⟩, by
    simpa [finsupp_sum_eq_finset_sum s.1] using s.2⟩
  invFun f := ⟨Finsupp.equivFunOnFinite.symm (fun i => (f.1 i).val), by
    simpa [equivFunOnFinite_symm_sum_finTripleThree f.1] using f.2⟩
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

private instance instFintypeCubicExponentSet : Fintype CubicExponentSet :=
  Fintype.ofEquiv BoundedFinTripleThree cubicExponentEquivBoundedFinTripleThree.symm

private theorem natCard_cubicExponentSet :
    Nat.card CubicExponentSet = 20 := by
  rw [Nat.card_congr cubicExponentEquivBoundedFinTripleThree]
  rw [Nat.card_eq_fintype_card]
  decide

theorem finrank_cubicSubmodule_eq_twenty :
    Module.finrank ℝ cubicSubmodule = 20 := by
  rw [cubicSubmodule_eq_restrictTotalDegree]
  change Module.finrank ℝ
    (MvPolynomial.restrictSupport ℝ {n : Fin 3 →₀ ℕ | n.sum (fun _ e => e) ≤ 3}) = 20
  rw [Module.finrank_eq_nat_card_basis
    (MvPolynomial.basisRestrictSupport ℝ
      {n : Fin 3 →₀ ℕ | n.sum (fun _ e => e) ≤ 3})]
  exact natCard_cubicExponentSet

/-- The submodule of affine-chart polynomials of total degree at most four. -/
def quarticSubmodule : Submodule ℝ Poly where
  carrier := {q | IsQuartic q}
  zero_mem' := by
    simp [IsQuartic]
  add_mem' := by
    intro p q hp hq
    exact (MvPolynomial.totalDegree_add p q).trans (max_le hp hq)
  smul_mem' := by
    intro a q hq
    exact (MvPolynomial.totalDegree_smul_le a q).trans hq

@[simp] theorem mem_quarticSubmodule {q : Poly} :
    q ∈ quarticSubmodule ↔ IsQuartic q := Iff.rfl

theorem quarticSubmodule_eq_restrictTotalDegree :
    quarticSubmodule = MvPolynomial.restrictTotalDegree (Fin 3) ℝ 4 := by
  ext q
  simp [quarticSubmodule, IsQuartic, MvPolynomial.mem_restrictTotalDegree]

instance instModuleFiniteQuarticSubmodule : Module.Finite ℝ quarticSubmodule := by
  rw [quarticSubmodule_eq_restrictTotalDegree]
  infer_instance

private abbrev QuarticExponentSet :=
  {s : Fin 3 →₀ ℕ // s.sum (fun _ e => e) ≤ 4}

private abbrev BoundedFinTripleFour :=
  {f : Fin 3 → Fin 5 // (∑ i, (f i).val) ≤ 4}

private theorem finsupp_value_lt_five (s : Fin 3 →₀ ℕ)
    (hs : s.sum (fun _ e => e) ≤ 4) (i : Fin 3) :
    s i < 5 := by
  have hle_sum : s i ≤ s.sum (fun _ e => e) := by
    simpa using
      (Finsupp.single_eval_le_sum (f := s) (g := fun n : ℕ => n)
        (by simp) (fun n => Nat.zero_le n) i)
  omega

private theorem equivFunOnFinite_symm_sum_finTripleFour (f : Fin 3 → Fin 5) :
    (Finsupp.equivFunOnFinite.symm (fun i => (f i).val)).sum (fun _ e => e) =
      ∑ i, (f i).val := by
  simpa using
    (Finsupp.equivFunOnFinite_symm_sum (f := fun i : Fin 3 => (f i).val))

private def quarticExponentEquivBoundedFinTripleFour :
    QuarticExponentSet ≃ BoundedFinTripleFour where
  toFun s := ⟨fun i => ⟨s.1 i, finsupp_value_lt_five s.1 s.2 i⟩, by
    simpa [finsupp_sum_eq_finset_sum s.1] using s.2⟩
  invFun f := ⟨Finsupp.equivFunOnFinite.symm (fun i => (f.1 i).val), by
    simpa [equivFunOnFinite_symm_sum_finTripleFour f.1] using f.2⟩
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

private instance instFintypeQuarticExponentSet : Fintype QuarticExponentSet :=
  Fintype.ofEquiv BoundedFinTripleFour quarticExponentEquivBoundedFinTripleFour.symm

private theorem natCard_quarticExponentSet :
    Nat.card QuarticExponentSet = 35 := by
  rw [Nat.card_congr quarticExponentEquivBoundedFinTripleFour]
  rw [Nat.card_eq_fintype_card]
  decide

theorem finrank_quarticSubmodule_eq_thirtyFive :
    Module.finrank ℝ quarticSubmodule = 35 := by
  rw [quarticSubmodule_eq_restrictTotalDegree]
  change Module.finrank ℝ
    (MvPolynomial.restrictSupport ℝ {n : Fin 3 →₀ ℕ | n.sum (fun _ e => e) ≤ 4}) = 35
  rw [Module.finrank_eq_nat_card_basis
    (MvPolynomial.basisRestrictSupport ℝ
      {n : Fin 3 →₀ ℕ | n.sum (fun _ e => e) ≤ 4})]
  exact natCard_quarticExponentSet

theorem mul_quad_quad_mem_quartic {p q : Poly}
    (hp : p ∈ quadSubmodule) (hq : q ∈ quadSubmodule) :
    p * q ∈ quarticSubmodule := by
  have hmul : (p * q).totalDegree ≤ p.totalDegree + q.totalDegree :=
    MvPolynomial.totalDegree_mul p q
  have hp2 : p.totalDegree ≤ 2 := hp
  have hq2 : q.totalDegree ≤ 2 := hq
  change (p * q).totalDegree ≤ 4
  omega

theorem sq_quad_mem_quartic {q : Poly}
    (hq : q ∈ quadSubmodule) :
    q^2 ∈ quarticSubmodule := by
  simpa [pow_two] using mul_quad_quad_mem_quartic hq hq

theorem mul_lin_lin_mem_quad {p q : Poly}
    (hp : p ∈ linSubmodule) (hq : q ∈ linSubmodule) :
    p * q ∈ quadSubmodule := by
  have hmul : (p * q).totalDegree ≤ p.totalDegree + q.totalDegree :=
    MvPolynomial.totalDegree_mul p q
  have hp1 : p.totalDegree ≤ 1 := hp
  have hq1 : q.totalDegree ≤ 1 := hq
  change (p * q).totalDegree ≤ 2
  omega

theorem mul_lin_quad_mem_cubic {p q : Poly}
    (hp : p ∈ linSubmodule) (hq : q ∈ quadSubmodule) :
    p * q ∈ cubicSubmodule := by
  have hmul : (p * q).totalDegree ≤ p.totalDegree + q.totalDegree :=
    MvPolynomial.totalDegree_mul p q
  have hp1 : p.totalDegree ≤ 1 := hp
  have hq2 : q.totalDegree ≤ 2 := hq
  change (p * q).totalDegree ≤ 3
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

theorem linProduct_self_ne_zero {a : linSubmodule}
    (ha : (a : Poly) ≠ 0) :
    (linProduct a a : quadSubmodule).1 ≠ 0 := by
  simpa [linProduct] using mul_ne_zero ha ha

def linQuadProduct (a : linSubmodule) (q : quadSubmodule) : cubicSubmodule :=
  ⟨a.1 * q.1, mul_lin_quad_mem_cubic a.2 q.2⟩

@[simp] theorem linQuadProduct_val (a : linSubmodule) (q : quadSubmodule) :
    (linQuadProduct a q : Poly) = a.1 * q.1 := rfl

@[simp] theorem linQuadProduct_add_left
    (a b : linSubmodule) (q : quadSubmodule) :
    linQuadProduct (a + b) q = linQuadProduct a q + linQuadProduct b q := by
  ext
  simp [linQuadProduct, add_mul]

@[simp] theorem linQuadProduct_add_right
    (a : linSubmodule) (q r : quadSubmodule) :
    linQuadProduct a (q + r) = linQuadProduct a q + linQuadProduct a r := by
  ext
  simp [linQuadProduct, mul_add]

@[simp] theorem linQuadProduct_smul_left
    (c : ℝ) (a : linSubmodule) (q : quadSubmodule) :
    linQuadProduct (c • a) q = c • linQuadProduct a q := by
  ext
  simp [linQuadProduct]

@[simp] theorem linQuadProduct_smul_right
    (c : ℝ) (a : linSubmodule) (q : quadSubmodule) :
    linQuadProduct a (c • q) = c • linQuadProduct a q := by
  ext
  simp [linQuadProduct]

def linQuadProductBilin :
    linSubmodule →ₗ[ℝ] quadSubmodule →ₗ[ℝ] cubicSubmodule where
  toFun a :=
    { toFun := fun q => linQuadProduct a q
      map_add' := by
        intro q r
        exact linQuadProduct_add_right a q r
      map_smul' := by
        intro c q
        exact linQuadProduct_smul_right c a q }
  map_add' := by
    intro a b
    apply LinearMap.ext
    intro q
    exact linQuadProduct_add_left a b q
  map_smul' := by
    intro c a
    apply LinearMap.ext
    intro q
    exact linQuadProduct_smul_left c a q

@[simp] theorem linQuadProductBilin_apply
    (a : linSubmodule) (q : quadSubmodule) :
    (linQuadProductBilin a) q = linQuadProduct a q := rfl

def linProductBilin :
    linSubmodule →ₗ[ℝ] linSubmodule →ₗ[ℝ] quadSubmodule where
  toFun a :=
    { toFun := fun b => linProduct a b
      map_add' := by
        intro b c
        exact linProduct_add_right a b c
      map_smul' := by
        intro r b
        exact linProduct_smul_right r a b }
  map_add' := by
    intro a b
    apply LinearMap.ext
    intro c
    exact linProduct_add_left a b c
  map_smul' := by
    intro r a
    apply LinearMap.ext
    intro b
    exact linProduct_smul_left r a b

@[simp] theorem linProductBilin_apply (a b : linSubmodule) :
    (linProductBilin a) b = linProduct a b := rfl

def linProductSubmodule (U V : Submodule ℝ linSubmodule) :
    Submodule ℝ quadSubmodule :=
  Submodule.span ℝ (Set.range fun x : U × V => linProduct x.1.1 x.2.1)

def linQuadProductSubmodule
    (U : Submodule ℝ linSubmodule) (P : Submodule ℝ quadSubmodule) :
    Submodule ℝ cubicSubmodule :=
  Submodule.span ℝ (Set.range fun x : U × P => linQuadProduct x.1.1 x.2.1)

def symSquareSubmodule (U : Submodule ℝ linSubmodule) :
    Submodule ℝ quadSubmodule :=
  linProductSubmodule U U

def linProductBilinOn (U : Submodule ℝ linSubmodule) :
    U →ₗ[ℝ] U →ₗ[ℝ] quadSubmodule where
  toFun a :=
    { toFun := fun b => linProduct a.1 b.1
      map_add' := by
        intro b c
        exact linProduct_add_right a.1 b.1 c.1
      map_smul' := by
        intro r b
        exact linProduct_smul_right r a.1 b.1 }
  map_add' := by
    intro a b
    apply LinearMap.ext
    intro c
    exact linProduct_add_left a.1 b.1 c.1
  map_smul' := by
    intro r a
    apply LinearMap.ext
    intro b
    exact linProduct_smul_left r a.1 b.1

theorem linProduct_mem_linProductSubmodule
    {U V : Submodule ℝ linSubmodule} (a : U) (b : V) :
    linProduct a.1 b.1 ∈ linProductSubmodule U V := by
  exact Submodule.subset_span ⟨(a, b), rfl⟩

theorem linQuadProduct_mem_linQuadProductSubmodule
    {U : Submodule ℝ linSubmodule} {P : Submodule ℝ quadSubmodule}
    (a : U) (q : P) :
    linQuadProduct a.1 q.1 ∈ linQuadProductSubmodule U P := by
  exact Submodule.subset_span ⟨(a, q), rfl⟩

theorem linProductSubmodule_mono
    {U₁ U₂ V₁ V₂ : Submodule ℝ linSubmodule}
    (hU : U₁ ≤ U₂) (hV : V₁ ≤ V₂) :
    linProductSubmodule U₁ V₁ ≤ linProductSubmodule U₂ V₂ := by
  refine Submodule.span_le.mpr ?_
  rintro q ⟨x, rfl⟩
  exact linProduct_mem_linProductSubmodule
    (⟨x.1.1, hU x.1.2⟩ : U₂) (⟨x.2.1, hV x.2.2⟩ : V₂)

theorem linQuadProductSubmodule_mono
    {U₁ U₂ : Submodule ℝ linSubmodule} {P₁ P₂ : Submodule ℝ quadSubmodule}
    (hU : U₁ ≤ U₂) (hP : P₁ ≤ P₂) :
    linQuadProductSubmodule U₁ P₁ ≤ linQuadProductSubmodule U₂ P₂ := by
  refine Submodule.span_le.mpr ?_
  rintro q ⟨x, rfl⟩
  exact linQuadProduct_mem_linQuadProductSubmodule
    (⟨x.1.1, hU x.1.2⟩ : U₂) (⟨x.2.1, hP x.2.2⟩ : P₂)

theorem linQuadProductSubmodule_le_of_generators
    {U : Submodule ℝ linSubmodule} {P : Submodule ℝ quadSubmodule}
    {C : Submodule ℝ cubicSubmodule}
    (hgen : ∀ (a : U) (q : P), linQuadProduct a.1 q.1 ∈ C) :
    linQuadProductSubmodule U P ≤ C := by
  refine Submodule.span_le.mpr ?_
  rintro q ⟨x, rfl⟩
  exact hgen x.1 x.2

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

theorem linProductSubmodule_le_span_square_of_span_eq
    {W : Submodule ℝ linSubmodule} {x : linSubmodule}
    (hxspan : ℝ ∙ x = W) :
    linProductSubmodule W W ≤ ℝ ∙ linProduct x x := by
  refine linProductSubmodule_le_of_generators ?_
  intro a b
  have ha : (a.1 : linSubmodule) ∈ ℝ ∙ x := by
    rw [hxspan]
    exact a.2
  have hb : (b.1 : linSubmodule) ∈ ℝ ∙ x := by
    rw [hxspan]
    exact b.2
  rcases Submodule.mem_span_singleton.mp ha with ⟨r, hr⟩
  rcases Submodule.mem_span_singleton.mp hb with ⟨s, hs⟩
  rw [← hr, ← hs]
  rw [linProduct_smul_left, linProduct_smul_right, smul_smul]
  exact Submodule.smul_mem _ (r * s) (Submodule.subset_span rfl)

theorem linProductSubmodule_le_span_pair_products_of_span_eq
    {W : Submodule ℝ linSubmodule} {x y : linSubmodule}
    (hspan : Submodule.span ℝ ({x, y} : Set linSubmodule) = W) :
    linProductSubmodule W W ≤
      Submodule.span ℝ
        ({linProduct x x, linProduct x y, linProduct y y} :
          Set quadSubmodule) := by
  refine linProductSubmodule_le_of_generators ?_
  intro a b
  have ha : (a.1 : linSubmodule) ∈
      Submodule.span ℝ ({x, y} : Set linSubmodule) := by
    rw [hspan]
    exact a.2
  have hb : (b.1 : linSubmodule) ∈
      Submodule.span ℝ ({x, y} : Set linSubmodule) := by
    rw [hspan]
    exact b.2
  rcases Submodule.mem_span_pair.mp ha with ⟨r, s, haeq⟩
  rcases Submodule.mem_span_pair.mp hb with ⟨u, v, hbeq⟩
  rw [Submodule.mem_span_triple]
  refine ⟨r * u, r * v + s * u, s * v, ?_⟩
  rw [← haeq, ← hbeq]
  simp [linProduct_add_right, smul_add, add_smul, smul_smul, linProduct_comm,
    mul_comm]
  abel_nf

theorem exists_quadraticCombination_of_mem_linProductSubmodule_span_pair
    {W : Submodule ℝ linSubmodule} {x y : linSubmodule} {q : quadSubmodule}
    (hspan : Submodule.span ℝ ({x, y} : Set linSubmodule) = W)
    (hq : q ∈ linProductSubmodule W W) :
    ∃ r s t : ℝ,
      q = r • linProduct x x + s • linProduct x y + t • linProduct y y := by
  have hmem :
      q ∈
        Submodule.span ℝ
          ({linProduct x x, linProduct x y, linProduct y y} :
            Set quadSubmodule) :=
    (linProductSubmodule_le_span_pair_products_of_span_eq hspan) hq
  rcases Submodule.mem_span_triple.mp hmem with ⟨r, s, t, hqeq⟩
  exact ⟨r, s, t, hqeq.symm⟩

theorem finrank_symSquareSubmodule_le_three_of_finrank_eq_two
    {A : Submodule ℝ linSubmodule}
    (hA : Module.finrank ℝ A = 2) :
    Module.finrank ℝ (symSquareSubmodule A) ≤ 3 := by
  classical
  letI : Module.Free ℝ A := Module.Free.of_divisionRing ℝ A
  let β := Module.finBasisOfFinrankEq ℝ A hA
  let ι := {ij : Fin 2 × Fin 2 // ij.1 ≤ ij.2}
  let S : Set quadSubmodule :=
    Set.range fun ij : ι => linProduct (β ij.1.1).1 (β ij.1.2).1
  have hle : symSquareSubmodule A ≤ Submodule.span ℝ S := by
    refine linProductSubmodule_le_of_generators ?_
    intro a b
    have hrepr :=
      LinearMap.sum_repr_mul_repr_mul
        (b₁' := β) (b₂' := β) (B := linProductBilinOn A) a b
    change ((linProductBilinOn A) a) b ∈ Submodule.span ℝ S
    rw [← hrepr]
    rw [Finsupp.sum_fintype]
    swap
    · simp
    refine Submodule.sum_mem _ ?_
    intro i _hi
    rw [Finsupp.sum_fintype]
    swap
    · simp
    refine Submodule.sum_mem _ ?_
    intro j _hj
    refine Submodule.smul_mem (Submodule.span ℝ S) _ ?_
    refine Submodule.smul_mem (Submodule.span ℝ S) _ ?_
    change linProduct (β i).1 (β j).1 ∈ Submodule.span ℝ S
    by_cases hij : i ≤ j
    · exact Submodule.subset_span ⟨⟨(i, j), hij⟩, rfl⟩
    · have hji : j ≤ i := le_of_not_ge hij
      rw [linProduct_comm]
      exact Submodule.subset_span ⟨⟨(j, i), hji⟩, rfl⟩
  have hspan :
      Module.finrank ℝ (Submodule.span ℝ S) ≤ Fintype.card ι := by
    simpa [S] using
      (finrank_range_le_card (R := ℝ)
        (b := fun ij : ι => linProduct (β ij.1.1).1 (β ij.1.2).1))
  have hcard : Fintype.card ι = 3 := by
    decide
  exact (Submodule.finrank_mono hle).trans (by simpa [hcard] using hspan)

theorem finrank_symSquareSubmodule_eq_three_of_basis_products_linearIndependent
    {A : Submodule ℝ linSubmodule}
    (β : Module.Basis (Fin 2) ℝ A)
    (hLI :
      LinearIndependent ℝ
        (fun ij : {ij : Fin 2 × Fin 2 // ij.1 ≤ ij.2} =>
          linProduct (β ij.1.1).1 (β ij.1.2).1)) :
    Module.finrank ℝ (symSquareSubmodule A) = 3 := by
  let ι := {ij : Fin 2 × Fin 2 // ij.1 ≤ ij.2}
  let f : ι → quadSubmodule :=
    fun ij => linProduct (β ij.1.1).1 (β ij.1.2).1
  have hspan_le : Submodule.span ℝ (Set.range f) ≤ symSquareSubmodule A := by
    refine Submodule.span_le.mpr ?_
    rintro q ⟨ij, rfl⟩
    exact linProduct_mem_linProductSubmodule
      (⟨(β ij.1.1).1, (β ij.1.1).2⟩ : A)
      (⟨(β ij.1.2).1, (β ij.1.2).2⟩ : A)
  have hspan_finrank :
      Module.finrank ℝ (Submodule.span ℝ
        (Set.range fun ij : {ij : Fin 2 × Fin 2 // ij.1 ≤ ij.2} =>
          linProduct (β ij.1.1).1 (β ij.1.2).1)) = 3 := by
    have hcard :
        Fintype.card {ij : Fin 2 × Fin 2 // ij.1 ≤ ij.2} =
          Module.finrank ℝ (Submodule.span ℝ
            (Set.range fun ij : {ij : Fin 2 × Fin 2 // ij.1 ≤ ij.2} =>
              linProduct (β ij.1.1).1 (β ij.1.2).1)) := by
      exact
        (linearIndependent_iff_card_eq_finrank_span (R := ℝ)
          (b := fun ij : {ij : Fin 2 × Fin 2 // ij.1 ≤ ij.2} =>
            linProduct (β ij.1.1).1 (β ij.1.2).1)).mp hLI
    have hιcard : Fintype.card ι = 3 := by
      decide
    simpa [ι, hιcard] using hcard.symm
  have hlower : 3 ≤ Module.finrank ℝ (symSquareSubmodule A) := by
    have hmono := Submodule.finrank_mono hspan_le
    rw [show Submodule.span ℝ (Set.range f) =
        Submodule.span ℝ
          (Set.range fun ij : {ij : Fin 2 × Fin 2 // ij.1 ≤ ij.2} =>
            linProduct (β ij.1.1).1 (β ij.1.2).1) by rfl] at hmono
    omega
  have hA : Module.finrank ℝ A = 2 := by
    rw [Module.finrank_eq_card_basis β]
    rfl
  have hupper :
      Module.finrank ℝ (symSquareSubmodule A) ≤ 3 :=
    finrank_symSquareSubmodule_le_three_of_finrank_eq_two hA
  omega

theorem finrank_symSquareSubmodule_le_six_of_finrank_eq_three
    {A : Submodule ℝ linSubmodule}
    (hA : Module.finrank ℝ A = 3) :
    Module.finrank ℝ (symSquareSubmodule A) ≤ 6 := by
  classical
  letI : Module.Free ℝ A := Module.Free.of_divisionRing ℝ A
  let β := Module.finBasisOfFinrankEq ℝ A hA
  let ι := {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2}
  let S : Set quadSubmodule :=
    Set.range fun ij : ι => linProduct (β ij.1.1).1 (β ij.1.2).1
  have hle : symSquareSubmodule A ≤ Submodule.span ℝ S := by
    refine linProductSubmodule_le_of_generators ?_
    intro a b
    have hrepr :=
      LinearMap.sum_repr_mul_repr_mul
        (b₁' := β) (b₂' := β) (B := linProductBilinOn A) a b
    change ((linProductBilinOn A) a) b ∈ Submodule.span ℝ S
    rw [← hrepr]
    rw [Finsupp.sum_fintype]
    swap
    · simp
    refine Submodule.sum_mem _ ?_
    intro i _hi
    rw [Finsupp.sum_fintype]
    swap
    · simp
    refine Submodule.sum_mem _ ?_
    intro j _hj
    refine Submodule.smul_mem (Submodule.span ℝ S) _ ?_
    refine Submodule.smul_mem (Submodule.span ℝ S) _ ?_
    change linProduct (β i).1 (β j).1 ∈ Submodule.span ℝ S
    by_cases hij : i ≤ j
    · exact Submodule.subset_span ⟨⟨(i, j), hij⟩, rfl⟩
    · have hji : j ≤ i := le_of_not_ge hij
      rw [linProduct_comm]
      exact Submodule.subset_span ⟨⟨(j, i), hji⟩, rfl⟩
  have hspan :
      Module.finrank ℝ (Submodule.span ℝ S) ≤ Fintype.card ι := by
    simpa [S] using
      (finrank_range_le_card (R := ℝ)
        (b := fun ij : ι => linProduct (β ij.1.1).1 (β ij.1.2).1))
  have hcard : Fintype.card ι = 6 := by
    decide
  exact (Submodule.finrank_mono hle).trans (by simpa [hcard] using hspan)

theorem finrank_symSquareSubmodule_eq_six_of_basis_products_linearIndependent
    {A : Submodule ℝ linSubmodule}
    (β : Module.Basis (Fin 3) ℝ A)
    (hLI :
      LinearIndependent ℝ
        (fun ij : {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} =>
          linProduct (β ij.1.1).1 (β ij.1.2).1)) :
    Module.finrank ℝ (symSquareSubmodule A) = 6 := by
  let ι := {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2}
  let f : ι → quadSubmodule :=
    fun ij => linProduct (β ij.1.1).1 (β ij.1.2).1
  have hspan_le : Submodule.span ℝ (Set.range f) ≤ symSquareSubmodule A := by
    refine Submodule.span_le.mpr ?_
    rintro q ⟨ij, rfl⟩
    exact linProduct_mem_linProductSubmodule
      (⟨(β ij.1.1).1, (β ij.1.1).2⟩ : A)
      (⟨(β ij.1.2).1, (β ij.1.2).2⟩ : A)
  have hspan_finrank :
      Module.finrank ℝ (Submodule.span ℝ
        (Set.range fun ij : {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} =>
          linProduct (β ij.1.1).1 (β ij.1.2).1)) = 6 := by
    have hcard :
        Fintype.card {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} =
          Module.finrank ℝ (Submodule.span ℝ
            (Set.range fun ij : {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} =>
              linProduct (β ij.1.1).1 (β ij.1.2).1)) := by
      exact
        (linearIndependent_iff_card_eq_finrank_span (R := ℝ)
          (b := fun ij : {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} =>
            linProduct (β ij.1.1).1 (β ij.1.2).1)).mp hLI
    have hιcard : Fintype.card ι = 6 := by
      decide
    simpa [ι, hιcard] using hcard.symm
  have hlower : 6 ≤ Module.finrank ℝ (symSquareSubmodule A) := by
    have hmono := Submodule.finrank_mono hspan_le
    rw [show Submodule.span ℝ (Set.range f) =
        Submodule.span ℝ
          (Set.range fun ij : {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} =>
            linProduct (β ij.1.1).1 (β ij.1.2).1) by rfl] at hmono
    omega
  have hA : Module.finrank ℝ A = 3 := by
    rw [Module.finrank_eq_card_basis β]
    rfl
  have hupper :
      Module.finrank ℝ (symSquareSubmodule A) ≤ 6 :=
    finrank_symSquareSubmodule_le_six_of_finrank_eq_three hA
  omega

theorem span_basis_pair_products_eq_symSquareSubmodule
    {A : Submodule ℝ linSubmodule}
    (β : Module.Basis (Fin 3) ℝ A) :
    Submodule.span ℝ
        (Set.range fun ij : {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} =>
          linProduct (β ij.1.1).1 (β ij.1.2).1) =
      symSquareSubmodule A := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro q ⟨ij, rfl⟩
    exact linProduct_mem_linProductSubmodule
      (⟨(β ij.1.1).1, (β ij.1.1).2⟩ : A)
      (⟨(β ij.1.2).1, (β ij.1.2).2⟩ : A)
  · refine linProductSubmodule_le_of_generators ?_
    intro a b
    have hrepr :=
      LinearMap.sum_repr_mul_repr_mul
        (b₁' := β) (b₂' := β) (B := linProductBilinOn A) a b
    change ((linProductBilinOn A) a) b ∈
      Submodule.span ℝ
        (Set.range fun ij : {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} =>
          linProduct (β ij.1.1).1 (β ij.1.2).1)
    rw [← hrepr]
    rw [Finsupp.sum_fintype]
    swap
    · simp
    refine Submodule.sum_mem _ ?_
    intro i _hi
    rw [Finsupp.sum_fintype]
    swap
    · simp
    refine Submodule.sum_mem _ ?_
    intro j _hj
    refine Submodule.smul_mem _ _ ?_
    refine Submodule.smul_mem _ _ ?_
    change linProduct (β i).1 (β j).1 ∈
      Submodule.span ℝ
        (Set.range fun ij : {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} =>
          linProduct (β ij.1.1).1 (β ij.1.2).1)
    by_cases hij : i ≤ j
    · exact Submodule.subset_span ⟨⟨(i, j), hij⟩, rfl⟩
    · have hji : j ≤ i := le_of_not_ge hij
      rw [linProduct_comm]
      exact Submodule.subset_span ⟨⟨(j, i), hji⟩, rfl⟩

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

theorem linSubmodule_mul_linSubmodule_le_quadSubmodule :
    linSubmodule * linSubmodule ≤ quadSubmodule := by
  rw [Submodule.mul_le]
  intro p hp q hq
  exact mul_lin_lin_mem_quad hp hq

theorem map_subtype_linProductSubmodule_top_top :
    (linProductSubmodule (⊤ : Submodule ℝ linSubmodule) ⊤).map
        quadSubmodule.subtype =
      linSubmodule * linSubmodule := by
  apply le_antisymm
  · rw [linProductSubmodule, Submodule.map_span]
    refine Submodule.span_le.mpr ?_
    rintro q ⟨x, hx, rfl⟩
    rcases hx with ⟨ab, rfl⟩
    exact Submodule.mul_mem_mul ab.1.1.2 ab.2.1.2
  · rw [Submodule.mul_le]
    intro p hp q hq
    let a : linSubmodule := ⟨p, hp⟩
    let b : linSubmodule := ⟨q, hq⟩
    refine ⟨linProduct a b, ?_, rfl⟩
    exact linProduct_mem_linProductSubmodule
      (⟨a, trivial⟩ : (⊤ : Submodule ℝ linSubmodule))
      (⟨b, trivial⟩ : (⊤ : Submodule ℝ linSubmodule))

theorem finsupp_degree_eq_total (s : Fin 3 →₀ ℕ) :
    Finsupp.degree s = s.sum (fun _ e => e) := by
  rw [Finsupp.degree_eq_sum]
  rw [Finsupp.sum_fintype]
  intro i
  simp

theorem bounded_totalDegree_two_eq_add_bounded_totalDegree_one :
    ({s : Fin 3 →₀ ℕ | s.sum (fun _ e => e) ≤ 2} : Set (Fin 3 →₀ ℕ)) =
      {s : Fin 3 →₀ ℕ | s.sum (fun _ e => e) ≤ 1} +
        {s : Fin 3 →₀ ℕ | s.sum (fun _ e => e) ≤ 1} := by
  let S1 : Set (Fin 3 →₀ ℕ) := {s | s.sum (fun _ e => e) ≤ 1}
  let S2 : Set (Fin 3 →₀ ℕ) := {s | s.sum (fun _ e => e) ≤ 2}
  let D1 : Set (Fin 3 →₀ ℕ) := Finsupp.degree ⁻¹' Set.Iic 1
  let D2 : Set (Fin 3 →₀ ℕ) := Finsupp.degree ⁻¹' Set.Iic 2
  have hS1D1 : S1 = D1 := by
    ext s
    simp [S1, D1, Set.mem_Iic, finsupp_degree_eq_total]
  have hS2D2 : S2 = D2 := by
    ext s
    simp [S2, D2, Set.mem_Iic, finsupp_degree_eq_total]
  have hIic : (Set.Iic 1 + Set.Iic 1 : Set ℕ) = Set.Iic 2 := by
    ext n
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      simp only [Set.mem_Iic] at ha hb ⊢
      omega
    · intro hn
      simp only [Set.mem_Iic] at hn
      interval_cases n
      · exact ⟨0, by norm_num, 0, by norm_num, by norm_num⟩
      · exact ⟨1, by norm_num, 0, by norm_num, by norm_num⟩
      · exact ⟨1, by norm_num, 1, by norm_num, by norm_num⟩
  change S2 = S1 + S1
  calc
    S2 = D2 := hS2D2
    _ = Finsupp.degree ⁻¹' (Set.Iic 1 + Set.Iic 1 : Set ℕ) := by
      rw [hIic]
    _ = D1 + D1 :=
      Finsupp.degree_preimage_add (σ := Fin 3) (Set.Iic 1) (Set.Iic 1)
    _ = S1 + S1 := by
      rw [hS1D1]

theorem bounded_totalDegree_three_eq_add_bounded_totalDegree_one_two :
    ({s : Fin 3 →₀ ℕ | s.sum (fun _ e => e) ≤ 3} : Set (Fin 3 →₀ ℕ)) =
      {s : Fin 3 →₀ ℕ | s.sum (fun _ e => e) ≤ 1} +
        {s : Fin 3 →₀ ℕ | s.sum (fun _ e => e) ≤ 2} := by
  let S1 : Set (Fin 3 →₀ ℕ) := {s | s.sum (fun _ e => e) ≤ 1}
  let S2 : Set (Fin 3 →₀ ℕ) := {s | s.sum (fun _ e => e) ≤ 2}
  let S3 : Set (Fin 3 →₀ ℕ) := {s | s.sum (fun _ e => e) ≤ 3}
  let D1 : Set (Fin 3 →₀ ℕ) := Finsupp.degree ⁻¹' Set.Iic 1
  let D2 : Set (Fin 3 →₀ ℕ) := Finsupp.degree ⁻¹' Set.Iic 2
  let D3 : Set (Fin 3 →₀ ℕ) := Finsupp.degree ⁻¹' Set.Iic 3
  have hS1D1 : S1 = D1 := by
    ext s
    simp [S1, D1, Set.mem_Iic, finsupp_degree_eq_total]
  have hS2D2 : S2 = D2 := by
    ext s
    simp [S2, D2, Set.mem_Iic, finsupp_degree_eq_total]
  have hS3D3 : S3 = D3 := by
    ext s
    simp [S3, D3, Set.mem_Iic, finsupp_degree_eq_total]
  have hIic : (Set.Iic 1 + Set.Iic 2 : Set ℕ) = Set.Iic 3 := by
    ext n
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      simp only [Set.mem_Iic] at ha hb ⊢
      omega
    · intro hn
      simp only [Set.mem_Iic] at hn
      interval_cases n
      · exact ⟨0, by norm_num, 0, by norm_num, by norm_num⟩
      · exact ⟨1, by norm_num, 0, by norm_num, by norm_num⟩
      · exact ⟨1, by norm_num, 1, by norm_num, by norm_num⟩
      · exact ⟨1, by norm_num, 2, by norm_num, by norm_num⟩
  change S3 = S1 + S2
  calc
    S3 = D3 := hS3D3
    _ = Finsupp.degree ⁻¹' (Set.Iic 1 + Set.Iic 2 : Set ℕ) := by
      rw [hIic]
    _ = D1 + D2 :=
      Finsupp.degree_preimage_add (σ := Fin 3) (Set.Iic 1) (Set.Iic 2)
    _ = S1 + S2 := by
      rw [hS1D1, hS2D2]

theorem linSubmodule_mul_linSubmodule_eq_quadSubmodule :
    linSubmodule * linSubmodule = quadSubmodule := by
  rw [linSubmodule_eq_restrictTotalDegree, quadSubmodule_eq_restrictTotalDegree]
  change
    MvPolynomial.restrictSupport ℝ
        ({s : Fin 3 →₀ ℕ | s.sum (fun _ e => e) ≤ 1} : Set (Fin 3 →₀ ℕ)) *
      MvPolynomial.restrictSupport ℝ
        ({s : Fin 3 →₀ ℕ | s.sum (fun _ e => e) ≤ 1} : Set (Fin 3 →₀ ℕ)) =
      MvPolynomial.restrictSupport ℝ
        ({s : Fin 3 →₀ ℕ | s.sum (fun _ e => e) ≤ 2} : Set (Fin 3 →₀ ℕ))
  rw [← MvPolynomial.restrictSupport_add]
  rw [← bounded_totalDegree_two_eq_add_bounded_totalDegree_one]

theorem linSubmodule_mul_quadSubmodule_le_cubicSubmodule :
    linSubmodule * quadSubmodule ≤ cubicSubmodule := by
  rw [Submodule.mul_le]
  intro p hp q hq
  exact mul_lin_quad_mem_cubic hp hq

theorem map_subtype_linQuadProductSubmodule_top_top :
    (linQuadProductSubmodule (⊤ : Submodule ℝ linSubmodule) ⊤).map
        cubicSubmodule.subtype =
      linSubmodule * quadSubmodule := by
  apply le_antisymm
  · rw [linQuadProductSubmodule, Submodule.map_span]
    refine Submodule.span_le.mpr ?_
    rintro q ⟨x, hx, rfl⟩
    rcases hx with ⟨aq, rfl⟩
    exact Submodule.mul_mem_mul aq.1.1.2 aq.2.1.2
  · rw [Submodule.mul_le]
    intro p hp q hq
    let a : linSubmodule := ⟨p, hp⟩
    let r : quadSubmodule := ⟨q, hq⟩
    refine ⟨linQuadProduct a r, ?_, rfl⟩
    exact linQuadProduct_mem_linQuadProductSubmodule
      (⟨a, trivial⟩ : (⊤ : Submodule ℝ linSubmodule))
      (⟨r, trivial⟩ : (⊤ : Submodule ℝ quadSubmodule))

theorem linSubmodule_mul_quadSubmodule_eq_cubicSubmodule :
    linSubmodule * quadSubmodule = cubicSubmodule := by
  rw [linSubmodule_eq_restrictTotalDegree, quadSubmodule_eq_restrictTotalDegree,
    cubicSubmodule_eq_restrictTotalDegree]
  change
    MvPolynomial.restrictSupport ℝ
        ({s : Fin 3 →₀ ℕ | s.sum (fun _ e => e) ≤ 1} : Set (Fin 3 →₀ ℕ)) *
      MvPolynomial.restrictSupport ℝ
        ({s : Fin 3 →₀ ℕ | s.sum (fun _ e => e) ≤ 2} : Set (Fin 3 →₀ ℕ)) =
      MvPolynomial.restrictSupport ℝ
        ({s : Fin 3 →₀ ℕ | s.sum (fun _ e => e) ≤ 3} : Set (Fin 3 →₀ ℕ))
  rw [← MvPolynomial.restrictSupport_add]
  rw [← bounded_totalDegree_three_eq_add_bounded_totalDegree_one_two]

theorem map_subtype_linQuadProductSubmodule_top_top_eq_cubicSubmodule :
    (linQuadProductSubmodule (⊤ : Submodule ℝ linSubmodule) ⊤).map
        cubicSubmodule.subtype =
      cubicSubmodule := by
  rw [map_subtype_linQuadProductSubmodule_top_top]
  exact linSubmodule_mul_quadSubmodule_eq_cubicSubmodule

theorem linQuadProductSubmodule_top_top_eq_top :
    linQuadProductSubmodule (⊤ : Submodule ℝ linSubmodule) ⊤ = ⊤ := by
  rw [eq_top_iff]
  intro q _hq
  have hqmap :
      (q : Poly) ∈
        (linQuadProductSubmodule (⊤ : Submodule ℝ linSubmodule) ⊤).map
          cubicSubmodule.subtype := by
    rw [map_subtype_linQuadProductSubmodule_top_top_eq_cubicSubmodule]
    exact q.2
  rcases hqmap with ⟨q', hq', hqeq⟩
  have hq'q : q' = q := Subtype.ext hqeq
  simpa [hq'q] using hq'

theorem map_subtype_linProductSubmodule_top_top_eq_quadSubmodule :
    (linProductSubmodule (⊤ : Submodule ℝ linSubmodule) ⊤).map
        quadSubmodule.subtype =
      quadSubmodule := by
  rw [map_subtype_linProductSubmodule_top_top]
  exact linSubmodule_mul_linSubmodule_eq_quadSubmodule

theorem linProductSubmodule_top_top_eq_top :
    linProductSubmodule (⊤ : Submodule ℝ linSubmodule) ⊤ = ⊤ := by
  rw [eq_top_iff]
  intro q _hq
  have hqmap :
      (q : Poly) ∈
        (linProductSubmodule (⊤ : Submodule ℝ linSubmodule) ⊤).map
          quadSubmodule.subtype := by
    rw [map_subtype_linProductSubmodule_top_top_eq_quadSubmodule]
    exact q.2
  rcases hqmap with ⟨q', hq', hqeq⟩
  have hq'q : q' = q := Subtype.ext hqeq
  simpa [hq'q] using hq'

theorem linProductSubmodule_top_top_le_span_basis_products
    (β : Module.Basis (Fin 4) ℝ linSubmodule) :
    linProductSubmodule (⊤ : Submodule ℝ linSubmodule) ⊤ ≤
      Submodule.span ℝ
        (Set.range fun ij : {ij : Fin 4 × Fin 4 // ij.1 ≤ ij.2} =>
          linProduct (β ij.1.1) (β ij.1.2)) := by
  refine linProductSubmodule_le_of_generators ?_
  intro a b
  have hrepr :=
    LinearMap.sum_repr_mul_repr_mul
      (b₁' := β) (b₂' := β) (B := linProductBilin) a.1 b.1
  change (linProductBilin a.1) b.1 ∈
    Submodule.span ℝ
      (Set.range fun ij : {ij : Fin 4 × Fin 4 // ij.1 ≤ ij.2} =>
        linProduct (β ij.1.1) (β ij.1.2))
  rw [← hrepr]
  rw [Finsupp.sum_fintype]
  swap
  · simp
  refine Submodule.sum_mem _ ?_
  intro i _hi
  rw [Finsupp.sum_fintype]
  swap
  · simp
  refine Submodule.sum_mem _ ?_
  intro j _hj
  refine Submodule.smul_mem _ _ ?_
  refine Submodule.smul_mem _ _ ?_
  change linProduct (β i) (β j) ∈
    Submodule.span ℝ
      (Set.range fun ij : {ij : Fin 4 × Fin 4 // ij.1 ≤ ij.2} =>
        linProduct (β ij.1.1) (β ij.1.2))
  by_cases hij : i ≤ j
  · exact Submodule.subset_span ⟨⟨(i, j), hij⟩, rfl⟩
  · have hji : j ≤ i := le_of_not_ge hij
    rw [linProduct_comm]
    exact Submodule.subset_span ⟨⟨(j, i), hji⟩, rfl⟩

theorem span_basis_products_eq_top
    (β : Module.Basis (Fin 4) ℝ linSubmodule) :
    Submodule.span ℝ
        (Set.range fun ij : {ij : Fin 4 × Fin 4 // ij.1 ≤ ij.2} =>
          linProduct (β ij.1.1) (β ij.1.2)) =
      ⊤ := by
  rw [← linProductSubmodule_top_top_eq_top]
  exact le_antisymm
    (by
      refine Submodule.span_le.mpr ?_
      rintro q ⟨ij, rfl⟩
      exact linProduct_mem_linProductSubmodule
        (⟨β ij.1.1, trivial⟩ : (⊤ : Submodule ℝ linSubmodule))
        (⟨β ij.1.2, trivial⟩ : (⊤ : Submodule ℝ linSubmodule)))
    (linProductSubmodule_top_top_le_span_basis_products β)

theorem linearIndependent_basis_products_fin_four
    (β : Module.Basis (Fin 4) ℝ linSubmodule) :
    LinearIndependent ℝ
      (fun ij : {ij : Fin 4 × Fin 4 // ij.1 ≤ ij.2} =>
        linProduct (β ij.1.1) (β ij.1.2)) := by
  rw [linearIndependent_iff_card_eq_finrank_span]
  rw [Set.finrank, span_basis_products_eq_top β]
  rw [finrank_top, finrank_quadSubmodule_eq_ten]
  decide

theorem linQuadProduct_reassociate
    (a b c : linSubmodule) :
    linQuadProduct a (linProduct b c) =
      linQuadProduct b (linProduct a c) := by
  ext
  simp [linQuadProduct, linProduct, mul_left_comm]

theorem linQuadProduct_reassociate_right
    (a b c : linSubmodule) :
    linQuadProduct a (linProduct b c) =
      linQuadProduct b (linProduct c a) := by
  rw [linQuadProduct_reassociate]
  rw [linProduct_comm]

theorem linQuadProductSubmodule_top_top_le_span_basis_cubic_products
    (β : Module.Basis (Fin 4) ℝ linSubmodule) :
    linQuadProductSubmodule (⊤ : Submodule ℝ linSubmodule) ⊤ ≤
      Submodule.span ℝ
        (Set.range fun ijk :
          {ijk : (Fin 4 × Fin 4) × Fin 4 // ijk.1.1 ≤ ijk.1.2 ∧ ijk.1.2 ≤ ijk.2} =>
          linQuadProduct (β ijk.1.1.1)
            (linProduct (β ijk.1.1.2) (β ijk.1.2))) := by
  let Pair4 := {ij : Fin 4 × Fin 4 // ij.1 ≤ ij.2}
  let Triple4 := {ijk : (Fin 4 × Fin 4) × Fin 4 // ijk.1.1 ≤ ijk.1.2 ∧ ijk.1.2 ≤ ijk.2}
  let quadBasis : Module.Basis Pair4 ℝ quadSubmodule :=
    Module.Basis.mk
      (by
        simpa [Pair4] using linearIndependent_basis_products_fin_four β)
      (by
        simpa [Pair4] using span_basis_products_eq_top β)
  have hquadBasis_apply (jk : Pair4) :
      quadBasis jk = linProduct (β jk.1.1) (β jk.1.2) := by
    exact Module.Basis.mk_apply
      (by
        simpa [Pair4] using linearIndependent_basis_products_fin_four β)
      (by
        simpa [Pair4] using span_basis_products_eq_top β) jk
  refine linQuadProductSubmodule_le_of_generators ?_
  intro a q
  have hrepr :=
    LinearMap.sum_repr_mul_repr_mul
      (b₁' := β) (b₂' := quadBasis) (B := linQuadProductBilin) a.1 q.1
  change (linQuadProductBilin a.1) q.1 ∈
    Submodule.span ℝ
      (Set.range fun ijk : Triple4 =>
        linQuadProduct (β ijk.1.1.1)
          (linProduct (β ijk.1.1.2) (β ijk.1.2)))
  rw [← hrepr]
  rw [Finsupp.sum_fintype]
  swap
  · simp
  refine Submodule.sum_mem _ ?_
  intro i _hi
  rw [Finsupp.sum_fintype]
  swap
  · simp
  refine Submodule.sum_mem _ ?_
  intro jk _hjk
  refine Submodule.smul_mem _ _ ?_
  refine Submodule.smul_mem _ _ ?_
  rw [hquadBasis_apply jk]
  change linQuadProduct (β i) (linProduct (β jk.1.1) (β jk.1.2)) ∈
    Submodule.span ℝ
      (Set.range fun ijk : Triple4 =>
        linQuadProduct (β ijk.1.1.1)
          (linProduct (β ijk.1.1.2) (β ijk.1.2)))
  by_cases hij : i ≤ jk.1.1
  · exact Submodule.subset_span
      ⟨⟨((i, jk.1.1), jk.1.2), hij, jk.2⟩, rfl⟩
  · have hji : jk.1.1 ≤ i := le_of_not_ge hij
    by_cases hik : i ≤ jk.1.2
    · rw [linQuadProduct_reassociate]
      exact Submodule.subset_span
        ⟨⟨((jk.1.1, i), jk.1.2), hji, hik⟩, rfl⟩
    · have hki : jk.1.2 ≤ i := le_of_not_ge hik
      rw [linQuadProduct_reassociate_right]
      exact Submodule.subset_span
        ⟨⟨((jk.1.1, jk.1.2), i), jk.2, hki⟩, rfl⟩

theorem span_basis_cubic_products_eq_top
    (β : Module.Basis (Fin 4) ℝ linSubmodule) :
    Submodule.span ℝ
        (Set.range fun ijk :
          {ijk : (Fin 4 × Fin 4) × Fin 4 // ijk.1.1 ≤ ijk.1.2 ∧ ijk.1.2 ≤ ijk.2} =>
          linQuadProduct (β ijk.1.1.1)
            (linProduct (β ijk.1.1.2) (β ijk.1.2))) =
      ⊤ := by
  rw [← linQuadProductSubmodule_top_top_eq_top]
  exact le_antisymm
    (by
      refine Submodule.span_le.mpr ?_
      rintro q ⟨ijk, rfl⟩
      exact linQuadProduct_mem_linQuadProductSubmodule
        (⟨β ijk.1.1.1, trivial⟩ : (⊤ : Submodule ℝ linSubmodule))
        (⟨linProduct (β ijk.1.1.2) (β ijk.1.2), trivial⟩ :
          (⊤ : Submodule ℝ quadSubmodule)))
    (linQuadProductSubmodule_top_top_le_span_basis_cubic_products β)

theorem linearIndependent_basis_cubic_products_fin_four
    (β : Module.Basis (Fin 4) ℝ linSubmodule) :
    LinearIndependent ℝ
      (fun ijk :
        {ijk : (Fin 4 × Fin 4) × Fin 4 // ijk.1.1 ≤ ijk.1.2 ∧ ijk.1.2 ≤ ijk.2} =>
        linQuadProduct (β ijk.1.1.1)
          (linProduct (β ijk.1.1.2) (β ijk.1.2))) := by
  rw [linearIndependent_iff_card_eq_finrank_span]
  rw [Set.finrank, span_basis_cubic_products_eq_top β]
  rw [finrank_top, finrank_cubicSubmodule_eq_twenty]
  decide

theorem exists_rank_one_adapted_basis
    {A W : Submodule ℝ linSubmodule} (hAW : IsCompl A W)
    (β : Module.Basis (Fin 3) ℝ A) {x : linSubmodule}
    (hxspan : ℝ ∙ x = W) :
    ∃ β4 : Module.Basis (Fin 4) ℝ linSubmodule,
      (∀ i : Fin 3, β4 (Fin.castSucc i) = (β i).1) ∧
        β4 ⟨3, by norm_num⟩ = x := by
  let v : Fin 4 → linSubmodule := fun i =>
    if h : i.1 < 3 then (β ⟨i.1, h⟩).1 else x
  have hv_cast : ∀ i : Fin 3, v (Fin.castSucc i) = (β i).1 := by
    intro i
    simp [v, Fin.castSucc]
  have hv_last : v ⟨3, by norm_num⟩ = x := by
    simp [v]
  have hA_le : A ≤ Submodule.span ℝ (Set.range v) := by
    intro a ha
    let aA : A := ⟨a, ha⟩
    have hrepr := β.sum_repr aA
    have hsum : (∑ i : Fin 3, β.repr aA i • (β i).1) = a := by
      change (fun z : A => (z : linSubmodule))
          (∑ i : Fin 3, β.repr aA i • β i) = (a : linSubmodule)
      exact congrArg (fun z : A => (z : linSubmodule)) hrepr
    rw [← hsum]
    refine Submodule.sum_mem _ ?_
    intro i _hi
    refine Submodule.smul_mem _ _ ?_
    rw [← hv_cast i]
    exact Submodule.subset_span ⟨Fin.castSucc i, rfl⟩
  have hW_le : W ≤ Submodule.span ℝ (Set.range v) := by
    rw [← hxspan]
    refine Submodule.span_le.mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy, ← hv_last]
    exact Submodule.subset_span ⟨⟨3, by norm_num⟩, rfl⟩
  have htop_le : ⊤ ≤ Submodule.span ℝ (Set.range v) := by
    have hsup_le : A ⊔ W ≤ Submodule.span ℝ (Set.range v) := sup_le hA_le hW_le
    simpa [hAW.codisjoint.eq_top] using hsup_le
  have hLI : LinearIndependent ℝ v :=
    linearIndependent_of_top_le_span_of_card_eq_finrank htop_le (by
      rw [Fintype.card_fin, finrank_linSubmodule_eq_four])
  let β4 : Module.Basis (Fin 4) ℝ linSubmodule := Module.Basis.mk hLI htop_le
  refine ⟨β4, ?_, ?_⟩
  · intro i
    rw [show β4 (Fin.castSucc i) = v (Fin.castSucc i) by
      exact Module.Basis.mk_apply hLI htop_le (Fin.castSucc i)]
    exact hv_cast i
  · rw [show β4 ⟨3, by norm_num⟩ = v ⟨3, by norm_num⟩ by
      exact Module.Basis.mk_apply hLI htop_le ⟨3, by norm_num⟩]
    exact hv_last

theorem linearIndependent_basis_cubic_products_fin_three_of_isCompl_line
    {A L : Submodule ℝ linSubmodule} (hAL : IsCompl A L)
    (β : Module.Basis (Fin 3) ℝ A) {x : linSubmodule}
    (hxspan : ℝ ∙ x = L) :
    LinearIndependent ℝ
      (fun ijk :
        {ijk : (Fin 3 × Fin 3) × Fin 3 // ijk.1.1 ≤ ijk.1.2 ∧ ijk.1.2 ≤ ijk.2} =>
        linQuadProduct (β ijk.1.1.1).1
          (linProduct (β ijk.1.1.2).1 (β ijk.1.2).1)) := by
  rcases exists_rank_one_adapted_basis hAL β hxspan with
    ⟨β4, hβA, _hβx⟩
  let Triple3 :=
    {ijk : (Fin 3 × Fin 3) × Fin 3 // ijk.1.1 ≤ ijk.1.2 ∧ ijk.1.2 ≤ ijk.2}
  let Triple4 :=
    {ijk : (Fin 4 × Fin 4) × Fin 4 // ijk.1.1 ≤ ijk.1.2 ∧ ijk.1.2 ≤ ijk.2}
  let φ : Triple3 → Triple4 := fun ijk =>
    ⟨((Fin.castSucc ijk.1.1.1, Fin.castSucc ijk.1.1.2), Fin.castSucc ijk.1.2), by
      constructor
      · exact (Fin.castSucc_le_castSucc_iff).mpr ijk.2.1
      · exact (Fin.castSucc_le_castSucc_iff).mpr ijk.2.2⟩
  have hφinj : Function.Injective φ := by
    intro a b h
    apply Subtype.ext
    have hp := congrArg Subtype.val h
    have hfstfst :
        Fin.castSucc a.1.1.1 = Fin.castSucc b.1.1.1 :=
      congrArg (fun t => t.1.1) hp
    have hfstsnd :
        Fin.castSucc a.1.1.2 = Fin.castSucc b.1.1.2 :=
      congrArg (fun t => t.1.2) hp
    have hsnd :
        Fin.castSucc a.1.2 = Fin.castSucc b.1.2 :=
      congrArg Prod.snd hp
    exact Prod.ext
      (Prod.ext ((Fin.castSucc_injective 3) hfstfst)
        ((Fin.castSucc_injective 3) hfstsnd))
      ((Fin.castSucc_injective 3) hsnd)
  have hsub := (linearIndependent_basis_cubic_products_fin_four β4).comp φ hφinj
  let target : Triple3 → cubicSubmodule := fun ijk =>
    linQuadProduct (β ijk.1.1.1).1
      (linProduct (β ijk.1.1.2).1 (β ijk.1.2).1)
  let pulled : Triple3 → cubicSubmodule := fun ijk =>
    linQuadProduct (β4 (φ ijk).1.1.1)
      (linProduct (β4 (φ ijk).1.1.2) (β4 (φ ijk).1.2))
  have hpulled : pulled = target := by
    funext ijk
    dsimp [pulled, target, φ]
    rw [hβA ijk.1.1.1, hβA ijk.1.1.2, hβA ijk.1.2]
  change LinearIndependent ℝ pulled at hsub
  change LinearIndependent ℝ target
  exact hpulled ▸ hsub

abbrev Pair3Idx := {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2}

abbrev Triple3Idx :=
  {ijk : (Fin 3 × Fin 3) × Fin 3 // ijk.1.1 ≤ ijk.1.2 ∧ ijk.1.2 ≤ ijk.2}

def pair3ZeroZero : Pair3Idx :=
  ⟨(0, 0), by norm_num⟩

def pair3ZeroOne : Pair3Idx :=
  ⟨(0, 1), by norm_num⟩

def triple3ZeroZeroZero : Triple3Idx :=
  ⟨((0, 0), 0), by norm_num⟩

def triple3ZeroZeroOne : Triple3Idx :=
  ⟨((0, 0), 1), by norm_num⟩

def spanPairProductsExceptZeroZero
    {A : Submodule ℝ linSubmodule} (β : Module.Basis (Fin 3) ℝ A) :
    Submodule ℝ quadSubmodule :=
  Submodule.span ℝ
    (Set.range fun ij : {ij : Pair3Idx // ij ≠ pair3ZeroZero} =>
      linProduct (β ij.1.1.1).1 (β ij.1.1.2).1)

def spanCubicProductsExceptZeroZeroZero
    {A : Submodule ℝ linSubmodule} (β : Module.Basis (Fin 3) ℝ A) :
    Submodule ℝ cubicSubmodule :=
  Submodule.span ℝ
    (Set.range fun ijk : {ijk : Triple3Idx // ijk ≠ triple3ZeroZeroZero} =>
      linQuadProduct (β ijk.1.1.1.1).1
        (linProduct (β ijk.1.1.1.2).1 (β ijk.1.1.2).1))

def spanPairProductsExceptZeroZeroZeroOne
    {A : Submodule ℝ linSubmodule} (β : Module.Basis (Fin 3) ℝ A) :
    Submodule ℝ quadSubmodule :=
  Submodule.span ℝ
    (Set.range fun ij :
      {ij : Pair3Idx // ij ≠ pair3ZeroZero ∧ ij ≠ pair3ZeroOne} =>
      linProduct (β ij.1.1.1).1 (β ij.1.1.2).1)

def spanCubicProductsExceptZeroZeroZeroZeroOne
    {A : Submodule ℝ linSubmodule} (β : Module.Basis (Fin 3) ℝ A) :
    Submodule ℝ cubicSubmodule :=
  Submodule.span ℝ
    (Set.range fun ijk :
      {ijk : Triple3Idx // ijk ≠ triple3ZeroZeroZero ∧ ijk ≠ triple3ZeroZeroOne} =>
      linQuadProduct (β ijk.1.1.1.1).1
        (linProduct (β ijk.1.1.1.2).1 (β ijk.1.1.2).1))

theorem spanPairProductsExceptZeroZero_le_symSquareSubmodule
    {A : Submodule ℝ linSubmodule} (β : Module.Basis (Fin 3) ℝ A) :
    spanPairProductsExceptZeroZero β ≤ symSquareSubmodule A := by
  refine Submodule.span_le.mpr ?_
  rintro q ⟨ij, rfl⟩
  exact linProduct_mem_linProductSubmodule
    (⟨(β ij.1.1.1).1, (β ij.1.1.1).2⟩ : A)
    (⟨(β ij.1.1.2).1, (β ij.1.1.2).2⟩ : A)

theorem spanPairProductsExceptZeroZeroZeroOne_le_symSquareSubmodule
    {A : Submodule ℝ linSubmodule} (β : Module.Basis (Fin 3) ℝ A) :
    spanPairProductsExceptZeroZeroZeroOne β ≤ symSquareSubmodule A := by
  refine Submodule.span_le.mpr ?_
  rintro q ⟨ij, rfl⟩
  exact linProduct_mem_linProductSubmodule
    (⟨(β ij.1.1.1).1, (β ij.1.1.1).2⟩ : A)
    (⟨(β ij.1.1.2).1, (β ij.1.1.2).2⟩ : A)

theorem spanCubicProductsExceptZeroZeroZero_le_linQuadProductSubmodule_exceptZeroZero
    {A : Submodule ℝ linSubmodule} (β : Module.Basis (Fin 3) ℝ A) :
    spanCubicProductsExceptZeroZeroZero β ≤
      linQuadProductSubmodule A (spanPairProductsExceptZeroZero β) := by
  refine Submodule.span_le.mpr ?_
  rintro c ⟨ijk, rfl⟩
  let jk : Pair3Idx := ⟨(ijk.1.1.1.2, ijk.1.1.2), ijk.1.2.2⟩
  have hjk_ne : jk ≠ pair3ZeroZero := by
    intro h
    have hj : ijk.1.1.1.2 = (0 : Fin 3) := by
      exact congrArg (fun p : Pair3Idx => p.1.1) h
    have hk : ijk.1.1.2 = (0 : Fin 3) := by
      exact congrArg (fun p : Pair3Idx => p.1.2) h
    have hi : ijk.1.1.1.1 = (0 : Fin 3) := by
      have hij := ijk.1.2.1
      rw [hj] at hij
      apply Fin.ext
      have hival : ijk.1.1.1.1.val ≤ 0 := by
        simpa [Fin.le_def] using hij
      omega
    exact ijk.2 (Subtype.ext (Prod.ext (Prod.ext hi hj) hk))
  have hpair :
      linProduct (β ijk.1.1.1.2).1 (β ijk.1.1.2).1 ∈
        spanPairProductsExceptZeroZero β := by
    exact Submodule.subset_span ⟨⟨jk, hjk_ne⟩, rfl⟩
  exact linQuadProduct_mem_linQuadProductSubmodule
    (⟨(β ijk.1.1.1.1).1, (β ijk.1.1.1.1).2⟩ : A)
    (⟨linProduct (β ijk.1.1.1.2).1 (β ijk.1.1.2).1, hpair⟩ :
      spanPairProductsExceptZeroZero β)

theorem finrank_spanCubicProductsExceptZeroZeroZero_eq_nine_of_isCompl_line
    {A L : Submodule ℝ linSubmodule} (hAL : IsCompl A L)
    (β : Module.Basis (Fin 3) ℝ A) {x : linSubmodule}
    (hxspan : ℝ ∙ x = L) :
    Module.finrank ℝ (spanCubicProductsExceptZeroZeroZero β) = 9 := by
  have hLIall :=
    linearIndependent_basis_cubic_products_fin_three_of_isCompl_line hAL β hxspan
  let f : {ijk : Triple3Idx // ijk ≠ triple3ZeroZeroZero} → cubicSubmodule :=
    fun ijk =>
      linQuadProduct (β ijk.1.1.1.1).1
        (linProduct (β ijk.1.1.1.2).1 (β ijk.1.1.2).1)
  have hLI : LinearIndependent ℝ f :=
    hLIall.comp (fun ijk : {ijk : Triple3Idx // ijk ≠ triple3ZeroZeroZero} => ijk.1)
      (fun a b h => Subtype.ext h)
  have hcard :
      Fintype.card {ijk : Triple3Idx // ijk ≠ triple3ZeroZeroZero} = 9 := by
    decide
  have hspan :
      Module.finrank ℝ (Submodule.span ℝ (Set.range f)) = 9 := by
    have hcard_eq :
        Fintype.card {ijk : Triple3Idx // ijk ≠ triple3ZeroZeroZero} =
          Module.finrank ℝ (Submodule.span ℝ (Set.range f)) := by
      exact (linearIndependent_iff_card_eq_finrank_span (R := ℝ) (b := f)).mp hLI
    omega
  simpa [spanCubicProductsExceptZeroZeroZero, f] using hspan

theorem nine_le_finrank_linQuadProductSubmodule_exceptZeroZero_of_isCompl_line
    {A L : Submodule ℝ linSubmodule} (hAL : IsCompl A L)
    (β : Module.Basis (Fin 3) ℝ A) {x : linSubmodule}
    (hxspan : ℝ ∙ x = L) :
    9 ≤ Module.finrank ℝ
      (linQuadProductSubmodule A (spanPairProductsExceptZeroZero β)) := by
  have hle :=
    spanCubicProductsExceptZeroZeroZero_le_linQuadProductSubmodule_exceptZeroZero β
  have hmono := Submodule.finrank_mono hle
  have hspan :=
    finrank_spanCubicProductsExceptZeroZeroZero_eq_nine_of_isCompl_line
      hAL β hxspan
  omega

theorem spanCubicProductsExceptZeroZeroZeroZeroOne_le_linQuadProductSubmodule_exceptZeroZeroZeroOne
    {A : Submodule ℝ linSubmodule} (β : Module.Basis (Fin 3) ℝ A) :
    spanCubicProductsExceptZeroZeroZeroZeroOne β ≤
      linQuadProductSubmodule A (spanPairProductsExceptZeroZeroZeroOne β) := by
  refine Submodule.span_le.mpr ?_
  rintro c ⟨ijk, rfl⟩
  let jk : Pair3Idx := ⟨(ijk.1.1.1.2, ijk.1.1.2), ijk.1.2.2⟩
  have hjk_ne00 : jk ≠ pair3ZeroZero := by
    intro h
    have hj : ijk.1.1.1.2 = (0 : Fin 3) := by
      exact congrArg (fun p : Pair3Idx => p.1.1) h
    have hk : ijk.1.1.2 = (0 : Fin 3) := by
      exact congrArg (fun p : Pair3Idx => p.1.2) h
    have hi : ijk.1.1.1.1 = (0 : Fin 3) := by
      have hij := ijk.1.2.1
      rw [hj] at hij
      apply Fin.ext
      have hival : ijk.1.1.1.1.val ≤ 0 := by
        simpa [Fin.le_def] using hij
      omega
    exact ijk.2.1 (Subtype.ext (Prod.ext (Prod.ext hi hj) hk))
  have hjk_ne01 : jk ≠ pair3ZeroOne := by
    intro h
    have hj : ijk.1.1.1.2 = (0 : Fin 3) := by
      exact congrArg (fun p : Pair3Idx => p.1.1) h
    have hk : ijk.1.1.2 = (1 : Fin 3) := by
      exact congrArg (fun p : Pair3Idx => p.1.2) h
    have hi : ijk.1.1.1.1 = (0 : Fin 3) := by
      have hij := ijk.1.2.1
      rw [hj] at hij
      apply Fin.ext
      have hival : ijk.1.1.1.1.val ≤ 0 := by
        simpa [Fin.le_def] using hij
      omega
    exact ijk.2.2 (Subtype.ext (Prod.ext (Prod.ext hi hj) hk))
  have hpair :
      linProduct (β ijk.1.1.1.2).1 (β ijk.1.1.2).1 ∈
        spanPairProductsExceptZeroZeroZeroOne β := by
    exact Submodule.subset_span ⟨⟨jk, hjk_ne00, hjk_ne01⟩, rfl⟩
  exact linQuadProduct_mem_linQuadProductSubmodule
    (⟨(β ijk.1.1.1.1).1, (β ijk.1.1.1.1).2⟩ : A)
    (⟨linProduct (β ijk.1.1.1.2).1 (β ijk.1.1.2).1, hpair⟩ :
      spanPairProductsExceptZeroZeroZeroOne β)

theorem finrank_spanCubicProductsExceptZeroZeroZeroZeroOne_eq_eight_of_isCompl_line
    {A L : Submodule ℝ linSubmodule} (hAL : IsCompl A L)
    (β : Module.Basis (Fin 3) ℝ A) {x : linSubmodule}
    (hxspan : ℝ ∙ x = L) :
    Module.finrank ℝ (spanCubicProductsExceptZeroZeroZeroZeroOne β) = 8 := by
  have hLIall :=
    linearIndependent_basis_cubic_products_fin_three_of_isCompl_line hAL β hxspan
  let f :
      {ijk : Triple3Idx //
        ijk ≠ triple3ZeroZeroZero ∧ ijk ≠ triple3ZeroZeroOne} → cubicSubmodule :=
    fun ijk =>
      linQuadProduct (β ijk.1.1.1.1).1
        (linProduct (β ijk.1.1.1.2).1 (β ijk.1.1.2).1)
  have hLI : LinearIndependent ℝ f :=
    hLIall.comp
      (fun ijk :
        {ijk : Triple3Idx //
          ijk ≠ triple3ZeroZeroZero ∧ ijk ≠ triple3ZeroZeroOne} =>
        ijk.1)
      (fun a b h => Subtype.ext h)
  have hcard :
      Fintype.card
        {ijk : Triple3Idx //
          ijk ≠ triple3ZeroZeroZero ∧ ijk ≠ triple3ZeroZeroOne} = 8 := by
    decide
  have hspan :
      Module.finrank ℝ (Submodule.span ℝ (Set.range f)) = 8 := by
    have hcard_eq :
        Fintype.card
          {ijk : Triple3Idx //
            ijk ≠ triple3ZeroZeroZero ∧ ijk ≠ triple3ZeroZeroOne} =
          Module.finrank ℝ (Submodule.span ℝ (Set.range f)) := by
      exact (linearIndependent_iff_card_eq_finrank_span (R := ℝ) (b := f)).mp hLI
    omega
  simpa [spanCubicProductsExceptZeroZeroZeroZeroOne, f] using hspan

theorem eight_le_finrank_linQuadProductSubmodule_exceptZeroZeroZeroOne_of_isCompl_line
    {A L : Submodule ℝ linSubmodule} (hAL : IsCompl A L)
    (β : Module.Basis (Fin 3) ℝ A) {x : linSubmodule}
    (hxspan : ℝ ∙ x = L) :
    8 ≤ Module.finrank ℝ
      (linQuadProductSubmodule A (spanPairProductsExceptZeroZeroZeroOne β)) := by
  have hle :=
    spanCubicProductsExceptZeroZeroZeroZeroOne_le_linQuadProductSubmodule_exceptZeroZeroZeroOne
      β
  have hmono := Submodule.finrank_mono hle
  have hspan :=
    finrank_spanCubicProductsExceptZeroZeroZeroZeroOne_eq_eight_of_isCompl_line
      hAL β hxspan
  omega

theorem linearIndependent_rank_one_combined_products_of_isCompl
    {A W : Submodule ℝ linSubmodule} (hAW : IsCompl A W)
    (β : Module.Basis (Fin 3) ℝ A) {x : linSubmodule}
    (hxspan : ℝ ∙ x = W) :
    LinearIndependent ℝ
      (Sum.elim
        (fun i : Fin 3 => linProduct x (β i).1)
        (fun ij : {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} =>
          linProduct (β ij.1.1).1 (β ij.1.2).1)) := by
  rcases exists_rank_one_adapted_basis hAW β hxspan with ⟨β4, hβA, hβx⟩
  let last : Fin 4 := ⟨3, by norm_num⟩
  let Pair3 := {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2}
  let Pair4 := {ij : Fin 4 × Fin 4 // ij.1 ≤ ij.2}
  let φ : (Fin 3 ⊕ Pair3) → Pair4 :=
    Sum.elim
      (fun i : Fin 3 =>
        ⟨(Fin.castSucc i, last), le_of_lt (Fin.castSucc_lt_last i)⟩)
      (fun ij : Pair3 =>
        ⟨(Fin.castSucc ij.1.1, Fin.castSucc ij.1.2),
          Fin.castSucc_le_castSucc_iff.mpr ij.2⟩)
  have hφinj : Function.Injective φ := by
    intro a b h
    cases a with
    | inl i =>
        cases b with
        | inl j =>
            have hp := congrArg Subtype.val h
            have hi : Fin.castSucc i = Fin.castSucc j := congrArg Prod.fst hp
            exact congrArg Sum.inl ((Fin.castSucc_injective 3) hi)
        | inr ij =>
            have hp := congrArg Subtype.val h
            have hsec : last = Fin.castSucc ij.1.2 := congrArg Prod.snd hp
            have hlt : Fin.castSucc ij.1.2 < last := Fin.castSucc_lt_last ij.1.2
            rw [← hsec] at hlt
            exact False.elim ((lt_self_iff_false last).mp hlt)
    | inr ij =>
        cases b with
        | inl j =>
            have hp := congrArg Subtype.val h
            have hsec : Fin.castSucc ij.1.2 = last := congrArg Prod.snd hp
            have hlt : Fin.castSucc ij.1.2 < last := Fin.castSucc_lt_last ij.1.2
            rw [hsec] at hlt
            exact False.elim ((lt_self_iff_false last).mp hlt)
        | inr kl =>
            have hp := congrArg Subtype.val h
            have hfst : Fin.castSucc ij.1.1 = Fin.castSucc kl.1.1 :=
              congrArg Prod.fst hp
            have hsnd : Fin.castSucc ij.1.2 = Fin.castSucc kl.1.2 :=
              congrArg Prod.snd hp
            have hij : ij.1 = kl.1 :=
              Prod.ext ((Fin.castSucc_injective 3) hfst)
                ((Fin.castSucc_injective 3) hsnd)
            exact congrArg Sum.inr (Subtype.ext hij)
  have hsub := (linearIndependent_basis_products_fin_four β4).comp φ hφinj
  let target : (Fin 3 ⊕ Pair3) → quadSubmodule :=
    Sum.elim
      (fun i : Fin 3 => linProduct x (β i).1)
      (fun ij : Pair3 => linProduct (β ij.1.1).1 (β ij.1.2).1)
  let pulled : (Fin 3 ⊕ Pair3) → quadSubmodule :=
    fun t => linProduct (β4 (φ t).1.1) (β4 (φ t).1.2)
  have hlast : β4 (3 : Fin 4) = x := by
    simpa [last] using hβx
  have hpulled : pulled = target := by
    funext t
    cases t with
    | inl i =>
        dsimp [pulled, target, φ, last]
        rw [hβA i, hlast, linProduct_comm]
    | inr ij =>
        dsimp [pulled, target, φ]
        rw [hβA ij.1.1, hβA ij.1.2]
  change LinearIndependent ℝ pulled at hsub
  change LinearIndependent ℝ target
  exact hpulled ▸ hsub

theorem linearIndependent_basis_pair_products_fin_three_of_isCompl_line
    {A L : Submodule ℝ linSubmodule} (hAL : IsCompl A L)
    (β : Module.Basis (Fin 3) ℝ A) {x : linSubmodule}
    (hxspan : ℝ ∙ x = L) :
    LinearIndependent ℝ
      (fun ij : {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} =>
        linProduct (β ij.1.1).1 (β ij.1.2).1) := by
  let Pair3 := {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2}
  have hcombined :=
    linearIndependent_rank_one_combined_products_of_isCompl hAL β hxspan
  let φ : Pair3 → (Fin 3 ⊕ Pair3) := Sum.inr
  have hφinj : Function.Injective φ := by
    intro a b h
    exact Sum.inr.inj h
  exact hcombined.comp φ hφinj

theorem finrank_spanPairProductsExceptZeroZero_eq_five_of_isCompl_line
    {A L : Submodule ℝ linSubmodule} (hAL : IsCompl A L)
    (β : Module.Basis (Fin 3) ℝ A) {x : linSubmodule}
    (hxspan : ℝ ∙ x = L) :
    Module.finrank ℝ (spanPairProductsExceptZeroZero β) = 5 := by
  have hLIall :=
    linearIndependent_basis_pair_products_fin_three_of_isCompl_line hAL β hxspan
  let f : {ij : Pair3Idx // ij ≠ pair3ZeroZero} → quadSubmodule :=
    fun ij => linProduct (β ij.1.1.1).1 (β ij.1.1.2).1
  have hLI : LinearIndependent ℝ f :=
    hLIall.comp (fun ij : {ij : Pair3Idx // ij ≠ pair3ZeroZero} => ij.1)
      (fun a b h => Subtype.ext h)
  have hcard :
      Fintype.card {ij : Pair3Idx // ij ≠ pair3ZeroZero} = 5 := by
    decide
  have hspan :
      Module.finrank ℝ (Submodule.span ℝ (Set.range f)) = 5 := by
    have hcard_eq :
        Fintype.card {ij : Pair3Idx // ij ≠ pair3ZeroZero} =
          Module.finrank ℝ (Submodule.span ℝ (Set.range f)) := by
      exact (linearIndependent_iff_card_eq_finrank_span (R := ℝ) (b := f)).mp hLI
    omega
  simpa [spanPairProductsExceptZeroZero, f] using hspan

theorem finrank_spanPairProductsExceptZeroZeroZeroOne_eq_four_of_isCompl_line
    {A L : Submodule ℝ linSubmodule} (hAL : IsCompl A L)
    (β : Module.Basis (Fin 3) ℝ A) {x : linSubmodule}
    (hxspan : ℝ ∙ x = L) :
    Module.finrank ℝ (spanPairProductsExceptZeroZeroZeroOne β) = 4 := by
  have hLIall :=
    linearIndependent_basis_pair_products_fin_three_of_isCompl_line hAL β hxspan
  let f :
      {ij : Pair3Idx // ij ≠ pair3ZeroZero ∧ ij ≠ pair3ZeroOne} → quadSubmodule :=
    fun ij => linProduct (β ij.1.1.1).1 (β ij.1.1.2).1
  have hLI : LinearIndependent ℝ f :=
    hLIall.comp
      (fun ij : {ij : Pair3Idx // ij ≠ pair3ZeroZero ∧ ij ≠ pair3ZeroOne} =>
        ij.1)
      (fun a b h => Subtype.ext h)
  have hcard :
      Fintype.card
        {ij : Pair3Idx // ij ≠ pair3ZeroZero ∧ ij ≠ pair3ZeroOne} = 4 := by
    decide
  have hspan :
      Module.finrank ℝ (Submodule.span ℝ (Set.range f)) = 4 := by
    have hcard_eq :
        Fintype.card
          {ij : Pair3Idx // ij ≠ pair3ZeroZero ∧ ij ≠ pair3ZeroOne} =
          Module.finrank ℝ (Submodule.span ℝ (Set.range f)) := by
      exact (linearIndependent_iff_card_eq_finrank_span (R := ℝ) (b := f)).mp hLI
    omega
  simpa [spanPairProductsExceptZeroZeroZeroOne, f] using hspan

theorem finrank_symSquareSubmodule_eq_six_of_isCompl_line
    {A L : Submodule ℝ linSubmodule} (hAL : IsCompl A L)
    (β : Module.Basis (Fin 3) ℝ A) {x : linSubmodule}
    (hxspan : ℝ ∙ x = L) :
    Module.finrank ℝ (symSquareSubmodule A) = 6 :=
  finrank_symSquareSubmodule_eq_six_of_basis_products_linearIndependent β
    (linearIndependent_basis_pair_products_fin_three_of_isCompl_line hAL β hxspan)

theorem linQuadProduct_mem_span_basis_cubic_products_of_mem_symSquare
    {A : Submodule ℝ linSubmodule}
    (β : Module.Basis (Fin 3) ℝ A)
    (a : A) {q : quadSubmodule}
    (hq : q ∈ symSquareSubmodule A) :
    linQuadProduct a.1 q ∈
      Submodule.span ℝ
        (Set.range fun ijk :
          {ijk : (Fin 3 × Fin 3) × Fin 3 // ijk.1.1 ≤ ijk.1.2 ∧ ijk.1.2 ≤ ijk.2} =>
          linQuadProduct (β ijk.1.1.1).1
            (linProduct (β ijk.1.1.2).1 (β ijk.1.2).1)) := by
  let Triple3 :=
    {ijk : (Fin 3 × Fin 3) × Fin 3 // ijk.1.1 ≤ ijk.1.2 ∧ ijk.1.2 ≤ ijk.2}
  let C : Submodule ℝ cubicSubmodule :=
    Submodule.span ℝ
      (Set.range fun ijk : Triple3 =>
        linQuadProduct (β ijk.1.1.1).1
          (linProduct (β ijk.1.1.2).1 (β ijk.1.2).1))
  have hqspan :
      q ∈ Submodule.span ℝ
        (Set.range fun ij : {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} =>
          linProduct (β ij.1.1).1 (β ij.1.2).1) := by
    simpa [span_basis_pair_products_eq_symSquareSubmodule β] using hq
  change linQuadProduct a.1 q ∈ C
  refine Submodule.span_induction
    (p := fun q _hq => linQuadProduct a.1 q ∈ C) ?_ ?_ ?_ ?_ hqspan
  · intro r hr
    rcases hr with ⟨ij, rfl⟩
    have hrepr := β.sum_repr a
    have hsum : (∑ i : Fin 3, β.repr a i • (β i).1) = (a : linSubmodule) := by
      change (fun z : A => (z : linSubmodule))
          (∑ i : Fin 3, β.repr a i • β i) = (a : linSubmodule)
      exact congrArg (fun z : A => (z : linSubmodule)) hrepr
    rw [← hsum]
    change (linQuadProductBilin (∑ i : Fin 3, β.repr a i • (β i).1))
        (linProduct (β ij.1.1).1 (β ij.1.2).1) ∈ C
    rw [map_sum]
    rw [LinearMap.sum_apply]
    refine Submodule.sum_mem C ?_
    intro i _hi
    rw [map_smul]
    change (β.repr a i) •
        linQuadProduct (β i).1 (linProduct (β ij.1.1).1 (β ij.1.2).1) ∈ C
    refine Submodule.smul_mem _ _ ?_
    change linQuadProduct (β i).1 (linProduct (β ij.1.1).1 (β ij.1.2).1) ∈ C
    by_cases hij : i ≤ ij.1.1
    · exact Submodule.subset_span
        ⟨⟨((i, ij.1.1), ij.1.2), hij, ij.2⟩, rfl⟩
    · have hji : ij.1.1 ≤ i := le_of_not_ge hij
      by_cases hik : i ≤ ij.1.2
      · rw [linQuadProduct_reassociate]
        exact Submodule.subset_span
          ⟨⟨((ij.1.1, i), ij.1.2), hji, hik⟩, rfl⟩
      · have hki : ij.1.2 ≤ i := le_of_not_ge hik
        rw [linQuadProduct_reassociate_right]
        exact Submodule.subset_span
          ⟨⟨((ij.1.1, ij.1.2), i), ij.2, hki⟩, rfl⟩
  · change linQuadProduct a.1 (0 : quadSubmodule) ∈ C
    rw [show linQuadProduct a.1 (0 : quadSubmodule) = 0 by
      ext
      simp [linQuadProduct]]
    exact C.zero_mem
  · intro x y _hx _hy hxC hyC
    simpa [linQuadProduct_add_right] using C.add_mem hxC hyC
  · intro c x _hx hxC
    simpa [linQuadProduct_smul_right] using C.smul_mem c hxC

theorem span_basis_cubic_products_eq_linQuadProductSubmodule_symSquare
    {A : Submodule ℝ linSubmodule}
    (β : Module.Basis (Fin 3) ℝ A) :
    Submodule.span ℝ
        (Set.range fun ijk :
          {ijk : (Fin 3 × Fin 3) × Fin 3 // ijk.1.1 ≤ ijk.1.2 ∧ ijk.1.2 ≤ ijk.2} =>
          linQuadProduct (β ijk.1.1.1).1
            (linProduct (β ijk.1.1.2).1 (β ijk.1.2).1)) =
      linQuadProductSubmodule A (symSquareSubmodule A) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro q ⟨ijk, rfl⟩
    exact linQuadProduct_mem_linQuadProductSubmodule
      (⟨(β ijk.1.1.1).1, (β ijk.1.1.1).2⟩ : A)
      (⟨linProduct (β ijk.1.1.2).1 (β ijk.1.2).1,
        linProduct_mem_linProductSubmodule
          (⟨(β ijk.1.1.2).1, (β ijk.1.1.2).2⟩ : A)
          (⟨(β ijk.1.2).1, (β ijk.1.2).2⟩ : A)⟩ :
        symSquareSubmodule A)
  · refine linQuadProductSubmodule_le_of_generators ?_
    intro a q
    exact linQuadProduct_mem_span_basis_cubic_products_of_mem_symSquare
      β a q.2

theorem finrank_linQuadProductSubmodule_symSquare_eq_ten_of_isCompl_line
    {A L : Submodule ℝ linSubmodule} (hAL : IsCompl A L)
    (β : Module.Basis (Fin 3) ℝ A) {x : linSubmodule}
    (hxspan : ℝ ∙ x = L) :
    Module.finrank ℝ (linQuadProductSubmodule A (symSquareSubmodule A)) = 10 := by
  let Triple3 :=
    {ijk : (Fin 3 × Fin 3) × Fin 3 // ijk.1.1 ≤ ijk.1.2 ∧ ijk.1.2 ≤ ijk.2}
  have hLI :
      LinearIndependent ℝ
        (fun ijk : Triple3 =>
          linQuadProduct (β ijk.1.1.1).1
            (linProduct (β ijk.1.1.2).1 (β ijk.1.2).1)) :=
    linearIndependent_basis_cubic_products_fin_three_of_isCompl_line hAL β hxspan
  have hcard :
      Fintype.card Triple3 =
        Module.finrank ℝ
          (Submodule.span ℝ
            (Set.range fun ijk : Triple3 =>
              linQuadProduct (β ijk.1.1.1).1
                (linProduct (β ijk.1.1.2).1 (β ijk.1.2).1))) := by
    exact (linearIndependent_iff_card_eq_finrank_span (R := ℝ)
      (b := fun ijk : Triple3 =>
        linQuadProduct (β ijk.1.1.1).1
          (linProduct (β ijk.1.1.2).1 (β ijk.1.2).1))).mp hLI
  have hTripleCard : Fintype.card Triple3 = 10 := by
    decide
  have hspan_finrank :
      Module.finrank ℝ
          (Submodule.span ℝ
            (Set.range fun ijk : Triple3 =>
              linQuadProduct (β ijk.1.1.1).1
                (linProduct (β ijk.1.1.2).1 (β ijk.1.2).1))) = 10 := by
    omega
  rw [← span_basis_cubic_products_eq_linQuadProductSubmodule_symSquare β]
  exact hspan_finrank

theorem finrank_symSquare_quotient_eq_zero_of_eq_symSquare
    {A : Submodule ℝ linSubmodule} {P : Submodule ℝ quadSubmodule}
    (hP : P = symSquareSubmodule A) :
    Module.finrank ℝ
        (symSquareSubmodule A ⧸
          P.comap (symSquareSubmodule A).subtype) = 0 := by
  subst P
  simp

theorem finrank_linQuadProductSubmodule_quotient_eq_zero_of_eq_symSquare
    {A : Submodule ℝ linSubmodule} {P : Submodule ℝ quadSubmodule}
    (hP : P = symSquareSubmodule A) :
    Module.finrank ℝ
        (linQuadProductSubmodule A (symSquareSubmodule A) ⧸
          (linQuadProductSubmodule A P).comap
            (linQuadProductSubmodule A (symSquareSubmodule A)).subtype) = 0 := by
  subst P
  simp

theorem macaulay_cokernel_bound_of_eq_symSquare
    {A : Submodule ℝ linSubmodule} {P : Submodule ℝ quadSubmodule}
    (hP : P = symSquareSubmodule A) :
    Module.finrank ℝ
        (linQuadProductSubmodule A (symSquareSubmodule A) ⧸
          (linQuadProductSubmodule A P).comap
            (linQuadProductSubmodule A (symSquareSubmodule A)).subtype) ≤
      Module.finrank ℝ
        (symSquareSubmodule A ⧸
          P.comap (symSquareSubmodule A).subtype) := by
  rw [finrank_linQuadProductSubmodule_quotient_eq_zero_of_eq_symSquare hP,
    finrank_symSquare_quotient_eq_zero_of_eq_symSquare hP]

theorem eq_symSquare_of_finrank_symSquare_quotient_eq_zero
    {A : Submodule ℝ linSubmodule} {P : Submodule ℝ quadSubmodule}
    (hP_le : P ≤ symSquareSubmodule A)
    (hquot :
      Module.finrank ℝ
        (symSquareSubmodule A ⧸
          P.comap (symSquareSubmodule A).subtype) = 0) :
    P = symSquareSubmodule A := by
  apply le_antisymm hP_le
  intro q hq
  let S : Submodule ℝ (symSquareSubmodule A) :=
    P.comap (symSquareSubmodule A).subtype
  have hSfin :
      Module.finrank ℝ S =
        Module.finrank ℝ (symSquareSubmodule A) := by
    have hdim := Submodule.finrank_quotient (R := ℝ) (S := ℝ) S
    have hquotS :
        Module.finrank ℝ ((symSquareSubmodule A) ⧸ S) = 0 := hquot
    rw [hquotS] at hdim
    have hle :
        Module.finrank ℝ S ≤
          Module.finrank ℝ (symSquareSubmodule A) := by
      simpa [finrank_top] using
        (Submodule.finrank_mono (show S ≤ (⊤ : Submodule ℝ (symSquareSubmodule A)) from le_top))
    omega
  have hStop : S = ⊤ := Submodule.eq_top_of_finrank_eq hSfin
  have hmemS : (⟨q, hq⟩ : symSquareSubmodule A) ∈ S := by
    rw [hStop]
    trivial
  exact hmemS

theorem macaulay_cokernel_bound_of_finrank_symSquare_quotient_eq_zero
    {A : Submodule ℝ linSubmodule} {P : Submodule ℝ quadSubmodule}
    (hP_le : P ≤ symSquareSubmodule A)
    (hquot :
      Module.finrank ℝ
        (symSquareSubmodule A ⧸
          P.comap (symSquareSubmodule A).subtype) = 0) :
    Module.finrank ℝ
        (linQuadProductSubmodule A (symSquareSubmodule A) ⧸
          (linQuadProductSubmodule A P).comap
            (linQuadProductSubmodule A (symSquareSubmodule A)).subtype) ≤
      Module.finrank ℝ
        (symSquareSubmodule A ⧸
          P.comap (symSquareSubmodule A).subtype) := by
  exact macaulay_cokernel_bound_of_eq_symSquare
    (eq_symSquare_of_finrank_symSquare_quotient_eq_zero hP_le hquot)

theorem finrank_symSquare_quotient_eq_one_of_eq_spanPairProductsExceptZeroZero
    {A L : Submodule ℝ linSubmodule} (hAL : IsCompl A L)
    (β : Module.Basis (Fin 3) ℝ A) {x : linSubmodule}
    (hxspan : ℝ ∙ x = L) {P : Submodule ℝ quadSubmodule}
    (hP : P = spanPairProductsExceptZeroZero β) :
    Module.finrank ℝ
        (symSquareSubmodule A ⧸
          P.comap (symSquareSubmodule A).subtype) = 1 := by
  subst P
  let S : Submodule ℝ (symSquareSubmodule A) :=
    (spanPairProductsExceptZeroZero β).comap (symSquareSubmodule A).subtype
  have hle := spanPairProductsExceptZeroZero_le_symSquareSubmodule β
  have hSfin :
      Module.finrank ℝ S =
        Module.finrank ℝ (spanPairProductsExceptZeroZero β) := by
    exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  have hquot := Submodule.finrank_quotient (R := ℝ) (S := ℝ) S
  have hsym := finrank_symSquareSubmodule_eq_six_of_isCompl_line hAL β hxspan
  have hPfin := finrank_spanPairProductsExceptZeroZero_eq_five_of_isCompl_line
    hAL β hxspan
  rw [hSfin, hPfin, hsym] at hquot
  omega

theorem finrank_symSquare_quotient_eq_two_of_eq_spanPairProductsExceptZeroZeroZeroOne
    {A L : Submodule ℝ linSubmodule} (hAL : IsCompl A L)
    (β : Module.Basis (Fin 3) ℝ A) {x : linSubmodule}
    (hxspan : ℝ ∙ x = L) {P : Submodule ℝ quadSubmodule}
    (hP : P = spanPairProductsExceptZeroZeroZeroOne β) :
    Module.finrank ℝ
        (symSquareSubmodule A ⧸
          P.comap (symSquareSubmodule A).subtype) = 2 := by
  subst P
  let S : Submodule ℝ (symSquareSubmodule A) :=
    (spanPairProductsExceptZeroZeroZeroOne β).comap
      (symSquareSubmodule A).subtype
  have hle := spanPairProductsExceptZeroZeroZeroOne_le_symSquareSubmodule β
  have hSfin :
      Module.finrank ℝ S =
        Module.finrank ℝ (spanPairProductsExceptZeroZeroZeroOne β) := by
    exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  have hquot := Submodule.finrank_quotient (R := ℝ) (S := ℝ) S
  have hsym := finrank_symSquareSubmodule_eq_six_of_isCompl_line hAL β hxspan
  have hPfin :=
    finrank_spanPairProductsExceptZeroZeroZeroOne_eq_four_of_isCompl_line
      hAL β hxspan
  rw [hSfin, hPfin, hsym] at hquot
  omega

theorem finrank_linQuadProductSubmodule_quotient_le_one_of_eq_spanPairProductsExceptZeroZero
    {A L : Submodule ℝ linSubmodule} (hAL : IsCompl A L)
    (β : Module.Basis (Fin 3) ℝ A) {x : linSubmodule}
    (hxspan : ℝ ∙ x = L) {P : Submodule ℝ quadSubmodule}
    (hP : P = spanPairProductsExceptZeroZero β) :
    Module.finrank ℝ
        (linQuadProductSubmodule A (symSquareSubmodule A) ⧸
          (linQuadProductSubmodule A P).comap
            (linQuadProductSubmodule A (symSquareSubmodule A)).subtype) ≤ 1 := by
  subst P
  let F := linQuadProductSubmodule A (symSquareSubmodule A)
  let G := linQuadProductSubmodule A (spanPairProductsExceptZeroZero β)
  have hleG : G ≤ F := by
    exact linQuadProductSubmodule_mono le_rfl
      (spanPairProductsExceptZeroZero_le_symSquareSubmodule β)
  let S : Submodule ℝ F := G.comap F.subtype
  have hSfin : Module.finrank ℝ S = Module.finrank ℝ G := by
    exact (Submodule.comapSubtypeEquivOfLe hleG).finrank_eq
  have hFfin := finrank_linQuadProductSubmodule_symSquare_eq_ten_of_isCompl_line
    hAL β hxspan
  have hGfin :=
    nine_le_finrank_linQuadProductSubmodule_exceptZeroZero_of_isCompl_line
      hAL β hxspan
  have hGfin' : 9 ≤ Module.finrank ℝ G := by
    simpa [G] using hGfin
  change Module.finrank ℝ (F ⧸ S) ≤ 1
  rw [Submodule.finrank_quotient, hSfin, hFfin]
  omega

theorem finrank_linQuadProductSubmodule_quotient_le_two_of_eq_spanPairProductsExceptZeroZeroZeroOne
    {A L : Submodule ℝ linSubmodule} (hAL : IsCompl A L)
    (β : Module.Basis (Fin 3) ℝ A) {x : linSubmodule}
    (hxspan : ℝ ∙ x = L) {P : Submodule ℝ quadSubmodule}
    (hP : P = spanPairProductsExceptZeroZeroZeroOne β) :
    Module.finrank ℝ
        (linQuadProductSubmodule A (symSquareSubmodule A) ⧸
          (linQuadProductSubmodule A P).comap
            (linQuadProductSubmodule A (symSquareSubmodule A)).subtype) ≤ 2 := by
  subst P
  let F := linQuadProductSubmodule A (symSquareSubmodule A)
  let G := linQuadProductSubmodule A (spanPairProductsExceptZeroZeroZeroOne β)
  have hleG : G ≤ F := by
    exact linQuadProductSubmodule_mono le_rfl
      (spanPairProductsExceptZeroZeroZeroOne_le_symSquareSubmodule β)
  let S : Submodule ℝ F := G.comap F.subtype
  have hSfin : Module.finrank ℝ S = Module.finrank ℝ G := by
    exact (Submodule.comapSubtypeEquivOfLe hleG).finrank_eq
  have hFfin := finrank_linQuadProductSubmodule_symSquare_eq_ten_of_isCompl_line
    hAL β hxspan
  have hGfin :=
    eight_le_finrank_linQuadProductSubmodule_exceptZeroZeroZeroOne_of_isCompl_line
      hAL β hxspan
  have hGfin' : 8 ≤ Module.finrank ℝ G := by
    simpa [G] using hGfin
  change Module.finrank ℝ (F ⧸ S) ≤ 2
  rw [Submodule.finrank_quotient, hSfin, hFfin]
  omega

theorem macaulay_cokernel_bound_of_eq_spanPairProductsExceptZeroZero
    {A L : Submodule ℝ linSubmodule} (hAL : IsCompl A L)
    (β : Module.Basis (Fin 3) ℝ A) {x : linSubmodule}
    (hxspan : ℝ ∙ x = L) {P : Submodule ℝ quadSubmodule}
    (hP : P = spanPairProductsExceptZeroZero β) :
    Module.finrank ℝ
        (linQuadProductSubmodule A (symSquareSubmodule A) ⧸
          (linQuadProductSubmodule A P).comap
            (linQuadProductSubmodule A (symSquareSubmodule A)).subtype) ≤
      Module.finrank ℝ
        (symSquareSubmodule A ⧸
          P.comap (symSquareSubmodule A).subtype) := by
  have hcubic :=
    finrank_linQuadProductSubmodule_quotient_le_one_of_eq_spanPairProductsExceptZeroZero
      hAL β hxspan hP
  have hquad :=
    finrank_symSquare_quotient_eq_one_of_eq_spanPairProductsExceptZeroZero
      hAL β hxspan hP
  omega

theorem macaulay_cokernel_bound_of_eq_spanPairProductsExceptZeroZeroZeroOne
    {A L : Submodule ℝ linSubmodule} (hAL : IsCompl A L)
    (β : Module.Basis (Fin 3) ℝ A) {x : linSubmodule}
    (hxspan : ℝ ∙ x = L) {P : Submodule ℝ quadSubmodule}
    (hP : P = spanPairProductsExceptZeroZeroZeroOne β) :
    Module.finrank ℝ
        (linQuadProductSubmodule A (symSquareSubmodule A) ⧸
          (linQuadProductSubmodule A P).comap
            (linQuadProductSubmodule A (symSquareSubmodule A)).subtype) ≤
      Module.finrank ℝ
        (symSquareSubmodule A ⧸
          P.comap (symSquareSubmodule A).subtype) := by
  have hcubic :=
    finrank_linQuadProductSubmodule_quotient_le_two_of_eq_spanPairProductsExceptZeroZeroZeroOne
      hAL β hxspan hP
  have hquad :=
    finrank_symSquare_quotient_eq_two_of_eq_spanPairProductsExceptZeroZeroZeroOne
      hAL β hxspan hP
  omega

theorem finrank_linQuadProductSubmodule_quotient_mono
    {A : Submodule ℝ linSubmodule} {P Q : Submodule ℝ quadSubmodule}
    (hPQ : P ≤ Q) (hQ_le : Q ≤ symSquareSubmodule A) :
    Module.finrank ℝ
        (linQuadProductSubmodule A (symSquareSubmodule A) ⧸
          (linQuadProductSubmodule A Q).comap
            (linQuadProductSubmodule A (symSquareSubmodule A)).subtype) ≤
      Module.finrank ℝ
        (linQuadProductSubmodule A (symSquareSubmodule A) ⧸
          (linQuadProductSubmodule A P).comap
            (linQuadProductSubmodule A (symSquareSubmodule A)).subtype) := by
  let F := linQuadProductSubmodule A (symSquareSubmodule A)
  let GP := linQuadProductSubmodule A P
  let GQ := linQuadProductSubmodule A Q
  have hP_le : P ≤ symSquareSubmodule A := le_trans hPQ hQ_le
  have hGP_le_F : GP ≤ F := by
    exact linQuadProductSubmodule_mono le_rfl hP_le
  have hGQ_le_F : GQ ≤ F := by
    exact linQuadProductSubmodule_mono le_rfl hQ_le
  have hGP_le_GQ : GP ≤ GQ := by
    exact linQuadProductSubmodule_mono le_rfl hPQ
  let SP : Submodule ℝ F := GP.comap F.subtype
  let SQ : Submodule ℝ F := GQ.comap F.subtype
  have hSPfin : Module.finrank ℝ SP = Module.finrank ℝ GP := by
    exact (Submodule.comapSubtypeEquivOfLe hGP_le_F).finrank_eq
  have hSQfin : Module.finrank ℝ SQ = Module.finrank ℝ GQ := by
    exact (Submodule.comapSubtypeEquivOfLe hGQ_le_F).finrank_eq
  have hfin_mono : Module.finrank ℝ GP ≤ Module.finrank ℝ GQ :=
    Submodule.finrank_mono hGP_le_GQ
  change Module.finrank ℝ (F ⧸ SQ) ≤ Module.finrank ℝ (F ⧸ SP)
  rw [Submodule.finrank_quotient, Submodule.finrank_quotient, hSPfin, hSQfin]
  omega

theorem macaulay_cokernel_bound_of_spanPairProductsExceptZeroZero_le_of_quotient_eq_one
    {A L : Submodule ℝ linSubmodule} (hAL : IsCompl A L)
    (β : Module.Basis (Fin 3) ℝ A) {x : linSubmodule}
    (hxspan : ℝ ∙ x = L) {P : Submodule ℝ quadSubmodule}
    (hlex : spanPairProductsExceptZeroZero β ≤ P)
    (hP_le : P ≤ symSquareSubmodule A)
    (hquot :
      Module.finrank ℝ
        (symSquareSubmodule A ⧸
          P.comap (symSquareSubmodule A).subtype) = 1) :
    Module.finrank ℝ
        (linQuadProductSubmodule A (symSquareSubmodule A) ⧸
          (linQuadProductSubmodule A P).comap
            (linQuadProductSubmodule A (symSquareSubmodule A)).subtype) ≤
      Module.finrank ℝ
        (symSquareSubmodule A ⧸
          P.comap (symSquareSubmodule A).subtype) := by
  have hmono :=
    finrank_linQuadProductSubmodule_quotient_mono
      (A := A) hlex hP_le
  have hlex_bound :=
    finrank_linQuadProductSubmodule_quotient_le_one_of_eq_spanPairProductsExceptZeroZero
      hAL β hxspan rfl
  rw [hquot]
  exact hmono.trans hlex_bound

theorem macaulay_cokernel_bound_of_spanPairProductsExceptZeroZeroZeroOne_le_of_quotient_eq_two
    {A L : Submodule ℝ linSubmodule} (hAL : IsCompl A L)
    (β : Module.Basis (Fin 3) ℝ A) {x : linSubmodule}
    (hxspan : ℝ ∙ x = L) {P : Submodule ℝ quadSubmodule}
    (hlex : spanPairProductsExceptZeroZeroZeroOne β ≤ P)
    (hP_le : P ≤ symSquareSubmodule A)
    (hquot :
      Module.finrank ℝ
        (symSquareSubmodule A ⧸
          P.comap (symSquareSubmodule A).subtype) = 2) :
    Module.finrank ℝ
        (linQuadProductSubmodule A (symSquareSubmodule A) ⧸
          (linQuadProductSubmodule A P).comap
            (linQuadProductSubmodule A (symSquareSubmodule A)).subtype) ≤
      Module.finrank ℝ
        (symSquareSubmodule A ⧸
          P.comap (symSquareSubmodule A).subtype) := by
  have hmono :=
    finrank_linQuadProductSubmodule_quotient_mono
      (A := A) hlex hP_le
  have hlex_bound :=
    finrank_linQuadProductSubmodule_quotient_le_two_of_eq_spanPairProductsExceptZeroZeroZeroOne
      hAL β hxspan rfl
  rw [hquot]
  exact hmono.trans hlex_bound

theorem exists_rank_two_adapted_basis
    {A W : Submodule ℝ linSubmodule} (hAW : IsCompl A W)
    (β : Module.Basis (Fin 2) ℝ A) {x y : linSubmodule}
    (hxyspan : Submodule.span ℝ ({x, y} : Set linSubmodule) = W) :
    ∃ β4 : Module.Basis (Fin 4) ℝ linSubmodule,
      (∀ i : Fin 2,
        β4 (Fin.castLE (by norm_num : (2 : ℕ) ≤ 4) i) = (β i).1) ∧
        β4 ⟨2, by norm_num⟩ = x ∧
          β4 ⟨3, by norm_num⟩ = y := by
  let v : Fin 4 → linSubmodule := fun i =>
    if h : i.1 < 2 then (β ⟨i.1, h⟩).1 else if i.1 = 2 then x else y
  have hv_cast :
      ∀ i : Fin 2,
        v (Fin.castLE (by norm_num : (2 : ℕ) ≤ 4) i) = (β i).1 := by
    intro i
    fin_cases i <;> simp [v, Fin.castLE]
  have hv_two : v ⟨2, by norm_num⟩ = x := by
    simp [v]
  have hv_three : v ⟨3, by norm_num⟩ = y := by
    simp [v]
  have hA_le : A ≤ Submodule.span ℝ (Set.range v) := by
    intro a ha
    let aA : A := ⟨a, ha⟩
    have hrepr := β.sum_repr aA
    have hsum : (∑ i : Fin 2, β.repr aA i • (β i).1) = a := by
      change (fun z : A => (z : linSubmodule))
          (∑ i : Fin 2, β.repr aA i • β i) = (a : linSubmodule)
      exact congrArg (fun z : A => (z : linSubmodule)) hrepr
    rw [← hsum]
    refine Submodule.sum_mem _ ?_
    intro i _hi
    refine Submodule.smul_mem _ _ ?_
    rw [← hv_cast i]
    exact Submodule.subset_span
      ⟨Fin.castLE (by norm_num : (2 : ℕ) ≤ 4) i, rfl⟩
  have hW_le : W ≤ Submodule.span ℝ (Set.range v) := by
    rw [← hxyspan]
    refine Submodule.span_le.mpr ?_
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · rw [← hv_two]
      exact Submodule.subset_span ⟨⟨2, by norm_num⟩, rfl⟩
    · rw [← hv_three]
      exact Submodule.subset_span ⟨⟨3, by norm_num⟩, rfl⟩
  have htop_le : ⊤ ≤ Submodule.span ℝ (Set.range v) := by
    have hsup_le : A ⊔ W ≤ Submodule.span ℝ (Set.range v) := sup_le hA_le hW_le
    simpa [hAW.codisjoint.eq_top] using hsup_le
  have hLI : LinearIndependent ℝ v :=
    linearIndependent_of_top_le_span_of_card_eq_finrank htop_le (by
      rw [Fintype.card_fin, finrank_linSubmodule_eq_four])
  let β4 : Module.Basis (Fin 4) ℝ linSubmodule := Module.Basis.mk hLI htop_le
  refine ⟨β4, ?_, ?_, ?_⟩
  · intro i
    rw [show β4 (Fin.castLE (by norm_num : (2 : ℕ) ≤ 4) i) =
        v (Fin.castLE (by norm_num : (2 : ℕ) ≤ 4) i) by
      exact Module.Basis.mk_apply hLI htop_le
        (Fin.castLE (by norm_num : (2 : ℕ) ≤ 4) i)]
    exact hv_cast i
  · rw [show β4 ⟨2, by norm_num⟩ = v ⟨2, by norm_num⟩ by
      exact Module.Basis.mk_apply hLI htop_le ⟨2, by norm_num⟩]
    exact hv_two
  · rw [show β4 ⟨3, by norm_num⟩ = v ⟨3, by norm_num⟩ by
      exact Module.Basis.mk_apply hLI htop_le ⟨3, by norm_num⟩]
    exact hv_three

theorem linearIndependent_rank_two_combined_products_of_isCompl
    {A W : Submodule ℝ linSubmodule} (hAW : IsCompl A W)
    (β : Module.Basis (Fin 2) ℝ A) {z y : linSubmodule}
    (hzyspan : Submodule.span ℝ ({z, y} : Set linSubmodule) = W) :
    LinearIndependent ℝ
      (Sum.elim
        (fun i : Fin 2 => linProduct z (β i).1)
        (fun ij : {ij : Fin 2 × Fin 2 // ij.1 ≤ ij.2} =>
          linProduct (β ij.1.1).1 (β ij.1.2).1)) := by
  rcases exists_rank_two_adapted_basis hAW β hzyspan with
    ⟨β4, hβA, hβz, _hβy⟩
  let cast2 : Fin 2 → Fin 4 := Fin.castLE (by norm_num : (2 : ℕ) ≤ 4)
  let two : Fin 4 := ⟨2, by norm_num⟩
  let Pair2 := {ij : Fin 2 × Fin 2 // ij.1 ≤ ij.2}
  let Pair4 := {ij : Fin 4 × Fin 4 // ij.1 ≤ ij.2}
  let φ : (Fin 2 ⊕ Pair2) → Pair4 :=
    Sum.elim
      (fun i : Fin 2 => ⟨(cast2 i, two), by simp [cast2, two, Fin.le_def]⟩)
      (fun ij : Pair2 =>
        ⟨(cast2 ij.1.1, cast2 ij.1.2), by
          simpa [cast2] using
            (Fin.castLE_le_castLE_iff (by norm_num : (2 : ℕ) ≤ 4)).mpr ij.2⟩)
  have hφinj : Function.Injective φ := by
    intro a b h
    cases a with
    | inl i =>
        cases b with
        | inl j =>
            have hp := congrArg Subtype.val h
            have hi : cast2 i = cast2 j := congrArg Prod.fst hp
            have hival : i.1 = j.1 := by
              simpa [cast2, Fin.ext_iff] using congrArg Fin.val hi
            exact congrArg Sum.inl (Fin.ext hival)
        | inr ij =>
            have hp := congrArg Subtype.val h
            have hsec : two = cast2 ij.1.2 := congrArg Prod.snd hp
            have hval := congrArg Fin.val hsec
            have hlt : (ij.1.2).1 < 2 := ij.1.2.2
            simp [two, cast2] at hval
            omega
    | inr ij =>
        cases b with
        | inl j =>
            have hp := congrArg Subtype.val h
            have hsec : cast2 ij.1.2 = two := congrArg Prod.snd hp
            have hval := congrArg Fin.val hsec
            have hlt : (ij.1.2).1 < 2 := ij.1.2.2
            simp [two, cast2] at hval
            omega
        | inr kl =>
            have hp := congrArg Subtype.val h
            have hfst : cast2 ij.1.1 = cast2 kl.1.1 := congrArg Prod.fst hp
            have hsnd : cast2 ij.1.2 = cast2 kl.1.2 := congrArg Prod.snd hp
            have hfstv : ij.1.1.1 = kl.1.1.1 := by
              simpa [cast2, Fin.ext_iff] using congrArg Fin.val hfst
            have hsndv : ij.1.2.1 = kl.1.2.1 := by
              simpa [cast2, Fin.ext_iff] using congrArg Fin.val hsnd
            have hij : ij.1 = kl.1 :=
              Prod.ext (Fin.ext hfstv) (Fin.ext hsndv)
            exact congrArg Sum.inr (Subtype.ext hij)
  have hsub := (linearIndependent_basis_products_fin_four β4).comp φ hφinj
  let target : (Fin 2 ⊕ Pair2) → quadSubmodule :=
    Sum.elim
      (fun i : Fin 2 => linProduct z (β i).1)
      (fun ij : Pair2 => linProduct (β ij.1.1).1 (β ij.1.2).1)
  let pulled : (Fin 2 ⊕ Pair2) → quadSubmodule :=
    fun t => linProduct (β4 (φ t).1.1) (β4 (φ t).1.2)
  have htwo : β4 (2 : Fin 4) = z := by
    simpa [two] using hβz
  have hpulled : pulled = target := by
    funext t
    cases t with
    | inl i =>
        dsimp [pulled, target, φ, cast2, two]
        rw [hβA i, htwo, linProduct_comm]
    | inr ij =>
        dsimp [pulled, target, φ, cast2]
        rw [hβA ij.1.1, hβA ij.1.2]
  change LinearIndependent ℝ pulled at hsub
  change LinearIndependent ℝ target
  exact hpulled ▸ hsub

theorem linProduct_mem_sup_of_isCompl
    {A W : Submodule ℝ linSubmodule} (hAW : IsCompl A W)
    (x y : linSubmodule) :
    linProduct x y ∈ linProductSubmodule A ⊤ ⊔ linProductSubmodule W W := by
  have hxAW : x ∈ A ⊔ W := by
    rw [hAW.codisjoint.eq_top]
    trivial
  have hyAW : y ∈ A ⊔ W := by
    rw [hAW.codisjoint.eq_top]
    trivial
  rcases Submodule.mem_sup.mp hxAW with ⟨xA, hxA, xW, hxW, hxeq⟩
  rcases Submodule.mem_sup.mp hyAW with ⟨yA, hyA, yW, hyW, hyeq⟩
  subst x
  subst y
  have hAA : linProduct xA yA ∈ linProductSubmodule A ⊤ := by
    exact linProduct_mem_linProductSubmodule
      (⟨xA, hxA⟩ : A) (⟨yA, trivial⟩ : (⊤ : Submodule ℝ linSubmodule))
  have hAWprod : linProduct xA yW ∈ linProductSubmodule A ⊤ := by
    exact linProduct_mem_linProductSubmodule
      (⟨xA, hxA⟩ : A) (⟨yW, trivial⟩ : (⊤ : Submodule ℝ linSubmodule))
  have hWAprod : linProduct xW yA ∈ linProductSubmodule A ⊤ := by
    rw [linProduct_comm]
    exact linProduct_mem_linProductSubmodule
      (⟨yA, hyA⟩ : A) (⟨xW, trivial⟩ : (⊤ : Submodule ℝ linSubmodule))
  have hWW : linProduct xW yW ∈ linProductSubmodule W W := by
    exact linProduct_mem_linProductSubmodule (⟨xW, hxW⟩ : W) (⟨yW, hyW⟩ : W)
  have hsum :
      linProduct xA yA + linProduct xA yW + linProduct xW yA + linProduct xW yW ∈
        linProductSubmodule A ⊤ ⊔ linProductSubmodule W W := by
    repeat' first
      | apply Submodule.add_mem
      | exact Submodule.mem_sup_left hAA
      | exact Submodule.mem_sup_left hAWprod
      | exact Submodule.mem_sup_left hWAprod
      | exact Submodule.mem_sup_right hWW
  simpa [add_assoc, add_left_comm, add_comm] using hsum

theorem linProductSubmodule_top_top_le_sup_of_isCompl
    {A W : Submodule ℝ linSubmodule} (hAW : IsCompl A W) :
    linProductSubmodule (⊤ : Submodule ℝ linSubmodule) ⊤ ≤
      linProductSubmodule A ⊤ ⊔ linProductSubmodule W W := by
  refine linProductSubmodule_le_of_generators ?_
  intro x y
  exact linProduct_mem_sup_of_isCompl hAW x.1 y.1

theorem sup_linProductSubmodule_eq_top_of_isCompl
    {A W : Submodule ℝ linSubmodule} (hAW : IsCompl A W) :
    linProductSubmodule A ⊤ ⊔ linProductSubmodule W W = ⊤ := by
  rw [← linProductSubmodule_top_top_eq_top]
  refine le_antisymm ?_ (linProductSubmodule_top_top_le_sup_of_isCompl hAW)
  exact sup_le
    (linProductSubmodule_mono le_top le_rfl)
    (linProductSubmodule_mono le_top le_top)

theorem exists_linProduct_decomposition_of_isCompl
    {A W : Submodule ℝ linSubmodule} (hAW : IsCompl A W)
    (q : quadSubmodule) :
    ∃ qA qW : quadSubmodule,
      qA ∈ linProductSubmodule A ⊤ ∧
        qW ∈ linProductSubmodule W W ∧
          q = qW + qA := by
  have hq :
      q ∈ linProductSubmodule A ⊤ ⊔ linProductSubmodule W W := by
    rw [sup_linProductSubmodule_eq_top_of_isCompl hAW]
    trivial
  rcases Submodule.mem_sup.mp hq with ⟨qA, hqA, qW, hqW, hsum⟩
  exact ⟨qA, qW, hqA, hqW, by rw [← hsum, add_comm]⟩

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

theorem range_linProductLeftMapOn_eq_span_basis_products
    {a : linSubmodule} {A : Submodule ℝ linSubmodule}
    {ι : Type*} (β : Module.Basis ι ℝ A) :
    LinearMap.range (linProductLeftMapOn a A) =
      Submodule.span ℝ (Set.range fun i : ι => linProduct a (β i).1) := by
  rw [← Submodule.map_top]
  rw [← β.span_eq]
  rw [Submodule.map_span]
  congr
  ext q
  constructor
  · rintro ⟨b, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨β i, ⟨i, rfl⟩, rfl⟩

theorem range_linProductLeftMapOn_inf_symSquare_eq_bot_of_basis_products_linearIndependent
    {A : Submodule ℝ linSubmodule} {z : linSubmodule}
    (β : Module.Basis (Fin 2) ℝ A)
    (hLI :
      LinearIndependent ℝ
        (Sum.elim
          (fun i : Fin 2 => linProduct z (β i).1)
          (fun ij : {ij : Fin 2 × Fin 2 // ij.1 ≤ ij.2} =>
            linProduct (β ij.1.1).1 (β ij.1.2).1))) :
    LinearMap.range (linProductLeftMapOn z A) ⊓ symSquareSubmodule A = ⊥ := by
  let f : Fin 2 → quadSubmodule := fun i => linProduct z (β i).1
  let g : {ij : Fin 2 × Fin 2 // ij.1 ≤ ij.2} → quadSubmodule :=
    fun ij => linProduct (β ij.1.1).1 (β ij.1.2).1
  have hrange :
      LinearMap.range (linProductLeftMapOn z A) =
        Submodule.span ℝ (Set.range f) := by
    simpa [f] using range_linProductLeftMapOn_eq_span_basis_products
      (a := z) (A := A) β
  have hsym :
      symSquareSubmodule A = Submodule.span ℝ (Set.range g) := by
    apply le_antisymm
    · refine linProductSubmodule_le_of_generators ?_
      intro a b
      have hrepr :=
        LinearMap.sum_repr_mul_repr_mul
          (b₁' := β) (b₂' := β) (B := linProductBilinOn A) a b
      change ((linProductBilinOn A) a) b ∈ Submodule.span ℝ (Set.range g)
      rw [← hrepr]
      rw [Finsupp.sum_fintype]
      swap
      · simp
      refine Submodule.sum_mem _ ?_
      intro i _hi
      rw [Finsupp.sum_fintype]
      swap
      · simp
      refine Submodule.sum_mem _ ?_
      intro j _hj
      refine Submodule.smul_mem _ _ ?_
      refine Submodule.smul_mem _ _ ?_
      change linProduct (β i).1 (β j).1 ∈ Submodule.span ℝ (Set.range g)
      by_cases hij : i ≤ j
      · exact Submodule.subset_span ⟨⟨(i, j), hij⟩, rfl⟩
      · have hji : j ≤ i := le_of_not_ge hij
        rw [linProduct_comm]
        exact Submodule.subset_span ⟨⟨(j, i), hji⟩, rfl⟩
    · refine Submodule.span_le.mpr ?_
      rintro q ⟨ij, rfl⟩
      exact linProduct_mem_linProductSubmodule
        (⟨(β ij.1.1).1, (β ij.1.1).2⟩ : A)
        (⟨(β ij.1.2).1, (β ij.1.2).2⟩ : A)
  rw [hrange, hsym]
  exact inf_span_ranges_eq_bot_of_linearIndependent_sum
    (K := ℝ) (V := quadSubmodule) hLI

theorem finrank_range_linProductLeftMapOn_le
    (a : linSubmodule) (A : Submodule ℝ linSubmodule) :
    Module.finrank ℝ (LinearMap.range (linProductLeftMapOn a A)) ≤
      Module.finrank ℝ A :=
  LinearMap.finrank_range_le (linProductLeftMapOn a A)

theorem finrank_range_linProductLeftMapOn_le_two
    {a : linSubmodule} {A : Submodule ℝ linSubmodule}
    (hA : Module.finrank ℝ A ≤ 2) :
    Module.finrank ℝ (LinearMap.range (linProductLeftMapOn a A)) ≤ 2 :=
  (finrank_range_linProductLeftMapOn_le a A).trans hA

theorem finrank_range_linProductLeftMapOn_le_three
    {a : linSubmodule} {A : Submodule ℝ linSubmodule}
    (hA : Module.finrank ℝ A ≤ 3) :
    Module.finrank ℝ (LinearMap.range (linProductLeftMapOn a A)) ≤ 3 :=
  (finrank_range_linProductLeftMapOn_le a A).trans hA

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

theorem linProductLeftPreimageOn_ne_bot_of_finrank_le_lt_add
    {a : linSubmodule} {A : Submodule ℝ linSubmodule}
    {P W : Submodule ℝ quadSubmodule}
    (ha : (a : Poly) ≠ 0)
    (hPW : P ≤ W)
    (hrangeW : LinearMap.range (linProductLeftMapOn a A) ≤ W)
    {pdim adim wdim : ℕ}
    (hPdim : pdim ≤ Module.finrank ℝ P)
    (hAdim : adim ≤ Module.finrank ℝ A)
    (hWdim : Module.finrank ℝ W ≤ wdim)
    (hgt : wdim < pdim + adim) :
    linProductLeftPreimageOn a A P ≠ ⊥ :=
  linProductLeftPreimageOn_ne_bot_of_finrank_lt_add
    ha hPW hrangeW hPdim hAdim rfl (lt_of_le_of_lt hWdim hgt)

theorem linProductLeftPreimageWithin_ne_bot_of_finrank_le_lt_add
    {a : linSubmodule} {A : Submodule ℝ linSubmodule}
    {P W : Submodule ℝ quadSubmodule}
    (ha : (a : Poly) ≠ 0)
    (hPW : P ≤ W)
    (hrangeW : LinearMap.range (linProductLeftMapOn a A) ≤ W)
    {pdim adim wdim : ℕ}
    (hPdim : pdim ≤ Module.finrank ℝ P)
    (hAdim : adim ≤ Module.finrank ℝ A)
    (hWdim : Module.finrank ℝ W ≤ wdim)
    (hgt : wdim < pdim + adim) :
    linProductLeftPreimageWithin a A P ≠ ⊥ :=
  linProductLeftPreimageWithin_ne_bot_of_on_ne_bot
    (linProductLeftPreimageOn_ne_bot_of_finrank_le_lt_add
      ha hPW hrangeW hPdim hAdim hWdim hgt)

def supportAmbient (x : linSubmodule) (A : Submodule ℝ linSubmodule) :
    Submodule ℝ quadSubmodule :=
  LinearMap.range (linProductLeftMapOn x A) ⊔ symSquareSubmodule A

theorem range_linProductLeftMapOn_le_supportAmbient
    (x : linSubmodule) (A : Submodule ℝ linSubmodule) :
    LinearMap.range (linProductLeftMapOn x A) ≤ supportAmbient x A :=
  le_sup_left

theorem symSquareSubmodule_le_supportAmbient
    (x : linSubmodule) (A : Submodule ℝ linSubmodule) :
    symSquareSubmodule A ≤ supportAmbient x A :=
  le_sup_right

theorem finrank_supportAmbient_le_of_bounds
    {x : linSubmodule} {A : Submodule ℝ linSubmodule} {m n c : ℕ}
    (hrange : Module.finrank ℝ (LinearMap.range (linProductLeftMapOn x A)) ≤ m)
    (hsym : Module.finrank ℝ (symSquareSubmodule A) ≤ n)
    (hmn : m + n ≤ c) :
    Module.finrank ℝ (supportAmbient x A) ≤ c :=
  finrank_sup_le_of_le_add
    (K := ℝ) (V := quadSubmodule)
    (s := LinearMap.range (linProductLeftMapOn x A)) (t := symSquareSubmodule A)
    hrange hsym hmn

theorem finrank_supportAmbient_le_five
    {x : linSubmodule} {A : Submodule ℝ linSubmodule}
    (hrange : Module.finrank ℝ (LinearMap.range (linProductLeftMapOn x A)) ≤ 2)
    (hsym : Module.finrank ℝ (symSquareSubmodule A) ≤ 3) :
    Module.finrank ℝ (supportAmbient x A) ≤ 5 :=
  finrank_supportAmbient_le_of_bounds
    (x := x) (A := A) (m := 2) (n := 3) (c := 5)
    hrange hsym (by norm_num)

theorem finrank_supportAmbient_le_five_of_finrank_eq_two
    {x : linSubmodule} {A : Submodule ℝ linSubmodule}
    (hA : Module.finrank ℝ A = 2) :
    Module.finrank ℝ (supportAmbient x A) ≤ 5 :=
  finrank_supportAmbient_le_five
    (x := x) (A := A)
    (finrank_range_linProductLeftMapOn_le_two (a := x) (A := A) (by omega))
    (finrank_symSquareSubmodule_le_three_of_finrank_eq_two hA)

theorem finrank_supportAmbient_le_nine
    {x : linSubmodule} {A : Submodule ℝ linSubmodule}
    (hrange : Module.finrank ℝ (LinearMap.range (linProductLeftMapOn x A)) ≤ 3)
    (hsym : Module.finrank ℝ (symSquareSubmodule A) ≤ 6) :
    Module.finrank ℝ (supportAmbient x A) ≤ 9 :=
  finrank_supportAmbient_le_of_bounds
    (x := x) (A := A) (m := 3) (n := 6) (c := 9)
    hrange hsym (by norm_num)

theorem finrank_supportAmbient_le_nine_of_finrank_eq_three
    {x : linSubmodule} {A : Submodule ℝ linSubmodule}
    (hA : Module.finrank ℝ A = 3) :
    Module.finrank ℝ (supportAmbient x A) ≤ 9 :=
  finrank_supportAmbient_le_nine
    (x := x) (A := A)
    (finrank_range_linProductLeftMapOn_le_three (a := x) (A := A) (by omega))
    (finrank_symSquareSubmodule_le_six_of_finrank_eq_three hA)

theorem linProductSubmodule_leftPreimageWithin_le_symSquare
    (x : linSubmodule) (A : Submodule ℝ linSubmodule)
    (P : Submodule ℝ quadSubmodule) :
    linProductSubmodule (linProductLeftPreimageWithin x A P) A ≤
      symSquareSubmodule A :=
  linProductSubmodule_mono
    (linProductLeftPreimageWithin_le_left x A P) le_rfl

theorem linProductSubmodule_leftPreimageWithin_le_supportAmbient
    (x : linSubmodule) (A : Submodule ℝ linSubmodule)
    (P : Submodule ℝ quadSubmodule) :
    linProductSubmodule (linProductLeftPreimageWithin x A P) A ≤
      supportAmbient x A :=
  (linProductSubmodule_leftPreimageWithin_le_symSquare x A P).trans
    (symSquareSubmodule_le_supportAmbient x A)

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

theorem ker_catalecticantMap_le_flip_ker
    (B : DotForm) (p : Poly) (u : RankSevenVec) :
    LinearMap.ker (catalecticantMap B p u) ≤
      LinearMap.ker (catalecticantMap B p u).flip := by
  intro q hq
  rw [LinearMap.mem_ker]
  ext r
  change catalecticantMap B p u r q = 0
  rw [catalecticantMap_pair_comm]
  exact congrArg (fun φ : Module.Dual ℝ quadSubmodule => φ r)
    (by simpa [LinearMap.mem_ker] using hq)

def quotientCatalecticantMap (B : DotForm) (p : Poly) (u : RankSevenVec) :
    (quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u)) →ₗ[ℝ]
      Module.Dual ℝ
        (quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u)) :=
  LinearMap.liftQ₂
    (LinearMap.ker (catalecticantMap B p u))
    (LinearMap.ker (catalecticantMap B p u))
    (catalecticantMap B p u)
    le_rfl
    (ker_catalecticantMap_le_flip_ker B p u)

@[simp] theorem quotientCatalecticantMap_mk
    (B : DotForm) (p : Poly) (u : RankSevenVec)
    (q r : quadSubmodule) :
    quotientCatalecticantMap B p u
        ((LinearMap.ker (catalecticantMap B p u)).mkQ q)
        ((LinearMap.ker (catalecticantMap B p u)).mkQ r) =
      catalecticantMap B p u q r := by
  rfl

theorem quotientCatalecticantMap_pair_comm
    (B : DotForm) (p : Poly) (u : RankSevenVec)
    (q r :
      quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u)) :
    quotientCatalecticantMap B p u q r =
      quotientCatalecticantMap B p u r q := by
  induction q using Submodule.Quotient.induction_on with
  | _ q' =>
      induction r using Submodule.Quotient.induction_on with
      | _ r' =>
          change catalecticantMap B p u q' r' = catalecticantMap B p u r' q'
          rw [catalecticantMap_pair_comm]

theorem ker_quotientCatalecticantMap_eq_bot
    (B : DotForm) (p : Poly) (u : RankSevenVec) :
    LinearMap.ker (quotientCatalecticantMap B p u) = ⊥ := by
  ext q
  constructor
  · intro hq
    induction q using Submodule.Quotient.induction_on with
    | _ q' =>
        have hmap : catalecticantMap B p u q' = 0 := by
          ext r
          have hzero :
              quotientCatalecticantMap B p u
                  ((LinearMap.ker (catalecticantMap B p u)).mkQ q') = 0 := by
            simpa [LinearMap.mem_ker] using hq
          have hval := congrArg
            (fun φ :
              Module.Dual ℝ
                (quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u)) =>
              φ ((LinearMap.ker (catalecticantMap B p u)).mkQ r)) hzero
          simpa using hval
        have hq' : q' ∈ LinearMap.ker (catalecticantMap B p u) := by
          simpa [LinearMap.mem_ker] using hmap
        simpa [Submodule.Quotient.mk_eq_zero] using hq'
  · intro hq
    have hqzero : q = 0 := by
      simpa using hq
    rw [LinearMap.mem_ker, hqzero]
    simp

theorem finrank_range_quotientCatalecticantMap_eq_finrank_quotient
    (B : DotForm) (p : Poly) (u : RankSevenVec) :
    Module.finrank ℝ (LinearMap.range (quotientCatalecticantMap B p u)) =
      Module.finrank ℝ
        (quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u)) := by
  have hsum := LinearMap.finrank_range_add_finrank_ker
    (quotientCatalecticantMap B p u)
  rw [ker_quotientCatalecticantMap_eq_bot] at hsum
  simp at hsum
  omega

theorem range_quotientCatalecticantMap_eq_top
    (B : DotForm) (p : Poly) (u : RankSevenVec) :
    LinearMap.range (quotientCatalecticantMap B p u) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [finrank_range_quotientCatalecticantMap_eq_finrank_quotient,
    Subspace.dual_finrank_eq]

theorem quotientCatalecticantMap_linearProducts_reassociate
    (B : DotForm) (p : Poly) (u : RankSevenVec)
    (w x y z : linSubmodule) :
    quotientCatalecticantMap B p u
        ((LinearMap.ker (catalecticantMap B p u)).mkQ (linProduct w x))
        ((LinearMap.ker (catalecticantMap B p u)).mkQ (linProduct y z)) =
      quotientCatalecticantMap B p u
        ((LinearMap.ker (catalecticantMap B p u)).mkQ (linProduct w y))
        ((LinearMap.ker (catalecticantMap B p u)).mkQ (linProduct x z)) := by
  change B ((linProduct w x : quadSubmodule).1 *
      (linProduct y z : quadSubmodule).1) (residual p u) =
    B ((linProduct w y : quadSubmodule).1 *
      (linProduct x z : quadSubmodule).1) (residual p u)
  simp [linProduct, mul_comm, mul_left_comm]

theorem catalecticantMap_eq_zero_of_residual_eq_zero
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hres : residual p u = 0) :
    catalecticantMap B p u = 0 := by
  ext q r
  simp [hres]

theorem finrank_range_catalecticantMap_eq_zero_of_residual_eq_zero
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hres : residual p u = 0) :
    Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 0 := by
  rw [catalecticantMap_eq_zero_of_residual_eq_zero hres]
  simp

theorem residual_ne_zero_of_catalecticantMap_rank_pos
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hrank : 0 < Module.finrank ℝ (LinearMap.range (catalecticantMap B p u))) :
    residual p u ≠ 0 := by
  intro hres
  have hzero :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 0 :=
    finrank_range_catalecticantMap_eq_zero_of_residual_eq_zero hres
  omega

theorem residual_ne_zero_of_catalecticantMap_rank_eq_one
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1) :
    residual p u ≠ 0 :=
  residual_ne_zero_of_catalecticantMap_rank_pos (by
    rw [hrank]
    norm_num)

theorem residual_ne_zero_of_catalecticantMap_rank_eq_two
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2) :
    residual p u ≠ 0 :=
  residual_ne_zero_of_catalecticantMap_rank_pos (by
    rw [hrank]
    norm_num)

theorem residual_ne_zero_of_catalecticantMap_rank_eq_three
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3) :
    residual p u ≠ 0 :=
  residual_ne_zero_of_catalecticantMap_rank_pos (by
    rw [hrank]
    norm_num)

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

theorem residualEval_sq_add_eq_of_mem_ker_catalecticantMap
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (q k : quadSubmodule)
    (hk : k ∈ LinearMap.ker (catalecticantMap B p u)) :
    B ((q.1 + k.1)^2) (residual p u) =
      B (q.1^2) (residual p u) := by
  have hkq : B (k.1 * q.1) (residual p u) = 0 := by
    have hmap : catalecticantMap B p u k = 0 := hk
    have hval := congrArg (fun φ : Module.Dual ℝ quadSubmodule => φ q) hmap
    simpa using hval
  have hkk : B (k.1 * k.1) (residual p u) = 0 := by
    have hmap : catalecticantMap B p u k = 0 := hk
    have hval := congrArg (fun φ : Module.Dual ℝ quadSubmodule => φ k) hmap
    simpa using hval
  have hpoly :
      (q.1 + k.1)^2 = q.1^2 + k.1 * q.1 + k.1 * q.1 + k.1^2 := by
    ring
  rw [hpoly]
  simp [hkq, hkk, pow_two]

theorem residualEval_sq_lt_of_add_mem_ker_catalecticantMap
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (q k : quadSubmodule)
    (hk : k ∈ LinearMap.ker (catalecticantMap B p u))
    (hneg : B ((q.1 + k.1)^2) (residual p u) < 0) :
    B (q.1^2) (residual p u) < 0 := by
  rwa [residualEval_sq_add_eq_of_mem_ker_catalecticantMap
    (B := B) (p := p) (u := u) q k hk] at hneg

theorem residualEval_sq_eq_of_eq_add_mem_ker_catalecticantMap
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {q qW qK : quadSubmodule}
    (hdecomp : q = qW + qK)
    (hK : qK ∈ LinearMap.ker (catalecticantMap B p u)) :
    B (q.1^2) (residual p u) =
      B (qW.1^2) (residual p u) := by
  subst q
  exact residualEval_sq_add_eq_of_mem_ker_catalecticantMap
    (B := B) (p := p) (u := u) qW qK hK

theorem residualEval_sq_lt_of_eq_add_mem_ker_catalecticantMap
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {q qW qK : quadSubmodule}
    (hdecomp : q = qW + qK)
    (hK : qK ∈ LinearMap.ker (catalecticantMap B p u))
    (hneg : B (q.1^2) (residual p u) < 0) :
    B (qW.1^2) (residual p u) < 0 := by
  rw [residualEval_sq_eq_of_eq_add_mem_ker_catalecticantMap
    (B := B) (p := p) (u := u) hdecomp hK] at hneg
  exact hneg

theorem residualEval_sq_smul
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (c : ℝ) (q : quadSubmodule) :
    B (((c • q : quadSubmodule).1)^2) (residual p u) =
      c^2 * B (q.1^2) (residual p u) := by
  simp [pow_two, mul_assoc, mul_comm]

theorem finrank_quotient_ker_catalecticantMap_eq_rank
    (B : DotForm) (p : Poly) (u : RankSevenVec) :
    Module.finrank ℝ
        (quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u)) =
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) :=
  (catalecticantMap B p u).quotKerEquivRange.finrank_eq

theorem finrank_range_quotientCatalecticantMap_eq_rank
    (B : DotForm) (p : Poly) (u : RankSevenVec) :
    Module.finrank ℝ (LinearMap.range (quotientCatalecticantMap B p u)) =
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) := by
  rw [finrank_range_quotientCatalecticantMap_eq_finrank_quotient]
  exact finrank_quotient_ker_catalecticantMap_eq_rank B p u

theorem finrank_quotient_ker_catalecticantMap_eq_one_of_rank_one
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1) :
    Module.finrank ℝ
        (quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u)) = 1 := by
  rw [finrank_quotient_ker_catalecticantMap_eq_rank, hrank]

theorem finrank_quotient_ker_catalecticantMap_eq_two_of_rank_two
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2) :
    Module.finrank ℝ
        (quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u)) = 2 := by
  rw [finrank_quotient_ker_catalecticantMap_eq_rank, hrank]

theorem finrank_quotient_ker_catalecticantMap_eq_three_of_rank_three
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3) :
    Module.finrank ℝ
        (quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u)) = 3 := by
  rw [finrank_quotient_ker_catalecticantMap_eq_rank, hrank]

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

theorem finrank_quotient_linearAnnihilator_eq_sub
    (B : DotForm) (p : Poly) (u : RankSevenVec) :
    Module.finrank ℝ (linSubmodule ⧸ linearAnnihilator B p u) =
      4 - Module.finrank ℝ (linearAnnihilator B p u) := by
  rw [Submodule.finrank_quotient, finrank_linSubmodule_eq_four]

theorem finrank_quotient_linearAnnihilator_le_four
    (B : DotForm) (p : Poly) (u : RankSevenVec) :
    Module.finrank ℝ (linSubmodule ⧸ linearAnnihilator B p u) ≤ 4 := by
  rw [finrank_quotient_linearAnnihilator_eq_sub]
  omega

theorem finrank_quotient_linearAnnihilator_eq_four_of_finrank_linearAnnihilator_eq_zero
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hzero : Module.finrank ℝ (linearAnnihilator B p u) = 0) :
    Module.finrank ℝ (linSubmodule ⧸ linearAnnihilator B p u) = 4 := by
  rw [finrank_quotient_linearAnnihilator_eq_sub, hzero]

theorem finrank_linearAnnihilator_eq_zero_of_finrank_quotient_linearAnnihilator_eq_four
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hquot : Module.finrank ℝ (linSubmodule ⧸ linearAnnihilator B p u) = 4) :
    Module.finrank ℝ (linearAnnihilator B p u) = 0 := by
  have hquot_sub := finrank_quotient_linearAnnihilator_eq_sub B p u
  rw [hquot] at hquot_sub
  omega

theorem linearAnnihilator_eq_bot_of_finrank_quotient_linearAnnihilator_eq_four
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hquot : Module.finrank ℝ (linSubmodule ⧸ linearAnnihilator B p u) = 4) :
    linearAnnihilator B p u = ⊥ := by
  exact (Submodule.finrank_eq_zero).mp
    (finrank_linearAnnihilator_eq_zero_of_finrank_quotient_linearAnnihilator_eq_four
      hquot)

@[simp] theorem mem_linearAnnihilator {B : DotForm} {p : Poly} {u : RankSevenVec}
    {a : linSubmodule} :
    a ∈ linearAnnihilator B p u ↔
      ∀ e : linSubmodule,
        linProduct a e ∈ LinearMap.ker (catalecticantMap B p u) :=
  Iff.rfl

def linearAnnihilatorMap (B : DotForm) (p : Poly) (u : RankSevenVec) :
    linSubmodule →ₗ[ℝ]
      linSubmodule →ₗ[ℝ]
        (quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u)) where
  toFun a :=
    { toFun := fun e =>
        (LinearMap.ker (catalecticantMap B p u)).mkQ (linProduct a e)
      map_add' := by
        intro e f
        rw [linProduct_add_right]
        simp
      map_smul' := by
        intro c e
        rw [linProduct_smul_right]
        simp }
  map_add' := by
    intro a b
    ext e
    change (LinearMap.ker (catalecticantMap B p u)).mkQ (linProduct (a + b) e) =
      (LinearMap.ker (catalecticantMap B p u)).mkQ (linProduct a e) +
        (LinearMap.ker (catalecticantMap B p u)).mkQ (linProduct b e)
    rw [linProduct_add_left]
    simp
  map_smul' := by
    intro c a
    ext e
    change (LinearMap.ker (catalecticantMap B p u)).mkQ (linProduct (c • a) e) =
      c • (LinearMap.ker (catalecticantMap B p u)).mkQ (linProduct a e)
    rw [linProduct_smul_left]
    simp

@[simp] theorem linearAnnihilatorMap_apply
    (B : DotForm) (p : Poly) (u : RankSevenVec)
    (a e : linSubmodule) :
    linearAnnihilatorMap B p u a e =
      (LinearMap.ker (catalecticantMap B p u)).mkQ (linProduct a e) :=
  rfl

theorem linearAnnihilator_eq_ker_linearAnnihilatorMap
    (B : DotForm) (p : Poly) (u : RankSevenVec) :
    linearAnnihilator B p u = LinearMap.ker (linearAnnihilatorMap B p u) := by
  ext a
  constructor
  · intro ha
    rw [LinearMap.mem_ker]
    ext e
    simp [ha e]
  · intro ha e
    have happ :
        linearAnnihilatorMap B p u a e = 0 := by
      have hzero : linearAnnihilatorMap B p u a = 0 := by
        simpa [LinearMap.mem_ker] using ha
      rw [hzero]
      simp
    simpa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using happ

theorem finrank_quotient_linearAnnihilator_eq_range_linearAnnihilatorMap
    (B : DotForm) (p : Poly) (u : RankSevenVec) :
    Module.finrank ℝ (linSubmodule ⧸ linearAnnihilator B p u) =
      Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) := by
  rw [linearAnnihilator_eq_ker_linearAnnihilatorMap]
  exact (linearAnnihilatorMap B p u).quotKerEquivRange.finrank_eq

theorem finrank_range_linearAnnihilatorMap_add_finrank_linearAnnihilator
    (B : DotForm) (p : Poly) (u : RankSevenVec) :
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) +
      Module.finrank ℝ (linearAnnihilator B p u) = 4 := by
  rw [linearAnnihilator_eq_ker_linearAnnihilatorMap]
  rw [LinearMap.finrank_range_add_finrank_ker]
  exact finrank_linSubmodule_eq_four

theorem ker_linearAnnihilatorMap_eq_bot_of_finrank_quotient_linearAnnihilator_eq_four
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hquot : Module.finrank ℝ (linSubmodule ⧸ linearAnnihilator B p u) = 4) :
    LinearMap.ker (linearAnnihilatorMap B p u) = ⊥ := by
  rw [← linearAnnihilator_eq_ker_linearAnnihilatorMap]
  exact linearAnnihilator_eq_bot_of_finrank_quotient_linearAnnihilator_eq_four hquot

theorem linearAnnihilatorMap_injective_of_finrank_quotient_linearAnnihilator_eq_four
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hquot : Module.finrank ℝ (linSubmodule ⧸ linearAnnihilator B p u) = 4) :
    Function.Injective (linearAnnihilatorMap B p u) :=
  LinearMap.ker_eq_bot.mp
    (ker_linearAnnihilatorMap_eq_bot_of_finrank_quotient_linearAnnihilator_eq_four
      hquot)

theorem finrank_range_linearAnnihilatorMap_eq_four_of_finrank_quotient_linearAnnihilator_eq_four
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hquot : Module.finrank ℝ (linSubmodule ⧸ linearAnnihilator B p u) = 4) :
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) = 4 := by
  rw [← finrank_quotient_linearAnnihilator_eq_range_linearAnnihilatorMap]
  exact hquot

theorem rankThreeBadBranch_leftMultiplication_finrank_range_pos
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hquot : Module.finrank ℝ (linSubmodule ⧸ linearAnnihilator B p u) = 4)
    {a : linSubmodule} (ha : a ≠ 0) :
    0 < Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u a)) := by
  by_contra hnot
  have hrange_zero :
      Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u a)) = 0 := by
    omega
  have hrange_bot :
      LinearMap.range (linearAnnihilatorMap B p u a) = ⊥ :=
    (Submodule.finrank_eq_zero).mp hrange_zero
  have hmap_zero : linearAnnihilatorMap B p u a = 0 := by
    ext e
    have hmem :
        linearAnnihilatorMap B p u a e ∈
          LinearMap.range (linearAnnihilatorMap B p u a) :=
      LinearMap.mem_range_self _ _
    have hbot :
        linearAnnihilatorMap B p u a e ∈
          (⊥ : Submodule ℝ
            (quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u))) := by
      simpa [hrange_bot] using hmem
    simpa using hbot
  have hker :
      a ∈ LinearMap.ker (linearAnnihilatorMap B p u) := by
    simpa [LinearMap.mem_ker] using hmap_zero
  have hbot :
      a ∈ (⊥ : Submodule ℝ linSubmodule) := by
    simpa [ker_linearAnnihilatorMap_eq_bot_of_finrank_quotient_linearAnnihilator_eq_four
      hquot] using hker
  exact ha (by simpa using hbot)

theorem rankThreeBadBranch_leftMultiplication_finrank_range_le_three
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3)
    (a : linSubmodule) :
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u a)) ≤ 3 := by
  have hcod :
      Module.finrank ℝ
          (quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u)) = 3 :=
    finrank_quotient_ker_catalecticantMap_eq_three_of_rank_three
      (B := B) (p := p) (u := u) hrank
  have hle :
      Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u a)) ≤
        Module.finrank ℝ
          (quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u)) :=
    by
      simpa [finrank_top] using
        (Submodule.finrank_mono
          (show LinearMap.range (linearAnnihilatorMap B p u a) ≤
            (⊤ : Submodule ℝ
              (quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u))) from
            le_top))
  omega

theorem rankThreeBadBranch_leftMultiplication_finrank_range_between
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3)
    (hquot : Module.finrank ℝ (linSubmodule ⧸ linearAnnihilator B p u) = 4)
    {a : linSubmodule} (ha : a ≠ 0) :
    1 ≤ Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u a)) ∧
      Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u a)) ≤ 3 := by
  exact ⟨
    rankThreeBadBranch_leftMultiplication_finrank_range_pos
      (B := B) (p := p) (u := u) hquot ha,
    rankThreeBadBranch_leftMultiplication_finrank_range_le_three
      (B := B) (p := p) (u := u) hrank a⟩

theorem exists_rankThreeBadBranch_leftMultiplication_finrank_range
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3)
    (hquot : Module.finrank ℝ (linSubmodule ⧸ linearAnnihilator B p u) = 4) :
    ∃ (a : linSubmodule) (b : ℕ),
      a ≠ 0 ∧
        Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u a)) = b ∧
          1 ≤ b ∧ b ≤ 3 := by
  have hpos : 0 < Module.finrank ℝ (⊤ : Submodule ℝ linSubmodule) := by
    rw [finrank_top, finrank_linSubmodule_eq_four]
    norm_num
  rcases exists_mem_ne_zero_of_finrank_pos
      (K := ℝ) (V := linSubmodule) (s := ⊤) hpos with
    ⟨a, _ha_top, ha_ne⟩
  refine ⟨a, Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u a)),
    ha_ne, rfl, ?_⟩
  exact rankThreeBadBranch_leftMultiplication_finrank_range_between
    (B := B) (p := p) (u := u) hrank hquot ha_ne

theorem rankThree_leftMultiplication_degreeTwoCokernel_finrank_eq_three_sub
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3)
    (a : linSubmodule) :
    Module.finrank ℝ
        ((quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u)) ⧸
          LinearMap.range (linearAnnihilatorMap B p u a)) =
      3 - Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u a)) := by
  rw [Submodule.finrank_quotient]
  rw [finrank_quotient_ker_catalecticantMap_eq_three_of_rank_three
    (B := B) (p := p) (u := u) hrank]

theorem exists_rankThreeBadBranch_leftMultiplication_degreeTwoCokernel
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3)
    (hquot : Module.finrank ℝ (linSubmodule ⧸ linearAnnihilator B p u) = 4) :
    ∃ (a : linSubmodule) (b q2 : ℕ),
      a ≠ 0 ∧
        Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u a)) = b ∧
          1 ≤ b ∧ b ≤ 3 ∧
            q2 = 3 - b ∧
              Module.finrank ℝ
                  ((quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u)) ⧸
                    LinearMap.range (linearAnnihilatorMap B p u a)) = q2 := by
  rcases exists_rankThreeBadBranch_leftMultiplication_finrank_range
      (B := B) (p := p) (u := u) hrank hquot with
    ⟨a, b, ha_ne, hb, hbpos, hbtop⟩
  refine ⟨a, b, 3 - b, ha_ne, hb, hbpos, hbtop, rfl, ?_⟩
  rw [rankThree_leftMultiplication_degreeTwoCokernel_finrank_eq_three_sub
    (B := B) (p := p) (u := u) hrank a]
  rw [hb]

def leftMultiplicationDegreeThreeMap
    (B : DotForm) (p : Poly) (u : RankSevenVec) (a : linSubmodule) :
    (quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u)) →ₗ[ℝ]
      Module.Dual ℝ linSubmodule :=
  (linearAnnihilatorMap B p u a).dualMap.comp
    (quotientCatalecticantMap B p u)

@[simp] theorem leftMultiplicationDegreeThreeMap_apply
    (B : DotForm) (p : Poly) (u : RankSevenVec)
    (a : linSubmodule)
    (q : quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u))
    (e : linSubmodule) :
    leftMultiplicationDegreeThreeMap B p u a q e =
      quotientCatalecticantMap B p u q (linearAnnihilatorMap B p u a e) :=
  rfl

theorem range_leftMultiplicationDegreeThreeMap_eq_range_dualMap
    (B : DotForm) (p : Poly) (u : RankSevenVec) (a : linSubmodule) :
    LinearMap.range (leftMultiplicationDegreeThreeMap B p u a) =
      LinearMap.range (linearAnnihilatorMap B p u a).dualMap := by
  rw [leftMultiplicationDegreeThreeMap, LinearMap.range_comp,
    range_quotientCatalecticantMap_eq_top, Submodule.map_top]

theorem finrank_range_leftMultiplicationDegreeThreeMap_eq
    (B : DotForm) (p : Poly) (u : RankSevenVec) (a : linSubmodule) :
    Module.finrank ℝ (LinearMap.range (leftMultiplicationDegreeThreeMap B p u a)) =
      Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u a)) := by
  rw [range_leftMultiplicationDegreeThreeMap_eq_range_dualMap,
    LinearMap.finrank_range_dualMap_eq_finrank_range]

theorem rankThree_leftMultiplication_degreeThreeCokernel_finrank_eq_four_sub
    (B : DotForm) (p : Poly) (u : RankSevenVec) (a : linSubmodule) :
    Module.finrank ℝ
        (Module.Dual ℝ linSubmodule ⧸
          LinearMap.range (leftMultiplicationDegreeThreeMap B p u a)) =
      4 - Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u a)) := by
  haveI : Module.Projective ℝ linSubmodule := inferInstance
  haveI : Module.Finite ℝ (Module.Dual ℝ linSubmodule) := Module.dual_finite
  rw [Submodule.finrank_quotient,
    finrank_range_leftMultiplicationDegreeThreeMap_eq,
    Subspace.dual_finrank_eq, finrank_linSubmodule_eq_four]

theorem exists_rankThreeBadBranch_leftMultiplication_degreeThreeCokernel
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3)
    (hquot : Module.finrank ℝ (linSubmodule ⧸ linearAnnihilator B p u) = 4) :
    ∃ (a : linSubmodule) (b q2 q3 : ℕ),
      a ≠ 0 ∧
        Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u a)) = b ∧
          1 ≤ b ∧ b ≤ 3 ∧
            q2 = 3 - b ∧
              Module.finrank ℝ
                  ((quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u)) ⧸
                    LinearMap.range (linearAnnihilatorMap B p u a)) = q2 ∧
                q3 = 4 - b ∧
                  Module.finrank ℝ
                      (Module.Dual ℝ linSubmodule ⧸
                        LinearMap.range (leftMultiplicationDegreeThreeMap B p u a)) = q3 := by
  rcases exists_rankThreeBadBranch_leftMultiplication_degreeTwoCokernel
      (B := B) (p := p) (u := u) hrank hquot with
    ⟨a, b, q2, ha_ne, hb, hbpos, hbtop, hq2, hq2fin⟩
  refine ⟨a, b, q2, 4 - b, ha_ne, hb, hbpos, hbtop, hq2, hq2fin, rfl, ?_⟩
  rw [rankThree_leftMultiplication_degreeThreeCokernel_finrank_eq_four_sub,
    hb]

theorem exists_rankThreeBadBranch_leftMultiplication_cokernel_not_macaulay
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3)
    (hquot : Module.finrank ℝ (linSubmodule ⧸ linearAnnihilator B p u) = 4) :
    ∃ a : linSubmodule,
      a ≠ 0 ∧
        ¬ Module.finrank ℝ
              (Module.Dual ℝ linSubmodule ⧸
                LinearMap.range (leftMultiplicationDegreeThreeMap B p u a)) ≤
            Module.finrank ℝ
              ((quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u)) ⧸
                LinearMap.range (linearAnnihilatorMap B p u a)) := by
  rcases exists_rankThreeBadBranch_leftMultiplication_degreeThreeCokernel
      (B := B) (p := p) (u := u) hrank hquot with
    ⟨a, b, q2, q3, ha_ne, _hb, hbpos, hbtop, hq2, hq2fin, hq3, hq3fin⟩
  refine ⟨a, ha_ne, ?_⟩
  intro hle
  exact rankThreeExactSequenceNumericalContradiction
    hbpos hbtop hq2 hq3 (by omega)

theorem rankThreeBadBranchContradiction_of_leftMultiplication_cokernel_macaulay
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3)
    (hquot : Module.finrank ℝ (linSubmodule ⧸ linearAnnihilator B p u) = 4)
    (hmac :
      ∀ a : linSubmodule,
        a ≠ 0 →
          Module.finrank ℝ
              (Module.Dual ℝ linSubmodule ⧸
                LinearMap.range (leftMultiplicationDegreeThreeMap B p u a)) ≤
            Module.finrank ℝ
              ((quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u)) ⧸
                LinearMap.range (linearAnnihilatorMap B p u a))) :
    False := by
  rcases exists_rankThreeBadBranch_leftMultiplication_cokernel_not_macaulay
      (B := B) (p := p) (u := u) hrank hquot with
    ⟨a, ha_ne, hnot⟩
  exact hnot (hmac a ha_ne)

def scalarizedLinearAnnihilatorMap
    (B : DotForm) (p : Poly) (u : RankSevenVec)
    (T :
      (quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u)) →ₗ[ℝ] ℝ) :
    linSubmodule →ₗ[ℝ] Module.Dual ℝ linSubmodule :=
  (linearMapPostcomp (V := linSubmodule) T).comp
    (linearAnnihilatorMap B p u)

@[simp] theorem scalarizedLinearAnnihilatorMap_apply
    (B : DotForm) (p : Poly) (u : RankSevenVec)
    (T :
      (quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u)) →ₗ[ℝ] ℝ)
    (a e : linSubmodule) :
    scalarizedLinearAnnihilatorMap B p u T a e =
      T ((LinearMap.ker (catalecticantMap B p u)).mkQ (linProduct a e)) :=
  rfl

theorem scalarizedLinearAnnihilatorMap_symm
    (B : DotForm) (p : Poly) (u : RankSevenVec)
    (T :
      (quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u)) →ₗ[ℝ] ℝ)
    (a e : linSubmodule) :
    scalarizedLinearAnnihilatorMap B p u T a e =
      scalarizedLinearAnnihilatorMap B p u T e a := by
  change T ((LinearMap.ker (catalecticantMap B p u)).mkQ (linProduct a e)) =
    T ((LinearMap.ker (catalecticantMap B p u)).mkQ (linProduct e a))
  rw [linProduct_comm]

theorem scalarizedLinearAnnihilatorMap_range_le_one_of_rank_one_identity
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (T :
      (quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u)) →ₗ[ℝ] ℝ)
    (hid :
      ∀ w x y z : linSubmodule,
        scalarizedLinearAnnihilatorMap B p u T w x *
            scalarizedLinearAnnihilatorMap B p u T y z =
          scalarizedLinearAnnihilatorMap B p u T w y *
            scalarizedLinearAnnihilatorMap B p u T x z) :
    Module.finrank ℝ
        (LinearMap.range (scalarizedLinearAnnihilatorMap B p u T)) ≤ 1 :=
  finrank_range_le_one_of_symmetric_rank_one_identity
    (scalarizedLinearAnnihilatorMap B p u T)
    (scalarizedLinearAnnihilatorMap_symm B p u T)
    hid

theorem finrank_range_linearAnnihilatorMap_le_one_of_scalarized_rank_one_identity
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (T :
      (quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u)) →ₗ[ℝ] ℝ)
    (hT : LinearMap.ker T = ⊥)
    (hid :
      ∀ w x y z : linSubmodule,
        scalarizedLinearAnnihilatorMap B p u T w x *
            scalarizedLinearAnnihilatorMap B p u T y z =
          scalarizedLinearAnnihilatorMap B p u T w y *
            scalarizedLinearAnnihilatorMap B p u T x z) :
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 1 := by
  exact finrank_range_le_one_of_scalarized_postcomp
    (V := linSubmodule) T hT (linearAnnihilatorMap B p u)
    (scalarizedLinearAnnihilatorMap_range_le_one_of_rank_one_identity
      (B := B) (p := p) (u := u) T hid)

theorem finrank_range_linearAnnihilatorMap_le_one_of_rank_one_scalarization
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hrank :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1)
    (hidentity :
      ∀ T :
          (quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u)) →ₗ[ℝ] ℝ,
        LinearMap.ker T = ⊥ →
          ∀ w x y z : linSubmodule,
            scalarizedLinearAnnihilatorMap B p u T w x *
                scalarizedLinearAnnihilatorMap B p u T y z =
              scalarizedLinearAnnihilatorMap B p u T w y *
                scalarizedLinearAnnihilatorMap B p u T x z) :
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 1 := by
  rcases exists_linearMap_to_field_ker_eq_bot_of_finrank_eq_one
      (K := ℝ)
      (V := quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u))
      (finrank_quotient_ker_catalecticantMap_eq_one_of_rank_one
        (B := B) (p := p) (u := u) hrank) with
    ⟨T, hT⟩
  exact finrank_range_linearAnnihilatorMap_le_one_of_scalarized_rank_one_identity
    (B := B) (p := p) (u := u) T hT (hidentity T hT)

theorem scalarizedLinearAnnihilatorMap_rank_one_identity_of_quotientPairing_nonzero
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (T :
      (quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u)) →ₗ[ℝ] ℝ)
    (hT : LinearMap.ker T = ⊥)
    {r s : quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u)}
    (hrs : quotientCatalecticantMap B p u r s ≠ 0) :
    ∀ w x y z : linSubmodule,
      scalarizedLinearAnnihilatorMap B p u T w x *
          scalarizedLinearAnnihilatorMap B p u T y z =
        scalarizedLinearAnnihilatorMap B p u T w y *
          scalarizedLinearAnnihilatorMap B p u T x z := by
  intro w x y z
  exact coordinate_mul_eq_of_bilin_eq_of_ker_eq_bot
    (T := T) hT (quotientCatalecticantMap B p u) hrs
    (quotientCatalecticantMap_linearProducts_reassociate B p u w x y z)

theorem finrank_range_linearAnnihilatorMap_le_one_of_rank_one_quotientPairing_nonzero
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hrank :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1)
    (hnonzero :
      ∀ T :
          (quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u)) →ₗ[ℝ] ℝ,
        LinearMap.ker T = ⊥ →
          ∃ r s : quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u),
            quotientCatalecticantMap B p u r s ≠ 0) :
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 1 :=
  finrank_range_linearAnnihilatorMap_le_one_of_rank_one_scalarization
    (B := B) (p := p) (u := u) hrank
    (by
      intro T hT
      rcases hnonzero T hT with ⟨r, s, hrs⟩
      exact scalarizedLinearAnnihilatorMap_rank_one_identity_of_quotientPairing_nonzero
        (B := B) (p := p) (u := u) T hT hrs)

theorem exists_quotientCatalecticantMap_pair_ne_zero_of_catalecticantMap_rank_one
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hrank :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1) :
    ∃ r s : quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u),
      quotientCatalecticantMap B p u r s ≠ 0 := by
  by_contra hnone
  push Not at hnone
  have hmap_zero : catalecticantMap B p u = 0 := by
    ext q r
    have hpair := hnone
      ((LinearMap.ker (catalecticantMap B p u)).mkQ q)
      ((LinearMap.ker (catalecticantMap B p u)).mkQ r)
    simpa using hpair
  have hrange_zero :
      LinearMap.range (catalecticantMap B p u) = ⊥ := by
    rw [hmap_zero]
    simp
  have hfin_zero :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 0 := by
    rw [hrange_zero]
    simp
  omega

theorem finrank_range_linearAnnihilatorMap_le_one_of_catalecticantMap_rank_one
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hrank :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1) :
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 1 :=
  finrank_range_linearAnnihilatorMap_le_one_of_rank_one_quotientPairing_nonzero
    (B := B) (p := p) (u := u) hrank
    (fun _T _hT =>
      exists_quotientCatalecticantMap_pair_ne_zero_of_catalecticantMap_rank_one
        (B := B) (p := p) (u := u) hrank)

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

theorem le_linearAnnihilator_of_linProductSubmodule_top_le_ker
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {A : Submodule ℝ linSubmodule}
    (hAE : linProductSubmodule A ⊤ ≤ LinearMap.ker (catalecticantMap B p u)) :
    A ≤ linearAnnihilator B p u := by
  intro a ha e
  exact hAE
    (linProduct_mem_linProductSubmodule
      (⟨a, ha⟩ : A) (⟨e, trivial⟩ : (⊤ : Submodule ℝ linSubmodule)))

theorem exists_catalecticantKernel_decomposition_of_annihilator_complement
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {A W : Submodule ℝ linSubmodule}
    (hA : A ≤ linearAnnihilator B p u)
    (hAW : IsCompl A W)
    (q : quadSubmodule) :
    ∃ qW qK : quadSubmodule,
      q = qW + qK ∧
        qW ∈ linProductSubmodule W W ∧
          qK ∈ LinearMap.ker (catalecticantMap B p u) := by
  rcases exists_linProduct_decomposition_of_isCompl hAW q with
    ⟨qK, qW, hqKprod, hqW, hqdecomp⟩
  exact ⟨qW, qK, hqdecomp, hqW,
    linProductSubmodule_le_ker_of_le_linearAnnihilator hA hqKprod⟩

theorem supportAmbient_le_ker_of_range_and_symSquare
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {x : linSubmodule} {A : Submodule ℝ linSubmodule}
    (hrange :
      LinearMap.range (linProductLeftMapOn x A) ≤
        LinearMap.ker (catalecticantMap B p u))
    (hsym :
      symSquareSubmodule A ≤ LinearMap.ker (catalecticantMap B p u)) :
    supportAmbient x A ≤ LinearMap.ker (catalecticantMap B p u) :=
  sup_le hrange hsym

theorem range_linProductLeftMapOn_le_ker_of_le_linearAnnihilator
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {x : linSubmodule} {A : Submodule ℝ linSubmodule}
    (hA : A ≤ linearAnnihilator B p u) :
    LinearMap.range (linProductLeftMapOn x A) ≤
      LinearMap.ker (catalecticantMap B p u) := by
  rintro q ⟨a, rfl⟩
  change linProduct x a.1 ∈ LinearMap.ker (catalecticantMap B p u)
  rw [linProduct_comm]
  exact hA a.2 x

theorem symSquareSubmodule_le_ker_of_le_linearAnnihilator
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {A : Submodule ℝ linSubmodule}
    (hA : A ≤ linearAnnihilator B p u) :
    symSquareSubmodule A ≤ LinearMap.ker (catalecticantMap B p u) :=
  (linProductSubmodule_mono le_rfl le_top).trans
    (linProductSubmodule_le_ker_of_le_linearAnnihilator hA)

theorem supportAmbient_le_ker_of_le_linearAnnihilator
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {x : linSubmodule} {A : Submodule ℝ linSubmodule}
    (hA : A ≤ linearAnnihilator B p u) :
    supportAmbient x A ≤ LinearMap.ker (catalecticantMap B p u) :=
  supportAmbient_le_ker_of_range_and_symSquare
    (range_linProductLeftMapOn_le_ker_of_le_linearAnnihilator
      (B := B) (p := p) (u := u) (x := x) hA)
    (symSquareSubmodule_le_ker_of_le_linearAnnihilator
      (B := B) (p := p) (u := u) hA)

theorem finrank_supportAmbient_eq_add_of_disjoint
    {x : linSubmodule} {A : Submodule ℝ linSubmodule}
    (hdisj :
      LinearMap.range (linProductLeftMapOn x A) ⊓ symSquareSubmodule A = ⊥) :
    Module.finrank ℝ (supportAmbient x A) =
      Module.finrank ℝ (LinearMap.range (linProductLeftMapOn x A)) +
        Module.finrank ℝ (symSquareSubmodule A) := by
  have hgrass :=
    Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.range (linProductLeftMapOn x A)) (symSquareSubmodule A)
  rw [hdisj] at hgrass
  simpa [supportAmbient] using hgrass

theorem finrank_supportAmbient_eq_five_of_rank_two_components
    {x : linSubmodule} {A : Submodule ℝ linSubmodule}
    (hx : (x : Poly) ≠ 0)
    (hA : Module.finrank ℝ A = 2)
    (hsym : Module.finrank ℝ (symSquareSubmodule A) = 3)
    (hdisj :
      LinearMap.range (linProductLeftMapOn x A) ⊓ symSquareSubmodule A = ⊥) :
    Module.finrank ℝ (supportAmbient x A) = 5 := by
  rw [finrank_supportAmbient_eq_add_of_disjoint hdisj]
  rw [finrank_range_linProductLeftMapOn_eq hx, hA, hsym]

theorem five_le_finrank_supportAmbient_of_rank_two_components
    {x : linSubmodule} {A : Submodule ℝ linSubmodule}
    (hx : (x : Poly) ≠ 0)
    (hA : Module.finrank ℝ A = 2)
    (hsym : Module.finrank ℝ (symSquareSubmodule A) = 3)
    (hdisj :
      LinearMap.range (linProductLeftMapOn x A) ⊓ symSquareSubmodule A = ⊥) :
    5 ≤ Module.finrank ℝ (supportAmbient x A) := by
  rw [finrank_supportAmbient_eq_five_of_rank_two_components hx hA hsym hdisj]

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

theorem linProduct_mem_catalecticantKernel_of_product_le_ker
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {A : Submodule ℝ linSubmodule}
    (hAE : linProductSubmodule A ⊤ ≤ LinearMap.ker (catalecticantMap B p u))
    (a : A) (e : linSubmodule) :
    (linProduct a.1 e : quadSubmodule).1 ∈ catalecticantKernel B p u := by
  exact mem_ker_catalecticantMap_iff.mp
    (hAE (linProduct_mem_linProductSubmodule a
      (⟨e, trivial⟩ : (⊤ : Submodule ℝ linSubmodule))))

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

theorem linProduct_comm_mem_catalecticantKernel_of_product_le_ker
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {A : Submodule ℝ linSubmodule}
    (hAE : linProductSubmodule A ⊤ ≤ LinearMap.ker (catalecticantMap B p u))
    (e : linSubmodule) (a : A) :
    (linProduct e a.1 : quadSubmodule).1 ∈ catalecticantKernel B p u := by
  rw [linProduct_comm]
  exact linProduct_mem_catalecticantKernel_of_product_le_ker hAE a e

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

theorem mem_spanUQuad_of_rank_three_of_mem_catalecticantKernel
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hfocp : IsFOCP B p u)
    (hker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3)
    {q : quadSubmodule}
    (hqK : q.1 ∈ catalecticantKernel B p u) :
    q ∈ spanUQuad hu := by
  have hspan_eq_ker :
      spanUQuad hu = LinearMap.ker (catalecticantMap B p u) :=
    spanUQuad_eq_ker_catalecticantMap_of_rank_three
      (B := B) (p := p) (u := u) hu hfocp hker hrank
  rw [hspan_eq_ker]
  exact mem_ker_catalecticantMap_iff.mpr hqK

theorem mem_spanUQuad_of_rank_three_of_mem_ker_catalecticantMap
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hfocp : IsFOCP B p u)
    (hker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3)
    {q : quadSubmodule}
    (hqK : q ∈ LinearMap.ker (catalecticantMap B p u)) :
    q ∈ spanUQuad hu := by
  have hspan_eq_ker :
      spanUQuad hu = LinearMap.ker (catalecticantMap B p u) :=
    spanUQuad_eq_ker_catalecticantMap_of_rank_three
      (B := B) (p := p) (u := u) hu hfocp hker hrank
  rw [hspan_eq_ker]
  exact hqK

theorem linProduct_mem_spanUQuad_of_rank_three_of_mem_linearAnnihilator
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hfocp : IsFOCP B p u)
    (hker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3)
    {a : linSubmodule}
    (ha : a ∈ linearAnnihilator B p u)
    (e : linSubmodule) :
    linProduct a e ∈ spanUQuad hu :=
  mem_spanUQuad_of_rank_three_of_mem_catalecticantKernel
    (B := B) (p := p) (u := u) hu hfocp hker hrank
    (linProduct_mem_catalecticantKernel_of_mem_linearAnnihilator ha e)

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

theorem four_le_finrank_spanUQuad_inf_of_rank_two_ambient
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hfocp : IsFOCP B p u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2)
    {U : Submodule ℝ quadSubmodule}
    (hUker : U ≤ LinearMap.ker (catalecticantMap B p u))
    (hUdim : 5 ≤ Module.finrank ℝ U) :
    4 ≤ Module.finrank ℝ ↥(spanUQuad hu ⊓ U) := by
  have hLker : spanUQuad hu ≤ LinearMap.ker (catalecticantMap B p u) :=
    spanUQuad_le_ker_catalecticantMap hu hfocp
  have hLdim : 7 ≤ Module.finrank ℝ (spanUQuad hu) := by
    rw [finrank_spanUQuad_eq_seven_of_relationPolyLin_ker_eq_bot hu hrelker]
  have hKdim : Module.finrank ℝ (LinearMap.ker (catalecticantMap B p u)) ≤ 8 := by
    rw [finrank_ker_catalecticantMap_eq_eight_of_rank_two hrank]
  exact four_le_finrank_inf_of_seven_five_eight
    (K := ℝ) (V := quadSubmodule)
    (s := spanUQuad hu) (t := U) (w := LinearMap.ker (catalecticantMap B p u))
    hLker hUker hLdim hUdim hKdim

theorem four_le_finrank_spanUQuad_inf_of_rank_one_ambient
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hfocp : IsFOCP B p u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1)
    {U : Submodule ℝ quadSubmodule}
    (hUker : U ≤ LinearMap.ker (catalecticantMap B p u))
    (hUdim : 6 ≤ Module.finrank ℝ U) :
    4 ≤ Module.finrank ℝ ↥(spanUQuad hu ⊓ U) := by
  have hLker : spanUQuad hu ≤ LinearMap.ker (catalecticantMap B p u) :=
    spanUQuad_le_ker_catalecticantMap hu hfocp
  have hLdim : 7 ≤ Module.finrank ℝ (spanUQuad hu) := by
    rw [finrank_spanUQuad_eq_seven_of_relationPolyLin_ker_eq_bot hu hrelker]
  have hKdim : Module.finrank ℝ (LinearMap.ker (catalecticantMap B p u)) ≤ 9 := by
    rw [finrank_ker_catalecticantMap_eq_nine_of_rank_one hrank]
  exact four_le_finrank_inf_of_seven_six_nine
    (K := ℝ) (V := quadSubmodule)
    (s := spanUQuad hu) (t := U) (w := LinearMap.ker (catalecticantMap B p u))
    hLker hUker hLdim hUdim hKdim

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

theorem exists_negative_sos_summand_of_catalecticantMap_rank_eq_one
    {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u)
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1) :
    ∃ q : Poly, IsQuadratic q ∧ B (q ^ 2) (residual p u) < 0 :=
  exists_negative_sos_summand_of_nonzero_residual
    (B := B) hu hp hfocp
    (residual_ne_zero_of_catalecticantMap_rank_eq_one hrank)

theorem exists_negative_sos_summand_of_catalecticantMap_rank_eq_two
    {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u)
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2) :
    ∃ q : Poly, IsQuadratic q ∧ B (q ^ 2) (residual p u) < 0 :=
  exists_negative_sos_summand_of_nonzero_residual
    (B := B) hu hp hfocp
    (residual_ne_zero_of_catalecticantMap_rank_eq_two hrank)

theorem exists_negative_sos_summand_of_catalecticantMap_rank_eq_three
    {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u)
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3) :
    ∃ q : Poly, IsQuadratic q ∧ B (q ^ 2) (residual p u) < 0 :=
  exists_negative_sos_summand_of_nonzero_residual
    (B := B) hu hp hfocp
    (residual_ne_zero_of_catalecticantMap_rank_eq_three hrank)

end ResidualFunctional

end QuaternaryQuartic
