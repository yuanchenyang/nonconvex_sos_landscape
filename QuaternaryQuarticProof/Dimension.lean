import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Basis.VectorSpace

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace QuaternaryQuartic

open Module

section Grassmann

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]

theorem finrank_add_le_finrank_add_finrank_inf_of_le
    {s t w : Submodule K V}
    (hsw : s ≤ w) (htw : t ≤ w) :
    finrank K s + finrank K t ≤ finrank K w + finrank K ↥(s ⊓ t) := by
  have hsup_le : s ⊔ t ≤ w := sup_le hsw htw
  have hsup_finrank : finrank K ↥(s ⊔ t) ≤ finrank K w :=
    Submodule.finrank_mono hsup_le
  have hgrassmann :
      finrank K ↥(s ⊔ t) + finrank K ↥(s ⊓ t) =
        finrank K s + finrank K t := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (Submodule.finrank_sup_add_finrank_inf_eq s t)
  nlinarith

theorem finrank_sup_le_add (s t : Submodule K V) :
    finrank K ↥(s ⊔ t) ≤ finrank K s + finrank K t := by
  have hgrassmann :
      finrank K ↥(s ⊔ t) + finrank K ↥(s ⊓ t) =
        finrank K s + finrank K t := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (Submodule.finrank_sup_add_finrank_inf_eq s t)
  omega

theorem finrank_sup_le_of_le_add
    {s t : Submodule K V} {a b c : ℕ}
    (hs : finrank K s ≤ a) (ht : finrank K t ≤ b)
    (habc : a + b ≤ c) :
    finrank K ↥(s ⊔ t) ≤ c := by
  have hsup := finrank_sup_le_add (K := K) (V := V) s t
  omega

theorem finrank_sup_le_five_of_le_two_three
    {s t : Submodule K V}
    (hs : finrank K s ≤ 2) (ht : finrank K t ≤ 3) :
    finrank K ↥(s ⊔ t) ≤ 5 :=
  finrank_sup_le_of_le_add (K := K) (V := V)
    (s := s) (t := t) hs ht (by norm_num)

theorem finrank_sup_le_six_of_le_three_three
    {s t : Submodule K V}
    (hs : finrank K s ≤ 3) (ht : finrank K t ≤ 3) :
    finrank K ↥(s ⊔ t) ≤ 6 :=
  finrank_sup_le_of_le_add (K := K) (V := V)
    (s := s) (t := t) hs ht (by norm_num)

theorem finrank_sup_le_nine_of_le_three_six
    {s t : Submodule K V}
    (hs : finrank K s ≤ 3) (ht : finrank K t ≤ 6) :
    finrank K ↥(s ⊔ t) ≤ 9 :=
  finrank_sup_le_of_le_add (K := K) (V := V)
    (s := s) (t := t) hs ht (by norm_num)

theorem inf_ne_bot_of_finrank_lt_add
    {s t w : Submodule K V}
    (hsw : s ≤ w) (htw : t ≤ w)
    (hgt : finrank K w < finrank K s + finrank K t) :
    s ⊓ t ≠ ⊥ := by
  intro hinf
  have hbound :=
    finrank_add_le_finrank_add_finrank_inf_of_le (K := K) (V := V) hsw htw
  have hinf_rank : finrank K ↥(s ⊓ t) = 0 := by
    rw [hinf]
    simp
  nlinarith

theorem exists_mem_inf_ne_zero_of_finrank_lt_add
    {s t w : Submodule K V}
    (hsw : s ≤ w) (htw : t ≤ w)
    (hgt : finrank K w < finrank K s + finrank K t) :
    ∃ x : V, x ∈ s ∧ x ∈ t ∧ x ≠ 0 := by
  have hinf_ne : s ⊓ t ≠ ⊥ :=
    inf_ne_bot_of_finrank_lt_add (K := K) (V := V) hsw htw hgt
  rcases Submodule.exists_mem_ne_zero_of_ne_bot hinf_ne with ⟨x, hx, hxne⟩
  exact ⟨x, hx.1, hx.2, hxne⟩

theorem exists_mem_inf_ne_zero_of_finrank_eq_and_lt_add
    {s t w : Submodule K V} {a b c : ℕ}
    (hsw : s ≤ w) (htw : t ≤ w)
    (hs : a ≤ finrank K s) (ht : b ≤ finrank K t)
    (hw : finrank K w = c)
    (hgt : c < a + b) :
    ∃ x : V, x ∈ s ∧ x ∈ t ∧ x ≠ 0 := by
  refine exists_mem_inf_ne_zero_of_finrank_lt_add (K := K) (V := V) hsw htw ?_
  nlinarith

theorem finrank_inf_ge_add_sub_of_le
    {s t w : Submodule K V} {a b c : ℕ}
    (hsw : s ≤ w) (htw : t ≤ w)
    (hs : a ≤ finrank K s) (ht : b ≤ finrank K t)
    (hw : finrank K w ≤ c) :
    a + b - c ≤ finrank K ↥(s ⊓ t) := by
  have hbound :=
    finrank_add_le_finrank_add_finrank_inf_of_le (K := K) (V := V) hsw htw
  omega

theorem four_le_finrank_inf_of_seven_five_eight
    {s t w : Submodule K V}
    (hsw : s ≤ w) (htw : t ≤ w)
    (hs : 7 ≤ finrank K s) (ht : 5 ≤ finrank K t)
    (hw : finrank K w ≤ 8) :
    4 ≤ finrank K ↥(s ⊓ t) := by
  simpa using
    finrank_inf_ge_add_sub_of_le
      (K := K) (V := V) (s := s) (t := t) (w := w)
      (a := 7) (b := 5) (c := 8) hsw htw hs ht hw

theorem four_le_finrank_inf_of_seven_six_nine
    {s t w : Submodule K V}
    (hsw : s ≤ w) (htw : t ≤ w)
    (hs : 7 ≤ finrank K s) (ht : 6 ≤ finrank K t)
    (hw : finrank K w ≤ 9) :
    4 ≤ finrank K ↥(s ⊓ t) := by
  simpa using
    finrank_inf_ge_add_sub_of_le
      (K := K) (V := V) (s := s) (t := t) (w := w)
      (a := 7) (b := 6) (c := 9) hsw htw hs ht hw

end Grassmann

section Complements

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]

theorem exists_isCompl_finrank_eq_sub
    (s : Submodule K V) {n m : ℕ}
    (hV : finrank K V = n)
    (hs : finrank K s = m) :
    ∃ t : Submodule K V, IsCompl s t ∧ finrank K t = n - m := by
  rcases Submodule.exists_isCompl s with ⟨t, hst⟩
  refine ⟨t, hst, ?_⟩
  have hsum := Submodule.finrank_add_eq_of_isCompl (K := K) (V := V) hst
  omega

theorem exists_isCompl_finrank_add_eq
    (s : Submodule K V) :
    ∃ t : Submodule K V, IsCompl s t ∧ finrank K s + finrank K t = finrank K V := by
  rcases Submodule.exists_isCompl s with ⟨t, hst⟩
  exact ⟨t, hst, Submodule.finrank_add_eq_of_isCompl (K := K) (V := V) hst⟩

end Complements

section ComplementVectors

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem exists_mem_ne_zero_of_finrank_pos
    {s : Submodule K V}
    (hs : 0 < finrank K s) :
    ∃ x : V, x ∈ s ∧ x ≠ 0 := by
  have hsne : s ≠ ⊥ := by
    intro hbot
    rw [hbot] at hs
    simp at hs
  exact Submodule.exists_mem_ne_zero_of_ne_bot hsne

theorem not_mem_left_of_isCompl_right_mem_ne_zero
    {s t : Submodule K V} (hst : IsCompl s t)
    {x : V} (hxt : x ∈ t) (hxne : x ≠ 0) :
    x ∉ s := by
  intro hxs
  have hxinf : x ∈ s ⊓ t := ⟨hxs, hxt⟩
  have hxbot : x ∈ (⊥ : Submodule K V) := by
    simpa [hst.disjoint.eq_bot] using hxinf
  exact hxne (by simpa using hxbot)

theorem not_mem_right_of_isCompl_left_mem_ne_zero
    {s t : Submodule K V} (hst : IsCompl s t)
    {x : V} (hxs : x ∈ s) (hxne : x ≠ 0) :
    x ∉ t := by
  intro hxt
  have hxinf : x ∈ s ⊓ t := ⟨hxs, hxt⟩
  have hxbot : x ∈ (⊥ : Submodule K V) := by
    simpa [hst.disjoint.eq_bot] using hxinf
  exact hxne (by simpa using hxbot)

end ComplementVectors

section SubspaceChoice

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]

section SpanDisjoint

variable {ι κ : Type*}

omit [FiniteDimensional K V] in
theorem disjoint_span_ranges_of_linearIndependent_sum
    {f : ι → V} {g : κ → V}
    (hLI : LinearIndependent K (Sum.elim f g : ι ⊕ κ → V)) :
    Disjoint (Submodule.span K (Set.range f)) (Submodule.span K (Set.range g)) := by
  simpa [Function.comp_def] using
    (linearIndependent_sum.mp hLI).2.2

omit [FiniteDimensional K V] in
theorem inf_span_ranges_eq_bot_of_linearIndependent_sum
    {f : ι → V} {g : κ → V}
    (hLI : LinearIndependent K (Sum.elim f g : ι ⊕ κ → V)) :
    Submodule.span K (Set.range f) ⊓ Submodule.span K (Set.range g) = ⊥ :=
  (disjoint_span_ranges_of_linearIndependent_sum
    (K := K) (V := V) hLI).eq_bot

end SpanDisjoint

theorem exists_mem_notMem_of_finrank_lt
    {s t : Submodule K V}
    (hlt : finrank K t < finrank K s) :
    ∃ x : V, x ∈ s ∧ x ∉ t := by
  by_contra h
  push Not at h
  have hs_le_t : s ≤ t := by
    intro x hx
    exact h x hx
  have hle := Submodule.finrank_mono hs_le_t
  omega

theorem exists_mem_notMem_span_singleton_of_finrank_two
    {W : Submodule K V} {x : V}
    (hxne : x ≠ 0)
    (hW : finrank K W = 2) :
    ∃ y : V, y ∈ W ∧ y ∉ K ∙ x := by
  have hline : finrank K (K ∙ x) = 1 := finrank_span_singleton hxne
  have hlt : finrank K (K ∙ x) < finrank K W := by omega
  exact exists_mem_notMem_of_finrank_lt (K := K) (V := V) hlt

omit [FiniteDimensional K V] in
theorem linearIndependent_pair_of_notMem_span_singleton
    {x y : V}
    (hxne : x ≠ 0)
    (hy : y ∉ K ∙ x) :
    LinearIndependent K ![x, y] := by
  rw [LinearIndependent.pair_iff' hxne]
  intro a hay
  exact hy (by
    rw [← hay]
    exact Submodule.smul_mem _ a (Submodule.subset_span (by simp)))

omit [FiniteDimensional K V] in
theorem finrank_span_pair_eq_two_of_notMem_span_singleton
    {x y : V}
    (hxne : x ≠ 0)
    (hy : y ∉ K ∙ x) :
    finrank K (Submodule.span K ({x, y} : Set V)) = 2 := by
  have hli : LinearIndependent K ![x, y] :=
    linearIndependent_pair_of_notMem_span_singleton
      (K := K) (V := V) hxne hy
  have hfin :
      finrank K (Submodule.span K (Set.range ![x, y])) =
        Fintype.card (Fin 2) :=
    finrank_span_eq_card hli
  have hrange : Set.range ![x, y] = ({x, y} : Set V) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
  rw [hrange] at hfin
  simpa using hfin

theorem span_pair_eq_of_mem_of_notMem_span_singleton_of_finrank_two
    {W : Submodule K V} {x y : V}
    (hxne : x ≠ 0)
    (hxW : x ∈ W)
    (hyW : y ∈ W)
    (hy : y ∉ K ∙ x)
    (hW : finrank K W = 2) :
    Submodule.span K ({x, y} : Set V) = W := by
  have hspan_le : Submodule.span K ({x, y} : Set V) ≤ W := by
    refine Submodule.span_le.mpr ?_
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hxW
    · exact hyW
  exact Submodule.eq_of_le_of_finrank_eq hspan_le (by
    rw [finrank_span_pair_eq_two_of_notMem_span_singleton
      (K := K) (V := V) hxne hy, hW])

theorem span_singleton_eq_of_mem_of_finrank_one
    {W : Submodule K V} {x : V}
    (hxne : x ≠ 0)
    (hxW : x ∈ W)
    (hW : finrank K W = 1) :
    K ∙ x = W := by
  have hspan_le : K ∙ x ≤ W := by
    exact Submodule.span_le.mpr (by
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hxW)
  exact Submodule.eq_of_le_of_finrank_eq hspan_le (by
    rw [finrank_span_singleton hxne, hW])

end SubspaceChoice

section RankOneBilinear

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem finrank_range_le_one_of_symmetric_rank_one_identity
    (M : V →ₗ[K] Module.Dual K V)
    (hsym : ∀ x y : V, M x y = M y x)
    (hrank_one : ∀ w x y z : V, M w x * M y z = M w y * M x z) :
    Module.finrank K (LinearMap.range M) ≤ 1 := by
  by_cases hzero : ∀ x y : V, M x y = 0
  · have hrange_bot : LinearMap.range M = ⊥ := by
      ext φ
      constructor
      · rintro ⟨x, rfl⟩
        ext y
        exact hzero x y
      · intro hφ
        have hφ0 : φ = 0 := by
          simp at hφ
          exact hφ
        refine ⟨0, ?_⟩
        rw [hφ0]
        simp
    rw [hrange_bot]
    simp
  · push Not at hzero
    rcases hzero with ⟨x, y, hxy⟩
    have hx_ne : M x ≠ 0 := by
      intro hx
      have hxy_zero := congrArg (fun φ : Module.Dual K V => φ y) hx
      exact hxy (by simpa using hxy_zero)
    have hrange_le :
        LinearMap.range M ≤ (K ∙ M x : Submodule K (Module.Dual K V)) := by
      rintro φ ⟨w, rfl⟩
      refine Submodule.mem_span_singleton.mpr ⟨M w y / M x y, ?_⟩
      ext z
      have hmul : M w z * M x y = M w y * M x z := by
        simpa [hsym y x, hsym z x] using hrank_one w z y x
      change (M w y / M x y) * M x z = M w z
      field_simp [hxy]
      simpa [mul_comm] using hmul.symm
    have hrange_fin := Submodule.finrank_mono hrange_le
    have hspan_fin :
        Module.finrank K (K ∙ M x : Submodule K (Module.Dual K V)) = 1 :=
      finrank_span_singleton hx_ne
    omega

end RankOneBilinear

section Postcomposition

variable {K U V W W' : Type*} [Field K]
variable [AddCommGroup U] [Module K U]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]
variable [AddCommGroup W'] [Module K W']

def linearMapPostcomp (T : W →ₗ[K] W') :
    (V →ₗ[K] W) →ₗ[K] V →ₗ[K] W' where
  toFun f := T.comp f
  map_add' := by
    intro f g
    ext x
    simp
  map_smul' := by
    intro c f
    ext x
    simp

theorem linearMapPostcomp_injective {T : W →ₗ[K] W'}
    (hT : LinearMap.ker T = ⊥) :
    Function.Injective (linearMapPostcomp (V := V) T) := by
  intro f g hfg
  ext x
  have hTx : T (f x) = T (g x) := by
    exact congrArg (fun F : V →ₗ[K] W' => F x) hfg
  exact (LinearMap.ker_eq_bot.mp hT) hTx

theorem finrank_range_eq_of_injective_postcomp
    (T : W →ₗ[K] W')
    (hT : LinearMap.ker T = ⊥)
    (M : U →ₗ[K] V →ₗ[K] W) :
    Module.finrank K (LinearMap.range M) =
      Module.finrank K
        (LinearMap.range ((linearMapPostcomp (V := V) T).comp M)) := by
  let P := linearMapPostcomp (V := V) T
  let Psub :
      LinearMap.range M →ₗ[K] LinearMap.range (P.comp M) :=
  {
    toFun f := ⟨P f.1, by
      rcases f.2 with ⟨u, hu⟩
      exact ⟨u, congrArg (fun g : V →ₗ[K] W => P g) hu⟩⟩
    map_add' := by
      intro f g
      ext x
      simp [P]
    map_smul' := by
      intro c f
      ext x
      simp [P]
  }
  have hPsub_inj : Function.Injective Psub := by
    intro f g hfg
    apply Subtype.ext
    exact (linearMapPostcomp_injective (V := V) hT)
      (Subtype.ext_iff.mp hfg)
  have hPsub_surj : Function.Surjective Psub := by
    rintro ⟨φ, u, rfl⟩
    exact ⟨⟨M u, ⟨u, rfl⟩⟩, rfl⟩
  exact (LinearEquiv.ofBijective Psub ⟨hPsub_inj, hPsub_surj⟩).finrank_eq

theorem finrank_range_le_one_of_scalarized_postcomp
    (T : W →ₗ[K] W')
    (hT : LinearMap.ker T = ⊥)
    (M : U →ₗ[K] V →ₗ[K] W)
    (hscalar :
      Module.finrank K
        (LinearMap.range ((linearMapPostcomp (V := V) T).comp M)) ≤ 1) :
    Module.finrank K (LinearMap.range M) ≤ 1 := by
  rw [finrank_range_eq_of_injective_postcomp (V := V) T hT M]
  exact hscalar

end Postcomposition

section OneDimensionalCoordinate

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem smul_eq_smul_of_linearMap_to_field_ker_eq_bot
    {T : V →ₗ[K] K} (hT : LinearMap.ker T = ⊥) (a b : V) :
    T a • b = T b • a := by
  apply LinearMap.ker_eq_bot.mp hT
  simp [mul_comm]

theorem exists_linearMap_to_field_ker_eq_bot_of_finrank_eq_one
    (hV : Module.finrank K V = 1) :
    ∃ T : V →ₗ[K] K, LinearMap.ker T = ⊥ := by
  letI : Module.Free K V := Module.Free.of_divisionRing K V
  rcases Module.nonempty_linearEquiv_of_finrank_eq_one
      (R := K) (M := V) hV with
    ⟨e⟩
  exact ⟨e.symm.toLinearMap, LinearMap.ker_eq_bot.mpr e.symm.injective⟩

theorem coordinate_mul_bilin_eq_coordinate_mul_bilin_of_ker_eq_bot
    {T : V →ₗ[K] K} (hT : LinearMap.ker T = ⊥)
    (C : V →ₗ[K] Module.Dual K V) (a b r s : V) :
    T r * T s * C a b = T a * T b * C r s := by
  have hra : T r • a = T a • r :=
    smul_eq_smul_of_linearMap_to_field_ker_eq_bot hT r a
  have hsb : T s • b = T b • s :=
    smul_eq_smul_of_linearMap_to_field_ker_eq_bot hT s b
  calc
    T r * T s * C a b =
        C (T r • a) (T s • b) := by
          simp [mul_assoc, mul_left_comm]
    _ = C (T a • r) (T b • s) := by
          rw [hra, hsb]
    _ = T a * T b * C r s := by
          simp [mul_assoc, mul_left_comm]

theorem coordinate_mul_eq_of_bilin_eq_of_ker_eq_bot
    {T : V →ₗ[K] K} (hT : LinearMap.ker T = ⊥)
    (C : V →ₗ[K] Module.Dual K V) {r s a b c d : V}
    (hrs : C r s ≠ 0)
    (habcd : C a b = C c d) :
    T a * T b = T c * T d := by
  have h_ab :=
    coordinate_mul_bilin_eq_coordinate_mul_bilin_of_ker_eq_bot
      (T := T) hT C a b r s
  have h_cd :=
    coordinate_mul_bilin_eq_coordinate_mul_bilin_of_ker_eq_bot
      (T := T) hT C c d r s
  have hmul : T a * T b * C r s = T c * T d * C r s := by
    rw [← h_ab, ← h_cd, habcd]
  exact (mul_right_inj' hrs).mp
    (by simpa [mul_assoc, mul_comm, mul_left_comm] using hmul)

end OneDimensionalCoordinate

section ExactSubspaces

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem exists_submodule_le_finrank_eq_of_le
    (s : Submodule K V) {n : ℕ}
    (hn : n ≤ finrank K s) :
    ∃ t : Submodule K V, t ≤ s ∧ finrank K t = n := by
  classical
  rcases exists_linearIndependent_of_le_finrank (R := K) (M := s) hn with
    ⟨f, hf⟩
  let q : Submodule K s := Submodule.span K (Set.range f)
  let t : Submodule K V := q.map s.subtype
  refine ⟨t, ?_, ?_⟩
  · rintro x ⟨y, _hy, rfl⟩
    exact y.2
  · rw [Submodule.finrank_map_subtype_eq s q]
    have hq :
        Fintype.card (Fin n) = finrank K q := by
      simpa [q] using
        (linearIndependent_iff_card_eq_finrank_span (R := K) (b := f)).mp hf
    simpa using hq.symm

theorem exists_submodule_le_finrank_eq_two
    (s : Submodule K V)
    (hs : 2 ≤ finrank K s) :
    ∃ t : Submodule K V, t ≤ s ∧ finrank K t = 2 :=
  exists_submodule_le_finrank_eq_of_le (K := K) (V := V) s hs

theorem exists_submodule_le_finrank_eq_three
    (s : Submodule K V)
    (hs : 3 ≤ finrank K s) :
    ∃ t : Submodule K V, t ≤ s ∧ finrank K t = 3 :=
  exists_submodule_le_finrank_eq_of_le (K := K) (V := V) s hs

end ExactSubspaces

section MacaulayNumerics

theorem rankTwoMacaulayGrowth_forces_hilbertFirst_le_two
    {h1 h2 h3 : ℕ}
    (hh2 : h2 = 2) (hsymm : h1 = h3) (hgrowth : h3 ≤ h2) :
    h1 ≤ 2 := by
  omega

theorem rankThreeMacaulayNumericalContradiction
    {b : ℕ} (hbpos : 1 ≤ b) (hbtop : b ≤ 3) :
    ¬ 4 - b ≤ 3 - b := by
  omega

theorem rankThreeExactSequenceNumericalContradiction
    {b q2 q3 : ℕ}
    (hbpos : 1 ≤ b) (hbtop : b ≤ 3)
    (hq2 : q2 = 3 - b) (hq3 : q3 = 4 - b)
    (hmac : q3 ≤ q2) :
    False := by
  exact rankThreeMacaulayNumericalContradiction hbpos hbtop (by omega)

theorem rankThreeMacaulayCaseOne :
    ¬ 4 - 1 ≤ (3 - 1 : ℕ) := by
  exact rankThreeMacaulayNumericalContradiction (by norm_num) (by norm_num)

theorem rankThreeMacaulayCaseTwo :
    ¬ 4 - 2 ≤ (3 - 2 : ℕ) := by
  exact rankThreeMacaulayNumericalContradiction (by norm_num) (by norm_num)

theorem rankThreeMacaulayCaseThree :
    ¬ 4 - 3 ≤ (3 - 3 : ℕ) := by
  exact rankThreeMacaulayNumericalContradiction (by norm_num) (by norm_num)

end MacaulayNumerics

end QuaternaryQuartic
