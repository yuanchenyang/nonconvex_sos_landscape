import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
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

section MacaulayNumerics

theorem rankThreeMacaulayNumericalContradiction
    {b : ℕ} (hbpos : 1 ≤ b) (hbtop : b ≤ 3) :
    ¬ 4 - b ≤ 3 - b := by
  omega

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
