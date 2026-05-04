import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

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

end Grassmann

end QuaternaryQuartic
