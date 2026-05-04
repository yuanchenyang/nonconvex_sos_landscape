import QuaternaryQuarticProof.Syzygy

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace QuaternaryQuartic

theorem exists_linear_combination_lt_zero (a b : ℝ) (hb : b ≠ 0) :
    ∃ t : ℝ, a + 4 * b * t < 0 := by
  refine ⟨-(|a| + 1) / (4 * b), ?_⟩
  have hfour_ne : (4 : ℝ) ≠ 0 := by norm_num
  have hden_ne : 4 * b ≠ 0 := mul_ne_zero hfour_ne hb
  have hmul :
      4 * b * (-(|a| + 1) / (4 * b)) = -(|a| + 1) := by
    field_simp [hden_ne]
  rw [hmul]
  have ha_le_abs : a ≤ |a| := le_abs_self a
  linarith

theorem exists_cubic_tail_lt_zero (b : ℝ) (hb : b ≠ 0) :
    ∃ t : ℝ, 4 * b * (t - t^3) < 0 := by
  by_cases hbpos : 0 < b
  · refine ⟨2, ?_⟩
    nlinarith
  · have hbneg : b < 0 := lt_of_le_of_ne (le_of_not_gt hbpos) hb
    refine ⟨-2, ?_⟩
    nlinarith

theorem exists_quartic_tail_lt_zero_of_nonzero_linear
    (a b : ℝ) (ha : a = 0) (hb : b ≠ 0) :
    ∃ t : ℝ, a * (1 - 6 * t^2 + t^4) + 4 * b * (t - t^3) < 0 := by
  rcases exists_cubic_tail_lt_zero b hb with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  rw [ha]
  simpa using ht

theorem quartic_tail_value_zero (a b : ℝ) :
    a * (1 - 6 * (0 : ℝ)^2 + (0 : ℝ)^4) + 4 * b * ((0 : ℝ) - (0 : ℝ)^3) = a := by
  ring

theorem quartic_tail_value_one (a b : ℝ) :
    a * (1 - 6 * (1 : ℝ)^2 + (1 : ℝ)^4) + 4 * b * ((1 : ℝ) - (1 : ℝ)^3) =
      -4 * a := by
  ring

theorem exists_quartic_tail_lt_zero_of_nonzero_quadratic
    (a b : ℝ) (ha : a ≠ 0) :
    ∃ t : ℝ, a * (1 - 6 * t^2 + t^4) + 4 * b * (t - t^3) < 0 := by
  by_cases hapos : 0 < a
  · refine ⟨1, ?_⟩
    rw [quartic_tail_value_one]
    nlinarith
  · have haneg : a < 0 := lt_of_le_of_ne (le_of_not_gt hapos) ha
    refine ⟨0, ?_⟩
    rw [quartic_tail_value_zero]
    exact haneg

theorem exists_quartic_tail_lt_zero
    (a b : ℝ) (hne : a ≠ 0 ∨ b ≠ 0) :
    ∃ t : ℝ, a * (1 - 6 * t^2 + t^4) + 4 * b * (t - t^3) < 0 := by
  rcases hne with ha | hb
  · exact exists_quartic_tail_lt_zero_of_nonzero_quadratic a b ha
  · by_cases ha : a = 0
    · exact exists_quartic_tail_lt_zero_of_nonzero_linear a b ha hb
    · exact exists_quartic_tail_lt_zero_of_nonzero_quadratic a b ha

end QuaternaryQuartic
