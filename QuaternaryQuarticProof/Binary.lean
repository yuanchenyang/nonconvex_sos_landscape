import QuaternaryQuarticProof.Syzygy

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace QuaternaryQuartic

def binaryQuarticEval (a b c d e x y : ℝ) : ℝ :=
  a * x^4 + 4 * b * x^3 * y + 6 * c * x^2 * y^2 + 4 * d * x * y^3 + e * y^4

theorem diagonal_form_negative_pure_of_negative
    {a e : ℝ} (hneg : ∃ x y : ℝ, a * x^2 + e * y^2 < 0) :
    a < 0 ∨ e < 0 := by
  rcases hneg with ⟨x, y, hxy⟩
  by_contra hnone
  push Not at hnone
  have hx2 : 0 ≤ x^2 := sq_nonneg x
  have hy2 : 0 ≤ y^2 := sq_nonneg y
  have hax : 0 ≤ a * x^2 := mul_nonneg hnone.1 hx2
  have hey : 0 ≤ e * y^2 := mul_nonneg hnone.2 hy2
  nlinarith

theorem diagonal_form_exists_pure_negative
    {a e : ℝ} (hneg : ∃ x y : ℝ, a * x^2 + e * y^2 < 0) :
    (a < 0 ∧ a * (1 : ℝ)^2 < 0) ∨ (e < 0 ∧ e * (1 : ℝ)^2 < 0) := by
  rcases diagonal_form_negative_pure_of_negative hneg with ha | he
  · exact Or.inl ⟨ha, by simpa using ha⟩
  · exact Or.inr ⟨he, by simpa using he⟩

theorem diagonal_binaryQuarticEval_exists_negative
    {a e : ℝ} (hneg : ∃ x y : ℝ, a * x^2 + e * y^2 < 0) :
    ∃ x y : ℝ, binaryQuarticEval a 0 0 0 e x y < 0 := by
  rcases diagonal_form_negative_pure_of_negative hneg with ha | he
  · exact ⟨1, 0, by simpa [binaryQuarticEval] using ha⟩
  · exact ⟨0, 1, by simpa [binaryQuarticEval] using he⟩

theorem rank_one_negative_value
    {ρ α β : ℝ} (hρ : ρ < 0) (hvec : α ≠ 0 ∨ β ≠ 0) :
    ρ * (α^2 + β^2)^2 < 0 := by
  have hsum_pos : 0 < α^2 + β^2 := by
    rcases hvec with hα | hβ
    · nlinarith [sq_pos_of_ne_zero hα, sq_nonneg β]
    · nlinarith [sq_nonneg α, sq_pos_of_ne_zero hβ]
  have hsquare_pos : 0 < (α^2 + β^2)^2 := sq_pos_of_pos hsum_pos
  exact mul_neg_of_neg_of_pos hρ hsquare_pos

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

theorem y_sq_kernel_binaryQuarticEval_exists_negative
    (a b : ℝ) (hb : b ≠ 0) :
    ∃ x y : ℝ, binaryQuarticEval a b 0 0 0 x y < 0 := by
  rcases exists_linear_combination_lt_zero a b hb with ⟨t, ht⟩
  refine ⟨1, t, ?_⟩
  simpa [binaryQuarticEval, mul_assoc] using ht

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

theorem elliptic_kernel_binaryQuarticEval_exists_negative
    (a b : ℝ) (hne : a ≠ 0 ∨ b ≠ 0) :
    ∃ x y : ℝ, binaryQuarticEval a b (-a) (-b) a x y < 0 := by
  rcases exists_quartic_tail_lt_zero a b hne with ⟨t, ht⟩
  refine ⟨1, t, ?_⟩
  have heq :
      binaryQuarticEval a b (-a) (-b) a 1 t =
        a * (1 - 6 * t^2 + t^4) + 4 * b * (t - t^3) := by
    unfold binaryQuarticEval
    ring_nf
  rwa [heq]

end QuaternaryQuartic
