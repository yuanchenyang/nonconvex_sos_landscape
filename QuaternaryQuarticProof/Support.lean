import QuaternaryQuarticProof.Syzygy

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace QuaternaryQuartic

/-- A finite-dimensional interface for the apolar support theorem: there is an
annihilator subspace of affine-linear forms of dimension at least `4 - k`. -/
def HasLinearAnnihilatorCodimAtMost
    (B : DotForm) (p : Poly) (u : RankSevenVec) (k : ℕ) : Prop :=
  ∃ A : Submodule ℝ linSubmodule,
    A ≤ linearAnnihilator B p u ∧
      4 - k ≤ Module.finrank ℝ A

theorem exists_support_complement_of_hasLinearAnnihilatorCodimAtMost
    {B : DotForm} {p : Poly} {u : RankSevenVec} {k : ℕ}
    (hk : k ≤ 4)
    (hsupp : HasLinearAnnihilatorCodimAtMost B p u k) :
    ∃ A W : Submodule ℝ linSubmodule,
      A ≤ linearAnnihilator B p u ∧
        IsCompl A W ∧
          Module.finrank ℝ W ≤ k ∧
            4 - k ≤ Module.finrank ℝ A := by
  rcases hsupp with ⟨A, hAann, hAdim⟩
  rcases exists_isCompl_finrank_add_eq (K := ℝ) (V := linSubmodule) A with
    ⟨W, hAW, hsum⟩
  refine ⟨A, W, hAann, hAW, ?_, hAdim⟩
  have hlin : Module.finrank ℝ linSubmodule = 4 := finrank_linSubmodule_eq_four
  omega

theorem exists_rank_one_support_complement
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupp : HasLinearAnnihilatorCodimAtMost B p u 1) :
    ∃ A W : Submodule ℝ linSubmodule,
      A ≤ linearAnnihilator B p u ∧
        IsCompl A W ∧
          Module.finrank ℝ W ≤ 1 ∧
            3 ≤ Module.finrank ℝ A := by
  simpa using
    exists_support_complement_of_hasLinearAnnihilatorCodimAtMost
      (B := B) (p := p) (u := u) (k := 1) (by norm_num) hsupp

theorem exists_rank_two_support_complement
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupp : HasLinearAnnihilatorCodimAtMost B p u 2) :
    ∃ A W : Submodule ℝ linSubmodule,
      A ≤ linearAnnihilator B p u ∧
        IsCompl A W ∧
          Module.finrank ℝ W ≤ 2 ∧
            2 ≤ Module.finrank ℝ A := by
  simpa using
    exists_support_complement_of_hasLinearAnnihilatorCodimAtMost
      (B := B) (p := p) (u := u) (k := 2) (by norm_num) hsupp

theorem exists_rank_three_support_complement
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupp : HasLinearAnnihilatorCodimAtMost B p u 3) :
    ∃ A W : Submodule ℝ linSubmodule,
      A ≤ linearAnnihilator B p u ∧
        IsCompl A W ∧
          Module.finrank ℝ W ≤ 3 ∧
            1 ≤ Module.finrank ℝ A := by
  simpa using
    exists_support_complement_of_hasLinearAnnihilatorCodimAtMost
      (B := B) (p := p) (u := u) (k := 3) (by norm_num) hsupp

end QuaternaryQuartic
