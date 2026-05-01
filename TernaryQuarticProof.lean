import TernaryQuarticProof.Basic

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace TernaryQuartic

/-
This root file must keep the final theorem declaration so that
`scripts/verify_ternary_quartic.sh` passes. All helper lemmas and proof
development should go in the `TernaryQuarticProof/` folder.

The final proof should complete:

`theorem ternaryQuartic_rankFour_no_spurious_socp :
    TernaryQuarticRankFourNoSpuriousSOCP := by ...`
-/

theorem ternaryQuartic_rankFour_no_spurious_socp :
    TernaryQuarticRankFourNoSpuriousSOCP := by
  intro B p u _hBsymm hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  by_cases hrelker : LinearMap.ker (relationPolyLin u) = ⊥
  · exact residual_eq_zero_of_relationPolyLin_ker_eq_bot
      (B := B) (u := u) hu hrelker hp hsocp
  · rcases Submodule.exists_mem_ne_zero_of_ne_bot hrelker with ⟨c, hc, hcne⟩
    have hrel : relationPoly u c = 0 := by
      simpa [relationPolyLin] using hc
    exact residual_eq_zero_of_constant_relation
      (B := B) (u := u) hu hrel hcne hp hsocp

end TernaryQuartic
