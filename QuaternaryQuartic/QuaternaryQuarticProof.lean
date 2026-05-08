import QuaternaryQuartic.QuaternaryQuarticProof.Basic

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace QuaternaryQuartic

/-
This root file keeps the final theorem declaration so that
`QuaternaryQuartic/verify.sh` can target a stable theorem name.
All helper lemmas and proof development live in the
`QuaternaryQuartic/QuaternaryQuarticProof/` folder.
-/

theorem quaternaryQuartic_rankSeven_no_spurious_socp :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  exact quaternaryQuartic_rankSeven_no_spurious_socp_of_globalRankThreeBadBranch
    globalRankThreeApolarBadBranchContradiction_direct

end QuaternaryQuartic
