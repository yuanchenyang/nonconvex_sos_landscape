import QuaternaryQuarticProof.Basic

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace QuaternaryQuartic

/-
This root file must keep the final theorem declaration so that
`scripts/verify_quaternary_quartic.sh` can target a stable theorem name.
All helper lemmas and proof development should go in the
`QuaternaryQuarticProof/` folder.

The current implementation is a scaffold: the root theorem is wired through a
temporary placeholder axiom declared in `QuaternaryQuarticProof.Basic`. Future
work should remove that axiom and replace it with a genuine proof.
-/

theorem quaternaryQuartic_rankSeven_no_spurious_socp :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  exact quaternaryQuartic_rankSeven_no_spurious_socp_placeholder

end QuaternaryQuartic
