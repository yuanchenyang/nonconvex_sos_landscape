import TernaryQuarticProof.Basic

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace TernaryQuartic

/-
This root file must keep the final theorem declaration so that
`scripts/verify_formalization.sh` passes. All helper lemmas and proof
development should go in the `TernaryQuarticProof/` folder.

The final proof should complete:

`theorem ternaryQuartic_rankFour_no_spurious_socp :
    TernaryQuarticRankFourNoSpuriousSOCP := by ...`
-/

end TernaryQuartic
