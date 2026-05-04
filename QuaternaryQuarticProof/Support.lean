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

theorem HasLinearAnnihilatorCodimAtMost.mono
    {B : DotForm} {p : Poly} {u : RankSevenVec} {k l : ℕ}
    (hkl : k ≤ l)
    (hsupp : HasLinearAnnihilatorCodimAtMost B p u k) :
    HasLinearAnnihilatorCodimAtMost B p u l := by
  rcases hsupp with ⟨A, hAann, hAdim⟩
  refine ⟨A, hAann, ?_⟩
  have hle : 4 - l ≤ 4 - k := Nat.sub_le_sub_left hkl 4
  exact hle.trans hAdim

theorem HasLinearAnnihilatorCodimAtMost.rank_one_to_two
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupp : HasLinearAnnihilatorCodimAtMost B p u 1) :
    HasLinearAnnihilatorCodimAtMost B p u 2 :=
  HasLinearAnnihilatorCodimAtMost.mono (by norm_num) hsupp

theorem HasLinearAnnihilatorCodimAtMost.rank_two_to_three
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupp : HasLinearAnnihilatorCodimAtMost B p u 2) :
    HasLinearAnnihilatorCodimAtMost B p u 3 :=
  HasLinearAnnihilatorCodimAtMost.mono (by norm_num) hsupp

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

def HasRankThreeAnnihilatorSupportData
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  ∃ (z : linSubmodule) (W : Submodule ℝ linSubmodule) (q : quadSubmodule),
    z ∈ linearAnnihilator B p u ∧
      (z : Poly) ≠ 0 ∧
        q ∈ linProductSubmodule W W ∧
          B (q.1^2) (residual p u) < 0

theorem exists_negative_syzygyCertificate_of_rank_three_supportData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hfocp : IsFOCP B p u)
    (hker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3)
    (hdata : HasRankThreeAnnihilatorSupportData B p u) :
    ∃ q' : Poly, IsQuadratic q' ∧
      B (q'^2) (residual p u) < 0 ∧ HasSyzygyCertificate B p u q' := by
  rcases hdata with ⟨z, W, q, hzann, hzne, hqWW, hneg⟩
  exact exists_negative_syzygyCertificate_of_rank_three_annihilator_support
    (B := B) (p := p) (u := u) (hu := hu) hfocp hker hrank
    hzann hzne hqWW hneg

def HasPreimageProductSupportData
    (B : DotForm) (p : Poly) (u : RankSevenVec)
    (hu : IsAdmissiblePoint u) : Prop :=
  ∃ (x : linSubmodule) (A : Submodule ℝ linSubmodule)
      (S W : Submodule ℝ quadSubmodule) (sdim adim wdim : ℕ),
    A ≤ linearAnnihilator B p u ∧
      S ≤ spanUQuad hu ∧
        S ≤ W ∧
          linProductSubmodule (linProductLeftPreimageWithin x A S) A ≤ W ∧
            linProductLeftPreimageWithin x A S ≠ ⊥ ∧
              sdim ≤ Module.finrank ℝ S ∧
                adim ≤ Module.finrank ℝ A ∧
                  Module.finrank ℝ W = wdim ∧
                    wdim < sdim + adim ∧
                      B ((linProduct x x : quadSubmodule).1^2) (residual p u) < 0

theorem exists_negative_syzygyCertificate_of_preimageProductSupportData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hdata : HasPreimageProductSupportData B p u hu) :
    ∃ q : Poly, IsQuadratic q ∧
      B (q^2) (residual p u) < 0 ∧ HasSyzygyCertificate B p u q := by
  rcases hdata with
    ⟨x, A, S, W, sdim, adim, wdim, hAann, hS_L, hSW, hMAW, hMne,
      hSdim, hAdim, hWdim, hgt, hneg⟩
  exact exists_negative_syzygyCertificate_of_preimage_product_dimension_of_annihilator
    (B := B) (p := p) (u := u) (hu := hu)
    (x := x) (A := A) (S := S) (W := W)
    hS_L hAann hSW hMAW hMne hSdim hAdim hWdim hgt hneg

end QuaternaryQuartic
