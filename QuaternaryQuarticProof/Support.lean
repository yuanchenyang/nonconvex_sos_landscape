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

theorem hasLinearAnnihilatorCodimAtMost_of_annihilatorMap_range
    {B : DotForm} {p : Poly} {u : RankSevenVec} {k : ℕ}
    (hk : k ≤ 4)
    (hrange :
      Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ k) :
    HasLinearAnnihilatorCodimAtMost B p u k := by
  refine ⟨linearAnnihilator B p u, le_rfl, ?_⟩
  have hsum :=
    finrank_range_linearAnnihilatorMap_add_finrank_linearAnnihilator B p u
  omega

theorem hasLinearAnnihilatorCodimAtMost_one_of_annihilatorMap_range
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hrange :
      Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 1) :
    HasLinearAnnihilatorCodimAtMost B p u 1 :=
  hasLinearAnnihilatorCodimAtMost_of_annihilatorMap_range
    (B := B) (p := p) (u := u) (k := 1) (by norm_num) hrange

theorem hasLinearAnnihilatorCodimAtMost_two_of_annihilatorMap_range
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hrange :
      Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 2) :
    HasLinearAnnihilatorCodimAtMost B p u 2 :=
  hasLinearAnnihilatorCodimAtMost_of_annihilatorMap_range
    (B := B) (p := p) (u := u) (k := 2) (by norm_num) hrange

theorem hasLinearAnnihilatorCodimAtMost_three_of_annihilatorMap_range
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hrange :
      Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 3) :
    HasLinearAnnihilatorCodimAtMost B p u 3 :=
  hasLinearAnnihilatorCodimAtMost_of_annihilatorMap_range
    (B := B) (p := p) (u := u) (k := 3) (by norm_num) hrange

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

theorem exists_support_complement_kernel_product_of_hasLinearAnnihilatorCodimAtMost
    {B : DotForm} {p : Poly} {u : RankSevenVec} {k : ℕ}
    (hk : k ≤ 4)
    (hsupp : HasLinearAnnihilatorCodimAtMost B p u k) :
    ∃ A W : Submodule ℝ linSubmodule,
      IsCompl A W ∧
        Module.finrank ℝ W ≤ k ∧
          4 - k ≤ Module.finrank ℝ A ∧
            linProductSubmodule A ⊤ ≤ LinearMap.ker (catalecticantMap B p u) := by
  rcases exists_support_complement_of_hasLinearAnnihilatorCodimAtMost
      (B := B) (p := p) (u := u) (k := k) hk hsupp with
    ⟨A, W, hAann, hAW, hWdim, hAdim⟩
  exact ⟨A, W, hAW, hWdim, hAdim,
    linProductSubmodule_le_ker_of_le_linearAnnihilator hAann⟩

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

theorem exists_rank_one_support_kernel_product
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupp : HasLinearAnnihilatorCodimAtMost B p u 1) :
    ∃ A W : Submodule ℝ linSubmodule,
      IsCompl A W ∧
        Module.finrank ℝ W ≤ 1 ∧
          3 ≤ Module.finrank ℝ A ∧
            linProductSubmodule A ⊤ ≤ LinearMap.ker (catalecticantMap B p u) := by
  simpa using
    exists_support_complement_kernel_product_of_hasLinearAnnihilatorCodimAtMost
      (B := B) (p := p) (u := u) (k := 1) (by norm_num) hsupp

theorem exists_rank_two_support_kernel_product
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupp : HasLinearAnnihilatorCodimAtMost B p u 2) :
    ∃ A W : Submodule ℝ linSubmodule,
      IsCompl A W ∧
        Module.finrank ℝ W ≤ 2 ∧
          2 ≤ Module.finrank ℝ A ∧
            linProductSubmodule A ⊤ ≤ LinearMap.ker (catalecticantMap B p u) := by
  simpa using
    exists_support_complement_kernel_product_of_hasLinearAnnihilatorCodimAtMost
      (B := B) (p := p) (u := u) (k := 2) (by norm_num) hsupp

theorem exists_rank_three_support_kernel_product
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupp : HasLinearAnnihilatorCodimAtMost B p u 3) :
    ∃ A W : Submodule ℝ linSubmodule,
      IsCompl A W ∧
        Module.finrank ℝ W ≤ 3 ∧
          1 ≤ Module.finrank ℝ A ∧
            linProductSubmodule A ⊤ ≤ LinearMap.ker (catalecticantMap B p u) := by
  simpa using
    exists_support_complement_kernel_product_of_hasLinearAnnihilatorCodimAtMost
      (B := B) (p := p) (u := u) (k := 3) (by norm_num) hsupp

theorem exists_nonzero_mem_linearAnnihilator_of_rank_three_support
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupp : HasLinearAnnihilatorCodimAtMost B p u 3) :
    ∃ z : linSubmodule, z ∈ linearAnnihilator B p u ∧ (z : Poly) ≠ 0 := by
  rcases hsupp with ⟨A, hAann, hAdim⟩
  have hAdim_one : 1 ≤ Module.finrank ℝ A := by
    simpa using hAdim
  have hAne : A ≠ ⊥ := by
    intro hA_bot
    have hfin : Module.finrank ℝ A = 0 := by
      rw [hA_bot]
      simp
    omega
  rcases Submodule.exists_mem_ne_zero_of_ne_bot hAne with ⟨z, hzA, hzne⟩
  refine ⟨z, hAann hzA, ?_⟩
  intro hzpoly
  exact hzne (Subtype.ext hzpoly)

def HasRankThreeAnnihilatorSupportData
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  ∃ (z : linSubmodule) (W : Submodule ℝ linSubmodule) (q : quadSubmodule),
    z ∈ linearAnnihilator B p u ∧
      (z : Poly) ≠ 0 ∧
        q ∈ linProductSubmodule W W ∧
          B (q.1^2) (residual p u) < 0

theorem hasRankThreeAnnihilatorSupportData_of_rank_three_support
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupp : HasLinearAnnihilatorCodimAtMost B p u 3)
    {W : Submodule ℝ linSubmodule} {q : quadSubmodule}
    (hqWW : q ∈ linProductSubmodule W W)
    (hneg : B (q.1^2) (residual p u) < 0) :
    HasRankThreeAnnihilatorSupportData B p u := by
  rcases exists_nonzero_mem_linearAnnihilator_of_rank_three_support hsupp with
    ⟨z, hzann, hzne⟩
  exact ⟨z, W, q, hzann, hzne, hqWW, hneg⟩

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

theorem exists_negative_syzygyCertificate_of_rank_three_support
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hfocp : IsFOCP B p u)
    (hker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3)
    (hsupp : HasLinearAnnihilatorCodimAtMost B p u 3)
    {W : Submodule ℝ linSubmodule} {q : quadSubmodule}
    (hqWW : q ∈ linProductSubmodule W W)
    (hneg : B (q.1^2) (residual p u) < 0) :
    ∃ q' : Poly, IsQuadratic q' ∧
      B (q'^2) (residual p u) < 0 ∧ HasSyzygyCertificate B p u q' :=
  exists_negative_syzygyCertificate_of_rank_three_supportData
    (B := B) (p := p) (u := u) hu hfocp hker hrank
    (hasRankThreeAnnihilatorSupportData_of_rank_three_support
      (B := B) (p := p) (u := u) hsupp hqWW hneg)

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

theorem hasPreimageProductSupportData_of_dimension
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    {x : linSubmodule} {A : Submodule ℝ linSubmodule}
    {S W : Submodule ℝ quadSubmodule} {sdim adim wdim : ℕ}
    (hx : (x : Poly) ≠ 0)
    (hAann : A ≤ linearAnnihilator B p u)
    (hS_L : S ≤ spanUQuad hu)
    (hSW : S ≤ W)
    (hrangeW : LinearMap.range (linProductLeftMapOn x A) ≤ W)
    (hMAW : linProductSubmodule (linProductLeftPreimageWithin x A S) A ≤ W)
    (hSdim : sdim ≤ Module.finrank ℝ S)
    (hAdim : adim ≤ Module.finrank ℝ A)
    (hWdim : Module.finrank ℝ W = wdim)
    (hgt : wdim < sdim + adim)
    (hneg : B ((linProduct x x : quadSubmodule).1^2) (residual p u) < 0) :
    HasPreimageProductSupportData B p u hu := by
  refine ⟨x, A, S, W, sdim, adim, wdim, hAann, hS_L, hSW,
    hMAW, ?_, hSdim, hAdim, hWdim, hgt, hneg⟩
  exact linProductLeftPreimageWithin_ne_bot_of_finrank_lt_add
    hx hSW hrangeW hSdim hAdim hWdim hgt

theorem hasPreimageProductSupportData_of_dimension_le
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    {x : linSubmodule} {A : Submodule ℝ linSubmodule}
    {S W : Submodule ℝ quadSubmodule} {sdim adim wdim : ℕ}
    (hx : (x : Poly) ≠ 0)
    (hAann : A ≤ linearAnnihilator B p u)
    (hS_L : S ≤ spanUQuad hu)
    (hSW : S ≤ W)
    (hrangeW : LinearMap.range (linProductLeftMapOn x A) ≤ W)
    (hMAW : linProductSubmodule (linProductLeftPreimageWithin x A S) A ≤ W)
    (hSdim : sdim ≤ Module.finrank ℝ S)
    (hAdim : adim ≤ Module.finrank ℝ A)
    (hWdim : Module.finrank ℝ W ≤ wdim)
    (hgt : wdim < sdim + adim)
    (hneg : B ((linProduct x x : quadSubmodule).1^2) (residual p u) < 0) :
    HasPreimageProductSupportData B p u hu := by
  refine ⟨x, A, S, W, sdim, adim, Module.finrank ℝ W,
    hAann, hS_L, hSW, hMAW, ?_, hSdim, hAdim, rfl, ?_, hneg⟩
  · exact linProductLeftPreimageWithin_ne_bot_of_finrank_le_lt_add
      hx hSW hrangeW hSdim hAdim hWdim hgt
  · exact lt_of_le_of_lt hWdim hgt

theorem hasPreimageProductSupportData_of_rank_two_dimensions
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    {x : linSubmodule} {A : Submodule ℝ linSubmodule}
    {S W : Submodule ℝ quadSubmodule}
    (hx : (x : Poly) ≠ 0)
    (hAann : A ≤ linearAnnihilator B p u)
    (hS_L : S ≤ spanUQuad hu)
    (hSW : S ≤ W)
    (hrangeW : LinearMap.range (linProductLeftMapOn x A) ≤ W)
    (hMAW : linProductSubmodule (linProductLeftPreimageWithin x A S) A ≤ W)
    (hSdim : 4 ≤ Module.finrank ℝ S)
    (hAdim : 2 ≤ Module.finrank ℝ A)
    (hWdim : Module.finrank ℝ W = 5)
    (hneg : B ((linProduct x x : quadSubmodule).1^2) (residual p u) < 0) :
    HasPreimageProductSupportData B p u hu :=
  hasPreimageProductSupportData_of_dimension
    (B := B) (p := p) (u := u) (hu := hu)
    (x := x) (A := A) (S := S) (W := W)
    (sdim := 4) (adim := 2) (wdim := 5)
    hx hAann hS_L hSW hrangeW hMAW hSdim hAdim hWdim (by norm_num) hneg

theorem hasPreimageProductSupportData_of_rank_two_dimension_bounds
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    {x : linSubmodule} {A : Submodule ℝ linSubmodule}
    {S W : Submodule ℝ quadSubmodule}
    (hx : (x : Poly) ≠ 0)
    (hAann : A ≤ linearAnnihilator B p u)
    (hS_L : S ≤ spanUQuad hu)
    (hSW : S ≤ W)
    (hrangeW : LinearMap.range (linProductLeftMapOn x A) ≤ W)
    (hMAW : linProductSubmodule (linProductLeftPreimageWithin x A S) A ≤ W)
    (hSdim : 4 ≤ Module.finrank ℝ S)
    (hAdim : 2 ≤ Module.finrank ℝ A)
    (hWdim : Module.finrank ℝ W ≤ 5)
    (hneg : B ((linProduct x x : quadSubmodule).1^2) (residual p u) < 0) :
    HasPreimageProductSupportData B p u hu :=
  hasPreimageProductSupportData_of_dimension_le
    (B := B) (p := p) (u := u) (hu := hu)
    (x := x) (A := A) (S := S) (W := W)
    (sdim := 4) (adim := 2) (wdim := 5)
    hx hAann hS_L hSW hrangeW hMAW hSdim hAdim hWdim (by norm_num) hneg

theorem hasPreimageProductSupportData_of_rank_one_dimensions
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    {x : linSubmodule} {A : Submodule ℝ linSubmodule}
    {S W : Submodule ℝ quadSubmodule}
    (hx : (x : Poly) ≠ 0)
    (hAann : A ≤ linearAnnihilator B p u)
    (hS_L : S ≤ spanUQuad hu)
    (hSW : S ≤ W)
    (hrangeW : LinearMap.range (linProductLeftMapOn x A) ≤ W)
    (hMAW : linProductSubmodule (linProductLeftPreimageWithin x A S) A ≤ W)
    (hSdim : 4 ≤ Module.finrank ℝ S)
    (hAdim : 3 ≤ Module.finrank ℝ A)
    (hWdim : Module.finrank ℝ W = 6)
    (hneg : B ((linProduct x x : quadSubmodule).1^2) (residual p u) < 0) :
    HasPreimageProductSupportData B p u hu :=
  hasPreimageProductSupportData_of_dimension
    (B := B) (p := p) (u := u) (hu := hu)
    (x := x) (A := A) (S := S) (W := W)
    (sdim := 4) (adim := 3) (wdim := 6)
    hx hAann hS_L hSW hrangeW hMAW hSdim hAdim hWdim (by norm_num) hneg

theorem hasPreimageProductSupportData_of_rank_one_dimension_bounds
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    {x : linSubmodule} {A : Submodule ℝ linSubmodule}
    {S W : Submodule ℝ quadSubmodule}
    (hx : (x : Poly) ≠ 0)
    (hAann : A ≤ linearAnnihilator B p u)
    (hS_L : S ≤ spanUQuad hu)
    (hSW : S ≤ W)
    (hrangeW : LinearMap.range (linProductLeftMapOn x A) ≤ W)
    (hMAW : linProductSubmodule (linProductLeftPreimageWithin x A S) A ≤ W)
    (hSdim : 4 ≤ Module.finrank ℝ S)
    (hAdim : 3 ≤ Module.finrank ℝ A)
    (hWdim : Module.finrank ℝ W ≤ 6)
    (hneg : B ((linProduct x x : quadSubmodule).1^2) (residual p u) < 0) :
    HasPreimageProductSupportData B p u hu :=
  hasPreimageProductSupportData_of_dimension_le
    (B := B) (p := p) (u := u) (hu := hu)
    (x := x) (A := A) (S := S) (W := W)
    (sdim := 4) (adim := 3) (wdim := 6)
    hx hAann hS_L hSW hrangeW hMAW hSdim hAdim hWdim (by norm_num) hneg

theorem hasPreimageProductSupportData_of_rank_two_ambient_bounds
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hfocp : IsFOCP B p u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2)
    {x : linSubmodule} {A : Submodule ℝ linSubmodule}
    {U : Submodule ℝ quadSubmodule}
    (hx : (x : Poly) ≠ 0)
    (hAann : A ≤ linearAnnihilator B p u)
    (hUker : U ≤ LinearMap.ker (catalecticantMap B p u))
    (hUdim_ge : 5 ≤ Module.finrank ℝ U)
    (hUdim_le : Module.finrank ℝ U ≤ 5)
    (hrangeU : LinearMap.range (linProductLeftMapOn x A) ≤ U)
    (hMAU :
      linProductSubmodule
          (linProductLeftPreimageWithin x A (spanUQuad hu ⊓ U)) A ≤ U)
    (hAdim : 2 ≤ Module.finrank ℝ A)
    (hneg : B ((linProduct x x : quadSubmodule).1^2) (residual p u) < 0) :
    HasPreimageProductSupportData B p u hu := by
  have hSdim :
      4 ≤ Module.finrank ℝ ↥(spanUQuad hu ⊓ U) :=
    four_le_finrank_spanUQuad_inf_of_rank_two_ambient
      (B := B) (p := p) (u := u) hu hfocp hrelker hrank hUker hUdim_ge
  exact hasPreimageProductSupportData_of_rank_two_dimension_bounds
    (B := B) (p := p) (u := u) (hu := hu)
    (x := x) (A := A) (S := spanUQuad hu ⊓ U) (W := U)
    hx hAann inf_le_left inf_le_right hrangeU hMAU hSdim hAdim hUdim_le hneg

theorem hasPreimageProductSupportData_of_rank_two_supportAmbient
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hfocp : IsFOCP B p u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2)
    {x : linSubmodule} {A : Submodule ℝ linSubmodule}
    (hx : (x : Poly) ≠ 0)
    (hAann : A ≤ linearAnnihilator B p u)
    (hUker : supportAmbient x A ≤ LinearMap.ker (catalecticantMap B p u))
    (hUdim_ge : 5 ≤ Module.finrank ℝ (supportAmbient x A))
    (hrangeDim : Module.finrank ℝ (LinearMap.range (linProductLeftMapOn x A)) ≤ 2)
    (hsymDim : Module.finrank ℝ (symSquareSubmodule A) ≤ 3)
    (hAdim : 2 ≤ Module.finrank ℝ A)
    (hneg : B ((linProduct x x : quadSubmodule).1^2) (residual p u) < 0) :
    HasPreimageProductSupportData B p u hu := by
  exact hasPreimageProductSupportData_of_rank_two_ambient_bounds
    (B := B) (p := p) (u := u) (hu := hu)
    hfocp hrelker hrank
    (x := x) (A := A) (U := supportAmbient x A)
    hx hAann hUker hUdim_ge
    (finrank_supportAmbient_le_five (x := x) (A := A) hrangeDim hsymDim)
    (range_linProductLeftMapOn_le_supportAmbient x A)
    (linProductSubmodule_leftPreimageWithin_le_supportAmbient
      x A (spanUQuad hu ⊓ supportAmbient x A))
    hAdim hneg

theorem hasPreimageProductSupportData_of_rank_one_ambient_bounds
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hfocp : IsFOCP B p u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1)
    {x : linSubmodule} {A : Submodule ℝ linSubmodule}
    {U : Submodule ℝ quadSubmodule}
    (hx : (x : Poly) ≠ 0)
    (hAann : A ≤ linearAnnihilator B p u)
    (hUker : U ≤ LinearMap.ker (catalecticantMap B p u))
    (hUdim_ge : 6 ≤ Module.finrank ℝ U)
    (hUdim_le : Module.finrank ℝ U ≤ 6)
    (hrangeU : LinearMap.range (linProductLeftMapOn x A) ≤ U)
    (hMAU :
      linProductSubmodule
          (linProductLeftPreimageWithin x A (spanUQuad hu ⊓ U)) A ≤ U)
    (hAdim : 3 ≤ Module.finrank ℝ A)
    (hneg : B ((linProduct x x : quadSubmodule).1^2) (residual p u) < 0) :
    HasPreimageProductSupportData B p u hu := by
  have hSdim :
      4 ≤ Module.finrank ℝ ↥(spanUQuad hu ⊓ U) :=
    four_le_finrank_spanUQuad_inf_of_rank_one_ambient
      (B := B) (p := p) (u := u) hu hfocp hrelker hrank hUker hUdim_ge
  exact hasPreimageProductSupportData_of_rank_one_dimension_bounds
    (B := B) (p := p) (u := u) (hu := hu)
    (x := x) (A := A) (S := spanUQuad hu ⊓ U) (W := U)
    hx hAann inf_le_left inf_le_right hrangeU hMAU hSdim hAdim hUdim_le hneg

end QuaternaryQuartic
