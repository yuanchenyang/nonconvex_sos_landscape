import QuaternaryQuarticProof.Binary

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

theorem annihilatorMap_range_le_of_hasLinearAnnihilatorCodimAtMost
    {B : DotForm} {p : Poly} {u : RankSevenVec} {k : ℕ}
    (hk : k ≤ 4)
    (hsupp : HasLinearAnnihilatorCodimAtMost B p u k) :
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ k := by
  rcases hsupp with ⟨A, hAann, hAdim⟩
  have hAfin_le :
      Module.finrank ℝ A ≤ Module.finrank ℝ (linearAnnihilator B p u) :=
    Submodule.finrank_mono hAann
  have hsum :=
    finrank_range_linearAnnihilatorMap_add_finrank_linearAnnihilator B p u
  omega

theorem annihilatorMap_range_le_one_of_hasLinearAnnihilatorCodimAtMost
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupp : HasLinearAnnihilatorCodimAtMost B p u 1) :
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 1 :=
  annihilatorMap_range_le_of_hasLinearAnnihilatorCodimAtMost
    (B := B) (p := p) (u := u) (k := 1) (by norm_num) hsupp

theorem annihilatorMap_range_le_two_of_hasLinearAnnihilatorCodimAtMost
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupp : HasLinearAnnihilatorCodimAtMost B p u 2) :
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 2 :=
  annihilatorMap_range_le_of_hasLinearAnnihilatorCodimAtMost
    (B := B) (p := p) (u := u) (k := 2) (by norm_num) hsupp

theorem annihilatorMap_range_le_three_of_hasLinearAnnihilatorCodimAtMost
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupp : HasLinearAnnihilatorCodimAtMost B p u 3) :
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 3 :=
  annihilatorMap_range_le_of_hasLinearAnnihilatorCodimAtMost
    (B := B) (p := p) (u := u) (k := 3) (by norm_num) hsupp

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

theorem exists_rank_one_exact_annihilator
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupp : HasLinearAnnihilatorCodimAtMost B p u 1) :
    ∃ A : Submodule ℝ linSubmodule,
      A ≤ linearAnnihilator B p u ∧ Module.finrank ℝ A = 3 := by
  rcases hsupp with ⟨A₀, hAann, hAdim⟩
  rcases exists_submodule_le_finrank_eq_three A₀ hAdim with
    ⟨A, hAA₀, hAfin⟩
  exact ⟨A, hAA₀.trans hAann, hAfin⟩

theorem exists_rank_one_exact_annihilator_complement
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupp : HasLinearAnnihilatorCodimAtMost B p u 1) :
    ∃ A W : Submodule ℝ linSubmodule,
      A ≤ linearAnnihilator B p u ∧
        IsCompl A W ∧
          Module.finrank ℝ A = 3 ∧
            Module.finrank ℝ W = 1 := by
  rcases exists_rank_one_exact_annihilator
      (B := B) (p := p) (u := u) hsupp with
    ⟨A, hAann, hAfin⟩
  rcases exists_isCompl_finrank_add_eq (K := ℝ) (V := linSubmodule) A with
    ⟨W, hAW, hsum⟩
  refine ⟨A, W, hAann, hAW, hAfin, ?_⟩
  have hlin : Module.finrank ℝ linSubmodule = 4 := finrank_linSubmodule_eq_four
  omega

theorem exists_rank_one_exact_annihilator_complement_vector
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupp : HasLinearAnnihilatorCodimAtMost B p u 1) :
    ∃ A W : Submodule ℝ linSubmodule,
      ∃ x : linSubmodule,
        A ≤ linearAnnihilator B p u ∧
          IsCompl A W ∧
            x ∈ W ∧
              (x : Poly) ≠ 0 ∧
                x ∉ A ∧
                  Module.finrank ℝ A = 3 ∧
                    Module.finrank ℝ W = 1 := by
  rcases exists_rank_one_exact_annihilator_complement
      (B := B) (p := p) (u := u) hsupp with
    ⟨A, W, hAann, hAW, hAfin, hWfin⟩
  have hWpos : 0 < Module.finrank ℝ W := by omega
  rcases exists_mem_ne_zero_of_finrank_pos (K := ℝ) (V := linSubmodule)
      (s := W) hWpos with
    ⟨x, hxW, hxne⟩
  refine ⟨A, W, x, hAann, hAW, hxW, ?_, ?_, hAfin, hWfin⟩
  · intro hxpoly
    exact hxne (Subtype.ext hxpoly)
  · exact not_mem_left_of_isCompl_right_mem_ne_zero hAW hxW hxne

theorem exists_rank_two_exact_annihilator
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupp : HasLinearAnnihilatorCodimAtMost B p u 2) :
    ∃ A : Submodule ℝ linSubmodule,
      A ≤ linearAnnihilator B p u ∧ Module.finrank ℝ A = 2 := by
  rcases hsupp with ⟨A₀, hAann, hAdim⟩
  rcases exists_submodule_le_finrank_eq_two A₀ hAdim with
    ⟨A, hAA₀, hAfin⟩
  exact ⟨A, hAA₀.trans hAann, hAfin⟩

theorem exists_rank_two_exact_annihilator_complement
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupp : HasLinearAnnihilatorCodimAtMost B p u 2) :
    ∃ A W : Submodule ℝ linSubmodule,
      A ≤ linearAnnihilator B p u ∧
        IsCompl A W ∧
          Module.finrank ℝ A = 2 ∧
            Module.finrank ℝ W = 2 := by
  rcases exists_rank_two_exact_annihilator
      (B := B) (p := p) (u := u) hsupp with
    ⟨A, hAann, hAfin⟩
  rcases exists_isCompl_finrank_add_eq (K := ℝ) (V := linSubmodule) A with
    ⟨W, hAW, hsum⟩
  refine ⟨A, W, hAann, hAW, hAfin, ?_⟩
  have hlin : Module.finrank ℝ linSubmodule = 4 := finrank_linSubmodule_eq_four
  omega

theorem exists_rank_two_exact_annihilator_complement_vector
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupp : HasLinearAnnihilatorCodimAtMost B p u 2) :
    ∃ A W : Submodule ℝ linSubmodule,
      ∃ x : linSubmodule,
        A ≤ linearAnnihilator B p u ∧
          IsCompl A W ∧
            x ∈ W ∧
              (x : Poly) ≠ 0 ∧
                x ∉ A ∧
                  Module.finrank ℝ A = 2 ∧
                    Module.finrank ℝ W = 2 := by
  rcases exists_rank_two_exact_annihilator_complement
      (B := B) (p := p) (u := u) hsupp with
    ⟨A, W, hAann, hAW, hAfin, hWfin⟩
  have hWpos : 0 < Module.finrank ℝ W := by omega
  rcases exists_mem_ne_zero_of_finrank_pos (K := ℝ) (V := linSubmodule)
      (s := W) hWpos with
    ⟨x, hxW, hxne⟩
  refine ⟨A, W, x, hAann, hAW, hxW, ?_, ?_, hAfin, hWfin⟩
  · intro hxpoly
    exact hxne (Subtype.ext hxpoly)
  · exact not_mem_left_of_isCompl_right_mem_ne_zero hAW hxW hxne

theorem exists_rank_two_exact_annihilator_supportAmbient
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupp : HasLinearAnnihilatorCodimAtMost B p u 2)
    (x : linSubmodule) :
    ∃ A : Submodule ℝ linSubmodule,
      A ≤ linearAnnihilator B p u ∧
        Module.finrank ℝ A = 2 ∧
          supportAmbient x A ≤ LinearMap.ker (catalecticantMap B p u) ∧
            Module.finrank ℝ (supportAmbient x A) ≤ 5 := by
  rcases exists_rank_two_exact_annihilator
      (B := B) (p := p) (u := u) hsupp with
    ⟨A, hAann, hAfin⟩
  exact ⟨A, hAann, hAfin,
    supportAmbient_le_ker_of_le_linearAnnihilator
      (B := B) (p := p) (u := u) (x := x) hAann,
    finrank_supportAmbient_le_five_of_finrank_eq_two (x := x) hAfin⟩

def HasRankOneBinaryRestrictionComponentData
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  ∃ A W : Submodule ℝ linSubmodule,
    ∃ x y : linSubmodule,
      A ≤ linearAnnihilator B p u ∧
        IsCompl A W ∧
          x ∈ W ∧
            (x : Poly) ≠ 0 ∧
              Module.finrank ℝ A = 3 ∧
                Module.finrank ℝ W = 1 ∧
                  Module.finrank ℝ (symSquareSubmodule A) = 6 ∧
                    HasBinaryLowRankNegativeNormalForm
                      (binaryRestrictionCoeffA B p u x)
                      (binaryRestrictionCoeffB B p u x y)
                      (binaryRestrictionCoeffC B p u x y)
                      (binaryRestrictionCoeffD B p u x y)
                      (binaryRestrictionCoeffE B p u y)

def HasRankTwoBinaryRestrictionComponentData
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  ∃ A W : Submodule ℝ linSubmodule,
    ∃ x y : linSubmodule,
      A ≤ linearAnnihilator B p u ∧
        IsCompl A W ∧
          x ∈ W ∧
            y ∈ W ∧
              (x : Poly) ≠ 0 ∧
                Module.finrank ℝ A = 2 ∧
                  Module.finrank ℝ W = 2 ∧
                    Module.finrank ℝ (symSquareSubmodule A) = 3 ∧
                      HasBinaryLowRankNegativeNormalForm
                        (binaryRestrictionCoeffA B p u x)
                        (binaryRestrictionCoeffB B p u x y)
                        (binaryRestrictionCoeffC B p u x y)
                        (binaryRestrictionCoeffD B p u x y)
                        (binaryRestrictionCoeffE B p u y) ∧
                        ∀ z : linSubmodule,
                          z ∈ W →
                            (z : Poly) ≠ 0 →
                              LinearMap.range (linProductLeftMapOn z A) ⊓
                                  symSquareSubmodule A =
                                ⊥

def HasRankOneSupportComponentHypothesis
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  ∀ (A W : Submodule ℝ linSubmodule) (x : linSubmodule),
    A ≤ linearAnnihilator B p u →
      IsCompl A W →
        x ∈ W →
          (x : Poly) ≠ 0 →
            Module.finrank ℝ A = 3 →
              Module.finrank ℝ W = 1 →
                ∃ y : linSubmodule,
                  Module.finrank ℝ (symSquareSubmodule A) = 6 ∧
                    HasBinaryLowRankNegativeNormalForm
                      (binaryRestrictionCoeffA B p u x)
                      (binaryRestrictionCoeffB B p u x y)
                      (binaryRestrictionCoeffC B p u x y)
                      (binaryRestrictionCoeffD B p u x y)
                      (binaryRestrictionCoeffE B p u y)

def HasRankTwoSupportComponentHypothesis
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  ∀ (A W : Submodule ℝ linSubmodule) (x : linSubmodule),
    A ≤ linearAnnihilator B p u →
      IsCompl A W →
        x ∈ W →
          (x : Poly) ≠ 0 →
            Module.finrank ℝ A = 2 →
              Module.finrank ℝ W = 2 →
                ∃ y : linSubmodule,
                  y ∈ W ∧
                    Module.finrank ℝ (symSquareSubmodule A) = 3 ∧
                      HasBinaryLowRankNegativeNormalForm
                        (binaryRestrictionCoeffA B p u x)
                        (binaryRestrictionCoeffB B p u x y)
                        (binaryRestrictionCoeffC B p u x y)
                        (binaryRestrictionCoeffD B p u x y)
                        (binaryRestrictionCoeffE B p u y) ∧
                        ∀ z : linSubmodule,
                          z ∈ W →
                            (z : Poly) ≠ 0 →
                              LinearMap.range (linProductLeftMapOn z A) ⊓
                                  symSquareSubmodule A =
                                ⊥

theorem exists_rank_two_complement_second_direction
    {W : Submodule ℝ linSubmodule} {x : linSubmodule}
    (hx : (x : Poly) ≠ 0)
    (hW : Module.finrank ℝ W = 2) :
    ∃ y : linSubmodule, y ∈ W ∧ y ∉ ℝ ∙ x :=
  exists_mem_notMem_span_singleton_of_finrank_two
    (K := ℝ) (V := linSubmodule)
    (W := W) (x := x)
    (by
      intro h
      exact hx (congrArg (fun z : linSubmodule => (z : Poly)) h))
    hW

theorem finrank_span_rank_two_support_pair_eq_two
    {x y : linSubmodule}
    (hx : (x : Poly) ≠ 0)
    (hy : y ∉ ℝ ∙ x) :
    Module.finrank ℝ (Submodule.span ℝ ({x, y} : Set linSubmodule)) = 2 :=
  finrank_span_pair_eq_two_of_notMem_span_singleton
    (K := ℝ) (V := linSubmodule)
    (by
      intro h
      exact hx (congrArg (fun z : linSubmodule => (z : Poly)) h))
    hy

theorem span_rank_two_support_pair_eq
    {W : Submodule ℝ linSubmodule} {x y : linSubmodule}
    (hx : (x : Poly) ≠ 0)
    (hxW : x ∈ W)
    (hyW : y ∈ W)
    (hy : y ∉ ℝ ∙ x)
    (hW : Module.finrank ℝ W = 2) :
    Submodule.span ℝ ({x, y} : Set linSubmodule) = W :=
  span_pair_eq_of_mem_of_notMem_span_singleton_of_finrank_two
    (K := ℝ) (V := linSubmodule)
    (by
      intro h
      exact hx (congrArg (fun z : linSubmodule => (z : Poly)) h))
    hxW hyW hy hW

theorem span_rank_one_support_vector_eq
    {W : Submodule ℝ linSubmodule} {x : linSubmodule}
    (hx : (x : Poly) ≠ 0)
    (hxW : x ∈ W)
    (hW : Module.finrank ℝ W = 1) :
    ℝ ∙ x = W :=
  span_singleton_eq_of_mem_of_finrank_one
    (K := ℝ) (V := linSubmodule)
    (by
      intro h
      exact hx (congrArg (fun z : linSubmodule => (z : Poly)) h))
    hxW hW

theorem hasRankTwoSupportComponentHypothesis_of_independent_binary_data
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hSym :
      ∀ (A W : Submodule ℝ linSubmodule) (x : linSubmodule),
        A ≤ linearAnnihilator B p u →
          IsCompl A W →
            x ∈ W →
              (x : Poly) ≠ 0 →
                Module.finrank ℝ A = 2 →
                  Module.finrank ℝ W = 2 →
                    Module.finrank ℝ (symSquareSubmodule A) = 3)
    (hform :
      ∀ (A W : Submodule ℝ linSubmodule) (x y : linSubmodule),
        A ≤ linearAnnihilator B p u →
          IsCompl A W →
            x ∈ W →
              y ∈ W →
                y ∉ ℝ ∙ x →
                  (x : Poly) ≠ 0 →
                    Module.finrank ℝ A = 2 →
                      Module.finrank ℝ W = 2 →
                        HasBinaryLowRankNegativeNormalForm
                          (binaryRestrictionCoeffA B p u x)
                          (binaryRestrictionCoeffB B p u x y)
                          (binaryRestrictionCoeffC B p u x y)
                          (binaryRestrictionCoeffD B p u x y)
                          (binaryRestrictionCoeffE B p u y))
    (hdisj :
      ∀ (A W : Submodule ℝ linSubmodule) (z : linSubmodule),
        A ≤ linearAnnihilator B p u →
          IsCompl A W →
            z ∈ W →
              (z : Poly) ≠ 0 →
                Module.finrank ℝ A = 2 →
                  Module.finrank ℝ W = 2 →
                    LinearMap.range (linProductLeftMapOn z A) ⊓
                        symSquareSubmodule A =
                      ⊥) :
    HasRankTwoSupportComponentHypothesis B p u := by
  intro A W x hAann hAW hxW hx hAdim hWdim
  rcases exists_rank_two_complement_second_direction
      (W := W) (x := x) hx hWdim with
    ⟨y, hyW, hynot⟩
  exact ⟨y, hyW, hSym A W x hAann hAW hxW hx hAdim hWdim,
    hform A W x y hAann hAW hxW hyW hynot hx hAdim hWdim,
    fun z hzW hz =>
      hdisj A W z hAann hAW hzW hz hAdim hWdim⟩

theorem hasRankTwoSupportComponentHypothesis_of_independent_binary_cases
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hSym :
      ∀ (A W : Submodule ℝ linSubmodule) (x : linSubmodule),
        A ≤ linearAnnihilator B p u →
          IsCompl A W →
            x ∈ W →
              (x : Poly) ≠ 0 →
                Module.finrank ℝ A = 2 →
                  Module.finrank ℝ W = 2 →
                    Module.finrank ℝ (symSquareSubmodule A) = 3)
    (hcase :
      ∀ (A W : Submodule ℝ linSubmodule) (x y : linSubmodule),
        A ≤ linearAnnihilator B p u →
          IsCompl A W →
            x ∈ W →
              y ∈ W →
                y ∉ ℝ ∙ x →
                  (x : Poly) ≠ 0 →
                    Module.finrank ℝ A = 2 →
                      Module.finrank ℝ W = 2 →
                        HasBinaryRestrictionKernelEquationCase B p u x y)
    (hdisj :
      ∀ (A W : Submodule ℝ linSubmodule) (z : linSubmodule),
        A ≤ linearAnnihilator B p u →
          IsCompl A W →
            z ∈ W →
              (z : Poly) ≠ 0 →
                Module.finrank ℝ A = 2 →
                  Module.finrank ℝ W = 2 →
                    LinearMap.range (linProductLeftMapOn z A) ⊓
                        symSquareSubmodule A =
                      ⊥) :
    HasRankTwoSupportComponentHypothesis B p u :=
  hasRankTwoSupportComponentHypothesis_of_independent_binary_data
    (B := B) (p := p) (u := u)
    hSym
    (fun A W x y hAann hAW hxW hyW hynot hx hAdim hWdim =>
      binaryRestriction_lowRankNegativeNormalForm_of_kernelEquationCase
        (hcase A W x y hAann hAW hxW hyW hynot hx hAdim hWdim))
    hdisj

theorem hasRankTwoSupportComponentHypothesis_of_independent_binary_plane_cases
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hSym :
      ∀ (A W : Submodule ℝ linSubmodule) (x : linSubmodule),
        A ≤ linearAnnihilator B p u →
          IsCompl A W →
            x ∈ W →
              (x : Poly) ≠ 0 →
                Module.finrank ℝ A = 2 →
                  Module.finrank ℝ W = 2 →
                    Module.finrank ℝ (symSquareSubmodule A) = 3)
    (hcase :
      ∀ (A W : Submodule ℝ linSubmodule) (x y : linSubmodule),
        A ≤ linearAnnihilator B p u →
          IsCompl A W →
            x ∈ W →
              y ∈ W →
                y ∉ ℝ ∙ x →
                  (x : Poly) ≠ 0 →
                    Module.finrank ℝ A = 2 →
                      Module.finrank ℝ W = 2 →
                        HasBinaryRestrictionKernelEquationCase B p u x y)
    (hdisj :
      ∀ (A W : Submodule ℝ linSubmodule) (x y z : linSubmodule),
        A ≤ linearAnnihilator B p u →
          IsCompl A W →
            x ∈ W →
              y ∈ W →
                y ∉ ℝ ∙ x →
                  (x : Poly) ≠ 0 →
                    Module.finrank ℝ A = 2 →
                      Module.finrank ℝ W = 2 →
                        z ∈ Submodule.span ℝ ({x, y} : Set linSubmodule) →
                          (z : Poly) ≠ 0 →
                            LinearMap.range (linProductLeftMapOn z A) ⊓
                                symSquareSubmodule A =
                              ⊥) :
    HasRankTwoSupportComponentHypothesis B p u := by
  intro A W x hAann hAW hxW hx hAdim hWdim
  rcases exists_rank_two_complement_second_direction
      (W := W) (x := x) hx hWdim with
    ⟨y, hyW, hynot⟩
  have hspan : Submodule.span ℝ ({x, y} : Set linSubmodule) = W :=
    span_rank_two_support_pair_eq hx hxW hyW hynot hWdim
  exact ⟨y, hyW, hSym A W x hAann hAW hxW hx hAdim hWdim,
    binaryRestriction_lowRankNegativeNormalForm_of_kernelEquationCase
      (hcase A W x y hAann hAW hxW hyW hynot hx hAdim hWdim),
    fun z hzW hz =>
      hdisj A W x y z hAann hAW hxW hyW hynot hx hAdim hWdim
        (by
          rw [hspan]
          exact hzW)
        hz⟩

theorem hasRankTwoSupportComponentHypothesis_of_independent_binary_plane_cases_and_productLI
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hSym :
      ∀ (A W : Submodule ℝ linSubmodule) (x : linSubmodule),
        A ≤ linearAnnihilator B p u →
          IsCompl A W →
            x ∈ W →
              (x : Poly) ≠ 0 →
                Module.finrank ℝ A = 2 →
                  Module.finrank ℝ W = 2 →
                    Module.finrank ℝ (symSquareSubmodule A) = 3)
    (hcase :
      ∀ (A W : Submodule ℝ linSubmodule) (x y : linSubmodule),
        A ≤ linearAnnihilator B p u →
          IsCompl A W →
            x ∈ W →
              y ∈ W →
                y ∉ ℝ ∙ x →
                  (x : Poly) ≠ 0 →
                    Module.finrank ℝ A = 2 →
                      Module.finrank ℝ W = 2 →
                        HasBinaryRestrictionKernelEquationCase B p u x y)
    (hprodLI :
      ∀ (A W : Submodule ℝ linSubmodule) (x y z : linSubmodule),
        A ≤ linearAnnihilator B p u →
          IsCompl A W →
            x ∈ W →
              y ∈ W →
                y ∉ ℝ ∙ x →
                  (x : Poly) ≠ 0 →
                    Module.finrank ℝ A = 2 →
                      Module.finrank ℝ W = 2 →
                        z ∈ Submodule.span ℝ ({x, y} : Set linSubmodule) →
                          (z : Poly) ≠ 0 →
                            ∃ β : Module.Basis (Fin 2) ℝ A,
                              LinearIndependent ℝ
                                (Sum.elim
                                  (fun i : Fin 2 => linProduct z (β i).1)
                                  (fun ij : {ij : Fin 2 × Fin 2 // ij.1 ≤ ij.2} =>
                                    linProduct (β ij.1.1).1 (β ij.1.2).1))) :
    HasRankTwoSupportComponentHypothesis B p u :=
  hasRankTwoSupportComponentHypothesis_of_independent_binary_plane_cases
    (B := B) (p := p) (u := u)
    hSym hcase
    (fun A W x y z hAann hAW hxW hyW hynot hx hAdim hWdim hzspan hz =>
      let hβ := hprodLI A W x y z hAann hAW hxW hyW hynot hx hAdim hWdim hzspan hz
      match hβ with
      | ⟨β, hLI⟩ =>
        range_linProductLeftMapOn_inf_symSquare_eq_bot_of_basis_products_linearIndependent
          (A := A) (z := z) β hLI)

theorem hasRankTwoSupportComponentHypothesis_of_basis_product_independence
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hSymLI :
      ∀ (A W : Submodule ℝ linSubmodule) (x : linSubmodule),
        A ≤ linearAnnihilator B p u →
          IsCompl A W →
            x ∈ W →
              (x : Poly) ≠ 0 →
                Module.finrank ℝ A = 2 →
                  Module.finrank ℝ W = 2 →
                    ∃ β : Module.Basis (Fin 2) ℝ A,
                      LinearIndependent ℝ
                        (fun ij : {ij : Fin 2 × Fin 2 // ij.1 ≤ ij.2} =>
                          linProduct (β ij.1.1).1 (β ij.1.2).1))
    (hcase :
      ∀ (A W : Submodule ℝ linSubmodule) (x y : linSubmodule),
        A ≤ linearAnnihilator B p u →
          IsCompl A W →
            x ∈ W →
              y ∈ W →
                y ∉ ℝ ∙ x →
                  (x : Poly) ≠ 0 →
                    Module.finrank ℝ A = 2 →
                      Module.finrank ℝ W = 2 →
                        HasBinaryRestrictionKernelEquationCase B p u x y)
    (hprodLI :
      ∀ (A W : Submodule ℝ linSubmodule) (x y z : linSubmodule),
        A ≤ linearAnnihilator B p u →
          IsCompl A W →
            x ∈ W →
              y ∈ W →
                y ∉ ℝ ∙ x →
                  (x : Poly) ≠ 0 →
                    Module.finrank ℝ A = 2 →
                      Module.finrank ℝ W = 2 →
                        z ∈ Submodule.span ℝ ({x, y} : Set linSubmodule) →
                          (z : Poly) ≠ 0 →
                            ∃ β : Module.Basis (Fin 2) ℝ A,
                              LinearIndependent ℝ
                                (Sum.elim
                                  (fun i : Fin 2 => linProduct z (β i).1)
                                  (fun ij : {ij : Fin 2 × Fin 2 // ij.1 ≤ ij.2} =>
                                    linProduct (β ij.1.1).1 (β ij.1.2).1))) :
    HasRankTwoSupportComponentHypothesis B p u :=
  hasRankTwoSupportComponentHypothesis_of_independent_binary_plane_cases_and_productLI
    (B := B) (p := p) (u := u)
    (fun A W x hAann hAW hxW hx hAdim hWdim =>
      match hSymLI A W x hAann hAW hxW hx hAdim hWdim with
      | ⟨β, hLI⟩ =>
        finrank_symSquareSubmodule_eq_three_of_basis_products_linearIndependent β hLI)
    hcase hprodLI

theorem hasRankOneSupportComponentHypothesis_of_self_negative
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hSym :
      ∀ (A W : Submodule ℝ linSubmodule) (x : linSubmodule),
        A ≤ linearAnnihilator B p u →
          IsCompl A W →
            x ∈ W →
              (x : Poly) ≠ 0 →
                Module.finrank ℝ A = 3 →
                  Module.finrank ℝ W = 1 →
                    Module.finrank ℝ (symSquareSubmodule A) = 6)
    (hneg :
      ∀ (A W : Submodule ℝ linSubmodule) (x : linSubmodule),
        A ≤ linearAnnihilator B p u →
          IsCompl A W →
            x ∈ W →
              (x : Poly) ≠ 0 →
                Module.finrank ℝ A = 3 →
                  Module.finrank ℝ W = 1 →
                    binaryRestrictionCoeffA B p u x < 0) :
    HasRankOneSupportComponentHypothesis B p u := by
  intro A W x hAann hAW hxW hx hAdim hWdim
  refine ⟨x, hSym A W x hAann hAW hxW hx hAdim hWdim, ?_⟩
  exact rankOneSelf_binaryLowRankNegativeNormalForm
    (hneg A W x hAann hAW hxW hx hAdim hWdim)

theorem hasRankOneSupportComponentHypothesis_of_basis_product_independence
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hSymLI :
      ∀ (A W : Submodule ℝ linSubmodule) (x : linSubmodule),
        A ≤ linearAnnihilator B p u →
          IsCompl A W →
            x ∈ W →
              (x : Poly) ≠ 0 →
                Module.finrank ℝ A = 3 →
                  Module.finrank ℝ W = 1 →
                    ∃ β : Module.Basis (Fin 3) ℝ A,
                      LinearIndependent ℝ
                        (fun ij : {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} =>
                          linProduct (β ij.1.1).1 (β ij.1.2).1))
    (hneg :
      ∀ (A W : Submodule ℝ linSubmodule) (x : linSubmodule),
        A ≤ linearAnnihilator B p u →
          IsCompl A W →
            x ∈ W →
              (x : Poly) ≠ 0 →
                Module.finrank ℝ A = 3 →
                  Module.finrank ℝ W = 1 →
                    binaryRestrictionCoeffA B p u x < 0) :
    HasRankOneSupportComponentHypothesis B p u :=
  hasRankOneSupportComponentHypothesis_of_self_negative
    (B := B) (p := p) (u := u)
    (fun A W x hAann hAW hxW hx hAdim hWdim =>
      match hSymLI A W x hAann hAW hxW hx hAdim hWdim with
      | ⟨β, hLI⟩ =>
        finrank_symSquareSubmodule_eq_six_of_basis_products_linearIndependent β hLI)
    hneg

theorem exists_rank_one_binaryRestrictionComponentData_of_support
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupp : HasLinearAnnihilatorCodimAtMost B p u 1)
    (hcomponent : HasRankOneSupportComponentHypothesis B p u) :
    HasRankOneBinaryRestrictionComponentData B p u := by
  rcases exists_rank_one_exact_annihilator_complement_vector
      (B := B) (p := p) (u := u) hsupp with
    ⟨A, W, x, hAann, hAW, hxW, hx, _hxnotA, hAdim, hWdim⟩
  rcases hcomponent A W x hAann hAW hxW hx hAdim hWdim with
    ⟨y, hSymdim, hform⟩
  exact ⟨A, W, x, y, hAann, hAW, hxW, hx, hAdim, hWdim, hSymdim, hform⟩

theorem exists_rank_two_binaryRestrictionComponentData_of_support
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupp : HasLinearAnnihilatorCodimAtMost B p u 2)
    (hcomponent : HasRankTwoSupportComponentHypothesis B p u) :
    HasRankTwoBinaryRestrictionComponentData B p u := by
  rcases exists_rank_two_exact_annihilator_complement_vector
      (B := B) (p := p) (u := u) hsupp with
    ⟨A, W, x, hAann, hAW, hxW, hx, _hxnotA, hAdim, hWdim⟩
  rcases hcomponent A W x hAann hAW hxW hx hAdim hWdim with
    ⟨y, hyW, hSymdim, hform, hdisj⟩
  exact ⟨A, W, x, y, hAann, hAW, hxW, hyW, hx, hAdim, hWdim, hSymdim, hform,
    hdisj⟩

theorem exists_rank_three_exact_annihilator
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupp : HasLinearAnnihilatorCodimAtMost B p u 3) :
    ∃ A : Submodule ℝ linSubmodule,
      A ≤ linearAnnihilator B p u ∧ Module.finrank ℝ A = 1 := by
  rcases hsupp with ⟨A₀, hAann, hAdim⟩
  have hAdim_one : 1 ≤ Module.finrank ℝ A₀ := by
    simpa using hAdim
  rcases exists_submodule_le_finrank_eq_of_le
      (K := ℝ) (V := linSubmodule) A₀ hAdim_one with
    ⟨A, hAA₀, hAfin⟩
  exact ⟨A, hAA₀.trans hAann, hAfin⟩

theorem exists_rank_one_exact_annihilator_symSquare
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupp : HasLinearAnnihilatorCodimAtMost B p u 1) :
    ∃ A : Submodule ℝ linSubmodule,
      A ≤ linearAnnihilator B p u ∧
        Module.finrank ℝ A = 3 ∧
          symSquareSubmodule A ≤ LinearMap.ker (catalecticantMap B p u) ∧
            Module.finrank ℝ (symSquareSubmodule A) ≤ 6 := by
  rcases exists_rank_one_exact_annihilator
      (B := B) (p := p) (u := u) hsupp with
    ⟨A, hAann, hAfin⟩
  exact ⟨A, hAann, hAfin,
    symSquareSubmodule_le_ker_of_le_linearAnnihilator
      (B := B) (p := p) (u := u) hAann,
    finrank_symSquareSubmodule_le_six_of_finrank_eq_three hAfin⟩

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

theorem hasPreimageProductSupportData_of_rank_two_supportAmbient_of_annihilator
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hfocp : IsFOCP B p u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2)
    {x : linSubmodule} {A : Submodule ℝ linSubmodule}
    (hx : (x : Poly) ≠ 0)
    (hAann : A ≤ linearAnnihilator B p u)
    (hUdim_ge : 5 ≤ Module.finrank ℝ (supportAmbient x A))
    (hrangeDim : Module.finrank ℝ (LinearMap.range (linProductLeftMapOn x A)) ≤ 2)
    (hsymDim : Module.finrank ℝ (symSquareSubmodule A) ≤ 3)
    (hAdim : 2 ≤ Module.finrank ℝ A)
    (hneg : B ((linProduct x x : quadSubmodule).1^2) (residual p u) < 0) :
    HasPreimageProductSupportData B p u hu :=
  hasPreimageProductSupportData_of_rank_two_supportAmbient
    (B := B) (p := p) (u := u) (hu := hu)
    hfocp hrelker hrank
    (x := x) (A := A)
    hx hAann
    (supportAmbient_le_ker_of_le_linearAnnihilator
      (B := B) (p := p) (u := u) (x := x) hAann)
    hUdim_ge hrangeDim hsymDim hAdim hneg

theorem hasPreimageProductSupportData_of_rank_two_supportAmbient_of_annihilator_dim
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hfocp : IsFOCP B p u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2)
    {x : linSubmodule} {A : Submodule ℝ linSubmodule}
    (hx : (x : Poly) ≠ 0)
    (hAann : A ≤ linearAnnihilator B p u)
    (hUdim_ge : 5 ≤ Module.finrank ℝ (supportAmbient x A))
    (hAdim_le : Module.finrank ℝ A ≤ 2)
    (hsymDim : Module.finrank ℝ (symSquareSubmodule A) ≤ 3)
    (hAdim_ge : 2 ≤ Module.finrank ℝ A)
    (hneg : B ((linProduct x x : quadSubmodule).1^2) (residual p u) < 0) :
    HasPreimageProductSupportData B p u hu :=
  hasPreimageProductSupportData_of_rank_two_supportAmbient_of_annihilator
    (B := B) (p := p) (u := u) (hu := hu)
    hfocp hrelker hrank
    (x := x) (A := A)
    hx hAann hUdim_ge
    (finrank_range_linProductLeftMapOn_le_two (a := x) (A := A) hAdim_le)
    hsymDim hAdim_ge hneg

theorem hasPreimageProductSupportData_of_rank_two_supportAmbient_of_annihilator_finrank_eq
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hfocp : IsFOCP B p u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2)
    {x : linSubmodule} {A : Submodule ℝ linSubmodule}
    (hx : (x : Poly) ≠ 0)
    (hAann : A ≤ linearAnnihilator B p u)
    (hUdim_ge : 5 ≤ Module.finrank ℝ (supportAmbient x A))
    (hAdim : Module.finrank ℝ A = 2)
    (hneg : B ((linProduct x x : quadSubmodule).1^2) (residual p u) < 0) :
    HasPreimageProductSupportData B p u hu := by
  exact hasPreimageProductSupportData_of_rank_two_supportAmbient_of_annihilator_dim
    (B := B) (p := p) (u := u) (hu := hu)
    hfocp hrelker hrank
    (x := x) (A := A)
    hx hAann hUdim_ge
    (by omega)
    (finrank_symSquareSubmodule_le_three_of_finrank_eq_two hAdim)
    (by omega)
    hneg

theorem hasPreimageProductSupportData_of_rank_two_supportAmbient_of_components
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hfocp : IsFOCP B p u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2)
    {x : linSubmodule} {A : Submodule ℝ linSubmodule}
    (hx : (x : Poly) ≠ 0)
    (hAann : A ≤ linearAnnihilator B p u)
    (hAdim : Module.finrank ℝ A = 2)
    (hsym : Module.finrank ℝ (symSquareSubmodule A) = 3)
    (hdisj :
      LinearMap.range (linProductLeftMapOn x A) ⊓ symSquareSubmodule A = ⊥)
    (hneg : B ((linProduct x x : quadSubmodule).1^2) (residual p u) < 0) :
    HasPreimageProductSupportData B p u hu :=
  hasPreimageProductSupportData_of_rank_two_supportAmbient_of_annihilator_finrank_eq
    (B := B) (p := p) (u := u) (hu := hu)
    hfocp hrelker hrank
    (x := x) (A := A)
    hx hAann
    (five_le_finrank_supportAmbient_of_rank_two_components hx hAdim hsym hdisj)
    hAdim hneg

theorem hasPreimageProductSupportData_of_rank_two_binaryNormalForm
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hfocp : IsFOCP B p u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2)
    {A : Submodule ℝ linSubmodule} {x y : linSubmodule}
    {a b c d e : ℝ}
    (hAann : A ≤ linearAnnihilator B p u)
    (hAdim : Module.finrank ℝ A = 2)
    (hsym : Module.finrank ℝ (symSquareSubmodule A) = 3)
    (hform : HasBinaryLowRankNegativeNormalForm a b c d e)
    (heval : ∀ X Y : ℝ,
      B ((linProduct (X • x + Y • y) (X • x + Y • y) : quadSubmodule).1^2)
          (residual p u) =
        binaryQuarticEval a b c d e X Y)
    (hdisj :
      ∀ z : linSubmodule,
        z ∈ Submodule.span ℝ ({x, y} : Set linSubmodule) →
          (z : Poly) ≠ 0 →
            LinearMap.range (linProductLeftMapOn z A) ⊓ symSquareSubmodule A = ⊥) :
    HasPreimageProductSupportData B p u hu := by
  rcases exists_negative_pure_square_of_binaryLowRankNormalForm
      (B := B) (p := p) (u := u)
      (x := x) (y := y) hform heval with
    ⟨z, hzspan, hneg⟩
  have hz : (z : Poly) ≠ 0 := by
    intro hzero
    have hval_zero :
        B ((linProduct z z : quadSubmodule).1^2) (residual p u) = 0 := by
      simp [linProduct, hzero]
    linarith
  exact hasPreimageProductSupportData_of_rank_two_supportAmbient_of_components
    (B := B) (p := p) (u := u) (hu := hu)
    hfocp hrelker hrank
    (x := z) (A := A)
    hz hAann hAdim hsym (hdisj z hzspan hz) hneg

theorem hasPreimageProductSupportData_of_rank_two_binaryRestriction
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hfocp : IsFOCP B p u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2)
    {A : Submodule ℝ linSubmodule} {x y : linSubmodule}
    (hAann : A ≤ linearAnnihilator B p u)
    (hAdim : Module.finrank ℝ A = 2)
    (hsym : Module.finrank ℝ (symSquareSubmodule A) = 3)
    (hform :
      HasBinaryLowRankNegativeNormalForm
        (binaryRestrictionCoeffA B p u x)
        (binaryRestrictionCoeffB B p u x y)
        (binaryRestrictionCoeffC B p u x y)
        (binaryRestrictionCoeffD B p u x y)
        (binaryRestrictionCoeffE B p u y))
    (hpow : ∀ X Y : ℝ,
      (linProduct (X • x + Y • y) (X • x + Y • y) :
          quadSubmodule).1^2 =
        X^4 • (linProduct x x : quadSubmodule).1^2 +
          (4 * X^3 * Y) •
            ((linProduct x x : quadSubmodule).1 *
              (linProduct x y : quadSubmodule).1) +
            (6 * X^2 * Y^2) • (linProduct x y : quadSubmodule).1^2 +
              (4 * X * Y^3) •
                ((linProduct x y : quadSubmodule).1 *
                  (linProduct y y : quadSubmodule).1) +
                Y^4 • (linProduct y y : quadSubmodule).1^2)
    (hdisj :
      ∀ z : linSubmodule,
        z ∈ Submodule.span ℝ ({x, y} : Set linSubmodule) →
          (z : Poly) ≠ 0 →
            LinearMap.range (linProductLeftMapOn z A) ⊓ symSquareSubmodule A = ⊥) :
    HasPreimageProductSupportData B p u hu :=
  hasPreimageProductSupportData_of_rank_two_binaryNormalForm
    (B := B) (p := p) (u := u) (hu := hu)
    hfocp hrelker hrank
    (A := A) (x := x) (y := y)
    hAann hAdim hsym hform
    (binaryRestriction_eval_eq_of_pow_expansion B p u x y hpow)
    hdisj

theorem hasPreimageProductSupportData_of_rank_two_binaryRestriction_coefficients
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hfocp : IsFOCP B p u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2)
    {A : Submodule ℝ linSubmodule} {x y : linSubmodule}
    (hAann : A ≤ linearAnnihilator B p u)
    (hAdim : Module.finrank ℝ A = 2)
    (hsym : Module.finrank ℝ (symSquareSubmodule A) = 3)
    (hform :
      HasBinaryLowRankNegativeNormalForm
        (binaryRestrictionCoeffA B p u x)
        (binaryRestrictionCoeffB B p u x y)
        (binaryRestrictionCoeffC B p u x y)
        (binaryRestrictionCoeffD B p u x y)
        (binaryRestrictionCoeffE B p u y))
    (hdisj :
      ∀ z : linSubmodule,
        z ∈ Submodule.span ℝ ({x, y} : Set linSubmodule) →
          (z : Poly) ≠ 0 →
            LinearMap.range (linProductLeftMapOn z A) ⊓ symSquareSubmodule A = ⊥) :
    HasPreimageProductSupportData B p u hu :=
  hasPreimageProductSupportData_of_rank_two_binaryNormalForm
    (B := B) (p := p) (u := u) (hu := hu)
    hfocp hrelker hrank
    (A := A) (x := x) (y := y)
    hAann hAdim hsym hform
    (binaryRestriction_eval_eq B p u x y)
    hdisj

theorem hasPreimageProductSupportData_of_rank_two_support
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hfocp : IsFOCP B p u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2)
    (hsupp : HasLinearAnnihilatorCodimAtMost B p u 2)
    {x : linSubmodule}
    (hx : (x : Poly) ≠ 0)
    (hUdim_ge :
      ∀ A : Submodule ℝ linSubmodule,
        A ≤ linearAnnihilator B p u →
          Module.finrank ℝ A = 2 →
            5 ≤ Module.finrank ℝ (supportAmbient x A))
    (hneg : B ((linProduct x x : quadSubmodule).1^2) (residual p u) < 0) :
    HasPreimageProductSupportData B p u hu := by
  rcases exists_rank_two_exact_annihilator
      (B := B) (p := p) (u := u) hsupp with
    ⟨A, hAann, hAfin⟩
  exact hasPreimageProductSupportData_of_rank_two_supportAmbient_of_annihilator_finrank_eq
    (B := B) (p := p) (u := u) (hu := hu)
    hfocp hrelker hrank
    (x := x) (A := A)
    hx hAann (hUdim_ge A hAann hAfin) hAfin hneg

theorem exists_negative_syzygyCertificate_of_rank_two_support
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hfocp : IsFOCP B p u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2)
    (hsupp : HasLinearAnnihilatorCodimAtMost B p u 2)
    {x : linSubmodule}
    (hx : (x : Poly) ≠ 0)
    (hUdim_ge :
      ∀ A : Submodule ℝ linSubmodule,
        A ≤ linearAnnihilator B p u →
          Module.finrank ℝ A = 2 →
            5 ≤ Module.finrank ℝ (supportAmbient x A))
    (hneg : B ((linProduct x x : quadSubmodule).1^2) (residual p u) < 0) :
    ∃ q : Poly, IsQuadratic q ∧
      B (q^2) (residual p u) < 0 ∧ HasSyzygyCertificate B p u q :=
  exists_negative_syzygyCertificate_of_preimageProductSupportData
    (B := B) (p := p) (u := u) (hu := hu)
    (hasPreimageProductSupportData_of_rank_two_support
      (B := B) (p := p) (u := u) (hu := hu)
      hfocp hrelker hrank hsupp hx hUdim_ge hneg)

def HasRankOneProductSupportData
    (B : DotForm) (p : Poly) (u : RankSevenVec)
    (hu : IsAdmissiblePoint u) : Prop :=
  ∃ (x : linSubmodule) (A M : Submodule ℝ linSubmodule)
      (N : Submodule ℝ quadSubmodule),
    A ≤ linearAnnihilator B p u ∧
      (∀ m : M, linProduct x m.1 ∈ spanUQuad hu) ∧
        N ≤ spanUQuad hu ∧
          N ≤ symSquareSubmodule A ∧
            linProductSubmodule M A ≤ symSquareSubmodule A ∧
              M ≠ ⊥ ∧
                4 ≤ Module.finrank ℝ N ∧
                  3 ≤ Module.finrank ℝ A ∧
                    Module.finrank ℝ (symSquareSubmodule A) = 6 ∧
                      B ((linProduct x x : quadSubmodule).1^2) (residual p u) < 0

theorem exists_negative_syzygyCertificate_of_rank_one_productSupportData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hdata : HasRankOneProductSupportData B p u hu) :
    ∃ q : Poly, IsQuadratic q ∧
      B (q^2) (residual p u) < 0 ∧ HasSyzygyCertificate B p u q := by
  rcases hdata with
    ⟨x, A, M, N, hAann, hxM_L, hN_L, hN_sym, hMA_sym, hMne,
      hNdim, hAdim, hSymdim, hneg⟩
  rcases exists_mem_inf_linProductSubmodule_ne_zero_of_finrank_lt_add
      (N := N) (W := symSquareSubmodule A) (M := M) (A := A)
      hN_sym hMA_sym hMne hNdim hAdim hSymdim (by norm_num) with
    ⟨s, hsN, hsMA, hsne⟩
  refine ⟨(linProduct x x : quadSubmodule).1, (linProduct x x : quadSubmodule).2,
    hneg, ?_⟩
  exact hasSyzygyCertificate_of_mem_linProductSubmodule
    (B := B) (p := p) (u := u) (hu := hu)
    (x := x) (M := M) (A := A) (s := s)
    hxM_L
    (fun a => linProduct_comm_mem_catalecticantKernel_of_le_linearAnnihilator hAann x a)
    (hN_L hsN)
    (fun hszero => hsne (Subtype.ext hszero))
    hsMA

theorem hasRankOneProductSupportData_of_annihilator_symSquare
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hfocp : IsFOCP B p u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1)
    {x : linSubmodule} {A : Submodule ℝ linSubmodule}
    (hx : (x : Poly) ≠ 0)
    (hAann : A ≤ linearAnnihilator B p u)
    (hAdim : Module.finrank ℝ A = 3)
    (hSymdim : Module.finrank ℝ (symSquareSubmodule A) = 6)
    (hneg : B ((linProduct x x : quadSubmodule).1^2) (residual p u) < 0) :
    HasRankOneProductSupportData B p u hu := by
  let M := linProductLeftPreimageWithin x A (spanUQuad hu)
  let N := spanUQuad hu ⊓ symSquareSubmodule A
  have hMne : M ≠ ⊥ := by
    refine linProductLeftPreimageWithin_ne_bot_of_finrank_le_lt_add
      (a := x) (A := A) (P := spanUQuad hu)
      (W := LinearMap.ker (catalecticantMap B p u))
      (pdim := 7) (adim := 3) (wdim := 9) hx ?_ ?_ ?_ ?_ ?_ ?_
    · exact spanUQuad_le_ker_catalecticantMap hu hfocp
    · exact range_linProductLeftMapOn_le_ker_of_le_linearAnnihilator
        (B := B) (p := p) (u := u) (x := x) hAann
    · rw [finrank_spanUQuad_eq_seven_of_relationPolyLin_ker_eq_bot hu hrelker]
    · omega
    · rw [finrank_ker_catalecticantMap_eq_nine_of_rank_one hrank]
    · norm_num
  have hNdim : 4 ≤ Module.finrank ℝ N := by
    exact four_le_finrank_spanUQuad_inf_of_rank_one_ambient
      (B := B) (p := p) (u := u) hu hfocp hrelker hrank
      (U := symSquareSubmodule A)
      (symSquareSubmodule_le_ker_of_le_linearAnnihilator
        (B := B) (p := p) (u := u) hAann)
      (by omega)
  refine ⟨x, A, M, N, hAann, ?_, inf_le_left, inf_le_right, ?_,
    hMne, hNdim, ?_, hSymdim, hneg⟩
  · intro m
    exact linProduct_mem_of_mem_linProductLeftPreimageWithin m.2
  · exact linProductSubmodule_leftPreimageWithin_le_symSquare x A (spanUQuad hu)
  · omega

theorem hasRankOneProductSupportData_of_binaryNormalForm
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hfocp : IsFOCP B p u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1)
    {A : Submodule ℝ linSubmodule} {x y : linSubmodule}
    {a b c d e : ℝ}
    (hAann : A ≤ linearAnnihilator B p u)
    (hAdim : Module.finrank ℝ A = 3)
    (hSymdim : Module.finrank ℝ (symSquareSubmodule A) = 6)
    (hform : HasBinaryLowRankNegativeNormalForm a b c d e)
    (heval : ∀ X Y : ℝ,
      B ((linProduct (X • x + Y • y) (X • x + Y • y) : quadSubmodule).1^2)
          (residual p u) =
        binaryQuarticEval a b c d e X Y) :
    HasRankOneProductSupportData B p u hu := by
  rcases exists_negative_pure_square_of_binaryLowRankNormalForm
      (B := B) (p := p) (u := u)
      (x := x) (y := y) hform heval with
    ⟨z, _hzspan, hneg⟩
  have hz : (z : Poly) ≠ 0 := by
    intro hzero
    have hval_zero :
        B ((linProduct z z : quadSubmodule).1^2) (residual p u) = 0 := by
      simp [linProduct, hzero]
    linarith
  exact hasRankOneProductSupportData_of_annihilator_symSquare
    (B := B) (p := p) (u := u) (hu := hu)
    hfocp hrelker hrank
    (x := z) (A := A)
    hz hAann hAdim hSymdim hneg

theorem hasRankOneProductSupportData_of_binaryRestriction
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hfocp : IsFOCP B p u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1)
    {A : Submodule ℝ linSubmodule} {x y : linSubmodule}
    (hAann : A ≤ linearAnnihilator B p u)
    (hAdim : Module.finrank ℝ A = 3)
    (hSymdim : Module.finrank ℝ (symSquareSubmodule A) = 6)
    (hform :
      HasBinaryLowRankNegativeNormalForm
        (binaryRestrictionCoeffA B p u x)
        (binaryRestrictionCoeffB B p u x y)
        (binaryRestrictionCoeffC B p u x y)
        (binaryRestrictionCoeffD B p u x y)
        (binaryRestrictionCoeffE B p u y))
    (hpow : ∀ X Y : ℝ,
      (linProduct (X • x + Y • y) (X • x + Y • y) :
          quadSubmodule).1^2 =
        X^4 • (linProduct x x : quadSubmodule).1^2 +
          (4 * X^3 * Y) •
            ((linProduct x x : quadSubmodule).1 *
              (linProduct x y : quadSubmodule).1) +
            (6 * X^2 * Y^2) • (linProduct x y : quadSubmodule).1^2 +
              (4 * X * Y^3) •
                ((linProduct x y : quadSubmodule).1 *
                  (linProduct y y : quadSubmodule).1) +
                Y^4 • (linProduct y y : quadSubmodule).1^2) :
    HasRankOneProductSupportData B p u hu :=
  hasRankOneProductSupportData_of_binaryNormalForm
    (B := B) (p := p) (u := u) (hu := hu)
    hfocp hrelker hrank
    (A := A) (x := x) (y := y)
    hAann hAdim hSymdim hform
    (binaryRestriction_eval_eq_of_pow_expansion B p u x y hpow)

theorem hasRankOneProductSupportData_of_binaryRestriction_coefficients
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hfocp : IsFOCP B p u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1)
    {A : Submodule ℝ linSubmodule} {x y : linSubmodule}
    (hAann : A ≤ linearAnnihilator B p u)
    (hAdim : Module.finrank ℝ A = 3)
    (hSymdim : Module.finrank ℝ (symSquareSubmodule A) = 6)
    (hform :
      HasBinaryLowRankNegativeNormalForm
        (binaryRestrictionCoeffA B p u x)
        (binaryRestrictionCoeffB B p u x y)
        (binaryRestrictionCoeffC B p u x y)
        (binaryRestrictionCoeffD B p u x y)
        (binaryRestrictionCoeffE B p u y)) :
    HasRankOneProductSupportData B p u hu :=
  hasRankOneProductSupportData_of_binaryNormalForm
    (B := B) (p := p) (u := u) (hu := hu)
    hfocp hrelker hrank
    (A := A) (x := x) (y := y)
    hAann hAdim hSymdim hform
    (binaryRestriction_eval_eq B p u x y)

theorem hasRankOneProductSupportData_of_binaryRestrictionComponentData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hfocp : IsFOCP B p u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1)
    (hdata : HasRankOneBinaryRestrictionComponentData B p u) :
    HasRankOneProductSupportData B p u hu := by
  rcases hdata with
    ⟨A, _W, x, y, hAann, _hAW, _hxW, _hx, hAdim, _hWdim, hSymdim, hform⟩
  exact hasRankOneProductSupportData_of_binaryRestriction_coefficients
    (B := B) (p := p) (u := u) (hu := hu)
    hfocp hrelker hrank
    (A := A) (x := x) (y := y)
    hAann hAdim hSymdim hform

theorem hasPreimageProductSupportData_of_rank_two_binaryRestrictionComponentData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hfocp : IsFOCP B p u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2)
    (hdata : HasRankTwoBinaryRestrictionComponentData B p u) :
    HasPreimageProductSupportData B p u hu := by
  rcases hdata with
    ⟨A, W, x, y, hAann, _hAW, hxW, hyW, _hx, hAdim, _hWdim, hSymdim,
      hform, hdisjW⟩
  exact hasPreimageProductSupportData_of_rank_two_binaryRestriction_coefficients
    (B := B) (p := p) (u := u) (hu := hu)
    hfocp hrelker hrank
    (A := A) (x := x) (y := y)
    hAann hAdim hSymdim hform
    (by
      intro z hzspan hz
      have hspan_le : Submodule.span ℝ ({x, y} : Set linSubmodule) ≤ W := by
        refine Submodule.span_le.mpr ?_
        intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl
        · exact hxW
        · exact hyW
      exact hdisjW z (hspan_le hzspan) hz)

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

theorem exists_negative_syzygyCertificate_of_rank_one_ambient_bounds
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
    ∃ q : Poly, IsQuadratic q ∧
      B (q^2) (residual p u) < 0 ∧ HasSyzygyCertificate B p u q :=
  exists_negative_syzygyCertificate_of_preimageProductSupportData
    (B := B) (p := p) (u := u) (hu := hu)
    (hasPreimageProductSupportData_of_rank_one_ambient_bounds
      (B := B) (p := p) (u := u) (hu := hu)
      hfocp hrelker hrank hx hAann hUker hUdim_ge hUdim_le
      hrangeU hMAU hAdim hneg)

end QuaternaryQuartic
