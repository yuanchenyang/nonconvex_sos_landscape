import QuaternaryQuarticProof.Dimension
import QuaternaryQuarticProof.Binary
import QuaternaryQuarticProof.Support
import QuaternaryQuarticProof.Syzygy

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace QuaternaryQuartic

def HasRankCaseNegativeCertificateFamily
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  residual p u ≠ 0 →
    LinearMap.ker (relationPolyLin u) = ⊥ →
      (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
        ∃ q : Poly, IsQuadratic q ∧
          B (q^2) (residual p u) < 0 ∧ HasSyzygyCertificate B p u q) ∧
      (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
        ∃ q : Poly, IsQuadratic q ∧
          B (q^2) (residual p u) < 0 ∧ HasSyzygyCertificate B p u q) ∧
      (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
        ∃ q : Poly, IsQuadratic q ∧
          B (q^2) (residual p u) < 0 ∧ HasSyzygyCertificate B p u q)

def HasRankCaseSupportData
    (B : DotForm) (p : Poly) (u : RankSevenVec)
    (hu : IsAdmissiblePoint u) : Prop :=
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
    HasPreimageProductSupportData B p u hu) ∧
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
    HasPreimageProductSupportData B p u hu) ∧
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
    HasRankThreeAnnihilatorSupportData B p u)

def HasRefinedRankCaseSupportData
    (B : DotForm) (p : Poly) (u : RankSevenVec)
    (hu : IsAdmissiblePoint u) : Prop :=
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
    HasRankOneProductSupportData B p u hu) ∧
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
    HasPreimageProductSupportData B p u hu) ∧
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
    HasRankThreeAnnihilatorSupportData B p u)

def HasRankCaseBinaryNormalFormData
    (B : DotForm) (p : Poly) (u : RankSevenVec)
    (_hu : IsAdmissiblePoint u) : Prop :=
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
    ∃ (A : Submodule ℝ linSubmodule) (x y : linSubmodule)
        (a b c d e : ℝ),
      A ≤ linearAnnihilator B p u ∧
        Module.finrank ℝ A = 3 ∧
          Module.finrank ℝ (symSquareSubmodule A) = 6 ∧
            HasBinaryLowRankNegativeNormalForm a b c d e ∧
              (∀ X Y : ℝ,
                B ((linProduct (X • x + Y • y) (X • x + Y • y) :
                    quadSubmodule).1^2) (residual p u) =
                  binaryQuarticEval a b c d e X Y)) ∧
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
    ∃ (A : Submodule ℝ linSubmodule) (x y : linSubmodule)
        (a b c d e : ℝ),
      A ≤ linearAnnihilator B p u ∧
        Module.finrank ℝ A = 2 ∧
          Module.finrank ℝ (symSquareSubmodule A) = 3 ∧
            HasBinaryLowRankNegativeNormalForm a b c d e ∧
              (∀ X Y : ℝ,
                B ((linProduct (X • x + Y • y) (X • x + Y • y) :
                    quadSubmodule).1^2) (residual p u) =
                  binaryQuarticEval a b c d e X Y) ∧
                ∀ z : linSubmodule,
                  z ∈ Submodule.span ℝ ({x, y} : Set linSubmodule) →
                    (z : Poly) ≠ 0 →
                      LinearMap.range (linProductLeftMapOn z A) ⊓
                          symSquareSubmodule A =
                        ⊥) ∧
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
    HasRankThreeAnnihilatorSupportData B p u)

def HasRankCaseBinaryRestrictionData
    (B : DotForm) (p : Poly) (u : RankSevenVec)
    (_hu : IsAdmissiblePoint u) : Prop :=
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
    ∃ (A : Submodule ℝ linSubmodule) (x y : linSubmodule),
      A ≤ linearAnnihilator B p u ∧
        Module.finrank ℝ A = 3 ∧
          Module.finrank ℝ (symSquareSubmodule A) = 6 ∧
            HasBinaryLowRankNegativeNormalForm
              (binaryRestrictionCoeffA B p u x)
              (binaryRestrictionCoeffB B p u x y)
              (binaryRestrictionCoeffC B p u x y)
              (binaryRestrictionCoeffD B p u x y)
              (binaryRestrictionCoeffE B p u y)) ∧
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
    ∃ (A : Submodule ℝ linSubmodule) (x y : linSubmodule),
      A ≤ linearAnnihilator B p u ∧
        Module.finrank ℝ A = 2 ∧
          Module.finrank ℝ (symSquareSubmodule A) = 3 ∧
            HasBinaryLowRankNegativeNormalForm
              (binaryRestrictionCoeffA B p u x)
              (binaryRestrictionCoeffB B p u x y)
              (binaryRestrictionCoeffC B p u x y)
              (binaryRestrictionCoeffD B p u x y)
              (binaryRestrictionCoeffE B p u y) ∧
                ∀ z : linSubmodule,
                  z ∈ Submodule.span ℝ ({x, y} : Set linSubmodule) →
                    (z : Poly) ≠ 0 →
                      LinearMap.range (linProductLeftMapOn z A) ⊓
                          symSquareSubmodule A =
                        ⊥) ∧
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
    HasRankThreeAnnihilatorSupportData B p u)

def HasRankCaseBinaryRestrictionComponentData
    (B : DotForm) (p : Poly) (u : RankSevenVec)
    (_hu : IsAdmissiblePoint u) : Prop :=
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
    HasRankOneBinaryRestrictionComponentData B p u) ∧
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
    HasRankTwoBinaryRestrictionComponentData B p u) ∧
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
    HasRankThreeAnnihilatorSupportData B p u)

def HasRankCaseApolarComponentData
    (B : DotForm) (p : Poly) (u : RankSevenVec)
    (_hu : IsAdmissiblePoint u) : Prop :=
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
    HasLinearAnnihilatorCodimAtMost B p u 1 ∧
      HasRankOneSupportComponentHypothesis B p u) ∧
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
    HasLinearAnnihilatorCodimAtMost B p u 2 ∧
      HasRankTwoSupportComponentHypothesis B p u) ∧
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
    HasRankThreeAnnihilatorSupportData B p u)

theorem hasRankCaseNegativeCertificateFamily_of_supportData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hfocp : IsFOCP B p u)
    (hdata : HasRankCaseSupportData B p u hu) :
    HasRankCaseNegativeCertificateFamily B p u := by
  intro _hres hker
  rcases hdata with ⟨hdata1, hdata2, hdata3⟩
  constructor
  · intro hrank1
    exact exists_negative_syzygyCertificate_of_preimageProductSupportData
      (B := B) (p := p) (u := u) (hu := hu) (hdata1 hrank1)
  constructor
  · intro hrank2
    exact exists_negative_syzygyCertificate_of_preimageProductSupportData
      (B := B) (p := p) (u := u) (hu := hu) (hdata2 hrank2)
  · intro hrank3
    exact exists_negative_syzygyCertificate_of_rank_three_supportData
      (B := B) (p := p) (u := u) hu hfocp hker hrank3 (hdata3 hrank3)

theorem hasRankCaseNegativeCertificateFamily_of_refinedSupportData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hfocp : IsFOCP B p u)
    (hdata : HasRefinedRankCaseSupportData B p u hu) :
    HasRankCaseNegativeCertificateFamily B p u := by
  intro _hres hker
  rcases hdata with ⟨hdata1, hdata2, hdata3⟩
  constructor
  · intro hrank1
    exact exists_negative_syzygyCertificate_of_rank_one_productSupportData
      (B := B) (p := p) (u := u) (hu := hu) (hdata1 hrank1)
  constructor
  · intro hrank2
    exact exists_negative_syzygyCertificate_of_preimageProductSupportData
      (B := B) (p := p) (u := u) (hu := hu) (hdata2 hrank2)
  · intro hrank3
    exact exists_negative_syzygyCertificate_of_rank_three_supportData
      (B := B) (p := p) (u := u) hu hfocp hker hrank3 (hdata3 hrank3)

theorem hasRankCaseNegativeCertificateFamily_of_binaryNormalFormData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hfocp : IsFOCP B p u)
    (hdata : HasRankCaseBinaryNormalFormData B p u hu) :
    HasRankCaseNegativeCertificateFamily B p u := by
  intro _hres hker
  rcases hdata with ⟨hdata1, hdata2, hdata3⟩
  constructor
  · intro hrank1
    rcases hdata1 hrank1 with
      ⟨A, x, y, a, b, c, d, e, hAann, hAdim, hSymdim, hform, heval⟩
    exact exists_negative_syzygyCertificate_of_rank_one_productSupportData
      (B := B) (p := p) (u := u) (hu := hu)
      (hasRankOneProductSupportData_of_binaryNormalForm
        (B := B) (p := p) (u := u) (hu := hu)
        hfocp hker hrank1
        (A := A) (x := x) (y := y)
        hAann hAdim hSymdim hform heval)
  constructor
  · intro hrank2
    rcases hdata2 hrank2 with
      ⟨A, x, y, a, b, c, d, e, hAann, hAdim, hSymdim, hform, heval, hdisj⟩
    exact exists_negative_syzygyCertificate_of_preimageProductSupportData
      (B := B) (p := p) (u := u) (hu := hu)
      (hasPreimageProductSupportData_of_rank_two_binaryNormalForm
        (B := B) (p := p) (u := u) (hu := hu)
        hfocp hker hrank2
        (A := A) (x := x) (y := y)
        hAann hAdim hSymdim hform heval hdisj)
  · intro hrank3
    exact exists_negative_syzygyCertificate_of_rank_three_supportData
      (B := B) (p := p) (u := u) hu hfocp hker hrank3 (hdata3 hrank3)

theorem hasRankCaseNegativeCertificateFamily_of_binaryRestrictionData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hfocp : IsFOCP B p u)
    (hdata : HasRankCaseBinaryRestrictionData B p u hu) :
    HasRankCaseNegativeCertificateFamily B p u := by
  intro _hres hker
  rcases hdata with ⟨hdata1, hdata2, hdata3⟩
  constructor
  · intro hrank1
    rcases hdata1 hrank1 with
      ⟨A, x, y, hAann, hAdim, hSymdim, hform⟩
    exact exists_negative_syzygyCertificate_of_rank_one_productSupportData
      (B := B) (p := p) (u := u) (hu := hu)
      (hasRankOneProductSupportData_of_binaryRestriction_coefficients
        (B := B) (p := p) (u := u) (hu := hu)
        hfocp hker hrank1
        (A := A) (x := x) (y := y)
        hAann hAdim hSymdim hform)
  constructor
  · intro hrank2
    rcases hdata2 hrank2 with
      ⟨A, x, y, hAann, hAdim, hSymdim, hform, hdisj⟩
    exact exists_negative_syzygyCertificate_of_preimageProductSupportData
      (B := B) (p := p) (u := u) (hu := hu)
      (hasPreimageProductSupportData_of_rank_two_binaryRestriction_coefficients
        (B := B) (p := p) (u := u) (hu := hu)
        hfocp hker hrank2
        (A := A) (x := x) (y := y)
        hAann hAdim hSymdim hform hdisj)
  · intro hrank3
    exact exists_negative_syzygyCertificate_of_rank_three_supportData
      (B := B) (p := p) (u := u) hu hfocp hker hrank3 (hdata3 hrank3)

theorem hasRankCaseNegativeCertificateFamily_of_binaryRestrictionComponentData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hfocp : IsFOCP B p u)
    (hdata : HasRankCaseBinaryRestrictionComponentData B p u hu) :
    HasRankCaseNegativeCertificateFamily B p u := by
  intro _hres hker
  rcases hdata with ⟨hdata1, hdata2, hdata3⟩
  constructor
  · intro hrank1
    exact exists_negative_syzygyCertificate_of_rank_one_productSupportData
      (B := B) (p := p) (u := u) (hu := hu)
      (hasRankOneProductSupportData_of_binaryRestrictionComponentData
        (B := B) (p := p) (u := u) (hu := hu)
        hfocp hker hrank1 (hdata1 hrank1))
  constructor
  · intro hrank2
    exact exists_negative_syzygyCertificate_of_preimageProductSupportData
      (B := B) (p := p) (u := u) (hu := hu)
      (hasPreimageProductSupportData_of_rank_two_binaryRestrictionComponentData
        (B := B) (p := p) (u := u) (hu := hu)
        hfocp hker hrank2 (hdata2 hrank2))
  · intro hrank3
    exact exists_negative_syzygyCertificate_of_rank_three_supportData
      (B := B) (p := p) (u := u) hu hfocp hker hrank3 (hdata3 hrank3)

theorem hasRankCaseNegativeCertificateFamily_of_apolarComponentData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hfocp : IsFOCP B p u)
    (hdata : HasRankCaseApolarComponentData B p u hu) :
    HasRankCaseNegativeCertificateFamily B p u := by
  intro _hres hker
  rcases hdata with ⟨hdata1, hdata2, hdata3⟩
  constructor
  · intro hrank1
    rcases hdata1 hrank1 with ⟨hsupp, hcomponent⟩
    exact exists_negative_syzygyCertificate_of_rank_one_productSupportData
      (B := B) (p := p) (u := u) (hu := hu)
      (hasRankOneProductSupportData_of_binaryRestrictionComponentData
        (B := B) (p := p) (u := u) (hu := hu)
        hfocp hker hrank1
        (exists_rank_one_binaryRestrictionComponentData_of_support hsupp hcomponent))
  constructor
  · intro hrank2
    rcases hdata2 hrank2 with ⟨hsupp, hcomponent⟩
    exact exists_negative_syzygyCertificate_of_preimageProductSupportData
      (B := B) (p := p) (u := u) (hu := hu)
      (hasPreimageProductSupportData_of_rank_two_binaryRestrictionComponentData
        (B := B) (p := p) (u := u) (hu := hu)
        hfocp hker hrank2
        (exists_rank_two_binaryRestrictionComponentData_of_support hsupp hcomponent))
  · intro hrank3
    exact exists_negative_syzygyCertificate_of_rank_three_supportData
      (B := B) (p := p) (u := u) hu hfocp hker hrank3 (hdata3 hrank3)

theorem residual_eq_zero_of_hasRankCaseNegativeCertificateFamily
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hcert : HasRankCaseNegativeCertificateFamily B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_rank_case_exists_negative_syzygy_certificate
    (B := B) hu hp hsocp hcert

theorem residual_eq_zero_of_rankCaseSupportData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdata : HasRankCaseSupportData B p u hu) :
    residual p u = 0 :=
  residual_eq_zero_of_hasRankCaseNegativeCertificateFamily
    (B := B) hu hp hsocp
    (hasRankCaseNegativeCertificateFamily_of_supportData hu hsocp.1 hdata)

theorem residual_eq_zero_of_refinedRankCaseSupportData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdata : HasRefinedRankCaseSupportData B p u hu) :
    residual p u = 0 :=
  residual_eq_zero_of_hasRankCaseNegativeCertificateFamily
    (B := B) hu hp hsocp
    (hasRankCaseNegativeCertificateFamily_of_refinedSupportData hu hsocp.1 hdata)

theorem residual_eq_zero_of_rankCaseBinaryNormalFormData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdata : HasRankCaseBinaryNormalFormData B p u hu) :
    residual p u = 0 :=
  residual_eq_zero_of_hasRankCaseNegativeCertificateFamily
    (B := B) hu hp hsocp
    (hasRankCaseNegativeCertificateFamily_of_binaryNormalFormData hu hsocp.1 hdata)

theorem residual_eq_zero_of_rankCaseBinaryRestrictionData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdata : HasRankCaseBinaryRestrictionData B p u hu) :
    residual p u = 0 :=
  residual_eq_zero_of_hasRankCaseNegativeCertificateFamily
    (B := B) hu hp hsocp
    (hasRankCaseNegativeCertificateFamily_of_binaryRestrictionData hu hsocp.1 hdata)

theorem residual_eq_zero_of_rankCaseBinaryRestrictionComponentData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdata : HasRankCaseBinaryRestrictionComponentData B p u hu) :
    residual p u = 0 :=
  residual_eq_zero_of_hasRankCaseNegativeCertificateFamily
    (B := B) hu hp hsocp
    (hasRankCaseNegativeCertificateFamily_of_binaryRestrictionComponentData
      hu hsocp.1 hdata)

theorem residual_eq_zero_of_rankCaseApolarComponentData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdata : HasRankCaseApolarComponentData B p u hu) :
    residual p u = 0 :=
  residual_eq_zero_of_hasRankCaseNegativeCertificateFamily
    (B := B) hu hp hsocp
    (hasRankCaseNegativeCertificateFamily_of_apolarComponentData hu hsocp.1 hdata)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_rankCaseNegativeCertificates
    (hcert :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsAdmissiblePoint u →
              IsSOCP B p u →
                HasRankCaseNegativeCertificateFamily B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_hasRankCaseNegativeCertificateFamily
    (B := B) hu hp hsocp (hcert B p u hB hp hu hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_rankCaseSupportData
    (hdata :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseSupportData B p u hu) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_rankCaseSupportData
    (B := B) hu hp hsocp (hdata B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_refinedRankCaseSupportData
    (hdata :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRefinedRankCaseSupportData B p u hu) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_refinedRankCaseSupportData
    (B := B) hu hp hsocp (hdata B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_rankCaseBinaryNormalFormData
    (hdata :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseBinaryNormalFormData B p u hu) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_rankCaseBinaryNormalFormData
    (B := B) hu hp hsocp (hdata B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_rankCaseBinaryRestrictionData
    (hdata :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseBinaryRestrictionData B p u hu) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_rankCaseBinaryRestrictionData
    (B := B) hu hp hsocp (hdata B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_rankCaseBinaryRestrictionComponentData
    (hdata :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseBinaryRestrictionComponentData B p u hu) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_rankCaseBinaryRestrictionComponentData
    (B := B) hu hp hsocp (hdata B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_rankCaseApolarComponentData
    (hdata :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseApolarComponentData B p u hu) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_rankCaseApolarComponentData
    (B := B) hu hp hsocp (hdata B p u hu hB hp hsocp)

/-
Helper lemmas for the quaternary quartic rank-7 proof go here.
Exploration agents should add new Lean code to files in this folder
(`QuaternaryQuarticProof/`), not to the root `QuaternaryQuarticProof.lean`.

The theorem below is a temporary scaffold axiom used to keep the new proof
track buildable while the actual proof decomposition is still being developed.
It must be replaced by proof-serving lemmas and a real derivation.
-/

axiom quaternaryQuartic_rankSeven_no_spurious_socp_placeholder :
    QuaternaryQuarticRankSevenNoSpuriousSOCP

end QuaternaryQuartic
