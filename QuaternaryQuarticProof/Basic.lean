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
