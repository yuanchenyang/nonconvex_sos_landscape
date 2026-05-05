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

def HasRankCaseProductIndependenceApolarData
    (B : DotForm) (p : Poly) (u : RankSevenVec)
    (_hu : IsAdmissiblePoint u) : Prop :=
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 1 ∧
      (∀ (A W : Submodule ℝ linSubmodule) (x : linSubmodule),
        A ≤ linearAnnihilator B p u →
          IsCompl A W →
            x ∈ W →
              (x : Poly) ≠ 0 →
                Module.finrank ℝ A = 3 →
                  Module.finrank ℝ W = 1 →
                    ∃ β : Module.Basis (Fin 3) ℝ A,
                      LinearIndependent ℝ
                        (Sum.elim
                          (fun i : Fin 3 => linProduct x (β i).1)
                          (fun ij :
                              {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} =>
                            linProduct (β ij.1.1).1 (β ij.1.2).1))) ∧
        ∀ (A W : Submodule ℝ linSubmodule) (x : linSubmodule),
          A ≤ linearAnnihilator B p u →
            IsCompl A W →
              x ∈ W →
                (x : Poly) ≠ 0 →
                  Module.finrank ℝ A = 3 →
                    Module.finrank ℝ W = 1 →
                      binaryRestrictionCoeffA B p u x < 0) ∧
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 2 ∧
      (∀ (A W : Submodule ℝ linSubmodule) (x y : linSubmodule),
        A ≤ linearAnnihilator B p u →
          IsCompl A W →
            x ∈ W →
              y ∈ W →
                y ∉ ℝ ∙ x →
                  (x : Poly) ≠ 0 →
                    Module.finrank ℝ A = 2 →
                      Module.finrank ℝ W = 2 →
                        HasBinaryRestrictionKernelEquationCase B p u x y) ∧
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
                                    (fun ij :
                                        {ij : Fin 2 × Fin 2 // ij.1 ≤ ij.2} =>
                                      linProduct (β ij.1.1).1 (β ij.1.2).1))) ∧
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 3 ∧
      ∃ (W : Submodule ℝ linSubmodule) (q : quadSubmodule),
        q ∈ linProductSubmodule W W ∧
          B (q.1^2) (residual p u) < 0)

def HasRankCaseProductFreeApolarData
    (B : DotForm) (p : Poly) (u : RankSevenVec)
    (_hu : IsAdmissiblePoint u) : Prop :=
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 1 ∧
      ∀ (A W : Submodule ℝ linSubmodule) (x : linSubmodule),
        A ≤ linearAnnihilator B p u →
          IsCompl A W →
            x ∈ W →
              (x : Poly) ≠ 0 →
                Module.finrank ℝ A = 3 →
                  Module.finrank ℝ W = 1 →
                    binaryRestrictionCoeffA B p u x < 0) ∧
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 2 ∧
      ∀ (A W : Submodule ℝ linSubmodule) (x y : linSubmodule),
        A ≤ linearAnnihilator B p u →
          IsCompl A W →
            x ∈ W →
              y ∈ W →
                y ∉ ℝ ∙ x →
                  (x : Poly) ≠ 0 →
                    Module.finrank ℝ A = 2 →
                      Module.finrank ℝ W = 2 →
                        HasBinaryRestrictionKernelEquationCase B p u x y) ∧
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 3 ∧
      ∃ (W : Submodule ℝ linSubmodule) (q : quadSubmodule),
        q ∈ linProductSubmodule W W ∧
          B (q.1^2) (residual p u) < 0)

def HasRankCaseRankOneFreeApolarData
    (B : DotForm) (p : Poly) (u : RankSevenVec)
    (_hu : IsAdmissiblePoint u) : Prop :=
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 1) ∧
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 2 ∧
      ∀ (A W : Submodule ℝ linSubmodule) (x y : linSubmodule),
        A ≤ linearAnnihilator B p u →
          IsCompl A W →
            x ∈ W →
              y ∈ W →
                y ∉ ℝ ∙ x →
                  (x : Poly) ≠ 0 →
                    Module.finrank ℝ A = 2 →
                      Module.finrank ℝ W = 2 →
                        HasBinaryRestrictionKernelEquationCase B p u x y) ∧
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 3 ∧
      ∃ (W : Submodule ℝ linSubmodule) (q : quadSubmodule),
        q ∈ linProductSubmodule W W ∧
          B (q.1^2) (residual p u) < 0)

def HasRankCaseBinaryFormApolarData
    (B : DotForm) (p : Poly) (u : RankSevenVec)
    (_hu : IsAdmissiblePoint u) : Prop :=
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 1) ∧
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 2 ∧
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
                          (binaryRestrictionCoeffE B p u y)) ∧
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 3 ∧
      ∃ (W : Submodule ℝ linSubmodule) (q : quadSubmodule),
        q ∈ linProductSubmodule W W ∧
          B (q.1^2) (residual p u) < 0)

def HasRankCaseBinaryFormAndAnnihilatorData
    (B : DotForm) (p : Poly) (u : RankSevenVec)
    (_hu : IsAdmissiblePoint u) : Prop :=
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 1) ∧
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 2 ∧
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
                          (binaryRestrictionCoeffE B p u y)) ∧
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 3)

def HasRankCaseExistentialBinaryFormData
    (B : DotForm) (p : Poly) (u : RankSevenVec)
    (_hu : IsAdmissiblePoint u) : Prop :=
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 1) ∧
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 2 ∧
      ∀ (A W : Submodule ℝ linSubmodule) (x : linSubmodule),
        A ≤ linearAnnihilator B p u →
          IsCompl A W →
            x ∈ W →
              (x : Poly) ≠ 0 →
                Module.finrank ℝ A = 2 →
                  Module.finrank ℝ W = 2 →
                    ∃ y : linSubmodule,
                      y ∈ W ∧
                        y ∉ ℝ ∙ x ∧
                          HasBinaryLowRankNegativeNormalForm
                            (binaryRestrictionCoeffA B p u x)
                            (binaryRestrictionCoeffB B p u x y)
                            (binaryRestrictionCoeffC B p u x y)
                            (binaryRestrictionCoeffD B p u x y)
                            (binaryRestrictionCoeffE B p u y)) ∧
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 3)

def HasRankCaseKernelDecompositionApolarData
    (B : DotForm) (p : Poly) (u : RankSevenVec)
    (_hu : IsAdmissiblePoint u) : Prop :=
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 1 ∧
      (∀ (A W : Submodule ℝ linSubmodule) (x : linSubmodule),
        A ≤ linearAnnihilator B p u →
          IsCompl A W →
            x ∈ W →
              (x : Poly) ≠ 0 →
                Module.finrank ℝ A = 3 →
                  Module.finrank ℝ W = 1 →
                    ∃ β : Module.Basis (Fin 3) ℝ A,
                      LinearIndependent ℝ
                        (Sum.elim
                          (fun i : Fin 3 => linProduct x (β i).1)
                          (fun ij :
                              {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} =>
                            linProduct (β ij.1.1).1 (β ij.1.2).1))) ∧
        ∀ (A W : Submodule ℝ linSubmodule) (x : linSubmodule),
          A ≤ linearAnnihilator B p u →
            IsCompl A W →
              x ∈ W →
                (x : Poly) ≠ 0 →
                  Module.finrank ℝ A = 3 →
                    Module.finrank ℝ W = 1 →
                      binaryRestrictionCoeffA B p u x < 0) ∧
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 2 ∧
      (∀ (A W : Submodule ℝ linSubmodule) (x y : linSubmodule),
        A ≤ linearAnnihilator B p u →
          IsCompl A W →
            x ∈ W →
              y ∈ W →
                y ∉ ℝ ∙ x →
                  (x : Poly) ≠ 0 →
                    Module.finrank ℝ A = 2 →
                      Module.finrank ℝ W = 2 →
                        HasBinaryRestrictionKernelEquationCase B p u x y) ∧
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
                                    (fun ij :
                                        {ij : Fin 2 × Fin 2 // ij.1 ≤ ij.2} =>
                                      linProduct (β ij.1.1).1 (β ij.1.2).1))) ∧
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 3 ∧
      ∀ q : quadSubmodule,
        B (q.1^2) (residual p u) < 0 →
          ∃ (W : Submodule ℝ linSubmodule) (qW qK : quadSubmodule),
            q = qW + qK ∧
              qW ∈ linProductSubmodule W W ∧
                qK ∈ LinearMap.ker (catalecticantMap B p u))

theorem hasRankCaseApolarComponentData_of_component_obligations
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hann1 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
        Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 1)
    (hSym1 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
        ∀ (A W : Submodule ℝ linSubmodule) (x : linSubmodule),
          A ≤ linearAnnihilator B p u →
            IsCompl A W →
              x ∈ W →
                (x : Poly) ≠ 0 →
                  Module.finrank ℝ A = 3 →
                    Module.finrank ℝ W = 1 →
                      Module.finrank ℝ (symSquareSubmodule A) = 6)
    (hneg1 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
        ∀ (A W : Submodule ℝ linSubmodule) (x : linSubmodule),
          A ≤ linearAnnihilator B p u →
            IsCompl A W →
              x ∈ W →
                (x : Poly) ≠ 0 →
                  Module.finrank ℝ A = 3 →
                    Module.finrank ℝ W = 1 →
                      binaryRestrictionCoeffA B p u x < 0)
    (hann2 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
        Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 2)
    (hSym2 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
        ∀ (A W : Submodule ℝ linSubmodule) (x : linSubmodule),
          A ≤ linearAnnihilator B p u →
            IsCompl A W →
              x ∈ W →
                (x : Poly) ≠ 0 →
                  Module.finrank ℝ A = 2 →
                    Module.finrank ℝ W = 2 →
                      Module.finrank ℝ (symSquareSubmodule A) = 3)
    (hcase2 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
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
    (hdisj2 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
        ∀ (A W : Submodule ℝ linSubmodule) (z : linSubmodule),
          A ≤ linearAnnihilator B p u →
            IsCompl A W →
              z ∈ W →
                (z : Poly) ≠ 0 →
                  Module.finrank ℝ A = 2 →
                    Module.finrank ℝ W = 2 →
                      LinearMap.range (linProductLeftMapOn z A) ⊓
                          symSquareSubmodule A =
                        ⊥)
    (hdata3 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
        HasRankThreeAnnihilatorSupportData B p u) :
    HasRankCaseApolarComponentData B p u hu := by
  constructor
  · intro hrank1
    exact ⟨
      hasLinearAnnihilatorCodimAtMost_one_of_annihilatorMap_range
        (B := B) (p := p) (u := u) (hann1 hrank1),
      hasRankOneSupportComponentHypothesis_of_self_negative
        (B := B) (p := p) (u := u)
        (hSym1 hrank1) (hneg1 hrank1)⟩
  constructor
  · intro hrank2
    exact ⟨
      hasLinearAnnihilatorCodimAtMost_two_of_annihilatorMap_range
        (B := B) (p := p) (u := u) (hann2 hrank2),
      hasRankTwoSupportComponentHypothesis_of_independent_binary_cases
        (B := B) (p := p) (u := u)
        (hSym2 hrank2) (hcase2 hrank2) (hdisj2 hrank2)⟩
  · intro hrank3
    exact hdata3 hrank3

theorem hasRankCaseApolarComponentData_of_component_obligations_with_rank_three_support
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hann1 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
        Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 1)
    (hSym1 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
        ∀ (A W : Submodule ℝ linSubmodule) (x : linSubmodule),
          A ≤ linearAnnihilator B p u →
            IsCompl A W →
              x ∈ W →
                (x : Poly) ≠ 0 →
                  Module.finrank ℝ A = 3 →
                    Module.finrank ℝ W = 1 →
                      Module.finrank ℝ (symSquareSubmodule A) = 6)
    (hneg1 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
        ∀ (A W : Submodule ℝ linSubmodule) (x : linSubmodule),
          A ≤ linearAnnihilator B p u →
            IsCompl A W →
              x ∈ W →
                (x : Poly) ≠ 0 →
                  Module.finrank ℝ A = 3 →
                    Module.finrank ℝ W = 1 →
                      binaryRestrictionCoeffA B p u x < 0)
    (hann2 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
        Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 2)
    (hSym2 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
        ∀ (A W : Submodule ℝ linSubmodule) (x : linSubmodule),
          A ≤ linearAnnihilator B p u →
            IsCompl A W →
              x ∈ W →
                (x : Poly) ≠ 0 →
                  Module.finrank ℝ A = 2 →
                    Module.finrank ℝ W = 2 →
                      Module.finrank ℝ (symSquareSubmodule A) = 3)
    (hcase2 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
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
    (hdisj2 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
        ∀ (A W : Submodule ℝ linSubmodule) (z : linSubmodule),
          A ≤ linearAnnihilator B p u →
            IsCompl A W →
              z ∈ W →
                (z : Poly) ≠ 0 →
                  Module.finrank ℝ A = 2 →
                    Module.finrank ℝ W = 2 →
                      LinearMap.range (linProductLeftMapOn z A) ⊓
                          symSquareSubmodule A =
                        ⊥)
    (hann3 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
        Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 3)
    (hneg3 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
        ∃ (W : Submodule ℝ linSubmodule) (q : quadSubmodule),
          q ∈ linProductSubmodule W W ∧
            B (q.1^2) (residual p u) < 0) :
    HasRankCaseApolarComponentData B p u hu :=
  hasRankCaseApolarComponentData_of_component_obligations
    (B := B) (p := p) (u := u) (hu := hu)
    hann1 hSym1 hneg1 hann2 hSym2 hcase2 hdisj2
    (fun hrank3 =>
      let hsupp :=
        hasLinearAnnihilatorCodimAtMost_three_of_annihilatorMap_range
          (B := B) (p := p) (u := u) (hann3 hrank3)
      let hneg := hneg3 hrank3
      match hneg with
      | ⟨_W, _q, hqWW, hqneg⟩ =>
        hasRankThreeAnnihilatorSupportData_of_rank_three_support
          (B := B) (p := p) (u := u) hsupp hqWW hqneg)

theorem hasRankCaseApolarComponentData_of_binary_plane_component_obligations
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hann1 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
        Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 1)
    (hSym1 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
        ∀ (A W : Submodule ℝ linSubmodule) (x : linSubmodule),
          A ≤ linearAnnihilator B p u →
            IsCompl A W →
              x ∈ W →
                (x : Poly) ≠ 0 →
                  Module.finrank ℝ A = 3 →
                    Module.finrank ℝ W = 1 →
                      Module.finrank ℝ (symSquareSubmodule A) = 6)
    (hneg1 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
        ∀ (A W : Submodule ℝ linSubmodule) (x : linSubmodule),
          A ≤ linearAnnihilator B p u →
            IsCompl A W →
              x ∈ W →
                (x : Poly) ≠ 0 →
                  Module.finrank ℝ A = 3 →
                    Module.finrank ℝ W = 1 →
                      binaryRestrictionCoeffA B p u x < 0)
    (hann2 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
        Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 2)
    (hSym2 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
        ∀ (A W : Submodule ℝ linSubmodule) (x : linSubmodule),
          A ≤ linearAnnihilator B p u →
            IsCompl A W →
              x ∈ W →
                (x : Poly) ≠ 0 →
                  Module.finrank ℝ A = 2 →
                    Module.finrank ℝ W = 2 →
                      Module.finrank ℝ (symSquareSubmodule A) = 3)
    (hcase2 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
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
    (hdisj2 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
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
                                ⊥)
    (hann3 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
        Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 3)
    (hneg3 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
        ∃ (W : Submodule ℝ linSubmodule) (q : quadSubmodule),
          q ∈ linProductSubmodule W W ∧
            B (q.1^2) (residual p u) < 0) :
    HasRankCaseApolarComponentData B p u hu := by
  constructor
  · intro hrank1
    exact ⟨
      hasLinearAnnihilatorCodimAtMost_one_of_annihilatorMap_range
        (B := B) (p := p) (u := u) (hann1 hrank1),
      hasRankOneSupportComponentHypothesis_of_self_negative
        (B := B) (p := p) (u := u)
        (hSym1 hrank1) (hneg1 hrank1)⟩
  constructor
  · intro hrank2
    exact ⟨
      hasLinearAnnihilatorCodimAtMost_two_of_annihilatorMap_range
        (B := B) (p := p) (u := u) (hann2 hrank2),
      hasRankTwoSupportComponentHypothesis_of_independent_binary_plane_cases
        (B := B) (p := p) (u := u)
        (hSym2 hrank2) (hcase2 hrank2) (hdisj2 hrank2)⟩
  · intro hrank3
    have hsupp : HasLinearAnnihilatorCodimAtMost B p u 3 :=
      hasLinearAnnihilatorCodimAtMost_three_of_annihilatorMap_range
        (B := B) (p := p) (u := u) (hann3 hrank3)
    rcases hneg3 hrank3 with ⟨W, q, hqWW, hqneg⟩
    exact hasRankThreeAnnihilatorSupportData_of_rank_three_support
      (B := B) (p := p) (u := u) hsupp hqWW hqneg

theorem hasRankCaseApolarComponentData_of_productLI_component_obligations
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hann1 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
        Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 1)
    (hSym1 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
        ∀ (A W : Submodule ℝ linSubmodule) (x : linSubmodule),
          A ≤ linearAnnihilator B p u →
            IsCompl A W →
              x ∈ W →
                (x : Poly) ≠ 0 →
                  Module.finrank ℝ A = 3 →
                    Module.finrank ℝ W = 1 →
                      Module.finrank ℝ (symSquareSubmodule A) = 6)
    (hneg1 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
        ∀ (A W : Submodule ℝ linSubmodule) (x : linSubmodule),
          A ≤ linearAnnihilator B p u →
            IsCompl A W →
              x ∈ W →
                (x : Poly) ≠ 0 →
                  Module.finrank ℝ A = 3 →
                    Module.finrank ℝ W = 1 →
                      binaryRestrictionCoeffA B p u x < 0)
    (hann2 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
        Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 2)
    (hSym2 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
        ∀ (A W : Submodule ℝ linSubmodule) (x : linSubmodule),
          A ≤ linearAnnihilator B p u →
            IsCompl A W →
              x ∈ W →
                (x : Poly) ≠ 0 →
                  Module.finrank ℝ A = 2 →
                    Module.finrank ℝ W = 2 →
                      Module.finrank ℝ (symSquareSubmodule A) = 3)
    (hcase2 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
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
    (hprodLI2 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
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
                                    (fun ij :
                                        {ij : Fin 2 × Fin 2 // ij.1 ≤ ij.2} =>
                                      linProduct (β ij.1.1).1 (β ij.1.2).1)))
    (hann3 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
        Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 3)
    (hneg3 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
        ∃ (W : Submodule ℝ linSubmodule) (q : quadSubmodule),
          q ∈ linProductSubmodule W W ∧
            B (q.1^2) (residual p u) < 0) :
    HasRankCaseApolarComponentData B p u hu := by
  exact hasRankCaseApolarComponentData_of_binary_plane_component_obligations
    (B := B) (p := p) (u := u) (hu := hu)
    hann1 hSym1 hneg1 hann2 hSym2 hcase2
    (fun hrank2 A W x y z hAann hAW hxW hyW hynot hx hAdim hWdim hzspan hz =>
      let hβ :=
        hprodLI2 hrank2 A W x y z hAann hAW hxW hyW hynot hx hAdim hWdim hzspan hz
      match hβ with
      | ⟨β, hLI⟩ =>
        range_linProductLeftMapOn_inf_symSquare_eq_bot_of_basis_products_linearIndependent
          (A := A) (z := z) β hLI)
    hann3 hneg3

theorem hasRankCaseApolarComponentData_of_product_independence_component_obligations
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hann1 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
        Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 1)
    (hSymLI1 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
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
    (hneg1 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
        ∀ (A W : Submodule ℝ linSubmodule) (x : linSubmodule),
          A ≤ linearAnnihilator B p u →
            IsCompl A W →
              x ∈ W →
                (x : Poly) ≠ 0 →
                  Module.finrank ℝ A = 3 →
                    Module.finrank ℝ W = 1 →
                      binaryRestrictionCoeffA B p u x < 0)
    (hann2 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
        Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 2)
    (hSymLI2 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
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
    (hcase2 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
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
    (hprodLI2 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
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
                                    (fun ij :
                                        {ij : Fin 2 × Fin 2 // ij.1 ≤ ij.2} =>
                                      linProduct (β ij.1.1).1 (β ij.1.2).1)))
    (hann3 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
        Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 3)
    (hneg3 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
        ∃ (W : Submodule ℝ linSubmodule) (q : quadSubmodule),
          q ∈ linProductSubmodule W W ∧
            B (q.1^2) (residual p u) < 0) :
    HasRankCaseApolarComponentData B p u hu := by
  exact hasRankCaseApolarComponentData_of_productLI_component_obligations
    (B := B) (p := p) (u := u) (hu := hu)
    hann1
    (fun hrank1 A W x hAann hAW hxW hx hAdim hWdim =>
      match hSymLI1 hrank1 A W x hAann hAW hxW hx hAdim hWdim with
      | ⟨β, hLI⟩ =>
        finrank_symSquareSubmodule_eq_six_of_basis_products_linearIndependent β hLI)
    hneg1
    hann2
    (fun hrank2 A W x hAann hAW hxW hx hAdim hWdim =>
      match hSymLI2 hrank2 A W x hAann hAW hxW hx hAdim hWdim with
      | ⟨β, hLI⟩ =>
        finrank_symSquareSubmodule_eq_three_of_basis_products_linearIndependent β hLI)
    hcase2 hprodLI2 hann3 hneg3

theorem hasRankCaseApolarComponentData_of_rank_two_productLI_component_obligations
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hann1 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
        Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 1)
    (hSymLI1 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
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
    (hneg1 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
        ∀ (A W : Submodule ℝ linSubmodule) (x : linSubmodule),
          A ≤ linearAnnihilator B p u →
            IsCompl A W →
              x ∈ W →
                (x : Poly) ≠ 0 →
                  Module.finrank ℝ A = 3 →
                    Module.finrank ℝ W = 1 →
                      binaryRestrictionCoeffA B p u x < 0)
    (hann2 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
        Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 2)
    (hcase2 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
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
    (hprodLI2 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
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
                                    (fun ij :
                                        {ij : Fin 2 × Fin 2 // ij.1 ≤ ij.2} =>
                                      linProduct (β ij.1.1).1 (β ij.1.2).1)))
    (hann3 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
        Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 3)
    (hneg3 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
        ∃ (W : Submodule ℝ linSubmodule) (q : quadSubmodule),
          q ∈ linProductSubmodule W W ∧
            B (q.1^2) (residual p u) < 0) :
    HasRankCaseApolarComponentData B p u hu := by
  constructor
  · intro hrank1
    exact ⟨
      hasLinearAnnihilatorCodimAtMost_one_of_annihilatorMap_range
        (B := B) (p := p) (u := u) (hann1 hrank1),
      hasRankOneSupportComponentHypothesis_of_basis_product_independence
        (B := B) (p := p) (u := u)
        (hSymLI1 hrank1) (hneg1 hrank1)⟩
  constructor
  · intro hrank2
    exact ⟨
      hasLinearAnnihilatorCodimAtMost_two_of_annihilatorMap_range
        (B := B) (p := p) (u := u) (hann2 hrank2),
      hasRankTwoSupportComponentHypothesis_of_binary_cases_and_productLI
        (B := B) (p := p) (u := u)
        (hcase2 hrank2) (hprodLI2 hrank2)⟩
  · intro hrank3
    have hsupp : HasLinearAnnihilatorCodimAtMost B p u 3 :=
      hasLinearAnnihilatorCodimAtMost_three_of_annihilatorMap_range
        (B := B) (p := p) (u := u) (hann3 hrank3)
    rcases hneg3 hrank3 with ⟨W, q, hqWW, hqneg⟩
    exact hasRankThreeAnnihilatorSupportData_of_rank_three_support
      (B := B) (p := p) (u := u) hsupp hqWW hqneg

theorem hasRankCaseApolarComponentData_of_combined_productLI_component_obligations
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hann1 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
        Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 1)
    (hprodLI1 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
        ∀ (A W : Submodule ℝ linSubmodule) (x : linSubmodule),
          A ≤ linearAnnihilator B p u →
            IsCompl A W →
              x ∈ W →
                (x : Poly) ≠ 0 →
                  Module.finrank ℝ A = 3 →
                    Module.finrank ℝ W = 1 →
                      ∃ β : Module.Basis (Fin 3) ℝ A,
                        LinearIndependent ℝ
                          (Sum.elim
                            (fun i : Fin 3 => linProduct x (β i).1)
                            (fun ij :
                                {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} =>
                              linProduct (β ij.1.1).1 (β ij.1.2).1)))
    (hneg1 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
        ∀ (A W : Submodule ℝ linSubmodule) (x : linSubmodule),
          A ≤ linearAnnihilator B p u →
            IsCompl A W →
              x ∈ W →
                (x : Poly) ≠ 0 →
                  Module.finrank ℝ A = 3 →
                    Module.finrank ℝ W = 1 →
                      binaryRestrictionCoeffA B p u x < 0)
    (hann2 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
        Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 2)
    (hcase2 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
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
    (hprodLI2 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
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
                                    (fun ij :
                                        {ij : Fin 2 × Fin 2 // ij.1 ≤ ij.2} =>
                                      linProduct (β ij.1.1).1 (β ij.1.2).1)))
    (hann3 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
        Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 3)
    (hneg3 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
        ∃ (W : Submodule ℝ linSubmodule) (q : quadSubmodule),
          q ∈ linProductSubmodule W W ∧
            B (q.1^2) (residual p u) < 0) :
    HasRankCaseApolarComponentData B p u hu := by
  constructor
  · intro hrank1
    exact ⟨
      hasLinearAnnihilatorCodimAtMost_one_of_annihilatorMap_range
        (B := B) (p := p) (u := u) (hann1 hrank1),
      hasRankOneSupportComponentHypothesis_of_combined_product_independence
        (B := B) (p := p) (u := u)
        (hprodLI1 hrank1) (hneg1 hrank1)⟩
  constructor
  · intro hrank2
    exact ⟨
      hasLinearAnnihilatorCodimAtMost_two_of_annihilatorMap_range
        (B := B) (p := p) (u := u) (hann2 hrank2),
      hasRankTwoSupportComponentHypothesis_of_binary_cases_and_productLI
        (B := B) (p := p) (u := u)
        (hcase2 hrank2) (hprodLI2 hrank2)⟩
  · intro hrank3
    have hsupp : HasLinearAnnihilatorCodimAtMost B p u 3 :=
      hasLinearAnnihilatorCodimAtMost_three_of_annihilatorMap_range
        (B := B) (p := p) (u := u) (hann3 hrank3)
    rcases hneg3 hrank3 with ⟨W, q, hqWW, hqneg⟩
    exact hasRankThreeAnnihilatorSupportData_of_rank_three_support
      (B := B) (p := p) (u := u) hsupp hqWW hqneg

theorem hasRankCaseApolarComponentData_of_product_free_component_obligations
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hann1 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
        Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 1)
    (hneg1 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
        ∀ (A W : Submodule ℝ linSubmodule) (x : linSubmodule),
          A ≤ linearAnnihilator B p u →
            IsCompl A W →
              x ∈ W →
                (x : Poly) ≠ 0 →
                  Module.finrank ℝ A = 3 →
                    Module.finrank ℝ W = 1 →
                      binaryRestrictionCoeffA B p u x < 0)
    (hann2 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
        Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 2)
    (hcase2 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
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
    (hann3 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
        Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 3)
    (hneg3 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
        ∃ (W : Submodule ℝ linSubmodule) (q : quadSubmodule),
          q ∈ linProductSubmodule W W ∧
            B (q.1^2) (residual p u) < 0) :
    HasRankCaseApolarComponentData B p u hu := by
  constructor
  · intro hrank1
    exact ⟨
      hasLinearAnnihilatorCodimAtMost_one_of_annihilatorMap_range
        (B := B) (p := p) (u := u) (hann1 hrank1),
      hasRankOneSupportComponentHypothesis_of_combined_product_independence
        (B := B) (p := p) (u := u)
        (fun A W x _hAann hAW hxW hx hAdim hWdim =>
          exists_rank_one_combined_product_independence hAW hxW hx hAdim hWdim)
        (hneg1 hrank1)⟩
  constructor
  · intro hrank2
    exact ⟨
      hasLinearAnnihilatorCodimAtMost_two_of_annihilatorMap_range
        (B := B) (p := p) (u := u) (hann2 hrank2),
      hasRankTwoSupportComponentHypothesis_of_binary_cases_and_productLI
        (B := B) (p := p) (u := u)
        (hcase2 hrank2)
        (fun A W x y z _hAann hAW hxW hyW hy hx hAdim hWdim hzspan hz =>
          exists_rank_two_combined_product_independence
            hAW hxW hyW hy hx hAdim hWdim hzspan hz)⟩
  · intro hrank3
    have hsupp : HasLinearAnnihilatorCodimAtMost B p u 3 :=
      hasLinearAnnihilatorCodimAtMost_three_of_annihilatorMap_range
        (B := B) (p := p) (u := u) (hann3 hrank3)
    rcases hneg3 hrank3 with ⟨W, q, hqWW, hqneg⟩
    exact hasRankThreeAnnihilatorSupportData_of_rank_three_support
      (B := B) (p := p) (u := u) hsupp hqWW hqneg

theorem hasRankCaseApolarComponentData_of_productIndependenceApolarData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hdata : HasRankCaseProductIndependenceApolarData B p u hu) :
    HasRankCaseApolarComponentData B p u hu := by
  rcases hdata with ⟨hdata1, hdata2, hdata3⟩
  exact hasRankCaseApolarComponentData_of_combined_productLI_component_obligations
    (B := B) (p := p) (u := u) (hu := hu)
    (fun hrank1 => (hdata1 hrank1).1)
    (fun hrank1 => (hdata1 hrank1).2.1)
    (fun hrank1 => (hdata1 hrank1).2.2)
    (fun hrank2 => (hdata2 hrank2).1)
    (fun hrank2 => (hdata2 hrank2).2.1)
    (fun hrank2 => (hdata2 hrank2).2.2)
    (fun hrank3 => (hdata3 hrank3).1)
    (fun hrank3 => (hdata3 hrank3).2)

theorem hasRankCaseApolarComponentData_of_productFreeApolarData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hdata : HasRankCaseProductFreeApolarData B p u hu) :
    HasRankCaseApolarComponentData B p u hu := by
  rcases hdata with ⟨hdata1, hdata2, hdata3⟩
  exact hasRankCaseApolarComponentData_of_product_free_component_obligations
    (B := B) (p := p) (u := u) (hu := hu)
    (fun hrank1 => (hdata1 hrank1).1)
    (fun hrank1 => (hdata1 hrank1).2)
    (fun hrank2 => (hdata2 hrank2).1)
    (fun hrank2 => (hdata2 hrank2).2)
    (fun hrank3 => (hdata3 hrank3).1)
    (fun hrank3 => (hdata3 hrank3).2)

theorem hasRankCaseProductFreeApolarData_of_rankOneFreeApolarData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u)
    (hdata : HasRankCaseRankOneFreeApolarData B p u hu) :
    HasRankCaseProductFreeApolarData B p u hu := by
  rcases hdata with ⟨hdata1, hdata2, hdata3⟩
  constructor
  · intro hrank1
    refine ⟨hdata1 hrank1, ?_⟩
    intro A W x hAann hAW hxW hx _hAdim hWdim
    exact rank_one_binaryRestrictionCoeffA_neg_of_annihilator_complement
      (B := B) (p := p) (u := u) hu hp hfocp hrank1
      hAann hAW hxW hx hWdim
  constructor
  · intro hrank2
    exact hdata2 hrank2
  · intro hrank3
    exact hdata3 hrank3

theorem hasRankCaseApolarComponentData_of_binaryFormApolarData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u)
    (hdata : HasRankCaseBinaryFormApolarData B p u hu) :
    HasRankCaseApolarComponentData B p u hu := by
  rcases hdata with ⟨hdata1, hdata2, hdata3⟩
  constructor
  · intro hrank1
    exact ⟨
      hasLinearAnnihilatorCodimAtMost_one_of_annihilatorMap_range
        (B := B) (p := p) (u := u) (hdata1 hrank1),
      hasRankOneSupportComponentHypothesis_of_combined_product_independence
        (B := B) (p := p) (u := u)
        (fun A W x _hAann hAW hxW hx hAdim hWdim =>
          exists_rank_one_combined_product_independence hAW hxW hx hAdim hWdim)
        (fun A W x hAann hAW hxW hx _hAdim hWdim =>
          rank_one_binaryRestrictionCoeffA_neg_of_annihilator_complement
            (B := B) (p := p) (u := u) hu hp hfocp hrank1
            hAann hAW hxW hx hWdim)⟩
  constructor
  · intro hrank2
    exact ⟨
      hasLinearAnnihilatorCodimAtMost_two_of_annihilatorMap_range
        (B := B) (p := p) (u := u) (hdata2 hrank2).1,
      hasRankTwoSupportComponentHypothesis_of_binary_forms_and_productLI
        (B := B) (p := p) (u := u)
        (hdata2 hrank2).2
        (fun A W x y z _hAann hAW hxW hyW hy hx hAdim hWdim hzspan hz =>
          exists_rank_two_combined_product_independence
            hAW hxW hyW hy hx hAdim hWdim hzspan hz)⟩
  · intro hrank3
    have hsupp : HasLinearAnnihilatorCodimAtMost B p u 3 :=
      hasLinearAnnihilatorCodimAtMost_three_of_annihilatorMap_range
        (B := B) (p := p) (u := u) (hdata3 hrank3).1
    rcases (hdata3 hrank3).2 with ⟨W, q, hqWW, hqneg⟩
    exact hasRankThreeAnnihilatorSupportData_of_rank_three_support
      (B := B) (p := p) (u := u) hsupp hqWW hqneg

theorem hasRankCaseBinaryFormApolarData_of_binaryFormAndAnnihilatorData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u)
    (hdata : HasRankCaseBinaryFormAndAnnihilatorData B p u hu) :
    HasRankCaseBinaryFormApolarData B p u hu := by
  rcases hdata with ⟨hdata1, hdata2, hdata3⟩
  constructor
  · intro hrank1
    exact hdata1 hrank1
  constructor
  · intro hrank2
    exact hdata2 hrank2
  · intro hrank3
    refine ⟨hdata3 hrank3, ?_⟩
    rcases exists_negative_sos_summand_of_catalecticantMap_rank_eq_three
        (B := B) hu hp hfocp hrank3 with
      ⟨q, hq, hqneg⟩
    let qQuad : quadSubmodule := ⟨q, hq⟩
    rcases exists_rank_three_catalecticantKernel_decomposition_of_annihilatorMap_range
        (B := B) (p := p) (u := u) (hdata3 hrank3) qQuad with
      ⟨W, qW, qK, hqdecomp, hqW, hqK⟩
    exact ⟨W, qW, hqW,
      residualEval_sq_lt_of_eq_add_mem_ker_catalecticantMap
        (B := B) (p := p) (u := u) hqdecomp hqK hqneg⟩

theorem hasRankCaseApolarComponentData_of_existentialBinaryFormData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u)
    (hdata : HasRankCaseExistentialBinaryFormData B p u hu) :
    HasRankCaseApolarComponentData B p u hu := by
  rcases hdata with ⟨hdata1, hdata2, hdata3⟩
  constructor
  · intro hrank1
    exact ⟨
      hasLinearAnnihilatorCodimAtMost_one_of_annihilatorMap_range
        (B := B) (p := p) (u := u) (hdata1 hrank1),
      hasRankOneSupportComponentHypothesis_of_combined_product_independence
        (B := B) (p := p) (u := u)
        (fun A W x _hAann hAW hxW hx hAdim hWdim =>
          exists_rank_one_combined_product_independence hAW hxW hx hAdim hWdim)
        (fun A W x hAann hAW hxW hx _hAdim hWdim =>
          rank_one_binaryRestrictionCoeffA_neg_of_annihilator_complement
            (B := B) (p := p) (u := u) hu hp hfocp hrank1
            hAann hAW hxW hx hWdim)⟩
  constructor
  · intro hrank2
    exact ⟨
      hasLinearAnnihilatorCodimAtMost_two_of_annihilatorMap_range
        (B := B) (p := p) (u := u) (hdata2 hrank2).1,
      hasRankTwoSupportComponentHypothesis_of_exists_binary_form_and_productLI
        (B := B) (p := p) (u := u)
        (hdata2 hrank2).2
        (fun A W x y z _hAann hAW hxW hyW hy hx hAdim hWdim hzspan hz =>
          exists_rank_two_combined_product_independence
            hAW hxW hyW hy hx hAdim hWdim hzspan hz)⟩
  · intro hrank3
    have hsupp : HasLinearAnnihilatorCodimAtMost B p u 3 :=
      hasLinearAnnihilatorCodimAtMost_three_of_annihilatorMap_range
        (B := B) (p := p) (u := u) (hdata3 hrank3)
    rcases exists_negative_sos_summand_of_catalecticantMap_rank_eq_three
        (B := B) hu hp hfocp hrank3 with
      ⟨q, hq, hqneg⟩
    let qQuad : quadSubmodule := ⟨q, hq⟩
    rcases exists_rank_three_catalecticantKernel_decomposition_of_annihilatorMap_range
        (B := B) (p := p) (u := u) (hdata3 hrank3) qQuad with
      ⟨W, qW, qK, hqdecomp, hqW, hqK⟩
    exact hasRankThreeAnnihilatorSupportData_of_rank_three_support
      (B := B) (p := p) (u := u) hsupp hqW
      (residualEval_sq_lt_of_eq_add_mem_ker_catalecticantMap
        (B := B) (p := p) (u := u) hqdecomp hqK hqneg)

theorem hasRankCaseKernelDecompositionApolarData_of_productIndependenceApolarData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hdata : HasRankCaseProductIndependenceApolarData B p u hu) :
    HasRankCaseKernelDecompositionApolarData B p u hu := by
  rcases hdata with ⟨hdata1, hdata2, hdata3⟩
  constructor
  · intro hrank1
    exact hdata1 hrank1
  constructor
  · intro hrank2
    exact hdata2 hrank2
  · intro hrank3
    refine ⟨(hdata3 hrank3).1, ?_⟩
    intro q _hqneg
    exact exists_rank_three_catalecticantKernel_decomposition_of_annihilatorMap_range
      (B := B) (p := p) (u := u) (hdata3 hrank3).1 q

theorem hasRankCaseProductIndependenceApolarData_of_kernelDecompositionApolarData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u)
    (hdata : HasRankCaseKernelDecompositionApolarData B p u hu) :
    HasRankCaseProductIndependenceApolarData B p u hu := by
  rcases hdata with ⟨hdata1, hdata2, hdata3⟩
  constructor
  · intro hrank1
    exact hdata1 hrank1
  constructor
  · intro hrank2
    exact hdata2 hrank2
  · intro hrank3
    refine ⟨(hdata3 hrank3).1, ?_⟩
    rcases exists_negative_sos_summand_of_catalecticantMap_rank_eq_three
        (B := B) hu hp hfocp hrank3 with
      ⟨q, hq, hqneg⟩
    let qQuad : quadSubmodule := ⟨q, hq⟩
    rcases (hdata3 hrank3).2 qQuad hqneg with
      ⟨W, qW, qK, hqdecomp, hqW, hqK⟩
    exact ⟨W, qW, hqW,
      residualEval_sq_lt_of_eq_add_mem_ker_catalecticantMap
        (B := B) (p := p) (u := u) hqdecomp hqK hqneg⟩

theorem hasRankCaseProductFreeApolarData_of_kernelDecompositionApolarData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u)
    (hdata : HasRankCaseKernelDecompositionApolarData B p u hu) :
    HasRankCaseProductFreeApolarData B p u hu := by
  rcases hdata with ⟨hdata1, hdata2, hdata3⟩
  constructor
  · intro hrank1
    exact ⟨(hdata1 hrank1).1, (hdata1 hrank1).2.2⟩
  constructor
  · intro hrank2
    exact ⟨(hdata2 hrank2).1, (hdata2 hrank2).2.1⟩
  · intro hrank3
    refine ⟨(hdata3 hrank3).1, ?_⟩
    rcases exists_negative_sos_summand_of_catalecticantMap_rank_eq_three
        (B := B) hu hp hfocp hrank3 with
      ⟨q, hq, hqneg⟩
    let qQuad : quadSubmodule := ⟨q, hq⟩
    rcases (hdata3 hrank3).2 qQuad hqneg with
      ⟨W, qW, qK, hqdecomp, hqW, hqK⟩
    exact ⟨W, qW, hqW,
      residualEval_sq_lt_of_eq_add_mem_ker_catalecticantMap
        (B := B) (p := p) (u := u) hqdecomp hqK hqneg⟩

theorem hasRankCaseBinaryFormAndAnnihilatorData_of_kernelDecompositionApolarData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hdata : HasRankCaseKernelDecompositionApolarData B p u hu) :
    HasRankCaseBinaryFormAndAnnihilatorData B p u hu := by
  rcases hdata with ⟨hdata1, hdata2, hdata3⟩
  constructor
  · intro hrank1
    exact (hdata1 hrank1).1
  constructor
  · intro hrank2
    refine ⟨(hdata2 hrank2).1, ?_⟩
    intro A W x y hAann hAW hxW hyW hy hx hAdim hWdim
    exact binaryRestriction_lowRankNegativeNormalForm_of_kernelEquationCase
      ((hdata2 hrank2).2.1 A W x y hAann hAW hxW hyW hy hx hAdim hWdim)
  · intro hrank3
    exact (hdata3 hrank3).1

theorem hasRankCaseApolarComponentData_of_kernelDecompositionApolarData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u)
    (hdata : HasRankCaseKernelDecompositionApolarData B p u hu) :
    HasRankCaseApolarComponentData B p u hu := by
  rcases hdata with ⟨hdata1, hdata2, hdata3⟩
  constructor
  · intro hrank1
    exact ⟨
      hasLinearAnnihilatorCodimAtMost_one_of_annihilatorMap_range
        (B := B) (p := p) (u := u) (hdata1 hrank1).1,
      hasRankOneSupportComponentHypothesis_of_combined_product_independence
        (B := B) (p := p) (u := u)
        (hdata1 hrank1).2.1 (hdata1 hrank1).2.2⟩
  constructor
  · intro hrank2
    exact ⟨
      hasLinearAnnihilatorCodimAtMost_two_of_annihilatorMap_range
        (B := B) (p := p) (u := u) (hdata2 hrank2).1,
      hasRankTwoSupportComponentHypothesis_of_binary_cases_and_productLI
        (B := B) (p := p) (u := u)
        (hdata2 hrank2).2.1 (hdata2 hrank2).2.2⟩
  · intro hrank3
    exact hasRankThreeAnnihilatorSupportData_of_rank_three_kernel_decomposition
      (B := B) (p := p) (u := u) hu hp hfocp hrank3
      (hasLinearAnnihilatorCodimAtMost_three_of_annihilatorMap_range
        (B := B) (p := p) (u := u) (hdata3 hrank3).1)
      (hdata3 hrank3).2

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

theorem residual_eq_zero_of_productIndependenceApolarData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdata : HasRankCaseProductIndependenceApolarData B p u hu) :
    residual p u = 0 :=
  residual_eq_zero_of_rankCaseApolarComponentData
    (B := B) hu hp hsocp
    (hasRankCaseApolarComponentData_of_productIndependenceApolarData hdata)

theorem residual_eq_zero_of_productFreeApolarData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdata : HasRankCaseProductFreeApolarData B p u hu) :
    residual p u = 0 :=
  residual_eq_zero_of_rankCaseApolarComponentData
    (B := B) hu hp hsocp
    (hasRankCaseApolarComponentData_of_productFreeApolarData hdata)

theorem residual_eq_zero_of_rankOneFreeApolarData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdata : HasRankCaseRankOneFreeApolarData B p u hu) :
    residual p u = 0 :=
  residual_eq_zero_of_productFreeApolarData
    (B := B) hu hp hsocp
    (hasRankCaseProductFreeApolarData_of_rankOneFreeApolarData
      (B := B) hp hsocp.1 hdata)

theorem residual_eq_zero_of_binaryFormApolarData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdata : HasRankCaseBinaryFormApolarData B p u hu) :
    residual p u = 0 :=
  residual_eq_zero_of_rankCaseApolarComponentData
    (B := B) hu hp hsocp
    (hasRankCaseApolarComponentData_of_binaryFormApolarData
      (B := B) hp hsocp.1 hdata)

theorem residual_eq_zero_of_binaryFormAndAnnihilatorData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdata : HasRankCaseBinaryFormAndAnnihilatorData B p u hu) :
    residual p u = 0 :=
  residual_eq_zero_of_binaryFormApolarData
    (B := B) hu hp hsocp
    (hasRankCaseBinaryFormApolarData_of_binaryFormAndAnnihilatorData
      (B := B) hp hsocp.1 hdata)

theorem residual_eq_zero_of_existentialBinaryFormData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdata : HasRankCaseExistentialBinaryFormData B p u hu) :
    residual p u = 0 :=
  residual_eq_zero_of_rankCaseApolarComponentData
    (B := B) hu hp hsocp
    (hasRankCaseApolarComponentData_of_existentialBinaryFormData
      (B := B) hp hsocp.1 hdata)

theorem residual_eq_zero_of_kernelDecompositionApolarData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdata : HasRankCaseKernelDecompositionApolarData B p u hu) :
    residual p u = 0 :=
  residual_eq_zero_of_binaryFormAndAnnihilatorData
    (B := B) hu hp hsocp
    (hasRankCaseBinaryFormAndAnnihilatorData_of_kernelDecompositionApolarData hdata)

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

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_productIndependenceApolarData
    (hdata :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseProductIndependenceApolarData B p u hu) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_productIndependenceApolarData
    (B := B) hu hp hsocp (hdata B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_productFreeApolarData
    (hdata :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseProductFreeApolarData B p u hu) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_productFreeApolarData
    (B := B) hu hp hsocp (hdata B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_rankOneFreeApolarData
    (hdata :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseRankOneFreeApolarData B p u hu) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_rankOneFreeApolarData
    (B := B) hu hp hsocp (hdata B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_binaryFormApolarData
    (hdata :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseBinaryFormApolarData B p u hu) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_binaryFormApolarData
    (B := B) hu hp hsocp (hdata B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_binaryFormAndAnnihilatorData
    (hdata :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseBinaryFormAndAnnihilatorData B p u hu) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_binaryFormAndAnnihilatorData
    (B := B) hu hp hsocp (hdata B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_existentialBinaryFormData
    (hdata :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseExistentialBinaryFormData B p u hu) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_existentialBinaryFormData
    (B := B) hu hp hsocp (hdata B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_kernelDecompositionApolarData
    (hdata :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseKernelDecompositionApolarData B p u hu) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_kernelDecompositionApolarData
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
