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

def HasRankCaseProductIndependenceGeometryData
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

def HasRankCaseNegativeSquareApolarData
    (B : DotForm) (p : Poly) (u : RankSevenVec)
    (_hu : IsAdmissiblePoint u) : Prop :=
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 1) ∧
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 2 ∧
      ∀ (A W : Submodule ℝ linSubmodule),
        A ≤ linearAnnihilator B p u →
          IsCompl A W →
            Module.finrank ℝ A = 2 →
              Module.finrank ℝ W = 2 →
                ∃ x : linSubmodule,
                  x ∈ W ∧
                    (x : Poly) ≠ 0 ∧
                      B ((linProduct x x : quadSubmodule).1^2) (residual p u) < 0) ∧
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 3)

def HasRankCaseAnnihilatorMapBounds
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 1) ∧
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 2) ∧
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 3)

def HasRankOneApolarAnnihilatorMapBound
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 1

def HasRankTwoApolarAnnihilatorMapBound
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 2

def HasRankThreeApolarAnnihilatorMapBound
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 3

def HasRankOneApolarAnnihilatorDimensionBound
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
    3 ≤ Module.finrank ℝ (linearAnnihilator B p u)

def HasRankTwoApolarAnnihilatorDimensionBound
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
    2 ≤ Module.finrank ℝ (linearAnnihilator B p u)

def HasRankThreeApolarAnnihilatorDimensionBound
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
    1 ≤ Module.finrank ℝ (linearAnnihilator B p u)

def HasRankCaseApolarAnnihilatorDimensionBounds
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  HasRankOneApolarAnnihilatorDimensionBound B p u ∧
    HasRankTwoApolarAnnihilatorDimensionBound B p u ∧
      HasRankThreeApolarAnnihilatorDimensionBound B p u

def HasRankTwoThreeApolarAnnihilatorDimensionBounds
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  HasRankTwoApolarAnnihilatorDimensionBound B p u ∧
    HasRankThreeApolarAnnihilatorDimensionBound B p u

def HasRankTwoApolarHilbertFirstBound
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
    4 - Module.finrank ℝ (linearAnnihilator B p u) ≤ 2

def HasRankTwoApolarEssentialQuotientBound
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
    Module.finrank ℝ (linSubmodule ⧸ linearAnnihilator B p u) ≤ 2

def HasRankTwoApolarQuotientGrowthData
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
    ∃ h3 : ℕ,
      Module.finrank ℝ (linSubmodule ⧸ linearAnnihilator B p u) = h3 ∧
        h3 ≤ Module.finrank ℝ
          (quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u))

def HasRankTwoApolarGorensteinSymmetryData
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
    ∃ h3 : ℕ,
      Module.finrank ℝ (linSubmodule ⧸ linearAnnihilator B p u) = h3

def HasRankTwoApolarMacaulayGrowthBound
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
    ∀ h3 : ℕ,
      Module.finrank ℝ (linSubmodule ⧸ linearAnnihilator B p u) = h3 →
        h3 ≤ Module.finrank ℝ
          (quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u))

def HasRankTwoApolarMacaulayGrowthData
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
    ∃ h1 h2 h3 : ℕ,
      h1 = 4 - Module.finrank ℝ (linearAnnihilator B p u) ∧
        h2 = 2 ∧
          h1 = h3 ∧
            h3 ≤ h2

def HasRankThreeApolarHilbertFirstBound
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
    4 - Module.finrank ℝ (linearAnnihilator B p u) ≤ 3

def HasRankThreeApolarEssentialQuotientBound
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
    Module.finrank ℝ (linSubmodule ⧸ linearAnnihilator B p u) ≤ 3

def HasLowRankApolarEssentialQuotientBounds
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  HasRankTwoApolarEssentialQuotientBound B p u ∧
    HasRankThreeApolarEssentialQuotientBound B p u

def HasLowRankApolarEssentialQuotientTheorem
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  ∀ k : ℕ,
    k ≤ 3 →
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = k →
        Module.finrank ℝ (linSubmodule ⧸ linearAnnihilator B p u) ≤ k

def HasRankThreeApolarMacaulayObstruction
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
    Module.finrank ℝ (linearAnnihilator B p u) = 0 →
      ∃ b : ℕ, 1 ≤ b ∧ b ≤ 3 ∧ 4 - b ≤ 3 - b

def HasRankThreeApolarExactSequenceData
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
    Module.finrank ℝ (linearAnnihilator B p u) = 0 →
      ∃ b q2 q3 : ℕ,
        1 ≤ b ∧ b ≤ 3 ∧
          q2 = 3 - b ∧
            q3 = 4 - b ∧
              q3 ≤ q2

def HasRankThreeApolarBadBranchExactSequenceData
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
    Module.finrank ℝ (linSubmodule ⧸ linearAnnihilator B p u) = 4 →
      ∃ b q2 q3 : ℕ,
        1 ≤ b ∧ b ≤ 3 ∧
          q2 = 3 - b ∧
            q3 = 4 - b ∧
              q3 ≤ q2

def HasRankThreeApolarBadBranchExactSequenceShape
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
    Module.finrank ℝ (linSubmodule ⧸ linearAnnihilator B p u) = 4 →
      ∃ b q2 q3 : ℕ,
        1 ≤ b ∧ b ≤ 3 ∧
          q2 = 3 - b ∧
            q3 = 4 - b

def HasRankThreeApolarBadBranchMacaulayBound
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
    Module.finrank ℝ (linSubmodule ⧸ linearAnnihilator B p u) = 4 →
      ∀ b q2 q3 : ℕ,
        1 ≤ b →
          b ≤ 3 →
            q2 = 3 - b →
              q3 = 4 - b →
                q3 ≤ q2

def HasRankThreeApolarBadBranchContradiction
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
    Module.finrank ℝ (linSubmodule ⧸ linearAnnihilator B p u) = 4 →
      False

def HasLowRankApolarHilbertData
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  HasRankTwoApolarMacaulayGrowthData B p u ∧
    HasRankThreeApolarExactSequenceData B p u

def HasLowRankApolarBlueprintHilbertData
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  HasRankTwoApolarQuotientGrowthData B p u ∧
    HasRankThreeApolarBadBranchExactSequenceData B p u

def HasLowRankApolarBlueprintLocalData
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  HasRankTwoApolarGorensteinSymmetryData B p u ∧
    HasRankTwoApolarMacaulayGrowthBound B p u ∧
      HasRankThreeApolarBadBranchExactSequenceShape B p u ∧
        HasRankThreeApolarBadBranchMacaulayBound B p u

def HasLowRankApolarQuotientLocalData
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  HasRankTwoApolarGorensteinSymmetryData B p u ∧
    HasRankTwoApolarMacaulayGrowthBound B p u ∧
      HasRankThreeApolarBadBranchContradiction B p u

def HasLowRankApolarQuotientCoreData
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  HasRankTwoApolarMacaulayGrowthBound B p u ∧
    HasRankThreeApolarBadBranchContradiction B p u

def HasGlobalLowRankApolarQuotientCoreData : Prop :=
  ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
    (_hu : IsAdmissiblePoint u),
    IsPositiveDefinite B →
      IsSOSQuartic p →
        IsSOCP B p u →
          HasLowRankApolarQuotientCoreData B p u

def HasGlobalLowRankApolarEssentialQuotientTheorem : Prop :=
  ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
    (_hu : IsAdmissiblePoint u),
    IsPositiveDefinite B →
      IsSOSQuartic p →
        IsSOCP B p u →
          HasLowRankApolarEssentialQuotientTheorem B p u

def HasRankTwoUniversalKernelEquationData
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
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
                      HasBinaryRestrictionKernelEquationCase B p u x y

def HasRankTwoUniversalCanonicalKernelData
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
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
                      HasBinaryCanonicalKernelData
                        (binaryRestrictionCoeffA B p u x)
                        (binaryRestrictionCoeffB B p u x y)
                        (binaryRestrictionCoeffC B p u x y)
                        (binaryRestrictionCoeffD B p u x y)
                        (binaryRestrictionCoeffE B p u y)

def HasRankTwoUniversalKernelBranchData
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
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
                      HasBinaryKernelBranchCertificate
                        (binaryRestrictionCoeffA B p u x)
                        (binaryRestrictionCoeffB B p u x y)
                        (binaryRestrictionCoeffC B p u x y)
                        (binaryRestrictionCoeffD B p u x y)
                        (binaryRestrictionCoeffE B p u y)

def HasRankTwoUniversalNormalizedHankelData
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
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
                      HasBinaryNormalizedKernelPosition
                        (binaryRestrictionCoeffA B p u x)
                        (binaryRestrictionCoeffB B p u x y)
                        (binaryRestrictionCoeffC B p u x y)
                        (binaryRestrictionCoeffD B p u x y)
                        (binaryRestrictionCoeffE B p u y) ∧
                      HasBinaryHankelNegativeValue
                        (binaryRestrictionCoeffA B p u x)
                        (binaryRestrictionCoeffB B p u x y)
                        (binaryRestrictionCoeffC B p u x y)
                        (binaryRestrictionCoeffD B p u x y)
                        (binaryRestrictionCoeffE B p u y) ∧
                      Module.finrank ℝ
                        (LinearMap.range
                          (binaryHankelLinearMap
                            (binaryRestrictionCoeffA B p u x)
                            (binaryRestrictionCoeffB B p u x y)
                            (binaryRestrictionCoeffC B p u x y)
                            (binaryRestrictionCoeffD B p u x y)
                            (binaryRestrictionCoeffE B p u y))) ≤ 2

def HasRankTwoUniversalNormalizedKernelPositionData
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
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
                      HasBinaryNormalizedKernelPosition
                        (binaryRestrictionCoeffA B p u x)
                        (binaryRestrictionCoeffB B p u x y)
                        (binaryRestrictionCoeffC B p u x y)
                        (binaryRestrictionCoeffD B p u x y)
                        (binaryRestrictionCoeffE B p u y)

def HasRankTwoUniversalHankelNegativeData
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
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
                      HasBinaryHankelNegativeValue
                        (binaryRestrictionCoeffA B p u x)
                        (binaryRestrictionCoeffB B p u x y)
                        (binaryRestrictionCoeffC B p u x y)
                        (binaryRestrictionCoeffD B p u x y)
                        (binaryRestrictionCoeffE B p u y)

theorem hasRankTwoUniversalHankelNegativeData_of_point
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u) :
    HasRankTwoUniversalHankelNegativeData B p u := by
  intro hrank A W x y hAann hAW hxW hyW hynot hx _hAdim hWdim
  exact rank_two_binaryHankelNegativeValue_of_annihilator_complement_pair
    (B := B) (p := p) (u := u) hu hp hfocp hrank
    hAann hAW hxW hyW hynot hx hWdim

def HasRankTwoUniversalBinaryHankelRankBound
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
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
                      Module.finrank ℝ
                        (LinearMap.range
                          (binaryHankelLinearMap
                            (binaryRestrictionCoeffA B p u x)
                            (binaryRestrictionCoeffB B p u x y)
                            (binaryRestrictionCoeffC B p u x y)
                            (binaryRestrictionCoeffD B p u x y)
                            (binaryRestrictionCoeffE B p u y))) ≤ 2

theorem universalBinaryHankelRankBound_of_catalecticantRankTwo
    {B : DotForm} {p : Poly} {u : RankSevenVec} :
    HasRankTwoUniversalBinaryHankelRankBound B p u := by
  intro hrank2 A W x y _hAann _hAW _hxW _hyW _hynot _hx _hAdim _hWdim
  have hle :=
    binaryHankelLinearMap_finrank_range_le_catalecticantMap_rank
      (B := B) (p := p) (u := u) x y
  rwa [hrank2] at hle

def HasRankCaseKernelEquationApolarData
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
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 3)

def HasLowRankApolarAnnihilatorMapTheorem
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  ∀ k : ℕ,
    k ≤ 3 →
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) ≤ k →
        Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ k

def HasRankCaseApolarSupportBounds
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
    HasLinearAnnihilatorCodimAtMost B p u 1) ∧
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
    HasLinearAnnihilatorCodimAtMost B p u 2) ∧
  (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
    HasLinearAnnihilatorCodimAtMost B p u 3)

def HasLowRankApolarSupportTheorem
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  ∀ k : ℕ,
    k ≤ 3 →
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) ≤ k →
        HasLinearAnnihilatorCodimAtMost B p u k

def HasGlobalLowRankApolarAnnihilatorMapTheorem : Prop :=
  ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
    (_hu : IsAdmissiblePoint u),
    IsPositiveDefinite B →
      IsSOSQuartic p →
        IsSOCP B p u →
          HasLowRankApolarAnnihilatorMapTheorem B p u

def HasGlobalLowRankApolarSupportTheorem : Prop :=
  ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
    (_hu : IsAdmissiblePoint u),
    IsPositiveDefinite B →
      IsSOSQuartic p →
        IsSOCP B p u →
          HasLowRankApolarSupportTheorem B p u

def HasGlobalRankCaseAnnihilatorMapBounds : Prop :=
  ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
    (_hu : IsAdmissiblePoint u),
    IsPositiveDefinite B →
      IsSOSQuartic p →
        IsSOCP B p u →
          HasRankCaseAnnihilatorMapBounds B p u

def HasGlobalRankCaseApolarSupportBounds : Prop :=
  ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
    (_hu : IsAdmissiblePoint u),
    IsPositiveDefinite B →
      IsSOSQuartic p →
        IsSOCP B p u →
          HasRankCaseApolarSupportBounds B p u

def HasGlobalRankTwoThreeApolarAnnihilatorMapBounds : Prop :=
  ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
    (_hu : IsAdmissiblePoint u),
    IsPositiveDefinite B →
      IsSOSQuartic p →
        IsSOCP B p u →
          HasRankTwoApolarAnnihilatorMapBound B p u ∧
            HasRankThreeApolarAnnihilatorMapBound B p u

def HasGlobalRankTwoThreeApolarSupportBounds : Prop :=
  ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
    (_hu : IsAdmissiblePoint u),
    IsPositiveDefinite B →
      IsSOSQuartic p →
        IsSOCP B p u →
          (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
            HasLinearAnnihilatorCodimAtMost B p u 2) ∧
          (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
            HasLinearAnnihilatorCodimAtMost B p u 3)

def HasGlobalRankTwoThreeApolarEssentialQuotientBounds : Prop :=
  ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
    (_hu : IsAdmissiblePoint u),
    IsPositiveDefinite B →
      IsSOSQuartic p →
        IsSOCP B p u →
          HasRankTwoApolarEssentialQuotientBound B p u ∧
            HasRankThreeApolarEssentialQuotientBound B p u

def HasGlobalRankTwoApolarEssentialQuotientBound : Prop :=
  ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
    (_hu : IsAdmissiblePoint u),
    IsPositiveDefinite B →
      IsSOSQuartic p →
        IsSOCP B p u →
          HasRankTwoApolarEssentialQuotientBound B p u

def HasGlobalRankThreeApolarEssentialQuotientBound : Prop :=
  ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
    (_hu : IsAdmissiblePoint u),
    IsPositiveDefinite B →
      IsSOSQuartic p →
        IsSOCP B p u →
          HasRankThreeApolarEssentialQuotientBound B p u

def HasGlobalRankTwoApolarMacaulayGrowthBound : Prop :=
  ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
    (_hu : IsAdmissiblePoint u),
    IsPositiveDefinite B →
      IsSOSQuartic p →
        IsSOCP B p u →
          HasRankTwoApolarMacaulayGrowthBound B p u

def HasGlobalRankThreeApolarBadBranchContradiction : Prop :=
  ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
    (_hu : IsAdmissiblePoint u),
    IsPositiveDefinite B →
      IsSOSQuartic p →
        IsSOCP B p u →
          HasRankThreeApolarBadBranchContradiction B p u

def HasGlobalRankTwoApolarHilbertFirstBound : Prop :=
  ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
    (_hu : IsAdmissiblePoint u),
    IsPositiveDefinite B →
      IsSOSQuartic p →
        IsSOCP B p u →
          HasRankTwoApolarHilbertFirstBound B p u

def HasGlobalRankThreeApolarHilbertFirstBound : Prop :=
  ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
    (_hu : IsAdmissiblePoint u),
    IsPositiveDefinite B →
      IsSOSQuartic p →
        IsSOCP B p u →
          HasRankThreeApolarHilbertFirstBound B p u

def HasGlobalRankTwoThreeApolarHilbertFirstBounds : Prop :=
  HasGlobalRankTwoApolarHilbertFirstBound ∧
    HasGlobalRankThreeApolarHilbertFirstBound

def HasGlobalRankThreeApolarBadBranchExactSequenceShape : Prop :=
  ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
    (_hu : IsAdmissiblePoint u),
    IsPositiveDefinite B →
      IsSOSQuartic p →
        IsSOCP B p u →
          HasRankThreeApolarBadBranchExactSequenceShape B p u

def HasGlobalRankThreeApolarBadBranchMacaulayBound : Prop :=
  ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
    (_hu : IsAdmissiblePoint u),
    IsPositiveDefinite B →
      IsSOSQuartic p →
        IsSOCP B p u →
          HasRankThreeApolarBadBranchMacaulayBound B p u

def HasLowRankApolarSupportDecomposition
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  ∀ k : ℕ,
    k ≤ 3 →
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) ≤ k →
        ∃ A W : Submodule ℝ linSubmodule,
          A ≤ linearAnnihilator B p u ∧
            IsCompl A W ∧
              Module.finrank ℝ W ≤ k ∧
                4 - k ≤ Module.finrank ℝ A

def HasLowRankApolarProductKernelDecomposition
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  ∀ k : ℕ,
    k ≤ 3 →
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) ≤ k →
        ∃ A W : Submodule ℝ linSubmodule,
          linProductSubmodule A ⊤ ≤ LinearMap.ker (catalecticantMap B p u) ∧
            IsCompl A W ∧
              Module.finrank ℝ W ≤ k ∧
                4 - k ≤ Module.finrank ℝ A

def HasRankTwoNegativeSquareData
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
    ∀ (A W : Submodule ℝ linSubmodule),
      A ≤ linearAnnihilator B p u →
        IsCompl A W →
          Module.finrank ℝ A = 2 →
            Module.finrank ℝ W = 2 →
              ∃ x : linSubmodule,
                x ∈ W ∧
                  (x : Poly) ≠ 0 ∧
                    B ((linProduct x x : quadSubmodule).1^2) (residual p u) < 0

def HasRankTwoExistentialBinaryFormData
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
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
                          (binaryRestrictionCoeffE B p u y)

def HasRankTwoExistentialKernelEquationData
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
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
                        HasBinaryRestrictionKernelEquationCase B p u x y

def HasRankTwoExistentialKernelBranchData
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
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
                        HasBinaryKernelBranchCertificate
                          (binaryRestrictionCoeffA B p u x)
                          (binaryRestrictionCoeffB B p u x y)
                          (binaryRestrictionCoeffC B p u x y)
                          (binaryRestrictionCoeffD B p u x y)
                          (binaryRestrictionCoeffE B p u y)

def HasRankTwoExistentialCanonicalKernelData
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
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
                        HasBinaryCanonicalKernelData
                          (binaryRestrictionCoeffA B p u x)
                          (binaryRestrictionCoeffB B p u x y)
                          (binaryRestrictionCoeffC B p u x y)
                          (binaryRestrictionCoeffD B p u x y)
                          (binaryRestrictionCoeffE B p u y)

def HasRankTwoExistentialScalarHankelData
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
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
                        HasBinaryRankTwoNormalizedKernelClassification
                          (binaryRestrictionCoeffA B p u x)
                          (binaryRestrictionCoeffB B p u x y)
                          (binaryRestrictionCoeffC B p u x y)
                          (binaryRestrictionCoeffD B p u x y)
                          (binaryRestrictionCoeffE B p u y) ∧
                        HasBinaryHankelNegativeValue
                          (binaryRestrictionCoeffA B p u x)
                          (binaryRestrictionCoeffB B p u x y)
                          (binaryRestrictionCoeffC B p u x y)
                          (binaryRestrictionCoeffD B p u x y)
                          (binaryRestrictionCoeffE B p u y) ∧
                        Module.finrank ℝ
                          (LinearMap.range
                            (binaryHankelLinearMap
                              (binaryRestrictionCoeffA B p u x)
                              (binaryRestrictionCoeffB B p u x y)
                              (binaryRestrictionCoeffC B p u x y)
                              (binaryRestrictionCoeffD B p u x y)
                              (binaryRestrictionCoeffE B p u y))) ≤ 2

def HasUniversalBinaryRankTwoNormalizedKernelClassification : Prop :=
  ∀ a b c d e : ℝ,
    HasBinaryRankTwoNormalizedKernelClassification a b c d e

def HasUniversalBinaryRankTwoNegativePureSquareTheorem : Prop :=
  ∀ a b c d e : ℝ,
    HasBinaryHankelNegativeValue a b c d e →
      Module.finrank ℝ (LinearMap.range (binaryHankelLinearMap a b c d e)) ≤ 2 →
        ∃ X Y : ℝ, binaryQuarticEval a b c d e X Y < 0

theorem hasUniversalBinaryRankTwoNegativePureSquareTheorem_of_classification
    (hclass : HasUniversalBinaryRankTwoNormalizedKernelClassification) :
    HasUniversalBinaryRankTwoNegativePureSquareTheorem := by
  intro a b c d e hneg hrank
  exact binaryQuarticEval_exists_negative_of_rankTwoNormalizedKernelClassification
    (hclass a b c d e) hneg hrank

theorem hasUniversalBinaryRankTwoNegativePureSquareTheorem_direct :
    HasUniversalBinaryRankTwoNegativePureSquareTheorem := by
  intro a b c d e hneg hrank
  exact binaryQuarticEval_exists_negative_of_finrank_range_le_two hneg hrank

def HasRankTwoExistentialScalarHankelFacts
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
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
                        HasBinaryHankelNegativeValue
                          (binaryRestrictionCoeffA B p u x)
                          (binaryRestrictionCoeffB B p u x y)
                          (binaryRestrictionCoeffC B p u x y)
                          (binaryRestrictionCoeffD B p u x y)
                          (binaryRestrictionCoeffE B p u y) ∧
                        Module.finrank ℝ
                          (LinearMap.range
                            (binaryHankelLinearMap
                              (binaryRestrictionCoeffA B p u x)
                              (binaryRestrictionCoeffB B p u x y)
                              (binaryRestrictionCoeffC B p u x y)
                              (binaryRestrictionCoeffD B p u x y)
                              (binaryRestrictionCoeffE B p u y))) ≤ 2

def HasRankTwoExistentialNormalizedHankelData
    (B : DotForm) (p : Poly) (u : RankSevenVec) : Prop :=
  Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
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
                        HasBinaryNormalizedKernelPosition
                          (binaryRestrictionCoeffA B p u x)
                          (binaryRestrictionCoeffB B p u x y)
                          (binaryRestrictionCoeffC B p u x y)
                          (binaryRestrictionCoeffD B p u x y)
                          (binaryRestrictionCoeffE B p u y) ∧
                        HasBinaryHankelNegativeValue
                          (binaryRestrictionCoeffA B p u x)
                          (binaryRestrictionCoeffB B p u x y)
                          (binaryRestrictionCoeffC B p u x y)
                          (binaryRestrictionCoeffD B p u x y)
                          (binaryRestrictionCoeffE B p u y) ∧
                        Module.finrank ℝ
                          (LinearMap.range
                            (binaryHankelLinearMap
                              (binaryRestrictionCoeffA B p u x)
                              (binaryRestrictionCoeffB B p u x y)
                              (binaryRestrictionCoeffC B p u x y)
                              (binaryRestrictionCoeffD B p u x y)
                              (binaryRestrictionCoeffE B p u y))) ≤ 2

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

theorem hasRankCaseApolarComponentData_of_combined_productLI_and_universalKernelBranchData
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
    (hbranches : HasRankTwoUniversalKernelBranchData B p u)
    (hann3 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
        Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) ≤ 3)
    (hneg3 :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
        ∃ (W : Submodule ℝ linSubmodule) (q : quadSubmodule),
          q ∈ linProductSubmodule W W ∧
            B (q.1^2) (residual p u) < 0) :
    HasRankCaseApolarComponentData B p u hu :=
  hasRankCaseApolarComponentData_of_combined_productLI_component_obligations
    (B := B) (p := p) (u := u) (hu := hu)
    hann1 hprodLI1 hneg1 hann2
    (fun hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim =>
      binaryRestriction_kernelEquationCase_of_kernelBranchCertificate
        (hbranches hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim))
    hprodLI2 hann3 hneg3

theorem hasRankCaseProductIndependenceGeometryData_of_productIndependenceApolarData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hdata : HasRankCaseProductIndependenceApolarData B p u hu) :
    HasRankCaseProductIndependenceGeometryData B p u hu := by
  rcases hdata with ⟨hdata1, hdata2, hdata3⟩
  constructor
  · intro hrank1
    exact hdata1 hrank1
  constructor
  · intro hrank2
    exact ⟨(hdata2 hrank2).1, (hdata2 hrank2).2.2⟩
  · intro hrank3
    exact hdata3 hrank3

theorem hasRankCaseProductIndependenceGeometryData_of_annihilatorMapBounds
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u)
    (hbounds : HasRankCaseAnnihilatorMapBounds B p u) :
    HasRankCaseProductIndependenceGeometryData B p u hu := by
  rcases hbounds with ⟨hann1, hann2, hann3⟩
  constructor
  · intro hrank1
    refine ⟨hann1 hrank1, ?_, ?_⟩
    · intro A W x _hAann hAW hxW hx hAdim hWdim
      exact exists_rank_one_combined_product_independence
        hAW hxW hx hAdim hWdim
    · intro A W x hAann hAW hxW hx _hAdim hWdim
      exact rank_one_binaryRestrictionCoeffA_neg_of_annihilator_complement
        (B := B) (p := p) (u := u) hu hp hfocp hrank1
        hAann hAW hxW hx hWdim
  constructor
  · intro hrank2
    refine ⟨hann2 hrank2, ?_⟩
    intro A W x y z _hAann hAW hxW hyW hynot hx hAdim hWdim hzspan hz
    exact exists_rank_two_combined_product_independence
      hAW hxW hyW hynot hx hAdim hWdim hzspan hz
  · intro hrank3
    refine ⟨hann3 hrank3, ?_⟩
    rcases exists_negative_sos_summand_of_catalecticantMap_rank_eq_three
        (B := B) hu hp hfocp hrank3 with
      ⟨q, hq, hqneg⟩
    let qQuad : quadSubmodule := ⟨q, hq⟩
    rcases exists_rank_three_catalecticantKernel_decomposition_of_annihilatorMap_range
        (B := B) (p := p) (u := u) (hann3 hrank3) qQuad with
      ⟨W, qW, qK, hqdecomp, hqW, hqK⟩
    exact ⟨W, qW, hqW,
      residualEval_sq_lt_of_eq_add_mem_ker_catalecticantMap
        (B := B) (p := p) (u := u) hqdecomp hqK hqneg⟩

theorem hasRankCaseApolarComponentData_of_productIndependenceGeometryData_and_universalKernelBranchData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hgeom : HasRankCaseProductIndependenceGeometryData B p u hu)
    (hbranches : HasRankTwoUniversalKernelBranchData B p u) :
    HasRankCaseApolarComponentData B p u hu := by
  rcases hgeom with ⟨hdata1, hdata2, hdata3⟩
  exact hasRankCaseApolarComponentData_of_combined_productLI_and_universalKernelBranchData
    (B := B) (p := p) (u := u) (hu := hu)
    (fun hrank1 => (hdata1 hrank1).1)
    (fun hrank1 => (hdata1 hrank1).2.1)
    (fun hrank1 => (hdata1 hrank1).2.2)
    (fun hrank2 => (hdata2 hrank2).1)
    (fun hrank2 => (hdata2 hrank2).2)
    hbranches
    (fun hrank3 => (hdata3 hrank3).1)
    (fun hrank3 => (hdata3 hrank3).2)

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

theorem hasRankCaseNegativeSquareApolarData_of_existentialBinaryFormData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hdata : HasRankCaseExistentialBinaryFormData B p u hu) :
    HasRankCaseNegativeSquareApolarData B p u hu := by
  rcases hdata with ⟨hdata1, hdata2, hdata3⟩
  constructor
  · intro hrank1
    exact hdata1 hrank1
  constructor
  · intro hrank2
    refine ⟨(hdata2 hrank2).1, ?_⟩
    intro A W hAann hAW hAdim hWdim
    have hWpos : 0 < Module.finrank ℝ W := by omega
    rcases exists_mem_ne_zero_of_finrank_pos (K := ℝ) (V := linSubmodule)
        (s := W) hWpos with
      ⟨x, hxW, hxne⟩
    have hx : (x : Poly) ≠ 0 := by
      intro hzero
      exact hxne (Subtype.ext hzero)
    rcases (hdata2 hrank2).2 A W x hAann hAW hxW hx hAdim hWdim with
      ⟨y, hyW, hynot, hform⟩
    rcases exists_negative_pure_square_of_binaryLowRankNormalForm
        (B := B) (p := p) (u := u)
        (x := x) (y := y) hform
        (binaryRestriction_eval_eq B p u x y) with
      ⟨z, hzspan, hneg⟩
    have hzW : z ∈ W := by
      have hspan : Submodule.span ℝ ({x, y} : Set linSubmodule) = W :=
        span_rank_two_support_pair_eq hx hxW hyW hynot hWdim
      rwa [hspan] at hzspan
    have hz : (z : Poly) ≠ 0 := by
      intro hzero
      have hval_zero :
          B ((linProduct z z : quadSubmodule).1^2) (residual p u) = 0 := by
        simp [linProduct, hzero]
      linarith
    exact ⟨z, hzW, hz, hneg⟩
  · intro hrank3
    exact hdata3 hrank3

theorem hasRankCaseNegativeSquareApolarData_of_annihilatorBounds_and_rankTwo
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hbounds : HasRankCaseAnnihilatorMapBounds B p u)
    (hneg2 : HasRankTwoNegativeSquareData B p u) :
    HasRankCaseNegativeSquareApolarData B p u hu := by
  rcases hbounds with ⟨hbound1, hbound2, hbound3⟩
  constructor
  · intro hrank1
    exact hbound1 hrank1
  constructor
  · intro hrank2
    exact ⟨hbound2 hrank2, hneg2 hrank2⟩
  · intro hrank3
    exact hbound3 hrank3

theorem hasRankCaseAnnihilatorMapBounds_of_apolarSupportBounds
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupport : HasRankCaseApolarSupportBounds B p u) :
    HasRankCaseAnnihilatorMapBounds B p u := by
  rcases hsupport with ⟨hsupport1, hsupport2, hsupport3⟩
  constructor
  · intro hrank1
    exact annihilatorMap_range_le_one_of_hasLinearAnnihilatorCodimAtMost
      (B := B) (p := p) (u := u) (hsupport1 hrank1)
  constructor
  · intro hrank2
    exact annihilatorMap_range_le_two_of_hasLinearAnnihilatorCodimAtMost
      (B := B) (p := p) (u := u) (hsupport2 hrank2)
  · intro hrank3
    exact annihilatorMap_range_le_three_of_hasLinearAnnihilatorCodimAtMost
      (B := B) (p := p) (u := u) (hsupport3 hrank3)

theorem hasRankCaseAnnihilatorMapBounds_of_splitAnnihilatorMapBounds
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hbound1 : HasRankOneApolarAnnihilatorMapBound B p u)
    (hbound2 : HasRankTwoApolarAnnihilatorMapBound B p u)
    (hbound3 : HasRankThreeApolarAnnihilatorMapBound B p u) :
    HasRankCaseAnnihilatorMapBounds B p u := by
  constructor
  · exact hbound1
  constructor
  · exact hbound2
  · exact hbound3

theorem rankOneApolarAnnihilatorMapBound_of_rankCaseAnnihilatorMapBounds
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hbounds : HasRankCaseAnnihilatorMapBounds B p u) :
    HasRankOneApolarAnnihilatorMapBound B p u :=
  hbounds.1

theorem rankTwoApolarAnnihilatorMapBound_of_rankCaseAnnihilatorMapBounds
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hbounds : HasRankCaseAnnihilatorMapBounds B p u) :
    HasRankTwoApolarAnnihilatorMapBound B p u :=
  hbounds.2.1

theorem rankThreeApolarAnnihilatorMapBound_of_rankCaseAnnihilatorMapBounds
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hbounds : HasRankCaseAnnihilatorMapBounds B p u) :
    HasRankThreeApolarAnnihilatorMapBound B p u :=
  hbounds.2.2

theorem rankOneApolarAnnihilatorMapBound_direct
    {B : DotForm} {p : Poly} {u : RankSevenVec} :
    HasRankOneApolarAnnihilatorMapBound B p u := by
  intro hrank1
  exact finrank_range_linearAnnihilatorMap_le_one_of_catalecticantMap_rank_one
    (B := B) (p := p) (u := u) hrank1

theorem rankOneApolarSupportBound_direct
    {B : DotForm} {p : Poly} {u : RankSevenVec} :
    Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
      HasLinearAnnihilatorCodimAtMost B p u 1 := by
  intro hrank1
  exact hasLinearAnnihilatorCodimAtMost_one_of_annihilatorMap_range
    (B := B) (p := p) (u := u)
    (rankOneApolarAnnihilatorMapBound_direct (B := B) (p := p) (u := u) hrank1)

theorem rankOneApolarAnnihilatorMapBound_of_rankOneDimensionBound
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdim : HasRankOneApolarAnnihilatorDimensionBound B p u) :
    HasRankOneApolarAnnihilatorMapBound B p u := by
  intro hrank1
  have hsum :=
    finrank_range_linearAnnihilatorMap_add_finrank_linearAnnihilator B p u
  have hdim1 := hdim hrank1
  omega

theorem rankTwoApolarAnnihilatorMapBound_of_rankTwoDimensionBound
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdim : HasRankTwoApolarAnnihilatorDimensionBound B p u) :
    HasRankTwoApolarAnnihilatorMapBound B p u := by
  intro hrank2
  have hsum :=
    finrank_range_linearAnnihilatorMap_add_finrank_linearAnnihilator B p u
  have hdim2 := hdim hrank2
  omega

theorem rankThreeApolarAnnihilatorMapBound_of_rankThreeDimensionBound
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdim : HasRankThreeApolarAnnihilatorDimensionBound B p u) :
    HasRankThreeApolarAnnihilatorMapBound B p u := by
  intro hrank3
  have hsum :=
    finrank_range_linearAnnihilatorMap_add_finrank_linearAnnihilator B p u
  have hdim3 := hdim hrank3
  omega

theorem hasRankCaseAnnihilatorMapBounds_of_rankTwo_rankThree
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hbound2 : HasRankTwoApolarAnnihilatorMapBound B p u)
    (hbound3 : HasRankThreeApolarAnnihilatorMapBound B p u) :
    HasRankCaseAnnihilatorMapBounds B p u :=
  hasRankCaseAnnihilatorMapBounds_of_splitAnnihilatorMapBounds
    (B := B) (p := p) (u := u)
    rankOneApolarAnnihilatorMapBound_direct hbound2 hbound3

theorem hasRankCaseAnnihilatorMapBounds_of_rankTwo_rankThreeDimensionBounds
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdims : HasRankTwoThreeApolarAnnihilatorDimensionBounds B p u) :
    HasRankCaseAnnihilatorMapBounds B p u :=
  hasRankCaseAnnihilatorMapBounds_of_rankTwo_rankThree
    (rankTwoApolarAnnihilatorMapBound_of_rankTwoDimensionBound hdims.1)
    (rankThreeApolarAnnihilatorMapBound_of_rankThreeDimensionBound hdims.2)

theorem rankOneDimensionBound_of_rankOneApolarAnnihilatorMapBound
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hbound : HasRankOneApolarAnnihilatorMapBound B p u) :
    HasRankOneApolarAnnihilatorDimensionBound B p u := by
  intro hrank1
  have hsum :=
    finrank_range_linearAnnihilatorMap_add_finrank_linearAnnihilator B p u
  have hbound1 := hbound hrank1
  omega

theorem rankTwoDimensionBound_of_rankTwoApolarAnnihilatorMapBound
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hbound : HasRankTwoApolarAnnihilatorMapBound B p u) :
    HasRankTwoApolarAnnihilatorDimensionBound B p u := by
  intro hrank2
  have hsum :=
    finrank_range_linearAnnihilatorMap_add_finrank_linearAnnihilator B p u
  have hbound2 := hbound hrank2
  omega

theorem rankThreeDimensionBound_of_rankThreeApolarAnnihilatorMapBound
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hbound : HasRankThreeApolarAnnihilatorMapBound B p u) :
    HasRankThreeApolarAnnihilatorDimensionBound B p u := by
  intro hrank3
  have hsum :=
    finrank_range_linearAnnihilatorMap_add_finrank_linearAnnihilator B p u
  have hbound3 := hbound hrank3
  omega

theorem rankTwoDimensionBound_of_rankTwoHilbertFirstBound
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hhilbert : HasRankTwoApolarHilbertFirstBound B p u) :
    HasRankTwoApolarAnnihilatorDimensionBound B p u := by
  intro hrank2
  have hann_le : Module.finrank ℝ (linearAnnihilator B p u) ≤ 4 := by
    have hle :
        linearAnnihilator B p u ≤ (⊤ : Submodule ℝ linSubmodule) := le_top
    have hmono := Submodule.finrank_mono hle
    have htop :
        Module.finrank ℝ (⊤ : Submodule ℝ linSubmodule) = 4 := by
      rw [finrank_top]
      exact finrank_linSubmodule_eq_four
    omega
  have hh := hhilbert hrank2
  omega

theorem rankTwoHilbertFirstBound_of_rankTwoEssentialQuotientBound
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hquot : HasRankTwoApolarEssentialQuotientBound B p u) :
    HasRankTwoApolarHilbertFirstBound B p u := by
  intro hrank2
  rw [← finrank_quotient_linearAnnihilator_eq_sub]
  exact hquot hrank2

theorem rankTwoEssentialQuotientBound_of_rankTwoHilbertFirstBound
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hhilbert : HasRankTwoApolarHilbertFirstBound B p u) :
    HasRankTwoApolarEssentialQuotientBound B p u := by
  intro hrank2
  rw [finrank_quotient_linearAnnihilator_eq_sub]
  exact hhilbert hrank2

theorem rankTwoHilbertFirstBound_iff_rankTwoEssentialQuotientBound
    {B : DotForm} {p : Poly} {u : RankSevenVec} :
    HasRankTwoApolarHilbertFirstBound B p u ↔
      HasRankTwoApolarEssentialQuotientBound B p u :=
  ⟨rankTwoEssentialQuotientBound_of_rankTwoHilbertFirstBound,
    rankTwoHilbertFirstBound_of_rankTwoEssentialQuotientBound⟩

theorem rankTwoEssentialQuotientBound_of_rankTwoApolarAnnihilatorMapBound
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hbound : HasRankTwoApolarAnnihilatorMapBound B p u) :
    HasRankTwoApolarEssentialQuotientBound B p u := by
  intro hrank2
  rw [finrank_quotient_linearAnnihilator_eq_range_linearAnnihilatorMap]
  exact hbound hrank2

theorem rankTwoApolarAnnihilatorMapBound_of_rankTwoEssentialQuotientBound
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hquot : HasRankTwoApolarEssentialQuotientBound B p u) :
    HasRankTwoApolarAnnihilatorMapBound B p u := by
  intro hrank2
  rw [← finrank_quotient_linearAnnihilator_eq_range_linearAnnihilatorMap]
  exact hquot hrank2

theorem rankTwoEssentialQuotientBound_iff_rankTwoApolarAnnihilatorMapBound
    {B : DotForm} {p : Poly} {u : RankSevenVec} :
    HasRankTwoApolarEssentialQuotientBound B p u ↔
      HasRankTwoApolarAnnihilatorMapBound B p u :=
  ⟨rankTwoApolarAnnihilatorMapBound_of_rankTwoEssentialQuotientBound,
    rankTwoEssentialQuotientBound_of_rankTwoApolarAnnihilatorMapBound⟩

theorem rankTwoEssentialQuotientBound_of_rankTwoSupportBound
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupport :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
        HasLinearAnnihilatorCodimAtMost B p u 2) :
    HasRankTwoApolarEssentialQuotientBound B p u :=
  rankTwoEssentialQuotientBound_of_rankTwoApolarAnnihilatorMapBound
    (by
      intro hrank2
      exact annihilatorMap_range_le_two_of_hasLinearAnnihilatorCodimAtMost
        (B := B) (p := p) (u := u) (hsupport hrank2))

theorem rankTwoSupportBound_of_rankTwoEssentialQuotientBound
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hquot : HasRankTwoApolarEssentialQuotientBound B p u) :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
        HasLinearAnnihilatorCodimAtMost B p u 2 := by
  intro hrank2
  exact hasLinearAnnihilatorCodimAtMost_two_of_annihilatorMap_range
    (B := B) (p := p) (u := u)
    (rankTwoApolarAnnihilatorMapBound_of_rankTwoEssentialQuotientBound
      hquot hrank2)

theorem rankTwoSupportBound_iff_rankTwoEssentialQuotientBound
    {B : DotForm} {p : Poly} {u : RankSevenVec} :
    (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
        HasLinearAnnihilatorCodimAtMost B p u 2) ↔
      HasRankTwoApolarEssentialQuotientBound B p u :=
  ⟨rankTwoEssentialQuotientBound_of_rankTwoSupportBound,
    rankTwoSupportBound_of_rankTwoEssentialQuotientBound⟩

theorem rankTwoEssentialQuotientBound_of_rankTwoQuotientGrowthData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasRankTwoApolarQuotientGrowthData B p u) :
    HasRankTwoApolarEssentialQuotientBound B p u := by
  intro hrank2
  rcases hdata hrank2 with ⟨h3, hsymm, hgrowth⟩
  have hdegree_two :
      Module.finrank ℝ
      (quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u)) = 2 :=
    finrank_quotient_ker_catalecticantMap_eq_two_of_rank_two hrank2
  omega

theorem rankTwoApolarGorensteinSymmetryData_direct
    (B : DotForm) (p : Poly) (u : RankSevenVec) :
    HasRankTwoApolarGorensteinSymmetryData B p u := by
  intro _hrank2
  exact ⟨Module.finrank ℝ (linSubmodule ⧸ linearAnnihilator B p u), rfl⟩

theorem rankTwoQuotientGrowthData_of_symmetry_and_macaulayGrowth
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsymm : HasRankTwoApolarGorensteinSymmetryData B p u)
    (hgrowth : HasRankTwoApolarMacaulayGrowthBound B p u) :
    HasRankTwoApolarQuotientGrowthData B p u := by
  intro hrank2
  rcases hsymm hrank2 with ⟨h3, hh3⟩
  exact ⟨h3, hh3, hgrowth hrank2 h3 hh3⟩

theorem rankTwoEssentialQuotientBound_of_symmetry_and_macaulayGrowth
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsymm : HasRankTwoApolarGorensteinSymmetryData B p u)
    (hgrowth : HasRankTwoApolarMacaulayGrowthBound B p u) :
    HasRankTwoApolarEssentialQuotientBound B p u :=
  rankTwoEssentialQuotientBound_of_rankTwoQuotientGrowthData
    (rankTwoQuotientGrowthData_of_symmetry_and_macaulayGrowth hsymm hgrowth)

theorem rankTwoEssentialQuotientBound_of_macaulayGrowth
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hgrowth : HasRankTwoApolarMacaulayGrowthBound B p u) :
    HasRankTwoApolarEssentialQuotientBound B p u :=
  rankTwoEssentialQuotientBound_of_symmetry_and_macaulayGrowth
    (rankTwoApolarGorensteinSymmetryData_direct B p u) hgrowth

theorem rankTwoMacaulayGrowthBound_of_rankTwoEssentialQuotientBound
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hquot : HasRankTwoApolarEssentialQuotientBound B p u) :
    HasRankTwoApolarMacaulayGrowthBound B p u := by
  intro hrank2 h3 hh3
  have hdegree_two :
      Module.finrank ℝ
          (quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u)) = 2 :=
    finrank_quotient_ker_catalecticantMap_eq_two_of_rank_two hrank2
  have hquot_le := hquot hrank2
  omega

theorem rankTwoMacaulayGrowthBound_iff_rankTwoEssentialQuotientBound
    {B : DotForm} {p : Poly} {u : RankSevenVec} :
    HasRankTwoApolarMacaulayGrowthBound B p u ↔
      HasRankTwoApolarEssentialQuotientBound B p u :=
  ⟨rankTwoEssentialQuotientBound_of_macaulayGrowth,
    rankTwoMacaulayGrowthBound_of_rankTwoEssentialQuotientBound⟩

theorem rankTwoMacaulayGrowthData_of_rankTwoEssentialQuotientBound
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hquot : HasRankTwoApolarEssentialQuotientBound B p u) :
    HasRankTwoApolarMacaulayGrowthData B p u := by
  intro hrank2
  refine ⟨Module.finrank ℝ (linSubmodule ⧸ linearAnnihilator B p u), 2,
    Module.finrank ℝ (linSubmodule ⧸ linearAnnihilator B p u), ?_, rfl, rfl, ?_⟩
  · rw [finrank_quotient_linearAnnihilator_eq_sub]
  · exact hquot hrank2

theorem rankTwoHilbertFirstBound_of_rankTwoMacaulayGrowthData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasRankTwoApolarMacaulayGrowthData B p u) :
    HasRankTwoApolarHilbertFirstBound B p u := by
  intro hrank2
  rcases hdata hrank2 with ⟨h1, h2, h3, hh1, hh2, hsymm, hgrowth⟩
  have hh1_le : h1 ≤ 2 :=
    rankTwoMacaulayGrowth_forces_hilbertFirst_le_two hh2 hsymm hgrowth
  omega

theorem rankTwoDimensionBound_of_rankTwoMacaulayGrowthData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasRankTwoApolarMacaulayGrowthData B p u) :
    HasRankTwoApolarAnnihilatorDimensionBound B p u :=
  rankTwoDimensionBound_of_rankTwoHilbertFirstBound
    (rankTwoHilbertFirstBound_of_rankTwoMacaulayGrowthData hdata)

theorem rankTwoDimensionBound_of_rankTwoEssentialQuotientBound
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hquot : HasRankTwoApolarEssentialQuotientBound B p u) :
    HasRankTwoApolarAnnihilatorDimensionBound B p u :=
  rankTwoDimensionBound_of_rankTwoHilbertFirstBound
    (rankTwoHilbertFirstBound_of_rankTwoEssentialQuotientBound hquot)

theorem rankThreeDimensionBound_of_rankThreeHilbertFirstBound
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hhilbert : HasRankThreeApolarHilbertFirstBound B p u) :
    HasRankThreeApolarAnnihilatorDimensionBound B p u := by
  intro hrank3
  have hann_le : Module.finrank ℝ (linearAnnihilator B p u) ≤ 4 := by
    have hle :
        linearAnnihilator B p u ≤ (⊤ : Submodule ℝ linSubmodule) := le_top
    have hmono := Submodule.finrank_mono hle
    have htop :
        Module.finrank ℝ (⊤ : Submodule ℝ linSubmodule) = 4 := by
      rw [finrank_top]
      exact finrank_linSubmodule_eq_four
    omega
  have hh := hhilbert hrank3
  omega

theorem rankThreeHilbertFirstBound_of_rankThreeEssentialQuotientBound
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hquot : HasRankThreeApolarEssentialQuotientBound B p u) :
    HasRankThreeApolarHilbertFirstBound B p u := by
  intro hrank3
  rw [← finrank_quotient_linearAnnihilator_eq_sub]
  exact hquot hrank3

theorem rankThreeEssentialQuotientBound_of_rankThreeHilbertFirstBound
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hhilbert : HasRankThreeApolarHilbertFirstBound B p u) :
    HasRankThreeApolarEssentialQuotientBound B p u := by
  intro hrank3
  rw [finrank_quotient_linearAnnihilator_eq_sub]
  exact hhilbert hrank3

theorem rankThreeHilbertFirstBound_iff_rankThreeEssentialQuotientBound
    {B : DotForm} {p : Poly} {u : RankSevenVec} :
    HasRankThreeApolarHilbertFirstBound B p u ↔
      HasRankThreeApolarEssentialQuotientBound B p u :=
  ⟨rankThreeEssentialQuotientBound_of_rankThreeHilbertFirstBound,
    rankThreeHilbertFirstBound_of_rankThreeEssentialQuotientBound⟩

theorem rankThreeEssentialQuotientBound_of_rankThreeApolarAnnihilatorMapBound
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hbound : HasRankThreeApolarAnnihilatorMapBound B p u) :
    HasRankThreeApolarEssentialQuotientBound B p u := by
  intro hrank3
  rw [finrank_quotient_linearAnnihilator_eq_range_linearAnnihilatorMap]
  exact hbound hrank3

theorem rankThreeApolarAnnihilatorMapBound_of_rankThreeEssentialQuotientBound
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hquot : HasRankThreeApolarEssentialQuotientBound B p u) :
    HasRankThreeApolarAnnihilatorMapBound B p u := by
  intro hrank3
  rw [← finrank_quotient_linearAnnihilator_eq_range_linearAnnihilatorMap]
  exact hquot hrank3

theorem rankThreeEssentialQuotientBound_iff_rankThreeApolarAnnihilatorMapBound
    {B : DotForm} {p : Poly} {u : RankSevenVec} :
    HasRankThreeApolarEssentialQuotientBound B p u ↔
      HasRankThreeApolarAnnihilatorMapBound B p u :=
  ⟨rankThreeApolarAnnihilatorMapBound_of_rankThreeEssentialQuotientBound,
    rankThreeEssentialQuotientBound_of_rankThreeApolarAnnihilatorMapBound⟩

theorem rankThreeEssentialQuotientBound_of_rankThreeSupportBound
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupport :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
        HasLinearAnnihilatorCodimAtMost B p u 3) :
    HasRankThreeApolarEssentialQuotientBound B p u :=
  rankThreeEssentialQuotientBound_of_rankThreeApolarAnnihilatorMapBound
    (by
      intro hrank3
      exact annihilatorMap_range_le_three_of_hasLinearAnnihilatorCodimAtMost
        (B := B) (p := p) (u := u) (hsupport hrank3))

theorem rankThreeSupportBound_of_rankThreeEssentialQuotientBound
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hquot : HasRankThreeApolarEssentialQuotientBound B p u) :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
        HasLinearAnnihilatorCodimAtMost B p u 3 := by
  intro hrank3
  exact hasLinearAnnihilatorCodimAtMost_three_of_annihilatorMap_range
    (B := B) (p := p) (u := u)
    (rankThreeApolarAnnihilatorMapBound_of_rankThreeEssentialQuotientBound
      hquot hrank3)

theorem rankThreeSupportBound_iff_rankThreeEssentialQuotientBound
    {B : DotForm} {p : Poly} {u : RankSevenVec} :
    (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
        HasLinearAnnihilatorCodimAtMost B p u 3) ↔
      HasRankThreeApolarEssentialQuotientBound B p u :=
  ⟨rankThreeEssentialQuotientBound_of_rankThreeSupportBound,
    rankThreeSupportBound_of_rankThreeEssentialQuotientBound⟩

theorem rankThreeDimensionBound_of_rankThreeEssentialQuotientBound
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hquot : HasRankThreeApolarEssentialQuotientBound B p u) :
    HasRankThreeApolarAnnihilatorDimensionBound B p u :=
  rankThreeDimensionBound_of_rankThreeHilbertFirstBound
    (rankThreeHilbertFirstBound_of_rankThreeEssentialQuotientBound hquot)

theorem rankThreeBadBranchContradiction_of_rankThreeEssentialQuotientBound
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hquot : HasRankThreeApolarEssentialQuotientBound B p u) :
    HasRankThreeApolarBadBranchContradiction B p u := by
  intro hrank3 hbad
  have hle := hquot hrank3
  omega

theorem rankThreeEssentialQuotientBound_of_badBranchContradiction
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hbadContra : HasRankThreeApolarBadBranchContradiction B p u) :
    HasRankThreeApolarEssentialQuotientBound B p u := by
  intro hrank3
  by_contra hnot
  have hle4 := finrank_quotient_linearAnnihilator_le_four B p u
  have hbad :
      Module.finrank ℝ (linSubmodule ⧸ linearAnnihilator B p u) = 4 := by
    omega
  exact hbadContra hrank3 hbad

theorem rankThreeEssentialQuotientBound_iff_badBranchContradiction
    {B : DotForm} {p : Poly} {u : RankSevenVec} :
    HasRankThreeApolarEssentialQuotientBound B p u ↔
      HasRankThreeApolarBadBranchContradiction B p u :=
  ⟨rankThreeBadBranchContradiction_of_rankThreeEssentialQuotientBound,
    rankThreeEssentialQuotientBound_of_badBranchContradiction⟩

theorem rankThreeBadBranchMacaulayBound_of_badBranchContradiction
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hbadContra : HasRankThreeApolarBadBranchContradiction B p u) :
    HasRankThreeApolarBadBranchMacaulayBound B p u := by
  intro hrank3 hbad b q2 q3 _hbpos _hbtop _hq2 _hq3
  exfalso
  exact hbadContra hrank3 hbad

theorem rankThreeBadBranchExactSequenceShape_of_badBranchContradiction
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hbadContra : HasRankThreeApolarBadBranchContradiction B p u) :
    HasRankThreeApolarBadBranchExactSequenceShape B p u := by
  intro hrank3 hbad
  exact False.elim (hbadContra hrank3 hbad)

theorem rankThreeBadBranchExactSequenceShape_direct
    (B : DotForm) (p : Poly) (u : RankSevenVec) :
    HasRankThreeApolarBadBranchExactSequenceShape B p u := by
  intro _hrank3 _hbad
  exact ⟨1, 2, 3, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem rankThreeBadBranchContradiction_of_shape_and_macaulayBound
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hshape : HasRankThreeApolarBadBranchExactSequenceShape B p u)
    (hmac : HasRankThreeApolarBadBranchMacaulayBound B p u) :
    HasRankThreeApolarBadBranchContradiction B p u := by
  intro hrank3 hbad
  rcases hshape hrank3 hbad with ⟨b, q2, q3, hbpos, hbtop, hq2, hq3⟩
  exact rankThreeExactSequenceNumericalContradiction
    hbpos hbtop hq2 hq3 (hmac hrank3 hbad b q2 q3 hbpos hbtop hq2 hq3)

theorem rankThreeEssentialQuotientBound_of_shape_and_macaulayBound
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hshape : HasRankThreeApolarBadBranchExactSequenceShape B p u)
    (hmac : HasRankThreeApolarBadBranchMacaulayBound B p u) :
    HasRankThreeApolarEssentialQuotientBound B p u := by
  exact rankThreeEssentialQuotientBound_of_badBranchContradiction
    (rankThreeBadBranchContradiction_of_shape_and_macaulayBound hshape hmac)

theorem rankThreeBadBranchContradiction_iff_shape_and_macaulayBound
    {B : DotForm} {p : Poly} {u : RankSevenVec} :
    HasRankThreeApolarBadBranchContradiction B p u ↔
      HasRankThreeApolarBadBranchExactSequenceShape B p u ∧
        HasRankThreeApolarBadBranchMacaulayBound B p u :=
  ⟨fun hbad =>
      ⟨rankThreeBadBranchExactSequenceShape_of_badBranchContradiction hbad,
        rankThreeBadBranchMacaulayBound_of_badBranchContradiction hbad⟩,
    fun hdata =>
      rankThreeBadBranchContradiction_of_shape_and_macaulayBound
        hdata.1 hdata.2⟩

theorem rankThreeExactSequenceData_of_rankThreeEssentialQuotientBound
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hquot : HasRankThreeApolarEssentialQuotientBound B p u) :
    HasRankThreeApolarExactSequenceData B p u := by
  intro hrank3 hzero
  have hquot_le := hquot hrank3
  have hquot_eq :
      Module.finrank ℝ (linSubmodule ⧸ linearAnnihilator B p u) = 4 := by
    rw [finrank_quotient_linearAnnihilator_eq_sub, hzero]
  omega

theorem rankThreeExactSequenceData_of_rankThreeBadBranchExactSequenceData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasRankThreeApolarBadBranchExactSequenceData B p u) :
    HasRankThreeApolarExactSequenceData B p u := by
  intro hrank3 hzero
  exact hdata hrank3
    (finrank_quotient_linearAnnihilator_eq_four_of_finrank_linearAnnihilator_eq_zero hzero)

theorem rankThreeBadBranchExactSequenceData_of_rankThreeExactSequenceData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasRankThreeApolarExactSequenceData B p u) :
    HasRankThreeApolarBadBranchExactSequenceData B p u := by
  intro hrank3 hquot
  exact hdata hrank3
    (finrank_linearAnnihilator_eq_zero_of_finrank_quotient_linearAnnihilator_eq_four hquot)

theorem rankThreeBadBranchExactSequenceData_of_shape_and_macaulayBound
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hshape : HasRankThreeApolarBadBranchExactSequenceShape B p u)
    (hmac : HasRankThreeApolarBadBranchMacaulayBound B p u) :
    HasRankThreeApolarBadBranchExactSequenceData B p u := by
  intro hrank3 hbad
  rcases hshape hrank3 hbad with ⟨b, q2, q3, hbpos, hbtop, hq2, hq3⟩
  exact ⟨b, q2, q3, hbpos, hbtop, hq2, hq3,
    hmac hrank3 hbad b q2 q3 hbpos hbtop hq2 hq3⟩

theorem rankThreeHilbertFirstBound_of_rankThreeMacaulayObstruction
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hobstruction : HasRankThreeApolarMacaulayObstruction B p u) :
    HasRankThreeApolarHilbertFirstBound B p u := by
  intro hrank3
  by_contra hhilbert
  have hann_le : Module.finrank ℝ (linearAnnihilator B p u) ≤ 4 := by
    have hle :
        linearAnnihilator B p u ≤ (⊤ : Submodule ℝ linSubmodule) := le_top
    have hmono := Submodule.finrank_mono hle
    have htop :
        Module.finrank ℝ (⊤ : Submodule ℝ linSubmodule) = 4 := by
      rw [finrank_top]
      exact finrank_linSubmodule_eq_four
    omega
  have hzero : Module.finrank ℝ (linearAnnihilator B p u) = 0 := by
    omega
  rcases hobstruction hrank3 hzero with ⟨b, hbpos, hbtop, hineq⟩
  exact rankThreeMacaulayNumericalContradiction hbpos hbtop hineq

theorem rankThreeMacaulayObstruction_of_rankThreeExactSequenceData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasRankThreeApolarExactSequenceData B p u) :
    HasRankThreeApolarMacaulayObstruction B p u := by
  intro hrank3 hzero
  rcases hdata hrank3 hzero with
    ⟨b, q2, q3, hbpos, hbtop, hq2, hq3, hineq⟩
  refine ⟨b, hbpos, hbtop, ?_⟩
  exfalso
  exact rankThreeExactSequenceNumericalContradiction
    hbpos hbtop hq2 hq3 hineq

theorem rankThreeHilbertFirstBound_of_rankThreeExactSequenceData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasRankThreeApolarExactSequenceData B p u) :
    HasRankThreeApolarHilbertFirstBound B p u :=
  rankThreeHilbertFirstBound_of_rankThreeMacaulayObstruction
    (rankThreeMacaulayObstruction_of_rankThreeExactSequenceData hdata)

theorem rankThreeDimensionBound_of_rankThreeMacaulayObstruction
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hobstruction : HasRankThreeApolarMacaulayObstruction B p u) :
    HasRankThreeApolarAnnihilatorDimensionBound B p u :=
  rankThreeDimensionBound_of_rankThreeHilbertFirstBound
    (rankThreeHilbertFirstBound_of_rankThreeMacaulayObstruction hobstruction)

theorem rankThreeDimensionBound_of_rankThreeExactSequenceData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasRankThreeApolarExactSequenceData B p u) :
    HasRankThreeApolarAnnihilatorDimensionBound B p u :=
  rankThreeDimensionBound_of_rankThreeMacaulayObstruction
    (rankThreeMacaulayObstruction_of_rankThreeExactSequenceData hdata)

theorem hasRankCaseAnnihilatorMapBounds_of_rankTwoDimensionBound_rankThreeMacaulayObstruction
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdim2 : HasRankTwoApolarAnnihilatorDimensionBound B p u)
    (hobstruction : HasRankThreeApolarMacaulayObstruction B p u) :
    HasRankCaseAnnihilatorMapBounds B p u :=
  hasRankCaseAnnihilatorMapBounds_of_rankTwo_rankThreeDimensionBounds
    ⟨hdim2, rankThreeDimensionBound_of_rankThreeMacaulayObstruction hobstruction⟩

theorem hasRankCaseAnnihilatorMapBounds_of_rankTwoHilbertFirstBound_rankThreeMacaulayObstruction
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hhilbert2 : HasRankTwoApolarHilbertFirstBound B p u)
    (hobstruction : HasRankThreeApolarMacaulayObstruction B p u) :
    HasRankCaseAnnihilatorMapBounds B p u :=
  hasRankCaseAnnihilatorMapBounds_of_rankTwoDimensionBound_rankThreeMacaulayObstruction
    (rankTwoDimensionBound_of_rankTwoHilbertFirstBound hhilbert2)
    hobstruction

theorem hasRankCaseAnnihilatorMapBounds_of_rankTwo_rankThreeEssentialQuotientBounds
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hquot2 : HasRankTwoApolarEssentialQuotientBound B p u)
    (hquot3 : HasRankThreeApolarEssentialQuotientBound B p u) :
    HasRankCaseAnnihilatorMapBounds B p u :=
  hasRankCaseAnnihilatorMapBounds_of_rankTwo_rankThreeDimensionBounds
    ⟨rankTwoDimensionBound_of_rankTwoEssentialQuotientBound hquot2,
      rankThreeDimensionBound_of_rankThreeEssentialQuotientBound hquot3⟩

theorem lowRankApolarHilbertData_of_rankTwo_rankThreeEssentialQuotientBounds
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hquot2 : HasRankTwoApolarEssentialQuotientBound B p u)
    (hquot3 : HasRankThreeApolarEssentialQuotientBound B p u) :
    HasLowRankApolarHilbertData B p u :=
  ⟨rankTwoMacaulayGrowthData_of_rankTwoEssentialQuotientBound hquot2,
    rankThreeExactSequenceData_of_rankThreeEssentialQuotientBound hquot3⟩

theorem lowRankApolarHilbertData_of_lowRankApolarEssentialQuotientBounds
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hquot : HasLowRankApolarEssentialQuotientBounds B p u) :
    HasLowRankApolarHilbertData B p u :=
  lowRankApolarHilbertData_of_rankTwo_rankThreeEssentialQuotientBounds
    hquot.1 hquot.2

theorem lowRankApolarEssentialQuotientBounds_of_lowRankApolarHilbertData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasLowRankApolarHilbertData B p u) :
    HasLowRankApolarEssentialQuotientBounds B p u :=
  ⟨rankTwoEssentialQuotientBound_of_rankTwoHilbertFirstBound
      (rankTwoHilbertFirstBound_of_rankTwoMacaulayGrowthData hdata.1),
    rankThreeEssentialQuotientBound_of_rankThreeHilbertFirstBound
      (rankThreeHilbertFirstBound_of_rankThreeExactSequenceData hdata.2)⟩

theorem lowRankApolarHilbertData_iff_lowRankApolarEssentialQuotientBounds
    {B : DotForm} {p : Poly} {u : RankSevenVec} :
    HasLowRankApolarHilbertData B p u ↔
      HasLowRankApolarEssentialQuotientBounds B p u :=
  ⟨lowRankApolarEssentialQuotientBounds_of_lowRankApolarHilbertData,
    lowRankApolarHilbertData_of_lowRankApolarEssentialQuotientBounds⟩

theorem lowRankApolarEssentialQuotientBounds_of_theorem
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hquot : HasLowRankApolarEssentialQuotientTheorem B p u) :
    HasLowRankApolarEssentialQuotientBounds B p u :=
  ⟨hquot 2 (by norm_num), hquot 3 (by norm_num)⟩

theorem lowRankApolarHilbertData_of_rankTwo_rankThreeApolarAnnihilatorMapBounds
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hbound2 : HasRankTwoApolarAnnihilatorMapBound B p u)
    (hbound3 : HasRankThreeApolarAnnihilatorMapBound B p u) :
    HasLowRankApolarHilbertData B p u :=
  lowRankApolarHilbertData_of_rankTwo_rankThreeEssentialQuotientBounds
    (rankTwoEssentialQuotientBound_of_rankTwoApolarAnnihilatorMapBound hbound2)
    (rankThreeEssentialQuotientBound_of_rankThreeApolarAnnihilatorMapBound hbound3)

theorem lowRankApolarHilbertData_of_rankTwoQuotientGrowthData_rankThreeExactSequenceData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata2 : HasRankTwoApolarQuotientGrowthData B p u)
    (hdata3 : HasRankThreeApolarExactSequenceData B p u) :
    HasLowRankApolarHilbertData B p u :=
  lowRankApolarHilbertData_of_rankTwo_rankThreeEssentialQuotientBounds
    (rankTwoEssentialQuotientBound_of_rankTwoQuotientGrowthData hdata2)
    (rankThreeEssentialQuotientBound_of_rankThreeHilbertFirstBound
      (rankThreeHilbertFirstBound_of_rankThreeExactSequenceData hdata3))

theorem lowRankApolarHilbertData_of_rankTwoQuotientGrowthData_rankThreeBadBranchExactSequenceData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata2 : HasRankTwoApolarQuotientGrowthData B p u)
    (hdata3 : HasRankThreeApolarBadBranchExactSequenceData B p u) :
    HasLowRankApolarHilbertData B p u :=
  lowRankApolarHilbertData_of_rankTwoQuotientGrowthData_rankThreeExactSequenceData
    hdata2
    (rankThreeExactSequenceData_of_rankThreeBadBranchExactSequenceData hdata3)

theorem lowRankApolarHilbertData_of_rankTwoSymmetryAndGrowth_rankThreeBadBranchExactSequenceData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsymm2 : HasRankTwoApolarGorensteinSymmetryData B p u)
    (hgrowth2 : HasRankTwoApolarMacaulayGrowthBound B p u)
    (hdata3 : HasRankThreeApolarBadBranchExactSequenceData B p u) :
    HasLowRankApolarHilbertData B p u :=
  lowRankApolarHilbertData_of_rankTwoQuotientGrowthData_rankThreeBadBranchExactSequenceData
    (rankTwoQuotientGrowthData_of_symmetry_and_macaulayGrowth hsymm2 hgrowth2)
    hdata3

theorem lowRankApolarHilbertData_of_rankTwoSymmetryAndGrowth_rankThreeShapeAndMacaulayBound
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsymm2 : HasRankTwoApolarGorensteinSymmetryData B p u)
    (hgrowth2 : HasRankTwoApolarMacaulayGrowthBound B p u)
    (hshape3 : HasRankThreeApolarBadBranchExactSequenceShape B p u)
    (hmac3 : HasRankThreeApolarBadBranchMacaulayBound B p u) :
    HasLowRankApolarHilbertData B p u :=
  lowRankApolarHilbertData_of_rankTwoSymmetryAndGrowth_rankThreeBadBranchExactSequenceData
    hsymm2 hgrowth2
    (rankThreeBadBranchExactSequenceData_of_shape_and_macaulayBound hshape3 hmac3)

theorem lowRankApolarEssentialQuotientBounds_of_rankTwoSymmetryAndGrowth_rankThreeShapeAndMacaulayBound
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsymm2 : HasRankTwoApolarGorensteinSymmetryData B p u)
    (hgrowth2 : HasRankTwoApolarMacaulayGrowthBound B p u)
    (hshape3 : HasRankThreeApolarBadBranchExactSequenceShape B p u)
    (hmac3 : HasRankThreeApolarBadBranchMacaulayBound B p u) :
    HasLowRankApolarEssentialQuotientBounds B p u :=
  ⟨rankTwoEssentialQuotientBound_of_symmetry_and_macaulayGrowth hsymm2 hgrowth2,
    rankThreeEssentialQuotientBound_of_shape_and_macaulayBound hshape3 hmac3⟩

theorem lowRankApolarEssentialQuotientBounds_of_rankTwoSymmetryAndGrowth_rankThreeBadBranchContradiction
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsymm2 : HasRankTwoApolarGorensteinSymmetryData B p u)
    (hgrowth2 : HasRankTwoApolarMacaulayGrowthBound B p u)
    (hbad3 : HasRankThreeApolarBadBranchContradiction B p u) :
    HasLowRankApolarEssentialQuotientBounds B p u :=
  ⟨rankTwoEssentialQuotientBound_of_symmetry_and_macaulayGrowth hsymm2 hgrowth2,
    rankThreeEssentialQuotientBound_of_badBranchContradiction hbad3⟩

theorem lowRankApolarEssentialQuotientBounds_of_lowRankApolarQuotientLocalData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasLowRankApolarQuotientLocalData B p u) :
    HasLowRankApolarEssentialQuotientBounds B p u :=
  lowRankApolarEssentialQuotientBounds_of_rankTwoSymmetryAndGrowth_rankThreeBadBranchContradiction
    hdata.1 hdata.2.1 hdata.2.2

theorem lowRankApolarQuotientLocalData_of_coreData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasLowRankApolarQuotientCoreData B p u) :
    HasLowRankApolarQuotientLocalData B p u :=
  ⟨rankTwoApolarGorensteinSymmetryData_direct B p u, hdata.1, hdata.2⟩

theorem lowRankApolarEssentialQuotientBounds_of_coreData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasLowRankApolarQuotientCoreData B p u) :
    HasLowRankApolarEssentialQuotientBounds B p u :=
  lowRankApolarEssentialQuotientBounds_of_lowRankApolarQuotientLocalData
    (lowRankApolarQuotientLocalData_of_coreData hdata)

theorem lowRankApolarQuotientCoreData_of_essentialQuotientBounds
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hquot : HasLowRankApolarEssentialQuotientBounds B p u) :
    HasLowRankApolarQuotientCoreData B p u :=
  ⟨rankTwoMacaulayGrowthBound_of_rankTwoEssentialQuotientBound hquot.1,
    rankThreeBadBranchContradiction_of_rankThreeEssentialQuotientBound hquot.2⟩

theorem lowRankApolarQuotientCoreData_iff_essentialQuotientBounds
    {B : DotForm} {p : Poly} {u : RankSevenVec} :
    HasLowRankApolarQuotientCoreData B p u ↔
      HasLowRankApolarEssentialQuotientBounds B p u :=
  ⟨lowRankApolarEssentialQuotientBounds_of_coreData,
    lowRankApolarQuotientCoreData_of_essentialQuotientBounds⟩

theorem lowRankApolarEssentialQuotientBounds_of_lowRankApolarBlueprintLocalData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasLowRankApolarBlueprintLocalData B p u) :
    HasLowRankApolarEssentialQuotientBounds B p u :=
  lowRankApolarEssentialQuotientBounds_of_rankTwoSymmetryAndGrowth_rankThreeShapeAndMacaulayBound
    hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2

theorem lowRankApolarHilbertData_of_lowRankApolarBlueprintLocalData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasLowRankApolarBlueprintLocalData B p u) :
    HasLowRankApolarHilbertData B p u :=
  lowRankApolarHilbertData_of_rankTwoSymmetryAndGrowth_rankThreeShapeAndMacaulayBound
    hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2

theorem lowRankApolarBlueprintHilbertData_of_lowRankApolarBlueprintLocalData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasLowRankApolarBlueprintLocalData B p u) :
    HasLowRankApolarBlueprintHilbertData B p u :=
  ⟨rankTwoQuotientGrowthData_of_symmetry_and_macaulayGrowth hdata.1 hdata.2.1,
    rankThreeBadBranchExactSequenceData_of_shape_and_macaulayBound
      hdata.2.2.1 hdata.2.2.2⟩

theorem rankTwoGorensteinSymmetryData_of_rankTwoQuotientGrowthData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasRankTwoApolarQuotientGrowthData B p u) :
    HasRankTwoApolarGorensteinSymmetryData B p u := by
  intro hrank2
  rcases hdata hrank2 with ⟨h3, hsymm, _hgrowth⟩
  exact ⟨h3, hsymm⟩

theorem rankTwoMacaulayGrowthBound_of_rankTwoQuotientGrowthData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasRankTwoApolarQuotientGrowthData B p u) :
    HasRankTwoApolarMacaulayGrowthBound B p u := by
  intro hrank2 h3 hh3
  rcases hdata hrank2 with ⟨h3', hsymm', hgrowth'⟩
  omega

theorem rankThreeBadBranchExactSequenceShape_of_data
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasRankThreeApolarBadBranchExactSequenceData B p u) :
    HasRankThreeApolarBadBranchExactSequenceShape B p u := by
  intro hrank3 hbad
  rcases hdata hrank3 hbad with ⟨b, q2, q3, hbpos, hbtop, hq2, hq3, _hmac⟩
  exact ⟨b, q2, q3, hbpos, hbtop, hq2, hq3⟩

theorem rankThreeBadBranchMacaulayBound_of_data
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasRankThreeApolarBadBranchExactSequenceData B p u) :
    HasRankThreeApolarBadBranchMacaulayBound B p u := by
  intro hrank3 hbad b q2 q3 hbpos hbtop hq2 hq3
  rcases hdata hrank3 hbad with
    ⟨b', q2', q3', hbpos', hbtop', hq2', hq3', hmac'⟩
  exfalso
  exact rankThreeExactSequenceNumericalContradiction
    hbpos' hbtop' hq2' hq3' hmac'

theorem lowRankApolarBlueprintLocalData_of_lowRankApolarBlueprintHilbertData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasLowRankApolarBlueprintHilbertData B p u) :
    HasLowRankApolarBlueprintLocalData B p u :=
  ⟨rankTwoGorensteinSymmetryData_of_rankTwoQuotientGrowthData hdata.1,
    rankTwoMacaulayGrowthBound_of_rankTwoQuotientGrowthData hdata.1,
    rankThreeBadBranchExactSequenceShape_of_data hdata.2,
    rankThreeBadBranchMacaulayBound_of_data hdata.2⟩

theorem lowRankApolarBlueprintLocalData_iff_lowRankApolarBlueprintHilbertData
    {B : DotForm} {p : Poly} {u : RankSevenVec} :
    HasLowRankApolarBlueprintLocalData B p u ↔
      HasLowRankApolarBlueprintHilbertData B p u :=
  ⟨lowRankApolarBlueprintHilbertData_of_lowRankApolarBlueprintLocalData,
    lowRankApolarBlueprintLocalData_of_lowRankApolarBlueprintHilbertData⟩

theorem lowRankApolarHilbertData_of_lowRankApolarBlueprintHilbertData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasLowRankApolarBlueprintHilbertData B p u) :
    HasLowRankApolarHilbertData B p u :=
  lowRankApolarHilbertData_of_rankTwoQuotientGrowthData_rankThreeBadBranchExactSequenceData
    hdata.1 hdata.2

theorem hasRankCaseAnnihilatorMapBounds_of_rankTwoMacaulayGrowthData_rankThreeMacaulayObstruction
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata2 : HasRankTwoApolarMacaulayGrowthData B p u)
    (hobstruction : HasRankThreeApolarMacaulayObstruction B p u) :
    HasRankCaseAnnihilatorMapBounds B p u :=
  hasRankCaseAnnihilatorMapBounds_of_rankTwoHilbertFirstBound_rankThreeMacaulayObstruction
    (rankTwoHilbertFirstBound_of_rankTwoMacaulayGrowthData hdata2)
    hobstruction

theorem hasRankCaseAnnihilatorMapBounds_of_rankTwoMacaulayGrowthData_rankThreeExactSequenceData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata2 : HasRankTwoApolarMacaulayGrowthData B p u)
    (hdata3 : HasRankThreeApolarExactSequenceData B p u) :
    HasRankCaseAnnihilatorMapBounds B p u :=
  hasRankCaseAnnihilatorMapBounds_of_rankTwoMacaulayGrowthData_rankThreeMacaulayObstruction
    hdata2
    (rankThreeMacaulayObstruction_of_rankThreeExactSequenceData hdata3)

theorem hasRankCaseAnnihilatorMapBounds_of_lowRankApolarHilbertData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasLowRankApolarHilbertData B p u) :
    HasRankCaseAnnihilatorMapBounds B p u :=
  hasRankCaseAnnihilatorMapBounds_of_rankTwoMacaulayGrowthData_rankThreeExactSequenceData
    hdata.1 hdata.2

theorem hasRankCaseAnnihilatorMapBounds_of_dimensionBounds
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdims : HasRankCaseApolarAnnihilatorDimensionBounds B p u) :
    HasRankCaseAnnihilatorMapBounds B p u :=
  hasRankCaseAnnihilatorMapBounds_of_splitAnnihilatorMapBounds
    (rankOneApolarAnnihilatorMapBound_of_rankOneDimensionBound hdims.1)
    (rankTwoApolarAnnihilatorMapBound_of_rankTwoDimensionBound hdims.2.1)
    (rankThreeApolarAnnihilatorMapBound_of_rankThreeDimensionBound hdims.2.2)

theorem dimensionBounds_of_hasRankCaseAnnihilatorMapBounds
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hbounds : HasRankCaseAnnihilatorMapBounds B p u) :
    HasRankCaseApolarAnnihilatorDimensionBounds B p u :=
  ⟨rankOneDimensionBound_of_rankOneApolarAnnihilatorMapBound hbounds.1,
    rankTwoDimensionBound_of_rankTwoApolarAnnihilatorMapBound hbounds.2.1,
    rankThreeDimensionBound_of_rankThreeApolarAnnihilatorMapBound hbounds.2.2⟩

theorem rankOneDimensionBound_of_hasLinearAnnihilatorCodimAtMost
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupp : HasLinearAnnihilatorCodimAtMost B p u 1) :
    HasRankOneApolarAnnihilatorDimensionBound B p u := by
  intro _hrank1
  rcases hsupp with ⟨A, hAann, hAdim⟩
  have hAfin_le :
      Module.finrank ℝ A ≤ Module.finrank ℝ (linearAnnihilator B p u) :=
    Submodule.finrank_mono hAann
  omega

theorem rankTwoDimensionBound_of_hasLinearAnnihilatorCodimAtMost
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupp : HasLinearAnnihilatorCodimAtMost B p u 2) :
    HasRankTwoApolarAnnihilatorDimensionBound B p u := by
  intro _hrank2
  rcases hsupp with ⟨A, hAann, hAdim⟩
  have hAfin_le :
      Module.finrank ℝ A ≤ Module.finrank ℝ (linearAnnihilator B p u) :=
    Submodule.finrank_mono hAann
  omega

theorem rankThreeDimensionBound_of_hasLinearAnnihilatorCodimAtMost
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupp : HasLinearAnnihilatorCodimAtMost B p u 3) :
    HasRankThreeApolarAnnihilatorDimensionBound B p u := by
  intro _hrank3
  rcases hsupp with ⟨A, hAann, hAdim⟩
  have hAfin_le :
      Module.finrank ℝ A ≤ Module.finrank ℝ (linearAnnihilator B p u) :=
    Submodule.finrank_mono hAann
  omega

theorem hasRankCaseApolarAnnihilatorDimensionBounds_of_apolarSupportBounds
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupport : HasRankCaseApolarSupportBounds B p u) :
    HasRankCaseApolarAnnihilatorDimensionBounds B p u := by
  rcases hsupport with ⟨hsupp1, hsupp2, hsupp3⟩
  exact ⟨
    fun hrank1 =>
      rankOneDimensionBound_of_hasLinearAnnihilatorCodimAtMost
        (B := B) (p := p) (u := u) (hsupp1 hrank1) hrank1,
    fun hrank2 =>
      rankTwoDimensionBound_of_hasLinearAnnihilatorCodimAtMost
        (B := B) (p := p) (u := u) (hsupp2 hrank2) hrank2,
    fun hrank3 =>
      rankThreeDimensionBound_of_hasLinearAnnihilatorCodimAtMost
        (B := B) (p := p) (u := u) (hsupp3 hrank3) hrank3⟩

theorem hasRankCaseApolarSupportBounds_of_annihilatorDimensionBounds
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdims : HasRankCaseApolarAnnihilatorDimensionBounds B p u) :
    HasRankCaseApolarSupportBounds B p u := by
  rcases hdims with ⟨hdim1, hdim2, hdim3⟩
  constructor
  · intro hrank1
    exact ⟨linearAnnihilator B p u, le_rfl, hdim1 hrank1⟩
  constructor
  · intro hrank2
    exact ⟨linearAnnihilator B p u, le_rfl, hdim2 hrank2⟩
  · intro hrank3
    exact ⟨linearAnnihilator B p u, le_rfl, hdim3 hrank3⟩

theorem hasRankCaseApolarSupportBounds_of_annihilatorMapBounds
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hbounds : HasRankCaseAnnihilatorMapBounds B p u) :
    HasRankCaseApolarSupportBounds B p u :=
  hasRankCaseApolarSupportBounds_of_annihilatorDimensionBounds
    (dimensionBounds_of_hasRankCaseAnnihilatorMapBounds hbounds)

theorem finrank_range_linearAnnihilatorMap_eq_zero_of_catalecticantMap_rank_zero
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hrank :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 0) :
    Module.finrank ℝ (LinearMap.range (linearAnnihilatorMap B p u)) = 0 := by
  have hrange_bot : LinearMap.range (catalecticantMap B p u) = ⊥ :=
    (Submodule.finrank_eq_zero).mp hrank
  have hcat_zero : catalecticantMap B p u = 0 := by
    ext q r
    have hmem :
        catalecticantMap B p u q ∈
          LinearMap.range (catalecticantMap B p u) :=
      LinearMap.mem_range_self _ _
    have hbot :
        catalecticantMap B p u q ∈
          (⊥ : Submodule ℝ (Module.Dual ℝ quadSubmodule)) := by
      simpa [hrange_bot] using hmem
    have hqzero : catalecticantMap B p u q = 0 := by
      simpa using hbot
    simp [hqzero]
  have hlin_top : linearAnnihilator B p u = ⊤ := by
    ext a
    constructor
    · intro _ha
      exact Submodule.mem_top
    · intro _ha e
      rw [hcat_zero]
      simp
  have hlin_dim : Module.finrank ℝ (linearAnnihilator B p u) = 4 := by
    rw [hlin_top]
    rw [finrank_top]
    exact finrank_linSubmodule_eq_four
  have hsum :=
    finrank_range_linearAnnihilatorMap_add_finrank_linearAnnihilator B p u
  omega

theorem hasLinearAnnihilatorCodimAtMost_zero_of_catalecticantMap_rank_zero
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hrank :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 0) :
    HasLinearAnnihilatorCodimAtMost B p u 0 :=
  hasLinearAnnihilatorCodimAtMost_of_annihilatorMap_range
    (B := B) (p := p) (u := u) (k := 0) (by norm_num)
    (by
      rw [finrank_range_linearAnnihilatorMap_eq_zero_of_catalecticantMap_rank_zero
        (B := B) (p := p) (u := u) hrank])

theorem lowRankApolarEssentialQuotientTheorem_of_bounds
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hquot : HasLowRankApolarEssentialQuotientBounds B p u) :
    HasLowRankApolarEssentialQuotientTheorem B p u := by
  intro k hk hrank
  interval_cases k
  · rw [finrank_quotient_linearAnnihilator_eq_range_linearAnnihilatorMap]
    rw [finrank_range_linearAnnihilatorMap_eq_zero_of_catalecticantMap_rank_zero
      (B := B) (p := p) (u := u) hrank]
  · rw [finrank_quotient_linearAnnihilator_eq_range_linearAnnihilatorMap]
    exact rankOneApolarAnnihilatorMapBound_direct (B := B) (p := p) (u := u) hrank
  · exact hquot.1 hrank
  · exact hquot.2 hrank

theorem rankTwoQuotientGrowthData_of_lowRankApolarEssentialQuotientTheorem
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hquot : HasLowRankApolarEssentialQuotientTheorem B p u) :
    HasRankTwoApolarQuotientGrowthData B p u := by
  intro hrank2
  refine ⟨Module.finrank ℝ (linSubmodule ⧸ linearAnnihilator B p u), rfl, ?_⟩
  have hq := hquot 2 (by norm_num) hrank2
  have hdegree_two :
      Module.finrank ℝ
          (quadSubmodule ⧸ LinearMap.ker (catalecticantMap B p u)) = 2 :=
    finrank_quotient_ker_catalecticantMap_eq_two_of_rank_two hrank2
  omega

theorem rankThreeBadBranchExactSequenceData_of_lowRankApolarEssentialQuotientTheorem
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hquot : HasLowRankApolarEssentialQuotientTheorem B p u) :
    HasRankThreeApolarBadBranchExactSequenceData B p u := by
  intro hrank3 hbad
  have hq := hquot 3 (by norm_num) hrank3
  exfalso
  omega

theorem lowRankApolarBlueprintHilbertData_of_lowRankApolarEssentialQuotientTheorem
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hquot : HasLowRankApolarEssentialQuotientTheorem B p u) :
    HasLowRankApolarBlueprintHilbertData B p u :=
  ⟨rankTwoQuotientGrowthData_of_lowRankApolarEssentialQuotientTheorem hquot,
    rankThreeBadBranchExactSequenceData_of_lowRankApolarEssentialQuotientTheorem hquot⟩

theorem lowRankApolarEssentialQuotientTheorem_of_lowRankApolarBlueprintHilbertData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasLowRankApolarBlueprintHilbertData B p u) :
    HasLowRankApolarEssentialQuotientTheorem B p u :=
  lowRankApolarEssentialQuotientTheorem_of_bounds
    (lowRankApolarEssentialQuotientBounds_of_lowRankApolarHilbertData
      (lowRankApolarHilbertData_of_lowRankApolarBlueprintHilbertData hdata))

theorem lowRankApolarBlueprintHilbertData_iff_lowRankApolarEssentialQuotientTheorem
    {B : DotForm} {p : Poly} {u : RankSevenVec} :
    HasLowRankApolarBlueprintHilbertData B p u ↔
      HasLowRankApolarEssentialQuotientTheorem B p u :=
  ⟨lowRankApolarEssentialQuotientTheorem_of_lowRankApolarBlueprintHilbertData,
    lowRankApolarBlueprintHilbertData_of_lowRankApolarEssentialQuotientTheorem⟩

theorem lowRankApolarBlueprintLocalData_of_lowRankApolarEssentialQuotientTheorem
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hquot : HasLowRankApolarEssentialQuotientTheorem B p u) :
    HasLowRankApolarBlueprintLocalData B p u :=
  lowRankApolarBlueprintLocalData_of_lowRankApolarBlueprintHilbertData
    (lowRankApolarBlueprintHilbertData_of_lowRankApolarEssentialQuotientTheorem hquot)

theorem lowRankApolarEssentialQuotientTheorem_of_lowRankApolarBlueprintLocalData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasLowRankApolarBlueprintLocalData B p u) :
    HasLowRankApolarEssentialQuotientTheorem B p u :=
  lowRankApolarEssentialQuotientTheorem_of_bounds
    (lowRankApolarEssentialQuotientBounds_of_lowRankApolarBlueprintLocalData hdata)

theorem lowRankApolarBlueprintLocalData_iff_lowRankApolarEssentialQuotientTheorem
    {B : DotForm} {p : Poly} {u : RankSevenVec} :
    HasLowRankApolarBlueprintLocalData B p u ↔
      HasLowRankApolarEssentialQuotientTheorem B p u :=
  ⟨lowRankApolarEssentialQuotientTheorem_of_lowRankApolarBlueprintLocalData,
    lowRankApolarBlueprintLocalData_of_lowRankApolarEssentialQuotientTheorem⟩

theorem lowRankApolarEssentialQuotientTheorem_of_blueprintLocalComponents
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsymm2 : HasRankTwoApolarGorensteinSymmetryData B p u)
    (hgrowth2 : HasRankTwoApolarMacaulayGrowthBound B p u)
    (hshape3 : HasRankThreeApolarBadBranchExactSequenceShape B p u)
    (hmac3 : HasRankThreeApolarBadBranchMacaulayBound B p u) :
    HasLowRankApolarEssentialQuotientTheorem B p u :=
  lowRankApolarEssentialQuotientTheorem_of_bounds
    (lowRankApolarEssentialQuotientBounds_of_rankTwoSymmetryAndGrowth_rankThreeShapeAndMacaulayBound
      hsymm2 hgrowth2 hshape3 hmac3)

theorem lowRankApolarEssentialQuotientTheorem_of_lowRankApolarQuotientLocalData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasLowRankApolarQuotientLocalData B p u) :
    HasLowRankApolarEssentialQuotientTheorem B p u :=
  lowRankApolarEssentialQuotientTheorem_of_bounds
    (lowRankApolarEssentialQuotientBounds_of_lowRankApolarQuotientLocalData hdata)

theorem lowRankApolarEssentialQuotientTheorem_of_coreData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasLowRankApolarQuotientCoreData B p u) :
    HasLowRankApolarEssentialQuotientTheorem B p u :=
  lowRankApolarEssentialQuotientTheorem_of_lowRankApolarQuotientLocalData
    (lowRankApolarQuotientLocalData_of_coreData hdata)

theorem lowRankApolarQuotientCoreData_of_lowRankApolarEssentialQuotientTheorem
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hquot : HasLowRankApolarEssentialQuotientTheorem B p u) :
    HasLowRankApolarQuotientCoreData B p u := by
  have hdata2 :=
    rankTwoQuotientGrowthData_of_lowRankApolarEssentialQuotientTheorem hquot
  exact ⟨
    rankTwoMacaulayGrowthBound_of_rankTwoQuotientGrowthData hdata2,
    rankThreeBadBranchContradiction_of_rankThreeEssentialQuotientBound
      (lowRankApolarEssentialQuotientBounds_of_theorem hquot).2⟩

theorem lowRankApolarQuotientCoreData_iff_lowRankApolarEssentialQuotientTheorem
    {B : DotForm} {p : Poly} {u : RankSevenVec} :
    HasLowRankApolarQuotientCoreData B p u ↔
      HasLowRankApolarEssentialQuotientTheorem B p u :=
  ⟨lowRankApolarEssentialQuotientTheorem_of_coreData,
    lowRankApolarQuotientCoreData_of_lowRankApolarEssentialQuotientTheorem⟩

theorem lowRankApolarQuotientLocalData_of_lowRankApolarEssentialQuotientTheorem
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hquot : HasLowRankApolarEssentialQuotientTheorem B p u) :
    HasLowRankApolarQuotientLocalData B p u := by
  have hdata2 :=
    rankTwoQuotientGrowthData_of_lowRankApolarEssentialQuotientTheorem hquot
  exact ⟨
    rankTwoGorensteinSymmetryData_of_rankTwoQuotientGrowthData hdata2,
    rankTwoMacaulayGrowthBound_of_rankTwoQuotientGrowthData hdata2,
    rankThreeBadBranchContradiction_of_rankThreeEssentialQuotientBound
      (lowRankApolarEssentialQuotientBounds_of_theorem hquot).2⟩

theorem lowRankApolarQuotientLocalData_iff_lowRankApolarEssentialQuotientTheorem
    {B : DotForm} {p : Poly} {u : RankSevenVec} :
    HasLowRankApolarQuotientLocalData B p u ↔
      HasLowRankApolarEssentialQuotientTheorem B p u :=
  ⟨lowRankApolarEssentialQuotientTheorem_of_lowRankApolarQuotientLocalData,
    lowRankApolarQuotientLocalData_of_lowRankApolarEssentialQuotientTheorem⟩

theorem lowRankApolarEssentialQuotientTheorem_of_lowRankApolarAnnihilatorMapTheorem
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hann : HasLowRankApolarAnnihilatorMapTheorem B p u) :
    HasLowRankApolarEssentialQuotientTheorem B p u := by
  intro k hk hrank
  rw [finrank_quotient_linearAnnihilator_eq_range_linearAnnihilatorMap]
  exact hann k hk (by omega)

theorem hasLowRankApolarAnnihilatorMapTheorem_of_lowRankApolarEssentialQuotientTheorem
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hquot : HasLowRankApolarEssentialQuotientTheorem B p u) :
    HasLowRankApolarAnnihilatorMapTheorem B p u := by
  intro k hk hrank_le
  let n := Module.finrank ℝ (LinearMap.range (catalecticantMap B p u))
  have hn_le_three : n ≤ 3 := by omega
  have hquot_n := hquot n hn_le_three rfl
  rw [finrank_quotient_linearAnnihilator_eq_range_linearAnnihilatorMap] at hquot_n
  exact hquot_n.trans hrank_le

theorem hasLowRankApolarAnnihilatorMapTheorem_iff_lowRankApolarEssentialQuotientTheorem
    {B : DotForm} {p : Poly} {u : RankSevenVec} :
    HasLowRankApolarAnnihilatorMapTheorem B p u ↔
      HasLowRankApolarEssentialQuotientTheorem B p u :=
  ⟨lowRankApolarEssentialQuotientTheorem_of_lowRankApolarAnnihilatorMapTheorem,
    hasLowRankApolarAnnihilatorMapTheorem_of_lowRankApolarEssentialQuotientTheorem⟩

theorem hasLowRankApolarAnnihilatorMapTheorem_of_blueprintLocalComponents
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsymm2 : HasRankTwoApolarGorensteinSymmetryData B p u)
    (hgrowth2 : HasRankTwoApolarMacaulayGrowthBound B p u)
    (hshape3 : HasRankThreeApolarBadBranchExactSequenceShape B p u)
    (hmac3 : HasRankThreeApolarBadBranchMacaulayBound B p u) :
    HasLowRankApolarAnnihilatorMapTheorem B p u :=
  hasLowRankApolarAnnihilatorMapTheorem_of_lowRankApolarEssentialQuotientTheorem
    (lowRankApolarEssentialQuotientTheorem_of_blueprintLocalComponents
      hsymm2 hgrowth2 hshape3 hmac3)

theorem lowRankApolarEssentialQuotientTheorem_of_lowRankApolarSupportTheorem
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupport : HasLowRankApolarSupportTheorem B p u) :
    HasLowRankApolarEssentialQuotientTheorem B p u := by
  intro k hk hrank
  rcases hsupport k hk (by omega) with ⟨A, hAann, hAdim⟩
  rw [finrank_quotient_linearAnnihilator_eq_sub]
  have hAfin_le :
      Module.finrank ℝ A ≤ Module.finrank ℝ (linearAnnihilator B p u) :=
    Submodule.finrank_mono hAann
  omega

theorem hasLowRankApolarSupportTheorem_of_lowRankApolarEssentialQuotientTheorem
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hquot : HasLowRankApolarEssentialQuotientTheorem B p u) :
    HasLowRankApolarSupportTheorem B p u := by
  intro k hk hrank_le
  let n := Module.finrank ℝ (LinearMap.range (catalecticantMap B p u))
  have hn_le_three : n ≤ 3 := by omega
  have hquot_n := hquot n hn_le_three rfl
  rw [finrank_quotient_linearAnnihilator_eq_sub] at hquot_n
  refine ⟨linearAnnihilator B p u, le_rfl, ?_⟩
  omega

theorem hasLowRankApolarSupportTheorem_iff_lowRankApolarEssentialQuotientTheorem
    {B : DotForm} {p : Poly} {u : RankSevenVec} :
    HasLowRankApolarSupportTheorem B p u ↔
      HasLowRankApolarEssentialQuotientTheorem B p u :=
  ⟨lowRankApolarEssentialQuotientTheorem_of_lowRankApolarSupportTheorem,
    hasLowRankApolarSupportTheorem_of_lowRankApolarEssentialQuotientTheorem⟩

theorem hasLowRankApolarSupportTheorem_of_blueprintLocalComponents
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsymm2 : HasRankTwoApolarGorensteinSymmetryData B p u)
    (hgrowth2 : HasRankTwoApolarMacaulayGrowthBound B p u)
    (hshape3 : HasRankThreeApolarBadBranchExactSequenceShape B p u)
    (hmac3 : HasRankThreeApolarBadBranchMacaulayBound B p u) :
    HasLowRankApolarSupportTheorem B p u :=
  hasLowRankApolarSupportTheorem_of_lowRankApolarEssentialQuotientTheorem
    (lowRankApolarEssentialQuotientTheorem_of_blueprintLocalComponents
      hsymm2 hgrowth2 hshape3 hmac3)

theorem hasRankCaseAnnihilatorMapBounds_of_lowRankApolarAnnihilatorMapTheorem
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hann : HasLowRankApolarAnnihilatorMapTheorem B p u) :
    HasRankCaseAnnihilatorMapBounds B p u := by
  constructor
  · intro hrank1
    exact hann 1 (by norm_num) (by omega)
  constructor
  · intro hrank2
    exact hann 2 (by norm_num) (by omega)
  · intro hrank3
    exact hann 3 (by norm_num) (by omega)

theorem hasLowRankApolarAnnihilatorMapTheorem_of_rankCaseAnnihilatorMapBounds
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hbounds : HasRankCaseAnnihilatorMapBounds B p u) :
    HasLowRankApolarAnnihilatorMapTheorem B p u := by
  rcases hbounds with ⟨hbound1, hbound2, hbound3⟩
  intro k hk hrank_le
  let n := Module.finrank ℝ (LinearMap.range (catalecticantMap B p u))
  have hn_le : n ≤ k := hrank_le
  interval_cases k
  · have hn0 : n = 0 := by omega
    rw [finrank_range_linearAnnihilatorMap_eq_zero_of_catalecticantMap_rank_zero
      (B := B) (p := p) (u := u) hn0]
  · by_cases hn0 : n = 0
    · rw [finrank_range_linearAnnihilatorMap_eq_zero_of_catalecticantMap_rank_zero
        (B := B) (p := p) (u := u) hn0]
      norm_num
    · have hn1 : n = 1 := by omega
      exact hbound1 hn1
  · by_cases hn0 : n = 0
    · rw [finrank_range_linearAnnihilatorMap_eq_zero_of_catalecticantMap_rank_zero
        (B := B) (p := p) (u := u) hn0]
      norm_num
    · by_cases hn1 : n = 1
      · exact (hbound1 hn1).trans (by norm_num)
      · have hn2 : n = 2 := by omega
        exact hbound2 hn2
  · by_cases hn0 : n = 0
    · rw [finrank_range_linearAnnihilatorMap_eq_zero_of_catalecticantMap_rank_zero
        (B := B) (p := p) (u := u) hn0]
      norm_num
    · by_cases hn1 : n = 1
      · exact (hbound1 hn1).trans (by norm_num)
      · by_cases hn2 : n = 2
        · exact (hbound2 hn2).trans (by norm_num)
        · have hn3 : n = 3 := by omega
          exact hbound3 hn3

theorem hasLowRankApolarAnnihilatorMapTheorem_iff_rankCaseAnnihilatorMapBounds
    {B : DotForm} {p : Poly} {u : RankSevenVec} :
    HasLowRankApolarAnnihilatorMapTheorem B p u ↔
      HasRankCaseAnnihilatorMapBounds B p u :=
  ⟨hasRankCaseAnnihilatorMapBounds_of_lowRankApolarAnnihilatorMapTheorem,
    hasLowRankApolarAnnihilatorMapTheorem_of_rankCaseAnnihilatorMapBounds⟩

theorem hasLowRankApolarSupportTheorem_of_annihilatorMapTheorem
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hann : HasLowRankApolarAnnihilatorMapTheorem B p u) :
    HasLowRankApolarSupportTheorem B p u := by
  intro k hk hrank_le
  exact hasLinearAnnihilatorCodimAtMost_of_annihilatorMap_range
    (B := B) (p := p) (u := u) (k := k) (by omega)
    (hann k hk hrank_le)

theorem hasLowRankApolarAnnihilatorMapTheorem_of_supportTheorem
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupport : HasLowRankApolarSupportTheorem B p u) :
    HasLowRankApolarAnnihilatorMapTheorem B p u := by
  intro k hk hrank_le
  exact annihilatorMap_range_le_of_hasLinearAnnihilatorCodimAtMost
    (B := B) (p := p) (u := u) (k := k) (by omega)
    (hsupport k hk hrank_le)

theorem hasLowRankApolarAnnihilatorMapTheorem_iff_supportTheorem
    {B : DotForm} {p : Poly} {u : RankSevenVec} :
    HasLowRankApolarAnnihilatorMapTheorem B p u ↔
      HasLowRankApolarSupportTheorem B p u :=
  ⟨hasLowRankApolarSupportTheorem_of_annihilatorMapTheorem,
    hasLowRankApolarAnnihilatorMapTheorem_of_supportTheorem⟩

theorem hasRankCaseApolarSupportBounds_of_lowRankApolarSupportTheorem
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupport : HasLowRankApolarSupportTheorem B p u) :
    HasRankCaseApolarSupportBounds B p u := by
  constructor
  · intro hrank1
    exact hsupport 1 (by norm_num) (by omega)
  constructor
  · intro hrank2
    exact hsupport 2 (by norm_num) (by omega)
  · intro hrank3
    exact hsupport 3 (by norm_num) (by omega)

theorem hasLowRankApolarSupportTheorem_of_rankCaseApolarSupportBounds
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupport : HasRankCaseApolarSupportBounds B p u) :
    HasLowRankApolarSupportTheorem B p u := by
  rcases hsupport with ⟨hsupp1, hsupp2, hsupp3⟩
  intro k hk hrank_le
  let n := Module.finrank ℝ (LinearMap.range (catalecticantMap B p u))
  have hn_le : n ≤ k := hrank_le
  interval_cases k
  · have hn0 : n = 0 := by omega
    exact hasLinearAnnihilatorCodimAtMost_zero_of_catalecticantMap_rank_zero
      (B := B) (p := p) (u := u) hn0
  · by_cases hn0 : n = 0
    · exact HasLinearAnnihilatorCodimAtMost.mono (by norm_num)
        (hasLinearAnnihilatorCodimAtMost_zero_of_catalecticantMap_rank_zero
          (B := B) (p := p) (u := u) hn0)
    · have hn1 : n = 1 := by omega
      exact hsupp1 hn1
  · by_cases hn0 : n = 0
    · exact HasLinearAnnihilatorCodimAtMost.mono (by norm_num)
        (hasLinearAnnihilatorCodimAtMost_zero_of_catalecticantMap_rank_zero
          (B := B) (p := p) (u := u) hn0)
    · by_cases hn1 : n = 1
      · exact HasLinearAnnihilatorCodimAtMost.rank_one_to_two (hsupp1 hn1)
      · have hn2 : n = 2 := by omega
        exact hsupp2 hn2
  · by_cases hn0 : n = 0
    · exact HasLinearAnnihilatorCodimAtMost.mono (by norm_num)
        (hasLinearAnnihilatorCodimAtMost_zero_of_catalecticantMap_rank_zero
          (B := B) (p := p) (u := u) hn0)
    · by_cases hn1 : n = 1
      · exact HasLinearAnnihilatorCodimAtMost.mono (by norm_num) (hsupp1 hn1)
      · by_cases hn2 : n = 2
        · exact HasLinearAnnihilatorCodimAtMost.rank_two_to_three (hsupp2 hn2)
        · have hn3 : n = 3 := by omega
          exact hsupp3 hn3

theorem hasLowRankApolarSupportTheorem_iff_rankCaseApolarSupportBounds
    {B : DotForm} {p : Poly} {u : RankSevenVec} :
    HasLowRankApolarSupportTheorem B p u ↔
      HasRankCaseApolarSupportBounds B p u :=
  ⟨hasRankCaseApolarSupportBounds_of_lowRankApolarSupportTheorem,
    hasLowRankApolarSupportTheorem_of_rankCaseApolarSupportBounds⟩

theorem hasLowRankApolarSupportTheorem_of_decomposition
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdecomp : HasLowRankApolarSupportDecomposition B p u) :
    HasLowRankApolarSupportTheorem B p u := by
  intro k hk hrank_le
  rcases hdecomp k hk hrank_le with
    ⟨A, _W, hAann, _hAW, _hWdim, hAdim⟩
  exact ⟨A, hAann, hAdim⟩

theorem hasLowRankApolarSupportDecomposition_of_lowRankApolarSupportTheorem
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsupport : HasLowRankApolarSupportTheorem B p u) :
    HasLowRankApolarSupportDecomposition B p u := by
  intro k hk hrank_le
  exact exists_support_complement_of_hasLinearAnnihilatorCodimAtMost
    (B := B) (p := p) (u := u) (k := k) (by omega)
    (hsupport k hk hrank_le)

theorem hasLowRankApolarSupportTheorem_iff_decomposition
    {B : DotForm} {p : Poly} {u : RankSevenVec} :
    HasLowRankApolarSupportTheorem B p u ↔
      HasLowRankApolarSupportDecomposition B p u :=
  ⟨hasLowRankApolarSupportDecomposition_of_lowRankApolarSupportTheorem,
    hasLowRankApolarSupportTheorem_of_decomposition⟩

theorem hasLowRankApolarSupportDecomposition_iff_rankCaseApolarSupportBounds
    {B : DotForm} {p : Poly} {u : RankSevenVec} :
    HasLowRankApolarSupportDecomposition B p u ↔
      HasRankCaseApolarSupportBounds B p u :=
  ⟨fun hdecomp =>
      hasRankCaseApolarSupportBounds_of_lowRankApolarSupportTheorem
        (hasLowRankApolarSupportTheorem_of_decomposition hdecomp),
    fun hsupport =>
      hasLowRankApolarSupportDecomposition_of_lowRankApolarSupportTheorem
        (hasLowRankApolarSupportTheorem_of_rankCaseApolarSupportBounds hsupport)⟩

theorem hasRankCaseApolarSupportBounds_of_lowRankApolarSupportDecomposition
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdecomp : HasLowRankApolarSupportDecomposition B p u) :
    HasRankCaseApolarSupportBounds B p u :=
  hasRankCaseApolarSupportBounds_of_lowRankApolarSupportTheorem
    (hasLowRankApolarSupportTheorem_of_decomposition hdecomp)

theorem hasLowRankApolarSupportDecomposition_of_productKernelDecomposition
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hprod : HasLowRankApolarProductKernelDecomposition B p u) :
    HasLowRankApolarSupportDecomposition B p u := by
  intro k hk hrank_le
  rcases hprod k hk hrank_le with
    ⟨A, W, hAE, hAW, hWdim, hAdim⟩
  exact ⟨A, W,
    le_linearAnnihilator_of_linProductSubmodule_top_le_ker hAE,
    hAW, hWdim, hAdim⟩

theorem hasLowRankApolarProductKernelDecomposition_of_supportDecomposition
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdecomp : HasLowRankApolarSupportDecomposition B p u) :
    HasLowRankApolarProductKernelDecomposition B p u := by
  intro k hk hrank_le
  rcases hdecomp k hk hrank_le with
    ⟨A, W, hAann, hAW, hWdim, hAdim⟩
  exact ⟨A, W,
    linProductSubmodule_le_ker_of_le_linearAnnihilator hAann,
    hAW, hWdim, hAdim⟩

theorem hasLowRankApolarSupportTheorem_of_productKernelDecomposition
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hprod : HasLowRankApolarProductKernelDecomposition B p u) :
    HasLowRankApolarSupportTheorem B p u :=
  hasLowRankApolarSupportTheorem_of_decomposition
    (hasLowRankApolarSupportDecomposition_of_productKernelDecomposition hprod)

theorem hasLowRankApolarProductKernelDecomposition_iff_supportDecomposition
    {B : DotForm} {p : Poly} {u : RankSevenVec} :
    HasLowRankApolarProductKernelDecomposition B p u ↔
      HasLowRankApolarSupportDecomposition B p u :=
  ⟨hasLowRankApolarSupportDecomposition_of_productKernelDecomposition,
    hasLowRankApolarProductKernelDecomposition_of_supportDecomposition⟩

theorem hasLowRankApolarAnnihilatorMapTheorem_of_productKernelDecomposition
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hprod : HasLowRankApolarProductKernelDecomposition B p u) :
    HasLowRankApolarAnnihilatorMapTheorem B p u :=
  hasLowRankApolarAnnihilatorMapTheorem_of_supportTheorem
    (hasLowRankApolarSupportTheorem_of_productKernelDecomposition hprod)

theorem hasLowRankApolarProductKernelDecomposition_of_annihilatorMapTheorem
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hann : HasLowRankApolarAnnihilatorMapTheorem B p u) :
    HasLowRankApolarProductKernelDecomposition B p u :=
  hasLowRankApolarProductKernelDecomposition_of_supportDecomposition
    (hasLowRankApolarSupportDecomposition_of_lowRankApolarSupportTheorem
      (hasLowRankApolarSupportTheorem_of_annihilatorMapTheorem hann))

theorem hasLowRankApolarAnnihilatorMapTheorem_iff_productKernelDecomposition
    {B : DotForm} {p : Poly} {u : RankSevenVec} :
    HasLowRankApolarAnnihilatorMapTheorem B p u ↔
      HasLowRankApolarProductKernelDecomposition B p u :=
  ⟨hasLowRankApolarProductKernelDecomposition_of_annihilatorMapTheorem,
    hasLowRankApolarAnnihilatorMapTheorem_of_productKernelDecomposition⟩

theorem hasRankCaseProductIndependenceGeometryData_of_apolarSupportBounds
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u)
    (hsupport : HasRankCaseApolarSupportBounds B p u) :
    HasRankCaseProductIndependenceGeometryData B p u hu :=
  hasRankCaseProductIndependenceGeometryData_of_annihilatorMapBounds
    (B := B) (p := p) (u := u) (hu := hu) hp hfocp
    (hasRankCaseAnnihilatorMapBounds_of_apolarSupportBounds hsupport)

theorem hasRankCaseProductIndependenceGeometryData_of_lowRankApolarSupportTheorem
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u)
    (hsupport : HasLowRankApolarSupportTheorem B p u) :
    HasRankCaseProductIndependenceGeometryData B p u hu :=
  hasRankCaseProductIndependenceGeometryData_of_apolarSupportBounds
    (B := B) (p := p) (u := u) (hu := hu) hp hfocp
    (hasRankCaseApolarSupportBounds_of_lowRankApolarSupportTheorem hsupport)

theorem hasRankCaseProductIndependenceGeometryData_of_lowRankApolarSupportDecomposition
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u)
    (hdecomp : HasLowRankApolarSupportDecomposition B p u) :
    HasRankCaseProductIndependenceGeometryData B p u hu :=
  hasRankCaseProductIndependenceGeometryData_of_lowRankApolarSupportTheorem
    (B := B) (p := p) (u := u) (hu := hu) hp hfocp
    (hasLowRankApolarSupportTheorem_of_decomposition hdecomp)

theorem hasRankTwoExistentialBinaryFormData_of_kernelEquationData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hcases : HasRankTwoExistentialKernelEquationData B p u) :
    HasRankTwoExistentialBinaryFormData B p u := by
  intro hrank2 A W x hAann hAW hxW hx hAdim hWdim
  rcases hcases hrank2 A W x hAann hAW hxW hx hAdim hWdim with
    ⟨y, hyW, hynot, hcase⟩
  exact ⟨y, hyW, hynot,
    binaryRestriction_lowRankNegativeNormalForm_of_kernelEquationCase hcase⟩

theorem hasRankTwoExistentialCanonicalKernelData_of_kernelEquationData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hcases : HasRankTwoExistentialKernelEquationData B p u) :
    HasRankTwoExistentialCanonicalKernelData B p u := by
  intro hrank2 A W x hAann hAW hxW hx hAdim hWdim
  rcases hcases hrank2 A W x hAann hAW hxW hx hAdim hWdim with
    ⟨y, hyW, hynot, hcase⟩
  exact ⟨y, hyW, hynot,
    binaryRestriction_canonicalKernelData_of_kernelEquationCase hcase⟩

theorem hasRankTwoExistentialBinaryFormData_of_kernelBranchData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hbranches : HasRankTwoExistentialKernelBranchData B p u) :
    HasRankTwoExistentialBinaryFormData B p u := by
  intro hrank2 A W x hAann hAW hxW hx hAdim hWdim
  rcases hbranches hrank2 A W x hAann hAW hxW hx hAdim hWdim with
    ⟨y, hyW, hynot, hcert⟩
  exact ⟨y, hyW, hynot,
    binaryRestriction_lowRankNegativeNormalForm_of_kernelBranchCertificate hcert⟩

theorem hasRankTwoExistentialKernelBranchData_of_canonicalKernelData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hcanon : HasRankTwoExistentialCanonicalKernelData B p u) :
    HasRankTwoExistentialKernelBranchData B p u := by
  intro hrank2 A W x hAann hAW hxW hx hAdim hWdim
  rcases hcanon hrank2 A W x hAann hAW hxW hx hAdim hWdim with
    ⟨y, hyW, hynot, hcanon_y⟩
  exact ⟨y, hyW, hynot,
    binaryKernelBranchCertificate_of_canonicalKernelData hcanon_y⟩

theorem hasRankTwoExistentialCanonicalKernelData_of_scalarHankelData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hscalar : HasRankTwoExistentialScalarHankelData B p u) :
    HasRankTwoExistentialCanonicalKernelData B p u := by
  intro hrank2 A W x hAann hAW hxW hx hAdim hWdim
  rcases hscalar hrank2 A W x hAann hAW hxW hx hAdim hWdim with
    ⟨y, hyW, hynot, hclass, hneg, hrank⟩
  exact ⟨y, hyW, hynot, hclass hneg hrank⟩

theorem hasRankTwoExistentialNormalizedHankelData_of_canonicalKernelData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hcanon : HasRankTwoExistentialCanonicalKernelData B p u) :
    HasRankTwoExistentialNormalizedHankelData B p u := by
  intro hrank2 A W x hAann hAW hxW hx hAdim hWdim
  rcases hcanon hrank2 A W x hAann hAW hxW hx hAdim hWdim with
    ⟨y, hyW, hynot, hcanon_y⟩
  exact ⟨y, hyW, hynot,
    binaryNormalizedKernelPosition_of_canonicalKernelData hcanon_y,
    binaryHankelNegativeValue_of_canonicalKernelData hcanon_y,
    binaryHankelLinearMap_finrank_range_le_two_of_canonicalKernelData hcanon_y⟩

theorem hasRankTwoExistentialNormalizedHankelData_of_kernelEquationData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hcases : HasRankTwoExistentialKernelEquationData B p u) :
    HasRankTwoExistentialNormalizedHankelData B p u :=
  hasRankTwoExistentialNormalizedHankelData_of_canonicalKernelData
    (hasRankTwoExistentialCanonicalKernelData_of_kernelEquationData hcases)

theorem hasRankTwoExistentialScalarHankelData_of_universal_and_facts
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hclass : HasUniversalBinaryRankTwoNormalizedKernelClassification)
    (hfacts : HasRankTwoExistentialScalarHankelFacts B p u) :
    HasRankTwoExistentialScalarHankelData B p u := by
  intro hrank2 A W x hAann hAW hxW hx hAdim hWdim
  rcases hfacts hrank2 A W x hAann hAW hxW hx hAdim hWdim with
    ⟨y, hyW, hynot, hneg, hrank⟩
  refine ⟨y, hyW, hynot, ?_, hneg, hrank⟩
  exact hclass
    (binaryRestrictionCoeffA B p u x)
    (binaryRestrictionCoeffB B p u x y)
    (binaryRestrictionCoeffC B p u x y)
    (binaryRestrictionCoeffD B p u x y)
    (binaryRestrictionCoeffE B p u y)

theorem hasRankTwoExistentialScalarHankelData_of_normalizedHankelData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasRankTwoExistentialNormalizedHankelData B p u) :
    HasRankTwoExistentialScalarHankelData B p u := by
  intro hrank2 A W x hAann hAW hxW hx hAdim hWdim
  rcases hdata hrank2 A W x hAann hAW hxW hx hAdim hWdim with
    ⟨y, hyW, hynot, hpos, hneg, hrank⟩
  exact ⟨y, hyW, hynot,
    binaryRankTwoNormalizedKernelClassification_of_normalizedKernelPosition hpos,
    hneg, hrank⟩

theorem hasRankTwoExistentialNormalizedHankelData_of_universalNormalizedPosition_and_facts
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hpos : HasRankTwoUniversalNormalizedKernelPositionData B p u)
    (hfacts : HasRankTwoExistentialScalarHankelFacts B p u) :
    HasRankTwoExistentialNormalizedHankelData B p u := by
  intro hrank2 A W x hAann hAW hxW hx hAdim hWdim
  rcases hfacts hrank2 A W x hAann hAW hxW hx hAdim hWdim with
    ⟨y, hyW, hynot, hneg, hrank⟩
  exact ⟨y, hyW, hynot,
    hpos hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim,
    hneg, hrank⟩

theorem hasRankTwoExistentialScalarHankelFacts_of_universalNormalizedPosition_and_HankelNegative
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (_hpos : HasRankTwoUniversalNormalizedKernelPositionData B p u)
    (hneg : HasRankTwoUniversalHankelNegativeData B p u) :
    HasRankTwoExistentialScalarHankelFacts B p u := by
  intro hrank2 A W x hAann hAW hxW hx hAdim hWdim
  rcases exists_rank_two_complement_second_direction
      (W := W) (x := x) hx hWdim with
    ⟨y, hyW, hynot⟩
  exact ⟨y, hyW, hynot,
    hneg hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim,
    universalBinaryHankelRankBound_of_catalecticantRankTwo
      hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim⟩

theorem hasRankTwoExistentialScalarHankelFacts_of_point
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u) :
    HasRankTwoExistentialScalarHankelFacts B p u := by
  intro hrank2 A W x hAann hAW hxW hx hAdim hWdim
  rcases exists_rank_two_complement_second_direction
      (W := W) (x := x) hx hWdim with
    ⟨y, hyW, hynot⟩
  refine ⟨y, hyW, hynot, ?_, ?_⟩
  · exact hasRankTwoUniversalHankelNegativeData_of_point
      (B := B) (p := p) (u := u) hu hp hfocp
      hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim
  · exact universalBinaryHankelRankBound_of_catalecticantRankTwo
      hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim

theorem hasRankTwoExistentialCanonicalKernelData_of_universal_and_facts
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hclass : HasUniversalBinaryRankTwoNormalizedKernelClassification)
    (hfacts : HasRankTwoExistentialScalarHankelFacts B p u) :
    HasRankTwoExistentialCanonicalKernelData B p u :=
  hasRankTwoExistentialCanonicalKernelData_of_scalarHankelData
    (hasRankTwoExistentialScalarHankelData_of_universal_and_facts hclass hfacts)

theorem hasRankTwoExistentialCanonicalKernelData_of_normalizedHankelData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasRankTwoExistentialNormalizedHankelData B p u) :
    HasRankTwoExistentialCanonicalKernelData B p u :=
  hasRankTwoExistentialCanonicalKernelData_of_scalarHankelData
    (hasRankTwoExistentialScalarHankelData_of_normalizedHankelData hdata)

theorem hasRankTwoExistentialCanonicalKernelData_of_universalClassification_of_point
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u)
    (hclass : HasUniversalBinaryRankTwoNormalizedKernelClassification) :
    HasRankTwoExistentialCanonicalKernelData B p u :=
  hasRankTwoExistentialCanonicalKernelData_of_universal_and_facts
    hclass
    (hasRankTwoExistentialScalarHankelFacts_of_point
      (B := B) (p := p) (u := u) hu hp hfocp)

theorem hasRankTwoExistentialNormalizedHankelData_of_universalClassification_of_point
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u)
    (hclass : HasUniversalBinaryRankTwoNormalizedKernelClassification) :
    HasRankTwoExistentialNormalizedHankelData B p u :=
  hasRankTwoExistentialNormalizedHankelData_of_canonicalKernelData
    (hasRankTwoExistentialCanonicalKernelData_of_universalClassification_of_point
      (B := B) (p := p) (u := u) hu hp hfocp hclass)

theorem hasRankTwoExistentialCanonicalKernelData_iff_normalizedHankelData
    {B : DotForm} {p : Poly} {u : RankSevenVec} :
    HasRankTwoExistentialCanonicalKernelData B p u ↔
      HasRankTwoExistentialNormalizedHankelData B p u :=
  ⟨hasRankTwoExistentialNormalizedHankelData_of_canonicalKernelData,
    hasRankTwoExistentialCanonicalKernelData_of_normalizedHankelData⟩

theorem hasRankTwoExistentialBinaryFormData_of_canonicalKernelData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hcanon : HasRankTwoExistentialCanonicalKernelData B p u) :
    HasRankTwoExistentialBinaryFormData B p u := by
  intro hrank2 A W x hAann hAW hxW hx hAdim hWdim
  rcases hcanon hrank2 A W x hAann hAW hxW hx hAdim hWdim with
    ⟨y, hyW, hynot, hcanon_y⟩
  exact ⟨y, hyW, hynot,
    binaryRestriction_lowRankNegativeNormalForm_of_canonicalKernelData hcanon_y⟩

theorem hasRankTwoExistentialBinaryFormData_of_scalarHankelData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hscalar : HasRankTwoExistentialScalarHankelData B p u) :
    HasRankTwoExistentialBinaryFormData B p u :=
  hasRankTwoExistentialBinaryFormData_of_canonicalKernelData
    (hasRankTwoExistentialCanonicalKernelData_of_scalarHankelData hscalar)

theorem hasRankTwoExistentialBinaryFormData_of_universal_and_facts
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hclass : HasUniversalBinaryRankTwoNormalizedKernelClassification)
    (hfacts : HasRankTwoExistentialScalarHankelFacts B p u) :
    HasRankTwoExistentialBinaryFormData B p u :=
  hasRankTwoExistentialBinaryFormData_of_scalarHankelData
    (hasRankTwoExistentialScalarHankelData_of_universal_and_facts hclass hfacts)

theorem hasRankTwoExistentialBinaryFormData_of_normalizedHankelData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasRankTwoExistentialNormalizedHankelData B p u) :
    HasRankTwoExistentialBinaryFormData B p u :=
  hasRankTwoExistentialBinaryFormData_of_scalarHankelData
    (hasRankTwoExistentialScalarHankelData_of_normalizedHankelData hdata)

theorem hasRankTwoNegativeSquareData_of_existentialBinaryFormData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hforms : HasRankTwoExistentialBinaryFormData B p u) :
    HasRankTwoNegativeSquareData B p u := by
  intro hrank2 A W hAann hAW hAdim hWdim
  have hWpos : 0 < Module.finrank ℝ W := by omega
  rcases exists_mem_ne_zero_of_finrank_pos (K := ℝ) (V := linSubmodule)
      (s := W) hWpos with
    ⟨x, hxW, hxne⟩
  have hx : (x : Poly) ≠ 0 := by
    intro hzero
    exact hxne (Subtype.ext hzero)
  rcases hforms hrank2 A W x hAann hAW hxW hx hAdim hWdim with
    ⟨y, hyW, hynot, hform⟩
  rcases exists_negative_pure_square_of_binaryLowRankNormalForm
      (B := B) (p := p) (u := u)
      (x := x) (y := y) hform
      (binaryRestriction_eval_eq B p u x y) with
    ⟨z, hzspan, hneg⟩
  have hzW : z ∈ W := by
    have hspan : Submodule.span ℝ ({x, y} : Set linSubmodule) = W :=
      span_rank_two_support_pair_eq hx hxW hyW hynot hWdim
    rwa [hspan] at hzspan
  have hz : (z : Poly) ≠ 0 := by
    intro hzero
    have hval_zero :
        B ((linProduct z z : quadSubmodule).1^2) (residual p u) = 0 := by
      simp [linProduct, hzero]
    linarith
  exact ⟨z, hzW, hz, hneg⟩

theorem hasRankCaseNegativeSquareApolarData_of_annihilatorBounds_and_binaryForms
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hbounds : HasRankCaseAnnihilatorMapBounds B p u)
    (hforms : HasRankTwoExistentialBinaryFormData B p u) :
    HasRankCaseNegativeSquareApolarData B p u hu :=
  hasRankCaseNegativeSquareApolarData_of_annihilatorBounds_and_rankTwo
    (hu := hu) hbounds
    (hasRankTwoNegativeSquareData_of_existentialBinaryFormData hforms)

theorem hasRankCaseNegativeSquareApolarData_of_apolarSupportBounds_and_binaryForms
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hsupport : HasRankCaseApolarSupportBounds B p u)
    (hforms : HasRankTwoExistentialBinaryFormData B p u) :
    HasRankCaseNegativeSquareApolarData B p u hu :=
  hasRankCaseNegativeSquareApolarData_of_annihilatorBounds_and_binaryForms
    (hu := hu)
    (hasRankCaseAnnihilatorMapBounds_of_apolarSupportBounds hsupport)
    hforms

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

theorem hasRankCaseKernelEquationApolarData_of_productIndependenceApolarData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hdata : HasRankCaseProductIndependenceApolarData B p u hu) :
    HasRankCaseKernelEquationApolarData B p u hu := by
  rcases hdata with ⟨hdata1, hdata2, hdata3⟩
  constructor
  · intro hrank1
    exact (hdata1 hrank1).1
  constructor
  · intro hrank2
    exact ⟨(hdata2 hrank2).1, (hdata2 hrank2).2.1⟩
  · intro hrank3
    exact (hdata3 hrank3).1

theorem hasRankCaseKernelEquationApolarData_of_productFreeApolarData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hdata : HasRankCaseProductFreeApolarData B p u hu) :
    HasRankCaseKernelEquationApolarData B p u hu := by
  rcases hdata with ⟨hdata1, hdata2, hdata3⟩
  constructor
  · intro hrank1
    exact (hdata1 hrank1).1
  constructor
  · intro hrank2
    exact ⟨(hdata2 hrank2).1, (hdata2 hrank2).2⟩
  · intro hrank3
    exact (hdata3 hrank3).1

theorem hasRankCaseKernelEquationApolarData_of_rankOneFreeApolarData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hdata : HasRankCaseRankOneFreeApolarData B p u hu) :
    HasRankCaseKernelEquationApolarData B p u hu := by
  rcases hdata with ⟨hdata1, hdata2, hdata3⟩
  constructor
  · intro hrank1
    exact hdata1 hrank1
  constructor
  · intro hrank2
    exact hdata2 hrank2
  · intro hrank3
    exact (hdata3 hrank3).1

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

theorem hasRankCaseAnnihilatorMapBounds_of_kernelDecompositionApolarData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hdata : HasRankCaseKernelDecompositionApolarData B p u hu) :
    HasRankCaseAnnihilatorMapBounds B p u := by
  rcases hdata with ⟨hdata1, hdata2, hdata3⟩
  constructor
  · intro hrank1
    exact (hdata1 hrank1).1
  constructor
  · intro hrank2
    exact (hdata2 hrank2).1
  · intro hrank3
    exact (hdata3 hrank3).1

theorem hasRankCaseKernelEquationApolarData_of_kernelDecompositionApolarData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hdata : HasRankCaseKernelDecompositionApolarData B p u hu) :
    HasRankCaseKernelEquationApolarData B p u hu := by
  rcases hdata with ⟨hdata1, hdata2, hdata3⟩
  constructor
  · intro hrank1
    exact (hdata1 hrank1).1
  constructor
  · intro hrank2
    exact ⟨(hdata2 hrank2).1, (hdata2 hrank2).2.1⟩
  · intro hrank3
    exact (hdata3 hrank3).1

theorem hasRankCaseKernelEquationApolarData_of_lowRankApolarAnnihilatorMapTheorem_and_universalKernelEquationData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hann : HasLowRankApolarAnnihilatorMapTheorem B p u)
    (hcases : HasRankTwoUniversalKernelEquationData B p u) :
    HasRankCaseKernelEquationApolarData B p u hu := by
  have hbounds : HasRankCaseAnnihilatorMapBounds B p u :=
    hasRankCaseAnnihilatorMapBounds_of_lowRankApolarAnnihilatorMapTheorem hann
  rcases hbounds with ⟨hbound1, hbound2, hbound3⟩
  constructor
  · intro hrank1
    exact hbound1 hrank1
  constructor
  · intro hrank2
    exact ⟨hbound2 hrank2, hcases hrank2⟩
  · intro hrank3
    exact hbound3 hrank3

theorem hasRankCaseKernelEquationApolarData_of_lowRankApolarSupportTheorem_and_universalKernelEquationData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hsupport : HasLowRankApolarSupportTheorem B p u)
    (hcases : HasRankTwoUniversalKernelEquationData B p u) :
    HasRankCaseKernelEquationApolarData B p u hu :=
  hasRankCaseKernelEquationApolarData_of_lowRankApolarAnnihilatorMapTheorem_and_universalKernelEquationData
    (B := B) (p := p) (u := u) (hu := hu)
    (hasLowRankApolarAnnihilatorMapTheorem_of_supportTheorem hsupport)
    hcases

theorem hasRankCaseAnnihilatorMapBounds_of_kernelEquationApolarData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hdata : HasRankCaseKernelEquationApolarData B p u hu) :
    HasRankCaseAnnihilatorMapBounds B p u := by
  rcases hdata with ⟨hdata1, hdata2, hdata3⟩
  constructor
  · intro hrank1
    exact hdata1 hrank1
  constructor
  · intro hrank2
    exact (hdata2 hrank2).1
  · intro hrank3
    exact hdata3 hrank3

theorem hasRankCaseApolarSupportBounds_of_kernelEquationApolarData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hdata : HasRankCaseKernelEquationApolarData B p u hu) :
    HasRankCaseApolarSupportBounds B p u :=
  hasRankCaseApolarSupportBounds_of_annihilatorMapBounds
    (hasRankCaseAnnihilatorMapBounds_of_kernelEquationApolarData hdata)

theorem hasRankTwoUniversalKernelEquationData_of_kernelEquationApolarData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hdata : HasRankCaseKernelEquationApolarData B p u hu) :
    HasRankTwoUniversalKernelEquationData B p u := by
  intro hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim
  rcases hdata with ⟨_hdata1, hdata2, _hdata3⟩
  exact (hdata2 hrank2).2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim

theorem supportBounds_and_universalKernelEquationData_of_kernelEquationApolarData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hdata : HasRankCaseKernelEquationApolarData B p u hu) :
    HasRankCaseApolarSupportBounds B p u ∧
      HasRankTwoUniversalKernelEquationData B p u :=
  ⟨hasRankCaseApolarSupportBounds_of_kernelEquationApolarData hdata,
    hasRankTwoUniversalKernelEquationData_of_kernelEquationApolarData hdata⟩

theorem supportBounds_and_universalKernelEquationData_of_kernelDecompositionApolarData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hdata : HasRankCaseKernelDecompositionApolarData B p u hu) :
    HasRankCaseApolarSupportBounds B p u ∧
      HasRankTwoUniversalKernelEquationData B p u :=
  supportBounds_and_universalKernelEquationData_of_kernelEquationApolarData
    (hasRankCaseKernelEquationApolarData_of_kernelDecompositionApolarData hdata)

theorem hasRankTwoUniversalCanonicalKernelData_of_universalKernelEquationData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hcases : HasRankTwoUniversalKernelEquationData B p u) :
    HasRankTwoUniversalCanonicalKernelData B p u := by
  intro hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim
  exact binaryRestriction_canonicalKernelData_of_kernelEquationCase
    (hcases hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim)

theorem hasRankTwoUniversalNormalizedKernelPositionData_of_universalKernelEquationData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hcases : HasRankTwoUniversalKernelEquationData B p u) :
    HasRankTwoUniversalNormalizedKernelPositionData B p u := by
  intro hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim
  exact binaryNormalizedKernelPosition_of_canonicalKernelData
    (binaryRestriction_canonicalKernelData_of_kernelEquationCase
      (hcases hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim))

theorem hasRankTwoUniversalKernelEquationData_of_universalCanonicalKernelData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hcanon : HasRankTwoUniversalCanonicalKernelData B p u) :
    HasRankTwoUniversalKernelEquationData B p u := by
  intro hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim
  exact binaryRestriction_kernelEquationCase_of_canonicalKernelData
    (hcanon hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim)

theorem hasRankTwoUniversalKernelBranchData_of_universalCanonicalKernelData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hcanon : HasRankTwoUniversalCanonicalKernelData B p u) :
    HasRankTwoUniversalKernelBranchData B p u := by
  intro hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim
  exact binaryKernelBranchCertificate_of_canonicalKernelData
    (hcanon hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim)

theorem hasRankTwoUniversalKernelBranchData_of_universalNormalizedPosition_and_HankelNegative
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hpos : HasRankTwoUniversalNormalizedKernelPositionData B p u)
    (hneg : HasRankTwoUniversalHankelNegativeData B p u) :
    HasRankTwoUniversalKernelBranchData B p u := by
  intro hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim
  exact binaryKernelBranchCertificate_of_normalizedKernelPosition
    (hpos hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim)
    (hneg hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim)

theorem universalNormalizedPosition_and_HankelNegative_of_universalKernelBranchData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hbranches : HasRankTwoUniversalKernelBranchData B p u) :
    HasRankTwoUniversalNormalizedKernelPositionData B p u ∧
      HasRankTwoUniversalHankelNegativeData B p u := by
  constructor
  · intro hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim
    exact binaryNormalizedKernelPosition_of_kernelBranchCertificate
      (hbranches hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim)
  · intro hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim
    exact binaryHankelNegativeValue_of_kernelBranchCertificate
      (hbranches hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim)

theorem hasRankTwoUniversalKernelBranchData_iff_universalNormalizedPosition_and_HankelNegative
    {B : DotForm} {p : Poly} {u : RankSevenVec} :
    HasRankTwoUniversalKernelBranchData B p u ↔
      HasRankTwoUniversalNormalizedKernelPositionData B p u ∧
        HasRankTwoUniversalHankelNegativeData B p u := by
  constructor
  · exact universalNormalizedPosition_and_HankelNegative_of_universalKernelBranchData
  · intro hdata
    exact hasRankTwoUniversalKernelBranchData_of_universalNormalizedPosition_and_HankelNegative
      hdata.1 hdata.2

theorem hasRankTwoUniversalKernelEquationData_of_universalKernelBranchData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hbranches : HasRankTwoUniversalKernelBranchData B p u) :
    HasRankTwoUniversalKernelEquationData B p u := by
  intro hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim
  exact binaryRestriction_kernelEquationCase_of_kernelBranchCertificate
    (hbranches hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim)

theorem hasRankTwoUniversalKernelEquationData_of_universalNormalizedPosition_of_point
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u)
    (hpos : HasRankTwoUniversalNormalizedKernelPositionData B p u) :
    HasRankTwoUniversalKernelEquationData B p u :=
  hasRankTwoUniversalKernelEquationData_of_universalKernelBranchData
    (hasRankTwoUniversalKernelBranchData_of_universalNormalizedPosition_and_HankelNegative
      hpos
      (hasRankTwoUniversalHankelNegativeData_of_point
        (B := B) (p := p) (u := u) hu hp hfocp))

theorem hasRankTwoUniversalNormalizedHankelData_of_universalKernelBranchData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hbranches : HasRankTwoUniversalKernelBranchData B p u) :
    HasRankTwoUniversalNormalizedHankelData B p u := by
  intro hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim
  have hcert :=
    hbranches hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim
  exact ⟨
    binaryNormalizedKernelPosition_of_kernelBranchCertificate hcert,
    binaryHankelNegativeValue_of_kernelBranchCertificate hcert,
    binaryHankelLinearMap_finrank_range_le_two_of_kernelBranchCertificate hcert⟩

theorem hasRankTwoUniversalNormalizedHankelData_of_universalCanonicalKernelData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hcanon : HasRankTwoUniversalCanonicalKernelData B p u) :
    HasRankTwoUniversalNormalizedHankelData B p u := by
  intro hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim
  have hcanon_xy :=
    hcanon hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim
  exact ⟨
    binaryNormalizedKernelPosition_of_canonicalKernelData hcanon_xy,
    binaryHankelNegativeValue_of_canonicalKernelData hcanon_xy,
    binaryHankelLinearMap_finrank_range_le_two_of_canonicalKernelData hcanon_xy⟩

theorem hasRankTwoUniversalCanonicalKernelData_of_universalNormalizedHankelData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasRankTwoUniversalNormalizedHankelData B p u) :
    HasRankTwoUniversalCanonicalKernelData B p u := by
  intro hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim
  rcases hdata hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim with
    ⟨hpos, hneg, _hrank⟩
  exact binaryCanonicalKernelData_of_normalizedKernelPosition hpos hneg

theorem hasRankTwoUniversalCanonicalKernelData_iff_universalNormalizedHankelData
    {B : DotForm} {p : Poly} {u : RankSevenVec} :
    HasRankTwoUniversalCanonicalKernelData B p u ↔
      HasRankTwoUniversalNormalizedHankelData B p u :=
  ⟨hasRankTwoUniversalNormalizedHankelData_of_universalCanonicalKernelData,
    hasRankTwoUniversalCanonicalKernelData_of_universalNormalizedHankelData⟩

theorem hasRankTwoUniversalKernelBranchData_of_universalNormalizedHankelData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasRankTwoUniversalNormalizedHankelData B p u) :
    HasRankTwoUniversalKernelBranchData B p u :=
  hasRankTwoUniversalKernelBranchData_of_universalCanonicalKernelData
    (hasRankTwoUniversalCanonicalKernelData_of_universalNormalizedHankelData hdata)

theorem hasRankCaseApolarComponentData_of_productIndependenceGeometryData_and_universalNormalizedHankelData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hgeom : HasRankCaseProductIndependenceGeometryData B p u hu)
    (hdata : HasRankTwoUniversalNormalizedHankelData B p u) :
    HasRankCaseApolarComponentData B p u hu :=
  hasRankCaseApolarComponentData_of_productIndependenceGeometryData_and_universalKernelBranchData
    (B := B) (p := p) (u := u) (hu := hu)
    hgeom
    (hasRankTwoUniversalKernelBranchData_of_universalNormalizedHankelData hdata)

theorem hasRankTwoUniversalNormalizedHankelData_of_components
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hpos : HasRankTwoUniversalNormalizedKernelPositionData B p u)
    (hneg : HasRankTwoUniversalHankelNegativeData B p u)
    (hrank : HasRankTwoUniversalBinaryHankelRankBound B p u) :
    HasRankTwoUniversalNormalizedHankelData B p u := by
  intro hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim
  exact ⟨
    hpos hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim,
    hneg hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim,
    hrank hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim⟩

theorem universalNormalizedKernelPositionData_of_universalNormalizedHankelData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasRankTwoUniversalNormalizedHankelData B p u) :
    HasRankTwoUniversalNormalizedKernelPositionData B p u := by
  intro hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim
  exact (hdata hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim).1

theorem universalHankelNegativeData_of_universalNormalizedHankelData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasRankTwoUniversalNormalizedHankelData B p u) :
    HasRankTwoUniversalHankelNegativeData B p u := by
  intro hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim
  exact (hdata hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim).2.1

theorem universalBinaryHankelRankBound_of_universalNormalizedHankelData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasRankTwoUniversalNormalizedHankelData B p u) :
    HasRankTwoUniversalBinaryHankelRankBound B p u := by
  intro hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim
  exact (hdata hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim).2.2

theorem universalBinaryHankelRankBound_of_universalNormalizedKernelPositionData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hpos : HasRankTwoUniversalNormalizedKernelPositionData B p u) :
    HasRankTwoUniversalBinaryHankelRankBound B p u := by
  intro hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim
  exact binaryHankelLinearMap_finrank_range_le_two_of_normalizedKernelPosition
    (hpos hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim)

theorem hasRankTwoUniversalNormalizedHankelData_of_universalNormalizedPosition_and_HankelNegative
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hpos : HasRankTwoUniversalNormalizedKernelPositionData B p u)
    (hneg : HasRankTwoUniversalHankelNegativeData B p u) :
    HasRankTwoUniversalNormalizedHankelData B p u :=
  hasRankTwoUniversalNormalizedHankelData_of_components
    hpos hneg
    universalBinaryHankelRankBound_of_catalecticantRankTwo

theorem hasRankTwoUniversalNormalizedHankelData_of_universalNormalizedPosition_of_point
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u)
    (hpos : HasRankTwoUniversalNormalizedKernelPositionData B p u) :
    HasRankTwoUniversalNormalizedHankelData B p u :=
  hasRankTwoUniversalNormalizedHankelData_of_universalNormalizedPosition_and_HankelNegative
    hpos
    (hasRankTwoUniversalHankelNegativeData_of_point
      (B := B) (p := p) (u := u) hu hp hfocp)

theorem hasRankTwoUniversalKernelBranchData_of_universalNormalizedPosition_of_point
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u)
    (hpos : HasRankTwoUniversalNormalizedKernelPositionData B p u) :
    HasRankTwoUniversalKernelBranchData B p u :=
  hasRankTwoUniversalKernelBranchData_of_universalNormalizedHankelData
    (hasRankTwoUniversalNormalizedHankelData_of_universalNormalizedPosition_of_point
      (B := B) (p := p) (u := u) hu hp hfocp hpos)

theorem hasRankCaseKernelEquationApolarData_of_annihilatorBounds_and_universalKernelEquationData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hbounds : HasRankCaseAnnihilatorMapBounds B p u)
    (hcases : HasRankTwoUniversalKernelEquationData B p u) :
    HasRankCaseKernelEquationApolarData B p u hu := by
  rcases hbounds with ⟨hbound1, hbound2, hbound3⟩
  constructor
  · intro hrank1
    exact hbound1 hrank1
  constructor
  · intro hrank2
    exact ⟨hbound2 hrank2, hcases hrank2⟩
  · intro hrank3
    exact hbound3 hrank3

theorem hasRankTwoExistentialKernelEquationData_of_kernelDecompositionApolarData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hdata : HasRankCaseKernelDecompositionApolarData B p u hu) :
    HasRankTwoExistentialKernelEquationData B p u := by
  intro hrank2 A W x hAann hAW hxW hx hAdim hWdim
  rcases hdata with ⟨_hdata1, hdata2, _hdata3⟩
  rcases exists_rank_two_complement_second_direction
      (W := W) (x := x) hx hWdim with
    ⟨y, hyW, hynot⟩
  exact ⟨y, hyW, hynot,
    (hdata2 hrank2).2.1 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim⟩

theorem hasRankTwoExistentialKernelEquationData_of_universalKernelEquationData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hcases : HasRankTwoUniversalKernelEquationData B p u) :
    HasRankTwoExistentialKernelEquationData B p u := by
  intro hrank2 A W x hAann hAW hxW hx hAdim hWdim
  rcases exists_rank_two_complement_second_direction
      (W := W) (x := x) hx hWdim with
    ⟨y, hyW, hynot⟩
  exact ⟨y, hyW, hynot,
    hcases hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim⟩

theorem hasRankTwoExistentialKernelBranchData_of_universalKernelBranchData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hbranches : HasRankTwoUniversalKernelBranchData B p u) :
    HasRankTwoExistentialKernelBranchData B p u := by
  intro hrank2 A W x hAann hAW hxW hx hAdim hWdim
  rcases exists_rank_two_complement_second_direction
      (W := W) (x := x) hx hWdim with
    ⟨y, hyW, hynot⟩
  exact ⟨y, hyW, hynot,
    hbranches hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim⟩

theorem hasRankTwoExistentialNormalizedHankelData_of_universalNormalizedHankelData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasRankTwoUniversalNormalizedHankelData B p u) :
    HasRankTwoExistentialNormalizedHankelData B p u := by
  intro hrank2 A W x hAann hAW hxW hx hAdim hWdim
  rcases exists_rank_two_complement_second_direction
      (W := W) (x := x) hx hWdim with
    ⟨y, hyW, hynot⟩
  exact ⟨y, hyW, hynot,
    hdata hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim⟩

theorem hasRankTwoExistentialNormalizedHankelData_of_universalKernelBranchData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hbranches : HasRankTwoUniversalKernelBranchData B p u) :
    HasRankTwoExistentialNormalizedHankelData B p u :=
  hasRankTwoExistentialNormalizedHankelData_of_universalNormalizedHankelData
    (hasRankTwoUniversalNormalizedHankelData_of_universalKernelBranchData hbranches)

theorem hasRankTwoNegativeSquareData_of_existentialNormalizedHankelData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasRankTwoExistentialNormalizedHankelData B p u) :
    HasRankTwoNegativeSquareData B p u :=
  hasRankTwoNegativeSquareData_of_existentialBinaryFormData
    (hasRankTwoExistentialBinaryFormData_of_normalizedHankelData hdata)

theorem hasRankTwoNegativeSquareData_of_universalClassification_of_point
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u)
    (hclass : HasUniversalBinaryRankTwoNormalizedKernelClassification) :
    HasRankTwoNegativeSquareData B p u :=
  hasRankTwoNegativeSquareData_of_existentialNormalizedHankelData
    (hasRankTwoExistentialNormalizedHankelData_of_universalClassification_of_point
      (B := B) (p := p) (u := u) hu hp hfocp hclass)

theorem hasRankTwoNegativeSquareData_of_universalPureSquareTheorem_of_point
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u)
    (hpure : HasUniversalBinaryRankTwoNegativePureSquareTheorem) :
    HasRankTwoNegativeSquareData B p u := by
  intro hrank2 A W hAann hAW hAdim hWdim
  have hWpos : 0 < Module.finrank ℝ W := by omega
  rcases exists_mem_ne_zero_of_finrank_pos (K := ℝ) (V := linSubmodule)
      (s := W) hWpos with
    ⟨x, hxW, hxne⟩
  have hx : (x : Poly) ≠ 0 := by
    intro hzero
    exact hxne (Subtype.ext hzero)
  rcases exists_rank_two_complement_second_direction
      (W := W) (x := x) hx hWdim with
    ⟨y, hyW, hynot⟩
  have hneg :
      HasBinaryHankelNegativeValue
        (binaryRestrictionCoeffA B p u x)
        (binaryRestrictionCoeffB B p u x y)
        (binaryRestrictionCoeffC B p u x y)
        (binaryRestrictionCoeffD B p u x y)
        (binaryRestrictionCoeffE B p u y) :=
    hasRankTwoUniversalHankelNegativeData_of_point
      (B := B) (p := p) (u := u) hu hp hfocp
      hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim
  have hrank :
      Module.finrank ℝ
          (LinearMap.range
            (binaryHankelLinearMap
              (binaryRestrictionCoeffA B p u x)
              (binaryRestrictionCoeffB B p u x y)
              (binaryRestrictionCoeffC B p u x y)
              (binaryRestrictionCoeffD B p u x y)
              (binaryRestrictionCoeffE B p u y))) ≤ 2 :=
    universalBinaryHankelRankBound_of_catalecticantRankTwo
      hrank2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim
  rcases hpure
      (binaryRestrictionCoeffA B p u x)
      (binaryRestrictionCoeffB B p u x y)
      (binaryRestrictionCoeffC B p u x y)
      (binaryRestrictionCoeffD B p u x y)
      (binaryRestrictionCoeffE B p u y)
      hneg hrank with
    ⟨X, Y, hXYneg⟩
  let z : linSubmodule := X • x + Y • y
  have hzW : z ∈ W := by
    exact Submodule.add_mem W
      (Submodule.smul_mem W X hxW)
      (Submodule.smul_mem W Y hyW)
  have hzneg :
      B ((linProduct z z : quadSubmodule).1^2) (residual p u) < 0 := by
    change B ((linProduct (X • x + Y • y) (X • x + Y • y) :
        quadSubmodule).1^2) (residual p u) < 0
    rw [binaryRestriction_eval_eq B p u x y X Y]
    exact hXYneg
  have hz : (z : Poly) ≠ 0 := by
    intro hzero
    have hval_zero :
        B ((linProduct z z : quadSubmodule).1^2) (residual p u) = 0 := by
      simp [linProduct, hzero]
    linarith
  exact ⟨z, hzW, hz, hzneg⟩

theorem hasRankTwoNegativeSquareData_of_point
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u) :
    HasRankTwoNegativeSquareData B p u :=
  hasRankTwoNegativeSquareData_of_universalPureSquareTheorem_of_point
    (B := B) (p := p) (u := u) hu hp hfocp
    hasUniversalBinaryRankTwoNegativePureSquareTheorem_direct

theorem hasRankCaseNegativeSquareApolarData_of_annihilatorBounds_and_universalClassification_of_point
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u)
    (hbounds : HasRankCaseAnnihilatorMapBounds B p u)
    (hclass : HasUniversalBinaryRankTwoNormalizedKernelClassification) :
    HasRankCaseNegativeSquareApolarData B p u hu :=
  hasRankCaseNegativeSquareApolarData_of_annihilatorBounds_and_rankTwo
    (hu := hu) hbounds
    (hasRankTwoNegativeSquareData_of_universalClassification_of_point
      (B := B) (p := p) (u := u) hu hp hfocp hclass)

theorem hasRankCaseNegativeSquareApolarData_of_lowRankApolarSupportTheorem_and_universalClassification_of_point
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u)
    (hsupport : HasLowRankApolarSupportTheorem B p u)
    (hclass : HasUniversalBinaryRankTwoNormalizedKernelClassification) :
    HasRankCaseNegativeSquareApolarData B p u hu :=
  hasRankCaseNegativeSquareApolarData_of_annihilatorBounds_and_universalClassification_of_point
    (hu := hu) hp hfocp
    (hasRankCaseAnnihilatorMapBounds_of_lowRankApolarAnnihilatorMapTheorem
      (hasLowRankApolarAnnihilatorMapTheorem_of_supportTheorem hsupport))
    hclass

theorem hasRankCaseNegativeSquareApolarData_of_annihilatorBounds_and_universalPureSquareTheorem_of_point
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u)
    (hbounds : HasRankCaseAnnihilatorMapBounds B p u)
    (hpure : HasUniversalBinaryRankTwoNegativePureSquareTheorem) :
    HasRankCaseNegativeSquareApolarData B p u hu :=
  hasRankCaseNegativeSquareApolarData_of_annihilatorBounds_and_rankTwo
    (hu := hu) hbounds
    (hasRankTwoNegativeSquareData_of_universalPureSquareTheorem_of_point
      (B := B) (p := p) (u := u) hu hp hfocp hpure)

theorem hasRankCaseNegativeSquareApolarData_of_annihilatorBounds_of_point
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u)
    (hbounds : HasRankCaseAnnihilatorMapBounds B p u) :
    HasRankCaseNegativeSquareApolarData B p u hu :=
  hasRankCaseNegativeSquareApolarData_of_annihilatorBounds_and_rankTwo
    (hu := hu) hbounds
    (hasRankTwoNegativeSquareData_of_point
      (B := B) (p := p) (u := u) hu hp hfocp)

theorem hasRankCaseNegativeSquareApolarData_of_lowRankApolarSupportTheorem_and_universalPureSquareTheorem_of_point
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u)
    (hsupport : HasLowRankApolarSupportTheorem B p u)
    (hpure : HasUniversalBinaryRankTwoNegativePureSquareTheorem) :
    HasRankCaseNegativeSquareApolarData B p u hu :=
  hasRankCaseNegativeSquareApolarData_of_annihilatorBounds_and_universalPureSquareTheorem_of_point
    (hu := hu) hp hfocp
    (hasRankCaseAnnihilatorMapBounds_of_lowRankApolarAnnihilatorMapTheorem
      (hasLowRankApolarAnnihilatorMapTheorem_of_supportTheorem hsupport))
    hpure

theorem hasRankCaseNegativeSquareApolarData_of_lowRankApolarSupportTheorem_of_point
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u)
    (hsupport : HasLowRankApolarSupportTheorem B p u) :
    HasRankCaseNegativeSquareApolarData B p u hu :=
  hasRankCaseNegativeSquareApolarData_of_annihilatorBounds_of_point
    (hu := hu) hp hfocp
    (hasRankCaseAnnihilatorMapBounds_of_lowRankApolarAnnihilatorMapTheorem
      (hasLowRankApolarAnnihilatorMapTheorem_of_supportTheorem hsupport))

theorem hasRankTwoNegativeSquareData_of_universalNormalizedHankelData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hdata : HasRankTwoUniversalNormalizedHankelData B p u) :
    HasRankTwoNegativeSquareData B p u :=
  hasRankTwoNegativeSquareData_of_existentialNormalizedHankelData
    (hasRankTwoExistentialNormalizedHankelData_of_universalNormalizedHankelData hdata)

theorem hasRankTwoNegativeSquareData_of_universalKernelBranchData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hbranches : HasRankTwoUniversalKernelBranchData B p u) :
    HasRankTwoNegativeSquareData B p u :=
  hasRankTwoNegativeSquareData_of_universalNormalizedHankelData
    (hasRankTwoUniversalNormalizedHankelData_of_universalKernelBranchData hbranches)

theorem hasRankTwoNegativeSquareData_of_universalNormalizedPosition_of_point
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u)
    (hpos : HasRankTwoUniversalNormalizedKernelPositionData B p u) :
    HasRankTwoNegativeSquareData B p u :=
  hasRankTwoNegativeSquareData_of_universalNormalizedHankelData
    (hasRankTwoUniversalNormalizedHankelData_of_universalNormalizedPosition_of_point
      (B := B) (p := p) (u := u) hu hp hfocp hpos)

theorem hasRankTwoNegativeSquareData_of_universalKernelEquationData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hcases : HasRankTwoUniversalKernelEquationData B p u) :
    HasRankTwoNegativeSquareData B p u :=
  hasRankTwoNegativeSquareData_of_existentialBinaryFormData
    (hasRankTwoExistentialBinaryFormData_of_kernelEquationData
      (hasRankTwoExistentialKernelEquationData_of_universalKernelEquationData hcases))

theorem hasRankCaseNegativeSquareApolarData_of_annihilatorBounds_and_universalNormalizedPosition_of_point
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u)
    (hbounds : HasRankCaseAnnihilatorMapBounds B p u)
    (hpos : HasRankTwoUniversalNormalizedKernelPositionData B p u) :
    HasRankCaseNegativeSquareApolarData B p u hu :=
  hasRankCaseNegativeSquareApolarData_of_annihilatorBounds_and_rankTwo
    (hu := hu) hbounds
    (hasRankTwoNegativeSquareData_of_universalNormalizedPosition_of_point
      (B := B) (p := p) (u := u) hu hp hfocp hpos)

theorem hasRankCaseNegativeSquareApolarData_of_lowRankApolarAnnihilatorMapTheorem_and_universalNormalizedPosition_of_point
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u)
    (hann : HasLowRankApolarAnnihilatorMapTheorem B p u)
    (hpos : HasRankTwoUniversalNormalizedKernelPositionData B p u) :
    HasRankCaseNegativeSquareApolarData B p u hu :=
  hasRankCaseNegativeSquareApolarData_of_annihilatorBounds_and_universalNormalizedPosition_of_point
    (hu := hu) hp hfocp
    (hasRankCaseAnnihilatorMapBounds_of_lowRankApolarAnnihilatorMapTheorem hann)
    hpos

theorem hasRankCaseNegativeSquareApolarData_of_lowRankApolarSupportTheorem_and_universalNormalizedPosition_of_point
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u)
    (hsupport : HasLowRankApolarSupportTheorem B p u)
    (hpos : HasRankTwoUniversalNormalizedKernelPositionData B p u) :
    HasRankCaseNegativeSquareApolarData B p u hu :=
  hasRankCaseNegativeSquareApolarData_of_lowRankApolarAnnihilatorMapTheorem_and_universalNormalizedPosition_of_point
    (hu := hu) hp hfocp
    (hasLowRankApolarAnnihilatorMapTheorem_of_supportTheorem hsupport)
    hpos

theorem hasRankCaseNegativeSquareApolarData_of_annihilatorBounds_and_universalKernelEquationData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hbounds : HasRankCaseAnnihilatorMapBounds B p u)
    (hcases : HasRankTwoUniversalKernelEquationData B p u) :
    HasRankCaseNegativeSquareApolarData B p u hu :=
  hasRankCaseNegativeSquareApolarData_of_annihilatorBounds_and_rankTwo
    (hu := hu) hbounds
    (hasRankTwoNegativeSquareData_of_universalKernelEquationData hcases)

theorem hasRankCaseNegativeSquareApolarData_of_lowRankApolarAnnihilatorMapTheorem_and_universalKernelEquationData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hann : HasLowRankApolarAnnihilatorMapTheorem B p u)
    (hcases : HasRankTwoUniversalKernelEquationData B p u) :
    HasRankCaseNegativeSquareApolarData B p u hu :=
  hasRankCaseNegativeSquareApolarData_of_annihilatorBounds_and_universalKernelEquationData
    (hu := hu)
    (hasRankCaseAnnihilatorMapBounds_of_lowRankApolarAnnihilatorMapTheorem hann)
    hcases

theorem hasRankCaseNegativeSquareApolarData_of_lowRankApolarSupportTheorem_and_universalKernelEquationData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hsupport : HasLowRankApolarSupportTheorem B p u)
    (hcases : HasRankTwoUniversalKernelEquationData B p u) :
    HasRankCaseNegativeSquareApolarData B p u hu :=
  hasRankCaseNegativeSquareApolarData_of_lowRankApolarAnnihilatorMapTheorem_and_universalKernelEquationData
    (hu := hu)
    (hasLowRankApolarAnnihilatorMapTheorem_of_supportTheorem hsupport)
    hcases

theorem hasRankTwoExistentialKernelEquationData_of_kernelEquationApolarData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hdata : HasRankCaseKernelEquationApolarData B p u hu) :
    HasRankTwoExistentialKernelEquationData B p u := by
  intro hrank2 A W x hAann hAW hxW hx hAdim hWdim
  rcases hdata with ⟨_hdata1, hdata2, _hdata3⟩
  rcases exists_rank_two_complement_second_direction
      (W := W) (x := x) hx hWdim with
    ⟨y, hyW, hynot⟩
  exact ⟨y, hyW, hynot,
    (hdata2 hrank2).2 A W x y hAann hAW hxW hyW hynot hx hAdim hWdim⟩

theorem hasRankTwoExistentialCanonicalKernelData_of_kernelDecompositionApolarData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hdata : HasRankCaseKernelDecompositionApolarData B p u hu) :
    HasRankTwoExistentialCanonicalKernelData B p u :=
  hasRankTwoExistentialCanonicalKernelData_of_kernelEquationData
    (hasRankTwoExistentialKernelEquationData_of_kernelDecompositionApolarData hdata)

theorem hasRankTwoExistentialNormalizedHankelData_of_kernelDecompositionApolarData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hdata : HasRankCaseKernelDecompositionApolarData B p u hu) :
    HasRankTwoExistentialNormalizedHankelData B p u :=
  hasRankTwoExistentialNormalizedHankelData_of_kernelEquationData
    (hasRankTwoExistentialKernelEquationData_of_kernelDecompositionApolarData hdata)

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

theorem hasRankCaseNegativeCertificateFamily_of_negativeSquareApolarData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hfocp : IsFOCP B p u)
    (hdata : HasRankCaseNegativeSquareApolarData B p u hu) :
    HasRankCaseNegativeCertificateFamily B p u := by
  intro _hres hker
  rcases hdata with ⟨hdata1, hdata2, hdata3⟩
  constructor
  · intro hrank1
    have hsupp : HasLinearAnnihilatorCodimAtMost B p u 1 :=
      hasLinearAnnihilatorCodimAtMost_one_of_annihilatorMap_range
        (B := B) (p := p) (u := u) (hdata1 hrank1)
    rcases exists_rank_one_exact_annihilator_complement_generator
        (B := B) (p := p) (u := u) hsupp with
      ⟨A, W, x, hAann, hAW, hxW, hx, _hxnotA, _hxspan, hAdim, hWdim⟩
    have hneg : binaryRestrictionCoeffA B p u x < 0 :=
      rank_one_binaryRestrictionCoeffA_neg_of_annihilator_complement
        (B := B) (p := p) (u := u) hu hp hfocp hrank1
        hAann hAW hxW hx hWdim
    rcases exists_rank_one_combined_product_independence hAW hxW hx hAdim hWdim with
      ⟨β, hLI⟩
    have hSymLI :
        LinearIndependent ℝ
          (fun ij : {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} =>
            linProduct (β ij.1.1).1 (β ij.1.2).1) := by
      simpa [Function.comp_def] using (linearIndependent_sum.mp hLI).2.1
    have hSymdim : Module.finrank ℝ (symSquareSubmodule A) = 6 :=
      finrank_symSquareSubmodule_eq_six_of_basis_products_linearIndependent β hSymLI
    exact exists_negative_syzygyCertificate_of_rank_one_productSupportData
      (B := B) (p := p) (u := u) (hu := hu)
      (hasRankOneProductSupportData_of_annihilator_symSquare
        (B := B) (p := p) (u := u) (hu := hu)
        hfocp hker hrank1
        (x := x) (A := A)
        hx hAann hAdim hSymdim hneg)
  constructor
  · intro hrank2
    have hsupp : HasLinearAnnihilatorCodimAtMost B p u 2 :=
      hasLinearAnnihilatorCodimAtMost_two_of_annihilatorMap_range
        (B := B) (p := p) (u := u) (hdata2 hrank2).1
    rcases exists_rank_two_exact_annihilator_complement
        (B := B) (p := p) (u := u) hsupp with
      ⟨A, W, hAann, hAW, hAdim, hWdim⟩
    rcases (hdata2 hrank2).2 A W hAann hAW hAdim hWdim with
      ⟨x, hxW, hx, hneg⟩
    exact exists_negative_syzygyCertificate_of_preimageProductSupportData
      (B := B) (p := p) (u := u) (hu := hu)
      (hasPreimageProductSupportData_of_rank_two_negative_square
        (B := B) (p := p) (u := u) (hu := hu)
        hfocp hker hrank2
        hAann hAW hxW hx hAdim hWdim hneg)
  · intro hrank3
    have hsupp : HasLinearAnnihilatorCodimAtMost B p u 3 :=
      hasLinearAnnihilatorCodimAtMost_three_of_annihilatorMap_range
        (B := B) (p := p) (u := u) (hdata3 hrank3)
    rcases exists_negative_sos_summand_of_catalecticantMap_rank_eq_three
        (B := B) hu hp hfocp hrank3 with
      ⟨q, hq, hqneg⟩
    let qQuad : quadSubmodule := ⟨q, hq⟩
    rcases exists_rank_three_catalecticantKernel_decomposition
        (B := B) (p := p) (u := u) hsupp qQuad with
      ⟨W, qW, qK, hqdecomp, hqW, hqK⟩
    exact exists_negative_syzygyCertificate_of_rank_three_support
      (B := B) (p := p) (u := u) hu hfocp hker hrank3 hsupp hqW
      (residualEval_sq_lt_of_eq_add_mem_ker_catalecticantMap
        (B := B) (p := p) (u := u) hqdecomp hqK hqneg)

theorem residual_eq_zero_of_hasRankCaseNegativeCertificateFamily
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hcert : HasRankCaseNegativeCertificateFamily B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_rank_case_exists_negative_syzygy_certificate
    (B := B) hu hp hsocp hcert

theorem residual_eq_zero_of_negativeSquareApolarData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdata : HasRankCaseNegativeSquareApolarData B p u hu) :
    residual p u = 0 :=
  residual_eq_zero_of_hasRankCaseNegativeCertificateFamily
    (B := B) hu hp hsocp
    (hasRankCaseNegativeCertificateFamily_of_negativeSquareApolarData
      (B := B) hu hp hsocp.1 hdata)

theorem residual_eq_zero_of_annihilatorBounds_and_rankTwoNegativeSquare
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hbounds : HasRankCaseAnnihilatorMapBounds B p u)
    (hneg2 : HasRankTwoNegativeSquareData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_negativeSquareApolarData
    (B := B) hu hp hsocp
    (hasRankCaseNegativeSquareApolarData_of_annihilatorBounds_and_rankTwo
      (hu := hu) hbounds hneg2)

theorem residual_eq_zero_of_annihilatorBounds_and_binaryForms
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hbounds : HasRankCaseAnnihilatorMapBounds B p u)
    (hforms : HasRankTwoExistentialBinaryFormData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_negativeSquareApolarData
    (B := B) hu hp hsocp
    (hasRankCaseNegativeSquareApolarData_of_annihilatorBounds_and_binaryForms
      (hu := hu) hbounds hforms)

theorem residual_eq_zero_of_apolarSupportBounds_and_binaryForms
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hsupport : HasRankCaseApolarSupportBounds B p u)
    (hforms : HasRankTwoExistentialBinaryFormData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_negativeSquareApolarData
    (B := B) hu hp hsocp
    (hasRankCaseNegativeSquareApolarData_of_apolarSupportBounds_and_binaryForms
      (hu := hu) hsupport hforms)

theorem residual_eq_zero_of_apolarSupportBounds_and_kernelEquationCases
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hsupport : HasRankCaseApolarSupportBounds B p u)
    (hcases : HasRankTwoExistentialKernelEquationData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_apolarSupportBounds_and_binaryForms
    (B := B) hu hp hsocp hsupport
    (hasRankTwoExistentialBinaryFormData_of_kernelEquationData hcases)

theorem residual_eq_zero_of_apolarSupportBounds_and_universalKernelEquationData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hsupport : HasRankCaseApolarSupportBounds B p u)
    (hcases : HasRankTwoUniversalKernelEquationData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_apolarSupportBounds_and_kernelEquationCases
    (B := B) hu hp hsocp hsupport
    (hasRankTwoExistentialKernelEquationData_of_universalKernelEquationData hcases)

theorem residual_eq_zero_of_lowRankApolarSupportTheorem_and_universalKernelEquationData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hsupport : HasLowRankApolarSupportTheorem B p u)
    (hcases : HasRankTwoUniversalKernelEquationData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_apolarSupportBounds_and_universalKernelEquationData
    (B := B) hu hp hsocp
    (hasRankCaseApolarSupportBounds_of_lowRankApolarSupportTheorem hsupport)
    hcases

theorem residual_eq_zero_of_lowRankApolarAnnihilatorMapTheorem_and_universalKernelEquationData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hann : HasLowRankApolarAnnihilatorMapTheorem B p u)
    (hcases : HasRankTwoUniversalKernelEquationData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_lowRankApolarSupportTheorem_and_universalKernelEquationData
    (B := B) hu hp hsocp
    (hasLowRankApolarSupportTheorem_of_annihilatorMapTheorem hann)
    hcases

theorem residual_eq_zero_of_lowRankApolarSupportDecomposition_and_universalKernelEquationData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdecomp : HasLowRankApolarSupportDecomposition B p u)
    (hcases : HasRankTwoUniversalKernelEquationData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_lowRankApolarSupportTheorem_and_universalKernelEquationData
    (B := B) hu hp hsocp
    (hasLowRankApolarSupportTheorem_of_decomposition hdecomp)
    hcases

theorem residual_eq_zero_of_lowRankApolarProductKernelDecomposition_and_universalKernelEquationData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hprod : HasLowRankApolarProductKernelDecomposition B p u)
    (hcases : HasRankTwoUniversalKernelEquationData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_lowRankApolarSupportTheorem_and_universalKernelEquationData
    (B := B) hu hp hsocp
    (hasLowRankApolarSupportTheorem_of_productKernelDecomposition hprod)
    hcases

theorem residual_eq_zero_of_apolarSupportBounds_and_kernelBranches
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hsupport : HasRankCaseApolarSupportBounds B p u)
    (hbranches : HasRankTwoExistentialKernelBranchData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_apolarSupportBounds_and_binaryForms
    (B := B) hu hp hsocp hsupport
    (hasRankTwoExistentialBinaryFormData_of_kernelBranchData hbranches)

theorem residual_eq_zero_of_lowRankApolarSupportTheorem_and_kernelBranches
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hsupport : HasLowRankApolarSupportTheorem B p u)
    (hbranches : HasRankTwoExistentialKernelBranchData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_apolarSupportBounds_and_kernelBranches
    (B := B) hu hp hsocp
    (hasRankCaseApolarSupportBounds_of_lowRankApolarSupportTheorem hsupport)
    hbranches

theorem residual_eq_zero_of_lowRankApolarSupportDecomposition_and_kernelBranches
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdecomp : HasLowRankApolarSupportDecomposition B p u)
    (hbranches : HasRankTwoExistentialKernelBranchData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_lowRankApolarSupportTheorem_and_kernelBranches
    (B := B) hu hp hsocp
    (hasLowRankApolarSupportTheorem_of_decomposition hdecomp)
    hbranches

theorem residual_eq_zero_of_lowRankApolarSupportDecomposition_and_canonicalKernelData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdecomp : HasLowRankApolarSupportDecomposition B p u)
    (hcanon : HasRankTwoExistentialCanonicalKernelData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_lowRankApolarSupportDecomposition_and_kernelBranches
    (B := B) hu hp hsocp hdecomp
    (hasRankTwoExistentialKernelBranchData_of_canonicalKernelData hcanon)

theorem residual_eq_zero_of_lowRankApolarSupportTheorem_and_canonicalKernelData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hsupport : HasLowRankApolarSupportTheorem B p u)
    (hcanon : HasRankTwoExistentialCanonicalKernelData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_lowRankApolarSupportDecomposition_and_canonicalKernelData
    (B := B) hu hp hsocp
    (hasLowRankApolarSupportDecomposition_of_lowRankApolarSupportTheorem hsupport)
    hcanon

theorem residual_eq_zero_of_lowRankApolarAnnihilatorMapTheorem_and_canonicalKernelData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hann : HasLowRankApolarAnnihilatorMapTheorem B p u)
    (hcanon : HasRankTwoExistentialCanonicalKernelData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_lowRankApolarSupportTheorem_and_canonicalKernelData
    (B := B) hu hp hsocp
    (hasLowRankApolarSupportTheorem_of_annihilatorMapTheorem hann)
    hcanon

theorem residual_eq_zero_of_rankCaseAnnihilatorMapBounds_and_canonicalKernelData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hbounds : HasRankCaseAnnihilatorMapBounds B p u)
    (hcanon : HasRankTwoExistentialCanonicalKernelData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_lowRankApolarAnnihilatorMapTheorem_and_canonicalKernelData
    (B := B) hu hp hsocp
    (hasLowRankApolarAnnihilatorMapTheorem_of_rankCaseAnnihilatorMapBounds hbounds)
    hcanon

theorem residual_eq_zero_of_rankCaseAnnihilatorMapBounds_and_kernelEquationData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hbounds : HasRankCaseAnnihilatorMapBounds B p u)
    (hcases : HasRankTwoExistentialKernelEquationData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_rankCaseAnnihilatorMapBounds_and_canonicalKernelData
    (B := B) hu hp hsocp hbounds
    (hasRankTwoExistentialCanonicalKernelData_of_kernelEquationData hcases)

theorem residual_eq_zero_of_kernelEquationApolarData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdata : HasRankCaseKernelEquationApolarData B p u hu) :
    residual p u = 0 :=
  residual_eq_zero_of_rankCaseAnnihilatorMapBounds_and_kernelEquationData
    (B := B) hu hp hsocp
    (hasRankCaseAnnihilatorMapBounds_of_kernelEquationApolarData hdata)
    (hasRankTwoExistentialKernelEquationData_of_kernelEquationApolarData hdata)

theorem residual_eq_zero_of_annihilatorBounds_and_universalKernelEquationData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hbounds : HasRankCaseAnnihilatorMapBounds B p u)
    (hcases : HasRankTwoUniversalKernelEquationData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_rankCaseAnnihilatorMapBounds_and_kernelEquationData
    (B := B) hu hp hsocp
    hbounds
    (hasRankTwoExistentialKernelEquationData_of_universalKernelEquationData hcases)

theorem residual_eq_zero_of_annihilatorBounds_and_universalKernelBranchData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hbounds : HasRankCaseAnnihilatorMapBounds B p u)
    (hbranches : HasRankTwoUniversalKernelBranchData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_annihilatorBounds_and_universalKernelEquationData
    (B := B) hu hp hsocp hbounds
    (hasRankTwoUniversalKernelEquationData_of_universalKernelBranchData hbranches)

theorem residual_eq_zero_of_splitAnnihilatorBounds_and_universalKernelEquationData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hbound1 : HasRankOneApolarAnnihilatorMapBound B p u)
    (hbound2 : HasRankTwoApolarAnnihilatorMapBound B p u)
    (hbound3 : HasRankThreeApolarAnnihilatorMapBound B p u)
    (hcases : HasRankTwoUniversalKernelEquationData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_annihilatorBounds_and_universalKernelEquationData
    (B := B) hu hp hsocp
    (hasRankCaseAnnihilatorMapBounds_of_splitAnnihilatorMapBounds
      hbound1 hbound2 hbound3)
    hcases

theorem residual_eq_zero_of_splitAnnihilatorBounds_and_universalCanonicalKernelData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hbound1 : HasRankOneApolarAnnihilatorMapBound B p u)
    (hbound2 : HasRankTwoApolarAnnihilatorMapBound B p u)
    (hbound3 : HasRankThreeApolarAnnihilatorMapBound B p u)
    (hcanon : HasRankTwoUniversalCanonicalKernelData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_splitAnnihilatorBounds_and_universalKernelEquationData
    (B := B) hu hp hsocp hbound1 hbound2 hbound3
    (hasRankTwoUniversalKernelEquationData_of_universalCanonicalKernelData hcanon)

theorem residual_eq_zero_of_splitAnnihilatorBounds_and_universalNormalizedHankelData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hbound1 : HasRankOneApolarAnnihilatorMapBound B p u)
    (hbound2 : HasRankTwoApolarAnnihilatorMapBound B p u)
    (hbound3 : HasRankThreeApolarAnnihilatorMapBound B p u)
    (hdata : HasRankTwoUniversalNormalizedHankelData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_splitAnnihilatorBounds_and_universalCanonicalKernelData
    (B := B) hu hp hsocp hbound1 hbound2 hbound3
    (hasRankTwoUniversalCanonicalKernelData_of_universalNormalizedHankelData hdata)

theorem residual_eq_zero_of_annihilatorBounds_and_universalNormalizedHankelData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hbounds : HasRankCaseAnnihilatorMapBounds B p u)
    (hdata : HasRankTwoUniversalNormalizedHankelData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_annihilatorBounds_and_universalKernelBranchData
    (B := B) hu hp hsocp hbounds
    (hasRankTwoUniversalKernelBranchData_of_universalNormalizedHankelData hdata)

theorem residual_eq_zero_of_annihilatorBounds_and_universalNormalizedPosition_and_HankelNegative
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hbounds : HasRankCaseAnnihilatorMapBounds B p u)
    (hpos : HasRankTwoUniversalNormalizedKernelPositionData B p u)
    (hneg : HasRankTwoUniversalHankelNegativeData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_annihilatorBounds_and_universalNormalizedHankelData
    (B := B) hu hp hsocp hbounds
    (hasRankTwoUniversalNormalizedHankelData_of_universalNormalizedPosition_and_HankelNegative
      hpos hneg)

theorem residual_eq_zero_of_splitAnnihilatorBounds_and_universalNormalizedHankelComponents
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hbound1 : HasRankOneApolarAnnihilatorMapBound B p u)
    (hbound2 : HasRankTwoApolarAnnihilatorMapBound B p u)
    (hbound3 : HasRankThreeApolarAnnihilatorMapBound B p u)
    (hpos : HasRankTwoUniversalNormalizedKernelPositionData B p u)
    (hneg : HasRankTwoUniversalHankelNegativeData B p u)
    (hrank : HasRankTwoUniversalBinaryHankelRankBound B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_splitAnnihilatorBounds_and_universalNormalizedHankelData
    (B := B) hu hp hsocp hbound1 hbound2 hbound3
    (hasRankTwoUniversalNormalizedHankelData_of_components hpos hneg hrank)

theorem residual_eq_zero_of_splitAnnihilatorBounds_and_universalNormalizedPosition_and_HankelNegative
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hbound1 : HasRankOneApolarAnnihilatorMapBound B p u)
    (hbound2 : HasRankTwoApolarAnnihilatorMapBound B p u)
    (hbound3 : HasRankThreeApolarAnnihilatorMapBound B p u)
    (hpos : HasRankTwoUniversalNormalizedKernelPositionData B p u)
    (hneg : HasRankTwoUniversalHankelNegativeData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_splitAnnihilatorBounds_and_universalNormalizedHankelComponents
    (B := B) hu hp hsocp hbound1 hbound2 hbound3 hpos hneg
    (universalBinaryHankelRankBound_of_universalNormalizedKernelPositionData hpos)

theorem residual_eq_zero_of_annihilatorDimensionBounds_and_universalNormalizedPosition_and_HankelNegative
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdims : HasRankCaseApolarAnnihilatorDimensionBounds B p u)
    (hpos : HasRankTwoUniversalNormalizedKernelPositionData B p u)
    (hneg : HasRankTwoUniversalHankelNegativeData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_splitAnnihilatorBounds_and_universalNormalizedPosition_and_HankelNegative
    (B := B) hu hp hsocp
    (rankOneApolarAnnihilatorMapBound_of_rankOneDimensionBound hdims.1)
    (rankTwoApolarAnnihilatorMapBound_of_rankTwoDimensionBound hdims.2.1)
    (rankThreeApolarAnnihilatorMapBound_of_rankThreeDimensionBound hdims.2.2)
    hpos hneg

theorem residual_eq_zero_of_annihilatorDimensionBounds_and_universalKernelBranchData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdims : HasRankCaseApolarAnnihilatorDimensionBounds B p u)
    (hbranches : HasRankTwoUniversalKernelBranchData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_annihilatorBounds_and_universalKernelBranchData
    (B := B) hu hp hsocp
    (hasRankCaseAnnihilatorMapBounds_of_dimensionBounds hdims)
    hbranches

theorem residual_eq_zero_of_apolarSupportBounds_and_universalKernelBranchData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hsupport : HasRankCaseApolarSupportBounds B p u)
    (hbranches : HasRankTwoUniversalKernelBranchData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_annihilatorDimensionBounds_and_universalKernelBranchData
    (B := B) hu hp hsocp
    (hasRankCaseApolarAnnihilatorDimensionBounds_of_apolarSupportBounds hsupport)
    hbranches

theorem residual_eq_zero_of_lowRankApolarSupportTheorem_and_universalKernelBranchData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hsupport : HasLowRankApolarSupportTheorem B p u)
    (hbranches : HasRankTwoUniversalKernelBranchData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_apolarSupportBounds_and_universalKernelBranchData
    (B := B) hu hp hsocp
    (hasRankCaseApolarSupportBounds_of_lowRankApolarSupportTheorem hsupport)
    hbranches

theorem residual_eq_zero_of_lowRankApolarSupportDecomposition_and_universalKernelBranchData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdecomp : HasLowRankApolarSupportDecomposition B p u)
    (hbranches : HasRankTwoUniversalKernelBranchData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_lowRankApolarSupportTheorem_and_universalKernelBranchData
    (B := B) hu hp hsocp
    (hasLowRankApolarSupportTheorem_of_decomposition hdecomp)
    hbranches

theorem residual_eq_zero_of_apolarSupportBounds_and_universalNormalizedPosition_and_HankelNegative
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hsupport : HasRankCaseApolarSupportBounds B p u)
    (hpos : HasRankTwoUniversalNormalizedKernelPositionData B p u)
    (hneg : HasRankTwoUniversalHankelNegativeData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_annihilatorDimensionBounds_and_universalNormalizedPosition_and_HankelNegative
    (B := B) hu hp hsocp
    (hasRankCaseApolarAnnihilatorDimensionBounds_of_apolarSupportBounds hsupport)
    hpos hneg

theorem residual_eq_zero_of_lowRankApolarSupportTheorem_and_universalNormalizedPosition_and_HankelNegative
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hsupport : HasLowRankApolarSupportTheorem B p u)
    (hpos : HasRankTwoUniversalNormalizedKernelPositionData B p u)
    (hneg : HasRankTwoUniversalHankelNegativeData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_lowRankApolarSupportTheorem_and_universalKernelBranchData
    (B := B) hu hp hsocp hsupport
    (hasRankTwoUniversalKernelBranchData_of_universalNormalizedPosition_and_HankelNegative
      hpos hneg)

theorem residual_eq_zero_of_lowRankApolarSupportDecomposition_and_universalNormalizedPosition_and_HankelNegative
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdecomp : HasLowRankApolarSupportDecomposition B p u)
    (hpos : HasRankTwoUniversalNormalizedKernelPositionData B p u)
    (hneg : HasRankTwoUniversalHankelNegativeData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_lowRankApolarSupportTheorem_and_universalNormalizedPosition_and_HankelNegative
    (B := B) hu hp hsocp
    (hasLowRankApolarSupportTheorem_of_decomposition hdecomp)
    hpos hneg

theorem residual_eq_zero_of_apolarSupportBounds_and_universalNormalizedPosition
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hsupport : HasRankCaseApolarSupportBounds B p u)
    (hpos : HasRankTwoUniversalNormalizedKernelPositionData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_apolarSupportBounds_and_universalNormalizedPosition_and_HankelNegative
    (B := B) hu hp hsocp hsupport hpos
    (hasRankTwoUniversalHankelNegativeData_of_point
      (B := B) (p := p) (u := u) hu hp hsocp.1)

theorem residual_eq_zero_of_lowRankApolarSupportTheorem_and_universalNormalizedPosition
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hsupport : HasLowRankApolarSupportTheorem B p u)
    (hpos : HasRankTwoUniversalNormalizedKernelPositionData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_lowRankApolarSupportTheorem_and_universalNormalizedPosition_and_HankelNegative
    (B := B) hu hp hsocp hsupport hpos
    (hasRankTwoUniversalHankelNegativeData_of_point
      (B := B) (p := p) (u := u) hu hp hsocp.1)

theorem residual_eq_zero_of_lowRankApolarAnnihilatorMapTheorem_and_universalNormalizedPosition
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hann : HasLowRankApolarAnnihilatorMapTheorem B p u)
    (hpos : HasRankTwoUniversalNormalizedKernelPositionData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_lowRankApolarSupportTheorem_and_universalNormalizedPosition
    (B := B) hu hp hsocp
    (hasLowRankApolarSupportTheorem_of_annihilatorMapTheorem hann)
    hpos

theorem residual_eq_zero_of_lowRankApolarSupportDecomposition_and_universalNormalizedPosition
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdecomp : HasLowRankApolarSupportDecomposition B p u)
    (hpos : HasRankTwoUniversalNormalizedKernelPositionData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_lowRankApolarSupportDecomposition_and_universalNormalizedPosition_and_HankelNegative
    (B := B) hu hp hsocp hdecomp hpos
    (hasRankTwoUniversalHankelNegativeData_of_point
      (B := B) (p := p) (u := u) hu hp hsocp.1)

theorem residual_eq_zero_of_lowRankApolarProductKernelDecomposition_and_universalNormalizedPosition
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hprod : HasLowRankApolarProductKernelDecomposition B p u)
    (hpos : HasRankTwoUniversalNormalizedKernelPositionData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_lowRankApolarSupportDecomposition_and_universalNormalizedPosition
    (B := B) hu hp hsocp
    (hasLowRankApolarSupportDecomposition_of_productKernelDecomposition hprod)
    hpos

theorem residual_eq_zero_of_lowRankApolarSupportTheorem_and_universalNormalizedHankelData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hsupport : HasLowRankApolarSupportTheorem B p u)
    (hdata : HasRankTwoUniversalNormalizedHankelData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_lowRankApolarSupportTheorem_and_universalKernelBranchData
    (B := B) hu hp hsocp hsupport
    (hasRankTwoUniversalKernelBranchData_of_universalNormalizedHankelData hdata)

theorem residual_eq_zero_of_lowRankApolarSupportDecomposition_and_universalNormalizedHankelData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdecomp : HasLowRankApolarSupportDecomposition B p u)
    (hdata : HasRankTwoUniversalNormalizedHankelData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_lowRankApolarSupportTheorem_and_universalNormalizedHankelData
    (B := B) hu hp hsocp
    (hasLowRankApolarSupportTheorem_of_decomposition hdecomp)
    hdata

theorem residual_eq_zero_of_lowRankApolarProductKernelDecomposition_and_universalNormalizedHankelData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hprod : HasLowRankApolarProductKernelDecomposition B p u)
    (hdata : HasRankTwoUniversalNormalizedHankelData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_lowRankApolarSupportDecomposition_and_universalNormalizedHankelData
    (B := B) hu hp hsocp
    (hasLowRankApolarSupportDecomposition_of_productKernelDecomposition hprod)
    hdata

theorem residual_eq_zero_of_lowRankApolarProductKernelDecomposition_and_canonicalKernelData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hprod : HasLowRankApolarProductKernelDecomposition B p u)
    (hcanon : HasRankTwoExistentialCanonicalKernelData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_lowRankApolarSupportDecomposition_and_canonicalKernelData
    (B := B) hu hp hsocp
    (hasLowRankApolarSupportDecomposition_of_productKernelDecomposition hprod)
    hcanon

theorem residual_eq_zero_of_lowRankApolarProductKernelDecomposition_and_scalarHankelData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hprod : HasLowRankApolarProductKernelDecomposition B p u)
    (hscalar : HasRankTwoExistentialScalarHankelData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_lowRankApolarProductKernelDecomposition_and_canonicalKernelData
    (B := B) hu hp hsocp hprod
    (hasRankTwoExistentialCanonicalKernelData_of_scalarHankelData hscalar)

theorem residual_eq_zero_of_productKernelSupport_and_universalNormalizedBinaryClassification_and_scalarFacts
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hprod : HasLowRankApolarProductKernelDecomposition B p u)
    (hclass : HasUniversalBinaryRankTwoNormalizedKernelClassification)
    (hfacts : HasRankTwoExistentialScalarHankelFacts B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_lowRankApolarProductKernelDecomposition_and_scalarHankelData
    (B := B) hu hp hsocp hprod
    (hasRankTwoExistentialScalarHankelData_of_universal_and_facts hclass hfacts)

theorem residual_eq_zero_of_supportDecomposition_and_universalNormalizedBinaryClassification_and_scalarFacts
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdecomp : HasLowRankApolarSupportDecomposition B p u)
    (hclass : HasUniversalBinaryRankTwoNormalizedKernelClassification)
    (hfacts : HasRankTwoExistentialScalarHankelFacts B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_productKernelSupport_and_universalNormalizedBinaryClassification_and_scalarFacts
    (B := B) hu hp hsocp
    (hasLowRankApolarProductKernelDecomposition_of_supportDecomposition hdecomp)
    hclass hfacts

theorem residual_eq_zero_of_supportDecomposition_and_universalNormalizedBinaryClassification
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdecomp : HasLowRankApolarSupportDecomposition B p u)
    (hclass : HasUniversalBinaryRankTwoNormalizedKernelClassification) :
    residual p u = 0 :=
  residual_eq_zero_of_supportDecomposition_and_universalNormalizedBinaryClassification_and_scalarFacts
    (B := B) hu hp hsocp hdecomp hclass
    (hasRankTwoExistentialScalarHankelFacts_of_point
      (B := B) (p := p) (u := u) hu hp hsocp.1)

theorem residual_eq_zero_of_lowRankApolarSupportTheorem_and_universalNormalizedBinaryClassification
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hsupport : HasLowRankApolarSupportTheorem B p u)
    (hclass : HasUniversalBinaryRankTwoNormalizedKernelClassification) :
    residual p u = 0 :=
  residual_eq_zero_of_supportDecomposition_and_universalNormalizedBinaryClassification
    (B := B) hu hp hsocp
    (hasLowRankApolarSupportDecomposition_of_lowRankApolarSupportTheorem hsupport)
    hclass

theorem residual_eq_zero_of_lowRankApolarSupportTheorem_and_universalPureSquareTheorem
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hsupport : HasLowRankApolarSupportTheorem B p u)
    (hpure : HasUniversalBinaryRankTwoNegativePureSquareTheorem) :
    residual p u = 0 :=
  residual_eq_zero_of_negativeSquareApolarData
    (B := B) hu hp hsocp
    (hasRankCaseNegativeSquareApolarData_of_lowRankApolarSupportTheorem_and_universalPureSquareTheorem_of_point
      (B := B) (p := p) (u := u) (hu := hu) hp hsocp.1 hsupport hpure)

theorem residual_eq_zero_of_lowRankApolarSupportTheorem_direct
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hsupport : HasLowRankApolarSupportTheorem B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_negativeSquareApolarData
    (B := B) hu hp hsocp
    (hasRankCaseNegativeSquareApolarData_of_lowRankApolarSupportTheorem_of_point
      (B := B) (p := p) (u := u) (hu := hu) hp hsocp.1 hsupport)

theorem residual_eq_zero_of_lowRankApolarAnnihilatorMapTheorem_direct
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hann : HasLowRankApolarAnnihilatorMapTheorem B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_lowRankApolarSupportTheorem_direct
    (B := B) hu hp hsocp
    (hasLowRankApolarSupportTheorem_of_annihilatorMapTheorem hann)

theorem residual_eq_zero_of_rankCaseAnnihilatorMapBounds_direct
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hbounds : HasRankCaseAnnihilatorMapBounds B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_lowRankApolarAnnihilatorMapTheorem_direct
    (B := B) hu hp hsocp
    (hasLowRankApolarAnnihilatorMapTheorem_of_rankCaseAnnihilatorMapBounds hbounds)

theorem residual_eq_zero_of_annihilatorDimensionBounds_direct
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdims : HasRankCaseApolarAnnihilatorDimensionBounds B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_rankCaseAnnihilatorMapBounds_direct
    (B := B) hu hp hsocp
    (hasRankCaseAnnihilatorMapBounds_of_dimensionBounds hdims)

theorem residual_eq_zero_of_rankTwo_rankThreeApolarAnnihilatorMapBounds_direct
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hbound2 : HasRankTwoApolarAnnihilatorMapBound B p u)
    (hbound3 : HasRankThreeApolarAnnihilatorMapBound B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_rankCaseAnnihilatorMapBounds_direct
    (B := B) hu hp hsocp
    (hasRankCaseAnnihilatorMapBounds_of_rankTwo_rankThree hbound2 hbound3)

theorem residual_eq_zero_of_rankTwo_rankThreeApolarAnnihilatorDimensionBounds_direct
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdims : HasRankTwoThreeApolarAnnihilatorDimensionBounds B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_rankCaseAnnihilatorMapBounds_direct
    (B := B) hu hp hsocp
    (hasRankCaseAnnihilatorMapBounds_of_rankTwo_rankThreeDimensionBounds hdims)

theorem residual_eq_zero_of_rankTwo_rankThreeEssentialQuotientBounds_direct
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hquot2 : HasRankTwoApolarEssentialQuotientBound B p u)
    (hquot3 : HasRankThreeApolarEssentialQuotientBound B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_rankCaseAnnihilatorMapBounds_direct
    (B := B) hu hp hsocp
    (hasRankCaseAnnihilatorMapBounds_of_rankTwo_rankThreeEssentialQuotientBounds
      hquot2 hquot3)

theorem residual_eq_zero_of_lowRankApolarEssentialQuotientBounds_direct
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hquot : HasLowRankApolarEssentialQuotientBounds B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_rankTwo_rankThreeEssentialQuotientBounds_direct
    (B := B) hu hp hsocp hquot.1 hquot.2

theorem residual_eq_zero_of_lowRankApolarEssentialQuotientTheorem_direct
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hquot : HasLowRankApolarEssentialQuotientTheorem B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_lowRankApolarEssentialQuotientBounds_direct
    (B := B) hu hp hsocp
    (lowRankApolarEssentialQuotientBounds_of_theorem hquot)

theorem residual_eq_zero_of_rankTwoDimensionBound_rankThreeMacaulayObstruction_direct
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdim2 : HasRankTwoApolarAnnihilatorDimensionBound B p u)
    (hobstruction : HasRankThreeApolarMacaulayObstruction B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_rankCaseAnnihilatorMapBounds_direct
    (B := B) hu hp hsocp
    (hasRankCaseAnnihilatorMapBounds_of_rankTwoDimensionBound_rankThreeMacaulayObstruction
      hdim2 hobstruction)

theorem residual_eq_zero_of_rankTwoHilbertFirstBound_rankThreeMacaulayObstruction_direct
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hhilbert2 : HasRankTwoApolarHilbertFirstBound B p u)
    (hobstruction : HasRankThreeApolarMacaulayObstruction B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_rankCaseAnnihilatorMapBounds_direct
    (B := B) hu hp hsocp
    (hasRankCaseAnnihilatorMapBounds_of_rankTwoHilbertFirstBound_rankThreeMacaulayObstruction
      hhilbert2 hobstruction)

theorem residual_eq_zero_of_rankTwoMacaulayGrowthData_rankThreeMacaulayObstruction_direct
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdata2 : HasRankTwoApolarMacaulayGrowthData B p u)
    (hobstruction : HasRankThreeApolarMacaulayObstruction B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_rankCaseAnnihilatorMapBounds_direct
    (B := B) hu hp hsocp
    (hasRankCaseAnnihilatorMapBounds_of_rankTwoMacaulayGrowthData_rankThreeMacaulayObstruction
      hdata2 hobstruction)

theorem residual_eq_zero_of_rankTwoMacaulayGrowthData_rankThreeExactSequenceData_direct
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdata2 : HasRankTwoApolarMacaulayGrowthData B p u)
    (hdata3 : HasRankThreeApolarExactSequenceData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_rankCaseAnnihilatorMapBounds_direct
    (B := B) hu hp hsocp
    (hasRankCaseAnnihilatorMapBounds_of_rankTwoMacaulayGrowthData_rankThreeExactSequenceData
      hdata2 hdata3)

theorem residual_eq_zero_of_lowRankApolarHilbertData_direct
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdata : HasLowRankApolarHilbertData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_rankCaseAnnihilatorMapBounds_direct
    (B := B) hu hp hsocp
    (hasRankCaseAnnihilatorMapBounds_of_lowRankApolarHilbertData hdata)

theorem residual_eq_zero_of_lowRankApolarBlueprintHilbertData_direct
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdata : HasLowRankApolarBlueprintHilbertData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_lowRankApolarHilbertData_direct
    (B := B) hu hp hsocp
    (lowRankApolarHilbertData_of_lowRankApolarBlueprintHilbertData hdata)

theorem residual_eq_zero_of_lowRankApolarBlueprintLocalData_direct
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdata : HasLowRankApolarBlueprintLocalData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_lowRankApolarEssentialQuotientBounds_direct
    (B := B) hu hp hsocp
    (lowRankApolarEssentialQuotientBounds_of_lowRankApolarBlueprintLocalData hdata)

theorem residual_eq_zero_of_blueprintLocalComponents_direct
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hsymm2 : HasRankTwoApolarGorensteinSymmetryData B p u)
    (hgrowth2 : HasRankTwoApolarMacaulayGrowthBound B p u)
    (hshape3 : HasRankThreeApolarBadBranchExactSequenceShape B p u)
    (hmac3 : HasRankThreeApolarBadBranchMacaulayBound B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_lowRankApolarEssentialQuotientBounds_direct
    (B := B) hu hp hsocp
    (lowRankApolarEssentialQuotientBounds_of_rankTwoSymmetryAndGrowth_rankThreeShapeAndMacaulayBound
      hsymm2 hgrowth2 hshape3 hmac3)

theorem residual_eq_zero_of_lowRankApolarQuotientLocalData_direct
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdata : HasLowRankApolarQuotientLocalData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_lowRankApolarEssentialQuotientBounds_direct
    (B := B) hu hp hsocp
    (lowRankApolarEssentialQuotientBounds_of_lowRankApolarQuotientLocalData hdata)

theorem residual_eq_zero_of_lowRankApolarQuotientCoreData_direct
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdata : HasLowRankApolarQuotientCoreData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_lowRankApolarQuotientLocalData_direct
    (B := B) hu hp hsocp
    (lowRankApolarQuotientLocalData_of_coreData hdata)

theorem residual_eq_zero_of_quotientCoreComponents_direct
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hgrowth2 : HasRankTwoApolarMacaulayGrowthBound B p u)
    (hbad3 : HasRankThreeApolarBadBranchContradiction B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_lowRankApolarQuotientCoreData_direct
    (B := B) hu hp hsocp
    ⟨hgrowth2, hbad3⟩

theorem residual_eq_zero_of_quotientLocalComponents_direct
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hsymm2 : HasRankTwoApolarGorensteinSymmetryData B p u)
    (hgrowth2 : HasRankTwoApolarMacaulayGrowthBound B p u)
    (hbad3 : HasRankThreeApolarBadBranchContradiction B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_lowRankApolarEssentialQuotientBounds_direct
    (B := B) hu hp hsocp
    (lowRankApolarEssentialQuotientBounds_of_rankTwoSymmetryAndGrowth_rankThreeBadBranchContradiction
      hsymm2 hgrowth2 hbad3)

theorem residual_eq_zero_of_supportDecomposition_and_normalizedHankelData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdecomp : HasLowRankApolarSupportDecomposition B p u)
    (hdata : HasRankTwoExistentialNormalizedHankelData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_lowRankApolarSupportDecomposition_and_canonicalKernelData
    (B := B) hu hp hsocp hdecomp
    (hasRankTwoExistentialCanonicalKernelData_of_normalizedHankelData hdata)

theorem residual_eq_zero_of_supportDecomposition_and_universalNormalizedPosition_and_scalarFacts
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdecomp : HasLowRankApolarSupportDecomposition B p u)
    (hpos : HasRankTwoUniversalNormalizedKernelPositionData B p u)
    (hfacts : HasRankTwoExistentialScalarHankelFacts B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_supportDecomposition_and_normalizedHankelData
    (B := B) hu hp hsocp hdecomp
    (hasRankTwoExistentialNormalizedHankelData_of_universalNormalizedPosition_and_facts
      hpos hfacts)

theorem residual_eq_zero_of_lowRankApolarSupportTheorem_and_normalizedHankelData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hsupport : HasLowRankApolarSupportTheorem B p u)
    (hdata : HasRankTwoExistentialNormalizedHankelData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_supportDecomposition_and_normalizedHankelData
    (B := B) hu hp hsocp
    (hasLowRankApolarSupportDecomposition_of_lowRankApolarSupportTheorem hsupport)
    hdata

theorem residual_eq_zero_of_lowRankApolarSupportTheorem_and_universalNormalizedPosition_and_scalarFacts
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hsupport : HasLowRankApolarSupportTheorem B p u)
    (hpos : HasRankTwoUniversalNormalizedKernelPositionData B p u)
    (hfacts : HasRankTwoExistentialScalarHankelFacts B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_supportDecomposition_and_universalNormalizedPosition_and_scalarFacts
    (B := B) hu hp hsocp
    (hasLowRankApolarSupportDecomposition_of_lowRankApolarSupportTheorem hsupport)
    hpos hfacts

theorem residual_eq_zero_of_apolarSupportBounds_and_universalNormalizedPosition_and_scalarFacts
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hsupport : HasRankCaseApolarSupportBounds B p u)
    (hpos : HasRankTwoUniversalNormalizedKernelPositionData B p u)
    (hfacts : HasRankTwoExistentialScalarHankelFacts B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_lowRankApolarSupportTheorem_and_universalNormalizedPosition_and_scalarFacts
    (B := B) hu hp hsocp
    (hasLowRankApolarSupportTheorem_of_rankCaseApolarSupportBounds hsupport)
    hpos hfacts

theorem residual_eq_zero_of_lowRankApolarAnnihilatorMapTheorem_and_normalizedHankelData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hann : HasLowRankApolarAnnihilatorMapTheorem B p u)
    (hdata : HasRankTwoExistentialNormalizedHankelData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_lowRankApolarSupportTheorem_and_normalizedHankelData
    (B := B) hu hp hsocp
    (hasLowRankApolarSupportTheorem_of_annihilatorMapTheorem hann)
    hdata

theorem residual_eq_zero_of_rankCaseAnnihilatorMapBounds_and_normalizedHankelData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hbounds : HasRankCaseAnnihilatorMapBounds B p u)
    (hdata : HasRankTwoExistentialNormalizedHankelData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_lowRankApolarAnnihilatorMapTheorem_and_normalizedHankelData
    (B := B) hu hp hsocp
    (hasLowRankApolarAnnihilatorMapTheorem_of_rankCaseAnnihilatorMapBounds hbounds)
    hdata

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

theorem residual_eq_zero_of_productIndependenceApolarData_via_kernelEquationData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdata : HasRankCaseProductIndependenceApolarData B p u hu) :
    residual p u = 0 :=
  residual_eq_zero_of_kernelEquationApolarData
    (B := B) hu hp hsocp
    (hasRankCaseKernelEquationApolarData_of_productIndependenceApolarData hdata)

theorem residual_eq_zero_of_productIndependenceGeometryData_and_universalKernelBranchData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hgeom : HasRankCaseProductIndependenceGeometryData B p u hu)
    (hbranches : HasRankTwoUniversalKernelBranchData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_rankCaseApolarComponentData
    (B := B) hu hp hsocp
    (hasRankCaseApolarComponentData_of_productIndependenceGeometryData_and_universalKernelBranchData
      hgeom hbranches)

theorem residual_eq_zero_of_productIndependenceGeometryData_and_universalNormalizedHankelData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hgeom : HasRankCaseProductIndependenceGeometryData B p u hu)
    (hdata : HasRankTwoUniversalNormalizedHankelData B p u) :
    residual p u = 0 :=
  residual_eq_zero_of_productIndependenceGeometryData_and_universalKernelBranchData
    (B := B) hu hp hsocp hgeom
    (hasRankTwoUniversalKernelBranchData_of_universalNormalizedHankelData hdata)

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

theorem residual_eq_zero_of_productFreeApolarData_via_kernelEquationData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdata : HasRankCaseProductFreeApolarData B p u hu) :
    residual p u = 0 :=
  residual_eq_zero_of_kernelEquationApolarData
    (B := B) hu hp hsocp
    (hasRankCaseKernelEquationApolarData_of_productFreeApolarData hdata)

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

theorem residual_eq_zero_of_rankOneFreeApolarData_via_kernelEquationData
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hdata : HasRankCaseRankOneFreeApolarData B p u hu) :
    residual p u = 0 :=
  residual_eq_zero_of_kernelEquationApolarData
    (B := B) hu hp hsocp
    (hasRankCaseKernelEquationApolarData_of_rankOneFreeApolarData hdata)

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
  residual_eq_zero_of_negativeSquareApolarData
    (B := B) hu hp hsocp
    (hasRankCaseNegativeSquareApolarData_of_existentialBinaryFormData hdata)

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

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_negativeSquareApolarData
    (hdata :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseNegativeSquareApolarData B p u hu) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_negativeSquareApolarData
    (B := B) hu hp hsocp (hdata B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_annihilatorBounds_and_rankTwo
    (hbounds :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseAnnihilatorMapBounds B p u)
    (hneg2 :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoNegativeSquareData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_annihilatorBounds_and_rankTwoNegativeSquare
    (B := B) hu hp hsocp
    (hbounds B p u hu hB hp hsocp)
    (hneg2 B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_annihilatorBounds_and_binaryForms
    (hbounds :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseAnnihilatorMapBounds B p u)
    (hforms :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoExistentialBinaryFormData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_annihilatorBounds_and_binaryForms
    (B := B) hu hp hsocp
    (hbounds B p u hu hB hp hsocp)
    (hforms B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_apolarSupportBounds_and_binaryForms
    (hsupport :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseApolarSupportBounds B p u)
    (hforms :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoExistentialBinaryFormData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_apolarSupportBounds_and_binaryForms
    (B := B) hu hp hsocp
    (hsupport B p u hu hB hp hsocp)
    (hforms B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_apolarSupportBounds_and_kernelEquationCases
    (hsupport :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseApolarSupportBounds B p u)
    (hcases :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoExistentialKernelEquationData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_apolarSupportBounds_and_kernelEquationCases
    (B := B) hu hp hsocp
    (hsupport B p u hu hB hp hsocp)
    (hcases B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_apolarSupportBounds_and_universalKernelEquationData
    (hsupport :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseApolarSupportBounds B p u)
    (hcases :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalKernelEquationData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_apolarSupportBounds_and_universalKernelEquationData
    (B := B) hu hp hsocp
    (hsupport B p u hu hB hp hsocp)
    (hcases B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarSupportTheorem_and_universalKernelEquationData
    (hsupport :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarSupportTheorem B p u)
    (hcases :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalKernelEquationData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_lowRankApolarSupportTheorem_and_universalKernelEquationData
    (B := B) hu hp hsocp
    (hsupport B p u hu hB hp hsocp)
    (hcases B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarAnnihilatorMapTheorem_and_universalKernelEquationData
    (hann :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarAnnihilatorMapTheorem B p u)
    (hcases :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalKernelEquationData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_lowRankApolarAnnihilatorMapTheorem_and_universalKernelEquationData
    (B := B) hu hp hsocp
    (hann B p u hu hB hp hsocp)
    (hcases B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarSupportDecomposition_and_universalKernelEquationData
    (hdecomp :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarSupportDecomposition B p u)
    (hcases :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalKernelEquationData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_lowRankApolarSupportDecomposition_and_universalKernelEquationData
    (B := B) hu hp hsocp
    (hdecomp B p u hu hB hp hsocp)
    (hcases B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarProductKernelDecomposition_and_universalKernelEquationData
    (hprod :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarProductKernelDecomposition B p u)
    (hcases :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalKernelEquationData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_lowRankApolarProductKernelDecomposition_and_universalKernelEquationData
    (B := B) hu hp hsocp
    (hprod B p u hu hB hp hsocp)
    (hcases B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_apolarSupportBounds_and_kernelBranches
    (hsupport :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseApolarSupportBounds B p u)
    (hbranches :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoExistentialKernelBranchData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_apolarSupportBounds_and_kernelBranches
    (B := B) hu hp hsocp
    (hsupport B p u hu hB hp hsocp)
    (hbranches B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarSupportTheorem_and_kernelBranches
    (hsupport :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarSupportTheorem B p u)
    (hbranches :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoExistentialKernelBranchData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_lowRankApolarSupportTheorem_and_kernelBranches
    (B := B) hu hp hsocp
    (hsupport B p u hu hB hp hsocp)
    (hbranches B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarSupportDecomposition_and_kernelBranches
    (hdecomp :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarSupportDecomposition B p u)
    (hbranches :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoExistentialKernelBranchData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_lowRankApolarSupportDecomposition_and_kernelBranches
    (B := B) hu hp hsocp
    (hdecomp B p u hu hB hp hsocp)
    (hbranches B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarSupportDecomposition_and_canonicalKernelData
    (hdecomp :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarSupportDecomposition B p u)
    (hcanon :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoExistentialCanonicalKernelData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_lowRankApolarSupportDecomposition_and_canonicalKernelData
    (B := B) hu hp hsocp
    (hdecomp B p u hu hB hp hsocp)
    (hcanon B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarSupportTheorem_and_canonicalKernelData
    (hsupport :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarSupportTheorem B p u)
    (hcanon :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoExistentialCanonicalKernelData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_lowRankApolarSupportTheorem_and_canonicalKernelData
    (B := B) hu hp hsocp
    (hsupport B p u hu hB hp hsocp)
    (hcanon B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarAnnihilatorMapTheorem_and_canonicalKernelData
    (hann :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarAnnihilatorMapTheorem B p u)
    (hcanon :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoExistentialCanonicalKernelData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_lowRankApolarAnnihilatorMapTheorem_and_canonicalKernelData
    (B := B) hu hp hsocp
    (hann B p u hu hB hp hsocp)
    (hcanon B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_rankCaseAnnihilatorMapBounds_and_canonicalKernelData
    (hbounds :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseAnnihilatorMapBounds B p u)
    (hcanon :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoExistentialCanonicalKernelData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_rankCaseAnnihilatorMapBounds_and_canonicalKernelData
    (B := B) hu hp hsocp
    (hbounds B p u hu hB hp hsocp)
    (hcanon B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_rankCaseAnnihilatorMapBounds_and_kernelEquationData
    (hbounds :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseAnnihilatorMapBounds B p u)
    (hcases :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoExistentialKernelEquationData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_rankCaseAnnihilatorMapBounds_and_kernelEquationData
    (B := B) hu hp hsocp
    (hbounds B p u hu hB hp hsocp)
    (hcases B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_kernelEquationApolarData
    (hdata :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseKernelEquationApolarData B p u hu) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_kernelEquationApolarData
    (B := B) hu hp hsocp (hdata B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_annihilatorBounds_and_universalKernelEquationData
    (hbounds :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseAnnihilatorMapBounds B p u)
    (hcases :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalKernelEquationData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_annihilatorBounds_and_universalKernelEquationData
    (B := B) hu hp hsocp
    (hbounds B p u hu hB hp hsocp)
    (hcases B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_annihilatorBounds_and_universalKernelBranchData
    (hbounds :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseAnnihilatorMapBounds B p u)
    (hbranches :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalKernelBranchData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_annihilatorBounds_and_universalKernelBranchData
    (B := B) hu hp hsocp
    (hbounds B p u hu hB hp hsocp)
    (hbranches B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_splitAnnihilatorBounds_and_universalKernelEquationData
    (hbound1 :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankOneApolarAnnihilatorMapBound B p u)
    (hbound2 :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoApolarAnnihilatorMapBound B p u)
    (hbound3 :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankThreeApolarAnnihilatorMapBound B p u)
    (hcases :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalKernelEquationData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_splitAnnihilatorBounds_and_universalKernelEquationData
    (B := B) hu hp hsocp
    (hbound1 B p u hu hB hp hsocp)
    (hbound2 B p u hu hB hp hsocp)
    (hbound3 B p u hu hB hp hsocp)
    (hcases B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_splitAnnihilatorBounds_and_universalCanonicalKernelData
    (hbound1 :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankOneApolarAnnihilatorMapBound B p u)
    (hbound2 :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoApolarAnnihilatorMapBound B p u)
    (hbound3 :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankThreeApolarAnnihilatorMapBound B p u)
    (hcanon :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalCanonicalKernelData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_splitAnnihilatorBounds_and_universalCanonicalKernelData
    (B := B) hu hp hsocp
    (hbound1 B p u hu hB hp hsocp)
    (hbound2 B p u hu hB hp hsocp)
    (hbound3 B p u hu hB hp hsocp)
    (hcanon B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_splitAnnihilatorBounds_and_universalNormalizedHankelData
    (hbound1 :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankOneApolarAnnihilatorMapBound B p u)
    (hbound2 :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoApolarAnnihilatorMapBound B p u)
    (hbound3 :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankThreeApolarAnnihilatorMapBound B p u)
    (hdata :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalNormalizedHankelData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_splitAnnihilatorBounds_and_universalNormalizedHankelData
    (B := B) hu hp hsocp
    (hbound1 B p u hu hB hp hsocp)
    (hbound2 B p u hu hB hp hsocp)
    (hbound3 B p u hu hB hp hsocp)
    (hdata B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_annihilatorBounds_and_universalNormalizedHankelData
    (hbounds :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseAnnihilatorMapBounds B p u)
    (hdata :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalNormalizedHankelData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_annihilatorBounds_and_universalNormalizedHankelData
    (B := B) hu hp hsocp
    (hbounds B p u hu hB hp hsocp)
    (hdata B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_annihilatorBounds_and_universalNormalizedPosition_and_HankelNegative
    (hbounds :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseAnnihilatorMapBounds B p u)
    (hpos :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalNormalizedKernelPositionData B p u)
    (hneg :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalHankelNegativeData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_annihilatorBounds_and_universalNormalizedPosition_and_HankelNegative
    (B := B) hu hp hsocp
    (hbounds B p u hu hB hp hsocp)
    (hpos B p u hu hB hp hsocp)
    (hneg B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_splitAnnihilatorBounds_and_universalNormalizedHankelComponents
    (hbound1 :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankOneApolarAnnihilatorMapBound B p u)
    (hbound2 :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoApolarAnnihilatorMapBound B p u)
    (hbound3 :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankThreeApolarAnnihilatorMapBound B p u)
    (hpos :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalNormalizedKernelPositionData B p u)
    (hneg :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalHankelNegativeData B p u)
    (hrank :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalBinaryHankelRankBound B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_splitAnnihilatorBounds_and_universalNormalizedHankelComponents
    (B := B) hu hp hsocp
    (hbound1 B p u hu hB hp hsocp)
    (hbound2 B p u hu hB hp hsocp)
    (hbound3 B p u hu hB hp hsocp)
    (hpos B p u hu hB hp hsocp)
    (hneg B p u hu hB hp hsocp)
    (hrank B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_splitAnnihilatorBounds_and_universalNormalizedPosition_and_HankelNegative
    (hbound1 :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankOneApolarAnnihilatorMapBound B p u)
    (hbound2 :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoApolarAnnihilatorMapBound B p u)
    (hbound3 :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankThreeApolarAnnihilatorMapBound B p u)
    (hpos :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalNormalizedKernelPositionData B p u)
    (hneg :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalHankelNegativeData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact
    residual_eq_zero_of_splitAnnihilatorBounds_and_universalNormalizedPosition_and_HankelNegative
      (B := B) hu hp hsocp
      (hbound1 B p u hu hB hp hsocp)
      (hbound2 B p u hu hB hp hsocp)
      (hbound3 B p u hu hB hp hsocp)
      (hpos B p u hu hB hp hsocp)
      (hneg B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_annihilatorDimensionBounds_and_universalNormalizedPosition_and_HankelNegative
    (hdims :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseApolarAnnihilatorDimensionBounds B p u)
    (hpos :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalNormalizedKernelPositionData B p u)
    (hneg :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalHankelNegativeData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact
    residual_eq_zero_of_annihilatorDimensionBounds_and_universalNormalizedPosition_and_HankelNegative
      (B := B) hu hp hsocp
      (hdims B p u hu hB hp hsocp)
      (hpos B p u hu hB hp hsocp)
      (hneg B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_annihilatorDimensionBounds_and_universalKernelBranchData
    (hdims :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseApolarAnnihilatorDimensionBounds B p u)
    (hbranches :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalKernelBranchData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_annihilatorDimensionBounds_and_universalKernelBranchData
    (B := B) hu hp hsocp
    (hdims B p u hu hB hp hsocp)
    (hbranches B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_apolarSupportBounds_and_universalKernelBranchData
    (hsupport :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseApolarSupportBounds B p u)
    (hbranches :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalKernelBranchData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_apolarSupportBounds_and_universalKernelBranchData
    (B := B) hu hp hsocp
    (hsupport B p u hu hB hp hsocp)
    (hbranches B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarSupportTheorem_and_universalKernelBranchData
    (hsupport :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarSupportTheorem B p u)
    (hbranches :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalKernelBranchData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_lowRankApolarSupportTheorem_and_universalKernelBranchData
    (B := B) hu hp hsocp
    (hsupport B p u hu hB hp hsocp)
    (hbranches B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarSupportDecomposition_and_universalKernelBranchData
    (hdecomp :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarSupportDecomposition B p u)
    (hbranches :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalKernelBranchData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_lowRankApolarSupportDecomposition_and_universalKernelBranchData
    (B := B) hu hp hsocp
    (hdecomp B p u hu hB hp hsocp)
    (hbranches B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_apolarSupportBounds_and_universalNormalizedPosition_and_HankelNegative
    (hsupport :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseApolarSupportBounds B p u)
    (hpos :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalNormalizedKernelPositionData B p u)
    (hneg :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalHankelNegativeData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact
    residual_eq_zero_of_apolarSupportBounds_and_universalNormalizedPosition_and_HankelNegative
      (B := B) hu hp hsocp
      (hsupport B p u hu hB hp hsocp)
      (hpos B p u hu hB hp hsocp)
      (hneg B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarSupportTheorem_and_universalNormalizedPosition_and_HankelNegative
    (hsupport :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarSupportTheorem B p u)
    (hpos :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalNormalizedKernelPositionData B p u)
    (hneg :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalHankelNegativeData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact
    residual_eq_zero_of_lowRankApolarSupportTheorem_and_universalNormalizedPosition_and_HankelNegative
      (B := B) hu hp hsocp
      (hsupport B p u hu hB hp hsocp)
      (hpos B p u hu hB hp hsocp)
      (hneg B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarSupportDecomposition_and_universalNormalizedPosition_and_HankelNegative
    (hdecomp :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarSupportDecomposition B p u)
    (hpos :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalNormalizedKernelPositionData B p u)
    (hneg :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalHankelNegativeData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact
    residual_eq_zero_of_lowRankApolarSupportDecomposition_and_universalNormalizedPosition_and_HankelNegative
      (B := B) hu hp hsocp
      (hdecomp B p u hu hB hp hsocp)
      (hpos B p u hu hB hp hsocp)
      (hneg B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_apolarSupportBounds_and_universalNormalizedPosition
    (hsupport :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseApolarSupportBounds B p u)
    (hpos :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalNormalizedKernelPositionData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact
    residual_eq_zero_of_apolarSupportBounds_and_universalNormalizedPosition
      (B := B) hu hp hsocp
      (hsupport B p u hu hB hp hsocp)
      (hpos B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarSupportTheorem_and_universalNormalizedPosition
    (hsupport :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarSupportTheorem B p u)
    (hpos :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalNormalizedKernelPositionData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact
    residual_eq_zero_of_lowRankApolarSupportTheorem_and_universalNormalizedPosition
      (B := B) hu hp hsocp
    (hsupport B p u hu hB hp hsocp)
    (hpos B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarAnnihilatorMapTheorem_and_universalNormalizedPosition
    (hann :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarAnnihilatorMapTheorem B p u)
    (hpos :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalNormalizedKernelPositionData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_lowRankApolarAnnihilatorMapTheorem_and_universalNormalizedPosition
    (B := B) hu hp hsocp
    (hann B p u hu hB hp hsocp)
    (hpos B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarSupportDecomposition_and_universalNormalizedPosition
    (hdecomp :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarSupportDecomposition B p u)
    (hpos :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalNormalizedKernelPositionData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact
    residual_eq_zero_of_lowRankApolarSupportDecomposition_and_universalNormalizedPosition
    (B := B) hu hp hsocp
    (hdecomp B p u hu hB hp hsocp)
    (hpos B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarProductKernelDecomposition_and_universalNormalizedPosition
    (hprod :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarProductKernelDecomposition B p u)
    (hpos :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalNormalizedKernelPositionData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_lowRankApolarProductKernelDecomposition_and_universalNormalizedPosition
    (B := B) hu hp hsocp
    (hprod B p u hu hB hp hsocp)
    (hpos B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarSupportTheorem_and_universalNormalizedHankelData
    (hsupport :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarSupportTheorem B p u)
    (hdata :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalNormalizedHankelData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_lowRankApolarSupportTheorem_and_universalNormalizedHankelData
    (B := B) hu hp hsocp
    (hsupport B p u hu hB hp hsocp)
    (hdata B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarSupportDecomposition_and_universalNormalizedHankelData
    (hdecomp :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarSupportDecomposition B p u)
    (hdata :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalNormalizedHankelData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_lowRankApolarSupportDecomposition_and_universalNormalizedHankelData
    (B := B) hu hp hsocp
    (hdecomp B p u hu hB hp hsocp)
    (hdata B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarProductKernelDecomposition_and_universalNormalizedHankelData
    (hprod :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarProductKernelDecomposition B p u)
    (hdata :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalNormalizedHankelData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_lowRankApolarProductKernelDecomposition_and_universalNormalizedHankelData
    (B := B) hu hp hsocp
    (hprod B p u hu hB hp hsocp)
    (hdata B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarProductKernelDecomposition_and_canonicalKernelData
    (hprod :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarProductKernelDecomposition B p u)
    (hcanon :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoExistentialCanonicalKernelData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_lowRankApolarProductKernelDecomposition_and_canonicalKernelData
    (B := B) hu hp hsocp
    (hprod B p u hu hB hp hsocp)
    (hcanon B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarProductKernelDecomposition_and_scalarHankelData
    (hprod :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarProductKernelDecomposition B p u)
    (hscalar :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoExistentialScalarHankelData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_lowRankApolarProductKernelDecomposition_and_scalarHankelData
    (B := B) hu hp hsocp
    (hprod B p u hu hB hp hsocp)
    (hscalar B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_productKernelSupport_and_universalNormalizedBinaryClassification_and_scalarFacts
    (hprod :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarProductKernelDecomposition B p u)
    (hclass : HasUniversalBinaryRankTwoNormalizedKernelClassification)
    (hfacts :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoExistentialScalarHankelFacts B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_productKernelSupport_and_universalNormalizedBinaryClassification_and_scalarFacts
    (B := B) hu hp hsocp
    (hprod B p u hu hB hp hsocp)
    hclass
    (hfacts B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_supportDecomposition_and_universalNormalizedBinaryClassification_and_scalarFacts
    (hdecomp :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarSupportDecomposition B p u)
    (hclass : HasUniversalBinaryRankTwoNormalizedKernelClassification)
    (hfacts :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoExistentialScalarHankelFacts B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_supportDecomposition_and_universalNormalizedBinaryClassification_and_scalarFacts
    (B := B) hu hp hsocp
    (hdecomp B p u hu hB hp hsocp)
    hclass
    (hfacts B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_supportDecomposition_and_universalNormalizedBinaryClassification
    (hdecomp :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarSupportDecomposition B p u)
    (hclass : HasUniversalBinaryRankTwoNormalizedKernelClassification) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_supportDecomposition_and_universalNormalizedBinaryClassification
    (B := B) hu hp hsocp
    (hdecomp B p u hu hB hp hsocp)
    hclass

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_supportDecomposition_and_normalizedHankelData
    (hdecomp :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarSupportDecomposition B p u)
    (hdata :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoExistentialNormalizedHankelData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_supportDecomposition_and_normalizedHankelData
    (B := B) hu hp hsocp
    (hdecomp B p u hu hB hp hsocp)
    (hdata B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_supportDecomposition_and_universalNormalizedPosition_and_scalarFacts
    (hdecomp :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarSupportDecomposition B p u)
    (hpos :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalNormalizedKernelPositionData B p u)
    (hfacts :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoExistentialScalarHankelFacts B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_supportDecomposition_and_universalNormalizedPosition_and_scalarFacts
    (B := B) hu hp hsocp
    (hdecomp B p u hu hB hp hsocp)
    (hpos B p u hu hB hp hsocp)
    (hfacts B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarSupportTheorem_and_normalizedHankelData
    (hsupport :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarSupportTheorem B p u)
    (hdata :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoExistentialNormalizedHankelData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_lowRankApolarSupportTheorem_and_normalizedHankelData
    (B := B) hu hp hsocp
    (hsupport B p u hu hB hp hsocp)
    (hdata B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarSupportTheorem_and_universalNormalizedBinaryClassification
    (hsupport :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarSupportTheorem B p u)
    (hclass : HasUniversalBinaryRankTwoNormalizedKernelClassification) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_lowRankApolarSupportTheorem_and_universalNormalizedBinaryClassification
    (B := B) hu hp hsocp
    (hsupport B p u hu hB hp hsocp)
    hclass

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarSupportTheorem_and_universalPureSquareTheorem
    (hsupport :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarSupportTheorem B p u)
    (hpure : HasUniversalBinaryRankTwoNegativePureSquareTheorem) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_lowRankApolarSupportTheorem_and_universalPureSquareTheorem
    (B := B) hu hp hsocp
    (hsupport B p u hu hB hp hsocp)
    hpure

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarSupportTheorem_direct
    (hsupport :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarSupportTheorem B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_lowRankApolarSupportTheorem_direct
    (B := B) hu hp hsocp
    (hsupport B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarAnnihilatorMapTheorem_direct
    (hann :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarAnnihilatorMapTheorem B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_lowRankApolarAnnihilatorMapTheorem_direct
    (B := B) hu hp hsocp
    (hann B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_rankCaseAnnihilatorMapBounds_direct
    (hbounds :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseAnnihilatorMapBounds B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_rankCaseAnnihilatorMapBounds_direct
    (B := B) hu hp hsocp
    (hbounds B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_annihilatorDimensionBounds_direct
    (hdims :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseApolarAnnihilatorDimensionBounds B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_annihilatorDimensionBounds_direct
    (B := B) hu hp hsocp
    (hdims B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_rankTwo_rankThreeApolarAnnihilatorMapBounds_direct
    (hbound2 :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoApolarAnnihilatorMapBound B p u)
    (hbound3 :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankThreeApolarAnnihilatorMapBound B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_rankTwo_rankThreeApolarAnnihilatorMapBounds_direct
    (B := B) hu hp hsocp
    (hbound2 B p u hu hB hp hsocp)
    (hbound3 B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_rankTwo_rankThreeApolarAnnihilatorDimensionBounds_direct
    (hdims :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoThreeApolarAnnihilatorDimensionBounds B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_rankTwo_rankThreeApolarAnnihilatorDimensionBounds_direct
    (B := B) hu hp hsocp
    (hdims B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_rankTwo_rankThreeEssentialQuotientBounds_direct
    (hquot2 :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoApolarEssentialQuotientBound B p u)
    (hquot3 :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankThreeApolarEssentialQuotientBound B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_rankTwo_rankThreeEssentialQuotientBounds_direct
    (B := B) hu hp hsocp
    (hquot2 B p u hu hB hp hsocp)
    (hquot3 B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarEssentialQuotientBounds_direct
    (hquot :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarEssentialQuotientBounds B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_lowRankApolarEssentialQuotientBounds_direct
    (B := B) hu hp hsocp
    (hquot B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarEssentialQuotientTheorem_direct
    (hquot :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarEssentialQuotientTheorem B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_lowRankApolarEssentialQuotientTheorem_direct
    (B := B) hu hp hsocp
    (hquot B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_rankTwoDimensionBound_rankThreeMacaulayObstruction_direct
    (hdim2 :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoApolarAnnihilatorDimensionBound B p u)
    (hobstruction :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankThreeApolarMacaulayObstruction B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_rankTwoDimensionBound_rankThreeMacaulayObstruction_direct
    (B := B) hu hp hsocp
    (hdim2 B p u hu hB hp hsocp)
    (hobstruction B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_rankTwoHilbertFirstBound_rankThreeMacaulayObstruction_direct
    (hhilbert2 :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoApolarHilbertFirstBound B p u)
    (hobstruction :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankThreeApolarMacaulayObstruction B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_rankTwoHilbertFirstBound_rankThreeMacaulayObstruction_direct
    (B := B) hu hp hsocp
    (hhilbert2 B p u hu hB hp hsocp)
    (hobstruction B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_rankTwoMacaulayGrowthData_rankThreeMacaulayObstruction_direct
    (hdata2 :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoApolarMacaulayGrowthData B p u)
    (hobstruction :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankThreeApolarMacaulayObstruction B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_rankTwoMacaulayGrowthData_rankThreeMacaulayObstruction_direct
    (B := B) hu hp hsocp
    (hdata2 B p u hu hB hp hsocp)
    (hobstruction B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_rankTwoMacaulayGrowthData_rankThreeExactSequenceData_direct
    (hdata2 :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoApolarMacaulayGrowthData B p u)
    (hdata3 :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankThreeApolarExactSequenceData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_rankTwoMacaulayGrowthData_rankThreeExactSequenceData_direct
    (B := B) hu hp hsocp
    (hdata2 B p u hu hB hp hsocp)
    (hdata3 B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarHilbertData_direct
    (hdata :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarHilbertData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_lowRankApolarHilbertData_direct
    (B := B) hu hp hsocp
    (hdata B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarBlueprintHilbertData_direct
    (hdata :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarBlueprintHilbertData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_lowRankApolarBlueprintHilbertData_direct
    (B := B) hu hp hsocp
    (hdata B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarBlueprintLocalData_direct
    (hdata :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarBlueprintLocalData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_lowRankApolarBlueprintLocalData_direct
    (B := B) hu hp hsocp
    (hdata B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_blueprintLocalComponents_direct
    (hsymm2 :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoApolarGorensteinSymmetryData B p u)
    (hgrowth2 :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoApolarMacaulayGrowthBound B p u)
    (hshape3 :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankThreeApolarBadBranchExactSequenceShape B p u)
    (hmac3 :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankThreeApolarBadBranchMacaulayBound B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_blueprintLocalComponents_direct
    (B := B) hu hp hsocp
    (hsymm2 B p u hu hB hp hsocp)
    (hgrowth2 B p u hu hB hp hsocp)
    (hshape3 B p u hu hB hp hsocp)
    (hmac3 B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarQuotientLocalData_direct
    (hdata :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarQuotientLocalData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_lowRankApolarQuotientLocalData_direct
    (B := B) hu hp hsocp
    (hdata B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarQuotientCoreData_direct
    (hdata :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarQuotientCoreData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_lowRankApolarQuotientCoreData_direct
    (B := B) hu hp hsocp
    (hdata B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_quotientCoreComponents_direct
    (hgrowth2 :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoApolarMacaulayGrowthBound B p u)
    (hbad3 :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankThreeApolarBadBranchContradiction B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_quotientCoreComponents_direct
    (B := B) hu hp hsocp
    (hgrowth2 B p u hu hB hp hsocp)
    (hbad3 B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_globalLowRankApolarQuotientCoreData
    (hdata : HasGlobalLowRankApolarQuotientCoreData) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP :=
  quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarQuotientCoreData_direct
    hdata

theorem globalLowRankApolarQuotientCoreData_of_quaternaryQuartic_rankSeven_no_spurious_socp
    (hmain : QuaternaryQuarticRankSevenNoSpuriousSOCP) :
    HasGlobalLowRankApolarQuotientCoreData := by
  intro B p u hu hB hp hsocp
  have hres : residual p u = 0 := hmain B p u hB hp hu hsocp
  have hrank_zero :
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 0 :=
    finrank_range_catalecticantMap_eq_zero_of_residual_eq_zero hres
  constructor
  · intro hrank2 h3 _hh3
    omega
  · intro hrank3 _hbad
    omega

theorem quaternaryQuartic_rankSeven_no_spurious_socp_iff_globalLowRankApolarQuotientCoreData :
    QuaternaryQuarticRankSevenNoSpuriousSOCP ↔
      HasGlobalLowRankApolarQuotientCoreData :=
  ⟨globalLowRankApolarQuotientCoreData_of_quaternaryQuartic_rankSeven_no_spurious_socp,
    quaternaryQuartic_rankSeven_no_spurious_socp_of_globalLowRankApolarQuotientCoreData⟩

theorem globalLowRankApolarQuotientCoreData_of_globalLowRankApolarEssentialQuotientTheorem
    (hquot : HasGlobalLowRankApolarEssentialQuotientTheorem) :
    HasGlobalLowRankApolarQuotientCoreData := by
  intro B p u hu hB hp hsocp
  exact lowRankApolarQuotientCoreData_of_lowRankApolarEssentialQuotientTheorem
    (hquot B p u hu hB hp hsocp)

theorem globalLowRankApolarEssentialQuotientTheorem_of_globalLowRankApolarQuotientCoreData
    (hcore : HasGlobalLowRankApolarQuotientCoreData) :
    HasGlobalLowRankApolarEssentialQuotientTheorem := by
  intro B p u hu hB hp hsocp
  exact lowRankApolarEssentialQuotientTheorem_of_coreData
    (hcore B p u hu hB hp hsocp)

theorem globalLowRankApolarQuotientCoreData_iff_globalLowRankApolarEssentialQuotientTheorem :
    HasGlobalLowRankApolarQuotientCoreData ↔
      HasGlobalLowRankApolarEssentialQuotientTheorem :=
  ⟨globalLowRankApolarEssentialQuotientTheorem_of_globalLowRankApolarQuotientCoreData,
    globalLowRankApolarQuotientCoreData_of_globalLowRankApolarEssentialQuotientTheorem⟩

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_globalLowRankApolarEssentialQuotientTheorem
    (hquot : HasGlobalLowRankApolarEssentialQuotientTheorem) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP :=
  quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarEssentialQuotientTheorem_direct
    hquot

theorem globalLowRankApolarEssentialQuotientTheorem_of_quaternaryQuartic_rankSeven_no_spurious_socp
    (hmain : QuaternaryQuarticRankSevenNoSpuriousSOCP) :
    HasGlobalLowRankApolarEssentialQuotientTheorem := by
  exact globalLowRankApolarEssentialQuotientTheorem_of_globalLowRankApolarQuotientCoreData
    (globalLowRankApolarQuotientCoreData_of_quaternaryQuartic_rankSeven_no_spurious_socp
      hmain)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_iff_globalLowRankApolarEssentialQuotientTheorem :
    QuaternaryQuarticRankSevenNoSpuriousSOCP ↔
      HasGlobalLowRankApolarEssentialQuotientTheorem :=
  ⟨globalLowRankApolarEssentialQuotientTheorem_of_quaternaryQuartic_rankSeven_no_spurious_socp,
    quaternaryQuartic_rankSeven_no_spurious_socp_of_globalLowRankApolarEssentialQuotientTheorem⟩

theorem globalLowRankApolarAnnihilatorMapTheorem_of_globalLowRankApolarEssentialQuotientTheorem
    (hquot : HasGlobalLowRankApolarEssentialQuotientTheorem) :
    HasGlobalLowRankApolarAnnihilatorMapTheorem := by
  intro B p u hu hB hp hsocp
  exact hasLowRankApolarAnnihilatorMapTheorem_of_lowRankApolarEssentialQuotientTheorem
    (hquot B p u hu hB hp hsocp)

theorem globalLowRankApolarEssentialQuotientTheorem_of_globalLowRankApolarAnnihilatorMapTheorem
    (hann : HasGlobalLowRankApolarAnnihilatorMapTheorem) :
    HasGlobalLowRankApolarEssentialQuotientTheorem := by
  intro B p u hu hB hp hsocp
  exact lowRankApolarEssentialQuotientTheorem_of_lowRankApolarAnnihilatorMapTheorem
    (hann B p u hu hB hp hsocp)

theorem globalLowRankApolarAnnihilatorMapTheorem_iff_globalLowRankApolarEssentialQuotientTheorem :
    HasGlobalLowRankApolarAnnihilatorMapTheorem ↔
      HasGlobalLowRankApolarEssentialQuotientTheorem :=
  ⟨globalLowRankApolarEssentialQuotientTheorem_of_globalLowRankApolarAnnihilatorMapTheorem,
    globalLowRankApolarAnnihilatorMapTheorem_of_globalLowRankApolarEssentialQuotientTheorem⟩

theorem globalLowRankApolarSupportTheorem_of_globalLowRankApolarEssentialQuotientTheorem
    (hquot : HasGlobalLowRankApolarEssentialQuotientTheorem) :
    HasGlobalLowRankApolarSupportTheorem := by
  intro B p u hu hB hp hsocp
  exact hasLowRankApolarSupportTheorem_of_lowRankApolarEssentialQuotientTheorem
    (hquot B p u hu hB hp hsocp)

theorem globalLowRankApolarEssentialQuotientTheorem_of_globalLowRankApolarSupportTheorem
    (hsupport : HasGlobalLowRankApolarSupportTheorem) :
    HasGlobalLowRankApolarEssentialQuotientTheorem := by
  intro B p u hu hB hp hsocp
  exact lowRankApolarEssentialQuotientTheorem_of_lowRankApolarSupportTheorem
    (hsupport B p u hu hB hp hsocp)

theorem globalLowRankApolarSupportTheorem_iff_globalLowRankApolarEssentialQuotientTheorem :
    HasGlobalLowRankApolarSupportTheorem ↔
      HasGlobalLowRankApolarEssentialQuotientTheorem :=
  ⟨globalLowRankApolarEssentialQuotientTheorem_of_globalLowRankApolarSupportTheorem,
    globalLowRankApolarSupportTheorem_of_globalLowRankApolarEssentialQuotientTheorem⟩

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_globalLowRankApolarAnnihilatorMapTheorem
    (hann : HasGlobalLowRankApolarAnnihilatorMapTheorem) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP :=
  quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarAnnihilatorMapTheorem_direct
    (fun B p u hu hB hp hsocp => hann B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_globalLowRankApolarSupportTheorem
    (hsupport : HasGlobalLowRankApolarSupportTheorem) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP :=
  quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarSupportTheorem_direct
    (fun B p u hu hB hp hsocp => hsupport B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_iff_globalLowRankApolarAnnihilatorMapTheorem :
    QuaternaryQuarticRankSevenNoSpuriousSOCP ↔
      HasGlobalLowRankApolarAnnihilatorMapTheorem :=
  ⟨fun hmain =>
      globalLowRankApolarAnnihilatorMapTheorem_of_globalLowRankApolarEssentialQuotientTheorem
        (globalLowRankApolarEssentialQuotientTheorem_of_quaternaryQuartic_rankSeven_no_spurious_socp
          hmain),
    quaternaryQuartic_rankSeven_no_spurious_socp_of_globalLowRankApolarAnnihilatorMapTheorem⟩

theorem quaternaryQuartic_rankSeven_no_spurious_socp_iff_globalLowRankApolarSupportTheorem :
    QuaternaryQuarticRankSevenNoSpuriousSOCP ↔
      HasGlobalLowRankApolarSupportTheorem :=
  ⟨fun hmain =>
      globalLowRankApolarSupportTheorem_of_globalLowRankApolarEssentialQuotientTheorem
        (globalLowRankApolarEssentialQuotientTheorem_of_quaternaryQuartic_rankSeven_no_spurious_socp
          hmain),
    quaternaryQuartic_rankSeven_no_spurious_socp_of_globalLowRankApolarSupportTheorem⟩

theorem globalRankCaseAnnihilatorMapBounds_of_globalLowRankApolarAnnihilatorMapTheorem
    (hann : HasGlobalLowRankApolarAnnihilatorMapTheorem) :
    HasGlobalRankCaseAnnihilatorMapBounds := by
  intro B p u hu hB hp hsocp
  exact hasRankCaseAnnihilatorMapBounds_of_lowRankApolarAnnihilatorMapTheorem
    (hann B p u hu hB hp hsocp)

theorem globalLowRankApolarAnnihilatorMapTheorem_of_globalRankCaseAnnihilatorMapBounds
    (hbounds : HasGlobalRankCaseAnnihilatorMapBounds) :
    HasGlobalLowRankApolarAnnihilatorMapTheorem := by
  intro B p u hu hB hp hsocp
  exact hasLowRankApolarAnnihilatorMapTheorem_of_rankCaseAnnihilatorMapBounds
    (hbounds B p u hu hB hp hsocp)

theorem globalRankCaseAnnihilatorMapBounds_iff_globalLowRankApolarAnnihilatorMapTheorem :
    HasGlobalRankCaseAnnihilatorMapBounds ↔
      HasGlobalLowRankApolarAnnihilatorMapTheorem :=
  ⟨globalLowRankApolarAnnihilatorMapTheorem_of_globalRankCaseAnnihilatorMapBounds,
    globalRankCaseAnnihilatorMapBounds_of_globalLowRankApolarAnnihilatorMapTheorem⟩

theorem globalRankCaseApolarSupportBounds_of_globalLowRankApolarSupportTheorem
    (hsupport : HasGlobalLowRankApolarSupportTheorem) :
    HasGlobalRankCaseApolarSupportBounds := by
  intro B p u hu hB hp hsocp
  exact hasRankCaseApolarSupportBounds_of_lowRankApolarSupportTheorem
    (hsupport B p u hu hB hp hsocp)

theorem globalLowRankApolarSupportTheorem_of_globalRankCaseApolarSupportBounds
    (hsupport : HasGlobalRankCaseApolarSupportBounds) :
    HasGlobalLowRankApolarSupportTheorem := by
  intro B p u hu hB hp hsocp
  exact hasLowRankApolarSupportTheorem_of_rankCaseApolarSupportBounds
    (hsupport B p u hu hB hp hsocp)

theorem globalRankCaseApolarSupportBounds_iff_globalLowRankApolarSupportTheorem :
    HasGlobalRankCaseApolarSupportBounds ↔
      HasGlobalLowRankApolarSupportTheorem :=
  ⟨globalLowRankApolarSupportTheorem_of_globalRankCaseApolarSupportBounds,
    globalRankCaseApolarSupportBounds_of_globalLowRankApolarSupportTheorem⟩

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_globalRankCaseAnnihilatorMapBounds
    (hbounds : HasGlobalRankCaseAnnihilatorMapBounds) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP :=
  quaternaryQuartic_rankSeven_no_spurious_socp_of_rankCaseAnnihilatorMapBounds_direct
    (fun B p u hu hB hp hsocp => hbounds B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_globalRankCaseApolarSupportBounds
    (hsupport : HasGlobalRankCaseApolarSupportBounds) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP :=
  quaternaryQuartic_rankSeven_no_spurious_socp_of_globalLowRankApolarSupportTheorem
    (globalLowRankApolarSupportTheorem_of_globalRankCaseApolarSupportBounds hsupport)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_iff_globalRankCaseAnnihilatorMapBounds :
    QuaternaryQuarticRankSevenNoSpuriousSOCP ↔
      HasGlobalRankCaseAnnihilatorMapBounds :=
  ⟨fun hmain =>
      globalRankCaseAnnihilatorMapBounds_of_globalLowRankApolarAnnihilatorMapTheorem
        ((quaternaryQuartic_rankSeven_no_spurious_socp_iff_globalLowRankApolarAnnihilatorMapTheorem).mp
          hmain),
    quaternaryQuartic_rankSeven_no_spurious_socp_of_globalRankCaseAnnihilatorMapBounds⟩

theorem quaternaryQuartic_rankSeven_no_spurious_socp_iff_globalRankCaseApolarSupportBounds :
    QuaternaryQuarticRankSevenNoSpuriousSOCP ↔
      HasGlobalRankCaseApolarSupportBounds :=
  ⟨fun hmain =>
      globalRankCaseApolarSupportBounds_of_globalLowRankApolarSupportTheorem
        ((quaternaryQuartic_rankSeven_no_spurious_socp_iff_globalLowRankApolarSupportTheorem).mp
          hmain),
    quaternaryQuartic_rankSeven_no_spurious_socp_of_globalRankCaseApolarSupportBounds⟩

theorem globalRankCaseAnnihilatorMapBounds_of_globalRankTwoThreeApolarAnnihilatorMapBounds
    (hbounds : HasGlobalRankTwoThreeApolarAnnihilatorMapBounds) :
    HasGlobalRankCaseAnnihilatorMapBounds := by
  intro B p u hu hB hp hsocp
  exact hasRankCaseAnnihilatorMapBounds_of_rankTwo_rankThree
    (hbounds B p u hu hB hp hsocp).1
    (hbounds B p u hu hB hp hsocp).2

theorem globalRankTwoThreeApolarAnnihilatorMapBounds_of_globalRankCaseAnnihilatorMapBounds
    (hbounds : HasGlobalRankCaseAnnihilatorMapBounds) :
    HasGlobalRankTwoThreeApolarAnnihilatorMapBounds := by
  intro B p u hu hB hp hsocp
  exact ⟨(hbounds B p u hu hB hp hsocp).2.1,
    (hbounds B p u hu hB hp hsocp).2.2⟩

theorem globalRankTwoThreeApolarAnnihilatorMapBounds_iff_globalRankCaseAnnihilatorMapBounds :
    HasGlobalRankTwoThreeApolarAnnihilatorMapBounds ↔
      HasGlobalRankCaseAnnihilatorMapBounds :=
  ⟨globalRankCaseAnnihilatorMapBounds_of_globalRankTwoThreeApolarAnnihilatorMapBounds,
    globalRankTwoThreeApolarAnnihilatorMapBounds_of_globalRankCaseAnnihilatorMapBounds⟩

theorem globalRankCaseApolarSupportBounds_of_globalRankTwoThreeApolarSupportBounds
    (hsupport : HasGlobalRankTwoThreeApolarSupportBounds) :
    HasGlobalRankCaseApolarSupportBounds := by
  intro B p u hu hB hp hsocp
  exact ⟨rankOneApolarSupportBound_direct (B := B) (p := p) (u := u),
    (hsupport B p u hu hB hp hsocp).1,
    (hsupport B p u hu hB hp hsocp).2⟩

theorem globalRankTwoThreeApolarSupportBounds_of_globalRankCaseApolarSupportBounds
    (hsupport : HasGlobalRankCaseApolarSupportBounds) :
    HasGlobalRankTwoThreeApolarSupportBounds := by
  intro B p u hu hB hp hsocp
  exact ⟨(hsupport B p u hu hB hp hsocp).2.1,
    (hsupport B p u hu hB hp hsocp).2.2⟩

theorem globalRankTwoThreeApolarSupportBounds_iff_globalRankCaseApolarSupportBounds :
    HasGlobalRankTwoThreeApolarSupportBounds ↔
      HasGlobalRankCaseApolarSupportBounds :=
  ⟨globalRankCaseApolarSupportBounds_of_globalRankTwoThreeApolarSupportBounds,
    globalRankTwoThreeApolarSupportBounds_of_globalRankCaseApolarSupportBounds⟩

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_globalRankTwoThreeApolarAnnihilatorMapBounds
    (hbounds : HasGlobalRankTwoThreeApolarAnnihilatorMapBounds) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP :=
  quaternaryQuartic_rankSeven_no_spurious_socp_of_globalRankCaseAnnihilatorMapBounds
    (globalRankCaseAnnihilatorMapBounds_of_globalRankTwoThreeApolarAnnihilatorMapBounds hbounds)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_globalRankTwoThreeApolarSupportBounds
    (hsupport : HasGlobalRankTwoThreeApolarSupportBounds) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP :=
  quaternaryQuartic_rankSeven_no_spurious_socp_of_globalRankCaseApolarSupportBounds
    (globalRankCaseApolarSupportBounds_of_globalRankTwoThreeApolarSupportBounds hsupport)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_iff_globalRankTwoThreeApolarAnnihilatorMapBounds :
    QuaternaryQuarticRankSevenNoSpuriousSOCP ↔
      HasGlobalRankTwoThreeApolarAnnihilatorMapBounds :=
  ⟨fun hmain =>
      globalRankTwoThreeApolarAnnihilatorMapBounds_of_globalRankCaseAnnihilatorMapBounds
        ((quaternaryQuartic_rankSeven_no_spurious_socp_iff_globalRankCaseAnnihilatorMapBounds).mp
          hmain),
    quaternaryQuartic_rankSeven_no_spurious_socp_of_globalRankTwoThreeApolarAnnihilatorMapBounds⟩

theorem quaternaryQuartic_rankSeven_no_spurious_socp_iff_globalRankTwoThreeApolarSupportBounds :
    QuaternaryQuarticRankSevenNoSpuriousSOCP ↔
      HasGlobalRankTwoThreeApolarSupportBounds :=
  ⟨fun hmain =>
      globalRankTwoThreeApolarSupportBounds_of_globalRankCaseApolarSupportBounds
        ((quaternaryQuartic_rankSeven_no_spurious_socp_iff_globalRankCaseApolarSupportBounds).mp
          hmain),
    quaternaryQuartic_rankSeven_no_spurious_socp_of_globalRankTwoThreeApolarSupportBounds⟩

theorem globalRankTwoThreeApolarEssentialQuotientBounds_of_globalRankTwoThreeApolarAnnihilatorMapBounds
    (hbounds : HasGlobalRankTwoThreeApolarAnnihilatorMapBounds) :
    HasGlobalRankTwoThreeApolarEssentialQuotientBounds := by
  intro B p u hu hB hp hsocp
  exact ⟨
    rankTwoEssentialQuotientBound_of_rankTwoApolarAnnihilatorMapBound
      (hbounds B p u hu hB hp hsocp).1,
    rankThreeEssentialQuotientBound_of_rankThreeApolarAnnihilatorMapBound
      (hbounds B p u hu hB hp hsocp).2⟩

theorem globalRankTwoThreeApolarAnnihilatorMapBounds_of_globalRankTwoThreeApolarEssentialQuotientBounds
    (hquot : HasGlobalRankTwoThreeApolarEssentialQuotientBounds) :
    HasGlobalRankTwoThreeApolarAnnihilatorMapBounds := by
  intro B p u hu hB hp hsocp
  exact ⟨
    rankTwoApolarAnnihilatorMapBound_of_rankTwoEssentialQuotientBound
      (hquot B p u hu hB hp hsocp).1,
    rankThreeApolarAnnihilatorMapBound_of_rankThreeEssentialQuotientBound
      (hquot B p u hu hB hp hsocp).2⟩

theorem globalRankTwoThreeApolarEssentialQuotientBounds_iff_globalRankTwoThreeApolarAnnihilatorMapBounds :
    HasGlobalRankTwoThreeApolarEssentialQuotientBounds ↔
      HasGlobalRankTwoThreeApolarAnnihilatorMapBounds :=
  ⟨globalRankTwoThreeApolarAnnihilatorMapBounds_of_globalRankTwoThreeApolarEssentialQuotientBounds,
    globalRankTwoThreeApolarEssentialQuotientBounds_of_globalRankTwoThreeApolarAnnihilatorMapBounds⟩

theorem globalRankTwoThreeApolarEssentialQuotientBounds_of_globalRankTwoThreeApolarSupportBounds
    (hsupport : HasGlobalRankTwoThreeApolarSupportBounds) :
    HasGlobalRankTwoThreeApolarEssentialQuotientBounds := by
  intro B p u hu hB hp hsocp
  exact ⟨
    rankTwoEssentialQuotientBound_of_rankTwoSupportBound
      (hsupport B p u hu hB hp hsocp).1,
    rankThreeEssentialQuotientBound_of_rankThreeSupportBound
      (hsupport B p u hu hB hp hsocp).2⟩

theorem globalRankTwoThreeApolarSupportBounds_of_globalRankTwoThreeApolarEssentialQuotientBounds
    (hquot : HasGlobalRankTwoThreeApolarEssentialQuotientBounds) :
    HasGlobalRankTwoThreeApolarSupportBounds := by
  intro B p u hu hB hp hsocp
  exact ⟨
    rankTwoSupportBound_of_rankTwoEssentialQuotientBound
      (hquot B p u hu hB hp hsocp).1,
    rankThreeSupportBound_of_rankThreeEssentialQuotientBound
      (hquot B p u hu hB hp hsocp).2⟩

theorem globalRankTwoThreeApolarEssentialQuotientBounds_iff_globalRankTwoThreeApolarSupportBounds :
    HasGlobalRankTwoThreeApolarEssentialQuotientBounds ↔
      HasGlobalRankTwoThreeApolarSupportBounds :=
  ⟨globalRankTwoThreeApolarSupportBounds_of_globalRankTwoThreeApolarEssentialQuotientBounds,
    globalRankTwoThreeApolarEssentialQuotientBounds_of_globalRankTwoThreeApolarSupportBounds⟩

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_globalRankTwoThreeApolarEssentialQuotientBounds
    (hquot : HasGlobalRankTwoThreeApolarEssentialQuotientBounds) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP :=
  quaternaryQuartic_rankSeven_no_spurious_socp_of_globalRankTwoThreeApolarAnnihilatorMapBounds
    (globalRankTwoThreeApolarAnnihilatorMapBounds_of_globalRankTwoThreeApolarEssentialQuotientBounds
      hquot)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_iff_globalRankTwoThreeApolarEssentialQuotientBounds :
    QuaternaryQuarticRankSevenNoSpuriousSOCP ↔
      HasGlobalRankTwoThreeApolarEssentialQuotientBounds :=
  ⟨fun hmain =>
      globalRankTwoThreeApolarEssentialQuotientBounds_of_globalRankTwoThreeApolarAnnihilatorMapBounds
        ((quaternaryQuartic_rankSeven_no_spurious_socp_iff_globalRankTwoThreeApolarAnnihilatorMapBounds).mp
          hmain),
    quaternaryQuartic_rankSeven_no_spurious_socp_of_globalRankTwoThreeApolarEssentialQuotientBounds⟩

theorem globalRankTwoThreeApolarEssentialQuotientBounds_of_splitGlobalEssentialQuotientBounds
    (hquot2 : HasGlobalRankTwoApolarEssentialQuotientBound)
    (hquot3 : HasGlobalRankThreeApolarEssentialQuotientBound) :
    HasGlobalRankTwoThreeApolarEssentialQuotientBounds := by
  intro B p u hu hB hp hsocp
  exact ⟨hquot2 B p u hu hB hp hsocp,
    hquot3 B p u hu hB hp hsocp⟩

theorem splitGlobalEssentialQuotientBounds_of_globalRankTwoThreeApolarEssentialQuotientBounds
    (hquot : HasGlobalRankTwoThreeApolarEssentialQuotientBounds) :
    HasGlobalRankTwoApolarEssentialQuotientBound ∧
      HasGlobalRankThreeApolarEssentialQuotientBound := by
  exact ⟨
    fun B p u hu hB hp hsocp => (hquot B p u hu hB hp hsocp).1,
    fun B p u hu hB hp hsocp => (hquot B p u hu hB hp hsocp).2⟩

theorem globalRankTwoThreeApolarEssentialQuotientBounds_iff_splitGlobalEssentialQuotientBounds :
    HasGlobalRankTwoThreeApolarEssentialQuotientBounds ↔
      HasGlobalRankTwoApolarEssentialQuotientBound ∧
        HasGlobalRankThreeApolarEssentialQuotientBound :=
  ⟨splitGlobalEssentialQuotientBounds_of_globalRankTwoThreeApolarEssentialQuotientBounds,
    fun hquot =>
      globalRankTwoThreeApolarEssentialQuotientBounds_of_splitGlobalEssentialQuotientBounds
        hquot.1 hquot.2⟩

theorem globalRankTwoApolarEssentialQuotientBound_of_globalRankTwoApolarMacaulayGrowthBound
    (hgrowth : HasGlobalRankTwoApolarMacaulayGrowthBound) :
    HasGlobalRankTwoApolarEssentialQuotientBound := by
  intro B p u hu hB hp hsocp
  exact rankTwoEssentialQuotientBound_of_macaulayGrowth
    (hgrowth B p u hu hB hp hsocp)

theorem globalRankTwoApolarMacaulayGrowthBound_of_globalRankTwoApolarEssentialQuotientBound
    (hquot : HasGlobalRankTwoApolarEssentialQuotientBound) :
    HasGlobalRankTwoApolarMacaulayGrowthBound := by
  intro B p u hu hB hp hsocp
  exact rankTwoMacaulayGrowthBound_of_rankTwoEssentialQuotientBound
    (hquot B p u hu hB hp hsocp)

theorem globalRankTwoApolarMacaulayGrowthBound_iff_globalRankTwoApolarEssentialQuotientBound :
    HasGlobalRankTwoApolarMacaulayGrowthBound ↔
      HasGlobalRankTwoApolarEssentialQuotientBound :=
  ⟨globalRankTwoApolarEssentialQuotientBound_of_globalRankTwoApolarMacaulayGrowthBound,
    globalRankTwoApolarMacaulayGrowthBound_of_globalRankTwoApolarEssentialQuotientBound⟩

theorem globalRankThreeApolarEssentialQuotientBound_of_globalRankThreeApolarBadBranchContradiction
    (hbad : HasGlobalRankThreeApolarBadBranchContradiction) :
    HasGlobalRankThreeApolarEssentialQuotientBound := by
  intro B p u hu hB hp hsocp
  exact rankThreeEssentialQuotientBound_of_badBranchContradiction
    (hbad B p u hu hB hp hsocp)

theorem globalRankThreeApolarBadBranchContradiction_of_globalRankThreeApolarEssentialQuotientBound
    (hquot : HasGlobalRankThreeApolarEssentialQuotientBound) :
    HasGlobalRankThreeApolarBadBranchContradiction := by
  intro B p u hu hB hp hsocp
  exact rankThreeBadBranchContradiction_of_rankThreeEssentialQuotientBound
    (hquot B p u hu hB hp hsocp)

theorem globalRankThreeApolarBadBranchContradiction_iff_globalRankThreeApolarEssentialQuotientBound :
    HasGlobalRankThreeApolarBadBranchContradiction ↔
      HasGlobalRankThreeApolarEssentialQuotientBound :=
  ⟨globalRankThreeApolarEssentialQuotientBound_of_globalRankThreeApolarBadBranchContradiction,
    globalRankThreeApolarBadBranchContradiction_of_globalRankThreeApolarEssentialQuotientBound⟩

theorem globalRankThreeApolarBadBranchExactSequenceShape_of_globalRankThreeApolarBadBranchContradiction
    (hbad : HasGlobalRankThreeApolarBadBranchContradiction) :
    HasGlobalRankThreeApolarBadBranchExactSequenceShape := by
  intro B p u hu hB hp hsocp
  exact rankThreeBadBranchExactSequenceShape_of_badBranchContradiction
    (hbad B p u hu hB hp hsocp)

theorem globalRankThreeApolarBadBranchMacaulayBound_of_globalRankThreeApolarBadBranchContradiction
    (hbad : HasGlobalRankThreeApolarBadBranchContradiction) :
    HasGlobalRankThreeApolarBadBranchMacaulayBound := by
  intro B p u hu hB hp hsocp
  exact rankThreeBadBranchMacaulayBound_of_badBranchContradiction
    (hbad B p u hu hB hp hsocp)

theorem globalRankThreeApolarBadBranchContradiction_of_shape_and_macaulayBound
    (hshape : HasGlobalRankThreeApolarBadBranchExactSequenceShape)
    (hmac : HasGlobalRankThreeApolarBadBranchMacaulayBound) :
    HasGlobalRankThreeApolarBadBranchContradiction := by
  intro B p u hu hB hp hsocp
  exact rankThreeBadBranchContradiction_of_shape_and_macaulayBound
    (hshape B p u hu hB hp hsocp)
    (hmac B p u hu hB hp hsocp)

theorem globalRankThreeApolarBadBranchContradiction_iff_shape_and_macaulayBound :
    HasGlobalRankThreeApolarBadBranchContradiction ↔
      HasGlobalRankThreeApolarBadBranchExactSequenceShape ∧
        HasGlobalRankThreeApolarBadBranchMacaulayBound :=
  ⟨fun hbad =>
      ⟨globalRankThreeApolarBadBranchExactSequenceShape_of_globalRankThreeApolarBadBranchContradiction
          hbad,
        globalRankThreeApolarBadBranchMacaulayBound_of_globalRankThreeApolarBadBranchContradiction
          hbad⟩,
    fun hdata =>
      globalRankThreeApolarBadBranchContradiction_of_shape_and_macaulayBound
        hdata.1 hdata.2⟩

theorem globalRankThreeApolarBadBranchExactSequenceShape_direct :
    HasGlobalRankThreeApolarBadBranchExactSequenceShape := by
  intro B p u _hu _hB _hp _hsocp
  exact rankThreeBadBranchExactSequenceShape_direct B p u

theorem globalRankTwoApolarHilbertFirstBound_of_globalRankTwoApolarEssentialQuotientBound
    (hquot : HasGlobalRankTwoApolarEssentialQuotientBound) :
    HasGlobalRankTwoApolarHilbertFirstBound := by
  intro B p u hu hB hp hsocp
  exact rankTwoHilbertFirstBound_of_rankTwoEssentialQuotientBound
    (hquot B p u hu hB hp hsocp)

theorem globalRankTwoApolarEssentialQuotientBound_of_globalRankTwoApolarHilbertFirstBound
    (hhilbert : HasGlobalRankTwoApolarHilbertFirstBound) :
    HasGlobalRankTwoApolarEssentialQuotientBound := by
  intro B p u hu hB hp hsocp
  exact rankTwoEssentialQuotientBound_of_rankTwoHilbertFirstBound
    (hhilbert B p u hu hB hp hsocp)

theorem globalRankTwoApolarHilbertFirstBound_iff_globalRankTwoApolarEssentialQuotientBound :
    HasGlobalRankTwoApolarHilbertFirstBound ↔
      HasGlobalRankTwoApolarEssentialQuotientBound :=
  ⟨globalRankTwoApolarEssentialQuotientBound_of_globalRankTwoApolarHilbertFirstBound,
    globalRankTwoApolarHilbertFirstBound_of_globalRankTwoApolarEssentialQuotientBound⟩

theorem globalRankThreeApolarHilbertFirstBound_of_globalRankThreeApolarEssentialQuotientBound
    (hquot : HasGlobalRankThreeApolarEssentialQuotientBound) :
    HasGlobalRankThreeApolarHilbertFirstBound := by
  intro B p u hu hB hp hsocp
  exact rankThreeHilbertFirstBound_of_rankThreeEssentialQuotientBound
    (hquot B p u hu hB hp hsocp)

theorem globalRankThreeApolarEssentialQuotientBound_of_globalRankThreeApolarHilbertFirstBound
    (hhilbert : HasGlobalRankThreeApolarHilbertFirstBound) :
    HasGlobalRankThreeApolarEssentialQuotientBound := by
  intro B p u hu hB hp hsocp
  exact rankThreeEssentialQuotientBound_of_rankThreeHilbertFirstBound
    (hhilbert B p u hu hB hp hsocp)

theorem globalRankThreeApolarHilbertFirstBound_iff_globalRankThreeApolarEssentialQuotientBound :
    HasGlobalRankThreeApolarHilbertFirstBound ↔
      HasGlobalRankThreeApolarEssentialQuotientBound :=
  ⟨globalRankThreeApolarEssentialQuotientBound_of_globalRankThreeApolarHilbertFirstBound,
    globalRankThreeApolarHilbertFirstBound_of_globalRankThreeApolarEssentialQuotientBound⟩

theorem globalRankTwoThreeApolarEssentialQuotientBounds_of_globalRankTwoThreeApolarHilbertFirstBounds
    (hhilbert : HasGlobalRankTwoThreeApolarHilbertFirstBounds) :
    HasGlobalRankTwoThreeApolarEssentialQuotientBounds :=
  globalRankTwoThreeApolarEssentialQuotientBounds_of_splitGlobalEssentialQuotientBounds
    (globalRankTwoApolarEssentialQuotientBound_of_globalRankTwoApolarHilbertFirstBound
      hhilbert.1)
    (globalRankThreeApolarEssentialQuotientBound_of_globalRankThreeApolarHilbertFirstBound
      hhilbert.2)

theorem globalRankTwoThreeApolarHilbertFirstBounds_of_globalRankTwoThreeApolarEssentialQuotientBounds
    (hquot : HasGlobalRankTwoThreeApolarEssentialQuotientBounds) :
    HasGlobalRankTwoThreeApolarHilbertFirstBounds := by
  have hsplit :=
    splitGlobalEssentialQuotientBounds_of_globalRankTwoThreeApolarEssentialQuotientBounds
      hquot
  exact ⟨
    globalRankTwoApolarHilbertFirstBound_of_globalRankTwoApolarEssentialQuotientBound
      hsplit.1,
    globalRankThreeApolarHilbertFirstBound_of_globalRankThreeApolarEssentialQuotientBound
      hsplit.2⟩

theorem globalRankTwoThreeApolarHilbertFirstBounds_iff_globalRankTwoThreeApolarEssentialQuotientBounds :
    HasGlobalRankTwoThreeApolarHilbertFirstBounds ↔
      HasGlobalRankTwoThreeApolarEssentialQuotientBounds :=
  ⟨globalRankTwoThreeApolarEssentialQuotientBounds_of_globalRankTwoThreeApolarHilbertFirstBounds,
    globalRankTwoThreeApolarHilbertFirstBounds_of_globalRankTwoThreeApolarEssentialQuotientBounds⟩

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_globalRankTwoThreeApolarHilbertFirstBounds
    (hhilbert : HasGlobalRankTwoThreeApolarHilbertFirstBounds) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP :=
  quaternaryQuartic_rankSeven_no_spurious_socp_of_globalRankTwoThreeApolarEssentialQuotientBounds
    (globalRankTwoThreeApolarEssentialQuotientBounds_of_globalRankTwoThreeApolarHilbertFirstBounds
      hhilbert)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_iff_globalRankTwoThreeApolarHilbertFirstBounds :
    QuaternaryQuarticRankSevenNoSpuriousSOCP ↔
      HasGlobalRankTwoThreeApolarHilbertFirstBounds :=
  ⟨fun hmain =>
      globalRankTwoThreeApolarHilbertFirstBounds_of_globalRankTwoThreeApolarEssentialQuotientBounds
        ((quaternaryQuartic_rankSeven_no_spurious_socp_iff_globalRankTwoThreeApolarEssentialQuotientBounds).mp
          hmain),
    quaternaryQuartic_rankSeven_no_spurious_socp_of_globalRankTwoThreeApolarHilbertFirstBounds⟩

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_globalRankTwoHilbertFirst_and_rankThreeShapeMacaulay
    (hhilbert2 : HasGlobalRankTwoApolarHilbertFirstBound)
    (hshape3 : HasGlobalRankThreeApolarBadBranchExactSequenceShape)
    (hmac3 : HasGlobalRankThreeApolarBadBranchMacaulayBound) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP :=
  quaternaryQuartic_rankSeven_no_spurious_socp_of_globalRankTwoThreeApolarEssentialQuotientBounds
    (globalRankTwoThreeApolarEssentialQuotientBounds_of_splitGlobalEssentialQuotientBounds
      (globalRankTwoApolarEssentialQuotientBound_of_globalRankTwoApolarHilbertFirstBound
        hhilbert2)
      (globalRankThreeApolarEssentialQuotientBound_of_globalRankThreeApolarBadBranchContradiction
        (globalRankThreeApolarBadBranchContradiction_of_shape_and_macaulayBound
          hshape3 hmac3)))

theorem quaternaryQuartic_rankSeven_no_spurious_socp_iff_globalRankTwoHilbertFirst_and_rankThreeShapeMacaulay :
    QuaternaryQuarticRankSevenNoSpuriousSOCP ↔
      HasGlobalRankTwoApolarHilbertFirstBound ∧
        HasGlobalRankThreeApolarBadBranchExactSequenceShape ∧
          HasGlobalRankThreeApolarBadBranchMacaulayBound := by
  constructor
  · intro hmain
    have hquot :=
      (quaternaryQuartic_rankSeven_no_spurious_socp_iff_globalRankTwoThreeApolarEssentialQuotientBounds).mp
        hmain
    have hsplit :=
      splitGlobalEssentialQuotientBounds_of_globalRankTwoThreeApolarEssentialQuotientBounds
        hquot
    have hbad3 :
        HasGlobalRankThreeApolarBadBranchContradiction :=
      globalRankThreeApolarBadBranchContradiction_of_globalRankThreeApolarEssentialQuotientBound
        hsplit.2
    exact ⟨
      globalRankTwoApolarHilbertFirstBound_of_globalRankTwoApolarEssentialQuotientBound
        hsplit.1,
      globalRankThreeApolarBadBranchExactSequenceShape_of_globalRankThreeApolarBadBranchContradiction
        hbad3,
      globalRankThreeApolarBadBranchMacaulayBound_of_globalRankThreeApolarBadBranchContradiction
        hbad3⟩
  · intro hdata
    exact quaternaryQuartic_rankSeven_no_spurious_socp_of_globalRankTwoHilbertFirst_and_rankThreeShapeMacaulay
      hdata.1 hdata.2.1 hdata.2.2

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_globalRankTwoHilbertFirst_and_rankThreeMacaulayBound
    (hhilbert2 : HasGlobalRankTwoApolarHilbertFirstBound)
    (hmac3 : HasGlobalRankThreeApolarBadBranchMacaulayBound) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP :=
  quaternaryQuartic_rankSeven_no_spurious_socp_of_globalRankTwoHilbertFirst_and_rankThreeShapeMacaulay
    hhilbert2 globalRankThreeApolarBadBranchExactSequenceShape_direct hmac3

theorem quaternaryQuartic_rankSeven_no_spurious_socp_iff_globalRankTwoHilbertFirst_and_rankThreeMacaulayBound :
    QuaternaryQuarticRankSevenNoSpuriousSOCP ↔
      HasGlobalRankTwoApolarHilbertFirstBound ∧
        HasGlobalRankThreeApolarBadBranchMacaulayBound := by
  constructor
  · intro hmain
    have hdata :=
      (quaternaryQuartic_rankSeven_no_spurious_socp_iff_globalRankTwoHilbertFirst_and_rankThreeShapeMacaulay).mp
        hmain
    exact ⟨hdata.1, hdata.2.2⟩
  · intro hdata
    exact quaternaryQuartic_rankSeven_no_spurious_socp_of_globalRankTwoHilbertFirst_and_rankThreeMacaulayBound
      hdata.1 hdata.2

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_globalRankTwoMacaulayGrowth_and_rankThreeBadBranch
    (hgrowth2 : HasGlobalRankTwoApolarMacaulayGrowthBound)
    (hbad3 : HasGlobalRankThreeApolarBadBranchContradiction) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP :=
  quaternaryQuartic_rankSeven_no_spurious_socp_of_globalRankTwoThreeApolarEssentialQuotientBounds
    (globalRankTwoThreeApolarEssentialQuotientBounds_of_splitGlobalEssentialQuotientBounds
      (globalRankTwoApolarEssentialQuotientBound_of_globalRankTwoApolarMacaulayGrowthBound
        hgrowth2)
      (globalRankThreeApolarEssentialQuotientBound_of_globalRankThreeApolarBadBranchContradiction
        hbad3))

theorem quaternaryQuartic_rankSeven_no_spurious_socp_iff_globalRankTwoMacaulayGrowth_and_rankThreeBadBranch :
    QuaternaryQuarticRankSevenNoSpuriousSOCP ↔
      HasGlobalRankTwoApolarMacaulayGrowthBound ∧
        HasGlobalRankThreeApolarBadBranchContradiction := by
  constructor
  · intro hmain
    have hquot :=
      (quaternaryQuartic_rankSeven_no_spurious_socp_iff_globalRankTwoThreeApolarEssentialQuotientBounds).mp
        hmain
    have hsplit :=
      splitGlobalEssentialQuotientBounds_of_globalRankTwoThreeApolarEssentialQuotientBounds
        hquot
    exact ⟨
      globalRankTwoApolarMacaulayGrowthBound_of_globalRankTwoApolarEssentialQuotientBound
        hsplit.1,
      globalRankThreeApolarBadBranchContradiction_of_globalRankThreeApolarEssentialQuotientBound
        hsplit.2⟩
  · intro hdata
    exact quaternaryQuartic_rankSeven_no_spurious_socp_of_globalRankTwoMacaulayGrowth_and_rankThreeBadBranch
      hdata.1 hdata.2

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_quotientLocalComponents_direct
    (hsymm2 :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoApolarGorensteinSymmetryData B p u)
    (hgrowth2 :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoApolarMacaulayGrowthBound B p u)
    (hbad3 :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankThreeApolarBadBranchContradiction B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_quotientLocalComponents_direct
    (B := B) hu hp hsocp
    (hsymm2 B p u hu hB hp hsocp)
    (hgrowth2 B p u hu hB hp hsocp)
    (hbad3 B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarSupportTheorem_and_universalNormalizedPosition_and_scalarFacts
    (hsupport :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarSupportTheorem B p u)
    (hpos :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalNormalizedKernelPositionData B p u)
    (hfacts :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoExistentialScalarHankelFacts B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_lowRankApolarSupportTheorem_and_universalNormalizedPosition_and_scalarFacts
    (B := B) hu hp hsocp
    (hsupport B p u hu hB hp hsocp)
    (hpos B p u hu hB hp hsocp)
    (hfacts B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_apolarSupportBounds_and_universalNormalizedPosition_and_scalarFacts
    (hsupport :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseApolarSupportBounds B p u)
    (hpos :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalNormalizedKernelPositionData B p u)
    (hfacts :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoExistentialScalarHankelFacts B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_apolarSupportBounds_and_universalNormalizedPosition_and_scalarFacts
    (B := B) hu hp hsocp
    (hsupport B p u hu hB hp hsocp)
    (hpos B p u hu hB hp hsocp)
    (hfacts B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_lowRankApolarAnnihilatorMapTheorem_and_normalizedHankelData
    (hann :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasLowRankApolarAnnihilatorMapTheorem B p u)
    (hdata :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoExistentialNormalizedHankelData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_lowRankApolarAnnihilatorMapTheorem_and_normalizedHankelData
    (B := B) hu hp hsocp
    (hann B p u hu hB hp hsocp)
    (hdata B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_rankCaseAnnihilatorMapBounds_and_normalizedHankelData
    (hbounds :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseAnnihilatorMapBounds B p u)
    (hdata :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoExistentialNormalizedHankelData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_rankCaseAnnihilatorMapBounds_and_normalizedHankelData
    (B := B) hu hp hsocp
    (hbounds B p u hu hB hp hsocp)
    (hdata B p u hu hB hp hsocp)

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

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_productIndependenceApolarData_via_kernelEquationData
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
  exact residual_eq_zero_of_productIndependenceApolarData_via_kernelEquationData
    (B := B) hu hp hsocp (hdata B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_productIndependenceGeometryData_and_universalKernelBranchData
    (hgeom :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseProductIndependenceGeometryData B p u hu)
    (hbranches :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalKernelBranchData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_productIndependenceGeometryData_and_universalKernelBranchData
    (B := B) hu hp hsocp
    (hgeom B p u hu hB hp hsocp)
    (hbranches B p u hu hB hp hsocp)

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_productIndependenceGeometryData_and_universalNormalizedHankelData
    (hgeom :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankCaseProductIndependenceGeometryData B p u hu)
    (hdata :
      ∀ (B : DotForm) (p : Poly) (u : RankSevenVec)
        (_hu : IsAdmissiblePoint u),
        IsPositiveDefinite B →
          IsSOSQuartic p →
            IsSOCP B p u →
              HasRankTwoUniversalNormalizedHankelData B p u) :
    QuaternaryQuarticRankSevenNoSpuriousSOCP := by
  intro B p u hB hp hu hsocp
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact residual_eq_zero_of_productIndependenceGeometryData_and_universalNormalizedHankelData
    (B := B) hu hp hsocp
    (hgeom B p u hu hB hp hsocp)
    (hdata B p u hu hB hp hsocp)

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

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_productFreeApolarData_via_kernelEquationData
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
  exact residual_eq_zero_of_productFreeApolarData_via_kernelEquationData
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

theorem quaternaryQuartic_rankSeven_no_spurious_socp_of_rankOneFreeApolarData_via_kernelEquationData
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
  exact residual_eq_zero_of_rankOneFreeApolarData_via_kernelEquationData
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
