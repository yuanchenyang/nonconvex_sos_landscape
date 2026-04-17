import Mathlib.LinearAlgebra.BilinearForm.Hom
import TernaryQuarticProof.AffineTransform

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace TernaryQuartic

/-- Transport a bilinear form across a polynomial algebra equivalence by
precomposing both arguments with the inverse. -/
def dotTransport (e : Poly ≃ₐ[ℝ] Poly) (B : DotForm) : DotForm :=
  B.comp e.symm.toLinearMap e.symm.toLinearMap

@[simp] theorem dotTransport_apply
    (e : Poly ≃ₐ[ℝ] Poly) (B : DotForm) (p q : Poly) :
    dotTransport e B p q = B (e.symm p) (e.symm q) :=
  rfl

theorem dotTransport_posDef
    (e : Poly ≃ₐ[ℝ] Poly) {B : DotForm} [Fact B.toQuadraticMap.PosDef] :
    (dotTransport e B).toQuadraticMap.PosDef := by
  have hBpos : B.toQuadraticMap.PosDef := Fact.out
  intro p hp
  change 0 < B (e.symm p) (e.symm p)
  have hp' : e.symm p ≠ 0 := by
    intro h
    apply hp
    apply e.injective
    simpa using h
  simpa [LinearMap.BilinMap.toQuadraticMap_apply] using hBpos (e.symm p) hp'

theorem isPositiveDefinite_dotTransport
    (e : Poly ≃ₐ[ℝ] Poly) {B : DotForm}
    (hB : IsPositiveDefinite B) :
    IsPositiveDefinite (dotTransport e B) := by
  letI : Fact B.toQuadraticMap.PosDef := ⟨hB⟩
  exact dotTransport_posDef e

@[simp] theorem mapVec_id (u : RankFourVec) :
    mapVec (AlgHom.id ℝ Poly) u = u := by
  ext i
  simp [mapVec]

@[simp] theorem mapVec_symm_mapVec (e : Poly ≃ₐ[ℝ] Poly) (u : RankFourVec) :
    mapVec e.symm.toAlgHom (mapVec e.toAlgHom u) = u := by
  ext i
  simp [mapVec]

@[simp] theorem mapVec_mapVec_symm (e : Poly ≃ₐ[ℝ] Poly) (u : RankFourVec) :
    mapVec e.toAlgHom (mapVec e.symm.toAlgHom u) = u := by
  ext i
  simp [mapVec]

theorem A_mapVec_equiv_inv_apply
    (e : Poly ≃ₐ[ℝ] Poly) (u v' : RankFourVec) :
    e.symm (A (mapVec e.toAlgHom u) v') = A u (mapVec e.symm.toAlgHom v') := by
  let v := mapVec e.symm.toAlgHom v'
  have h : A (mapVec e.toAlgHom u) (mapVec e.toAlgHom v) = e (A u v) :=
    A_mapVec (φ := e.toAlgHom) u v
  have hv : mapVec e.toAlgHom v = v' := by
    ext i
    simp [v, mapVec]
  rw [hv] at h
  simpa [v] using congrArg e.symm h

theorem sigma_mapVec_equiv_inv_apply
    (e : Poly ≃ₐ[ℝ] Poly) (u : RankFourVec) :
    e.symm (sigma (mapVec e.toAlgHom u)) = sigma u := by
  have h := sigma_mapVec (φ := e.toAlgHom) u
  simpa using congrArg e.symm h

theorem residual_mapVec_equiv_inv_apply
    (e : Poly ≃ₐ[ℝ] Poly) (p : Poly) (u : RankFourVec) :
    e.symm (residual (e p) (mapVec e.toAlgHom u)) = residual p u := by
  have h := residual_mapVec (φ := e.toAlgHom) p u
  simpa using congrArg e.symm h

theorem hessianTerm_mapVec_of_equiv
    (e : Poly ≃ₐ[ℝ] Poly) (B : DotForm) (p : Poly) (u v : RankFourVec) :
    hessianTerm (dotTransport e B) (e p) (mapVec e.toAlgHom u) (mapVec e.toAlgHom v) =
      hessianTerm B p u v := by
  have hv : mapVec e.symm.toAlgHom (mapVec e.toAlgHom v) = v := mapVec_symm_mapVec e v
  simp only [hessianTerm, dotTransport_apply]
  rw [sigma_mapVec_equiv_inv_apply, residual_mapVec_equiv_inv_apply,
    A_mapVec_equiv_inv_apply]
  rw [hv]

theorem isFOCP_mapVec_of_equiv
    (e : Poly ≃ₐ[ℝ] Poly)
    (heSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hfocp : IsFOCP B p u) :
    IsFOCP (dotTransport e B) (e p) (mapVec e.toAlgHom u) := by
  intro v' hv'
  let v : RankFourVec := mapVec e.symm.toAlgHom v'
  have hv : IsAdmissibleDirection v := by
    intro i
    exact heSymm (hv' i)
  have h0 := hfocp v hv
  rw [dotTransport_apply, A_mapVec_equiv_inv_apply, residual_mapVec_equiv_inv_apply]
  exact h0

theorem isSOCP_mapVec_of_equiv
    (e : Poly ≃ₐ[ℝ] Poly)
    (heSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hsocp : IsSOCP B p u) :
    IsSOCP (dotTransport e B) (e p) (mapVec e.toAlgHom u) := by
  refine ⟨isFOCP_mapVec_of_equiv e heSymm hsocp.1, ?_⟩
  intro v' hv'
  let v : RankFourVec := mapVec e.symm.toAlgHom v'
  have hv : IsAdmissibleDirection v := by
    intro i
    exact heSymm (hv' i)
  have h0 : 0 ≤ hessianTerm B p u v := hsocp.2 v hv
  have hv'Eq : mapVec e.toAlgHom v = v' := by
    ext i
    simp [v, mapVec]
  rw [← hv'Eq]
  simpa using (hessianTerm_mapVec_of_equiv e B p u v).symm ▸ h0

theorem isQuadratic_affineEquiv
    (A A' : Matrix (Fin 2) (Fin 2) ℝ) (b b' : Fin 2 → ℝ)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (hb : ∀ i, b' i + Matrix.mulVec A' b i = 0)
    (hb' : ∀ i, b i + Matrix.mulVec A b' i = 0)
    {p : Poly} (hp : IsQuadratic p) :
    IsQuadratic ((affineEquiv A A' b b' hAA' hA'A hb hb') p) := by
  change IsQuadratic (affineHom A b p)
  exact isQuadratic_affineHom A b hp

theorem isQuartic_affineEquiv
    (A A' : Matrix (Fin 2) (Fin 2) ℝ) (b b' : Fin 2 → ℝ)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (hb : ∀ i, b' i + Matrix.mulVec A' b i = 0)
    (hb' : ∀ i, b i + Matrix.mulVec A b' i = 0)
    {p : Poly} (hp : IsQuartic p) :
    IsQuartic ((affineEquiv A A' b b' hAA' hA'A hb hb') p) := by
  change IsQuartic (affineHom A b p)
  exact isQuartic_affineHom A b hp

theorem isQuadratic_affineEquiv_symm
    (A A' : Matrix (Fin 2) (Fin 2) ℝ) (b b' : Fin 2 → ℝ)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (hb : ∀ i, b' i + Matrix.mulVec A' b i = 0)
    (hb' : ∀ i, b i + Matrix.mulVec A b' i = 0)
    {p : Poly} (hp : IsQuadratic p) :
    IsQuadratic ((affineEquiv A A' b b' hAA' hA'A hb hb').symm p) := by
  change IsQuadratic (affineHom A' b' p)
  exact isQuadratic_affineHom A' b' hp

theorem isQuartic_affineEquiv_symm
    (A A' : Matrix (Fin 2) (Fin 2) ℝ) (b b' : Fin 2 → ℝ)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (hb : ∀ i, b' i + Matrix.mulVec A' b i = 0)
    (hb' : ∀ i, b i + Matrix.mulVec A b' i = 0)
    {p : Poly} (hp : IsQuartic p) :
    IsQuartic ((affineEquiv A A' b b' hAA' hA'A hb hb').symm p) := by
  change IsQuartic (affineHom A' b' p)
  exact isQuartic_affineHom A' b' hp

theorem isAdmissiblePoint_mapVec_of_equiv
    (e : Poly ≃ₐ[ℝ] Poly)
    (he : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    {u : RankFourVec} (hu : IsAdmissiblePoint u) :
    IsAdmissiblePoint (mapVec e.toAlgHom u) := by
  intro i
  exact he (hu i)

theorem isAdmissiblePoint_mapVec_affineEquiv
    (A A' : Matrix (Fin 2) (Fin 2) ℝ) (b b' : Fin 2 → ℝ)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (hb : ∀ i, b' i + Matrix.mulVec A' b i = 0)
    (hb' : ∀ i, b i + Matrix.mulVec A b' i = 0)
    {u : RankFourVec} (hu : IsAdmissiblePoint u) :
    IsAdmissiblePoint
      (mapVec (affineEquiv A A' b b' hAA' hA'A hb hb').toAlgHom u) := by
  refine isAdmissiblePoint_mapVec_of_equiv
    (e := affineEquiv A A' b b' hAA' hA'A hb hb')
    (he := fun {_} hp => isQuadratic_affineEquiv A A' b b' hAA' hA'A hb hb' hp)
    hu

theorem isSOSQuartic_map_of_equiv
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuartic : ∀ {p : Poly}, IsQuartic p → IsQuartic (e p))
    {p : Poly} (hp : IsSOSQuartic p) :
    IsSOSQuartic (e p) := by
  rcases hp with ⟨hpQuartic, k, qs, hqs, hpq⟩
  refine ⟨heQuartic hpQuartic, k, fun i => e (qs i), ?_, ?_⟩
  · intro i
    exact heQuad (hqs i)
  · calc
      e p = e (∑ i : Fin k, (qs i) ^ 2) := by rw [hpq]
      _ = ∑ i : Fin k, e ((qs i) ^ 2) := by simp
      _ = ∑ i : Fin k, (e (qs i)) ^ 2 := by simp

theorem isSOSQuartic_affineEquiv
    (A A' : Matrix (Fin 2) (Fin 2) ℝ) (b b' : Fin 2 → ℝ)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (hb : ∀ i, b' i + Matrix.mulVec A' b i = 0)
    (hb' : ∀ i, b i + Matrix.mulVec A b' i = 0)
    {p : Poly} (hp : IsSOSQuartic p) :
    IsSOSQuartic ((affineEquiv A A' b b' hAA' hA'A hb hb') p) := by
  refine isSOSQuartic_map_of_equiv
    (e := affineEquiv A A' b b' hAA' hA'A hb hb')
    (heQuad := fun {_} hp => isQuadratic_affineEquiv A A' b b' hAA' hA'A hb hb' hp)
    (heQuartic := fun {_} hp => isQuartic_affineEquiv A A' b b' hAA' hA'A hb hb' hp)
    hp

theorem residual_eq_zero_mapVec_iff_of_equiv
    (e : Poly ≃ₐ[ℝ] Poly) (p : Poly) (u : RankFourVec) :
    residual (e p) (mapVec e.toAlgHom u) = 0 ↔ residual p u = 0 := by
  constructor
  · intro h
    have h' := congrArg e.symm h
    rw [residual_mapVec_equiv_inv_apply] at h'
    simpa using h'
  · intro h
    simpa [h] using residual_mapVec (φ := e.toAlgHom) p u

theorem isSOCP_mapVec_affineEquiv
    (A A' : Matrix (Fin 2) (Fin 2) ℝ) (b b' : Fin 2 → ℝ)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (hb : ∀ i, b' i + Matrix.mulVec A' b i = 0)
    (hb' : ∀ i, b i + Matrix.mulVec A b' i = 0)
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hsocp : IsSOCP B p u) :
    IsSOCP
      (dotTransport (affineEquiv A A' b b' hAA' hA'A hb hb') B)
      ((affineEquiv A A' b b' hAA' hA'A hb hb') p)
      (mapVec (affineEquiv A A' b b' hAA' hA'A hb hb').toAlgHom u) := by
  refine isSOCP_mapVec_of_equiv
    (e := affineEquiv A A' b b' hAA' hA'A hb hb')
    (heSymm := fun {_} hp => isQuadratic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hp)
    hsocp

end TernaryQuartic
