import TernaryQuarticProof.AffineSocpTransform
import TernaryQuarticProof.FactorTransform

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace TernaryQuartic

/-- Pull back a representative no-spurious-SOCP theorem through an affine
polynomial equivalence followed by an orthogonal factor-coordinate mixing. The
normal-form data needed later is exactly the equality identifying the
transformed SOCP point with the representative. -/
theorem residual_eq_zero_of_socp_of_eq_mix_mapVec
    (uRep : RankFourVec)
    (hRep :
      ∀ {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly},
        IsSOSQuartic p → IsSOCP B p uRep → residual p uRep = 0)
    (e : Poly ≃ₐ[ℝ] Poly)
    (heQuad : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e p))
    (heQuadSymm : ∀ {p : Poly}, IsQuadratic p → IsQuadratic (e.symm p))
    (heQuarticSymm : ∀ {p : Poly}, IsQuartic p → IsQuartic (e.symm p))
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hMtM : M.transpose * M = 1)
    (hMMt : M * M.transpose = 1)
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (huRep : mix M.transpose (mapVec e.symm.toAlgHom u) = uRep)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  let B0 : DotForm := dotTransport e.symm B
  have hB0 : IsPositiveDefinite B0 := by
    dsimp [B0]
    exact isPositiveDefinite_dotTransport e.symm hB
  letI : Fact B0.toQuadraticMap.PosDef := ⟨hB0⟩
  have hp0 : IsSOSQuartic (e.symm p) := by
    exact isSOSQuartic_map_of_equiv
      (e := e.symm)
      (heQuad := fun {_} hpq => heQuadSymm hpq)
      (heQuartic := fun {_} hpq => heQuarticSymm hpq)
      hp
  have hsocp0 : IsSOCP B0 (e.symm p) (mapVec e.symm.toAlgHom u) := by
    dsimp [B0]
    simpa using
      (isSOCP_mapVec_of_equiv
        (e := e.symm)
        (heSymm := fun {_} hpq => heQuad hpq)
        hsocp)
  have hsocpRep :
      IsSOCP B0 (e.symm p) uRep := by
    have hsocpMix :
        IsSOCP B0 (e.symm p) (mix M.transpose (mapVec e.symm.toAlgHom u)) := by
      exact isSOCP_mix_of_orthogonal
        (M := M.transpose)
        (B := B0)
        (p := e.symm p)
        (u := mapVec e.symm.toAlgHom u)
        (by simpa using hMMt)
        (by simpa using hMtM)
        hsocp0
    rw [huRep] at hsocpMix
    exact hsocpMix
  have hresRep : residual (e.symm p) uRep = 0 := hRep hp0 hsocpRep
  have hresMap :
      residual (e.symm p) (mapVec e.symm.toAlgHom u) = 0 := by
    have hmix :
        residual (e.symm p) uRep =
          residual (e.symm p) (mapVec e.symm.toAlgHom u) := by
      have hmix0 :=
        (residual_mix_of_transpose_mul_self_eq_one
          (M := M.transpose)
          (p := e.symm p)
          (u := mapVec e.symm.toAlgHom u)
          (by simpa using hMMt))
      rw [huRep] at hmix0
      exact hmix0
    rw [← hmix]
    exact hresRep
  exact (residual_eq_zero_mapVec_iff_of_equiv
    (e := e.symm) (p := p) (u := u)).mp hresMap

theorem residual_eq_zero_of_socp_of_eq_mix_affineEquiv
    (uRep : RankFourVec)
    (hRep :
      ∀ {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly},
        IsSOSQuartic p → IsSOCP B p uRep → residual p uRep = 0)
    (A A' : Matrix (Fin 2) (Fin 2) ℝ) (b b' : Fin 2 → ℝ)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (hb : ∀ i, b' i + Matrix.mulVec A' b i = 0)
    (hb' : ∀ i, b i + Matrix.mulVec A b' i = 0)
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hMtM : M.transpose * M = 1)
    (hMMt : M * M.transpose = 1)
    {B : DotForm} {p : Poly} {u : RankFourVec}
    (hB : IsPositiveDefinite B)
    (hp : IsSOSQuartic p)
    (huRep :
      mix M.transpose
        (mapVec (affineEquiv A A' b b' hAA' hA'A hb hb').symm.toAlgHom u) = uRep)
    (hsocp : IsSOCP B p u) :
    residual p u = 0 := by
  exact residual_eq_zero_of_socp_of_eq_mix_mapVec
    (uRep := uRep)
    (hRep := hRep)
    (e := affineEquiv A A' b b' hAA' hA'A hb hb')
    (heQuad := fun {_} hpq => isQuadratic_affineEquiv A A' b b' hAA' hA'A hb hb' hpq)
    (heQuadSymm := fun {_} hpq => isQuadratic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (heQuarticSymm := fun {_} hpq => isQuartic_affineEquiv_symm A A' b b' hAA' hA'A hb hb' hpq)
    (M := M)
    hMtM hMMt hB hp huRep hsocp

end TernaryQuartic
