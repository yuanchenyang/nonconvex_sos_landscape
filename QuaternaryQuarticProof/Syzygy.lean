import QuaternaryQuarticProof.Catalecticant

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace QuaternaryQuartic

open scoped BigOperators

def HasSyzygyCertificate (B : DotForm) (p : Poly) (u : RankSevenVec) (q : Poly) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι),
    ∃ (α : ι → Fin 7 → ℝ) (n : ι → Poly) (β : Fin 7 → ℝ),
      (∀ j, n j ∈ catalecticantKernel B p u) ∧
        (∑ j : ι, relationPoly u (α j) * n j) = relationPoly u β * q ∧
          β ≠ 0

def syzygyDirection {ι : Type*} [Fintype ι]
    (α : ι → Fin 7 → ℝ) (n : ι → Poly) (β : Fin 7 → ℝ) (q : Poly) :
    RankSevenVec :=
  fun i => (∑ j : ι, α j i • n j) - β i • q

theorem syzygyDirection_admissible {ι : Type*} [Fintype ι]
    (α : ι → Fin 7 → ℝ) {n : ι → Poly} (β : Fin 7 → ℝ) {q : Poly}
    (hn : ∀ j, IsQuadratic (n j)) (hq : IsQuadratic q) :
    IsAdmissibleDirection (syzygyDirection α n β q) := by
  intro i
  unfold syzygyDirection IsQuadratic
  refine (MvPolynomial.totalDegree_sub _ _).trans ?_
  refine max_le ?_ ?_
  · refine MvPolynomial.totalDegree_finsetSum_le ?_
    intro j _hj
    exact (MvPolynomial.totalDegree_smul_le (α j i) (n j)).trans (hn j)
  · exact (MvPolynomial.totalDegree_smul_le (β i) q).trans hq

private theorem sum_mul_sum_comm {ι : Type*} [Fintype ι]
    (α : ι → Fin 7 → ℝ) (u : RankSevenVec) (n : ι → Poly) :
    (∑ i : Fin 7, ∑ j : ι, (α j i • u i) * n j) =
      ∑ j : ι, relationPoly u (α j) * n j := by
  classical
  calc
    (∑ i : Fin 7, ∑ j : ι, (α j i • u i) * n j) =
        ∑ j : ι, ∑ i : Fin 7, (α j i • u i) * n j := by
          rw [Finset.sum_comm]
    _ = ∑ j : ι, relationPoly u (α j) * n j := by
      refine Finset.sum_congr rfl ?_
      intro j _hj
      rw [relationPoly, Finset.sum_mul]

theorem A_syzygyDirection {ι : Type*} [Fintype ι]
    (u : RankSevenVec) (α : ι → Fin 7 → ℝ) (n : ι → Poly)
    (β : Fin 7 → ℝ) (q : Poly) :
    A u (syzygyDirection α n β q) =
      (∑ j : ι, relationPoly u (α j) * n j) - relationPoly u β * q := by
  classical
  unfold A syzygyDirection
  calc
    (∑ i : Fin 7, u i * ((∑ j : ι, α j i • n j) - β i • q)) =
        (∑ i : Fin 7, ∑ j : ι, (α j i • u i) * n j) -
          ∑ i : Fin 7, (β i • u i) * q := by
            simp [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
    _ = (∑ j : ι, relationPoly u (α j) * n j) - relationPoly u β * q := by
      rw [sum_mul_sum_comm, relationPoly, Finset.sum_mul]

theorem A_syzygyDirection_eq_zero {ι : Type*} [Fintype ι]
    {u : RankSevenVec} {α : ι → Fin 7 → ℝ} {n : ι → Poly}
    {β : Fin 7 → ℝ} {q : Poly}
    (hsyzygy : (∑ j : ι, relationPoly u (α j) * n j) = relationPoly u β * q) :
    A u (syzygyDirection α n β q) = 0 := by
  rw [A_syzygyDirection, hsyzygy, sub_self]

private theorem kernel_linear_combo_mem {ι : Type*} [Fintype ι]
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (α : ι → ℝ) {n : ι → Poly}
    (hnK : ∀ j, n j ∈ catalecticantKernel B p u) :
    (∑ j : ι, α j • n j) ∈ catalecticantKernel B p u := by
  exact Submodule.sum_mem _ fun j _hj =>
    Submodule.smul_mem _ (α j) (hnK j)

private theorem dot_sigma_sum_left {B : DotForm} (v : RankSevenVec) (r : Poly) :
    B (sigma v) r = ∑ i : Fin 7, B ((v i)^2) r := by
  classical
  unfold sigma
  refine Finset.induction_on (Finset.univ : Finset (Fin 7)) ?_ ?_
  · simp
  · intro i s hi ih
    calc
      B ((insert i s).sum fun i => (v i)^2) r =
          B ((v i)^2 + s.sum fun i => (v i)^2) r := by
            simp [hi]
      _ = B ((v i)^2) r + B (s.sum fun i => (v i)^2) r := by
        simp
      _ = B ((v i)^2) r + s.sum (fun i => B ((v i)^2) r) := by
        rw [ih]
      _ = (insert i s).sum fun i => B ((v i)^2) r := by
        simp [hi]

private theorem dot_syzygyDirection_coord_sq
    {ι : Type*} [Fintype ι] {B : DotForm} {p : Poly} {u : RankSevenVec}
    (α : ι → ℝ) {n : ι → Poly} (β : ℝ) {q : Poly}
    (hnK : ∀ j, n j ∈ catalecticantKernel B p u)
    (hq : IsQuadratic q) :
    B (((∑ j : ι, α j • n j) - β • q)^2) (residual p u) =
      β^2 * B (q^2) (residual p u) := by
  let N : Poly := ∑ j : ι, α j • n j
  have hNK : N ∈ catalecticantKernel B p u :=
    kernel_linear_combo_mem α hnK
  have hN_N : B (N * N) (residual p u) = 0 :=
    hNK.2 N hNK.1
  have hN_q : B (N * q) (residual p u) = 0 :=
    hNK.2 q hq
  have hq_N : B (q * N) (residual p u) = 0 := by
    rw [mul_comm]
    exact hN_q
  have hsquare :
      (N - β • q)^2 =
        N * N - N * (β • q) - (β • q) * N + (β^2) • (q^2) := by
    rw [pow_two]
    simp [MvPolynomial.smul_eq_C_mul]
    ring
  calc
    B (((∑ j : ι, α j • n j) - β • q)^2) (residual p u) =
        B ((N - β • q)^2) (residual p u) := by rfl
    _ = B (N * N - N * (β • q) - (β • q) * N + (β^2) • (q^2))
          (residual p u) := by
      rw [hsquare]
    _ = β^2 * B (q^2) (residual p u) := by
      simp [sub_eq_add_neg, hN_N, hN_q, hq_N]

theorem dot_sigma_syzygyDirection
    {ι : Type*} [Fintype ι] {B : DotForm} {p : Poly} {u : RankSevenVec}
    (α : ι → Fin 7 → ℝ) {n : ι → Poly} (β : Fin 7 → ℝ) {q : Poly}
    (hnK : ∀ j, n j ∈ catalecticantKernel B p u)
    (hq : IsQuadratic q) :
    B (sigma (syzygyDirection α n β q)) (residual p u) =
      (∑ i : Fin 7, (β i)^2) * B (q^2) (residual p u) := by
  classical
  rw [dot_sigma_sum_left]
  calc
    (∑ i : Fin 7,
        B ((syzygyDirection α n β q i)^2) (residual p u)) =
        ∑ i : Fin 7, (β i)^2 * B (q^2) (residual p u) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          exact dot_syzygyDirection_coord_sq (fun j => α j i) (β i) hnK hq
    _ = (∑ i : Fin 7, (β i)^2) * B (q^2) (residual p u) := by
      rw [Finset.sum_mul]

theorem false_of_syzygy_negative_curvature
    {ι : Type*} [Fintype ι] {B : DotForm} {p : Poly} {u : RankSevenVec}
    {α : ι → Fin 7 → ℝ} {n : ι → Poly} {β : Fin 7 → ℝ} {q : Poly}
    (hsocp : IsSOCP B p u)
    (hnK : ∀ j, n j ∈ catalecticantKernel B p u)
    (hq : IsQuadratic q)
    (hsyzygy : (∑ j : ι, relationPoly u (α j) * n j) = relationPoly u β * q)
    (hβ : β ≠ 0)
    (hnegq : B (q^2) (residual p u) < 0) :
    False := by
  let v : RankSevenVec := syzygyDirection α n β q
  have hnquad : ∀ j, IsQuadratic (n j) := fun j => (hnK j).1
  have hvadm : IsAdmissibleDirection v :=
    syzygyDirection_admissible α β hnquad hq
  have hA : A u v = 0 := by
    exact A_syzygyDirection_eq_zero hsyzygy
  have hsum_pos : 0 < ∑ i : Fin 7, (β i)^2 :=
    sum_sq_pos_of_ne_zero β hβ
  have hsigma :
      B (sigma v) (residual p u) =
        (∑ i : Fin 7, (β i)^2) * B (q^2) (residual p u) := by
    exact dot_sigma_syzygyDirection α β hnK hq
  have hneg_sigma : B (sigma v) (residual p u) < 0 := by
    rw [hsigma]
    nlinarith
  exact false_of_negative_curvature_direction hsocp hvadm hA hneg_sigma

theorem residual_eq_zero_of_syzygy_certificates_for_negative_squares
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hcert :
      ∀ q : Poly, IsQuadratic q → B (q^2) (residual p u) < 0 →
        HasSyzygyCertificate B p u q) :
    residual p u = 0 := by
  by_contra hres
  rcases exists_negative_sos_summand_of_nonzero_residual
      (B := B) hu hp hsocp.1 hres with ⟨q, hq, hnegq⟩
  rcases hcert q hq hnegq with ⟨ι, hι, α, n, β, hnK, hsyzygy, hβ⟩
  letI : Fintype ι := hι
  exact false_of_syzygy_negative_curvature
    (B := B) (p := p) (u := u) (α := α) (n := n) (β := β) (q := q)
    hsocp hnK hq hsyzygy hβ hnegq

theorem residual_eq_zero_of_rank_case_syzygy_certificates
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hcase :
      ∀ q : Poly, IsQuadratic q → B (q^2) (residual p u) < 0 →
        LinearMap.ker (relationPolyLin u) = ⊥ →
          (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 1 →
            HasSyzygyCertificate B p u q) ∧
          (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 2 →
            HasSyzygyCertificate B p u q) ∧
          (Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3 →
            HasSyzygyCertificate B p u q)) :
    residual p u = 0 := by
  rcases residual_eq_zero_or_relationPolyLin_ker_eq_bot
      (B := B) hu hp hsocp with hres | hker
  · exact hres
  · refine residual_eq_zero_of_syzygy_certificates_for_negative_squares
      (B := B) hu hp hsocp ?_
    intro q hq hnegq
    have hrank_cases :=
      catalecticantMap_rank_eq_one_or_two_or_three
        (B := B) (p := p) (u := u) hu hsocp.1 hker hq hnegq
    rcases hcase q hq hnegq hker with ⟨hcase1, hcase2, hcase3⟩
    rcases hrank_cases with hrank1 | hrank23
    · exact hcase1 hrank1
    · rcases hrank23 with hrank2 | hrank3
      · exact hcase2 hrank2
      · exact hcase3 hrank3

theorem residual_eq_zero_of_exists_negative_syzygy_certificate
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    (hsocp : IsSOCP B p u)
    (hcert :
      residual p u ≠ 0 →
        ∃ q : Poly, IsQuadratic q ∧
          B (q^2) (residual p u) < 0 ∧ HasSyzygyCertificate B p u q) :
    residual p u = 0 := by
  by_contra hres
  rcases hcert hres with ⟨q, hq, hnegq, hcertq⟩
  rcases hcertq with ⟨ι, hι, α, n, β, hnK, hsyzygy, hβ⟩
  letI : Fintype ι := hι
  exact false_of_syzygy_negative_curvature
    (B := B) (p := p) (u := u) (α := α) (n := n) (β := β) (q := q)
    hsocp hnK hq hsyzygy hβ hnegq

theorem residual_eq_zero_of_rank_case_exists_negative_syzygy_certificate
    {B : DotForm} [Fact B.toQuadraticMap.PosDef] {p : Poly} {u : RankSevenVec}
    (hu : IsAdmissiblePoint u)
    (hp : IsSOSQuartic p)
    (hsocp : IsSOCP B p u)
    (hcase :
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
              B (q^2) (residual p u) < 0 ∧ HasSyzygyCertificate B p u q)) :
    residual p u = 0 := by
  refine residual_eq_zero_of_exists_negative_syzygy_certificate
    (B := B) (p := p) (u := u) hsocp ?_
  intro hres
  rcases residual_eq_zero_or_relationPolyLin_ker_eq_bot
      (B := B) hu hp hsocp with hzero | hker
  · exact False.elim (hres hzero)
  · rcases exists_negative_sos_summand_of_nonzero_residual
        (B := B) hu hp hsocp.1 hres with ⟨q₀, hq₀, hnegq₀⟩
    have hrank_cases :=
      catalecticantMap_rank_eq_one_or_two_or_three
        (B := B) (p := p) (u := u) hu hsocp.1 hker hq₀ hnegq₀
    rcases hcase hres hker with ⟨hcase1, hcase2, hcase3⟩
    rcases hrank_cases with hrank1 | hrank23
    · exact hcase1 hrank1
    · rcases hrank23 with hrank2 | hrank3
      · exact hcase2 hrank2
      · exact hcase3 hrank3

theorem hasSyzygyCertificate_of_product_identity
    {ι : Type} [Fintype ι] {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    {m : ι → quadSubmodule} {n : ι → Poly} {s : quadSubmodule} {q : Poly}
    (hmL : ∀ j, m j ∈ spanUQuad hu)
    (hnK : ∀ j, n j ∈ catalecticantKernel B p u)
    (hsL : s ∈ spanUQuad hu)
    (hsne : s.1 ≠ 0)
    (hprod : (∑ j : ι, (m j).1 * n j) = s.1 * q) :
    HasSyzygyCertificate B p u q := by
  classical
  have hmCoeff : ∀ j, ∃ c : Fin 7 → ℝ, relationPoly u c = (m j).1 := by
    intro j
    exact exists_relationPoly_eq_of_mem_spanUQuad (u := u) (hu := hu) (x := m j) (hmL j)
  choose α hα using hmCoeff
  rcases exists_relationPoly_eq_of_mem_spanUQuad (u := u) (hu := hu) (x := s) hsL with
    ⟨β, hβeq⟩
  have hβne : β ≠ 0 := by
    intro hβzero
    apply hsne
    calc
      s.1 = relationPoly u β := hβeq.symm
      _ = relationPoly u 0 := by rw [hβzero]
      _ = 0 := by simp [relationPoly]
  refine ⟨ι, inferInstance, α, n, β, hnK, ?_, hβne⟩
  calc
    (∑ j : ι, relationPoly u (α j) * n j) =
        ∑ j : ι, (m j).1 * n j := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          rw [hα j]
    _ = s.1 * q := hprod
    _ = relationPoly u β * q := by rw [hβeq]

theorem hasSyzygyCertificate_of_mem_linProductSubmodule
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    {x : linSubmodule} {M A : Submodule ℝ linSubmodule} {s : quadSubmodule}
    (hxM_L : ∀ m : M, linProduct x m.1 ∈ spanUQuad hu)
    (hxA_K : ∀ a : A, (linProduct x a.1 : quadSubmodule).1 ∈ catalecticantKernel B p u)
    (hsL : s ∈ spanUQuad hu)
    (hsne : s.1 ≠ 0)
    (hsMA : s ∈ linProductSubmodule M A) :
    HasSyzygyCertificate B p u (linProduct x x).1 := by
  classical
  rcases Finsupp.mem_span_range_iff_exists_finsupp.mp hsMA with ⟨c, hc⟩
  let ι := {y : M × A // y ∈ c.support}
  letI : Fintype ι := Finset.fintypeCoeSort c.support
  let m : ι → quadSubmodule := fun j => linProduct x j.1.1.1
  let n : ι → Poly := fun j => c j.1 • (linProduct x j.1.2.1 : quadSubmodule).1
  refine hasSyzygyCertificate_of_product_identity
    (B := B) (p := p) (u := u) (hu := hu)
    (m := m) (n := n) (s := s) (q := (linProduct x x).1) ?_ ?_ hsL hsne ?_
  · intro j
    exact hxM_L j.1.1
  · intro j
    exact Submodule.smul_mem _ (c j.1) (hxA_K j.1.2)
  · have hcSubtype :
        (∑ j : ι, c j.1 • (linProduct j.1.1.1 j.1.2.1 : quadSubmodule)) = s := by
      rw [← hc]
      change
        (∑ j : {y : M × A // y ∈ c.support},
            c j.1 • (linProduct j.1.1.1 j.1.2.1 : quadSubmodule)) =
          ∑ y ∈ c.support, c y • (linProduct y.1.1 y.2.1 : quadSubmodule)
      rw [show (Finset.univ : Finset {y : M × A // y ∈ c.support}) =
          c.support.attach by
        ext y
        simp]
      simpa using
        (Finset.sum_attach c.support
          (fun y : M × A => c y • (linProduct y.1.1 y.2.1 : quadSubmodule)))
    have hcPoly :
        (∑ j : ι, c j.1 • (linProduct j.1.1.1 j.1.2.1 : quadSubmodule).1) = s.1 := by
      calc
        (∑ j : ι, c j.1 • (linProduct j.1.1.1 j.1.2.1 : quadSubmodule).1) =
            ((∑ j : ι,
              c j.1 • (linProduct j.1.1.1 j.1.2.1 : quadSubmodule)) : quadSubmodule).1 := by
              change
                Finset.sum (Finset.univ : Finset ι)
                    (fun j =>
                      (quadSubmodule.subtype)
                        (c j.1 • (linProduct j.1.1.1 j.1.2.1 : quadSubmodule))) =
                  (quadSubmodule.subtype)
                    (Finset.sum (Finset.univ : Finset ι)
                      (fun j =>
                        c j.1 • (linProduct j.1.1.1 j.1.2.1 : quadSubmodule)))
              exact
                (map_sum (quadSubmodule.subtype)
                  (fun j : ι =>
                    c j.1 • (linProduct j.1.1.1 j.1.2.1 : quadSubmodule))
                  Finset.univ).symm
        _ = s.1 := congrArg (fun q : quadSubmodule => (q : Poly)) hcSubtype
    calc
      (∑ j : ι, (m j).1 * n j) =
          ∑ j : ι,
            (linProduct x j.1.1.1 : quadSubmodule).1 *
              (c j.1 • (linProduct x j.1.2.1 : quadSubmodule).1) := by
            rfl
      _ = ∑ j : ι,
            c j.1 • ((linProduct j.1.1.1 j.1.2.1 : quadSubmodule).1 *
              (linProduct x x : quadSubmodule).1) := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            simp [linProduct, mul_comm, mul_left_comm]
      _ = (∑ j : ι,
            c j.1 • (linProduct j.1.1.1 j.1.2.1 : quadSubmodule).1) *
              (linProduct x x : quadSubmodule).1 := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl ?_
            intro j _hj
            simp
      _ = s.1 * (linProduct x x : quadSubmodule).1 := by
            rw [hcPoly]

theorem hasSyzygyCertificate_of_rank_three_kernel_product_identity
    {ι : Type} [Fintype ι] {B : DotForm} {p : Poly} {u : RankSevenVec}
    {hu : IsAdmissiblePoint u}
    (hfocp : IsFOCP B p u)
    (hrelker : LinearMap.ker (relationPolyLin u) = ⊥)
    (hrank : Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) = 3)
    {m : ι → quadSubmodule} {n : ι → Poly} {s : quadSubmodule} {q : Poly}
    (hmK : ∀ j, m j ∈ LinearMap.ker (catalecticantMap B p u))
    (hnK : ∀ j, n j ∈ catalecticantKernel B p u)
    (hsK : s ∈ LinearMap.ker (catalecticantMap B p u))
    (hsne : s.1 ≠ 0)
    (hprod : (∑ j : ι, (m j).1 * n j) = s.1 * q) :
    HasSyzygyCertificate B p u q := by
  have hspan_eq_ker :
      spanUQuad hu = LinearMap.ker (catalecticantMap B p u) :=
    spanUQuad_eq_ker_catalecticantMap_of_rank_three
      (B := B) (p := p) (u := u) hu hfocp hrelker hrank
  refine hasSyzygyCertificate_of_product_identity
    (B := B) (p := p) (u := u) (hu := hu)
    (m := m) (n := n) (s := s) (q := q) ?_ hnK ?_ hsne hprod
  · intro j
    rw [hspan_eq_ker]
    exact hmK j
  · rw [hspan_eq_ker]
    exact hsK

end QuaternaryQuartic
