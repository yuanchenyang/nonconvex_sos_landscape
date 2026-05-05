import QuaternaryQuarticProof.Syzygy

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace QuaternaryQuartic

def binaryQuarticEval (a b c d e x y : ℝ) : ℝ :=
  a * x^4 + 4 * b * x^3 * y + 6 * c * x^2 * y^2 + 4 * d * x * y^3 + e * y^4

def binaryQuadraticEval (r s t x y : ℝ) : ℝ :=
  r * x^2 + s * x * y + t * y^2

def IsBinaryQuarticPullback
    (a b c d e A B C D E α β γ δ : ℝ) : Prop :=
  ∀ X Y : ℝ,
    binaryQuarticEval A B C D E X Y =
      binaryQuarticEval a b c d e (α * X + β * Y) (γ * X + δ * Y)

def IsBinaryQuadraticPullback
    (r s t R S T α β γ δ : ℝ) : Prop :=
  ∀ X Y : ℝ,
    binaryQuadraticEval R S T X Y =
      binaryQuadraticEval r s t (α * X + β * Y) (γ * X + δ * Y)

theorem isBinaryQuadraticPullback_id (r s t : ℝ) :
    IsBinaryQuadraticPullback r s t r s t 1 0 0 1 := by
  intro X Y
  simp [binaryQuadraticEval]

theorem isBinaryQuadraticPullback_swap (r s t : ℝ) :
    IsBinaryQuadraticPullback r s t t s r 0 1 1 0 := by
  intro X Y
  unfold binaryQuadraticEval
  ring

theorem IsBinaryQuadraticPullback.comp
    {r s t R S T P Q U α β γ δ mu nu xi om : ℝ}
    (h1 : IsBinaryQuadraticPullback r s t R S T α β γ δ)
    (h2 : IsBinaryQuadraticPullback R S T P Q U mu nu xi om) :
    IsBinaryQuadraticPullback r s t P Q U
      (α * mu + β * xi) (α * nu + β * om)
      (γ * mu + δ * xi) (γ * nu + δ * om) := by
  intro X Y
  rw [h2 X Y, h1 (mu * X + nu * Y) (xi * X + om * Y)]
  unfold binaryQuadraticEval
  ring

theorem isBinaryQuadraticPullback_diagonal
    (r s t α δ : ℝ) :
    IsBinaryQuadraticPullback r s t
      (r * α^2) (s * α * δ) (t * δ^2) α 0 0 δ := by
  intro X Y
  unfold binaryQuadraticEval
  ring

theorem isBinaryQuadraticPullback_shearX
    (r s t tau : ℝ) :
    IsBinaryQuadraticPullback r s t
      r
      (2 * r * tau + s)
      (r * tau^2 + s * tau + t)
      1 tau 0 1 := by
  intro X Y
  unfold binaryQuadraticEval
  ring

theorem isBinaryQuadraticPullback_shearY
    (r s t tau : ℝ) :
    IsBinaryQuadraticPullback r s t
      (r + s * tau + t * tau^2)
      (s + 2 * t * tau)
      t
      1 0 tau 1 := by
  intro X Y
  unfold binaryQuadraticEval
  ring

theorem isBinaryQuarticPullback_id (a b c d e : ℝ) :
    IsBinaryQuarticPullback a b c d e a b c d e 1 0 0 1 := by
  intro X Y
  simp [binaryQuarticEval]

theorem isBinaryQuarticPullback_swap (a b c d e : ℝ) :
    IsBinaryQuarticPullback a b c d e e d c b a 0 1 1 0 := by
  intro X Y
  unfold binaryQuarticEval
  ring

theorem IsBinaryQuarticPullback.comp
    {a b c d e A B C D E P Q R S T α β γ δ mu nu xi om : ℝ}
    (h1 : IsBinaryQuarticPullback a b c d e A B C D E α β γ δ)
    (h2 : IsBinaryQuarticPullback A B C D E P Q R S T mu nu xi om) :
    IsBinaryQuarticPullback a b c d e P Q R S T
      (α * mu + β * xi) (α * nu + β * om)
      (γ * mu + δ * xi) (γ * nu + δ * om) := by
  intro X Y
  rw [h2 X Y, h1 (mu * X + nu * Y) (xi * X + om * Y)]
  unfold binaryQuarticEval
  ring

theorem isBinaryQuarticPullback_diagonal
    (a b c d e α δ : ℝ) :
    IsBinaryQuarticPullback a b c d e
      (a * α^4) (b * α^3 * δ) (c * α^2 * δ^2)
      (d * α * δ^3) (e * δ^4) α 0 0 δ := by
  intro X Y
  unfold binaryQuarticEval
  ring

theorem isBinaryQuarticPullback_shearX
    (a b c d e t : ℝ) :
    IsBinaryQuarticPullback a b c d e
      a
      (a * t + b)
      (a * t^2 + 2 * b * t + c)
      (a * t^3 + 3 * b * t^2 + 3 * c * t + d)
      (a * t^4 + 4 * b * t^3 + 6 * c * t^2 + 4 * d * t + e)
      1 t 0 1 := by
  intro X Y
  unfold binaryQuarticEval
  ring

theorem isBinaryQuarticPullback_shearY
    (a b c d e t : ℝ) :
    IsBinaryQuarticPullback a b c d e
      (a + 4 * b * t + 6 * c * t^2 + 4 * d * t^3 + e * t^4)
      (b + 3 * c * t + 3 * d * t^2 + e * t^3)
      (c + 2 * d * t + e * t^2)
      (d + e * t)
      e
      1 0 t 1 := by
  intro X Y
  unfold binaryQuarticEval
  ring

def binaryHankelQuad (a b c d e r s t : ℝ) : ℝ :=
  a * r^2 + 2 * b * r * s + 2 * c * r * t + c * s^2 + 2 * d * s * t + e * t^2

def binaryKernelDiscriminant (r s t : ℝ) : ℝ :=
  s^2 - 4 * r * t

theorem binaryKernelDiscriminant_swap (r s t : ℝ) :
    binaryKernelDiscriminant t s r = binaryKernelDiscriminant r s t := by
  unfold binaryKernelDiscriminant
  ring

theorem binaryKernelDiscriminant_diagonal (r s t α δ : ℝ) :
    binaryKernelDiscriminant (r * α^2) (s * α * δ) (t * δ^2) =
      (α * δ)^2 * binaryKernelDiscriminant r s t := by
  unfold binaryKernelDiscriminant
  ring

theorem binaryKernelDiscriminant_shearX (r s t tau : ℝ) :
    binaryKernelDiscriminant r (2 * r * tau + s) (r * tau^2 + s * tau + t) =
      binaryKernelDiscriminant r s t := by
  unfold binaryKernelDiscriminant
  ring

theorem binaryKernelDiscriminant_shearY (r s t tau : ℝ) :
    binaryKernelDiscriminant (r + s * tau + t * tau^2) (s + 2 * t * tau) t =
      binaryKernelDiscriminant r s t := by
  unfold binaryKernelDiscriminant
  ring

theorem parabolic_shearX_mixedCoeff_eq_zero
    {r s : ℝ} (hr : r ≠ 0) :
    2 * r * (-s / (2 * r)) + s = 0 := by
  field_simp [hr]
  ring

theorem parabolic_shearX_ySqCoeff_eq_zero
    {r s t : ℝ} (hr : r ≠ 0)
    (hdisc : binaryKernelDiscriminant r s t = 0) :
    r * (-s / (2 * r))^2 + s * (-s / (2 * r)) + t = 0 := by
  have hdisc' : s^2 = 4 * r * t := by
    unfold binaryKernelDiscriminant at hdisc
    nlinarith
  field_simp [hr]
  nlinarith

theorem isBinaryQuadraticPullback_parabolic_shearX_to_xSq
    {r s t : ℝ} (hr : r ≠ 0)
    (hdisc : binaryKernelDiscriminant r s t = 0) :
    IsBinaryQuadraticPullback r s t r 0 0 1 (-s / (2 * r)) 0 1 := by
  convert isBinaryQuadraticPullback_shearX r s t (-s / (2 * r)) using 1
  · exact (parabolic_shearX_mixedCoeff_eq_zero (r := r) (s := s) hr).symm
  · exact (parabolic_shearX_ySqCoeff_eq_zero
      (r := r) (s := s) (t := t) hr hdisc).symm

theorem parabolic_zero_xCoeff_mixedCoeff_eq_zero
    {r s t : ℝ} (hr : r = 0)
    (hdisc : binaryKernelDiscriminant r s t = 0) :
    s = 0 := by
  unfold binaryKernelDiscriminant at hdisc
  rw [hr] at hdisc
  nlinarith [sq_nonneg s]

theorem hyperbolic_shearX_mixedCoeff_eq_sqrt_discriminant
    {r s t : ℝ} (hr : r ≠ 0) :
    2 * r * ((-s + Real.sqrt (binaryKernelDiscriminant r s t)) / (2 * r)) + s =
      Real.sqrt (binaryKernelDiscriminant r s t) := by
  field_simp [hr]
  ring

theorem hyperbolic_shearX_ySqCoeff_eq_zero
    {r s t : ℝ} (hr : r ≠ 0)
    (hdisc_pos : 0 < binaryKernelDiscriminant r s t) :
    r * ((-s + Real.sqrt (binaryKernelDiscriminant r s t)) / (2 * r))^2 +
        s * ((-s + Real.sqrt (binaryKernelDiscriminant r s t)) / (2 * r)) + t =
      0 := by
  let D := binaryKernelDiscriminant r s t
  have hD_nonneg : 0 ≤ D := le_of_lt hdisc_pos
  have hsqrt_sq : (Real.sqrt D)^2 = D := Real.sq_sqrt hD_nonneg
  have hD_def : D = s^2 - 4 * r * t := by
    simp [D, binaryKernelDiscriminant]
  field_simp [hr]
  nlinarith

theorem hyperbolic_shearX_sqrt_discriminant_ne_zero
    {r s t : ℝ}
    (hdisc_pos : 0 < binaryKernelDiscriminant r s t) :
    Real.sqrt (binaryKernelDiscriminant r s t) ≠ 0 := by
  exact ne_of_gt (Real.sqrt_pos_of_pos hdisc_pos)

theorem isBinaryQuadraticPullback_hyperbolic_shearX_to_zero_ySq
    {r s t : ℝ} (hr : r ≠ 0)
    (hdisc_pos : 0 < binaryKernelDiscriminant r s t) :
    IsBinaryQuadraticPullback r s t
      r (Real.sqrt (binaryKernelDiscriminant r s t)) 0
      1 ((-s + Real.sqrt (binaryKernelDiscriminant r s t)) / (2 * r)) 0 1 := by
  convert isBinaryQuadraticPullback_shearX r s t
      ((-s + Real.sqrt (binaryKernelDiscriminant r s t)) / (2 * r)) using 1
  · exact (hyperbolic_shearX_mixedCoeff_eq_sqrt_discriminant
      (r := r) (s := s) (t := t) hr).symm
  · exact (hyperbolic_shearX_ySqCoeff_eq_zero
      (r := r) (s := s) (t := t) hr hdisc_pos).symm

theorem hyperbolic_shearY_xSqCoeff_eq_zero
    {R S : ℝ} (hS : S ≠ 0) :
    R + S * (-R / S) + 0 * (-R / S)^2 = 0 := by
  field_simp [hS]
  ring

theorem hyperbolic_shearY_mixedCoeff_eq
    (R S : ℝ) :
    S + 2 * 0 * (-R / S) = S := by
  ring

theorem isBinaryQuadraticPullback_hyperbolic_shearY_to_xy
    {R S : ℝ} (hS : S ≠ 0) :
    IsBinaryQuadraticPullback R S 0 0 S 0 1 0 (-R / S) 1 := by
  convert isBinaryQuadraticPullback_shearY R S 0 (-R / S) using 1
  · exact (hyperbolic_shearY_xSqCoeff_eq_zero (R := R) (S := S) hS).symm
  · exact (hyperbolic_shearY_mixedCoeff_eq R S).symm

theorem exists_binaryQuadraticPullback_hyperbolic_to_xy_of_xCoeff_ne_zero
    {r s t : ℝ} (hr : r ≠ 0)
    (hdisc_pos : 0 < binaryKernelDiscriminant r s t) :
    ∃ alpha beta gamma delta S : ℝ,
      S ≠ 0 ∧
        IsBinaryQuadraticPullback r s t 0 S 0 alpha beta gamma delta := by
  let D := binaryKernelDiscriminant r s t
  let tau := (-s + Real.sqrt D) / (2 * r)
  have hfirst :
      IsBinaryQuadraticPullback r s t r (Real.sqrt D) 0 1 tau 0 1 := by
    simpa [D, tau] using
      isBinaryQuadraticPullback_hyperbolic_shearX_to_zero_ySq
        (r := r) (s := s) (t := t) hr hdisc_pos
  have hS : Real.sqrt D ≠ 0 := by
    exact hyperbolic_shearX_sqrt_discriminant_ne_zero
      (r := r) (s := s) (t := t) hdisc_pos
  have hsecond :
      IsBinaryQuadraticPullback r (Real.sqrt D) 0
        0 (Real.sqrt D) 0 1 0 (-r / Real.sqrt D) 1 :=
    isBinaryQuadraticPullback_hyperbolic_shearY_to_xy
      (R := r) (S := Real.sqrt D) hS
  refine ⟨1 + tau * (-r / Real.sqrt D), tau, -r / Real.sqrt D, 1,
    Real.sqrt D, hS, ?_⟩
  simpa [D, tau, add_comm, add_left_comm, add_assoc] using hfirst.comp hsecond

theorem hyperbolic_zero_xCoeff_mixedCoeff_ne_zero
    {r s t : ℝ} (hr : r = 0)
    (hdisc_pos : 0 < binaryKernelDiscriminant r s t) :
    s ≠ 0 := by
  intro hs
  unfold binaryKernelDiscriminant at hdisc_pos
  rw [hr, hs] at hdisc_pos
  norm_num at hdisc_pos

theorem hyperbolic_zero_xCoeff_shearX_ySqCoeff_eq_zero
    {s t : ℝ} (hs : s ≠ 0) :
    s * (-t / s) + t = 0 := by
  field_simp [hs]
  ring

theorem isBinaryQuadraticPullback_hyperbolic_zero_xCoeff_to_xy
    {r s t : ℝ} (hr : r = 0)
    (hdisc_pos : 0 < binaryKernelDiscriminant r s t) :
    IsBinaryQuadraticPullback r s t 0 s 0 1 (-t / s) 0 1 := by
  have hs : s ≠ 0 :=
    hyperbolic_zero_xCoeff_mixedCoeff_ne_zero (r := r) (s := s) (t := t)
      hr hdisc_pos
  subst r
  convert isBinaryQuadraticPullback_shearX 0 s t (-t / s) using 1
  · ring
  · simpa using (hyperbolic_zero_xCoeff_shearX_ySqCoeff_eq_zero
      (s := s) (t := t) hs).symm

theorem exists_binaryQuadraticPullback_hyperbolic_to_xy_of_xCoeff_eq_zero
    {r s t : ℝ} (hr : r = 0)
    (hdisc_pos : 0 < binaryKernelDiscriminant r s t) :
    ∃ alpha beta gamma delta S : ℝ,
      S ≠ 0 ∧
        IsBinaryQuadraticPullback r s t 0 S 0 alpha beta gamma delta := by
  have hs : s ≠ 0 :=
    hyperbolic_zero_xCoeff_mixedCoeff_ne_zero (r := r) (s := s) (t := t)
      hr hdisc_pos
  exact ⟨1, -t / s, 0, 1, s, hs,
    isBinaryQuadraticPullback_hyperbolic_zero_xCoeff_to_xy
      (r := r) (s := s) (t := t) hr hdisc_pos⟩

theorem exists_binaryQuadraticPullback_hyperbolic_to_xy
    {r s t : ℝ}
    (hdisc_pos : 0 < binaryKernelDiscriminant r s t) :
    ∃ alpha beta gamma delta S : ℝ,
      S ≠ 0 ∧
        IsBinaryQuadraticPullback r s t 0 S 0 alpha beta gamma delta := by
  by_cases hr : r = 0
  · exact exists_binaryQuadraticPullback_hyperbolic_to_xy_of_xCoeff_eq_zero
      (r := r) (s := s) (t := t) hr hdisc_pos
  · exact exists_binaryQuadraticPullback_hyperbolic_to_xy_of_xCoeff_ne_zero
      (r := r) (s := s) (t := t) hr hdisc_pos

def binaryHankelMul (a b c d e : ℝ) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![a * v 0 + b * v 1 + c * v 2,
    b * v 0 + c * v 1 + d * v 2,
    c * v 0 + d * v 1 + e * v 2]

def binaryHankelLinearMap (a b c d e : ℝ) :
    (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun := binaryHankelMul a b c d e
  map_add' := by
    intro v w
    ext i
    fin_cases i
    · simp [binaryHankelMul]
      ring
    · simp [binaryHankelMul]
      ring
    · simp [binaryHankelMul]
      ring
  map_smul' := by
    intro r v
    ext i
    fin_cases i
    · simp [binaryHankelMul]
      ring
    · simp [binaryHankelMul]
      ring
    · simp [binaryHankelMul]
      ring

@[simp] theorem binaryHankelLinearMap_apply
    (a b c d e : ℝ) (v : Fin 3 → ℝ) :
    binaryHankelLinearMap a b c d e v = binaryHankelMul a b c d e v :=
  rfl

theorem binaryHankelQuad_eq_dot_binaryHankelMul
    (a b c d e r s t : ℝ) :
    binaryHankelQuad a b c d e r s t =
      r * (binaryHankelMul a b c d e (![r, s, t] : Fin 3 → ℝ)) 0 +
        s * (binaryHankelMul a b c d e (![r, s, t] : Fin 3 → ℝ)) 1 +
          t * (binaryHankelMul a b c d e (![r, s, t] : Fin 3 → ℝ)) 2 := by
  simp [binaryHankelQuad, binaryHankelMul]
  ring

theorem binaryHankelQuad_eq_zero_of_binaryHankelMul_eq_zero
    {a b c d e r s t : ℝ}
    (hker : binaryHankelMul a b c d e (![r, s, t] : Fin 3 → ℝ) = 0) :
    binaryHankelQuad a b c d e r s t = 0 := by
  rw [binaryHankelQuad_eq_dot_binaryHankelMul]
  rw [hker]
  simp

def binaryQuadraticCombinationMap (x y : linSubmodule) :
    (Fin 3 → ℝ) →ₗ[ℝ] quadSubmodule where
  toFun v := v 0 • linProduct x x + v 1 • linProduct x y + v 2 • linProduct y y
  map_add' v w := by
    ext
    simp [Pi.add_apply, add_smul]
    abel
  map_smul' r v := by
    ext
    simp [mul_smul]

def binaryHankelCoordinateMap (x y : linSubmodule) :
    Module.Dual ℝ quadSubmodule →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun φ := ![φ (linProduct x x), φ (linProduct x y), φ (linProduct y y)]
  map_add' φ ψ := by
    ext i
    fin_cases i <;> simp
  map_smul' r φ := by
    ext i
    fin_cases i <;> simp

theorem binaryHankelMul_ne_zero_of_binaryHankelQuad_neg
    {a b c d e r s t : ℝ}
    (hneg : binaryHankelQuad a b c d e r s t < 0) :
    binaryHankelMul a b c d e (![r, s, t] : Fin 3 → ℝ) ≠ 0 := by
  intro hker
  have hzero : binaryHankelQuad a b c d e r s t = 0 :=
    binaryHankelQuad_eq_zero_of_binaryHankelMul_eq_zero hker
  linarith

def HasBinaryHankelNegativeValue (a b c d e : ℝ) : Prop :=
  ∃ r s t : ℝ, binaryHankelQuad a b c d e r s t < 0

def HasBinaryKernelDiscriminantCase (r s t : ℝ) : Prop :=
  0 < binaryKernelDiscriminant r s t ∨
    binaryKernelDiscriminant r s t = 0 ∨
      binaryKernelDiscriminant r s t < 0

def HasBinaryKernelBranchCertificate (a b c d e : ℝ) : Prop :=
  (b = 0 ∧ c = 0 ∧ d = 0 ∧
    HasBinaryHankelNegativeValue a b c d e) ∨
  (c = 0 ∧ d = 0 ∧ e = 0 ∧
    LinearIndependent ℝ
      ![(![a, b, 0] : Fin 3 → ℝ), (![b, 0, 0] : Fin 3 → ℝ)]) ∨
  (c = -a ∧ d = -b ∧ e = a ∧
    HasBinaryHankelNegativeValue a b c d e)

def HasBinaryCanonicalKernelData (a b c d e : ℝ) : Prop :=
  (binaryHankelMul a b c d e (![0, 1, 0] : Fin 3 → ℝ) = 0 ∧
    HasBinaryHankelNegativeValue a b c d e) ∨
  (binaryHankelMul a b c d e (![0, 0, 1] : Fin 3 → ℝ) = 0 ∧
    LinearIndependent ℝ
      ![(![a, b, 0] : Fin 3 → ℝ), (![b, 0, 0] : Fin 3 → ℝ)]) ∨
  (binaryHankelMul a b c d e (![1, 0, 1] : Fin 3 → ℝ) = 0 ∧
    HasBinaryHankelNegativeValue a b c d e)

def HasBinaryNormalizedKernelPosition (a b c d e : ℝ) : Prop :=
  binaryHankelMul a b c d e (![0, 1, 0] : Fin 3 → ℝ) = 0 ∨
  (binaryHankelMul a b c d e (![0, 0, 1] : Fin 3 → ℝ) = 0 ∧
    LinearIndependent ℝ
      ![(![a, b, 0] : Fin 3 → ℝ), (![b, 0, 0] : Fin 3 → ℝ)]) ∨
  binaryHankelMul a b c d e (![1, 0, 1] : Fin 3 → ℝ) = 0

def HasBinaryRankTwoNormalizedKernelClassification (a b c d e : ℝ) : Prop :=
  HasBinaryHankelNegativeValue a b c d e →
    Module.finrank ℝ (LinearMap.range (binaryHankelLinearMap a b c d e)) ≤ 2 →
      HasBinaryCanonicalKernelData a b c d e

theorem xy_kernel_equations_of_binaryHankelMul_eq_zero
    {a b c d e : ℝ}
    (hker : binaryHankelMul a b c d e (![0, 1, 0] : Fin 3 → ℝ) = 0) :
    b = 0 ∧ c = 0 ∧ d = 0 := by
  have h0 := congrArg (fun v : Fin 3 → ℝ => v 0) hker
  have h1 := congrArg (fun v : Fin 3 → ℝ => v 1) hker
  have h2 := congrArg (fun v : Fin 3 → ℝ => v 2) hker
  simp [binaryHankelMul] at h0 h1 h2
  exact ⟨h0, h1, h2⟩

theorem ySq_kernel_equations_of_binaryHankelMul_eq_zero
    {a b c d e : ℝ}
    (hker : binaryHankelMul a b c d e (![0, 0, 1] : Fin 3 → ℝ) = 0) :
    c = 0 ∧ d = 0 ∧ e = 0 := by
  have h0 := congrArg (fun v : Fin 3 → ℝ => v 0) hker
  have h1 := congrArg (fun v : Fin 3 → ℝ => v 1) hker
  have h2 := congrArg (fun v : Fin 3 → ℝ => v 2) hker
  simp [binaryHankelMul] at h0 h1 h2
  exact ⟨h0, h1, h2⟩

theorem elliptic_kernel_equations_of_binaryHankelMul_eq_zero
    {a b c d e : ℝ}
    (hker : binaryHankelMul a b c d e (![1, 0, 1] : Fin 3 → ℝ) = 0) :
    c = -a ∧ d = -b ∧ e = a := by
  have h0 := congrArg (fun v : Fin 3 → ℝ => v 0) hker
  have h1 := congrArg (fun v : Fin 3 → ℝ => v 1) hker
  have h2 := congrArg (fun v : Fin 3 → ℝ => v 2) hker
  simp [binaryHankelMul] at h0 h1 h2
  constructor
  · linarith
  constructor
  · linarith
  · linarith

theorem binaryKernelBranchCertificate_of_xy_kernel
    {a b c d e : ℝ}
    (hker : binaryHankelMul a b c d e (![0, 1, 0] : Fin 3 → ℝ) = 0)
    (hneg : HasBinaryHankelNegativeValue a b c d e) :
    HasBinaryKernelBranchCertificate a b c d e := by
  rcases xy_kernel_equations_of_binaryHankelMul_eq_zero hker with ⟨hb, hc, hd⟩
  exact Or.inl ⟨hb, hc, hd, hneg⟩

theorem binaryKernelBranchCertificate_of_ySq_kernel
    {a b c d e : ℝ}
    (hker : binaryHankelMul a b c d e (![0, 0, 1] : Fin 3 → ℝ) = 0)
    (hLI : LinearIndependent ℝ
      ![(![a, b, 0] : Fin 3 → ℝ), (![b, 0, 0] : Fin 3 → ℝ)]) :
    HasBinaryKernelBranchCertificate a b c d e := by
  rcases ySq_kernel_equations_of_binaryHankelMul_eq_zero hker with ⟨hc, hd, he⟩
  exact Or.inr (Or.inl ⟨hc, hd, he, hLI⟩)

theorem binaryKernelBranchCertificate_of_elliptic_kernel
    {a b c d e : ℝ}
    (hker : binaryHankelMul a b c d e (![1, 0, 1] : Fin 3 → ℝ) = 0)
    (hneg : HasBinaryHankelNegativeValue a b c d e) :
    HasBinaryKernelBranchCertificate a b c d e := by
  rcases elliptic_kernel_equations_of_binaryHankelMul_eq_zero hker with
    ⟨hc, hd, he⟩
  exact Or.inr (Or.inr ⟨hc, hd, he, hneg⟩)

theorem binaryKernelBranchCertificate_of_canonicalKernelData
    {a b c d e : ℝ}
    (hcanon : HasBinaryCanonicalKernelData a b c d e) :
    HasBinaryKernelBranchCertificate a b c d e := by
  rcases hcanon with hxy | hySq | hell
  · exact binaryKernelBranchCertificate_of_xy_kernel hxy.1 hxy.2
  · exact binaryKernelBranchCertificate_of_ySq_kernel hySq.1 hySq.2
  · exact binaryKernelBranchCertificate_of_elliptic_kernel hell.1 hell.2

theorem binaryCanonicalKernelData_of_normalizedKernelPosition
    {a b c d e : ℝ}
    (hpos : HasBinaryNormalizedKernelPosition a b c d e)
    (hneg : HasBinaryHankelNegativeValue a b c d e) :
    HasBinaryCanonicalKernelData a b c d e := by
  rcases hpos with hxy | hySq | hell
  · exact Or.inl ⟨hxy, hneg⟩
  · exact Or.inr (Or.inl hySq)
  · exact Or.inr (Or.inr ⟨hell, hneg⟩)

theorem binaryKernelBranchCertificate_of_normalizedKernelPosition
    {a b c d e : ℝ}
    (hpos : HasBinaryNormalizedKernelPosition a b c d e)
    (hneg : HasBinaryHankelNegativeValue a b c d e) :
    HasBinaryKernelBranchCertificate a b c d e :=
  binaryKernelBranchCertificate_of_canonicalKernelData
    (binaryCanonicalKernelData_of_normalizedKernelPosition hpos hneg)

theorem binaryRankTwoNormalizedKernelClassification_of_normalizedKernelPosition
    {a b c d e : ℝ}
    (hpos : HasBinaryNormalizedKernelPosition a b c d e) :
    HasBinaryRankTwoNormalizedKernelClassification a b c d e := by
  intro hneg _hrank
  exact binaryCanonicalKernelData_of_normalizedKernelPosition hpos hneg

theorem binaryHankelLinearMap_finrank_range_le_two_of_nonzero_kernel
    {a b c d e : ℝ} {v : Fin 3 → ℝ}
    (hker : binaryHankelLinearMap a b c d e v = 0)
    (hv : v ≠ 0) :
    Module.finrank ℝ
      (LinearMap.range (binaryHankelLinearMap a b c d e)) ≤ 2 := by
  let f := binaryHankelLinearMap a b c d e
  change Module.finrank ℝ (LinearMap.range f) ≤ 2
  have hvker : v ∈ LinearMap.ker f := by
    simpa [f, LinearMap.mem_ker] using hker
  have hker_ne_bot : LinearMap.ker f ≠ ⊥ := by
    intro hbot
    have hvbot : v ∈ (⊥ : Submodule ℝ (Fin 3 → ℝ)) := by
      simpa [hbot] using hvker
    exact hv (by simpa using hvbot)
  have hkerdim : 1 ≤ Module.finrank ℝ (LinearMap.ker f) :=
    (Submodule.one_le_finrank_iff).2 hker_ne_bot
  have hsum :
      Module.finrank ℝ (LinearMap.range f) +
          Module.finrank ℝ (LinearMap.ker f) =
        3 := by
    simpa [f] using (LinearMap.finrank_range_add_finrank_ker f)
  omega

theorem exists_nonzero_binaryHankelKernel_of_finrank_range_le_two
    {a b c d e : ℝ}
    (hrank :
      Module.finrank ℝ (LinearMap.range (binaryHankelLinearMap a b c d e)) ≤ 2) :
    ∃ v : Fin 3 → ℝ,
      v ≠ 0 ∧ binaryHankelLinearMap a b c d e v = 0 := by
  let f := binaryHankelLinearMap a b c d e
  have hsum :
      Module.finrank ℝ (LinearMap.range f) +
          Module.finrank ℝ (LinearMap.ker f) =
        3 := by
    simpa [f] using (LinearMap.finrank_range_add_finrank_ker f)
  have hrankf : Module.finrank ℝ (LinearMap.range f) ≤ 2 := by
    simpa [f] using hrank
  have hker_one : 1 ≤ Module.finrank ℝ (LinearMap.ker f) := by
    omega
  have hker_ne_bot : LinearMap.ker f ≠ ⊥ := by
    exact (Submodule.one_le_finrank_iff).1 hker_one
  rw [Submodule.ne_bot_iff] at hker_ne_bot
  rcases hker_ne_bot with ⟨v, hvker, hvne⟩
  exact ⟨v, hvne, by simpa [f, LinearMap.mem_ker] using hvker⟩

theorem exists_nonzero_binaryHankelMul_kernel_of_finrank_range_le_two
    {a b c d e : ℝ}
    (hrank :
      Module.finrank ℝ (LinearMap.range (binaryHankelLinearMap a b c d e)) ≤ 2) :
    ∃ v : Fin 3 → ℝ,
      v ≠ 0 ∧ binaryHankelMul a b c d e v = 0 := by
  rcases exists_nonzero_binaryHankelKernel_of_finrank_range_le_two
      (a := a) (b := b) (c := c) (d := d) (e := e) hrank with
    ⟨v, hv, hker⟩
  exact ⟨v, hv, by simpa using hker⟩

theorem binaryHankelLinearMap_finrank_ker_eq_one_of_finrank_range_eq_two
    {a b c d e : ℝ}
    (hrank :
      Module.finrank ℝ (LinearMap.range (binaryHankelLinearMap a b c d e)) = 2) :
    Module.finrank ℝ (LinearMap.ker (binaryHankelLinearMap a b c d e)) = 1 := by
  let f := binaryHankelLinearMap a b c d e
  change Module.finrank ℝ (LinearMap.ker f) = 1
  have hsum :
      Module.finrank ℝ (LinearMap.range f) +
          Module.finrank ℝ (LinearMap.ker f) =
        3 := by
    simpa [f] using (LinearMap.finrank_range_add_finrank_ker f)
  have hrankf : Module.finrank ℝ (LinearMap.range f) = 2 := by
    simpa [f] using hrank
  rw [hrankf] at hsum
  omega

theorem exists_nonzero_binaryHankelKernel_and_finrank_ker_eq_one_of_finrank_range_eq_two
    {a b c d e : ℝ}
    (hrank :
      Module.finrank ℝ (LinearMap.range (binaryHankelLinearMap a b c d e)) = 2) :
    ∃ v : Fin 3 → ℝ,
      v ≠ 0 ∧
        binaryHankelLinearMap a b c d e v = 0 ∧
          Module.finrank ℝ
            (LinearMap.ker (binaryHankelLinearMap a b c d e)) = 1 := by
  rcases exists_nonzero_binaryHankelKernel_of_finrank_range_le_two
      (a := a) (b := b) (c := c) (d := d) (e := e)
      (by rw [hrank]) with
    ⟨v, hv, hker⟩
  exact ⟨v, hv, hker,
    binaryHankelLinearMap_finrank_ker_eq_one_of_finrank_range_eq_two
      (a := a) (b := b) (c := c) (d := d) (e := e) hrank⟩

theorem binaryHankelMul_eq_zero_iff
    (a b c d e r s t : ℝ) :
    binaryHankelMul a b c d e (![r, s, t] : Fin 3 → ℝ) = 0 ↔
      a * r + b * s + c * t = 0 ∧
        b * r + c * s + d * t = 0 ∧
          c * r + d * s + e * t = 0 := by
  constructor
  · intro hker
    have h0 := congrArg (fun v : Fin 3 → ℝ => v 0) hker
    have h1 := congrArg (fun v : Fin 3 → ℝ => v 1) hker
    have h2 := congrArg (fun v : Fin 3 → ℝ => v 2) hker
    simp [binaryHankelMul] at h0 h1 h2
    exact ⟨h0, h1, h2⟩
  · intro h
    ext i
    fin_cases i <;> simp [binaryHankelMul, h.1, h.2.1, h.2.2]

theorem ySq_kernel_of_parabolic_zero_xCoeff_kernel_equations
    {a b c d e r s t : ℝ}
    (hr : r = 0)
    (hdisc : binaryKernelDiscriminant r s t = 0)
    (hnonzero : r ≠ 0 ∨ s ≠ 0 ∨ t ≠ 0)
    (h0 : a * r + b * s + c * t = 0)
    (h1 : b * r + c * s + d * t = 0)
    (h2 : c * r + d * s + e * t = 0) :
    binaryHankelMul a b c d e (![0, 0, 1] : Fin 3 → ℝ) = 0 := by
  have hs : s = 0 :=
    parabolic_zero_xCoeff_mixedCoeff_eq_zero (r := r) (s := s) (t := t)
      hr hdisc
  have ht : t ≠ 0 := by
    rcases hnonzero with hr_ne | hs_ne | ht_ne
    · exact (hr_ne hr).elim
    · exact (hs_ne hs).elim
    · exact ht_ne
  have hc_mul : c * t = 0 := by
    simpa [hr, hs] using h0
  have hd_mul : d * t = 0 := by
    simpa [hr, hs] using h1
  have he_mul : e * t = 0 := by
    simpa [hr, hs] using h2
  have hc : c = 0 := (mul_eq_zero.mp hc_mul).resolve_right ht
  have hd : d = 0 := (mul_eq_zero.mp hd_mul).resolve_right ht
  have he : e = 0 := (mul_eq_zero.mp he_mul).resolve_right ht
  ext i
  fin_cases i <;> simp [binaryHankelMul, hc, hd, he]

theorem exists_nonzero_binaryHankel_kernel_equations_of_finrank_range_le_two
    {a b c d e : ℝ}
    (hrank :
      Module.finrank ℝ (LinearMap.range (binaryHankelLinearMap a b c d e)) ≤ 2) :
    ∃ r s t : ℝ,
      (r ≠ 0 ∨ s ≠ 0 ∨ t ≠ 0) ∧
        a * r + b * s + c * t = 0 ∧
          b * r + c * s + d * t = 0 ∧
            c * r + d * s + e * t = 0 := by
  rcases exists_nonzero_binaryHankelMul_kernel_of_finrank_range_le_two
      (a := a) (b := b) (c := c) (d := d) (e := e) hrank with
    ⟨v, hv, hker⟩
  refine ⟨v 0, v 1, v 2, ?_, ?_⟩
  · by_contra hzero
    push Not at hzero
    exact hv (by
      ext i
      fin_cases i <;> simp [hzero.1, hzero.2.1, hzero.2.2])
  · exact (binaryHankelMul_eq_zero_iff a b c d e (v 0) (v 1) (v 2)).1
      (by
        have hvec : (![v 0, v 1, v 2] : Fin 3 → ℝ) = v := by
          ext i
          fin_cases i <;> simp
        rwa [hvec])

theorem hasBinaryKernelDiscriminantCase
    (r s t : ℝ) :
    HasBinaryKernelDiscriminantCase r s t := by
  by_cases hpos : 0 < binaryKernelDiscriminant r s t
  · exact Or.inl hpos
  · by_cases hzero : binaryKernelDiscriminant r s t = 0
    · exact Or.inr (Or.inl hzero)
    · exact Or.inr (Or.inr (lt_of_le_of_ne (le_of_not_gt hpos) hzero))

def HasBinaryHankelKernelDiscriminantData (a b c d e : ℝ) : Prop :=
  ∃ r s t : ℝ,
    (r ≠ 0 ∨ s ≠ 0 ∨ t ≠ 0) ∧
      a * r + b * s + c * t = 0 ∧
        b * r + c * s + d * t = 0 ∧
          c * r + d * s + e * t = 0 ∧
            HasBinaryKernelDiscriminantCase r s t

theorem hasBinaryHankelKernelDiscriminantData_of_finrank_range_le_two
    {a b c d e : ℝ}
    (hrank :
      Module.finrank ℝ (LinearMap.range (binaryHankelLinearMap a b c d e)) ≤ 2) :
    HasBinaryHankelKernelDiscriminantData a b c d e := by
  rcases exists_nonzero_binaryHankel_kernel_equations_of_finrank_range_le_two
      (a := a) (b := b) (c := c) (d := d) (e := e) hrank with
    ⟨r, s, t, hnonzero, h0, h1, h2⟩
  exact ⟨r, s, t, hnonzero, h0, h1, h2,
    hasBinaryKernelDiscriminantCase r s t⟩

theorem binaryHankelLinearMap_finrank_range_le_two_of_xy_kernel
    {a b c d e : ℝ}
    (hker : binaryHankelMul a b c d e (![0, 1, 0] : Fin 3 → ℝ) = 0) :
    Module.finrank ℝ
      (LinearMap.range (binaryHankelLinearMap a b c d e)) ≤ 2 := by
  refine binaryHankelLinearMap_finrank_range_le_two_of_nonzero_kernel
    (a := a) (b := b) (c := c) (d := d) (e := e)
    (v := (![0, 1, 0] : Fin 3 → ℝ)) ?_ ?_
  · simpa using hker
  · intro h
    have h1 := congrArg (fun v : Fin 3 → ℝ => v 1) h
    norm_num [Fin.isValue] at h1

theorem binaryHankelLinearMap_finrank_range_le_two_of_ySq_kernel
    {a b c d e : ℝ}
    (hker : binaryHankelMul a b c d e (![0, 0, 1] : Fin 3 → ℝ) = 0) :
    Module.finrank ℝ
      (LinearMap.range (binaryHankelLinearMap a b c d e)) ≤ 2 := by
  refine binaryHankelLinearMap_finrank_range_le_two_of_nonzero_kernel
    (a := a) (b := b) (c := c) (d := d) (e := e)
    (v := (![0, 0, 1] : Fin 3 → ℝ)) ?_ ?_
  · simpa using hker
  · intro h
    have h2 := congrArg (fun v : Fin 3 → ℝ => v ⟨2, by norm_num⟩) h
    norm_num [Fin.isValue] at h2

theorem binaryHankelLinearMap_finrank_range_le_two_of_elliptic_kernel
    {a b c d e : ℝ}
    (hker : binaryHankelMul a b c d e (![1, 0, 1] : Fin 3 → ℝ) = 0) :
    Module.finrank ℝ
      (LinearMap.range (binaryHankelLinearMap a b c d e)) ≤ 2 := by
  refine binaryHankelLinearMap_finrank_range_le_two_of_nonzero_kernel
    (a := a) (b := b) (c := c) (d := d) (e := e)
    (v := (![1, 0, 1] : Fin 3 → ℝ)) ?_ ?_
  · simpa using hker
  · intro h
    have h0 := congrArg (fun v : Fin 3 → ℝ => v 0) h
    norm_num [Fin.isValue] at h0

theorem binaryNormalizedKernelPosition_of_canonicalKernelData
    {a b c d e : ℝ}
    (hcanon : HasBinaryCanonicalKernelData a b c d e) :
    HasBinaryNormalizedKernelPosition a b c d e := by
  rcases hcanon with hxy | hySq | hell
  · exact Or.inl hxy.1
  · exact Or.inr (Or.inl hySq)
  · exact Or.inr (Or.inr hell.1)

theorem binaryHankelLinearMap_finrank_range_le_two_of_canonicalKernelData
    {a b c d e : ℝ}
    (hcanon : HasBinaryCanonicalKernelData a b c d e) :
    Module.finrank ℝ
      (LinearMap.range (binaryHankelLinearMap a b c d e)) ≤ 2 := by
  rcases hcanon with hxy | hySq | hell
  · exact binaryHankelLinearMap_finrank_range_le_two_of_xy_kernel hxy.1
  · exact binaryHankelLinearMap_finrank_range_le_two_of_ySq_kernel hySq.1
  · exact binaryHankelLinearMap_finrank_range_le_two_of_elliptic_kernel hell.1

theorem binaryHankelLinearMap_finrank_range_le_two_of_normalizedKernelPosition
    {a b c d e : ℝ}
    (hpos : HasBinaryNormalizedKernelPosition a b c d e) :
    Module.finrank ℝ
      (LinearMap.range (binaryHankelLinearMap a b c d e)) ≤ 2 := by
  rcases hpos with hxy | hySq | hell
  · exact binaryHankelLinearMap_finrank_range_le_two_of_xy_kernel hxy
  · exact binaryHankelLinearMap_finrank_range_le_two_of_ySq_kernel hySq.1
  · exact binaryHankelLinearMap_finrank_range_le_two_of_elliptic_kernel hell

def HasBinaryLowRankNegativeNormalForm (a b c d e : ℝ) : Prop :=
  (∃ ρ α β : ℝ,
    ρ < 0 ∧
      (α ≠ 0 ∨ β ≠ 0) ∧
        a = ρ * α^4 ∧
          b = ρ * α^3 * β ∧
            c = ρ * α^2 * β^2 ∧
              d = ρ * α * β^3 ∧
                e = ρ * β^4) ∨
  (b = 0 ∧ c = 0 ∧ d = 0 ∧
    ∃ r t : ℝ, a * r^2 + e * t^2 < 0) ∨
  (c = 0 ∧ d = 0 ∧ e = 0 ∧ b ≠ 0) ∨
  (c = -a ∧ d = -b ∧ e = a ∧ (a ≠ 0 ∨ b ≠ 0))

theorem HasBinaryLowRankNegativeNormalForm.rankOne
    {ρ α β : ℝ} (hρ : ρ < 0) (hvec : α ≠ 0 ∨ β ≠ 0) :
    HasBinaryLowRankNegativeNormalForm
      (ρ * α^4) (ρ * α^3 * β) (ρ * α^2 * β^2)
      (ρ * α * β^3) (ρ * β^4) := by
  exact Or.inl ⟨ρ, α, β, hρ, hvec, rfl, rfl, rfl, rfl, rfl⟩

theorem binaryHankelQuad_rankOne_eq (ρ α β r s t : ℝ) :
    binaryHankelQuad
        (ρ * α^4) (ρ * α^3 * β) (ρ * α^2 * β^2)
        (ρ * α * β^3) (ρ * β^4) r s t =
      ρ * (α^2 * r + α * β * s + β^2 * t)^2 := by
  unfold binaryHankelQuad
  ring

theorem rankOne_hankel_scalar_neg_of_negative
    {ρ α β : ℝ}
    (hneg : ∃ r s t : ℝ,
      binaryHankelQuad
        (ρ * α^4) (ρ * α^3 * β) (ρ * α^2 * β^2)
        (ρ * α * β^3) (ρ * β^4) r s t < 0) :
    ρ < 0 := by
  rcases hneg with ⟨r, s, t, hneg⟩
  rw [binaryHankelQuad_rankOne_eq] at hneg
  by_contra hρ
  have hρ_nonneg : 0 ≤ ρ := le_of_not_gt hρ
  have hsquare : 0 ≤ (α^2 * r + α * β * s + β^2 * t)^2 :=
    sq_nonneg _
  nlinarith

theorem HasBinaryLowRankNegativeNormalForm.rankOne_of_negative_hankel
    {ρ α β : ℝ}
    (hvec : α ≠ 0 ∨ β ≠ 0)
    (hneg : ∃ r s t : ℝ,
      binaryHankelQuad
        (ρ * α^4) (ρ * α^3 * β) (ρ * α^2 * β^2)
        (ρ * α * β^3) (ρ * β^4) r s t < 0) :
    HasBinaryLowRankNegativeNormalForm
      (ρ * α^4) (ρ * α^3 * β) (ρ * α^2 * β^2)
      (ρ * α * β^3) (ρ * β^4) :=
  HasBinaryLowRankNegativeNormalForm.rankOne
    (rankOne_hankel_scalar_neg_of_negative hneg) hvec

theorem HasBinaryLowRankNegativeNormalForm.xyKernel
    {a e : ℝ} (hneg : ∃ r t : ℝ, a * r^2 + e * t^2 < 0) :
    HasBinaryLowRankNegativeNormalForm a 0 0 0 e := by
  exact Or.inr (Or.inl ⟨rfl, rfl, rfl, hneg⟩)

theorem HasBinaryLowRankNegativeNormalForm.xyKernel_of_negative_hankel
    {a e : ℝ} (hneg : HasBinaryHankelNegativeValue a 0 0 0 e) :
    HasBinaryLowRankNegativeNormalForm a 0 0 0 e := by
  rcases hneg with ⟨r, _s, t, hneg⟩
  exact HasBinaryLowRankNegativeNormalForm.xyKernel
    ⟨r, t, by simpa [binaryHankelQuad] using hneg⟩

theorem HasBinaryLowRankNegativeNormalForm.ySqKernel
    {a b : ℝ} (hb : b ≠ 0) :
    HasBinaryLowRankNegativeNormalForm a b 0 0 0 := by
  exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, hb⟩))

theorem ySqKernel_b_ne_zero_of_column_linearIndependent
    {a b : ℝ}
    (hLI : LinearIndependent ℝ
      ![(![a, b, 0] : Fin 3 → ℝ), (![b, 0, 0] : Fin 3 → ℝ)]) :
    b ≠ 0 := by
  intro hb
  have hcol : (![b, 0, 0] : Fin 3 → ℝ) = 0 := by
    ext i
    fin_cases i <;> simp [hb]
  exact (LinearIndependent.ne_zero (R := ℝ) (1 : Fin 2) hLI) hcol

theorem ySqKernel_column_linearIndependent_of_b_ne_zero
    {a b : ℝ} (hb : b ≠ 0) :
    LinearIndependent ℝ
      ![(![a, b, 0] : Fin 3 → ℝ), (![b, 0, 0] : Fin 3 → ℝ)] := by
  rw [LinearIndependent.pair_iff']
  · intro t ht
    have hcoord1 := congrArg (fun v : Fin 3 → ℝ => v 1) ht
    have htzero : t = 0 := by
      have hmul : t * b = 0 := by
        simpa [Pi.smul_apply] using hcoord1
      exact (mul_eq_zero.mp hmul).resolve_right hb
    have hcoord0 := congrArg (fun v : Fin 3 → ℝ => v 0) ht
    rw [htzero] at hcoord0
    simp at hcoord0
    exact hb hcoord0.symm
  · intro hzero
    have hcoord1 := congrArg (fun v : Fin 3 → ℝ => v 1) hzero
    simpa using hb hcoord1

theorem HasBinaryLowRankNegativeNormalForm.ySqKernel_of_column_linearIndependent
    {a b : ℝ}
    (hLI : LinearIndependent ℝ
      ![(![a, b, 0] : Fin 3 → ℝ), (![b, 0, 0] : Fin 3 → ℝ)]) :
    HasBinaryLowRankNegativeNormalForm a b 0 0 0 :=
  HasBinaryLowRankNegativeNormalForm.ySqKernel
    (ySqKernel_b_ne_zero_of_column_linearIndependent hLI)

theorem HasBinaryLowRankNegativeNormalForm.ellipticKernel
    {a b : ℝ} (hne : a ≠ 0 ∨ b ≠ 0) :
    HasBinaryLowRankNegativeNormalForm a b (-a) (-b) a := by
  exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, hne⟩))

theorem ellipticKernel_nonzero_of_negative_hankel
    {a b : ℝ} (hneg : HasBinaryHankelNegativeValue a b (-a) (-b) a) :
    a ≠ 0 ∨ b ≠ 0 := by
  by_contra hzero
  push Not at hzero
  rcases hneg with ⟨r, s, t, hneg⟩
  rw [hzero.1, hzero.2] at hneg
  norm_num [binaryHankelQuad] at hneg

theorem ellipticKernel_binaryHankelNegativeValue
    {a b : ℝ} (hne : a ≠ 0 ∨ b ≠ 0) :
    HasBinaryHankelNegativeValue a b (-a) (-b) a := by
  by_cases ha : a = 0
  · rcases hne with ha_ne | hb
    · exact (ha_ne ha).elim
    · by_cases hbpos : 0 < b
      · refine ⟨0, 1, 1, ?_⟩
        unfold binaryHankelQuad
        nlinarith
      · have hbneg : b < 0 := lt_of_le_of_ne (le_of_not_gt hbpos) hb
        refine ⟨1, 1, 0, ?_⟩
        unfold binaryHankelQuad
        nlinarith
  · by_cases hapos : 0 < a
    · refine ⟨0, 1, 0, ?_⟩
      unfold binaryHankelQuad
      nlinarith
    · have haneg : a < 0 := lt_of_le_of_ne (le_of_not_gt hapos) ha
      refine ⟨1, 0, 0, ?_⟩
      unfold binaryHankelQuad
      nlinarith

theorem HasBinaryLowRankNegativeNormalForm.ellipticKernel_of_negative_hankel
    {a b : ℝ} (hneg : HasBinaryHankelNegativeValue a b (-a) (-b) a) :
    HasBinaryLowRankNegativeNormalForm a b (-a) (-b) a :=
  HasBinaryLowRankNegativeNormalForm.ellipticKernel
    (ellipticKernel_nonzero_of_negative_hankel hneg)

theorem HasBinaryLowRankNegativeNormalForm.of_xyKernel_equations
    {a b c d e : ℝ}
    (hb : b = 0) (hc : c = 0) (hd : d = 0)
    (hneg : ∃ r t : ℝ, a * r^2 + e * t^2 < 0) :
    HasBinaryLowRankNegativeNormalForm a b c d e := by
  subst b
  subst c
  subst d
  exact HasBinaryLowRankNegativeNormalForm.xyKernel hneg

theorem HasBinaryLowRankNegativeNormalForm.of_ySqKernel_equations
    {a b c d e : ℝ}
    (hc : c = 0) (hd : d = 0) (he : e = 0)
    (hb : b ≠ 0) :
    HasBinaryLowRankNegativeNormalForm a b c d e := by
  subst c
  subst d
  subst e
  exact HasBinaryLowRankNegativeNormalForm.ySqKernel hb

theorem HasBinaryLowRankNegativeNormalForm.of_ellipticKernel_equations
    {a b c d e : ℝ}
    (hc : c = -a) (hd : d = -b) (he : e = a)
    (hne : a ≠ 0 ∨ b ≠ 0) :
    HasBinaryLowRankNegativeNormalForm a b c d e := by
  subst c
  subst d
  subst e
  exact HasBinaryLowRankNegativeNormalForm.ellipticKernel hne

def binaryRestrictionCoeffA
    (B : DotForm) (p : Poly) (u : RankSevenVec) (x : linSubmodule) : ℝ :=
  B ((linProduct x x : quadSubmodule).1^2) (residual p u)

def binaryRestrictionCoeffB
    (B : DotForm) (p : Poly) (u : RankSevenVec) (x y : linSubmodule) : ℝ :=
  B ((linProduct x x : quadSubmodule).1 *
      (linProduct x y : quadSubmodule).1) (residual p u)

def binaryRestrictionCoeffC
    (B : DotForm) (p : Poly) (u : RankSevenVec) (x y : linSubmodule) : ℝ :=
  B ((linProduct x y : quadSubmodule).1^2) (residual p u)

def binaryRestrictionCoeffD
    (B : DotForm) (p : Poly) (u : RankSevenVec) (x y : linSubmodule) : ℝ :=
  B ((linProduct x y : quadSubmodule).1 *
      (linProduct y y : quadSubmodule).1) (residual p u)

def binaryRestrictionCoeffE
    (B : DotForm) (p : Poly) (u : RankSevenVec) (y : linSubmodule) : ℝ :=
  B ((linProduct y y : quadSubmodule).1^2) (residual p u)

theorem binaryHankelLinearMap_eq_coordinate_comp_catalecticant
    (B : DotForm) (p : Poly) (u : RankSevenVec) (x y : linSubmodule) :
    binaryHankelLinearMap
        (binaryRestrictionCoeffA B p u x)
        (binaryRestrictionCoeffB B p u x y)
        (binaryRestrictionCoeffC B p u x y)
        (binaryRestrictionCoeffD B p u x y)
        (binaryRestrictionCoeffE B p u y) =
      (binaryHankelCoordinateMap x y).comp
        ((catalecticantMap B p u).comp (binaryQuadraticCombinationMap x y)) := by
  ext v i
  fin_cases i <;>
    simp [binaryHankelLinearMap, binaryHankelMul, binaryHankelCoordinateMap,
      binaryQuadraticCombinationMap, binaryRestrictionCoeffA,
      binaryRestrictionCoeffB, binaryRestrictionCoeffC, binaryRestrictionCoeffD,
      binaryRestrictionCoeffE] <;>
    ring_nf

theorem binaryHankelLinearMap_finrank_range_le_catalecticantMap_rank
    (B : DotForm) (p : Poly) (u : RankSevenVec) (x y : linSubmodule) :
    Module.finrank ℝ
        (LinearMap.range
          (binaryHankelLinearMap
            (binaryRestrictionCoeffA B p u x)
            (binaryRestrictionCoeffB B p u x y)
            (binaryRestrictionCoeffC B p u x y)
            (binaryRestrictionCoeffD B p u x y)
            (binaryRestrictionCoeffE B p u y))) ≤
      Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) := by
  rw [binaryHankelLinearMap_eq_coordinate_comp_catalecticant]
  let f := (catalecticantMap B p u).comp (binaryQuadraticCombinationMap x y)
  let g := binaryHankelCoordinateMap x y
  have hpost :
      Module.finrank ℝ (LinearMap.range (g.comp f)) ≤
        Module.finrank ℝ (LinearMap.range f) := by
    rw [LinearMap.range_comp]
    exact Submodule.finrank_map_le g (LinearMap.range f)
  have hpre :
      Module.finrank ℝ (LinearMap.range f) ≤
        Module.finrank ℝ (LinearMap.range (catalecticantMap B p u)) := by
    exact Submodule.finrank_mono
      (LinearMap.range_comp_le_range (binaryQuadraticCombinationMap x y)
        (catalecticantMap B p u))
  exact hpost.trans hpre

theorem binaryRestriction_lowRankNegativeNormalForm_of_xyKernel_equations
    {B : DotForm} {p : Poly} {u : RankSevenVec} {x y : linSubmodule}
    (hb : binaryRestrictionCoeffB B p u x y = 0)
    (hc : binaryRestrictionCoeffC B p u x y = 0)
    (hd : binaryRestrictionCoeffD B p u x y = 0)
    (hneg :
      ∃ r t : ℝ,
        binaryRestrictionCoeffA B p u x * r^2 +
            binaryRestrictionCoeffE B p u y * t^2 <
          0) :
    HasBinaryLowRankNegativeNormalForm
      (binaryRestrictionCoeffA B p u x)
      (binaryRestrictionCoeffB B p u x y)
      (binaryRestrictionCoeffC B p u x y)
      (binaryRestrictionCoeffD B p u x y)
      (binaryRestrictionCoeffE B p u y) :=
  HasBinaryLowRankNegativeNormalForm.of_xyKernel_equations hb hc hd hneg

theorem binaryRestriction_lowRankNegativeNormalForm_of_ySqKernel_equations
    {B : DotForm} {p : Poly} {u : RankSevenVec} {x y : linSubmodule}
    (hc : binaryRestrictionCoeffC B p u x y = 0)
    (hd : binaryRestrictionCoeffD B p u x y = 0)
    (he : binaryRestrictionCoeffE B p u y = 0)
    (hb : binaryRestrictionCoeffB B p u x y ≠ 0) :
    HasBinaryLowRankNegativeNormalForm
      (binaryRestrictionCoeffA B p u x)
      (binaryRestrictionCoeffB B p u x y)
      (binaryRestrictionCoeffC B p u x y)
      (binaryRestrictionCoeffD B p u x y)
      (binaryRestrictionCoeffE B p u y) :=
  HasBinaryLowRankNegativeNormalForm.of_ySqKernel_equations hc hd he hb

theorem binaryRestriction_lowRankNegativeNormalForm_of_ellipticKernel_equations
    {B : DotForm} {p : Poly} {u : RankSevenVec} {x y : linSubmodule}
    (hc :
      binaryRestrictionCoeffC B p u x y =
        -binaryRestrictionCoeffA B p u x)
    (hd :
      binaryRestrictionCoeffD B p u x y =
        -binaryRestrictionCoeffB B p u x y)
    (he :
      binaryRestrictionCoeffE B p u y =
        binaryRestrictionCoeffA B p u x)
    (hne :
      binaryRestrictionCoeffA B p u x ≠ 0 ∨
        binaryRestrictionCoeffB B p u x y ≠ 0) :
    HasBinaryLowRankNegativeNormalForm
      (binaryRestrictionCoeffA B p u x)
      (binaryRestrictionCoeffB B p u x y)
      (binaryRestrictionCoeffC B p u x y)
      (binaryRestrictionCoeffD B p u x y)
      (binaryRestrictionCoeffE B p u y) :=
  HasBinaryLowRankNegativeNormalForm.of_ellipticKernel_equations hc hd he hne

def HasBinaryRestrictionKernelEquationCase
    (B : DotForm) (p : Poly) (u : RankSevenVec) (x y : linSubmodule) : Prop :=
  (binaryRestrictionCoeffB B p u x y = 0 ∧
    binaryRestrictionCoeffC B p u x y = 0 ∧
      binaryRestrictionCoeffD B p u x y = 0 ∧
        ∃ r t : ℝ,
          binaryRestrictionCoeffA B p u x * r^2 +
              binaryRestrictionCoeffE B p u y * t^2 <
            0) ∨
  (binaryRestrictionCoeffC B p u x y = 0 ∧
    binaryRestrictionCoeffD B p u x y = 0 ∧
      binaryRestrictionCoeffE B p u y = 0 ∧
        binaryRestrictionCoeffB B p u x y ≠ 0) ∨
  (binaryRestrictionCoeffC B p u x y =
      -binaryRestrictionCoeffA B p u x ∧
    binaryRestrictionCoeffD B p u x y =
      -binaryRestrictionCoeffB B p u x y ∧
    binaryRestrictionCoeffE B p u y =
      binaryRestrictionCoeffA B p u x ∧
    (binaryRestrictionCoeffA B p u x ≠ 0 ∨
      binaryRestrictionCoeffB B p u x y ≠ 0))

theorem binaryRestriction_lowRankNegativeNormalForm_of_kernelEquationCase
    {B : DotForm} {p : Poly} {u : RankSevenVec} {x y : linSubmodule}
    (hcase : HasBinaryRestrictionKernelEquationCase B p u x y) :
    HasBinaryLowRankNegativeNormalForm
      (binaryRestrictionCoeffA B p u x)
      (binaryRestrictionCoeffB B p u x y)
      (binaryRestrictionCoeffC B p u x y)
      (binaryRestrictionCoeffD B p u x y)
      (binaryRestrictionCoeffE B p u y) := by
  rcases hcase with hxy | hySq | hell
  · rcases hxy with ⟨hb, hc, hd, hneg⟩
    exact binaryRestriction_lowRankNegativeNormalForm_of_xyKernel_equations
      hb hc hd hneg
  · rcases hySq with ⟨hc, hd, he, hb⟩
    exact binaryRestriction_lowRankNegativeNormalForm_of_ySqKernel_equations
      hc hd he hb
  · rcases hell with ⟨hc, hd, he, hne⟩
    exact binaryRestriction_lowRankNegativeNormalForm_of_ellipticKernel_equations
      hc hd he hne

theorem binaryRestriction_canonicalKernelData_of_kernelEquationCase
    {B : DotForm} {p : Poly} {u : RankSevenVec} {x y : linSubmodule}
    (hcase : HasBinaryRestrictionKernelEquationCase B p u x y) :
    HasBinaryCanonicalKernelData
      (binaryRestrictionCoeffA B p u x)
      (binaryRestrictionCoeffB B p u x y)
      (binaryRestrictionCoeffC B p u x y)
      (binaryRestrictionCoeffD B p u x y)
      (binaryRestrictionCoeffE B p u y) := by
  rcases hcase with hxy | hySq | hell
  · rcases hxy with ⟨hb, hc, hd, hneg⟩
    refine Or.inl ⟨?_, ?_⟩
    · ext i
      fin_cases i <;> simp [binaryHankelMul, hb, hc, hd]
    · rcases hneg with ⟨r, t, hrt⟩
      refine ⟨r, 0, t, ?_⟩
      simpa [binaryHankelQuad, hb, hc, hd] using hrt
  · rcases hySq with ⟨hc, hd, he, hb⟩
    refine Or.inr (Or.inl ⟨?_, ?_⟩)
    · ext i
      fin_cases i <;> simp [binaryHankelMul, hc, hd, he]
    · exact ySqKernel_column_linearIndependent_of_b_ne_zero hb
  · rcases hell with ⟨hc, hd, he, hne⟩
    refine Or.inr (Or.inr ⟨?_, ?_⟩)
    · ext i
      fin_cases i <;> simp [binaryHankelMul, hc, hd, he]
    · simpa [hc, hd, he] using ellipticKernel_binaryHankelNegativeValue hne

theorem binaryRestriction_kernelEquationCase_of_canonicalKernelData
    {B : DotForm} {p : Poly} {u : RankSevenVec} {x y : linSubmodule}
    (hcanon :
      HasBinaryCanonicalKernelData
        (binaryRestrictionCoeffA B p u x)
        (binaryRestrictionCoeffB B p u x y)
        (binaryRestrictionCoeffC B p u x y)
        (binaryRestrictionCoeffD B p u x y)
        (binaryRestrictionCoeffE B p u y)) :
    HasBinaryRestrictionKernelEquationCase B p u x y := by
  rcases hcanon with hxy | hySq | hell
  · rcases xy_kernel_equations_of_binaryHankelMul_eq_zero hxy.1 with
      ⟨hb, hc, hd⟩
    refine Or.inl ⟨hb, hc, hd, ?_⟩
    rcases hxy.2 with ⟨r, _s, t, hneg⟩
    refine ⟨r, t, ?_⟩
    simpa [binaryHankelQuad, hb, hc, hd] using hneg
  · rcases ySq_kernel_equations_of_binaryHankelMul_eq_zero hySq.1 with
      ⟨hc, hd, he⟩
    refine Or.inr (Or.inl ⟨hc, hd, he, ?_⟩)
    exact ySqKernel_b_ne_zero_of_column_linearIndependent hySq.2
  · rcases elliptic_kernel_equations_of_binaryHankelMul_eq_zero hell.1 with
      ⟨hc, hd, he⟩
    refine Or.inr (Or.inr ⟨hc, hd, he, ?_⟩)
    by_contra hzero
    push Not at hzero
    rcases hell.2 with ⟨r, s, t, hneg⟩
    simp [binaryHankelQuad, hc, hd, he, hzero.1, hzero.2] at hneg

theorem binaryRestriction_kernelEquationCase_of_kernelBranchCertificate
    {B : DotForm} {p : Poly} {u : RankSevenVec} {x y : linSubmodule}
    (hcert :
      HasBinaryKernelBranchCertificate
        (binaryRestrictionCoeffA B p u x)
        (binaryRestrictionCoeffB B p u x y)
        (binaryRestrictionCoeffC B p u x y)
        (binaryRestrictionCoeffD B p u x y)
        (binaryRestrictionCoeffE B p u y)) :
    HasBinaryRestrictionKernelEquationCase B p u x y := by
  rcases hcert with hxy | hySq | hell
  · rcases hxy with ⟨hb, hc, hd, hneg⟩
    refine Or.inl ⟨hb, hc, hd, ?_⟩
    rcases hneg with ⟨r, _s, t, hneg⟩
    refine ⟨r, t, ?_⟩
    simpa [binaryHankelQuad, hb, hc, hd] using hneg
  · rcases hySq with ⟨hc, hd, he, hLI⟩
    exact Or.inr (Or.inl
      ⟨hc, hd, he, ySqKernel_b_ne_zero_of_column_linearIndependent hLI⟩)
  · rcases hell with ⟨hc, hd, he, hneg⟩
    refine Or.inr (Or.inr ⟨hc, hd, he, ?_⟩)
    by_contra hzero
    push Not at hzero
    rcases hneg with ⟨r, s, t, hneg⟩
    simp [binaryHankelQuad, hc, hd, he, hzero.1, hzero.2] at hneg

theorem binaryLowRankNegativeNormalForm_of_kernelBranchCertificate
    {a b c d e : ℝ}
    (hcert : HasBinaryKernelBranchCertificate a b c d e) :
    HasBinaryLowRankNegativeNormalForm a b c d e := by
  rcases hcert with hxy | hySq | hell
  · rcases hxy with ⟨hb, hc, hd, hneg⟩
    subst b
    subst c
    subst d
    exact HasBinaryLowRankNegativeNormalForm.xyKernel_of_negative_hankel hneg
  · rcases hySq with ⟨hc, hd, he, hLI⟩
    subst c
    subst d
    subst e
    exact HasBinaryLowRankNegativeNormalForm.ySqKernel_of_column_linearIndependent hLI
  · rcases hell with ⟨hc, hd, he, hneg⟩
    subst c
    subst d
    subst e
    exact HasBinaryLowRankNegativeNormalForm.ellipticKernel_of_negative_hankel hneg

theorem binaryLowRankNegativeNormalForm_of_canonicalKernelData
    {a b c d e : ℝ}
    (hcanon : HasBinaryCanonicalKernelData a b c d e) :
    HasBinaryLowRankNegativeNormalForm a b c d e :=
  binaryLowRankNegativeNormalForm_of_kernelBranchCertificate
    (binaryKernelBranchCertificate_of_canonicalKernelData hcanon)

theorem binaryLowRankNegativeNormalForm_of_rankTwoNormalizedKernelClassification
    {a b c d e : ℝ}
    (hclass : HasBinaryRankTwoNormalizedKernelClassification a b c d e)
    (hneg : HasBinaryHankelNegativeValue a b c d e)
    (hrank :
      Module.finrank ℝ (LinearMap.range (binaryHankelLinearMap a b c d e)) ≤ 2) :
    HasBinaryLowRankNegativeNormalForm a b c d e :=
  binaryLowRankNegativeNormalForm_of_canonicalKernelData (hclass hneg hrank)

theorem binaryRestriction_lowRankNegativeNormalForm_of_kernelBranchCertificate
    {B : DotForm} {p : Poly} {u : RankSevenVec} {x y : linSubmodule}
    (hcert :
      HasBinaryKernelBranchCertificate
        (binaryRestrictionCoeffA B p u x)
        (binaryRestrictionCoeffB B p u x y)
        (binaryRestrictionCoeffC B p u x y)
        (binaryRestrictionCoeffD B p u x y)
        (binaryRestrictionCoeffE B p u y)) :
    HasBinaryLowRankNegativeNormalForm
      (binaryRestrictionCoeffA B p u x)
      (binaryRestrictionCoeffB B p u x y)
      (binaryRestrictionCoeffC B p u x y)
      (binaryRestrictionCoeffD B p u x y)
      (binaryRestrictionCoeffE B p u y) :=
  binaryLowRankNegativeNormalForm_of_kernelBranchCertificate hcert

theorem binaryRestriction_lowRankNegativeNormalForm_of_canonicalKernelData
    {B : DotForm} {p : Poly} {u : RankSevenVec} {x y : linSubmodule}
    (hcanon :
      HasBinaryCanonicalKernelData
        (binaryRestrictionCoeffA B p u x)
        (binaryRestrictionCoeffB B p u x y)
        (binaryRestrictionCoeffC B p u x y)
        (binaryRestrictionCoeffD B p u x y)
        (binaryRestrictionCoeffE B p u y)) :
    HasBinaryLowRankNegativeNormalForm
      (binaryRestrictionCoeffA B p u x)
      (binaryRestrictionCoeffB B p u x y)
      (binaryRestrictionCoeffC B p u x y)
      (binaryRestrictionCoeffD B p u x y)
      (binaryRestrictionCoeffE B p u y) :=
  binaryLowRankNegativeNormalForm_of_canonicalKernelData hcanon

theorem binaryRestriction_pow_eq_C
    (x y : linSubmodule) (X Y : ℝ) :
    (linProduct (X • x + Y • y) (X • x + Y • y) :
        quadSubmodule).1^2 =
      MvPolynomial.C (X^4) * (linProduct x x : quadSubmodule).1^2 +
        MvPolynomial.C (X^3 * Y) *
            ((linProduct x x : quadSubmodule).1 *
              (linProduct x y : quadSubmodule).1) * 4 +
          MvPolynomial.C (X^2 * Y^2) *
              (linProduct x y : quadSubmodule).1^2 * 6 +
            MvPolynomial.C (X * Y^3) *
                ((linProduct x y : quadSubmodule).1 *
                  (linProduct y y : quadSubmodule).1) * 4 +
              MvPolynomial.C (Y^4) * (linProduct y y : quadSubmodule).1^2 := by
  simp [linProduct, Algebra.smul_def]
  ring_nf

theorem residualEval_C_mul
    (B : DotForm) (r : ℝ) (q s : Poly) :
    B (MvPolynomial.C r * q) s = r * B q s := by
  rw [show MvPolynomial.C r * q = r • q by
    rw [← MvPolynomial.algebraMap_eq ℝ (Fin 3)]
    exact (Algebra.smul_def r q).symm]
  simp

theorem residualEval_mul_four
    (B : DotForm) (q s : Poly) :
    B (q * (4 : Poly)) s = 4 * B q s := by
  have hq : q * (4 : Poly) = q + q + q + q := by
    ring
  rw [hq]
  simp
  ring

theorem residualEval_mul_two
    (B : DotForm) (q s : Poly) :
    B (q * (2 : Poly)) s = 2 * B q s := by
  have hq : q * (2 : Poly) = q + q := by
    ring
  rw [hq]
  simp
  ring

theorem residualEval_mul_six
    (B : DotForm) (q s : Poly) :
    B (q * (6 : Poly)) s = 6 * B q s := by
  have hq : q * (6 : Poly) = q + q + q + q + q + q := by
    ring
  rw [hq]
  simp
  ring

theorem residualEval_C_mul_mul_four
    (B : DotForm) (r : ℝ) (q s : Poly) :
    B ((MvPolynomial.C r * q) * (4 : Poly)) s = 4 * r * B q s := by
  rw [residualEval_mul_four]
  rw [residualEval_C_mul]
  ring

theorem residualEval_C_mul_mul_two
    (B : DotForm) (r : ℝ) (q s : Poly) :
    B ((MvPolynomial.C r * q) * (2 : Poly)) s = 2 * r * B q s := by
  rw [residualEval_mul_two]
  rw [residualEval_C_mul]
  ring

theorem residualEval_C_mul_mul_six
    (B : DotForm) (r : ℝ) (q s : Poly) :
    B ((MvPolynomial.C r * q) * (6 : Poly)) s = 6 * r * B q s := by
  rw [residualEval_mul_six]
  rw [residualEval_C_mul]
  ring

theorem rankOneSelf_binaryLowRankNegativeNormalForm
    {B : DotForm} {p : Poly} {u : RankSevenVec} {x : linSubmodule}
    (hneg : binaryRestrictionCoeffA B p u x < 0) :
    HasBinaryLowRankNegativeNormalForm
      (binaryRestrictionCoeffA B p u x)
      (binaryRestrictionCoeffB B p u x x)
      (binaryRestrictionCoeffC B p u x x)
      (binaryRestrictionCoeffD B p u x x)
      (binaryRestrictionCoeffE B p u x) := by
  left
  refine ⟨binaryRestrictionCoeffA B p u x, 1, 1, hneg, Or.inl (by norm_num),
    ?_, ?_, ?_, ?_, ?_⟩
  · ring
  · simp [binaryRestrictionCoeffA, binaryRestrictionCoeffB]
    change (B ((x : Poly) * x * (x * x))) (residual p u) =
      (B (((x : Poly) * x) ^ 2)) (residual p u)
    rw [show (x : Poly) * x * (x * x) = ((x : Poly) * x) ^ 2 by ring]
  · simp [binaryRestrictionCoeffA, binaryRestrictionCoeffC]
  · simp [binaryRestrictionCoeffA, binaryRestrictionCoeffD]
    change (B ((x : Poly) * x * (x * x))) (residual p u) =
      (B (((x : Poly) * x) ^ 2)) (residual p u)
    rw [show (x : Poly) * x * (x * x) = ((x : Poly) * x) ^ 2 by ring]
  · simp [binaryRestrictionCoeffA, binaryRestrictionCoeffE]

theorem binaryRestriction_eval_eq
    (B : DotForm) (p : Poly) (u : RankSevenVec) (x y : linSubmodule) :
    ∀ X Y : ℝ,
      B ((linProduct (X • x + Y • y) (X • x + Y • y) :
          quadSubmodule).1^2) (residual p u) =
        binaryQuarticEval
          (binaryRestrictionCoeffA B p u x)
          (binaryRestrictionCoeffB B p u x y)
          (binaryRestrictionCoeffC B p u x y)
          (binaryRestrictionCoeffD B p u x y)
          (binaryRestrictionCoeffE B p u y) X Y := by
  intro X Y
  rw [binaryRestriction_pow_eq_C]
  simp only [map_add, LinearMap.add_apply]
  rw [residualEval_C_mul]
  rw [residualEval_C_mul_mul_four]
  rw [residualEval_C_mul_mul_six]
  rw [residualEval_C_mul_mul_four]
  rw [residualEval_C_mul]
  simp [binaryRestrictionCoeffA, binaryRestrictionCoeffB,
    binaryRestrictionCoeffC, binaryRestrictionCoeffD, binaryRestrictionCoeffE,
    binaryQuarticEval]
  ring

theorem binaryRestriction_quadraticCombination_sq_eq_C
    (x y : linSubmodule) (r s t : ℝ) :
    (((r • linProduct x x + s • linProduct x y + t • linProduct y y :
        quadSubmodule).1)^2) =
      MvPolynomial.C (r^2) * (linProduct x x : quadSubmodule).1^2 +
        (MvPolynomial.C (r * s) *
            ((linProduct x x : quadSubmodule).1 *
              (linProduct x y : quadSubmodule).1)) * 2 +
          (MvPolynomial.C (r * t) *
              (linProduct x y : quadSubmodule).1^2) * 2 +
            MvPolynomial.C (s^2) * (linProduct x y : quadSubmodule).1^2 +
              (MvPolynomial.C (s * t) *
                ((linProduct x y : quadSubmodule).1 *
                  (linProduct y y : quadSubmodule).1)) * 2 +
                MvPolynomial.C (t^2) * (linProduct y y : quadSubmodule).1^2 := by
  simp [linProduct, Algebra.smul_def]
  ring_nf

theorem binaryRestriction_hankelQuad_eval_eq
    (B : DotForm) (p : Poly) (u : RankSevenVec) (x y : linSubmodule)
    (r s t : ℝ) :
    B (((r • linProduct x x + s • linProduct x y + t • linProduct y y :
        quadSubmodule).1)^2) (residual p u) =
      binaryHankelQuad
        (binaryRestrictionCoeffA B p u x)
        (binaryRestrictionCoeffB B p u x y)
        (binaryRestrictionCoeffC B p u x y)
        (binaryRestrictionCoeffD B p u x y)
        (binaryRestrictionCoeffE B p u y) r s t := by
  rw [binaryRestriction_quadraticCombination_sq_eq_C]
  simp only [map_add, LinearMap.add_apply]
  rw [residualEval_C_mul]
  rw [residualEval_C_mul_mul_two]
  rw [residualEval_C_mul_mul_two]
  rw [residualEval_C_mul]
  rw [residualEval_C_mul_mul_two]
  rw [residualEval_C_mul]
  simp [binaryRestrictionCoeffA, binaryRestrictionCoeffB,
    binaryRestrictionCoeffC, binaryRestrictionCoeffD, binaryRestrictionCoeffE,
    binaryHankelQuad]
  ring

theorem binaryHankelNegativeValue_of_quadraticCombination
    {B : DotForm} {p : Poly} {u : RankSevenVec} {x y : linSubmodule}
    {r s t : ℝ}
    (hneg :
      B (((r • linProduct x x + s • linProduct x y + t • linProduct y y :
          quadSubmodule).1)^2) (residual p u) < 0) :
    HasBinaryHankelNegativeValue
      (binaryRestrictionCoeffA B p u x)
      (binaryRestrictionCoeffB B p u x y)
      (binaryRestrictionCoeffC B p u x y)
      (binaryRestrictionCoeffD B p u x y)
      (binaryRestrictionCoeffE B p u y) := by
  refine ⟨r, s, t, ?_⟩
  rwa [← binaryRestriction_hankelQuad_eval_eq B p u x y r s t]

theorem binaryHankelNegativeValue_of_mem_linProductSubmodule_span_pair
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {W : Submodule ℝ linSubmodule} {x y : linSubmodule} {q : quadSubmodule}
    (hspan : Submodule.span ℝ ({x, y} : Set linSubmodule) = W)
    (hq : q ∈ linProductSubmodule W W)
    (hneg : B (q.1^2) (residual p u) < 0) :
    HasBinaryHankelNegativeValue
      (binaryRestrictionCoeffA B p u x)
      (binaryRestrictionCoeffB B p u x y)
      (binaryRestrictionCoeffC B p u x y)
      (binaryRestrictionCoeffD B p u x y)
      (binaryRestrictionCoeffE B p u y) := by
  rcases exists_quadraticCombination_of_mem_linProductSubmodule_span_pair
      hspan hq with ⟨r, s, t, hqeq⟩
  refine binaryHankelNegativeValue_of_quadraticCombination
    (B := B) (p := p) (u := u) (x := x) (y := y)
    (r := r) (s := s) (t := t) ?_
  simpa [← hqeq] using hneg

theorem binaryRestriction_eval_eq_of_pow_expansion
    (B : DotForm) (p : Poly) (u : RankSevenVec) (x y : linSubmodule)
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
    ∀ X Y : ℝ,
      B ((linProduct (X • x + Y • y) (X • x + Y • y) :
          quadSubmodule).1^2) (residual p u) =
        binaryQuarticEval
          (binaryRestrictionCoeffA B p u x)
          (binaryRestrictionCoeffB B p u x y)
          (binaryRestrictionCoeffC B p u x y)
          (binaryRestrictionCoeffD B p u x y)
          (binaryRestrictionCoeffE B p u y) X Y := by
  intro X Y
  rw [hpow X Y]
  simp [binaryRestrictionCoeffA, binaryRestrictionCoeffB,
    binaryRestrictionCoeffC, binaryRestrictionCoeffD, binaryRestrictionCoeffE,
    binaryQuarticEval]
  ring

theorem diagonal_form_negative_pure_of_negative
    {a e : ℝ} (hneg : ∃ x y : ℝ, a * x^2 + e * y^2 < 0) :
    a < 0 ∨ e < 0 := by
  rcases hneg with ⟨x, y, hxy⟩
  by_contra hnone
  push Not at hnone
  have hx2 : 0 ≤ x^2 := sq_nonneg x
  have hy2 : 0 ≤ y^2 := sq_nonneg y
  have hax : 0 ≤ a * x^2 := mul_nonneg hnone.1 hx2
  have hey : 0 ≤ e * y^2 := mul_nonneg hnone.2 hy2
  nlinarith

theorem diagonal_form_exists_pure_negative
    {a e : ℝ} (hneg : ∃ x y : ℝ, a * x^2 + e * y^2 < 0) :
    (a < 0 ∧ a * (1 : ℝ)^2 < 0) ∨ (e < 0 ∧ e * (1 : ℝ)^2 < 0) := by
  rcases diagonal_form_negative_pure_of_negative hneg with ha | he
  · exact Or.inl ⟨ha, by simpa using ha⟩
  · exact Or.inr ⟨he, by simpa using he⟩

theorem diagonal_binaryQuarticEval_exists_negative
    {a e : ℝ} (hneg : ∃ x y : ℝ, a * x^2 + e * y^2 < 0) :
    ∃ x y : ℝ, binaryQuarticEval a 0 0 0 e x y < 0 := by
  rcases diagonal_form_negative_pure_of_negative hneg with ha | he
  · exact ⟨1, 0, by simpa [binaryQuarticEval] using ha⟩
  · exact ⟨0, 1, by simpa [binaryQuarticEval] using he⟩

theorem xy_kernel_binaryQuarticEval_exists_negative
    {a e : ℝ} (hneg : ∃ r t : ℝ, a * r^2 + e * t^2 < 0) :
    ∃ x y : ℝ, binaryQuarticEval a 0 0 0 e x y < 0 := by
  rcases hneg with ⟨r, t, hrt⟩
  exact diagonal_binaryQuarticEval_exists_negative ⟨r, t, hrt⟩

theorem rank_one_negative_value
    {ρ α β : ℝ} (hρ : ρ < 0) (hvec : α ≠ 0 ∨ β ≠ 0) :
    ρ * (α^2 + β^2)^2 < 0 := by
  have hsum_pos : 0 < α^2 + β^2 := by
    rcases hvec with hα | hβ
    · nlinarith [sq_pos_of_ne_zero hα, sq_nonneg β]
    · nlinarith [sq_nonneg α, sq_pos_of_ne_zero hβ]
  have hsquare_pos : 0 < (α^2 + β^2)^2 := sq_pos_of_pos hsum_pos
  exact mul_neg_of_neg_of_pos hρ hsquare_pos

theorem rank_one_binaryQuarticEval_exists_negative
    {ρ α β : ℝ} (hρ : ρ < 0) (hvec : α ≠ 0 ∨ β ≠ 0) :
    ∃ x y : ℝ,
      binaryQuarticEval
        (ρ * α^4) (ρ * α^3 * β) (ρ * α^2 * β^2) (ρ * α * β^3) (ρ * β^4)
        x y < 0 := by
  refine ⟨α, β, ?_⟩
  have hsum_pos : 0 < α^2 + β^2 := by
    rcases hvec with hα | hβ
    · nlinarith [sq_pos_of_ne_zero hα, sq_nonneg β]
    · nlinarith [sq_nonneg α, sq_pos_of_ne_zero hβ]
  have hpow_pos : 0 < (α^2 + β^2)^4 := pow_pos hsum_pos 4
  have heq :
      binaryQuarticEval
        (ρ * α^4) (ρ * α^3 * β) (ρ * α^2 * β^2) (ρ * α * β^3) (ρ * β^4)
        α β = ρ * (α^2 + β^2)^4 := by
    unfold binaryQuarticEval
    ring
  rw [heq]
  exact mul_neg_of_neg_of_pos hρ hpow_pos

theorem exists_linear_combination_lt_zero (a b : ℝ) (hb : b ≠ 0) :
    ∃ t : ℝ, a + 4 * b * t < 0 := by
  refine ⟨-(|a| + 1) / (4 * b), ?_⟩
  have hfour_ne : (4 : ℝ) ≠ 0 := by norm_num
  have hden_ne : 4 * b ≠ 0 := mul_ne_zero hfour_ne hb
  have hmul :
      4 * b * (-(|a| + 1) / (4 * b)) = -(|a| + 1) := by
    field_simp [hden_ne]
  rw [hmul]
  have ha_le_abs : a ≤ |a| := le_abs_self a
  linarith

theorem y_sq_kernel_binaryQuarticEval_exists_negative
    (a b : ℝ) (hb : b ≠ 0) :
    ∃ x y : ℝ, binaryQuarticEval a b 0 0 0 x y < 0 := by
  rcases exists_linear_combination_lt_zero a b hb with ⟨t, ht⟩
  refine ⟨1, t, ?_⟩
  simpa [binaryQuarticEval, mul_assoc] using ht

theorem y_sq_kernel_binaryHankelNegativeValue
    (a b : ℝ) (hb : b ≠ 0) :
    HasBinaryHankelNegativeValue a b 0 0 0 := by
  rcases exists_linear_combination_lt_zero a b hb with ⟨t, ht⟩
  refine ⟨1, 2 * t, 0, ?_⟩
  have heq : binaryHankelQuad a b 0 0 0 1 (2 * t) 0 = a + 4 * b * t := by
    unfold binaryHankelQuad
    ring
  rwa [heq]

theorem y_sq_kernel_binaryHankelNegativeValue_of_column_linearIndependent
    {a b : ℝ}
    (hLI : LinearIndependent ℝ
      ![(![a, b, 0] : Fin 3 → ℝ), (![b, 0, 0] : Fin 3 → ℝ)]) :
    HasBinaryHankelNegativeValue a b 0 0 0 :=
  y_sq_kernel_binaryHankelNegativeValue a b
    (ySqKernel_b_ne_zero_of_column_linearIndependent hLI)

theorem binaryHankelNegativeValue_of_canonicalKernelData
    {a b c d e : ℝ}
    (hcanon : HasBinaryCanonicalKernelData a b c d e) :
    HasBinaryHankelNegativeValue a b c d e := by
  rcases hcanon with hxy | hySq | hell
  · exact hxy.2
  · rcases ySq_kernel_equations_of_binaryHankelMul_eq_zero hySq.1 with
      ⟨hc, hd, he⟩
    subst c
    subst d
    subst e
    exact y_sq_kernel_binaryHankelNegativeValue_of_column_linearIndependent hySq.2
  · exact hell.2

theorem binaryNormalizedKernelPosition_of_kernelBranchCertificate
    {a b c d e : ℝ}
    (hcert : HasBinaryKernelBranchCertificate a b c d e) :
    HasBinaryNormalizedKernelPosition a b c d e := by
  rcases hcert with hxy | hySq | hell
  · rcases hxy with ⟨hb, hc, hd, _hneg⟩
    exact Or.inl (by
      ext i
      fin_cases i <;> simp [binaryHankelMul, hb, hc, hd])
  · rcases hySq with ⟨hc, hd, he, hLI⟩
    exact Or.inr (Or.inl ⟨by
      ext i
      fin_cases i <;> simp [binaryHankelMul, hc, hd, he], hLI⟩)
  · rcases hell with ⟨hc, hd, he, _hneg⟩
    exact Or.inr (Or.inr (by
      ext i
      fin_cases i <;> simp [binaryHankelMul, hc, hd, he]))

theorem binaryHankelNegativeValue_of_kernelBranchCertificate
    {a b c d e : ℝ}
    (hcert : HasBinaryKernelBranchCertificate a b c d e) :
    HasBinaryHankelNegativeValue a b c d e := by
  rcases hcert with hxy | hySq | hell
  · exact hxy.2.2.2
  · rcases hySq with ⟨hc, hd, he, hLI⟩
    subst c
    subst d
    subst e
    exact y_sq_kernel_binaryHankelNegativeValue_of_column_linearIndependent hLI
  · exact hell.2.2.2

theorem binaryHankelLinearMap_finrank_range_le_two_of_kernelBranchCertificate
    {a b c d e : ℝ}
    (hcert : HasBinaryKernelBranchCertificate a b c d e) :
    Module.finrank ℝ (LinearMap.range (binaryHankelLinearMap a b c d e)) ≤ 2 :=
  binaryHankelLinearMap_finrank_range_le_two_of_normalizedKernelPosition
    (binaryNormalizedKernelPosition_of_kernelBranchCertificate hcert)

theorem binaryKernelBranchCertificate_iff_normalizedKernelPosition_and_hankelNegative
    {a b c d e : ℝ} :
    HasBinaryKernelBranchCertificate a b c d e ↔
      HasBinaryNormalizedKernelPosition a b c d e ∧
        HasBinaryHankelNegativeValue a b c d e := by
  constructor
  · intro hcert
    exact ⟨
      binaryNormalizedKernelPosition_of_kernelBranchCertificate hcert,
      binaryHankelNegativeValue_of_kernelBranchCertificate hcert⟩
  · intro hdata
    exact binaryKernelBranchCertificate_of_normalizedKernelPosition
      hdata.1 hdata.2

theorem binaryCanonicalKernelData_iff_normalizedKernelPosition_and_hankelNegative
    {a b c d e : ℝ} :
    HasBinaryCanonicalKernelData a b c d e ↔
      HasBinaryNormalizedKernelPosition a b c d e ∧
        HasBinaryHankelNegativeValue a b c d e := by
  constructor
  · intro hcanon
    exact ⟨
      binaryNormalizedKernelPosition_of_canonicalKernelData hcanon,
      binaryHankelNegativeValue_of_canonicalKernelData hcanon⟩
  · intro hdata
    exact binaryCanonicalKernelData_of_normalizedKernelPosition
      hdata.1 hdata.2

theorem y_sq_kernel_binaryQuarticEval_exists_negative_of_rank_two
    (a b : ℝ) (_hneg : ∃ r s : ℝ, a * r^2 + 2 * b * r * s < 0)
    (hb : b ≠ 0) :
    ∃ x y : ℝ, binaryQuarticEval a b 0 0 0 x y < 0 :=
  y_sq_kernel_binaryQuarticEval_exists_negative a b hb

theorem exists_cubic_tail_lt_zero (b : ℝ) (hb : b ≠ 0) :
    ∃ t : ℝ, 4 * b * (t - t^3) < 0 := by
  by_cases hbpos : 0 < b
  · refine ⟨2, ?_⟩
    nlinarith
  · have hbneg : b < 0 := lt_of_le_of_ne (le_of_not_gt hbpos) hb
    refine ⟨-2, ?_⟩
    nlinarith

theorem exists_quartic_tail_lt_zero_of_nonzero_linear
    (a b : ℝ) (ha : a = 0) (hb : b ≠ 0) :
    ∃ t : ℝ, a * (1 - 6 * t^2 + t^4) + 4 * b * (t - t^3) < 0 := by
  rcases exists_cubic_tail_lt_zero b hb with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  rw [ha]
  simpa using ht

theorem quartic_tail_value_zero (a b : ℝ) :
    a * (1 - 6 * (0 : ℝ)^2 + (0 : ℝ)^4) + 4 * b * ((0 : ℝ) - (0 : ℝ)^3) = a := by
  ring

theorem quartic_tail_value_one (a b : ℝ) :
    a * (1 - 6 * (1 : ℝ)^2 + (1 : ℝ)^4) + 4 * b * ((1 : ℝ) - (1 : ℝ)^3) =
      -4 * a := by
  ring

theorem exists_quartic_tail_lt_zero_of_nonzero_quadratic
    (a b : ℝ) (ha : a ≠ 0) :
    ∃ t : ℝ, a * (1 - 6 * t^2 + t^4) + 4 * b * (t - t^3) < 0 := by
  by_cases hapos : 0 < a
  · refine ⟨1, ?_⟩
    rw [quartic_tail_value_one]
    nlinarith
  · have haneg : a < 0 := lt_of_le_of_ne (le_of_not_gt hapos) ha
    refine ⟨0, ?_⟩
    rw [quartic_tail_value_zero]
    exact haneg

theorem exists_quartic_tail_lt_zero
    (a b : ℝ) (hne : a ≠ 0 ∨ b ≠ 0) :
    ∃ t : ℝ, a * (1 - 6 * t^2 + t^4) + 4 * b * (t - t^3) < 0 := by
  rcases hne with ha | hb
  · exact exists_quartic_tail_lt_zero_of_nonzero_quadratic a b ha
  · by_cases ha : a = 0
    · exact exists_quartic_tail_lt_zero_of_nonzero_linear a b ha hb
    · exact exists_quartic_tail_lt_zero_of_nonzero_quadratic a b ha

theorem elliptic_kernel_binaryQuarticEval_exists_negative
    (a b : ℝ) (hne : a ≠ 0 ∨ b ≠ 0) :
    ∃ x y : ℝ, binaryQuarticEval a b (-a) (-b) a x y < 0 := by
  rcases exists_quartic_tail_lt_zero a b hne with ⟨t, ht⟩
  refine ⟨1, t, ?_⟩
  have heq :
      binaryQuarticEval a b (-a) (-b) a 1 t =
        a * (1 - 6 * t^2 + t^4) + 4 * b * (t - t^3) := by
    unfold binaryQuarticEval
    ring_nf
  rwa [heq]

theorem elliptic_kernel_binaryQuarticEval_exists_negative_of_nonzero_hankel
    (a b : ℝ) (hne : a ≠ 0 ∨ b ≠ 0)
    (_hneg : ∃ r s t : ℝ,
      a * r^2 + 2 * b * r * s - 2 * a * r * t - 2 * b * s * t + a * t^2 < 0) :
    ∃ x y : ℝ, binaryQuarticEval a b (-a) (-b) a x y < 0 :=
  elliptic_kernel_binaryQuarticEval_exists_negative a b hne

theorem binaryQuarticEval_exists_negative_of_lowRankNegativeNormalForm
    {a b c d e : ℝ}
    (hform : HasBinaryLowRankNegativeNormalForm a b c d e) :
    ∃ x y : ℝ, binaryQuarticEval a b c d e x y < 0 := by
  rcases hform with hRankOne | hxy | hySq | hell
  · rcases hRankOne with
      ⟨ρ, α, β, hρ, hvec, rfl, rfl, rfl, rfl, rfl⟩
    exact rank_one_binaryQuarticEval_exists_negative hρ hvec
  · rcases hxy with ⟨rfl, rfl, rfl, hneg⟩
    exact xy_kernel_binaryQuarticEval_exists_negative hneg
  · rcases hySq with ⟨rfl, rfl, rfl, hb⟩
    exact y_sq_kernel_binaryQuarticEval_exists_negative _ _ hb
  · rcases hell with ⟨rfl, rfl, rfl, hne⟩
    exact elliptic_kernel_binaryQuarticEval_exists_negative _ _ hne

theorem binaryQuarticEval_exists_negative_of_pullback
    {a b c d e A B C D E α β γ δ : ℝ}
    (hpull : IsBinaryQuarticPullback a b c d e A B C D E α β γ δ)
    (hneg : ∃ X Y : ℝ, binaryQuarticEval A B C D E X Y < 0) :
    ∃ x y : ℝ, binaryQuarticEval a b c d e x y < 0 := by
  rcases hneg with ⟨X, Y, hXY⟩
  refine ⟨α * X + β * Y, γ * X + δ * Y, ?_⟩
  rwa [← hpull X Y]

theorem binaryQuarticEval_exists_negative_of_pullback_lowRankNegativeNormalForm
    {a b c d e A B C D E α β γ δ : ℝ}
    (hpull : IsBinaryQuarticPullback a b c d e A B C D E α β γ δ)
    (hform : HasBinaryLowRankNegativeNormalForm A B C D E) :
    ∃ x y : ℝ, binaryQuarticEval a b c d e x y < 0 :=
  binaryQuarticEval_exists_negative_of_pullback hpull
    (binaryQuarticEval_exists_negative_of_lowRankNegativeNormalForm hform)

theorem binaryQuarticEval_exists_negative_of_canonicalKernelData
    {a b c d e : ℝ}
    (hcanon : HasBinaryCanonicalKernelData a b c d e) :
    ∃ x y : ℝ, binaryQuarticEval a b c d e x y < 0 :=
  binaryQuarticEval_exists_negative_of_lowRankNegativeNormalForm
    (binaryLowRankNegativeNormalForm_of_canonicalKernelData hcanon)

theorem binaryQuarticEval_exists_negative_of_kernelBranchCertificate
    {a b c d e : ℝ}
    (hcert : HasBinaryKernelBranchCertificate a b c d e) :
    ∃ x y : ℝ, binaryQuarticEval a b c d e x y < 0 :=
  binaryQuarticEval_exists_negative_of_lowRankNegativeNormalForm
    (binaryLowRankNegativeNormalForm_of_kernelBranchCertificate hcert)

theorem binaryQuarticEval_exists_negative_of_normalizedKernelPosition
    {a b c d e : ℝ}
    (hpos : HasBinaryNormalizedKernelPosition a b c d e)
    (hneg : HasBinaryHankelNegativeValue a b c d e) :
    ∃ x y : ℝ, binaryQuarticEval a b c d e x y < 0 :=
  binaryQuarticEval_exists_negative_of_canonicalKernelData
    (binaryCanonicalKernelData_of_normalizedKernelPosition hpos hneg)

theorem binaryQuarticEval_exists_negative_of_rankTwoNormalizedKernelClassification
    {a b c d e : ℝ}
    (hclass : HasBinaryRankTwoNormalizedKernelClassification a b c d e)
    (hneg : HasBinaryHankelNegativeValue a b c d e)
    (hrank :
      Module.finrank ℝ (LinearMap.range (binaryHankelLinearMap a b c d e)) ≤ 2) :
    ∃ x y : ℝ, binaryQuarticEval a b c d e x y < 0 :=
  binaryQuarticEval_exists_negative_of_canonicalKernelData (hclass hneg hrank)

theorem exists_negative_pure_square_of_binaryLowRankNormalForm
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {a b c d e : ℝ} {x y : linSubmodule}
    (hform : HasBinaryLowRankNegativeNormalForm a b c d e)
    (heval : ∀ X Y : ℝ,
      B ((linProduct (X • x + Y • y) (X • x + Y • y) : quadSubmodule).1^2)
          (residual p u) =
        binaryQuarticEval a b c d e X Y) :
    ∃ z : linSubmodule,
      z ∈ Submodule.span ℝ ({x, y} : Set linSubmodule) ∧
        B ((linProduct z z : quadSubmodule).1^2) (residual p u) < 0 := by
  rcases binaryQuarticEval_exists_negative_of_lowRankNegativeNormalForm hform with
    ⟨X, Y, hneg⟩
  refine ⟨X • x + Y • y, ?_, ?_⟩
  · exact Submodule.add_mem _
      (Submodule.smul_mem _ X (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ Y (Submodule.subset_span (by simp)))
  · rw [heval X Y]
    exact hneg

theorem exists_negative_pure_square_of_binaryCanonicalKernelData
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {a b c d e : ℝ} {x y : linSubmodule}
    (hcanon : HasBinaryCanonicalKernelData a b c d e)
    (heval : ∀ X Y : ℝ,
      B ((linProduct (X • x + Y • y) (X • x + Y • y) : quadSubmodule).1^2)
          (residual p u) =
        binaryQuarticEval a b c d e X Y) :
    ∃ z : linSubmodule,
      z ∈ Submodule.span ℝ ({x, y} : Set linSubmodule) ∧
        B ((linProduct z z : quadSubmodule).1^2) (residual p u) < 0 :=
  exists_negative_pure_square_of_binaryLowRankNormalForm
    (binaryLowRankNegativeNormalForm_of_canonicalKernelData hcanon) heval

theorem exists_negative_pure_square_of_binaryKernelBranchCertificate
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {a b c d e : ℝ} {x y : linSubmodule}
    (hcert : HasBinaryKernelBranchCertificate a b c d e)
    (heval : ∀ X Y : ℝ,
      B ((linProduct (X • x + Y • y) (X • x + Y • y) : quadSubmodule).1^2)
          (residual p u) =
        binaryQuarticEval a b c d e X Y) :
    ∃ z : linSubmodule,
      z ∈ Submodule.span ℝ ({x, y} : Set linSubmodule) ∧
        B ((linProduct z z : quadSubmodule).1^2) (residual p u) < 0 :=
  exists_negative_pure_square_of_binaryLowRankNormalForm
    (binaryLowRankNegativeNormalForm_of_kernelBranchCertificate hcert) heval

theorem exists_negative_pure_square_of_binaryNormalizedKernelPosition
    {B : DotForm} {p : Poly} {u : RankSevenVec}
    {a b c d e : ℝ} {x y : linSubmodule}
    (hpos : HasBinaryNormalizedKernelPosition a b c d e)
    (hneg : HasBinaryHankelNegativeValue a b c d e)
    (heval : ∀ X Y : ℝ,
      B ((linProduct (X • x + Y • y) (X • x + Y • y) : quadSubmodule).1^2)
          (residual p u) =
        binaryQuarticEval a b c d e X Y) :
    ∃ z : linSubmodule,
      z ∈ Submodule.span ℝ ({x, y} : Set linSubmodule) ∧
        B ((linProduct z z : quadSubmodule).1^2) (residual p u) < 0 :=
  exists_negative_pure_square_of_binaryCanonicalKernelData
    (binaryCanonicalKernelData_of_normalizedKernelPosition hpos hneg) heval

end QuaternaryQuartic
