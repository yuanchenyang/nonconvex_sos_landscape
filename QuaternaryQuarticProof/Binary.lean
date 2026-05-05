import QuaternaryQuarticProof.Syzygy

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace QuaternaryQuartic

def binaryQuarticEval (a b c d e x y : ℝ) : ℝ :=
  a * x^4 + 4 * b * x^3 * y + 6 * c * x^2 * y^2 + 4 * d * x * y^3 + e * y^4

def binaryHankelQuad (a b c d e r s t : ℝ) : ℝ :=
  a * r^2 + 2 * b * r * s + 2 * c * r * t + c * s^2 + 2 * d * s * t + e * t^2

def binaryHankelMul (a b c d e : ℝ) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![a * v 0 + b * v 1 + c * v 2,
    b * v 0 + c * v 1 + d * v 2,
    c * v 0 + d * v 1 + e * v 2]

def HasBinaryHankelNegativeValue (a b c d e : ℝ) : Prop :=
  ∃ r s t : ℝ, binaryHankelQuad a b c d e r s t < 0

def HasBinaryKernelBranchCertificate (a b c d e : ℝ) : Prop :=
  (b = 0 ∧ c = 0 ∧ d = 0 ∧
    HasBinaryHankelNegativeValue a b c d e) ∨
  (c = 0 ∧ d = 0 ∧ e = 0 ∧
    LinearIndependent ℝ
      ![(![a, b, 0] : Fin 3 → ℝ), (![b, 0, 0] : Fin 3 → ℝ)]) ∨
  (c = -a ∧ d = -b ∧ e = a ∧
    HasBinaryHankelNegativeValue a b c d e)

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

end QuaternaryQuartic
