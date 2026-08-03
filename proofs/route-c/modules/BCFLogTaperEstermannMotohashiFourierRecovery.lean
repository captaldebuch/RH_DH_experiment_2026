import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiCuspInvariance

/-!
# BT1-C2: Motohashi two-variable Fourier recovery and the first seminorm test

Motohashi (6.5.20) samples the two-dimensional Fourier transform of a
big-cell seed in the two unipotent coordinates.  Equation (6.5.21) is the
anisotropic change of variables

`x₁ = y₁ / m`, `x₂ = m u y₂`, `U = m n u`.

This file formalizes the Euclidean Fourier-recovery part on Schwartz space,
the exact phase/Jacobian identity behind that change of variables, and a
sharp necessary seminorm bound for the radial modulus interpolation from
BT1-C1.

The bound gives a genuine stop-test result.  Every unit-normalized selector
at `u = q²` has first Schwartz seminorm at least `q²`; hence no such family
is uniformly bounded in the modulus.  This rules out feeding the C1 family
unchanged into a trace theorem whose constants require a uniform Schwartz
seminorm.  It does not rule out a different global weighted seed.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiFourierRecovery

open Complex MeasureTheory Real SchwartzMap Set
open scoped BigOperators ContDiff FourierTransform ComplexInnerProductSpace
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiCuspInvariance

/-- The Euclidean plane of the two unipotent big-cell coordinates. -/
abbrev H15MotohashiUnipotentPlane := EuclideanSpace ℝ (Fin 2)

/-- Motohashi's frequency pair in (6.5.20). -/
noncomputable def h15MotohashiFourierFrequency
    (δ₁ δ₂ m n u : ℝ) : H15MotohashiUnipotentPlane :=
  WithLp.toLp 2 ![δ₁ * m, δ₂ * n / u]

/-- A Schwartz-valued radial big-cell profile. -/
abbrev H15MotohashiSchwartzProfile :=
  ℝ → SchwartzMap H15MotohashiUnipotentPlane ℂ

set_option maxSynthPendingDepth 8 in
/-- The two-variable Fourier sample occurring in Motohashi (6.5.20). -/
noncomputable def h15MotohashiTwoVariableFourierSample
    (F : H15MotohashiSchwartzProfile)
    (δ₁ δ₂ m n u : ℝ) : ℂ :=
  SchwartzMap.fourierTransformCLM ℂ (F u)
    (h15MotohashiFourierFrequency δ₁ δ₂ m n u)

set_option maxSynthPendingDepth 8 in
/-- The sample is exactly the standard two-dimensional Fourier integral.
This is the analytic inner integral in Motohashi (6.5.20), with Mathlib's
`exp (-2π i <x,ξ>)` convention. -/
theorem h15MotohashiTwoVariableFourierSample_eq_integral
    (F : H15MotohashiSchwartzProfile)
    (δ₁ δ₂ m n u : ℝ) :
    h15MotohashiTwoVariableFourierSample F δ₁ δ₂ m n u =
      ∫ x : H15MotohashiUnipotentPlane,
        𝐞 (-inner ℝ x (h15MotohashiFourierFrequency δ₁ δ₂ m n u)) •
          F u x := by
  unfold h15MotohashiTwoVariableFourierSample
  rw [SchwartzMap.fourierTransformCLM_apply,
    SchwartzMap.fourier_coe, Real.fourier_eq]

set_option maxSynthPendingDepth 8 in
/-- Inverse Fourier construction of a physical big-cell seed from a desired
Schwartz frequency profile. -/
noncomputable def h15MotohashiRecoveredProfile
    (Phi : H15MotohashiSchwartzProfile) : H15MotohashiSchwartzProfile :=
  fun u => 𝓕⁻ (Phi u)

set_option maxSynthPendingDepth 8 in
/-- **Exact two-variable Fourier recovery.**  This is unconditional
Fourier inversion on Schwartz space; no distributional or almost-everywhere
qualification remains. -/
theorem h15MotohashiTwoVariableFourier_recovered
    (Phi : H15MotohashiSchwartzProfile) (u : ℝ) :
    SchwartzMap.fourierTransformCLM ℂ
      (h15MotohashiRecoveredProfile Phi u) = Phi u := by
  simp [h15MotohashiRecoveredProfile]

theorem h15MotohashiTwoVariableFourierSample_recovered
    (Phi : H15MotohashiSchwartzProfile)
    (δ₁ δ₂ m n u : ℝ) :
    h15MotohashiTwoVariableFourierSample
        (h15MotohashiRecoveredProfile Phi) δ₁ δ₂ m n u =
      Phi u (h15MotohashiFourierFrequency δ₁ δ₂ m n u) := by
  unfold h15MotohashiTwoVariableFourierSample
  rw [h15MotohashiTwoVariableFourier_recovered]

/-! ## The (6.5.20) to (6.5.21) scaling -/

/-- The scalar additive phase used in the displayed Motohashi integrals. -/
noncomputable def h15MotohashiPlanePhase
    (δ₁ δ₂ m n u x₁ x₂ : ℝ) : ℂ :=
  Complex.exp
    (-((2 * Real.pi : ℂ) * Complex.I) *
      ((δ₁ * m * x₁ + δ₂ * n * x₂ / u : ℝ) : ℂ))

/-- The anisotropic big-cell coordinate substitution in (6.5.21). -/
noncomputable def h15MotohashiScaledPlanePoint
    (m u y₁ y₂ : ℝ) : H15MotohashiUnipotentPlane :=
  WithLp.toLp 2 ![y₁ / m, m * u * y₂]

/-- Under `U = m n u`, the two oscillatory phases in (6.5.20) become the
unit frequencies displayed in (6.5.21). -/
theorem h15MotohashiPlanePhase_scaled
    (δ₁ δ₂ m n u y₁ y₂ : ℝ)
    (hm : m ≠ 0) (hn : n ≠ 0) (hu : u ≠ 0) :
    h15MotohashiPlanePhase δ₁ δ₂ m n (m * n * u)
        (y₁ / m) (m * u * y₂) =
      h15MotohashiPlanePhase δ₁ δ₂ 1 1 1 y₁ y₂ := by
  unfold h15MotohashiPlanePhase
  congr 2
  push_cast
  field_simp [hm, hn, hu]

/-- The inner double integral in (6.5.20), written without representation-
theoretic notation. -/
noncomputable def h15MotohashiUnscaledPlaneIntegral
    (F : ℝ → ℝ → ℝ → ℂ)
    (δ₁ δ₂ m n U : ℝ) : ℂ :=
  ∫ x₁ : ℝ, ∫ x₂ : ℝ,
    F x₁ x₂ U * h15MotohashiPlanePhase δ₁ δ₂ m n U x₁ x₂

/-- The rescaled inner integral displayed in (6.5.21). -/
noncomputable def h15MotohashiScaledPlaneIntegral
    (F : ℝ → ℝ → ℝ → ℂ)
    (δ₁ δ₂ m n u : ℝ) : ℂ :=
  ∫ y₁ : ℝ, ∫ y₂ : ℝ,
    F (y₁ / m) (m * u * y₂) (m * n * u) *
      h15MotohashiPlanePhase δ₁ δ₂ 1 1 1 y₁ y₂

/-- **Motohashi (6.5.20)--(6.5.21), inner Jacobian identity.**

The scaled double integral is `u⁻¹` times the unscaled integral at
`U = m n u`.  The proof uses the two one-dimensional Haar changes of
variables, whose Jacobians are `m` and `(m u)⁻¹`. -/
theorem h15MotohashiScaledPlaneIntegral_eq
    (F : ℝ → ℝ → ℝ → ℂ)
    (δ₁ δ₂ m n u : ℝ)
    (hm : 0 < m) (hn : 0 < n) (hu : 0 < u) :
    h15MotohashiScaledPlaneIntegral F δ₁ δ₂ m n u =
      u⁻¹ • h15MotohashiUnscaledPlaneIntegral
        F δ₁ δ₂ m n (m * n * u) := by
  let H : ℝ → ℝ → ℂ := fun x₁ x₂ =>
    F x₁ x₂ (m * n * u) *
      h15MotohashiPlanePhase δ₁ δ₂ m n (m * n * u) x₁ x₂
  have hphase (y₁ y₂ : ℝ) :
      F (y₁ / m) (m * u * y₂) (m * n * u) *
          h15MotohashiPlanePhase δ₁ δ₂ 1 1 1 y₁ y₂ =
        H (y₁ / m) (m * u * y₂) := by
    unfold H
    rw [h15MotohashiPlanePhase_scaled δ₁ δ₂ m n u y₁ y₂
      hm.ne' hn.ne' hu.ne']
  have hinner (y₁ : ℝ) :
      (∫ y₂ : ℝ, H (y₁ / m) (m * u * y₂)) =
        |(m * u)⁻¹| • ∫ x₂ : ℝ, H (y₁ / m) x₂ := by
    exact Measure.integral_comp_mul_left (fun x₂ => H (y₁ / m) x₂) (m * u)
  have houter :
      (∫ y₁ : ℝ, ∫ x₂ : ℝ, H (y₁ / m) x₂) =
        |m| • ∫ x₁ : ℝ, ∫ x₂ : ℝ, H x₁ x₂ := by
    simpa only [div_eq_inv_mul] using
      Measure.integral_comp_inv_mul_left (fun x₁ => ∫ x₂ : ℝ, H x₁ x₂) m
  unfold h15MotohashiScaledPlaneIntegral h15MotohashiUnscaledPlaneIntegral
  simp_rw [hphase, hinner]
  rw [integral_smul, houter]
  change |(m * u)⁻¹| •
      (|m| • (∫ x₁ : ℝ, ∫ x₂ : ℝ, H x₁ x₂)) =
    u⁻¹ • (∫ x₁ : ℝ, ∫ x₂ : ℝ, H x₁ x₂)
  rw [abs_inv, abs_of_pos hm, abs_of_pos (mul_pos hm hu)]
  simp only [smul_smul]
  congr 1
  field_simp [hm.ne', hu.ne']

/-- The complete radial transform on the left side of Motohashi (6.5.21),
before the substitution `U = m n u`.  The generic function `J` stands for
the Jacquet/Bessel kernel `j_ν`. -/
noncomputable def h15MotohashiUnscaledKernelTransform
    (F : ℝ → ℝ → ℝ → ℂ) (J : ℝ → ℂ)
    (δ₁ δ₂ m n : ℝ) : ℂ :=
  ∫ U in Ioi 0,
    U⁻¹ • (J (δ₁ * δ₂ * m * n / U) *
      h15MotohashiUnscaledPlaneIntegral F δ₁ δ₂ m n U)

/-- The complete radial transform after Motohashi's anisotropic substitution.
This is the right side of (6.5.21). -/
noncomputable def h15MotohashiScaledKernelTransform
    (F : ℝ → ℝ → ℝ → ℂ) (J : ℝ → ℂ)
    (δ₁ δ₂ m n : ℝ) : ℂ :=
  ∫ u in Ioi 0,
    J (δ₁ * δ₂ / u) *
      h15MotohashiScaledPlaneIntegral F δ₁ δ₂ m n u

/-- **Full Motohashi (6.5.20)--(6.5.21) change of variables.**

After `U = m n u`, the radial Haar measure, the inner Jacobian, the Jacquet
kernel, and the two-variable phase combine to give exactly the scaled
transform.  No convergence hypothesis is needed for the equality because
Mathlib's Haar change-of-variables theorem is stated for the totalized
Bochner integral. -/
theorem h15MotohashiUnscaledKernelTransform_eq_scaled
    (F : ℝ → ℝ → ℝ → ℂ) (J : ℝ → ℂ)
    (δ₁ δ₂ m n : ℝ) (hm : 0 < m) (hn : 0 < n) :
    h15MotohashiUnscaledKernelTransform F J δ₁ δ₂ m n =
      h15MotohashiScaledKernelTransform F J δ₁ δ₂ m n := by
  let c : ℝ := m * n
  have hc : 0 < c := mul_pos hm hn
  let G : ℝ → ℂ := fun U =>
    U⁻¹ • (J (δ₁ * δ₂ * m * n / U) *
      h15MotohashiUnscaledPlaneIntegral F δ₁ δ₂ m n U)
  have hchange :
      (∫ u in Ioi 0, G (c * u)) =
        c⁻¹ • ∫ U in Ioi 0, G U := by
    simpa using integral_comp_mul_left_Ioi G 0 hc
  have hpoint (u : ℝ) (hu : u ∈ Ioi (0 : ℝ)) :
      c • G (c * u) =
        J (δ₁ * δ₂ / u) *
          h15MotohashiScaledPlaneIntegral F δ₁ δ₂ m n u := by
    have hu' : 0 < u := hu
    have hkernel : δ₁ * δ₂ * m * n / (c * u) = δ₁ * δ₂ / u := by
      dsimp [c]
      field_simp [hm.ne', hn.ne', hu'.ne']
    have hplane := h15MotohashiScaledPlaneIntegral_eq
      F δ₁ δ₂ m n u hm hn hu'
    dsimp [G]
    rw [hkernel, hplane]
    simp only [c, Complex.real_smul, ofReal_mul]
    push_cast
    field_simp [hm.ne', hn.ne', hu'.ne']
  unfold h15MotohashiUnscaledKernelTransform
    h15MotohashiScaledKernelTransform
  change (∫ U in Ioi 0, G U) = _
  calc
    (∫ U in Ioi 0, G U) = c • ∫ u in Ioi 0, G (c * u) := by
      rw [hchange]
      simp [hc.ne']
    _ = ∫ u in Ioi 0, c • G (c * u) := by
      rw [integral_smul]
    _ = ∫ u in Ioi 0,
        J (δ₁ * δ₂ / u) *
          h15MotohashiScaledPlaneIntegral F δ₁ δ₂ m n u := by
      exact setIntegral_congr_fun measurableSet_Ioi hpoint

/-! ## Quantitative radial seminorm stop test -/

/-- The explicit compactly supported radial selector from BT1-C1, now
bundled as a Schwartz function. -/
noncomputable def h15MotohashiRadialSchwartzSelector (q : ℕ) :
    SchwartzMap ℝ ℂ :=
  (h15MotohashiRadialSelector_hasCompactSupport q).toSchwartzMap
    (h15MotohashiRadialSelector_smooth q)

@[simp]
theorem h15MotohashiRadialSchwartzSelector_apply (q : ℕ) (u : ℝ) :
    h15MotohashiRadialSchwartzSelector q u =
      h15MotohashiRadialSelector q u :=
  rfl

/-- Any Schwartz function taking the value one at `q²` has first weighted
Schwartz seminorm at least `q²`.  This lower bound is independent of the
choice of bump or interpolation construction. -/
theorem h15Motohashi_unit_sample_le_first_seminorm
    (f : SchwartzMap ℝ ℂ) (q : ℕ)
    (hsample : f (h15MotohashiRadialSample q) = 1) :
    h15MotohashiRadialSample q ≤ (SchwartzMap.seminorm ℂ 1 0) f := by
  have h := SchwartzMap.norm_pow_mul_le_seminorm ℂ f 1
    (h15MotohashiRadialSample q)
  rw [hsample] at h
  simpa [h15MotohashiRadialSample, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg (q : ℝ))] using h

/-- Sharp lower bound for the concrete selectors constructed in BT1-C1. -/
theorem h15MotohashiRadialSchwartzSelector_first_seminorm_lower
    (q : ℕ) :
    (q : ℝ) ^ 2 ≤
      (SchwartzMap.seminorm ℂ 1 0)
        (h15MotohashiRadialSchwartzSelector q) := by
  apply h15Motohashi_unit_sample_le_first_seminorm
  simp

/-- **Quantitative BT1-C2 stop result.**  No exact unit-normalized radial
interpolation at the samples `q²` can have a uniform first Schwartz
seminorm. -/
theorem no_uniform_first_seminorm_of_unit_radial_samples
    (R : ℕ → SchwartzMap ℝ ℂ)
    (hsample : ∀ q : ℕ, R q (h15MotohashiRadialSample q) = 1) :
    ¬ ∃ C : ℝ, ∀ q : ℕ,
      (SchwartzMap.seminorm ℂ 1 0) (R q) ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨q : ℕ, hq⟩ := exists_nat_gt (max C 1)
  have hqC : C < (q : ℝ) := lt_of_le_of_lt (le_max_left C 1) hq
  have hq1 : 1 < (q : ℝ) := lt_of_le_of_lt (le_max_right C 1) hq
  have hlower := h15Motohashi_unit_sample_le_first_seminorm
    (R q) q (hsample q)
  change (q : ℝ) ^ 2 ≤ (SchwartzMap.seminorm ℂ 1 0) (R q) at hlower
  have hupper := hC q
  have hqsq : (q : ℝ) < (q : ℝ) ^ 2 := by nlinarith
  linarith

/-- In particular, the explicit C1 selector family fails the uniform
Schwartz-seminorm requirement. -/
theorem no_uniform_first_seminorm_radialSchwartzSelector :
    ¬ ∃ C : ℝ, ∀ q : ℕ,
      (SchwartzMap.seminorm ℂ 1 0)
        (h15MotohashiRadialSchwartzSelector q) ≤ C := by
  apply no_uniform_first_seminorm_of_unit_radial_samples
  intro q
  simp

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiFourierRecovery
