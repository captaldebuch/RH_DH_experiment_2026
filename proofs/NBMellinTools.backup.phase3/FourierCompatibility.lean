/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Compatibility of the integral and `L²` Fourier transforms

Mathlib defines the Fourier transform of an integrable function pointwise and
the Fourier transform on `Lp` as an `L²` isometry. This file proves that the
two representatives agree almost everywhere on `L¹ ∩ L²(ℝ)`.
-/

open scoped FourierTransform ContDiff InnerProductSpace
open MeasureTheory Set Complex

namespace NBMellinTools

/-- On the real line, the pointwise Fourier integral of an `L¹ ∩ L²`
function is the almost-everywhere representative of its `L²` Fourier
transform. -/
theorem fourierIntegral_ae_eq_LpFourier_of_integrable_memLp_two
    (g : ℝ → ℂ) (hg1 : Integrable g) (hg2 : MemLp g 2 volume) :
    (𝓕 g) =ᵐ[volume] (𝓕 hg2.toLp : Lp ℂ 2 volume) := by
  apply ae_eq_of_integral_contDiff_smul_eq
  · apply (VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (innerSL ℝ).continuous₂ hg1).locallyIntegrable
  · exact (Lp.memLp (𝓕 hg2.toLp)).locallyIntegrable (by norm_num)
  intro φ hφsmooth hφsupport
  let φc : SchwartzMap ℝ ℂ :=
    (hφsupport.comp_left rfl).toSchwartzMap
      ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).contDiff.comp hφsmooth)
  have hφc : ∀ x : ℝ, φc x = (φ x : ℂ) := by
    intro x
    rfl
  have hswap :
      ∫ x : ℝ, (𝓕 g) x • φc x =
        ∫ x : ℝ, g x • (𝓕 (φc : ℝ → ℂ)) x := by
    have hinter : (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip =
        (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ) := by
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      simp only [LinearMap.flip_apply, innerₗ_apply_apply]
      exact real_inner_comm _ _
    have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
      (e := Real.fourierChar) (μ := volume) (ν := volume) (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner hg1 φc.integrable
    simpa only [FourierTransform.fourier, hinter] using h
  have hdist := congrArg (fun T => T φc)
    (MeasureTheory.Lp.fourier_toTemperedDistribution_eq hg2.toLp)
  simp only [TemperedDistribution.fourier_apply,
    MeasureTheory.Lp.toTemperedDistribution_apply] at hdist
  have htest_fourier :
      ∫ x : ℝ, φ x • (𝓕 g) x = ∫ x : ℝ, φc x • (𝓕 g) x := by
    apply integral_congr_ae
    filter_upwards with x
    rw [Complex.real_smul, hφc x, smul_eq_mul]
  have htest_lp :
      ∫ x : ℝ, φ x • (𝓕 hg2.toLp : Lp ℂ 2 volume) x =
        ∫ x : ℝ, φc x • (𝓕 hg2.toLp : Lp ℂ 2 volume) x := by
    apply integral_congr_ae
    filter_upwards with x
    rw [Complex.real_smul, hφc x, smul_eq_mul]
  calc
    ∫ x : ℝ, φ x • (𝓕 g) x = ∫ x : ℝ, φc x • (𝓕 g) x := htest_fourier
    _ = ∫ x : ℝ, (𝓕 g) x • φc x := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [smul_eq_mul, mul_comm]
    _ = ∫ x : ℝ, g x • (𝓕 (φc : ℝ → ℂ)) x := hswap
    _ = ∫ x : ℝ, (𝓕 (φc : ℝ → ℂ)) x • g x := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [smul_eq_mul, mul_comm]
    _ = ∫ x : ℝ, (𝓕 (φc : ℝ → ℂ)) x •
        ((hg2.toLp : Lp ℂ 2 volume) : ℝ → ℂ) x := by
      apply integral_congr_ae
      filter_upwards [hg2.coeFn_toLp] with x hx
      rw [hx]
    _ = ∫ x : ℝ, φc x • (𝓕 hg2.toLp : Lp ℂ 2 volume) x := hdist
    _ = ∫ x : ℝ, φ x • (𝓕 hg2.toLp : Lp ℂ 2 volume) x := htest_lp.symm

/-- Exact Plancherel equality for the integral Fourier transform on an
`L¹ ∩ L²` function. -/
theorem integral_sq_norm_fourier_eq_integral_sq_norm
    (g : ℝ → ℂ) (hg1 : Integrable g) (hg2 : MemLp g 2 volume) :
    (∫ x : ℝ, ‖𝓕 g x‖ ^ 2) = ∫ x : ℝ, ‖g x‖ ^ 2 := by
  have hcompat := fourierIntegral_ae_eq_LpFourier_of_integrable_memLp_two g hg1 hg2
  calc
    (∫ x : ℝ, ‖𝓕 g x‖ ^ 2) =
        ∫ x : ℝ, ‖(𝓕 hg2.toLp : Lp ℂ 2 volume) x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hcompat] with x hx
      rw [hx]
    _ = ∫ x : ℝ, ‖(hg2.toLp g : Lp ℂ 2 volume) x‖ ^ 2 := by
      apply Complex.ofRealLI.injective
      rw [← LinearIsometry.integral_comp_comm,
        ← LinearIsometry.integral_comp_comm]
      calc
        ∫ x : ℝ, Complex.ofRealLI (‖(𝓕 hg2.toLp : Lp ℂ 2 volume) x‖ ^ 2) =
            ∫ x : ℝ, ⟪(𝓕 hg2.toLp : Lp ℂ 2 volume) x,
              (𝓕 hg2.toLp : Lp ℂ 2 volume) x⟫_ℂ := by
          apply integral_congr_ae
          filter_upwards with x
          change (↑(‖(𝓕 hg2.toLp : Lp ℂ 2 volume) x‖ ^ 2) : ℂ) =
            ⟪(𝓕 hg2.toLp : Lp ℂ 2 volume) x,
              (𝓕 hg2.toLp : Lp ℂ 2 volume) x⟫_ℂ
          rw [inner_self_eq_norm_sq_to_K]
          norm_cast
        _ = ⟪(𝓕 hg2.toLp : Lp ℂ 2 volume),
            (𝓕 hg2.toLp : Lp ℂ 2 volume)⟫_ℂ :=
          (MeasureTheory.L2.inner_def _ _).symm
        _ = ⟪(hg2.toLp g : Lp ℂ 2 volume),
            (hg2.toLp g : Lp ℂ 2 volume)⟫_ℂ :=
          MeasureTheory.Lp.inner_fourier_eq (hg2.toLp g) (hg2.toLp g)
        _ = ∫ x : ℝ, ⟪(hg2.toLp g : Lp ℂ 2 volume) x,
            (hg2.toLp g : Lp ℂ 2 volume) x⟫_ℂ :=
          MeasureTheory.L2.inner_def _ _
        _ = ∫ x : ℝ, Complex.ofRealLI
            (‖(hg2.toLp g : Lp ℂ 2 volume) x‖ ^ 2) := by
          apply integral_congr_ae
          filter_upwards with x
          change ⟪(hg2.toLp g : Lp ℂ 2 volume) x,
              (hg2.toLp g : Lp ℂ 2 volume) x⟫_ℂ =
            (↑(‖(hg2.toLp g : Lp ℂ 2 volume) x‖ ^ 2) : ℂ)
          rw [inner_self_eq_norm_sq_to_K]
          norm_cast
    _ = ∫ x : ℝ, ‖g x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hg2.coeFn_toLp] with x hx
      rw [hx]

/-- The `2π` critical-line frequency coordinate has exactly the Jacobian
needed to recover the unscaled Fourier `L²` energy. -/
theorem criticalLineFrequencyEnergy_eq_fourierNormSq (g : ℝ → ℂ) :
    (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖𝓕 g (t / (2 * Real.pi))‖ ^ 2 =
      ∫ ξ : ℝ, ‖𝓕 g ξ‖ ^ 2 := by
  change (1 / (2 * Real.pi)) *
      ∫ t : ℝ, (fun ξ : ℝ => ‖𝓕 g ξ‖ ^ 2) (t / (2 * Real.pi)) = _
  have hscale := Measure.integral_comp_div
    (fun ξ : ℝ => ‖𝓕 g ξ‖ ^ 2) (2 * Real.pi)
  rw [hscale]
  have hpos : 0 < 2 * Real.pi := by positivity
  rw [abs_of_pos hpos, smul_eq_mul]
  field_simp [ne_of_gt Real.pi_pos]

end NBMellinTools
