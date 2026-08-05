/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.FourierCompatibility
import Mathlib.Analysis.MellinInversion

/-!
# Mellin--Plancherel on the positive half-line

The logarithmic change of variables `x = exp (-u)`, with the half-density
`exp (-u/2)`, turns the Mellin transform on `Re s = 1/2` into Mathlib's
ordinary Fourier transform.  This module proves the resulting squared-norm
identity for measurable representatives whose logarithmic pullback belongs
to `L¹ ∩ L²`.
-/

open MeasureTheory Set Complex
open scoped FourierTransform

namespace NBMellinTools

/-- Half-density logarithmic pullback from `(0,∞)` to the real line. -/
noncomputable def mellinLogPullback (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  Real.exp (-u / 2) • f (Real.exp (-u))

private theorem rexp_neg_deriv :
    ∀ u ∈ (univ : Set ℝ),
      HasDerivWithinAt (Real.exp ∘ Neg.neg) (-Real.exp (-u)) univ u :=
  fun u _ ↦ mul_neg_one (Real.exp (-u)) ▸
    ((Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)).hasDerivWithinAt

private theorem rexp_neg_image :
    (Real.exp ∘ Neg.neg) '' (univ : Set ℝ) = Ioi 0 := by
  rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective,
    Set.image_univ, Real.range_exp]

private theorem rexp_neg_injOn :
    (univ : Set ℝ).InjOn (Real.exp ∘ Neg.neg) :=
  Real.exp_injective.injOn.comp neg_injective.injOn (univ.mapsTo_univ _)

/-- The logarithmic half-density is an exact `L²` coordinate change. -/
theorem integral_sq_norm_mellinLogPullback (f : ℝ → ℂ) :
    (∫ u : ℝ, ‖mellinLogPullback f u‖ ^ 2) =
      ∫ x in Ioi (0 : ℝ), ‖f x‖ ^ 2 := by
  calc
    (∫ u : ℝ, ‖mellinLogPullback f u‖ ^ 2) =
        ∫ u : ℝ, Real.exp (-u) * ‖f (Real.exp (-u))‖ ^ 2 := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with u
      unfold mellinLogPullback
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
      have hexp : Real.exp (-u / 2) ^ 2 = Real.exp (-u) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      rw [hexp]
    _ = ∫ x in (Real.exp ∘ Neg.neg) '' (univ : Set ℝ), ‖f x‖ ^ 2 := by
      rw [MeasureTheory.integral_image_eq_integral_abs_deriv_smul
        MeasurableSet.univ rexp_neg_deriv rexp_neg_injOn]
      simp only [Measure.restrict_univ]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with u
      simp only [Function.comp_apply, abs_neg,
        abs_of_pos (Real.exp_pos _), smul_eq_mul]
    _ = ∫ x in Ioi (0 : ℝ), ‖f x‖ ^ 2 := by
      rw [rexp_neg_image]

/-- The logarithmic coordinate change transports `L²` membership. -/
theorem mellinLogPullback_memLp_two_of_measurable
    (f : ℝ → ℂ) (hfmeas : Measurable f)
    (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ)))) :
    MemLp (mellinLogPullback f) 2 volume := by
  have hpullback_meas : Measurable (mellinLogPullback f) := by
    unfold mellinLogPullback
    apply Measurable.smul
    · exact (Real.continuous_exp.comp
        (continuous_neg.div_const 2)).measurable
    · exact hfmeas.comp
        (Real.continuous_exp.comp continuous_neg).measurable
  apply (memLp_two_iff_integrable_sq_norm
    hpullback_meas.aestronglyMeasurable).2
  have hsource : Integrable (fun x : ℝ => ‖f x‖ ^ 2)
      (volume.restrict (Ioi (0 : ℝ))) :=
    hf.integrable_norm_pow (by norm_num)
  have himage : IntegrableOn (fun x : ℝ => ‖f x‖ ^ 2)
      ((Real.exp ∘ Neg.neg) '' (univ : Set ℝ)) := by
    simpa only [rexp_neg_image] using hsource
  have hcoordinateOn :=
    (MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
      MeasurableSet.univ rexp_neg_deriv rexp_neg_injOn
      (fun x : ℝ => ‖f x‖ ^ 2)).mp himage
  have hcoordinate : Integrable
      (fun u : ℝ => Real.exp (-u) * ‖f (Real.exp (-u))‖ ^ 2) := by
    rw [integrableOn_univ] at hcoordinateOn
    simpa only [Function.comp_apply, abs_neg,
      abs_of_pos (Real.exp_pos _), smul_eq_mul] using hcoordinateOn
  apply hcoordinate.congr
  filter_upwards with u
  unfold mellinLogPullback
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
  have hexp : Real.exp (-u / 2) ^ 2 = Real.exp (-u) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]

/-- Standard point `1/2 + it` on the critical line. -/
noncomputable def mellinCriticalLinePoint (t : ℝ) : ℂ :=
  ((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)

@[simp] theorem mellinCriticalLinePoint_re (t : ℝ) :
    (mellinCriticalLinePoint t).re = 1 / 2 := by
  simp [mellinCriticalLinePoint]

@[simp] theorem mellinCriticalLinePoint_im (t : ℝ) :
    (mellinCriticalLinePoint t).im = t := by
  simp [mellinCriticalLinePoint]

/-- On the critical line, Mellin transform is the Fourier transform of the
logarithmic pullback with Mathlib's `2π` frequency convention. -/
theorem mellin_criticalLine_eq_fourier_mellinLogPullback
    (f : ℝ → ℂ) (t : ℝ) :
    mellin f (mellinCriticalLinePoint t) =
      𝓕 (mellinLogPullback f) (t / (2 * Real.pi)) := by
  rw [mellin_eq_fourier, mellinCriticalLinePoint_re,
    mellinCriticalLinePoint_im]
  apply congrArg (fun g : ℝ → ℂ => 𝓕 g (t / (2 * Real.pi)))
  funext u
  unfold mellinLogPullback
  congr 1
  ring_nf

/-- Function-level Mellin--Plancherel theorem on `(0,∞)`.  The explicit
`L¹` hypothesis selects the pointwise Fourier integral representative. -/
theorem mellin_plancherel_positive_half_line_of_measurable
    (f : ℝ → ℂ) (hfmeas : Measurable f)
    (hf2 : MemLp f 2 (volume.restrict (Ioi (0 : ℝ))))
    (hlog : Integrable (mellinLogPullback f)) :
    (∫ x in Ioi (0 : ℝ), ‖f x‖ ^ 2) =
      (1 / (2 * Real.pi)) * ∫ t : ℝ,
        ‖mellin f (mellinCriticalLinePoint t)‖ ^ 2 := by
  have hpullback : MemLp (mellinLogPullback f) 2 volume :=
    mellinLogPullback_memLp_two_of_measurable f hfmeas hf2
  calc
    (∫ x in Ioi (0 : ℝ), ‖f x‖ ^ 2) =
        ∫ u : ℝ, ‖mellinLogPullback f u‖ ^ 2 :=
      (integral_sq_norm_mellinLogPullback f).symm
    _ = ∫ ξ : ℝ, ‖𝓕 (mellinLogPullback f) ξ‖ ^ 2 :=
      (integral_sq_norm_fourier_eq_integral_sq_norm
        (mellinLogPullback f) hlog hpullback).symm
    _ = (1 / (2 * Real.pi)) * ∫ t : ℝ,
        ‖𝓕 (mellinLogPullback f) (t / (2 * Real.pi))‖ ^ 2 :=
      (criticalLineFrequencyEnergy_eq_fourierNormSq
        (mellinLogPullback f)).symm
    _ = (1 / (2 * Real.pi)) * ∫ t : ℝ,
        ‖mellin f (mellinCriticalLinePoint t)‖ ^ 2 := by
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards with t
      rw [mellin_criticalLine_eq_fourier_mellinLogPullback]

end NBMellinTools
