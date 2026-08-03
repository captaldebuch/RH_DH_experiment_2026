/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Continuous integral evaluation on an `L²` domain

The reusable functional-analytic core of off-line Mellin evaluation is just
Cauchy--Schwarz on a region where the Mellin kernel is square-integrable.
This formulation works for any measure and any measurable region.
-/

open MeasureTheory Set

namespace NBMellinTools

/-- Cauchy--Schwarz for a scalar kernel acting on a complex-valued function,
stated with the explicit square integrals needed by Mellin applications. -/
theorem norm_setIntegral_mul_le_sqrt_mul_sqrt
    (f g : α → ℂ) [MeasurableSpace α] (s : Set α) (μ : Measure α)
    (hf : MemLp f 2 (μ.restrict s)) (hg : MemLp g 2 (μ.restrict s)) :
    ‖∫ x in s, f x * g x ∂μ‖ ≤
      Real.sqrt (∫ x in s, ‖f x‖ ^ 2 ∂μ) *
        Real.sqrt (∫ x in s, ‖g x‖ ^ 2 ∂μ) := by
  have hfg : Integrable (fun x ↦ ‖f x‖ * ‖g x‖) (μ.restrict s) := by
    simpa only [Pi.mul_apply, norm_mul] using (hf.integrable_mul hg).norm
  calc
    ‖∫ x in s, f x * g x ∂μ‖ ≤ ∫ x in s, ‖f x‖ * ‖g x‖ ∂μ := by
      exact norm_integral_le_of_norm_le hfg
        (Filter.Eventually.of_forall fun x ↦ by rw [norm_mul])
    _ ≤ (∫ x in s, ‖f x‖ ^ 2 ∂μ) ^ (1 / (2 : ℝ)) *
        (∫ x in s, ‖g x‖ ^ 2 ∂μ) ^ (1 / (2 : ℝ)) := by
      simpa only [ENNReal.ofReal_ofNat, Real.rpow_two] using
        integral_mul_norm_le_Lp_mul_Lq (Real.HolderConjugate.two_two)
          (show MemLp f (ENNReal.ofReal 2) (μ.restrict s) by
            simpa only [ENNReal.ofReal_ofNat] using hf)
          (show MemLp g (ENNReal.ofReal 2) (μ.restrict s) by
            simpa only [ENNReal.ofReal_ofNat] using hg)
    _ = Real.sqrt (∫ x in s, ‖f x‖ ^ 2 ∂μ) *
        Real.sqrt (∫ x in s, ‖g x‖ ^ 2 ∂μ) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

end NBMellinTools
