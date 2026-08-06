/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import Mathlib
import NBMellinTools.MellinEvaluation
import NBMellinTools.BaezDuarteTail

/-!
# NB Field 1: Mellin evaluation continuity

This file proves the continuity estimate for the Mellin functional on finite
Báez--Duarte approximants. On `(0,1]` it is Cauchy--Schwarz against the Mellin
kernel; on `(1,∞)` it uses the exact reciprocal tail proved in
`BaezDuarteTail`.
-/

namespace NBMellinTools.NB3

noncomputable section

open scoped BigOperators
open MeasureTheory Set Complex
open NBMellinTools
open NBMellinTools.NB2

private def mellinError (N : ℕ) (coeffs : Fin N → ℝ) (x : ℝ) : ℂ :=
  ((chi01 x - bdApprox N coeffs x : ℝ) : ℂ)

private def realError (N : ℕ) (coeffs : Fin N → ℝ) (x : ℝ) : ℝ :=
  chi01 x - bdApprox N coeffs x

private def tailCoeff (N : ℕ) (coeffs : Fin N → ℝ) : ℝ :=
  ∑ k : Fin N, coeffs k / (k.val + 1 : ℝ)

private theorem measurable_chi01 : Measurable chi01 := by
  unfold chi01
  exact Measurable.ite measurableSet_Ioc measurable_const measurable_const

private theorem measurable_rhoBD (k : ℕ) : Measurable (rhoBD k) := by
  unfold rhoBD
  measurability

private theorem measurable_bdApprox (N : ℕ) (coeffs : Fin N → ℝ) :
    Measurable (bdApprox N coeffs) := by
  unfold bdApprox
  exact Finset.measurable_sum _
    (fun k _ ↦ measurable_const.mul (measurable_rhoBD k.val))

private theorem measurable_mellinError (N : ℕ) (coeffs : Fin N → ℝ) :
    Measurable (mellinError N coeffs) := by
  unfold mellinError
  exact (measurable_chi01.sub
    (measurable_bdApprox N coeffs)).complex_ofReal

private theorem norm_chi01_le_one (x : ℝ) : ‖chi01 x‖ ≤ 1 := by
  unfold chi01
  by_cases hx : 0 < x ∧ x ≤ 1 <;> simp [hx]

private theorem norm_rhoBD_le_one (k : ℕ) (x : ℝ) : ‖rhoBD k x‖ ≤ 1 := by
  unfold rhoBD
  rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
  exact (Int.fract_lt_one _).le

private theorem norm_bdApprox_le (N : ℕ) (coeffs : Fin N → ℝ) (x : ℝ) :
    ‖bdApprox N coeffs x‖ ≤ ∑ k : Fin N, ‖coeffs k‖ := by
  unfold bdApprox
  calc
    ‖∑ k, coeffs k * rhoBD k.val x‖ ≤
        ∑ k, ‖coeffs k * rhoBD k.val x‖ := norm_sum_le _ _
    _ = ∑ k, ‖coeffs k‖ * ‖rhoBD k.val x‖ := by
      simp only [norm_mul]
    _ ≤ ∑ k, ‖coeffs k‖ := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_of_le_one_right (norm_nonneg _)
        (norm_rhoBD_le_one k.val x)

private theorem norm_mellinError_le
    (N : ℕ) (coeffs : Fin N → ℝ) (x : ℝ) :
    ‖mellinError N coeffs x‖ ≤ 1 + ∑ k : Fin N, ‖coeffs k‖ := by
  unfold mellinError
  rw [Complex.norm_real, Real.norm_eq_abs]
  calc
    |chi01 x - bdApprox N coeffs x| ≤
        |chi01 x| + |bdApprox N coeffs x| := abs_sub _ _
    _ = ‖chi01 x‖ + ‖bdApprox N coeffs x‖ := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ 1 + ∑ k : Fin N, ‖coeffs k‖ := by
      gcongr
      · exact norm_chi01_le_one x
      · exact norm_bdApprox_le N coeffs x

private def mellinKernel (s : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (s - 1)

private theorem mellinKernel_integrableOn_Ioc01
    {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (mellinKernel s) (Ioc (0 : ℝ) 1) := by
  have h := intervalIntegral.intervalIntegrable_cpow'
    (r := s - 1) (a := (0 : ℝ)) (b := 1) (by
      rw [Complex.sub_re, Complex.one_re]
      linarith)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h
  exact h

private theorem mellinKernel_norm_sq_integral
    {s : ℂ} (hs : 1 / 2 < s.re) :
    (∫ x in Ioc (0 : ℝ) 1, ‖mellinKernel s x‖ ^ 2) =
      1 / (2 * s.re - 1) := by
  have hexp : -1 < 2 * s.re - 2 := by linarith
  have hpow := integral_rpow (a := (0 : ℝ)) (b := 1)
    (r := 2 * s.re - 2) (Or.inl hexp)
  have heq :
      (∫ x in Ioc (0 : ℝ) 1, ‖mellinKernel s x‖ ^ 2) =
        ∫ x in Ioc (0 : ℝ) 1, x ^ (2 * s.re - 2) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hxpos : 0 < x := hx.1
    simp only [mellinKernel, Complex.norm_cpow_eq_rpow_re_of_pos hxpos,
      Complex.sub_re, Complex.one_re]
    rw [show 2 * s.re - 2 = (s.re - 1) * 2 by ring,
      Real.rpow_mul hxpos.le]
    norm_num [Real.rpow_natCast]
  calc
    (∫ x in Ioc (0 : ℝ) 1, ‖mellinKernel s x‖ ^ 2) =
        ∫ x in Ioc (0 : ℝ) 1, x ^ (2 * s.re - 2) := heq
    _ = (1 ^ (2 * s.re - 2 + 1) - 0 ^ (2 * s.re - 2 + 1)) /
          (2 * s.re - 2 + 1) := by
      rw [← intervalIntegral.integral_of_le zero_le_one]
      exact hpow
    _ = 1 / (2 * s.re - 1) := by
      norm_num
      have hz : (0 : ℝ) ^ (2 * s.re - 2 + 1) = 0 :=
        Real.zero_rpow (by intro h; linarith)
      rw [hz]
      ring

private theorem mellinKernel_memLp_Ioc01
    {s : ℂ} (hs : 1 / 2 < s.re) :
    MemLp (mellinKernel s) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  apply (memLp_two_iff_integrable_sq_norm
    (mellinKernel_integrableOn_Ioc01
      (by linarith)).aestronglyMeasurable).2
  have hpow : IntegrableOn (fun x : ℝ ↦ x ^ (2 * s.re - 2))
      (Ioc (0 : ℝ) 1) := by
    have h := intervalIntegral.intervalIntegrable_rpow'
      (a := (0 : ℝ)) (b := 1) (r := 2 * s.re - 2)
      (by linarith : -1 < 2 * s.re - 2)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h
    exact h
  have heq : EqOn (fun x : ℝ ↦ ‖mellinKernel s x‖ ^ 2)
      (fun x : ℝ ↦ x ^ (2 * s.re - 2)) (Ioc (0 : ℝ) 1) := by
    intro x hx
    have hxpos : 0 < x := hx.1
    simp only [mellinKernel, Complex.norm_cpow_eq_rpow_re_of_pos hxpos,
      Complex.sub_re, Complex.one_re]
    rw [show 2 * s.re - 2 = (s.re - 1) * 2 by ring,
      Real.rpow_mul hxpos.le]
    norm_num [Real.rpow_natCast]
  have hnorm : IntegrableOn (fun x : ℝ ↦ ‖mellinKernel s x‖ ^ 2)
      (Ioc (0 : ℝ) 1) := hpow.congr_fun heq.symm measurableSet_Ioc
  simpa only [IntegrableOn] using hnorm

private theorem mellinError_memLp_Ioc01
    (N : ℕ) (coeffs : Fin N → ℝ) :
    MemLp (mellinError N coeffs) 2
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
  apply (memLp_two_iff_integrable_sq_norm
    (measurable_mellinError N coeffs).aestronglyMeasurable).2
  have hM : 0 ≤ 1 + ∑ k : Fin N, ‖coeffs k‖ := by positivity
  have hsq : IntegrableOn
      (fun x : ℝ ↦ ‖mellinError N coeffs x‖ ^ 2)
      (Ioc (0 : ℝ) 1) := by
    apply Measure.integrableOn_of_bounded
      (μ := volume) (s := Ioc (0 : ℝ) 1)
      (M := (1 + ∑ k : Fin N, ‖coeffs k‖) ^ 2)
      measure_Ioc_lt_top.ne
      ((measurable_mellinError N coeffs).norm.pow_const 2).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hnonneg : 0 ≤ ‖mellinError N coeffs x‖ ^ 2 := sq_nonneg _
    calc
      ‖‖mellinError N coeffs x‖ ^ 2‖ =
          ‖mellinError N coeffs x‖ ^ 2 := Real.norm_of_nonneg hnonneg
      _ ≤ (1 + ∑ k : Fin N, ‖coeffs k‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) hM).2
          (norm_mellinError_le N coeffs x)
  exact hsq

private theorem realError_measurable
    (N : ℕ) (coeffs : Fin N → ℝ) : Measurable (realError N coeffs) := by
  exact measurable_chi01.sub (measurable_bdApprox N coeffs)

private theorem realError_sq_integrableOn_Ioc01
    (N : ℕ) (coeffs : Fin N → ℝ) :
    IntegrableOn (fun x ↦ realError N coeffs x ^ 2)
      (Ioc (0 : ℝ) 1) := by
  refine Measure.integrableOn_of_bounded
    (μ := volume) (s := Ioc (0 : ℝ) 1)
    (M := (1 + ∑ k : Fin N, ‖coeffs k‖) ^ 2)
    measure_Ioc_lt_top.ne
    (((realError_measurable N coeffs).pow_const 2).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have h := norm_mellinError_le N coeffs x
  change ‖((realError N coeffs x : ℝ) : ℂ)‖ ≤ _ at h
  rw [Complex.norm_real, Real.norm_eq_abs] at h
  calc
    ‖realError N coeffs x ^ 2‖ = |realError N coeffs x| ^ 2 := by
      rw [Real.norm_eq_abs, abs_pow]
    _ ≤ (1 + ∑ k : Fin N, ‖coeffs k‖) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 h

private theorem realError_eq_tail_on_Ioi
    (N : ℕ) (coeffs : Fin N → ℝ) :
    EqOn (realError N coeffs)
      (fun x ↦ -tailCoeff N coeffs / x) (Ioi (1 : ℝ)) := by
  intro x hx
  exact chi_sub_bdApprox_eq_tail_of_one_lt N coeffs hx

private theorem realError_sq_integrableOn_Ioi
    (N : ℕ) (coeffs : Fin N → ℝ) :
    IntegrableOn (fun x ↦ realError N coeffs x ^ 2)
      (Ioi (1 : ℝ)) := by
  have hpow : IntegrableOn (fun x : ℝ ↦ x ^ (-2 : ℝ))
      (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
  have hconst : AEStronglyMeasurable
      (fun _ : ℝ ↦ tailCoeff N coeffs ^ 2)
      (volume.restrict (Ioi (1 : ℝ))) :=
    measurable_const.aestronglyMeasurable
  have hbound : ∀ᵐ x ∂(volume.restrict (Ioi (1 : ℝ))),
      ‖tailCoeff N coeffs ^ 2‖ ≤ |tailCoeff N coeffs ^ 2| := by
    filter_upwards with x
    rw [Real.norm_eq_abs]
  have hmodel : IntegrableOn
      (fun x : ℝ ↦ tailCoeff N coeffs ^ 2 * x ^ (-2 : ℝ))
      (Ioi (1 : ℝ)) := by
    have h := hpow.mul_bdd hconst hbound
    simpa only [mul_comm] using h
  apply hmodel.congr_fun _ measurableSet_Ioi
  intro x hx
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  change tailCoeff N coeffs ^ 2 * x ^ (-2 : ℝ) =
    (realError N coeffs x) ^ 2
  rw [realError_eq_tail_on_Ioi N coeffs hx]
  rw [Real.rpow_neg hx0.le]
  norm_num [Real.rpow_natCast]
  field_simp

private theorem realError_sq_integrableOn_Ioi_zero
    (N : ℕ) (coeffs : Fin N → ℝ) :
    IntegrableOn (fun x ↦ realError N coeffs x ^ 2)
      (Ioi (0 : ℝ)) := by
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  exact (realError_sq_integrableOn_Ioc01 N coeffs).union
    (realError_sq_integrableOn_Ioi N coeffs)

private theorem realError_sq_integral_Ioc_le_error
    (N : ℕ) (coeffs : Fin N → ℝ) :
    (∫ x in Ioc (0 : ℝ) 1, realError N coeffs x ^ 2) ≤
      BaezDuarteL2Error N coeffs := by
  change (∫ x in Ioc (0 : ℝ) 1, realError N coeffs x ^ 2) ≤
    ∫ x in Ioi (0 : ℝ), realError N coeffs x ^ 2
  apply setIntegral_mono_set
    (realError_sq_integrableOn_Ioi_zero N coeffs)
    (Filter.Eventually.of_forall (fun x ↦ sq_nonneg _))
  exact Filter.Eventually.of_forall (fun x hx ↦ Ioc_subset_Ioi_self hx)

private theorem tailCoeff_sq_le_error
    (N : ℕ) (coeffs : Fin N → ℝ) :
    tailCoeff N coeffs ^ 2 ≤ BaezDuarteL2Error N coeffs := by
  have hpow : IntegrableOn (fun x : ℝ ↦ x ^ (-2 : ℝ))
      (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
  have htail :
      (∫ x in Ioi (1 : ℝ),
        tailCoeff N coeffs ^ 2 * x ^ (-2 : ℝ)) =
        tailCoeff N coeffs ^ 2 := by
    rw [integral_const_mul]
    rw [integral_Ioi_rpow_of_lt (by norm_num) one_pos]
    norm_num
  have hsubset :
      (∫ x in Ioi (1 : ℝ), realError N coeffs x ^ 2) ≤
        BaezDuarteL2Error N coeffs := by
    change (∫ x in Ioi (1 : ℝ), realError N coeffs x ^ 2) ≤
      ∫ x in Ioi (0 : ℝ), realError N coeffs x ^ 2
    apply setIntegral_mono_set
      (realError_sq_integrableOn_Ioi_zero N coeffs)
      (Filter.Eventually.of_forall (fun x ↦ sq_nonneg _))
    exact Filter.Eventually.of_forall
      (fun x hx ↦ lt_trans zero_lt_one hx)
  rw [← htail]
  calc
    (∫ x in Ioi (1 : ℝ),
        tailCoeff N coeffs ^ 2 * x ^ (-2 : ℝ)) =
        ∫ x in Ioi (1 : ℝ), realError N coeffs x ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hx0 : 0 < x := lt_trans zero_lt_one hx
      change tailCoeff N coeffs ^ 2 * x ^ (-2 : ℝ) =
        realError N coeffs x ^ 2
      rw [realError_eq_tail_on_Ioi N coeffs hx]
      rw [Real.rpow_neg hx0.le]
      norm_num [Real.rpow_natCast]
      field_simp
    _ ≤ BaezDuarteL2Error N coeffs := hsubset

private theorem mellin_integrand_integrableOn_Ioc01
    {s : ℂ} (hs : 0 < s.re)
    (N : ℕ) (coeffs : Fin N → ℝ) :
    IntegrableOn (fun x ↦ mellinKernel s x * mellinError N coeffs x)
      (Ioc (0 : ℝ) 1) := by
  have hk := mellinKernel_integrableOn_Ioc01 hs
  have he : AEStronglyMeasurable (mellinError N coeffs)
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (measurable_mellinError N coeffs).aestronglyMeasurable.restrict
  have hbound : ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      ‖mellinError N coeffs x‖ ≤ 1 + ∑ k : Fin N, ‖coeffs k‖ :=
    Filter.Eventually.of_forall (fun x ↦ norm_mellinError_le N coeffs x)
  exact hk.mul_bdd he hbound

private theorem mellinError_local_sq_eq_realError
    (N : ℕ) (coeffs : Fin N → ℝ) :
    (∫ x in Ioc (0 : ℝ) 1, ‖mellinError N coeffs x‖ ^ 2) =
      ∫ x in Ioc (0 : ℝ) 1, realError N coeffs x ^ 2 := by
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x _
  change ‖((realError N coeffs x : ℝ) : ℂ)‖ ^ 2 =
    realError N coeffs x ^ 2
  simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem mellin_error_part_A_bound
    {s : ℂ} (hs : 1 / 2 < s.re)
    (N : ℕ) (coeffs : Fin N → ℝ) :
    ‖∫ x in Ioc (0 : ℝ) 1,
        mellinKernel s x * mellinError N coeffs x‖ ≤
      (1 / Real.sqrt (2 * s.re - 1)) *
        Real.sqrt (BaezDuarteL2Error N coeffs) := by
  have hcs := norm_setIntegral_mul_le_sqrt_mul_sqrt
    (mellinError N coeffs) (mellinKernel s)
    (Ioc (0 : ℝ) 1) volume
    (mellinError_memLp_Ioc01 N coeffs) (mellinKernel_memLp_Ioc01 hs)
  have hlocal :
      (∫ x in Ioc (0 : ℝ) 1, ‖mellinError N coeffs x‖ ^ 2) ≤
        BaezDuarteL2Error N coeffs := by
    rw [mellinError_local_sq_eq_realError N coeffs]
    exact realError_sq_integral_Ioc_le_error N coeffs
  have hroot : Real.sqrt
      (∫ x in Ioc (0 : ℝ) 1, ‖mellinError N coeffs x‖ ^ 2) ≤
      Real.sqrt (BaezDuarteL2Error N coeffs) := Real.sqrt_le_sqrt hlocal
  have hrootk : 0 ≤ Real.sqrt
      (∫ x in Ioc (0 : ℝ) 1, ‖mellinKernel s x‖ ^ 2) :=
    Real.sqrt_nonneg _
  calc
    ‖∫ x in Ioc (0 : ℝ) 1,
        mellinKernel s x * mellinError N coeffs x‖ =
        ‖∫ x in Ioc (0 : ℝ) 1,
          mellinError N coeffs x * mellinKernel s x‖ := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x _
      ring
    _ ≤ Real.sqrt
          (∫ x in Ioc (0 : ℝ) 1, ‖mellinError N coeffs x‖ ^ 2) *
          Real.sqrt
            (∫ x in Ioc (0 : ℝ) 1, ‖mellinKernel s x‖ ^ 2) := hcs
    _ ≤ Real.sqrt (BaezDuarteL2Error N coeffs) *
          Real.sqrt
            (∫ x in Ioc (0 : ℝ) 1, ‖mellinKernel s x‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hroot hrootk
    _ = (1 / Real.sqrt (2 * s.re - 1)) *
          Real.sqrt (BaezDuarteL2Error N coeffs) := by
      rw [mellinKernel_norm_sq_integral hs]
      have hspos : 0 < 2 * s.re - 1 := by linarith
      rw [show Real.sqrt (1 / (2 * s.re - 1)) =
        1 / Real.sqrt (2 * s.re - 1) by
          rw [Real.sqrt_div (by norm_num), Real.sqrt_one]]
      ring

private theorem mellinError_tail_model_eq
    {s : ℂ} (N : ℕ) (coeffs : Fin N → ℝ)
    {x : ℝ} (hx : 1 < x) :
    mellinKernel s x * mellinError N coeffs x =
      (-(tailCoeff N coeffs) : ℂ) * (x : ℂ) ^ (s - 2) := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hcx : (x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hx0
  change (x : ℂ) ^ (s - 1) * ((realError N coeffs x : ℝ) : ℂ) = _
  rw [realError_eq_tail_on_Ioi N coeffs hx]
  simp only [Complex.ofReal_div, Complex.ofReal_neg]
  calc
    (x : ℂ) ^ (s - 1) * ((-(tailCoeff N coeffs) : ℂ) / (x : ℂ)) =
        (-(tailCoeff N coeffs) : ℂ) *
          ((x : ℂ) ^ (s - 1) / (x : ℂ)) := by ring
    _ = (-(tailCoeff N coeffs) : ℂ) * (x : ℂ) ^ (s - 2) := by
      rw [show s - 2 = (s - 1) - 1 by ring,
        Complex.cpow_sub (s - 1) 1 hcx, Complex.cpow_one]

private theorem mellin_tail_integrableOn_Ioi
    {s : ℂ} (hs : s.re < 1)
    (N : ℕ) (coeffs : Fin N → ℝ) :
    IntegrableOn (fun x ↦ mellinKernel s x * mellinError N coeffs x)
      (Ioi (1 : ℝ)) := by
  have hcpow : IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ (s - 2))
      (Ioi (1 : ℝ)) := by
    exact integrableOn_Ioi_cpow_of_lt (c := 1)
      (by change s.re - 2 < -1; linarith) one_pos
  have hconst : AEStronglyMeasurable
      (fun _ : ℝ ↦ (-(tailCoeff N coeffs) : ℂ))
      (volume.restrict (Ioi (1 : ℝ))) :=
    measurable_const.aestronglyMeasurable
  have hmodel : IntegrableOn
      (fun x : ℝ ↦ (-(tailCoeff N coeffs) : ℂ) * (x : ℂ) ^ (s - 2))
      (Ioi (1 : ℝ)) := by
    have h := hcpow.mul_bdd
      (c := ‖(-(tailCoeff N coeffs) : ℂ)‖) hconst
      (Filter.Eventually.of_forall (fun _ ↦ le_rfl))
    simpa only [mul_comm] using h
  apply hmodel.congr_fun _ measurableSet_Ioi
  intro x hx
  exact (mellinError_tail_model_eq N coeffs hx).symm

theorem mellin_error_tail_part_B_bound
    {s : ℂ} (hs : s.re < 1)
    (N : ℕ) (coeffs : Fin N → ℝ) :
    ‖∫ x in Ioi (1 : ℝ),
        mellinKernel s x * mellinError N coeffs x‖ ≤
      (1 / (1 - s.re)) * Real.sqrt (BaezDuarteL2Error N coeffs) := by
  have hpow : IntegrableOn
      (fun x : ℝ ↦ Real.sqrt (BaezDuarteL2Error N coeffs) *
        x ^ (s.re - 2)) (Ioi (1 : ℝ)) := by
    have h := integrableOn_Ioi_rpow_of_lt
      (by linarith : s.re - 2 < -1) one_pos
    have hc : AEStronglyMeasurable
        (fun _ : ℝ ↦ Real.sqrt (BaezDuarteL2Error N coeffs))
        (volume.restrict (Ioi (1 : ℝ))) :=
      measurable_const.aestronglyMeasurable
    have hb : ∀ᵐ x ∂(volume.restrict (Ioi (1 : ℝ))),
        ‖Real.sqrt (BaezDuarteL2Error N coeffs)‖ ≤
          |Real.sqrt (BaezDuarteL2Error N coeffs)| :=
      Filter.Eventually.of_forall (fun _ ↦ by rw [Real.norm_eq_abs])
    have hm := h.mul_bdd
      (c := |Real.sqrt (BaezDuarteL2Error N coeffs)|) hc hb
    simpa only [mul_comm] using hm
  have hbound : ∀ᵐ x ∂(volume.restrict (Ioi (1 : ℝ))),
      ‖mellinKernel s x * mellinError N coeffs x‖ ≤
        Real.sqrt (BaezDuarteL2Error N coeffs) * x ^ (s.re - 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    rw [mellinError_tail_model_eq N coeffs hx, norm_mul,
      norm_neg, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hcoeff : |tailCoeff N coeffs| ≤
        Real.sqrt (BaezDuarteL2Error N coeffs) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (tailCoeff_sq_le_error N coeffs)
    exact mul_le_mul_of_nonneg_right hcoeff
      (Real.rpow_nonneg hx0.le _)
  calc
    ‖∫ x in Ioi (1 : ℝ),
        mellinKernel s x * mellinError N coeffs x‖ ≤
        ∫ x in Ioi (1 : ℝ),
          Real.sqrt (BaezDuarteL2Error N coeffs) * x ^ (s.re - 2) :=
      norm_integral_le_of_norm_le hpow hbound
    _ = (1 / (1 - s.re)) *
          Real.sqrt (BaezDuarteL2Error N coeffs) := by
      rw [integral_const_mul,
        integral_Ioi_rpow_of_lt (by linarith) one_pos]
      norm_num
      have hden : s.re - 2 + 1 ≠ 0 := by linarith
      have hden' : 1 - s.re ≠ 0 := by linarith
      field_simp [hden, hden']
      ring

private theorem mellin_integrand_integrableOn_Ioi
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (N : ℕ) (coeffs : Fin N → ℝ) :
    IntegrableOn (fun x ↦ mellinKernel s x * mellinError N coeffs x)
      (Ioi (0 : ℝ)) := by
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  exact (mellin_integrand_integrableOn_Ioc01 hs0 N coeffs).union
    (mellin_tail_integrableOn_Ioi hs1 N coeffs)

private theorem mellin_split_at_one
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (N : ℕ) (coeffs : Fin N → ℝ) :
    mellin (fun x : ℝ ↦
        ((chi01 x - bdApprox N coeffs x : ℝ) : ℂ)) s =
      (∫ x in Ioc (0 : ℝ) 1,
        mellinKernel s x * mellinError N coeffs x) +
      (∫ x in Ioi (1 : ℝ),
        mellinKernel s x * mellinError N coeffs x) := by
  unfold mellin
  simp only [smul_eq_mul]
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  change (∫ x in Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ),
      mellinKernel s x * mellinError N coeffs x) = _
  rw [setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (mellin_integrand_integrableOn_Ioc01 hs0 N coeffs)
    (mellin_tail_integrableOn_Ioi hs1 N coeffs)]

noncomputable def MellinContinuityConstant (s : ℂ) : ℝ :=
  1 / Real.sqrt (2 * s.re - 1) + 1 / (1 - s.re)

theorem mellinContinuityConstant_nonneg
    {s : ℂ} (hs0 : 1 / 2 < s.re) (hs1 : s.re < 1) :
    0 ≤ MellinContinuityConstant s := by
  unfold MellinContinuityConstant
  have ha : 0 < 2 * s.re - 1 := by linarith
  have hb : 0 < 1 - s.re := by linarith
  positivity

/-- Point evaluation of the Mellin transform is continuous with respect to
the exact full-half-line Báez--Duarte `L²` error throughout
`1/2 < Re(s) < 1`. -/
theorem mellin_evaluation_continuous_on_critical_strip
    (s₀ : ℂ) (hs0 : 1 / 2 < s₀.re) (hs1 : s₀.re < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ) (coeffs : Fin N → ℝ),
        ‖mellin (fun x : ℝ ↦
            ((chi01 x - bdApprox N coeffs x : ℝ) : ℂ)) s₀‖ ≤
          C * Real.sqrt (BaezDuarteL2Error N coeffs) := by
  refine ⟨MellinContinuityConstant s₀,
    mellinContinuityConstant_nonneg hs0 hs1, ?_⟩
  intro N coeffs
  rw [mellin_split_at_one (by linarith) hs1 N coeffs]
  calc
    ‖(∫ x in Ioc (0 : ℝ) 1,
        mellinKernel s₀ x * mellinError N coeffs x) +
        ∫ x in Ioi (1 : ℝ),
          mellinKernel s₀ x * mellinError N coeffs x‖ ≤
      ‖∫ x in Ioc (0 : ℝ) 1,
          mellinKernel s₀ x * mellinError N coeffs x‖ +
        ‖∫ x in Ioi (1 : ℝ),
          mellinKernel s₀ x * mellinError N coeffs x‖ := norm_add_le _ _
    _ ≤ (1 / Real.sqrt (2 * s₀.re - 1)) *
          Real.sqrt (BaezDuarteL2Error N coeffs) +
        (1 / (1 - s₀.re)) *
          Real.sqrt (BaezDuarteL2Error N coeffs) :=
      add_le_add (mellin_error_part_A_bound hs0 N coeffs)
        (mellin_error_tail_part_B_bound hs1 N coeffs)
    _ = MellinContinuityConstant s₀ *
          Real.sqrt (BaezDuarteL2Error N coeffs) := by
      unfold MellinContinuityConstant
      ring

end

end NBMellinTools.NB3
