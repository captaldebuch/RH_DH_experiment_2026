/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB15CertifiedMellinTransform
import NBMellinTools.MellinPlancherelPositiveHalfLine

/-!
# Mellin--Plancherel for the certified NB8 residual

This module proves that the active NB8 physical energy is exactly the
critical-line energy of its certified Dirichlet polynomial.  The theorem is
unconditional and finite-stage.  It proves no asymptotic decay and makes no
identification with the transformed Estermann object on `Re s = 3/2`.
-/

open MeasureTheory Set Complex
open scoped BigOperators

namespace NBMellinTools.NB15

open NBMellinTools.NB2
open NBMellinTools.NB8

private theorem measurable_bdApprox
    (N : ℕ) (coeffs : Fin N → ℝ) :
    Measurable (bdApprox N coeffs) := by
  unfold bdApprox
  exact Finset.measurable_sum _ (fun k _ =>
    measurable_const.mul (NBMellinTools.NB9.measurable_rhoBD k.val))

theorem measurable_certifiedResidual (n : ℕ) :
    Measurable (certifiedResidual n) := by
  unfold certifiedResidual
  exact (NBMellinTools.NB9.measurable_chi01.sub
    (measurable_bdApprox (logTaperLength n) (logTaperCoeffs n))).complex_ofReal

private theorem chi01_memLp_two :
    MemLp chi01 2 (volume.restrict (Ioi (0 : ℝ))) := by
  apply (memLp_two_iff_integrable_sq_norm
    NBMellinTools.NB9.measurable_chi01.aestronglyMeasurable).2
  simpa only [Real.norm_eq_abs, sq_abs] using
    NBMellinTools.NB9.chi01_sq_integrableOn_Ioi_zero

private theorem rhoBD_memLp_two (k : ℕ) :
    MemLp (rhoBD k) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  apply (memLp_two_iff_integrable_sq_norm
    (NBMellinTools.NB9.measurable_rhoBD k).aestronglyMeasurable).2
  refine (NBMellinTools.NB9.rhoBD_mul_rhoBD_integrableOn_Ioi_zero k k).congr_fun
    ?_ measurableSet_Ioi
  intro x hx
  change rhoBD k x * rhoBD k x = ‖rhoBD k x‖ ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _), pow_two]

private theorem bdApprox_memLp_two
    (N : ℕ) (coeffs : Fin N → ℝ) :
    MemLp (bdApprox N coeffs) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  unfold bdApprox
  apply MeasureTheory.memLp_finsetSum (Finset.univ : Finset (Fin N))
  intro i hi
  simpa only [Pi.smul_apply, smul_eq_mul] using
    (rhoBD_memLp_two i.val).const_smul (coeffs i)

/-- The actual complex certified residual lies in `L²(0,∞)`. -/
theorem certifiedResidual_memLp_two (n : ℕ) :
    MemLp (certifiedResidual n) 2
      (volume.restrict (Ioi (0 : ℝ))) := by
  have hreal : MemLp
      (fun x : ℝ => chi01 x -
        bdApprox (logTaperLength n) (logTaperCoeffs n) x)
      2 (volume.restrict (Ioi (0 : ℝ))) :=
    chi01_memLp_two.sub
      (bdApprox_memLp_two (logTaperLength n) (logTaperCoeffs n))
  simpa only [certifiedResidual] using hreal.ofReal

/-- Coefficient of the exact reciprocal tail of the finite residual. -/
noncomputable def certifiedTailCoefficient (n : ℕ) : ℝ :=
  ∑ k : Fin (logTaperLength n),
    logTaperCoeffs n k / (k.val + 1 : ℝ)

theorem certifiedResidual_eq_tail_of_one_lt
    (n : ℕ) {x : ℝ} (hx : 1 < x) :
    certifiedResidual n x =
      ((-certifiedTailCoefficient n / x : ℝ) : ℂ) := by
  unfold certifiedResidual certifiedTailCoefficient
  rw [chi_sub_bdApprox_eq_tail_of_one_lt
    (logTaperLength n) (logTaperCoeffs n) hx]

private theorem norm_bdApprox_le
    (N : ℕ) (coeffs : Fin N → ℝ) (x : ℝ) :
    ‖bdApprox N coeffs x‖ ≤ ∑ k : Fin N, ‖coeffs k‖ := by
  unfold bdApprox
  calc
    ‖∑ k, coeffs k * rhoBD k.val x‖ ≤
        ∑ k, ‖coeffs k * rhoBD k.val x‖ := norm_sum_le _ _
    _ = ∑ k, ‖coeffs k‖ * ‖rhoBD k.val x‖ := by
      simp only [norm_mul]
    _ ≤ ∑ k, ‖coeffs k‖ := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_of_le_one_right (norm_nonneg _)
        (NBMellinTools.NB9.norm_rhoBD_le_one k.val x)

private theorem norm_certifiedResidual_le (n : ℕ) (x : ℝ) :
    ‖certifiedResidual n x‖ ≤
      1 + ∑ k : Fin (logTaperLength n), ‖logTaperCoeffs n k‖ := by
  unfold certifiedResidual
  rw [Complex.norm_real, Real.norm_eq_abs]
  calc
    |chi01 x - bdApprox (logTaperLength n) (logTaperCoeffs n) x| ≤
        |chi01 x| +
          |bdApprox (logTaperLength n) (logTaperCoeffs n) x| :=
      abs_sub _ _
    _ = ‖chi01 x‖ +
        ‖bdApprox (logTaperLength n) (logTaperCoeffs n) x‖ := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ 1 + ∑ k : Fin (logTaperLength n), ‖logTaperCoeffs n k‖ := by
      gcongr
      · exact NBMellinTools.NB9.norm_chi01_le_one x
      · exact norm_bdApprox_le
          (logTaperLength n) (logTaperCoeffs n) x

/-- Logarithmic pullback of the literal certified residual. -/
noncomputable def certifiedLogPullback (n : ℕ) (u : ℝ) : ℂ :=
  mellinLogPullback (certifiedResidual n) u

private theorem measurable_certifiedLogPullback (n : ℕ) :
    Measurable (certifiedLogPullback n) := by
  unfold certifiedLogPullback mellinLogPullback
  apply Measurable.smul
  · exact (Real.continuous_exp.comp
      (continuous_neg.div_const 2)).measurable
  · exact (measurable_certifiedResidual n).comp
      (Real.continuous_exp.comp continuous_neg).measurable

private theorem certifiedLogPullback_integrableOn_Iio (n : ℕ) :
    IntegrableOn (certifiedLogPullback n) (Iio (0 : ℝ)) := by
  have hbase : IntegrableOn (fun u : ℝ => Real.exp ((1 / 2 : ℝ) * u))
      (Iic (0 : ℝ)) :=
    integrableOn_exp_mul_Iic (by norm_num) 0
  have hbase' : IntegrableOn (fun u : ℝ => Real.exp ((1 / 2 : ℝ) * u))
      (Iio (0 : ℝ)) :=
    (integrableOn_Iic_iff_integrableOn_Iio).mp hbase
  have hmodel : IntegrableOn
      (fun u : ℝ => |certifiedTailCoefficient n| *
        Real.exp ((1 / 2 : ℝ) * u))
      (Iio (0 : ℝ)) :=
    hbase'.const_mul _
  apply Integrable.mono' hmodel
    (measurable_certifiedLogPullback n).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Iio] with u hu
  have hx : 1 < Real.exp (-u) := by
    simpa only [Real.exp_zero] using
      Real.exp_lt_exp.mpr (neg_pos.mpr hu)
  unfold certifiedLogPullback mellinLogPullback
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    certifiedResidual_eq_tail_of_one_lt n hx,
    Complex.norm_real, Real.norm_eq_abs, abs_div, abs_neg,
    abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-u / 2) *
          (|certifiedTailCoefficient n| / Real.exp (-u)) =
        |certifiedTailCoefficient n| *
          (Real.exp (-u / 2) / Real.exp (-u)) := by ring
    _ = |certifiedTailCoefficient n| *
          Real.exp ((1 / 2 : ℝ) * u) := by
      rw [← Real.exp_sub]
      congr 2
      ring
    _ ≤ |certifiedTailCoefficient n| *
          Real.exp ((1 / 2 : ℝ) * u) := le_rfl

private theorem certifiedLogPullback_integrableOn_Ici (n : ℕ) :
    IntegrableOn (certifiedLogPullback n) (Ici (0 : ℝ)) := by
  have hbase : IntegrableOn (fun u : ℝ => Real.exp ((-1 / 2 : ℝ) * u))
      (Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_Ioi (by norm_num) 0
  have hbase' : IntegrableOn (fun u : ℝ => Real.exp ((-1 / 2 : ℝ) * u))
      (Ici (0 : ℝ)) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr hbase
  have hmodel : IntegrableOn
      (fun u : ℝ =>
        (1 + ∑ k : Fin (logTaperLength n), ‖logTaperCoeffs n k‖) *
          Real.exp ((-1 / 2 : ℝ) * u))
      (Ici (0 : ℝ)) :=
    hbase'.const_mul _
  apply Integrable.mono' hmodel
    (measurable_certifiedLogPullback n).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
  unfold certifiedLogPullback mellinLogPullback
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-u / 2) * ‖certifiedResidual n (Real.exp (-u))‖ ≤
        Real.exp (-u / 2) *
          (1 + ∑ k : Fin (logTaperLength n), ‖logTaperCoeffs n k‖) :=
      mul_le_mul_of_nonneg_left
        (norm_certifiedResidual_le n _) (Real.exp_pos _).le
    _ = (1 + ∑ k : Fin (logTaperLength n), ‖logTaperCoeffs n k‖) *
          Real.exp ((-1 / 2 : ℝ) * u) := by
      have hexp : Real.exp (-u / 2) =
          Real.exp ((-1 / 2 : ℝ) * u) := by
        congr 1
        ring
      rw [hexp]
      ring

/-- The logarithmic pullback of every finite certified residual belongs to
`L¹(ℝ)`, selecting its pointwise Fourier representative. -/
theorem certifiedLogPullback_integrable (n : ℕ) :
    Integrable (certifiedLogPullback n) := by
  simpa only [Iio_union_Ici, IntegrableOn, Measure.restrict_univ] using
    (certifiedLogPullback_integrableOn_Iio n).union
      (certifiedLogPullback_integrableOn_Ici n)

theorem certifiedCriticalLinePoint_eq_mellinCriticalLinePoint (t : ℝ) :
    certifiedCriticalLinePoint t = mellinCriticalLinePoint t := rfl

/-- The exact critical-line energy of the active NB8 Dirichlet polynomial. -/
noncomputable def certifiedCriticalLineEnergy (n : ℕ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ t : ℝ,
    ‖certifiedCriticalLineNumerator n t‖ ^ 2

/-- Unconditional finite-stage Mellin--Plancherel bridge for NB8. -/
theorem logTaperL2Error_eq_certifiedCriticalLineEnergy (n : ℕ) :
    logTaperL2Error n = certifiedCriticalLineEnergy n := by
  calc
    logTaperL2Error n =
        ∫ x in Ioi (0 : ℝ), ‖certifiedResidual n x‖ ^ 2 :=
      logTaperL2Error_eq_certifiedResidual_normSq n
    _ = (1 / (2 * Real.pi)) * ∫ t : ℝ,
        ‖mellin (certifiedResidual n) (mellinCriticalLinePoint t)‖ ^ 2 := by
      apply mellin_plancherel_positive_half_line_of_measurable
      · exact measurable_certifiedResidual n
      · exact certifiedResidual_memLp_two n
      · simpa only [certifiedLogPullback] using
          certifiedLogPullback_integrable n
    _ = certifiedCriticalLineEnergy n := by
      unfold certifiedCriticalLineEnergy
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards with t
      rw [← certifiedCriticalLinePoint_eq_mellinCriticalLinePoint,
        mellin_certifiedResidual_criticalLine]

end NBMellinTools.NB15
