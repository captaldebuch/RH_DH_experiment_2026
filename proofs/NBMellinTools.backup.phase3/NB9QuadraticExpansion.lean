/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB8LogTaperTarget

/-!
# NB9: exact quadratic and Gram expansion

This file expands the project `L²(0,∞)` error of an arbitrary finite
Báez--Duarte approximant into its constant, linear, and Gram terms.  It then
specializes the identity to the explicit Möbius log-taper coefficients of NB8.

Everything here is a finite algebraic/measure-theoretic identity.  No
cancellation estimate or limit is asserted.
-/

open MeasureTheory Set
open scoped BigOperators

namespace NBMellinTools.NB9

open NBMellinTools.NB2
open NBMellinTools.NB8

theorem measurable_chi01 : Measurable chi01 := by
  unfold chi01
  exact Measurable.ite measurableSet_Ioc measurable_const measurable_const

theorem measurable_rhoBD (k : ℕ) : Measurable (rhoBD k) := by
  unfold rhoBD
  measurability

theorem norm_chi01_le_one (x : ℝ) : ‖chi01 x‖ ≤ 1 := by
  unfold chi01
  by_cases hx : 0 < x ∧ x ≤ 1 <;> simp [hx]

theorem norm_rhoBD_le_one (k : ℕ) (x : ℝ) : ‖rhoBD k x‖ ≤ 1 := by
  unfold rhoBD
  rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
  exact (Int.fract_lt_one _).le

/-- The linear moment coupling the target indicator to one generator. -/
noncomputable def bdLinearMoment (k : ℕ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), chi01 x * rhoBD k x

/-- The Gram entry of two zero-based Báez--Duarte generators. -/
noncomputable def bdGram (j k : ℕ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), rhoBD j x * rhoBD k x

theorem chi_mul_rhoBD_integrableOn_Ioc (k : ℕ) :
    IntegrableOn (fun x : ℝ => chi01 x * rhoBD k x) (Ioc (0 : ℝ) 1) := by
  refine Measure.integrableOn_of_bounded
    (μ := volume) (s := Ioc (0 : ℝ) 1) (M := 1)
    measure_Ioc_lt_top.ne
    ((measurable_chi01.mul (measurable_rhoBD k)).aestronglyMeasurable) ?_
  filter_upwards with x
  rw [norm_mul]
  calc
    ‖chi01 x‖ * ‖rhoBD k x‖ ≤ 1 * 1 :=
      mul_le_mul (norm_chi01_le_one x) (norm_rhoBD_le_one k x)
        (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem chi_mul_rhoBD_integrableOn_Ioi_one (k : ℕ) :
    IntegrableOn (fun x : ℝ => chi01 x * rhoBD k x) (Ioi (1 : ℝ)) := by
  have hzero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioi (1 : ℝ)) := integrableOn_zero
  apply hzero.congr_fun _ measurableSet_Ioi
  intro x hx
  have hx' : 1 < x := hx
  simp [chi01, not_le_of_gt hx']

theorem chi_mul_rhoBD_integrableOn_Ioi_zero (k : ℕ) :
    IntegrableOn (fun x : ℝ => chi01 x * rhoBD k x) (Ioi (0 : ℝ)) := by
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  exact (chi_mul_rhoBD_integrableOn_Ioc k).union
    (chi_mul_rhoBD_integrableOn_Ioi_one k)

theorem rhoBD_mul_rhoBD_integrableOn_Ioc (j k : ℕ) :
    IntegrableOn (fun x : ℝ => rhoBD j x * rhoBD k x) (Ioc (0 : ℝ) 1) := by
  refine Measure.integrableOn_of_bounded
    (μ := volume) (s := Ioc (0 : ℝ) 1) (M := 1)
    measure_Ioc_lt_top.ne
    (((measurable_rhoBD j).mul (measurable_rhoBD k)).aestronglyMeasurable) ?_
  filter_upwards with x
  rw [norm_mul]
  calc
    ‖rhoBD j x‖ * ‖rhoBD k x‖ ≤ 1 * 1 :=
      mul_le_mul (norm_rhoBD_le_one j x) (norm_rhoBD_le_one k x)
        (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem rhoBD_mul_rhoBD_integrableOn_Ioi_one (j k : ℕ) :
    IntegrableOn (fun x : ℝ => rhoBD j x * rhoBD k x) (Ioi (1 : ℝ)) := by
  have hpow : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
  apply Integrable.mono' hpow
  · exact ((measurable_rhoBD j).mul (measurable_rhoBD k)).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := by positivity
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith
    have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith
    rw [rhoBD_eq_one_div_of_one_lt j hx, rhoBD_eq_one_div_of_one_lt k hx,
      norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 1 / ((j + 1 : ℝ) * x)),
      abs_of_pos (by positivity : 0 < 1 / ((k + 1 : ℝ) * x))]
    calc
      1 / ((j + 1 : ℝ) * x) * (1 / ((k + 1 : ℝ) * x))
          ≤ (1 / x) * (1 / x) := by
            gcongr
            · simpa using mul_le_mul_of_nonneg_right hj hx0.le
            · simpa using mul_le_mul_of_nonneg_right hk hx0.le
      _ = x ^ (-2 : ℝ) := by
        rw [Real.rpow_neg hx0.le]
        norm_num [Real.rpow_natCast]
        field_simp

theorem rhoBD_mul_rhoBD_integrableOn_Ioi_zero (j k : ℕ) :
    IntegrableOn (fun x : ℝ => rhoBD j x * rhoBD k x) (Ioi (0 : ℝ)) := by
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  exact (rhoBD_mul_rhoBD_integrableOn_Ioc j k).union
    (rhoBD_mul_rhoBD_integrableOn_Ioi_one j k)

/-- The indicator has unit squared norm on the positive half-line. -/
theorem chi01_sq_integral :
    (∫ x in Ioi (0 : ℝ), chi01 x ^ 2) = 1 := by
  have hfun : (fun x : ℝ => chi01 x ^ 2) =
      (Ioc (0 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) := by
    funext x
    by_cases hx : 0 < x ∧ x ≤ 1 <;> simp [chi01, hx, Set.mem_Ioc]
  rw [hfun, MeasureTheory.setIntegral_indicator measurableSet_Ioc]
  rw [show Ioi (0 : ℝ) ∩ Ioc (0 : ℝ) 1 = Ioc (0 : ℝ) 1 by ext x; simp]
  simp

theorem chi01_sq_integrableOn_Ioi_zero :
    IntegrableOn (fun x : ℝ => chi01 x ^ 2) (Ioi (0 : ℝ)) := by
  have hlocal : IntegrableOn (fun x : ℝ => chi01 x ^ 2) (Ioc (0 : ℝ) 1) := by
    refine Measure.integrableOn_of_bounded
      (μ := volume) (s := Ioc (0 : ℝ) 1) (M := 1)
      measure_Ioc_lt_top.ne
      ((measurable_chi01.pow_const 2).aestronglyMeasurable) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (by simpa [Real.norm_eq_abs] using norm_chi01_le_one x)
  have htail : IntegrableOn (fun x : ℝ => chi01 x ^ 2) (Ioi (1 : ℝ)) := by
    have hzero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioi (1 : ℝ)) := integrableOn_zero
    apply hzero.congr_fun _ measurableSet_Ioi
    intro x hx
    have hx' : 1 < x := hx
    simp [chi01, not_le_of_gt hx']
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  exact hlocal.union htail

/-- The exact finite quadratic form attached to a coefficient vector. -/
noncomputable def bdQuadraticForm (N : ℕ) (coeffs : Fin N → ℝ) : ℝ :=
  1 - 2 * ∑ k : Fin N, coeffs k * bdLinearMoment k.val +
    ∑ j : Fin N, ∑ k : Fin N,
      coeffs j * coeffs k * bdGram j.val k.val

/-- The constant together with the complete retained linear correction. -/
noncomputable def bdCorrectionTerm (N : ℕ) (coeffs : Fin N → ℝ) : ℝ :=
  1 - 2 * ∑ k : Fin N, coeffs k * bdLinearMoment k.val

/-- The complete signed Gram bilinear term. -/
noncomputable def bdGramTerm (N : ℕ) (coeffs : Fin N → ℝ) : ℝ :=
  ∑ j : Fin N, ∑ k : Fin N,
    coeffs j * coeffs k * bdGram j.val k.val

theorem bdQuadraticForm_eq_correction_add_gram
    (N : ℕ) (coeffs : Fin N → ℝ) :
    bdQuadraticForm N coeffs =
      bdCorrectionTerm N coeffs + bdGramTerm N coeffs := by
  rfl

theorem bdGram_comm (j k : ℕ) : bdGram j k = bdGram k j := by
  unfold bdGram
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  ring

private theorem pointwise_error_sq_expansion
    (N : ℕ) (coeffs : Fin N → ℝ) (x : ℝ) :
    (chi01 x - bdApprox N coeffs x) ^ 2 =
      chi01 x ^ 2 -
        2 * ∑ k : Fin N, coeffs k * (chi01 x * rhoBD k.val x) +
        ∑ j : Fin N, ∑ k : Fin N,
          coeffs j * coeffs k * (rhoBD j.val x * rhoBD k.val x) := by
  unfold bdApprox
  have hdouble :
      (∑ j : Fin N, ∑ k : Fin N,
          coeffs j * coeffs k * (rhoBD j.val x * rhoBD k.val x)) =
        (∑ j : Fin N, coeffs j * rhoBD j.val x) *
          (∑ k : Fin N, coeffs k * rhoBD k.val x) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hlinear :
      (∑ k : Fin N, coeffs k * (chi01 x * rhoBD k.val x)) =
        chi01 x * ∑ k : Fin N, coeffs k * rhoBD k.val x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hdouble, hlinear]
  ring

/-- Exact Gram expansion of the project `L²` error for arbitrary finite real
coefficients. -/
theorem baezDuarteL2Error_eq_quadraticForm
    (N : ℕ) (coeffs : Fin N → ℝ) :
    BaezDuarteL2Error N coeffs = bdQuadraticForm N coeffs := by
  unfold BaezDuarteL2Error bdQuadraticForm
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (fun x _ => pointwise_error_sq_expansion N coeffs x)]
  have hchi : IntegrableOn (fun x : ℝ => chi01 x ^ 2) (Ioi (0 : ℝ)) :=
    chi01_sq_integrableOn_Ioi_zero
  have hlinearSummand : ∀ k : Fin N,
      IntegrableOn
        (fun x : ℝ => coeffs k * (chi01 x * rhoBD k.val x))
        (Ioi (0 : ℝ)) := by
    intro k
    exact (chi_mul_rhoBD_integrableOn_Ioi_zero k.val).const_mul (coeffs k)
  have hlinearSum :
      IntegrableOn
        (fun x : ℝ => ∑ k : Fin N,
          coeffs k * (chi01 x * rhoBD k.val x))
        (Ioi (0 : ℝ)) :=
    integrable_finsetSum _ (fun k _ => hlinearSummand k)
  have hlinear :
      IntegrableOn
        (fun x : ℝ => 2 * ∑ k : Fin N,
          coeffs k * (chi01 x * rhoBD k.val x))
        (Ioi (0 : ℝ)) := hlinearSum.const_mul 2
  have hgramSummand : ∀ j k : Fin N,
      IntegrableOn
        (fun x : ℝ => coeffs j * coeffs k *
          (rhoBD j.val x * rhoBD k.val x))
        (Ioi (0 : ℝ)) := by
    intro j k
    exact (rhoBD_mul_rhoBD_integrableOn_Ioi_zero j.val k.val).const_mul
      (coeffs j * coeffs k)
  have hgramInner : ∀ j : Fin N,
      IntegrableOn
        (fun x : ℝ => ∑ k : Fin N,
          coeffs j * coeffs k * (rhoBD j.val x * rhoBD k.val x))
        (Ioi (0 : ℝ)) := by
    intro j
    exact integrable_finsetSum _ (fun k _ => hgramSummand j k)
  have hgram :
      IntegrableOn
        (fun x : ℝ => ∑ j : Fin N, ∑ k : Fin N,
          coeffs j * coeffs k * (rhoBD j.val x * rhoBD k.val x))
        (Ioi (0 : ℝ)) :=
    integrable_finsetSum _ (fun j _ => hgramInner j)
  have hadd :
      (∫ x in Ioi (0 : ℝ),
          (chi01 x ^ 2 -
            2 * ∑ k : Fin N, coeffs k * (chi01 x * rhoBD k.val x)) +
          ∑ j : Fin N, ∑ k : Fin N,
            coeffs j * coeffs k * (rhoBD j.val x * rhoBD k.val x)) =
        (∫ x in Ioi (0 : ℝ),
          chi01 x ^ 2 -
            2 * ∑ k : Fin N, coeffs k * (chi01 x * rhoBD k.val x)) +
        ∫ x in Ioi (0 : ℝ), ∑ j : Fin N, ∑ k : Fin N,
          coeffs j * coeffs k * (rhoBD j.val x * rhoBD k.val x) :=
    integral_add (hchi.sub hlinear) hgram
  rw [hadd]
  have hsub :
      (∫ x in Ioi (0 : ℝ),
          chi01 x ^ 2 -
            2 * ∑ k : Fin N, coeffs k * (chi01 x * rhoBD k.val x)) =
        (∫ x in Ioi (0 : ℝ), chi01 x ^ 2) -
        ∫ x in Ioi (0 : ℝ),
          2 * ∑ k : Fin N, coeffs k * (chi01 x * rhoBD k.val x) :=
    integral_sub hchi hlinear
  rw [hsub, chi01_sq_integral, integral_const_mul]
  have hlinearIntegral :
      (∫ x in Ioi (0 : ℝ), ∑ k : Fin N,
          coeffs k * (chi01 x * rhoBD k.val x)) =
        ∑ k : Fin N, coeffs k * bdLinearMoment k.val := by
    rw [integral_finsetSum Finset.univ (fun k _ => hlinearSummand k)]
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_const_mul]
    rfl
  rw [hlinearIntegral]
  have hgramIntegral :
      (∫ x in Ioi (0 : ℝ), ∑ j : Fin N, ∑ k : Fin N,
          coeffs j * coeffs k * (rhoBD j.val x * rhoBD k.val x)) =
        ∑ j : Fin N, ∑ k : Fin N,
          coeffs j * coeffs k * bdGram j.val k.val := by
    rw [integral_finsetSum Finset.univ (fun j _ => hgramInner j)]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_finsetSum Finset.univ (fun k _ => hgramSummand j k)]
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_const_mul]
    rfl
  rw [hgramIntegral]

/-- Specialization of the exact expansion to the explicit NB8 log taper. -/
theorem logTaperL2Error_eq_quadraticForm (n : ℕ) :
    logTaperL2Error n =
      bdQuadraticForm (logTaperLength n) (logTaperCoeffs n) := by
  exact baezDuarteL2Error_eq_quadraticForm _ _

/-- The correction-preserving form of the explicit log-taper identity. -/
theorem logTaperL2Error_eq_correction_add_gram (n : ℕ) :
    logTaperL2Error n =
      bdCorrectionTerm (logTaperLength n) (logTaperCoeffs n) +
      bdGramTerm (logTaperLength n) (logTaperCoeffs n) := by
  rw [logTaperL2Error_eq_quadraticForm,
    bdQuadraticForm_eq_correction_add_gram]

/-- Consequently, the NB8 target is exactly decay of the complete coupled
correction-plus-Gram expression.  No termwise decay is inferred. -/
theorem logTaperL2Decay_iff_correction_add_gram_tendsto :
    LogTaperL2Decay ↔
      Filter.Tendsto
        (fun n : ℕ =>
          bdCorrectionTerm (logTaperLength n) (logTaperCoeffs n) +
          bdGramTerm (logTaperLength n) (logTaperCoeffs n))
        Filter.atTop (nhds 0) := by
  unfold LogTaperL2Decay
  apply Filter.tendsto_congr'
  exact Filter.Eventually.of_forall logTaperL2Error_eq_correction_add_gram

end NBMellinTools.NB9
