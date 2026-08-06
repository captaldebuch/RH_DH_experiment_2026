/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FrequencySplit

/-!
# NB12z: high-frequency sum--integral exchange

This file supplies the analytic compatibility theorem promised by the exact
frequency split.  It proves continuity and global integrability of each
paired functional-equation frequency, then exchanges the shifted Estermann
`tsum` with integration on a finite vertical interval.

All bounds here are rowwise absolute-convergence statements on
`Re(s)=3/2`.  They justify the exchange, but they do not provide the signed
cutoff decay required for H15.
-/

open scoped BigOperators Topology LSeries.notation Interval
open Complex Filter MeasureTheory LSeries

namespace NBMellinTools.NB12

/-! ## Continuity of one paired frequency -/

theorem continuous_bblsEstermannThreeHalfPoint :
    Continuous bblsEstermannThreeHalfPoint := by
  unfold bblsEstermannThreeHalfPoint
  fun_prop

theorem continuous_bblsEstermannTerm_threeHalf
    (phase : ℝ) (r : ℕ) :
    Continuous (fun t : ℝ =>
      LSeries.term (bblsEstermannCoeff phase)
        (bblsEstermannThreeHalfPoint t) r) := by
  by_cases hr : r = 0
  · subst r
    simpa only [LSeries.term_zero] using
      (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
  · rw [show (fun t : ℝ =>
          LSeries.term (bblsEstermannCoeff phase)
            (bblsEstermannThreeHalfPoint t) r) =
        (fun t : ℝ => bblsEstermannCoeff phase r /
          (r : ℂ) ^ (bblsEstermannThreeHalfPoint t)) by
        funext t
        rw [LSeries.term_of_ne_zero hr]
      ]
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr
    letI : NeZero (r : ℂ) := ⟨hr0⟩
    exact continuous_const.div
      ((continuous_const_cpow (r : ℂ)).comp
        continuous_bblsEstermannThreeHalfPoint)
      (fun _ => cpow_ne_zero_iff.mpr (Or.inl hr0))

theorem continuous_Gamma_neg_bblsEstermannThreeHalfPoint :
    Continuous (fun t : ℝ =>
      Complex.Gamma (-bblsEstermannThreeHalfPoint t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  apply (Complex.continuousAt_Gamma _ ?_).comp
    continuous_bblsEstermannThreeHalfPoint.neg.continuousAt
  intro n hn
  have hre := congrArg Complex.re hn
  have hn' : (n : ℝ) = 3 / 2 := by
    norm_num [bblsEstermannThreeHalfPoint] at hre ⊢
    linarith
  have hlo : 1 < n := by
    exact_mod_cast (show (1 : ℝ) < n by rw [hn']; norm_num)
  have hhi : n < 2 := by
    exact_mod_cast (show (n : ℝ) < 2 by rw [hn']; norm_num)
  omega

theorem continuous_Gamma_bblsEstermannThreeHalfPoint :
    Continuous (fun t : ℝ =>
      Complex.Gamma (bblsEstermannThreeHalfPoint t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  apply (Complex.continuousAt_Gamma _ ?_).comp
    continuous_bblsEstermannThreeHalfPoint.continuousAt
  intro n hn
  have hre := congrArg Complex.re hn
  norm_num [bblsEstermannThreeHalfPoint] at hre
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem continuous_bblsActiveThreeHalfFrequencyTerm
    {damping : ℝ} (hdamping : 0 < damping)
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q) (r : ℕ) :
    Continuous (bblsActiveThreeHalfFrequencyTerm
      damping a q haq r) := by
  have hd0 : (damping : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hdamping.ne'
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  have hpi0 : (2 * (Real.pi : ℂ)) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)
  letI : NeZero (damping : ℂ) := ⟨hd0⟩
  letI : NeZero (q : ℂ) := ⟨hq0⟩
  letI : NeZero (2 * (Real.pi : ℂ)) := ⟨hpi0⟩
  have hs : Continuous (fun t : ℝ => bblsEstermannThreeHalfPoint t) :=
    continuous_bblsEstermannThreeHalfPoint
  have hd : Continuous (fun t : ℝ =>
      (damping : ℂ) ^ (bblsEstermannThreeHalfPoint t)) :=
    (continuous_const_cpow (damping : ℂ)).comp hs
  have hqpow : Continuous (fun t : ℝ =>
      (q : ℂ) ^ (2 * bblsEstermannThreeHalfPoint t - 1)) :=
    (continuous_const_cpow (q : ℂ)).comp
      ((continuous_const.mul hs).sub continuous_const)
  have hpipow : Continuous (fun t : ℝ =>
      (2 * Real.pi : ℂ) ^
        (-2 * bblsEstermannThreeHalfPoint t)) :=
    (continuous_const_cpow (2 * Real.pi : ℂ)).comp
      ((continuous_const : Continuous (fun _ : ℝ => (-(2 : ℂ)))).mul hs)
  have hfactor : Continuous (fun t : ℝ =>
      bblsEstermannClassicalFactor q
        (bblsEstermannThreeHalfPoint t)) := by
    unfold bblsEstermannClassicalFactor
    exact (((continuous_const.mul hqpow).mul hpipow).mul
      (continuous_Gamma_bblsEstermannThreeHalfPoint.pow 2))
  have hcos : Continuous (fun t : ℝ =>
      Complex.cos ((Real.pi : ℂ) *
        bblsEstermannThreeHalfPoint t)) := by
    exact Complex.continuous_cos.comp (continuous_const.mul hs)
  have hp := continuous_bblsEstermannTerm_threeHalf
    ((bblsEstermannInverseNumerator a q haq : ℝ) / (q : ℝ)) r
  have hm := continuous_bblsEstermannTerm_threeHalf
    ((bblsEstermannNegativeInverseNumerator a q haq : ℝ) / (q : ℝ)) r
  unfold bblsActiveThreeHalfFrequencyTerm
  exact ((continuous_Gamma_neg_bblsEstermannThreeHalfPoint.mul hd).mul
    ((hfactor.mul hp).add ((hfactor.mul hcos).mul hm)))

/-! ## A summable global majorant -/

/-- One paired frequency has the same vertical Gamma decay as the full row,
with the full Dirichlet majorant replaced by the norm of that frequency. -/
theorem norm_bblsActiveThreeHalfFrequencyTerm_le
    {damping : ℝ} (hdamping : 0 < damping)
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q)
    (r : ℕ) (t : ℝ) :
    ‖bblsActiveThreeHalfFrequencyTerm damping a q haq r t‖ ≤
      (4 * Real.sqrt (2 * Real.pi)) *
        (q : ℝ) ^ 2 * damping ^ (3 / 2 : ℝ) *
        ‖LSeries.term bblsEstermannDivisorCoeff (3 / 2 : ℂ) r‖ *
        bblsPolynomialExponentialMajorant 2 (Real.pi / 2) t := by
  let s := bblsEstermannThreeHalfPoint t
  let G := Complex.Gamma (-s)
  let P := LSeries.term
    (bblsEstermannCoeff
      ((bblsEstermannInverseNumerator a q haq : ℝ) / (q : ℝ))) s r
  let M := LSeries.term
    (bblsEstermannCoeff
      ((bblsEstermannNegativeInverseNumerator a q haq : ℝ) / (q : ℝ))) s r
  let F := bblsEstermannClassicalFactor q s
  let C := Complex.cos ((Real.pi : ℂ) * s)
  let D := ‖LSeries.term bblsEstermannDivisorCoeff (3 / 2 : ℂ) r‖
  have hG : ‖G‖ ≤ 2 * gammaHalfMajorant t :=
    norm_Gamma_neg_bblsEstermannThreeHalfPoint_le t
  have hd : ‖(damping : ℂ) ^ s‖ = damping ^ (3 / 2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hdamping]
    norm_num [s, bblsEstermannThreeHalfPoint]
  have hF : ‖F‖ ≤ (q : ℝ) ^ 2 * (1 + |t|) ^ 2 :=
    norm_bblsEstermannClassicalFactor_threeHalf_le q t
  have hFC : ‖F * C‖ ≤ (q : ℝ) ^ 2 * (1 + |t|) ^ 2 :=
    norm_bblsEstermannClassicalFactor_mul_cos_threeHalf_le q t
  have hP : ‖P‖ = D := by
    exact norm_bblsEstermann_term_threeHalfPoint _ r t
  have hM : ‖M‖ = D := by
    exact norm_bblsEstermann_term_threeHalfPoint _ r t
  have hgamma : 0 ≤ gammaHalfMajorant t := by
    unfold gammaHalfMajorant
    positivity
  have hD : 0 ≤ D := norm_nonneg _
  have hq : 0 ≤ (q : ℝ) ^ 2 := by positivity
  have ht : 0 ≤ (1 + |t|) ^ 2 := by positivity
  have hdpow : 0 ≤ damping ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg hdamping.le _
  unfold bblsActiveThreeHalfFrequencyTerm
  change ‖G * (damping : ℂ) ^ s * (F * P + (F * C) * M)‖ ≤ _
  calc
    ‖G * (damping : ℂ) ^ s * (F * P + (F * C) * M)‖ ≤
        ‖G‖ * ‖(damping : ℂ) ^ s‖ *
          (‖F‖ * ‖P‖ + ‖F * C‖ * ‖M‖) := by
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [norm_mul] using
          norm_add_le (F * P) ((F * C) * M))
        (mul_nonneg (norm_nonneg G)
          (norm_nonneg ((damping : ℂ) ^ s)))
    _ ≤ (2 * gammaHalfMajorant t) * damping ^ (3 / 2 : ℝ) *
        (((q : ℝ) ^ 2 * (1 + |t|) ^ 2) * D +
          ((q : ℝ) ^ 2 * (1 + |t|) ^ 2) * D) := by
      rw [hd, hP, hM]
      gcongr
    _ = (4 * Real.sqrt (2 * Real.pi)) *
        (q : ℝ) ^ 2 * damping ^ (3 / 2 : ℝ) * D *
        bblsPolynomialExponentialMajorant 2 (Real.pi / 2) t := by
      unfold gammaHalfMajorant bblsPolynomialExponentialMajorant
      ring

/-- Every paired frequency is globally integrable on the three-halves
vertical line. -/
theorem integrable_bblsActiveThreeHalfFrequencyTerm
    {damping : ℝ} (hdamping : 0 < damping)
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q) (r : ℕ) :
    Integrable (bblsActiveThreeHalfFrequencyTerm damping a q haq r) := by
  let c : ℝ :=
    (4 * Real.sqrt (2 * Real.pi)) * (q : ℝ) ^ 2 *
      damping ^ (3 / 2 : ℝ) *
      ‖LSeries.term bblsEstermannDivisorCoeff (3 / 2 : ℂ) r‖
  have hmajorant : Integrable (fun t : ℝ =>
      c * bblsPolynomialExponentialMajorant 2 (Real.pi / 2) t) :=
    (integrable_bblsPolynomialExponentialMajorant 2
      (by positivity : 0 < Real.pi / 2)).const_mul c
  apply Integrable.mono' hmajorant
  · exact (continuous_bblsActiveThreeHalfFrequencyTerm
      hdamping a q haq r).aestronglyMeasurable
  · filter_upwards [] with t
    exact norm_bblsActiveThreeHalfFrequencyTerm_le
      hdamping a q haq r t

/-- The global `L¹` norms of the shifted paired frequencies are summable.
This is stronger than the compact-window statement needed by the truncated
right edge and makes the later exchange independent of the contour height. -/
theorem summable_integral_norm_bblsActiveThreeHalfFrequencyTerm
    {damping : ℝ} (hdamping : 0 < damping)
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q) (K : ℕ) :
    Summable (fun j : ℕ =>
      ∫ t : ℝ, ‖bblsActiveThreeHalfFrequencyTerm damping a q haq
        (j + (K + 1)) t‖) := by
  have hs : Summable (fun j : ℕ =>
      ‖LSeries.term bblsEstermannDivisorCoeff (3 / 2 : ℂ)
        (j + (K + 1))‖) :=
    summable_bblsThreeHalfDirichletMajorant.comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
  let C : ℝ :=
    (4 * Real.sqrt (2 * Real.pi)) * (q : ℝ) ^ 2 *
      damping ^ (3 / 2 : ℝ)
  let M : ℝ := ∫ t : ℝ,
    bblsPolynomialExponentialMajorant 2 (Real.pi / 2) t
  have hcomparison : ∀ j : ℕ,
      (∫ t : ℝ, ‖bblsActiveThreeHalfFrequencyTerm damping a q haq
        (j + (K + 1)) t‖) ≤
        (C * M) *
          ‖LSeries.term bblsEstermannDivisorCoeff (3 / 2 : ℂ)
            (j + (K + 1))‖ := by
    intro j
    let c : ℝ := C *
      ‖LSeries.term bblsEstermannDivisorCoeff (3 / 2 : ℂ)
        (j + (K + 1))‖
    have hrow :=
      (integrable_bblsActiveThreeHalfFrequencyTerm hdamping a q haq
        (j + (K + 1))).norm
    have hmaj : Integrable (fun t : ℝ =>
        c * bblsPolynomialExponentialMajorant 2 (Real.pi / 2) t) :=
      (integrable_bblsPolynomialExponentialMajorant 2
        (by positivity : 0 < Real.pi / 2)).const_mul c
    have hle :
        (∫ t : ℝ, ‖bblsActiveThreeHalfFrequencyTerm damping a q haq
          (j + (K + 1)) t‖) ≤
          ∫ t : ℝ,
            c * bblsPolynomialExponentialMajorant 2 (Real.pi / 2) t := by
      apply integral_mono hrow hmaj
      intro t
      simpa [c, C, mul_assoc] using
        norm_bblsActiveThreeHalfFrequencyTerm_le
          hdamping a q haq (j + (K + 1)) t
    rw [integral_const_mul] at hle
    dsimp [c, C, M] at hle ⊢
    calc
      (∫ t : ℝ, ‖bblsActiveThreeHalfFrequencyTerm damping a q haq
        (j + (K + 1)) t‖) ≤
          ((4 * Real.sqrt (2 * Real.pi)) * (q : ℝ) ^ 2 *
              damping ^ (3 / 2 : ℝ) *
              ‖LSeries.term bblsEstermannDivisorCoeff (3 / 2 : ℂ)
                (j + (K + 1))‖) *
            ∫ t : ℝ,
              bblsPolynomialExponentialMajorant 2 (Real.pi / 2) t := hle
      _ = (((4 * Real.sqrt (2 * Real.pi)) * (q : ℝ) ^ 2 *
              damping ^ (3 / 2 : ℝ)) *
            ∫ t : ℝ,
              bblsPolynomialExponentialMajorant 2 (Real.pi / 2) t) *
          ‖LSeries.term bblsEstermannDivisorCoeff (3 / 2 : ℂ)
            (j + (K + 1))‖ := by ring
  exact ((hs.mul_left (C * M)).of_nonneg_of_le
    (fun _ => integral_nonneg fun _ => norm_nonneg _)) hcomparison

/-- Genuine global exchange of the shifted high-frequency Estermann series
with vertical integration. -/
theorem tsum_integral_eq_integral_tsum_bblsActiveThreeHalfFrequencyTerm
    {damping : ℝ} (hdamping : 0 < damping)
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q) (K : ℕ) :
    (∑' j : ℕ, ∫ t : ℝ,
      bblsActiveThreeHalfFrequencyTerm damping a q haq
        (j + (K + 1)) t) =
      ∫ t : ℝ, ∑' j : ℕ,
        bblsActiveThreeHalfFrequencyTerm damping a q haq
          (j + (K + 1)) t := by
  exact integral_tsum_of_summable_integral_norm
    (fun j => integrable_bblsActiveThreeHalfFrequencyTerm
      hdamping a q haq (j + (K + 1)))
    (summable_integral_norm_bblsActiveThreeHalfFrequencyTerm
      hdamping a q haq K)

/-- The same exchange on every symmetric finite contour window.  The proof
is inherited from the global `L¹` theorem by restriction, so its majorant is
independent of the height `T`. -/
theorem tsum_intervalIntegral_eq_intervalIntegral_tsum_bblsActiveThreeHalfFrequencyTerm
    {damping : ℝ} (hdamping : 0 < damping)
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q) (K : ℕ)
    (T : ℝ) (hT : 0 ≤ T) :
    (∑' j : ℕ, ∫ t : ℝ in -T..T,
      bblsActiveThreeHalfFrequencyTerm damping a q haq
        (j + (K + 1)) t) =
      ∫ t : ℝ in -T..T, ∑' j : ℕ,
        bblsActiveThreeHalfFrequencyTerm damping a q haq
          (j + (K + 1)) t := by
  have hle : -T ≤ T := by linarith
  let s : Set ℝ := Set.Ioc (-T) T
  have hrestricted (j : ℕ) :
      Integrable
        (bblsActiveThreeHalfFrequencyTerm damping a q haq
          (j + (K + 1))) (volume.restrict s) :=
    (integrable_bblsActiveThreeHalfFrequencyTerm
      hdamping a q haq (j + (K + 1))).integrableOn
  have hrestrictedNorm : Summable (fun j : ℕ =>
      ∫ t : ℝ, ‖bblsActiveThreeHalfFrequencyTerm damping a q haq
        (j + (K + 1)) t‖ ∂(volume.restrict s)) := by
    apply (summable_integral_norm_bblsActiveThreeHalfFrequencyTerm
      hdamping a q haq K).of_nonneg_of_le
    · intro j
      exact integral_nonneg fun _ => norm_nonneg _
    · intro j
      exact integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        (integrable_bblsActiveThreeHalfFrequencyTerm
          hdamping a q haq (j + (K + 1))).norm
  have hexchange := integral_tsum_of_summable_integral_norm
    hrestricted hrestrictedNorm
  simpa only [s, intervalIntegral.integral_of_le hle] using hexchange

/-- The active high-frequency row is globally integrable. -/
theorem integrable_bblsActiveThreeHalfHighFrequency
    {damping : ℝ} (hdamping : 0 < damping)
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q) (K : ℕ) :
    Integrable (fun t : ℝ =>
      bblsActiveThreeHalfHighFrequency damping a q haq t K) := by
  have hs : Summable (fun j : ℕ =>
      ‖LSeries.term bblsEstermannDivisorCoeff (3 / 2 : ℂ)
        (j + (K + 1))‖) :=
    summable_bblsThreeHalfDirichletMajorant.comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
  let C : ℝ :=
    (4 * Real.sqrt (2 * Real.pi)) * (q : ℝ) ^ 2 *
      damping ^ (3 / 2 : ℝ)
  let B : ℝ := ∑' j : ℕ,
    ‖LSeries.term bblsEstermannDivisorCoeff (3 / 2 : ℂ)
      (j + (K + 1))‖
  have hmajorant : Integrable (fun t : ℝ =>
      (C * B) *
        bblsPolynomialExponentialMajorant 2 (Real.pi / 2) t) :=
    (integrable_bblsPolynomialExponentialMajorant 2
      (by positivity : 0 < Real.pi / 2)).const_mul (C * B)
  have hsum : Integrable (fun t : ℝ => ∑' j : ℕ,
      bblsActiveThreeHalfFrequencyTerm damping a q haq
        (j + (K + 1)) t) := by
    apply Integrable.mono' hmajorant
    · exact (AEMeasurable.tsum fun j =>
        (continuous_bblsActiveThreeHalfFrequencyTerm
          hdamping a q haq (j + (K + 1))).measurable.aemeasurable
        ).aestronglyMeasurable
    · filter_upwards [] with t
      let P : ℝ :=
        bblsPolynomialExponentialMajorant 2 (Real.pi / 2) t
      have hP : 0 ≤ P := by
        unfold P bblsPolynomialExponentialMajorant
        positivity
      have hC : 0 ≤ C := by
        unfold C
        positivity
      have hbound : ∀ j : ℕ,
          ‖bblsActiveThreeHalfFrequencyTerm damping a q haq
              (j + (K + 1)) t‖ ≤
            (C * P) *
              ‖LSeries.term bblsEstermannDivisorCoeff (3 / 2 : ℂ)
                (j + (K + 1))‖ := by
        intro j
        simpa [C, P, mul_assoc, mul_left_comm, mul_comm] using
          norm_bblsActiveThreeHalfFrequencyTerm_le
            hdamping a q haq (j + (K + 1)) t
      have hseq : Summable (fun j : ℕ =>
          (C * P) *
            ‖LSeries.term bblsEstermannDivisorCoeff (3 / 2 : ℂ)
              (j + (K + 1))‖) :=
        hs.mul_left (C * P)
      have hnorms : Summable (fun j : ℕ =>
          ‖bblsActiveThreeHalfFrequencyTerm damping a q haq
            (j + (K + 1)) t‖) :=
        hseq.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
      calc
        ‖∑' j : ℕ, bblsActiveThreeHalfFrequencyTerm damping a q haq
            (j + (K + 1)) t‖ ≤
            ∑' j : ℕ,
              ‖bblsActiveThreeHalfFrequencyTerm damping a q haq
                (j + (K + 1)) t‖ :=
          norm_tsum_le_tsum_norm hnorms
        _ ≤ ∑' j : ℕ, (C * P) *
              ‖LSeries.term bblsEstermannDivisorCoeff (3 / 2 : ℂ)
                (j + (K + 1))‖ :=
          Summable.tsum_le_tsum hbound hnorms hseq
        _ = (C * B) *
              bblsPolynomialExponentialMajorant 2 (Real.pi / 2) t := by
          rw [tsum_mul_left]
          dsimp [B, P]
          ring
  exact hsum.congr (Filter.Eventually.of_forall fun t =>
    (bblsActiveThreeHalfHighFrequency_eq_tsum a q haq t K).symm)

/-- On a finite window the integral of one high row is the `tsum` of the
integrals of its genuine shifted frequencies. -/
theorem intervalIntegral_bblsActiveThreeHalfHighFrequency_eq_tsum
    {damping : ℝ} (hdamping : 0 < damping)
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q) (K : ℕ)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t : ℝ in -T..T,
      bblsActiveThreeHalfHighFrequency damping a q haq t K) =
      ∑' j : ℕ, ∫ t : ℝ in -T..T,
        bblsActiveThreeHalfFrequencyTerm damping a q haq
          (j + (K + 1)) t := by
  calc
    (∫ t : ℝ in -T..T,
      bblsActiveThreeHalfHighFrequency damping a q haq t K) =
        ∫ t : ℝ in -T..T, ∑' j : ℕ,
          bblsActiveThreeHalfFrequencyTerm damping a q haq
            (j + (K + 1)) t := by
      apply intervalIntegral.integral_congr
      intro t _
      exact bblsActiveThreeHalfHighFrequency_eq_tsum a q haq t K
    _ = ∑' j : ℕ, ∫ t : ℝ in -T..T,
        bblsActiveThreeHalfFrequencyTerm damping a q haq
          (j + (K + 1)) t :=
      (tsum_intervalIntegral_eq_intervalIntegral_tsum_bblsActiveThreeHalfFrequencyTerm
        hdamping a q haq K T hT).symm

/-! ## Assembly over the finite signed H15 row family -/

/-- The complete signed high-frequency aggregate is globally integrable for
every fixed H15 cutoff and every frequency cutoff. -/
theorem integrable_h15ThreeHalfHighFrequencyAggregate
    (n K : ℕ) :
    Integrable (h15ThreeHalfHighFrequencyAggregate n K) := by
  unfold h15ThreeHalfHighFrequencyAggregate
  apply integrable_finsetSum
  intro i _
  exact (integrable_bblsActiveThreeHalfHighFrequency
    (h15ContourDamping_pos n)
    (h15LaurentRow i).numerator (h15LaurentRow i).denominator
    (h15LaurentRow i).coprime K).const_mul (h15LaurentRowWeight i)

/-- The finite low-frequency aggregate is also globally integrable.  This is
deduced from the already proved full-line integrability and the exact
low/high split, avoiding any second majorant argument. -/
theorem integrable_h15ThreeHalfLowFrequencyAggregate
    (n K : ℕ) :
    Integrable (h15ThreeHalfLowFrequencyAggregate n K) := by
  have htotal : Integrable (fun t : ℝ =>
      h15VerticalAggregate n (3 / 2) t) := by
    exact integrable_h15ActiveContourAggregate_threeHalf n
  have hhigh := integrable_h15ThreeHalfHighFrequencyAggregate n K
  have hdiff : Integrable (fun t : ℝ =>
      h15VerticalAggregate n (3 / 2) t -
        h15ThreeHalfHighFrequencyAggregate n K t) :=
    htotal.sub hhigh
  exact hdiff.congr (Filter.Eventually.of_forall fun t => by
    change h15VerticalAggregate n (3 / 2) t -
      h15ThreeHalfHighFrequencyAggregate n K t =
        h15ThreeHalfLowFrequencyAggregate n K t
    rw [h15VerticalAggregate_threeHalf_eq_low_add_high n K t]
    ring)

/-- The algebraically defined high remainder is exactly the interval
integral of the genuine shifted high-frequency `tsum`. -/
theorem h15ThreeHalfHighFrequencyIntegralRemainder_eq_integral
    (n K : ℕ) (T : ℝ) :
    h15ThreeHalfHighFrequencyIntegralRemainder n K T =
      ∫ t : ℝ in -T..T,
        h15ThreeHalfHighFrequencyAggregate n K t := by
  have hlow : IntervalIntegrable
      (h15ThreeHalfLowFrequencyAggregate n K) volume (-T) T :=
    (integrable_h15ThreeHalfLowFrequencyAggregate n K).intervalIntegrable
  have hhigh : IntervalIntegrable
      (h15ThreeHalfHighFrequencyAggregate n K) volume (-T) T :=
    (integrable_h15ThreeHalfHighFrequencyAggregate n K).intervalIntegrable
  have hpoint : (fun t : ℝ => h15VerticalAggregate n (3 / 2) t) =
      fun t : ℝ => h15ThreeHalfLowFrequencyAggregate n K t +
        h15ThreeHalfHighFrequencyAggregate n K t := by
    funext t
    exact h15VerticalAggregate_threeHalf_eq_low_add_high n K t
  unfold h15ThreeHalfHighFrequencyIntegralRemainder
    h15TruncatedVerticalIntegral h15ThreeHalfLowFrequencyIntegral
  rw [hpoint, intervalIntegral.integral_add hlow hhigh]
  ring

/-- Consequently the high right-edge remainder has no hidden residue or
endpoint term: it is precisely `I` times the genuine high-frequency
integral. -/
theorem h15HighFrequencyRightEdgeRemainder_eq_integral
    (n K : ℕ) (T : ℝ) :
    h15HighFrequencyRightEdgeRemainder n K T =
      I * ∫ t : ℝ in -T..T,
        h15ThreeHalfHighFrequencyAggregate n K t := by
  unfold h15HighFrequencyRightEdgeRemainder
  rw [h15ThreeHalfHighFrequencyIntegralRemainder_eq_integral]

/-- Fully expanded exchange theorem for the H15 high remainder.  It is a
finite signed sum over the exact H15 rows, followed by the genuine shifted
frequency `tsum`; all residue and endpoint corrections remain absent from
this high sector. -/
theorem h15ThreeHalfHighFrequencyIntegralRemainder_eq_sum_tsum
    (n K : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    h15ThreeHalfHighFrequencyIntegralRemainder n K T =
      ∑ i : H15LaurentRowIndex (NB8.logTaperLength n),
        h15LaurentRowWeight i *
          (∑' j : ℕ, ∫ t : ℝ in -T..T,
            bblsActiveThreeHalfFrequencyTerm (h15ContourDamping n)
              (h15LaurentRow i).numerator
              (h15LaurentRow i).denominator
              (h15LaurentRow i).coprime (j + (K + 1)) t) := by
  rw [h15ThreeHalfHighFrequencyIntegralRemainder_eq_integral]
  unfold h15ThreeHalfHighFrequencyAggregate
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral_bblsActiveThreeHalfHighFrequency_eq_tsum
      (h15ContourDamping_pos n)
      (h15LaurentRow i).numerator (h15LaurentRow i).denominator
      (h15LaurentRow i).coprime K T hT]
  · intro i _
    exact (integrable_bblsActiveThreeHalfHighFrequency
      (h15ContourDamping_pos n)
      (h15LaurentRow i).numerator (h15LaurentRow i).denominator
      (h15LaurentRow i).coprime K).const_mul
        (h15LaurentRowWeight i) |>.intervalIntegrable

end NBMellinTools.NB12
