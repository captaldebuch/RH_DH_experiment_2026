/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSEstermannCompatibility
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# NB12h: shifted Abel--Mellin identity for the BBLS Estermann series

The BBLS product expansion contains `1 / (m*ell)`.  After divisor
regrouping, the relevant damped series is therefore

`sum d(n) e(n*x) exp(-delta*n) / n`,

not the unshifted Lambert series without `1/n`.  Consequently the correct
Mellin integrand is

`delta^(-w) Gamma(w) D(1+w,x)`

on `Re(w)=1/2`, so that the Estermann series itself is evaluated on the
absolutely convergent line `Re(1+w)=3/2`.

This file proves the raw identity with a genuine global sum--integral
exchange.  It does not shift the contour, apply an Estermann functional
equation, pass to `delta = 0`, or prove signed H15 decay.
-/

open scoped BigOperators Topology LSeries.notation
open Complex MeasureTheory Set LSeries

namespace NBMellinTools.NB12

/-! ## Gamma on the central Abel line -/

/-- Elementary sine evaluation needed for the Gamma reflection formula. -/
lemma sin_pi_half_add_I_mul (t : ℝ) :
    Complex.sin ((Real.pi : ℂ) * ((1 / 2 : ℝ) + Complex.I * t)) =
      (Real.cosh (Real.pi * t) : ℂ) := by
  rw [show (Real.pi : ℂ) * ((1 / 2 : ℝ) + Complex.I * t) =
      (Real.pi / 2 : ℂ) + (Real.pi * t) * Complex.I by
        push_cast
        ring]
  rw [Complex.sin_add_mul_I]
  rw [show Complex.sin ((Real.pi : ℂ) / 2) = 1 by
      have h : (Real.pi : ℂ) / 2 = ((Real.pi / 2 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [h, ← Complex.ofReal_sin]
      norm_num,
    show Complex.cos ((Real.pi : ℂ) / 2) = 0 by
      have h : (Real.pi : ℂ) / 2 = ((Real.pi / 2 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [h, ← Complex.ofReal_cos]
      norm_num]
  simp [Complex.ofReal_cosh]

/-- Exact squared Gamma norm on `Re(w)=1/2`. -/
theorem norm_Gamma_half_add_I_mul_sq (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℝ) + Complex.I * t)‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * t) := by
  let a : ℂ := (1 / 2 : ℝ) + Complex.I * t
  have ha : (1 - a) = (starRingEnd ℂ) a := by
    dsimp [a]
    apply Complex.ext
    · norm_num
    · simp
  have hgamma := Complex.Gamma_mul_Gamma_one_sub a
  rw [ha, Complex.Gamma_conj] at hgamma
  have hsin : Complex.sin (Real.pi * a) =
      (Real.cosh (Real.pi * t) : ℂ) :=
    sin_pi_half_add_I_mul t
  rw [hsin] at hgamma
  have hnorm : (‖Complex.Gamma a‖ ^ 2 : ℂ) =
      (starRingEnd ℂ) (Complex.Gamma a) * Complex.Gamma a := by
    calc
      (‖Complex.Gamma a‖ ^ 2 : ℂ) =
          (Complex.normSq (Complex.Gamma a) : ℂ) := by
            exact_mod_cast
              (Complex.normSq_eq_norm_sq (Complex.Gamma a)).symm
      _ = (starRingEnd ℂ) (Complex.Gamma a) * Complex.Gamma a :=
        Complex.normSq_eq_conj_mul_self
  have hgammaNorm : (‖Complex.Gamma a‖ ^ 2 : ℂ) =
      (Real.pi : ℂ) / (Real.cosh (Real.pi * t) : ℂ) := by
    rw [hnorm]
    calc
      (starRingEnd ℂ) (Complex.Gamma a) * Complex.Gamma a =
          Complex.Gamma a * (starRingEnd ℂ) (Complex.Gamma a) := by ring
      _ = (Real.pi : ℂ) / (Real.cosh (Real.pi * t) : ℂ) := hgamma
  have hgammaReal : ‖Complex.Gamma a‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * t) := by
    exact_mod_cast hgammaNorm
  simpa [a] using hgammaReal

/-- Exponential majorant for Gamma on `Re(w)=1/2`. -/
noncomputable def gammaHalfMajorant (t : ℝ) : ℝ :=
  Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi / 2) * |t|)

/-- Standard lower bound for hyperbolic cosine. -/
theorem exp_abs_le_two_mul_cosh (x : ℝ) :
    Real.exp |x| ≤ 2 * Real.cosh x := by
  rw [Real.cosh_eq]
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    linarith [Real.exp_pos (-x)]
  · rw [abs_of_neg (lt_of_not_ge hx)]
    linarith [Real.exp_pos x]

/-- Intrinsic exponential decay of Gamma on `Re(w)=1/2`. -/
theorem norm_Gamma_half_add_I_mul_le_majorant (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℝ) + Complex.I * t)‖ ≤
      gammaHalfMajorant t := by
  have hcosh : 0 < Real.cosh (Real.pi * t) := Real.cosh_pos _
  have hexp : 0 < Real.exp (Real.pi * |t|) := Real.exp_pos _
  have habs : |Real.pi * t| = Real.pi * |t| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
  have hcoshLower : Real.exp (Real.pi * |t|) ≤
      2 * Real.cosh (Real.pi * t) := by
    rw [← habs]
    exact exp_abs_le_two_mul_cosh (Real.pi * t)
  have hinv : 1 / Real.cosh (Real.pi * t) ≤
      2 * Real.exp (-(Real.pi * |t|)) := by
    rw [Real.exp_neg]
    apply (div_le_iff₀ hcosh).2
    calc
      1 = (Real.exp (Real.pi * |t|))⁻¹ *
          Real.exp (Real.pi * |t|) := by
            rw [inv_mul_cancel₀ hexp.ne']
      _ ≤ (Real.exp (Real.pi * |t|))⁻¹ *
          (2 * Real.cosh (Real.pi * t)) :=
            mul_le_mul_of_nonneg_left hcoshLower (inv_nonneg.mpr hexp.le)
      _ = 2 * (Real.exp (Real.pi * |t|))⁻¹ *
          Real.cosh (Real.pi * t) := by ring
  have hsquare :
      ‖Complex.Gamma ((1 / 2 : ℝ) + Complex.I * t)‖ ^ 2 ≤
        gammaHalfMajorant t ^ 2 := by
    rw [norm_Gamma_half_add_I_mul_sq]
    unfold gammaHalfMajorant
    have hsqrt : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi := by
      rw [Real.sq_sqrt]
      positivity
    rw [mul_pow, hsqrt]
    rw [show Real.exp (-(Real.pi / 2) * |t|) ^ 2 =
        Real.exp (-(Real.pi * |t|)) by
      rw [← Real.exp_nat_mul]
      congr 1
      ring]
    calc
      Real.pi / Real.cosh (Real.pi * t) ≤
          Real.pi * (2 * Real.exp (-(Real.pi * |t|))) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa [one_div] using hinv) Real.pi_pos.le
      _ = 2 * Real.pi * Real.exp (-(Real.pi * |t|)) := by ring
  have hmajorant : 0 ≤ gammaHalfMajorant t := by
    unfold gammaHalfMajorant
    positivity
  nlinarith [norm_nonneg
    (Complex.Gamma ((1 / 2 : ℝ) + Complex.I * t))]

set_option maxHeartbeats 800000 in
-- The half-line transport through `Measure.measurePreserving_neg` triggers
-- substantial elaboration in Mathlib's measure-theory typeclass hierarchy.
/-- The explicit Gamma majorant is integrable on the real line. -/
theorem integrable_gammaHalfMajorant : Integrable gammaHalfMajorant := by
  let a : ℝ := Real.pi / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hzero : IntegrableOn
      (fun x : ℝ => x ^ (0 : ℝ) * Real.exp (-a * x ^ (1 : ℝ)))
        (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) ha
  have hpos : IntegrableOn
      (fun x : ℝ => Real.exp (-a * |x|)) (Ioi 0) := by
    refine hzero.congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hx' : 0 < x := hx
    change x ^ (0 : ℝ) * Real.exp (-a * x ^ (1 : ℝ)) =
      Real.exp (-a * |x|)
    rw [abs_of_pos hx']
    simp only [Real.rpow_zero, one_mul, Real.rpow_one]
  have hneg : IntegrableOn
      (fun x : ℝ => Real.exp (-a * |x|)) (Iio 0) := by
    rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
    simpa only [Function.comp_def, abs_neg, neg_preimage, neg_Iio, neg_zero]
      using hpos
  have hfull : Integrable (fun x : ℝ => Real.exp (-a * |x|)) := by
    rw [← integrableOn_univ, ← Iio_union_Ici, integrableOn_union]
    refine ⟨hneg, ?_⟩
    rwa [integrableOn_Ici_iff_integrableOn_Ioi]
  unfold gammaHalfMajorant
  convert hfull.const_mul (Real.sqrt (2 * Real.pi)) using 1

/-- Gamma is vertically integrable on the shifted BBLS Abel line. -/
theorem verticalIntegrable_Gamma_half :
    Complex.VerticalIntegrable Complex.Gamma (1 / 2 : ℝ) := by
  apply Integrable.mono' integrable_gammaHalfMajorant
  · have hline : Continuous
        (fun t : ℝ => Complex.Gamma ((1 / 2 : ℝ) + t * Complex.I)) := by
      rw [continuous_iff_continuousAt]
      intro t
      apply (Complex.continuousAt_Gamma _ ?_).comp (by fun_prop)
      intro n h
      have hre := congrArg Complex.re h
      norm_num at hre
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    exact hline.aestronglyMeasurable
  · filter_upwards [] with t
    simpa [mul_comm (t : ℂ) Complex.I] using
      norm_Gamma_half_add_I_mul_le_majorant t

/-! ## Inverse Mellin for exponential damping -/

/-- Exponential damping as a complex-valued function. -/
noncomputable def bblsAbelExponential (x : ℝ) : ℂ := Real.exp (-x)

/-- Euler's Gamma integral is the Mellin transform of exponential damping. -/
theorem mellin_bblsAbelExponential_eq_Gamma {s : ℂ} (hs : 0 < s.re) :
    mellin bblsAbelExponential s = Complex.Gamma s := by
  unfold bblsAbelExponential
  rw [← Complex.GammaIntegral_eq_mellin]
  exact (Complex.Gamma_eq_integral hs).symm

/-- Mellin convergence of exponential damping on `Re(w)=1/2`. -/
theorem mellinConvergent_bblsAbelExponential_half :
    MellinConvergent bblsAbelExponential (1 / 2 : ℝ) := by
  rw [MellinConvergent]
  refine IntegrableOn.congr_fun
    (Complex.GammaIntegral_convergent (s := (1 / 2 : ℂ)) (by norm_num))
    ?_ measurableSet_Ioi
  intro x hx
  unfold bblsAbelExponential
  simp only [smul_eq_mul]
  norm_num
  exact mul_comm _ _

/-- The Mellin transform is vertically integrable without Gaussian damping. -/
theorem verticalIntegrable_mellin_bblsAbelExponential_half :
    Complex.VerticalIntegrable (mellin bblsAbelExponential) (1 / 2 : ℝ) := by
  apply verticalIntegrable_Gamma_half.congr
  filter_upwards [] with t
  exact (mellin_bblsAbelExponential_eq_Gamma
    (s := ((1 / 2 : ℝ) : ℂ) + t * Complex.I) (by norm_num)).symm

/-- Specialized inverse Mellin theorem on the BBLS Abel line. -/
theorem mellinInv_mellin_bblsAbelExponential_half
    {x : ℝ} (hx : 0 < x) :
    mellinInv (1 / 2 : ℝ) (mellin bblsAbelExponential) x =
      Real.exp (-x) := by
  simpa [bblsAbelExponential] using
    mellinInv_mellin_eq (1 / 2 : ℝ) bblsAbelExponential hx
      mellinConvergent_bblsAbelExponential_half
      verticalIntegrable_mellin_bblsAbelExponential_half
      (Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp continuous_neg)).continuousAt

/-- Gamma itself has the expected inverse Mellin transform on `Re(w)=1/2`. -/
theorem mellinInv_Gamma_half {x : ℝ} (hx : 0 < x) :
    mellinInv (1 / 2 : ℝ) Complex.Gamma x = Real.exp (-x) := by
  calc
    mellinInv (1 / 2 : ℝ) Complex.Gamma x =
        mellinInv (1 / 2 : ℝ) (mellin bblsAbelExponential) x := by
      unfold mellinInv
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      rw [mellin_bblsAbelExponential_eq_Gamma
        (s := ((1 / 2 : ℝ) : ℂ) + t * Complex.I) (by norm_num)]
    _ = Real.exp (-x) := mellinInv_mellin_bblsAbelExponential_half hx

/-- Raw vertical-integral form of inverse Mellin for the exponential. -/
theorem integral_Gamma_vertical_half {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ,
      (x : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + t * Complex.I)) *
        Complex.Gamma (((1 / 2 : ℝ) : ℂ) + t * Complex.I)) =
      (2 * Real.pi : ℝ) * Real.exp (-x) := by
  have h := mellinInv_Gamma_half hx
  unfold mellinInv at h
  let J : ℂ := ∫ t : ℝ,
    (x : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + t * Complex.I)) *
      Complex.Gamma (((1 / 2 : ℝ) : ℂ) + t * Complex.I)
  change ((1 / (2 * Real.pi : ℝ) : ℝ) : ℂ) * J = Real.exp (-x) at h
  change J = ((2 * Real.pi : ℝ) : ℂ) * Real.exp (-x)
  have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  calc
    J = ((2 * Real.pi : ℝ) : ℂ) *
        (((1 / (2 * Real.pi : ℝ) : ℝ) : ℂ) * J) := by
      rw [← mul_assoc]
      norm_num
      field_simp
    _ = ((2 * Real.pi : ℝ) : ℂ) * Real.exp (-x) := by rw [h]

/-! ## Shifted Estermann series under the Abel contour -/

/-- The `n`th row of the correctly shifted BBLS Abel--Mellin integrand. -/
noncomputable def bblsAbelMellinEstermannTerm
    (phase damping : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  let w : ℂ := ((1 / 2 : ℝ) : ℂ) + t * Complex.I
  (damping : ℂ) ^ (-w) * Complex.Gamma w *
    LSeries.term (bblsEstermannCoeff phase) (1 + w) n

/-- On `Re(w)=1/2`, the shifted Estermann row is evaluated at real part
`3/2`; its norm is independent of the height. -/
theorem norm_bblsEstermannTerm_one_add_half_add_I_mul
    (phase : ℝ) (n : ℕ) (t : ℝ) :
    ‖LSeries.term (bblsEstermannCoeff phase)
      (1 + (((1 / 2 : ℝ) : ℂ) + t * Complex.I)) n‖ =
      ‖LSeries.term (bblsEstermannCoeff phase) (3 / 2 : ℂ) n‖ := by
  simp only [LSeries.norm_term_eq]
  congr 2
  norm_num

/-- A shifted L-series row separates into its value at `s=1` and the
remaining Mellin frequency. -/
theorem bblsEstermannTerm_one_add
    (phase : ℝ) (n : ℕ) (hn : n ≠ 0) (w : ℂ) :
    LSeries.term (bblsEstermannCoeff phase) (1 + w) n =
      LSeries.term (bblsEstermannCoeff phase) 1 n * (n : ℂ) ^ (-w) := by
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
  rw [Complex.cpow_add _ _ (by exact_mod_cast hn)]
  rw [Complex.cpow_neg]
  ring

/-- Uniform majorization of each shifted divisor row. -/
theorem norm_bblsAbelMellinEstermannTerm_le
    (phase : ℝ) {damping : ℝ} (hdamping : 0 < damping)
    (n : ℕ) (t : ℝ) :
    ‖bblsAbelMellinEstermannTerm phase damping n t‖ ≤
      (damping ^ (-(1 / 2 : ℝ)) *
          ‖LSeries.term (bblsEstermannCoeff phase) (3 / 2 : ℂ) n‖) *
        gammaHalfMajorant t := by
  unfold bblsAbelMellinEstermannTerm
  dsimp only
  rw [norm_mul, norm_mul]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hdamping]
  rw [norm_bblsEstermannTerm_one_add_half_add_I_mul]
  have hGamma : ‖Complex.Gamma
      (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ≤ gammaHalfMajorant t := by
    simpa [mul_comm] using norm_Gamma_half_add_I_mul_le_majorant t
  have hdpow : 0 ≤ damping ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg hdamping.le _
  have hterm : 0 ≤
      ‖LSeries.term (bblsEstermannCoeff phase) (3 / 2 : ℂ) n‖ :=
    norm_nonneg _
  norm_num
  have hmul := mul_le_mul_of_nonneg_left hGamma (mul_nonneg hdpow hterm)
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Each shifted divisor row is integrable on the full vertical line. -/
theorem integrable_bblsAbelMellinEstermannTerm
    (phase : ℝ) {damping : ℝ} (hdamping : 0 < damping) (n : ℕ) :
    Integrable (bblsAbelMellinEstermannTerm phase damping n) := by
  let c : ℝ := damping ^ (-(1 / 2 : ℝ)) *
    ‖LSeries.term (bblsEstermannCoeff phase) (3 / 2 : ℂ) n‖
  have hmajorant : Integrable (fun t : ℝ => c * gammaHalfMajorant t) :=
    integrable_gammaHalfMajorant.const_mul c
  apply Integrable.mono' hmajorant
  · have hd0 : (damping : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hdamping.ne'
    letI : NeZero (damping : ℂ) := ⟨hd0⟩
    have hpow : Continuous (fun t : ℝ =>
        (damping : ℂ) ^
          (-(((1 / 2 : ℝ) : ℂ) + t * Complex.I))) :=
      (continuous_const_cpow (damping : ℂ)).comp (by fun_prop)
    have hGamma : Continuous (fun t : ℝ =>
        Complex.Gamma (((1 / 2 : ℝ) : ℂ) + t * Complex.I)) := by
      rw [continuous_iff_continuousAt]
      intro t
      apply (Complex.continuousAt_Gamma _ ?_).comp (by fun_prop)
      intro k hk
      have hre := congrArg Complex.re hk
      norm_num at hre
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have hterm : Continuous (fun t : ℝ =>
        LSeries.term (bblsEstermannCoeff phase)
          (1 + (((1 / 2 : ℝ) : ℂ) + t * Complex.I)) n) := by
      by_cases hn : n = 0
      · subst n
        simpa only [LSeries.term_zero] using
          (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
      · rw [show (fun t : ℝ => LSeries.term (bblsEstermannCoeff phase)
            (1 + (((1 / 2 : ℝ) : ℂ) + t * Complex.I)) n) =
          (fun t : ℝ => bblsEstermannCoeff phase n /
            (n : ℂ) ^
              (1 + (((1 / 2 : ℝ) : ℂ) + t * Complex.I))) by
            funext t
            rw [LSeries.term_of_ne_zero hn]]
        have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
        letI : NeZero (n : ℂ) := ⟨hn0⟩
        exact continuous_const.div
          ((continuous_const_cpow (n : ℂ)).comp (by fun_prop))
          (fun _ => cpow_ne_zero_iff.mpr (Or.inl hn0))
    exact (hpow.mul hGamma |>.mul hterm).aestronglyMeasurable
  · filter_upwards [] with t
    exact norm_bblsAbelMellinEstermannTerm_le phase hdamping n t

/-- The rowwise `L¹` norms are summable.  This is the Tonelli/Fubini input
for the global BBLS Abel--Mellin exchange. -/
theorem summable_integral_norm_bblsAbelMellinEstermannTerm
    (phase : ℝ) {damping : ℝ} (hdamping : 0 < damping) :
    Summable (fun n : ℕ =>
      ∫ t : ℝ, ‖bblsAbelMellinEstermannTerm phase damping n t‖) := by
  have hs0 := bblsEstermannCoeff_summable phase
    (s := (3 / 2 : ℂ)) (by norm_num)
  rw [LSeriesSummable] at hs0
  have hs : Summable (fun n : ℕ =>
      ‖LSeries.term (bblsEstermannCoeff phase) (3 / 2 : ℂ) n‖) :=
    hs0.norm
  let M : ℝ := ∫ t : ℝ, gammaHalfMajorant t
  have hcomparison : ∀ n : ℕ,
      (∫ t : ℝ, ‖bblsAbelMellinEstermannTerm phase damping n t‖) ≤
        (damping ^ (-(1 / 2 : ℝ)) * M) *
          ‖LSeries.term (bblsEstermannCoeff phase) (3 / 2 : ℂ) n‖ := by
    intro n
    let c : ℝ := damping ^ (-(1 / 2 : ℝ)) *
      ‖LSeries.term (bblsEstermannCoeff phase) (3 / 2 : ℂ) n‖
    have hrow :=
      (integrable_bblsAbelMellinEstermannTerm phase hdamping n).norm
    have hmaj : Integrable (fun t : ℝ => c * gammaHalfMajorant t) :=
      integrable_gammaHalfMajorant.const_mul c
    have hle :
        (∫ t : ℝ, ‖bblsAbelMellinEstermannTerm phase damping n t‖) ≤
          ∫ t : ℝ, c * gammaHalfMajorant t := by
      apply integral_mono hrow hmaj
      intro t
      exact norm_bblsAbelMellinEstermannTerm_le phase hdamping n t
    rw [integral_const_mul] at hle
    dsimp [c, M] at hle ⊢
    calc
      (∫ t : ℝ, ‖bblsAbelMellinEstermannTerm phase damping n t‖) ≤
          (damping ^ (-(1 / 2 : ℝ)) *
            ‖LSeries.term (bblsEstermannCoeff phase) (3 / 2 : ℂ) n‖) *
            ∫ t : ℝ, gammaHalfMajorant t := hle
      _ = (damping ^ (-(1 / 2 : ℝ)) *
            ∫ t : ℝ, gammaHalfMajorant t) *
            ‖LSeries.term (bblsEstermannCoeff phase) (3 / 2 : ℂ) n‖ := by
          ring
  exact ((hs.mul_left (damping ^ (-(1 / 2 : ℝ)) * M)).of_nonneg_of_le
    (fun n => integral_nonneg fun _ => norm_nonneg _)) hcomparison

/-- Genuine global sum--integral exchange on the shifted Abel line. -/
theorem tsum_integral_eq_integral_tsum_bblsAbelMellinEstermannTerm
    (phase : ℝ) {damping : ℝ} (hdamping : 0 < damping) :
    (∑' n : ℕ, ∫ t : ℝ,
      bblsAbelMellinEstermannTerm phase damping n t) =
      ∫ t : ℝ, ∑' n : ℕ,
        bblsAbelMellinEstermannTerm phase damping n t := by
  exact integral_tsum_of_summable_integral_norm
    (fun n => integrable_bblsAbelMellinEstermannTerm phase hdamping n)
    (summable_integral_norm_bblsAbelMellinEstermannTerm phase hdamping)

/-- Pointwise identification of the summed integrand with `D(1+w,phase)`. -/
theorem tsum_bblsAbelMellinEstermannTerm
    (phase damping t : ℝ) :
    (∑' n : ℕ, bblsAbelMellinEstermannTerm phase damping n t) =
      let w : ℂ := ((1 / 2 : ℝ) : ℂ) + t * Complex.I
      (damping : ℂ) ^ (-w) * Complex.Gamma w *
        bblsEstermannDirichletSeries phase (1 + w) := by
  unfold bblsAbelMellinEstermannTerm bblsEstermannDirichletSeries LSeries
  dsimp only
  rw [← tsum_mul_left]

/-- The assembled shifted Abel--Estermann contour is the sum of its
individually integrated rows. -/
theorem integral_bblsAbelEstermann_eq_tsum_integral_rows
    (phase : ℝ) {damping : ℝ} (hdamping : 0 < damping) :
    (∫ t : ℝ,
      let w : ℂ := ((1 / 2 : ℝ) : ℂ) + t * Complex.I
      (damping : ℂ) ^ (-w) * Complex.Gamma w *
        bblsEstermannDirichletSeries phase (1 + w)) =
      ∑' n : ℕ, ∫ t : ℝ,
        bblsAbelMellinEstermannTerm phase damping n t := by
  rw [tsum_integral_eq_integral_tsum_bblsAbelMellinEstermannTerm
    phase hdamping]
  apply integral_congr_ae
  filter_upwards [] with t
  exact (tsum_bblsAbelMellinEstermannTerm phase damping t).symm

/-- Termwise inverse-Mellin evaluation of one shifted Estermann row. -/
theorem integral_bblsAbelMellinEstermannTerm
    (phase : ℝ) {damping : ℝ} (hdamping : 0 < damping) (n : ℕ) :
    (∫ t : ℝ, bblsAbelMellinEstermannTerm phase damping n t) =
      (2 * Real.pi : ℝ) *
        (LSeries.term (bblsEstermannCoeff phase) 1 n *
          Real.exp (-(damping * n))) := by
  by_cases hn : n = 0
  · subst n
    simp [bblsAbelMellinEstermannTerm]
  · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hdn : 0 < damping * (n : ℝ) := mul_pos hdamping hnpos
    have hfun : (fun t : ℝ =>
        bblsAbelMellinEstermannTerm phase damping n t) =
      (fun t : ℝ => LSeries.term (bblsEstermannCoeff phase) 1 n *
        ((((damping * (n : ℝ) : ℝ) : ℂ) ^
            (-(((1 / 2 : ℝ) : ℂ) + t * Complex.I))) *
          Complex.Gamma (((1 / 2 : ℝ) : ℂ) + t * Complex.I))) := by
      funext t
      let w : ℂ := ((1 / 2 : ℝ) : ℂ) + t * Complex.I
      unfold bblsAbelMellinEstermannTerm
      dsimp only
      rw [bblsEstermannTerm_one_add phase n hn w]
      have hmul :
          (((damping * (n : ℝ) : ℝ) : ℂ) ^ (-w)) =
            (damping : ℂ) ^ (-w) * (n : ℂ) ^ (-w) := by
        rw [Complex.ofReal_mul,
          Complex.mul_cpow_ofReal_nonneg hdamping.le (Nat.cast_nonneg n)]
        norm_num
      rw [hmul]
      dsimp [w]
      ring
    rw [hfun, integral_const_mul, integral_Gamma_vertical_half hdn]
    norm_num
    ring

/-- Exponentially damped Estermann series at the BBLS boundary `s=1`. -/
noncomputable def bblsDampedEstermannAtOne
    (phase damping : ℝ) : ℂ :=
  ∑' n : ℕ, LSeries.term (bblsEstermannCoeff phase) 1 n *
    Real.exp (-(damping * n))

/-- The normalized Estermann coefficient at `s=1` is bounded by one. -/
theorem norm_bblsEstermannTerm_one_le_one (phase : ℝ) (n : ℕ) :
    ‖LSeries.term (bblsEstermannCoeff phase) 1 n‖ ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [LSeries.term_of_ne_zero hn, norm_div,
      norm_bblsEstermannCoeff, bblsEstermannDivisorCoeff_apply]
    simp only [Complex.norm_natCast]
    norm_num
    exact (div_le_one (by positivity)).mpr (by
      exact_mod_cast Nat.card_divisors_le_self n)

/-- Absolute summability of the damped Estermann boundary series. -/
theorem summable_bblsDampedEstermannAtOne
    (phase : ℝ) {damping : ℝ} (hdamping : 0 < damping) :
    Summable (fun n : ℕ => LSeries.term (bblsEstermannCoeff phase) 1 n *
      Real.exp (-(damping * n))) := by
  have hbase : Summable (fun n : ℕ => Real.exp (n * (-damping))) :=
    Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr hdamping)
  apply hbase.of_norm_bounded
  intro n
  rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [show -(damping * (n : ℝ)) = (n : ℝ) * (-damping) by ring]
  exact mul_le_of_le_one_left (Real.exp_nonneg _)
    (norm_bblsEstermannTerm_one_le_one phase n)

/-- The damped Estermann boundary value is exactly the BBLS
product-frequency Abel sum. -/
theorem bblsDampedEstermannAtOne_eq_productAbelSum
    (phase : ℝ) {damping : ℝ} (hdamping : 0 < damping) :
    bblsDampedEstermannAtOne phase damping =
      bblsProductAbelSum (Real.exp (-damping)) phase := by
  let f : ℕ → ℂ := fun n =>
    LSeries.term (bblsEstermannCoeff phase) 1 n *
      Real.exp (-(damping * n))
  have hsum : Summable f :=
    summable_bblsDampedEstermannAtOne phase hdamping
  have htail : bblsDampedEstermannAtOne phase damping =
      ∑' n : ℕ+, f (n : ℕ) := by
    unfold bblsDampedEstermannAtOne
    change (∑' n : ℕ, f n) = ∑' n : ℕ+, f (n : ℕ)
    rw [hsum.tsum_eq_zero_add, tsum_pnat_eq_tsum_succ]
    simp [f]
  rw [htail, bblsProductAbelSum_eq_estermannLambert
    damping phase hdamping]

/-- The full shifted vertical integral is exactly the damped Estermann
series at `s=1`, including the BBLS `1/n` normalization. -/
theorem bblsShiftedAbelMellinIdentity
    (phase : ℝ) {damping : ℝ} (hdamping : 0 < damping) :
    (∫ t : ℝ,
      let w : ℂ := ((1 / 2 : ℝ) : ℂ) + t * Complex.I
      (damping : ℂ) ^ (-w) * Complex.Gamma w *
        bblsEstermannDirichletSeries phase (1 + w)) =
      (2 * Real.pi : ℝ) * bblsDampedEstermannAtOne phase damping := by
  rw [integral_bblsAbelEstermann_eq_tsum_integral_rows phase hdamping]
  unfold bblsDampedEstermannAtOne
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  exact integral_bblsAbelMellinEstermannTerm phase hdamping n

/-- Final normalization check: the shifted Abel--Mellin contour recovers the
actual BBLS product-frequency Abel sum, not an unnormalized Lambert series. -/
theorem bblsShiftedAbelMellinIdentity_eq_productAbelSum
    (phase : ℝ) {damping : ℝ} (hdamping : 0 < damping) :
    (∫ t : ℝ,
      let w : ℂ := ((1 / 2 : ℝ) : ℂ) + t * Complex.I
      (damping : ℂ) ^ (-w) * Complex.Gamma w *
        bblsEstermannDirichletSeries phase (1 + w)) =
      (2 * Real.pi : ℝ) *
        bblsProductAbelSum (Real.exp (-damping)) phase := by
  rw [bblsShiftedAbelMellinIdentity phase hdamping,
    bblsDampedEstermannAtOne_eq_productAbelSum phase hdamping]

end NBMellinTools.NB12
