import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCGammaHalfLines
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannSeries

/-!
# Route C: the raw Abel--Mellin identity on the initial line

The Bettin--Conrey rational boundary argument starts from an exponentially
damped divisor Lambert series.  This module fixes the initial Mellin line at
`Re s = 3/2`, proves that Gamma is genuinely integrable there without Gaussian
damping, and develops the corresponding specialized inverse Mellin identity.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelMellin

open Complex MeasureTheory Set
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCGammaHalfLines
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannSeries

/-- Exact squared Gamma norm on the initial Abel contour `Re s = 3/2`. -/
theorem norm_Gamma_three_halves_add_I_mul_sq (t : ℝ) :
    ‖Complex.Gamma ((3 / 2 : ℝ) + Complex.I * t)‖ ^ 2 =
      ((1 / 2 : ℝ) ^ 2 + t ^ 2) *
        (Real.pi / Real.cosh (Real.pi * t)) := by
  let z : ℂ := (1 / 2 : ℝ) + Complex.I * t
  have hz : z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [z] at hre
  have hshift : z + 1 = (3 / 2 : ℝ) + Complex.I * t := by
    dsimp [z]
    push_cast
    ring
  have hrec := Complex.Gamma_add_one z hz
  rw [hshift] at hrec
  have hrecNorm := congrArg (fun w : ℂ ↦ ‖w‖ ^ 2) hrec
  change ‖Complex.Gamma ((3 / 2 : ℝ) + Complex.I * t)‖ ^ 2 =
    ‖z * Complex.Gamma z‖ ^ 2 at hrecNorm
  rw [norm_mul, mul_pow] at hrecNorm
  have hzNorm : ‖z‖ ^ 2 = (1 / 2 : ℝ) ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm]
    change Complex.normSq ((1 / 2 : ℝ) + Complex.I * t) = _
    rw [show ((1 / 2 : ℝ) + Complex.I * t : ℂ) =
        (((1 / 2 : ℝ) : ℝ) : ℂ) + t * Complex.I by
      push_cast
      ring]
    rw [Complex.normSq_add_mul_I]
  rw [hzNorm, norm_Gamma_half_add_I_mul_sq] at hrecNorm
  simpa [z] using hrecNorm

/-- The elementary exponential majorant used for the raw Gamma contour. -/
noncomputable def gammaThreeHalvesMajorant (t : ℝ) : ℝ :=
  Real.sqrt (2 * Real.pi) * (1 + |t|) *
    Real.exp (-(Real.pi / 2) * |t|)

/-- The standard exponential lower bound for the hyperbolic cosine. -/
theorem exp_abs_le_two_mul_cosh (x : ℝ) :
    Real.exp |x| ≤ 2 * Real.cosh x := by
  rw [Real.cosh_eq]
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    linarith [Real.exp_pos (-x)]
  · rw [abs_of_neg (lt_of_not_ge hx)]
    linarith [Real.exp_pos x]

/-- Intrinsic exponential decay of Gamma on `Re s = 3/2`. -/
theorem norm_Gamma_three_halves_add_I_mul_le_majorant (t : ℝ) :
    ‖Complex.Gamma ((3 / 2 : ℝ) + Complex.I * t)‖ ≤
      gammaThreeHalvesMajorant t := by
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
  have hquad : (1 / 2 : ℝ) ^ 2 + t ^ 2 ≤ (1 + |t|) ^ 2 := by
    have habs_nonneg : 0 ≤ |t| := abs_nonneg t
    nlinarith [sq_abs t]
  have hsquare :
      ‖Complex.Gamma ((3 / 2 : ℝ) + Complex.I * t)‖ ^ 2 ≤
        gammaThreeHalvesMajorant t ^ 2 := by
    rw [norm_Gamma_three_halves_add_I_mul_sq]
    unfold gammaThreeHalvesMajorant
    have hsqrt : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi := by
      rw [Real.sq_sqrt]
      positivity
    rw [mul_pow, mul_pow, hsqrt]
    rw [show Real.exp (-(Real.pi / 2) * |t|) ^ 2 =
        Real.exp (-(Real.pi * |t|)) by
      rw [← Real.exp_nat_mul]
      congr 1
      ring]
    calc
      ((1 / 2 : ℝ) ^ 2 + t ^ 2) *
          (Real.pi / Real.cosh (Real.pi * t)) ≤
        ((1 / 2 : ℝ) ^ 2 + t ^ 2) *
          (Real.pi * (2 * Real.exp (-(Real.pi * |t|)))) := by
            apply mul_le_mul_of_nonneg_left
            · exact mul_le_mul_of_nonneg_left
                (by simpa [one_div] using hinv) Real.pi_pos.le
            · positivity
      _ ≤ 2 * Real.pi * (1 + |t|) ^ 2 *
          Real.exp (-(Real.pi * |t|)) := by
            have hfactor : 0 ≤
                2 * Real.pi * Real.exp (-(Real.pi * |t|)) := by positivity
            have hmul := mul_le_mul_of_nonneg_right hquad hfactor
            convert hmul using 1 <;> ring
  have hmajorant : 0 ≤ gammaThreeHalvesMajorant t := by
    unfold gammaThreeHalvesMajorant
    positivity
  nlinarith [norm_nonneg (Complex.Gamma ((3 / 2 : ℝ) + Complex.I * t))]

set_option maxHeartbeats 800000 in
-- The two half-line `rpow * exp` conversions are elaboration-heavy.
/-- The explicit exponential majorant is integrable on the real line. -/
theorem integrable_gammaThreeHalvesMajorant :
    Integrable gammaThreeHalvesMajorant := by
  let a : ℝ := Real.pi / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hzero : IntegrableOn
      (fun x : ℝ ↦ x ^ (0 : ℝ) * Real.exp (-a * x ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) ha
  have hone : IntegrableOn
      (fun x : ℝ ↦ x ^ (1 : ℝ) * Real.exp (-a * x ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) ha
  have hpos : IntegrableOn
      (fun x : ℝ ↦ (1 + |x|) * Real.exp (-a * |x|)) (Ioi 0) := by
    refine (hzero.add hone).congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hx' : 0 < x := hx
    change x ^ (0 : ℝ) * Real.exp (-a * x ^ (1 : ℝ)) +
        x ^ (1 : ℝ) * Real.exp (-a * x ^ (1 : ℝ)) =
      (1 + |x|) * Real.exp (-a * |x|)
    rw [abs_of_pos hx']
    simp only [Real.rpow_zero, one_mul, Real.rpow_one]
    ring
  have hneg : IntegrableOn
      (fun x : ℝ ↦ (1 + |x|) * Real.exp (-a * |x|)) (Iio 0) := by
    rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
    simpa only [Function.comp_def, abs_neg, neg_preimage, neg_Iio, neg_zero] using hpos
  have hfull : Integrable
      (fun x : ℝ ↦ (1 + |x|) * Real.exp (-a * |x|)) := by
    rw [← integrableOn_univ, ← Iio_union_Ici, integrableOn_union]
    refine ⟨hneg, ?_⟩
    rwa [integrableOn_Ici_iff_integrableOn_Ioi]
  unfold gammaThreeHalvesMajorant
  convert hfull.const_mul (Real.sqrt (2 * Real.pi)) using 1
  ext t
  dsimp [a]
  ring

/-- Gamma is vertically integrable on the raw initial line `Re s = 3/2`. -/
theorem verticalIntegrable_Gamma_three_halves :
    Complex.VerticalIntegrable Complex.Gamma (3 / 2 : ℝ) := by
  apply Integrable.mono' integrable_gammaThreeHalvesMajorant
  · have hline : Continuous
        (fun t : ℝ ↦ Complex.Gamma ((3 / 2 : ℝ) + t * Complex.I)) := by
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
      norm_Gamma_three_halves_add_I_mul_le_majorant t

/-- The exponentially damped function whose Mellin transform is Gamma. -/
noncomputable def abelExponential (x : ℝ) : ℂ := Real.exp (-x)

/-- Euler's Gamma integral is exactly the Mellin transform of the Abel
exponential throughout its half-plane of absolute convergence. -/
theorem mellin_abelExponential_eq_Gamma {s : ℂ} (hs : 0 < s.re) :
    mellin abelExponential s = Complex.Gamma s := by
  unfold abelExponential
  rw [← Complex.GammaIntegral_eq_mellin]
  exact (Complex.Gamma_eq_integral hs).symm

/-- Absolute convergence of the Abel exponential on the initial line. -/
theorem mellinConvergent_abelExponential_three_halves :
    MellinConvergent abelExponential (3 / 2 : ℝ) := by
  rw [MellinConvergent]
  refine IntegrableOn.congr_fun
    (Complex.GammaIntegral_convergent (s := (3 / 2 : ℂ)) (by norm_num)) ?_
    measurableSet_Ioi
  intro x hx
  unfold abelExponential
  simp only [smul_eq_mul]
  norm_num
  exact mul_comm _ _

/-- The Mellin transform of the Abel exponential is vertically integrable on
the initial line, with no auxiliary Gaussian. -/
theorem verticalIntegrable_mellin_abelExponential_three_halves :
    Complex.VerticalIntegrable (mellin abelExponential) (3 / 2 : ℝ) := by
  apply verticalIntegrable_Gamma_three_halves.congr
  filter_upwards [] with t
  exact (mellin_abelExponential_eq_Gamma
    (s := ((3 / 2 : ℝ) : ℂ) + t * Complex.I) (by norm_num)).symm

/-- Specialized inverse Mellin theorem for the exponentially damped Abel
factor on the initial line `Re s = 3/2`. -/
theorem mellinInv_mellin_abelExponential_three_halves {x : ℝ} (hx : 0 < x) :
    mellinInv (3 / 2 : ℝ) (mellin abelExponential) x = Real.exp (-x) := by
  simpa [abelExponential] using
    mellinInv_mellin_eq (3 / 2 : ℝ) abelExponential hx
      mellinConvergent_abelExponential_three_halves
      verticalIntegrable_mellin_abelExponential_three_halves
      (Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp continuous_neg)).continuousAt

/-- Euler's Gamma function itself has the expected inverse Mellin transform
on the raw initial line. -/
theorem mellinInv_Gamma_three_halves {x : ℝ} (hx : 0 < x) :
    mellinInv (3 / 2 : ℝ) Complex.Gamma x = Real.exp (-x) := by
  calc
    mellinInv (3 / 2 : ℝ) Complex.Gamma x =
        mellinInv (3 / 2 : ℝ) (mellin abelExponential) x := by
      unfold mellinInv
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      rw [mellin_abelExponential_eq_Gamma
        (s := ((3 / 2 : ℝ) : ℂ) + t * Complex.I) (by norm_num)]
    _ = Real.exp (-x) := mellinInv_mellin_abelExponential_three_halves hx

/-- Raw vertical-integral form of inverse Mellin for the exponential. -/
theorem integral_Gamma_vertical_three_halves {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ,
      (x : ℂ) ^ (-(((3 / 2 : ℝ) : ℂ) + t * Complex.I)) *
        Complex.Gamma (((3 / 2 : ℝ) : ℂ) + t * Complex.I)) =
      (2 * Real.pi : ℝ) * Real.exp (-x) := by
  have h := mellinInv_Gamma_three_halves hx
  unfold mellinInv at h
  let J : ℂ := ∫ t : ℝ,
    (x : ℂ) ^ (-(((3 / 2 : ℝ) : ℂ) + t * Complex.I)) *
      Complex.Gamma (((3 / 2 : ℝ) : ℂ) + t * Complex.I)
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

/-! ## The Estermann divisor series under the Abel contour -/

/-- The `n`th summand of the inverse-Mellin Estermann integrand on the raw
line `Re s = 3/2`. -/
noncomputable def abelMellinEstermannTerm
    (a q : ℕ) (x : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  (x : ℂ) ^ (-(((3 / 2 : ℝ) : ℂ) + t * Complex.I)) *
    Complex.Gamma (((3 / 2 : ℝ) : ℂ) + t * Complex.I) *
    LSeries.term (estermannCoeff a q)
      (((3 / 2 : ℝ) : ℂ) + t * Complex.I) n

/-- On the initial line, the norm of an L-series term depends only on the
real part of the exponent. -/
theorem norm_estermannTerm_three_halves_add_I_mul
    (a q n : ℕ) (t : ℝ) :
    ‖LSeries.term (estermannCoeff a q)
      (((3 / 2 : ℝ) : ℂ) + t * Complex.I) n‖ =
      ‖LSeries.term (estermannCoeff a q) (3 / 2 : ℂ) n‖ := by
  simp only [LSeries.norm_term_eq]
  congr 2
  norm_num

/-- Uniform, summable-in-frequency majorization of each divisor-series row. -/
theorem norm_abelMellinEstermannTerm_le
    (a q : ℕ) {x : ℝ} (hx : 0 < x) (n : ℕ) (t : ℝ) :
    ‖abelMellinEstermannTerm a q x n t‖ ≤
      (x ^ (-(3 / 2 : ℝ)) *
          ‖LSeries.term (estermannCoeff a q) (3 / 2 : ℂ) n‖) *
        gammaThreeHalvesMajorant t := by
  unfold abelMellinEstermannTerm
  rw [norm_mul, norm_mul]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  rw [norm_estermannTerm_three_halves_add_I_mul]
  have hGamma : ‖Complex.Gamma
      (((3 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ≤
      gammaThreeHalvesMajorant t := by
    simpa [mul_comm] using norm_Gamma_three_halves_add_I_mul_le_majorant t
  have hxpow : 0 ≤ x ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hx.le _
  have hterm : 0 ≤ ‖LSeries.term (estermannCoeff a q) (3 / 2 : ℂ) n‖ :=
    norm_nonneg _
  norm_num
  have hmul :=
    mul_le_mul_of_nonneg_left hGamma (mul_nonneg hxpow hterm)
  convert hmul using 1 <;> (norm_num; ring)

/-- Each fixed divisor coefficient gives an integrable row on the initial
vertical line. -/
theorem integrable_abelMellinEstermannTerm
    (a q : ℕ) {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Integrable (abelMellinEstermannTerm a q x n) := by
  let c : ℝ := x ^ (-(3 / 2 : ℝ)) *
    ‖LSeries.term (estermannCoeff a q) (3 / 2 : ℂ) n‖
  have hmajorant : Integrable (fun t : ℝ ↦ c * gammaThreeHalvesMajorant t) :=
    integrable_gammaThreeHalvesMajorant.const_mul c
  apply Integrable.mono' hmajorant
  · have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    letI : NeZero (x : ℂ) := ⟨hx0⟩
    have hpow : Continuous (fun t : ℝ ↦
        (x : ℂ) ^ (-(((3 / 2 : ℝ) : ℂ) + t * Complex.I))) :=
      (continuous_const_cpow (x : ℂ)).comp (by fun_prop)
    have hGamma : Continuous (fun t : ℝ ↦
        Complex.Gamma (((3 / 2 : ℝ) : ℂ) + t * Complex.I)) := by
      rw [continuous_iff_continuousAt]
      intro t
      apply (Complex.continuousAt_Gamma _ ?_).comp (by fun_prop)
      intro k hk
      have hre := congrArg Complex.re hk
      norm_num at hre
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have hterm : Continuous (fun t : ℝ ↦
        LSeries.term (estermannCoeff a q)
          (((3 / 2 : ℝ) : ℂ) + t * Complex.I) n) := by
      by_cases hn : n = 0
      · subst n
        simpa only [LSeries.term_zero] using
          (continuous_const : Continuous (fun _ : ℝ ↦ (0 : ℂ)))
      · rw [show (fun t : ℝ ↦ LSeries.term (estermannCoeff a q)
            (((3 / 2 : ℝ) : ℂ) + t * Complex.I) n) =
          (fun t : ℝ ↦ estermannCoeff a q n /
            (n : ℂ) ^ (((3 / 2 : ℝ) : ℂ) + t * Complex.I)) by
            funext t
            rw [LSeries.term_of_ne_zero hn]]
        have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
        letI : NeZero (n : ℂ) := ⟨hn0⟩
        exact continuous_const.div
          ((continuous_const_cpow (n : ℂ)).comp (by fun_prop))
          (fun _ ↦ cpow_ne_zero_iff.mpr (Or.inl hn0))
    exact (hpow.mul hGamma |>.mul hterm).aestronglyMeasurable
  · filter_upwards [] with t
    exact norm_abelMellinEstermannTerm_le a q hx n t

/-- The rowwise `L¹` norms are summable.  This is the precise Tonelli/Fubini
input needed for the Abel--Estermann sum--integral exchange. -/
theorem summable_integral_norm_abelMellinEstermannTerm
    (a q : ℕ) {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ ↦
      ∫ t : ℝ, ‖abelMellinEstermannTerm a q x n t‖) := by
  have hs0 := estermannCoeff_summable a q (s := (3 / 2 : ℂ)) (by norm_num)
  rw [LSeriesSummable] at hs0
  have hs : Summable (fun n : ℕ ↦
      ‖LSeries.term (estermannCoeff a q) (3 / 2 : ℂ) n‖) := hs0.norm
  let M : ℝ := ∫ t : ℝ, gammaThreeHalvesMajorant t
  have hcomparison : ∀ n : ℕ,
      (∫ t : ℝ, ‖abelMellinEstermannTerm a q x n t‖) ≤
        (x ^ (-(3 / 2 : ℝ)) * M) *
          ‖LSeries.term (estermannCoeff a q) (3 / 2 : ℂ) n‖ := by
    intro n
    let c : ℝ := x ^ (-(3 / 2 : ℝ)) *
      ‖LSeries.term (estermannCoeff a q) (3 / 2 : ℂ) n‖
    have hrow := (integrable_abelMellinEstermannTerm a q hx n).norm
    have hmaj : Integrable (fun t : ℝ ↦ c * gammaThreeHalvesMajorant t) :=
      integrable_gammaThreeHalvesMajorant.const_mul c
    have hle : (∫ t : ℝ, ‖abelMellinEstermannTerm a q x n t‖) ≤
        ∫ t : ℝ, c * gammaThreeHalvesMajorant t := by
      apply integral_mono hrow hmaj
      intro t
      exact norm_abelMellinEstermannTerm_le a q hx n t
    rw [integral_const_mul] at hle
    dsimp [c, M] at hle ⊢
    calc
      (∫ t : ℝ, ‖abelMellinEstermannTerm a q x n t‖) ≤
          (x ^ (-(3 / 2 : ℝ)) *
            ‖LSeries.term (estermannCoeff a q) (3 / 2 : ℂ) n‖) *
            ∫ t : ℝ, gammaThreeHalvesMajorant t := hle
      _ = (x ^ (-(3 / 2 : ℝ)) *
            ∫ t : ℝ, gammaThreeHalvesMajorant t) *
            ‖LSeries.term (estermannCoeff a q) (3 / 2 : ℂ) n‖ := by ring
  exact ((hs.mul_left (x ^ (-(3 / 2 : ℝ)) * M)).of_nonneg_of_le
    (fun n ↦ integral_nonneg fun _ ↦ norm_nonneg _)) hcomparison

/-- Genuine global sum--integral exchange for the exponentially damped
Estermann series on `Re s = 3/2`. -/
theorem tsum_integral_eq_integral_tsum_abelMellinEstermannTerm
    (a q : ℕ) {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, ∫ t : ℝ, abelMellinEstermannTerm a q x n t) =
      ∫ t : ℝ, ∑' n : ℕ, abelMellinEstermannTerm a q x n t := by
  exact integral_tsum_of_summable_integral_norm
    (fun n ↦ integrable_abelMellinEstermannTerm a q hx n)
    (summable_integral_norm_abelMellinEstermannTerm a q hx)

/-- The pointwise divisor sum under the integral is the classical Estermann
Dirichlet series. -/
theorem tsum_abelMellinEstermannTerm
    (a q : ℕ) (x t : ℝ) :
    (∑' n : ℕ, abelMellinEstermannTerm a q x n t) =
      (x : ℂ) ^ (-(((3 / 2 : ℝ) : ℂ) + t * Complex.I)) *
        Complex.Gamma (((3 / 2 : ℝ) : ℂ) + t * Complex.I) *
        estermannDirichletSeries a q
          (((3 / 2 : ℝ) : ℂ) + t * Complex.I) := by
  unfold abelMellinEstermannTerm estermannDirichletSeries LSeries
  rw [← tsum_mul_left]

/-- The assembled Abel--Estermann contour equals the sum of its individually
integrated divisor rows.  This is uniform over the whole vertical line, not a
pointwise formal rearrangement. -/
theorem integral_abelEstermann_eq_tsum_integral_rows
    (a q : ℕ) {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ,
      (x : ℂ) ^ (-(((3 / 2 : ℝ) : ℂ) + t * Complex.I)) *
        Complex.Gamma (((3 / 2 : ℝ) : ℂ) + t * Complex.I) *
        estermannDirichletSeries a q
          (((3 / 2 : ℝ) : ℂ) + t * Complex.I)) =
      ∑' n : ℕ, ∫ t : ℝ, abelMellinEstermannTerm a q x n t := by
  rw [tsum_integral_eq_integral_tsum_abelMellinEstermannTerm a q hx]
  apply integral_congr_ae
  filter_upwards [] with t
  exact (tsum_abelMellinEstermannTerm a q x t).symm

/-- The exponentially damped Estermann divisor Lambert series. -/
noncomputable def dampedEstermannLambertSeries
    (a q : ℕ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, LSeries.term (estermannCoeff a q) 0 n *
    Real.exp (-(x * n))

/-- Termwise inverse Mellin evaluation of one damped Estermann row. -/
theorem integral_abelMellinEstermannTerm
    (a q : ℕ) {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (∫ t : ℝ, abelMellinEstermannTerm a q x n t) =
      (2 * Real.pi : ℝ) *
        (LSeries.term (estermannCoeff a q) 0 n * Real.exp (-(x * n))) := by
  by_cases hn : n = 0
  · subst n
    simp [abelMellinEstermannTerm]
  · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hxn : 0 < x * (n : ℝ) := mul_pos hx hnpos
    have hfun : (fun t : ℝ ↦ abelMellinEstermannTerm a q x n t) =
        (fun t : ℝ ↦ estermannCoeff a q n *
          (((x * (n : ℝ) : ℝ) : ℂ) ^
              (-(((3 / 2 : ℝ) : ℂ) + t * Complex.I)) *
            Complex.Gamma (((3 / 2 : ℝ) : ℂ) + t * Complex.I))) := by
      funext t
      unfold abelMellinEstermannTerm
      rw [LSeries.term_of_ne_zero hn]
      let s : ℂ := ((3 / 2 : ℝ) : ℂ) + t * Complex.I
      change (x : ℂ) ^ (-s) * Complex.Gamma s *
          (estermannCoeff a q n / (n : ℂ) ^ s) =
        estermannCoeff a q n *
          ((((x * (n : ℝ) : ℝ) : ℂ) ^ (-s)) * Complex.Gamma s)
      rw [div_eq_mul_inv, ← Complex.cpow_neg]
      have hmul : (((x * (n : ℝ) : ℝ) : ℂ) ^ (-s)) =
          (x : ℂ) ^ (-s) * (n : ℂ) ^ (-s) := by
        rw [Complex.ofReal_mul,
          Complex.mul_cpow_ofReal_nonneg hx.le (Nat.cast_nonneg n)]
        norm_num
      rw [hmul]
      ring
    rw [hfun, integral_const_mul,
      integral_Gamma_vertical_three_halves hxn]
    rw [LSeries.term_of_ne_zero hn]
    norm_num
    ring

/-- Absolute summability of the exponentially damped Estermann Lambert
series, obtained from the already proved rowwise `L¹` estimate. -/
theorem summable_dampedEstermannLambertSeries
    (a q : ℕ) {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ ↦ LSeries.term (estermannCoeff a q) 0 n *
      Real.exp (-(x * n))) := by
  have hnorm := summable_integral_norm_abelMellinEstermannTerm a q hx
  have hint : Summable (fun n : ℕ ↦
      ∫ t : ℝ, abelMellinEstermannTerm a q x n t) := by
    rw [← summable_norm_iff]
    exact hnorm.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (fun n ↦ norm_integral_le_integral_norm _)
  have hscaled : Summable (fun n : ℕ ↦
      ((2 * Real.pi : ℝ) : ℂ) *
        (LSeries.term (estermannCoeff a q) 0 n *
          Real.exp (-(x * n)))) := by
    exact hint.congr fun n ↦ integral_abelMellinEstermannTerm a q hx n
  have h2pi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  simpa only [inv_mul_cancel_left₀ h2pi] using
    hscaled.mul_left (((2 * Real.pi : ℝ) : ℂ)⁻¹)

/-- The full raw vertical integral is exactly `2π` times the exponentially
damped Estermann Lambert series. -/
theorem abelEstermannMellinIdentity
    (a q : ℕ) {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ,
      (x : ℂ) ^ (-(((3 / 2 : ℝ) : ℂ) + t * Complex.I)) *
        Complex.Gamma (((3 / 2 : ℝ) : ℂ) + t * Complex.I) *
        estermannDirichletSeries a q
          (((3 / 2 : ℝ) : ℂ) + t * Complex.I)) =
      (2 * Real.pi : ℝ) * dampedEstermannLambertSeries a q x := by
  rw [integral_abelEstermann_eq_tsum_integral_rows a q hx]
  unfold dampedEstermannLambertSeries
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  exact integral_abelMellinEstermannTerm a q hx n

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelMellin
