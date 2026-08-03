import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleFarLimit

/-!
# Route C: root-exponential absorption and the full far-tail target

The factorial compression supplies a strict geometric factor after division
by the real principal saddle scale.  The full complex normalization also
contains `exp (-A * sqrt n)`.  This module spends half of the logarithmic
geometric gap in a Young inequality to absorb that subexponential factor.

It then computes the squared norm of the complete complex normalizer and
proves `RouteCSaddleFarTailTarget A 1 delta` for every `0 < delta < 1`.
Thus the central Bettin--Conrey far sector is closed unconditionally; the
remaining saddle-analysis target is the near-sector Gaussian limit.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleRootAbsorption

open Filter
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleCentralWindow
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleWeightedFar
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleFarOptimization
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleFarLimit

theorem linear_mul_exp_neg_nat_mul_tendsto_zero
    {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n : ℕ => (n + 1 : ℝ) * Real.exp (-r * (n : ℝ)))
      atTop (nhds 0) := by
  have hlinear :=
    (Real.summable_pow_mul_exp_neg_nat_mul 1 hr).tendsto_atTop_zero
  have hconstant :=
    (Real.summable_pow_mul_exp_neg_nat_mul 0 hr).tendsto_atTop_zero
  simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, pow_one,
    pow_zero, one_mul, zero_add] using hlinear.add hconstant

theorem linear_mul_geometric_exp_re_sqrt_tendsto_zero
    (A : ℂ) {rho : ℝ} (hrho0 : 0 < rho) (hrho1 : rho < 1) :
    Tendsto (fun n : ℕ =>
      (n + 1 : ℝ) * rho ^ n *
        Real.exp (2 * A.re * Real.sqrt (n : ℝ)))
      atTop (nhds 0) := by
  let r := -Real.log rho
  let epsilon := r / 2
  let C := ‖(2 : ℂ) * A‖ ^ 2 / (4 * epsilon)
  have hr : 0 < r := neg_pos.mpr (Real.log_neg hrho0 hrho1)
  have hepsilon : 0 < epsilon := div_pos hr (by norm_num)
  have hdecay : Tendsto (fun n : ℕ =>
      Real.exp C * ((n + 1 : ℝ) *
        Real.exp (-epsilon * (n : ℝ)))) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (linear_mul_exp_neg_nat_mul_tendsto_zero hepsilon).const_mul
        (Real.exp C)
  apply squeeze_zero'
    (g := fun n : ℕ =>
      Real.exp C * ((n + 1 : ℝ) * Real.exp (-epsilon * (n : ℝ))))
  · filter_upwards with n
    positivity
  · filter_upwards with n
    have hre : 2 * A.re ≤ ‖(2 : ℂ) * A‖ := by
      rw [norm_mul]
      norm_num
      nlinarith [le_trans (le_abs_self A.re) (Complex.abs_re_le_norm A)]
    have hsqrt : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    have hroot : 2 * A.re * Real.sqrt (n : ℝ) ≤
        epsilon * (n : ℝ) + C := by
      exact (mul_le_mul_of_nonneg_right hre hsqrt).trans
        (norm_mul_sqrt_le_epsilon_add_sq_div ((2 : ℂ) * A)
          hepsilon (Nat.cast_nonneg n))
    have hrhopow : rho ^ n = Real.exp (-r * (n : ℝ)) := by
      rw [show -r * (n : ℝ) = Real.log rho * (n : ℝ) by
        dsimp [r]
        ring]
      rw [mul_comm (Real.log rho) (n : ℝ), Real.exp_nat_mul,
        Real.exp_log hrho0]
    rw [hrhopow]
    calc
      (n + 1 : ℝ) * Real.exp (-r * (n : ℝ)) *
          Real.exp (2 * A.re * Real.sqrt (n : ℝ))
        = (n + 1 : ℝ) * Real.exp
            (-r * (n : ℝ) + 2 * A.re * Real.sqrt (n : ℝ)) := by
              rw [Real.exp_add]
              ring
      _ ≤ (n + 1 : ℝ) * Real.exp (-epsilon * (n : ℝ) + C) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        dsimp [epsilon] at hroot ⊢
        nlinarith
      _ = Real.exp C * ((n + 1 : ℝ) *
            Real.exp (-epsilon * (n : ℝ))) := by
        rw [Real.exp_add]
        ring
  · exact hdecay

noncomputable def routeCSaddleComplexNormalizerOne
    (A : ℂ) (n : ℕ) : ℂ :=
  (Real.sqrt (2 * Real.pi) : ℂ) * Complex.exp (A ^ 2 / 8) *
    Complex.exp (-A * (Real.sqrt n : ℂ)) *
      Complex.exp (-(n : ℝ)) *
        ((Real.rpow n ((n : ℝ) + 1 / 2) : ℝ) : ℂ)

noncomputable def routeCSaddleComplexFixedNormSq (A : ℂ) : ℝ :=
  2 * Real.pi * Real.exp (2 * (A ^ 2 / 8).re)

theorem routeCSaddleComplexFixedNormSq_pos (A : ℂ) :
    0 < routeCSaddleComplexFixedNormSq A := by
  unfold routeCSaddleComplexFixedNormSq
  positivity

theorem norm_routeCSaddleComplexNormalizerOne_sq
    (A : ℂ) (n : ℕ) :
    ‖routeCSaddleComplexNormalizerOne A n‖ ^ 2 =
      routeCSaddleComplexFixedNormSq A *
        Real.exp (-2 * A.re * Real.sqrt (n : ℝ)) *
          routeCSaddlePrincipalScaleOne n ^ 2 := by
  unfold routeCSaddleComplexNormalizerOne
    routeCSaddleComplexFixedNormSq routeCSaddlePrincipalScaleOne
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, neg_mul]
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [show |Real.rpow (n : ℝ) ((n : ℝ) + 1 / 2)| =
      Real.rpow (n : ℝ) ((n : ℝ) + 1 / 2) by
        exact abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  rw [pow_two, pow_two]
  have hsqrt : Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) =
      2 * Real.pi := Real.mul_self_sqrt (by positivity)
  have hA : Real.exp (A * A / 8).re * Real.exp (A * A / 8).re =
      Real.exp (2 * (A * A / 8).re) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hroot : Real.exp (-(A.re * Real.sqrt (n : ℝ))) *
      Real.exp (-(A.re * Real.sqrt (n : ℝ))) =
      Real.exp (-2 * A.re * Real.sqrt (n : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
  calc
    Real.sqrt (2 * Real.pi) * Real.exp (A * A / 8).re *
          Real.exp (-(A.re * Real.sqrt (n : ℝ))) * Real.exp (-(n : ℝ)) *
          Real.rpow (n : ℝ) ((n : ℝ) + 1 / 2) *
        (Real.sqrt (2 * Real.pi) * Real.exp (A * A / 8).re *
          Real.exp (-(A.re * Real.sqrt (n : ℝ))) * Real.exp (-(n : ℝ)) *
          Real.rpow (n : ℝ) ((n : ℝ) + 1 / 2)) =
        (Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi)) *
          (Real.exp (A * A / 8).re * Real.exp (A * A / 8).re) *
          (Real.exp (-(A.re * Real.sqrt (n : ℝ))) *
            Real.exp (-(A.re * Real.sqrt (n : ℝ)))) *
          (Real.exp (-(n : ℝ)) *
            Real.rpow (n : ℝ) ((n : ℝ) + 1 / 2)) ^ 2 := by ring
    _ = 2 * Real.pi * Real.exp (2 * (A * A / 8).re) *
        Real.exp (-2 * A.re * Real.sqrt (n : ℝ)) *
          (Real.exp (-(n : ℝ)) *
            Real.rpow (n : ℝ) ((n : ℝ) + 1 / 2)) ^ 2 := by
      rw [hsqrt, hA, hroot]
    _ = 2 * Real.pi * Real.exp (2 * (A * A / 8).re) *
        Real.exp (-(2 * A.re * Real.sqrt (n : ℝ))) *
          (Real.exp (-(n : ℝ)) *
            Real.rpow (n : ℝ) ((n : ℝ) + 1 / 2)) ^ 2 := by
      congr 2
      ring

theorem norm_routeCSaddleFarIntegral_one_sq_normalized_le
    (A : ℂ) {delta : ℝ} (hd0 : 0 < delta) (hd1 : delta < 1)
    (n : ℕ) (hn : 2 ≤ n) :
    ‖routeCSaddleFarIntegral A 1 delta n‖ ^ 2 /
        routeCSaddlePrincipalScaleOne n ^ 2 ≤
      (routeCSaddleHalfNormalizationConstant A delta *
          Stirling.stirlingSeq 1 * Real.exp 2) *
        ((n + 1 : ℝ) * routeCSaddleHalfGeometricBase delta ^ n) := by
  calc
    ‖routeCSaddleFarIntegral A 1 delta n‖ ^ 2 /
          routeCSaddlePrincipalScaleOne n ^ 2 ≤
        (routeCSaddleHalfGammaPrefactor A delta
              (routeCSaddleHalfEntropyEpsilon delta) n ^ 2 *
            (((n + 1).factorial : ℝ) *
              Real.rpow 2 (-((n : ℝ) + 1)) * Real.sqrt Real.pi)) /
          routeCSaddlePrincipalScaleOne n ^ 2 :=
      div_le_div_of_nonneg_right
        (norm_routeCSaddleFarIntegral_one_sq_le_factorial A delta
          (routeCSaddleHalfEntropyEpsilon delta) n hn hd0 hd1
          (routeCSaddleHalfEntropyEpsilon_pos hd0 hd1)
          (routeCSaddleHalfEntropyEpsilon_lt_half hd0 hd1))
        (sq_nonneg _)
    _ = routeCSaddleHalfNormalizationConstant A delta *
          (Real.exp (n : ℝ) * ((n + 1).factorial : ℝ) /
            Real.rpow n ((n : ℝ) + 1)) *
          routeCSaddleHalfGeometricBase delta ^ n :=
      factorial_majorant_normalized_eq A delta n (by omega) hd0 hd1
    _ ≤ (routeCSaddleHalfNormalizationConstant A delta *
          Stirling.stirlingSeq 1 * Real.exp 2) *
        ((n + 1 : ℝ) * routeCSaddleHalfGeometricBase delta ^ n) := by
      have hscaled := factorial_scaled_le_linear n (by omega)
      have hconstant : 0 ≤ routeCSaddleHalfNormalizationConstant A delta := by
        unfold routeCSaddleHalfNormalizationConstant
        positivity
      have hrho : 0 ≤ routeCSaddleHalfGeometricBase delta ^ n :=
        pow_nonneg (routeCSaddleHalfGeometricBase_pos hd0 hd1).le _
      calc
        routeCSaddleHalfNormalizationConstant A delta *
              (Real.exp (n : ℝ) * ((n + 1).factorial : ℝ) /
                Real.rpow n ((n : ℝ) + 1)) *
              routeCSaddleHalfGeometricBase delta ^ n ≤
            routeCSaddleHalfNormalizationConstant A delta *
              (Stirling.stirlingSeq 1 * Real.exp 2 * (n + 1 : ℝ)) *
              routeCSaddleHalfGeometricBase delta ^ n :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hscaled hconstant) hrho
        _ = _ := by ring

theorem norm_far_div_complexNormalizer_sq_eq
    (A : ℂ) (delta : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ‖routeCSaddleFarIntegral A 1 delta n /
        routeCSaddleComplexNormalizerOne A n‖ ^ 2 =
      (‖routeCSaddleFarIntegral A 1 delta n‖ ^ 2 /
          routeCSaddlePrincipalScaleOne n ^ 2) *
        Real.exp (2 * A.re * Real.sqrt (n : ℝ)) /
          routeCSaddleComplexFixedNormSq A := by
  have hscale : 0 < routeCSaddlePrincipalScaleOne n := by
    unfold routeCSaddlePrincipalScaleOne
    exact mul_pos (Real.exp_pos _)
      (Real.rpow_pos_of_pos (by positivity) _)
  have hK := routeCSaddleComplexFixedNormSq_pos A
  rw [norm_div, div_pow, norm_routeCSaddleComplexNormalizerOne_sq]
  have hexp : Real.exp (-2 * A.re * Real.sqrt (n : ℝ)) =
      (Real.exp (2 * A.re * Real.sqrt (n : ℝ)))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [hexp]
  field_simp

theorem norm_far_div_complexNormalizer_sq_tendsto_zero
    (A : ℂ) {delta : ℝ} (hd0 : 0 < delta) (hd1 : delta < 1) :
    Tendsto (fun n : ℕ =>
      ‖routeCSaddleFarIntegral A 1 delta n /
        routeCSaddleComplexNormalizerOne A n‖ ^ 2)
      atTop (nhds 0) := by
  let C := (routeCSaddleHalfNormalizationConstant A delta *
      Stirling.stirlingSeq 1 * Real.exp 2) /
    routeCSaddleComplexFixedNormSq A
  have hupper : Tendsto (fun n : ℕ =>
      C * ((n + 1 : ℝ) * routeCSaddleHalfGeometricBase delta ^ n *
        Real.exp (2 * A.re * Real.sqrt (n : ℝ))))
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      (linear_mul_geometric_exp_re_sqrt_tendsto_zero A
        (routeCSaddleHalfGeometricBase_pos hd0 hd1)
        (routeCSaddleHalfGeometricBase_lt_one hd0 hd1)).const_mul C
  apply squeeze_zero'
    (g := fun n : ℕ =>
      C * ((n + 1 : ℝ) * routeCSaddleHalfGeometricBase delta ^ n *
        Real.exp (2 * A.re * Real.sqrt (n : ℝ))))
  · filter_upwards with n
    exact sq_nonneg _
  · filter_upwards [eventually_atTop.2 ⟨2, fun _ hn => hn⟩] with n hn
    rw [norm_far_div_complexNormalizer_sq_eq A delta n (by omega)]
    have hreal := norm_routeCSaddleFarIntegral_one_sq_normalized_le
      A hd0 hd1 n hn
    have hK := routeCSaddleComplexFixedNormSq_pos A
    have hexp : 0 ≤ Real.exp (2 * A.re * Real.sqrt (n : ℝ)) :=
      (Real.exp_pos _).le
    calc
      (‖routeCSaddleFarIntegral A 1 delta n‖ ^ 2 /
            routeCSaddlePrincipalScaleOne n ^ 2) *
          Real.exp (2 * A.re * Real.sqrt (n : ℝ)) /
            routeCSaddleComplexFixedNormSq A ≤
        ((routeCSaddleHalfNormalizationConstant A delta *
              Stirling.stirlingSeq 1 * Real.exp 2) *
            ((n + 1 : ℝ) * routeCSaddleHalfGeometricBase delta ^ n)) *
          Real.exp (2 * A.re * Real.sqrt (n : ℝ)) /
            routeCSaddleComplexFixedNormSq A :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hreal hexp) hK.le
      _ = C * ((n + 1 : ℝ) *
          routeCSaddleHalfGeometricBase delta ^ n *
            Real.exp (2 * A.re * Real.sqrt (n : ℝ))) := by
        dsimp [C]
        ring
  · exact hupper

theorem far_div_complexNormalizer_tendsto_zero
    (A : ℂ) {delta : ℝ} (hd0 : 0 < delta) (hd1 : delta < 1) :
    Tendsto (fun n : ℕ =>
      routeCSaddleFarIntegral A 1 delta n /
        routeCSaddleComplexNormalizerOne A n)
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hsqrt :=
    (norm_far_div_complexNormalizer_sq_tendsto_zero A hd0 hd1).sqrt
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt

theorem routeCSaddleFarTailTarget_one
    (A : ℂ) {delta : ℝ} (hd0 : 0 < delta) (hd1 : delta < 1) :
    RouteCSaddleFarTailTarget A 1 delta := by
  refine ⟨hd0, hd1, ?_⟩
  convert far_div_complexNormalizer_tendsto_zero A hd0 hd1 using 1
  ext n
  unfold routeCSaddleComplexNormalizerOne
  congr 4
  ring

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleRootAbsorption
