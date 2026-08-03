import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Route C: integrability of the deformed saddle

This file proves that Bettin--Conrey's nonzero-`A` saddle integral is a genuine
Bochner integral whenever `n + alpha > 0`.  The key domination is

`‖A‖ * sqrt u ≤ u / 2 + ‖A‖^2 / 2`,

which converts the complex square-root perturbation into an integrable Gamma
majorant with exponential rate `1/2`.  This is the first analytic prerequisite
for central-window localization and steepest descent.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleIntegrability

open MeasureTheory Set
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleIntegral

/-- A Gamma-type majorant for the deformed saddle integrand. -/
noncomputable def routeCSaddleIntegrabilityMajorant
    (A : ℂ) (alpha : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  Real.exp (‖A‖ ^ 2 / 2) *
    (Real.rpow u ((n : ℝ) + alpha - 1) * Real.exp (-((1 / 2 : ℝ) * u)))

theorem norm_mul_sqrt_le_half_add_half_sq (A : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖A‖ * Real.sqrt u ≤ u / 2 + ‖A‖ ^ 2 / 2 := by
  have hsqrt_sq : (Real.sqrt u) ^ 2 = u := Real.sq_sqrt hu
  nlinarith [sq_nonneg (Real.sqrt u - ‖A‖)]

theorem norm_exp_neg_mul_sqrt_le (A : ℂ) (u : ℝ) :
    ‖Complex.exp (-A * (Real.sqrt u : ℂ))‖ ≤
      Real.exp (‖A‖ * Real.sqrt u) := by
  calc
    ‖Complex.exp (-A * (Real.sqrt u : ℂ))‖
        ≤ Real.exp ‖-A * (Real.sqrt u : ℂ)‖ :=
          Complex.norm_exp_le_exp_norm _
    _ = Real.exp (‖A‖ * Real.sqrt u) := by
      rw [norm_mul, norm_neg, Complex.norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg u)]

theorem norm_routeCSaddleIntegrand_le_majorant
    (A : ℂ) (alpha : ℝ) (n : ℕ) {u : ℝ} (hu : 0 < u) :
    ‖((Real.rpow u ((n : ℝ) + alpha - 1) * Real.exp (-u) : ℝ) : ℂ) *
        Complex.exp (-A * (Real.sqrt u : ℂ))‖ ≤
      routeCSaddleIntegrabilityMajorant A alpha n u := by
  have hu0 : 0 ≤ u := hu.le
  have hbase :
      0 ≤ Real.rpow u ((n : ℝ) + alpha - 1) * Real.exp (-u) :=
    mul_nonneg (Real.rpow_nonneg hu0 _) (Real.exp_nonneg _)
  have hpert := norm_exp_neg_mul_sqrt_le A u
  have hyoung := norm_mul_sqrt_le_half_add_half_sq A hu0
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hbase]
  calc
    (Real.rpow u ((n : ℝ) + alpha - 1) * Real.exp (-u)) *
        ‖Complex.exp (-A * (Real.sqrt u : ℂ))‖
        ≤ (Real.rpow u ((n : ℝ) + alpha - 1) * Real.exp (-u)) *
            Real.exp (‖A‖ * Real.sqrt u) :=
          mul_le_mul_of_nonneg_left hpert hbase
    _ = Real.rpow u ((n : ℝ) + alpha - 1) *
          Real.exp (-u + ‖A‖ * Real.sqrt u) := by
        rw [Real.exp_add]
        ring
    _ ≤ Real.rpow u ((n : ℝ) + alpha - 1) *
          Real.exp (-(1 / 2 : ℝ) * u + ‖A‖ ^ 2 / 2) := by
        apply mul_le_mul_of_nonneg_left
        · apply Real.exp_le_exp.mpr
          linarith
        · exact Real.rpow_nonneg hu0 _
    _ = routeCSaddleIntegrabilityMajorant A alpha n u := by
        unfold routeCSaddleIntegrabilityMajorant
        rw [Real.exp_add]
        ring

theorem integrableOn_routeCSaddleIntegrabilityMajorant
    (A : ℂ) (alpha : ℝ) (n : ℕ)
    (hpos : 0 < (n : ℝ) + alpha) :
    IntegrableOn (routeCSaddleIntegrabilityMajorant A alpha n) (Ioi 0) := by
  have hbase : IntegrableOn
      (fun u : ℝ =>
        Real.rpow u ((n : ℝ) + alpha - 1) *
          Real.exp (-(1 / 2 : ℝ) * Real.rpow u (1 : ℝ)))
      (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (n : ℝ) + alpha - 1) (b := (1 / 2 : ℝ))
      (by linarith) (by norm_num) (by norm_num)
  have hbase' : IntegrableOn
      (fun u : ℝ =>
        Real.rpow u ((n : ℝ) + alpha - 1) *
          Real.exp (-((1 / 2 : ℝ) * u)))
      (Ioi 0) := by
    convert hbase using 1
    ext u
    have hu1 : Real.rpow u (1 : ℝ) = u := Real.rpow_one u
    rw [hu1]
    congr 1
    ring
  exact hbase'.const_mul (Real.exp (‖A‖ ^ 2 / 2))

/-- The Gamma majorant has an exact closed form. -/
theorem integral_routeCSaddleIntegrabilityMajorant
    (A : ℂ) (alpha : ℝ) (n : ℕ)
    (hpos : 0 < (n : ℝ) + alpha) :
    ∫ u : ℝ in Ioi 0, routeCSaddleIntegrabilityMajorant A alpha n u =
      Real.exp (‖A‖ ^ 2 / 2) *
        (Real.rpow 2 ((n : ℝ) + alpha) *
          Real.Gamma ((n : ℝ) + alpha)) := by
  unfold routeCSaddleIntegrabilityMajorant
  rw [integral_const_mul]
  have hinner :
      (∫ u : ℝ in Ioi 0,
        Real.rpow u ((n : ℝ) + alpha - 1) *
          Real.exp (-((1 / 2 : ℝ) * u))) =
        Real.rpow (1 / (1 / 2 : ℝ)) ((n : ℝ) + alpha) *
          Real.Gamma ((n : ℝ) + alpha) := by
    exact Real.integral_rpow_mul_exp_neg_mul_Ioi
      hpos (by norm_num : (0 : ℝ) < 1 / 2)
  rw [hinner]
  norm_num

private theorem continuousOn_routeCSaddleIntegrand
    (A : ℂ) (alpha : ℝ) (n : ℕ) :
    ContinuousOn
      (fun u : ℝ =>
        ((Real.rpow u ((n : ℝ) + alpha - 1) * Real.exp (-u) : ℝ) : ℂ) *
          Complex.exp (-A * (Real.sqrt u : ℂ)))
      (Ioi 0) := by
  have hrpow : ContinuousOn
      (fun u : ℝ => Real.rpow u ((n : ℝ) + alpha - 1)) (Ioi 0) :=
    continuousOn_id.rpow_const fun u hu => Or.inl (ne_of_gt hu)
  have hbase : ContinuousOn
      (fun u : ℝ => Real.rpow u ((n : ℝ) + alpha - 1) * Real.exp (-u))
      (Ioi 0) :=
    hrpow.mul ((Real.continuous_exp.comp continuous_neg).continuousOn)
  have hbaseC : ContinuousOn
      (fun u : ℝ =>
        ((Real.rpow u ((n : ℝ) + alpha - 1) * Real.exp (-u) : ℝ) : ℂ))
      (Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn hbase
  have hpert : Continuous
      (fun u : ℝ => Complex.exp (-A * (Real.sqrt u : ℂ))) := by
    fun_prop
  exact hbaseC.mul hpert.continuousOn

/-- The deformed saddle integrand is Bochner integrable on the positive
half-line for every fixed complex `A` once the Gamma exponent is positive. -/
theorem integrableOn_routeCSaddleIntegrand
    (A : ℂ) (alpha : ℝ) (n : ℕ)
    (hpos : 0 < (n : ℝ) + alpha) :
    IntegrableOn
      (fun u : ℝ =>
        ((Real.rpow u ((n : ℝ) + alpha - 1) * Real.exp (-u) : ℝ) : ℂ) *
          Complex.exp (-A * (Real.sqrt u : ℂ)))
      (Ioi 0) := by
  apply Integrable.mono'
    (integrableOn_routeCSaddleIntegrabilityMajorant A alpha n hpos)
  · exact (continuousOn_routeCSaddleIntegrand A alpha n).aestronglyMeasurable
      measurableSet_Ioi
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    exact norm_routeCSaddleIntegrand_le_majorant A alpha n hu

/-- A global quantitative bound for the deformed saddle.  It is deliberately
crude—the sharp root-exponential asymptotic requires localization near
`u = n`—but it makes all later truncation and dominated-convergence arguments
legitimate. -/
theorem norm_routeCSaddleIntegral_le_gammaMajorant
    (A : ℂ) (alpha : ℝ) (n : ℕ)
    (hpos : 0 < (n : ℝ) + alpha) :
    ‖routeCSaddleIntegral A alpha n‖ ≤
      Real.exp (‖A‖ ^ 2 / 2) *
        (Real.rpow 2 ((n : ℝ) + alpha) *
          Real.Gamma ((n : ℝ) + alpha)) := by
  unfold routeCSaddleIntegral
  calc
    ‖∫ u : ℝ in Ioi 0,
        ((Real.rpow u ((n : ℝ) + alpha - 1) * Real.exp (-u) : ℝ) : ℂ) *
          Complex.exp (-A * (Real.sqrt u : ℂ))‖
        ≤ ∫ u : ℝ in Ioi 0,
            routeCSaddleIntegrabilityMajorant A alpha n u := by
          apply norm_integral_le_of_norm_le
            (integrableOn_routeCSaddleIntegrabilityMajorant A alpha n hpos)
          filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
          exact norm_routeCSaddleIntegrand_le_majorant A alpha n hu
    _ = Real.exp (‖A‖ ^ 2 / 2) *
          (Real.rpow 2 ((n : ℝ) + alpha) *
            Real.Gamma ((n : ℝ) + alpha)) :=
      integral_routeCSaddleIntegrabilityMajorant A alpha n hpos

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleIntegrability
