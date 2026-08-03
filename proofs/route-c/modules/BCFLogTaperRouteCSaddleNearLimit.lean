import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleNearRescaling
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Route C: dominated near-saddle limit and complete saddle asymptotic

The expanding central window is represented by a measurable cutoff profile.
The explicit Gaussian majorant from the rescaling module permits dominated
convergence, while the complex moment-generating function of the standard
Gaussian evaluates the limiting integral exactly as `1`.  Combining this
near contribution with the previously proved normalized far-tail decay gives
the complete normalized Bettin--Conrey saddle integral asymptotic.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleNearLimit

open Filter MeasureTheory Set
open ProbabilityTheory
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleIntegral
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleCentralWindow
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleRootAbsorption
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleNearPointwise
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleNearRescaling

theorem measurable_routeCSaddleScaledEntropy (n : ℕ) :
    Measurable (fun t : ℝ => routeCSaddleScaledEntropy t n) := by
  unfold routeCSaddleScaledEntropy
  fun_prop

theorem measurable_routeCSaddleScaledRootShift (n : ℕ) :
    Measurable (fun t : ℝ => routeCSaddleScaledRootShift t n) := by
  unfold routeCSaddleScaledRootShift
  fun_prop

theorem measurable_routeCSaddleNearNormalizedProfile (A : ℂ) (n : ℕ) :
    Measurable (fun t : ℝ => routeCSaddleNearNormalizedProfile A t n) := by
  have he : Measurable (fun t : ℝ =>
      (routeCSaddleScaledEntropy t n : ℂ)) :=
    Complex.measurable_ofReal.comp (measurable_routeCSaddleScaledEntropy n)
  have hr : Measurable (fun t : ℝ =>
      (routeCSaddleScaledRootShift t n : ℂ)) :=
    Complex.measurable_ofReal.comp (measurable_routeCSaddleScaledRootShift n)
  unfold routeCSaddleNearNormalizedProfile routeCSaddleNearPhase
  exact (measurable_const.mul measurable_const).mul
    (Complex.measurable_exp.comp (he.sub (measurable_const.mul hr)))

noncomputable def routeCSaddleNearWindowProfile
    (A : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  (Icc (-Real.sqrt ((n + 1 : ℕ) : ℝ) / 8)
      (Real.sqrt ((n + 1 : ℕ) : ℝ) / 8)).indicator
    (fun x => routeCSaddleNearNormalizedProfile A x (n + 1)) t

theorem aestronglyMeasurable_routeCSaddleNearWindowProfile
    (A : ℂ) (n : ℕ) :
    AEStronglyMeasurable (routeCSaddleNearWindowProfile A n) := by
  apply Measurable.aestronglyMeasurable
  unfold routeCSaddleNearWindowProfile
  exact (measurable_routeCSaddleNearNormalizedProfile A (n + 1)).indicator
    measurableSet_Icc

theorem norm_routeCSaddleNearWindowProfile_le_majorant
    (A : ℂ) (n : ℕ) (t : ℝ) :
    ‖routeCSaddleNearWindowProfile A n t‖ ≤
      routeCSaddleNearGaussianMajorant A t := by
  let s := Real.sqrt ((n + 1 : ℕ) : ℝ)
  by_cases ht : t ∈ Icc (-s / 8) (s / 8)
  · have habs : |t| ≤ s / 8 := abs_le.2 ⟨by linarith [ht.1], ht.2⟩
    rw [routeCSaddleNearWindowProfile, Set.indicator_of_mem]
    · exact norm_routeCSaddleNearNormalizedProfile_le_majorant
        A t (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
          (by simpa only [s] using habs)
    · simpa only [s] using ht
  · have ht' : t ∉ Icc
        (-Real.sqrt ((n + 1 : ℕ) : ℝ) / 8)
        (Real.sqrt ((n + 1 : ℕ) : ℝ) / 8) := by
      simpa only [s] using ht
    simp only [routeCSaddleNearWindowProfile, Set.indicator, ht',
      ↓reduceIte, norm_zero]
    unfold routeCSaddleNearGaussianMajorant
    exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

theorem routeCSaddleNearWindowProfile_tendsto
    (A : ℂ) (t : ℝ) :
    Tendsto (fun n : ℕ => routeCSaddleNearWindowProfile A n t) atTop
      (nhds (routeCSaddleGaussianProfile A t)) := by
  have hnat : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hwindow : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) / 8) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp hnat).atTop_div_const (by norm_num)
  have hevent : ∀ᶠ n : ℕ in atTop,
      |t| ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) / 8 :=
    tendsto_atTop.1 hwindow |t|
  have hprofile := (routeCSaddleNearNormalizedProfile_tendsto A t).comp
    (tendsto_add_atTop_nat 1)
  apply hprofile.congr'
  filter_upwards [hevent] with n hn
  unfold routeCSaddleNearWindowProfile
  change routeCSaddleNearNormalizedProfile A t (n + 1) = _
  symm
  exact Set.indicator_of_mem (α := ℝ) (M := ℂ)
    (s := Icc (-Real.sqrt ((n + 1 : ℕ) : ℝ) / 8)
      (Real.sqrt ((n + 1 : ℕ) : ℝ) / 8)) (a := t)
    (by
      have hab := abs_le.1 hn
      exact ⟨by linarith [hab.1], hab.2⟩)
    (fun x => routeCSaddleNearNormalizedProfile A x (n + 1))

theorem measurable_routeCSaddleGaussianProfile (A : ℂ) :
    Measurable (routeCSaddleGaussianProfile A) := by
  unfold routeCSaddleGaussianProfile routeCSaddleGaussianPhase
  fun_prop

theorem routeCSaddleNearWindowProfile_integral_tendsto
    (A : ℂ) :
    Tendsto (fun n : ℕ => ∫ t : ℝ, routeCSaddleNearWindowProfile A n t)
      atTop (nhds (∫ t : ℝ, routeCSaddleGaussianProfile A t)) := by
  apply tendsto_integral_of_dominated_convergence
    (routeCSaddleNearGaussianMajorant A)
  · exact aestronglyMeasurable_routeCSaddleNearWindowProfile A
  · exact integrable_routeCSaddleNearGaussianMajorant A
  · intro n
    filter_upwards with t
    exact norm_routeCSaddleNearWindowProfile_le_majorant A n t
  · filter_upwards with t
    exact routeCSaddleNearWindowProfile_tendsto A t

theorem integral_routeCSaddleNearWindowProfile_eq_intervalIntegral
    (A : ℂ) (n : ℕ) :
    (∫ t : ℝ, routeCSaddleNearWindowProfile A n t) =
      ∫ t in (-Real.sqrt ((n + 1 : ℕ) : ℝ) / 8)..
          (Real.sqrt ((n + 1 : ℕ) : ℝ) / 8),
        routeCSaddleNearNormalizedProfile A t (n + 1) := by
  unfold routeCSaddleNearWindowProfile
  rw [MeasureTheory.integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by
      have := Real.sqrt_nonneg ((n + 1 : ℕ) : ℝ)
      linarith)]

theorem routeCSaddleNearIntegral_normalized_tendsto_gaussianIntegral
    (A : ℂ) :
    Tendsto (fun n : ℕ =>
        routeCSaddleNearIntegral A 1 (1 / 8) (n + 1) /
          routeCSaddleComplexNormalizerOne A (n + 1))
      atTop (nhds (∫ t : ℝ, routeCSaddleGaussianProfile A t)) := by
  have h := routeCSaddleNearWindowProfile_integral_tendsto A
  apply h.congr'
  filter_upwards with n
  rw [integral_routeCSaddleNearWindowProfile_eq_intervalIntegral]
  convert (routeCSaddleNearIntegral_div_normalizer_eq_profile_integral
    A (1 / 8) (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
      (by norm_num) (by norm_num)).symm using 1
  all_goals ring

theorem routeCSaddleGaussianProfile_eq_gaussianPDF_mul_exp
    (A : ℂ) (t : ℝ) :
    routeCSaddleGaussianProfile A t =
      Complex.exp (-(A ^ 2) / 8) *
        ((gaussianPDFReal 0 1 t : ℝ) : ℂ) *
          Complex.exp ((-A / 2) * (t : ℂ)) := by
  unfold routeCSaddleGaussianProfile routeCSaddleGaussianPhase
    gaussianPDFReal
  push_cast
  norm_num
  rw [show Complex.exp (-((t : ℂ) ^ 2) / 2 - A * ((t : ℂ) / 2)) =
      Complex.exp (-((t : ℂ) ^ 2) / 2) *
        Complex.exp ((-A / 2) * (t : ℂ)) by
    rw [← Complex.exp_add]
    congr 1
    ring]
  ring

theorem integral_routeCSaddleGaussianProfile (A : ℂ) :
    ∫ t : ℝ, routeCSaddleGaussianProfile A t = 1 := by
  have hmgf := complexMGF_id_gaussianReal (μ := 0) (v := 1) (-A / 2)
  unfold complexMGF at hmgf
  rw [integral_gaussianReal_eq_integral_smul
    (by norm_num : (1 : NNReal) ≠ 0)] at hmgf
  simp only [Complex.real_smul, id_eq] at hmgf
  rw [show (∫ t : ℝ, routeCSaddleGaussianProfile A t) =
      Complex.exp (-(A ^ 2) / 8) *
        (∫ t : ℝ, ((gaussianPDFReal 0 1 t : ℝ) : ℂ) *
          Complex.exp ((-A / 2) * (t : ℂ))) by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    simpa only [mul_assoc] using
      routeCSaddleGaussianProfile_eq_gaussianPDF_mul_exp A t]
  rw [hmgf]
  norm_num
  rw [← Complex.exp_add]
  convert Complex.exp_zero using 1
  all_goals ring

theorem routeCSaddleNearIntegral_normalized_tendsto_one
    (A : ℂ) :
    Tendsto (fun n : ℕ =>
        routeCSaddleNearIntegral A 1 (1 / 8) (n + 1) /
          routeCSaddleComplexNormalizerOne A (n + 1))
      atTop (nhds 1) := by
  simpa only [integral_routeCSaddleGaussianProfile] using
    routeCSaddleNearIntegral_normalized_tendsto_gaussianIntegral A

theorem routeCSaddleIntegral_normalized_tendsto_one
    (A : ℂ) :
    Tendsto (fun n : ℕ =>
        routeCSaddleIntegral A 1 (n + 1) /
          routeCSaddleComplexNormalizerOne A (n + 1))
      atTop (nhds 1) := by
  have hnear := routeCSaddleNearIntegral_normalized_tendsto_one A
  have hfar := (far_div_complexNormalizer_tendsto_zero A
    (delta := 1 / 8) (by norm_num) (by norm_num)).comp
      (tendsto_add_atTop_nat 1)
  have hsum := hnear.add hfar
  simpa only [add_zero] using hsum.congr' (by
    filter_upwards with n
    rw [routeCSaddleIntegral_eq_near_add_far A 1 (1 / 8) (n + 1)
      (by positivity)]
    simp only [Function.comp_apply]
    ring)

/-- The exact `alpha = 1` instance of Bettin--Conrey's saddle target.  The
shift by one in the proved asymptotic removes only a finite prefix. -/
theorem routeCSaddleIntegralAsymptoticTarget_one (A : ℂ) :
    RouteCSaddleIntegralAsymptoticTarget A 1 := by
  unfold RouteCSaddleIntegralAsymptoticTarget
  apply (tendsto_add_atTop_iff_nat 1).1
  apply (routeCSaddleIntegral_normalized_tendsto_one A).congr'
  filter_upwards with n
  unfold routeCSaddleComplexNormalizerOne
  congr 4
  ring

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleNearLimit
