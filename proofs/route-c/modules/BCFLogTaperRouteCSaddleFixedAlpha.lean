import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleNearLimit

/-!
# Route C: fixed-alpha saddle rows used by the Bessel expansion

Bettin--Conrey's coefficient extraction does not use only the `alpha = 1`
row of the saddle integral.  The leading, first-correction, and error rows of
the `K₁` expansion have respectively `alpha = 1/4`, `-1/4`, and `-3/4`.

This module fixes that normalization before any coefficient transfer.  After
the substitution `u = n + sqrt n * t`, changing `alpha` multiplies the
already-normalized `alpha = 1` profile by the exact factor

`(1 + t / sqrt n) ^ (alpha - 1)`.

The identity below is algebraic and retains the full complex saddle phase.
It is the required bridge from the completed `alpha = 1` saddle theorem to
the three rows occurring in the paper.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleFixedAlpha

open Filter MeasureTheory Set
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleIntegral
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleCentralWindow
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleRootAbsorption
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleNearPointwise
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleNearRescaling
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleNearLimit

/-- The exact normalizer in Bettin--Conrey's Lemma 3 for a general fixed
power `alpha`. -/
noncomputable def routeCSaddleComplexNormalizer
    (A : ℂ) (alpha : ℝ) (n : ℕ) : ℂ :=
  (Real.sqrt (2 * Real.pi) : ℂ) * Complex.exp (A ^ 2 / 8) *
    Complex.exp (-A * (Real.sqrt (n : ℝ) : ℂ)) *
      Complex.exp (-((n : ℝ) : ℂ)) *
        (Real.rpow n ((n : ℝ) + alpha - 1 / 2) : ℂ)

/-- The entire dependence on `alpha` after central rescaling. -/
noncomputable def routeCSaddleAlphaWeight
    (alpha t : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (1 + t / Real.sqrt (n : ℝ)) (alpha - 1)

/-- The general fixed-`alpha` normalized central profile. -/
noncomputable def routeCSaddleNearNormalizedProfileAlpha
    (A : ℂ) (alpha t : ℝ) (n : ℕ) : ℂ :=
  (routeCSaddleAlphaWeight alpha t n : ℂ) *
    routeCSaddleNearNormalizedProfile A t n

/-- The Jacobian-rescaled original integrand with the general normalizer. -/
noncomputable def routeCSaddleNearRescaledNormalizedIntegrandAlpha
    (A : ℂ) (alpha t : ℝ) (n : ℕ) : ℂ :=
  (Real.sqrt (n : ℝ) : ℂ) *
      routeCSaddleIntegrand A alpha n
        ((n : ℝ) + Real.sqrt (n : ℝ) * t) /
    routeCSaddleComplexNormalizer A alpha n

theorem routeCSaddleComplexNormalizer_one
    (A : ℂ) (n : ℕ) :
    routeCSaddleComplexNormalizer A 1 n =
      routeCSaddleComplexNormalizerOne A n := by
  unfold routeCSaddleComplexNormalizer routeCSaddleComplexNormalizerOne
  congr 4
  ring

theorem routeCSaddleAlphaWeight_one
    (t : ℝ) (n : ℕ) :
    routeCSaddleAlphaWeight 1 t n = 1 := by
  simp [routeCSaddleAlphaWeight]

theorem routeCSaddleNearNormalizedProfileAlpha_one
    (A : ℂ) (t : ℝ) (n : ℕ) :
    routeCSaddleNearNormalizedProfileAlpha A 1 t n =
      routeCSaddleNearNormalizedProfile A t n := by
  simp [routeCSaddleNearNormalizedProfileAlpha,
    routeCSaddleAlphaWeight_one]

/-- Changing `alpha` in the rescaled integrand is exactly multiplication by
the fixed-power central weight.  No limiting statement is used here. -/
theorem routeCSaddleNearRescaledNormalizedIntegrandAlpha_eq_weight_mul_one
    (A : ℂ) (alpha t : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (ht : -Real.sqrt (n : ℝ) < t) :
    routeCSaddleNearRescaledNormalizedIntegrandAlpha A alpha t n =
      (routeCSaddleAlphaWeight alpha t n : ℂ) *
        routeCSaddleNearRescaledNormalizedIntegrand A t n := by
  let s := Real.sqrt (n : ℝ)
  let u := (n : ℝ) + s * t
  let w := 1 + t / s
  have hnR : 0 < (n : ℝ) := by positivity
  have hs : 0 < s := Real.sqrt_pos.2 hnR
  have hw : 0 < w := by
    rw [show w = (s + t) / s by dsimp [w]; field_simp]
    exact div_pos (by dsimp [s] at ht ⊢; linarith) hs
  have hu : u = (n : ℝ) * w := by
    dsimp [u, w]
    have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
    rw [← hs2]
    field_simp
  have hualpha : Real.rpow u ((n : ℝ) + alpha - 1) =
      Real.rpow u (n : ℝ) * Real.rpow u (alpha - 1) := by
    rw [show (n : ℝ) + alpha - 1 = (n : ℝ) + (alpha - 1) by ring]
    exact Real.rpow_add (by rw [hu]; positivity) _ _
  have huweight : Real.rpow u (alpha - 1) =
      Real.rpow n (alpha - 1) * Real.rpow w (alpha - 1) := by
    rw [hu]
    exact Real.mul_rpow (z := alpha - 1) hnR.le hw.le
  have hnalpha : Real.rpow n ((n : ℝ) + alpha - 1 / 2) =
      Real.rpow n ((n : ℝ) + 1 / 2) * Real.rpow n (alpha - 1) := by
    rw [show (n : ℝ) + alpha - 1 / 2 =
        ((n : ℝ) + 1 / 2) + (alpha - 1) by ring]
    exact Real.rpow_add hnR _ _
  have hnpow_ne : (Real.rpow n (alpha - 1) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Real.rpow_pos_of_pos hnR _))
  unfold routeCSaddleNearRescaledNormalizedIntegrandAlpha
    routeCSaddleNearRescaledNormalizedIntegrand
    routeCSaddleAlphaWeight routeCSaddleComplexNormalizer
    routeCSaddleComplexNormalizerOne routeCSaddleIntegrand
  rw [show (n : ℝ) + 1 - 1 = (n : ℝ) by ring]
  rw [hualpha, huweight, hnalpha]
  push_cast
  have hwRaw : w = 1 + t / Real.sqrt (n : ℝ) := by rfl
  have huRaw : u = (n : ℝ) + Real.sqrt (n : ℝ) * t := by rfl
  rw [hwRaw, huRaw]
  field_simp

/-- Exact fixed-`alpha` rescaling into the common Gaussian phase and the
additional algebraic weight. -/
theorem routeCSaddleNearRescaledNormalizedIntegrandAlpha_eq_profile
    (A : ℂ) (alpha t : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (ht : -Real.sqrt (n : ℝ) < t) :
    routeCSaddleNearRescaledNormalizedIntegrandAlpha A alpha t n =
      routeCSaddleNearNormalizedProfileAlpha A alpha t n := by
  rw [routeCSaddleNearRescaledNormalizedIntegrandAlpha_eq_weight_mul_one
    A alpha t n hn ht]
  rw [routeCSaddleNearRescaledNormalizedIntegrand_eq_profile A t n hn ht]
  rfl

theorem routeCSaddleAlphaWeight_tendsto_one
    (alpha t : ℝ) :
    Tendsto (routeCSaddleAlphaWeight alpha t) atTop (nhds 1) := by
  have hbase : Tendsto
      (fun n : ℕ => 1 + t / Real.sqrt (n : ℝ)) atTop (nhds 1) := by
    simpa only [add_zero] using
      tendsto_const_nhds.add (tendsto_div_sqrt_nat_zero t)
  have hpow := (Real.continuousAt_rpow_const 1 (alpha - 1)
    (Or.inl one_ne_zero)).tendsto.comp hbase
  simpa only [routeCSaddleAlphaWeight, Real.one_rpow] using hpow

theorem routeCSaddleNearNormalizedProfileAlpha_tendsto
    (A : ℂ) (alpha t : ℝ) :
    Tendsto (routeCSaddleNearNormalizedProfileAlpha A alpha t) atTop
      (nhds (routeCSaddleGaussianProfile A t)) := by
  unfold routeCSaddleNearNormalizedProfileAlpha
  have hw := (Complex.continuous_ofReal.tendsto 1).comp
    (routeCSaddleAlphaWeight_tendsto_one alpha t)
  simpa only [Complex.ofReal_one, one_mul] using
    hw.mul (routeCSaddleNearNormalizedProfile_tendsto A t)

/-- A fixed constant controlling the additional `alpha`-weight throughout
the central relative window. -/
noncomputable def routeCSaddleAlphaWeightMajorant (alpha : ℝ) : ℝ :=
  max (Real.rpow (7 / 8) (alpha - 1))
    (Real.rpow (9 / 8) (alpha - 1))

theorem routeCSaddleAlphaWeightMajorant_nonneg (alpha : ℝ) :
    0 ≤ routeCSaddleAlphaWeightMajorant alpha := by
  unfold routeCSaddleAlphaWeightMajorant
  exact (Real.rpow_nonneg (by norm_num) _).trans (le_max_left _ _)

theorem routeCSaddleAlphaWeight_le_majorant
    (alpha t : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (ht : |t| ≤ Real.sqrt (n : ℝ) / 8) :
    routeCSaddleAlphaWeight alpha t n ≤
      routeCSaddleAlphaWeightMajorant alpha := by
  let s := Real.sqrt (n : ℝ)
  let b := 1 + t / s
  let p := alpha - 1
  have hnR : 0 < (n : ℝ) := by positivity
  have hs : 0 < s := Real.sqrt_pos.2 hnR
  have htlo : -s / 8 ≤ t := by
    have hab := neg_abs_le t
    dsimp [s] at ht ⊢
    linarith
  have hthi : t ≤ s / 8 := by
    have hab := le_abs_self t
    dsimp [s] at ht ⊢
    linarith
  have hbLo : 7 / 8 ≤ b := by
    have hdiv : -(1 : ℝ) / 8 ≤ t / s := by
      rw [le_div_iff₀ hs]
      linarith
    dsimp [b]
    linarith
  have hbHi : b ≤ 9 / 8 := by
    have hdiv : t / s ≤ (1 : ℝ) / 8 := by
      rw [div_le_iff₀ hs]
      linarith
    dsimp [b]
    linarith
  have hbPos : 0 < b := (by norm_num : (0 : ℝ) < 7 / 8).trans_le hbLo
  unfold routeCSaddleAlphaWeight routeCSaddleAlphaWeightMajorant
  change Real.rpow b p ≤ max (Real.rpow (7 / 8) p) (Real.rpow (9 / 8) p)
  by_cases hp : 0 ≤ p
  · exact (Real.rpow_le_rpow hbPos.le hbHi hp).trans (le_max_right _ _)
  · have hp' : p ≤ 0 := le_of_not_ge hp
    exact (Real.rpow_le_rpow_of_nonpos (by norm_num) hbLo hp').trans
      (le_max_left _ _)

theorem measurable_routeCSaddleAlphaWeight
    (alpha : ℝ) (n : ℕ) :
    Measurable (fun t : ℝ => routeCSaddleAlphaWeight alpha t n) := by
  unfold routeCSaddleAlphaWeight
  have hrpow : Measurable (fun x : ℝ => Real.rpow x (alpha - 1)) := by
    apply measurable_of_continuousOn_compl_singleton 0
    intro x hx
    exact (Real.continuousAt_rpow_const x (alpha - 1)
      (Or.inl (Set.mem_compl_singleton_iff.mp hx))).continuousWithinAt
  exact hrpow.comp (by fun_prop)

theorem measurable_routeCSaddleNearNormalizedProfileAlpha
    (A : ℂ) (alpha : ℝ) (n : ℕ) :
    Measurable (fun t : ℝ =>
      routeCSaddleNearNormalizedProfileAlpha A alpha t n) := by
  unfold routeCSaddleNearNormalizedProfileAlpha
  exact (Complex.measurable_ofReal.comp
    (measurable_routeCSaddleAlphaWeight alpha n)).mul
      (measurable_routeCSaddleNearNormalizedProfile A n)

theorem norm_routeCSaddleNearNormalizedProfileAlpha_le_majorant
    (A : ℂ) (alpha t : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (ht : |t| ≤ Real.sqrt (n : ℝ) / 8) :
    ‖routeCSaddleNearNormalizedProfileAlpha A alpha t n‖ ≤
      routeCSaddleAlphaWeightMajorant alpha *
        routeCSaddleNearGaussianMajorant A t := by
  have hw := routeCSaddleAlphaWeight_le_majorant alpha t n hn ht
  have hp := norm_routeCSaddleNearNormalizedProfile_le_majorant
    A t n hn ht
  have hweight : 0 ≤ routeCSaddleAlphaWeight alpha t n := by
    have hnR : 0 < (n : ℝ) := by positivity
    have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
    have htlo : -Real.sqrt (n : ℝ) / 8 ≤ t := by
      linarith [neg_abs_le t]
    have hbase : 0 ≤ 1 + t / Real.sqrt (n : ℝ) := by
      have hdiv : -(1 : ℝ) / 8 ≤ t / Real.sqrt (n : ℝ) := by
        rw [le_div_iff₀ hs]
        linarith
      linarith
    unfold routeCSaddleAlphaWeight
    exact Real.rpow_nonneg hbase _
  unfold routeCSaddleNearNormalizedProfileAlpha
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hweight]
  exact mul_le_mul hw hp (norm_nonneg _)
    (routeCSaddleAlphaWeightMajorant_nonneg alpha)

theorem integrable_routeCSaddleNearAlphaMajorant
    (A : ℂ) (alpha : ℝ) :
    Integrable (fun t : ℝ => routeCSaddleAlphaWeightMajorant alpha *
      routeCSaddleNearGaussianMajorant A t) :=
  (integrable_routeCSaddleNearGaussianMajorant A).const_mul _

noncomputable def routeCSaddleNearWindowProfileAlpha
    (A : ℂ) (alpha : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  (Icc (-Real.sqrt ((n + 1 : ℕ) : ℝ) / 8)
      (Real.sqrt ((n + 1 : ℕ) : ℝ) / 8)).indicator
    (fun x => routeCSaddleNearNormalizedProfileAlpha A alpha x (n + 1)) t

theorem aestronglyMeasurable_routeCSaddleNearWindowProfileAlpha
    (A : ℂ) (alpha : ℝ) (n : ℕ) :
    AEStronglyMeasurable (routeCSaddleNearWindowProfileAlpha A alpha n) := by
  apply Measurable.aestronglyMeasurable
  unfold routeCSaddleNearWindowProfileAlpha
  exact (measurable_routeCSaddleNearNormalizedProfileAlpha A alpha (n + 1)).indicator
    measurableSet_Icc

theorem norm_routeCSaddleNearWindowProfileAlpha_le_majorant
    (A : ℂ) (alpha : ℝ) (n : ℕ) (t : ℝ) :
    ‖routeCSaddleNearWindowProfileAlpha A alpha n t‖ ≤
      routeCSaddleAlphaWeightMajorant alpha *
        routeCSaddleNearGaussianMajorant A t := by
  let s := Real.sqrt ((n + 1 : ℕ) : ℝ)
  by_cases ht : t ∈ Icc (-s / 8) (s / 8)
  · have habs : |t| ≤ s / 8 := abs_le.2 ⟨by linarith [ht.1], ht.2⟩
    rw [routeCSaddleNearWindowProfileAlpha, Set.indicator_of_mem]
    · exact norm_routeCSaddleNearNormalizedProfileAlpha_le_majorant
        A alpha t (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
          (by simpa only [s] using habs)
    · simpa only [s] using ht
  · have ht' : t ∉ Icc
        (-Real.sqrt ((n + 1 : ℕ) : ℝ) / 8)
        (Real.sqrt ((n + 1 : ℕ) : ℝ) / 8) := by
      simpa only [s] using ht
    simp only [routeCSaddleNearWindowProfileAlpha, Set.indicator, ht',
      ↓reduceIte, norm_zero]
    exact mul_nonneg (routeCSaddleAlphaWeightMajorant_nonneg alpha)
      (by
        unfold routeCSaddleNearGaussianMajorant
        exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)

theorem routeCSaddleNearWindowProfileAlpha_tendsto
    (A : ℂ) (alpha t : ℝ) :
    Tendsto (fun n : ℕ => routeCSaddleNearWindowProfileAlpha A alpha n t)
      atTop (nhds (routeCSaddleGaussianProfile A t)) := by
  have hnat : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hwindow : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) / 8) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp hnat).atTop_div_const (by norm_num)
  have hevent : ∀ᶠ n : ℕ in atTop,
      |t| ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) / 8 :=
    tendsto_atTop.1 hwindow |t|
  have hprofile :=
    (routeCSaddleNearNormalizedProfileAlpha_tendsto A alpha t).comp
      (tendsto_add_atTop_nat 1)
  apply hprofile.congr'
  filter_upwards [hevent] with n hn
  unfold routeCSaddleNearWindowProfileAlpha
  change routeCSaddleNearNormalizedProfileAlpha A alpha t (n + 1) = _
  symm
  exact Set.indicator_of_mem (α := ℝ) (M := ℂ)
    (s := Icc (-Real.sqrt ((n + 1 : ℕ) : ℝ) / 8)
      (Real.sqrt ((n + 1 : ℕ) : ℝ) / 8)) (a := t)
    (by
      have hab := abs_le.1 hn
      exact ⟨by linarith [hab.1], hab.2⟩)
    (fun x => routeCSaddleNearNormalizedProfileAlpha A alpha x (n + 1))

theorem routeCSaddleNearWindowProfileAlpha_integral_tendsto
    (A : ℂ) (alpha : ℝ) :
    Tendsto (fun n : ℕ =>
        ∫ t : ℝ, routeCSaddleNearWindowProfileAlpha A alpha n t)
      atTop (nhds (∫ t : ℝ, routeCSaddleGaussianProfile A t)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun t : ℝ => routeCSaddleAlphaWeightMajorant alpha *
      routeCSaddleNearGaussianMajorant A t)
  · exact aestronglyMeasurable_routeCSaddleNearWindowProfileAlpha A alpha
  · exact integrable_routeCSaddleNearAlphaMajorant A alpha
  · intro n
    filter_upwards with t
    exact norm_routeCSaddleNearWindowProfileAlpha_le_majorant A alpha n t
  · filter_upwards with t
    exact routeCSaddleNearWindowProfileAlpha_tendsto A alpha t

/-- General fixed-`alpha` version of the exact near-set change of variables. -/
theorem routeCSaddleNearIntegral_div_normalizer_eq_profileAlpha_integral
    (A : ℂ) (alpha delta : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta < 1) :
    routeCSaddleNearIntegral A alpha delta n /
        routeCSaddleComplexNormalizer A alpha n =
      ∫ t in (-delta * Real.sqrt (n : ℝ))..
          (delta * Real.sqrt (n : ℝ)),
        routeCSaddleNearNormalizedProfileAlpha A alpha t n := by
  let s := Real.sqrt (n : ℝ)
  let f := routeCSaddleIntegrand A alpha n
  let z := routeCSaddleComplexNormalizer A alpha n
  have hnR : 0 < (n : ℝ) := by positivity
  have hs : 0 < s := Real.sqrt_pos.2 hnR
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
  have hbounds : (1 - delta) * (n : ℝ) ≤
      (1 + delta) * (n : ℝ) := by nlinarith
  have hnear : routeCSaddleNearIntegral A alpha delta n =
      ∫ u in ((1 - delta) * (n : ℝ))..((1 + delta) * (n : ℝ)), f u := by
    unfold routeCSaddleNearIntegral
    rw [routeCSaddleNearSet_eq_Icc delta n hn hdelta1,
      integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hbounds]
  have hchange :
      (s : ℂ) *
          (∫ t in (-delta * s)..(delta * s),
            f ((n : ℝ) + s * t)) =
        ∫ u in ((1 - delta) * (n : ℝ))..((1 + delta) * (n : ℝ)), f u := by
    have h := intervalIntegral.smul_integral_comp_add_mul
      (a := -delta * s) (b := delta * s) f s (n : ℝ)
    convert h using 1
    all_goals rw [← hs2]
    all_goals ring
  have hpoint : EqOn
      (fun t => (s : ℂ) * f ((n : ℝ) + s * t) / z)
      (routeCSaddleNearNormalizedProfileAlpha A alpha · n)
      (uIcc (-delta * s) (delta * s)) := by
    intro t ht
    have hab : -delta * s ≤ t ∧ t ≤ delta * s := by
      rw [uIcc_of_le (by nlinarith : -delta * s ≤ delta * s)] at ht
      exact ht
    have ht_lower : -s < t := by
      have : -s < -delta * s := by nlinarith
      linarith
    simpa only [s, f, z,
      routeCSaddleNearRescaledNormalizedIntegrandAlpha] using
        routeCSaddleNearRescaledNormalizedIntegrandAlpha_eq_profile
          A alpha t n hn ht_lower
  rw [hnear, ← hchange]
  rw [← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_div]
  exact intervalIntegral.integral_congr hpoint

theorem integral_routeCSaddleNearWindowProfileAlpha_eq_intervalIntegral
    (A : ℂ) (alpha : ℝ) (n : ℕ) :
    (∫ t : ℝ, routeCSaddleNearWindowProfileAlpha A alpha n t) =
      ∫ t in (-Real.sqrt ((n + 1 : ℕ) : ℝ) / 8)..
          (Real.sqrt ((n + 1 : ℕ) : ℝ) / 8),
        routeCSaddleNearNormalizedProfileAlpha A alpha t (n + 1) := by
  unfold routeCSaddleNearWindowProfileAlpha
  rw [MeasureTheory.integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by
      have := Real.sqrt_nonneg ((n + 1 : ℕ) : ℝ)
      linarith)]

/-- The normalized near-saddle contribution tends to one for every fixed
real `alpha`; in particular this covers the three Bessel rows. -/
theorem routeCSaddleNearIntegralAlpha_normalized_tendsto_one
    (A : ℂ) (alpha : ℝ) :
    Tendsto (fun n : ℕ =>
        routeCSaddleNearIntegral A alpha (1 / 8) (n + 1) /
          routeCSaddleComplexNormalizer A alpha (n + 1))
      atTop (nhds 1) := by
  have h := routeCSaddleNearWindowProfileAlpha_integral_tendsto A alpha
  rw [integral_routeCSaddleGaussianProfile] at h
  apply h.congr'
  filter_upwards with n
  rw [integral_routeCSaddleNearWindowProfileAlpha_eq_intervalIntegral]
  convert (routeCSaddleNearIntegral_div_normalizer_eq_profileAlpha_integral
    A alpha (1 / 8) (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
      (by norm_num) (by norm_num)).symm using 1
  all_goals ring

theorem routeCSaddleNearIntegral_quarter_normalized_tendsto_one (A : ℂ) :
    Tendsto (fun n : ℕ =>
        routeCSaddleNearIntegral A (1 / 4) (1 / 8) (n + 1) /
          routeCSaddleComplexNormalizer A (1 / 4) (n + 1))
      atTop (nhds 1) :=
  routeCSaddleNearIntegralAlpha_normalized_tendsto_one A (1 / 4)

theorem routeCSaddleNearIntegral_neg_quarter_normalized_tendsto_one (A : ℂ) :
    Tendsto (fun n : ℕ =>
        routeCSaddleNearIntegral A (-1 / 4) (1 / 8) (n + 1) /
          routeCSaddleComplexNormalizer A (-1 / 4) (n + 1))
      atTop (nhds 1) :=
  routeCSaddleNearIntegralAlpha_normalized_tendsto_one A (-1 / 4)

theorem routeCSaddleNearIntegral_neg_three_quarters_normalized_tendsto_one
    (A : ℂ) :
    Tendsto (fun n : ℕ =>
        routeCSaddleNearIntegral A (-3 / 4) (1 / 8) (n + 1) /
          routeCSaddleComplexNormalizer A (-3 / 4) (n + 1))
      atTop (nhds 1) :=
  routeCSaddleNearIntegralAlpha_normalized_tendsto_one A (-3 / 4)

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleFixedAlpha
