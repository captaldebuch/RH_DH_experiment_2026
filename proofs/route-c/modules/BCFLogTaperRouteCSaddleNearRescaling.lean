import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleNearPointwise

/-!
# Route C: exact near-saddle rescaling and Gaussian domination

This module closes the measure-theoretic gap between the pointwise central
saddle asymptotics and the original Bettin--Conrey integral.  It proves the
exact Jacobian-rescaled identity under `u = n + sqrt n * t`, converts the
genuine near-set integral to the normalized profile integral, and supplies an
explicit integrable Gaussian majorant on the fixed relative window
`|t| ≤ sqrt n / 8`.

No asymptotic statement is used in the change of variables: all normalizing
constants and both complex exponential factors are retained exactly.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleNearRescaling

open Filter MeasureTheory Set
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleIntegral
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleCentralWindow
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleRootAbsorption
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleNearPointwise

noncomputable def routeCSaddleRescaledRealBase (t : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (n : ℝ) *
      (Real.rpow ((n : ℝ) + Real.sqrt (n : ℝ) * t) (n : ℝ) *
        Real.exp (-((n : ℝ) + Real.sqrt (n : ℝ) * t))) /
    (Real.exp (-(n : ℝ)) *
      Real.rpow n ((n : ℝ) + 1 / 2))

theorem routeCSaddleRescaledRealBase_eq_exp_scaledEntropy
    (t : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (ht : -Real.sqrt (n : ℝ) < t) :
    routeCSaddleRescaledRealBase t n =
      Real.exp (routeCSaddleScaledEntropy t n) := by
  let s := Real.sqrt (n : ℝ)
  let w := t / s
  have hnR : 0 < (n : ℝ) := by positivity
  have hs : 0 < s := Real.sqrt_pos.2 hnR
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
  have hw : 0 < 1 + w := by
    rw [show 1 + w = (s + t) / s by dsimp [w]; field_simp]
    exact div_pos (by dsimp [s] at ht ⊢; linarith) hs
  have hu : (n : ℝ) + s * t = (n : ℝ) * (1 + w) := by
    dsimp [w]
    rw [← hs2]
    field_simp
  have hrpowu : Real.rpow ((n : ℝ) + s * t) (n : ℝ) =
      Real.rpow n (n : ℝ) * Real.rpow (1 + w) (n : ℝ) := by
    rw [hu]
    exact Real.mul_rpow (z := (n : ℝ)) hnR.le hw.le
  have hrpown : Real.rpow n ((n : ℝ) + 1 / 2) =
      Real.rpow n (n : ℝ) * s := by
    calc
      Real.rpow n ((n : ℝ) + 1 / 2) =
          Real.rpow n (n : ℝ) * Real.rpow n (1 / 2) :=
        Real.rpow_add hnR _ _
      _ = Real.rpow n (n : ℝ) * s := by
        exact congrArg (Real.rpow n (n : ℝ) * ·)
          (by simpa only [s] using (Real.sqrt_eq_rpow (n : ℝ)).symm)
  have hscaled : routeCSaddleScaledEntropy t n =
      (n : ℝ) * Real.log (1 + w) - s * t := by
    unfold routeCSaddleScaledEntropy
    change (n : ℝ) * (Real.log (1 + t / s) - t / s) = _
    dsimp [w]
    rw [← hs2]
    field_simp
  unfold routeCSaddleRescaledRealBase
  change s *
      (Real.rpow ((n : ℝ) + s * t) (n : ℝ) *
        Real.exp (-((n : ℝ) + s * t))) /
    (Real.exp (-(n : ℝ)) * Real.rpow n ((n : ℝ) + 1 / 2)) = _
  rw [hrpowu, hrpown, hscaled]
  rw [show Real.rpow (1 + w) (n : ℝ) =
      Real.exp ((n : ℝ) * Real.log (1 + w)) by
        calc
          Real.rpow (1 + w) (n : ℝ) =
              Real.exp (Real.log (1 + w) * (n : ℝ)) :=
            Real.rpow_def_of_pos hw _
          _ = Real.exp ((n : ℝ) * Real.log (1 + w)) := by
            congr 1
            ring]
  field_simp
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem routeCSaddleRescaledRootExp_div
    (A : ℂ) (t : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (ht : -Real.sqrt (n : ℝ) < t) :
    Complex.exp (-A *
        (Real.sqrt ((n : ℝ) + Real.sqrt (n : ℝ) * t) : ℂ)) /
      Complex.exp (-A * (Real.sqrt (n : ℝ) : ℂ)) =
        Complex.exp (-A * (routeCSaddleScaledRootShift t n : ℂ)) := by
  rw [← Complex.exp_sub]
  rw [routeCSaddleScaledRootShift_eq_saddle_coordinate t n hn ht]
  congr 1
  push_cast
  ring

noncomputable def routeCSaddleNearRescaledNormalizedIntegrand
    (A : ℂ) (t : ℝ) (n : ℕ) : ℂ :=
  ((Real.sqrt (n : ℝ) : ℝ) : ℂ) *
      routeCSaddleIntegrand A 1 n
        ((n : ℝ) + Real.sqrt (n : ℝ) * t) /
    routeCSaddleComplexNormalizerOne A n

theorem routeCSaddleNearRescaledNormalizedIntegrand_eq_profile
    (A : ℂ) (t : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (ht : -Real.sqrt (n : ℝ) < t) :
    routeCSaddleNearRescaledNormalizedIntegrand A t n =
      routeCSaddleNearNormalizedProfile A t n := by
  let s := Real.sqrt (n : ℝ)
  let u := (n : ℝ) + s * t
  let q := Real.rpow u (n : ℝ) * Real.exp (-u)
  let d := Real.exp (-(n : ℝ)) * Real.rpow n ((n : ℝ) + 1 / 2)
  let qC : ℂ := (Real.rpow u (n : ℝ) : ℂ) * Complex.exp (-(u : ℂ))
  let dC : ℂ := Complex.exp (-((n : ℝ) : ℂ)) *
    (Real.rpow n ((n : ℝ) + 1 / 2) : ℂ)
  let z := Complex.exp (-A * (Real.sqrt u : ℂ))
  let z₀ := Complex.exp (-A * (s : ℂ))
  let c : ℂ := (Real.sqrt (2 * Real.pi) : ℂ) * Complex.exp (A ^ 2 / 8)
  have hnR : 0 < (n : ℝ) := by positivity
  have hs : 0 < s := Real.sqrt_pos.2 hnR
  have hu : 0 < u := by
    have hmul := mul_lt_mul_of_pos_left ht hs
    dsimp [u, s] at hmul ⊢
    nlinarith [Real.sq_sqrt hnR.le]
  have hd : 0 < d := by
    dsimp [d]
    exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hnR _)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero
      (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne')
      (Complex.exp_ne_zero _)
  have hz₀ : z₀ ≠ 0 := by dsimp [z₀]; exact Complex.exp_ne_zero _
  have hreal : s * q / d = Real.exp (routeCSaddleScaledEntropy t n) := by
    simpa only [routeCSaddleRescaledRealBase, s, u, q, d] using
      routeCSaddleRescaledRealBase_eq_exp_scaledEntropy t n hn ht
  have hroot : z / z₀ =
      Complex.exp (-A * (routeCSaddleScaledRootShift t n : ℂ)) := by
    simpa only [s, u, z, z₀] using
      routeCSaddleRescaledRootExp_div A t n hn ht
  have hqC : qC = (q : ℂ) := by
    dsimp [qC, q]
    calc
      (Real.rpow u (n : ℝ) : ℂ) * Complex.exp (-(u : ℂ)) =
          (Real.rpow u (n : ℝ) : ℂ) * (Real.exp (-u) : ℂ) := by
            rw [Complex.ofReal_exp]
            push_cast
            rfl
      _ = (Real.rpow u (n : ℝ) * Real.exp (-u) : ℝ) := by
            push_cast
            rfl
  have hdC : dC = (d : ℂ) := by
    dsimp [dC, d]
    calc
      Complex.exp (-((n : ℝ) : ℂ)) *
          (Real.rpow n ((n : ℝ) + 1 / 2) : ℂ) =
          (Real.exp (-(n : ℝ)) : ℂ) *
            (Real.rpow n ((n : ℝ) + 1 / 2) : ℂ) := by
              rw [Complex.ofReal_exp]
              push_cast
              rfl
      _ = (Real.exp (-(n : ℝ)) *
          Real.rpow n ((n : ℝ) + 1 / 2) : ℝ) := by
            push_cast
            rfl
  have hrealC : (s : ℂ) * qC / dC =
      Complex.exp (routeCSaddleScaledEntropy t n) := by
    rw [hqC, hdC]
    calc
      (s : ℂ) * (q : ℂ) / (d : ℂ) = (s * q / d : ℝ) := by
        push_cast
        rfl
      _ = (Real.exp (routeCSaddleScaledEntropy t n) : ℝ) := by rw [hreal]
      _ = Complex.exp (routeCSaddleScaledEntropy t n) :=
        Complex.ofReal_exp _
  have haux : (s : ℂ) * (qC * z) / (c * z₀ * dC) =
      ((1 / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) *
        Complex.exp (-(A ^ 2) / 8) *
          Complex.exp (routeCSaddleNearPhase A t n) := by
    rw [show ((s : ℂ) * (qC * z)) / (c * z₀ * dC) =
        c⁻¹ * ((s : ℂ) * qC / dC) * (z / z₀) by
          field_simp]
    rw [hrealC, hroot]
    rw [show c⁻¹ =
        ((1 / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) *
          Complex.exp (-(A ^ 2) / 8) by
      dsimp [c]
      push_cast
      field_simp
      rw [← Complex.exp_add]
      simp]
    rw [mul_assoc, ← Complex.exp_add]
    congr 1
    unfold routeCSaddleNearPhase
    ring
  unfold routeCSaddleNearRescaledNormalizedIntegrand
    routeCSaddleNearNormalizedProfile routeCSaddleIntegrand
    routeCSaddleComplexNormalizerOne
  rw [show (n : ℝ) + 1 - 1 = (n : ℝ) by ring]
  rw [show (((Real.rpow ((n : ℝ) + Real.sqrt (n : ℝ) * t) (n : ℝ) *
        Real.exp (-((n : ℝ) + Real.sqrt (n : ℝ) * t)) : ℝ) : ℂ)) = qC by
      rw [hqC]]
  rw [show Complex.exp (-A *
      (Real.sqrt ((n : ℝ) + Real.sqrt (n : ℝ) * t) : ℂ)) = z by rfl]
  rw [show (Real.sqrt (2 * Real.pi) : ℂ) * Complex.exp (A ^ 2 / 8) *
        Complex.exp (-A * (Real.sqrt (n : ℝ) : ℂ)) *
        Complex.exp (-((n : ℝ) : ℂ)) *
        (Real.rpow n ((n : ℝ) + 1 / 2) : ℂ) = c * z₀ * dC by
      dsimp [c, z₀, dC]
      ring]
  change (s : ℂ) * (qC * z) / (c * z₀ * dC) = _
  exact haux

theorem routeCSaddleNearSet_eq_Icc
    (delta : ℝ) (n : ℕ) (hn : 1 ≤ n) (hdelta : delta < 1) :
    routeCSaddleNearSet delta n =
      Icc ((1 - delta) * (n : ℝ)) ((1 + delta) * (n : ℝ)) := by
  have hnR : 0 < (n : ℝ) := by positivity
  have hlower : 0 < (1 - delta) * (n : ℝ) :=
    mul_pos (sub_pos.mpr hdelta) hnR
  ext u
  constructor
  · exact fun hu => hu.2
  · intro hu
    exact ⟨lt_of_lt_of_le hlower hu.1, hu⟩

theorem routeCSaddleNearIntegral_div_normalizer_eq_profile_integral
    (A : ℂ) (delta : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta < 1) :
    routeCSaddleNearIntegral A 1 delta n /
        routeCSaddleComplexNormalizerOne A n =
      ∫ t in (-delta * Real.sqrt (n : ℝ))..
          (delta * Real.sqrt (n : ℝ)),
        routeCSaddleNearNormalizedProfile A t n := by
  let s := Real.sqrt (n : ℝ)
  let f := routeCSaddleIntegrand A 1 n
  let z := routeCSaddleComplexNormalizerOne A n
  have hnR : 0 < (n : ℝ) := by positivity
  have hs : 0 < s := Real.sqrt_pos.2 hnR
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
  have hbounds : (1 - delta) * (n : ℝ) ≤ (1 + delta) * (n : ℝ) := by
    nlinarith
  have hnear : routeCSaddleNearIntegral A 1 delta n =
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
      (routeCSaddleNearNormalizedProfile A · n)
      (uIcc (-delta * s) (delta * s)) := by
    intro t ht
    have hab : -delta * s ≤ t ∧ t ≤ delta * s := by
      rw [uIcc_of_le (by nlinarith : -delta * s ≤ delta * s)] at ht
      exact ht
    have ht_lower : -s < t := by
      have : -s < -delta * s := by nlinarith
      linarith
    simpa only [s, f, z,
      routeCSaddleNearRescaledNormalizedIntegrand] using
        routeCSaddleNearRescaledNormalizedIntegrand_eq_profile
          A t n hn ht_lower
  rw [hnear, ← hchange]
  rw [← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_div]
  exact intervalIntegral.integral_congr hpoint

theorem routeCSaddleScaledEntropy_le_neg_sq_div_four
    (t : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (ht : |t| ≤ Real.sqrt (n : ℝ) / 8) :
    routeCSaddleScaledEntropy t n ≤ -(t ^ 2) / 4 := by
  let s := Real.sqrt (n : ℝ)
  have hnR : 0 < (n : ℝ) := by positivity
  have hs : 0 < s := Real.sqrt_pos.2 hnR
  have ht' : |t| ≤ s / 8 := by simpa only [s] using ht
  have hw : |t / Real.sqrt (n : ℝ)| < 1 / 2 := by
    rw [abs_div, abs_of_pos hs]
    calc
      |t| / s ≤ (s / 8) / s := div_le_div_of_nonneg_right ht' hs.le
      _ = 1 / 8 := by field_simp
      _ < 1 / 2 := by norm_num
  have herr := abs_routeCSaddleScaledEntropy_add_half_sq_le t n hn hw
  have hcubic : 2 * |t| ^ 3 / s ≤ t ^ 2 / 4 := by
    rw [div_le_iff₀ hs]
    have hfactor : 0 ≤ |t| ^ 2 * (s - 8 * |t|) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    rw [← sq_abs]
    nlinarith [hfactor]
  have hupper : routeCSaddleScaledEntropy t n + t ^ 2 / 2 ≤
      2 * |t| ^ 3 / s :=
    le_trans (le_abs_self _) (by simpa only [s] using herr)
  linarith

theorem abs_routeCSaddleScaledRootShift_le_nine_sixteen
    (t : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (ht : |t| ≤ Real.sqrt (n : ℝ) / 8) :
    |routeCSaddleScaledRootShift t n| ≤ 9 * |t| / 16 := by
  let s := Real.sqrt (n : ℝ)
  have hnR : 0 < (n : ℝ) := by positivity
  have hs : 0 < s := Real.sqrt_pos.2 hnR
  have ht' : |t| ≤ s / 8 := by simpa only [s] using ht
  have hw : |t / Real.sqrt (n : ℝ)| < 1 / 2 := by
    rw [abs_div, abs_of_pos hs]
    calc
      |t| / s ≤ (s / 8) / s := div_le_div_of_nonneg_right ht' hs.le
      _ = 1 / 8 := by field_simp
      _ < 1 / 2 := by norm_num
  have herr := abs_routeCSaddleScaledRootShift_sub_half_le t n hn hw
  have hquad : t ^ 2 / (2 * s) ≤ |t| / 16 := by
    rw [div_le_iff₀ (by positivity : 0 < 2 * s)]
    have hfactor : 0 ≤ |t| * (s - 8 * |t|) :=
      mul_nonneg (abs_nonneg _) (by linarith)
    rw [← sq_abs]
    nlinarith [hfactor]
  calc
    |routeCSaddleScaledRootShift t n| =
        |(routeCSaddleScaledRootShift t n - t / 2) + t / 2| := by
          congr 1
          ring
    _ ≤
        |routeCSaddleScaledRootShift t n - t / 2| + |t / 2| := by
      exact abs_add_le _ _
    _ ≤ t ^ 2 / (2 * s) + |t| / 2 := by
      exact add_le_add (by simpa only [s] using herr) (by
        rw [abs_div]
        norm_num)
    _ ≤ |t| / 16 + |t| / 2 := by
      simpa only [add_comm] using add_le_add_right hquad (|t| / 2)
    _ = 9 * |t| / 16 := by ring

theorem routeCSaddleNearPhase_re_le_gaussian
    (A : ℂ) (t : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (ht : |t| ≤ Real.sqrt (n : ℝ) / 8) :
    (routeCSaddleNearPhase A t n).re ≤
      -(t ^ 2) / 8 + 2 * ((9 / 16 : ℝ) * ‖A‖) ^ 2 := by
  have hentropy := routeCSaddleScaledEntropy_le_neg_sq_div_four t n hn ht
  have hroot := abs_routeCSaddleScaledRootShift_le_nine_sixteen t n hn ht
  let b : ℝ := (9 / 16 : ℝ) * ‖A‖
  have hproduct :
      |(A * (routeCSaddleScaledRootShift t n : ℂ)).re| ≤ b * |t| := by
    calc
      |(A * (routeCSaddleScaledRootShift t n : ℂ)).re| ≤
          ‖A * (routeCSaddleScaledRootShift t n : ℂ)‖ :=
        Complex.abs_re_le_norm _
      _ = ‖A‖ * |routeCSaddleScaledRootShift t n| := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ‖A‖ * (9 * |t| / 16) :=
        mul_le_mul_of_nonneg_left hroot (norm_nonneg _)
      _ = b * |t| := by dsimp [b]; ring
  have hyoung : b * |t| ≤ t ^ 2 / 8 + 2 * b ^ 2 := by
    have hsquare : 0 ≤ (|t| - 4 * b) ^ 2 := sq_nonneg _
    rw [← sq_abs]
    nlinarith [hsquare]
  unfold routeCSaddleNearPhase
  change routeCSaddleScaledEntropy t n -
      (A * (routeCSaddleScaledRootShift t n : ℂ)).re ≤ _
  calc
    routeCSaddleScaledEntropy t n -
        (A * (routeCSaddleScaledRootShift t n : ℂ)).re ≤
        routeCSaddleScaledEntropy t n +
          |(A * (routeCSaddleScaledRootShift t n : ℂ)).re| := by
      linarith [neg_abs_le (A * (routeCSaddleScaledRootShift t n : ℂ)).re]
    _ ≤ -(t ^ 2) / 4 + b * |t| := add_le_add hentropy hproduct
    _ ≤ -(t ^ 2) / 8 + 2 * b ^ 2 := by linarith

noncomputable def routeCSaddleNearProfilePrefactor (A : ℂ) : ℂ :=
  ((1 / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) *
    Complex.exp (-(A ^ 2) / 8)

noncomputable def routeCSaddleNearGaussianMajorant (A : ℂ) (t : ℝ) : ℝ :=
  ‖routeCSaddleNearProfilePrefactor A‖ *
    Real.exp (-(t ^ 2) / 8 + 2 * ((9 / 16 : ℝ) * ‖A‖) ^ 2)

theorem norm_routeCSaddleNearNormalizedProfile_le_majorant
    (A : ℂ) (t : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (ht : |t| ≤ Real.sqrt (n : ℝ) / 8) :
    ‖routeCSaddleNearNormalizedProfile A t n‖ ≤
      routeCSaddleNearGaussianMajorant A t := by
  have hphase := routeCSaddleNearPhase_re_le_gaussian A t n hn ht
  unfold routeCSaddleNearNormalizedProfile routeCSaddleNearGaussianMajorant
    routeCSaddleNearProfilePrefactor
  rw [norm_mul, Complex.norm_exp]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hphase) (norm_nonneg _)

theorem integrable_routeCSaddleNearGaussianMajorant (A : ℂ) :
    Integrable (routeCSaddleNearGaussianMajorant A) := by
  let C : ℝ := ‖routeCSaddleNearProfilePrefactor A‖ *
    Real.exp (2 * ((9 / 16 : ℝ) * ‖A‖) ^ 2)
  have hgauss : Integrable (fun t : ℝ => Real.exp (-(1 / 8 : ℝ) * t ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  have h := hgauss.const_mul C
  apply h.congr
  filter_upwards with t
  dsimp [C, routeCSaddleNearGaussianMajorant]
  rw [show -(1 / 8 : ℝ) * t ^ 2 = -(t ^ 2) / 8 by ring,
    Real.exp_add]
  ring

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleNearRescaling
