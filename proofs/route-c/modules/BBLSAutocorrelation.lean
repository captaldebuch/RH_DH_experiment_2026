import Mathlib
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninExplicitFormula
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninPeriodReduction
import RiemannHypothesis.Criteria.NymanBeurling.BBLSPhiOne

/-!
# BBLS §9: the autocorrelation function `A(λ)` and its value at `λ = 1`

Formalizes Proposition 87 of Báez-Duarte–Balazard–Landreau–Saias
(arXiv:math/0306251): `A(1) = ∫₀^∞ {t}²/t² dt = log 2π − γ`, plus the
integrability facts for the autocorrelation integrands on `(0, ∞)` needed by
the `x → ∞` limit of Proposition 22 (Proposition 88).

The evaluation follows the classical route: block integrals
`∫_n^{n+1} (t−n)²/t² dt = 1 − 2n·log((n+1)/n) + n/(n+1)` telescope to
`2N − H_N − 2N log N + 2 log N!`, and Stirling's formula
(`Stirling.tendsto_stirlingSeq_sqrt_pi`) together with the Euler–Mascheroni
limit (`Real.tendsto_eulerMascheroniSeq`) give the constant. All statements
were numerically verified (exact piecewise integration) before formalization.
-/

namespace RH.Criteria.NymanBeurling.VasyuninGram

open Finset Filter Topology MeasureTheory

/-! ## Integrability of the autocorrelation integrands on `(0, ∞)` -/

/-- The product integrand `{t}·{θt}/t²` is integrable on `(0, ∞)`. -/
theorem integrableOn_fract_mul_fract_div_sq {θ : ℝ} (hθ : 0 < θ) :
    IntegrableOn (fun t : ℝ => Int.fract t * Int.fract (θ * t) / t ^ 2)
      (Set.Ioi (0 : ℝ)) := by
  have hfle : ∀ y : ℝ, 0 ≤ y → Int.fract y ≤ y := by
    intro y hy
    have h0 : (0 : ℝ) ≤ (⌊y⌋ : ℝ) := by exact_mod_cast Int.floor_nonneg.mpr hy
    linarith [Int.self_sub_fract y]
  have hmeas : Measurable (fun t : ℝ => Int.fract t * Int.fract (θ * t) / t ^ 2) :=
    (measurable_fract.mul (measurable_id.const_mul θ).fract).div
      (measurable_id.pow_const 2)
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) :=
    (Set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit]
  apply IntegrableOn.union
  · -- bounded by θ on (0, 1]
    have h01 : IntervalIntegrable (fun t : ℝ => Int.fract t * Int.fract (θ * t) / t ^ 2)
        MeasureTheory.volume (0 : ℝ) 1 := by
      refine intervalIntegrable_of_bound_on_Ioc zero_le_one hmeas (C := θ) ?_
      intro u hu
      have hupos : 0 < u := hu.1
      have h1 := hfle u hupos.le
      have h2 := hfle (θ * u) (by positivity)
      have h3 := Int.fract_nonneg (θ * u)
      have h4 := Int.fract_nonneg u
      have hprod : Int.fract u * Int.fract (θ * u) ≤ u * (θ * u) :=
        mul_le_mul h1 h2 h3 hupos.le
      have hle : Int.fract u * Int.fract (θ * u) / u ^ 2 ≤ θ := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < u ^ 2)]
        nlinarith
      have hnn : 0 ≤ Int.fract u * Int.fract (θ * u) / u ^ 2 := by positivity
      rwa [abs_of_nonneg hnn]
    have := intervalIntegrable_iff.mp h01
    rwa [Set.uIoc_of_le zero_le_one] at this
  · -- dominated by t^(-2) on (1, ∞)
    have hmaj : IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Set.Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
    apply Integrable.mono' hmaj
    · exact hmeas.aestronglyMeasurable.restrict
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
      filter_upwards with t ht
      have ht1 : (1 : ℝ) < t := ht
      have htpos : 0 < t := lt_trans one_pos ht1
      have hf1 : Int.fract t < 1 := Int.fract_lt_one t
      have hf2 : Int.fract (θ * t) < 1 := Int.fract_lt_one (θ * t)
      have hf3 := Int.fract_nonneg t
      have hf4 := Int.fract_nonneg (θ * t)
      have hnn : 0 ≤ Int.fract t * Int.fract (θ * t) / t ^ 2 := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnn,
        Real.rpow_neg htpos.le, Real.rpow_two]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < t ^ 2)]
      have hinv : (t ^ 2)⁻¹ * t ^ 2 = 1 := by
        field_simp
      rw [hinv]
      nlinarith

/-- The square integrand `{t}²/t²` is integrable on `(0, ∞)`. -/
theorem integrableOn_fract_sq_div_sq :
    IntegrableOn (fun t : ℝ => (Int.fract t) ^ 2 / t ^ 2) (Set.Ioi (0 : ℝ)) := by
  have h := integrableOn_fract_mul_fract_div_sq (θ := 1) one_pos
  apply h.congr_fun ?_ measurableSet_Ioi
  intro t _
  simp [sq]

/-- Interval integrability of `{t}²/t²` from `0` to any nonnegative endpoint. -/
theorem intervalIntegrable_fract_sq_div_sq {x : ℝ} (hx : 0 ≤ x) :
    IntervalIntegrable (fun t : ℝ => (Int.fract t) ^ 2 / t ^ 2)
      MeasureTheory.volume (0 : ℝ) x := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
  exact integrableOn_fract_sq_div_sq.mono_set Set.Ioc_subset_Ioi_self

/-! ## Block evaluation of `∫_n^{n+1} {t}²/t² dt` -/

/-- On `[n, n+1]` with `n ≥ 1`, the block integral evaluates in closed form. -/
theorem fract_sq_block {n : ℕ} (hn : 1 ≤ n) :
    (∫ t in (n : ℝ)..((n : ℝ) + 1), (Int.fract t) ^ 2 / t ^ 2) =
      1 - 2 * n * Real.log (((n : ℝ) + 1) / n) + n / ((n : ℝ) + 1) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le one_pos hnR
  -- a.e. congruence to the polynomial-over-t² integrand
  have hcongr : (∫ t in (n : ℝ)..((n : ℝ) + 1), (Int.fract t) ^ 2 / t ^ 2) =
      ∫ t in (n : ℝ)..((n : ℝ) + 1), ((t - n) ^ 2 / t ^ 2) := by
    apply intervalIntegral.integral_congr_ae'
    · filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume ((n : ℝ) + 1)]
        with t ht_ne ht
      have htIoc : t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1) := ht
      have hfr : Int.fract t = t - n := by
        have hlt : t < (n : ℝ) + 1 := lt_of_le_of_ne htIoc.2 ht_ne
        have hfloor : ⌊t⌋ = (n : ℤ) := by
          apply Int.floor_eq_iff.mpr
          constructor
          · exact_mod_cast htIoc.1.le
          · exact_mod_cast hlt
        rw [Int.fract, hfloor]
        push_cast
        ring
      rw [hfr]
    · filter_upwards with t ht
      exfalso
      have h1 : ((n : ℝ) + 1) < t := ht.1
      have h2 : t ≤ (n : ℝ) := ht.2
      linarith
  rw [hcongr]
  -- FTC with the explicit antiderivative F(t) = t − 2n log t − n²/t
  have hderiv : ∀ t ∈ Set.uIcc (n : ℝ) ((n : ℝ) + 1),
      HasDerivAt (fun t : ℝ => t - 2 * n * Real.log t - (n : ℝ) ^ 2 / t)
        ((t - n) ^ 2 / t ^ 2) t := by
    intro t ht
    have htIcc : t ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1) := by
      rwa [Set.uIcc_of_le (by linarith)] at ht
    have htpos : 0 < t := lt_of_lt_of_le hnpos htIcc.1
    have h1 : HasDerivAt (fun t : ℝ => t) 1 t := hasDerivAt_id t
    have h2 : HasDerivAt (fun t : ℝ => Real.log t) (1 / t) t := by
      simpa [one_div] using Real.hasDerivAt_log htpos.ne'
    have h3 : HasDerivAt (fun t : ℝ => (n : ℝ) ^ 2 / t) (-(n : ℝ) ^ 2 / t ^ 2) t := by
      have hinv := hasDerivAt_inv htpos.ne'
      have h4 := hinv.const_mul ((n : ℝ) ^ 2)
      have hfun : (fun y : ℝ => (n : ℝ) ^ 2 * y⁻¹) = fun y : ℝ => (n : ℝ) ^ 2 / y := by
        funext y
        rw [div_eq_mul_inv]
      rw [hfun] at h4
      convert h4 using 1
      field_simp
    have hcomb := (h1.sub ((h2.const_mul (2 * (n : ℝ))))).sub h3
    convert hcomb using 1
    field_simp
    ring
  have hint : IntervalIntegrable (fun t : ℝ => (t - n) ^ 2 / t ^ 2)
      MeasureTheory.volume (n : ℝ) ((n : ℝ) + 1) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro t ht
      have htIcc : t ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1) := by
        rwa [Set.uIcc_of_le (by linarith)] at ht
      have : 0 < t := lt_of_lt_of_le hnpos htIcc.1
      positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hlog : Real.log (((n : ℝ) + 1) / n) = Real.log ((n : ℝ) + 1) - Real.log n :=
    Real.log_div (by positivity) (by positivity)
  rw [hlog]
  field_simp
  ring

/-- The first block `∫_0^1 {t}²/t² dt = 1`. -/
theorem fract_sq_block_zero :
    (∫ t in (0 : ℝ)..1, (Int.fract t) ^ 2 / t ^ 2) = 1 := by
  have hcongr : (∫ t in (0 : ℝ)..1, (Int.fract t) ^ 2 / t ^ 2) =
      ∫ _t in (0 : ℝ)..1, (1 : ℝ) := by
    apply intervalIntegral.integral_congr_ae'
    · filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (1 : ℝ)]
        with t ht_ne ht
      have htIoc : t ∈ Set.Ioc (0 : ℝ) 1 := ht
      have hlt : t < 1 := lt_of_le_of_ne htIoc.2 ht_ne
      have hfr : Int.fract t = t := Int.fract_eq_self.mpr ⟨htIoc.1.le, hlt⟩
      rw [hfr]
      have htpos : 0 < t := htIoc.1
      field_simp
    · filter_upwards with t ht
      exfalso
      have h1 : (1 : ℝ) < t := ht.1
      have h2 : t ≤ 0 := ht.2
      linarith
  rw [hcongr]
  simp

/-! ## The partial-sum closed form and the limit -/

/-- `∫_0^N {t}²/t² dt = 2N − H_N − 2N·log N + 2·log N!`. -/
theorem fract_sq_integral_nat (N : ℕ) :
    (∫ t in (0 : ℝ)..(N : ℝ), (Int.fract t) ^ 2 / t ^ 2) =
      2 * N - (harmonic N : ℝ) - 2 * N * Real.log N + 2 * Real.log ((Nat.factorial N : ℕ) : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hsplit : (∫ t in (0 : ℝ)..((N + 1 : ℕ) : ℝ), (Int.fract t) ^ 2 / t ^ 2) =
          (∫ t in (0 : ℝ)..(N : ℝ), (Int.fract t) ^ 2 / t ^ 2) +
            ∫ t in (N : ℝ)..((N : ℝ) + 1), (Int.fract t) ^ 2 / t ^ 2 := by
        have h1 : IntervalIntegrable (fun t : ℝ => (Int.fract t) ^ 2 / t ^ 2)
            MeasureTheory.volume (0 : ℝ) (N : ℝ) :=
          intervalIntegrable_fract_sq_div_sq (by positivity)
        have h2 : IntervalIntegrable (fun t : ℝ => (Int.fract t) ^ 2 / t ^ 2)
            MeasureTheory.volume (N : ℝ) ((N : ℝ) + 1) := by
          have h3 := intervalIntegrable_fract_sq_div_sq
            (x := (N : ℝ) + 1) (by positivity)
          have h4 := intervalIntegrable_fract_sq_div_sq (x := (N : ℝ)) (by positivity)
          exact (h4.symm.trans h3)
        have hadd := intervalIntegral.integral_add_adjacent_intervals h1 h2
        rw [show (((N + 1 : ℕ)) : ℝ) = (N : ℝ) + 1 by push_cast; ring]
        exact hadd.symm
      rw [hsplit, ih]
      rcases Nat.eq_zero_or_pos N with hN0 | hNpos
      · subst hN0
        have hz1 : (∫ t in ((0 : ℕ) : ℝ)..(((0 : ℕ) : ℝ) + 1), (Int.fract t) ^ 2 / t ^ 2) =
            (1 : ℝ) := by
          rw [show ((0 : ℕ) : ℝ) = (0 : ℝ) by norm_num]
          rw [show (0 : ℝ) + 1 = 1 by norm_num]
          exact fract_sq_block_zero
        rw [hz1]
        norm_num [harmonic_succ, harmonic_zero, Nat.factorial]
      · rw [fract_sq_block hNpos]
        have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
        have hlog_div : Real.log (((N : ℝ) + 1) / N) =
            Real.log ((N : ℝ) + 1) - Real.log N := Real.log_div (by positivity) (by positivity)
        have hfact : Real.log ((Nat.factorial (N + 1) : ℕ) : ℝ) =
            Real.log ((N : ℝ) + 1) + Real.log ((Nat.factorial N : ℕ) : ℝ) := by
          have hfp : (0 : ℝ) < ((Nat.factorial N : ℕ) : ℝ) := by
            exact_mod_cast Nat.factorial_pos N
          rw [Nat.factorial_succ]
          push_cast
          rw [Real.log_mul (by positivity) hfp.ne']
        have hharm : ((harmonic (N + 1) : ℚ) : ℝ) = (harmonic N : ℝ) + 1 / ((N : ℝ) + 1) := by
          rw [harmonic_succ]
          push_cast
          ring
        rw [hharm, hfact, hlog_div]
        have h1N : ((N : ℝ) + 1) ≠ 0 := by positivity
        push_cast
        field_simp
        ring

/-- The `N → ∞` limit: `∫_0^N {t}²/t² dt → log 2π − γ`. -/
theorem tendsto_fract_sq_integral_nat :
    Tendsto (fun N : ℕ => ∫ t in (0 : ℝ)..(N : ℝ), (Int.fract t) ^ 2 / t ^ 2) atTop
      (𝓝 (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant)) := by
  -- rewrite via the closed form and Stirling
  have hstirling := Stirling.tendsto_stirlingSeq_sqrt_pi
  have hlogstirling : Tendsto (fun N : ℕ => Real.log (Stirling.stirlingSeq N)) atTop
      (𝓝 (Real.log (Real.sqrt Real.pi))) := by
    apply Filter.Tendsto.log hstirling
    positivity
  have hgamma := Real.tendsto_eulerMascheroniSeq
  -- log(N+1) − log N → 0
  have hlogshift : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1) - Real.log N) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => ((N : ℝ) + 1) / N) atTop (𝓝 1) := by
      have h2 : (fun N : ℕ => ((N : ℝ) + 1) / N) =ᶠ[atTop] fun N : ℕ => 1 + 1 / N := by
        filter_upwards [eventually_ge_atTop 1] with N hN
        have hNR : (0 : ℝ) < N := by exact_mod_cast hN
        field_simp
      rw [tendsto_congr' h2]
      have h3 : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) := by
        simpa [one_div] using tendsto_natCast_atTop_atTop.inv_tendsto_atTop
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add h3
    have h4 : Tendsto (fun N : ℕ => Real.log (((N : ℝ) + 1) / N)) atTop (𝓝 0) := by
      have := Filter.Tendsto.log h1 one_ne_zero
      simpa using this
    apply h4.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    rw [Real.log_div (by positivity) (by positivity)]
  -- (log N − H_N) → −γ
  have hHN : Tendsto (fun N : ℕ => Real.log N - (harmonic N : ℝ)) atTop
      (𝓝 (-Real.eulerMascheroniConstant)) := by
    have h1 : (fun N : ℕ => Real.log N - (harmonic N : ℝ)) =
        fun N : ℕ => -(Real.eulerMascheroniSeq N) - (Real.log ((N : ℝ) + 1) - Real.log N) := by
      funext N
      unfold Real.eulerMascheroniSeq
      ring
    rw [h1]
    have := (hgamma.neg).sub hlogshift
    simpa using this
  -- combine
  have hcomb : Tendsto (fun N : ℕ =>
      (Real.log N - (harmonic N : ℝ)) + 2 * Real.log (Stirling.stirlingSeq N) + Real.log 2)
      atTop (𝓝 (-Real.eulerMascheroniConstant + 2 * Real.log (Real.sqrt Real.pi) +
        Real.log 2)) := by
    exact (hHN.add (hlogstirling.const_mul 2)).add tendsto_const_nhds
  have hconst : -Real.eulerMascheroniConstant + 2 * Real.log (Real.sqrt Real.pi) +
      Real.log 2 = Real.log (2 * Real.pi) - Real.eulerMascheroniConstant := by
    rw [Real.log_sqrt Real.pi_pos.le, Real.log_mul (by norm_num) Real.pi_pos.ne']
    ring
  rw [hconst] at hcomb
  -- identify with the closed form, eventually in N
  apply hcomb.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hfactpos : (0 : ℝ) < ((Nat.factorial N : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos N
  rw [fract_sq_integral_nat N]
  have hstirlingN := Stirling.log_stirlingSeq_formula N
  have hlogNe : Real.log ((N : ℝ) / Real.exp 1) = Real.log N - 1 := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_exp]
  have hlog2N : Real.log (2 * (N : ℝ)) = Real.log 2 + Real.log N :=
    Real.log_mul (by norm_num) (by positivity)
  rw [hlogNe, hlog2N] at hstirlingN
  -- hstirlingN : log stirlingSeq N = log N! − 1/2(log2 + logN) − N(logN − 1)
  have hexpand : Real.log ((Nat.factorial N : ℕ) : ℝ) =
      Real.log (Stirling.stirlingSeq N) + 1 / 2 * (Real.log 2 + Real.log N) +
        (N : ℝ) * (Real.log N - 1) := by
    linarith [hstirlingN]
  rw [hexpand]
  ring

/-- **BBLS Proposition 87**: `A(1) = ∫_{(0,∞)} {t}²/t² dt = log 2π − γ`. -/
theorem bbls_A_one :
    (∫ t in Set.Ioi (0 : ℝ), (Int.fract t) ^ 2 / t ^ 2) =
      Real.log (2 * Real.pi) - Real.eulerMascheroniConstant := by
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h1 := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (0 : ℝ)
    integrableOn_fract_sq_div_sq hcast
  exact tendsto_nhds_unique h1 tendsto_fract_sq_integral_nat

/-! ## The `x → ∞` limit of Proposition 22 (BBLS Propositions 88–89 at rationals) -/

/-- The middle interval `∫_x^{θx} {t}/t² dt` vanishes as `x → ∞`. -/
theorem tendsto_fract_div_sq_interval_zero {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun x : ℝ => ∫ t in x..(θ * x), Int.fract t / t ^ 2) atTop (𝓝 0) := by
  have hkey : ∀ a b : ℝ, 0 < a → a ≤ b →
      |∫ t in a..b, Int.fract t / t ^ 2| ≤ 1 / a - 1 / b := by
    intro a b ha hab
    have hb : (0 : ℝ) < b := lt_of_lt_of_le ha hab
    have hfint : IntervalIntegrable (fun t : ℝ => Int.fract t / t ^ 2)
        MeasureTheory.volume a b := by
      have := fract_mul_div_sq_intervalIntegrable (c := 1) (a := a) (b := b)
        (lt_min ha hb)
      simpa [one_mul] using this
    have hgint : IntervalIntegrable (fun t : ℝ => 1 / t ^ 2)
        MeasureTheory.volume a b := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro t ht
      have htIcc : t ∈ Set.Icc a b := by rwa [Set.uIcc_of_le hab] at ht
      have : 0 < t := lt_of_lt_of_le ha htIcc.1
      positivity
    have hmono : (∫ t in a..b, Int.fract t / t ^ 2) ≤ ∫ t in a..b, 1 / t ^ 2 := by
      apply intervalIntegral.integral_mono_on hab hfint hgint
      intro t htIcc
      have htpos : 0 < t := lt_of_lt_of_le ha htIcc.1
      gcongr
      exact (Int.fract_lt_one t).le
    have hnonneg : (0 : ℝ) ≤ ∫ t in a..b, Int.fract t / t ^ 2 := by
      apply intervalIntegral.integral_nonneg hab
      intro u huIcc
      have hupos : 0 < u := lt_of_lt_of_le ha huIcc.1
      have := Int.fract_nonneg u
      positivity
    have hval : (∫ t in a..b, 1 / t ^ 2) = 1 / a - 1 / b := by
      have := intervalIntegral_const_div_sq 1 a b ha hb
      simpa using this
    rw [abs_of_nonneg hnonneg]
    rw [hval] at hmono
    exact hmono
  have hb : ∀ᶠ x : ℝ in atTop, ‖∫ t in x..(θ * x), Int.fract t / t ^ 2‖ ≤
      |1 / x - 1 / (θ * x)| := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hθx : (0 : ℝ) < θ * x := by positivity
    rcases le_total x (θ * x) with hle | hle
    · have h1 := hkey x (θ * x) hx hle
      rw [Real.norm_eq_abs]
      calc |∫ t in x..(θ * x), Int.fract t / t ^ 2| ≤ 1 / x - 1 / (θ * x) := h1
        _ ≤ |1 / x - 1 / (θ * x)| := le_abs_self _
    · have h1 := hkey (θ * x) x hθx hle
      rw [Real.norm_eq_abs, intervalIntegral.integral_symm, abs_neg]
      calc |∫ t in (θ * x)..x, Int.fract t / t ^ 2| ≤ 1 / (θ * x) - 1 / x := h1
        _ ≤ |1 / (θ * x) - 1 / x| := le_abs_self _
        _ = |1 / x - 1 / (θ * x)| := abs_sub_comm _ _
  refine squeeze_zero_norm' hb ?_
  · have h1 : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := by
      simpa [one_div] using tendsto_inv_atTop_zero (𝕜 := ℝ)
    have h2 : Tendsto (fun x : ℝ => 1 / (θ * x)) atTop (𝓝 0) := by
      have hθmul : Tendsto (fun x : ℝ => θ * x) atTop atTop :=
        Tendsto.const_mul_atTop hθ tendsto_id
      simpa only [one_div] using hθmul.inv_tendsto_atTop
    have h3 := (h1.sub h2).abs
    simpa using h3

/-- Generic squeeze: `(1/(cx))·Δ(x) → 0` for eventually-bounded `Δ`. -/
theorem tendsto_one_div_mul_bounded_zero (C c : ℝ) (_hC : 0 ≤ C) (hc : 0 < c)
    (Δ : ℝ → ℝ) (hΔ : ∀ x : ℝ, 1 ≤ x → |Δ x| ≤ C) :
    Tendsto (fun x : ℝ => 1 / (c * x) * Δ x) atTop (𝓝 0) := by
  have hb : ∀ᶠ x : ℝ in atTop, ‖1 / (c * x) * Δ x‖ ≤ C / (c * x) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hxpos : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
    have hcx : (0 : ℝ) < c * x := by positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (c * x))]
    calc 1 / (c * x) * |Δ x| ≤ 1 / (c * x) * C := by
          apply mul_le_mul_of_nonneg_left (hΔ x hx) (by positivity)
      _ = C / (c * x) := by ring
  refine squeeze_zero_norm' hb ?_
  · have hmul : Tendsto (fun x : ℝ => c * x) atTop atTop :=
      Tendsto.const_mul_atTop hc tendsto_id
    have h2 : Tendsto (fun x : ℝ => C * (c * x)⁻¹) atTop (𝓝 (C * 0)) :=
      tendsto_const_nhds.mul hmul.inv_tendsto_atTop
    simpa [div_eq_mul_inv] using h2

/-- **BBLS Propositions 88–89 fused, at an arbitrary positive rational** `θ = k/h`
(coprimality NOT required — numerically verified for non-coprime pairs): the
autocorrelation integral `A(k/h) = ∫₀^∞ {t}{(k/h)t}/t² dt` in closed form. -/
theorem bbls_A_rat (h k : ℕ) (hh : 0 < h) (hk : 0 < k) :
    (∫ t in Set.Ioi (0 : ℝ), Int.fract t * Int.fract (((k : ℝ) / (h : ℝ)) * t) / t ^ 2) =
      (1 - (k : ℝ) / h) / 2 * Real.log ((k : ℝ) / h) +
        ((k : ℝ) / h + 1) / 2 * (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) -
        Real.pi / (2 * h) * cotangentSumVFormula k h -
        ((k : ℝ) / h) * (Real.pi / (2 * k) * cotangentSumVFormula h k) := by
  set θ : ℝ := (k : ℝ) / (h : ℝ) with hθdef
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hθpos : 0 < θ := by rw [hθdef]; positivity
  -- the reduced coprime representation, for Proposition 22
  set d : ℕ := Nat.gcd h k with hddef
  have hd : 0 < d := Nat.gcd_pos_of_pos_left k hh
  set h' : ℕ := h / d with hh'def
  set k' : ℕ := k / d with hk'def
  have hh' : 0 < h' := Nat.div_pos (Nat.le_of_dvd hh (Nat.gcd_dvd_left h k)) hd
  have hk' : 0 < k' := Nat.div_pos (Nat.le_of_dvd hk (Nat.gcd_dvd_right h k)) hd
  have hcop : Nat.Coprime h' k' := Nat.coprime_div_gcd_div_gcd hd
  have hkd : (k' : ℝ) * d = k := by
    exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_right h k)
  have hhd : (h' : ℝ) * d = h := by
    exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_left h k)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hh'R : (0 : ℝ) < h' := by exact_mod_cast hh'
  have hθeq : θ = (k' : ℝ) / (h' : ℝ) := by
    rw [hθdef, ← hkd, ← hhd]
    field_simp
  -- Proposition 22 restated for θ
  have h22 : ∀ x : ℝ, 0 < x →
      (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, bernoulliB1 ((m : ℝ) * θ) / (m : ℝ)) +
        θ * (∑ n ∈ Finset.Icc 1 ⌊θ * x⌋₊, bernoulliB1 ((n : ℝ) / θ) / (n : ℝ)) =
      (θ / 2) * (∫ t in (0 : ℝ)..x, (Int.fract t) ^ 2 / t ^ 2) +
        (1 / 2) * (∫ t in (0 : ℝ)..(θ * x), (Int.fract t) ^ 2 / t ^ 2) -
        (∫ t in (0 : ℝ)..x, (Int.fract t * Int.fract (θ * t)) / t ^ 2) +
        ((θ - 1) / 2) * Real.log (1 / θ) +
        ((θ - 1) / 2) * (∫ t in x..(θ * x), Int.fract t / t ^ 2) +
        (1 / (2 * θ * x)) * (Int.fract (θ * x) - θ * Int.fract x) ^ 2 +
        ((θ - 1) / (2 * θ * x)) * (Int.fract (θ * x) - θ * Int.fract x) := by
    intro x hx
    rw [hθeq]
    exact baezDuarte_prop22_rat hh' hk' hcop x hx
  -- limits of the integral pieces
  have hIθmul : Tendsto (fun x : ℝ => θ * x) atTop atTop :=
    Tendsto.const_mul_atTop hθpos tendsto_id
  have hI1 : Tendsto (fun x : ℝ => ∫ t in (0 : ℝ)..x, (Int.fract t) ^ 2 / t ^ 2) atTop
      (𝓝 (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant)) := by
    have h1 := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (0 : ℝ)
      integrableOn_fract_sq_div_sq tendsto_id
    rwa [bbls_A_one] at h1
  have hI2 : Tendsto (fun x : ℝ => ∫ t in (0 : ℝ)..(θ * x), (Int.fract t) ^ 2 / t ^ 2) atTop
      (𝓝 (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant)) := by
    have h1 := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (0 : ℝ)
      integrableOn_fract_sq_div_sq hIθmul
    rwa [bbls_A_one] at h1
  have hI3 : Tendsto (fun x : ℝ =>
      ∫ t in (0 : ℝ)..x, (Int.fract t * Int.fract (θ * t)) / t ^ 2) atTop
      (𝓝 (∫ t in Set.Ioi (0 : ℝ), Int.fract t * Int.fract (θ * t) / t ^ 2)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi (0 : ℝ)
      (integrableOn_fract_mul_fract_div_sq hθpos) tendsto_id
  have hI5 := tendsto_fract_div_sq_interval_zero hθpos
  -- boundary terms
  have hΔbdd : ∀ x : ℝ, 1 ≤ x → |Int.fract (θ * x) - θ * Int.fract x| ≤ 1 + θ := by
    intro x hx
    have h1 := Int.fract_nonneg (θ * x)
    have h2 := (Int.fract_lt_one (θ * x)).le
    have h3 := Int.fract_nonneg x
    have h4 := (Int.fract_lt_one x).le
    have h5 : 0 ≤ θ * Int.fract x := mul_nonneg hθpos.le h3
    have h6 : θ * Int.fract x ≤ θ := by nlinarith
    rw [abs_le]
    constructor <;> linarith
  have hB1 : Tendsto (fun x : ℝ =>
      1 / (2 * θ * x) * (Int.fract (θ * x) - θ * Int.fract x) ^ 2) atTop (𝓝 0) := by
    apply tendsto_one_div_mul_bounded_zero ((1 + θ) ^ 2) (2 * θ) (by positivity)
      (by positivity)
    intro x hx
    have h1 := hΔbdd x hx
    rw [abs_pow]
    nlinarith [abs_nonneg (Int.fract (θ * x) - θ * Int.fract x)]
  have hB2 : Tendsto (fun x : ℝ =>
      (θ - 1) / (2 * θ * x) * (Int.fract (θ * x) - θ * Int.fract x)) atTop (𝓝 0) := by
    have hbound : ∀ x : ℝ, 1 ≤ x →
        |(θ - 1) * (Int.fract (θ * x) - θ * Int.fract x)| ≤ |θ - 1| * (1 + θ) := by
      intro x hx
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hΔbdd x hx) (abs_nonneg _)
    have hgen := tendsto_one_div_mul_bounded_zero (|θ - 1| * (1 + θ)) (2 * θ)
      (by positivity) (by positivity) _ hbound
    apply Tendsto.congr ?_ hgen
    intro x
    ring
  -- limits of the two series (Stage A, at the NON-reduced representations)
  have hA1 : Tendsto (fun x : ℝ =>
      ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, bernoulliB1 ((m : ℝ) * θ) / (m : ℝ)) atTop
      (𝓝 (Real.pi / (2 * h) * cotangentSumVFormula k h)) := by
    have h1 := (tendsto_bernoulliB1_sum_div_rat k h hk hh).comp
      (tendsto_nat_floor_atTop (α := ℝ))
    simp only [Function.comp_def] at h1
    have h2 : ∀ x : ℝ, (∑ m ∈ Finset.Icc 1 ⌊x⌋₊,
        bernoulliB1 ((m : ℝ) * ((k : ℝ) / h)) / (m : ℝ)) =
        ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, bernoulliB1 ((m : ℝ) * θ) / (m : ℝ) := by
      intro x
      rfl
    exact Tendsto.congr h2 h1
  have hA2 : Tendsto (fun x : ℝ =>
      ∑ n ∈ Finset.Icc 1 ⌊θ * x⌋₊, bernoulliB1 ((n : ℝ) / θ) / (n : ℝ)) atTop
      (𝓝 (Real.pi / (2 * k) * cotangentSumVFormula h k)) := by
    have h1 := (tendsto_bernoulliB1_sum_div_rat h k hh hk).comp
      ((tendsto_nat_floor_atTop (α := ℝ)).comp hIθmul)
    simp only [Function.comp_def] at h1
    apply Tendsto.congr ?_ h1
    intro x
    apply Finset.sum_congr rfl
    intro n _
    have harg : (n : ℝ) * ((h : ℝ) / k) = (n : ℝ) / θ := by
      rw [hθdef]
      field_simp
    rw [harg]
  -- combine
  have hLHS := hA1.add (hA2.const_mul θ)
  have hRHS := ((((((hI1.const_mul (θ / 2)).add (hI2.const_mul (1 / 2))).sub hI3).add
    (tendsto_const_nhds (x := (θ - 1) / 2 * Real.log (1 / θ)))).add
      (hI5.const_mul ((θ - 1) / 2))).add hB1).add hB2
  have hEq : (fun x : ℝ =>
      (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, bernoulliB1 ((m : ℝ) * θ) / (m : ℝ)) +
        θ * (∑ n ∈ Finset.Icc 1 ⌊θ * x⌋₊, bernoulliB1 ((n : ℝ) / θ) / (n : ℝ)))
      =ᶠ[atTop] (fun x : ℝ =>
      (θ / 2) * (∫ t in (0 : ℝ)..x, (Int.fract t) ^ 2 / t ^ 2) +
        (1 / 2) * (∫ t in (0 : ℝ)..(θ * x), (Int.fract t) ^ 2 / t ^ 2) -
        (∫ t in (0 : ℝ)..x, (Int.fract t * Int.fract (θ * t)) / t ^ 2) +
        ((θ - 1) / 2) * Real.log (1 / θ) +
        ((θ - 1) / 2) * (∫ t in x..(θ * x), Int.fract t / t ^ 2) +
        (1 / (2 * θ * x)) * (Int.fract (θ * x) - θ * Int.fract x) ^ 2 +
        ((θ - 1) / (2 * θ * x)) * (Int.fract (θ * x) - θ * Int.fract x)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact h22 x hx
  have hLHS' := Filter.Tendsto.congr' hEq hLHS
  have hkey := tendsto_nhds_unique hLHS' hRHS
  have hlog : Real.log (1 / θ) = -Real.log θ := by
    rw [one_div, Real.log_inv]
  rw [hlog] at hkey
  linear_combination hkey


/-! ## Period unfolding: the shifted-integral tsum equals the Vasyunin entry -/

/-- The two-period integrand `{s/h}{s/k}/s²` is integrable on `(0, ∞)`. -/
theorem integrableOn_fract_two_div_sq (h k : ℕ) (hh : 0 < h) (hk : 0 < k) :
    IntegrableOn (fun s : ℝ => Int.fract (s / (h : ℝ)) * Int.fract (s / (k : ℝ)) / s ^ 2)
      (Set.Ioi (0 : ℝ)) := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hfle : ∀ y : ℝ, 0 ≤ y → Int.fract y ≤ y := by
    intro y hy
    have h0 : (0 : ℝ) ≤ (⌊y⌋ : ℝ) := by exact_mod_cast Int.floor_nonneg.mpr hy
    linarith [Int.self_sub_fract y]
  have hmeas : Measurable (fun s : ℝ => Int.fract (s / (h : ℝ)) * Int.fract (s / (k : ℝ)) / s ^ 2) :=
    ((measurable_id.div_const (h : ℝ)).fract.mul
      (measurable_id.div_const (k : ℝ)).fract).div (measurable_id.pow_const 2)
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) :=
    (Set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit]
  apply IntegrableOn.union
  · have h01 : IntervalIntegrable
        (fun s : ℝ => Int.fract (s / (h : ℝ)) * Int.fract (s / (k : ℝ)) / s ^ 2)
        MeasureTheory.volume (0 : ℝ) 1 := by
      refine intervalIntegrable_of_bound_on_Ioc zero_le_one hmeas
        (C := 1 / ((h : ℝ) * k)) ?_
      intro u hu
      have hupos : 0 < u := hu.1
      have h1 := hfle (u / h) (by positivity)
      have h2 := hfle (u / k) (by positivity)
      have h3 := Int.fract_nonneg (u / (h : ℝ))
      have h4 := Int.fract_nonneg (u / (k : ℝ))
      have hprod : Int.fract (u / (h : ℝ)) * Int.fract (u / (k : ℝ)) ≤ (u / h) * (u / k) :=
        mul_le_mul h1 h2 h4 (by positivity)
      have hle : Int.fract (u / (h : ℝ)) * Int.fract (u / (k : ℝ)) / u ^ 2 ≤ 1 / ((h : ℝ) * k) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hexp : (u / h) * (u / k) * ((h : ℝ) * k) = u ^ 2 := by
          field_simp
        nlinarith [mul_le_mul_of_nonneg_right hprod
          (by positivity : (0 : ℝ) ≤ (h : ℝ) * k)]
      have hnn : 0 ≤ Int.fract (u / (h : ℝ)) * Int.fract (u / (k : ℝ)) / u ^ 2 := by positivity
      rwa [abs_of_nonneg hnn]
    have h02 := intervalIntegrable_iff.mp h01
    rwa [Set.uIoc_of_le zero_le_one] at h02
  · have hmaj : IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Set.Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
    apply Integrable.mono' hmaj
    · exact hmeas.aestronglyMeasurable.restrict
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
      filter_upwards with t ht
      have ht1 : (1 : ℝ) < t := ht
      have htpos : 0 < t := lt_trans one_pos ht1
      have hf1 : Int.fract (t / (h : ℝ)) < 1 := Int.fract_lt_one _
      have hf2 : Int.fract (t / (k : ℝ)) < 1 := Int.fract_lt_one _
      have hf3 := Int.fract_nonneg (t / (h : ℝ))
      have hf4 := Int.fract_nonneg (t / (k : ℝ))
      have hnn : 0 ≤ Int.fract (t / (h : ℝ)) * Int.fract (t / (k : ℝ)) / t ^ 2 := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnn, Real.rpow_neg htpos.le, Real.rpow_two]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < t ^ 2)]
      have hinv : (t ^ 2)⁻¹ * t ^ 2 = 1 := by field_simp
      rw [hinv]
      nlinarith

/-- Period unfolding: the tsum of shifted slice integrals is the improper integral. -/
theorem bbls_period_unfolding (h k : ℕ) (hh : 0 < h) (hk : 0 < k) :
    (∑' n : ℕ, ∫ s in Set.Ioc (0 : ℝ) (Nat.lcm h k : ℝ),
        Int.fract (s / (h : ℝ)) * Int.fract (s / (k : ℝ)) /
          ((n : ℝ) * (Nat.lcm h k : ℝ) + s) ^ 2)
      = ∫ s in Set.Ioi (0 : ℝ),
          Int.fract (s / (h : ℝ)) * Int.fract (s / (k : ℝ)) / s ^ 2 := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  set L : ℕ := Nat.lcm h k with hLdef
  have hL : 0 < L := Nat.pos_of_ne_zero (Nat.lcm_ne_zero hh.ne' hk.ne')
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  set g : ℝ → ℝ := fun s => Int.fract (s / (h : ℝ)) * Int.fract (s / (k : ℝ)) / s ^ 2
    with hgdef
  -- fract periodicity under shifts by multiples of L
  have hper : ∀ (m : ℕ) (hdvd : (m : ℕ) ∣ L) (n : ℕ) (u : ℝ),
      Int.fract ((u + (n : ℝ) * L) / (m : ℝ)) = Int.fract (u / (m : ℝ)) := by
    intro m hdvd n u
    obtain ⟨c, hc⟩ := hdvd
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      simp
    · have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
      have hcast : (u + (n : ℝ) * L) / (m : ℝ) = u / m + ((n * c : ℕ) : ℝ) := by
        rw [hc]
        push_cast
        field_simp
      rw [hcast, Int.fract_add_natCast]
  -- each slice integral is the integral of g over the shifted block
  have hslice : ∀ n : ℕ,
      (∫ s in Set.Ioc (0 : ℝ) (L : ℝ),
        Int.fract (s / (h : ℝ)) * Int.fract (s / (k : ℝ)) / ((n : ℝ) * L + s) ^ 2)
      = ∫ s in Set.Ioc ((n : ℝ) * L) ((n : ℝ) * L + L), g s := by
    intro n
    have hle1 : (0 : ℝ) ≤ (L : ℝ) := hLR.le
    have hle2 : (n : ℝ) * L ≤ (n : ℝ) * L + L := by linarith
    rw [← intervalIntegral.integral_of_le hle1, ← intervalIntegral.integral_of_le hle2]
    have hcongr : (∫ s in (0 : ℝ)..(L : ℝ),
        Int.fract (s / (h : ℝ)) * Int.fract (s / (k : ℝ)) / ((n : ℝ) * L + s) ^ 2)
        = ∫ s in (0 : ℝ)..(L : ℝ), g (s + (n : ℝ) * L) := by
      apply intervalIntegral.integral_congr
      intro s _
      rw [hgdef]
      simp only
      rw [hper h (Nat.dvd_lcm_left h k) n s, hper k (Nat.dvd_lcm_right h k) n s]
      congr 1
      ring
    rw [hcongr]
    have hcomp := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := (L : ℝ))
      (f := g) ((n : ℝ) * L)
    rw [hcomp]
    congr 1 <;> ring
  -- the blocks partition (0, ∞)
  have hunion : (⋃ n : ℕ, Set.Ioc ((n : ℝ) * L) ((n : ℝ) * L + L)) = Set.Ioi (0 : ℝ) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro ⟨n, hn1, _⟩
      have : (0 : ℝ) ≤ (n : ℝ) * L := by positivity
      linarith
    · intro hx
      have hxL : 0 < x / (L : ℝ) := by positivity
      have hceil : 1 ≤ ⌈x / (L : ℝ)⌉₊ := Nat.one_le_ceil_iff.mpr hxL
      refine ⟨⌈x / (L : ℝ)⌉₊ - 1, ?_, ?_⟩
      · have hlt : ((⌈x / (L : ℝ)⌉₊ - 1 : ℕ) : ℝ) < x / L := by
          rw [Nat.cast_sub hceil]
          push_cast
          have := Nat.ceil_lt_add_one hxL.le
          have h2 : (⌈x / (L : ℝ)⌉₊ : ℝ) < x / L + 1 := this
          linarith
        calc ((⌈x / (L : ℝ)⌉₊ - 1 : ℕ) : ℝ) * L < (x / L) * L := by
              apply mul_lt_mul_of_pos_right hlt hLR
          _ = x := by field_simp
      · have hle : x / (L : ℝ) ≤ (⌈x / (L : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
        have h2 : x ≤ (⌈x / (L : ℝ)⌉₊ : ℝ) * L := by
          rw [← div_le_iff₀ hLR]
          exact hle
        calc x ≤ (⌈x / (L : ℝ)⌉₊ : ℝ) * L := h2
          _ = ((⌈x / (L : ℝ)⌉₊ - 1 : ℕ) : ℝ) * L + L := by
              rw [Nat.cast_sub hceil]
              push_cast
              ring
  have hdisj : Pairwise (Function.onFun Disjoint
      (fun n : ℕ => Set.Ioc ((n : ℝ) * L) ((n : ℝ) * L + L))) := by
    intro m n hmn
    have hkey : ∀ a b : ℕ, a < b → Disjoint (Set.Ioc ((a : ℝ) * L) ((a : ℝ) * L + L))
        (Set.Ioc ((b : ℝ) * L) ((b : ℝ) * L + L)) := by
      intro a b hab
      apply Set.disjoint_left.mpr
      intro x hxa hxb
      have h1 : x ≤ (a : ℝ) * L + L := hxa.2
      have h2 : (b : ℝ) * L < x := hxb.1
      have h3 : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hab
      nlinarith
    rcases lt_or_gt_of_ne hmn with hlt | hlt
    · exact hkey m n hlt
    · exact (hkey n m hlt).symm
  have hint : IntegrableOn g (⋃ n : ℕ, Set.Ioc ((n : ℝ) * L) ((n : ℝ) * L + L)) := by
    rw [hunion]
    exact integrableOn_fract_two_div_sq h k hh hk
  have hiUnion := MeasureTheory.integral_iUnion (fun n => measurableSet_Ioc) hdisj hint
  calc (∑' n : ℕ, ∫ s in Set.Ioc (0 : ℝ) (L : ℝ),
        Int.fract (s / (h : ℝ)) * Int.fract (s / (k : ℝ)) / ((n : ℝ) * L + s) ^ 2)
      = ∑' n : ℕ, ∫ s in Set.Ioc ((n : ℝ) * L) ((n : ℝ) * L + L), g s := by
        exact tsum_congr hslice
    _ = ∫ s in (⋃ n : ℕ, Set.Ioc ((n : ℝ) * L) ((n : ℝ) * L + L)), g s := hiUnion.symm
    _ = ∫ s in Set.Ioi (0 : ℝ), g s := by rw [hunion]

/-- **The Vasyunin period reduction**: the shifted-integral tsum equals the Vasyunin
explicit-formula entry, for all positive `h, k` (`h = k` included). -/
theorem bbls_tsum_eq_vasyuninBEntry (h k : ℕ) (hh : 0 < h) (hk : 0 < k) :
    (∑' n : ℕ, ∫ s in Set.Ioc (0 : ℝ) (Nat.lcm h k : ℝ),
        Int.fract (s / (h : ℝ)) * Int.fract (s / (k : ℝ)) /
          ((n : ℝ) * (Nat.lcm h k : ℝ) + s) ^ 2)
      = vasyuninBEntry h k := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  rw [bbls_period_unfolding h k hh hk]
  -- substitution s = t·h reduces to the autocorrelation integral at h/k
  have hcomp := MeasureTheory.integral_comp_mul_right_Ioi
    (fun s : ℝ => Int.fract (s / (h : ℝ)) * Int.fract (s / (k : ℝ)) / s ^ 2) 0 hhR
  simp only [zero_mul, smul_eq_mul] at hcomp
  have hpoint : ∀ t : ℝ, 0 < t →
      Int.fract ((t * h) / (h : ℝ)) * Int.fract ((t * h) / (k : ℝ)) / (t * h) ^ 2
        = (1 / (h : ℝ) ^ 2) * (Int.fract t * Int.fract (((h : ℝ) / (k : ℝ)) * t) / t ^ 2) := by
    intro t ht
    have h1 : (t * h) / (h : ℝ) = t := by field_simp
    have h2 : (t * h) / (k : ℝ) = ((h : ℝ) / k) * t := by field_simp
    rw [h1, h2]
    field_simp
  have hcongr : (∫ t in Set.Ioi (0 : ℝ),
      Int.fract ((t * h) / (h : ℝ)) * Int.fract ((t * h) / (k : ℝ)) / (t * h) ^ 2)
      = ∫ t in Set.Ioi (0 : ℝ),
          (1 / (h : ℝ) ^ 2) * (Int.fract t * Int.fract (((h : ℝ) / (k : ℝ)) * t) / t ^ 2) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact hpoint t ht
  have hsub : (∫ s in Set.Ioi (0 : ℝ),
      Int.fract (s / (h : ℝ)) * Int.fract (s / (k : ℝ)) / s ^ 2)
      = (1 / (h : ℝ)) * ∫ t in Set.Ioi (0 : ℝ),
          Int.fract t * Int.fract (((h : ℝ) / (k : ℝ)) * t) / t ^ 2 := by
    have hg : (∫ s in Set.Ioi (0 : ℝ),
        Int.fract (s / (h : ℝ)) * Int.fract (s / (k : ℝ)) / s ^ 2)
        = (h : ℝ) * ∫ t in Set.Ioi (0 : ℝ),
            Int.fract ((t * h) / (h : ℝ)) * Int.fract ((t * h) / (k : ℝ)) / (t * h) ^ 2 := by
      rw [hcomp]
      have hhne : (h : ℝ) ≠ 0 := hhR.ne'
      field_simp
    rw [hg, hcongr, MeasureTheory.integral_const_mul]
    have hhne : (h : ℝ) ≠ 0 := hhR.ne'
    field_simp
  rw [hsub, bbls_A_rat k h hk hh]
  unfold vasyuninBEntry vasyuninBEntryFormula
  have hhne : (h : ℝ) ≠ 0 := hhR.ne'
  have hkne : (k : ℝ) ≠ 0 := hkR.ne'
  field_simp
  ring

/-- The period-reduction statement in its original recorded form (with the unused
`h ≠ k` hypothesis), replacing the former `sorry` in
`VasyuninCotangentRecognition.lean`. -/
theorem shiftedIntegralTsum_period_reduction (h k : ℕ) (_hne : h ≠ k) (hh : 0 < h)
    (hk : 0 < k) :
    (∑' n : ℕ, ∫ s in Set.Ioc (0 : ℝ) (Nat.lcm h k : ℝ),
        Int.fract (s / (h : ℝ)) * Int.fract (s / (k : ℝ)) /
          ((n : ℝ) * (Nat.lcm h k : ℝ) + s) ^ 2)
      = vasyuninBEntry h k :=
  bbls_tsum_eq_vasyuninBEntry h k hh hk


end RH.Criteria.NymanBeurling.VasyuninGram
