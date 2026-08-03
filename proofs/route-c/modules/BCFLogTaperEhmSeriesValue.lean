import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmR1Decay
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
import RiemannHypothesis.Criteria.NymanBeurling.G11IntegralEvaluation

/-!
# Finite identities toward Ehm's autocorrelation--`R₁` series value

The remaining value identity

`ehmS1Autocorrelation x = ∑' q, ehmR1 ((q + 1) * x)`

is Ehm's Theorem 2.1 / Proposition 5.1.  This file records genuine finite
identities at every positive rational scale, proves absolute convergence from
the concrete quadratic decay theorem, and evaluates the normalization-point
series.  The identification of the rational series value with the concrete
autocorrelation remains explicit.  No `sorry` or external axiom is introduced.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmSeriesValue

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmKernel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmSeriesBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmR1Decay
open RH.Criteria.NymanBeurling.VasyuninGram

/-- The exact factorial--harmonic expression for the integer-scale partial
sum of Ehm's `R₁` series. -/
noncomputable def ehmR1IntegerPartialClosedForm (N : ℕ) : ℝ :=
  Real.log ((Nat.factorial N : ℕ) : ℝ) +
    (N : ℝ) * (Real.eulerMascheroniConstant + 1) -
    ((N : ℝ) + 1 / 2) * ehmHarmonic N

/-- At a natural argument, Ehm's finite-floor harmonic sum is the project
harmonic sum used in the proved `G₁₁` evaluation. -/
theorem ehmHarmonic_nat_eq_HarmonicReal (N : ℕ) :
    ehmHarmonic N = HarmonicReal N := by
  unfold ehmHarmonic HarmonicReal
  rw [Nat.floor_natCast]

/-- Ehm's elementary remainder at a positive integer. -/
theorem ehmR1_nat_formula (n : ℕ) (hn : 0 < n) :
    ehmR1 n = Real.log n + Real.eulerMascheroniConstant -
      ehmHarmonic n + 1 / (2 * (n : ℝ)) := by
  unfold ehmR1
  rw [Int.fract_natCast]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hnR]
  ring

/-- Reversing the finite harmonic double sum gives
`∑_{n≤N} H(n) = (N+1)H(N)-N`. -/
theorem sum_ehmHarmonic_Icc (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ehmHarmonic n) =
      ((N : ℝ) + 1) * ehmHarmonic N - N := by
  induction N with
  | zero => simp [ehmHarmonic]
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      have hsucc : ehmHarmonic ((N + 1 : ℕ) : ℝ) =
          ehmHarmonic (N : ℝ) + 1 / ((N : ℝ) + 1) := by
        unfold ehmHarmonic
        rw [Nat.floor_natCast, Nat.floor_natCast]
        rw [Finset.sum_Icc_succ_top (by omega)]
        push_cast
        rfl
      rw [hsucc]
      have hne : (N : ℝ) + 1 ≠ 0 := by positivity
      push_cast
      field_simp [hne]
      ring

/-- The logarithms over `1,…,N` combine to `log (N!)`. -/
theorem sum_log_nat_Icc (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ)) =
      Real.log ((Nat.factorial N : ℕ) : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.factorial_succ]
      push_cast
      rw [Real.log_mul (by positivity) (by positivity)]
      ring

/-- The reciprocal sum over `1,…,N` is Ehm's harmonic sum. -/
theorem sum_one_div_nat_Icc (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ)) = ehmHarmonic N := by
  unfold ehmHarmonic
  rw [Nat.floor_natCast]

/-- Exact finite form of Proposition 6.1 in Ehm (2024), before taking the
limit.  This is the finite algebra on which the analytic value at `x = 1`
rests. -/
theorem ehmR1PartialSeries_one_eq_closedForm (N : ℕ) :
    ehmR1PartialSeries ehmR1 N 1 = ehmR1IntegerPartialClosedForm N := by
  classical
  unfold ehmR1PartialSeries ehmR1IntegerPartialClosedForm
  simp only [mul_one]
  calc
    (∑ n ∈ Finset.Icc 1 N, ehmR1 (n : ℝ)) =
        ∑ n ∈ Finset.Icc 1 N,
          (Real.log (n : ℝ) + Real.eulerMascheroniConstant -
            ehmHarmonic n + 1 / (2 * (n : ℝ))) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [ehmR1_nat_formula n (lt_of_lt_of_le Nat.zero_lt_one
        (Finset.mem_Icc.mp hn).1)]
    _ = (∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ)) +
          (N : ℝ) * Real.eulerMascheroniConstant -
          (∑ n ∈ Finset.Icc 1 N, ehmHarmonic n) +
          (1 / 2) * (∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ)) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_add_distrib]
      have hcard : (Finset.Icc 1 N).card = N := by simp
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
      rw [Finset.mul_sum]
      apply congrArg
      apply Finset.sum_congr rfl
      intro n hn
      have hn0 : (n : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one
          (Finset.mem_Icc.mp hn).1))
      field_simp [hn0]
    _ = _ := by
      rw [sum_log_nat_Icc, sum_ehmHarmonic_Icc, sum_one_div_nat_Icc]
      ring

/-- Exact finite expression at the positive rational scale `d/m`.  Keeping
the floor-harmonic and centered-fractional sums coupled is important: their
large pieces cancel, while estimating either one separately loses the value
identity. -/
noncomputable def ehmR1RationalPartialClosedForm
    (d m N : ℕ) : ℝ :=
  (N : ℝ) *
      (Real.log ((d : ℝ) / (m : ℝ)) +
        Real.eulerMascheroniConstant) +
    Real.log ((Nat.factorial N : ℕ) : ℝ) -
    (∑ k ∈ Finset.Icc 1 N,
      ehmHarmonic ((k : ℝ) * ((d : ℝ) / (m : ℝ)))) -
    ((m : ℝ) / (d : ℝ)) *
      ∑ k ∈ Finset.Icc 1 N,
        (Int.fract ((k : ℝ) * ((d : ℝ) / (m : ℝ))) - 1 / 2) / (k : ℝ)

/-- Finite rational-scale form of Ehm's series.  This is the strongest purely
finite reduction: the remaining passage to the autocorrelation is exactly a
limit theorem for the displayed *coupled* floor/sawtooth expression. -/
theorem ehmR1PartialSeries_ratio_eq_closedForm
    (d m N : ℕ) (hd : 0 < d) (hm : 0 < m) :
    ehmR1PartialSeries ehmR1 N ((d : ℝ) / (m : ℝ)) =
      ehmR1RationalPartialClosedForm d m N := by
  classical
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hrR : (d : ℝ) / (m : ℝ) ≠ 0 := div_ne_zero hdR hmR
  unfold ehmR1PartialSeries ehmR1RationalPartialClosedForm
  calc
    (∑ k ∈ Finset.Icc 1 N,
        ehmR1 ((k : ℝ) * ((d : ℝ) / (m : ℝ)))) =
      ∑ k ∈ Finset.Icc 1 N,
        (Real.log (k : ℝ) + Real.log ((d : ℝ) / (m : ℝ)) +
          Real.eulerMascheroniConstant -
          ehmHarmonic ((k : ℝ) * ((d : ℝ) / (m : ℝ))) -
          ((m : ℝ) / (d : ℝ)) *
            ((Int.fract ((k : ℝ) * ((d : ℝ) / (m : ℝ))) - 1 / 2) /
              (k : ℝ))) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one
        (Finset.mem_Icc.mp hk).1
      have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hkpos.ne'
      unfold ehmR1
      rw [Real.log_mul hkR hrR]
      have hscale :
          (Int.fract ((k : ℝ) * ((d : ℝ) / (m : ℝ))) - 1 / 2) /
              ((k : ℝ) * ((d : ℝ) / (m : ℝ))) =
            ((m : ℝ) / (d : ℝ)) *
              ((Int.fract ((k : ℝ) * ((d : ℝ) / (m : ℝ))) - 1 / 2) /
                (k : ℝ)) := by
        field_simp [hkR, hdR, hmR]
      rw [hscale]
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, Finset.sum_add_distrib]
      rw [sum_log_nat_Icc]
      have hcard : (Finset.Icc 1 N).card = N := by simp
      rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul,
        nsmul_eq_mul, hcard, Finset.mul_sum]
      ring

private theorem sum_range_shift_ehmR1_at_scale (N : ℕ) (x : ℝ) :
    (∑ q ∈ Finset.range N, ehmR1 (((q + 1 : ℕ) : ℝ) * x)) =
      ehmR1PartialSeries ehmR1 N x := by
  induction N with
  | zero => simp [ehmR1PartialSeries]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      unfold ehmR1PartialSeries
      rw [Finset.sum_Icc_succ_top (by omega)]

/-- For every positive rational scale, the explicit coupled closed form has
an unconditional limit: the absolutely convergent `R₁` series.  Thus neither
convergence nor tail control remains in the value problem; the only missing
assertion is identification of this limit with the autocorrelation. -/
theorem ehmR1RationalPartialClosedForm_tendsto_tsum
    (d m : ℕ) (hd : 0 < d) (hm : 0 < m) :
    Tendsto (fun N : ℕ => ehmR1RationalPartialClosedForm d m N) atTop
      (𝓝 (∑' q : ℕ,
        ehmR1 (((q + 1 : ℕ) : ℝ) * ((d : ℝ) / (m : ℝ))))) := by
  have hx : 0 < (d : ℝ) / (m : ℝ) := by positivity
  have HS := ehmConcreteR1QuadraticDecay.summable_series
    ((d : ℝ) / (m : ℝ)) hx
  apply HS.hasSum.tendsto_sum_nat.congr'
  filter_upwards with N
  rw [sum_range_shift_ehmR1_at_scale,
    ehmR1PartialSeries_ratio_eq_closedForm d m N hd hm]

/-- Exact pointwise description of what remains from Ehm's value theorem at
a positive rational scale.  The coupled closed-form limit is the
autocorrelation iff the already convergent `R₁` series has that value. -/
theorem ehmR1RationalClosedForm_limit_iff_autocorrelation_eq_tsum
    (d m : ℕ) (hd : 0 < d) (hm : 0 < m) :
    Tendsto (fun N : ℕ => ehmR1RationalPartialClosedForm d m N) atTop
        (𝓝 (ehmS1Autocorrelation ((d : ℝ) / (m : ℝ)))) ↔
      ehmS1Autocorrelation ((d : ℝ) / (m : ℝ)) =
        ∑' q : ℕ,
          ehmR1 (((q + 1 : ℕ) : ℝ) * ((d : ℝ) / (m : ℝ))) := by
  constructor
  · intro hlimit
    exact tendsto_nhds_unique hlimit
      (ehmR1RationalPartialClosedForm_tendsto_tsum d m hd hm)
  · intro hvalue
    rw [hvalue]
    exact ehmR1RationalPartialClosedForm_tendsto_tsum d m hd hm

/-- Reciprocal-square decay and convergence of the explicit *finite coupled
expression* construct precisely the rational series bridge used by H15.
Thus the value problem is reduced to the displayed floor/sawtooth limit,
without requiring an identity at irrational scales. -/
noncomputable def ehmAutocorrelationRationalSeriesBridge_of_closedForm_limit
    (HL : ∀ d m : ℕ, 0 < d → 0 < m →
      Tendsto (fun N : ℕ => ehmR1RationalPartialClosedForm d m N) atTop
        (𝓝 (ehmS1Autocorrelation ((d : ℝ) / (m : ℝ))))) :
    EhmAutocorrelationR1RationalSeriesBridge where
  hasSum_ratio d m hd hm := by
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hx : 0 < (d : ℝ) / (m : ℝ) :=
      div_pos (by exact_mod_cast hd) hmR
    have hsummable :=
      ehmConcreteR1QuadraticDecay.summable_series ((d : ℝ) / (m : ℝ)) hx
    apply (hsummable.hasSum_iff_tendsto_nat).mpr
    apply (HL d m hd hm).congr'
    filter_upwards with N
    rw [sum_range_shift_ehmR1_at_scale,
      ehmR1PartialSeries_ratio_eq_closedForm d m N hd hm]

/-- The single sharp harmonic remainder needed to pass the exact finite
identity at `x = 1` to its limit.  This is strictly smaller than the global
autocorrelation--series value theorem. -/
noncomputable def ehmHarmonicSecondOrderRemainder (N : ℕ) : ℝ :=
  ((N : ℝ) + 1 / 2) *
    (ehmHarmonic N - Real.log N - Real.eulerMascheroniConstant)

/-- The sharp second-order harmonic asymptotic needed at the normalization
point is already a consequence of the explicit Euler--Mascheroni remainder
bounds used to prove quadratic decay of `ehmR1`. -/
theorem ehmHarmonicSecondOrderRemainder_tendsto :
    Tendsto ehmHarmonicSecondOrderRemainder atTop (𝓝 (1 / 2 : ℝ)) := by
  let lower : ℕ → ℝ := fun n => (2 * (n : ℝ) + 1) / (4 * (n : ℝ) + 1)
  let upper : ℕ → ℝ := fun n => (2 * (n : ℝ) + 1) / (4 * (n : ℝ))
  have hone : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hlower' : Tendsto
      (fun n : ℕ => (2 + 1 / (n : ℝ)) / (4 + 1 / (n : ℝ)))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    have hnum : Tendsto (fun n : ℕ => (2 : ℝ) + 1 / (n : ℝ))
        atTop (𝓝 2) := by simpa using tendsto_const_nhds.add hone
    have hden : Tendsto (fun n : ℕ => (4 : ℝ) + 1 / (n : ℝ))
        atTop (𝓝 4) := by simpa using tendsto_const_nhds.add hone
    have hdiv := hnum.div hden (by norm_num : (4 : ℝ) ≠ 0)
    change Tendsto
      (fun n : ℕ => (2 + 1 / (n : ℝ)) / (4 + 1 / (n : ℝ)))
      atTop (𝓝 ((2 : ℝ) / 4)) at hdiv
    norm_num at hdiv
    simpa only [one_div] using hdiv
  have hlower : Tendsto lower atTop (𝓝 (1 / 2 : ℝ)) := by
    apply hlower'.congr'
    filter_upwards [eventually_atTop.2 ⟨1, fun _ h => h⟩] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    dsimp [lower]
    field_simp [hn0]
  have hupper' : Tendsto
      (fun n : ℕ => (1 / 2 : ℝ) + (1 / 4) * (1 / (n : ℝ)))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    have hquarter : Tendsto (fun _ : ℕ => (1 / 4 : ℝ)) atTop (𝓝 (1 / 4)) :=
      tendsto_const_nhds
    have hprod : Tendsto (fun n : ℕ => (1 / 4 : ℝ) * (1 / (n : ℝ)))
        atTop (𝓝 0) := by simpa using hquarter.mul hone
    simpa using (tendsto_const_nhds.add hprod :
      Tendsto (fun n : ℕ => (1 / 2 : ℝ) + (1 / 4) * (1 / (n : ℝ)))
        atTop (𝓝 ((1 / 2 : ℝ) + 0)))
  have hupper : Tendsto upper atTop (𝓝 (1 / 2 : ℝ)) := by
    apply hupper'.congr'
    filter_upwards [eventually_atTop.2 ⟨1, fun _ h => h⟩] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    dsimp [upper]
    field_simp [hn0]
    ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [eventually_atTop.2 ⟨1, fun _ h => h⟩] with n hn
    have hnpos : 0 < n := hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hb := harmonic_log_remainder_bounds n hnpos
    have hb' :
        Real.log (1 + 1 / (2 * (n : ℝ))) ≤
          ehmHarmonic n - Real.log (n : ℝ) -
            Real.eulerMascheroniConstant := by
      rw [ehmHarmonic_eq_harmonic_floor, Nat.floor_natCast]
      exact hb.1
    have hlog := Real.le_log_one_add_of_nonneg
      (show 0 ≤ 1 / (2 * (n : ℝ)) by positivity)
    dsimp [lower, ehmHarmonicSecondOrderRemainder]
    calc
      (2 * (n : ℝ) + 1) / (4 * (n : ℝ) + 1) =
          ((n : ℝ) + 1 / 2) *
            (2 * (1 / (2 * (n : ℝ))) /
              (1 / (2 * (n : ℝ)) + 2)) := by
                field_simp [ne_of_gt hnR]
                ring
      _ ≤ ((n : ℝ) + 1 / 2) *
          Real.log (1 + 1 / (2 * (n : ℝ))) := by
            gcongr
      _ ≤ ((n : ℝ) + 1 / 2) *
          (ehmHarmonic n - Real.log (n : ℝ) -
            Real.eulerMascheroniConstant) := by gcongr
  · filter_upwards [eventually_atTop.2 ⟨1, fun _ h => h⟩] with n hn
    have hnpos : 0 < n := hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hb := harmonic_log_remainder_bounds n hnpos
    have hb' :
        ehmHarmonic n - Real.log (n : ℝ) -
            Real.eulerMascheroniConstant ≤ 1 / (2 * (n : ℝ)) := by
      rw [ehmHarmonic_eq_harmonic_floor, Nat.floor_natCast]
      exact hb.2
    dsimp [upper, ehmHarmonicSecondOrderRemainder]
    calc
      ((n : ℝ) + 1 / 2) *
          (ehmHarmonic n - Real.log (n : ℝ) -
            Real.eulerMascheroniConstant) ≤
          ((n : ℝ) + 1 / 2) * (1 / (2 * (n : ℝ))) := by gcongr
      _ = (2 * (n : ℝ) + 1) / (4 * (n : ℝ)) := by
        field_simp [ne_of_gt hnR]
        ring

/-- Exact decomposition of the integer partial sum into the Stirling
remainder and the second-order harmonic remainder. -/
theorem ehmR1IntegerPartialClosedForm_eq_remainders (N : ℕ) :
    ehmR1IntegerPartialClosedForm N =
      (1 / 2) * Real.log (2 * Real.pi) -
        Real.eulerMascheroniConstant / 2 +
        LogStirlingRemainder N - ehmHarmonicSecondOrderRemainder N := by
  unfold ehmR1IntegerPartialClosedForm LogStirlingRemainder
    ehmHarmonicSecondOrderRemainder
  ring

/-- The standard second-order harmonic asymptotic is sufficient to evaluate
Ehm's integer-scale partial sums.  The hypothesis is precisely
`(N + 1/2) (H_N - log N - γ) → 1/2`. -/
theorem ehmR1PartialSeries_one_tendsto_of_harmonic_second_order
    (HH : Tendsto ehmHarmonicSecondOrderRemainder atTop (𝓝 (1 / 2 : ℝ))) :
    Tendsto (fun N : ℕ => ehmR1PartialSeries ehmR1 N 1) atTop
      (𝓝 ((Real.log (2 * Real.pi) - Real.eulerMascheroniConstant - 1) / 2)) := by
  have hconst : Tendsto (fun _ : ℕ =>
      (1 / 2) * Real.log (2 * Real.pi) -
        Real.eulerMascheroniConstant / 2) atTop
      (𝓝 ((1 / 2) * Real.log (2 * Real.pi) -
        Real.eulerMascheroniConstant / 2)) := tendsto_const_nhds
  have hrem := log_stirling_remainder_tendsto_zero
  have hlim := (hconst.add hrem).sub HH
  have hlim' : Tendsto (fun N : ℕ =>
      (1 / 2) * Real.log (2 * Real.pi) -
        Real.eulerMascheroniConstant / 2 + LogStirlingRemainder N -
        ehmHarmonicSecondOrderRemainder N) atTop
      (𝓝 ((Real.log (2 * Real.pi) - Real.eulerMascheroniConstant - 1) / 2)) := by
    convert hlim using 1
    ring_nf
  apply Tendsto.congr' _ hlim'
  filter_upwards with N
  rw [ehmR1PartialSeries_one_eq_closedForm,
    ehmR1IntegerPartialClosedForm_eq_remainders]

/-- Unconditional evaluation of the integer-scale partial sums. -/
theorem ehmR1PartialSeries_one_tendsto :
    Tendsto (fun N : ℕ => ehmR1PartialSeries ehmR1 N 1) atTop
      (𝓝 ((Real.log (2 * Real.pi) - Real.eulerMascheroniConstant - 1) / 2)) :=
  ehmR1PartialSeries_one_tendsto_of_harmonic_second_order
    ehmHarmonicSecondOrderRemainder_tendsto

private theorem sum_range_shift_ehmR1 (N : ℕ) :
    (∑ q ∈ Finset.range N, ehmR1 ((q + 1 : ℕ) : ℝ)) =
      ehmR1PartialSeries ehmR1 N 1 := by
  induction N with
  | zero => simp [ehmR1PartialSeries]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      unfold ehmR1PartialSeries
      rw [Finset.sum_Icc_succ_top (by omega)]
      simp

/-- At `x = 1`, the second-order harmonic asymptotic already constructs the
actual `HasSum` required by the series bridge. -/
theorem hasSum_ehmR1_nat_of_harmonic_second_order
    (HH : Tendsto ehmHarmonicSecondOrderRemainder atTop (𝓝 (1 / 2 : ℝ))) :
    HasSum (fun q : ℕ => ehmR1 ((q + 1 : ℕ) : ℝ))
      ((Real.log (2 * Real.pi) - Real.eulerMascheroniConstant - 1) / 2) := by
  have HS : Summable (fun q : ℕ => ehmR1 ((q + 1 : ℕ) : ℝ)) := by
    simpa using
      (ehmConcreteR1QuadraticDecay.summable_series (1 : ℝ) zero_lt_one)
  apply (HS.hasSum_iff_tendsto_nat).mpr
  exact (ehmR1PartialSeries_one_tendsto_of_harmonic_second_order HH).congr'
    (Filter.Eventually.of_forall fun N => (sum_range_shift_ehmR1 N).symm)

/-- The normalization-point `R₁` series is evaluated without any analytic
hypothesis. -/
theorem hasSum_ehmR1_nat :
    HasSum (fun q : ℕ => ehmR1 ((q + 1 : ℕ) : ℝ))
      ((Real.log (2 * Real.pi) - Real.eulerMascheroniConstant - 1) / 2) :=
  hasSum_ehmR1_nat_of_harmonic_second_order
    ehmHarmonicSecondOrderRemainder_tendsto

end RH.Criteria.NymanBeurling.BCFLogTaperEhmSeriesValue
