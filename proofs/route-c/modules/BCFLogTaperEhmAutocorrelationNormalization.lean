import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmAutocorrelationFourier
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperCotangentReduction
import RiemannHypothesis.Criteria.NymanBeurling.G11Formula

/-!
# Rational normalization of Ehm's autocorrelation series

This module discharges the self-dual value `r = 1` in Ehm's
autocorrelation--`R₁` identity and reduces every positive rational value to
one explicit finite harmonic-progression limit.

The reduction is the rational form actually needed by H15.  It avoids the
stronger all-real weighted-tail statement and makes clear that Fourier
coefficient convergence alone does not evaluate the independent Gram
autocorrelation.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmAutocorrelationNormalization

open Filter
open scoped Topology
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmKernel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmSeriesBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmSeriesValue
open RH.Criteria.NymanBeurling.BCFLogTaperEhmR1Decay
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmIntegralSeriesAssembly
open RH.Criteria.NymanBeurling.BCFLogTaperCotangentReduction
open RH.Criteria.NymanBeurling.VasyuninGram

/-- At the self-dual scale, the independently defined Gram autocorrelation
has exactly Ehm's normalization constant. -/
theorem ehmS1Autocorrelation_one_value :
    ehmS1Autocorrelation 1 =
      (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant - 1) / 2 := by
  have hgram := baezDuarteGramEntry_eq_inv_mul_ehmAutocorrelation
    1 1 Nat.one_pos Nat.one_pos
  have hG := G11_formula_theorem
  have hA : ehmAutocorrelation 1 =
      Real.log (2 * Real.pi) - Real.eulerMascheroniConstant := by
    calc
      ehmAutocorrelation 1 = baezDuarteGramEntry 1 1 := by
        simpa using hgram.symm
      _ = Real.log (2 * Real.pi) - Real.eulerMascheroniConstant := hG
  unfold ehmS1Autocorrelation ehmK
  rw [hA]
  norm_num
  ring

/-- The normalization-point `R₁` series has the independently defined Gram
autocorrelation as its sum. -/
theorem hasSum_ehmR1_nat_to_autocorrelation :
    HasSum (fun q : ℕ => ehmR1 ((q + 1 : ℕ) : ℝ))
      (ehmS1Autocorrelation 1) := by
  rw [ehmS1Autocorrelation_one_value]
  exact hasSum_ehmR1_nat

/-- Exact value identity at `r = 1`. -/
theorem ehmS1Autocorrelation_one_eq_tsum :
    ehmS1Autocorrelation 1 =
      ∑' q : ℕ, ehmR1 ((q + 1 : ℕ) : ℝ) :=
  hasSum_ehmR1_nat_to_autocorrelation.tsum_eq.symm

/-- Ehm's concrete finite weighted tails converge to the Gram
autocorrelation at the normalization point. -/
theorem ehmPhi1Integral_tendsto_autocorrelation_one :
    Tendsto (fun K : ℕ =>
      -(∫ x in Set.Ioi (1 : ℝ), ehmPhi1Partial K x / x ^ 2))
      atTop (𝓝 (ehmS1Autocorrelation 1)) := by
  rw [ehmS1Autocorrelation_one_eq_tsum]
  simpa using integral_ehmPhi1Partial_tendsto_tsum 1 zero_lt_one

/-- At a positive rational scale, the finite coupled floor/sawtooth limit
has the Vasyunin value exactly when the Gram autocorrelation equals the
convergent `R₁` series. -/
theorem ehmR1RationalClosedForm_tendsto_vasyunin_iff_seriesValue
    (d m : ℕ) (hd : 0 < d) (hm : 0 < m) :
    Tendsto (fun N : ℕ => ehmR1RationalPartialClosedForm d m N) atTop
        (𝓝 (vasyuninS1RationalKernel m d)) ↔
      ehmS1Autocorrelation ((d : ℝ) / (m : ℝ)) =
        ∑' q : ℕ,
          ehmR1 (((q + 1 : ℕ) : ℝ) * ((d : ℝ) / (m : ℝ))) := by
  rw [← ehmS1Autocorrelation_eq_vasyuninS1RationalKernel_proved
    m d hm hd]
  exact ehmR1RationalClosedForm_limit_iff_autocorrelation_eq_tsum
    d m hd hm

/-- Multiplying both entries of a positive rational scale by the same
positive natural does not change the exact finite progression expression. -/
theorem ehmR1RationalPartialClosedForm_mul_left
    (c d m N : ℕ) (hc : 0 < c) (hd : 0 < d) (hm : 0 < m) :
    ehmR1RationalPartialClosedForm (c * d) (c * m) N =
      ehmR1RationalPartialClosedForm d m N := by
  rw [← ehmR1PartialSeries_ratio_eq_closedForm
      (c * d) (c * m) N (Nat.mul_pos hc hd) (Nat.mul_pos hc hm),
    ← ehmR1PartialSeries_ratio_eq_closedForm d m N hd hm]
  have hratio : (((c * d : ℕ) : ℝ) / ((c * m : ℕ) : ℝ)) =
      (d : ℝ) / (m : ℝ) := by
    push_cast
    field_simp [show (c : ℝ) ≠ 0 by positivity,
      show (m : ℝ) ≠ 0 by positivity]
  rw [hratio]

/-- The Vasyunin target has the same common-factor invariance.  This proof
uses its already-proved identification with the Gram autocorrelation rather
than expanding non-coprime cotangent sums. -/
theorem vasyuninS1RationalKernel_mul_left
    (c d m : ℕ) (hc : 0 < c) (hd : 0 < d) (hm : 0 < m) :
    vasyuninS1RationalKernel (c * m) (c * d) =
      vasyuninS1RationalKernel m d := by
  rw [← ehmS1Autocorrelation_eq_vasyuninS1RationalKernel_proved
      (c * m) (c * d) (Nat.mul_pos hc hm) (Nat.mul_pos hc hd),
    ← ehmS1Autocorrelation_eq_vasyuninS1RationalKernel_proved m d hm hd]
  congr 1
  push_cast
  field_simp [show (c : ℝ) ≠ 0 by positivity,
    show (m : ℝ) ≠ 0 by positivity]

/-- The finite harmonic-progression asymptotic which remains after the
self-dual normalization and the BBLS/Vasyunin autocorrelation evaluation. -/
structure EhmRationalProgressionAsymptotics where
  tendsto_value : ∀ d m : ℕ, 0 < d → 0 < m →
    Tendsto (fun N : ℕ => ehmR1RationalPartialClosedForm d m N) atTop
      (𝓝 (vasyuninS1RationalKernel m d))

/-- It is enough to prove the progression asymptotic for coprime positive
pairs.  The exact finite expression and its Vasyunin target both descend
through the common gcd. -/
structure EhmCoprimeRationalProgressionAsymptotics where
  tendsto_value : ∀ d m : ℕ, 0 < d → 0 < m → Nat.Coprime d m →
    Tendsto (fun N : ℕ => ehmR1RationalPartialClosedForm d m N) atTop
      (𝓝 (vasyuninS1RationalKernel m d))

/-- Remove the common gcd and lift a coprime progression theorem to every
positive rational representation. -/
noncomputable def EhmCoprimeRationalProgressionAsymptotics.toRational
    (H : EhmCoprimeRationalProgressionAsymptotics) :
    EhmRationalProgressionAsymptotics where
  tendsto_value d m hd hm := by
    let g : ℕ := Nat.gcd d m
    let d' : ℕ := d / g
    let m' : ℕ := m / g
    have hg : 0 < g := Nat.gcd_pos_of_pos_left m hd
    have hd' : 0 < d' :=
      Nat.div_pos (Nat.le_of_dvd hd (Nat.gcd_dvd_left d m)) hg
    have hm' : 0 < m' :=
      Nat.div_pos (Nat.le_of_dvd hm (Nat.gcd_dvd_right d m)) hg
    have hcop : Nat.Coprime d' m' := by
      exact Nat.coprime_div_gcd_div_gcd hg
    have hd_factor : g * d' = d := by
      exact Nat.mul_div_cancel' (Nat.gcd_dvd_left d m)
    have hm_factor : g * m' = m := by
      exact Nat.mul_div_cancel' (Nat.gcd_dvd_right d m)
    have hfinite : ∀ N : ℕ,
        ehmR1RationalPartialClosedForm d m N =
          ehmR1RationalPartialClosedForm d' m' N := by
      intro N
      rw [← hd_factor, ← hm_factor]
      exact ehmR1RationalPartialClosedForm_mul_left
        g d' m' N hg hd' hm'
    have htarget : vasyuninS1RationalKernel m d =
        vasyuninS1RationalKernel m' d' := by
      rw [← hd_factor, ← hm_factor]
      exact vasyuninS1RationalKernel_mul_left g d' m' hg hd' hm'
    rw [htarget]
    exact (H.tendsto_value d' m' hd' hm' hcop).congr'
      (Eventually.of_forall fun N => (hfinite N).symm)

/-- The rational progression asymptotic supplies precisely the rational
autocorrelation--`R₁` bridge required downstream by H15. -/
noncomputable def ehmAutocorrelationR1RationalSeriesBridge_of_progressions
    (H : EhmRationalProgressionAsymptotics) :
    EhmAutocorrelationR1RationalSeriesBridge :=
  EhmR1RationalSeriesBridge.of_decay_and_value
    ehmConcreteR1QuadraticDecay
    { value := fun d m hd hm =>
        (ehmR1RationalClosedForm_tendsto_vasyunin_iff_seriesValue
          d m hd hm).mp (H.tendsto_value d m hd hm) }

end RH.Criteria.NymanBeurling.BCFLogTaperEhmAutocorrelationNormalization
