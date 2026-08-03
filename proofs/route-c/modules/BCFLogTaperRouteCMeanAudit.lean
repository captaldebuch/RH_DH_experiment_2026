import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperCotangentReduction
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEnergyMeanContourExtraction

/-!
# Route C mean-value audit

Bettin--Conrey's divisor transformation and cotangent reciprocity provide the
correct local analytic language for H15, but their divisor-series constant
and rapidly convergent Taylor tail cannot be identified directly with the
BCF diagonal and signed dispersion.

This module records the exact compatible target.  The dyadic mean of the
*complete* Vasyunin expression--including constant, logarithmic-ratio,
cotangent, linear, and endpoint terms--is exactly the normalized BCF energy
mean.  It also gives a formal normalization stop test: the universal `1/4`
in Bettin--Conrey's divisor transformation cannot equal the H15 diagonal
mean, which is strictly larger than one.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCMeanAudit

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperBettinConreyAggregate
open RH.Criteria.NymanBeurling.BCFLogTaperCotangentReduction
open RH.Criteria.NymanBeurling.BCFLogTaperEnergyMeanAnatomy
open RH.Criteria.NymanBeurling.BCFLogTaperGcd
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCompleteRowAbelDecay
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeTruncatedFormula
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.BCFLogTaperSpectral
open RH.Criteria.NymanBeurling.QuadraticInteraction

/-- The only Route-C mean which preserves every term of the proved finite
Vasyunin reduction. -/
noncomputable def ehmDyadicVasyuninCoupledMean (X : ℕ) : ℝ :=
  (∑ N ∈ ehmDyadicNBlock X, vasyuninCoupledExpression N) /
    ((ehmDyadicNBlock X).card : ℝ)

/-- Exact compatibility theorem: Route C is a change of coordinates for the
canonical energy mean, not yet a weaker estimate. -/
theorem ehmDyadicVasyuninCoupledMean_eq_energyMean (X : ℕ) :
    ehmDyadicVasyuninCoupledMean X = ehmDyadicExactEnergyMean X := by
  unfold ehmDyadicVasyuninCoupledMean ehmDyadicExactEnergyMean
  congr 1
  apply Finset.sum_congr rfl
  intro N _
  calc
    vasyuninCoupledExpression N = coupledGcdRatioExpression N :=
      (coupledGcdRatioExpression_eq_vasyuninCoupledExpression_proved N).symm
    _ = energy N := by
      simpa only [coupledGcdRatioExpression] using
        (RH.Criteria.NymanBeurling.BCFLogTaperGcd.energy_eq_gcdRatioFormula N).symm

/-- Thus decay of the complete dyadic Vasyunin expression is exactly the H15
outer-scale analytic gate. -/
theorem tendsto_vasyuninCoupledMean_zero_iff_energyMean :
    Tendsto ehmDyadicVasyuninCoupledMean atTop (nhds 0) ↔
      Tendsto ehmDyadicExactEnergyMean atTop (nhds 0) := by
  apply tendsto_congr'
  exact Eventually.of_forall ehmDyadicVasyuninCoupledMean_eq_energyMean

/-- Under the established rational-series bridge, the genuine Route-C mean
target is equivalent to existence of complete row-Abel decay. -/
theorem tendsto_vasyuninCoupledMean_zero_iff_completeRowAbel
    (D : EhmPrimeDiscrepancyTruncatedModeData)
    (V : VaalerSawtoothPackage)
    (HS : EhmAutocorrelationR1RationalSeriesBridge) :
    Tendsto ehmDyadicVasyuninCoupledMean atTop (nhds 0) ↔
      Nonempty (EhmPrimeCompleteRowAbelSignedDecay D V) := by
  rw [tendsto_vasyuninCoupledMean_zero_iff_energyMean]
  exact (nonempty_completeRowAbelSignedDecay_iff_tendsto_energyMean
    D V HS).symm

/-- Normalization stop test: Bettin--Conrey's universal divisor-transform
constant `1/4` is not the BCF diagonal mean. -/
theorem quarter_lt_ehmDyadicDiagonalMean {X : ℕ} (hX : 2 ≤ X) :
    (1 / 4 : ℝ) < ehmDyadicDiagonalMean X := by
  exact (by norm_num : (1 / 4 : ℝ) < 1).trans
    (one_lt_ehmDyadicDiagonalMean hX)

theorem ehmDyadicDiagonalMean_ne_quarter {X : ℕ} (hX : 2 ≤ X) :
    ehmDyadicDiagonalMean X ≠ (1 / 4 : ℝ) := by
  exact ne_of_gt (quarter_lt_ehmDyadicDiagonalMean hX)

/-- The local central Bettin--Conrey correction also fails to reproduce the
retained H15 correction at the first nontrivial cutoff.  Any valid Route C
must retain a transformed off-diagonal contribution. -/
theorem routeC_localCentralCorrection_two_ne_globalCorrection :
    bettinConreyCentralCorrection 2 ≠
      -(2 * gramLinearCorrection 2 + 1) :=
  bettinConreyCentralCorrection_two_ne_neg_retained

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCMeanAudit
