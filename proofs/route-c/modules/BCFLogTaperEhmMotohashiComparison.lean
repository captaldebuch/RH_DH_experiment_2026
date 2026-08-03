import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiSobolevTranslation
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannBilinearTraceTarget
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal

/-!
# BT1-C5B: exact Ehm--Motohashi comparison

The direct Ehm route and the Estermann/Motohashi route are not estimates of
different H15 objects.  This file proves that their complete, correction-
coupled expressions are exactly equal to the original coupled GCD-ratio
expression.

The difference between the routes is therefore analytic overhead:

* the direct Ehm formulation introduces no representation-theoretic
  polynomial loss;
* the generic Motohashi local Sobolev support ledger at Casimir power `a`
  leaves residual modulus exponent `4a-2` after the two exact H15 inverse-
  modulus factors.

The comparison does not prove either missing signed cancellation estimate.
It proves that the Ehm route attacks the same target with the strictly lower
generic power budget, and transports the existing double-cofinal Ehm target
back to the full Estermann expression without a remainder.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmMotohashiComparison

open Filter Real Topology
open scoped Topology
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCompensator
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmKernel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.BCFLogTaperBettinConreyAggregate
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannAtZeroReduction
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannBilinearTraceTarget
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiSobolevTranslation
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiTraceAudit
open RH.Criteria.NymanBeurling.BCFLogTaperSpectral

/-! ## The common completed expression -/

/-- The full Estermann expression before any independent absolute-value
split of its elementary, special-value, or endpoint terms. -/
noncomputable def h15EhmMotohashiCommonExpression
    (H : EstermannAtZeroPackage) (N : ℕ) : ℝ :=
  estermannInteriorElementaryExpression N +
    (estermannInteriorValueAggregate H N).im +
      estermannEndpointCompletedExpression H N

/-- Exact reverse-completion bridge to the signed Ehm balanced/far split. -/
theorem h15EhmMotohashiCommonExpression_eq_ehmBalancedCore_add_far
    (H : EstermannAtZeroPackage) (N : ℕ) :
    h15EhmMotohashiCommonExpression H N =
      ehmS1BalancedCoupledCore N + ehmS1OneSidedFarRatioSum N := by
  exact estermannFullExpression_eq_ehmBalancedCore_add_far H N

/-- Both analytic routes are exact presentations of the original coupled
GCD-ratio expression. -/
theorem h15EhmMotohashiCommonExpression_eq_coupledGcdRatioExpression
    (H : EstermannAtZeroPackage) (N : ℕ) :
    h15EhmMotohashiCommonExpression H N =
      coupledGcdRatioExpression N := by
  rw [h15EhmMotohashiCommonExpression_eq_ehmBalancedCore_add_far,
    ← coupledGcdRatioExpression_eq_ehmS1BalancedCore_add_far]

/-- A proof-carrying estimate on the common expression.  The correction
terms remain inside the same absolute value. -/
structure H15EhmMotohashiCommonCancellationEstimate
    (H : EstermannAtZeroPackage) where
  C : ℝ
  C_pos : 0 < C
  α : ℝ
  α_pos : 0 < α
  bound : ∀ N : ℕ, 2 ≤ N →
    |h15EhmMotohashiCommonExpression H N| ≤
      C / (Real.log (N : ℝ)) ^ α

/-- The common-expression estimate is exactly the direct Ehm ratio-sector
estimate, with no loss of constants or exponent. -/
def H15EhmMotohashiCommonCancellationEstimate.toEhmRatioSector
    {H : EstermannAtZeroPackage}
    (HC : H15EhmMotohashiCommonCancellationEstimate H) :
    EhmS1RatioSectorCoupledCancellationEstimate where
  C := HC.C
  C_pos := HC.C_pos
  α := HC.α
  α_pos := HC.α_pos
  bound N hN := by
    rw [← h15EhmMotohashiCommonExpression_eq_ehmBalancedCore_add_far H N]
    exact HC.bound N hN

/-- Conversely the direct Ehm estimate proves the full Estermann expression
estimate with identical quantitative data. -/
def EhmS1RatioSectorCoupledCancellationEstimate.toCommon
    (HE : EhmS1RatioSectorCoupledCancellationEstimate)
    (H : EstermannAtZeroPackage) :
    H15EhmMotohashiCommonCancellationEstimate H where
  C := HE.C
  C_pos := HE.C_pos
  α := HE.α
  α_pos := HE.α_pos
  bound N hN := by
    rw [h15EhmMotohashiCommonExpression_eq_ehmBalancedCore_add_far]
    exact HE.bound N hN

/-! ## Power-budget comparison -/

/-- The direct Ehm algebra adds no representation-theoretic modulus power.
This is an overhead ledger, not a decay theorem. -/
def h15EhmDirectResidualExponent : ℕ := 0

/-- Direct-route diagnostic after a hypothetical gain of `gainPower`
modulus powers. -/
noncomputable def h15EhmDirectPowerProfile
    (gainPower N : ℕ) : ℝ :=
  1 / (((N + 1 : ℕ) : ℝ) ^ gainPower)

@[simp]
theorem h15EhmDirectPowerProfile_zero_gain (N : ℕ) :
    h15EhmDirectPowerProfile 0 N = 1 := by
  simp [h15EhmDirectPowerProfile]

theorem h15EhmDirectPowerProfile_one_gain (N : ℕ) :
    h15EhmDirectPowerProfile 1 N = (((N + 1 : ℕ) : ℝ))⁻¹ := by
  simp [h15EhmDirectPowerProfile, div_eq_mul_inv]

theorem h15EhmDirectPowerProfile_one_gain_tendsto_zero :
    Tendsto (h15EhmDirectPowerProfile 1) atTop (nhds 0) := by
  have hinv : Tendsto
      (fun N : ℕ => (((N + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) := by
    simpa using (tendsto_add_atTop_iff_nat (α := ℝ) 1).2
      tendsto_inv_atTop_nhds_zero_nat
  apply hinv.congr'
  exact Filter.Eventually.of_forall fun N =>
    (h15EhmDirectPowerProfile_one_gain N).symm

/-- The exact Motohashi generic-surplus target after local translation. -/
theorem h15MotohashiRequiredGain_iwasawaRadialOrder
    (a : ℕ) (ha : 1 ≤ a) :
    h15MotohashiResidualExponent
          (h15MotohashiIwasawaRadialOrder a) + 1 =
      4 * a - 1 := by
  rw [h15MotohashiResidualExponent_iwasawaRadialOrder a ha]
  omega

/-- At every positive Casimir power, the direct Ehm power ledger requires
strictly fewer modulus powers than the generic Motohashi support ledger. -/
theorem h15EhmDirectRequiredGain_lt_motohashiRequiredGain
    (a : ℕ) (ha : 1 ≤ a) :
    h15EhmDirectResidualExponent + 1 <
      h15MotohashiResidualExponent
          (h15MotohashiIwasawaRadialOrder a) + 1 := by
  rw [h15MotohashiResidualExponent_iwasawaRadialOrder a ha]
  simp [h15EhmDirectResidualExponent]
  omega

/-- For the crude `a=3` diagnostic, the comparison is one direct-route
power versus eleven Motohashi powers. -/
theorem h15EhmDirectRequiredGain_lt_motohashiCrudeThree :
    h15EhmDirectResidualExponent + 1 <
      h15MotohashiResidualExponent
          (h15MotohashiIwasawaRadialOrder 3) + 1 := by
  norm_num [h15EhmDirectResidualExponent,
    h15MotohashiResidualExponent_crudeCasimirThree]

/-! ## Cofinal transfer to the common expression -/

/-- The already-isolated double-cofinal Ehm boundary target controls the
full Estermann expression at arbitrarily large outer cutoffs.  No rate in
`N` is introduced. -/
theorem h15EhmMotohashiCommonExpression_cofinally_small_of_doubleCofinal
    (H : EstermannAtZeroPackage)
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (HB : EhmDoubleCofinalBoundaryVanishing ehmR1) :
    ∀ ε : ℝ, 0 < ε → ∀ N₀ : ℕ,
      ∃ N : ℕ, N₀ ≤ N ∧ 2 ≤ N ∧
        |h15EhmMotohashiCommonExpression H N| < ε := by
  intro ε hε N₀
  let K : EhmKernelPackage :=
    ehmS1PointwiseKernelPackageProved.toEhmKernelPackage
  rcases coupledGcdRatioExpression_cofinally_small_of_doubleCofinal
      K HS HB ε hε N₀ with ⟨N, hN₀, hN, hsmall⟩
  refine ⟨N, hN₀, hN, ?_⟩
  rw [h15EhmMotohashiCommonExpression_eq_coupledGcdRatioExpression]
  exact hsmall

end RH.Criteria.NymanBeurling.BCFLogTaperEhmMotohashiComparison
