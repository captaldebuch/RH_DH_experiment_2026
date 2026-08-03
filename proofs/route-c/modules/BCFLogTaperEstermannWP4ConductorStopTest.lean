import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmMotohashiComparison
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannKuznetsovProof

/-!
# WP4: quantitative conductor stop test

The Mellin--Barnes assembly and the finite Fourier/Kloosterman completion are
already exact identities.  This module keeps those identities separate from
the one new analytic assertion needed by the spectral route.

For Casimir power `a ≥ 1`, the sharp local Iwasawa support calculation costs
`q^(4a)`.  The two proved inverse-modulus factors in the H15 coefficient leave
residual exponent `4a - 2`.  Therefore an integral conductor gain closes the
power budget precisely when

`gainPower > 4a - 2`,

or equivalently `gainPower ≥ 4a - 1`.  Equality with `4a - 2` gives only a
constant majorant.  The classical Motohashi identity supplies a change of
representation, but no positive uniform H15 conductor power; this file does
not manufacture one.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannWP4ConductorStopTest

open Complex Filter Real Topology
open scoped Topology
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMotohashiComparison
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannAtZeroReduction
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannBilinearTraceTarget
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannH15MellinAssembly
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiSobolevTranslation
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiTraceAudit
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannRegularizedKernels
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi
open RH.Criteria.NymanBeurling.BCFLogTaperSpectral

/-! ## The theorem-backed transform layer -/

/-- Parameters needed to evaluate the already-proved Mellin--Barnes and DFT
identities.  There is no spectral estimate in this structure. -/
structure H15WP4ExactTransformData where
  H : EstermannAtZeroPackage
  eta : ℝ
  eta_pos : 0 < eta
  verticalLine : ℝ
  verticalLine_gt_one : 1 < verticalLine

/-- The full common expression is exactly the original signed H15 coupled
expression; no contour or spectral hypothesis is used here. -/
theorem H15WP4ExactTransformData.common_eq_coupled
    (E : H15WP4ExactTransformData) (N : ℕ) :
    h15EhmMotohashiCommonExpression E.H N =
      coupledGcdRatioExpression N :=
  h15EhmMotohashiCommonExpression_eq_coupledGcdRatioExpression E.H N

/-- The assembled Mellin--Barnes integral is exactly the zero-mode-corrected
joint bilinear kernel.  In particular the `(q,m)` dependence has not been
discarded in order to invoke an ordinary one-frequency Kuznetsov formula. -/
theorem H15WP4ExactTransformData.mellinBarnes_eq_jointBilinear
    (E : H15WP4ExactTransformData) (N : ℕ) :
    (∫ t : ℝ,
      h15InteriorNaturalDualIntegrand N
        (estermannGaussianEvaluationWeight E.eta)
        (estermannVerticalPoint E.verticalLine t)) =
      h15InteriorZeroCorrectedBilinearKernelAggregate N E.eta
        E.verticalLine := by
  exact h15Interior_integral_eq_zeroCorrectedBilinearKernelAggregate
    N E.eta E.verticalLine E.eta_pos E.verticalLine_gt_one

/-- The finite DFT completion, including its degenerate zero mode, is an
exact equality before any spectral estimate is requested. -/
theorem H15WP4ExactTransformData.completed_eq_zeroCorrectedBilinear
    (_E : H15WP4ExactTransformData) (N g q : ℕ) [NeZero q]
    (eta c : ℝ) :
    h15TwoSignCompletedKernelSeries N g q eta c =
      h15TwoSignZeroCorrectedBilinearKernelSeries N g q eta c :=
  h15TwoSignCompletedKernelSeries_eq_zeroCorrectedBilinear N g q eta c

/-! ## Exact pass/fail exponent -/

/-- Smallest integral conductor exponent which strictly dominates the
generic H15 residual cost at Casimir power `a`. -/
def h15WP4MinimumClosingGain (a : ℕ) : ℕ := 4 * a - 1

theorem h15WP4MinimumClosingGain_eq_residual_add_one
    (a : ℕ) (ha : 1 ≤ a) :
    h15WP4MinimumClosingGain a =
      h15MotohashiResidualExponent
          (h15MotohashiIwasawaRadialOrder a) + 1 := by
  rw [h15MotohashiResidualExponent_iwasawaRadialOrder a ha]
  simp [h15WP4MinimumClosingGain]
  omega

/-- The crude source-audit choice `a=3` requires eleven conductor powers. -/
theorem h15WP4MinimumClosingGain_three :
    h15WP4MinimumClosingGain 3 = 11 := by
  norm_num [h15WP4MinimumClosingGain]

/-- At or below the residual exponent, the unsigned power profile is at
least one.  Hence this majorant alone cannot certify decay. -/
theorem one_le_h15MotohashiTracePowerProfile_of_gain_le_residual
    (seminormOrder gainPower N : ℕ)
    (hgain : gainPower ≤ h15MotohashiResidualExponent seminormOrder) :
    1 ≤ h15MotohashiTracePowerProfile seminormOrder gainPower N := by
  let x : ℝ := ((N + 1 : ℕ) : ℝ)
  let r := h15MotohashiResidualExponent seminormOrder
  have hx : 1 ≤ x := by
    dsimp [x]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
  have hx0 : x ^ gainPower ≠ 0 := by
    apply pow_ne_zero
    dsimp [x]
    positivity
  have hr : r = (r - gainPower) + gainPower :=
    (Nat.sub_add_cancel hgain).symm
  unfold h15MotohashiTracePowerProfile
  change 1 ≤ x ^ r / x ^ gainPower
  rw [hr, pow_add, mul_div_cancel_right₀ _ hx0]
  exact one_le_pow₀ hx

/-- Therefore every subcritical or critical profile fails the zero-limit
stop test.  This says nothing against extra signed cancellation not encoded
by the profile. -/
theorem h15MotohashiTracePowerProfile_not_tendsto_zero_of_gain_le_residual
    (seminormOrder gainPower : ℕ)
    (hgain : gainPower ≤ h15MotohashiResidualExponent seminormOrder) :
    ¬ Tendsto (h15MotohashiTracePowerProfile seminormOrder gainPower)
        atTop (nhds 0) := by
  intro h
  have hbad : (1 : ℝ) ≤ 0 := by
    apply ge_of_tendsto h
    exact Filter.Eventually.of_forall fun N =>
      one_le_h15MotohashiTracePowerProfile_of_gain_le_residual
        seminormOrder gainPower N hgain
  norm_num at hbad

/-! ## The sole new spectral input -/

/-- A signed H15 conductor estimate after the exact transform layer.

`signed_trace_bound` is the only analytic cancellation field.  All other
fields are parameters or positivity bookkeeping.  In particular, no
Mellin--Barnes, DFT, correction-matching, or route-comparison theorem is
assumed here. -/
structure H15WP4SignedConductorDecayInput
    (E : H15WP4ExactTransformData) where
  casimirPower : ℕ
  casimirPower_pos : 0 < casimirPower
  gainPower : ℕ
  C : ℝ
  C_nonneg : 0 ≤ C
  signed_trace_bound : ∀ N : ℕ,
    |h15EhmMotohashiCommonExpression E.H N| ≤
      C *
        h15MotohashiTracePowerProfile
          (h15MotohashiIwasawaRadialOrder casimirPower) gainPower N

/-- A strictly supercritical conductor gain is bounded by the canonical
one-surplus profile. -/
theorem H15WP4SignedConductorDecayInput.abs_common_le_one_surplus
    {E : H15WP4ExactTransformData}
    (S : H15WP4SignedConductorDecayInput E)
    (hgain :
      h15MotohashiResidualExponent
          (h15MotohashiIwasawaRadialOrder S.casimirPower) < S.gainPower)
    (N : ℕ) :
    |h15EhmMotohashiCommonExpression E.H N| ≤
      S.C * h15MotohashiTracePowerProfile
        (h15MotohashiIwasawaRadialOrder S.casimirPower)
        (h15MotohashiResidualExponent
          (h15MotohashiIwasawaRadialOrder S.casimirPower) + 1) N := by
  let x : ℝ := ((N + 1 : ℕ) : ℝ)
  let r := h15MotohashiResidualExponent
    (h15MotohashiIwasawaRadialOrder S.casimirPower)
  have hx : 1 ≤ x := by
    dsimp [x]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
  have hpow : x ^ (r + 1) ≤ x ^ S.gainPower :=
    pow_le_pow_right₀ hx ((Nat.lt_iff_add_one_le.mp hgain))
  have hnum : 0 ≤ x ^ r := by positivity
  have hden : 0 < x ^ (r + 1) := by positivity
  have hprofile :
      h15MotohashiTracePowerProfile
          (h15MotohashiIwasawaRadialOrder S.casimirPower) S.gainPower N ≤
        h15MotohashiTracePowerProfile
          (h15MotohashiIwasawaRadialOrder S.casimirPower) (r + 1) N := by
    unfold h15MotohashiTracePowerProfile
    change x ^ r / x ^ S.gainPower ≤ x ^ r / x ^ (r + 1)
    exact div_le_div_of_nonneg_left hnum hden hpow
  exact (S.signed_trace_bound N).trans
    (mul_le_mul_of_nonneg_left hprofile S.C_nonneg)

/-- **WP4 pass theorem.**  Any signed trace estimate with conductor exponent
strictly exceeding the exact H15 residual exponent forces the complete H15
expression to vanish. -/
theorem H15WP4SignedConductorDecayInput.common_tendsto_zero_of_strict_gain
    {E : H15WP4ExactTransformData}
    (S : H15WP4SignedConductorDecayInput E)
    (hgain :
      h15MotohashiResidualExponent
          (h15MotohashiIwasawaRadialOrder S.casimirPower) < S.gainPower) :
    Tendsto (h15EhmMotohashiCommonExpression E.H) atTop (nhds 0) := by
  apply squeeze_zero_norm
  · intro N
    simpa [Real.norm_eq_abs] using S.abs_common_le_one_surplus hgain N
  · have hconst : Tendsto (fun _ : ℕ => S.C) atTop (nhds S.C) :=
      tendsto_const_nhds
    simpa using hconst.mul
      (h15MotohashiTracePowerProfile_one_power_surplus_tendsto_zero
        (h15MotohashiIwasawaRadialOrder S.casimirPower))

/-- The same input controls the original coupled GCD-ratio expression, since
the transform layer is exact. -/
theorem H15WP4SignedConductorDecayInput.coupled_tendsto_zero_of_strict_gain
    {E : H15WP4ExactTransformData}
    (S : H15WP4SignedConductorDecayInput E)
    (hgain :
      h15MotohashiResidualExponent
          (h15MotohashiIwasawaRadialOrder S.casimirPower) < S.gainPower) :
    Tendsto coupledGcdRatioExpression atTop (nhds 0) := by
  apply (S.common_tendsto_zero_of_strict_gain hgain).congr'
  exact Filter.Eventually.of_forall fun N => E.common_eq_coupled N

/-- In integral exponents, passing the stop test is exactly the threshold
`gainPower ≥ 4a-1`. -/
theorem h15WP4_gain_pass_iff
    (a gainPower : ℕ) (ha : 1 ≤ a) :
    h15MotohashiResidualExponent (h15MotohashiIwasawaRadialOrder a) <
        gainPower ↔
      h15WP4MinimumClosingGain a ≤ gainPower := by
  rw [h15WP4MinimumClosingGain_eq_residual_add_one a ha]
  exact Nat.lt_iff_add_one_le

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannWP4ConductorStopTest
