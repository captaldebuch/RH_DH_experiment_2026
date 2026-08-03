import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmEarlyBlockCorrection
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannWP4ConductorStopTest

/-!
# Geometric Ehm allocation versus the spectral conductor ledger

The normalized geometric weight is indexed by the Ehm divisor block, not by
the Estermann/Kuznetsov modulus.  This module proves the exact consequences:

* a fixed geometric weight commutes with the proved Mellin--Barnes identity
  by linearity;
* the allocated correction reassembles exactly only after summing all
  blocks; and
* multiplication by a fixed positive block weight does not change the WP4
  conductor threshold.  At the critical conductor exponent the weighted
  profile is a positive constant, while one surplus power still tends to
  zero.

No blockwise diagonal/Eisenstein correction identity is asserted.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmGeometricSpectralCompatibility

open Complex Filter MeasureTheory Real Topology
open scoped BigOperators Topology
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicCorrectionAbel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmEarlyBlockCorrection
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannBilinearTraceTarget
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannH15MellinAssembly
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiSobolevTranslation
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiTraceAudit
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannWP4ConductorStopTest

/-- Every normalized geometric block weight is strictly positive, including
the first block. -/
theorem ehmGeometricCorrectionWeight_pos (X L k : ℕ) :
    0 < ehmGeometricCorrectionWeight X L k := by
  unfold ehmGeometricCorrectionWeight
  exact div_pos (by positivity) (ehmGeometricCorrectionMass_pos X L)

/-- A geometric weight is independent of the spectral conductor variable.
This small identity makes explicit why it cannot itself be recorded as a
power of `q`. -/
theorem ehmGeometricCorrectionWeight_conductor_independent
    (X L k q q' : ℕ) :
    (fun _conductor : ℕ ↦ ehmGeometricCorrectionWeight X L k) q =
      (fun _conductor : ℕ ↦ ehmGeometricCorrectionWeight X L k) q' := rfl

/-- Scalar multiplication by a geometric block weight commutes with the
already-proved global Mellin--Barnes identity.  This is a linearity theorem;
it does not identify an Ehm divisor block with an Estermann modulus block. -/
theorem geometricWeight_mul_mellinBarnes_eq_jointBilinear
    (E : H15WP4ExactTransformData) (X L k N : ℕ) :
    (∫ t : ℝ,
      (ehmGeometricCorrectionWeight X L k : ℂ) *
        h15InteriorNaturalDualIntegrand N
          (estermannGaussianEvaluationWeight E.eta)
          (estermannVerticalPoint E.verticalLine t)) =
      (ehmGeometricCorrectionWeight X L k : ℂ) *
        h15InteriorZeroCorrectedBilinearKernelAggregate N E.eta
          E.verticalLine := by
  rw [integral_const_mul, E.mellinBarnes_eq_jointBilinear]

/-- The canonical allocation reproduces the retained main-plus-linear
correction exactly after summing all actual divisor blocks. -/
theorem sum_geometricWeight_mul_retainedCorrection
    (R1 : ℝ → ℝ) (X J L : ℕ) :
    (∑ k ∈ ehmShiftedDyadicDIndices X L,
      ehmGeometricCorrectionWeight X L k *
        ehmH15RetainedCorrection R1 X J) =
      ehmH15RetainedCorrection R1 X J := by
  rw [← Finset.sum_mul, sum_ehmGeometricCorrectionWeight, one_mul]

/-! ## The weighted conductor stop test -/

/-- WP4 power profile after multiplication by one fixed geometric block
weight. -/
noncomputable def ehmGeometricWeightedTracePowerProfile
    (X L k seminormOrder gainPower conductor : ℕ) : ℝ :=
  ehmGeometricCorrectionWeight X L k *
    h15MotohashiTracePowerProfile seminormOrder gainPower conductor

/-- At the critical conductor exponent the weighted profile is the positive
constant block weight, rather than a decaying function. -/
theorem ehmGeometricWeightedTracePowerProfile_critical
    (X L k seminormOrder conductor : ℕ) :
    ehmGeometricWeightedTracePowerProfile X L k seminormOrder
        (h15MotohashiResidualExponent seminormOrder) conductor =
      ehmGeometricCorrectionWeight X L k := by
  simp [ehmGeometricWeightedTracePowerProfile,
    h15MotohashiTracePowerProfile_critical]

/-- Therefore geometric localization does not rescue a critical spectral
conductor budget. -/
theorem ehmGeometricWeightedTracePowerProfile_critical_not_tendsto_zero
    (X L k seminormOrder : ℕ) :
    ¬ Tendsto
      (ehmGeometricWeightedTracePowerProfile X L k seminormOrder
        (h15MotohashiResidualExponent seminormOrder))
      atTop (nhds 0) := by
  intro h
  have hbad : ehmGeometricCorrectionWeight X L k ≤ 0 := by
    apply ge_of_tendsto h
    exact Filter.Eventually.of_forall fun conductor => by
      rw [ehmGeometricWeightedTracePowerProfile_critical]
  exact (not_le_of_gt (ehmGeometricCorrectionWeight_pos X L k)) hbad

/-- One surplus conductor power still gives decay after geometric
localization. -/
theorem ehmGeometricWeightedTracePowerProfile_one_surplus_tendsto_zero
    (X L k seminormOrder : ℕ) :
    Tendsto
      (ehmGeometricWeightedTracePowerProfile X L k seminormOrder
        (h15MotohashiResidualExponent seminormOrder + 1))
      atTop (nhds 0) := by
  have hconst : Tendsto
      (fun _ : ℕ ↦ ehmGeometricCorrectionWeight X L k)
      atTop (nhds (ehmGeometricCorrectionWeight X L k)) :=
    tendsto_const_nhds
  simpa [ehmGeometricWeightedTracePowerProfile] using hconst.mul
    (h15MotohashiTracePowerProfile_one_power_surplus_tendsto_zero
      seminormOrder)

/-- The exact integral pass threshold is consequently unchanged:
`gainPower ≥ 4a-1`. -/
theorem ehmGeometricWeight_gain_pass_iff
    (a gainPower : ℕ) (ha : 1 ≤ a) :
    h15MotohashiResidualExponent (h15MotohashiIwasawaRadialOrder a) <
        gainPower ↔
      h15WP4MinimumClosingGain a ≤ gainPower :=
  h15WP4_gain_pass_iff a gainPower ha

end RH.Criteria.NymanBeurling.BCFLogTaperEhmGeometricSpectralCompatibility
