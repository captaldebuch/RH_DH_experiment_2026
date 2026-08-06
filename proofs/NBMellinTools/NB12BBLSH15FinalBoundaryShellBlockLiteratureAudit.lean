/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FinalBoundaryShellBlockScale

/-!
# NB12zzm: literature compatibility and exponent stop test

This file records the exact ranges and coefficient envelope of a direct H15
interval block, and combines two previously proved published-tool audits:

* Bettin--Chandee uses an inverse residue, whereas the H15 dual phase is direct;
* the elementary direct additive large sieve has no saving at fixed frequency.

This is a stop test, not an impossibility theorem.  A completion, duality, or
new correction-coupled shifted-convolution estimate may still close the gate.
-/

open Filter
open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate
open Complex

namespace NBMellinTools.NB12

/-- Exact dyadic and cutoff ranges of the two distinct moduli in every direct
interval block. -/
theorem h15IntervalBlockSupportedModuli_ranges
    {N g Q q q' : ℕ}
    (hq : q ∈ h15BettinChandeeSupportedNatBlock N g Q)
    (hq' : q' ∈ h15BettinChandeeSupportedNatBlock N g Q) :
    Q ≤ q ∧ q < 2 * Q ∧ g * q ≤ N ∧
      Q ≤ q' ∧ q' < 2 * Q ∧ g * q' ≤ N := by
  have hqBounds := mem_h15BettinChandeeSupportedNatBlock.mp hq
  have hq'Bounds := mem_h15BettinChandeeSupportedNatBlock.mp hq'
  exact ⟨hqBounds.1, hqBounds.2.1, hqBounds.2.2,
    hq'Bounds.1, hq'Bounds.2.1, hq'Bounds.2.2⟩

/-- The product of the two original H15 endpoint coefficients has the exact
inverse-fourth-power envelope used in the block audit. -/
theorem abs_h15IntervalBlockEndpointWeightProduct_le
    {N g U L L' q q' d d' u v : ℕ}
    (hN : 2 ≤ N) (hg : 1 ≤ g) (hU : 0 < U)
    (hq : 0 < q) (hq' : 0 < q')
    (hu : u ∈ h15NormalizedSuperperiodBoundarySupport U L q)
    (hv : v ∈ h15NormalizedSuperperiodBoundarySupport U L' q') :
    |h15NormalizedProgressionCoupledBoundaryPointWeight N g U L q d u *
        h15NormalizedProgressionCoupledBoundaryPointWeight N g U L' q' d' v| ≤
      (1 / (U : ℝ)) ^ 4 := by
  rw [abs_mul]
  have huBound :=
    abs_h15NormalizedProgressionCoupledBoundaryPointWeight_le
      (d := d) hN hg hU hq hu
  have hvBound :=
    abs_h15NormalizedProgressionCoupledBoundaryPointWeight_le
      (d := d') hN hg hU hq' hv
  calc
    |h15NormalizedProgressionCoupledBoundaryPointWeight N g U L q d u| *
        |h15NormalizedProgressionCoupledBoundaryPointWeight N g U L' q' d' v| ≤
      (1 / (U : ℝ)) ^ 2 * (1 / (U : ℝ)) ^ 2 := by
        exact mul_le_mul huBound hvBound (abs_nonneg _) (by positivity)
    _ = (1 / (U : ℝ)) ^ 4 := by ring

/-! ## Literal direct/inverse mismatch -/

theorem zmod_five_two_ne_inverseResidue :
    (2 : ZMod 5) ≠
      (((ZMod.unitOfCoprime 2 (by decide : Nat.Coprime 2 5))⁻¹ :
        (ZMod 5)ˣ).val) := by
  decide

/-- A concrete reduced residue already distinguishes the direct H15 phase
from the inverse-residue phase in Bettin--Chandee Theorem 1. -/
theorem stdAddChar_zmod_five_direct_ne_inverse :
    ZMod.stdAddChar (2 : ZMod 5) ≠
      ZMod.stdAddChar
        (((ZMod.unitOfCoprime 2 (by decide : Nat.Coprime 2 5))⁻¹ :
          (ZMod 5)ˣ).val) := by
  intro h
  exact zmod_five_two_ne_inverseResidue
    (ZMod.injective_stdAddChar h)

/-! ## Published exponent stop test at fixed frequency -/

theorem h15BettinChandeeFixedFrequencyExponent_nonneg :
    0 ≤ h15BettinChandeeWorstScaledExponent 0 := by
  rw [h15BettinChandeeWorstScaledExponent_zero]
  norm_num

theorem h15DirectAdditiveBalancedExponent_zero :
    h15DirectAdditiveBalancedExponent 0 = 2 := by
  norm_num [h15DirectAdditiveBalancedExponent]

theorem h15DirectAdditiveFixedFrequencyExponent_nonneg :
    0 ≤ h15DirectAdditiveBalancedExponent 0 := by
  rw [h15DirectAdditiveBalancedExponent_zero]
  norm_num

/-- Combined formal stop test for direct application of the two audited
published-tool routes to the fixed/low-frequency interval blocks. -/
def H15IntervalBlockPublishedToolStopTest : Prop :=
  H15PostFunctionalEquationPhaseIsDirect ∧
    0 ≤ h15BettinChandeeWorstScaledExponent 0 ∧
      0 ≤ h15DirectAdditiveBalancedExponent 0

theorem h15IntervalBlockPublishedToolStopTest :
    H15IntervalBlockPublishedToolStopTest := by
  exact ⟨h15PostFunctionalEquationPhaseIsDirect,
    h15BettinChandeeFixedFrequencyExponent_nonneg,
    h15DirectAdditiveFixedFrequencyExponent_nonneg⟩

end NBMellinTools.NB12
