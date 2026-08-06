/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FinalBoundaryShellBlockDecay

/-!
# NB12zzk: direct interval form of the signed shell blocks

The analytic block is rewritten directly on endpoint pairs.  For positive
width `K`, quotient block `j` is exactly the cyclic-distance interval
`j*K <= distance < (j+1)*K`.  This exposes the variables and coefficient
support expected by shifted-convolution and additive large-sieve estimates.
-/

open Filter
open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate
open Complex

namespace NBMellinTools.NB12

theorem natDiv_eq_iff_mem_mulInterval
    {n j K : ℕ} (hK : 0 < K) :
    n / K = j ↔ j * K ≤ n ∧ n < (j + 1) * K := by
  constructor
  · intro h
    constructor
    · apply (Nat.le_div_iff_mul_le hK).mp
      omega
    · apply (Nat.div_lt_iff_lt_mul hK).mp
      omega
  · rintro ⟨hlower, hupper⟩
    have hle : j ≤ n / K := (Nat.le_div_iff_mul_le hK).2 hlower
    have hlt : n / K < j + 1 := (Nat.div_lt_iff_lt_mul hK).2 hupper
    omega

/-! ## Direct endpoint-pair blocks -/

noncomputable def h15NormalizedBoundaryDifferenceIntervalBlockLedger
    (N g r U Q K : ℕ) (j : Fin (h15BoundarySpacingBlockCount Q K)) : ℝ :=
  h15NormalizedBoundaryEndpointPairFilteredPhaseAggregate N g r U Q
    h15DifferenceEndpointPairPhase
    (fun r u q v q' =>
      ¬ h15DifferenceEndpointPairCollision r u q v q' ∧
        h15DifferenceEndpointPairCyclicDistance r u q v q' / K = j.val)

noncomputable def h15NormalizedBoundarySumIntervalBlockLedger
    (N g r U Q K : ℕ) (j : Fin (h15BoundarySpacingBlockCount Q K)) : ℝ :=
  h15NormalizedBoundaryEndpointPairFilteredPhaseAggregate N g r U Q
    h15SumEndpointPairPhase
    (fun r u q v q' =>
      ¬ h15SumEndpointPairCollision r u q v q' ∧
        h15SumEndpointPairCyclicDistance r u q v q' / K = j.val)

theorem h15NormalizedBoundaryDifferenceSeparatedLedger_eq_sum_intervalBlocks
    {N g r U Q K : ℕ} (hQ : 0 < Q) :
    h15NormalizedBoundaryDifferenceSeparatedLedger N g r U Q =
      ∑ j : Fin (h15BoundarySpacingBlockCount Q K),
        h15NormalizedBoundaryDifferenceIntervalBlockLedger N g r U Q K j := by
  classical
  unfold h15NormalizedBoundaryDifferenceSeparatedLedger
    h15NormalizedBoundaryDifferenceIntervalBlockLedger
    h15NormalizedBoundaryEndpointPairFilteredPhaseAggregate
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q' hq'Erase
  have hq'Mem := Finset.mem_of_mem_erase hq'Erase
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d' _hd'
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _hu
  let shellOf (v : ℕ) : Fin (h15BoundarySpacingShellCount Q) :=
    ⟨h15DifferenceEndpointPairCyclicDistance r u q v q',
      h15DifferenceEndpointPairCyclicDistance_lt_shellCount hQ hq hq'Mem⟩
  let blockOf (v : ℕ) : Fin (h15BoundarySpacingBlockCount Q K) :=
    ⟨(shellOf v).val / K,
      h15BoundarySpacingShell_div_lt_blockCount (shellOf v)⟩
  simpa only [Finset.filter_filter, and_assoc, shellOf, blockOf, Fin.ext_iff] using
    (Finset.sum_fiberwise
      ((h15NormalizedSuperperiodBoundarySupport U
        (h15SquareDivisorProgressionModulus g d') q').filter
          (fun v => ¬ h15DifferenceEndpointPairCollision r u q v q'))
      blockOf
      (fun v =>
        (h15NormalizedProgressionCoupledBoundaryPointWeight N g U
            (h15SquareDivisorProgressionModulus g d) q d u *
          h15NormalizedProgressionCoupledBoundaryPointWeight N g U
            (h15SquareDivisorProgressionModulus g d') q' d' v) *
          h15DifferenceEndpointPairPhase r u q v q'))

theorem h15NormalizedBoundarySumSeparatedLedger_eq_sum_intervalBlocks
    {N g r U Q K : ℕ} (hQ : 0 < Q) :
    h15NormalizedBoundarySumSeparatedLedger N g r U Q =
      ∑ j : Fin (h15BoundarySpacingBlockCount Q K),
        h15NormalizedBoundarySumIntervalBlockLedger N g r U Q K j := by
  classical
  unfold h15NormalizedBoundarySumSeparatedLedger
    h15NormalizedBoundarySumIntervalBlockLedger
    h15NormalizedBoundaryEndpointPairFilteredPhaseAggregate
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q' hq'Erase
  have hq'Mem := Finset.mem_of_mem_erase hq'Erase
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d' _hd'
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _hu
  let shellOf (v : ℕ) : Fin (h15BoundarySpacingShellCount Q) :=
    ⟨h15SumEndpointPairCyclicDistance r u q v q',
      h15SumEndpointPairCyclicDistance_lt_shellCount hQ hq hq'Mem⟩
  let blockOf (v : ℕ) : Fin (h15BoundarySpacingBlockCount Q K) :=
    ⟨(shellOf v).val / K,
      h15BoundarySpacingShell_div_lt_blockCount (shellOf v)⟩
  simpa only [Finset.filter_filter, and_assoc, shellOf, blockOf, Fin.ext_iff] using
    (Finset.sum_fiberwise
      ((h15NormalizedSuperperiodBoundarySupport U
        (h15SquareDivisorProgressionModulus g d') q').filter
          (fun v => ¬ h15SumEndpointPairCollision r u q v q'))
      blockOf
      (fun v =>
        (h15NormalizedProgressionCoupledBoundaryPointWeight N g U
            (h15SquareDivisorProgressionModulus g d) q d u *
          h15NormalizedProgressionCoupledBoundaryPointWeight N g U
            (h15SquareDivisorProgressionModulus g d') q' d' v) *
          h15SumEndpointPairPhase r u q v q'))

noncomputable def h15NormalizedBoundarySignedIntervalBlockLedger
    (N g r U Q K : ℕ) (j : Fin (h15BoundarySpacingBlockCount Q K)) : ℝ :=
  (h15NormalizedBoundaryDifferenceIntervalBlockLedger N g r U Q K j -
    h15NormalizedBoundarySumIntervalBlockLedger N g r U Q K j) / 2

theorem h15NormalizedBoundaryPhaseSeparatedLedger_eq_sum_signedIntervalBlocks
    {N g r U Q K : ℕ} (hQ : 0 < Q) :
    h15NormalizedBoundaryPhaseSeparatedLedger N g r U Q =
      ∑ j : Fin (h15BoundarySpacingBlockCount Q K),
        h15NormalizedBoundarySignedIntervalBlockLedger N g r U Q K j := by
  unfold h15NormalizedBoundaryPhaseSeparatedLedger
    h15NormalizedBoundarySignedIntervalBlockLedger
  rw [h15NormalizedBoundaryDifferenceSeparatedLedger_eq_sum_intervalBlocks hQ,
    h15NormalizedBoundarySumSeparatedLedger_eq_sum_intervalBlocks hQ,
    ← Finset.sum_div, Finset.sum_sub_distrib]

/-- For positive width, the direct difference-block predicate is literally a
half-open cyclic-distance interval. -/
theorem h15DifferenceIntervalBlockPredicate_iff
    {r u q v q' K : ℕ} (hK : 0 < K) (j : ℕ) :
    (¬ h15DifferenceEndpointPairCollision r u q v q' ∧
        h15DifferenceEndpointPairCyclicDistance r u q v q' / K = j) ↔
      (¬ h15DifferenceEndpointPairCollision r u q v q' ∧
        j * K ≤ h15DifferenceEndpointPairCyclicDistance r u q v q' ∧
        h15DifferenceEndpointPairCyclicDistance r u q v q' < (j + 1) * K) := by
  rw [and_congr_right_iff]
  intro _hsep
  exact natDiv_eq_iff_mem_mulInterval hK

theorem h15SumIntervalBlockPredicate_iff
    {r u q v q' K : ℕ} (hK : 0 < K) (j : ℕ) :
    (¬ h15SumEndpointPairCollision r u q v q' ∧
        h15SumEndpointPairCyclicDistance r u q v q' / K = j) ↔
      (¬ h15SumEndpointPairCollision r u q v q' ∧
        j * K ≤ h15SumEndpointPairCyclicDistance r u q v q' ∧
        h15SumEndpointPairCyclicDistance r u q v q' < (j + 1) * K) := by
  rw [and_congr_right_iff]
  intro _hsep
  exact natDiv_eq_iff_mem_mulInterval hK

noncomputable def h15NormalizedBoundaryAbsoluteSignedIntervalBlockBudget
    (N g r U Q K : ℕ) : ℝ :=
  ∑ j : Fin (h15BoundarySpacingBlockCount Q K),
    |h15NormalizedBoundarySignedIntervalBlockLedger N g r U Q K j|

theorem h15CorrectionCoupledCrossModulusFrequencyDispersion_of_intervalBlockBudget
    {N g r U Q K : ℕ} (hQ : 0 < Q) {Delta : ℝ} (hDelta : 0 ≤ Delta)
    (hbudget :
      h15NormalizedBoundaryAbsoluteSignedIntervalBlockBudget N g r U Q K +
          h15NormalizedBoundaryPhaseCollisionDefect N g r U Q ≤
        Delta * h15NormalizedBoundaryCrossModulusFrequencyEnergy N g U Q) :
    H15CorrectionCoupledCrossModulusFrequencyDispersion N g r U Q Delta := by
  rw [h15CorrectionCoupledCrossModulusFrequencyDispersion_iff_phaseSeparated hQ,
    h15NormalizedBoundaryPhaseSeparatedLedger_eq_sum_signedIntervalBlocks hQ]
  constructor
  · exact hDelta
  · unfold h15NormalizedBoundaryAbsoluteSignedIntervalBlockBudget at hbudget
    have hblocks :
        (∑ j : Fin (h15BoundarySpacingBlockCount Q K),
            h15NormalizedBoundarySignedIntervalBlockLedger N g r U Q K j) ≤
          ∑ j : Fin (h15BoundarySpacingBlockCount Q K),
            |h15NormalizedBoundarySignedIntervalBlockLedger N g r U Q K j| := by
      calc
        (∑ j : Fin (h15BoundarySpacingBlockCount Q K),
            h15NormalizedBoundarySignedIntervalBlockLedger N g r U Q K j) ≤
            |∑ j : Fin (h15BoundarySpacingBlockCount Q K),
              h15NormalizedBoundarySignedIntervalBlockLedger N g r U Q K j| :=
          le_abs_self _
        _ ≤ ∑ j : Fin (h15BoundarySpacingBlockCount Q K),
            |h15NormalizedBoundarySignedIntervalBlockLedger N g r U Q K j| :=
          Finset.abs_sum_le_sum_abs _ _
    linarith

end NBMellinTools.NB12
