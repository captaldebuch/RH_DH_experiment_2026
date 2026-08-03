/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FinalBoundaryIntervalCompletion

/-!
# NB12zzp: aggregate completion and the correction ledger

The literal inner-row completion is lifted through every outer H15 index.
This produces exact zero- and nonzero-frequency aggregates for each signed
interval block.  Combining the result with the previously proved collision
identity shows the precise correction bookkeeping:

`boundary² = collision defect + completed zero modes + completed nonzero modes`.

Thus the completion zero mode is not identified with the collision defect by
finite Fourier algebra.  They are distinct signed ledgers which must be kept
coupled in any subsequent estimate.
-/

open AddChar Complex ZMod
open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate

namespace NBMellinTools.NB12

/-! ## Total versions, including the vacuous modulus-zero case -/

noncomputable def h15ComplexIntervalEndpointRowTotal
    (orientation : H15IntervalCompletionOrientation)
    (N g r U L' q q' d' u K j : ℕ) : ℂ :=
  if hq' : q' = 0 then 0
  else
    letI : NeZero q' := ⟨hq'⟩
    h15ComplexIntervalEndpointRow orientation
      N g r U L' q q' d' u K j

noncomputable def h15ComplexIntervalEndpointZeroModeTotal
    (orientation : H15IntervalCompletionOrientation)
    (N g r U L' q q' d' u K j : ℕ) : ℂ :=
  if hq' : q' = 0 then 0
  else
    letI : NeZero q' := ⟨hq'⟩
    h15ComplexIntervalEndpointZeroMode orientation
      N g r U L' q q' d' u K j

noncomputable def h15ComplexIntervalEndpointNonzeroModeTotal
    (orientation : H15IntervalCompletionOrientation)
    (N g r U L' q q' d' u K j : ℕ) : ℂ :=
  if hq' : q' = 0 then 0
  else
    letI : NeZero q' := ⟨hq'⟩
    h15ComplexIntervalEndpointNonzeroMode orientation
      N g r U L' q q' d' u K j

theorem h15ComplexIntervalEndpointRowTotal_eq_zeroMode_add_nonzero
    (orientation : H15IntervalCompletionOrientation)
    (N g r U L' q q' d' u K j : ℕ) :
    h15ComplexIntervalEndpointRowTotal orientation
        N g r U L' q q' d' u K j =
      h15ComplexIntervalEndpointZeroModeTotal orientation
          N g r U L' q q' d' u K j +
        h15ComplexIntervalEndpointNonzeroModeTotal orientation
          N g r U L' q q' d' u K j := by
  by_cases hq' : q' = 0
  · simp [h15ComplexIntervalEndpointRowTotal,
      h15ComplexIntervalEndpointZeroModeTotal,
      h15ComplexIntervalEndpointNonzeroModeTotal, hq']
  · letI : NeZero q' := ⟨hq'⟩
    simp only [h15ComplexIntervalEndpointRowTotal,
      h15ComplexIntervalEndpointZeroModeTotal,
      h15ComplexIntervalEndpointNonzeroModeTotal, hq', dite_false]
    exact h15ComplexIntervalEndpointRow_eq_zeroMode_add_nonzero
      orientation N g r U L' q q' d' u K j

/-! ## The fixed outer endpoint factor -/

noncomputable def h15ComplexIntervalOuterEndpointFactor
    (N g r U L q d u : ℕ) : ℂ :=
  (h15NormalizedProgressionCoupledBoundaryPointWeight
      N g U L q d u : ℂ) *
    h15DoubledDirectAdditivePhase r u q

private theorem re_ofReal_mul_phase_mul_ofReal_mul_phase
    (a b : ℝ) (z w : ℂ) :
    (((a : ℂ) * z) * ((b : ℂ) * w)).re =
      (a * b) * (z * w).re := by
  simp only [mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
  ring

/-- Local real-part recovery for one fixed outer endpoint. -/
theorem re_h15ComplexIntervalOuterEndpointFactor_mul_rowTotal
    (orientation : H15IntervalCompletionOrientation)
    (N g r U L L' q q' d d' u K j : ℕ) (hq' : q' ≠ 0) :
    (h15ComplexIntervalOuterEndpointFactor N g r U L q d u *
        h15ComplexIntervalEndpointRowTotal orientation
          N g r U L' q q' d' u K j).re =
      ∑ v ∈ (h15NormalizedSuperperiodBoundarySupport U L' q').filter
          (fun v => h15IntervalCompletionPredicate
            orientation r u q v q' K j),
        (h15NormalizedProgressionCoupledBoundaryPointWeight
            N g U L q d u *
          h15NormalizedProgressionCoupledBoundaryPointWeight
            N g U L' q' d' v) *
          match orientation with
          | .difference => h15DifferenceEndpointPairPhase r u q v q'
          | .sum => h15SumEndpointPairPhase r u q v q' := by
  letI : NeZero q' := ⟨hq'⟩
  simp only [h15ComplexIntervalEndpointRowTotal, hq', dite_false]
  unfold h15ComplexIntervalOuterEndpointFactor
    h15ComplexIntervalEndpointRow
  rw [Finset.mul_sum, Complex.re_sum]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v hv
  have hvq' :=
    coprime_of_mem_h15NormalizedSuperperiodBoundarySupport hv
  by_cases hblock :
      h15IntervalCompletionPredicate orientation r u q v q' K j
  · simp only [hblock, if_true]
    cases orientation with
    | difference =>
        unfold h15DifferenceEndpointPairPhase
        exact re_ofReal_mul_phase_mul_ofReal_mul_phase _ _ _ _
    | sum =>
        unfold h15SumEndpointPairPhase
        exact re_ofReal_mul_phase_mul_ofReal_mul_phase _ _ _ _
  · simp [hblock]

/-! ## Completion lifted through the outer indices -/

noncomputable def h15ComplexIntervalBlockAggregate
    (orientation : H15IntervalCompletionOrientation)
    (N g r U Q K : ℕ)
    (j : Fin (h15BoundarySpacingBlockCount Q K)) : ℂ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    ∑ q' ∈ (h15BettinChandeeSupportedNatBlock N g Q).erase q,
      ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
        ∑ d' ∈ h15DyadicActivePeriodSquareDivisorIndices g U q',
          ∑ u ∈ h15NormalizedSuperperiodBoundarySupport U
              (h15SquareDivisorProgressionModulus g d) q,
            h15ComplexIntervalOuterEndpointFactor N g r U
                (h15SquareDivisorProgressionModulus g d) q d u *
              h15ComplexIntervalEndpointRowTotal orientation N g r U
                (h15SquareDivisorProgressionModulus g d') q q' d' u K j.val

noncomputable def h15ComplexIntervalBlockZeroModeAggregate
    (orientation : H15IntervalCompletionOrientation)
    (N g r U Q K : ℕ)
    (j : Fin (h15BoundarySpacingBlockCount Q K)) : ℂ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    ∑ q' ∈ (h15BettinChandeeSupportedNatBlock N g Q).erase q,
      ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
        ∑ d' ∈ h15DyadicActivePeriodSquareDivisorIndices g U q',
          ∑ u ∈ h15NormalizedSuperperiodBoundarySupport U
              (h15SquareDivisorProgressionModulus g d) q,
            h15ComplexIntervalOuterEndpointFactor N g r U
                (h15SquareDivisorProgressionModulus g d) q d u *
              h15ComplexIntervalEndpointZeroModeTotal orientation N g r U
                (h15SquareDivisorProgressionModulus g d') q q' d' u K j.val

noncomputable def h15ComplexIntervalBlockNonzeroModeAggregate
    (orientation : H15IntervalCompletionOrientation)
    (N g r U Q K : ℕ)
    (j : Fin (h15BoundarySpacingBlockCount Q K)) : ℂ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    ∑ q' ∈ (h15BettinChandeeSupportedNatBlock N g Q).erase q,
      ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
        ∑ d' ∈ h15DyadicActivePeriodSquareDivisorIndices g U q',
          ∑ u ∈ h15NormalizedSuperperiodBoundarySupport U
              (h15SquareDivisorProgressionModulus g d) q,
            h15ComplexIntervalOuterEndpointFactor N g r U
                (h15SquareDivisorProgressionModulus g d) q d u *
              h15ComplexIntervalEndpointNonzeroModeTotal orientation N g r U
                (h15SquareDivisorProgressionModulus g d') q q' d' u K j.val

theorem h15ComplexIntervalBlockAggregate_eq_zeroMode_add_nonzero
    (orientation : H15IntervalCompletionOrientation)
    (N g r U Q K : ℕ)
    (j : Fin (h15BoundarySpacingBlockCount Q K)) :
    h15ComplexIntervalBlockAggregate orientation N g r U Q K j =
      h15ComplexIntervalBlockZeroModeAggregate orientation N g r U Q K j +
        h15ComplexIntervalBlockNonzeroModeAggregate
          orientation N g r U Q K j := by
  classical
  unfold h15ComplexIntervalBlockAggregate
    h15ComplexIntervalBlockZeroModeAggregate
    h15ComplexIntervalBlockNonzeroModeAggregate
  simp_rw [h15ComplexIntervalEndpointRowTotal_eq_zeroMode_add_nonzero,
    mul_add, Finset.sum_add_distrib]

theorem re_h15ComplexDifferenceIntervalBlockAggregate
    {N g r U Q K : ℕ} (hQ : 0 < Q)
    (j : Fin (h15BoundarySpacingBlockCount Q K)) :
    (h15ComplexIntervalBlockAggregate .difference N g r U Q K j).re =
      h15NormalizedBoundaryDifferenceIntervalBlockLedger N g r U Q K j := by
  classical
  unfold h15ComplexIntervalBlockAggregate
    h15NormalizedBoundaryDifferenceIntervalBlockLedger
    h15NormalizedBoundaryEndpointPairFilteredPhaseAggregate
  simp_rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro q _hq
  apply Finset.sum_congr rfl
  intro q' hq'Erase
  have hq'Mem := Finset.mem_of_mem_erase hq'Erase
  have hq'Bounds := mem_h15BettinChandeeSupportedNatBlock.mp hq'Mem
  have hq'Ne : q' ≠ 0 := (hQ.trans_le hq'Bounds.1).ne'
  apply Finset.sum_congr rfl
  intro d _hd
  apply Finset.sum_congr rfl
  intro d' _hd'
  apply Finset.sum_congr rfl
  intro u _hu
  simpa only [h15IntervalCompletionPredicate] using
    (re_h15ComplexIntervalOuterEndpointFactor_mul_rowTotal
      .difference N g r U
      (h15SquareDivisorProgressionModulus g d)
      (h15SquareDivisorProgressionModulus g d') q q' d d' u K j.val hq'Ne)

theorem re_h15ComplexSumIntervalBlockAggregate
    {N g r U Q K : ℕ} (hQ : 0 < Q)
    (j : Fin (h15BoundarySpacingBlockCount Q K)) :
    (h15ComplexIntervalBlockAggregate .sum N g r U Q K j).re =
      h15NormalizedBoundarySumIntervalBlockLedger N g r U Q K j := by
  classical
  unfold h15ComplexIntervalBlockAggregate
    h15NormalizedBoundarySumIntervalBlockLedger
    h15NormalizedBoundaryEndpointPairFilteredPhaseAggregate
  simp_rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro q _hq
  apply Finset.sum_congr rfl
  intro q' hq'Erase
  have hq'Mem := Finset.mem_of_mem_erase hq'Erase
  have hq'Bounds := mem_h15BettinChandeeSupportedNatBlock.mp hq'Mem
  have hq'Ne : q' ≠ 0 := (hQ.trans_le hq'Bounds.1).ne'
  apply Finset.sum_congr rfl
  intro d _hd
  apply Finset.sum_congr rfl
  intro d' _hd'
  apply Finset.sum_congr rfl
  intro u _hu
  simpa only [h15IntervalCompletionPredicate] using
    (re_h15ComplexIntervalOuterEndpointFactor_mul_rowTotal
      .sum N g r U
      (h15SquareDivisorProgressionModulus g d)
      (h15SquareDivisorProgressionModulus g d') q q' d d' u K j.val hq'Ne)

/-! ## Exact correction-preserving aggregate ledger -/

noncomputable def h15CompletedIntervalBlockZeroLedger
    (N g r U Q K : ℕ)
    (j : Fin (h15BoundarySpacingBlockCount Q K)) : ℝ :=
  ((h15ComplexIntervalBlockZeroModeAggregate
      .difference N g r U Q K j).re -
    (h15ComplexIntervalBlockZeroModeAggregate
      .sum N g r U Q K j).re) / 2

noncomputable def h15CompletedIntervalBlockNonzeroLedger
    (N g r U Q K : ℕ)
    (j : Fin (h15BoundarySpacingBlockCount Q K)) : ℝ :=
  ((h15ComplexIntervalBlockNonzeroModeAggregate
      .difference N g r U Q K j).re -
    (h15ComplexIntervalBlockNonzeroModeAggregate
      .sum N g r U Q K j).re) / 2

theorem h15NormalizedBoundarySignedIntervalBlockLedger_eq_completedModes
    {N g r U Q K : ℕ} (hQ : 0 < Q)
    (j : Fin (h15BoundarySpacingBlockCount Q K)) :
    h15NormalizedBoundarySignedIntervalBlockLedger N g r U Q K j =
      h15CompletedIntervalBlockZeroLedger N g r U Q K j +
        h15CompletedIntervalBlockNonzeroLedger N g r U Q K j := by
  unfold h15NormalizedBoundarySignedIntervalBlockLedger
    h15CompletedIntervalBlockZeroLedger
    h15CompletedIntervalBlockNonzeroLedger
  rw [← re_h15ComplexDifferenceIntervalBlockAggregate hQ,
    ← re_h15ComplexSumIntervalBlockAggregate hQ,
    h15ComplexIntervalBlockAggregate_eq_zeroMode_add_nonzero,
    h15ComplexIntervalBlockAggregate_eq_zeroMode_add_nonzero]
  simp only [add_re]
  ring

/-- Final exact normalization after completion.  The collision defect and the
Ramanujan zero-mode aggregate are adjacent but distinct terms. -/
theorem sq_abs_h15NormalizedBoundaryFourierAggregate_eq_completedIntervalModes
    {N g r U Q K : ℕ} (hQ : 0 < Q) :
    |h15NormalizedBoundaryFourierAggregate N g r U Q| ^ 2 =
      h15NormalizedBoundaryPhaseCollisionDefect N g r U Q +
        ∑ j : Fin (h15BoundarySpacingBlockCount Q K),
          h15CompletedIntervalBlockZeroLedger N g r U Q K j +
        ∑ j : Fin (h15BoundarySpacingBlockCount Q K),
          h15CompletedIntervalBlockNonzeroLedger N g r U Q K j := by
  rw [sq_abs_h15NormalizedBoundaryFourierAggregate_eq_collisionDefect_add_separated hQ,
    h15NormalizedBoundaryPhaseSeparatedLedger_eq_sum_signedIntervalBlocks hQ]
  all_goals
    simp_rw [h15NormalizedBoundarySignedIntervalBlockLedger_eq_completedModes hQ,
      Finset.sum_add_distrib]
    ring

end NBMellinTools.NB12
