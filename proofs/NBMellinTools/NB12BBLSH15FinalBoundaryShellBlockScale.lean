/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FinalBoundaryShellBlockIntervals

/-!
# NB12zzl: direct correction-coupled interval-block scale

The energy-normalized dispersion coefficient is not needed at the endpoint.
The complete squared Fourier boundary is exactly the collision defect plus the
signed separated ledger.  Therefore a direct nonnegative scale `S` bounding
the absolute interval-block budget together with the collision defect yields
the Fourier bound `sqrt S`.
-/

open Filter
open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate
open Complex

namespace NBMellinTools.NB12

/-- Exact conservation law behind the correction-coupled shell programme. -/
theorem sq_abs_h15NormalizedBoundaryFourierAggregate_eq_collisionDefect_add_separated
    {N g r U Q : ℕ} (hQ : 0 < Q) :
    |h15NormalizedBoundaryFourierAggregate N g r U Q| ^ 2 =
      h15NormalizedBoundaryPhaseCollisionDefect N g r U Q +
        h15NormalizedBoundaryPhaseSeparatedLedger N g r U Q := by
  rw [sq_abs_h15NormalizedBoundaryFourierAggregate_eq_modulusBlockDiagonal_add_cross,
    h15NormalizedBoundaryFixedFrequencyCrossModulusOffDiagonal_eq_explicit,
    h15NormalizedBoundaryExplicitCrossModulusCorrelation_eq_collision_add_separated hQ]
  unfold h15NormalizedBoundaryPhaseCollisionDefect
  ring

theorem sum_signedIntervalBlocks_le_absoluteIntervalBlockBudget
    (N g r U Q K : ℕ) :
    (∑ j : Fin (h15BoundarySpacingBlockCount Q K),
        h15NormalizedBoundarySignedIntervalBlockLedger N g r U Q K j) ≤
      h15NormalizedBoundaryAbsoluteSignedIntervalBlockBudget N g r U Q K := by
  unfold h15NormalizedBoundaryAbsoluteSignedIntervalBlockBudget
  calc
    (∑ j : Fin (h15BoundarySpacingBlockCount Q K),
        h15NormalizedBoundarySignedIntervalBlockLedger N g r U Q K j) ≤
        |∑ j : Fin (h15BoundarySpacingBlockCount Q K),
          h15NormalizedBoundarySignedIntervalBlockLedger N g r U Q K j| :=
      le_abs_self _
    _ ≤ ∑ j : Fin (h15BoundarySpacingBlockCount Q K),
        |h15NormalizedBoundarySignedIntervalBlockLedger N g r U Q K j| :=
      Finset.abs_sum_le_sum_abs _ _

/-- Direct, non-energy-normalized sufficient estimate. -/
def H15CorrectionCoupledIntervalBlockScaleEstimate
    (N g r U Q K : ℕ) (S : ℝ) : Prop :=
  0 ≤ S ∧
    h15NormalizedBoundaryAbsoluteSignedIntervalBlockBudget N g r U Q K +
        h15NormalizedBoundaryPhaseCollisionDefect N g r U Q ≤ S

theorem sq_abs_h15NormalizedBoundaryFourierAggregate_le_of_intervalBlockScale
    {N g r U Q K : ℕ} (hQ : 0 < Q) {S : ℝ}
    (H : H15CorrectionCoupledIntervalBlockScaleEstimate N g r U Q K S) :
    |h15NormalizedBoundaryFourierAggregate N g r U Q| ^ 2 ≤ S := by
  have hblocks :=
    sum_signedIntervalBlocks_le_absoluteIntervalBlockBudget N g r U Q K
  calc
    |h15NormalizedBoundaryFourierAggregate N g r U Q| ^ 2 =
        h15NormalizedBoundaryPhaseCollisionDefect N g r U Q +
          h15NormalizedBoundaryPhaseSeparatedLedger N g r U Q :=
      sq_abs_h15NormalizedBoundaryFourierAggregate_eq_collisionDefect_add_separated hQ
    _ = h15NormalizedBoundaryPhaseCollisionDefect N g r U Q +
        ∑ j : Fin (h15BoundarySpacingBlockCount Q K),
          h15NormalizedBoundarySignedIntervalBlockLedger N g r U Q K j := by
      rw [h15NormalizedBoundaryPhaseSeparatedLedger_eq_sum_signedIntervalBlocks hQ]
    _ ≤ h15NormalizedBoundaryPhaseCollisionDefect N g r U Q +
        h15NormalizedBoundaryAbsoluteSignedIntervalBlockBudget N g r U Q K :=
      by
        simpa only [add_comm] using
          add_le_add_right hblocks
            (h15NormalizedBoundaryPhaseCollisionDefect N g r U Q)
    _ ≤ S := by linarith [H.2]

theorem h15CorrectionCoupledFinalBoundaryFourierEstimate_of_intervalBlockScale
    {N g r U Q K : ℕ} (hQ : 0 < Q) {S : ℝ}
    (H : H15CorrectionCoupledIntervalBlockScaleEstimate N g r U Q K S) :
    H15CorrectionCoupledFinalBoundaryFourierEstimate N g r U Q
      (Real.sqrt S) := by
  constructor
  · exact Real.sqrt_nonneg _
  · exact (Real.le_sqrt (abs_nonneg _) H.1).2
      (sq_abs_h15NormalizedBoundaryFourierAggregate_le_of_intervalBlockScale
        hQ H)

/-- Moving-cutoff version of the direct scale estimate.  This is the clean
analytic target: prove `scale N -> 0` while retaining the interval-block
budget and collision defect in one inequality. -/
structure H15CorrectionCoupledIntervalBlockScaleDecayData
    (g r U Q K : ℕ → ℕ) where
  scale : ℕ → ℝ
  q_pos : ∀ N, 0 < Q N
  estimate : ∀ N,
    H15CorrectionCoupledIntervalBlockScaleEstimate
      N (g N) (r N) (U N) (Q N) (K N) (scale N)
  scale_tendsto_zero : Tendsto scale atTop (nhds 0)

theorem H15CorrectionCoupledIntervalBlockScaleDecayData.fourierEstimate
    {g r U Q K : ℕ → ℕ}
    (H : H15CorrectionCoupledIntervalBlockScaleDecayData g r U Q K)
    (N : ℕ) :
    H15CorrectionCoupledFinalBoundaryFourierEstimate
      N (g N) (r N) (U N) (Q N) (Real.sqrt (H.scale N)) := by
  exact h15CorrectionCoupledFinalBoundaryFourierEstimate_of_intervalBlockScale
    (H.q_pos N) (H.estimate N)

theorem H15CorrectionCoupledIntervalBlockScaleDecayData.sqrtScale_tendsto_zero
    {g r U Q K : ℕ → ℕ}
    (H : H15CorrectionCoupledIntervalBlockScaleDecayData g r U Q K) :
    Tendsto (fun N => Real.sqrt (H.scale N)) atTop (nhds 0) := by
  simpa only [Real.sqrt_zero] using H.scale_tendsto_zero.sqrt

end NBMellinTools.NB12
