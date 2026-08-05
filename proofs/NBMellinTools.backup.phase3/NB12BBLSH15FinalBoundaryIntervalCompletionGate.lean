/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FinalBoundaryIntervalCompletionAggregate

/-!
# NB12zzq: the correction-preserving completed-mode gate

Finite inverse-coordinate completion leaves two analytically distinct pieces:

* the original collision defect together with every Ramanujan zero mode;
* the nonzero inverse-frequency Kloosterman sector.

This file packages the exact sum of those pieces and gives the minimal direct
scale estimate needed for final-boundary decay.  It deliberately does not
bound them separately before their signs have interacted.
-/

open Filter
open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate

namespace NBMellinTools.NB12

/-- The complete correction ledger after interval-row completion.  It includes
both the pre-existing collision defect and the newly exposed Ramanujan modes. -/
noncomputable def h15CompletedIntervalCorrectionLedger
    (N g r U Q K : ℕ) : ℝ :=
  h15NormalizedBoundaryPhaseCollisionDefect N g r U Q +
    ∑ j : Fin (h15BoundarySpacingBlockCount Q K),
      h15CompletedIntervalBlockZeroLedger N g r U Q K j

/-- The complete nonzero inverse-frequency sector. -/
noncomputable def h15CompletedIntervalKloostermanDispersionLedger
    (N g r U Q K : ℕ) : ℝ :=
  ∑ j : Fin (h15BoundarySpacingBlockCount Q K),
    h15CompletedIntervalBlockNonzeroLedger N g r U Q K j

/-- Exact post-completion conservation law. -/
theorem sq_abs_h15NormalizedBoundaryFourierAggregate_eq_completedCorrection_add_dispersion
    {N g r U Q K : ℕ} (hQ : 0 < Q) :
    |h15NormalizedBoundaryFourierAggregate N g r U Q| ^ 2 =
      h15CompletedIntervalCorrectionLedger N g r U Q K +
        h15CompletedIntervalKloostermanDispersionLedger N g r U Q K := by
  rw [sq_abs_h15NormalizedBoundaryFourierAggregate_eq_completedIntervalModes hQ]
  all_goals
    unfold h15CompletedIntervalCorrectionLedger
      h15CompletedIntervalKloostermanDispersionLedger
    ring

/-- A direct scale bound on the two completed signed ledgers.  Absolute values
are introduced only after the collision, correction, and all interval rows
have been assembled. -/
def H15CompletedIntervalModeScaleEstimate
    (N g r U Q K : ℕ) (S : ℝ) : Prop :=
  0 ≤ S ∧
    |h15CompletedIntervalCorrectionLedger N g r U Q K| +
        |h15CompletedIntervalKloostermanDispersionLedger N g r U Q K| ≤ S

theorem sq_abs_h15NormalizedBoundaryFourierAggregate_le_of_completedModeScale
    {N g r U Q K : ℕ} (hQ : 0 < Q) {S : ℝ}
    (H : H15CompletedIntervalModeScaleEstimate N g r U Q K S) :
    |h15NormalizedBoundaryFourierAggregate N g r U Q| ^ 2 ≤ S := by
  rw [sq_abs_h15NormalizedBoundaryFourierAggregate_eq_completedCorrection_add_dispersion
    hQ]
  calc
    h15CompletedIntervalCorrectionLedger N g r U Q K +
        h15CompletedIntervalKloostermanDispersionLedger N g r U Q K ≤
      |h15CompletedIntervalCorrectionLedger N g r U Q K| +
        |h15CompletedIntervalKloostermanDispersionLedger N g r U Q K| :=
      add_le_add (le_abs_self _) (le_abs_self _)
    _ ≤ S := H.2

theorem h15CorrectionCoupledFinalBoundaryFourierEstimate_of_completedModeScale
    {N g r U Q K : ℕ} (hQ : 0 < Q) {S : ℝ}
    (H : H15CompletedIntervalModeScaleEstimate N g r U Q K S) :
    H15CorrectionCoupledFinalBoundaryFourierEstimate N g r U Q
      (Real.sqrt S) := by
  constructor
  · exact Real.sqrt_nonneg _
  · exact (Real.le_sqrt (abs_nonneg _) H.1).2
      (sq_abs_h15NormalizedBoundaryFourierAggregate_le_of_completedModeScale
        hQ H)

/-- Moving-parameter form of the final completed-mode analytic target. -/
structure H15CompletedIntervalModeScaleDecayData
    (g r U Q K : ℕ → ℕ) where
  scale : ℕ → ℝ
  q_pos : ∀ N, 0 < Q N
  estimate : ∀ N,
    H15CompletedIntervalModeScaleEstimate
      N (g N) (r N) (U N) (Q N) (K N) (scale N)
  scale_tendsto_zero : Tendsto scale atTop (nhds 0)

theorem H15CompletedIntervalModeScaleDecayData.fourierEstimate
    {g r U Q K : ℕ → ℕ}
    (H : H15CompletedIntervalModeScaleDecayData g r U Q K)
    (N : ℕ) :
    H15CorrectionCoupledFinalBoundaryFourierEstimate
      N (g N) (r N) (U N) (Q N) (Real.sqrt (H.scale N)) := by
  exact h15CorrectionCoupledFinalBoundaryFourierEstimate_of_completedModeScale
    (H.q_pos N) (H.estimate N)

theorem H15CompletedIntervalModeScaleDecayData.sqrtScale_tendsto_zero
    {g r U Q K : ℕ → ℕ}
    (H : H15CompletedIntervalModeScaleDecayData g r U Q K) :
    Tendsto (fun N => Real.sqrt (H.scale N)) atTop (nhds 0) := by
  simpa only [Real.sqrt_zero] using H.scale_tendsto_zero.sqrt

end NBMellinTools.NB12
