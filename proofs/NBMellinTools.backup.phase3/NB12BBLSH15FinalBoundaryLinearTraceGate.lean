/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FinalBoundaryCompletedCrossModulus

/-!
# NB12zzv: the minimal linear trace gate after H15 completion

The post-completion conservation law is linear in the completed correction
and in the signed nonzero Kloosterman aggregate.  Bounding those two terms
separately is unnecessary and can destroy the cancellation a trace formula is
supposed to reveal.

This file defines the canonical complex two-orientation aggregate, proves
that its real part is exactly the existing nonzero dispersion ledger, and
packages a bound only after it has been coupled to the correction.
-/

open Filter Complex
open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate

namespace NBMellinTools.NB12

/-- The canonical signed complex nonzero aggregate: difference orientation
minus sum orientation, with the product-to-sum factor `1/2`. -/
noncomputable def h15CompletedIntervalSignedKloostermanAggregate
    (N g r U Q K : ℕ) : ℂ :=
  ∑ j : Fin (h15BoundarySpacingBlockCount Q K),
    (((1 / 2 : ℝ) : ℂ) *
      (h15ComplexIntervalBlockNonzeroModeAggregate
          .difference N g r U Q K j -
        h15ComplexIntervalBlockNonzeroModeAggregate
          .sum N g r U Q K j))

/-- Its real part is exactly the previously assembled nonzero dispersion
ledger.  No absolute value or square is introduced. -/
theorem re_h15CompletedIntervalSignedKloostermanAggregate_eq_dispersion
    (N g r U Q K : ℕ) :
    (h15CompletedIntervalSignedKloostermanAggregate N g r U Q K).re =
      h15CompletedIntervalKloostermanDispersionLedger N g r U Q K := by
  unfold h15CompletedIntervalSignedKloostermanAggregate
    h15CompletedIntervalKloostermanDispersionLedger
    h15CompletedIntervalBlockNonzeroLedger
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_re, Complex.sub_im, zero_mul, sub_zero]
  ring

/-- The single canonical linear trace expression.  A Kuznetsov/Estermann
argument must estimate this coupled quantity, not its summands separately. -/
noncomputable def h15CompletedIntervalLinearTraceExpression
    (N g r U Q K : ℕ) : ℝ :=
  h15CompletedIntervalCorrectionLedger N g r U Q K +
    (h15CompletedIntervalSignedKloostermanAggregate N g r U Q K).re

/-- Exact minimal post-completion conservation law. -/
theorem sq_abs_h15NormalizedBoundaryFourierAggregate_eq_linearTraceExpression
    {N g r U Q K : ℕ} (hQ : 0 < Q) :
    |h15NormalizedBoundaryFourierAggregate N g r U Q| ^ 2 =
      h15CompletedIntervalLinearTraceExpression N g r U Q K := by
  rw [sq_abs_h15NormalizedBoundaryFourierAggregate_eq_completedCorrection_add_dispersion
    hQ]
  unfold h15CompletedIntervalLinearTraceExpression
  rw [re_h15CompletedIntervalSignedKloostermanAggregate_eq_dispersion]

/-- Weakest direct scale estimate: take the absolute value only after the
correction and the full signed Kloosterman aggregate have interacted. -/
def H15CompletedLinearTraceEstimate
    (N g r U Q K : ℕ) (S : ℝ) : Prop :=
  0 ≤ S ∧ |h15CompletedIntervalLinearTraceExpression N g r U Q K| ≤ S

theorem sq_abs_h15NormalizedBoundaryFourierAggregate_le_of_linearTraceEstimate
    {N g r U Q K : ℕ} (hQ : 0 < Q) {S : ℝ}
    (H : H15CompletedLinearTraceEstimate N g r U Q K S) :
    |h15NormalizedBoundaryFourierAggregate N g r U Q| ^ 2 ≤ S := by
  rw [sq_abs_h15NormalizedBoundaryFourierAggregate_eq_linearTraceExpression hQ]
  exact (le_abs_self _).trans H.2

theorem h15CorrectionCoupledFinalBoundaryFourierEstimate_of_linearTraceEstimate
    {N g r U Q K : ℕ} (hQ : 0 < Q) {S : ℝ}
    (H : H15CompletedLinearTraceEstimate N g r U Q K S) :
    H15CorrectionCoupledFinalBoundaryFourierEstimate N g r U Q
      (Real.sqrt S) := by
  constructor
  · exact Real.sqrt_nonneg _
  · exact (Real.le_sqrt (abs_nonneg _) H.1).2
      (sq_abs_h15NormalizedBoundaryFourierAggregate_le_of_linearTraceEstimate
        hQ H)

/-- The earlier separate-ledger scale implies the new linear trace scale, but
not conversely.  Thus the new interface preserves strictly more possible
cancellation. -/
theorem H15CompletedIntervalModeScaleEstimate.toLinearTraceEstimate
    {N g r U Q K : ℕ} {S : ℝ}
    (H : H15CompletedIntervalModeScaleEstimate N g r U Q K S) :
    H15CompletedLinearTraceEstimate N g r U Q K S := by
  refine ⟨H.1, ?_⟩
  unfold h15CompletedIntervalLinearTraceExpression
  rw [re_h15CompletedIntervalSignedKloostermanAggregate_eq_dispersion]
  exact (abs_add_le _ _).trans H.2

/-- Moving-parameter form of the minimal signed trace target. -/
structure H15CompletedLinearTraceDecayData
    (g r U Q K : ℕ → ℕ) where
  scale : ℕ → ℝ
  q_pos : ∀ N, 0 < Q N
  estimate : ∀ N,
    H15CompletedLinearTraceEstimate
      N (g N) (r N) (U N) (Q N) (K N) (scale N)
  scale_tendsto_zero : Tendsto scale atTop (nhds 0)

theorem H15CompletedLinearTraceDecayData.fourierEstimate
    {g r U Q K : ℕ → ℕ}
    (H : H15CompletedLinearTraceDecayData g r U Q K)
    (N : ℕ) :
    H15CorrectionCoupledFinalBoundaryFourierEstimate
      N (g N) (r N) (U N) (Q N) (Real.sqrt (H.scale N)) := by
  exact h15CorrectionCoupledFinalBoundaryFourierEstimate_of_linearTraceEstimate
    (H.q_pos N) (H.estimate N)

theorem H15CompletedLinearTraceDecayData.sqrtScale_tendsto_zero
    {g r U Q K : ℕ → ℕ}
    (H : H15CompletedLinearTraceDecayData g r U Q K) :
    Tendsto (fun N => Real.sqrt (H.scale N)) atTop (nhds 0) := by
  simpa only [Real.sqrt_zero] using H.scale_tendsto_zero.sqrt

end NBMellinTools.NB12
