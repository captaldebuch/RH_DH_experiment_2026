/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FinalBoundaryLinearTraceCompatibility

/-!
# NB12zzx: moving linear-trace decay and the active residual

The finite compatibility theorem is assembled here along moving H15
parameters.  The majorant contains exactly three terms:

* the first signed Abel-prefix cost;
* the second signed superperiod-prefix cost;
* the square root of the correction-coupled linear trace scale.

No contour hypothesis is hidden in this package.  In particular, an eventual
zero theorem for the raw Estermann aggregate is not accepted in place of the
localized linear trace estimate.
-/

open Filter
open scoped BigOperators Topology ArithmeticFunction.Moebius

namespace NBMellinTools.NB12

/-- Decay of the minimal trace scale already forces decay of the localized
final-boundary Fourier aggregate. -/
theorem H15CompletedLinearTraceDecayData.boundaryFourier_tendsto_zero
    {g r U Q K : ℕ → ℕ}
    (H : H15CompletedLinearTraceDecayData g r U Q K) :
    Tendsto
      (fun N => h15NormalizedBoundaryFourierAggregate
        N (g N) (r N) (U N) (Q N))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_
    H.sqrtScale_tendsto_zero
  exact Eventually.of_forall fun N => (H.fourierEstimate N).2

/-- Complete moving-parameter input for the active row-to-pointwise residual.
The `combined_tendsto_zero` field is deliberately stated for the literal
majorant produced by the two Abel transforms and the linear trace gate. -/
structure H15CompletedLinearTraceResidualDecayData
    (g r U Q K : ℕ → ℕ) where
  trace : H15CompletedLinearTraceDecayData g r U Q K
  firstPrefixScale : ℕ → ℝ
  secondPrefixScale : ℕ → ℝ
  cutoff_ge_two : ∀ᶠ N in atTop, 2 ≤ N
  gcdSlice_pos : ∀ N, 1 ≤ g N
  endpointCutoff_pos : ∀ N, 0 < U N
  firstPrefixBound : ∀ N,
    H15NormalizedProgressionAbelPrefixBound
      N (g N) (r N) (U N) (Q N) (firstPrefixScale N)
  secondPrefixBound : ∀ N,
    H15NormalizedRowSuperperiodAbelPrefixBound
      N (g N) (r N) (U N) (Q N) (secondPrefixScale N)
  combined_tendsto_zero :
    Tendsto
      (fun N =>
        2 * ((g N).divisors.card : ℝ) * firstPrefixScale N +
          4 * ((g N).divisors.card : ℝ) * secondPrefixScale N +
          Real.sqrt (trace.scale N))
      atTop (nhds 0)

/-- The moving correction-coupled trace package closes the active
row-to-pointwise residual, with no intermediate triangle inequality on the
completed correction and Kloosterman sectors. -/
theorem H15CompletedLinearTraceResidualDecayData.residual_tendsto_zero
    {g r U Q K : ℕ → ℕ}
    (H : H15CompletedLinearTraceResidualDecayData g r U Q K) :
    Tendsto
      (fun N => h15NormalizedProgressionRowToPointwiseResidual
        N (g N) (r N) (U N) (Q N))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_
    H.combined_tendsto_zero
  filter_upwards [H.cutoff_ge_two] with N hN
  exact abs_h15NormalizedProgressionRowToPointwiseResidual_le_linearTraceGate
    hN (H.gcdSlice_pos N) (H.endpointCutoff_pos N) (H.trace.q_pos N)
      (H.firstPrefixBound N) (H.secondPrefixBound N) (H.trace.estimate N)

end NBMellinTools.NB12
