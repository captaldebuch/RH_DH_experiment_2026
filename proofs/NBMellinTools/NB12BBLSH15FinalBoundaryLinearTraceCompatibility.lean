/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FinalBoundaryLinearTraceGate
import NBMellinTools.NB12BBLSH15Rectangle

/-!
# NB12zzw: compatibility of the linear trace gate with the active H15 residual

This file performs two separate checks.

First, it composes the minimal correction-coupled linear trace estimate with
the exact two-Abel decomposition.  Thus the trace target controls the genuine
row-to-pointwise residual, rather than an auxiliary completed square.

Second, it records a cutoff mismatch with the full Estermann contour family.
The raw contour aggregate contains the complete Laurent row family and has a
nonzero cubic Laurent mode already at `n = 2`.  The final-boundary object has
an additional dyadic outer-modulus cutoff and is identically zero when that
block is outside the H15 support.  Therefore the raw contour integrand cannot
be identified directly with the final-boundary trace expression; a genuine
boundary-projection theorem is still required.
-/

open Filter
open scoped BigOperators Topology ArithmeticFunction.Moebius

namespace NBMellinTools.NB12

/-! ## The active trace-to-residual bridge -/

/-- A correction-coupled linear trace estimate feeds directly into the exact
two-Abel bound for the active H15 row-to-pointwise residual. -/
theorem abs_h15NormalizedProgressionRowToPointwiseResidual_le_linearTraceGate
    {N g r U Q K : ℕ} {P₁ P₂ S : ℝ}
    (hN : 2 ≤ N) (hg : 1 ≤ g) (hU : 0 < U) (hQ : 0 < Q)
    (hprefix₁ : H15NormalizedProgressionAbelPrefixBound N g r U Q P₁)
    (hprefix₂ : H15NormalizedRowSuperperiodAbelPrefixBound N g r U Q P₂)
    (htrace : H15CompletedLinearTraceEstimate N g r U Q K S) :
    |h15NormalizedProgressionRowToPointwiseResidual N g r U Q| ≤
      2 * (g.divisors.card : ℝ) * P₁ +
        4 * (g.divisors.card : ℝ) * P₂ + Real.sqrt S := by
  exact abs_h15NormalizedProgressionRowToPointwiseResidual_le_fourierBoundaryGate
    hN hg hU hQ hprefix₁ hprefix₂
      (h15CorrectionCoupledFinalBoundaryFourierEstimate_of_linearTraceEstimate
        hQ htrace)

/-! ## Why the raw contour family is not yet the final-boundary trace -/

/-- If the left endpoint of the dyadic modulus block is already beyond the
H15 support, the supported block is empty. -/
theorem h15BettinChandeeSupportedNatBlock_eq_empty_of_lt
    {N g Q : ℕ} (h : N < g * Q) :
    h15BettinChandeeSupportedNatBlock N g Q = ∅ := by
  ext q
  constructor
  · intro hq
    have hqBounds := mem_h15BettinChandeeSupportedNatBlock.mp hq
    have hmul : g * Q ≤ g * q := Nat.mul_le_mul_left g hqBounds.1
    simp only [Finset.notMem_empty]
    omega
  · simp

/-- Consequently the active final-boundary Fourier aggregate vanishes for an
unsupported outer-modulus block. -/
theorem h15NormalizedBoundaryFourierAggregate_eq_zero_of_lt
    {N g r U Q : ℕ} (h : N < g * Q) :
    h15NormalizedBoundaryFourierAggregate N g r U Q = 0 := by
  unfold h15NormalizedBoundaryFourierAggregate
  rw [h15BettinChandeeSupportedNatBlock_eq_empty_of_lt h]
  simp

/-- The completed linear trace expression has the same support property,
because it is exactly the square of the final-boundary Fourier aggregate. -/
theorem h15CompletedIntervalLinearTraceExpression_eq_zero_of_lt
    {N g r U Q K : ℕ} (hQ : 0 < Q) (h : N < g * Q) :
    h15CompletedIntervalLinearTraceExpression N g r U Q K = 0 := by
  rw [← sq_abs_h15NormalizedBoundaryFourierAggregate_eq_linearTraceExpression
    hQ, h15NormalizedBoundaryFourierAggregate_eq_zero_of_lt h]
  norm_num

/-- Concrete compatibility stop test.  At log-taper index `n = 2` the raw
H15 contour family has a nonzero cubic Laurent coefficient, whereas an
unsupported final-boundary dyadic trace is zero.  Hence a direct identification
of the two objects (without residue extraction and boundary projection) is
mathematically impossible. -/
theorem h15RawContour_finalBoundary_cutoff_mismatch
    (r U K : ℕ) :
    h15CompletedIntervalLinearTraceExpression 4 1 r U 5 K = 0 ∧
      h15GlobalThirdOrderCoefficient 2 ≠ 0 := by
  constructor
  · exact h15CompletedIntervalLinearTraceExpression_eq_zero_of_lt
      (by norm_num) (by norm_num)
  · exact h15GlobalThirdOrderCoefficient_two_ne_zero

end NBMellinTools.NB12
