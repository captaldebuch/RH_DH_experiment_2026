/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FinalBoundarySectorAudit

/-!
# NB12zza: the correction-preserving terminal/smooth coupled gate

The sectorwise absolute audit grows on balanced blocks.  The remaining
analytic input is therefore stated on the single signed combination
`TT + 2 TS + SS`.  This file proves that this coupled inequality is exactly
equivalent to the prior cross-modulus dispersion gate and transfers it to the
existing endpoint estimate.

No inhabitant with a decaying coefficient is constructed here.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate
open Complex

namespace NBMellinTools.NB12

/-- Exact signed analytic target after the terminal/smooth expansion. -/
def H15CorrectionCoupledTerminalSmoothCompensation
    (N g r U Q : ℕ) (Δ : ℝ) : Prop :=
  0 ≤ Δ ∧
    h15NormalizedBoundaryTerminalTerminalCorrelation N g r U Q +
        2 * h15NormalizedBoundaryTerminalSmoothCorrelation N g r U Q +
        h15NormalizedBoundarySmoothSmoothCorrelation N g r U Q ≤
      Δ * h15NormalizedBoundaryCrossModulusFrequencyEnergy N g U Q -
        h15NormalizedBoundaryFixedFrequencyModulusBlockDiagonal N g r U Q

/-- The new coupled gate is neither stronger nor weaker than the exact
cross-modulus dispersion statement. -/
theorem h15CorrectionCoupledCrossModulusFrequencyDispersion_iff_terminalSmooth
    {N g r U Q : ℕ} (hQ : 0 < Q) (Δ : ℝ) :
    H15CorrectionCoupledCrossModulusFrequencyDispersion N g r U Q Δ ↔
      H15CorrectionCoupledTerminalSmoothCompensation N g r U Q Δ := by
  rw [h15CorrectionCoupledCrossModulusFrequencyDispersion_iff_explicitCorrelation]
  unfold H15CorrectionCoupledExplicitCrossModulusCompensation
    H15CorrectionCoupledTerminalSmoothCompensation
  rw [h15NormalizedBoundaryExplicitCrossModulusCorrelation_eq_threeSectors hQ]

/-- At coefficient zero, the coupled terminal/smooth expression must cancel
the entire nonnegative modulus-block diagonal. -/
theorem h15CorrectionCoupledZeroDispersion_iff_terminalSmoothCancellation
    {N g r U Q : ℕ} (hQ : 0 < Q) :
    H15CorrectionCoupledCrossModulusFrequencyDispersion N g r U Q 0 ↔
      h15NormalizedBoundaryTerminalTerminalCorrelation N g r U Q +
          2 * h15NormalizedBoundaryTerminalSmoothCorrelation N g r U Q +
          h15NormalizedBoundarySmoothSmoothCorrelation N g r U Q ≤
        -h15NormalizedBoundaryFixedFrequencyModulusBlockDiagonal N g r U Q := by
  rw [h15CorrectionCoupledCrossModulusFrequencyDispersion_iff_terminalSmooth
    hQ]
  simp [H15CorrectionCoupledTerminalSmoothCompensation]

/-- The coupled three-sector input feeds the exact Fourier endpoint gate. -/
theorem h15CorrectionCoupledFinalBoundaryFourierEstimate_of_terminalSmooth
    {N g r U Q : ℕ} {Δ : ℝ} (hQ : 0 < Q)
    (hcomp : H15CorrectionCoupledTerminalSmoothCompensation N g r U Q Δ) :
    H15CorrectionCoupledFinalBoundaryFourierEstimate N g r U Q
      (Real.sqrt
        (Δ * h15NormalizedBoundaryCrossModulusFrequencyEnergy N g U Q)) := by
  apply h15CorrectionCoupledFinalBoundaryFourierEstimate_of_crossModulusDispersion
  exact
    (h15CorrectionCoupledCrossModulusFrequencyDispersion_iff_terminalSmooth
      hQ Δ).2 hcomp

/-- On balanced blocks, a coupled coefficient `Delta` gives the same sharp
square-root endpoint estimate as the original dispersion formulation. -/
theorem abs_h15NormalizedBoundaryFourierAggregate_le_terminalSmooth_balanced
    {N g r U Q : ℕ} {Δ : ℝ}
    (hN : 2 ≤ N) (hg : 0 < g) (hU : 0 < U)
    (hQ : 0 < Q) (hQU : Q ≤ U)
    (hcomp : H15CorrectionCoupledTerminalSmoothCompensation
      N g r U Q Δ) :
    |h15NormalizedBoundaryFourierAggregate N g r U Q| ≤
      Real.sqrt (64 * (g.divisors.card : ℝ) * Δ) := by
  apply abs_h15NormalizedBoundaryFourierAggregate_le_sqrt_dispersion_balanced
    hN hg hU hQ hQU
  exact
    (h15CorrectionCoupledCrossModulusFrequencyDispersion_iff_terminalSmooth
      hQ Δ).2 hcomp

end NBMellinTools.NB12
