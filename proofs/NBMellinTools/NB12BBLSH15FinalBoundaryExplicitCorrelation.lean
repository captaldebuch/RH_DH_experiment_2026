/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FinalBoundaryCrossModulus

/-!
# NB12zx: the literal distinct-modulus correlation

This file removes the last subtraction notation from the endpoint frontier.
The cross-modulus sector is proved equal to the literal ordered correlation

`sum q in S, sum q' in S.erase q, R q * R q'`,

where `R q` is the complete signed, correction-coupled modulus row.  The final
dispersion gate is then restated exactly in this form.  This is the expression
that a dispersion, shifted-convolution, or spectral theorem must estimate.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate
open Complex

namespace NBMellinTools.NB12

/-! ## A reusable finite off-diagonal identity -/

theorem sq_sum_sub_sum_sq_eq_sum_erase
    {ι : Type} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, f i) ^ 2 - ∑ i ∈ s, (f i) ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s.erase i, f i * f j := by
  calc
    (∑ i ∈ s, f i) ^ 2 - ∑ i ∈ s, (f i) ^ 2 =
        ∑ i ∈ s, (f i * (∑ j ∈ s, f j) - (f i) ^ 2) := by
      rw [pow_two, Finset.sum_mul, Finset.sum_sub_distrib]
    _ = ∑ i ∈ s, f i * (∑ j ∈ s.erase i, f j) := by
      apply Finset.sum_congr rfl
      intro i hi
      have herase := Finset.sum_erase_add s f hi
      rw [← herase]
      ring
    _ = ∑ i ∈ s, ∑ j ∈ s.erase i, f i * f j := by
      simp only [Finset.mul_sum]

/-! ## The exact H15 modulus-row kernel -/

/-- The complete signed endpoint row at fixed modulus, after summing all
active square-divisor indices. -/
noncomputable def h15NormalizedBoundaryFixedFrequencyModulusRow
    (N g r U q : ℕ) : ℝ :=
  ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
    h15NormalizedBoundaryFourierRowValue N g r U
      (h15SquareDivisorProgressionModulus g d) q d

theorem h15NormalizedBoundaryFourierAggregate_eq_sum_modulusRows
    (N g r U Q : ℕ) :
    h15NormalizedBoundaryFourierAggregate N g r U Q =
      ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        h15NormalizedBoundaryFixedFrequencyModulusRow N g r U q := by
  rfl

theorem h15NormalizedBoundaryFixedFrequencyModulusBlockDiagonal_eq_sum_sq_rows
    (N g r U Q : ℕ) :
    h15NormalizedBoundaryFixedFrequencyModulusBlockDiagonal N g r U Q =
      ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        (h15NormalizedBoundaryFixedFrequencyModulusRow N g r U q) ^ 2 := by
  rfl

/-- Literal ordered correlation over distinct supported moduli. -/
noncomputable def h15NormalizedBoundaryExplicitCrossModulusCorrelation
    (N g r U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    ∑ q' ∈ (h15BettinChandeeSupportedNatBlock N g Q).erase q,
      h15NormalizedBoundaryFixedFrequencyModulusRow N g r U q *
        h15NormalizedBoundaryFixedFrequencyModulusRow N g r U q'

/-- The subtraction-defined cross sector is exactly the literal ordered
`q != q'` correlation. -/
theorem h15NormalizedBoundaryFixedFrequencyCrossModulusOffDiagonal_eq_explicit
    (N g r U Q : ℕ) :
    h15NormalizedBoundaryFixedFrequencyCrossModulusOffDiagonal N g r U Q =
      h15NormalizedBoundaryExplicitCrossModulusCorrelation N g r U Q := by
  unfold h15NormalizedBoundaryFixedFrequencyCrossModulusOffDiagonal
    h15NormalizedBoundaryFourierAggregate
    h15NormalizedBoundaryFixedFrequencyModulusBlockDiagonal
    h15NormalizedBoundaryExplicitCrossModulusCorrelation
    h15NormalizedBoundaryFixedFrequencyModulusRow
  exact sq_sum_sub_sum_sq_eq_sum_erase
    (h15BettinChandeeSupportedNatBlock N g Q)
    (fun q => ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
      h15NormalizedBoundaryFourierRowValue N g r U
        (h15SquareDivisorProgressionModulus g d) q d)

/-! ## Literal statement of the remaining analytic gate -/

def H15CorrectionCoupledExplicitCrossModulusCompensation
    (N g r U Q : ℕ) (Δ : ℝ) : Prop :=
  0 ≤ Δ ∧
    h15NormalizedBoundaryExplicitCrossModulusCorrelation N g r U Q ≤
      Δ * h15NormalizedBoundaryCrossModulusFrequencyEnergy N g U Q -
        h15NormalizedBoundaryFixedFrequencyModulusBlockDiagonal N g r U Q

theorem h15CorrectionCoupledCrossModulusFrequencyDispersion_iff_explicitCorrelation
    (N g r U Q : ℕ) (Δ : ℝ) :
    H15CorrectionCoupledCrossModulusFrequencyDispersion N g r U Q Δ ↔
      H15CorrectionCoupledExplicitCrossModulusCompensation
        N g r U Q Δ := by
  rw [h15CorrectionCoupledCrossModulusFrequencyDispersion_iff_crossCompensation]
  simp only [H15CorrectionCoupledCrossModulusOffDiagonalCompensation,
    H15CorrectionCoupledExplicitCrossModulusCompensation,
    h15NormalizedBoundaryFixedFrequencyCrossModulusOffDiagonal_eq_explicit]

/-- At the ideal coefficient `Delta = 0`, the literal distinct-modulus
correlation must cancel the complete nonnegative modulus-row square mass. -/
theorem h15CorrectionCoupledZeroDispersion_iff_explicitCorrelationCancellation
    (N g r U Q : ℕ) :
    H15CorrectionCoupledCrossModulusFrequencyDispersion N g r U Q 0 ↔
      h15NormalizedBoundaryExplicitCrossModulusCorrelation N g r U Q ≤
        -h15NormalizedBoundaryFixedFrequencyModulusBlockDiagonal N g r U Q := by
  rw [h15CorrectionCoupledCrossModulusFrequencyDispersion_iff_explicitCorrelation]
  simp [H15CorrectionCoupledExplicitCrossModulusCompensation]

end NBMellinTools.NB12
