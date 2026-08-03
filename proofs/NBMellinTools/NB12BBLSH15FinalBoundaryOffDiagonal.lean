/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FinalBoundaryDispersionLedger

/-!
# NB12zv: exact diagonal/off-diagonal final-boundary ledger

This file expands the square of the complete correction-coupled
fixed-frequency endpoint aggregate before any cross-row triangle inequality.
The diagonal is the positive sum of individual `(q,d)` row squares.  The
off-diagonal is the complete ordered cross-row product sector after that
diagonal has been removed.

The retained endpoint correction is already internal to every row.  It does
not occur as an additional term outside the square that could automatically
subtract the positive diagonal.  Consequently a dispersion coefficient
`Delta` is exactly equivalent to a negative off-diagonal compensation bound

`offDiagonal <= Delta * frequencyEnergy - diagonal`.

This is a finite algebraic stop test.  It does not assert the remaining signed
off-diagonal estimate.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate
open Complex

namespace NBMellinTools.NB12

/-! ## Exact ordered-pair expansion -/

/-- Positive fixed-frequency diagonal of the active `(q,d)` row family. -/
noncomputable def h15NormalizedBoundaryFixedFrequencyDiagonal
    (N g r U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
      (h15NormalizedBoundaryFourierRowValue N g r U
        (h15SquareDivisorProgressionModulus g d) q d) ^ 2

/-- Complete ordered product of two active `(q,d)` rows, with no absolute
values inserted. -/
noncomputable def h15NormalizedBoundaryFixedFrequencyFullPair
    (N g r U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
      ∑ q' ∈ h15BettinChandeeSupportedNatBlock N g Q,
        ∑ d' ∈ h15DyadicActivePeriodSquareDivisorIndices g U q',
          h15NormalizedBoundaryFourierRowValue N g r U
              (h15SquareDivisorProgressionModulus g d') q' d' *
            h15NormalizedBoundaryFourierRowValue N g r U
              (h15SquareDivisorProgressionModulus g d) q d

/-- Exact ordered off-diagonal sector: the full pair sum with the row-square
diagonal removed. -/
noncomputable def h15NormalizedBoundaryFixedFrequencyOffDiagonal
    (N g r U Q : ℕ) : ℝ :=
  h15NormalizedBoundaryFixedFrequencyFullPair N g r U Q -
    h15NormalizedBoundaryFixedFrequencyDiagonal N g r U Q

theorem h15NormalizedBoundaryFixedFrequencyDiagonal_nonneg
    (N g r U Q : ℕ) :
    0 ≤ h15NormalizedBoundaryFixedFrequencyDiagonal N g r U Q := by
  unfold h15NormalizedBoundaryFixedFrequencyDiagonal
  exact Finset.sum_nonneg (fun _q _hq =>
    Finset.sum_nonneg (fun _d _hd => sq_nonneg _))

/-- The full ordered pair sum is exactly the square of the signed aggregate. -/
theorem h15NormalizedBoundaryFixedFrequencyFullPair_eq_sq
    (N g r U Q : ℕ) :
    h15NormalizedBoundaryFixedFrequencyFullPair N g r U Q =
      (h15NormalizedBoundaryFourierAggregate N g r U Q) ^ 2 := by
  unfold h15NormalizedBoundaryFixedFrequencyFullPair
    h15NormalizedBoundaryFourierAggregate
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]

/-- Exact signed diagonal/off-diagonal expansion. -/
theorem sq_h15NormalizedBoundaryFourierAggregate_eq_diagonal_add_offDiagonal
    (N g r U Q : ℕ) :
    (h15NormalizedBoundaryFourierAggregate N g r U Q) ^ 2 =
      h15NormalizedBoundaryFixedFrequencyDiagonal N g r U Q +
        h15NormalizedBoundaryFixedFrequencyOffDiagonal N g r U Q := by
  rw [h15NormalizedBoundaryFixedFrequencyOffDiagonal,
    h15NormalizedBoundaryFixedFrequencyFullPair_eq_sq]
  ring

theorem sq_abs_h15NormalizedBoundaryFourierAggregate_eq_diagonal_add_offDiagonal
    (N g r U Q : ℕ) :
    |h15NormalizedBoundaryFourierAggregate N g r U Q| ^ 2 =
      h15NormalizedBoundaryFixedFrequencyDiagonal N g r U Q +
        h15NormalizedBoundaryFixedFrequencyOffDiagonal N g r U Q := by
  rw [sq_abs]
  exact sq_h15NormalizedBoundaryFourierAggregate_eq_diagonal_add_offDiagonal
    N g r U Q

/-! ## Location of the retained correction -/

/-- For positive supported moduli, the diagonal is literally the sum of
squares of the complete correction-coupled point rows.  Thus the correction
has not been dropped, but it is internal to the rows rather than an external
additive diagonal subtraction. -/
theorem h15NormalizedBoundaryFixedFrequencyDiagonal_eq_pointRows
    {N g r U Q : ℕ} (hQ : 0 < Q) :
    h15NormalizedBoundaryFixedFrequencyDiagonal N g r U Q =
      ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
          (h15NormalizedProgressionCoupledBoundaryPointRow N g r U
            (h15SquareDivisorProgressionModulus g d) q d) ^ 2 := by
  unfold h15NormalizedBoundaryFixedFrequencyDiagonal
  apply Finset.sum_congr rfl
  intro q hqMem
  have hqBounds := mem_h15BettinChandeeSupportedNatBlock.mp hqMem
  have hqPos : 0 < q := hQ.trans_le hqBounds.1
  apply Finset.sum_congr rfl
  intro d _hd
  rw [h15NormalizedBoundaryFourierRowValue_eq_pointRow
    N g r U (h15SquareDivisorProgressionModulus g d) q d hqPos]

/-- The positive fixed-frequency diagonal is controlled by the complete
frequency energy, row by row. -/
theorem h15NormalizedBoundaryFixedFrequencyDiagonal_le_frequencyEnergy
    {N g r U Q : ℕ} (hQ : 0 < Q) :
    h15NormalizedBoundaryFixedFrequencyDiagonal N g r U Q ≤
      h15NormalizedBoundaryCrossModulusFrequencyEnergy N g U Q := by
  unfold h15NormalizedBoundaryFixedFrequencyDiagonal
    h15NormalizedBoundaryCrossModulusFrequencyEnergy
  apply Finset.sum_le_sum
  intro q hqMem
  have hqBounds := mem_h15BettinChandeeSupportedNatBlock.mp hqMem
  have hqPos : 0 < q := hQ.trans_le hqBounds.1
  apply Finset.sum_le_sum
  intro d _hd
  exact sq_h15NormalizedBoundaryFourierRowValue_le_meanSquareValue
    N g r U (h15SquareDivisorProgressionModulus g d) q d hqPos

/-! ## Exact signed compensation formulation -/

/-- The off-diagonal form must compensate the positive diagonal up to the
allowed frequency-energy budget. -/
def H15CorrectionCoupledOffDiagonalCompensation
    (N g r U Q : ℕ) (Δ : ℝ) : Prop :=
  0 ≤ Δ ∧
    h15NormalizedBoundaryFixedFrequencyOffDiagonal N g r U Q ≤
      Δ * h15NormalizedBoundaryCrossModulusFrequencyEnergy N g U Q -
        h15NormalizedBoundaryFixedFrequencyDiagonal N g r U Q

/-- Dispersion is exactly negative signed off-diagonal compensation; this is
not an application of a triangle inequality. -/
theorem h15CorrectionCoupledCrossModulusFrequencyDispersion_iff_offDiagonal
    (N g r U Q : ℕ) (Δ : ℝ) :
    H15CorrectionCoupledCrossModulusFrequencyDispersion N g r U Q Δ ↔
      H15CorrectionCoupledOffDiagonalCompensation N g r U Q Δ := by
  constructor
  · intro hdisp
    refine ⟨hdisp.1, ?_⟩
    have hsq :=
      sq_abs_h15NormalizedBoundaryFourierAggregate_eq_diagonal_add_offDiagonal
        N g r U Q
    linarith [hdisp.2]
  · intro hcomp
    refine ⟨hcomp.1, ?_⟩
    have hsq :=
      sq_abs_h15NormalizedBoundaryFourierAggregate_eq_diagonal_add_offDiagonal
        N g r U Q
    linarith [hcomp.2]

/-- At the ideal coefficient `Delta = 0`, closure requires the off-diagonal
sector to cancel the entire positive diagonal. -/
theorem h15CorrectionCoupledZeroDispersion_iff_fullDiagonalCancellation
    (N g r U Q : ℕ) :
    H15CorrectionCoupledCrossModulusFrequencyDispersion N g r U Q 0 ↔
      h15NormalizedBoundaryFixedFrequencyOffDiagonal N g r U Q ≤
        -h15NormalizedBoundaryFixedFrequencyDiagonal N g r U Q := by
  rw [h15CorrectionCoupledCrossModulusFrequencyDispersion_iff_offDiagonal]
  simp [H15CorrectionCoupledOffDiagonalCompensation]

end NBMellinTools.NB12
