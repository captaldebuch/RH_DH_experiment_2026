/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FinalBoundaryOffDiagonal

/-!
# NB12zw: within-modulus versus cross-modulus compensation

Step 4v-o shows that the correction-coupled row-square diagonal remains
positive.  This file makes the next exact split.  First sum all active `d`
rows at each fixed modulus `q` and square that modulus row.  The resulting
modulus-block diagonal is again nonnegative.  Therefore interactions between
different `d` at the same modulus can reduce the individual-row diagonal only
to this nonnegative block diagonal.  Any further cancellation must come from
interactions between distinct moduli.

The final theorem rewrites the dispersion gate exactly as a negative
cross-modulus compensation estimate.  No estimate of that frontier term is
asserted here.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate
open Complex

namespace NBMellinTools.NB12

/-! ## The exact two-scale off-diagonal split -/

/-- Sum of squared complete `d`-aggregates at each fixed modulus. -/
noncomputable def h15NormalizedBoundaryFixedFrequencyModulusBlockDiagonal
    (N g r U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    (∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
      h15NormalizedBoundaryFourierRowValue N g r U
        (h15SquareDivisorProgressionModulus g d) q d) ^ 2

/-- Same-modulus, distinct-row sector, represented exactly as the difference
between the modulus-block diagonal and the individual-row diagonal. -/
noncomputable def h15NormalizedBoundaryFixedFrequencyWithinModulusOffDiagonal
    (N g r U Q : ℕ) : ℝ :=
  h15NormalizedBoundaryFixedFrequencyModulusBlockDiagonal N g r U Q -
    h15NormalizedBoundaryFixedFrequencyDiagonal N g r U Q

/-- Distinct-modulus sector, represented exactly as the full square minus the
nonnegative modulus-block diagonal. -/
noncomputable def h15NormalizedBoundaryFixedFrequencyCrossModulusOffDiagonal
    (N g r U Q : ℕ) : ℝ :=
  (h15NormalizedBoundaryFourierAggregate N g r U Q) ^ 2 -
    h15NormalizedBoundaryFixedFrequencyModulusBlockDiagonal N g r U Q

theorem h15NormalizedBoundaryFixedFrequencyModulusBlockDiagonal_nonneg
    (N g r U Q : ℕ) :
    0 ≤ h15NormalizedBoundaryFixedFrequencyModulusBlockDiagonal N g r U Q := by
  unfold h15NormalizedBoundaryFixedFrequencyModulusBlockDiagonal
  exact Finset.sum_nonneg (fun _q _hq => sq_nonneg _)

theorem diagonal_add_withinModulusOffDiagonal_eq_modulusBlockDiagonal
    (N g r U Q : ℕ) :
    h15NormalizedBoundaryFixedFrequencyDiagonal N g r U Q +
        h15NormalizedBoundaryFixedFrequencyWithinModulusOffDiagonal N g r U Q =
      h15NormalizedBoundaryFixedFrequencyModulusBlockDiagonal N g r U Q := by
  unfold h15NormalizedBoundaryFixedFrequencyWithinModulusOffDiagonal
  ring

/-- Same-modulus interactions alone can never push the individual-row
diagonal below zero. -/
theorem neg_diagonal_le_withinModulusOffDiagonal
    (N g r U Q : ℕ) :
    -h15NormalizedBoundaryFixedFrequencyDiagonal N g r U Q ≤
      h15NormalizedBoundaryFixedFrequencyWithinModulusOffDiagonal N g r U Q := by
  have hnonneg :=
    h15NormalizedBoundaryFixedFrequencyModulusBlockDiagonal_nonneg N g r U Q
  rw [← diagonal_add_withinModulusOffDiagonal_eq_modulusBlockDiagonal] at hnonneg
  linarith

/-- The complete fixed-frequency square is the nonnegative modulus-block
diagonal plus the genuinely cross-modulus sector. -/
theorem sq_h15NormalizedBoundaryFourierAggregate_eq_modulusBlockDiagonal_add_cross
    (N g r U Q : ℕ) :
    (h15NormalizedBoundaryFourierAggregate N g r U Q) ^ 2 =
      h15NormalizedBoundaryFixedFrequencyModulusBlockDiagonal N g r U Q +
        h15NormalizedBoundaryFixedFrequencyCrossModulusOffDiagonal N g r U Q := by
  unfold h15NormalizedBoundaryFixedFrequencyCrossModulusOffDiagonal
  ring

theorem sq_abs_h15NormalizedBoundaryFourierAggregate_eq_modulusBlockDiagonal_add_cross
    (N g r U Q : ℕ) :
    |h15NormalizedBoundaryFourierAggregate N g r U Q| ^ 2 =
      h15NormalizedBoundaryFixedFrequencyModulusBlockDiagonal N g r U Q +
        h15NormalizedBoundaryFixedFrequencyCrossModulusOffDiagonal N g r U Q := by
  rw [sq_abs]
  exact
    sq_h15NormalizedBoundaryFourierAggregate_eq_modulusBlockDiagonal_add_cross
      N g r U Q

/-- The ordered row off-diagonal is exactly the sum of its same-modulus and
distinct-modulus sectors. -/
theorem h15NormalizedBoundaryFixedFrequencyOffDiagonal_eq_within_add_cross
    (N g r U Q : ℕ) :
    h15NormalizedBoundaryFixedFrequencyOffDiagonal N g r U Q =
      h15NormalizedBoundaryFixedFrequencyWithinModulusOffDiagonal N g r U Q +
        h15NormalizedBoundaryFixedFrequencyCrossModulusOffDiagonal N g r U Q := by
  rw [h15NormalizedBoundaryFixedFrequencyOffDiagonal,
    h15NormalizedBoundaryFixedFrequencyFullPair_eq_sq]
  unfold h15NormalizedBoundaryFixedFrequencyWithinModulusOffDiagonal
    h15NormalizedBoundaryFixedFrequencyCrossModulusOffDiagonal
  ring

/-! ## The sharpened cross-modulus frontier -/

/-- The distinct-modulus sector must compensate the whole nonnegative
modulus-block diagonal up to the allowed energy budget. -/
def H15CorrectionCoupledCrossModulusOffDiagonalCompensation
    (N g r U Q : ℕ) (Δ : ℝ) : Prop :=
  0 ≤ Δ ∧
    h15NormalizedBoundaryFixedFrequencyCrossModulusOffDiagonal N g r U Q ≤
      Δ * h15NormalizedBoundaryCrossModulusFrequencyEnergy N g U Q -
        h15NormalizedBoundaryFixedFrequencyModulusBlockDiagonal N g r U Q

/-- Exact equivalence between the original dispersion gate and negative
cross-modulus compensation after all within-modulus interactions have already
been absorbed. -/
theorem h15CorrectionCoupledCrossModulusFrequencyDispersion_iff_crossCompensation
    (N g r U Q : ℕ) (Δ : ℝ) :
    H15CorrectionCoupledCrossModulusFrequencyDispersion N g r U Q Δ ↔
      H15CorrectionCoupledCrossModulusOffDiagonalCompensation
        N g r U Q Δ := by
  constructor
  · intro hdisp
    refine ⟨hdisp.1, ?_⟩
    have hsq :=
      sq_abs_h15NormalizedBoundaryFourierAggregate_eq_modulusBlockDiagonal_add_cross
        N g r U Q
    linarith [hdisp.2]
  · intro hcomp
    refine ⟨hcomp.1, ?_⟩
    have hsq :=
      sq_abs_h15NormalizedBoundaryFourierAggregate_eq_modulusBlockDiagonal_add_cross
        N g r U Q
    linarith [hcomp.2]

/-- At zero dispersion, different moduli must cancel the entire nonnegative
modulus-block diagonal. -/
theorem h15CorrectionCoupledZeroDispersion_iff_fullModulusBlockCancellation
    (N g r U Q : ℕ) :
    H15CorrectionCoupledCrossModulusFrequencyDispersion N g r U Q 0 ↔
      h15NormalizedBoundaryFixedFrequencyCrossModulusOffDiagonal N g r U Q ≤
        -h15NormalizedBoundaryFixedFrequencyModulusBlockDiagonal N g r U Q := by
  rw [h15CorrectionCoupledCrossModulusFrequencyDispersion_iff_crossCompensation]
  simp [H15CorrectionCoupledCrossModulusOffDiagonalCompensation]

end NBMellinTools.NB12
