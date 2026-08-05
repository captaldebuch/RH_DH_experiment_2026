/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEConstantModeCoefficientAudit

/-!
# NB12zzzbI: equal/opposite orientation split of the constant mode

The constant degenerate diagonal has a sign determined by whether the lifted
pair frequency equals or is opposite to the lifted missing frequency.  This
file partitions the genuine collision support accordingly and removes the
remaining phase notation from the diagonal atom.

The resulting constant-mode audit is a literal signed coefficient ledger:
opposite-collision mass minus equal-collision mass minus four times the full
missing constant mass.  No cancellation of that ledger is asserted.
-/

open scoped BigOperators ComplexConjugate

namespace NBMellinTools.NB12

noncomputable def h15PostFEDegenerateEqualCollisionSupport
    (M : ℕ) [NeZero M] (n g U Q : ℕ) :
    Finset H15PostFEMissingPairAtomIndex :=
  (h15PostFEDegenerateCrossModulusCollisionSupport M n g U Q).filter
    (fun p =>
      h15PostFELiftedMissingFrequency M p.1 =
        h15PostFELiftedPairFrequency M p.2.2.1 p.2.2.2 p.2.1)

noncomputable def h15PostFEDegenerateOppositeCollisionSupport
    (M : ℕ) [NeZero M] (n g U Q : ℕ) :
    Finset H15PostFEMissingPairAtomIndex :=
  (h15PostFEDegenerateCrossModulusCollisionSupport M n g U Q).filter
    (fun p =>
      h15PostFELiftedMissingFrequency M p.1 ≠
        h15PostFELiftedPairFrequency M p.2.2.1 p.2.2.2 p.2.1)

noncomputable def h15PostFEDegenerateSignedDiagonalCoefficientAtom
    (n g U Q : ℕ) (t : ℝ) (p : H15PostFEMissingPairAtomIndex) : ℝ :=
  h15PostFEDegenerateCollisionRealPrefactor n g U Q t p *
    (h15PostFEDegenerateCollisionComplexCoefficient n g U Q t p).im / 2

theorem h15PostFEDegenerateCollisionSupport_eq_equal_add_opposite
    (M : ℕ) [NeZero M] (n g U Q : ℕ)
    (f : H15PostFEMissingPairAtomIndex → ℝ) :
    (∑ p ∈ h15PostFEDegenerateCrossModulusCollisionSupport M n g U Q,
        f p) =
      (∑ p ∈ h15PostFEDegenerateEqualCollisionSupport M n g U Q,
          f p) +
        ∑ p ∈ h15PostFEDegenerateOppositeCollisionSupport M n g U Q,
          f p := by
  classical
  simpa [h15PostFEDegenerateEqualCollisionSupport,
    h15PostFEDegenerateOppositeCollisionSupport] using
      (Finset.sum_filter_add_sum_filter_not
        (h15PostFEDegenerateCrossModulusCollisionSupport M n g U Q)
        (fun p =>
          h15PostFELiftedMissingFrequency M p.1 =
            h15PostFELiftedPairFrequency M p.2.2.1 p.2.2.2 p.2.1)
        f).symm

theorem h15PostFEDegenerateCollisionDiagonalAtom_eq_neg_signedCoefficient
    (M : ℕ) [NeZero M] (n g U Q : ℕ) (t : ℝ)
    (p : H15PostFEMissingPairAtomIndex)
    (hp : h15PostFELiftedMissingFrequency M p.1 =
      h15PostFELiftedPairFrequency M p.2.2.1 p.2.2.2 p.2.1) :
    h15PostFEDegenerateCollisionDiagonalAtom M n g U Q t p =
      -h15PostFEDegenerateSignedDiagonalCoefficientAtom n g U Q t p := by
  simp [h15PostFEDegenerateCollisionDiagonalAtom,
    h15PostFECollidingPhaseDiagonal,
    h15PostFEDegenerateSignedDiagonalCoefficientAtom, hp]
  ring

theorem h15PostFEDegenerateCollisionDiagonalAtom_eq_signedCoefficient
    (M : ℕ) [NeZero M] (n g U Q : ℕ) (t : ℝ)
    (p : H15PostFEMissingPairAtomIndex)
    (hp : h15PostFELiftedMissingFrequency M p.1 ≠
      h15PostFELiftedPairFrequency M p.2.2.1 p.2.2.2 p.2.1) :
    h15PostFEDegenerateCollisionDiagonalAtom M n g U Q t p =
      h15PostFEDegenerateSignedDiagonalCoefficientAtom n g U Q t p := by
  simp [h15PostFEDegenerateCollisionDiagonalAtom,
    h15PostFECollidingPhaseDiagonal,
    h15PostFEDegenerateSignedDiagonalCoefficientAtom, hp]
  ring

/-- The degenerate diagonal is the opposite-collision coefficient mass minus
the equal-collision coefficient mass. -/
theorem h15PostFEDegenerateCollisionDiagonalDispersion_eq_opposite_sub_equal
    (M : ℕ) [NeZero M] (n g U Q : ℕ) (t : ℝ) :
    h15PostFEDegenerateCollisionDiagonalDispersion M n g U Q t =
      (∑ p ∈ h15PostFEDegenerateOppositeCollisionSupport M n g U Q,
          h15PostFEDegenerateSignedDiagonalCoefficientAtom n g U Q t p) -
        ∑ p ∈ h15PostFEDegenerateEqualCollisionSupport M n g U Q,
          h15PostFEDegenerateSignedDiagonalCoefficientAtom n g U Q t p := by
  rw [h15PostFEDegenerateCollisionDiagonalDispersion_eq_supportSum]
  rw [h15PostFEDegenerateCollisionSupport_eq_equal_add_opposite]
  have heq :
      (∑ p ∈ h15PostFEDegenerateEqualCollisionSupport M n g U Q,
          h15PostFEDegenerateCollisionDiagonalAtom M n g U Q t p) =
        ∑ p ∈ h15PostFEDegenerateEqualCollisionSupport M n g U Q,
          -h15PostFEDegenerateSignedDiagonalCoefficientAtom n g U Q t p := by
    apply Finset.sum_congr rfl
    intro p hp
    exact h15PostFEDegenerateCollisionDiagonalAtom_eq_neg_signedCoefficient
      M n g U Q t p (Finset.mem_filter.mp hp).2
  have hopp :
      (∑ p ∈ h15PostFEDegenerateOppositeCollisionSupport M n g U Q,
          h15PostFEDegenerateCollisionDiagonalAtom M n g U Q t p) =
        ∑ p ∈ h15PostFEDegenerateOppositeCollisionSupport M n g U Q,
          h15PostFEDegenerateSignedDiagonalCoefficientAtom n g U Q t p := by
    apply Finset.sum_congr rfl
    intro p hp
    exact h15PostFEDegenerateCollisionDiagonalAtom_eq_signedCoefficient
      M n g U Q t p (Finset.mem_filter.mp hp).2
  rw [heq, hopp, Finset.sum_neg_distrib]
  ring

/-- Final coefficient-only normal form of the constant diagonal balance. -/
theorem h15PostFECompleteConstantDiagonalBalance_eq_orientationLedger
    (M : ℕ) [NeZero M] (n g U Q : ℕ) (t : ℝ) :
    h15PostFECompleteConstantDiagonalBalance M n g U Q t =
      (∑ p ∈ h15PostFEDegenerateOppositeCollisionSupport M n g U Q,
          h15PostFEDegenerateSignedDiagonalCoefficientAtom n g U Q t p) -
        (∑ p ∈ h15PostFEDegenerateEqualCollisionSupport M n g U Q,
          h15PostFEDegenerateSignedDiagonalCoefficientAtom n g U Q t p) -
        4 * h15PostFEMissingMissingDiagonalConstantFiber n g U Q t := by
  unfold h15PostFECompleteConstantDiagonalBalance
  rw [h15PostFEDegenerateCollisionDiagonalDispersion_eq_opposite_sub_equal]

end NBMellinTools.NB12
