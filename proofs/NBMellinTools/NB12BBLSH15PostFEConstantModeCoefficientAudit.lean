/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFECompleteHarmonicNormalForm

/-!
# NB12zzzbH: coefficient-level audit of the constant diagonal balance

The frequency-independent degenerate diagonal was originally collected by the
quotient `k = q*q'/p`.  This file removes that organizational index and
recovers the exact sum over the genuine collision support.  It then compares
that sum with the constant part of the missing--missing diagonal at the
factor-four normalization forced by the full H15 alignment identity.

The result is deliberately an audit: it proves the precise finite coefficient
identity equivalent to constant-mode cancellation, but does not assume or
claim that identity.
-/

open scoped BigOperators

namespace NBMellinTools.NB12

/-- The quotient-collected degenerate diagonal is exactly the direct sum over
the genuine density-degenerate collision support. -/
theorem h15PostFEDegenerateCollisionDiagonalDispersion_eq_supportSum
    (M : ℕ) [NeZero M] (n g U Q : ℕ) (t : ℝ) :
    h15PostFEDegenerateCollisionDiagonalDispersion M n g U Q t =
      ∑ p ∈ h15PostFEDegenerateCrossModulusCollisionSupport M n g U Q,
        h15PostFEDegenerateCollisionDiagonalAtom M n g U Q t p := by
  classical
  let S := h15PostFEDegenerateCrossModulusCollisionSupport M n g U Q
  let key := h15PostFEMissingPairDegenerateQuotient
  let summand := fun p : H15PostFEMissingPairAtomIndex =>
    h15PostFEDegenerateCollisionDiagonalAtom M n g U Q t p
  have hcollect := sum_mul_kernel_eq_sum_image_collected
    S key summand (fun _k : ℕ => (1 : ℝ))
  simpa [S, key, summand, h15PostFEDegenerateCollisionDiagonalDispersion,
    h15PostFEDegenerateQuotientFrequencyDiagonalFiber,
    h15PostFEDegenerateQuotientSupport] using hcollect.symm

/-- The literal coefficient residual whose vanishing is exactly constant-mode
matching.  Both finite supports and every H15 coefficient remain visible. -/
noncomputable def h15PostFEConstantDiagonalCoefficientResidual
    (M : ℕ) [NeZero M] (n g U Q : ℕ) (t : ℝ) : ℝ :=
  (∑ p ∈ h15PostFEDegenerateCrossModulusCollisionSupport M n g U Q,
      h15PostFEDegenerateCollisionDiagonalAtom M n g U Q t p) -
    4 *
      ∑ i ∈ h15PostFEJointMissingAtomSupport
          (h15PostFEResidueModulusSupport n g U Q)
          (h15PostFEReducedMissingResidues n g U Q),
        h15PostFEMissingMissingDiagonalConstantAtom n g U Q t i

/-- The abstract constant diagonal balance is the literal finite coefficient
residual. -/
theorem h15PostFECompleteConstantDiagonalBalance_eq_coefficientResidual
    (M : ℕ) [NeZero M] (n g U Q : ℕ) (t : ℝ) :
    h15PostFECompleteConstantDiagonalBalance M n g U Q t =
      h15PostFEConstantDiagonalCoefficientResidual M n g U Q t := by
  unfold h15PostFECompleteConstantDiagonalBalance
  rw [h15PostFEDegenerateCollisionDiagonalDispersion_eq_supportSum]
  rfl

/-- Constant-mode cancellation holds if and only if the direct degenerate
collision coefficient sum equals four times the missing constant sum. -/
theorem h15PostFECompleteConstantDiagonalBalance_eq_zero_iff_coefficientIdentity
    (M : ℕ) [NeZero M] (n g U Q : ℕ) (t : ℝ) :
    h15PostFECompleteConstantDiagonalBalance M n g U Q t = 0 ↔
      (∑ p ∈ h15PostFEDegenerateCrossModulusCollisionSupport M n g U Q,
          h15PostFEDegenerateCollisionDiagonalAtom M n g U Q t p) =
        4 *
          ∑ i ∈ h15PostFEJointMissingAtomSupport
              (h15PostFEResidueModulusSupport n g U Q)
              (h15PostFEReducedMissingResidues n g U Q),
            h15PostFEMissingMissingDiagonalConstantAtom n g U Q t i := by
  rw [h15PostFECompleteConstantDiagonalBalance_eq_coefficientResidual]
  unfold h15PostFEConstantDiagonalCoefficientResidual
  exact sub_eq_zero

end NBMellinTools.NB12
