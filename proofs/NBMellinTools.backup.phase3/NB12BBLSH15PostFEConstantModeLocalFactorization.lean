/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEConstantModeFiberMismatch

/-!
# NB12zzzbK: local endpoint-times-coefficient factorization

Every diagonal collision atom contains the endpoint mean coefficient of its
missing modulus as a literal factor.  This file pulls that factor through each
missing fiber.  The local constant-mode mismatch becomes

`endpointMean * (signedPairMass - 2 * laurentMean)`.

Thus any exact residue/finite-part cancellation must act on the displayed
inner coefficient defect.  No such cancellation is assumed here.
-/

open scoped BigOperators

namespace NBMellinTools.NB12

noncomputable def h15PostFEDegeneratePairDiagonalCoefficient
    (M : ℕ) [NeZero M] (n g U Q : ℕ) (t : ℝ)
    (p : H15PostFEMissingPairAtomIndex) : ℝ :=
  (4 / (2 * h15PairedHyperbolicCoefficient t)) *
    h15PostFECollidingPhaseDiagonal
      (h15PostFELiftedMissingFrequency M p.1)
      (h15PostFELiftedPairFrequency M p.2.2.1 p.2.2.2 p.2.1)
      (h15PostFEDegenerateCollisionComplexCoefficient n g U Q t p)

theorem h15PostFEDegenerateCollisionDiagonalAtom_eq_endpoint_mul_pairCoefficient
    (M : ℕ) [NeZero M] (n g U Q : ℕ) (t : ℝ)
    (p : H15PostFEMissingPairAtomIndex) :
    h15PostFEDegenerateCollisionDiagonalAtom M n g U Q t p =
      h15PostFEResidueFiberEndpointMeanCoefficient n g U Q p.1.1 *
        h15PostFEDegeneratePairDiagonalCoefficient M n g U Q t p := by
  unfold h15PostFEDegenerateCollisionDiagonalAtom
    h15PostFEDegenerateCollisionRealPrefactor
    h15PostFEDegeneratePairDiagonalCoefficient
  ring

noncomputable def h15PostFEDegeneratePairDiagonalMissingFiber
    (M : ℕ) [NeZero M] (n g U Q : ℕ) (t : ℝ)
    (i : H15PostFEMissingAtomIndex) : ℝ :=
  ∑ p ∈ (h15PostFEDegenerateCrossModulusCollisionSupport M n g U Q).filter
      (fun p => p.1 = i),
    h15PostFEDegeneratePairDiagonalCoefficient M n g U Q t p

theorem h15PostFEDegenerateCollisionDiagonalMissingFiber_eq_endpoint_mul_pairFiber
    (M : ℕ) [NeZero M] (n g U Q : ℕ) (t : ℝ)
    (i : H15PostFEMissingAtomIndex) :
    h15PostFEDegenerateCollisionDiagonalMissingFiber M n g U Q t i =
      h15PostFEResidueFiberEndpointMeanCoefficient n g U Q i.1 *
        h15PostFEDegeneratePairDiagonalMissingFiber M n g U Q t i := by
  unfold h15PostFEDegenerateCollisionDiagonalMissingFiber
    h15PostFEDegeneratePairDiagonalMissingFiber
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [h15PostFEDegenerateCollisionDiagonalAtom_eq_endpoint_mul_pairCoefficient]
  rw [(Finset.mem_filter.mp hp).2]

noncomputable def h15PostFEConstantDiagonalInnerCoefficientDefect
    (M : ℕ) [NeZero M] (n g U Q : ℕ) (t : ℝ)
    (i : H15PostFEMissingAtomIndex) : ℝ :=
  h15PostFEDegeneratePairDiagonalMissingFiber M n g U Q t i -
    2 * h15PostFEResidueFiberLaurentMeanCoefficientWithoutFrequency
      n g U Q t i.1

/-- Exact local factorization of the constant-mode mismatch. -/
theorem h15PostFEConstantDiagonalMissingFiberMismatch_eq_endpoint_mul_innerDefect
    (M : ℕ) [NeZero M] (n g U Q : ℕ) (t : ℝ)
    (i : H15PostFEMissingAtomIndex) :
    h15PostFEConstantDiagonalMissingFiberMismatch M n g U Q t i =
      h15PostFEResidueFiberEndpointMeanCoefficient n g U Q i.1 *
        h15PostFEConstantDiagonalInnerCoefficientDefect M n g U Q t i := by
  unfold h15PostFEConstantDiagonalMissingFiberMismatch
    h15PostFEMissingMissingDiagonalConstantAtom
    h15PostFEConstantDiagonalInnerCoefficientDefect
  rw [h15PostFEDegenerateCollisionDiagonalMissingFiber_eq_endpoint_mul_pairFiber]
  ring

/-- Complete endpoint-weighted inner-defect form of the constant balance. -/
theorem h15PostFECompleteConstantDiagonalBalance_eq_sum_endpoint_mul_innerDefect
    (M : ℕ) [NeZero M] (n g U Q : ℕ) (t : ℝ) :
    h15PostFECompleteConstantDiagonalBalance M n g U Q t =
      ∑ i ∈ h15PostFEJointMissingAtomSupport
          (h15PostFEResidueModulusSupport n g U Q)
          (h15PostFEReducedMissingResidues n g U Q),
        h15PostFEResidueFiberEndpointMeanCoefficient n g U Q i.1 *
          h15PostFEConstantDiagonalInnerCoefficientDefect M n g U Q t i := by
  rw [h15PostFECompleteConstantDiagonalBalance_eq_sum_missingFiberMismatch]
  apply Finset.sum_congr rfl
  intro i _hi
  exact
    h15PostFEConstantDiagonalMissingFiberMismatch_eq_endpoint_mul_innerDefect
      M n g U Q t i

end NBMellinTools.NB12
