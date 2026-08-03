/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEConstantModeLocalFactorization

/-!
# NB12zzzbL: modulus collection of the constant-mode defect

The endpoint mean and Laurent mean depend only on the missing modulus.  The
residue-dependent inner coefficient defects are therefore collected by that
modulus before any estimate is attempted.  This preserves cancellation among
missing residues of the same modulus and gives the smallest natural
one-dimensional constant-mode ledger.
-/

open scoped BigOperators

namespace NBMellinTools.NB12

noncomputable def h15PostFEActualMissingModulusSupport
    (n g U Q : ℕ) : Finset ℕ :=
  (h15PostFEJointMissingAtomSupport
      (h15PostFEResidueModulusSupport n g U Q)
      (h15PostFEReducedMissingResidues n g U Q)).image (fun i => i.1)

noncomputable def h15PostFEConstantDiagonalInnerDefectModulusFiber
    (M : ℕ) [NeZero M] (n g U Q : ℕ) (t : ℝ) (q : ℕ) : ℝ :=
  ∑ i ∈ (h15PostFEJointMissingAtomSupport
      (h15PostFEResidueModulusSupport n g U Q)
      (h15PostFEReducedMissingResidues n g U Q)).filter
      (fun i => i.1 = q),
    h15PostFEConstantDiagonalInnerCoefficientDefect M n g U Q t i

/-- Exact collection of the endpoint-weighted local defects by missing
modulus. -/
theorem h15PostFECompleteConstantDiagonalBalance_eq_modulusLedger
    (M : ℕ) [NeZero M] (n g U Q : ℕ) (t : ℝ) :
    h15PostFECompleteConstantDiagonalBalance M n g U Q t =
      ∑ q ∈ h15PostFEActualMissingModulusSupport n g U Q,
        h15PostFEResidueFiberEndpointMeanCoefficient n g U Q q *
          h15PostFEConstantDiagonalInnerDefectModulusFiber
            M n g U Q t q := by
  rw [h15PostFECompleteConstantDiagonalBalance_eq_sum_endpoint_mul_innerDefect]
  let S := h15PostFEJointMissingAtomSupport
    (h15PostFEResidueModulusSupport n g U Q)
    (h15PostFEReducedMissingResidues n g U Q)
  let coefficient := fun i : H15PostFEMissingAtomIndex =>
    h15PostFEConstantDiagonalInnerCoefficientDefect M n g U Q t i
  let kernel := fun q : ℕ =>
    h15PostFEResidueFiberEndpointMeanCoefficient n g U Q q
  have hcollect := sum_mul_kernel_eq_sum_image_collected
    S (fun i : H15PostFEMissingAtomIndex => i.1) coefficient kernel
  simpa [S, coefficient, kernel, mul_comm,
    h15PostFEActualMissingModulusSupport,
    h15PostFEConstantDiagonalInnerDefectModulusFiber] using hcollect

/-- Constant cancellation is exactly cancellation of the signed
endpoint-weighted modulus ledger. -/
theorem h15PostFECompleteConstantDiagonalBalance_eq_zero_iff_modulusLedger
    (M : ℕ) [NeZero M] (n g U Q : ℕ) (t : ℝ) :
    h15PostFECompleteConstantDiagonalBalance M n g U Q t = 0 ↔
      (∑ q ∈ h15PostFEActualMissingModulusSupport n g U Q,
        h15PostFEResidueFiberEndpointMeanCoefficient n g U Q q *
          h15PostFEConstantDiagonalInnerDefectModulusFiber
            M n g U Q t q) = 0 := by
  rw [h15PostFECompleteConstantDiagonalBalance_eq_modulusLedger]

/-- At a fixed modulus the Laurent contribution is constant across missing
residues; differences of inner defects are therefore exactly differences of
the signed pair fibers. -/
theorem h15PostFEConstantDiagonalInnerDefect_sub_eq_pairFiber_sub
    (M : ℕ) [NeZero M] (n g U Q : ℕ) (t : ℝ)
    (i j : H15PostFEMissingAtomIndex) (hij : i.1 = j.1) :
    h15PostFEConstantDiagonalInnerCoefficientDefect M n g U Q t i -
        h15PostFEConstantDiagonalInnerCoefficientDefect M n g U Q t j =
      h15PostFEDegeneratePairDiagonalMissingFiber M n g U Q t i -
        h15PostFEDegeneratePairDiagonalMissingFiber M n g U Q t j := by
  unfold h15PostFEConstantDiagonalInnerCoefficientDefect
  rw [hij]
  ring

end NBMellinTools.NB12
