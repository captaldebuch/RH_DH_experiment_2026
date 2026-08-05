/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEConstantModeOrientationSplit

/-!
# NB12zzzbJ: missing-fiber localization of the constant-mode gap

The signed equal/opposite collision diagonal is collected by its missing atom.
The projected collision support is proved to lie inside the genuine full
missing support, so the sum can be extended there by zero.  The complete
constant balance then becomes one sum of local coefficient mismatches.

This is the strongest purely finite localization available at this stage.  It
does not assert pointwise matching or cancellation of the resulting signed
sum.
-/

open scoped BigOperators

namespace NBMellinTools.NB12

noncomputable def h15PostFEDegenerateCollisionMissingProjection
    (M : ℕ) [NeZero M] (n g U Q : ℕ) :
    Finset H15PostFEMissingAtomIndex :=
  (h15PostFEDegenerateCrossModulusCollisionSupport M n g U Q).image Prod.fst

noncomputable def h15PostFEDegenerateCollisionDiagonalMissingFiber
    (M : ℕ) [NeZero M] (n g U Q : ℕ) (t : ℝ)
    (i : H15PostFEMissingAtomIndex) : ℝ :=
  ∑ p ∈ (h15PostFEDegenerateCrossModulusCollisionSupport M n g U Q).filter
      (fun p => p.1 = i),
    h15PostFEDegenerateCollisionDiagonalAtom M n g U Q t p

theorem h15PostFEDegenerateCollisionDiagonalDispersion_eq_missingProjection
    (M : ℕ) [NeZero M] (n g U Q : ℕ) (t : ℝ) :
    h15PostFEDegenerateCollisionDiagonalDispersion M n g U Q t =
      ∑ i ∈ h15PostFEDegenerateCollisionMissingProjection M n g U Q,
        h15PostFEDegenerateCollisionDiagonalMissingFiber
          M n g U Q t i := by
  classical
  rw [h15PostFEDegenerateCollisionDiagonalDispersion_eq_supportSum]
  let S := h15PostFEDegenerateCrossModulusCollisionSupport M n g U Q
  let summand := fun p : H15PostFEMissingPairAtomIndex =>
    h15PostFEDegenerateCollisionDiagonalAtom M n g U Q t p
  have hcollect := sum_mul_kernel_eq_sum_image_collected
    S Prod.fst summand (fun _i : H15PostFEMissingAtomIndex => (1 : ℝ))
  simpa [S, summand, h15PostFEDegenerateCollisionMissingProjection,
    h15PostFEDegenerateCollisionDiagonalMissingFiber] using hcollect

theorem h15PostFEDegenerateCollisionMissingProjection_subset_missingSupport
    (M : ℕ) [NeZero M] (n g U Q : ℕ) :
    h15PostFEDegenerateCollisionMissingProjection M n g U Q ⊆
      h15PostFEJointMissingAtomSupport
        (h15PostFEResidueModulusSupport n g U Q)
        (h15PostFEReducedMissingResidues n g U Q) := by
  classical
  intro i hi
  rw [h15PostFEDegenerateCollisionMissingProjection,
    Finset.mem_image] at hi
  rcases hi with ⟨p, hp, rfl⟩
  exact (h15PostFEDegenerateCrossModulusCollisionSupport_mem_base hp).1

theorem h15PostFEDegenerateCollisionDiagonalMissingFiber_eq_zero_of_not_mem_projection
    (M : ℕ) [NeZero M] (n g U Q : ℕ) (t : ℝ)
    {i : H15PostFEMissingAtomIndex}
    (hi : i ∉ h15PostFEDegenerateCollisionMissingProjection M n g U Q) :
    h15PostFEDegenerateCollisionDiagonalMissingFiber M n g U Q t i = 0 := by
  classical
  unfold h15PostFEDegenerateCollisionDiagonalMissingFiber
  apply Finset.sum_eq_zero
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  exfalso
  apply hi
  exact Finset.mem_image.mpr ⟨p, hp'.1, hp'.2⟩

/-- Zero-extension from the collision projection to the complete missing
support is exact. -/
theorem h15PostFEDegenerateCollisionDiagonalDispersion_eq_missingSupport
    (M : ℕ) [NeZero M] (n g U Q : ℕ) (t : ℝ) :
    h15PostFEDegenerateCollisionDiagonalDispersion M n g U Q t =
      ∑ i ∈ h15PostFEJointMissingAtomSupport
          (h15PostFEResidueModulusSupport n g U Q)
          (h15PostFEReducedMissingResidues n g U Q),
        h15PostFEDegenerateCollisionDiagonalMissingFiber
          M n g U Q t i := by
  rw [h15PostFEDegenerateCollisionDiagonalDispersion_eq_missingProjection]
  apply Finset.sum_subset
    (h15PostFEDegenerateCollisionMissingProjection_subset_missingSupport
      M n g U Q)
  intro i _hi hnot
  exact
    h15PostFEDegenerateCollisionDiagonalMissingFiber_eq_zero_of_not_mem_projection
      M n g U Q t hnot

noncomputable def h15PostFEConstantDiagonalMissingFiberMismatch
    (M : ℕ) [NeZero M] (n g U Q : ℕ) (t : ℝ)
    (i : H15PostFEMissingAtomIndex) : ℝ :=
  h15PostFEDegenerateCollisionDiagonalMissingFiber M n g U Q t i -
    4 * h15PostFEMissingMissingDiagonalConstantAtom n g U Q t i

/-- The complete constant balance is exactly the signed sum of local
missing-fiber coefficient mismatches. -/
theorem h15PostFECompleteConstantDiagonalBalance_eq_sum_missingFiberMismatch
    (M : ℕ) [NeZero M] (n g U Q : ℕ) (t : ℝ) :
    h15PostFECompleteConstantDiagonalBalance M n g U Q t =
      ∑ i ∈ h15PostFEJointMissingAtomSupport
          (h15PostFEResidueModulusSupport n g U Q)
          (h15PostFEReducedMissingResidues n g U Q),
        h15PostFEConstantDiagonalMissingFiberMismatch M n g U Q t i := by
  unfold h15PostFECompleteConstantDiagonalBalance
    h15PostFEMissingMissingDiagonalConstantFiber
    h15PostFEConstantDiagonalMissingFiberMismatch
  rw [h15PostFEDegenerateCollisionDiagonalDispersion_eq_missingSupport]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]

end NBMellinTools.NB12
