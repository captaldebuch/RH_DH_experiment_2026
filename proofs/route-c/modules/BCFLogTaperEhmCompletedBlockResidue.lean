import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmEarlyBlockCorrection

/-!
# Residue-completed dyadic Ehm blocks

The Ehm dyadic construction distributes the retained H15 correction by an
arbitrary unit-mass allocation.  A contour or trace-formula calculation, on
the other hand, produces arithmetic residue, zero-mode, and diagonal terms.
There is no reason for those physical terms to agree block by block with a
chosen allocation.

This file records the exact comparison before any absolute value is taken.
For a family of physical block modes `Z`, the local mismatch is

`physicalMode Z k - weight k * retainedCorrection`.

The correction-completed Abel block is exactly the physical-mode transform
minus this mismatch.  Summing the mismatches gives the physical total minus
the retained correction.  In particular, the desired geometric matching is
equivalent to the vanishing of the displayed mismatch; it is not asserted.

All statements in this file are finite algebraic identities.  No contour
shift, trace formula, or cancellation estimate is assumed.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmCompletedBlockResidue

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCoupledNearCoreTarget
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCutoffAverageMainTerm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicCorrectionAbel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmEarlyBlockCorrection
open RH.Criteria.NymanBeurling.BCFLogTaperEhmExplicitFarCutoff
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRectangularInstantiation

/-- Real components of a block-localized contour/trace calculation.  The
three fields are already projected to the real scalar in the H15 target.
This structure contains data only; it makes no matching assertion. -/
structure EhmCompletedBlockContourModes where
  residueMode : ℕ → ℝ
  zeroMode : ℕ → ℝ
  diagonalMode : ℕ → ℝ

/-- The complete physical contribution assigned by a contour calculation to
one dyadic block. -/
noncomputable def ehmCompletedBlockPhysicalMode
    (Z : EhmCompletedBlockContourModes) (k : ℕ) : ℝ :=
  Z.residueMode k + Z.zeroMode k + Z.diagonalMode k

/-- Difference between the physical block contribution and the correction
share selected by an arbitrary unit-mass Ehm allocation. -/
noncomputable def ehmCompletedBlockCorrectionMismatch
    (R1 : ℝ → ℝ) (X J L : ℕ)
    (A : EhmDyadicCorrectionAllocation X L)
    (Z : EhmCompletedBlockContourModes) (k : ℕ) : ℝ :=
  ehmCompletedBlockPhysicalMode Z k -
    A.weight k * ehmH15RetainedCorrection R1 X J

/-- The Abel block with its physical residue/zero/diagonal contribution,
before any triangle inequality or allocation replacement. -/
noncomputable def ehmCompletedBlockPhysicalTransform
    (R1 : ℝ → ℝ) (X J M L : ℕ)
    (Z : EhmCompletedBlockContourModes) (k : ℕ) : ℝ :=
  ehmShiftedDyadicAbelExpression R1 X J M L k +
    ehmCompletedBlockPhysicalMode Z k

/-- Exact local correction ledger.  This is the corrected target when a
physical contour mode is not known to equal the chosen correction share. -/
theorem ehmCorrectionCompletedDyadicAbelBlock_eq_physical_sub_mismatch
    (R1 : ℝ → ℝ) (X J M L k : ℕ)
    (A : EhmDyadicCorrectionAllocation X L)
    (Z : EhmCompletedBlockContourModes) :
    ehmCorrectionCompletedDyadicAbelBlock R1 X J M L A k =
      ehmCompletedBlockPhysicalTransform R1 X J M L Z k -
        ehmCompletedBlockCorrectionMismatch R1 X J L A Z k := by
  unfold ehmCorrectionCompletedDyadicAbelBlock
    ehmCompletedBlockPhysicalTransform
    ehmCompletedBlockCorrectionMismatch
  ring

/-- The total allocation mismatch is exactly the physical total minus the
retained H15 correction.  No estimate and no absolute value is involved. -/
theorem sum_ehmCompletedBlockCorrectionMismatch
    (R1 : ℝ → ℝ) (X J L : ℕ)
    (A : EhmDyadicCorrectionAllocation X L)
    (Z : EhmCompletedBlockContourModes) :
    (∑ k ∈ ehmShiftedDyadicDIndices X L,
      ehmCompletedBlockCorrectionMismatch R1 X J L A Z k) =
        (∑ k ∈ ehmShiftedDyadicDIndices X L,
          ehmCompletedBlockPhysicalMode Z k) -
          ehmH15RetainedCorrection R1 X J := by
  classical
  unfold ehmCompletedBlockCorrectionMismatch
  rw [Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_mul]
  rw [A.mass_one, one_mul]

/-- Exact finite transform of every correction-completed block.  The only
remainder is the explicitly displayed physical/allocation mismatch. -/
theorem sum_ehmCorrectionCompletedDyadicAbelBlock_eq_physical_sub_mismatch
    (R1 : ℝ → ℝ) (X J M L : ℕ)
    (A : EhmDyadicCorrectionAllocation X L)
    (Z : EhmCompletedBlockContourModes) :
    (∑ k ∈ ehmShiftedDyadicDIndices X L,
      ehmCorrectionCompletedDyadicAbelBlock R1 X J M L A k) =
        (∑ k ∈ ehmShiftedDyadicDIndices X L,
          ehmCompletedBlockPhysicalTransform R1 X J M L Z k) -
        ∑ k ∈ ehmShiftedDyadicDIndices X L,
          ehmCompletedBlockCorrectionMismatch R1 X J L A Z k := by
  classical
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  exact ehmCorrectionCompletedDyadicAbelBlock_eq_physical_sub_mismatch
    R1 X J M L k A Z

/-- A zero total mismatch is equivalent to matching the *sum* of the
physical modes with the retained correction.  This is weaker than local
blockwise matching and is the exact global normalization obligation. -/
theorem sum_ehmCompletedBlockCorrectionMismatch_eq_zero_iff
    (R1 : ℝ → ℝ) (X J L : ℕ)
    (A : EhmDyadicCorrectionAllocation X L)
    (Z : EhmCompletedBlockContourModes) :
    (∑ k ∈ ehmShiftedDyadicDIndices X L,
      ehmCompletedBlockCorrectionMismatch R1 X J L A Z k) = 0 ↔
        (∑ k ∈ ehmShiftedDyadicDIndices X L,
          ehmCompletedBlockPhysicalMode Z k) =
          ehmH15RetainedCorrection R1 X J := by
  rw [sum_ehmCompletedBlockCorrectionMismatch]
  exact sub_eq_zero

/-- Specialization of the local mismatch to the normalized geometric
weights `w_k proportional to 2^{-k}`. -/
noncomputable def ehmGeometricCompletedBlockMismatch
    (R1 : ℝ → ℝ) (X J L : ℕ)
    (Z : EhmCompletedBlockContourModes) (k : ℕ) : ℝ :=
  ehmCompletedBlockPhysicalMode Z k -
    ehmGeometricCorrectionWeight X L k *
      ehmH15RetainedCorrection R1 X J

/-- The proposed equality `physicalMode k = w_k * C` holds precisely when
the geometric block mismatch vanishes.  This is the first presently open
local equality, stated without promoting it to a hypothesis or theorem. -/
theorem physicalMode_eq_geometricCorrectionShare_iff
    (R1 : ℝ → ℝ) (X J L k : ℕ)
    (Z : EhmCompletedBlockContourModes) :
    ehmCompletedBlockPhysicalMode Z k =
        ehmGeometricCorrectionWeight X L k *
          ehmH15RetainedCorrection R1 X J ↔
      ehmGeometricCompletedBlockMismatch R1 X J L Z k = 0 := by
  unfold ehmGeometricCompletedBlockMismatch
  simp only [sub_eq_zero]

/-- The geometric completed block has the physical contour form plus the
explicit local mismatch remainder. -/
theorem ehmGeometricCompletedBlock_eq_physical_sub_mismatch
    (R1 : ℝ → ℝ) (X J M L k : ℕ)
    (Z : EhmCompletedBlockContourModes) :
    ehmCorrectionCompletedDyadicAbelBlock R1 X J M L
        (ehmGeometricCorrectionAllocation X L) k =
      ehmCompletedBlockPhysicalTransform R1 X J M L Z k -
        ehmGeometricCompletedBlockMismatch R1 X J L Z k := by
  unfold ehmCorrectionCompletedDyadicAbelBlock
    ehmCompletedBlockPhysicalTransform
    ehmGeometricCompletedBlockMismatch
    ehmGeometricCorrectionAllocation
  ring

/-- The summed geometric mismatch has the same exact total as every other
unit-mass allocation: physical total minus retained correction. -/
theorem sum_ehmGeometricCompletedBlockMismatch
    (R1 : ℝ → ℝ) (X J L : ℕ)
    (Z : EhmCompletedBlockContourModes) :
    (∑ k ∈ ehmShiftedDyadicDIndices X L,
      ehmGeometricCompletedBlockMismatch R1 X J L Z k) =
        (∑ k ∈ ehmShiftedDyadicDIndices X L,
          ehmCompletedBlockPhysicalMode Z k) -
          ehmH15RetainedCorrection R1 X J := by
  classical
  unfold ehmGeometricCompletedBlockMismatch
  rw [Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_mul]
  rw [sum_ehmGeometricCorrectionWeight, one_mul]

/-- Proof-carrying global correction matching.  The contour modes need only
reproduce the retained correction after summing the physical dyadic blocks;
no unsupported equality with the geometric share is requested blockwise. -/
structure EhmCompletedBlockGlobalCorrectionMatching
    (R1 : ℝ → ℝ) (X J L : ℕ) where
  modes : EhmCompletedBlockContourModes
  physical_sum_eq_correction :
    (∑ k ∈ ehmShiftedDyadicDIndices X L,
      ehmCompletedBlockPhysicalMode modes k) =
        ehmH15RetainedCorrection R1 X J

/-- Global physical correction matching kills the *sum* of local geometric
mismatches while retaining every local term signed until reassembly. -/
theorem EhmCompletedBlockGlobalCorrectionMatching.sum_geometricMismatch_eq_zero
    {R1 : ℝ → ℝ} {X J L : ℕ}
    (H : EhmCompletedBlockGlobalCorrectionMatching R1 X J L) :
    (∑ k ∈ ehmShiftedDyadicDIndices X L,
      ehmGeometricCompletedBlockMismatch R1 X J L H.modes k) = 0 := by
  rw [sum_ehmGeometricCompletedBlockMismatch,
    H.physical_sum_eq_correction, sub_self]

/-- At the actual H15 near cutoff, the coupled near core is exactly the sum
of the physical block transforms minus the explicit geometric mismatch. -/
theorem ehmDyadicExplicitCoupledNearCore_eq_physical_sub_geometricMismatch
    (R1 : ℝ → ℝ) (X J : ℕ)
    (Z : EhmCompletedBlockContourModes) (hX : 1 ≤ X) :
    ehmDyadicExplicitCoupledNearCore R1 X (ehmExplicitFarCutoff X) J =
      (∑ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
        ehmCompletedBlockPhysicalTransform R1 X J
          (ehmH15NearMMax X) (ehmH15NearDMax X) Z k) -
      ∑ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
        ehmGeometricCompletedBlockMismatch R1 X J
          (ehmH15NearDMax X) Z k := by
  rw [← sum_ehmCorrectionCompletedDyadicAbelBlock_eq_coupledNearCore
    R1 X J (ehmGeometricCorrectionAllocation X (ehmH15NearDMax X)) hX]
  exact sum_ehmCorrectionCompletedDyadicAbelBlock_eq_physical_sub_mismatch
    R1 X J (ehmH15NearMMax X) (ehmH15NearDMax X)
      (ehmGeometricCorrectionAllocation X (ehmH15NearDMax X)) Z

/-- Once a contour calculation supplies global correction matching at the
actual H15 cutoff, the coupled near core is exactly the sum of its physical
block transforms.  This is the correct diagonal/residue endpoint for the
direct route; a signed `o(X)` estimate for this sum is still required. -/
theorem ehmDyadicExplicitCoupledNearCore_eq_sum_physical_of_globalMatching
    (R1 : ℝ → ℝ) (X J : ℕ)
    (H : EhmCompletedBlockGlobalCorrectionMatching R1 X J
      (ehmH15NearDMax X))
    (hX : 1 ≤ X) :
    ehmDyadicExplicitCoupledNearCore R1 X (ehmExplicitFarCutoff X) J =
      ∑ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
        ehmCompletedBlockPhysicalTransform R1 X J
          (ehmH15NearMMax X) (ehmH15NearDMax X) H.modes k := by
  rw [ehmDyadicExplicitCoupledNearCore_eq_physical_sub_geometricMismatch
    R1 X J H.modes hX, H.sum_geometricMismatch_eq_zero, sub_zero]

end RH.Criteria.NymanBeurling.BCFLogTaperEhmCompletedBlockResidue
