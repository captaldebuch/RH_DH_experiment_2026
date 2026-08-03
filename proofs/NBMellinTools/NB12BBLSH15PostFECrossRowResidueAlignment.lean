/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFERamanujanCompletion

/-!
# NB12zzzh: residue alignment of the ordered post-FE cross-row dispersion

The literal ordered Laurent-row off-diagonal is reindexed as one finite row-
pair family and then collected by the two residue keys

`((u mod q,q),(u' mod q',q'))`.

Every key occurring in this pair support belongs to the actual post-FE residue
support.  Hence neither coordinate belongs to the missing-residue support.
This is an exact support-level stop test: the linear missing-residue trace has
no termwise counterpart inside the ordered cross-row sum.  Any cancellation
between them must therefore be a global signed identity or estimate, not a
same-index diagonal cancellation.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate
open Complex

namespace NBMellinTools.NB12

/-- Dependent-pair index type for two Laurent rows with the same ambient
cutoff. -/
abbrev H15PostFEOrderedLaurentPairIndex (N : ℕ) :=
  Σ _ : H15LaurentRowIndex N, H15LaurentRowIndex N

/-- Literal ordered distinct-row family underlying the orientation-zero
off-diagonal. -/
def h15PostFEOrderedLaurentPairIndices
    (n g U Q : ℕ) :
    Finset (H15PostFEOrderedLaurentPairIndex (NB8.logTaperLength n)) :=
  (h15DoublyLocalizedOrientationZeroIndices
    (NB8.logTaperLength n) g U Q).sigma fun i =>
      (h15DoublyLocalizedOrientationZeroIndices
        (NB8.logTaperLength n) g U Q).erase i

/-- Residue key of one orientation-zero Laurent row. -/
def h15PostFEOrientationZeroRowResidueKey
    {N : ℕ} (i : H15LaurentRowIndex N) : ℕ × ℕ :=
  h15PostFEResidueKey (h15OrientationZeroLaurentRowKey i)

/-- Pair of residue keys attached to an ordered pair of Laurent rows. -/
def h15PostFEOrderedPairResidueKey
    {N : ℕ} (p : H15PostFEOrderedLaurentPairIndex N) :
    (ℕ × ℕ) × (ℕ × ℕ) :=
  (h15PostFEOrientationZeroRowResidueKey p.1,
    h15PostFEOrientationZeroRowResidueKey p.2)

/-- One literal ordered cross-row summand. -/
noncomputable def h15PostFEOrderedPairSummand
    (n r : ℕ) (t : ℝ)
    (p : H15PostFEOrderedLaurentPairIndex (NB8.logTaperLength n)) : ℝ :=
  (conj
      (h15DirectAdditiveFixedHeightSummand (NB8.logTaperLength n)
        (h15ContourDamping n) (p.1, r) t) *
    h15DirectAdditiveFixedHeightSummand (NB8.logTaperLength n)
      (h15ContourDamping n) (p.2, r) t).re

/-- The nested erase-sum defining the off-diagonal is exactly one sum over
the ordered row-pair family. -/
theorem h15OrientationZeroFrequencyOffDiagonal_eq_orderedPairSum
    (n g U Q r : ℕ) (t : ℝ) :
    h15OrientationZeroFrequencyOffDiagonal n g U Q r t =
      ∑ p ∈ h15PostFEOrderedLaurentPairIndices n g U Q,
        h15PostFEOrderedPairSummand n r t p := by
  unfold h15OrientationZeroFrequencyOffDiagonal
    h15PostFEOrderedLaurentPairIndices h15PostFEOrderedPairSummand
  rw [Finset.sum_sigma']

/-- Finite support of ordered residue-key pairs. -/
def h15PostFEOrderedPairResidueSupport
    (n g U Q : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (h15PostFEOrderedLaurentPairIndices n g U Q).image
    h15PostFEOrderedPairResidueKey

/-- Ordered cross-row coefficients collected at a fixed pair of residue
keys. -/
noncomputable def h15PostFEOrderedPairResidueCoefficient
    (n g U Q r : ℕ) (t : ℝ) (κ : (ℕ × ℕ) × (ℕ × ℕ)) : ℝ :=
  ∑ p ∈ (h15PostFEOrderedLaurentPairIndices n g U Q).filter
      (fun p => h15PostFEOrderedPairResidueKey p = κ),
    h15PostFEOrderedPairSummand n r t p

/-- The ordered off-diagonal collected exactly by its two residue keys. -/
theorem h15OrientationZeroFrequencyOffDiagonal_eq_residuePairCollected
    (n g U Q r : ℕ) (t : ℝ) :
    h15OrientationZeroFrequencyOffDiagonal n g U Q r t =
      ∑ κ ∈ h15PostFEOrderedPairResidueSupport n g U Q,
        h15PostFEOrderedPairResidueCoefficient n g U Q r t κ := by
  rw [h15OrientationZeroFrequencyOffDiagonal_eq_orderedPairSum]
  have hcollect := sum_mul_kernel_eq_sum_image_collected
    (h15PostFEOrderedLaurentPairIndices n g U Q)
    h15PostFEOrderedPairResidueKey
    (h15PostFEOrderedPairSummand n r t)
    (fun _κ : (ℕ × ℕ) × (ℕ × ℕ) => (1 : ℝ))
  simpa [h15PostFEOrderedPairResidueSupport,
    h15PostFEOrderedPairResidueCoefficient] using hcollect

/-- Every orientation-zero Laurent row residue key occurs in the actual
post-FE residue support. -/
theorem h15PostFEOrientationZeroRowResidueKey_mem
    {n g U Q : ℕ}
    {i : H15LaurentRowIndex (NB8.logTaperLength n)}
    (hi : i ∈ h15DoublyLocalizedOrientationZeroIndices
      (NB8.logTaperLength n) g U Q) :
    h15PostFEOrientationZeroRowResidueKey i ∈
      h15PostFEResidueSupport n g U Q := by
  classical
  rw [h15PostFEResidueSupport, Finset.mem_image]
  refine ⟨h15OrientationZeroLaurentRowKey i, ?_, rfl⟩
  apply Finset.mem_union_right
  rw [h15LaurentCollectedKeySupport, Finset.mem_image]
  exact ⟨i, hi, rfl⟩

/-- Both coordinates of every collected ordered-pair key lie in the actual
post-FE residue support. -/
theorem h15PostFEOrderedPairResidueSupport_subset_actual
    {n g U Q : ℕ} {κ : (ℕ × ℕ) × (ℕ × ℕ)}
    (hκ : κ ∈ h15PostFEOrderedPairResidueSupport n g U Q) :
    κ.1 ∈ h15PostFEResidueSupport n g U Q ∧
      κ.2 ∈ h15PostFEResidueSupport n g U Q := by
  classical
  rw [h15PostFEOrderedPairResidueSupport, Finset.mem_image] at hκ
  rcases hκ with ⟨p, hp, rfl⟩
  have hp' := Finset.mem_sigma.mp hp
  exact ⟨h15PostFEOrientationZeroRowResidueKey_mem hp'.1,
    h15PostFEOrientationZeroRowResidueKey_mem
      (Finset.mem_erase.mp hp'.2).2⟩

/-- An actually occurring residue key cannot simultaneously be a missing
residue for its own modulus. -/
theorem h15PostFEResidueSupport_not_mem_missing
    {n g U Q : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ h15PostFEResidueSupport n g U Q) :
    z.1 ∉ h15PostFEMissingResidues n g U Q z.2 := by
  classical
  intro hmissing
  have hnot := (Finset.mem_sdiff.mp hmissing).2
  apply hnot
  rw [h15PostFEResidueFiberResidues, Finset.mem_image]
  refine ⟨z, Finset.mem_filter.mpr ⟨hz, rfl⟩, rfl⟩

/-- Support-level stop test: neither residue coordinate in the ordered
cross-row dispersion belongs to the missing-residue support. -/
theorem h15PostFEOrderedPairResidueSupport_disjoint_missing
    {n g U Q : ℕ} {κ : (ℕ × ℕ) × (ℕ × ℕ)}
    (hκ : κ ∈ h15PostFEOrderedPairResidueSupport n g U Q) :
    κ.1.1 ∉ h15PostFEMissingResidues n g U Q κ.1.2 ∧
      κ.2.1 ∉ h15PostFEMissingResidues n g U Q κ.2.2 := by
  have hactual := h15PostFEOrderedPairResidueSupport_subset_actual hκ
  exact ⟨h15PostFEResidueSupport_not_mem_missing hactual.1,
    h15PostFEResidueSupport_not_mem_missing hactual.2⟩

/-- Fully residue-aligned canonical frontier.  The missing-residue term is
linear and supported off the actual fibers; the ordered dispersion is a sum
over actual-actual residue pairs. -/
theorem h15PostFECenteredLiftDefect_eq_meanZero_sub_missing_sub_pairDispersion
    (n g U Q r : ℕ) (t : ℝ)
    (hQ : 0 < Q) (hS : h15PairedHyperbolicCoefficient t ≠ 0) :
    h15PostFECenteredLiftDefect n g U Q r t =
      h15PostFEResidueMeanZeroVariation n g U Q r t -
        (∑ q ∈ h15PostFEResidueModulusSupport n g U Q,
          h15PostFEResidueFiberMeanCoefficient n g U Q r t q *
            ∑ a ∈ h15PostFEMissingResidues n g U Q q,
              h15PairedDirectCrossMode r a q) -
        4 *
          (∑ κ ∈ h15PostFEOrderedPairResidueSupport n g U Q,
            h15PostFEOrderedPairResidueCoefficient n g U Q r t κ) /
          (2 * h15PairedHyperbolicCoefficient t) := by
  rw [h15PostFECenteredLiftDefect_eq_meanZero_sub_missing_sub_dispersion
      n g U Q r t hQ hS,
    h15OrientationZeroFrequencyOffDiagonal_eq_residuePairCollected]

end NBMellinTools.NB12
