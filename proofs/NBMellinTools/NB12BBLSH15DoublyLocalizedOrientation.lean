/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15LocalizedFrequencySplit

/-!
# NB12zzza: doubly localized H15 rows and the orientation swap

The one-dimensional Laurent localization fixes the raw primitive coordinate
`q`.  After the Estermann functional equation this is the modulus only in
orientation zero; in orientation one it is the inverted coordinate.  Thus a
single `(g,Q)` block is not, by itself, a post-functional-equation modulus
block.

This file adds the missing primitive-`a` scale `U` and proves the exact
orientation audit.  On orientation zero the Bettin--Chandee inverse/modulus
scales are `(U,Q)`, while on orientation one they are `(Q,U)`.  These are
finite support identities only: no cancellation estimate and no identification
with the endpoint boundary is asserted.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius

namespace NBMellinTools.NB12

/-- Raw Laurent rows localized simultaneously in the gcd slice, primitive
`a` block `[U,2U)`, and primitive `q` block `[Q,2Q)`. -/
def h15DoublyLocalizedLaurentRowIndices
    (N g U Q : ℕ) : Finset (H15LaurentRowIndex N) :=
  (h15LocalizedLaurentRowIndices N g Q).filter fun i =>
    h15LaurentA i ∈ h15BettinChandeeSupportedNatBlock N g U

theorem mem_h15DoublyLocalizedLaurentRowIndices
    {N g U Q : ℕ} {i : H15LaurentRowIndex N} :
    i ∈ h15DoublyLocalizedLaurentRowIndices N g U Q ↔
      h15LaurentG i = g ∧
        h15LaurentA i ∈ h15BettinChandeeSupportedNatBlock N g U ∧
        h15LaurentQ i ∈ h15BettinChandeeSupportedNatBlock N g Q := by
  simp only [h15DoublyLocalizedLaurentRowIndices, Finset.mem_filter,
    mem_h15LocalizedLaurentRowIndices]
  aesop

theorem h15DoublyLocalizedLaurentRowIndices_subset_localized
    (N g U Q : ℕ) :
    h15DoublyLocalizedLaurentRowIndices N g U Q ⊆
      h15LocalizedLaurentRowIndices N g Q := by
  intro i hi
  exact (Finset.mem_filter.mp hi).1

/-- Exact raw-coordinate bounds on a doubly localized row. -/
theorem h15DoublyLocalizedLaurentRow_bounds
    {N g U Q : ℕ} {i : H15LaurentRowIndex N}
    (hi : i ∈ h15DoublyLocalizedLaurentRowIndices N g U Q) :
    h15LaurentG i = g ∧
      U ≤ h15LaurentA i ∧ h15LaurentA i < 2 * U ∧
        g * h15LaurentA i ≤ N ∧
      Q ≤ h15LaurentQ i ∧ h15LaurentQ i < 2 * Q ∧
        g * h15LaurentQ i ≤ N := by
  have hmem := mem_h15DoublyLocalizedLaurentRowIndices.mp hi
  have ha := mem_h15BettinChandeeSupportedNatBlock.mp hmem.2.1
  have hq := mem_h15BettinChandeeSupportedNatBlock.mp hmem.2.2
  exact ⟨hmem.1, ha.1, ha.2.1, ha.2.2, hq.1, hq.2.1, hq.2.2⟩

/-- The orientation-zero half of one doubly localized primitive block. -/
def h15DoublyLocalizedOrientationZeroIndices
    (N g U Q : ℕ) : Finset (H15LaurentRowIndex N) :=
  (h15DoublyLocalizedLaurentRowIndices N g U Q).filter fun i =>
    h15LaurentOrientation i = 0

/-- The orientation-one half of one doubly localized primitive block. -/
def h15DoublyLocalizedOrientationOneIndices
    (N g U Q : ℕ) : Finset (H15LaurentRowIndex N) :=
  (h15DoublyLocalizedLaurentRowIndices N g U Q).filter fun i =>
    h15LaurentOrientation i = 1

theorem mem_h15DoublyLocalizedOrientationZeroIndices
    {N g U Q : ℕ} {i : H15LaurentRowIndex N} :
    i ∈ h15DoublyLocalizedOrientationZeroIndices N g U Q ↔
      i ∈ h15DoublyLocalizedLaurentRowIndices N g U Q ∧
        h15LaurentOrientation i = 0 := by
  simp [h15DoublyLocalizedOrientationZeroIndices]

theorem mem_h15DoublyLocalizedOrientationOneIndices
    {N g U Q : ℕ} {i : H15LaurentRowIndex N} :
    i ∈ h15DoublyLocalizedOrientationOneIndices N g U Q ↔
      i ∈ h15DoublyLocalizedLaurentRowIndices N g U Q ∧
        h15LaurentOrientation i = 1 := by
  simp [h15DoublyLocalizedOrientationOneIndices]

/-- The two orientations form an exact partition of every doubly localized
raw block. -/
theorem h15DoublyLocalizedLaurentRowIndices_eq_orientation_union
    (N g U Q : ℕ) :
    h15DoublyLocalizedLaurentRowIndices N g U Q =
      h15DoublyLocalizedOrientationZeroIndices N g U Q ∪
        h15DoublyLocalizedOrientationOneIndices N g U Q := by
  ext i
  simp only [mem_h15DoublyLocalizedLaurentRowIndices,
    mem_h15DoublyLocalizedOrientationZeroIndices,
    mem_h15DoublyLocalizedOrientationOneIndices, Finset.mem_union]
  constructor
  · intro hi
    rcases h15LaurentOrientation_eq_zero_or_one i with hzero | hone
    · exact Or.inl ⟨hi, hzero⟩
    · exact Or.inr ⟨hi, hone⟩
  · rintro (hi | hi) <;> exact hi.1

theorem h15DoublyLocalizedOrientation_disjoint
    (N g U Q : ℕ) :
    Disjoint (h15DoublyLocalizedOrientationZeroIndices N g U Q)
      (h15DoublyLocalizedOrientationOneIndices N g U Q) := by
  rw [Finset.disjoint_left]
  intro i hzero hone
  have hz := (mem_h15DoublyLocalizedOrientationZeroIndices.mp hzero).2
  have ho := (mem_h15DoublyLocalizedOrientationOneIndices.mp hone).2
  omega

/-- In orientation zero, the raw `(a,q)` scales remain the post-functional-
equation `(inverse,modulus)` scales `(U,Q)`. -/
theorem h15DoublyLocalized_orientation_zero_postFE_support
    {N g U Q : ℕ} {i : H15LaurentRowIndex N}
    (hi : i ∈ h15DoublyLocalizedOrientationZeroIndices N g U Q) :
    h15BettinChandeeInverseVariable i ∈
        h15BettinChandeeSupportedNatBlock N g U ∧
      h15BettinChandeeModulusVariable i ∈
        h15BettinChandeeSupportedNatBlock N g Q := by
  have hmem := mem_h15DoublyLocalizedOrientationZeroIndices.mp hi
  have hraw := mem_h15DoublyLocalizedLaurentRowIndices.mp hmem.1
  simpa [h15BettinChandeeInverseVariable,
    h15BettinChandeeModulusVariable, hmem.2] using
      And.intro hraw.2.1 hraw.2.2

/-- In orientation one, the functional equation swaps the two primitive
scales: `(inverse,modulus) = (Q,U)`. -/
theorem h15DoublyLocalized_orientation_one_postFE_support
    {N g U Q : ℕ} {i : H15LaurentRowIndex N}
    (hi : i ∈ h15DoublyLocalizedOrientationOneIndices N g U Q) :
    h15BettinChandeeInverseVariable i ∈
        h15BettinChandeeSupportedNatBlock N g Q ∧
      h15BettinChandeeModulusVariable i ∈
        h15BettinChandeeSupportedNatBlock N g U := by
  have hmem := mem_h15DoublyLocalizedOrientationOneIndices.mp hi
  have hraw := mem_h15DoublyLocalizedLaurentRowIndices.mp hmem.1
  have hne : h15LaurentOrientation i ≠ 0 := by omega
  simpa [h15BettinChandeeInverseVariable,
    h15BettinChandeeModulusVariable, hne] using
      And.intro hraw.2.2 hraw.2.1

/-- The one-dimensional `(g,Q)` localization genuinely fixes the post-FE
modulus in orientation zero. -/
theorem h15Localized_orientation_zero_modulus_support
    {N g Q : ℕ} {i : H15LaurentRowIndex N}
    (hi : i ∈ h15LocalizedLaurentRowIndices N g Q)
    (hzero : h15LaurentOrientation i = 0) :
    h15BettinChandeeModulusVariable i ∈
      h15BettinChandeeSupportedNatBlock N g Q := by
  simpa [h15BettinChandeeModulusVariable, hzero] using
    (mem_h15LocalizedLaurentRowIndices.mp hi).2

/-- In orientation one the same one-dimensional `(g,Q)` localization fixes
the post-FE inverse variable, not the modulus. -/
theorem h15Localized_orientation_one_inverse_support
    {N g Q : ℕ} {i : H15LaurentRowIndex N}
    (hi : i ∈ h15LocalizedLaurentRowIndices N g Q)
    (hone : h15LaurentOrientation i = 1) :
    h15BettinChandeeInverseVariable i ∈
      h15BettinChandeeSupportedNatBlock N g Q := by
  have hne : h15LaurentOrientation i ≠ 0 := by omega
  simpa [h15BettinChandeeInverseVariable, hne] using
    (mem_h15LocalizedLaurentRowIndices.mp hi).2

/-! ## Canonical transpose of the two orientations -/

/-- Swap the two primitive coordinates and toggle the orientation.  This is
the exact finite symmetry which turns an orientation-one `(U,Q)` block into
an orientation-zero `(Q,U)` block. -/
def h15LaurentTranspose {N : ℕ}
    (i : H15LaurentRowIndex N) : H15LaurentRowIndex N :=
  (i.1, i.2.2.1, i.2.1,
    ⟨1 - i.2.2.2.val, by have := i.2.2.2.isLt; omega⟩)

@[simp] theorem h15LaurentG_transpose {N : ℕ}
    (i : H15LaurentRowIndex N) :
    h15LaurentG (h15LaurentTranspose i) = h15LaurentG i := by
  rfl

@[simp] theorem h15LaurentA_transpose {N : ℕ}
    (i : H15LaurentRowIndex N) :
    h15LaurentA (h15LaurentTranspose i) = h15LaurentQ i := by
  rfl

@[simp] theorem h15LaurentQ_transpose {N : ℕ}
    (i : H15LaurentRowIndex N) :
    h15LaurentQ (h15LaurentTranspose i) = h15LaurentA i := by
  rfl

@[simp] theorem h15LaurentOrientation_transpose {N : ℕ}
    (i : H15LaurentRowIndex N) :
    h15LaurentOrientation (h15LaurentTranspose i) =
      1 - h15LaurentOrientation i := by
  rfl

@[simp] theorem h15LaurentTranspose_involutive {N : ℕ}
    (i : H15LaurentRowIndex N) :
    h15LaurentTranspose (h15LaurentTranspose i) = i := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Fin.ext
        change 1 - (1 - i.2.2.2.val) = i.2.2.2.val
        have hi := i.2.2.2.isLt
        omega

theorem h15LaurentTranspose_injective {N : ℕ} :
    Function.Injective
      (h15LaurentTranspose : H15LaurentRowIndex N → H15LaurentRowIndex N) := by
  intro i j hij
  simpa only [h15LaurentTranspose_involutive] using
    congrArg h15LaurentTranspose hij

/-- The transpose as a finite embedding, used for exact reindexing. -/
def h15LaurentTransposeEmbedding (N : ℕ) :
    H15LaurentRowIndex N ↪ H15LaurentRowIndex N where
  toFun := h15LaurentTranspose
  inj' := h15LaurentTranspose_injective

/-- Transposition swaps the two raw dyadic blocks exactly. -/
theorem h15LaurentTranspose_mem_doublyLocalized_iff
    {N g U Q : ℕ} {i : H15LaurentRowIndex N} :
    h15LaurentTranspose i ∈ h15DoublyLocalizedLaurentRowIndices N g Q U ↔
      i ∈ h15DoublyLocalizedLaurentRowIndices N g U Q := by
  simp only [mem_h15DoublyLocalizedLaurentRowIndices,
    h15LaurentG_transpose, h15LaurentA_transpose, h15LaurentQ_transpose]
  aesop

/-- Orientation one on `(U,Q)` is canonically orientation zero on the
transposed `(Q,U)` block. -/
theorem h15LaurentTranspose_mem_orientationZero_iff_orientationOne
    {N g U Q : ℕ} {i : H15LaurentRowIndex N} :
    h15LaurentTranspose i ∈
        h15DoublyLocalizedOrientationZeroIndices N g Q U ↔
      i ∈ h15DoublyLocalizedOrientationOneIndices N g U Q := by
  rw [mem_h15DoublyLocalizedOrientationZeroIndices,
    h15LaurentTranspose_mem_doublyLocalized_iff,
    mem_h15DoublyLocalizedOrientationOneIndices]
  constructor
  · rintro ⟨hi, horient⟩
    refine ⟨hi, ?_⟩
    rw [h15LaurentOrientation_transpose] at horient
    rcases h15LaurentOrientation_eq_zero_or_one i with hzero | hone
    · omega
    · exact hone
  · rintro ⟨hi, hone⟩
    refine ⟨hi, ?_⟩
    rw [h15LaurentOrientation_transpose, hone]

/-- Orientation zero on `(U,Q)` is canonically orientation one on the
transposed `(Q,U)` block. -/
theorem h15LaurentTranspose_mem_orientationOne_iff_orientationZero
    {N g U Q : ℕ} {i : H15LaurentRowIndex N} :
    h15LaurentTranspose i ∈
        h15DoublyLocalizedOrientationOneIndices N g Q U ↔
      i ∈ h15DoublyLocalizedOrientationZeroIndices N g U Q := by
  rw [mem_h15DoublyLocalizedOrientationOneIndices,
    h15LaurentTranspose_mem_doublyLocalized_iff,
    mem_h15DoublyLocalizedOrientationZeroIndices]
  constructor
  · rintro ⟨hi, horient⟩
    refine ⟨hi, ?_⟩
    rw [h15LaurentOrientation_transpose] at horient
    rcases h15LaurentOrientation_eq_zero_or_one i with hzero | hone
    · exact hzero
    · omega
  · rintro ⟨hi, hzero⟩
    refine ⟨hi, ?_⟩
    rw [h15LaurentOrientation_transpose, hzero]

/-- Exact image identity for the orientation swap. -/
theorem map_h15DoublyLocalizedOrientationOne_transpose
    (N g U Q : ℕ) :
    (h15DoublyLocalizedOrientationOneIndices N g U Q).map
        (h15LaurentTransposeEmbedding N) =
      h15DoublyLocalizedOrientationZeroIndices N g Q U := by
  ext i
  constructor
  · intro hi
    rw [Finset.mem_map] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    exact h15LaurentTranspose_mem_orientationZero_iff_orientationOne.mpr hj
  · intro hi
    rw [Finset.mem_map]
    refine ⟨h15LaurentTranspose i, ?_, ?_⟩
    · exact h15LaurentTranspose_mem_orientationOne_iff_orientationZero.mpr hi
    · exact h15LaurentTranspose_involutive i

/-- Any finite sum on orientation one can be reindexed exactly as an
orientation-zero sum on the transposed dyadic block. -/
theorem sum_orientationOne_comp_transpose_eq_sum_orientationZero
    {N g U Q : ℕ} {R : Type*} [AddCommMonoid R]
    (f : H15LaurentRowIndex N → R) :
    ∑ i ∈ h15DoublyLocalizedOrientationOneIndices N g U Q,
        f (h15LaurentTranspose i) =
      ∑ i ∈ h15DoublyLocalizedOrientationZeroIndices N g Q U, f i := by
  rw [← map_h15DoublyLocalizedOrientationOne_transpose N g U Q]
  exact (Finset.sum_map
    (h15DoublyLocalizedOrientationOneIndices N g U Q)
    (h15LaurentTransposeEmbedding N) f).symm

end NBMellinTools.NB12
