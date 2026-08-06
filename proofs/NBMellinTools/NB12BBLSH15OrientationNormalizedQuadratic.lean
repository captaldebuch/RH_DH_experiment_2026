/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15TransposeInvariant
import NBMellinTools.NB12BBLSH15LocalizedQuadraticProjection

/-!
# NB12zzzc: raw-block and post-functional-equation orientation normalization

Both H15 orientations are literally identical after transposing the two
primitive dyadic scales.  A complete *raw* `(g,U,Q)` Laurent-frequency slice
therefore consists of orientation-zero blocks on `(U,Q)` and `(Q,U)`.

For comparison with an endpoint block whose post-functional-equation inverse
scale is `U` and modulus scale is `Q`, however, the correct row set is

`orientation zero on (U,Q) ∪ orientation one on (Q,U)`.

That endpoint-aligned set is exactly two copies of the orientation-zero
`(U,Q)` block.  Both identities are recorded below so that raw-coordinate and
post-functional-equation localization cannot be conflated.

No asymptotic estimate is asserted.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate
open Complex

namespace NBMellinTools.NB12

/-- One transformed-frequency slice on the full doubly localized raw block. -/
noncomputable def h15DoublyLocalizedDirectAdditiveFrequencySlice
    (n g U Q r : ℕ) (t : ℝ) : ℂ :=
  ∑ i ∈ h15DoublyLocalizedLaurentRowIndices
      (NB8.logTaperLength n) g U Q,
    h15DirectAdditiveFixedHeightSummand (NB8.logTaperLength n)
      (h15ContourDamping n) (i, r) t

/-- The orientation-zero half of the same transformed-frequency slice. -/
noncomputable def h15OrientationZeroDirectAdditiveFrequencySlice
    (n g U Q r : ℕ) (t : ℝ) : ℂ :=
  ∑ i ∈ h15DoublyLocalizedOrientationZeroIndices
      (NB8.logTaperLength n) g U Q,
    h15DirectAdditiveFixedHeightSummand (NB8.logTaperLength n)
      (h15ContourDamping n) (i, r) t

/-- First split the doubly localized slice into its two disjoint raw
orientations. -/
theorem h15DoublyLocalizedDirectAdditiveFrequencySlice_eq_orientation_sum
    (n g U Q r : ℕ) (t : ℝ) :
    h15DoublyLocalizedDirectAdditiveFrequencySlice n g U Q r t =
      h15OrientationZeroDirectAdditiveFrequencySlice n g U Q r t +
        ∑ i ∈ h15DoublyLocalizedOrientationOneIndices
            (NB8.logTaperLength n) g U Q,
          h15DirectAdditiveFixedHeightSummand (NB8.logTaperLength n)
            (h15ContourDamping n) (i, r) t := by
  unfold h15DoublyLocalizedDirectAdditiveFrequencySlice
    h15OrientationZeroDirectAdditiveFrequencySlice
  rw [h15DoublyLocalizedLaurentRowIndices_eq_orientation_union,
    Finset.sum_union
      (h15DoublyLocalizedOrientation_disjoint
        (NB8.logTaperLength n) g U Q)]

/-- Exact orientation normalization: the complete `(U,Q)` slice is the sum
of orientation-zero slices on `(U,Q)` and on the swapped block `(Q,U)`. -/
theorem h15DoublyLocalizedDirectAdditiveFrequencySlice_eq_zero_add_swapped
    (n g U Q r : ℕ) (t : ℝ) :
    h15DoublyLocalizedDirectAdditiveFrequencySlice n g U Q r t =
      h15OrientationZeroDirectAdditiveFrequencySlice n g U Q r t +
        h15OrientationZeroDirectAdditiveFrequencySlice n g Q U r t := by
  rw [h15DoublyLocalizedDirectAdditiveFrequencySlice_eq_orientation_sum]
  congr 1
  exact sum_orientationOne_directAdditive_eq_orientationZero_swapped
    (N := NB8.logTaperLength n) (g := g) (U := U) (Q := Q)
    (h15ContourDamping n) r t

/-- Signed interaction between the two orientation-normalized dyadic
blocks.  It is kept intact rather than bounded by absolute values. -/
noncomputable def h15OrientationNormalizedCrossScale
    (n g U Q r : ℕ) (t : ℝ) : ℝ :=
  2 * (h15OrientationZeroDirectAdditiveFrequencySlice n g U Q r t *
    conj (h15OrientationZeroDirectAdditiveFrequencySlice n g Q U r t)).re

/-- Canonical quadratic expansion after orientation normalization. -/
theorem normSq_h15DoublyLocalizedDirectAdditiveFrequencySlice
    (n g U Q r : ℕ) (t : ℝ) :
    Complex.normSq
        (h15DoublyLocalizedDirectAdditiveFrequencySlice n g U Q r t) =
      Complex.normSq
          (h15OrientationZeroDirectAdditiveFrequencySlice n g U Q r t) +
        Complex.normSq
          (h15OrientationZeroDirectAdditiveFrequencySlice n g Q U r t) +
        h15OrientationNormalizedCrossScale n g U Q r t := by
  rw [h15DoublyLocalizedDirectAdditiveFrequencySlice_eq_zero_add_swapped,
    Complex.normSq_add]
  rfl

/-! ## Endpoint-aligned post-functional-equation block -/

/-- Rows whose *post-functional-equation* inverse coordinate is in the `U`
block and modulus is in the `Q` block.  Orientation one therefore uses the
swapped raw block `(Q,U)`. -/
def h15PostFELocalizedLaurentRowIndices
    (N g U Q : ℕ) : Finset (H15LaurentRowIndex N) :=
  h15DoublyLocalizedOrientationZeroIndices N g U Q ∪
    h15DoublyLocalizedOrientationOneIndices N g Q U

theorem h15PostFELocalizedLaurentRowIndices_disjoint
    (N g U Q : ℕ) :
    Disjoint (h15DoublyLocalizedOrientationZeroIndices N g U Q)
      (h15DoublyLocalizedOrientationOneIndices N g Q U) := by
  rw [Finset.disjoint_left]
  intro i hzero hone
  have hz := (mem_h15DoublyLocalizedOrientationZeroIndices.mp hzero).2
  have ho := (mem_h15DoublyLocalizedOrientationOneIndices.mp hone).2
  omega

/-- Every endpoint-aligned row has inverse scale `U` and modulus scale `Q`,
independently of its raw orientation. -/
theorem h15PostFELocalizedLaurentRow_postFE_support
    {N g U Q : ℕ} {i : H15LaurentRowIndex N}
    (hi : i ∈ h15PostFELocalizedLaurentRowIndices N g U Q) :
    h15BettinChandeeInverseVariable i ∈
        h15BettinChandeeSupportedNatBlock N g U ∧
      h15BettinChandeeModulusVariable i ∈
        h15BettinChandeeSupportedNatBlock N g Q := by
  rcases Finset.mem_union.mp hi with hzero | hone
  · exact h15DoublyLocalized_orientation_zero_postFE_support hzero
  · exact h15DoublyLocalized_orientation_one_postFE_support hone

/-- Direct-additive frequency slice on the genuinely endpoint-aligned post-FE
block. -/
noncomputable def h15PostFELocalizedDirectAdditiveFrequencySlice
    (n g U Q r : ℕ) (t : ℝ) : ℂ :=
  ∑ i ∈ h15PostFELocalizedLaurentRowIndices
      (NB8.logTaperLength n) g U Q,
    h15DirectAdditiveFixedHeightSummand (NB8.logTaperLength n)
      (h15ContourDamping n) (i, r) t

/-- The endpoint-aligned slice is exactly twice the canonical
orientation-zero `(U,Q)` slice. -/
theorem h15PostFELocalizedDirectAdditiveFrequencySlice_eq_two_mul
    (n g U Q r : ℕ) (t : ℝ) :
    h15PostFELocalizedDirectAdditiveFrequencySlice n g U Q r t =
      2 * h15OrientationZeroDirectAdditiveFrequencySlice n g U Q r t := by
  unfold h15PostFELocalizedDirectAdditiveFrequencySlice
    h15PostFELocalizedLaurentRowIndices
  rw [Finset.sum_union
    (h15PostFELocalizedLaurentRowIndices_disjoint
      (NB8.logTaperLength n) g U Q)]
  change h15OrientationZeroDirectAdditiveFrequencySlice n g U Q r t + _ = _
  rw [sum_orientationOne_directAdditive_eq_orientationZero_swapped
    (N := NB8.logTaperLength n) (g := g) (U := Q) (Q := U)
    (h15ContourDamping n) r t]
  change h15OrientationZeroDirectAdditiveFrequencySlice n g U Q r t +
    h15OrientationZeroDirectAdditiveFrequencySlice n g U Q r t = _
  ring

theorem normSq_h15PostFELocalizedDirectAdditiveFrequencySlice
    (n g U Q r : ℕ) (t : ℝ) :
    Complex.normSq
        (h15PostFELocalizedDirectAdditiveFrequencySlice n g U Q r t) =
      4 * Complex.normSq
        (h15OrientationZeroDirectAdditiveFrequencySlice n g U Q r t) := by
  rw [h15PostFELocalizedDirectAdditiveFrequencySlice_eq_two_mul,
    Complex.normSq_mul]
  norm_num

/-! ## Canonical two-scale endpoint projection defect -/

/-- The endpoint spectral aggregate minus the genuinely endpoint-aligned
post-functional-equation quadratic contour slice. -/
noncomputable def h15OrientationNormalizedQuadraticLiftDefect
    (n g U Q r : ℕ) (t : ℝ) : ℝ :=
  h15NormalizedBoundarySpectralAggregate
      (NB8.logTaperLength n) g r U Q t -
    Complex.normSq
      (h15PostFELocalizedDirectAdditiveFrequencySlice n g U Q r t)

/-- The canonical fixed-height endpoint ledger after the orientation audit.
The only unnamed analytic content is now the two-scale lift defect; the
signed cross-scale interaction remains inside the exact expression. -/
theorem h15NormalizedBoundaryFourierAggregate_eq_orientationNormalizedLedger
    (n g U Q r : ℕ) (t : ℝ) (hQ : 0 < Q)
    (hS : h15PairedHyperbolicCoefficient t ≠ 0) :
    h15NormalizedBoundaryFourierAggregate
        (NB8.logTaperLength n) g r U Q =
      4 * Complex.normSq
          (h15OrientationZeroDirectAdditiveFrequencySlice n g U Q r t) +
        h15OrientationNormalizedQuadraticLiftDefect n g U Q r t := by
  rw [← h15NormalizedBoundarySpectralAggregate_eq_fourierAggregate
    (NB8.logTaperLength n) g r U Q t hQ hS]
  unfold h15OrientationNormalizedQuadraticLiftDefect
  rw [normSq_h15PostFELocalizedDirectAdditiveFrequencySlice]
  ring

end NBMellinTools.NB12
