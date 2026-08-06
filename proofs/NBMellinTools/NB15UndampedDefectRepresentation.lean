/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB15TwoVariableBridgeAudit
import NBMellinTools.NB15GlobalPostFEAssembly
import NBMellinTools.NB12BBLSH15FrequencyTailRate

/-!
# Complete linear representation of the undamped PostFE frontier

The functional equation acts on the **linear** signed Estermann aggregate.
The object `h15GlobalPostFEJointCorrectionTransform`, on the other hand, is
a fixed-frequency, fixed-height quadratic projection.  These two objects
must not be identified.

This file assembles the complete linear right edge from

* every canonical dyadic block in each low-frequency slice;
* every low frequency up to an arbitrary cutoff;
* the genuine infinite complementary frequency tail; and
* the complete first-order/additional-residue ledger.

It then inserts that complete transform into the certified energy identity.
The old undamped PostFE bridge defect splits exactly into two independently
visible terms:

1. an endpoint-to-linear-contour defect; and
2. a linear-to-quadratic PostFE mismatch.

Thus a proof that the old defect vanishes cannot be obtained merely by
renaming the quadratic transform as the contour image.  No decay estimate is
asserted here.
-/

open scoped BigOperators ComplexConjugate Interval

namespace NBMellinTools.NB15

open Complex MeasureTheory
open NBMellinTools.NB8
open NBMellinTools.NB12

/-! ## Complete linear PostFE aggregate -/

/-- The complete functional-equation aggregate at height `t`: the globally
assembled finite low-frequency sector plus its genuine infinite tail. -/
noncomputable def h15CompleteLinearPostFEAggregate
    (n K : ℕ) (t : ℝ) : ℂ :=
  (∑ r ∈ Finset.range (K + 1),
      h15GlobalPostFELinearFrequencySlice n r t) +
    h15ThreeHalfHighFrequencyAggregate n K t

/-- The complete linear PostFE aggregate is exactly the original active H15
aggregate on the three-halves line.  In particular, the dyadic assembly and
frequency split omit no row and no frequency. -/
theorem h15CompleteLinearPostFEAggregate_eq_verticalAggregate
    (n K : ℕ) (t : ℝ) :
    h15CompleteLinearPostFEAggregate n K t =
      h15VerticalAggregate n (3 / 2) t := by
  unfold h15CompleteLinearPostFEAggregate
  rw [← h15ThreeHalfLowFrequencyAggregate_eq_globalPostFESlices]
  exact (h15VerticalAggregate_threeHalf_eq_low_add_high n K t).symm

/-- The low-frequency interval integral can be written literally as the
integral of all globally assembled dyadic frequency slices. -/
theorem h15ThreeHalfLowFrequencyIntegral_eq_globalPostFESlices
    (n K : ℕ) (T : ℝ) :
    h15ThreeHalfLowFrequencyIntegral n K T =
      ∫ t : ℝ in -T..T,
        ∑ r ∈ Finset.range (K + 1),
          h15GlobalPostFELinearFrequencySlice n r t := by
  unfold h15ThreeHalfLowFrequencyIntegral
  congr 1
  funext t
  exact h15ThreeHalfLowFrequencyAggregate_eq_globalPostFESlices n K t

/-! ## Correction-preserving complete right edge -/

/-- The complete linear PostFE right edge.  The residue ledger remains
attached to the low sector, while the high sector is the genuine infinite
frequency tail. -/
noncomputable def h15CompleteLinearPostFERightEdge
    (n K : ℕ) (T : ℝ) : ℂ :=
  (I * (∫ t : ℝ in -T..T,
      ∑ r ∈ Finset.range (K + 1),
        h15GlobalPostFELinearFrequencySlice n r t) -
    2 * Real.pi * I * h15ContourResidueLedger n) +
    h15HighFrequencyRightEdgeRemainder n K T

/-- Exact completeness: the global linear PostFE construction is the
certified correction-preserving right edge, independently of the cutoff. -/
theorem h15CompleteLinearPostFERightEdge_eq_correctedRightEdge
    (n K : ℕ) (T : ℝ) :
    h15CompleteLinearPostFERightEdge n K T =
      h15CorrectedThreeHalfRightEdge n T := by
  unfold h15CompleteLinearPostFERightEdge
  rw [← h15ThreeHalfLowFrequencyIntegral_eq_globalPostFESlices]
  exact (h15CorrectedThreeHalfRightEdge_eq_low_add_high n K T).symm

/-- Because both sectors together contain every frequency, the complete
linear edge is independent of where the low/high split is made. -/
theorem h15CompleteLinearPostFERightEdge_cutoff_independent
    (n K L : ℕ) (T : ℝ) :
    h15CompleteLinearPostFERightEdge n K T =
      h15CompleteLinearPostFERightEdge n L T := by
  rw [h15CompleteLinearPostFERightEdge_eq_correctedRightEdge,
    h15CompleteLinearPostFERightEdge_eq_correctedRightEdge]

/-- The complete linear transform also has the genuine closed-rectangle
description.  Thus its remaining normalization problem is a left-edge and
horizontal-edge problem, not a missing-frequency problem. -/
theorem h15CompleteLinearPostFERightEdge_eq_left_sub_horizontal
    (n K : ℕ) (σL T : ℝ) (hL : σL < 0) (hT : 0 < T) :
    h15CompleteLinearPostFERightEdge n K T =
      I * h15TruncatedVerticalIntegral n σL T -
        symmetricHorizontalEdges (h15ActiveContourAggregate n)
          σL (3 / 2) T := by
  rw [h15CompleteLinearPostFERightEdge_eq_correctedRightEdge]
  exact h15CorrectedThreeHalfRightEdge_eq_left_sub_horizontal
    n σL T hL hT

/-- Expanded polar ledger.  Both the `s=0` first-order coefficient and the
`s=1` additional residue are retained explicitly.  Higher-order polar data
remain in the active aggregate; they are not falsely counted as contour
residues. -/
theorem h15CompleteLinearPostFERightEdge_eq_expandedResidueLedger
    (n K : ℕ) (T : ℝ) :
    h15CompleteLinearPostFERightEdge n K T =
      I * (∫ t : ℝ in -T..T,
        ∑ r ∈ Finset.range (K + 1),
          h15GlobalPostFELinearFrequencySlice n r t) -
        2 * Real.pi * I * h15GlobalFirstOrderCoefficient n -
        2 * Real.pi * I * h15GlobalAdditionalResidue n +
        h15HighFrequencyRightEdgeRemainder n K T := by
  unfold h15CompleteLinearPostFERightEdge h15ContourResidueLedger
  ring

/-- Stop test for dropping the correction: the difference between the
complete edge and the uncorrected all-frequency transform is exactly the
full residue ledger, with its contour normalization. -/
theorem h15CompleteLinearPostFERightEdge_sub_uncorrected
    (n K : ℕ) (T : ℝ) :
    h15CompleteLinearPostFERightEdge n K T -
        (I * (∫ t : ℝ in -T..T,
          ∑ r ∈ Finset.range (K + 1),
            h15GlobalPostFELinearFrequencySlice n r t) +
          h15HighFrequencyRightEdgeRemainder n K T) =
      -(2 * Real.pi * I * h15ContourResidueLedger n) := by
  unfold h15CompleteLinearPostFERightEdge
  ring

/-! ## The honest two-defect decomposition -/

/-- What remains between the undamped endpoint amplitude occurring in the
certified energy and the complete linear contour transform. -/
noncomputable def h15EndpointToLinearPostFEDefect
    (n K : ℕ) (T : ℝ) : ℝ :=
  (h15AdditionalResidueAmplitude n).im -
    (h15CompleteLinearPostFERightEdge n K T).im

/-- The separate mismatch between the complete linear contour transform and
the fixed-frequency, fixed-height quadratic PostFE projection. -/
noncomputable def h15LinearToQuadraticPostFEMismatch
    (n K r : ℕ) (T t : ℝ) : ℝ :=
  (h15CompleteLinearPostFERightEdge n K T).im -
    h15GlobalPostFEJointCorrectionTransform n r t

/-- Exact decomposition of the old bridge defect.  It displays rather than
hides the change of mathematical level from a linear contour transform to a
quadratic fixed-height projection. -/
theorem h15UndampedPostFEBridgeDefect_eq_linearDefect_add_mismatch
    (n K r : ℕ) (T t : ℝ) :
    h15UndampedPostFEBridgeDefect n r t =
      h15EndpointToLinearPostFEDefect n K T +
        h15LinearToQuadraticPostFEMismatch n K r T t := by
  unfold h15UndampedPostFEBridgeDefect
    h15EndpointToLinearPostFEDefect
    h15LinearToQuadraticPostFEMismatch
  ring

/-- The inverse adaptive-damping factor is explicit in the endpoint-to-linear
defect.  It is not cancelled by the frequency or dyadic reassembly. -/
theorem h15EndpointToLinearPostFEDefect_eq_rescaledResidue_sub_edge
    (n K : ℕ) (T : ℝ) :
    h15EndpointToLinearPostFEDefect n K T =
      (((h15ContourDamping n : ℂ)⁻¹ *
          h15GlobalAdditionalResidue n).im) -
        (h15CompleteLinearPostFERightEdge n K T).im := by
  unfold h15EndpointToLinearPostFEDefect
  rw [h15ContourDamping_inv_mul_globalAdditionalResidue]

/-- Rectangle form of the endpoint-to-linear defect.  Every PostFE
frequency and block has disappeared into the exact boundary identity; the
remaining issue is the undamped residue versus the left/horizontal edges. -/
theorem h15EndpointToLinearPostFEDefect_eq_residue_sub_boundary
    (n K : ℕ) (σL T : ℝ) (hL : σL < 0) (hT : 0 < T) :
    h15EndpointToLinearPostFEDefect n K T =
      (((h15ContourDamping n : ℂ)⁻¹ *
          h15GlobalAdditionalResidue n).im) -
        (I * h15TruncatedVerticalIntegral n σL T -
          symmetricHorizontalEdges (h15ActiveContourAggregate n)
            σL (3 / 2) T).im := by
  rw [h15EndpointToLinearPostFEDefect_eq_rescaledResidue_sub_edge,
    h15CompleteLinearPostFERightEdge_eq_left_sub_horizontal
      n K σL T hL hT]

/-- The certified Nyman--Beurling energy with the complete linear transform
inserted.  The only new remainder is the endpoint-to-linear contour defect;
no quadratic PostFE object is silently substituted for the linear one. -/
theorem logTaperL2Error_eq_elementaryEndpoint_add_completeLinearPostFE_add_defect
    (n K : ℕ) (T : ℝ) :
    logTaperL2Error n =
      h15CertifiedElementaryEndpointLedger n +
        (h15CompleteLinearPostFERightEdge n K T).im +
        h15EndpointToLinearPostFEDefect n K T := by
  rw [logTaperL2Error_eq_elementaryEndpoint_add_additionalResidueAmplitude_im]
  unfold h15EndpointToLinearPostFEDefect
  ring

end NBMellinTools.NB15
