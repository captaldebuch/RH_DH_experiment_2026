/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB15UndampedDefectRepresentation

/-!
# Exact extraction of the undamped endpoint from the closed H15 boundary

The undamped `s = 1` endpoint is not the corrected right edge.  The closed
rectangle first returns the sum of the two simple residues.  Consequently
one must

1. normalize the complete closed boundary by `2 * pi * I`;
2. subtract the `s = 0` first-order residue; and
3. multiply by the inverse adaptive damping.

This file proves that identity for the literal H15 row family and inserts it
into the certified energy.  It also gives the exact stop test showing the
error made by omitting the first-order subtraction.  No asymptotic boundary
estimate is asserted.
-/

open scoped BigOperators Interval

namespace NBMellinTools.NB15

open Complex
open NBMellinTools.NB8
open NBMellinTools.NB12

/-! ## Normalized complete boundary -/

/-- The residue-normalized closed boundary with right edge `Re(s)=3/2`. -/
noncomputable def h15NormalizedCompleteContourBoundary
    (n : ℕ) (σL T : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ *
    rectangularBoundaryIntegral (h15ActiveContourAggregate n)
      (symmetricLowerCorner σL T) (symmetricUpperCorner (3 / 2) T)

/-- On every admissible finite rectangle, the normalized complete boundary
is exactly the sum of the two simple residues. -/
theorem h15NormalizedCompleteContourBoundary_eq_residueLedger
    (n : ℕ) (σL T : ℝ) (hL : σL < 0) (hT : 0 < T) :
    h15NormalizedCompleteContourBoundary n σL T =
      h15ContourResidueLedger n := by
  unfold h15NormalizedCompleteContourBoundary
  rw [rectangularBoundaryIntegral_h15ActiveContourAggregate
    n σL (3 / 2) T hL (by norm_num) (by norm_num) hT]
  have hfactor : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero))
      I_ne_zero
  rw [← mul_assoc, inv_mul_cancel₀ hfactor, one_mul]

/-- The normalized boundary is independent of the admissible rectangle.
This is useful as a consistency check: changing the auxiliary contour cannot
change the extracted endpoint. -/
theorem h15NormalizedCompleteContourBoundary_independent
    (n : ℕ) (σL σL' T T' : ℝ)
    (hL : σL < 0) (hL' : σL' < 0) (hT : 0 < T) (hT' : 0 < T') :
    h15NormalizedCompleteContourBoundary n σL T =
      h15NormalizedCompleteContourBoundary n σL' T' := by
  rw [h15NormalizedCompleteContourBoundary_eq_residueLedger n σL T hL hT,
    h15NormalizedCompleteContourBoundary_eq_residueLedger
      n σL' T' hL' hT']

/-- Exact extraction of the damped `s = 1` residue: normalize the full
boundary and subtract the first-order `s = 0` residue. -/
theorem h15GlobalAdditionalResidue_eq_normalizedBoundary_sub_firstOrder
    (n : ℕ) (σL T : ℝ) (hL : σL < 0) (hT : 0 < T) :
    h15GlobalAdditionalResidue n =
      h15NormalizedCompleteContourBoundary n σL T -
        h15GlobalFirstOrderCoefficient n := by
  rw [h15NormalizedCompleteContourBoundary_eq_residueLedger n σL T hL hT]
  unfold h15ContourResidueLedger
  ring

/-- Exact extraction of the **undamped** endpoint amplitude.  The inverse
damping multiplies the complete residue extraction and is not absorbed into
one edge or one frequency sector. -/
theorem h15AdditionalResidueAmplitude_eq_inverseDamping_mul_boundary_sub_first
    (n : ℕ) (σL T : ℝ) (hL : σL < 0) (hT : 0 < T) :
    h15AdditionalResidueAmplitude n =
      (h15ContourDamping n : ℂ)⁻¹ *
        (h15NormalizedCompleteContourBoundary n σL T -
          h15GlobalFirstOrderCoefficient n) := by
  rw [← h15GlobalAdditionalResidue_eq_normalizedBoundary_sub_firstOrder
    n σL T hL hT]
  exact h15ContourDamping_inv_mul_globalAdditionalResidue n |>.symm

/-! ## Edge expansion -/

/-- The normalized boundary contains both vertical edges and the oriented
horizontal pair.  This is the exact edge bookkeeping behind the endpoint
extraction formula. -/
theorem h15NormalizedCompleteContourBoundary_eq_edges
    (n : ℕ) (σL T : ℝ) :
    h15NormalizedCompleteContourBoundary n σL T =
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        (symmetricHorizontalEdges (h15ActiveContourAggregate n)
            σL (3 / 2) T +
          I * h15TruncatedVerticalIntegral n (3 / 2) T -
          I * h15TruncatedVerticalIntegral n σL T) := by
  unfold h15NormalizedCompleteContourBoundary rectangularBoundaryIntegral
    symmetricHorizontalEdges rectangularRightEdge rectangularLeftEdge
    h15TruncatedVerticalIntegral h15VerticalAggregate
  simp only [symmetricLowerCorner, symmetricUpperCorner,
    Complex.sub_re, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
    zero_sub, add_zero, Complex.sub_im, Complex.add_im,
    sub_self, zero_add]
  ring

/-- Fully expanded undamped endpoint formula in terms of the two vertical
edges, the horizontal pair, and the first-order correction. -/
theorem h15AdditionalResidueAmplitude_eq_inverseDamping_mul_edges_sub_first
    (n : ℕ) (σL T : ℝ) (hL : σL < 0) (hT : 0 < T) :
    h15AdditionalResidueAmplitude n =
      (h15ContourDamping n : ℂ)⁻¹ *
        ((2 * (Real.pi : ℂ) * I)⁻¹ *
            (symmetricHorizontalEdges (h15ActiveContourAggregate n)
                σL (3 / 2) T +
              I * h15TruncatedVerticalIntegral n (3 / 2) T -
              I * h15TruncatedVerticalIntegral n σL T) -
          h15GlobalFirstOrderCoefficient n) := by
  rw [h15AdditionalResidueAmplitude_eq_inverseDamping_mul_boundary_sub_first
    n σL T hL hT,
    h15NormalizedCompleteContourBoundary_eq_edges]

/-! ## Certified energy and stop test -/

/-- The certified Nyman--Beurling energy with the endpoint replaced by its
exact full-boundary extraction. -/
theorem logTaperL2Error_eq_elementaryEndpoint_add_boundaryExtraction_im
    (n : ℕ) (σL T : ℝ) (hL : σL < 0) (hT : 0 < T) :
    logTaperL2Error n =
      h15CertifiedElementaryEndpointLedger n +
        ((h15ContourDamping n : ℂ)⁻¹ *
          (h15NormalizedCompleteContourBoundary n σL T -
            h15GlobalFirstOrderCoefficient n)).im := by
  rw [logTaperL2Error_eq_elementaryEndpoint_add_additionalResidueAmplitude_im,
    h15AdditionalResidueAmplitude_eq_inverseDamping_mul_boundary_sub_first
      n σL T hL hT]

/-- Stop test: using the normalized boundary without subtracting the
first-order residue overcounts the endpoint by exactly the inverse-damped
first-order mode. -/
theorem h15BoundaryExtraction_without_firstOrder_error
    (n : ℕ) (σL T : ℝ) (hL : σL < 0) (hT : 0 < T) :
    (h15ContourDamping n : ℂ)⁻¹ *
          h15NormalizedCompleteContourBoundary n σL T -
        h15AdditionalResidueAmplitude n =
      (h15ContourDamping n : ℂ)⁻¹ *
        h15GlobalFirstOrderCoefficient n := by
  rw [h15AdditionalResidueAmplitude_eq_inverseDamping_mul_boundary_sub_first
    n σL T hL hT]
  ring

/-- The endpoint-to-linear defect from WP1k, now expressed entirely through
the exact boundary extraction and the corrected complete right edge. -/
theorem h15EndpointToLinearPostFEDefect_eq_boundaryExtraction_sub_rightEdge
    (n K : ℕ) (σL T : ℝ) (hL : σL < 0) (hT : 0 < T) :
    h15EndpointToLinearPostFEDefect n K T =
      ((h15ContourDamping n : ℂ)⁻¹ *
        (h15NormalizedCompleteContourBoundary n σL T -
          h15GlobalFirstOrderCoefficient n)).im -
        (h15CorrectedThreeHalfRightEdge n T).im := by
  unfold h15EndpointToLinearPostFEDefect
  rw [h15AdditionalResidueAmplitude_eq_inverseDamping_mul_boundary_sub_first
      n σL T hL hT,
    h15CompleteLinearPostFERightEdge_eq_correctedRightEdge]

end NBMellinTools.NB15
