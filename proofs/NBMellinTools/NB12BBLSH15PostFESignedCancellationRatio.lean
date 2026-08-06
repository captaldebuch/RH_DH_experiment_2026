/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEArchimedeanCostAudit

/-!
# NB12zzzQ: normalized signed-cancellation ratio

The unconditional absolute baseline has a non-decaying Archimedean cost.
This file therefore normalizes the exact correction-preserving transform by
that baseline.  The resulting ratio lies in `[0,1]`, and the transform is
exactly the ratio times the baseline.

An explicit moving-scale package then shows what a successful signed theorem
must prove: the cancellation ratio, multiplied by the Archimedean envelope
and the literal joint coefficient mass, tends to zero.  Such data constructs
the existing `H15PostFEJointTransformDecayData` without changing phase,
separating coefficients, or dropping the missing-residue trace.

No decay estimate or RH conclusion is asserted here.
-/

open Filter
open scoped Topology

namespace NBMellinTools.NB12

/-! ## A common absolute envelope -/

/-- One coefficient multiplying the complete joint `L¹` mass. -/
noncomputable def h15PostFEAbsoluteEnvelopeGain (t : ℝ) : ℝ :=
  max 1 (h15PostFEAbsolutePairGain t)

theorem one_le_h15PostFEAbsoluteEnvelopeGain (t : ℝ) :
    1 ≤ h15PostFEAbsoluteEnvelopeGain t := by
  exact le_max_left _ _

theorem h15PostFEAbsolutePairGain_le_envelope (t : ℝ) :
    h15PostFEAbsolutePairGain t ≤ h15PostFEAbsoluteEnvelopeGain t := by
  exact le_max_right _ _

theorem h15PostFEAbsoluteEnvelopeGain_nonneg (t : ℝ) :
    0 ≤ h15PostFEAbsoluteEnvelopeGain t := by
  linarith [one_le_h15PostFEAbsoluteEnvelopeGain t]

theorem h15PostFEJointAbsoluteBaseline_le_envelope_mul_mass
    (pairSupport : Finset H15PostFEJointResiduePair)
    (pairCoefficient : H15PostFEJointResiduePair → ℂ)
    (modulusSupport : Finset ℕ)
    (missingSupport : ℕ → Finset ℕ)
    (missingCoefficient : ℕ → ℝ)
    (t : ℝ) :
    h15PostFEJointAbsoluteBaseline pairSupport pairCoefficient
        modulusSupport missingSupport missingCoefficient t ≤
      h15PostFEAbsoluteEnvelopeGain t *
        h15PostFEJointCoefficientL1Mass pairSupport pairCoefficient
          modulusSupport missingSupport missingCoefficient := by
  rw [h15PostFEJointAbsoluteBaseline_eq_missing_add_pairGain,
    h15PostFEJointCoefficientL1Mass_eq_missing_add_pair]
  have hmissing := h15PostFEJointMissingL1Mass_nonneg
    modulusSupport missingSupport missingCoefficient
  have hpair := h15PostFEJointPairL1Mass_nonneg
    pairSupport pairCoefficient
  calc
    h15PostFEJointMissingL1Mass modulusSupport missingSupport
          missingCoefficient +
        h15PostFEAbsolutePairGain t *
          h15PostFEJointPairL1Mass pairSupport pairCoefficient ≤
      h15PostFEAbsoluteEnvelopeGain t *
          h15PostFEJointMissingL1Mass modulusSupport missingSupport
            missingCoefficient +
        h15PostFEAbsoluteEnvelopeGain t *
          h15PostFEJointPairL1Mass pairSupport pairCoefficient := by
      exact add_le_add
        (by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right
              (one_le_h15PostFEAbsoluteEnvelopeGain t) hmissing)
        (mul_le_mul_of_nonneg_right
          (h15PostFEAbsolutePairGain_le_envelope t) hpair)
    _ = h15PostFEAbsoluteEnvelopeGain t *
        (h15PostFEJointMissingL1Mass modulusSupport missingSupport
            missingCoefficient +
          h15PostFEJointPairL1Mass pairSupport pairCoefficient) := by ring

/-! ## Literal signed-cancellation ratio -/

noncomputable def h15PostFEActualSignedCancellationRatio
    (n g U Q r : ℕ) (t : ℝ) : ℝ :=
  |h15PostFEActualJointCorrectionTransform n g U Q r t| /
    h15PostFEActualJointAbsoluteBaseline n g U Q r t

theorem h15PostFEActualJointAbsoluteBaseline_nonneg
    (n g U Q r : ℕ) (t : ℝ) :
    0 ≤ h15PostFEActualJointAbsoluteBaseline n g U Q r t := by
  unfold h15PostFEActualJointAbsoluteBaseline
  exact h15PostFEJointAbsoluteBaseline_nonneg _ _ _ _ _ _

theorem h15PostFEActualSignedCancellationRatio_nonneg
    (n g U Q r : ℕ) (t : ℝ) :
    0 ≤ h15PostFEActualSignedCancellationRatio n g U Q r t := by
  unfold h15PostFEActualSignedCancellationRatio
  exact div_nonneg (abs_nonneg _)
    (h15PostFEActualJointAbsoluteBaseline_nonneg n g U Q r t)

theorem h15PostFEActualSignedCancellationRatio_le_one
    (n g U Q r : ℕ) (t : ℝ) :
    h15PostFEActualSignedCancellationRatio n g U Q r t ≤ 1 := by
  unfold h15PostFEActualSignedCancellationRatio
  by_cases hzero : h15PostFEActualJointAbsoluteBaseline n g U Q r t = 0
  · simp [hzero]
  · apply (div_le_one
      (lt_of_le_of_ne
        (h15PostFEActualJointAbsoluteBaseline_nonneg n g U Q r t)
        (Ne.symm hzero))).2
    exact abs_h15PostFEActualJointCorrectionTransform_le_absoluteBaseline
      n g U Q r t

/-- Exact reconstruction of the absolute transform from its normalized
cancellation ratio and absolute baseline. -/
theorem abs_h15PostFEActualJointCorrectionTransform_eq_ratio_mul_baseline
    (n g U Q r : ℕ) (t : ℝ) :
    |h15PostFEActualJointCorrectionTransform n g U Q r t| =
      h15PostFEActualSignedCancellationRatio n g U Q r t *
        h15PostFEActualJointAbsoluteBaseline n g U Q r t := by
  unfold h15PostFEActualSignedCancellationRatio
  by_cases hzero : h15PostFEActualJointAbsoluteBaseline n g U Q r t = 0
  · have habs :
        |h15PostFEActualJointCorrectionTransform n g U Q r t| = 0 := by
      apply le_antisymm
      · simpa [hzero] using
          abs_h15PostFEActualJointCorrectionTransform_le_absoluteBaseline
            n g U Q r t
      · exact abs_nonneg _
    simp [hzero, habs]
  · field_simp [hzero]

/-! ## Moving signed-improvement package -/

/-- A quantitative signed theorem stated in normalized form.  The gain is
allowed to depend on the whole H15 scale, but it must beat both the literal
joint coefficient mass and the exact Archimedean envelope. -/
structure H15PostFESignedCancellationRatioDecayData
    (g U Q r : ℕ → ℕ) (t : ℕ → ℝ) where
  gain : ℕ → ℝ
  gain_nonneg : ∀ N, 0 ≤ gain N
  ratio_bound : ∀ N,
    h15PostFEActualSignedCancellationRatio
      N (g N) (U N) (Q N) (r N) (t N) ≤ gain N
  scaled_envelope_mass_tendsto_zero :
    Tendsto
      (fun N => gain N * h15PostFEAbsoluteEnvelopeGain (t N) *
        h15PostFEActualJointCoefficientL1Mass
          N (g N) (U N) (Q N) (r N) (t N))
      atTop (nhds 0)

/-- A normalized signed-improvement theorem supplies exactly the joint
transform decay interface used by the post-FE reduction. -/
noncomputable def H15PostFESignedCancellationRatioDecayData.toJointDecayData
    {g U Q r : ℕ → ℕ} {t : ℕ → ℝ}
    (H : H15PostFESignedCancellationRatioDecayData g U Q r t) :
    H15PostFEJointTransformDecayData g U Q r t where
  gain N := H.gain N * h15PostFEAbsoluteEnvelopeGain (t N)
  gain_nonneg N := mul_nonneg (H.gain_nonneg N)
    (h15PostFEAbsoluteEnvelopeGain_nonneg (t N))
  estimate N := by
    rw [abs_h15PostFEActualJointCorrectionTransform_eq_ratio_mul_baseline]
    calc
      h15PostFEActualSignedCancellationRatio
            N (g N) (U N) (Q N) (r N) (t N) *
          h15PostFEActualJointAbsoluteBaseline
            N (g N) (U N) (Q N) (r N) (t N) ≤
        H.gain N *
          h15PostFEActualJointAbsoluteBaseline
            N (g N) (U N) (Q N) (r N) (t N) :=
        mul_le_mul_of_nonneg_right (H.ratio_bound N)
          (h15PostFEActualJointAbsoluteBaseline_nonneg
            N (g N) (U N) (Q N) (r N) (t N))
      _ ≤ H.gain N *
          (h15PostFEAbsoluteEnvelopeGain (t N) *
            h15PostFEActualJointCoefficientL1Mass
              N (g N) (U N) (Q N) (r N) (t N)) := by
        apply mul_le_mul_of_nonneg_left _ (H.gain_nonneg N)
        unfold h15PostFEActualJointAbsoluteBaseline
          h15PostFEActualJointCoefficientL1Mass
        exact h15PostFEJointAbsoluteBaseline_le_envelope_mul_mass
          _ _ _ _ _ _
      _ = (H.gain N * h15PostFEAbsoluteEnvelopeGain (t N)) *
          h15PostFEActualJointCoefficientL1Mass
            N (g N) (U N) (Q N) (r N) (t N) := by ring
  scaled_mass_tendsto_zero := by
    simpa only [mul_assoc] using H.scaled_envelope_mass_tendsto_zero

end NBMellinTools.NB12
