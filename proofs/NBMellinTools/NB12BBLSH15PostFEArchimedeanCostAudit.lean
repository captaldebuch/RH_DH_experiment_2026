/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEJointTransformAbsoluteBaseline

/-!
# NB12zzzP: Archimedean cost of the absolute joint-transform baseline

The four orientation factors in the post-functional-equation transform have
an exact norm cost

`(1 + |sinh (pi t)|)^2`.

After the normalization already present in the correction-preserving
transform, the absolute pair multiplier is

`2 * (1 + |sinh (pi t)|)^2 / |sinh (pi t)|`

away from `t = 0`.  It is at least eight.  Thus the unconditional triangle
bound does not manufacture a small analytic gain: any low-frequency decay
must come from signed arithmetic cancellation in the joint transform.

At `t = 0`, Lean's totalized division makes the pair multiplier zero.  This
single point is harmless for later integration but is stated separately so
that the nonzero-height lower bound is not misread as a global assertion.
-/

open Complex

namespace NBMellinTools.NB12

@[simp] theorem norm_h15PostFEOrientationArchimedeanFactor_positive
    (t : ℝ) :
    ‖h15PostFEOrientationArchimedeanFactor .positive t‖ = 1 := by
  simp [h15PostFEOrientationArchimedeanFactor]

theorem norm_h15PostFEOrientationArchimedeanFactor_negative
    (t : ℝ) :
    ‖h15PostFEOrientationArchimedeanFactor .negative t‖ =
      |h15PairedHyperbolicCoefficient t| := by
  unfold h15PostFEOrientationArchimedeanFactor
  rw [cos_pi_mul_bblsEstermannThreeHalfPoint_eq_sinh_mul_I]
  simp [Real.norm_eq_abs]

theorem h15PostFEFourOrientationNormCost_eq (t : ℝ) :
    h15PostFEFourOrientationNormCost t =
      (1 + |h15PairedHyperbolicCoefficient t|) ^ 2 := by
  unfold h15PostFEFourOrientationNormCost
    h15PostFEOrientationPairNormCost
  rw [norm_h15PostFEOrientationArchimedeanFactor_negative]
  simp only [norm_h15PostFEOrientationArchimedeanFactor_positive]
  ring

/-- The multiplier of the joint pair `L¹` mass in the absolute baseline. -/
noncomputable def h15PostFEAbsolutePairGain (t : ℝ) : ℝ :=
  |4 / (2 * h15PairedHyperbolicCoefficient t)| *
    h15PostFEFourOrientationNormCost t

theorem h15PostFEAbsolutePairGain_eq_of_ne_zero
    (t : ℝ) (ht : h15PairedHyperbolicCoefficient t ≠ 0) :
    h15PostFEAbsolutePairGain t =
      2 * (1 + |h15PairedHyperbolicCoefficient t|) ^ 2 /
        |h15PairedHyperbolicCoefficient t| := by
  unfold h15PostFEAbsolutePairGain
  rw [h15PostFEFourOrientationNormCost_eq, abs_div, abs_mul]
  have htwo : |(2 : ℝ)| = 2 := by norm_num
  have hfour : |(4 : ℝ)| = 4 := by norm_num
  rw [htwo, hfour]
  have habs : |h15PairedHyperbolicCoefficient t| ≠ 0 := abs_ne_zero.mpr ht
  field_simp [habs]
  ring

/-- The absolute baseline pays at least a factor eight at every nonzero
height.  In particular, it cannot supply a vanishing gain by itself. -/
theorem eight_le_h15PostFEAbsolutePairGain
    (t : ℝ) (ht : h15PairedHyperbolicCoefficient t ≠ 0) :
    8 ≤ h15PostFEAbsolutePairGain t := by
  rw [h15PostFEAbsolutePairGain_eq_of_ne_zero t ht]
  have hx : 0 < |h15PairedHyperbolicCoefficient t| := abs_pos.mpr ht
  apply (le_div_iff₀ hx).2
  nlinarith [sq_nonneg (|h15PairedHyperbolicCoefficient t| - 1)]

@[simp] theorem h15PostFEAbsolutePairGain_zero :
    h15PostFEAbsolutePairGain 0 = 0 := by
  simp [h15PostFEAbsolutePairGain, h15PairedHyperbolicCoefficient]

/-- The baseline rewritten with its exact pair multiplier. -/
theorem h15PostFEJointAbsoluteBaseline_eq_missing_add_pairGain
    (pairSupport : Finset H15PostFEJointResiduePair)
    (pairCoefficient : H15PostFEJointResiduePair → ℂ)
    (modulusSupport : Finset ℕ)
    (missingSupport : ℕ → Finset ℕ)
    (missingCoefficient : ℕ → ℝ)
    (t : ℝ) :
    h15PostFEJointAbsoluteBaseline pairSupport pairCoefficient
        modulusSupport missingSupport missingCoefficient t =
      h15PostFEJointMissingL1Mass modulusSupport missingSupport
          missingCoefficient +
        h15PostFEAbsolutePairGain t *
          h15PostFEJointPairL1Mass pairSupport pairCoefficient := by
  unfold h15PostFEJointAbsoluteBaseline h15PostFEAbsolutePairGain
  ring

end NBMellinTools.NB12
