/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEJointTransformCompatibilityAudit

/-!
# NB12zzzO: unconditional absolute baseline for the joint transform

This file proves the strongest immediate triangle-inequality estimate for the
exact post-functional-equation joint transform.  The missing-residue trace is
kept in the same baseline as all four orientation populations.

The result is deliberately expressed using the genuinely joint `L¹` mass.
It neither factors the pair coefficient nor discards the retained correction.
Consequently it is a faithful unconditional baseline.  Any closure theorem
which improves on it must exploit signed cancellation rather than a hidden
change of coefficient model.
-/

open scoped BigOperators ComplexConjugate
open Complex

namespace NBMellinTools.NB12

/-! ## Pointwise character norms -/

theorem norm_h15PostFECommonPairAdditivePhase_le_one
    (left right : BettinChandeeUnitSign)
    (r u q v q' : ℕ) :
    ‖h15PostFECommonPairAdditivePhase left right r u q v q'‖ ≤ 1 := by
  by_cases hM : q * q' = 0
  · simp [h15PostFECommonPairAdditivePhase, hM]
  · letI : NeZero (q * q') := ⟨hM⟩
    by_cases hcop : Nat.Coprime u q ∧ Nat.Coprime v q'
    · unfold h15PostFECommonPairAdditivePhase
      simp only [hM, dite_false]
      rw [if_pos hcop, AddChar.norm_apply]
    · unfold h15PostFECommonPairAdditivePhase
      simp only [hM, dite_false]
      rw [if_neg hcop, norm_zero]
      exact zero_le_one

theorem norm_h15PostFEReducedDoubledAdditivePhase_le_one
    (r u q : ℕ) :
    ‖h15PostFEReducedDoubledAdditivePhase r u q‖ ≤ 1 := by
  by_cases hq : q = 0
  · simp [h15PostFEReducedDoubledAdditivePhase, hq]
  · letI : NeZero q := ⟨hq⟩
    by_cases hcop : Nat.Coprime u q
    · unfold h15PostFEReducedDoubledAdditivePhase
      simp only [hq, dite_false]
      rw [if_pos hcop, AddChar.norm_apply]
    · unfold h15PostFEReducedDoubledAdditivePhase
      simp only [hq, dite_false]
      rw [if_neg hcop, norm_zero]
      exact zero_le_one

/-! ## Separate masses and the Archimedean cost -/

noncomputable def h15PostFEJointMissingL1Mass
    (modulusSupport : Finset ℕ)
    (missingSupport : ℕ → Finset ℕ)
    (missingCoefficient : ℕ → ℝ) : ℝ :=
  ∑ q ∈ modulusSupport,
    |missingCoefficient q| * ((missingSupport q).card : ℝ)

noncomputable def h15PostFEJointPairL1Mass
    (pairSupport : Finset H15PostFEJointResiduePair)
    (pairCoefficient : H15PostFEJointResiduePair → ℂ) : ℝ :=
  ∑ κ ∈ pairSupport, ‖pairCoefficient κ‖

noncomputable def h15PostFEOrientationPairNormCost
    (left right : BettinChandeeUnitSign) (t : ℝ) : ℝ :=
  ‖h15PostFEOrientationArchimedeanFactor left t‖ *
    ‖h15PostFEOrientationArchimedeanFactor right t‖

noncomputable def h15PostFEFourOrientationNormCost (t : ℝ) : ℝ :=
  h15PostFEOrientationPairNormCost .positive .positive t +
    h15PostFEOrientationPairNormCost .positive .negative t +
      h15PostFEOrientationPairNormCost .negative .positive t +
        h15PostFEOrientationPairNormCost .negative .negative t

theorem h15PostFEJointMissingL1Mass_nonneg
    (modulusSupport : Finset ℕ)
    (missingSupport : ℕ → Finset ℕ)
    (missingCoefficient : ℕ → ℝ) :
    0 ≤ h15PostFEJointMissingL1Mass modulusSupport missingSupport
      missingCoefficient := by
  unfold h15PostFEJointMissingL1Mass
  positivity

theorem h15PostFEJointPairL1Mass_nonneg
    (pairSupport : Finset H15PostFEJointResiduePair)
    (pairCoefficient : H15PostFEJointResiduePair → ℂ) :
    0 ≤ h15PostFEJointPairL1Mass pairSupport pairCoefficient := by
  unfold h15PostFEJointPairL1Mass
  positivity

theorem h15PostFEFourOrientationNormCost_nonneg (t : ℝ) :
    0 ≤ h15PostFEFourOrientationNormCost t := by
  unfold h15PostFEFourOrientationNormCost
    h15PostFEOrientationPairNormCost
  positivity

theorem h15PostFEJointCoefficientL1Mass_eq_missing_add_pair
    (pairSupport : Finset H15PostFEJointResiduePair)
    (pairCoefficient : H15PostFEJointResiduePair → ℂ)
    (modulusSupport : Finset ℕ)
    (missingSupport : ℕ → Finset ℕ)
    (missingCoefficient : ℕ → ℝ) :
    h15PostFEJointCoefficientL1Mass pairSupport pairCoefficient
        modulusSupport missingSupport missingCoefficient =
      h15PostFEJointMissingL1Mass modulusSupport missingSupport
          missingCoefficient +
        h15PostFEJointPairL1Mass pairSupport pairCoefficient := by
  rfl

/-! ## Componentwise triangle bounds -/

theorem abs_h15PostFEJointPairTransform_le
    (left right : BettinChandeeUnitSign)
    (support : Finset H15PostFEJointResiduePair)
    (coefficient : H15PostFEJointResiduePair → ℂ)
    (r : ℕ) (t : ℝ) :
    |h15PostFEJointPairTransform left right support coefficient r t| ≤
      h15PostFEOrientationPairNormCost left right t *
        h15PostFEJointPairL1Mass support coefficient := by
  unfold h15PostFEJointPairTransform
  calc
    |∑ κ ∈ support,
        (coefficient κ *
          (conj (h15PostFEOrientationArchimedeanFactor left t) *
            h15PostFEOrientationArchimedeanFactor right t *
            h15PostFECommonPairAdditivePhase left right r
              κ.1.1 κ.1.2 κ.2.1 κ.2.2)).re| ≤
        ∑ κ ∈ support,
          |(coefficient κ *
            (conj (h15PostFEOrientationArchimedeanFactor left t) *
              h15PostFEOrientationArchimedeanFactor right t *
              h15PostFECommonPairAdditivePhase left right r
                κ.1.1 κ.1.2 κ.2.1 κ.2.2)).re| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ κ ∈ support,
        h15PostFEOrientationPairNormCost left right t *
          ‖coefficient κ‖ := by
      apply Finset.sum_le_sum
      intro κ _hκ
      calc
        |(coefficient κ *
            (conj (h15PostFEOrientationArchimedeanFactor left t) *
              h15PostFEOrientationArchimedeanFactor right t *
              h15PostFECommonPairAdditivePhase left right r
                κ.1.1 κ.1.2 κ.2.1 κ.2.2)).re| ≤
            ‖coefficient κ *
              (conj (h15PostFEOrientationArchimedeanFactor left t) *
                h15PostFEOrientationArchimedeanFactor right t *
                h15PostFECommonPairAdditivePhase left right r
                  κ.1.1 κ.1.2 κ.2.1 κ.2.2)‖ :=
          Complex.abs_re_le_norm _
        _ ≤ h15PostFEOrientationPairNormCost left right t *
              ‖coefficient κ‖ := by
          rw [norm_mul, norm_mul, norm_mul, norm_conj]
          have hphase := norm_h15PostFECommonPairAdditivePhase_le_one
            left right r κ.1.1 κ.1.2 κ.2.1 κ.2.2
          unfold h15PostFEOrientationPairNormCost
          calc
            ‖coefficient κ‖ *
                (‖h15PostFEOrientationArchimedeanFactor left t‖ *
                  ‖h15PostFEOrientationArchimedeanFactor right t‖ *
                    ‖h15PostFECommonPairAdditivePhase left right r
                      κ.1.1 κ.1.2 κ.2.1 κ.2.2‖) ≤
                ‖coefficient κ‖ *
                  (‖h15PostFEOrientationArchimedeanFactor left t‖ *
                    ‖h15PostFEOrientationArchimedeanFactor right t‖ * 1) := by
              gcongr
            _ = ‖h15PostFEOrientationArchimedeanFactor left t‖ *
                  ‖h15PostFEOrientationArchimedeanFactor right t‖ *
                    ‖coefficient κ‖ := by ring
    _ = h15PostFEOrientationPairNormCost left right t *
        h15PostFEJointPairL1Mass support coefficient := by
      unfold h15PostFEJointPairL1Mass
      rw [Finset.mul_sum]

theorem abs_h15PostFEJointMissingTransform_le
    (modulusSupport : Finset ℕ)
    (missingSupport : ℕ → Finset ℕ)
    (coefficient : ℕ → ℝ) (r : ℕ) :
    |h15PostFEJointMissingTransform modulusSupport missingSupport
        coefficient r| ≤
      h15PostFEJointMissingL1Mass modulusSupport missingSupport
        coefficient := by
  unfold h15PostFEJointMissingTransform h15PostFEJointMissingL1Mass
  calc
    |∑ q ∈ modulusSupport,
        coefficient q *
          ∑ a ∈ missingSupport q,
            (h15PostFEReducedDoubledAdditivePhase r a q).im| ≤
      ∑ q ∈ modulusSupport,
        |coefficient q *
          ∑ a ∈ missingSupport q,
            (h15PostFEReducedDoubledAdditivePhase r a q).im| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ modulusSupport,
        |coefficient q| * ((missingSupport q).card : ℝ) := by
      apply Finset.sum_le_sum
      intro q _hq
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      calc
        |∑ a ∈ missingSupport q,
            (h15PostFEReducedDoubledAdditivePhase r a q).im| ≤
            ∑ a ∈ missingSupport q,
              |(h15PostFEReducedDoubledAdditivePhase r a q).im| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _a ∈ missingSupport q, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro a _ha
          exact (Complex.abs_im_le_norm _).trans
            (norm_h15PostFEReducedDoubledAdditivePhase_le_one r a q)
        _ = ((missingSupport q).card : ℝ) := by simp

/-! ## The full correction-preserving baseline -/

noncomputable def h15PostFEJointAbsoluteBaseline
    (pairSupport : Finset H15PostFEJointResiduePair)
    (pairCoefficient : H15PostFEJointResiduePair → ℂ)
    (modulusSupport : Finset ℕ)
    (missingSupport : ℕ → Finset ℕ)
    (missingCoefficient : ℕ → ℝ)
    (t : ℝ) : ℝ :=
  h15PostFEJointMissingL1Mass modulusSupport missingSupport
      missingCoefficient +
    |4 / (2 * h15PairedHyperbolicCoefficient t)| *
      h15PostFEFourOrientationNormCost t *
        h15PostFEJointPairL1Mass pairSupport pairCoefficient

theorem h15PostFEJointAbsoluteBaseline_nonneg
    (pairSupport : Finset H15PostFEJointResiduePair)
    (pairCoefficient : H15PostFEJointResiduePair → ℂ)
    (modulusSupport : Finset ℕ)
    (missingSupport : ℕ → Finset ℕ)
    (missingCoefficient : ℕ → ℝ)
    (t : ℝ) :
    0 ≤ h15PostFEJointAbsoluteBaseline pairSupport pairCoefficient
      modulusSupport missingSupport missingCoefficient t := by
  unfold h15PostFEJointAbsoluteBaseline
  exact add_nonneg
    (h15PostFEJointMissingL1Mass_nonneg _ _ _)
    (mul_nonneg
      (mul_nonneg (abs_nonneg _)
        (h15PostFEFourOrientationNormCost_nonneg t))
      (h15PostFEJointPairL1Mass_nonneg _ _))

theorem abs_h15PostFEJointCorrectionTransform_le_absoluteBaseline
    (pairSupport : Finset H15PostFEJointResiduePair)
    (pairCoefficient : H15PostFEJointResiduePair → ℂ)
    (modulusSupport : Finset ℕ)
    (missingSupport : ℕ → Finset ℕ)
    (missingCoefficient : ℕ → ℝ)
    (r : ℕ) (t : ℝ) :
    |h15PostFEJointCorrectionTransform pairSupport pairCoefficient
        modulusSupport missingSupport missingCoefficient r t| ≤
      h15PostFEJointAbsoluteBaseline pairSupport pairCoefficient
        modulusSupport missingSupport missingCoefficient t := by
  unfold h15PostFEJointCorrectionTransform
  let Ppp := h15PostFEJointPairTransform .positive .positive
    pairSupport pairCoefficient r t
  let Ppn := h15PostFEJointPairTransform .positive .negative
    pairSupport pairCoefficient r t
  let Pnp := h15PostFEJointPairTransform .negative .positive
    pairSupport pairCoefficient r t
  let Pnn := h15PostFEJointPairTransform .negative .negative
    pairSupport pairCoefficient r t
  have hmissing := abs_h15PostFEJointMissingTransform_le
    modulusSupport missingSupport missingCoefficient r
  have hpp := abs_h15PostFEJointPairTransform_le .positive .positive
    pairSupport pairCoefficient r t
  have hpn := abs_h15PostFEJointPairTransform_le .positive .negative
    pairSupport pairCoefficient r t
  have hnp := abs_h15PostFEJointPairTransform_le .negative .positive
    pairSupport pairCoefficient r t
  have hnn := abs_h15PostFEJointPairTransform_le .negative .negative
    pairSupport pairCoefficient r t
  have hpairs :
      |Ppp + Ppn + Pnp + Pnn| ≤
        h15PostFEFourOrientationNormCost t *
          h15PostFEJointPairL1Mass pairSupport pairCoefficient := by
    calc
      |Ppp + Ppn + Pnp + Pnn| ≤
          |Ppp| + |Ppn| + |Pnp| + |Pnn| := by
        calc
          |Ppp + Ppn + Pnp + Pnn| ≤ |Ppp + Ppn + Pnp| + |Pnn| :=
            abs_add_le _ _
          _ ≤ (|Ppp + Ppn| + |Pnp|) + |Pnn| := by
            gcongr
            exact abs_add_le _ _
          _ ≤ ((|Ppp| + |Ppn|) + |Pnp|) + |Pnn| := by
            gcongr
            exact abs_add_le _ _
          _ = _ := by ring
      _ ≤ h15PostFEFourOrientationNormCost t *
          h15PostFEJointPairL1Mass pairSupport pairCoefficient := by
        dsimp [Ppp, Ppn, Pnp, Pnn] at hpp hpn hnp hnn ⊢
        unfold h15PostFEFourOrientationNormCost
        nlinarith [h15PostFEJointPairL1Mass_nonneg pairSupport pairCoefficient]
  calc
    |h15PostFEJointMissingTransform modulusSupport missingSupport
          missingCoefficient r +
        4 * (Ppp + Ppn + Pnp + Pnn) /
          (2 * h15PairedHyperbolicCoefficient t)| ≤
      |h15PostFEJointMissingTransform modulusSupport missingSupport
          missingCoefficient r| +
        |4 * (Ppp + Ppn + Pnp + Pnn) /
          (2 * h15PairedHyperbolicCoefficient t)| := abs_add_le _ _
    _ ≤ h15PostFEJointMissingL1Mass modulusSupport missingSupport
          missingCoefficient +
        |4 / (2 * h15PairedHyperbolicCoefficient t)| *
          (h15PostFEFourOrientationNormCost t *
            h15PostFEJointPairL1Mass pairSupport pairCoefficient) := by
      gcongr
      rw [show 4 * (Ppp + Ppn + Pnp + Pnn) /
          (2 * h15PairedHyperbolicCoefficient t) =
        (4 / (2 * h15PairedHyperbolicCoefficient t)) *
          (Ppp + Ppn + Pnp + Pnn) by ring]
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hpairs (abs_nonneg _)
    _ = h15PostFEJointAbsoluteBaseline pairSupport pairCoefficient
        modulusSupport missingSupport missingCoefficient t := by
      unfold h15PostFEJointAbsoluteBaseline
      ring

/-- The literal H15 absolute baseline. -/
noncomputable def h15PostFEActualJointAbsoluteBaseline
    (n g U Q r : ℕ) (t : ℝ) : ℝ :=
  h15PostFEJointAbsoluteBaseline
    (h15PostFEOrderedPairResidueSupport n g U Q)
    (h15PostFEOrderedPairCollectedScalar n g U Q r t)
    (h15PostFEResidueModulusSupport n g U Q)
    (h15PostFEMissingResidues n g U Q)
    (h15PostFEResidueFiberMeanCoefficient n g U Q r t)
    t

theorem abs_h15PostFEActualJointCorrectionTransform_le_absoluteBaseline
    (n g U Q r : ℕ) (t : ℝ) :
    |h15PostFEActualJointCorrectionTransform n g U Q r t| ≤
      h15PostFEActualJointAbsoluteBaseline n g U Q r t := by
  exact abs_h15PostFEJointCorrectionTransform_le_absoluteBaseline
    _ _ _ _ _ _ _

end NBMellinTools.NB12
