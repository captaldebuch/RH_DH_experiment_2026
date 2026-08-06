/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEBilinearExponentAudit

/-!
# NB12zzzm: joint-coefficient correction-preserving transform interface

The exponent audit rules out applying the two immediate separated-coefficient
estimates to the unresolved post-functional-equation sector.  This file
therefore defines the exact transform that a stronger analytic theorem must
control.

The input is deliberately joint:

* one arbitrary complex coefficient on each ordered key
  `((u,q),(v,q'))`;
* one real mean coefficient on each modulus and its missing residue set;
* all four positive/negative Estermann phase populations; and
* the doubled missing-residue trace.

No factorization of the ordered coefficient into one-variable sequences is
assumed.  A natural joint `L¹` coefficient mass is recorded, and the literal
H15 data are instantiated in the generic transform.  Finally, a moving-scale
decay package is shown to imply decay of the common-additive boundary
transfer and, together with decay of the mean-zero variation, decay of the
centered lift defect.

This is an exact conditional reduction.  It does not construct the required
analytic transform estimate and does not prove RH.
-/

open Filter
open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate
open Complex

namespace NBMellinTools.NB12

abbrev H15PostFEJointResiduePair := (ℕ × ℕ) × (ℕ × ℕ)

/-! ## Generic joint transform -/

/-- One signed orientation population with a genuinely joint coefficient. -/
noncomputable def h15PostFEJointPairTransform
    (left right : BettinChandeeUnitSign)
    (support : Finset H15PostFEJointResiduePair)
    (coefficient : H15PostFEJointResiduePair → ℂ)
    (r : ℕ) (t : ℝ) : ℝ :=
  ∑ κ ∈ support,
    (coefficient κ *
      (conj (h15PostFEOrientationArchimedeanFactor left t) *
        h15PostFEOrientationArchimedeanFactor right t *
        h15PostFECommonPairAdditivePhase left right r
          κ.1.1 κ.1.2 κ.2.1 κ.2.2)).re

/-- The linear doubled-character trace retained by residue completion. -/
noncomputable def h15PostFEJointMissingTransform
    (modulusSupport : Finset ℕ)
    (missingSupport : ℕ → Finset ℕ)
    (coefficient : ℕ → ℝ) (r : ℕ) : ℝ :=
  ∑ q ∈ modulusSupport,
    coefficient q *
      ∑ a ∈ missingSupport q,
        (h15PostFEReducedDoubledAdditivePhase r a q).im

/-- The complete correction-preserving transform.  The missing trace and all
four ordered populations occur inside one value; an estimate on this object
does not separate the correction from the oscillatory sector. -/
noncomputable def h15PostFEJointCorrectionTransform
    (pairSupport : Finset H15PostFEJointResiduePair)
    (pairCoefficient : H15PostFEJointResiduePair → ℂ)
    (modulusSupport : Finset ℕ)
    (missingSupport : ℕ → Finset ℕ)
    (missingCoefficient : ℕ → ℝ)
    (r : ℕ) (t : ℝ) : ℝ :=
  h15PostFEJointMissingTransform modulusSupport missingSupport
      missingCoefficient r +
    4 *
      (h15PostFEJointPairTransform .positive .positive
          pairSupport pairCoefficient r t +
        h15PostFEJointPairTransform .positive .negative
          pairSupport pairCoefficient r t +
        h15PostFEJointPairTransform .negative .positive
          pairSupport pairCoefficient r t +
        h15PostFEJointPairTransform .negative .negative
          pairSupport pairCoefficient r t) /
      (2 * h15PairedHyperbolicCoefficient t)

/-! ## Literal H15 instantiation -/

/-- The actual H15 data inserted into the generic joint transform. -/
noncomputable def h15PostFEActualJointCorrectionTransform
    (n g U Q r : ℕ) (t : ℝ) : ℝ :=
  h15PostFEJointCorrectionTransform
    (h15PostFEOrderedPairResidueSupport n g U Q)
    (h15PostFEOrderedPairCollectedScalar n g U Q r t)
    (h15PostFEResidueModulusSupport n g U Q)
    (h15PostFEMissingResidues n g U Q)
    (h15PostFEResidueFiberMeanCoefficient n g U Q r t)
    r t

theorem h15PostFEOrderedPairCommonAdditivePopulation_eq_jointTransform
    (left right : BettinChandeeUnitSign)
    (n g U Q r : ℕ) (t : ℝ) :
    h15PostFEOrderedPairCommonAdditivePopulation
        left right n g U Q r t =
      h15PostFEJointPairTransform left right
        (h15PostFEOrderedPairResidueSupport n g U Q)
        (h15PostFEOrderedPairCollectedScalar n g U Q r t) r t := by
  rfl

theorem h15PostFEMissingResidueAdditiveTrace_eq_jointTransform
    (n g U Q r : ℕ) (t : ℝ) :
    h15PostFEMissingResidueAdditiveTrace n g U Q r t =
      h15PostFEJointMissingTransform
        (h15PostFEResidueModulusSupport n g U Q)
        (h15PostFEMissingResidues n g U Q)
        (h15PostFEResidueFiberMeanCoefficient n g U Q r t) r := by
  rfl

/-- The generic transform is not a proxy: on the literal H15 support it is
definitionally the common-additive boundary-transfer expression. -/
theorem h15PostFECommonAdditiveBoundaryTransfer_eq_actualJointTransform
    (n g U Q r : ℕ) (t : ℝ) :
    h15PostFECommonAdditiveBoundaryTransfer n g U Q r t =
      h15PostFEActualJointCorrectionTransform n g U Q r t := by
  rfl

/-! ## Minimal joint coefficient mass -/

/-- Joint `L¹` coefficient mass.  It records no false tensor-product norm:
the ordered coefficient is measured directly on the pair support. -/
noncomputable def h15PostFEJointCoefficientL1Mass
    (pairSupport : Finset H15PostFEJointResiduePair)
    (pairCoefficient : H15PostFEJointResiduePair → ℂ)
    (modulusSupport : Finset ℕ)
    (missingSupport : ℕ → Finset ℕ)
    (missingCoefficient : ℕ → ℝ) : ℝ :=
  (∑ q ∈ modulusSupport,
      |missingCoefficient q| * ((missingSupport q).card : ℝ)) +
    ∑ κ ∈ pairSupport, ‖pairCoefficient κ‖

theorem h15PostFEJointCoefficientL1Mass_nonneg
    (pairSupport : Finset H15PostFEJointResiduePair)
    (pairCoefficient : H15PostFEJointResiduePair → ℂ)
    (modulusSupport : Finset ℕ)
    (missingSupport : ℕ → Finset ℕ)
    (missingCoefficient : ℕ → ℝ) :
    0 ≤ h15PostFEJointCoefficientL1Mass pairSupport pairCoefficient
      modulusSupport missingSupport missingCoefficient := by
  unfold h15PostFEJointCoefficientL1Mass
  positivity

/-- Joint mass of the actual correction-coupled H15 data. -/
noncomputable def h15PostFEActualJointCoefficientL1Mass
    (n g U Q r : ℕ) (t : ℝ) : ℝ :=
  h15PostFEJointCoefficientL1Mass
    (h15PostFEOrderedPairResidueSupport n g U Q)
    (h15PostFEOrderedPairCollectedScalar n g U Q r t)
    (h15PostFEResidueModulusSupport n g U Q)
    (h15PostFEMissingResidues n g U Q)
    (h15PostFEResidueFiberMeanCoefficient n g U Q r t)

theorem h15PostFEActualJointCoefficientL1Mass_nonneg
    (n g U Q r : ℕ) (t : ℝ) :
    0 ≤ h15PostFEActualJointCoefficientL1Mass n g U Q r t := by
  exact h15PostFEJointCoefficientL1Mass_nonneg _ _ _ _ _

/-- The actual joint mass is bounded by the missing-trace coefficient mass
plus the uncollected raw ordered-pair mass. -/
theorem h15PostFEActualJointCoefficientL1Mass_le_raw
    (n g U Q r : ℕ) (t : ℝ) :
    h15PostFEActualJointCoefficientL1Mass n g U Q r t ≤
      (∑ q ∈ h15PostFEResidueModulusSupport n g U Q,
          |h15PostFEResidueFiberMeanCoefficient n g U Q r t q| *
            ((h15PostFEMissingResidues n g U Q q).card : ℝ)) +
        ∑ p ∈ h15PostFEOrderedLaurentPairIndices n g U Q,
          ‖h15PostFEOrderedPairScalar n r t p‖ := by
  unfold h15PostFEActualJointCoefficientL1Mass
    h15PostFEJointCoefficientL1Mass
  have hcollection :=
    sum_norm_h15PostFEOrderedPairCollectedScalar_le_raw n g U Q r t
  linarith

/-! ## Moving-parameter analytic interface -/

/-- Exact analytic input required after the finite reductions.  `gain` is
allowed to depend on the whole H15 scale, but its product with the literal
joint coefficient mass must tend to zero. -/
structure H15PostFEJointTransformDecayData
    (g U Q r : ℕ → ℕ) (t : ℕ → ℝ) where
  gain : ℕ → ℝ
  gain_nonneg : ∀ N, 0 ≤ gain N
  estimate : ∀ N,
    |h15PostFEActualJointCorrectionTransform
        N (g N) (U N) (Q N) (r N) (t N)| ≤
      gain N *
        h15PostFEActualJointCoefficientL1Mass
          N (g N) (U N) (Q N) (r N) (t N)
  scaled_mass_tendsto_zero :
    Tendsto
      (fun N => gain N *
        h15PostFEActualJointCoefficientL1Mass
          N (g N) (U N) (Q N) (r N) (t N))
      atTop (nhds 0)

theorem H15PostFEJointTransformDecayData.jointTransform_tendsto_zero
    {g U Q r : ℕ → ℕ} {t : ℕ → ℝ}
    (H : H15PostFEJointTransformDecayData g U Q r t) :
    Tendsto
      (fun N => h15PostFEActualJointCorrectionTransform
        N (g N) (U N) (Q N) (r N) (t N))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_
    H.scaled_mass_tendsto_zero
  exact Eventually.of_forall H.estimate

theorem H15PostFEJointTransformDecayData.commonAdditive_tendsto_zero
    {g U Q r : ℕ → ℕ} {t : ℕ → ℝ}
    (H : H15PostFEJointTransformDecayData g U Q r t) :
    Tendsto
      (fun N => h15PostFECommonAdditiveBoundaryTransfer
        N (g N) (U N) (Q N) (r N) (t N))
      atTop (nhds 0) := by
  simpa only [h15PostFECommonAdditiveBoundaryTransfer_eq_actualJointTransform]
    using H.jointTransform_tendsto_zero

/-- The transform estimate closes the centered local lift defect once the
separately centered coefficient variation is also known to vanish.  This is
the exact final composition point of the post-FE reduction. -/
theorem H15PostFEJointTransformDecayData.centeredLiftDefect_tendsto_zero
    {g U Q r : ℕ → ℕ} {t : ℕ → ℝ}
    (H : H15PostFEJointTransformDecayData g U Q r t)
    (hQ : ∀ N, 0 < Q N)
    (hS : ∀ N, h15PairedHyperbolicCoefficient (t N) ≠ 0)
    (hvariation : Tendsto
      (fun N => h15PostFEResidueMeanZeroVariation
        N (g N) (U N) (Q N) (r N) (t N))
      atTop (nhds 0)) :
    Tendsto
      (fun N => h15PostFECenteredLiftDefect
        N (g N) (U N) (Q N) (r N) (t N))
      atTop (nhds 0) := by
  have hdiff : Tendsto
      (fun N =>
        h15PostFEResidueMeanZeroVariation
            N (g N) (U N) (Q N) (r N) (t N) -
          h15PostFECommonAdditiveBoundaryTransfer
            N (g N) (U N) (Q N) (r N) (t N))
      atTop (nhds 0) := by
    simpa using hvariation.sub H.commonAdditive_tendsto_zero
  refine hdiff.congr' ?_
  exact Eventually.of_forall fun N =>
    (h15PostFECenteredLiftDefect_eq_meanZero_sub_commonAdditiveTransfer
      N (g N) (U N) (Q N) (r N) (t N) (hQ N) (hS N)).symm

end NBMellinTools.NB12
