/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFELiteralLiftedFrequencies

/-!
# NB12zzzaa: literal H15 transform as one common-period value

The reduced ordered-pair support is expanded into four explicit orientation
atoms.  Their exact Archimedean scalars and lifted common-period frequencies
are inserted into the abstract correction system together with the reduced
missing atoms.

The main theorem identifies this common-period value, at every natural
frequency, with the literal correction-preserving H15 transform.
-/

open AddChar Complex ZMod
open scoped BigOperators ComplexConjugate

namespace NBMellinTools.NB12

def h15PostFEUnitSignSupport : Finset BettinChandeeUnitSign :=
  {.positive, .negative}

theorem sum_h15PostFEUnitSignSupport
    {R : Type} [AddCommMonoid R]
    (f : BettinChandeeUnitSign → R) :
    (∑ s ∈ h15PostFEUnitSignSupport, f s) =
      f .positive + f .negative := by
  simp [h15PostFEUnitSignSupport]

theorem sum_h15PostFEUnitSignSupport_product
    {R : Type} [AddCommMonoid R]
    (f : BettinChandeeUnitSign × BettinChandeeUnitSign → R) :
    (∑ s ∈ h15PostFEUnitSignSupport.product h15PostFEUnitSignSupport,
        f s) =
      f (.positive, .positive) + f (.positive, .negative) +
        f (.negative, .positive) + f (.negative, .negative) := by
  refine (Finset.sum_product h15PostFEUnitSignSupport
    h15PostFEUnitSignSupport f).trans ?_
  simp [h15PostFEUnitSignSupport, add_assoc]

theorem ofReal_mul_re (c : ℝ) (z : ℂ) :
    ((c : ℂ) * z).re = c * z.re := by
  simp [Complex.mul_re]

abbrev H15PostFEOrientedPairAtomIndex :=
  H15PostFEJointResiduePair ×
    (BettinChandeeUnitSign × BettinChandeeUnitSign)

def h15PostFEActualOrientedPairSupport
    (n g U Q : ℕ) : Finset H15PostFEOrientedPairAtomIndex :=
  (h15PostFEReducedOrderedPairResidueSupport n g U Q).product
    (h15PostFEUnitSignSupport.product h15PostFEUnitSignSupport)

noncomputable def h15PostFEActualCommonPeriodMissingCoefficient
    (n g U Q r : ℕ) (t : ℝ)
    (i : H15PostFEMissingAtomIndex) : ℂ :=
  h15PostFEResidueFiberMeanCoefficient n g U Q r t i.1

noncomputable def h15PostFEActualCommonPeriodPairCoefficient
    (n g U Q r : ℕ) (t : ℝ)
    (x : H15PostFEOrientedPairAtomIndex) : ℂ :=
  ((4 / (2 * h15PairedHyperbolicCoefficient t) : ℝ) : ℂ) *
    h15PostFEOrderedPairCollectedScalar n g U Q r t x.1 *
      (conj (h15PostFEOrientationArchimedeanFactor x.2.1 t) *
        h15PostFEOrientationArchimedeanFactor x.2.2 t)

noncomputable def h15PostFEActualCommonPeriodValue
    (n g U Q r : ℕ) (t : ℝ)
    [NeZero (h15PostFEActualCommonSuperperiod n g U Q)]
    (x : ZMod (h15PostFEActualCommonSuperperiod n g U Q)) : ℝ :=
  h15PostFECommonPeriodMissingValue
      (h15PostFEJointMissingAtomSupport
        (h15PostFEResidueModulusSupport n g U Q)
        (h15PostFEReducedMissingResidues n g U Q))
      (h15PostFEActualCommonPeriodMissingCoefficient n g U Q r t)
      (h15PostFELiftedMissingFrequency
        (h15PostFEActualCommonSuperperiod n g U Q)) x +
    h15PostFECommonPeriodPairValue
      (h15PostFEActualOrientedPairSupport n g U Q)
      (h15PostFEActualCommonPeriodPairCoefficient n g U Q r t)
      (fun y => h15PostFELiftedPairFrequency
        (h15PostFEActualCommonSuperperiod n g U Q)
        y.2.1 y.2.2 y.1) x

theorem h15PostFEActualCommonPeriodMissingValue_eq_jointMissing
    (n g U Q r : ℕ) (t : ℝ) (hQ : 0 < Q) :
    letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
      ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
    h15PostFECommonPeriodMissingValue
        (h15PostFEJointMissingAtomSupport
          (h15PostFEResidueModulusSupport n g U Q)
          (h15PostFEReducedMissingResidues n g U Q))
        (h15PostFEActualCommonPeriodMissingCoefficient n g U Q r t)
        (h15PostFELiftedMissingFrequency
          (h15PostFEActualCommonSuperperiod n g U Q))
        (r : ZMod (h15PostFEActualCommonSuperperiod n g U Q)) =
      h15PostFEJointMissingTransform
        (h15PostFEResidueModulusSupport n g U Q)
        (h15PostFEReducedMissingResidues n g U Q)
        (h15PostFEResidueFiberMeanCoefficient n g U Q r t) r := by
  letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
    ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
  rw [h15PostFEJointMissingTransform_eq_sum_atoms]
  unfold h15PostFECommonPeriodMissingValue
  apply Finset.sum_congr rfl
  intro i hi
  rw [← h15PostFEActualMissingPhase_eq_commonSuperperiod hQ hi r]
  simp [h15PostFEActualCommonPeriodMissingCoefficient,
    h15PostFEJointMissingAtom]

theorem h15PostFEActualCommonPeriodPairValue_eq_pairSector
    (n g U Q r : ℕ) (t : ℝ) (hQ : 0 < Q) :
    letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
      ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
    h15PostFECommonPeriodPairValue
        (h15PostFEActualOrientedPairSupport n g U Q)
        (h15PostFEActualCommonPeriodPairCoefficient n g U Q r t)
        (fun y => h15PostFELiftedPairFrequency
          (h15PostFEActualCommonSuperperiod n g U Q)
          y.2.1 y.2.2 y.1)
        (r : ZMod (h15PostFEActualCommonSuperperiod n g U Q)) =
      4 *
        (h15PostFEJointPairTransform .positive .positive
            (h15PostFEReducedOrderedPairResidueSupport n g U Q)
            (h15PostFEOrderedPairCollectedScalar n g U Q r t) r t +
          h15PostFEJointPairTransform .positive .negative
            (h15PostFEReducedOrderedPairResidueSupport n g U Q)
            (h15PostFEOrderedPairCollectedScalar n g U Q r t) r t +
          h15PostFEJointPairTransform .negative .positive
            (h15PostFEReducedOrderedPairResidueSupport n g U Q)
            (h15PostFEOrderedPairCollectedScalar n g U Q r t) r t +
          h15PostFEJointPairTransform .negative .negative
            (h15PostFEReducedOrderedPairResidueSupport n g U Q)
            (h15PostFEOrderedPairCollectedScalar n g U Q r t) r t) /
        (2 * h15PairedHyperbolicCoefficient t) := by
  letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
    ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
  rw [h15PostFEJointPairSector_eq_sum_fourOrientationAtoms]
  unfold h15PostFECommonPeriodPairValue
    h15PostFEActualOrientedPairSupport
  refine (Finset.sum_product
    (h15PostFEReducedOrderedPairResidueSupport n g U Q)
    (h15PostFEUnitSignSupport.product h15PostFEUnitSignSupport)
    (fun k =>
      (h15PostFEActualCommonPeriodPairCoefficient n g U Q r t k *
        stdAddChar ((r : ZMod (h15PostFEActualCommonSuperperiod n g U Q)) *
          h15PostFELiftedPairFrequency
            (h15PostFEActualCommonSuperperiod n g U Q)
            k.2.1 k.2.2 k.1)).re)).trans ?_
  apply Finset.sum_congr rfl
  intro κ hκ
  rw [sum_h15PostFEUnitSignSupport_product]
  unfold h15PostFEJointFourOrientationPairAtom
  rw [← h15PostFEActualPairPhase_eq_commonSuperperiod
      hQ hκ .positive .positive r,
    ← h15PostFEActualPairPhase_eq_commonSuperperiod
      hQ hκ .positive .negative r,
    ← h15PostFEActualPairPhase_eq_commonSuperperiod
      hQ hκ .negative .positive r,
    ← h15PostFEActualPairPhase_eq_commonSuperperiod
      hQ hκ .negative .negative r]
  have hscale (left right : BettinChandeeUnitSign) (z : ℂ) :
      (h15PostFEActualCommonPeriodPairCoefficient n g U Q r t
          (κ, (left, right)) * z).re =
        (4 / (2 * h15PairedHyperbolicCoefficient t)) *
          (h15PostFEOrderedPairCollectedScalar n g U Q r t κ *
            (conj (h15PostFEOrientationArchimedeanFactor left t) *
              h15PostFEOrientationArchimedeanFactor right t * z)).re := by
    unfold h15PostFEActualCommonPeriodPairCoefficient
    rw [show
        (((4 / (2 * h15PairedHyperbolicCoefficient t) : ℝ) : ℂ) *
              h15PostFEOrderedPairCollectedScalar n g U Q r t κ *
            (conj (h15PostFEOrientationArchimedeanFactor left t) *
              h15PostFEOrientationArchimedeanFactor right t)) * z =
          ((4 / (2 * h15PairedHyperbolicCoefficient t) : ℝ) : ℂ) *
            (h15PostFEOrderedPairCollectedScalar n g U Q r t κ *
              (conj (h15PostFEOrientationArchimedeanFactor left t) *
                h15PostFEOrientationArchimedeanFactor right t * z)) by ring]
    exact ofReal_mul_re _ _
  rw [hscale .positive .positive,
    hscale .positive .negative,
    hscale .negative .positive,
    hscale .negative .negative]
  simp only [div_eq_mul_inv]
  ring

/-- Pointwise literal instantiation of the common-period correction system. -/
theorem h15PostFEActualJointCorrectionTransform_eq_commonPeriodValue
    (n g U Q r : ℕ) (t : ℝ) (hQ : 0 < Q) :
    letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
      ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
    h15PostFEActualJointCorrectionTransform n g U Q r t =
      h15PostFEActualCommonPeriodValue n g U Q r t
        (r : ZMod (h15PostFEActualCommonSuperperiod n g U Q)) := by
  letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
    ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
  rw [h15PostFEActualJointCorrectionTransform_eq_reducedSupports]
  unfold h15PostFEJointCorrectionTransform
    h15PostFEActualCommonPeriodValue
  rw [h15PostFEActualCommonPeriodMissingValue_eq_jointMissing n g U Q r t hQ,
    h15PostFEActualCommonPeriodPairValue_eq_pairSector n g U Q r t hQ]

end NBMellinTools.NB12
