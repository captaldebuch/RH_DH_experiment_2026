/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFESignedCancellationRatio

/-!
# NB12zzzR: correction-preserving finite frequency Gram identity

This file starts the signed `L²` route after the absolute-envelope stop test.
It rewrites the complete joint correction transform as a sum of two kinds of
real atoms:

* missing-residue atoms, and
* genuinely joint pair atoms containing all four Estermann orientations.

The square over an arbitrary finite frequency set is then expanded exactly
into missing--missing, twice the missing--pair mixed Gram sector, and the
pair--pair Gram sector.  Each sector is also written as a literal finite
double atom sum.

No absolute value, Cauchy--Schwarz inequality, or spectral estimate is used.
The retained correction therefore remains inside the same Gram identity.
-/

open scoped BigOperators ComplexConjugate
open Complex

namespace NBMellinTools.NB12

/-! ## Unified atom supports -/

abbrev H15PostFEMissingAtomIndex := Σ _q : ℕ, ℕ

def h15PostFEJointMissingAtomSupport
    (modulusSupport : Finset ℕ)
    (missingSupport : ℕ → Finset ℕ) :
    Finset H15PostFEMissingAtomIndex :=
  modulusSupport.sigma missingSupport

noncomputable def h15PostFEJointMissingAtom
    (missingCoefficient : ℕ → ℝ) (r : ℕ)
    (i : H15PostFEMissingAtomIndex) : ℝ :=
  missingCoefficient i.1 *
    (h15PostFEReducedDoubledAdditivePhase r i.2 i.1).im

/-- One ordered-pair atom with all four orientation populations retained. -/
noncomputable def h15PostFEJointFourOrientationPairAtom
    (pairCoefficient : H15PostFEJointResiduePair → ℂ)
    (r : ℕ) (t : ℝ) (κ : H15PostFEJointResiduePair) : ℝ :=
  4 *
    ((pairCoefficient κ *
        (conj (h15PostFEOrientationArchimedeanFactor .positive t) *
          h15PostFEOrientationArchimedeanFactor .positive t *
          h15PostFECommonPairAdditivePhase .positive .positive r
            κ.1.1 κ.1.2 κ.2.1 κ.2.2)).re +
      (pairCoefficient κ *
        (conj (h15PostFEOrientationArchimedeanFactor .positive t) *
          h15PostFEOrientationArchimedeanFactor .negative t *
          h15PostFECommonPairAdditivePhase .positive .negative r
            κ.1.1 κ.1.2 κ.2.1 κ.2.2)).re +
      (pairCoefficient κ *
        (conj (h15PostFEOrientationArchimedeanFactor .negative t) *
          h15PostFEOrientationArchimedeanFactor .positive t *
          h15PostFECommonPairAdditivePhase .negative .positive r
            κ.1.1 κ.1.2 κ.2.1 κ.2.2)).re +
      (pairCoefficient κ *
        (conj (h15PostFEOrientationArchimedeanFactor .negative t) *
          h15PostFEOrientationArchimedeanFactor .negative t *
          h15PostFECommonPairAdditivePhase .negative .negative r
            κ.1.1 κ.1.2 κ.2.1 κ.2.2)).re) /
    (2 * h15PairedHyperbolicCoefficient t)

/-! ## Exact atom reassembly -/

theorem h15PostFEJointMissingTransform_eq_sum_atoms
    (modulusSupport : Finset ℕ)
    (missingSupport : ℕ → Finset ℕ)
    (missingCoefficient : ℕ → ℝ) (r : ℕ) :
    h15PostFEJointMissingTransform modulusSupport missingSupport
        missingCoefficient r =
      ∑ i ∈ h15PostFEJointMissingAtomSupport
          modulusSupport missingSupport,
        h15PostFEJointMissingAtom missingCoefficient r i := by
  unfold h15PostFEJointMissingTransform
    h15PostFEJointMissingAtomSupport h15PostFEJointMissingAtom
  rw [Finset.sum_sigma]
  simp only [Finset.mul_sum]

theorem h15PostFEJointPairSector_eq_sum_fourOrientationAtoms
    (pairSupport : Finset H15PostFEJointResiduePair)
    (pairCoefficient : H15PostFEJointResiduePair → ℂ)
    (r : ℕ) (t : ℝ) :
    4 *
        (h15PostFEJointPairTransform .positive .positive
            pairSupport pairCoefficient r t +
          h15PostFEJointPairTransform .positive .negative
            pairSupport pairCoefficient r t +
          h15PostFEJointPairTransform .negative .positive
            pairSupport pairCoefficient r t +
          h15PostFEJointPairTransform .negative .negative
            pairSupport pairCoefficient r t) /
        (2 * h15PairedHyperbolicCoefficient t) =
      ∑ κ ∈ pairSupport,
        h15PostFEJointFourOrientationPairAtom pairCoefficient r t κ := by
  unfold h15PostFEJointPairTransform
    h15PostFEJointFourOrientationPairAtom
  simp only [div_eq_mul_inv, mul_add, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]

/-- The complete correction transform as one missing-atom sum plus one
four-orientation joint-pair atom sum. -/
theorem h15PostFEJointCorrectionTransform_eq_atomSums
    (pairSupport : Finset H15PostFEJointResiduePair)
    (pairCoefficient : H15PostFEJointResiduePair → ℂ)
    (modulusSupport : Finset ℕ)
    (missingSupport : ℕ → Finset ℕ)
    (missingCoefficient : ℕ → ℝ)
    (r : ℕ) (t : ℝ) :
    h15PostFEJointCorrectionTransform pairSupport pairCoefficient
        modulusSupport missingSupport missingCoefficient r t =
      (∑ i ∈ h15PostFEJointMissingAtomSupport
          modulusSupport missingSupport,
        h15PostFEJointMissingAtom missingCoefficient r i) +
      ∑ κ ∈ pairSupport,
        h15PostFEJointFourOrientationPairAtom pairCoefficient r t κ := by
  unfold h15PostFEJointCorrectionTransform
  rw [h15PostFEJointMissingTransform_eq_sum_atoms,
    h15PostFEJointPairSector_eq_sum_fourOrientationAtoms]

/-! ## Finite frequency Gram sectors -/

noncomputable def h15PostFEJointFrequencyEnergy
    (frequencySupport : Finset ℕ)
    (pairSupport : Finset H15PostFEJointResiduePair)
    (pairCoefficient : H15PostFEJointResiduePair → ℂ)
    (modulusSupport : Finset ℕ)
    (missingSupport : ℕ → Finset ℕ)
    (missingCoefficient : ℕ → ℝ)
    (t : ℝ) : ℝ :=
  ∑ r ∈ frequencySupport,
    (h15PostFEJointCorrectionTransform pairSupport pairCoefficient
      modulusSupport missingSupport missingCoefficient r t) ^ 2

noncomputable def h15PostFEMissingFrequencyGram
    (frequencySupport : Finset ℕ)
    (modulusSupport : Finset ℕ)
    (missingSupport : ℕ → Finset ℕ)
    (missingCoefficient : ℕ → ℝ) : ℝ :=
  ∑ r ∈ frequencySupport,
    ∑ i ∈ h15PostFEJointMissingAtomSupport modulusSupport missingSupport,
      ∑ j ∈ h15PostFEJointMissingAtomSupport modulusSupport missingSupport,
        h15PostFEJointMissingAtom missingCoefficient r i *
          h15PostFEJointMissingAtom missingCoefficient r j

noncomputable def h15PostFEMixedFrequencyGram
    (frequencySupport : Finset ℕ)
    (pairSupport : Finset H15PostFEJointResiduePair)
    (pairCoefficient : H15PostFEJointResiduePair → ℂ)
    (modulusSupport : Finset ℕ)
    (missingSupport : ℕ → Finset ℕ)
    (missingCoefficient : ℕ → ℝ)
    (t : ℝ) : ℝ :=
  ∑ r ∈ frequencySupport,
    ∑ i ∈ h15PostFEJointMissingAtomSupport modulusSupport missingSupport,
      ∑ κ ∈ pairSupport,
        h15PostFEJointMissingAtom missingCoefficient r i *
          h15PostFEJointFourOrientationPairAtom pairCoefficient r t κ

noncomputable def h15PostFEPairFrequencyGram
    (frequencySupport : Finset ℕ)
    (pairSupport : Finset H15PostFEJointResiduePair)
    (pairCoefficient : H15PostFEJointResiduePair → ℂ)
    (t : ℝ) : ℝ :=
  ∑ r ∈ frequencySupport,
    ∑ κ ∈ pairSupport,
      ∑ κ' ∈ pairSupport,
        h15PostFEJointFourOrientationPairAtom pairCoefficient r t κ *
          h15PostFEJointFourOrientationPairAtom pairCoefficient r t κ'

theorem sq_sum_eq_double_sum
    {ι : Type} (support : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ support, f i) ^ 2 =
      ∑ i ∈ support, ∑ j ∈ support, f i * f j := by
  rw [pow_two, Finset.sum_mul]
  simp only [Finset.mul_sum]

theorem mul_sum_sum_eq_double_sum
    {ι κ : Type} (left : Finset ι) (right : Finset κ)
    (f : ι → ℝ) (g : κ → ℝ) :
    (∑ i ∈ left, f i) * (∑ j ∈ right, g j) =
      ∑ i ∈ left, ∑ j ∈ right, f i * g j := by
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]

/-- Exact correction-preserving Gram identity.  The mixed sector has factor
two because it appears in both orders in the square. -/
theorem h15PostFEJointFrequencyEnergy_eq_gramSectors
    (frequencySupport : Finset ℕ)
    (pairSupport : Finset H15PostFEJointResiduePair)
    (pairCoefficient : H15PostFEJointResiduePair → ℂ)
    (modulusSupport : Finset ℕ)
    (missingSupport : ℕ → Finset ℕ)
    (missingCoefficient : ℕ → ℝ)
    (t : ℝ) :
    h15PostFEJointFrequencyEnergy frequencySupport pairSupport
        pairCoefficient modulusSupport missingSupport missingCoefficient t =
      h15PostFEMissingFrequencyGram frequencySupport modulusSupport
          missingSupport missingCoefficient +
        2 * h15PostFEMixedFrequencyGram frequencySupport pairSupport
          pairCoefficient modulusSupport missingSupport missingCoefficient t +
        h15PostFEPairFrequencyGram frequencySupport pairSupport
          pairCoefficient t := by
  unfold h15PostFEJointFrequencyEnergy h15PostFEMissingFrequencyGram
    h15PostFEMixedFrequencyGram h15PostFEPairFrequencyGram
  rw [Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [h15PostFEJointCorrectionTransform_eq_atomSums]
  rw [add_sq, sq_sum_eq_double_sum, sq_sum_eq_double_sum]
  rw [mul_assoc, mul_sum_sum_eq_double_sum]

end NBMellinTools.NB12
