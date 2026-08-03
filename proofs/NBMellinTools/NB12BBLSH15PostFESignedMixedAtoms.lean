/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFESignedMixedExpansion

/-!
# NB12zzzaJ: atom expansion of the signed affine mixed sector

The literal alignment residual still contains two transforms.  This file
expands both into their original finite atoms while retaining the divisor-
square frequency weight, every orientation sign, and the Archimedean
normalization.  It is the exact input for the next collision/off-diagonal
partition.

No estimate or asymptotic hypothesis is used.
-/

open scoped BigOperators

namespace NBMellinTools.NB12

/-- The endpoint missing-residue atom. -/
noncomputable def h15PostFEEndpointMissingAtom
    (n g U Q r : ℕ) (i : H15PostFEMissingAtomIndex) : ℝ :=
  h15PostFEJointMissingAtom
    (h15PostFEResidueFiberEndpointMeanCoefficient n g U Q) r i

/-- The frequency-free Laurent missing-residue atom. -/
noncomputable def h15PostFELaurentMissingAtomWithoutFrequency
    (n g U Q r : ℕ) (t : ℝ) (i : H15PostFEMissingAtomIndex) : ℝ :=
  h15PostFEJointMissingAtom
    (h15PostFEResidueFiberLaurentMeanCoefficientWithoutFrequency
      n g U Q t) r i

/-- One four-orientation pair atom with the common divisor-frequency factor
removed but the Archimedean normalization retained. -/
noncomputable def h15PostFEFourOrientationPairAtomWithoutFrequency
    (n g U Q r : ℕ) (t : ℝ)
    (κ : H15PostFEJointResiduePair) : ℝ :=
  h15PostFEJointFourOrientationPairAtom
    (h15PostFEOrderedPairCollectedScalarWithoutFrequency n g U Q t) r t κ

/-- Lambda-weighted endpoint--Laurent-missing correlation of two individual
missing-residue atoms. -/
noncomputable def h15PostFEWeightedEndpointLaurentMissingAtomCorrelation
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ)
    (i j : H15PostFEMissingAtomIndex) : ℝ :=
  ∑ r ∈ frequencySupport,
    Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t) *
      h15PostFEEndpointMissingAtom n g U Q r i *
      h15PostFELaurentMissingAtomWithoutFrequency n g U Q r t j

/-- Lambda-weighted correlation of one endpoint atom with one normalized
four-orientation pair atom. -/
noncomputable def h15PostFEWeightedEndpointPairAtomCorrelation
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ)
    (i : H15PostFEMissingAtomIndex)
    (κ : H15PostFEJointResiduePair) : ℝ :=
  ∑ r ∈ frequencySupport,
    Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t) *
      h15PostFEEndpointMissingAtom n g U Q r i *
      h15PostFEFourOrientationPairAtomWithoutFrequency n g U Q r t κ

theorem sum_biDouble_biSum_comm
    {R I J : Type}
    (rs : Finset R) (is : Finset I) (js : Finset J)
    (f : R → I → J → ℝ) :
    (∑ r ∈ rs, ∑ i ∈ is, ∑ j ∈ js, f r i j) =
      ∑ i ∈ is, ∑ j ∈ js, ∑ r ∈ rs, f r i j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.sum_comm]

/-- Exact atom expansion of the endpoint--Laurent-missing mixed ledger. -/
theorem h15PostFEWeightedEndpointLaurentMissingMixedEnergy_eq_atomCorrelations
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) :
    h15PostFEWeightedEndpointLaurentMissingMixedEnergy
        frequencySupport n g U Q t =
      ∑ i ∈ h15PostFEJointMissingAtomSupport
          (h15PostFEResidueModulusSupport n g U Q)
          (h15PostFEReducedMissingResidues n g U Q),
        ∑ j ∈ h15PostFEJointMissingAtomSupport
            (h15PostFEResidueModulusSupport n g U Q)
            (h15PostFEReducedMissingResidues n g U Q),
          h15PostFEWeightedEndpointLaurentMissingAtomCorrelation
            frequencySupport n g U Q t i j := by
  unfold h15PostFEWeightedEndpointLaurentMissingMixedEnergy
    h15PostFEEndpointFrequencyTransform
    h15PostFELaurentMissingFrequencyTransform
  simp_rw [h15PostFEJointMissingTransform_eq_sum_atoms]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [sum_biDouble_biSum_comm]
  rw [Finset.sum_comm]
  rfl

/-- Exact atom expansion of the normalized endpoint--four-orientation pair
ledger.  The factor `4/(2H(t))` has not been discarded: it is inside every
pair atom on the right. -/
theorem four_mul_h15PostFEWeightedEndpointPairMixedEnergy_div_eq_atomCorrelations
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) :
    4 * h15PostFEWeightedEndpointPairMixedEnergy
          frequencySupport n g U Q t /
        (2 * h15PairedHyperbolicCoefficient t) =
      ∑ i ∈ h15PostFEJointMissingAtomSupport
          (h15PostFEResidueModulusSupport n g U Q)
          (h15PostFEReducedMissingResidues n g U Q),
        ∑ κ ∈ h15PostFEReducedOrderedPairResidueSupport n g U Q,
          h15PostFEWeightedEndpointPairAtomCorrelation
            frequencySupport n g U Q t i κ := by
  unfold h15PostFEWeightedEndpointPairMixedEnergy
    h15PostFEEndpointFrequencyTransform
    h15PostFEFourOrientationPairFrequencyTransform
  rw [show
      4 * (∑ r ∈ frequencySupport,
          Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t) *
            h15PostFEJointMissingTransform
              (h15PostFEResidueModulusSupport n g U Q)
              (h15PostFEReducedMissingResidues n g U Q)
              (h15PostFEResidueFiberEndpointMeanCoefficient n g U Q) r *
            (h15PostFEJointPairTransform .positive .positive
                (h15PostFEReducedOrderedPairResidueSupport n g U Q)
                (h15PostFEOrderedPairCollectedScalarWithoutFrequency
                  n g U Q t) r t +
              h15PostFEJointPairTransform .positive .negative
                (h15PostFEReducedOrderedPairResidueSupport n g U Q)
                (h15PostFEOrderedPairCollectedScalarWithoutFrequency
                  n g U Q t) r t +
              h15PostFEJointPairTransform .negative .positive
                (h15PostFEReducedOrderedPairResidueSupport n g U Q)
                (h15PostFEOrderedPairCollectedScalarWithoutFrequency
                  n g U Q t) r t +
              h15PostFEJointPairTransform .negative .negative
                (h15PostFEReducedOrderedPairResidueSupport n g U Q)
                (h15PostFEOrderedPairCollectedScalarWithoutFrequency
                  n g U Q t) r t)) /
          (2 * h15PairedHyperbolicCoefficient t) =
        ∑ r ∈ frequencySupport,
          Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t) *
            h15PostFEJointMissingTransform
              (h15PostFEResidueModulusSupport n g U Q)
              (h15PostFEReducedMissingResidues n g U Q)
              (h15PostFEResidueFiberEndpointMeanCoefficient n g U Q) r *
            (4 *
              (h15PostFEJointPairTransform .positive .positive
                  (h15PostFEReducedOrderedPairResidueSupport n g U Q)
                  (h15PostFEOrderedPairCollectedScalarWithoutFrequency
                    n g U Q t) r t +
                h15PostFEJointPairTransform .positive .negative
                  (h15PostFEReducedOrderedPairResidueSupport n g U Q)
                  (h15PostFEOrderedPairCollectedScalarWithoutFrequency
                    n g U Q t) r t +
                h15PostFEJointPairTransform .negative .positive
                  (h15PostFEReducedOrderedPairResidueSupport n g U Q)
                  (h15PostFEOrderedPairCollectedScalarWithoutFrequency
                    n g U Q t) r t +
                h15PostFEJointPairTransform .negative .negative
                  (h15PostFEReducedOrderedPairResidueSupport n g U Q)
                  (h15PostFEOrderedPairCollectedScalarWithoutFrequency
                    n g U Q t) r t) /
              (2 * h15PairedHyperbolicCoefficient t)) by
      rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro r _hr
      ring]
  simp_rw [h15PostFEJointMissingTransform_eq_sum_atoms,
    h15PostFEJointPairSector_eq_sum_fourOrientationAtoms]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [sum_biDouble_biSum_comm]
  rw [Finset.sum_comm]
  rfl

/-- The explicit alignment residual as a finite atom correlation ledger. -/
theorem h15PostFEAffineAlignmentResidual_eq_atomCorrelations
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) :
    h15PostFEAffineAlignmentResidual frequencySupport n g U Q t =
      Real.sqrt (h15PostFEEndpointFrequencyEnergy frequencySupport n g U Q) *
          Real.sqrt (h15PostFEWeightedLaurentPairFrequencyEnergy
            frequencySupport n g U Q t) -
        4 *
          (∑ i ∈ h15PostFEJointMissingAtomSupport
              (h15PostFEResidueModulusSupport n g U Q)
              (h15PostFEReducedMissingResidues n g U Q),
            ∑ j ∈ h15PostFEJointMissingAtomSupport
                (h15PostFEResidueModulusSupport n g U Q)
                (h15PostFEReducedMissingResidues n g U Q),
              h15PostFEWeightedEndpointLaurentMissingAtomCorrelation
                frequencySupport n g U Q t i j) +
        ∑ i ∈ h15PostFEJointMissingAtomSupport
            (h15PostFEResidueModulusSupport n g U Q)
            (h15PostFEReducedMissingResidues n g U Q),
          ∑ κ ∈ h15PostFEReducedOrderedPairResidueSupport n g U Q,
            h15PostFEWeightedEndpointPairAtomCorrelation
              frequencySupport n g U Q t i κ := by
  unfold h15PostFEAffineAlignmentResidual
  rw [h15PostFEWeightedEndpointLaurentMissingMixedEnergy_eq_atomCorrelations,
    four_mul_h15PostFEWeightedEndpointPairMixedEnergy_div_eq_atomCorrelations]

end NBMellinTools.NB12
