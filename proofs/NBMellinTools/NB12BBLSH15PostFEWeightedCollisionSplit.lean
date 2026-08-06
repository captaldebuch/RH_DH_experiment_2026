/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFESignedMixedAtoms

/-!
# NB12zzzaK: weighted collision/off-diagonal split

The signed mixed ledgers have a varying divisor-square weight and an arbitrary
finite natural-frequency support.  Therefore complete-period character
orthogonality cannot be applied to them.  This file instead performs the
honest finite partition: first expand the four pair orientations, then split
the literal atom pairs according to equality or opposition of their lifted
frequencies.

The off-diagonal terms are retained exactly.  No claim that they vanish is
made here.
-/

open scoped BigOperators ComplexConjugate

namespace NBMellinTools.NB12

/-- One normalized orientation atom after removing the common divisor-
frequency norm square. -/
noncomputable def h15PostFEOrientedPairAtomWithoutFrequency
    (n g U Q r : ℕ) (t : ℝ)
    (x : H15PostFEOrientedPairAtomIndex) : ℝ :=
  (4 / (2 * h15PairedHyperbolicCoefficient t)) *
    (h15PostFEOrderedPairCollectedScalarWithoutFrequency n g U Q t x.1 *
      (conj (h15PostFEOrientationArchimedeanFactor x.2.1 t) *
        h15PostFEOrientationArchimedeanFactor x.2.2 t *
        h15PostFECommonPairAdditivePhase x.2.1 x.2.2 r
          x.1.1.1 x.1.1.2 x.1.2.1 x.1.2.2)).re

/-- The normalized four-orientation atom is literally the sum of its four
oriented constituents. -/
theorem h15PostFEFourOrientationPairAtomWithoutFrequency_eq_sum_orientations
    (n g U Q r : ℕ) (t : ℝ) (κ : H15PostFEJointResiduePair) :
    h15PostFEFourOrientationPairAtomWithoutFrequency n g U Q r t κ =
      ∑ signs ∈ h15PostFEUnitSignSupport.product h15PostFEUnitSignSupport,
        h15PostFEOrientedPairAtomWithoutFrequency
          n g U Q r t (κ, signs) := by
  unfold h15PostFEFourOrientationPairAtomWithoutFrequency
    h15PostFEOrientedPairAtomWithoutFrequency
    h15PostFEJointFourOrientationPairAtom
  rw [sum_h15PostFEUnitSignSupport_product]
  ring

/-- Lambda-weighted correlation of one endpoint missing atom with one
individual normalized orientation atom. -/
noncomputable def h15PostFEWeightedEndpointOrientedPairAtomCorrelation
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ)
    (i : H15PostFEMissingAtomIndex)
    (x : H15PostFEOrientedPairAtomIndex) : ℝ :=
  ∑ r ∈ frequencySupport,
    Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t) *
      h15PostFEEndpointMissingAtom n g U Q r i *
      h15PostFEOrientedPairAtomWithoutFrequency n g U Q r t x

theorem h15PostFEWeightedEndpointPairAtomCorrelation_eq_sum_orientations
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ)
    (i : H15PostFEMissingAtomIndex)
    (κ : H15PostFEJointResiduePair) :
    h15PostFEWeightedEndpointPairAtomCorrelation
        frequencySupport n g U Q t i κ =
      ∑ signs ∈ h15PostFEUnitSignSupport.product h15PostFEUnitSignSupport,
        h15PostFEWeightedEndpointOrientedPairAtomCorrelation
          frequencySupport n g U Q t i (κ, signs) := by
  unfold h15PostFEWeightedEndpointPairAtomCorrelation
    h15PostFEWeightedEndpointOrientedPairAtomCorrelation
  simp_rw [h15PostFEFourOrientationPairAtomWithoutFrequency_eq_sum_orientations]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Equal or opposite frequencies are the two collision relations arising
from products of real/imaginary additive characters. -/
def h15PostFEFrequencyCollides
    {M : ℕ} [NeZero M] (x y : ZMod M) : Prop :=
  x = y ∨ x + y = 0

noncomputable instance h15PostFEFrequencyCollides_decidable
    {M : ℕ} [NeZero M] (x y : ZMod M) :
    Decidable (h15PostFEFrequencyCollides x y) :=
  Classical.dec _

/-! ## Missing--missing partition -/

noncomputable def h15PostFEWeightedMissingMissingCollisionLedger
    (M : ℕ) [NeZero M]
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) : ℝ :=
  let support := h15PostFEJointMissingAtomSupport
    (h15PostFEResidueModulusSupport n g U Q)
    (h15PostFEReducedMissingResidues n g U Q)
  ∑ p ∈ (support.product support).filter (fun p =>
      h15PostFEFrequencyCollides
        (h15PostFELiftedMissingFrequency M p.1)
        (h15PostFELiftedMissingFrequency M p.2)),
    h15PostFEWeightedEndpointLaurentMissingAtomCorrelation
      frequencySupport n g U Q t p.1 p.2

noncomputable def h15PostFEWeightedMissingMissingOffDiagonalLedger
    (M : ℕ) [NeZero M]
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) : ℝ :=
  let support := h15PostFEJointMissingAtomSupport
    (h15PostFEResidueModulusSupport n g U Q)
    (h15PostFEReducedMissingResidues n g U Q)
  ∑ p ∈ (support.product support).filter (fun p =>
      ¬ h15PostFEFrequencyCollides
        (h15PostFELiftedMissingFrequency M p.1)
        (h15PostFELiftedMissingFrequency M p.2)),
    h15PostFEWeightedEndpointLaurentMissingAtomCorrelation
      frequencySupport n g U Q t p.1 p.2

theorem h15PostFEWeightedMissingAtomCorrelations_eq_collision_add_offDiagonal
    (M : ℕ) [NeZero M]
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) :
    (∑ i ∈ h15PostFEJointMissingAtomSupport
        (h15PostFEResidueModulusSupport n g U Q)
        (h15PostFEReducedMissingResidues n g U Q),
      ∑ j ∈ h15PostFEJointMissingAtomSupport
          (h15PostFEResidueModulusSupport n g U Q)
          (h15PostFEReducedMissingResidues n g U Q),
        h15PostFEWeightedEndpointLaurentMissingAtomCorrelation
          frequencySupport n g U Q t i j) =
      h15PostFEWeightedMissingMissingCollisionLedger
          M frequencySupport n g U Q t +
        h15PostFEWeightedMissingMissingOffDiagonalLedger
          M frequencySupport n g U Q t := by
  classical
  let support := h15PostFEJointMissingAtomSupport
    (h15PostFEResidueModulusSupport n g U Q)
    (h15PostFEReducedMissingResidues n g U Q)
  let collision : H15PostFEMissingAtomIndex ×
      H15PostFEMissingAtomIndex → Prop := fun p =>
    h15PostFEFrequencyCollides
      (h15PostFELiftedMissingFrequency M p.1)
      (h15PostFELiftedMissingFrequency M p.2)
  let summand : H15PostFEMissingAtomIndex ×
      H15PostFEMissingAtomIndex → ℝ := fun p =>
    h15PostFEWeightedEndpointLaurentMissingAtomCorrelation
      frequencySupport n g U Q t p.1 p.2
  change (∑ i ∈ support, ∑ j ∈ support, summand (i, j)) = _
  rw [← Finset.sum_product]
  change (∑ p ∈ support.product support, summand p) =
    (∑ p ∈ (support.product support).filter collision, summand p) +
      ∑ p ∈ (support.product support).filter (fun p => ¬ collision p), summand p
  exact (Finset.sum_filter_add_sum_filter_not
    (support.product support) collision summand).symm

/-! ## Missing--oriented-pair partition -/

noncomputable def h15PostFEWeightedMissingPairCollisionLedger
    (M : ℕ) [NeZero M]
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) : ℝ :=
  let missingSupport := h15PostFEJointMissingAtomSupport
    (h15PostFEResidueModulusSupport n g U Q)
    (h15PostFEReducedMissingResidues n g U Q)
  let pairSupport := h15PostFEActualOrientedPairSupport n g U Q
  ∑ p ∈ (missingSupport.product pairSupport).filter (fun p =>
      h15PostFEFrequencyCollides
        (h15PostFELiftedMissingFrequency M p.1)
        (h15PostFELiftedPairFrequency M p.2.2.1 p.2.2.2 p.2.1)),
    h15PostFEWeightedEndpointOrientedPairAtomCorrelation
      frequencySupport n g U Q t p.1 p.2

noncomputable def h15PostFEWeightedMissingPairOffDiagonalLedger
    (M : ℕ) [NeZero M]
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) : ℝ :=
  let missingSupport := h15PostFEJointMissingAtomSupport
    (h15PostFEResidueModulusSupport n g U Q)
    (h15PostFEReducedMissingResidues n g U Q)
  let pairSupport := h15PostFEActualOrientedPairSupport n g U Q
  ∑ p ∈ (missingSupport.product pairSupport).filter (fun p =>
      ¬ h15PostFEFrequencyCollides
        (h15PostFELiftedMissingFrequency M p.1)
        (h15PostFELiftedPairFrequency M p.2.2.1 p.2.2.2 p.2.1)),
    h15PostFEWeightedEndpointOrientedPairAtomCorrelation
      frequencySupport n g U Q t p.1 p.2

theorem h15PostFEWeightedPairAtomCorrelations_eq_collision_add_offDiagonal
    (M : ℕ) [NeZero M]
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) :
    (∑ i ∈ h15PostFEJointMissingAtomSupport
        (h15PostFEResidueModulusSupport n g U Q)
        (h15PostFEReducedMissingResidues n g U Q),
      ∑ κ ∈ h15PostFEReducedOrderedPairResidueSupport n g U Q,
        h15PostFEWeightedEndpointPairAtomCorrelation
          frequencySupport n g U Q t i κ) =
      h15PostFEWeightedMissingPairCollisionLedger
          M frequencySupport n g U Q t +
        h15PostFEWeightedMissingPairOffDiagonalLedger
          M frequencySupport n g U Q t := by
  classical
  let missingSupport := h15PostFEJointMissingAtomSupport
    (h15PostFEResidueModulusSupport n g U Q)
    (h15PostFEReducedMissingResidues n g U Q)
  let pairSupport := h15PostFEReducedOrderedPairResidueSupport n g U Q
  let orientedSupport := h15PostFEActualOrientedPairSupport n g U Q
  let collision : H15PostFEMissingAtomIndex ×
      H15PostFEOrientedPairAtomIndex → Prop := fun p =>
    h15PostFEFrequencyCollides
      (h15PostFELiftedMissingFrequency M p.1)
      (h15PostFELiftedPairFrequency M p.2.2.1 p.2.2.2 p.2.1)
  let summand : H15PostFEMissingAtomIndex ×
      H15PostFEOrientedPairAtomIndex → ℝ := fun p =>
    h15PostFEWeightedEndpointOrientedPairAtomCorrelation
      frequencySupport n g U Q t p.1 p.2
  simp_rw [h15PostFEWeightedEndpointPairAtomCorrelation_eq_sum_orientations]
  change (∑ i ∈ missingSupport,
      ∑ κ ∈ pairSupport,
        ∑ signs ∈ h15PostFEUnitSignSupport.product h15PostFEUnitSignSupport,
          summand (i, (κ, signs))) = _
  calc
    (∑ i ∈ missingSupport,
        ∑ κ ∈ pairSupport,
          ∑ signs ∈ h15PostFEUnitSignSupport.product h15PostFEUnitSignSupport,
            summand (i, (κ, signs))) =
        ∑ i ∈ missingSupport,
          ∑ x ∈ orientedSupport, summand (i, x) := by
      apply Finset.sum_congr rfl
      intro i _hi
      unfold orientedSupport h15PostFEActualOrientedPairSupport
      exact (Finset.sum_product pairSupport
        (h15PostFEUnitSignSupport.product h15PostFEUnitSignSupport)
        (fun x => summand (i, x))).symm
    _ = _ := by
      rw [← Finset.sum_product]
      change (∑ p ∈ missingSupport.product orientedSupport, summand p) =
        (∑ p ∈ (missingSupport.product orientedSupport).filter collision,
            summand p) +
          ∑ p ∈ (missingSupport.product orientedSupport).filter
            (fun p => ¬ collision p), summand p
      exact (Finset.sum_filter_add_sum_filter_not
        (missingSupport.product orientedSupport) collision summand).symm

/-- Exact collision/off-diagonal normal form for the alignment residual at
the actual H15 common superperiod.  This theorem is a partition, not an
orthogonality estimate: both off-diagonal ledgers remain present. -/
theorem h15PostFEAffineAlignmentResidual_eq_collision_add_offDiagonal
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) (hQ : 0 < Q) :
    letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
      ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
    h15PostFEAffineAlignmentResidual frequencySupport n g U Q t =
      Real.sqrt (h15PostFEEndpointFrequencyEnergy frequencySupport n g U Q) *
          Real.sqrt (h15PostFEWeightedLaurentPairFrequencyEnergy
            frequencySupport n g U Q t) -
        4 *
          (h15PostFEWeightedMissingMissingCollisionLedger
              (h15PostFEActualCommonSuperperiod n g U Q)
              frequencySupport n g U Q t +
            h15PostFEWeightedMissingMissingOffDiagonalLedger
              (h15PostFEActualCommonSuperperiod n g U Q)
              frequencySupport n g U Q t) +
        (h15PostFEWeightedMissingPairCollisionLedger
            (h15PostFEActualCommonSuperperiod n g U Q)
            frequencySupport n g U Q t +
          h15PostFEWeightedMissingPairOffDiagonalLedger
            (h15PostFEActualCommonSuperperiod n g U Q)
            frequencySupport n g U Q t) := by
  letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
    ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
  rw [h15PostFEAffineAlignmentResidual_eq_atomCorrelations,
    h15PostFEWeightedMissingAtomCorrelations_eq_collision_add_offDiagonal
      (h15PostFEActualCommonSuperperiod n g U Q)
      frequencySupport n g U Q t,
    h15PostFEWeightedPairAtomCorrelations_eq_collision_add_offDiagonal
      (h15PostFEActualCommonSuperperiod n g U Q)
      frequencySupport n g U Q t]

end NBMellinTools.NB12
