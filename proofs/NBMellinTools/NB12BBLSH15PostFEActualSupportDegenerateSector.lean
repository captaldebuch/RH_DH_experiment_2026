/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEExternalShellDensityDegeneracy

/-!
# NB12zzzaT: actual-support external density split

The exact external-shell count loses all density saving when the missing
modulus `p` divides the ordered-pair modulus `q*q'`.  This file inserts that
criterion into the genuine signed H15 cross-modulus collision ledger.

The ledger is split exactly into:

* the degenerate sector `p ∣ q*q'`, where the missing-residue shell has full
  admissible density; and
* the favorable sector `p ∤ q*q'`, where the shell multiplier is not one.

The original signed atom correlation is retained in both sectors.  No
absolute value or asymptotic estimate is used.  The split exposes the next
analytic target but does not prove that either sector is small.
-/

open scoped BigOperators

namespace NBMellinTools.NB12

/-! ## Actual-support predicates -/

def h15PostFEMissingPairExternalDensityDegenerate
    (i : H15PostFEMissingAtomIndex)
    (x : H15PostFEOrientedPairAtomIndex) : Prop :=
  i.1 ∣ x.1.1.2 * x.1.2.2

noncomputable instance h15PostFEMissingPairExternalDensityDegenerate_decidable
    (i : H15PostFEMissingAtomIndex)
    (x : H15PostFEOrientedPairAtomIndex) :
    Decidable (h15PostFEMissingPairExternalDensityDegenerate i x) :=
  Classical.dec _

theorem h15PostFEMissingPair_not_sharesModulus_implies_external
    {i : H15PostFEMissingAtomIndex}
    {x : H15PostFEOrientedPairAtomIndex}
    (h : ¬ h15PostFEMissingPairSharesModulus i x) :
    h15PostFEIsExternalMissingPairModulus
      i.1 x.1.1.2 x.1.2.2 := by
  constructor
  · intro heq
    exact h (Or.inl heq)
  · intro heq
    exact h (Or.inr heq)

theorem h15PostFEActualExternalDensityDegenerate_iff_multiplier_eq_one
    {n g U Q : ℕ} {i : H15PostFEMissingAtomIndex}
    {x : H15PostFEOrientedPairAtomIndex}
    (hQ : 0 < Q)
    (hx : x ∈ h15PostFEActualOrientedPairSupport n g U Q) :
    h15PostFEMissingPairExternalDensityDegenerate i x ↔
      h15PostFEExternalPairMultiplier
        i.1 x.1.1.2 x.1.2.2 = 1 := by
  have hx' := Finset.mem_product.mp hx
  have hraw := h15PostFEReducedOrderedPairResidueSupport_subset
    n g U Q hx'.1
  have hactual := h15PostFEOrderedPairResidueSupport_subset_actual hraw
  have hq : 0 < x.1.1.2 :=
    Nat.zero_lt_of_lt (h15PostFEResidueKey_fst_lt_snd hQ hactual.1)
  have hq' : 0 < x.1.2.2 :=
    Nat.zero_lt_of_lt (h15PostFEResidueKey_fst_lt_snd hQ hactual.2)
  simpa [h15PostFEMissingPairExternalDensityDegenerate] using
    (h15PostFEExternalPairMultiplier_eq_one_iff_dvd_product
      i.1 x.1.1.2 x.1.2.2 hq hq').symm

/-! ## Signed cross-modulus sector split -/

noncomputable def h15PostFEMissingPairDegenerateCrossModulusCollisionLedger
    (M : ℕ) [NeZero M] (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) : ℝ :=
  let missingSupport := h15PostFEJointMissingAtomSupport
    (h15PostFEResidueModulusSupport n g U Q)
    (h15PostFEReducedMissingResidues n g U Q)
  let pairSupport := h15PostFEActualOrientedPairSupport n g U Q
  let collisions := (missingSupport.product pairSupport).filter (fun p =>
    h15PostFEFrequencyCollides
      (h15PostFELiftedMissingFrequency M p.1)
      (h15PostFELiftedPairFrequency M p.2.2.1 p.2.2.2 p.2.1))
  let external := (collisions.filter (fun p =>
    ¬ h15PostFEMissingPairEndpointIncident p.1 p.2)).filter
      (fun p => ¬ h15PostFEMissingPairSharesModulus p.1 p.2)
  ∑ p ∈ external.filter (fun p =>
      h15PostFEMissingPairExternalDensityDegenerate p.1 p.2),
    h15PostFEWeightedEndpointOrientedPairAtomCorrelation
      frequencySupport n g U Q t p.1 p.2

noncomputable def h15PostFEMissingPairFavorableCrossModulusCollisionLedger
    (M : ℕ) [NeZero M] (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) : ℝ :=
  let missingSupport := h15PostFEJointMissingAtomSupport
    (h15PostFEResidueModulusSupport n g U Q)
    (h15PostFEReducedMissingResidues n g U Q)
  let pairSupport := h15PostFEActualOrientedPairSupport n g U Q
  let collisions := (missingSupport.product pairSupport).filter (fun p =>
    h15PostFEFrequencyCollides
      (h15PostFELiftedMissingFrequency M p.1)
      (h15PostFELiftedPairFrequency M p.2.2.1 p.2.2.2 p.2.1))
  let external := (collisions.filter (fun p =>
    ¬ h15PostFEMissingPairEndpointIncident p.1 p.2)).filter
      (fun p => ¬ h15PostFEMissingPairSharesModulus p.1 p.2)
  ∑ p ∈ external.filter (fun p =>
      ¬ h15PostFEMissingPairExternalDensityDegenerate p.1 p.2),
    h15PostFEWeightedEndpointOrientedPairAtomCorrelation
      frequencySupport n g U Q t p.1 p.2

theorem h15PostFEMissingPairCrossModulusCollisionLedger_eq_degenerate_add_favorable
    (M : ℕ) [NeZero M] (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) :
    h15PostFEMissingPairCrossModulusCollisionLedger
        M frequencySupport n g U Q t =
      h15PostFEMissingPairDegenerateCrossModulusCollisionLedger
          M frequencySupport n g U Q t +
        h15PostFEMissingPairFavorableCrossModulusCollisionLedger
          M frequencySupport n g U Q t := by
  classical
  let missingSupport := h15PostFEJointMissingAtomSupport
    (h15PostFEResidueModulusSupport n g U Q)
    (h15PostFEReducedMissingResidues n g U Q)
  let pairSupport := h15PostFEActualOrientedPairSupport n g U Q
  let collisions := (missingSupport.product pairSupport).filter (fun p =>
    h15PostFEFrequencyCollides
      (h15PostFELiftedMissingFrequency M p.1)
      (h15PostFELiftedPairFrequency M p.2.2.1 p.2.2.2 p.2.1))
  let external := (collisions.filter (fun p =>
    ¬ h15PostFEMissingPairEndpointIncident p.1 p.2)).filter
      (fun p => ¬ h15PostFEMissingPairSharesModulus p.1 p.2)
  let degenerate := fun p : H15PostFEMissingAtomIndex ×
      H15PostFEOrientedPairAtomIndex =>
    h15PostFEMissingPairExternalDensityDegenerate p.1 p.2
  let summand := fun p : H15PostFEMissingAtomIndex ×
      H15PostFEOrientedPairAtomIndex =>
    h15PostFEWeightedEndpointOrientedPairAtomCorrelation
      frequencySupport n g U Q t p.1 p.2
  unfold h15PostFEMissingPairCrossModulusCollisionLedger
    h15PostFEMissingPairDegenerateCrossModulusCollisionLedger
    h15PostFEMissingPairFavorableCrossModulusCollisionLedger
  change (∑ p ∈ external, summand p) =
    (∑ p ∈ external.filter degenerate, summand p) +
      ∑ p ∈ external.filter (fun p => ¬ degenerate p), summand p
  exact (Finset.sum_filter_add_sum_filter_not
    external degenerate summand).symm

end NBMellinTools.NB12
