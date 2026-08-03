/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFECollisionMatchingAudit

/-!
# NB12zzzaM: collision congruence classification

This file replaces the abstract equal/opposite-frequency collision predicate
by an exact arithmetic condition on natural lift numerators.  It then splits
the two collision ledgers into three disjoint sectors:

* literal diagonal (or endpoint incidence);
* same-modulus alias; and
* genuinely cross-modulus collision.

These are finite identities.  No estimate for any sector is asserted.
-/

open scoped BigOperators

namespace NBMellinTools.NB12

/-! ## Natural representatives of the lifted frequencies -/

/-- Natural numerator whose cast to `ZMod M` is the total lifted missing
frequency. -/
noncomputable def h15PostFEMissingLiftNumerator
    (M : ℕ) (i : H15PostFEMissingAtomIndex) : ℕ :=
  if hq : i.1 = 0 then 0
  else
    letI : NeZero i.1 := ⟨hq⟩
    (h15PostFEMissingBaseFrequency i.2 i.1).val *
      h15PostFEPeriodLiftMultiplier i.1 M

/-- Natural numerator whose cast to `ZMod M` is the total lifted oriented-pair
frequency. -/
noncomputable def h15PostFEPairLiftNumerator
    (M : ℕ) (x : H15PostFEOrientedPairAtomIndex) : ℕ :=
  if hpair : x.1.1.2 * x.1.2.2 = 0 then 0
  else
    letI : NeZero (x.1.1.2 * x.1.2.2) := ⟨hpair⟩
    (h15PostFECommonPairBaseFrequency x.2.1 x.2.2
        x.1.1.1 x.1.1.2 x.1.2.1 x.1.2.2).val *
      h15PostFEPeriodLiftMultiplier (x.1.1.2 * x.1.2.2) M

theorem h15PostFELiftedMissingFrequency_eq_natCast_numerator
    (M : ℕ) [NeZero M] (i : H15PostFEMissingAtomIndex) :
    h15PostFELiftedMissingFrequency M i =
      (h15PostFEMissingLiftNumerator M i : ZMod M) := by
  by_cases hq : i.1 = 0
  · simp [h15PostFELiftedMissingFrequency,
      h15PostFEMissingLiftNumerator, hq]
  · letI : NeZero i.1 := ⟨hq⟩
    simp [h15PostFELiftedMissingFrequency,
      h15PostFEMissingLiftNumerator, h15PostFELiftFrequency, hq]

theorem h15PostFELiftedPairFrequency_eq_natCast_numerator
    (M : ℕ) [NeZero M] (x : H15PostFEOrientedPairAtomIndex) :
    h15PostFELiftedPairFrequency M x.2.1 x.2.2 x.1 =
      (h15PostFEPairLiftNumerator M x : ZMod M) := by
  by_cases hpair : x.1.1.2 * x.1.2.2 = 0
  · simp [h15PostFELiftedPairFrequency,
      h15PostFEPairLiftNumerator, hpair]
  · letI : NeZero (x.1.1.2 * x.1.2.2) := ⟨hpair⟩
    simp [h15PostFELiftedPairFrequency,
      h15PostFEPairLiftNumerator, h15PostFELiftFrequency, hpair]

/-- Equal frequencies are a natural congruence; opposite frequencies are
equivalently divisibility of the sum of the chosen lift numerators. -/
theorem h15PostFEFrequencyCollides_natCast_iff
    (M A B : ℕ) [NeZero M] :
    h15PostFEFrequencyCollides (A : ZMod M) (B : ZMod M) ↔
      A ≡ B [MOD M] ∨ M ∣ A + B := by
  unfold h15PostFEFrequencyCollides
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl ((ZMod.natCast_eq_natCast_iff A B M).mp h)
    · right
      have h' : ((A + B : ℕ) : ZMod M) = 0 := by
        simpa only [Nat.cast_add] using h
      exact (ZMod.natCast_eq_zero_iff (A + B) M).mp h'
  · intro h
    rcases h with h | h
    · exact Or.inl ((ZMod.natCast_eq_natCast_iff A B M).mpr h)
    · right
      have h' : ((A + B : ℕ) : ZMod M) = 0 :=
        (ZMod.natCast_eq_zero_iff (A + B) M).mpr h
      simpa only [Nat.cast_add] using h'

theorem h15PostFEMissingMissingCollides_iff_numerator
    (M : ℕ) [NeZero M]
    (i j : H15PostFEMissingAtomIndex) :
    h15PostFEFrequencyCollides
        (h15PostFELiftedMissingFrequency M i)
        (h15PostFELiftedMissingFrequency M j) ↔
      h15PostFEMissingLiftNumerator M i ≡
          h15PostFEMissingLiftNumerator M j [MOD M] ∨
        M ∣ h15PostFEMissingLiftNumerator M i +
          h15PostFEMissingLiftNumerator M j := by
  rw [h15PostFELiftedMissingFrequency_eq_natCast_numerator,
    h15PostFELiftedMissingFrequency_eq_natCast_numerator,
    h15PostFEFrequencyCollides_natCast_iff]

theorem h15PostFEMissingPairCollides_iff_numerator
    (M : ℕ) [NeZero M]
    (i : H15PostFEMissingAtomIndex)
    (x : H15PostFEOrientedPairAtomIndex) :
    h15PostFEFrequencyCollides
        (h15PostFELiftedMissingFrequency M i)
        (h15PostFELiftedPairFrequency M x.2.1 x.2.2 x.1) ↔
      h15PostFEMissingLiftNumerator M i ≡
          h15PostFEPairLiftNumerator M x [MOD M] ∨
        M ∣ h15PostFEMissingLiftNumerator M i +
          h15PostFEPairLiftNumerator M x := by
  rw [h15PostFELiftedMissingFrequency_eq_natCast_numerator,
    h15PostFELiftedPairFrequency_eq_natCast_numerator,
    h15PostFEFrequencyCollides_natCast_iff]

/-! ## A generic exact three-way sum partition -/

theorem sum_eq_filter_add_filter_not_filter_add_filter_not
    {α : Type}
    (s : Finset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q] (f : α → ℝ) :
    (∑ x ∈ s, f x) =
      (∑ x ∈ s.filter p, f x) +
        (∑ x ∈ (s.filter (fun y => ¬ p y)).filter q, f x) +
          ∑ x ∈ (s.filter (fun y => ¬ p y)).filter (fun y => ¬ q y), f x := by
  rw [(Finset.sum_filter_add_sum_filter_not s p f).symm]
  rw [(Finset.sum_filter_add_sum_filter_not
    (s.filter (fun y => ¬ p y)) q f).symm]
  abel

/-! ## Missing--missing: diagonal, same-modulus alias, cross-modulus -/

noncomputable def h15PostFEMissingMissingDiagonalCollisionLedger
    (M : ℕ) [NeZero M] (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) : ℝ :=
  let support := h15PostFEJointMissingAtomSupport
    (h15PostFEResidueModulusSupport n g U Q)
    (h15PostFEReducedMissingResidues n g U Q)
  let collisions := (support.product support).filter (fun p =>
    h15PostFEFrequencyCollides
      (h15PostFELiftedMissingFrequency M p.1)
      (h15PostFELiftedMissingFrequency M p.2))
  ∑ p ∈ collisions.filter (fun p => p.1 = p.2),
    h15PostFEWeightedEndpointLaurentMissingAtomCorrelation
      frequencySupport n g U Q t p.1 p.2

noncomputable def h15PostFEMissingMissingAliasCollisionLedger
    (M : ℕ) [NeZero M] (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) : ℝ :=
  let support := h15PostFEJointMissingAtomSupport
    (h15PostFEResidueModulusSupport n g U Q)
    (h15PostFEReducedMissingResidues n g U Q)
  let collisions := (support.product support).filter (fun p =>
    h15PostFEFrequencyCollides
      (h15PostFELiftedMissingFrequency M p.1)
      (h15PostFELiftedMissingFrequency M p.2))
  ∑ p ∈ (collisions.filter (fun p => p.1 ≠ p.2)).filter
      (fun p => p.1.1 = p.2.1),
    h15PostFEWeightedEndpointLaurentMissingAtomCorrelation
      frequencySupport n g U Q t p.1 p.2

noncomputable def h15PostFEMissingMissingCrossModulusCollisionLedger
    (M : ℕ) [NeZero M] (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) : ℝ :=
  let support := h15PostFEJointMissingAtomSupport
    (h15PostFEResidueModulusSupport n g U Q)
    (h15PostFEReducedMissingResidues n g U Q)
  let collisions := (support.product support).filter (fun p =>
    h15PostFEFrequencyCollides
      (h15PostFELiftedMissingFrequency M p.1)
      (h15PostFELiftedMissingFrequency M p.2))
  ∑ p ∈ (collisions.filter (fun p => p.1 ≠ p.2)).filter
      (fun p => p.1.1 ≠ p.2.1),
    h15PostFEWeightedEndpointLaurentMissingAtomCorrelation
      frequencySupport n g U Q t p.1 p.2

theorem h15PostFEWeightedMissingMissingCollisionLedger_eq_threeSectors
    (M : ℕ) [NeZero M] (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) :
    h15PostFEWeightedMissingMissingCollisionLedger
        M frequencySupport n g U Q t =
      h15PostFEMissingMissingDiagonalCollisionLedger
          M frequencySupport n g U Q t +
        h15PostFEMissingMissingAliasCollisionLedger
          M frequencySupport n g U Q t +
      h15PostFEMissingMissingCrossModulusCollisionLedger
          M frequencySupport n g U Q t := by
  classical
  let support := h15PostFEJointMissingAtomSupport
    (h15PostFEResidueModulusSupport n g U Q)
    (h15PostFEReducedMissingResidues n g U Q)
  let collisions := (support.product support).filter (fun p =>
    h15PostFEFrequencyCollides
      (h15PostFELiftedMissingFrequency M p.1)
      (h15PostFELiftedMissingFrequency M p.2))
  let summand := fun p : H15PostFEMissingAtomIndex ×
      H15PostFEMissingAtomIndex =>
    h15PostFEWeightedEndpointLaurentMissingAtomCorrelation
      frequencySupport n g U Q t p.1 p.2
  unfold h15PostFEWeightedMissingMissingCollisionLedger
    h15PostFEMissingMissingDiagonalCollisionLedger
    h15PostFEMissingMissingAliasCollisionLedger
    h15PostFEMissingMissingCrossModulusCollisionLedger
  change (∑ p ∈ collisions, summand p) =
    (∑ p ∈ collisions.filter (fun p => p.1 = p.2), summand p) +
      (∑ p ∈ (collisions.filter (fun p => p.1 ≠ p.2)).filter
          (fun p => p.1.1 = p.2.1), summand p) +
        ∑ p ∈ (collisions.filter (fun p => p.1 ≠ p.2)).filter
          (fun p => p.1.1 ≠ p.2.1), summand p
  exact sum_eq_filter_add_filter_not_filter_add_filter_not
    collisions (fun p => p.1 = p.2) (fun p => p.1.1 = p.2.1) summand

/-! ## Missing--pair: endpoint incidence, alias, external cross-modulus -/

/-- The missing atom is literally one of the two residue endpoints of the
oriented pair. -/
def h15PostFEMissingPairEndpointIncident
    (i : H15PostFEMissingAtomIndex)
    (x : H15PostFEOrientedPairAtomIndex) : Prop :=
  (i.1 = x.1.1.2 ∧ i.2 = x.1.1.1) ∨
    (i.1 = x.1.2.2 ∧ i.2 = x.1.2.1)

/-- The missing modulus occurs in the pair, irrespective of its residue. -/
def h15PostFEMissingPairSharesModulus
    (i : H15PostFEMissingAtomIndex)
    (x : H15PostFEOrientedPairAtomIndex) : Prop :=
  i.1 = x.1.1.2 ∨ i.1 = x.1.2.2

noncomputable instance h15PostFEMissingPairEndpointIncident_decidable
    (i : H15PostFEMissingAtomIndex)
    (x : H15PostFEOrientedPairAtomIndex) :
    Decidable (h15PostFEMissingPairEndpointIncident i x) := Classical.dec _

noncomputable instance h15PostFEMissingPairSharesModulus_decidable
    (i : H15PostFEMissingAtomIndex)
    (x : H15PostFEOrientedPairAtomIndex) :
    Decidable (h15PostFEMissingPairSharesModulus i x) := Classical.dec _

theorem h15PostFEMissingPairEndpointIncident_implies_sharesModulus
    {i : H15PostFEMissingAtomIndex}
    {x : H15PostFEOrientedPairAtomIndex}
    (h : h15PostFEMissingPairEndpointIncident i x) :
    h15PostFEMissingPairSharesModulus i x := by
  rcases h with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

noncomputable def h15PostFEMissingPairIncidentCollisionLedger
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
  ∑ p ∈ collisions.filter (fun p =>
      h15PostFEMissingPairEndpointIncident p.1 p.2),
    h15PostFEWeightedEndpointOrientedPairAtomCorrelation
      frequencySupport n g U Q t p.1 p.2

noncomputable def h15PostFEMissingPairAliasCollisionLedger
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
  ∑ p ∈ (collisions.filter (fun p =>
      ¬ h15PostFEMissingPairEndpointIncident p.1 p.2)).filter
        (fun p => h15PostFEMissingPairSharesModulus p.1 p.2),
    h15PostFEWeightedEndpointOrientedPairAtomCorrelation
      frequencySupport n g U Q t p.1 p.2

noncomputable def h15PostFEMissingPairCrossModulusCollisionLedger
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
  ∑ p ∈ (collisions.filter (fun p =>
      ¬ h15PostFEMissingPairEndpointIncident p.1 p.2)).filter
        (fun p => ¬ h15PostFEMissingPairSharesModulus p.1 p.2),
    h15PostFEWeightedEndpointOrientedPairAtomCorrelation
      frequencySupport n g U Q t p.1 p.2

theorem h15PostFEWeightedMissingPairCollisionLedger_eq_threeSectors
    (M : ℕ) [NeZero M] (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) :
    h15PostFEWeightedMissingPairCollisionLedger
        M frequencySupport n g U Q t =
      h15PostFEMissingPairIncidentCollisionLedger
          M frequencySupport n g U Q t +
        h15PostFEMissingPairAliasCollisionLedger
          M frequencySupport n g U Q t +
      h15PostFEMissingPairCrossModulusCollisionLedger
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
  let summand := fun p : H15PostFEMissingAtomIndex ×
      H15PostFEOrientedPairAtomIndex =>
    h15PostFEWeightedEndpointOrientedPairAtomCorrelation
      frequencySupport n g U Q t p.1 p.2
  unfold h15PostFEWeightedMissingPairCollisionLedger
    h15PostFEMissingPairIncidentCollisionLedger
    h15PostFEMissingPairAliasCollisionLedger
    h15PostFEMissingPairCrossModulusCollisionLedger
  change (∑ p ∈ collisions, summand p) =
    (∑ p ∈ collisions.filter (fun p =>
        h15PostFEMissingPairEndpointIncident p.1 p.2), summand p) +
      (∑ p ∈ (collisions.filter (fun p =>
          ¬ h15PostFEMissingPairEndpointIncident p.1 p.2)).filter
            (fun p => h15PostFEMissingPairSharesModulus p.1 p.2), summand p) +
        ∑ p ∈ (collisions.filter (fun p =>
          ¬ h15PostFEMissingPairEndpointIncident p.1 p.2)).filter
            (fun p => ¬ h15PostFEMissingPairSharesModulus p.1 p.2), summand p
  exact sum_eq_filter_add_filter_not_filter_add_filter_not
    collisions
    (fun p : H15PostFEMissingAtomIndex × H15PostFEOrientedPairAtomIndex =>
      h15PostFEMissingPairEndpointIncident p.1 p.2)
    (fun p : H15PostFEMissingAtomIndex × H15PostFEOrientedPairAtomIndex =>
      h15PostFEMissingPairSharesModulus p.1 p.2) summand

/-- The collision mismatch itself splits into diagonal/incidence, alias, and
cross-modulus sectors while the Cauchy norm product remains explicit. -/
theorem h15PostFECollisionMatchingResidual_eq_threeSectorAudit
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) (hQ : 0 < Q) :
    letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
      ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
    h15PostFECollisionMatchingResidual frequencySupport n g U Q t =
      Real.sqrt (h15PostFEEndpointFrequencyEnergy frequencySupport n g U Q) *
          Real.sqrt (h15PostFEWeightedLaurentPairFrequencyEnergy
            frequencySupport n g U Q t) -
        4 *
          (h15PostFEMissingMissingDiagonalCollisionLedger
              (h15PostFEActualCommonSuperperiod n g U Q)
              frequencySupport n g U Q t +
            h15PostFEMissingMissingAliasCollisionLedger
              (h15PostFEActualCommonSuperperiod n g U Q)
              frequencySupport n g U Q t +
            h15PostFEMissingMissingCrossModulusCollisionLedger
              (h15PostFEActualCommonSuperperiod n g U Q)
              frequencySupport n g U Q t) +
        (h15PostFEMissingPairIncidentCollisionLedger
            (h15PostFEActualCommonSuperperiod n g U Q)
            frequencySupport n g U Q t +
          h15PostFEMissingPairAliasCollisionLedger
            (h15PostFEActualCommonSuperperiod n g U Q)
            frequencySupport n g U Q t +
          h15PostFEMissingPairCrossModulusCollisionLedger
            (h15PostFEActualCommonSuperperiod n g U Q)
            frequencySupport n g U Q t) := by
  letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
    ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
  simp only [h15PostFECollisionMatchingResidual, dif_pos hQ]
  rw [h15PostFEWeightedMissingMissingCollisionLedger_eq_threeSectors,
    h15PostFEWeightedMissingPairCollisionLedger_eq_threeSectors]

end NBMellinTools.NB12
