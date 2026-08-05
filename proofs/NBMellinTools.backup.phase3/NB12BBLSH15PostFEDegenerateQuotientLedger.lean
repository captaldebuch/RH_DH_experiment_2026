/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEDegenerateQuotientReindex

/-!
# NB12zzzaV: signed quotient ledger for the degenerate external sector

The density-degenerate cross-modulus collision sector is now collected by the
canonical quotient `k = q*q'/p`.  The construction retains the literal H15
atom correlation in every fiber.  In particular, Möbius signs, logarithmic
tapers, the missing coefficient, all four pair orientations, and the retained
correction remain inside the same signed finite sum.

The quotient support lies in the explicit half-open scale window
`Q < 2*k` and `k < 4*Q`.  This is an exact reindexing, not an estimate.
The remaining task is therefore a quotient-indexed signed dispersion bound.
-/

open scoped BigOperators

namespace NBMellinTools.NB12

abbrev H15PostFEMissingPairAtomIndex :=
  H15PostFEMissingAtomIndex × H15PostFEOrientedPairAtomIndex

/-! ## The genuine degenerate collision support -/

noncomputable def h15PostFEDegenerateCrossModulusCollisionSupport
    (M : ℕ) [NeZero M] (n g U Q : ℕ) :
    Finset H15PostFEMissingPairAtomIndex :=
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
  external.filter fun p =>
    h15PostFEMissingPairExternalDensityDegenerate p.1 p.2

theorem h15PostFEDegenerateCrossModulusCollisionSupport_mem_base
    {M n g U Q : ℕ} [NeZero M]
    {p : H15PostFEMissingPairAtomIndex}
    (hp : p ∈ h15PostFEDegenerateCrossModulusCollisionSupport
      M n g U Q) :
    p.1 ∈ h15PostFEJointMissingAtomSupport
        (h15PostFEResidueModulusSupport n g U Q)
        (h15PostFEReducedMissingResidues n g U Q) ∧
      p.2 ∈ h15PostFEActualOrientedPairSupport n g U Q := by
  unfold h15PostFEDegenerateCrossModulusCollisionSupport at hp
  exact Finset.mem_product.mp
    (Finset.mem_filter.mp
      (Finset.mem_filter.mp
        (Finset.mem_filter.mp
          (Finset.mem_filter.mp hp).1).1).1).1

theorem h15PostFEDegenerateCrossModulusCollisionSupport_is_degenerate
    {M n g U Q : ℕ} [NeZero M]
    {p : H15PostFEMissingPairAtomIndex}
    (hp : p ∈ h15PostFEDegenerateCrossModulusCollisionSupport
      M n g U Q) :
    h15PostFEMissingPairExternalDensityDegenerate p.1 p.2 := by
  unfold h15PostFEDegenerateCrossModulusCollisionSupport at hp
  exact (Finset.mem_filter.mp hp).2

/-! ## Quotient collection -/

def h15PostFEMissingPairDegenerateQuotient
    (p : H15PostFEMissingPairAtomIndex) : ℕ :=
  h15PostFEDegenerateQuotient p.1.1 p.2.1.1.2 p.2.1.2.2

noncomputable def h15PostFEDegenerateQuotientSupport
    (M : ℕ) [NeZero M] (n g U Q : ℕ) : Finset ℕ :=
  (h15PostFEDegenerateCrossModulusCollisionSupport M n g U Q).image
    h15PostFEMissingPairDegenerateQuotient

noncomputable def h15PostFEDegenerateQuotientFiberCorrelation
    (M : ℕ) [NeZero M] (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) (k : ℕ) : ℝ :=
  ∑ p ∈ (h15PostFEDegenerateCrossModulusCollisionSupport
      M n g U Q).filter
      (fun p => h15PostFEMissingPairDegenerateQuotient p = k),
    h15PostFEWeightedEndpointOrientedPairAtomCorrelation
      frequencySupport n g U Q t p.1 p.2

theorem h15PostFEDegenerateCollisionLedger_eq_supportSum
    (M : ℕ) [NeZero M] (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) :
    h15PostFEMissingPairDegenerateCrossModulusCollisionLedger
        M frequencySupport n g U Q t =
      ∑ p ∈ h15PostFEDegenerateCrossModulusCollisionSupport M n g U Q,
        h15PostFEWeightedEndpointOrientedPairAtomCorrelation
          frequencySupport n g U Q t p.1 p.2 := by
  rfl

/-- Exact signed collection by `k=q*q'/p`.  No triangle inequality is used. -/
theorem h15PostFEDegenerateCollisionLedger_eq_sum_quotientFibers
    (M : ℕ) [NeZero M] (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) :
    h15PostFEMissingPairDegenerateCrossModulusCollisionLedger
        M frequencySupport n g U Q t =
      ∑ k ∈ h15PostFEDegenerateQuotientSupport M n g U Q,
        h15PostFEDegenerateQuotientFiberCorrelation
          M frequencySupport n g U Q t k := by
  classical
  rw [h15PostFEDegenerateCollisionLedger_eq_supportSum]
  let S := h15PostFEDegenerateCrossModulusCollisionSupport M n g U Q
  let key := h15PostFEMissingPairDegenerateQuotient
  let summand := fun p : H15PostFEMissingPairAtomIndex =>
    h15PostFEWeightedEndpointOrientedPairAtomCorrelation
      frequencySupport n g U Q t p.1 p.2
  have hcollect := sum_mul_kernel_eq_sum_image_collected
    S key summand (fun _k : ℕ => (1 : ℝ))
  simpa [S, key, summand, h15PostFEDegenerateQuotientSupport,
    h15PostFEDegenerateQuotientFiberCorrelation] using hcollect

/-! ## The collected quotient occupies another dyadic-scale window -/

theorem h15PostFEDegenerateQuotientSupport_scale
    {M n g U Q k : ℕ} [NeZero M] (hQ : 0 < Q)
    (hk : k ∈ h15PostFEDegenerateQuotientSupport M n g U Q) :
    Q < 2 * k ∧ k < 4 * Q := by
  classical
  rw [h15PostFEDegenerateQuotientSupport, Finset.mem_image] at hk
  rcases hk with ⟨p, hp, rfl⟩
  have hbase := h15PostFEDegenerateCrossModulusCollisionSupport_mem_base hp
  exact h15PostFEActualDegenerateQuotient_dyadicScale hQ
    hbase.1 hbase.2
    (h15PostFEDegenerateCrossModulusCollisionSupport_is_degenerate hp)

theorem h15PostFEDegenerateQuotientSupport_subset_range_four_mul
    {M n g U Q : ℕ} [NeZero M] (hQ : 0 < Q) :
    h15PostFEDegenerateQuotientSupport M n g U Q ⊆
      Finset.range (4 * Q) := by
  intro k hk
  exact Finset.mem_range.mpr
    (h15PostFEDegenerateQuotientSupport_scale hQ hk).2

theorem card_h15PostFEDegenerateQuotientSupport_le
    (M : ℕ) [NeZero M] (n g U Q : ℕ) (hQ : 0 < Q) :
    (h15PostFEDegenerateQuotientSupport M n g U Q).card ≤ 4 * Q := by
  have hcard := Finset.card_le_card
    (h15PostFEDegenerateQuotientSupport_subset_range_four_mul
      (M := M) (n := n) (g := g) (U := U) hQ)
  simpa using hcard

end NBMellinTools.NB12
