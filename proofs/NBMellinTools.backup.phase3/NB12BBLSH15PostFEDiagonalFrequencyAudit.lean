/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFECompleteDiagonalBalance

/-!
# NB12zzzbE: frequency audit of the complete diagonal balance

The missing--missing diagonal is first collapsed from a filtered product to a
single support sum, then reindexed frequency-first.  This puts it at the same
outer `|lambda_r|^2` normalization as the extracted degenerate diagonal.

The resulting exact identity shows that diagonal matching is a signed
frequency-average problem: the missing--missing fiber still depends on `r`,
whereas the extracted degenerate collision diagonal does not.
-/

open scoped BigOperators

namespace NBMellinTools.NB12

theorem sum_product_collision_diagonal_eq_single
    {α : Type} [DecidableEq α]
    (s : Finset α) (collision : α × α → Prop)
    [DecidablePred collision] (f : α × α → ℝ)
    (hdiag : ∀ i ∈ s, collision (i, i)) :
    (∑ p ∈ (s.product s).filter collision |>.filter (fun p => p.1 = p.2),
        f p) =
      ∑ i ∈ s, f (i, i) := by
  classical
  symm
  refine Finset.sum_bij (fun i _hi => (i, i)) ?_ ?_ ?_ ?_
  · intro i hi
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hi, hi⟩, hdiag i hi⟩, rfl⟩
  · intro i₁ hi₁ i₂ hi₂ h
    exact congrArg Prod.fst h
  · intro p hp
    have hpOuter := Finset.mem_filter.mp hp
    have hpInner := Finset.mem_filter.mp hpOuter.1
    have hpProduct := Finset.mem_product.mp hpInner.1
    refine ⟨p.1, hpProduct.1, ?_⟩
    exact Prod.ext rfl hpOuter.2
  · intro i _hi
    rfl

/-- The filtered missing--missing diagonal is exactly a single sum over the
actual missing support. -/
theorem h15PostFEMissingMissingDiagonalCollisionLedger_eq_singleSupport
    (M : ℕ) [NeZero M] (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) :
    h15PostFEMissingMissingDiagonalCollisionLedger
        M frequencySupport n g U Q t =
      ∑ i ∈ h15PostFEJointMissingAtomSupport
          (h15PostFEResidueModulusSupport n g U Q)
          (h15PostFEReducedMissingResidues n g U Q),
        h15PostFEWeightedEndpointLaurentMissingAtomCorrelation
          frequencySupport n g U Q t i i := by
  classical
  let support := h15PostFEJointMissingAtomSupport
    (h15PostFEResidueModulusSupport n g U Q)
    (h15PostFEReducedMissingResidues n g U Q)
  let collision := fun p : H15PostFEMissingAtomIndex ×
      H15PostFEMissingAtomIndex =>
    h15PostFEFrequencyCollides
      (h15PostFELiftedMissingFrequency M p.1)
      (h15PostFELiftedMissingFrequency M p.2)
  unfold h15PostFEMissingMissingDiagonalCollisionLedger
  change
    (∑ p ∈ (support.product support).filter collision |>.filter
        (fun p => p.1 = p.2),
      h15PostFEWeightedEndpointLaurentMissingAtomCorrelation
        frequencySupport n g U Q t p.1 p.2) = _
  exact sum_product_collision_diagonal_eq_single support collision
    (fun p => h15PostFEWeightedEndpointLaurentMissingAtomCorrelation
      frequencySupport n g U Q t p.1 p.2)
    (fun i _hi => Or.inl rfl)

/-- One natural-frequency fiber of the missing--missing diagonal. -/
noncomputable def h15PostFEMissingMissingDiagonalFrequencyFiber
    (n g U Q r : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ h15PostFEJointMissingAtomSupport
      (h15PostFEResidueModulusSupport n g U Q)
      (h15PostFEReducedMissingResidues n g U Q),
    h15PostFEEndpointMissingAtom n g U Q r i *
      h15PostFELaurentMissingAtomWithoutFrequency n g U Q r t i

/-- Frequency-first form of the complete missing--missing diagonal ledger. -/
theorem h15PostFEMissingMissingDiagonalCollisionLedger_eq_frequencySum
    (M : ℕ) [NeZero M] (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) :
    h15PostFEMissingMissingDiagonalCollisionLedger
        M frequencySupport n g U Q t =
      ∑ r ∈ frequencySupport,
        Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t) *
          h15PostFEMissingMissingDiagonalFrequencyFiber n g U Q r t := by
  rw [h15PostFEMissingMissingDiagonalCollisionLedger_eq_singleSupport]
  unfold h15PostFEWeightedEndpointLaurentMissingAtomCorrelation
    h15PostFEMissingMissingDiagonalFrequencyFiber
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- The complete diagonal-balance gap is a signed frequency average of the
pointwise difference between the constant degenerate diagonal and the
frequency-dependent missing--missing diagonal fiber. -/
theorem h15PostFECompleteDiagonalBalanceGap_eq_frequencySum
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) (hQ : 0 < Q) :
    letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
      ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
    h15PostFECompleteDiagonalBalanceGap frequencySupport n g U Q t =
      ∑ r ∈ frequencySupport,
        Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t) *
          (h15PostFEDegenerateCollisionDiagonalDispersion
              (h15PostFEActualCommonSuperperiod n g U Q) n g U Q t -
            4 * h15PostFEMissingMissingDiagonalFrequencyFiber
              n g U Q r t) := by
  letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
    ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
  simp only [h15PostFECompleteDiagonalBalanceGap, dif_pos hQ]
  rw [h15PostFEMissingMissingDiagonalCollisionLedger_eq_frequencySum]
  unfold h15PostFEDegenerateExtractedDiagonalContribution
    h15PostFEDegenerateFrequencyMass
  rw [Finset.sum_mul, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  ring

end NBMellinTools.NB12
