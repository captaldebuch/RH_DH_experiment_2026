/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEReducedMissingSupport

/-!
# NB12zzzX: removing zero atoms from the H15 ordered-pair support

The literal ordered-pair support can contain raw rows whose primitive
coordinates are not coprime.  The common additive phase is zero on such a
pair.  This file removes those artificial atoms and proves that every one of
the four orientation populations, hence the complete correction transform,
is unchanged.
-/

open scoped BigOperators

namespace NBMellinTools.NB12

def h15PostFEReducedOrderedPairResidueSupport
    (n g U Q : ℕ) : Finset H15PostFEJointResiduePair :=
  (h15PostFEOrderedPairResidueSupport n g U Q).filter fun κ =>
    Nat.Coprime κ.1.1 κ.1.2 ∧ Nat.Coprime κ.2.1 κ.2.2

theorem h15PostFEReducedOrderedPairResidueSupport_subset
    (n g U Q : ℕ) :
    h15PostFEReducedOrderedPairResidueSupport n g U Q ⊆
      h15PostFEOrderedPairResidueSupport n g U Q := by
  exact Finset.filter_subset _ _

theorem coprime_of_mem_h15PostFEReducedOrderedPairResidueSupport
    {n g U Q : ℕ} {κ : H15PostFEJointResiduePair}
    (hκ : κ ∈ h15PostFEReducedOrderedPairResidueSupport n g U Q) :
    Nat.Coprime κ.1.1 κ.1.2 ∧ Nat.Coprime κ.2.1 κ.2.2 := by
  exact (Finset.mem_filter.mp hκ).2

theorem h15PostFECommonPairAdditivePhase_eq_zero_of_not_coprime
    (left right : BettinChandeeUnitSign)
    (r u q v q' : ℕ)
    (hcop : ¬ (Nat.Coprime u q ∧ Nat.Coprime v q')) :
    h15PostFECommonPairAdditivePhase left right r u q v q' = 0 := by
  unfold h15PostFECommonPairAdditivePhase
  by_cases hM : q * q' = 0
  · simp [hM]
  · simp [hM, hcop]

/-- Any one of the four generic pair populations is unchanged after
discarding pairs on which its zero-extended phase vanishes. -/
theorem h15PostFEJointPairTransform_eq_filter_coprime
    (left right : BettinChandeeUnitSign)
    (support : Finset H15PostFEJointResiduePair)
    (coefficient : H15PostFEJointResiduePair → ℂ)
    (r : ℕ) (t : ℝ) :
    h15PostFEJointPairTransform left right support coefficient r t =
      h15PostFEJointPairTransform left right
        (support.filter fun κ =>
          Nat.Coprime κ.1.1 κ.1.2 ∧ Nat.Coprime κ.2.1 κ.2.2)
        coefficient r t := by
  classical
  unfold h15PostFEJointPairTransform
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro κ _hκ
  by_cases hcop :
      Nat.Coprime κ.1.1 κ.1.2 ∧ Nat.Coprime κ.2.1 κ.2.2
  · simp [hcop]
  · rw [h15PostFECommonPairAdditivePhase_eq_zero_of_not_coprime
      left right r κ.1.1 κ.1.2 κ.2.1 κ.2.2 hcop]
    simp [hcop]

theorem h15PostFEActualJointCorrectionTransform_eq_reducedSupports
    (n g U Q r : ℕ) (t : ℝ) :
    h15PostFEActualJointCorrectionTransform n g U Q r t =
      h15PostFEJointCorrectionTransform
        (h15PostFEReducedOrderedPairResidueSupport n g U Q)
        (h15PostFEOrderedPairCollectedScalar n g U Q r t)
        (h15PostFEResidueModulusSupport n g U Q)
        (h15PostFEReducedMissingResidues n g U Q)
        (h15PostFEResidueFiberMeanCoefficient n g U Q r t) r t := by
  rw [h15PostFEActualJointCorrectionTransform_eq_reducedMissing]
  unfold h15PostFEJointCorrectionTransform
    h15PostFEReducedOrderedPairResidueSupport
  rw [h15PostFEJointPairTransform_eq_filter_coprime
      .positive .positive
      (h15PostFEOrderedPairResidueSupport n g U Q)
      (h15PostFEOrderedPairCollectedScalar n g U Q r t) r t,
    h15PostFEJointPairTransform_eq_filter_coprime
      .positive .negative
      (h15PostFEOrderedPairResidueSupport n g U Q)
      (h15PostFEOrderedPairCollectedScalar n g U Q r t) r t,
    h15PostFEJointPairTransform_eq_filter_coprime
      .negative .positive
      (h15PostFEOrderedPairResidueSupport n g U Q)
      (h15PostFEOrderedPairCollectedScalar n g U Q r t) r t,
    h15PostFEJointPairTransform_eq_filter_coprime
      .negative .negative
      (h15PostFEOrderedPairResidueSupport n g U Q)
      (h15PostFEOrderedPairCollectedScalar n g U Q r t) r t]

/-- Every retained pair satisfies the coprimality hypotheses of the literal
base-frequency theorem. -/
theorem h15PostFEReducedOrderedPair_phase_eq_baseFrequency
    {n g U Q : ℕ} {κ : H15PostFEJointResiduePair}
    (hQ : 0 < Q)
    (hκ : κ ∈ h15PostFEReducedOrderedPairResidueSupport n g U Q)
    (left right : BettinChandeeUnitSign) (r : ℕ) :
    letI : NeZero (κ.1.2 * κ.2.2) :=
      ⟨Nat.mul_ne_zero
        (Nat.ne_of_gt (Nat.zero_lt_of_lt
          (h15PostFEResidueKey_fst_lt_snd hQ
          (h15PostFEOrderedPairResidueSupport_subset_actual
            (h15PostFEReducedOrderedPairResidueSupport_subset
              n g U Q hκ)).1)))
        (Nat.ne_of_gt (Nat.zero_lt_of_lt
          (h15PostFEResidueKey_fst_lt_snd hQ
          (h15PostFEOrderedPairResidueSupport_subset_actual
            (h15PostFEReducedOrderedPairResidueSupport_subset
              n g U Q hκ)).2)))⟩
    h15PostFECommonPairAdditivePhase left right r
        κ.1.1 κ.1.2 κ.2.1 κ.2.2 =
      ZMod.stdAddChar
        ((r : ZMod (κ.1.2 * κ.2.2)) *
          h15PostFECommonPairBaseFrequency left right
            κ.1.1 κ.1.2 κ.2.1 κ.2.2) := by
  have hraw := h15PostFEReducedOrderedPairResidueSupport_subset
    n g U Q hκ
  have hactual := h15PostFEOrderedPairResidueSupport_subset_actual hraw
  have hq : 0 < κ.1.2 :=
    Nat.zero_lt_of_lt (h15PostFEResidueKey_fst_lt_snd hQ hactual.1)
  have hq' : 0 < κ.2.2 :=
    Nat.zero_lt_of_lt (h15PostFEResidueKey_fst_lt_snd hQ hactual.2)
  have hcop :=
    coprime_of_mem_h15PostFEReducedOrderedPairResidueSupport hκ
  exact h15PostFECommonPairAdditivePhase_eq_baseFrequency
    left right r κ.1.1 κ.1.2 κ.2.1 κ.2.2 hq hq' hcop.1 hcop.2

end NBMellinTools.NB12
