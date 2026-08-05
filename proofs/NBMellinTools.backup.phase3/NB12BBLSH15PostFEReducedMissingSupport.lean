/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEFrequencyLift

/-!
# NB12zzzW: removing zero atoms from the H15 missing-residue support

The missing-residue support is defined inside the complete natural residue
system.  Its doubled additive phase is deliberately extended by zero away
from reduced residues.  Before lifting all literal phases to one common
period, those artificial zero atoms should be removed.

This file filters every missing fiber by coprimality and proves that:

* non-coprime doubled phases are exactly zero;
* the missing transform is unchanged by the filter;
* the complete correction transform is unchanged; and
* every retained missing atom has a positive modulus and a genuine reduced
  base frequency.

All statements are finite equalities.  No decay estimate is used.
-/

open scoped BigOperators

namespace NBMellinTools.NB12

/-- The genuine reduced atoms in one zero-extended missing-residue fiber. -/
def h15PostFEReducedMissingResidues
    (n g U Q q : ℕ) : Finset ℕ :=
  (h15PostFEMissingResidues n g U Q q).filter fun a => Nat.Coprime a q

theorem h15PostFEReducedMissingResidues_subset
    (n g U Q q : ℕ) :
    h15PostFEReducedMissingResidues n g U Q q ⊆
      h15PostFEMissingResidues n g U Q q := by
  exact Finset.filter_subset _ _

theorem coprime_of_mem_h15PostFEReducedMissingResidues
    {n g U Q q a : ℕ}
    (ha : a ∈ h15PostFEReducedMissingResidues n g U Q q) :
    Nat.Coprime a q := by
  exact (Finset.mem_filter.mp ha).2

/-- The zero extension really kills every non-reduced missing atom. -/
theorem h15PostFEReducedDoubledAdditivePhase_eq_zero_of_not_coprime
    (r u q : ℕ) (huq : ¬ Nat.Coprime u q) :
    h15PostFEReducedDoubledAdditivePhase r u q = 0 := by
  unfold h15PostFEReducedDoubledAdditivePhase
  by_cases hq : q = 0
  · simp [hq]
  · simp [hq, huq]

/-- Filtering any finite support by coprimality leaves its zero-extended
doubled-character sum unchanged. -/
theorem sum_reducedDoubledAdditivePhase_im_eq_filter_coprime
    (support : Finset ℕ) (r q : ℕ) :
    (∑ a ∈ support,
        (h15PostFEReducedDoubledAdditivePhase r a q).im) =
      ∑ a ∈ support.filter (fun a => Nat.Coprime a q),
        (h15PostFEReducedDoubledAdditivePhase r a q).im := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases huq : Nat.Coprime a q
  · simp [huq]
  · rw [h15PostFEReducedDoubledAdditivePhase_eq_zero_of_not_coprime
      r a q huq]
    simp [huq]

theorem sum_h15PostFEMissingResidues_eq_reduced
    (n g U Q r q : ℕ) :
    (∑ a ∈ h15PostFEMissingResidues n g U Q q,
        (h15PostFEReducedDoubledAdditivePhase r a q).im) =
      ∑ a ∈ h15PostFEReducedMissingResidues n g U Q q,
        (h15PostFEReducedDoubledAdditivePhase r a q).im := by
  exact sum_reducedDoubledAdditivePhase_im_eq_filter_coprime
    (h15PostFEMissingResidues n g U Q q) r q

/-- The entire literal missing transform is unchanged after zero-atom
removal. -/
theorem h15PostFEJointMissingTransform_eq_reducedMissing
    (n g U Q r : ℕ) (coefficient : ℕ → ℝ) :
    h15PostFEJointMissingTransform
        (h15PostFEResidueModulusSupport n g U Q)
        (h15PostFEMissingResidues n g U Q) coefficient r =
      h15PostFEJointMissingTransform
        (h15PostFEResidueModulusSupport n g U Q)
        (h15PostFEReducedMissingResidues n g U Q) coefficient r := by
  unfold h15PostFEJointMissingTransform
  apply Finset.sum_congr rfl
  intro q _hq
  rw [sum_h15PostFEMissingResidues_eq_reduced]

/-- The literal correction-preserving transform is unchanged after deleting
the non-coprime zero atoms from every missing fiber. -/
theorem h15PostFEActualJointCorrectionTransform_eq_reducedMissing
    (n g U Q r : ℕ) (t : ℝ) :
    h15PostFEActualJointCorrectionTransform n g U Q r t =
      h15PostFEJointCorrectionTransform
        (h15PostFEOrderedPairResidueSupport n g U Q)
        (h15PostFEOrderedPairCollectedScalar n g U Q r t)
        (h15PostFEResidueModulusSupport n g U Q)
        (h15PostFEReducedMissingResidues n g U Q)
        (h15PostFEResidueFiberMeanCoefficient n g U Q r t) r t := by
  unfold h15PostFEActualJointCorrectionTransform
    h15PostFEJointCorrectionTransform
  rw [h15PostFEJointMissingTransform_eq_reducedMissing]

/-- Every modulus that actually occurs in the missing ledger is positive. -/
theorem h15PostFEResidueModulusSupport_pos
    {n g U Q q : ℕ} (hQ : 0 < Q)
    (hq : q ∈ h15PostFEResidueModulusSupport n g U Q) :
    0 < q := by
  classical
  rw [h15PostFEResidueModulusSupport, Finset.mem_image] at hq
  rcases hq with ⟨z, hz, rfl⟩
  have hlt := h15PostFEResidueKey_fst_lt_snd hQ hz
  exact Nat.zero_lt_of_lt hlt

/-- Each retained atom now satisfies exactly the hypotheses of the literal
base-frequency theorem. -/
theorem h15PostFEReducedMissingResidue_phase_eq_baseFrequency
    {n g U Q q a : ℕ} (hQ : 0 < Q)
    (hq : q ∈ h15PostFEResidueModulusSupport n g U Q)
    (ha : a ∈ h15PostFEReducedMissingResidues n g U Q q)
    (r : ℕ) :
    letI : NeZero q := ⟨(h15PostFEResidueModulusSupport_pos hQ hq).ne'⟩
    h15PostFEReducedDoubledAdditivePhase r a q =
      ZMod.stdAddChar
        ((r : ZMod q) * h15PostFEMissingBaseFrequency a q) := by
  exact h15PostFEReducedDoubledAdditivePhase_eq_baseFrequency r a q
    (h15PostFEResidueModulusSupport_pos hQ hq)
    (coprime_of_mem_h15PostFEReducedMissingResidues ha)

end NBMellinTools.NB12
