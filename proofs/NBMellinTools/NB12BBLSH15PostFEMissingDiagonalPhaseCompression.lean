/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEDiagonalFrequencyAudit

/-!
# NB12zzzbF: phase compression of the missing--missing diagonal

The actual reduced missing phase has unit norm.  Therefore its squared
imaginary part is a constant mode minus a doubled-frequency real character.
This file applies that elementary identity to every missing--missing diagonal
atom and lifts it through the full support.

The outcome separates the complete diagonal-balance gap into a constant
balance and a signed second-harmonic remainder.  No matching or decay is
asserted.
-/

open AddChar
open scoped BigOperators

namespace NBMellinTools.NB12

theorem im_sq_eq_one_sub_sq_re_div_two
    (z : ℂ) (hz : ‖z‖ = 1) :
    z.im * z.im = (1 - (z ^ 2).re) / 2 := by
  have hnorm : z.re * z.re + z.im * z.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hz]
    norm_num
  rw [pow_two, Complex.mul_re]
  nlinarith

noncomputable def h15PostFEMissingMissingDiagonalConstantAtom
    (n g U Q : ℕ) (t : ℝ) (i : H15PostFEMissingAtomIndex) : ℝ :=
  h15PostFEResidueFiberEndpointMeanCoefficient n g U Q i.1 *
      h15PostFEResidueFiberLaurentMeanCoefficientWithoutFrequency
        n g U Q t i.1 /
    2

noncomputable def h15PostFEMissingMissingDiagonalSecondHarmonicAtom
    (n g U Q r : ℕ) (t : ℝ) (i : H15PostFEMissingAtomIndex) : ℝ :=
  -(h15PostFEResidueFiberEndpointMeanCoefficient n g U Q i.1 *
      h15PostFEResidueFiberLaurentMeanCoefficientWithoutFrequency
        n g U Q t i.1 *
      (h15PostFEReducedDoubledAdditivePhase r i.2 i.1 ^ 2).re) /
    2

/-- One genuine diagonal atom is a constant plus a doubled-frequency
character. -/
theorem h15PostFEEndpointMissing_mul_laurentMissing_eq_constant_add_secondHarmonic
    {n g U Q r : ℕ} (t : ℝ) (hQ : 0 < Q)
    {i : H15PostFEMissingAtomIndex}
    (hi : i ∈ h15PostFEJointMissingAtomSupport
      (h15PostFEResidueModulusSupport n g U Q)
      (h15PostFEReducedMissingResidues n g U Q)) :
    h15PostFEEndpointMissingAtom n g U Q r i *
        h15PostFELaurentMissingAtomWithoutFrequency n g U Q r t i =
      h15PostFEMissingMissingDiagonalConstantAtom n g U Q t i +
        h15PostFEMissingMissingDiagonalSecondHarmonicAtom
          n g U Q r t i := by
  have hi' := Finset.mem_sigma.mp hi
  letI : NeZero i.1 :=
    ⟨(h15PostFEResidueModulusSupport_pos hQ hi'.1).ne'⟩
  have hphase := h15PostFEReducedMissingResidue_phase_eq_baseFrequency
    hQ hi'.1 hi'.2 r
  have hnorm :
      ‖h15PostFEReducedDoubledAdditivePhase r i.2 i.1‖ = 1 := by
    rw [hphase, AddChar.norm_apply]
  have hsquare := im_sq_eq_one_sub_sq_re_div_two
    (h15PostFEReducedDoubledAdditivePhase r i.2 i.1) hnorm
  unfold h15PostFEEndpointMissingAtom
    h15PostFELaurentMissingAtomWithoutFrequency
    h15PostFEJointMissingAtom
    h15PostFEMissingMissingDiagonalConstantAtom
    h15PostFEMissingMissingDiagonalSecondHarmonicAtom
  rw [show
      (h15PostFEResidueFiberEndpointMeanCoefficient n g U Q i.1 *
          (h15PostFEReducedDoubledAdditivePhase r i.2 i.1).im) *
        (h15PostFEResidueFiberLaurentMeanCoefficientWithoutFrequency
            n g U Q t i.1 *
          (h15PostFEReducedDoubledAdditivePhase r i.2 i.1).im) =
      (h15PostFEResidueFiberEndpointMeanCoefficient n g U Q i.1 *
        h15PostFEResidueFiberLaurentMeanCoefficientWithoutFrequency
          n g U Q t i.1) *
        ((h15PostFEReducedDoubledAdditivePhase r i.2 i.1).im *
          (h15PostFEReducedDoubledAdditivePhase r i.2 i.1).im) by ring]
  rw [hsquare]
  ring

noncomputable def h15PostFEMissingMissingDiagonalConstantFiber
    (n g U Q : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ h15PostFEJointMissingAtomSupport
      (h15PostFEResidueModulusSupport n g U Q)
      (h15PostFEReducedMissingResidues n g U Q),
    h15PostFEMissingMissingDiagonalConstantAtom n g U Q t i

noncomputable def h15PostFEMissingMissingDiagonalSecondHarmonicFiber
    (n g U Q r : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ h15PostFEJointMissingAtomSupport
      (h15PostFEResidueModulusSupport n g U Q)
      (h15PostFEReducedMissingResidues n g U Q),
    h15PostFEMissingMissingDiagonalSecondHarmonicAtom n g U Q r t i

theorem h15PostFEMissingMissingDiagonalFrequencyFiber_eq_constant_add_secondHarmonic
    (n g U Q r : ℕ) (t : ℝ) (hQ : 0 < Q) :
    h15PostFEMissingMissingDiagonalFrequencyFiber n g U Q r t =
      h15PostFEMissingMissingDiagonalConstantFiber n g U Q t +
        h15PostFEMissingMissingDiagonalSecondHarmonicFiber
          n g U Q r t := by
  unfold h15PostFEMissingMissingDiagonalFrequencyFiber
    h15PostFEMissingMissingDiagonalConstantFiber
    h15PostFEMissingMissingDiagonalSecondHarmonicFiber
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact
    h15PostFEEndpointMissing_mul_laurentMissing_eq_constant_add_secondHarmonic
      t hQ hi

/-- Constant part of the correctly normalized diagonal comparison. -/
noncomputable def h15PostFECompleteConstantDiagonalBalance
    (M : ℕ) [NeZero M] (n g U Q : ℕ) (t : ℝ) : ℝ :=
  h15PostFEDegenerateCollisionDiagonalDispersion M n g U Q t -
    4 * h15PostFEMissingMissingDiagonalConstantFiber n g U Q t

noncomputable def h15PostFEWeightedMissingMissingDiagonalSecondHarmonic
    (frequencySupport : Finset ℕ) (n g U Q : ℕ) (t : ℝ) : ℝ :=
  ∑ r ∈ frequencySupport,
    Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t) *
      h15PostFEMissingMissingDiagonalSecondHarmonicFiber n g U Q r t

/-- Final phase-compressed diagonal audit: constant diagonal balance weighted
by the full frequency mass, minus the signed missing--missing second
harmonic. -/
theorem h15PostFECompleteDiagonalBalanceGap_eq_constantBalance_sub_secondHarmonic
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) (hQ : 0 < Q) :
    letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
      ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
    h15PostFECompleteDiagonalBalanceGap frequencySupport n g U Q t =
      h15PostFEDegenerateFrequencyMass frequencySupport t *
          h15PostFECompleteConstantDiagonalBalance
            (h15PostFEActualCommonSuperperiod n g U Q) n g U Q t -
        4 * h15PostFEWeightedMissingMissingDiagonalSecondHarmonic
          frequencySupport n g U Q t := by
  letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
    ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
  rw [h15PostFECompleteDiagonalBalanceGap_eq_frequencySum
    frequencySupport n g U Q t hQ]
  simp_rw [h15PostFEMissingMissingDiagonalFrequencyFiber_eq_constant_add_secondHarmonic
    n g U Q _ t hQ]
  unfold h15PostFEDegenerateFrequencyMass
    h15PostFECompleteConstantDiagonalBalance
    h15PostFEWeightedMissingMissingDiagonalSecondHarmonic
  rw [Finset.sum_mul, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  ring

end NBMellinTools.NB12
