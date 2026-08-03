/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEConstantModeModulusCollection

/-!
# NB12zzzbM: sharp outer absolute budget for the constant-mode ledger

Absolute values are introduced only after all missing residues at a fixed
modulus have been summed with their signs.  The resulting nonnegative budget
dominates the constant balance and yields a moving-parameter decay interface.

The budget is not proved to vanish here.  Its decay is the explicit analytic
input exposed by this module.
-/

open Filter
open scoped BigOperators

namespace NBMellinTools.NB12

noncomputable def h15PostFEConstantModeModulusL1Budget
    (M : ℕ) [NeZero M] (n g U Q : ℕ) (t : ℝ) : ℝ :=
  ∑ q ∈ h15PostFEActualMissingModulusSupport n g U Q,
    |h15PostFEResidueFiberEndpointMeanCoefficient n g U Q q| *
      |h15PostFEConstantDiagonalInnerDefectModulusFiber
        M n g U Q t q|

theorem h15PostFEConstantModeModulusL1Budget_nonneg
    (M : ℕ) [NeZero M] (n g U Q : ℕ) (t : ℝ) :
    0 ≤ h15PostFEConstantModeModulusL1Budget M n g U Q t := by
  unfold h15PostFEConstantModeModulusL1Budget
  exact Finset.sum_nonneg fun _q _hq => mul_nonneg (abs_nonneg _) (abs_nonneg _)

/-- Sharp post-collection triangle bound for the constant diagonal balance. -/
theorem abs_h15PostFECompleteConstantDiagonalBalance_le_modulusBudget
    (M : ℕ) [NeZero M] (n g U Q : ℕ) (t : ℝ) :
    |h15PostFECompleteConstantDiagonalBalance M n g U Q t| ≤
      h15PostFEConstantModeModulusL1Budget M n g U Q t := by
  rw [h15PostFECompleteConstantDiagonalBalance_eq_modulusLedger]
  refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
  unfold h15PostFEConstantModeModulusL1Budget
  apply Finset.sum_congr rfl
  intro q _hq
  rw [abs_mul]

noncomputable def h15PostFEWeightedConstantModeModulusL1Budget
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) : ℝ :=
  if hQ : 0 < Q then
    letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
      ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
    h15PostFEDegenerateFrequencyMass frequencySupport t *
      h15PostFEConstantModeModulusL1Budget
        (h15PostFEActualCommonSuperperiod n g U Q) n g U Q t
  else 0

theorem h15PostFEWeightedConstantModeModulusL1Budget_nonneg
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) :
    0 ≤ h15PostFEWeightedConstantModeModulusL1Budget
      frequencySupport n g U Q t := by
  by_cases hQ : 0 < Q
  · letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
      ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
    simp only [h15PostFEWeightedConstantModeModulusL1Budget, dif_pos hQ]
    exact mul_nonneg
      (h15PostFEDegenerateFrequencyMass_nonneg frequencySupport t)
      (h15PostFEConstantModeModulusL1Budget_nonneg
        (h15PostFEActualCommonSuperperiod n g U Q) n g U Q t)
  · simp [h15PostFEWeightedConstantModeModulusL1Budget, hQ]

theorem abs_h15PostFEWeightedConstantDiagonalBalance_le_modulusBudget
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) (hQ : 0 < Q) :
    |h15PostFEWeightedConstantDiagonalBalance
        frequencySupport n g U Q t| ≤
      h15PostFEWeightedConstantModeModulusL1Budget
        frequencySupport n g U Q t := by
  letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
    ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
  simp only [h15PostFEWeightedConstantDiagonalBalance,
    h15PostFEWeightedConstantModeModulusL1Budget, dif_pos hQ, abs_mul,
    abs_of_nonneg (h15PostFEDegenerateFrequencyMass_nonneg frequencySupport t)]
  exact mul_le_mul_of_nonneg_left
    (abs_h15PostFECompleteConstantDiagonalBalance_le_modulusBudget
      (h15PostFEActualCommonSuperperiod n g U Q) n g U Q t)
    (h15PostFEDegenerateFrequencyMass_nonneg frequencySupport t)

/-- Exact moving-parameter analytic input for decay of the weighted constant
mode.  All residue cancellation within a modulus has already occurred in the
budget. -/
structure H15PostFEConstantModeModulusDecayData
    (frequencySupport : ℕ → Finset ℕ)
    (n g U Q : ℕ → ℕ) (t : ℕ → ℝ) where
  cutoff_pos : ∀ k, 0 < Q k
  budget_tendsto_zero :
    Tendsto
      (fun k => h15PostFEWeightedConstantModeModulusL1Budget
        (frequencySupport k) (n k) (g k) (U k) (Q k) (t k))
      atTop (nhds 0)

theorem H15PostFEConstantModeModulusDecayData.weightedConstant_tendsto_zero
    {frequencySupport : ℕ → Finset ℕ}
    {n g U Q : ℕ → ℕ} {t : ℕ → ℝ}
    (H : H15PostFEConstantModeModulusDecayData
      frequencySupport n g U Q t) :
    Tendsto
      (fun k => h15PostFEWeightedConstantDiagonalBalance
        (frequencySupport k) (n k) (g k) (U k) (Q k) (t k))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _k => abs_nonneg _) ?_
    H.budget_tendsto_zero
  exact Eventually.of_forall fun k =>
    abs_h15PostFEWeightedConstantDiagonalBalance_le_modulusBudget
      (frequencySupport k) (n k) (g k) (U k) (Q k) (t k) (H.cutoff_pos k)

/-- The modulus-budget decay input plugs directly into the complete harmonic
normal form; the remaining norm, static, and harmonic limits stay explicit. -/
theorem tendsto_h15PostFEActualVaryingRowEnergy_zero_of_modulusBudget
    (frequencySupport : ℕ → Finset ℕ)
    (n g U Q : ℕ → ℕ) (t : ℕ → ℝ)
    (Hconstant : H15PostFEConstantModeModulusDecayData
      frequencySupport n g U Q t)
    (hnorm :
      Tendsto
        (fun k => h15PostFEAffineNormImbalanceDefect
          (frequencySupport k) (n k) (g k) (U k) (Q k) (t k))
        atTop (nhds 0))
    (hstatic :
      Tendsto
        (fun k => h15PostFECompleteStaticNondiagonalGap
          (frequencySupport k) (n k) (g k) (U k) (Q k) (t k))
        atTop (nhds 0))
    (hharmonic :
      Tendsto
        (fun k => h15PostFECompleteCombinedHarmonicLedger
          (frequencySupport k) (n k) (g k) (U k) (Q k) (t k))
        atTop (nhds 0)) :
    Tendsto
      (fun k => h15PostFEActualVaryingRowEnergy
        (frequencySupport k) (n k) (g k) (U k) (Q k) (t k))
      atTop (nhds 0) :=
  tendsto_h15PostFEActualVaryingRowEnergy_zero_of_completeHarmonicNormalForm
    frequencySupport n g U Q t Hconstant.cutoff_pos hnorm
    Hconstant.weightedConstant_tendsto_zero hstatic hharmonic

end NBMellinTools.NB12
