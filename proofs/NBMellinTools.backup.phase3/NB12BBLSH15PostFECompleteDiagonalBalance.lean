/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFECompleteCollisionGap

/-!
# NB12zzzbD: diagonal-balance audit inside the complete collision gap

The extracted degenerate diagonal can now be compared with the genuine
missing--missing diagonal at the only normalization justified by the global
collision formula.  This file isolates their signed difference and keeps all
remaining static sectors in a separate, exact ledger.

No equality or decay of the diagonal-balance gap is assumed.
-/

namespace NBMellinTools.NB12

/-- The exact diagonal comparison occurring in the global collision-matching
residual.  The coefficient `4` is inherited from the literal H15 alignment
identity, not chosen after taking bounds. -/
noncomputable def h15PostFECompleteDiagonalBalanceGap
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) : ℝ :=
  if hQ : 0 < Q then
    letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
      ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
    h15PostFEDegenerateExtractedDiagonalContribution
        (h15PostFEActualCommonSuperperiod n g U Q)
        frequencySupport n g U Q t -
      4 * h15PostFEMissingMissingDiagonalCollisionLedger
        (h15PostFEActualCommonSuperperiod n g U Q)
        frequencySupport n g U Q t
  else 0

/-- All static collision-matching terms other than the explicit comparison of
the extracted degenerate diagonal with the missing--missing diagonal. -/
noncomputable def h15PostFECompleteStaticNondiagonalGap
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) : ℝ :=
  if hQ : 0 < Q then
    letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
      ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
    Real.sqrt (h15PostFEEndpointFrequencyEnergy frequencySupport n g U Q) *
        Real.sqrt (h15PostFEWeightedLaurentPairFrequencyEnergy
          frequencySupport n g U Q t) -
      4 *
        (h15PostFEMissingMissingAliasCollisionLedger
            (h15PostFEActualCommonSuperperiod n g U Q)
            frequencySupport n g U Q t +
          h15PostFEMissingMissingCrossModulusCollisionLedger
            (h15PostFEActualCommonSuperperiod n g U Q)
            frequencySupport n g U Q t) +
      h15PostFEMissingPairIncidentCollisionLedger
          (h15PostFEActualCommonSuperperiod n g U Q)
          frequencySupport n g U Q t +
      h15PostFEMissingPairAliasCollisionLedger
          (h15PostFEActualCommonSuperperiod n g U Q)
          frequencySupport n g U Q t +
      h15PostFEMissingPairFavorableCrossModulusCollisionLedger
          (h15PostFEActualCommonSuperperiod n g U Q)
          frequencySupport n g U Q t
  else 0

/-- Zero diagonal-balance gap is exactly the correctly normalized diagonal
matching identity. -/
theorem h15PostFECompleteDiagonalBalanceGap_eq_zero_iff
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) (hQ : 0 < Q) :
    letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
      ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
    h15PostFECompleteDiagonalBalanceGap frequencySupport n g U Q t = 0 ↔
      h15PostFEDegenerateExtractedDiagonalContribution
          (h15PostFEActualCommonSuperperiod n g U Q)
          frequencySupport n g U Q t =
        4 * h15PostFEMissingMissingDiagonalCollisionLedger
          (h15PostFEActualCommonSuperperiod n g U Q)
          frequencySupport n g U Q t := by
  letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
    ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
  simp only [h15PostFECompleteDiagonalBalanceGap, dif_pos hQ]
  constructor <;> intro h <;> linarith

/-- Exact internal decomposition of the complete static gap. -/
theorem h15PostFECompleteStaticCollisionGap_eq_diagonalBalance_add_nondiagonal
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) (hQ : 0 < Q) :
    h15PostFECompleteStaticCollisionGap frequencySupport n g U Q t =
      h15PostFECompleteDiagonalBalanceGap frequencySupport n g U Q t +
        h15PostFECompleteStaticNondiagonalGap
          frequencySupport n g U Q t := by
  letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
    ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
  simp only [h15PostFECompleteStaticCollisionGap,
    h15PostFECompleteDiagonalBalanceGap,
    h15PostFECompleteStaticNondiagonalGap, dif_pos hQ]
  ring

/-- Final three-ledger form of the alignment residual. -/
theorem h15PostFEAffineAlignmentResidual_eq_diagonalBalance_add_remainders
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) (hQ : 0 < Q) :
    h15PostFEAffineAlignmentResidual frequencySupport n g U Q t =
      h15PostFECompleteDiagonalBalanceGap frequencySupport n g U Q t +
        h15PostFECompleteStaticNondiagonalGap frequencySupport n g U Q t +
        h15PostFECompleteOscillatoryAlignmentLedger
          frequencySupport n g U Q t := by
  rw [h15PostFEAffineAlignmentResidual_eq_completeCollisionGap
    frequencySupport n g U Q t hQ]
  rw [h15PostFECompleteStaticCollisionGap_eq_diagonalBalance_add_nondiagonal
    frequencySupport n g U Q t hQ]

end NBMellinTools.NB12
