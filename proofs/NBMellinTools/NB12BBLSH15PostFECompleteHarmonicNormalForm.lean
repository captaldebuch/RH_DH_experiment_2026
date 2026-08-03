/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEMissingDiagonalPhaseCompression

/-!
# NB12zzzbG: complete constant/harmonic normal form

The two diagonal phase compressions are assembled into the complete alignment
defect.  The result has exactly three signed components:

1. the frequency mass times an explicit constant diagonal balance;
2. the static non-diagonal collision gap;
3. one combined harmonic ledger containing both doubled-frequency terms and
   the retained off-diagonal expression.

This is an exact normal form.  Its three required decay statements remain
analytic inputs.
-/

open Filter

namespace NBMellinTools.NB12

noncomputable def h15PostFEWeightedConstantDiagonalBalance
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) : ℝ :=
  if hQ : 0 < Q then
    letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
      ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
    h15PostFEDegenerateFrequencyMass frequencySupport t *
      h15PostFECompleteConstantDiagonalBalance
        (h15PostFEActualCommonSuperperiod n g U Q) n g U Q t
  else 0

noncomputable def h15PostFECompleteCombinedHarmonicLedger
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) : ℝ :=
  if hQ : 0 < Q then
    letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
      ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
    h15PostFEDegenerateWeightedSecondHarmonicLedger
        (h15PostFEActualCommonSuperperiod n g U Q)
        frequencySupport n g U Q t -
      4 * h15PostFEWeightedMissingMissingDiagonalSecondHarmonic
        frequencySupport n g U Q t +
      h15PostFEWeightedOffDiagonalAlignmentLedger
        frequencySupport n g U Q t
  else 0

/-- Complete phase-compressed normal form of the alignment residual. -/
theorem h15PostFEAffineAlignmentResidual_eq_constant_add_static_add_harmonic
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) (hQ : 0 < Q) :
    h15PostFEAffineAlignmentResidual frequencySupport n g U Q t =
      h15PostFEWeightedConstantDiagonalBalance
          frequencySupport n g U Q t +
        h15PostFECompleteStaticNondiagonalGap frequencySupport n g U Q t +
        h15PostFECompleteCombinedHarmonicLedger
          frequencySupport n g U Q t := by
  letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
    ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
  rw [h15PostFEAffineAlignmentResidual_eq_diagonalBalance_add_remainders
    frequencySupport n g U Q t hQ]
  rw [h15PostFECompleteDiagonalBalanceGap_eq_constantBalance_sub_secondHarmonic
    frequencySupport n g U Q t hQ]
  simp only [h15PostFEWeightedConstantDiagonalBalance,
    h15PostFECompleteCombinedHarmonicLedger,
    h15PostFECompleteOscillatoryAlignmentLedger, dif_pos hQ]
  ring

/-- Complete phase-compressed normal form of the actual varying-row energy. -/
theorem h15PostFEActualVaryingRowEnergy_eq_normImbalance_add_constant_static_harmonic
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) (hQ : 0 < Q) :
    h15PostFEActualVaryingRowEnergy frequencySupport n g U Q t =
      h15PostFEAffineNormImbalanceDefect frequencySupport n g U Q t +
        2 *
          (h15PostFEWeightedConstantDiagonalBalance
              frequencySupport n g U Q t +
            h15PostFECompleteStaticNondiagonalGap
              frequencySupport n g U Q t +
            h15PostFECompleteCombinedHarmonicLedger
              frequencySupport n g U Q t) := by
  rw [h15PostFEActualVaryingRowEnergy_eq_affineDefects,
    h15PostFEAffineAntiparallelDefect_eq_two_mul_alignmentResidual,
    h15PostFEAffineAlignmentResidual_eq_constant_add_static_add_harmonic
      frequencySupport n g U Q t hQ]

/-- The exact analytic inputs exposed by the complete harmonic normal form. -/
theorem tendsto_h15PostFEActualVaryingRowEnergy_zero_of_completeHarmonicNormalForm
    (frequencySupport : ℕ → Finset ℕ)
    (n g U Q : ℕ → ℕ) (t : ℕ → ℝ)
    (hQ : ∀ k, 0 < Q k)
    (hnorm :
      Tendsto
        (fun k => h15PostFEAffineNormImbalanceDefect
          (frequencySupport k) (n k) (g k) (U k) (Q k) (t k))
        atTop (nhds 0))
    (hconstant :
      Tendsto
        (fun k => h15PostFEWeightedConstantDiagonalBalance
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
      atTop (nhds 0) := by
  have halign := (hconstant.add hstatic).add hharmonic
  have htwice := halign.const_mul 2
  rw [show
      (fun k => h15PostFEActualVaryingRowEnergy
        (frequencySupport k) (n k) (g k) (U k) (Q k) (t k)) =
      (fun k => h15PostFEAffineNormImbalanceDefect
          (frequencySupport k) (n k) (g k) (U k) (Q k) (t k) +
        2 *
          (h15PostFEWeightedConstantDiagonalBalance
              (frequencySupport k) (n k) (g k) (U k) (Q k) (t k) +
            h15PostFECompleteStaticNondiagonalGap
              (frequencySupport k) (n k) (g k) (U k) (Q k) (t k) +
            h15PostFECompleteCombinedHarmonicLedger
              (frequencySupport k) (n k) (g k) (U k) (Q k) (t k))) by
    funext k
    exact
      h15PostFEActualVaryingRowEnergy_eq_normImbalance_add_constant_static_harmonic
        (frequencySupport k) (n k) (g k) (U k) (Q k) (t k) (hQ k)]
  simpa only [zero_add, add_zero, mul_zero] using hnorm.add htwice

end NBMellinTools.NB12
