/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEDegenerateCollisionDiagonalExtraction

/-!
# NB12zzzbB: complete missing--pair collision reassembly

The extracted degenerate diagonal is only one part of the missing--pair
collision ledger.  This file puts it back into the complete arithmetic
partition before any comparison with the retained H15 correction is made.

The exact five-term normal form is

`incident + alias + extracted degenerate diagonal
  + degenerate second harmonic + favorable cross-modulus`.

The second theorem substitutes that form into the global collision-matching
residual.  Hence all missing--missing collision sectors and the Cauchy norm
product remain visible at the point where correction matching must actually
be proved.
-/

namespace NBMellinTools.NB12

/-- Complete reassembly of the missing--pair collision ledger after splitting
the cross-modulus sector and extracting its degenerate diagonal. -/
theorem h15PostFEWeightedMissingPairCollisionLedger_eq_fiveSectorDiagonalReassembly
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) (hQ : 0 < Q) :
    letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
      ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
    h15PostFEWeightedMissingPairCollisionLedger
        (h15PostFEActualCommonSuperperiod n g U Q)
        frequencySupport n g U Q t =
      h15PostFEMissingPairIncidentCollisionLedger
          (h15PostFEActualCommonSuperperiod n g U Q)
          frequencySupport n g U Q t +
        h15PostFEMissingPairAliasCollisionLedger
          (h15PostFEActualCommonSuperperiod n g U Q)
          frequencySupport n g U Q t +
        h15PostFEDegenerateExtractedDiagonalContribution
          (h15PostFEActualCommonSuperperiod n g U Q)
          frequencySupport n g U Q t +
        h15PostFEDegenerateWeightedSecondHarmonicLedger
          (h15PostFEActualCommonSuperperiod n g U Q)
          frequencySupport n g U Q t +
        h15PostFEMissingPairFavorableCrossModulusCollisionLedger
          (h15PostFEActualCommonSuperperiod n g U Q)
          frequencySupport n g U Q t := by
  letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
    ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
  rw [h15PostFEWeightedMissingPairCollisionLedger_eq_threeSectors]
  rw [h15PostFEMissingPairCrossModulusCollisionLedger_eq_degenerate_add_favorable]
  rw [h15PostFEDegenerateCollisionLedger_eq_extractedDiagonal_add_secondHarmonic
    hQ frequencySupport t]
  ring

/-- The global collision-matching residual with the complete missing--pair
five-term ledger exposed.  In particular, the extracted degenerate diagonal
is not silently identified with the retained correction. -/
theorem h15PostFECollisionMatchingResidual_eq_fiveSectorDiagonalAudit
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
          h15PostFEDegenerateExtractedDiagonalContribution
            (h15PostFEActualCommonSuperperiod n g U Q)
            frequencySupport n g U Q t +
          h15PostFEDegenerateWeightedSecondHarmonicLedger
            (h15PostFEActualCommonSuperperiod n g U Q)
            frequencySupport n g U Q t +
          h15PostFEMissingPairFavorableCrossModulusCollisionLedger
            (h15PostFEActualCommonSuperperiod n g U Q)
            frequencySupport n g U Q t) := by
  letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
    ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
  rw [h15PostFECollisionMatchingResidual_eq_threeSectorAudit
    frequencySupport n g U Q t hQ]
  rw [h15PostFEMissingPairCrossModulusCollisionLedger_eq_degenerate_add_favorable]
  rw [h15PostFEDegenerateCollisionLedger_eq_extractedDiagonal_add_secondHarmonic
    hQ frequencySupport t]
  ring

end NBMellinTools.NB12
