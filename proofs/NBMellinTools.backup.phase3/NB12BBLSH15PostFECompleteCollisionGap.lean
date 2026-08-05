/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFECollisionFourSectorDiagonalReassembly

/-!
# NB12zzzbC: the complete correction-matching gap

After complete collision-sector reassembly, the alignment defect has a
canonical two-part signed normal form:

* a static collision gap containing the Cauchy norm product, all three
  missing--missing collision sectors, the incident and alias missing--pair
  sectors, the extracted degenerate diagonal, and the favorable sector;
* an oscillatory ledger containing the weighted degenerate second harmonic
  and the complete retained off-diagonal expression.

This file proves the exact decomposition and its consequence for the full
varying-row energy.  It does not assert decay of either signed term.
-/

open Filter

namespace NBMellinTools.NB12

/-- The non-second-harmonic part of the complete collision-matching residual.
This is the smallest correction-matching gap currently justified by the full
arithmetic partition. -/
noncomputable def h15PostFECompleteStaticCollisionGap
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) : ℝ :=
  if hQ : 0 < Q then
    letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
      ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
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
      h15PostFEMissingPairIncidentCollisionLedger
          (h15PostFEActualCommonSuperperiod n g U Q)
          frequencySupport n g U Q t +
      h15PostFEMissingPairAliasCollisionLedger
          (h15PostFEActualCommonSuperperiod n g U Q)
          frequencySupport n g U Q t +
      h15PostFEDegenerateExtractedDiagonalContribution
          (h15PostFEActualCommonSuperperiod n g U Q)
          frequencySupport n g U Q t +
      h15PostFEMissingPairFavorableCrossModulusCollisionLedger
          (h15PostFEActualCommonSuperperiod n g U Q)
          frequencySupport n g U Q t
  else 0

/-- The genuinely oscillatory remainder after extracting the complete static
collision gap: the signed weighted second harmonic plus all retained
off-diagonal correlations. -/
noncomputable def h15PostFECompleteOscillatoryAlignmentLedger
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) : ℝ :=
  if hQ : 0 < Q then
    letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
      ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
    h15PostFEDegenerateWeightedSecondHarmonicLedger
        (h15PostFEActualCommonSuperperiod n g U Q)
        frequencySupport n g U Q t +
      h15PostFEWeightedOffDiagonalAlignmentLedger
        frequencySupport n g U Q t
  else 0

/-- The collision-matching residual is exactly the complete static gap plus
the degenerate weighted second harmonic. -/
theorem h15PostFECollisionMatchingResidual_eq_staticGap_add_secondHarmonic
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) (hQ : 0 < Q) :
    letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
      ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
    h15PostFECollisionMatchingResidual frequencySupport n g U Q t =
      h15PostFECompleteStaticCollisionGap frequencySupport n g U Q t +
        h15PostFEDegenerateWeightedSecondHarmonicLedger
          (h15PostFEActualCommonSuperperiod n g U Q)
          frequencySupport n g U Q t := by
  letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
    ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
  rw [h15PostFECollisionMatchingResidual_eq_fiveSectorDiagonalAudit
    frequencySupport n g U Q t hQ]
  simp only [h15PostFECompleteStaticCollisionGap, dif_pos hQ]
  ring

/-- Exact final alignment normal form: a complete static correction-matching
gap plus one signed oscillatory ledger. -/
theorem h15PostFEAffineAlignmentResidual_eq_completeCollisionGap
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) (hQ : 0 < Q) :
    h15PostFEAffineAlignmentResidual frequencySupport n g U Q t =
      h15PostFECompleteStaticCollisionGap frequencySupport n g U Q t +
        h15PostFECompleteOscillatoryAlignmentLedger
          frequencySupport n g U Q t := by
  letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
    ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
  rw [h15PostFEAffineAlignmentResidual_eq_collisionMatching_add_offDiagonal
    frequencySupport n g U Q t hQ]
  rw [h15PostFECollisionMatchingResidual_eq_staticGap_add_secondHarmonic
    frequencySupport n g U Q t hQ]
  simp only [h15PostFECompleteOscillatoryAlignmentLedger, dif_pos hQ]
  ring

/-- The full energy in the final correction-preserving collision normal
form. -/
theorem h15PostFEActualVaryingRowEnergy_eq_normImbalance_add_completeCollisionGap
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) (hQ : 0 < Q) :
    h15PostFEActualVaryingRowEnergy frequencySupport n g U Q t =
      h15PostFEAffineNormImbalanceDefect frequencySupport n g U Q t +
        2 *
          (h15PostFECompleteStaticCollisionGap frequencySupport n g U Q t +
            h15PostFECompleteOscillatoryAlignmentLedger
              frequencySupport n g U Q t) := by
  rw [h15PostFEActualVaryingRowEnergy_eq_affineDefects,
    h15PostFEAffineAntiparallelDefect_eq_two_mul_alignmentResidual,
    h15PostFEAffineAlignmentResidual_eq_completeCollisionGap
      frequencySupport n g U Q t hQ]

/-- Exact conditional endpoint: norm balance and decay of the two complete
signed ledgers imply decay of the actual varying-row energy. -/
theorem tendsto_h15PostFEActualVaryingRowEnergy_zero_of_completeCollisionGap
    (frequencySupport : ℕ → Finset ℕ)
    (n g U Q : ℕ → ℕ) (t : ℕ → ℝ)
    (hQ : ∀ k, 0 < Q k)
    (hnorm :
      Tendsto
        (fun k => h15PostFEAffineNormImbalanceDefect
          (frequencySupport k) (n k) (g k) (U k) (Q k) (t k))
        atTop (nhds 0))
    (hstatic :
      Tendsto
        (fun k => h15PostFECompleteStaticCollisionGap
          (frequencySupport k) (n k) (g k) (U k) (Q k) (t k))
        atTop (nhds 0))
    (hoscillatory :
      Tendsto
        (fun k => h15PostFECompleteOscillatoryAlignmentLedger
          (frequencySupport k) (n k) (g k) (U k) (Q k) (t k))
        atTop (nhds 0)) :
    Tendsto
      (fun k => h15PostFEActualVaryingRowEnergy
        (frequencySupport k) (n k) (g k) (U k) (Q k) (t k))
      atTop (nhds 0) := by
  have hgap :
      Tendsto
        (fun k => 2 *
          (h15PostFECompleteStaticCollisionGap
              (frequencySupport k) (n k) (g k) (U k) (Q k) (t k) +
            h15PostFECompleteOscillatoryAlignmentLedger
              (frequencySupport k) (n k) (g k) (U k) (Q k) (t k)))
        atTop (nhds 0) := by
    simpa only [zero_add, add_zero, mul_zero] using
      (hstatic.add hoscillatory).const_mul 2
  rw [show
      (fun k => h15PostFEActualVaryingRowEnergy
        (frequencySupport k) (n k) (g k) (U k) (Q k) (t k)) =
      (fun k => h15PostFEAffineNormImbalanceDefect
          (frequencySupport k) (n k) (g k) (U k) (Q k) (t k) +
        2 *
          (h15PostFECompleteStaticCollisionGap
              (frequencySupport k) (n k) (g k) (U k) (Q k) (t k) +
            h15PostFECompleteOscillatoryAlignmentLedger
              (frequencySupport k) (n k) (g k) (U k) (Q k) (t k))) by
    funext k
    exact h15PostFEActualVaryingRowEnergy_eq_normImbalance_add_completeCollisionGap
      (frequencySupport k) (n k) (g k) (U k) (Q k) (t k) (hQ k)]
  simpa only [zero_add] using hnorm.add hgap

end NBMellinTools.NB12
