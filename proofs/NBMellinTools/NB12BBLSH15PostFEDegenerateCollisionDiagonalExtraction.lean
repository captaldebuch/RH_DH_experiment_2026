/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEDegenerateCollisionHarmonicLedger

/-!
# NB12zzzbA: extraction of the full degenerate collision diagonal

The collision diagonal is independent of the natural frequency `r`.  This
file pulls it through the outer divisor-frequency norm-square sum.  The full
degenerate ledger is thereby written exactly as

`frequency mass * collision diagonal + weighted second harmonic`.

This identifies the term that must be compared with the retained global
correction.  It does not assert that a single cross-modulus subsector equals
that global correction: the endpoint-incidence, shared-modulus, favorable,
missing--missing, and off-diagonal sectors remain separate parts of the
complete correction ledger.
-/

open scoped BigOperators

namespace NBMellinTools.NB12

noncomputable def h15PostFEDegenerateFrequencyMass
    (frequencySupport : Finset ℕ) (t : ℝ) : ℝ :=
  ∑ r ∈ frequencySupport,
    Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t)

noncomputable def h15PostFEDegenerateWeightedSecondHarmonicLedger
    (M : ℕ) [NeZero M] (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) : ℝ :=
  ∑ r ∈ frequencySupport,
    Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t) *
      h15PostFEDegenerateCollisionSecondHarmonicDispersion
        M n g U Q r t

noncomputable def h15PostFEDegenerateExtractedDiagonalContribution
    (M : ℕ) [NeZero M] (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) : ℝ :=
  h15PostFEDegenerateFrequencyMass frequencySupport t *
    h15PostFEDegenerateCollisionDiagonalDispersion M n g U Q t

/-- The complete degenerate ledger is an extracted constant diagonal plus
the still-signed doubled-frequency remainder. -/
theorem h15PostFEDegenerateCollisionLedger_eq_extractedDiagonal_add_secondHarmonic
    {n g U Q : ℕ}
    [NeZero (h15PostFEActualCommonSuperperiod n g U Q)]
    (hQ : 0 < Q) (frequencySupport : Finset ℕ) (t : ℝ) :
    h15PostFEMissingPairDegenerateCrossModulusCollisionLedger
        (h15PostFEActualCommonSuperperiod n g U Q)
        frequencySupport n g U Q t =
      h15PostFEDegenerateExtractedDiagonalContribution
          (h15PostFEActualCommonSuperperiod n g U Q)
          frequencySupport n g U Q t +
        h15PostFEDegenerateWeightedSecondHarmonicLedger
          (h15PostFEActualCommonSuperperiod n g U Q)
          frequencySupport n g U Q t := by
  rw [h15PostFEDegenerateCollisionLedger_eq_frequencyDispersion]
  simp_rw [h15PostFEDegenerateFrequencyQuotientDispersion_eq_diagonal_add_secondHarmonic
    hQ]
  unfold h15PostFEDegenerateExtractedDiagonalContribution
    h15PostFEDegenerateFrequencyMass
    h15PostFEDegenerateWeightedSecondHarmonicLedger
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_mul]

/-- Equivalent subtraction form: after removing the explicit second
harmonic, exactly the extracted collision diagonal remains. -/
theorem h15PostFEDegenerateCollisionLedger_sub_secondHarmonic_eq_extractedDiagonal
    {n g U Q : ℕ}
    [NeZero (h15PostFEActualCommonSuperperiod n g U Q)]
    (hQ : 0 < Q) (frequencySupport : Finset ℕ) (t : ℝ) :
    h15PostFEMissingPairDegenerateCrossModulusCollisionLedger
          (h15PostFEActualCommonSuperperiod n g U Q)
          frequencySupport n g U Q t -
        h15PostFEDegenerateWeightedSecondHarmonicLedger
          (h15PostFEActualCommonSuperperiod n g U Q)
          frequencySupport n g U Q t =
      h15PostFEDegenerateExtractedDiagonalContribution
        (h15PostFEActualCommonSuperperiod n g U Q)
        frequencySupport n g U Q t := by
  rw [h15PostFEDegenerateCollisionLedger_eq_extractedDiagonal_add_secondHarmonic
    hQ frequencySupport t]
  ring

theorem h15PostFEDegenerateFrequencyMass_nonneg
    (frequencySupport : Finset ℕ) (t : ℝ) :
    0 ≤ h15PostFEDegenerateFrequencyMass frequencySupport t := by
  unfold h15PostFEDegenerateFrequencyMass
  exact Finset.sum_nonneg fun r _hr =>
    Complex.normSq_nonneg (h15DirectAdditiveFrequencyCoefficient r t)

end NBMellinTools.NB12
