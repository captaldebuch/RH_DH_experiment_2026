/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEDegenerateQuotientLedger

/-!
# NB12zzzaW: frequency-first form of the degenerate quotient ledger

The quotient-fiber ledger is expanded one final time without taking absolute
values.  For each natural frequency `r` and quotient `k`, the inner
dispersion retains:

* the endpoint missing atom and its canonical fiber-mean coefficient;
* the complete oriented pair atom, including its Archimedean normalization;
* the actual collision, external-incidence, and `p ∣ q*q'` support; and
* the exact quotient fiber `q*q'/p = k`.

The common nonnegative divisor-frequency factor
`normSq (h15DirectAdditiveFrequencyCoefficient r t)` is then pulled outside
the arithmetic fiber.  The complete degenerate collision ledger becomes a
finite signed frequency sum of finite signed quotient dispersions.

This is an exact normal form, not a decay estimate.  It identifies the next
analytic gate without replacing signed cancellation by an absolute envelope.
-/

open scoped BigOperators ComplexConjugate

namespace NBMellinTools.NB12

/-! ## One frequency inside one quotient fiber -/

noncomputable def h15PostFEDegenerateQuotientFrequencyFiberCorrelation
    (M : ℕ) [NeZero M] (n g U Q r : ℕ) (t : ℝ) (k : ℕ) : ℝ :=
  ∑ p ∈ (h15PostFEDegenerateCrossModulusCollisionSupport
      M n g U Q).filter
      (fun p => h15PostFEMissingPairDegenerateQuotient p = k),
    h15PostFEEndpointMissingAtom n g U Q r p.1 *
      h15PostFEOrientedPairAtomWithoutFrequency n g U Q r t p.2

/-- Literal coefficient-and-phase expansion of one `(r,k)` fiber.  This is
the form to compare with an external signed exponential-sum estimate. -/
theorem h15PostFEDegenerateQuotientFrequencyFiberCorrelation_eq_explicit
    (M : ℕ) [NeZero M] (n g U Q r : ℕ) (t : ℝ) (k : ℕ) :
    h15PostFEDegenerateQuotientFrequencyFiberCorrelation
        M n g U Q r t k =
      ∑ p ∈ (h15PostFEDegenerateCrossModulusCollisionSupport
          M n g U Q).filter
          (fun p => h15PostFEMissingPairDegenerateQuotient p = k),
        (h15PostFEResidueFiberEndpointMeanCoefficient n g U Q p.1.1 *
          (h15PostFEReducedDoubledAdditivePhase r p.1.2 p.1.1).im) *
        ((4 / (2 * h15PairedHyperbolicCoefficient t)) *
          (h15PostFEOrderedPairCollectedScalarWithoutFrequency
              n g U Q t p.2.1 *
            (conj
                (h15PostFEOrientationArchimedeanFactor p.2.2.1 t) *
              h15PostFEOrientationArchimedeanFactor p.2.2.2 t *
              h15PostFECommonPairAdditivePhase p.2.2.1 p.2.2.2 r
                p.2.1.1.1 p.2.1.1.2 p.2.1.2.1 p.2.1.2.2)).re) := by
  rfl

/-- The original quotient-fiber correlation is the signed frequency sum of
the frequency-free arithmetic fibers, weighted by the exact divisor-square
factor. -/
theorem h15PostFEDegenerateQuotientFiberCorrelation_eq_frequencySum
    (M : ℕ) [NeZero M] (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) (k : ℕ) :
    h15PostFEDegenerateQuotientFiberCorrelation
        M frequencySupport n g U Q t k =
      ∑ r ∈ frequencySupport,
        Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t) *
          h15PostFEDegenerateQuotientFrequencyFiberCorrelation
            M n g U Q r t k := by
  classical
  unfold h15PostFEDegenerateQuotientFiberCorrelation
    h15PostFEWeightedEndpointOrientedPairAtomCorrelation
    h15PostFEDegenerateQuotientFrequencyFiberCorrelation
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _hp
  ring

/-! ## Signed quotient dispersion at one frequency -/

noncomputable def h15PostFEDegenerateFrequencyQuotientDispersion
    (M : ℕ) [NeZero M] (n g U Q r : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ h15PostFEDegenerateQuotientSupport M n g U Q,
    h15PostFEDegenerateQuotientFrequencyFiberCorrelation
      M n g U Q r t k

/-- Complete frequency-first normal form of the density-degenerate ledger. -/
theorem h15PostFEDegenerateCollisionLedger_eq_frequencyDispersion
    (M : ℕ) [NeZero M] (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) :
    h15PostFEMissingPairDegenerateCrossModulusCollisionLedger
        M frequencySupport n g U Q t =
      ∑ r ∈ frequencySupport,
        Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t) *
          h15PostFEDegenerateFrequencyQuotientDispersion
            M n g U Q r t := by
  classical
  rw [h15PostFEDegenerateCollisionLedger_eq_sum_quotientFibers]
  simp_rw [h15PostFEDegenerateQuotientFiberCorrelation_eq_frequencySum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _hr
  unfold h15PostFEDegenerateFrequencyQuotientDispersion
  rw [Finset.mul_sum]

/-! ## A sufficient absolute frequency budget

This budget is deliberately separated from the exact signed normal form.
It is a sufficient route to decay, but may be stronger than necessary because
it discards cancellation between distinct natural frequencies. -/

noncomputable def h15PostFEDegenerateFrequencyDispersionL1Budget
    (M : ℕ) [NeZero M] (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) : ℝ :=
  ∑ r ∈ frequencySupport,
    Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t) *
      |h15PostFEDegenerateFrequencyQuotientDispersion
        M n g U Q r t|

theorem abs_h15PostFEDegenerateCollisionLedger_le_frequencyBudget
    (M : ℕ) [NeZero M] (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) :
    |h15PostFEMissingPairDegenerateCrossModulusCollisionLedger
        M frequencySupport n g U Q t| ≤
      h15PostFEDegenerateFrequencyDispersionL1Budget
        M frequencySupport n g U Q t := by
  rw [h15PostFEDegenerateCollisionLedger_eq_frequencyDispersion]
  refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
  unfold h15PostFEDegenerateFrequencyDispersionL1Budget
  apply Finset.sum_congr rfl
  intro r _hr
  rw [abs_mul, abs_of_nonneg (Complex.normSq_nonneg _)]

end NBMellinTools.NB12
