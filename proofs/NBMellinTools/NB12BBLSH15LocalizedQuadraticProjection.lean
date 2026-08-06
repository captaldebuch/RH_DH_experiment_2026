/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15LocalizedFrequencySplit

/-!
# NB12zzza: the quadratic endpoint projection

The localized functional-equation aggregate is linear in each transformed
Estermann frequency.  The final H15 endpoint boundary is not: its real phase
is the cross-orientation term in the squared norm of the paired direct kernel.

This file records the exact quadratic extractor.  After subtracting the two
unsigned norm-square modes, division by the nonzero hyperbolic coefficient
recovers `h15PairedDirectCrossMode`.  The identity is then lifted through the
complete endpoint cutoff and square-divisor incidence sums.  Thus the
remaining contour-to-boundary problem is a quadratic spectral projection,
not a linear identification of frequency slices.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate
open Complex

namespace NBMellinTools.NB12

/-- Squared norm of the paired direct kernel after removing its two unsigned
pointwise modes. -/
noncomputable def h15PairedDirectCenteredNormSq
    (t : ℝ) (r u q : ℕ) : ℝ :=
  Complex.normSq (h15PairedDirectKernel t r u q) -
    (1 + h15PairedHyperbolicCoefficient t ^ 2)

/-- Exact centered-norm identity: the only surviving term is the signed
doubled additive-character cross mode. -/
theorem h15PairedDirectCenteredNormSq_eq_crossMode
    (t : ℝ) (r u q : ℕ) (hq : 0 < q) (huq : Nat.Coprime u q) :
    h15PairedDirectCenteredNormSq t r u q =
      2 * h15PairedHyperbolicCoefficient t *
        h15PairedDirectCrossMode r u q := by
  unfold h15PairedDirectCenteredNormSq h15PairedDirectCrossMode
  rw [normSq_h15PairedDirectKernel t r u q hq huq]
  ring

/-- At every height with nonzero hyperbolic coefficient, the final-boundary
cross mode is recovered exactly from the centered paired norm square. -/
theorem h15PairedDirectCrossMode_eq_centeredNormSq_div
    (t : ℝ) (r u q : ℕ) (hq : 0 < q) (huq : Nat.Coprime u q)
    (hS : h15PairedHyperbolicCoefficient t ≠ 0) :
    h15PairedDirectCrossMode r u q =
      h15PairedDirectCenteredNormSq t r u q /
        (2 * h15PairedHyperbolicCoefficient t) := by
  rw [h15PairedDirectCenteredNormSq_eq_crossMode t r u q hq huq]
  field_simp

/-- One correction-coupled endpoint row written as a centered quadratic
spectral projection.  The full endpoint support and its signed point weights
are retained verbatim. -/
noncomputable def h15NormalizedProgressionCoupledBoundarySpectralRow
    (N g r U L q d : ℕ) (t : ℝ) : ℝ :=
  ∑ u ∈ h15NormalizedSuperperiodBoundarySupport U L q,
    h15NormalizedProgressionCoupledBoundaryPointWeight N g U L q d u *
      (h15PairedDirectCenteredNormSq t r u q /
        (2 * h15PairedHyperbolicCoefficient t))

/-- Exact rowwise endpoint projection from the centered paired spectral
kernel. -/
theorem h15NormalizedProgressionCoupledBoundarySpectralRow_eq_pointRow
    (N g r U L q d : ℕ) (t : ℝ) (hq : 0 < q)
    (hS : h15PairedHyperbolicCoefficient t ≠ 0) :
    h15NormalizedProgressionCoupledBoundarySpectralRow
        N g r U L q d t =
      h15NormalizedProgressionCoupledBoundaryPointRow N g r U L q d := by
  unfold h15NormalizedProgressionCoupledBoundarySpectralRow
    h15NormalizedProgressionCoupledBoundaryPointRow
  apply Finset.sum_congr rfl
  intro u hu
  rw [← h15PairedDirectCrossMode_eq_centeredNormSq_div
    t r u q hq
      (coprime_of_mem_h15NormalizedSuperperiodBoundarySupport hu) hS]

/-- Complete active-incidence spectral endpoint projection. -/
noncomputable def h15NormalizedBoundarySpectralAggregate
    (N g r U Q : ℕ) (t : ℝ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
      h15NormalizedProgressionCoupledBoundarySpectralRow N g r U
        (h15SquareDivisorProgressionModulus g d) q d t

/-- The spectral endpoint projection is exactly the already verified final
boundary Fourier aggregate.  No endpoint or correction weight is discarded. -/
theorem h15NormalizedBoundarySpectralAggregate_eq_fourierAggregate
    (N g r U Q : ℕ) (t : ℝ) (hQ : 0 < Q)
    (hS : h15PairedHyperbolicCoefficient t ≠ 0) :
    h15NormalizedBoundarySpectralAggregate N g r U Q t =
      h15NormalizedBoundaryFourierAggregate N g r U Q := by
  unfold h15NormalizedBoundarySpectralAggregate
    h15NormalizedBoundaryFourierAggregate
  apply Finset.sum_congr rfl
  intro q hqMem
  have hqBounds := mem_h15BettinChandeeSupportedNatBlock.mp hqMem
  have hqPos : 0 < q := hQ.trans_le hqBounds.1
  apply Finset.sum_congr rfl
  intro d _hd
  rw [h15NormalizedProgressionCoupledBoundarySpectralRow_eq_pointRow
      N g r U (h15SquareDivisorProgressionModulus g d) q d t hqPos hS,
    h15NormalizedBoundaryFourierRowValue_eq_pointRow
      N g r U (h15SquareDivisorProgressionModulus g d) q d hqPos]

/-! ## Quadratic lifting through the localized Laurent coefficients -/

/-- Positive row diagonal created by squaring one localized direct-additive
frequency slice. -/
noncomputable def h15LocalizedDirectAdditiveFrequencyDiagonal
    (n g Q r : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ h15LocalizedLaurentRowIndices (NB8.logTaperLength n) g Q,
    Complex.normSq
      (h15DirectAdditiveFixedHeightSummand (NB8.logTaperLength n)
        (h15ContourDamping n) (i, r) t)

/-- Literal ordered cross-row sector created by the same square. -/
noncomputable def h15LocalizedDirectAdditiveFrequencyOffDiagonal
    (n g Q r : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ h15LocalizedLaurentRowIndices (NB8.logTaperLength n) g Q,
    ∑ j ∈ (h15LocalizedLaurentRowIndices
        (NB8.logTaperLength n) g Q).erase i,
      (conj
          (h15DirectAdditiveFixedHeightSummand (NB8.logTaperLength n)
            (h15ContourDamping n) (i, r) t) *
        h15DirectAdditiveFixedHeightSummand (NB8.logTaperLength n)
          (h15ContourDamping n) (j, r) t).re

/-- Exact diagonal/ordered-cross-row expansion of a localized contour
frequency slice. -/
theorem normSq_h15LocalizedDirectAdditiveFrequencySlice_eq_diagonal_add_offDiagonal
    (n g Q r : ℕ) (t : ℝ) :
    Complex.normSq (h15LocalizedDirectAdditiveFrequencySlice n g Q r t) =
      h15LocalizedDirectAdditiveFrequencyDiagonal n g Q r t +
        h15LocalizedDirectAdditiveFrequencyOffDiagonal n g Q r t := by
  unfold h15LocalizedDirectAdditiveFrequencySlice
    h15LocalizedDirectAdditiveFrequencyDiagonal
    h15LocalizedDirectAdditiveFrequencyOffDiagonal
  exact normSq_sum_eq_sum_normSq_add_orderedOffDiagonal
    (h15LocalizedLaurentRowIndices (NB8.logTaperLength n) g Q)
    (fun i => h15DirectAdditiveFixedHeightSummand
      (NB8.logTaperLength n) (h15ContourDamping n) (i, r) t)

/-- The exact fixed-height defect between the endpoint spectral projection
and the raw square of the localized Laurent slice.  It records, without any
estimate, the difference in coefficient degree, endpoint cutoff and
square-divisor incidence. -/
noncomputable def h15LocalizedQuadraticLiftDefect
    (n g Q r U : ℕ) (t : ℝ) : ℝ :=
  h15NormalizedBoundarySpectralAggregate
      (NB8.logTaperLength n) g r U Q t -
    Complex.normSq (h15LocalizedDirectAdditiveFrequencySlice n g Q r t)

/-- Complete fixed-height projection ledger.  The named defect is exactly
what must be transformed or estimated before the contour square can control
the endpoint boundary. -/
theorem h15NormalizedBoundaryFourierAggregate_eq_localizedQuadraticLedger
    (n g Q r U : ℕ) (t : ℝ) (hQ : 0 < Q)
    (hS : h15PairedHyperbolicCoefficient t ≠ 0) :
    h15NormalizedBoundaryFourierAggregate
        (NB8.logTaperLength n) g r U Q =
      h15LocalizedDirectAdditiveFrequencyDiagonal n g Q r t +
        h15LocalizedDirectAdditiveFrequencyOffDiagonal n g Q r t +
          h15LocalizedQuadraticLiftDefect n g Q r U t := by
  rw [← h15NormalizedBoundarySpectralAggregate_eq_fourierAggregate
    (NB8.logTaperLength n) g r U Q t hQ hS]
  unfold h15LocalizedQuadraticLiftDefect
  rw [normSq_h15LocalizedDirectAdditiveFrequencySlice_eq_diagonal_add_offDiagonal]
  ring

end NBMellinTools.NB12
