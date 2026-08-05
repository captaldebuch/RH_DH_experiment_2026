/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FinalBoundaryKloostermanNormAudit

/-!
# NB12zzu: cross-modulus square of the completed H15 nonzero sector

The moduluswise norm audit has no power saving.  The next legitimate object is
therefore the square of the complete signed outer-modulus sum, expanded before
any triangle inequality.  This file exposes its positive diagonal and literal
ordered distinct-modulus sector.

The diagonal is not identified here with the completed correction ledger.
Such an identification would be an analytic trace/residue theorem, not finite
Fourier algebra.
-/

open AddChar Complex ZMod
open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate

namespace NBMellinTools.NB12

/-- One completed nonzero interval block, grouped by its outer modulus `q`.
The inner modulus `q'`, both divisor variables, and the endpoint coordinate
remain inside the signed row. -/
noncomputable def h15ComplexIntervalBlockNonzeroOuterModulusRow
    (orientation : H15IntervalCompletionOrientation)
    (N g r U Q K : ℕ)
    (j : Fin (h15BoundarySpacingBlockCount Q K)) (q : ℕ) : ℂ :=
  ∑ q' ∈ (h15BettinChandeeSupportedNatBlock N g Q).erase q,
    ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
      ∑ d' ∈ h15DyadicActivePeriodSquareDivisorIndices g U q',
        ∑ u ∈ h15NormalizedSuperperiodBoundarySupport U
            (h15SquareDivisorProgressionModulus g d) q,
          h15ComplexIntervalOuterEndpointFactor N g r U
              (h15SquareDivisorProgressionModulus g d) q d u *
            h15ComplexIntervalEndpointNonzeroModeTotal orientation N g r U
              (h15SquareDivisorProgressionModulus g d') q q' d' u K j.val

/-- The completed nonzero block is exactly the signed sum of its outer-modulus
rows. -/
theorem h15ComplexIntervalBlockNonzeroModeAggregate_eq_sum_outerModulusRows
    (orientation : H15IntervalCompletionOrientation)
    (N g r U Q K : ℕ)
    (j : Fin (h15BoundarySpacingBlockCount Q K)) :
    h15ComplexIntervalBlockNonzeroModeAggregate orientation N g r U Q K j =
      ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        h15ComplexIntervalBlockNonzeroOuterModulusRow orientation
          N g r U Q K j q := by
  rfl

/-- Positive modulus diagonal of one completed nonzero block. -/
noncomputable def h15ComplexIntervalBlockNonzeroModulusDiagonal
    (orientation : H15IntervalCompletionOrientation)
    (N g r U Q K : ℕ)
    (j : Fin (h15BoundarySpacingBlockCount Q K)) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    Complex.normSq
      (h15ComplexIntervalBlockNonzeroOuterModulusRow orientation
        N g r U Q K j q)

/-- Literal ordered cross-modulus part of the completed nonzero square. -/
noncomputable def h15ComplexIntervalBlockNonzeroModulusOffDiagonal
    (orientation : H15IntervalCompletionOrientation)
    (N g r U Q K : ℕ)
    (j : Fin (h15BoundarySpacingBlockCount Q K)) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    ∑ q' ∈ (h15BettinChandeeSupportedNatBlock N g Q).erase q,
      (conj
          (h15ComplexIntervalBlockNonzeroOuterModulusRow orientation
            N g r U Q K j q) *
        h15ComplexIntervalBlockNonzeroOuterModulusRow orientation
          N g r U Q K j q').re

theorem h15ComplexIntervalBlockNonzeroModulusDiagonal_nonneg
    (orientation : H15IntervalCompletionOrientation)
    (N g r U Q K : ℕ)
    (j : Fin (h15BoundarySpacingBlockCount Q K)) :
    0 ≤ h15ComplexIntervalBlockNonzeroModulusDiagonal orientation
      N g r U Q K j := by
  unfold h15ComplexIntervalBlockNonzeroModulusDiagonal
  exact Finset.sum_nonneg (fun _q _hq => Complex.normSq_nonneg _)

private theorem normSq_sum_eq_sum_conj_mul_add_orderedOffDiagonal
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (F : ι → ℂ) :
    (Complex.normSq (∑ i ∈ s, F i) : ℂ) =
      (∑ i ∈ s, conj (F i) * F i) +
        ∑ i ∈ s, ∑ k ∈ s.erase i, conj (F i) * F k := by
  rw [Complex.normSq_eq_conj_mul_self]
  simp_rw [map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.add_sum_erase _ _ hi]

/-- Generic exact diagonal/off-diagonal expansion for a finite complex sum. -/
theorem normSq_sum_eq_sum_normSq_add_orderedOffDiagonal
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (F : ι → ℂ) :
    Complex.normSq (∑ i ∈ s, F i) =
      (∑ i ∈ s, Complex.normSq (F i)) +
        ∑ i ∈ s, ∑ k ∈ s.erase i, (conj (F i) * F k).re := by
  have hre (z : ℂ) : (conj z * z).re = Complex.normSq z := by
    rw [← Complex.normSq_eq_conj_mul_self]
    simp
  have h := congrArg Complex.re
    (normSq_sum_eq_sum_conj_mul_add_orderedOffDiagonal s F)
  simpa only [ofReal_re, add_re, Complex.re_sum, hre] using h

/-- Exact completed cross-modulus square.  Any saving must occur in the
ordered off-diagonal term, since the diagonal is nonnegative. -/
theorem normSq_h15ComplexIntervalBlockNonzeroModeAggregate_eq_diagonal_add_offDiagonal
    (orientation : H15IntervalCompletionOrientation)
    (N g r U Q K : ℕ)
    (j : Fin (h15BoundarySpacingBlockCount Q K)) :
    Complex.normSq
        (h15ComplexIntervalBlockNonzeroModeAggregate orientation
          N g r U Q K j) =
      h15ComplexIntervalBlockNonzeroModulusDiagonal orientation
          N g r U Q K j +
        h15ComplexIntervalBlockNonzeroModulusOffDiagonal orientation
          N g r U Q K j := by
  rw [h15ComplexIntervalBlockNonzeroModeAggregate_eq_sum_outerModulusRows]
  exact normSq_sum_eq_sum_normSq_add_orderedOffDiagonal
    (h15BettinChandeeSupportedNatBlock N g Q)
    (h15ComplexIntervalBlockNonzeroOuterModulusRow orientation
      N g r U Q K j)

/-- A target bound for the complete nonzero block is exactly a negative
cross-modulus compensation estimate against its positive diagonal. -/
theorem normSq_h15ComplexIntervalBlockNonzeroModeAggregate_le_iff_offDiagonal
    (orientation : H15IntervalCompletionOrientation)
    (N g r U Q K : ℕ)
    (j : Fin (h15BoundarySpacingBlockCount Q K)) (S : ℝ) :
    Complex.normSq
        (h15ComplexIntervalBlockNonzeroModeAggregate orientation
          N g r U Q K j) ≤ S ↔
      h15ComplexIntervalBlockNonzeroModulusOffDiagonal orientation
          N g r U Q K j ≤
        S - h15ComplexIntervalBlockNonzeroModulusDiagonal orientation
          N g r U Q K j := by
  constructor
  · intro h
    have heq :=
      normSq_h15ComplexIntervalBlockNonzeroModeAggregate_eq_diagonal_add_offDiagonal
        orientation N g r U Q K j
    linarith
  · intro h
    rw [normSq_h15ComplexIntervalBlockNonzeroModeAggregate_eq_diagonal_add_offDiagonal]
    linarith

end NBMellinTools.NB12
