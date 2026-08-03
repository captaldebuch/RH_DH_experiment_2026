/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15LocalizedLaurentProjection

/-!
# NB12zzz: localized functional-equation and frequency split

This file applies the verified Estermann functional equation and its exact
low/high frequency split to one fixed gcd slice and one dyadic outer-modulus
block of the H15 Laurent family.

The complementary Laurent rows remain a separate summand.  In particular,
the theorem below does not identify the localized contour family with the
endpoint trace and does not distribute the global residue ledger among
dyadic blocks.  Those are genuine downstream projection problems.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius
open Complex

namespace NBMellinTools.NB12

/-- Low-frequency functional-equation aggregate on one localized Laurent
slice. -/
noncomputable def h15LocalizedThreeHalfLowFrequencyAggregate
    (n g Q K : ℕ) (t : ℝ) : ℂ :=
  ∑ i ∈ h15LocalizedLaurentRowIndices (NB8.logTaperLength n) g Q,
    h15LaurentRowWeight i *
      bblsActiveThreeHalfLowFrequency (h15ContourDamping n)
        (h15LaurentRow i).numerator (h15LaurentRow i).denominator
        (h15LaurentRow i).coprime t K

/-- High-frequency functional-equation aggregate on the same localized
Laurent slice. -/
noncomputable def h15LocalizedThreeHalfHighFrequencyAggregate
    (n g Q K : ℕ) (t : ℝ) : ℂ :=
  ∑ i ∈ h15LocalizedLaurentRowIndices (NB8.logTaperLength n) g Q,
    h15LaurentRowWeight i *
      bblsActiveThreeHalfHighFrequency (h15ContourDamping n)
        (h15LaurentRow i).numerator (h15LaurentRow i).denominator
        (h15LaurentRow i).coprime t K

/-- Exact low/high decomposition of a localized Laurent slice on the
three-halves line. -/
theorem h15LocalizedActiveContourAggregate_threeHalf_eq_low_add_high
    (n g Q K : ℕ) (t : ℝ) :
    h15LocalizedActiveContourAggregate n g Q
        (bblsEstermannThreeHalfPoint t) =
      h15LocalizedThreeHalfLowFrequencyAggregate n g Q K t +
        h15LocalizedThreeHalfHighFrequencyAggregate n g Q K t := by
  unfold h15LocalizedActiveContourAggregate
    h15LocalizedThreeHalfLowFrequencyAggregate
    h15LocalizedThreeHalfHighFrequencyAggregate
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [bblsActiveReflectedExpression_threeHalf_eq_low_add_high
    (h15LaurentRow i).numerator (h15LaurentRow i).denominator
    (h15LaurentRow i).coprime t K]
  ring

/-! ## Explicit transformed-frequency slices -/

/-- One transformed Estermann frequency, summed only over the localized
Laurent rows.  This is the contour-side object whose frequency parameter is
to be compared with the endpoint-side parameter `r`. -/
noncomputable def h15LocalizedThreeHalfFrequencySlice
    (n g Q r : ℕ) (t : ℝ) : ℂ :=
  ∑ i ∈ h15LocalizedLaurentRowIndices (NB8.logTaperLength n) g Q,
    h15LaurentRowWeight i *
      bblsActiveThreeHalfFrequencyTerm (h15ContourDamping n)
        (h15LaurentRow i).numerator (h15LaurentRow i).denominator
        (h15LaurentRow i).coprime r t

/-- The same localized slice after the already verified double-inversion
collapse.  Invalid Laurent rows are zero by construction, so this definition
does not enlarge the active support. -/
noncomputable def h15LocalizedDirectAdditiveFrequencySlice
    (n g Q r : ℕ) (t : ℝ) : ℂ :=
  ∑ i ∈ h15LocalizedLaurentRowIndices (NB8.logTaperLength n) g Q,
    h15DirectAdditiveFixedHeightSummand (NB8.logTaperLength n)
      (h15ContourDamping n) (i, r) t

/-- Exact direct-additive realization of every localized transformed
frequency. -/
theorem h15LocalizedThreeHalfFrequencySlice_eq_direct
    (n g Q r : ℕ) (t : ℝ) :
    h15LocalizedThreeHalfFrequencySlice n g Q r t =
      h15LocalizedDirectAdditiveFrequencySlice n g Q r t := by
  unfold h15LocalizedThreeHalfFrequencySlice
    h15LocalizedDirectAdditiveFrequencySlice
  apply Finset.sum_congr rfl
  intro i _hi
  exact h15WeightedFrequencyTerm_eq_directFixedHeightSummand
    (NB8.logTaperLength n) (h15ContourDamping n) (i, r) t

/-- The low-frequency part of one functional-equation row is exactly the
finite sum of its individual transformed-frequency terms. -/
theorem bblsActiveThreeHalfLowFrequency_eq_sum_frequencyTerm
    {damping : ℝ} (a q : ℕ) [NeZero q]
    (haq : Nat.Coprime a q) (t : ℝ) (K : ℕ) :
    bblsActiveThreeHalfLowFrequency damping a q haq t K =
      ∑ r ∈ Finset.range (K + 1),
        bblsActiveThreeHalfFrequencyTerm damping a q haq r t := by
  unfold bblsActiveThreeHalfLowFrequency
    bblsEstermannHurwitzLowFrequency bblsEstermannLowFrequency
    bblsActiveThreeHalfFrequencyTerm
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  rw [Finset.mul_sum]

/-- Exact finite-frequency expansion of the localized low sector. -/
theorem h15LocalizedThreeHalfLowFrequencyAggregate_eq_sum_slices
    (n g Q K : ℕ) (t : ℝ) :
    h15LocalizedThreeHalfLowFrequencyAggregate n g Q K t =
      ∑ r ∈ Finset.range (K + 1),
        h15LocalizedThreeHalfFrequencySlice n g Q r t := by
  classical
  unfold h15LocalizedThreeHalfLowFrequencyAggregate
    h15LocalizedThreeHalfFrequencySlice
  simp_rw [bblsActiveThreeHalfLowFrequency_eq_sum_frequencyTerm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [Finset.mul_sum]

/-- The localized low sector is therefore a finite sum of literal paired
direct-additive H15 slices. -/
theorem h15LocalizedThreeHalfLowFrequencyAggregate_eq_sum_direct_slices
    (n g Q K : ℕ) (t : ℝ) :
    h15LocalizedThreeHalfLowFrequencyAggregate n g Q K t =
      ∑ r ∈ Finset.range (K + 1),
        h15LocalizedDirectAdditiveFrequencySlice n g Q r t := by
  rw [h15LocalizedThreeHalfLowFrequencyAggregate_eq_sum_slices]
  apply Finset.sum_congr rfl
  intro r _hr
  exact h15LocalizedThreeHalfFrequencySlice_eq_direct n g Q r t

/-- An unsupported dyadic Laurent slice has no transformed-frequency
contribution, at every frequency and height. -/
theorem h15LocalizedThreeHalfFrequencySlice_eq_zero_of_lt
    {n g Q r : ℕ} (h : NB8.logTaperLength n < g * Q) (t : ℝ) :
    h15LocalizedThreeHalfFrequencySlice n g Q r t = 0 := by
  unfold h15LocalizedThreeHalfFrequencySlice
    h15LocalizedLaurentRowIndices
  rw [h15BettinChandeeSupportedNatBlock_eq_empty_of_lt h]
  simp

/-- The full vertical aggregate is the localized low sector, the localized
high sector, and the untouched complementary Laurent ledger. -/
theorem h15VerticalAggregate_threeHalf_eq_localized_low_add_high_add_complement
    (n g Q K : ℕ) (t : ℝ) :
    h15VerticalAggregate n (3 / 2) t =
      h15LocalizedThreeHalfLowFrequencyAggregate n g Q K t +
        h15LocalizedThreeHalfHighFrequencyAggregate n g Q K t +
          h15ComplementaryActiveContourAggregate n g Q
            (bblsEstermannThreeHalfPoint t) := by
  have hpoint : ((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I =
      bblsEstermannThreeHalfPoint t := by
    norm_num [bblsEstermannThreeHalfPoint]
    ring
  unfold h15VerticalAggregate
  rw [hpoint, h15ActiveContourAggregate_eq_localized_add_complement,
    h15LocalizedActiveContourAggregate_threeHalf_eq_low_add_high]

/-- Unsupported localized slices have no low-frequency contribution. -/
theorem h15LocalizedThreeHalfLowFrequencyAggregate_eq_zero_of_lt
    {n g Q K : ℕ} (h : NB8.logTaperLength n < g * Q) (t : ℝ) :
    h15LocalizedThreeHalfLowFrequencyAggregate n g Q K t = 0 := by
  unfold h15LocalizedThreeHalfLowFrequencyAggregate
    h15LocalizedLaurentRowIndices
  rw [h15BettinChandeeSupportedNatBlock_eq_empty_of_lt h]
  simp

/-- Unsupported localized slices have no high-frequency contribution. -/
theorem h15LocalizedThreeHalfHighFrequencyAggregate_eq_zero_of_lt
    {n g Q K : ℕ} (h : NB8.logTaperLength n < g * Q) (t : ℝ) :
    h15LocalizedThreeHalfHighFrequencyAggregate n g Q K t = 0 := by
  unfold h15LocalizedThreeHalfHighFrequencyAggregate
    h15LocalizedLaurentRowIndices
  rw [h15BettinChandeeSupportedNatBlock_eq_empty_of_lt h]
  simp

end NBMellinTools.NB12
