/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB15GlobalPostFEAssembly
import NBMellinTools.NB12BBLSH15FrequencyIntegral

/-!
# Exact vertical frequency pairing for the global H15 PostFE assembly

`NB15GlobalPostFEAssembly` identifies the low-frequency right-line aggregate
with a finite sum of globally assembled linear frequency slices.  This file
takes the next exact step: on every finite vertical interval it expands the
square norm of that sum into its complete signed pairing matrix.

The index set is the product of the frequency cutoff with the canonical
dyadic block support.  Consequently the resulting quadratic expression keeps
both cross-frequency and cross-block interactions.  No diagonal, residue, or
correction term is discarded.

This is a finite vertical pairing identity, not yet the missing identification
of the Estermann right-line aggregate with the Mellin transform of the
certified Nyman--Beurling residual.  That normalization theorem remains the
next bridge.
-/

open scoped BigOperators ComplexConjugate Interval

namespace NBMellinTools.NB15

open Complex MeasureTheory
open NBMellinTools.NB8
open NBMellinTools.NB12

/-! ## Flattened block--frequency support -/

/-- A low-mode index together with one canonical PostFE dyadic block. -/
abbrev H15GlobalPostFEFrequencyBlockIndex :=
  ℕ × H15GlobalPostFEBlockKey

/-- Complete finite support of frequency--block pairs below cutoff `K`. -/
def h15GlobalPostFEFrequencyBlockSupport (n K : ℕ) :
    Finset H15GlobalPostFEFrequencyBlockIndex :=
  Finset.range (K + 1) ×ˢ
    h15GlobalPostFEBlockSupport (logTaperLength n)

/-- One local linear term in the flattened block--frequency expansion. -/
noncomputable def h15GlobalPostFEFrequencyBlockTerm
    (n : ℕ) (p : H15GlobalPostFEFrequencyBlockIndex) (t : ℝ) : ℂ :=
  h15PostFELocalizedDirectAdditiveFrequencySlice n
    (h15GlobalPostFEBlockG p.2) (h15GlobalPostFEBlockU p.2)
    (h15GlobalPostFEBlockQ p.2) p.1 t

/-- The genuine low-frequency right-line aggregate is exactly the flattened
finite sum over all frequencies and all canonical dyadic blocks. -/
theorem h15ThreeHalfLowFrequencyAggregate_eq_frequencyBlockSum
    (n K : ℕ) (t : ℝ) :
    h15ThreeHalfLowFrequencyAggregate n K t =
      ∑ p ∈ h15GlobalPostFEFrequencyBlockSupport n K,
        h15GlobalPostFEFrequencyBlockTerm n p t := by
  rw [h15ThreeHalfLowFrequencyAggregate_eq_globalPostFESlices]
  unfold h15GlobalPostFEFrequencyBlockSupport
    h15GlobalPostFEFrequencyBlockTerm
    h15GlobalPostFELinearFrequencySlice
  rw [Finset.sum_product]

/-! ## Continuity and compact-interval integrability -/

theorem continuous_h15GlobalPostFEFrequencyBlockTerm
    (n : ℕ) (p : H15GlobalPostFEFrequencyBlockIndex) :
    Continuous (h15GlobalPostFEFrequencyBlockTerm n p) := by
  unfold h15GlobalPostFEFrequencyBlockTerm
    h15PostFELocalizedDirectAdditiveFrequencySlice
  apply continuous_finsetSum
  intro i _hi
  have heq :
      (fun t => h15DirectAdditiveFixedHeightSummand
        (logTaperLength n) (h15ContourDamping n) (i, p.1) t) =
        fun t => h15LaurentRowWeight i *
          bblsActiveThreeHalfFrequencyTerm (h15ContourDamping n)
            (h15LaurentRow i).numerator (h15LaurentRow i).denominator
            (h15LaurentRow i).coprime p.1 t := by
    funext t
    exact (h15WeightedFrequencyTerm_eq_directFixedHeightSummand
      (logTaperLength n) (h15ContourDamping n) (i, p.1) t).symm
  change Continuous (fun t => h15DirectAdditiveFixedHeightSummand
    (logTaperLength n) (h15ContourDamping n) (i, p.1) t)
  rw [heq]
  exact continuous_const.mul
    (continuous_bblsActiveThreeHalfFrequencyTerm
      (h15ContourDamping_pos n)
      (h15LaurentRow i).numerator (h15LaurentRow i).denominator
      (h15LaurentRow i).coprime p.1)

theorem continuous_h15GlobalPostFELinearFrequencySlice
    (n r : ℕ) :
    Continuous (h15GlobalPostFELinearFrequencySlice n r) := by
  unfold h15GlobalPostFELinearFrequencySlice
  apply continuous_finsetSum
  intro b _hb
  exact continuous_h15GlobalPostFEFrequencyBlockTerm n (r, b)

theorem continuous_h15ThreeHalfLowFrequencyAggregate
    (n K : ℕ) :
    Continuous (h15ThreeHalfLowFrequencyAggregate n K) := by
  rw [show h15ThreeHalfLowFrequencyAggregate n K =
      fun t => ∑ r ∈ Finset.range (K + 1),
        h15GlobalPostFELinearFrequencySlice n r t by
    funext t
    exact h15ThreeHalfLowFrequencyAggregate_eq_globalPostFESlices n K t]
  apply continuous_finsetSum
  intro r _hr
  exact continuous_h15GlobalPostFELinearFrequencySlice n r

/-! ## Pointwise signed pairing matrix -/

/-- The real Hermitian pairing of two block--frequency terms.  Individual
entries can have either sign. -/
noncomputable def h15GlobalPostFEFrequencyPairKernel
    (n : ℕ) (p q : H15GlobalPostFEFrequencyBlockIndex) (t : ℝ) : ℝ :=
  (conj (h15GlobalPostFEFrequencyBlockTerm n p t) *
    h15GlobalPostFEFrequencyBlockTerm n q t).re

theorem continuous_h15GlobalPostFEFrequencyPairKernel
    (n : ℕ) (p q : H15GlobalPostFEFrequencyBlockIndex) :
    Continuous (h15GlobalPostFEFrequencyPairKernel n p q) := by
  unfold h15GlobalPostFEFrequencyPairKernel
  exact Complex.continuous_re.comp
    ((Complex.continuous_conj.comp
        (continuous_h15GlobalPostFEFrequencyBlockTerm n p)).mul
      (continuous_h15GlobalPostFEFrequencyBlockTerm n q))

private theorem normSq_finsetSum_eq_completePairing
    {ι : Type*} (s : Finset ι) (F : ι → ℂ) :
    Complex.normSq (∑ i ∈ s, F i) =
      ∑ i ∈ s, ∑ j ∈ s, (conj (F i) * F j).re := by
  have hcomplex :
      (Complex.normSq (∑ i ∈ s, F i) : ℂ) =
        ∑ i ∈ s, ∑ j ∈ s, conj (F i) * F j := by
    rw [Complex.normSq_eq_conj_mul_self]
    simp_rw [map_sum, Finset.sum_mul, Finset.mul_sum]
  have hre := congrArg Complex.re hcomplex
  simpa only [ofReal_re, Complex.re_sum] using hre

/-- Exact pointwise expansion of the complete low-frequency square.  The
right side contains diagonal, cross-frequency, cross-block, and simultaneous
cross-frequency/cross-block entries. -/
theorem normSq_h15ThreeHalfLowFrequencyAggregate_eq_completePairing
    (n K : ℕ) (t : ℝ) :
    Complex.normSq (h15ThreeHalfLowFrequencyAggregate n K t) =
      ∑ p ∈ h15GlobalPostFEFrequencyBlockSupport n K,
        ∑ q ∈ h15GlobalPostFEFrequencyBlockSupport n K,
          h15GlobalPostFEFrequencyPairKernel n p q t := by
  rw [h15ThreeHalfLowFrequencyAggregate_eq_frequencyBlockSum]
  exact normSq_finsetSum_eq_completePairing
    (h15GlobalPostFEFrequencyBlockSupport n K)
    (fun p => h15GlobalPostFEFrequencyBlockTerm n p t)

/-! ## Exact finite vertical energy identity -/

/-- The actual finite vertical `L²` energy of the complete low-frequency
Estermann aggregate. -/
noncomputable def h15TruncatedLowFrequencyVerticalEnergy
    (n K : ℕ) (T : ℝ) : ℝ :=
  ∫ t : ℝ in -T..T,
    Complex.normSq (h15ThreeHalfLowFrequencyAggregate n K t)

/-- Its complete signed block--frequency pairing expansion. -/
noncomputable def h15TruncatedGlobalPostFEFrequencyPairing
    (n K : ℕ) (T : ℝ) : ℝ :=
  ∑ p ∈ h15GlobalPostFEFrequencyBlockSupport n K,
    ∑ q ∈ h15GlobalPostFEFrequencyBlockSupport n K,
      ∫ t : ℝ in -T..T,
        h15GlobalPostFEFrequencyPairKernel n p q t

/-- Finite vertical Plancherel/pairing identity.  This is an equality, with
no use of triangle inequalities and therefore no loss of the signed
cross-block or cross-frequency cancellation. -/
theorem h15TruncatedLowFrequencyVerticalEnergy_eq_completePairing
    (n K : ℕ) (T : ℝ) :
    h15TruncatedLowFrequencyVerticalEnergy n K T =
      h15TruncatedGlobalPostFEFrequencyPairing n K T := by
  unfold h15TruncatedLowFrequencyVerticalEnergy
    h15TruncatedGlobalPostFEFrequencyPairing
  rw [intervalIntegral.integral_congr
    (fun t _ht =>
      normSq_h15ThreeHalfLowFrequencyAggregate_eq_completePairing n K t)]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [intervalIntegral.integral_finsetSum]
    intro q hq
    exact (continuous_h15GlobalPostFEFrequencyPairKernel n p q).intervalIntegrable
      (-T) T
  · intro p hp
    have hfun :
        (fun x => ∑ q ∈ h15GlobalPostFEFrequencyBlockSupport n K,
          h15GlobalPostFEFrequencyPairKernel n p q x) =
          ∑ q ∈ h15GlobalPostFEFrequencyBlockSupport n K,
            (fun x => h15GlobalPostFEFrequencyPairKernel n p q x) := by
      funext x
      simp
    rw [hfun]
    exact IntervalIntegrable.sum
      (h15GlobalPostFEFrequencyBlockSupport n K)
      (fun q _hq =>
        Continuous.intervalIntegrable (μ := volume)
          (continuous_h15GlobalPostFEFrequencyPairKernel n p q) (-T) T)

end NBMellinTools.NB15
