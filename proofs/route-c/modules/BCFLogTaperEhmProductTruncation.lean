import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmPairedAdditiveRows

/-!
# Product-coordinate truncation of the paired Ehm rows

The paired additive row is split exactly at an arbitrary product cutoff
`Y`.  The low range is `2 ≤ n ≤ min Y J`; the high range is
`max 2 (Y+1) ≤ n ≤ J`.  These definitions cover all relative positions of
`Y`, `J`, and the lower endpoint without side conditions.

This module proves only finite identities and coordinate-range facts.  It
makes no analytic estimate for the high-product row.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmProductTruncation

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFourierResonanceAudit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPairedAdditiveRows
open RH.Criteria.NymanBeurling.BCFLogTaperEhmVaalerNormalizedCharacters

/-! ## Exact low and high product ranges -/

/-- Product coordinates retained below the cutoff `Y`. -/
def ehmDyadicVaalerLowProductRange (J Y : ℕ) : Finset ℕ :=
  Finset.Icc 2 (min Y J)

/-- Product coordinates strictly above the cutoff `Y`. -/
def ehmDyadicVaalerHighProductRange (J Y : ℕ) : Finset ℕ :=
  Finset.Icc (max 2 (Y + 1)) J

theorem mem_ehmDyadicVaalerLowProductRange_iff
    (J Y n : ℕ) :
    n ∈ ehmDyadicVaalerLowProductRange J Y ↔
      2 ≤ n ∧ n ≤ J ∧ n ≤ Y := by
  simp only [ehmDyadicVaalerLowProductRange, Finset.mem_Icc]
  omega

theorem mem_ehmDyadicVaalerHighProductRange_iff
    (J Y n : ℕ) :
    n ∈ ehmDyadicVaalerHighProductRange J Y ↔
      2 ≤ n ∧ n ≤ J ∧ Y < n := by
  simp only [ehmDyadicVaalerHighProductRange, Finset.mem_Icc]
  omega

/-- Every retained product coordinate satisfies the advertised bound. -/
theorem ehmDyadicVaalerLowProductCoordinate_le
    {J Y n : ℕ} (hn : n ∈ ehmDyadicVaalerLowProductRange J Y) :
    n ≤ Y :=
  (mem_ehmDyadicVaalerLowProductRange_iff J Y n).1 hn |>.2.2

private theorem low_union_high_eq_full (J Y : ℕ) :
    ehmDyadicVaalerLowProductRange J Y ∪
        ehmDyadicVaalerHighProductRange J Y =
      Finset.Icc 2 J := by
  ext n
  simp only [Finset.mem_union,
    mem_ehmDyadicVaalerLowProductRange_iff,
    mem_ehmDyadicVaalerHighProductRange_iff, Finset.mem_Icc]
  omega

private theorem low_disjoint_high (J Y : ℕ) :
    Disjoint (ehmDyadicVaalerLowProductRange J Y)
      (ehmDyadicVaalerHighProductRange J Y) := by
  apply Finset.disjoint_left.mpr
  intro n hnLow hnHigh
  have hnY := ehmDyadicVaalerLowProductCoordinate_le hnLow
  have hYn :=
    (mem_ehmDyadicVaalerHighProductRange_iff J Y n).1 hnHigh |>.2.2
  omega

/-! ## One-row truncation -/

/-- One paired summand at product coordinate `n`. -/
noncomputable def ehmDyadicVaalerPairedProductSummand
    (h : ℤ) (X D m n : ℕ) : ℂ :=
  ((ehmDyadicVaalerPairedProductCoefficient X D m n / (n : ℝ) : ℝ) : ℂ) *
    ehmVaalerRationalPhase h n 1 m

/-- The retained low-product part of one paired additive row. -/
noncomputable def ehmDyadicVaalerPairedLowProductRow
    (h : ℤ) (X D J Y m : ℕ) : ℂ :=
  ∑ n ∈ ehmDyadicVaalerLowProductRange J Y,
    ehmDyadicVaalerPairedProductSummand h X D m n

/-- The complementary high-product part of one paired additive row. -/
noncomputable def ehmDyadicVaalerPairedHighProductRow
    (h : ℤ) (X D J Y m : ℕ) : ℂ :=
  ∑ n ∈ ehmDyadicVaalerHighProductRange J Y,
    ehmDyadicVaalerPairedProductSummand h X D m n

/-- Exact finite split of one paired additive row at `Y`. -/
theorem ehmDyadicVaalerPairedAdditiveRow_eq_low_add_high
    (h : ℤ) (X D J Y m : ℕ) :
    ehmDyadicVaalerPairedAdditiveRow h X D J m =
      ehmDyadicVaalerPairedLowProductRow h X D J Y m +
        ehmDyadicVaalerPairedHighProductRow h X D J Y m := by
  classical
  unfold ehmDyadicVaalerPairedAdditiveRow
    ehmDyadicVaalerPairedLowProductRow
    ehmDyadicVaalerPairedHighProductRow
    ehmDyadicVaalerPairedProductSummand
  rw [← Finset.sum_union (low_disjoint_high J Y),
    low_union_high_eq_full]

/-! ## Lift to signed Möbius sums -/

/-- Low-product paired rows on an arbitrary `m`-range. -/
noncomputable def ehmDyadicVaalerPairedLowProductRowsMRange
    (h : ℤ) (X D J Y mLo mHi : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc mLo mHi,
    ((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
      ehmDyadicVaalerPairedLowProductRow h X D J Y m)

/-- High-product paired rows on an arbitrary `m`-range. -/
noncomputable def ehmDyadicVaalerPairedHighProductRowsMRange
    (h : ℤ) (X D J Y mLo mHi : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc mLo mHi,
    ((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
      ehmDyadicVaalerPairedHighProductRow h X D J Y m)

/-- The product truncation commutes exactly with the signed outer Möbius
sum on every `m`-range. -/
theorem ehmDyadicVaalerPairedAdditiveRowsMRange_eq_low_add_high
    (h : ℤ) (X D J Y mLo mHi : ℕ) :
    ehmDyadicVaalerPairedAdditiveRowsMRange h X D J mLo mHi =
      ehmDyadicVaalerPairedLowProductRowsMRange
          h X D J Y mLo mHi +
        ehmDyadicVaalerPairedHighProductRowsMRange
          h X D J Y mLo mHi := by
  classical
  unfold ehmDyadicVaalerPairedAdditiveRowsMRange
    ehmDyadicVaalerPairedLowProductRowsMRange
    ehmDyadicVaalerPairedHighProductRowsMRange
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [← mul_add,
    ← ehmDyadicVaalerPairedAdditiveRow_eq_low_add_high h X D J Y m]

/-! ## Complete normalized-kernel truncation -/

/-- Exact low/high product decomposition of the complete normalized kernel
phase.  No estimate is made for either component. -/
theorem ehmDyadicVaalerNormalizedKernelPhaseForm_eq_low_add_high
    (h : ℤ) (X D J U Y : ℕ) (hX : 1 ≤ X) (hU : U ≤ 2 * X) :
    ehmDyadicVaalerNormalizedKernelPhaseForm h X D J U =
      ehmDyadicVaalerPairedLowProductRowsMRange
          h X D J Y 1 (2 * X) +
        ehmDyadicVaalerPairedHighProductRowsMRange
          h X D J Y 1 (2 * X) := by
  rw [ehmDyadicVaalerNormalizedKernelPhaseForm_eq_pairedAdditiveRows
      h X D J U hX hU,
    ehmDyadicVaalerPairedAdditiveRowsMRange_eq_low_add_high]

end RH.Criteria.NymanBeurling.BCFLogTaperEhmProductTruncation
