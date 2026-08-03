/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15BettinChandeeAudit

/-!
# NB12y: correction-preserving Estermann-frequency split

This file splits the absolutely convergent Estermann series on
`Re(s)=3/2` at an arbitrary natural cutoff.  The split is first proved for
one rational row, then lifted through the complete finite signed H15 row
family.

The residue ledger is not divided between the two frequency sectors.  In the
corrected finite right edge it is attached in full to the low-frequency
piece, leaving the high-frequency piece free of correction terms.  This is
the exact algebraic interface required before a Bettin--Chandee estimate can
be applied to the high sector.

No decay estimate is asserted here.
-/

open scoped BigOperators Topology LSeries.notation Interval
open Complex Filter MeasureTheory LSeries

namespace NBMellinTools.NB12

/-! ## One-series low/high split -/

/-- The first `K+1` terms of an Estermann Dirichlet series.  The zero term is
harmless because `LSeries.term` vanishes there. -/
noncomputable def bblsEstermannLowFrequency
    (phase : ℝ) (s : ℂ) (K : ℕ) : ℂ :=
  ∑ r ∈ Finset.range (K + 1),
    LSeries.term (bblsEstermannCoeff phase) s r

/-- The genuine complementary Estermann tail, reindexed from zero. -/
noncomputable def bblsEstermannHighFrequency
    (phase : ℝ) (s : ℂ) (K : ℕ) : ℂ :=
  ∑' j : ℕ,
    LSeries.term (bblsEstermannCoeff phase) s (j + (K + 1))

/-- Exact low/high split on the initial half-plane of absolute convergence. -/
theorem bblsEstermannDirichletSeries_eq_low_add_high
    (phase : ℝ) {s : ℂ} (hs : 1 < s.re) (K : ℕ) :
    bblsEstermannDirichletSeries phase s =
      bblsEstermannLowFrequency phase s K +
        bblsEstermannHighFrequency phase s K := by
  have hsum : Summable (fun r : ℕ =>
      LSeries.term (bblsEstermannCoeff phase) s r) :=
    bblsEstermannCoeff_summable phase hs
  unfold bblsEstermannDirichletSeries LSeries
    bblsEstermannLowFrequency bblsEstermannHighFrequency
  exact (Summable.sum_add_tsum_nat_add (K + 1) hsum).symm

/-- Low-frequency part of the rational Hurwitz continuation on the
three-halves line. -/
noncomputable def bblsEstermannHurwitzLowFrequency
    (a q : ℕ) [NeZero q] (t : ℝ) (K : ℕ) : ℂ :=
  bblsEstermannLowFrequency ((a : ℝ) / (q : ℝ))
    (bblsEstermannThreeHalfPoint t) K

/-- Complementary high-frequency part of the same rational row. -/
noncomputable def bblsEstermannHurwitzHighFrequency
    (a q : ℕ) [NeZero q] (t : ℝ) (K : ℕ) : ℂ :=
  bblsEstermannHighFrequency ((a : ℝ) / (q : ℝ))
    (bblsEstermannThreeHalfPoint t) K

/-- The analytically continued rational Estermann value equals its genuine
low-frequency block plus its complementary tail on `Re(s)=3/2`. -/
theorem bblsEstermannHurwitzContinuation_threeHalf_eq_low_add_high
    (a q : ℕ) [NeZero q] (t : ℝ) (K : ℕ) :
    bblsEstermannHurwitzContinuation a q
        (bblsEstermannThreeHalfPoint t) =
      bblsEstermannHurwitzLowFrequency a q t K +
        bblsEstermannHurwitzHighFrequency a q t K := by
  have hs : 1 < (bblsEstermannThreeHalfPoint t).re := by
    norm_num [bblsEstermannThreeHalfPoint]
  rw [bblsEstermannHurwitzContinuation_eq_dirichletSeries a q hs]
  exact bblsEstermannDirichletSeries_eq_low_add_high _ hs K

/-! ## Functional-equation row split -/

/-- Low-frequency part of one active reflected row after the exact
functional equation. -/
noncomputable def bblsActiveThreeHalfLowFrequency
    (damping : ℝ) (a q : ℕ) [NeZero q]
    (haq : Nat.Coprime a q) (t : ℝ) (K : ℕ) : ℂ :=
  let s := bblsEstermannThreeHalfPoint t
  Complex.Gamma (-s) * (damping : ℂ) ^ s *
    (bblsEstermannClassicalFactor q s *
        bblsEstermannHurwitzLowFrequency
          (bblsEstermannInverseNumerator a q haq) q t K +
      (bblsEstermannClassicalFactor q s *
          Complex.cos ((Real.pi : ℂ) * s)) *
        bblsEstermannHurwitzLowFrequency
          (bblsEstermannNegativeInverseNumerator a q haq) q t K)

/-- High-frequency part of one active reflected row after the same functional
equation. -/
noncomputable def bblsActiveThreeHalfHighFrequency
    (damping : ℝ) (a q : ℕ) [NeZero q]
    (haq : Nat.Coprime a q) (t : ℝ) (K : ℕ) : ℂ :=
  let s := bblsEstermannThreeHalfPoint t
  Complex.Gamma (-s) * (damping : ℂ) ^ s *
    (bblsEstermannClassicalFactor q s *
        bblsEstermannHurwitzHighFrequency
          (bblsEstermannInverseNumerator a q haq) q t K +
      (bblsEstermannClassicalFactor q s *
          Complex.cos ((Real.pi : ℂ) * s)) *
        bblsEstermannHurwitzHighFrequency
          (bblsEstermannNegativeInverseNumerator a q haq) q t K)

/-- Exact rowwise low/high decomposition after the functional equation. -/
theorem bblsActiveReflectedExpression_threeHalf_eq_low_add_high
    {damping : ℝ} (a q : ℕ) [NeZero q]
    (haq : Nat.Coprime a q) (t : ℝ) (K : ℕ) :
    bblsActiveReflectedExpression damping a q
        (bblsEstermannThreeHalfPoint t) =
      bblsActiveThreeHalfLowFrequency damping a q haq t K +
        bblsActiveThreeHalfHighFrequency damping a q haq t K := by
  rw [bblsActiveReflectedExpression_threeHalf_eq_dual a q haq t]
  rw [bblsEstermannHurwitzContinuation_threeHalf_eq_low_add_high
        (bblsEstermannInverseNumerator a q haq) q t K,
      bblsEstermannHurwitzContinuation_threeHalf_eq_low_add_high
        (bblsEstermannNegativeInverseNumerator a q haq) q t K]
  unfold bblsActiveThreeHalfLowFrequency
    bblsActiveThreeHalfHighFrequency
  ring

/-- One frequency of the functional-equation row.  Keeping the two
orientations inside the same term is essential for the later signed
trilinear estimate. -/
noncomputable def bblsActiveThreeHalfFrequencyTerm
    (damping : ℝ) (a q : ℕ) [NeZero q]
    (haq : Nat.Coprime a q) (r : ℕ) (t : ℝ) : ℂ :=
  let s := bblsEstermannThreeHalfPoint t
  Complex.Gamma (-s) * (damping : ℂ) ^ s *
    (bblsEstermannClassicalFactor q s *
        LSeries.term
          (bblsEstermannCoeff
            ((bblsEstermannInverseNumerator a q haq : ℝ) / (q : ℝ))) s r +
      (bblsEstermannClassicalFactor q s *
          Complex.cos ((Real.pi : ℂ) * s)) *
        LSeries.term
          (bblsEstermannCoeff
            ((bblsEstermannNegativeInverseNumerator a q haq : ℝ) / (q : ℝ))) s r)

/-- The high-frequency functional-equation row is the genuine sum of its
paired frequency terms. -/
theorem bblsActiveThreeHalfHighFrequency_eq_tsum
    {damping : ℝ} (a q : ℕ) [NeZero q]
    (haq : Nat.Coprime a q) (t : ℝ) (K : ℕ) :
    bblsActiveThreeHalfHighFrequency damping a q haq t K =
      ∑' j : ℕ, bblsActiveThreeHalfFrequencyTerm damping a q haq
        (j + (K + 1)) t := by
  let s := bblsEstermannThreeHalfPoint t
  let p : ℝ :=
    (bblsEstermannInverseNumerator a q haq : ℝ) / (q : ℝ)
  let m : ℝ :=
    (bblsEstermannNegativeInverseNumerator a q haq : ℝ) / (q : ℝ)
  have hs : 1 < s.re := by
    norm_num [s, bblsEstermannThreeHalfPoint]
  have hp : Summable (fun j : ℕ =>
      LSeries.term (bblsEstermannCoeff p) s (j + (K + 1))) :=
    (bblsEstermannCoeff_summable p hs).comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
  have hm : Summable (fun j : ℕ =>
      LSeries.term (bblsEstermannCoeff m) s (j + (K + 1))) :=
    (bblsEstermannCoeff_summable m hs).comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
  unfold bblsActiveThreeHalfHighFrequency
    bblsEstermannHurwitzHighFrequency bblsEstermannHighFrequency
    bblsActiveThreeHalfFrequencyTerm
  change
    Complex.Gamma (-s) * (damping : ℂ) ^ s *
        (bblsEstermannClassicalFactor q s *
            (∑' j : ℕ, LSeries.term (bblsEstermannCoeff p) s
              (j + (K + 1))) +
          (bblsEstermannClassicalFactor q s *
              Complex.cos ((Real.pi : ℂ) * s)) *
            (∑' j : ℕ, LSeries.term (bblsEstermannCoeff m) s
              (j + (K + 1)))) = _
  rw [← tsum_mul_left, ← tsum_mul_left,
    ← (hp.mul_left _).tsum_add (hm.mul_left _), ← tsum_mul_left]

/-! ## Complete signed H15 aggregate -/

/-- The complete finite signed H15 low-frequency aggregate. -/
noncomputable def h15ThreeHalfLowFrequencyAggregate
    (n K : ℕ) (t : ℝ) : ℂ :=
  ∑ i : H15LaurentRowIndex (NB8.logTaperLength n),
    h15LaurentRowWeight i *
      bblsActiveThreeHalfLowFrequency (h15ContourDamping n)
        (h15LaurentRow i).numerator (h15LaurentRow i).denominator
        (h15LaurentRow i).coprime t K

/-- The complete finite signed H15 complementary high-frequency aggregate. -/
noncomputable def h15ThreeHalfHighFrequencyAggregate
    (n K : ℕ) (t : ℝ) : ℂ :=
  ∑ i : H15LaurentRowIndex (NB8.logTaperLength n),
    h15LaurentRowWeight i *
      bblsActiveThreeHalfHighFrequency (h15ContourDamping n)
        (h15LaurentRow i).numerator (h15LaurentRow i).denominator
        (h15LaurentRow i).coprime t K

/-- Exact low/high split after summing all signed H15 rows. -/
theorem h15VerticalAggregate_threeHalf_eq_low_add_high
    (n K : ℕ) (t : ℝ) :
    h15VerticalAggregate n (3 / 2) t =
      h15ThreeHalfLowFrequencyAggregate n K t +
        h15ThreeHalfHighFrequencyAggregate n K t := by
  unfold h15VerticalAggregate h15ActiveContourAggregate
    bblsFiniteActiveAggregate h15ThreeHalfLowFrequencyAggregate
    h15ThreeHalfHighFrequencyAggregate
  have hpoint : ((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I =
      bblsEstermannThreeHalfPoint t := by
    norm_num [bblsEstermannThreeHalfPoint]
    ring
  rw [hpoint, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [bblsActiveReflectedExpression_threeHalf_eq_low_add_high
    (h15LaurentRow i).numerator (h15LaurentRow i).denominator
    (h15LaurentRow i).coprime t K]
  ring

/-- Canonical integer cutoff corresponding to the strict
`R = N^(3/4+eta)` Bettin--Chandee exponent margin. -/
noncomputable def h15BettinChandeeFrequencyCutoff
    (eta : ℝ) (n : ℕ) : ℕ :=
  Nat.ceil
    ((NB8.logTaperLength n : ℝ) ^ ((3 / 4 : ℝ) + eta))

/-- The pointwise split at the canonical Bettin--Chandee cutoff.  The theorem
is exact for every `eta`; the analytic high-frequency estimate will require
`0 < eta`. -/
theorem h15VerticalAggregate_threeHalf_eq_bettinChandeeLow_add_high
    (eta : ℝ) (n : ℕ) (t : ℝ) :
    h15VerticalAggregate n (3 / 2) t =
      h15ThreeHalfLowFrequencyAggregate n
          (h15BettinChandeeFrequencyCutoff eta n) t +
        h15ThreeHalfHighFrequencyAggregate n
          (h15BettinChandeeFrequencyCutoff eta n) t :=
  h15VerticalAggregate_threeHalf_eq_low_add_high
    n (h15BettinChandeeFrequencyCutoff eta n) t

/-! ## The correction remains entirely on the low side -/

/-- Truncated low-frequency vertical integral. -/
noncomputable def h15ThreeHalfLowFrequencyIntegral
    (n K : ℕ) (T : ℝ) : ℂ :=
  ∫ t : ℝ in -T..T, h15ThreeHalfLowFrequencyAggregate n K t

/-- The exact algebraic high-frequency complement of the truncated vertical
integral.  Identifying it with the integral of the high-frequency series is
the next sum--integral exchange theorem. -/
noncomputable def h15ThreeHalfHighFrequencyIntegralRemainder
    (n K : ℕ) (T : ℝ) : ℂ :=
  h15TruncatedVerticalIntegral n (3 / 2) T -
    h15ThreeHalfLowFrequencyIntegral n K T

/-- The low-frequency right-edge contribution with the **complete** residue
ledger attached. -/
noncomputable def h15CorrectionCoupledLowFrequencyRightEdge
    (n K : ℕ) (T : ℝ) : ℂ :=
  I * h15ThreeHalfLowFrequencyIntegral n K T -
    2 * Real.pi * I * h15ContourResidueLedger n

/-- The high-frequency right-edge contribution contains no correction term. -/
noncomputable def h15HighFrequencyRightEdgeRemainder
    (n K : ℕ) (T : ℝ) : ℂ :=
  I * h15ThreeHalfHighFrequencyIntegralRemainder n K T

/-- Lossless correction-preserving split of the finite right edge.  In
particular, no fraction of the residue ledger is assigned to the high
frequency sector. -/
theorem h15CorrectedThreeHalfRightEdge_eq_low_add_high
    (n K : ℕ) (T : ℝ) :
    h15CorrectedThreeHalfRightEdge n T =
      h15CorrectionCoupledLowFrequencyRightEdge n K T +
        h15HighFrequencyRightEdgeRemainder n K T := by
  unfold h15CorrectedThreeHalfRightEdge
    h15CorrectionCoupledLowFrequencyRightEdge
    h15HighFrequencyRightEdgeRemainder
    h15ThreeHalfHighFrequencyIntegralRemainder
  ring

/-- Correction-preserving right-edge split at the canonical
`N^(3/4+eta)` frequency threshold. -/
theorem h15CorrectedThreeHalfRightEdge_eq_bettinChandeeLow_add_high
    (eta : ℝ) (n : ℕ) (T : ℝ) :
    h15CorrectedThreeHalfRightEdge n T =
      h15CorrectionCoupledLowFrequencyRightEdge n
          (h15BettinChandeeFrequencyCutoff eta n) T +
        h15HighFrequencyRightEdgeRemainder n
          (h15BettinChandeeFrequencyCutoff eta n) T :=
  h15CorrectedThreeHalfRightEdge_eq_low_add_high
    n (h15BettinChandeeFrequencyCutoff eta n) T

end NBMellinTools.NB12
