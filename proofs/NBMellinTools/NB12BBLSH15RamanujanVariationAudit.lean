/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15RamanujanCompletionDefect

/-!
# NB12zf: quantitative variation audit for H15 Ramanujan completion

The exact completion identity leaves a within-period variation defect and an
endpoint defect.  This file proves the strongest elementary absolute bounds
available from the existing H15 coefficient ledger.

The endpoint contribution gains `q/U²`.  The total within-period variation is
at most `2/U`.  After summing a modulus block `q ~ Q`, the resulting budget is

`2Q/U + 4Q²/U²`.

On the balanced block `Q=U` this is the constant `6`, so the absolute
completion argument gives no decay.  This is a method stop test, not a lower
bound for the genuine signed correlation.  Any improvement must use the
arithmetic factor `mu(g*u)^2` inside the additive character sum, or preserve
signed cancellation across moduli and corrections.
-/

open scoped BigOperators Topology LSeries.notation
open Complex

namespace NBMellinTools.NB12

/-! ## Pointwise H15 square-weight bounds -/

/-- The supported H15 inverse square weight is nonnegative. -/
theorem h15SupportedInverseSquareWeight_nonneg
    (N g u : ℕ) :
    0 ≤ h15SupportedInverseSquareWeight N g u := by
  unfold h15SupportedInverseSquareWeight
  split_ifs <;> positivity

/-- The inverse-square bound only needs membership in the natural dyadic
block; no coprimality hypothesis is required. -/
theorem h15SupportedInverseSquareWeight_le_of_mem_natBlock
    {N g U u : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g) (hU : 0 < U)
    (hu : u ∈ h15BettinChandeeNatBlock U) :
    h15SupportedInverseSquareWeight N g u ≤
      (1 / (U : ℝ)) ^ 2 := by
  unfold h15SupportedInverseSquareWeight
  split_ifs with hsupport
  · have huSupported :
        u ∈ h15BettinChandeeSupportedNatBlock N g U := by
      exact Finset.mem_filter.mpr ⟨hu, hsupport⟩
    rw [← sq_abs]
    exact pow_le_pow_left₀
      (abs_nonneg (h15BettinChandeeInverseCoefficient N g u))
      (abs_h15BettinChandeeInverseCoefficient_le
        hN hg hU huSupported) 2
  · positivity

/-! ## Exact squarefree/envelope separation -/

/-- Real indicator of squarefreeness.  Squaring the Möbius coefficient turns
it into exactly this arithmetic factor. -/
noncomputable def h15SquarefreeIndicator (n : ℕ) : ℝ :=
  if Squarefree n then 1 else 0

/-- The nonnegative smooth part of the supported inverse square weight. -/
noncomputable def h15SupportedInverseSmoothEnvelope
    (N g u : ℕ) : ℝ :=
  if g * u ≤ N then
    (Real.log ((N : ℝ) / ((g * u : ℕ) : ℝ)) /
        Real.log (N : ℝ)) ^ 2 / (u : ℝ) ^ 2
  else 0

/-- Exact factorization of the squared H15 coefficient into a squarefree
indicator and a smooth logarithmic envelope. -/
theorem h15SupportedInverseSquareWeight_eq_indicator_mul_envelope
    (N g u : ℕ) :
    h15SupportedInverseSquareWeight N g u =
      h15SquarefreeIndicator (g * u) *
        h15SupportedInverseSmoothEnvelope N g u := by
  have hmuZ := ArithmeticFunction.moebius_sq (n := g * u)
  have hmuR :
      (((ArithmeticFunction.moebius (g * u) : ℤ) : ℝ) ^ 2) =
        if Squarefree (g * u) then 1 else 0 := by
    exact_mod_cast hmuZ
  unfold h15SupportedInverseSquareWeight
    h15BettinChandeeInverseCoefficient h15NaturalLogTaperCoeff
    h15SquarefreeIndicator h15SupportedInverseSmoothEnvelope
  split_ifs with hsupport hsquarefree
  · rw [if_pos hsquarefree] at hmuR
    rw [← hmuR]
    ring
  · rw [if_neg hsquarefree] at hmuR
    rw [← hmuR]
    ring
  · ring
  · ring

/-- Smooth-envelope contribution to the centered cross mode on one complete
period. -/
noncomputable def h15PeriodSmoothEnvelopeDefect
    (N g r k q : ℕ) : ℝ :=
  ∑ u ∈ h15ReducedNaturalPeriod k q,
    h15SquarefreeIndicator (g * u) *
      (h15SupportedInverseSmoothEnvelope N g u -
        h15SupportedInverseSmoothEnvelope N g (k * q)) *
      h15PairedDirectCrossMode r u q

/-- Arithmetic fluctuation left after freezing the smooth envelope at the
period endpoint. -/
noncomputable def h15PeriodSquarefreeFluctuationDefect
    (N g r k q : ℕ) : ℝ :=
  ∑ u ∈ h15ReducedNaturalPeriod k q,
    (h15SquarefreeIndicator (g * u) -
      h15SquarefreeIndicator (g * (k * q))) *
      h15SupportedInverseSmoothEnvelope N g (k * q) *
      h15PairedDirectCrossMode r u q

/-- Exact decomposition of periodwise H15 weight variation into genuinely
smooth envelope variation and squarefree additive-character fluctuation. -/
theorem h15PeriodVariationDefect_eq_smooth_add_squarefree
    (N g r k q : ℕ) :
    h15PeriodVariationDefect r k q
        (h15SupportedInverseSquareWeight N g)
        (h15SupportedPeriodReferenceWeight N g q k) =
      h15PeriodSmoothEnvelopeDefect N g r k q +
        h15PeriodSquarefreeFluctuationDefect N g r k q := by
  unfold h15PeriodVariationDefect h15SupportedPeriodReferenceWeight
    h15PeriodSmoothEnvelopeDefect h15PeriodSquarefreeFluctuationDefect
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  rw [h15SupportedInverseSquareWeight_eq_indicator_mul_envelope,
    h15SupportedInverseSquareWeight_eq_indicator_mul_envelope]
  ring

/-- Complete dyadic sum of the smooth-envelope defects. -/
noncomputable def h15DyadicSmoothEnvelopeDefect
    (N g r U q : ℕ) : ℝ :=
  ∑ k ∈ h15CompletePeriodIndices U q,
    h15PeriodSmoothEnvelopeDefect N g r k q

/-- Complete dyadic sum of the squarefree fluctuation defects. -/
noncomputable def h15DyadicSquarefreeFluctuationDefect
    (N g r U q : ℕ) : ℝ :=
  ∑ k ∈ h15CompletePeriodIndices U q,
    h15PeriodSquarefreeFluctuationDefect N g r k q

/-- Global exact separation of the within-period completion defect. -/
theorem h15DyadicPeriodVariationDefect_eq_smooth_add_squarefree
    (N g r U q : ℕ) :
    h15DyadicPeriodVariationDefect r U q
        (h15SupportedInverseSquareWeight N g)
        (h15SupportedPeriodReferenceWeight N g q) =
      h15DyadicSmoothEnvelopeDefect N g r U q +
        h15DyadicSquarefreeFluctuationDefect N g r U q := by
  unfold h15DyadicPeriodVariationDefect
    h15DyadicSmoothEnvelopeDefect h15DyadicSquarefreeFluctuationDefect
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  exact h15PeriodVariationDefect_eq_smooth_add_squarefree N g r k q

/-- Every point of a complete reduced period belongs to the ambient dyadic
numerator block. -/
theorem h15ReducedNaturalPeriod_subset_natBlock
    {U q k : ℕ} (hk : k ∈ h15CompletePeriodIndices U q) :
    h15ReducedNaturalPeriod k q ⊆ h15BettinChandeeNatBlock U := by
  intro u hu
  have hkBounds := (Finset.mem_filter.mp hk).2
  have huRange := Finset.mem_Ico.mp (Finset.mem_filter.mp hu).1
  exact Finset.mem_Ico.mpr
    ⟨hkBounds.1.trans huRange.1, huRange.2.trans_le hkBounds.2⟩

/-- The canonical left-endpoint reference weight has the same inverse-square
bound as every point of its complete period. -/
theorem h15SupportedPeriodReferenceWeight_le
    {N g U q k : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g)
    (hU : 0 < U) (hq : 0 < q)
    (hk : k ∈ h15CompletePeriodIndices U q) :
    h15SupportedPeriodReferenceWeight N g q k ≤
      (1 / (U : ℝ)) ^ 2 := by
  apply h15SupportedInverseSquareWeight_le_of_mem_natBlock hN hg hU
  have hkBounds := (Finset.mem_filter.mp hk).2
  apply Finset.mem_Ico.mpr
  refine ⟨hkBounds.1, ?_⟩
  have hstep : k * q < (k + 1) * q :=
    Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self k) hq
  exact hstep.trans_le hkBounds.2

/-! ## Periodwise and total variation -/

/-- Absolute variation on one complete period is bounded by twice its
cardinality times the dyadic inverse-square scale. -/
theorem abs_h15PeriodVariationDefect_supported_le
    {N g r U q k : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g)
    (hU : 0 < U) (hq : 0 < q)
    (hk : k ∈ h15CompletePeriodIndices U q) :
    |h15PeriodVariationDefect r k q
        (h15SupportedInverseSquareWeight N g)
        (h15SupportedPeriodReferenceWeight N g q k)| ≤
      ((h15ReducedNaturalPeriod k q).card : ℝ) *
        (2 * (1 / (U : ℝ)) ^ 2) := by
  unfold h15PeriodVariationDefect
  calc
    |∑ u ∈ h15ReducedNaturalPeriod k q,
        (h15SupportedInverseSquareWeight N g u -
            h15SupportedPeriodReferenceWeight N g q k) *
          h15PairedDirectCrossMode r u q| ≤
      ∑ u ∈ h15ReducedNaturalPeriod k q,
        |(h15SupportedInverseSquareWeight N g u -
            h15SupportedPeriodReferenceWeight N g q k) *
          h15PairedDirectCrossMode r u q| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _u ∈ h15ReducedNaturalPeriod k q,
        2 * (1 / (U : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro u hu
      rw [abs_mul]
      have huBlock : u ∈ h15BettinChandeeNatBlock U :=
        h15ReducedNaturalPeriod_subset_natBlock hk hu
      have hwu := h15SupportedInverseSquareWeight_le_of_mem_natBlock
        hN hg hU huBlock
      have hwk := h15SupportedPeriodReferenceWeight_le
        hN hg hU hq hk
      have hwuNonneg := h15SupportedInverseSquareWeight_nonneg N g u
      have hwkNonneg :
          0 ≤ h15SupportedPeriodReferenceWeight N g q k := by
        unfold h15SupportedPeriodReferenceWeight
        exact h15SupportedInverseSquareWeight_nonneg N g (k * q)
      calc
        |h15SupportedInverseSquareWeight N g u -
              h15SupportedPeriodReferenceWeight N g q k| *
            |h15PairedDirectCrossMode r u q| ≤
          |h15SupportedInverseSquareWeight N g u -
              h15SupportedPeriodReferenceWeight N g q k| * 1 :=
            mul_le_mul_of_nonneg_left
              (abs_h15PairedDirectCrossMode_le_one r u q hq)
              (abs_nonneg _)
        _ ≤ h15SupportedInverseSquareWeight N g u +
              h15SupportedPeriodReferenceWeight N g q k := by
            simpa [abs_of_nonneg hwuNonneg, abs_of_nonneg hwkNonneg] using
              (abs_sub
                (h15SupportedInverseSquareWeight N g u)
                (h15SupportedPeriodReferenceWeight N g q k))
        _ ≤ 2 * (1 / (U : ℝ)) ^ 2 := by linarith
    _ = ((h15ReducedNaturalPeriod k q).card : ℝ) *
        (2 * (1 / (U : ℝ)) ^ 2) := by
      simp [Finset.sum_const, nsmul_eq_mul]

/-- The complete-period support has at most the cardinality of the ambient
dyadic block. -/
theorem card_h15CompletePeriodSupport_le
    (U q : ℕ) :
    (h15CompletePeriodSupport U q).card ≤ U := by
  calc
    (h15CompletePeriodSupport U q).card ≤
        (h15ReducedDyadicNumeratorBlock U q).card :=
      Finset.card_le_card
        (h15CompletePeriodSupport_subset_reducedDyadic U q)
    _ ≤ (h15BettinChandeeNatBlock U).card := by
      unfold h15ReducedDyadicNumeratorBlock
      exact Finset.card_filter_le _ _
    _ = U := by
      simp only [h15BettinChandeeNatBlock, Nat.card_Ico]
      omega

/-- The sum of the reduced-period cardinalities equals the cardinality of
their disjoint complete support. -/
theorem sum_card_h15ReducedNaturalPeriod
    (U q : ℕ) :
    (∑ k ∈ h15CompletePeriodIndices U q,
        ((h15ReducedNaturalPeriod k q).card : ℝ)) =
      ((h15CompletePeriodSupport U q).card : ℝ) := by
  have hsum := sum_h15CompletePeriodSupport U q (fun _ => (1 : ℝ))
  simpa [Finset.sum_const, nsmul_eq_mul] using hsum.symm

/-- Elementary total absolute variation bound.  It is independent of the
modulus and therefore loses the possible complete-period gain after summing
over a balanced modulus block. -/
theorem abs_h15DyadicPeriodVariationDefect_supported_le
    {N g r U q : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g)
    (hU : 0 < U) (hq : 0 < q) :
    |h15DyadicPeriodVariationDefect r U q
        (h15SupportedInverseSquareWeight N g)
        (h15SupportedPeriodReferenceWeight N g q)| ≤
      2 / (U : ℝ) := by
  unfold h15DyadicPeriodVariationDefect
  calc
    |∑ k ∈ h15CompletePeriodIndices U q,
        h15PeriodVariationDefect r k q
          (h15SupportedInverseSquareWeight N g)
          (h15SupportedPeriodReferenceWeight N g q k)| ≤
      ∑ k ∈ h15CompletePeriodIndices U q,
        |h15PeriodVariationDefect r k q
          (h15SupportedInverseSquareWeight N g)
          (h15SupportedPeriodReferenceWeight N g q k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ h15CompletePeriodIndices U q,
        ((h15ReducedNaturalPeriod k q).card : ℝ) *
          (2 * (1 / (U : ℝ)) ^ 2) := by
      apply Finset.sum_le_sum
      intro k hk
      exact abs_h15PeriodVariationDefect_supported_le
        hN hg hU hq hk
    _ = ((h15CompletePeriodSupport U q).card : ℝ) *
        (2 * (1 / (U : ℝ)) ^ 2) := by
      rw [← sum_card_h15ReducedNaturalPeriod U q,
        Finset.sum_mul]
    _ ≤ (U : ℝ) * (2 * (1 / (U : ℝ)) ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_h15CompletePeriodSupport_le U q
    _ = 2 / (U : ℝ) := by
      have hU0 : (U : ℝ) ≠ 0 := by positivity
      field_simp

/-! ## Completion budget and balanced stop test -/

/-- The exact completion identity together with the elementary variation and
endpoint estimates. -/
theorem abs_h15PairedDirectCrossCorrelation_supported_le_completion
    {N g r U q : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g)
    (hU : 0 < U) (hq : 0 < q) :
    |h15PairedDirectCrossCorrelation r U q
        (h15SupportedInverseCoefficient N g)| ≤
      2 / (U : ℝ) +
        (2 * q : ℝ) * (1 / (U : ℝ)) ^ 2 := by
  rw [h15PairedDirectCrossCorrelation_supported_eq_completionDefects
    N g r U q hq]
  calc
    |h15DyadicPeriodVariationDefect r U q
          (h15SupportedInverseSquareWeight N g)
          (h15SupportedPeriodReferenceWeight N g q) +
        h15DyadicBoundaryDefect r U q
          (h15SupportedInverseSquareWeight N g)| ≤
      |h15DyadicPeriodVariationDefect r U q
          (h15SupportedInverseSquareWeight N g)
          (h15SupportedPeriodReferenceWeight N g q)| +
        |h15DyadicBoundaryDefect r U q
          (h15SupportedInverseSquareWeight N g)| := abs_add_le _ _
    _ ≤ 2 / (U : ℝ) +
        (2 * q : ℝ) * (1 / (U : ℝ)) ^ 2 :=
      add_le_add
        (abs_h15DyadicPeriodVariationDefect_supported_le
          hN hg hU hq)
        (abs_h15DyadicBoundaryDefect_supported_le hN hg hU hq)

/-- Absolute completion budget over one supported dyadic modulus block. -/
noncomputable def h15RamanujanAbsoluteCompletionBudget
    (N g r U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    |h15PairedDirectCrossCorrelation r U q
      (h15SupportedInverseCoefficient N g)|

/-- Summing the elementary completion estimate over `q ~ Q` gives
`2Q/U + 4Q²/U²`. -/
theorem h15RamanujanAbsoluteCompletionBudget_le
    {N g r U Q : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g)
    (hU : 0 < U) (hQ : 0 < Q) :
    h15RamanujanAbsoluteCompletionBudget N g r U Q ≤
      (2 * (Q : ℝ)) / (U : ℝ) +
        4 * (Q : ℝ) ^ 2 * (1 / (U : ℝ)) ^ 2 := by
  unfold h15RamanujanAbsoluteCompletionBudget
  calc
    (∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        |h15PairedDirectCrossCorrelation r U q
          (h15SupportedInverseCoefficient N g)|) ≤
      ∑ _q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        (2 / (U : ℝ) +
          4 * (Q : ℝ) * (1 / (U : ℝ)) ^ 2) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqMem := mem_h15BettinChandeeSupportedNatBlock.mp hq
      have hqPos : 0 < q := hQ.trans_le hqMem.1
      have hbase :=
        abs_h15PairedDirectCrossCorrelation_supported_le_completion
          (r := r) hN hg hU hqPos
      calc
        |h15PairedDirectCrossCorrelation r U q
            (h15SupportedInverseCoefficient N g)| ≤
          2 / (U : ℝ) +
            (2 * q : ℝ) * (1 / (U : ℝ)) ^ 2 := hbase
        _ ≤ 2 / (U : ℝ) +
            4 * (Q : ℝ) * (1 / (U : ℝ)) ^ 2 := by
          have hqLe : (q : ℝ) ≤ 2 * (Q : ℝ) := by
            exact_mod_cast hqMem.2.1.le
          apply add_le_add_right _ _
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          nlinarith
    _ = ((h15BettinChandeeSupportedNatBlock N g Q).card : ℝ) *
        (2 / (U : ℝ) +
          4 * (Q : ℝ) * (1 / (U : ℝ)) ^ 2) := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ (Q : ℝ) *
        (2 / (U : ℝ) +
          4 * (Q : ℝ) * (1 / (U : ℝ)) ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_h15BettinChandeeSupportedNatBlock_le N g Q
    _ = (2 * (Q : ℝ)) / (U : ℝ) +
        4 * (Q : ℝ) ^ 2 * (1 / (U : ℝ)) ^ 2 := by ring

/-- On the balanced modulus/numerator block the elementary absolute budget
is the constant six.  Thus this estimate cannot imply decay as the scale
tends to infinity. -/
theorem h15RamanujanAbsoluteCompletionBudget_balanced_le
    {N g r U : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g) (hU : 0 < U) :
    h15RamanujanAbsoluteCompletionBudget N g r U U ≤ 6 := by
  calc
    h15RamanujanAbsoluteCompletionBudget N g r U U ≤
        (2 * (U : ℝ)) / (U : ℝ) +
          4 * (U : ℝ) ^ 2 * (1 / (U : ℝ)) ^ 2 :=
      h15RamanujanAbsoluteCompletionBudget_le hN hg hU hU
    _ = 6 := by
      have hU0 : (U : ℝ) ≠ 0 := by positivity
      field_simp
      norm_num

/-- The power exponent of the balanced absolute completion budget. -/
noncomputable def h15RamanujanAbsoluteCompletionBalancedExponent : ℝ := 0

theorem h15RamanujanAbsoluteCompletionBalancedExponent_not_neg :
    ¬ h15RamanujanAbsoluteCompletionBalancedExponent < 0 := by
  norm_num [h15RamanujanAbsoluteCompletionBalancedExponent]

end NBMellinTools.NB12
