/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FinalBoundaryFourSector

/-!
# NB12zz: sectorwise absolute-value stop test

The existing endpoint estimates are propagated separately through the
terminal-terminal, terminal-smooth, and smooth-smooth correlations.  On a
balanced block `Q ≤ U`, each sector receives only an `O(tau(g)^2 Q^2)`
absolute majorant.  Thus this particular sectorwise triangle-inequality route
does not decay.  No impossibility theorem for stronger signed estimates is
claimed.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate
open Complex

namespace NBMellinTools.NB12

/-! ## Row and modulus budgets -/

theorem abs_h15NormalizedProgressionTerminalRowBoundaryLift_le
    {N g r U L q d : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g)
    (hU : 0 < U) (hL : 0 < L) (hq : 0 < q) :
    |h15NormalizedProgressionTerminalRowBoundaryLift N g r U L q d| ≤
      (2 * (q + 1) : ℝ) * (1 / (U : ℝ)) ^ 2 := by
  rw [← sum_h15NormalizedRowBoundaryPointSupport_eq_terminalLift]
  have hsub :
      h15NormalizedRowSuperperiodBoundaryPointSupport U L q ⊆
        h15NormalizedSuperperiodBoundarySupport U L q := by
    intro u hu
    rw [← h15NormalizedRowBoundary_union_incomplete_eq_superperiodBoundary
      U L q hq]
    exact Finset.mem_union_left _ hu
  calc
    |∑ u ∈ h15NormalizedRowSuperperiodBoundaryPointSupport U L q,
        h15NormalizedProgressionCoupledBoundaryPointWeight N g U L q d u *
          h15PairedDirectCrossMode r u q| ≤
        ∑ u ∈ h15NormalizedRowSuperperiodBoundaryPointSupport U L q,
          |h15NormalizedProgressionCoupledBoundaryPointWeight
              N g U L q d u * h15PairedDirectCrossMode r u q| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _u ∈ h15NormalizedRowSuperperiodBoundaryPointSupport U L q,
        (1 / (U : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro u hu
      rw [abs_mul]
      calc
        |h15NormalizedProgressionCoupledBoundaryPointWeight N g U L q d u| *
            |h15PairedDirectCrossMode r u q| ≤
            (1 / (U : ℝ)) ^ 2 * 1 :=
          mul_le_mul
            (abs_h15NormalizedProgressionCoupledBoundaryPointWeight_le
              hN hg hU hq (hsub hu))
            (abs_h15PairedDirectCrossMode_le_one r u q hq)
            (abs_nonneg _) (by positivity)
        _ = (1 / (U : ℝ)) ^ 2 := mul_one _
    _ = ((h15NormalizedRowSuperperiodBoundaryPointSupport U L q).card : ℝ) *
        (1 / (U : ℝ)) ^ 2 := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * (q + 1) : ℝ) * (1 / (U : ℝ)) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (Finset.card_le_card hsub).trans
        (card_h15NormalizedSuperperiodBoundarySupport_le_density
          U L q hL hq)

noncomputable def h15NormalizedBoundarySectorModulusBudget
    (g U Q : ℕ) : ℝ :=
  (8 * (g.divisors.card : ℝ) * (Q : ℝ)) / (U : ℝ)

theorem abs_h15NormalizedBoundaryTerminalModulusRow_le
    {N g r U Q q : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g)
    (hU : 0 < U) (hQ : 0 < Q)
    (hqMem : q ∈ h15BettinChandeeSupportedNatBlock N g Q) :
    |h15NormalizedBoundaryTerminalModulusRow N g r U q| ≤
      h15NormalizedBoundarySectorModulusBudget g U Q := by
  have hqBounds := mem_h15BettinChandeeSupportedNatBlock.mp hqMem
  have hq : 0 < q := hQ.trans_le hqBounds.1
  have hqOne : q + 1 ≤ 2 * Q := by omega
  unfold h15NormalizedBoundaryTerminalModulusRow
    h15NormalizedBoundarySectorModulusBudget
  calc
    |∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
        h15NormalizedProgressionTerminalRowBoundaryLift N g r U
          (h15SquareDivisorProgressionModulus g d) q d| ≤
        ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
          |h15NormalizedProgressionTerminalRowBoundaryLift N g r U
            (h15SquareDivisorProgressionModulus g d) q d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
        (4 * Q : ℝ) * (1 / (U : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro d hd
      have hactive := activeNormalizedModulus_bounds (Nat.zero_lt_of_lt hg) hU hd
      calc
        |h15NormalizedProgressionTerminalRowBoundaryLift N g r U
            (h15SquareDivisorProgressionModulus g d) q d| ≤
            (2 * (q + 1) : ℝ) * (1 / (U : ℝ)) ^ 2 :=
          abs_h15NormalizedProgressionTerminalRowBoundaryLift_le
            hN hg hU (by omega) hq
        _ ≤ (4 * Q : ℝ) * (1 / (U : ℝ)) ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast (show 2 * (q + 1) ≤ 4 * Q by omega)
    _ = ((h15DyadicActivePeriodSquareDivisorIndices g U q).card : ℝ) *
        ((4 * Q : ℝ) * (1 / (U : ℝ)) ^ 2) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2 * U : ℝ) * (g.divisors.card : ℝ)) *
        ((4 * Q : ℝ) * (1 / (U : ℝ)) ^ 2) := by
      apply mul_le_mul_of_nonneg_right
      · exact card_h15DyadicActivePeriodSquareDivisorIndices_le
          (Nat.zero_lt_of_lt hg) hU
      · positivity
    _ = (8 * (g.divisors.card : ℝ) * (Q : ℝ)) / (U : ℝ) := by
      field_simp
      ring

theorem abs_h15NormalizedBoundaryIncompleteSmoothModulusRow_le
    {N g r U Q q : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g)
    (hU : 0 < U) (hQ : 0 < Q)
    (hqMem : q ∈ h15BettinChandeeSupportedNatBlock N g Q) :
    |h15NormalizedBoundaryIncompleteSmoothModulusRow N g r U q| ≤
      h15NormalizedBoundarySectorModulusBudget g U Q := by
  have hqBounds := mem_h15BettinChandeeSupportedNatBlock.mp hqMem
  have hq : 0 < q := hQ.trans_le hqBounds.1
  have hqOne : q + 1 ≤ 2 * Q := by omega
  unfold h15NormalizedBoundaryIncompleteSmoothModulusRow
    h15NormalizedBoundarySectorModulusBudget
  calc
    |∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
        h15NormalizedProgressionIncompleteEndpointRow N g r U
          (h15SquareDivisorProgressionModulus g d) q d| ≤
        ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
          |h15NormalizedProgressionIncompleteEndpointRow N g r U
            (h15SquareDivisorProgressionModulus g d) q d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
        (4 * Q : ℝ) * (1 / (U : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro d _hd
      calc
        |h15NormalizedProgressionIncompleteEndpointRow N g r U
            (h15SquareDivisorProgressionModulus g d) q d| ≤
            (2 * q : ℝ) * (1 / (U : ℝ)) ^ 2 :=
          abs_h15NormalizedProgressionIncompleteEndpointRow_le
            hN hg hU hq
        _ ≤ (4 * Q : ℝ) * (1 / (U : ℝ)) ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast (show 2 * q ≤ 4 * Q by omega)
    _ = ((h15DyadicActivePeriodSquareDivisorIndices g U q).card : ℝ) *
        ((4 * Q : ℝ) * (1 / (U : ℝ)) ^ 2) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2 * U : ℝ) * (g.divisors.card : ℝ)) *
        ((4 * Q : ℝ) * (1 / (U : ℝ)) ^ 2) := by
      apply mul_le_mul_of_nonneg_right
      · exact card_h15DyadicActivePeriodSquareDivisorIndices_le
          (Nat.zero_lt_of_lt hg) hU
      · positivity
    _ = (8 * (g.divisors.card : ℝ) * (Q : ℝ)) / (U : ℝ) := by
      field_simp
      ring

/-! ## Global L1 and correlation budgets -/

noncomputable def h15NormalizedBoundarySectorGlobalL1Budget
    (g U Q : ℕ) : ℝ :=
  (8 * (g.divisors.card : ℝ) * (Q : ℝ) ^ 2) / (U : ℝ)

noncomputable def h15NormalizedBoundaryTerminalModulusL1Mass
    (N g r U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    |h15NormalizedBoundaryTerminalModulusRow N g r U q|

noncomputable def h15NormalizedBoundaryIncompleteSmoothModulusL1Mass
    (N g r U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    |h15NormalizedBoundaryIncompleteSmoothModulusRow N g r U q|

theorem h15NormalizedBoundaryTerminalModulusL1Mass_le
    {N g r U Q : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g)
    (hU : 0 < U) (hQ : 0 < Q) :
    h15NormalizedBoundaryTerminalModulusL1Mass N g r U Q ≤
      h15NormalizedBoundarySectorGlobalL1Budget g U Q := by
  unfold h15NormalizedBoundaryTerminalModulusL1Mass
    h15NormalizedBoundarySectorGlobalL1Budget
  calc
    (∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        |h15NormalizedBoundaryTerminalModulusRow N g r U q|) ≤
        ∑ _q ∈ h15BettinChandeeSupportedNatBlock N g Q,
          h15NormalizedBoundarySectorModulusBudget g U Q := by
      apply Finset.sum_le_sum
      intro q hqMem
      exact abs_h15NormalizedBoundaryTerminalModulusRow_le
        hN hg hU hQ hqMem
    _ = ((h15BettinChandeeSupportedNatBlock N g Q).card : ℝ) *
        h15NormalizedBoundarySectorModulusBudget g U Q := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Q : ℝ) * h15NormalizedBoundarySectorModulusBudget g U Q := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast card_h15BettinChandeeSupportedNatBlock_le N g Q
      · unfold h15NormalizedBoundarySectorModulusBudget
        positivity
    _ = (8 * (g.divisors.card : ℝ) * (Q : ℝ) ^ 2) / (U : ℝ) := by
      unfold h15NormalizedBoundarySectorModulusBudget
      ring

theorem h15NormalizedBoundaryIncompleteSmoothModulusL1Mass_le
    {N g r U Q : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g)
    (hU : 0 < U) (hQ : 0 < Q) :
    h15NormalizedBoundaryIncompleteSmoothModulusL1Mass N g r U Q ≤
      h15NormalizedBoundarySectorGlobalL1Budget g U Q := by
  unfold h15NormalizedBoundaryIncompleteSmoothModulusL1Mass
    h15NormalizedBoundarySectorGlobalL1Budget
  calc
    (∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        |h15NormalizedBoundaryIncompleteSmoothModulusRow N g r U q|) ≤
        ∑ _q ∈ h15BettinChandeeSupportedNatBlock N g Q,
          h15NormalizedBoundarySectorModulusBudget g U Q := by
      apply Finset.sum_le_sum
      intro q hqMem
      exact abs_h15NormalizedBoundaryIncompleteSmoothModulusRow_le
        hN hg hU hQ hqMem
    _ = ((h15BettinChandeeSupportedNatBlock N g Q).card : ℝ) *
        h15NormalizedBoundarySectorModulusBudget g U Q := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Q : ℝ) * h15NormalizedBoundarySectorModulusBudget g U Q := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast card_h15BettinChandeeSupportedNatBlock_le N g Q
      · unfold h15NormalizedBoundarySectorModulusBudget
        positivity
    _ = (8 * (g.divisors.card : ℝ) * (Q : ℝ) ^ 2) / (U : ℝ) := by
      unfold h15NormalizedBoundarySectorModulusBudget
      ring

theorem abs_sum_erase_mul_le_mul_sum_abs
    {ι : Type} [DecidableEq ι] (s : Finset ι) (f g : ι → ℝ) :
    |∑ i ∈ s, ∑ j ∈ s.erase i, f i * g j| ≤
      (∑ i ∈ s, |f i|) * (∑ j ∈ s, |g j|) := by
  calc
    |∑ i ∈ s, ∑ j ∈ s.erase i, f i * g j| ≤
        ∑ i ∈ s, |∑ j ∈ s.erase i, f i * g j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, ∑ j ∈ s.erase i, |f i * g j| := by
      apply Finset.sum_le_sum
      intro i _hi
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ s, |f i| * (∑ j ∈ s.erase i, |g j|) := by
      apply Finset.sum_congr rfl
      intro i _hi
      simp only [abs_mul, Finset.mul_sum]
    _ ≤ ∑ i ∈ s, |f i| * (∑ j ∈ s, |g j|) := by
      apply Finset.sum_le_sum
      intro i _hi
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.erase_subset i s) (fun _j _hj _ => abs_nonneg _)
      · exact abs_nonneg _
    _ = (∑ i ∈ s, |f i|) * (∑ j ∈ s, |g j|) := by
      rw [Finset.sum_mul]

noncomputable def h15NormalizedBoundarySectorCorrelationBudget
    (g U Q : ℕ) : ℝ :=
  (h15NormalizedBoundarySectorGlobalL1Budget g U Q) ^ 2

theorem abs_h15NormalizedBoundaryTerminalTerminalCorrelation_le
    {N g r U Q : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g)
    (hU : 0 < U) (hQ : 0 < Q) :
    |h15NormalizedBoundaryTerminalTerminalCorrelation N g r U Q| ≤
      h15NormalizedBoundarySectorCorrelationBudget g U Q := by
  unfold h15NormalizedBoundaryTerminalTerminalCorrelation
    h15NormalizedBoundarySectorCorrelationBudget
  calc
    |∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        ∑ q' ∈ (h15BettinChandeeSupportedNatBlock N g Q).erase q,
          h15NormalizedBoundaryTerminalModulusRow N g r U q *
            h15NormalizedBoundaryTerminalModulusRow N g r U q'| ≤
        h15NormalizedBoundaryTerminalModulusL1Mass N g r U Q *
          h15NormalizedBoundaryTerminalModulusL1Mass N g r U Q :=
      abs_sum_erase_mul_le_mul_sum_abs _ _ _
    _ ≤ h15NormalizedBoundarySectorGlobalL1Budget g U Q *
        h15NormalizedBoundarySectorGlobalL1Budget g U Q := by
      have hmass := h15NormalizedBoundaryTerminalModulusL1Mass_le
        (r := r) hN hg hU hQ
      have hmassNonneg :
          0 ≤ h15NormalizedBoundaryTerminalModulusL1Mass N g r U Q := by
        unfold h15NormalizedBoundaryTerminalModulusL1Mass
        positivity
      have hbudgetNonneg :
          0 ≤ h15NormalizedBoundarySectorGlobalL1Budget g U Q := by
        unfold h15NormalizedBoundarySectorGlobalL1Budget
        positivity
      exact mul_le_mul hmass hmass hmassNonneg hbudgetNonneg
    _ = (h15NormalizedBoundarySectorGlobalL1Budget g U Q) ^ 2 := by ring

theorem abs_h15NormalizedBoundaryTerminalSmoothCorrelation_le
    {N g r U Q : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g)
    (hU : 0 < U) (hQ : 0 < Q) :
    |h15NormalizedBoundaryTerminalSmoothCorrelation N g r U Q| ≤
      h15NormalizedBoundarySectorCorrelationBudget g U Q := by
  unfold h15NormalizedBoundaryTerminalSmoothCorrelation
    h15NormalizedBoundarySectorCorrelationBudget
  calc
    |∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        ∑ q' ∈ (h15BettinChandeeSupportedNatBlock N g Q).erase q,
          h15NormalizedBoundaryTerminalModulusRow N g r U q *
            h15NormalizedBoundaryIncompleteSmoothModulusRow N g r U q'| ≤
        h15NormalizedBoundaryTerminalModulusL1Mass N g r U Q *
          h15NormalizedBoundaryIncompleteSmoothModulusL1Mass N g r U Q :=
      abs_sum_erase_mul_le_mul_sum_abs _ _ _
    _ ≤ h15NormalizedBoundarySectorGlobalL1Budget g U Q *
        h15NormalizedBoundarySectorGlobalL1Budget g U Q := by
      have hterminal := h15NormalizedBoundaryTerminalModulusL1Mass_le
        (r := r) hN hg hU hQ
      have hsmooth := h15NormalizedBoundaryIncompleteSmoothModulusL1Mass_le
        (r := r) hN hg hU hQ
      have hsmoothNonneg :
          0 ≤ h15NormalizedBoundaryIncompleteSmoothModulusL1Mass N g r U Q := by
        unfold h15NormalizedBoundaryIncompleteSmoothModulusL1Mass
        positivity
      have hbudgetNonneg :
          0 ≤ h15NormalizedBoundarySectorGlobalL1Budget g U Q := by
        unfold h15NormalizedBoundarySectorGlobalL1Budget
        positivity
      exact mul_le_mul hterminal hsmooth hsmoothNonneg hbudgetNonneg
    _ = (h15NormalizedBoundarySectorGlobalL1Budget g U Q) ^ 2 := by ring

theorem abs_h15NormalizedBoundarySmoothSmoothCorrelation_le
    {N g r U Q : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g)
    (hU : 0 < U) (hQ : 0 < Q) :
    |h15NormalizedBoundarySmoothSmoothCorrelation N g r U Q| ≤
      h15NormalizedBoundarySectorCorrelationBudget g U Q := by
  unfold h15NormalizedBoundarySmoothSmoothCorrelation
    h15NormalizedBoundarySectorCorrelationBudget
  calc
    |∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        ∑ q' ∈ (h15BettinChandeeSupportedNatBlock N g Q).erase q,
          h15NormalizedBoundaryIncompleteSmoothModulusRow N g r U q *
            h15NormalizedBoundaryIncompleteSmoothModulusRow N g r U q'| ≤
        h15NormalizedBoundaryIncompleteSmoothModulusL1Mass N g r U Q *
          h15NormalizedBoundaryIncompleteSmoothModulusL1Mass N g r U Q :=
      abs_sum_erase_mul_le_mul_sum_abs _ _ _
    _ ≤ h15NormalizedBoundarySectorGlobalL1Budget g U Q *
        h15NormalizedBoundarySectorGlobalL1Budget g U Q := by
      have hmass := h15NormalizedBoundaryIncompleteSmoothModulusL1Mass_le
        (r := r) hN hg hU hQ
      have hmassNonneg :
          0 ≤ h15NormalizedBoundaryIncompleteSmoothModulusL1Mass N g r U Q := by
        unfold h15NormalizedBoundaryIncompleteSmoothModulusL1Mass
        positivity
      have hbudgetNonneg :
          0 ≤ h15NormalizedBoundarySectorGlobalL1Budget g U Q := by
        unfold h15NormalizedBoundarySectorGlobalL1Budget
        positivity
      exact mul_le_mul hmass hmass hmassNonneg hbudgetNonneg
    _ = (h15NormalizedBoundarySectorGlobalL1Budget g U Q) ^ 2 := by ring

/-- Separating the three sectors by absolute values costs four copies of the
common correlation budget. -/
theorem abs_h15NormalizedBoundaryExplicitCrossModulusCorrelation_le_four_mul
    {N g r U Q : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g)
    (hU : 0 < U) (hQ : 0 < Q) :
    |h15NormalizedBoundaryExplicitCrossModulusCorrelation N g r U Q| ≤
      4 * h15NormalizedBoundarySectorCorrelationBudget g U Q := by
  rw [h15NormalizedBoundaryExplicitCrossModulusCorrelation_eq_threeSectors hQ]
  have hTT := abs_h15NormalizedBoundaryTerminalTerminalCorrelation_le
    (r := r) hN hg hU hQ
  have hTS := abs_h15NormalizedBoundaryTerminalSmoothCorrelation_le
    (r := r) hN hg hU hQ
  have hSS := abs_h15NormalizedBoundarySmoothSmoothCorrelation_le
    (r := r) hN hg hU hQ
  have htriangle :
      |h15NormalizedBoundaryTerminalTerminalCorrelation N g r U Q +
          2 * h15NormalizedBoundaryTerminalSmoothCorrelation N g r U Q +
          h15NormalizedBoundarySmoothSmoothCorrelation N g r U Q| ≤
        |h15NormalizedBoundaryTerminalTerminalCorrelation N g r U Q| +
          2 * |h15NormalizedBoundaryTerminalSmoothCorrelation N g r U Q| +
          |h15NormalizedBoundarySmoothSmoothCorrelation N g r U Q| := by
    calc
      |h15NormalizedBoundaryTerminalTerminalCorrelation N g r U Q +
          2 * h15NormalizedBoundaryTerminalSmoothCorrelation N g r U Q +
          h15NormalizedBoundarySmoothSmoothCorrelation N g r U Q| ≤
          |h15NormalizedBoundaryTerminalTerminalCorrelation N g r U Q +
            2 * h15NormalizedBoundaryTerminalSmoothCorrelation N g r U Q| +
            |h15NormalizedBoundarySmoothSmoothCorrelation N g r U Q| :=
        abs_add_le _ _
      _ ≤ (|h15NormalizedBoundaryTerminalTerminalCorrelation N g r U Q| +
          |2 * h15NormalizedBoundaryTerminalSmoothCorrelation N g r U Q|) +
          |h15NormalizedBoundarySmoothSmoothCorrelation N g r U Q| := by
        gcongr
        exact abs_add_le _ _
      _ = |h15NormalizedBoundaryTerminalTerminalCorrelation N g r U Q| +
          2 * |h15NormalizedBoundaryTerminalSmoothCorrelation N g r U Q| +
          |h15NormalizedBoundarySmoothSmoothCorrelation N g r U Q| := by
        rw [abs_mul]
        norm_num
  linarith

/-! ## Balanced exponent ledger -/

theorem h15NormalizedBoundarySectorGlobalL1Budget_balanced_le
    {g U Q : ℕ} (hU : 0 < U) (hQU : Q ≤ U) :
    h15NormalizedBoundarySectorGlobalL1Budget g U Q ≤
      8 * (g.divisors.card : ℝ) * (Q : ℝ) := by
  unfold h15NormalizedBoundarySectorGlobalL1Budget
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (U : ℝ))).2
  have hQU' : (Q : ℝ) ≤ (U : ℝ) := by exact_mod_cast hQU
  calc
    8 * (g.divisors.card : ℝ) * (Q : ℝ) ^ 2 ≤
        8 * (g.divisors.card : ℝ) * ((Q : ℝ) * (U : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [pow_two]
      exact mul_le_mul_of_nonneg_left hQU' (by positivity)
    _ = 8 * (g.divisors.card : ℝ) * (Q : ℝ) * (U : ℝ) := by ring

theorem h15NormalizedBoundarySectorCorrelationBudget_balanced_le
    {g U Q : ℕ} (hU : 0 < U) (hQU : Q ≤ U) :
    h15NormalizedBoundarySectorCorrelationBudget g U Q ≤
      64 * (g.divisors.card : ℝ) ^ 2 * (Q : ℝ) ^ 2 := by
  unfold h15NormalizedBoundarySectorCorrelationBudget
  have h := h15NormalizedBoundarySectorGlobalL1Budget_balanced_le
    (g := g) hU hQU
  calc
    (h15NormalizedBoundarySectorGlobalL1Budget g U Q) ^ 2 ≤
        (8 * (g.divisors.card : ℝ) * (Q : ℝ)) ^ 2 := by
      exact pow_le_pow_left₀ (by
        unfold h15NormalizedBoundarySectorGlobalL1Budget
        positivity) h 2
    _ = 64 * (g.divisors.card : ℝ) ^ 2 * (Q : ℝ) ^ 2 := by ring

/-- The complete sectorwise absolute route still grows quadratically in the
balanced modulus scale. -/
theorem abs_h15NormalizedBoundaryExplicitCrossModulusCorrelation_balanced_le
    {N g r U Q : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g)
    (hU : 0 < U) (hQ : 0 < Q) (hQU : Q ≤ U) :
    |h15NormalizedBoundaryExplicitCrossModulusCorrelation N g r U Q| ≤
      256 * (g.divisors.card : ℝ) ^ 2 * (Q : ℝ) ^ 2 := by
  calc
    |h15NormalizedBoundaryExplicitCrossModulusCorrelation N g r U Q| ≤
        4 * h15NormalizedBoundarySectorCorrelationBudget g U Q :=
      abs_h15NormalizedBoundaryExplicitCrossModulusCorrelation_le_four_mul
        hN hg hU hQ
    _ ≤ 4 * (64 * (g.divisors.card : ℝ) ^ 2 * (Q : ℝ) ^ 2) := by
      gcongr
      exact h15NormalizedBoundarySectorCorrelationBudget_balanced_le hU hQU
    _ = 256 * (g.divisors.card : ℝ) ^ 2 * (Q : ℝ) ^ 2 := by ring

end NBMellinTools.NB12
