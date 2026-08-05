/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FinalBoundaryEvenAlias

/-!
# NB12zu: the final-boundary dispersion exponent ledger

This file computes the elementary baseline for the correction-preserving
cross-`(q,d)` dispersion gate.  Two finite Cauchy--Schwarz inequalities give
the trivial dispersion coefficient.  The all-modulus endpoint mean square
from Step 4v-m gives a uniform bound for the complete frequency energy.

On balanced blocks `Q ≤ U`, the energy is at most `64 * τ(g)`, whereas the
trivial dispersion coefficient is `2 * U * Q * τ(g)`.  Thus a dispersion
coefficient tending to zero is sufficient for endpoint decay; on `Q = U`
this requires a full `o(U⁻²)` relative saving over the trivial coefficient.
No such signed saving is asserted here.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate
open Complex

namespace NBMellinTools.NB12

/-! ## Two-level Cauchy--Schwarz baseline -/

theorem sq_h15NormalizedBoundaryFourierRowValue_le_meanSquareValue
    (N g r U L q d : ℕ) (hq : 0 < q) :
    (h15NormalizedBoundaryFourierRowValue N g r U L q d) ^ 2 ≤
      h15NormalizedBoundaryFourierMeanSquareValue N g U L q d := by
  rw [h15NormalizedBoundaryFourierRowValue_eq_pointRow N g r U L q d hq]
  unfold h15NormalizedBoundaryFourierMeanSquareValue
  rw [dif_pos hq]
  exact sq_h15NormalizedProgressionCoupledBoundaryPointRow_le_meanSquare
    N g r U L q d hq

theorem sq_h15NormalizedBoundaryFourierModulusRow_le
    (N g r U q : ℕ) (hq : 0 < q) :
    (∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
      h15NormalizedBoundaryFourierRowValue N g r U
        (h15SquareDivisorProgressionModulus g d) q d) ^ 2 ≤
      ((h15DyadicActivePeriodSquareDivisorIndices g U q).card : ℝ) *
        ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
          h15NormalizedBoundaryFourierMeanSquareValue N g U
            (h15SquareDivisorProgressionModulus g d) q d := by
  calc
    (∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
        h15NormalizedBoundaryFourierRowValue N g r U
          (h15SquareDivisorProgressionModulus g d) q d) ^ 2 ≤
        ((h15DyadicActivePeriodSquareDivisorIndices g U q).card : ℝ) *
          ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
            (h15NormalizedBoundaryFourierRowValue N g r U
              (h15SquareDivisorProgressionModulus g d) q d) ^ 2 := by
      simpa only [sq] using
        (sq_sum_le_card_mul_sum_sq
          (s := h15DyadicActivePeriodSquareDivisorIndices g U q)
          (f := fun d => h15NormalizedBoundaryFourierRowValue N g r U
            (h15SquareDivisorProgressionModulus g d) q d))
    _ ≤ ((h15DyadicActivePeriodSquareDivisorIndices g U q).card : ℝ) *
        ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
          h15NormalizedBoundaryFourierMeanSquareValue N g U
            (h15SquareDivisorProgressionModulus g d) q d := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro d _hd
      exact sq_h15NormalizedBoundaryFourierRowValue_le_meanSquareValue
        N g r U (h15SquareDivisorProgressionModulus g d) q d hq

/-- The exact trivial cross-row coefficient is bounded by
`2 * U * Q * τ(g)`. -/
theorem sq_h15NormalizedBoundaryFourierAggregate_le_trivial
    {N g r U Q : ℕ} (hg : 0 < g) (hU : 0 < U) (hQ : 0 < Q) :
    |h15NormalizedBoundaryFourierAggregate N g r U Q| ^ 2 ≤
      (2 * (U : ℝ) * (Q : ℝ) * (g.divisors.card : ℝ)) *
        h15NormalizedBoundaryCrossModulusFrequencyEnergy N g U Q := by
  have hqCard :
      ((h15BettinChandeeSupportedNatBlock N g Q).card : ℝ) ≤ (Q : ℝ) := by
    exact_mod_cast card_h15BettinChandeeSupportedNatBlock_le N g Q
  unfold h15NormalizedBoundaryFourierAggregate
  rw [sq_abs]
  calc
    (∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
          h15NormalizedBoundaryFourierRowValue N g r U
            (h15SquareDivisorProgressionModulus g d) q d) ^ 2 ≤
        ((h15BettinChandeeSupportedNatBlock N g Q).card : ℝ) *
          ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
            (∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
              h15NormalizedBoundaryFourierRowValue N g r U
                (h15SquareDivisorProgressionModulus g d) q d) ^ 2 := by
      simpa only [sq] using
        (sq_sum_le_card_mul_sum_sq
          (s := h15BettinChandeeSupportedNatBlock N g Q)
          (f := fun q => ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
            h15NormalizedBoundaryFourierRowValue N g r U
              (h15SquareDivisorProgressionModulus g d) q d))
    _ ≤ ((h15BettinChandeeSupportedNatBlock N g Q).card : ℝ) *
        ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
          ((h15DyadicActivePeriodSquareDivisorIndices g U q).card : ℝ) *
            ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
              h15NormalizedBoundaryFourierMeanSquareValue N g U
                (h15SquareDivisorProgressionModulus g d) q d := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro q hqMem
      have hqBounds := mem_h15BettinChandeeSupportedNatBlock.mp hqMem
      exact sq_h15NormalizedBoundaryFourierModulusRow_le
        N g r U q (hQ.trans_le hqBounds.1)
    _ ≤ ((h15BettinChandeeSupportedNatBlock N g Q).card : ℝ) *
        ((2 * U : ℝ) * (g.divisors.card : ℝ) *
          h15NormalizedBoundaryCrossModulusFrequencyEnergy N g U Q) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      unfold h15NormalizedBoundaryCrossModulusFrequencyEnergy
      calc
        (∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
            ((h15DyadicActivePeriodSquareDivisorIndices g U q).card : ℝ) *
              ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
                h15NormalizedBoundaryFourierMeanSquareValue N g U
                  (h15SquareDivisorProgressionModulus g d) q d) ≤
            ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
              ((2 * U : ℝ) * (g.divisors.card : ℝ)) *
                ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
                  h15NormalizedBoundaryFourierMeanSquareValue N g U
                    (h15SquareDivisorProgressionModulus g d) q d := by
          apply Finset.sum_le_sum
          intro q _hqMem
          apply mul_le_mul_of_nonneg_right
          · exact card_h15DyadicActivePeriodSquareDivisorIndices_le hg hU
          · exact Finset.sum_nonneg (fun _d _hd =>
              h15NormalizedBoundaryFourierMeanSquareValue_nonneg _ _ _ _ _ _)
        _ = (2 * U : ℝ) * (g.divisors.card : ℝ) *
            ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
              ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
                h15NormalizedBoundaryFourierMeanSquareValue N g U
                  (h15SquareDivisorProgressionModulus g d) q d := by
          rw [Finset.mul_sum]
    _ ≤ (Q : ℝ) *
        ((2 * U : ℝ) * (g.divisors.card : ℝ) *
          h15NormalizedBoundaryCrossModulusFrequencyEnergy N g U Q) := by
      apply mul_le_mul_of_nonneg_right hqCard
      exact mul_nonneg (by positivity)
        (h15NormalizedBoundaryCrossModulusFrequencyEnergy_nonneg N g U Q)
    _ = (2 * (U : ℝ) * (Q : ℝ) * (g.divisors.card : ℝ)) *
        h15NormalizedBoundaryCrossModulusFrequencyEnergy N g U Q := by ring

/-! ## Explicit frequency-energy majorant -/

noncomputable def h15NormalizedBoundaryModulusFrequencyEnergy
    (N g U q : ℕ) : ℝ :=
  ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
    h15NormalizedBoundaryFourierMeanSquareValue N g U
      (h15SquareDivisorProgressionModulus g d) q d

theorem h15NormalizedBoundaryModulusFrequencyEnergy_le
    {N g U Q q : ℕ} (hN : 2 ≤ N) (hg : 0 < g)
    (hU : 0 < U) (hQ : 0 < Q)
    (hqMem : q ∈ h15BettinChandeeSupportedNatBlock N g Q) :
    h15NormalizedBoundaryModulusFrequencyEnergy N g U q ≤
      ((2 * U : ℝ) * (g.divisors.card : ℝ)) *
        ((32 * Q ^ 2 : ℝ) * (1 / (U : ℝ)) ^ 4) := by
  have hqBounds := mem_h15BettinChandeeSupportedNatBlock.mp hqMem
  have hq : 0 < q := hQ.trans_le hqBounds.1
  letI : NeZero q := ⟨hq.ne'⟩
  have hqUpper : q + 1 ≤ 2 * Q := by omega
  unfold h15NormalizedBoundaryModulusFrequencyEnergy
  calc
    (∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
        h15NormalizedBoundaryFourierMeanSquareValue N g U
          (h15SquareDivisorProgressionModulus g d) q d) ≤
        ∑ _d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
          (32 * Q ^ 2 : ℝ) * (1 / (U : ℝ)) ^ 4 := by
      apply Finset.sum_le_sum
      intro d hd
      have hactive := activeNormalizedModulus_bounds hg hU hd
      unfold h15NormalizedBoundaryFourierMeanSquareValue
      rw [dif_pos hq]
      calc
        h15NormalizedBoundaryFourierMeanSquare N g U
            (h15SquareDivisorProgressionModulus g d) q d ≤
            (8 * q * (q + 1) : ℝ) * (1 / (U : ℝ)) ^ 4 :=
          h15NormalizedBoundaryFourierMeanSquare_le_explicit
            N g U (h15SquareDivisorProgressionModulus g d) q d
              hN (by omega) hU (by omega) hq hactive.2.2
        _ ≤ (32 * Q ^ 2 : ℝ) * (1 / (U : ℝ)) ^ 4 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast (show 8 * q * (q + 1) ≤ 32 * Q ^ 2 by
            nlinarith [hqBounds.2.1, hqUpper])
    _ = (((h15DyadicActivePeriodSquareDivisorIndices g U q).card : ℝ) *
        ((32 * Q ^ 2 : ℝ) * (1 / (U : ℝ)) ^ 4)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2 * U : ℝ) * (g.divisors.card : ℝ)) *
        ((32 * Q ^ 2 : ℝ) * (1 / (U : ℝ)) ^ 4) := by
      apply mul_le_mul_of_nonneg_right
      · exact card_h15DyadicActivePeriodSquareDivisorIndices_le hg hU
      · positivity

/-- The complete cross-modulus energy is `O(τ(g) Q³/U³)`. -/
theorem h15NormalizedBoundaryCrossModulusFrequencyEnergy_le
    {N g U Q : ℕ} (hN : 2 ≤ N) (hg : 0 < g)
    (hU : 0 < U) (hQ : 0 < Q) :
    h15NormalizedBoundaryCrossModulusFrequencyEnergy N g U Q ≤
      (64 * (g.divisors.card : ℝ) * (Q : ℝ) ^ 3) /
        (U : ℝ) ^ 3 := by
  unfold h15NormalizedBoundaryCrossModulusFrequencyEnergy
  calc
    (∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
          h15NormalizedBoundaryFourierMeanSquareValue N g U
            (h15SquareDivisorProgressionModulus g d) q d) ≤
        ∑ _q ∈ h15BettinChandeeSupportedNatBlock N g Q,
          ((2 * U : ℝ) * (g.divisors.card : ℝ)) *
            ((32 * Q ^ 2 : ℝ) * (1 / (U : ℝ)) ^ 4) := by
      apply Finset.sum_le_sum
      intro q hqMem
      exact h15NormalizedBoundaryModulusFrequencyEnergy_le
        hN hg hU hQ hqMem
    _ = ((h15BettinChandeeSupportedNatBlock N g Q).card : ℝ) *
        (((2 * U : ℝ) * (g.divisors.card : ℝ)) *
          ((32 * Q ^ 2 : ℝ) * (1 / (U : ℝ)) ^ 4)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Q : ℝ) *
        (((2 * U : ℝ) * (g.divisors.card : ℝ)) *
          ((32 * Q ^ 2 : ℝ) * (1 / (U : ℝ)) ^ 4)) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast card_h15BettinChandeeSupportedNatBlock_le N g Q
      · positivity
    _ = (64 * (g.divisors.card : ℝ) * (Q : ℝ) ^ 3) /
        (U : ℝ) ^ 3 := by
      field_simp
      ring

/-- On balanced blocks the complete frequency energy is uniformly bounded
for fixed `g`. -/
theorem h15NormalizedBoundaryCrossModulusFrequencyEnergy_balanced_le
    {N g U Q : ℕ} (hN : 2 ≤ N) (hg : 0 < g)
    (hU : 0 < U) (hQ : 0 < Q) (hQU : Q ≤ U) :
    h15NormalizedBoundaryCrossModulusFrequencyEnergy N g U Q ≤
      64 * (g.divisors.card : ℝ) := by
  calc
    h15NormalizedBoundaryCrossModulusFrequencyEnergy N g U Q ≤
        (64 * (g.divisors.card : ℝ) * (Q : ℝ) ^ 3) /
          (U : ℝ) ^ 3 :=
      h15NormalizedBoundaryCrossModulusFrequencyEnergy_le hN hg hU hQ
    _ ≤ 64 * (g.divisors.card : ℝ) := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (U : ℝ) ^ 3)).2
      have hQU' : (Q : ℝ) ≤ (U : ℝ) := by exact_mod_cast hQU
      have hpow : (Q : ℝ) ^ 3 ≤ (U : ℝ) ^ 3 :=
        pow_le_pow_left₀ (by positivity) hQU' 3
      nlinarith [show 0 ≤ (g.divisors.card : ℝ) by positivity]

/-! ## The exact saving threshold -/

theorem h15CorrectionCoupledCrossModulusFrequencyDispersion_trivial
    {N g r U Q : ℕ} (hg : 0 < g) (hU : 0 < U) (hQ : 0 < Q) :
    H15CorrectionCoupledCrossModulusFrequencyDispersion N g r U Q
      (2 * (U : ℝ) * (Q : ℝ) * (g.divisors.card : ℝ)) := by
  constructor
  · positivity
  · exact sq_h15NormalizedBoundaryFourierAggregate_le_trivial hg hU hQ

/-- On balanced blocks, a dispersion coefficient `Δ = o(1)` is sufficient
for final-boundary decay when `g` is fixed. -/
theorem abs_h15NormalizedBoundaryFourierAggregate_le_sqrt_dispersion_balanced
    {N g r U Q : ℕ} {Δ : ℝ}
    (hN : 2 ≤ N) (hg : 0 < g) (hU : 0 < U)
    (hQ : 0 < Q) (hQU : Q ≤ U)
    (hdisp : H15CorrectionCoupledCrossModulusFrequencyDispersion
      N g r U Q Δ) :
    |h15NormalizedBoundaryFourierAggregate N g r U Q| ≤
      Real.sqrt (64 * (g.divisors.card : ℝ) * Δ) := by
  apply (Real.le_sqrt (abs_nonneg _)
    (mul_nonneg (by positivity) hdisp.1)).2
  calc
    |h15NormalizedBoundaryFourierAggregate N g r U Q| ^ 2 ≤
        Δ * h15NormalizedBoundaryCrossModulusFrequencyEnergy N g U Q :=
      hdisp.2
    _ ≤ Δ * (64 * (g.divisors.card : ℝ)) := by
      apply mul_le_mul_of_nonneg_left
      · exact h15NormalizedBoundaryCrossModulusFrequencyEnergy_balanced_le
          hN hg hU hQ hQU
      · exact hdisp.1
    _ = 64 * (g.divisors.card : ℝ) * Δ := by ring

/-- The purely elementary bound still grows like `sqrt(UQ)` and therefore
cannot prove endpoint decay on balanced blocks. -/
theorem abs_h15NormalizedBoundaryFourierAggregate_le_trivial_balanced
    {N g r U Q : ℕ} (hN : 2 ≤ N) (hg : 0 < g)
    (hU : 0 < U) (hQ : 0 < Q) (hQU : Q ≤ U) :
    |h15NormalizedBoundaryFourierAggregate N g r U Q| ≤
      Real.sqrt
        (128 * (U : ℝ) * (Q : ℝ) * (g.divisors.card : ℝ) ^ 2) := by
  have hradicand :
      64 * (g.divisors.card : ℝ) *
          (2 * (U : ℝ) * (Q : ℝ) * (g.divisors.card : ℝ)) =
        128 * (U : ℝ) * (Q : ℝ) * (g.divisors.card : ℝ) ^ 2 := by
    ring
  rw [← hradicand]
  exact abs_h15NormalizedBoundaryFourierAggregate_le_sqrt_dispersion_balanced
    hN hg hU hQ hQU
    (h15CorrectionCoupledCrossModulusFrequencyDispersion_trivial hg hU hQ)

end NBMellinTools.NB12
