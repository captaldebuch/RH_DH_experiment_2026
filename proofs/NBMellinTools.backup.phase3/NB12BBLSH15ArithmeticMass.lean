/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15MovingCutoff

/-!
# Polynomial growth of the complete H15 arithmetic row mass

The adaptive cutoff theorem is qualitative until the finite arithmetic row
mass is bounded as the H15 cutoff grows.  This file supplies a deliberately
coarse but completely explicit polynomial bound.  It uses only the support of
the log taper, `|c_N(m)| ≤ 1`, the finite `N^3 × 2` row family, and the fact
that every reduced denominator is at most `N`.

No cancellation is used.  The purpose is to identify the precise decay rate
that the shifted divisor-frequency tail must beat before a fixed-power cutoff
can be certified.
-/

open scoped BigOperators
open Complex

namespace NBMellinTools.NB12

theorem h15LaurentG_pos {N : ℕ} (i : H15LaurentRowIndex N) :
    0 < h15LaurentG i := by
  simp [h15LaurentG]

theorem h15LaurentA_pos {N : ℕ} (i : H15LaurentRowIndex N) :
    0 < h15LaurentA i := by
  simp [h15LaurentA]

theorem h15LaurentQ_pos {N : ℕ} (i : H15LaurentRowIndex N) :
    0 < h15LaurentQ i := by
  simp [h15LaurentQ]

theorem h15LaurentA_le {N : ℕ} (i : H15LaurentRowIndex N) :
    h15LaurentA i ≤ N := by
  simpa [h15LaurentA] using i.2.1.isLt

theorem h15LaurentQ_le {N : ℕ} (i : H15LaurentRowIndex N) :
    h15LaurentQ i ≤ N := by
  simpa [h15LaurentQ] using i.2.2.1.isLt

/-- Reduction by a gcd never makes either oriented denominator larger than
the ambient H15 cutoff. -/
theorem h15LaurentReducedDenominator_le {N : ℕ}
    (i : H15LaurentRowIndex N) :
    h15LaurentReducedDenominator i ≤ N := by
  unfold h15LaurentReducedDenominator
  split_ifs
  · exact (Nat.div_le_self _ _).trans (h15LaurentQ_le i)
  · exact (Nat.div_le_self _ _).trans (h15LaurentA_le i)

theorem h15LaurentRow_denominator_le {N : ℕ}
    (i : H15LaurentRowIndex N) :
    (h15LaurentRow i).denominator ≤ N := by
  rw [h15LaurentRow_denominator]
  exact h15LaurentReducedDenominator_le i

/-- A supported oriented H15 row has absolute coefficient at most `π`.
This intentionally discards all reciprocal `g a q` savings. -/
theorem norm_h15LaurentRowWeight_le_pi {N : ℕ}
    (hN : 2 ≤ N) (i : H15LaurentRowIndex N) :
    ‖h15LaurentRowWeight i‖ ≤ Real.pi := by
  classical
  unfold h15LaurentRowWeight
  split_ifs with hvalid
  · have hgpos : 1 ≤ h15LaurentG i := h15LaurentG_pos i
    have hapos : 1 ≤ h15LaurentA i := h15LaurentA_pos i
    have hqpos : 1 ≤ h15LaurentQ i := h15LaurentQ_pos i
    have hga : 1 ≤ h15LaurentG i * h15LaurentA i :=
      Nat.mul_pos hgpos hapos
    have hgq : 1 ≤ h15LaurentG i * h15LaurentQ i :=
      Nat.mul_pos hgpos hqpos
    have hca := abs_h15NaturalLogTaperCoeff_le_one
      hN hga hvalid.1
    have hcq := abs_h15NaturalLogTaperCoeff_le_one
      hN hgq hvalid.2.1
    have hgcast : (1 : ℝ) ≤ h15LaurentG i := by exact_mod_cast hgpos
    have hacast : (1 : ℝ) ≤ h15LaurentA i := by exact_mod_cast hapos
    have hqcast : (1 : ℝ) ≤ h15LaurentQ i := by exact_mod_cast hqpos
    simp only [norm_real, Real.norm_eq_abs, abs_div, abs_mul]
    rw [abs_of_nonneg Real.pi_pos.le]
    have hprod :
        |h15NaturalLogTaperCoeff N (h15LaurentG i * h15LaurentA i)| *
            |h15NaturalLogTaperCoeff N (h15LaurentG i * h15LaurentQ i)| ≤
          1 :=
      mul_le_one₀ hca
        (abs_nonneg
          (h15NaturalLogTaperCoeff N
            (h15LaurentG i * h15LaurentQ i))) hcq
    have hden : (1 : ℝ) ≤
        |(h15LaurentG i : ℝ)| *
          (|(h15LaurentA i : ℝ)| * |(h15LaurentQ i : ℝ)|) := by
      rw [abs_of_nonneg (show 0 ≤ (h15LaurentG i : ℝ) by positivity),
        abs_of_nonneg (show 0 ≤ (h15LaurentA i : ℝ) by positivity),
        abs_of_nonneg (show 0 ≤ (h15LaurentQ i : ℝ) by positivity)]
      calc
        (1 : ℝ) = 1 * (1 * 1) := by ring
        _ ≤ (h15LaurentG i : ℝ) *
            ((h15LaurentA i : ℝ) * (h15LaurentQ i : ℝ)) := by
          gcongr
    calc
      (|h15NaturalLogTaperCoeff N (h15LaurentG i * h15LaurentA i)| *
            |h15NaturalLogTaperCoeff N (h15LaurentG i * h15LaurentQ i)| /
          |(h15LaurentG i : ℝ)| * Real.pi) /
          (|(h15LaurentA i : ℝ)| * |(h15LaurentQ i : ℝ)|) =
        (|h15NaturalLogTaperCoeff N (h15LaurentG i * h15LaurentA i)| *
            |h15NaturalLogTaperCoeff N (h15LaurentG i * h15LaurentQ i)|) *
          Real.pi /
          (|(h15LaurentG i : ℝ)| *
            (|(h15LaurentA i : ℝ)| * |(h15LaurentQ i : ℝ)|)) := by
              ring
      _ ≤ (1 * Real.pi) /
          (|(h15LaurentG i : ℝ)| *
            (|(h15LaurentA i : ℝ)| * |(h15LaurentQ i : ℝ)|)) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hprod Real.pi_pos.le) (by positivity)
      _ ≤ 1 * Real.pi / 1 := by
        exact div_le_div_of_nonneg_left
          (mul_nonneg (by norm_num) Real.pi_pos.le) (by norm_num) hden
      _ = Real.pi := by ring
  · simpa using Real.pi_pos.le

/-- Each summand in the three-halves arithmetic mass is bounded by
`π N²`. -/
theorem h15ThreeHalfArithmeticMass_summand_le
    {N : ℕ} (hN : 2 ≤ N) (i : H15LaurentRowIndex N) :
    ‖h15LaurentRowWeight i‖ *
        ((h15LaurentRow i).denominator : ℝ) ^ 2 ≤
      Real.pi * (N : ℝ) ^ 2 := by
  have hd : ((h15LaurentRow i).denominator : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast h15LaurentRow_denominator_le i
  have hdn : 0 ≤ ((h15LaurentRow i).denominator : ℝ) := by positivity
  have hNn : 0 ≤ (N : ℝ) := by positivity
  exact mul_le_mul
    (norm_h15LaurentRowWeight_le_pi hN i)
    (pow_le_pow_left₀ hdn hd 2)
    (sq_nonneg _)
    Real.pi_pos.le

/-- Coarse unconditional polynomial bound for the complete arithmetic row
mass.  The exponent `5` comes from `2N³` possible oriented rows and the
discarded denominator-square bound `N²`. -/
theorem h15ThreeHalfArithmeticMass_le (n : ℕ) :
    h15ThreeHalfPositiveLineRowGrowth.arithmeticMass n ≤
      2 * Real.pi * ((n + 2 : ℕ) : ℝ) ^ 5 := by
  classical
  let N : ℕ := n + 2
  have hN : 2 ≤ N := by omega
  unfold H15PositiveLineRowGrowth.arithmeticMass
  change (∑ i : H15LaurentRowIndex N,
      ‖h15LaurentRowWeight i‖ *
        ((h15LaurentRow i).denominator : ℝ) ^ 2) ≤ _
  calc
    (∑ i : H15LaurentRowIndex N,
        ‖h15LaurentRowWeight i‖ *
          ((h15LaurentRow i).denominator : ℝ) ^ 2) ≤
      ∑ _i : H15LaurentRowIndex N, Real.pi * (N : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact h15ThreeHalfArithmeticMass_summand_le hN i
    _ = 2 * Real.pi * (N : ℝ) ^ 5 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_prod, Fintype.card_fin]
      push_cast
      ring
    _ = 2 * Real.pi * ((n + 2 : ℕ) : ℝ) ^ 5 := by rfl

/-- After Abel damping, the mass part of the ultra-high budget grows at most
like `(n+2)^5/(n+1)^(3/2)`. -/
theorem h15ThreeHalfDampedArithmeticMass_le (n : ℕ) :
    h15ContourDamping n ^ (3 / 2 : ℝ) *
        h15ThreeHalfPositiveLineRowGrowth.arithmeticMass n ≤
      (1 / (((n + 1 : ℕ) : ℝ))) ^ (3 / 2 : ℝ) *
        (2 * Real.pi * ((n + 2 : ℕ) : ℝ) ^ 5) := by
  exact mul_le_mul
    (Real.rpow_le_rpow (le_of_lt (h15ContourDamping_pos n))
      (h15ContourDamping_le_one_div n) (by norm_num))
    (h15ThreeHalfArithmeticMass_le n)
    (h15ThreeHalfPositiveLineRowGrowth.arithmeticMass_nonneg n)
    (Real.rpow_nonneg (by positivity) _)

/-- The complete ultra-high budget with every arithmetic dependence replaced
by the explicit polynomial majorant.  Thus the only non-explicit asymptotic
factor left in this sector is the shifted divisor-frequency tail. -/
theorem h15ThreeHalfUltraHighCoupledBudget_le_polynomial
    (n J : ℕ) :
    h15ThreeHalfUltraHighCoupledBudget n J ≤
      h15ThreeHalfFrequencyConstant *
        ((1 / (((n + 1 : ℕ) : ℝ))) ^ (3 / 2 : ℝ) *
          (2 * Real.pi * ((n + 2 : ℕ) : ℝ) ^ 5)) *
        h15ThreeHalfShiftedFrequencyTail J *
        h15ThreeHalfVerticalProfileMass := by
  unfold h15ThreeHalfUltraHighCoupledBudget
  let M : ℝ :=
    (1 / (((n + 1 : ℕ) : ℝ))) ^ (3 / 2 : ℝ) *
      (2 * Real.pi * ((n + 2 : ℕ) : ℝ) ^ 5)
  have hmass :
      h15ContourDamping n ^ (3 / 2 : ℝ) *
          h15ThreeHalfPositiveLineRowGrowth.arithmeticMass n ≤ M :=
    h15ThreeHalfDampedArithmeticMass_le n
  have hfirst :
      h15ThreeHalfFrequencyConstant *
          (h15ContourDamping n ^ (3 / 2 : ℝ) *
            h15ThreeHalfPositiveLineRowGrowth.arithmeticMass n) ≤
        h15ThreeHalfFrequencyConstant * M :=
    mul_le_mul_of_nonneg_left hmass h15ThreeHalfFrequencyConstant_nonneg
  have hsecond := mul_le_mul_of_nonneg_right hfirst
    (h15ThreeHalfShiftedFrequencyTail_nonneg J)
  have hthird := mul_le_mul_of_nonneg_right hsecond
    h15ThreeHalfVerticalProfileMass_nonneg
  calc
    h15ThreeHalfFrequencyConstant * h15ContourDamping n ^ (3 / 2 : ℝ) *
          h15ThreeHalfPositiveLineRowGrowth.arithmeticMass n *
          h15ThreeHalfShiftedFrequencyTail J *
          h15ThreeHalfVerticalProfileMass =
        h15ThreeHalfFrequencyConstant *
            (h15ContourDamping n ^ (3 / 2 : ℝ) *
              h15ThreeHalfPositiveLineRowGrowth.arithmeticMass n) *
            h15ThreeHalfShiftedFrequencyTail J *
            h15ThreeHalfVerticalProfileMass := by ring
    _ ≤ h15ThreeHalfFrequencyConstant * M *
          h15ThreeHalfShiftedFrequencyTail J *
          h15ThreeHalfVerticalProfileMass := hthird
    _ = h15ThreeHalfFrequencyConstant *
        ((1 / (((n + 1 : ℕ) : ℝ))) ^ (3 / 2 : ℝ) *
          (2 * Real.pi * ((n + 2 : ℕ) : ℝ) ^ 5)) *
        h15ThreeHalfShiftedFrequencyTail J *
        h15ThreeHalfVerticalProfileMass := by rfl

/-- The same explicit polynomial ledger controls the actual finite-height
H15 ultra-high integral remainder.  This is uniform in every nonnegative
contour height. -/
theorem norm_h15ThreeHalfHighFrequencyIntegralRemainder_le_polynomial
    (n J : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    ‖h15ThreeHalfHighFrequencyIntegralRemainder n (2 ^ J - 1) T‖ ≤
      h15ThreeHalfFrequencyConstant *
        ((1 / (((n + 1 : ℕ) : ℝ))) ^ (3 / 2 : ℝ) *
          (2 * Real.pi * ((n + 2 : ℕ) : ℝ) ^ 5)) *
        h15ThreeHalfShiftedFrequencyTail J *
        h15ThreeHalfVerticalProfileMass :=
  (norm_h15ThreeHalfHighFrequencyIntegralRemainder_le_budget n J T hT).trans
    (h15ThreeHalfUltraHighCoupledBudget_le_polynomial n J)

end NBMellinTools.NB12
