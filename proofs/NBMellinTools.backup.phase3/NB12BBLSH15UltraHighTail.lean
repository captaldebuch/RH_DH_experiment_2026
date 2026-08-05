/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSDivisorSquareDyadic
import Mathlib.Algebra.Order.Chebyshev

/-!
# Quantitative frequency control for the H15 ultra-high tail

This file converts the proved divisor-square dyadic estimate into the
`L¹` frequency bound needed by the absolute ultra-high part of the hybrid
Bettin--Chandee strategy.  The conversion is finite Cauchy--Schwarz and does
not use any cancellation or unproved analytic-number-theory input.

It does not yet estimate the complete H15 row aggregate: the arithmetic row
mass and the passage from dyadic frequency blocks to the chosen moving cutoff
must still be coupled to this bound.
-/

open scoped BigOperators
open Filter Topology

namespace NBMellinTools.NB12

/-- The absolute frequency mass in one dyadic block. -/
noncomputable def h15BettinChandeeFrequencyBlockL1 (R : ℕ) : ℝ :=
  ∑ r ∈ h15BettinChandeeNatBlock R,
    h15BettinChandeeFrequencyCoefficient r

theorem h15BettinChandeeFrequencyCoefficient_nonneg (r : ℕ) :
    0 ≤ h15BettinChandeeFrequencyCoefficient r := by
  exact norm_nonneg _

theorem h15BettinChandeeFrequencyBlockL1_nonneg (R : ℕ) :
    0 ≤ h15BettinChandeeFrequencyBlockL1 R := by
  unfold h15BettinChandeeFrequencyBlockL1
  exact Finset.sum_nonneg fun r _ =>
    h15BettinChandeeFrequencyCoefficient_nonneg r

theorem card_h15BettinChandeeNatBlock (R : ℕ) :
    (h15BettinChandeeNatBlock R).card = R := by
  simp [h15BettinChandeeNatBlock]
  omega

/-- Finite Cauchy--Schwarz converts the exact frequency `L²` mass into the
absolute frequency mass on the same block. -/
theorem h15BettinChandeeFrequencyBlockL1_sq_le
    (R : ℕ) :
    h15BettinChandeeFrequencyBlockL1 R ^ 2 ≤
      (R : ℝ) * h15BettinChandeeFrequencyMass R := by
  unfold h15BettinChandeeFrequencyBlockL1
    h15BettinChandeeFrequencyMass
  calc
    (∑ r ∈ h15BettinChandeeNatBlock R,
        h15BettinChandeeFrequencyCoefficient r) ^ 2 ≤
      ((h15BettinChandeeNatBlock R).card : ℝ) *
        ∑ r ∈ h15BettinChandeeNatBlock R,
          h15BettinChandeeFrequencyCoefficient r ^ 2 := by
            exact sq_sum_le_card_mul_sum_sq
    _ = (R : ℝ) *
        ∑ r ∈ h15BettinChandeeNatBlock R,
          h15BettinChandeeFrequencyCoefficient r ^ 2 := by
            rw [card_h15BettinChandeeNatBlock]

/-- The explicit squared `L¹` block estimate obtained from the divisor-square
package constructed in `NB12BBLSDivisorSquareDyadic`. -/
theorem h15BettinChandeeFrequencyBlockL1_sq_le_explicit
    (R : ℕ) (hR : 1 ≤ R) :
    h15BettinChandeeFrequencyBlockL1 R ^ 2 ≤
      2 * (1 + Real.log (2 * (R : ℝ))) ^ 3 / (R : ℝ) := by
  calc
    h15BettinChandeeFrequencyBlockL1 R ^ 2 ≤
        (R : ℝ) * h15BettinChandeeFrequencyMass R :=
      h15BettinChandeeFrequencyBlockL1_sq_le R
    _ ≤ (R : ℝ) *
        (2 * (1 + Real.log (2 * (R : ℝ))) ^ 3 / (R : ℝ) ^ 2) := by
      gcongr
      exact h15DivisorSquareDyadicBound.bound R hR
    _ = 2 * (1 + Real.log (2 * (R : ℝ))) ^ 3 / (R : ℝ) := by
      have hR0 : (R : ℝ) ≠ 0 := by positivity
      field_simp

/-- Square-root form of the explicit dyadic `L¹` estimate. -/
theorem h15BettinChandeeFrequencyBlockL1_le_explicit
    (R : ℕ) (hR : 1 ≤ R) :
    h15BettinChandeeFrequencyBlockL1 R ≤
      Real.sqrt
        (2 * (1 + Real.log (2 * (R : ℝ))) ^ 3 / (R : ℝ)) := by
  exact Real.le_sqrt_of_sq_le
    (h15BettinChandeeFrequencyBlockL1_sq_le_explicit R hR)

/-- The explicit squared block majorant tends to zero.  This is the first
genuine asymptotic consequence of the divisor-square input. -/
theorem tendsto_h15FrequencyBlockSqMajorant_zero :
    Tendsto (fun R : ℕ =>
      2 * (1 + Real.log (2 * (R : ℝ))) ^ 3 / (R : ℝ))
      atTop (nhds 0) := by
  let c : ℝ := 2 * Real.exp 1
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hbase : Tendsto (fun x : ℝ =>
      Real.log x ^ 3 / ((1 : ℝ) * x + 0)) atTop (nhds 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 3 one_ne_zero
  have hscaled : Tendsto (fun x : ℝ =>
      (2 * c) * (Real.log (c * x) ^ 3 / (c * x))) atTop (nhds 0) :=
    by
      simpa only [Function.comp_apply, one_mul, add_zero, mul_zero] using
        (show Tendsto (fun _ : ℝ => 2 * c) atTop (nhds (2 * c)) from
          tendsto_const_nhds).mul
            (hbase.comp (tendsto_id.const_mul_atTop hc))
  have hnat := hscaled.comp tendsto_natCast_atTop_atTop
  apply hnat.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with R hR
  have hR0 : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
  have htwoR0 : (2 * (R : ℝ)) ≠ 0 := mul_ne_zero (by norm_num) hR0
  have hc0 : c ≠ 0 := hc.ne'
  have hlog : Real.log (c * (R : ℝ)) =
      1 + Real.log (2 * (R : ℝ)) := by
    rw [show c * (R : ℝ) = Real.exp 1 * (2 * (R : ℝ)) by
      dsimp [c]
      ring]
    rw [Real.log_mul (Real.exp_ne_zero 1) htwoR0, Real.log_exp]
  simp only [Function.comp_apply]
  rw [hlog]
  field_simp

/-- Consequently the absolute frequency mass of a single moving dyadic
block vanishes.  This remains a block statement, not yet the complete
ultra-high tail summed over all subsequent blocks. -/
theorem tendsto_h15BettinChandeeFrequencyBlockL1_zero :
    Tendsto h15BettinChandeeFrequencyBlockL1 atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun R =>
      h15BettinChandeeFrequencyBlockL1_nonneg R
  · filter_upwards [eventually_ge_atTop 1] with R hR
    exact h15BettinChandeeFrequencyBlockL1_le_explicit R hR
  · simpa using tendsto_h15FrequencyBlockSqMajorant_zero.sqrt

/-! ## Summability of the complete dyadic frequency tail -/

private abbrev H15DyadicFrequencySigma :=
  Σ j : ℕ, {r : ℕ // r ∈ h15BettinChandeeNatBlock (2 ^ j)}

private def h15DyadicFrequencySigmaToNat :
    H15DyadicFrequencySigma → ℕ := fun x => x.2.val

private theorem h15DyadicFrequencySigmaToNat_injective :
    Function.Injective h15DyadicFrequencySigmaToNat := by
  rintro ⟨j, r⟩ ⟨k, s⟩ h
  have hrval : r.val = s.val := h
  have hjlog : Nat.log2 r.val = j := by
    rw [Nat.log2_eq_log_two]
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · exact (Finset.mem_Ico.mp r.property).1
    · simpa [h15BettinChandeeNatBlock, pow_succ, Nat.mul_comm] using
        (Finset.mem_Ico.mp r.property).2
  have hklog : Nat.log2 s.val = k := by
    rw [Nat.log2_eq_log_two]
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · exact (Finset.mem_Ico.mp s.property).1
    · simpa [h15BettinChandeeNatBlock, pow_succ, Nat.mul_comm] using
        (Finset.mem_Ico.mp s.property).2
  have hjk : j = k := by
    rw [← hjlog, ← hklog, hrval]
  subst k
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext hrval))

private theorem summable_h15DyadicFrequencySigma :
    Summable (fun x : H15DyadicFrequencySigma =>
      h15BettinChandeeFrequencyCoefficient x.2.val) := by
  have hfrequency : Summable h15BettinChandeeFrequencyCoefficient := by
    simpa [h15BettinChandeeFrequencyCoefficient] using
      summable_bblsThreeHalfDirichletMajorant
  simpa [h15DyadicFrequencySigmaToNat] using
    hfrequency.comp_injective h15DyadicFrequencySigmaToNat_injective

/-- The absolute frequency masses of all positive dyadic blocks are
summable.  This is an unconditional frequency-only tail statement. -/
theorem summable_h15BettinChandeeFrequencyBlockL1_two_pow :
    Summable (fun j : ℕ =>
      h15BettinChandeeFrequencyBlockL1 (2 ^ j)) := by
  have hsigma := summable_h15DyadicFrequencySigma
  have hnonneg : ∀ x : H15DyadicFrequencySigma,
      0 ≤ h15BettinChandeeFrequencyCoefficient x.2.val := fun x =>
    h15BettinChandeeFrequencyCoefficient_nonneg x.2.val
  have hout := (summable_sigma_of_nonneg hnonneg).mp hsigma |>.2
  apply hout.congr
  intro j
  unfold h15BettinChandeeFrequencyBlockL1
  rw [tsum_fintype]
  exact Finset.sum_attach _ _

/-- The dyadic frequency tail beginning at block `J`. -/
noncomputable def h15BettinChandeeDyadicFrequencyTail (J : ℕ) : ℝ :=
  ∑' j : ℕ, h15BettinChandeeFrequencyBlockL1 (2 ^ (j + J))

/-- The complete absolute frequency-only dyadic tail tends to zero. -/
theorem tendsto_h15BettinChandeeDyadicFrequencyTail_zero :
    Tendsto h15BettinChandeeDyadicFrequencyTail atTop (nhds 0) := by
  let f : ℕ → ℝ := fun j =>
    h15BettinChandeeFrequencyBlockL1 (2 ^ j)
  have hf : Summable f :=
    summable_h15BettinChandeeFrequencyBlockL1_two_pow
  have hpartial : Tendsto (fun J : ℕ => ∑ j ∈ Finset.range J, f j)
      atTop (nhds (∑' j, f j)) := hf.hasSum.tendsto_sum_nat
  have htail : Tendsto (fun J : ℕ =>
      (∑' j, f j) - ∑ j ∈ Finset.range J, f j) atTop (nhds 0) := by
    simpa using
      (show Tendsto (fun _ : ℕ => ∑' j, f j) atTop
          (nhds (∑' j, f j)) from tendsto_const_nhds).sub hpartial
  apply htail.congr'
  filter_upwards [] with J
  rw [show h15BettinChandeeDyadicFrequencyTail J =
      ∑' j : ℕ, f (j + J) by
        unfold h15BettinChandeeDyadicFrequencyTail f
        rfl]
  have hsum := hf.sum_add_tsum_nat_add J
  linarith

end NBMellinTools.NB12
