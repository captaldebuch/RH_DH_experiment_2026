/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB15OperatorAdaptation

/-!
# NB15: Oscillatory cancellation for the nonresonant block

This module contains the arithmetic input for the nonresonant estimates: the
incomplete exponential sum

  `S(m, q, B) = ∑_{b < B} e(m b / q)`

is periodic of period `q` in `b`, a complete period sums to zero as soon as
`q ∤ m`, and consequently an incomplete sum is bounded by `q` — the classical
"complete periods cancel, incomplete periods cost at most one period" bound.

The normalised average `S(m, q, B)/B` is therefore `O(q/B)`, which is the source
of the decay of the nonresonant Gram block.
-/

open scoped BigOperators
open Finset Complex

namespace NBMellinTools.NB12

/-- Incomplete exponential sum `S(m,q,B) = ∑_{b<B} e(mb/q)`. -/
noncomputable def h15ExpSum (m : ℤ) (q : ℕ) (B : ℕ) : ℂ :=
  ∑ b ∈ Finset.range B, h15Phase ((m * (b : ℤ) : ℤ) / (q : ℝ))

/-- The normalised (averaged) exponential sum. -/
noncomputable def h15NormalizedExpSum (m : ℤ) (q : ℕ) (B : ℕ) : ℂ :=
  h15ExpSum m q B / (B : ℂ)

/-- The geometric phase has period `q` in the summation variable. -/
theorem h15NonresonantGeometricPeriod (m : ℤ) (q : ℕ) (hq : 0 < q) (b : ℕ) :
    h15Phase ((m * ((b : ℤ) + (q : ℤ)) : ℤ) / (q : ℝ))
      = h15Phase ((m * (b : ℤ) : ℤ) / (q : ℝ)) := by
  have hq' : (q : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    exact ne_of_gt this
  have hsplit : ((m * ((b : ℤ) + (q : ℤ)) : ℤ) : ℝ) / (q : ℝ)
      = ((m * (b : ℤ) : ℤ) : ℝ) / (q : ℝ) + (m : ℝ) := by
    push_cast
    field_simp
  rw [hsplit, h15Phase_add, h15Phase_intCast, mul_one]

/-- The exponential sum written as a geometric series. -/
theorem h15ExpSum_eq_geom (m : ℤ) (q : ℕ) (B : ℕ) :
    h15ExpSum m q B = ∑ b ∈ Finset.range B, (h15Phase ((m : ℝ) / (q : ℝ))) ^ b := by
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [h15Phase_pow]
  congr 1
  push_cast
  ring

/-- The ratio of the geometric series is a nontrivial root of unity when `q ∤ m`. -/
theorem h15Phase_ratio_ne_one (m : ℤ) (q : ℕ) (hq : 0 < q) (hmq : ¬ ((q : ℤ) ∣ m)) :
    h15Phase ((m : ℝ) / (q : ℝ)) ≠ 1 := by
  intro h
  rw [h15Phase_eq_one_iff] at h
  obtain ⟨k, hk⟩ := h
  apply hmq
  have hq' : (q : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    exact ne_of_gt this
  have h1 : (m : ℝ) = (k : ℝ) * (q : ℝ) := by field_simp at hk; linarith [hk]
  have h2 : m = k * q := by exact_mod_cast h1
  exact ⟨k, by linarith [h2]⟩

theorem h15Phase_ratio_pow (m : ℤ) (q : ℕ) (hq : 0 < q) :
    (h15Phase ((m : ℝ) / (q : ℝ))) ^ q = 1 := by
  rw [h15Phase_pow]
  have h : (q : ℝ) * ((m : ℝ) / (q : ℝ)) = ((m : ℤ) : ℝ) := by
    have hq' : (q : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
      exact ne_of_gt this
    field_simp
  rw [h, h15Phase_intCast]

/-- A complete period of the geometric phase sums to zero exactly (`q ∤ m`). -/
theorem h15NonresonantCompletePeriodSumZero (m : ℤ) (q : ℕ) (hq : 0 < q)
    (hmq : ¬ ((q : ℤ) ∣ m)) :
    h15ExpSum m q q = 0 := by
  rw [h15ExpSum_eq_geom, geom_sum_eq (h15Phase_ratio_ne_one m q hq hmq),
    h15Phase_ratio_pow m q hq]
  simp

/-- Shifting the length of the sum by one full period does not change it. -/
theorem h15ExpSum_period_shift (m : ℤ) (q : ℕ) (hq : 0 < q) (hmq : ¬ ((q : ℤ) ∣ m))
    (B : ℕ) : h15ExpSum m q (B + q) = h15ExpSum m q B := by
  have hzero : ∑ i ∈ Finset.range q, (h15Phase ((m : ℝ) / (q : ℝ))) ^ i = 0 := by
    rw [← h15ExpSum_eq_geom]
    exact h15NonresonantCompletePeriodSumZero m q hq hmq
  rw [h15ExpSum_eq_geom, h15ExpSum_eq_geom, Finset.sum_range_add]
  have h2 : ∑ i ∈ Finset.range q, (h15Phase ((m : ℝ) / (q : ℝ))) ^ (B + i)
      = (h15Phase ((m : ℝ) / (q : ℝ))) ^ B * ∑ i ∈ Finset.range q,
        (h15Phase ((m : ℝ) / (q : ℝ))) ^ i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [pow_add]
  rw [h2, hzero, mul_zero, add_zero]

/-- Complete periods cancel, so the sum only depends on `B mod q`. -/
theorem h15NonresonantHSNormViaCompletePeriodsCancel (m : ℤ) (q : ℕ) (hq : 0 < q)
    (hmq : ¬ ((q : ℤ) ∣ m)) (B : ℕ) :
    h15ExpSum m q B = h15ExpSum m q (B % q) := by
  have shift : ∀ c : ℕ, h15ExpSum m q (B % q + q * c) = h15ExpSum m q (B % q) := by
    intro c
    induction c with
    | zero => simp
    | succ c ih =>
        have hrw : B % q + q * (c + 1) = (B % q + q * c) + q := by ring
        rw [hrw, h15ExpSum_period_shift m q hq hmq, ih]
  have hB := shift (B / q)
  rwa [Nat.mod_add_div B q] at hB

/-- Incomplete-period bound: an incomplete exponential sum costs at most one period. -/
theorem h15NonresonantIncompletePeriodBound (m : ℤ) (q : ℕ) (hq : 0 < q)
    (hmq : ¬ ((q : ℤ) ∣ m)) (B : ℕ) :
    ‖h15ExpSum m q B‖ ≤ (q : ℝ) := by
  rw [h15NonresonantHSNormViaCompletePeriodsCancel m q hq hmq B]
  have hnorm : ‖h15ExpSum m q (B % q)‖ ≤ ((B % q : ℕ) : ℝ) := by
    calc ‖h15ExpSum m q (B % q)‖
        ≤ ∑ b ∈ Finset.range (B % q), ‖h15Phase ((m * (b : ℤ) : ℤ) / (q : ℝ))‖ :=
          norm_sum_le _ _
      _ = ((B % q : ℕ) : ℝ) := by simp
  have hmod : ((B % q : ℕ) : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast (Nat.mod_lt B hq).le
  linarith

/-- Trivial bound: an exponential sum of `B` unimodular terms has norm at most `B`. -/
theorem h15ExpSum_norm_le (m : ℤ) (q : ℕ) (B : ℕ) : ‖h15ExpSum m q B‖ ≤ (B : ℝ) := by
  calc ‖h15ExpSum m q B‖
      ≤ ∑ b ∈ Finset.range B, ‖h15Phase ((m * (b : ℤ) : ℤ) / (q : ℝ))‖ := norm_sum_le _ _
    _ = (B : ℝ) := by simp

/-- Abel-summation form of the estimate: the normalised sum is `O(q/B)`. -/
theorem h15NonresonantAbelSummation (m : ℤ) (q : ℕ) (hq : 0 < q)
    (hmq : ¬ ((q : ℤ) ∣ m)) (B : ℕ) (hB : 0 < B) :
    ‖h15NormalizedExpSum m q B‖ ≤ (q : ℝ) / (B : ℝ) := by
  have hB' : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  rw [h15NormalizedExpSum, norm_div]
  rw [Complex.norm_natCast]
  gcongr
  exact h15NonresonantIncompletePeriodBound m q hq hmq B

/-- Trivial bound for the normalised sum (each term has modulus one). -/
theorem h15NormalizedExpSum_norm_le_one (m : ℤ) (q : ℕ) (B : ℕ) :
    ‖h15NormalizedExpSum m q B‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · simp [h15NormalizedExpSum, h15ExpSum]
  · have hB' : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
    rw [h15NormalizedExpSum, norm_div, Complex.norm_natCast, div_le_one hB']
    exact h15ExpSum_norm_le m q B

end NBMellinTools.NB12
