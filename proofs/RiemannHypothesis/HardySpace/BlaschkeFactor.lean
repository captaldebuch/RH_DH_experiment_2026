/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Blaschke factors on the unit disc

This file develops the elementary theory of the *Blaschke factor*

  `b_a(z) = (‖a‖ / a) * (a - z) / (1 - conj a * z)`   (`a ≠ 0`),  `b_0(z) = z`,

for `a` in the open unit disc.  These are the building blocks of Blaschke products,
which in turn provide the "inner" factor in the inner-outer factorization of a Hardy
space function.

Main results:

* `Blaschke.norm_blaschkeFactor_lt_one` : `‖b_a z‖ < 1` for `z` in the disc;
* `Blaschke.blaschkeFactor_eq_zero_iff` : `b_a z = 0 ↔ z = a` on the disc;
* `Blaschke.blaschkeFactor_zero` : `b_a 0 = ‖a‖`;
* `Blaschke.norm_one_sub_blaschkeFactor_le` : the estimate `‖1 - b_a z‖ ≤ (1-‖a‖)(1+ρ)/(1-ρ)`
  on `‖z‖ ≤ ρ`, which drives the convergence of infinite Blaschke products;
* `Blaschke.sub_eq_blaschkeFactor_mul_unit` : `z - a = b_a z * u_a z` with `u_a` analytic and
  zero-free on the disc.
-/

noncomputable section

open Metric Complex Set

namespace Blaschke

/-- The open unit disc. -/
abbrev disc : Set ℂ := Metric.ball (0 : ℂ) 1

lemma mem_disc_iff {z : ℂ} : z ∈ disc ↔ ‖z‖ < 1 := by
  simp [disc]

/-- The Blaschke factor associated with a point `a` of the unit disc. -/
def blaschkeFactor (a z : ℂ) : ℂ :=
  if a = 0 then z else ((‖a‖ : ℂ) / a) * ((a - z) / (1 - (starRingEnd ℂ) a * z))

/-- The (zero-free) unit that converts a Blaschke factor into the linear factor `z - a`. -/
def blaschkeUnit (a z : ℂ) : ℂ :=
  if a = 0 then 1 else -(a * (1 - (starRingEnd ℂ) a * z) / (‖a‖ : ℂ))

lemma denom_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    1 - (starRingEnd ℂ) a * z ≠ 0 := by
  intro h
  have h1 : (starRingEnd ℂ) a * z = 1 := by linear_combination -h
  have hnorm : ‖a‖ * ‖z‖ = 1 := by
    have := congrArg norm h1
    simpa [norm_mul] using this
  nlinarith [norm_nonneg a, norm_nonneg z]

/-- The key algebraic identity `|1 - conj a * z|² - |a - z|² = (1 - |a|²)(1 - |z|²)`. -/
lemma normSq_identity (a z : ℂ) :
    Complex.normSq (1 - (starRingEnd ℂ) a * z) - Complex.normSq (a - z)
      = (1 - Complex.normSq a) * (1 - Complex.normSq z) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
  ring

lemma norm_blaschkeFactor_lt_one {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    ‖blaschkeFactor a z‖ < 1 := by
  by_cases h : a = 0
  · simpa [blaschkeFactor, h] using hz
  · have hden : 1 - (starRingEnd ℂ) a * z ≠ 0 := denom_ne_zero ha hz
    have hane : ‖a‖ ≠ 0 := by simpa using h
    have hkey : ‖a - z‖ < ‖1 - (starRingEnd ℂ) a * z‖ := by
      have h1 : Complex.normSq (a - z) < Complex.normSq (1 - (starRingEnd ℂ) a * z) := by
        have hid := normSq_identity a z
        have hA : Complex.normSq a < 1 := by
          rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
        have hZ : Complex.normSq z < 1 := by
          rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
        nlinarith
      have h2 : ‖a - z‖ ^ 2 < ‖1 - (starRingEnd ℂ) a * z‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]; exact h1
      nlinarith [norm_nonneg (a - z), norm_nonneg (1 - (starRingEnd ℂ) a * z)]
    rw [blaschkeFactor, if_neg h, norm_mul, norm_div, norm_div]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg a)]
    rw [div_self hane, one_mul, div_lt_one (by positivity)]
    exact hkey

lemma blaschkeFactor_eq_zero_iff {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    blaschkeFactor a z = 0 ↔ z = a := by
  by_cases h : a = 0
  · simp [blaschkeFactor, h]
  · have hden : 1 - (starRingEnd ℂ) a * z ≠ 0 := denom_ne_zero ha hz
    have hane : ((‖a‖ : ℂ) / a) ≠ 0 := by
      simp [h]
    rw [blaschkeFactor, if_neg h, mul_eq_zero]
    simp only [hane, false_or, div_eq_zero_iff, hden, or_false, sub_eq_zero]
    exact eq_comm

lemma blaschkeFactor_zero (a : ℂ) : blaschkeFactor a 0 = (‖a‖ : ℂ) := by
  by_cases h : a = 0 <;> simp [blaschkeFactor, h]

/-- Blaschke factors are analytic on the unit disc. -/
lemma blaschkeFactor_analyticAt {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    AnalyticAt ℂ (blaschkeFactor a) z := by
  by_cases h : a = 0
  · subst h
    have : blaschkeFactor (0 : ℂ) = fun w => w := by
      funext w; simp [blaschkeFactor]
    rw [this]
    exact analyticAt_id
  · rw [show blaschkeFactor a
        = fun w => ((‖a‖ : ℂ) / a) * ((a - w) / (1 - (starRingEnd ℂ) a * w)) from by
      funext w; rw [blaschkeFactor, if_neg h]]
    apply AnalyticAt.mul analyticAt_const
    exact AnalyticAt.div (by fun_prop) (by fun_prop) (denom_ne_zero ha hz)

lemma blaschkeFactor_analyticOnNhd {a : ℂ} (ha : ‖a‖ < 1) :
    AnalyticOnNhd ℂ (blaschkeFactor a) disc :=
  fun _ hz => blaschkeFactor_analyticAt ha (mem_disc_iff.mp hz)

lemma blaschkeFactor_continuousOn {a : ℂ} (ha : ‖a‖ < 1) :
    ContinuousOn (blaschkeFactor a) disc :=
  (blaschkeFactor_analyticOnNhd ha).continuousOn

/-- The basic estimate driving convergence of Blaschke products. -/
lemma norm_one_sub_blaschkeFactor_le {a z : ℂ} {ρ : ℝ} (ha : ‖a‖ < 1) (hρ : ρ < 1)
    (hz : ‖z‖ ≤ ρ) :
    ‖1 - blaschkeFactor a z‖ ≤ (1 - ‖a‖) * ((1 + ρ) / (1 - ρ)) := by
  have hρ0 : 0 ≤ ρ := le_trans (norm_nonneg z) hz
  have h1ρ : 0 < 1 - ρ := by linarith
  have hzlt : ‖z‖ < 1 := lt_of_le_of_lt hz hρ
  set c : ℝ := (1 + ρ) / (1 - ρ) with hc_def
  have hc : c * (1 - ρ) = 1 + ρ := by
    rw [hc_def, div_mul_cancel₀]
    exact ne_of_gt h1ρ
  have hc0 : 0 ≤ c := by positivity
  by_cases h : a = 0
  · have hb : ‖(1 : ℂ) - z‖ ≤ 1 + ρ := by
      calc ‖(1 : ℂ) - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le _ _
        _ ≤ 1 + ρ := by simp [hz]
    subst h
    rw [show blaschkeFactor (0:ℂ) z = z from by simp [blaschkeFactor]]
    simp only [norm_zero, sub_zero, one_mul]
    have hcge : (1 + ρ) ≤ c := by nlinarith
    linarith
  · have hden : 1 - (starRingEnd ℂ) a * z ≠ 0 := denom_ne_zero ha hzlt
    have hnorm_a : (0:ℝ) < ‖a‖ := by simpa [norm_pos_iff] using h
    have hden' : 1 - z * (starRingEnd ℂ) a ≠ 0 := by rw [mul_comm]; exact hden
    have hconj : (starRingEnd ℂ) a * a = ((‖a‖ : ℂ))^2 := by
      rw [Complex.conj_mul']
    have key : 1 - blaschkeFactor a z
        = (((1 - ‖a‖ : ℝ) : ℂ) * (a + (‖a‖:ℂ) * z)) / (a * (1 - (starRingEnd ℂ) a * z)) := by
      rw [eq_div_iff (by exact mul_ne_zero h hden), blaschkeFactor, if_neg h]
      push_cast
      field_simp
      linear_combination (-z) * hconj
    have hd : (1 : ℝ) - ρ ≤ ‖1 - (starRingEnd ℂ) a * z‖ := by
      have hle : ‖(starRingEnd ℂ) a * z‖ ≤ ρ := by
        rw [norm_mul, RCLike.norm_conj]
        calc ‖a‖ * ‖z‖ ≤ 1 * ρ := by
              exact mul_le_mul ha.le hz (norm_nonneg z) zero_le_one
          _ = ρ := one_mul ρ
      have h2 : ‖(1:ℂ)‖ - ‖(starRingEnd ℂ) a * z‖ ≤ ‖1 - (starRingEnd ℂ) a * z‖ :=
        norm_sub_norm_le _ _
      simp only [norm_one] at h2
      linarith
    have hnum : ‖a + (‖a‖:ℂ) * z‖ ≤ ‖a‖ * (1 + ρ) := by
      calc ‖a + (‖a‖:ℂ) * z‖ ≤ ‖a‖ + ‖(‖a‖:ℂ) * z‖ := norm_add_le _ _
        _ = ‖a‖ + ‖a‖ * ‖z‖ := by
            simp
        _ ≤ ‖a‖ + ‖a‖ * ρ := by nlinarith
        _ = ‖a‖ * (1 + ρ) := by ring
    have hposden : 0 < ‖a‖ * ‖1 - (starRingEnd ℂ) a * z‖ := by
      have : 0 < ‖1 - (starRingEnd ℂ) a * z‖ := lt_of_lt_of_le h1ρ hd
      positivity
    rw [key, norm_div, norm_mul, norm_mul]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [ha.le] : (0:ℝ) ≤ 1 - ‖a‖)]
    rw [div_le_iff₀ hposden]
    have hcoef : 0 ≤ 1 - ‖a‖ := by linarith
    calc (1 - ‖a‖) * ‖a + (‖a‖:ℂ) * z‖
        ≤ (1 - ‖a‖) * (‖a‖ * (1 + ρ)) := by exact mul_le_mul_of_nonneg_left hnum hcoef
      _ = (1 - ‖a‖) * c * (‖a‖ * (1 - ρ)) := by rw [← hc]; ring
      _ ≤ (1 - ‖a‖) * c * (‖a‖ * ‖1 - (starRingEnd ℂ) a * z‖) := by
          have h1 : 0 ≤ (1 - ‖a‖) * c := mul_nonneg hcoef hc0
          have h2 : ‖a‖ * (1 - ρ) ≤ ‖a‖ * ‖1 - (starRingEnd ℂ) a * z‖ :=
            mul_le_mul_of_nonneg_left hd hnorm_a.le
          exact mul_le_mul_of_nonneg_left h2 h1

/-- `z - a = b_a z * u_a z` where `u_a` is zero-free and analytic on the disc. -/
lemma sub_eq_blaschkeFactor_mul_unit {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    z - a = blaschkeFactor a z * blaschkeUnit a z := by
  by_cases h : a = 0
  · subst h; simp [blaschkeFactor, blaschkeUnit]
  · have hden : 1 - (starRingEnd ℂ) a * z ≠ 0 := denom_ne_zero ha hz
    have hden' : 1 - z * (starRingEnd ℂ) a ≠ 0 := by rw [mul_comm]; exact hden
    have hnorm : ((‖a‖ : ℂ)) ≠ 0 := by
      simpa [Complex.ofReal_ne_zero, norm_ne_zero_iff] using h
    rw [blaschkeFactor, blaschkeUnit, if_neg h, if_neg h]
    field_simp
    ring

lemma blaschkeUnit_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : blaschkeUnit a z ≠ 0 := by
  by_cases h : a = 0
  · subst h; simp [blaschkeUnit]
  · have hden : 1 - (starRingEnd ℂ) a * z ≠ 0 := denom_ne_zero ha hz
    have hnorm : ((‖a‖ : ℂ)) ≠ 0 := by
      simpa [Complex.ofReal_ne_zero, norm_ne_zero_iff] using h
    intro hzero
    rw [blaschkeUnit, if_neg h] at hzero
    rcases div_eq_zero_iff.mp (neg_eq_zero.mp hzero) with h1 | h2
    · rcases mul_eq_zero.mp h1 with h3 | h4
      · exact h h3
      · exact hden h4
    · exact hnorm h2

lemma blaschkeUnit_analyticOnNhd {a : ℂ} (ha : ‖a‖ < 1) :
    AnalyticOnNhd ℂ (blaschkeUnit a) disc := by
  intro z hz
  by_cases h : a = 0
  · subst h
    have : blaschkeUnit (0 : ℂ) = fun _ => (1 : ℂ) := by
      funext w; simp [blaschkeUnit]
    rw [this]
    exact analyticAt_const
  · have hnorm : ((‖a‖ : ℂ)) ≠ 0 := by
      simpa [Complex.ofReal_ne_zero, norm_ne_zero_iff] using h
    rw [show blaschkeUnit a
        = fun w => -(a * (1 - (starRingEnd ℂ) a * w) / (‖a‖ : ℂ)) from by
      funext w; rw [blaschkeUnit, if_neg h]]
    exact AnalyticAt.neg (AnalyticAt.div (by fun_prop) analyticAt_const hnorm)

end Blaschke
