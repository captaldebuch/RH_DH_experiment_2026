/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB5FunctionalEquationClosure
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# NB6: closure to Mathlib's global Riemann hypothesis

NB5 proves the critical-strip formulation.  This file discharges the remaining
standard bookkeeping needed for Mathlib's global `RiemannHypothesis`: zeta is
nonzero on `Re(s) ≥ 1`, the functional equation reflects points with
`Re(s) ≤ 0` that are not nonpositive integers, `ζ(0) ≠ 0`, and the negative
odd integers are nonzeros by the functional equation evaluated at positive
even integers.  The negative even integers are precisely the trivial zeros
excluded by Mathlib's definition.

The final theorem remains conditional on `NymanBeurlingCriterion`; this file
does not supply that analytic approximation statement.
-/

namespace NBMellinTools.NB6

open Complex
open NBMellinTools.NB2
open NBMellinTools.NB5

/-- Zeta is nonzero at `1 - 2k` for every positive natural number `k`.
These are exactly the negative odd integers. -/
theorem riemannZeta_one_sub_two_mul_nat_ne_zero (k : ℕ) (hk : k ≠ 0) :
    riemannZeta (1 - 2 * (k : ℂ)) ≠ 0 := by
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hnotNegNat : ∀ n : ℕ, (2 : ℂ) * k ≠ -n := by
    intro n h
    have hre := congrArg Complex.re h
    norm_num at hre
    have hn : (0 : ℝ) ≤ n := by positivity
    linarith
  have hneOne : (2 : ℂ) * k ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    have hkone : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    linarith
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [riemannZeta_one_sub hnotNegNat hneOne]
  refine mul_ne_zero ?_ ?_
  · refine mul_ne_zero ?_ ?_
    · refine mul_ne_zero ?_ ?_
      · exact mul_ne_zero two_ne_zero
          (Complex.cpow_ne_zero_iff.mpr <| Or.inl <| mul_ne_zero two_ne_zero hpi)
      · exact Gamma_ne_zero_of_re_pos (by norm_num; positivity)
    · have harg : (Real.pi : ℂ) * ((2 : ℂ) * k) / 2 =
          ((k : ℝ) * Real.pi : ℝ) := by
        push_cast
        ring
      rw [harg, ← ofReal_cos, Real.cos_nat_mul_pi]
      simp
  · apply riemannZeta_ne_zero_of_one_le_re
    norm_num
    exact_mod_cast (show 1 ≤ 2 * k by omega)

/-- A zero with nonpositive real part, other than a negative even integer, is
impossible.  This is the standard outside-the-critical-strip classification
needed to pass from NB5's formulation to Mathlib's global one. -/
theorem riemannZeta_ne_zero_of_re_nonpos_of_not_trivial
    {s : ℂ} (hsre : s.re ≤ 0)
    (htrivial : ¬∃ n : ℕ, s = -2 * (n + 1)) :
    riemannZeta s ≠ 0 := by
  by_cases hnegNat : ∃ n : ℕ, s = -n
  · obtain ⟨n, rfl⟩ := hnegNat
    rcases Nat.even_or_odd' n with ⟨k, hk | hk⟩
    · subst n
      rcases eq_or_ne k 0 with rfl | hk0
      · norm_num [riemannZeta_zero]
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
        exfalso
        apply htrivial
        exact ⟨j, by push_cast; ring⟩
    · subst n
      convert riemannZeta_one_sub_two_mul_nat_ne_zero (k + 1) (by omega) using 1
      push_cast
      ring_nf
  · intro hzeta
    have hsneOne : s ≠ 1 := by
      intro hs
      subst s
      norm_num at hsre
    have hreflected : riemannZeta (1 - s) = 0 := by
      rw [riemannZeta_one_sub (fun n hs => hnegNat ⟨n, hs⟩) hsneOne, hzeta]
      simp
    exact (riemannZeta_ne_zero_of_one_le_re (by simp; linarith)) hreflected

/-- The critical-strip formulation implies Mathlib's global
`RiemannHypothesis`. -/
theorem riemannHypothesis_of_criticalStripRiemannHypothesis
    (hstrip : CriticalStripRiemannHypothesis) :
    RiemannHypothesis := by
  intro s hzeta htrivial hsneOne
  have hsltOne : s.re < 1 := by
    by_contra h
    exact (riemannZeta_ne_zero_of_one_le_re (le_of_not_gt h)) hzeta
  have hspos : 0 < s.re := by
    by_contra h
    exact (riemannZeta_ne_zero_of_re_nonpos_of_not_trivial
      (le_of_not_gt h) htrivial) hzeta
  exact hstrip s hspos hsltOne hzeta

/-- The exact public endpoint: the finite-approximation Nyman--Beurling
criterion implies Mathlib's global Riemann hypothesis. -/
theorem riemannHypothesis_of_nymanBeurlingCriterion
    (hcriterion : NymanBeurlingCriterion) :
    RiemannHypothesis :=
  riemannHypothesis_of_criticalStripRiemannHypothesis
    (criticalStripRiemannHypothesis_of_nymanBeurlingCriterion hcriterion)

end NBMellinTools.NB6
