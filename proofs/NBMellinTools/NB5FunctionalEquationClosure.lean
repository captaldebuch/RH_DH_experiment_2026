/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB4ZeroDetection

/-!
# NB5: functional-equation closure

This file replaces the historical project assumption asserting symmetry of zeta
zeros.  Mathlib's theorem `riemannZeta_one_sub` proves the required reflection
directly on the open critical strip.  Combining that reflection with NB4's
right-half zero-free theorem shows, conditionally on the finite-approximation
Nyman--Beurling criterion, that every zeta zero in `0 < Re(s) < 1` lies on the
critical line.

The endpoint is intentionally phrased on the critical strip.  Mathlib's root
definition `RiemannHypothesis` additionally quantifies over all nontrivial
zeros using an explicit exclusion of the negative even integers; proving that
global formulation also requires a classification of zeros outside the strip.
-/

namespace NBMellinTools.NB5

open Complex
open NBMellinTools.NB2

/-- The critical-strip formulation closed by NB5. -/
def CriticalStripRiemannHypothesis : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1 / 2

/-- Zeta-zero reflection on the open critical strip, derived from Mathlib's
functional equation rather than from a project assumption. -/
theorem riemannZeta_one_sub_eq_zero_of_eq_zero
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hzeta : riemannZeta s = 0) :
    riemannZeta (1 - s) = 0 := by
  have hnegNat : ∀ n : ℕ, s ≠ -n := by
    intro n hsn
    have hre : s.re = -(n : ℝ) := by
      rw [hsn]
      norm_num
    have hn : (0 : ℝ) ≤ n := by positivity
    linarith
  have hsne1 : s ≠ 1 := by
    intro hs
    subst s
    norm_num at hs1
  rw [riemannZeta_one_sub hnegNat hsne1, hzeta]
  simp

/-- On the open critical strip, zero reflection is an equivalence. -/
theorem riemannZeta_one_sub_eq_zero_iff
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    riemannZeta (1 - s) = 0 ↔ riemannZeta s = 0 := by
  constructor
  · intro hreflected
    have hreflected0 : 0 < (1 - s).re := by
      simp only [sub_re, one_re]
      linarith
    have hreflected1 : (1 - s).re < 1 := by
      simp only [sub_re, one_re]
      linarith
    have hback := riemannZeta_one_sub_eq_zero_of_eq_zero
      hreflected0 hreflected1 hreflected
    simpa only [sub_sub_cancel] using hback
  · exact riemannZeta_one_sub_eq_zero_of_eq_zero hs0 hs1

/-- NB4's right-half theorem and zeta-zero reflection rule out zeros in the
left half of the open critical strip. -/
theorem riemannZeta_ne_zero_left_half_of_nymanBeurlingCriterion
    (hcriterion : NymanBeurlingCriterion) {s : ℂ}
    (hs0 : 0 < s.re) (hsHalf : s.re < 1 / 2) :
    riemannZeta s ≠ 0 := by
  intro hzeta
  have hreflected := riemannZeta_one_sub_eq_zero_of_eq_zero
    hs0 (by linarith) hzeta
  have hreflectedHalf : 1 / 2 < (1 - s).re := by
    simp only [sub_re, one_re]
    linarith
  have hreflectedOne : (1 - s).re < 1 := by
    simp only [sub_re, one_re]
    linarith
  exact
    (NBMellinTools.NB4.riemannZeta_ne_zero_of_nymanBeurlingCriterion
      hcriterion hreflectedHalf hreflectedOne) hreflected

/-- A generic right-half zero-free statement, together with the proved
functional-equation reflection, forces all critical-strip zeros onto the
critical line. -/
theorem criticalStripRiemannHypothesis_of_no_zeros_right_half
    (hright : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0) :
    CriticalStripRiemannHypothesis := by
  intro s hs0 hs1 hzeta
  by_contra hne
  rcases lt_or_gt_of_ne hne with hsleft | hsright
  · have hreflected := riemannZeta_one_sub_eq_zero_of_eq_zero hs0 hs1 hzeta
    have hreflectedHalf : 1 / 2 < (1 - s).re := by
      simp only [sub_re, one_re]
      linarith
    have hreflectedOne : (1 - s).re < 1 := by
      simp only [sub_re, one_re]
      linarith
    exact (hright (1 - s) hreflectedHalf hreflectedOne) hreflected
  · exact (hright s hsright hs1) hzeta

/-- NB5 closure: the finite-approximation Nyman--Beurling criterion implies
the critical-strip formulation of the Riemann hypothesis. -/
theorem criticalStripRiemannHypothesis_of_nymanBeurlingCriterion
    (hcriterion : NymanBeurlingCriterion) :
    CriticalStripRiemannHypothesis :=
  criticalStripRiemannHypothesis_of_no_zeros_right_half
    (fun _ hs0 hs1 =>
      NBMellinTools.NB4.riemannZeta_ne_zero_of_nymanBeurlingCriterion
        hcriterion hs0 hs1)

end NBMellinTools.NB5
