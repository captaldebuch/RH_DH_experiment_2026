/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB2Mellin

/-!
# Finite Báez--Duarte approximants and their reciprocal tails

This file supplies the active-package approximation API needed by the
Mellin-continuity and zero-transport fields.  It deliberately stops at the
classical Nyman--Beurling approximation criterion; no implication to the
Riemann hypothesis is assumed here.
-/

open MeasureTheory Set
open scoped BigOperators

namespace NBMellinTools.NB2

/-- A finite real linear combination of the zero-based Báez--Duarte
generators. -/
noncomputable def bdApprox
    (N : ℕ) (coeffs : Fin N → ℝ) (x : ℝ) : ℝ :=
  ∑ k, coeffs k * rhoBD k.val x

/-- The squared `L²(0,∞)` approximation error. -/
noncomputable def BaezDuarteL2Error
    (N : ℕ) (coeffs : Fin N → ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), (chi01 x - bdApprox N coeffs x) ^ 2

theorem baezDuarteL2Error_nonneg
    (N : ℕ) (coeffs : Fin N → ℝ) :
    0 ≤ BaezDuarteL2Error N coeffs := by
  unfold BaezDuarteL2Error
  apply integral_nonneg
  intro x
  positivity

/-- The finite-approximation formulation of the Nyman--Beurling criterion.
It is kept as a proposition and is not asserted unconditionally. -/
def NymanBeurlingCriterion : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∃ coeffs : Fin N → ℝ,
      BaezDuarteL2Error N coeffs < ε

/-- Above one, every zero-based generator is exactly reciprocal. -/
theorem rhoBD_eq_one_div_of_one_lt (k : ℕ) {x : ℝ} (hx : 1 < x) :
    rhoBD k x = 1 / ((k + 1 : ℝ) * x) := by
  unfold rhoBD
  rw [Int.fract]
  have hpos : 0 < 1 / ((k + 1 : ℝ) * x) := by positivity
  have hlt : 1 / ((k + 1 : ℝ) * x) < 1 := by
    rw [div_lt_one (by positivity)]
    have hk : (1 : ℝ) ≤ (k + 1 : ℕ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    nlinarith
  rw [Int.floor_eq_zero_iff.mpr ⟨le_of_lt hpos, hlt⟩]
  norm_num

/-- A finite approximant has a single scalar reciprocal tail. -/
theorem bdApprox_eq_tail_of_one_lt
    (N : ℕ) (coeffs : Fin N → ℝ) {x : ℝ} (hx : 1 < x) :
    bdApprox N coeffs x =
      (∑ k, coeffs k / (k.val + 1 : ℝ)) / x := by
  simp_rw [bdApprox, rhoBD_eq_one_div_of_one_lt _ hx]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  field_simp

/-- The complete approximation error therefore has an exact reciprocal
tail on `(1,∞)`. -/
theorem chi_sub_bdApprox_eq_tail_of_one_lt
    (N : ℕ) (coeffs : Fin N → ℝ) {x : ℝ} (hx : 1 < x) :
    chi01 x - bdApprox N coeffs x =
      -(∑ k, coeffs k / (k.val + 1 : ℝ)) / x := by
  rw [bdApprox_eq_tail_of_one_lt N coeffs hx]
  simp [chi01, not_le_of_gt hx]
  ring

end NBMellinTools.NB2
