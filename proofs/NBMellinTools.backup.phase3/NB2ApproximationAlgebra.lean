/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.BaezDuarteTail

/-!
# Algebra of finite Báez--Duarte approximants

This is the elementary linear layer behind quadratic-form expansions of finite
Nyman--Beurling/Báez--Duarte approximants.  It is intentionally source-neutral:
it proves only identities for the project definitions and does **not** identify
this `L²(0,∞)` model with a paper's critical-line `d_N` norm.
-/

open scoped BigOperators

namespace NBMellinTools.NB2

/-- The zero coefficient vector gives the zero finite approximant. -/
theorem bdApprox_zero (N : ℕ) (x : ℝ) :
    bdApprox N (0 : Fin N → ℝ) x = 0 := by
  simp [bdApprox]

/-- Finite Báez--Duarte approximation is additive in its coefficients. -/
theorem bdApprox_add (N : ℕ) (a b : Fin N → ℝ) (x : ℝ) :
    bdApprox N (fun k => a k + b k) x =
      bdApprox N a x + bdApprox N b x := by
  simp [bdApprox, add_mul, Finset.sum_add_distrib]

/-- Finite Báez--Duarte approximation commutes with real scalar multiplication. -/
theorem bdApprox_scale (N : ℕ) (c : ℝ) (a : Fin N → ℝ) (x : ℝ) :
    bdApprox N (fun k => c * a k) x = c * bdApprox N a x := by
  simp [bdApprox, mul_assoc, Finset.mul_sum]

/-- Finite Báez--Duarte approximation respects coefficient subtraction. -/
theorem bdApprox_sub (N : ℕ) (a b : Fin N → ℝ) (x : ℝ) :
    bdApprox N (fun k => a k - b k) x =
      bdApprox N a x - bdApprox N b x := by
  simp [bdApprox, sub_mul, Finset.sum_sub_distrib]

end NBMellinTools.NB2
