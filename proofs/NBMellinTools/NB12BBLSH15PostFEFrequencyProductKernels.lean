/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEFrequencyOrthogonality

/-!
# NB12zzzT: real/imaginary frequency-product kernels

The H15 Gram atoms are real or imaginary parts of complex additive
characters.  This file converts their complete-period products into the two
exact kernels evaluated in `NB12BBLSH15PostFEFrequencyOrthogonality`.

Consequently every such product has only two possible arithmetic supports:
equal-frequency collisions and opposite-frequency anti-collisions.  The
identities retain arbitrary complex scalar coefficients, so they apply to
the Archimedean Estermann orientation factors without separating them from
the phase.
-/

open AddChar Complex ZMod
open scoped BigOperators ComplexConjugate

namespace NBMellinTools.NB12

/-! ## Pointwise product-to-character identities -/

theorem mul_re_mul_re_eq_half_sum (z w : ℂ) :
    z.re * w.re = ((z * w).re + (z * conj w).re) / 2 := by
  simp only [Complex.mul_re, conj_re, conj_im]
  ring

theorem mul_im_mul_im_eq_half_difference (z w : ℂ) :
    z.im * w.im = ((z * conj w).re - (z * w).re) / 2 := by
  simp only [Complex.mul_re, conj_re, conj_im]
  ring

theorem mul_im_mul_re_eq_half_im_sum (z w : ℂ) :
    z.im * w.re = ((z * w).im + (z * conj w).im) / 2 := by
  simp only [Complex.mul_im, conj_re, conj_im]
  ring

/-! ## Scalar-weighted character products -/

theorem sum_weighted_additiveProducts_eq_sumKernel
    {M : ℕ} [NeZero M] (c d : ℂ) (x y : ZMod M) :
    (∑ r : ZMod M,
        (c * ZMod.stdAddChar (r * x)) *
          (d * ZMod.stdAddChar (r * y))) =
      (c * d) * h15PostFEAdditiveSumKernel x y := by
  classical
  unfold h15PostFEAdditiveSumKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  ring

theorem sum_weighted_additiveConjugateProducts_eq_differenceKernel
    {M : ℕ} [NeZero M] (c d : ℂ) (x y : ZMod M) :
    (∑ r : ZMod M,
        (c * ZMod.stdAddChar (r * x)) *
          conj (d * ZMod.stdAddChar (r * y))) =
      (c * conj d) * h15PostFEAdditiveDifferenceKernel x y := by
  classical
  unfold h15PostFEAdditiveDifferenceKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  simp only [map_mul]
  ring

/-! ## Exact complete-period real/imaginary Gram kernels -/

noncomputable def h15PostFERealRealFrequencyKernel
    {M : ℕ} [NeZero M] (c d : ℂ) (x y : ZMod M) : ℝ :=
  ∑ r : ZMod M,
    (c * ZMod.stdAddChar (r * x)).re *
      (d * ZMod.stdAddChar (r * y)).re

noncomputable def h15PostFEImagImagFrequencyKernel
    {M : ℕ} [NeZero M] (c d : ℂ) (x y : ZMod M) : ℝ :=
  ∑ r : ZMod M,
    (c * ZMod.stdAddChar (r * x)).im *
      (d * ZMod.stdAddChar (r * y)).im

noncomputable def h15PostFEImagRealFrequencyKernel
    {M : ℕ} [NeZero M] (c d : ℂ) (x y : ZMod M) : ℝ :=
  ∑ r : ZMod M,
    (c * ZMod.stdAddChar (r * x)).im *
      (d * ZMod.stdAddChar (r * y)).re

theorem h15PostFERealRealFrequencyKernel_eq_sum_difference
    {M : ℕ} [NeZero M] (c d : ℂ) (x y : ZMod M) :
    h15PostFERealRealFrequencyKernel c d x y =
      (((c * d) * h15PostFEAdditiveSumKernel x y).re +
        ((c * conj d) * h15PostFEAdditiveDifferenceKernel x y).re) / 2 := by
  classical
  unfold h15PostFERealRealFrequencyKernel
  simp_rw [mul_re_mul_re_eq_half_sum]
  rw [← Finset.sum_div, Finset.sum_add_distrib,
    ← Complex.re_sum, ← Complex.re_sum,
    sum_weighted_additiveProducts_eq_sumKernel,
    sum_weighted_additiveConjugateProducts_eq_differenceKernel]

theorem h15PostFEImagImagFrequencyKernel_eq_difference_sub_sum
    {M : ℕ} [NeZero M] (c d : ℂ) (x y : ZMod M) :
    h15PostFEImagImagFrequencyKernel c d x y =
      (((c * conj d) * h15PostFEAdditiveDifferenceKernel x y).re -
        ((c * d) * h15PostFEAdditiveSumKernel x y).re) / 2 := by
  classical
  unfold h15PostFEImagImagFrequencyKernel
  simp_rw [mul_im_mul_im_eq_half_difference]
  rw [← Finset.sum_div, Finset.sum_sub_distrib,
    ← Complex.re_sum, ← Complex.re_sum,
    sum_weighted_additiveConjugateProducts_eq_differenceKernel,
    sum_weighted_additiveProducts_eq_sumKernel]

theorem h15PostFEImagRealFrequencyKernel_eq_sum_difference
    {M : ℕ} [NeZero M] (c d : ℂ) (x y : ZMod M) :
    h15PostFEImagRealFrequencyKernel c d x y =
      (((c * d) * h15PostFEAdditiveSumKernel x y).im +
        ((c * conj d) * h15PostFEAdditiveDifferenceKernel x y).im) / 2 := by
  classical
  unfold h15PostFEImagRealFrequencyKernel
  simp_rw [mul_im_mul_re_eq_half_im_sum]
  rw [← Finset.sum_div, Finset.sum_add_distrib,
    ← Complex.im_sum, ← Complex.im_sum,
    sum_weighted_additiveProducts_eq_sumKernel,
    sum_weighted_additiveConjugateProducts_eq_differenceKernel]

/-! ## Explicit collision-indicator forms -/

theorem h15PostFERealRealFrequencyKernel_eq_collisionIndicators
    {M : ℕ} [NeZero M] (c d : ℂ) (x y : ZMod M) :
    h15PostFERealRealFrequencyKernel c d x y =
      (((c * d) * (if x + y = 0 then (M : ℂ) else 0)).re +
        ((c * conj d) * (if x = y then (M : ℂ) else 0)).re) / 2 := by
  rw [h15PostFERealRealFrequencyKernel_eq_sum_difference,
    h15PostFEAdditiveSumKernel_eq_ite,
    h15PostFEAdditiveDifferenceKernel_eq_ite]

theorem h15PostFEImagImagFrequencyKernel_eq_collisionIndicators
    {M : ℕ} [NeZero M] (c d : ℂ) (x y : ZMod M) :
    h15PostFEImagImagFrequencyKernel c d x y =
      (((c * conj d) * (if x = y then (M : ℂ) else 0)).re -
        ((c * d) * (if x + y = 0 then (M : ℂ) else 0)).re) / 2 := by
  rw [h15PostFEImagImagFrequencyKernel_eq_difference_sub_sum,
    h15PostFEAdditiveDifferenceKernel_eq_ite,
    h15PostFEAdditiveSumKernel_eq_ite]

theorem h15PostFEImagRealFrequencyKernel_eq_collisionIndicators
    {M : ℕ} [NeZero M] (c d : ℂ) (x y : ZMod M) :
    h15PostFEImagRealFrequencyKernel c d x y =
      (((c * d) * (if x + y = 0 then (M : ℂ) else 0)).im +
        ((c * conj d) * (if x = y then (M : ℂ) else 0)).im) / 2 := by
  rw [h15PostFEImagRealFrequencyKernel_eq_sum_difference,
    h15PostFEAdditiveSumKernel_eq_ite,
    h15PostFEAdditiveDifferenceKernel_eq_ite]

end NBMellinTools.NB12
