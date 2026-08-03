/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEFrequencyProductKernels

/-!
# NB12zzzU: correction-preserving collision Gram template

This file packages the complete-period consequence of finite additive
orthogonality.  An arbitrary finite sum of imaginary correction atoms and
real pair atoms is squared *before* any estimate.  Its energy is exactly the
sum of three collision Gram sectors:

* correction--correction (imaginary--imaginary),
* correction--pair (imaginary--real), with multiplicity two, and
* pair--pair (real--real).

The scalar coefficients are arbitrary complex numbers and remain coupled to
their frequencies.  Thus the template is suitable for the four Estermann
orientation factors and the retained missing-residue trace once those
literal H15 phases have been lifted to one common period.
-/

open AddChar Complex ZMod
open scoped BigOperators ComplexConjugate

namespace NBMellinTools.NB12

/-! ## A common-period signed system -/

noncomputable def h15PostFECommonPeriodMissingValue
    {M : ℕ} [NeZero M]
    {I : Type} (support : Finset I)
    (coefficient : I → ℂ) (frequency : I → ZMod M)
    (r : ZMod M) : ℝ :=
  ∑ i ∈ support,
    (coefficient i * ZMod.stdAddChar (r * frequency i)).im

noncomputable def h15PostFECommonPeriodPairValue
    {M : ℕ} [NeZero M]
    {K : Type} (support : Finset K)
    (coefficient : K → ℂ) (frequency : K → ZMod M)
    (r : ZMod M) : ℝ :=
  ∑ k ∈ support,
    (coefficient k * ZMod.stdAddChar (r * frequency k)).re

noncomputable def h15PostFECommonPeriodCorrectionEnergy
    {M : ℕ} [NeZero M]
    {I K : Type}
    (missingSupport : Finset I)
    (missingCoefficient : I → ℂ) (missingFrequency : I → ZMod M)
    (pairSupport : Finset K)
    (pairCoefficient : K → ℂ) (pairFrequency : K → ZMod M) : ℝ :=
  ∑ r : ZMod M,
    (h15PostFECommonPeriodMissingValue missingSupport
        missingCoefficient missingFrequency r +
      h15PostFECommonPeriodPairValue pairSupport
        pairCoefficient pairFrequency r) ^ 2

/-! ## Collision Gram sectors -/

noncomputable def h15PostFECommonPeriodMissingCollisionGram
    {M : ℕ} [NeZero M]
    {I : Type} (support : Finset I)
    (coefficient : I → ℂ) (frequency : I → ZMod M) : ℝ :=
  ∑ i ∈ support, ∑ j ∈ support,
    h15PostFEImagImagFrequencyKernel
      (coefficient i) (coefficient j) (frequency i) (frequency j)

noncomputable def h15PostFECommonPeriodMixedCollisionGram
    {M : ℕ} [NeZero M]
    {I K : Type}
    (missingSupport : Finset I)
    (missingCoefficient : I → ℂ) (missingFrequency : I → ZMod M)
    (pairSupport : Finset K)
    (pairCoefficient : K → ℂ) (pairFrequency : K → ZMod M) : ℝ :=
  ∑ i ∈ missingSupport, ∑ k ∈ pairSupport,
    h15PostFEImagRealFrequencyKernel
      (missingCoefficient i) (pairCoefficient k)
      (missingFrequency i) (pairFrequency k)

noncomputable def h15PostFECommonPeriodPairCollisionGram
    {M : ℕ} [NeZero M]
    {K : Type} (support : Finset K)
    (coefficient : K → ℂ) (frequency : K → ZMod M) : ℝ :=
  ∑ k ∈ support, ∑ l ∈ support,
    h15PostFERealRealFrequencyKernel
      (coefficient k) (coefficient l) (frequency k) (frequency l)

/-! ## Finite-sum transport -/

theorem sum_univ_biDouble_comm
    {R I K : Type} [Fintype R]
    (left : Finset I) (right : Finset K)
    (f : R → I → K → ℝ) :
    (∑ r : R, ∑ i ∈ left, ∑ k ∈ right, f r i k) =
      ∑ i ∈ left, ∑ k ∈ right, ∑ r : R, f r i k := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.sum_comm]

/-- Exact common-period energy decomposition.  In particular the correction
atoms are not removed before squaring. -/
theorem h15PostFECommonPeriodCorrectionEnergy_eq_collisionGrams
    {M : ℕ} [NeZero M]
    {I K : Type}
    (missingSupport : Finset I)
    (missingCoefficient : I → ℂ) (missingFrequency : I → ZMod M)
    (pairSupport : Finset K)
    (pairCoefficient : K → ℂ) (pairFrequency : K → ZMod M) :
    h15PostFECommonPeriodCorrectionEnergy
        missingSupport missingCoefficient missingFrequency
        pairSupport pairCoefficient pairFrequency =
      h15PostFECommonPeriodMissingCollisionGram
          missingSupport missingCoefficient missingFrequency +
        2 * h15PostFECommonPeriodMixedCollisionGram
          missingSupport missingCoefficient missingFrequency
          pairSupport pairCoefficient pairFrequency +
        h15PostFECommonPeriodPairCollisionGram
          pairSupport pairCoefficient pairFrequency := by
  unfold h15PostFECommonPeriodCorrectionEnergy
    h15PostFECommonPeriodMissingValue
    h15PostFECommonPeriodPairValue
    h15PostFECommonPeriodMissingCollisionGram
    h15PostFECommonPeriodMixedCollisionGram
    h15PostFECommonPeriodPairCollisionGram
    h15PostFEImagImagFrequencyKernel
    h15PostFEImagRealFrequencyKernel
    h15PostFERealRealFrequencyKernel
  calc
    (∑ r : ZMod M,
        ((∑ i ∈ missingSupport,
            (missingCoefficient i *
              ZMod.stdAddChar (r * missingFrequency i)).im) +
          ∑ k ∈ pairSupport,
            (pairCoefficient k *
              ZMod.stdAddChar (r * pairFrequency k)).re) ^ 2) =
        ∑ r : ZMod M,
          ((∑ i ∈ missingSupport, ∑ j ∈ missingSupport,
              (missingCoefficient i *
                  ZMod.stdAddChar (r * missingFrequency i)).im *
                (missingCoefficient j *
                  ZMod.stdAddChar (r * missingFrequency j)).im) +
            2 * (∑ i ∈ missingSupport, ∑ k ∈ pairSupport,
              (missingCoefficient i *
                  ZMod.stdAddChar (r * missingFrequency i)).im *
                (pairCoefficient k *
                  ZMod.stdAddChar (r * pairFrequency k)).re) +
            ∑ k ∈ pairSupport, ∑ l ∈ pairSupport,
              (pairCoefficient k *
                  ZMod.stdAddChar (r * pairFrequency k)).re *
                (pairCoefficient l *
                  ZMod.stdAddChar (r * pairFrequency l)).re) := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [add_sq, sq_sum_eq_double_sum, sq_sum_eq_double_sum]
      rw [mul_assoc, mul_sum_sum_eq_double_sum]
    _ =
        (∑ i ∈ missingSupport, ∑ j ∈ missingSupport,
          ∑ r : ZMod M,
            (missingCoefficient i *
                ZMod.stdAddChar (r * missingFrequency i)).im *
              (missingCoefficient j *
                ZMod.stdAddChar (r * missingFrequency j)).im) +
          2 * (∑ i ∈ missingSupport, ∑ k ∈ pairSupport,
            ∑ r : ZMod M,
              (missingCoefficient i *
                  ZMod.stdAddChar (r * missingFrequency i)).im *
                (pairCoefficient k *
                  ZMod.stdAddChar (r * pairFrequency k)).re) +
          ∑ k ∈ pairSupport, ∑ l ∈ pairSupport,
            ∑ r : ZMod M,
              (pairCoefficient k *
                  ZMod.stdAddChar (r * pairFrequency k)).re *
                (pairCoefficient l *
                  ZMod.stdAddChar (r * pairFrequency l)).re := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum]
      rw [sum_univ_biDouble_comm, sum_univ_biDouble_comm,
        sum_univ_biDouble_comm]

/-! ## Explicit collision-indicator normal form -/

theorem h15PostFECommonPeriodCorrectionEnergy_eq_collisionIndicators
    {M : ℕ} [NeZero M]
    {I K : Type}
    (missingSupport : Finset I)
    (missingCoefficient : I → ℂ) (missingFrequency : I → ZMod M)
    (pairSupport : Finset K)
    (pairCoefficient : K → ℂ) (pairFrequency : K → ZMod M) :
    h15PostFECommonPeriodCorrectionEnergy
        missingSupport missingCoefficient missingFrequency
        pairSupport pairCoefficient pairFrequency =
      (∑ i ∈ missingSupport, ∑ j ∈ missingSupport,
        (((missingCoefficient i * conj (missingCoefficient j)) *
              (if missingFrequency i = missingFrequency j
                then (M : ℂ) else 0)).re -
          ((missingCoefficient i * missingCoefficient j) *
              (if missingFrequency i + missingFrequency j = 0
                then (M : ℂ) else 0)).re) / 2) +
      2 * (∑ i ∈ missingSupport, ∑ k ∈ pairSupport,
        (((missingCoefficient i * pairCoefficient k) *
              (if missingFrequency i + pairFrequency k = 0
                then (M : ℂ) else 0)).im +
          ((missingCoefficient i * conj (pairCoefficient k)) *
              (if missingFrequency i = pairFrequency k
                then (M : ℂ) else 0)).im) / 2) +
      ∑ k ∈ pairSupport, ∑ l ∈ pairSupport,
        (((pairCoefficient k * pairCoefficient l) *
              (if pairFrequency k + pairFrequency l = 0
                then (M : ℂ) else 0)).re +
          ((pairCoefficient k * conj (pairCoefficient l)) *
              (if pairFrequency k = pairFrequency l
                then (M : ℂ) else 0)).re) / 2 := by
  rw [h15PostFECommonPeriodCorrectionEnergy_eq_collisionGrams]
  unfold h15PostFECommonPeriodMissingCollisionGram
    h15PostFECommonPeriodMixedCollisionGram
    h15PostFECommonPeriodPairCollisionGram
  simp_rw [h15PostFEImagImagFrequencyKernel_eq_collisionIndicators,
    h15PostFEImagRealFrequencyKernel_eq_collisionIndicators,
    h15PostFERealRealFrequencyKernel_eq_collisionIndicators]

end NBMellinTools.NB12
