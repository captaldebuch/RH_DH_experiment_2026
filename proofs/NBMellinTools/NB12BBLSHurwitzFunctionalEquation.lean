/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSHurwitzLaurent

/-!
# NB12k: finite Fourier normalization and Estermann functional equation

The rational BBLS Estermann continuation is a nested `ZMod.LFunction`.
This file applies Mathlib's functional equation at both levels and performs
the finite Fourier algebra which introduces the inverse residue frequency.

The zero-frequency mode is retained explicitly.  It is the finite channel
which must later be combined with the Laurent terms and the H15 correction;
it is not discarded as part of an oscillatory estimate.

No contour shift, Kuznetsov estimate, correction matching, or signed H15
decay is claimed here.
-/

open scoped BigOperators LSeries.notation
open AddChar Complex LSeries HurwitzZeta ZMod

namespace NBMellinTools.NB12

/-! ## Finite Fourier algebra -/

/-- One Hurwitz coefficient before multiplication by the reduced numerator. -/
noncomputable def bblsEstermannHurwitzCoefficient
    {q : ℕ} [NeZero q] (s : ℂ) (j : ZMod q) : ℂ :=
  HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) s

/-- Multiplication of a Fourier frequency by the inverse of a reduced
numerator. -/
noncomputable def bblsEstermannInverseFrequency
    (a : ℕ) {q : ℕ} (haq : Nat.Coprime a q) (k : ZMod q) : ZMod q :=
  ((ZMod.unitOfCoprime a haq)⁻¹ : (ZMod q)ˣ).val * k

@[simp] theorem bblsEstermannInverseFrequency_zero
    (a : ℕ) {q : ℕ} (haq : Nat.Coprime a q) :
    bblsEstermannInverseFrequency a haq (0 : ZMod q) = 0 := by
  simp [bblsEstermannInverseFrequency]

/-- Multiplying the residue coordinate by a unit moves the DFT to the
inverse frequency. -/
theorem dft_bblsEstermannHurwitzCoefficient_mul
    (a : ℕ) {q : ℕ} [NeZero q] (haq : Nat.Coprime a q)
    (s : ℂ) (k : ZMod q) :
    ZMod.dft
        (fun j : ZMod q =>
          bblsEstermannHurwitzCoefficient s ((a : ZMod q) * j)) k =
      ZMod.dft (bblsEstermannHurwitzCoefficient (q := q) s)
        (bblsEstermannInverseFrequency a haq k) := by
  simpa [bblsEstermannInverseFrequency, ZMod.coe_unitOfCoprime] using
    (ZMod.dft_comp_unitMul
      (bblsEstermannHurwitzCoefficient (q := q) s)
      (ZMod.unitOfCoprime a haq) k)

/-- The reflected residue coordinate produces the negative inverse
frequency. -/
theorem dft_bblsEstermannHurwitzCoefficient_neg_mul
    (a : ℕ) {q : ℕ} [NeZero q] (haq : Nat.Coprime a q)
    (s : ℂ) (k : ZMod q) :
    ZMod.dft
        (fun j : ZMod q =>
          bblsEstermannHurwitzCoefficient s (-((a : ZMod q) * j))) k =
      ZMod.dft (bblsEstermannHurwitzCoefficient (q := q) s)
        (-(bblsEstermannInverseFrequency a haq k)) := by
  have hfun :
      (fun j : ZMod q =>
        bblsEstermannHurwitzCoefficient s (-((a : ZMod q) * j))) =
        fun j : ZMod q =>
          bblsEstermannHurwitzCoefficient s ((a : ZMod q) * (-j)) := by
    funext j
    congr 2
    ring
  rw [hfun]
  have hneg := congrFun
    (ZMod.dft_comp_neg
      (fun j : ZMod q =>
        bblsEstermannHurwitzCoefficient s ((a : ZMod q) * j))) k
  rw [hneg]
  simpa [bblsEstermannInverseFrequency] using
    (dft_bblsEstermannHurwitzCoefficient_mul a haq s (-k))

/-- The inner periodic coefficient at a fixed outer residue. -/
noncomputable def bblsEstermannInnerCoefficient
    (a : ℕ) {q : ℕ} [NeZero q] (j k : ZMod q) : ℂ :=
  bblsEstermannResiduePhase a j k

/-- The inner bilinear additive character has a point-mass DFT.  Mathlib's
DFT convention is `e(-xk/q)`, so the support is `k = a*j`. -/
theorem dft_bblsEstermannInnerCoefficient
    (a : ℕ) {q : ℕ} [NeZero q] (j k : ZMod q) :
    ZMod.dft (bblsEstermannInnerCoefficient a j) k =
      if k = (a : ZMod q) * j then (q : ℂ) else 0 := by
  classical
  rw [ZMod.dft_apply]
  simp only [bblsEstermannInnerCoefficient,
    bblsEstermannResiduePhase, smul_eq_mul]
  calc
    (∑ x : ZMod q,
        ZMod.stdAddChar (-(x * k)) *
          ZMod.stdAddChar ((a : ZMod q) * j * x)) =
        ∑ x : ZMod q,
          ZMod.stdAddChar (x * ((a : ZMod q) * j - k)) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← map_add_eq_mul]
      congr 1
      ring
    _ = if (a : ZMod q) * j - k = 0 then (q : ℂ) else 0 := by
      simpa using
        (AddChar.sum_mulShift ((a : ZMod q) * j - k)
          (ZMod.isPrimitive_stdAddChar q))
    _ = if k = (a : ZMod q) * j then (q : ℂ) else 0 := by
      simp only [sub_eq_zero]
      split_ifs <;> simp_all

/-- The exceptional inner zero-frequency mode is present exactly when the
outer residue is zero for a reduced numerator. -/
theorem dft_bblsEstermannInnerCoefficient_zero_of_coprime
    (a : ℕ) {q : ℕ} [NeZero q] (haq : Nat.Coprime a q)
    (j : ZMod q) :
    ZMod.dft (bblsEstermannInnerCoefficient a j) 0 =
      if j = 0 then (q : ℂ) else 0 := by
  rw [dft_bblsEstermannInnerCoefficient]
  have ha : IsUnit (a : ZMod q) :=
    (ZMod.isUnit_iff_coprime a q).2 haq
  have hz : (0 : ZMod q) = (a : ZMod q) * j ↔ j = 0 := by
    constructor
    · intro h
      apply ha.mul_right_eq_zero.mp
      exact h.symm
    · rintro rfl
      simp
  simp only [hz]

/-- Negating the input of the inner phase negates its outer frequency. -/
theorem bblsEstermannInnerCoefficient_comp_neg
    (a : ℕ) {q : ℕ} [NeZero q] (j : ZMod q) :
    (fun k => bblsEstermannInnerCoefficient a j (-k)) =
      bblsEstermannInnerCoefficient a (-j) := by
  funext k
  unfold bblsEstermannInnerCoefficient bblsEstermannResiduePhase
  apply congrArg ZMod.stdAddChar
  ring

/-- The L-function of the inner DFT is the one supported Hurwitz term. -/
theorem LFunction_dft_bblsEstermannInnerCoefficient
    (a : ℕ) {q : ℕ} [NeZero q] (j : ZMod q) (s : ℂ) :
    ZMod.LFunction (ZMod.dft (bblsEstermannInnerCoefficient a j)) s =
      (q : ℂ) ^ (-s) * (q : ℂ) *
        HurwitzZeta.hurwitzZeta
          (ZMod.toAddCircle ((a : ZMod q) * j)) s := by
  unfold ZMod.LFunction
  simp_rw [dft_bblsEstermannInnerCoefficient]
  simp
  ring

/-! ## First functional-equation level -/

/-- The inner functional equation after collapsing the point-mass DFT. -/
theorem bblsEstermannInnerLFunction_one_sub
    (a : ℕ) {q : ℕ} [NeZero q] (j : ZMod q) {s : ℂ}
    (hs : ∀ n : ℕ, s ≠ -n) (hs1 : s ≠ 1) :
    ZMod.LFunction (bblsEstermannInnerCoefficient a j) (1 - s) =
      (q : ℂ) ^ (s - 1) * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
        (Complex.exp (Real.pi * Complex.I * s / 2) *
            ((q : ℂ) ^ (-s) * (q : ℂ) *
              HurwitzZeta.hurwitzZeta
                (ZMod.toAddCircle ((a : ZMod q) * j)) s) +
          Complex.exp (-Real.pi * Complex.I * s / 2) *
            ((q : ℂ) ^ (-s) * (q : ℂ) *
              HurwitzZeta.hurwitzZeta
                (ZMod.toAddCircle (-((a : ZMod q) * j))) s)) := by
  rw [ZMod.LFunction_one_sub _ hs (Or.inr hs1)]
  rw [LFunction_dft_bblsEstermannInnerCoefficient]
  have hneg : (fun x => bblsEstermannInnerCoefficient a j (-x)) =
      bblsEstermannInnerCoefficient a (-j) :=
    bblsEstermannInnerCoefficient_comp_neg a j
  rw [hneg, LFunction_dft_bblsEstermannInnerCoefficient]
  congr 3
  congr 5
  ring

/-- The explicit value produced by the inner functional equation. -/
noncomputable def bblsEstermannInnerFunctionalValue
    (a : ℕ) {q : ℕ} [NeZero q] (s : ℂ) (j : ZMod q) : ℂ :=
  (q : ℂ) ^ (s - 1) * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
    (Complex.exp (Real.pi * Complex.I * s / 2) *
        ((q : ℂ) ^ (-s) * (q : ℂ) *
          HurwitzZeta.hurwitzZeta
            (ZMod.toAddCircle ((a : ZMod q) * j)) s) +
      Complex.exp (-Real.pi * Complex.I * s / 2) *
        ((q : ℂ) ^ (-s) * (q : ℂ) *
          HurwitzZeta.hurwitzZeta
            (ZMod.toAddCircle (-((a : ZMod q) * j))) s))

noncomputable def bblsEstermannOuterPositiveFactor
    (q : ℕ) (s : ℂ) : ℂ :=
  (q : ℂ) ^ (s - 1) * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
    Complex.exp (Real.pi * Complex.I * s / 2) *
      ((q : ℂ) ^ (-s) * (q : ℂ))

noncomputable def bblsEstermannOuterNegativeFactor
    (q : ℕ) (s : ℂ) : ℂ :=
  (q : ℂ) ^ (s - 1) * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
    Complex.exp (-Real.pi * Complex.I * s / 2) *
      ((q : ℂ) ^ (-s) * (q : ℂ))

/-- The outer DFT is the sum of the positive and negative Hurwitz transforms
at inverse residue frequencies. -/
theorem dft_bblsEstermannInnerFunctionalValue
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q)
    (s : ℂ) (k : ZMod q) :
    ZMod.dft (bblsEstermannInnerFunctionalValue (q := q) a s) k =
      bblsEstermannOuterPositiveFactor q s *
          ZMod.dft (bblsEstermannHurwitzCoefficient (q := q) s)
            (bblsEstermannInverseFrequency a haq k) +
        bblsEstermannOuterNegativeFactor q s *
          ZMod.dft (bblsEstermannHurwitzCoefficient (q := q) s)
            (-(bblsEstermannInverseFrequency a haq k)) := by
  have hfun : bblsEstermannInnerFunctionalValue (q := q) a s =
      fun j : ZMod q =>
        bblsEstermannOuterPositiveFactor q s *
            bblsEstermannHurwitzCoefficient s ((a : ZMod q) * j) +
          bblsEstermannOuterNegativeFactor q s *
            bblsEstermannHurwitzCoefficient s (-((a : ZMod q) * j)) := by
    funext j
    unfold bblsEstermannInnerFunctionalValue
      bblsEstermannOuterPositiveFactor
      bblsEstermannOuterNegativeFactor
      bblsEstermannHurwitzCoefficient
    ring
  rw [hfun]
  change ZMod.dft
      ((fun j : ZMod q => bblsEstermannOuterPositiveFactor q s *
          bblsEstermannHurwitzCoefficient s ((a : ZMod q) * j)) +
        (fun j : ZMod q => bblsEstermannOuterNegativeFactor q s *
          bblsEstermannHurwitzCoefficient s (-((a : ZMod q) * j)))) k = _
  rw [map_add]
  simp only [Pi.add_apply]
  rw [congrFun (ZMod.dft_const_mul
    (bblsEstermannOuterPositiveFactor q s)
    (fun j : ZMod q =>
      bblsEstermannHurwitzCoefficient s ((a : ZMod q) * j))) k]
  rw [congrFun (ZMod.dft_const_mul
    (bblsEstermannOuterNegativeFactor q s)
    (fun j : ZMod q =>
      bblsEstermannHurwitzCoefficient s (-((a : ZMod q) * j)))) k]
  rw [dft_bblsEstermannHurwitzCoefficient_mul a haq s k,
    dft_bblsEstermannHurwitzCoefficient_neg_mul a haq s k]

/-- The normalized dual coefficient for the outer functional equation. -/
noncomputable def bblsEstermannOuterDualCoefficient
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q)
    (s : ℂ) (k : ZMod q) : ℂ :=
  bblsEstermannOuterPositiveFactor q s *
      ZMod.dft (bblsEstermannHurwitzCoefficient (q := q) s)
        (bblsEstermannInverseFrequency a haq k) +
    bblsEstermannOuterNegativeFactor q s *
      ZMod.dft (bblsEstermannHurwitzCoefficient (q := q) s)
        (-(bblsEstermannInverseFrequency a haq k))

theorem dft_bblsEstermannInnerFunctionalValue_eq_outerDual
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q) (s : ℂ) :
    ZMod.dft (bblsEstermannInnerFunctionalValue (q := q) a s) =
      bblsEstermannOuterDualCoefficient a q haq s := by
  funext k
  exact dft_bblsEstermannInnerFunctionalValue a q haq s k

theorem dft_bblsEstermannInnerFunctionalValue_comp_neg_eq_outerDual
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q) (s : ℂ) :
    ZMod.dft
        (fun j : ZMod q =>
          bblsEstermannInnerFunctionalValue (q := q) a s (-j)) =
      fun k => bblsEstermannOuterDualCoefficient a q haq s (-k) := by
  rw [ZMod.dft_comp_neg,
    dft_bblsEstermannInnerFunctionalValue_eq_outerDual a q haq s]

/-! ## The retained zero mode -/

/-- The complete zero-frequency Hurwitz mass. -/
noncomputable def bblsEstermannHurwitzZeroMode
    (q : ℕ) [NeZero q] (s : ℂ) : ℂ :=
  ∑ j : ZMod q, bblsEstermannHurwitzCoefficient s j

theorem dft_bblsEstermannHurwitzCoefficient_zero
    (q : ℕ) [NeZero q] (s : ℂ) :
    ZMod.dft (bblsEstermannHurwitzCoefficient (q := q) s) 0 =
      bblsEstermannHurwitzZeroMode q s := by
  rw [ZMod.dft_apply_zero]
  rfl

/-- On the absolutely convergent right half-plane, the retained Hurwitz zero
mode is the untwisted zeta channel with its exact modulus factor. -/
theorem bblsEstermannHurwitzZeroMode_eq_riemannZeta
    (q : ℕ) [NeZero q] {s : ℂ} (hs : 1 < s.re) :
    bblsEstermannHurwitzZeroMode q s =
      (q : ℂ) ^ s * riemannZeta s := by
  have hL := ZMod.LFunction_eq_LSeries
    (fun _ : ZMod q => (1 : ℂ)) hs
  have hL' : ZMod.LFunction (fun _ : ZMod q => (1 : ℂ)) s =
      L (1 : ℕ → ℂ) s := by
    simpa only [Pi.one_apply] using hL
  rw [LSeries_one_eq_riemannZeta hs] at hL'
  have hzero :
      (q : ℂ) ^ (-s) * bblsEstermannHurwitzZeroMode q s =
        riemannZeta s := by
    simpa [ZMod.LFunction, bblsEstermannHurwitzZeroMode,
      bblsEstermannHurwitzCoefficient] using hL'
  rw [← hzero]
  have hq : (q : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne q)
  have hpow : (q : ℂ) ^ s * (q : ℂ) ^ (-s) = 1 := by
    rw [← Complex.cpow_add s (-s) hq]
    simp
  rw [← mul_assoc, hpow, one_mul]

/-- Exact zero-frequency part of the normalized outer dual coefficient.
This is deliberately retained for later residue/correction matching. -/
theorem bblsEstermannOuterDualCoefficient_zero
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q) (s : ℂ) :
    bblsEstermannOuterDualCoefficient a q haq s 0 =
      (bblsEstermannOuterPositiveFactor q s +
        bblsEstermannOuterNegativeFactor q s) *
          bblsEstermannHurwitzZeroMode q s := by
  unfold bblsEstermannOuterDualCoefficient
  simp only [bblsEstermannInverseFrequency_zero, neg_zero]
  rw [dft_bblsEstermannHurwitzCoefficient_zero]
  ring

/-! ## Second functional-equation level -/

/-- Pointwise replacement of each inner `LFunction (1-s)` by its explicit
Hurwitz value. -/
theorem bblsEstermannInnerLFunction_one_sub_eq_functionalValue
    (a : ℕ) {q : ℕ} [NeZero q] {s : ℂ}
    (hs : ∀ n : ℕ, s ≠ -n) (hs1 : s ≠ 1) :
    (fun j : ZMod q =>
      ZMod.LFunction (bblsEstermannInnerCoefficient a j) (1 - s)) =
        bblsEstermannInnerFunctionalValue a s := by
  funext j
  simpa [bblsEstermannInnerFunctionalValue] using
    bblsEstermannInnerLFunction_one_sub a j hs hs1

/-- The complete continuation as an outer congruence L-function. -/
noncomputable def bblsEstermannOuterCoefficient
    (a q : ℕ) [NeZero q] (s : ℂ) (j : ZMod q) : ℂ :=
  ZMod.LFunction (bblsEstermannInnerCoefficient a j) s

/-- The raw outer functional equation. -/
theorem bblsEstermannHurwitzContinuation_one_sub
    (a q : ℕ) [NeZero q] {s : ℂ}
    (hs : ∀ n : ℕ, s ≠ -n) (hs1 : s ≠ 1) :
    bblsEstermannHurwitzContinuation a q (1 - s) =
      (q : ℂ) ^ (s - 1) * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
        (Complex.exp (Real.pi * Complex.I * s / 2) *
            ZMod.LFunction
              (ZMod.dft (bblsEstermannOuterCoefficient a q (1 - s))) s +
          Complex.exp (-Real.pi * Complex.I * s / 2) *
            ZMod.LFunction
              (ZMod.dft
                (fun j => bblsEstermannOuterCoefficient a q (1 - s) (-j))) s) := by
  unfold bblsEstermannHurwitzContinuation bblsEstermannOuterCoefficient
    bblsEstermannInnerCoefficient
  exact ZMod.LFunction_one_sub _ hs (Or.inr hs1)

/-- The two-level functional equation with both inner continuations replaced
by finite Hurwitz expressions. -/
theorem bblsEstermannHurwitzContinuation_one_sub_explicit
    (a q : ℕ) [NeZero q] {s : ℂ}
    (hs : ∀ n : ℕ, s ≠ -n) (hs1 : s ≠ 1) :
    bblsEstermannHurwitzContinuation a q (1 - s) =
      (q : ℂ) ^ (s - 1) * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
        (Complex.exp (Real.pi * Complex.I * s / 2) *
            ZMod.LFunction
              (ZMod.dft
                (bblsEstermannInnerFunctionalValue (q := q) a s)) s +
          Complex.exp (-Real.pi * Complex.I * s / 2) *
            ZMod.LFunction
              (ZMod.dft
                (fun j : ZMod q =>
                  bblsEstermannInnerFunctionalValue (q := q) a s (-j))) s) := by
  rw [bblsEstermannHurwitzContinuation_one_sub a q hs hs1]
  have hcoeff :=
    bblsEstermannInnerLFunction_one_sub_eq_functionalValue
      (q := q) a hs hs1
  unfold bblsEstermannOuterCoefficient
  rw [hcoeff]
  have hneg :
      (fun j : ZMod q =>
        ZMod.LFunction (bblsEstermannInnerCoefficient a (-j)) (1 - s)) =
          fun j : ZMod q =>
            bblsEstermannInnerFunctionalValue (q := q) a s (-j) := by
    funext j
    exact congrFun hcoeff (-j)
  rw [hneg]

/-- Fully normalized two-level functional equation.  The inverse residue
frequency is explicit and the zero mode remains part of the displayed dual
coefficient. -/
theorem bblsEstermannHurwitzContinuation_one_sub_normalized
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q) {s : ℂ}
    (hs : ∀ n : ℕ, s ≠ -n) (hs1 : s ≠ 1) :
    bblsEstermannHurwitzContinuation a q (1 - s) =
      (q : ℂ) ^ (s - 1) * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
        (Complex.exp (Real.pi * Complex.I * s / 2) *
            ZMod.LFunction
              (bblsEstermannOuterDualCoefficient a q haq s) s +
          Complex.exp (-Real.pi * Complex.I * s / 2) *
            ZMod.LFunction
              (fun k : ZMod q =>
                bblsEstermannOuterDualCoefficient a q haq s (-k)) s) := by
  rw [bblsEstermannHurwitzContinuation_one_sub_explicit a q hs hs1]
  rw [dft_bblsEstermannInnerFunctionalValue_eq_outerDual a q haq s,
    dft_bblsEstermannInnerFunctionalValue_comp_neg_eq_outerDual a q haq s]

end NBMellinTools.NB12
