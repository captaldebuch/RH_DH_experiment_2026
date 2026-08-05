/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FinalBoundaryShellBlockLiteratureAudit

/-!
# NB12zzn: finite inverse-coordinate completion with retained zero mode

This ports the reusable finite Fourier algebra into the active NBMellinTools
pipeline.  An arbitrary weight on reduced residues is converted exactly into
inverse-coordinate Kloosterman frequencies.  The degenerate frequency is
retained explicitly as a Ramanujan sum.

No Weil, Kuznetsov, or asymptotic estimate is asserted.
-/

open AddChar Complex ZMod
open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate

namespace NBMellinTools.NB12

/-- Classical two-frequency Kloosterman sum over units modulo `q`. -/
noncomputable def h15KloostermanSum
    {q : ℕ} [NeZero q] (n m : ZMod q) : ℂ :=
  ∑ x : (ZMod q)ˣ,
    ZMod.stdAddChar
      (n * (x : ZMod q) + m * ((x⁻¹ : (ZMod q)ˣ) : ZMod q))

/-- Fourier coefficient after inversion of the unit coordinate. -/
noncomputable def h15InverseCoordinateFourierCoefficient
    {q : ℕ} [NeZero q] (A : (ZMod q)ˣ → ℂ) (m : ZMod q) : ℂ :=
  ∑ y : (ZMod q)ˣ,
    A (y⁻¹) * ZMod.stdAddChar (-(m * (y : ZMod q)))

/-- Degenerate Kloosterman frequency, kept as the exact Ramanujan sum. -/
noncomputable def h15RamanujanSum
    {q : ℕ} [NeZero q] (n : ZMod q) : ℂ :=
  ∑ x : (ZMod q)ˣ, ZMod.stdAddChar (n * (x : ZMod q))

@[simp] theorem h15InverseCoordinateFourierCoefficient_zero
    {q : ℕ} [NeZero q] (A : (ZMod q)ˣ → ℂ) :
    h15InverseCoordinateFourierCoefficient A 0 =
      ∑ y : (ZMod q)ˣ, A (y⁻¹) := by
  classical
  unfold h15InverseCoordinateFourierCoefficient
  simp

theorem h15KloostermanSum_zero_eq_ramanujanSum
    {q : ℕ} [NeZero q] (n : ZMod q) :
    h15KloostermanSum n 0 = h15RamanujanSum n := by
  classical
  unfold h15KloostermanSum h15RamanujanSum
  apply Finset.sum_congr rfl
  intro x _hx
  simp

/-- Orthogonality forces the inverse relation `y=x⁻¹`. -/
theorem h15InverseCoordinatePhase_orthogonality
    {q : ℕ} [NeZero q] (n : ZMod q) (x y : (ZMod q)ˣ) :
    (∑ m : ZMod q,
        ZMod.stdAddChar (-(m * (y : ZMod q))) *
          ZMod.stdAddChar
            (n * (x : ZMod q) +
              m * ((x⁻¹ : (ZMod q)ˣ) : ZMod q))) =
      ZMod.stdAddChar (n * (x : ZMod q)) *
        (if y = x⁻¹ then (q : ℂ) else 0) := by
  classical
  calc
    (∑ m : ZMod q,
        ZMod.stdAddChar (-(m * (y : ZMod q))) *
          ZMod.stdAddChar
            (n * (x : ZMod q) +
              m * ((x⁻¹ : (ZMod q)ˣ) : ZMod q))) =
      ZMod.stdAddChar (n * (x : ZMod q)) *
        ∑ m : ZMod q,
          ZMod.stdAddChar
            (m * (((x⁻¹ : (ZMod q)ˣ) : ZMod q) - (y : ZMod q))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _hm
      rw [← map_add_eq_mul, ← map_add_eq_mul]
      apply congrArg ZMod.stdAddChar
      ring
    _ = ZMod.stdAddChar (n * (x : ZMod q)) *
        (if (((x⁻¹ : (ZMod q)ˣ) : ZMod q) - (y : ZMod q)) = 0
          then (q : ℂ) else 0) := by
      rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q)]
      simp only [ZMod.card, Nat.cast_ite, Nat.cast_zero]
    _ = ZMod.stdAddChar (n * (x : ZMod q)) *
        (if y = x⁻¹ then (q : ℂ) else 0) := by
      have hiff :
          (((x⁻¹ : (ZMod q)ˣ) : ZMod q) - (y : ZMod q)) = 0 ↔
            y = x⁻¹ := by
        constructor
        · intro hzero
          apply Units.ext
          exact (sub_eq_zero.mp hzero).symm
        · intro hunit
          apply sub_eq_zero.mpr
          exact congrArg Units.val hunit.symm
      simp only [hiff]

/-- Scaled completion identity before division by the modulus. -/
theorem sum_h15InverseFourierCoefficient_mul_kloostermanSum
    {q : ℕ} [NeZero q] (A : (ZMod q)ˣ → ℂ) (n : ZMod q) :
    (∑ m : ZMod q,
        h15InverseCoordinateFourierCoefficient A m *
          h15KloostermanSum n m) =
      (q : ℂ) *
        ∑ x : (ZMod q)ˣ,
          A x * ZMod.stdAddChar (n * (x : ZMod q)) := by
  classical
  unfold h15InverseCoordinateFourierCoefficient h15KloostermanSum
  calc
    (∑ m : ZMod q,
        (∑ y : (ZMod q)ˣ,
          A (y⁻¹) * ZMod.stdAddChar (-(m * (y : ZMod q)))) *
        ∑ x : (ZMod q)ˣ,
          ZMod.stdAddChar
            (n * (x : ZMod q) +
              m * ((x⁻¹ : (ZMod q)ˣ) : ZMod q))) =
      ∑ y : (ZMod q)ˣ, ∑ x : (ZMod q)ˣ,
        A (y⁻¹) *
          ∑ m : ZMod q,
            ZMod.stdAddChar (-(m * (y : ZMod q))) *
              ZMod.stdAddChar
                (n * (x : ZMod q) +
                  m * ((x⁻¹ : (ZMod q)ˣ) : ZMod q)) := by
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _hy
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _hx
      apply Finset.sum_congr rfl
      intro m _hm
      ring
    _ = ∑ y : (ZMod q)ˣ, ∑ x : (ZMod q)ˣ,
        A (y⁻¹) * ZMod.stdAddChar (n * (x : ZMod q)) *
          (if y = x⁻¹ then (q : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro y _hy
      apply Finset.sum_congr rfl
      intro x _hx
      rw [h15InverseCoordinatePhase_orthogonality]
      ring
    _ = ∑ x : (ZMod q)ˣ,
        A x * ZMod.stdAddChar (n * (x : ZMod q)) * (q : ℂ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _hx
      simp
    _ = (q : ℂ) *
        ∑ x : (ZMod q)ˣ,
          A x * ZMod.stdAddChar (n * (x : ZMod q)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      ring

/-- Divided finite completion formula. -/
theorem h15UnitAdditiveSum_eq_kloostermanCompletion
    {q : ℕ} [NeZero q] (A : (ZMod q)ˣ → ℂ) (n : ZMod q) :
    (∑ x : (ZMod q)ˣ,
        A x * ZMod.stdAddChar (n * (x : ZMod q))) =
      (q : ℂ)⁻¹ *
        ∑ m : ZMod q,
          h15InverseCoordinateFourierCoefficient A m *
            h15KloostermanSum n m := by
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  rw [sum_h15InverseFourierCoefficient_mul_kloostermanSum]
  field_simp

/-- Exact zero/nonzero decomposition.  The zero mode is never discarded. -/
theorem h15KloostermanCompletion_eq_zeroMode_add_nonzero
    {q : ℕ} [NeZero q] (A : (ZMod q)ˣ → ℂ) (n : ZMod q) :
    (∑ m : ZMod q,
        h15InverseCoordinateFourierCoefficient A m *
          h15KloostermanSum n m) =
      h15InverseCoordinateFourierCoefficient A 0 * h15RamanujanSum n +
        ∑ m ∈ (Finset.univ.erase (0 : ZMod q)),
          h15InverseCoordinateFourierCoefficient A m *
            h15KloostermanSum n m := by
  classical
  rw [← Finset.sum_erase_add Finset.univ
    (fun m : ZMod q =>
      h15InverseCoordinateFourierCoefficient A m * h15KloostermanSum n m)
    (by simp)]
  rw [h15KloostermanSum_zero_eq_ramanujanSum]
  exact add_comm _ _

/-- Fully completed direct unit sum with its correction-sensitive zero mode
and its nonzero inverse-residue sector displayed separately. -/
theorem h15UnitAdditiveSum_eq_zeroMode_add_nonzero
    {q : ℕ} [NeZero q] (A : (ZMod q)ˣ → ℂ) (n : ZMod q) :
    (∑ x : (ZMod q)ˣ,
        A x * ZMod.stdAddChar (n * (x : ZMod q))) =
      (q : ℂ)⁻¹ *
          (h15InverseCoordinateFourierCoefficient A 0 * h15RamanujanSum n) +
        (q : ℂ)⁻¹ *
          ∑ m ∈ (Finset.univ.erase (0 : ZMod q)),
            h15InverseCoordinateFourierCoefficient A m *
              h15KloostermanSum n m := by
  rw [h15UnitAdditiveSum_eq_kloostermanCompletion,
    h15KloostermanCompletion_eq_zeroMode_add_nonzero]
  ring

end NBMellinTools.NB12
