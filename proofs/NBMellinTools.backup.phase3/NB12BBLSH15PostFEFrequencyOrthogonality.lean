/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEFrequencyGram

/-!
# NB12zzzS: exact finite-frequency character kernels

The correction-preserving Gram identity reduces the next algebraic layer to
finite correlations of additive characters.  This file evaluates the two
basic kernels on a complete residue period:

* the difference kernel, with a conjugate on the second character; and
* the sum kernel, with the two characters in the same orientation.

The first is supported exactly on equal frequencies.  The second is
supported exactly on opposite frequencies.  These are the collision and
anti-collision conditions that occur after expanding products of real and
imaginary parts in the missing--missing, mixed, and pair--pair Gram sectors.

No estimate is used: both evaluations are exact finite orthogonality
identities.
-/

open AddChar Complex ZMod
open scoped BigOperators ComplexConjugate

namespace NBMellinTools.NB12

/-! ## The two complete-period kernels -/

noncomputable def h15PostFEAdditiveDifferenceKernel
    {M : ℕ} [NeZero M] (x y : ZMod M) : ℂ :=
  ∑ r : ZMod M,
    ZMod.stdAddChar (r * x) * conj (ZMod.stdAddChar (r * y))

noncomputable def h15PostFEAdditiveSumKernel
    {M : ℕ} [NeZero M] (x y : ZMod M) : ℂ :=
  ∑ r : ZMod M,
    ZMod.stdAddChar (r * x) * ZMod.stdAddChar (r * y)

/-- Conjugating the second character produces the difference frequency. -/
theorem h15PostFEAdditiveDifferenceKernel_eq_characterSum
    {M : ℕ} [NeZero M] (x y : ZMod M) :
    h15PostFEAdditiveDifferenceKernel x y =
      ∑ r : ZMod M, ZMod.stdAddChar (r * (x - y)) := by
  classical
  unfold h15PostFEAdditiveDifferenceKernel
  apply Finset.sum_congr rfl
  intro r _hr
  rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
  congr 2
  ring

/-- Characters in the same orientation produce the sum frequency. -/
theorem h15PostFEAdditiveSumKernel_eq_characterSum
    {M : ℕ} [NeZero M] (x y : ZMod M) :
    h15PostFEAdditiveSumKernel x y =
      ∑ r : ZMod M, ZMod.stdAddChar (r * (x + y)) := by
  classical
  unfold h15PostFEAdditiveSumKernel
  apply Finset.sum_congr rfl
  intro r _hr
  rw [← AddChar.map_add_eq_mul]
  congr 2
  ring

/-- Exact complete-period difference orthogonality. -/
theorem h15PostFEAdditiveDifferenceKernel_eq_ite
    {M : ℕ} [NeZero M] (x y : ZMod M) :
    h15PostFEAdditiveDifferenceKernel x y =
      if x = y then (M : ℂ) else 0 := by
  rw [h15PostFEAdditiveDifferenceKernel_eq_characterSum]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar M)]
  simp only [ZMod.card, Nat.cast_ite, Nat.cast_zero, sub_eq_zero]

/-- Exact complete-period same-orientation orthogonality. -/
theorem h15PostFEAdditiveSumKernel_eq_ite
    {M : ℕ} [NeZero M] (x y : ZMod M) :
    h15PostFEAdditiveSumKernel x y =
      if x + y = 0 then (M : ℂ) else 0 := by
  rw [h15PostFEAdditiveSumKernel_eq_characterSum]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar M)]
  simp only [ZMod.card, Nat.cast_ite, Nat.cast_zero]

/-! ## Collision consequences -/

theorem h15PostFEAdditiveDifferenceKernel_of_eq
    {M : ℕ} [NeZero M] {x y : ZMod M} (hxy : x = y) :
    h15PostFEAdditiveDifferenceKernel x y = (M : ℂ) := by
  rw [h15PostFEAdditiveDifferenceKernel_eq_ite, if_pos hxy]

theorem h15PostFEAdditiveDifferenceKernel_of_ne
    {M : ℕ} [NeZero M] {x y : ZMod M} (hxy : x ≠ y) :
    h15PostFEAdditiveDifferenceKernel x y = 0 := by
  rw [h15PostFEAdditiveDifferenceKernel_eq_ite, if_neg hxy]

theorem h15PostFEAdditiveSumKernel_of_antiCollision
    {M : ℕ} [NeZero M] {x y : ZMod M} (hxy : x + y = 0) :
    h15PostFEAdditiveSumKernel x y = (M : ℂ) := by
  rw [h15PostFEAdditiveSumKernel_eq_ite, if_pos hxy]

theorem h15PostFEAdditiveSumKernel_of_no_antiCollision
    {M : ℕ} [NeZero M] {x y : ZMod M} (hxy : x + y ≠ 0) :
    h15PostFEAdditiveSumKernel x y = 0 := by
  rw [h15PostFEAdditiveSumKernel_eq_ite, if_neg hxy]

/-- The difference kernel is Hermitian; in fact its exact indicator formula
is symmetric in the two frequencies. -/
theorem h15PostFEAdditiveDifferenceKernel_comm
    {M : ℕ} [NeZero M] (x y : ZMod M) :
    h15PostFEAdditiveDifferenceKernel x y =
      h15PostFEAdditiveDifferenceKernel y x := by
  rw [h15PostFEAdditiveDifferenceKernel_eq_ite,
    h15PostFEAdditiveDifferenceKernel_eq_ite]
  simp only [eq_comm]

end NBMellinTools.NB12
