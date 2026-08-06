/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FinalBoundaryPhaseCollision

/-!
# NB12zzd: rational congruences behind endpoint phase collisions

The doubled direct phase is placed on the common modulus `q*q'`.  Equality
of phases can then be read as an ordinary natural-number congruence.  This is
the arithmetic interface needed before a quantitative near/far spacing split.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate
open Complex

namespace NBMellinTools.NB12

/-- Explicit exponential formula for the reduced doubled direct phase. -/
theorem h15DoubledDirectAdditivePhase_eq_exp
    {r u q : ℕ} [NeZero q] (hq : 0 < q) (huq : Nat.Coprime u q) :
    h15DoubledDirectAdditivePhase r u q =
      Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * ((2 * u * r : ℕ) : ℂ) / (q : ℂ)) := by
  unfold h15DoubledDirectAdditivePhase
  rw [h15DirectAdditiveReducedUnitPhase_of_coprime _ _ _ _ huq]
  unfold h15DirectAdditiveUnitPhase
  simp only [hq.ne', dite_false]
  rw [show (u : ZMod q) * (r : ZMod q) = ((u * r : ℕ) : ZMod q) by
      push_cast
      rfl]
  rw [show ZMod.stdAddChar ((u * r : ℕ) : ZMod q) =
      Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * ((u * r : ℕ) : ℂ) / (q : ℂ)) by
      simpa using ZMod.stdAddChar_coe (N := q) ((u * r : ℕ) : ℤ)]
  rw [pow_two, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- A phase of denominator `q` embeds exactly into the common denominator
`q*q'` by multiplying its numerator by `q'`. -/
theorem h15DoubledDirectAdditivePhase_eq_commonModulus
    {r u q q' : ℕ} [NeZero q] [NeZero (q * q')]
    (hq : 0 < q) (hq' : 0 < q')
    (huq : Nat.Coprime u q) :
    h15DoubledDirectAdditivePhase r u q =
      ZMod.stdAddChar
        (((2 * u * r * q' : ℕ) : ZMod (q * q'))) := by
  rw [h15DoubledDirectAdditivePhase_eq_exp hq huq]
  rw [show ZMod.stdAddChar (((2 * u * r * q' : ℕ) : ZMod (q * q'))) =
      Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I *
          ((2 * u * r * q' : ℕ) : ℂ) / ((q * q' : ℕ) : ℂ)) by
      simpa using ZMod.stdAddChar_coe (N := q * q')
        ((2 * u * r * q' : ℕ) : ℤ)]
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hq'C : (q' : ℂ) ≠ 0 := by exact_mod_cast hq'.ne'
  congr 1
  push_cast
  field_simp [hqC, hq'C]

/-- Difference-frequency phase equality is exactly a congruence on the
common modulus. -/
theorem h15DoubledDirectAdditivePhase_eq_iff_modEq
    {r u q v q' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (huq : Nat.Coprime u q) (hvq' : Nat.Coprime v q') :
    h15DoubledDirectAdditivePhase r u q =
        h15DoubledDirectAdditivePhase r v q' ↔
      2 * u * r * q' ≡ 2 * v * r * q [MOD q * q'] := by
  letI : NeZero q := ⟨hq.ne'⟩
  letI : NeZero q' := ⟨hq'.ne'⟩
  letI : NeZero (q * q') := ⟨Nat.mul_ne_zero hq.ne' hq'.ne'⟩
  letI : NeZero (q' * q) := ⟨Nat.mul_ne_zero hq'.ne' hq.ne'⟩
  rw [h15DoubledDirectAdditivePhase_eq_commonModulus hq hq' huq]
  have hsecond :
      h15DoubledDirectAdditivePhase r v q' =
        ZMod.stdAddChar
          (((2 * v * r * q : ℕ) : ZMod (q * q'))) := by
    rw [h15DoubledDirectAdditivePhase_eq_exp hq' hvq']
    rw [show ZMod.stdAddChar (((2 * v * r * q : ℕ) : ZMod (q * q'))) =
        Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I *
            ((2 * v * r * q : ℕ) : ℂ) / ((q * q' : ℕ) : ℂ)) by
        simpa using ZMod.stdAddChar_coe (N := q * q')
          ((2 * v * r * q : ℕ) : ℤ)]
    have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    have hq'C : (q' : ℂ) ≠ 0 := by exact_mod_cast hq'.ne'
    congr 1
    push_cast
    field_simp [hqC, hq'C]
  rw [hsecond]
  rw [ZMod.injective_stdAddChar.eq_iff]
  exact ZMod.natCast_eq_natCast_iff _ _ _

/-! ## Collision predicates as congruences -/

theorem normSq_h15DoubledDirectAdditivePhase
    {r u q : ℕ} (hq : 0 < q) (huq : Nat.Coprime u q) :
    Complex.normSq (h15DoubledDirectAdditivePhase r u q) = 1 := by
  unfold h15DoubledDirectAdditivePhase
  rw [pow_two, Complex.normSq_mul,
    normSq_h15DirectAdditiveReducedUnitPhase_positive r u q hq huq]
  norm_num

theorem mul_conj_eq_one_iff_eq_of_normSq_one
    {z w : ℂ} (hw : Complex.normSq w = 1) :
    z * conj w = 1 ↔ z = w := by
  constructor
  · intro h
    calc
      z = z * 1 := by ring
      _ = z * (conj w * w) := by
        rw [← Complex.normSq_eq_conj_mul_self, hw]
        norm_num
      _ = (z * conj w) * w := by ring
      _ = w := by rw [h]; ring
  · rintro rfl
    rw [Complex.mul_conj, hw]
    norm_num

/-- The exact difference-collision predicate is a common-denominator
congruence. -/
theorem h15DifferenceEndpointPairCollision_iff_modEq
    {r u q v q' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (huq : Nat.Coprime u q) (hvq' : Nat.Coprime v q') :
    h15DifferenceEndpointPairCollision r u q v q' ↔
      2 * u * r * q' ≡ 2 * v * r * q [MOD q * q'] := by
  unfold h15DifferenceEndpointPairCollision
  rw [mul_conj_eq_one_iff_eq_of_normSq_one
    (normSq_h15DoubledDirectAdditivePhase hq' hvq')]
  exact h15DoubledDirectAdditivePhase_eq_iff_modEq hq hq' huq hvq'

/-- The exact sum-collision predicate is the zero congruence for the sum of
the two lifted numerators. -/
theorem h15SumEndpointPairCollision_iff_modEq_zero
    {r u q v q' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (huq : Nat.Coprime u q) (hvq' : Nat.Coprime v q') :
    h15SumEndpointPairCollision r u q v q' ↔
      2 * u * r * q' + 2 * v * r * q ≡ 0 [MOD q * q'] := by
  letI : NeZero q := ⟨hq.ne'⟩
  letI : NeZero q' := ⟨hq'.ne'⟩
  letI : NeZero (q * q') := ⟨Nat.mul_ne_zero hq.ne' hq'.ne'⟩
  unfold h15SumEndpointPairCollision
  rw [h15DoubledDirectAdditivePhase_eq_commonModulus hq hq' huq]
  have hsecond :
      h15DoubledDirectAdditivePhase r v q' =
        ZMod.stdAddChar
          (((2 * v * r * q : ℕ) : ZMod (q * q'))) := by
    rw [h15DoubledDirectAdditivePhase_eq_exp hq' hvq']
    rw [show ZMod.stdAddChar (((2 * v * r * q : ℕ) : ZMod (q * q'))) =
        Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I *
            ((2 * v * r * q : ℕ) : ℂ) / ((q * q' : ℕ) : ℂ)) by
        simpa using ZMod.stdAddChar_coe (N := q * q')
          ((2 * v * r * q : ℕ) : ℤ)]
    have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    have hq'C : (q' : ℂ) ≠ 0 := by exact_mod_cast hq'.ne'
    congr 1
    push_cast
    field_simp [hqC, hq'C]
  rw [hsecond]
  rw [← (ZMod.stdAddChar (N := q * q')).map_zero_eq_one]
  rw [← AddChar.map_add_eq_mul, ZMod.injective_stdAddChar.eq_iff]
  simpa only [Nat.cast_add, Nat.cast_zero] using
    (ZMod.natCast_eq_natCast_iff
      (2 * u * r * q' + 2 * v * r * q) 0 (q * q'))

end NBMellinTools.NB12
