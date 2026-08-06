/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFESignedMissingPairNativeCongruences

/-!
# NB12zzzaQ: external missing--pair congruence shells

The incident missing--pair sector collapses to the product modulus `q*q'`.
For an external missing modulus `p`, that collapse is unavailable.  The
minimal common modulus is

`L = lcm p (q*q')`.

This file identifies the two lift multipliers exactly as

* `(q*q') / gcd p (q*q')` for the missing atom, and
* `p / gcd p (q*q')` for the oriented pair.

They are coprime.  Equal- and opposite-frequency collisions are then exposed
as two named natural congruence shells at `L` and instantiated on the actual
reduced H15 support.  No shell count or asymptotic cancellation estimate is
claimed.
-/

namespace NBMellinTools.NB12

/-! ## Arithmetic of the minimal common modulus -/

theorem h15PostFELcm_div_left_eq_right_div_gcd
    (a b : ℕ) (ha : 0 < a) :
    Nat.lcm a b / a = b / Nat.gcd a b := by
  apply (Nat.div_eq_iff_eq_mul_left ha (Nat.dvd_lcm_left a b)).mpr
  apply Nat.eq_of_mul_eq_mul_left (Nat.gcd_pos_of_pos_left b ha)
  rw [Nat.gcd_mul_lcm]
  rw [← mul_assoc, Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)]
  ring

theorem h15PostFELcm_div_right_eq_left_div_gcd
    (a b : ℕ) (hb : 0 < b) :
    Nat.lcm a b / b = a / Nat.gcd a b := by
  rw [Nat.lcm_comm, Nat.gcd_comm]
  exact h15PostFELcm_div_left_eq_right_div_gcd b a hb

def h15PostFEExternalMissingMultiplier (p q q' : ℕ) : ℕ :=
  Nat.lcm p (q * q') / p

def h15PostFEExternalPairMultiplier (p q q' : ℕ) : ℕ :=
  Nat.lcm p (q * q') / (q * q')

theorem h15PostFEExternalMissingMultiplier_eq_div_gcd
    (p q q' : ℕ) (hp : 0 < p) :
    h15PostFEExternalMissingMultiplier p q q' =
      q * q' / Nat.gcd p (q * q') := by
  exact h15PostFELcm_div_left_eq_right_div_gcd
    p (q * q') hp

theorem h15PostFEExternalPairMultiplier_eq_div_gcd
    (p q q' : ℕ) (hq : 0 < q) (hq' : 0 < q') :
    h15PostFEExternalPairMultiplier p q q' =
      p / Nat.gcd p (q * q') := by
  exact h15PostFELcm_div_right_eq_left_div_gcd
    p (q * q') (Nat.mul_pos hq hq')

theorem h15PostFEExternalMultipliers_coprime
    (p q q' : ℕ) (hp : 0 < p) (hq : 0 < q) (hq' : 0 < q') :
    Nat.Coprime
      (h15PostFEExternalPairMultiplier p q q')
      (h15PostFEExternalMissingMultiplier p q q') := by
  rw [h15PostFEExternalPairMultiplier_eq_div_gcd p q q' hq hq',
    h15PostFEExternalMissingMultiplier_eq_div_gcd p q q' hp]
  exact Nat.coprime_div_gcd_div_gcd
    (Nat.gcd_pos_of_pos_left (q * q') hp)

/-! ## The two external collision shells -/

def h15PostFEExternalMissingPairEqualShell
    (left right : BettinChandeeUnitSign)
    (w p u q v q' : ℕ) : Prop :=
  h15PostFEMissingNativeResidue ⟨p, w⟩ *
      h15PostFEExternalMissingMultiplier p q q' ≡
    h15PostFESignedPairNativeResidue left right u q v q' *
      h15PostFEExternalPairMultiplier p q q'
        [MOD Nat.lcm p (q * q')]

def h15PostFEExternalMissingPairOppositeShell
    (left right : BettinChandeeUnitSign)
    (w p u q v q' : ℕ) : Prop :=
  Nat.lcm p (q * q') ∣
    h15PostFEMissingNativeResidue ⟨p, w⟩ *
        h15PostFEExternalMissingMultiplier p q q' +
      h15PostFESignedPairNativeResidue left right u q v q' *
        h15PostFEExternalPairMultiplier p q q'

def h15PostFEIsExternalMissingPairModulus (p q q' : ℕ) : Prop :=
  p ≠ q ∧ p ≠ q'

theorem h15PostFEExternalMissingPairShells_iff_collision
    (left right : BettinChandeeUnitSign)
    (w p u q v q' : ℕ) (hp : 0 < p) (hq : 0 < q) (hq' : 0 < q') :
    h15PostFEExternalMissingPairEqualShell left right w p u q v q' ∨
        h15PostFEExternalMissingPairOppositeShell left right w p u q v q' ↔
      letI : NeZero (Nat.lcm p (q * q')) :=
        ⟨(Nat.lcm_pos hp (Nat.mul_pos hq hq')).ne'⟩
      h15PostFEFrequencyCollides
        ((h15PostFEMissingNativeResidue ⟨p, w⟩ *
          h15PostFEExternalMissingMultiplier p q q' : ℕ) :
            ZMod (Nat.lcm p (q * q')))
        ((h15PostFESignedPairNativeResidue left right u q v q' *
          h15PostFEExternalPairMultiplier p q q' : ℕ) :
            ZMod (Nat.lcm p (q * q'))) := by
  letI : NeZero (Nat.lcm p (q * q')) :=
    ⟨(Nat.lcm_pos hp (Nat.mul_pos hq hq')).ne'⟩
  rw [h15PostFEFrequencyCollides_natCast_iff]
  rfl

/-! ## Actual reduced-support instantiation -/

theorem h15PostFEActualMissingPairCollides_iff_externalShells
    {n g U Q w p u q v q' : ℕ}
    {left right : BettinChandeeUnitSign}
    (hQ : 0 < Q)
    (hi : (⟨p, w⟩ : H15PostFEMissingAtomIndex) ∈
      h15PostFEJointMissingAtomSupport
        (h15PostFEResidueModulusSupport n g U Q)
        (h15PostFEReducedMissingResidues n g U Q))
    (hx : ((((u, q), (v, q')), (left, right)) :
        H15PostFEOrientedPairAtomIndex) ∈
      h15PostFEActualOrientedPairSupport n g U Q) :
    letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
      ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
    h15PostFEFrequencyCollides
        (h15PostFELiftedMissingFrequency
          (h15PostFEActualCommonSuperperiod n g U Q) ⟨p, w⟩)
        (h15PostFELiftedPairFrequency
          (h15PostFEActualCommonSuperperiod n g U Q)
          left right ((u, q), (v, q'))) ↔
      h15PostFEExternalMissingPairEqualShell left right w p u q v q' ∨
        h15PostFEExternalMissingPairOppositeShell left right w p u q v q' := by
  let M := h15PostFEActualCommonSuperperiod n g U Q
  letI : NeZero M :=
    ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
  have hnative :=
    h15PostFEActualMissingPairCollides_iff_nativeLcm hQ hi hx
  dsimp only [h15PostFEExternalMissingMultiplier,
    h15PostFEExternalPairMultiplier,
    h15PostFEExternalMissingPairEqualShell,
    h15PostFEExternalMissingPairOppositeShell] at hnative ⊢
  exact hnative

theorem h15PostFEActualExternalMissingPairCollides_iff_shells
    {n g U Q w p u q v q' : ℕ}
    {left right : BettinChandeeUnitSign}
    (hQ : 0 < Q)
    (hi : (⟨p, w⟩ : H15PostFEMissingAtomIndex) ∈
      h15PostFEJointMissingAtomSupport
        (h15PostFEResidueModulusSupport n g U Q)
        (h15PostFEReducedMissingResidues n g U Q))
    (hx : ((((u, q), (v, q')), (left, right)) :
        H15PostFEOrientedPairAtomIndex) ∈
      h15PostFEActualOrientedPairSupport n g U Q)
    (_hexternal : h15PostFEIsExternalMissingPairModulus p q q') :
    letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
      ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
    h15PostFEFrequencyCollides
        (h15PostFELiftedMissingFrequency
          (h15PostFEActualCommonSuperperiod n g U Q) ⟨p, w⟩)
        (h15PostFELiftedPairFrequency
          (h15PostFEActualCommonSuperperiod n g U Q)
          left right ((u, q), (v, q'))) ↔
      h15PostFEExternalMissingPairEqualShell left right w p u q v q' ∨
        h15PostFEExternalMissingPairOppositeShell left right w p u q v q' :=
  h15PostFEActualMissingPairCollides_iff_externalShells hQ hi hx

end NBMellinTools.NB12
