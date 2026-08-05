/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFENativeCollisionDiophantineAudit

/-!
# NB12zzzaP: signed missing--pair native congruences

This file expands the four orientation choices in a collision between a
doubled missing frequency and an oriented-pair frequency.  The missing atom is
first placed at the left endpoint and then at the right endpoint.  Every
collision becomes one of four explicit pairs of congruences in `ZMod (q*q')`.

Endpoint incidence is therefore only an index relation: it does not by itself
force a collision.  The appropriate signed Diophantine congruence must still
hold.  No orientation, alias, or cross-modulus family is discarded.
-/

namespace NBMellinTools.NB12

/-! ## Native representatives in the product modulus -/

theorem h15PostFELeftMissingNative_cast_eq_doubled
    (u q q' : ℕ) [NeZero (q * q')] :
    ((h15PostFEMissingNativeResidue ⟨q, u⟩ * q' : ℕ) :
        ZMod (q * q')) =
      ((2 * u * q' : ℕ) : ZMod (q * q')) := by
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mpr
  have h : h15PostFEMissingNativeResidue ⟨q, u⟩ ≡ 2 * u [MOD q] := by
    simp [h15PostFEMissingNativeResidue, Nat.ModEq]
  exact h.mul_right' q'

theorem h15PostFERightMissingNative_cast_eq_doubled
    (v q q' : ℕ) [NeZero (q * q')] :
    ((h15PostFEMissingNativeResidue ⟨q', v⟩ * q : ℕ) :
        ZMod (q * q')) =
      ((2 * v * q : ℕ) : ZMod (q * q')) := by
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mpr
  have h : h15PostFEMissingNativeResidue ⟨q', v⟩ ≡ 2 * v [MOD q'] := by
    simp [h15PostFEMissingNativeResidue, Nat.ModEq]
  simpa only [mul_comm q' q] using h.mul_right' q

theorem h15PostFESignedPairNative_cast_eq_baseFrequency
    (left right : BettinChandeeUnitSign)
    (u q v q' : ℕ) [NeZero (q * q')] :
    ((h15PostFESignedPairNativeResidue left right u q v q' : ℕ) :
        ZMod (q * q')) =
      h15PostFECommonPairBaseFrequency left right u q v q' := by
  rw [← h15PostFECommonPairBaseFrequency_val_eq_signedNativeResidue]
  exact ZMod.natCast_zmod_val _

/-! ## Endpoint incidence collapses the native `lcm` -/

/-- If the missing atom is the left endpoint of the pair, then the native
`lcm` condition is exactly the product-modulus collision condition. -/
theorem h15PostFELeftEndpointNativeLcmCondition_iff
    (left right : BettinChandeeUnitSign)
    (u q v q' : ℕ) (hq : 0 < q) (hq' : 0 < q') :
    (h15PostFEMissingNativeResidue ⟨q, u⟩ *
          (Nat.lcm q (q * q') / q) ≡
        h15PostFESignedPairNativeResidue left right u q v q' *
          (Nat.lcm q (q * q') / (q * q'))
            [MOD Nat.lcm q (q * q')] ∨
      Nat.lcm q (q * q') ∣
        h15PostFEMissingNativeResidue ⟨q, u⟩ *
            (Nat.lcm q (q * q') / q) +
          h15PostFESignedPairNativeResidue left right u q v q' *
            (Nat.lcm q (q * q') / (q * q'))) ↔
      letI : NeZero (q * q') := ⟨(Nat.mul_pos hq hq').ne'⟩
      h15PostFEFrequencyCollides
        ((2 * u * q' : ℕ) : ZMod (q * q'))
        (h15PostFECommonPairBaseFrequency left right u q v q') := by
  letI : NeZero (q * q') := ⟨(Nat.mul_pos hq hq').ne'⟩
  have hlcm : Nat.lcm q (q * q') = q * q' :=
    Nat.lcm_eq_right_iff_dvd.mpr (dvd_mul_right q q')
  have hleft : q * q' / q = q' := by
    rw [mul_comm]
    exact Nat.mul_div_left q' hq
  rw [hlcm, hleft, Nat.div_self (Nat.mul_pos hq hq')]
  simp only [mul_one]
  rw [← h15PostFEFrequencyCollides_natCast_iff]
  rw [h15PostFELeftMissingNative_cast_eq_doubled,
    h15PostFESignedPairNative_cast_eq_baseFrequency]

/-- If the missing atom is the right endpoint of the pair, then the native
`lcm` condition is again exactly the product-modulus collision condition. -/
theorem h15PostFERightEndpointNativeLcmCondition_iff
    (left right : BettinChandeeUnitSign)
    (u q v q' : ℕ) (hq : 0 < q) (hq' : 0 < q') :
    (h15PostFEMissingNativeResidue ⟨q', v⟩ *
          (Nat.lcm q' (q * q') / q') ≡
        h15PostFESignedPairNativeResidue left right u q v q' *
          (Nat.lcm q' (q * q') / (q * q'))
            [MOD Nat.lcm q' (q * q')] ∨
      Nat.lcm q' (q * q') ∣
        h15PostFEMissingNativeResidue ⟨q', v⟩ *
            (Nat.lcm q' (q * q') / q') +
          h15PostFESignedPairNativeResidue left right u q v q' *
            (Nat.lcm q' (q * q') / (q * q'))) ↔
      letI : NeZero (q * q') := ⟨(Nat.mul_pos hq hq').ne'⟩
      h15PostFEFrequencyCollides
        ((2 * v * q : ℕ) : ZMod (q * q'))
        (h15PostFECommonPairBaseFrequency left right u q v q') := by
  letI : NeZero (q * q') := ⟨(Nat.mul_pos hq hq').ne'⟩
  have hlcm : Nat.lcm q' (q * q') = q * q' :=
    Nat.lcm_eq_right_iff_dvd.mpr (dvd_mul_of_dvd_right dvd_rfl q)
  have hright : q * q' / q' = q := Nat.mul_div_left q hq'
  rw [hlcm, hright, Nat.div_self (Nat.mul_pos hq hq')]
  simp only [mul_one]
  rw [← h15PostFEFrequencyCollides_natCast_iff]
  rw [h15PostFERightMissingNative_cast_eq_doubled,
    h15PostFESignedPairNative_cast_eq_baseFrequency]

/-! ## Actual reduced-support bridges -/

/-- On the actual reduced H15 support, a missing atom incident to the left
endpoint of an oriented pair collides precisely when its product-modulus
frequency does.  Incidence alone supplies no collision. -/
theorem h15PostFEActualLeftEndpointMissingPairCollides_iff_product
    {n g U Q u q v q' : ℕ}
    {left right : BettinChandeeUnitSign}
    (hQ : 0 < Q)
    (hi : (⟨q, u⟩ : H15PostFEMissingAtomIndex) ∈
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
          (h15PostFEActualCommonSuperperiod n g U Q) ⟨q, u⟩)
        (h15PostFELiftedPairFrequency
          (h15PostFEActualCommonSuperperiod n g U Q)
          left right ((u, q), (v, q'))) ↔
      letI : NeZero (q * q') := by
        have hx' := Finset.mem_product.mp hx
        have hraw := h15PostFEReducedOrderedPairResidueSupport_subset
          n g U Q hx'.1
        have hactual := h15PostFEOrderedPairResidueSupport_subset_actual hraw
        exact ⟨Nat.mul_ne_zero
          (Nat.ne_of_gt (Nat.zero_lt_of_lt
            (h15PostFEResidueKey_fst_lt_snd hQ hactual.1)))
          (Nat.ne_of_gt (Nat.zero_lt_of_lt
            (h15PostFEResidueKey_fst_lt_snd hQ hactual.2)))⟩
      h15PostFEFrequencyCollides
        ((2 * u * q' : ℕ) : ZMod (q * q'))
        (h15PostFECommonPairBaseFrequency left right u q v q') := by
  let M := h15PostFEActualCommonSuperperiod n g U Q
  letI : NeZero M :=
    ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
  have hx' := Finset.mem_product.mp hx
  have hraw := h15PostFEReducedOrderedPairResidueSupport_subset
    n g U Q hx'.1
  have hactual := h15PostFEOrderedPairResidueSupport_subset_actual hraw
  have hq : 0 < q :=
    Nat.zero_lt_of_lt (h15PostFEResidueKey_fst_lt_snd hQ hactual.1)
  have hq' : 0 < q' :=
    Nat.zero_lt_of_lt (h15PostFEResidueKey_fst_lt_snd hQ hactual.2)
  have hnative :=
    h15PostFEActualMissingPairCollides_iff_nativeLcm hQ hi hx
  dsimp only at hnative
  exact hnative.trans (h15PostFELeftEndpointNativeLcmCondition_iff
    left right u q v q' hq hq')

/-- The corresponding actual-support bridge for a missing atom incident to
the right endpoint. -/
theorem h15PostFEActualRightEndpointMissingPairCollides_iff_product
    {n g U Q u q v q' : ℕ}
    {left right : BettinChandeeUnitSign}
    (hQ : 0 < Q)
    (hi : (⟨q', v⟩ : H15PostFEMissingAtomIndex) ∈
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
          (h15PostFEActualCommonSuperperiod n g U Q) ⟨q', v⟩)
        (h15PostFELiftedPairFrequency
          (h15PostFEActualCommonSuperperiod n g U Q)
          left right ((u, q), (v, q'))) ↔
      letI : NeZero (q * q') := by
        have hx' := Finset.mem_product.mp hx
        have hraw := h15PostFEReducedOrderedPairResidueSupport_subset
          n g U Q hx'.1
        have hactual := h15PostFEOrderedPairResidueSupport_subset_actual hraw
        exact ⟨Nat.mul_ne_zero
          (Nat.ne_of_gt (Nat.zero_lt_of_lt
            (h15PostFEResidueKey_fst_lt_snd hQ hactual.1)))
          (Nat.ne_of_gt (Nat.zero_lt_of_lt
            (h15PostFEResidueKey_fst_lt_snd hQ hactual.2)))⟩
      h15PostFEFrequencyCollides
        ((2 * v * q : ℕ) : ZMod (q * q'))
        (h15PostFECommonPairBaseFrequency left right u q v q') := by
  let M := h15PostFEActualCommonSuperperiod n g U Q
  letI : NeZero M :=
    ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
  have hx' := Finset.mem_product.mp hx
  have hraw := h15PostFEReducedOrderedPairResidueSupport_subset
    n g U Q hx'.1
  have hactual := h15PostFEOrderedPairResidueSupport_subset_actual hraw
  have hq : 0 < q :=
    Nat.zero_lt_of_lt (h15PostFEResidueKey_fst_lt_snd hQ hactual.1)
  have hq' : 0 < q' :=
    Nat.zero_lt_of_lt (h15PostFEResidueKey_fst_lt_snd hQ hactual.2)
  have hnative :=
    h15PostFEActualMissingPairCollides_iff_nativeLcm hQ hi hx
  dsimp only at hnative
  exact hnative.trans (h15PostFERightEndpointNativeLcmCondition_iff
    left right u q v q' hq hq')

/-! ## Left endpoint incidence: missing atom `(q,u)` -/

theorem h15PostFELeftIncidentPP_iff
    (u q v q' : ℕ) [NeZero (q * q')] :
    h15PostFEFrequencyCollides
        ((2 * u * q' : ℕ) : ZMod (q * q'))
        (h15PostFECommonPairBaseFrequency
          .positive .positive u q v q') ↔
      (((3 * u * q' : ℕ) : ZMod (q * q')) =
          ((v * q : ℕ) : ZMod (q * q')) ∨
        (((u * q' + v * q : ℕ) : ZMod (q * q')) = 0)) := by
  unfold h15PostFEFrequencyCollides h15PostFECommonPairBaseFrequency
    h15PostFESignedCommonResidue
  push_cast
  ring_nf
  constructor
  · rintro (h | h)
    · left
      linear_combination h
    · right
      linear_combination h
  · rintro (h | h)
    · left
      linear_combination h
    · right
      linear_combination h

theorem h15PostFELeftIncidentPN_iff
    (u q v q' : ℕ) [NeZero (q * q')] :
    h15PostFEFrequencyCollides
        ((2 * u * q' : ℕ) : ZMod (q * q'))
        (h15PostFECommonPairBaseFrequency
          .positive .negative u q v q') ↔
      ((((3 * u * q' + v * q : ℕ) : ZMod (q * q')) = 0) ∨
        ((u * q' : ℕ) : ZMod (q * q')) =
          ((v * q : ℕ) : ZMod (q * q'))) := by
  unfold h15PostFEFrequencyCollides h15PostFECommonPairBaseFrequency
    h15PostFESignedCommonResidue
  push_cast
  ring_nf
  constructor
  · rintro (h | h)
    · left
      linear_combination h
    · right
      linear_combination h
  · rintro (h | h)
    · left
      linear_combination h
    · right
      linear_combination h

theorem h15PostFELeftIncidentNP_iff
    (u q v q' : ℕ) [NeZero (q * q')] :
    h15PostFEFrequencyCollides
        ((2 * u * q' : ℕ) : ZMod (q * q'))
        (h15PostFECommonPairBaseFrequency
          .negative .positive u q v q') ↔
      (((u * q' : ℕ) : ZMod (q * q')) =
          ((v * q : ℕ) : ZMod (q * q')) ∨
        (((3 * u * q' + v * q : ℕ) : ZMod (q * q')) = 0)) := by
  unfold h15PostFEFrequencyCollides h15PostFECommonPairBaseFrequency
    h15PostFESignedCommonResidue
  push_cast
  ring_nf
  constructor
  · rintro (h | h)
    · left
      linear_combination h
    · right
      linear_combination h
  · rintro (h | h)
    · left
      linear_combination h
    · right
      linear_combination h

theorem h15PostFELeftIncidentNN_iff
    (u q v q' : ℕ) [NeZero (q * q')] :
    h15PostFEFrequencyCollides
        ((2 * u * q' : ℕ) : ZMod (q * q'))
        (h15PostFECommonPairBaseFrequency
          .negative .negative u q v q') ↔
      ((((u * q' + v * q : ℕ) : ZMod (q * q')) = 0) ∨
        ((3 * u * q' : ℕ) : ZMod (q * q')) =
          ((v * q : ℕ) : ZMod (q * q'))) := by
  unfold h15PostFEFrequencyCollides h15PostFECommonPairBaseFrequency
    h15PostFESignedCommonResidue
  push_cast
  ring_nf
  constructor
  · rintro (h | h)
    · left
      linear_combination h
    · right
      linear_combination h
  · rintro (h | h)
    · left
      linear_combination h
    · right
      linear_combination h

/-! ## Right endpoint incidence: missing atom `(q',v)` -/

theorem h15PostFERightIncidentPP_iff
    (u q v q' : ℕ) [NeZero (q * q')] :
    h15PostFEFrequencyCollides
        ((2 * v * q : ℕ) : ZMod (q * q'))
        (h15PostFECommonPairBaseFrequency
          .positive .positive u q v q') ↔
      ((((u * q' + v * q : ℕ) : ZMod (q * q')) = 0) ∨
        ((3 * v * q : ℕ) : ZMod (q * q')) =
          ((u * q' : ℕ) : ZMod (q * q'))) := by
  unfold h15PostFEFrequencyCollides h15PostFECommonPairBaseFrequency
    h15PostFESignedCommonResidue
  push_cast
  ring_nf
  constructor
  · rintro (h | h)
    · left
      linear_combination h
    · right
      linear_combination h
  · rintro (h | h)
    · left
      linear_combination h
    · right
      linear_combination h

theorem h15PostFERightIncidentPN_iff
    (u q v q' : ℕ) [NeZero (q * q')] :
    h15PostFEFrequencyCollides
        ((2 * v * q : ℕ) : ZMod (q * q'))
        (h15PostFECommonPairBaseFrequency
          .positive .negative u q v q') ↔
      ((((u * q' + 3 * v * q : ℕ) : ZMod (q * q')) = 0) ∨
        ((v * q : ℕ) : ZMod (q * q')) =
          ((u * q' : ℕ) : ZMod (q * q'))) := by
  unfold h15PostFEFrequencyCollides h15PostFECommonPairBaseFrequency
    h15PostFESignedCommonResidue
  push_cast
  ring_nf
  constructor
  · rintro (h | h)
    · left
      linear_combination h
    · right
      linear_combination h
  · rintro (h | h)
    · left
      linear_combination h
    · right
      linear_combination h

theorem h15PostFERightIncidentNP_iff
    (u q v q' : ℕ) [NeZero (q * q')] :
    h15PostFEFrequencyCollides
        ((2 * v * q : ℕ) : ZMod (q * q'))
        (h15PostFECommonPairBaseFrequency
          .negative .positive u q v q') ↔
      (((v * q : ℕ) : ZMod (q * q')) =
          ((u * q' : ℕ) : ZMod (q * q')) ∨
        (((u * q' + 3 * v * q : ℕ) : ZMod (q * q')) = 0)) := by
  unfold h15PostFEFrequencyCollides h15PostFECommonPairBaseFrequency
    h15PostFESignedCommonResidue
  push_cast
  ring_nf
  constructor
  · rintro (h | h)
    · left
      linear_combination h
    · right
      linear_combination h
  · rintro (h | h)
    · left
      linear_combination h
    · right
      linear_combination h

theorem h15PostFERightIncidentNN_iff
    (u q v q' : ℕ) [NeZero (q * q')] :
    h15PostFEFrequencyCollides
        ((2 * v * q : ℕ) : ZMod (q * q'))
        (h15PostFECommonPairBaseFrequency
          .negative .negative u q v q') ↔
      (((3 * v * q : ℕ) : ZMod (q * q')) =
          ((u * q' : ℕ) : ZMod (q * q')) ∨
        (((u * q' + v * q : ℕ) : ZMod (q * q')) = 0)) := by
  unfold h15PostFEFrequencyCollides h15PostFECommonPairBaseFrequency
    h15PostFESignedCommonResidue
  push_cast
  ring_nf
  constructor
  · rintro (h | h)
    · left
      linear_combination h
    · right
      linear_combination h
  · rintro (h | h)
    · left
      linear_combination h
    · right
      linear_combination h

end NBMellinTools.NB12
