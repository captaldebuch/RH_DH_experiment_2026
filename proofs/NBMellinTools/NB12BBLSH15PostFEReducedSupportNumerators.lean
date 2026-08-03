/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFECollisionCongruenceClassification

/-!
# NB12zzzaN: native-modulus collision numerators

The collision classification in the preceding file still uses numerators in
the large product-square common period.  Here the common lift factor is
cancelled exactly.  Two lifted rational frequencies collide in `ZMod M` iff
their native representatives collide in the least common multiple of their
denominators.

The missing representative is `2u mod q`.  The oriented-pair representative
is the residue of the signed integer `-epsilon*u*q' + eta*v*q` modulo `q*q'`.
The final theorems instantiate these formulas on the actual reduced H15
supports.  No cardinality or cancellation estimate is proved.
-/

namespace NBMellinTools.NB12

/-! ## Cancelling a common-period lift -/

theorem h15PostFEPeriodLiftMultiplier_eq_lcm_mul
    {q q' M : ℕ} (hqM : q ∣ M) (hq'M : q' ∣ M) :
    h15PostFEPeriodLiftMultiplier q M =
      (Nat.lcm q q' / q) * (M / Nat.lcm q q') := by
  have hLM : Nat.lcm q q' ∣ M := Nat.lcm_dvd hqM hq'M
  have hqL : q ∣ Nat.lcm q q' := Nat.dvd_lcm_left q q'
  unfold h15PostFEPeriodLiftMultiplier
  calc
    M / q = (Nat.lcm q q' * (M / Nat.lcm q q')) / q := by
      rw [Nat.mul_div_cancel' hLM]
    _ = ((M / Nat.lcm q q') * Nat.lcm q q') / q := by
      rw [mul_comm]
    _ = (M / Nat.lcm q q') * (Nat.lcm q q' / q) :=
      Nat.mul_div_assoc _ hqL
    _ = (Nat.lcm q q' / q) * (M / Nat.lcm q q') := by
      rw [mul_comm]

theorem h15PostFELiftedEqualCongruence_iff_lcm
    {q q' M a b : ℕ}
    (hq : 0 < q) (hq' : 0 < q') (hM : 0 < M)
    (hqM : q ∣ M) (hq'M : q' ∣ M) :
    a * h15PostFEPeriodLiftMultiplier q M ≡
        b * h15PostFEPeriodLiftMultiplier q' M [MOD M] ↔
      a * (Nat.lcm q q' / q) ≡
        b * (Nat.lcm q q' / q') [MOD Nat.lcm q q'] := by
  have hL : 0 < Nat.lcm q q' := Nat.lcm_pos hq hq'
  have hLM : Nat.lcm q q' ∣ M := Nat.lcm_dvd hqM hq'M
  let c := M / Nat.lcm q q'
  have hc : 0 < c :=
    Nat.div_pos (Nat.le_of_dvd hM hLM) hL
  have hMc : M = Nat.lcm q q' * c := by
    exact (Nat.mul_div_cancel' hLM).symm
  rw [h15PostFEPeriodLiftMultiplier_eq_lcm_mul hqM hq'M,
    h15PostFEPeriodLiftMultiplier_eq_lcm_mul hq'M hqM]
  simp only [Nat.lcm_comm q' q]
  change
    a * ((Nat.lcm q q' / q) * c) ≡
        b * ((Nat.lcm q q' / q') * c) [MOD M] ↔ _
  simp only [← mul_assoc]
  rw [hMc]
  simpa only [mul_assoc] using
    (Nat.ModEq.mul_right_cancel_iff'
      (a := a * (Nat.lcm q q' / q))
      (b := b * (Nat.lcm q q' / q')) hc.ne')

theorem h15PostFELiftedOppositeDivisibility_iff_lcm
    {q q' M a b : ℕ}
    (hq : 0 < q) (hq' : 0 < q') (hM : 0 < M)
    (hqM : q ∣ M) (hq'M : q' ∣ M) :
    M ∣ a * h15PostFEPeriodLiftMultiplier q M +
        b * h15PostFEPeriodLiftMultiplier q' M ↔
      Nat.lcm q q' ∣
        a * (Nat.lcm q q' / q) +
          b * (Nat.lcm q q' / q') := by
  have hL : 0 < Nat.lcm q q' := Nat.lcm_pos hq hq'
  have hLM : Nat.lcm q q' ∣ M := Nat.lcm_dvd hqM hq'M
  let c := M / Nat.lcm q q'
  have hc : 0 < c :=
    Nat.div_pos (Nat.le_of_dvd hM hLM) hL
  have hMc : M = Nat.lcm q q' * c := by
    exact (Nat.mul_div_cancel' hLM).symm
  rw [h15PostFEPeriodLiftMultiplier_eq_lcm_mul hqM hq'M,
    h15PostFEPeriodLiftMultiplier_eq_lcm_mul hq'M hqM]
  simp only [Nat.lcm_comm q' q]
  change
    M ∣ a * ((Nat.lcm q q' / q) * c) +
        b * ((Nat.lcm q q' / q') * c) ↔ _
  simp only [← mul_assoc]
  rw [hMc]
  rw [show
      a * (Nat.lcm q q' / q) * c +
          b * (Nat.lcm q q' / q') * c =
        (a * (Nat.lcm q q' / q) +
          b * (Nat.lcm q q' / q')) * c by ring]
  exact Nat.mul_dvd_mul_iff_right hc

/-- Collision of two common-period lifts is entirely a native-lcm
condition. -/
theorem h15PostFELiftedNatCollision_iff_lcm
    {q q' M a b : ℕ} [NeZero M]
    (hq : 0 < q) (hq' : 0 < q') (hM : 0 < M)
    (hqM : q ∣ M) (hq'M : q' ∣ M) :
    h15PostFEFrequencyCollides
        ((a * h15PostFEPeriodLiftMultiplier q M : ℕ) : ZMod M)
        ((b * h15PostFEPeriodLiftMultiplier q' M : ℕ) : ZMod M) ↔
      a * (Nat.lcm q q' / q) ≡
          b * (Nat.lcm q q' / q') [MOD Nat.lcm q q'] ∨
        Nat.lcm q q' ∣
          a * (Nat.lcm q q' / q) +
            b * (Nat.lcm q q' / q') := by
  rw [h15PostFEFrequencyCollides_natCast_iff,
    h15PostFELiftedEqualCongruence_iff_lcm hq hq' hM hqM hq'M,
    h15PostFELiftedOppositeDivisibility_iff_lcm hq hq' hM hqM hq'M]

/-! ## Explicit missing and oriented-pair representatives -/

/-- Native residue of the doubled missing frequency. -/
def h15PostFEMissingNativeResidue
    (i : H15PostFEMissingAtomIndex) : ℕ :=
  (2 * i.2) % i.1

theorem h15PostFEMissingLiftNumerator_eq_native
    (M : ℕ) (i : H15PostFEMissingAtomIndex) (hq : 0 < i.1) :
    h15PostFEMissingLiftNumerator M i =
      h15PostFEMissingNativeResidue i *
        h15PostFEPeriodLiftMultiplier i.1 M := by
  letI : NeZero i.1 := ⟨hq.ne'⟩
  simp only [h15PostFEMissingLiftNumerator, dif_neg hq.ne',
    h15PostFEMissingNativeResidue]
  rw [show (h15PostFEMissingBaseFrequency i.2 i.1).val =
      (2 * i.2) % i.1 by
    unfold h15PostFEMissingBaseFrequency
    rw [ZMod.val_natCast]]

/-- Integer action of an orientation sign. -/
def h15PostFEUnitSignInt
    (sign : BettinChandeeUnitSign) (a : ℕ) : ℤ :=
  match sign with
  | .positive => a
  | .negative => -(a : ℤ)

/-- Native residue of `-epsilon*u*q' + eta*v*q` modulo `q*q'`. -/
noncomputable def h15PostFESignedPairNativeResidue
    (left right : BettinChandeeUnitSign)
    (u q v q' : ℕ) : ℕ :=
  if h : q * q' = 0 then 0 else
    letI : NeZero (q * q') := ⟨h⟩
    ((-h15PostFEUnitSignInt left (u * q') +
        h15PostFEUnitSignInt right (v * q) : ℤ) : ZMod (q * q')).val

theorem h15PostFECommonPairBaseFrequency_val_eq_signedNativeResidue
    (left right : BettinChandeeUnitSign)
    (u q v q' : ℕ) [NeZero (q * q')] :
    (h15PostFECommonPairBaseFrequency left right u q v q').val =
      h15PostFESignedPairNativeResidue left right u q v q' := by
  unfold h15PostFECommonPairBaseFrequency
    h15PostFESignedPairNativeResidue h15PostFEUnitSignInt
  simp only [dif_neg (NeZero.ne (q * q'))]
  cases left <;> cases right <;>
    simp only [h15PostFESignedCommonResidue] <;>
    apply congrArg ZMod.val <;> push_cast <;> ring

theorem h15PostFEPairLiftNumerator_eq_native
    (M : ℕ) (x : H15PostFEOrientedPairAtomIndex)
    (hpair : 0 < x.1.1.2 * x.1.2.2) :
    h15PostFEPairLiftNumerator M x =
      h15PostFESignedPairNativeResidue x.2.1 x.2.2
          x.1.1.1 x.1.1.2 x.1.2.1 x.1.2.2 *
        h15PostFEPeriodLiftMultiplier (x.1.1.2 * x.1.2.2) M := by
  letI : NeZero (x.1.1.2 * x.1.2.2) := ⟨hpair.ne'⟩
  simp only [h15PostFEPairLiftNumerator, dif_neg hpair.ne']
  rw [h15PostFECommonPairBaseFrequency_val_eq_signedNativeResidue]

/-! ## Actual reduced-support instantiations -/

theorem h15PostFEActualMissingMissingCollides_iff_nativeLcm
    {n g U Q : ℕ} {i j : H15PostFEMissingAtomIndex}
    (hQ : 0 < Q)
    (hi : i ∈ h15PostFEJointMissingAtomSupport
      (h15PostFEResidueModulusSupport n g U Q)
      (h15PostFEReducedMissingResidues n g U Q))
    (hj : j ∈ h15PostFEJointMissingAtomSupport
      (h15PostFEResidueModulusSupport n g U Q)
      (h15PostFEReducedMissingResidues n g U Q)) :
    letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
      ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
    h15PostFEFrequencyCollides
        (h15PostFELiftedMissingFrequency
          (h15PostFEActualCommonSuperperiod n g U Q) i)
        (h15PostFELiftedMissingFrequency
          (h15PostFEActualCommonSuperperiod n g U Q) j) ↔
      h15PostFEMissingNativeResidue i * (Nat.lcm i.1 j.1 / i.1) ≡
          h15PostFEMissingNativeResidue j * (Nat.lcm i.1 j.1 / j.1)
            [MOD Nat.lcm i.1 j.1] ∨
        Nat.lcm i.1 j.1 ∣
          h15PostFEMissingNativeResidue i * (Nat.lcm i.1 j.1 / i.1) +
            h15PostFEMissingNativeResidue j *
              (Nat.lcm i.1 j.1 / j.1) := by
  let M := h15PostFEActualCommonSuperperiod n g U Q
  letI : NeZero M :=
    ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
  have hi' := Finset.mem_sigma.mp hi
  have hj' := Finset.mem_sigma.mp hj
  have hqi : 0 < i.1 := h15PostFEResidueModulusSupport_pos hQ hi'.1
  have hqj : 0 < j.1 := h15PostFEResidueModulusSupport_pos hQ hj'.1
  rw [h15PostFELiftedMissingFrequency_eq_natCast_numerator,
    h15PostFELiftedMissingFrequency_eq_natCast_numerator,
    h15PostFEMissingLiftNumerator_eq_native M i hqi,
    h15PostFEMissingLiftNumerator_eq_native M j hqj]
  exact h15PostFELiftedNatCollision_iff_lcm hqi hqj
    (h15PostFEActualCommonSuperperiod_pos n g U Q hQ)
    (modulus_dvd_h15PostFEActualCommonSuperperiod hi'.1)
    (modulus_dvd_h15PostFEActualCommonSuperperiod hj'.1)

theorem h15PostFEActualMissingPairCollides_iff_nativeLcm
    {n g U Q : ℕ} {i : H15PostFEMissingAtomIndex}
    {x : H15PostFEOrientedPairAtomIndex}
    (hQ : 0 < Q)
    (hi : i ∈ h15PostFEJointMissingAtomSupport
      (h15PostFEResidueModulusSupport n g U Q)
      (h15PostFEReducedMissingResidues n g U Q))
    (hx : x ∈ h15PostFEActualOrientedPairSupport n g U Q) :
    let pairModulus := x.1.1.2 * x.1.2.2
    letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
      ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
    h15PostFEFrequencyCollides
        (h15PostFELiftedMissingFrequency
          (h15PostFEActualCommonSuperperiod n g U Q) i)
        (h15PostFELiftedPairFrequency
          (h15PostFEActualCommonSuperperiod n g U Q)
          x.2.1 x.2.2 x.1) ↔
      h15PostFEMissingNativeResidue i *
          (Nat.lcm i.1 pairModulus / i.1) ≡
        h15PostFESignedPairNativeResidue x.2.1 x.2.2
            x.1.1.1 x.1.1.2 x.1.2.1 x.1.2.2 *
          (Nat.lcm i.1 pairModulus / pairModulus)
            [MOD Nat.lcm i.1 pairModulus] ∨
      Nat.lcm i.1 pairModulus ∣
        h15PostFEMissingNativeResidue i *
            (Nat.lcm i.1 pairModulus / i.1) +
          h15PostFESignedPairNativeResidue x.2.1 x.2.2
              x.1.1.1 x.1.1.2 x.1.2.1 x.1.2.2 *
            (Nat.lcm i.1 pairModulus / pairModulus) := by
  dsimp only
  let M := h15PostFEActualCommonSuperperiod n g U Q
  letI : NeZero M :=
    ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
  have hi' := Finset.mem_sigma.mp hi
  have hx' := Finset.mem_product.mp hx
  have hκ := hx'.1
  have hraw := h15PostFEReducedOrderedPairResidueSupport_subset
    n g U Q hκ
  have hactual := h15PostFEOrderedPairResidueSupport_subset_actual hraw
  have hqi : 0 < i.1 := h15PostFEResidueModulusSupport_pos hQ hi'.1
  have hql : 0 < x.1.1.2 :=
    Nat.zero_lt_of_lt (h15PostFEResidueKey_fst_lt_snd hQ hactual.1)
  have hqr : 0 < x.1.2.2 :=
    Nat.zero_lt_of_lt (h15PostFEResidueKey_fst_lt_snd hQ hactual.2)
  have hpair : 0 < x.1.1.2 * x.1.2.2 := Nat.mul_pos hql hqr
  rw [h15PostFELiftedMissingFrequency_eq_natCast_numerator,
    h15PostFELiftedPairFrequency_eq_natCast_numerator,
    h15PostFEMissingLiftNumerator_eq_native M i hqi,
    h15PostFEPairLiftNumerator_eq_native M x hpair]
  exact h15PostFELiftedNatCollision_iff_lcm hqi hpair
    (h15PostFEActualCommonSuperperiod_pos n g U Q hQ)
    (modulus_dvd_h15PostFEActualCommonSuperperiod hi'.1)
    (pair_modulus_dvd_h15PostFEActualCommonSuperperiod hraw)

end NBMellinTools.NB12
