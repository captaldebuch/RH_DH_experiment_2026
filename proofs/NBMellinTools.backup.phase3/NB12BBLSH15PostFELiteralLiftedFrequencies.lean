/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFECommonSuperperiod

/-!
# NB12zzzZ: literal H15 frequencies in the common superperiod

This file defines total lifted-frequency functions for missing atoms and
oriented pair atoms.  On the reduced literal supports, their characters in
the product-square common period are proved exactly equal to the original
H15 phases.

The definitions are total so they can be passed directly to the abstract
collision-Gram interface.  Their zero branches are irrelevant on the
reduced supports and are discharged by the support theorems.
-/

open AddChar ZMod

namespace NBMellinTools.NB12

/-- Total lift of one missing-residue base frequency to a common period. -/
noncomputable def h15PostFELiftedMissingFrequency
    (M : ℕ) [NeZero M] (i : H15PostFEMissingAtomIndex) : ZMod M :=
  if hq : i.1 = 0 then 0
  else
    letI : NeZero i.1 := ⟨hq⟩
    h15PostFELiftFrequency i.1 M
      (h15PostFEMissingBaseFrequency i.2 i.1)

/-- Total lift of one signed ordered-pair base frequency to a common
period. -/
noncomputable def h15PostFELiftedPairFrequency
    (M : ℕ) [NeZero M]
    (left right : BettinChandeeUnitSign)
    (κ : H15PostFEJointResiduePair) : ZMod M :=
  if hpair : κ.1.2 * κ.2.2 = 0 then 0
  else
    letI : NeZero (κ.1.2 * κ.2.2) := ⟨hpair⟩
    h15PostFELiftFrequency (κ.1.2 * κ.2.2) M
      (h15PostFECommonPairBaseFrequency left right
        κ.1.1 κ.1.2 κ.2.1 κ.2.2)

theorem h15PostFEReducedMissingPhase_eq_liftedFrequency
    (M r a q : ℕ) (hq : 0 < q) (hM : 0 < M)
    (huq : Nat.Coprime a q) (hdiv : q ∣ M) :
    letI : NeZero M := ⟨hM.ne'⟩
    h15PostFEReducedDoubledAdditivePhase r a q =
      ZMod.stdAddChar
        ((r : ZMod M) *
          h15PostFELiftedMissingFrequency M ⟨q, a⟩) := by
  letI : NeZero M := ⟨hM.ne'⟩
  letI : NeZero q := ⟨hq.ne'⟩
  rw [h15PostFEReducedDoubledAdditivePhase_eq_baseFrequency
    r a q hq huq]
  rw [stdAddChar_mul_liftFrequency q M r
    (h15PostFEMissingBaseFrequency a q) hq hM hdiv]
  unfold h15PostFELiftedMissingFrequency
  simp [hq.ne']

theorem h15PostFEReducedPairPhase_eq_liftedFrequency
    (M r u q v q' : ℕ) (hM : 0 < M)
    (hq : 0 < q) (hq' : 0 < q')
    (huq : Nat.Coprime u q) (hvq' : Nat.Coprime v q')
    (hdiv : q * q' ∣ M)
    (left right : BettinChandeeUnitSign) :
    letI : NeZero M := ⟨hM.ne'⟩
    h15PostFECommonPairAdditivePhase left right r u q v q' =
      ZMod.stdAddChar
        ((r : ZMod M) *
          h15PostFELiftedPairFrequency M left right
            ((u, q), (v, q'))) := by
  letI : NeZero M := ⟨hM.ne'⟩
  letI : NeZero (q * q') :=
    ⟨Nat.mul_ne_zero hq.ne' hq'.ne'⟩
  rw [h15PostFECommonPairAdditivePhase_eq_baseFrequency
    left right r u q v q' hq hq' huq hvq']
  rw [stdAddChar_mul_liftFrequency (q * q') M r
    (h15PostFECommonPairBaseFrequency left right u q v q')
    (Nat.mul_pos hq hq') hM hdiv]
  unfold h15PostFELiftedPairFrequency
  simp [hq.ne', hq'.ne']

/-- Literal missing atoms have exactly their original doubled phase after
lifting to the actual H15 superperiod. -/
theorem h15PostFEActualMissingPhase_eq_commonSuperperiod
    {n g U Q : ℕ} {i : H15PostFEMissingAtomIndex}
    (hQ : 0 < Q)
    (hi : i ∈ h15PostFEJointMissingAtomSupport
      (h15PostFEResidueModulusSupport n g U Q)
      (h15PostFEReducedMissingResidues n g U Q))
    (r : ℕ) :
    letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
      ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
    h15PostFEReducedDoubledAdditivePhase r i.2 i.1 =
      ZMod.stdAddChar
        ((r : ZMod (h15PostFEActualCommonSuperperiod n g U Q)) *
          h15PostFELiftedMissingFrequency
            (h15PostFEActualCommonSuperperiod n g U Q) i) := by
  have hi' := Finset.mem_sigma.mp hi
  exact h15PostFEReducedMissingPhase_eq_liftedFrequency
    (h15PostFEActualCommonSuperperiod n g U Q) r i.2 i.1
    (h15PostFEResidueModulusSupport_pos hQ hi'.1)
    (h15PostFEActualCommonSuperperiod_pos n g U Q hQ)
    (coprime_of_mem_h15PostFEReducedMissingResidues hi'.2)
    (modulus_dvd_h15PostFEActualCommonSuperperiod hi'.1)

/-- Literal reduced pair atoms have exactly their original signed common
phase after lifting to the actual H15 superperiod. -/
theorem h15PostFEActualPairPhase_eq_commonSuperperiod
    {n g U Q : ℕ} {κ : H15PostFEJointResiduePair}
    (hQ : 0 < Q)
    (hκ : κ ∈ h15PostFEReducedOrderedPairResidueSupport n g U Q)
    (left right : BettinChandeeUnitSign) (r : ℕ) :
    letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
      ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
    h15PostFECommonPairAdditivePhase left right r
        κ.1.1 κ.1.2 κ.2.1 κ.2.2 =
      ZMod.stdAddChar
        ((r : ZMod (h15PostFEActualCommonSuperperiod n g U Q)) *
          h15PostFELiftedPairFrequency
            (h15PostFEActualCommonSuperperiod n g U Q)
            left right κ) := by
  have hraw := h15PostFEReducedOrderedPairResidueSupport_subset
    n g U Q hκ
  have hactual := h15PostFEOrderedPairResidueSupport_subset_actual hraw
  have hq : 0 < κ.1.2 :=
    Nat.zero_lt_of_lt (h15PostFEResidueKey_fst_lt_snd hQ hactual.1)
  have hq' : 0 < κ.2.2 :=
    Nat.zero_lt_of_lt (h15PostFEResidueKey_fst_lt_snd hQ hactual.2)
  have hcop :=
    coprime_of_mem_h15PostFEReducedOrderedPairResidueSupport hκ
  exact h15PostFEReducedPairPhase_eq_liftedFrequency
    (h15PostFEActualCommonSuperperiod n g U Q) r
    κ.1.1 κ.1.2 κ.2.1 κ.2.2
    (h15PostFEActualCommonSuperperiod_pos n g U Q hQ)
    hq hq' hcop.1 hcop.2
    (pair_modulus_dvd_h15PostFEActualCommonSuperperiod hraw)
    left right

end NBMellinTools.NB12
