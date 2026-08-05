/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEReducedPairSupport

/-!
# NB12zzzY: a literal finite common superperiod for one H15 block

For one fixed `(n,g,U,Q)` block, take the product of every residue modulus
that occurs and square it.  This is not claimed to be the smallest possible
period.  It is a canonical finite period with the two properties needed by
the collision Gram:

* every retained missing modulus divides it; and
* every retained ordered-pair modulus `q*q'` divides it.

The construction is deliberately elementary.  A later optimization may
replace the product by an `lcm` without changing the collision identity.
-/

open AddChar ZMod
open scoped BigOperators

namespace NBMellinTools.NB12

/-- Product of all moduli occurring in the post-FE residue ledger. -/
def h15PostFEActualModulusProduct
    (n g U Q : ℕ) : ℕ :=
  ∏ q ∈ h15PostFEResidueModulusSupport n g U Q, q

/-- A common period for both the linear missing atoms and the pair atoms. -/
def h15PostFEActualCommonSuperperiod
    (n g U Q : ℕ) : ℕ :=
  h15PostFEActualModulusProduct n g U Q *
    h15PostFEActualModulusProduct n g U Q

theorem h15PostFEActualModulusProduct_pos
    (n g U Q : ℕ) (hQ : 0 < Q) :
    0 < h15PostFEActualModulusProduct n g U Q := by
  unfold h15PostFEActualModulusProduct
  exact Finset.prod_pos fun q hq =>
    h15PostFEResidueModulusSupport_pos hQ hq

theorem h15PostFEActualCommonSuperperiod_pos
    (n g U Q : ℕ) (hQ : 0 < Q) :
    0 < h15PostFEActualCommonSuperperiod n g U Q := by
  unfold h15PostFEActualCommonSuperperiod
  exact Nat.mul_pos
    (h15PostFEActualModulusProduct_pos n g U Q hQ)
    (h15PostFEActualModulusProduct_pos n g U Q hQ)

theorem modulus_dvd_h15PostFEActualModulusProduct
    {n g U Q q : ℕ}
    (hq : q ∈ h15PostFEResidueModulusSupport n g U Q) :
    q ∣ h15PostFEActualModulusProduct n g U Q := by
  unfold h15PostFEActualModulusProduct
  simpa using
    (Finset.dvd_prod_of_mem (fun x : ℕ => x) hq)

theorem modulus_dvd_h15PostFEActualCommonSuperperiod
    {n g U Q q : ℕ}
    (hq : q ∈ h15PostFEResidueModulusSupport n g U Q) :
    q ∣ h15PostFEActualCommonSuperperiod n g U Q := by
  unfold h15PostFEActualCommonSuperperiod
  exact dvd_mul_of_dvd_left
    (modulus_dvd_h15PostFEActualModulusProduct hq)
    (h15PostFEActualModulusProduct n g U Q)

theorem pair_left_modulus_mem_h15PostFEResidueModulusSupport
    {n g U Q : ℕ} {κ : H15PostFEJointResiduePair}
    (hκ : κ ∈ h15PostFEOrderedPairResidueSupport n g U Q) :
    κ.1.2 ∈ h15PostFEResidueModulusSupport n g U Q := by
  classical
  have hactual := h15PostFEOrderedPairResidueSupport_subset_actual hκ
  unfold h15PostFEResidueModulusSupport
  exact Finset.mem_image.mpr ⟨κ.1, hactual.1, rfl⟩

theorem pair_right_modulus_mem_h15PostFEResidueModulusSupport
    {n g U Q : ℕ} {κ : H15PostFEJointResiduePair}
    (hκ : κ ∈ h15PostFEOrderedPairResidueSupport n g U Q) :
    κ.2.2 ∈ h15PostFEResidueModulusSupport n g U Q := by
  classical
  have hactual := h15PostFEOrderedPairResidueSupport_subset_actual hκ
  unfold h15PostFEResidueModulusSupport
  exact Finset.mem_image.mpr ⟨κ.2, hactual.2, rfl⟩

/-- Every literal pair-character denominator divides the common period. -/
theorem pair_modulus_dvd_h15PostFEActualCommonSuperperiod
    {n g U Q : ℕ} {κ : H15PostFEJointResiduePair}
    (hκ : κ ∈ h15PostFEOrderedPairResidueSupport n g U Q) :
    κ.1.2 * κ.2.2 ∣ h15PostFEActualCommonSuperperiod n g U Q := by
  unfold h15PostFEActualCommonSuperperiod
  exact Nat.mul_dvd_mul
    (modulus_dvd_h15PostFEActualModulusProduct
      (pair_left_modulus_mem_h15PostFEResidueModulusSupport hκ))
    (modulus_dvd_h15PostFEActualModulusProduct
      (pair_right_modulus_mem_h15PostFEResidueModulusSupport hκ))

/-- Quotient used to lift a character from a divisor modulus to a common
period. -/
def h15PostFEPeriodLiftMultiplier (q M : ℕ) : ℕ := M / q

theorem h15PostFEPeriodLiftMultiplier_pos
    {q M : ℕ} (hq : 0 < q) (hM : 0 < M) (hdiv : q ∣ M) :
    0 < h15PostFEPeriodLiftMultiplier q M := by
  unfold h15PostFEPeriodLiftMultiplier
  exact Nat.div_pos (Nat.le_of_dvd hM hdiv) hq

theorem modulus_mul_h15PostFEPeriodLiftMultiplier
    {q M : ℕ} (hdiv : q ∣ M) :
    q * h15PostFEPeriodLiftMultiplier q M = M := by
  unfold h15PostFEPeriodLiftMultiplier
  exact Nat.mul_div_cancel' hdiv

/-- A base frequency lifted from `ZMod q` to `ZMod M`. -/
noncomputable def h15PostFELiftFrequency
    (q M : ℕ) [NeZero q] [NeZero M] (a : ZMod q) : ZMod M :=
  ((a.val * h15PostFEPeriodLiftMultiplier q M : ℕ) : ZMod M)

/-- Character evaluation commutes with lifting a base frequency to a
positive multiple of its modulus. -/
theorem stdAddChar_mul_liftFrequency
    (q M r : ℕ) (a : ZMod q)
    (hq : 0 < q) (hM : 0 < M) (hdiv : q ∣ M) :
    letI : NeZero q := ⟨hq.ne'⟩
    letI : NeZero M := ⟨hM.ne'⟩
    ZMod.stdAddChar ((r : ZMod q) * a) =
      ZMod.stdAddChar
        ((r : ZMod M) * h15PostFELiftFrequency q M a) := by
  letI : NeZero q := ⟨hq.ne'⟩
  letI : NeZero M := ⟨hM.ne'⟩
  have hb : 0 < h15PostFEPeriodLiftMultiplier q M :=
    h15PostFEPeriodLiftMultiplier_pos hq hM hdiv
  have hmul := modulus_mul_h15PostFEPeriodLiftMultiplier hdiv
  calc
    ZMod.stdAddChar ((r : ZMod q) * a) =
        ZMod.stdAddChar (((r * a.val : ℕ) : ZMod q)) := by
      have ha : a = (a.val : ZMod q) :=
        (ZMod.natCast_zmod_val a).symm
      apply congrArg ZMod.stdAddChar
      calc
        (r : ZMod q) * a = (r : ZMod q) * (a.val : ZMod q) := by
          exact congrArg (fun z : ZMod q => (r : ZMod q) * z) ha
        _ = ((r * a.val : ℕ) : ZMod q) := by push_cast; rfl
    _ = ZMod.stdAddChar
        (((r * (a.val * h15PostFEPeriodLiftMultiplier q M) : ℕ) : ZMod M)) := by
      rw [show ZMod.stdAddChar (((r * a.val : ℕ) : ZMod q)) =
          Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I * ((r * a.val : ℕ) : ℂ) /
              (q : ℂ)) by
        simpa using ZMod.stdAddChar_coe (N := q) ((r * a.val : ℕ) : ℤ)]
      rw [show ZMod.stdAddChar
            (((r * (a.val * h15PostFEPeriodLiftMultiplier q M) : ℕ) : ZMod M)) =
          Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I *
              ((r * (a.val * h15PostFEPeriodLiftMultiplier q M) : ℕ) : ℂ) /
              (M : ℂ)) by
        simpa using ZMod.stdAddChar_coe (N := M)
          ((r * (a.val * h15PostFEPeriodLiftMultiplier q M) : ℕ) : ℤ)]
      congr 1
      have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
      have hbC : (h15PostFEPeriodLiftMultiplier q M : ℂ) ≠ 0 := by
        exact_mod_cast hb.ne'
      have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
      have hmulC :
          (q : ℂ) * (h15PostFEPeriodLiftMultiplier q M : ℂ) =
            (M : ℂ) := by
        exact_mod_cast hmul
      push_cast
      field_simp [hqC, hMC]
      rw [← hmulC]
      ring
    _ = ZMod.stdAddChar
        ((r : ZMod M) * h15PostFELiftFrequency q M a) := by
      unfold h15PostFELiftFrequency
      push_cast
      rfl

end NBMellinTools.NB12
