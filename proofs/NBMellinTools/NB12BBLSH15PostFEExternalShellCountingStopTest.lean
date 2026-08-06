/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEExternalMissingPairCongruenceShells

/-!
# NB12zzzaR: external-shell counting stop test

The two lift multipliers in an external missing--pair collision are coprime.
This file extracts the exact divisibility forced by either the equal or the
opposite shell.  It then counts the admissible missing native residues below
the missing modulus.

The resulting density restriction is genuine finite arithmetic information.
It is only a necessary condition, however, and no signed coefficient saving
or asymptotic H15 estimate is inferred from it.
-/

namespace NBMellinTools.NB12

/-! ## Generic coprime-multiplier extraction -/

theorem coprimeMultiplier_modEq_forces_divisibility
    {A B L x y : ℕ}
    (hA : A ∣ L) (hB : B ∣ L) (hcop : Nat.Coprime B A)
    (h : x * A ≡ y * B [MOD L]) :
    B ∣ x ∧ A ∣ y := by
  have hmodB : x * A ≡ y * B [MOD B] := h.of_dvd hB
  have hBy : B ∣ y * B := dvd_mul_left B y
  have hBxA : B ∣ x * A := Nat.modEq_zero_iff_dvd.mp
    (hmodB.trans (Nat.modEq_zero_iff_dvd.mpr hBy))
  have hmodA : x * A ≡ y * B [MOD A] := h.of_dvd hA
  have hAx : A ∣ x * A := dvd_mul_left A x
  have hAyB : A ∣ y * B := Nat.modEq_zero_iff_dvd.mp
    (hmodA.symm.trans (Nat.modEq_zero_iff_dvd.mpr hAx))
  exact ⟨hcop.dvd_of_dvd_mul_right hBxA,
    hcop.symm.dvd_of_dvd_mul_right hAyB⟩

theorem coprimeMultiplier_sum_forces_divisibility
    {A B L x y : ℕ}
    (hA : A ∣ L) (hB : B ∣ L) (hcop : Nat.Coprime B A)
    (h : L ∣ x * A + y * B) :
    B ∣ x ∧ A ∣ y := by
  have hBsum : B ∣ x * A + y * B := hB.trans h
  have hBy : B ∣ y * B := dvd_mul_left B y
  have hBsumMod : x * A + y * B ≡ 0 [MOD B] :=
    Nat.modEq_zero_iff_dvd.mpr hBsum
  have hByMod : y * B ≡ 0 [MOD B] :=
    Nat.modEq_zero_iff_dvd.mpr hBy
  have hBxAMod : x * A ≡ 0 [MOD B] := by
    apply (Nat.ModEq.add_iff_right hByMod).mp
    simpa only [add_zero] using hBsumMod
  have hBxA : B ∣ x * A := Nat.modEq_zero_iff_dvd.mp hBxAMod
  have hAsum : A ∣ x * A + y * B := hA.trans h
  have hAx : A ∣ x * A := dvd_mul_left A x
  have hAsumMod : x * A + y * B ≡ 0 [MOD A] :=
    Nat.modEq_zero_iff_dvd.mpr hAsum
  have hAxMod : x * A ≡ 0 [MOD A] :=
    Nat.modEq_zero_iff_dvd.mpr hAx
  have hAyBMod : y * B ≡ 0 [MOD A] := by
    apply (Nat.ModEq.add_iff_left hAxMod).mp
    simpa only [zero_add] using hAsumMod
  have hAyB : A ∣ y * B := Nat.modEq_zero_iff_dvd.mp hAyBMod
  exact ⟨hcop.dvd_of_dvd_mul_right hBxA,
    hcop.symm.dvd_of_dvd_mul_right hAyB⟩

/-! ## Specialization to the H15 external shells -/

theorem h15PostFEExternalEqualShell_forces_divisibility
    (left right : BettinChandeeUnitSign)
    (w p u q v q' : ℕ) (hp : 0 < p) (hq : 0 < q) (hq' : 0 < q')
    (h : h15PostFEExternalMissingPairEqualShell
      left right w p u q v q') :
    h15PostFEExternalPairMultiplier p q q' ∣
        h15PostFEMissingNativeResidue ⟨p, w⟩ ∧
      h15PostFEExternalMissingMultiplier p q q' ∣
        h15PostFESignedPairNativeResidue left right u q v q' := by
  have hA : h15PostFEExternalMissingMultiplier p q q' ∣
      Nat.lcm p (q * q') :=
    ⟨p, (Nat.div_mul_cancel (Nat.dvd_lcm_left p (q * q'))).symm⟩
  have hB : h15PostFEExternalPairMultiplier p q q' ∣
      Nat.lcm p (q * q') :=
    ⟨q * q', (Nat.div_mul_cancel (Nat.dvd_lcm_right p (q * q'))).symm⟩
  apply coprimeMultiplier_modEq_forces_divisibility hA hB
    (h15PostFEExternalMultipliers_coprime p q q' hp hq hq')
  exact h

theorem h15PostFEExternalOppositeShell_forces_divisibility
    (left right : BettinChandeeUnitSign)
    (w p u q v q' : ℕ) (hp : 0 < p) (hq : 0 < q) (hq' : 0 < q')
    (h : h15PostFEExternalMissingPairOppositeShell
      left right w p u q v q') :
    h15PostFEExternalPairMultiplier p q q' ∣
        h15PostFEMissingNativeResidue ⟨p, w⟩ ∧
      h15PostFEExternalMissingMultiplier p q q' ∣
        h15PostFESignedPairNativeResidue left right u q v q' := by
  have hA : h15PostFEExternalMissingMultiplier p q q' ∣
      Nat.lcm p (q * q') :=
    ⟨p, (Nat.div_mul_cancel (Nat.dvd_lcm_left p (q * q'))).symm⟩
  have hB : h15PostFEExternalPairMultiplier p q q' ∣
      Nat.lcm p (q * q') :=
    ⟨q * q', (Nat.div_mul_cancel (Nat.dvd_lcm_right p (q * q'))).symm⟩
  apply coprimeMultiplier_sum_forces_divisibility hA hB
    (h15PostFEExternalMultipliers_coprime p q q' hp hq hq')
  exact h

theorem h15PostFEExternalShell_forces_divisibility
    (left right : BettinChandeeUnitSign)
    (w p u q v q' : ℕ) (hp : 0 < p) (hq : 0 < q) (hq' : 0 < q')
    (h : h15PostFEExternalMissingPairEqualShell
          left right w p u q v q' ∨
        h15PostFEExternalMissingPairOppositeShell
          left right w p u q v q') :
    h15PostFEExternalPairMultiplier p q q' ∣
        h15PostFEMissingNativeResidue ⟨p, w⟩ ∧
      h15PostFEExternalMissingMultiplier p q q' ∣
        h15PostFESignedPairNativeResidue left right u q v q' := by
  rcases h with h | h
  · exact h15PostFEExternalEqualShell_forces_divisibility
      left right w p u q v q' hp hq hq' h
  · exact h15PostFEExternalOppositeShell_forces_divisibility
      left right w p u q v q' hp hq hq' h

/-! ## Exact admissible-residue count -/

def h15PostFEExternalAdmissibleMissingNativeSupport
    (p q q' : ℕ) : Finset ℕ :=
  (Finset.range p).filter fun x =>
    h15PostFEExternalPairMultiplier p q q' ∣ x

theorem h15PostFEMissingNativeResidue_mem_externalAdmissible
    (left right : BettinChandeeUnitSign)
    (w p u q v q' : ℕ) (hp : 0 < p) (hq : 0 < q) (hq' : 0 < q')
    (h : h15PostFEExternalMissingPairEqualShell
          left right w p u q v q' ∨
        h15PostFEExternalMissingPairOppositeShell
          left right w p u q v q') :
    h15PostFEMissingNativeResidue ⟨p, w⟩ ∈
      h15PostFEExternalAdmissibleMissingNativeSupport p q q' := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr ?_, ?_⟩
  · unfold h15PostFEMissingNativeResidue
    exact Nat.mod_lt _ hp
  · exact (h15PostFEExternalShell_forces_divisibility
      left right w p u q v q' hp hq hq' h).1

theorem h15PostFEExternalAdmissibleMissingNativeSupport_card
    (p q q' : ℕ) (hp : 0 < p) :
    (h15PostFEExternalAdmissibleMissingNativeSupport p q q').card =
      (p - 1) / h15PostFEExternalPairMultiplier p q q' + 1 := by
  let B := h15PostFEExternalPairMultiplier p q q'
  have hrange : (p - 1).succ = p := Nat.succ_pred_eq_of_pos hp
  have hcard := Nat.card_multiples' (p - 1) B
  rw [hrange] at hcard
  have hdecomp :
      h15PostFEExternalAdmissibleMissingNativeSupport p q q' =
        insert 0 ((Finset.range p).filter fun x => x ≠ 0 ∧ B ∣ x) := by
    ext x
    simp only [h15PostFEExternalAdmissibleMissingNativeSupport,
      Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    change (x < p ∧ B ∣ x) ↔ x = 0 ∨ (x < p ∧ x ≠ 0 ∧ B ∣ x)
    constructor
    · rintro ⟨hxp, hBx⟩
      by_cases hx : x = 0
      · exact Or.inl hx
      · exact Or.inr ⟨hxp, hx, hBx⟩
    · rintro (rfl | ⟨hxp, _hx, hBx⟩)
      · exact ⟨hp, dvd_zero B⟩
      · exact ⟨hxp, hBx⟩
  calc
    (h15PostFEExternalAdmissibleMissingNativeSupport p q q').card =
        (insert 0 ((Finset.range p).filter fun x => x ≠ 0 ∧ B ∣ x)).card :=
      congrArg Finset.card hdecomp
    _ = ((Finset.range p).filter fun x => x ≠ 0 ∧ B ∣ x).card + 1 :=
      Finset.card_insert_of_notMem (by simp)
    _ = (p - 1) / B + 1 := congrArg (fun n => n + 1) hcard
    _ = (p - 1) / h15PostFEExternalPairMultiplier p q q' + 1 := rfl

end NBMellinTools.NB12
