/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEReducedSupportNumerators

/-!
# NB12zzzaO: native collision Diophantine audit

This file performs the first exact arithmetic audit after cancelling the
large common period.  For two missing atoms above the same modulus, the
doubled frequency has only the expected two-torsion ambiguity:

* at an odd modulus, multiplication by two is invertible;
* at modulus `2*k`, equal doubled frequencies mean equality modulo `k`;
* the opposite-frequency condition similarly drops from modulus `2*k` to
  modulus `k`.

The final two theorems instantiate this classification on the actual reduced
H15 missing support.  At odd modulus, the equal-frequency branch is the
literal residue diagonal.  At even modulus the possible half-modulus alias is
retained explicitly.  No cross-modulus collision or asymptotic estimate is
removed.
-/

namespace NBMellinTools.NB12

/-! ## Generic doubled-residue arithmetic -/

theorem h15PostFEMissingNativeResidue_modEq_iff_doubled
    (q u v : ℕ) :
    h15PostFEMissingNativeResidue ⟨q, u⟩ ≡
        h15PostFEMissingNativeResidue ⟨q, v⟩ [MOD q] ↔
      2 * u ≡ 2 * v [MOD q] := by
  simp [h15PostFEMissingNativeResidue, Nat.ModEq]

theorem h15PostFEMissingNativeResidue_sum_dvd_iff_doubled
    (q u v : ℕ) :
    q ∣ h15PostFEMissingNativeResidue ⟨q, u⟩ +
        h15PostFEMissingNativeResidue ⟨q, v⟩ ↔
      q ∣ 2 * u + 2 * v := by
  have hu : h15PostFEMissingNativeResidue ⟨q, u⟩ ≡ 2 * u [MOD q] := by
    simp [h15PostFEMissingNativeResidue, Nat.ModEq]
  have hv : h15PostFEMissingNativeResidue ⟨q, v⟩ ≡ 2 * v [MOD q] := by
    simp [h15PostFEMissingNativeResidue, Nat.ModEq]
  constructor
  · intro h
    apply Nat.modEq_zero_iff_dvd.mp
    exact (hu.add hv).symm.trans (Nat.modEq_zero_iff_dvd.mpr h)
  · intro h
    apply Nat.modEq_zero_iff_dvd.mp
    exact (hu.add hv).trans (Nat.modEq_zero_iff_dvd.mpr h)

theorem h15PostFEMissingNativeResidue_modEq_iff_of_odd
    (q u v : ℕ) (hqOdd : Odd q) :
    h15PostFEMissingNativeResidue ⟨q, u⟩ ≡
        h15PostFEMissingNativeResidue ⟨q, v⟩ [MOD q] ↔
      u ≡ v [MOD q] := by
  rw [h15PostFEMissingNativeResidue_modEq_iff_doubled]
  constructor
  · exact Nat.ModEq.cancel_left_of_coprime
      hqOdd.coprime_two_right.gcd_eq_one
  · exact Nat.ModEq.mul_left 2

theorem h15PostFEMissingNativeResidue_sum_dvd_iff_of_odd
    (q u v : ℕ) (hqOdd : Odd q) :
    q ∣ h15PostFEMissingNativeResidue ⟨q, u⟩ +
        h15PostFEMissingNativeResidue ⟨q, v⟩ ↔
      q ∣ u + v := by
  rw [h15PostFEMissingNativeResidue_sum_dvd_iff_doubled]
  rw [show 2 * u + 2 * v = 2 * (u + v) by ring]
  exact hqOdd.coprime_two_right.dvd_mul_left

theorem h15PostFEMissingNativeResidue_modEq_iff_evenModulus
    (k u v : ℕ) :
    h15PostFEMissingNativeResidue ⟨2 * k, u⟩ ≡
        h15PostFEMissingNativeResidue ⟨2 * k, v⟩ [MOD 2 * k] ↔
      u ≡ v [MOD k] := by
  rw [h15PostFEMissingNativeResidue_modEq_iff_doubled]
  exact Nat.ModEq.mul_left_cancel_iff' (by norm_num : (2 : ℕ) ≠ 0)

theorem h15PostFEMissingNativeResidue_sum_dvd_iff_evenModulus
    (k u v : ℕ) :
    2 * k ∣ h15PostFEMissingNativeResidue ⟨2 * k, u⟩ +
        h15PostFEMissingNativeResidue ⟨2 * k, v⟩ ↔
      k ∣ u + v := by
  rw [h15PostFEMissingNativeResidue_sum_dvd_iff_doubled]
  rw [show 2 * u + 2 * v = 2 * (u + v) by ring]
  exact mul_dvd_mul_iff_left (by norm_num : (2 : ℕ) ≠ 0)

theorem h15PostFESameModulusMissingNativeCollision_odd_iff
    (q u v : ℕ) (hqOdd : Odd q) :
    (h15PostFEMissingNativeResidue ⟨q, u⟩ ≡
          h15PostFEMissingNativeResidue ⟨q, v⟩ [MOD q] ∨
        q ∣ h15PostFEMissingNativeResidue ⟨q, u⟩ +
          h15PostFEMissingNativeResidue ⟨q, v⟩) ↔
      u ≡ v [MOD q] ∨ q ∣ u + v := by
  rw [h15PostFEMissingNativeResidue_modEq_iff_of_odd q u v hqOdd,
    h15PostFEMissingNativeResidue_sum_dvd_iff_of_odd q u v hqOdd]

theorem h15PostFESameModulusMissingNativeCollision_even_iff
    (k u v : ℕ) :
    (h15PostFEMissingNativeResidue ⟨2 * k, u⟩ ≡
          h15PostFEMissingNativeResidue ⟨2 * k, v⟩ [MOD 2 * k] ∨
        2 * k ∣ h15PostFEMissingNativeResidue ⟨2 * k, u⟩ +
          h15PostFEMissingNativeResidue ⟨2 * k, v⟩) ↔
      u ≡ v [MOD k] ∨ k ∣ u + v := by
  rw [h15PostFEMissingNativeResidue_modEq_iff_evenModulus,
    h15PostFEMissingNativeResidue_sum_dvd_iff_evenModulus]

/-! ## Actual-support consequences -/

theorem h15PostFEActualMissingResidue_lt_modulus
    {n g U Q : ℕ} {i : H15PostFEMissingAtomIndex}
    (hi : i ∈ h15PostFEJointMissingAtomSupport
      (h15PostFEResidueModulusSupport n g U Q)
      (h15PostFEReducedMissingResidues n g U Q)) :
    i.2 < i.1 := by
  have hi' := Finset.mem_sigma.mp hi
  have hmissing := h15PostFEReducedMissingResidues_subset
    n g U Q i.1 hi'.2
  exact Finset.mem_range.mp (Finset.mem_sdiff.mp hmissing).1

theorem h15PostFEActualSameModulusMissingCollides_odd_iff
    {n g U Q : ℕ} {i j : H15PostFEMissingAtomIndex}
    (hQ : 0 < Q)
    (hi : i ∈ h15PostFEJointMissingAtomSupport
      (h15PostFEResidueModulusSupport n g U Q)
      (h15PostFEReducedMissingResidues n g U Q))
    (hj : j ∈ h15PostFEJointMissingAtomSupport
      (h15PostFEResidueModulusSupport n g U Q)
      (h15PostFEReducedMissingResidues n g U Q))
    (hmod : j.1 = i.1) (hqOdd : Odd i.1) :
    letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
      ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
    h15PostFEFrequencyCollides
        (h15PostFELiftedMissingFrequency
          (h15PostFEActualCommonSuperperiod n g U Q) i)
        (h15PostFELiftedMissingFrequency
          (h15PostFEActualCommonSuperperiod n g U Q) j) ↔
      i.2 = j.2 ∨ i.1 ∣ i.2 + j.2 := by
  rcases i with ⟨qi, ui⟩
  rcases j with ⟨qj, vj⟩
  dsimp at hmod hqOdd ⊢
  subst qj
  letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
    ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
  rw [h15PostFEActualMissingMissingCollides_iff_nativeLcm hQ hi hj]
  simp only [Nat.lcm_self, Nat.div_self
    (h15PostFEResidueModulusSupport_pos hQ (Finset.mem_sigma.mp hi).1),
    mul_one]
  rw [h15PostFESameModulusMissingNativeCollision_odd_iff
    qi ui vj hqOdd]
  constructor
  · intro h
    rcases h with h | h
    · left
      unfold Nat.ModEq at h
      simpa [Nat.mod_eq_of_lt (h15PostFEActualMissingResidue_lt_modulus hi),
        Nat.mod_eq_of_lt (h15PostFEActualMissingResidue_lt_modulus hj)] using h
    · exact Or.inr h
  · intro h
    rcases h with h | h
    · exact Or.inl (h ▸ Nat.ModEq.rfl)
    · exact Or.inr h

theorem h15PostFEActualSameModulusMissingCollides_even_iff
    {n g U Q k : ℕ} {i j : H15PostFEMissingAtomIndex}
    (hQ : 0 < Q)
    (hi : i ∈ h15PostFEJointMissingAtomSupport
      (h15PostFEResidueModulusSupport n g U Q)
      (h15PostFEReducedMissingResidues n g U Q))
    (hj : j ∈ h15PostFEJointMissingAtomSupport
      (h15PostFEResidueModulusSupport n g U Q)
      (h15PostFEReducedMissingResidues n g U Q))
    (hiModulus : i.1 = 2 * k) (hjModulus : j.1 = 2 * k) :
    letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
      ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
    h15PostFEFrequencyCollides
        (h15PostFELiftedMissingFrequency
          (h15PostFEActualCommonSuperperiod n g U Q) i)
        (h15PostFELiftedMissingFrequency
          (h15PostFEActualCommonSuperperiod n g U Q) j) ↔
      i.2 ≡ j.2 [MOD k] ∨ k ∣ i.2 + j.2 := by
  rcases i with ⟨qi, ui⟩
  rcases j with ⟨qj, vj⟩
  dsimp at hiModulus hjModulus ⊢
  subst qi
  subst qj
  letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
    ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
  rw [h15PostFEActualMissingMissingCollides_iff_nativeLcm hQ hi hj]
  have hq : 0 < 2 * k := by
    simpa using
      h15PostFEResidueModulusSupport_pos hQ (Finset.mem_sigma.mp hi).1
  simp only [Nat.lcm_self, Nat.div_self hq,
    mul_one]
  exact h15PostFESameModulusMissingNativeCollision_even_iff k ui vj

end NBMellinTools.NB12
