/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEExternalShellCountingStopTest

/-!
# NB12zzzaS: external-shell density degeneracy

The external-shell divisibility condition restricts the missing native
residue to multiples of

`p / gcd p (q*q')`.

This file identifies the exact degeneracy of that restriction.  The
multiplier is one precisely when `p ∣ q*q'`; in that case every native
residue below `p` is admissible.  Merely requiring that `p` differ from the
two endpoint moduli does not exclude this case: `(p,q,q') = (6,2,3)` is an
explicit counterexample.

Thus external incidence alone gives no uniform congruence-density saving.
This is a finite stop test only; it neither rules out stronger information
on the actual H15 support nor proves an asymptotic cancellation estimate.
-/

namespace NBMellinTools.NB12

/-! ## Exact collapse criterion -/

theorem h15PostFEExternalPairMultiplier_eq_one_iff_dvd_product
    (p q q' : ℕ) (hq : 0 < q) (hq' : 0 < q') :
    h15PostFEExternalPairMultiplier p q q' = 1 ↔ p ∣ q * q' := by
  constructor
  · intro h
    unfold h15PostFEExternalPairMultiplier at h
    have hlcm : q * q' = Nat.lcm p (q * q') :=
      Nat.eq_of_dvd_of_div_eq_one
        (Nat.dvd_lcm_right p (q * q')) h
    exact Nat.lcm_eq_right_iff_dvd.mp hlcm.symm
  · intro h
    have hlcm : Nat.lcm p (q * q') = q * q' :=
      Nat.lcm_eq_right_iff_dvd.mpr h
    unfold h15PostFEExternalPairMultiplier
    rw [hlcm]
    exact Nat.div_self (Nat.mul_pos hq hq')

theorem h15PostFEExternalAdmissibleMissingNativeSupport_card_eq_modulus
    (p q q' : ℕ) (hp : 0 < p) (hq : 0 < q) (hq' : 0 < q')
    (hdiv : p ∣ q * q') :
    (h15PostFEExternalAdmissibleMissingNativeSupport p q q').card = p := by
  rw [h15PostFEExternalAdmissibleMissingNativeSupport_card p q q' hp,
    (h15PostFEExternalPairMultiplier_eq_one_iff_dvd_product
      p q q' hq hq').mpr hdiv]
  omega

theorem h15PostFEExternalAdmissibleMissingNativeSupport_eq_range
    (p q q' : ℕ) (hq : 0 < q) (hq' : 0 < q')
    (hdiv : p ∣ q * q') :
    h15PostFEExternalAdmissibleMissingNativeSupport p q q' =
      Finset.range p := by
  ext x
  simp [h15PostFEExternalAdmissibleMissingNativeSupport,
    (h15PostFEExternalPairMultiplier_eq_one_iff_dvd_product
      p q q' hq hq').mpr hdiv]

/-! ## External incidence does not prevent collapse -/

theorem h15PostFEExternalDensityDegeneracy_example :
    h15PostFEIsExternalMissingPairModulus 6 2 3 ∧
      h15PostFEExternalPairMultiplier 6 2 3 = 1 ∧
      (h15PostFEExternalAdmissibleMissingNativeSupport 6 2 3).card = 6 := by
  constructor
  · norm_num [h15PostFEIsExternalMissingPairModulus]
  constructor
  · exact (h15PostFEExternalPairMultiplier_eq_one_iff_dvd_product
      6 2 3 (by norm_num) (by norm_num)).mpr (by norm_num)
  · exact h15PostFEExternalAdmissibleMissingNativeSupport_card_eq_modulus
      6 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem h15PostFEExternalPairMultiplier_not_uniformly_two :
    ¬ ∀ p q q' : ℕ,
      h15PostFEIsExternalMissingPairModulus p q q' →
        2 ≤ h15PostFEExternalPairMultiplier p q q' := by
  intro h
  have hbad := h 6 2 3 h15PostFEExternalDensityDegeneracy_example.1
  rw [h15PostFEExternalDensityDegeneracy_example.2.1] at hbad
  omega

end NBMellinTools.NB12
