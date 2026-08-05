/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15DirectAdditiveReassembly

/-!
# NB15: audit of the proposed Euler--Maclaurin / van der Corput /
Bettin--Chandee activation routes

This exploration module records the decisive arithmetic phase diagnosis.
The numerator stored in an H15 Laurent row is already an inverse residue.
The Estermann functional equation applies a second modular inversion, so the
post-functional-equation phase is the direct additive product

`e_q(± r u)`,

not the Kloosterman-fraction phase `e_q(± r u⁻¹)` estimated in
Bettin--Chandee Theorem 1.

The first theorem below gives a concrete, inhabited counterexample to an
identification of those two phase families.  The next two theorems isolate
the exact resonant rows of the direct phase: on reduced H15 rows, every
frequency divisible by the modulus has phase one in both orientations.
Consequently second-derivative van der Corput estimates cannot control this
sector, and a direct additive large sieve reaches only the already-proved
quadratic frequency threshold.

No asymptotic estimate, literature theorem, or RH statement is assumed here.
This file is deliberately excluded from the public `NBMellinTools` umbrella.
-/

open scoped BigOperators Topology LSeries.notation
open Complex

namespace NBMellinTools.NB12

/-! ## A non-vacuous phase stop test -/

/-- At the reduced residue `u = 2 (mod 5)`, the actual direct H15 phase is
not the Bettin--Chandee inverse-residue phase.  This concrete witness rules
out treating the two phase families as definitionally or extensionally
identical. -/
theorem h15DirectPhase_ne_bettinChandeeInversePhase_example :
    h15DirectAdditiveUnitPhase .positive 1 2 5 ≠
      bettinChandeeSignedUnitPhase .positive 1 2 5 := by
  intro h
  unfold h15DirectAdditiveUnitPhase at h
  simp only [OfNat.ofNat_ne_zero, ↓reduceDIte] at h
  rw [bettinChandeeSignedUnitPhase_positive_eq_h15 1 2 5 (by norm_num),
    bblsAdditiveCharacter_rat_eq_stdAddChar] at h
  rw [ZMod.injective_stdAddChar.eq_iff] at h
  have hcop : Nat.Coprime 2 5 := by norm_num
  have h' : (2 : ZMod 5) =
      (((ZMod.unitOfCoprime 2 hcop)⁻¹ : (ZMod 5)ˣ).val) := by
    simpa [bblsEstermannInverseNumerator,
      bblsEstermannInverseResidue] using h
  have htwo : (2 : ZMod 5) * 2 = 1 := by
    calc
      (2 : ZMod 5) * 2 =
          (((ZMod.unitOfCoprime 2 hcop)⁻¹ : (ZMod 5)ˣ).val) * 2 :=
        congrArg (fun z : ZMod 5 => z * 2) h'
      _ = 1 := by
        simpa only [ZMod.coe_unitOfCoprime] using
          (Units.inv_mul (ZMod.unitOfCoprime 2 hcop))
  have hne : (4 : ZMod 5) ≠ 1 := by decide
  exact hne (by norm_num at htwo; exact htwo)

/-! ## Exact direct-phase resonance -/

/-- The direct phase is identically one whenever the modulus divides the
frequency--numerator product.  Both Estermann orientations have the same
resonance set. -/
theorem h15DirectAdditiveUnitPhase_eq_one_of_dvd
    (sign : BettinChandeeUnitSign) (r u q : ℕ)
    (hq : q ≠ 0) (hdiv : q ∣ r * u) :
    h15DirectAdditiveUnitPhase sign r u q = 1 := by
  unfold h15DirectAdditiveUnitPhase
  rw [dif_neg hq]
  letI : NeZero q := ⟨hq⟩
  have hz : ((r * u : ℕ) : ZMod q) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact hdiv
  cases sign <;> simp only
  · rw [mul_comm, ← Nat.cast_mul, hz]
    simp
  · rw [neg_mul, mul_comm, ← Nat.cast_mul, hz, neg_zero]
    simp

/-- On a reduced H15 row, `q ∣ r*u` is exactly `q ∣ r`.  Thus the
resonant quotient fibers are not an artefact of non-coprime rows. -/
theorem h15DirectAdditive_resonance_dvd_iff
    {r u q : ℕ} (huq : Nat.Coprime u q) :
    q ∣ r * u ↔ q ∣ r := by
  exact huq.symm.dvd_mul_right

/-- Every reduced H15 row is therefore resonant at frequencies divisible
by its modulus. -/
theorem h15DirectAdditiveUnitPhase_eq_one_of_modulus_dvd_frequency
    (sign : BettinChandeeUnitSign) (r u q : ℕ)
    (hq : q ≠ 0) (huq : Nat.Coprime u q) (hqr : q ∣ r) :
    h15DirectAdditiveUnitPhase sign r u q = 1 := by
  apply h15DirectAdditiveUnitPhase_eq_one_of_dvd sign r u q hq
  exact (h15DirectAdditive_resonance_dvd_iff huq).2 hqr

/-! ## Quantitative large-sieve stop test -/

/-- The elementary direct-additive large-sieve scale has no power saving at
the quadratic transition.  This aliases the exact exponent calculation at
the point relevant to the proposed Path A fallback. -/
theorem h15Aristotle_directLargeSieve_quadratic_stopTest :
    h15DirectAdditiveBalancedExponent 2 = 0 :=
  h15DirectAdditiveBalancedExponent_two

/-- A negative balanced exponent occurs only strictly above the quadratic
frequency threshold. -/
theorem h15Aristotle_directLargeSieve_saves_iff (kappa : ℝ) :
    h15DirectAdditiveBalancedExponent kappa < 0 ↔ 2 < kappa :=
  h15DirectAdditiveBalancedExponent_neg_iff kappa

end NBMellinTools.NB12
