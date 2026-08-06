/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEJointTransformInterface

/-!
# NB12zzzn: compatibility audit for post-FE transform estimates

This file compares the exact correction-preserving joint transform with the
two published-tool models already formalized in the active package.

The conclusions are proof-backed stop tests.

* The literal H15 phase after the functional equation is direct.
* A direct-to-inverse relabelling required by the immediate
  Bettin--Chandee application is false already modulo five.
* The formal Bettin--Chandee pair exponent has no fixed-frequency saving,
  even before accounting for the phase failure.
* The direct additive large-sieve exponent has the correct phase but has no
  saving at fixed frequency or at the quadratic transition; it becomes
  negative exactly above that transition.
* A genuine `H15PostFEJointTransformDecayData` estimate acts on the exact
  joint coefficient and the retained missing-residue trace in one expression.

The audit does **not** prove that no future Voronoi, Motohashi, or Kuznetsov
theorem can handle the transform.  It proves that such a theorem must be a
new joint-coefficient, correction-preserving estimate rather than a direct
application of either audited separated-coefficient bound.
-/

open Filter
open scoped Topology

namespace NBMellinTools.NB12

/-! ## Literal phase stop test -/

/-- The direct-to-inverse identification which would be needed to feed the
literal post-functional-equation residue into the inverse-residue phase of
the immediate Bettin--Chandee theorem without an additional transform. -/
def H15PostFEBettinChandeeLiteralPhaseCompatibility : Prop :=
  ∀ (u q : ℕ) [NeZero q] (huq : Nat.Coprime u q),
    ZMod.stdAddChar (u : ZMod q) =
      ZMod.stdAddChar
        (((ZMod.unitOfCoprime u huq)⁻¹ : (ZMod q)ˣ).val)

/-- The required direct-to-inverse identification is false.  The witness is
the reduced residue `2 mod 5`, whose inverse is `3 mod 5`. -/
theorem not_h15PostFEBettinChandeeLiteralPhaseCompatibility :
    ¬ H15PostFEBettinChandeeLiteralPhaseCompatibility := by
  intro H
  exact stdAddChar_zmod_five_direct_ne_inverse
    (H 2 5 (by decide : Nat.Coprime 2 5))

/-! ## Fixed-frequency exponent stop tests -/

/-- A candidate power ledger saves at frequency exponent `kappa` precisely
when its resulting exponent is strictly negative. -/
def H15PostFEPowerSavingAt
    (exponent : ℝ → ℝ) (kappa : ℝ) : Prop :=
  exponent kappa < 0

theorem not_h15PostFEBettinChandeePairPowerSavingAt_zero :
    ¬ H15PostFEPowerSavingAt h15PostFEBettinChandeePairExponent 0 := by
  rw [H15PostFEPowerSavingAt, h15PostFEBettinChandeePairExponent_zero]
  norm_num

theorem not_h15PostFEDirectAdditivePairPowerSavingAt_zero :
    ¬ H15PostFEPowerSavingAt h15PostFEDirectAdditivePairExponent 0 := by
  rw [H15PostFEPowerSavingAt, h15PostFEDirectAdditivePairExponent_zero]
  norm_num

theorem not_h15PostFEDirectAdditivePairPowerSavingAt_two :
    ¬ H15PostFEPowerSavingAt h15PostFEDirectAdditivePairExponent 2 := by
  rw [H15PostFEPowerSavingAt, h15PostFEDirectAdditivePairExponent_two]
  norm_num

theorem h15PostFEDirectAdditivePairPowerSavingAt_iff (kappa : ℝ) :
    H15PostFEPowerSavingAt h15PostFEDirectAdditivePairExponent kappa ↔
      2 < kappa := by
  exact h15PostFEDirectAdditivePairExponent_neg_iff kappa

/-! ## Exact-target compatibility -/

/-- Every inhabitant of the joint decay interface bounds the literal
correction-preserving common-additive transfer, not merely one separated
orientation population. -/
theorem H15PostFEJointTransformDecayData.commonAdditive_estimate
    {g U Q r : ℕ → ℕ} {t : ℕ → ℝ}
    (H : H15PostFEJointTransformDecayData g U Q r t) (N : ℕ) :
    |h15PostFECommonAdditiveBoundaryTransfer
        N (g N) (U N) (Q N) (r N) (t N)| ≤
      H.gain N *
        h15PostFEActualJointCoefficientL1Mass
          N (g N) (U N) (Q N) (r N) (t N) := by
  rw [h15PostFECommonAdditiveBoundaryTransfer_eq_actualJointTransform]
  exact H.estimate N

/-- Compact, mechanically checked outcome of the compatibility audit.

The first conjunct records the actual direct phase.  The next three reject
the two immediate fixed-frequency applications.  The final conjunct records
the exact high-frequency range in which the elementary direct-additive
power ledger does give a saving. -/
def H15PostFEJointTransformCompatibilityAudit : Prop :=
  H15PostFunctionalEquationPhaseIsDirect ∧
    ¬ H15PostFEBettinChandeeLiteralPhaseCompatibility ∧
      ¬ H15PostFEPowerSavingAt h15PostFEBettinChandeePairExponent 0 ∧
        ¬ H15PostFEPowerSavingAt h15PostFEDirectAdditivePairExponent 0 ∧
          ∀ kappa : ℝ,
            H15PostFEPowerSavingAt
                h15PostFEDirectAdditivePairExponent kappa ↔
              2 < kappa

theorem h15PostFEJointTransformCompatibilityAudit :
    H15PostFEJointTransformCompatibilityAudit := by
  exact ⟨h15PostFunctionalEquationPhaseIsDirect,
    not_h15PostFEBettinChandeeLiteralPhaseCompatibility,
    not_h15PostFEBettinChandeePairPowerSavingAt_zero,
    not_h15PostFEDirectAdditivePairPowerSavingAt_zero,
    h15PostFEDirectAdditivePairPowerSavingAt_iff⟩

end NBMellinTools.NB12
