/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFELiteralCommonPeriodValue

/-!
# NB12zzzac: literal frozen-row collision energy

For one fixed H15 frequency row, this file squares the complete lifted
correction value over its full common period.  Finite additive orthogonality
then gives an exact collision-indicator ledger, with the missing trace and all
four Estermann orientations kept inside the same square.

The arithmetic coefficients themselves depend on the H15 row `r`.  The
collision identity below therefore applies to the phase orbit with that row
frozen.  A final theorem records the exact diagonal relation for a varying
finite row support; it deliberately does not replace those varying
coefficients by one fixed coefficient system.
-/

open AddChar Complex ZMod
open scoped BigOperators ComplexConjugate

namespace NBMellinTools.NB12

/-- Full-period energy of the literal H15 coefficient system with its
arithmetic row `r` frozen while the additive phase traverses the period. -/
noncomputable def h15PostFEActualFrozenRowOrbitEnergy
    (n g U Q r : ℕ) (t : ℝ)
    [NeZero (h15PostFEActualCommonSuperperiod n g U Q)] : ℝ :=
  h15PostFECommonPeriodCorrectionEnergy
    (h15PostFEJointMissingAtomSupport
      (h15PostFEResidueModulusSupport n g U Q)
      (h15PostFEReducedMissingResidues n g U Q))
    (h15PostFEActualCommonPeriodMissingCoefficient n g U Q r t)
    (h15PostFELiftedMissingFrequency
      (h15PostFEActualCommonSuperperiod n g U Q))
    (h15PostFEActualOrientedPairSupport n g U Q)
    (h15PostFEActualCommonPeriodPairCoefficient n g U Q r t)
    (fun y => h15PostFELiftedPairFrequency
      (h15PostFEActualCommonSuperperiod n g U Q)
      y.2.1 y.2.2 y.1)

/-- Exact literal collision normal form for one frozen H15 row. -/
theorem h15PostFEActualFrozenRowOrbitEnergy_eq_collisionIndicators
    (n g U Q r : ℕ) (t : ℝ) (hQ : 0 < Q) :
    letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
      ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
    h15PostFEActualFrozenRowOrbitEnergy n g U Q r t =
      (∑ i ∈ h15PostFEJointMissingAtomSupport
          (h15PostFEResidueModulusSupport n g U Q)
          (h15PostFEReducedMissingResidues n g U Q),
        ∑ j ∈ h15PostFEJointMissingAtomSupport
            (h15PostFEResidueModulusSupport n g U Q)
            (h15PostFEReducedMissingResidues n g U Q),
          (((h15PostFEActualCommonPeriodMissingCoefficient n g U Q r t i *
                  conj (h15PostFEActualCommonPeriodMissingCoefficient
                    n g U Q r t j)) *
                (if h15PostFELiftedMissingFrequency
                      (h15PostFEActualCommonSuperperiod n g U Q) i =
                    h15PostFELiftedMissingFrequency
                      (h15PostFEActualCommonSuperperiod n g U Q) j
                  then (h15PostFEActualCommonSuperperiod n g U Q : ℂ) else 0)).re -
            ((h15PostFEActualCommonPeriodMissingCoefficient n g U Q r t i *
                  h15PostFEActualCommonPeriodMissingCoefficient n g U Q r t j) *
                (if h15PostFELiftedMissingFrequency
                        (h15PostFEActualCommonSuperperiod n g U Q) i +
                      h15PostFELiftedMissingFrequency
                        (h15PostFEActualCommonSuperperiod n g U Q) j = 0
                  then (h15PostFEActualCommonSuperperiod n g U Q : ℂ) else 0)).re) / 2) +
      2 * (∑ i ∈ h15PostFEJointMissingAtomSupport
          (h15PostFEResidueModulusSupport n g U Q)
          (h15PostFEReducedMissingResidues n g U Q),
        ∑ k ∈ h15PostFEActualOrientedPairSupport n g U Q,
          (((h15PostFEActualCommonPeriodMissingCoefficient n g U Q r t i *
                  h15PostFEActualCommonPeriodPairCoefficient n g U Q r t k) *
                (if h15PostFELiftedMissingFrequency
                        (h15PostFEActualCommonSuperperiod n g U Q) i +
                      h15PostFELiftedPairFrequency
                        (h15PostFEActualCommonSuperperiod n g U Q)
                        k.2.1 k.2.2 k.1 = 0
                  then (h15PostFEActualCommonSuperperiod n g U Q : ℂ) else 0)).im +
            ((h15PostFEActualCommonPeriodMissingCoefficient n g U Q r t i *
                  conj (h15PostFEActualCommonPeriodPairCoefficient
                    n g U Q r t k)) *
                (if h15PostFELiftedMissingFrequency
                      (h15PostFEActualCommonSuperperiod n g U Q) i =
                    h15PostFELiftedPairFrequency
                      (h15PostFEActualCommonSuperperiod n g U Q)
                      k.2.1 k.2.2 k.1
                  then (h15PostFEActualCommonSuperperiod n g U Q : ℂ) else 0)).im) / 2) +
      ∑ k ∈ h15PostFEActualOrientedPairSupport n g U Q,
        ∑ l ∈ h15PostFEActualOrientedPairSupport n g U Q,
          (((h15PostFEActualCommonPeriodPairCoefficient n g U Q r t k *
                  h15PostFEActualCommonPeriodPairCoefficient n g U Q r t l) *
                (if h15PostFELiftedPairFrequency
                        (h15PostFEActualCommonSuperperiod n g U Q)
                        k.2.1 k.2.2 k.1 +
                      h15PostFELiftedPairFrequency
                        (h15PostFEActualCommonSuperperiod n g U Q)
                        l.2.1 l.2.2 l.1 = 0
                  then (h15PostFEActualCommonSuperperiod n g U Q : ℂ) else 0)).re +
            ((h15PostFEActualCommonPeriodPairCoefficient n g U Q r t k *
                  conj (h15PostFEActualCommonPeriodPairCoefficient
                    n g U Q r t l)) *
                (if h15PostFELiftedPairFrequency
                      (h15PostFEActualCommonSuperperiod n g U Q)
                      k.2.1 k.2.2 k.1 =
                    h15PostFELiftedPairFrequency
                      (h15PostFEActualCommonSuperperiod n g U Q)
                      l.2.1 l.2.2 l.1
                  then (h15PostFEActualCommonSuperperiod n g U Q : ℂ) else 0)).re) / 2 := by
  letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
    ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
  exact h15PostFECommonPeriodCorrectionEnergy_eq_collisionIndicators
    (h15PostFEJointMissingAtomSupport
      (h15PostFEResidueModulusSupport n g U Q)
      (h15PostFEReducedMissingResidues n g U Q))
    (h15PostFEActualCommonPeriodMissingCoefficient n g U Q r t)
    (h15PostFELiftedMissingFrequency
      (h15PostFEActualCommonSuperperiod n g U Q))
    (h15PostFEActualOrientedPairSupport n g U Q)
    (h15PostFEActualCommonPeriodPairCoefficient n g U Q r t)
    (fun y => h15PostFELiftedPairFrequency
      (h15PostFEActualCommonSuperperiod n g U Q)
      y.2.1 y.2.2 y.1)

/-- The actual finite H15 row energy.  Unlike the frozen orbit above, every
summand uses coefficients built from its own row index. -/
noncomputable def h15PostFEActualVaryingRowEnergy
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) : ℝ :=
  ∑ r ∈ frequencySupport,
    (h15PostFEActualJointCorrectionTransform n g U Q r t) ^ 2

/-- Exact diagonal embedding of the varying-row energy into the lifted
common-period values.  This is intentionally a diagonal `r ↦ (r,r)` identity,
not a fixed-coefficient Parseval assertion. -/
theorem h15PostFEActualVaryingRowEnergy_eq_commonPeriodDiagonal
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) (hQ : 0 < Q) :
    letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
      ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
    h15PostFEActualVaryingRowEnergy frequencySupport n g U Q t =
      ∑ r ∈ frequencySupport,
        (h15PostFEActualCommonPeriodValue n g U Q r t
          (r : ZMod (h15PostFEActualCommonSuperperiod n g U Q))) ^ 2 := by
  letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
    ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
  unfold h15PostFEActualVaryingRowEnergy
  apply Finset.sum_congr rfl
  intro r _hr
  rw [h15PostFEActualJointCorrectionTransform_eq_commonPeriodValue
    n g U Q r t hQ]

end NBMellinTools.NB12
