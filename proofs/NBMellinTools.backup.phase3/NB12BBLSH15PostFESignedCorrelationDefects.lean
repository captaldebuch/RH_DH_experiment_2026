/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEWeightedAffineEnergy

/-!
# NB12zzzaH: signed correlation defects for the affine H15 energy

The exact affine energy has two nonnegative square sectors and one signed
mixed sector.  Finite Cauchy--Schwarz shows that the mixed sector is bounded
below by minus the geometric mean of the square sectors.  Consequently the
full energy is exactly the sum of two nonnegative defects:

* the square of the difference of the two sector norms;
* the failure of the signed mixed sector to attain the negative
  Cauchy--Schwarz boundary.

This is a sharp stop test.  Any analytic H15 closure must establish both norm
balance and asymptotic antiparallel alignment.  No asymptotic estimate is
proved in this file.
-/

open Filter
open scoped BigOperators

namespace NBMellinTools.NB12

/-- The two nonnegative affine sectors must have asymptotically matching
square-root sizes. -/
noncomputable def h15PostFEAffineNormImbalanceDefect
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) : ℝ :=
  (Real.sqrt (h15PostFEEndpointFrequencyEnergy frequencySupport n g U Q) -
    Real.sqrt (h15PostFEWeightedLaurentPairFrequencyEnergy
      frequencySupport n g U Q t)) ^ 2

/-- The signed mixed sector must approach the negative Cauchy--Schwarz
boundary.  This defect measures its failure to do so. -/
noncomputable def h15PostFEAffineAntiparallelDefect
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) : ℝ :=
  2 *
    (Real.sqrt (h15PostFEEndpointFrequencyEnergy frequencySupport n g U Q) *
        Real.sqrt (h15PostFEWeightedLaurentPairFrequencyEnergy
          frequencySupport n g U Q t) +
      h15PostFEWeightedEndpointLaurentPairMixedEnergy
        frequencySupport n g U Q t)

/-- Sharp finite Cauchy--Schwarz lower bound for the signed weighted mixed
sector. -/
theorem neg_sqrt_mul_sqrt_le_h15PostFEWeightedMixedEnergy
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) :
    -(Real.sqrt (h15PostFEEndpointFrequencyEnergy
        frequencySupport n g U Q) *
      Real.sqrt (h15PostFEWeightedLaurentPairFrequencyEnergy
        frequencySupport n g U Q t)) ≤
      h15PostFEWeightedEndpointLaurentPairMixedEnergy
        frequencySupport n g U Q t := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt frequencySupport
    (fun r => -h15PostFEEndpointFrequencyTransform n g U Q r)
    (fun r => Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t) *
      h15PostFELaurentPairFrequencyTransform n g U Q r t)
  have hleft :
      (∑ r ∈ frequencySupport,
          (-h15PostFEEndpointFrequencyTransform n g U Q r) *
            (Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t) *
              h15PostFELaurentPairFrequencyTransform n g U Q r t)) =
        -h15PostFEWeightedEndpointLaurentPairMixedEnergy
          frequencySupport n g U Q t := by
    unfold h15PostFEWeightedEndpointLaurentPairMixedEnergy
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r _hr
    ring
  have hendpoint :
      (∑ r ∈ frequencySupport,
          (-h15PostFEEndpointFrequencyTransform n g U Q r) ^ 2) =
        h15PostFEEndpointFrequencyEnergy frequencySupport n g U Q := by
    unfold h15PostFEEndpointFrequencyEnergy
    apply Finset.sum_congr rfl
    intro r _hr
    ring
  have hlaurent :
      (∑ r ∈ frequencySupport,
          (Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t) *
            h15PostFELaurentPairFrequencyTransform n g U Q r t) ^ 2) =
        h15PostFEWeightedLaurentPairFrequencyEnergy
          frequencySupport n g U Q t := by
    unfold h15PostFEWeightedLaurentPairFrequencyEnergy
    apply Finset.sum_congr rfl
    intro r _hr
    ring
  rw [hleft, hendpoint, hlaurent] at hcs
  linarith

theorem h15PostFEAffineNormImbalanceDefect_nonneg
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) :
    0 ≤ h15PostFEAffineNormImbalanceDefect
      frequencySupport n g U Q t := by
  unfold h15PostFEAffineNormImbalanceDefect
  positivity

theorem h15PostFEAffineAntiparallelDefect_nonneg
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) :
    0 ≤ h15PostFEAffineAntiparallelDefect
      frequencySupport n g U Q t := by
  unfold h15PostFEAffineAntiparallelDefect
  have h := neg_sqrt_mul_sqrt_le_h15PostFEWeightedMixedEnergy
    frequencySupport n g U Q t
  linarith

/-- Exact sharp-defect decomposition of the literal varying-row energy. -/
theorem h15PostFEActualVaryingRowEnergy_eq_affineDefects
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) :
    h15PostFEActualVaryingRowEnergy frequencySupport n g U Q t =
      h15PostFEAffineNormImbalanceDefect frequencySupport n g U Q t +
        h15PostFEAffineAntiparallelDefect frequencySupport n g U Q t := by
  rw [h15PostFEActualVaryingRowEnergy_eq_weightedAffineSectors]
  unfold h15PostFEAffineNormImbalanceDefect
    h15PostFEAffineAntiparallelDefect
  have hendpoint := h15PostFEEndpointFrequencyEnergy_nonneg
    frequencySupport n g U Q
  have hlaurent := h15PostFEWeightedLaurentPairFrequencyEnergy_nonneg
    frequencySupport n g U Q t
  rw [sub_sq]
  rw [Real.sq_sqrt hendpoint, Real.sq_sqrt hlaurent]
  ring

/-- The full energy controls each sharp defect separately. -/
theorem h15PostFEAffineNormImbalanceDefect_le_actualEnergy
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) :
    h15PostFEAffineNormImbalanceDefect frequencySupport n g U Q t ≤
      h15PostFEActualVaryingRowEnergy frequencySupport n g U Q t := by
  rw [h15PostFEActualVaryingRowEnergy_eq_affineDefects]
  exact le_add_of_nonneg_right
    (h15PostFEAffineAntiparallelDefect_nonneg frequencySupport n g U Q t)

/-- The full energy also controls failure of antiparallel signed alignment. -/
theorem h15PostFEAffineAntiparallelDefect_le_actualEnergy
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) :
    h15PostFEAffineAntiparallelDefect frequencySupport n g U Q t ≤
      h15PostFEActualVaryingRowEnergy frequencySupport n g U Q t := by
  rw [h15PostFEActualVaryingRowEnergy_eq_affineDefects]
  exact le_add_of_nonneg_left
    (h15PostFEAffineNormImbalanceDefect_nonneg frequencySupport n g U Q t)

/-- Along arbitrary parameter schedules, vanishing of the complete literal
energy is equivalent to simultaneous vanishing of norm imbalance and failure
of antiparallel alignment.  This is the exact asymptotic stop test. -/
theorem tendsto_h15PostFEActualVaryingRowEnergy_zero_iff_affineDefects
    (frequencySupport : ℕ → Finset ℕ)
    (n g U Q : ℕ → ℕ) (t : ℕ → ℝ) :
    Tendsto
        (fun k => h15PostFEActualVaryingRowEnergy
          (frequencySupport k) (n k) (g k) (U k) (Q k) (t k))
        atTop (nhds 0) ↔
      Tendsto
          (fun k => h15PostFEAffineNormImbalanceDefect
            (frequencySupport k) (n k) (g k) (U k) (Q k) (t k))
          atTop (nhds 0) ∧
        Tendsto
          (fun k => h15PostFEAffineAntiparallelDefect
            (frequencySupport k) (n k) (g k) (U k) (Q k) (t k))
          atTop (nhds 0) := by
  constructor
  · intro henergy
    constructor
    · apply squeeze_zero'
      · exact Filter.Eventually.of_forall fun k =>
          h15PostFEAffineNormImbalanceDefect_nonneg
            (frequencySupport k) (n k) (g k) (U k) (Q k) (t k)
      · exact Filter.Eventually.of_forall fun k =>
          h15PostFEAffineNormImbalanceDefect_le_actualEnergy
            (frequencySupport k) (n k) (g k) (U k) (Q k) (t k)
      · exact henergy
    · apply squeeze_zero'
      · exact Filter.Eventually.of_forall fun k =>
          h15PostFEAffineAntiparallelDefect_nonneg
            (frequencySupport k) (n k) (g k) (U k) (Q k) (t k)
      · exact Filter.Eventually.of_forall fun k =>
          h15PostFEAffineAntiparallelDefect_le_actualEnergy
            (frequencySupport k) (n k) (g k) (U k) (Q k) (t k)
      · exact henergy
  · rintro ⟨hnorm, halignment⟩
    simpa only [h15PostFEActualVaryingRowEnergy_eq_affineDefects, zero_add] using
      hnorm.add halignment

end NBMellinTools.NB12
