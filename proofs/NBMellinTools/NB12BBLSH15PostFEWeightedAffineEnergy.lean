/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEAffineFrequencyTransform

/-!
# NB12zzzaG: weighted affine energy decomposition

Squaring the exact affine transform produces three finite sectors: the
endpoint square, twice the signed endpoint--Laurent/pair mixed term, and the
divisor-square-weighted Laurent/pair square.  This is the varying-row energy
identity for which a future analytic estimate is actually required.
-/

open scoped BigOperators

namespace NBMellinTools.NB12

noncomputable def h15PostFEEndpointFrequencyEnergy
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) : ℝ :=
  ∑ r ∈ frequencySupport,
    (h15PostFEEndpointFrequencyTransform n g U Q r) ^ 2

noncomputable def h15PostFEWeightedEndpointLaurentPairMixedEnergy
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) : ℝ :=
  ∑ r ∈ frequencySupport,
    Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t) *
      h15PostFEEndpointFrequencyTransform n g U Q r *
      h15PostFELaurentPairFrequencyTransform n g U Q r t

noncomputable def h15PostFEWeightedLaurentPairFrequencyEnergy
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) : ℝ :=
  ∑ r ∈ frequencySupport,
    (Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t)) ^ 2 *
      (h15PostFELaurentPairFrequencyTransform n g U Q r t) ^ 2

/-- Exact endpoint/mixed/weighted-square decomposition of the actual
varying-row energy. -/
theorem h15PostFEActualVaryingRowEnergy_eq_weightedAffineSectors
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) :
    h15PostFEActualVaryingRowEnergy frequencySupport n g U Q t =
      h15PostFEEndpointFrequencyEnergy frequencySupport n g U Q +
        2 * h15PostFEWeightedEndpointLaurentPairMixedEnergy
          frequencySupport n g U Q t +
        h15PostFEWeightedLaurentPairFrequencyEnergy
          frequencySupport n g U Q t := by
  unfold h15PostFEActualVaryingRowEnergy
    h15PostFEEndpointFrequencyEnergy
    h15PostFEWeightedEndpointLaurentPairMixedEnergy
    h15PostFEWeightedLaurentPairFrequencyEnergy
  simp_rw [h15PostFEActualJointCorrectionTransform_eq_endpoint_add_frequencyNormSq_mul]
  calc
    (∑ r ∈ frequencySupport,
        (h15PostFEEndpointFrequencyTransform n g U Q r +
          Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t) *
            h15PostFELaurentPairFrequencyTransform n g U Q r t) ^ 2) =
      ∑ r ∈ frequencySupport,
        ((h15PostFEEndpointFrequencyTransform n g U Q r) ^ 2 +
          2 * (Complex.normSq
              (h15DirectAdditiveFrequencyCoefficient r t) *
            h15PostFEEndpointFrequencyTransform n g U Q r *
            h15PostFELaurentPairFrequencyTransform n g U Q r t) +
          (Complex.normSq
              (h15DirectAdditiveFrequencyCoefficient r t)) ^ 2 *
            (h15PostFELaurentPairFrequencyTransform n g U Q r t) ^ 2) := by
      apply Finset.sum_congr rfl
      intro r _hr
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.mul_sum]

theorem h15PostFEEndpointFrequencyEnergy_nonneg
    (frequencySupport : Finset ℕ) (n g U Q : ℕ) :
    0 ≤ h15PostFEEndpointFrequencyEnergy frequencySupport n g U Q := by
  unfold h15PostFEEndpointFrequencyEnergy
  positivity

theorem h15PostFEWeightedLaurentPairFrequencyEnergy_nonneg
    (frequencySupport : Finset ℕ) (n g U Q : ℕ) (t : ℝ) :
    0 ≤ h15PostFEWeightedLaurentPairFrequencyEnergy
      frequencySupport n g U Q t := by
  unfold h15PostFEWeightedLaurentPairFrequencyEnergy
  positivity

/-- If the full energy is small, the signed mixed sector must cancel the two
nonnegative square sectors.  This exact rearrangement prevents treating the
mixed term as an independent error. -/
theorem two_mul_h15PostFEWeightedMixedEnergy_eq
    (frequencySupport : Finset ℕ) (n g U Q : ℕ) (t : ℝ) :
    2 * h15PostFEWeightedEndpointLaurentPairMixedEnergy
        frequencySupport n g U Q t =
      h15PostFEActualVaryingRowEnergy frequencySupport n g U Q t -
        h15PostFEEndpointFrequencyEnergy frequencySupport n g U Q -
        h15PostFEWeightedLaurentPairFrequencyEnergy
          frequencySupport n g U Q t := by
  rw [h15PostFEActualVaryingRowEnergy_eq_weightedAffineSectors]
  ring

end NBMellinTools.NB12
