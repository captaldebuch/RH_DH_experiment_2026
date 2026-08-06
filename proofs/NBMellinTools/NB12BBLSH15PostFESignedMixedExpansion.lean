/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFESignedCorrelationDefects

/-!
# NB12zzzaI: literal expansion of the signed affine mixed sector

The affine Laurent/pair transform contains two mathematically distinct
pieces: the frequency-free Laurent missing trace and the four signed
Estermann pair populations.  This file keeps the common divisor-square
weight and endpoint transform outside neither piece.  It expands the signed
mixed energy exactly and packages the antiparallel defect as one explicit
correction-preserving residual.

No absolute value, asymptotic estimate, or nonzero-height cancellation is
used.
-/

open Filter
open scoped BigOperators

namespace NBMellinTools.NB12

/-- Frequency-free Laurent missing-residue transform. -/
noncomputable def h15PostFELaurentMissingFrequencyTransform
    (n g U Q r : ℕ) (t : ℝ) : ℝ :=
  h15PostFEJointMissingTransform
    (h15PostFEResidueModulusSupport n g U Q)
    (h15PostFEReducedMissingResidues n g U Q)
    (h15PostFEResidueFiberLaurentMeanCoefficientWithoutFrequency
      n g U Q t) r

/-- Sum of the four frequency-free signed Estermann pair populations before
the common archimedean normalization. -/
noncomputable def h15PostFEFourOrientationPairFrequencyTransform
    (n g U Q r : ℕ) (t : ℝ) : ℝ :=
  h15PostFEJointPairTransform .positive .positive
      (h15PostFEReducedOrderedPairResidueSupport n g U Q)
      (h15PostFEOrderedPairCollectedScalarWithoutFrequency n g U Q t) r t +
    h15PostFEJointPairTransform .positive .negative
      (h15PostFEReducedOrderedPairResidueSupport n g U Q)
      (h15PostFEOrderedPairCollectedScalarWithoutFrequency n g U Q t) r t +
    h15PostFEJointPairTransform .negative .positive
      (h15PostFEReducedOrderedPairResidueSupport n g U Q)
      (h15PostFEOrderedPairCollectedScalarWithoutFrequency n g U Q t) r t +
    h15PostFEJointPairTransform .negative .negative
      (h15PostFEReducedOrderedPairResidueSupport n g U Q)
      (h15PostFEOrderedPairCollectedScalarWithoutFrequency n g U Q t) r t

theorem h15PostFELaurentPairFrequencyTransform_eq_missing_add_pair
    (n g U Q r : ℕ) (t : ℝ) :
    h15PostFELaurentPairFrequencyTransform n g U Q r t =
      -4 * h15PostFELaurentMissingFrequencyTransform n g U Q r t +
        4 * h15PostFEFourOrientationPairFrequencyTransform
          n g U Q r t /
          (2 * h15PairedHyperbolicCoefficient t) := by
  rfl

/-- Lambda-weighted endpoint--Laurent-missing correlation. -/
noncomputable def h15PostFEWeightedEndpointLaurentMissingMixedEnergy
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) : ℝ :=
  ∑ r ∈ frequencySupport,
    Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t) *
      h15PostFEEndpointFrequencyTransform n g U Q r *
      h15PostFELaurentMissingFrequencyTransform n g U Q r t

/-- Lambda-weighted endpoint correlation with all four signed pair
populations retained together. -/
noncomputable def h15PostFEWeightedEndpointPairMixedEnergy
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) : ℝ :=
  ∑ r ∈ frequencySupport,
    Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t) *
      h15PostFEEndpointFrequencyTransform n g U Q r *
      h15PostFEFourOrientationPairFrequencyTransform n g U Q r t

/-- Exact literal split of the signed affine mixed sector. -/
theorem h15PostFEWeightedMixedEnergy_eq_laurentMissing_add_pair
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) :
    h15PostFEWeightedEndpointLaurentPairMixedEnergy
        frequencySupport n g U Q t =
      -4 * h15PostFEWeightedEndpointLaurentMissingMixedEnergy
          frequencySupport n g U Q t +
        4 * h15PostFEWeightedEndpointPairMixedEnergy
          frequencySupport n g U Q t /
          (2 * h15PairedHyperbolicCoefficient t) := by
  unfold h15PostFEWeightedEndpointLaurentPairMixedEnergy
    h15PostFEWeightedEndpointLaurentMissingMixedEnergy
    h15PostFEWeightedEndpointPairMixedEnergy
  simp_rw [h15PostFELaurentPairFrequencyTransform_eq_missing_add_pair]
  calc
    (∑ r ∈ frequencySupport,
        Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t) *
          h15PostFEEndpointFrequencyTransform n g U Q r *
          (-4 * h15PostFELaurentMissingFrequencyTransform n g U Q r t +
            4 * h15PostFEFourOrientationPairFrequencyTransform
                n g U Q r t /
              (2 * h15PairedHyperbolicCoefficient t))) =
      ∑ r ∈ frequencySupport,
        (-4 *
            (Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t) *
              h15PostFEEndpointFrequencyTransform n g U Q r *
              h15PostFELaurentMissingFrequencyTransform n g U Q r t) +
          (4 / (2 * h15PairedHyperbolicCoefficient t)) *
            (Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t) *
              h15PostFEEndpointFrequencyTransform n g U Q r *
              h15PostFEFourOrientationPairFrequencyTransform
                n g U Q r t)) := by
        apply Finset.sum_congr rfl
        intro r _hr
        ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      ring

/-- Explicit residual whose vanishing is precisely antiparallel alignment. -/
noncomputable def h15PostFEAffineAlignmentResidual
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) : ℝ :=
  Real.sqrt (h15PostFEEndpointFrequencyEnergy frequencySupport n g U Q) *
      Real.sqrt (h15PostFEWeightedLaurentPairFrequencyEnergy
        frequencySupport n g U Q t) -
    4 * h15PostFEWeightedEndpointLaurentMissingMixedEnergy
      frequencySupport n g U Q t +
    4 * h15PostFEWeightedEndpointPairMixedEnergy
      frequencySupport n g U Q t /
      (2 * h15PairedHyperbolicCoefficient t)

theorem h15PostFEAffineAntiparallelDefect_eq_two_mul_alignmentResidual
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) :
    h15PostFEAffineAntiparallelDefect frequencySupport n g U Q t =
      2 * h15PostFEAffineAlignmentResidual
        frequencySupport n g U Q t := by
  unfold h15PostFEAffineAntiparallelDefect
    h15PostFEAffineAlignmentResidual
  rw [h15PostFEWeightedMixedEnergy_eq_laurentMissing_add_pair]
  ring

theorem h15PostFEAffineAlignmentResidual_nonneg
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) :
    0 ≤ h15PostFEAffineAlignmentResidual frequencySupport n g U Q t := by
  have h := h15PostFEAffineAntiparallelDefect_nonneg
    frequencySupport n g U Q t
  rw [h15PostFEAffineAntiparallelDefect_eq_two_mul_alignmentResidual] at h
  linarith

/-- Antiparallel-defect decay is equivalent to decay of its explicit literal
alignment residual. -/
theorem tendsto_h15PostFEAffineAntiparallelDefect_zero_iff_alignmentResidual
    (frequencySupport : ℕ → Finset ℕ)
    (n g U Q : ℕ → ℕ) (t : ℕ → ℝ) :
    Tendsto
        (fun k => h15PostFEAffineAntiparallelDefect
          (frequencySupport k) (n k) (g k) (U k) (Q k) (t k))
        atTop (nhds 0) ↔
      Tendsto
        (fun k => h15PostFEAffineAlignmentResidual
          (frequencySupport k) (n k) (g k) (U k) (Q k) (t k))
        atTop (nhds 0) := by
  constructor
  · intro h
    have hhalf := h.const_mul (1 / 2 : ℝ)
    convert hhalf using 1 <;>
      simp only [h15PostFEAffineAntiparallelDefect_eq_two_mul_alignmentResidual,
        mul_zero] <;> ring
  · intro h
    simpa only [h15PostFEAffineAntiparallelDefect_eq_two_mul_alignmentResidual,
      mul_zero] using h.const_mul 2

end NBMellinTools.NB12
