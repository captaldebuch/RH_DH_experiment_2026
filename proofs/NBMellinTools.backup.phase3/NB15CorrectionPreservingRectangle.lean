/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB15CertifiedMellinPlancherel
import NBMellinTools.NB15EstermannRowAssembly

/-!
# The concrete correction-preserving H15 rectangle

`NB12BBLSH15Rectangle` proves the closed-rectangle identity for the literal
finite H15 Estermann row family.  This file supplies the missing certified
normalization: the retained correction is the actual NB8 quadratic
correction, and the elementary endpoint is exactly the remaining certified
Gram/endpoint sector.

The resulting `BBLSCorrectionPreservingRectangleData` is constructed from
the genuine boundary integrals.  Its decomposition is therefore not a
tautological choice of arbitrary bulk terms.

This is still a finite closed-contour identity.  It does not identify a
vertical edge with the certified critical-line numerator, and it proves no
asymptotic decay.
-/

open scoped BigOperators

namespace NBMellinTools.NB15

open Complex
open NBMellinTools.NB8
open NBMellinTools.NB12

/-! ## The certified elementary endpoint -/

/-- The part of the certified elementary/endpoint ledger remaining after
the NB8 constant-plus-linear correction is kept as its own sector. -/
noncomputable def h15ContourElementaryEndpoint (n : ℕ) : ℂ :=
  ((oneBasedEstermannElementaryInterior (logTaperLength n) +
    oneBasedVasyuninEndpoint (logTaperLength n) : ℝ) : ℂ)

/-- Exact split of the previously certified endpoint ledger into the
retained NB8 correction and the non-correction elementary endpoint. -/
theorem h15CertifiedElementaryEndpointLedger_eq_correction_add_endpoint
    (n : ℕ) :
    (h15CertifiedElementaryEndpointLedger n : ℂ) =
      (preFECorrection n : ℂ) + h15ContourElementaryEndpoint n := by
  unfold h15CertifiedElementaryEndpointLedger h15ContourElementaryEndpoint
  push_cast
  ring

/-! ## Concrete normalized rectangle values -/

/-- The closed boundary of the literal active H15 aggregate, normalized by
`2*pi*i` and with the certified correction and endpoint attached. -/
noncomputable def h15NormalizedClosedRectangleValue
    (n : ℕ) (σL σR T : ℝ) : ℂ :=
  (preFECorrection n : ℂ) + h15ContourElementaryEndpoint n +
    (2 * (Real.pi : ℂ) * I)⁻¹ *
      rectangularBoundaryIntegral (h15ActiveContourAggregate n)
        (symmetricLowerCorner σL T) (symmetricUpperCorner σR T)

/-- The identically normalized closed boundary of the completely
pole-subtracted H15 aggregate. -/
noncomputable def h15NormalizedPoleSubtractedBoundary
    (n : ℕ) (σL σR T : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ *
    rectangularBoundaryIntegral (h15AllPoleRemoved n)
      (symmetricLowerCorner σL T) (symmetricUpperCorner σR T)

theorem h15NormalizedPoleSubtractedBoundary_eq_zero
    (n : ℕ) (σL σR T : ℝ)
    (hσ : σL ≤ σR) (hR2 : σR < 2) :
    h15NormalizedPoleSubtractedBoundary n σL σR T = 0 := by
  unfold h15NormalizedPoleSubtractedBoundary
  rw [rectangularBoundaryIntegral_h15AllPoleRemoved n σL σR T hσ hR2]
  ring

/-! ## Actual H15 inhabitant of the generic ledger interface -/

/-- The generic correction-preserving rectangle interface instantiated by
the literal H15 rows and the certified NB8 correction/endpoint sectors.

The proof uses the genuine H15 rectangle theorem and the holomorphic closed
boundary of `h15AllPoleRemoved`; the decomposition is not put into the
definitions of the two boundary values. -/
noncomputable def h15CorrectionPreservingRectangleData
    (n : ℕ) (σL σR T : ℝ)
    (hL : σL < 0) (hR : 1 < σR) (hR2 : σR < 2) (hT : 0 < T) :
    BBLSCorrectionPreservingRectangleData
      (h15ContourDamping n) (h15ContourDamping_pos n)
      (preFECorrection n : ℂ)
      (h15LaurentRowWeight (N := logTaperLength n))
      (h15LaurentRow (N := logTaperLength n)) where
  normalizedRectangleValue :=
    h15NormalizedClosedRectangleValue n σL σR T
  poleSubtractedInterior :=
    h15NormalizedPoleSubtractedBoundary n σL σR T
  elementaryEndpoint := h15ContourElementaryEndpoint n
  decomposition := by
    have hσ : σL ≤ σR :=
      le_of_lt (lt_trans hL (lt_trans zero_lt_one hR))
    rw [h15NormalizedPoleSubtractedBoundary_eq_zero n σL σR T hσ hR2]
    unfold h15NormalizedClosedRectangleValue bblsFullCorrectionLedger
    rw [rectangularBoundaryIntegral_h15ActiveContourAggregate
      n σL σR T hL hR hR2 hT]
    unfold h15ContourResidueLedger h15GlobalFirstOrderCoefficient
      h15GlobalAdditionalResidue
    have hfactor : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
      exact mul_ne_zero
        (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
    rw [← mul_assoc, inv_mul_cancel₀ hfactor, one_mul]
    ring

/-- Fully expanded four-sector ledger for the concrete H15 rectangle. -/
theorem h15NormalizedClosedRectangleValue_eq_four_sectors
    (n : ℕ) (σL σR T : ℝ)
    (hL : σL < 0) (hR : 1 < σR) (hR2 : σR < 2) (hT : 0 < T) :
    h15NormalizedClosedRectangleValue n σL σR T =
      bblsCorrectionFinitePartGap
          (h15ContourDamping n) (h15ContourDamping_pos n)
          (preFECorrection n : ℂ)
          (h15LaurentRowWeight (N := logTaperLength n))
          (h15LaurentRow (N := logTaperLength n)) +
        bblsFirstOrderPolarResidual
          (h15ContourDamping n)
          (h15LaurentRowWeight (N := logTaperLength n))
          (h15LaurentRow (N := logTaperLength n)) +
        h15GlobalAdditionalResidue n +
        h15ContourElementaryEndpoint n := by
  let H := h15CorrectionPreservingRectangleData
    n σL σR T hL hR hR2 hT
  have hexpanded := H.decomposition_expanded
  dsimp [H, h15CorrectionPreservingRectangleData] at hexpanded
  rw [h15NormalizedPoleSubtractedBoundary_eq_zero n σL σR T
    (le_of_lt (lt_trans hL (lt_trans zero_lt_one hR))) hR2] at hexpanded
  simpa [h15GlobalAdditionalResidue] using hexpanded

/-! ## Connection to the already certified physical energy -/

/-- Exact physical-energy ledger in the same certified endpoint
normalization.  The inverse damping is essential: the finite rectangle sees
the damped `s=1` residue, whereas the NB8 energy contains its undamped
amplitude. -/
theorem certifiedCriticalLineEnergy_eq_contourResidueLedger
    (n : ℕ) :
    certifiedCriticalLineEnergy n =
      h15CertifiedElementaryEndpointLedger n +
        (((h15ContourDamping n : ℂ)⁻¹ *
          h15GlobalAdditionalResidue n).im) := by
  rw [← logTaperL2Error_eq_certifiedCriticalLineEnergy]
  exact logTaperL2Error_eq_elementaryEndpoint_add_rescaledContourResidue_im n

/-- The same identity with the certified correction and non-correction
endpoint displayed separately. -/
theorem certifiedCriticalLineEnergy_eq_correction_add_endpoint_add_residue
    (n : ℕ) :
    (certifiedCriticalLineEnergy n : ℂ) =
      (preFECorrection n : ℂ) + h15ContourElementaryEndpoint n +
        ((((h15ContourDamping n : ℂ)⁻¹ *
          h15GlobalAdditionalResidue n).im : ℝ) : ℂ) := by
  have henergy := congrArg (fun x : ℝ => (x : ℂ))
    (certifiedCriticalLineEnergy_eq_contourResidueLedger n)
  push_cast at henergy
  rw [henergy,
    h15CertifiedElementaryEndpointLedger_eq_correction_add_endpoint]

end NBMellinTools.NB15
