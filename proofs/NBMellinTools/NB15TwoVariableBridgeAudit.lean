/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB15PhysicalContourSingularityMismatch
import NBMellinTools.NB15CorrectionPreservingRectangle

/-!
# Audit of the proposed two-variable H15 bridge

The physical critical-line numerator is a linear spectral object.  Its
Hermitian pairing, followed by integration in the spectral height, is the
certified Nyman--Beurling energy.  The active Estermann aggregate is already
part of a quadratic Gram decomposition: the certified energy sees its
undamped residue at `w = 1`, together with the elementary/correction ledger.

Consequently these objects are not pointwise boundary values of the same
one-variable function.  Merely adding a second variable does not fix that
problem: two arbitrary slices admit a tautological additive splice whenever
their corner values agree.  The first section proves this precise stop test.

The second section records the non-vacuous bridge that is actually certified:
the integral of the physical Hermitian diagonal equals the retained
elementary ledger plus the rescaled `w = 1` Estermann residue.  The physical
spectral height and the auxiliary contour variable remain distinct, and the
certified cubic pole at `w = 0` is retained rather than identified with the
physical numerator.

No asymptotic decay estimate is proved here.
-/

open scoped BigOperators ComplexConjugate Topology

namespace NBMellinTools.NB15

open Complex Filter MeasureTheory
open NBMellinTools.NB8
open NBMellinTools.NB12

/-! ## Boundary-slice stop test -/

/-- The tautological additive splice of two one-variable functions.  It is
included to show that the mere existence of a two-variable function with two
prescribed slices has no analytic content. -/
noncomputable def additiveTwoVariableSplice
    (physical contour : ℂ → ℂ) (u₀ : ℂ) (u w : ℂ) : ℂ :=
  physical u + contour w - physical u₀

theorem additiveTwoVariableSplice_contourSlice
    (physical contour : ℂ → ℂ) (u₀ w : ℂ) :
    additiveTwoVariableSplice physical contour u₀ u₀ w = contour w := by
  simp [additiveTwoVariableSplice]

theorem additiveTwoVariableSplice_physicalSlice
    (physical contour : ℂ → ℂ) (u₀ w₀ u : ℂ)
    (hcorner : contour w₀ = physical u₀) :
    additiveTwoVariableSplice physical contour u₀ u w₀ = physical u := by
  simp [additiveTwoVariableSplice, hcorner]

/-- Two exact slices of one two-variable function must agree at their
intersection.  Apart from this scalar compatibility, the preceding additive
splice shows that slice recovery alone is vacuous. -/
theorem twoBoundarySlices_force_cornerCompatibility
    (T : ℂ → ℂ → ℂ) (physical contour : ℂ → ℂ)
    (u₀ w₀ : ℂ)
    (hphysical : ∀ u, T u w₀ = physical u)
    (hcontour : ∀ w, T u₀ w = contour w) :
    physical u₀ = contour w₀ := by
  exact (hphysical u₀).symm.trans (hcontour w₀)

/-- The certified singularity mismatch supplies an anchor at which the raw
physical and contour functions are incompatible. -/
theorem exists_incompatible_h15_common_anchor :
    ∃ s : ℂ,
      certifiedMellinNumerator 2 s ≠ h15ActiveContourAggregate 2 s := by
  by_contra h
  push Not at h
  exact certifiedMellinNumerator_two_ne_h15ActiveContourAggregate (funext h)

/-- Hence there is a certified anchor at which no two-variable function can
have the entire physical function as one slice and the entire raw Estermann
aggregate as the other.  Keeping variable names distinct is not sufficient;
the two sides must first be compared at the correct quadratic/residue level. -/
theorem exists_anchor_with_no_raw_twoBoundaryBridge :
    ∃ s : ℂ, ¬ ∃ T : ℂ → ℂ → ℂ,
      (∀ u, T u s = certifiedMellinNumerator 2 u) ∧
      (∀ w, T s w = h15ActiveContourAggregate 2 w) := by
  rcases exists_incompatible_h15_common_anchor with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  rintro ⟨T, hphysical, hcontour⟩
  exact hs (twoBoundarySlices_force_cornerCompatibility
    T (certifiedMellinNumerator 2) (h15ActiveContourAggregate 2)
      s s hphysical hcontour)

/-! ## The certified role-differentiated bridge -/

/-- The physical Hermitian diagonal density.  Its variable is the real
spectral height; it is not the Mellin--Barnes contour variable. -/
noncomputable def h15PhysicalPairingDensity (n : ℕ) (t : ℝ) : ℝ :=
  (certifiedMellinPairingKernel n
    (conj (certifiedCriticalLinePoint t))
    (certifiedCriticalLinePoint t)).re

theorem h15PhysicalPairingDensity_eq_normSq (n : ℕ) (t : ℝ) :
    h15PhysicalPairingDensity n t =
      Complex.normSq (certifiedCriticalLineNumerator n t) := by
  rw [h15PhysicalPairingDensity,
    certifiedMellinPairingKernel_criticalDiagonal]
  norm_num

/-- The auxiliary `w = 1` residue carrier of the active Estermann aggregate.
It is deliberately a function of the contour variable alone. -/
noncomputable def h15AuxiliaryResidueCarrier (n : ℕ) (w : ℂ) : ℂ :=
  (w - 1) * h15ActiveContourAggregate n w

/-- The auxiliary contour retains the certified cubic pole at `w = 0`. -/
theorem h15AuxiliaryContour_cubicPole (n : ℕ) :
    Tendsto (fun w : ℂ => w ^ 3 * h15ActiveContourAggregate n w)
      (𝓝[≠] 0) (𝓝 (h15GlobalThirdOrderCoefficient n)) :=
  tendsto_cubic_mul_h15ActiveContourAggregate_zero n

/-- The same contour has the certified additional residue at `w = 1`. -/
theorem h15AuxiliaryResidueCarrier_tendsto (n : ℕ) :
    Tendsto (h15AuxiliaryResidueCarrier n) (𝓝[≠] 1)
      (𝓝 (h15GlobalAdditionalResidue n)) := by
  exact tendsto_bblsFiniteActiveAggregate_residue_one
    (h15ContourDamping n) (h15ContourDamping_pos n)
    (h15LaurentRowWeight (N := logTaperLength n))
    (h15LaurentRow (N := logTaperLength n))

/-- Exact recovery of the certified physical numerator on the critical line.
This is independent of the auxiliary contour variable. -/
theorem h15PhysicalNumerator_exactRecovery (n : ℕ) (t : ℝ) :
    certifiedMellinNumerator n (certifiedCriticalLinePoint t) =
      certifiedCriticalLineNumerator n t :=
  certifiedMellinNumerator_criticalLine n t

/-- The genuine finite bridge.  The left side is the physical Hermitian
pairing integrated in the spectral height.  The right side is the retained
elementary/correction ledger plus the undamped value recovered from the
auxiliary `w = 1` residue.  No pointwise identification of the physical
numerator with the Estermann aggregate occurs. -/
theorem h15PhysicalPairingIntegral_eq_contourResidueLedger
    (n : ℕ) :
    (1 / (2 * Real.pi)) * ∫ t : ℝ, h15PhysicalPairingDensity n t =
      h15CertifiedElementaryEndpointLedger n +
        (((h15ContourDamping n : ℂ)⁻¹ *
          h15GlobalAdditionalResidue n).im) := by
  unfold h15PhysicalPairingDensity
  rw [← certifiedCriticalLineEnergy_eq_pairingDiagonalIntegral]
  exact certifiedCriticalLineEnergy_eq_contourResidueLedger n

end NBMellinTools.NB15
