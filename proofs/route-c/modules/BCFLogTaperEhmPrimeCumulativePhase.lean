import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeVaalerTarget

/-!
# Normalized reciprocal phases in the cumulative prime transform

The Bernoulli quotient contributes a factor `m / (k+1)`, which cancels the
`1/m` in the Möbius coefficient.  The Vaaler phase is therefore a normalized
Möbius polynomial with the cumulative taper as its only real amplitude.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativePhase

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmAlternativeRoutes
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFourierResonanceAudit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeTaper
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeVaaler
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeVaalerTarget
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeTruncatedFormula
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.QuadraticInteraction

/-- Reciprocal-phase form after cancelling the Bernoulli quotient denominator
against the Möbius coefficient's `1/m`. -/
noncomputable def ehmPrimeCumulativeNormalizedPhaseForm
    (h : ℤ) (X k : ℕ) : ℂ :=
  (1 / ((((k + 1 : ℕ) : ℝ) : ℂ))) *
    ∑ m ∈ Finset.Icc 1 (2 * X),
      ((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
        (ehmPrimeCumulativeOuterTaper X k m : ℂ)) *
          ehmVaalerRationalPhase h (k + 1) 1 m

/-- Exact cancellation of the apparent `1/m` loss. -/
theorem ehmPrimeCumulativePhaseForm_eq_normalized
    (h : ℤ) (X k : ℕ) :
    ehmPrimeCumulativePhaseForm h X k =
      ehmPrimeCumulativeNormalizedPhaseForm h X k := by
  classical
  unfold ehmPrimeCumulativePhaseForm
    ehmPrimeCumulativeNormalizedPhaseForm ehmPrimeCumulativeMobiusCoeff
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hm0 : (m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hm).1)
  have hm0c : (((m : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hm0
  have hk0 : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  push_cast
  field_simp [hm0, hk0]
  apply (div_eq_iff hm0c).2
  push_cast
  ring

/-- Frequency-first Vaaler expansion in normalized Möbius-polynomial form. -/
theorem ehmPrimeCumulativeVaalerApprox_eq_normalizedFrequencySum
    (V : VaalerSawtoothPackage)
    (H X k : ℕ) :
    ehmPrimeCumulativeVaalerApprox V H X k =
      ∑ h ∈ V.frequencies H,
        V.coefficient H h *
          ehmPrimeCumulativeNormalizedPhaseForm h X k := by
  rw [ehmPrimeCumulativeVaalerApprox_eq_frequencySum]
  apply Finset.sum_congr rfl
  intro h _
  rw [ehmPrimeCumulativePhaseForm_eq_normalized]

/-- Reconstructed prefix with the Vaaler term displayed directly as its
normalized reciprocal-frequency sum. -/
noncomputable def ehmPrimeCumulativeNormalizedReconstructedPrefix
    (V : VaalerSawtoothPackage) (H X J k : ℕ) : ℂ :=
  if k < J then
    -ehmPrimeCumulativeKernelTransform ehmR1SmoothPart X k +
      (∑ h ∈ V.frequencies H,
        V.coefficient H h *
          ehmPrimeCumulativeNormalizedPhaseForm h X k) +
        ehmPrimeCumulativeVaalerError V H X k -
          ehmPrimeCumulativeKernelTransform ehmR1IntegerEndpointPart X k
  else 0

/-- The normalized reciprocal-phase prefix is exactly the earlier Vaaler
reconstruction. -/
theorem ehmPrimeCumulativeVaalerReconstructedPrefix_eq_normalized
    (V : VaalerSawtoothPackage) (H X J k : ℕ) :
    ehmPrimeCumulativeVaalerReconstructedPrefix V H X J k =
      ehmPrimeCumulativeNormalizedReconstructedPrefix V H X J k := by
  unfold ehmPrimeCumulativeVaalerReconstructedPrefix
    ehmPrimeCumulativeNormalizedReconstructedPrefix
  by_cases hkJ : k < J
  · simp only [if_pos hkJ]
    rw [ehmPrimeCumulativeVaalerApprox_eq_normalizedFrequencySum]
  · simp [hkJ]

/-- Exact common-height remainder identity in normalized reciprocal-phase
coordinates. -/
theorem ehmPrimeTruncatedRemainderDyadicAggregate_eq_normalizedPhaseVariation
    (D : EhmPrimeDiscrepancyTruncatedModeData)
    (V : VaalerSawtoothPackage) (H Y X J : ℕ) (hJ : 2 * X ≤ J) :
    ehmPrimeTruncatedRemainderDyadicAggregate D Y X J =
      ∑ k ∈ Finset.Icc X J,
        ehmPrimeCumulativeNormalizedReconstructedPrefix V H X J k *
          (D.remainderMode Y k - D.remainderMode Y (k + 1)) := by
  rw [ehmPrimeTruncatedRemainderDyadicAggregate_eq_cumulativeVaalerVariation
    D V H Y X J hJ]
  apply Finset.sum_congr rfl
  intro k _
  rw [ehmPrimeCumulativeVaalerReconstructedPrefix_eq_normalized]

/-- Final analytic gate stated directly with normalized reciprocal-phase
Möbius polynomials and all correction-bearing pieces retained. -/
structure EhmPrimeTruncatedNormalizedPhaseControl
    (D : EhmPrimeDiscrepancyTruncatedModeData)
    (V : VaalerSawtoothPackage) where
  height : ℕ → ℕ → ℕ
  frequencyCutoff : ℕ → ℕ → ℕ
  structuredEta : ℕ → ℝ
  remainderEta : ℕ → ℝ
  structuredEta_nonneg : ∀ X, 0 ≤ structuredEta X
  remainderEta_nonneg : ∀ X, 0 ≤ remainderEta X
  structuredEta_tendsto_zero : Tendsto structuredEta atTop (nhds 0)
  remainderEta_tendsto_zero : Tendsto remainderEta atTop (nhds 0)
  cofinal_control : ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      2 * X ≤ J ∧
      ehmPrimeTruncatedStructuredDyadicSum D (height X J) X J ≤
        ((ehmDyadicNBlock X).card : ℝ) * structuredEta X ∧
      ‖∑ k ∈ Finset.Icc X J,
          ehmPrimeCumulativeNormalizedReconstructedPrefix V
              (frequencyCutoff X J) X J k *
            (D.remainderMode (height X J) k -
              D.remainderMode (height X J) (k + 1))‖ ≤
        ((ehmDyadicNBlock X).card : ℝ) * remainderEta X

/-- Normalized phase control instantiates the cumulative Vaaler gate. -/
noncomputable def EhmPrimeTruncatedNormalizedPhaseControl.toCumulativeVaaler
    {D : EhmPrimeDiscrepancyTruncatedModeData}
    {V : VaalerSawtoothPackage}
    (HT : EhmPrimeTruncatedNormalizedPhaseControl D V) :
    EhmPrimeTruncatedCumulativeVaalerControl D V where
  height := HT.height
  frequencyCutoff := HT.frequencyCutoff
  structuredEta := HT.structuredEta
  remainderEta := HT.remainderEta
  structuredEta_nonneg := HT.structuredEta_nonneg
  remainderEta_nonneg := HT.remainderEta_nonneg
  structuredEta_tendsto_zero := HT.structuredEta_tendsto_zero
  remainderEta_tendsto_zero := HT.remainderEta_tendsto_zero
  cofinal_control X hX :=
    (HT.cofinal_control X hX).mono fun J hJ ↦ by
      refine ⟨hJ.1, hJ.2.1, ?_⟩
      simpa only [ehmPrimeCumulativeVaalerReconstructedPrefix_eq_normalized]
        using hJ.2.2

/-- A proof of the normalized signed reciprocal-phase gate closes the
Báez--Duarte route. -/
theorem baezDuarteCriterion_of_ehmPrimeTruncatedNormalizedPhaseControl
    {D : EhmPrimeDiscrepancyTruncatedModeData}
    {V : VaalerSawtoothPackage}
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (HT : EhmPrimeTruncatedNormalizedPhaseControl D V) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmPrimeTruncatedCumulativeVaalerControl HS
    HT.toCumulativeVaaler

end RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativePhase
