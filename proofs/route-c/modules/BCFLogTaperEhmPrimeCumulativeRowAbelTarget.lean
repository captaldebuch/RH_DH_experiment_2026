import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeRowAbel

/-!
# Signed H15 target in cumulative row-Abel coordinates

The endpoint and variation terms of the outer row Abel transform must not be
bounded separately.  This module inserts their exact signed difference into
the complete Vaaler reconstruction and then into the common-height prime
remainder variation.  Smooth, Vaaler-error, and integer-endpoint modes remain
inside the same signed expression.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeRowAbelTarget

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmAlternativeRoutes
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativePhase
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeRowAbel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeVaaler
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeTruncatedFormula
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.QuadraticInteraction

/-- The full reconstructed prefix with every reciprocal-frequency row written
as its exact endpoint-minus-variation Abel form. -/
noncomputable def ehmPrimeCumulativeRowAbelReconstructedPrefix
    (V : VaalerSawtoothPackage) (H X J k : ℕ) : ℂ :=
  if k < J then
    -ehmPrimeCumulativeKernelTransform ehmR1SmoothPart X k +
      (∑ h ∈ V.frequencies H,
        V.coefficient H h *
          ((1 / ((((k + 1 : ℕ) : ℝ) : ℂ))) *
            ehmPrimeTaperedRowAbelForm h k X
              (ehmPrimeCumulativeRowAbelLength X k))) +
        ehmPrimeCumulativeVaalerError V H X k -
          ehmPrimeCumulativeKernelTransform ehmR1IntegerEndpointPart X k
  else 0

/-- Exact replacement of the normalized Vaaler reconstruction by row-Abel
coordinates throughout the active range. -/
theorem ehmPrimeCumulativeNormalizedReconstructedPrefix_eq_rowAbel
    (V : VaalerSawtoothPackage) (H X J k : ℕ)
    (hX : 2 ≤ X) (hXk : X ≤ k) :
    ehmPrimeCumulativeNormalizedReconstructedPrefix V H X J k =
      ehmPrimeCumulativeRowAbelReconstructedPrefix V H X J k := by
  unfold ehmPrimeCumulativeNormalizedReconstructedPrefix
    ehmPrimeCumulativeRowAbelReconstructedPrefix
  by_cases hkJ : k < J
  · simp only [if_pos hkJ]
    apply congrArg (fun z : ℂ ↦
      -ehmPrimeCumulativeKernelTransform ehmR1SmoothPart X k + z +
        ehmPrimeCumulativeVaalerError V H X k -
          ehmPrimeCumulativeKernelTransform ehmR1IntegerEndpointPart X k)
    apply Finset.sum_congr rfl
    intro h _
    rw [ehmPrimeCumulativeNormalizedPhaseForm_eq_rowAbel_of_le
      h X k hX hXk]
  · simp [hkJ]

/-- The complete signed common-height variation in row-Abel coordinates. -/
theorem ehmPrimeTruncatedRemainderDyadicAggregate_eq_rowAbelVariation
    (D : EhmPrimeDiscrepancyTruncatedModeData)
    (V : VaalerSawtoothPackage) (H Y X J : ℕ)
    (hX : 2 ≤ X) (hJ : 2 * X ≤ J) :
    ehmPrimeTruncatedRemainderDyadicAggregate D Y X J =
      ∑ k ∈ Finset.Icc X J,
        ehmPrimeCumulativeRowAbelReconstructedPrefix V H X J k *
          (D.remainderMode Y k - D.remainderMode Y (k + 1)) := by
  rw [ehmPrimeTruncatedRemainderDyadicAggregate_eq_normalizedPhaseVariation
    D V H Y X J hJ]
  apply Finset.sum_congr rfl
  intro k hk
  rw [ehmPrimeCumulativeNormalizedReconstructedPrefix_eq_rowAbel
    V H X J k hX (Finset.mem_Icc.mp hk).1]

/-- The remaining analytic hypothesis with the outer Abel endpoint and
variation kept coupled to every retained H15 mode. -/
structure EhmPrimeTruncatedRowAbelControl
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
          ehmPrimeCumulativeRowAbelReconstructedPrefix V
              (frequencyCutoff X J) X J k *
            (D.remainderMode (height X J) k -
              D.remainderMode (height X J) (k + 1))‖ ≤
        ((ehmDyadicNBlock X).card : ℝ) * remainderEta X

/-- Row-Abel control supplies the normalized reciprocal-phase gate. -/
noncomputable def EhmPrimeTruncatedRowAbelControl.toNormalizedPhase
    {D : EhmPrimeDiscrepancyTruncatedModeData}
    {V : VaalerSawtoothPackage}
    (HT : EhmPrimeTruncatedRowAbelControl D V) :
    EhmPrimeTruncatedNormalizedPhaseControl D V where
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
      have hsum :
          (∑ k ∈ Finset.Icc X J,
              ehmPrimeCumulativeNormalizedReconstructedPrefix V
                  (HT.frequencyCutoff X J) X J k *
                (D.remainderMode (HT.height X J) k -
                  D.remainderMode (HT.height X J) (k + 1))) =
            ∑ k ∈ Finset.Icc X J,
              ehmPrimeCumulativeRowAbelReconstructedPrefix V
                  (HT.frequencyCutoff X J) X J k *
                (D.remainderMode (HT.height X J) k -
                  D.remainderMode (HT.height X J) (k + 1)) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [ehmPrimeCumulativeNormalizedReconstructedPrefix_eq_rowAbel
          V (HT.frequencyCutoff X J) X J k hX (Finset.mem_Icc.mp hk).1]
      rw [hsum]
      exact hJ.2.2

/-- A signed proof in row-Abel coordinates closes the Báez--Duarte route. -/
theorem baezDuarteCriterion_of_ehmPrimeTruncatedRowAbelControl
    {D : EhmPrimeDiscrepancyTruncatedModeData}
    {V : VaalerSawtoothPackage}
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (HT : EhmPrimeTruncatedRowAbelControl D V) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmPrimeTruncatedNormalizedPhaseControl HS
    HT.toNormalizedPhase

end RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeRowAbelTarget
