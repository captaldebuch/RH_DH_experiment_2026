import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeVaaler

/-!
# Correction-coupled cumulative Vaaler target

This module substitutes the cumulative Vaaler reconstruction into the exact
second Abel transform of the common-height prime remainder.  It packages the
remaining estimate only after the smooth, reciprocal-phase, Vaaler-error,
endpoint, and explicit-formula variation terms have been recombined.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeVaalerTarget

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmAlternativeRoutes
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeVaaler
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimePrefixCollapse
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeRemainderKernel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeTruncatedFormula
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.QuadraticInteraction

/-- The exact reconstructed prefix, including its terminal zero mode. -/
noncomputable def ehmPrimeCumulativeVaalerReconstructedPrefix
    (V : VaalerSawtoothPackage) (H X J k : ℕ) : ℂ :=
  if k < J then
    -ehmPrimeCumulativeKernelTransform ehmR1SmoothPart X k +
      ehmPrimeCumulativeVaalerApprox V H X k +
        ehmPrimeCumulativeVaalerError V H X k -
          ehmPrimeCumulativeKernelTransform ehmR1IntegerEndpointPart X k
  else 0

/-- The reconstructed expression agrees with the global prime prefix at
every index in the second Abel transform. -/
theorem ehmPrimeDyadicAbelKernelPrefix_eq_reconstructed
    (V : VaalerSawtoothPackage) (H X J k : ℕ)
    (hJ : 2 * X ≤ J) (hk : k ∈ Finset.Icc X J) :
    ehmPrimeDyadicAbelKernelPrefix X J k =
      ehmPrimeCumulativeVaalerReconstructedPrefix V H X J k := by
  by_cases hkJ : k < J
  · rw [ehmPrimeDyadicAbelKernelPrefix_eq_cumulativeVaaler
      V H X J k hJ (Finset.mem_Icc.mp hk).1 hkJ]
    simp [ehmPrimeCumulativeVaalerReconstructedPrefix, hkJ]
  · have hkeq : k = J := Nat.le_antisymm (Finset.mem_Icc.mp hk).2
        (Nat.le_of_not_gt hkJ)
    subst k
    rw [ehmPrimeDyadicAbelKernelPrefix_terminal X J hJ]
    simp [ehmPrimeCumulativeVaalerReconstructedPrefix]

/-- Exact signed variation formula after the cumulative Vaaler lift. -/
theorem ehmPrimeDyadicAbelAggregate_eq_cumulativeVaalerVariation
    (V : VaalerSawtoothPackage) (H : ℕ) (u : ℕ → ℂ)
    (X J : ℕ) (hJ : 2 * X ≤ J) :
    ehmPrimeDyadicAbelAggregate u X J =
      ∑ k ∈ Finset.Icc X J,
        ehmPrimeCumulativeVaalerReconstructedPrefix V H X J k *
          (u k - u (k + 1)) := by
  rw [ehmPrimeDyadicAbelAggregate_eq_variation_kernel_sum u X J hJ]
  apply Finset.sum_congr rfl
  intro k hk
  rw [ehmPrimeDyadicAbelKernelPrefix_eq_reconstructed V H X J k hJ hk]

/-- The common-height explicit-formula remainder in the exact reconstructed
coordinates. -/
theorem ehmPrimeTruncatedRemainderDyadicAggregate_eq_cumulativeVaalerVariation
    (D : EhmPrimeDiscrepancyTruncatedModeData)
    (V : VaalerSawtoothPackage) (H Y X J : ℕ) (hJ : 2 * X ≤ J) :
    ehmPrimeTruncatedRemainderDyadicAggregate D Y X J =
      ∑ k ∈ Finset.Icc X J,
        ehmPrimeCumulativeVaalerReconstructedPrefix V H X J k *
          (D.remainderMode Y k - D.remainderMode Y (k + 1)) := by
  rw [ehmPrimeTruncatedRemainderDyadicAggregate_eq_abelAggregate]
  exact ehmPrimeDyadicAbelAggregate_eq_cumulativeVaalerVariation
    V H (D.remainderMode Y) X J hJ

/-- The remaining analytic gate in cumulative Vaaler coordinates.  The norm
is outside the complete signed `k`-sum; no individual reconstructed mode is
bounded separately. -/
structure EhmPrimeTruncatedCumulativeVaalerControl
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
          ehmPrimeCumulativeVaalerReconstructedPrefix V
              (frequencyCutoff X J) X J k *
            (D.remainderMode (height X J) k -
              D.remainderMode (height X J) (k + 1))‖ ≤
        ((ehmDyadicNBlock X).card : ℝ) * remainderEta X

/-- The exact reconstruction turns the cumulative Vaaler gate into the
existing globally separated truncated-formula control. -/
noncomputable def EhmPrimeTruncatedCumulativeVaalerControl.toSeparated
    {D : EhmPrimeDiscrepancyTruncatedModeData}
    {V : VaalerSawtoothPackage}
    (HT : EhmPrimeTruncatedCumulativeVaalerControl D V) :
    EhmPrimeTruncatedDyadicSeparatedControl D where
  height := HT.height
  structuredEta := HT.structuredEta
  remainderEta := HT.remainderEta
  structuredEta_nonneg := HT.structuredEta_nonneg
  remainderEta_nonneg := HT.remainderEta_nonneg
  structuredEta_tendsto_zero := HT.structuredEta_tendsto_zero
  remainderEta_tendsto_zero := HT.remainderEta_tendsto_zero
  cofinal_control X hX :=
    (HT.cofinal_control X hX).mono fun J hJ ↦ by
      refine ⟨hJ.1, hJ.2.1, ?_⟩
      rw [ehmPrimeTruncatedRemainderDyadicAggregate_eq_cumulativeVaalerVariation
        D V (HT.frequencyCutoff X J) (HT.height X J) X J hJ.1]
      exact hJ.2.2

/-- A proof of the signed cumulative Vaaler gate closes the verified
Báez--Duarte route. -/
theorem baezDuarteCriterion_of_ehmPrimeTruncatedCumulativeVaalerControl
    {D : EhmPrimeDiscrepancyTruncatedModeData}
    {V : VaalerSawtoothPackage}
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (HT : EhmPrimeTruncatedCumulativeVaalerControl D V) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmPrimeTruncatedDyadicSeparated HS HT.toSeparated

end RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeVaalerTarget
