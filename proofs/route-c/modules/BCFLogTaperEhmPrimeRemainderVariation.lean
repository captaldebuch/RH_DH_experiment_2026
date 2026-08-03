import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmPrimeRemainderKernel

/-!
# Variation control for the common-height prime remainder

The global Abel kernel has exact zero mass, so the truncated explicit-formula
remainder is controlled by its discrete variation.  This module connects that
finite estimate to the existing dyadic H15 closure interface.

It also records the precise limitation of pointwise convergence in the
truncation height: it makes the remainder arbitrarily small for every fixed
finite rectangle, but it does not control the finite zero modes at the same
chosen height.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeRemainderVariation

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeRemainderKernel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeTruncatedFormula
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge

/-- Discrete variation of the common-height remainder at the prime index
`k`. -/
noncomputable def ehmPrimeTruncatedRemainderVariation
    (H : EhmPrimeDiscrepancyTruncatedModeData) (Y k : ℕ) : ℝ :=
  ‖H.remainderMode Y k - H.remainderMode Y (k + 1)‖

/-- Pointwise convergence supplied by a genuine symmetric explicit formula.
No such formula is asserted here. -/
structure EhmPrimeTruncatedRemainderPointwiseConvergence
    (H : EhmPrimeDiscrepancyTruncatedModeData) : Prop where
  tendsto_zero : ∀ k : ℕ,
    Tendsto (fun Y ↦ H.remainderMode Y k) atTop (nhds 0)

/-- Pointwise convergence of the remainder implies convergence of each
discrete variation. -/
theorem tendsto_ehmPrimeTruncatedRemainderVariation_zero
    {H : EhmPrimeDiscrepancyTruncatedModeData}
    (HC : EhmPrimeTruncatedRemainderPointwiseConvergence H)
    (k : ℕ) :
    Tendsto (fun Y ↦ ehmPrimeTruncatedRemainderVariation H Y k)
      atTop (nhds 0) := by
  unfold ehmPrimeTruncatedRemainderVariation
  simpa using (HC.tendsto_zero k).sub (HC.tendsto_zero (k + 1)) |>.norm

/-- On a fixed finite rectangle, the variation-weighted kernel cost tends
to zero with the common truncation height. -/
theorem tendsto_ehmPrimeTruncatedRemainderVariationKernelCost_zero
    {H : EhmPrimeDiscrepancyTruncatedModeData}
    (HC : EhmPrimeTruncatedRemainderPointwiseConvergence H)
    (X J : ℕ) :
    Tendsto
      (fun Y ↦ ehmPrimeDyadicAbelVariationKernelCost
        (ehmPrimeTruncatedRemainderVariation H Y) X J)
      atTop (nhds 0) := by
  unfold ehmPrimeDyadicAbelVariationKernelCost
  simpa using tendsto_finsetSum (Finset.Icc X J) (fun k _ ↦
    (tendsto_ehmPrimeTruncatedRemainderVariation_zero HC k).mul_const _)

/-- The complete dyadic remainder aggregate tends to zero at every fixed
finite `(X,J)` rectangle.  This uses the signed kernel expansion; no rowwise
absolute value is introduced. -/
theorem tendsto_ehmPrimeTruncatedRemainderDyadicAggregate_zero
    {H : EhmPrimeDiscrepancyTruncatedModeData}
    (HC : EhmPrimeTruncatedRemainderPointwiseConvergence H)
    (X J : ℕ) (hJ : 2 * X ≤ J) :
    Tendsto
      (fun Y ↦ ehmPrimeTruncatedRemainderDyadicAggregate H Y X J)
      atTop (nhds 0) := by
  simp_rw [ehmPrimeTruncatedRemainderDyadicAggregate_eq_abelAggregate,
    ehmPrimeDyadicAbelAggregate_eq_kernel_sum _ X J hJ]
  simpa using tendsto_finsetSum (Finset.Icc X J) (fun k _ ↦
    (HC.tendsto_zero k).mul_const _)

/-- Hence one common height makes the remainder as small as desired on any
fixed finite rectangle. -/
theorem exists_height_norm_ehmPrimeTruncatedRemainderDyadicAggregate_le
    {H : EhmPrimeDiscrepancyTruncatedModeData}
    (HC : EhmPrimeTruncatedRemainderPointwiseConvergence H)
    (X J : ℕ) (hJ : 2 * X ≤ J) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ Y : ℕ,
      ‖ehmPrimeTruncatedRemainderDyadicAggregate H Y X J‖ ≤ epsilon := by
  have ht := tendsto_ehmPrimeTruncatedRemainderDyadicAggregate_zero HC X J hJ
  rw [Metric.tendsto_atTop] at ht
  obtain ⟨Y, hY⟩ := ht epsilon hepsilon
  refine ⟨Y, ?_⟩
  simpa [dist_zero_right] using (hY Y le_rfl).le

/-! ## Joint asymptotic interface -/

/-- Sufficient H15 data formulated with a discrete-variation envelope for
the common-height remainder.  The finite structured modes and the remainder
use the same height, and the complete dyadic aggregation occurs before the
variation-kernel bound. -/
structure EhmPrimeTruncatedDyadicVariationControl
    (H : EhmPrimeDiscrepancyTruncatedModeData) where
  height : ℕ → ℕ → ℕ
  structuredEta : ℕ → ℝ
  variationEta : ℕ → ℝ
  variationEnvelope : ℕ → ℕ → ℕ → ℝ
  structuredEta_nonneg : ∀ X, 0 ≤ structuredEta X
  variationEta_nonneg : ∀ X, 0 ≤ variationEta X
  structuredEta_tendsto_zero : Tendsto structuredEta atTop (nhds 0)
  variationEta_tendsto_zero : Tendsto variationEta atTop (nhds 0)
  cofinal_control : ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      2 * X ≤ J ∧
      ehmPrimeTruncatedStructuredDyadicSum H (height X J) X J ≤
        ((ehmDyadicNBlock X).card : ℝ) * structuredEta X ∧
      (∀ k ∈ Finset.Icc X J,
        ‖H.remainderMode (height X J) k -
            H.remainderMode (height X J) (k + 1)‖ ≤
          variationEnvelope X J k) ∧
      ehmPrimeDyadicAbelVariationKernelCost
          (variationEnvelope X J) X J ≤
        ((ehmDyadicNBlock X).card : ℝ) * variationEta X

/-- Variation control supplies the earlier global separated-control
interface. -/
noncomputable def EhmPrimeTruncatedDyadicVariationControl.toSeparated
    {H : EhmPrimeDiscrepancyTruncatedModeData}
    (HT : EhmPrimeTruncatedDyadicVariationControl H) :
    EhmPrimeTruncatedDyadicSeparatedControl H where
  height := HT.height
  structuredEta := HT.structuredEta
  remainderEta := HT.variationEta
  structuredEta_nonneg := HT.structuredEta_nonneg
  remainderEta_nonneg := HT.variationEta_nonneg
  structuredEta_tendsto_zero := HT.structuredEta_tendsto_zero
  remainderEta_tendsto_zero := HT.variationEta_tendsto_zero
  cofinal_control X hX :=
    (HT.cofinal_control X hX).mono fun J hJ ↦ by
      refine ⟨hJ.1, hJ.2.1, ?_⟩
      exact (norm_ehmPrimeTruncatedRemainderDyadicAggregate_le_variationKernelCost
        H (HT.variationEnvelope X J) (HT.height X J) X J hJ.1
          hJ.2.2.1).trans hJ.2.2.2

/-- The joint structured-mode and remainder-variation estimate closes the
Báez--Duarte criterion. -/
theorem baezDuarteCriterion_of_ehmPrimeTruncatedDyadicVariationControl
    {H : EhmPrimeDiscrepancyTruncatedModeData}
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (HT : EhmPrimeTruncatedDyadicVariationControl H) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmPrimeTruncatedDyadicSeparated HS HT.toSeparated

end RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeRemainderVariation
