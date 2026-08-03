import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeRowAbelTarget
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmSignedTransferAudit

/-!
# Complete signed row-Abel decay: exact stop theorem

This module keeps the outer Abel endpoint-minus-variation expression, the
common-height prime remainder, and every retained finite correction in one
signed real quantity.

The resulting expression has an important exact normal form: after the
structured modes and the remainder are recombined, it is the original finite
Ehm boundary sum.  It is therefore independent of the explicit-formula
height, the Vaaler package, and the reciprocal-frequency cutoff.  In
particular, pointwise decay of the prime remainder in the height variable
cannot prove decay of the complete expression; the finite structured modes
move by the exactly compensating amount.

The final structure below is consequently not advertised as a newly proved
analytic estimate.  It is proved equivalent, by explicit maps, to the
existing signed finite-boundary gate.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCompleteRowAbelDecay

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeRowAbelTarget
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeTruncatedFormula
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmSignedAverage
open RH.Criteria.NymanBeurling.BCFLogTaperEhmSignedTransferAudit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmUniformBoundary
open RH.Criteria.NymanBeurling.QuadraticInteraction

/-- The complete correction-coupled row-Abel expression.  The norm is not
taken around either the endpoint or variation term: their signed difference
is first multiplied by the common-height prime remainder variation and only
then recombined with the structured endpoint, zero, natural, and
missing-divisor modes. -/
noncomputable def ehmPrimeCompleteRowAbelDyadicExpression
    (D : EhmPrimeDiscrepancyTruncatedModeData)
    (V : VaalerSawtoothPackage)
    (Q Y X J : ℕ) : ℝ :=
  ehmPrimeTruncatedStructuredDyadicSum D Y X J +
    (∑ k ∈ Finset.Icc X J,
      ehmPrimeCumulativeRowAbelReconstructedPrefix V Q X J k *
        (D.remainderMode Y k - D.remainderMode Y (k + 1))).re

/-- Exact reassembly: the complete endpoint-minus-variation expression is
the original finite H15 boundary. -/
theorem ehmPrimeCompleteRowAbelDyadicExpression_eq_boundary
    (D : EhmPrimeDiscrepancyTruncatedModeData)
    (V : VaalerSawtoothPackage)
    (Q Y X J : ℕ) (hX : 2 ≤ X) (hJ : 2 * X ≤ J) :
    ehmPrimeCompleteRowAbelDyadicExpression D V Q Y X J =
      ∑ N ∈ ehmDyadicNBlock X,
        ehmFiniteCoupledBoundaryExpression ehmR1 N J := by
  unfold ehmPrimeCompleteRowAbelDyadicExpression
  rw [← ehmPrimeTruncatedRemainderDyadicAggregate_eq_rowAbelVariation
    D V Q Y X J hX hJ]
  exact (sum_ehmFiniteCoupledBoundaryExpression_eq_truncatedDyadic
    D Y X J hX hJ).symm

/-- The complete expression is independent of every auxiliary analytic
coordinate.  Thus changing the common zero height or reciprocal-frequency
cutoff cannot create decay after the retained corrections are restored. -/
theorem ehmPrimeCompleteRowAbelDyadicExpression_independent
    (D₁ D₂ : EhmPrimeDiscrepancyTruncatedModeData)
    (V₁ V₂ : VaalerSawtoothPackage)
    (Q₁ Y₁ Q₂ Y₂ X J : ℕ) (hX : 2 ≤ X) (hJ : 2 * X ≤ J) :
    ehmPrimeCompleteRowAbelDyadicExpression D₁ V₁ Q₁ Y₁ X J =
      ehmPrimeCompleteRowAbelDyadicExpression D₂ V₂ Q₂ Y₂ X J := by
  rw [ehmPrimeCompleteRowAbelDyadicExpression_eq_boundary
      D₁ V₁ Q₁ Y₁ X J hX hJ,
    ehmPrimeCompleteRowAbelDyadicExpression_eq_boundary
      D₂ V₂ Q₂ Y₂ X J hX hJ]

/-- For a fixed finite rectangle the complete expression is constant in the
common explicit-formula height.  Its height-limit is the finite boundary,
not zero in general. -/
theorem tendsto_ehmPrimeCompleteRowAbelDyadicExpression_height
    (D : EhmPrimeDiscrepancyTruncatedModeData)
    (V : VaalerSawtoothPackage)
    (Q X J : ℕ) (hX : 2 ≤ X) (hJ : 2 * X ≤ J) :
    Tendsto
      (fun Y ↦ ehmPrimeCompleteRowAbelDyadicExpression D V Q Y X J)
      atTop
      (nhds (∑ N ∈ ehmDyadicNBlock X,
        ehmFiniteCoupledBoundaryExpression ehmR1 N J)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards with Y
  exact (ehmPrimeCompleteRowAbelDyadicExpression_eq_boundary
    D V Q Y X J hX hJ).symm

/-- Height-decay of the *complete* expression occurs exactly when the fixed
finite boundary already vanishes.  This is the formal stop test separating
remainder convergence from the genuine outer-scale cancellation problem. -/
theorem tendsto_ehmPrimeCompleteRowAbelDyadicExpression_height_zero_iff
    (D : EhmPrimeDiscrepancyTruncatedModeData)
    (V : VaalerSawtoothPackage)
    (Q X J : ℕ) (hX : 2 ≤ X) (hJ : 2 * X ≤ J) :
    Tendsto
        (fun Y ↦ ehmPrimeCompleteRowAbelDyadicExpression D V Q Y X J)
        atTop (nhds 0) ↔
      (∑ N ∈ ehmDyadicNBlock X,
        ehmFiniteCoupledBoundaryExpression ehmR1 N J) = 0 := by
  constructor
  · intro hzero
    exact (tendsto_nhds_unique hzero
      (tendsto_ehmPrimeCompleteRowAbelDyadicExpression_height
        D V Q X J hX hJ)).symm
  · intro hboundary
    simpa [hboundary] using
      tendsto_ehmPrimeCompleteRowAbelDyadicExpression_height
        D V Q X J hX hJ

/-- The genuine remaining decay statement, with the endpoint-minus-
variation term, prime remainder, and retained corrections all inside one
signed expression. -/
structure EhmPrimeCompleteRowAbelSignedDecay
    (D : EhmPrimeDiscrepancyTruncatedModeData)
    (V : VaalerSawtoothPackage) where
  height : ℕ → ℕ → ℕ
  frequencyCutoff : ℕ → ℕ → ℕ
  eta : ℕ → ℝ
  eta_nonneg : ∀ X, 0 ≤ eta X
  eta_tendsto_zero : Tendsto eta atTop (nhds 0)
  cofinal_bound : ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      2 * X ≤ J ∧
      ehmPrimeCompleteRowAbelDyadicExpression D V
          (frequencyCutoff X J) (height X J) X J ≤
        ((ehmDyadicNBlock X).card : ℝ) * eta X

/-- Complete row-Abel decay is exactly sufficient for the established signed
finite-boundary gate. -/
noncomputable def EhmPrimeCompleteRowAbelSignedDecay.toBoundaryAverage
    {D : EhmPrimeDiscrepancyTruncatedModeData}
    {V : VaalerSawtoothPackage}
    (H : EhmPrimeCompleteRowAbelSignedDecay D V) :
    EhmDyadicSignedBoundaryAverageVanishing where
  eta := H.eta
  eta_nonneg := H.eta_nonneg
  eta_tendsto_zero := H.eta_tendsto_zero
  cofinal_sum_bound X hX :=
    (H.cofinal_bound X hX).mono fun J hJ ↦ by
      rw [← ehmPrimeCompleteRowAbelDyadicExpression_eq_boundary
        D V (H.frequencyCutoff X J) (H.height X J) X J hX hJ.1]
      exact hJ.2

/-- Conversely, every signed finite-boundary estimate supplies the complete
row-Abel estimate, with arbitrary fixed auxiliary coordinates. -/
noncomputable def boundaryAverageToCompleteRowAbel
    (D : EhmPrimeDiscrepancyTruncatedModeData)
    (V : VaalerSawtoothPackage)
    (H : EhmDyadicSignedBoundaryAverageVanishing) :
    EhmPrimeCompleteRowAbelSignedDecay D V where
  height := fun _ _ ↦ 0
  frequencyCutoff := fun _ _ ↦ 0
  eta := H.eta
  eta_nonneg := H.eta_nonneg
  eta_tendsto_zero := H.eta_tendsto_zero
  cofinal_bound X hX := by
    have hlate : ∀ᶠ J : ℕ in atTop, 2 * X ≤ J :=
      eventually_ge_atTop (2 * X)
    exact ((H.cofinal_sum_bound X hX).and_eventually hlate).mono
      fun J hJ ↦ by
        refine ⟨hJ.2, ?_⟩
        rw [ehmPrimeCompleteRowAbelDyadicExpression_eq_boundary
          D V 0 0 X J hX hJ.2]
        exact hJ.1

/-- At the level of existence, complete signed row-Abel decay and signed
finite-boundary decay are equivalent.  The row-Abel coordinates expose the
cancellation but do not weaken the RH-strength analytic gate. -/
theorem nonempty_ehmPrimeCompleteRowAbelSignedDecay_iff
    (D : EhmPrimeDiscrepancyTruncatedModeData)
    (V : VaalerSawtoothPackage) :
    Nonempty (EhmPrimeCompleteRowAbelSignedDecay D V) ↔
      Nonempty EhmDyadicSignedBoundaryAverageVanishing := by
  constructor
  · rintro ⟨H⟩
    exact ⟨H.toBoundaryAverage⟩
  · rintro ⟨H⟩
    exact ⟨boundaryAverageToCompleteRowAbel D V H⟩

/-! ## Exact outer-scale strength -/

/-- Complete row-Abel decay yields a null dyadic mean of the exact
nonnegative BCF energies.  This is the quantitative content that survives
the limit in the hyperbolic cutoff. -/
noncomputable def EhmPrimeCompleteRowAbelSignedDecay.toEnergyMean
    {D : EhmPrimeDiscrepancyTruncatedModeData}
    {V : VaalerSawtoothPackage}
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (H : EhmPrimeCompleteRowAbelSignedDecay D V) :
    DyadicLogTaperEnergyMeanVanishing :=
  H.toBoundaryAverage.toEnergyMean HS

/-- Conversely, a null dyadic mean of the exact energies supplies complete
row-Abel decay.  The reverse finite-boundary transfer uses only the explicit
vanishing slack `1/(X+1)`. -/
noncomputable def energyMeanToCompleteRowAbel
    (D : EhmPrimeDiscrepancyTruncatedModeData)
    (V : VaalerSawtoothPackage)
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (H : DyadicLogTaperEnergyMeanVanishing) :
    EhmPrimeCompleteRowAbelSignedDecay D V :=
  boundaryAverageToCompleteRowAbel D V
    (DyadicLogTaperEnergyMeanVanishing.toSignedBoundaryAverage HS H)

/-- With the rational-series bridge fixed, the requested complete signed
endpoint-minus-variation decay exists exactly when the dyadic means of the
exact nonnegative log-taper energies vanish.  This is the final outer-scale
gate, not an estimate in the auxiliary truncation height. -/
theorem nonempty_ehmPrimeCompleteRowAbelSignedDecay_iff_energyMean
    (D : EhmPrimeDiscrepancyTruncatedModeData)
    (V : VaalerSawtoothPackage)
    (HS : EhmAutocorrelationR1RationalSeriesBridge) :
    Nonempty (EhmPrimeCompleteRowAbelSignedDecay D V) ↔
      Nonempty DyadicLogTaperEnergyMeanVanishing := by
  rw [nonempty_ehmPrimeCompleteRowAbelSignedDecay_iff D V]
  exact nonempty_signedBoundaryAverage_iff_nonempty_energyMean HS

/-- A genuine proof of the complete signed decay closes the verified
Báez--Duarte route. -/
theorem baezDuarteCriterion_of_ehmPrimeCompleteRowAbelSignedDecay
    {D : EhmPrimeDiscrepancyTruncatedModeData}
    {V : VaalerSawtoothPackage}
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (H : EhmPrimeCompleteRowAbelSignedDecay D V) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmDyadicSignedBoundaryAverage HS
    H.toBoundaryAverage

end RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCompleteRowAbelDecay
