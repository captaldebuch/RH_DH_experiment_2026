import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmPrimeProfileCollapse

/-!
# Common-height truncated explicit formula for the H15 prime profile

The complete explicit formula collapses back to `ψ`, so analytic gain can
only come from a controlled truncation.  This module introduces a common
truncation height, proves the exact finite assembly, and isolates a sufficient
two-part estimate:

* a signed dyadic bound for the correction-completed finite-mode expression;
* a norm bound for the remainder only after its full dyadic Abel aggregation.

No rowwise or modewise absolute values are introduced.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeTruncatedFormula

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmBoundaryResearch
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmHighSectorCompensation
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCorrectionMatching
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeDiscrepancyAbel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeProfileCollapse
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmSignedAverage
open RH.Criteria.NymanBeurling.BCFLogTaperEhmUniformBoundary

/-- Abstract exact explicit formula truncated at a common height `Y`.  The
remainder carries every omitted zero and every truncation error. -/
structure EhmPrimeDiscrepancyTruncatedModeData where
  endpointMode : ℕ → ℕ → ℂ
  trivialZeroMode : ℕ → ℕ → ℂ
  symmetricZeroMode : ℕ → ℕ → ℂ
  remainderMode : ℕ → ℕ → ℂ
  decomposition : ∀ Y k : ℕ,
    (ehmPrimeDiscrepancy k : ℂ) =
      endpointMode Y k + trivialZeroMode Y k +
        symmetricZeroMode Y k + remainderMode Y k

/-- Regard a truncated formula as an exact three-mode decomposition by
keeping the zero sum and the truncation remainder coupled in the third mode. -/
def EhmPrimeDiscrepancyTruncatedModeData.toExplicitModeData
    (H : EhmPrimeDiscrepancyTruncatedModeData) (Y : ℕ) :
    EhmPrimeDiscrepancyExplicitModeData where
  endpointMode := H.endpointMode Y
  trivialZeroMode := H.trivialZeroMode Y
  symmetricZeroMode := H.symmetricZeroMode Y + H.remainderMode Y
  decomposition k := by
    simpa only [Pi.add_apply, add_assoc] using H.decomposition Y k

/-- Linear, endpoint, trivial-zero, and retained finite-zero modes.  The
natural defect and missing-divisor correction will be attached after Abel
transport. -/
noncomputable def ehmPrimeTruncatedPrincipalProfile
    (H : EhmPrimeDiscrepancyTruncatedModeData) (Y : ℕ) : ℕ → ℂ :=
  (fun k : ℕ ↦ (k : ℂ)) + H.endpointMode Y +
    H.trivialZeroMode Y + H.symmetricZeroMode Y

/-- The complete truncated profile before Abel transport. -/
noncomputable def ehmPrimeTruncatedFullProfile
    (H : EhmPrimeDiscrepancyTruncatedModeData) (Y : ℕ) : ℕ → ℂ :=
  ehmPrimeTruncatedPrincipalProfile H Y + H.remainderMode Y

/-- Exact profile assembly at every truncation height. -/
theorem ehmPrimeTruncatedFullProfile_eq_chebyshev
    (H : EhmPrimeDiscrepancyTruncatedModeData) (Y k : ℕ) :
    ehmPrimeTruncatedFullProfile H Y k =
      (ehmPrimeChebyshevValue k : ℂ) := by
  unfold ehmPrimeTruncatedFullProfile ehmPrimeTruncatedPrincipalProfile
  simp only [Pi.add_apply]
  calc
    (k : ℂ) + H.endpointMode Y k + H.trivialZeroMode Y k +
          H.symmetricZeroMode Y k + H.remainderMode Y k =
        (k : ℂ) + (ehmPrimeDiscrepancy k : ℂ) := by
      rw [H.decomposition]
      ring
    _ = (ehmPrimeChebyshevValue k : ℂ) := by
      have h := congrArg (fun x : ℝ ↦ (x : ℂ))
        (ehmPrimeDiscrepancy_add_natCast k)
      push_cast at h
      simpa [add_comm] using h

/-- Any two exact common-height truncation packages reassemble to the same
full profile, even at different heights.  Analytic information can therefore
only be gained before the finite modes and the coupled remainder are added
back together. -/
theorem ehmPrimeTruncatedFullProfile_independent
    (H₁ H₂ : EhmPrimeDiscrepancyTruncatedModeData) (Y₁ Y₂ : ℕ) :
    ehmPrimeTruncatedFullProfile H₁ Y₁ =
      ehmPrimeTruncatedFullProfile H₂ Y₂ := by
  funext k
  rw [ehmPrimeTruncatedFullProfile_eq_chebyshev,
    ehmPrimeTruncatedFullProfile_eq_chebyshev]

/-- The truncated full profile is exactly the completed profile obtained by
coupling the finite zero sum and the remainder. -/
theorem ehmPrimeCompletedExplicitProfile_toExplicit_eq_truncatedFull
    (H : EhmPrimeDiscrepancyTruncatedModeData) (Y : ℕ) :
    ehmPrimeCompletedExplicitProfile (H.toExplicitModeData Y) =
      ehmPrimeTruncatedFullProfile H Y := by
  funext k
  unfold ehmPrimeCompletedExplicitProfile
    EhmPrimeDiscrepancyTruncatedModeData.toExplicitModeData
    ehmPrimeTruncatedFullProfile ehmPrimeTruncatedPrincipalProfile
  simp only [Pi.add_apply]
  ring

/-- Correction-completed finite-mode expression at one outer cutoff.  The
explicit-formula remainder is the only omitted term. -/
noncomputable def ehmPrimeTruncatedStructuredBoundary
    (H : EhmPrimeDiscrepancyTruncatedModeData)
    (Y N J : ℕ) : ℂ :=
  (ehmFiniteNaturalCutoffDefect N : ℂ) +
    ehmPrimeHighAggregateMode (ehmPrimeTruncatedPrincipalProfile H Y) N J -
      (ehmFiniteMissingDivisorTailOuter ehmR1 N J : ℂ)

/-- The explicit-formula remainder after complete row and outer Möbius
aggregation at one cutoff. -/
noncomputable def ehmPrimeTruncatedRemainderAggregate
    (H : EhmPrimeDiscrepancyTruncatedModeData)
    (Y N J : ℕ) : ℂ :=
  ehmPrimeHighAggregateMode (H.remainderMode Y) N J

/-- Exact finite truncated-formula identity.  The finite modes retain the
natural and missing-divisor corrections, while the remainder is separated
only after the full per-`N` Abel aggregation. -/
theorem ofReal_ehmFiniteCoupledBoundaryExpression_eq_truncated
    (H : EhmPrimeDiscrepancyTruncatedModeData)
    (Y N J : ℕ) (hN : 2 ≤ N) (hNJ : N ≤ J) :
    (ehmFiniteCoupledBoundaryExpression ehmR1 N J : ℂ) =
      ehmPrimeTruncatedStructuredBoundary H Y N J +
        ehmPrimeTruncatedRemainderAggregate H Y N J := by
  rw [ofReal_ehmFiniteCoupledBoundaryExpression_eq_completedBoundaryProfile
    (H.toExplicitModeData Y) N J hN hNJ]
  unfold ehmPrimeCompletedBoundaryProfile
    ehmPrimeTruncatedStructuredBoundary
    ehmPrimeTruncatedRemainderAggregate
  rw [ehmPrimeCompletedExplicitProfile_toExplicit_eq_truncatedFull]
  unfold ehmPrimeTruncatedFullProfile
  rw [ehmPrimeHighAggregateMode_add]
  ring

/-! ## Global dyadic remainder separation -/

/-- Signed dyadic finite-mode sum.  All correction and retained-zero terms
remain coupled across the complete outer block. -/
noncomputable def ehmPrimeTruncatedStructuredDyadicSum
    (H : EhmPrimeDiscrepancyTruncatedModeData)
    (Y X J : ℕ) : ℝ :=
  ∑ N ∈ ehmDyadicNBlock X,
    (ehmPrimeTruncatedStructuredBoundary H Y N J).re

/-- The single complex remainder after summing over the entire dyadic outer
block.  Taking its norm does not discard cancellation between cutoffs. -/
noncomputable def ehmPrimeTruncatedRemainderDyadicAggregate
    (H : EhmPrimeDiscrepancyTruncatedModeData)
    (Y X J : ℕ) : ℂ :=
  ∑ N ∈ ehmDyadicNBlock X,
    ehmPrimeTruncatedRemainderAggregate H Y N J

/-- Exact dyadic truncated-formula assembly. -/
theorem sum_ehmFiniteCoupledBoundaryExpression_eq_truncatedDyadic
    (H : EhmPrimeDiscrepancyTruncatedModeData)
    (Y X J : ℕ) (hX : 2 ≤ X) (hJ : 2 * X ≤ J) :
    (∑ N ∈ ehmDyadicNBlock X,
        ehmFiniteCoupledBoundaryExpression ehmR1 N J) =
      ehmPrimeTruncatedStructuredDyadicSum H Y X J +
        (ehmPrimeTruncatedRemainderDyadicAggregate H Y X J).re := by
  classical
  unfold ehmPrimeTruncatedStructuredDyadicSum
    ehmPrimeTruncatedRemainderDyadicAggregate
  let reHom : ℂ →+ ℝ :=
    { toFun := fun z ↦ z.re
      map_zero' := rfl
      map_add' := by intro x y; rfl }
  change (∑ N ∈ ehmDyadicNBlock X,
      ehmFiniteCoupledBoundaryExpression ehmR1 N J) =
    (∑ N ∈ ehmDyadicNBlock X,
      (ehmPrimeTruncatedStructuredBoundary H Y N J).re) +
      reHom (∑ N ∈ ehmDyadicNBlock X,
        ehmPrimeTruncatedRemainderAggregate H Y N J)
  rw [map_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro N hNmem
  have hid := ofReal_ehmFiniteCoupledBoundaryExpression_eq_truncated
    H Y N J (hX.trans (Finset.mem_Icc.mp hNmem).1)
      ((Finset.mem_Icc.mp hNmem).2.trans hJ)
  have hre := congrArg Complex.re hid
  simpa using hre

/-! ## Analytic interfaces -/

/-- Exact coupled truncated-formula target with a common height on each
dyadic block and hyperbolic cutoff.  This is a coordinate version of the
signed finite-boundary target. -/
structure EhmPrimeTruncatedDyadicCoupledVanishing
    (H : EhmPrimeDiscrepancyTruncatedModeData) where
  height : ℕ → ℕ → ℕ
  eta : ℕ → ℝ
  eta_nonneg : ∀ X, 0 ≤ eta X
  eta_tendsto_zero : Tendsto eta atTop (nhds 0)
  cofinal_bound : ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      2 * X ≤ J ∧
      ehmPrimeTruncatedStructuredDyadicSum H (height X J) X J +
          (ehmPrimeTruncatedRemainderDyadicAggregate
            H (height X J) X J).re ≤
        ((ehmDyadicNBlock X).card : ℝ) * eta X

/-- The coupled truncated target gives the existing signed boundary average. -/
noncomputable def EhmPrimeTruncatedDyadicCoupledVanishing.toBoundaryAverage
    {H : EhmPrimeDiscrepancyTruncatedModeData}
    (HT : EhmPrimeTruncatedDyadicCoupledVanishing H) :
    EhmDyadicSignedBoundaryAverageVanishing where
  eta := HT.eta
  eta_nonneg := HT.eta_nonneg
  eta_tendsto_zero := HT.eta_tendsto_zero
  cofinal_sum_bound X hX :=
    (HT.cofinal_bound X hX).mono fun J hJ ↦ by
      rw [sum_ehmFiniteCoupledBoundaryExpression_eq_truncatedDyadic
        H (HT.height X J) X J hX hJ.1]
      exact hJ.2

/-- A sufficient split made only at the global dyadic level.  In particular,
the remainder norm is outside the `N`-sum, not inside it. -/
structure EhmPrimeTruncatedDyadicSeparatedControl
    (H : EhmPrimeDiscrepancyTruncatedModeData) where
  height : ℕ → ℕ → ℕ
  structuredEta : ℕ → ℝ
  remainderEta : ℕ → ℝ
  structuredEta_nonneg : ∀ X, 0 ≤ structuredEta X
  remainderEta_nonneg : ∀ X, 0 ≤ remainderEta X
  structuredEta_tendsto_zero : Tendsto structuredEta atTop (nhds 0)
  remainderEta_tendsto_zero : Tendsto remainderEta atTop (nhds 0)
  cofinal_control : ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      2 * X ≤ J ∧
      ehmPrimeTruncatedStructuredDyadicSum H (height X J) X J ≤
        ((ehmDyadicNBlock X).card : ℝ) * structuredEta X ∧
      ‖ehmPrimeTruncatedRemainderDyadicAggregate
          H (height X J) X J‖ ≤
        ((ehmDyadicNBlock X).card : ℝ) * remainderEta X

/-- Global finite-mode control plus a global remainder norm bound imply the
coupled truncated-formula target. -/
noncomputable def EhmPrimeTruncatedDyadicSeparatedControl.toCoupled
    {H : EhmPrimeDiscrepancyTruncatedModeData}
    (HT : EhmPrimeTruncatedDyadicSeparatedControl H) :
    EhmPrimeTruncatedDyadicCoupledVanishing H where
  height := HT.height
  eta := fun X ↦ HT.structuredEta X + HT.remainderEta X
  eta_nonneg X := add_nonneg
    (HT.structuredEta_nonneg X) (HT.remainderEta_nonneg X)
  eta_tendsto_zero := by
    simpa using HT.structuredEta_tendsto_zero.add
      HT.remainderEta_tendsto_zero
  cofinal_bound X hX :=
    (HT.cofinal_control X hX).mono fun J hJ ↦ by
      refine ⟨hJ.1, ?_⟩
      calc
        ehmPrimeTruncatedStructuredDyadicSum H (HT.height X J) X J +
            (ehmPrimeTruncatedRemainderDyadicAggregate
              H (HT.height X J) X J).re ≤
          ehmPrimeTruncatedStructuredDyadicSum H (HT.height X J) X J +
            ‖ehmPrimeTruncatedRemainderDyadicAggregate
              H (HT.height X J) X J‖ := by
                gcongr
                exact Complex.re_le_norm _
        _ ≤ ((ehmDyadicNBlock X).card : ℝ) * HT.structuredEta X +
            ((ehmDyadicNBlock X).card : ℝ) * HT.remainderEta X :=
          add_le_add hJ.2.1 hJ.2.2
        _ = ((ehmDyadicNBlock X).card : ℝ) *
            (HT.structuredEta X + HT.remainderEta X) := by ring

/-- The global truncated-formula estimates close the Báez--Duarte route. -/
theorem baezDuarteCriterion_of_ehmPrimeTruncatedDyadicSeparated
    {H : EhmPrimeDiscrepancyTruncatedModeData}
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (HT : EhmPrimeTruncatedDyadicSeparatedControl H) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmDyadicSignedBoundaryAverage HS
    HT.toCoupled.toBoundaryAverage

end RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeTruncatedFormula
