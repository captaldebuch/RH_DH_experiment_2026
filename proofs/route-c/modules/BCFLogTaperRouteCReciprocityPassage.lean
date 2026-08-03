import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCMeanAudit

/-!
# Route C: finite reciprocity passage for the complete dyadic mean

This module performs the next exact bookkeeping step after the Route-C mean
audit.  It separates the complete Vasyunin expression into

* the elementary, logarithmic-ratio, linear, and endpoint sector;
* the finite aggregate of the local Bettin--Conrey pole residue; and
* the remaining signed cotangent sector after that bookkeeping subtraction.

No estimate is asserted.  For every fixed dyadic block, the punctured
central limit may be interchanged with the finite H15 aggregation.  This
does **not** give uniformity as the outer scale tends to infinity.  The final
theorems isolate that distinction explicitly.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCReciprocityPassage

open Complex Filter Topology
open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperBettinConreyAggregate
open RH.Criteria.NymanBeurling.BCFLogTaperCotangentReduction
open RH.Criteria.NymanBeurling.BCFLogTaperEnergyMeanAnatomy
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCompleteRowAbelDecay
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeTruncatedFormula
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.BCFLogTaperGcd
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCMeanAudit
open RH.Criteria.NymanBeurling.QuadraticInteraction

/-- All terms in the Vasyunin expression which are not part of the oriented
cotangent bilinear.  In particular, the original H15 linear correction and
endpoint constant remain here. -/
noncomputable def vasyuninElementaryCompletedExpression (N : ℕ) : ℝ :=
  (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) *
      cotangentDirichletMass N * cotangentDirichletHarmonicMass N +
    vasyuninLogRatioBilinear N + 2 * gramLinearCorrection N + 1

/-- The cotangent contribution left after the local pole-residue aggregate
has been subtracted.  This legacy split is exact bookkeeping, but it is not
the Laurent finite-part reciprocity decomposition. -/
noncomputable def vasyuninCotangentAfterCentralCorrection (N : ℕ) : ℝ :=
  -Real.pi * vasyuninCotangentBilinear N -
    bettinConreyCentralCorrection N

/-- Pointwise correction-preserving Route-C split. -/
theorem vasyuninCoupledExpression_eq_elementary_add_central_add_remainder
    (N : ℕ) :
    vasyuninCoupledExpression N =
      vasyuninElementaryCompletedExpression N +
        bettinConreyCentralCorrection N +
          vasyuninCotangentAfterCentralCorrection N := by
  unfold vasyuninCoupledExpression vasyuninElementaryCompletedExpression
    vasyuninCotangentAfterCentralCorrection
  ring

/-- Dyadic mean of the non-cotangent completed sector. -/
noncomputable def ehmDyadicVasyuninElementaryCompletedMean (X : ℕ) : ℝ :=
  (∑ N ∈ ehmDyadicNBlock X, vasyuninElementaryCompletedExpression N) /
    ((ehmDyadicNBlock X).card : ℝ)

/-- Dyadic mean of the local pole-residue aggregate. -/
noncomputable def ehmDyadicBettinConreyCentralCorrectionMean (X : ℕ) : ℝ :=
  (∑ N ∈ ehmDyadicNBlock X, bettinConreyCentralCorrection N) /
    ((ehmDyadicNBlock X).card : ℝ)

/-- Dyadic mean of the post-central cotangent remainder. -/
noncomputable def ehmDyadicVasyuninCotangentRemainderMean (X : ℕ) : ℝ :=
  (∑ N ∈ ehmDyadicNBlock X,
      vasyuninCotangentAfterCentralCorrection N) /
    ((ehmDyadicNBlock X).card : ℝ)

/-- Exact dyadic three-sector decomposition.  It retains every H15 term and
therefore is still exactly the canonical energy mean. -/
theorem ehmDyadicVasyuninCoupledMean_eq_three_sector_sum (X : ℕ) :
    ehmDyadicVasyuninCoupledMean X =
      ehmDyadicVasyuninElementaryCompletedMean X +
        ehmDyadicBettinConreyCentralCorrectionMean X +
          ehmDyadicVasyuninCotangentRemainderMean X := by
  unfold ehmDyadicVasyuninCoupledMean
    ehmDyadicVasyuninElementaryCompletedMean
    ehmDyadicBettinConreyCentralCorrectionMean
    ehmDyadicVasyuninCotangentRemainderMean
  rw [← add_div, ← add_div]
  congr 1
  simp_rw [vasyuninCoupledExpression_eq_elementary_add_central_add_remainder]
  simp only [Finset.sum_add_distrib]

/-- The three-sector Route-C sum is exactly the normalized H15 energy. -/
theorem ehmDyadicExactEnergyMean_eq_routeC_three_sector_sum (X : ℕ) :
    ehmDyadicExactEnergyMean X =
      ehmDyadicVasyuninElementaryCompletedMean X +
        ehmDyadicBettinConreyCentralCorrectionMean X +
          ehmDyadicVasyuninCotangentRemainderMean X := by
  rw [← ehmDyadicVasyuninCoupledMean_eq_three_sector_sum,
    ehmDyadicVasyuninCoupledMean_eq_energyMean]

/-! ## Finite dyadic passage through the punctured central limit -/

/-- The finite dyadic aggregate of the scaled Bettin--Conrey residue probe
before taking its central value. -/
noncomputable def ehmDyadicBettinConreyCorrectionAggregate
    (z : ℂ) (X : ℕ) : ℂ :=
  (∑ N ∈ ehmDyadicNBlock X, bettinConreyCorrectionAggregate z N) /
    ((ehmDyadicNBlock X).card : ℂ)

/-- For each fixed outer block, the local punctured central limit commutes
with the complete finite dyadic sum. -/
theorem tendsto_ehmDyadicBettinConreyCorrectionAggregate_zero (X : ℕ) :
    Tendsto (fun z : ℂ ↦ ehmDyadicBettinConreyCorrectionAggregate z X)
      (𝓝[≠] 0) (𝓝 (ehmDyadicBettinConreyCentralCorrectionMean X : ℂ)) := by
  have hsum : Tendsto
      (fun z : ℂ ↦
        ∑ N ∈ ehmDyadicNBlock X, bettinConreyCorrectionAggregate z N)
      (𝓝[≠] 0)
      (𝓝 (∑ N ∈ ehmDyadicNBlock X,
        (bettinConreyCentralCorrection N : ℂ))) := by
    apply tendsto_finsetSum
    intro N _
    exact tendsto_bettinConreyCorrectionAggregate_zero N
  have hdiv := hsum.div_const ((ehmDyadicNBlock X).card : ℂ)
  have hcast :
      (ehmDyadicBettinConreyCentralCorrectionMean X : ℂ) =
        (∑ N ∈ ehmDyadicNBlock X,
          (bettinConreyCentralCorrection N : ℂ)) /
            ((ehmDyadicNBlock X).card : ℂ) := by
    unfold ehmDyadicBettinConreyCentralCorrectionMean
    push_cast
    rfl
  rw [hcast]
  exact hdiv

/-- The analytic remainder obtained by subtracting the local correction
aggregate from the exact Vasyunin mean. -/
noncomputable def ehmDyadicRouteCAnalyticRemainder
    (z : ℂ) (X : ℕ) : ℂ :=
  (ehmDyadicVasyuninCoupledMean X : ℂ) -
    ehmDyadicBettinConreyCorrectionAggregate z X

/-- Its fixed-block central limit is the complete Vasyunin mean minus the
pole-residue mean. -/
theorem tendsto_ehmDyadicRouteCAnalyticRemainder_zero (X : ℕ) :
    Tendsto (fun z : ℂ ↦ ehmDyadicRouteCAnalyticRemainder z X)
      (𝓝[≠] 0)
      (𝓝 ((ehmDyadicVasyuninCoupledMean X -
        ehmDyadicBettinConreyCentralCorrectionMean X : ℝ) : ℂ)) := by
  have hconst : Tendsto
      (fun _z : ℂ ↦ (ehmDyadicVasyuninCoupledMean X : ℂ))
      (𝓝[≠] 0) (𝓝 (ehmDyadicVasyuninCoupledMean X : ℂ)) :=
    tendsto_const_nhds
  have hsub := hconst.sub
    (tendsto_ehmDyadicBettinConreyCorrectionAggregate_zero X)
  have hcast :
      ((ehmDyadicVasyuninCoupledMean X -
        ehmDyadicBettinConreyCentralCorrectionMean X : ℝ) : ℂ) =
        (ehmDyadicVasyuninCoupledMean X : ℂ) -
          (ehmDyadicBettinConreyCentralCorrectionMean X : ℂ) := by
    push_cast
    rfl
  rw [hcast]
  exact hsub

/-- Before taking any limit, correction aggregate and analytic remainder
reconstruct the complete Route-C mean exactly. -/
theorem ehmDyadicCorrectionAggregate_add_analyticRemainder
    (z : ℂ) (X : ℕ) :
    ehmDyadicBettinConreyCorrectionAggregate z X +
        ehmDyadicRouteCAnalyticRemainder z X =
      (ehmDyadicVasyuninCoupledMean X : ℂ) := by
  unfold ehmDyadicRouteCAnalyticRemainder
  ring

/-- The genuine remaining outer-scale assertion.  Fixed-block finite limit
exchange above does not inhabit this structure: uniform signed decay in the
outer scale is additional analytic input. -/
structure RouteCCompleteDyadicReciprocityDecay where
  tendsto_zero : Tendsto
    (fun X ↦
      ehmDyadicVasyuninElementaryCompletedMean X +
        ehmDyadicBettinConreyCentralCorrectionMean X +
          ehmDyadicVasyuninCotangentRemainderMean X)
    atTop (𝓝 0)

/-- The Route-C reciprocity decay package is exactly the canonical H15
dyadic mean gate. -/
theorem nonempty_routeCCompleteDyadicReciprocityDecay_iff_energyMean :
    Nonempty RouteCCompleteDyadicReciprocityDecay ↔
      Tendsto ehmDyadicExactEnergyMean atTop (𝓝 0) := by
  constructor
  · rintro ⟨H⟩
    apply H.tendsto_zero.congr'
    exact Eventually.of_forall fun X ↦
      (ehmDyadicExactEnergyMean_eq_routeC_three_sector_sum X).symm
  · intro henergy
    refine ⟨{
      tendsto_zero := ?_ }⟩
    apply henergy.congr'
    exact Eventually.of_forall fun X ↦
      ehmDyadicExactEnergyMean_eq_routeC_three_sector_sum X

/-- Final exact handoff to the existing Ehm/row-Abel formulation.  This
theorem adds no analytic estimate; it confirms that the Route-C package has
neither lost nor strengthened the genuine H15 gate. -/
theorem nonempty_routeCCompleteDyadicReciprocityDecay_iff_completeRowAbel
    (D : EhmPrimeDiscrepancyTruncatedModeData)
    (V : VaalerSawtoothPackage)
    (HS : EhmAutocorrelationR1RationalSeriesBridge) :
    Nonempty RouteCCompleteDyadicReciprocityDecay ↔
      Nonempty (EhmPrimeCompleteRowAbelSignedDecay D V) := by
  rw [nonempty_routeCCompleteDyadicReciprocityDecay_iff_energyMean]
  exact (nonempty_completeRowAbelSignedDecay_iff_tendsto_energyMean
    D V HS).symm

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCReciprocityPassage
