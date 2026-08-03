import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmMSTTTaylorAccumulation
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmFullVaalerLift
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmMSTTWindowCover

/-!
# The combined MSTT optimization functional

The variation loss and reciprocal Taylor loss must be optimized together.
This module defines the exact finite objective which occurs after applying
MSTT to every low-product Vaaler row.  In particular, the MSTT constant,
window length, logarithmic saving, endpoint variation majorant, actual Vaaler
coefficients, and Taylor envelope all occur in one expression.

No numerical value for the external MSTT constant and no asymptotic decay of
the objective is asserted.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTOptimization

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCutoffAverageMainTerm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFullVaalerLift
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTLowRows
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTTaylorAccumulation
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTVariation
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTWindowCover
open RH.Criteria.NymanBeurling.BCFLogTaperEhmProductTruncation
open RH.Criteria.NymanBeurling.BCFLogTaperMSTTPolynomialPhase
open RH.Criteria.NymanBeurling.QuadraticInteraction

/-- The complete MSTT prefactor; it is deliberately not separated from the
variation objective in subsequent definitions. -/
noncomputable def ehmMSTTLogSavingPrefactor
    (HM : MSTTMobiusPolynomialPhaseEstimate)
    (K logSaving X H : ℕ) (epsilon : ℝ) : ℝ :=
  HM.constant K logSaving epsilon * (H : ℝ) /
    (Real.log (X : ℝ)) ^ logSaving

theorem ehmMSTTLogSavingPrefactor_nonneg
    (HM : MSTTMobiusPolynomialPhaseEstimate)
    (K logSaving X H : ℕ) (epsilon : ℝ) :
    0 ≤ ehmMSTTLogSavingPrefactor HM K logSaving X H epsilon := by
  unfold ehmMSTTLogSavingPrefactor
  exact div_nonneg
    (mul_nonneg (HM.constant_nonneg K logSaving epsilon)
      (Nat.cast_nonneg H))
    (pow_nonneg (Real.log_natCast_nonneg X) _)

/-- One product coordinate's combined variation-plus-Taylor cost. -/
noncomputable def ehmMSTTCombinedProductCost
    (HM : MSTTMobiusPolynomialPhaseEstimate)
    (h : ℤ) (N D n X H K logSaving : ℕ) (epsilon : ℝ) : ℝ :=
  ehmMSTTLogSavingPrefactor HM K logSaving X H epsilon *
      ehmMSTTLowProductEndpointVariationMajorant N D n (X + 1) +
    ehmMSTTLowProductWeightL1Mass N D n X H *
      ehmMSTTReciprocalTaylorBlockFactor h n X H K

/-- The cost for one actual Vaaler frequency after summing every retained
low-product coordinate. -/
noncomputable def ehmMSTTCombinedFrequencyCost
    (HM : MSTTMobiusPolynomialPhaseEstimate)
    (h : ℤ) (N D J Y X H K logSaving : ℕ) (epsilon : ℝ) : ℝ :=
  ∑ n ∈ ehmDyadicVaalerLowProductRange J Y,
    ehmMSTTCombinedProductCost HM h N D n X H K logSaving epsilon

/-- The actual finite low-mode optimization objective.  It uses the Vaaler
package's own frequency set and coefficient norms rather than replacing them
by an unweighted symmetric interval. -/
noncomputable def ehmMSTTCombinedLowModeObjective
    (V : VaalerSawtoothPackage)
    (HM : MSTTMobiusPolynomialPhaseEstimate)
    (Q N D J Y X H K logSaving : ℕ) (epsilon : ℝ) : ℝ :=
  ∑ h ∈ (V.frequencies Q).erase 0,
    ‖V.coefficient Q h‖ *
      ehmMSTTCombinedFrequencyCost
        HM h N D J Y X H K logSaving epsilon

/-! ## Moment factorization of the objective -/

/-- Zeroth absolute moment of the actual nonzero Vaaler coefficients. -/
noncomputable def ehmMSTTVaalerCoefficientMass
    (V : VaalerSawtoothPackage) (Q : ℕ) : ℝ :=
  ∑ h ∈ (V.frequencies Q).erase 0, ‖V.coefficient Q h‖

/-- First absolute frequency moment of the Vaaler coefficients. -/
noncomputable def ehmMSTTVaalerCoefficientFirstMoment
    (V : VaalerSawtoothPackage) (Q : ℕ) : ℝ :=
  ∑ h ∈ (V.frequencies Q).erase 0,
    ‖V.coefficient Q h‖ * |(h : ℝ)|

/-- Sum of the exact left-endpoint variation majorants. -/
noncomputable def ehmMSTTEndpointVariationMass
    (N D J Y X : ℕ) : ℝ :=
  ∑ n ∈ ehmDyadicVaalerLowProductRange J Y,
    ehmMSTTLowProductEndpointVariationMajorant N D n (X + 1)

/-- Closed main-only endpoint mass valid when the product cutoff does not
exceed the outer scale. -/
noncomputable def ehmMSTTMainOnlyEndpointVariationMass
    (N J Y X : ℕ) : ℝ :=
  ehmDyadicLogTaperAverage N (X + 1) *
    ∑ n ∈ ehmDyadicVaalerLowProductRange J Y,
      ‖(((ArithmeticFunction.vonMangoldt n / (n : ℝ) : ℝ) : ℂ))‖

/-- Choosing `Y ≤ N` kills every near-divisor endpoint contribution exactly;
the Gate-1 mass is then the log-taper endpoint times a finite von-Mangoldt
harmonic moment. -/
theorem ehmMSTTEndpointVariationMass_eq_mainOnly_of_productCutoff_le
    (N D J Y X : ℕ) (hYN : Y ≤ N) :
    ehmMSTTEndpointVariationMass N D J Y X =
      ehmMSTTMainOnlyEndpointVariationMass N J Y X := by
  classical
  unfold ehmMSTTEndpointVariationMass
    ehmMSTTMainOnlyEndpointVariationMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnrange :=
    (mem_ehmDyadicVaalerLowProductRange_iff J Y n).1 hn
  rw [ehmMSTTLowProductEndpointVariationMajorant_eq_main_of_le
    N D n (X + 1) (by omega) (hnrange.2.2.trans hYN)]
  ring

/-- Product-first moment of the unsigned block masses. -/
noncomputable def ehmMSTTProductWeightFirstMoment
    (N D J Y X H : ℕ) : ℝ :=
  ∑ n ∈ ehmDyadicVaalerLowProductRange J Y,
    ehmMSTTLowProductWeightL1Mass N D n X H * (n : ℝ)

/-- The Taylor scale shared by all retained frequencies and products. -/
noncomputable def ehmMSTTTaylorScale (X H K : ℕ) : ℝ :=
  2 * Real.pi * (H : ℝ) ^ (K + 1) / (X : ℝ) ^ (K + 2)

/-- Factorized form of the combined objective.  This is the useful input for
parameter optimization: the Vaaler zeroth/first moments and the Ehm
endpoint/product moments are now visibly separate, while the MSTT constant
remains attached to the variation term. -/
noncomputable def ehmMSTTFactorizedLowModeObjective
    (V : VaalerSawtoothPackage)
    (HM : MSTTMobiusPolynomialPhaseEstimate)
    (Q N D J Y X H K logSaving : ℕ) (epsilon : ℝ) : ℝ :=
  ∑ h ∈ (V.frequencies Q).erase 0,
    ‖V.coefficient Q h‖ *
      (ehmMSTTLogSavingPrefactor HM K logSaving X H epsilon *
          ehmMSTTEndpointVariationMass N D J Y X +
        ehmMSTTTaylorScale X H K * |(h : ℝ)| *
          ehmMSTTProductWeightFirstMoment N D J Y X H)

theorem ehmMSTTCombinedLowModeObjective_eq_factorized
    (V : VaalerSawtoothPackage)
    (HM : MSTTMobiusPolynomialPhaseEstimate)
    (Q N D J Y X H K logSaving : ℕ) (epsilon : ℝ) :
    ehmMSTTCombinedLowModeObjective
        V HM Q N D J Y X H K logSaving epsilon =
      ehmMSTTFactorizedLowModeObjective
        V HM Q N D J Y X H K logSaving epsilon := by
  classical
  unfold ehmMSTTCombinedLowModeObjective
    ehmMSTTFactorizedLowModeObjective
  apply Finset.sum_congr rfl
  intro h _
  congr 1
  unfold ehmMSTTCombinedFrequencyCost ehmMSTTCombinedProductCost
    ehmMSTTReciprocalTaylorBlockFactor
    ehmMSTTEndpointVariationMass
    ehmMSTTProductWeightFirstMoment ehmMSTTTaylorScale
  rw [Finset.sum_add_distrib]
  apply congrArg₂ (· + ·)
  · rw [Finset.mul_sum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    have hnatAbs : |(n : ℝ)| = (n : ℝ) :=
      abs_of_nonneg (Nat.cast_nonneg n)
    rw [abs_mul, hnatAbs]
    ring

/-- The low-product Vaaler modes restricted to one MSTT window. -/
noncomputable def ehmMSTTWeightedLowProductModesBlock
    (V : VaalerSawtoothPackage)
    (Q N D J Y X H : ℕ) : ℂ :=
  ∑ h ∈ (V.frequencies Q).erase 0,
    V.coefficient Q h * ehmMSTTLowProductRowsBlock h N D J Y X H

/-- One frequency is bounded by the combined cost, with the MSTT constant
already multiplied into the endpoint variation majorant. -/
theorem norm_ehmMSTTLowProductRowsBlock_le_combinedFrequencyCost
    (HM : MSTTMobiusPolynomialPhaseEstimate)
    (h : ℤ) (N D J Y : ℕ)
    (logSaving K : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (X H : ℕ)
    (hthreshold : HM.threshold K logSaving epsilon ≤ X)
    (hN : 2 ≤ N) (hX : 3 ≤ X) (hH : 1 ≤ H)
    (hHlower :
      Real.rpow (X : ℝ) ((5 / 8 : ℝ) + epsilon) ≤ (H : ℝ))
    (hHupper :
      (H : ℝ) ≤ Real.rpow (X : ℝ) (1 - epsilon)) :
    ‖ehmMSTTLowProductRowsBlock h N D J Y X H‖ ≤
      ehmMSTTCombinedFrequencyCost
        HM h N D J Y X H K logSaving epsilon := by
  have hbase := norm_ehmMSTTLowProductRowsBlock_le
    HM h N D J Y logSaving K epsilon hepsilon X H
      hthreshold hX hH hHlower hHupper
  refine hbase.trans ?_
  unfold ehmMSTTCombinedFrequencyCost ehmMSTTCombinedProductCost
    ehmMSTTLogSavingPrefactor
  apply Finset.sum_le_sum
  intro n _
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left
      (complexWeightVariation_ehmMSTTLowProductWeight_le_endpointMajorant
        N D n (X + 1) (X + H) hN (by omega) (by omega))
      (ehmMSTTLogSavingPrefactor_nonneg
        HM K logSaving X H epsilon)
  · exact ehmMSTTLowProductTaylorErrorMajorant_le_blockFactor
      h N D n X H K (by omega)

/-- The weighted sum of all actual low Vaaler modes is controlled by the
single combined optimization objective. -/
theorem norm_ehmMSTTWeightedLowProductModesBlock_le_objective
    (V : VaalerSawtoothPackage)
    (HM : MSTTMobiusPolynomialPhaseEstimate)
    (Q N D J Y : ℕ)
    (logSaving K : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (X H : ℕ)
    (hthreshold : HM.threshold K logSaving epsilon ≤ X)
    (hN : 2 ≤ N) (hX : 3 ≤ X) (hH : 1 ≤ H)
    (hHlower :
      Real.rpow (X : ℝ) ((5 / 8 : ℝ) + epsilon) ≤ (H : ℝ))
    (hHupper :
      (H : ℝ) ≤ Real.rpow (X : ℝ) (1 - epsilon)) :
    ‖ehmMSTTWeightedLowProductModesBlock V Q N D J Y X H‖ ≤
      ehmMSTTCombinedLowModeObjective
        V HM Q N D J Y X H K logSaving epsilon := by
  classical
  unfold ehmMSTTWeightedLowProductModesBlock
    ehmMSTTCombinedLowModeObjective
  calc
    ‖∑ h ∈ (V.frequencies Q).erase 0,
        V.coefficient Q h *
          ehmMSTTLowProductRowsBlock h N D J Y X H‖ ≤
      ∑ h ∈ (V.frequencies Q).erase 0,
        ‖V.coefficient Q h *
          ehmMSTTLowProductRowsBlock h N D J Y X H‖ := norm_sum_le _ _
    _ = ∑ h ∈ (V.frequencies Q).erase 0,
        ‖V.coefficient Q h‖ *
          ‖ehmMSTTLowProductRowsBlock h N D J Y X H‖ := by
      apply Finset.sum_congr rfl
      intro h _
      rw [norm_mul]
    _ ≤ ∑ h ∈ (V.frequencies Q).erase 0,
        ‖V.coefficient Q h‖ *
          ehmMSTTCombinedFrequencyCost
            HM h N D J Y X H K logSaving epsilon := by
      apply Finset.sum_le_sum
      intro h _
      exact mul_le_mul_of_nonneg_left
        (norm_ehmMSTTLowProductRowsBlock_le_combinedFrequencyCost
          HM h N D J Y logSaving K epsilon hepsilon X H
          hthreshold hN hX hH hHlower hHupper)
        (norm_nonneg _)

/-- The same objective at the normalization used by the dyadic outer mean. -/
noncomputable def ehmMSTTNormalizedCombinedLowModeObjective
    (V : VaalerSawtoothPackage)
    (HM : MSTTMobiusPolynomialPhaseEstimate)
    (Q N D J Y X H K logSaving : ℕ) (epsilon : ℝ) : ℝ :=
  ehmMSTTCombinedLowModeObjective
      V HM Q N D J Y X H K logSaving epsilon /
    ((ehmDyadicNBlock N).card : ℝ)

theorem norm_ehmMSTTWeightedLowProductModesBlock_div_card_le_normalizedObjective
    (V : VaalerSawtoothPackage)
    (HM : MSTTMobiusPolynomialPhaseEstimate)
    (Q N D J Y : ℕ)
    (logSaving K : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (X H : ℕ)
    (hthreshold : HM.threshold K logSaving epsilon ≤ X)
    (hN : 2 ≤ N) (hX : 3 ≤ X) (hH : 1 ≤ H)
    (hHlower :
      Real.rpow (X : ℝ) ((5 / 8 : ℝ) + epsilon) ≤ (H : ℝ))
    (hHupper :
      (H : ℝ) ≤ Real.rpow (X : ℝ) (1 - epsilon)) :
    ‖ehmMSTTWeightedLowProductModesBlock V Q N D J Y X H‖ /
        ((ehmDyadicNBlock N).card : ℝ) ≤
      ehmMSTTNormalizedCombinedLowModeObjective
        V HM Q N D J Y X H K logSaving epsilon := by
  unfold ehmMSTTNormalizedCombinedLowModeObjective
  exact div_le_div_of_nonneg_right
    (norm_ehmMSTTWeightedLowProductModesBlock_le_objective
      V HM Q N D J Y logSaving K epsilon hepsilon X H
      hthreshold hN hX hH hHlower hHupper)
    (Nat.cast_nonneg _)

/-! ## Parameter packages and the padded dyadic cover -/

/-- The five discrete parameters to be optimized together. -/
structure EhmMSTTOptimizationParameters where
  productCutoff : ℕ
  windowLength : ℕ
  vaalerCutoff : ℕ
  taylorDegree : ℕ
  logSaving : ℕ

/-- Exact feasibility conditions on every shifted window in the upper
dyadic cover. -/
def EhmMSTTOptimizationParameters.Feasible
    (p : EhmMSTTOptimizationParameters)
    (HM : MSTTMobiusPolynomialPhaseEstimate)
    (epsilon : ℝ) (X : ℕ) : Prop :=
  2 ≤ X ∧
    ∀ r ∈ Finset.range (ehmMSTTWindowCount X p.windowLength),
      EhmMSTTWindowAdmissible HM p.taylorDegree p.logSaving epsilon
        X p.windowLength r

/-- Sum of the complete weighted low-mode rows on every padded full window.
The final window is not clipped here; transferring this to the exact dyadic
support costs the endpoint-indicator variation isolated by Gate 3. -/
noncomputable def ehmMSTTPaddedFullWindowLowModes
    (V : VaalerSawtoothPackage)
    (p : EhmMSTTOptimizationParameters)
    (X D J : ℕ) : ℂ :=
  ∑ r ∈ Finset.range (ehmMSTTWindowCount X p.windowLength),
    ehmMSTTWeightedLowProductModesBlock V p.vaalerCutoff X D J
      p.productCutoff (ehmMSTTWindowStart X p.windowLength r)
      p.windowLength

/-- The combined Gate-1/Gate-2 objective summed over the padded Gate-3
window cover and normalized by the outer dyadic cutoff count. -/
noncomputable def ehmMSTTNormalizedPaddedDyadicObjective
    (V : VaalerSawtoothPackage)
    (HM : MSTTMobiusPolynomialPhaseEstimate)
    (p : EhmMSTTOptimizationParameters)
    (epsilon : ℝ) (X D J : ℕ) : ℝ :=
  (∑ r ∈ Finset.range (ehmMSTTWindowCount X p.windowLength),
      ehmMSTTCombinedLowModeObjective V HM p.vaalerCutoff X D J
        p.productCutoff (ehmMSTTWindowStart X p.windowLength r)
        p.windowLength p.taylorDegree p.logSaving epsilon) /
    ((ehmDyadicNBlock X).card : ℝ)

/-- A feasible parameter package bounds the entire padded upper-dyadic
low-mode sum by the one normalized optimization objective. -/
theorem norm_ehmMSTTPaddedFullWindowLowModes_div_card_le_objective
    (V : VaalerSawtoothPackage)
    (HM : MSTTMobiusPolynomialPhaseEstimate)
    (p : EhmMSTTOptimizationParameters)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (X D J : ℕ)
    (hfeasible : p.Feasible HM epsilon X) :
    ‖ehmMSTTPaddedFullWindowLowModes V p X D J‖ /
        ((ehmDyadicNBlock X).card : ℝ) ≤
      ehmMSTTNormalizedPaddedDyadicObjective V HM p epsilon X D J := by
  classical
  unfold ehmMSTTPaddedFullWindowLowModes
    ehmMSTTNormalizedPaddedDyadicObjective
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    ‖∑ r ∈ Finset.range (ehmMSTTWindowCount X p.windowLength),
        ehmMSTTWeightedLowProductModesBlock V p.vaalerCutoff X D J
          p.productCutoff (ehmMSTTWindowStart X p.windowLength r)
          p.windowLength‖ ≤
      ∑ r ∈ Finset.range (ehmMSTTWindowCount X p.windowLength),
        ‖ehmMSTTWeightedLowProductModesBlock V p.vaalerCutoff X D J
          p.productCutoff (ehmMSTTWindowStart X p.windowLength r)
          p.windowLength‖ := norm_sum_le _ _
    _ ≤ ∑ r ∈ Finset.range (ehmMSTTWindowCount X p.windowLength),
        ehmMSTTCombinedLowModeObjective V HM p.vaalerCutoff X D J
          p.productCutoff (ehmMSTTWindowStart X p.windowLength r)
          p.windowLength p.taylorDegree p.logSaving epsilon := by
      apply Finset.sum_le_sum
      intro r hr
      have hw := hfeasible.2 r hr
      exact norm_ehmMSTTWeightedLowProductModesBlock_le_objective
        V HM p.vaalerCutoff X D J p.productCutoff p.logSaving
        p.taylorDegree epsilon hepsilon
        (ehmMSTTWindowStart X p.windowLength r) p.windowLength
        hw.threshold_le hfeasible.1 hw.base_ge_three hw.length_pos
        hw.length_lower hw.length_upper

end RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTOptimization
