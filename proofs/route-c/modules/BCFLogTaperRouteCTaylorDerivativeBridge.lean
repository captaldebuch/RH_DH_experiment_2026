import Mathlib.Analysis.Calculus.IteratedDeriv.ConvergenceOnBall
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCLambertPhaseEvaluation
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZeroHolomorphic
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorCoefficientIdentification

/-!
# Route C: derivative-to-Taylor bridge

The contour-defined normalized period is now known to be holomorphic on the
unit disc.  This file uses Mathlib's canonical iterated-derivative Taylor
series to isolate the remaining calculation in Bettin--Conrey Theorem 2:
the explicit value of each derivative at the origin.

Once those values are known, holomorphy and the independently proved radius
bound propagate the Taylor expansion across the complete open unit disc.
Thus no separate global value identity is needed.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorDerivativeBridge

open Complex ENNReal
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZero
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorAnalytic
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorCoefficientIdentification
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZeroHolomorphic
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCLambertPhaseEvaluation
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralReciprocity
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodRealization
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralTaylorRow

/-- Mathlib's canonical Taylor series of the normalized central period at
the origin. -/
noncomputable def bettinConreyPsiZeroNativeTaylorSeries :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n =>
    iteratedDeriv n bettinConreyPsiZeroTaylorFunction 0 / n.factorial)

/-- Holomorphy supplies a genuine local Taylor expansion without assuming
any coefficient formula. -/
theorem bettinConreyPsiZeroNativeTaylorSeries_hasFPowerSeriesAt :
    HasFPowerSeriesAt bettinConreyPsiZeroTaylorFunction
      bettinConreyPsiZeroNativeTaylorSeries 0 := by
  have hzero : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
  have han :=
    analyticOnNhd_bettinConreyPsiZeroTaylorFunction_unitDisc 0 hzero
  simpa [bettinConreyPsiZeroNativeTaylorSeries] using
    han.hasFPowerSeriesAt

/-- The proved rational reciprocity theorem fixes the central period at its
self-dual point. -/
theorem bettinConreyPsiZero_one :
    bettinConreyPsiZero 1 = 2 * I / (Real.pi : ℂ) := by
  have h := bettinConreyPsiZeroCentralRationalTheorem_proved.reciprocity
    1 1 (by norm_num) (by norm_num) (by simp)
  simp [bettinConreyCentralFinitePartSide,
    bettinConreyCentralValueRe, bettinConreyCentralFinitePartCorrection,
    bettinConreyCentralFiniteSum, routeCUnitIntervalRatio] at h
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hI : I / (2 : ℂ) ≠ 0 := div_ne_zero I_ne_zero (by norm_num)
  apply mul_left_cancel₀ hI
  rw [← h]
  field_simp [hpi]
  rw [I_sq]

/-- The degree-zero derivative identity is therefore unconditional. -/
theorem bettinConreyPsiZeroTaylorFunction_zero :
    bettinConreyPsiZeroTaylorFunction 0 = 0 := by
  unfold bettinConreyPsiZeroTaylorFunction
  norm_num only [add_zero, zero_div, add_zero]
  rw [bettinConreyPsiZero_one]
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  field_simp [hpi]
  rw [I_sq]
  norm_num

theorem bettinConreyPsiZeroTaylorDerivativeIdentification_zero :
    iteratedDeriv 0 bettinConreyPsiZeroTaylorFunction 0 /
        (0 : ℕ).factorial =
      bettinConreyPsiZeroTaylorScalarCoefficient 0 := by
  simp [bettinConreyPsiZeroTaylorFunction_zero]

/-- The precise finite-contour output still needed from the paper: every
canonical derivative coefficient equals its Bernoulli--zeta expression.
This is a proposition, not an assumed package. -/
def BettinConreyPsiZeroTaylorDerivativeIdentification : Prop :=
  ∀ n : ℕ,
    iteratedDeriv n bettinConreyPsiZeroTaylorFunction 0 / n.factorial =
      bettinConreyPsiZeroTaylorScalarCoefficient n

/-- Derivative identification makes the canonical and explicit formal
series literally equal. -/
theorem bettinConreyPsiZeroNativeTaylorSeries_eq_explicit
    (H : BettinConreyPsiZeroTaylorDerivativeIdentification) :
    bettinConreyPsiZeroNativeTaylorSeries =
      bettinConreyPsiZeroTaylorFormalSeries := by
  ext n
  simp [bettinConreyPsiZeroNativeTaylorSeries,
    bettinConreyPsiZeroTaylorFormalSeries, H n]

/-- **Global Taylor reconstruction.**  The explicit derivative calculation,
holomorphy on `|z| < 1`, and the already proved coefficient-radius estimate
produce the complete native Taylor theorem on that disc. -/
noncomputable def bettinConreyPsiZeroTaylorSeriesOnDisc_of_derivatives
    (H : BettinConreyPsiZeroTaylorDerivativeIdentification)
    (D : BettinConreyCentralCoefficientRootDecay) :
    BettinConreyPsiZeroTaylorSeriesOnDisc where
  hasSeries := by
    let p := bettinConreyPsiZeroNativeTaylorSeries
    have hp : p = bettinConreyPsiZeroTaylorFormalSeries := by
      exact bettinConreyPsiZeroNativeTaylorSeries_eq_explicit H
    have hr : (1 : ℝ≥0∞) ≤ p.radius := by
      rw [hp]
      exact bettinConreyPsiZeroTaylorFormalSeries_radius_ge_one D
    have hanNhd : AnalyticOnNhd ℂ bettinConreyPsiZeroTaylorFunction
        (Metric.eball (0 : ℂ) (1 : ℝ≥0∞)) := by
      simpa only [← ENNReal.ofReal_one, Metric.eball_ofReal] using
        analyticOnNhd_bettinConreyPsiZeroTaylorFunction_unitDisc
    have han : AnalyticOn ℂ bettinConreyPsiZeroTaylorFunction
        (Metric.eball (0 : ℂ) (1 : ℝ≥0∞)) := hanNhd.analyticOn
    have hnative : HasFPowerSeriesOnBall
        bettinConreyPsiZeroTaylorFunction p 0 1 := by
      simpa [p, bettinConreyPsiZeroNativeTaylorSeries] using
        han.hasFPowerSeriesOnSubball (by norm_num) hr
    simpa [hp] using hnative

/-- Consequently the finite derivative calculation is sufficient for the
literal scalar `HasSum` theorem used by Phase 4. -/
noncomputable def bettinConreyPsiZeroTaylorHasSum_of_derivatives
    (H : BettinConreyPsiZeroTaylorDerivativeIdentification)
    (D : BettinConreyCentralCoefficientRootDecay) :
    BettinConreyPsiZeroTaylorHasSum :=
  (bettinConreyPsiZeroTaylorSeriesOnDisc_of_derivatives H D).toTaylorHasSum

/-- Conversely, the literal scalar Taylor theorem identifies every
canonical derivative coefficient.  This proves that the derivative target
is neither stronger nor weaker than the source value identity once the
independent radius estimate is supplied. -/
theorem bettinConreyPsiZeroTaylorDerivativeIdentification_of_hasSum
    (T : BettinConreyPsiZeroTaylorHasSum)
    (D : BettinConreyCentralCoefficientRootDecay) :
    BettinConreyPsiZeroTaylorDerivativeIdentification := by
  intro n
  have hn := bettinConreyPsiZeroTaylorCoefficient_identification
    T D bettinConreyPsiZeroNativeTaylorSeries
      bettinConreyPsiZeroNativeTaylorSeries_hasFPowerSeriesAt n
  simpa [bettinConreyPsiZeroNativeTaylorSeries] using hn

/-- Exact logical equivalence between the finite contour derivative
calculation and the source scalar Taylor theorem. -/
theorem bettinConreyPsiZeroTaylorDerivativeIdentification_iff_hasSum
    (D : BettinConreyCentralCoefficientRootDecay) :
    BettinConreyPsiZeroTaylorDerivativeIdentification ↔
      Nonempty BettinConreyPsiZeroTaylorHasSum := by
  constructor
  · intro H
    exact ⟨bettinConreyPsiZeroTaylorHasSum_of_derivatives H D⟩
  · rintro ⟨T⟩
    exact bettinConreyPsiZeroTaylorDerivativeIdentification_of_hasSum T D

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorDerivativeBridge
