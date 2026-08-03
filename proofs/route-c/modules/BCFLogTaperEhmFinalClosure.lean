import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmAlternativeRoutes
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmTypeIIAnalyticGate
import RiemannHypothesis.Criteria.NymanBeurling.RHBridge

/-!
# Honest final closures for the coupled H15 routes

This file collects the conclusions justified by the current formalization.
Each arithmetic route still takes its explicitly named cancellation estimate
as an input.  From that input the Báez--Duarte and Nyman--Beurling criteria are
unconditional.  A Riemann-hypothesis conclusion additionally takes the
forward Nyman--Beurling theorem as an explicit argument, rather than silently
using the historical project axiom.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmFinalClosure

open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaperCotangentReduction
open RH.Criteria.NymanBeurling.BCFLogTaperEhmAlternativeRoutes
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCoupledNearCoreTarget
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmTypeIIAnalyticGate
open RH.Criteria.NymanBeurling.RHBridge

/-! ## Primary Type-I/II route -/

/-- The exact Type-I/II analytic gate closes the Báez--Duarte criterion. -/
theorem baezDuarteCriterion_of_ehmTypeIICoupledAnalyticGate
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (H : EhmDyadicTypeIICoupledAnalyticGate) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmDyadicCoupledNearCoreSignedAverage HS
    H.toCoupledNearCore

/-- The same inputs close the proved finite Báez--Duarte-to-Nyman bridge. -/
theorem nymanBeurlingCriterion_of_ehmTypeIICoupledAnalyticGate
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (H : EhmDyadicTypeIICoupledAnalyticGate) :
    NymanBeurlingCriterion :=
  nymanBeurlingCriterion_iff_baezDuarteCriterion.mpr
    (baezDuarteCriterion_of_ehmTypeIICoupledAnalyticGate HS H)

/-- The Type-I/II route implies RH once the forward Nyman--Beurling theorem
is supplied explicitly.  No project RH equivalence axiom is hidden here. -/
theorem riemannHypothesis_of_ehmTypeIICoupledAnalyticGate_of_NBForward
    (hNB : NBForward)
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (H : EhmDyadicTypeIICoupledAnalyticGate) :
    RH.Basic.RiemannHypothesis :=
  hNB (nymanBeurlingCriterion_of_ehmTypeIICoupledAnalyticGate HS H)

/-! ## Alternative reciprocal and cotangent routes -/

/-- A reciprocal-phase argument is sufficient only through the reconstructed
three-piece estimate, which retains the smooth, endpoint, and linear terms. -/
theorem nymanBeurlingCriterion_of_ehmCoupledReciprocalRoute
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (H : EhmCoupledReciprocalRouteEstimate) :
    NymanBeurlingCriterion :=
  nymanBeurlingCriterion_iff_baezDuarteCriterion.mpr
    (baezDuarteCriterion_of_ehmCoupledReciprocalRoute HS H)

/-- Conditional RH closure of the correctly reconstructed reciprocal route. -/
theorem riemannHypothesis_of_ehmCoupledReciprocalRoute_of_NBForward
    (hNB : NBForward)
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (H : EhmCoupledReciprocalRouteEstimate) :
    RH.Basic.RiemannHypothesis :=
  hNB (nymanBeurlingCriterion_of_ehmCoupledReciprocalRoute HS H)

/-- A fully coupled Vasyunin estimate closes the Nyman--Beurling criterion. -/
theorem nymanBeurlingCriterion_of_vasyuninCoupledCancellation
    (H : VasyuninCoupledCancellationEstimate) :
    NymanBeurlingCriterion :=
  nymanBeurlingCriterion_iff_baezDuarteCriterion.mpr
    (baezDuarteCriterion_of_vasyuninCoupledCancellation H)

/-- Conditional RH closure of the fully coupled cotangent route. -/
theorem riemannHypothesis_of_vasyuninCoupledCancellation_of_NBForward
    (hNB : NBForward)
    (H : VasyuninCoupledCancellationEstimate) :
    RH.Basic.RiemannHypothesis :=
  hNB (nymanBeurlingCriterion_of_vasyuninCoupledCancellation H)

end RH.Criteria.NymanBeurling.BCFLogTaperEhmFinalClosure
