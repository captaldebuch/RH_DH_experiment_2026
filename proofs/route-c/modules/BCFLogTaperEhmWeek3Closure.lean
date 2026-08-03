import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmRationalBlocks
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmFinalClosure
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmSignedTransferAudit
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmDyadicCorrectionAbel

/-!
# Week 3 closure after the rational Ehm value theorem

Week 2 constructed the rational autocorrelation--`R₁` series bridge.  This
module inserts that proved bridge into the full finite H15 boundary and
removes it from every downstream hypothesis list.

The remaining input is therefore only signed cancellation.  Two coordinate
systems are recorded:

* `H15Week3SignedCancellation` is the weakest double-cofinal finite-boundary
  statement presently used by the proof;
* `H15Week3TypeIICancellation` is the stronger explicit Type-I/II analytic
  interface.

No inhabitant of either cancellation type is constructed here.  The first
is equivalent, at package-existence level, to cofinal smallness of the exact
nonnegative BCF energies.  Thus filling it is the remaining H15/RH-strength
analytic problem, not an algebraic consequence of the rational value
identity.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmWeek3Closure

open Filter
open scoped Topology
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperCofinalEnergy
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicCorrectionAbel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFinalClosure
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBlocks
open RH.Criteria.NymanBeurling.BCFLogTaperEhmSignedAverage
open RH.Criteria.NymanBeurling.BCFLogTaperEhmSignedTransferAudit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmTypeIIAnalyticGate
open RH.Criteria.NymanBeurling.BCFLogTaperEhmUniformBoundary
open RH.Criteria.NymanBeurling.RHBridge

/-! ## Unconditional insertion of the Week 2 bridge -/

/-- At every fixed outer cutoff, the concrete finite Ehm boundary tends to
the exact log-taper energy.  The rational-series argument is now internal,
not a theorem parameter. -/
theorem ehmFiniteCoupledBoundaryExpression_tendsto_energy_proved
    (N : ℕ) (hN : 2 ≤ N) :
    Tendsto
      (fun J : ℕ => ehmFiniteCoupledBoundaryExpression ehmR1 N J)
      atTop (nhds (energy N)) :=
  ehmFiniteCoupledBoundaryExpression_tendsto_energy
    ehmAutocorrelationR1RationalSeriesBridgeProved N hN

/-- The signed finite boundary sum on a fixed dyadic block converges to the
sum of exact nonnegative energies, with no remaining normalization input. -/
theorem ehmDyadicBoundarySum_tendsto_energySum_proved
    (X : ℕ) (hX : 2 ≤ X) :
    Tendsto
      (fun J : ℕ => ∑ N ∈ ehmDyadicNBlock X,
        ehmFiniteCoupledBoundaryExpression ehmR1 N J)
      atTop (nhds (∑ N ∈ ehmDyadicNBlock X, energy N)) :=
  ehmDyadicBoundarySum_tendsto_energySum
    ehmAutocorrelationR1RationalSeriesBridgeProved X hX

/-- The corresponding fixed-block second-moment identity. -/
theorem ehmDyadicBoundarySquareSum_tendsto_energySquareSum_proved
    (X : ℕ) (hX : 2 ≤ X) :
    Tendsto
      (fun J : ℕ => ∑ N ∈ ehmDyadicNBlock X,
        (ehmFiniteCoupledBoundaryExpression ehmR1 N J) ^ 2)
      atTop (nhds (∑ N ∈ ehmDyadicNBlock X, (energy N) ^ 2)) :=
  ehmDyadicBoundarySquareSum_tendsto_energySquareSum
    ehmAutocorrelationR1RationalSeriesBridgeProved X hX

/-! ## The single remaining Week 3 input -/

/-- Weakest currently exposed signed H15 cancellation statement. -/
abbrev H15Week3SignedCancellation :=
  EhmDoubleCofinalBoundaryVanishing ehmR1

/-- Explicit Type-I/II coordinate system for the stronger dyadic route. -/
abbrev H15Week3TypeIICancellation :=
  EhmDyadicTypeIICoupledAnalyticGate

/-- Direct arithmetic coordinate system: every dyadic Abel block retains
its allocated share of the combined main and linear correction before the
absolute value is taken. -/
abbrev H15Week3CorrectionCoupledAbelCancellation :=
  EhmDyadicCorrectionCoupledAbelDecay

/-- The weakest signed finite-boundary package exists exactly when the
explicit log-taper energies are cofinally small.  Week 2 has removed the
only former auxiliary hypothesis from this equivalence. -/
theorem nonempty_h15Week3SignedCancellation_iff_cofinalEnergy :
    Nonempty H15Week3SignedCancellation ↔
      Nonempty CofinalLogTaperEnergyVanishing :=
  nonempty_ehmDoubleCofinal_iff_nonempty_cofinalEnergy
    ehmAutocorrelationR1RationalSeriesBridgeProved

/-- A genuine proof of the weakest Week 3 signed estimate closes the
Báez--Duarte criterion. -/
theorem baezDuarteCriterion_of_h15Week3SignedCancellation
    (H : H15Week3SignedCancellation) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmDoubleCofinal
    ehmAutocorrelationR1RationalSeriesBridgeProved H

/-- The same signed estimate closes the Nyman--Beurling criterion through
the proved finite Báez--Duarte equivalence. -/
theorem nymanBeurlingCriterion_of_h15Week3SignedCancellation
    (H : H15Week3SignedCancellation) :
    NymanBeurlingCriterion :=
  nymanBeurlingCriterion_iff_baezDuarteCriterion.mpr
    (baezDuarteCriterion_of_h15Week3SignedCancellation H)

/-- RH follows from the Week 3 estimate once the forward Nyman--Beurling
theorem is supplied explicitly. -/
theorem riemannHypothesis_of_h15Week3SignedCancellation_of_NBForward
    (hNB : NBForward) (H : H15Week3SignedCancellation) :
    RH.Basic.RiemannHypothesis :=
  hNB (nymanBeurlingCriterion_of_h15Week3SignedCancellation H)

/-! ## Stronger Type-I/II route with the value bridge discharged -/

/-- The explicit Type-I/II cancellation gate now has no separate rational
normalization assumption. -/
theorem baezDuarteCriterion_of_h15Week3TypeIICancellation
    (H : H15Week3TypeIICancellation) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmTypeIICoupledAnalyticGate
    ehmAutocorrelationR1RationalSeriesBridgeProved H

/-- Type-I/II cancellation closes the Nyman--Beurling criterion. -/
theorem nymanBeurlingCriterion_of_h15Week3TypeIICancellation
    (H : H15Week3TypeIICancellation) :
    NymanBeurlingCriterion :=
  nymanBeurlingCriterion_of_ehmTypeIICoupledAnalyticGate
    ehmAutocorrelationR1RationalSeriesBridgeProved H

/-- Conditional RH endpoint of the explicit Type-I/II route. -/
theorem riemannHypothesis_of_h15Week3TypeIICancellation_of_NBForward
    (hNB : NBForward) (H : H15Week3TypeIICancellation) :
    RH.Basic.RiemannHypothesis :=
  riemannHypothesis_of_ehmTypeIICoupledAnalyticGate_of_NBForward
    hNB ehmAutocorrelationR1RationalSeriesBridgeProved H

/-! ## Direct correction-coupled Abel route -/

/-- The localized Abel cancellation theorem closes Báez--Duarte with the
rational normalization now discharged. -/
theorem baezDuarteCriterion_of_h15Week3CorrectionCoupledAbelCancellation
    (H : H15Week3CorrectionCoupledAbelCancellation) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmDyadicCorrectionCoupledAbelDecay
    ehmAutocorrelationR1RationalSeriesBridgeProved H

/-- The direct correction-coupled Abel route also closes Nyman--Beurling. -/
theorem nymanBeurlingCriterion_of_h15Week3CorrectionCoupledAbelCancellation
    (H : H15Week3CorrectionCoupledAbelCancellation) :
    NymanBeurlingCriterion :=
  nymanBeurlingCriterion_iff_baezDuarteCriterion.mpr
    (baezDuarteCriterion_of_h15Week3CorrectionCoupledAbelCancellation H)

/-- Conditional RH endpoint of the direct Abel route. -/
theorem riemannHypothesis_of_h15Week3CorrectionCoupledAbelCancellation_of_NBForward
    (hNB : NBForward)
    (H : H15Week3CorrectionCoupledAbelCancellation) :
    RH.Basic.RiemannHypothesis :=
  hNB (nymanBeurlingCriterion_of_h15Week3CorrectionCoupledAbelCancellation H)

end RH.Criteria.NymanBeurling.BCFLogTaperEhmWeek3Closure
