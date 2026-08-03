import RiemannHypothesis.Criteria.NymanBeurling.FinalAssembly
import RiemannHypothesis.Criteria.NymanBeurling.H15StructuredCorrelationEstimate

/-!
# H15 centered aggregate: an explicit open-problem boundary

The earlier cellwise Farey interface is not a valid H15 target: its weight
class contains point masses, so no fixed logarithmic saving can hold uniformly
for all of its weights.  The corrected object is the coupled, centered
aggregate `H15CenteredAggregateEstimate`, whose terms retain the cancellations
created by the actual cutoff-Möbius kernel.

This is a theorem-matching problem before it is a Lean formalization problem.
Potential routes include a Vaaler reciprocal-phase reduction followed by
Type-I/Type-II estimates, or a suitably matched averaged multiplicative
correlation theorem.  None of those routes is asserted to imply the exact
aggregate below until its weights and uniformity have been checked.
-/

namespace RH.Criteria.NymanBeurling.QuadraticInteraction

open RH.Criteria.NymanBeurling
open RH.Criteria.NymanBeurling.CutoffMobiusKernels
open RH.Criteria.NymanBeurling.MobiusSummatory
open RH.Criteria.NymanBeurling.RHBridge

/-! ## Literature-route labels -/

/-- The three modern routes that could eventually discharge the open estimate.
These constructors are labels only; no route is asserted to be formalized. -/
inductive H15MobiusCorrelationRoute
  | averagedChowla
  | taoTeravainenLogAverage
  | characterTheoretic
  deriving DecidableEq, Repr

def h15MobiusCorrelationRoutes : List H15MobiusCorrelationRoute :=
  [.averagedChowla, .taoTeravainenLogAverage, .characterTheoretic]

/-- Audit labels for the independent obstructions found during reconnaissance.
They are documentation markers, not propositions asserting mathematical
nonexistence. -/
inductive H15MobiusCorrelationObstacle
  | noAveragedChowlaInMathlib
  | noLogAveragedCorrelationInMathlib
  | noCharacterConductorCorrelationInMathlib
  | fixedShiftDoesNotMatchFareyTwoForms
  deriving DecidableEq, Repr

def h15MobiusCorrelationObstacles : List H15MobiusCorrelationObstacle :=
  [.noAveragedChowlaInMathlib,
    .noLogAveragedCorrelationInMathlib,
    .noCharacterConductorCorrelationInMathlib,
    .fixedShiftDoesNotMatchFareyTwoForms]

/-! ## Named open proposition -/

/--
The corrected H15 aggregate estimate as an explicit open problem.  Its
definition is intentionally `Nonempty` rather than an axiom: an eventual proof
must provide the one content-bearing analytic estimate used by the final
conditional RH chain.
-/
def H15CenteredAggregateEstimate_open_problem : Prop :=
  Nonempty H15CenteredAggregateEstimate

theorem h15CenteredAggregateEstimate_open_problem_iff :
    H15CenteredAggregateEstimate_open_problem ↔
      Nonempty H15CenteredAggregateEstimate :=
  Iff.rfl

/-- Extract the corrected aggregate estimate when the open problem is supplied. -/
noncomputable def h15CenteredAggregateEstimate_of_open_problem
    (H : H15CenteredAggregateEstimate_open_problem) :
    H15CenteredAggregateEstimate :=
  Classical.choice H

theorem open_problem_routes_are_documentary :
    h15MobiusCorrelationRoutes.length = 3 := by
  rfl

theorem open_problem_obstacle_audit_length :
    h15MobiusCorrelationObstacles.length = 4 := by
  rfl

/-! ## Retired compatibility boundary -/

/-- Retained with its original value for downstream compatibility.  This is
not a viable H15 target: its underlying cellwise weight class admits point
masses.  Use `H15CenteredAggregateEstimate_open_problem` for the corrected
research boundary. -/
def FareyCellMobiusCorrelationEstimate_Restricted_open_problem : Prop :=
  Nonempty FareyCellMobiusCorrelationEstimate_Restricted

theorem fareyCellMobiusCorrelationEstimate_Restricted_open_problem_iff :
    FareyCellMobiusCorrelationEstimate_Restricted_open_problem ↔
      Nonempty FareyCellMobiusCorrelationEstimate_Restricted :=
  Iff.rfl

/-- Extract the retired cellwise package only for compatibility with older
exploratory code.  It is not used by the corrected final assembly. -/
noncomputable def fareyCellMobiusCorrelationEstimate_of_open_problem
    (H : FareyCellMobiusCorrelationEstimate_Restricted_open_problem) :
    FareyCellMobiusCorrelationEstimate_Restricted :=
  Classical.choice H

/-! ## Conditional endgame wiring -/

/--
The RH conditional result with the corrected H15 debt named explicitly.
Supplying the open proposition only supplies that analytic estimate; it does
not discharge the forward Nyman--Beurling implication.
-/
theorem riemannHypothesis_assuming_centeredAggregate_open_problem
    (H_open : H15CenteredAggregateEstimate_open_problem)
    (H_decay : MobiusSummatory.ClassicalMertensDecay)
    (h_forward : NBForward) :
    RH.Basic.RiemannHypothesis := by
  exact FinalAssembly.riemannHypothesis_of_centeredAggregate_and_NBforward
    H_decay (h15CenteredAggregateEstimate_of_open_problem H_open) h_forward

end RH.Criteria.NymanBeurling.QuadraticInteraction
