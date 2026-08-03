import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCRootAsymptotic

/-!
# Route C: assembly of the classical Bettin--Conrey inputs

The local Route-C calculation uses four source-level analytic inputs:

1. rational reciprocity together with its central specialization;
2. the parameter-dependent three-term relation;
3. the central Taylor theorem on the open unit disc; and
4. the root-exponential coefficient asymptotic.

This module assembles those inputs without adding an axiom.  An inhabitant of
`BettinConreyRouteCClassicalAnalyticData` produces the exact
`BettinConreyCentralTaylorPackage` used downstream and hence the already
proved equivalence between the adaptive low-mode limit and the Route-C
finite-part target.

The point of the combined structure is auditing: all classical analysis is
visible on the left of the constructor, while the remaining signed H15 limit
is visible on the right of the final equivalence.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCClassicalAssembly

open Filter Topology
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAdaptiveTransfer
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralReciprocity
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralTaylorRow
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodDiagonal
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodFinitePart
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZero
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCRootAsymptotic
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorAnalytic
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCThreeTermDefect

/-- The complete classical analytic input for the source-normalized central
Route-C row.  This is an interface, not an asserted inhabitant. -/
structure BettinConreyRouteCClassicalAnalyticData where
  reciprocity : AuliBettinConreyRationalReciprocityPackage
  centralSpecialization :
    BettinConreyPsiZeroCentralSpecialization reciprocity
  threeTerm : AuliBettinConreyRationalThreeTermPackage reciprocity
  taylorSeries : BettinConreyPsiZeroTaylorSeriesOnDisc
  coefficientAsymptotic :
    BettinConreyCentralCoefficientSourceAsymptoticBound

/-- The source inputs canonically assemble to the local central Taylor
package.  All normalization changes and finite-prefix absorption have already
been proved in the preceding modules. -/
noncomputable def BettinConreyRouteCClassicalAnalyticData.toCentralTaylorPackage
    (D : BettinConreyRouteCClassicalAnalyticData) :
    BettinConreyCentralTaylorPackage :=
  bettinConreyCentralTaylorPackage
    D.reciprocity
    D.centralSpecialization
    D.taylorSeries.toTaylorHasSum
    D.coefficientAsymptotic.toRootDecay

/-- The target reached by the local Taylor package is exactly the signed
primitive-interior period-plus-dual aggregate.  This theorem is also a scope
guard: the local target does not contain the other sectors of the complete
dyadic H15 energy. -/
theorem routeCCentralFinitePartTarget_eq_period_add_dual (N : ℕ) :
    routeCCentralFinitePartTarget N =
      ((routeCInteriorCentralPeriodAggregate N +
        routeCInteriorCentralDualAggregate N : ℝ) : ℂ) := by
  unfold routeCCentralFinitePartTarget
  rw [routeCInteriorCentralCotangent_sub_finitePart]

/-- Complete classical-to-H15 handoff.  Once the four source inputs are
inhabited, no further local analytic lemma is needed: the only remaining
statement is the signed adaptive low-mode limit, equivalently the finite-part
target on the right. -/
theorem BettinConreyRouteCClassicalAnalyticData.exists_cofinal_lowMode_iff_target
    (D : BettinConreyRouteCClassicalAnalyticData) :
    ∃ K : ℕ → ℕ,
      (∀ N, N ≤ K N) ∧
      (Tendsto (fun N : ℕ =>
          routeCAdaptiveTransformLow
            ((D.toCentralTaylorPackage.toUnitIntervalTaylorData.toPeriodCoefficientData
              D.reciprocity D.threeTerm).toLocalPeriodData.toPrimitiveSummableData.toNormSummableTransfer)
            (K N) N)
          atTop (nhds 0) ↔
        Tendsto routeCCentralFinitePartTarget atTop (nhds 0)) :=
  exists_cofinal_routeCCentralTaylorLowMode_iff_target
    D.toCentralTaylorPackage D.reciprocity D.threeTerm

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCClassicalAssembly
