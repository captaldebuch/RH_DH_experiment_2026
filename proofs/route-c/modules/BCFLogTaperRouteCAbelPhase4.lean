import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCAbelCentralConstructor

/-!
# Route C: Phase 4 Abel-to-Taylor handoff

The central Abel programme and the local Taylor programme meet at one exact
interface.  Phase 3 constructs the rational central reciprocity theorem from
the two boundary evaluations of the coupled Lambert period.  The remaining
classical inputs are Bettin--Conrey's Taylor theorem on the unit disc and the
root-exponential saddle-point estimate for its centered coefficients.

This module assembles those three independent pieces into the already proved
Route-C central analytic data.  It adds no analytic assertion: an inhabitant
must still contain genuine proofs of every source theorem.  Once inhabited,
the local Taylor package, Euclidean descent, and adaptive low-mode reduction
are consequences rather than additional hypotheses.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelPhase4

open Filter Topology
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAdaptiveTransfer
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelCentralConstructor
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralOnlyAssembly
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralTaylorRow
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodDiagonal
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodFinitePart
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCRootAsymptotic
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorAnalytic

/-- Complete classical input at the Phase 4 boundary.

The first field is the Phase 3 Abel constructor.  The other two fields are
the paper's native Taylor and saddle-point theorems.  This separation is
intentional: neither coefficient decay nor a Taylor identity is smuggled
into the rational-boundary proof. -/
structure BettinConreyRouteCAbelPhase4Data where
  abel : BettinConreyCentralAbelConstructorData
  taylorSeries : BettinConreyPsiZeroTaylorSeriesOnDisc
  coefficientAsymptotic :
    BettinConreyCentralCoefficientSourceAsymptoticBound

/-- Phase 4 produces exactly the economical central analytic interface used
by Route C. -/
noncomputable def BettinConreyRouteCAbelPhase4Data.toCentralAnalyticData
    (D : BettinConreyRouteCAbelPhase4Data) :
    BettinConreyRouteCCentralAnalyticData where
  centralRational := D.abel.toCentralRationalTheorem
  taylorSeries := D.taylorSeries
  coefficientAsymptotic := D.coefficientAsymptotic

/-- The exact local Taylor package obtained after the Abel boundary, Taylor
series, and saddle-point estimate have all been proved. -/
noncomputable def BettinConreyRouteCAbelPhase4Data.toCentralTaylorPackage
    (D : BettinConreyRouteCAbelPhase4Data) :
    BettinConreyCentralTaylorPackage :=
  D.toCentralAnalyticData.toCentralTaylorPackage

/-- Phase 4 also constructs the Euclidean-descent coefficient data. -/
noncomputable def BettinConreyRouteCAbelPhase4Data.toPeriodData
    (D : BettinConreyRouteCAbelPhase4Data) :=
  D.toCentralAnalyticData.toPeriodData

/-- Complete Phase 4 handoff to the signed adaptive low-mode target.

The theorem is deliberately an equivalence.  The classical Abel/Taylor
analysis changes the representation of the target, but it does not assert
the final RH-strength signed limit. -/
theorem BettinConreyRouteCAbelPhase4Data.exists_cofinal_lowMode_iff_target
    (D : BettinConreyRouteCAbelPhase4Data) :
    ∃ K : ℕ → ℕ,
      (∀ N, N ≤ K N) ∧
      (Tendsto (fun N : ℕ =>
          routeCAdaptiveTransformLow
            (D.toPeriodData.toLocalPeriodData.toPrimitiveSummableData.toNormSummableTransfer)
            (K N) N)
          atTop (nhds 0) ↔
        Tendsto routeCCentralFinitePartTarget atTop (nhds 0)) :=
  D.toCentralAnalyticData.exists_cofinal_lowMode_iff_target

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelPhase4
