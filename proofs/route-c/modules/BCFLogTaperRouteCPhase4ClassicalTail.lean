import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCLambertPhaseEvaluation
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCAbelPhase4
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorCoefficientIdentification

/-!
# Route C: the two remaining classical Phase 4 inputs

Phase 3 is now unconditional.  This module removes its formerly open Abel
field from the public Phase 4 interface and leaves exactly the two source
theorems that have not yet been formalized:

* the native Taylor series on the unit disc;
* the root-exponential centered-coefficient bound.

The final signed low-mode limit is not a field of this structure and remains
the subsequent RH-strength target.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCPhase4ClassicalTail

open Filter Topology
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelPhase4
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAdaptiveTransfer
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralTaylorRow
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCLambertPhaseEvaluation
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodDiagonal
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodFinitePart
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZero
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCRootAsymptotic
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorAnalytic
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorCoefficientIdentification

/-- Exact classical tail after the unconditional Abel construction. -/
structure BettinConreyRouteCPhase4ClassicalTailData where
  taylorSeries : BettinConreyPsiZeroTaylorSeriesOnDisc
  coefficientAsymptotic :
    BettinConreyCentralCoefficientSourceAsymptoticBound

/-- Literal paper-level form of the same tail.  The Taylor input is only the
printed scalar value identity; the coefficient-identification theorem proves
the native `FormalMultilinearSeries` statement rather than asking for it as
an additional field. -/
structure BettinConreyRouteCPhase4ScalarTailData where
  taylorValue : BettinConreyPsiZeroTaylorValueIdentity
  coefficientAsymptotic :
    BettinConreyCentralCoefficientSourceAsymptoticBound

/-- The scalar Taylor identity and source asymptotic canonically construct
the former native Phase 4 interface. -/
noncomputable def
    BettinConreyRouteCPhase4ScalarTailData.toClassicalTailData
    (D : BettinConreyRouteCPhase4ScalarTailData) :
    BettinConreyRouteCPhase4ClassicalTailData where
  taylorSeries :=
    bettinConreyPsiZeroTaylorSeriesOnDisc_of_valueIdentity
      D.taylorValue D.coefficientAsymptotic.toEnvelope
  coefficientAsymptotic := D.coefficientAsymptotic

/-- Insert the proved Phase 3 Abel data into the original Phase 4 bundle. -/
noncomputable def
    BettinConreyRouteCPhase4ClassicalTailData.toAbelPhase4Data
    (D : BettinConreyRouteCPhase4ClassicalTailData) :
    BettinConreyRouteCAbelPhase4Data where
  abel := bettinConreyCentralAbelConstructorData_proved
  taylorSeries := D.taylorSeries
  coefficientAsymptotic := D.coefficientAsymptotic

/-- The two remaining classical theorems construct the complete central
Taylor package without any further compatibility condition. -/
noncomputable def
    BettinConreyRouteCPhase4ClassicalTailData.toCentralTaylorPackage
    (D : BettinConreyRouteCPhase4ClassicalTailData) :
    BettinConreyCentralTaylorPackage :=
  D.toAbelPhase4Data.toCentralTaylorPackage

noncomputable def
    BettinConreyRouteCPhase4ClassicalTailData.toNormSummableTransfer
    (D : BettinConreyRouteCPhase4ClassicalTailData) :=
  D.toAbelPhase4Data.toPeriodData.toLocalPeriodData
    |>.toPrimitiveSummableData.toNormSummableTransfer

/-- Exact handoff from the two classical inputs to the signed low-mode gate. -/
theorem
    BettinConreyRouteCPhase4ClassicalTailData.exists_cofinal_lowMode_iff_target
    (D : BettinConreyRouteCPhase4ClassicalTailData) :
    ∃ K : ℕ → ℕ,
      (∀ N, N ≤ K N) ∧
      (Tendsto (fun N : ℕ =>
          routeCAdaptiveTransformLow
            D.toNormSummableTransfer
            (K N) N)
          atTop (nhds 0) ↔
        Tendsto routeCCentralFinitePartTarget atTop (nhds 0)) :=
  D.toAbelPhase4Data.exists_cofinal_lowMode_iff_target

/-- Literal source-level handoff to the signed low-mode gate. -/
theorem
    BettinConreyRouteCPhase4ScalarTailData.exists_cofinal_lowMode_iff_target
    (D : BettinConreyRouteCPhase4ScalarTailData) :
    ∃ K : ℕ → ℕ,
      (∀ N, N ≤ K N) ∧
      (Tendsto (fun N : ℕ =>
          routeCAdaptiveTransformLow
            D.toClassicalTailData.toNormSummableTransfer
            (K N) N)
          atTop (nhds 0) ↔
        Tendsto routeCCentralFinitePartTarget atTop (nhds 0)) :=
  D.toClassicalTailData.exists_cofinal_lowMode_iff_target

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCPhase4ClassicalTail
