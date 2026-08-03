import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCPhase4ClassicalTail
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorCoefficientUniqueness

/-!
# Route C Phase 4: reduction to the root-exponential tail

The contour calculation now proves every Taylor coefficient of the normalized
central period.  Therefore the former Taylor-series field in Phase 4 is no
longer an independent classical input: the coefficient asymptotic supplies a
radius bound, and holomorphy plus coefficient uniqueness reconstructs the
series on the entire unit disc.

This file reduces the classical Phase 4 boundary to one source theorem, the
root-exponential saddle-point estimate.  The subsequent signed low-mode limit
remains the separate RH-strength gate.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCPhase4RootTail

open Filter Topology
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAdaptiveTransfer
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodDiagonal
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodFinitePart
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPhase4ClassicalTail
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCRootAsymptotic
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorAnalytic
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorCoefficientUniqueness
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorDerivativeBridge

/-- The source saddle-point bound now constructs the native Taylor theorem;
no scalar value identity or additional coefficient formula is assumed. -/
noncomputable def
    bettinConreyPsiZeroTaylorSeriesOnDisc_of_sourceAsymptotic
    (A : BettinConreyCentralCoefficientSourceAsymptoticBound) :
    BettinConreyPsiZeroTaylorSeriesOnDisc :=
  bettinConreyPsiZeroTaylorSeriesOnDisc_of_derivatives
    bettinConreyPsiZeroTaylorDerivativeIdentification_proved A.toRootDecay

/-- The single remaining classical input inhabits the former two-field Phase
4 tail. -/
noncomputable def
    bettinConreyRouteCPhase4ClassicalTailData_of_sourceAsymptotic
    (A : BettinConreyCentralCoefficientSourceAsymptoticBound) :
    BettinConreyRouteCPhase4ClassicalTailData where
  taylorSeries :=
    bettinConreyPsiZeroTaylorSeriesOnDisc_of_sourceAsymptotic A
  coefficientAsymptotic := A

/-- Direct construction of the central Taylor package from the sole
remaining classical saddle-point input. -/
noncomputable def
    bettinConreyCentralTaylorPackage_of_sourceAsymptotic
    (A : BettinConreyCentralCoefficientSourceAsymptoticBound) :=
  (bettinConreyRouteCPhase4ClassicalTailData_of_sourceAsymptotic A)
    |>.toCentralTaylorPackage

/-- Exact handoff from the root-exponential source estimate to the signed
adaptive low-mode gate. -/
theorem exists_cofinal_lowMode_iff_target_of_sourceAsymptotic
    (A : BettinConreyCentralCoefficientSourceAsymptoticBound) :
    ∃ K : ℕ → ℕ,
      (∀ N, N ≤ K N) ∧
      (Tendsto (fun N : ℕ =>
          routeCAdaptiveTransformLow
            (bettinConreyRouteCPhase4ClassicalTailData_of_sourceAsymptotic A).toNormSummableTransfer
            (K N) N)
          atTop (nhds 0) ↔
        Tendsto routeCCentralFinitePartTarget atTop (nhds 0)) :=
  (bettinConreyRouteCPhase4ClassicalTailData_of_sourceAsymptotic A)
    |>.exists_cofinal_lowMode_iff_target

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCPhase4RootTail
