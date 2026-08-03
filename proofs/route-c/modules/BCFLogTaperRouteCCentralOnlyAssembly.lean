import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCClassicalAssembly

/-!
# Route C: central-only analytic assembly

The parameter-dependent Bettin--Conrey family is one way to obtain the
central period theorem, but it is stronger than the downstream Route-C
descent needs.  This module proves a sharper dependency result: it suffices
to know the rational central reciprocity value of `psi_0` and its rational
three-term law.

Consequently a future formal proof may work directly at the central
parameter.  It need not formalize convergence of the entire `psi_a` family
to `psi_0` merely to construct the H15 local Taylor row.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralOnlyAssembly

open Complex Filter Topology
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAdaptiveTransfer
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralReciprocity
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralTaylorRow
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodDescent
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodDiagonal
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodFinitePart
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZero
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCRootAsymptotic
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorAnalytic
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCThreeTermDefect

/-- The exact central information needed from Bettin--Conrey.  Both fields
are rational boundary statements for the single function `psi_0`. -/
structure BettinConreyPsiZeroCentralRationalTheorem where
  reciprocity : ∀ h k : ℕ, 0 < h → 0 < k → Nat.Coprime h k →
    (bettinConreyCentralFinitePartSide h k : ℂ) =
      I / 2 * bettinConreyPsiZero (routeCUnitIntervalRatio h k : ℂ)
  threeTerm : ∀ h k : ℕ, 0 < k → k < h →
    bettinConreyPsiZero
          (((((h - k : ℕ) : ℝ) / (k : ℝ) : ℝ) : ℂ)) -
        bettinConreyPsiZero ((((h : ℝ) / (k : ℝ) : ℝ) : ℂ)) =
      ((k : ℂ) / (h : ℂ)) *
        bettinConreyPsiZero
          (((((h - k : ℕ) : ℝ) / (h : ℝ) : ℝ) : ℂ))

/-- The earlier parameter-dependent source interfaces imply the economical
central-only theorem. -/
noncomputable def BettinConreyPsiZeroCentralRationalTheorem.ofParametric
    (H : AuliBettinConreyRationalReciprocityPackage)
    (S : BettinConreyPsiZeroCentralSpecialization H)
    (T : AuliBettinConreyRationalThreeTermPackage H) :
    BettinConreyPsiZeroCentralRationalTheorem where
  reciprocity := fun h k hh hk hcop =>
    bettinConreyCentralFinitePartSide_eq_psiZero H S h k hh hk hcop
  threeTerm := fun h k hk hkh =>
    bettinConreyPsiZero_rational_threeTerm H S T h k hk hkh

/-- Central reciprocity and the central three-term law imply exactly the
homogeneous finite-part recurrence used by Euclidean descent. -/
theorem BettinConreyPsiZeroCentralRationalTheorem.finitePart_descent
    (C : BettinConreyPsiZeroCentralRationalTheorem)
    (h k : ℕ) (hk : 0 < k) (hkh : k < h) (hcop : Nat.Coprime h k) :
    (bettinConreyCentralFinitePartSide h k : ℂ) =
      (bettinConreyCentralFinitePartSide (h - k) k : ℂ) -
        ((k : ℂ) / (h : ℂ)) *
          (bettinConreyCentralFinitePartSide (h - k) h : ℂ) := by
  have hh : 0 < h := Nat.zero_lt_of_lt hkh
  have hsub : 0 < h - k := Nat.sub_pos_of_lt hkh
  have hcop₁ : Nat.Coprime (h - k) k :=
    (Nat.coprime_sub_self_left hkh.le).2 hcop
  have hcop₂ : Nat.Coprime (h - k) h :=
    (Nat.coprime_self_sub_left hkh.le).2 hcop.symm
  rw [C.reciprocity h k hh hk hcop,
    C.reciprocity (h - k) k hsub hk hcop₁,
    C.reciprocity (h - k) h hsub hh hcop₂]
  have hthree := C.threeTerm h k hk hkh
  simp only [routeCUnitIntervalRatio] at *
  linear_combination -(I / 2) * hthree

/-- Unit-disc Taylor data can therefore be descended using only the central
rational theorem. -/
noncomputable def RouteCUnitIntervalTaylorCoefficientData.toCentralPeriodData
    (D : RouteCUnitIntervalTaylorCoefficientData)
    (C : BettinConreyPsiZeroCentralRationalTheorem) :
    RouteCUnitIntervalPeriodCoefficientData where
  baseCompleted := D.baseCompleted
  baseCenteredMode := D.baseCenteredMode
  baseCenteredMode_norm_summable := D.baseCenteredMode_norm_summable
  base_eq := D.base_eq
  descent_eq := C.finitePart_descent

/-- Minimal classical source data for the central Route-C row. -/
structure BettinConreyRouteCCentralAnalyticData where
  centralRational : BettinConreyPsiZeroCentralRationalTheorem
  taylorSeries : BettinConreyPsiZeroTaylorSeriesOnDisc
  coefficientAsymptotic :
    BettinConreyCentralCoefficientSourceAsymptoticBound

/-- The central-only data constructs the same Taylor package without a
parameter-dependent reciprocity object. -/
noncomputable def BettinConreyRouteCCentralAnalyticData.toCentralTaylorPackage
    (D : BettinConreyRouteCCentralAnalyticData) :
    BettinConreyCentralTaylorPackage :=
  ({
    psiZero := bettinConreyPsiZero
    central_reciprocity := fun h k hh hk _hhk hcop =>
      D.centralRational.reciprocity h k hh hk hcop
    taylor_hasSum := D.taylorSeries.toTaylorHasSum.hasSum
    decayScale := D.coefficientAsymptotic.toRootDecay.scale
    decayRate := D.coefficientAsymptotic.toRootDecay.rate
    decayScale_nonneg := D.coefficientAsymptotic.toRootDecay.scale_nonneg
    decayRate_pos := D.coefficientAsymptotic.toRootDecay.rate_pos
    centered_bound := D.coefficientAsymptotic.toRootDecay.bound } :
      BettinConreyCentralTaylorAnalyticTheorem).toPackage

/-- The minimal source data as the exact Euclidean-descent input. -/
noncomputable def BettinConreyRouteCCentralAnalyticData.toPeriodData
    (D : BettinConreyRouteCCentralAnalyticData) :
    RouteCUnitIntervalPeriodCoefficientData :=
  RouteCUnitIntervalTaylorCoefficientData.toCentralPeriodData
    D.toCentralTaylorPackage.toUnitIntervalTaylorData D.centralRational

/-- Central-only complete handoff to the same signed adaptive low-mode
target. -/
theorem BettinConreyRouteCCentralAnalyticData.exists_cofinal_lowMode_iff_target
    (D : BettinConreyRouteCCentralAnalyticData) :
    ∃ K : ℕ → ℕ,
      (∀ N, N ≤ K N) ∧
      (Tendsto (fun N : ℕ =>
          routeCAdaptiveTransformLow
            (D.toPeriodData.toLocalPeriodData.toPrimitiveSummableData.toNormSummableTransfer)
            (K N) N)
          atTop (nhds 0) ↔
        Tendsto routeCCentralFinitePartTarget atTop (nhds 0)) :=
  exists_cofinal_routeCUnitIntervalLowMode_iff_target
    D.toPeriodData

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralOnlyAssembly
