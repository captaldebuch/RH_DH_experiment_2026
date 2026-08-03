import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCAdaptiveTransfer

/-!
# Route C: local rational-period coefficient transfer

The adaptive primitive assembly leaves one source-level input: expand the
central finite part of the Bettin--Conrey period side at each fixed positive
reduced rational pair into a completed term plus an absolutely summable
centered coefficient series.

This module proves that such local data is sufficient.  It lifts the two
inverse-numerator orientations through the exact H15 primitive-pair scale,
keeps the genuine dual cotangent pair in the completed contribution, proves
absolute summability of the lifted centered modes, and constructs the
adaptive global transfer.

Thus neither the H15 triple aggregation nor correction matching remains in
the analytic input.  The unproved source theorem is precisely the local
rational-period expansion recorded by `RouteCLocalPeriodCoefficientData`.
No inhabitant of that structure is asserted here.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCLocalPeriodTransfer

open Complex Filter Topology
open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperBettinConreyAggregate
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKuznetsovGate
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralReciprocity
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodFinitePart
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodDiagonal
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPrimitiveTransfer
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAdaptiveTransfer

/-- The exact local coefficient theorem still needed from the
Bettin--Conrey period expansion.  `completedPeriod` must retain the harmonic
main coefficient and all local finite-part terms; only `centeredPeriodMode`
is placed in the absolutely summable tail. -/
structure RouteCLocalPeriodCoefficientData where
  completedPeriod : ℕ → ℕ → ℂ
  centeredPeriodMode : ℕ → ℕ → ℕ → ℂ
  centeredPeriodMode_norm_summable : ∀ h k,
    Summable (fun n : ℕ => ‖centeredPeriodMode h k n‖)
  finitePart_eq : ∀ h k, 0 < h → 0 < k → Nat.Coprime h k →
    (bettinConreyCentralFinitePartSide h k : ℂ) =
      completedPeriod h k + ∑' n : ℕ, centeredPeriodMode h k n

theorem RouteCLocalPeriodCoefficientData.centeredPeriodMode_summable
    (L : RouteCLocalPeriodCoefficientData) (h k : ℕ) :
    Summable (L.centeredPeriodMode h k) :=
  (L.centeredPeriodMode_norm_summable h k).of_norm

/-- Completed period contribution for one H15 primitive pair, before the
genuine dual cotangent term is reattached. -/
noncomputable def routeCLocalCompletedPeriodPair
    (L : RouteCLocalPeriodCoefficientData)
    (N g a b : ℕ) : ℂ :=
  if hcop : Nat.Coprime a b then
    if _ha : 2 ≤ a then
      if _hb : 2 ≤ b then
        -(routeCCentralPairScale N g a b : ℂ) *
          (L.completedPeriod (inverseResidueNumerator a b hcop) b +
            L.completedPeriod (inverseResidueNumerator b a hcop.symm) a)
      else 0
    else 0
  else 0

/-- The centered `n`-th period mode for one H15 primitive pair. -/
noncomputable def routeCLocalCenteredPeriodPairMode
    (L : RouteCLocalPeriodCoefficientData)
    (N g a b n : ℕ) : ℂ :=
  if hcop : Nat.Coprime a b then
    if _ha : 2 ≤ a then
      if _hb : 2 ≤ b then
        -(routeCCentralPairScale N g a b : ℂ) *
          (L.centeredPeriodMode (inverseResidueNumerator a b hcop) b n +
            L.centeredPeriodMode
              (inverseResidueNumerator b a hcop.symm) a n)
      else 0
    else 0
  else 0

theorem summable_norm_routeCLocalCenteredPeriodPairMode
    (L : RouteCLocalPeriodCoefficientData)
    (N g a b : ℕ) :
    Summable (fun n : ℕ =>
      ‖routeCLocalCenteredPeriodPairMode L N g a b n‖) := by
  classical
  unfold routeCLocalCenteredPeriodPairMode
  by_cases hcop : Nat.Coprime a b
  · simp only [dif_pos hcop]
    by_cases ha : 2 ≤ a
    · simp only [dif_pos ha]
      by_cases hb : 2 ≤ b
      · simp only [dif_pos hb]
        let h₁ := inverseResidueNumerator a b hcop
        let h₂ := inverseResidueNumerator b a hcop.symm
        let scale : ℂ := -(routeCCentralPairScale N g a b : ℂ)
        have hmajor : Summable (fun n : ℕ =>
            ‖scale‖ *
              (‖L.centeredPeriodMode h₁ b n‖ +
                ‖L.centeredPeriodMode h₂ a n‖)) :=
          ((L.centeredPeriodMode_norm_summable h₁ b).add
            (L.centeredPeriodMode_norm_summable h₂ a)).mul_left ‖scale‖
        apply hmajor.of_nonneg_of_le (fun n => norm_nonneg _)
        intro n
        change ‖scale *
          (L.centeredPeriodMode h₁ b n +
            L.centeredPeriodMode h₂ a n)‖ ≤ _
        rw [norm_mul]
        gcongr
        exact norm_add_le _ _
      · simp only [dif_neg hb]
        simpa only [norm_zero] using
          (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
    · simp only [dif_neg ha]
      simpa only [norm_zero] using
        (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  · simp only [dif_neg hcop]
    simpa only [norm_zero] using
      (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))

/-- The actual central period pair is reconstructed exactly from the local
completed values and the lifted centered coefficient series. -/
theorem routeCInteriorCentralPeriodPairC_eq_localCompleted_add_modes
    (L : RouteCLocalPeriodCoefficientData)
    (N g a b : ℕ) :
    routeCInteriorCentralPeriodPairC N g a b =
      routeCLocalCompletedPeriodPair L N g a b +
        ∑' n : ℕ, routeCLocalCenteredPeriodPairMode L N g a b n := by
  classical
  unfold routeCInteriorCentralPeriodPairC
    routeCLocalCompletedPeriodPair routeCLocalCenteredPeriodPairMode
  by_cases hcop : Nat.Coprime a b
  · simp only [dif_pos hcop]
    by_cases ha : 2 ≤ a
    · simp only [dif_pos ha]
      by_cases hb : 2 ≤ b
      · simp only [dif_pos hb]
        let h₁ := inverseResidueNumerator a b hcop
        let h₂ := inverseResidueNumerator b a hcop.symm
        have hh₁ : 0 < h₁ := inverseResidueNumerator_pos a b hcop hb
        have hh₂ : 0 < h₂ := inverseResidueNumerator_pos b a hcop.symm ha
        have hcop₁ : Nat.Coprime h₁ b :=
          inverseResidueNumerator_coprime a b hcop
        have hcop₂ : Nat.Coprime h₂ a :=
          inverseResidueNumerator_coprime b a hcop.symm
        rw [L.finitePart_eq h₁ b hh₁ (by omega) hcop₁,
          L.finitePart_eq h₂ a hh₂ (by omega) hcop₂]
        have hsum₁ := L.centeredPeriodMode_summable h₁ b
        have hsum₂ := L.centeredPeriodMode_summable h₂ a
        rw [tsum_mul_left, hsum₁.tsum_add hsum₂]
        dsimp only [h₁, h₂]
        ring
      · simp only [dif_neg hb]
        simp
    · simp only [dif_neg ha]
      simp
  · simp only [dif_neg hcop]
    simp

/-- The completed primitive pair retains the genuine dual cotangent term;
it is not estimated separately or discarded. -/
noncomputable def routeCLocalCompletedPrimitivePair
    (L : RouteCLocalPeriodCoefficientData)
    (N g a b : ℕ) : ℂ :=
  routeCLocalCompletedPeriodPair L N g a b +
    (routeCInteriorCentralDualPair N g a b : ℂ)

/-- Exact primitive cotangent-minus-finite-part expansion obtained from the
local rational period theorem. -/
theorem routeCLocalPrimitivePair_eq_completed_add_modes
    (L : RouteCLocalPeriodCoefficientData)
    (N g a b : ℕ) :
    ((routeCInteriorCentralCotangentPair N g a b -
        routeCInteriorCentralFinitePartPair N g a b : ℝ) : ℂ) =
      routeCLocalCompletedPrimitivePair L N g a b +
        ∑' n : ℕ, routeCLocalCenteredPeriodPairMode L N g a b n := by
  have hreal :
      routeCInteriorCentralCotangentPair N g a b -
          routeCInteriorCentralFinitePartPair N g a b =
        routeCInteriorCentralPeriodPair N g a b +
          routeCInteriorCentralDualPair N g a b := by
    rw [routeCInteriorCentralCotangentPair_eq_period_add_dual_add_finitePart]
    ring
  rw [hreal]
  push_cast
  rw [← routeCInteriorCentralPeriodPairC_eq_ofReal,
    routeCInteriorCentralPeriodPairC_eq_localCompleted_add_modes L]
  unfold routeCLocalCompletedPrimitivePair
  ring

/-- Local rational-period coefficient data supplies the exact individually
summable primitive interface. -/
noncomputable def RouteCLocalPeriodCoefficientData.toPrimitiveSummableData
    (L : RouteCLocalPeriodCoefficientData) :
    RouteCPrimitivePairSummableData where
  completedPair := routeCLocalCompletedPrimitivePair L
  centeredPairMode := routeCLocalCenteredPeriodPairMode L
  centeredPairMode_norm_summable :=
    summable_norm_routeCLocalCenteredPeriodPairMode L
  pair_eq := routeCLocalPrimitivePair_eq_completed_add_modes L

/-- Complete handoff from the local Bettin--Conrey coefficient theorem to
the adaptive cofinal H15 stop test. -/
theorem exists_cofinal_routeCLocalPeriodLowMode_iff_target
    (L : RouteCLocalPeriodCoefficientData) :
    ∃ K : ℕ → ℕ,
      (∀ N, N ≤ K N) ∧
      (Tendsto (fun N : ℕ =>
          routeCAdaptiveTransformLow
            L.toPrimitiveSummableData.toNormSummableTransfer (K N) N)
          atTop (nhds 0) ↔
        Tendsto routeCCentralFinitePartTarget atTop (nhds 0)) :=
  exists_cofinal_routeCPrimitiveAdaptiveLowMode_iff_target
    L.toPrimitiveSummableData

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCLocalPeriodTransfer
