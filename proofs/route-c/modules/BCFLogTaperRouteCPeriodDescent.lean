import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCLocalPeriodTransfer

/-!
# Route C: source-normalized rational period descent

For the source normalization, the correction is
`a * k^a * ζ(1-a)/(πh)`.  Its leading parameter cancels the zeta pole, and
the central period-function three-term relation remains homogeneous:

`F(h,k) = F(h-k,k) - (k/h) F(h-k,h)`.

This module formalizes that recurrence and proves that absolutely summable
Taylor expansions on the unit interval `0 < h <= k` propagate to every
positive reduced rational.  Both the completed term and the centered
coefficient rows satisfy the homogeneous recurrence.

The remaining analytic input is the Taylor expansion on `0 < h <= k` and
the proof that the displayed recurrence follows from the Bettin--Conrey
three-term relation.  No inhabitant is asserted here.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodDescent

open Complex Filter Topology
open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralReciprocity
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodDiagonal
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAdaptiveTransfer
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCLocalPeriodTransfer

/-- The logarithmic divided difference which would arise from the unscaled
meromorphic quotient.  It is retained as an auxiliary definition for audit
purposes, but is not part of the source-normalized period descent. -/
noncomputable def routeCCentralPeriodDescentDefect (h k : ℕ) : ℂ :=
  (((k : ℝ) * Real.log ((h : ℝ) / (k : ℝ)) /
    (Real.pi * ((h - k : ℕ) : ℝ) * (h : ℝ))) : ℂ)

/-- Source-normalized Euclidean descent of completed values. -/
noncomputable def routeCPeriodCompletedDescent
    (base : ℕ → ℕ → ℂ) : ℕ → ℕ → ℂ
  | h, k =>
      if k = 0 then 0
      else if h ≤ k then base h k
      else
        routeCPeriodCompletedDescent base (h - k) k -
          ((k : ℂ) / (h : ℂ)) * base (h - k) h
termination_by h _ => h
decreasing_by omega

/-- Homogeneous Euclidean descent of one centered Taylor coefficient. -/
noncomputable def routeCPeriodModeDescent
    (base : ℕ → ℕ → ℂ) : ℕ → ℕ → ℂ
  | h, k =>
      if k = 0 then 0
      else if h ≤ k then base h k
      else
        routeCPeriodModeDescent base (h - k) k -
          ((k : ℂ) / (h : ℂ)) * base (h - k) h
termination_by h _ => h
decreasing_by omega

/-- Source-level data on the Taylor disk together with the exact homogeneous
central three-term recurrence. -/
structure RouteCUnitIntervalPeriodCoefficientData where
  baseCompleted : ℕ → ℕ → ℂ
  baseCenteredMode : ℕ → ℕ → ℕ → ℂ
  baseCenteredMode_norm_summable : ∀ h k,
    Summable (fun n : ℕ => ‖baseCenteredMode h k n‖)
  base_eq : ∀ h k, 0 < h → 0 < k → h ≤ k → Nat.Coprime h k →
    (bettinConreyCentralFinitePartSide h k : ℂ) =
      baseCompleted h k + ∑' n : ℕ, baseCenteredMode h k n
  descent_eq : ∀ h k, 0 < k → k < h → Nat.Coprime h k →
    (bettinConreyCentralFinitePartSide h k : ℂ) =
      (bettinConreyCentralFinitePartSide (h - k) k : ℂ) -
        ((k : ℂ) / (h : ℂ)) *
          (bettinConreyCentralFinitePartSide (h - k) h : ℂ)

/-- Completed local period value obtained by the finite Euclidean descent. -/
noncomputable def routeCDescendedCompletedPeriod
    (D : RouteCUnitIntervalPeriodCoefficientData) (h k : ℕ) : ℂ :=
  routeCPeriodCompletedDescent D.baseCompleted h k

/-- The descended `n`-th centered coefficient. -/
noncomputable def routeCDescendedCenteredPeriodMode
    (D : RouteCUnitIntervalPeriodCoefficientData) (h k n : ℕ) : ℂ :=
  routeCPeriodModeDescent (fun h k => D.baseCenteredMode h k n) h k

theorem summable_norm_routeCDescendedCenteredPeriodMode
    (D : RouteCUnitIntervalPeriodCoefficientData) (h k : ℕ) :
    Summable (fun n : ℕ => ‖routeCDescendedCenteredPeriodMode D h k n‖) := by
  induction h using Nat.strong_induction_on generalizing k with
  | h h ih =>
      by_cases hk0 : k = 0
      · subst k
        apply (summable_zero : Summable (fun _ : ℕ => (0 : ℝ))).congr
        intro n
        unfold routeCDescendedCenteredPeriodMode
        rw [routeCPeriodModeDescent, if_pos rfl, norm_zero]
      · by_cases hle : h ≤ k
        · apply (D.baseCenteredMode_norm_summable h k).congr
          intro n
          unfold routeCDescendedCenteredPeriodMode
          rw [routeCPeriodModeDescent, if_neg hk0, if_pos hle]
        · have hkh : k < h := Nat.lt_of_not_ge hle
          have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
          have hsub : h - k < h := Nat.sub_lt (Nat.zero_lt_of_lt hkh) hkpos
          have hrec := ih (h - k) hsub k
          have hbase := D.baseCenteredMode_norm_summable (h - k) h
          let scalar : ℂ := (k : ℂ) / (h : ℂ)
          have hmajor : Summable (fun n : ℕ =>
              ‖routeCDescendedCenteredPeriodMode D (h - k) k n‖ +
                ‖scalar‖ * ‖D.baseCenteredMode (h - k) h n‖) :=
            hrec.add (hbase.mul_left ‖scalar‖)
          apply hmajor.of_nonneg_of_le (fun n => norm_nonneg _)
          intro n
          unfold routeCDescendedCenteredPeriodMode
          rw [routeCPeriodModeDescent, if_neg hk0, if_neg hle]
          change ‖routeCDescendedCenteredPeriodMode D (h - k) k n -
            scalar * D.baseCenteredMode (h - k) h n‖ ≤ _
          calc
            _ ≤ ‖routeCDescendedCenteredPeriodMode D (h - k) k n‖ +
                ‖scalar * D.baseCenteredMode (h - k) h n‖ :=
              norm_sub_le _ _
            _ = _ := by
              rw [norm_mul]
              rfl

/-- The source-normalized descent reconstructs the central period value
at every positive reduced rational. -/
theorem routeC_finitePart_eq_descendedCompleted_add_modes
    (D : RouteCUnitIntervalPeriodCoefficientData)
    (h k : ℕ) (hh : 0 < h) (hk : 0 < k) (hcop : Nat.Coprime h k) :
    (bettinConreyCentralFinitePartSide h k : ℂ) =
      routeCDescendedCompletedPeriod D h k +
        ∑' n : ℕ, routeCDescendedCenteredPeriodMode D h k n := by
  induction h using Nat.strong_induction_on generalizing k with
  | h h ih =>
      by_cases hle : h ≤ k
      · rw [D.base_eq h k hh hk hle hcop]
        have hcompleted :
            routeCDescendedCompletedPeriod D h k = D.baseCompleted h k := by
          unfold routeCDescendedCompletedPeriod
          rw [routeCPeriodCompletedDescent, if_neg hk.ne', if_pos hle]
        have hmode :
            (fun n : ℕ => routeCDescendedCenteredPeriodMode D h k n) =
              D.baseCenteredMode h k := by
          funext n
          unfold routeCDescendedCenteredPeriodMode
          rw [routeCPeriodModeDescent, if_neg hk.ne', if_pos hle]
        rw [hcompleted, hmode]
      · have hkh : k < h := Nat.lt_of_not_ge hle
        have hsubpos : 0 < h - k := Nat.sub_pos_of_lt hkh
        have hsub : h - k < h := Nat.sub_lt hh hk
        have hcop₁ : Nat.Coprime (h - k) k :=
          (Nat.coprime_sub_self_left hkh.le).2 hcop
        have hcop₂ : Nat.Coprime (h - k) h :=
          (Nat.coprime_self_sub_left hkh.le).2 hcop.symm
        have hrec := ih (h - k) hsub k hsubpos hk hcop₁
        have hbase := D.base_eq (h - k) h hsubpos hh
          (Nat.sub_le h k) hcop₂
        have hrecSum := summable_norm_routeCDescendedCenteredPeriodMode
          D (h - k) k |>.of_norm
        have hbaseSum := D.baseCenteredMode_norm_summable (h - k) h |>.of_norm
        let scalar : ℂ := (k : ℂ) / (h : ℂ)
        have hcompleted :
            routeCDescendedCompletedPeriod D h k =
              routeCDescendedCompletedPeriod D (h - k) k -
                scalar * D.baseCompleted (h - k) h := by
          change routeCPeriodCompletedDescent D.baseCompleted h k =
            routeCPeriodCompletedDescent D.baseCompleted (h - k) k -
              scalar * D.baseCompleted (h - k) h
          rw [routeCPeriodCompletedDescent, if_neg hk.ne', if_neg hle]
        have hmode :
            (∑' n : ℕ, routeCDescendedCenteredPeriodMode D h k n) =
              (∑' n : ℕ,
                routeCDescendedCenteredPeriodMode D (h - k) k n) -
                scalar * ∑' n : ℕ, D.baseCenteredMode (h - k) h n := by
          have hfun :
              (fun n : ℕ => routeCDescendedCenteredPeriodMode D h k n) =
                (fun n : ℕ =>
                  routeCDescendedCenteredPeriodMode D (h - k) k n -
                    scalar * D.baseCenteredMode (h - k) h n) := by
            funext n
            unfold routeCDescendedCenteredPeriodMode
            rw [routeCPeriodModeDescent, if_neg hk.ne', if_neg hle]
          rw [hfun]
          rw [Summable.tsum_sub hrecSum (hbaseSum.mul_left scalar),
            tsum_mul_left]
        rw [D.descent_eq h k hk hkh hcop, hrec, hbase]
        rw [hcompleted, hmode]
        ring

/-- Unit-interval Taylor data plus the homogeneous three-term relation produces
the exact local-period interface used by the H15 lift. -/
noncomputable def RouteCUnitIntervalPeriodCoefficientData.toLocalPeriodData
    (D : RouteCUnitIntervalPeriodCoefficientData) :
    RouteCLocalPeriodCoefficientData where
  completedPeriod := routeCDescendedCompletedPeriod D
  centeredPeriodMode := routeCDescendedCenteredPeriodMode D
  centeredPeriodMode_norm_summable :=
    summable_norm_routeCDescendedCenteredPeriodMode D
  finitePart_eq := routeC_finitePart_eq_descendedCompleted_add_modes D

/-- Complete handoff from source-normalized unit-interval period data to
the adaptive cofinal H15 stop test. -/
theorem exists_cofinal_routeCUnitIntervalLowMode_iff_target
    (D : RouteCUnitIntervalPeriodCoefficientData) :
    ∃ K : ℕ → ℕ,
      (∀ N, N ≤ K N) ∧
      (Tendsto (fun N : ℕ =>
          routeCAdaptiveTransformLow
            D.toLocalPeriodData.toPrimitiveSummableData.toNormSummableTransfer
            (K N) N)
          atTop (nhds 0) ↔
        Tendsto routeCCentralFinitePartTarget atTop (nhds 0)) :=
  exists_cofinal_routeCLocalPeriodLowMode_iff_target D.toLocalPeriodData

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodDescent
