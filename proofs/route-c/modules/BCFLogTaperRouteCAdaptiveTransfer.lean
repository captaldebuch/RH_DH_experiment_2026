import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCPrimitiveTransfer

/-!
# Route C: adaptive transform tails

Bettin--Conrey's coefficient asymptotic at a point `tau` contains the factor
`exp (-2 * sqrt (pi * tau * n))`.  Along H15 rational pairs, `tau` can tend
to zero as the denominator grows, so a single denominator-uniform positive
decay constant is not available from that theorem.

Uniformity is unnecessary for the cofinal low-mode reduction.  At every
fixed outer cutoff the primitive H15 box is finite, and every fixed positive
rational parameter still gives an absolutely summable coefficient row.  The
transform cutoff may then be selected separately at each outer scale.

This module proves that stronger adaptive result.  It first shows that any
exact transform whose centered rows are norm-summable admits a cofinal
`O(1/N)` truncation.  It then assembles such data from individually
norm-summable primitive rational pairs.  No uniform decay rate in the pair
variables is assumed.

No instance of the primitive analytic data is asserted here.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCAdaptiveTransfer

open Complex Filter Topology
open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralReciprocity
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodDiagonal
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPrimitiveTransfer

/-! ## Generic norm-summable low-mode reduction -/

/-- The exact data actually needed for cofinal truncation.  No uniform
coefficient rate is required; absolute summability is asserted row by row. -/
structure RouteCNormSummableTransformTransfer where
  completedBase : ℕ → ℂ
  centeredMode : ℕ → ℕ → ℂ
  centeredMode_norm_summable : ∀ N,
    Summable (fun n : ℕ => ‖centeredMode N n‖)
  target_eq : ∀ N,
    routeCCentralFinitePartTarget N =
      completedBase N + ∑' n : ℕ, centeredMode N n

theorem RouteCNormSummableTransformTransfer.centeredMode_summable
    (T : RouteCNormSummableTransformTransfer) (N : ℕ) :
    Summable (T.centeredMode N) :=
  (T.centeredMode_norm_summable N).of_norm

/-- Completed low modes through transform index `K`. -/
noncomputable def routeCAdaptiveTransformLow
    (T : RouteCNormSummableTransformTransfer) (K N : ℕ) : ℂ :=
  T.completedBase N + ∑ n ∈ Finset.range (K + 1), T.centeredMode N n

/-- The shifted infinite tail after transform index `K`. -/
noncomputable def routeCAdaptiveTransformTail
    (T : RouteCNormSummableTransformTransfer) (K N : ℕ) : ℂ :=
  ∑' r : ℕ, T.centeredMode N (r + (K + 1))

theorem routeCCentralFinitePartTarget_eq_adaptiveLow_add_tail
    (T : RouteCNormSummableTransformTransfer) (K N : ℕ) :
    routeCCentralFinitePartTarget N =
      routeCAdaptiveTransformLow T K N +
        routeCAdaptiveTransformTail T K N := by
  rw [T.target_eq N]
  have hsplit := Summable.sum_add_tsum_nat_add
    (K + 1) (T.centeredMode_summable N)
  unfold routeCAdaptiveTransformLow routeCAdaptiveTransformTail
  rw [← hsplit]
  ring

theorem norm_routeCAdaptiveTransformTail_le
    (T : RouteCNormSummableTransformTransfer) (K N : ℕ) :
    ‖routeCAdaptiveTransformTail T K N‖ ≤
      ∑' r : ℕ, ‖T.centeredMode N (r + (K + 1))‖ := by
  unfold routeCAdaptiveTransformTail
  exact norm_tsum_le_tsum_norm
    ((summable_nat_add_iff (K + 1)).2
      (T.centeredMode_norm_summable N))

/-- Rowwise absolute summability suffices to select a cofinal cutoff with
error at most `1/(N+1)`, even when the decay rate deteriorates with `N`. -/
theorem exists_cofinal_routeCAdaptiveLowModeApproximation
    (T : RouteCNormSummableTransformTransfer) :
    ∃ K : ℕ → ℕ,
      (∀ N, N ≤ K N) ∧
      ∀ N,
        ‖routeCCentralFinitePartTarget N -
            routeCAdaptiveTransformLow T (K N) N‖ ≤
          1 / ((N : ℝ) + 1) := by
  let normTail : ℕ → ℕ → ℝ := fun N i =>
    ∑' r : ℕ, ‖T.centeredMode N (r + i)‖
  have htail : ∀ N : ℕ, Tendsto (normTail N) atTop (nhds 0) := by
    intro N
    exact tendsto_sum_nat_add (fun n : ℕ => ‖T.centeredMode N n‖)
  have hchoice : ∀ N : ℕ, ∃ K : ℕ, N ≤ K ∧
      normTail N (K + 1) ≤ 1 / ((N : ℝ) + 1) := by
    intro N
    have hε : 0 < 1 / ((N : ℝ) + 1) := by positivity
    have hevent : ∀ᶠ i : ℕ in atTop,
        normTail N i < 1 / ((N : ℝ) + 1) := by
      have hmetric := Metric.tendsto_nhds.mp (htail N)
        (1 / ((N : ℝ) + 1)) hε
      filter_upwards [hmetric] with i hi
      have hnonneg : 0 ≤ normTail N i := by
        unfold normTail
        exact tsum_nonneg fun r => norm_nonneg _
      simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hi
    rcases eventually_atTop.1 hevent with ⟨K₀, hK₀⟩
    let K := max N K₀
    refine ⟨K, le_max_left _ _, ?_⟩
    exact (hK₀ (K + 1)
      (le_trans (le_max_right N K₀) (Nat.le_succ K))).le
  let K : ℕ → ℕ := fun N => Classical.choose (hchoice N)
  refine ⟨K, fun N => (Classical.choose_spec (hchoice N)).1, ?_⟩
  intro N
  have hnorm := norm_routeCAdaptiveTransformTail_le T (K N) N
  calc
    ‖routeCCentralFinitePartTarget N -
        routeCAdaptiveTransformLow T (K N) N‖ =
        ‖routeCAdaptiveTransformTail T (K N) N‖ := by
      rw [routeCCentralFinitePartTarget_eq_adaptiveLow_add_tail T (K N) N]
      congr 1
      ring
    _ ≤ ∑' r : ℕ, ‖T.centeredMode N (r + (K N + 1))‖ := hnorm
    _ = normTail N (K N + 1) := rfl
    _ ≤ 1 / ((N : ℝ) + 1) :=
      (Classical.choose_spec (hchoice N)).2

theorem exists_cofinal_routeCAdaptiveLowMode_difference_tendsto_zero
    (T : RouteCNormSummableTransformTransfer) :
    ∃ K : ℕ → ℕ,
      (∀ N, N ≤ K N) ∧
      Tendsto (fun N : ℕ =>
        routeCCentralFinitePartTarget N -
          routeCAdaptiveTransformLow T (K N) N)
        atTop (nhds 0) := by
  rcases exists_cofinal_routeCAdaptiveLowModeApproximation T with
    ⟨K, hK, hbound⟩
  refine ⟨K, hK, ?_⟩
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact Eventually.of_forall hbound

/-- Adaptive stop test: target decay is equivalent to decay of a cofinally
growing completed low-mode expression. -/
theorem exists_cofinal_routeCAdaptiveLowMode_tendsto_zero_iff_target
    (T : RouteCNormSummableTransformTransfer) :
    ∃ K : ℕ → ℕ,
      (∀ N, N ≤ K N) ∧
      (Tendsto (fun N : ℕ => routeCAdaptiveTransformLow T (K N) N)
          atTop (nhds 0) ↔
        Tendsto routeCCentralFinitePartTarget atTop (nhds 0)) := by
  rcases exists_cofinal_routeCAdaptiveLowMode_difference_tendsto_zero T with
    ⟨K, hK, hdifference⟩
  refine ⟨K, hK, ?_⟩
  constructor
  · intro hlow
    have h := hdifference.add hlow
    convert h using 1
    · funext N
      ring
    · ring
  · intro htarget
    have h := htarget.sub hdifference
    convert h using 1
    · funext N
      ring
    · ring

/-! ## Assembly from individually summable primitive rational pairs -/

/-- Local primitive data with no denominator-uniform decay constant. -/
structure RouteCPrimitivePairSummableData where
  completedPair : ℕ → ℕ → ℕ → ℕ → ℂ
  centeredPairMode : ℕ → ℕ → ℕ → ℕ → ℕ → ℂ
  centeredPairMode_norm_summable : ∀ N g a b,
    Summable (fun n : ℕ => ‖centeredPairMode N g a b n‖)
  pair_eq : ∀ N g a b,
    ((routeCInteriorCentralCotangentPair N g a b -
        routeCInteriorCentralFinitePartPair N g a b : ℝ) : ℂ) =
      completedPair N g a b +
        ∑' n : ℕ, centeredPairMode N g a b n

noncomputable def routeCPrimitiveSummableCompletedBase
    (P : RouteCPrimitivePairSummableData) (N : ℕ) : ℂ :=
  routeCComplexPairAggregate P.completedPair N

noncomputable def routeCPrimitiveSummableCenteredMode
    (P : RouteCPrimitivePairSummableData) (N n : ℕ) : ℂ :=
  routeCComplexPairAggregate
    (fun N g a b => P.centeredPairMode N g a b n) N

theorem RouteCPrimitivePairSummableData.centeredPairMode_summable
    (P : RouteCPrimitivePairSummableData) (N g a b : ℕ) :
    Summable (P.centeredPairMode N g a b) :=
  (P.centeredPairMode_norm_summable N g a b).of_norm

theorem RouteCPrimitivePairSummableData.aggregateMode_norm_summable
    (P : RouteCPrimitivePairSummableData) (N : ℕ) :
    Summable (fun n : ℕ =>
      ‖routeCPrimitiveSummableCenteredMode P N n‖) := by
  let major : ℕ → ℝ := fun n =>
    ∑ g ∈ Finset.Icc 1 N,
      ∑ a ∈ Finset.Icc 1 (N / g),
        ∑ b ∈ Finset.Icc 1 (N / g),
          ‖P.centeredPairMode N g a b n‖
  have hmajor : Summable major := by
    unfold major
    exact summable_sum fun g _hg =>
      summable_sum fun a _ha =>
        summable_sum fun b _hb =>
          P.centeredPairMode_norm_summable N g a b
  apply hmajor.of_nonneg_of_le (fun n => norm_nonneg _)
  intro n
  unfold routeCPrimitiveSummableCenteredMode routeCComplexPairAggregate major
  exact norm_sum_le_of_le _ fun g _hg =>
    norm_sum_le_of_le _ fun a _ha =>
      norm_sum_le _ _

theorem tsum_routeCPrimitiveSummableCenteredMode
    (P : RouteCPrimitivePairSummableData) (N : ℕ) :
    (∑' n : ℕ, routeCPrimitiveSummableCenteredMode P N n) =
      routeCComplexPairAggregate
        (fun N g a b => ∑' n : ℕ, P.centeredPairMode N g a b n) N := by
  classical
  unfold routeCPrimitiveSummableCenteredMode routeCComplexPairAggregate
  rw [Summable.tsum_finsetSum (fun g _hg =>
    summable_sum fun a _ha =>
      summable_sum fun b _hb => P.centeredPairMode_summable N g a b)]
  apply Finset.sum_congr rfl
  intro g _hg
  rw [Summable.tsum_finsetSum (fun a _ha =>
    summable_sum fun b _hb => P.centeredPairMode_summable N g a b)]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Summable.tsum_finsetSum (fun b _hb =>
    P.centeredPairMode_summable N g a b)]

theorem routeCCentralFinitePartTarget_eq_summableCompleted_add_modes
    (P : RouteCPrimitivePairSummableData) (N : ℕ) :
    routeCCentralFinitePartTarget N =
      routeCPrimitiveSummableCompletedBase P N +
        ∑' n : ℕ, routeCPrimitiveSummableCenteredMode P N n := by
  rw [routeCCentralFinitePartTarget_eq_pairAggregate,
    tsum_routeCPrimitiveSummableCenteredMode]
  unfold routeCPrimitiveSummableCompletedBase routeCComplexPairAggregate
  simp_rw [P.pair_eq]
  simp only [Finset.sum_add_distrib]

/-- Individually summable primitive rational expansions assemble into the
adaptive global transfer with no common rate assumption. -/
noncomputable def RouteCPrimitivePairSummableData.toNormSummableTransfer
    (P : RouteCPrimitivePairSummableData) :
    RouteCNormSummableTransformTransfer where
  completedBase := routeCPrimitiveSummableCompletedBase P
  centeredMode := routeCPrimitiveSummableCenteredMode P
  centeredMode_norm_summable := P.aggregateMode_norm_summable
  target_eq := routeCCentralFinitePartTarget_eq_summableCompleted_add_modes P

theorem exists_cofinal_routeCPrimitiveAdaptiveLowMode_iff_target
    (P : RouteCPrimitivePairSummableData) :
    ∃ K : ℕ → ℕ,
      (∀ N, N ≤ K N) ∧
      (Tendsto (fun N : ℕ =>
          routeCAdaptiveTransformLow P.toNormSummableTransfer (K N) N)
          atTop (nhds 0) ↔
        Tendsto routeCCentralFinitePartTarget atTop (nhds 0)) :=
  exists_cofinal_routeCAdaptiveLowMode_tendsto_zero_iff_target
    P.toNormSummableTransfer

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCAdaptiveTransfer
