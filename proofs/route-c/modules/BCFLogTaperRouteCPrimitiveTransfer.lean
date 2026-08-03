import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCLowModeReduction

/-!
# Route C: assembling primitive transform coefficients

The Bettin--Conrey coefficient expansion is local in a reduced rational
pair, whereas the H15 central target is a weighted sum over the finite
`(g,a,b)` primitive box.  This module proves the exact assembly theorem.

The input keeps, for every primitive H15 pair, a completed contribution and
an absolutely controlled centered transform series.  The completed term is
where the harmonic main coefficient, genuine dual term, finite-part
correction, and retained H15 correction must remain.  Only the centered
series receives the root-exponential estimate.

From this local data we construct a genuine
`RouteCCenteredTransformTransfer`.  Thus the remaining analytic task is no
longer a global exchange of an infinite series with the H15 sum: it is the
primitive-pair coefficient identity and its uniform majorant.

No instance of the primitive data is asserted here.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCPrimitiveTransfer

open Complex
open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralReciprocity
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodDiagonal
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTransformTail
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCLowModeReduction

/-- Primitive-pair coefficient data for the correction-preserving central
transform.  `pair_eq` is the actual Bettin--Conrey coefficient identity that
remains to be supplied; `amplitude` records all arithmetic dependence before
the common root-exponential transform profile is applied. -/
structure RouteCPrimitivePairTransformData where
  c : ℝ
  c_pos : 0 < c
  amplitude : ℕ → ℕ → ℕ → ℕ → ℝ
  amplitude_nonneg : ∀ N g a b, 0 ≤ amplitude N g a b
  completedPair : ℕ → ℕ → ℕ → ℕ → ℂ
  centeredPairMode : ℕ → ℕ → ℕ → ℕ → ℕ → ℂ
  centeredPairMode_bound : ∀ N g a b n,
    ‖centeredPairMode N g a b n‖ ≤
      amplitude N g a b * routeCRootExponentialMajorant c n
  pair_eq : ∀ N g a b,
    ((routeCInteriorCentralCotangentPair N g a b -
        routeCInteriorCentralFinitePartPair N g a b : ℝ) : ℂ) =
      completedPair N g a b +
        ∑' n : ℕ, centeredPairMode N g a b n

/-- Sum a complex primitive-pair expression over the exact H15 box. -/
noncomputable def routeCComplexPairAggregate
    (F : ℕ → ℕ → ℕ → ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ g ∈ Finset.Icc 1 N,
    ∑ a ∈ Finset.Icc 1 (N / g),
      ∑ b ∈ Finset.Icc 1 (N / g), F N g a b

/-- The total arithmetic majorant at outer cutoff `N`. -/
noncomputable def routeCPrimitiveTransformGrowth
    (P : RouteCPrimitivePairTransformData) (N : ℕ) : ℝ :=
  ∑ g ∈ Finset.Icc 1 N,
    ∑ a ∈ Finset.Icc 1 (N / g),
      ∑ b ∈ Finset.Icc 1 (N / g), P.amplitude N g a b

/-- Completed primitive contributions, with every low-frequency correction
still inside the same signed expression. -/
noncomputable def routeCPrimitiveTransformCompletedBase
    (P : RouteCPrimitivePairTransformData) (N : ℕ) : ℂ :=
  routeCComplexPairAggregate P.completedPair N

/-- The `n`-th centered transform coefficient after the full H15 lift. -/
noncomputable def routeCPrimitiveTransformCenteredMode
    (P : RouteCPrimitivePairTransformData) (N n : ℕ) : ℂ :=
  routeCComplexPairAggregate
    (fun N g a b => P.centeredPairMode N g a b n) N

theorem routeCPrimitiveTransformGrowth_nonneg
    (P : RouteCPrimitivePairTransformData) (N : ℕ) :
    0 ≤ routeCPrimitiveTransformGrowth P N := by
  unfold routeCPrimitiveTransformGrowth
  exact Finset.sum_nonneg fun g _hg =>
    Finset.sum_nonneg fun a _ha =>
      Finset.sum_nonneg fun b _hb => P.amplitude_nonneg N g a b

theorem norm_routeCPrimitiveTransformCenteredMode_le
    (P : RouteCPrimitivePairTransformData) (N n : ℕ) :
    ‖routeCPrimitiveTransformCenteredMode P N n‖ ≤
      routeCPrimitiveTransformGrowth P N *
        routeCRootExponentialMajorant P.c n := by
  classical
  unfold routeCPrimitiveTransformCenteredMode routeCComplexPairAggregate
    routeCPrimitiveTransformGrowth
  calc
    ‖∑ g ∈ Finset.Icc 1 N,
        ∑ a ∈ Finset.Icc 1 (N / g),
          ∑ b ∈ Finset.Icc 1 (N / g),
            P.centeredPairMode N g a b n‖ ≤
        ∑ g ∈ Finset.Icc 1 N,
          ∑ a ∈ Finset.Icc 1 (N / g),
            ∑ b ∈ Finset.Icc 1 (N / g),
              ‖P.centeredPairMode N g a b n‖ := by
      exact norm_sum_le_of_le _ fun g _hg =>
        norm_sum_le_of_le _ fun a _ha =>
          norm_sum_le _ _
    _ ≤ ∑ g ∈ Finset.Icc 1 N,
          ∑ a ∈ Finset.Icc 1 (N / g),
            ∑ b ∈ Finset.Icc 1 (N / g),
              P.amplitude N g a b *
                routeCRootExponentialMajorant P.c n := by
      gcongr with g _ a _ b _
      exact P.centeredPairMode_bound N g a b n
    _ = (∑ g ∈ Finset.Icc 1 N,
          ∑ a ∈ Finset.Icc 1 (N / g),
            ∑ b ∈ Finset.Icc 1 (N / g), P.amplitude N g a b) *
          routeCRootExponentialMajorant P.c n := by
      simp only [Finset.sum_mul]

theorem RouteCPrimitivePairTransformData.centeredPairMode_summable
    (P : RouteCPrimitivePairTransformData) (N g a b : ℕ) :
    Summable (P.centeredPairMode N g a b) := by
  have hmajor : Summable (fun n : ℕ =>
      P.amplitude N g a b * routeCRootExponentialMajorant P.c n) :=
    (summable_routeCRootExponentialMajorant P.c P.c_pos).mul_left _
  exact Summable.of_norm_bounded hmajor fun n =>
    P.centeredPairMode_bound N g a b n

/-- A finite H15 aggregate commutes exactly with the absolutely convergent
primitive centered-mode series. -/
theorem tsum_routeCPrimitiveTransformCenteredMode
    (P : RouteCPrimitivePairTransformData) (N : ℕ) :
    (∑' n : ℕ, routeCPrimitiveTransformCenteredMode P N n) =
      routeCComplexPairAggregate
        (fun N g a b => ∑' n : ℕ, P.centeredPairMode N g a b n) N := by
  classical
  unfold routeCPrimitiveTransformCenteredMode routeCComplexPairAggregate
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

/-- The central target is the aggregate of the exact primitive
cotangent-minus-finite-part rows. -/
theorem routeCCentralFinitePartTarget_eq_pairAggregate (N : ℕ) :
    routeCCentralFinitePartTarget N =
      routeCComplexPairAggregate
        (fun N g a b =>
          ((routeCInteriorCentralCotangentPair N g a b -
            routeCInteriorCentralFinitePartPair N g a b : ℝ) : ℂ)) N := by
  unfold routeCCentralFinitePartTarget
    routeCInteriorCentralCotangentAggregate
    routeCInteriorCentralFinitePartAggregate
    routeCInteriorPairAggregate routeCComplexPairAggregate
  push_cast
  simp only [Finset.sum_sub_distrib]

/-- Exact global transfer identity obtained solely from the primitive-pair
coefficient identities and finite absolute sum/series exchange. -/
theorem routeCCentralFinitePartTarget_eq_completedBase_add_centeredModes
    (P : RouteCPrimitivePairTransformData) (N : ℕ) :
    routeCCentralFinitePartTarget N =
      routeCPrimitiveTransformCompletedBase P N +
        ∑' n : ℕ, routeCPrimitiveTransformCenteredMode P N n := by
  rw [routeCCentralFinitePartTarget_eq_pairAggregate,
    tsum_routeCPrimitiveTransformCenteredMode]
  unfold routeCPrimitiveTransformCompletedBase routeCComplexPairAggregate
  simp_rw [P.pair_eq]
  simp only [Finset.sum_add_distrib]

/-- Primitive-pair data automatically supplies the complete global transfer
interface used by the low-mode reduction. -/
noncomputable def RouteCPrimitivePairTransformData.toCenteredTransformTransfer
    (P : RouteCPrimitivePairTransformData) :
    RouteCCenteredTransformTransfer where
  c := P.c
  c_pos := P.c_pos
  growth := routeCPrimitiveTransformGrowth P
  growth_nonneg := routeCPrimitiveTransformGrowth_nonneg P
  completedBase := routeCPrimitiveTransformCompletedBase P
  centeredMode := routeCPrimitiveTransformCenteredMode P
  centeredMode_bound := norm_routeCPrimitiveTransformCenteredMode_le P
  target_eq := routeCCentralFinitePartTarget_eq_completedBase_add_centeredModes P

/-- Final handoff: primitive-pair transfer data already enjoys the cofinal
completed-low-mode stop test proved for the global interface. -/
theorem exists_cofinal_routeCPrimitiveLowMode_tendsto_zero_iff_target
    (P : RouteCPrimitivePairTransformData) :
    ∃ K : ℕ → ℕ,
      (∀ N, N ≤ K N) ∧
      (Filter.Tendsto (fun N : ℕ =>
          routeCCenteredTransformLow P.toCenteredTransformTransfer (K N) N)
          Filter.atTop (nhds 0) ↔
        Filter.Tendsto routeCCentralFinitePartTarget
          Filter.atTop (nhds 0)) :=
  exists_cofinal_routeCCenteredLowMode_tendsto_zero_iff_target
    P.toCenteredTransformTransfer

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCPrimitiveTransfer
