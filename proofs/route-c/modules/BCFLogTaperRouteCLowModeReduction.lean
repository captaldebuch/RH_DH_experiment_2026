import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCTransformTail

/-!
# Route C: exact reduction to completed low transform modes

The Taylor coefficients in Bettin--Conrey contain an explicit harmonic main
part; only the centered remainder has root-exponential decay.  Consequently
the main part, the H15 linear and endpoint corrections, and the finite-part
terms must first be assembled into one completed base.

This module records that exact transfer convention and proves its complete
consequence.  Once the central H15 target is represented as the completed
base plus an absolutely convergent centered mode series with a separated
root-exponential majorant, a cofinal cutoff makes the high modes `O(1/N)`.
Decay of the exact target is then equivalent to decay of the retained signed
low-mode expression.

No inhabitant of the transfer structure is asserted here.  Constructing one
requires matching the Bettin--Conrey Taylor formula to the complete weighted
H15 post-central sector without dropping its correction terms.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCLowModeReduction

open Complex Filter Topology
open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodDiagonal
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTransformTail

/-- Exact coefficient-transfer data after the harmonic main coefficient and
all retained H15 corrections have been placed in `completedBase`. -/
structure RouteCCenteredTransformTransfer where
  c : ℝ
  c_pos : 0 < c
  growth : ℕ → ℝ
  growth_nonneg : ∀ N, 0 ≤ growth N
  completedBase : ℕ → ℂ
  centeredMode : ℕ → ℕ → ℂ
  centeredMode_bound : ∀ N n,
    ‖centeredMode N n‖ ≤
      growth N * routeCRootExponentialMajorant c n
  target_eq : ∀ N,
    routeCCentralFinitePartTarget N =
      completedBase N + ∑' n : ℕ, centeredMode N n

theorem RouteCCenteredTransformTransfer.centeredMode_norm_summable
    (T : RouteCCenteredTransformTransfer) (N : ℕ) :
    Summable (fun n : ℕ => ‖T.centeredMode N n‖) := by
  have hmajor : Summable (fun n : ℕ =>
      T.growth N * routeCRootExponentialMajorant T.c n) :=
    (summable_routeCRootExponentialMajorant T.c T.c_pos).mul_left _
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (T.centeredMode_bound N) hmajor

theorem RouteCCenteredTransformTransfer.centeredMode_summable
    (T : RouteCCenteredTransformTransfer) (N : ℕ) :
    Summable (T.centeredMode N) :=
  (T.centeredMode_norm_summable N).of_norm

/-- The retained signed low modes, including the already-completed base. -/
noncomputable def routeCCenteredTransformLow
    (T : RouteCCenteredTransformTransfer) (K N : ℕ) : ℂ :=
  T.completedBase N + ∑ n ∈ Finset.range (K + 1), T.centeredMode N n

/-- The absolutely convergent mode tail after cutoff `K`. -/
noncomputable def routeCCenteredTransformTail
    (T : RouteCCenteredTransformTransfer) (K N : ℕ) : ℂ :=
  ∑' r : ℕ, T.centeredMode N (r + (K + 1))

/-- Exact low-plus-tail decomposition of the central H15 target. -/
theorem routeCCentralFinitePartTarget_eq_low_add_tail
    (T : RouteCCenteredTransformTransfer) (K N : ℕ) :
    routeCCentralFinitePartTarget N =
      routeCCenteredTransformLow T K N +
        routeCCenteredTransformTail T K N := by
  rw [T.target_eq N]
  have hsplit := Summable.sum_add_tsum_nat_add
    (K + 1) (T.centeredMode_summable N)
  unfold routeCCenteredTransformLow routeCCenteredTransformTail
  rw [← hsplit]
  ring

set_option maxHeartbeats 800000 in
-- Elaborating the nested shifted `tsum` comparison is costly, so the larger
-- heartbeat budget is scoped to this tail-bound declaration.
theorem norm_routeCCenteredTransformTail_le
    (T : RouteCCenteredTransformTransfer) (K N : ℕ) :
    ‖routeCCenteredTransformTail T K N‖ ≤
      T.growth N *
        ∑' r : ℕ, routeCRootExponentialMajorant T.c (r + (K + 1)) := by
  have hnorm : Summable (fun r : ℕ =>
      ‖T.centeredMode N (r + (K + 1))‖) :=
    (summable_nat_add_iff (K + 1)).2 (T.centeredMode_norm_summable N)
  have hmajorFull : Summable (fun n : ℕ =>
      T.growth N * routeCRootExponentialMajorant T.c n) :=
    (summable_routeCRootExponentialMajorant T.c T.c_pos).mul_left _
  have hmajor : Summable (fun r : ℕ =>
      T.growth N *
        routeCRootExponentialMajorant T.c (r + (K + 1))) :=
    (summable_nat_add_iff (K + 1)).2 hmajorFull
  calc
    ‖routeCCenteredTransformTail T K N‖ ≤
        ∑' r : ℕ, ‖T.centeredMode N (r + (K + 1))‖ := by
      unfold routeCCenteredTransformTail
      exact norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' r : ℕ, T.growth N *
        routeCRootExponentialMajorant T.c (r + (K + 1)) :=
      Summable.tsum_le_tsum
        (fun r => T.centeredMode_bound N (r + (K + 1))) hnorm hmajor
    _ = T.growth N *
        ∑' r : ℕ, routeCRootExponentialMajorant T.c (r + (K + 1)) :=
      tsum_mul_left

/-- A cofinal low-mode cutoff makes the exact central target and its
completed low-mode approximation differ by at most `1/(N+1)`. -/
theorem exists_cofinal_routeCCenteredLowModeApproximation
    (T : RouteCCenteredTransformTransfer) :
    ∃ K : ℕ → ℕ,
      (∀ N, N ≤ K N) ∧
      ∀ N,
        ‖routeCCentralFinitePartTarget N -
            routeCCenteredTransformLow T (K N) N‖ ≤
          1 / ((N : ℝ) + 1) := by
  let rootTail : ℕ → ℝ := fun i =>
    ∑' r : ℕ, routeCRootExponentialMajorant T.c (r + i)
  have hrootTail : Tendsto rootTail atTop (nhds 0) := by
    exact tendsto_sum_nat_add (routeCRootExponentialMajorant T.c)
  have hchoice : ∀ N : ℕ, ∃ K : ℕ, N ≤ K ∧
      T.growth N * rootTail (K + 1) ≤ 1 / ((N : ℝ) + 1) := by
    intro N
    let ε : ℝ := 1 / (((N : ℝ) + 1) * (T.growth N + 1))
    have hε : 0 < ε := by
      unfold ε
      have hg := T.growth_nonneg N
      positivity
    have hevent : ∀ᶠ i : ℕ in atTop, rootTail i < ε := by
      have hmetric := Metric.tendsto_nhds.mp hrootTail ε hε
      filter_upwards [hmetric] with i hi
      have htail_nonneg : 0 ≤ rootTail i := by
        unfold rootTail
        exact tsum_nonneg fun r => routeCRootExponentialMajorant_nonneg _ _
      simpa [Real.dist_eq, abs_of_nonneg htail_nonneg] using hi
    rcases eventually_atTop.1 hevent with ⟨K₀, hK₀⟩
    let K := max N K₀
    refine ⟨K, le_max_left _ _, ?_⟩
    have htail : rootTail (K + 1) ≤ ε :=
      (hK₀ (K + 1) (le_trans (le_max_right N K₀) (Nat.le_succ K))).le
    have hg0 : 0 ≤ T.growth N := T.growth_nonneg N
    have hNpos : 0 < (N : ℝ) + 1 := by positivity
    have hgpos : 0 < T.growth N + 1 := by linarith
    calc
      T.growth N * rootTail (K + 1) ≤ T.growth N * ε :=
        mul_le_mul_of_nonneg_left htail hg0
      _ = (T.growth N / (T.growth N + 1)) *
          (1 / ((N : ℝ) + 1)) := by
        unfold ε
        field_simp
      _ ≤ 1 * (1 / ((N : ℝ) + 1)) := by
        gcongr
        exact (div_le_one hgpos).2 (by linarith)
      _ = 1 / ((N : ℝ) + 1) := one_mul _
  let K : ℕ → ℕ := fun N => Classical.choose (hchoice N)
  refine ⟨K, fun N => (Classical.choose_spec (hchoice N)).1, ?_⟩
  intro N
  have htail := norm_routeCCenteredTransformTail_le T (K N) N
  have hselected := (Classical.choose_spec (hchoice N)).2
  calc
    ‖routeCCentralFinitePartTarget N -
        routeCCenteredTransformLow T (K N) N‖ =
        ‖routeCCenteredTransformTail T (K N) N‖ := by
      rw [routeCCentralFinitePartTarget_eq_low_add_tail T (K N) N]
      congr 1
      ring
    _ ≤ T.growth N *
        ∑' r : ℕ,
          routeCRootExponentialMajorant T.c (r + (K N + 1)) := htail
    _ = T.growth N * rootTail (K N + 1) := rfl
    _ ≤ 1 / ((N : ℝ) + 1) := hselected

/-- For the selected cofinal cutoff, the exact target minus the completed
low-mode expression tends to zero. -/
theorem exists_cofinal_routeCCenteredLowMode_difference_tendsto_zero
    (T : RouteCCenteredTransformTransfer) :
    ∃ K : ℕ → ℕ,
      (∀ N, N ≤ K N) ∧
      Tendsto (fun N : ℕ =>
        routeCCentralFinitePartTarget N -
          routeCCenteredTransformLow T (K N) N)
        atTop (nhds 0) := by
  rcases exists_cofinal_routeCCenteredLowModeApproximation T with
    ⟨K, hK, hbound⟩
  refine ⟨K, hK, ?_⟩
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact Eventually.of_forall hbound

/-- The final stop test: after an exact centered transform transfer, decay
of H15 is equivalent to signed decay of the completed retained low modes. -/
theorem exists_cofinal_routeCCenteredLowMode_tendsto_zero_iff_target
    (T : RouteCCenteredTransformTransfer) :
    ∃ K : ℕ → ℕ,
      (∀ N, N ≤ K N) ∧
      (Tendsto (fun N : ℕ => routeCCenteredTransformLow T (K N) N)
          atTop (nhds 0) ↔
        Tendsto routeCCentralFinitePartTarget atTop (nhds 0)) := by
  rcases exists_cofinal_routeCCenteredLowMode_difference_tendsto_zero T with
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

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCLowModeReduction
