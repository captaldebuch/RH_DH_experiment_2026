import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmMaierRassiasWeightedTransfer
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge

/-!
# Exact collapse of the Ehm Type-I `q ≥ 2` sector

Priority 3 asks whether the rational `R₁`-series bridge removes the auxiliary
`q` variable before any absolute values are introduced.  It does.

The finite `q ≥ 2` row is exactly a positive-index `R₁` partial series minus
its `q = 1` term.  Under an `EhmR1RationalSeriesBridge`, the full finite H15
sector therefore converges, for fixed outer cutoffs, to a signed bilinear
`(d,m)` sum with kernel `S₁(d/m)-R₁(d/m)`.

This removes `q` but does not separate the two remaining arithmetic
variables and supplies no cutoff-uniform convergence rate.  Those two facts
are the surviving H15-strength obstruction.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmQGeTwoCollapse

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDirectFeasibility
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmSeriesBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmTypeIISplit

private theorem sum_Icc_one_eq_value_add_sum_Icc_two
    {R : Type*} [AddCommMonoid R] (f : ℕ → R) (J : ℕ) (hJ : 1 ≤ J) :
    (∑ q ∈ Finset.Icc 1 J, f q) =
      f 1 + ∑ q ∈ Finset.Icc 2 J, f q := by
  have hset : Finset.Icc 1 J = {1} ∪ Finset.Icc 2 J := by
    ext q
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    omega
  have hdis : Disjoint ({1} : Finset ℕ) (Finset.Icc 2 J) := by
    simp
  rw [hset, Finset.sum_union hdis]
  simp

private theorem qGeTwo_filter_eq
    (d J : ℕ) (hd : 0 < d) :
    (Finset.Icc 2 J).filter (fun q ↦ d * q ≤ J) =
      Finset.Icc 2 (J / d) := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hq2, _⟩, hdqJ⟩
    exact ⟨hq2, (Nat.le_div_iff_mul_le hd).2
      (by simpa [Nat.mul_comm] using hdqJ)⟩
  · rintro ⟨hq2, hqdiv⟩
    have hdqJ : d * q ≤ J := by
      simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).1 hqdiv
    have hqJ : q ≤ J :=
      hqdiv.trans (Nat.div_le_self J d)
    exact ⟨⟨hq2, hqJ⟩, hdqJ⟩

/-- Exact finite collapse of one unweighted `q ≥ 2` row. -/
theorem ehmR1QGeTwoRow_eq_partialSeries_sub_first
    (R1 : ℝ → ℝ) (d m J : ℕ) (hd : 0 < d) :
    (∑ q ∈ Finset.Icc 2 J,
      if d * q ≤ J then
        R1 (((d * q : ℕ) : ℝ) / (m : ℝ))
      else 0) =
      if d ≤ J then
        ehmR1PartialSeries R1 (J / d) ((d : ℝ) / (m : ℝ)) -
          R1 ((d : ℝ) / (m : ℝ))
      else 0 := by
  classical
  rw [← Finset.sum_filter, qGeTwo_filter_eq d J hd]
  by_cases hdJ : d ≤ J
  · simp only [hdJ, if_true]
    have hdiv : 1 ≤ J / d := by
      exact (Nat.le_div_iff_mul_le hd).2 (by simpa using hdJ)
    unfold ehmR1PartialSeries
    rw [sum_Icc_one_eq_value_add_sum_Icc_two
      (fun q ↦ R1 ((q : ℝ) * ((d : ℝ) / (m : ℝ))))
      (J / d) hdiv]
    have hsum :
        (∑ q ∈ Finset.Icc 2 (J / d),
          R1 (((d * q : ℕ) : ℝ) / (m : ℝ))) =
        ∑ q ∈ Finset.Icc 2 (J / d),
          R1 ((q : ℝ) * ((d : ℝ) / (m : ℝ))) := by
      apply Finset.sum_congr rfl
      intro q hqMem
      congr 1
      push_cast
      ring
    rw [hsum]
    simp only [Nat.cast_one, one_mul]
    ring
  · simp only [hdJ, if_false]
    have hdiv : J / d = 0 := Nat.div_eq_of_lt (Nat.lt_of_not_ge hdJ)
    simp [hdiv]

/-- The coefficient outside the `q` row in the genuine H15 Type-I sector. -/
noncomputable def ehmTypeIOuterPairCoefficient
    (X m d : ℕ) : ℝ :=
  ((((ArithmeticFunction.moebius m : ℤ) : ℝ) *
      ((ArithmeticFunction.moebius d : ℤ) : ℝ)) / (m : ℝ)) *
    ehmDyadicNearPairAmplitude X m d

/-- The finite collapsed form of the complete `q ≥ 2` Type-I sector. -/
noncomputable def ehmDyadicNearTypeIQGeTwoCollapsed
    (R1 : ℝ → ℝ) (X D J U : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 U, ∑ d ∈ Finset.Icc (X + 1) D,
    if d ≤ J then
      ehmTypeIOuterPairCoefficient X m d *
        (ehmR1PartialSeries R1 (J / d) ((d : ℝ) / (m : ℝ)) -
          R1 ((d : ℝ) / (m : ℝ)))
    else 0

/-- The `q ≥ 2` sector collapses exactly at every secondary cutoff.
No absolute value or asymptotic passage is used. -/
theorem ehmDyadicNearTypeIQGeTwo_eq_collapsed
    (R1 : ℝ → ℝ) (X D J U : ℕ) :
    ehmDyadicNearTypeIQGeTwo R1 X D J U =
      ehmDyadicNearTypeIQGeTwoCollapsed R1 X D J U := by
  classical
  unfold ehmDyadicNearTypeIQGeTwo
    ehmDyadicNearTypeIQGeTwoCollapsed
  apply Finset.sum_congr rfl
  intro m hmMem
  apply Finset.sum_congr rfl
  intro d hdMem
  have hd : 0 < d := by
    have hdLower := (Finset.mem_Icc.mp hdMem).1
    omega
  calc
    (∑ q ∈ Finset.Icc 2 J,
        if d * q ≤ J then
          ehmTypeIOuterPairCoefficient X m d *
            R1 (((d * q : ℕ) : ℝ) / (m : ℝ))
        else 0) =
        ehmTypeIOuterPairCoefficient X m d *
          (∑ q ∈ Finset.Icc 2 J,
            if d * q ≤ J then
              R1 (((d * q : ℕ) : ℝ) / (m : ℝ))
            else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hqMem
          by_cases hdqJ : d * q ≤ J <;> simp [hdqJ]
    _ = if d ≤ J then
          ehmTypeIOuterPairCoefficient X m d *
            (ehmR1PartialSeries R1 (J / d) ((d : ℝ) / (m : ℝ)) -
              R1 ((d : ℝ) / (m : ℝ)))
        else 0 := by
          rw [ehmR1QGeTwoRow_eq_partialSeries_sub_first R1 d m J hd]
          by_cases hdJ : d ≤ J <;> simp [hdJ]

/-- The pointwise-in-cutoffs limit after eliminating `q`.  The result is
still a signed bilinear sum in `(d,m)`. -/
noncomputable def ehmDyadicNearTypeIQGeTwoSeriesLimit
    (S1 R1 : ℝ → ℝ) (X D U : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 U, ∑ d ∈ Finset.Icc (X + 1) D,
    ehmTypeIOuterPairCoefficient X m d *
      (S1 ((d : ℝ) / (m : ℝ)) - R1 ((d : ℝ) / (m : ℝ)))

/-- A rational series bridge carries the finite collapsed sector to the
bilinear `S₁-R₁` kernel for fixed outer cutoffs.  This theorem asserts no
uniformity as `X`, `D`, or `U` vary. -/
theorem ehmDyadicNearTypeIQGeTwo_tendsto_seriesLimit
    {S1 R1 : ℝ → ℝ} (H : EhmR1RationalSeriesBridge S1 R1)
    (X D U : ℕ) :
    Tendsto (fun J : ℕ ↦ ehmDyadicNearTypeIQGeTwo R1 X D J U)
      atTop (𝓝 (ehmDyadicNearTypeIQGeTwoSeriesLimit S1 R1 X D U)) := by
  classical
  have hcollapsed :
      Tendsto
        (fun J : ℕ ↦ ehmDyadicNearTypeIQGeTwoCollapsed R1 X D J U)
        atTop (𝓝 (ehmDyadicNearTypeIQGeTwoSeriesLimit S1 R1 X D U)) := by
    unfold ehmDyadicNearTypeIQGeTwoCollapsed
      ehmDyadicNearTypeIQGeTwoSeriesLimit
    apply tendsto_finsetSum
    intro m hmMem
    have hm : 0 < m :=
      lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hmMem).1
    apply tendsto_finsetSum
    intro d hdMem
    have hd : 0 < d := by
      have hdLower := (Finset.mem_Icc.mp hdMem).1
      omega
    have hpartial := ehmR1PartialSeries_ratio_tendsto H d m hd hm
    have hdiv := Nat.tendsto_div_const_atTop (Nat.ne_of_gt hd)
    have hlimit := ((hpartial.comp hdiv).sub_const
      (R1 ((d : ℝ) / (m : ℝ)))).const_mul
        (ehmTypeIOuterPairCoefficient X m d)
    apply Tendsto.congr' _ hlimit
    filter_upwards [eventually_ge_atTop d] with J hdJ
    simp [hdJ]
  apply Tendsto.congr' _ hcollapsed
  filter_upwards [] with J
  exact (ehmDyadicNearTypeIQGeTwo_eq_collapsed R1 X D J U).symm

end RH.Criteria.NymanBeurling.BCFLogTaperEhmQGeTwoCollapse
