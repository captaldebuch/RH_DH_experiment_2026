import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCLipschitzReduction
import RiemannHypothesis.Criteria.NymanBeurling.MobiusSummatoryClassical

/-!
# Route C: uniform removal of separated transform tails

Bettin--Conrey period-function coefficients have root-exponential decay in
their transform index.  This does not give cancellation in the growing H15
arithmetic variables.  It does, however, make the high transform-index tail
harmless whenever the arithmetic dependence separates as a finite growth
factor times one summable coefficient majorant.

This module proves that statement without imposing a rate on the arithmetic
growth.  A cofinal cutoff can be selected so that the complete later finite
tail is at most `1/(N+1)`.  Consequently a valid Route-C expansion may reduce
to its finitely many low modes, but those low modes and the retained H15
correction must still be estimated as one signed expression.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCTransformTail

open Filter Set Topology
open scoped BigOperators
open RH.Criteria.NymanBeurling.MobiusSummatory

/-- The root-exponential profile occurring in the Bettin--Conrey transform
coefficient estimate, with the constant left explicit. -/
noncomputable def routeCRootExponentialMajorant (c : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-c * Real.sqrt (n : ℝ))

theorem routeCRootExponentialMajorant_nonneg (c : ℝ) (n : ℕ) :
    0 ≤ routeCRootExponentialMajorant c n := by
  exact Real.exp_nonneg _

/-- Root-exponential decay is summable.  The proof uses the elementary fact
that `exp (-c sqrt n)` is eventually bounded by a constant times `n⁻²`. -/
theorem summable_routeCRootExponentialMajorant
    (c : ℝ) (hc : 0 < c) :
    Summable (routeCRootExponentialMajorant c) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_pos_bound_rpow_mul_exp_neg_mul_sqrt (2 : ℝ) c hc
  have hmajor : Summable (fun n : ℕ =>
      C * (1 / (n : ℝ) ^ (2 : ℕ))) :=
    (Real.summable_one_div_nat_pow.mpr (by norm_num)).mul_left C
  apply Summable.of_norm_bounded_eventually hmajor
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hraw := hbound (n : ℝ) (by exact_mod_cast hn)
  rw [Real.rpow_two] at hraw
  rw [Real.norm_eq_abs, abs_of_nonneg
    (routeCRootExponentialMajorant_nonneg c n)]
  unfold routeCRootExponentialMajorant
  have hdiv : Real.exp (-c * Real.sqrt (n : ℝ)) ≤ C / (n : ℝ) ^ 2 := by
    exact (le_div_iff₀ (sq_pos_of_pos hnpos)).2 (by simpa [mul_comm] using hraw)
  calc
    Real.exp (-c * Real.sqrt (n : ℝ)) ≤ C / (n : ℝ) ^ 2 := hdiv
    _ = C * (1 / (n : ℝ) ^ (2 : ℕ)) := by ring

/-- A summable scalar sequence has a finite tail uniformly small in every
later finite endpoint. -/
theorem exists_routeCUniformFiniteTail_lt
    (f : ℕ → ℝ) (hf : Summable f) (ε : ℝ) (hε : 0 < ε) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ J : ℕ, K ≤ J →
      (∑ n ∈ Finset.Icc (K + 1) J, f n) < ε := by
  rw [summable_iff_vanishing] at hf
  rcases hf (Set.Iio ε) (Iio_mem_nhds hε) with ⟨s, hs⟩
  refine ⟨s.sup id, ?_⟩
  intro K hK J _hKJ
  have hdis : Disjoint (Finset.Icc (K + 1) J) s := by
    apply Finset.disjoint_left.mpr
    intro n hnI hns
    have hnle : n ≤ s.sup id := Finset.le_sup (f := id) hns
    have hnlo := (Finset.mem_Icc.mp hnI).1
    omega
  exact hs (Finset.Icc (K + 1) J) hdis

/-- A single cofinal transform cutoff defeats an arbitrary nonnegative
cutoff-dependent growth factor.  This is the precise gain supplied by a
separated summable coefficient majorant. -/
theorem exists_cofinal_routeCTransformTailCutoff
    (f growth : ℕ → ℝ)
    (hf : Summable f) (hgrowth : ∀ N, 0 ≤ growth N) :
    ∃ K : ℕ → ℕ,
      (∀ N, N ≤ K N) ∧
      ∀ N J, K N ≤ J →
        growth N * (∑ n ∈ Finset.Icc (K N + 1) J, f n) ≤
          1 / ((N : ℝ) + 1) := by
  have hchoice : ∀ N : ℕ, ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K →
      ∀ J : ℕ, K ≤ J →
        (∑ n ∈ Finset.Icc (K + 1) J, f n) <
          1 / (((N : ℝ) + 1) * (growth N + 1)) := by
    intro N
    exact exists_routeCUniformFiniteTail_lt f hf _ (by
      have hg := hgrowth N
      positivity)
  let K : ℕ → ℕ := fun N => max N (Classical.choose (hchoice N))
  refine ⟨K, fun N => le_max_left _ _, ?_⟩
  intro N J hKJ
  have htail := Classical.choose_spec (hchoice N) (K N)
    (le_max_right N (Classical.choose (hchoice N))) J hKJ
  have hg0 : 0 ≤ growth N := hgrowth N
  have hNpos : 0 < (N : ℝ) + 1 := by positivity
  have hgpos : 0 < growth N + 1 := by linarith
  calc
    growth N * (∑ n ∈ Finset.Icc (K N + 1) J, f n) ≤
        growth N * (1 / (((N : ℝ) + 1) * (growth N + 1))) :=
      mul_le_mul_of_nonneg_left htail.le hg0
    _ = (growth N / (growth N + 1)) * (1 / ((N : ℝ) + 1)) := by
      field_simp
    _ ≤ 1 * (1 / ((N : ℝ) + 1)) := by
      gcongr
      exact (div_le_one hgpos).2 (by linarith)
    _ = 1 / ((N : ℝ) + 1) := one_mul _

/-- In particular, every positive root-exponential transform profile admits
such a cofinal cutoff against arbitrary nonnegative arithmetic growth. -/
theorem exists_cofinal_routeCRootExponentialTailCutoff
    (c : ℝ) (hc : 0 < c) (growth : ℕ → ℝ)
    (hgrowth : ∀ N, 0 ≤ growth N) :
    ∃ K : ℕ → ℕ,
      (∀ N, N ≤ K N) ∧
      ∀ N J, K N ≤ J →
        growth N *
            (∑ n ∈ Finset.Icc (K N + 1) J,
              routeCRootExponentialMajorant c n) ≤
          1 / ((N : ℝ) + 1) :=
  exists_cofinal_routeCTransformTailCutoff
    (routeCRootExponentialMajorant c) growth
    (summable_routeCRootExponentialMajorant c hc) hgrowth

/-- The selected high transform-index sector actually tends to zero for
every later endpoint.  Thus, under a separated root-exponential majorant,
the high modes are not the Route-C obstruction. -/
theorem exists_cofinal_routeCRootExponentialTail_tendsto_zero
    (c : ℝ) (hc : 0 < c) (growth : ℕ → ℝ)
    (hgrowth : ∀ N, 0 ≤ growth N) :
    ∃ K : ℕ → ℕ,
      (∀ N, N ≤ K N) ∧
      ∀ J : ℕ → ℕ, (∀ N, K N ≤ J N) →
        Tendsto (fun N : ℕ =>
          growth N *
            (∑ n ∈ Finset.Icc (K N + 1) (J N),
              routeCRootExponentialMajorant c n))
          atTop (nhds 0) := by
  rcases exists_cofinal_routeCRootExponentialTailCutoff
    c hc growth hgrowth with ⟨K, hKcofinal, hKbound⟩
  refine ⟨K, hKcofinal, ?_⟩
  intro J hJ
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact Eventually.of_forall fun N => by
    have hsum_nonneg : 0 ≤
        ∑ n ∈ Finset.Icc (K N + 1) (J N),
          routeCRootExponentialMajorant c n := by
      exact Finset.sum_nonneg fun n _hn =>
        routeCRootExponentialMajorant_nonneg c n
    change |growth N *
      (∑ n ∈ Finset.Icc (K N + 1) (J N),
        routeCRootExponentialMajorant c n)| ≤ 1 / ((N : ℝ) + 1)
    rw [abs_of_nonneg (mul_nonneg (hgrowth N) hsum_nonneg)]
    exact hKbound N (J N) (hJ N)

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCTransformTail
