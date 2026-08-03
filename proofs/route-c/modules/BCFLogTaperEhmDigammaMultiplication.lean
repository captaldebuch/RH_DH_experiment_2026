import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmAutocorrelationNormalization

/-!
# Gauss multiplication for the BBLS digamma surrogate

The finite progression calculation in Ehm's rational autocorrelation formula
needs only the logarithmic derivative of Gauss' multiplication formula.  The
project's `bblsDigammaShift` is defined by an absolutely convergent series, so
we prove the required identity directly by grouping its finite partial sums
into denominator blocks.  No Gamma-function multiplication theorem is used.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmDigammaMultiplication

open Filter
open scoped Topology BigOperators
open RH.Criteria.NymanBeurling.VasyuninGram

/-- One consecutive denominator block is the difference of two harmonic
numbers. -/
theorem sum_inv_nat_block_eq_harmonic_sub
    (p M : ℕ) :
    (∑ r ∈ Finset.Ioc 0 p, 1 / (((M * p + r : ℕ) : ℝ))) =
      (harmonic ((M + 1) * p) : ℝ) - (harmonic (M * p) : ℝ) := by
  have hIccIoc : ∀ n : ℕ, Finset.Icc 1 n = Finset.Ioc 0 n := by
    intro n
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hsplit :
      (∑ k ∈ Finset.Ioc 0 ((M + 1) * p), 1 / (k : ℝ)) =
        (∑ k ∈ Finset.Ioc 0 (M * p), 1 / (k : ℝ)) +
          ∑ k ∈ Finset.Ioc (M * p) ((M + 1) * p), 1 / (k : ℝ) := by
    rw [Finset.sum_Ioc_consecutive (fun k : ℕ => 1 / (k : ℝ))
      (Nat.zero_le (M * p)) (by simp [Nat.succ_mul])]
  have hset : Finset.Ioc (M * p) ((M + 1) * p) =
      (Finset.Ioc 0 p).map (addLeftEmbedding (M * p)) := by
    ext j
    simp only [Finset.mem_Ioc, Finset.mem_map, addLeftEmbedding_apply]
    constructor
    · intro hj
      refine ⟨j - M * p, ?_, ?_⟩
      · have hj' : j ≤ M * p + p := by
          simpa only [Nat.succ_mul] using hj.2
        constructor <;> omega
      · omega
    · rintro ⟨r, hr, rfl⟩
      simp only [Nat.succ_mul]
      omega
  have hblock :
      (∑ k ∈ Finset.Ioc (M * p) ((M + 1) * p), 1 / (k : ℝ)) =
        ∑ r ∈ Finset.Ioc 0 p, 1 / (((M * p + r : ℕ) : ℝ)) := by
    rw [hset, Finset.sum_map]
    rfl
  rw [harmonic_eq_sum_Icc, harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  simp only [one_div] at hsplit hblock
  rw [hIccIoc, hIccIoc, hsplit, hblock]
  ring

/-- Summing the first `M` complete denominator blocks gives the harmonic
number at `M*p`. -/
theorem sum_range_sum_inv_nat_block
    (p M : ℕ) :
    (∑ n ∈ Finset.range M,
      ∑ r ∈ Finset.Ioc 0 p, 1 / (((n * p + r : ℕ) : ℝ))) =
        (harmonic (M * p) : ℝ) := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ, ih,
        sum_inv_nat_block_eq_harmonic_sub p M]
      ring

/-- The finite sum of length-`M` BBLS digamma partial sums is exactly a
rescaled difference of harmonic numbers. -/
theorem sum_bblsDigammaPartial_rat_eq_harmonic_sub
    (p M : ℕ) (hp : 0 < p) :
    (∑ r ∈ Finset.Ioc 0 p,
      ∑ n ∈ Finset.range M,
        (1 / ((n : ℝ) + (r : ℝ) / p) - 1 / ((n : ℝ) + 1))) =
      (p : ℝ) * ((harmonic (M * p) : ℝ) - (harmonic M : ℝ)) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hterm : ∀ n r : ℕ, 0 < r → r ≤ p →
      1 / ((n : ℝ) + (r : ℝ) / p) =
        (p : ℝ) * (1 / (((n * p + r : ℕ) : ℝ))) := by
    intro n r hr hrp
    push_cast
    field_simp [ne_of_gt hpR]
  rw [Finset.sum_comm]
  calc
    (∑ n ∈ Finset.range M, ∑ r ∈ Finset.Ioc 0 p,
        (1 / ((n : ℝ) + (r : ℝ) / p) - 1 / ((n : ℝ) + 1))) =
        ∑ n ∈ Finset.range M,
          ((p : ℝ) * (∑ r ∈ Finset.Ioc 0 p,
            1 / (((n * p + r : ℕ) : ℝ))) -
              (p : ℝ) * (1 / ((n : ℝ) + 1))) := by
          apply Finset.sum_congr rfl
          intro n hn
          have hfirst :
              (∑ r ∈ Finset.Ioc 0 p, 1 / ((n : ℝ) + (r : ℝ) / p)) =
                (p : ℝ) * ∑ r ∈ Finset.Ioc 0 p,
                  1 / (((n * p + r : ℕ) : ℝ)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro r hr
            have hr' := Finset.mem_Ioc.mp hr
            exact hterm n r hr'.1 hr'.2
          have hsecond :
              (∑ _r ∈ Finset.Ioc 0 p, 1 / ((n : ℝ) + 1)) =
                (p : ℝ) * (1 / ((n : ℝ) + 1)) := by
            rw [Finset.sum_const]
            simp only [Nat.card_Ioc, Nat.cast_sub, hp.le, Nat.cast_zero,
              sub_zero, nsmul_eq_mul]
          rw [Finset.sum_sub_distrib, hfirst, hsecond]
    _ = (p : ℝ) *
        ((∑ n ∈ Finset.range M, ∑ r ∈ Finset.Ioc 0 p,
          1 / (((n * p + r : ℕ) : ℝ))) -
            ∑ n ∈ Finset.range M, 1 / ((n : ℝ) + 1)) := by
          rw [mul_sub, Finset.mul_sum, Finset.mul_sum,
            Finset.sum_sub_distrib]
    _ = (p : ℝ) * ((harmonic (M * p) : ℝ) - (harmonic M : ℝ)) := by
          rw [sum_range_sum_inv_nat_block p M]
          have hharmonic : (harmonic M : ℝ) =
              ∑ k ∈ Finset.Icc 1 M, (1 / (k : ℝ)) := by
            rw [harmonic_eq_sum_Icc]
            simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
              one_div]
          have hshift :
              (∑ n ∈ Finset.range M, (1 / ((n : ℝ) + 1))) =
                ∑ k ∈ Finset.Icc 1 M, (1 / (k : ℝ)) := by
            rw [← Finset.Ico_succ_right_eq_Icc,
              Finset.sum_Ico_eq_sum_range]
            apply Finset.sum_congr rfl
            intro n hn
            push_cast
            ring
          rw [hshift, ← hharmonic]

/-- Multiplication by a fixed positive natural is cofinal on `ℕ`. -/
theorem tendsto_nat_mul_const_atTop (p : ℕ) (hp : 0 < p) :
    Tendsto (fun M : ℕ => M * p) atTop atTop := by
  apply tendsto_atTop_mono (fun M => Nat.le_mul_of_pos_right M hp)
  exact tendsto_id

/-- The harmonic difference occurring in the block decomposition tends to
`log p`. -/
theorem tendsto_harmonic_mul_sub_harmonic (p : ℕ) (hp : 0 < p) :
    Tendsto (fun M : ℕ =>
      (harmonic (M * p) : ℝ) - (harmonic M : ℝ)) atTop
      (𝓝 (Real.log p)) := by
  have hmul := Real.tendsto_harmonic_sub_log.comp
    (tendsto_nat_mul_const_atTop p hp)
  have hbase := Real.tendsto_harmonic_sub_log
  have hdiff := hmul.sub hbase
  have hlog : ∀ᶠ M : ℕ in atTop,
      Real.log ((M * p : ℕ) : ℝ) - Real.log (M : ℝ) = Real.log (p : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with M hM
    push_cast
    rw [Real.log_mul (by positivity) (by positivity)]
    ring
  have hdiff0 : Tendsto (fun M : ℕ =>
      ((harmonic (M * p) : ℝ) - Real.log ((M * p : ℕ) : ℝ)) -
        ((harmonic M : ℝ) - Real.log (M : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Nat.mul_comm, sub_self] using hdiff
  have hlogT : Tendsto (fun M : ℕ =>
      Real.log ((M * p : ℕ) : ℝ) - Real.log (M : ℝ)) atTop
      (𝓝 (Real.log (p : ℝ))) :=
    tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hlog)
  have hadd := hdiff0.add hlogT
  convert hadd using 1
  · funext M
    ring
  · simp

/-- **Gauss multiplication identity for the BBLS surrogate.** -/
theorem sum_bblsDigammaShift_rat (p : ℕ) (hp : 0 < p) :
    (∑ r ∈ Finset.Ioc 0 p,
      bblsDigammaShift ((r : ℝ) / p)) =
        (p : ℝ) * Real.log p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hpartial : Tendsto (fun M : ℕ =>
      ∑ r ∈ Finset.Ioc 0 p,
        ∑ n ∈ Finset.range M,
          (1 / ((n : ℝ) + (r : ℝ) / p) - 1 / ((n : ℝ) + 1))) atTop
      (𝓝 (∑ r ∈ Finset.Ioc 0 p,
        bblsDigammaShift ((r : ℝ) / p))) := by
    apply tendsto_finsetSum
    intro r hr
    have hr0 : 0 < r := (Finset.mem_Ioc.mp hr).1
    have hrR : (0 : ℝ) < (r : ℝ) / p := by positivity
    exact (summable_bblsDigammaShift hrR).hasSum.tendsto_sum_nat
  have hclosed :=
    (tendsto_harmonic_mul_sub_harmonic p hp).const_mul (p : ℝ)
  have hclosed' : Tendsto (fun M : ℕ =>
      ∑ r ∈ Finset.Ioc 0 p,
        ∑ n ∈ Finset.range M,
          (1 / ((n : ℝ) + (r : ℝ) / p) - 1 / ((n : ℝ) + 1))) atTop
      (𝓝 ((p : ℝ) * Real.log p)) := by
    exact hclosed.congr' (Eventually.of_forall fun M =>
      (sum_bblsDigammaPartial_rat_eq_harmonic_sub p M hp).symm)
  exact tendsto_nhds_unique hpartial hclosed'

end RH.Criteria.NymanBeurling.BCFLogTaperEhmDigammaMultiplication
