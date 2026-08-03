import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmAdditiveRatioReduction
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmR1Decay
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Near/far decomposition of the collapsed Ehm additive-ratio sector

This file carries out the first stage of the direct additive-ratio route.
After restoring the BCF cutoff `N`, it splits the exact signed kernel at

```text
m < d < 2m        (near core),
2m <= d           (far sector).
```

The support conditions `m <= N < d` already imply `m < d`.  The split is
therefore exhaustive and disjoint.  The near core retains every arithmetic
sign.  For the far sector, the rational `R₁`-series bridge and the proved
quadratic decay of Ehm's elementary `R₁` give the pointwise bound

```text
|S₁(d/m) - R₁(d/m)| <= C * m² / d².
```

No cancellation estimate for the near core is asserted here.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmAdditiveRatioNearFar

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmAdditiveRatioReduction
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmKernel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmR1Decay
open RH.Criteria.NymanBeurling.BCFLogTaperEhmSeriesBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTVariation
open RH.Criteria.NymanBeurling.BCFLogTaperEhmQGeTwoCollapse

/-! ## Exact ratio split -/

/-- The signed near part of one restored-cutoff slice. -/
noncomputable def ehmQGeTwoNearRatioSlice
    (S1 R1 : ℝ → ℝ) (X D U N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 U, ∑ d ∈ Finset.Icc (X + 1) D,
    if m ≤ N then
      if N < d then
        if d < 2 * m then
          ehmQGeTwoMWeight N m * ehmQGeTwoDWeight N d *
            ehmQGeTwoLimitKernel S1 R1 d m
        else 0
      else 0
    else 0

/-- The complementary far part of one restored-cutoff slice. -/
noncomputable def ehmQGeTwoFarRatioSlice
    (S1 R1 : ℝ → ℝ) (X D U N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 U, ∑ d ∈ Finset.Icc (X + 1) D,
    if m ≤ N then
      if N < d then
        if 2 * m ≤ d then
          ehmQGeTwoMWeight N m * ehmQGeTwoDWeight N d *
            ehmQGeTwoLimitKernel S1 R1 d m
        else 0
      else 0
    else 0

/-- Exact disjoint split of one separated cutoff slice at `d = 2m`. -/
theorem ehmQGeTwoCutoffSeparatedSlice_eq_near_add_far
    (S1 R1 : ℝ → ℝ) (X D U N : ℕ) :
    ehmQGeTwoCutoffSeparatedSlice S1 R1 X D U N =
      ehmQGeTwoNearRatioSlice S1 R1 X D U N +
        ehmQGeTwoFarRatioSlice S1 R1 X D U N := by
  classical
  unfold ehmQGeTwoCutoffSeparatedSlice ehmQGeTwoNearRatioSlice
    ehmQGeTwoFarRatioSlice
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hmMem
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hdMem
  by_cases hmN : m ≤ N
  · simp only [hmN, if_true]
    by_cases hNd : N < d
    · simp only [hNd, if_true]
      by_cases hnear : d < 2 * m
      · simp [hnear, Nat.not_le_of_lt hnear]
      · have hfar : 2 * m ≤ d := Nat.le_of_not_gt hnear
        simp [hnear, hfar]
    · simp [hNd]
  · simp [hmN]

/-- The complete collapsed `q >= 2` limit is the exact sum of its signed
near core and far sector, still before taking any absolute value. -/
theorem ehmDyadicNearTypeIQGeTwoSeriesLimit_eq_near_add_far
    (S1 R1 : ℝ → ℝ) (X D U : ℕ) :
    ehmDyadicNearTypeIQGeTwoSeriesLimit S1 R1 X D U =
      (∑ N ∈ ehmDyadicNBlock X,
        ehmQGeTwoNearRatioSlice S1 R1 X D U N) +
      (∑ N ∈ ehmDyadicNBlock X,
        ehmQGeTwoFarRatioSlice S1 R1 X D U N) := by
  rw [ehmDyadicNearTypeIQGeTwoSeriesLimit_eq_sum_cutoffSeparated]
  simp_rw [ehmQGeTwoCutoffSeparatedSlice_eq_near_add_far]
  exact Finset.sum_add_distrib

/-! ## A proved pointwise majorant for the collapsed tail kernel -/

/-- The collapsed kernel is exactly the `q >= 2` tail of the rational
`R₁` series. -/
theorem ehmQGeTwoLimitKernel_eq_tsum_tail
    {S1 R1 : ℝ → ℝ} (HS : EhmR1RationalSeriesBridge S1 R1)
    (d m : ℕ) (hd : 0 < d) (hm : 0 < m) :
    ehmQGeTwoLimitKernel S1 R1 d m =
      ∑' q : ℕ,
        R1 (((q + 2 : ℕ) : ℝ) * ((d : ℝ) / (m : ℝ))) := by
  let f : ℕ → ℝ := fun q ↦
    R1 (((q + 1 : ℕ) : ℝ) * ((d : ℝ) / (m : ℝ)))
  have hsum := HS.hasSum_ratio d m hd hm
  have hsplit := hsum.summable.sum_add_tsum_nat_add 1
  have hvalue : (∑' q : ℕ, f q) = S1 ((d : ℝ) / (m : ℝ)) := hsum.tsum_eq
  unfold ehmQGeTwoLimitKernel
  have hf0 : f 0 = R1 ((d : ℝ) / (m : ℝ)) := by simp [f]
  rw [← hf0]
  change S1 ((d : ℝ) / (m : ℝ)) - f 0 =
    ∑' q : ℕ, R1 (((q + 2 : ℕ) : ℝ) * ((d : ℝ) / (m : ℝ)))
  rw [← hvalue]
  have hsplit' :
      f 0 + (∑' q : ℕ, f (q + 1)) = ∑' q : ℕ, f q := by
    simpa only [f, Finset.sum_range_one, Nat.cast_zero, Nat.cast_one,
      zero_add, one_mul, Nat.cast_add] using hsplit
  rw [← hsplit']
  simp only [add_sub_cancel_left]
  apply tsum_congr
  intro q
  simp only [f]

/-- The shifted reciprocal-square series occurring in the `q >= 2` tail
has total mass at most one. -/
theorem tsum_one_div_nat_add_two_sq_le_one :
    (∑' q : ℕ, 1 / (((q + 2 : ℕ) : ℝ) ^ 2)) ≤ 1 := by
  let p : ℕ → ℝ := fun n ↦ 1 / (n : ℝ) ^ 2
  have hp : Summable p := by
    simpa [p] using hasSum_zeta_two.summable
  have hsplit := hp.sum_add_tsum_nat_add 2
  have hvalue : (∑' n : ℕ, p n) = Real.pi ^ 2 / 6 := by
    simpa [p] using hasSum_zeta_two.tsum_eq
  have htail :
      (∑' q : ℕ, (((q : ℝ) + 2) ^ 2)⁻¹) =
        Real.pi ^ 2 / 6 - 1 := by
    rw [hvalue] at hsplit
    norm_num [p] at hsplit
    linarith
  have hpi : Real.pi ^ 2 / 6 - 1 ≤ 1 := by
    have hpi0 : 0 ≤ Real.pi := Real.pi_pos.le
    have hpilt : Real.pi < 3.15 := Real.pi_lt_d2
    nlinarith
  calc
    (∑' q : ℕ, 1 / (((q + 2 : ℕ) : ℝ) ^ 2)) =
        ∑' q : ℕ, (((q : ℝ) + 2) ^ 2)⁻¹ := by
      apply tsum_congr
      intro q
      norm_num [Nat.cast_add, one_div]
    _ ≤ 1 := by rw [htail]; exact hpi

/-- Quadratic decay of `R₁` gives a sharp-enough quadratic majorant for the
entire collapsed `q >= 2` kernel. -/
theorem abs_ehmQGeTwoLimitKernel_le
    {S1 R1 : ℝ → ℝ}
    (HS : EhmR1RationalSeriesBridge S1 R1)
    (HD : EhmR1QuadraticDecay R1)
    (d m : ℕ) (hd : 0 < d) (hm : 0 < m) :
    |ehmQGeTwoLimitKernel S1 R1 d m| ≤
      HD.C / (((d : ℝ) / (m : ℝ)) ^ 2) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  let x : ℝ := (d : ℝ) / (m : ℝ)
  have hx : 0 < x := div_pos hdR hmR
  let p : ℕ → ℝ := fun q ↦ 1 / (((q + 2 : ℕ) : ℝ) ^ 2)
  have hp0 : Summable p := by
    let z : ℕ → ℝ := fun n ↦ 1 / (n : ℝ) ^ (2 : ℕ)
    have hz : Summable z :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have hzShift : Summable (fun q : ℕ ↦ z (q + 2)) :=
      (summable_nat_add_iff 2).2 hz
    simpa [p, z] using hzShift
  have hmajor : Summable (fun q : ℕ ↦ (HD.C / x ^ 2) * p q) :=
    hp0.mul_left (HD.C / x ^ 2)
  have hpoint : ∀ q : ℕ,
      |R1 (((q + 2 : ℕ) : ℝ) * x)| ≤ (HD.C / x ^ 2) * p q := by
    intro q
    calc
      |R1 (((q + 2 : ℕ) : ℝ) * x)| ≤
          HD.C / ((((q + 2 : ℕ) : ℝ) * x) ^ 2) :=
        HD.bound _ (mul_pos (by positivity) hx)
      _ = (HD.C / x ^ 2) * p q := by
        unfold p
        field_simp [ne_of_gt hx]
  rw [ehmQGeTwoLimitKernel_eq_tsum_tail HS d m hd hm]
  change |∑' q : ℕ, R1 (((q + 2 : ℕ) : ℝ) * x)| ≤ HD.C / x ^ 2
  calc
    |∑' q : ℕ, R1 (((q + 2 : ℕ) : ℝ) * x)| ≤
        ∑' q : ℕ, (HD.C / x ^ 2) * p q := by
      have hb := tsum_of_norm_bounded
        (f := fun q : ℕ ↦ R1 (((q + 2 : ℕ) : ℝ) * x))
        hmajor.hasSum
        (fun q ↦ by simpa only [Real.norm_eq_abs] using hpoint q)
      simpa only [Real.norm_eq_abs] using hb
    _ = (HD.C / x ^ 2) * (∑' q : ℕ, p q) := tsum_mul_left
    _ ≤ (HD.C / x ^ 2) * 1 := by
      have hC : 0 ≤ HD.C / x ^ 2 := div_nonneg HD.C_nonneg (sq_nonneg x)
      have hpBound : (∑' q : ℕ, p q) ≤ 1 := by
        change (∑' q : ℕ, 1 / (((q + 2 : ℕ) : ℝ) ^ 2)) ≤ 1
        exact tsum_one_div_nat_add_two_sq_le_one
      exact mul_le_mul_of_nonneg_left hpBound hC
    _ = HD.C / x ^ 2 := by ring

/-- Concrete Ehm specialization: the collapsed far-kernel has constant
eight. -/
theorem abs_ehmAutocorrelationQGeTwoLimitKernel_le
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (d m : ℕ) (hd : 0 < d) (hm : 0 < m) :
    |ehmQGeTwoLimitKernel ehmS1Autocorrelation ehmR1 d m| ≤
      8 / (((d : ℝ) / (m : ℝ)) ^ 2) := by
  simpa using abs_ehmQGeTwoLimitKernel_le HS
    ehmConcreteR1QuadraticDecay d m hd hm

/-! ## The finite far-sector majorant -/

/-- The direct nonnegative majorant obtained by applying quadratic kernel
decay term by term in the ratio-far sector.  This definition deliberately
retains the exact BCF weights: it is the correct object on which to perform
the quantitative stop test, rather than an unweighted count of pairs. -/
noncomputable def ehmQGeTwoFarRatioMajorant
    (C : ℝ) (X D U N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 U, ∑ d ∈ Finset.Icc (X + 1) D,
    if m ≤ N then
      if N < d then
        if 2 * m ≤ d then
          |ehmQGeTwoMWeight N m| * |ehmQGeTwoDWeight N d| *
            (C / (((d : ℝ) / (m : ℝ)) ^ 2))
        else 0
      else 0
    else 0

/-- Quadratic decay bounds the finite far sector by the explicit weighted
majorant.  The theorem is intentionally pointwise in the restored cutoff
`N`; summing this majorant absolutely is not claimed to produce decay. -/
theorem abs_ehmQGeTwoFarRatioSlice_le_majorant
    {S1 R1 : ℝ → ℝ}
    (HS : EhmR1RationalSeriesBridge S1 R1)
    (HD : EhmR1QuadraticDecay R1)
    (X D U N : ℕ) :
    |ehmQGeTwoFarRatioSlice S1 R1 X D U N| ≤
      ehmQGeTwoFarRatioMajorant HD.C X D U N := by
  classical
  unfold ehmQGeTwoFarRatioSlice ehmQGeTwoFarRatioMajorant
  calc
    |∑ m ∈ Finset.Icc 1 U, ∑ d ∈ Finset.Icc (X + 1) D,
        if m ≤ N then
          if N < d then
            if 2 * m ≤ d then
              ehmQGeTwoMWeight N m * ehmQGeTwoDWeight N d *
                ehmQGeTwoLimitKernel S1 R1 d m
            else 0
          else 0
        else 0| ≤
      ∑ m ∈ Finset.Icc 1 U,
        |∑ d ∈ Finset.Icc (X + 1) D,
          if m ≤ N then
            if N < d then
              if 2 * m ≤ d then
                ehmQGeTwoMWeight N m * ehmQGeTwoDWeight N d *
                  ehmQGeTwoLimitKernel S1 R1 d m
              else 0
            else 0
          else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 U, ∑ d ∈ Finset.Icc (X + 1) D,
        |if m ≤ N then
          if N < d then
            if 2 * m ≤ d then
              ehmQGeTwoMWeight N m * ehmQGeTwoDWeight N d *
                ehmQGeTwoLimitKernel S1 R1 d m
            else 0
          else 0
        else 0| := by
      apply Finset.sum_le_sum
      intro m _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 U, ∑ d ∈ Finset.Icc (X + 1) D,
        if m ≤ N then
          if N < d then
            if 2 * m ≤ d then
              |ehmQGeTwoMWeight N m| * |ehmQGeTwoDWeight N d| *
                (HD.C / (((d : ℝ) / (m : ℝ)) ^ 2))
            else 0
          else 0
        else 0 := by
      apply Finset.sum_le_sum
      intro m hmMem
      apply Finset.sum_le_sum
      intro d hdMem
      by_cases hmN : m ≤ N
      · simp only [hmN, if_true]
        by_cases hNd : N < d
        · simp only [hNd, if_true]
          by_cases hfar : 2 * m ≤ d
          · simp only [hfar, if_true, abs_mul]
            have hm : 0 < m := (Finset.mem_Icc.mp hmMem).1
            have hd : 0 < d := by
              have : X + 1 ≤ d := (Finset.mem_Icc.mp hdMem).1
              omega
            gcongr
            exact abs_ehmQGeTwoLimitKernel_le HS HD d m hd hm
          · simp [hfar]
        · simp [hNd]
      · simp [hmN]

/-- Concrete Ehm specialization of the finite far-sector majorant. -/
theorem abs_ehmAutocorrelationQGeTwoFarRatioSlice_le_majorant
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (X D U N : ℕ) :
    |ehmQGeTwoFarRatioSlice ehmS1Autocorrelation ehmR1 X D U N| ≤
      ehmQGeTwoFarRatioMajorant 8 X D U N := by
  simpa using abs_ehmQGeTwoFarRatioSlice_le_majorant HS
    ehmConcreteR1QuadraticDecay X D U N

end RH.Criteria.NymanBeurling.BCFLogTaperEhmAdditiveRatioNearFar
