import Mathlib

/-!
# Logarithmic Riesz means of the Möbius function

For `N : ℕ` and `s : ℂ` we set

`R_N(s) = ∑_{n ≤ N} μ(n) log(N/n) n^{-s}`,

the logarithmic Riesz mean of the Dirichlet series of the Möbius function.  The main result,
`RieszMeanZeta.rieszMean_div_log_tendsto`, is that in the half-plane of absolute convergence
`Re s > 1` the normalised Riesz means converge to `1/ζ(s)`:

`R_N(s) / log N → 1/ζ(s)`  as `N → ∞`.

The proof is the elementary Abelian argument: writing `a_n = μ(n) n^{-s}` we have

`R_N(s)/log N = ∑_{n ≤ N} a_n - (1/log N) ∑_{n ≤ N} a_n log n`,

the first sum converges to `∑ a_n = 1/ζ(s)`, and the second sum converges as well (the series
`∑ a_n log n` is again absolutely convergent for `Re s > 1`), so after division by
`log N → ∞` it contributes nothing.
-/

open Filter Topology Complex

open scoped ArithmeticFunction.Moebius

noncomputable section

namespace RieszMeanZeta

/-- The coefficients `a_n = μ(n) n^{-s}` of the Dirichlet series of the Möbius function. -/
def moebiusCoeff (s : ℂ) (n : ℕ) : ℂ := (μ n : ℂ) * (n : ℂ) ^ (-s)

/-- The coefficients `a_n log n`. -/
def moebiusLogCoeff (s : ℂ) (n : ℕ) : ℂ := moebiusCoeff s n * (Real.log n : ℂ)

/-- The logarithmic Riesz mean `R_N(s) = ∑_{n ≤ N} μ(n) log(N/n) n^{-s}`. -/
def rieszMean (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, (μ n : ℂ) * (Real.log ((N : ℝ) / (n : ℝ)) : ℂ) * (n : ℂ) ^ (-s)

lemma moebiusCoeff_zero (s : ℂ) : moebiusCoeff s 0 = 0 := by simp [moebiusCoeff]

lemma moebiusLogCoeff_zero (s : ℂ) : moebiusLogCoeff s 0 = 0 := by
  simp [moebiusLogCoeff, moebiusCoeff]

lemma moebiusCoeff_eq_term (s : ℂ) : moebiusCoeff s = LSeries.term (fun k => (μ k : ℂ)) s := by
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [moebiusCoeff, LSeries.term]
  · rw [LSeries.term_of_ne_zero hn]
    simp [moebiusCoeff, Complex.cpow_neg, div_eq_mul_inv]

lemma moebiusLogCoeff_eq_term (s : ℂ) :
    moebiusLogCoeff s = LSeries.term (LSeries.logMul (fun k => (μ k : ℂ))) s := by
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [moebiusLogCoeff, moebiusCoeff, LSeries.term]
  · rw [LSeries.term_of_ne_zero hn, moebiusLogCoeff, moebiusCoeff_eq_term,
      LSeries.term_of_ne_zero hn, LSeries.logMul, Complex.ofReal_log (Nat.cast_nonneg n),
      Complex.ofReal_natCast]
    ring

lemma summable_moebiusCoeff {s : ℂ} (hs : 1 < s.re) : Summable (moebiusCoeff s) := by
  rw [moebiusCoeff_eq_term]
  exact ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs

lemma summable_moebiusLogCoeff {s : ℂ} (hs : 1 < s.re) : Summable (moebiusLogCoeff s) := by
  rw [moebiusLogCoeff_eq_term]
  refine LSeriesSummable_logMul_of_lt_re ?_
  rw [ArithmeticFunction.abscissaOfAbsConv_moebius]
  exact_mod_cast hs

lemma tsum_moebiusCoeff {s : ℂ} (hs : 1 < s.re) :
    ∑' n, moebiusCoeff s n = 1 / riemannZeta s := by
  rw [moebiusCoeff_eq_term]
  have h := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at h
  show LSeries (fun n => (μ n : ℂ)) s = 1 / riemannZeta s
  field_simp [riemannZeta_ne_zero_of_one_lt_re hs]
  linear_combination h

/-- A sum over `Icc 1 N` of a function vanishing at `0` is a sum over `range (N+1)`. -/
lemma sum_Icc_eq_sum_range (f : ℕ → ℂ) (hf : f 0 = 0) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, f n = ∑ n ∈ Finset.range (N + 1), f n := by
  refine Finset.sum_subset (fun k hk => ?_) (fun k _ hk => ?_)
  · simp only [Finset.mem_Icc] at hk
    simp only [Finset.mem_range]
    omega
  · simp only [Finset.mem_Icc, not_and, not_le] at hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact hf
    · exact absurd (Finset.mem_range.1 ‹k ∈ Finset.range (N + 1)›) (by omega)

lemma tendsto_partialSum (f : ℕ → ℂ) (hf : Summable f) (hf0 : f 0 = 0) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f n) atTop (𝓝 (∑' n, f n)) := by
  have h1 := hf.hasSum.tendsto_sum_nat
  have h2 : Tendsto (fun N : ℕ => N + 1) atTop atTop := tendsto_add_atTop_nat 1
  refine (h1.comp h2).congr fun N => ?_
  exact (sum_Icc_eq_sum_range f hf0 N).symm

/-- The exact decomposition of the Riesz mean into the two partial sums. -/
lemma rieszMean_eq (N : ℕ) (hN : 1 ≤ N) (s : ℂ) :
    rieszMean N s =
      (Real.log N : ℂ) * (∑ n ∈ Finset.Icc 1 N, moebiusCoeff s n)
        - ∑ n ∈ Finset.Icc 1 N, moebiusLogCoeff s n := by
  rw [rieszMean, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  simp only [Finset.mem_Icc] at hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [Real.log_div hN0 hn0]
  simp only [moebiusCoeff, moebiusLogCoeff, Complex.ofReal_sub]
  ring

/-- **Convergence of the normalised Riesz means to `1/ζ`** in the half-plane of absolute
convergence. -/
theorem rieszMean_div_log_tendsto {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => rieszMean N s / (Real.log N : ℂ)) atTop (𝓝 (1 / riemannZeta s)) := by
  have hA : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, moebiusCoeff s n) atTop
      (𝓝 (∑' n, moebiusCoeff s n)) :=
    tendsto_partialSum _ (summable_moebiusCoeff hs) (moebiusCoeff_zero s)
  have hB : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, moebiusLogCoeff s n) atTop
      (𝓝 (∑' n, moebiusLogCoeff s n)) :=
    tendsto_partialSum _ (summable_moebiusLogCoeff hs) (moebiusLogCoeff_zero s)
  have hlog : Tendsto (fun N : ℕ => ((Real.log N : ℝ) : ℂ)⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => (Real.log N)⁻¹) atTop (𝓝 (0:ℝ)) := by
      refine Tendsto.comp tendsto_inv_atTop_zero ?_
      exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have h2 := (Complex.continuous_ofReal.tendsto (0:ℝ)).comp h1
    rw [Complex.ofReal_zero] at h2
    exact h2.congr fun N => by rw [Function.comp_apply, Complex.ofReal_inv]
  have hlim : Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, moebiusCoeff s n)
      - (∑ n ∈ Finset.Icc 1 N, moebiusLogCoeff s n) * ((Real.log N : ℝ) : ℂ)⁻¹) atTop
      (𝓝 (1 / riemannZeta s)) := by
    have := hA.sub (hB.mul hlog)
    rw [mul_zero, sub_zero, tsum_moebiusCoeff hs] at this
    exact this
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hN1 : 1 ≤ N := by omega
  have hlogN : (Real.log N : ℝ) ≠ 0 := by
    have h2 : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have : (1:ℝ) < (N:ℝ) := by linarith
    exact ne_of_gt (Real.log_pos this)
  have hlogNC : ((Real.log N : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlogN
  rw [rieszMean_eq N hN1 s]
  field_simp

end RieszMeanZeta
