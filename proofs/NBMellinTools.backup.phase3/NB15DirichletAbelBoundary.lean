/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# A real Dirichlet--Abelian boundary theorem

This is the small reusable analytic lemma needed to identify the rational
`sinZeta` value at `s = 1`.  It has no arithmetic or RH input.
-/

open Filter Finset Topology
open scoped BigOperators

namespace NBMellinTools.NB15

/-- Finite Abel summation on a natural interval. -/
theorem finiteAbelSum_Icc_mul_eq_endpoint_add_sum_partial
    (a b : ℕ → ℝ) (A B : ℕ) (hAB : A ≤ B) :
    (∑ k ∈ Icc A B, a k * b k) =
      (∑ j ∈ Icc A B, a j) * b (B + 1) +
        ∑ k ∈ Icc A B,
          (∑ j ∈ Icc A k, a j) * (b k - b (k + 1)) := by
  induction B, hAB using Nat.le_induction with
  | base => simp; ring
  | succ B hAB ih =>
      have hAB' : A ≤ B + 1 := by omega
      rw [sum_Icc_succ_top hAB', sum_Icc_succ_top hAB',
        sum_Icc_succ_top hAB']
      rw [ih]
      rw [sum_Icc_succ_top hAB']
      ring

private lemma sum_Icc_sub_succ_add_endpoint
    (b : ℕ → ℝ) (A B : ℕ) (hAB : A ≤ B) :
    b (B + 1) + ∑ k ∈ Icc A B, (b k - b (k + 1)) = b A := by
  induction B, hAB using Nat.le_induction with
  | base => simp
  | succ B hAB ih =>
      rw [sum_Icc_succ_top (by omega)]
      linarith

/-- Abel's inequality for a nonnegative decreasing weight. -/
theorem abs_sum_Icc_mul_le_of_partial_sum_le_of_antitone
    (a b : ℕ → ℝ) (A B : ℕ) (D : ℝ)
    (hAB : A ≤ B) (hD : 0 ≤ D)
    (hb_nonneg : ∀ k ∈ Icc A (B + 1), 0 ≤ b k)
    (hb_antitone : ∀ k ∈ Icc A B, b (k + 1) ≤ b k)
    (hbA : b A ≤ 1)
    (hpartial : ∀ k ∈ Icc A B,
      |∑ j ∈ Icc A k, a j| ≤ D) :
    |∑ k ∈ Icc A B, a k * b k| ≤ D := by
  have hBmem : B ∈ Icc A B := mem_Icc.mpr ⟨hAB, le_rfl⟩
  have hB1mem : B + 1 ∈ Icc A (B + 1) :=
    mem_Icc.mpr ⟨hAB.trans (by omega), le_rfl⟩
  have hAmem : A ∈ Icc A (B + 1) :=
    mem_Icc.mpr ⟨le_rfl, hAB.trans (by omega)⟩
  have hdiff_nonneg : ∀ k ∈ Icc A B, 0 ≤ b k - b (k + 1) := by
    intro k hk
    exact sub_nonneg.mpr (hb_antitone k hk)
  rw [finiteAbelSum_Icc_mul_eq_endpoint_add_sum_partial a b A B hAB]
  calc
    |(∑ j ∈ Icc A B, a j) * b (B + 1) +
        ∑ k ∈ Icc A B,
          (∑ j ∈ Icc A k, a j) * (b k - b (k + 1))| ≤
        |(∑ j ∈ Icc A B, a j) * b (B + 1)| +
          |∑ k ∈ Icc A B,
            (∑ j ∈ Icc A k, a j) * (b k - b (k + 1))| :=
      abs_add_le _ _
    _ ≤ D * b (B + 1) +
        ∑ k ∈ Icc A B, D * (b k - b (k + 1)) := by
      gcongr
      · rw [abs_mul, abs_of_nonneg (hb_nonneg _ hB1mem)]
        exact mul_le_mul_of_nonneg_right (hpartial B hBmem)
          (hb_nonneg _ hB1mem)
      · calc
          |∑ k ∈ Icc A B,
              (∑ j ∈ Icc A k, a j) * (b k - b (k + 1))| ≤
              ∑ k ∈ Icc A B,
                |(∑ j ∈ Icc A k, a j) * (b k - b (k + 1))| :=
            abs_sum_le_sum_abs _ _
          _ ≤ ∑ k ∈ Icc A B, D * (b k - b (k + 1)) := by
            apply sum_le_sum
            intro k hk
            rw [abs_mul, abs_of_nonneg (hdiff_nonneg k hk)]
            exact mul_le_mul_of_nonneg_right (hpartial k hk)
              (hdiff_nonneg k hk)
    _ = D * b A := by
      rw [← mul_sum, ← mul_add,
        sum_Icc_sub_succ_add_endpoint b A B hAB]
    _ ≤ D := by
      nlinarith [hb_nonneg A hAmem]

private lemma sum_Icc_one_sub_sum_Icc_one
    (f : ℕ → ℝ) (N R : ℕ) (hNR : N ≤ R) :
    (∑ k ∈ Icc 1 R, f k) - (∑ k ∈ Icc 1 N, f k) =
      ∑ k ∈ Icc (N + 1) R, f k := by
  induction R, hNR using Nat.le_induction with
  | base => simp
  | succ R hNR ih =>
      have h1R : 1 ≤ R + 1 := by omega
      have hNR' : N + 1 ≤ R + 1 := by omega
      rw [sum_Icc_succ_top h1R, sum_Icc_succ_top hNR']
      calc
        _ = ((∑ k ∈ Icc 1 R, f k) - (∑ k ∈ Icc 1 N, f k)) +
            f (R + 1) := by ring
        _ = _ := by rw [ih]

private lemma sum_range_succ_eq_sum_Icc_one_of_zero
    (a : ℕ → ℝ) (ha0 : a 0 = 0) (N : ℕ) :
    (∑ n ∈ range (N + 1), a n) = ∑ n ∈ Icc 1 N, a n := by
  induction N with
  | zero => simp [ha0]
  | succ N ih =>
      rw [sum_range_succ, ih]
      rw [sum_Icc_succ_top (by omega)]

private lemma abs_sum_Icc_rpow_neg_le_of_partial_limit
    (a : ℕ → ℝ) {ℓ ε : ℝ} (K B : ℕ) (d : ℝ)
    (hε : 0 ≤ ε) (hd : 0 < d) (hKB : K + 1 ≤ B)
    (htail : ∀ n : ℕ, K ≤ n →
      |(∑ j ∈ Icc 1 n, a j) - ℓ| ≤ ε) :
    |∑ n ∈ Icc (K + 1) B, a n * (n : ℝ) ^ (-d)| ≤ 2 * ε := by
  apply abs_sum_Icc_mul_le_of_partial_sum_le_of_antitone
    a (fun n : ℕ => (n : ℝ) ^ (-d)) (K + 1) B (2 * ε) hKB (by positivity)
  · intro n hn
    exact Real.rpow_nonneg (by positivity) _
  · intro n hn
    have hnrange := mem_Icc.mp hn
    exact Real.rpow_le_rpow_of_nonpos
      (by exact_mod_cast (show 0 < n by omega)) (by norm_cast; omega) (by linarith)
  · exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_cast; omega) (by linarith)
  · intro n hn
    have hnrange := mem_Icc.mp hn
    rw [← sum_Icc_one_sub_sum_Icc_one a K n (by omega)]
    calc
      |(∑ j ∈ Icc 1 n, a j) - ∑ j ∈ Icc 1 K, a j| =
          |((∑ j ∈ Icc 1 n, a j) - ℓ) -
            ((∑ j ∈ Icc 1 K, a j) - ℓ)| := by ring_nf
      _ ≤ |(∑ j ∈ Icc 1 n, a j) - ℓ| +
          |(∑ j ∈ Icc 1 K, a j) - ℓ| := abs_sub _ _
      _ ≤ 2 * ε := by
        have hnK : K ≤ n := by omega
        linarith [htail n hnK, htail K le_rfl]

private lemma abs_dirichlet_series_sub_head_le_of_partial_limit
    (a : ℕ → ℝ) (F : ℝ) {ℓ ε : ℝ} (K : ℕ) (d : ℝ)
    (ha0 : a 0 = 0) (hε : 0 ≤ ε) (hd : 0 < d)
    (htail : ∀ n : ℕ, K ≤ n →
      |(∑ j ∈ Icc 1 n, a j) - ℓ| ≤ ε)
    (hsum : HasSum (fun n : ℕ => a n * (n : ℝ) ^ (-d)) F) :
    |F - ∑ n ∈ Icc 1 K, a n * (n : ℝ) ^ (-d)| ≤ 2 * ε := by
  let f : ℕ → ℝ := fun n => a n * (n : ℝ) ^ (-d)
  have hf0 : f 0 = 0 := by simp [f, ha0]
  have hrange := hsum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hpartial :
      Tendsto (fun B : ℕ => ∑ n ∈ Icc 1 B, f n) atTop (𝓝 F) := by
    convert hrange using 1
    ext B
    exact (sum_range_succ_eq_sum_Icc_one_of_zero f hf0 B).symm
  have htail_tendsto :
      Tendsto (fun B : ℕ => ∑ n ∈ Icc (K + 1) B, f n) atTop
        (𝓝 (F - ∑ n ∈ Icc 1 K, f n)) := by
    have hsub := hpartial.sub_const (∑ n ∈ Icc 1 K, f n)
    apply hsub.congr'
    filter_upwards [eventually_ge_atTop K] with B hKB
    exact sum_Icc_one_sub_sum_Icc_one f K B hKB
  have habs_tendsto := htail_tendsto.abs
  apply le_of_tendsto habs_tendsto
  filter_upwards [eventually_ge_atTop (K + 1)] with B hKB
  simpa [f] using
    abs_sum_Icc_rpow_neg_le_of_partial_limit a K B d hε hd hKB htail

/-- Ordered convergence at the boundary and absolute convergence at each
positive displacement imply convergence back to the boundary from the
right. -/
theorem dirichletAbelian_tendsto_of_partial_sum_tendsto
    (a : ℕ → ℝ) (F : ℝ → ℝ) {ℓ : ℝ} (ha0 : a 0 = 0)
    (hpartial : Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, a n) atTop (𝓝 ℓ))
    (hsum : ∀ d : ℝ, 0 < d →
      HasSum (fun n : ℕ => a n * (n : ℝ) ^ (-d)) (F d)) :
    Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 ℓ) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hη : 0 < ε / 8 := by positivity
  rw [Metric.tendsto_atTop] at hpartial
  obtain ⟨K, hK⟩ := hpartial (ε / 8) hη
  have htail : ∀ n : ℕ, K ≤ n →
      |(∑ j ∈ Icc 1 n, a j) - ℓ| ≤ ε / 8 := by
    intro n hn
    have hdist := hK n hn
    rw [Real.dist_eq] at hdist
    exact hdist.le
  have hhead : Tendsto
      (fun d : ℝ => ∑ n ∈ Icc 1 K, a n * (n : ℝ) ^ (-d))
      (𝓝[>] (0 : ℝ)) (𝓝 (∑ n ∈ Icc 1 K, a n)) := by
    simpa using tendsto_finsetSum (Icc 1 K) (fun n hn => by
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast (mem_Icc.mp hn).1
      have hrpow : Tendsto (fun d : ℝ => (n : ℝ) ^ (-d))
          (𝓝[>] (0 : ℝ)) (𝓝 1) := by
        have hneg : Tendsto (fun d : ℝ => -d) (𝓝 0) (𝓝 0) := by
          simpa using (continuousAt_neg : ContinuousAt (fun d : ℝ => -d) 0).tendsto
        have hbase :=
          (Real.continuousAt_const_rpow (a := (n : ℝ)) (b := (0 : ℝ))
            hnpos.ne').tendsto
        have hfull : Tendsto (fun d : ℝ => (n : ℝ) ^ (-d))
            (𝓝 0) (𝓝 1) := by
          simpa using hbase.comp hneg
        exact tendsto_nhdsWithin_of_tendsto_nhds hfull
      simpa using (tendsto_const_nhds.mul hrpow :
        Tendsto (fun d : ℝ => a n * (n : ℝ) ^ (-d))
          (𝓝[>] (0 : ℝ)) (𝓝 (a n * 1))))
  have hhead_eventually :=
    (Metric.tendsto_nhds.mp hhead) (ε / 2) (by positivity)
  filter_upwards [hhead_eventually, self_mem_nhdsWithin] with d hhead_d hdmem
  have hd : 0 < d := hdmem
  have hseries_tail := abs_dirichlet_series_sub_head_le_of_partial_limit
    a (F d) K d ha0 hη.le hd htail (hsum d hd)
  rw [Real.dist_eq] at hhead_d ⊢
  calc
    |F d - ℓ| ≤
        |F d - ∑ n ∈ Icc 1 K, a n * (n : ℝ) ^ (-d)| +
          |(∑ n ∈ Icc 1 K, a n * (n : ℝ) ^ (-d)) -
            ∑ n ∈ Icc 1 K, a n| +
          |(∑ n ∈ Icc 1 K, a n) - ℓ| := by
      calc
        |F d - ℓ| =
            |(F d - ∑ n ∈ Icc 1 K, a n * (n : ℝ) ^ (-d)) +
              ((∑ n ∈ Icc 1 K, a n * (n : ℝ) ^ (-d)) -
                ∑ n ∈ Icc 1 K, a n) +
              ((∑ n ∈ Icc 1 K, a n) - ℓ)| := by ring_nf
        _ ≤ _ := abs_add_three _ _ _
    _ < ε := by linarith [hseries_tail, hhead_d, htail K le_rfl]

end NBMellinTools.NB15
