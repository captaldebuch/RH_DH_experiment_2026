import Mathlib
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninExplicitFormula
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninPeriodReduction
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninCotangentRecognition

/-!
# BBLS §7.2: the function `φ₁` and its evaluation at rationals

Formalizes Proposition 48 of Báez-Duarte–Balazard–Landreau–Saias
(arXiv:math/0306251): for positive integers `p, q`, the conditionally
convergent series `φ₁(p/q) = ∑_{k≥1} B₁(k·p/q)/k` converges, with sum
`(π/(2q))·V(p,q)`, where `V(p,q) = ∑_{a=1}^{q-1} {ap/q}·cot(πa/q)` is the
Vasyunin cotangent sum (`cotangentSumVFormula p q` in this project).

This holds for ALL positive `p, q` — no coprimality is required
(numerically re-verified for non-coprime pairs before formalization).

The proof chain, following the paper but routed through machinery already in
this project:

1. `bblsDigammaShift x := ∑' n, (1/(n+x) − 1/(n+1))` — an absolutely
   convergent surrogate for `−ψ(x) − γ` (digamma), so no digamma API is
   needed.
2. Reflection: `bblsDigammaShift x − bblsDigammaShift (1−x) = π·cot(πx)`,
   derived from the real Mittag-Leffler cotangent expansion
   `real_cot_series_rep'` proved in `VasyuninCotangentRecognition.lean`.
3. A general limit theorem for `∑_{k≤N} g(k)/k` with `g` periodic of mean
   zero: convergence via the discrete Abel identity
   `sum_Icc_div_eq_endpoint_add_abel` (bounded partial sums ⟹ absolutely
   convergent Abel side), value via the block subsequence `N = mq`.
4. Specialization to `g(k) = B₁(k·p/q)` and the pairing `r ↔ q−r`, using
   the oddness of `B₁` and the reflection identity, to produce the finite
   cotangent sum.
-/

namespace RH.Criteria.NymanBeurling.VasyuninGram

open Finset Filter Topology
open RH.Criteria.NymanBeurling.VasyuninCotangentRecognition

/-! ## Elementary `bernoulliB1` symmetry lemmas -/

/-- `B₁` is invariant under integer shifts. -/
theorem bernoulliB1_add_int (x : ℝ) (n : ℤ) : bernoulliB1 (x + n) = bernoulliB1 x := by
  unfold bernoulliB1
  rw [Int.fract_add_intCast]

/-- `B₁` is invariant under natural shifts. -/
theorem bernoulliB1_add_nat (x : ℝ) (n : ℕ) : bernoulliB1 (x + n) = bernoulliB1 x := by
  simpa using bernoulliB1_add_int x n

/-- `B₁` is an odd function (in the Dedekind-sawtooth convention, including at
integers where it vanishes). -/
theorem bernoulliB1_neg (x : ℝ) : bernoulliB1 (-x) = -bernoulliB1 x := by
  unfold bernoulliB1
  by_cases hx : Int.fract x = 0
  · have hnx : Int.fract (-x) = 0 := by
      obtain ⟨m, hm⟩ : ∃ m : ℤ, (m : ℝ) = x := by
        refine ⟨⌊x⌋, ?_⟩
        have h := Int.fract_add_floor x
        rw [hx] at h
        simpa using h
      rw [← hm, ← Int.cast_neg, Int.fract_intCast]
    rw [if_pos hx, if_pos hnx]
    ring
  · have hnx : Int.fract (-x) ≠ 0 := by
      intro h0
      apply hx
      obtain ⟨m, hm⟩ : ∃ m : ℤ, (m : ℝ) = -x := by
        refine ⟨⌊-x⌋, ?_⟩
        have h := Int.fract_add_floor (-x)
        rw [h0] at h
        simpa using h
      have hxx : x = ((-m : ℤ) : ℝ) := by push_cast; linarith [hm]
      rw [hxx, Int.fract_intCast]
    rw [if_neg hx, if_neg hnx, Int.fract_neg hx]
    ring

/-! ## The absolutely convergent digamma-shift series -/

/-- `bblsDigammaShift x = ∑_{n≥0} (1/(n+x) − 1/(n+1))`, an absolutely convergent
series equal to `−ψ(x) − γ` classically; used here as a self-contained surrogate
so that no digamma API is required. -/
noncomputable def bblsDigammaShift (x : ℝ) : ℝ :=
  ∑' n : ℕ, (1 / ((n : ℝ) + x) - 1 / ((n : ℝ) + 1))

theorem summable_bblsDigammaShift {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + x) - 1 / ((n : ℝ) + 1)) := by
  have hmaj : Summable (fun n : ℕ => (|1 - x| / min x 1) * (1 / ((n : ℝ) + 1) ^ 2)) :=
    (summable_realTrigammaSeriesNat 1).mul_left _
  refine Summable.of_abs (Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_) hmaj)
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hnx : (0 : ℝ) < (n : ℝ) + x := by positivity
  have hminpos : (0 : ℝ) < min x 1 := lt_min hx one_pos
  have hkey : 1 / ((n : ℝ) + x) - 1 / ((n : ℝ) + 1) =
      (1 - x) / (((n : ℝ) + x) * ((n : ℝ) + 1)) := by
    field_simp
    ring
  rw [hkey, abs_div, abs_of_pos (by positivity : (0:ℝ) < ((n : ℝ) + x) * ((n : ℝ) + 1))]
  have htarget : (|1 - x| / min x 1) * (1 / ((n : ℝ) + 1) ^ 2) =
      |1 - x| / (min x 1 * ((n : ℝ) + 1) ^ 2) := by
    field_simp
  have hDle : min x 1 * ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + x) * ((n : ℝ) + 1) := by
    have hle : min x 1 * ((n : ℝ) + 1) ≤ (n : ℝ) + x := by
      rcases min_cases x 1 with ⟨hmeq, hx1⟩ | ⟨hmeq, hx1⟩
      · rw [hmeq]
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      · rw [hmeq]
        nlinarith
    calc min x 1 * ((n : ℝ) + 1) ^ 2 = (min x 1 * ((n : ℝ) + 1)) * ((n : ℝ) + 1) := by ring
      _ ≤ ((n : ℝ) + x) * ((n : ℝ) + 1) := mul_le_mul_of_nonneg_right hle hn1.le
  rw [htarget]
  gcongr

/-- Telescoping evaluation `∑_{n≥0} (1/(n+x) − 1/(n+1+x)) = 1/x`. -/
theorem hasSum_bbls_telescope {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + x) - 1 / (((n : ℝ) + 1) + x)) (1 / x) := by
  have hsummable : Summable (fun n : ℕ => 1 / ((n : ℝ) + x) - 1 / (((n : ℝ) + 1) + x)) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
      (summable_realTrigammaSeriesNat x)
    · have h1 : (0 : ℝ) < (n : ℝ) + x := by positivity
      have h2 : (n : ℝ) + x ≤ ((n : ℝ) + 1) + x := by linarith
      have := one_div_le_one_div_of_le h1 h2
      linarith
    · have h1 : (0 : ℝ) < (n : ℝ) + x := by positivity
      have h2 : (0 : ℝ) < ((n : ℝ) + 1) + x := by positivity
      have hkey : 1 / ((n : ℝ) + x) - 1 / (((n : ℝ) + 1) + x) =
          1 / (((n : ℝ) + x) * (((n : ℝ) + 1) + x)) := by
        field_simp
        ring
      rw [hkey]
      have hden : ((n : ℝ) + x) * ((n : ℝ) + x) ≤ ((n : ℝ) + x) * (((n : ℝ) + 1) + x) := by
        nlinarith
    -- 1/((n+x)((n+1)+x)) ≤ 1/(n+x)^2
      have h3 := one_div_le_one_div_of_le (by positivity : (0:ℝ) < ((n : ℝ) + x) * ((n : ℝ) + x))
        hden
      calc 1 / (((n : ℝ) + x) * (((n : ℝ) + 1) + x))
          ≤ 1 / (((n : ℝ) + x) * ((n : ℝ) + x)) := h3
        _ = 1 / ((n : ℝ) + x) ^ 2 := by rw [sq]
  have hps : ∀ N : ℕ, (∑ n ∈ Finset.range N,
      (1 / ((n : ℝ) + x) - 1 / (((n : ℝ) + 1) + x))) = 1 / x - 1 / ((N : ℝ) + x) := by
    intro N
    have h := Finset.sum_range_sub' (f := fun n : ℕ => 1 / ((n : ℝ) + x)) N
    have hcongr : (∑ n ∈ Finset.range N, (1 / ((n : ℝ) + x) - 1 / (((n : ℝ) + 1) + x))) =
        ∑ n ∈ Finset.range N,
          ((fun m : ℕ => 1 / ((m : ℝ) + x)) n - (fun m : ℕ => 1 / ((m : ℝ) + x)) (n + 1)) := by
      apply Finset.sum_congr rfl
      intro n _
      push_cast
      ring_nf
    rw [hcongr, h]
    push_cast
    ring_nf
  have htendsto : Tendsto (fun N : ℕ => 1 / x - 1 / ((N : ℝ) + x)) atTop (𝓝 (1 / x)) := by
    have hdenom : Tendsto (fun N : ℕ => (N : ℝ) + x) atTop atTop :=
      tendsto_atTop_add_const_right atTop x tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + x)) atTop (𝓝 0) := by
      simpa [one_div] using hdenom.inv_tendsto_atTop
    have hconst : Tendsto (fun _ : ℕ => 1 / x) atTop (𝓝 (1 / x)) := tendsto_const_nhds
    simpa using hconst.sub hinv
  have hlim := hsummable.hasSum.tendsto_sum_nat
  have hlim' : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
      (1 / ((n : ℝ) + x) - 1 / (((n : ℝ) + 1) + x))) atTop (𝓝 (1 / x)) := by
    simpa only [hps] using htendsto
  have heq : (∑' n : ℕ, (1 / ((n : ℝ) + x) - 1 / (((n : ℝ) + 1) + x))) = 1 / x :=
    tendsto_nhds_unique hlim hlim'
  exact heq ▸ hsummable.hasSum

/-! ## The reflection identity -/

/-- Reflection: `bblsDigammaShift x − bblsDigammaShift (1−x) = π·cot(πx)` for
`0 < x < 1` — the digamma reflection formula in surrogate form, obtained from
the real Mittag-Leffler cotangent expansion `real_cot_series_rep'`. -/
theorem bblsDigammaShift_reflection {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    bblsDigammaShift x - bblsDigammaShift (1 - x) = Real.pi * Real.cot (Real.pi * x) := by
  have hnint : ∀ n : ℤ, (n : ℝ) ≠ x := by
    intro n hn
    have h0 : (0 : ℤ) < n := by exact_mod_cast hn ▸ hx0
    have h1 : n < (1 : ℤ) := by exact_mod_cast hn ▸ hx1
    omega
  have havail := real_cot_series_rep' hnint
  have hx1' : 0 < 1 - x := by linarith
  have hsx := summable_bblsDigammaShift hx0
  have hs1x := summable_bblsDigammaShift hx1'
  have htargetSummable : Summable
      (fun n : ℕ => 1 / ((n : ℝ) + x) - 1 / (((n : ℝ) + 1) - x)) := by
    have h := hsx.sub hs1x
    apply h.congr
    intro n
    ring_nf
  have hdiff : bblsDigammaShift x - bblsDigammaShift (1 - x) =
      ∑' n : ℕ, (1 / ((n : ℝ) + x) - 1 / (((n : ℝ) + 1) - x)) := by
    unfold bblsDigammaShift
    rw [← hsx.tsum_sub hs1x]
    apply tsum_congr
    intro n
    ring_nf
  have htele := hasSum_bbls_telescope hx0
  have htargetHasSum := htargetSummable.hasSum
  have hfun : (fun n : ℕ =>
      (1 / ((n : ℝ) + x) - 1 / (((n : ℝ) + 1) - x)) -
        (1 / ((n : ℝ) + x) - 1 / (((n : ℝ) + 1) + x))) =
      fun n : ℕ => 1 / (x - ((n : ℝ) + 1)) + 1 / (x + ((n : ℝ) + 1)) := by
    funext n
    have h1 : ((n : ℝ) + 1) - x ≠ 0 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have h2 : ((n : ℝ) + 1) + x ≠ 0 := by positivity
    have h3 : x - ((n : ℝ) + 1) ≠ 0 := by
      intro h
      apply h1
      linarith
    field_simp
    ring
  have havailHasSum : HasSum
      (fun n : ℕ => 1 / (x - ((n : ℝ) + 1)) + 1 / (x + ((n : ℝ) + 1)))
      ((∑' n : ℕ, (1 / ((n : ℝ) + x) - 1 / (((n : ℝ) + 1) - x))) - 1 / x) :=
    hfun ▸ (htargetHasSum.sub htele)
  have havailValue : Real.pi * Real.cot (Real.pi * x) - 1 / x =
      (∑' n : ℕ, (1 / ((n : ℝ) + x) - 1 / (((n : ℝ) + 1) - x))) - 1 / x := by
    rw [havail, havailHasSum.tsum_eq]
  rw [hdiff]
  linarith [havailValue]

/-! ## Convergence of `∑ g(k)/k` for periodic mean-zero `g` -/

section PeriodicMeanZero

variable (g : ℕ → ℝ) (q : ℕ)

/-- Iterated periodicity. -/
theorem bbls_periodic_iterate (hper : ∀ k, g (k + q) = g k) :
    ∀ m k, g (k + m * q) = g k := by
  intro m
  induction m with
  | zero => intro k; simp
  | succ m ih =>
      intro k
      have h1 : k + (m + 1) * q = (k + m * q) + q := by ring
      rw [h1, hper, ih]

/-- The sum of `g` over any block of `q` consecutive integers `(k, k+q]` equals
the sum over `(0, q]`, for `q`-periodic `g`. -/
theorem bbls_block_sum_invariant (hper : ∀ k, g (k + q) = g k) :
    ∀ k, (∑ j ∈ Finset.Ioc k (k + q), g j) = ∑ j ∈ Finset.Ioc 0 q, g j := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hsplit1 : (∑ j ∈ Finset.Ioc k (k + 1 + q), g j) =
          (∑ j ∈ Finset.Ioc k (k + 1), g j) + ∑ j ∈ Finset.Ioc (k + 1) (k + 1 + q), g j := by
        rw [Finset.sum_Ioc_consecutive]
        · omega
        · omega
      have hsplit2 : (∑ j ∈ Finset.Ioc k (k + 1 + q), g j) =
          (∑ j ∈ Finset.Ioc k (k + q), g j) + ∑ j ∈ Finset.Ioc (k + q) (k + 1 + q), g j := by
        rw [Finset.sum_Ioc_consecutive]
        · omega
        · omega
      have hIoc1 : (∑ j ∈ Finset.Ioc k (k + 1), g j) = g (k + 1) := by
        have : Finset.Ioc k (k + 1) = {k + 1} := by
          ext j
          simp only [Finset.mem_Ioc, Finset.mem_singleton]
          omega
        rw [this, Finset.sum_singleton]
      have hIoc2 : (∑ j ∈ Finset.Ioc (k + q) (k + 1 + q), g j) = g (k + 1 + q) := by
        have : Finset.Ioc (k + q) (k + 1 + q) = {k + 1 + q} := by
          ext j
          simp only [Finset.mem_Ioc, Finset.mem_singleton]
          omega
        rw [this, Finset.sum_singleton]
      have hgper : g (k + 1 + q) = g (k + 1) := hper (k + 1)
      have : (∑ j ∈ Finset.Ioc (k + 1) (k + 1 + q), g j) =
          ∑ j ∈ Finset.Ioc k (k + q), g j := by
        have h12 := hsplit1
        rw [hsplit2, hIoc2, hgper] at h12
        rw [hIoc1] at h12
        linarith
      rw [this, ih]

/-- Partial sums of a `q`-periodic mean-zero `g` are `q`-periodic. -/
theorem bbls_partial_sum_periodic (hper : ∀ k, g (k + q) = g k)
    (hmean : (∑ r ∈ Finset.Ioc 0 q, g r) = 0) :
    ∀ k, (∑ j ∈ Finset.Ioc 0 (k + q), g j) = ∑ j ∈ Finset.Ioc 0 k, g j := by
  intro k
  have hsplit : (∑ j ∈ Finset.Ioc 0 (k + q), g j) =
      (∑ j ∈ Finset.Ioc 0 k, g j) + ∑ j ∈ Finset.Ioc k (k + q), g j := by
    rw [Finset.sum_Ioc_consecutive]
    · omega
    · omega
  rw [hsplit, bbls_block_sum_invariant g q hper k, hmean, add_zero]

/-- Partial sums of a `q`-periodic mean-zero `g` are uniformly bounded by
`∑_{j∈(0,q]} |g j|`. -/
theorem bbls_partial_sum_bounded (hq : 0 < q) (hper : ∀ k, g (k + q) = g k)
    (hmean : (∑ r ∈ Finset.Ioc 0 q, g r) = 0) :
    ∀ k, |∑ j ∈ Finset.Ioc 0 k, g j| ≤ ∑ j ∈ Finset.Ioc 0 q, |g j| := by
  have haux : ∀ m r : ℕ, (∑ j ∈ Finset.Ioc 0 (r + m * q), g j) = ∑ j ∈ Finset.Ioc 0 r, g j := by
    intro m
    induction m with
    | zero => intro r; simp
    | succ m ih =>
        intro r
        have h1 : r + (m + 1) * q = (r + m * q) + q := by ring
        rw [h1, bbls_partial_sum_periodic g q hper hmean (r + m * q), ih]
  have hreduce : ∀ k, (∑ j ∈ Finset.Ioc 0 k, g j) = ∑ j ∈ Finset.Ioc 0 (k % q), g j := by
    intro k
    conv_lhs => rw [show k = k % q + (k / q) * q from (Nat.mod_add_div' k q).symm]
    rw [haux (k / q) (k % q)]
  intro k
  rw [hreduce k]
  calc |∑ j ∈ Finset.Ioc 0 (k % q), g j| ≤ ∑ j ∈ Finset.Ioc 0 (k % q), |g j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.Ioc 0 q, |g j| := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · apply Finset.Ioc_subset_Ioc_right
          exact (Nat.mod_lt k hq).le
        · intro j _ _
          exact abs_nonneg _

/-- **Convergence and value of `∑_{k≤N} g(k)/k` for periodic mean-zero `g`**
(BBLS Propositions 46–47 in surrogate form): the partial sums converge to
`(1/q)·∑_{r∈(0,q]} g(r)·bblsDigammaShift(r/q)`. -/
theorem bbls_tendsto_sum_div_of_periodic_meanzero (hq : 0 < q)
    (hper : ∀ k, g (k + q) = g k)
    (hmean : (∑ r ∈ Finset.Ioc 0 q, g r) = 0) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N, g k / (k : ℝ)) atTop
      (𝓝 ((1 / (q : ℝ)) *
        ∑ r ∈ Finset.Ioc 0 q, g r * bblsDigammaShift ((r : ℝ) / q))) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  -- the bound on partial sums
  set B : ℝ := ∑ j ∈ Finset.Ioc 0 q, |g j| with hBdef
  have hGbdd := bbls_partial_sum_bounded g q hq hper hmean
  -- Icc 1 k = Ioc 0 k for ℕ
  have hIccIoc : ∀ k : ℕ, Finset.Icc 1 k = Finset.Ioc 0 k := by
    intro k
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  -- Step 1: existence of the limit, via the Abel identity.
  set T : ℕ → ℝ := fun k =>
    (∑ j ∈ Finset.Icc 1 k, g j) * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) with hTdef
  have hT0 : T 0 = 0 := by
    simp [hTdef]
  have hTsummable : Summable T := by
    apply Summable.of_norm_bounded
      (g := fun k : ℕ => (2 * B) * (1 / ((k : ℝ) + 1) ^ 2))
      ((summable_realTrigammaSeriesNat 1).mul_left _)
    intro k
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      simp only [hT0, norm_zero]
      have hBnn : 0 ≤ B := Finset.sum_nonneg fun j _ => abs_nonneg _
      positivity
    · have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
      have hbound : |∑ j ∈ Finset.Icc 1 k, g j| ≤ B := by
        rw [hIccIoc k]
        exact hGbdd k
      have hfrac : 1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ) =
          1 / ((k : ℝ) * ((k : ℝ) + 1)) := by
        push_cast
        field_simp
        ring
      have hfracnn : (0 : ℝ) ≤ 1 / ((k : ℝ) * ((k : ℝ) + 1)) := by positivity
      rw [Real.norm_eq_abs, hTdef]
      simp only
      rw [abs_mul, hfrac, abs_of_nonneg hfracnn]
      have h2 : 1 / ((k : ℝ) * ((k : ℝ) + 1)) ≤ 2 / ((k : ℝ) + 1) ^ 2 := by
        have h1k : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkpos
        have hkey : ((k : ℝ) + 1) ^ 2 ≤ 2 * ((k : ℝ) * ((k : ℝ) + 1)) := by nlinarith
        calc 1 / ((k : ℝ) * ((k : ℝ) + 1)) = 2 / (2 * ((k : ℝ) * ((k : ℝ) + 1))) := by
              rw [div_eq_div_iff (by positivity) (by positivity)]
              ring
          _ ≤ 2 / ((k : ℝ) + 1) ^ 2 := by gcongr
      calc |∑ j ∈ Finset.Icc 1 k, g j| * (1 / ((k : ℝ) * ((k : ℝ) + 1)))
          ≤ B * (2 / ((k : ℝ) + 1) ^ 2) := by
            apply mul_le_mul hbound h2 hfracnn
            exact le_trans (abs_nonneg _) hbound
        _ = (2 * B) * (1 / ((k : ℝ) + 1) ^ 2) := by ring
  -- partial sums of T over Icc 1 N converge to the tsum
  have hTsum_tendsto : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N, T k) atTop
      (𝓝 (∑' k, T k)) := by
    have hIccRange : ∀ N : ℕ, (∑ k ∈ Finset.Icc 1 N, T k) = ∑ k ∈ Finset.range (N + 1), T k := by
      intro N
      have hins : Finset.range (N + 1) = insert 0 (Finset.Ioc 0 N) := by
        ext j
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
        omega
      rw [hIccIoc N, hins, Finset.sum_insert (by simp), hT0, zero_add]
    have h1 := hTsummable.hasSum.tendsto_sum_nat
    have h2 : Tendsto (fun N : ℕ => N + 1) atTop atTop := tendsto_add_atTop_nat 1
    have h3 := h1.comp h2
    simp only [Function.comp_def] at h3
    exact Tendsto.congr (fun N => (hIccRange N).symm) h3
  -- endpoint term → 0
  have hEndpoint : Tendsto (fun N : ℕ =>
      (∑ j ∈ Finset.Icc 1 N, g j) / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have hb : ∀ N : ℕ, ‖(∑ j ∈ Finset.Icc 1 N, g j) / ((N + 1 : ℕ) : ℝ)‖ ≤
        B / ((N : ℝ) + 1) := by
      intro N
      rw [Real.norm_eq_abs, abs_div]
      have h1 : |((N + 1 : ℕ) : ℝ)| = (N : ℝ) + 1 := by
        push_cast
        rw [abs_of_pos (by positivity)]
      rw [h1]
      gcongr
      rw [hIccIoc N]
      exact hGbdd N
    have hg0 : Tendsto (fun N : ℕ => B / ((N : ℝ) + 1)) atTop (𝓝 0) := by
      have hdenom : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
        tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
      simpa [div_eq_mul_inv] using
        (tendsto_const_nhds (x := B)).mul hdenom.inv_tendsto_atTop
    exact squeeze_zero_norm hb hg0
  -- so S_N converges to ∑' T
  have hS_tendsto : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N, g k / (k : ℝ)) atTop
      (𝓝 (∑' k, T k)) := by
    have habel : ∀ N : ℕ, (∑ k ∈ Finset.Icc 1 N, g k / (k : ℝ)) =
        (∑ j ∈ Finset.Icc 1 N, g j) / ((N + 1 : ℕ) : ℝ) + ∑ k ∈ Finset.Icc 1 N, T k := by
      intro N
      exact sum_Icc_div_eq_endpoint_add_abel g N
    have := hEndpoint.add hTsum_tendsto
    rw [zero_add] at this
    exact Tendsto.congr (fun N => (habel N).symm) this
  -- Step 2: block subsequence N = m·q and its explicit limit.
  have hmul_tendsto : Tendsto (fun m : ℕ => m * q) atTop atTop := by
    apply tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_right m hq)
    exact tendsto_id
  have hblock_sub : Tendsto (fun m : ℕ => ∑ k ∈ Finset.Icc 1 (m * q), g k / (k : ℝ)) atTop
      (𝓝 (∑' k, T k)) := hS_tendsto.comp hmul_tendsto
  -- the block partial sums, rearranged
  have hblock_eq : ∀ m : ℕ, (∑ k ∈ Finset.Icc 1 (m * q), g k / (k : ℝ)) =
      ∑ r ∈ Finset.Ioc 0 q, g r *
        (∑ n ∈ Finset.range m, (1 / (((n * q + r : ℕ) : ℝ)) - 1 / (((n * q + q : ℕ) : ℝ)))) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        have heq : (m + 1) * q = m * q + q := by ring
        have hsplit : (∑ k ∈ Finset.Icc 1 ((m + 1) * q), g k / (k : ℝ)) =
            (∑ k ∈ Finset.Icc 1 (m * q), g k / (k : ℝ)) +
              ∑ k ∈ Finset.Ioc (m * q) (m * q + q), g k / (k : ℝ) := by
          rw [heq, hIccIoc, hIccIoc]
          rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le (m * q))
            (by omega : m * q ≤ m * q + q)]
        have hset : Finset.Ioc (m * q) (m * q + q) =
            (Finset.Ioc 0 q).map (addLeftEmbedding (m * q)) := by
          ext j
          simp only [Finset.mem_map, Finset.mem_Ioc, addLeftEmbedding_apply]
          constructor
          · intro ⟨h1, h2⟩
            exact ⟨j - m * q, by omega, by omega⟩
          · rintro ⟨r, ⟨hr0, hrq⟩, rfl⟩
            omega
        have hper' : ∀ r : ℕ, g (m * q + r) = g r := by
          intro r
          have h := bbls_periodic_iterate g q hper m r
          rw [← h]
          congr 1
          omega
        have hshift : (∑ k ∈ Finset.Ioc (m * q) (m * q + q), g k / (k : ℝ)) =
            ∑ r ∈ Finset.Ioc 0 q, g r * (1 / ((m * q + r : ℕ) : ℝ)) := by
          rw [hset, Finset.sum_map]
          apply Finset.sum_congr rfl
          intro r _
          simp only [addLeftEmbedding_apply]
          rw [hper' r, div_eq_mul_one_div]
        have hzero : (∑ r ∈ Finset.Ioc 0 q, g r * (1 / ((m * q + q : ℕ) : ℝ))) = 0 := by
          rw [← Finset.sum_mul, hmean, zero_mul]
        have hlast : (∑ k ∈ Finset.Ioc (m * q) (m * q + q), g k / (k : ℝ)) =
            ∑ r ∈ Finset.Ioc 0 q, g r * (1 / ((m * q + r : ℕ) : ℝ) -
              1 / ((m * q + q : ℕ) : ℝ)) := by
          have hexpand : (∑ r ∈ Finset.Ioc 0 q, g r * (1 / ((m * q + r : ℕ) : ℝ) -
              1 / ((m * q + q : ℕ) : ℝ))) =
              (∑ r ∈ Finset.Ioc 0 q, g r * (1 / ((m * q + r : ℕ) : ℝ))) -
                ∑ r ∈ Finset.Ioc 0 q, g r * (1 / ((m * q + q : ℕ) : ℝ)) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro r _
            ring
          rw [hexpand, hzero, sub_zero, hshift]
        rw [hsplit, ih, hlast, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.sum_range_succ]
        ring
  -- the explicit limit of the blocks
  have hblock_limit : Tendsto (fun m : ℕ => ∑ r ∈ Finset.Ioc 0 q, g r *
      (∑ n ∈ Finset.range m, (1 / (((n * q + r : ℕ) : ℝ)) - 1 / (((n * q + q : ℕ) : ℝ)))))
      atTop (𝓝 (∑ r ∈ Finset.Ioc 0 q, g r * ((1 / (q : ℝ)) * bblsDigammaShift ((r : ℝ) / q)))) := by
    apply tendsto_finsetSum
    intro r hr
    have hr0 : 0 < r := (Finset.mem_Ioc.mp hr).1
    have hrq : r ≤ q := (Finset.mem_Ioc.mp hr).2
    have hrR : (0 : ℝ) < (r : ℝ) / q := by
      apply div_pos (by exact_mod_cast hr0) hqR
    have hterm : ∀ n : ℕ, (1 / (((n * q + r : ℕ) : ℝ)) - 1 / (((n * q + q : ℕ) : ℝ))) =
        (1 / (q : ℝ)) * (1 / ((n : ℝ) + (r : ℝ) / q) - 1 / ((n : ℝ) + 1)) := by
      intro n
      push_cast
      have h1 : ((n : ℝ) * q + r) ≠ 0 := by positivity
      have h2 : ((n : ℝ) * q + q) ≠ 0 := by positivity
      have h3 : ((n : ℝ) + (r : ℝ) / q) ≠ 0 := by positivity
      have h4 : ((n : ℝ) + 1) ≠ 0 := by positivity
      field_simp
    have hinner : Tendsto (fun m : ℕ => ∑ n ∈ Finset.range m,
        (1 / ((n : ℝ) + (r : ℝ) / q) - 1 / ((n : ℝ) + 1))) atTop
        (𝓝 (bblsDigammaShift ((r : ℝ) / q))) :=
      (summable_bblsDigammaShift hrR).hasSum.tendsto_sum_nat
    have hscaled := hinner.const_mul (1 / (q : ℝ))
    have hfinal := hscaled.const_mul (g r)
    have hswap : ∀ m : ℕ, g r * ((1 / (q : ℝ)) * ∑ n ∈ Finset.range m,
        (1 / ((n : ℝ) + (r : ℝ) / q) - 1 / ((n : ℝ) + 1))) =
        g r * ∑ n ∈ Finset.range m,
          (1 / (((n * q + r : ℕ) : ℝ)) - 1 / (((n * q + q : ℕ) : ℝ))) := by
      intro m
      congr 1
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => (hterm n).symm
    exact Tendsto.congr (fun m => hswap m) hfinal
  -- combine: limit uniqueness on the subsequence
  have hblocks := Tendsto.congr (fun m => (hblock_eq m).symm) hblock_limit
  have huniq : (∑' k, T k) = ∑ r ∈ Finset.Ioc 0 q, g r *
      ((1 / (q : ℝ)) * bblsDigammaShift ((r : ℝ) / q)) :=
    tendsto_nhds_unique hblock_sub hblocks
  rw [huniq] at hS_tendsto
  have hfinal_eq : (∑ r ∈ Finset.Ioc 0 q, g r * ((1 / (q : ℝ)) * bblsDigammaShift ((r : ℝ) / q)))
      = (1 / (q : ℝ)) * ∑ r ∈ Finset.Ioc 0 q, g r * bblsDigammaShift ((r : ℝ) / q) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [hfinal_eq] at hS_tendsto
  exact hS_tendsto

end PeriodicMeanZero

/-! ## Specialization: `φ₁(p/q) = (π/(2q))·V(p,q)` (BBLS Proposition 48) -/

section Phi1AtRationals

variable (p q : ℕ)

/-- `B₁(m/2) = 0` for every natural `m`: at integers by convention, at
half-integers because the sawtooth value `1/2 − 1/2` vanishes. -/
theorem bernoulliB1_nat_div_two (m : ℕ) : bernoulliB1 ((m : ℝ) / 2) = 0 := by
  rcases Nat.even_or_odd m with ⟨t, ht⟩ | ⟨t, ht⟩
  · subst ht
    apply bernoulliB1_of_isInt (t : ℤ)
    push_cast
    ring
  · subst ht
    have harg : ((2 * t + 1 : ℕ) : ℝ) / 2 = 1 / 2 + (t : ℕ) := by
      push_cast
      ring
    rw [harg, bernoulliB1_add_nat]
    unfold bernoulliB1
    have h12 : Int.fract (1 / 2 : ℝ) = 1 / 2 := by
      rw [Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
    rw [h12]
    norm_num

/-- Periodicity of `k ↦ B₁(k·p/q)` with period `q`. -/
theorem bernoulliB1_rat_periodic (hq : 0 < q) :
    ∀ k : ℕ, bernoulliB1 (((k + q : ℕ) : ℝ) * ((p : ℝ) / q)) =
      bernoulliB1 ((k : ℝ) * ((p : ℝ) / q)) := by
  intro k
  have hqne : (q : ℝ) ≠ 0 := by positivity
  have harg : ((k + q : ℕ) : ℝ) * ((p : ℝ) / q) = (k : ℝ) * ((p : ℝ) / q) + (p : ℕ) := by
    push_cast
    field_simp
  rw [harg, bernoulliB1_add_nat]

/-- Oddness under the reflection `r ↦ q − r`. -/
theorem bernoulliB1_rat_reflect (hq : 0 < q) :
    ∀ r ∈ Finset.Ioc 0 (q - 1), bernoulliB1 (((q - r : ℕ) : ℝ) * ((p : ℝ) / q)) =
      -bernoulliB1 ((r : ℝ) * ((p : ℝ) / q)) := by
  intro r hr
  simp only [Finset.mem_Ioc] at hr
  have hrq : r ≤ q := by omega
  have hqne : (q : ℝ) ≠ 0 := by positivity
  have hcast : ((q - r : ℕ) : ℝ) = (q : ℝ) - r := by
    push_cast [Nat.cast_sub hrq]
    ring
  have harg : ((q : ℝ) - r) * ((p : ℝ) / q) = -((r : ℝ) * ((p : ℝ) / q)) + (p : ℕ) := by
    field_simp
    ring
  rw [hcast, harg, bernoulliB1_add_nat, bernoulliB1_neg]

/-- Mean zero of `B₁(r·p/q)` over one period. -/
theorem bernoulliB1_rat_meanzero (hp : 0 < p) (hq : 0 < q) :
    (∑ r ∈ Finset.Ioc 0 q, bernoulliB1 ((r : ℝ) * ((p : ℝ) / q))) = 0 := by
  have hqne : (q : ℝ) ≠ 0 := by positivity
  have hq_term : bernoulliB1 ((q : ℝ) * ((p : ℝ) / q)) = 0 := by
    apply bernoulliB1_of_isInt (p : ℤ)
    push_cast
    field_simp
  have hsplit : Finset.Ioc 0 q = insert q (Finset.Ioc 0 (q - 1)) := by
    ext j
    simp only [Finset.mem_Ioc, Finset.mem_insert]
    omega
  have hqnotmem : q ∉ Finset.Ioc 0 (q - 1) := by
    simp only [Finset.mem_Ioc]
    omega
  rw [hsplit, Finset.sum_insert hqnotmem, hq_term, zero_add]
  apply Finset.sum_involution (fun r _ => q - r)
  · intro r hr
    rw [bernoulliB1_rat_reflect p q hq r hr]
    ring
  · intro r hr hfr
    simp only [Finset.mem_Ioc] at hr
    intro heq
    apply hfr
    have hq2r : q = 2 * r := by omega
    have harg : (r : ℝ) * ((p : ℝ) / q) = (p : ℝ) / 2 := by
      rw [hq2r]
      have hrne : (r : ℝ) ≠ 0 := by
        have : 0 < r := hr.1
        positivity
      push_cast
      field_simp
    rw [harg]
    exact bernoulliB1_nat_div_two p
  · intro r hr
    simp only [Finset.mem_Ioc] at hr ⊢
    omega
  · intro r hr
    simp only [Finset.mem_Ioc] at hr
    omega

/-- Antisymmetry of the cotangent term under `r ↦ q − r`. -/
theorem cotangentTermV_reflect (hq : 0 < q) :
    ∀ r ∈ Finset.Ioc 0 (q - 1), cotangentTermV (q - r) q = -cotangentTermV r q := by
  intro r hr
  simp only [Finset.mem_Ioc] at hr
  have hrq : r ≤ q := by omega
  have hqne : (q : ℝ) ≠ 0 := by positivity
  unfold cotangentTermV
  have hcast : ((q - r : ℕ) : ℝ) = (q : ℝ) - r := by
    push_cast [Nat.cast_sub hrq]
    ring
  have harg : Real.pi * (((q : ℝ) - r)) / q = Real.pi - Real.pi * r / q := by
    field_simp
  rw [hcast, harg, Real.cos_pi_sub, Real.sin_pi_sub]
  ring

/-- The fract-vanishing condition is stable under the reflection `r ↦ q − r`. -/
theorem fract_rat_reflect_eq_zero_iff (hq : 0 < q) :
    ∀ r ∈ Finset.Ioc 0 (q - 1),
      (Int.fract (((q - r : ℕ) : ℝ) * ((p : ℝ) / q)) = 0 ↔
        Int.fract ((r : ℝ) * ((p : ℝ) / q)) = 0) := by
  intro r hr
  simp only [Finset.mem_Ioc] at hr
  have hrq : r ≤ q := by omega
  have hqne : (q : ℝ) ≠ 0 := by positivity
  have hcast : ((q - r : ℕ) : ℝ) = (q : ℝ) - r := by
    push_cast [Nat.cast_sub hrq]
    ring
  have harg : ((q : ℝ) - r) * ((p : ℝ) / q) = -((r : ℝ) * ((p : ℝ) / q)) + ((p : ℤ) : ℝ) := by
    push_cast
    field_simp
    ring
  rw [hcast, harg, Int.fract_add_intCast, Int.fract_neg_eq_zero]

/-- The evaluated limit: `(1/q)·∑_{r∈(0,q]} B₁(r·p/q)·G(r/q) = (π/(2q))·V(p,q)`. -/
theorem bbls_phi1_value (hp : 0 < p) (hq : 0 < q) :
    (1 / (q : ℝ)) * ∑ r ∈ Finset.Ioc 0 q,
        bernoulliB1 ((r : ℝ) * ((p : ℝ) / q)) * bblsDigammaShift ((r : ℝ) / q) =
      Real.pi / (2 * q) * cotangentSumVFormula p q := by
  have hqne : (q : ℝ) ≠ 0 := by positivity
  have hqR : (0 : ℝ) < q := by positivity
  -- drop the r = q term
  have hq_term : bernoulliB1 ((q : ℝ) * ((p : ℝ) / q)) = 0 := by
    apply bernoulliB1_of_isInt (p : ℤ)
    push_cast
    field_simp
  have hsplitq : Finset.Ioc 0 q = insert q (Finset.Ioc 0 (q - 1)) := by
    ext j
    simp only [Finset.mem_Ioc, Finset.mem_insert]
    omega
  have hqnotmem : q ∉ Finset.Ioc 0 (q - 1) := by
    simp only [Finset.mem_Ioc]
    omega
  rw [hsplitq, Finset.sum_insert hqnotmem, hq_term, zero_mul, zero_add]
  -- reindex the sum under the reflection r ↦ q − r
  set S : ℝ := ∑ r ∈ Finset.Ioc 0 (q - 1),
    bernoulliB1 ((r : ℝ) * ((p : ℝ) / q)) * bblsDigammaShift ((r : ℝ) / q) with hSdef
  have hreindex : S = ∑ r ∈ Finset.Ioc 0 (q - 1),
      (-bernoulliB1 ((r : ℝ) * ((p : ℝ) / q))) * bblsDigammaShift (1 - (r : ℝ) / q) := by
    rw [hSdef]
    apply Finset.sum_nbij' (i := fun r => q - r) (j := fun r => q - r)
    · intro r hr
      simp only [Finset.mem_Ioc] at hr ⊢
      omega
    · intro r hr
      simp only [Finset.mem_Ioc] at hr ⊢
      omega
    · intro r hr
      simp only [Finset.mem_Ioc] at hr
      omega
    · intro r hr
      simp only [Finset.mem_Ioc] at hr
      omega
    · intro r hr
      have hrmem := hr
      simp only [Finset.mem_Ioc] at hr
      have hrq : r ≤ q := by omega
      -- B₁((q−r)p/q) = −B₁(rp/q), so −B₁((q−r)p/q) = B₁(rp/q)
      have hB := bernoulliB1_rat_reflect p q hq r hrmem
      -- (q−r)/q = 1 − r/q
      have hGarg : ((q - r : ℕ) : ℝ) / q = 1 - (r : ℝ) / q := by
        push_cast [Nat.cast_sub hrq]
        field_simp
      rw [hB, hGarg]
      ring
  -- double the sum and apply the reflection identity
  have hdouble : 2 * S = ∑ r ∈ Finset.Ioc 0 (q - 1),
      bernoulliB1 ((r : ℝ) * ((p : ℝ) / q)) *
        (Real.pi * Real.cot (Real.pi * ((r : ℝ) / q))) := by
    have h2 : 2 * S = S + S := by ring
    rw [h2]
    nth_rewrite 2 [hreindex]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [Finset.mem_Ioc] at hr
    have hr0 : (0 : ℝ) < (r : ℝ) / q := by
      have h1 : 0 < r := hr.1
      have h1' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast h1
      positivity
    have hr1 : (r : ℝ) / q < 1 := by
      rw [div_lt_one hqR]
      have : r < q := by omega
      exact_mod_cast this
    have hrefl := bblsDigammaShift_reflection hr0 hr1
    calc bernoulliB1 ((r : ℝ) * ((p : ℝ) / q)) * bblsDigammaShift ((r : ℝ) / q) +
          (-bernoulliB1 ((r : ℝ) * ((p : ℝ) / q))) * bblsDigammaShift (1 - (r : ℝ) / q)
        = bernoulliB1 ((r : ℝ) * ((p : ℝ) / q)) *
            (bblsDigammaShift ((r : ℝ) / q) - bblsDigammaShift (1 - (r : ℝ) / q)) := by
          ring
      _ = bernoulliB1 ((r : ℝ) * ((p : ℝ) / q)) *
            (Real.pi * Real.cot (Real.pi * ((r : ℝ) / q))) := by
          rw [hrefl]
  -- identify the cotangent with the project's cotangent term
  have hcot_eq : ∀ r : ℕ, Real.cot (Real.pi * ((r : ℝ) / q)) = cotangentTermV r q := by
    intro r
    unfold cotangentTermV
    rw [Real.cot_eq_cos_div_sin]
    have harg : Real.pi * ((r : ℝ) / q) = Real.pi * (r : ℝ) / q := by ring
    rw [harg]
  -- split B₁ into fract minus half-indicator
  have hsplit_sum : (∑ r ∈ Finset.Ioc 0 (q - 1),
      bernoulliB1 ((r : ℝ) * ((p : ℝ) / q)) * cotangentTermV r q) =
      (∑ r ∈ Finset.Ioc 0 (q - 1), Int.fract ((r : ℝ) * ((p : ℝ) / q)) * cotangentTermV r q) -
        (1 / 2) * ∑ r ∈ Finset.Ioc 0 (q - 1),
          (if Int.fract ((r : ℝ) * ((p : ℝ) / q)) = 0 then 0 else cotangentTermV r q) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    unfold bernoulliB1
    by_cases h : Int.fract ((r : ℝ) * ((p : ℝ) / q)) = 0
    · rw [if_pos h, if_pos h, h]
      ring
    · rw [if_neg h, if_neg h]
      ring
  -- the half-indicator sum vanishes by the reflection involution
  have hite_zero : (∑ r ∈ Finset.Ioc 0 (q - 1),
      (if Int.fract ((r : ℝ) * ((p : ℝ) / q)) = 0 then 0 else cotangentTermV r q)) = 0 := by
    apply Finset.sum_involution (fun r _ => q - r)
    · intro r hr
      have hiff := fract_rat_reflect_eq_zero_iff p q hq r hr
      have hcot := cotangentTermV_reflect q hq r hr
      by_cases h : Int.fract ((r : ℝ) * ((p : ℝ) / q)) = 0
      · rw [if_pos h, if_pos (hiff.mpr h)]
        ring
      · rw [if_neg h, if_neg (fun hc => h (hiff.mp hc)), hcot]
        ring
    · intro r hr hne heq
      apply hne
      simp only [Finset.mem_Ioc] at hr
      have hq2r : q = 2 * r := by omega
      have hval : cotangentTermV r q = 0 := by
        unfold cotangentTermV
        have hrne : (r : ℝ) ≠ 0 := by
          have h1 : 0 < r := hr.1
          have : (0 : ℝ) < (r : ℝ) := by exact_mod_cast h1
          positivity
        have harg : Real.pi * (r : ℝ) / (q : ℝ) = Real.pi / 2 := by
          rw [hq2r]
          push_cast
          field_simp
        rw [harg, Real.cos_pi_div_two]
        simp
      rw [hval]
      split <;> rfl
    · intro r hr
      simp only [Finset.mem_Ioc] at hr ⊢
      omega
    · intro r hr
      simp only [Finset.mem_Ioc] at hr
      omega
  -- the fract-cotangent sum is exactly the Vasyunin sum
  have hV : (∑ r ∈ Finset.Ioc 0 (q - 1),
      Int.fract ((r : ℝ) * ((p : ℝ) / q)) * cotangentTermV r q) =
      cotangentSumVFormula p q := by
    unfold cotangentSumVFormula
    have hset : Finset.Ico 1 q = Finset.Ioc 0 (q - 1) := by
      ext j
      simp only [Finset.mem_Ico, Finset.mem_Ioc]
      omega
    rw [hset]
    apply Finset.sum_congr rfl
    intro r _
    congr 2
    push_cast
    ring
  -- assemble
  have h2S : 2 * S = Real.pi * cotangentSumVFormula p q := by
    have hstep : 2 * S = Real.pi * ∑ r ∈ Finset.Ioc 0 (q - 1),
        bernoulliB1 ((r : ℝ) * ((p : ℝ) / q)) * cotangentTermV r q := by
      rw [hdouble, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [hcot_eq r]
      ring
    rw [hstep, hsplit_sum, hite_zero, mul_zero, sub_zero, hV]
  have hSval : S = Real.pi * cotangentSumVFormula p q / 2 := by linarith
  rw [hSval]
  field_simp

/-- **BBLS Proposition 48**: the partial sums of `∑_{k≥1} B₁(k·p/q)/k` converge, with
limit `(π/(2q))·V(p,q)` — for ALL positive `p, q`, coprime or not. -/
theorem tendsto_bernoulliB1_sum_div_rat (hp : 0 < p) (hq : 0 < q) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
        bernoulliB1 ((k : ℝ) * ((p : ℝ) / q)) / (k : ℝ)) atTop
      (𝓝 (Real.pi / (2 * q) * cotangentSumVFormula p q)) := by
  have h := bbls_tendsto_sum_div_of_periodic_meanzero
    (fun k : ℕ => bernoulliB1 ((k : ℝ) * ((p : ℝ) / q))) q hq
    (fun k => bernoulliB1_rat_periodic p q hq k)
    (bernoulliB1_rat_meanzero p q hp hq)
  rw [bbls_phi1_value p q hp hq] at h
  exact h

end Phi1AtRationals

end RH.Criteria.NymanBeurling.VasyuninGram
