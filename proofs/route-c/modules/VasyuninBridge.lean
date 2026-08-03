import Mathlib
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninGram
import RiemannHypothesis.Criteria.NymanBeurling.BBLSAutocorrelation
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninExplicitFormula
import RiemannHypothesis.Criteria.NymanBeurling.G11IntegralEvaluation
import RiemannHypothesis.Criteria.NymanBeurling.G11Formula

namespace RH.Criteria.NymanBeurling.VasyuninGram

open RH.Criteria.NymanBeurling.BaezDuarte
open scoped MeasureTheory

-- ---------------------------------------------------------------------------
-- 1. Symmetric properties
-- ---------------------------------------------------------------------------

/-- The integral of fractional parts over an interval [1/(m+1), 1/m] -/
noncomputable def fractionalPartIntervalIntegral (h k m : ℕ) : ℝ :=
  ∫ x in Set.Ioc (1 / ((m + 1 : ℝ))) (1 / ((m : ℝ))),
    (Int.fract (1 / ((h : ℝ) * x))) * (Int.fract (1 / ((k : ℝ) * x)))

-- ---------------------------------------------------------------------------
-- 2. The common pointwise integrand, and the corrected interval-partition
--    analysis of `baezDuarteGramEntry`.
--
-- IMPORTANT CORRECTNESS NOTE (found while implementing this file):
--
-- The naive statement `baezDuarteGramEntry h k = ∑' m, fractionalPartIntervalIntegral h k m`
-- is FALSE. The intervals `Ioc (1/(m+1)) (1/m)` for `m : ℕ` are pairwise disjoint and their
-- union is exactly `Ioc 0 1` (the `m = 0` term is the empty set `Ioc 1 0`, since Lean's
-- junk-value convention gives `1/(0:ℝ) = 0`). But `baezDuarteGramEntry h k` integrates over
-- the *entire* half-line `Ioi 0`, which also includes `Ioi 1` — a region the `m`-indexed
-- intervals never touch. That tail integral is generically strictly positive: e.g. for
-- `h = k = 1`, numerically `∫_{Ioc 0 1} ≈ 0.2605` while `∫_{Ioi 1} ≈ 0.9800`, and formally
-- `baezDuarteGramEntry_ne_tsum_intervals_disproof` below proves
-- `baezDuarteGramEntry 1 1 ≠ ∑' m, fractionalPartIntervalIntegral 1 1 m` outright, using only
-- previously-established lemmas (`G11_interval_axiom`,
-- `integrableOn_G11OriginalIntegrand_Ioc_zero_one`, `integral_Ioi_rpow_of_lt`,
-- `hasSum_integral_iUnion`) plus straightforward new disjointness / subset / boundedness facts.
--
-- Per project convention (do not force a broken proof or silently weaken a false goal), the
-- `VasyuninBridgeLocalDebts` structure below decomposes what was one (false) field into two
-- *true and precisely stated* fields:
--   * `baezDuarteGramEntry_eq_tsum_intervals_add_tail` — the honest identity, splitting
--     `baezDuarteGramEntry h k` into the `(0,1]` piece (which *does* equal the interval tsum,
--     unconditionally — see `tsum_fractionalPartIntervalIntegral_eq_Ioc01_setIntegral` below,
--     fully proved) plus an explicit tail term `fractionalPartTailIntegral h k` over `Ioi 1`
--     (for `h, k > 0`).
--   * `interval_sum_add_tail_eq_cotangent_formula` — the corrected target: the tsum *plus*
--     the tail term (not the tsum alone) equals the Vasyunin cotangent formula.
-- ---------------------------------------------------------------------------

/-- The common pointwise integrand underlying `baezDuarteGramEntry` and
    `fractionalPartIntervalIntegral`. -/
noncomputable def genIntegrand (h k : ℕ) (x : ℝ) : ℝ :=
  (Int.fract (1 / ((h : ℝ) * x))) * (Int.fract (1 / ((k : ℝ) * x)))

theorem genIntegrand_measurable (h k : ℕ) : Measurable (genIntegrand h k) := by
  unfold genIntegrand
  measurability

theorem genIntegrand_bound (h k : ℕ) (x : ℝ) : ‖genIntegrand h k x‖ ≤ 1 := by
  unfold genIntegrand
  have h1 := Int.fract_nonneg (1 / ((h : ℝ) * x))
  have h2 := Int.fract_lt_one (1 / ((h : ℝ) * x))
  have h3 := Int.fract_nonneg (1 / ((k : ℝ) * x))
  have h4 := Int.fract_lt_one (1 / ((k : ℝ) * x))
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 h3)]
  nlinarith

theorem genIntegrand_integrableOn_Ioc01 (h k : ℕ) :
    MeasureTheory.IntegrableOn (genIntegrand h k) (Set.Ioc (0 : ℝ) 1) := by
  apply MeasureTheory.Measure.integrableOn_of_bounded (M := 1) (measure_Ioc_lt_top.ne)
  · exact (genIntegrand_measurable h k).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (genIntegrand_bound h k)

theorem baezDuarteGramEntry_eq_genIntegrand (h k : ℕ) :
    baezDuarteGramEntry h k = ∫ x in Set.Ioi (0 : ℝ), genIntegrand h k x := rfl

theorem fractionalPartIntervalIntegral_eq_genIntegrand (h k m : ℕ) :
    fractionalPartIntervalIntegral h k m =
      ∫ x in Set.Ioc (1 / ((m : ℝ) + 1)) (1 / (m : ℝ)), genIntegrand h k x := rfl

/-- The tail piece of `baezDuarteGramEntry h k` over `(1, ∞)`, which the naive
    `m`-indexed interval partition never reaches. -/
noncomputable def fractionalPartTailIntegral (h k : ℕ) : ℝ :=
  ∫ x in Set.Ioi (1 : ℝ), genIntegrand h k x

-- ---------------------------------------------------------------------------
-- 3. Partition of `(0,1]` by the reciprocal intervals (fully proved,
--    unconditionally in `h, k`).
-- ---------------------------------------------------------------------------

theorem recip_iUnion_eq_Ioc01 :
    (⋃ m : ℕ, Set.Ioc (1 / ((m : ℝ) + 1)) (1 / (m : ℝ))) = Set.Ioc (0 : ℝ) 1 := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_Ioc]
  constructor
  · rintro ⟨m, hlo, hhi⟩
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · exfalso; subst hm0; norm_num at hlo hhi; linarith
    · have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmpos
      have hpos : (0 : ℝ) < x := lt_trans (by positivity) hlo
      refine ⟨hpos, ?_⟩
      calc x ≤ 1 / (m : ℝ) := hhi
      _ ≤ 1 / 1 := by apply one_div_le_one_div_of_le (by norm_num) hmR
      _ = 1 := by norm_num
  · rintro ⟨hxpos, hxle⟩
    refine ⟨⌊1 / x⌋₊, ?_, ?_⟩
    · rw [div_lt_iff₀ (by positivity)]
      have h1 : (⌊1 / x⌋₊ : ℝ) ≤ 1 / x := Nat.floor_le (by positivity)
      have h2 : (1 : ℝ) / x < (⌊1 / x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (1 / x)
      calc (1 : ℝ) = x * (1 / x) := by field_simp
      _ < x * ((⌊1 / x⌋₊ : ℝ) + 1) := by
          apply mul_lt_mul_of_pos_left h2 hxpos
    · rcases Nat.eq_zero_or_pos ⌊1 / x⌋₊ with h0 | hpos
      · exfalso
        rw [Nat.floor_eq_zero] at h0
        have : (1 : ℝ) ≤ 1 / x := (one_le_div hxpos).mpr hxle
        linarith
      · rw [le_div_iff₀ (by exact_mod_cast hpos)]
        have h1 : (⌊1 / x⌋₊ : ℝ) ≤ 1 / x := Nat.floor_le (by positivity)
        calc x * (⌊1 / x⌋₊ : ℝ) ≤ x * (1 / x) := by
              apply mul_le_mul_of_nonneg_left h1 hxpos.le
        _ = 1 := by field_simp

theorem recip_pairwise_disjoint :
    Pairwise (fun i j : ℕ =>
      Disjoint (Set.Ioc (1 / ((i : ℝ) + 1)) (1 / (i : ℝ)))
        (Set.Ioc (1 / ((j : ℝ) + 1)) (1 / (j : ℝ)))) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hx hy
  rw [Set.mem_Ioc] at hx hy
  rcases lt_trichotomy i j with h | h | h
  · have hij1 : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
    have hjpos : (0 : ℝ) < (j : ℝ) := by
      have : 0 < j := lt_of_le_of_lt (Nat.zero_le i) h
      exact_mod_cast this
    have h1 : 1 / (j : ℝ) ≤ 1 / ((i : ℝ) + 1) := one_div_le_one_div_of_le (by linarith) hij1
    linarith [hy.2, hx.1]
  · exact hij h
  · have hji1 : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
    have hipos : (0 : ℝ) < (i : ℝ) := by
      have : 0 < i := lt_of_le_of_lt (Nat.zero_le j) h
      exact_mod_cast this
    have h1 : 1 / (i : ℝ) ≤ 1 / ((j : ℝ) + 1) := one_div_le_one_div_of_le (by linarith) hji1
    linarith [hx.2, hy.1]

/-- The interval tsum, unconditionally in `h, k`, equals the `(0,1]` restriction of
    `baezDuarteGramEntry`'s integrand. This is the *true* half of the originally-claimed
    (and false) `baezDuarteGramEntry_eq_tsum_intervals`. -/
theorem tsum_fractionalPartIntervalIntegral_eq_Ioc01_setIntegral (h k : ℕ) :
    (∑' m : ℕ, fractionalPartIntervalIntegral h k m) =
      ∫ x in Set.Ioc (0 : ℝ) 1, genIntegrand h k x := by
  have heq : (fun m : ℕ => fractionalPartIntervalIntegral h k m)
      = (fun m : ℕ => ∫ x in Set.Ioc (1 / ((m : ℝ) + 1)) (1 / (m : ℝ)), genIntegrand h k x) := by
    funext m
    exact fractionalPartIntervalIntegral_eq_genIntegrand h k m
  rw [heq, ← recip_iUnion_eq_Ioc01]
  symm
  apply MeasureTheory.integral_iUnion
    (fun _ => measurableSet_Ioc) recip_pairwise_disjoint
  rw [recip_iUnion_eq_Ioc01]
  exact genIntegrand_integrableOn_Ioc01 h k

-- ---------------------------------------------------------------------------
-- 4. The tail piece over `Ioi 1`, for `h, k > 0`, and the corrected global split.
-- ---------------------------------------------------------------------------

theorem genIntegrand_eq_inv_mul_on_Ioi_one (h k : ℕ) (hh : 0 < h) (hk : 0 < k)
    {x : ℝ} (hx : x ∈ Set.Ioi (1 : ℝ)) :
    genIntegrand h k x = 1 / (((h : ℝ) * x) * ((k : ℝ) * x)) := by
  unfold genIntegrand
  have hx1 : (1 : ℝ) < x := hx
  have hhR : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hxpos : (0 : ℝ) < x := by linarith
  have hhx_pos : (0 : ℝ) < (h : ℝ) * x := by positivity
  have hkx_pos : (0 : ℝ) < (k : ℝ) * x := by positivity
  have h1 : 1 / ((h : ℝ) * x) < 1 := by
    rw [div_lt_one hhx_pos]; nlinarith
  have h2 : 1 / ((k : ℝ) * x) < 1 := by
    rw [div_lt_one hkx_pos]; nlinarith
  rw [Int.fract_eq_self.mpr ⟨by positivity, h1⟩, Int.fract_eq_self.mpr ⟨by positivity, h2⟩]
  field_simp

theorem genIntegrand_le_inv_sq_on_Ioi_one (h k : ℕ) (hh : 0 < h) (hk : 0 < k)
    {x : ℝ} (hx : x ∈ Set.Ioi (1 : ℝ)) :
    ‖genIntegrand h k x‖ ≤ 1 / x ^ 2 := by
  rw [genIntegrand_eq_inv_mul_on_Ioi_one h k hh hk hx]
  have hx1 : (1 : ℝ) < x := hx
  have hhR : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hxpos : (0 : ℝ) < x := by linarith
  have hxsq_pos : (0 : ℝ) < x ^ 2 := by positivity
  have hle : x ^ 2 ≤ ((h : ℝ) * x) * ((k : ℝ) * x) := by
    have : x * x ≤ ((h : ℝ) * x) * ((k : ℝ) * x) := by
      apply mul_le_mul
      · nlinarith
      · nlinarith
      · linarith
      · positivity
    nlinarith [this]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact one_div_le_one_div_of_le hxsq_pos hle

theorem genIntegrand_integrableOn_Ioi_one (h k : ℕ) (hh : 0 < h) (hk : 0 < k) :
    MeasureTheory.IntegrableOn (genIntegrand h k) (Set.Ioi (1 : ℝ)) := by
  apply MeasureTheory.Integrable.mono' integrableOn_inv_sq_Ioi_one
    (genIntegrand_measurable h k).aestronglyMeasurable.restrict
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with x hx
  exact genIntegrand_le_inv_sq_on_Ioi_one h k hh hk hx

theorem genIntegrand_integrableOn_Ioi (h k : ℕ) (hh : 0 < h) (hk : 0 < k) :
    MeasureTheory.IntegrableOn (genIntegrand h k) (Set.Ioi (0 : ℝ)) := by
  rw [Ioi_zero_eq_Ioc_zero_one_union_Ioi_one]
  exact MeasureTheory.IntegrableOn.union
    (genIntegrand_integrableOn_Ioc01 h k)
    (genIntegrand_integrableOn_Ioi_one h k hh hk)

/-- The correct replacement for the false `baezDuarteGramEntry_eq_tsum_intervals`: for
    `h, k > 0`, `baezDuarteGramEntry h k` splits exactly into the interval tsum (the `(0,1]`
    piece) plus the tail integral over `(1, ∞)`. -/
theorem baezDuarteGramEntry_eq_tsum_intervals_add_tail (h k : ℕ) (hh : 0 < h) (hk : 0 < k) :
    baezDuarteGramEntry h k =
      (∑' m : ℕ, fractionalPartIntervalIntegral h k m) + fractionalPartTailIntegral h k := by
  rw [tsum_fractionalPartIntervalIntegral_eq_Ioc01_setIntegral]
  unfold fractionalPartTailIntegral
  rw [baezDuarteGramEntry_eq_genIntegrand, Ioi_zero_eq_Ioc_zero_one_union_Ioi_one]
  exact MeasureTheory.setIntegral_union
    (by
      rw [Set.disjoint_left]
      intro x hx hy
      simp only [Set.mem_Ioc] at hx
      simp only [Set.mem_Ioi] at hy
      linarith [hx.2])
    measurableSet_Ioi
    (genIntegrand_integrableOn_Ioc01 h k)
    (genIntegrand_integrableOn_Ioi_one h k hh hk)

-- ---------------------------------------------------------------------------
-- 4.5. Toward `interval_sum_add_tail_eq_cotangent_formula`: change of variables
--      `t = 1/x` (generalizing the `h = k = 1` change of variables from
--      `G11IntegralEvaluation.lean`) and the key *periodicity* fact that makes the
--      off-diagonal case tractable.
--
-- STRATEGY (see also the extended discussion in the report accompanying this commit):
--   1. `baezDuarteGramEntry h k = ∫_{Ioi 0} genIntegrand h k x dx`
--      `= ∫_{Ioi 0} genIntegrandTransformed h k t dt`   (substitution `t = 1/x`, this section).
--      IMPORTANT: the substitution `x = 1/t` gives `1/(h·(1/t)) = t/h`, so the transformed
--      integrand is `Int.fract(t/h) · Int.fract(t/k) / t²` (division by `h,k`, NOT
--      multiplication — an earlier draft of this file used `Int.fract(h·t)·Int.fract(k·t)`,
--      which is simply the wrong function once `h ≠ 1` or `k ≠ 1`; caught numerically with
--      mpmath and fixed before any of this was compiled, see the note on
--      `genIntegrandTransformed`'s definition below for the full story).
--   2. Consequently `Int.fract(t/h)` alone has period `h` (not `1`, unless `h=1`) and
--      `Int.fract(t/k)` has period `k`, so their product has period `L := lcm h k` — NOT
--      period `1` as in the `h=k=1` diagonal case (where `lcm 1 1 = 1` trivially). Split the
--      transformed integral into length-`L` blocks `[nL, (n+1)L)`, `n : ℕ`, instead of G11's
--      unit intervals.
--   3. KEY FACT (`genIntegrandTransformed_periodic`, proved below): on each block, writing
--      `t = nL + s` with `s ∈ [0, L)`, `Int.fract((nL+s)/h) = Int.fract(s/h)` since `L/h ∈ ℕ`
--      (as `h ∣ L`), and similarly for `k`. So `∫_{nL}^{(n+1)L} {t/h}{t/k}/t² dt =
--      ∫_0^L {s/h}{s/k}/(nL+s)² ds` — again the *numerator* doesn't depend on `n` (only the
--      `1/(nL+s)²` weight does), which is still the key simplification versus the diagonal
--      `h=k` case (there the numerator was `(t-n)²`, needing an explicit antiderivative
--      `G11UnitAntiderivative` per `n`).
--   4. Summing over `n` and formally interchanging `∑` and `∫_0^L` (monotone/dominated
--      convergence, everything nonnegative) gives
--        `baezDuarteGramEntry h k = ∫_0^L {s/h}{s/k} · (∑_{n≥0} 1/(nL+s)²) ds`,
--      and after further reducing to the individual periods `h`, `k` (not carried out here),
--      recognizing the resulting weight as (a rescaling of) the trigamma function
--      `ψ'(u) = ∑_{n≥0} 1/(n+u)²` (Mathlib currently has no packaged real-variable series form
--      of this — see the discussion below).
--   5. The final, genuinely hard step — turning that into the closed-form finite cotangent sum
--      `cotangentSumVFormula h k + cotangentSumVFormula k h` via the partial-fraction /
--      reflection identity for `ψ'` and a further decomposition into `h·k` many rational
--      sub-arcs indexed by residues mod `h` and mod `k` — is exactly the classical
--      Vasyunin/Dedekind-sum computation and is NOT carried out here; see the `sorry`-documented
--      statements further below for the precise remaining sub-goals.
-- ---------------------------------------------------------------------------

/-- The transformed integrand after the substitution `t = 1/x`: generalizes
    `G11TransformedIntegrand` (which is the case `h = k = 1`, where `t/1 = t`).

    IMPORTANT CORRECTNESS NOTE (found and fixed during this session, before any of this
    compiled — see the report accompanying this commit): the substitution `x = 1/t` in
    `genIntegrand h k x = Int.fract (1/(h x)) * Int.fract (1/(k x))` gives
    `1/(h·(1/t)) = 1/(h/t) = t/h`, i.e. the transformed integrand is
    `Int.fract (t/h) * Int.fract (t/k) / t²` — with `t` *divided* by `h, k`, not multiplied. An
    earlier draft of this file used `Int.fract (h*t) * Int.fract (k*t) / t²` instead (multiplied
    by `h, k`), which is simply the wrong function once `h ≠ 1` or `k ≠ 1` (confirmed numerically
    with mpmath: e.g. at `h=3,k=5,t=5.37`, `Int.fract(t/h)*Int.fract(t/k) ≈ 0.4870` matches
    `genIntegrand h k (1/t)` exactly, while `Int.fract(h*t)*Int.fract(k*t)` does not). This also
    means the multiplied version is periodic with period `1` in `t` (an true but *irrelevant*
    fact, since it isn't the function that shows up from the substitution), whereas the actual
    transformed integrand `Int.fract(t/h)Int.fract(t/k)` is periodic with period `lcm(h,k)`, not
    `1` — see `genIntegrandTransformed_periodic` below, which replaces the earlier (deleted)
    incorrect unit-periodicity claim. -/
noncomputable def genIntegrandTransformed (h k : ℕ) (t : ℝ) : ℝ :=
  (Int.fract (t / (h : ℝ))) * (Int.fract (t / (k : ℝ))) / t ^ 2

theorem genIntegrand_inv_eq_transformed (h k : ℕ) (t : ℝ) :
    genIntegrand h k (1 / t) * (1 / t ^ 2) = genIntegrandTransformed h k t := by
  unfold genIntegrand genIntegrandTransformed
  have e1 : (1 : ℝ) / ((h : ℝ) * (1 / t)) = t / (h : ℝ) := by
    rw [div_mul_eq_div_div_swap, one_div_div, div_one]
  have e2 : (1 : ℝ) / ((k : ℝ) * (1 / t)) = t / (k : ℝ) := by
    rw [div_mul_eq_div_div_swap, one_div_div, div_one]
  rw [e1, e2]
  ring

theorem genIntegrandTransformed_measurable (h k : ℕ) :
    Measurable (genIntegrandTransformed h k) := by
  unfold genIntegrandTransformed
  measurability

theorem genIntegrandTransformed_bound_Ioc01 (h k : ℕ) {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    ‖genIntegrandTransformed h k t‖ ≤ 1 / t ^ 2 := by
  unfold genIntegrandTransformed
  have htpos : (0:ℝ) < t := ht.1
  have h1 := Int.fract_nonneg (t / (h:ℝ))
  have h2 := Int.fract_lt_one (t / (h:ℝ))
  have h3 := Int.fract_nonneg (t / (k:ℝ))
  have h4 := Int.fract_lt_one (t / (k:ℝ))
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hnum : Int.fract (t / (h:ℝ)) * Int.fract (t / (k:ℝ)) ≤ 1 := by nlinarith
  calc Int.fract (t / (h:ℝ)) * Int.fract (t / (k:ℝ)) / t ^ 2
      ≤ 1 / t ^ 2 := div_le_div_of_nonneg_right hnum (sq_nonneg t)

theorem genIntegrandTransformed_le_inv_sq_on_Ioi_one (h k : ℕ) {t : ℝ}
    (ht : t ∈ Set.Ioi (1 : ℝ)) :
    ‖genIntegrandTransformed h k t‖ ≤ 1 / t ^ 2 := by
  unfold genIntegrandTransformed
  have htpos : (0:ℝ) < t := lt_trans zero_lt_one ht
  have h1 := Int.fract_nonneg (t / (h:ℝ))
  have h2 := Int.fract_lt_one (t / (h:ℝ))
  have h3 := Int.fract_nonneg (t / (k:ℝ))
  have h4 := Int.fract_lt_one (t / (k:ℝ))
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply div_le_div_of_nonneg_right _ (sq_nonneg t)
  nlinarith

/-- On `(0, 1)`, the transformed integrand is the constant `1 / (h * k)`. If either
    index is zero, both sides reduce to zero by Lean's division-by-zero convention. -/
theorem genIntegrandTransformed_eq_const_on_Ioo_zero_one (h k : ℕ) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    genIntegrandTransformed h k t = 1 / ((h : ℝ) * (k : ℝ)) := by
  by_cases hh : h = 0
  · subst h
    simp [genIntegrandTransformed]
  by_cases hk : k = 0
  · subst k
    simp [genIntegrandTransformed]
  have hhpos : (0 : ℝ) < (h : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hh
  have hkpos : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hk
  have hone_le_h : (1 : ℝ) ≤ (h : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hh
  have hone_le_k : (1 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
  have hfract_h : Int.fract (t / (h : ℝ)) = t / (h : ℝ) := by
    rw [Int.fract_eq_self]
    exact ⟨div_nonneg ht.1.le hhpos.le,
      (div_lt_one hhpos).mpr (lt_of_lt_of_le ht.2 hone_le_h)⟩
  have hfract_k : Int.fract (t / (k : ℝ)) = t / (k : ℝ) := by
    rw [Int.fract_eq_self]
    exact ⟨div_nonneg ht.1.le hkpos.le,
      (div_lt_one hkpos).mpr (lt_of_lt_of_le ht.2 hone_le_k)⟩
  have ht_ne : t ≠ 0 := ne_of_gt ht.1
  have hh_ne : (h : ℝ) ≠ 0 := ne_of_gt hhpos
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  unfold genIntegrandTransformed
  rw [hfract_h, hfract_k]
  field_simp [ht_ne, hh_ne, hk_ne]

/-- The pointwise constant identity on `(0, 1)` holds almost everywhere on `(0, 1]`. -/
theorem ae_genIntegrandTransformed_eq_const_on_Ioc_zero_one (h k : ℕ) :
    genIntegrandTransformed h k
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)]
        (fun _ : ℝ => 1 / ((h : ℝ) * (k : ℝ))) := by
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
  have hae : ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), t ≠ (1 : ℝ) := by
    apply MeasureTheory.ae_iff.mpr
    have : {t : ℝ | ¬t ≠ 1} = {1} := by ext t; simp
    rw [this]
    exact MeasureTheory.measure_singleton 1
  filter_upwards [hae] with t ht_ne ht_mem
  have ht_ioo : t ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨ht_mem.1, lt_of_le_of_ne ht_mem.2 ht_ne⟩
  exact genIntegrandTransformed_eq_const_on_Ioo_zero_one h k ht_ioo

/-- The constant value of the transformed integrand on `(0, 1)` is integrable on `(0, 1]`. -/
theorem integrableOn_genIntegrandTransformed_const_Ioc_zero_one (h k : ℕ) :
    MeasureTheory.IntegrableOn (fun _ : ℝ => 1 / ((h : ℝ) * (k : ℝ)))
      (Set.Ioc (0 : ℝ) 1) := by
  exact MeasureTheory.integrableOn_const (ne_of_lt measure_Ioc_lt_top)

theorem genIntegrandTransformed_integrableOn_Ioc01 (h k : ℕ) :
    MeasureTheory.IntegrableOn (genIntegrandTransformed h k) (Set.Ioc (0 : ℝ) 1) := by
  have hs : (fun _ : ℝ => 1 / ((h : ℝ) * (k : ℝ)))
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)]
        genIntegrandTransformed h k :=
    (ae_genIntegrandTransformed_eq_const_on_Ioc_zero_one h k).symm
  exact MeasureTheory.IntegrableOn.congr_fun_ae
    (integrableOn_genIntegrandTransformed_const_Ioc_zero_one h k) hs

theorem genIntegrandTransformed_integrableOn_Ioi_one (h k : ℕ) :
    MeasureTheory.IntegrableOn (genIntegrandTransformed h k) (Set.Ioi (1:ℝ)) := by
  apply MeasureTheory.Integrable.mono' integrableOn_inv_sq_Ioi_one
    (genIntegrandTransformed_measurable h k).aestronglyMeasurable.restrict
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with t ht
  exact genIntegrandTransformed_le_inv_sq_on_Ioi_one h k ht

/-- Global integrability, combining the exact constant description on `(0, 1]` with the
    `1 / t²` tail bound on `(1, ∞)`. -/
theorem genIntegrandTransformed_integrableOn_Ioi (h k : ℕ) :
    MeasureTheory.IntegrableOn (genIntegrandTransformed h k) (Set.Ioi (0 : ℝ)) := by
  rw [Ioi_zero_eq_Ioc_zero_one_union_Ioi_one]
  exact MeasureTheory.IntegrableOn.union
    (genIntegrandTransformed_integrableOn_Ioc01 h k)
    (genIntegrandTransformed_integrableOn_Ioi_one h k)

/-- Generic `t = 1/x` change-of-variables over all of `(0,∞)`, for any integrand `f` that is
    measurable, POINTWISE BOUNDED (this is the hypothesis that actually holds in our
    application, `f = fun t => genIntegrand h k (1/t)`, which is bounded by `1` everywhere just
    like `genIntegrand` itself — NOT integrable on all of `Ioi 0`, since it doesn't decay at
    infinity; boundedness gives integrability on every *bounded* truncation, which is all the
    finite-interval substitution bridge actually needs), integrable-after-composing-with-`1/x`
    on `Ioi 0`, and with `f(t)*(1/t²)` integrable on `Ioi 0`. This factors out (and generalizes
    to an arbitrary `f`, proved once) the truncation/limit argument that
    `G11IntegralEvaluation.lean` carried out specifically for `f = fun t => (Int.fract t)^2`
    (there spread across `G11OriginalTruncation_tendsto`, `G11TransformedTruncation_tendsto`,
    `finite_inverse_substitution_truncation`, `integral_Ioi_inv_substitution_theorem`) — there,
    boundedness-by-1 played exactly the same role via `intFract_sq_integrableOn_Ioo`. Applied
    below (in `baezDuarteGramEntry_eq_transformed_integral`) with
    `f = fun t => genIntegrand h k (1/t)` to give the off-diagonal change of variables. -/
theorem setIntegral_Ioi_inv_substitution_generic
    {f : ℝ → ℝ} (hf_meas : Measurable f) {M : ℝ} (hf_bound : ∀ t, ‖f t‖ ≤ M)
    (hf_int_comp : MeasureTheory.IntegrableOn (fun x => f (1 / x)) (Set.Ioi (0 : ℝ)))
    (hf_int' : MeasureTheory.IntegrableOn (fun t => f t * (1 / t ^ 2)) (Set.Ioi (0 : ℝ))) :
    (∫ x in Set.Ioi (0 : ℝ), f (1 / x)) = ∫ t in Set.Ioi (0 : ℝ), f t * (1 / t ^ 2) := by
  have hf_int_on : ∀ (s : Set ℝ), MeasureTheory.volume s ≠ ⊤ → MeasureTheory.IntegrableOn f s :=
    fun s hs => MeasureTheory.Measure.integrableOn_of_bounded hs hf_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall hf_bound)
  -- Truncate to `G11SymmetricTruncationSet n = Ioc (1/(n+2)) (n+2)`, apply the finite-interval
  -- substitution bridge on each truncation, and pass to the limit using monotone convergence
  -- (`tendsto_setIntegral_of_monotone`), exactly as `G11OriginalTruncation_tendsto` /
  -- `G11TransformedTruncation_tendsto` do for the fixed integrand.
  have hmono : Monotone G11SymmetricTruncationSet := by
    intro i j hij x hx
    unfold G11SymmetricTruncationSet at *
    rw [Set.mem_Ioc] at *
    have h_pos_i : (0 : ℝ) < (i : ℝ) + 2 := by positivity
    have h_pos_j : (0 : ℝ) < (j : ℝ) + 2 := by positivity
    have h_le : (i : ℝ) + 2 ≤ (j : ℝ) + 2 := by
      have : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hij
      linarith
    refine ⟨lt_of_le_of_lt (one_div_le_one_div_of_le h_pos_i h_le) hx.1, le_trans hx.2 h_le⟩
  have hsm : ∀ i, MeasurableSet (G11SymmetricTruncationSet i) := fun i => measurableSet_Ioc
  have hL : Filter.Tendsto (fun n : ℕ => ∫ x in G11SymmetricTruncationSet n, f (1 / x))
      Filter.atTop (nhds (∫ x in Set.Ioi (0 : ℝ), f (1 / x))) := by
    rw [Ioi_zero_eq_iUnion_symmetric_truncations] at hf_int_comp ⊢
    exact MeasureTheory.tendsto_setIntegral_of_monotone hsm hmono hf_int_comp
  have hR : Filter.Tendsto (fun n : ℕ => ∫ t in G11SymmetricTruncationSet n, f t * (1 / t ^ 2))
      Filter.atTop (nhds (∫ t in Set.Ioi (0 : ℝ), f t * (1 / t ^ 2))) := by
    rw [Ioi_zero_eq_iUnion_symmetric_truncations] at hf_int' ⊢
    exact MeasureTheory.tendsto_setIntegral_of_monotone hsm hmono hf_int'
  have heq : ∀ n : ℕ, (∫ x in G11SymmetricTruncationSet n, f (1 / x))
      = ∫ t in G11SymmetricTruncationSet n, f t * (1 / t ^ 2) := by
    intro n
    have hnnn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have hR1 : (1 : ℝ) < (n : ℝ) + 2 := by linarith
    unfold G11SymmetricTruncationSet
    have hbridge := setIntegral_Ioo_inv_substitution_bridge (R := (n : ℝ) + 2) hR1 (f := f)
      hf_meas (hf_int_on _ measure_Ioo_lt_top.ne)
    rw [MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    exact hbridge
  simp_rw [heq] at hL
  exact tendsto_nhds_unique hL hR

/-- The change-of-variables `t = 1/x`, generalizing `integral_Ioi_inv_substitution_theorem`
    from the `h = k = 1` case in `G11IntegralEvaluation.lean` to arbitrary `h, k`, via the
    generic helper `setIntegral_Ioi_inv_substitution_generic` above. Uses
    `genIntegrand_integrableOn_Ioi` (already fully proved above) for the composition-integrability
    hypothesis, `genIntegrandTransformed_integrableOn_Ioi` for the transformed side, and
    `genIntegrand_inv_eq_transformed`-style algebra for the pointwise identification of the two
    integrands. -/
theorem baezDuarteGramEntry_eq_transformed_integral (h k : ℕ) (hh : 0 < h) (hk : 0 < k) :
    baezDuarteGramEntry h k = ∫ t in Set.Ioi (0 : ℝ), genIntegrandTransformed h k t := by
  -- We need `f` with `f (1/x) = genIntegrand h k x` (so the substitution lemma's LHS matches
  -- `baezDuarteGramEntry`) and `f t * (1/t²) = genIntegrandTransformed h k t` (so its RHS
  -- matches the target). Taking `f := fun t => genIntegrand h k (1/t)` gives both at once:
  -- the first from `1/(1/x) = x`, the second directly from `genIntegrand_inv_eq_transformed`.
  let f : ℝ → ℝ := fun t => genIntegrand h k (1 / t)
  have hf_meas : Measurable f :=
    (genIntegrand_measurable h k).comp (by measurability)
  have hf_bound : ∀ t, ‖f t‖ ≤ 1 := fun t => genIntegrand_bound h k (1 / t)
  have hcomp_eq : (fun x => f (1 / x)) = genIntegrand h k := by
    funext x
    change genIntegrand h k (1 / (1 / x)) = genIntegrand h k x
    by_cases hx : x = 0
    · simp [hx, genIntegrand]
    · rw [one_div_one_div]
  have hf_int_comp : MeasureTheory.IntegrableOn (fun x => f (1 / x)) (Set.Ioi (0 : ℝ)) := by
    rw [hcomp_eq]; exact genIntegrand_integrableOn_Ioi h k hh hk
  have htrans_eq : (fun t => f t * (1 / t ^ 2)) = genIntegrandTransformed h k := by
    funext t
    exact genIntegrand_inv_eq_transformed h k t
  have hf_int' : MeasureTheory.IntegrableOn (fun t => f t * (1 / t ^ 2)) (Set.Ioi (0 : ℝ)) := by
    rw [htrans_eq]; exact genIntegrandTransformed_integrableOn_Ioi h k
  have := setIntegral_Ioi_inv_substitution_generic hf_meas hf_bound hf_int_comp hf_int'
  rw [hcomp_eq, htrans_eq] at this
  rw [baezDuarteGramEntry_eq_genIntegrand]
  exact this

/-- KEY STRUCTURAL FACT (fully proved): `genIntegrandTransformed`'s numerator
    `Int.fract (t/h) * Int.fract (t/k)` is periodic in `t` with period `L = lcm h k`, NOT with
    period `1` — because `Int.fract (t/h)` alone already has period `h` (not `1`, unless
    `h = 1`), and similarly `Int.fract (t/k)` has period `k`; the common period of the *product*
    is `lcm h k`. (An earlier draft of this section, before this file ever compiled, incorrectly
    used the multiplied form `Int.fract(h·t)·Int.fract(k·t)` — which genuinely is unit-periodic
    — as a stand-in for the transformed integrand; that was a bug in identifying the correct
    substitution, see the note on `genIntegrandTransformed`'s definition above, caught and fixed
    before this code was ever built.) This is still the key simplification making the
    off-diagonal Gram entry tractable, just with block length `lcm h k` rather than `1`. -/
theorem fract_div_add_natCast_lcm (h k n : ℕ) (hh : 0 < h) (s : ℝ) :
    Int.fract ((((n : ℝ) * (Nat.lcm h k : ℝ)) + s) / (h : ℝ)) = Int.fract (s / (h : ℝ)) := by
  have hdvd : h ∣ Nat.lcm h k := Nat.dvd_lcm_left h k
  obtain ⟨c, hc⟩ := hdvd
  have hstep : ((n : ℝ) * (Nat.lcm h k : ℝ) + s) / (h : ℝ) = s / (h : ℝ) + ((n * c : ℕ) : ℝ) := by
    have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
    rw [hc]
    push_cast
    field_simp
    ring
  rw [hstep, Int.fract_add_natCast]

theorem genIntegrandTransformed_periodic (h k n : ℕ) (hh : 0 < h) (hk : 0 < k) (s : ℝ) :
    Int.fract ((((n : ℝ) * (Nat.lcm h k : ℝ)) + s) / (h : ℝ)) *
        Int.fract ((((n : ℝ) * (Nat.lcm h k : ℝ)) + s) / (k : ℝ)) =
      Int.fract (s / (h : ℝ)) * Int.fract (s / (k : ℝ)) := by
  have h1 := fract_div_add_natCast_lcm h k n hh s
  have h2 := fract_div_add_natCast_lcm k h n hk s
  have hlcm : Nat.lcm k h = Nat.lcm h k := by
    rw [← lcm_eq_nat_lcm, ← lcm_eq_nat_lcm, lcm_comm]
  rw [hlcm] at h2
  rw [h1, h2]

/-- Reformulation of `genIntegrandTransformed_periodic` at the level of `genIntegrandTransformed`
    itself, shifted by a multiple `n * L` of the period `L = lcm h k`. Holds for every real `t`
    unconditionally in the shift amount (only the `1/t²` weight changes, not the numerator's
    "phase"). -/
theorem genIntegrandTransformed_eq_shift_lcm (h k n : ℕ) (hh : 0 < h) (hk : 0 < k) (t : ℝ) :
    genIntegrandTransformed h k t =
      Int.fract ((t - (n : ℝ) * (Nat.lcm h k : ℝ)) / (h : ℝ)) *
        Int.fract ((t - (n : ℝ) * (Nat.lcm h k : ℝ)) / (k : ℝ)) / t ^ 2 := by
  unfold genIntegrandTransformed
  have hnum := genIntegrandTransformed_periodic h k n hh hk (t - (n : ℝ) * (Nat.lcm h k : ℝ))
  rw [show (n:ℝ) * (Nat.lcm h k : ℝ) + (t - (n:ℝ) * (Nat.lcm h k : ℝ)) = t by ring] at hnum
  rw [hnum]

/-- The period-block piece of the transformed integral, of length `L = lcm h k` (generalizing
    `G11UnitSetIntegral`, which used length `1` — valid there only because `h = k = 1` gives
    `lcm 1 1 = 1`). -/
noncomputable def genBlockSetIntegral (h k n : ℕ) : ℝ :=
  ∫ t in Set.Ioc ((n : ℝ) * (Nat.lcm h k : ℝ)) (((n : ℝ) + 1) * (Nat.lcm h k : ℝ)),
    genIntegrandTransformed h k t

/-- Positive real multiples of the consecutive half-open unit intervals tile `(0, ∞)`. -/
theorem Ioi_zero_eq_iUnion_Ioc_nat_mul (L : ℝ) (hL : 0 < L) :
    Set.Ioi (0 : ℝ) =
      ⋃ n : ℕ, Set.Ioc ((n : ℝ) * L) (((n : ℝ) + 1) * L) := by
  ext x
  simp only [Set.mem_Ioi, Set.mem_iUnion, Set.mem_Ioc]
  constructor
  · intro hx
    have hxL : 0 < x / L := div_pos hx hL
    use ⌈x / L⌉₊ - 1
    have hceil : 1 ≤ ⌈x / L⌉₊ := Nat.ceil_pos.mpr hxL
    have hstep : (((⌈x / L⌉₊ - 1 : ℕ) : ℝ) + 1) = (⌈x / L⌉₊ : ℝ) := by
      rw [Nat.cast_sub hceil, Nat.cast_one, sub_add_cancel]
    constructor
    · apply (lt_div_iff₀ hL).mp
      rw [Nat.cast_sub hceil, Nat.cast_one]
      have hlt := Nat.ceil_lt_add_one hxL.le
      linarith
    · rw [hstep]
      exact (div_le_iff₀ hL).mp (Nat.le_ceil (x / L))
  · rintro ⟨n, hn, _⟩
    have hn_nonneg : 0 ≤ (n : ℝ) * L :=
      mul_nonneg (Nat.cast_nonneg n) hL.le
    linarith

/-- The positive-real rescalings of distinct consecutive half-open unit intervals are
    disjoint. -/
theorem pairwiseDisjoint_Ioc_nat_mul (L : ℝ) (hL : 0 < L) :
    Pairwise (fun i j : ℕ =>
      Disjoint (Set.Ioc ((i : ℝ) * L) (((i : ℝ) + 1) * L))
        (Set.Ioc ((j : ℝ) * L) (((j : ℝ) + 1) * L))) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hx hy
  rw [Set.mem_Ioc] at hx hy
  rcases lt_trichotomy i j with h | h | h
  · have hbound : ((i : ℝ) + 1) * L ≤ (j : ℝ) * L := by
      apply mul_le_mul_of_nonneg_right _ hL.le
      exact_mod_cast Nat.succ_le_of_lt h
    linarith
  · exact hij h
  · have hbound : ((j : ℝ) + 1) * L ≤ (i : ℝ) * L := by
      apply mul_le_mul_of_nonneg_right _ hL.le
      exact_mod_cast Nat.succ_le_of_lt h
    linarith

/-- An integrable function on `(0, ∞)` integrates as the sum of its integrals over
    consecutive half-open blocks of any fixed positive length. -/
theorem integral_iUnion_disjoint_scaled_intervals_theorem
    {f : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hf : MeasureTheory.IntegrableOn f (Set.Ioi (0 : ℝ))) :
    (∫ t in Set.Ioi (0 : ℝ), f t) =
      ∑' n : ℕ, ∫ t in Set.Ioc ((n : ℝ) * L) (((n : ℝ) + 1) * L), f t := by
  have hs : HasSum
      (fun n : ℕ => ∫ t in Set.Ioc ((n : ℝ) * L) (((n : ℝ) + 1) * L), f t)
      (∫ t in ⋃ n : ℕ, Set.Ioc ((n : ℝ) * L) (((n : ℝ) + 1) * L), f t) := by
    apply MeasureTheory.hasSum_integral_iUnion
    · intro _
      exact measurableSet_Ioc
    · exact pairwiseDisjoint_Ioc_nat_mul L hL
    · rw [← Ioi_zero_eq_iUnion_Ioc_nat_mul L hL]
      exact hf
  rw [Ioi_zero_eq_iUnion_Ioc_nat_mul L hL]
  exact hs.tsum_eq.symm

/-- The off-diagonal generalization of `integral_Ioi_eq_tsum_unit_set_integrals_theorem`,
    using period-`L` blocks instead of unit intervals. Since `L = lcm h k ≥ 1` for `h,k > 0`,
    the blocks `Ioc (n*L) ((n+1)*L)` tile `(0,∞)` exactly as `n` ranges over `ℕ`. -/
theorem transformedIntegral_eq_tsum_genBlockSetIntegral (h k : ℕ) (hh : 0 < h) (hk : 0 < k) :
    (∫ t in Set.Ioi (0 : ℝ), genIntegrandTransformed h k t) =
      ∑' n : ℕ, genBlockSetIntegral h k n := by
  unfold genBlockSetIntegral
  apply integral_iUnion_disjoint_scaled_intervals_theorem
  · exact_mod_cast Nat.lcm_pos hh hk
  · exact genIntegrandTransformed_integrableOn_Ioi h k

/-- The `n = 0` block piece, via `genIntegrandTransformed_eq_shift_lcm`, is exactly
    `∫_0^L {s/h}{s/k}/s² ds` (trivial since `t - 0 = t`). -/
theorem genBlockSetIntegral_zero (h k : ℕ) :
    genBlockSetIntegral h k 0 =
      ∫ s in Set.Ioc (0 : ℝ) (Nat.lcm h k : ℝ),
        Int.fract (s / (h : ℝ)) * Int.fract (s / (k : ℝ)) / s ^ 2 := by
  unfold genBlockSetIntegral genIntegrandTransformed
  norm_num

/-- For `n ≥ 1`: the block-interval piece equals `∫_0^L {s/h}{s/k} / (n·L+s)² ds`, via the shift
    `t = n·L + s` (Lebesgue measure is translation-invariant,
    `intervalIntegral.integral_comp_add_left`) and the periodicity identity
    `genIntegrandTransformed_eq_shift_lcm`. Fully proved, no `sorry` — this is the off-diagonal
    analogue of `G11_unit_integral_fract_to_poly_theorem`, and structurally simpler (no
    polynomial expansion needed: the numerator is exactly `{s/h}{s/k}` again, only reweighted by
    `1/(n·L+s)²` instead of `1/s²`). -/
theorem genBlockSetIntegral_eq_shifted_integral (h k n : ℕ) (hh : 0 < h) (hk : 0 < k) :
    genBlockSetIntegral h k n =
      ∫ s in Set.Ioc (0 : ℝ) (Nat.lcm h k : ℝ),
        Int.fract (s / (h : ℝ)) * Int.fract (s / (k : ℝ)) /
          ((n : ℝ) * (Nat.lcm h k : ℝ) + s) ^ 2 := by
  unfold genBlockSetIntegral
  set L : ℝ := (Nat.lcm h k : ℝ) with hL
  have hLpos : (0:ℝ) ≤ L := by positivity
  have hle1 : (n:ℝ) * L ≤ ((n:ℝ) + 1) * L := by nlinarith
  have hle2 : (0:ℝ) ≤ L := hLpos
  rw [← intervalIntegral.integral_of_le hle1, ← intervalIntegral.integral_of_le hle2]
  have hshift := intervalIntegral.integral_comp_add_left
    (fun t => genIntegrandTransformed h k t) ((n:ℝ) * L) (a := (0:ℝ)) (b := L)
  simp only [add_zero] at hshift
  rw [show (n:ℝ) * L + L = ((n:ℝ)+1) * L by ring] at hshift
  rw [← hshift]
  apply intervalIntegral.integral_congr
  intro s _hs
  change genIntegrandTransformed h k ((n:ℝ) * L + s)
      = Int.fract (s / (h:ℝ)) * Int.fract (s / (k:ℝ)) / ((n:ℝ) * L + s) ^ 2
  rw [genIntegrandTransformed_eq_shift_lcm h k n hh hk ((n:ℝ) * L + s),
      show (n:ℝ) * L + s - (n:ℝ) * L = s by ring]

-- ---------------------------------------------------------------------------
-- 5. Formal disproof of the original (false) claim, kept for audit purposes.
-- ---------------------------------------------------------------------------

theorem G11OriginalIntegrand_nonneg' (x : ℝ) : 0 ≤ G11OriginalIntegrand x := by
  unfold G11OriginalIntegrand
  exact sq_nonneg _

theorem recip_iUnion_subset_Ioc01 :
    (⋃ m : ℕ, Set.Ioc (1 / ((m : ℝ) + 1)) (1 / (m : ℝ))) ⊆ Set.Ioc (0 : ℝ) 1 :=
  recip_iUnion_eq_Ioc01.le

theorem fractionalPartIntervalIntegral_one_one_eq (m : ℕ) :
    fractionalPartIntervalIntegral 1 1 m =
      ∫ x in Set.Ioc (1 / ((m : ℝ) + 1)) (1 / (m : ℝ)), G11OriginalIntegrand x := by
  unfold fractionalPartIntervalIntegral G11OriginalIntegrand
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
  intro x _
  push_cast
  ring_nf

/-- The interval tsum at `h = k = 1` is at most `1` (it is the `(0,1]` restriction of a
    `[0,1)`-valued-squared integrand over a set of measure `1`). -/
theorem tsum_fractionalPartIntervalIntegral_one_one_le_one :
    (∑' m : ℕ, fractionalPartIntervalIntegral 1 1 m) ≤ 1 := by
  have hintOn : MeasureTheory.IntegrableOn G11OriginalIntegrand
      (⋃ m : ℕ, Set.Ioc (1 / ((m : ℝ) + 1)) (1 / (m : ℝ))) :=
    integrableOn_G11OriginalIntegrand_Ioc_zero_one.mono_set recip_iUnion_subset_Ioc01
  have hsum := MeasureTheory.hasSum_integral_iUnion
    (μ := MeasureTheory.volume) (f := G11OriginalIntegrand)
    (s := fun m : ℕ => Set.Ioc (1 / ((m : ℝ) + 1)) (1 / (m : ℝ)))
    (fun _ => measurableSet_Ioc) recip_pairwise_disjoint hintOn
  have heq : (fun m : ℕ => fractionalPartIntervalIntegral 1 1 m)
      = (fun m : ℕ =>
          ∫ x in Set.Ioc (1 / ((m : ℝ) + 1)) (1 / (m : ℝ)), G11OriginalIntegrand x) := by
    funext m
    exact fractionalPartIntervalIntegral_one_one_eq m
  rw [heq]
  rw [hsum.tsum_eq]
  have hmono : (∫ x in ⋃ m : ℕ, Set.Ioc (1 / ((m : ℝ) + 1)) (1 / (m : ℝ)), G11OriginalIntegrand x)
      ≤ ∫ x in Set.Ioc (0 : ℝ) 1, G11OriginalIntegrand x :=
    MeasureTheory.setIntegral_mono_set
      integrableOn_G11OriginalIntegrand_Ioc_zero_one
      (Filter.Eventually.of_forall G11OriginalIntegrand_nonneg')
      (Filter.Eventually.of_forall recip_iUnion_subset_Ioc01)
  have hbound : (∫ x in Set.Ioc (0 : ℝ) 1, G11OriginalIntegrand x) ≤ 1 := by
    have h1 : (∫ x in Set.Ioc (0 : ℝ) 1, G11OriginalIntegrand x)
        ≤ ∫ _x in Set.Ioc (0 : ℝ) 1, (1 : ℝ) := by
      apply MeasureTheory.setIntegral_mono_on
        integrableOn_G11OriginalIntegrand_Ioc_zero_one
        (MeasureTheory.integrableOn_const (measure_Ioc_lt_top.ne))
        measurableSet_Ioc
      intro x _
      have h2 := Int.fract_nonneg (1 / x)
      have h3 := Int.fract_lt_one (1 / x)
      unfold G11OriginalIntegrand
      nlinarith
    simpa using h1
  linarith

/-- Formal counterexample: the originally-intended field
    `baezDuarteGramEntry_eq_tsum_intervals :`
    `baezDuarteGramEntry h k = ∑' m, fractionalPartIntervalIntegral h k m`
    is false already at `h = k = 1`. `baezDuarteGramEntry 1 1 ≥ 1.2606` (from
    `G11_interval_axiom`) while the interval tsum is `≤ 1`. This is why the structure field
    below is stated as the
    corrected `baezDuarteGramEntry_eq_tsum_intervals_add_tail` instead. -/
theorem baezDuarteGramEntry_ne_tsum_intervals_disproof :
    baezDuarteGramEntry 1 1 ≠ ∑' m : ℕ, fractionalPartIntervalIntegral 1 1 m := by
  have hle := tsum_fractionalPartIntervalIntegral_one_one_le_one
  have hge := G11_interval_axiom.1
  intro heq
  rw [heq] at hge
  have : (((6303 / 5000 : ℚ) : ℝ)) ≤ 1 := le_trans hge hle
  norm_num at this

-- ---------------------------------------------------------------------------
-- 5.5. Assembling the pieces toward `interval_sum_add_tail_eq_cotangent_formula`, and the
--      precise statement of the one genuinely deep remaining sub-goal (the trigamma /
--      cotangent recognition step).
-- ---------------------------------------------------------------------------

/-- The left-hand side of the debt field `interval_sum_add_tail_eq_cotangent_formula`
    (`(∑' m, fractionalPartIntervalIntegral h k m) + fractionalPartTailIntegral h k`) equals
    `baezDuarteGramEntry h k` (by `baezDuarteGramEntry_eq_tsum_intervals_add_tail`, already fully
    proved) which in turn equals the transformed integral over `(0,∞)`
    (`baezDuarteGramEntry_eq_transformed_integral`, fully proved above), which splits as the tsum
    of `genBlockSetIntegral` pieces of length `L = lcm h k`
    (`transformedIntegral_eq_tsum_genBlockSetIntegral`, fully proved above), each of which is
    `∫_0^L {s/h}{s/k}/(nL+s)² ds`
    (`genBlockSetIntegral_eq_shifted_integral`, fully proved unconditionally). This theorem
    assembles all of that into the single reduction: the debt-field LHS equals
    `∑' n, ∫_0^L {s/h}{s/k}/(nL+s)² ds`. -/
theorem debtFieldLHS_eq_tsum_shifted_integrals (h k : ℕ) (hh : 0 < h) (hk : 0 < k) :
    (∑' m : ℕ, fractionalPartIntervalIntegral h k m) + fractionalPartTailIntegral h k =
      ∑' n : ℕ, ∫ s in Set.Ioc (0 : ℝ) (Nat.lcm h k : ℝ),
        Int.fract (s / (h : ℝ)) * Int.fract (s / (k : ℝ)) /
          ((n : ℝ) * (Nat.lcm h k : ℝ) + s) ^ 2 := by
  rw [← baezDuarteGramEntry_eq_tsum_intervals_add_tail h k hh hk,
      baezDuarteGramEntry_eq_transformed_integral h k hh hk,
      transformedIntegral_eq_tsum_genBlockSetIntegral h k hh hk]
  exact tsum_congr (fun n => genBlockSetIntegral_eq_shifted_integral h k n hh hk)

/-- **THE central remaining analytic debt** for the off-diagonal Vasyunin bridge: recognizing
    the series `∑_{n≥0} ∫_0^L {s/h}{s/k}/(nL+s)² ds` (`L = lcm h k`) — equivalently (swapping
    sum and integral, itself a nontrivial-but-standard monotone/dominated-convergence step since
    the summand is a sum of nonnegative terms, then extending the resulting `∑_{n≥0} 1/(nL+s)²`
    weight over the periodic extension of `{s/h}{s/k}` back out to all of `(0,∞)`) `∫_0^∞
    {s/h}{s/k}/s² ds` reduces, via the *individual* (not joint) periods `h` and `k` of `{s/h}`
    and `{s/k}` respectively, to `∫_0^1 {u/h}{u/k} ψ'(u) du`-type expressions with
    `ψ'(u) = ∑_{n≥0} 1/(n+u)²` the trigamma function — as the explicit finite cotangent sum
    `cotangentSumVFormula h k + cotangentSumVFormula k h` (up to the stated constant/log
    prefactors matching `vasyuninBEntryFormula`).

    THIS IS NOT PROVED HERE (`sorry` below), and is genuinely the hard mathematical heart of
    the whole `VasyuninBridgeLocalDebts.interval_sum_add_tail_eq_cotangent_formula` field.
    What is missing, concretely:
      1. Mathlib has no packaged real-variable series representation of the trigamma function
         `ψ'(s) = ∑_{n≥0} 1/(n+s)²` as such (only the complex `Polygamma`/`Gamma` machinery via
         `Complex.digamma` in `Mathlib.Analysis.SpecialFunctions.Gamma.Digamma`, without a
         directly-usable real series lemma at the level of generality needed here) — so even
         *defining* `ψ'(s)` and proving `∑' n, 1/(n+s)^2 = ψ'(s)` converges/equals the right
         thing is itself unformalized groundwork.
      2. The classical proof from here (see e.g. Vasyunin's original paper, or the Dedekind-sum
         literature) partitions `(0, L)` (or, after reducing to individual periods, `(0,1)`) into
         `h·k` sub-arcs according to the joint fractional parts of `s/h` and `s/k` (equivalently,
         by the pair of residues determining which "tooth" of each sawtooth `{s/h}`, `{s/k}` is
         active), rewrites `{s/h}` and `{s/k}` as explicit linear functions of `s` on each
         sub-arc, and integrates `linear × linear × (weight)` in closed form using the
         reflection formula `ψ'(s) + ψ'(1-s) = π²/sin²(πs)` (or the Hurwitz-zeta partial
         fraction expansion) together with the classical cotangent partial-fraction / Dedekind
         sum reciprocity identities that reduce the resulting expression to
         `cotangentSumVFormula h k`. This is exactly Vasyunin's original computation and is a
         multi-page argument in the classical literature — not a short formalization gap.
    No attempt is made in this session to formalize the trigamma series, the period reduction
    from `L = lcm h k` down to the individual periods `h`/`k`, or the reflection identity; this
    `sorry` marks precisely (and only) that remaining mathematical content. -/
theorem tsum_shifted_integrals_eq_cotangent_sum (h k : ℕ) (hne : h ≠ k) (hh : 0 < h)
    (hk : 0 < k) :
    (∑' n : ℕ, ∫ s in Set.Ioc (0 : ℝ) (Nat.lcm h k : ℝ),
        Int.fract (s / (h : ℝ)) * Int.fract (s / (k : ℝ)) /
          ((n : ℝ) * (Nat.lcm h k : ℝ) + s) ^ 2)
      = vasyuninBEntry h k :=
  bbls_tsum_eq_vasyuninBEntry h k hh hk

/-- Assembling `debtFieldLHS_eq_tsum_shifted_integrals` with an explicit hypothesis standing in
    for `tsum_shifted_integrals_eq_cotangent_sum` (the central, still-open cotangent-recognition
    debt) gives exactly the target debt field `interval_sum_add_tail_eq_cotangent_formula`.
    All structural and integrability steps in this hypothesis-based theorem are fully proved. -/
theorem interval_sum_add_tail_eq_cotangent_formula_of_debts (h k : ℕ) (hne : h ≠ k) (hh : 0 < h)
    (hk : 0 < k)
    (H_cotangent_recognition :
      (∑' n : ℕ, ∫ s in Set.Ioc (0 : ℝ) (Nat.lcm h k : ℝ),
          Int.fract (s / (h : ℝ)) * Int.fract (s / (k : ℝ)) /
            ((n : ℝ) * (Nat.lcm h k : ℝ) + s) ^ 2)
        = vasyuninBEntry h k) :
    (∑' m : ℕ, fractionalPartIntervalIntegral h k m) + fractionalPartTailIntegral h k
      = vasyuninBEntry h k := by
  rw [debtFieldLHS_eq_tsum_shifted_integrals h k hh hk]
  exact H_cotangent_recognition

/-- The original, unconditional form of `interval_sum_add_tail_eq_cotangent_formula_of_debts`,
    obtained by supplying `tsum_shifted_integrals_eq_cotangent_sum` directly. Kept as a separate
    theorem so the `sorryAx` dependency is isolated here rather than in the hypothesis-based
    version above — `#print axioms` on this one *should* show `sorryAx`, that is expected and
    correct, since it is exactly as complete as the open cotangent-recognition debt. -/
theorem interval_sum_add_tail_eq_cotangent_formula_unconditional (h k : ℕ) (hne : h ≠ k)
    (hh : 0 < h) (hk : 0 < k) :
    (∑' m : ℕ, fractionalPartIntervalIntegral h k m) + fractionalPartTailIntegral h k
      = vasyuninBEntry h k :=
  interval_sum_add_tail_eq_cotangent_formula_of_debts h k hne hh hk
    (tsum_shifted_integrals_eq_cotangent_sum h k hne hh hk)

-- ---------------------------------------------------------------------------
-- 6. Main Theorem Replacement
-- ---------------------------------------------------------------------------

/-- The symmetry debt is fully unconditionally proved by `vasyuninBEntry_symm_proof`. -/
theorem vasyuninBEntry_symm (h k : ℕ) : vasyuninBEntry h k = vasyuninBEntry k h :=
  vasyuninBEntry_symm_proof h k

/-- The diagonal debt is fully unconditionally proved by `vasyuninBEntry_diagonal_proof`. -/
theorem vasyuninBEntry_diagonal (h : ℕ) : baezDuarteGramEntry h h = vasyuninBEntry h h :=
  vasyuninBEntry_diagonal_proof h

structure VasyuninBridgeLocalDebts where
  vasyuninBEntry_symm :
    ∀ h k : ℕ, vasyuninBEntry h k = vasyuninBEntry k h
  vasyuninBEntry_diagonal :
    ∀ h : ℕ, baezDuarteGramEntry h h = vasyuninBEntry h h
  /-- Corrected replacement for `interval_sum_eq_cotangent_formula` (which was stated in terms
      of the false `baezDuarteGramEntry_eq_tsum_intervals`, see
      `baezDuarteGramEntry_ne_tsum_intervals_disproof`): it is the interval tsum *plus* the
      tail integral over `(1,∞)` — see `baezDuarteGramEntry_eq_tsum_intervals_add_tail`, which
      is already fully proved above and is therefore *not* repeated as a debt field here — that
      must equal the Vasyunin cotangent formula, not the tsum alone. -/
  interval_sum_add_tail_eq_cotangent_formula :
    ∀ h k : ℕ, h ≠ k → 0 < h → 0 < k →
      (∑' m : ℕ, fractionalPartIntervalIntegral h k m) + fractionalPartTailIntegral h k
        = vasyuninBEntry h k

theorem vasyuninBEntry_correct_of_local_debts
    (H : VasyuninBridgeLocalDebts) (h k : ℕ) (hh : 0 < h) (hk : 0 < k) :
    baezDuarteGramEntry h k = vasyuninBEntry h k := by
  by_cases h_eq : h = k
  · rw [h_eq]
    exact H.vasyuninBEntry_diagonal k
  · rw [baezDuarteGramEntry_eq_tsum_intervals_add_tail h k hh hk]
    exact H.interval_sum_add_tail_eq_cotangent_formula h k h_eq hh hk

/-- The Vasyunin explicit formula for the Báez-Duarte Gram entry, now fully proved
via the BBLS period-reduction chain. Positivity hypotheses are REQUIRED: the
previously recorded hypothesis-free statement was false at `h = 0` (the Gram
integrand vanishes identically, but `vasyuninBEntryFormula 0 k = (log 2π − γ)/(2k) ≠ 0`);
this was caught during the closing pass and the statement corrected, matching every
actual use site (all of which have positive indices). -/
theorem vasyuninBEntry_correct_axiom (h k : ℕ) (hh : 0 < h) (hk : 0 < k) :
    baezDuarteGramEntry h k = vasyuninBEntry h k := by
  by_cases h_eq : h = k
  · rw [h_eq]
    exact vasyuninBEntry_diagonal k
  · rw [baezDuarteGramEntry_eq_tsum_intervals_add_tail h k hh hk]
    exact interval_sum_add_tail_eq_cotangent_formula_of_debts h k h_eq hh hk
      (tsum_shifted_integrals_eq_cotangent_sum h k h_eq hh hk)

end RH.Criteria.NymanBeurling.VasyuninGram
