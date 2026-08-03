import RiemannHypothesis.Criteria.NymanBeurling.MobiusSummatoryClassical
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Topology.MetricSpace.Thickening

/-! # H14M-B: de la Vallée Poussin zero-free-region assembly -/

namespace RH.Criteria.NymanBeurling.MobiusSummatory

open Filter Finset Topology
open scoped ArithmeticFunction BigOperators LSeries.notation

section ZetaGrowthPartialSummation

open Complex

/--
P1: complex-valued finite Abel summation on an arbitrary natural interval.

This is the zeta-growth analogue of
`finite_abel_sum_Icc_mul_eq_endpoint_add_sum_partial_from` from
`MobiusSummatoryClassical.lean`.  The forthcoming vertical-growth argument for
`ζ(s)` needs the same endpoint-plus-differences identity with complex weights
such as `n ^ (-s)`, so we keep this reusable copy local to the zero-free-region
pipeline rather than changing the real-valued H14 API.
-/
theorem finite_abel_sum_Icc_mul_eq_endpoint_add_sum_partial_from_complex
    (a b : ℕ → ℂ) (A B : ℕ) (hAB : A ≤ B) :
    (∑ k ∈ Finset.Icc A B, a k * b k) =
      (∑ j ∈ Finset.Icc A B, a j) * b (B + 1) +
        ∑ k ∈ Finset.Icc A B,
          (∑ j ∈ Finset.Icc A k, a j) * (b k - b (k + 1)) := by
  induction B, hAB using Nat.le_induction with
  | base =>
      simp
      ring
  | succ B hAB ih =>
      have hAB' : A ≤ B + 1 := by omega
      rw [Finset.sum_Icc_succ_top hAB', Finset.sum_Icc_succ_top hAB',
        Finset.sum_Icc_succ_top hAB']
      rw [ih]
      rw [Finset.sum_Icc_succ_top hAB']
      ring

end ZetaGrowthPartialSummation

section ThreeFourOneLogDerivative

open Complex

private noncomputable def vonMangoldtCosTerm (σ t : ℝ) (n : ℕ) : ℝ :=
  if _ : n = 0 then 0
  else Λ n * (n : ℝ) ^ (-σ) * Real.cos (t * Real.log n)

private lemma summable_vonMangoldtCosTerm {σ t : ℝ} (hσ : 1 < σ) :
    Summable (vonMangoldtCosTerm σ t) := by
  have hs : 1 < (σ + Complex.I * t : ℂ).re := by simpa using hσ
  have hsum : Summable (fun n : ℕ =>
      (LSeries.term ↗Λ (σ + Complex.I * t : ℂ) n).re) :=
    (Complex.hasSum_re
      (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).hasSum).summable
  apply hsum.congr
  intro n
  by_cases hn : n = 0
  · simp [hn, vonMangoldtCosTerm, LSeries.term]
  · simpa [hn, vonMangoldtCosTerm] using
      deLaValleePoussin_vonMangoldt_term_re_eq_cos
        (σ := σ) (t := t) hn

private lemma neg_zeta_logDeriv_re_eq_tsum_vonMangoldtCosTerm
    {σ t : ℝ} (hσ : 1 < σ) :
    (-deriv riemannZeta (σ + Complex.I * t : ℂ) /
        riemannZeta (σ + Complex.I * t : ℂ)).re =
      ∑' n : ℕ, vonMangoldtCosTerm σ t n := by
  simpa [vonMangoldtCosTerm] using
    deLaValleePoussin_neg_zeta_logDeriv_re_eq_tsum_cos
      (σ := σ) (t := t) hσ

/-- Z1: the logarithmic-derivative form of the de la Vallée Poussin
`3-4-1` positivity inequality. -/
theorem deLaValleePoussin_logDeriv_three_four_one_nonneg
    {σ t : ℝ} (hσ : 1 < σ) :
    0 ≤
      3 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re +
      4 * (-deriv riemannZeta (σ + Complex.I * t : ℂ) /
        riemannZeta (σ + Complex.I * t : ℂ)).re +
      (-deriv riemannZeta (σ + Complex.I * (2 * t) : ℂ) /
        riemannZeta (σ + Complex.I * (2 * t) : ℂ)).re := by
  have hzero :
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re =
        ∑' n : ℕ, vonMangoldtCosTerm σ 0 n := by
    simpa using
      neg_zeta_logDeriv_re_eq_tsum_vonMangoldtCosTerm
        (σ := σ) (t := 0) hσ
  have hdouble :
      (-deriv riemannZeta (σ + Complex.I * (2 * t) : ℂ) /
          riemannZeta (σ + Complex.I * (2 * t) : ℂ)).re =
        ∑' n : ℕ, vonMangoldtCosTerm σ (2 * t) n := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using
      neg_zeta_logDeriv_re_eq_tsum_vonMangoldtCosTerm
        (σ := σ) (t := 2 * t) hσ
  rw [hzero,
    neg_zeta_logDeriv_re_eq_tsum_vonMangoldtCosTerm
      (σ := σ) (t := t) hσ,
    hdouble]
  have hsum₀ : Summable (vonMangoldtCosTerm σ 0) :=
    summable_vonMangoldtCosTerm hσ
  have hsum₁ : Summable (vonMangoldtCosTerm σ t) :=
    summable_vonMangoldtCosTerm hσ
  have hsum₂ : Summable (vonMangoldtCosTerm σ (2 * t)) :=
    summable_vonMangoldtCosTerm hσ
  rw [← hsum₀.tsum_mul_left 3, ← hsum₁.tsum_mul_left 4,
    ← (hsum₀.mul_left 3).tsum_add (hsum₁.mul_left 4),
    ← ((hsum₀.mul_left 3).add (hsum₁.mul_left 4)).tsum_add hsum₂]
  apply tsum_nonneg
  intro n
  by_cases hn : n = 0
  · simp [hn, vonMangoldtCosTerm]
  · simp only [vonMangoldtCosTerm, hn, ↓reduceDIte, zero_mul, Real.cos_zero,
      mul_one]
    have hΛ : 0 ≤ (Λ n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
    have hpow : 0 ≤ (n : ℝ) ^ (-σ) :=
      Real.rpow_nonneg (Nat.cast_nonneg n) _
    have htrig :=
      deLaValleePoussin_three_four_one_trig_nonneg (t * Real.log n)
    have htwo : (2 * t) * Real.log n = 2 * (t * Real.log n) := by ring
    rw [htwo]
    calc
      3 * (Λ n * (n : ℝ) ^ (-σ)) +
            4 * (Λ n * (n : ℝ) ^ (-σ) *
              Real.cos (t * Real.log n)) +
            Λ n * (n : ℝ) ^ (-σ) *
              Real.cos (2 * (t * Real.log n)) =
          (Λ n * (n : ℝ) ^ (-σ)) *
            (3 + 4 * Real.cos (t * Real.log n) +
              Real.cos (2 * (t * Real.log n))) := by ring
      _ ≥ 0 := mul_nonneg (mul_nonneg hΛ hpow) htrig

end ThreeFourOneLogDerivative

section PoleLogDerivativeBound

open Complex

/-- The pole-removed zeta function is analytic at every point. -/
lemma zetaPoleRemoved_analyticAt (s : ℂ) :
    AnalyticAt ℂ zetaPoleRemoved s := by
  by_cases hs : s = 1
  · simpa [hs] using zetaPoleRemoved_analyticAt_one
  · have hprod : AnalyticAt ℂ
        (fun z : ℂ => (z - 1) * riemannZeta z) s :=
      (analyticAt_id.sub analyticAt_const).mul
        (analyticOn_riemannZeta s (by simpa using hs))
    apply hprod.congr
    filter_upwards [eventually_ne_nhds hs] with z hz
    exact (zetaPoleRemoved_of_ne_one hz).symm

/-- On the real interval `[1, 2]`, removing the pole introduces no zero. -/
lemma zetaPoleRemoved_ne_zero_of_real_mem_Icc {σ : ℝ}
    (hσ : σ ∈ Set.Icc (1 : ℝ) 2) :
    zetaPoleRemoved (σ : ℂ) ≠ 0 := by
  rcases hσ with ⟨hσ1, _⟩
  by_cases heq : σ = 1
  · subst σ
    simp
  · have hσgt : 1 < σ := lt_of_le_of_ne hσ1 (Ne.symm heq)
    rw [zetaPoleRemoved_of_ne_one (by exact_mod_cast heq)]
    exact mul_ne_zero
      (sub_ne_zero.mpr (by exact_mod_cast heq))
      (riemannZeta_ne_zero_of_one_lt_re (by simpa using hσgt))

/-- The bounded regular contribution to `-ζ'/ζ` after its pole is removed. -/
noncomputable def zetaPoleLogDerivRemainder (σ : ℝ) : ℝ :=
  -(deriv zetaPoleRemoved (σ : ℂ) / zetaPoleRemoved (σ : ℂ)).re

lemma continuousOn_zetaPoleLogDerivRemainder :
    ContinuousOn zetaPoleLogDerivRemainder (Set.Icc (1 : ℝ) 2) := by
  intro σ hσ
  have hGne := zetaPoleRemoved_ne_zero_of_real_mem_Icc hσ
  have hcoe : ContinuousAt (fun x : ℝ => (x : ℂ)) σ :=
    Complex.continuous_ofReal.continuousAt
  have hG : ContinuousAt (fun x : ℝ => zetaPoleRemoved (x : ℂ)) σ :=
    (zetaPoleRemoved_analyticAt (σ : ℂ)).continuousAt.comp hcoe
  have hG' : ContinuousAt
      (fun x : ℝ => deriv zetaPoleRemoved (x : ℂ)) σ :=
    (zetaPoleRemoved_analyticAt (σ : ℂ)).deriv.continuousAt.comp hcoe
  have hre : ContinuousAt (fun x : ℝ =>
      (deriv zetaPoleRemoved (x : ℂ) / zetaPoleRemoved (x : ℂ)).re) σ :=
    Complex.continuous_re.continuousAt.comp (hG'.div hG hGne)
  exact hre.neg.continuousWithinAt

/-- Algebraic separation of the pole contribution from the logarithmic
derivative of zeta. -/
lemma neg_zeta_logDeriv_eq_inv_sub_poleRemovedLogDeriv
    {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    -deriv riemannZeta s / riemannZeta s =
      1 / (s - 1) - deriv zetaPoleRemoved s / zetaPoleRemoved s := by
  rw [zetaPoleRemoved_of_ne_one hs, deriv_zetaPoleRemoved_of_ne_one hs]
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  field_simp [hsub, hz]
  ring

/-- Z2: the real pole term dominates `-ζ'/ζ` up to one fixed constant on
`1 < σ ≤ 2`.  Compactness absorbs the portion away from the pole. -/
theorem deLaValleePoussin_neg_logDeriv_real_le_pole_add_const :
    ∃ A > 0, ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤
        1 / (σ - 1) + A := by
  rcases isCompact_Icc.bddAbove_image
      continuousOn_zetaPoleLogDerivRemainder with ⟨A₀, hA₀⟩
  refine ⟨max 1 A₀, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro σ hσ1 hσ2
  have hmem : σ ∈ Set.Icc (1 : ℝ) 2 := ⟨hσ1.le, hσ2⟩
  have hrem : zetaPoleLogDerivRemainder σ ≤ max 1 A₀ :=
    (hA₀ (Set.mem_image_of_mem zetaPoleLogDerivRemainder hmem)).trans
      (le_max_right _ _)
  have hs : (σ : ℂ) ≠ 1 := by exact_mod_cast ne_of_gt hσ1
  have hz : riemannZeta (σ : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simpa using hσ1)
  have hid := neg_zeta_logDeriv_eq_inv_sub_poleRemovedLogDeriv hs hz
  have hinv :
      1 / ((σ : ℂ) - 1) = ((1 / (σ - 1) : ℝ) : ℂ) := by
    calc
      1 / ((σ : ℂ) - 1) = 1 / ((σ - 1 : ℝ) : ℂ) := by norm_num
      _ = ((1 / (σ - 1) : ℝ) : ℂ) :=
        (Complex.ofReal_div 1 (σ - 1)).symm
  have hre :
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re =
        1 / (σ - 1) + zetaPoleLogDerivRemainder σ := by
    calc
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re =
          (1 / ((σ : ℂ) - 1) -
            deriv zetaPoleRemoved (σ : ℂ) /
              zetaPoleRemoved (σ : ℂ)).re := congrArg Complex.re hid
      _ = (1 / ((σ : ℂ) - 1)).re -
            (deriv zetaPoleRemoved (σ : ℂ) /
              zetaPoleRemoved (σ : ℂ)).re := rfl
      _ = (((1 / (σ - 1) : ℝ) : ℂ)).re -
            (deriv zetaPoleRemoved (σ : ℂ) /
              zetaPoleRemoved (σ : ℂ)).re := by rw [hinv]
      _ = 1 / (σ - 1) + zetaPoleLogDerivRemainder σ := by
        change (1 / (σ - 1) : ℝ) -
            (deriv zetaPoleRemoved (σ : ℂ) /
              zetaPoleRemoved (σ : ℂ)).re =
          1 / (σ - 1) -
            (deriv zetaPoleRemoved (σ : ℂ) /
              zetaPoleRemoved (σ : ℂ)).re
        rfl
  rw [hre]
  linarith

end PoleLogDerivativeBound

section ZetaLogDerivativeDiscBound

open Complex

/--
Z3: the one quantitative complex-analytic input still missing from Mathlib for
the classical de la Vallée Poussin argument.

Mathlib supplies Borel--Carathéodory, Jensen's formula, discreteness of the
zeta zeros, and analytic order/factorization.  What is not currently supplied
is the quantitative application of those tools to zeta in a disc centered at
height `t`: a logarithmic vertical bound for `-ζ'/ζ`, together with the same
bound after retaining the contribution of a specified zero.  The latter is
stated with coefficient one, so it applies to zeros of arbitrary positive
multiplicity (and deliberately does not assume a simple zero).

The companion diagnostic checks the normalization on the first twenty
critical-line zeros; it suggests that `C = 1` has a wide numerical margin.
No numerical observation is used in this hypothesis package.
-/
structure ZetaLogDerivDiscBound where
  C : ℝ
  C_nonneg : 0 ≤ C
  vertical_bound :
    ∀ {σ t : ℝ}, 1 < σ → σ ≤ 2 → t ≠ 0 →
      (-deriv riemannZeta (σ + Complex.I * t : ℂ) /
          riemannZeta (σ + Complex.I * t : ℂ)).re ≤
        C * Real.log (|t| + 2)
  zero_contribution_bound :
    ∀ {σ β t : ℝ}, 1 < σ → σ ≤ 2 → β ≤ 1 → t ≠ 0 →
      riemannZeta (β + Complex.I * t : ℂ) = 0 →
      (-deriv riemannZeta (σ + Complex.I * t : ℂ) /
          riemannZeta (σ + Complex.I * t : ℂ)).re ≤
        -1 / (σ - β) + C * Real.log (|t| + 2)

private lemma three_four_one_forces_repulsion
    {A C l logHeight delta x : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hl : 0 < l)
    (hlL : l ≤ logHeight) (hL : 0 < logHeight)
    (hδ : 0 < delta) (hx : 0 ≤ x)
    (hδsmall : delta ≤ 1 / (10 * (3 * A / l + 6 * C + 1)))
    (hmain :
      0 ≤ 3 * logHeight / delta + 3 * A -
        4 / (delta / logHeight + x) + 6 * C * logHeight) :
    delta / 4 ≤ x * logHeight := by
  by_contra hn
  have hxlt : x * logHeight < delta / 4 := lt_of_not_ge hn
  have hqpos : 0 < delta / logHeight + x :=
    add_pos_of_pos_of_nonneg (div_pos hδ hL) hx
  have hqLt :
      delta / logHeight + x < 5 * delta / (4 * logHeight) := by
    calc
      delta / logHeight + x =
          (delta + x * logHeight) / logHeight := by field_simp
      _ < (delta + delta / 4) / logHeight :=
        (div_lt_div_iff_of_pos_right hL).2 (by linarith)
      _ = 5 * delta / (4 * logHeight) := by field_simp; norm_num
  have hinv :
      4 * logHeight / (5 * delta) < 1 / (delta / logHeight + x) := by
    have h := one_div_lt_one_div_of_lt hqpos hqLt
    calc
      4 * logHeight / (5 * delta) =
          1 / (5 * delta / (4 * logHeight)) := by field_simp
      _ < 1 / (delta / logHeight + x) := h
  have hBpos : 0 < 3 * A / l + 6 * C + 1 := by positivity
  have hδB : delta * (3 * A / l + 6 * C + 1) ≤ 1 / 10 := by
    have h := (le_div_iff₀
      (by positivity : 0 < 10 * (3 * A / l + 6 * C + 1))).mp hδsmall
    nlinarith
  have hAl : A / logHeight ≤ A / l :=
    div_le_div_of_nonneg_left hA hl hlL
  have htarget :
      3 * A + 6 * C * logHeight < logHeight / (5 * delta) := by
    have haux : delta * (3 * A / logHeight + 6 * C) < 1 / 5 := by
      have hcomp : delta * (3 * A / logHeight + 6 * C) ≤
          delta * (3 * A / l + 6 * C) := by gcongr
      nlinarith
    apply (lt_div_iff₀ (by positivity : 0 < 5 * delta)).2
    calc
      (3 * A + 6 * C * logHeight) * (5 * delta) =
          5 * logHeight * (delta * (3 * A / logHeight + 6 * C)) := by
        field_simp
      _ < 5 * logHeight * (1 / 5) := by gcongr
      _ = logHeight := by ring
  have hfour :
      16 * logHeight / (5 * delta) < 4 / (delta / logHeight + x) := by
    calc
      16 * logHeight / (5 * delta) =
          4 * (4 * logHeight / (5 * delta)) := by ring
      _ < 4 * (1 / (delta / logHeight + x)) := by gcongr
      _ = 4 / (delta / logHeight + x) := by ring
  have hneg :
      -4 / (delta / logHeight + x) <
        -16 * logHeight / (5 * delta) := by
    calc
      -4 / (delta / logHeight + x) =
          -(4 / (delta / logHeight + x)) := by ring
      _ < -(16 * logHeight / (5 * delta)) := neg_lt_neg hfour
      _ = -16 * logHeight / (5 * delta) := by ring
  have hbad :
      0 < 3 * logHeight / delta + 3 * A -
        16 * logHeight / (5 * delta) + 6 * C * logHeight := by
    linarith
  have hid :
      3 * logHeight / delta + 3 * A -
          16 * logHeight / (5 * delta) + 6 * C * logHeight =
        3 * A + 6 * C * logHeight - logHeight / (5 * delta) := by
    field_simp
    ring
  rw [hid] at hbad
  linarith

/--
Z4, nonreal part: the disc logarithmic-derivative package and the proved
`3-4-1`/pole estimates repel every nonreal zeta zero from the line `Re s = 1`
by a uniform logarithmic distance.  No assumption on the zero's multiplicity
is made.
-/
theorem deLaValleePoussin_nonreal_zero_repulsion
    (H : ZetaLogDerivDiscBound) :
    ∃ c > 0, ∀ {β t : ℝ}, β ≤ 1 → t ≠ 0 →
      riemannZeta (β + Complex.I * t : ℂ) = 0 →
      c ≤ (1 - β) * Real.log (|t| + 2) := by
  rcases deLaValleePoussin_neg_logDeriv_real_le_pole_add_const with
    ⟨A, hA, hApole⟩
  let l : ℝ := Real.log 2
  let B : ℝ := 3 * A / l + 6 * H.C + 1
  let delta : ℝ := min (l / 2) (1 / (10 * B))
  have hl : 0 < l := by
    dsimp [l]
    exact Real.log_pos (by norm_num)
  have hB : 0 < B := by
    dsimp [B]
    have hquot : 0 ≤ 3 * A / l := div_nonneg (by positivity) hl.le
    nlinarith [H.C_nonneg]
  have hδ : 0 < delta := by
    dsimp [delta]
    exact lt_min (div_pos hl (by norm_num)) (one_div_pos.mpr (by positivity))
  refine ⟨delta / 4, div_pos hδ (by norm_num), ?_⟩
  intro β t hβ ht hz
  let logHeight : ℝ := Real.log (|t| + 2)
  let x : ℝ := 1 - β
  let σ : ℝ := 1 + delta / logHeight
  have hL : 0 < logHeight := by
    dsimp [logHeight]
    exact Real.log_pos (by linarith [abs_nonneg t])
  have hlL : l ≤ logHeight := by
    dsimp [l, logHeight]
    exact Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hδsmall : delta ≤ 1 / (10 * B) := by
    dsimp [delta]
    exact min_le_right _ _
  have hδhalf : delta ≤ l / 2 := by
    dsimp [delta]
    exact min_le_left _ _
  have hσ1 : 1 < σ := by
    dsimp [σ]
    exact lt_add_of_pos_right 1 (div_pos hδ hL)
  have hσ2 : σ ≤ 2 := by
    have hδL : delta ≤ logHeight / 2 := hδhalf.trans (by linarith)
    dsimp [σ]
    have hquot : delta / logHeight ≤ 1 / 2 := by
      apply (div_le_iff₀ hL).2
      simpa [div_eq_mul_inv, mul_comm] using hδL
    linarith
  have hzero := H.zero_contribution_bound hσ1 hσ2 hβ ht hz
  have hzero' :
      (-deriv riemannZeta (σ + Complex.I * t : ℂ) /
          riemannZeta (σ + Complex.I * t : ℂ)).re ≤
        -1 / (delta / logHeight + x) + H.C * logHeight := by
    calc
      _ ≤ -1 / (σ - β) + H.C * Real.log (|t| + 2) := hzero
      _ = -1 / (delta / logHeight + x) + H.C * logHeight := by
        dsimp [σ, x, logHeight]
        congr 2
        ring
  have hpole := hApole σ hσ1 hσ2
  have hpole' :
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤
        logHeight / delta + A := by
    calc
      _ ≤ 1 / (σ - 1) + A := hpole
      _ = logHeight / delta + A := by
        dsimp [σ]
        field_simp [ne_of_gt hL, ne_of_gt hδ]
        ring
  have htwo_ne : 2 * t ≠ 0 := mul_ne_zero (by norm_num) ht
  have hdouble := H.vertical_bound hσ1 hσ2 htwo_ne
  have hlogdouble : Real.log (|2 * t| + 2) ≤ 2 * logHeight := by
    have habs : |2 * t| = 2 * |t| := by rw [abs_mul]; norm_num
    have harg : 2 * |t| + 2 ≤ (|t| + 2) ^ 2 := by
      nlinarith [abs_nonneg t, sq_nonneg (|t| + 1)]
    calc
      Real.log (|2 * t| + 2) = Real.log (2 * |t| + 2) := by rw [habs]
      _ ≤ Real.log ((|t| + 2) ^ 2) :=
        Real.log_le_log (by positivity) harg
      _ = 2 * logHeight := by simp [Real.log_pow, logHeight]
  have hdouble' :
      (-deriv riemannZeta (σ + Complex.I * (2 * t) : ℂ) /
          riemannZeta (σ + Complex.I * (2 * t) : ℂ)).re ≤
        H.C * (2 * logHeight) := by
    calc
      _ ≤ H.C * Real.log (|2 * t| + 2) := by
        simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using hdouble
      _ ≤ H.C * (2 * logHeight) :=
        mul_le_mul_of_nonneg_left hlogdouble H.C_nonneg
  have hpos := deLaValleePoussin_logDeriv_three_four_one_nonneg
    (σ := σ) (t := t) hσ1
  have hmain :
      0 ≤ 3 * logHeight / delta + 3 * A -
        4 / (delta / logHeight + x) + 6 * H.C * logHeight := by
    have hmain' :
        0 ≤ 3 * (logHeight / delta + A) +
          4 * (-1 / (delta / logHeight + x) + H.C * logHeight) +
          H.C * (2 * logHeight) := by
      linarith
    convert hmain' using 1 <;> ring
  exact three_four_one_forces_repulsion hA.le H.C_nonneg hl hlL hL hδ hx
    (by simpa [B] using hδsmall) hmain

/--
Z5: the isolated logarithmic-derivative disc estimate is sufficient to
construct the frozen de la Vallée Poussin zero-free-region package.

The nonreal case is `deLaValleePoussin_nonreal_zero_repulsion`.  On the real
axis, continuity and the value `zetaPoleRemoved 1 = 1` give a zero-free
neighborhood of the pole; shrinking the same positive constant absorbs this
compact low-height case.  The closed half-plane `Re s ≥ 1` is Mathlib's
unconditional zeta nonvanishing theorem.
-/
noncomputable def deLaValleePoussinZeroFreeRegion_of_logDerivDiscBound
    (H : ZetaLogDerivDiscBound) :
    DeLaValleePoussinZeroFreeRegion := by
  let hrepExists := deLaValleePoussin_nonreal_zero_repulsion H
  let c₀ : ℝ := Classical.choose hrepExists
  have hc₀ : 0 < c₀ := (Classical.choose_spec hrepExists).1
  have hrepel :
      ∀ {β t : ℝ}, β ≤ 1 → t ≠ 0 →
        riemannZeta (β + Complex.I * t : ℂ) = 0 →
        c₀ ≤ (1 - β) * Real.log (|t| + 2) :=
    (Classical.choose_spec hrepExists).2
  have hG_eventually :
      ∀ᶠ z : ℂ in 𝓝 (1 : ℂ), zetaPoleRemoved z ≠ 0 :=
    (zetaPoleRemoved_analyticAt (1 : ℂ)).continuousAt.eventually_ne (by simp)
  let hlocalExists := Metric.eventually_nhds_iff.mp hG_eventually
  let ε : ℝ := Classical.choose hlocalExists
  have hε : 0 < ε := (Classical.choose_spec hlocalExists).1
  have hG_ne :
      ∀ ⦃z : ℂ⦄, dist z (1 : ℂ) < ε → zetaPoleRemoved z ≠ 0 :=
    (Classical.choose_spec hlocalExists).2
  let l : ℝ := Real.log 2
  let c : ℝ := min c₀ (ε * l / 2)
  have hl : 0 < l := by
    dsimp [l]
    exact Real.log_pos (by norm_num)
  have hc : 0 < c := by
    dsimp [c]
    exact lt_min hc₀ (div_pos (mul_pos hε hl) (by norm_num))
  refine
    { c := c
      c_pos := hc
      zeta_ne_zero := ?_ }
  intro s hs
  by_cases hre : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re hre
  have hre_lt : s.re < 1 := lt_of_not_ge hre
  by_cases him : s.im = 0
  · have hs_real : s = (s.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa [him]
    have hregion : 1 - c / l < s.re := by
      simpa [deLaValleePoussinRegion, him, l] using hs
    have hgap : 1 - s.re < c / l := by linarith
    have hcε : c ≤ ε * l / 2 := by
      dsimp [c]
      exact min_le_right _ _
    have hcdiv : c / l ≤ ε / 2 := by
      apply (div_le_iff₀ hl).2
      calc
        c ≤ ε * l / 2 := hcε
        _ = (ε / 2) * l := by ring
    have hdist : dist s (1 : ℂ) < ε := by
      rw [hs_real]
      have hreal : dist s.re (1 : ℝ) = 1 - s.re := by
        rw [Real.dist_eq, abs_of_nonpos (by linarith)]
        ring
      have hsmall : 1 - s.re < ε := by linarith [hε]
      have hcoe : dist (s.re : ℂ) (1 : ℂ) = dist s.re (1 : ℝ) := by
        rw [dist_eq_norm, dist_eq_norm]
        calc
          ‖(s.re : ℂ) - 1‖ = ‖((s.re - 1 : ℝ) : ℂ)‖ := by
            rw [Complex.ofReal_sub, Complex.ofReal_one]
          _ = ‖s.re - 1‖ := Complex.norm_real _
      rw [hcoe, hreal]
      exact hsmall
    have hG := hG_ne hdist
    intro hz
    have hs_ne : s ≠ 1 := by
      intro h
      have : s.re = 1 := by simpa [h]
      linarith
    rw [zetaPoleRemoved_of_ne_one hs_ne] at hG
    exact hG (by rw [hz]; simp)
  · intro hz
    have hs_cart : s = (s.re + Complex.I * s.im : ℂ) := by
      apply Complex.ext <;> simp
    rw [hs_cart] at hz
    have hrep := hrepel hre_lt.le him hz
    have hL : 0 < Real.log (|s.im| + 2) := log_abs_im_add_two_pos s
    have hregion :
        1 - c / Real.log (|s.im| + 2) < s.re := by
      simpa [deLaValleePoussinRegion] using hs
    have hgap :
        (1 - s.re) * Real.log (|s.im| + 2) < c := by
      apply (lt_div_iff₀ hL).mp
      linarith
    have hc₀c : c ≤ c₀ := by
      dsimp [c]
      exact min_le_left _ _
    linarith

section FrozenDiscBoundObstruction

open Complex

/-- The regular part of the zeta logarithmic derivative after removing its
pole at `s = 1`. -/
noncomputable def zetaPoleLogDerivRegularPart (s : ℂ) : ℝ :=
  (deriv zetaPoleRemoved s / zetaPoleRemoved s).re

lemma continuousAt_zetaPoleLogDerivRegularPart :
    ContinuousAt zetaPoleLogDerivRegularPart (1 : ℂ) := by
  have hG := zetaPoleRemoved_analyticAt (1 : ℂ)
  have hquot : ContinuousAt
      (fun s : ℂ => deriv zetaPoleRemoved s / zetaPoleRemoved s) 1 :=
    hG.deriv.continuousAt.div hG.continuousAt (by simp)
  exact Complex.continuous_re.continuousAt.comp hquot

/--
The globally quantified `vertical_bound` field in the frozen Z3 package is
incompatible with zeta's pole.  Along `s = 1 + x + ix`, its left side grows
as `1 / (2x)`, while `C * log (x + 2)` remains bounded as `x → 0⁺`.

Consequently the frozen package cannot be instantiated.  A corrected API
must restrict the vertical estimate to ordinates of nonreal zeta zeros (which
is all the zero-repulsion proof uses), or impose a fixed positive lower bound
on `|t|` and absorb the remaining compact region separately.
-/
theorem not_nonempty_zetaLogDerivDiscBound :
    ¬ Nonempty ZetaLogDerivDiscBound := by
  rintro ⟨H⟩
  let Q : ℂ → ℝ := zetaPoleLogDerivRegularPart
  have hQcont : ContinuousAt Q (1 : ℂ) := by
    simpa [Q] using continuousAt_zetaPoleLogDerivRegularPart
  rcases Metric.continuousAt_iff.mp hQcont 1 zero_lt_one with
    ⟨radius, hradius, hQclose⟩
  let B : ℝ := |Q 1| + 1
  let M : ℝ := H.C * Real.log 3 + B + 1
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hB : 0 < B := by
    dsimp [B]
    linarith [abs_nonneg (Q 1)]
  have hM : 0 < M := by
    dsimp [M]
    nlinarith [H.C_nonneg, hlog3]
  let x : ℝ := min (radius / 4) (min (1 / 2) (1 / (4 * M)))
  have hx : 0 < x := by
    dsimp [x]
    exact lt_min (div_pos hradius (by norm_num))
      (lt_min (by norm_num) (one_div_pos.mpr (by positivity)))
  have hxradius : x ≤ radius / 4 := by
    dsimp [x]
    exact min_le_left _ _
  have hxone : x ≤ 1 / 2 := by
    dsimp [x]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hxM : x ≤ 1 / (4 * M) := by
    dsimp [x]
    exact (min_le_right _ _).trans (min_le_right _ _)
  let s : ℂ := (1 + x : ℝ) + Complex.I * x
  have hsre : s.re = 1 + x := by simp [s]
  have hsim : s.im = x := by simp [s]
  have hsone : 1 < s.re := by rw [hsre]; linarith
  have hstwo : s.re ≤ 2 := by rw [hsre]; linarith
  have hvertical :
      (-deriv riemannZeta s / riemannZeta s).re ≤
        H.C * Real.log (x + 2) := by
    have h := H.vertical_bound
      (σ := 1 + x) (t := x) (by linarith) (by linarith) hx.ne'
    simpa [s, abs_of_pos hx] using h
  have hs_ne : s ≠ 1 := by
    intro hs
    have : s.re = 1 := by simp [hs]
    linarith
  have hz : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re hsone
  have hdist : dist s (1 : ℂ) < radius := by
    have hsub : s - 1 = (x : ℂ) + Complex.I * x := by
      dsimp [s]
      push_cast
      ring
    rw [dist_eq_norm, hsub]
    calc
      ‖(x : ℂ) + Complex.I * x‖ ≤
          ‖(x : ℂ)‖ + ‖Complex.I * (x : ℂ)‖ := norm_add_le _ _
      _ = 2 * x := by simp [abs_of_pos hx]; ring
      _ < radius := by linarith
  have hQdist : dist (Q s) (Q 1) < 1 := hQclose hdist
  have hQlt : Q s < B := by
    have hdiff : Q s - Q 1 < 1 := by
      rw [Real.dist_eq] at hQdist
      exact lt_of_le_of_lt (le_abs_self _) hQdist
    dsimp [B]
    linarith [le_abs_self (Q 1)]
  have hpole : (1 / (s - 1)).re = 1 / (2 * x) := by
    have hsub : s - 1 = (x : ℂ) + Complex.I * x := by
      dsimp [s]
      push_cast
      ring
    rw [hsub, div_eq_mul_inv, one_mul, Complex.inv_re]
    simp [Complex.normSq_apply]
    field_simp [hx.ne']
    ring
  have hformula :
      (-deriv riemannZeta s / riemannZeta s).re =
        1 / (2 * x) - Q s := by
    have h := neg_zeta_logDeriv_eq_inv_sub_poleRemovedLogDeriv hs_ne hz
    calc
      (-deriv riemannZeta s / riemannZeta s).re =
          (1 / (s - 1) - deriv zetaPoleRemoved s /
            zetaPoleRemoved s).re := congrArg Complex.re h
      _ = (1 / (s - 1)).re -
          (deriv zetaPoleRemoved s / zetaPoleRemoved s).re := rfl
      _ = 1 / (2 * x) - Q s := by rw [hpole]; rfl
  have hxMprod : x * (4 * M) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 4 * M)).mp hxM
  have hinv : 2 * M ≤ 1 / (2 * x) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * x)).2
    nlinarith
  have hlarge : H.C * Real.log 3 < 1 / (2 * x) - Q s := by
    dsimp [M] at hinv
    linarith
  have hlog : Real.log (x + 2) ≤ Real.log 3 := by
    exact Real.log_le_log (by positivity) (by linarith)
  have hupper : H.C * Real.log (x + 2) ≤ H.C * Real.log 3 :=
    mul_le_mul_of_nonneg_left hlog H.C_nonneg
  rw [hformula] at hvertical
  linarith

end FrozenDiscBoundObstruction

section RepairedDiscBound

open Complex

/--
R1: the repaired quantitative logarithmic-derivative package.

Unlike `ZetaLogDerivDiscBound`, both estimates are restricted to heights
`|t| ≥ t₀`, keeping them uniformly away from zeta's pole.  The companion
diagnostic sampled the full frozen `1 < σ ≤ 2`, `|t| ≥ 1` shape (including
`σ - 1` down to `10⁻⁶`, both signs of `t`, and heights through `250`): the
normalized vertical quantity stayed between approximately `-0.4821` and
`0.1424`.  The retained-zero normalization stayed below `0.233` on the first
twenty critical-line zeros.  These observations only gate the statement;
the constant `C` remains abstract.
-/
structure ZetaLogDerivDiscBoundAtHeight where
  t₀ : ℝ
  t₀_pos : 0 < t₀
  t₀_le_one : t₀ ≤ 1
  C : ℝ
  C_nonneg : 0 ≤ C
  vertical_bound :
    ∀ {σ t : ℝ}, 1 < σ → σ ≤ 2 → t₀ ≤ |t| →
      (-deriv riemannZeta (σ + Complex.I * t : ℂ) /
          riemannZeta (σ + Complex.I * t : ℂ)).re ≤
        C * Real.log (|t| + 2)
  zero_contribution_bound :
    ∀ {σ β t : ℝ}, 1 < σ → σ ≤ 2 → β ≤ 1 → t₀ ≤ |t| →
      riemannZeta (β + Complex.I * t : ℂ) = 0 →
      (-deriv riemannZeta (σ + Complex.I * t : ℂ) /
          riemannZeta (σ + Complex.I * t : ℂ)).re ≤
        -1 / (σ - β) + C * Real.log (|t| + 2)

/-- R2: every bounded-height portion of the line `Re s = 1` has a uniform
zero-free neighborhood to its left.  This is purely compactness: the
pole-removed zeta function is continuous and nonzero on the compact vertical
segment. -/
theorem exists_lowHeight_zeta_zeroFree_left_strip (t₀ : ℝ) (_ht₀ : 0 ≤ t₀) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ {σ t : ℝ}, 1 - delta ≤ σ → σ ≤ 1 → |t| ≤ t₀ →
        riemannZeta (σ + Complex.I * t : ℂ) ≠ 0 := by
  let lineMap : ℝ → ℂ := fun t => (1 : ℂ) + Complex.I * t
  let K : Set ℂ := lineMap '' Set.Icc (-t₀) t₀
  let U : Set ℂ := {s | zetaPoleRemoved s ≠ 0}
  have hline : Continuous lineMap := by
    dsimp [lineMap]
    exact continuous_const.add (continuous_const.mul Complex.continuous_ofReal)
  have hK : IsCompact K := by
    dsimp [K]
    exact isCompact_Icc.image hline
  have hGcontinuous : Continuous zetaPoleRemoved :=
    continuous_iff_continuousAt.mpr fun s =>
      (zetaPoleRemoved_analyticAt s).continuousAt
  have hU : IsOpen U := by
    dsimp [U]
    exact isOpen_compl_singleton.preimage hGcontinuous
  have hKU : K ⊆ U := by
    rintro s ⟨t, ht, rfl⟩
    dsimp [U, lineMap]
    by_cases htzero : t = 0
    · subst t
      simp
    · have hs_ne : (1 + Complex.I * t : ℂ) ≠ 1 := by
        intro h
        have him : (1 + Complex.I * t : ℂ).im = (1 : ℂ).im :=
          congrArg Complex.im h
        simpa using htzero (by simpa using him)
      rw [zetaPoleRemoved_of_ne_one hs_ne]
      exact mul_ne_zero (sub_ne_zero.mpr hs_ne)
        (riemannZeta_ne_zero_of_one_le_re (by simp))
  rcases hK.exists_thickening_subset_open hU hKU with
    ⟨radius, hradius, hthick⟩
  refine ⟨radius / 2, div_pos hradius (by norm_num), ?_⟩
  intro σ t hσleft hσright ht
  let center : ℂ := (1 : ℂ) + Complex.I * t
  have htIcc : t ∈ Set.Icc (-t₀) t₀ := by
    rw [Set.mem_Icc]
    exact ⟨(neg_le_of_abs_le ht), (le_of_abs_le ht)⟩
  have hcenter : center ∈ K := by
    exact ⟨t, htIcc, rfl⟩
  have hdist : dist (σ + Complex.I * t : ℂ) center < radius := by
    have hsub : (σ + Complex.I * t : ℂ) - center = ((σ - 1 : ℝ) : ℂ) := by
      dsimp [center]
      push_cast
      ring
    rw [dist_eq_norm, hsub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    linarith
  have hmem : (σ + Complex.I * t : ℂ) ∈ Metric.thickening radius K :=
    Metric.mem_thickening_iff.mpr ⟨center, hcenter, hdist⟩
  have hG : zetaPoleRemoved (σ + Complex.I * t : ℂ) ≠ 0 :=
    hthick hmem
  by_cases hsone : (σ + Complex.I * t : ℂ) = 1
  · rw [hsone]
    exact riemannZeta_one_ne_zero
  · rw [zetaPoleRemoved_of_ne_one hsone] at hG
    exact (mul_ne_zero_iff.mp hG).2

/--
R3, high-height part: the repaired logarithmic-derivative package repels zeta
zeros whose ordinate is at least the package's fixed height.
-/
theorem deLaValleePoussin_high_zero_repulsion
    (H : ZetaLogDerivDiscBoundAtHeight) :
    ∃ c > 0, ∀ {β t : ℝ}, β ≤ 1 → H.t₀ ≤ |t| →
      riemannZeta (β + Complex.I * t : ℂ) = 0 →
      c ≤ (1 - β) * Real.log (|t| + 2) := by
  rcases deLaValleePoussin_neg_logDeriv_real_le_pole_add_const with
    ⟨A, hA, hApole⟩
  let l : ℝ := Real.log 2
  let B : ℝ := 3 * A / l + 6 * H.C + 1
  let delta : ℝ := min (l / 2) (1 / (10 * B))
  have hl : 0 < l := by
    dsimp [l]
    exact Real.log_pos (by norm_num)
  have hB : 0 < B := by
    dsimp [B]
    have hquot : 0 ≤ 3 * A / l := div_nonneg (by positivity) hl.le
    nlinarith [H.C_nonneg]
  have hδ : 0 < delta := by
    dsimp [delta]
    exact lt_min (div_pos hl (by norm_num)) (one_div_pos.mpr (by positivity))
  refine ⟨delta / 4, div_pos hδ (by norm_num), ?_⟩
  intro β t hβ htHeight hz
  let logHeight : ℝ := Real.log (|t| + 2)
  let x : ℝ := 1 - β
  let σ : ℝ := 1 + delta / logHeight
  have hL : 0 < logHeight := by
    dsimp [logHeight]
    exact Real.log_pos (by linarith [abs_nonneg t])
  have hlL : l ≤ logHeight := by
    dsimp [l, logHeight]
    exact Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hδsmall : delta ≤ 1 / (10 * B) := by
    dsimp [delta]
    exact min_le_right _ _
  have hδhalf : delta ≤ l / 2 := by
    dsimp [delta]
    exact min_le_left _ _
  have hσ1 : 1 < σ := by
    dsimp [σ]
    exact lt_add_of_pos_right 1 (div_pos hδ hL)
  have hσ2 : σ ≤ 2 := by
    have hδL : delta ≤ logHeight / 2 := hδhalf.trans (by linarith)
    dsimp [σ]
    have hquot : delta / logHeight ≤ 1 / 2 := by
      apply (div_le_iff₀ hL).2
      simpa [div_eq_mul_inv, mul_comm] using hδL
    linarith
  have hzero := H.zero_contribution_bound hσ1 hσ2 hβ htHeight hz
  have hzero' :
      (-deriv riemannZeta (σ + Complex.I * t : ℂ) /
          riemannZeta (σ + Complex.I * t : ℂ)).re ≤
        -1 / (delta / logHeight + x) + H.C * logHeight := by
    calc
      _ ≤ -1 / (σ - β) + H.C * Real.log (|t| + 2) := hzero
      _ = -1 / (delta / logHeight + x) + H.C * logHeight := by
        dsimp [σ, x, logHeight]
        congr 2
        ring
  have hpole := hApole σ hσ1 hσ2
  have hpole' :
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤
        logHeight / delta + A := by
    calc
      _ ≤ 1 / (σ - 1) + A := hpole
      _ = logHeight / delta + A := by
        dsimp [σ]
        field_simp [ne_of_gt hL, ne_of_gt hδ]
        ring
  have htHeightDouble : H.t₀ ≤ |2 * t| := by
    rw [abs_mul, abs_of_pos (by norm_num : 0 < (2 : ℝ))]
    nlinarith [htHeight, abs_nonneg t]
  have hdouble := H.vertical_bound hσ1 hσ2 htHeightDouble
  have hlogdouble : Real.log (|2 * t| + 2) ≤ 2 * logHeight := by
    have habs : |2 * t| = 2 * |t| := by rw [abs_mul]; norm_num
    have harg : 2 * |t| + 2 ≤ (|t| + 2) ^ 2 := by
      nlinarith [abs_nonneg t, sq_nonneg (|t| + 1)]
    calc
      Real.log (|2 * t| + 2) = Real.log (2 * |t| + 2) := by rw [habs]
      _ ≤ Real.log ((|t| + 2) ^ 2) :=
        Real.log_le_log (by positivity) harg
      _ = 2 * logHeight := by simp [Real.log_pow, logHeight]
  have hdouble' :
      (-deriv riemannZeta (σ + Complex.I * (2 * t) : ℂ) /
          riemannZeta (σ + Complex.I * (2 * t) : ℂ)).re ≤
        H.C * (2 * logHeight) := by
    calc
      _ ≤ H.C * Real.log (|2 * t| + 2) := by
        simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using hdouble
      _ ≤ H.C * (2 * logHeight) :=
        mul_le_mul_of_nonneg_left hlogdouble H.C_nonneg
  have hpos := deLaValleePoussin_logDeriv_three_four_one_nonneg
    (σ := σ) (t := t) hσ1
  have hmain :
      0 ≤ 3 * logHeight / delta + 3 * A -
        4 / (delta / logHeight + x) + 6 * H.C * logHeight := by
    have hmain' :
        0 ≤ 3 * (logHeight / delta + A) +
          4 * (-1 / (delta / logHeight + x) + H.C * logHeight) +
          H.C * (2 * logHeight) := by
      linarith
    convert hmain' using 1 <;> ring
  exact three_four_one_forces_repulsion hA.le H.C_nonneg hl hlL hL hδ hx
    (by simpa [B] using hδsmall) hmain

/--
R3/Z5': the repaired high-height logarithmic-derivative estimate, together with
the compact low-height zero-free strip, constructs the frozen de la Vallee
Poussin zero-free-region package.
-/
noncomputable def deLaValleePoussinZeroFreeRegion_of_logDerivDiscBoundAtHeight
    (H : ZetaLogDerivDiscBoundAtHeight) :
    DeLaValleePoussinZeroFreeRegion := by
  let hrepExists := deLaValleePoussin_high_zero_repulsion H
  let c₀ : ℝ := Classical.choose hrepExists
  have hc₀ : 0 < c₀ := (Classical.choose_spec hrepExists).1
  have hrepel :
      ∀ {β t : ℝ}, β ≤ 1 → H.t₀ ≤ |t| →
        riemannZeta (β + Complex.I * t : ℂ) = 0 →
        c₀ ≤ (1 - β) * Real.log (|t| + 2) :=
    (Classical.choose_spec hrepExists).2
  let hlowExists := exists_lowHeight_zeta_zeroFree_left_strip H.t₀ H.t₀_pos.le
  let delta : ℝ := Classical.choose hlowExists
  have hdelta : 0 < delta := (Classical.choose_spec hlowExists).1
  have hlow :
      ∀ {σ t : ℝ}, 1 - delta ≤ σ → σ ≤ 1 → |t| ≤ H.t₀ →
        riemannZeta (σ + Complex.I * t : ℂ) ≠ 0 :=
    (Classical.choose_spec hlowExists).2
  let l : ℝ := Real.log 2
  let c : ℝ := min c₀ (delta * l / 2)
  have hl : 0 < l := by
    dsimp [l]
    exact Real.log_pos (by norm_num)
  have hc : 0 < c := by
    dsimp [c]
    exact lt_min hc₀ (div_pos (mul_pos hdelta hl) (by norm_num))
  refine
    { c := c
      c_pos := hc
      zeta_ne_zero := ?_ }
  intro s hs
  by_cases hre : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re hre
  have hre_lt : s.re < 1 := lt_of_not_ge hre
  by_cases hheight : H.t₀ ≤ |s.im|
  · intro hz
    have hs_cart : s = (s.re + Complex.I * s.im : ℂ) := by
      apply Complex.ext <;> simp
    rw [hs_cart] at hz
    have hrep := hrepel hre_lt.le hheight hz
    have hL : 0 < Real.log (|s.im| + 2) := log_abs_im_add_two_pos s
    have hregion :
        1 - c / Real.log (|s.im| + 2) < s.re := by
      simpa [deLaValleePoussinRegion] using hs
    have hgap :
        (1 - s.re) * Real.log (|s.im| + 2) < c := by
      apply (lt_div_iff₀ hL).mp
      linarith
    have hc₀c : c ≤ c₀ := by
      dsimp [c]
      exact min_le_left _ _
    linarith
  · have himlow : |s.im| ≤ H.t₀ := le_of_not_ge hheight
    have hL : 0 < Real.log (|s.im| + 2) := log_abs_im_add_two_pos s
    have hlL : l ≤ Real.log (|s.im| + 2) := by
      dsimp [l]
      exact Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
    have hregion :
        1 - c / Real.log (|s.im| + 2) < s.re := by
      simpa [deLaValleePoussinRegion] using hs
    have hcdelta : c ≤ delta * l / 2 := by
      dsimp [c]
      exact min_le_right _ _
    have hcdiv : c / Real.log (|s.im| + 2) ≤ delta / 2 := by
      apply (div_le_iff₀ hL).2
      calc
        c ≤ delta * l / 2 := hcdelta
        _ = (delta / 2) * l := by ring
        _ ≤ (delta / 2) * Real.log (|s.im| + 2) := by
          exact mul_le_mul_of_nonneg_left hlL (by linarith)
    have hleft : 1 - delta ≤ s.re := by linarith
    have hs_cart : s = (s.re + Complex.I * s.im : ℂ) := by
      apply Complex.ext <;> simp
    rw [hs_cart]
    exact hlow hleft hre_lt.le himlow

/--
R4 stop-gate: the single quantitative output needed from the classical
Borel--Caratheodory/Jensen/partial-fraction argument at fixed positive height.

The preceding search found Mathlib's Borel--Caratheodory theorem, Jensen's
formula, zeta-zero discreteness, and analytic-order infrastructure, but not the
polynomial vertical growth bound for `ζ` in a strip nor the assembled
partial-fraction estimate for `ζ'/ζ`.  This package names precisely that
assembled complex-analysis output without changing the repaired disc-bound API.
-/
structure ZetaLinearVerticalGrowthInStripAtHeight where
  t₀ : ℝ
  t₀_pos : 0 < t₀
  t₀_le_one : t₀ ≤ 1
  C : ℝ
  C_nonneg : 0 ≤ C
  vertical_growth :
    ∀ {σ t : ℝ}, -(1 / 2 : ℝ) ≤ σ → σ ≤ 2 → t₀ ≤ |t| →
      ‖riemannZeta (σ + Complex.I * t : ℂ)‖ ≤ C * (|t| + 2)

/--
Stage V right-half target: the elementary partial-summation route advertised
for P2.  It is deliberately separated from the frozen full-strip field because
the current `ZetaLinearVerticalGrowthInStripAtHeight` asks for
`-1/2 ≤ σ ≤ 2`, whereas the `X = ⌈|t|⌉ + 2` Abel estimate naturally covers
only `1/2 ≤ σ ≤ 2`.
-/
structure ZetaRightHalfLinearVerticalGrowthAtHeight where
  t₀ : ℝ
  t₀_pos : 0 < t₀
  t₀_le_one : t₀ ≤ 1
  C : ℝ
  C_nonneg : 0 ≤ C
  right_half_growth :
    ∀ {σ t : ℝ}, (1 / 2 : ℝ) ≤ σ → σ ≤ 2 → t₀ ≤ |t| →
      ‖riemannZeta (σ + Complex.I * t : ℂ)‖ ≤ C * (|t| + 2)

/--
V-R stop-gate: the concrete Euler--Maclaurin/Abel decomposition needed to
inhabit the right-half vertical-growth field.

The intended instantiation is the classical choice `X = ⌈|t|⌉ + 2`, with
`partialSum σ t = ∑_{n≤X} n^{-(σ+it)}`,
`poleTerm σ t = X^{1-(σ+it)} / ((σ+it)-1)`, and `tailTerm` the fractional-part
integral `-(σ+it) ∫_X^∞ {u} u^{-(σ+it)-1} du`.  Mathlib currently provides
the Dirichlet-series identity only for `Re s > 1`; the missing formal bridge is
this explicit continuation formula and its three elementary estimates on
`1/2 ≤ σ ≤ 2`, `|t| ≥ t₀`.
-/
structure ZetaRightHalfEulerMaclaurinComponentsAtHeight where
  t₀ : ℝ
  t₀_pos : 0 < t₀
  t₀_le_one : t₀ ≤ 1
  partialSum : ℝ → ℝ → ℂ
  poleTerm : ℝ → ℝ → ℂ
  tailTerm : ℝ → ℝ → ℂ
  C_sum : ℝ
  C_pole : ℝ
  C_tail : ℝ
  C_sum_nonneg : 0 ≤ C_sum
  C_pole_nonneg : 0 ≤ C_pole
  C_tail_nonneg : 0 ≤ C_tail
  decomposition :
    ∀ {σ t : ℝ}, (1 / 2 : ℝ) ≤ σ → σ ≤ 2 → t₀ ≤ |t| →
      riemannZeta (σ + Complex.I * t : ℂ) =
        partialSum σ t + poleTerm σ t + tailTerm σ t
  partial_sum_bound :
    ∀ {σ t : ℝ}, (1 / 2 : ℝ) ≤ σ → σ ≤ 2 → t₀ ≤ |t| →
      ‖partialSum σ t‖ ≤ C_sum * (|t| + 2)
  pole_bound :
    ∀ {σ t : ℝ}, (1 / 2 : ℝ) ≤ σ → σ ≤ 2 → t₀ ≤ |t| →
      ‖poleTerm σ t‖ ≤ C_pole * (|t| + 2)
  tail_bound :
    ∀ {σ t : ℝ}, (1 / 2 : ℝ) ≤ σ → σ ≤ 2 → t₀ ≤ |t| →
      ‖tailTerm σ t‖ ≤ C_tail * (|t| + 2)

/--
The Euler--Maclaurin component package is sufficient for the Stage V right-half
vertical-growth field.
-/
noncomputable def zetaRightHalfLinearVerticalGrowthAtHeight_of_eulerMaclaurinComponents
    (H : ZetaRightHalfEulerMaclaurinComponentsAtHeight) :
    ZetaRightHalfLinearVerticalGrowthAtHeight :=
  { t₀ := H.t₀
    t₀_pos := H.t₀_pos
    t₀_le_one := H.t₀_le_one
    C := H.C_sum + H.C_pole + H.C_tail
    C_nonneg := add_nonneg (add_nonneg H.C_sum_nonneg H.C_pole_nonneg) H.C_tail_nonneg
    right_half_growth := by
      intro σ t hσlow hσhigh ht
      have hsum := H.partial_sum_bound hσlow hσhigh ht
      have hpole := H.pole_bound hσlow hσhigh ht
      have htail := H.tail_bound hσlow hσhigh ht
      calc
        ‖riemannZeta (σ + Complex.I * t : ℂ)‖ =
            ‖H.partialSum σ t + H.poleTerm σ t + H.tailTerm σ t‖ := by
          rw [H.decomposition hσlow hσhigh ht]
        _ ≤ ‖H.partialSum σ t + H.poleTerm σ t‖ + ‖H.tailTerm σ t‖ :=
          norm_add_le _ _
        _ ≤ (‖H.partialSum σ t‖ + ‖H.poleTerm σ t‖) + ‖H.tailTerm σ t‖ := by
          exact add_le_add (norm_add_le _ _) le_rfl
        _ ≤ (H.C_sum * (|t| + 2) + H.C_pole * (|t| + 2)) +
            H.C_tail * (|t| + 2) := by
          gcongr
        _ = (H.C_sum + H.C_pole + H.C_tail) * (|t| + 2) := by
          ring }

/--
Stage V left-strip target: the functional-equation/gamma-factor transport
needed to extend the right-half vertical-growth bound from
`1/2 ≤ σ ≤ 2` to the frozen full strip `-1/2 ≤ σ ≤ 2`.
-/
structure ZetaLeftStripLinearVerticalGrowthAtHeight where
  t₀ : ℝ
  t₀_pos : 0 < t₀
  t₀_le_one : t₀ ≤ 1
  C : ℝ
  C_nonneg : 0 ≤ C
  left_strip_growth :
    ∀ {σ t : ℝ}, -(1 / 2 : ℝ) ≤ σ → σ ≤ (1 / 2 : ℝ) → t₀ ≤ |t| →
      ‖riemannZeta (σ + Complex.I * t : ℂ)‖ ≤ C * (|t| + 2)

/--
The two natural Stage V sub-bounds reassemble the exact frozen P2 package.
-/
noncomputable def zetaLinearVerticalGrowthInStripAtHeight_of_rightHalf_and_leftStrip
    (R : ZetaRightHalfLinearVerticalGrowthAtHeight)
    (S : ZetaLeftStripLinearVerticalGrowthAtHeight) :
    ZetaLinearVerticalGrowthInStripAtHeight :=
  { t₀ := max R.t₀ S.t₀
    t₀_pos := lt_of_lt_of_le R.t₀_pos (le_max_left _ _)
    t₀_le_one := max_le R.t₀_le_one S.t₀_le_one
    C := R.C + S.C
    C_nonneg := add_nonneg R.C_nonneg S.C_nonneg
    vertical_growth := by
      intro σ t hσlow hσhigh ht
      have htR : R.t₀ ≤ |t| := le_trans (le_max_left _ _) ht
      have htS : S.t₀ ≤ |t| := le_trans (le_max_right _ _) ht
      have hx_nonneg : 0 ≤ |t| + 2 := by positivity
      by_cases hhalf : (1 / 2 : ℝ) ≤ σ
      · have hR := R.right_half_growth hhalf hσhigh htR
        have hSterm : 0 ≤ S.C * (|t| + 2) :=
          mul_nonneg S.C_nonneg hx_nonneg
        nlinarith
      · have hσle : σ ≤ (1 / 2 : ℝ) := le_of_not_ge hhalf
        have hS := S.left_strip_growth hσlow hσle htS
        have hRterm : 0 ≤ R.C * (|t| + 2) :=
          mul_nonneg R.C_nonneg hx_nonneg
        nlinarith }

/--
P3 stop-gate after P2: the Borel--Caratheodory/Jensen and local
factorization step that turns a strip-growth input into the two
logarithmic-derivative estimates required by the repaired zero-free-region
pipeline.

The diagnostic script samples the P2 normalization
`|ζ(σ+it)| / (|t|+2)` on `-1/2 ≤ σ ≤ 2`, `|t| ≥ 1`; the maximum on the current
grid is approximately `0.418`.  The structure below does not use the numerical
sample as proof: it records the remaining complex-analysis construction once
the vertical-growth input is available.
-/
structure ZetaBorelJensenFactorizationAtHeight
    (G : ZetaLinearVerticalGrowthInStripAtHeight) where
  C : ℝ
  C_nonneg : 0 ≤ C
  log_derivative_bounds :
    (∀ {σ t : ℝ}, 1 < σ → σ ≤ 2 → G.t₀ ≤ |t| →
      (-deriv riemannZeta (σ + Complex.I * t : ℂ) /
          riemannZeta (σ + Complex.I * t : ℂ)).re ≤
        C * Real.log (|t| + 2)) ∧
    (∀ {σ β t : ℝ}, 1 < σ → σ ≤ 2 → β ≤ 1 → G.t₀ ≤ |t| →
      riemannZeta (β + Complex.I * t : ℂ) = 0 →
      (-deriv riemannZeta (σ + Complex.I * t : ℂ) /
          riemannZeta (σ + Complex.I * t : ℂ)).re ≤
        -1 / (σ - β) + C * Real.log (|t| + 2))

/--
Legacy assembled R4 package.  The newer P2/P3 split above refines this
monolithic stop-gate into the strip-growth input and the remaining
Borel--Jensen/factorization step.
-/
structure ZetaBorelJensenLogDerivDiscEstimateAtHeight where
  t₀ : ℝ
  t₀_pos : 0 < t₀
  t₀_le_one : t₀ ≤ 1
  C : ℝ
  C_nonneg : 0 ≤ C
  borel_jensen_bound :
    (∀ {σ t : ℝ}, 1 < σ → σ ≤ 2 → t₀ ≤ |t| →
      (-deriv riemannZeta (σ + Complex.I * t : ℂ) /
          riemannZeta (σ + Complex.I * t : ℂ)).re ≤
        C * Real.log (|t| + 2)) ∧
    (∀ {σ β t : ℝ}, 1 < σ → σ ≤ 2 → β ≤ 1 → t₀ ≤ |t| →
      riemannZeta (β + Complex.I * t : ℂ) = 0 →
      (-deriv riemannZeta (σ + Complex.I * t : ℂ) /
          riemannZeta (σ + Complex.I * t : ℂ)).re ≤
        -1 / (σ - β) + C * Real.log (|t| + 2))

/-- The P2/P3 split reassembles the existing R4 package. -/
noncomputable def zetaBorelJensenLogDerivDiscEstimateAtHeight_of_factorization
    {G : ZetaLinearVerticalGrowthInStripAtHeight}
    (H : ZetaBorelJensenFactorizationAtHeight G) :
    ZetaBorelJensenLogDerivDiscEstimateAtHeight :=
  { t₀ := G.t₀
    t₀_pos := G.t₀_pos
    t₀_le_one := G.t₀_le_one
    C := H.C
    C_nonneg := H.C_nonneg
    borel_jensen_bound := H.log_derivative_bounds }

/-- The R4 complex-analysis package is exactly enough to instantiate R1. -/
noncomputable def zetaLogDerivDiscBoundAtHeight_of_borelJensen
    (H : ZetaBorelJensenLogDerivDiscEstimateAtHeight) :
    ZetaLogDerivDiscBoundAtHeight :=
  { t₀ := H.t₀
    t₀_pos := H.t₀_pos
    t₀_le_one := H.t₀_le_one
    C := H.C
    C_nonneg := H.C_nonneg
    vertical_bound := H.borel_jensen_bound.1
    zero_contribution_bound := H.borel_jensen_bound.2 }

/--
R4 conditional headline: the named Borel/Jensen disc-control output feeds the
R3 repair and hence gives the frozen de la Vallee Poussin zero-free package.
-/
noncomputable def deLaValleePoussinZeroFreeRegion_of_borelJensenDiscEstimateAtHeight
    (H : ZetaBorelJensenLogDerivDiscEstimateAtHeight) :
    DeLaValleePoussinZeroFreeRegion :=
  deLaValleePoussinZeroFreeRegion_of_logDerivDiscBoundAtHeight
    (zetaLogDerivDiscBoundAtHeight_of_borelJensen H)

end RepairedDiscBound

end ZetaLogDerivativeDiscBound

end RH.Criteria.NymanBeurling.MobiusSummatory
