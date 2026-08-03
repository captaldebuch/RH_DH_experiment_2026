import RiemannHypothesis.Criteria.NymanBeurling.MobiusSummatory
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace RH.Criteria.NymanBeurling.MobiusSummatory

open Filter Finset Topology
open RH.Criteria.NymanBeurling.CutoffMobiusKernels
open scoped BigOperators

-- ---------------------------------------------------------------------------
-- H14M-A. de la Vallée Poussin zero-free-region API
-- ---------------------------------------------------------------------------

/--
The normalized de la Vallée Poussin zero-free strip used for the future
quantitative Mertens bound.

The `+ 2` keeps the logarithmic denominator positive uniformly, including on
the real axis.  The point `s = 1` needs no separate exclusion in this project
because Mathlib's `riemannZeta` is total and has a nonzero junk value there.
-/
noncomputable def deLaValleePoussinRegion (c : ℝ) (s : ℂ) : Prop :=
  1 - c / Real.log (|s.im| + 2) < s.re

lemma log_abs_im_add_two_pos (s : ℂ) :
    0 < Real.log (|s.im| + 2) := by
  exact Real.log_pos (by linarith [abs_nonneg s.im])

lemma deLaValleePoussinRegion_of_one_le_re {c : ℝ} (hc : 0 < c) {s : ℂ}
    (hs : 1 ≤ s.re) :
    deLaValleePoussinRegion c s := by
  unfold deLaValleePoussinRegion
  have hden : 0 < Real.log (|s.im| + 2) := log_abs_im_add_two_pos s
  have hquot : 0 < c / Real.log (|s.im| + 2) := div_pos hc hden
  linarith

/--
H14M-A frozen statement of the classical de la Vallée Poussin zero-free
region needed by the later effective Perron/contour-shift development.

This is intentionally only an API package: constructing it is the substantive
future analytic-number-theory work.  The constant is existential rather than
numeric, since the downstream `mertens_bound` only needs some positive
zero-free-region width.
-/
structure DeLaValleePoussinZeroFreeRegion where
  c : ℝ
  c_pos : 0 < c
  zeta_ne_zero :
    ∀ s : ℂ, deLaValleePoussinRegion c s → riemannZeta s ≠ 0

/--
The frozen package extends Mathlib's already-formalized closed half-plane
nonvanishing into the logarithmically thin region to the left of `Re s = 1`.
-/
lemma DeLaValleePoussinZeroFreeRegion.ne_zero_of_one_le_re
    (H : DeLaValleePoussinZeroFreeRegion) {s : ℂ} (hs : 1 ≤ s.re) :
    riemannZeta s ≠ 0 :=
  H.zeta_ne_zero s (deLaValleePoussinRegion_of_one_le_re H.c_pos hs)

-- ---------------------------------------------------------------------------
-- H14M-B0. Elementary 3-4-1 trigonometric ingredient
-- ---------------------------------------------------------------------------

/--
The elementary trigonometric inequality underlying the classical
de la Vallée Poussin `3-4-1` positivity trick.

This is only the real-variable algebraic ingredient.  The analytic use in the
zero-free-region proof still requires the von Mangoldt logarithmic-derivative
identity, pole control at `s = 1`, and uniform vertical growth estimates.
-/
lemma deLaValleePoussin_three_four_one_trig_nonneg (θ : ℝ) :
    0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [Real.cos_two_mul]
  nlinarith [sq_nonneg (Real.cos θ + 1)]

-- ---------------------------------------------------------------------------
-- H14M-B1. Public 3-4-1 positivity package
-- ---------------------------------------------------------------------------

section ThreeFourOnePositivity

open Complex

/--
Complex unit-circle form of the de la Vallée Poussin `3-4-1` positivity
identity.

For `‖z‖ = 1`, the left side is `2 * (z.re + 1)^2`.  This is the algebraic
core behind the nonnegative Euler-factor/logarithmic combinations used in the
classical zero-free-region argument.
-/
lemma deLaValleePoussin_three_four_one_unit_re_nonneg {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ 3 + 4 * z.re + (z ^ 2).re := by
  have hnormSq : z.re * z.re + z.im * z.im = 1 := by
    have hsq : ‖z‖ ^ 2 = (1 : ℝ) ^ 2 := by rw [hz]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at hsq
    norm_num at hsq
    simpa [sq] using hsq
  have hre : (z ^ 2).re = z.re * z.re - z.im * z.im := by
    simp [pow_two, Complex.mul_re]
  rw [hre]
  nlinarith [sq_nonneg (z.re + 1)]

/--
Reusable logarithmic Euler-factor positivity lemma.

This is the public project-facing analogue of Mathlib's private
`re_log_comb_nonneg'` lemma in `Mathlib.NumberTheory.LSeries.Nonvanishing`.
It packages the Taylor-series proof of the `3-4-1` trick for any real
`0 ≤ a < 1` and any unit complex number `z`.
-/
lemma deLaValleePoussin_re_log_comb_nonneg_unit {a : ℝ}
    (ha₀ : 0 ≤ a) (ha₁ : a < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ 3 * (-log (1 - a)).re + 4 * (-log (1 - a * z)).re +
      (-log (1 - a * z ^ 2)).re := by
  have hac₀ : ‖(a : ℂ)‖ < 1 := by
    simp only [Complex.norm_of_nonneg ha₀, ha₁]
  have hac₁ : ‖a * z‖ < 1 := by rwa [norm_mul, hz, mul_one]
  have hac₂ : ‖a * z ^ 2‖ < 1 := by rwa [norm_mul, norm_pow, hz, one_pow, mul_one]
  rw [← ((hasSum_re <| hasSum_taylorSeries_neg_log hac₀).mul_left 3).add
    ((hasSum_re <| hasSum_taylorSeries_neg_log hac₁).mul_left 4) |>.add
    (hasSum_re <| hasSum_taylorSeries_neg_log hac₂) |>.tsum_eq]
  refine tsum_nonneg fun n ↦ ?_
  simp only [← ofReal_pow, div_natCast_re, ofReal_re, mul_pow, mul_re, ofReal_im, zero_mul,
    sub_zero]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · simp only [← mul_div_assoc, ← add_div]
    refine div_nonneg ?_ n.cast_nonneg
    have hzpow : ‖z ^ n‖ = 1 := by rw [norm_pow, hz, one_pow]
    have hunit : 0 ≤ 3 + 4 * (z ^ n).re + ((z ^ n) ^ 2).re :=
      deLaValleePoussin_three_four_one_unit_re_nonneg hzpow
    have hpoweq : ((z ^ 2) ^ n).re = ((z ^ n) ^ 2).re := by
      congr 1
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [hpoweq]
    nlinarith [mul_nonneg (pow_nonneg ha₀ n) hunit]

end ThreeFourOnePositivity

-- ---------------------------------------------------------------------------
-- H14M-B2. Public von Mangoldt logarithmic-derivative wrappers
-- ---------------------------------------------------------------------------

section VonMangoldtLogDerivative

open Complex
open scoped ArithmeticFunction LSeries.notation

/--
Project-facing wrapper for Mathlib's von Mangoldt logarithmic-derivative
identity.

For `Re s > 1`, the Dirichlet series of the von Mangoldt function is the
negative logarithmic derivative of the Riemann zeta function.  This is the
analytic bridge used by the de la Vallée Poussin `3-4-1` argument.
-/
lemma deLaValleePoussin_vonMangoldt_LSeries_eq_neg_zeta_logDeriv
    {s : ℂ} (hs : 1 < s.re) :
    L ↗Λ s =
      - deriv riemannZeta s / riemannZeta s :=
  ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs

/--
The same identity in the orientation most often used when substituting
`ζ'/ζ` into the positivity argument.
-/
lemma deLaValleePoussin_neg_zeta_logDeriv_eq_vonMangoldt_LSeries
    {s : ℂ} (hs : 1 < s.re) :
    - deriv riemannZeta s / riemannZeta s =
      L ↗Λ s :=
  (deLaValleePoussin_vonMangoldt_LSeries_eq_neg_zeta_logDeriv hs).symm

/--
Termwise real-part expansion of the von Mangoldt L-series in the half-plane
`Re s > 1`.

This is the public project hook for the later cosine expansion
`Λ(n) n^{-σ} cos(t log n)`: that last syntactic simplification is separate
`cpow` algebra, while this lemma provides the justified interchange of real
part and infinite sum.
-/
lemma deLaValleePoussin_vonMangoldt_LSeries_re_eq_tsum_term_re
    {s : ℂ} (hs : 1 < s.re) :
    (L ↗Λ s).re =
      ∑' n : ℕ, (LSeries.term ↗Λ s n).re := by
  have hsum :
      HasSum (LSeries.term ↗Λ s) (L ↗Λ s) :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).hasSum
  exact (Complex.hasSum_re hsum).tsum_eq.symm

/--
Real-part form of the logarithmic-derivative identity, with the von Mangoldt
series expanded termwise.
-/
lemma deLaValleePoussin_neg_zeta_logDeriv_re_eq_tsum_term_re
    {s : ℂ} (hs : 1 < s.re) :
    (- deriv riemannZeta s / riemannZeta s).re =
      ∑' n : ℕ, (LSeries.term ↗Λ s n).re := by
  rw [deLaValleePoussin_neg_zeta_logDeriv_eq_vonMangoldt_LSeries hs,
    deLaValleePoussin_vonMangoldt_LSeries_re_eq_tsum_term_re hs]

/--
Real part of a negative complex power with positive real base.

This is the elementary `cpow` algebra behind the cosine form of the
von Mangoldt Dirichlet series.
-/
lemma deLaValleePoussin_real_cpow_neg_re {x σ t : ℝ} (hx : 0 < x) :
    (((x : ℂ) ^ (-(σ + Complex.I * t : ℂ))).re) =
      x ^ (-σ) * Real.cos (t * Real.log x) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
  have hlog : Complex.log (x : ℂ) = (Real.log x : ℂ) :=
    (Complex.ofReal_log hx.le).symm
  rw [hlog]
  simp [Complex.exp_re, Real.cos_neg, mul_comm]
  rw [Real.rpow_def_of_pos hx]
  ring

/--
Term-level cosine form of the von Mangoldt L-series at `s = σ + it`.
-/
lemma deLaValleePoussin_vonMangoldt_term_re_eq_cos
    {σ t : ℝ} {n : ℕ} (hn : n ≠ 0) :
    (LSeries.term ↗Λ (σ + Complex.I * t : ℂ) n).re =
      Λ n * (n : ℝ) ^ (-σ) * Real.cos (t * Real.log n) := by
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg]
  rw [← Complex.ofReal_natCast n]
  change ((((Λ n : ℂ) * (((n : ℝ) : ℂ) ^ (-(σ + Complex.I * t : ℂ)))).re) =
    Λ n * (n : ℝ) ^ (-σ) * Real.cos (t * Real.log n))
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hpow := deLaValleePoussin_real_cpow_neg_re
    (x := (n : ℝ)) (σ := σ) (t := t) hnpos
  calc
    (((Λ n : ℂ) * (((n : ℝ) : ℂ) ^ (-(σ + Complex.I * t : ℂ)))).re)
        = Λ n * ((((n : ℝ) : ℂ) ^ (-(σ + Complex.I * t : ℂ))).re) := by
          simp [Complex.mul_re]
    _ = Λ n * ((n : ℝ) ^ (-σ) * Real.cos (t * Real.log n)) := by
          rw [hpow]
    _ = Λ n * (n : ℝ) ^ (-σ) * Real.cos (t * Real.log n) := by ring

/--
Cosine expansion of the real part of `-ζ'/ζ(σ + it)` for `σ > 1`.
-/
lemma deLaValleePoussin_neg_zeta_logDeriv_re_eq_tsum_cos
    {σ t : ℝ} (hσ : 1 < σ) :
    (- deriv riemannZeta (σ + Complex.I * t : ℂ) /
        riemannZeta (σ + Complex.I * t : ℂ)).re =
      ∑' n : ℕ,
        if _ : n = 0 then 0
        else Λ n * (n : ℝ) ^ (-σ) * Real.cos (t * Real.log n) := by
  have hs : 1 < (σ + Complex.I * t : ℂ).re := by simpa using hσ
  rw [deLaValleePoussin_neg_zeta_logDeriv_re_eq_tsum_term_re hs]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · simp [hn, LSeries.term]
  · simpa [hn] using
      deLaValleePoussin_vonMangoldt_term_re_eq_cos (σ := σ) (t := t) hn

end VonMangoldtLogDerivative

-- ---------------------------------------------------------------------------
-- H14M-B3. Local zeta pole and hypothetical-zero contribution wrappers
-- ---------------------------------------------------------------------------

section ZetaLocalContributions

open Filter

/--
Project-facing residue statement for the simple pole of `ζ` at `s = 1`.

This is the local pole input available in Mathlib.  Turning it into the full
quantitative `ζ'/ζ` pole contribution used in a de la Vallée Poussin contour
argument still needs additional Laurent/log-derivative control.
-/
lemma deLaValleePoussin_zeta_residue_one :
    Tendsto (fun s : ℂ => (s - 1) * riemannZeta s)
      (nhdsWithin 1 ({1}ᶜ : Set ℂ)) (nhds 1) :=
  riemannZeta_residue_one

/--
The regular part `ζ(s) - 1/(s-1)` is locally bounded at `s = 1`.

This is a useful pole-neighborhood estimate already formalized in Mathlib.
It is not by itself the full logarithmic-derivative pole estimate.
-/
lemma deLaValleePoussin_zeta_regular_part_isBigO_one :
    Asymptotics.IsBigO (nhds (1 : ℂ))
      (fun s : ℂ => riemannZeta s - 1 / (s - 1))
      (fun _ : ℂ => (1 : ℂ)) :=
  isBigO_riemannZeta_sub_one_div

/--
Hypothetical simple-zero contribution to the logarithmic derivative of `ζ`.

If `ρ ≠ 1` is a simple zero of `ζ`, then the logarithmic residue of `ζ'/ζ`
at `ρ` is `1`.  This is the clean local contribution theorem currently
available from Mathlib's generic analytic simple-zero API.

The zero-free-region proof ultimately needs an arbitrary-multiplicity and
quantitative version; that stronger statement is deliberately not claimed here.
-/
lemma deLaValleePoussin_zeta_simple_zero_logDeriv_residue
    {ρ : ℂ} (hρ : ρ ≠ 1) (hz : riemannZeta ρ = 0)
    (hsimple : deriv riemannZeta ρ ≠ 0) :
    Tendsto (fun s : ℂ => (s - ρ) * logDeriv riemannZeta s)
      (nhdsWithin ρ ({ρ}ᶜ : Set ℂ)) (nhds 1) := by
  have han : AnalyticAt ℂ riemannZeta ρ := by
    exact analyticOn_riemannZeta ρ (by simpa [Set.mem_compl_iff] using hρ)
  exact han.tendsto_mul_logDeriv_simple_zero hz hsimple

end ZetaLocalContributions

lemma log_tail_term_le_telescoping (k : ℕ) :
    1 / (((k + 1 : ℕ) : ℝ) * Real.log (k + 2 : ℝ) ^ 2) ≤
      6 * (1 / Real.log (k + 2 : ℝ) - 1 / Real.log (k + 3 : ℝ)) := by
  have hk2 : (1 : ℝ) < (k : ℝ) + 2 := by norm_cast; omega
  have hlog2 : 0 < Real.log (k + 2 : ℝ) := Real.log_pos hk2
  have hlog3 : 0 < Real.log (k + 3 : ℝ) := Real.log_pos (by norm_cast; omega)
  have hratio : 0 < ((k + 3 : ℕ) : ℝ) / (k + 2 : ℝ) := by positivity
  have hdelta :
      1 / ((k + 3 : ℕ) : ℝ) ≤
        Real.log (k + 3 : ℝ) - Real.log (k + 2 : ℝ) := by
    calc
      1 / ((k + 3 : ℕ) : ℝ) =
          1 - ((((k + 3 : ℕ) : ℝ) / (k + 2 : ℝ))⁻¹) := by
            field_simp
            norm_num [Nat.cast_add]
      _ ≤ Real.log (((k + 3 : ℕ) : ℝ) / (k + 2 : ℝ)) :=
        Real.one_sub_inv_le_log_of_pos hratio
      _ = _ := by
        simpa only [Nat.cast_add, Nat.cast_ofNat] using
          (Real.log_div
            (x := ((k + 3 : ℕ) : ℝ)) (y := ((k + 2 : ℕ) : ℝ))
            (by positivity) (by positivity))
  have hlog3_le : Real.log (k + 3 : ℝ) ≤ 2 * Real.log (k + 2 : ℝ) := by
    have hnat : ((k + 3 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) ^ 2 := by
      norm_num
      nlinarith [sq_nonneg (k : ℝ)]
    have hlog := Real.strictMonoOn_log.monotoneOn
      (show (0 : ℝ) < (k + 3 : ℕ) by positivity)
      (show (0 : ℝ) < ((k + 2 : ℕ) : ℝ) ^ 2 by positivity) hnat
    rw [Real.log_pow] at hlog
    norm_num at hlog
    simpa using hlog
  have hk3_le : ((k + 3 : ℕ) : ℝ) ≤ 3 * ((k + 1 : ℕ) : ℝ) := by
    norm_num
    linarith
  rw [show 1 / Real.log (k + 2 : ℝ) - 1 / Real.log (k + 3 : ℝ) =
      (Real.log (k + 3 : ℝ) - Real.log (k + 2 : ℝ)) /
        (Real.log (k + 2 : ℝ) * Real.log (k + 3 : ℝ)) by
          field_simp]
  calc
    1 / (((k + 1 : ℕ) : ℝ) * Real.log (k + 2 : ℝ) ^ 2)
        ≤ 3 / (((k + 3 : ℕ) : ℝ) * Real.log (k + 2 : ℝ) ^ 2) := by
          apply (div_le_div_iff₀ (by positivity) (by positivity)).2
          have hmul := mul_le_mul_of_nonneg_right hk3_le
            (sq_nonneg (Real.log (k + 2 : ℝ)))
          nlinarith
    _ ≤ 6 / (((k + 3 : ℕ) : ℝ) *
          (Real.log (k + 2 : ℝ) * Real.log (k + 3 : ℝ))) := by
          apply (div_le_div_iff₀ (by positivity) (by positivity)).2
          have hmul := mul_le_mul_of_nonneg_left hlog3_le
            (mul_nonneg (by positivity) hlog2.le)
          nlinarith
    _ ≤ 6 * ((Real.log (k + 3 : ℝ) - Real.log (k + 2 : ℝ)) /
          (Real.log (k + 2 : ℝ) * Real.log (k + 3 : ℝ))) := by
          calc
            _ = 6 * (1 / ((k + 3 : ℕ) : ℝ)) /
                (Real.log (k + 2 : ℝ) * Real.log (k + 3 : ℝ)) := by
                  field_simp
            _ ≤ 6 * (Real.log (k + 3 : ℝ) - Real.log (k + 2 : ℝ)) /
                (Real.log (k + 2 : ℝ) * Real.log (k + 3 : ℝ)) := by
                  gcongr
            _ = _ := by ring
    _ = _ := by ring

lemma sum_Icc_sub_succ (a : ℕ → ℝ) (m n : ℕ) (hmn : m ≤ n) :
    (∑ k ∈ Finset.Icc m n, (a k - a (k + 1))) = a m - a (n + 1) := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      ring

lemma finite_log_tail_bound (N R : ℕ) :
    (∑ k ∈ Finset.Icc (N + 1) R,
      1 / (((k + 1 : ℕ) : ℝ) * Real.log (k + 2 : ℝ) ^ 2)) ≤
        6 / Real.log (N + 2 : ℝ) := by
  by_cases hNR : N + 1 ≤ R
  · calc
      _ ≤ ∑ k ∈ Finset.Icc (N + 1) R,
          6 * (1 / Real.log (k + 2 : ℝ) - 1 / Real.log (k + 3 : ℝ)) := by
            apply Finset.sum_le_sum
            intro k _
            exact log_tail_term_le_telescoping k
      _ = 6 * (1 / Real.log (N + 3 : ℝ) - 1 / Real.log (R + 3 : ℝ)) := by
            rw [← Finset.mul_sum]
            have htel := sum_Icc_sub_succ (fun k => 1 / Real.log (k + 2 : ℝ))
              (N + 1) R hNR
            congr 1
            convert htel using 1 <;> norm_num [Nat.cast_add] <;> ring
      _ ≤ 6 / Real.log (N + 3 : ℝ) := by
            have hlog : 0 < Real.log (R + 3 : ℝ) := Real.log_pos (by norm_cast; omega)
            have hnonneg : 0 ≤ 1 / Real.log (R + 3 : ℝ) := by positivity
            calc
              6 * (1 / Real.log (N + 3 : ℝ) - 1 / Real.log (R + 3 : ℝ)) ≤
                  6 * (1 / Real.log (N + 3 : ℝ)) := by nlinarith
              _ = _ := by ring
      _ ≤ 6 / Real.log (N + 2 : ℝ) := by
            have hlogN2 : 0 < Real.log (N + 2 : ℝ) := Real.log_pos (by norm_cast; omega)
            have hN2pos : (0 : ℝ) < (N : ℝ) + 2 := by positivity
            have hN3pos : (0 : ℝ) < (N : ℝ) + 3 := by positivity
            have hmono : Real.log (N + 2 : ℝ) ≤ Real.log (N + 3 : ℝ) := by
              exact Real.strictMonoOn_log.monotoneOn hN2pos hN3pos (by norm_num)
            simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left
              (one_div_le_one_div_of_le hlogN2 hmono) (show (0 : ℝ) ≤ 6 by norm_num)
  · simp [Finset.Icc_eq_empty (by omega)]
    exact div_nonneg (by norm_num) (Real.log_pos (by norm_cast; omega)).le

lemma finite_log_cubed_tail_bound (N R : ℕ) :
    (∑ k ∈ Finset.Icc (N + 1) R,
      1 / (((k + 1 : ℕ) : ℝ) * Real.log (k + 2 : ℝ) ^ 3)) ≤
        12 / Real.log (N + 2 : ℝ) := by
  calc
    _ ≤ ∑ k ∈ Finset.Icc (N + 1) R,
        2 * (1 / (((k + 1 : ℕ) : ℝ) * Real.log (k + 2 : ℝ) ^ 2)) := by
          apply Finset.sum_le_sum
          intro k _
          have hlog : (1 / 2 : ℝ) ≤ Real.log (k + 2 : ℝ) := by
            have hbase := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
            have hk2pos : (0 : ℝ) < (k : ℝ) + 2 := by positivity
            have hmono : Real.log (2 : ℝ) ≤ Real.log (k + 2 : ℝ) := by
              exact Real.strictMonoOn_log.monotoneOn (by norm_num) hk2pos (by norm_num)
            norm_num at hbase
            linarith
          have hlogpos : 0 < Real.log (k + 2 : ℝ) := Real.log_pos (by norm_cast; omega)
          field_simp
          nlinarith
    _ = 2 * (∑ k ∈ Finset.Icc (N + 1) R,
        1 / (((k + 1 : ℕ) : ℝ) * Real.log (k + 2 : ℝ) ^ 2)) := by
          rw [Finset.mul_sum]
    _ ≤ 2 * (6 / Real.log (N + 2 : ℝ)) := by
          gcongr
          exact finite_log_tail_bound N R
    _ = _ := by ring

noncomputable def mobiusOverKPartial (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N,
    ((ArithmeticFunction.moebius k : ℤ) : ℝ) / (k : ℝ)

noncomputable def mobiusLogOverKPartial (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N,
    ((ArithmeticFunction.moebius k : ℤ) : ℝ) * Real.log (k : ℝ) / (k : ℝ)

-- ---------------------------------------------------------------------------
-- H14 Axer step. Exact finite hyperbola identities
-- ---------------------------------------------------------------------------

/-- The divisor sum of the integer-valued Möbius function. -/
lemma sum_moebius_divisors_int (n : ℕ) :
    (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) =
      if n = 1 then 1 else 0 := by
  calc
    _ = (ArithmeticFunction.moebius *
          (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) n :=
      ArithmeticFunction.coe_mul_zeta_apply.symm
    _ = (1 : ArithmeticFunction ℤ) n := by
      rw [ArithmeticFunction.moebius_mul_coe_zeta]
    _ = _ := ArithmeticFunction.one_apply

/--
The exact finite Möbius hyperbola identity
`∑_{k≤N} μ(k) ⌊N/k⌋ = 1`.

The proof increments `N`, uses `Nat.succ_div`, and identifies the new terms
with the divisor sum of the Möbius function.
-/
theorem mobius_floor_hyperbola_identity (N : ℕ) (hN : 1 ≤ N) :
    (∑ k ∈ Finset.Icc 1 N,
      ArithmeticFunction.moebius k * ((N / k : ℕ) : ℤ)) = 1 := by
  induction N, hN using Nat.le_induction with
  | base => norm_num [ArithmeticFunction.moebius]
  | succ N hN ih =>
      have hNpos : 0 < N + 1 := by omega
      have hdivisors :
          Finset.filter (fun k : ℕ => k ∣ N + 1) (Finset.Icc 1 (N + 1)) =
            (N + 1).divisors := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
        constructor
        · rintro ⟨_, hk⟩
          exact ⟨hk, hNpos.ne'⟩
        · rintro ⟨hk, _⟩
          exact ⟨⟨Nat.pos_of_dvd_of_pos hk hNpos,
            Nat.le_of_dvd hNpos hk⟩, hk⟩
      have hdivsum :
          (∑ k ∈ Finset.Icc 1 (N + 1),
              ArithmeticFunction.moebius k *
                (if k ∣ N + 1 then (1 : ℤ) else 0)) = 0 := by
        calc
          _ = ∑ k ∈ Finset.Icc 1 (N + 1),
                if k ∣ N + 1 then ArithmeticFunction.moebius k else 0 := by
              apply Finset.sum_congr rfl
              intro k _
              split <;> simp_all
          _ = ∑ k ∈ Finset.filter (fun k : ℕ => k ∣ N + 1)
                (Finset.Icc 1 (N + 1)), ArithmeticFunction.moebius k := by
              rw [Finset.sum_filter]
          _ = 0 := by
              rw [hdivisors, sum_moebius_divisors_int]
              split <;> simp_all
      have hold :
          (∑ k ∈ Finset.Icc 1 (N + 1),
              ArithmeticFunction.moebius k * ((N / k : ℕ) : ℤ)) = 1 := by
        rw [Finset.sum_Icc_succ_top (by omega)]
        have hlast : ((N / (N + 1) : ℕ) : ℤ) = 0 := by
          rw [Nat.div_eq_of_lt (by omega)]
          norm_num
        rw [hlast, mul_zero, add_zero]
        exact ih
      calc
        (∑ k ∈ Finset.Icc 1 (N + 1),
            ArithmeticFunction.moebius k * (((N + 1) / k : ℕ) : ℤ)) =
            ∑ k ∈ Finset.Icc 1 (N + 1),
              ArithmeticFunction.moebius k * (((N / k : ℕ) : ℤ) +
                if k ∣ N + 1 then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro k _
              rw [Nat.succ_div]
              push_cast
              rfl
        _ = (∑ k ∈ Finset.Icc 1 (N + 1),
              ArithmeticFunction.moebius k * ((N / k : ℕ) : ℤ)) +
            ∑ k ∈ Finset.Icc 1 (N + 1),
              ArithmeticFunction.moebius k *
                (if k ∣ N + 1 then (1 : ℤ) else 0) := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro k _
              ring
        _ = 1 := by rw [hold, hdivsum, add_zero]

/-- The fractional-part sum occurring in the quantitative Axer identity. -/
noncomputable def mobiusFractHyperbolaSum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N,
    ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
      Int.fract ((N : ℝ) / (k : ℝ))

lemma nat_div_add_fract_natCast_div (N k : ℕ) :
    ((N / k : ℕ) : ℝ) + Int.fract ((N : ℝ) / (k : ℝ)) =
      (N : ℝ) / (k : ℝ) := by
  have hnonneg : 0 ≤ (N : ℝ) / (k : ℝ) := by positivity
  calc
    ((N / k : ℕ) : ℝ) + Int.fract ((N : ℝ) / (k : ℝ)) =
        (⌊(N : ℝ) / (k : ℝ)⌋₊ : ℝ) +
          Int.fract ((N : ℝ) / (k : ℝ)) := by
            rw [Nat.floor_div_eq_div]
    _ = ((⌊(N : ℝ) / (k : ℝ)⌋ : ℤ) : ℝ) +
          Int.fract ((N : ℝ) / (k : ℝ)) := by
            rw [natCast_floor_eq_intCast_floor hnonneg]
    _ = _ := Int.floor_add_fract _

/--
Exact floor/fractional-part decomposition of the Möbius hyperbola identity:
`N * ∑_{k≤N} μ(k)/k = 1 + ∑_{k≤N} μ(k) {N/k}`.
-/
theorem mobius_overK_fract_decomposition (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) * mobiusOverKPartial N = 1 + mobiusFractHyperbolaSum N := by
  have hhyperbola :
      (∑ k ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
          ((N / k : ℕ) : ℝ)) = 1 := by
    have h := congrArg (fun z : ℤ => (z : ℝ))
      (mobius_floor_hyperbola_identity N hN)
    push_cast at h
    exact h
  unfold mobiusOverKPartial mobiusFractHyperbolaSum
  calc
    (N : ℝ) *
        (∑ k ∈ Finset.Icc 1 N,
          ((ArithmeticFunction.moebius k : ℤ) : ℝ) / (k : ℝ)) =
        ∑ k ∈ Finset.Icc 1 N,
          ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
            (((N / k : ℕ) : ℝ) + Int.fract ((N : ℝ) / (k : ℝ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [nat_div_add_fract_natCast_div]
      ring
    _ = (∑ k ∈ Finset.Icc 1 N,
          ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
            ((N / k : ℕ) : ℝ)) +
        ∑ k ∈ Finset.Icc 1 N,
          ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
            Int.fract ((N : ℝ) / (k : ℝ)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [hhyperbola]

/-- Finite Abel summation on an arbitrary natural interval. -/
theorem finite_abel_sum_Icc_mul_eq_endpoint_add_sum_partial_from
    (a b : ℕ → ℝ) (A B : ℕ) (hAB : A ≤ B) :
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

lemma sum_Icc_sub_succ_add_endpoint (b : ℕ → ℝ) (A B : ℕ) (hAB : A ≤ B) :
    b (B + 1) + ∑ k ∈ Finset.Icc A B, (b k - b (k + 1)) = b A := by
  induction B, hAB using Nat.le_induction with
  | base => simp
  | succ B hAB ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      linarith

/--
Abel's inequality on a finite interval for a nonnegative decreasing weight.

If every local partial sum of `a` is bounded in absolute value by `D`, and
`b` decreases from a value at most `1`, then the weighted block sum is also
bounded by `D`.
-/
theorem abs_sum_Icc_mul_le_of_partial_sum_le_of_antitone
    (a b : ℕ → ℝ) (A B : ℕ) (D : ℝ)
    (hAB : A ≤ B) (hD : 0 ≤ D)
    (hb_nonneg : ∀ k ∈ Finset.Icc A (B + 1), 0 ≤ b k)
    (hb_antitone : ∀ k ∈ Finset.Icc A B, b (k + 1) ≤ b k)
    (hbA : b A ≤ 1)
    (hpartial : ∀ k ∈ Finset.Icc A B,
      |∑ j ∈ Finset.Icc A k, a j| ≤ D) :
    |∑ k ∈ Finset.Icc A B, a k * b k| ≤ D := by
  have hBmem : B ∈ Finset.Icc A B := Finset.mem_Icc.mpr ⟨hAB, le_rfl⟩
  have hB1mem : B + 1 ∈ Finset.Icc A (B + 1) :=
    Finset.mem_Icc.mpr ⟨hAB.trans (by omega), le_rfl⟩
  have hAmem : A ∈ Finset.Icc A (B + 1) :=
    Finset.mem_Icc.mpr ⟨le_rfl, hAB.trans (by omega)⟩
  have hdiff_nonneg :
      ∀ k ∈ Finset.Icc A B, 0 ≤ b k - b (k + 1) := by
    intro k hk
    exact sub_nonneg.mpr (hb_antitone k hk)
  rw [finite_abel_sum_Icc_mul_eq_endpoint_add_sum_partial_from a b A B hAB]
  calc
    |(∑ j ∈ Finset.Icc A B, a j) * b (B + 1) +
        ∑ k ∈ Finset.Icc A B,
          (∑ j ∈ Finset.Icc A k, a j) * (b k - b (k + 1))| ≤
        |(∑ j ∈ Finset.Icc A B, a j) * b (B + 1)| +
          |∑ k ∈ Finset.Icc A B,
            (∑ j ∈ Finset.Icc A k, a j) * (b k - b (k + 1))| :=
      abs_add_le _ _
    _ ≤ D * b (B + 1) +
        ∑ k ∈ Finset.Icc A B, D * (b k - b (k + 1)) := by
      gcongr
      · rw [abs_mul, abs_of_nonneg (hb_nonneg _ hB1mem)]
        exact mul_le_mul_of_nonneg_right (hpartial B hBmem)
          (hb_nonneg _ hB1mem)
      · calc
          |∑ k ∈ Finset.Icc A B,
              (∑ j ∈ Finset.Icc A k, a j) * (b k - b (k + 1))| ≤
              ∑ k ∈ Finset.Icc A B,
                |(∑ j ∈ Finset.Icc A k, a j) * (b k - b (k + 1))| :=
            abs_sum_le_sum_abs _ _
          _ ≤ ∑ k ∈ Finset.Icc A B, D * (b k - b (k + 1)) := by
            apply Finset.sum_le_sum
            intro k hk
            rw [abs_mul, abs_of_nonneg (hdiff_nonneg k hk)]
            exact mul_le_mul_of_nonneg_right (hpartial k hk)
              (hdiff_nonneg k hk)
    _ = D * b A := by
      rw [← Finset.mul_sum, ← mul_add,
        sum_Icc_sub_succ_add_endpoint b A B hAB]
    _ ≤ D := by
      nlinarith [hb_nonneg A hAmem]

lemma nat_div_eq_iff_mem_Icc_div (N q k : ℕ) (hk : 0 < k) (hq : 0 < q) :
    N / k = q ↔ k ∈ Finset.Icc (N / (q + 1) + 1) (N / q) := by
  constructor
  · intro heq
    have hlower : N / (q + 1) < k := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      have : N / k < q + 1 := by omega
      simpa [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hk).mp this
    have hupper : k ≤ N / q := by
      rw [Nat.le_div_iff_mul_le hq]
      have : q ≤ N / k := by omega
      simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hk).mp this
    exact Finset.mem_Icc.mpr ⟨by omega, hupper⟩
  · intro hmem
    rcases Finset.mem_Icc.mp hmem with ⟨hlower, hupper⟩
    have hlt : N / k < q + 1 := by
      rw [Nat.div_lt_iff_lt_mul hk]
      have : N < k * (q + 1) :=
        (Nat.div_lt_iff_lt_mul (by omega)).mp (by omega)
      simpa [Nat.mul_comm] using this
    have hle : q ≤ N / k := by
      rw [Nat.le_div_iff_mul_le hk]
      have : k * q ≤ N :=
        (Nat.le_div_iff_mul_le hq).mp hupper
      simpa [Nat.mul_comm] using this
    omega

/-- The contribution from the block on which `⌊N/k⌋ = q`. -/
noncomputable def mobiusFractBlock (N q : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc (N / (q + 1) + 1) (N / q),
    ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
      Int.fract ((N : ℝ) / (k : ℝ))

lemma mobiusFractBlock_eq_filtered_tail (N Q q : ℕ)
    (hq : 1 ≤ q) (hqQ : q ≤ Q) :
    mobiusFractBlock N q =
      ∑ k ∈ Finset.filter (fun k : ℕ => N / k = q)
        (Finset.Icc (N / (Q + 1) + 1) N),
          ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
            Int.fract ((N : ℝ) / (k : ℝ)) := by
  unfold mobiusFractBlock
  have hsets :
      Finset.Icc (N / (q + 1) + 1) (N / q) =
        Finset.filter (fun k : ℕ => N / k = q)
          (Finset.Icc (N / (Q + 1) + 1) N) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_filter]
    constructor
    · intro hkblock
      have hkpos : 0 < k := lt_of_lt_of_le (Nat.zero_lt_succ _) hkblock.1
      have heq := (nat_div_eq_iff_mem_Icc_div N q k hkpos (by omega)).mpr
        (Finset.mem_Icc.mpr hkblock)
      have hKle : N / (Q + 1) ≤ N / (q + 1) :=
        Nat.div_le_div_left (by omega) (by omega)
      exact ⟨⟨by omega, hkblock.2.trans (Nat.div_le_self N q)⟩, heq⟩
    · rintro ⟨hktail, heq⟩
      have hkpos : 0 < k :=
        lt_of_lt_of_le (Nat.zero_lt_succ _) hktail.1
      exact Finset.mem_Icc.mp
        ((nat_div_eq_iff_mem_Icc_div N q k hkpos (by omega)).mp heq)
  rw [hsets]

/-- The tail above `N/(Q+1)` is the exact sum of the first `Q` floor blocks. -/
lemma mobiusFractTail_eq_sum_blocks (N Q : ℕ) :
    (∑ k ∈ Finset.Icc (N / (Q + 1) + 1) N,
      ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
        Int.fract ((N : ℝ) / (k : ℝ))) =
      ∑ q ∈ Finset.Icc 1 Q, mobiusFractBlock N q := by
  let s := Finset.Icc (N / (Q + 1) + 1) N
  let f := fun k : ℕ =>
    ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
      Int.fract ((N : ℝ) / (k : ℝ))
  have hmaps : ∀ k ∈ s, N / k ∈ Finset.Icc 1 Q := by
    intro k hk
    have hkIcc : k ∈ Finset.Icc (N / (Q + 1) + 1) N := hk
    rcases Finset.mem_Icc.mp hkIcc with ⟨hKk, hkN⟩
    have hkpos : 0 < k := lt_of_lt_of_le (Nat.zero_lt_succ _) hKk
    have hlower : 1 ≤ N / k := by
      rw [Nat.le_div_iff_mul_le hkpos]
      simpa using hkN
    have hupper : N / k ≤ Q := by
      have hlt : N / k < Q + 1 := by
        rw [Nat.div_lt_iff_lt_mul hkpos]
        have : N < k * (Q + 1) :=
          (Nat.div_lt_iff_lt_mul (by omega)).mp (by omega)
        simpa [Nat.mul_comm] using this
      omega
    exact Finset.mem_Icc.mpr ⟨hlower, hupper⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps f
  change (∑ k ∈ s, f k) = ∑ q ∈ Finset.Icc 1 Q, mobiusFractBlock N q
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro q hq
  rcases Finset.mem_Icc.mp hq with ⟨hq1, hqQ⟩
  exact (mobiusFractBlock_eq_filtered_tail N Q q hq1 hqQ).symm

lemma sum_Icc_succ_eq_sum_Icc_one_sub (a : ℕ → ℝ) (K R : ℕ) (hKR : K ≤ R) :
    (∑ k ∈ Finset.Icc (K + 1) R, a k) =
      (∑ k ∈ Finset.Icc 1 R, a k) - ∑ k ∈ Finset.Icc 1 K, a k := by
  induction R, hKR using Nat.le_induction with
  | base => simp
  | succ R hKR ih =>
      rw [Finset.sum_Icc_succ_top (by omega),
        Finset.sum_Icc_succ_top (by omega), ih]
      ring

/--
A single floor block is controlled by twice a uniform Mertens bound on the
surrounding interval.
-/
lemma abs_mobiusFractBlock_le_of_summatory_bound
    (N q : ℕ) (D : ℝ) (hq : 1 ≤ q) (hD : 0 ≤ D)
    (hM : ∀ k ∈ Finset.Icc (N / (q + 1)) N,
      |mobiusSummatory k| ≤ D) :
    |mobiusFractBlock N q| ≤ 2 * D := by
  let A := N / (q + 1) + 1
  let B := N / q
  by_cases hAB : A ≤ B
  · let weight := fun k : ℕ =>
      if k ≤ B then Int.fract ((N : ℝ) / (k : ℝ)) else 0
    have hsum : mobiusFractBlock N q =
        ∑ k ∈ Finset.Icc A B,
          ((ArithmeticFunction.moebius k : ℤ) : ℝ) * weight k := by
      unfold mobiusFractBlock
      apply Finset.sum_congr
      · rfl
      · intro k hk
        simp [weight, B, Finset.mem_Icc.mp hk |>.2]
    rw [hsum]
    apply abs_sum_Icc_mul_le_of_partial_sum_le_of_antitone
      (fun k : ℕ => ((ArithmeticFunction.moebius k : ℤ) : ℝ))
      weight A B (2 * D) hAB (by positivity)
    · intro k hk
      simp only [weight]
      split
      · exact Int.fract_nonneg _
      · exact le_rfl
    · intro k hk
      rcases Finset.mem_Icc.mp hk with ⟨hAk, hkB⟩
      have hApos : 0 < A := by simp [A]
      have hkpos : 0 < k := hApos.trans_le hAk
      simp only [weight, if_pos hkB]
      by_cases hksucc : k + 1 ≤ B
      · rw [if_pos hksucc]
        have hkblock : k ∈ Finset.Icc (N / (q + 1) + 1) (N / q) := by
          simpa [A, B] using Finset.mem_Icc.mpr ⟨hAk, hkB⟩
        have hksuccblock :
            k + 1 ∈ Finset.Icc (N / (q + 1) + 1) (N / q) := by
          simpa [A, B] using
            Finset.mem_Icc.mpr ⟨hAk.trans (Nat.le_succ k), hksucc⟩
        have hkfloor :=
          (nat_div_eq_iff_mem_Icc_div N q k hkpos (by omega)).mpr hkblock
        have hksuccfloor :=
          (nat_div_eq_iff_mem_Icc_div N q (k + 1) (by omega) (by omega)).mpr
            hksuccblock
        have hkfract := nat_div_add_fract_natCast_div N k
        have hksuccfract := nat_div_add_fract_natCast_div N (k + 1)
        norm_cast at hkfloor hksuccfloor
        rw [hkfloor] at hkfract
        rw [hksuccfloor] at hksuccfract
        have hdiv : (N : ℝ) / (k + 1 : ℕ) ≤ (N : ℝ) / k := by
          gcongr
          norm_num
        linarith
      · rw [if_neg hksucc]
        exact Int.fract_nonneg _
    · simp only [weight, if_pos hAB]
      exact (Int.fract_lt_one _).le
    · intro k hk
      rcases Finset.mem_Icc.mp hk with ⟨hAk, hkB⟩
      have hKk : N / (q + 1) ≤ k := by simp [A] at hAk; omega
      have hkN : k ≤ N := by
        exact hkB.trans (by simpa [B] using Nat.div_le_self N q)
      have hlocal :
          (∑ j ∈ Finset.Icc A k,
            ((ArithmeticFunction.moebius j : ℤ) : ℝ)) =
            mobiusSummatory k - mobiusSummatory (N / (q + 1)) := by
        unfold mobiusSummatory
        simpa [A] using sum_Icc_succ_eq_sum_Icc_one_sub
          (fun j : ℕ => ((ArithmeticFunction.moebius j : ℤ) : ℝ))
          (N / (q + 1)) k hKk
      rw [hlocal]
      calc
        |mobiusSummatory k - mobiusSummatory (N / (q + 1))| ≤
            |mobiusSummatory k| + |mobiusSummatory (N / (q + 1))| :=
          abs_sub _ _
        _ ≤ D + D := add_le_add
          (hM k (Finset.mem_Icc.mpr ⟨hKk, hkN⟩))
          (hM (N / (q + 1))
            (Finset.mem_Icc.mpr ⟨le_rfl, Nat.div_le_self N (q + 1)⟩))
        _ = 2 * D := by ring
  · have hempty : Finset.Icc (N / (q + 1) + 1) (N / q) = ∅ :=
      Finset.Icc_eq_empty (by simpa [A, B] using hAB)
    simp [mobiusFractBlock, hempty, hD]

lemma abs_mobiusFractHead_le (N K : ℕ) :
    |∑ k ∈ Finset.Icc 1 K,
      ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
        Int.fract ((N : ℝ) / (k : ℝ))| ≤ K := by
  calc
    |∑ k ∈ Finset.Icc 1 K,
        ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
          Int.fract ((N : ℝ) / (k : ℝ))| ≤
        ∑ k ∈ Finset.Icc 1 K,
          |((ArithmeticFunction.moebius k : ℤ) : ℝ) *
            Int.fract ((N : ℝ) / (k : ℝ))| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.Icc 1 K, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul, abs_of_nonneg
        (Int.fract_nonneg ((N : ℝ) / (k : ℝ)))]
      have hmu : |((ArithmeticFunction.moebius k : ℤ) : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := k)
      calc
        |((ArithmeticFunction.moebius k : ℤ) : ℝ)| *
            Int.fract ((N : ℝ) / (k : ℝ)) ≤
            1 * Int.fract ((N : ℝ) / (k : ℝ)) :=
          mul_le_mul_of_nonneg_right hmu (Int.fract_nonneg _)
        _ ≤ 1 := by simpa using (Int.fract_lt_one _).le
    _ ≤ K := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      have hcard : (Finset.Icc 1 K).card ≤ K := by
        rw [Nat.card_Icc]
        omega
      exact_mod_cast hcard

lemma mobiusFractHyperbolaSum_eq_head_add_tail (N K : ℕ) (hKN : K ≤ N) :
    mobiusFractHyperbolaSum N =
      (∑ k ∈ Finset.Icc 1 K,
        ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
          Int.fract ((N : ℝ) / (k : ℝ))) +
      ∑ k ∈ Finset.Icc (K + 1) N,
        ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
          Int.fract ((N : ℝ) / (k : ℝ)) := by
  unfold mobiusFractHyperbolaSum
  have htail := sum_Icc_succ_eq_sum_Icc_one_sub
    (fun k : ℕ => ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
      Int.fract ((N : ℝ) / (k : ℝ))) K N hKN
  linarith

/--
Quantitative and boundary-value inputs for the linear Mobius/Dirichlet bridge.
This isolates the still-unformalized classical analytic number theory from the
mechanical Abel-summation consequences used by Phase 14.
-/
structure ClassicalMertensAPI where
  C_M : ℝ
  C_L : ℝ
  C_M_pos : 0 < C_M
  C_L_pos : 0 < C_L
  mertens_bound :
    ∀ N : ℕ,
      |mobiusSummatory N| ≤ C_M * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 3
  mobiusLogSummatory_bound :
    ∀ N : ℕ,
      |mobiusLogSummatory N| ≤ C_L * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2
  mobius_sum_zero : Tendsto mobiusOverKPartial atTop (𝓝 0)
  mobiusLog_sum_neg_one : Tendsto mobiusLogOverKPartial atTop (𝓝 (-1))

/--
Single classical de la Vallée Poussin decay input for the Mertens summatory
function.

This is the intended final quantitative H14 debt: proving this structure from
the zero-free region/effective Perron contour argument is classical analytic
number theory.  The remaining wrappers below convert it into the polynomial-log
Mertens bound used by the finite Abel estimates.
-/
structure ClassicalMertensDecay where
  C : ℝ
  a : ℝ
  C_pos : 0 < C
  a_pos : 0 < a
  mertens_decay :
    ∀ N : ℕ, 2 ≤ N →
      |mobiusSummatory N| ≤ C * (N : ℝ) * Real.exp (-a * Real.sqrt (Real.log N))

lemma abs_mobiusFractTail_le_of_decay (H : ClassicalMertensDecay)
    (N Q : ℕ) (hK : 2 ≤ N / (Q + 1)) :
    |∑ k ∈ Finset.Icc (N / (Q + 1) + 1) N,
      ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
        Int.fract ((N : ℝ) / (k : ℝ))| ≤
      2 * H.C * (Q : ℝ) * (N : ℝ) *
        Real.exp (-H.a *
          Real.sqrt (Real.log ((N / (Q + 1) : ℕ) : ℝ))) := by
  let K := N / (Q + 1)
  let D := H.C * (N : ℝ) *
    Real.exp (-H.a * Real.sqrt (Real.log (K : ℝ)))
  have hD : 0 ≤ D := by
    exact mul_nonneg (mul_nonneg H.C_pos.le (by positivity)) (Real.exp_pos _).le
  have hblock : ∀ q ∈ Finset.Icc 1 Q, |mobiusFractBlock N q| ≤ 2 * D := by
    intro q hq
    rcases Finset.mem_Icc.mp hq with ⟨hq1, hqQ⟩
    apply abs_mobiusFractBlock_le_of_summatory_bound N q D hq1 hD
    intro k hk
    rcases Finset.mem_Icc.mp hk with ⟨hlower, hkN⟩
    have hKlower : K ≤ N / (q + 1) := by
      exact Nat.div_le_div_left (by omega) (by omega)
    have hKk : K ≤ k := hKlower.trans hlower
    have hK2 : 2 ≤ K := by simpa [K] using hK
    have hk2 : 2 ≤ k := hK2.trans hKk
    have hKpos : 0 < (K : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) (by simpa [K] using hK))
    have hlog : Real.log (K : ℝ) ≤ Real.log (k : ℝ) := by
      exact Real.log_le_log hKpos (by exact_mod_cast hKk)
    have hsqrt : Real.sqrt (Real.log (K : ℝ)) ≤
        Real.sqrt (Real.log (k : ℝ)) := Real.sqrt_le_sqrt hlog
    have hexp : Real.exp (-H.a * Real.sqrt (Real.log (k : ℝ))) ≤
        Real.exp (-H.a * Real.sqrt (Real.log (K : ℝ))) := by
      apply Real.exp_le_exp.mpr
      nlinarith [H.a_pos]
    calc
      |mobiusSummatory k| ≤ H.C * (k : ℝ) *
          Real.exp (-H.a * Real.sqrt (Real.log k)) := H.mertens_decay k hk2
      _ ≤ H.C * (N : ℝ) *
          Real.exp (-H.a * Real.sqrt (Real.log k)) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hkN) H.C_pos.le
        · exact (Real.exp_pos _).le
      _ ≤ D := by
        unfold D
        exact mul_le_mul_of_nonneg_left hexp
          (mul_nonneg H.C_pos.le (by positivity))
  rw [mobiusFractTail_eq_sum_blocks]
  calc
    |∑ q ∈ Finset.Icc 1 Q, mobiusFractBlock N q| ≤
        ∑ q ∈ Finset.Icc 1 Q, |mobiusFractBlock N q| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _q ∈ Finset.Icc 1 Q, 2 * D := by
      exact Finset.sum_le_sum hblock
    _ = 2 * D * (Q : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : (Finset.Icc 1 Q).card = Q := by simp
      rw [hcard]
      ring
    _ = _ := by simp [D, K]; ring

/--
Abstract-cutoff form of the quantitative Axer fractional-part estimate.
-/
lemma abs_mobiusFractHyperbolaSum_le_cutoff (H : ClassicalMertensDecay)
    (N Q : ℕ) (hK : 2 ≤ N / (Q + 1)) :
    |mobiusFractHyperbolaSum N| ≤
      ((N / (Q + 1) : ℕ) : ℝ) +
        2 * H.C * (Q : ℝ) * (N : ℝ) *
          Real.exp (-H.a *
            Real.sqrt (Real.log ((N / (Q + 1) : ℕ) : ℝ))) := by
  let K := N / (Q + 1)
  have hKN : K ≤ N := by exact Nat.div_le_self N (Q + 1)
  rw [mobiusFractHyperbolaSum_eq_head_add_tail N K hKN]
  calc
    |(∑ k ∈ Finset.Icc 1 K,
        ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
          Int.fract ((N : ℝ) / (k : ℝ))) +
      ∑ k ∈ Finset.Icc (K + 1) N,
        ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
          Int.fract ((N : ℝ) / (k : ℝ))| ≤
        |∑ k ∈ Finset.Icc 1 K,
          ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
            Int.fract ((N : ℝ) / (k : ℝ))| +
        |∑ k ∈ Finset.Icc (K + 1) N,
          ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
            Int.fract ((N : ℝ) / (k : ℝ))| := abs_add_le _ _
    _ ≤ (K : ℝ) + 2 * H.C * (Q : ℝ) * (N : ℝ) *
        Real.exp (-H.a * Real.sqrt (Real.log (K : ℝ))) := by
      exact add_le_add (abs_mobiusFractHead_le N K)
        (by simpa [K] using abs_mobiusFractTail_le_of_decay H N Q hK)
    _ = _ := by rfl

/-- Integer cutoff used in the quantitative Axer decomposition. -/
noncomputable def axerExpCutoff (a : ℝ) (N : ℕ) : ℕ :=
  ⌊Real.exp ((a / 8) * Real.sqrt (Real.log (N : ℝ)))⌋₊

lemma axerExpCutoff_succ_le_nat_sqrt {a : ℝ} (ha : 0 < a)
    (N : ℕ) (hN : 1 ≤ N)
    (hy : 2 * (a / 8) + 4 ≤ Real.sqrt (Real.log (N : ℝ))) :
    axerExpCutoff a N + 1 ≤ Nat.sqrt N := by
  let b := a / 8
  let y := Real.sqrt (Real.log (N : ℝ))
  let x := Real.exp (b * y)
  let Q := axerExpCutoff a N
  have hb : 0 < b := by
    dsimp [b]
    exact div_pos ha (by norm_num)
  have hy_nonneg : 0 ≤ y := Real.sqrt_nonneg _
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have hy_sq : y ^ 2 = Real.log (N : ℝ) := by
    simp [y, Real.sq_sqrt hlog_nonneg]
  have hx_pos : 0 < x := Real.exp_pos _
  have hx_one : 1 ≤ x := Real.one_le_exp (mul_nonneg hb.le hy_nonneg)
  have hQ_le_x : (Q : ℝ) ≤ x := by
    simpa [Q, axerExpCutoff, x, b, y] using
      (Nat.floor_le hx_pos.le)
  have hQ1_le_two_x : (Q + 1 : ℕ) ≤ (2 * x : ℝ) := by
    push_cast
    linarith
  have hquad : 2 + b * y ≤ y ^ 2 / 2 := by
    have hgap : 0 ≤ y - (2 * b + 4) := by simpa [b, y] using hy
    have hprod := mul_nonneg hgap hy_nonneg
    nlinarith
  have he2 : (2 : ℝ) < Real.exp 1 := by
    have h := Real.add_one_lt_exp (x := (1 : ℝ)) one_ne_zero
    norm_num at h ⊢
    exact h
  have he4 : (4 : ℝ) ≤ Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    have hprod : 0 < (Real.exp 1 - 2) * (Real.exp 1 + 2) :=
      mul_pos (sub_pos.mpr he2) (add_pos (Real.exp_pos 1) (by norm_num))
    nlinarith
  have hfour_x : 4 * x ≤ Real.sqrt (N : ℝ) := by
    calc
      4 * x ≤ Real.exp 2 * x := mul_le_mul_of_nonneg_right he4 hx_pos.le
      _ = Real.exp (2 + b * y) := by simp [x, Real.exp_add]
      _ ≤ Real.exp (y ^ 2 / 2) := Real.exp_le_exp.mpr hquad
      _ = Real.sqrt (N : ℝ) := by
        rw [hy_sq, Real.exp_half, Real.exp_log]
        exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hN)
  have htwo_Q1 : (2 * (Q + 1) : ℕ) ≤ Real.sqrt (N : ℝ) := by
    push_cast
    linarith
  have hsqrt_lt : Real.sqrt (N : ℝ) < (Nat.sqrt N + 1 : ℕ) := by
    rw [Real.sqrt_lt' (by positivity)]
    exact_mod_cast Nat.lt_succ_sqrt' N
  have hQ_sqrt_real : ((Q + 1 : ℕ) : ℝ) ≤ Nat.sqrt N := by
    have hQ1pos : (1 : ℝ) ≤ (Q + 1 : ℕ) := by norm_cast; omega
    push_cast at htwo_Q1 hsqrt_lt ⊢
    linarith
  exact_mod_cast hQ_sqrt_real

lemma nat_le_sqrt_pow_four (N : ℕ) (hN : 16 ≤ N) :
    N ≤ (Nat.sqrt N) ^ 4 := by
  let S := Nat.sqrt N
  have hS4 : 4 ≤ S := by
    have hsqrt_mono := Nat.sqrt_le_sqrt hN
    norm_num [S] at hsqrt_mono ⊢
    exact hsqrt_mono
  have hlt : N < (S + 1) ^ 2 := by
    simpa [S] using Nat.lt_succ_sqrt' N
  have hpoly : (S + 1) ^ 2 ≤ S ^ 4 := by
    have hbase : S + 1 ≤ S ^ 2 := by nlinarith
    calc
      (S + 1) ^ 2 ≤ (S ^ 2) ^ 2 := by gcongr
      _ = S ^ 4 := by ring
  exact (Nat.le_of_lt hlt).trans hpoly

lemma eventually_abs_mobiusFractHyperbolaSum_le_exp
    (H : ClassicalMertensDecay) :
    ∀ᶠ N : ℕ in atTop,
      |mobiusFractHyperbolaSum N| ≤
        (1 + 2 * H.C) * (N : ℝ) *
          Real.exp (-(H.a / 8) * Real.sqrt (Real.log (N : ℝ))) := by
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hyTop : Tendsto
      (fun N : ℕ => Real.sqrt (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp hnat)
  filter_upwards
    [hyTop.eventually_ge_atTop (2 * (H.a / 8) + 4),
      eventually_ge_atTop (16 : ℕ)] with N hy hN
  let b := H.a / 8
  let y := Real.sqrt (Real.log (N : ℝ))
  let x := Real.exp (b * y)
  let Q := axerExpCutoff H.a N
  let S := Nat.sqrt N
  let K := N / (Q + 1)
  have hb : 0 < b := by
    dsimp [b]
    exact div_pos H.a_pos (by norm_num)
  have hy_nonneg : 0 ≤ y := Real.sqrt_nonneg _
  have hN1 : 1 ≤ N := by omega
  have hQsqrt : Q + 1 ≤ S := by
    simpa [Q, S, b, y] using axerExpCutoff_succ_le_nat_sqrt H.a_pos N hN1 hy
  have hS4 : 4 ≤ S := by
    have hsqrt_mono := Nat.sqrt_le_sqrt hN
    norm_num [S] at hsqrt_mono ⊢
    exact hsqrt_mono
  have hS_mul : S * (Q + 1) ≤ N :=
    (Nat.mul_le_mul_left S hQsqrt).trans (Nat.sqrt_le N)
  have hSK : S ≤ K := by
    exact (Nat.le_div_iff_mul_le (by omega)).mpr hS_mul
  have hK2 : 2 ≤ K := (by omega : 2 ≤ S).trans hSK
  have hcut := abs_mobiusFractHyperbolaSum_le_cutoff H N Q
    (by simpa [K] using hK2)
  have hx_pos : 0 < x := Real.exp_pos _
  have hx_le_Q1 : x ≤ (Q + 1 : ℕ) := by
    exact (by simpa [x, Q, b, y, axerExpCutoff] using
      (Nat.lt_floor_add_one (Real.exp (b * y))).le)
  have hKmul : K * (Q + 1) ≤ N := by
    simpa [K] using Nat.div_mul_le_self N (Q + 1)
  have hKx : (K : ℝ) * x ≤ (N : ℝ) := by
    calc
      (K : ℝ) * x ≤ (K : ℝ) * (Q + 1 : ℕ) :=
        mul_le_mul_of_nonneg_left hx_le_Q1 (by positivity)
      _ ≤ (N : ℝ) := by exact_mod_cast hKmul
  have hhead : (K : ℝ) ≤
      (N : ℝ) * Real.exp (-b * y) := by
    have hdiv : (K : ℝ) ≤ (N : ℝ) / x :=
      (le_div_iff₀ hx_pos).mpr hKx
    simpa [x, Real.exp_neg, div_eq_mul_inv] using hdiv
  have hQle : (Q : ℝ) ≤ x := by
    simpa [Q, axerExpCutoff, x, b, y] using
      (Nat.floor_le (Real.exp_pos (b * y)).le)
  have hNKpow : N ≤ K ^ 4 := by
    exact (nat_le_sqrt_pow_four N hN).trans (by gcongr)
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hKpos : 0 < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hlogN_nonneg : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN1)
  have hlogK_nonneg : 0 ≤ Real.log (K : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ K by omega))
  have hlog : Real.log (N : ℝ) ≤ 4 * Real.log (K : ℝ) := by
    calc
      Real.log (N : ℝ) ≤ Real.log ((K : ℝ) ^ 4) :=
        Real.log_le_log hNpos (by exact_mod_cast hNKpow)
      _ = 4 * Real.log (K : ℝ) := by rw [Real.log_pow]; norm_num
  let z := Real.sqrt (Real.log (K : ℝ))
  have hz_nonneg : 0 ≤ z := Real.sqrt_nonneg _
  have hy_sq : y ^ 2 = Real.log (N : ℝ) := by
    simp [y, Real.sq_sqrt hlogN_nonneg]
  have hz_sq : z ^ 2 = Real.log (K : ℝ) := by
    simp [z, Real.sq_sqrt hlogK_nonneg]
  have hy_le_two_z : y ≤ 2 * z := by
    nlinarith
  have hexponent : b * y - H.a * z ≤ -b * y := by
    have hgap : 0 ≤ z - y / 2 := by linarith
    have hprod := mul_nonneg H.a_pos.le hgap
    have hay := mul_nonneg H.a_pos.le hy_nonneg
    dsimp [b]
    nlinarith
  have hQexp : (Q : ℝ) * Real.exp (-H.a * z) ≤
      Real.exp (-b * y) := by
    calc
      (Q : ℝ) * Real.exp (-H.a * z) ≤
          x * Real.exp (-H.a * z) :=
        mul_le_mul_of_nonneg_right hQle (Real.exp_pos _).le
      _ = Real.exp (b * y - H.a * z) := by
        dsimp [x]
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-b * y) := Real.exp_le_exp.mpr hexponent
  calc
    |mobiusFractHyperbolaSum N| ≤
        (K : ℝ) + 2 * H.C * (Q : ℝ) * (N : ℝ) *
          Real.exp (-H.a * z) := by simpa [K, z] using hcut
    _ ≤ (N : ℝ) * Real.exp (-b * y) +
        2 * H.C * (N : ℝ) * Real.exp (-b * y) := by
      apply add_le_add hhead
      calc
        2 * H.C * (Q : ℝ) * (N : ℝ) * Real.exp (-H.a * z) =
            (2 * H.C * (N : ℝ)) *
              ((Q : ℝ) * Real.exp (-H.a * z)) := by ring
        _ ≤ (2 * H.C * (N : ℝ)) * Real.exp (-b * y) :=
          mul_le_mul_of_nonneg_left hQexp
            (mul_nonneg (mul_nonneg (by norm_num) H.C_pos.le) (by positivity))
    _ = (1 + 2 * H.C) * (N : ℝ) *
        Real.exp (-(H.a / 8) * Real.sqrt (Real.log (N : ℝ))) := by
      simp [b, y]
      ring

/--
Global quantitative form of the Axer fractional-part estimate.  The finitely
many values before the asymptotic cutoff are absorbed into the constant.
-/
theorem mobiusFractHyperbolaSum_quantitative_of_decay
    (H : ClassicalMertensDecay) :
    ∃ C' c' : ℝ, 0 < C' ∧ 0 < c' ∧
      ∀ N : ℕ, 2 ≤ N →
        |mobiusFractHyperbolaSum N| ≤
          C' * (N : ℝ) *
            Real.exp (-c' * Real.sqrt (Real.log (N : ℝ))) := by
  let b := H.a / 8
  have hb : 0 < b := div_pos H.a_pos (by norm_num)
  rcases eventually_atTop.1
      (eventually_abs_mobiusFractHyperbolaSum_le_exp H) with ⟨N₀, hlarge⟩
  let R := max N₀ 2
  let E := Real.exp (b * Real.sqrt (Real.log (R : ℝ)))
  let C' := max (1 + 2 * H.C) E
  have hR2 : 2 ≤ R := le_max_right _ _
  have hEpos : 0 < E := Real.exp_pos _
  have hCpos : 0 < C' := hEpos.trans_le (le_max_right _ _)
  refine ⟨C', b, hCpos, hb, ?_⟩
  intro N hN
  by_cases hNlarge : N₀ ≤ N
  · have h := hlarge N hNlarge
    have hcoeff : 1 + 2 * H.C ≤ C' := le_max_left _ _
    calc
      |mobiusFractHyperbolaSum N| ≤
          (1 + 2 * H.C) * (N : ℝ) *
            Real.exp (-(H.a / 8) * Real.sqrt (Real.log (N : ℝ))) := h
      _ ≤ C' * (N : ℝ) *
          Real.exp (-b * Real.sqrt (Real.log (N : ℝ))) := by
        dsimp [b]
        gcongr
      _ = _ := rfl
  · have hNR : N ≤ R := by
      exact (Nat.le_of_lt (lt_of_not_ge hNlarge)).trans (le_max_left _ _)
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hRpos : 0 < (R : ℝ) := by exact_mod_cast (by omega : 0 < R)
    have hlog : Real.log (N : ℝ) ≤ Real.log (R : ℝ) :=
      Real.log_le_log hNpos (by exact_mod_cast hNR)
    have hsqrt : Real.sqrt (Real.log (N : ℝ)) ≤
        Real.sqrt (Real.log (R : ℝ)) := Real.sqrt_le_sqrt hlog
    have hexp : Real.exp (b * Real.sqrt (Real.log (N : ℝ))) ≤ E := by
      dsimp [E]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsqrt hb.le)
    have hscale : 1 ≤ E *
        Real.exp (-b * Real.sqrt (Real.log (N : ℝ))) := by
      calc
        1 = Real.exp (b * Real.sqrt (Real.log (N : ℝ))) *
            Real.exp (-b * Real.sqrt (Real.log (N : ℝ))) := by
          rw [← Real.exp_add]
          ring_nf
          simp
        _ ≤ E * Real.exp (-b * Real.sqrt (Real.log (N : ℝ))) :=
          mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
    have htrivial : |mobiusFractHyperbolaSum N| ≤ (N : ℝ) := by
      simpa [mobiusFractHyperbolaSum] using abs_mobiusFractHead_le N N
    calc
      |mobiusFractHyperbolaSum N| ≤ (N : ℝ) := htrivial
      _ ≤ E * (N : ℝ) *
          Real.exp (-b * Real.sqrt (Real.log (N : ℝ))) := by
        have hNnonneg : 0 ≤ (N : ℝ) := by positivity
        nlinarith [mul_nonneg hNnonneg (sub_nonneg.mpr hscale)]
      _ ≤ C' * (N : ℝ) *
          Real.exp (-b * Real.sqrt (Real.log (N : ℝ))) := by
        gcongr
        exact le_max_right _ _

lemma abs_mobiusOverKPartial_le_two (N : ℕ) (hN : 1 ≤ N) :
    |mobiusOverKPartial N| ≤ 2 := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hN)
  have heq : (N : ℝ) * |mobiusOverKPartial N| =
      |1 + mobiusFractHyperbolaSum N| := by
    calc
      (N : ℝ) * |mobiusOverKPartial N| =
          |(N : ℝ)| * |mobiusOverKPartial N| := by
        rw [abs_of_pos hNpos]
      _ = |(N : ℝ) * mobiusOverKPartial N| := (abs_mul _ _).symm
      _ = _ := congrArg abs (mobius_overK_fract_decomposition N hN)
  apply le_of_mul_le_mul_left _ hNpos
  rw [heq]
  calc
    |1 + mobiusFractHyperbolaSum N| ≤ 1 + |mobiusFractHyperbolaSum N| := by
      simpa using abs_add_le (1 : ℝ) (mobiusFractHyperbolaSum N)
    _ ≤ 1 + (N : ℝ) := by
      gcongr
      simpa [mobiusFractHyperbolaSum] using abs_mobiusFractHead_le N N
    _ ≤ (N : ℝ) * 2 := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith

lemma eventually_abs_mobiusOverKPartial_le_exp (H : ClassicalMertensDecay) :
    ∀ᶠ N : ℕ in atTop,
      |mobiusOverKPartial N| ≤
        (2 + 2 * H.C) *
          Real.exp (-(H.a / 8) * Real.sqrt (Real.log (N : ℝ))) := by
  let b := H.a / 8
  have hb : 0 < b := div_pos H.a_pos (by norm_num)
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hyTop : Tendsto
      (fun N : ℕ => Real.sqrt (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp hnat)
  filter_upwards
    [eventually_abs_mobiusFractHyperbolaSum_le_exp H,
      hyTop.eventually_ge_atTop b, eventually_ge_atTop (2 : ℕ)] with N hfract hy hN
  let y := Real.sqrt (Real.log (N : ℝ))
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hy_sq : y ^ 2 = Real.log (N : ℝ) := by
    simp [y, Real.sq_sqrt hlog_nonneg]
  have hy_nonneg : 0 ≤ y := Real.sqrt_nonneg _
  have hexponent : 0 ≤ Real.log (N : ℝ) - b * y := by
    have hy' : b ≤ y := by simpa [y] using hy
    have hprod := mul_nonneg (sub_nonneg.mpr hy') hy_nonneg
    nlinarith
  have hscale : 1 ≤ (N : ℝ) * Real.exp (-b * y) := by
    calc
      1 = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp (Real.log (N : ℝ) - b * y) :=
        Real.exp_le_exp.mpr hexponent
      _ = (N : ℝ) * Real.exp (-b * y) := by
        rw [Real.exp_sub, Real.exp_log hNpos]
        simp [Real.exp_neg, div_eq_mul_inv]
  have heq : (N : ℝ) * |mobiusOverKPartial N| =
      |1 + mobiusFractHyperbolaSum N| := by
    calc
      (N : ℝ) * |mobiusOverKPartial N| =
          |(N : ℝ)| * |mobiusOverKPartial N| := by rw [abs_of_pos hNpos]
      _ = |(N : ℝ) * mobiusOverKPartial N| := (abs_mul _ _).symm
      _ = _ := congrArg abs
        (mobius_overK_fract_decomposition N (by omega))
  apply le_of_mul_le_mul_left _ hNpos
  rw [heq]
  calc
    |1 + mobiusFractHyperbolaSum N| ≤ 1 + |mobiusFractHyperbolaSum N| := by
      simpa using abs_add_le (1 : ℝ) (mobiusFractHyperbolaSum N)
    _ ≤ (N : ℝ) * Real.exp (-b * y) +
        (1 + 2 * H.C) * (N : ℝ) * Real.exp (-b * y) :=
      add_le_add hscale (by simpa [b, y] using hfract)
    _ = (N : ℝ) * ((2 + 2 * H.C) * Real.exp
        (-(H.a / 8) * Real.sqrt (Real.log (N : ℝ)))) := by
      simp [b, y]
      ring

/-- Quantitative Axer bound for the partial sums `∑_{k≤N} μ(k)/k`. -/
theorem mobiusOverK_quantitative_of_decay (H : ClassicalMertensDecay) :
    ∃ C' c' : ℝ, 0 < C' ∧ 0 < c' ∧
      ∀ N : ℕ, 2 ≤ N →
        |mobiusOverKPartial N| ≤
          C' * Real.exp (-c' * Real.sqrt (Real.log (N : ℝ))) := by
  let b := H.a / 8
  have hb : 0 < b := div_pos H.a_pos (by norm_num)
  rcases eventually_atTop.1 (eventually_abs_mobiusOverKPartial_le_exp H) with
    ⟨N₀, hlarge⟩
  let R := max N₀ 2
  let E := Real.exp (b * Real.sqrt (Real.log (R : ℝ)))
  let C' := max (2 + 2 * H.C) (2 * E)
  have hR2 : 2 ≤ R := le_max_right _ _
  have hEpos : 0 < E := Real.exp_pos _
  have hCpos : 0 < C' := by
    exact (mul_pos (by norm_num) hEpos).trans_le (le_max_right _ _)
  refine ⟨C', b, hCpos, hb, ?_⟩
  intro N hN
  by_cases hNlarge : N₀ ≤ N
  · have h := hlarge N hNlarge
    calc
      |mobiusOverKPartial N| ≤
          (2 + 2 * H.C) * Real.exp
            (-(H.a / 8) * Real.sqrt (Real.log (N : ℝ))) := h
      _ ≤ C' * Real.exp (-b * Real.sqrt (Real.log (N : ℝ))) := by
        dsimp [b]
        gcongr
        exact le_max_left _ _
      _ = _ := rfl
  · have hNR : N ≤ R :=
      (Nat.le_of_lt (lt_of_not_ge hNlarge)).trans (le_max_left _ _)
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hlog : Real.log (N : ℝ) ≤ Real.log (R : ℝ) :=
      Real.log_le_log hNpos (by exact_mod_cast hNR)
    have hsqrt : Real.sqrt (Real.log (N : ℝ)) ≤
        Real.sqrt (Real.log (R : ℝ)) := Real.sqrt_le_sqrt hlog
    have hexp : Real.exp (b * Real.sqrt (Real.log (N : ℝ))) ≤ E := by
      dsimp [E]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsqrt hb.le)
    have hscale : 1 ≤ E *
        Real.exp (-b * Real.sqrt (Real.log (N : ℝ))) := by
      calc
        1 = Real.exp (b * Real.sqrt (Real.log (N : ℝ))) *
            Real.exp (-b * Real.sqrt (Real.log (N : ℝ))) := by
          rw [← Real.exp_add]
          ring_nf
          simp
        _ ≤ E * Real.exp (-b * Real.sqrt (Real.log (N : ℝ))) :=
          mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
    calc
      |mobiusOverKPartial N| ≤ 2 := abs_mobiusOverKPartial_le_two N (by omega)
      _ ≤ (2 * E) * Real.exp (-b * Real.sqrt (Real.log (N : ℝ))) := by
        nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
          (sub_nonneg.mpr hscale)]
      _ ≤ C' * Real.exp (-b * Real.sqrt (Real.log (N : ℝ))) := by
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-- The quantitative Axer estimate identifies the boundary value as zero. -/
theorem mobiusOverK_tendsto_zero_of_decay (H : ClassicalMertensDecay) :
    Tendsto mobiusOverKPartial atTop (𝓝 0) := by
  rcases mobiusOverK_quantitative_of_decay H with
    ⟨C', c', hC', hc', hbound⟩
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hyTop : Tendsto
      (fun N : ℕ => Real.sqrt (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp hnat)
  have hcyTop : Tendsto
      (fun N : ℕ => c' * Real.sqrt (Real.log (N : ℝ))) atTop atTop :=
    Tendsto.const_mul_atTop hc' hyTop
  have hexp : Tendsto
      (fun N : ℕ => Real.exp (-c' * Real.sqrt (Real.log (N : ℝ))))
      atTop (𝓝 0) := by
    simpa [Function.comp_def, neg_mul] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp hcyTop)
  have hmajorant : Tendsto
      (fun N : ℕ => C' * Real.exp (-c' * Real.sqrt (Real.log (N : ℝ))))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hexp)
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _)
    ?_ hmajorant
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  exact hbound N hN

/--
Residual non-Mertens inputs needed to assemble the existing
`ClassicalMertensAPI`.

The logarithmic summatory estimate is classically a separate Abel consequence
of sufficiently strong Mertens decay, but formalizing that derivation is not
part of this wrapper.  The two boundary values are Tauberian/residue inputs
(`1 / ζ(1) = 0` and the `ζ'/ζ` residue) rather than mere decay estimates.
-/
structure ClassicalMertensResidualInputs where
  C_L : ℝ
  C_L_pos : 0 < C_L
  mobiusLogSummatory_bound :
    ∀ N : ℕ,
      |mobiusLogSummatory N| ≤ C_L * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2
  mobius_sum_zero : Tendsto mobiusOverKPartial atTop (𝓝 0)
  mobiusLog_sum_neg_one : Tendsto mobiusLogOverKPartial atTop (𝓝 (-1))

/--
Finite Abel summation for a cutoff that vanishes at `N + 1`.

This is the public H14-classical copy of the private finite Abel lemma in
`MobiusSummatory.lean`; it is kept here so the residual-reduction layer can use
the same summation-by-parts shape without changing the earlier file.
-/
theorem finite_abel_sum_Icc_mul_sub_endpoint_eq_sum_partial
    (a b : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, a k * (b k - b (N + 1))) =
      ∑ k ∈ Finset.Icc 1 N,
        (∑ j ∈ Finset.Icc 1 k, a j) * (b k - b (k + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hone : 1 ≤ N + 1 := by omega
      rw [Finset.sum_Icc_succ_top hone, Finset.sum_Icc_succ_top hone]
      have hshift :
          (∑ k ∈ Finset.Icc 1 N, a k * (b k - b (N + 1 + 1))) =
            (∑ k ∈ Finset.Icc 1 N, a k * (b k - b (N + 1))) +
              (∑ k ∈ Finset.Icc 1 N, a k) * (b (N + 1) - b (N + 1 + 1)) := by
        calc
          _ = ∑ k ∈ Finset.Icc 1 N,
                (a k * (b k - b (N + 1)) +
                  a k * (b (N + 1) - b (N + 1 + 1))) := by
              apply Finset.sum_congr rfl
              intro k _
              ring
          _ = _ := by
              rw [Finset.sum_add_distrib, Finset.sum_mul]
      rw [hshift, ih, Finset.sum_Icc_succ_top hone]
      ring

/--
Finite Abel summation in endpoint-plus-differences form.
-/
theorem finite_abel_sum_Icc_mul_eq_endpoint_add_sum_partial
    (a b : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, a k * b k) =
      (∑ k ∈ Finset.Icc 1 N, a k) * b (N + 1) +
        ∑ k ∈ Finset.Icc 1 N,
          (∑ j ∈ Finset.Icc 1 k, a j) * (b k - b (k + 1)) := by
  have habel := finite_abel_sum_Icc_mul_sub_endpoint_eq_sum_partial a b N
  calc
    (∑ k ∈ Finset.Icc 1 N, a k * b k)
        = (∑ k ∈ Finset.Icc 1 N, a k * b (N + 1)) +
            ∑ k ∈ Finset.Icc 1 N, a k * (b k - b (N + 1)) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = (∑ k ∈ Finset.Icc 1 N, a k) * b (N + 1) +
            ∑ k ∈ Finset.Icc 1 N, a k * (b k - b (N + 1)) := by
          rw [Finset.sum_mul]
    _ = (∑ k ∈ Finset.Icc 1 N, a k) * b (N + 1) +
            ∑ k ∈ Finset.Icc 1 N,
              (∑ j ∈ Finset.Icc 1 k, a j) * (b k - b (k + 1)) := by
          rw [habel]

/--
Exact Abel-summation expansion for the logarithmic Möbius summatory function.
-/
theorem mobiusLogSummatory_eq_abel_endpoint_add_sum (N : ℕ) :
    mobiusLogSummatory N =
      mobiusSummatory N * Real.log (N + 1 : ℝ) +
        ∑ k ∈ Finset.Icc 1 N,
          mobiusSummatory k *
            (Real.log (k : ℝ) - Real.log ((k + 1 : ℕ) : ℝ)) := by
  simpa [mobiusLogSummatory, mobiusSummatory] using
    finite_abel_sum_Icc_mul_eq_endpoint_add_sum_partial
      (fun k ↦ ((ArithmeticFunction.moebius k : ℤ) : ℝ))
      (fun k ↦ Real.log (k : ℝ)) N

lemma abs_mobiusSummatory_le_nat (N : ℕ) :
    |mobiusSummatory N| ≤ (N : ℝ) := by
  unfold mobiusSummatory
  calc
    |∑ k ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius k : ℤ) : ℝ)|
      ≤ ∑ k ∈ Finset.Icc 1 N, |((ArithmeticFunction.moebius k : ℤ) : ℝ)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.Icc 1 N, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro k _hk
          exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := k))
    _ ≤ N := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          have hcard : (Finset.Icc 1 N).card ≤ N := by
            rw [Nat.card_Icc]
            omega
          exact_mod_cast hcard

lemma tendsto_rpow_mul_exp_neg_mul_sqrt_atTop_nhds_zero
    (A a : ℝ) (ha : 0 < a) :
    Tendsto (fun t : ℝ => t ^ A * Real.exp (-a * Real.sqrt t)) atTop (𝓝 0) := by
  have hbase :
      Tendsto (fun x : ℝ => x ^ (2 * A) * Real.exp (-a * x)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 * A) a ha
  refine (hbase.comp Real.tendsto_sqrt_atTop).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have hsqrt : t ^ A = Real.sqrt t ^ (2 * A) := by
    rw [← Real.rpow_div_two_eq_sqrt (2 * A) ht]
    congr 1
    ring
  simp [hsqrt]

/--
Exponential decay in `√t` dominates every real power of `t`, uniformly on
`[1, ∞)`.

This is the calculus conversion used to turn the classical de la Vallée
Poussin decay `exp (-a √log N)` into any desired power of `1 / log N`.
-/
lemma exists_pos_bound_rpow_mul_exp_neg_mul_sqrt
    (A a : ℝ) (ha : 0 < a) :
    ∃ C_A : ℝ, 0 < C_A ∧
      ∀ t : ℝ, 1 ≤ t → t ^ A * Real.exp (-a * Real.sqrt t) ≤ C_A := by
  have hlim := tendsto_rpow_mul_exp_neg_mul_sqrt_atTop_nhds_zero A a ha
  have hsmall :
      ∀ᶠ t : ℝ in atTop, t ^ A * Real.exp (-a * Real.sqrt t) ≤ 1 := by
    have hball : Metric.ball (0 : ℝ) 1 ∈ 𝓝 (0 : ℝ) :=
      Metric.ball_mem_nhds _ zero_lt_one
    filter_upwards [hlim hball] with t ht
    have habs : |t ^ A * Real.exp (-a * Real.sqrt t)| < 1 := by
      simpa [Real.dist_eq] using ht
    exact (le_abs_self _).trans habs.le
  rcases eventually_atTop.1 hsmall with ⟨B, hB⟩
  let R : ℝ := max 1 B
  have hcont :
      ContinuousOn (fun t : ℝ => t ^ A * Real.exp (-a * Real.sqrt t))
        (Set.Icc 1 R) := by
    have hpow : ContinuousOn (fun t : ℝ => t ^ A) (Set.Icc 1 R) := by
      refine ContinuousOn.rpow_const continuousOn_id ?_
      intro t ht
      exact Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))
    have hexp : ContinuousOn (fun t : ℝ => Real.exp (-a * Real.sqrt t))
        (Set.Icc 1 R) := by
      fun_prop
    exact hpow.mul hexp
  rcases isCompact_Icc.exists_bound_of_continuousOn hcont with ⟨C₀, hC₀⟩
  refine ⟨max C₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right C₀ 1), ?_⟩
  intro t ht
  by_cases htR : t ≤ R
  · have hnorm := hC₀ t ⟨ht, htR⟩
    exact (le_abs_self _).trans <| hnorm.trans (le_max_left C₀ 1)
  · have hRt : R ≤ t := le_of_not_ge htR
    have hBt : B ≤ t := (le_max_right 1 B).trans hRt
    exact (hB t hBt).trans (le_max_right C₀ 1)

/--
Natural-number logarithmic form of
`exists_pos_bound_rpow_mul_exp_neg_mul_sqrt`.
-/
lemma exists_pos_exp_neg_mul_sqrt_log_nat_le_const_div_log_pow
    (m : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ C_A : ℝ, 0 < C_A ∧
      ∀ N : ℕ, 3 ≤ N →
        Real.exp (-a * Real.sqrt (Real.log (N : ℝ))) ≤
          C_A / Real.log (N : ℝ) ^ m := by
  rcases exists_pos_bound_rpow_mul_exp_neg_mul_sqrt (m : ℝ) a ha with
    ⟨C_A, hC_A_pos, hC_A⟩
  refine ⟨C_A, hC_A_pos, ?_⟩
  intro N hN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN)
  have hlog_one : 1 ≤ Real.log (N : ℝ) := by
    rw [Real.le_log_iff_exp_le hNpos]
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hN)
  have hlog_pos : 0 < Real.log (N : ℝ) :=
    lt_of_lt_of_le zero_lt_one hlog_one
  have hprod := hC_A (Real.log (N : ℝ)) hlog_one
  have hprod_nat :
      Real.log (N : ℝ) ^ m * Real.exp (-a * Real.sqrt (Real.log (N : ℝ))) ≤ C_A := by
    simpa [Real.rpow_natCast] using hprod
  have hpow_pos : 0 < Real.log (N : ℝ) ^ m := pow_pos hlog_pos m
  calc
    Real.exp (-a * Real.sqrt (Real.log (N : ℝ)))
        = (Real.log (N : ℝ) ^ m *
            Real.exp (-a * Real.sqrt (Real.log (N : ℝ)))) /
            Real.log (N : ℝ) ^ m := by
          field_simp [hpow_pos.ne']
    _ ≤ C_A / Real.log (N : ℝ) ^ m := by
          exact div_le_div_of_nonneg_right hprod_nat hpow_pos.le

lemma log_nat_add_two_le_two_log_nat {N : ℕ} (hN : 3 ≤ N) :
    Real.log (N + 2 : ℝ) ≤ 2 * Real.log (N : ℝ) := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN)
  have hargpos : 0 < (N + 2 : ℝ) := by positivity
  have hle_sq : (N + 2 : ℝ) ≤ (N : ℝ) ^ 2 := by
    norm_num [sq]
    nlinarith [show (3 : ℝ) ≤ N by exact_mod_cast hN]
  have hlog := Real.log_le_log hargpos hle_sq
  have hlog_sq : Real.log ((N : ℝ) ^ 2) = 2 * Real.log (N : ℝ) := by
    rw [Real.log_pow]
    norm_num
  exact hlog.trans_eq hlog_sq

/--
The classical de la Vallée Poussin decay form implies the polynomial-log
Mertens bound used by `ClassicalMertensAPI`.

The proof is deliberately lossy in constants: large `N` uses
`exp (-a √log N) ≪ 1 / log(N)^3`, and the finitely many small values are
absorbed by a harmless absolute constant.
-/
lemma mertens_bound_of_decay (H : ClassicalMertensDecay) :
    ∃ C_M : ℝ, 0 < C_M ∧
      ∀ N : ℕ,
        |mobiusSummatory N| ≤ C_M * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 3 := by
  rcases exists_pos_exp_neg_mul_sqrt_log_nat_le_const_div_log_pow 3 H.a H.a_pos with
    ⟨C₃, hC₃_pos, hC₃⟩
  refine ⟨max (8 * H.C * C₃) 100, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro N
  by_cases hN0 : N = 0
  · subst N
    simp [mobiusSummatory]
  by_cases hNlarge : 3 ≤ N
  · have hN2 : 2 ≤ N := by omega
    have hNpos : 0 ≤ (N : ℝ) := by positivity
    have hlogN_pos : 0 < Real.log (N : ℝ) := by
      exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hlogN2_pos : 0 < Real.log (N + 2 : ℝ) := by
      exact Real.log_pos (by norm_cast; omega)
    have hlogN2_nonneg : 0 ≤ Real.log (N + 2 : ℝ) := hlogN2_pos.le
    have hlog_compare := log_nat_add_two_le_two_log_nat hNlarge
    have hcube :
        Real.log (N + 2 : ℝ) ^ 3 ≤ 8 * Real.log (N : ℝ) ^ 3 := by
      have hpow :=
        pow_le_pow_left₀ hlogN2_nonneg hlog_compare 3
      have hrewrite :
          (2 * Real.log (N : ℝ)) ^ 3 = 8 * Real.log (N : ℝ) ^ 3 := by ring
      simpa [hrewrite] using hpow
    have hpowN_pos : 0 < Real.log (N : ℝ) ^ 3 := pow_pos hlogN_pos 3
    have hpowN2_pos : 0 < Real.log (N + 2 : ℝ) ^ 3 := pow_pos hlogN2_pos 3
    have hinv :
        (1 : ℝ) / Real.log (N : ℝ) ^ 3 ≤
          8 / Real.log (N + 2 : ℝ) ^ 3 := by
      rw [div_le_div_iff₀ hpowN_pos hpowN2_pos]
      nlinarith
    have hdecay := H.mertens_decay N hN2
    have hpoly := hC₃ N hNlarge
    have hCN_nonneg : 0 ≤ H.C * (N : ℝ) :=
      mul_nonneg H.C_pos.le hNpos
    have hcoeff_nonneg : 0 ≤ H.C * C₃ * (N : ℝ) :=
      mul_nonneg (mul_nonneg H.C_pos.le hC₃_pos.le) hNpos
    calc
      |mobiusSummatory N|
          ≤ H.C * (N : ℝ) *
              Real.exp (-H.a * Real.sqrt (Real.log (N : ℝ))) := hdecay
      _ ≤ H.C * (N : ℝ) * (C₃ / Real.log (N : ℝ) ^ 3) := by
            exact mul_le_mul_of_nonneg_left hpoly hCN_nonneg
      _ = (H.C * C₃ * (N : ℝ)) * (1 / Real.log (N : ℝ) ^ 3) := by ring
      _ ≤ (H.C * C₃ * (N : ℝ)) * (8 / Real.log (N + 2 : ℝ) ^ 3) := by
            exact mul_le_mul_of_nonneg_left hinv hcoeff_nonneg
      _ = (8 * H.C * C₃) * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 3 := by ring
      _ ≤ max (8 * H.C * C₃) 100 * (N : ℝ) /
            Real.log (N + 2 : ℝ) ^ 3 := by
            gcongr
            exact le_max_left _ _
  · have hNsmall : N ≤ 2 := by omega
    have hNpos_nat : 0 < N := Nat.pos_of_ne_zero hN0
    have hN_nonneg : 0 ≤ (N : ℝ) := by positivity
    have hlog_pos : 0 < Real.log (N + 2 : ℝ) := by
      exact Real.log_pos (by norm_cast; omega)
    have hlog_nonneg : 0 ≤ Real.log (N + 2 : ℝ) := hlog_pos.le
    have hlog_le_four : Real.log (N + 2 : ℝ) ≤ 4 := by
      have hle : (N + 2 : ℝ) ≤ 4 := by exact_mod_cast (by omega : N + 2 ≤ 4)
      exact (Real.log_le_log (by positivity) hle).trans
        (Real.log_le_self (by norm_num : (0 : ℝ) ≤ 4))
    have hlog_cube_le : Real.log (N + 2 : ℝ) ^ 3 ≤ 100 := by
      nlinarith [sq_nonneg (Real.log (N + 2 : ℝ)), hlog_nonneg, hlog_le_four]
    have hpow_pos : 0 < Real.log (N + 2 : ℝ) ^ 3 := pow_pos hlog_pos 3
    have hone_le :
        (1 : ℝ) ≤ max (8 * H.C * C₃) 100 / Real.log (N + 2 : ℝ) ^ 3 := by
      rw [le_div_iff₀ hpow_pos]
      simpa [one_mul] using hlog_cube_le.trans (le_max_right _ _)
    calc
      |mobiusSummatory N| ≤ (N : ℝ) := abs_mobiusSummatory_le_nat N
      _ = 1 * (N : ℝ) := by ring
      _ ≤ (max (8 * H.C * C₃) 100 / Real.log (N + 2 : ℝ) ^ 3) * (N : ℝ) := by
            exact mul_le_mul_of_nonneg_right hone_le hN_nonneg
      _ = max (8 * H.C * C₃) 100 * (N : ℝ) /
            Real.log (N + 2 : ℝ) ^ 3 := by ring

lemma log_nat_succ_sub_log_nat_le_inv (k : ℕ) (hk : 1 ≤ k) :
    Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) ≤ 1 / (k : ℝ) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hksuccpos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  calc
    Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) =
        Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ)) := by
          rw [Real.log_div hksuccpos.ne' hkpos.ne']
    _ ≤ (((k + 1 : ℕ) : ℝ) / (k : ℝ)) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hksuccpos hkpos)
    _ = 1 / (k : ℝ) := by
      push_cast
      field_simp
      ring

lemma one_le_log_nat_add_two (k : ℕ) (hk : 1 ≤ k) :
    1 ≤ Real.log (k + 2 : ℝ) := by
  have hargpos : (0 : ℝ) < k + 2 := by positivity
  rw [Real.le_log_iff_exp_le hargpos]
  exact Real.exp_one_lt_three.le.trans (by exact_mod_cast (show 3 ≤ k + 2 by omega))

lemma finite_inv_log_cube_head_le (S : ℕ) :
    (∑ k ∈ Finset.Icc 1 S, 1 / Real.log (k + 2 : ℝ) ^ 3) ≤ (S : ℝ) := by
  calc
    (∑ k ∈ Finset.Icc 1 S, 1 / Real.log (k + 2 : ℝ) ^ 3)
        ≤ ∑ _k ∈ Finset.Icc 1 S, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro k hk
          have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
          have hlog := one_le_log_nat_add_two k hk1
          have hlogpos : 0 < Real.log (k + 2 : ℝ) := zero_lt_one.trans_le hlog
          rw [div_le_one (pow_pos hlogpos 3)]
          nlinarith [sq_nonneg (Real.log (k + 2 : ℝ))]
    _ ≤ S := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          have hcard : (Finset.Icc 1 S).card ≤ S := by
            rw [Nat.card_Icc]
            omega
          exact_mod_cast hcard

lemma finite_inv_log_cube_tail_le (S N : ℕ) :
    (∑ k ∈ Finset.Icc (S + 1) N, 1 / Real.log (k + 2 : ℝ) ^ 3) ≤
      (N : ℝ) / Real.log (S + 2 : ℝ) ^ 3 := by
  have hlogSpos : 0 < Real.log (S + 2 : ℝ) := Real.log_pos (by norm_cast; omega)
  calc
    (∑ k ∈ Finset.Icc (S + 1) N, 1 / Real.log (k + 2 : ℝ) ^ 3)
        ≤ ∑ _k ∈ Finset.Icc (S + 1) N,
            1 / Real.log (S + 2 : ℝ) ^ 3 := by
          apply Finset.sum_le_sum
          intro k hk
          have hSk : S + 1 ≤ k := (Finset.mem_Icc.mp hk).1
          have hlogpos : 0 < Real.log (k + 2 : ℝ) :=
            Real.log_pos (by norm_cast; omega)
          have hlogle : Real.log (S + 2 : ℝ) ≤ Real.log (k + 2 : ℝ) := by
            exact Real.log_le_log (by positivity) (by exact_mod_cast (show S + 2 ≤ k + 2 by omega))
          have hpowle : Real.log (S + 2 : ℝ) ^ 3 ≤ Real.log (k + 2 : ℝ) ^ 3 := by
            gcongr
          exact one_div_le_one_div_of_le (pow_pos hlogSpos 3) hpowle
    _ ≤ N * (1 / Real.log (S + 2 : ℝ) ^ 3) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          gcongr
          rw [Nat.card_Icc]
          omega
    _ = (N : ℝ) / Real.log (S + 2 : ℝ) ^ 3 := by ring

lemma log_nat_add_two_le_two_log_sqrt_add_two (N : ℕ) :
    Real.log (N + 2 : ℝ) ≤ 2 * Real.log (Nat.sqrt N + 2 : ℝ) := by
  have hsquare : (N + 2 : ℝ) ≤ (Nat.sqrt N + 2 : ℝ) ^ 2 := by
    have hsqrt := Nat.lt_succ_sqrt' N
    have hsqrtNat : N + 1 ≤ (Nat.sqrt N + 1) ^ 2 := by
      simpa [Nat.succ_eq_add_one] using (Nat.succ_le_iff.mpr hsqrt)
    have hsqrtReal : ((N + 1 : ℕ) : ℝ) ≤ ((Nat.sqrt N + 1 : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast hsqrtNat
    have hsqrt_nonneg : (0 : ℝ) ≤ Nat.sqrt N := by positivity
    push_cast at hsqrtReal ⊢
    nlinarith
  have hargpos : (0 : ℝ) < N + 2 := by positivity
  calc
    Real.log (N + 2 : ℝ) ≤ Real.log ((Nat.sqrt N + 2 : ℝ) ^ 2) :=
      Real.log_le_log hargpos hsquare
    _ = 2 * Real.log (Nat.sqrt N + 2 : ℝ) := by
      rw [Real.log_pow]
      norm_num

lemma log_nat_add_two_sq_le_sixteen_sqrt (N : ℕ) :
    Real.log (N + 2 : ℝ) ^ 2 ≤ 16 * Real.sqrt (N + 2 : ℝ) := by
  have hx : (0 : ℝ) ≤ N + 2 := by positivity
  have hlog_nonneg : 0 ≤ Real.log (N + 2 : ℝ) :=
    Real.log_nonneg (by norm_cast; omega)
  have hpow_nonneg : 0 ≤ (N + 2 : ℝ) ^ (1 / 4 : ℝ) :=
    (Real.rpow_nonneg hx _)
  have hlog := Real.log_le_rpow_div hx (show (0 : ℝ) < 1 / 4 by norm_num)
  have hpow_sq : ((N + 2 : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt (N + 2 : ℝ) := by
    calc
      ((N + 2 : ℝ) ^ (1 / 4 : ℝ)) ^ 2 =
          (N + 2 : ℝ) ^ ((1 / 4 : ℝ) * 2) :=
            (Real.rpow_mul_natCast hx (1 / 4 : ℝ) 2).symm
      _ = Real.sqrt (N + 2 : ℝ) := by
            rw [show (1 / 4 : ℝ) * 2 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  rw [show (N + 2 : ℝ) ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) =
      4 * (N + 2 : ℝ) ^ (1 / 4 : ℝ) by ring] at hlog
  nlinarith

lemma nat_sqrt_le_fortyeight_mul_div_log_sq (N : ℕ) (hN : 1 ≤ N) :
    (Nat.sqrt N : ℝ) ≤ 48 * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 := by
  have hlogpos : 0 < Real.log (N + 2 : ℝ) := Real.log_pos (by norm_cast; omega)
  rw [le_div_iff₀ (pow_pos hlogpos 2)]
  have hsqrtN : (Nat.sqrt N : ℝ) ≤ Real.sqrt (N : ℝ) :=
    Real.nat_sqrt_le_real_sqrt
  have hsqrtmono : Real.sqrt (N : ℝ) ≤ Real.sqrt (N + 2 : ℝ) := by
    gcongr
    norm_num
  have hsqrt_nonneg : 0 ≤ (Nat.sqrt N : ℝ) := by positivity
  have hlog_sq_nonneg : 0 ≤ Real.log (N + 2 : ℝ) ^ 2 := sq_nonneg _
  have hprod := mul_le_mul (hsqrtN.trans hsqrtmono)
    (log_nat_add_two_sq_le_sixteen_sqrt N) hlog_sq_nonneg (Real.sqrt_nonneg _)
  have hsqrt_sq : Real.sqrt (N + 2 : ℝ) * Real.sqrt (N + 2 : ℝ) = N + 2 := by
    rw [Real.mul_self_sqrt]
    positivity
  have hN2 : (N + 2 : ℝ) ≤ 3 * N := by
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  nlinarith [hprod, hsqrt_sq]

lemma sum_Icc_one_eq_head_add_tail (f : ℕ → ℝ) (S N : ℕ) (hSN : S ≤ N) :
    (∑ k ∈ Finset.Icc 1 N, f k) =
      (∑ k ∈ Finset.Icc 1 S, f k) + ∑ k ∈ Finset.Icc (S + 1) N, f k := by
  have hdiff :
      (∑ k ∈ Finset.Icc 1 N, f k) - (∑ k ∈ Finset.Icc 1 S, f k) =
        ∑ k ∈ Finset.Icc (S + 1) N, f k := by
    induction N, hSN using Nat.le_induction with
    | base => simp
    | succ N hSN ih =>
        have h1N : 1 ≤ N + 1 := by omega
        have hSN' : S + 1 ≤ N + 1 := by omega
        rw [Finset.sum_Icc_succ_top h1N, Finset.sum_Icc_succ_top hSN']
        linarith
  linarith

lemma finite_inv_log_cube_sum_bound (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, 1 / Real.log (k + 2 : ℝ) ^ 3) ≤
      100 * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 := by
  by_cases hN0 : N = 0
  · subst N
    simp
  have hN : 1 ≤ N := Nat.pos_of_ne_zero hN0
  let S := Nat.sqrt N
  have hSN : S ≤ N := Nat.sqrt_le_self N
  have hsplit := sum_Icc_one_eq_head_add_tail
    (fun k : ℕ => 1 / Real.log (k + 2 : ℝ) ^ 3) S N hSN
  have hhead := finite_inv_log_cube_head_le S
  have htail := finite_inv_log_cube_tail_le S N
  have hlogNpos : 0 < Real.log (N + 2 : ℝ) := Real.log_pos (by norm_cast; omega)
  have hlogSpos : 0 < Real.log (S + 2 : ℝ) := Real.log_pos (by norm_cast; omega)
  have hlogcompare : Real.log (N + 2 : ℝ) ≤ 2 * Real.log (S + 2 : ℝ) := by
    simpa [S] using log_nat_add_two_le_two_log_sqrt_add_two N
  have hhead' :
      (∑ k ∈ Finset.Icc 1 S, 1 / Real.log (k + 2 : ℝ) ^ 3) ≤
        48 * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 :=
    hhead.trans (by simpa [S] using nat_sqrt_le_fortyeight_mul_div_log_sq N hN)
  have htail' :
      (∑ k ∈ Finset.Icc (S + 1) N, 1 / Real.log (k + 2 : ℝ) ^ 3) ≤
        48 * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 := by
    calc
      _ ≤ (N : ℝ) / Real.log (S + 2 : ℝ) ^ 3 := htail
      _ ≤ 48 * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 := by
            have hlogN_one : 1 ≤ Real.log (N + 2 : ℝ) := one_le_log_nat_add_two N hN
            rw [div_le_div_iff₀ (pow_pos hlogSpos 3) (pow_pos hlogNpos 2)]
            have hNnonneg : 0 ≤ (N : ℝ) := by positivity
            have hscalar :
                Real.log (N + 2 : ℝ) ^ 2 ≤
                  48 * Real.log (S + 2 : ℝ) ^ 3 := by
              nlinarith [sq_nonneg (Real.log (S + 2 : ℝ)),
                sq_nonneg (Real.log (N + 2 : ℝ))]
            convert mul_le_mul_of_nonneg_left hscalar hNnonneg using 1
            all_goals ring
  have htotal :
      (∑ k ∈ Finset.Icc 1 N, 1 / Real.log (k + 2 : ℝ) ^ 3) =
        (∑ k ∈ Finset.Icc 1 S, 1 / Real.log (k + 2 : ℝ) ^ 3) +
          ∑ k ∈ Finset.Icc (S + 1) N, 1 / Real.log (k + 2 : ℝ) ^ 3 := by
    linarith
  rw [htotal]
  calc
    _ ≤ 48 * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 +
          48 * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 := add_le_add hhead' htail'
    _ = 96 * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 := by ring
    _ ≤ 100 * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 := by
      gcongr
      norm_num

/--
The classical Mertens decay also gives the logarithmic Möbius summatory bound
needed by `ClassicalMertensAPI`.

The proof first applies finite Abel summation. The endpoint is controlled by
the existing cubic-log Mertens estimate, while the difference sum is reduced
to `finite_inv_log_cube_sum_bound` using
`log (k + 1) - log k ≤ 1 / k`.
-/
theorem mobiusLogSummatory_bound_of_decay (H : ClassicalMertensDecay) :
    ∃ C_L : ℝ, 0 < C_L ∧
      ∀ N : ℕ,
        |mobiusLogSummatory N| ≤
          C_L * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 := by
  rcases mertens_bound_of_decay H with ⟨C_M, hC_M_pos, hM⟩
  refine ⟨max (101 * C_M) 1,
    lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro N
  by_cases hN0 : N = 0
  · subst N
    simp [mobiusLogSummatory]
  have hN : 1 ≤ N := Nat.pos_of_ne_zero hN0
  have hlogN2pos : 0 < Real.log (N + 2 : ℝ) :=
    Real.log_pos (by norm_cast; omega)
  have hlogN1nonneg : 0 ≤ Real.log (N + 1 : ℝ) :=
    Real.log_nonneg (by norm_cast; omega)
  have hlogN1leN2 : Real.log (N + 1 : ℝ) ≤ Real.log (N + 2 : ℝ) := by
    exact Real.log_le_log (by positivity) (by norm_num)
  have hendpoint :
      |mobiusSummatory N * Real.log (N + 1 : ℝ)| ≤
        C_M * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 := by
    rw [abs_mul, abs_of_nonneg hlogN1nonneg]
    calc
      |mobiusSummatory N| * Real.log (N + 1 : ℝ)
          ≤ (C_M * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 3) *
              Real.log (N + 1 : ℝ) := by
            gcongr
            exact hM N
      _ ≤ (C_M * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 3) *
              Real.log (N + 2 : ℝ) := by
            gcongr
      _ = C_M * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 := by
            field_simp
  have hterm :
      ∀ k ∈ Finset.Icc 1 N,
        |mobiusSummatory k *
            (Real.log (k : ℝ) - Real.log ((k + 1 : ℕ) : ℝ))| ≤
          C_M * (1 / Real.log (k + 2 : ℝ) ^ 3) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk1)
    have hksuccpos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
    have hlogmono : Real.log (k : ℝ) ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
      Real.strictMonoOn_log.monotoneOn hkpos hksuccpos (by norm_num)
    have hdiff_nonneg :
        0 ≤ Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) := sub_nonneg.mpr hlogmono
    have hdiff := log_nat_succ_sub_log_nat_le_inv k hk1
    have hlogpos : 0 < Real.log (k + 2 : ℝ) := Real.log_pos (by norm_cast; omega)
    have hupper_nonneg :
        0 ≤ C_M * (k : ℝ) / Real.log (k + 2 : ℝ) ^ 3 := by positivity
    calc
      |mobiusSummatory k *
          (Real.log (k : ℝ) - Real.log ((k + 1 : ℕ) : ℝ))| =
          |mobiusSummatory k| *
            (Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ)) := by
            rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr hlogmono)]
            ring
      _ ≤ (C_M * (k : ℝ) / Real.log (k + 2 : ℝ) ^ 3) *
            (1 / (k : ℝ)) := by
            exact mul_le_mul (hM k) hdiff hdiff_nonneg hupper_nonneg
      _ = C_M * (1 / Real.log (k + 2 : ℝ) ^ 3) := by
            field_simp
  have hsum :
      |∑ k ∈ Finset.Icc 1 N,
          mobiusSummatory k *
            (Real.log (k : ℝ) - Real.log ((k + 1 : ℕ) : ℝ))| ≤
        100 * C_M * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 := by
    calc
      |∑ k ∈ Finset.Icc 1 N,
          mobiusSummatory k *
            (Real.log (k : ℝ) - Real.log ((k + 1 : ℕ) : ℝ))| ≤
          ∑ k ∈ Finset.Icc 1 N,
            |mobiusSummatory k *
              (Real.log (k : ℝ) - Real.log ((k + 1 : ℕ) : ℝ))| :=
            abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.Icc 1 N,
            C_M * (1 / Real.log (k + 2 : ℝ) ^ 3) := by
            exact Finset.sum_le_sum hterm
      _ = C_M *
          (∑ k ∈ Finset.Icc 1 N, 1 / Real.log (k + 2 : ℝ) ^ 3) := by
            rw [Finset.mul_sum]
      _ ≤ C_M * (100 * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2) := by
            exact mul_le_mul_of_nonneg_left (finite_inv_log_cube_sum_bound N) hC_M_pos.le
      _ = 100 * C_M * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 := by ring
  rw [mobiusLogSummatory_eq_abel_endpoint_add_sum]
  calc
    |mobiusSummatory N * Real.log (N + 1 : ℝ) +
        ∑ k ∈ Finset.Icc 1 N,
          mobiusSummatory k *
            (Real.log (k : ℝ) - Real.log ((k + 1 : ℕ) : ℝ))| ≤
        |mobiusSummatory N * Real.log (N + 1 : ℝ)| +
          |∑ k ∈ Finset.Icc 1 N,
            mobiusSummatory k *
              (Real.log (k : ℝ) - Real.log ((k + 1 : ℕ) : ℝ))| := abs_add_le _ _
    _ ≤ C_M * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 +
          100 * C_M * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 :=
      add_le_add hendpoint hsum
    _ = 101 * C_M * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 := by ring
    _ ≤ max (101 * C_M) 1 * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 := by
      gcongr
      exact le_max_left _ _

/--
Constructor bridge from the single classical Mertens decay hypothesis plus the
remaining non-Mertens residual inputs to the existing Phase 14 API.
-/
noncomputable def ClassicalMertensAPI.ofDecay
    (H : ClassicalMertensDecay) (R : ClassicalMertensResidualInputs) :
    ClassicalMertensAPI :=
  { C_M := Classical.choose (mertens_bound_of_decay H)
    C_L := R.C_L
    C_M_pos := (Classical.choose_spec (mertens_bound_of_decay H)).1
    C_L_pos := R.C_L_pos
    mertens_bound := (Classical.choose_spec (mertens_bound_of_decay H)).2
    mobiusLogSummatory_bound := R.mobiusLogSummatory_bound
    mobius_sum_zero := R.mobius_sum_zero
    mobiusLog_sum_neg_one := R.mobiusLog_sum_neg_one }

lemma tendsto_inv_log_nat_add_two :
    Tendsto (fun N : ℕ => 1 / Real.log (N + 2 : ℝ)) atTop (𝓝 0) := by
  have harg : Tendsto (fun N : ℕ => ((N + 2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  simpa [one_div] using (Real.tendsto_log_atTop.comp harg).inv_tendsto_atTop

lemma cutoffMobiusOverKSum_eq_partial_sub (N : ℕ) :
    cutoffMobiusOverKSum N =
      mobiusOverKPartial N - mobiusSummatory N / ((N + 1 : ℕ) : ℝ) := by
  unfold cutoffMobiusOverKSum mobiusOverKPartial mobiusSummatory
  calc
    _ = ∑ k ∈ Finset.Icc 1 N,
        (((ArithmeticFunction.moebius k : ℤ) : ℝ) / (k : ℝ) -
          ((ArithmeticFunction.moebius k : ℤ) : ℝ) / ((N + 1 : ℕ) : ℝ)) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hk0 : (k : ℝ) ≠ 0 := by
            exact_mod_cast (ne_of_gt (Finset.mem_Icc.mp hk).1)
          field_simp
    _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_div]

lemma cutoffMobiusLogOverKSum_eq_partial_sub (N : ℕ) :
    cutoffMobiusLogOverKSum N =
      mobiusLogOverKPartial N - mobiusLogSummatory N / ((N + 1 : ℕ) : ℝ) := by
  unfold cutoffMobiusLogOverKSum mobiusLogOverKPartial mobiusLogSummatory
  calc
    _ = ∑ k ∈ Finset.Icc 1 N,
        (((ArithmeticFunction.moebius k : ℤ) : ℝ) * Real.log (k : ℝ) / (k : ℝ) -
          ((ArithmeticFunction.moebius k : ℤ) : ℝ) * Real.log (k : ℝ) /
            ((N + 1 : ℕ) : ℝ)) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hk0 : (k : ℝ) ≠ 0 := by
            exact_mod_cast (ne_of_gt (Finset.mem_Icc.mp hk).1)
          field_simp
    _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_div]

lemma sum_Icc_one_sub_sum_Icc_one (f : ℕ → ℝ) (N R : ℕ) (hNR : N ≤ R) :
    (∑ k ∈ Finset.Icc 1 R, f k) - (∑ k ∈ Finset.Icc 1 N, f k) =
      ∑ k ∈ Finset.Icc (N + 1) R, f k := by
  induction R, hNR using Nat.le_induction with
  | base => simp
  | succ R hNR ih =>
      have h1R : 1 ≤ R + 1 := by omega
      have hNR' : N + 1 ≤ R + 1 := by omega
      rw [Finset.sum_Icc_succ_top h1R, Finset.sum_Icc_succ_top hNR']
      calc
        _ = ((∑ k ∈ Finset.Icc 1 R, f k) - (∑ k ∈ Finset.Icc 1 N, f k)) +
            f (R + 1) := by ring
        _ = _ := by rw [ih]

lemma ClassicalMertensAPI.mobius_ratio_tendsto_zero (api : ClassicalMertensAPI) :
    Tendsto (fun N : ℕ => mobiusSummatory N / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hmajorant :
      Tendsto (fun N : ℕ => api.C_M * (1 / Real.log (N + 2 : ℝ)) ^ 3) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (tendsto_inv_log_nat_add_two.pow 3))
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N : ℕ => abs_nonneg _)
    (Eventually.of_forall fun N : ℕ => ?_) hmajorant
  calc
    |mobiusSummatory N / ((N + 1 : ℕ) : ℝ)| =
        |mobiusSummatory N| / ((N + 1 : ℕ) : ℝ) := by
          rw [abs_div]
          congr 1
          exact abs_of_pos (by exact_mod_cast Nat.succ_pos N)
    _ ≤ (api.C_M * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 3) /
          ((N + 1 : ℕ) : ℝ) := by
            gcongr
            exact api.mertens_bound N
    _ ≤ api.C_M * (1 / Real.log (N + 2 : ℝ)) ^ 3 := by
          have hlog : 0 < Real.log (N + 2 : ℝ) := Real.log_pos (by norm_cast; omega)
          have hN : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by norm_cast; omega
          field_simp
          nlinarith [api.C_M_pos]

/--
The Mertens ratio `M(N)/(N+1)` tends to zero under the single de la Vallée
Poussin decay input.
-/
lemma mobius_ratio_tendsto_zero_of_decay (H : ClassicalMertensDecay) :
    Tendsto (fun N : ℕ => mobiusSummatory N / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  rcases mertens_bound_of_decay H with ⟨C_M, hC_M_pos, hM⟩
  have hmajorant :
      Tendsto (fun N : ℕ => C_M * (1 / Real.log (N + 2 : ℝ)) ^ 3) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (tendsto_inv_log_nat_add_two.pow 3))
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N : ℕ => abs_nonneg _)
    (Eventually.of_forall fun N : ℕ => ?_) hmajorant
  calc
    |mobiusSummatory N / ((N + 1 : ℕ) : ℝ)| =
        |mobiusSummatory N| / ((N + 1 : ℕ) : ℝ) := by
          rw [abs_div]
          congr 1
          exact abs_of_pos (by exact_mod_cast Nat.succ_pos N)
    _ ≤ (C_M * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 3) /
          ((N + 1 : ℕ) : ℝ) := by
            gcongr
            exact hM N
    _ ≤ C_M * (1 / Real.log (N + 2 : ℝ)) ^ 3 := by
          have hlog : 0 < Real.log (N + 2 : ℝ) := Real.log_pos (by norm_cast; omega)
          have hN : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by norm_cast; omega
          field_simp
          nlinarith [hC_M_pos]

lemma ClassicalMertensAPI.mobiusLog_ratio_tendsto_zero (api : ClassicalMertensAPI) :
    Tendsto (fun N : ℕ => mobiusLogSummatory N / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hmajorant :
      Tendsto (fun N : ℕ => api.C_L * (1 / Real.log (N + 2 : ℝ)) ^ 2) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (tendsto_inv_log_nat_add_two.pow 2))
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N : ℕ => abs_nonneg _)
    (Eventually.of_forall fun N : ℕ => ?_) hmajorant
  calc
    |mobiusLogSummatory N / ((N + 1 : ℕ) : ℝ)| =
        |mobiusLogSummatory N| / ((N + 1 : ℕ) : ℝ) := by
          rw [abs_div]
          congr 1
          exact abs_of_pos (by exact_mod_cast Nat.succ_pos N)
    _ ≤ (api.C_L * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2) /
          ((N + 1 : ℕ) : ℝ) := by
            gcongr
            exact api.mobiusLogSummatory_bound N
    _ ≤ api.C_L * (1 / Real.log (N + 2 : ℝ)) ^ 2 := by
          have hlog : 0 < Real.log (N + 2 : ℝ) := Real.log_pos (by norm_cast; omega)
          have hN : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by norm_cast; omega
          field_simp
          nlinarith [api.C_L_pos]

lemma ClassicalMertensAPI.cutoff_overK_tendsto_zero (api : ClassicalMertensAPI) :
    Tendsto cutoffMobiusOverKSum atTop (𝓝 0) := by
  have h : Tendsto (fun N =>
      mobiusOverKPartial N - mobiusSummatory N / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa using api.mobius_sum_zero.sub api.mobius_ratio_tendsto_zero
  exact h.congr' (Eventually.of_forall fun N => (cutoffMobiusOverKSum_eq_partial_sub N).symm)

lemma ClassicalMertensAPI.cutoff_log_plus_one_tendsto_zero (api : ClassicalMertensAPI) :
    Tendsto (fun N : ℕ => cutoffMobiusLogOverKSum N + 1) atTop (𝓝 0) := by
  have h : Tendsto (fun N =>
      mobiusLogOverKPartial N - mobiusLogSummatory N / ((N + 1 : ℕ) : ℝ) + 1) atTop (𝓝 0) := by
    simpa [add_assoc] using
      (api.mobiusLog_sum_neg_one.sub api.mobiusLog_ratio_tendsto_zero).add
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  exact h.congr' (Eventually.of_forall fun N => by
    simp [cutoffMobiusLogOverKSum_eq_partial_sub, add_comm])

lemma ClassicalMertensAPI.overK_difference_bound (api : ClassicalMertensAPI)
    (N R : ℕ) (hNR : N ≤ R) :
    |cutoffMobiusOverKSum R - cutoffMobiusOverKSum N| ≤
      12 * api.C_M / Real.log (N + 2 : ℝ) := by
  rw [cutoffMobiusOverKSum_eq_abel_sum, cutoffMobiusOverKSum_eq_abel_sum,
    sum_Icc_one_sub_sum_Icc_one _ N R hNR]
  calc
    |∑ k ∈ Finset.Icc (N + 1) R,
        mobiusSummatory k * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))|
      ≤ ∑ k ∈ Finset.Icc (N + 1) R,
          |mobiusSummatory k * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Icc (N + 1) R,
        api.C_M * (1 / (((k + 1 : ℕ) : ℝ) * Real.log (k + 2 : ℝ) ^ 3)) := by
          apply Finset.sum_le_sum
          intro k hk
          have hkpos : 0 < k := lt_of_lt_of_le (by omega) (Finset.mem_Icc.mp hk).1
          have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
          have hdiff : 0 ≤ 1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ) := by
            exact sub_nonneg.mpr (one_div_le_one_div_of_le hkR (by norm_cast; omega))
          rw [abs_mul, abs_of_nonneg hdiff]
          calc
            |mobiusSummatory k| * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))
              ≤ (api.C_M * (k : ℝ) / Real.log (k + 2 : ℝ) ^ 3) *
                  (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) := by
                    exact mul_le_mul_of_nonneg_right (api.mertens_bound k) hdiff
            _ = api.C_M * (1 / (((k + 1 : ℕ) : ℝ) * Real.log (k + 2 : ℝ) ^ 3)) := by
                  field_simp
                  norm_num [Nat.cast_add]
    _ = api.C_M * (∑ k ∈ Finset.Icc (N + 1) R,
        1 / (((k + 1 : ℕ) : ℝ) * Real.log (k + 2 : ℝ) ^ 3)) := by
          rw [Finset.mul_sum]
    _ ≤ api.C_M * (12 / Real.log (N + 2 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left (finite_log_cubed_tail_bound N R) api.C_M_pos.le
    _ = _ := by ring

/--
Tail Cauchy bound for the cutoff Abel transform, using only an explicit
polynomial-log Mertens bound.
-/
lemma cutoffMobiusOverKSum_difference_bound_of_mertens_bound
    {C_M : ℝ} (hC_M_nonneg : 0 ≤ C_M)
    (hM : ∀ N : ℕ,
      |mobiusSummatory N| ≤ C_M * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 3)
    (N R : ℕ) (hNR : N ≤ R) :
    |cutoffMobiusOverKSum R - cutoffMobiusOverKSum N| ≤
      12 * C_M / Real.log (N + 2 : ℝ) := by
  rw [cutoffMobiusOverKSum_eq_abel_sum, cutoffMobiusOverKSum_eq_abel_sum,
    sum_Icc_one_sub_sum_Icc_one _ N R hNR]
  calc
    |∑ k ∈ Finset.Icc (N + 1) R,
        mobiusSummatory k * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))|
      ≤ ∑ k ∈ Finset.Icc (N + 1) R,
          |mobiusSummatory k * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Icc (N + 1) R,
        C_M * (1 / (((k + 1 : ℕ) : ℝ) * Real.log (k + 2 : ℝ) ^ 3)) := by
          apply Finset.sum_le_sum
          intro k hk
          have hkpos : 0 < k := lt_of_lt_of_le (by omega) (Finset.mem_Icc.mp hk).1
          have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
          have hdiff : 0 ≤ 1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ) := by
            exact sub_nonneg.mpr (one_div_le_one_div_of_le hkR (by norm_cast; omega))
          rw [abs_mul, abs_of_nonneg hdiff]
          calc
            |mobiusSummatory k| * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))
              ≤ (C_M * (k : ℝ) / Real.log (k + 2 : ℝ) ^ 3) *
                  (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) := by
                    exact mul_le_mul_of_nonneg_right (hM k) hdiff
            _ = C_M * (1 / (((k + 1 : ℕ) : ℝ) * Real.log (k + 2 : ℝ) ^ 3)) := by
                  field_simp
                  norm_num [Nat.cast_add]
    _ = C_M * (∑ k ∈ Finset.Icc (N + 1) R,
        1 / (((k + 1 : ℕ) : ℝ) * Real.log (k + 2 : ℝ) ^ 3)) := by
          rw [Finset.mul_sum]
    _ ≤ C_M * (12 / Real.log (N + 2 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left (finite_log_cubed_tail_bound N R) hC_M_nonneg
    _ = _ := by ring

/--
The cutoff Abel transform is Cauchy under the single de la Vallée Poussin decay
input.  This is the convergence half of the classical Axer step; it does not
identify the limiting value.
-/
lemma cutoffMobiusOverKSum_cauchySeq_of_decay (H : ClassicalMertensDecay) :
    CauchySeq cutoffMobiusOverKSum := by
  rcases mertens_bound_of_decay H with ⟨C_M, hC_M_pos, hM⟩
  refine cauchySeq_of_le_tendsto_0 (fun N : ℕ => 12 * C_M / Real.log (N + 2 : ℝ)) ?_ ?_
  · intro n m N hNn hNm
    have hlogN : 0 < Real.log (N + 2 : ℝ) := Real.log_pos (by norm_cast; omega)
    by_cases hnm : n ≤ m
    · have hdiff :=
        cutoffMobiusOverKSum_difference_bound_of_mertens_bound hC_M_pos.le hM n m hnm
      have hlogn : 0 < Real.log (n + 2 : ℝ) := Real.log_pos (by norm_cast; omega)
      have hmono : Real.log (N + 2 : ℝ) ≤ Real.log (n + 2 : ℝ) := by
        exact Real.log_le_log (by positivity) (by norm_cast; omega)
      have htail :
          12 * C_M / Real.log (n + 2 : ℝ) ≤
            12 * C_M / Real.log (N + 2 : ℝ) := by
        have hcoeff : 0 ≤ 12 * C_M := by positivity
        exact mul_le_mul_of_nonneg_left
          (by simpa [one_div] using one_div_le_one_div_of_le hlogN hmono) hcoeff
      calc
        dist (cutoffMobiusOverKSum n) (cutoffMobiusOverKSum m)
            = |cutoffMobiusOverKSum m - cutoffMobiusOverKSum n| := by
              rw [Real.dist_eq, abs_sub_comm]
        _ ≤ 12 * C_M / Real.log (n + 2 : ℝ) := hdiff
        _ ≤ 12 * C_M / Real.log (N + 2 : ℝ) := htail
    · have hmn : m ≤ n := le_of_not_ge hnm
      have hdiff :=
        cutoffMobiusOverKSum_difference_bound_of_mertens_bound hC_M_pos.le hM m n hmn
      have hlogm : 0 < Real.log (m + 2 : ℝ) := Real.log_pos (by norm_cast; omega)
      have hmono : Real.log (N + 2 : ℝ) ≤ Real.log (m + 2 : ℝ) := by
        exact Real.log_le_log (by positivity) (by norm_cast; omega)
      have htail :
          12 * C_M / Real.log (m + 2 : ℝ) ≤
            12 * C_M / Real.log (N + 2 : ℝ) := by
        have hcoeff : 0 ≤ 12 * C_M := by positivity
        exact mul_le_mul_of_nonneg_left
          (by simpa [one_div] using one_div_le_one_div_of_le hlogN hmono) hcoeff
      calc
        dist (cutoffMobiusOverKSum n) (cutoffMobiusOverKSum m)
            = |cutoffMobiusOverKSum n - cutoffMobiusOverKSum m| := by
              rw [Real.dist_eq]
        _ ≤ 12 * C_M / Real.log (m + 2 : ℝ) := hdiff
        _ ≤ 12 * C_M / Real.log (N + 2 : ℝ) := htail
  · simpa [div_eq_mul_inv, mul_assoc] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => 12 * C_M) atTop (𝓝 (12 * C_M))).mul
        tendsto_inv_log_nat_add_two)

/--
R2a: under classical de la Vallée Poussin decay, the partial sums
`∑_{k≤N} μ(k)/k` converge to some real limit.

The Axer normalization identifying this limit with `0` is not claimed here.
-/
lemma mobiusOverKPartial_convergent_of_decay (H : ClassicalMertensDecay) :
    ∃ ℓ : ℝ, Tendsto mobiusOverKPartial atTop (𝓝 ℓ) := by
  rcases cauchySeq_tendsto_of_complete (cutoffMobiusOverKSum_cauchySeq_of_decay H) with
    ⟨ℓ, hℓ⟩
  refine ⟨ℓ, ?_⟩
  have hsum := hℓ.add (mobius_ratio_tendsto_zero_of_decay H)
  simpa using hsum.congr' (Eventually.of_forall fun N => by
    rw [cutoffMobiusOverKSum_eq_partial_sub]
    ring)

/--
Residual Axer normalization after the convergence half has been proved from
`ClassicalMertensDecay`.

This is intentionally weaker and more precise than assuming
`mobius_sum_zero` directly: the remaining classical content is only that the
already-existing limit of `∑_{k≤N} μ(k)/k` is the value `0`.
-/
structure MobiusOverKLimitIsZero where
  limit_eq_zero :
    ∀ ℓ : ℝ, Tendsto mobiusOverKPartial atTop (𝓝 ℓ) → ℓ = 0

/-- Classical Mertens decay discharges the Axer normalization residual. -/
theorem mobiusOverKLimitIsZero_of_decay
    (H : ClassicalMertensDecay) : MobiusOverKLimitIsZero where
  limit_eq_zero := by
    intro ℓ hℓ
    exact tendsto_nhds_unique hℓ (mobiusOverK_tendsto_zero_of_decay H)

/--
The old `mobius_sum_zero` field follows from decay plus the remaining Axer
normalization residual.
-/
lemma mobius_sum_zero_of_decay_and_limit_zero
    (H : ClassicalMertensDecay) (Z : MobiusOverKLimitIsZero) :
    Tendsto mobiusOverKPartial atTop (𝓝 0) := by
  rcases mobiusOverKPartial_convergent_of_decay H with ⟨ℓ, hℓ⟩
  simpa [Z.limit_eq_zero ℓ hℓ] using hℓ

/--
Slimmed residual inputs after deriving the Mertens polynomial-log bound and
the convergence half of the `μ(k)/k` boundary value from
`ClassicalMertensDecay`.

Compared with `ClassicalMertensResidualInputs`, the `mobius_sum_zero` field is
replaced by the narrower `mobius_overK_limit_zero` normalization statement.
The logarithmic summatory bound and the logarithmic boundary value remain
separate residuals.
-/
structure ClassicalMertensResidualInputsOfDecay where
  C_L : ℝ
  C_L_pos : 0 < C_L
  mobiusLogSummatory_bound :
    ∀ N : ℕ,
      |mobiusLogSummatory N| ≤ C_L * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2
  mobius_overK_limit_zero : MobiusOverKLimitIsZero
  mobiusLog_sum_neg_one : Tendsto mobiusLogOverKPartial atTop (𝓝 (-1))

/--
Additive constructor exposing the residual shrinkage achieved by the H14
decay/convergence work.  The original `ClassicalMertensAPI.ofDecay` is left
unchanged.
-/
noncomputable def ClassicalMertensAPI.ofDecay'
    (H : ClassicalMertensDecay) (R : ClassicalMertensResidualInputsOfDecay) :
    ClassicalMertensAPI :=
  { C_M := Classical.choose (mertens_bound_of_decay H)
    C_L := R.C_L
    C_M_pos := (Classical.choose_spec (mertens_bound_of_decay H)).1
    C_L_pos := R.C_L_pos
    mertens_bound := (Classical.choose_spec (mertens_bound_of_decay H)).2
    mobiusLogSummatory_bound := R.mobiusLogSummatory_bound
    mobius_sum_zero :=
      mobius_sum_zero_of_decay_and_limit_zero H R.mobius_overK_limit_zero
    mobiusLog_sum_neg_one := R.mobiusLog_sum_neg_one }

/--
The two boundary normalizations still needed after deriving both quantitative
summatory bounds from `ClassicalMertensDecay`.

The first field records the Axer identification of the already-proved limit of
`mobiusOverKPartial`; the second is the logarithmic boundary normalization.
-/
structure ClassicalMertensBoundaryResidualInputs where
  mobius_overK_limit_zero : MobiusOverKLimitIsZero
  mobiusLog_sum_neg_one : Tendsto mobiusLogOverKPartial atTop (𝓝 (-1))

/--
Assemble `ClassicalMertensAPI` from Mertens decay and only the two remaining
boundary normalizations.

This is additive: the earlier residual structures and constructors remain
available unchanged.
-/
noncomputable def ClassicalMertensAPI.ofDecay''
    (H : ClassicalMertensDecay) (R : ClassicalMertensBoundaryResidualInputs) :
    ClassicalMertensAPI :=
  { C_M := Classical.choose (mertens_bound_of_decay H)
    C_L := Classical.choose (mobiusLogSummatory_bound_of_decay H)
    C_M_pos := (Classical.choose_spec (mertens_bound_of_decay H)).1
    C_L_pos := (Classical.choose_spec (mobiusLogSummatory_bound_of_decay H)).1
    mertens_bound := (Classical.choose_spec (mertens_bound_of_decay H)).2
    mobiusLogSummatory_bound :=
      (Classical.choose_spec (mobiusLogSummatory_bound_of_decay H)).2
    mobius_sum_zero :=
      mobius_sum_zero_of_decay_and_limit_zero H R.mobius_overK_limit_zero
    mobiusLog_sum_neg_one := R.mobiusLog_sum_neg_one }

/--
The sole remaining H14 boundary input after the quantitative Axer step has
been derived from `ClassicalMertensDecay`.
-/
structure ClassicalMertensLogBoundaryResidualInput where
  mobiusLog_sum_neg_one : Tendsto mobiusLogOverKPartial atTop (𝓝 (-1))

/--
Assemble the classical H14 API from decay and only the logarithmic boundary
normalization.  Earlier constructors are intentionally left unchanged.
-/
noncomputable def ClassicalMertensAPI.ofDecay'''
    (H : ClassicalMertensDecay)
    (R : ClassicalMertensLogBoundaryResidualInput) : ClassicalMertensAPI :=
  { C_M := Classical.choose (mertens_bound_of_decay H)
    C_L := Classical.choose (mobiusLogSummatory_bound_of_decay H)
    C_M_pos := (Classical.choose_spec (mertens_bound_of_decay H)).1
    C_L_pos := (Classical.choose_spec (mobiusLogSummatory_bound_of_decay H)).1
    mertens_bound := (Classical.choose_spec (mertens_bound_of_decay H)).2
    mobiusLogSummatory_bound :=
      (Classical.choose_spec (mobiusLogSummatory_bound_of_decay H)).2
    mobius_sum_zero := mobiusOverK_tendsto_zero_of_decay H
    mobiusLog_sum_neg_one := R.mobiusLog_sum_neg_one }

lemma ClassicalMertensAPI.logOverK_difference_bound (api : ClassicalMertensAPI)
    (N R : ℕ) (hNR : N ≤ R) :
    |(cutoffMobiusLogOverKSum R + 1) - (cutoffMobiusLogOverKSum N + 1)| ≤
      6 * api.C_L / Real.log (N + 2 : ℝ) := by
  rw [cutoffMobiusLogOverKSum_eq_abel_sum, cutoffMobiusLogOverKSum_eq_abel_sum]
  have hshift :
      (1 + ∑ k ∈ Finset.Icc 1 R,
          mobiusLogSummatory k * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))) -
        (1 + ∑ k ∈ Finset.Icc 1 N,
          mobiusLogSummatory k * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))) =
      (∑ k ∈ Finset.Icc 1 R,
          mobiusLogSummatory k * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))) -
        (∑ k ∈ Finset.Icc 1 N,
          mobiusLogSummatory k * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))) := by ring
  rw [hshift, sum_Icc_one_sub_sum_Icc_one _ N R hNR]
  calc
    |∑ k ∈ Finset.Icc (N + 1) R,
        mobiusLogSummatory k * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))|
      ≤ ∑ k ∈ Finset.Icc (N + 1) R,
          |mobiusLogSummatory k * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Icc (N + 1) R,
        api.C_L * (1 / (((k + 1 : ℕ) : ℝ) * Real.log (k + 2 : ℝ) ^ 2)) := by
          apply Finset.sum_le_sum
          intro k hk
          have hkpos : 0 < k := lt_of_lt_of_le (by omega) (Finset.mem_Icc.mp hk).1
          have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
          have hdiff : 0 ≤ 1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ) := by
            exact sub_nonneg.mpr (one_div_le_one_div_of_le hkR (by norm_cast; omega))
          rw [abs_mul, abs_of_nonneg hdiff]
          calc
            |mobiusLogSummatory k| * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))
              ≤ (api.C_L * (k : ℝ) / Real.log (k + 2 : ℝ) ^ 2) *
                  (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) := by
                    exact mul_le_mul_of_nonneg_right (api.mobiusLogSummatory_bound k) hdiff
            _ = api.C_L * (1 / (((k + 1 : ℕ) : ℝ) * Real.log (k + 2 : ℝ) ^ 2)) := by
                  field_simp
                  norm_num [Nat.cast_add]
    _ = api.C_L * (∑ k ∈ Finset.Icc (N + 1) R,
        1 / (((k + 1 : ℕ) : ℝ) * Real.log (k + 2 : ℝ) ^ 2)) := by
          rw [Finset.mul_sum]
    _ ≤ api.C_L * (6 / Real.log (N + 2 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left (finite_log_tail_bound N R) api.C_L_pos.le
    _ = _ := by ring

lemma ClassicalMertensAPI.overK_bound (api : ClassicalMertensAPI) (N : ℕ) :
    |cutoffMobiusOverKSum N| ≤ 12 * api.C_M / Real.log (N + 2 : ℝ) := by
  have htendsto := (api.cutoff_overK_tendsto_zero.sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => cutoffMobiusOverKSum N) atTop (𝓝 _))).abs
  have hle : ∀ᶠ R : ℕ in atTop,
      |cutoffMobiusOverKSum R - cutoffMobiusOverKSum N| ≤
        12 * api.C_M / Real.log (N + 2 : ℝ) := by
    filter_upwards [eventually_ge_atTop N] with R hNR
    exact api.overK_difference_bound N R hNR
  have hlimit := le_of_tendsto htendsto hle
  simpa using hlimit

lemma ClassicalMertensAPI.logOverK_bound (api : ClassicalMertensAPI) (N : ℕ) :
    |cutoffMobiusLogOverKSum N + 1| ≤ 6 * api.C_L / Real.log (N + 2 : ℝ) := by
  have htendsto := (api.cutoff_log_plus_one_tendsto_zero.sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => cutoffMobiusLogOverKSum N + 1) atTop (𝓝 _))).abs
  have hle : ∀ᶠ R : ℕ in atTop,
      |(cutoffMobiusLogOverKSum R + 1) - (cutoffMobiusLogOverKSum N + 1)| ≤
        6 * api.C_L / Real.log (N + 2 : ℝ) := by
    filter_upwards [eventually_ge_atTop N] with R hNR
    exact api.logOverK_difference_bound N R hNR
  have hlimit := le_of_tendsto htendsto hle
  have hrewrite : |0 - (cutoffMobiusLogOverKSum N + 1)| = |cutoffMobiusLogOverKSum N + 1| := by
    rw [zero_sub, abs_neg]
  rw [← hrewrite]
  exact hlimit

noncomputable def mobius_pnt_style_of_classical_api (api : ClassicalMertensAPI) :
    MobiusPNTStyleEstimates :=
  { C_M := 12 * api.C_M
    C_L := 6 * api.C_L
    C_M_nonneg := mul_nonneg (by norm_num) api.C_M_pos.le
    C_L_pos := mul_pos (by norm_num) api.C_L_pos
    mobius_abel_bound := by
      intro N
      rw [← cutoffMobiusOverKSum_eq_abel_sum]
      exact api.overK_bound N
    mobiusLog_abel_bound := by
      intro N
      rw [← cutoffMobiusLogOverKSum_eq_abel_sum]
      exact api.logOverK_bound N }

noncomputable def linear_mobius_dirichlet_estimates_of_classical_api
    (api : ClassicalMertensAPI) :
    LinearMobiusDirichletEstimates :=
  linear_mobius_dirichlet_estimates_of_pnt_style
    (mobius_pnt_style_of_classical_api api)

-- ---------------------------------------------------------------------------
-- H14 final field, B1. Convergence of the logarithmic boundary series
-- ---------------------------------------------------------------------------

/--
Tail Cauchy bound for the logarithmic cutoff Abel transform, using only an
explicit quadratic-log bound for `mobiusLogSummatory`.
-/
lemma cutoffMobiusLogOverKSum_difference_bound_of_log_summatory_bound
    {C_L : ℝ} (hC_L_nonneg : 0 ≤ C_L)
    (hL : ∀ N : ℕ,
      |mobiusLogSummatory N| ≤ C_L * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2)
    (N R : ℕ) (hNR : N ≤ R) :
    |cutoffMobiusLogOverKSum R - cutoffMobiusLogOverKSum N| ≤
      6 * C_L / Real.log (N + 2 : ℝ) := by
  have hshift :
      cutoffMobiusLogOverKSum R - cutoffMobiusLogOverKSum N =
        (cutoffMobiusLogOverKSum R + 1) - (cutoffMobiusLogOverKSum N + 1) := by
    ring
  rw [hshift, cutoffMobiusLogOverKSum_eq_abel_sum, cutoffMobiusLogOverKSum_eq_abel_sum]
  have hcancel :
      (1 + ∑ k ∈ Finset.Icc 1 R,
          mobiusLogSummatory k * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))) -
        (1 + ∑ k ∈ Finset.Icc 1 N,
          mobiusLogSummatory k * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))) =
      (∑ k ∈ Finset.Icc 1 R,
          mobiusLogSummatory k * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))) -
        ∑ k ∈ Finset.Icc 1 N,
          mobiusLogSummatory k * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) := by
    ring
  rw [hcancel, sum_Icc_one_sub_sum_Icc_one _ N R hNR]
  calc
    |∑ k ∈ Finset.Icc (N + 1) R,
        mobiusLogSummatory k * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))|
      ≤ ∑ k ∈ Finset.Icc (N + 1) R,
          |mobiusLogSummatory k * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Icc (N + 1) R,
        C_L * (1 / (((k + 1 : ℕ) : ℝ) * Real.log (k + 2 : ℝ) ^ 2)) := by
          apply Finset.sum_le_sum
          intro k hk
          have hkpos : 0 < k := lt_of_lt_of_le (by omega) (Finset.mem_Icc.mp hk).1
          have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
          have hdiff : 0 ≤ 1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ) := by
            exact sub_nonneg.mpr (one_div_le_one_div_of_le hkR (by norm_cast; omega))
          rw [abs_mul, abs_of_nonneg hdiff]
          calc
            |mobiusLogSummatory k| * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))
              ≤ (C_L * (k : ℝ) / Real.log (k + 2 : ℝ) ^ 2) *
                  (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) := by
                    exact mul_le_mul_of_nonneg_right (hL k) hdiff
            _ = C_L *
                (1 / (((k + 1 : ℕ) : ℝ) * Real.log (k + 2 : ℝ) ^ 2)) := by
                  field_simp
                  norm_num [Nat.cast_add]
    _ = C_L * (∑ k ∈ Finset.Icc (N + 1) R,
        1 / (((k + 1 : ℕ) : ℝ) * Real.log (k + 2 : ℝ) ^ 2)) := by
          rw [Finset.mul_sum]
    _ ≤ C_L * (6 / Real.log (N + 2 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left (finite_log_tail_bound N R) hC_L_nonneg
    _ = _ := by ring

/--
The logarithmic cutoff Abel transform is Cauchy under
`ClassicalMertensDecay`.
-/
lemma cutoffMobiusLogOverKSum_cauchySeq_of_decay (H : ClassicalMertensDecay) :
    CauchySeq cutoffMobiusLogOverKSum := by
  rcases mobiusLogSummatory_bound_of_decay H with ⟨C_L, hC_L_pos, hL⟩
  refine cauchySeq_of_le_tendsto_0 (fun N : ℕ => 6 * C_L / Real.log (N + 2 : ℝ)) ?_ ?_
  · intro n m N hNn hNm
    have hlogN : 0 < Real.log (N + 2 : ℝ) := Real.log_pos (by norm_cast; omega)
    by_cases hnm : n ≤ m
    · have hdiff :=
        cutoffMobiusLogOverKSum_difference_bound_of_log_summatory_bound
          hC_L_pos.le hL n m hnm
      have hmono : Real.log (N + 2 : ℝ) ≤ Real.log (n + 2 : ℝ) := by
        exact Real.log_le_log (by positivity) (by norm_cast; omega)
      have htail :
          6 * C_L / Real.log (n + 2 : ℝ) ≤
            6 * C_L / Real.log (N + 2 : ℝ) := by
        have hcoeff : 0 ≤ 6 * C_L := by positivity
        exact mul_le_mul_of_nonneg_left
          (by simpa [one_div] using one_div_le_one_div_of_le hlogN hmono) hcoeff
      calc
        dist (cutoffMobiusLogOverKSum n) (cutoffMobiusLogOverKSum m)
            = |cutoffMobiusLogOverKSum m - cutoffMobiusLogOverKSum n| := by
              rw [Real.dist_eq, abs_sub_comm]
        _ ≤ 6 * C_L / Real.log (n + 2 : ℝ) := hdiff
        _ ≤ 6 * C_L / Real.log (N + 2 : ℝ) := htail
    · have hmn : m ≤ n := le_of_not_ge hnm
      have hdiff :=
        cutoffMobiusLogOverKSum_difference_bound_of_log_summatory_bound
          hC_L_pos.le hL m n hmn
      have hmono : Real.log (N + 2 : ℝ) ≤ Real.log (m + 2 : ℝ) := by
        exact Real.log_le_log (by positivity) (by norm_cast; omega)
      have htail :
          6 * C_L / Real.log (m + 2 : ℝ) ≤
            6 * C_L / Real.log (N + 2 : ℝ) := by
        have hcoeff : 0 ≤ 6 * C_L := by positivity
        exact mul_le_mul_of_nonneg_left
          (by simpa [one_div] using one_div_le_one_div_of_le hlogN hmono) hcoeff
      calc
        dist (cutoffMobiusLogOverKSum n) (cutoffMobiusLogOverKSum m)
            = |cutoffMobiusLogOverKSum n - cutoffMobiusLogOverKSum m| := by
              rw [Real.dist_eq]
        _ ≤ 6 * C_L / Real.log (m + 2 : ℝ) := hdiff
        _ ≤ 6 * C_L / Real.log (N + 2 : ℝ) := htail
  · simpa [div_eq_mul_inv, mul_assoc] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => 6 * C_L) atTop (𝓝 (6 * C_L))).mul
        tendsto_inv_log_nat_add_two)

/-- The endpoint term in logarithmic Abel summation tends to zero. -/
lemma mobiusLog_ratio_tendsto_zero_of_decay (H : ClassicalMertensDecay) :
    Tendsto (fun N : ℕ => mobiusLogSummatory N / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  rcases mobiusLogSummatory_bound_of_decay H with ⟨C_L, hC_L_pos, hL⟩
  have hmajorant :
      Tendsto (fun N : ℕ => C_L * (1 / Real.log (N + 2 : ℝ)) ^ 2) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (tendsto_inv_log_nat_add_two.pow 2))
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N : ℕ => abs_nonneg _)
    (Eventually.of_forall fun N : ℕ => ?_) hmajorant
  calc
    |mobiusLogSummatory N / ((N + 1 : ℕ) : ℝ)| =
        |mobiusLogSummatory N| / ((N + 1 : ℕ) : ℝ) := by
          rw [abs_div]
          congr 1
          exact abs_of_pos (by exact_mod_cast Nat.succ_pos N)
    _ ≤ (C_L * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2) /
          ((N + 1 : ℕ) : ℝ) := by
            gcongr
            exact hL N
    _ ≤ C_L * (1 / Real.log (N + 2 : ℝ)) ^ 2 := by
          have hlog : 0 < Real.log (N + 2 : ℝ) := Real.log_pos (by norm_cast; omega)
          have hN : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by norm_cast; omega
          field_simp
          nlinarith [hC_L_pos]

/--
B1: the partial sums `∑_{k≤N} μ(k) log(k) / k` converge under the single
de la Vallée Poussin Mertens decay input.
-/
theorem mobiusLogOverKPartial_convergent_of_decay (H : ClassicalMertensDecay) :
    ∃ ℓ : ℝ, Tendsto mobiusLogOverKPartial atTop (𝓝 ℓ) := by
  rcases cauchySeq_tendsto_of_complete (cutoffMobiusLogOverKSum_cauchySeq_of_decay H) with
    ⟨ℓ, hℓ⟩
  refine ⟨ℓ, ?_⟩
  have hsum := hℓ.add (mobiusLog_ratio_tendsto_zero_of_decay H)
  simpa using hsum.congr' (Eventually.of_forall fun N => by
    rw [cutoffMobiusLogOverKSum_eq_partial_sub]
    ring)

-- ---------------------------------------------------------------------------
-- H14 final field, B2. Möbius logarithmic L-series identity
-- ---------------------------------------------------------------------------

section MobiusLogLSeries

open Complex
open scoped ArithmeticFunction LSeries.notation

/-- Complex coefficient sequence `μ(n) log n`. -/
noncomputable def mobiusLogCoeffC (n : ℕ) : ℂ :=
  (Real.log (n : ℝ) : ℂ) * ((ArithmeticFunction.moebius n : ℤ) : ℂ)

lemma mobius_LSeries_eq_inv_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    L ↗ArithmeticFunction.moebius s = (riemannZeta s)⁻¹ := by
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  rw [← one_div]
  apply (eq_div_iff hz).2
  have hmul := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at hmul
  simpa [mul_comm] using hmul

lemma deriv_mobius_LSeries_eq_neg_zeta_deriv_div_sq {s : ℂ} (hs : 1 < s.re) :
    deriv (L ↗ArithmeticFunction.moebius) s =
      -deriv riemannZeta s / riemannZeta s ^ 2 := by
  have hregion : {z : ℂ | 1 < z.re} ∈ 𝓝 s :=
    (isOpen_lt continuous_const continuous_re).mem_nhds hs
  have heq :
      (L ↗ArithmeticFunction.moebius) =ᶠ[𝓝 s]
        (riemannZeta ·)⁻¹ := by
    filter_upwards [hregion] with z hz
    exact mobius_LSeries_eq_inv_riemannZeta hz
  rw [heq.deriv_eq]
  have hs1 : s ≠ 1 := by
    intro h
    simpa [h] using hs
  exact ((differentiableAt_riemannZeta hs1).hasDerivAt.inv
    (riemannZeta_ne_zero_of_one_lt_re hs)).deriv

/--
B2: on `Re s > 1`, the Dirichlet series of `μ(n) log n` is
`ζ'(s) / ζ(s)^2`.
-/
theorem mobiusLog_LSeries_eq_zeta_deriv_div_sq {s : ℂ} (hs : 1 < s.re) :
    L mobiusLogCoeffC s = deriv riemannZeta s / riemannZeta s ^ 2 := by
  have habs : LSeries.abscissaOfAbsConv (↗ArithmeticFunction.moebius : ℕ → ℂ) < s.re := by
    rw [ArithmeticFunction.abscissaOfAbsConv_moebius, ← EReal.coe_one,
      EReal.coe_lt_coe_iff]
    exact hs
  have hLderiv := LSeries_deriv habs
  have hzderiv := deriv_mobius_LSeries_eq_neg_zeta_deriv_div_sq hs
  have hneg :
      -L (LSeries.logMul (↗ArithmeticFunction.moebius : ℕ → ℂ)) s =
        -(deriv riemannZeta s / riemannZeta s ^ 2) := by
    calc
      -L (LSeries.logMul (↗ArithmeticFunction.moebius : ℕ → ℂ)) s =
          deriv (L ↗ArithmeticFunction.moebius) s := hLderiv.symm
      _ = -deriv riemannZeta s / riemannZeta s ^ 2 := hzderiv
      _ = -(deriv riemannZeta s / riemannZeta s ^ 2) := by ring
  calc
    L mobiusLogCoeffC s =
        L (LSeries.logMul (↗ArithmeticFunction.moebius : ℕ → ℂ)) s := by
      apply LSeries_congr
      intro n _hn
      simp [mobiusLogCoeffC, LSeries.logMul, ← Complex.natCast_log]
    _ = deriv riemannZeta s / riemannZeta s ^ 2 := neg_inj.mp hneg

end MobiusLogLSeries

-- ---------------------------------------------------------------------------
-- H14 final field, B3. A Dirichlet--Abelian boundary theorem
-- ---------------------------------------------------------------------------

open scoped LSeries.notation

/-- The real boundary coefficient `mu(n) log(n) / n`. -/
noncomputable def mobiusLogBoundaryTerm (n : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℝ) * Real.log (n : ℝ) / (n : ℝ)

@[simp]
lemma mobiusLogBoundaryTerm_zero : mobiusLogBoundaryTerm 0 = 0 := by
  simp [mobiusLogBoundaryTerm]

lemma sum_range_succ_eq_sum_Icc_one_of_zero
    (a : ℕ → ℝ) (ha0 : a 0 = 0) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), a n) = ∑ n ∈ Finset.Icc 1 N, a n := by
  induction N with
  | zero => simp [ha0]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      rw [Finset.sum_Icc_succ_top (by omega)]

lemma mobiusLogBoundaryTerm_partial_sum (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, mobiusLogBoundaryTerm n) =
      mobiusLogOverKPartial N := by
  rfl

/--
For a positive displacement `d`, taking real parts in the absolutely
convergent logarithmic Möbius L-series gives the real weighted boundary
series.
-/
lemma mobiusLog_LSeries_hasSum_boundary_weighted (d : ℝ) (hd : 0 < d) :
    HasSum (fun n : ℕ => mobiusLogBoundaryTerm n * (n : ℝ) ^ (-d))
      (L mobiusLogCoeffC (((1 + d : ℝ) : ℂ))).re := by
  have habs :
      LSeries.abscissaOfAbsConv
          (↗ArithmeticFunction.moebius : ℕ → ℂ) <
        (((1 + d : ℝ) : ℂ)).re := by
    rw [ArithmeticFunction.abscissaOfAbsConv_moebius, ← EReal.coe_one,
      EReal.coe_lt_coe_iff]
    simpa using hd
  have hcomplex :=
    (LSeriesSummable_logMul_of_lt_re habs).LSeriesHasSum
  have hseries_eq :
      L (LSeries.logMul (↗ArithmeticFunction.moebius : ℕ → ℂ))
          (((1 + d : ℝ) : ℂ)) =
        L mobiusLogCoeffC (((1 + d : ℝ) : ℂ)) := by
    symm
    apply LSeries_congr
    intro n _hn
    simp [mobiusLogCoeffC, LSeries.logMul, ← Complex.natCast_log]
  rw [← hseries_eq]
  have hreal := Complex.hasSum_re hcomplex
  refine hreal.congr_fun (fun n => ?_)
  symm
  by_cases hn : n = 0
  · subst n
    simp [mobiusLogBoundaryTerm, LSeries.term]
  · rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg]
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hpow := deLaValleePoussin_real_cpow_neg_re
      (x := (n : ℝ)) (σ := 1 + d) (t := 0) hnpos
    have hpow' :
        ((n : ℂ) ^ (-(((1 + d : ℝ) : ℂ) + Complex.I * (0 : ℝ)))).re =
          (n : ℝ) ^ (-(1 + d)) * Real.cos (0 * Real.log (n : ℝ)) := by
      simpa using hpow
    change
      ((Complex.log (n : ℂ) * ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
          (n : ℂ) ^ (-((1 + d : ℝ) : ℂ))).re) = _
    rw [← Complex.natCast_log]
    have hcoeff :
        (Real.log (n : ℝ) : ℂ) * ((ArithmeticFunction.moebius n : ℤ) : ℂ) =
          ((Real.log (n : ℝ) *
            ((ArithmeticFunction.moebius n : ℤ) : ℝ) : ℝ) : ℂ) := by
      push_cast
      ring
    calc
      (((Real.log (n : ℝ) : ℂ) * ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
          (n : ℂ) ^ (-((1 + d : ℝ) : ℂ))).re) =
          Real.log (n : ℝ) * ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
            (n : ℝ) ^ (-(1 + d)) := by
              rw [hcoeff]
              rw [show (-((1 + d : ℝ) : ℂ)) =
                (-(((1 + d : ℝ) : ℂ) + Complex.I * (0 : ℝ))) by simp]
              simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
                sub_zero]
              rw [hpow']
              norm_num
      _ = mobiusLogBoundaryTerm n * (n : ℝ) ^ (-d) := by
        rw [show -(1 + d) = (-1 : ℝ) + (-d) by ring,
          Real.rpow_add hnpos, Real.rpow_neg_one]
        simp [mobiusLogBoundaryTerm, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/--
Finite tail estimate underlying the Dirichlet--Abelian boundary theorem.
It is a direct application of the finite Abel inequality already used in the
quantitative Axer argument.
-/
lemma abs_sum_Icc_rpow_neg_le_of_partial_limit
    (a : ℕ → ℝ) {ℓ ε : ℝ} (K B : ℕ) (d : ℝ)
    (hε : 0 ≤ ε) (hd : 0 < d) (hKB : K + 1 ≤ B)
    (htail : ∀ n : ℕ, K ≤ n →
      |(∑ j ∈ Finset.Icc 1 n, a j) - ℓ| ≤ ε) :
    |∑ n ∈ Finset.Icc (K + 1) B, a n * (n : ℝ) ^ (-d)| ≤ 2 * ε := by
  apply abs_sum_Icc_mul_le_of_partial_sum_le_of_antitone
    a (fun n : ℕ => (n : ℝ) ^ (-d)) (K + 1) B (2 * ε) hKB (by positivity)
  · intro n hn
    exact Real.rpow_nonneg (by positivity) _
  · intro n hn
    have hnrange := Finset.mem_Icc.mp hn
    exact Real.rpow_le_rpow_of_nonpos
      (by exact_mod_cast (show 0 < n by omega)) (by norm_cast; omega) (by linarith)
  · exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_cast; omega) (by linarith)
  · intro n hn
    have hnrange := Finset.mem_Icc.mp hn
    rw [← sum_Icc_one_sub_sum_Icc_one a K n (by omega)]
    calc
      |(∑ j ∈ Finset.Icc 1 n, a j) - ∑ j ∈ Finset.Icc 1 K, a j| =
          |((∑ j ∈ Finset.Icc 1 n, a j) - ℓ) -
            ((∑ j ∈ Finset.Icc 1 K, a j) - ℓ)| := by ring_nf
      _ ≤ |(∑ j ∈ Finset.Icc 1 n, a j) - ℓ| +
          |(∑ j ∈ Finset.Icc 1 K, a j) - ℓ| := abs_sub _ _
      _ ≤ 2 * ε := by
        have hnK : K ≤ n := by omega
        linarith [htail n hnK, htail K le_rfl]

/-- Passing the finite Abel tail estimate to an absolutely convergent series. -/
lemma abs_dirichlet_series_sub_head_le_of_partial_limit
    (a : ℕ → ℝ) (F : ℝ) {ℓ ε : ℝ} (K : ℕ) (d : ℝ)
    (ha0 : a 0 = 0) (hε : 0 ≤ ε) (hd : 0 < d)
    (htail : ∀ n : ℕ, K ≤ n →
      |(∑ j ∈ Finset.Icc 1 n, a j) - ℓ| ≤ ε)
    (hsum : HasSum (fun n : ℕ => a n * (n : ℝ) ^ (-d)) F) :
    |F - ∑ n ∈ Finset.Icc 1 K, a n * (n : ℝ) ^ (-d)| ≤ 2 * ε := by
  let f : ℕ → ℝ := fun n => a n * (n : ℝ) ^ (-d)
  have hf0 : f 0 = 0 := by simp [f, ha0]
  have hrange := hsum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  have hpartial :
      Tendsto (fun B : ℕ => ∑ n ∈ Finset.Icc 1 B, f n) atTop (𝓝 F) := by
    convert hrange using 1
    ext B
    exact (sum_range_succ_eq_sum_Icc_one_of_zero f hf0 B).symm
  have htail_tendsto :
      Tendsto (fun B : ℕ => ∑ n ∈ Finset.Icc (K + 1) B, f n) atTop
        (𝓝 (F - ∑ n ∈ Finset.Icc 1 K, f n)) := by
    have hsub := hpartial.sub_const (∑ n ∈ Finset.Icc 1 K, f n)
    apply hsub.congr'
    filter_upwards [eventually_ge_atTop K] with B hKB
    exact sum_Icc_one_sub_sum_Icc_one f K B hKB
  have habs_tendsto := htail_tendsto.abs
  apply le_of_tendsto habs_tendsto
  filter_upwards [eventually_ge_atTop (K + 1)] with B hKB
  simpa [f] using
    abs_sum_Icc_rpow_neg_le_of_partial_limit a K B d hε hd hKB htail

/--
A real Dirichlet--Abelian boundary theorem in the exact form needed here.
Ordered convergence of the boundary partial sums, together with absolute
convergence at every positive displacement, implies convergence back to the
boundary from the right.
-/
theorem dirichlet_abelian_tendsto_of_partial_sum_tendsto
    (a : ℕ → ℝ) (F : ℝ → ℝ) {ℓ : ℝ} (ha0 : a 0 = 0)
    (hpartial : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, a n) atTop (𝓝 ℓ))
    (hsum : ∀ d : ℝ, 0 < d →
      HasSum (fun n : ℕ => a n * (n : ℝ) ^ (-d)) (F d)) :
    Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 ℓ) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hη : 0 < ε / 8 := by positivity
  rw [Metric.tendsto_atTop] at hpartial
  obtain ⟨K, hK⟩ := hpartial (ε / 8) hη
  have htail : ∀ n : ℕ, K ≤ n →
      |(∑ j ∈ Finset.Icc 1 n, a j) - ℓ| ≤ ε / 8 := by
    intro n hn
    have hdist := hK n hn
    rw [Real.dist_eq] at hdist
    exact hdist.le
  have hhead :
      Tendsto (fun d : ℝ =>
        ∑ n ∈ Finset.Icc 1 K, a n * (n : ℝ) ^ (-d))
        (𝓝[>] (0 : ℝ)) (𝓝 (∑ n ∈ Finset.Icc 1 K, a n)) := by
    simpa using tendsto_finset_sum (Finset.Icc 1 K) (fun n hn => by
      have hnpos : 0 < (n : ℝ) := by
        exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hrpow :
          Tendsto (fun d : ℝ => (n : ℝ) ^ (-d)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
        have hneg : Tendsto (fun d : ℝ => -d) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
          simpa using (continuousAt_neg : ContinuousAt (fun d : ℝ => -d) 0).tendsto
        have hbase :=
          (Real.continuousAt_const_rpow (a := (n : ℝ)) (b := (0 : ℝ)) hnpos.ne').tendsto
        have hfull : Tendsto (fun d : ℝ => (n : ℝ) ^ (-d)) (𝓝 (0 : ℝ)) (𝓝 1) := by
          simpa using hbase.comp hneg
        exact tendsto_nhdsWithin_of_tendsto_nhds hfull
      simpa using (tendsto_const_nhds.mul hrpow :
        Tendsto (fun d : ℝ => a n * (n : ℝ) ^ (-d))
          (𝓝[>] (0 : ℝ)) (𝓝 (a n * 1))))
  have hhead_eventually := (Metric.tendsto_nhds.mp hhead) (ε / 2) (by positivity)
  filter_upwards [hhead_eventually, self_mem_nhdsWithin] with d hhead_d hdmem
  have hd : 0 < d := hdmem
  have hseries_tail := abs_dirichlet_series_sub_head_le_of_partial_limit
    a (F d) K d ha0 hη.le hd htail (hsum d hd)
  rw [Real.dist_eq] at hhead_d ⊢
  calc
    |F d - ℓ| ≤
        |F d - ∑ n ∈ Finset.Icc 1 K, a n * (n : ℝ) ^ (-d)| +
          |(∑ n ∈ Finset.Icc 1 K, a n * (n : ℝ) ^ (-d)) -
            ∑ n ∈ Finset.Icc 1 K, a n| +
          |(∑ n ∈ Finset.Icc 1 K, a n) - ℓ| := by
      calc
        |F d - ℓ| =
            |(F d - ∑ n ∈ Finset.Icc 1 K, a n * (n : ℝ) ^ (-d)) +
              ((∑ n ∈ Finset.Icc 1 K, a n * (n : ℝ) ^ (-d)) -
                ∑ n ∈ Finset.Icc 1 K, a n) +
              ((∑ n ∈ Finset.Icc 1 K, a n) - ℓ)| := by ring_nf
        _ ≤ _ := (abs_add_three _ _ _)
    _ < ε := by linarith [hseries_tail, hhead_d, htail K le_rfl]

/-- B3: the logarithmic Möbius L-series tends to its ordered boundary sum. -/
theorem mobiusLog_LSeries_tendsto_boundary
    {ℓ : ℝ} (hℓ : Tendsto mobiusLogOverKPartial atTop (𝓝 ℓ)) :
    Tendsto (fun s : ℝ => (L mobiusLogCoeffC (s : ℂ)).re)
      (𝓝[>] (1 : ℝ)) (𝓝 ℓ) := by
  have habelian := dirichlet_abelian_tendsto_of_partial_sum_tendsto
    mobiusLogBoundaryTerm
    (fun d : ℝ => (L mobiusLogCoeffC (((1 + d : ℝ) : ℂ))).re)
    mobiusLogBoundaryTerm_zero
    (by simpa [mobiusLogBoundaryTerm_partial_sum] using hℓ)
    mobiusLog_LSeries_hasSum_boundary_weighted
  have hshift : Tendsto (fun s : ℝ => s - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [nhdsWithin]
    apply tendsto_inf.2
    constructor
    · exact tendsto_nhdsWithin_of_tendsto_nhds (by
        have hid : Tendsto (fun s : ℝ => s) (𝓝 (1 : ℝ)) (𝓝 (1 : ℝ)) := tendsto_id
        simpa using hid.sub_const (1 : ℝ))
    · rw [tendsto_principal]
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact show 0 < s - 1 from sub_pos.mpr hs
  apply (habelian.comp hshift).congr'
  filter_upwards [] with s
  simp only [Function.comp_apply]
  rw [show (1 + (s - 1) : ℝ) = s by ring]

-- ---------------------------------------------------------------------------
-- H14 final field, B4. The zeta-pole normalization
-- ---------------------------------------------------------------------------

/-- The simple pole of `ζ` at `1`, removed by multiplication and update. -/
noncomputable def zetaPoleRemoved (s : ℂ) : ℂ :=
  Function.update (fun z : ℂ => (z - 1) * riemannZeta z) 1 1 s

@[simp]
lemma zetaPoleRemoved_one : zetaPoleRemoved 1 = 1 := by
  simp [zetaPoleRemoved]

lemma zetaPoleRemoved_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    zetaPoleRemoved s = (s - 1) * riemannZeta s := by
  simp [zetaPoleRemoved, Function.update_of_ne hs]

/-- The pole-removed zeta function is analytic at the former pole. -/
lemma zetaPoleRemoved_analyticAt_one : AnalyticAt ℂ zetaPoleRemoved 1 := by
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hprod : DifferentiableAt ℂ (fun z : ℂ => (z - 1) * riemannZeta z) s :=
      (differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hs)
    apply hprod.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hs] with z hz
    exact zetaPoleRemoved_of_ne_one hz
  · change ContinuousAt
      (Function.update (fun z : ℂ => (z - 1) * riemannZeta z) 1 1) 1
    simpa only [continuousAt_update_same] using
      deLaValleePoussin_zeta_residue_one

/-- Derivative formula for the pole-removed zeta function away from `1`. -/
lemma deriv_zetaPoleRemoved_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    deriv zetaPoleRemoved s =
      riemannZeta s + (s - 1) * deriv riemannZeta s := by
  have heq : zetaPoleRemoved =ᶠ[𝓝 s]
      (fun z : ℂ => (z - 1) * riemannZeta z) := by
    filter_upwards [eventually_ne_nhds hs] with z hz
    exact zetaPoleRemoved_of_ne_one hz
  rw [heq.deriv_eq]
  convert ((hasDerivAt_id s).sub_const 1).mul
    (differentiableAt_riemannZeta hs).hasDerivAt |>.deriv using 1 <;>
      simp only [id_eq] <;> ring

/-- Algebraic form of `ζ'/ζ²` after removal of the simple pole. -/
lemma zeta_deriv_div_sq_eq_poleRemoved {s : ℂ} (hs : s ≠ 1)
    (hz : riemannZeta s ≠ 0) :
    deriv riemannZeta s / riemannZeta s ^ 2 =
      ((s - 1) * deriv zetaPoleRemoved s - zetaPoleRemoved s) /
        zetaPoleRemoved s ^ 2 := by
  rw [zetaPoleRemoved_of_ne_one hs, deriv_zetaPoleRemoved_of_ne_one hs]
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  field_simp [hsub, hz]
  ring

/-- B4: the pole of `ζ` anchors `ζ'(s)/ζ(s)^2` at `-1`. -/
theorem zeta_deriv_div_sq_tendsto_neg_one :
    Tendsto (fun s : ℝ =>
      (deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ) ^ 2).re)
      (𝓝[>] (1 : ℝ)) (𝓝 (-1 : ℝ)) := by
  have hcoe : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
  have hG : Tendsto (fun s : ℝ => zetaPoleRemoved (s : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    by simpa only [Function.comp_apply, zetaPoleRemoved_one] using
      zetaPoleRemoved_analyticAt_one.continuousAt.tendsto.comp hcoe
  have hG' : Tendsto (fun s : ℝ => deriv zetaPoleRemoved (s : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (deriv zetaPoleRemoved 1)) :=
    zetaPoleRemoved_analyticAt_one.deriv.continuousAt.tendsto.comp hcoe
  have hsub : Tendsto (fun s : ℝ => (s : ℂ) - 1)
      (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℂ)) := by
    simpa using hcoe.sub_const (1 : ℂ)
  have hexpr : Tendsto (fun s : ℝ =>
      (((s : ℂ) - 1) * deriv zetaPoleRemoved (s : ℂ) -
        zetaPoleRemoved (s : ℂ)) / zetaPoleRemoved (s : ℂ) ^ 2)
      (𝓝[>] (1 : ℝ)) (𝓝 (-1 : ℂ)) := by
    convert ((hsub.mul hG').sub hG).div (hG.pow 2) (by norm_num) using 1 <;> simp
  have hre : Tendsto (fun s : ℝ =>
      ((((s : ℂ) - 1) * deriv zetaPoleRemoved (s : ℂ) -
        zetaPoleRemoved (s : ℂ)) / zetaPoleRemoved (s : ℂ) ^ 2).re)
      (𝓝[>] (1 : ℝ)) (𝓝 (-1 : ℝ)) := by
    simpa using Complex.continuous_re.tendsto (-1) |>.comp hexpr
  apply hre.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : (s : ℂ) ≠ 1 := by
    exact_mod_cast ne_of_gt hs
  have hz : riemannZeta (s : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simpa using hs)
  exact congrArg Complex.re (zeta_deriv_div_sq_eq_poleRemoved hs1 hz).symm

-- ---------------------------------------------------------------------------
-- H14 final field, B5. Collapse to the single classical decay input
-- ---------------------------------------------------------------------------

/--
B5: the logarithmic Möbius boundary value is forced to be `-1` by its
Dirichlet series and the simple pole of `ζ`.
-/
theorem mobiusLog_sum_neg_one_of_decay (H : ClassicalMertensDecay) :
    Tendsto mobiusLogOverKPartial atTop (𝓝 (-1)) := by
  rcases mobiusLogOverKPartial_convergent_of_decay H with ⟨ℓ, hℓ⟩
  have hboundary := mobiusLog_LSeries_tendsto_boundary hℓ
  have hzeta := zeta_deriv_div_sq_tendsto_neg_one
  have hLseries : Tendsto (fun s : ℝ => (L mobiusLogCoeffC (s : ℂ)).re)
      (𝓝[>] (1 : ℝ)) (𝓝 (-1 : ℝ)) := by
    apply hzeta.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact congrArg Complex.re
      (mobiusLog_LSeries_eq_zeta_deriv_div_sq (by simpa using hs)).symm
  have hℓeq : ℓ = -1 := tendsto_nhds_unique hboundary hLseries
  simpa [hℓeq] using hℓ

/--
Final H14 constructor: the whole classical linear Möbius API follows from the
single de la Vallée Poussin decay statement.
-/
noncomputable def ClassicalMertensAPI.ofDecayOnly
    (H : ClassicalMertensDecay) : ClassicalMertensAPI :=
  { C_M := Classical.choose (mertens_bound_of_decay H)
    C_L := Classical.choose (mobiusLogSummatory_bound_of_decay H)
    C_M_pos := (Classical.choose_spec (mertens_bound_of_decay H)).1
    C_L_pos := (Classical.choose_spec (mobiusLogSummatory_bound_of_decay H)).1
    mertens_bound := (Classical.choose_spec (mertens_bound_of_decay H)).2
    mobiusLogSummatory_bound :=
      (Classical.choose_spec (mobiusLogSummatory_bound_of_decay H)).2
    mobius_sum_zero := mobiusOverK_tendsto_zero_of_decay H
    mobiusLog_sum_neg_one := mobiusLog_sum_neg_one_of_decay H }





end RH.Criteria.NymanBeurling.MobiusSummatory
