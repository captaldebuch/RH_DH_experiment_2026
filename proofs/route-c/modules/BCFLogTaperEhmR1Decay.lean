import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmSeriesBridge
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Quadratic decay of Ehm's elementary `R₁` function

This file proves the elementary analytic input left open in the Ehm series
bridge: the floor-corrected harmonic remainder `ehmR1` is `O(x⁻²)` on the
positive half-line.  The proof uses explicit upper and lower bounds for the
Euler--Mascheroni remainder and keeps a deliberately generous constant.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmR1Decay

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmSeriesBridge

/-- The trapezoid upper bound for `log (1 + u)`. -/
private theorem log_one_add_le_trapezoid {u : ℝ} (hu : 0 ≤ u) :
    Real.log (1 + u) ≤ u * (u + 2) / (2 * (u + 1)) := by
  let t := u / (u + 2)
  have hu2 : 0 < u + 2 := by linarith
  have ht0 : 0 ≤ t := div_nonneg hu hu2.le
  have ht1 : t < 1 := by
    dsimp [t]
    exact (div_lt_one hu2).2 (by linarith)
  have h := Real.log_div_le_sum_range_add ht0 ht1 1
  have hratio : (1 + t) / (1 - t) = 1 + u := by
    dsimp [t]
    field_simp
    ring
  rw [hratio] at h
  simp only [Finset.sum_range_one, pow_one, Nat.cast_one, div_one] at h
  have hden : 0 < 1 - t ^ 2 := by
    have htt : t * t < 1 := by nlinarith
    simpa [pow_two] using sub_pos.mpr htt
  calc
    Real.log (1 + u) ≤ 2 * (t + t ^ 3 / (1 - t ^ 2)) := by linarith
    _ = u * (u + 2) / (2 * (u + 1)) := by
      have hu1 : 0 < u + 1 := by linarith
      have hsq : 1 - t ^ 2 = 4 * (u + 1) / (u + 2) ^ 2 := by
        dsimp [t]
        field_simp [ne_of_gt hu2]
        <;> ring
      rw [hsq]
      dsimp [t]
      field_simp [ne_of_gt hu2, ne_of_gt hu1]
      <;> ring

/-- A second-order lower bound, in a form convenient for the harmonic
remainder. -/
private theorem log_one_add_lower_midpoint {u : ℝ} (hu : 0 ≤ u) :
    2 * u / (u + 2) ≤ Real.log (1 + u) := by
  exact Real.le_log_one_add_of_nonneg hu

/-- The lower Euler--Mascheroni approximants.  Indexing by `n + 1` avoids
all artificial values at zero. -/
private noncomputable def lowerGammaSeq (n : ℕ) : ℝ :=
  (harmonic (n + 1) : ℝ) - Real.log (n + 1 : ℝ) -
    1 / (2 * (n + 1 : ℝ))

/-- The midpoint upper Euler--Mascheroni approximants. -/
private noncomputable def upperGammaSeq (n : ℕ) : ℝ :=
  (harmonic (n + 1) : ℝ) - Real.log ((n + 1 : ℝ) + 1 / 2)

private theorem monotone_lowerGammaSeq : Monotone lowerGammaSeq := by
  refine monotone_nat_of_le_succ (fun n ↦ ?_)
  have hm : (0 : ℝ) < n + 1 := by positivity
  have hlog := log_one_add_le_trapezoid (u := 1 / (n + 1 : ℝ)) (by positivity)
  have hlog' :
      Real.log (((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) ≤
        (2 * (n + 1 : ℝ) + 1) /
          (2 * (n + 1 : ℝ) * (n + 2 : ℝ)) := by
    rw [show (((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) =
      1 + 1 / (n + 1 : ℝ) by
        norm_num [Nat.cast_add, Nat.cast_one]
        field_simp
        <;> ring]
    calc
      Real.log (1 + 1 / (n + 1 : ℝ)) ≤
          (1 / (n + 1 : ℝ)) * (1 / (n + 1 : ℝ) + 2) /
            (2 * (1 / (n + 1 : ℝ) + 1)) := hlog
      _ = _ := by
        norm_num [Nat.cast_add, Nat.cast_one]
        field_simp
        <;> ring
  have hh : (harmonic (n + 2) : ℝ) =
      (harmonic (n + 1) : ℝ) + 1 / (n + 2 : ℝ) := by
    rw [show n + 2 = (n + 1) + 1 by omega, harmonic_succ]
    push_cast
    ring
  have hdiff : lowerGammaSeq (n + 1) - lowerGammaSeq n =
      (1 / (↑n + 2 : ℝ) - 1 / (2 * (↑n + 2 : ℝ)) +
        1 / (2 * (↑n + 1 : ℝ))) -
          (Real.log (↑n + 2) - Real.log (↑n + 1)) := by
    simp only [lowerGammaSeq]
    rw [show n + 1 + 1 = n + 2 by omega, hh]
    push_cast
    ring
  rw [← sub_nonneg, hdiff]
  norm_num [Nat.cast_add, Nat.cast_one] at hlog'
  rw [Real.log_div (by positivity) (by positivity)] at hlog'
  have hdenpos : 0 < 2 * (↑n + 1) * (↑n + 2 : ℝ) := by positivity
  have halg :
      1 / (↑n + 2 : ℝ) - 1 / (2 * (↑n + 2 : ℝ)) +
          1 / (2 * (↑n + 1 : ℝ)) =
        (2 * (↑n + 1 : ℝ) + 1) /
          (2 * (↑n + 1 : ℝ) * (↑n + 2 : ℝ)) := by
    field_simp
    <;> ring
  rw [halg]
  linarith

private theorem antitone_upperGammaSeq : Antitone upperGammaSeq := by
  refine antitone_nat_of_succ_le (fun n ↦ ?_)
  have hu : 0 ≤ 1 / ((n + 1 : ℝ) + 1 / 2) := by positivity
  have hlog := log_one_add_lower_midpoint hu
  have hlog' :
      1 / (n + 2 : ℝ) ≤
        Real.log (((n + 2 : ℝ) + 1 / 2) /
          ((n + 1 : ℝ) + 1 / 2)) := by
    rw [show (((n + 2 : ℝ) + 1 / 2) /
        ((n + 1 : ℝ) + 1 / 2)) =
      1 + 1 / ((n + 1 : ℝ) + 1 / 2) by
        norm_num [Nat.cast_add, Nat.cast_one]
        field_simp
        <;> ring]
    calc
      1 / (n + 2 : ℝ) =
          2 * (1 / ((n + 1 : ℝ) + 1 / 2)) /
            (1 / ((n + 1 : ℝ) + 1 / 2) + 2) := by
              norm_num [Nat.cast_add, Nat.cast_one]
              field_simp
              <;> ring
      _ ≤ _ := hlog
  have hh : (harmonic (n + 2) : ℝ) =
      (harmonic (n + 1) : ℝ) + 1 / (n + 2 : ℝ) := by
    rw [show n + 2 = (n + 1) + 1 by omega, harmonic_succ]
    push_cast
    ring
  have hdiff : upperGammaSeq n - upperGammaSeq (n + 1) =
      (Real.log ((↑n + 2 : ℝ) + 1 / 2) -
        Real.log ((↑n + 1 : ℝ) + 1 / 2)) - 1 / (↑n + 2 : ℝ) := by
    simp only [upperGammaSeq]
    rw [show n + 1 + 1 = n + 2 by omega, hh]
    push_cast
    ring
  rw [← sub_nonneg, hdiff]
  norm_num [Nat.cast_add, Nat.cast_one] at hlog'
  rw [Real.log_div (by positivity) (by positivity)] at hlog'
  exact sub_nonneg.mpr (by simpa [one_div] using hlog')

private theorem lowerGammaSeq_tendsto :
    Tendsto lowerGammaSeq atTop (nhds Real.eulerMascheroniConstant) := by
  have hmain := Real.tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)
  have hsmall : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (2 * (n + 1 : ℝ)))
      atTop (nhds 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 2 : ℝ)
    convert h using 1
    · funext n
      rw [one_div, mul_inv_rev]
      ring
    · ring
  convert hmain.sub hsmall using 1
  · funext n
    simp only [lowerGammaSeq, Function.comp_apply, Nat.cast_add, Nat.cast_one]
  · ring

private theorem upperGammaSeq_tendsto :
    Tendsto upperGammaSeq atTop (nhds Real.eulerMascheroniConstant) := by
  have hmain := Real.tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)
  have hdiff : Tendsto
      (fun n : ℕ ↦ Real.log (n + 1 : ℝ) -
        Real.log ((n + 1 : ℝ) + 1 / 2)) atTop (nhds 0) := by
    have hden : Tendsto (fun n : ℕ ↦ (n : ℝ) + 3 / 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop (3 / 2 : ℝ) tendsto_natCast_atTop_atTop
    have hsmall : Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) / ((n : ℝ) + 3 / 2))
        atTop (nhds 0) := tendsto_const_nhds.div_atTop hden
    have hsub : Tendsto (fun n : ℕ ↦
        (1 : ℝ) - (1 / 2 : ℝ) / ((n : ℝ) + 3 / 2)) atTop (nhds 1) := by
      simpa using tendsto_const_nhds.sub hsmall
    have hfun : (fun n : ℕ ↦
        (n + 1 : ℝ) / ((n + 1 : ℝ) + 1 / 2)) =
        (fun n : ℕ ↦ (1 : ℝ) - (1 / 2 : ℝ) / ((n : ℝ) + 3 / 2)) := by
      funext n
      norm_num [Nat.cast_add, Nat.cast_one]
      field_simp
      ring
    have hratio : Tendsto (fun n : ℕ ↦
        (n + 1 : ℝ) / ((n + 1 : ℝ) + 1 / 2)) atTop (nhds 1) := by
      rw [hfun]
      exact hsub
    have hcomp :=
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
    convert hcomp using 1
    · funext n
      rw [Function.comp_apply, Real.log_div (by positivity) (by positivity)]
    · simp
  convert hmain.add hdiff using 1
  · funext n
    simp only [upperGammaSeq, Function.comp_apply, Nat.cast_add, Nat.cast_one]
    ring
  · ring

/-- Explicit two-sided control of the Euler--Mascheroni remainder. -/
theorem harmonic_log_remainder_bounds (n : ℕ) (hn : 0 < n) :
    Real.log (1 + 1 / (2 * (n : ℝ))) ≤
        (harmonic n : ℝ) - Real.log (n : ℝ) - Real.eulerMascheroniConstant ∧
      (harmonic n : ℝ) - Real.log (n : ℝ) - Real.eulerMascheroniConstant ≤
        1 / (2 * (n : ℝ)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hlower : lowerGammaSeq m ≤ Real.eulerMascheroniConstant :=
    monotone_lowerGammaSeq.ge_of_tendsto lowerGammaSeq_tendsto m
  have hupper : Real.eulerMascheroniConstant ≤ upperGammaSeq m :=
    antitone_upperGammaSeq.le_of_tendsto upperGammaSeq_tendsto m
  constructor
  · unfold upperGammaSeq at hupper
    norm_num [upperGammaSeq, Nat.cast_add, Nat.cast_one] at hupper ⊢
    rw [show (m : ℝ) + 1 + 1 / 2 =
      ((m : ℝ) + 1) * (1 + 1 / (2 * ((m : ℝ) + 1))) by field_simp <;> ring,
      Real.log_mul (by positivity) (by positivity)] at hupper
    have hone : 1 / (2 * ((m : ℝ) + 1)) =
        ((m : ℝ) + 1)⁻¹ * (1 / 2) := by field_simp <;> ring
    rw [hone] at hupper
    linarith
  · unfold lowerGammaSeq at hlower
    norm_num [Nat.cast_add, Nat.cast_one] at hlower ⊢
    linarith

/-- Ehm's finite harmonic sum is the ordinary harmonic number at the
natural floor. -/
theorem ehmHarmonic_eq_harmonic_floor (x : ℝ) :
    ehmHarmonic x = (harmonic ⌊x⌋₊ : ℝ) := by
  unfold ehmHarmonic
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]

private theorem ehmR1_of_pos_lt_one {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    ehmR1 x = Real.log x + Real.eulerMascheroniConstant - 1 + 1 / (2 * x) := by
  have hfloor : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr hx1
  have hfract : Int.fract x = x := Int.fract_eq_self.mpr ⟨hx.le, hx1⟩
  unfold ehmR1 ehmHarmonic
  rw [hfloor, hfract]
  simp only [Finset.Icc_eq_empty_of_lt (by omega : (0 : ℕ) < 1), Finset.sum_empty,
    sub_zero]
  field_simp [ne_of_gt hx]
  ring

private theorem ehmR1_small_bound {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    |ehmR1 x| ≤ 8 / x ^ 2 := by
  have hlog_nonpos : Real.log x ≤ 0 := Real.log_nonpos hx.le hx1.le
  have hlog_lower : 1 - x⁻¹ ≤ Real.log x := Real.one_sub_inv_le_log_of_pos hx
  have hlogabs : |Real.log x| ≤ 1 / x := by
    rw [abs_of_nonpos hlog_nonpos]
    have : -Real.log x ≤ x⁻¹ - 1 := by linarith
    have hinv : 0 ≤ x⁻¹ := inv_nonneg.mpr hx.le
    simpa [one_div] using this.trans (by linarith : x⁻¹ - 1 ≤ x⁻¹)
  have hgamma : |Real.eulerMascheroniConstant - 1| ≤ 1 := by
    rw [abs_le]
    constructor
    · linarith [Real.one_half_lt_eulerMascheroniConstant]
    · linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  have hinvabs : |1 / (2 * x)| = 1 / (2 * x) :=
    abs_of_nonneg (by positivity)
  have htri :
      |Real.log x + Real.eulerMascheroniConstant - 1 + 1 / (2 * x)| ≤
        |Real.log x| + |Real.eulerMascheroniConstant - 1| + |1 / (2 * x)| := by
    convert abs_add_three (Real.log x) (Real.eulerMascheroniConstant - 1)
      (1 / (2 * x)) using 1 <;> ring
  have hinv_le_sq : 1 / x ≤ 1 / x ^ 2 := by
    have hxx : x ^ 2 ≤ x := by nlinarith
    exact one_div_le_one_div_of_le (sq_pos_of_pos hx) hxx
  rw [ehmR1_of_pos_lt_one hx hx1]
  calc
    _ ≤ |Real.log x| + |Real.eulerMascheroniConstant - 1| + |1 / (2 * x)| := htri
    _ ≤ 1 / x + 1 + 1 / (2 * x) := by
      rw [hinvabs]
      gcongr
    _ ≤ 3 * (1 / x ^ 2) := by
      have hone : 1 ≤ 1 / x ^ 2 := by
        have : x ^ 2 ≤ 1 := by nlinarith
        exact (le_div_iff₀ (sq_pos_of_pos hx)).2 (by simpa using this)
      have hhalf : 1 / (2 * x) ≤ 1 / x := by
        have hx0 : x ≠ 0 := ne_of_gt hx
        field_simp [hx0]
        linarith
      linarith
    _ ≤ 8 / x ^ 2 := by
      have : 0 ≤ 1 / x ^ 2 := by positivity
      simpa [div_eq_mul_inv] using (mul_le_mul_of_nonneg_right (by norm_num : (3 : ℝ) ≤ 8) this)

private theorem ehmR1_large_bound {x : ℝ} (hx : 1 ≤ x) :
    |ehmR1 x| ≤ 8 / x ^ 2 := by
  let n : ℕ := ⌊x⌋₊
  let θ : ℝ := Int.fract x
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hn : 0 < n := by
    dsimp [n]
    exact Nat.floor_pos.mpr hx
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hθ0 : 0 ≤ θ := Int.fract_nonneg x
  have hθ1 : θ < 1 := Int.fract_lt_one x
  have hnx : (n : ℝ) + θ = x := by
    dsimp [n, θ]
    rw [natCast_floor_eq_intCast_floor hxpos.le, Int.floor_add_fract]
  have hnx_le : (n : ℝ) ≤ x := by linarith
  have hx_le_two_n : x ≤ 2 * (n : ℝ) := by
    have : x < (n : ℝ) + 1 := by
      dsimp [n]
      exact Nat.lt_floor_add_one x
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hH : ehmHarmonic x = (harmonic n : ℝ) := by
    simpa [n] using ehmHarmonic_eq_harmonic_floor x
  obtain ⟨hDlower, hDupper⟩ := harmonic_log_remainder_bounds n hn
  let D : ℝ := (harmonic n : ℝ) - Real.log (n : ℝ) -
    Real.eulerMascheroniConstant
  let E : ℝ := 1 / (2 * (n : ℝ)) - D
  have hE0 : 0 ≤ E := by dsimp [E, D]; linarith
  have hEupper : E ≤ 1 / (8 * (n : ℝ) ^ 2) := by
    let u : ℝ := 1 / (2 * (n : ℝ))
    have hu0 : 0 ≤ u := by positivity
    have hu_le : u ≤ 1 / 2 := by
      dsimp [u]
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * n)
        (by norm_num : (0 : ℝ) < 2)).2
      nlinarith
    have hmid := log_one_add_lower_midpoint hu0
    have hdiff : u - Real.log (1 + u) ≤ u ^ 2 / 2 := by
      calc
        u - Real.log (1 + u) ≤ u - 2 * u / (u + 2) := by linarith
        _ = u ^ 2 / (u + 2) := by field_simp; ring
        _ ≤ u ^ 2 / 2 := by
          gcongr
          linarith
    have hED : E ≤ u - Real.log (1 + u) := by
      dsimp [E, D, u] at hDlower ⊢
      linarith
    calc
      E ≤ u - Real.log (1 + u) := hED
      _ ≤ u ^ 2 / 2 := hdiff
      _ = 1 / (8 * (n : ℝ) ^ 2) := by
        dsimp [u]
        field_simp
        ring
  let v : ℝ := θ / (n : ℝ)
  have hv0 : 0 ≤ v := div_nonneg hθ0 hnreal.le
  have hv_le : v ≤ 1 / (n : ℝ) := by
    dsimp [v]
    exact div_le_div_of_nonneg_right hθ1.le hnreal.le
  have hlogv_upper : Real.log (1 + v) ≤ v := by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + v)
    linarith
  have hlogv_lower := log_one_add_lower_midpoint hv0
  have hlog_error : |Real.log (1 + v) - v| ≤ 1 / (2 * (n : ℝ) ^ 2) := by
    rw [abs_of_nonpos (sub_nonpos.mpr hlogv_upper)]
    rw [neg_sub]
    calc
      v - Real.log (1 + v) ≤ v - 2 * v / (v + 2) := by linarith
      _ = v ^ 2 / (v + 2) := by field_simp; ring
      _ ≤ v ^ 2 / 2 := by
        gcongr
        linarith
      _ ≤ (1 / (n : ℝ)) ^ 2 / 2 := by gcongr
      _ = 1 / (2 * (n : ℝ) ^ 2) := by field_simp
  let M : ℝ := v - (θ - 1 / 2) / x - 1 / (2 * (n : ℝ))
  have hMformula : M = (2 * θ - 1) * θ / (2 * (n : ℝ) * x) := by
    dsimp [M, v]
    rw [← hnx]
    field_simp
    ring
  have hlinear : |2 * θ - 1| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hM : |M| ≤ 1 / (2 * (n : ℝ) ^ 2) := by
    rw [hMformula, abs_div, abs_mul, abs_of_nonneg hθ0,
      abs_of_pos (mul_pos (mul_pos (by norm_num) hnreal) hxpos)]
    have hnum : |2 * θ - 1| * θ ≤ 1 := by nlinarith
    calc
      |2 * θ - 1| * θ / (2 * (n : ℝ) * x) ≤
          1 / (2 * (n : ℝ) * x) := by gcongr
      _ ≤ 1 / (2 * (n : ℝ) ^ 2) := by
        apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 2 * n ^ 2)
        nlinarith [hnx_le]
  have hlogx : Real.log x = Real.log (n : ℝ) + Real.log (1 + v) := by
    have hprod : (n : ℝ) * (1 + v) = x := by
      dsimp [v]
      field_simp
      linarith
    rw [← hprod, Real.log_mul (ne_of_gt hnreal) (by linarith : 1 + v ≠ 0)]
  have hdecomp : ehmR1 x = (Real.log (1 + v) - v) + M + E := by
    unfold ehmR1
    rw [hH, hlogx]
    dsimp [M, E, D, v]
    ring
  rw [hdecomp]
  calc
    |(Real.log (1 + v) - v) + M + E| ≤
        |Real.log (1 + v) - v| + |M| + |E| := abs_add_three _ _ _
    _ ≤ 1 / (2 * (n : ℝ) ^ 2) + 1 / (2 * (n : ℝ) ^ 2) +
        1 / (8 * (n : ℝ) ^ 2) := by
      rw [abs_of_nonneg hE0]
      gcongr
    _ ≤ 2 / (n : ℝ) ^ 2 := by
      have : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos hnreal
      field_simp
      linarith
    _ ≤ 8 / x ^ 2 := by
      have hsquares : x ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by nlinarith
      have hposn : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos hnreal
      have hposx : 0 < x ^ 2 := sq_pos_of_pos hxpos
      apply (div_le_div_iff₀ hposn hposx).2
      nlinarith

/-- Ehm's explicit elementary function has uniform quadratic reciprocal
decay on the positive half-line. -/
noncomputable def ehmConcreteR1QuadraticDecay : EhmConcreteR1QuadraticDecay where
  C := 8
  C_nonneg := by norm_num
  bound y hy := by
    by_cases hy1 : y < 1
    · exact ehmR1_small_bound hy hy1
    · exact ehmR1_large_bound (le_of_not_gt hy1)

end RH.Criteria.NymanBeurling.BCFLogTaperEhmR1Decay
