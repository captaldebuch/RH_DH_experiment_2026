import Mathlib
import NBMellinTools.NB17Mellin

/-!
# Riesz means of `1/ζ` via the Mellin transform

This file gives a rigorous Mellin-transform description of the first-order Riesz mean of the
Möbius function,
`R(y) = ∑_{n ≤ y} μ(n) (1 - n/y)`,
namely that for `Re s > 1`,
`∫_0^∞ R(y) y^{-s-1} dy = 1 / (s (s+1) ζ(s))`.

Equivalently `mellin R (-s) = 1 / (s (s+1) ζ(s))`.  This is the standard "Riesz mean of `1/ζ`"
identity: the Riesz mean is the inverse Mellin transform of `1/(s(s+1)ζ(s))`, so its behaviour is
governed by the analytic properties of `1/ζ` on vertical lines, in particular on the critical line.

## Main definitions

* `RieszMeanZeta.rieszKernelR` / `rieszKernel` : the first-order Riesz kernel `max (1 - x) 0`
  supported in `(0,1]`, real- and complex-valued.
* `RieszMeanZeta.rieszMean` : the first-order Riesz mean `∑_{n ≤ y} μ(n) (1 - n/y)`.

## Main statements

* `RieszMeanZeta.mellin_rieszKernel` : `mellin rieszKernel s = 1/(s(s+1))` for `Re s > 0`.
* `RieszMeanZeta.mellin_rieszMean` : `mellin rieszMean (-s) = 1/(s(s+1)ζ(s))` for `Re s > 1`.
-/

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology ArithmeticFunction.Moebius

noncomputable section

namespace RieszMeanZeta

/-! ## The first-order Riesz kernel -/

/-- The first-order Riesz kernel `x ↦ 1 - x` on `(0,1]`, extended by zero. -/
def rieszKernelR : ℝ → ℝ := (Set.Ioc (0:ℝ) 1).indicator (fun x => 1 - x)

/-- The complex-valued first-order Riesz kernel. -/
def rieszKernel : ℝ → ℂ := fun x => (rieszKernelR x : ℂ)

lemma rieszKernel_eq_indicator :
    rieszKernel = (Set.Ioc (0:ℝ) 1).indicator (fun x => 1 - (x : ℂ)) := by
  funext x
  by_cases h : x ∈ Set.Ioc (0:ℝ) 1 <;> simp [rieszKernel, rieszKernelR, h]

lemma rieszKernelR_nonneg (x : ℝ) : 0 ≤ rieszKernelR x := by
  by_cases h : x ∈ Set.Ioc (0:ℝ) 1
  · simp only [rieszKernelR, Set.indicator_of_mem h]
    linarith [h.2]
  · simp [rieszKernelR, h]

lemma rieszKernelR_le_one (x : ℝ) : rieszKernelR x ≤ 1 := by
  by_cases h : x ∈ Set.Ioc (0:ℝ) 1
  · simp only [rieszKernelR, Set.indicator_of_mem h]
    linarith [h.1]
  · simp [rieszKernelR, h]

lemma norm_rieszKernel (x : ℝ) : ‖rieszKernel x‖ = rieszKernelR x := by
  rw [rieszKernel, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (rieszKernelR_nonneg x)]

/-- The Mellin transform of the first-order Riesz kernel. -/
theorem mellin_rieszKernel {s : ℂ} (hs : 0 < s.re) : mellin rieszKernel s = 1 / (s * (s + 1)) := by
  have h1 := hasMellin_one_Ioc hs
  have h2 := hasMellin_cpow_Ioc (1 : ℂ) (s := s) (by simp; linarith)
  have hsub := hasMellin_sub h1.1 h2.1
  have heq : (fun t : ℝ => (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℂ)) t
      - (Set.Ioc (0:ℝ) 1).indicator (fun t : ℝ => (t:ℂ) ^ (1:ℂ)) t) = rieszKernel := by
    funext t
    by_cases h : t ∈ Set.Ioc (0:ℝ) 1 <;> simp [rieszKernel_eq_indicator, h]
  rw [heq] at hsub
  rw [hsub.2, h1.2, h2.2]
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have hh : s = -1 := by linear_combination h
    rw [hh] at hs; norm_num at hs
  field_simp
  ring

/-- Mellin convergence of the Riesz kernel on the right half plane. -/
theorem mellinConvergent_rieszKernel {s : ℂ} (hs : 0 < s.re) : MellinConvergent rieszKernel s := by
  have h1 := hasMellin_one_Ioc hs
  have h2 := hasMellin_cpow_Ioc (1 : ℂ) (s := s) (by simp; linarith)
  have hsub := hasMellin_sub h1.1 h2.1
  have heq : (fun t : ℝ => (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℂ)) t
      - (Set.Ioc (0:ℝ) 1).indicator (fun t : ℝ => (t:ℂ) ^ (1:ℂ)) t) = rieszKernel := by
    funext t
    by_cases h : t ∈ Set.Ioc (0:ℝ) 1 <;> simp [rieszKernel_eq_indicator, h]
  rw [heq] at hsub
  exact hsub.1

/-! ## The scaled kernel -/

/-- The Mellin transform at `-s` of the scaled kernel `y ↦ K (n / y)`. -/
theorem mellin_rieszKernel_scaled {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 < a) :
    mellin (fun y : ℝ => rieszKernel (a / y)) (-s) = (a : ℂ) ^ (-s) / (s * (s + 1)) := by
  have hfun : (fun y : ℝ => rieszKernel (a / y)) = (fun y : ℝ => rieszKernel (a * y⁻¹)) := by
    funext y; rw [div_eq_mul_inv]
  rw [hfun,
    show (fun y : ℝ => rieszKernel (a * y⁻¹))
        = (fun y : ℝ => (fun t : ℝ => rieszKernel (a * t)) y⁻¹) from rfl,
    mellin_comp_inv (fun t : ℝ => rieszKernel (a * t)) (-s), neg_neg,
    mellin_comp_mul_left rieszKernel s ha, mellin_rieszKernel hs, smul_eq_mul]
  ring

/-- Mellin convergence of the scaled kernel at `-s`. -/
theorem mellinConvergent_rieszKernel_scaled {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 < a) :
    MellinConvergent (fun y : ℝ => rieszKernel (a / y)) (-s) := by
  have h1 : (fun y : ℝ => rieszKernel (a / y))
      = (fun y : ℝ => (fun t : ℝ => rieszKernel (a * t)) (y ^ (-1:ℝ))) := by
    funext y; rw [Real.rpow_neg_one, div_eq_mul_inv]
  rw [h1, MellinConvergent.comp_rpow (f := fun t : ℝ => rieszKernel (a * t)) (a := (-1:ℝ))
    (by norm_num), show (-s) / ((-1 : ℝ) : ℂ) = s from by push_cast; ring]
  exact (MellinConvergent.comp_mul_left (f := rieszKernel) ha).mpr
    (mellinConvergent_rieszKernel hs)

/-- The `L¹` norm of the scaled kernel against `y^{-σ-1}`. -/
theorem integral_norm_rieszKernel_scaled {σ : ℝ} (hσ : 0 < σ) {a : ℝ} (ha : 0 < a) :
    ∫ y in Set.Ioi (0:ℝ), ‖(y : ℂ) ^ (-(σ:ℂ) - 1) • rieszKernel (a / y)‖
      = a ^ (-σ) / (σ * (σ + 1)) := by
  set F : ℝ → ℝ := fun y => y ^ (-σ - 1) * rieszKernelR (a / y) with hF
  have hcpow : ∀ y ∈ Set.Ioi (0:ℝ), (y : ℂ) ^ (-(σ:ℂ) - 1) = ((y ^ (-σ - 1) : ℝ) : ℂ) := by
    intro y hy
    rw [Complex.ofReal_cpow (le_of_lt hy)]
    push_cast
    ring_nf
  have hnorm : ∀ y ∈ Set.Ioi (0:ℝ), ‖(y : ℂ) ^ (-(σ:ℂ) - 1) • rieszKernel (a / y)‖ = F y := by
    intro y hy
    rw [norm_smul, hcpow y hy, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (le_of_lt hy) _), norm_rieszKernel]
  rw [setIntegral_congr_fun measurableSet_Ioi hnorm]
  have hmel : mellin (fun y : ℝ => rieszKernel (a / y)) (-(σ:ℂ))
      = ((∫ y in Set.Ioi (0:ℝ), F y : ℝ) : ℂ) := by
    rw [mellin, show ((∫ y in Set.Ioi (0:ℝ), F y : ℝ) : ℂ)
        = ∫ y in Set.Ioi (0:ℝ), ((F y : ℝ) : ℂ) from integral_ofReal.symm]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro y hy
    show (y : ℂ) ^ (-(σ:ℂ) - 1) • rieszKernel (a / y) = ((F y : ℝ) : ℂ)
    rw [hcpow y hy]
    simp only [hF, smul_eq_mul, rieszKernel]
    push_cast
    ring
  rw [mellin_rieszKernel_scaled (s := (σ:ℂ)) (by simpa using hσ) ha] at hmel
  have hval : ((a:ℂ)) ^ (-(σ:ℂ)) / ((σ:ℂ) * ((σ:ℂ) + 1))
      = ((a ^ (-σ) / (σ * (σ + 1)) : ℝ) : ℂ) := by
    have h1 : ((a ^ (-σ) : ℝ) : ℂ) = (a:ℂ) ^ (-(σ:ℂ)) := by
      rw [Complex.ofReal_cpow ha.le]; push_cast; ring_nf
    push_cast
    rw [h1]
  rw [hval] at hmel
  exact_mod_cast hmel.symm

/-! ## The Riesz mean of the Möbius function -/

/-- The first-order Riesz mean `∑_{n ≤ y} μ(n) (1 - n/y)`. -/
def rieszMean (y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (ArithmeticFunction.moebius n : ℂ) * (1 - (n : ℂ) / (y : ℂ))

/-- The Riesz mean written as a (locally finite) series against the Riesz kernel. -/
theorem rieszMean_eq_tsum {y : ℝ} (hy : 0 < y) :
    rieszMean y = ∑' n : ℕ, (ArithmeticFunction.moebius n : ℂ) * rieszKernel ((n : ℝ) / y) := by
  rw [rieszMean, tsum_eq_sum (s := Finset.Icc 1 ⌊y⌋₊) ?_]
  · refine (Finset.sum_congr rfl ?_).symm
    intro n hn
    simp only [Finset.mem_Icc] at hn
    have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn.1
    have hny : (n:ℝ) ≤ y := le_trans (by exact_mod_cast hn.2) (Nat.floor_le hy.le)
    have hmem : (n:ℝ)/y ∈ Set.Ioc (0:ℝ) 1 := by
      refine ⟨by positivity, ?_⟩
      rw [div_le_one hy]; exact hny
    simp [rieszKernel, rieszKernelR, Set.indicator_of_mem hmem]
  · intro n hn
    simp only [Finset.mem_Icc, not_and_or, not_le] at hn
    rcases hn with h | h
    · interval_cases n
      · simp
    · have hny : y < (n:ℝ) := (Nat.floor_lt hy.le).mp h
      have hnot : (n:ℝ)/y ∉ Set.Ioc (0:ℝ) 1 := by
        rintro ⟨-, hc⟩
        rw [div_le_one hy] at hc
        linarith
      simp [rieszKernel, rieszKernelR, Set.indicator_of_notMem hnot]

/-! ## The main identity -/

/-- **Riesz mean of `1/ζ`.** For `Re s > 1` the Mellin transform of the first-order Riesz mean of
the Möbius function is `1 / (s (s+1) ζ(s))`. -/
theorem mellin_rieszMean {s : ℂ} (hs : 1 < s.re) :
    mellin rieszMean (-s) = 1 / (s * (s + 1) * riemannZeta s) := by
  have hσ : (0:ℝ) < s.re := by linarith
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs; linarith
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have hh : s = -1 := by linear_combination h
    rw [hh] at hs; norm_num at hs
  set G : ℕ → ℝ → ℂ :=
    fun n y => (y:ℂ) ^ (-s - 1) • ((ArithmeticFunction.moebius n : ℂ) * rieszKernel ((n:ℝ)/y))
    with hG
  have hG0 : G 0 = fun _ => 0 := by
    funext y; simp [hG]
  -- integrability of each term
  have hint : ∀ n : ℕ, Integrable (G n) (volume.restrict (Set.Ioi (0:ℝ))) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; rw [hG0]; exact integrable_zero ℝ ℂ _
    · have hn : (0:ℝ) < (n:ℝ) := by exact_mod_cast h
      have hmc := mellinConvergent_rieszKernel_scaled (s := s) (by linarith) hn
      rw [MellinConvergent] at hmc
      have h2 : G n = fun y : ℝ => (ArithmeticFunction.moebius n : ℂ) *
          ((y:ℂ) ^ (-s - 1) • rieszKernel ((n:ℝ)/y)) := by
        funext y; simp only [hG, smul_eq_mul]; ring
      rw [h2]
      exact hmc.const_mul _
  -- the `L¹` norms
  have hnormG : ∀ n : ℕ, 0 < n → ∫ y in Set.Ioi (0:ℝ), ‖G n y‖
      = |((ArithmeticFunction.moebius n : ℤ) : ℝ)| * ((n:ℝ) ^ (-s.re) / (s.re * (s.re + 1))) := by
    intro n hn
    have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    have heq : ∀ y ∈ Set.Ioi (0:ℝ), ‖G n y‖ = |((ArithmeticFunction.moebius n : ℤ) : ℝ)| *
        ‖(y : ℂ) ^ (-((s.re : ℝ) : ℂ) - 1) • rieszKernel ((n:ℝ) / y)‖ := by
      intro y hy
      simp only [hG, norm_smul, norm_mul]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hy, Complex.norm_cpow_eq_rpow_re_of_pos hy]
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re, Complex.ofReal_re]
      simp only [Complex.norm_intCast]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul,
      integral_norm_rieszKernel_scaled hσ hn']
  -- summability of the norms
  have hsum : Summable (fun n : ℕ => ∫ y in Set.Ioi (0:ℝ), ‖G n y‖) := by
    have hb : Summable (fun n : ℕ => (n:ℝ) ^ (-s.re) / (s.re * (s.re + 1))) :=
      (Real.summable_nat_rpow.mpr (by linarith)).div_const _
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg (fun y => norm_nonneg _)) ?_ hb
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp only [hG0, norm_zero, integral_zero]
      positivity
    · rw [hnormG n h]
      have hmu : |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 := by
        rcases eq_or_ne (ArithmeticFunction.moebius n) 0 with hh | hh
        · simp [hh]
        · rcases (ArithmeticFunction.moebius_ne_zero_iff_eq_or (n := n)).mp hh with h1 | h1 <;>
            simp [h1]
      have hpos : 0 ≤ (n:ℝ) ^ (-s.re) / (s.re * (s.re + 1)) := by positivity
      nlinarith [hpos]
  have hHS := hasSum_integral_of_summable_integral_norm hint hsum
  -- identify the sum of the series with the Riesz mean
  have hsumfun : ∀ y ∈ Set.Ioi (0:ℝ), (∑' n : ℕ, G n y) = (y:ℂ) ^ (-s - 1) • rieszMean y := by
    intro y hy
    simp only [hG, smul_eq_mul]
    rw [tsum_mul_left, rieszMean_eq_tsum hy]
  have hlhs : (∫ y in Set.Ioi (0:ℝ), ∑' n : ℕ, G n y) = mellin rieszMean (-s) := by
    rw [mellin]
    exact setIntegral_congr_fun measurableSet_Ioi hsumfun
  rw [hlhs] at hHS
  -- identify each integral with a term of the L-series of the Möbius function
  have hterm : ∀ n : ℕ, (∫ y in Set.Ioi (0:ℝ), G n y)
      = (1 / (s * (s + 1))) * LSeries.term (fun m => (ArithmeticFunction.moebius m : ℂ)) s n := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [hG0]
    · have hn : (0:ℝ) < (n:ℝ) := by exact_mod_cast h
      have h2 : G n = fun y : ℝ => (ArithmeticFunction.moebius n : ℂ) *
          ((y:ℂ) ^ (-s - 1) • rieszKernel ((n:ℝ)/y)) := by
        funext y; simp only [hG, smul_eq_mul]; ring
      rw [h2, integral_const_mul,
        show (∫ y in Set.Ioi (0:ℝ), (y:ℂ) ^ (-s - 1) • rieszKernel ((n:ℝ)/y))
          = mellin (fun y : ℝ => rieszKernel ((n:ℝ)/y)) (-s) from rfl,
        mellin_rieszKernel_scaled (by linarith) hn,
        LSeries.term_of_ne_zero (n := n) h.ne' _ s, Complex.cpow_neg]
      have hnc : ((n:ℕ) : ℂ) ≠ 0 := by
        simpa using h.ne'
      have hnz : ((n:ℕ) : ℂ) ^ s ≠ 0 := by
        rw [Complex.cpow_def_of_ne_zero hnc]
        exact Complex.exp_ne_zero _
      push_cast
      field_simp
  simp_rw [hterm] at hHS
  -- compare with the L-series
  have hLS : LSeriesSummable (fun m => (ArithmeticFunction.moebius m : ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  have hHS2 := (hLS.hasSum).mul_left (1 / (s * (s + 1)))
  have := hHS.unique hHS2
  rw [this]
  have hzeta : LSeries (fun m => (ArithmeticFunction.moebius m : ℂ)) s = 1 / riemannZeta s := by
    have h1 := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
    have h2 := ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs
    rw [h2] at h1
    have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
    field_simp at h1 ⊢
    linear_combination h1
  rw [show (∑' b : ℕ, LSeries.term (fun m => (ArithmeticFunction.moebius m : ℂ)) s b)
      = LSeries (fun m => (ArithmeticFunction.moebius m : ℂ)) s from rfl, hzeta]
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  field_simp

end RieszMeanZeta
