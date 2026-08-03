import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmDyadicFarTail
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# An explicit polynomial common cutoff for the Ehm far tail

The original far-tail package selects a common divisor cutoff by classical
choice from summability.  That is sufficient for the qualitative closure but
does not expose a conductor for subsequent Type-I/II estimates.  This file
replaces it with the explicit polynomial cutoff

```text
D(X) = (X + 1)^8.
```

The proof uses elementary integral-test bounds for the tails of `d⁻²` and
`d⁻³ᐟ²`.  No signed cancellation is used here.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmExplicitFarCutoff

open scoped BigOperators Topology
open Filter Set
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicCommonSplit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicFarTail

/-! ## Explicit finite p-series tails -/

/-- Integral-test bound for the finite `d⁻³ᐟ²` tail. -/
theorem sum_Icc_one_div_rpow_three_halves_le
    (D J : ℕ) (hD : 1 ≤ D) (hDJ : D ≤ J) :
    (∑ d ∈ Finset.Icc (D + 1) J,
      1 / (d : ℝ) ^ (3 / 2 : ℝ)) ≤
        2 * (D : ℝ) ^ (-(1 / 2 : ℝ)) := by
  let f : ℝ → ℝ := fun x ↦ x ^ (-(3 / 2 : ℝ))
  have hanti : AntitoneOn f (Set.Icc (D : ℝ) (J : ℝ)) := by
    apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (r := -(3 / 2 : ℝ))
      (by norm_num)).mono
    intro x hx
    have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
    exact hDpos.trans_le hx.1
  have hsum := hanti.sum_le_integral_Ico hDJ
  have hreindex :
      (∑ d ∈ Finset.Icc (D + 1) J,
        1 / (d : ℝ) ^ (3 / 2 : ℝ)) =
      ∑ i ∈ Finset.Ico D J, f (i + 1 : ℕ) := by
    have hadd := Finset.sum_Ico_add (fun d : ℕ ↦ f d) D J 1
    rw [show Finset.Icc (D + 1) J = Finset.Ico (D + 1) (J + 1) by
      ext d
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega]
    calc
      (∑ d ∈ Finset.Ico (D + 1) (J + 1),
          1 / (d : ℝ) ^ (3 / 2 : ℝ)) =
          ∑ d ∈ Finset.Ico (D + 1) (J + 1), f d := by
            apply Finset.sum_congr rfl
            intro d _
            unfold f
            rw [Real.rpow_neg (Nat.cast_nonneg d)]
            simp only [one_div]
      _ = ∑ i ∈ Finset.Ico D J, f ((1 + i : ℕ) : ℝ) := hadd.symm
      _ = ∑ i ∈ Finset.Ico D J, f (i + 1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [add_comm]
  rw [hreindex]
  refine hsum.trans ?_
  have hzero : (0 : ℝ) ∉ Set.uIcc (D : ℝ) (J : ℝ) := by
    rw [uIcc_of_le (by exact_mod_cast hDJ)]
    intro hz
    have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
    exact (not_le_of_gt hDpos) hz.1
  rw [show f = fun x : ℝ ↦ x ^ (-(3 / 2 : ℝ)) by rfl]
  rw [integral_rpow (Or.inr ⟨by norm_num, hzero⟩)]
  have hJnonneg : 0 ≤ (J : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  norm_num
  linarith

/-- Integral-test bound for the finite `d⁻²` tail. -/
theorem sum_Icc_one_div_sq_le
    (D J : ℕ) (hD : 1 ≤ D) (hDJ : D ≤ J) :
    (∑ d ∈ Finset.Icc (D + 1) J,
      1 / (d : ℝ) ^ (2 : ℕ)) ≤ 1 / (D : ℝ) := by
  let f : ℝ → ℝ := fun x ↦ x ^ (-(2 : ℝ))
  have hanti : AntitoneOn f (Set.Icc (D : ℝ) (J : ℝ)) := by
    apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (r := -(2 : ℝ))
      (by norm_num)).mono
    intro x hx
    have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
    exact hDpos.trans_le hx.1
  have hsum := hanti.sum_le_integral_Ico hDJ
  have hreindex :
      (∑ d ∈ Finset.Icc (D + 1) J,
        1 / (d : ℝ) ^ (2 : ℕ)) =
      ∑ i ∈ Finset.Ico D J, f (i + 1 : ℕ) := by
    have hadd := Finset.sum_Ico_add (fun d : ℕ ↦ f d) D J 1
    rw [show Finset.Icc (D + 1) J = Finset.Ico (D + 1) (J + 1) by
      ext d
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega]
    calc
      (∑ d ∈ Finset.Ico (D + 1) (J + 1),
          1 / (d : ℝ) ^ (2 : ℕ)) =
          ∑ d ∈ Finset.Ico (D + 1) (J + 1), f d := by
            apply Finset.sum_congr rfl
            intro d _
            unfold f
            rw [Real.rpow_neg (Nat.cast_nonneg d)]
            calc
              1 / (d : ℝ) ^ (2 : ℕ) = ((d : ℝ) ^ (2 : ℕ))⁻¹ := by
                rw [one_div]
              _ = ((d : ℝ) ^ (2 : ℝ))⁻¹ :=
                congrArg Inv.inv (Real.rpow_natCast (d : ℝ) 2).symm
      _ = ∑ i ∈ Finset.Ico D J, f ((1 + i : ℕ) : ℝ) := hadd.symm
      _ = ∑ i ∈ Finset.Ico D J, f (i + 1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [add_comm]
  rw [hreindex]
  refine hsum.trans ?_
  have hzero : (0 : ℝ) ∉ Set.uIcc (D : ℝ) (J : ℝ) := by
    rw [uIcc_of_le (by exact_mod_cast hDJ)]
    intro hz
    have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
    exact (not_le_of_gt hDpos) hz.1
  rw [show f = fun x : ℝ ↦ x ^ (-(2 : ℝ)) by rfl]
  rw [integral_rpow (Or.inr ⟨by norm_num, hzero⟩)]
  have hJnonneg : 0 ≤ (J : ℝ) ^ (-(1 : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  norm_num
  rw [Real.rpow_neg (Nat.cast_nonneg D), Real.rpow_one]
  linarith

/-! ## Quantitative logarithmic coefficient bound -/

/-- Pointwise p-series majorant for one BCF logarithmic coefficient. -/
theorem abs_dirichletCoeff_div_sq_le_pSeries
    (N d : ℕ) (hN : 2 ≤ N) :
    |dirichletCoeff N d| / (d : ℝ) ^ 2 ≤
      1 / (d : ℝ) ^ (2 : ℕ) +
        (2 / Real.log (N : ℝ)) *
          (1 / (d : ℝ) ^ (3 / 2 : ℝ)) := by
  by_cases hd0 : d = 0
  · subst d
    norm_num
  have hdpos : (0 : ℝ) < d := by
    exact_mod_cast (Nat.pos_of_ne_zero hd0)
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogd0 : 0 ≤ Real.log (d : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hd0))
  have hmu : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  have hratio0 : 0 ≤ Real.log (d : ℝ) / Real.log (N : ℝ) :=
    div_nonneg hlogd0 hlogN.le
  have hweight : |weight N d| ≤
      1 + Real.log (d : ℝ) / Real.log (N : ℝ) := by
    rw [weight_of_two_le hN]
    calc
      |1 - Real.log (d : ℝ) / Real.log (N : ℝ)| ≤
          |(1 : ℝ)| + |Real.log (d : ℝ) / Real.log (N : ℝ)| :=
        abs_sub _ _
      _ = 1 + Real.log (d : ℝ) / Real.log (N : ℝ) := by
        rw [abs_one, abs_of_nonneg hratio0]
  have hlogd : Real.log (d : ℝ) ≤
      2 * (d : ℝ) ^ (1 / 2 : ℝ) := by
    have h := Real.log_le_rpow_div
      (x := (d : ℝ)) (ε := (1 / 2 : ℝ)) hdpos.le (by norm_num)
    nlinarith
  have hcoeff : |dirichletCoeff N d| ≤
      1 + (2 / Real.log (N : ℝ)) * (d : ℝ) ^ (1 / 2 : ℝ) := by
    unfold dirichletCoeff
    rw [abs_mul]
    calc
      |((ArithmeticFunction.moebius d : ℤ) : ℝ)| * |weight N d| ≤
          1 * (1 + Real.log (d : ℝ) / Real.log (N : ℝ)) := by
        gcongr
      _ = 1 + Real.log (d : ℝ) / Real.log (N : ℝ) := by ring
      _ ≤ 1 + (2 * (d : ℝ) ^ (1 / 2 : ℝ)) /
          Real.log (N : ℝ) := by
        have hdiv := (div_le_div_iff_of_pos_right hlogN).mpr hlogd
        simpa [add_comm] using add_le_add_left hdiv 1
      _ = _ := by ring
  calc
    |dirichletCoeff N d| / (d : ℝ) ^ 2 ≤
        (1 + (2 / Real.log (N : ℝ)) * (d : ℝ) ^ (1 / 2 : ℝ)) /
          (d : ℝ) ^ 2 := by gcongr
    _ = 1 / (d : ℝ) ^ (2 : ℕ) +
        (2 / Real.log (N : ℝ)) *
          (1 / (d : ℝ) ^ (3 / 2 : ℝ)) := by
      have hpow2 : (d : ℝ) ^ (2 : ℕ) = (d : ℝ) ^ (2 : ℝ) :=
        (Real.rpow_natCast (d : ℝ) 2).symm
      rw [hpow2]
      have hratio :
          (d : ℝ) ^ (1 / 2 : ℝ) / (d : ℝ) ^ (2 : ℝ) =
            1 / (d : ℝ) ^ (3 / 2 : ℝ) := by
        rw [← Real.rpow_sub hdpos]
        norm_num
        exact Real.rpow_neg hdpos.le (3 / 2 : ℝ)
      rw [add_div, mul_div_assoc, hratio]

/-- Uniform finite tail bound for a single logarithmic coefficient sequence. -/
theorem sum_abs_dirichletCoeff_div_sq_le
    (N D J : ℕ) (hN : 2 ≤ N) (hD : 1 ≤ D) (hDJ : D ≤ J) :
    (∑ d ∈ Finset.Icc (D + 1) J,
      |dirichletCoeff N d| / (d : ℝ) ^ 2) ≤
      1 / (D : ℝ) +
        (4 / Real.log (N : ℝ)) * (D : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  calc
    (∑ d ∈ Finset.Icc (D + 1) J,
        |dirichletCoeff N d| / (d : ℝ) ^ 2) ≤
      ∑ d ∈ Finset.Icc (D + 1) J,
        (1 / (d : ℝ) ^ (2 : ℕ) +
          (2 / Real.log (N : ℝ)) *
            (1 / (d : ℝ) ^ (3 / 2 : ℝ))) := by
      exact Finset.sum_le_sum fun d _ ↦
        abs_dirichletCoeff_div_sq_le_pSeries N d hN
    _ = (∑ d ∈ Finset.Icc (D + 1) J, 1 / (d : ℝ) ^ (2 : ℕ)) +
        (2 / Real.log (N : ℝ)) *
          (∑ d ∈ Finset.Icc (D + 1) J,
            1 / (d : ℝ) ^ (3 / 2 : ℝ)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 1 / (D : ℝ) +
        (2 / Real.log (N : ℝ)) *
          (2 * (D : ℝ) ^ (-(1 / 2 : ℝ))) := by
      exact add_le_add
        (sum_Icc_one_div_sq_le D J hD hDJ)
        (mul_le_mul_of_nonneg_left
          (sum_Icc_one_div_rpow_three_halves_le D J hD hDJ)
          (div_nonneg (by norm_num) hlogN.le))
    _ = _ := by ring

/-! ## Explicit dyadic package -/

/-- Polynomial common divisor cutoff used by the quantitative route. -/
def ehmExplicitFarCutoff (X : ℕ) : ℕ :=
  (X + 1) ^ 8

/-- The explicit cutoff dominates the whole dyadic block. -/
theorem two_mul_le_ehmExplicitFarCutoff (X : ℕ) :
    2 * X ≤ ehmExplicitFarCutoff X := by
  unfold ehmExplicitFarCutoff
  calc
    2 * X ≤ (X + 1) ^ 2 := by nlinarith [Nat.zero_le (X ^ 2)]
    _ ≤ (X + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)

/-- Closed form of the fractional power generated by the `d⁻³ᐟ²` tail. -/
theorem ehmExplicitFarCutoff_rpow_neg_half (X : ℕ) :
    (ehmExplicitFarCutoff X : ℝ) ^ (-(1 / 2 : ℝ)) =
      1 / (((X : ℝ) + 1) ^ (4 : ℕ)) := by
  have hx : 0 < (X : ℝ) + 1 := by positivity
  unfold ehmExplicitFarCutoff
  push_cast
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hx.le]
  norm_num
  rfl

/-- Explicit null majorant after summing the coefficient tails over the
dyadic block. -/
noncomputable def ehmExplicitFarEta (X : ℕ) : ℝ :=
  let x := (X : ℝ) + 1
  64 * (x ^ 2 / x ^ 8 +
    (4 / Real.log 2) * (x ^ 2 / x ^ 4))

theorem ehmExplicitFarEta_nonneg (X : ℕ) :
    0 ≤ ehmExplicitFarEta X := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold ehmExplicitFarEta
  dsimp only
  positivity

theorem ehmExplicitFarEta_tendsto_zero :
    Tendsto ehmExplicitFarEta atTop (nhds 0) := by
  have hx : Tendsto (fun X : ℕ ↦ (X : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have h28 : Tendsto (fun X : ℕ ↦
      (((X : ℝ) + 1) ^ 2 / ((X : ℝ) + 1) ^ 8)) atTop (nhds 0) :=
    (tendsto_pow_div_pow_atTop_zero (𝕜 := ℝ) (p := 2) (q := 8)
      (by omega)).comp hx
  have h24 : Tendsto (fun X : ℕ ↦
      (((X : ℝ) + 1) ^ 2 / ((X : ℝ) + 1) ^ 4)) atTop (nhds 0) :=
    (tendsto_pow_div_pow_atTop_zero (𝕜 := ℝ) (p := 2) (q := 4)
      (by omega)).comp hx
  simpa [ehmExplicitFarEta] using
    (h28.add ((tendsto_const_nhds.mul h24))).const_mul (64 : ℝ)

/-- Each member of the dyadic block contributes at most the explicit common
majorant. -/
theorem ehmDyadicDivisorTailTerm_le_explicitEta
    (X J N : ℕ) (hX : 2 ≤ X) (hJ : ehmExplicitFarCutoff X ≤ J)
    (hNmem : N ∈ ehmDyadicNBlock X) :
    16 * (N : ℝ) ^ 2 *
        (∑ d ∈ Finset.Icc (ehmExplicitFarCutoff X + 1) J,
          |dirichletCoeff N d| / (d : ℝ) ^ 2) ≤
      ehmExplicitFarEta X := by
  have hN2 : 2 ≤ N := hX.trans (Finset.mem_Icc.mp hNmem).1
  have hNle : N ≤ 2 * X := (Finset.mem_Icc.mp hNmem).2
  have hD1 : 1 ≤ ehmExplicitFarCutoff X := by
    unfold ehmExplicitFarCutoff
    have hpos : 0 < (X + 1) ^ 8 := by positivity
    omega
  have htail := sum_abs_dirichletCoeff_div_sq_le
    N (ehmExplicitFarCutoff X) J hN2 hD1 hJ
  have hlogN : Real.log 2 ≤ Real.log (N : ℝ) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast hN2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogNpos : 0 < Real.log (N : ℝ) := hlog2.trans_le hlogN
  have hrecip : 4 / Real.log (N : ℝ) ≤ 4 / Real.log 2 := by
    exact div_le_div_of_nonneg_left (by norm_num) hlog2 hlogN
  have hNcast : (N : ℝ) ≤ 2 * (X : ℝ) := by exact_mod_cast hNle
  have hxnonneg : 0 ≤ (X : ℝ) := Nat.cast_nonneg X
  have htail_nonneg : 0 ≤
      1 / (ehmExplicitFarCutoff X : ℝ) +
        (4 / Real.log (N : ℝ)) *
          (ehmExplicitFarCutoff X : ℝ) ^ (-(1 / 2 : ℝ)) := by
    positivity
  calc
    16 * (N : ℝ) ^ 2 *
        (∑ d ∈ Finset.Icc (ehmExplicitFarCutoff X + 1) J,
          |dirichletCoeff N d| / (d : ℝ) ^ 2) ≤
      16 * (N : ℝ) ^ 2 *
        (1 / (ehmExplicitFarCutoff X : ℝ) +
          (4 / Real.log (N : ℝ)) *
            (ehmExplicitFarCutoff X : ℝ) ^ (-(1 / 2 : ℝ))) := by
      gcongr
    _ ≤ 64 * (X : ℝ) ^ 2 *
        (1 / (ehmExplicitFarCutoff X : ℝ) +
          (4 / Real.log 2) *
            (ehmExplicitFarCutoff X : ℝ) ^ (-(1 / 2 : ℝ))) := by
      have hpow : (N : ℝ) ^ 2 ≤ (2 * (X : ℝ)) ^ 2 := by gcongr
      have hbracket :
          1 / (ehmExplicitFarCutoff X : ℝ) +
              (4 / Real.log (N : ℝ)) *
                (ehmExplicitFarCutoff X : ℝ) ^ (-(1 / 2 : ℝ)) ≤
            1 / (ehmExplicitFarCutoff X : ℝ) +
              (4 / Real.log 2) *
                (ehmExplicitFarCutoff X : ℝ) ^ (-(1 / 2 : ℝ)) := by
        gcongr
      nlinarith [Real.rpow_nonneg
        (show 0 ≤ (ehmExplicitFarCutoff X : ℝ) by positivity)
        (-(1 / 2 : ℝ))]
    _ ≤ ehmExplicitFarEta X := by
      rw [ehmExplicitFarCutoff_rpow_neg_half]
      unfold ehmExplicitFarCutoff ehmExplicitFarEta
      dsimp only
      push_cast
      have hxle : (X : ℝ) ≤ (X : ℝ) + 1 := by linarith
      have hxpow : (X : ℝ) ^ 2 ≤ ((X : ℝ) + 1) ^ 2 := by gcongr
      have hbase : 0 < (X : ℝ) + 1 := by positivity
      field_simp
      nlinarith [sq_nonneg (Real.log 2), hlog2]

/-- Quantitative dyadic far-tail bound at the explicit cutoff. -/
theorem ehmDyadicCommonDivisorTailMass_explicit_bound
    (X J : ℕ) (hX : 2 ≤ X) (hJ : ehmExplicitFarCutoff X ≤ J) :
    ehmDyadicCommonDivisorTailMass X (ehmExplicitFarCutoff X) J ≤
      ((ehmDyadicNBlock X).card : ℝ) * ehmExplicitFarEta X := by
  unfold ehmDyadicCommonDivisorTailMass
  calc
    (∑ N ∈ ehmDyadicNBlock X,
        16 * (N : ℝ) ^ 2 *
          ∑ d ∈ Finset.Icc (ehmExplicitFarCutoff X + 1) J,
            |dirichletCoeff N d| / (d : ℝ) ^ 2) ≤
      ∑ _N ∈ ehmDyadicNBlock X, ehmExplicitFarEta X := by
        exact Finset.sum_le_sum fun N hNmem ↦
          ehmDyadicDivisorTailTerm_le_explicitEta X J N hX hJ hNmem
    _ = ((ehmDyadicNBlock X).card : ℝ) * ehmExplicitFarEta X := by simp

/-- Fully explicit replacement for the choice-based far-tail package. -/
noncomputable def ehmDyadicExplicitFarTailVanishing :
    EhmDyadicUniformFarTailVanishing where
  D := ehmExplicitFarCutoff
  D_ge := two_mul_le_ehmExplicitFarCutoff
  eta := ehmExplicitFarEta
  eta_nonneg := ehmExplicitFarEta_nonneg
  eta_tendsto_zero := ehmExplicitFarEta_tendsto_zero
  uniform_bound := fun X hX J hJ ↦
    ehmDyadicCommonDivisorTailMass_explicit_bound X J hX hJ

end RH.Criteria.NymanBeurling.BCFLogTaperEhmExplicitFarCutoff
