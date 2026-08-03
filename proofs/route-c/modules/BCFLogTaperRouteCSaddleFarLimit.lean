import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleFarOptimization
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Route C: vanishing of the factorial-compressed far-saddle majorant

This module completes the quantitative step left by the optimized Gamma
bound.  After division by the principal real saddle scale, the exact
factorization consists of a Stirling-normalized factorial factor and a strict
geometric factor.  The former grows at most linearly; the latter has base
strictly below one.  Consequently the factorial majorant, and then the
squared norm of the genuine far-sector integral, tend to zero.

The result is deliberately stated relative to the real principal scale.  The
full complex saddle normalization also contains a fixed complex constant and
the root-exponential factor `exp (-A * sqrt n)`; absorbing that subexponential
factor is the next step.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleFarLimit


open Filter
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleCentralWindow
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleFarEntropy
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleFarOptimization

theorem stirlingSeq_succ_le_one (n : ℕ) :
    Stirling.stirlingSeq (n + 1) ≤ Stirling.stirlingSeq 1 := by
  simpa only [Function.comp_apply, Nat.zero_add] using
    Stirling.stirlingSeq'_antitone (Nat.zero_le n)

theorem sqrt_two_mul_succ_le_succ (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt (2 * (n + 1 : ℝ)) ≤ (n + 1 : ℝ) := by
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith

theorem one_add_inv_pow_succ_le_exp_two (n : ℕ) (hn : 1 ≤ n) :
    (1 + 1 / (n : ℝ)) ^ (n + 1) ≤ Real.exp 2 := by
  have hnR : 0 < (n : ℝ) := by positivity
  have hbase : 1 + 1 / (n : ℝ) ≤ Real.exp (1 / (n : ℝ)) :=
    by simpa [add_comm] using Real.add_one_le_exp (1 / (n : ℝ))
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + 1 / (n : ℝ))
    hbase (n + 1)
  calc
    (1 + 1 / (n : ℝ)) ^ (n + 1) ≤
        Real.exp (1 / (n : ℝ)) ^ (n + 1) := hp
    _ = Real.exp (((n + 1 : ℕ) : ℝ) * (1 / (n : ℝ))) := by
      rw [← Real.exp_nat_mul]
    _ ≤ Real.exp 2 := by
      apply Real.exp_le_exp.mpr
      have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      field_simp
      push_cast
      nlinarith

theorem factorial_scaled_le_linear (n : ℕ) (hn : 1 ≤ n) :
    Real.exp (n : ℝ) * ((n + 1).factorial : ℝ) /
        Real.rpow n ((n : ℝ) + 1) ≤
      Stirling.stirlingSeq 1 * Real.exp 2 * (n + 1 : ℝ) := by
  have hnR : 0 < (n : ℝ) := by positivity
  have hsuccR : 0 < (n + 1 : ℝ) := by positivity
  have hden : 0 < Real.sqrt (2 * (n + 1 : ℝ)) *
      (((n + 1 : ℝ) / Real.exp 1) ^ (n + 1)) := by positivity
  have hfac : ((n + 1).factorial : ℝ) =
      Stirling.stirlingSeq (n + 1) *
        (Real.sqrt (2 * (n + 1 : ℝ)) *
          (((n + 1 : ℝ) / Real.exp 1) ^ (n + 1))) := by
    rw [Stirling.stirlingSeq]
    field_simp
    push_cast
    rfl
  have hstir : Stirling.stirlingSeq (n + 1) ≤ Stirling.stirlingSeq 1 :=
    stirlingSeq_succ_le_one n
  have hstir0 : 0 ≤ Stirling.stirlingSeq (n + 1) := by
    unfold Stirling.stirlingSeq
    positivity
  have hstir10 : 0 ≤ Stirling.stirlingSeq 1 := by
    unfold Stirling.stirlingSeq
    positivity
  have hsqrt := sqrt_two_mul_succ_le_succ n hn
  have hpow := one_add_inv_pow_succ_le_exp_two n hn
  rw [hfac]
  have hratio :
      Real.exp (n : ℝ) *
          (((n + 1 : ℝ) / Real.exp 1) ^ (n + 1)) /
            Real.rpow n ((n : ℝ) + 1) =
        Real.exp (-1) * (1 + 1 / (n : ℝ)) ^ (n + 1) := by
    have hexp : (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) := by
      push_cast
      ring
    have hrpow : Real.rpow (n : ℝ) (((n + 1 : ℕ) : ℝ)) =
        (n : ℝ) ^ (n + 1) := Real.rpow_natCast _ _
    rw [hexp, hrpow]
    rw [div_pow]
    rw [Real.exp_one_pow]
    field_simp
    rw [show Real.exp (((n + 1 : ℕ) : ℝ)) =
        Real.exp (n : ℝ) * Real.exp 1 by
      push_cast
      rw [Real.exp_add]]
    rw [Real.exp_neg]
    field_simp
    push_cast
    rw [div_pow]
    field_simp
  rw [show Real.exp (n : ℝ) *
      (Stirling.stirlingSeq (n + 1) *
        (Real.sqrt (2 * (n + 1 : ℝ)) *
          (((n + 1 : ℝ) / Real.exp 1) ^ (n + 1)))) /
          Real.rpow n ((n : ℝ) + 1) =
      Stirling.stirlingSeq (n + 1) * Real.sqrt (2 * (n + 1 : ℝ)) *
        (Real.exp (n : ℝ) *
          (((n + 1 : ℝ) / Real.exp 1) ^ (n + 1)) /
            Real.rpow n ((n : ℝ) + 1)) by ring]
  rw [hratio]
  calc
    Stirling.stirlingSeq (n + 1) * Real.sqrt (2 * (n + 1 : ℝ)) *
        (Real.exp (-1) * (1 + 1 / (n : ℝ)) ^ (n + 1))
      ≤ Stirling.stirlingSeq 1 * (n + 1 : ℝ) *
          (1 * Real.exp 2) := by
        gcongr
        · exact Real.exp_neg_one_lt_half.le.trans (by norm_num)
    _ = Stirling.stirlingSeq 1 * Real.exp 2 * (n + 1 : ℝ) := by ring

noncomputable def routeCSaddlePrincipalScaleOne (n : ℕ) : ℝ :=
  Real.exp (-(n : ℝ)) * Real.rpow n ((n : ℝ) + 1 / 2)

noncomputable def routeCSaddleHalfGeometricBase (delta : ℝ) : ℝ :=
  Real.exp (-routeCSaddleEntropyGap delta) /
    (2 * (1 / 2 - routeCSaddleHalfEntropyEpsilon delta))

theorem routeCSaddleHalfGeometricBase_pos
    {delta : ℝ} (hd0 : 0 < delta) (hd1 : delta < 1) :
    0 < routeCSaddleHalfGeometricBase delta := by
  unfold routeCSaddleHalfGeometricBase
  exact div_pos (Real.exp_pos _)
    (mul_pos (by norm_num) (sub_pos.mpr
      (routeCSaddleHalfEntropyEpsilon_lt_half hd0 hd1)))

theorem routeCSaddleHalfGeometricBase_lt_one
    {delta : ℝ} (hd0 : 0 < delta) (hd1 : delta < 1) :
    routeCSaddleHalfGeometricBase delta < 1 := by
  unfold routeCSaddleHalfGeometricBase
  rw [div_lt_one (mul_pos (by norm_num) (sub_pos.mpr
    (routeCSaddleHalfEntropyEpsilon_lt_half hd0 hd1)))]
  exact exp_neg_entropyGap_lt_double_retainedRate hd0 hd1

noncomputable def routeCSaddleHalfNormalizationConstant
    (A : ℂ) (delta : ℝ) : ℝ :=
  Real.exp (‖A‖ ^ 2 /
      (2 * routeCSaddleHalfEntropyEpsilon delta)) * Real.sqrt Real.pi /
    (2 * (1 / 2 - routeCSaddleHalfEntropyEpsilon delta) ^ 2)

theorem factorial_majorant_normalized_eq
    (A : ℂ) (delta : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hd0 : 0 < delta) (hd1 : delta < 1) :
    (routeCSaddleHalfGammaPrefactor A delta
          (routeCSaddleHalfEntropyEpsilon delta) n ^ 2 *
        (((n + 1).factorial : ℝ) *
          Real.rpow 2 (-((n : ℝ) + 1)) * Real.sqrt Real.pi)) /
        routeCSaddlePrincipalScaleOne n ^ 2 =
      routeCSaddleHalfNormalizationConstant A delta *
        (Real.exp (n : ℝ) * ((n + 1).factorial : ℝ) /
          Real.rpow n ((n : ℝ) + 1)) *
        routeCSaddleHalfGeometricBase delta ^ n := by
  have hnR : 0 < (n : ℝ) := by positivity
  have he0 := routeCSaddleHalfEntropyEpsilon_pos hd0 hd1
  have he1 := routeCSaddleHalfEntropyEpsilon_lt_half hd0 hd1
  have hb : 0 < 1 / 2 - routeCSaddleHalfEntropyEpsilon delta := sub_pos.mpr he1
  have hrho : 0 < routeCSaddleHalfGeometricBase delta :=
    routeCSaddleHalfGeometricBase_pos hd0 hd1
  have hpref : 0 < routeCSaddleHalfGammaPrefactor A delta
      (routeCSaddleHalfEntropyEpsilon delta) n := by
    unfold routeCSaddleHalfGammaPrefactor
    exact mul_pos
      (mul_pos
        (mul_pos
          (mul_pos (Real.rpow_pos_of_pos hnR _) (Real.exp_pos _))
          (Real.exp_pos _))
        (Real.exp_pos _))
      (mul_pos
        (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hnR _))
        (Real.rpow_pos_of_pos (one_div_pos.mpr hb) _))
  have hscale : 0 < routeCSaddlePrincipalScaleOne n := by
    unfold routeCSaddlePrincipalScaleOne
    exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hnR _)
  have hfactor : 0 < (((n + 1).factorial : ℝ) *
      Real.rpow 2 (-((n : ℝ) + 1)) * Real.sqrt Real.pi) := by
    exact mul_pos
      (mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _))
        (Real.rpow_pos_of_pos (by norm_num) _))
      (Real.sqrt_pos.2 Real.pi_pos)
  have hleft : 0 <
      (routeCSaddleHalfGammaPrefactor A delta
            (routeCSaddleHalfEntropyEpsilon delta) n ^ 2 *
          (((n + 1).factorial : ℝ) *
            Real.rpow 2 (-((n : ℝ) + 1)) * Real.sqrt Real.pi)) /
          routeCSaddlePrincipalScaleOne n ^ 2 := by
    exact div_pos (mul_pos (sq_pos_of_pos hpref) hfactor)
      (sq_pos_of_pos hscale)
  have hconstant : 0 < routeCSaddleHalfNormalizationConstant A delta := by
    unfold routeCSaddleHalfNormalizationConstant
    exact div_pos
      (mul_pos (Real.exp_pos _) (Real.sqrt_pos.2 Real.pi_pos))
      (mul_pos (by norm_num) (sq_pos_of_pos hb))
  have hscaled : 0 < Real.exp (n : ℝ) * ((n + 1).factorial : ℝ) /
      Real.rpow n ((n : ℝ) + 1) := by
    exact div_pos
      (mul_pos (Real.exp_pos _) (Nat.cast_pos.mpr (Nat.factorial_pos _)))
      (Real.rpow_pos_of_pos hnR _)
  have hright : 0 < routeCSaddleHalfNormalizationConstant A delta *
      (Real.exp (n : ℝ) * ((n + 1).factorial : ℝ) /
        Real.rpow n ((n : ℝ) + 1)) *
      routeCSaddleHalfGeometricBase delta ^ n := by positivity
  have hlogpref :
      Real.log (routeCSaddleHalfGammaPrefactor A delta
        (routeCSaddleHalfEntropyEpsilon delta) n) =
        (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) -
          (1 / 2 * (n : ℝ) * routeCSaddleEntropyGap delta) +
          ‖A‖ ^ 2 / (4 * routeCSaddleHalfEntropyEpsilon delta) +
          (1 / 2 * (n : ℝ)) - ((n : ℝ) / 2) * Real.log (n : ℝ) -
          ((n : ℝ) / 2 + 1) *
            Real.log (1 / 2 - routeCSaddleHalfEntropyEpsilon delta) := by
    unfold routeCSaddleHalfGammaPrefactor
    have hx1 : 0 < Real.rpow (n : ℝ) (n : ℝ) * Real.exp (-(n : ℝ)) :=
      mul_pos (Real.rpow_pos_of_pos hnR _) (Real.exp_pos _)
    have hx2 : 0 < Real.exp
        (-((1 / 2 : ℝ) * (n : ℝ) * routeCSaddleEntropyGap delta)) :=
      Real.exp_pos _
    have hx3 : 0 < Real.exp
        (‖A‖ ^ 2 / (4 * routeCSaddleHalfEntropyEpsilon delta)) :=
      Real.exp_pos _
    have hx4a : 0 < Real.exp ((1 / 2 : ℝ) * (n : ℝ)) := Real.exp_pos _
    have hx4b : 0 < Real.rpow (n : ℝ) (-((n : ℝ) / 2)) :=
      Real.rpow_pos_of_pos hnR _
    have hx4c : 0 < Real.rpow
        (1 / (1 / 2 - routeCSaddleHalfEntropyEpsilon delta))
        ((n : ℝ) / 2 + 1) :=
      Real.rpow_pos_of_pos (one_div_pos.mpr hb) _
    rw [Real.log_mul (mul_ne_zero (mul_ne_zero hx1.ne' hx2.ne') hx3.ne')
      (mul_ne_zero (mul_ne_zero hx4a.ne' hx4b.ne') hx4c.ne')]
    rw [Real.log_mul (mul_ne_zero hx1.ne' hx2.ne') hx3.ne']
    rw [Real.log_mul hx1.ne' hx2.ne']
    rw [Real.log_mul
      (x := Real.rpow (n : ℝ) (n : ℝ)) (y := Real.exp (-(n : ℝ)))
      (Real.rpow_pos_of_pos hnR _).ne' (Real.exp_ne_zero _)]
    rw [Real.log_mul (mul_ne_zero hx4a.ne' hx4b.ne') hx4c.ne']
    rw [Real.log_mul hx4a.ne' hx4b.ne']
    have hlogn₁ : Real.log (Real.rpow (n : ℝ) (n : ℝ)) =
        (n : ℝ) * Real.log (n : ℝ) := Real.log_rpow hnR _
    have hlogn₂ : Real.log (Real.rpow (n : ℝ) (-((n : ℝ) / 2))) =
        (-((n : ℝ) / 2)) * Real.log (n : ℝ) := Real.log_rpow hnR _
    have hloginvb : Real.log (Real.rpow
        (1 / (1 / 2 - routeCSaddleHalfEntropyEpsilon delta))
        ((n : ℝ) / 2 + 1)) =
        ((n : ℝ) / 2 + 1) *
          Real.log (1 / (1 / 2 - routeCSaddleHalfEntropyEpsilon delta)) :=
      Real.log_rpow (one_div_pos.mpr hb) _
    rw [hlogn₁, hlogn₂, hloginvb]
    rw [Real.log_div one_ne_zero hb.ne', Real.log_one]
    simp only [Real.log_exp, zero_sub]
    ring
  have hlogscale : Real.log (routeCSaddlePrincipalScaleOne n) =
      -(n : ℝ) + ((n : ℝ) + 1 / 2) * Real.log (n : ℝ) := by
    unfold routeCSaddlePrincipalScaleOne
    rw [Real.log_mul
      (x := Real.exp (-(n : ℝ)))
      (y := Real.rpow n ((n : ℝ) + 1 / 2))
      (Real.exp_ne_zero _) (Real.rpow_pos_of_pos hnR _).ne']
    have hlogn : Real.log (Real.rpow (n : ℝ) ((n : ℝ) + 1 / 2)) =
        ((n : ℝ) + 1 / 2) * Real.log (n : ℝ) :=
      Real.log_rpow hnR _
    rw [Real.log_exp, hlogn]
  have hlogfactor : Real.log ((((n + 1).factorial : ℝ) *
      Real.rpow 2 (-((n : ℝ) + 1)) * Real.sqrt Real.pi)) =
      Real.log ((n + 1).factorial : ℝ) -
        ((n : ℝ) + 1) * Real.log 2 + Real.log (Real.sqrt Real.pi) := by
    rw [Real.log_mul
      (x := ((n + 1).factorial : ℝ) * Real.rpow 2 (-((n : ℝ) + 1)))
      (y := Real.sqrt Real.pi)
      (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
        (Real.rpow_pos_of_pos (by norm_num) _).ne')
      (Real.sqrt_pos.2 Real.pi_pos).ne']
    rw [Real.log_mul
      (x := ((n + 1).factorial : ℝ))
      (y := Real.rpow 2 (-((n : ℝ) + 1)))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
      (Real.rpow_pos_of_pos (by norm_num) _).ne']
    have hlogtwo : Real.log (Real.rpow 2 (-((n : ℝ) + 1))) =
        (-((n : ℝ) + 1)) * Real.log 2 :=
      Real.log_rpow (by norm_num) _
    rw [hlogtwo]
    ring
  have hlogconstant :
      Real.log (routeCSaddleHalfNormalizationConstant A delta) =
        ‖A‖ ^ 2 / (2 * routeCSaddleHalfEntropyEpsilon delta) +
          Real.log (Real.sqrt Real.pi) - Real.log 2 -
          2 * Real.log (1 / 2 - routeCSaddleHalfEntropyEpsilon delta) := by
    unfold routeCSaddleHalfNormalizationConstant
    rw [Real.log_div
      (mul_ne_zero (Real.exp_ne_zero _) (Real.sqrt_pos.2 Real.pi_pos).ne')
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hb.ne'))]
    rw [Real.log_mul (Real.exp_ne_zero _) (Real.sqrt_pos.2 Real.pi_pos).ne']
    rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hb.ne')]
    rw [Real.log_exp, Real.log_pow]
    ring
  have hlogscaled :
      Real.log (Real.exp (n : ℝ) * ((n + 1).factorial : ℝ) /
        Real.rpow n ((n : ℝ) + 1)) =
        (n : ℝ) + Real.log ((n + 1).factorial : ℝ) -
          ((n : ℝ) + 1) * Real.log (n : ℝ) := by
    rw [Real.log_div
      (x := Real.exp (n : ℝ) * ((n + 1).factorial : ℝ))
      (y := Real.rpow n ((n : ℝ) + 1))
      (mul_ne_zero (Real.exp_ne_zero _)
        (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)))
      (Real.rpow_pos_of_pos hnR _).ne']
    rw [Real.log_mul
      (x := Real.exp (n : ℝ)) (y := ((n + 1).factorial : ℝ))
      (Real.exp_ne_zero _)
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))]
    have hlogn : Real.log (Real.rpow (n : ℝ) ((n : ℝ) + 1)) =
        ((n : ℝ) + 1) * Real.log (n : ℝ) :=
      Real.log_rpow hnR _
    rw [Real.log_exp, hlogn]
  have hlogrho :
      Real.log (routeCSaddleHalfGeometricBase delta) =
        -routeCSaddleEntropyGap delta - Real.log 2 -
          Real.log (1 / 2 - routeCSaddleHalfEntropyEpsilon delta) := by
    unfold routeCSaddleHalfGeometricBase
    rw [Real.log_div (Real.exp_ne_zero _)
      (mul_ne_zero (by norm_num) hb.ne')]
    rw [Real.log_exp, Real.log_mul (by norm_num) hb.ne']
    ring
  apply Real.log_injOn_pos
  · exact Set.mem_Ioi.mpr hleft
  · exact Set.mem_Ioi.mpr hright
  rw [Real.log_div
    (mul_ne_zero (pow_ne_zero 2 hpref.ne') hfactor.ne')
    (pow_ne_zero 2 hscale.ne')]
  rw [Real.log_mul (pow_ne_zero 2 hpref.ne') hfactor.ne']
  rw [Real.log_pow, Real.log_pow, hlogpref, hlogfactor, hlogscale]
  rw [Real.log_mul (mul_ne_zero hconstant.ne' hscaled.ne')
    (pow_ne_zero _ hrho.ne')]
  rw [Real.log_mul hconstant.ne' hscaled.ne']
  rw [Real.log_pow, hlogconstant, hlogscaled, hlogrho]
  ring

theorem linear_mul_halfGeometricBase_tendsto_zero
    {delta : ℝ} (hd0 : 0 < delta) (hd1 : delta < 1) :
    Tendsto (fun n : ℕ =>
      (n + 1 : ℝ) * routeCSaddleHalfGeometricBase delta ^ n)
      atTop (nhds 0) := by
  let rho := routeCSaddleHalfGeometricBase delta
  let r := -Real.log rho
  have hrho0 : 0 < rho := routeCSaddleHalfGeometricBase_pos hd0 hd1
  have hrho1 : rho < 1 := routeCSaddleHalfGeometricBase_lt_one hd0 hd1
  have hr : 0 < r := neg_pos.mpr (Real.log_neg hrho0 hrho1)
  have hsummable := Real.summable_pow_mul_exp_neg_nat_mul 1 hr
  have hlinear : Tendsto (fun n : ℕ => (n : ℝ) * rho ^ n)
      atTop (nhds 0) := by
    have hzero := hsummable.tendsto_atTop_zero
    convert hzero using 1
    ext n
    rw [show -r * (n : ℝ) = Real.log rho * (n : ℝ) by
      dsimp [r]
      ring]
    rw [mul_comm (Real.log rho) (n : ℝ), Real.exp_nat_mul,
      Real.exp_log hrho0]
    simp
  have hgeometric : Tendsto (fun n : ℕ => rho ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hrho0.le hrho1
  simpa only [rho, Nat.cast_add, Nat.cast_one, add_mul, one_mul, zero_add] using
    hlinear.add hgeometric

theorem factorial_majorant_normalized_tendsto_zero
    (A : ℂ) {delta : ℝ} (hd0 : 0 < delta) (hd1 : delta < 1) :
    Tendsto (fun n : ℕ =>
      (routeCSaddleHalfGammaPrefactor A delta
            (routeCSaddleHalfEntropyEpsilon delta) n ^ 2 *
          (((n + 1).factorial : ℝ) *
            Real.rpow 2 (-((n : ℝ) + 1)) * Real.sqrt Real.pi)) /
        routeCSaddlePrincipalScaleOne n ^ 2)
      atTop (nhds 0) := by
  let C := routeCSaddleHalfNormalizationConstant A delta *
    Stirling.stirlingSeq 1 * Real.exp 2
  have hupper : Tendsto (fun n : ℕ =>
      C * ((n + 1 : ℝ) * routeCSaddleHalfGeometricBase delta ^ n))
      atTop (nhds 0) := by
    simpa only [C, mul_zero] using
      (linear_mul_halfGeometricBase_tendsto_zero hd0 hd1).const_mul C
  apply squeeze_zero'
    (g := fun n : ℕ =>
      C * ((n + 1 : ℝ) * routeCSaddleHalfGeometricBase delta ^ n))
  · filter_upwards with n
    exact div_nonneg
      (mul_nonneg (sq_nonneg _)
        (mul_nonneg
          (mul_nonneg (Nat.cast_nonneg _)
            (Real.rpow_nonneg (by norm_num) _))
          (Real.sqrt_nonneg _)))
      (sq_nonneg _)
  · filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
    rw [factorial_majorant_normalized_eq A delta n hn hd0 hd1]
    have hscaled := factorial_scaled_le_linear n hn
    have hconstant : 0 ≤ routeCSaddleHalfNormalizationConstant A delta := by
      unfold routeCSaddleHalfNormalizationConstant
      positivity
    have hrho : 0 ≤ routeCSaddleHalfGeometricBase delta ^ n :=
      pow_nonneg (routeCSaddleHalfGeometricBase_pos hd0 hd1).le _
    calc
      routeCSaddleHalfNormalizationConstant A delta *
            (Real.exp (n : ℝ) * ((n + 1).factorial : ℝ) /
              Real.rpow n ((n : ℝ) + 1)) *
            routeCSaddleHalfGeometricBase delta ^ n
          ≤ routeCSaddleHalfNormalizationConstant A delta *
              (Stirling.stirlingSeq 1 * Real.exp 2 * (n + 1 : ℝ)) *
              routeCSaddleHalfGeometricBase delta ^ n :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hscaled hconstant) hrho
      _ = C * ((n + 1 : ℝ) * routeCSaddleHalfGeometricBase delta ^ n) := by
        dsimp [C]
        ring
  · exact hupper

/-- The genuine far-sector integral is negligible in squared norm after
division by the real principal saddle scale. -/
theorem norm_routeCSaddleFarIntegral_one_sq_normalized_tendsto_zero
    (A : ℂ) {delta : ℝ} (hd0 : 0 < delta) (hd1 : delta < 1) :
    Tendsto (fun n : ℕ =>
      ‖routeCSaddleFarIntegral A 1 delta n‖ ^ 2 /
        routeCSaddlePrincipalScaleOne n ^ 2)
      atTop (nhds 0) := by
  apply squeeze_zero'
    (g := fun n : ℕ =>
      (routeCSaddleHalfGammaPrefactor A delta
            (routeCSaddleHalfEntropyEpsilon delta) n ^ 2 *
          (((n + 1).factorial : ℝ) *
            Real.rpow 2 (-((n : ℝ) + 1)) * Real.sqrt Real.pi)) /
        routeCSaddlePrincipalScaleOne n ^ 2)
  · filter_upwards with n
    exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  · filter_upwards [eventually_atTop.2 ⟨2, fun _ hn => hn⟩] with n hn
    exact div_le_div_of_nonneg_right
      (norm_routeCSaddleFarIntegral_one_sq_le_factorial A delta
        (routeCSaddleHalfEntropyEpsilon delta) n hn hd0 hd1
        (routeCSaddleHalfEntropyEpsilon_pos hd0 hd1)
        (routeCSaddleHalfEntropyEpsilon_lt_half hd0 hd1))
      (sq_nonneg _)
  · exact factorial_majorant_normalized_tendsto_zero A hd0 hd1

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleFarLimit
