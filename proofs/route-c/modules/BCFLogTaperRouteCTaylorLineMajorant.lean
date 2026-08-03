import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorFEFactor
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZeroVerticalMajorant

/-!
# Route C: majorants on the finite Taylor remainder lines

This module assembles the exact discrete functional-equation calculation,
the full sine denominator, and the principal-power sector bound for the
literal `g₀` integrand.  The output is an explicit polynomial-exponential
majorant on every line `Re s = 1/2-n`.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorLineMajorant

open Complex MeasureTheory
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelRightLine
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCGammaShiftedLines
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZero
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZeroVerticalMajorant
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorFEFactor
open RH.Criteria.NymanBeurling.H14ZetaFETransport

/-- The finite polynomial which is exactly the squared norm of the
functional-equation factor on the `n`-th shifted line. -/
noncomputable def routeCTaylorFEPolynomial (n : ℕ) (t : ℝ) : ℝ :=
  2 * ((2 * Real.pi : ℝ) ^ (-((n : ℝ) + 1 / 2))) ^ 2 *
    (∏ j ∈ Finset.range n,
      (((j : ℝ) + 1 / 2) ^ 2 + t ^ 2)) * Real.pi

theorem routeCTaylorFEPolynomial_nonneg (n : ℕ) (t : ℝ) :
    0 ≤ routeCTaylorFEPolynomial n t := by
  unfold routeCTaylorFEPolynomial
  positivity

theorem shiftedQuadratic_le_dyadicPower
    (n j : ℕ) (hj : j < n) (t : ℝ) :
    ((j : ℝ) + 1 / 2) ^ 2 + t ^ 2 ≤
      ((n : ℝ) + 1) ^ 2 * (1 + |t|) ^ 2 := by
  have hjR : (j : ℝ) + 1 / 2 ≤ (n : ℝ) + 1 := by
    have hjR' : (j : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hj)
    linarith
  have hj0 : 0 ≤ (j : ℝ) + 1 / 2 := by positivity
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hn1 : 1 ≤ (n : ℝ) + 1 := by linarith
  have ht0 : 0 ≤ |t| := abs_nonneg t
  have htSq : t ^ 2 = |t| ^ 2 := by rw [sq_abs]
  rw [htSq]
  have hsum :
      (j : ℝ) + 1 / 2 + |t| ≤
        ((n : ℝ) + 1) * (1 + |t|) := by
    have hprod : 0 ≤ ((n : ℝ) + 1 - 1) * |t| :=
      mul_nonneg (by positivity) ht0
    nlinarith
  nlinarith [sq_nonneg ((j : ℝ) + 1 / 2 + |t|),
    sq_nonneg (((n : ℝ) + 1) * (1 + |t|))]

theorem shiftedQuadraticProduct_le_dyadicPower (n : ℕ) (t : ℝ) :
    (∏ j ∈ Finset.range n,
        (((j : ℝ) + 1 / 2) ^ 2 + t ^ 2)) ≤
      (((n : ℝ) + 1) ^ 2 * (1 + |t|) ^ 2) ^ n := by
  calc
    (∏ j ∈ Finset.range n,
        (((j : ℝ) + 1 / 2) ^ 2 + t ^ 2)) ≤
      ∏ _j ∈ Finset.range n,
        (((n : ℝ) + 1) ^ 2 * (1 + |t|) ^ 2) := by
          apply Finset.prod_le_prod
          · intro j _hj
            positivity
          · intro j hj
            exact shiftedQuadratic_le_dyadicPower n j
              (Finset.mem_range.mp hj) t
    _ = (((n : ℝ) + 1) ^ 2 * (1 + |t|) ^ 2) ^ n := by
      rw [Finset.prod_const, Finset.card_range]

/-- Line-dependent constant in the polynomial majorant. -/
noncomputable def routeCTaylorFEPolynomialConstant (n : ℕ) : ℝ :=
  2 * ((2 * Real.pi : ℝ) ^ (-((n : ℝ) + 1 / 2))) ^ 2 *
    (((n : ℝ) + 1) ^ 2) ^ n * Real.pi

theorem routeCTaylorFEPolynomialConstant_nonneg (n : ℕ) :
    0 ≤ routeCTaylorFEPolynomialConstant n := by
  unfold routeCTaylorFEPolynomialConstant
  positivity

theorem routeCTaylorFEPolynomial_le (n : ℕ) (t : ℝ) :
    routeCTaylorFEPolynomial n t ≤
      routeCTaylorFEPolynomialConstant n * (1 + |t|) ^ (2 * n) := by
  have hprod := shiftedQuadraticProduct_le_dyadicPower n t
  unfold routeCTaylorFEPolynomial routeCTaylorFEPolynomialConstant
  have hconstant :
      0 ≤ 2 * ((2 * Real.pi : ℝ) ^ (-((n : ℝ) + 1 / 2))) ^ 2 := by
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hprod hconstant
  have hpi := mul_le_mul_of_nonneg_right hscaled Real.pi_pos.le
  calc
    2 * ((2 * Real.pi : ℝ) ^ (-((n : ℝ) + 1 / 2))) ^ 2 *
          (∏ j ∈ Finset.range n,
            (((j : ℝ) + 1 / 2) ^ 2 + t ^ 2)) * Real.pi ≤
        2 * ((2 * Real.pi : ℝ) ^ (-((n : ℝ) + 1 / 2))) ^ 2 *
          ((((n : ℝ) + 1) ^ 2 * (1 + |t|) ^ 2) ^ n) *
            Real.pi := hpi
    _ = 2 * ((2 * Real.pi : ℝ) ^ (-((n : ℝ) + 1 / 2))) ^ 2 *
          (((n : ℝ) + 1) ^ 2) ^ n * Real.pi *
            (1 + |t|) ^ (2 * n) := by
      rw [mul_pow]
      have hpow : ((1 + |t|) ^ 2) ^ n =
          (1 + |t|) ^ (2 * n) := by
        rw [← pow_mul]
      rw [hpow]
      ring

theorem norm_zetaFEFactor_shiftedPoint_sq_eq_polynomial
    (n : ℕ) (t : ℝ) :
    ‖zetaFEFactor (routeCGammaShiftedPoint n t)‖ ^ 2 =
      routeCTaylorFEPolynomial n t := by
  exact norm_zetaFEFactor_routeCGammaShiftedPoint_sq n t

/-- A norm bound for the unreflected zeta factor which avoids introducing a
square root of the finite polynomial. -/
theorem norm_riemannZeta_shiftedPoint_le_polynomial
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : t ≠ 0) :
    ‖riemannZeta (routeCGammaShiftedPoint n t)‖ ≤
      9 * (1 + routeCTaylorFEPolynomial n t) := by
  have him : (routeCGammaShiftedPoint n t).im ≠ 0 := by
    simpa [routeCGammaShiftedPoint] using ht
  rw [riemannZeta_eq_zetaFEFactor_mul him, norm_mul]
  have href := norm_riemannZeta_one_sub_shiftedPoint_le n hn t
  have hpoly : 0 ≤ routeCTaylorFEPolynomial n t :=
    routeCTaylorFEPolynomial_nonneg n t
  have honePoly : 0 ≤ 1 + routeCTaylorFEPolynomial n t := by linarith
  have hfac :
      ‖zetaFEFactor (routeCGammaShiftedPoint n t)‖ ≤
        1 + routeCTaylorFEPolynomial n t := by
    rw [← norm_zetaFEFactor_shiftedPoint_sq_eq_polynomial]
    nlinarith [norm_nonneg
      (zetaFEFactor (routeCGammaShiftedPoint n t))]
  calc
    ‖zetaFEFactor (routeCGammaShiftedPoint n t)‖ *
        ‖riemannZeta (1 - routeCGammaShiftedPoint n t)‖ ≤
      (1 + routeCTaylorFEPolynomial n t) * 9 := by
        exact mul_le_mul hfac href (norm_nonneg _)
          honePoly
    _ = 9 * (1 + routeCTaylorFEPolynomial n t) := by ring

/-- The full sine denominator on every half-integer Taylor line has norm
`cosh(pi*t)`. -/
theorem norm_sin_pi_mul_shiftedPoint (n : ℕ) (t : ℝ) :
    ‖Complex.sin ((Real.pi : ℂ) *
      routeCGammaShiftedPoint n t)‖ =
        Real.cosh (Real.pi * t) := by
  have hdouble :
      Complex.sin ((Real.pi : ℂ) * routeCGammaShiftedPoint n t) =
        2 * Complex.sin ((Real.pi : ℂ) *
            routeCGammaShiftedPoint n t / 2) *
          Complex.cos ((Real.pi : ℂ) *
            routeCGammaShiftedPoint n t / 2) := by
    calc
      Complex.sin ((Real.pi : ℂ) * routeCGammaShiftedPoint n t) =
          Complex.sin (2 * ((Real.pi : ℂ) *
            routeCGammaShiftedPoint n t / 2)) := by
              congr 1
              ring
      _ = _ := Complex.sin_two_mul _
  have hsin := (normSq_sin_cos_taylorHalfAngle n t).1
  have hcos := (normSq_sin_cos_taylorHalfAngle n t).2
  have hsq :
      ‖Complex.sin ((Real.pi : ℂ) *
        routeCGammaShiftedPoint n t)‖ ^ 2 =
          Real.cosh (Real.pi * t) ^ 2 := by
    rw [hdouble, norm_mul, norm_mul, mul_pow, mul_pow]
    norm_num
    rw [← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq, hsin, hcos]
    ring
  nlinarith [norm_nonneg (Complex.sin ((Real.pi : ℂ) *
    routeCGammaShiftedPoint n t)), Real.cosh_pos (Real.pi * t)]

/-- The literal `g₀` integrand on a shifted Taylor line. -/
noncomputable def bettinConreyGZeroShiftedVerticalIntegrand
    (u : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  let s := routeCGammaShiftedPoint n t
  riemannZeta s * riemannZeta (1 - s) /
      Complex.sin ((Real.pi : ℂ) * s) * u ^ (-s)

theorem bettinConreyGZeroShiftedVerticalIntegrand_one
    (u : ℂ) (t : ℝ) :
    bettinConreyGZeroShiftedVerticalIntegrand u 1 t =
      bettinConreyGZeroVerticalIntegrand u t := by
  unfold bettinConreyGZeroShiftedVerticalIntegrand
    bettinConreyGZeroVerticalIntegrand
    routeCGammaShiftedPoint bettinConreyCentralVerticalPoint
  congr 1 <;> push_cast <;> ring

/-- Explicit majorant before replacing the finite product by a single
power of `1+|t|`. -/
noncomputable def routeCTaylorLineMajorant
    (u : ℂ) (n : ℕ) (θ : ℝ) (t : ℝ) : ℝ :=
  162 * ‖u‖ ^ ((n : ℝ) - 1 / 2) *
    (1 + routeCTaylorFEPolynomial n t) *
      Real.exp (-(Real.pi - θ) * |t|)

theorem routeCTaylorLineMajorant_nonneg
    (u : ℂ) (n : ℕ) (θ t : ℝ) :
    0 ≤ routeCTaylorLineMajorant u n θ t := by
  unfold routeCTaylorLineMajorant
  have hpoly := routeCTaylorFEPolynomial_nonneg n t
  positivity

/-- Constant which converts the exact finite-product majorant into the
standard polynomial-exponential profile. -/
noncomputable def routeCTaylorLineMajorantConstant
    (u : ℂ) (n : ℕ) : ℝ :=
  162 * ‖u‖ ^ ((n : ℝ) - 1 / 2) *
    (1 + routeCTaylorFEPolynomialConstant n)

theorem routeCTaylorLineMajorant_le_standard
    (u : ℂ) (n : ℕ) (θ t : ℝ) :
    routeCTaylorLineMajorant u n θ t ≤
      routeCTaylorLineMajorantConstant u n *
        abelPolynomialExponentialMajorant (2 * n)
          (Real.pi - θ) t := by
  have hpoly := routeCTaylorFEPolynomial_le n t
  have hC := routeCTaylorFEPolynomialConstant_nonneg n
  have hbase : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hpow : 1 ≤ (1 + |t|) ^ (2 * n) := one_le_pow₀ hbase
  have hsum :
      1 + routeCTaylorFEPolynomial n t ≤
        (1 + routeCTaylorFEPolynomialConstant n) *
          (1 + |t|) ^ (2 * n) := by
    calc
      1 + routeCTaylorFEPolynomial n t ≤
          (1 + |t|) ^ (2 * n) +
            routeCTaylorFEPolynomialConstant n *
              (1 + |t|) ^ (2 * n) := add_le_add hpow hpoly
      _ = (1 + routeCTaylorFEPolynomialConstant n) *
            (1 + |t|) ^ (2 * n) := by ring
  unfold routeCTaylorLineMajorant routeCTaylorLineMajorantConstant
    abelPolynomialExponentialMajorant
  have hradial :
      0 ≤ 162 * ‖u‖ ^ ((n : ℝ) - 1 / 2) := by positivity
  calc
    162 * ‖u‖ ^ ((n : ℝ) - 1 / 2) *
          (1 + routeCTaylorFEPolynomial n t) *
          Real.exp (-(Real.pi - θ) * |t|) ≤
        162 * ‖u‖ ^ ((n : ℝ) - 1 / 2) *
          ((1 + routeCTaylorFEPolynomialConstant n) *
            (1 + |t|) ^ (2 * n)) *
          Real.exp (-(Real.pi - θ) * |t|) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsum hradial) (Real.exp_pos _).le
    _ = 162 * ‖u‖ ^ ((n : ℝ) - 1 / 2) *
          (1 + routeCTaylorFEPolynomialConstant n) *
          ((1 + |t|) ^ (2 * n) *
            Real.exp (-(Real.pi - θ) * |t|)) := by ring

/-- Every finite Taylor remainder line has an integrable intrinsic
majorant on a sector of aperture strictly below `pi`. -/
theorem integrable_routeCTaylorLineMajorant
    (u : ℂ) (n : ℕ) (θ : ℝ) (hθ : θ < Real.pi) :
    Integrable (routeCTaylorLineMajorant u n θ) := by
  have hstandard : Integrable (fun t : ℝ =>
      routeCTaylorLineMajorantConstant u n *
        abelPolynomialExponentialMajorant (2 * n)
          (Real.pi - θ) t) :=
    (integrable_abelPolynomialExponentialMajorant (2 * n)
      (sub_pos.mpr hθ)).const_mul _
  apply Integrable.mono' hstandard
  · have hcont : Continuous (routeCTaylorLineMajorant u n θ) := by
      unfold routeCTaylorLineMajorant routeCTaylorFEPolynomial
      fun_prop
    exact hcont.aestronglyMeasurable
  · filter_upwards [] with t
    rw [Real.norm_eq_abs,
      abs_of_nonneg (routeCTaylorLineMajorant_nonneg u n θ t)]
    exact routeCTaylorLineMajorant_le_standard u n θ t

/-- Pointwise shifted-line domination.  The only excluded height is the
measure-zero point required by the current zeta functional-equation API. -/
theorem norm_bettinConreyGZeroShiftedVerticalIntegrand_le
    (u : ℂ) (hu : u ≠ 0) (n : ℕ) (hn : 1 ≤ n)
    (θ t : ℝ) (harg : |Complex.arg u| ≤ θ) (ht : t ≠ 0) :
    ‖bettinConreyGZeroShiftedVerticalIntegrand u n t‖ ≤
      routeCTaylorLineMajorant u n θ t := by
  have hzleft := norm_riemannZeta_shiftedPoint_le_polynomial n hn t ht
  have hzright := norm_riemannZeta_one_sub_shiftedPoint_le n hn t
  have hpower := norm_cpow_neg_routeCGammaShiftedPoint_le
    u hu n t θ harg
  have hcosh := one_div_cosh_pi_mul_le_exp t
  have hpoly : 0 ≤ routeCTaylorFEPolynomial n t :=
    routeCTaylorFEPolynomial_nonneg n t
  have honePoly : 0 ≤ 1 + routeCTaylorFEPolynomial n t := by linarith
  have hleftBound : 0 ≤ 9 * (1 + routeCTaylorFEPolynomial n t) * 9 := by
    positivity
  have hpowerBound :
      0 ≤ ‖u‖ ^ ((n : ℝ) - 1 / 2) * Real.exp (θ * |t|) := by
    positivity
  unfold bettinConreyGZeroShiftedVerticalIntegrand
  dsimp only
  rw [norm_mul, norm_div, norm_mul,
    norm_sin_pi_mul_shiftedPoint]
  have hfirst :
      ‖riemannZeta (routeCGammaShiftedPoint n t)‖ *
          ‖riemannZeta (1 - routeCGammaShiftedPoint n t)‖ /
            Real.cosh (Real.pi * t) *
          ‖u ^ (-routeCGammaShiftedPoint n t)‖ ≤
        (9 * (1 + routeCTaylorFEPolynomial n t) * 9) *
          (1 / Real.cosh (Real.pi * t)) *
          (‖u‖ ^ ((n : ℝ) - 1 / 2) *
            Real.exp (θ * |t|)) := by
    have hnum :
        ‖riemannZeta (routeCGammaShiftedPoint n t)‖ *
            ‖riemannZeta (1 - routeCGammaShiftedPoint n t)‖ ≤
          9 * (1 + routeCTaylorFEPolynomial n t) * 9 :=
      mul_le_mul hzleft hzright (norm_nonneg _)
        (mul_nonneg (by norm_num) honePoly)
    have hquot :
        (‖riemannZeta (routeCGammaShiftedPoint n t)‖ *
              ‖riemannZeta (1 - routeCGammaShiftedPoint n t)‖) *
            (Real.cosh (Real.pi * t))⁻¹ ≤
          (9 * (1 + routeCTaylorFEPolynomial n t) * 9) *
            (Real.cosh (Real.pi * t))⁻¹ :=
      mul_le_mul_of_nonneg_right hnum
        (inv_nonneg.mpr (Real.cosh_pos (Real.pi * t)).le)
    have hout := mul_le_mul hquot hpower (norm_nonneg _)
      (mul_nonneg hleftBound
        (inv_nonneg.mpr (Real.cosh_pos (Real.pi * t)).le))
    simpa only [div_eq_mul_inv, one_mul] using hout
  calc
    ‖riemannZeta (routeCGammaShiftedPoint n t)‖ *
          ‖riemannZeta (1 - routeCGammaShiftedPoint n t)‖ /
            Real.cosh (Real.pi * t) *
          ‖u ^ (-routeCGammaShiftedPoint n t)‖ ≤
        (9 * (1 + routeCTaylorFEPolynomial n t) * 9) *
          (1 / Real.cosh (Real.pi * t)) *
          (‖u‖ ^ ((n : ℝ) - 1 / 2) *
            Real.exp (θ * |t|)) := hfirst
    _ ≤ (9 * (1 + routeCTaylorFEPolynomial n t) * 9) *
          (2 * Real.exp (-(Real.pi * |t|))) *
          (‖u‖ ^ ((n : ℝ) - 1 / 2) *
            Real.exp (θ * |t|)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcosh hleftBound) hpowerBound
    _ = routeCTaylorLineMajorant u n θ t := by
      unfold routeCTaylorLineMajorant
      have hexp :
          Real.exp (-(Real.pi * |t|)) * Real.exp (θ * |t|) =
            Real.exp (-(Real.pi - θ) * |t|) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        9 * (1 + routeCTaylorFEPolynomial n t) * 9 *
              (2 * Real.exp (-(Real.pi * |t|))) *
              (‖u‖ ^ ((n : ℝ) - 1 / 2) * Real.exp (θ * |t|)) =
            162 * ‖u‖ ^ ((n : ℝ) - 1 / 2) *
              (1 + routeCTaylorFEPolynomial n t) *
              (Real.exp (-(Real.pi * |t|)) *
                Real.exp (θ * |t|)) := by ring
        _ = 162 * ‖u‖ ^ ((n : ℝ) - 1 / 2) *
              (1 + routeCTaylorFEPolynomial n t) *
              Real.exp (-(Real.pi - θ) * |t|) := by rw [hexp]

theorem continuous_bettinConreyGZeroShiftedVerticalIntegrand
    (u : ℂ) (hu : u ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    Continuous (bettinConreyGZeroShiftedVerticalIntegrand u n) := by
  let s : ℝ → ℂ := fun t => routeCGammaShiftedPoint n t
  have hs : Continuous s := by
    dsimp [s, routeCGammaShiftedPoint]
    fun_prop
  have hs_ne_one : ∀ t : ℝ, s t ≠ 1 := by
    intro t h
    have hre := congrArg Complex.re h
    simp [s, routeCGammaShiftedPoint] at hre
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hone_sub_ne_one : ∀ t : ℝ, 1 - s t ≠ 1 := by
    intro t h
    have hre := congrArg Complex.re h
    simp [s, routeCGammaShiftedPoint] at hre
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hzleft : Continuous (fun t : ℝ => riemannZeta (s t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (differentiableAt_riemannZeta (hs_ne_one t)).continuousAt.comp
      hs.continuousAt
  have hrightArg : Continuous (fun t : ℝ => 1 - s t) :=
    continuous_const.sub hs
  have hzright : Continuous (fun t : ℝ => riemannZeta (1 - s t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact ContinuousAt.comp' (f := fun t : ℝ => 1 - s t)
      (g := riemannZeta)
      (differentiableAt_riemannZeta
        (hone_sub_ne_one t)).continuousAt hrightArg.continuousAt
  have hsin : Continuous (fun t : ℝ =>
      Complex.sin ((Real.pi : ℂ) * s t)) := by
    fun_prop
  have hsin_ne : ∀ t : ℝ,
      Complex.sin ((Real.pi : ℂ) * s t) ≠ 0 := by
    intro t hzero
    have hnorm := norm_sin_pi_mul_shiftedPoint n t
    change ‖Complex.sin ((Real.pi : ℂ) * s t)‖ =
      Real.cosh (Real.pi * t) at hnorm
    rw [hzero, norm_zero] at hnorm
    linarith [Real.cosh_pos (Real.pi * t)]
  have hpower : Continuous (fun t : ℝ => u ^ (-(s t))) :=
    hs.neg.const_cpow (Or.inl hu)
  unfold bettinConreyGZeroShiftedVerticalIntegrand
  dsimp only
  exact (hzleft.mul hzright).div hsin hsin_ne |>.mul hpower

/-- The actual shifted `g₀` line is integrable.  The pointwise estimate uses
the functional equation away from `t=0`; the excluded singleton is null. -/
theorem integrable_bettinConreyGZeroShiftedVerticalIntegrand
    (u : ℂ) (hu : u ≠ 0) (n : ℕ) (hn : 1 ≤ n)
    (θ : ℝ) (harg : |Complex.arg u| ≤ θ) (hθ : θ < Real.pi) :
    Integrable (bettinConreyGZeroShiftedVerticalIntegrand u n) := by
  have hmajor := integrable_routeCTaylorLineMajorant u n θ hθ
  apply Integrable.mono' hmajor
  · exact (continuous_bettinConreyGZeroShiftedVerticalIntegrand
      u hu n hn).aestronglyMeasurable
  · have hne : ∀ᵐ t : ℝ, t ≠ 0 := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne] with t ht
    exact norm_bettinConreyGZeroShiftedVerticalIntegrand_le
      u hu n hn θ t harg ht

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorLineMajorant
