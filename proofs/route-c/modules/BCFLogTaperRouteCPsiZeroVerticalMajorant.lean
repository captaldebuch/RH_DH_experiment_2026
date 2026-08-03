import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZeroContinuity
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCAbelRightLine
import RiemannHypothesis.Criteria.NymanBeurling.H14FEFactorBound

/-!
# Route C: intrinsic vertical decay of the central period integrand

On `s = -1/2 + i t`, the functional equation gives linear growth for the
left zeta factor, while the denominator is exactly `-cosh (pi*t)`.  Their
combination is therefore bounded by a polynomial times `exp (-pi*|t|)`.
This is the spectral half of the local majorant required for continuity of
the literal Bettin--Conrey period.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZeroVerticalMajorant

open Complex MeasureTheory
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelMellin
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelRightLine
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZero
open RH.Criteria.NymanBeurling.H14ZetaFETransport

/-- The zeta/sine part of the central vertical integrand, before the
geometric factor `z^(-s)`. -/
noncomputable def bettinConreyCentralSpectralKernel (t : ℝ) : ℂ :=
  let s := bettinConreyCentralVerticalPoint t
  riemannZeta s * riemannZeta (1 - s) /
    Complex.sin ((Real.pi : ℂ) * s)

/-- On the central line the sine denominator is the real number
`-cosh(pi*t)`. -/
theorem sin_bettinConreyCentralVerticalPoint (t : ℝ) :
    Complex.sin
        ((Real.pi : ℂ) * bettinConreyCentralVerticalPoint t) =
      -(Real.cosh (Real.pi * t) : ℂ) := by
  rw [show
      (Real.pi : ℂ) * bettinConreyCentralVerticalPoint t =
        ((-(Real.pi / 2) : ℝ) : ℂ) +
          ((Real.pi * t : ℝ) : ℂ) * I by
    unfold bettinConreyCentralVerticalPoint
    push_cast
    ring,
    Complex.sin_add_mul_I]
  simp

/-- Reciprocal hyperbolic cosine has the precise two-sided exponential
decay needed below. -/
theorem one_div_cosh_pi_mul_le_exp (t : ℝ) :
    1 / Real.cosh (Real.pi * t) ≤
      2 * Real.exp (-(Real.pi * |t|)) := by
  have hcosh : 0 < Real.cosh (Real.pi * t) := Real.cosh_pos _
  have hexp : 0 < Real.exp (Real.pi * |t|) := Real.exp_pos _
  have habs : |Real.pi * t| = Real.pi * |t| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
  have hcoshLower : Real.exp (Real.pi * |t|) ≤
      2 * Real.cosh (Real.pi * t) := by
    rw [← habs]
    exact exp_abs_le_two_mul_cosh (Real.pi * t)
  rw [Real.exp_neg]
  apply (div_le_iff₀ hcosh).2
  calc
    1 = (Real.exp (Real.pi * |t|))⁻¹ *
        Real.exp (Real.pi * |t|) := by
          rw [inv_mul_cancel₀ hexp.ne']
    _ ≤ (Real.exp (Real.pi * |t|))⁻¹ *
        (2 * Real.cosh (Real.pi * t)) :=
      mul_le_mul_of_nonneg_left hcoshLower (inv_nonneg.mpr hexp.le)
    _ = 2 * (Real.exp (Real.pi * |t|))⁻¹ *
        Real.cosh (Real.pi * t) := by ring

/-- The right zeta factor lies on `Re(s)=3/2`, where the absolutely
convergent Dirichlet series gives the uniform project bound `9`. -/
theorem norm_riemannZeta_one_sub_central_le (t : ℝ) :
    ‖riemannZeta (1 - bettinConreyCentralVerticalPoint t)‖ ≤ 9 := by
  apply norm_riemannZeta_le_of_re_ge
  simp [bettinConreyCentralVerticalPoint]
  norm_num

/-- The functional equation transports the right-line bound to a linear
bound on the left central line. -/
theorem norm_riemannZeta_central_le
    (t : ℝ) (ht : t ≠ 0) :
    ‖riemannZeta (bettinConreyCentralVerticalPoint t)‖ ≤
      9 * (1 + |t|) := by
  have him : (bettinConreyCentralVerticalPoint t).im ≠ 0 := by
    simpa [bettinConreyCentralVerticalPoint] using ht
  rw [riemannZeta_eq_zetaFEFactor_mul him, norm_mul]
  have hfactor := zetaFEFactor_minus_half_norm ht
  have hright := norm_riemannZeta_one_sub_central_le t
  have hpoint :
      bettinConreyCentralVerticalPoint t =
        (-(1 / 2 : ℝ) + Complex.I * t : ℂ) := by
    unfold bettinConreyCentralVerticalPoint
    push_cast
    ring
  rw [hpoint, hfactor]
  have hright' :
      ‖riemannZeta
          (1 - (-(1 / 2 : ℝ) + Complex.I * t : ℂ))‖ ≤ 9 := by
    rw [← hpoint]
    exact hright
  have hnorm : ‖(1 / 2 : ℝ) - Complex.I * t‖ ≤ 1 + |t| := by
    calc
      ‖(1 / 2 : ℝ) - Complex.I * t‖ ≤
          ‖((1 / 2 : ℝ) : ℂ)‖ +
            ‖Complex.I * (t : ℂ)‖ := by
              exact norm_sub_le _ _
      _ = 1 / 2 + |t| := by
        simp [Real.norm_eq_abs]
      _ ≤ 1 + |t| := by linarith
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hquot :
      ‖(1 / 2 : ℝ) - Complex.I * t‖ / (2 * Real.pi) ≤
        1 + |t| := by
    exact (div_le_self (norm_nonneg _) hpi).trans hnorm
  calc
    ‖(1 / 2 : ℝ) - Complex.I * t‖ / (2 * Real.pi) *
          ‖riemannZeta
            (1 - (-(1 / 2 : ℝ) + Complex.I * t : ℂ))‖ ≤
        (1 + |t|) * 9 :=
      mul_le_mul hquot hright' (norm_nonneg _) (by positivity)
    _ = 9 * (1 + |t|) := by ring

/-- The spectral kernel has unconditional polynomial-exponential decay away
from the compact central segment. -/
theorem norm_bettinConreyCentralSpectralKernel_le
    (t : ℝ) (ht : 1 ≤ |t|) :
    ‖bettinConreyCentralSpectralKernel t‖ ≤
      162 * (1 + |t|) * Real.exp (-(Real.pi * |t|)) := by
  have ht0 : t ≠ 0 := by
    exact abs_pos.mp (lt_of_lt_of_le zero_lt_one ht)
  have hleft := norm_riemannZeta_central_le t ht0
  have hright := norm_riemannZeta_one_sub_central_le t
  have hsin :
      ‖Complex.sin
          ((Real.pi : ℂ) * bettinConreyCentralVerticalPoint t)‖ =
        Real.cosh (Real.pi * t) := by
    rw [sin_bettinConreyCentralVerticalPoint, norm_neg,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.cosh_pos _)]
  unfold bettinConreyCentralSpectralKernel
  dsimp only
  rw [norm_div, norm_mul, hsin]
  calc
    ‖riemannZeta (bettinConreyCentralVerticalPoint t)‖ *
          ‖riemannZeta (1 - bettinConreyCentralVerticalPoint t)‖ /
          Real.cosh (Real.pi * t) ≤
        (9 * (1 + |t|) * 9) /
          Real.cosh (Real.pi * t) := by
      apply div_le_div_of_nonneg_right _ (Real.cosh_pos _).le
      exact mul_le_mul hleft hright (norm_nonneg _) (by positivity)
    _ = 81 * (1 + |t|) *
        (1 / Real.cosh (Real.pi * t)) := by ring
    _ ≤ 81 * (1 + |t|) *
        (2 * Real.exp (-(Real.pi * |t|))) := by
      exact mul_le_mul_of_nonneg_left (one_div_cosh_pi_mul_le_exp t)
        (by positivity)
    _ = 162 * (1 + |t|) *
        Real.exp (-(Real.pi * |t|)) := by ring

/-- The compact central segment causes no singularity: both zeta factors are
away from their pole and the sine denominator is a nonzero hyperbolic
cosine. -/
theorem continuous_bettinConreyCentralSpectralKernel :
    Continuous bettinConreyCentralSpectralKernel := by
  rw [continuous_iff_continuousAt]
  intro t
  let s : ℝ → ℂ := fun u ↦ bettinConreyCentralVerticalPoint u
  have hs : ContinuousAt s t := by
    dsimp [s, bettinConreyCentralVerticalPoint]
    fun_prop
  have hs_ne_one : s t ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [s, bettinConreyCentralVerticalPoint] at hre
  have hone_sub_ne_one : 1 - s t ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [s, bettinConreyCentralVerticalPoint] at hre
  have hzetaLeft : ContinuousAt (fun u : ℝ ↦ riemannZeta (s u)) t :=
    (differentiableAt_riemannZeta hs_ne_one).continuousAt.comp hs
  have honeSub : ContinuousAt (fun u : ℝ ↦ 1 - s u) t := by
    fun_prop
  have hzetaRightAt : ContinuousAt riemannZeta (1 - s t) :=
    (differentiableAt_riemannZeta
      (s := 1 - s t) hone_sub_ne_one).continuousAt
  have hzetaRight : ContinuousAt
      (fun u : ℝ ↦ riemannZeta (1 - s u)) t := by
    exact ContinuousAt.comp' (f := fun u : ℝ ↦ 1 - s u)
      (g := riemannZeta) hzetaRightAt honeSub
  have hsin : ContinuousAt
      (fun u : ℝ ↦ Complex.sin ((Real.pi : ℂ) * s u)) t := by
    fun_prop
  have hsin0 : Complex.sin ((Real.pi : ℂ) * s t) ≠ 0 := by
    rw [show s t = bettinConreyCentralVerticalPoint t by rfl,
      sin_bettinConreyCentralVerticalPoint]
    exact neg_ne_zero.mpr
      (ofReal_ne_zero.mpr (Real.cosh_pos _).ne')
  unfold bettinConreyCentralSpectralKernel
  dsimp only
  exact (hzetaLeft.mul hzetaRight).div hsin hsin0

/-- For every fixed right-half-plane point, the complete vertical integrand
is a continuous function of the spectral parameter. -/
theorem continuous_bettinConreyGZeroVerticalIntegrand
    (z : ℂ) (hz : 0 < z.re) :
    Continuous (fun t : ℝ ↦ bettinConreyGZeroVerticalIntegrand z t) := by
  rw [continuous_iff_continuousAt]
  intro t
  let s : ℝ → ℂ := fun u ↦ bettinConreyCentralVerticalPoint u
  have hs : ContinuousAt s t := by
    dsimp [s, bettinConreyCentralVerticalPoint]
    fun_prop
  have hs_ne_one : s t ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [s, bettinConreyCentralVerticalPoint] at hre
  have hone_sub_ne_one : 1 - s t ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [s, bettinConreyCentralVerticalPoint] at hre
  have hzetaLeft : ContinuousAt (fun u : ℝ ↦ riemannZeta (s u)) t :=
    (differentiableAt_riemannZeta hs_ne_one).continuousAt.comp hs
  have honeSub : ContinuousAt (fun u : ℝ ↦ 1 - s u) t := by
    fun_prop
  have hzetaRightAt : ContinuousAt riemannZeta (1 - s t) :=
    (differentiableAt_riemannZeta
      (s := 1 - s t) hone_sub_ne_one).continuousAt
  have hzetaRight : ContinuousAt
      (fun u : ℝ ↦ riemannZeta (1 - s u)) t := by
    exact ContinuousAt.comp' (f := fun u : ℝ ↦ 1 - s u)
      (g := riemannZeta) hzetaRightAt honeSub
  have hsin : ContinuousAt
      (fun u : ℝ ↦ Complex.sin ((Real.pi : ℂ) * s u)) t := by
    fun_prop
  have hsin0 : Complex.sin ((Real.pi : ℂ) * s t) ≠ 0 := by
    rw [show s t = bettinConreyCentralVerticalPoint t by rfl,
      sin_bettinConreyCentralVerticalPoint]
    exact neg_ne_zero.mpr
      (ofReal_ne_zero.mpr (Real.cosh_pos _).ne')
  have hz0 : z ≠ 0 := ne_of_apply_ne Complex.re hz.ne'
  have hpow : ContinuousAt (fun u : ℝ ↦ z ^ (-(s u))) t :=
    (continuousAt_const_cpow hz0).comp (by fun_prop)
  unfold bettinConreyGZeroVerticalIntegrand
  dsimp only
  exact ((hzetaLeft.mul hzetaRight).div hsin hsin0).mul hpow

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZeroVerticalMajorant
