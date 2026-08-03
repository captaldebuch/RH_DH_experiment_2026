import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZeroLocalMajorant
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorAnalytic

/-!
# Route C: holomorphy of the central period

The Taylor proof needs more than the previously established continuity of
`psi_0`.  This module differentiates the defining Mellin integral under the
integral sign.  The derivative costs one factor `1 + |t|` and one locally
bounded reciprocal power of the geometric variable; intrinsic
`exp (-pi*|t|)` decay still makes the resulting majorant integrable.

Consequently the literal contour-defined `g_0` and `psi_0` are holomorphic
throughout the right half-plane.  This is the analytic-regularity half of
the Taylor argument; the separate finite contour shift at the origin remains
the coefficient-value calculation.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZeroHolomorphic

open Complex Filter MeasureTheory Set Topology
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelRightLine
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZero
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZeroContinuity
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZeroLocalMajorant
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZeroVerticalMajorant
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorAnalytic

/-- Pointwise derivative of the vertical `g_0` integrand in its geometric
variable. -/
noncomputable def bettinConreyGZeroVerticalDerivativeIntegrand
    (z : ℂ) (t : ℝ) : ℂ :=
  let s := bettinConreyCentralVerticalPoint t
  bettinConreyCentralSpectralKernel t *
    ((-s) * z ^ (-s - 1))

theorem hasDerivAt_bettinConreyGZeroVerticalIntegrand
    (z : ℂ) (t : ℝ) (hz : 0 < z.re) :
    HasDerivAt
      (fun w : ℂ => bettinConreyGZeroVerticalIntegrand w t)
      (bettinConreyGZeroVerticalDerivativeIntegrand z t) z := by
  have hzslit : z ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    exact Or.inl hz
  let s := bettinConreyCentralVerticalPoint t
  have hp := (hasDerivAt_id z).cpow_const (c := -s) hzslit
  have hmul := (hasDerivAt_const z
    (bettinConreyCentralSpectralKernel t)).mul hp
  change HasDerivAt
    (fun w : ℂ =>
      bettinConreyCentralSpectralKernel t * w ^ (-s))
    (bettinConreyCentralSpectralKernel t *
      ((-s) * z ^ (-s - 1))) z
  simpa [mul_assoc] using hmul

/-- A local bound for the reciprocal factor introduced by differentiation. -/
noncomputable def psiZeroLocalInverseConstant (z : ℂ) : ℝ :=
  2 / ‖z‖

theorem psiZeroLocalInverseConstant_nonneg (z : ℂ) :
    0 ≤ psiZeroLocalInverseConstant z := by
  unfold psiZeroLocalInverseConstant
  positivity

theorem eventually_norm_inv_le_psiZeroLocalInverseConstant
    (z : ℂ) (hz : 0 < z.re) :
    ∀ᶠ w in nhds z, ‖w⁻¹‖ ≤ psiZeroLocalInverseConstant z := by
  have hz0 : z ≠ 0 := ne_of_apply_ne Complex.re hz.ne'
  have hznorm : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hnormCont : ContinuousAt (fun w : ℂ => ‖w‖) z :=
    continuous_norm.continuousAt
  have hlower : ∀ᶠ w : ℂ in nhds z, ‖z‖ / 2 < ‖w‖ :=
    continuousAt_const.eventually_lt hnormCont (by linarith)
  filter_upwards [hlower] with w hw
  have hwpos : 0 < ‖w‖ := lt_of_le_of_lt (by positivity) hw
  rw [norm_inv, inv_eq_one_div]
  unfold psiZeroLocalInverseConstant
  apply (div_le_div_iff₀ hwpos hznorm).2
  nlinarith

theorem norm_bettinConreyCentralVerticalPoint_le (t : ℝ) :
    ‖bettinConreyCentralVerticalPoint t‖ ≤ 1 + |t| := by
  unfold bettinConreyCentralVerticalPoint
  calc
    ‖-(1 : ℂ) / 2 + (t : ℂ) * I‖ ≤
        ‖-(1 : ℂ) / 2‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
    _ = (1 / 2 : ℝ) + |t| := by norm_num [Real.norm_eq_abs]
    _ ≤ 1 + |t| := by linarith

/-- The derivative majorant is just one more polynomial factor times the
already proved local majorant. -/
noncomputable def psiZeroLocalDerivativeMajorant
    (z : ℂ) (t : ℝ) : ℝ :=
  psiZeroLocalInverseConstant z * (1 + |t|) *
    psiZeroLocalMajorant z t

theorem psiZeroLocalDerivativeMajorant_integrable
    (z : ℂ) (hz : 0 < z.re) :
    Integrable (psiZeroLocalDerivativeMajorant z) := by
  let C : ℝ := psiZeroLocalInverseConstant z
  let R : ℝ := psiZeroLocalRadialConstant z
  let θ : ℝ := psiZeroLocalAngle z
  let compact : ℝ → ℝ :=
    (Icc (-1 : ℝ) 1).indicator
      (fun t : ℝ =>
        C * (1 + |t|) *
          (R * Real.exp θ *
            ‖bettinConreyCentralSpectralKernel t‖))
  have hcompactContinuous : Continuous
      (fun t : ℝ =>
        C * (1 + |t|) *
          (R * Real.exp θ *
            ‖bettinConreyCentralSpectralKernel t‖)) := by
    exact (continuous_const.mul
      (continuous_const.add continuous_abs)).mul
        (continuous_const.mul
          continuous_bettinConreyCentralSpectralKernel.norm)
  have hcompact : Integrable compact :=
    hcompactContinuous.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have htail : Integrable
      (fun t : ℝ =>
        (162 * C * R) *
          abelPolynomialExponentialMajorant 2
            (Real.pi - θ) t) :=
    (integrable_abelPolynomialExponentialMajorant 2
      (psiZeroLocalRate_pos z hz)).const_mul _
  have hdecomp : psiZeroLocalDerivativeMajorant z =
      fun t => compact t +
        (162 * C * R) *
          abelPolynomialExponentialMajorant 2
            (Real.pi - θ) t := by
    funext t
    unfold psiZeroLocalDerivativeMajorant psiZeroLocalMajorant compact
      abelPolynomialExponentialMajorant C R θ
    by_cases ht : t ∈ Icc (-1 : ℝ) 1 <;>
      simp [Set.indicator, ht] <;> ring
  rw [hdecomp]
  exact hcompact.add htail

/-- Uniform pointwise domination of the differentiated vertical integrand
on a neighborhood of a right-half-plane point. -/
theorem eventually_norm_bettinConreyGZeroVerticalDerivativeIntegrand_le
    (z : ℂ) (hz : 0 < z.re) :
    ∀ᶠ w in nhds z, ∀ t : ℝ,
      ‖bettinConreyGZeroVerticalDerivativeIntegrand w t‖ ≤
        psiZeroLocalDerivativeMajorant z t := by
  have hre : ∀ᶠ w : ℂ in nhds z, 0 < w.re :=
    continuousAt_const.eventually_lt Complex.continuous_re.continuousAt hz
  filter_upwards [eventually_norm_cpow_central_le z hz,
    eventually_norm_inv_le_psiZeroLocalInverseConstant z hz, hre]
      with w hpow hinv hwre
  intro t
  let s := bettinConreyCentralVerticalPoint t
  have hw0 : w ≠ 0 := ne_of_apply_ne Complex.re hwre.ne'
  have hcpow : w ^ (-s - 1) = w ^ (-s) * w⁻¹ := by
    calc
      w ^ (-s - 1) = w ^ ((-s) + (-1 : ℂ)) := by ring_nf
      _ = w ^ (-s) * w ^ (-1 : ℂ) := Complex.cpow_add _ _ hw0
      _ = w ^ (-s) * w⁻¹ := by rw [Complex.cpow_neg_one]
  have hbase :=
    norm_bettinConreyGZeroVerticalIntegrand_le_localMajorant
      z w t (hpow t)
  have hintegrand :
      bettinConreyGZeroVerticalIntegrand w t =
        bettinConreyCentralSpectralKernel t * w ^ (-s) := rfl
  rw [hintegrand, norm_mul] at hbase
  unfold bettinConreyGZeroVerticalDerivativeIntegrand
  dsimp only
  rw [hcpow]
  simp only [norm_mul, norm_neg]
  have hs := norm_bettinConreyCentralVerticalPoint_le t
  have hmajorant_nonneg : 0 ≤ psiZeroLocalMajorant z t := by
    unfold psiZeroLocalMajorant abelPolynomialExponentialMajorant
    exact add_nonneg
      (Set.indicator_nonneg (fun _ _ =>
        mul_nonneg
          (mul_nonneg (psiZeroLocalRadialConstant_nonneg z)
            (Real.exp_pos _).le)
          (norm_nonneg _)) t)
      (mul_nonneg
        (mul_nonneg (by norm_num) (psiZeroLocalRadialConstant_nonneg z))
        (mul_nonneg (pow_nonneg (by positivity) _) (Real.exp_pos _).le))
  have hproduct :
      ‖bettinConreyCentralSpectralKernel t‖ *
          ‖w ^ (-s)‖ * ‖s‖ * ‖w⁻¹‖ ≤
        psiZeroLocalMajorant z t * (1 + |t|) *
          psiZeroLocalInverseConstant z := by
    have hfirst :
        (‖bettinConreyCentralSpectralKernel t‖ * ‖w ^ (-s)‖) * ‖s‖ ≤
          psiZeroLocalMajorant z t * (1 + |t|) :=
      mul_le_mul hbase hs (norm_nonneg _) hmajorant_nonneg
    calc
      ‖bettinConreyCentralSpectralKernel t‖ *
            ‖w ^ (-s)‖ * ‖s‖ * ‖w⁻¹‖ ≤
          (psiZeroLocalMajorant z t * (1 + |t|)) * ‖w⁻¹‖ :=
        mul_le_mul_of_nonneg_right hfirst (norm_nonneg _)
      _ ≤ (psiZeroLocalMajorant z t * (1 + |t|)) *
          psiZeroLocalInverseConstant z :=
        mul_le_mul_of_nonneg_left hinv
          (mul_nonneg hmajorant_nonneg (by positivity))
  unfold psiZeroLocalDerivativeMajorant
  change
    ‖bettinConreyCentralSpectralKernel t‖ *
        (‖s‖ * (‖w ^ (-s)‖ * ‖w⁻¹‖)) ≤ _
  calc
    ‖bettinConreyCentralSpectralKernel t‖ *
          (‖s‖ * (‖w ^ (-s)‖ * ‖w⁻¹‖)) =
        ‖bettinConreyCentralSpectralKernel t‖ *
          ‖w ^ (-s)‖ * ‖s‖ * ‖w⁻¹‖ := by ring
    _ ≤ psiZeroLocalMajorant z t * (1 + |t|) *
          psiZeroLocalInverseConstant z := hproduct
    _ = psiZeroLocalInverseConstant z * (1 + |t|) *
          psiZeroLocalMajorant z t := by ring

theorem continuous_bettinConreyGZeroVerticalDerivativeIntegrand
    (z : ℂ) (hz : 0 < z.re) :
    Continuous (bettinConreyGZeroVerticalDerivativeIntegrand z) := by
  have hz0 : z ≠ 0 := ne_of_apply_ne Complex.re hz.ne'
  letI : NeZero z := ⟨hz0⟩
  have hs : Continuous
      (fun t : ℝ => bettinConreyCentralVerticalPoint t) := by
    unfold bettinConreyCentralVerticalPoint
    fun_prop
  have hpow : Continuous
      (fun t : ℝ =>
        z ^ (-(bettinConreyCentralVerticalPoint t) - 1)) :=
    (continuous_const_cpow z).comp (hs.neg.sub continuous_const)
  unfold bettinConreyGZeroVerticalDerivativeIntegrand
  exact continuous_bettinConreyCentralSpectralKernel.mul
    (hs.neg.mul hpow)

/-- Differentiation under the defining Mellin integral. -/
theorem differentiableAt_bettinConreyGZero
    (z : ℂ) (hz : 0 < z.re) :
    DifferentiableAt ℂ bettinConreyGZero z := by
  let bound := psiZeroLocalDerivativeMajorant z
  let s : Set ℂ := {w | 0 < w.re ∧
    ∀ t : ℝ,
      ‖bettinConreyGZeroVerticalDerivativeIntegrand w t‖ ≤ bound t}
  have hre : ∀ᶠ w : ℂ in nhds z, 0 < w.re :=
    continuousAt_const.eventually_lt Complex.continuous_re.continuousAt hz
  have hderivBound :=
    eventually_norm_bettinConreyGZeroVerticalDerivativeIntegrand_le z hz
  have hs : s ∈ nhds z := by
    filter_upwards [hre, hderivBound] with w hw hbound
    exact ⟨hw, hbound⟩
  let H := bettinConreyGZeroLocalMajorant_proved z hz
  have hFmeas : ∀ᶠ w in nhds z,
      AEStronglyMeasurable
        (fun t : ℝ => bettinConreyGZeroVerticalIntegrand w t) :=
    H.integrand_aestronglyMeasurable
  have hFint : Integrable
      (fun t : ℝ => bettinConreyGZeroVerticalIntegrand z t) := by
    apply Integrable.mono' H.bound_integrable
    · exact (continuous_bettinConreyGZeroVerticalIntegrand z hz).aestronglyMeasurable
    · exact H.norm_le.self_of_nhds
  have hF'meas : AEStronglyMeasurable
      (bettinConreyGZeroVerticalDerivativeIntegrand z) :=
    (continuous_bettinConreyGZeroVerticalDerivativeIntegrand z hz).aestronglyMeasurable
  have hbound : ∀ᵐ t : ℝ ∂volume, ∀ w ∈ s,
      ‖bettinConreyGZeroVerticalDerivativeIntegrand w t‖ ≤ bound t := by
    filter_upwards [] with t w hw
    exact hw.2 t
  have hdiff : ∀ᵐ t : ℝ ∂volume, ∀ w ∈ s,
      HasDerivAt
        (fun u : ℂ => bettinConreyGZeroVerticalIntegrand u t)
        (bettinConreyGZeroVerticalDerivativeIntegrand w t) w := by
    filter_upwards [] with t w hw
    exact hasDerivAt_bettinConreyGZeroVerticalIntegrand w t hw.1
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := fun w t => bettinConreyGZeroVerticalIntegrand w t)
    (F' := fun w t => bettinConreyGZeroVerticalDerivativeIntegrand w t)
    (bound := bound) hs hFmeas hFint hF'meas hbound
    (psiZeroLocalDerivativeMajorant_integrable z hz) hdiff
  unfold bettinConreyGZero
  exact (hasDerivAt_const z (1 / (Real.pi : ℂ))).mul hmain.2
    |>.differentiableAt

/-- The complete literal central period is holomorphic at every point of the
right half-plane. -/
theorem differentiableAt_bettinConreyPsiZero
    (z : ℂ) (hz : 0 < z.re) :
    DifferentiableAt ℂ bettinConreyPsiZero z := by
  have hz0 : z ≠ 0 := ne_of_apply_ne Complex.re hz.ne'
  have hscaleRe : 0 < (((2 * Real.pi : ℂ) * z).re) := by
    norm_num
    positivity
  have hscaleSlit : (2 * Real.pi : ℂ) * z ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    exact Or.inl hscaleRe
  have hinner : DifferentiableAt ℂ
      (fun w : ℂ => (2 * Real.pi : ℂ) * w) z :=
    differentiableAt_id.const_mul _
  have hlog : DifferentiableAt ℂ
      (fun w : ℂ => Complex.log ((2 * Real.pi : ℂ) * w)) z :=
    hinner.clog hscaleSlit
  have hg := differentiableAt_bettinConreyGZero z hz
  have hden : (Real.pi : ℂ) * I * z ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) I_ne_zero) hz0
  have hfirst : DifferentiableAt ℂ
      (fun w : ℂ =>
        -2 *
            (Complex.log ((2 * Real.pi : ℂ) * w) -
              (Real.eulerMascheroniConstant : ℂ)) /
          ((Real.pi : ℂ) * I * w)) z :=
    (hlog.sub (differentiableAt_const (x := z)
      (c := (Real.eulerMascheroniConstant : ℂ)))).const_mul (-2) |>.div
      (differentiableAt_id.const_mul ((Real.pi : ℂ) * I)) hden
  have hsecond : DifferentiableAt ℂ
      (fun w : ℂ => 2 * I * bettinConreyGZero w) z :=
    hg.const_mul (2 * I)
  unfold bettinConreyPsiZero
  exact hfirst.sub hsecond

/-- Holomorphy on the complete right half-plane. -/
theorem analyticOnNhd_bettinConreyPsiZero_rightHalfPlane :
    AnalyticOnNhd ℂ bettinConreyPsiZero {z : ℂ | 0 < z.re} := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} :=
    Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  apply (analyticOnNhd_iff_differentiableOn hopen).2
  intro z hz
  exact (differentiableAt_bettinConreyPsiZero z hz).differentiableWithinAt

/-- The normalized function occurring in the source Taylor theorem is
analytic on its full natural unit disc. -/
theorem analyticOnNhd_bettinConreyPsiZeroTaylorFunction_unitDisc :
    AnalyticOnNhd ℂ bettinConreyPsiZeroTaylorFunction
      (Metric.ball (0 : ℂ) 1) := by
  apply (analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2
  intro z hz
  have hznorm : ‖z‖ < 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hre : 0 < (1 + z).re := by
    have hzre : -‖z‖ ≤ z.re := neg_le_of_abs_le (abs_re_le_norm z)
    norm_num
    linarith
  have hone : DifferentiableAt ℂ (fun w : ℂ => 1 + w) z := by
    fun_prop
  have hpsi : DifferentiableAt ℂ
      (fun w : ℂ => bettinConreyPsiZero (1 + w)) z :=
    (differentiableAt_bettinConreyPsiZero (1 + z) hre).comp z hone
  unfold bettinConreyPsiZeroTaylorFunction
  have hproduct : DifferentiableAt ℂ
      (fun w : ℂ =>
        (Real.pi : ℂ) * I / 2 * (1 + w) *
          bettinConreyPsiZero (1 + w)) z :=
    (hone.const_mul ((Real.pi : ℂ) * I / 2)).mul hpsi
  have honeConst : DifferentiableAt ℂ (fun _w : ℂ => (1 : ℂ)) z :=
    differentiableAt_const (x := z) (c := (1 : ℂ))
  have hlinear : DifferentiableAt ℂ (fun w : ℂ => w / 2) z :=
    differentiableAt_id.div_const 2
  exact ((hproduct.add honeConst).add hlinear).differentiableWithinAt

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZeroHolomorphic
