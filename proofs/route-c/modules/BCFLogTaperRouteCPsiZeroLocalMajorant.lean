import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZeroVerticalMajorant

/-!
# Route C: a local dominated-convergence majorant for `psi_0`

The central spectral kernel has intrinsic decay `exp (-π |t|)`.  On a
neighbourhood of a fixed point in the right half-plane, the complex power
contributes at most `exp (θ |t|)` for some `θ < π / 2`.  Their product is
therefore integrable, uniformly on that neighbourhood.

This closes the continuity input in the finite Abel boundary theorem without
an axiom or a global branch-cut assumption.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZeroLocalMajorant

open Complex Filter MeasureTheory Set Topology
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelRightLine
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelCentralConstructor
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCFiniteAbelEvaluation
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralOnlyAssembly
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCLambertPeriod
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZero
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZeroContinuity
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZeroVerticalMajorant

/-- A strict angular envelope halfway between `|arg z|` and `π/2`. -/
noncomputable def psiZeroLocalAngle (z : ℂ) : ℝ :=
  (|Complex.arg z| + Real.pi / 2) / 2

theorem abs_arg_lt_psiZeroLocalAngle (z : ℂ) (hz : 0 < z.re) :
    |Complex.arg z| < psiZeroLocalAngle z := by
  have harg : |Complex.arg z| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hz)
  unfold psiZeroLocalAngle
  linarith

theorem psiZeroLocalAngle_lt_pi_div_two (z : ℂ) (hz : 0 < z.re) :
    psiZeroLocalAngle z < Real.pi / 2 := by
  have harg : |Complex.arg z| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hz)
  unfold psiZeroLocalAngle
  linarith

theorem psiZeroLocalRate_pos (z : ℂ) (hz : 0 < z.re) :
    0 < Real.pi - psiZeroLocalAngle z := by
  have hθ := psiZeroLocalAngle_lt_pi_div_two z hz
  have hpi := Real.pi_pos
  linarith

/-- The harmless local radial constant for the real part `1/2` of the
complex-power exponent. -/
noncomputable def psiZeroLocalRadialConstant (z : ℂ) : ℝ :=
  Real.rpow (‖z‖ + 1) (1 / 2 : ℝ)

theorem psiZeroLocalRadialConstant_nonneg (z : ℂ) :
    0 ≤ psiZeroLocalRadialConstant z := by
  unfold psiZeroLocalRadialConstant
  exact Real.rpow_nonneg (by positivity) _

/-- Uniform complex-power growth on a small right-half-plane neighbourhood.
The angular loss is strictly smaller than the intrinsic spectral decay. -/
theorem eventually_norm_cpow_central_le
    (z : ℂ) (hz : 0 < z.re) :
    ∀ᶠ w in nhds z,
      ∀ t : ℝ,
        ‖w ^ (-(bettinConreyCentralVerticalPoint t))‖ ≤
          psiZeroLocalRadialConstant z *
            Real.exp (psiZeroLocalAngle z * |t|) := by
  have hzslit : z ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    exact Or.inl hz
  have hnormCont : ContinuousAt (fun w : ℂ ↦ ‖w‖) z :=
    continuous_norm.continuousAt
  have hnorm : ∀ᶠ w : ℂ in nhds z, ‖w‖ < ‖z‖ + 1 :=
    hnormCont.eventually_lt continuousAt_const (lt_add_one _)
  have harg : ∀ᶠ w : ℂ in nhds z,
      |Complex.arg w| < psiZeroLocalAngle z :=
    (Complex.continuousAt_arg hzslit).abs.eventually_lt continuousAt_const
      (abs_arg_lt_psiZeroLocalAngle z hz)
  have hre : ∀ᶠ w : ℂ in nhds z, 0 < w.re :=
    continuousAt_const.eventually_lt Complex.continuous_re.continuousAt hz
  filter_upwards [hnorm, harg, hre] with w hwNorm hwArg hwRe
  intro t
  have hw0 : w ≠ 0 := ne_of_apply_ne Complex.re hwRe.ne'
  have hbase : ‖w‖ ^ (1 / 2 : ℝ) ≤
      (‖z‖ + 1) ^ (1 / 2 : ℝ) := by
    exact Real.rpow_le_rpow (norm_nonneg w) hwNorm.le (by norm_num)
  have hphase : Complex.arg w * t ≤ psiZeroLocalAngle z * |t| := by
    calc
      Complex.arg w * t ≤ |Complex.arg w| * |t| :=
        (le_abs_self (Complex.arg w * t)).trans_eq (abs_mul _ _)
      _ ≤ psiZeroLocalAngle z * |t| :=
        mul_le_mul_of_nonneg_right hwArg.le (abs_nonneg t)
  have hpow :
      ‖w ^ (-(bettinConreyCentralVerticalPoint t))‖ =
        ‖w‖ ^ (1 / 2 : ℝ) * Real.exp (Complex.arg w * t) := by
    rw [Complex.norm_cpow_of_ne_zero hw0]
    norm_num [bettinConreyCentralVerticalPoint]
    rw [Real.exp_neg, div_inv_eq_mul]
  rw [hpow]
  unfold psiZeroLocalRadialConstant
  exact mul_le_mul hbase (Real.exp_le_exp.mpr hphase)
    (Real.exp_pos _).le (Real.rpow_nonneg (by positivity) _)

/-- The explicit dominating function.  On `[-1,1]` it keeps the exact
continuous spectral kernel; globally it adds an integrable exponential tail. -/
noncomputable def psiZeroLocalMajorant (z : ℂ) (t : ℝ) : ℝ :=
  (Icc (-1 : ℝ) 1).indicator
      (fun u : ℝ ↦
        psiZeroLocalRadialConstant z *
          Real.exp (psiZeroLocalAngle z) *
          ‖bettinConreyCentralSpectralKernel u‖) t +
    162 * psiZeroLocalRadialConstant z *
      abelPolynomialExponentialMajorant 1
        (Real.pi - psiZeroLocalAngle z) t

theorem psiZeroLocalMajorant_integrable (z : ℂ) (hz : 0 < z.re) :
    Integrable (psiZeroLocalMajorant z) := by
  have hcompactContinuous : Continuous
      (fun t : ℝ ↦
        psiZeroLocalRadialConstant z *
          Real.exp (psiZeroLocalAngle z) *
          ‖bettinConreyCentralSpectralKernel t‖) := by
    exact continuous_const.mul
      continuous_bettinConreyCentralSpectralKernel.norm
  have hcompact : Integrable
      ((Icc (-1 : ℝ) 1).indicator
        (fun t : ℝ ↦
          psiZeroLocalRadialConstant z *
            Real.exp (psiZeroLocalAngle z) *
            ‖bettinConreyCentralSpectralKernel t‖)) :=
    hcompactContinuous.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have htail : Integrable
      (fun t : ℝ ↦
        162 * psiZeroLocalRadialConstant z *
          abelPolynomialExponentialMajorant 1
            (Real.pi - psiZeroLocalAngle z) t) :=
    (integrable_abelPolynomialExponentialMajorant 1
      (psiZeroLocalRate_pos z hz)).const_mul _
  exact hcompact.add htail

theorem psiZeroLocalAngle_nonneg (z : ℂ) :
    0 ≤ psiZeroLocalAngle z := by
  unfold psiZeroLocalAngle
  positivity

/-- Pointwise domination once the local complex-power estimate is known. -/
theorem norm_bettinConreyGZeroVerticalIntegrand_le_localMajorant
    (z w : ℂ) (t : ℝ)
    (hpow :
      ‖w ^ (-(bettinConreyCentralVerticalPoint t))‖ ≤
        psiZeroLocalRadialConstant z *
          Real.exp (psiZeroLocalAngle z * |t|)) :
    ‖bettinConreyGZeroVerticalIntegrand w t‖ ≤
      psiZeroLocalMajorant z t := by
  have hintegrand :
      bettinConreyGZeroVerticalIntegrand w t =
        bettinConreyCentralSpectralKernel t *
          w ^ (-(bettinConreyCentralVerticalPoint t)) := by
    rfl
  rw [hintegrand, norm_mul]
  by_cases ht : |t| ≤ 1
  · have htmem : t ∈ Icc (-1 : ℝ) 1 := by
      rw [mem_Icc]
      exact (abs_le.mp ht)
    have hexp :
        Real.exp (psiZeroLocalAngle z * |t|) ≤
          Real.exp (psiZeroLocalAngle z) := by
      apply Real.exp_le_exp.mpr
      nlinarith [psiZeroLocalAngle_nonneg z]
    have hpowerCompact :
        ‖w ^ (-(bettinConreyCentralVerticalPoint t))‖ ≤
          psiZeroLocalRadialConstant z *
            Real.exp (psiZeroLocalAngle z) :=
      hpow.trans (mul_le_mul_of_nonneg_left hexp
        (psiZeroLocalRadialConstant_nonneg z))
    have hcompact :
        ‖bettinConreyCentralSpectralKernel t‖ *
            ‖w ^ (-(bettinConreyCentralVerticalPoint t))‖ ≤
          psiZeroLocalRadialConstant z *
            Real.exp (psiZeroLocalAngle z) *
            ‖bettinConreyCentralSpectralKernel t‖ := by
      calc
        ‖bettinConreyCentralSpectralKernel t‖ *
              ‖w ^ (-(bettinConreyCentralVerticalPoint t))‖ ≤
            ‖bettinConreyCentralSpectralKernel t‖ *
              (psiZeroLocalRadialConstant z *
                Real.exp (psiZeroLocalAngle z)) :=
          mul_le_mul_of_nonneg_left hpowerCompact (norm_nonneg _)
        _ = psiZeroLocalRadialConstant z *
              Real.exp (psiZeroLocalAngle z) *
              ‖bettinConreyCentralSpectralKernel t‖ := by ring
    unfold psiZeroLocalMajorant
    rw [indicator_of_mem htmem]
    exact hcompact.trans (le_add_of_nonneg_right (by
      unfold abelPolynomialExponentialMajorant
      exact mul_nonneg
        (mul_nonneg (by norm_num) (psiZeroLocalRadialConstant_nonneg z))
        (mul_nonneg (pow_nonneg (by positivity) _) (Real.exp_pos _).le)))
  · have htTail : 1 ≤ |t| := le_of_lt (lt_of_not_ge ht)
    have hkernel := norm_bettinConreyCentralSpectralKernel_le t htTail
    have hproduct :
        ‖bettinConreyCentralSpectralKernel t‖ *
            ‖w ^ (-(bettinConreyCentralVerticalPoint t))‖ ≤
          (162 * (1 + |t|) * Real.exp (-(Real.pi * |t|))) *
            (psiZeroLocalRadialConstant z *
              Real.exp (psiZeroLocalAngle z * |t|)) :=
      mul_le_mul hkernel hpow (norm_nonneg _) (by positivity)
    have htailIdentity :
        (162 * (1 + |t|) * Real.exp (-(Real.pi * |t|))) *
            (psiZeroLocalRadialConstant z *
              Real.exp (psiZeroLocalAngle z * |t|)) =
          162 * psiZeroLocalRadialConstant z *
            abelPolynomialExponentialMajorant 1
              (Real.pi - psiZeroLocalAngle z) t := by
      unfold abelPolynomialExponentialMajorant
      simp only [pow_one]
      calc
        (162 * (1 + |t|) * Real.exp (-(Real.pi * |t|))) *
              (psiZeroLocalRadialConstant z *
                Real.exp (psiZeroLocalAngle z * |t|)) =
            162 * psiZeroLocalRadialConstant z * (1 + |t|) *
              (Real.exp (-(Real.pi * |t|)) *
                Real.exp (psiZeroLocalAngle z * |t|)) := by ring
        _ = 162 * psiZeroLocalRadialConstant z * (1 + |t|) *
              Real.exp (-(Real.pi * |t|) +
                psiZeroLocalAngle z * |t|) := by rw [Real.exp_add]
        _ = 162 * psiZeroLocalRadialConstant z *
              ((1 + |t|) *
                Real.exp (-(Real.pi - psiZeroLocalAngle z) * |t|)) := by
          rw [show -(Real.pi * |t|) + psiZeroLocalAngle z * |t| =
            -(Real.pi - psiZeroLocalAngle z) * |t| by ring]
          ring
    rw [htailIdentity] at hproduct
    unfold psiZeroLocalMajorant
    exact hproduct.trans (le_add_of_nonneg_left (by
      exact Set.indicator_nonneg (fun u _ ↦ mul_nonneg
        (mul_nonneg (psiZeroLocalRadialConstant_nonneg z)
          (Real.exp_pos _).le) (norm_nonneg _)) t))

/-- The local dominated-convergence datum is now unconditional. -/
noncomputable def bettinConreyGZeroLocalMajorant_proved
    (z : ℂ) (hz : 0 < z.re) :
    BettinConreyGZeroLocalMajorant z where
  bound := psiZeroLocalMajorant z
  bound_integrable := psiZeroLocalMajorant_integrable z hz
  integrand_aestronglyMeasurable := by
    have hre : ∀ᶠ w : ℂ in nhds z, 0 < w.re :=
      continuousAt_const.eventually_lt Complex.continuous_re.continuousAt hz
    filter_upwards [hre] with w hw
    exact (continuous_bettinConreyGZeroVerticalIntegrand w hw).aestronglyMeasurable
  norm_le := by
    filter_upwards [eventually_norm_cpow_central_le z hz] with w hw
    exact Filter.Eventually.of_forall fun t ↦
      norm_bettinConreyGZeroVerticalIntegrand_le_localMajorant z w t (hw t)

/-- Continuity of the literal contour-defined central period throughout the
right half-plane. -/
theorem continuousAt_bettinConreyPsiZero
    (z : ℂ) (hz : 0 < z.re) :
    ContinuousAt bettinConreyPsiZero z :=
  continuousAt_bettinConreyPsiZero_of_localMajorant z hz
    (bettinConreyGZeroLocalMajorant_proved z hz)

/-- The finite Abel constructor now needs only the literal Lambert-series
identification; continuity has been discharged by the explicit majorant. -/
noncomputable def bettinConreyCentralAbelConstructorData_of_identification_proved
    (H : BettinConreyLambertPsiZeroIdentification) :
    BettinConreyCentralAbelConstructorData :=
  bettinConreyCentralAbelConstructorData_of_identification
    H continuousAt_bettinConreyPsiZero

/-- One-input form of the central rational Bettin--Conrey theorem. -/
noncomputable def bettinConreyPsiZeroCentralRationalTheorem_of_identification
    (H : BettinConreyLambertPsiZeroIdentification) :
  BettinConreyPsiZeroCentralRationalTheorem :=
  BettinConreyCentralAbelConstructorData.toCentralRationalTheorem
    (bettinConreyCentralAbelConstructorData_of_identification_proved H)

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZeroLocalMajorant
