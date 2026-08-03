import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCFiniteAbelEvaluation

/-!
# Route C: continuity of the literal central period

The finite Abel boundary leaves two global classical inputs: identification
of the upper-half-plane Lambert period with the contour-defined `psi_0`, and
continuity of that literal contour expression on the right half-plane.

This file reduces the latter to its exact analytic content.  Dependence of
the vertical integrand on `z` is pointwise continuous.  A local integrable
majorant therefore gives continuity of the integral by dominated convergence,
and hence continuity of `psi_0`.  No boundary or RH-strength estimate enters.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZeroContinuity

open Complex Filter MeasureTheory Topology
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZero

/-- On the right half-plane, the vertical Mellin integrand is continuous in
its geometric variable for every fixed spectral parameter. -/
theorem continuousAt_bettinConreyGZeroVerticalIntegrand
    (z : ℂ) (t : ℝ) (hz : 0 < z.re) :
    ContinuousAt (fun w : ℂ ↦ bettinConreyGZeroVerticalIntegrand w t) z := by
  have hzslit : z ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    exact Or.inl hz
  unfold bettinConreyGZeroVerticalIntegrand
  dsimp only
  exact continuousAt_const.mul
    (continuousAt_cpow_const hzslit)

/-- The precise local domination datum needed for continuity of the Mellin
integral.  It records no more than the hypotheses of dominated convergence
in a neighbourhood of one right-half-plane point. -/
structure BettinConreyGZeroLocalMajorant (z : ℂ) where
  bound : ℝ → ℝ
  bound_integrable : Integrable bound
  integrand_aestronglyMeasurable :
    ∀ᶠ w in nhds z,
      AEStronglyMeasurable
        (fun t : ℝ ↦ bettinConreyGZeroVerticalIntegrand w t)
  norm_le :
    ∀ᶠ w in nhds z,
      ∀ᵐ t : ℝ ∂volume,
        ‖bettinConreyGZeroVerticalIntegrand w t‖ ≤ bound t

/-- Dominated convergence turns a local majorant into continuity of the
vertical Mellin integral. -/
theorem continuousAt_bettinConreyGZero_of_localMajorant
    (z : ℂ) (hz : 0 < z.re)
    (H : BettinConreyGZeroLocalMajorant z) :
    ContinuousAt bettinConreyGZero z := by
  have hint : Tendsto
      (fun w : ℂ ↦
        ∫ t : ℝ, bettinConreyGZeroVerticalIntegrand w t)
      (nhds z)
      (nhds (∫ t : ℝ, bettinConreyGZeroVerticalIntegrand z t)) := by
    apply tendsto_integral_filter_of_dominated_convergence H.bound
    · exact H.integrand_aestronglyMeasurable
    · exact H.norm_le
    · exact H.bound_integrable
    · filter_upwards [] with t
      exact (continuousAt_bettinConreyGZeroVerticalIntegrand z t hz).tendsto
  unfold bettinConreyGZero
  exact continuousAt_const.mul hint

/-- The explicit elementary term in `psi_0` is continuous on the right half
plane; thus the same local majorant proves continuity of the complete period
function. -/
theorem continuousAt_bettinConreyPsiZero_of_localMajorant
    (z : ℂ) (hz : 0 < z.re)
    (H : BettinConreyGZeroLocalMajorant z) :
    ContinuousAt bettinConreyPsiZero z := by
  have hz0 : z ≠ 0 := by
    exact ne_of_apply_ne Complex.re hz.ne'
  have hscaleRe : 0 < (((2 * Real.pi : ℂ) * z).re) := by
    norm_num
    positivity
  have hscaleSlit : (2 * Real.pi : ℂ) * z ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    exact Or.inl hscaleRe
  have hlog : ContinuousAt
      (fun w : ℂ ↦ Complex.log ((2 * Real.pi : ℂ) * w)) z :=
    (continuousAt_clog hscaleSlit).comp
      (continuousAt_const.mul continuousAt_id)
  have hg := continuousAt_bettinConreyGZero_of_localMajorant z hz H
  have hden : (Real.pi : ℂ) * I * z ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) I_ne_zero) hz0
  have hfirst : ContinuousAt
      (fun w : ℂ ↦
        -2 *
            (Complex.log ((2 * Real.pi : ℂ) * w) -
              (Real.eulerMascheroniConstant : ℂ)) /
          ((Real.pi : ℂ) * I * w)) z := by
    exact (continuousAt_const.mul (hlog.sub continuousAt_const)).div
      (continuousAt_const.mul continuousAt_id) hden
  have hsecond : ContinuousAt
      (fun w : ℂ ↦ 2 * I * bettinConreyGZero w) z := by
    exact (continuousAt_const.mul continuousAt_const).mul hg
  simpa only [bettinConreyPsiZero] using hfirst.sub hsecond

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZeroContinuity
