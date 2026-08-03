import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleFixedAlpha

/-!
# Route C: far tails for the coefficient Bessel rows

For `theta = 1/2`, the integrated Gamma majorant for a general fixed
`alpha` differs from the proved `alpha = 1` majorant in only two places:

* `Gamma (n/2 + alpha)` replaces `Gamma (n/2 + 1)`;
* the retained-rate power contributes the fixed factor
  `(1 / (1/2-epsilon))^(alpha-1)`.

All powers of `n` cancel independently of `alpha`.  This observation is the
efficient transfer mechanism for the three Bessel rows `1/4`, `-1/4`, and
`-3/4`.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleCoefficientFar

open Filter Set
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleCentralWindow
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleFarGamma
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleFarOptimization
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleFarLimit
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleRootAbsorption
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleFixedAlpha

theorem routeCSaddleRetainedShape_fixedAlpha_half
    (alpha : ℝ) (n : ℕ) :
    routeCSaddleRetainedShape alpha (1 / 2) n =
      (n : ℝ) / 2 + alpha := by
  unfold routeCSaddleRetainedShape
  ring

/-- The general half-Gamma majorant written relative to the already proved
`alpha = 1` prefactor. -/
noncomputable def routeCSaddleFixedAlphaHalfGammaMajorant
    (A : ℂ) (alpha delta epsilon : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (1 / (1 / 2 - epsilon)) (alpha - 1) *
    routeCSaddleHalfGammaPrefactor A delta epsilon n *
      Real.Gamma ((n : ℝ) / 2 + alpha)

theorem routeCSaddleFixedAlphaHalfGammaMajorant_nonneg
    (A : ℂ) (alpha delta epsilon : ℝ) (n : ℕ)
    (hq : 0 < (n : ℝ) / 2 + alpha) (hepsilon : epsilon < 1 / 2) :
    0 ≤ routeCSaddleFixedAlphaHalfGammaMajorant
      A alpha delta epsilon n := by
  unfold routeCSaddleFixedAlphaHalfGammaMajorant
  have hb : 0 < 1 / (1 / 2 - epsilon) := by positivity
  exact mul_nonneg
    (mul_nonneg (Real.rpow_nonneg hb.le _)
      (routeCSaddleHalfGammaPrefactor_nonneg
        A delta epsilon n hepsilon))
    (Real.Gamma_pos_of_pos hq).le

/-- Exact specialization of the generic Gamma estimate.  Crucially, the
`n`-powers cancel for every `alpha`; only a fixed retained-rate power and the
shifted Gamma value remain. -/
theorem norm_routeCSaddleFarIntegral_fixedAlpha_le_halfGamma
    (A : ℂ) (alpha delta epsilon : ℝ) (n : ℕ)
    (hn : 0 < n) (hd0 : 0 < delta) (hd1 : delta < 1)
    (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2)
    (hq : 0 < (n : ℝ) / 2 + alpha) :
    ‖routeCSaddleFarIntegral A alpha delta n‖ ≤
      routeCSaddleFixedAlphaHalfGammaMajorant
        A alpha delta epsilon n := by
  have h := norm_routeCSaddleFarIntegral_le_gamma
    A alpha (1 / 2) delta epsilon n hn hd0 hd1 (by norm_num) he0
      (by simpa only [routeCSaddleRetainedShape_fixedAlpha_half] using hq)
      (by rw [routeCSaddleRetainedRate_half]; linarith)
  rw [routeCSaddleFixedAlphaHalfGammaMajorant,
    routeCSaddleHalfGammaPrefactor]
  rw [routeCSaddleRetainedShape_fixedAlpha_half,
    routeCSaddleRetainedRate_half] at h
  convert h using 1
  · have hnR : 0 < (n : ℝ) := by positivity
    have hb : 0 < 1 / (1 / 2 - epsilon) := by positivity
    have hnPower :
        Real.rpow n ((n : ℝ) + alpha - 1) *
            Real.rpow n (1 - ((n : ℝ) / 2 + alpha)) =
          Real.rpow n (n : ℝ) * Real.rpow n (-((n : ℝ) / 2)) := by
      calc
        _ = Real.rpow n (((n : ℝ) + alpha - 1) +
              (1 - ((n : ℝ) / 2 + alpha))) :=
          (Real.rpow_add hnR _ _).symm
        _ = Real.rpow n ((n : ℝ) + (-((n : ℝ) / 2))) := by
          congr 1
          ring
        _ = _ := Real.rpow_add hnR _ _
    have hbPower :
        Real.rpow (1 / (1 / 2 - epsilon)) (alpha - 1) *
            Real.rpow (1 / (1 / 2 - epsilon)) ((n : ℝ) / 2 + 1) =
          Real.rpow (1 / (1 / 2 - epsilon)) ((n : ℝ) / 2 + alpha) := by
      calc
        _ = Real.rpow (1 / (1 / 2 - epsilon))
              ((alpha - 1) + ((n : ℝ) / 2 + 1)) :=
          (Real.rpow_add hb _ _).symm
        _ = _ := by
          congr 1
          ring
    let common : ℝ :=
      Real.exp (-(n : ℝ)) *
        Real.exp (-((1 / 2 : ℝ) * (n : ℝ) *
          BCFLogTaperRouteCSaddleFarEntropy.routeCSaddleEntropyGap delta)) *
        Real.exp (‖A‖ ^ 2 / (4 * epsilon)) *
        Real.exp ((1 / 2 : ℝ) * (n : ℝ)) *
        Real.Gamma ((n : ℝ) / 2 + alpha)
    calc
      _ = (Real.rpow n (n : ℝ) * Real.rpow n (-((n : ℝ) / 2))) *
          (Real.rpow (1 / (1 / 2 - epsilon)) (alpha - 1) *
            Real.rpow (1 / (1 / 2 - epsilon)) ((n : ℝ) / 2 + 1)) *
          common := by
        dsimp [common]
        ring
      _ = (Real.rpow n ((n : ℝ) + alpha - 1) *
            Real.rpow n (1 - ((n : ℝ) / 2 + alpha))) *
          Real.rpow (1 / (1 / 2 - epsilon)) ((n : ℝ) / 2 + alpha) *
          common := by rw [← hnPower, hbPower]
      _ = _ := by
        dsimp [common]
        ring

/-- For `alpha ≤ 1`, the shifted Gamma factor is bounded by the completed
`alpha = 1` Gamma factor once both arguments lie in the monotone region. -/
theorem fixedAlphaHalfGammaMajorant_le_one
    (A : ℂ) (alpha delta epsilon : ℝ) (n : ℕ)
    (halpha : alpha ≤ 1) (hq : 2 ≤ (n : ℝ) / 2 + alpha)
    (hepsilon : epsilon < 1 / 2) :
    routeCSaddleFixedAlphaHalfGammaMajorant A alpha delta epsilon n ≤
      Real.rpow (1 / (1 / 2 - epsilon)) (alpha - 1) *
        routeCSaddleHalfGammaMajorant A delta epsilon n := by
  have hq1 : 2 ≤ (n : ℝ) / 2 + 1 := hq.trans (by linarith)
  have hgamma : Real.Gamma ((n : ℝ) / 2 + alpha) ≤
      Real.Gamma ((n : ℝ) / 2 + 1) :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn hq hq1 (by linarith)
  unfold routeCSaddleFixedAlphaHalfGammaMajorant
    routeCSaddleHalfGammaMajorant
  have hc : 0 ≤ Real.rpow (1 / (1 / 2 - epsilon)) (alpha - 1) :=
    Real.rpow_nonneg (by positivity) _
  have hp := routeCSaddleHalfGammaPrefactor_nonneg
    A delta epsilon n hepsilon
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hgamma hp) hc

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleCoefficientFar
