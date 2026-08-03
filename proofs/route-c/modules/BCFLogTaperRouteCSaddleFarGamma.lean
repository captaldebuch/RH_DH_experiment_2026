import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleWeightedFar

/-!
# Route C: Gamma evaluation of the weighted far profile

This file integrates the retained `(1-theta)` saddle profile from
`BCFLogTaperRouteCSaddleWeightedFar`.  With

`q = (1-theta)*n + alpha` and `b = 1-theta-epsilon`,

the rescaled profile is exactly

`exp((1-theta)*n) * n^(1-q) * u^(q-1) * exp(-b*u)`.

For `q > 0` and `b > 0`, its integral is therefore an explicit Gamma value.
Combining this with the entropy gap gives a closed, unconditional upper bound
for the norm of the genuine far-sector integral.  The remaining step is to
choose `theta` and `epsilon` and prove that this explicit bound is negligible
relative to the principal saddle normalization.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleFarGamma

open MeasureTheory Set
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleCentralWindow
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleFarEntropy
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleWeightedFar

noncomputable def routeCSaddleRetainedProfile
    (alpha theta epsilon : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  Real.rpow (u / (n : ℝ)) (alpha - 1) *
    Real.exp (((1 - theta) * (n : ℝ)) *
      routeCSaddleRate (u / (n : ℝ)) + epsilon * u)

def routeCSaddleRetainedShape (alpha theta : ℝ) (n : ℕ) : ℝ :=
  (1 - theta) * (n : ℝ) + alpha

def routeCSaddleRetainedRate (theta epsilon : ℝ) : ℝ :=
  1 - theta - epsilon

/-- The same retained profile in Gamma-integrable form. -/
noncomputable def routeCSaddleRetainedGammaProfile
    (alpha theta epsilon : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  Real.exp ((1 - theta) * (n : ℝ)) *
    Real.rpow n (1 - routeCSaddleRetainedShape alpha theta n) *
      (Real.rpow u (routeCSaddleRetainedShape alpha theta n - 1) *
        Real.exp (-(routeCSaddleRetainedRate theta epsilon * u)))

theorem routeCSaddleRetainedProfile_eq_gammaProfile
    {u : ℝ} {n : ℕ} (alpha theta epsilon : ℝ)
    (hu : 0 < u) (hn : 0 < n) :
    routeCSaddleRetainedProfile alpha theta epsilon n u =
      routeCSaddleRetainedGammaProfile alpha theta epsilon n u := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hv : 0 < u / (n : ℝ) := div_pos hu hnR
  rw [routeCSaddleRetainedProfile, routeCSaddleRetainedGammaProfile]
  rw [show Real.rpow (u / (n : ℝ)) (alpha - 1) =
      Real.exp (Real.log (u / (n : ℝ)) * (alpha - 1)) from
        Real.rpow_def_of_pos hv _,
    show Real.rpow (n : ℝ)
        (1 - routeCSaddleRetainedShape alpha theta n) =
      Real.exp (Real.log (n : ℝ) *
        (1 - routeCSaddleRetainedShape alpha theta n)) from
          Real.rpow_def_of_pos hnR _,
    show Real.rpow u (routeCSaddleRetainedShape alpha theta n - 1) =
      Real.exp (Real.log u *
        (routeCSaddleRetainedShape alpha theta n - 1)) from
          Real.rpow_def_of_pos hu _]
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [routeCSaddleRate, routeCSaddleRetainedShape,
    routeCSaddleRetainedRate,
    Real.log_div (ne_of_gt hu) (ne_of_gt hnR)]
  field_simp [ne_of_gt hnR]
  ring

theorem integrableOn_routeCSaddleRetainedGammaProfile
    (alpha theta epsilon : ℝ) (n : ℕ)
    (hq : 0 < routeCSaddleRetainedShape alpha theta n)
    (hb : 0 < routeCSaddleRetainedRate theta epsilon) :
    IntegrableOn
      (routeCSaddleRetainedGammaProfile alpha theta epsilon n) (Ioi 0) := by
  have hbase0 :=
    integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ))
      (s := routeCSaddleRetainedShape alpha theta n - 1)
      (b := routeCSaddleRetainedRate theta epsilon)
      (by linarith) (by norm_num) hb
  have hbase : IntegrableOn
      (fun u : ℝ =>
        Real.rpow u (routeCSaddleRetainedShape alpha theta n - 1) *
          Real.exp (-(routeCSaddleRetainedRate theta epsilon *
            Real.rpow u (1 : ℝ))))
      (Ioi 0) := by
    simpa only [Real.rpow_eq_pow, neg_mul] using hbase0
  have hbase' : IntegrableOn
      (fun u : ℝ =>
        Real.rpow u (routeCSaddleRetainedShape alpha theta n - 1) *
          Real.exp (-(routeCSaddleRetainedRate theta epsilon * u)))
      (Ioi 0) := by
    simpa only [Real.rpow_eq_pow, Real.rpow_one] using hbase
  change IntegrableOn (fun x : ℝ =>
    Real.exp ((1 - theta) * (n : ℝ)) *
      Real.rpow n (1 - routeCSaddleRetainedShape alpha theta n) *
        (Real.rpow x (routeCSaddleRetainedShape alpha theta n - 1) *
          Real.exp (-(routeCSaddleRetainedRate theta epsilon * x))))
    (Ioi 0)
  simpa only [mul_assoc] using
    (hbase'.const_mul
      (Real.rpow n (1 - routeCSaddleRetainedShape alpha theta n))).const_mul
        (Real.exp ((1 - theta) * (n : ℝ)))

/-- Exact Gamma evaluation of the retained full-line profile. -/
theorem integral_routeCSaddleRetainedGammaProfile
    (alpha theta epsilon : ℝ) (n : ℕ)
    (hq : 0 < routeCSaddleRetainedShape alpha theta n)
    (hb : 0 < routeCSaddleRetainedRate theta epsilon) :
    ∫ u : ℝ in Ioi 0,
        routeCSaddleRetainedGammaProfile alpha theta epsilon n u =
      Real.exp ((1 - theta) * (n : ℝ)) *
        Real.rpow n (1 - routeCSaddleRetainedShape alpha theta n) *
          (Real.rpow (1 / routeCSaddleRetainedRate theta epsilon)
              (routeCSaddleRetainedShape alpha theta n) *
            Real.Gamma (routeCSaddleRetainedShape alpha theta n)) := by
  unfold routeCSaddleRetainedGammaProfile
  rw [integral_const_mul]
  have hinner := Real.integral_rpow_mul_exp_neg_mul_Ioi hq hb
  have hinner' :
      (∫ u : ℝ in Ioi 0,
        Real.rpow u (routeCSaddleRetainedShape alpha theta n - 1) *
          Real.exp (-(routeCSaddleRetainedRate theta epsilon * u))) =
        Real.rpow (1 / routeCSaddleRetainedRate theta epsilon)
            (routeCSaddleRetainedShape alpha theta n) *
          Real.Gamma (routeCSaddleRetainedShape alpha theta n) := by
    simpa only [Real.rpow_eq_pow] using hinner
  exact congrArg
    (fun x : ℝ => Real.exp ((1 - theta) * (n : ℝ)) *
      Real.rpow n (1 - routeCSaddleRetainedShape alpha theta n) * x)
    hinner'

/-- The explicit Gamma-integrable majorant for the deformed far sector. -/
noncomputable def routeCSaddleFarGammaMajorant
    (A : ℂ) (alpha theta delta epsilon : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  (Real.rpow n ((n : ℝ) + alpha - 1) * Real.exp (-(n : ℝ))) *
    Real.exp (-(theta * (n : ℝ) * routeCSaddleEntropyGap delta)) *
      Real.exp (‖A‖ ^ 2 / (4 * epsilon)) *
        routeCSaddleRetainedGammaProfile alpha theta epsilon n u

theorem norm_routeCSaddleIntegrand_far_le_gammaMajorant
    (A : ℂ) (alpha theta delta epsilon : ℝ) {u : ℝ} {n : ℕ}
    (hu : u ∈ routeCSaddleFarSet delta n) (hn : 0 < n)
    (hd0 : 0 < delta) (hd1 : delta < 1) (htheta : 0 ≤ theta)
    (hepsilon : 0 < epsilon) :
    ‖routeCSaddleIntegrand A alpha n u‖ ≤
      routeCSaddleFarGammaMajorant A alpha theta delta epsilon n u := by
  calc
    ‖routeCSaddleIntegrand A alpha n u‖ ≤
      (Real.rpow n ((n : ℝ) + alpha - 1) * Real.exp (-(n : ℝ))) *
        Real.rpow (u / (n : ℝ)) (alpha - 1) *
          Real.exp (-(theta * (n : ℝ) * routeCSaddleEntropyGap delta)) *
            Real.exp (((1 - theta) * (n : ℝ)) *
              routeCSaddleRate (u / (n : ℝ)) +
                epsilon * u + ‖A‖ ^ 2 / (4 * epsilon)) :=
      norm_routeCSaddleIntegrand_far_le_split_young
        A alpha theta delta epsilon hu hn hd0 hd1 htheta hepsilon
    _ = routeCSaddleFarGammaMajorant
        A alpha theta delta epsilon n u := by
      rw [show ((1 - theta) * (n : ℝ)) *
            routeCSaddleRate (u / (n : ℝ)) + epsilon * u +
              ‖A‖ ^ 2 / (4 * epsilon) =
          (((1 - theta) * (n : ℝ)) *
            routeCSaddleRate (u / (n : ℝ)) + epsilon * u) +
              ‖A‖ ^ 2 / (4 * epsilon) by ring, Real.exp_add]
      rw [routeCSaddleFarGammaMajorant,
        ← routeCSaddleRetainedProfile_eq_gammaProfile
          alpha theta epsilon hu.1 hn,
        routeCSaddleRetainedProfile]
      ring

theorem integrableOn_routeCSaddleFarGammaMajorant
    (A : ℂ) (alpha theta delta epsilon : ℝ) (n : ℕ)
    (hq : 0 < routeCSaddleRetainedShape alpha theta n)
    (hb : 0 < routeCSaddleRetainedRate theta epsilon) :
    IntegrableOn
      (routeCSaddleFarGammaMajorant A alpha theta delta epsilon n) (Ioi 0) := by
  unfold routeCSaddleFarGammaMajorant
  simpa only [mul_assoc] using
    (((integrableOn_routeCSaddleRetainedGammaProfile
        alpha theta epsilon n hq hb).const_mul
      (Real.exp (‖A‖ ^ 2 / (4 * epsilon)))).const_mul
        (Real.exp (-(theta * (n : ℝ) *
          routeCSaddleEntropyGap delta)))).const_mul
          (Real.rpow n ((n : ℝ) + alpha - 1) * Real.exp (-(n : ℝ)))

theorem integral_routeCSaddleFarGammaMajorant
    (A : ℂ) (alpha theta delta epsilon : ℝ) (n : ℕ)
    (hq : 0 < routeCSaddleRetainedShape alpha theta n)
    (hb : 0 < routeCSaddleRetainedRate theta epsilon) :
    ∫ u : ℝ in Ioi 0,
        routeCSaddleFarGammaMajorant A alpha theta delta epsilon n u =
      (Real.rpow n ((n : ℝ) + alpha - 1) * Real.exp (-(n : ℝ))) *
        Real.exp (-(theta * (n : ℝ) * routeCSaddleEntropyGap delta)) *
          Real.exp (‖A‖ ^ 2 / (4 * epsilon)) *
            (Real.exp ((1 - theta) * (n : ℝ)) *
              Real.rpow n (1 - routeCSaddleRetainedShape alpha theta n) *
                (Real.rpow (1 / routeCSaddleRetainedRate theta epsilon)
                    (routeCSaddleRetainedShape alpha theta n) *
                  Real.Gamma
                    (routeCSaddleRetainedShape alpha theta n))) := by
  unfold routeCSaddleFarGammaMajorant
  rw [integral_const_mul]
  rw [integral_routeCSaddleRetainedGammaProfile
    alpha theta epsilon n hq hb]

theorem routeCSaddleFarGammaMajorant_nonneg
    (A : ℂ) (alpha theta delta epsilon : ℝ)
    (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ routeCSaddleFarGammaMajorant
      A alpha theta delta epsilon n u := by
  unfold routeCSaddleFarGammaMajorant routeCSaddleRetainedGammaProfile
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
          (Real.exp_nonneg _))
        (Real.exp_nonneg _))
      (Real.exp_nonneg _))
    (mul_nonneg
      (mul_nonneg (Real.exp_nonneg _)
        (Real.rpow_nonneg (Nat.cast_nonneg n) _))
      (mul_nonneg (Real.rpow_nonneg hu _)
        (Real.exp_nonneg _)))

/-- Closed Gamma upper bound for the genuine far-sector integral. -/
theorem norm_routeCSaddleFarIntegral_le_gamma
    (A : ℂ) (alpha theta delta epsilon : ℝ) (n : ℕ)
    (hn : 0 < n) (hd0 : 0 < delta) (hd1 : delta < 1)
    (htheta : 0 ≤ theta) (hepsilon : 0 < epsilon)
    (hq : 0 < routeCSaddleRetainedShape alpha theta n)
    (hb : 0 < routeCSaddleRetainedRate theta epsilon) :
    ‖routeCSaddleFarIntegral A alpha delta n‖ ≤
      (Real.rpow n ((n : ℝ) + alpha - 1) * Real.exp (-(n : ℝ))) *
        Real.exp (-(theta * (n : ℝ) * routeCSaddleEntropyGap delta)) *
          Real.exp (‖A‖ ^ 2 / (4 * epsilon)) *
            (Real.exp ((1 - theta) * (n : ℝ)) *
              Real.rpow n (1 - routeCSaddleRetainedShape alpha theta n) *
                (Real.rpow (1 / routeCSaddleRetainedRate theta epsilon)
                    (routeCSaddleRetainedShape alpha theta n) *
                  Real.Gamma
                    (routeCSaddleRetainedShape alpha theta n))) := by
  have hglobal := integrableOn_routeCSaddleFarGammaMajorant
    A alpha theta delta epsilon n hq hb
  have hfar := hglobal.mono_set (routeCSaddleFarSet_subset_Ioi delta n)
  unfold routeCSaddleFarIntegral
  calc
    ‖∫ u : ℝ in routeCSaddleFarSet delta n,
        routeCSaddleIntegrand A alpha n u‖ ≤
        ∫ u : ℝ in routeCSaddleFarSet delta n,
          routeCSaddleFarGammaMajorant
            A alpha theta delta epsilon n u := by
      apply norm_integral_le_of_norm_le hfar
      filter_upwards [self_mem_ae_restrict
        (measurableSet_routeCSaddleFarSet delta n)] with u hu
      exact norm_routeCSaddleIntegrand_far_le_gammaMajorant
        A alpha theta delta epsilon hu hn hd0 hd1 htheta hepsilon
    _ ≤ ∫ u : ℝ in Ioi 0,
        routeCSaddleFarGammaMajorant
          A alpha theta delta epsilon n u := by
      apply setIntegral_mono_set hglobal
      · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
        exact routeCSaddleFarGammaMajorant_nonneg
          A alpha theta delta epsilon n hu.le
      · exact Filter.Eventually.of_forall
          (routeCSaddleFarSet_subset_Ioi delta n)
    _ = _ := integral_routeCSaddleFarGammaMajorant
      A alpha theta delta epsilon n hq hb

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleFarGamma
