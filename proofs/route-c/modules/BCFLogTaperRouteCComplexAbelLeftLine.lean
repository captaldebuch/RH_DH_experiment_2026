import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCComplexEstermannMellin

/-!
# Route C: the complex Abel left vertical line

This module inserts the complex-damped Estermann inverse-Mellin formula on
the left side of the canonical Abel rectangle.  It proves integrability of
the complete initial divisor row, identifies the reflected integrand after
vertical reversal, and evaluates the normalized left line exactly.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCComplexAbelLeftLine

open Complex Filter MeasureTheory Set Topology
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannContourShift
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannHurwitz
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannSeries
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelComplexDamping
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelContourLimit
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCComplexEstermannMellin
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCComplexInverseMellin

/-- The complete Estermann row on the initial line is Bochner integrable for
every complex damping parameter in the open right half-plane. -/
theorem integrable_initialComplexAbelEstermann
    {u : ℂ} (hu : 0 < u.re) (a q : ℕ) :
    Integrable (fun t : ℝ =>
      u ^ (-estermannVerticalPoint (3 / 2 : ℝ) t) *
        Complex.Gamma (estermannVerticalPoint (3 / 2 : ℝ) t) *
        estermannDirichletSeries a q
          (estermannVerticalPoint (3 / 2 : ℝ) t)) := by
  have hu0 : u ≠ 0 := by
    intro h
    subst u
    norm_num at hu
  have hstrip := log_mem_complexGammaMellinStrip hu
  change |(Complex.log u).im| < Real.pi / 2 at hstrip
  let M : ℝ := estermannThreeHalvesNormMass a q
  have hscalar : Integrable
      (complexGammaMellinIntegrand (Complex.log u)) :=
    integrable_complexGammaMellinIntegrand hstrip
  have hmajor : Integrable (fun t : ℝ =>
      ‖complexGammaMellinIntegrand (Complex.log u) t‖ * M) :=
    hscalar.norm.mul_const M
  apply Integrable.mono' hmajor
  · have hrows : ∀ n : ℕ, AEStronglyMeasurable
        (complexAbelMellinEstermannTerm a q u n) := fun n =>
      (integrable_complexAbelMellinEstermannTerm a q hu n).aestronglyMeasurable
    have hsum : AEStronglyMeasurable
        (fun t : ℝ => ∑' n : ℕ,
          complexAbelMellinEstermannTerm a q u n t) :=
      AEStronglyMeasurable.tsum hrows
    exact hsum.congr (Eventually.of_forall fun t =>
      tsum_complexAbelMellinEstermannTerm a q u t)
  · filter_upwards [] with t
    have hD := norm_estermannDirichletSeries_threeHalves_le a q t
    change
      ‖u ^ (-estermannVerticalPoint (3 / 2 : ℝ) t) *
          Complex.Gamma (estermannVerticalPoint (3 / 2 : ℝ) t) *
          estermannDirichletSeries a q
            (estermannVerticalPoint (3 / 2 : ℝ) t)‖ ≤ _
    rw [← complexGammaMellinIntegrand_log_eq_cpow hu0, norm_mul]
    exact mul_le_mul_of_nonneg_left hD (norm_nonneg _)

/-- On the left side of the canonical rectangle, the normalized complex
Abel integrand is the negative initial-line integrand with reversed vertical
parameter. -/
theorem complexAbel_leftVertical_integrand
    (u : ℂ) (a q : ℕ) [NeZero q] (t : ℝ) :
    estermannWeightedIntegrand a q
        (bettinConreyComplexAbelReflectionWeight u)
        (estermannVerticalPoint (-1 / 2 : ℝ) t) =
      -(u ^ (-estermannVerticalPoint (3 / 2 : ℝ) (-t)) *
        Complex.Gamma (estermannVerticalPoint (3 / 2 : ℝ) (-t)) *
        estermannDirichletSeries a q
          (estermannVerticalPoint (3 / 2 : ℝ) (-t))) := by
  unfold estermannWeightedIntegrand bettinConreyComplexAbelReflectionWeight
  have hs : 1 < (estermannVerticalPoint (3 / 2 : ℝ) (-t)).re := by
    norm_num [estermannVerticalPoint]
  have harg :
      1 - estermannVerticalPoint (-1 / 2 : ℝ) t =
        estermannVerticalPoint (3 / 2 : ℝ) (-t) := by
    unfold estermannVerticalPoint
    push_cast
    ring
  have hpow :
      estermannVerticalPoint (-1 / 2 : ℝ) t - 1 =
        -estermannVerticalPoint (3 / 2 : ℝ) (-t) := by
    unfold estermannVerticalPoint
    push_cast
    ring
  rw [harg, estermannHurwitzContinuation_eq_dirichletSeries a q hs, hpow]
  ring

/-- Exact complex Mellin identification of the normalized left vertical
line. -/
theorem complexAbel_leftVerticalIntegral_eq_damped
    {u : ℂ} (hu : 0 < u.re) (a q : ℕ) [NeZero q] :
    estermannPrimalVerticalIntegral a q (-1 / 2 : ℝ)
        (bettinConreyComplexAbelReflectionWeight u) =
      -(2 * Real.pi : ℝ) *
        complexDampedEstermannLambertSeries a q u := by
  let F : ℝ → ℂ := fun t =>
    u ^ (-estermannVerticalPoint (3 / 2 : ℝ) t) *
      Complex.Gamma (estermannVerticalPoint (3 / 2 : ℝ) t) *
      estermannDirichletSeries a q
        (estermannVerticalPoint (3 / 2 : ℝ) t)
  have hraw : (∫ t : ℝ, F t) =
      (2 * Real.pi : ℝ) *
        complexDampedEstermannLambertSeries a q u := by
    simpa [F] using complexAbelEstermannMellinIdentity a q hu
  unfold estermannPrimalVerticalIntegral
  rw [show (fun t : ℝ =>
      bettinConreyComplexAbelReflectionWeight u
          (estermannVerticalPoint (-1 / 2 : ℝ) t) *
        estermannHurwitzContinuation a q
          (1 - estermannVerticalPoint (-1 / 2 : ℝ) t)) =
      fun t : ℝ => -(F (-t)) by
    funext t
    simpa [F, estermannWeightedIntegrand] using
      complexAbel_leftVertical_integrand u a q t]
  rw [integral_neg, integral_neg_eq_self, hraw]
  push_cast
  ring

/-- The complex left-line integrability condition is unconditional in the
open right half-plane. -/
theorem integrable_complexAbel_leftVertical
    {u : ℂ} (hu : 0 < u.re) (a q : ℕ) [NeZero q] :
    Integrable (fun t : ℝ =>
      estermannWeightedIntegrand a q
        (bettinConreyComplexAbelReflectionWeight u)
        (estermannVerticalPoint (-1 / 2 : ℝ) t)) := by
  let F : ℝ → ℂ := fun t =>
    u ^ (-estermannVerticalPoint (3 / 2 : ℝ) t) *
      Complex.Gamma (estermannVerticalPoint (3 / 2 : ℝ) t) *
      estermannDirichletSeries a q
        (estermannVerticalPoint (3 / 2 : ℝ) t)
  have hF : Integrable F := by
    simpa [F] using integrable_initialComplexAbelEstermann hu a q
  have hneg : Integrable (fun t : ℝ => -(F (-t))) := hF.comp_neg.neg
  exact hneg.congr (Eventually.of_forall fun t => by
    simpa [F] using (complexAbel_leftVertical_integrand u a q t).symm)

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCComplexAbelLeftLine
