import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCAbelTwoPole
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannBoundaryAnalysis

/-!
# Route C: from the finite Abel rectangle to the infinite contour

The finite two-pole rectangle is already unconditional.  This module first
identifies its left vertical line with the exponentially damped Estermann
Lambert series constructed by inverse Mellin.  It then packages only the two
genuine limiting obligations (vertical integrability and disappearance of the
horizontal pair) and derives the exact infinite two-pole identity.

No asymptotic estimate, boundary value, or reciprocity theorem is assumed by
the identities proved below.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelContourLimit

open Complex Filter Topology MeasureTheory
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannContourShift
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannHurwitz
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannSeries
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelMellin
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelReflectionWeight
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelTwoPole

/-- The absolutely convergent norm mass of the Estermann series on the
initial line. -/
noncomputable def estermannThreeHalvesNormMass (a q : ℕ) : ℝ :=
  ∑' n : ℕ,
    ‖LSeries.term (estermannCoeff a q) (3 / 2 : ℂ) n‖

theorem estermannThreeHalvesNormMass_nonneg (a q : ℕ) :
    0 ≤ estermannThreeHalvesNormMass a q := by
  unfold estermannThreeHalvesNormMass
  exact tsum_nonneg fun _ => norm_nonneg _

/-- Absolute convergence makes the Estermann series uniformly bounded on
the complete initial vertical line. -/
theorem norm_estermannDirichletSeries_threeHalves_le
    (a q : ℕ) (t : ℝ) :
    ‖estermannDirichletSeries a q
        (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      estermannThreeHalvesNormMass a q := by
  have hs : LSeriesSummable (estermannCoeff a q)
      (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I) :=
    estermannCoeff_summable a q (by norm_num)
  unfold estermannDirichletSeries LSeries
  calc
    ‖∑' n : ℕ,
        LSeries.term (estermannCoeff a q)
          (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I) n‖ ≤
      ∑' n : ℕ,
        ‖LSeries.term (estermannCoeff a q)
          (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I) n‖ :=
        norm_tsum_le_tsum_norm hs.norm
    _ = estermannThreeHalvesNormMass a q := by
      unfold estermannThreeHalvesNormMass
      apply tsum_congr
      intro n
      exact norm_estermannTerm_three_halves_add_I_mul a q n t

/-- The complete initial Abel--Estermann integrand is genuinely integrable,
not merely assigned a total Bochner integral. -/
theorem integrable_initialAbelEstermann
    (x : ℝ) (hx : 0 < x) (a q : ℕ) :
    Integrable (fun t : ℝ =>
      (x : ℂ) ^ (-(((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) *
        Complex.Gamma (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        estermannDirichletSeries a q
          (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) := by
  let C : ℝ := x ^ (-(3 / 2 : ℝ)) * estermannThreeHalvesNormMass a q
  have hmajor : Integrable (fun t : ℝ => C * gammaThreeHalvesMajorant t) :=
    integrable_gammaThreeHalvesMajorant.const_mul C
  apply Integrable.mono' hmajor
  · have hrows : ∀ n : ℕ, AEStronglyMeasurable
        (abelMellinEstermannTerm a q x n) := fun n =>
      (integrable_abelMellinEstermannTerm a q hx n).aestronglyMeasurable
    have hsum : AEStronglyMeasurable
        (fun t : ℝ => ∑' n : ℕ, abelMellinEstermannTerm a q x n t) :=
      AEStronglyMeasurable.tsum hrows
    exact hsum.congr (Eventually.of_forall fun t =>
      tsum_abelMellinEstermannTerm a q x t)
  · filter_upwards [] with t
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    have hGamma := norm_Gamma_three_halves_add_I_mul_le_majorant t
    have hD := norm_estermannDirichletSeries_threeHalves_le a q t
    have hxpow : 0 ≤ x ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hx.le _
    have hmajorNonneg : 0 ≤ gammaThreeHalvesMajorant t := by
      unfold gammaThreeHalvesMajorant
      positivity
    have hfirst := mul_le_mul hGamma hD (norm_nonneg _) hmajorNonneg
    have htotal := mul_le_mul_of_nonneg_left hfirst hxpow
    simpa [C, mul_assoc, mul_left_comm, mul_comm] using htotal

/-- On the left side of the canonical rectangle, the normalized reflected
integrand is the negative of the initial Abel--Mellin integrand with the
vertical parameter reversed. -/
theorem normalizedAbel_leftVertical_integrand
    (x : ℝ) (a q : ℕ) [NeZero q] (t : ℝ) :
    estermannWeightedIntegrand a q
        (bettinConreyNormalizedAbelReflectionWeight x)
        (estermannVerticalPoint (-1 / 2 : ℝ) t) =
      -((x : ℂ) ^
          (-(((3 / 2 : ℝ) : ℂ) + (-t : ℂ) * I)) *
        Complex.Gamma (((3 / 2 : ℝ) : ℂ) + (-t : ℂ) * I) *
        estermannDirichletSeries a q
          (((3 / 2 : ℝ) : ℂ) + (-t : ℂ) * I)) := by
  rw [normalizedWeightedIntegrand_eq_neg_rawReflected]
  unfold bettinConreyRawAbelReflectionWeight estermannVerticalPoint
  have hs : 1 < ((((3 / 2 : ℝ) : ℂ) + (-t : ℂ) * I)).re := by
    norm_num
  have harg :
      1 - (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) =
        ((3 / 2 : ℝ) : ℂ) + (-t : ℂ) * I := by
    push_cast
    ring
  have hpow :
      (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) - 1 =
        -(((3 / 2 : ℝ) : ℂ) + (-t : ℂ) * I) := by
    push_cast
    ring
  rw [harg, estermannHurwitzContinuation_eq_dirichletSeries a q hs, hpow]
  ring

/-- Exact Mellin identification of the left vertical line.  In the
unit-residue convention it is `-2*pi` times the damped Estermann series. -/
theorem normalizedAbel_leftVerticalIntegral_eq_damped
    (x : ℝ) (hx : 0 < x) (a q : ℕ) [NeZero q] :
    estermannPrimalVerticalIntegral a q (-1 / 2 : ℝ)
        (bettinConreyNormalizedAbelReflectionWeight x) =
      -(2 * Real.pi : ℝ) * dampedEstermannLambertSeries a q x := by
  let F : ℝ → ℂ := fun t =>
    (x : ℂ) ^ (-(((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) *
      Complex.Gamma (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
      estermannDirichletSeries a q
        (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
  have hraw : (∫ t : ℝ, F t) =
      (2 * Real.pi : ℝ) * dampedEstermannLambertSeries a q x := by
    simpa [F] using abelEstermannMellinIdentity a q hx
  unfold estermannPrimalVerticalIntegral
  rw [show (fun t : ℝ =>
      bettinConreyNormalizedAbelReflectionWeight x
          (estermannVerticalPoint (-1 / 2 : ℝ) t) *
        estermannHurwitzContinuation a q
          (1 - estermannVerticalPoint (-1 / 2 : ℝ) t)) =
      fun t : ℝ => -(F (-t)) by
    funext t
    simpa [F] using normalizedAbel_leftVertical_integrand x a q t]
  rw [integral_neg]
  rw [integral_neg_eq_self]
  rw [hraw]
  push_cast
  ring

/-- Hence the left-line integrability field in the infinite-contour package
is unconditional; only the transformed right line and horizontal pair need
additional estimates. -/
theorem integrable_normalizedAbel_leftVertical
    (x : ℝ) (hx : 0 < x) (a q : ℕ) [NeZero q] :
    Integrable (fun t : ℝ =>
      estermannWeightedIntegrand a q
        (bettinConreyNormalizedAbelReflectionWeight x)
        (estermannVerticalPoint (-1 / 2 : ℝ) t)) := by
  let F : ℝ → ℂ := fun t =>
    (x : ℂ) ^ (-(((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) *
      Complex.Gamma (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
      estermannDirichletSeries a q
        (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
  have hF : Integrable F := by
    simpa [F] using integrable_initialAbelEstermann x hx a q
  have hneg : Integrable (fun t : ℝ => -(F (-t))) := hF.comp_neg.neg
  exact hneg.congr (Eventually.of_forall fun t => by
    simpa [F] using (normalizedAbel_leftVertical_integrand x a q t).symm)

/-- The only analytic limit data left after the finite rectangle and the
left-line Mellin identity have been proved.  Left-line integrability is now a
theorem, so the package asks only for the transformed right line and the
coupled horizontal pair. -/
structure BettinConreyAbelContourLimitData
    (x : ℝ) (a q : ℕ) [NeZero q] where
  right_integrable : Integrable (fun t : ℝ =>
    estermannWeightedIntegrand a q
      (bettinConreyNormalizedAbelReflectionWeight x)
      (estermannVerticalPoint (3 / 2 : ℝ) t))
  horizontal_pair_vanishes : Tendsto
    (symmetricHorizontalEdges
      (estermannWeightedIntegrand a q
        (bettinConreyNormalizedAbelReflectionWeight x))
      (-1 / 2 : ℝ) (3 / 2 : ℝ)) atTop (𝓝 0)

/-- The genuine finite two-pole rectangle plus the two remaining limit statements
construct the standard infinite Estermann contour shift. -/
noncomputable def BettinConreyAbelContourLimitData.toEvaluationContourShift
    {x : ℝ} (hx : 0 < x) {a q : ℕ} [NeZero q]
    (H : BettinConreyAbelContourLimitData x a q) :
    EstermannEvaluationContourShift a q
      (bettinConreyNormalizedAbelReflectionWeight x)
      (-1 / 2 : ℝ) (3 / 2 : ℝ) where
  weight_differentiableAt_zero :=
    differentiableAt_normalizedAbelReflectionWeight_zero x hx
  weight_unitResidueAt_one :=
    hasUnitResidueAtOne_normalizedAbelReflectionWeight x hx
  left_of_zero := by norm_num
  right_of_one := by norm_num
  boundary_eq_two_residues := fun T hT =>
    bettinConreyAbel_twoPoleRectangle x hx a q T hT
  left_vertical_converges :=
    tendsto_truncatedVerticalIntegral_of_integrable _ _
      (integrable_normalizedAbel_leftVertical x hx a q)
  right_vertical_converges :=
    tendsto_truncatedVerticalIntegral_of_integrable _ _ H.right_integrable
  horizontal_pair_vanishes := H.horizontal_pair_vanishes

/-- Exact infinite contour identity with the left Lambert row substituted.
This is the completed contour part of Phase 2; no boundary limit in the
damping parameter is used here. -/
theorem BettinConreyAbelContourLimitData.rightVertical_eq_damped_add_residues
    {x : ℝ} (hx : 0 < x) {a q : ℕ} [NeZero q]
    (H : BettinConreyAbelContourLimitData x a q) :
    estermannPrimalVerticalIntegral a q (3 / 2 : ℝ)
        (bettinConreyNormalizedAbelReflectionWeight x) =
      -(2 * Real.pi : ℝ) * dampedEstermannLambertSeries a q x +
        2 * Real.pi *
          (estermannWeightedResidueCoefficient a q
              (bettinConreyNormalizedAbelReflectionWeight x) +
            estermannHurwitzContinuation a q 0) := by
  rw [(H.toEvaluationContourShift hx).primalVerticalIntegral_eq,
    normalizedAbel_leftVerticalIntegral_eq_damped x hx a q]

/-- Coprimality converts the right line to the normalized dual kernel.  This
is the exact pre-Voronoi formula produced by the Abel contour: the damped
Lambert row and the zero residue remain coupled to the dual integral. -/
theorem BettinConreyAbelContourLimitData.continuation_zero_eq_dual_add_damped
    {x : ℝ} (hx : 0 < x) {a q : ℕ} [NeZero q]
    (H : BettinConreyAbelContourLimitData x a q)
    (hcop : Nat.Coprime a q) :
    estermannHurwitzContinuation a q 0 =
      (estermannDualVerticalIntegral a q hcop (3 / 2 : ℝ)
          (bettinConreyNormalizedAbelReflectionWeight x) +
        (2 * Real.pi : ℝ) * dampedEstermannLambertSeries a q x) /
          (2 * Real.pi) -
        estermannWeightedResidueCoefficient a q
          (bettinConreyNormalizedAbelReflectionWeight x) := by
  rw [(H.toEvaluationContourShift hx).value_eq_dual_difference hcop,
    normalizedAbel_leftVerticalIntegral_eq_damped x hx a q]
  ring

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelContourLimit
