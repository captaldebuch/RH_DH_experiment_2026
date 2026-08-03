import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannGaussianSubtraction

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannGaussianAssembly

open Complex Filter Set Topology MeasureTheory
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannContourShift
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannBoundaryAnalysis
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannGaussianSubtraction
open RH.Criteria.NymanBeurling.BCFLogTaperBettinConreyAggregate

theorem continuous_estermannGaussianWeightedIntegrand_vertical
    (η : ℝ) (a q : ℕ) [NeZero q] (σ : ℝ)
    (hσ0 : σ ≠ 0) (hσ1 : σ ≠ 1) :
    Continuous (fun t : ℝ =>
      estermannWeightedIntegrand a q
        (estermannGaussianEvaluationWeight η)
        (estermannVerticalPoint σ t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hp1 : estermannVerticalPoint σ t ≠ (1 : ℂ) := by
    intro h
    have hre := congrArg Complex.re h
    simp [estermannVerticalPoint] at hre
    exact hσ1 hre
  have hp0 : estermannVerticalPoint σ t ≠ (0 : ℂ) := by
    intro h
    have hre := congrArg Complex.re h
    simp [estermannVerticalPoint] at hre
    exact hσ0 hre
  have hW : DifferentiableAt ℂ (estermannGaussianEvaluationWeight η)
      (estermannVerticalPoint σ t) := by
    unfold estermannGaussianEvaluationWeight estermannEvaluationWeight
    have hnum : DifferentiableAt ℂ (estermannGaussianDamping η)
        (estermannVerticalPoint σ t) := by
      unfold estermannGaussianDamping
      fun_prop
    exact hnum.div (by fun_prop) (sub_ne_zero.mpr hp1)
  have hf := differentiableAt_estermannWeightedIntegrand a q
    (estermannGaussianEvaluationWeight η) hW hp0
  have hp : ContinuousAt (estermannVerticalPoint σ) t := by
    unfold estermannVerticalPoint
    fun_prop
  simpa [Function.comp_def] using hf.continuousAt.comp hp

theorem aestronglyMeasurable_estermannGaussianWeightedIntegrand_vertical
    (η : ℝ) (a q : ℕ) [NeZero q] (σ : ℝ)
    (hσ0 : σ ≠ 0) (hσ1 : σ ≠ 1) :
    AEStronglyMeasurable (fun t : ℝ =>
      estermannWeightedIntegrand a q
        (estermannGaussianEvaluationWeight η)
        (estermannVerticalPoint σ t)) :=
  (continuous_estermannGaussianWeightedIntegrand_vertical
    η a q σ hσ0 hσ1).aestronglyMeasurable

structure ReducedEstermannGaussianMajorants
    (η : ℝ) (a q : ℕ) [NeZero q] (σL σR : ℝ) where
  leftEta : ℝ
  leftEta_pos : 0 < leftEta
  leftC : ℝ
  left_majorant : HasGaussianVerticalMajorant
    (estermannWeightedIntegrand a q
      (estermannGaussianEvaluationWeight η)) σL leftEta leftC
  rightEta : ℝ
  rightEta_pos : 0 < rightEta
  rightC : ℝ
  right_majorant : HasGaussianVerticalMajorant
    (estermannWeightedIntegrand a q
      (estermannGaussianEvaluationWeight η)) σR rightEta rightC
  horizontalMajorant : ℝ → ℝ
  horizontal_bound : HasEventuallySymmetricHorizontalMajorant
    (estermannWeightedIntegrand a q
      (estermannGaussianEvaluationWeight η)) σL σR horizontalMajorant
  horizontal_tendsto_zero : Tendsto horizontalMajorant atTop (𝓝 0)

structure H15GaussianMajorantFamilyData
    (η σL σR : ℝ) where
  eta_pos : 0 < η
  left_of_zero : σL < 0
  right_of_one : 1 < σR
  estimates : ∀ (a q : ℕ) (hcop : Nat.Coprime a q) (hq : 2 ≤ q),
    @ReducedEstermannGaussianMajorants η
      (inverseResidueNumerator a q hcop) q
      ⟨Nat.ne_of_gt (by omega)⟩ σL σR

noncomputable def H15GaussianMajorantFamilyData.toAsymptoticContourFamily
    {η σL σR : ℝ} (H : H15GaussianMajorantFamilyData η σL σR) :
    H15AsymptoticGaussianContourFamilyData
      (estermannGaussianEvaluationWeight η) σL σR where
  data a q hcop hq := by
    letI : NeZero q := ⟨Nat.ne_of_gt (by omega)⟩
    let b := inverseResidueNumerator a q hcop
    let E := H.estimates a q hcop hq
    exact {
      weight_differentiableAt_zero :=
        differentiableAt_estermannGaussianEvaluationWeight_zero η
      weight_unitResidueAt_one :=
        hasUnitResidueAtOne_estermannGaussianEvaluationWeight η
      left_of_zero := H.left_of_zero
      right_of_one := H.right_of_one
      boundary := estermannGaussianTwoPoleBoundaryIdentity η b q σL σR
        H.left_of_zero H.right_of_one
      leftEta := E.leftEta
      leftEta_pos := E.leftEta_pos
      leftC := E.leftC
      left_measurable :=
        aestronglyMeasurable_estermannGaussianWeightedIntegrand_vertical
          η b q σL (ne_of_lt H.left_of_zero) (by linarith [H.left_of_zero])
      left_majorant := E.left_majorant
      rightEta := E.rightEta
      rightEta_pos := E.rightEta_pos
      rightC := E.rightC
      right_measurable :=
        aestronglyMeasurable_estermannGaussianWeightedIntegrand_vertical
          η b q σR (by linarith [H.right_of_one])
            (ne_of_gt H.right_of_one)
      right_majorant := E.right_majorant
      horizontalMajorant := E.horizontalMajorant
      horizontal_bound := E.horizontal_bound
      horizontal_tendsto_zero := E.horizontal_tendsto_zero
    }

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannGaussianAssembly
