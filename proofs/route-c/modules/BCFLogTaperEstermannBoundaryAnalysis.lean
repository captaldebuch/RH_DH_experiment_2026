import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannVerticalBounds
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannTwoPoleRectangle

/-!
# Route B7.5: boundary analysis for the Gaussian two-pole contour

This module proves the reusable horizontal-edge estimate needed by the H15
Estermann contour.  A uniform bound on the two horizontal sides by `M(T)`
implies a bound by the rectangle width times `M(T)`; if `M(T) → 0`, the
coupled oriented horizontal pair vanishes.

The meromorphic two-residue identity is kept separate from decay.  The
reusable subtraction theorem in `BCFLogTaperEstermannTwoPoleRectangle` proves
it from Cauchy--Goursat and exact rational pole integrals; the Gaussian H15
integrand instantiates that theorem in the downstream subtraction module.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannBoundaryAnalysis

open Complex Filter Set Topology MeasureTheory
open scoped Interval Real
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannHurwitz
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannContourShift
open RH.Criteria.NymanBeurling.BCFLogTaperBettinConreyAggregate
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVerticalBounds
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannTwoPoleRectangle

/-- A common pointwise bound for the upper and lower horizontal sides at one
fixed height. -/
def HasSymmetricHorizontalBoundAt
    (f : ℂ → ℂ) (σL σR : ℝ) (M : ℝ → ℝ) (T : ℝ) : Prop :=
  ∀ x ∈ Set.Icc σL σR,
    ‖f ((x : ℂ) + (T : ℂ) * I)‖ ≤ M T ∧
      ‖f ((x : ℂ) - (T : ℂ) * I)‖ ≤ M T

/-- A common pointwise majorant for the upper and lower horizontal sides of
a symmetric rectangle at every nonnegative height.  This legacy predicate is
stronger than the eventual version below. -/
def HasSymmetricHorizontalMajorant
    (f : ℂ → ℂ) (σL σR : ℝ) (M : ℝ → ℝ) : Prop :=
  ∀ T : ℝ, 0 ≤ T → HasSymmetricHorizontalBoundAt f σL σR M T

/-- The asymptotically sufficient horizontal hypothesis.  It deliberately
places no condition at bounded heights, where an evaluation kernel can have
a pole on the real segment. -/
def HasEventuallySymmetricHorizontalMajorant
    (f : ℂ → ℂ) (σL σR : ℝ) (M : ℝ → ℝ) : Prop :=
  ∀ᶠ T : ℝ in atTop,
    0 ≤ T ∧ HasSymmetricHorizontalBoundAt f σL σR M T

/-- The lower horizontal edge is bounded by its length times the common
majorant. -/
theorem norm_rectangularLowerEdge_le
    (f : ℂ → ℂ) (σL σR T : ℝ) (M : ℝ → ℝ)
    (hσ : σL ≤ σR) (hT : 0 ≤ T)
    (H : HasSymmetricHorizontalMajorant f σL σR M) :
    ‖rectangularLowerEdge f (symmetricLowerCorner σL T)
        (symmetricUpperCorner σR T)‖ ≤
      M T * |σR - σL| := by
  have hinterval := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x : ℝ => f ((x : ℂ) - (T : ℂ) * I))
    (a := σL) (b := σR) (C := M T) (fun x hx => by
      apply (H T hT x ?_).2
      have hx' := Set.uIoc_subset_uIcc hx
      simpa [Set.uIcc_of_le hσ] using hx')
  simpa [rectangularLowerEdge, symmetricLowerCorner,
    symmetricUpperCorner, sub_eq_add_neg] using hinterval

/-- The lower-edge estimate only uses the pointwise hypothesis at the
current height. -/
theorem norm_rectangularLowerEdge_le_of_boundAt
    (f : ℂ → ℂ) (σL σR T : ℝ) (M : ℝ → ℝ)
    (hσ : σL ≤ σR)
    (H : HasSymmetricHorizontalBoundAt f σL σR M T) :
    ‖rectangularLowerEdge f (symmetricLowerCorner σL T)
        (symmetricUpperCorner σR T)‖ ≤
      M T * |σR - σL| := by
  have hinterval := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x : ℝ => f ((x : ℂ) - (T : ℂ) * I))
    (a := σL) (b := σR) (C := M T) (fun x hx => by
      apply (H x ?_).2
      have hx' := Set.uIoc_subset_uIcc hx
      simpa [Set.uIcc_of_le hσ] using hx')
  simpa [rectangularLowerEdge, symmetricLowerCorner,
    symmetricUpperCorner, sub_eq_add_neg] using hinterval

/-- The same bound for the oppositely oriented upper edge. -/
theorem norm_rectangularUpperEdge_le
    (f : ℂ → ℂ) (σL σR T : ℝ) (M : ℝ → ℝ)
    (hσ : σL ≤ σR) (hT : 0 ≤ T)
    (H : HasSymmetricHorizontalMajorant f σL σR M) :
    ‖rectangularUpperEdge f (symmetricLowerCorner σL T)
        (symmetricUpperCorner σR T)‖ ≤
      M T * |σR - σL| := by
  have hinterval := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x : ℝ => f ((x : ℂ) + (T : ℂ) * I))
    (a := σL) (b := σR) (C := M T) (fun x hx => by
      apply (H T hT x ?_).1
      have hx' := Set.uIoc_subset_uIcc hx
      simpa [Set.uIcc_of_le hσ] using hx')
  simpa [rectangularUpperEdge, symmetricLowerCorner,
    symmetricUpperCorner] using hinterval

/-- The upper-edge estimate only uses the pointwise hypothesis at the
current height. -/
theorem norm_rectangularUpperEdge_le_of_boundAt
    (f : ℂ → ℂ) (σL σR T : ℝ) (M : ℝ → ℝ)
    (hσ : σL ≤ σR)
    (H : HasSymmetricHorizontalBoundAt f σL σR M T) :
    ‖rectangularUpperEdge f (symmetricLowerCorner σL T)
        (symmetricUpperCorner σR T)‖ ≤
      M T * |σR - σL| := by
  have hinterval := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x : ℝ => f ((x : ℂ) + (T : ℂ) * I))
    (a := σL) (b := σR) (C := M T) (fun x hx => by
      apply (H x ?_).1
      have hx' := Set.uIoc_subset_uIcc hx
      simpa [Set.uIcc_of_le hσ] using hx')
  simpa [rectangularUpperEdge, symmetricLowerCorner,
    symmetricUpperCorner] using hinterval

/-- The coupled pair costs at most twice the horizontal length. -/
theorem norm_symmetricHorizontalEdges_le
    (f : ℂ → ℂ) (σL σR T : ℝ) (M : ℝ → ℝ)
    (hσ : σL ≤ σR) (hT : 0 ≤ T)
    (H : HasSymmetricHorizontalMajorant f σL σR M) :
    ‖symmetricHorizontalEdges f σL σR T‖ ≤
      2 * |σR - σL| * M T := by
  have hlower := norm_rectangularLowerEdge_le f σL σR T M hσ hT H
  have hupper := norm_rectangularUpperEdge_le f σL σR T M hσ hT H
  have hadd := norm_add_le
    (rectangularLowerEdge f (symmetricLowerCorner σL T)
      (symmetricUpperCorner σR T))
    (rectangularUpperEdge f (symmetricLowerCorner σL T)
      (symmetricUpperCorner σR T))
  unfold symmetricHorizontalEdges
  nlinarith [abs_nonneg (σR - σL)]

/-- The coupled pair estimate at one height. -/
theorem norm_symmetricHorizontalEdges_le_of_boundAt
    (f : ℂ → ℂ) (σL σR T : ℝ) (M : ℝ → ℝ)
    (hσ : σL ≤ σR)
    (H : HasSymmetricHorizontalBoundAt f σL σR M T) :
    ‖symmetricHorizontalEdges f σL σR T‖ ≤
      2 * |σR - σL| * M T := by
  have hlower := norm_rectangularLowerEdge_le_of_boundAt
    f σL σR T M hσ H
  have hupper := norm_rectangularUpperEdge_le_of_boundAt
    f σL σR T M hσ H
  have hadd := norm_add_le
    (rectangularLowerEdge f (symmetricLowerCorner σL T)
      (symmetricUpperCorner σR T))
    (rectangularUpperEdge f (symmetricLowerCorner σL T)
      (symmetricUpperCorner σR T))
  unfold symmetricHorizontalEdges
  nlinarith [abs_nonneg (σR - σL)]

/-- Any horizontal majorant tending to zero discharges the coupled
horizontal-edge field in the infinite contour package. -/
theorem horizontal_pair_vanishes_of_majorant
    (f : ℂ → ℂ) (σL σR : ℝ) (M : ℝ → ℝ)
    (hσ : σL ≤ σR)
    (H : HasSymmetricHorizontalMajorant f σL σR M)
    (hM : Tendsto M atTop (𝓝 0)) :
    Tendsto (symmetricHorizontalEdges f σL σR) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hnonneg : ∀ᶠ T : ℝ in atTop, 0 ≤ T := eventually_ge_atTop 0
  have hupper : ∀ᶠ T : ℝ in atTop,
      ‖symmetricHorizontalEdges f σL σR T‖ ≤
        2 * |σR - σL| * M T := by
    filter_upwards [hnonneg] with T hT
    exact norm_symmetricHorizontalEdges_le f σL σR T M hσ hT H
  have htend : Tendsto (fun T : ℝ => 2 * |σR - σL| * M T)
      atTop (𝓝 0) := by
    simpa using
      (tendsto_const_nhds.mul hM :
        Tendsto (fun T : ℝ => (2 * |σR - σL|) * M T) atTop
          (𝓝 ((2 * |σR - σL|) * 0)))
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hupper htend

/-- Eventual horizontal control is sufficient for the infinite contour
limit.  No artificial bound near the evaluation pole at height zero is
required. -/
theorem horizontal_pair_vanishes_of_eventual_majorant
    (f : ℂ → ℂ) (σL σR : ℝ) (M : ℝ → ℝ)
    (hσ : σL ≤ σR)
    (H : HasEventuallySymmetricHorizontalMajorant f σL σR M)
    (hM : Tendsto M atTop (𝓝 0)) :
    Tendsto (symmetricHorizontalEdges f σL σR) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hupper : ∀ᶠ T : ℝ in atTop,
      ‖symmetricHorizontalEdges f σL σR T‖ ≤
        2 * |σR - σL| * M T := by
    filter_upwards [H] with T hT
    exact norm_symmetricHorizontalEdges_le_of_boundAt
      f σL σR T M hσ hT.2
  have htend : Tendsto (fun T : ℝ => 2 * |σR - σL| * M T)
      atTop (𝓝 0) := by
    simpa using
      (tendsto_const_nhds.mul hM :
        Tendsto (fun T : ℝ => (2 * |σR - σL|) * M T) atTop
          (𝓝 ((2 * |σR - σL|) * 0)))
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hupper htend

/-- The exact two-residue boundary identity still required for one reduced
Estermann fraction.  This is pole geometry, not a cancellation estimate. -/
structure EstermannTwoPoleBoundaryIdentity
    (a q : ℕ) [NeZero q] (W : ℂ → ℂ) (σL σR : ℝ) where
  boundary_eq : ∀ T : ℝ, 0 < T →
    rectangularBoundaryIntegral (estermannWeightedIntegrand a q W)
      (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) =
        2 * Real.pi * I *
          (estermannWeightedResidueCoefficient a q W +
            estermannHurwitzContinuation a q 0)

/-- A genuine global subtraction at `s = 0, 1` supplies the exact Estermann
two-pole boundary identity.  The double-pole coefficient does not enter the
boundary value because its rectangular integral is zero. -/
noncomputable def EstermannTwoPoleBoundaryIdentity.of_subtraction
    {a q : ℕ} [NeZero q] {W : ℂ → ℂ} {σL σR : ℝ}
    (hL : σL < 0) (hR : 1 < σR)
    (H : TwoPoleRectangleSubtraction
      (estermannWeightedIntegrand a q W))
    (hzero : H.residueAtZero =
      estermannWeightedResidueCoefficient a q W)
    (hone : H.residueAtOne =
      estermannHurwitzContinuation a q 0) :
    EstermannTwoPoleBoundaryIdentity a q W σL σR where
  boundary_eq T hT := by
    rw [H.boundary_eq σL σR T hL hR hT, hzero, hone]

/-- Concrete analytic data sufficient to build the complete two-pole contour
shift.  Vertical convergence and horizontal vanishing are consequences, not
fields, once the displayed majorants are supplied. -/
structure EstermannGaussianContourData
    (a q : ℕ) [NeZero q] (W : ℂ → ℂ) (σL σR : ℝ) where
  weight_differentiableAt_zero : DifferentiableAt ℂ W 0
  weight_unitResidueAt_one : HasUnitResidueAtOne W
  left_of_zero : σL < 0
  right_of_one : 1 < σR
  boundary : EstermannTwoPoleBoundaryIdentity a q W σL σR
  leftEta : ℝ
  leftEta_pos : 0 < leftEta
  leftC : ℝ
  left_measurable : AEStronglyMeasurable
    (fun t : ℝ => estermannWeightedIntegrand a q W
      (estermannVerticalPoint σL t))
  left_majorant : HasGaussianVerticalMajorant
    (estermannWeightedIntegrand a q W) σL leftEta leftC
  rightEta : ℝ
  rightEta_pos : 0 < rightEta
  rightC : ℝ
  right_measurable : AEStronglyMeasurable
    (fun t : ℝ => estermannWeightedIntegrand a q W
      (estermannVerticalPoint σR t))
  right_majorant : HasGaussianVerticalMajorant
    (estermannWeightedIntegrand a q W) σR rightEta rightC
  horizontalMajorant : ℝ → ℝ
  horizontal_bound : HasSymmetricHorizontalMajorant
    (estermannWeightedIntegrand a q W) σL σR horizontalMajorant
  horizontal_tendsto_zero : Tendsto horizontalMajorant atTop (𝓝 0)

/-- Step 2 reduction: Gaussian contour data canonically inhabits the exact
two-pole shift used by the H15 aggregation. -/
noncomputable def EstermannGaussianContourData.toEvaluationContourShift
    {a q : ℕ} [NeZero q] {W : ℂ → ℂ} {σL σR : ℝ}
    (H : EstermannGaussianContourData a q W σL σR) :
    EstermannEvaluationContourShift a q W σL σR where
  weight_differentiableAt_zero := H.weight_differentiableAt_zero
  weight_unitResidueAt_one := H.weight_unitResidueAt_one
  left_of_zero := H.left_of_zero
  right_of_one := H.right_of_one
  boundary_eq_two_residues := H.boundary.boundary_eq
  left_vertical_converges :=
    estermannVerticalIntegral_converges_of_gaussianMajorant
      a q W σL H.leftEta H.leftC H.leftEta_pos
        H.left_measurable H.left_majorant
  right_vertical_converges :=
    estermannVerticalIntegral_converges_of_gaussianMajorant
      a q W σR H.rightEta H.rightC H.rightEta_pos
        H.right_measurable H.right_majorant
  horizontal_pair_vanishes :=
    horizontal_pair_vanishes_of_majorant
      (estermannWeightedIntegrand a q W) σL σR H.horizontalMajorant
        (le_trans H.left_of_zero.le (by linarith [H.right_of_one]))
        H.horizontal_bound H.horizontal_tendsto_zero

/-- Analytic contour data with the asymptotically natural horizontal
hypothesis.  Unlike `EstermannGaussianContourData`, it does not demand a
pointwise bound at small heights, where the real horizontal segment can meet
the evaluation pole at `s = 1`. -/
structure EstermannAsymptoticGaussianContourData
    (a q : ℕ) [NeZero q] (W : ℂ → ℂ) (σL σR : ℝ) where
  weight_differentiableAt_zero : DifferentiableAt ℂ W 0
  weight_unitResidueAt_one : HasUnitResidueAtOne W
  left_of_zero : σL < 0
  right_of_one : 1 < σR
  boundary : EstermannTwoPoleBoundaryIdentity a q W σL σR
  leftEta : ℝ
  leftEta_pos : 0 < leftEta
  leftC : ℝ
  left_measurable : AEStronglyMeasurable
    (fun t : ℝ => estermannWeightedIntegrand a q W
      (estermannVerticalPoint σL t))
  left_majorant : HasGaussianVerticalMajorant
    (estermannWeightedIntegrand a q W) σL leftEta leftC
  rightEta : ℝ
  rightEta_pos : 0 < rightEta
  rightC : ℝ
  right_measurable : AEStronglyMeasurable
    (fun t : ℝ => estermannWeightedIntegrand a q W
      (estermannVerticalPoint σR t))
  right_majorant : HasGaussianVerticalMajorant
    (estermannWeightedIntegrand a q W) σR rightEta rightC
  horizontalMajorant : ℝ → ℝ
  horizontal_bound : HasEventuallySymmetricHorizontalMajorant
    (estermannWeightedIntegrand a q W) σL σR horizontalMajorant
  horizontal_tendsto_zero : Tendsto horizontalMajorant atTop (𝓝 0)

/-- Eventual Gaussian contour data canonically supplies the exact infinite
two-pole contour shift used by the H15 aggregation. -/
noncomputable def EstermannAsymptoticGaussianContourData.toEvaluationContourShift
    {a q : ℕ} [NeZero q] {W : ℂ → ℂ} {σL σR : ℝ}
    (H : EstermannAsymptoticGaussianContourData a q W σL σR) :
    EstermannEvaluationContourShift a q W σL σR where
  weight_differentiableAt_zero := H.weight_differentiableAt_zero
  weight_unitResidueAt_one := H.weight_unitResidueAt_one
  left_of_zero := H.left_of_zero
  right_of_one := H.right_of_one
  boundary_eq_two_residues := H.boundary.boundary_eq
  left_vertical_converges :=
    estermannVerticalIntegral_converges_of_gaussianMajorant
      a q W σL H.leftEta H.leftC H.leftEta_pos
        H.left_measurable H.left_majorant
  right_vertical_converges :=
    estermannVerticalIntegral_converges_of_gaussianMajorant
      a q W σR H.rightEta H.rightC H.rightEta_pos
        H.right_measurable H.right_majorant
  horizontal_pair_vanishes :=
    horizontal_pair_vanishes_of_eventual_majorant
      (estermannWeightedIntegrand a q W) σL σR H.horizontalMajorant
        (le_trans H.left_of_zero.le (by linarith [H.right_of_one]))
        H.horizontal_bound H.horizontal_tendsto_zero

/-- The legacy all-height data is stronger than the eventual-height data. -/
noncomputable def EstermannGaussianContourData.toAsymptotic
    {a q : ℕ} [NeZero q] {W : ℂ → ℂ} {σL σR : ℝ}
    (H : EstermannGaussianContourData a q W σL σR) :
    EstermannAsymptoticGaussianContourData a q W σL σR where
  weight_differentiableAt_zero := H.weight_differentiableAt_zero
  weight_unitResidueAt_one := H.weight_unitResidueAt_one
  left_of_zero := H.left_of_zero
  right_of_one := H.right_of_one
  boundary := H.boundary
  leftEta := H.leftEta
  leftEta_pos := H.leftEta_pos
  leftC := H.leftC
  left_measurable := H.left_measurable
  left_majorant := H.left_majorant
  rightEta := H.rightEta
  rightEta_pos := H.rightEta_pos
  rightC := H.rightC
  right_measurable := H.right_measurable
  right_majorant := H.right_majorant
  horizontalMajorant := H.horizontalMajorant
  horizontal_bound := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact ⟨hT, H.horizontal_bound T hT⟩
  horizontal_tendsto_zero := H.horizontal_tendsto_zero

/-- Uniform Gaussian contour data for every reduced interior H15 fraction. -/
structure H15GaussianContourFamilyData
    (W : ℂ → ℂ) (σL σR : ℝ) where
  data : ∀ (a q : ℕ) (hcop : Nat.Coprime a q) (hq : 2 ≤ q),
    @EstermannGaussianContourData
      (inverseResidueNumerator a q hcop) q
      ⟨Nat.ne_of_gt (by omega)⟩ W σL σR

/-- Uniform eventual-height Gaussian contour data for every reduced interior
H15 fraction. -/
structure H15AsymptoticGaussianContourFamilyData
    (W : ℂ → ℂ) (σL σR : ℝ) where
  data : ∀ (a q : ℕ) (hcop : Nat.Coprime a q) (hq : 2 ≤ q),
    @EstermannAsymptoticGaussianContourData
      (inverseResidueNumerator a q hcop) q
      ⟨Nat.ne_of_gt (by omega)⟩ W σL σR

/-- Such a family supplies the exact contour family consumed by the finite
H15 reconstruction theorem. -/
noncomputable def H15GaussianContourFamilyData.toEvaluationContourFamily
    {W : ℂ → ℂ} {σL σR : ℝ}
    (H : H15GaussianContourFamilyData W σL σR) :
    H15EvaluationContourFamily W σL σR where
  shift a q hcop hq := by
    letI : NeZero q := ⟨by omega⟩
    exact (H.data a q hcop hq).toEvaluationContourShift

/-- The asymptotically natural family also supplies the exact contour family
consumed by the finite H15 reconstruction theorem. -/
noncomputable def H15AsymptoticGaussianContourFamilyData.toEvaluationContourFamily
    {W : ℂ → ℂ} {σL σR : ℝ}
    (H : H15AsymptoticGaussianContourFamilyData W σL σR) :
    H15EvaluationContourFamily W σL σR where
  shift a q hcop hq := by
    letI : NeZero q := ⟨by omega⟩
    exact (H.data a q hcop hq).toEvaluationContourShift

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannBoundaryAnalysis
