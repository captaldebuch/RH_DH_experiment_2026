import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannContourShift
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperBettinConreyAggregate
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannAtZeroBridge
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Route B7.3: the two-pole contour needed to recover the H15 special value

The H15 interior contains the continued value `D(0,a⁻¹/q)`.  In the contour
variable used by the normalized Estermann functional equation this value is
`D(1-s,a⁻¹/q)` at `s = 1`.  Consequently a Mellin/Cauchy weight which extracts
the H15 value has a pole at `s = 1`.  A contour moving from `σL < 0` to
`1 < σR` therefore crosses two contributions:

* the intrinsic Estermann pole at `s = 0`, with the already proved canonical
  weighted residue; and
* the evaluation pole at `s = 1`, whose residue is exactly `D(0,a⁻¹/q)` for a
  unit-residue weight.

This file proves the local evaluation-residue limit and the exact infinite
two-pole contour identity.  It deliberately leaves the boundary theorem and
decay estimates as fields: those are the analytic inputs still needed for a
chosen H15 weight.  No Kuznetsov estimate is asserted.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour

open Complex Filter Topology MeasureTheory
open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannHurwitz
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannContourShift
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannAtZeroReduction
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannAtZeroBridge
open RH.Criteria.NymanBeurling.BCFLogTaperBettinConreyAggregate

/-! ## Separating the elementary and analytic interior terms -/

/-- The part of the primitive Gram kernel which does not contain an
Estermann special value. -/
noncomputable def estermannInteriorElementaryKernel (a b : ℕ) : ℝ :=
  (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / 2 *
      (1 / (a : ℝ) + 1 / (b : ℝ)) +
    ((b : ℝ) - (a : ℝ)) / (2 * (a : ℝ) * (b : ℝ)) *
      Real.log ((a : ℝ) / (b : ℝ))

/-- The complex coefficient which turns the imaginary part of the two
oriented Estermann values into the Vasyunin contribution. -/
noncomputable def estermannInteriorValueCoefficient
    (N g a b : ℕ) : ℂ :=
  (coprimeSliceCoefficient N g a b *
    Real.pi / ((a : ℝ) * (b : ℝ)) : ℝ)

/-- The elementary part of the full interior expression. -/
noncomputable def estermannInteriorElementaryExpression
    (N : ℕ) : ℝ :=
  ∑ g ∈ Finset.Icc 1 N,
    ∑ a ∈ Finset.Icc 1 (N / g),
      ∑ b ∈ Finset.Icc 1 (N / g),
        if Nat.Coprime a b ∧ 2 ≤ a ∧ 2 ≤ b then
          coprimeSliceCoefficient N g a b *
            estermannInteriorElementaryKernel a b
        else 0

/-- The special-value part of the interior expression, before taking its
imaginary part. -/
noncomputable def estermannInteriorValueAggregate
    (H : EstermannAtZeroPackage) (N : ℕ) : ℂ :=
  ∑ g ∈ Finset.Icc 1 N,
    ∑ a ∈ Finset.Icc 1 (N / g),
      ∑ b ∈ Finset.Icc 1 (N / g),
        if Nat.Coprime a b ∧ 2 ≤ a ∧ 2 ≤ b then
          estermannInteriorValueCoefficient N g a b *
            (H.value a b + H.value b a)
        else 0

/-- Pointwise separation of the primitive H15 kernel into its elementary
part and the imaginary part of the two oriented analytic values. -/
theorem weighted_estermannCoprimeGramKernel_eq
    (H : EstermannAtZeroPackage) (N g a b : ℕ) :
    coprimeSliceCoefficient N g a b *
        estermannCoprimeGramKernel H a b =
      coprimeSliceCoefficient N g a b *
          estermannInteriorElementaryKernel a b +
        (estermannInteriorValueCoefficient N g a b *
          (H.value a b + H.value b a)).im := by
  simp only [estermannCoprimeGramKernel,
    estermannInteriorElementaryKernel, estermannInteriorValueCoefficient,
    Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero]
  ring

/-- Exact global split of the automorphic interior into elementary terms and
one complex special-value aggregate. -/
theorem estermannInteriorExpression_eq_elementary_add_value_im
    (H : EstermannAtZeroPackage) (N : ℕ) :
    estermannInteriorExpression H N =
      estermannInteriorElementaryExpression N +
        (estermannInteriorValueAggregate H N).im := by
  classical
  unfold estermannInteriorExpression estermannInteriorCoprimeRatioSlice
    estermannInteriorElementaryExpression estermannInteriorValueAggregate
  simp only [Complex.im_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro g _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : Nat.Coprime a b ∧ 2 ≤ a ∧ 2 ≤ b
  · simp only [if_pos h]
    exact weighted_estermannCoprimeGramKernel_eq H N g a b
  · simp [h]

/-- The complete H15 target with all three pieces visible: elementary
interior, analytic special values, and the endpoint-completed correction. -/
theorem coupledGcdRatioExpression_eq_elementary_add_value_im_add_endpoint
    (H : EstermannAtZeroPackage) (N : ℕ) :
    RH.Criteria.NymanBeurling.BCFLogTaperSpectral.coupledGcdRatioExpression N =
      estermannInteriorElementaryExpression N +
        (estermannInteriorValueAggregate H N).im +
          estermannEndpointCompletedExpression H N := by
  rw [coupledGcdRatioExpression_eq_estermannInterior_add_endpointCompleted H,
    estermannInteriorExpression_eq_elementary_add_value_im H]

/-- The proof-carrying inverse representative used in B7.2 agrees with the
analytic inverse-residue convention used by the genuine Estermann package. -/
theorem inverseResidueNumerator_eq_inverseResidue
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q) :
    inverseResidueNumerator a q hcop = inverseResidue a q := by
  rfl

/-- An inverse-residue numerator remains coprime to its modulus. -/
theorem inverseResidueNumerator_coprime
    (a q : ℕ) (hcop : Nat.Coprime a q) :
    Nat.Coprime (inverseResidueNumerator a q hcop) q := by
  unfold inverseResidueNumerator
  exact ZMod.val_coe_unit_coprime ((ZMod.unitOfCoprime a hcop)⁻¹)

/-- A weight has normalized residue one at the evaluation point `s = 1`.
The punctured formulation permits the weight itself to have a pole there. -/
def HasUnitResidueAtOne (W : ℂ → ℂ) : Prop :=
  Tendsto (fun s : ℂ => (s - 1) * W s) (𝓝[≠] 1) (𝓝 1)

/-- A Cauchy evaluation kernel with an optional analytic damping factor.
The normalization `Φ 1 = 1` makes its residue at one equal to one. -/
noncomputable def estermannEvaluationWeight
    (Φ : ℂ → ℂ) (s : ℂ) : ℂ :=
  Φ s / (s - 1)

/-- A continuous damping factor normalized at one gives a unit-residue
evaluation weight. -/
theorem hasUnitResidueAtOne_estermannEvaluationWeight
    (Φ : ℂ → ℂ) (hΦ : ContinuousAt Φ 1) (hΦ1 : Φ 1 = 1) :
    HasUnitResidueAtOne (estermannEvaluationWeight Φ) := by
  have heventually :
      (fun s : ℂ => (s - 1) * estermannEvaluationWeight Φ s) =ᶠ[𝓝[≠] 1] Φ := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr (by simpa using hs)
    unfold estermannEvaluationWeight
    field_simp
  unfold HasUnitResidueAtOne
  simpa only [hΦ1] using
    (hΦ.tendsto.mono_left inf_le_left).congr' heventually.symm

/-- Differentiability of the damping factor at zero is inherited by the
evaluation weight there; its only introduced pole is at one. -/
theorem differentiableAt_estermannEvaluationWeight_zero
    (Φ : ℂ → ℂ) (hΦ : DifferentiableAt ℂ Φ 0) :
    DifferentiableAt ℂ (estermannEvaluationWeight Φ) 0 := by
  unfold estermannEvaluationWeight
  apply hΦ.div (by fun_prop)
  norm_num

/-- Gaussian damping centered at the evaluation pole.  On vertical lines its
norm has the factor `exp (-η t²)`, which is the natural choice for the next
uniform boundary estimates. -/
noncomputable def estermannGaussianDamping
    (η : ℝ) (s : ℂ) : ℂ :=
  Complex.exp ((η : ℂ) * (s - 1) ^ 2)

/-- The corresponding normalized Gaussian evaluation weight. -/
noncomputable def estermannGaussianEvaluationWeight
    (η : ℝ) (s : ℂ) : ℂ :=
  estermannEvaluationWeight (estermannGaussianDamping η) s

@[simp] theorem estermannGaussianDamping_one (η : ℝ) :
    estermannGaussianDamping η 1 = 1 := by
  simp [estermannGaussianDamping]

/-- The Gaussian evaluation weight has the required residue at one. -/
theorem hasUnitResidueAtOne_estermannGaussianEvaluationWeight (η : ℝ) :
    HasUnitResidueAtOne (estermannGaussianEvaluationWeight η) := by
  apply hasUnitResidueAtOne_estermannEvaluationWeight
  · unfold estermannGaussianDamping
    fun_prop
  · exact estermannGaussianDamping_one η

/-- The Gaussian evaluation weight is holomorphic at the intrinsic
Estermann pole. -/
theorem differentiableAt_estermannGaussianEvaluationWeight_zero (η : ℝ) :
    DifferentiableAt ℂ (estermannGaussianEvaluationWeight η) 0 := by
  apply differentiableAt_estermannEvaluationWeight_zero
  unfold estermannGaussianDamping
  fun_prop

/-- Exact Gaussian decay on a vertical line.  This isolates the exponential
gain available for the horizontal and vertical boundary estimates. -/
theorem norm_estermannGaussianDamping_vertical (η σ t : ℝ) :
    ‖estermannGaussianDamping η (estermannVerticalPoint σ t)‖ =
      Real.exp (η * ((σ - 1) ^ 2 - t ^ 2)) := by
  unfold estermannGaussianDamping
  rw [Complex.norm_exp]
  congr 1
  norm_num [estermannVerticalPoint, pow_two, Complex.mul_re]

/-! ## Gaussian majorants discharge the vertical-limit obligation -/

/-- A pointwise Gaussian majorant on one vertical line.  Polynomial factors
can be absorbed by weakening the Gaussian exponent before instantiating this
predicate. -/
def HasGaussianVerticalMajorant
    (f : ℂ → ℂ) (σ η C : ℝ) : Prop :=
  ∀ t : ℝ,
    ‖f (estermannVerticalPoint σ t)‖ ≤
      C * Real.exp (-η * t ^ 2)

/-- A measurable function with a positive Gaussian majorant is integrable on
the complete vertical parameter line. -/
theorem integrable_vertical_of_gaussianMajorant
    (f : ℂ → ℂ) (σ η C : ℝ)
    (hη : 0 < η)
    (hmeas : AEStronglyMeasurable
      (fun t : ℝ => f (estermannVerticalPoint σ t)))
    (hbound : HasGaussianVerticalMajorant f σ η C) :
    Integrable (fun t : ℝ => f (estermannVerticalPoint σ t)) := by
  have hmajor : Integrable
      (fun t : ℝ => C * Real.exp (-η * t ^ 2)) :=
    (integrable_exp_neg_mul_sq hη).const_mul C
  apply Integrable.mono' hmajor hmeas
  filter_upwards [] with t
  exact hbound t

/-- Integrability on a vertical line implies convergence of the symmetric
truncations used by the contour structures. -/
theorem tendsto_truncatedVerticalIntegral_of_integrable
    (f : ℂ → ℂ) (σ : ℝ)
    (hf : Integrable (fun t : ℝ => f (estermannVerticalPoint σ t))) :
    Tendsto (truncatedVerticalIntegral f σ) atTop
      (𝓝 (∫ t : ℝ, f (estermannVerticalPoint σ t))) := by
  simpa [truncatedVerticalIntegral, estermannVerticalPoint] using
    intervalIntegral_tendsto_integral hf tendsto_neg_atTop_atBot tendsto_id

/-- A Gaussian bound therefore supplies exactly the vertical-convergence
field required by the two-pole Estermann shift. -/
theorem estermannVerticalIntegral_converges_of_gaussianMajorant
    (a q : ℕ) [NeZero q] (W : ℂ → ℂ) (σ η C : ℝ)
    (hη : 0 < η)
    (hmeas : AEStronglyMeasurable
      (fun t : ℝ => estermannWeightedIntegrand a q W
        (estermannVerticalPoint σ t)))
    (hbound : HasGaussianVerticalMajorant
      (estermannWeightedIntegrand a q W) σ η C) :
    Tendsto (truncatedVerticalIntegral
      (estermannWeightedIntegrand a q W) σ) atTop
      (𝓝 (estermannPrimalVerticalIntegral a q σ W)) := by
  exact tendsto_truncatedVerticalIntegral_of_integrable _ _
    (integrable_vertical_of_gaussianMajorant _ _ _ _ hη hmeas hbound)

/-- A unit-residue evaluation weight extracts the continued Estermann value
at zero from the pole at `s = 1`. -/
theorem estermannWeightedIntegrand_evaluationResidue_limit
    (a q : ℕ) [NeZero q] (W : ℂ → ℂ)
    (hW : HasUnitResidueAtOne W) :
    Tendsto
      (fun s : ℂ => (s - 1) * estermannWeightedIntegrand a q W s)
      (𝓝[≠] 1) (𝓝 (estermannHurwitzContinuation a q 0)) := by
  have hD : Tendsto
      (fun s : ℂ => estermannHurwitzContinuation a q (1 - s))
      (𝓝[≠] 1) (𝓝 (estermannHurwitzContinuation a q 0)) := by
    have hcont : ContinuousAt
        (fun s : ℂ => estermannHurwitzContinuation a q (1 - s)) 1 := by
      apply (differentiableAt_estermannHurwitzContinuation a q (by norm_num)).continuousAt.comp
      fun_prop
    simpa using hcont.tendsto.mono_left inf_le_left
  have hmul := hW.mul hD
  simpa [HasUnitResidueAtOne, estermannWeightedIntegrand, mul_assoc] using hmul

/-- The exact analytic data for a contour which crosses both `s = 0` and the
evaluation point `s = 1`.  The zero residue is not freely chosen: it is the
canonical coefficient proved in the one-pole Laurent analysis. -/
structure EstermannEvaluationContourShift
    (a q : ℕ) [NeZero q] (W : ℂ → ℂ) (σL σR : ℝ) where
  weight_differentiableAt_zero : DifferentiableAt ℂ W 0
  weight_unitResidueAt_one : HasUnitResidueAtOne W
  left_of_zero : σL < 0
  right_of_one : 1 < σR
  boundary_eq_two_residues : ∀ T : ℝ, 0 < T →
    rectangularBoundaryIntegral (estermannWeightedIntegrand a q W)
      (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) =
        2 * Real.pi * I *
          (estermannWeightedResidueCoefficient a q W +
            estermannHurwitzContinuation a q 0)
  left_vertical_converges :
    Tendsto (truncatedVerticalIntegral
      (estermannWeightedIntegrand a q W) σL) atTop
      (𝓝 (estermannPrimalVerticalIntegral a q σL W))
  right_vertical_converges :
    Tendsto (truncatedVerticalIntegral
      (estermannWeightedIntegrand a q W) σR) atTop
      (𝓝 (estermannPrimalVerticalIntegral a q σR W))
  horizontal_pair_vanishes :
    Tendsto (symmetricHorizontalEdges
      (estermannWeightedIntegrand a q W) σL σR) atTop (𝓝 0)

/-- The complete vertical-line identity after crossing the intrinsic and
evaluation poles. -/
theorem EstermannEvaluationContourShift.primalVerticalIntegral_eq
    {a q : ℕ} [NeZero q] {W : ℂ → ℂ} {σL σR : ℝ}
    (H : EstermannEvaluationContourShift a q W σL σR) :
    estermannPrimalVerticalIntegral a q σR W =
      estermannPrimalVerticalIntegral a q σL W +
        2 * Real.pi *
          (estermannWeightedResidueCoefficient a q W +
            estermannHurwitzContinuation a q 0) := by
  exact verticalLimit_eq_of_rectangularBoundary
    (estermannWeightedIntegrand a q W) σL σR
    (estermannWeightedResidueCoefficient a q W +
      estermannHurwitzContinuation a q 0)
    (estermannPrimalVerticalIntegral a q σL W)
    (estermannPrimalVerticalIntegral a q σR W)
    H.boundary_eq_two_residues H.left_vertical_converges
      H.right_vertical_converges H.horizontal_pair_vanishes

/-- Solving the two-pole identity isolates the exact Estermann value needed
by H15. -/
theorem EstermannEvaluationContourShift.value_eq_primal_difference
    {a q : ℕ} [NeZero q] {W : ℂ → ℂ} {σL σR : ℝ}
    (H : EstermannEvaluationContourShift a q W σL σR) :
    estermannHurwitzContinuation a q 0 =
      (estermannPrimalVerticalIntegral a q σR W -
          estermannPrimalVerticalIntegral a q σL W) /
        (2 * Real.pi) - estermannWeightedResidueCoefficient a q W := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  rw [H.primalVerticalIntegral_eq]
  field_simp [hpi]
  ring

/-- On the right line, the normalized functional equation converts the
evaluation formula into the genuine pre-Voronoi form. -/
theorem EstermannEvaluationContourShift.value_eq_dual_difference
    {a q : ℕ} [NeZero q] {W : ℂ → ℂ} {σL σR : ℝ}
    (H : EstermannEvaluationContourShift a q W σL σR)
    (hcop : Nat.Coprime a q) :
    estermannHurwitzContinuation a q 0 =
      (estermannDualVerticalIntegral a q hcop σR W -
          estermannPrimalVerticalIntegral a q σL W) /
        (2 * Real.pi) - estermannWeightedResidueCoefficient a q W := by
  have hσR0 : 0 < σR := lt_trans (by norm_num) H.right_of_one
  have hσR1 : σR ≠ 1 := ne_of_gt H.right_of_one
  rw [← estermannPrimalVerticalIntegral_eq_dual
    a q hcop σR hσR0 hσR1 W]
  exact H.value_eq_primal_difference

/-! ## Finite aggregation over the H15 interior -/

/-- A uniform family of genuine two-pole shifts for every reduced H15
interior fraction.  Its only fields are the local analytic contour
obligations; finite aggregation will be proved below. -/
structure H15EvaluationContourFamily
    (W : ℂ → ℂ) (σL σR : ℝ) where
  shift : ∀ (a q : ℕ) (hcop : Nat.Coprime a q) (hq : 2 ≤ q),
    @EstermannEvaluationContourShift
      (inverseResidueNumerator a q hcop) q
      ⟨Nat.ne_of_gt (by omega)⟩ W σL σR

/-- The value reconstructed from the right dual line, left primal line, and
the canonical zero residue. -/
noncomputable def estermannContourRecoveredValue
    (W : ℂ → ℂ) (σL σR : ℝ)
    (a q : ℕ) (hcop : Nat.Coprime a q) (hq : 2 ≤ q) : ℂ := by
  letI : NeZero q :=
    ⟨Nat.ne_of_gt (by omega)⟩
  exact
    (estermannDualVerticalIntegral
          (inverseResidueNumerator a q hcop) q
          (inverseResidueNumerator_coprime a q hcop) σR W -
        estermannPrimalVerticalIntegral
          (inverseResidueNumerator a q hcop) q σL W) /
      (2 * Real.pi) -
        estermannWeightedResidueCoefficient
          (inverseResidueNumerator a q hcop) q W

/-- Every member of the contour family reconstructs the corresponding
analytic Estermann value at zero. -/
theorem H15EvaluationContourFamily.continuation_eq_recoveredValue
    {W : ℂ → ℂ} {σL σR : ℝ}
    (F : H15EvaluationContourFamily W σL σR)
    (a q : ℕ) (hcop : Nat.Coprime a q) (hq : 2 ≤ q) :
    @estermannHurwitzContinuation
        (inverseResidueNumerator a q hcop) q
        ⟨Nat.ne_of_gt (by omega)⟩ 0 =
      estermannContourRecoveredValue W σL σR a q hcop hq := by
  letI : NeZero q :=
    ⟨Nat.ne_of_gt (by omega)⟩
  exact (F.shift a q hcop hq).value_eq_dual_difference
    (inverseResidueNumerator_coprime a q hcop)

/-- The finite aggregate of all reconstructed special values in the H15
interior. -/
noncomputable def estermannInteriorRecoveredAggregate
    (W : ℂ → ℂ) (σL σR : ℝ) (N : ℕ) : ℂ :=
  ∑ g ∈ Finset.Icc 1 N,
    ∑ a ∈ Finset.Icc 1 (N / g),
      ∑ b ∈ Finset.Icc 1 (N / g),
        if hcop : Nat.Coprime a b then
          if ha : 2 ≤ a then
            if hb : 2 ≤ b then
              estermannInteriorValueCoefficient N g a b *
                (estermannContourRecoveredValue W σL σR a b hcop hb +
                  estermannContourRecoveredValue W σL σR b a hcop.symm ha)
            else 0
          else 0
        else 0

/-- Under a genuine contour family, the analytic special-value aggregate is
exactly the reconstructed contour aggregate. -/
theorem estermannInteriorValueAggregate_eq_recovered
    (HZ : HurwitzZetaZeroFormula)
    (HC : EstermannBernoulliCotangentIdentity)
    {W : ℂ → ℂ} {σL σR : ℝ}
    (F : H15EvaluationContourFamily W σL σR) (N : ℕ) :
    estermannInteriorValueAggregate
        (analyticEstermannAtZeroPackage HZ HC) N =
      estermannInteriorRecoveredAggregate W σL σR N := by
  classical
  unfold estermannInteriorValueAggregate estermannInteriorRecoveredAggregate
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hcop : Nat.Coprime a b
  · by_cases ha : 2 ≤ a
    · by_cases hb : 2 ≤ b
      · rw [if_pos ⟨hcop, ha, hb⟩, dif_pos hcop, dif_pos ha, dif_pos hb]
        letI : NeZero a := ⟨by omega⟩
        letI : NeZero b := ⟨by omega⟩
        apply congrArg (estermannInteriorValueCoefficient N g a b * ·)
        congr 1
        · change analyticEstermannAtZeroValue a b = _
          rw [analyticEstermannAtZeroValue_eq a b
              (by omega)]
          rw [← inverseResidueNumerator_eq_inverseResidue a b hcop]
          exact F.continuation_eq_recoveredValue a b hcop hb
        · change analyticEstermannAtZeroValue b a = _
          rw [analyticEstermannAtZeroValue_eq b a
              (by omega)]
          rw [← inverseResidueNumerator_eq_inverseResidue b a hcop.symm]
          exact F.continuation_eq_recoveredValue b a hcop.symm ha
      · simp [ha, hb]
    · simp [ha]
  · simp [hcop]

/-- The exact endpoint-coupled pre-Voronoi realization of the complete H15
expression.  Nothing is estimated: the theorem merely replaces every
interior special value by its two-line contour representation while retaining
the elementary and endpoint-completed terms. -/
theorem coupledGcdRatioExpression_eq_contourRecovered_add_endpoint
    (HZ : HurwitzZetaZeroFormula)
    (HC : EstermannBernoulliCotangentIdentity)
    {W : ℂ → ℂ} {σL σR : ℝ}
    (F : H15EvaluationContourFamily W σL σR) (N : ℕ) :
    RH.Criteria.NymanBeurling.BCFLogTaperSpectral.coupledGcdRatioExpression N =
      estermannInteriorElementaryExpression N +
        (estermannInteriorRecoveredAggregate W σL σR N).im +
          estermannEndpointCompletedExpression
            (analyticEstermannAtZeroPackage HZ HC) N := by
  rw [coupledGcdRatioExpression_eq_elementary_add_value_im_add_endpoint,
    estermannInteriorValueAggregate_eq_recovered HZ HC F]

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
