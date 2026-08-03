import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannModulusSeparation
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmCompensator

/-!
# Route B9.6: correction-coupled bilinear pivot

The ordinary Kuznetsov separation audit fails because the inverse-coordinate
phase depends jointly on `(q,m)`.  This file therefore names the exact
bilinear coefficient that a replacement trace/dispersion theorem must
transform.  It proves, without a convergence split, that retaining the
completion zero mode together with this joint coefficient recovers the full
physical-kernel aggregate.

No trace formula or decay estimate is asserted.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannBilinearTraceTarget

open Complex ZMod
open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperBettinConreyAggregate
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannAtZeroReduction
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannH15MellinAssembly
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannModulusSeparation
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannRegularizedKernels
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannSeries
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCompensator

/-- The exact same-sign, nonzero-frequency bilinear coefficient.  Its
`e_q(-m a⁻¹) S_q(n,m)` dependence is retained inside the joint kernel. -/
noncomputable def h15SameSignJointBilinearCoefficient
    (N g q : ℕ) [NeZero q] (n : ℕ) : ℂ :=
  estermannDivisorCoeff n * (q : ℂ)⁻¹ * h15ModulusScalar N g q *
    ∑ a ∈ Finset.Icc 2 (N / g),
      if hcop : Nat.Coprime a q then
        h15NumeratorScalar N g a *
          h15SameSignJointCompletedKernel a q hcop n
      else 0

/-- The exact opposite-sign, nonzero-frequency bilinear coefficient. -/
noncomputable def h15OppositeSignJointBilinearCoefficient
    (N g q : ℕ) [NeZero q] (n : ℕ) : ℂ :=
  estermannDivisorCoeff n * (q : ℂ)⁻¹ * h15ModulusScalar N g q *
    ∑ a ∈ Finset.Icc 2 (N / g),
      if hcop : Nat.Coprime a q then
        h15NumeratorScalar N g a *
          h15OppositeSignJointCompletedKernel a q hcop n
      else 0

theorem h15SameSignJointBilinearCoefficient_eq_nonzeroMode
    (N g q : ℕ) [NeZero q] (n : ℕ) :
    h15SameSignJointBilinearCoefficient N g q n =
      h15SameSignNonzeroModeCoefficient N g q n := by
  exact (h15SameSignNonzeroModeCoefficient_eq_numeratorJointSum N g q n).symm

theorem h15OppositeSignJointBilinearCoefficient_eq_nonzeroMode
    (N g q : ℕ) [NeZero q] (n : ℕ) :
    h15OppositeSignJointBilinearCoefficient N g q n =
      h15OppositeSignNonzeroModeCoefficient N g q n := by
  exact (h15OppositeSignNonzeroModeCoefficient_eq_numeratorJointSum N g q n).symm

/-- The zero mode must remain coupled to the joint same-sign coefficient.
Splitting their infinite kernel series would require extra summability
hypotheses and would obscure their exact Ramanujan cancellation. -/
noncomputable def h15SameSignZeroCorrectedBilinearCoefficient
    (N g q : ℕ) [NeZero q] (n : ℕ) : ℂ :=
  h15SameSignZeroModeCoefficient N g q n +
    h15SameSignJointBilinearCoefficient N g q n

noncomputable def h15OppositeSignZeroCorrectedBilinearCoefficient
    (N g q : ℕ) [NeZero q] (n : ℕ) : ℂ :=
  h15OppositeSignZeroModeCoefficient N g q n +
    h15OppositeSignJointBilinearCoefficient N g q n

theorem h15SameSignZeroCorrectedBilinearCoefficient_eq_completed
    (N g q : ℕ) [NeZero q] (n : ℕ) :
    h15SameSignZeroCorrectedBilinearCoefficient N g q n =
      h15SameSignCompletedCoefficient N g q n := by
  unfold h15SameSignZeroCorrectedBilinearCoefficient
  rw [h15SameSignCompletedCoefficient_eq_zero_add_nonzero,
    h15SameSignJointBilinearCoefficient_eq_nonzeroMode]

theorem h15OppositeSignZeroCorrectedBilinearCoefficient_eq_completed
    (N g q : ℕ) [NeZero q] (n : ℕ) :
    h15OppositeSignZeroCorrectedBilinearCoefficient N g q n =
      h15OppositeSignCompletedCoefficient N g q n := by
  unfold h15OppositeSignZeroCorrectedBilinearCoefficient
  rw [h15OppositeSignCompletedCoefficient_eq_zero_add_nonzero,
    h15OppositeSignJointBilinearCoefficient_eq_nonzeroMode]

theorem h15SameSignZeroCorrectedBilinearCoefficient_eq_additive
    (N g q : ℕ) [NeZero q] (n : ℕ) :
    h15SameSignZeroCorrectedBilinearCoefficient N g q n =
      h15SameSignSeparatedAdditiveCoefficient N g q n := by
  unfold h15SameSignZeroCorrectedBilinearCoefficient
  rw [h15SameSignJointBilinearCoefficient_eq_nonzeroMode,
    h15SameSign_zero_add_nonzero_eq_separatedAdditive]

theorem h15OppositeSignZeroCorrectedBilinearCoefficient_eq_additive
    (N g q : ℕ) [NeZero q] (n : ℕ) :
    h15OppositeSignZeroCorrectedBilinearCoefficient N g q n =
      h15OppositeSignSeparatedAdditiveCoefficient N g q n := by
  unfold h15OppositeSignZeroCorrectedBilinearCoefficient
  rw [h15OppositeSignJointBilinearCoefficient_eq_nonzeroMode,
    h15OppositeSign_zero_add_nonzero_eq_separatedAdditive]

/-- Same-sign physical-kernel series with the zero and joint nonzero modes
kept in one coefficient. -/
noncomputable def h15SameSignZeroCorrectedBilinearKernelSeries
    (N g q : ℕ) [NeZero q] (η c : ℝ) : ℂ :=
  ∑' n : ℕ, h15SameSignZeroCorrectedBilinearCoefficient N g q n *
    ((2 * Real.pi : ℂ) * h15SameSignMellinKernel η c q n)

noncomputable def h15OppositeSignZeroCorrectedBilinearKernelSeries
    (N g q : ℕ) [NeZero q] (η c : ℝ) : ℂ :=
  ∑' n : ℕ, h15OppositeSignZeroCorrectedBilinearCoefficient N g q n *
    ((2 * Real.pi : ℂ) * h15OppositeSignMellinKernel η c q n)

noncomputable def h15TwoSignZeroCorrectedBilinearKernelSeries
    (N g q : ℕ) [NeZero q] (η c : ℝ) : ℂ :=
  h15SameSignZeroCorrectedBilinearKernelSeries N g q η c +
    h15OppositeSignZeroCorrectedBilinearKernelSeries N g q η c

theorem h15SameSignCompletedKernelSeries_eq_zeroCorrectedBilinear
    (N g q : ℕ) [NeZero q] (η c : ℝ) :
    h15SameSignCompletedKernelSeries N g q η c =
      h15SameSignZeroCorrectedBilinearKernelSeries N g q η c := by
  unfold h15SameSignCompletedKernelSeries
    h15SameSignZeroCorrectedBilinearKernelSeries
  apply tsum_congr
  intro n
  rw [h15SameSignZeroCorrectedBilinearCoefficient_eq_completed]

theorem h15OppositeSignCompletedKernelSeries_eq_zeroCorrectedBilinear
    (N g q : ℕ) [NeZero q] (η c : ℝ) :
    h15OppositeSignCompletedKernelSeries N g q η c =
      h15OppositeSignZeroCorrectedBilinearKernelSeries N g q η c := by
  unfold h15OppositeSignCompletedKernelSeries
    h15OppositeSignZeroCorrectedBilinearKernelSeries
  apply tsum_congr
  intro n
  rw [h15OppositeSignZeroCorrectedBilinearCoefficient_eq_completed]

theorem h15TwoSignCompletedKernelSeries_eq_zeroCorrectedBilinear
    (N g q : ℕ) [NeZero q] (η c : ℝ) :
    h15TwoSignCompletedKernelSeries N g q η c =
      h15TwoSignZeroCorrectedBilinearKernelSeries N g q η c := by
  unfold h15TwoSignCompletedKernelSeries
    h15TwoSignZeroCorrectedBilinearKernelSeries
  rw [h15SameSignCompletedKernelSeries_eq_zeroCorrectedBilinear,
    h15OppositeSignCompletedKernelSeries_eq_zeroCorrectedBilinear]

/-- The exact full fixed-`N` object to which a generalised bilinear trace
formula (or the reverse-completion dispersion route) must be applied. -/
noncomputable def h15InteriorZeroCorrectedBilinearKernelAggregate
    (N : ℕ) (η c : ℝ) : ℂ :=
  ∑ g ∈ Finset.Icc 1 N,
    ∑ q ∈ Finset.Icc 2 (N / g),
      if hq : 0 < q then
        @h15TwoSignZeroCorrectedBilinearKernelSeries N g q
          ⟨Nat.ne_of_gt hq⟩ η c
      else 0

/-- The pivot loses no terms: the exact joint bilinear aggregate is the WP3
physical-kernel aggregate. -/
theorem h15InteriorCompletedKernelAggregate_eq_zeroCorrectedBilinear
    (N : ℕ) (η c : ℝ) :
    h15InteriorCompletedKernelAggregate N η c =
      h15InteriorZeroCorrectedBilinearKernelAggregate N η c := by
  classical
  unfold h15InteriorCompletedKernelAggregate
    h15InteriorZeroCorrectedBilinearKernelAggregate
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro q hqmem
  have hq : 0 < q := by
    have := (Finset.mem_Icc.mp hqmem).1
    omega
  rw [dif_pos hq, dif_pos hq]
  exact @h15TwoSignCompletedKernelSeries_eq_zeroCorrectedBilinear N g q
    ⟨Nat.ne_of_gt hq⟩ η c

/-- WP2/WP3a therefore land exactly on the correction-coupled bilinear
pivot, with no pointwise or global remainder. -/
theorem h15Interior_integral_eq_zeroCorrectedBilinearKernelAggregate
    (N : ℕ) (η c : ℝ) (hη : 0 < η) (hc : 1 < c) :
    (∫ t : ℝ,
      h15InteriorNaturalDualIntegrand N
        (estermannGaussianEvaluationWeight η)
        (estermannVerticalPoint c t)) =
      h15InteriorZeroCorrectedBilinearKernelAggregate N η c := by
  rw [h15Interior_integral_eq_completedKernelAggregate N η c hη hc,
    h15InteriorCompletedKernelAggregate_eq_zeroCorrectedBilinear]

/-! ## Exact route pivot at the complete H15 expression -/

/-- Before the unfinished physical-kernel contour shift, the complete
Estermann expression is already exactly the complete Ehm balanced/far
expression.  This permits a rigorous reverse-completion pivot, but it does
not assert that either Ehm sector is separately small. -/
theorem estermannFullExpression_eq_ehmBalancedCore_add_far
    (H : EstermannAtZeroPackage) (N : ℕ) :
    estermannInteriorElementaryExpression N +
          (estermannInteriorValueAggregate H N).im +
          estermannEndpointCompletedExpression H N =
      ehmS1BalancedCoupledCore N + ehmS1OneSidedFarRatioSum N := by
  rw [← coupledGcdRatioExpression_eq_elementary_add_value_im_add_endpoint H N,
    coupledGcdRatioExpression_eq_ehmS1BalancedCore_add_far]

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannBilinearTraceTarget
