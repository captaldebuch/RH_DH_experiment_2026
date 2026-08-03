import RiemannHypothesis.Criteria.NymanBeurling.H15CenteredAggregateEstimate

/-!
# H15: exact reduction to cutoff Möbius--sawtooth sums

This module establishes the finite algebraic part of the reciprocal-phase
programme.  The BBLS Bernoulli inner sum is exactly a cutoff Möbius--sawtooth
sum at parameter `A = m*h`; consequently every finite Fourier partial is an
explicit weighted sum of those one-variable objects.

This is not yet a bound for the centered H15 residual.  The outer mode sum has
a `1/m` weight and is only conditionally convergent, so a pointwise uniform
estimate for `mobiusSawtoothSum` alone cannot be promoted to an H15 estimate
without an additional summation/cancellation argument.
-/

namespace RH.Criteria.NymanBeurling.QuadraticInteraction

open RH.Criteria.NymanBeurling.CutoffMobiusKernels
open RH.Criteria.NymanBeurling.VasyuninGram

/-- The cutoff Möbius--sawtooth sum suggested by the reciprocal-phase route.
For H15 it is evaluated at the structured parameters `A = m*h`, rather than
uniformly at arbitrary, independently chosen cell weights. -/
noncomputable def mobiusSawtoothSum (N A : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N,
    ((ArithmeticFunction.moebius k : ℤ) : ℝ) * cutoffWeight N k *
      bernoulliB1 ((A : ℝ) / (k : ℝ))

/-- The BBLS inner sum is exactly the negative cutoff Möbius--sawtooth sum.
This is the rigorous finite reduction behind the proposed reciprocal-phase
programme. -/
theorem cutoffMobiusBernoulliInner_eq_neg_mobiusSawtoothSum
    (N m h : ℕ) :
    cutoffMobiusBernoulliInner N m h =
      -mobiusSawtoothSum N (m * h) := by
  unfold cutoffMobiusBernoulliInner mobiusSawtoothSum cutoffMobiusCoeff
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  ring

/-- Rewriting a single positive BBLS Fourier mode in terms of the exact
one-variable cutoff Möbius--sawtooth sums. -/
theorem cutoffMobiusBernoulliMode_eq_mobiusSawtoothSum
    (N m : ℕ) :
    cutoffMobiusBernoulliMode N m =
      2 * ((∑ h ∈ Finset.Icc 1 N,
        cutoffMobiusCoeff N h / (h : ℝ) *
          mobiusSawtoothSum N (m * h)) / (m : ℝ)) := by
  unfold cutoffMobiusBernoulliMode
  simp_rw [cutoffMobiusBernoulliInner_eq_neg_mobiusSawtoothSum]
  simp_rw [mul_neg]
  rw [Finset.sum_neg_distrib]
  ring

/-- Every finite BBLS correlation partial is an explicitly weighted sum of
the cutoff Möbius--sawtooth sums.  The displayed outer `1/m` factor is why a
mere pointwise bound for the inner sums is insufficient for Phase 1. -/
theorem cutoffMobiusBernoulliCorrelationPartial_eq_mobiusSawtoothSum
    (N M : ℕ) :
    cutoffMobiusBernoulliCorrelationPartial N M =
      2 * ∑ m ∈ Finset.Icc 1 M,
        ((∑ h ∈ Finset.Icc 1 N,
          cutoffMobiusCoeff N h / (h : ℝ) *
            mobiusSawtoothSum N (m * h)) / (m : ℝ)) := by
  rw [cutoffMobiusBernoulliCorrelationPartial_eq_mode_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  exact cutoffMobiusBernoulliMode_eq_mobiusSawtoothSum N m

/-- The centered H15 mode partial written entirely in terms of the exact
cutoff Möbius--sawtooth sums.  The finite parameter `M` is retained because
the outer harmonic mode series is conditionally, not absolutely, convergent. -/
noncomputable def h15CenteredSawtoothModePartial (N M : ℕ) : ℝ :=
  explicitQuadraticLogRatioComponent N +
    2 * ∑ m ∈ Finset.Icc 1 M,
      ((∑ h ∈ Finset.Icc 1 N,
        cutoffMobiusCoeff N h / (h : ℝ) *
          mobiusSawtoothSum N (m * h)) / (m : ℝ)) -
      1 + 2 * (explicitLinearMobiusSum N + 1)

/-- The centered partial is exactly the existing BBLS centered partial;
this rewrites its Fourier contribution into the one-variable sawtooth form. -/
theorem h15CenteredSawtoothModePartial_eq_centeredPartial
    (N M : ℕ) :
    h15CenteredSawtoothModePartial N M =
      cutoffMobiusBernoulliCenteredPartial N M := by
  unfold h15CenteredSawtoothModePartial cutoffMobiusBernoulliCenteredPartial
  rw [← cutoffMobiusBernoulliCorrelationPartial_eq_mobiusSawtoothSum]

/-- The actual centered H15 sawtooth residual is the ordinary partial-sum
limit of its explicit Möbius--sawtooth mode partials.  This completes the
algebraic/convergence reduction; a quantitative rate for this limit is the
separate Route A2 problem. -/
theorem h15CenteredSawtoothModePartial_tendsto
    (N : ℕ) :
    Filter.Tendsto (h15CenteredSawtoothModePartial N) Filter.atTop
      (nhds (h15CenteredSawtoothResidual N)) := by
  have h := cutoffMobiusBernoulliCenteredPartial_tendsto N
  rw [cutoffMobiusDefectEnergy_sub_loggamma_eq_bernoulli_value] at h
  apply h.congr'
  filter_upwards [] with M
  exact (h15CenteredSawtoothModePartial_eq_centeredPartial N M).symm

end RH.Criteria.NymanBeurling.QuadraticInteraction
