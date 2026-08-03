import RiemannHypothesis.Criteria.NymanBeurling.QuadraticInteraction

/-!
# Corrected H15 centered aggregate interface

The earlier Farey-cell correlation interfaces quantified over independent
weights (including point masses) and demanded a logarithmic saving for every
individual cell.  Such an estimate cannot be the H15 input: the actual
kernel produces one coupled, `N`-dependent aggregate, and its main terms must
remain paired before cancellation is estimated.

This module freezes that exact aggregate in the normalization already used by
the quadratic-interaction finish.  It is deliberately a single analytic
number-theory target.  In particular, it does not claim that a generic
averaged-Chowla, logarithmically averaged, or DFI statement implies the
bound; theorem matching is a prerequisite for any such bridge.
-/

namespace RH.Criteria.NymanBeurling.QuadraticInteraction

open RH.Criteria.NymanBeurling.CutoffMobiusKernels

/-- The signed, centered H15 expression after the finite Farey and Fourier
bookkeeping has been aggregated with the specific cutoff-Möbius weights.  The
log-ratio, Bernoulli, and linear terms are intentionally kept in one absolute
value: bounding them separately loses the cancellation required by H15. -/
noncomputable def h15CenteredSawtoothResidual (N : ℕ) : ℝ :=
  explicitQuadraticLogRatioComponent N +
    cutoffMobiusBernoulliCorrelationValue N - 1 +
      2 * (explicitLinearMobiusSum N + 1)

/-- The complete aggregate controlled by the corrected H15 estimate.  The
smooth log-gamma component is included because the norm-residual endgame
needs the total mass of this package, not a cellwise estimate. -/
noncomputable def h15CenteredAggregateResidual (N : ℕ) : ℝ :=
  |explicitQuadraticLogGammaComponent N| + |h15CenteredSawtoothResidual N|

/-- The Phase 0 name for the exact residual.  It is definitionally the same
quantity as `h15CenteredAggregateResidual`; the separate name makes clear that
this is the object to reduce analytically before selecting a proof route. -/
noncomputable def h15CenteredResidual (N : ℕ) : ℝ :=
  |explicitQuadraticLogGammaComponent N| + |h15CenteredSawtoothResidual N|

theorem h15CenteredResidual_eq_aggregateResidual (N : ℕ) :
    h15CenteredResidual N = h15CenteredAggregateResidual N :=
  rfl

/-- The Phase 0 H15 hypothesis, stated directly in terms of the exact
centered residual.  Nonnegativity, rather than strict positivity, permits the
sharp case in which the residual vanishes. -/
structure H15CenteredResidualBound where
  C_residual : ℝ
  C_residual_nonneg : 0 ≤ C_residual
  residual_bound :
    ∀ N : ℕ,
      h15CenteredResidual N ≤
        C_residual / Real.log (N + 2 : ℝ) ^ 2

/-- The centered sawtooth component of H15, isolated from the smooth
log-gamma term.  This is the output genuinely targeted by the
Möbius--sawtooth, Vaaler, and reciprocal-phase routes. -/
structure H15CenteredSawtoothBound where
  C_sawtooth : ℝ
  C_sawtooth_nonneg : 0 ≤ C_sawtooth
  sawtooth_bound :
    ∀ N : ℕ,
      |h15CenteredSawtoothResidual N| ≤
        C_sawtooth / Real.log (N + 2 : ℝ) ^ 2

/-- The smooth log-gamma component of H15, isolated from the oscillatory
sawtooth problem. -/
structure H15CenteredSmoothLogGammaBound where
  C_smooth : ℝ
  C_smooth_nonneg : 0 ≤ C_smooth
  smooth_bound :
    ∀ N : ℕ,
      |explicitQuadraticLogGammaComponent N| ≤
        C_smooth / Real.log (N + 2 : ℝ) ^ 2

/-- The pre-existing smooth-product H15 interface supplies the smooth half
of the Phase 0 residual package without adding new analysis. -/
noncomputable def h15CenteredSmoothLogGammaBound_of_smoothProduct
    {H : MobiusSummatory.ClassicalMertensDecay}
    (S : QuadraticInteractionSmoothProductLogSqEstimate H) :
    H15CenteredSmoothLogGammaBound :=
  { C_smooth := S.C_smooth
    C_smooth_nonneg := S.C_smooth_nonneg
    smooth_bound := S.smooth_product_bound }

/-- Recombine the genuinely separate smooth and sawtooth estimates into the
exact Phase 0 residual estimate. -/
noncomputable def h15CenteredResidualBound_of_smooth_and_sawtooth
    (H_smooth : H15CenteredSmoothLogGammaBound)
    (H_sawtooth : H15CenteredSawtoothBound) :
    H15CenteredResidualBound :=
  { C_residual := H_smooth.C_smooth + H_sawtooth.C_sawtooth
    C_residual_nonneg :=
      add_nonneg H_smooth.C_smooth_nonneg H_sawtooth.C_sawtooth_nonneg
    residual_bound := by
      intro N
      unfold h15CenteredResidual
      calc
        |explicitQuadraticLogGammaComponent N| +
            |h15CenteredSawtoothResidual N|
          ≤ H_smooth.C_smooth / Real.log (N + 2 : ℝ) ^ 2 +
              H_sawtooth.C_sawtooth / Real.log (N + 2 : ℝ) ^ 2 :=
            add_le_add (H_smooth.smooth_bound N) (H_sawtooth.sawtooth_bound N)
        _ = (H_smooth.C_smooth + H_sawtooth.C_sawtooth) /
            Real.log (N + 2 : ℝ) ^ 2 := by ring }

/--
The sole content-bearing H15 input in the corrected final route.

It is an aggregate estimate for the specific cutoff-Möbius kernel, uniformly
in its cutoff `N`; it has no quantification over arbitrary weights, Farey
cells, or affine forms.  A future analytic proof may derive it through a
Vaaler reciprocal-phase reduction, but that derivation is not asserted here.
-/
structure H15CenteredAggregateEstimate where
  C_aggregate : ℝ
  C_aggregate_nonneg : 0 ≤ C_aggregate
  aggregate_bound :
    ∀ N : ℕ,
      h15CenteredAggregateResidual N ≤
        C_aggregate / Real.log (N + 2 : ℝ) ^ 2

/-- Convert the Phase 0 residual interface to the existing final H15
aggregate interface.  This is an exact repackaging, with no analytic content.
-/
noncomputable def h15CenteredAggregateEstimate_of_residualBound
    (H_residual : H15CenteredResidualBound) : H15CenteredAggregateEstimate :=
  { C_aggregate := H_residual.C_residual
    C_aggregate_nonneg := H_residual.C_residual_nonneg
    aggregate_bound := by
      intro N
      rw [← h15CenteredResidual_eq_aggregateResidual]
      exact H_residual.residual_bound N }

/-- The corrected aggregate is definitionally the existing centered
Möbius--Bernoulli package.  This is a bookkeeping conversion, not an
additional analytic assertion. -/
noncomputable def quadraticInteractionBernoulliCorrelationEstimate_of_h15CenteredAggregate
    (H_decay : MobiusSummatory.ClassicalMertensDecay)
    (H_aggregate : H15CenteredAggregateEstimate) :
    QuadraticInteractionBernoulliCorrelationEstimate H_decay :=
  { C_correlation := H_aggregate.C_aggregate
    C_correlation_nonneg := H_aggregate.C_aggregate_nonneg
    centered_correlation_bound := by
      intro N
      simpa [h15CenteredAggregateResidual, h15CenteredSawtoothResidual] using
        H_aggregate.aggregate_bound N }

/-- The corrected aggregate directly discharges the norm-residual interface
used by the established H15 finish. -/
noncomputable def quadraticInteractionNormResidual_of_h15CenteredAggregate
    (H_decay : MobiusSummatory.ClassicalMertensDecay)
    (H_aggregate : H15CenteredAggregateEstimate) :
    QuadraticInteractionNormResidual :=
  quadraticInteractionNormResidual_of_bernoulliCorrelation H_decay
    (quadraticInteractionBernoulliCorrelationEstimate_of_h15CenteredAggregate
      H_decay H_aggregate)

/-- Phase 0 closes directly: the exact centered-residual bound gives the
norm-residual interface without assuming a particular analytic proof of that
bound. -/
noncomputable def quadraticInteractionNormResidual_of_h15CenteredResidual_bound
    (H_residual : H15CenteredResidualBound) :
    QuadraticInteractionNormResidual := by
  let logTwo := Real.log (2 : ℝ)
  refine
    { C_norm := H_residual.C_residual / logTwo
      C_norm_nonneg := div_nonneg H_residual.C_residual_nonneg
        (Real.log_pos (by norm_num)).le
      norm_loggamma_package_bound := ?_ }
  intro N
  rw [cutoffMobiusDefectEnergy_sub_loggamma_eq_bernoulli_value]
  have hresidual := H_residual.residual_bound N
  rw [h15CenteredResidual] at hresidual
  have hlogTwo : 0 < logTwo := Real.log_pos (by norm_num)
  have hlogN : 0 < Real.log (N + 2 : ℝ) := Real.log_pos (by norm_cast; omega)
  have hmono : logTwo ≤ Real.log (N + 2 : ℝ) := by
    exact Real.log_le_log (by norm_num) (by norm_cast; omega)
  have hratio :
      H_residual.C_residual / Real.log (N + 2 : ℝ) ≤
        H_residual.C_residual / logTwo :=
    div_le_div_of_nonneg_left H_residual.C_residual_nonneg hlogTwo hmono
  calc
    |explicitQuadraticLogGammaComponent N| +
          |explicitQuadraticLogRatioComponent N +
              cutoffMobiusBernoulliCorrelationValue N - 1 +
                2 * (explicitLinearMobiusSum N + 1)|
        ≤ H_residual.C_residual / Real.log (N + 2 : ℝ) ^ 2 := hresidual
    _ = (H_residual.C_residual / Real.log (N + 2 : ℝ)) /
          Real.log (N + 2 : ℝ) := by ring
    _ ≤ (H_residual.C_residual / logTwo) /
          Real.log (N + 2 : ℝ) :=
      div_le_div_of_nonneg_right hratio hlogN.le

/-- H14 decay and the corrected H15 aggregate yield the existing quadratic
interaction estimates. -/
noncomputable def quadraticInteractionEstimates_of_decay_and_h15CenteredAggregate
    (H_decay : MobiusSummatory.ClassicalMertensDecay)
    (H_aggregate : H15CenteredAggregateEstimate) :
    QuadraticInteractionEstimates :=
  quadraticInteractionEstimates_of_mertens_and_normResidual
    (MobiusSummatory.ClassicalMertensAPI.ofDecayOnly H_decay)
    (quadraticInteractionNormResidual_of_h15CenteredAggregate H_decay H_aggregate)

end RH.Criteria.NymanBeurling.QuadraticInteraction
