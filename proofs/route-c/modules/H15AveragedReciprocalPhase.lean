import RiemannHypothesis.Criteria.NymanBeurling.H15SawtoothAnalyticInterfaces

/-!
# Averaged-cutoff reciprocal phases for H15

This module isolates a mathematically weaker target than a pointwise-in-`N`
reciprocal-phase estimate.  The finite average is taken over the dyadic block
`[X, 2X]`.  A vanishing dyadic mean of a nonnegative majorant gives
arbitrarily large good cutoffs by a finite pigeonhole argument.

The architecture has three deliberately separate layers:

* `DyadicAverageDecay` contains the mean-value estimate;
* `AveragedUniformMobiusSawtoothEstimate` turns it into cofinally good
  cutoffs for the exact finite sawtooth sum; and
* `AveragedH15SawtoothLogReduction` records the still-essential conditional
  harmonic-mode summation needed to reach the centered H15 residual.

Vaaler approximation is **not** needed for the deterministic averaging
argument.  It appears only in
`AveragedReciprocalPhaseVaalerPackage`, an optional constructor of the direct
averaged sawtooth interface.  Thus a future mollified-Chowla or dispersion
proof can enter at the sawtooth layer without manufacturing Vaaler data.

No reciprocal-phase, Vaaler-error, or H15 cancellation estimate is asserted
in this file.  Those inputs remain explicit structures.
-/

namespace RH.Criteria.NymanBeurling.QuadraticInteraction

open Filter Topology

/-! ## Finite dyadic averaging -/

/-- The inclusive dyadic block of natural cutoffs `[X, 2X]`. -/
def h15DyadicCutoffBlock (X : ℕ) : Finset ℕ :=
  Finset.Icc X (2 * X)

theorem mem_h15DyadicCutoffBlock_self (X : ℕ) :
    X ∈ h15DyadicCutoffBlock X := by
  simp only [h15DyadicCutoffBlock, Finset.mem_Icc]
  omega

theorem h15DyadicCutoffBlock_nonempty (X : ℕ) :
    (h15DyadicCutoffBlock X).Nonempty :=
  ⟨X, mem_h15DyadicCutoffBlock_self X⟩

/-- A nonnegative sequence has vanishing dyadic average when its sum on
`[X,2X]` is bounded by the block cardinality times a null majorant.  The
cardinality-scaled form avoids any artificial division-by-zero convention. -/
structure DyadicAverageDecay (f : ℕ → ℝ) where
  f_nonneg : ∀ N, 0 ≤ f N
  eta : ℕ → ℝ
  eta_nonneg : ∀ X, 0 ≤ eta X
  eta_tendsto_zero : Tendsto eta atTop (nhds 0)
  sum_bound : ∀ X,
    ∑ N ∈ h15DyadicCutoffBlock X, f N ≤
      ((h15DyadicCutoffBlock X).card : ℝ) * eta X

/-- Finite pigeonhole principle in the normalization used by
`DyadicAverageDecay`: one term is no larger than the stated block mean. -/
theorem exists_mem_le_of_dyadic_sum_le
    (f : ℕ → ℝ) (X : ℕ) (a : ℝ)
    (havg : ∑ N ∈ h15DyadicCutoffBlock X, f N ≤
      ((h15DyadicCutoffBlock X).card : ℝ) * a) :
    ∃ N ∈ h15DyadicCutoffBlock X, f N ≤ a := by
  classical
  by_contra h
  push Not at h
  have hstrict :
      ∑ N ∈ h15DyadicCutoffBlock X, a <
        ∑ N ∈ h15DyadicCutoffBlock X, f N := by
    exact Finset.sum_lt_sum_of_nonempty (h15DyadicCutoffBlock_nonempty X) (by
      intro N hN
      exact h N hN)
  have hconst :
      ∑ _N ∈ h15DyadicCutoffBlock X, a =
        ((h15DyadicCutoffBlock X).card : ℝ) * a := by
    simp
  rw [hconst] at hstrict
  exact (not_lt_of_ge havg) hstrict

/-- A vanishing dyadic mean produces arbitrarily large pointwise-small
values.  This is the precise deterministic gain supplied by averaging in
the cutoff; it does not promote the conclusion to eventual pointwise decay. -/
theorem DyadicAverageDecay.cofinal_small
    {f : ℕ → ℝ} (H : DyadicAverageDecay f) :
    ∀ ε : ℝ, 0 < ε → ∀ N₀ : ℕ,
      ∃ N ≥ N₀, f N < ε := by
  intro ε hε N₀
  have heta := H.eta_tendsto_zero
  rw [Metric.tendsto_atTop] at heta
  obtain ⟨X₀, hX₀⟩ := heta ε hε
  let X := max X₀ N₀
  have hX₀_le : X₀ ≤ X := le_max_left _ _
  have hN₀_le : N₀ ≤ X := le_max_right _ _
  have heta_lt : H.eta X < ε := by
    have hdist := hX₀ X hX₀_le
    simpa [Real.dist_eq, abs_of_nonneg (H.eta_nonneg X)] using hdist
  obtain ⟨N, hNmem, hNle⟩ :=
    exists_mem_le_of_dyadic_sum_le f X (H.eta X) (H.sum_bound X)
  refine ⟨N, ?_, hNle.trans_lt heta_lt⟩
  exact hN₀_le.trans (Finset.mem_Icc.mp hNmem).1

/-! ## Averaged direct sawtooth target -/

/-- The direct averaged target for the exact cutoff Möbius--sawtooth sum.
The bound is uniform in `A` at each cutoff; only its behavior in `N` is
averaged. -/
structure AveragedUniformMobiusSawtoothEstimate where
  sawtoothMajorant : ℕ → ℝ
  uniformEstimate : UniformMobiusSawtoothEstimate sawtoothMajorant
  dyadicDecay : DyadicAverageDecay sawtoothMajorant

/-- Cofinal pointwise vanishing of the exact finite sawtooth family,
uniformly in the reciprocal numerator `A`. -/
structure CofinalUniformMobiusSawtoothVanishing where
  good_cutoff : ∀ ε : ℝ, 0 < ε → ∀ N₀ : ℕ,
    ∃ N ≥ N₀, ∀ A : ℕ, |mobiusSawtoothSum N A| < ε

/-- The only argument here is dyadic pigeonholing followed by the existing
uniform sawtooth majorant. -/
noncomputable def
    AveragedUniformMobiusSawtoothEstimate.toCofinalVanishing
    (H : AveragedUniformMobiusSawtoothEstimate) :
    CofinalUniformMobiusSawtoothVanishing where
  good_cutoff ε hε N₀ := by
    obtain ⟨N, hN, hmajorant⟩ := H.dyadicDecay.cofinal_small ε hε N₀
    refine ⟨N, hN, fun A ↦ ?_⟩
    exact (H.uniformEstimate.sawtooth_bound N A).trans_lt hmajorant

/-! ## Optional reciprocal-phase/Vaaler constructor -/

/-- An averaged-in-`N` reciprocal-phase/Vaaler package.  The phase estimate
and the Vaaler reduction retain their original pointwise mathematical
content.  What is weakened is the demanded decay of the resulting sawtooth
majorant: only its dyadic mean must tend to zero.

The `dyadicDecay` field is where the weighted Fourier coefficients, the
Vaaler error, and any `N`-dependent truncation degree must actually be
summed.  A mean estimate for individual phases alone cannot silently fill
this field, because the good cutoff could otherwise depend on `A` or `j`. -/
structure AveragedReciprocalPhaseVaalerPackage where
  phaseMajorant : ℕ → ℕ → ℤ → ℝ
  sawtoothMajorant : ℕ → ℝ
  phaseEstimate : MobiusReciprocalPhaseEstimate phaseMajorant
  vaalerReduction :
    VaalerSawtoothReduction phaseMajorant sawtoothMajorant
  dyadicDecay : DyadicAverageDecay sawtoothMajorant

/-- Reciprocal phases followed by the Vaaler reduction construct the direct
averaged sawtooth interface. -/
noncomputable def
    AveragedReciprocalPhaseVaalerPackage.toAveragedSawtooth
    (H : AveragedReciprocalPhaseVaalerPackage) :
    AveragedUniformMobiusSawtoothEstimate where
  sawtoothMajorant := H.sawtoothMajorant
  uniformEstimate :=
    uniformMobiusSawtoothEstimate_of_reciprocalPhase
      H.phaseEstimate H.vaalerReduction
  dyadicDecay := H.dyadicDecay

/-- The complete A3/Vaaler mean-value package yields arbitrarily large
cutoffs at which the exact sawtooth sum is uniformly small. -/
noncomputable def
    cofinalUniformMobiusSawtoothVanishing_of_averagedReciprocalPhase
    (H : AveragedReciprocalPhaseVaalerPackage) :
    CofinalUniformMobiusSawtoothVanishing :=
  H.toAveragedSawtooth.toCofinalVanishing

/-! ## The remaining A2 boundary and a cofinal H15 target -/

/-- Cofinal smallness of the centered H15 sawtooth residual.  This is weaker
than `H15CenteredSawtoothBound`, but is the exact conclusion supported by a
vanishing dyadic mean. -/
structure CofinalH15CenteredSawtoothVanishing where
  good_cutoff : ∀ ε : ℝ, 0 < ε → ∀ N₀ : ℕ,
    ∃ N ≥ N₀, |h15CenteredSawtoothResidual N| < ε

/-- Averaged version of the A2 harmonic-mode boundary.  The first field is
the exact pointwise implication from uniform finite sawtooth control to a
majorant for the centered residual; the second field is the required
mean-value estimate for that resulting majorant.

This is intentionally not derived from `UniformMobiusSawtoothEstimate`:
the outer `1/m` series is conditional and needs genuine cancellation. -/
structure AveragedH15SawtoothLogReduction
    (sawtoothMajorant : ℕ → ℝ) where
  residualMajorant : ℕ → ℝ
  residual_bound_of_uniform_sawtooth :
    UniformMobiusSawtoothEstimate sawtoothMajorant →
      ∀ N, |h15CenteredSawtoothResidual N| ≤ residualMajorant N
  residualDyadicDecay : DyadicAverageDecay residualMajorant

/-- Direct averaged sawtooth control plus the explicit averaged A2 boundary
gives cofinally small centered H15 sawtooth residuals. -/
noncomputable def cofinalH15CenteredSawtoothVanishing_of_averagedSawtooth
    (H : AveragedUniformMobiusSawtoothEstimate)
    (A2 : AveragedH15SawtoothLogReduction H.sawtoothMajorant) :
    CofinalH15CenteredSawtoothVanishing where
  good_cutoff ε hε N₀ := by
    obtain ⟨N, hN, hres⟩ :=
      A2.residualDyadicDecay.cofinal_small ε hε N₀
    refine ⟨N, hN, ?_⟩
    exact (A2.residual_bound_of_uniform_sawtooth H.uniformEstimate N).trans_lt hres

/-- The averaged reciprocal-phase/Vaaler route, followed by the still
explicit A2 summation boundary, reaches the cofinal centered H15 target. -/
noncomputable def
    cofinalH15CenteredSawtoothVanishing_of_averagedReciprocalPhase
    (H : AveragedReciprocalPhaseVaalerPackage)
    (A2 : AveragedH15SawtoothLogReduction H.sawtoothMajorant) :
    CofinalH15CenteredSawtoothVanishing :=
  cofinalH15CenteredSawtoothVanishing_of_averagedSawtooth
    H.toAveragedSawtooth A2

end RH.Criteria.NymanBeurling.QuadraticInteraction
