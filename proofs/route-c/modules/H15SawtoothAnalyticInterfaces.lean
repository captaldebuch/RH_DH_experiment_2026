import RiemannHypothesis.Criteria.NymanBeurling.H15MobiusSawtoothReduction

/-!
# H15 sawtooth analytic interfaces

This module records the analytic inputs needed after the exact finite
Möbius--sawtooth reduction.  It deliberately separates three issues:

* a finite Vaaler approximation of the project's endpoint-corrected `B₁`;
* estimates for the resulting reciprocal phases; and
* the logarithmic summation needed to return from the finite mode partials
  to the centered sawtooth residual.

The third point is not a consequence of a pointwise sawtooth estimate.  It is
therefore a separate interface, which keeps Routes A1--A3 mathematically
honest: A1 supplies a sawtooth estimate, A3 supplies a phase estimate through
Vaaler, and A2 supplies the remaining harmonic-mode summation.  The smooth
log-gamma component is a separate H15 input and is recombined only at Phase 0.
-/

namespace RH.Criteria.NymanBeurling.QuadraticInteraction

open RH.Criteria.NymanBeurling.CutoffMobiusKernels
open RH.Criteria.NymanBeurling.VasyuninGram

/-! ## Vaaler Fourier data -/

/-- The `j`th Fourier character on the real torus.  Integer frequencies are
used because a finite Vaaler polynomial necessarily contains both signs. -/
noncomputable def vaalerFourierPhase (j : ℤ) (x : ℝ) : ℂ :=
  Complex.exp
    (((2 * Real.pi * (j : ℝ) * x : ℝ) : ℂ) * Complex.I)

/-- A reusable Vaaler interface for the endpoint convention of
`bernoulliB1`.  The actual coefficients and the error majorant remain data of
the package until a particular Vaaler theorem, including its endpoint
normalization, is formalized. -/
structure VaalerSawtoothPackage where
  approximant : ℕ → ℝ → ℂ
  error : ℕ → ℝ → ℂ
  errorMajorant : ℕ → ℝ → ℝ
  frequencies : ℕ → Finset ℤ
  coefficient : ℕ → ℤ → ℂ
  decomposition :
    ∀ D x, (bernoulliB1 x : ℂ) = approximant D x + error D x
  finite_fourier :
    ∀ D x, approximant D x =
      ∑ j ∈ frequencies D, coefficient D j * vaalerFourierPhase j x
  errorMajorant_nonneg : ∀ D x, 0 ≤ errorMajorant D x
  error_bound : ∀ D x, ‖error D x‖ ≤ errorMajorant D x

/-- The approximation selected by a Vaaler package.  Writing it as a
definition gives later analytic modules a stable, package-independent name. -/
noncomputable def vaalerSawtoothApprox
    (V : VaalerSawtoothPackage) (D : ℕ) (x : ℝ) : ℂ :=
  V.approximant D x

/-- The accompanying Vaaler error. -/
noncomputable def vaalerSawtoothError
    (V : VaalerSawtoothPackage) (D : ℕ) (x : ℝ) : ℂ :=
  V.error D x

theorem vaalerSawtooth_decomposition
    (V : VaalerSawtoothPackage) (D : ℕ) (x : ℝ) :
    (bernoulliB1 x : ℂ) =
      vaalerSawtoothApprox V D x + vaalerSawtoothError V D x :=
  V.decomposition D x

theorem vaalerSawtooth_error_bound
    (V : VaalerSawtoothPackage) (D : ℕ) (x : ℝ) :
    ‖vaalerSawtoothError V D x‖ ≤ V.errorMajorant D x :=
  V.error_bound D x

/-! ## Reciprocal phases -/

/-- The reciprocal Fourier phase arising when the Vaaler character is
evaluated at `A / k`. -/
noncomputable def mobiusReciprocalPhase (A : ℕ) (j : ℤ) (k : ℕ) : ℂ :=
  Complex.exp
    (((2 * Real.pi * (j : ℝ) * (A : ℝ) / (k : ℝ) : ℝ) : ℂ) * Complex.I)

/-- The cutoff Möbius reciprocal-phase sum exposed by the Vaaler expansion.
The frequency is integral so that negative Vaaler modes are represented
exactly, rather than folded into an unstated conjugation convention. -/
noncomputable def mobiusReciprocalPhaseSum (N A : ℕ) (j : ℤ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 N,
    ((ArithmeticFunction.moebius k : ℤ) : ℂ) *
      ((cutoffWeight N k : ℝ) : ℂ) * mobiusReciprocalPhase A j k

/-- A rate-parametrized reciprocal-phase estimate.  The selected analytic
route must state its actual range and majorant through `phaseMajorant`; no
unjustified DFI/Kloosterman rate is hard-coded here. -/
structure MobiusReciprocalPhaseEstimate
    (phaseMajorant : ℕ → ℕ → ℤ → ℝ) where
  phaseMajorant_nonneg :
    ∀ N A j, 0 ≤ phaseMajorant N A j
  phase_bound :
    ∀ N A j,
      ‖mobiusReciprocalPhaseSum N A j‖ ≤ phaseMajorant N A j

/-- A uniform one-variable bound for the exact finite sawtooth target.
Its majorant is deliberately explicit so that a future theorem can record
the saving, smoothing, and uniformity it really proves. -/
structure UniformMobiusSawtoothEstimate
    (sawtoothMajorant : ℕ → ℝ) where
  sawtoothMajorant_nonneg : ∀ N, 0 ≤ sawtoothMajorant N
  sawtooth_bound :
    ∀ N A, |mobiusSawtoothSum N A| ≤ sawtoothMajorant N

/-- The Vaaler reduction is an analytic theorem-to-be-proved: it converts a
specified reciprocal-phase estimate into a uniform bound for the exact
sawtooth sum.  Keeping it separate prevents a hidden appeal to a particular
Farey or Kloosterman theorem. -/
structure VaalerSawtoothReduction
    (phaseMajorant : ℕ → ℕ → ℤ → ℝ)
    (sawtoothMajorant : ℕ → ℝ) where
  vaaler : VaalerSawtoothPackage
  sawtooth_bound_of_phase_bounds :
    MobiusReciprocalPhaseEstimate phaseMajorant →
      UniformMobiusSawtoothEstimate sawtoothMajorant

/-- Phase 3 followed by the Vaaler interface supplies the Phase 1 uniform
sawtooth estimate. -/
noncomputable def uniformMobiusSawtoothEstimate_of_reciprocalPhase
    {phaseMajorant : ℕ → ℕ → ℤ → ℝ}
    {sawtoothMajorant : ℕ → ℝ}
    (P : MobiusReciprocalPhaseEstimate phaseMajorant)
    (R : VaalerSawtoothReduction phaseMajorant sawtoothMajorant) :
    UniformMobiusSawtoothEstimate sawtoothMajorant :=
  R.sawtooth_bound_of_phase_bounds P

/-! ## The harmonic-mode summation boundary -/

/-- Route A2: the additional logarithmic averaging/cancellation statement
needed to turn a pointwise sawtooth bound into the centered sawtooth bound.
This is intentionally independent of the Vaaler reduction: the exact finite
identity has an outer `1/m` mode sum, and this field is where that convergence
is controlled. -/
structure H15SawtoothLogAverageReduction
    (sawtoothMajorant : ℕ → ℝ) where
  sawtooth_bound_of_uniform_sawtooth :
    UniformMobiusSawtoothEstimate sawtoothMajorant →
      H15CenteredSawtoothBound

/-- Route A1 may supply the uniform sawtooth estimate directly, for example
from a properly matched mollified-Chowla theorem.  The named package prevents
that external theorem from being silently treated as already formalized. -/
structure MollifiedChowlaSawtoothEstimate
    (sawtoothMajorant : ℕ → ℝ) where
  uniform_sawtooth_estimate :
    UniformMobiusSawtoothEstimate sawtoothMajorant

/-- Route A1 followed by Route A2 reaches the centered sawtooth bound. -/
noncomputable def h15CenteredSawtoothBound_of_mollifiedChowla
    {sawtoothMajorant : ℕ → ℝ}
    (A1 : MollifiedChowlaSawtoothEstimate sawtoothMajorant)
    (A2 : H15SawtoothLogAverageReduction sawtoothMajorant) :
    H15CenteredSawtoothBound :=
  A2.sawtooth_bound_of_uniform_sawtooth A1.uniform_sawtooth_estimate

/-- Routes A3, Vaaler, and A2 reach the centered sawtooth bound. -/
noncomputable def h15CenteredSawtoothBound_of_reciprocalPhase
    {phaseMajorant : ℕ → ℕ → ℤ → ℝ}
    {sawtoothMajorant : ℕ → ℝ}
    (A3 : MobiusReciprocalPhaseEstimate phaseMajorant)
    (R : VaalerSawtoothReduction phaseMajorant sawtoothMajorant)
    (A2 : H15SawtoothLogAverageReduction sawtoothMajorant) :
    H15CenteredSawtoothBound :=
  A2.sawtooth_bound_of_uniform_sawtooth
    (uniformMobiusSawtoothEstimate_of_reciprocalPhase A3 R)

/-- Route A1 together with the separate smooth estimate reaches the exact
Phase 0 residual bound. -/
noncomputable def h15CenteredResidualBound_of_mollifiedChowla_and_smooth
    {sawtoothMajorant : ℕ → ℝ}
    (H_smooth : H15CenteredSmoothLogGammaBound)
    (A1 : MollifiedChowlaSawtoothEstimate sawtoothMajorant)
    (A2 : H15SawtoothLogAverageReduction sawtoothMajorant) :
    H15CenteredResidualBound :=
  h15CenteredResidualBound_of_smooth_and_sawtooth H_smooth
    (h15CenteredSawtoothBound_of_mollifiedChowla A1 A2)

/-- Routes A3, Vaaler, and A2 together with the separate smooth estimate
reach the exact Phase 0 residual bound. -/
noncomputable def h15CenteredResidualBound_of_reciprocalPhase_and_smooth
    {phaseMajorant : ℕ → ℕ → ℤ → ℝ}
    {sawtoothMajorant : ℕ → ℝ}
    (H_smooth : H15CenteredSmoothLogGammaBound)
    (A3 : MobiusReciprocalPhaseEstimate phaseMajorant)
    (R : VaalerSawtoothReduction phaseMajorant sawtoothMajorant)
    (A2 : H15SawtoothLogAverageReduction sawtoothMajorant) :
    H15CenteredResidualBound :=
  h15CenteredResidualBound_of_smooth_and_sawtooth H_smooth
    (h15CenteredSawtoothBound_of_reciprocalPhase A3 R A2)

/-- The full A3 → Vaaler → A2 route, supplied with the independent smooth
input, reaches the existing quadratic norm residual interface. -/
noncomputable def quadraticInteractionNormResidual_of_reciprocalPhase
    {phaseMajorant : ℕ → ℕ → ℤ → ℝ}
    {sawtoothMajorant : ℕ → ℝ}
    (H_smooth : H15CenteredSmoothLogGammaBound)
    (A3 : MobiusReciprocalPhaseEstimate phaseMajorant)
    (R : VaalerSawtoothReduction phaseMajorant sawtoothMajorant)
    (A2 : H15SawtoothLogAverageReduction sawtoothMajorant) :
    QuadraticInteractionNormResidual :=
  quadraticInteractionNormResidual_of_h15CenteredResidual_bound
    (h15CenteredResidualBound_of_reciprocalPhase_and_smooth H_smooth A3 R A2)

end RH.Criteria.NymanBeurling.QuadraticInteraction
