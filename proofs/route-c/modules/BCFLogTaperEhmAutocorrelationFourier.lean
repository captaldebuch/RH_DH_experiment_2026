import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmDilationFourier

/-!
# Fourier-pairing route to Ehm's autocorrelation value

The periodic Ehm kernel is an `L²` function on `AddCircle 1`, whereas
`∑ k ≥ 1, R₁(kr)` is a scalar depending on a positive real parameter `r`.
Consequently these objects cannot be identified directly.  The correct
statement applies the weighted-tail functional at `r` to the periodic
kernel.

This module proves unconditionally that every `L²` pairing of the concrete
finite Ehm functions converges to the corresponding pairing of the periodic
kernel, and rewrites the limit by polarized Parseval.  It then records the
exact two compatibility fields required of the weighted-tail probe.  Only
the second field--identification with the independently defined Gram
autocorrelation--contains Ehm's remaining global value theorem.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmAutocorrelationFourier

open Filter MeasureTheory AddCircle
open scoped Topology ComplexConjugate
open RH.Criteria.NymanBeurling.BCFLogTaperEhmKernel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmSeriesBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmIntegralSeriesAssembly
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPeriodicL2
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFourierBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDilationFourier

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- Every fixed `L²` probe may be paired through the concrete Ehm limit. -/
theorem ehmPhi1Pairing_tendsto
    (g : Lp ℂ 2 (@AddCircle.haarAddCircle 1 inferInstance)) :
    Tendsto (fun K : ℕ =>
      ∫ t : AddCircle (1 : ℝ),
        inner ℂ (ehmPhi1PartialL2 K t) (g t)
          ∂AddCircle.haarAddCircle)
      atTop
      (nhds (∫ t : AddCircle (1 : ℝ),
        inner ℂ (periodicEhmKernelL2 t) (g t)
          ∂AddCircle.haarAddCircle)) := by
  have h : Tendsto
      (fun K : ℕ => inner ℂ (ehmPhi1PartialL2 K) g)
      atTop (nhds (inner ℂ periodicEhmKernelL2 g)) :=
    Filter.Tendsto.inner ehmPhi1L2Convergence tendsto_const_nhds
  simpa only [MeasureTheory.L2.inner_def] using h

/-- Polarized Parseval identifies the limiting pairing purely from the
prescribed divisor Fourier coefficients. -/
theorem periodicEhmKernel_pairing_eq_fourierSeries
    (g : Lp ℂ 2 (@AddCircle.haarAddCircle 1 inferInstance)) :
    (∫ t : AddCircle (1 : ℝ),
        inner ℂ (periodicEhmKernelL2 t) (g t)
          ∂AddCircle.haarAddCircle) =
      ∑' m : ℤ,
        inner ℂ (ehmPhi1ComplexFourierCoefficient m)
          (fourierCoeff g m) := by
  rw [weightedIntegralAutocorrelation]
  apply tsum_congr
  intro m
  rw [periodicEhmKernelL2_fourierCoefficient]

/-- Coefficient form of the concrete pairing limit. -/
theorem ehmPhi1Pairing_tendsto_fourierSeries
    (g : Lp ℂ 2 (@AddCircle.haarAddCircle 1 inferInstance)) :
    Tendsto (fun K : ℕ =>
      ∫ t : AddCircle (1 : ℝ),
        inner ℂ (ehmPhi1PartialL2 K t) (g t)
          ∂AddCircle.haarAddCircle)
      atTop
      (nhds (∑' m : ℤ,
        inner ℂ (ehmPhi1ComplexFourierCoefficient m)
          (fourierCoeff g m))) := by
  rw [← periodicEhmKernel_pairing_eq_fourierSeries g]
  exact ehmPhi1Pairing_tendsto g

/-- Correctly typed interface for the weighted-tail functional.  The first
field realizes the finite tail integrals as circle pairings.  The second is
the genuine global autocorrelation identification; it must not be inferred
from equality of the Ehm Fourier coefficients alone. -/
structure EhmAutocorrelationFourierProbe where
  probe : ℝ → Lp ℂ 2 (@AddCircle.haarAddCircle 1 inferInstance)
  finite_tail : ∀ r : ℝ, 0 < r → ∀ K : ℕ,
    (inner ℂ (ehmPhi1PartialL2 K) (probe r)).re =
      -(∫ x in Set.Ioi r, ehmPhi1Partial K x / x ^ 2)
  autocorrelation_value : ∀ r : ℝ, 0 < r →
    (inner ℂ periodicEhmKernelL2 (probe r)).re =
      ehmS1Autocorrelation r

/-- A genuine Fourier probe constructs the global weighted-integral clause
of Ehm Proposition 5.1. -/
noncomputable def ehmPhi1IntegralLimitIdentity_of_fourierProbe
    (H : EhmAutocorrelationFourierProbe) :
    EhmPhi1IntegralLimitIdentity where
  tendsto_value r hr := by
    have hpair : Tendsto
        (fun K : ℕ => inner ℂ (ehmPhi1PartialL2 K) (H.probe r))
        atTop (nhds (inner ℂ periodicEhmKernelL2 (H.probe r))) :=
      Filter.Tendsto.inner ehmPhi1L2Convergence
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => H.probe r) atTop (nhds (H.probe r)))
    have hre : Tendsto
        (fun K : ℕ => (inner ℂ (ehmPhi1PartialL2 K) (H.probe r)).re)
        atTop (nhds (inner ℂ periodicEhmKernelL2 (H.probe r)).re) :=
      Complex.continuous_re.continuousAt.tendsto.comp hpair
    rw [H.autocorrelation_value r hr] at hre
    apply hre.congr'
    filter_upwards with K
    rw [H.finite_tail r hr K]

/-- The Fourier probe therefore supplies the exact all-real
autocorrelation--`R₁` series value identity. -/
noncomputable def ehmS1AutocorrelationIdentity
    (H : EhmAutocorrelationFourierProbe) :
    EhmAutocorrelationR1SeriesValueIdentity :=
  ehmAutocorrelationR1SeriesValueIdentity_of_phi1Limit
    (ehmPhi1IntegralLimitIdentity_of_fourierProbe H)

end RH.Criteria.NymanBeurling.BCFLogTaperEhmAutocorrelationFourier
