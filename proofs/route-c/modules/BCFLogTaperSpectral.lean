import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperMellin
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperGcd
import RiemannHypothesis.Criteria.NymanBeurling.BaezDuarte

/-!
# Spectral reduction of the BCF logarithmic-taper energy

This module is the formal, conditional part of WP3.  It gives a single name to
the critical-line spectral energy and proves its exact identification with the
finite GCD-ratio formula once the reusable half-line Mellin--Plancherel theorem
has been supplied.  Thus the remaining analytic work is isolated in the
Plancherel package, not hidden in a change of notation.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperSpectral

open Filter Topology MeasureTheory
open RH.Criteria.NymanBeurling.AsymptoticEnergy
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperGcd
open RH.Criteria.NymanBeurling.BCFLogTaperMellin

/-- The critical-line spectral expression associated with the BCF energy. -/
noncomputable def spectralEnergy (N : ℕ) : ℝ :=
  criticalLineEnergy N

/-- The signed gap between the finite BCF energy and its spectral expression.
It vanishes as soon as the reusable Mellin--Plancherel bridge is available. -/
noncomputable def spectralRemainder (N : ℕ) : ℝ :=
  energy N - spectralEnergy N

/-- The spectral energy is equivalently the Fourier-coordinate expression of
the finite BCF logarithmic pullback. -/
theorem spectralEnergy_eq_fourierCriticalLineEnergy (N : ℕ) :
    spectralEnergy N = fourierCriticalLineEnergy N := by
  unfold spectralEnergy
  calc
    criticalLineEnergy N = mellinCriticalLineEnergy N :=
      (mellinCriticalLineEnergy_eq_criticalLineEnergy N).symm
    _ = fourierCriticalLineEnergy N :=
      mellinCriticalLineEnergy_eq_fourierCriticalLineEnergy N

/-- The critical-line spectral expression is nonnegative. -/
theorem spectralEnergy_nonneg (N : ℕ) : 0 ≤ spectralEnergy N := by
  unfold spectralEnergy criticalLineEnergy
  apply mul_nonneg
  · positivity
  · exact integral_nonneg fun t => sq_nonneg _

/-- Exact algebraic splitting of the finite energy into the spectral
expression and its signed comparison remainder. -/
theorem energy_eq_spectralEnergy_add_spectralRemainder (N : ℕ) :
    energy N = spectralEnergy N + spectralRemainder N := by
  unfold spectralRemainder
  ring

/-- The proved Fourier/Mellin bridge removes the comparison remainder. -/
theorem energy_eq_spectralEnergy (N : ℕ) :
    energy N = spectralEnergy N := by
  exact energy_eq_criticalLineEnergy_unconditional N

/-- The named finite/spectral comparison remainder is exactly zero. -/
theorem spectralRemainder_eq_zero (N : ℕ) :
    spectralRemainder N = 0 := by
  unfold spectralRemainder
  rw [energy_eq_spectralEnergy N]
  ring

/-- WP3 reduction: the critical-line spectral expression equals the exact
finite GCD-ratio formula.  All finite GCD reindexing, Mellin/Fourier
identification, and kernel scaling are unconditional. -/
theorem spectralEnergy_eq_gcdRatioFormula (N : ℕ) :
    spectralEnergy N =
      (∑ g ∈ Finset.Icc 1 N, gramCoprimeRatioSlice N g) +
        2 * gramLinearCorrection N + 1 := by
  rw [← energy_eq_spectralEnergy N]
  exact energy_eq_gcdRatioFormula N

/-- The complete signed finite expression which a genuine BCF cancellation
theorem must control.  The linear correction and constant are deliberately
part of this definition: neither the GCD slices nor their absolute values are
an asymptotic substitute for this coupled quantity. -/
noncomputable def coupledGcdRatioExpression (N : ℕ) : ℝ :=
  (∑ g ∈ Finset.Icc 1 N, gramCoprimeRatioSlice N g) +
    2 * gramLinearCorrection N + 1

/-- The coupled signed expression is exactly the spectral energy. -/
theorem spectralEnergy_eq_coupledGcdRatioExpression (N : ℕ) :
    spectralEnergy N = coupledGcdRatioExpression N :=
  spectralEnergy_eq_gcdRatioFormula N

/-- The elementary asymptotic fact used to turn a log-power correlation bound
into spectral vanishing. -/
theorem logRpowBound_tendsto_zero (C α : ℝ) (hα : 0 < α) :
    Tendsto (fun N : ℕ => C / (Real.log (N : ℝ)) ^ α) atTop (nhds 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hrpow : Tendsto (fun N : ℕ => (Real.log (N : ℝ)) ^ α) atTop atTop :=
    (tendsto_rpow_atTop hα).comp hlog
  have hinv : Tendsto (fun N : ℕ => ((Real.log (N : ℝ)) ^ α)⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hrpow
  simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hinv

/-- The exact Route D interface.  Its bound applies only after the entire
signed coprime-pair sum has been coupled with `2L_N + 1`; it makes no
termwise absolute-value assertion. -/
structure CoupledLogTaperCancellationEstimate where
  C : ℝ
  C_pos : 0 < C
  α : ℝ
  α_pos : 0 < α
  bound : ∀ N : ℕ, 2 ≤ N →
    |coupledGcdRatioExpression N| ≤ C / (Real.log (N : ℝ)) ^ α

/-- A genuine coupled signed cancellation estimate gives the required
spectral-energy limit. -/
theorem coupledGcdRatioExpression_tendsto_zero
    (H : CoupledLogTaperCancellationEstimate) :
    Tendsto coupledGcdRatioExpression atTop (nhds 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_
    (logRpowBound_tendsto_zero H.C H.α H.α_pos)
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  exact H.bound N hN

/-- The remaining analytic input in the BCF programme.  This is deliberately
an explicit hypothesis object, not an axiom or a theorem inferred from the
finite GCD-ratio formula: proving this convergence is RH-strength. -/
structure SpectralVanishingEstimate where
  tendsto_zero : Tendsto spectralEnergy atTop (nhds 0)

/-- A BCF-style first-order asymptotic is a sufficient, and more natural,
interface for spectral vanishing than a bound required at every small cutoff.
The theorem of Bettin--Conrey--Farmer predicts precisely such a limit for the
logarithmically tapered polynomial under RH and a negative moment hypothesis
for zeta derivatives.  This structure does not assert that conditional
analytic theorem; it records exactly the conclusion needed by the present
finite/spectral pipeline. -/
structure LogScaledSpectralEnergyAsymptotic where
  limit : ℝ
  tendsto_log_mul : Tendsto
    (fun N : ℕ => Real.log (N : ℝ) * spectralEnergy N) atTop (nhds limit)

/-- Any finite limit after multiplication by `log N` forces spectral energy
to vanish.  This is a purely topological consequence of `log N → ∞`; no
estimate on individual GCD-ratio terms and no contour remainder is used. -/
theorem spectralVanishingEstimate_of_logScaledSpectralEnergyAsymptotic
    (H : LogScaledSpectralEnergyAsymptotic) : SpectralVanishingEstimate := by
  refine ⟨?_⟩
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun N : ℕ => (Real.log (N : ℝ))⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hlog
  have hproduct : Tendsto
      (fun N : ℕ =>
        (Real.log (N : ℝ) * spectralEnergy N) *
          (Real.log (N : ℝ))⁻¹)
      atTop (nhds 0) := by
    simpa using H.tendsto_log_mul.mul hinv
  apply hproduct.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hN_real : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hlog_ne : Real.log (N : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hN_real)
  field_simp [hlog_ne]

/-- Route D closes the formal pipeline as soon as an external Route A/B/C
proof supplies the coupled signed cancellation estimate. -/
def spectralVanishingEstimate_of_coupledLogTaperCancellation
    (H : CoupledLogTaperCancellationEstimate) : SpectralVanishingEstimate where
  tendsto_zero :=
    (coupledGcdRatioExpression_tendsto_zero H).congr fun N =>
      (spectralEnergy_eq_coupledGcdRatioExpression N).symm

/-- A proved spectral-vanishing estimate gives the corresponding vanishing
of the finite BCF approximation energy. -/
theorem energy_tendsto_zero_of_spectralVanishing (H : SpectralVanishingEstimate) :
    Tendsto energy atTop (nhds 0) := by
  apply H.tendsto_zero.congr
  intro N
  exact (energy_eq_spectralEnergy N).symm

/-- This is the precise conditional closure point of the BCF route.  No
contour-remainder estimate is used: the only remaining analytic input is the
explicit RH-strength spectral-vanishing estimate above. -/
theorem baezDuarteCriterion_of_spectralVanishing (H : SpectralVanishingEstimate) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_certified_energy_sequence energy distance_le_energy
    (energy_tendsto_zero_of_spectralVanishing H)

/-- Conditional BCF-type asymptotics close the existing formal pipeline once
they have been established by genuine analysis.  This theorem is only the
downstream implication; it does not turn the BCF conditional theorem into an
unconditional assertion. -/
theorem baezDuarteCriterion_of_logScaledSpectralEnergyAsymptotic
    (H : LogScaledSpectralEnergyAsymptotic) : BaezDuarteCriterion :=
  baezDuarteCriterion_of_spectralVanishing
    (spectralVanishingEstimate_of_logScaledSpectralEnergyAsymptotic H)

end RH.Criteria.NymanBeurling.BCFLogTaperSpectral
