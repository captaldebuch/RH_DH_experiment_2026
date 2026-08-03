import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmPeriodicL2
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCofinal
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmAutocorrelationFourier
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmCompensator

/-!
# Correction-preserving spectral truncation for the Ehm H15 boundary

This module records the exact interface needed to turn the already formalized
Ehm Fourier coefficients into a spectral expansion of the correction-complete
finite H15 boundary.  The interface deliberately has a separate correction
field: putting the complete boundary into the correction and taking every mode
amplitude to be zero is ruled out by the `correction_spec` field, which fixes
the correction before the spectral identity is asserted.

The main results are purely unconditional consequences of an exact
realization:

* the full Fourier series splits into a finite symmetric low-frequency block
  and its genuine complementary `tsum`;
* the whole correction stays with the low-frequency block;
* an `ℓ²` bound for the mode amplitudes gives the precise Cauchy--Schwarz
  reduction for the high-frequency tail.

The Fourier index is `ℤ`, not `ℕ`.  Ehm's displayed coefficient
`-d(m)/(πm)` is a sine coefficient.  In Mathlib's complex Fourier convention
the coefficient at positive frequency is `I*d(m)/(2πm)` and the negative
frequency is its conjugate.  Pairing the two signs is therefore a later real
identity, not part of the truncation definition.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmCorrectionPreservingSpectralTruncation

open scoped BigOperators Topology
open Filter MeasureTheory AddCircle
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmKernel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmBoundaryResearch
open RH.Criteria.NymanBeurling.BCFLogTaperEhmHighSectorCompensation
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPeriodicL2
open RH.Criteria.NymanBeurling.BCFLogTaperEhmIntegralSeriesAssembly
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFourierBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmAutocorrelationFourier
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCompensator
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCorrectionMatching
open RH.Criteria.NymanBeurling.BCFLogTaperEhmUniformBoundary
open RH.Criteria.NymanBeurling.BCFLogTaperSpectral

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- The symmetric integer-frequency cutoff `[-M,M]`.  In particular, the
zero mode is retained explicitly even though the centered Ehm coefficient at
zero is zero. -/
noncomputable def ehmSpectralModeFinset (M : ℕ) : Finset ℤ :=
  Finset.Icc (-(M : ℤ)) (M : ℤ)

/-- The logarithmic cutoff proposed by the correction-preserving route. -/
noncomputable def ehmLogSquaredModeCutoff (N : ℕ) : ℕ :=
  Nat.ceil (Real.log (N + 2 : ℝ) ^ 2)

/-- Exact realization data for the correction-complete Ehm boundary.

`prescribedCorrection` is supplied independently of the Fourier expansion;
`correction_spec` identifies the correction that must be retained.  The
subsequent `expansion` field is therefore the genuine missing Fourier-pairing
theorem, rather than a definition that can absorb the whole target into an
unspecified correction. -/
structure EhmCompletedBoundarySpectralExpansion
    (H : EhmPrimeDiscrepancyExplicitModeData) where
  prescribedCorrection : ℕ → ℕ → ℂ
  modeAmplitude : ℕ → ℕ → ℤ → ℂ
  correction_spec : ∀ N J,
    prescribedCorrection N J =
      (ehmFiniteNaturalCutoffDefect N : ℂ) -
        (ehmFiniteMissingDivisorTailOuter ehmR1 N J : ℂ)
  summable_modes : ∀ N J,
    Summable (fun m : ℤ ↦
      (ehmPhi1ComplexFourierCoefficient m : ℂ) * modeAmplitude N J m)
  expansion : ∀ N J,
    ehmPrimeCompletedBoundaryProfile H N J =
      prescribedCorrection N J +
        ∑' m : ℤ,
          (ehmPhi1ComplexFourierCoefficient m : ℂ) * modeAmplitude N J m

variable {H : EhmPrimeDiscrepancyExplicitModeData}

/-- One spectral term in the exact realization. -/
noncomputable def ehmBoundarySpectralModeTerm
    (S : EhmCompletedBoundarySpectralExpansion H)
    (N J : ℕ) (m : ℤ) : ℂ :=
  (ehmPhi1ComplexFourierCoefficient m : ℂ) * S.modeAmplitude N J m

/-- The finite symmetric low-frequency expression. -/
noncomputable def ehmBoundaryLowModeExpression
    (S : EhmCompletedBoundarySpectralExpansion H)
    (N J M : ℕ) : ℂ :=
  ∑ m ∈ ehmSpectralModeFinset M,
    ehmBoundarySpectralModeTerm S N J m

/-- The genuine complementary high-frequency series.  Its index subtype is
the complement of `[-M,M]`, so no low-frequency or zero mode is silently
duplicated. -/
noncomputable def ehmBoundaryHighModeExpression
    (S : EhmCompletedBoundarySpectralExpansion H)
    (N J M : ℕ) : ℂ :=
  ∑' m : {m : ℤ // m ∉ ehmSpectralModeFinset M},
    ehmBoundarySpectralModeTerm S N J m.1

/-- Exact low/high splitting of the full modal series. -/
theorem ehmBoundaryModeSeries_eq_low_add_high
    (S : EhmCompletedBoundarySpectralExpansion H)
    (N J M : ℕ) :
    (∑' m : ℤ, ehmBoundarySpectralModeTerm S N J m) =
      ehmBoundaryLowModeExpression S N J M +
        ehmBoundaryHighModeExpression S N J M := by
  have hsum : Summable (fun m : ℤ ↦ ehmBoundarySpectralModeTerm S N J m) :=
    S.summable_modes N J
  exact (hsum.sum_add_tsum_compl (s := ehmSpectralModeFinset M)).symm

/-- The lossless correction-preserving truncation identity.  The complete
correction is grouped with the low modes; it is not split or estimated
termwise. -/
theorem correction_preserving_mode_split
    (S : EhmCompletedBoundarySpectralExpansion H)
    (N J M : ℕ) :
    ehmPrimeCompletedBoundaryProfile H N J =
      (S.prescribedCorrection N J +
          ehmBoundaryLowModeExpression S N J M) +
        ehmBoundaryHighModeExpression S N J M := by
  rw [S.expansion]
  change S.prescribedCorrection N J +
      (∑' m : ℤ, ehmBoundarySpectralModeTerm S N J m) = _
  rw [ehmBoundaryModeSeries_eq_low_add_high]
  ring

/-- The preferred logarithmic specialization of the exact split. -/
theorem correction_preserving_logSquared_mode_split
    (S : EhmCompletedBoundarySpectralExpansion H)
    (N J : ℕ) :
    ehmPrimeCompletedBoundaryProfile H N J =
      (S.prescribedCorrection N J +
          ehmBoundaryLowModeExpression S N J
            (ehmLogSquaredModeCutoff N)) +
        ehmBoundaryHighModeExpression S N J
          (ehmLogSquaredModeCutoff N) :=
  correction_preserving_mode_split S N J (ehmLogSquaredModeCutoff N)

/-- Direct bridge to the already verified finite H15 boundary.  This is the
WP1 identity in the repository's actual two-cutoff normalization. -/
theorem ofReal_ehmFiniteCoupledBoundaryExpression_eq_mode_split
    (S : EhmCompletedBoundarySpectralExpansion H)
    (N J M : ℕ) (hN : 2 ≤ N) (hNJ : N ≤ J) :
    (ehmFiniteCoupledBoundaryExpression ehmR1 N J : ℂ) =
      (S.prescribedCorrection N J +
          ehmBoundaryLowModeExpression S N J M) +
        ehmBoundaryHighModeExpression S N J M := by
  rw [ofReal_ehmFiniteCoupledBoundaryExpression_eq_completedBoundaryProfile
    H N J hN hNJ]
  exact correction_preserving_mode_split S N J M

/-! ## The exact high-mode `ℓ²` reduction -/

/-- Squared `ℓ²` mass of the Ehm kernel coefficients outside `[-M,M]`. -/
noncomputable def ehmHighModeKernelEnergy (M : ℕ) : ℝ :=
  ∑' m : {m : ℤ // m ∉ ehmSpectralModeFinset M},
    ‖ehmPhi1ComplexFourierCoefficient m.1‖ ^ 2

/-- Squared `ℓ²` mass of the H15 amplitudes outside `[-M,M]`. -/
noncomputable def ehmHighModeAmplitudeEnergy
    (S : EhmCompletedBoundarySpectralExpansion H)
    (N J M : ℕ) : ℝ :=
  ∑' m : {m : ℤ // m ∉ ehmSpectralModeFinset M},
    ‖S.modeAmplitude N J m.1‖ ^ 2

/-- The additional analytic datum needed beyond the exact spectral identity:
the H15 mode-amplitude row is square summable. -/
structure EhmCompletedBoundaryModeAmplitudeL2
    (S : EhmCompletedBoundarySpectralExpansion H) : Prop where
  summable_sq : ∀ N J,
    Summable (fun m : ℤ ↦ ‖S.modeAmplitude N J m‖ ^ 2)

private theorem summable_high_kernel_sq (M : ℕ) :
    Summable (fun m : {m : ℤ // m ∉ ehmSpectralModeFinset M} ↦
      ‖ehmPhi1ComplexFourierCoefficient m.1‖ ^ 2) :=
  summable_norm_sq_ehmPhi1ComplexFourierCoefficient.subtype _

private theorem summable_high_amplitude_sq
    (S : EhmCompletedBoundarySpectralExpansion H)
    (hS : EhmCompletedBoundaryModeAmplitudeL2 S)
    (N J M : ℕ) :
    Summable (fun m : {m : ℤ // m ∉ ehmSpectralModeFinset M} ↦
      ‖S.modeAmplitude N J m.1‖ ^ 2) :=
  (hS.summable_sq N J).subtype _

/-- Cauchy--Schwarz for the genuine complementary high-mode series.

This theorem is the precise fail-fast reduction: the divisor-square kernel
energy is only one factor.  A usable H15 amplitude-energy estimate is still
required for the other factor. -/
theorem norm_ehmBoundaryHighModeExpression_le_energy
    (S : EhmCompletedBoundarySpectralExpansion H)
    (hS : EhmCompletedBoundaryModeAmplitudeL2 S)
    (N J M : ℕ) :
    ‖ehmBoundaryHighModeExpression S N J M‖ ≤
      Real.sqrt (ehmHighModeKernelEnergy M) *
        Real.sqrt (ehmHighModeAmplitudeEnergy S N J M) := by
  let I := {m : ℤ // m ∉ ehmSpectralModeFinset M}
  let f : I → ℝ := fun m ↦ ‖ehmPhi1ComplexFourierCoefficient m.1‖
  let g : I → ℝ := fun m ↦ ‖S.modeAmplitude N J m.1‖
  have hf2 : Summable (fun m : I ↦ f m ^ (2 : ℝ)) := by
    simpa [I, f] using summable_high_kernel_sq M
  have hg2 : Summable (fun m : I ↦ g m ^ (2 : ℝ)) := by
    simpa [I, g] using summable_high_amplitude_sq S hS N J M
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hfg : Summable (fun m : I ↦ f m * g m) :=
    Real.summable_mul_of_Lp_Lq_of_nonneg hpq
      (fun m ↦ norm_nonneg _) (fun m ↦ norm_nonneg _) hf2 hg2
  have htermNorm : Summable (fun m : I ↦
      ‖ehmBoundarySpectralModeTerm S N J m.1‖) := by
    simpa [ehmBoundarySpectralModeTerm, I, f, g, norm_mul] using hfg
  calc
    ‖ehmBoundaryHighModeExpression S N J M‖ ≤
        ∑' m : I, ‖ehmBoundarySpectralModeTerm S N J m.1‖ := by
      exact norm_tsum_le_tsum_norm htermNorm
    _ = ∑' m : I, f m * g m := by
      apply tsum_congr
      intro m
      simp [ehmBoundarySpectralModeTerm, f, g]
    _ ≤ (∑' m : I, f m ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∑' m : I, g m ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
      Real.inner_le_Lp_mul_Lq_tsum_of_nonneg hpq
        (fun m ↦ norm_nonneg _) (fun m ↦ norm_nonneg _) hf2 hg2
    _ = Real.sqrt (ehmHighModeKernelEnergy M) *
          Real.sqrt (ehmHighModeAmplitudeEnergy S N J M) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
      simp [ehmHighModeKernelEnergy, ehmHighModeAmplitudeEnergy, I, f, g]

/-- A quantitative high-mode energy interface.  It does not claim that the
scale is small; that is the genuine arithmetic input to be audited. -/
structure EhmHighModeAmplitudeEnergyBound
    (S : EhmCompletedBoundarySpectralExpansion H) where
  scale : ℕ → ℕ → ℕ → ℝ
  C : ℝ
  C_nonneg : 0 ≤ C
  scale_nonneg : ∀ N J M, 0 ≤ scale N J M
  amplitude_l2 : EhmCompletedBoundaryModeAmplitudeL2 S
  bound : ∀ N J M,
    ehmHighModeAmplitudeEnergy S N J M ≤ C * scale N J M

/-- The high-mode norm after inserting an amplitude-energy majorant. -/
theorem norm_ehmBoundaryHighModeExpression_le_of_energyBound
    (S : EhmCompletedBoundarySpectralExpansion H)
    (hE : EhmHighModeAmplitudeEnergyBound S)
    (N J M : ℕ) :
    ‖ehmBoundaryHighModeExpression S N J M‖ ≤
      Real.sqrt (ehmHighModeKernelEnergy M) *
        Real.sqrt (hE.C * hE.scale N J M) := by
  refine (norm_ehmBoundaryHighModeExpression_le_energy
    S hE.amplitude_l2 N J M).trans ?_
  gcongr
  exact hE.bound N J M

/-! ## The one-parameter H15 expression after the hyperbolic limit

The finite-boundary interface above is useful for cofinal work, but the
one-parameter object in the spectral-truncation programme is
`coupledGcdRatioExpression`.  A Fourier probe gives its genuine modal
realization directly, without confusing full Ehm coefficients with a finite
hyperbolic truncation.
-/

/-- The exact Fourier-probe interface needed by H15 is only rational.

The quadratic H15 row samples the autocorrelation at `n / m` for positive
natural numbers `m,n`; asking for a probe at every positive real parameter
would therefore add an irrelevant all-real extension problem to WP1.  The
finite-tail field records the intended weighted-tail provenance of the probe,
while `autocorrelation_value` is the exact scalar identity used by the modal
expansion. -/
structure EhmRationalAutocorrelationFourierProbe where
  probe : ℕ → ℕ → Lp ℂ 2 (@AddCircle.haarAddCircle 1 inferInstance)
  finite_tail : ∀ n m : ℕ, 0 < n → 0 < m → ∀ K : ℕ,
    (inner ℂ (ehmPhi1PartialL2 K) (probe n m)).re =
      -(∫ x in Set.Ioi ((n : ℝ) / (m : ℝ)),
          ehmPhi1Partial K x / x ^ 2)
  autocorrelation_value : ∀ n m : ℕ, 0 < n → 0 < m →
    (inner ℂ periodicEhmKernelL2 (probe n m)).re =
      ehmS1Autocorrelation ((n : ℝ) / (m : ℝ))

/-- Every all-real Fourier probe restricts to the rational data actually
used by H15. -/
noncomputable def EhmRationalAutocorrelationFourierProbe.ofAllReal
    (P : EhmAutocorrelationFourierProbe) :
    EhmRationalAutocorrelationFourierProbe where
  probe n m := P.probe ((n : ℝ) / (m : ℝ))
  finite_tail n m hn hm K :=
    P.finite_tail ((n : ℝ) / (m : ℝ))
      (div_pos (by exact_mod_cast hn) (by exact_mod_cast hm)) K
  autocorrelation_value n m hn hm :=
    P.autocorrelation_value ((n : ℝ) / (m : ℝ))
      (div_pos (by exact_mod_cast hn) (by exact_mod_cast hm))

/-- Contribution of one Fourier frequency to one ordered pair in Ehm's
quadratic `S₁` term. -/
noncomputable def ehmH15FourierPairMode
    (P : EhmRationalAutocorrelationFourierProbe)
    (N m n : ℕ) (k : ℤ) : ℝ :=
  (dirichletCoeff N m / (m : ℝ) * dirichletCoeff N n) *
    (inner ℂ (ehmPhi1ComplexFourierCoefficient k)
      (fourierCoeff (P.probe n m) k)).re

/-- The complete signed H15 contribution at a single integer frequency. -/
noncomputable def ehmH15FourierMode
    (P : EhmRationalAutocorrelationFourierProbe)
    (N : ℕ) (k : ℤ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N,
    ∑ n ∈ Finset.Icc 1 N, ehmH15FourierPairMode P N m n k

/-- The H15 amplitude before pairing with Ehm's kernel coefficient.  Unlike
`ehmH15FourierMode`, this quantity does not contain the kernel coefficient;
it is therefore the correct second factor in the WP3 high-mode energy. -/
noncomputable def ehmH15FourierAmplitude
    (P : EhmRationalAutocorrelationFourierProbe)
    (N : ℕ) (k : ℤ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 N,
    ∑ n ∈ Finset.Icc 1 N,
      ((dirichletCoeff N m / (m : ℝ) * dirichletCoeff N n : ℝ) : ℂ) *
        fourierCoeff (P.probe n m) k

/-- The real H15 mode is exactly the polarized pairing of the Ehm kernel
coefficient with the correction-free amplitude. -/
theorem ehmH15FourierMode_eq_re_inner_amplitude
    (P : EhmRationalAutocorrelationFourierProbe)
    (N : ℕ) (k : ℤ) :
    ehmH15FourierMode P N k =
      (inner ℂ (ehmPhi1ComplexFourierCoefficient k)
        (ehmH15FourierAmplitude P N k)).re := by
  classical
  unfold ehmH15FourierMode ehmH15FourierPairMode ehmH15FourierAmplitude
  rw [inner_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [inner_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp [Complex.mul_re]
  ring

/-- Exact WP4 arithmetic audit of a low (or high) mode.  Before the rational
probe coefficients are computed, the mode is a *bilinear* Möbius sum; no
nonlinear phase or stationary point is present in the formal data.

Consequently saddle analysis is not justified at this layer.  Any phase used
later must be derived from an explicit formula for
`fourierCoeff (P.probe n m) k`, not postulated from the mode index. -/
theorem ehmH15FourierAmplitude_eq_mobius_taper_sum
    (P : EhmRationalAutocorrelationFourierProbe)
    (N : ℕ) (k : ℤ) :
    ehmH15FourierAmplitude P N k =
      ∑ m ∈ Finset.Icc 1 N,
        ∑ n ∈ Finset.Icc 1 N,
          (((ArithmeticFunction.moebius m : ℤ) : ℝ) *
              ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
              (weight N m / (m : ℝ) * weight N n) : ℝ) *
            fourierCoeff (P.probe n m) k := by
  classical
  unfold ehmH15FourierAmplitude dirichletCoeff
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  push_cast
  congr 1
  ring

private theorem summable_ehmProbeCoefficientPair
    (P : EhmRationalAutocorrelationFourierProbe) (n m : ℕ) :
    Summable (fun k : ℤ ↦
      inner ℂ (ehmPhi1ComplexFourierCoefficient k)
        (fourierCoeff (P.probe n m) k)) := by
  have h := lp.summable_inner (𝕜 := ℂ)
    ((@fourierBasis 1 inferInstance).repr periodicEhmKernelL2)
    ((@fourierBasis 1 inferInstance).repr (P.probe n m))
  simpa only [fourierBasis_repr,
    periodicEhmKernelL2_fourierCoefficient] using h

private theorem summable_re_ehmProbeCoefficientPair
    (P : EhmRationalAutocorrelationFourierProbe) (n m : ℕ) :
    Summable (fun k : ℤ ↦
      (inner ℂ (ehmPhi1ComplexFourierCoefficient k)
        (fourierCoeff (P.probe n m) k)).re) := by
  simpa only [Function.comp_apply] using
    (summable_ehmProbeCoefficientPair P n m).map
      Complex.reCLM Complex.reCLM.continuous

private theorem summable_ehmH15FourierPairMode
    (P : EhmRationalAutocorrelationFourierProbe)
    (N m n : ℕ) :
    Summable (ehmH15FourierPairMode P N m n) := by
  unfold ehmH15FourierPairMode
  exact (summable_re_ehmProbeCoefficientPair P n m).mul_left _

/-- The full signed H15 frequency row is summable.  This follows from
polarized Parseval for each pair and only finite summation over the H15
cutoff. -/
theorem summable_ehmH15FourierMode
    (P : EhmRationalAutocorrelationFourierProbe) (N : ℕ) :
    Summable (ehmH15FourierMode P N) := by
  unfold ehmH15FourierMode
  apply summable_sum
  intro m hm
  apply summable_sum
  intro n hn
  exact summable_ehmH15FourierPairMode P N m n

private theorem tsum_re_ehmProbeCoefficientPair
    (P : EhmRationalAutocorrelationFourierProbe)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    (∑' k : ℤ,
      (inner ℂ (ehmPhi1ComplexFourierCoefficient k)
        (fourierCoeff (P.probe n m) k)).re) =
      ehmS1Autocorrelation ((n : ℝ) / (m : ℝ)) := by
  have hsum := summable_ehmProbeCoefficientPair P n m
  have hpair :
      inner ℂ periodicEhmKernelL2 (P.probe n m) =
        ∑' k : ℤ,
          inner ℂ (ehmPhi1ComplexFourierCoefficient k)
            (fourierCoeff (P.probe n m) k) := by
    simpa only [MeasureTheory.L2.inner_def] using
      periodicEhmKernel_pairing_eq_fourierSeries (P.probe n m)
  calc
    (∑' k : ℤ,
        (inner ℂ (ehmPhi1ComplexFourierCoefficient k)
          (fourierCoeff (P.probe n m) k)).re) =
      (∑' k : ℤ,
        inner ℂ (ehmPhi1ComplexFourierCoefficient k)
          (fourierCoeff (P.probe n m) k)).re := by
            exact (Complex.reCLM.map_tsum hsum).symm
    _ = (inner ℂ periodicEhmKernelL2 (P.probe n m)).re := by rw [hpair]
    _ = ehmS1Autocorrelation ((n : ℝ) / (m : ℝ)) :=
      P.autocorrelation_value n m hn hm

private theorem tsum_ehmH15FourierPairMode
    (P : EhmRationalAutocorrelationFourierProbe)
    (N m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (∑' k : ℤ, ehmH15FourierPairMode P N m n k) =
      (dirichletCoeff N m / (m : ℝ) * dirichletCoeff N n) *
        ehmS1Autocorrelation ((n : ℝ) / (m : ℝ)) := by
  unfold ehmH15FourierPairMode
  rw [tsum_mul_left]
  rw [tsum_re_ehmProbeCoefficientPair P n m hn hm]

/-- The sum of all Fourier modes is exactly Ehm's finite `S₁` quadratic
term. -/
theorem tsum_ehmH15FourierMode_eq_quadraticTerm
    (P : EhmRationalAutocorrelationFourierProbe) (N : ℕ) :
    (∑' k : ℤ, ehmH15FourierMode P N k) =
      ehmS1QuadraticTerm ehmS1Autocorrelation N := by
  classical
  unfold ehmH15FourierMode ehmS1QuadraticTerm
  rw [Summable.tsum_finsetSum]
  · apply Finset.sum_congr rfl
    intro m hm
    rw [Summable.tsum_finsetSum]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [tsum_ehmH15FourierPairMode P N m n
        (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hm).1)
        (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1)]
      ring
    · intro n hn
      exact summable_ehmH15FourierPairMode P N m n
  · intro m hm
    apply summable_sum
    intro n hn
    exact summable_ehmH15FourierPairMode P N m n

/-- WP1 in the exact one-parameter H15 normalization.  The complete moment
correction is retained outside the globally summed Fourier row. -/
theorem h15_eq_spectral_expression
    (P : EhmRationalAutocorrelationFourierProbe) (N : ℕ) :
    coupledGcdRatioExpression N =
      ehmS1MomentCorrection N +
        ∑' k : ℤ, ehmH15FourierMode P N k := by
  rw [coupledGcdRatioExpression_eq_ehmS1QuadraticTerm_add_momentCorrection
    ehmS1PointwiseKernelPackageProved]
  change ehmS1QuadraticTerm ehmS1Autocorrelation N +
      ehmS1MomentCorrection N = _
  rw [tsum_ehmH15FourierMode_eq_quadraticTerm P]
  ring

/-- Low modes of the genuine one-parameter H15 Fourier expansion. -/
noncomputable def ehmH15LowModeExpression
    (P : EhmRationalAutocorrelationFourierProbe) (N M : ℕ) : ℝ :=
  ∑ k ∈ ehmSpectralModeFinset M, ehmH15FourierMode P N k

/-- Complementary high modes of the genuine one-parameter H15 expansion. -/
noncomputable def ehmH15HighModeExpression
    (P : EhmRationalAutocorrelationFourierProbe) (N M : ℕ) : ℝ :=
  ∑' k : {k : ℤ // k ∉ ehmSpectralModeFinset M},
    ehmH15FourierMode P N k.1

/-- WP2 for the actual H15 expression: the complete correction stays with
the symmetric low-mode block. -/
theorem h15_correction_preserving_mode_split
    (P : EhmRationalAutocorrelationFourierProbe) (N M : ℕ) :
    coupledGcdRatioExpression N =
      (ehmS1MomentCorrection N + ehmH15LowModeExpression P N M) +
        ehmH15HighModeExpression P N M := by
  have hsplit := (summable_ehmH15FourierMode P N).sum_add_tsum_compl
    (s := ehmSpectralModeFinset M)
  rw [h15_eq_spectral_expression P N]
  have heq : (∑' k : ℤ, ehmH15FourierMode P N k) =
      ehmH15LowModeExpression P N M +
        ehmH15HighModeExpression P N M := by
    exact hsplit.symm
  rw [heq]
  ring

/-! ## WP3 for the genuine one-parameter H15 amplitude -/

/-- The arithmetic high-mode energy after the Ehm kernel coefficient has
been factored out. -/
noncomputable def ehmH15HighModeAmplitudeEnergy
    (P : EhmRationalAutocorrelationFourierProbe)
    (N M : ℕ) : ℝ :=
  ∑' k : {k : ℤ // k ∉ ehmSpectralModeFinset M},
    ‖ehmH15FourierAmplitude P N k.1‖ ^ 2

/-- Square-summability of the genuine H15 amplitude row.  This is not a
consequence of divisor-square summability; it is the independent arithmetic
input exposed by the WP3 fail-fast test. -/
structure EhmH15FourierAmplitudeL2
    (P : EhmRationalAutocorrelationFourierProbe) : Prop where
  summable_sq : ∀ N : ℕ,
    Summable (fun k : ℤ ↦ ‖ehmH15FourierAmplitude P N k‖ ^ 2)

private theorem summable_high_h15_amplitude_sq
    (P : EhmRationalAutocorrelationFourierProbe)
    (hP : EhmH15FourierAmplitudeL2 P)
    (N M : ℕ) :
    Summable (fun k : {k : ℤ // k ∉ ehmSpectralModeFinset M} ↦
      ‖ehmH15FourierAmplitude P N k.1‖ ^ 2) :=
  (hP.summable_sq N).subtype _

/-- The actual H15 high-frequency tail is bounded by the product of the Ehm
divisor-kernel energy and the correction-free arithmetic amplitude energy.

This is the quantitative content of WP3 before any rate is asserted.  In
particular it makes precise why square-summability of the divisor coefficients
alone cannot close the tail. -/
theorem abs_ehmH15HighModeExpression_le_energy
    (P : EhmRationalAutocorrelationFourierProbe)
    (hP : EhmH15FourierAmplitudeL2 P)
    (N M : ℕ) :
    |ehmH15HighModeExpression P N M| ≤
      Real.sqrt (ehmHighModeKernelEnergy M) *
        Real.sqrt (ehmH15HighModeAmplitudeEnergy P N M) := by
  let I := {k : ℤ // k ∉ ehmSpectralModeFinset M}
  let f : I → ℝ := fun k ↦ ‖ehmPhi1ComplexFourierCoefficient k.1‖
  let g : I → ℝ := fun k ↦ ‖ehmH15FourierAmplitude P N k.1‖
  have hf2 : Summable (fun k : I ↦ f k ^ (2 : ℝ)) := by
    simpa [I, f] using summable_high_kernel_sq M
  have hg2 : Summable (fun k : I ↦ g k ^ (2 : ℝ)) := by
    simpa [I, g] using summable_high_h15_amplitude_sq P hP N M
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hfg : Summable (fun k : I ↦ f k * g k) :=
    Real.summable_mul_of_Lp_Lq_of_nonneg hpq
      (fun k ↦ norm_nonneg _) (fun k ↦ norm_nonneg _) hf2 hg2
  have hmode_le : ∀ k : I,
      ‖ehmH15FourierMode P N k.1‖ ≤ f k * g k := by
    intro k
    rw [ehmH15FourierMode_eq_re_inner_amplitude]
    change |(inner ℂ (ehmPhi1ComplexFourierCoefficient k.1)
      (ehmH15FourierAmplitude P N k.1)).re| ≤ _
    exact (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
  have hmodeNorm : Summable (fun k : I ↦
      ‖ehmH15FourierMode P N k.1‖) :=
    Summable.of_nonneg_of_le (fun k ↦ norm_nonneg _) hmode_le hfg
  calc
    |ehmH15HighModeExpression P N M| =
        ‖ehmH15HighModeExpression P N M‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' k : I, ‖ehmH15FourierMode P N k.1‖ :=
      norm_tsum_le_tsum_norm hmodeNorm
    _ ≤ ∑' k : I, f k * g k :=
      hmodeNorm.tsum_le_tsum hmode_le hfg
    _ ≤ (∑' k : I, f k ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∑' k : I, g k ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
      Real.inner_le_Lp_mul_Lq_tsum_of_nonneg hpq
        (fun k ↦ norm_nonneg _) (fun k ↦ norm_nonneg _) hf2 hg2
    _ = Real.sqrt (ehmHighModeKernelEnergy M) *
          Real.sqrt (ehmH15HighModeAmplitudeEnergy P N M) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
      simp [ehmHighModeKernelEnergy, ehmH15HighModeAmplitudeEnergy, I, f, g]

end RH.Criteria.NymanBeurling.BCFLogTaperEhmCorrectionPreservingSpectralTruncation
