import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEnergyMeanAnatomy
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperH15ContourTraceModes

/-!
# Contour extraction of the negative diagonal mean

This module performs the correction-preserving extraction suggested by the
exact dyadic energy anatomy.  It distinguishes two statements which must not
be conflated.

* The visible intrinsic residue and completed zero mode do **not** reproduce
  the negative Gram diagonal.  The failure is already certified at `N = 2`.
* After the omitted primal, elementary, Eisenstein, and remaining spectral
  ledger is restored together with the retained linear/endpoint correction,
  the completed contour sector is exactly the negative Gram diagonal.

Subtracting this completed sector from the signed compensator leaves the
exact BCF energy.  Thus the extraction is an exact normalization theorem,
not by itself a decay estimate: the remaining signed dispersion still has
precisely the strength of H15.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEnergyMeanContourExtraction

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperCancellationAnatomy
open RH.Criteria.NymanBeurling.BCFLogTaperEnergyMeanAnatomy
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCompleteRowAbelDecay
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeTruncatedFormula
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
open RH.Criteria.NymanBeurling.BCFLogTaperH15ContourTraceModes
open RH.Criteria.NymanBeurling.QuadraticInteraction

/-- The sectors which are already represented by literal finite formulas,
coupled to the retained linear/endpoint correction. -/
noncomputable def h15ContourVisibleDiagonalCancellation
    (N : ℕ) (η c : ℝ) : ℝ :=
  h15ContourResidueTotal (estermannGaussianEvaluationWeight η) N +
    h15MotohashiZeroTotal N η c + h15LinearEndpointCorrection N

/-- The completed contour cancellation sector.  The missing-sector ledger
names exactly the primal/elementary/Eisenstein/remaining-spectrum contribution
which has not yet been analytically realized by a trace formula. -/
noncomputable def h15ContourCompletedDiagonalCancellation
    (N : ℕ) (η c : ℝ) : ℝ :=
  h15ContourVisibleDiagonalCancellation N η c +
    h15ContourTraceMissingSector N η c

/-- The visible residue and zero-mode formulas alone fail the desired
diagonal normalization already at the first nontrivial cutoff. -/
theorem h15ContourVisibleDiagonalCancellation_two_ne_neg_diagonal
    (η c : ℝ) :
    h15ContourVisibleDiagonalCancellation 2 η c ≠ -gramDiagonal 2 := by
  intro hvisible
  apply h15ContourTraceNamedTotal_two_ne_neg_correction η c
  unfold h15ContourVisibleDiagonalCancellation at hvisible
  unfold h15ContourTraceNamedTotal
  rw [h15GramDiagonalTotal_eq_gramDiagonal]
  linarith

/-- Exact pointwise extraction: once every omitted contour/trace sector and
the retained correction are restored, their total is the negative Gram
diagonal. -/
theorem h15ContourCompletedDiagonalCancellation_eq_neg_diagonal
    (N : ℕ) (η c : ℝ) :
    h15ContourCompletedDiagonalCancellation N η c = -gramDiagonal N := by
  have hledger := sum_named_add_missingSector_eq_neg_correction N η c
  rw [sum_h15ContourTraceBlockMode] at hledger
  unfold h15ContourCompletedDiagonalCancellation
    h15ContourVisibleDiagonalCancellation
  unfold h15ContourTraceNamedTotal at hledger
  rw [h15GramDiagonalTotal_eq_gramDiagonal] at hledger
  linarith

/-- The signed remainder after the completed negative-diagonal sector is
removed from the compensating correlation. -/
noncomputable def h15ContourSignedDispersionRemainder
    (N : ℕ) (η c : ℝ) : ℝ :=
  compensatingCorrelation N -
    h15ContourCompletedDiagonalCancellation N η c

/-- Stop theorem: the remaining signed dispersion is exactly the original
nonnegative BCF energy.  The contour extraction normalizes the cancellation
but does not weaken the final analytic estimate. -/
theorem h15ContourSignedDispersionRemainder_eq_energy
    (N : ℕ) (η c : ℝ) :
    h15ContourSignedDispersionRemainder N η c = energy N := by
  rw [h15ContourSignedDispersionRemainder,
    h15ContourCompletedDiagonalCancellation_eq_neg_diagonal]
  calc
    compensatingCorrelation N - -gramDiagonal N =
        gramDiagonal N + compensatingCorrelation N := by ring
    _ = energy N := by
      rw [RH.Criteria.NymanBeurling.BCFLogTaperGcd.energy_eq_gramQuadraticForm_add_linearCorrection,
        gramQuadraticForm_eq_diagonal_add_offDiagonal]
      unfold compensatingCorrelation
      ring

/-- Dyadic average of the completed contour-derived diagonal cancellation. -/
noncomputable def ehmDyadicContourDiagonalCancellationMean
    (X : ℕ) (η c : ℝ) : ℝ :=
  (∑ N ∈ ehmDyadicNBlock X,
      h15ContourCompletedDiagonalCancellation N η c) /
    ((ehmDyadicNBlock X).card : ℝ)

/-- The completed contour contribution is exactly the negative dyadic
diagonal mean requested by the energy anatomy. -/
theorem ehmDyadicContourDiagonalCancellationMean_eq_neg_diagonalMean
    (X : ℕ) (η c : ℝ) :
    ehmDyadicContourDiagonalCancellationMean X η c =
      -ehmDyadicDiagonalMean X := by
  unfold ehmDyadicContourDiagonalCancellationMean ehmDyadicDiagonalMean
  simp_rw [h15ContourCompletedDiagonalCancellation_eq_neg_diagonal]
  rw [Finset.sum_neg_distrib, neg_div]

/-- Dyadic mean of the signed dispersion remaining after extraction. -/
noncomputable def ehmDyadicContourSignedDispersionMean
    (X : ℕ) (η c : ℝ) : ℝ :=
  (∑ N ∈ ehmDyadicNBlock X,
      h15ContourSignedDispersionRemainder N η c) /
    ((ehmDyadicNBlock X).card : ℝ)

/-- The remaining signed dyadic dispersion is exactly the normalized exact
energy mean, independently of the Gaussian and right-line parameters. -/
theorem ehmDyadicContourSignedDispersionMean_eq_energyMean
    (X : ℕ) (η c : ℝ) :
    ehmDyadicContourSignedDispersionMean X η c =
      ehmDyadicExactEnergyMean X := by
  unfold ehmDyadicContourSignedDispersionMean ehmDyadicExactEnergyMean
  simp_rw [h15ContourSignedDispersionRemainder_eq_energy]

/-- Estimating the post-extraction signed dispersion is therefore exactly
the established outer-scale H15 target. -/
theorem tendsto_contourSignedDispersionMean_zero_iff_energyMean
    (η c : ℝ) :
    Tendsto (fun X ↦ ehmDyadicContourSignedDispersionMean X η c)
        atTop (nhds 0) ↔
      Tendsto ehmDyadicExactEnergyMean atTop (nhds 0) := by
  apply tendsto_congr'
  exact Eventually.of_forall fun X ↦
    ehmDyadicContourSignedDispersionMean_eq_energyMean X η c

/-- Final exact handoff: under the already proved rational-series bridge,
post-extraction signed dispersion decay is equivalent to existence of the
complete endpoint-minus-variation decay package. -/
theorem tendsto_contourSignedDispersionMean_zero_iff_completeRowAbel
    (D : EhmPrimeDiscrepancyTruncatedModeData)
    (V : VaalerSawtoothPackage)
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (η c : ℝ) :
    Tendsto (fun X ↦ ehmDyadicContourSignedDispersionMean X η c)
        atTop (nhds 0) ↔
      Nonempty (EhmPrimeCompleteRowAbelSignedDecay D V) := by
  rw [tendsto_contourSignedDispersionMean_zero_iff_energyMean]
  exact (nonempty_completeRowAbelSignedDecay_iff_tendsto_energyMean
    D V HS).symm

end RH.Criteria.NymanBeurling.BCFLogTaperEnergyMeanContourExtraction
