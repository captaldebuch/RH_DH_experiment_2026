import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannGaussianAssembly
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmMotohashiComparison
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperH15ResolvedSpectralSplit

/-!
# Classical contour, Ehm stop test, and spectral realization

This module reconnects the now-genuine Gaussian two-pole contour with the two
remaining signed formulations.  It proves that the Ehm double-cofinal target
and any Poincare-linked bilinear spectral expansion act on exactly the same
completed H15 expression.  It does not manufacture either missing signed
estimate.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperH15ContourEhmSpectralBridge

open Filter Real Topology
open scoped Topology
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMotohashiComparison
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannAtZeroReduction
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannBoundaryAnalysis
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannGaussianAssembly
open RH.Criteria.NymanBeurling.BCFLogTaperH15ContourTraceModes
open RH.Criteria.NymanBeurling.BCFLogTaperH15ResolvedTraceLedger
open RH.Criteria.NymanBeurling.BCFLogTaperH15ResolvedSpectralSplit

/-- The corrected majorant package supplies the exact contour family used by
the resolved spectral ledger.  Boundary geometry and measurability are no
longer open fields here. -/
noncomputable def H15GaussianMajorantFamilyData.toEvaluationContourFamily
    {η σL σR : ℝ} (A : H15GaussianMajorantFamilyData η σL σR) :=
  A.toAsymptoticContourFamily.toEvaluationContourFamily

/-- Exact comparison of the direct Ehm expression and the resolved spectral
ledger.  The equality retains every named zero/diagonal/residue correction. -/
theorem h15EhmCommonExpression_eq_resolvedSpectralExpression
    {η σL σR : ℝ} (A : H15GaussianMajorantFamilyData η σL σR)
    (D : H15ResolvedDualSpectralDecomposition η σR) (N : ℕ) :
    h15EhmMotohashiCommonExpression
        BCFLogTaperEstermannKuznetsovGate.rationalAnalyticEstermannAtZeroPackage N =
      h15ContourTraceNamedTotal N η σR +
        h15ResolvedSpectralLedger D
          BCFLogTaperEstermannKuznetsovGate.rationalAnalyticEstermannAtZeroPackage N σL := by
  rw [h15EhmMotohashiCommonExpression_eq_coupledGcdRatioExpression]
  exact coupledGcdRatioExpression_eq_named_add_spectralLedger
    D N σL A.eta_pos A.right_of_one
      A.toAsymptoticContourFamily.toEvaluationContourFamily

/-- The Ehm signed double-cofinal stop test transfers without loss to the
complete resolved spectral expression.  This is a cofinal smallness theorem,
not a pointwise or absolute-value estimate. -/
theorem resolvedSpectralExpression_cofinally_small_of_ehmDoubleCofinal
    {η σL σR : ℝ} (A : H15GaussianMajorantFamilyData η σL σR)
    (D : H15ResolvedDualSpectralDecomposition η σR)
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (HB : EhmDoubleCofinalBoundaryVanishing ehmR1) :
    ∀ ε : ℝ, 0 < ε → ∀ N₀ : ℕ,
      ∃ N : ℕ, N₀ ≤ N ∧ 2 ≤ N ∧
        |h15ContourTraceNamedTotal N η σR +
          h15ResolvedSpectralLedger D
            BCFLogTaperEstermannKuznetsovGate.rationalAnalyticEstermannAtZeroPackage N σL| < ε := by
  intro ε hε N₀
  rcases h15EhmMotohashiCommonExpression_cofinally_small_of_doubleCofinal
    BCFLogTaperEstermannKuznetsovGate.rationalAnalyticEstermannAtZeroPackage
      HS HB ε hε N₀ with
      ⟨N, hN₀, hN, hsmall⟩
  refine ⟨N, hN₀, hN, ?_⟩
  rw [← h15EhmCommonExpression_eq_resolvedSpectralExpression A D]
  exact hsmall

/-- Conversely, cofinal signed smallness of a resolved spectral realization
is already the Ehm common-expression stop test.  No sector may be estimated
separately in this transport. -/
theorem h15EhmCommonExpression_cofinally_small_of_resolvedSpectral
    {η σL σR : ℝ} (A : H15GaussianMajorantFamilyData η σL σR)
    (D : H15ResolvedDualSpectralDecomposition η σR)
    (Hsmall : ∀ ε : ℝ, 0 < ε → ∀ N₀ : ℕ,
      ∃ N : ℕ, N₀ ≤ N ∧ 2 ≤ N ∧
        |h15ContourTraceNamedTotal N η σR +
          h15ResolvedSpectralLedger D
            BCFLogTaperEstermannKuznetsovGate.rationalAnalyticEstermannAtZeroPackage N σL| < ε) :
    ∀ ε : ℝ, 0 < ε → ∀ N₀ : ℕ,
      ∃ N : ℕ, N₀ ≤ N ∧ 2 ≤ N ∧
        |h15EhmMotohashiCommonExpression
          BCFLogTaperEstermannKuznetsovGate.rationalAnalyticEstermannAtZeroPackage N| < ε := by
  intro ε hε N₀
  rcases Hsmall ε hε N₀ with ⟨N, hN₀, hN, hsmall⟩
  refine ⟨N, hN₀, hN, ?_⟩
  rw [h15EhmCommonExpression_eq_resolvedSpectralExpression A D]
  exact hsmall

end RH.Criteria.NymanBeurling.BCFLogTaperH15ContourEhmSpectralBridge
