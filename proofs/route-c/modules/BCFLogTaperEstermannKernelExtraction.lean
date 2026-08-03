import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannBoundaryAnalysis

/-!
# Route B7.6: exact extraction of the paired Estermann contour kernel

The two-pole identity reconstructs each special value from three terms: a
right-line dual integral, a left-line primal integral, and the canonical
residue at zero.  This file names those terms for both orientations of every
coprime H15 pair and proves the exact finite aggregate identity.

The dual kernel is already in normalized functional-equation form.  Calling
it a Bessel/Kloosterman kernel would require a further inverse-Mellin theorem;
that analytic identification is not asserted here.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannKernelExtraction

open Complex
open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannContourShift
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannAtZeroBridge
open RH.Criteria.NymanBeurling.BCFLogTaperBettinConreyAggregate
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannBoundaryAnalysis

/-- The two oriented left-line primal integrals for a coprime pair. -/
noncomputable def estermannPairedPrimalKernel
    (W : ℂ → ℂ) (σL : ℝ)
    (a b : ℕ) (hcop : Nat.Coprime a b)
    (ha : 2 ≤ a) (hb : 2 ≤ b) : ℂ := by
  letI : NeZero a := ⟨by omega⟩
  letI : NeZero b := ⟨by omega⟩
  exact
    estermannPrimalVerticalIntegral
        (inverseResidueNumerator a b hcop) b σL W +
      estermannPrimalVerticalIntegral
        (inverseResidueNumerator b a hcop.symm) a σL W

/-- The two normalized functional-equation integrals on the right line. -/
noncomputable def estermannPairedDualKernel
    (W : ℂ → ℂ) (σR : ℝ)
    (a b : ℕ) (hcop : Nat.Coprime a b)
    (ha : 2 ≤ a) (hb : 2 ≤ b) : ℂ := by
  letI : NeZero a := ⟨by omega⟩
  letI : NeZero b := ⟨by omega⟩
  exact
    estermannDualVerticalIntegral
        (inverseResidueNumerator a b hcop) b
        (inverseResidueNumerator_coprime a b hcop) σR W +
      estermannDualVerticalIntegral
        (inverseResidueNumerator b a hcop.symm) a
        (inverseResidueNumerator_coprime b a hcop.symm) σR W

/-- The two canonical residues at the intrinsic Estermann pole. -/
noncomputable def estermannPairedZeroResidue
    (W : ℂ → ℂ)
    (a b : ℕ) (hcop : Nat.Coprime a b)
    (ha : 2 ≤ a) (hb : 2 ≤ b) : ℂ := by
  letI : NeZero a := ⟨by omega⟩
  letI : NeZero b := ⟨by omega⟩
  exact
    estermannWeightedResidueCoefficient
        (inverseResidueNumerator a b hcop) b W +
      estermannWeightedResidueCoefficient
        (inverseResidueNumerator b a hcop.symm) a W

/-- The paired special value reconstructed from the two contours. -/
noncomputable def estermannPairedRecoveredKernel
    (W : ℂ → ℂ) (σL σR : ℝ)
    (a b : ℕ) (hcop : Nat.Coprime a b)
    (ha : 2 ≤ a) (hb : 2 ≤ b) : ℂ :=
  estermannContourRecoveredValue W σL σR a b hcop hb +
    estermannContourRecoveredValue W σL σR b a hcop.symm ha

/-- The extracted pre-Kuznetsov kernel, with the residue retained in the same
signed expression. -/
noncomputable def estermannExtractedPairKernel
    (W : ℂ → ℂ) (σL σR : ℝ)
    (a b : ℕ) (hcop : Nat.Coprime a b)
    (ha : 2 ≤ a) (hb : 2 ≤ b) : ℂ :=
  (estermannPairedDualKernel W σR a b hcop ha hb -
      estermannPairedPrimalKernel W σL a b hcop ha hb) /
      (2 * Real.pi) -
    estermannPairedZeroResidue W a b hcop ha hb

/-- Exact pointwise extraction from the two-pole representation. -/
theorem estermannPairedRecoveredKernel_eq_extracted
    (W : ℂ → ℂ) (σL σR : ℝ)
    (a b : ℕ) (hcop : Nat.Coprime a b)
    (ha : 2 ≤ a) (hb : 2 ≤ b) :
    estermannPairedRecoveredKernel W σL σR a b hcop ha hb =
      estermannExtractedPairKernel W σL σR a b hcop ha hb := by
  letI : NeZero a := ⟨by omega⟩
  letI : NeZero b := ⟨by omega⟩
  unfold estermannPairedRecoveredKernel estermannExtractedPairKernel
    estermannPairedDualKernel estermannPairedPrimalKernel
    estermannPairedZeroResidue estermannContourRecoveredValue
  ring

/-- The full finite H15 aggregate of the extracted pointwise kernels. -/
noncomputable def estermannInteriorExtractedKernelAggregate
    (W : ℂ → ℂ) (σL σR : ℝ) (N : ℕ) : ℂ :=
  ∑ g ∈ Finset.Icc 1 N,
    ∑ a ∈ Finset.Icc 1 (N / g),
      ∑ b ∈ Finset.Icc 1 (N / g),
        if hcop : Nat.Coprime a b then
          if ha : 2 ≤ a then
            if hb : 2 ≤ b then
              estermannInteriorValueCoefficient N g a b *
                estermannExtractedPairKernel W σL σR a b hcop ha hb
            else 0
          else 0
        else 0

/-- Finite aggregation introduces no extra remainder: the previously
recovered aggregate is exactly the extracted kernel aggregate. -/
theorem estermannInteriorRecoveredAggregate_eq_extracted
    (W : ℂ → ℂ) (σL σR : ℝ) (N : ℕ) :
    estermannInteriorRecoveredAggregate W σL σR N =
      estermannInteriorExtractedKernelAggregate W σL σR N := by
  classical
  unfold estermannInteriorRecoveredAggregate
    estermannInteriorExtractedKernelAggregate
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hcop : Nat.Coprime a b
  · by_cases ha : 2 ≤ a
    · by_cases hb : 2 ≤ b
      · rw [dif_pos hcop, dif_pos hcop, dif_pos ha, dif_pos ha,
          dif_pos hb, dif_pos hb]
        change estermannInteriorValueCoefficient N g a b *
            estermannPairedRecoveredKernel W σL σR a b hcop ha hb = _
        rw [estermannPairedRecoveredKernel_eq_extracted]
      · simp [ha, hb]
    · simp [ha]
  · simp [hcop]

/-- The complete endpoint-coupled H15 realization in the exact kernel form
consumed by the next signed spectral gate. -/
theorem coupledGcdRatioExpression_eq_extractedKernel_add_endpoint
    (HZ : HurwitzZetaZeroFormula)
    (HC : EstermannBernoulliCotangentIdentity)
    {W : ℂ → ℂ} {σL σR : ℝ}
    (F : H15EvaluationContourFamily W σL σR) (N : ℕ) :
    RH.Criteria.NymanBeurling.BCFLogTaperSpectral.coupledGcdRatioExpression N =
      estermannInteriorElementaryExpression N +
        (estermannInteriorExtractedKernelAggregate W σL σR N).im +
          estermannEndpointCompletedExpression
            (analyticEstermannAtZeroPackage HZ HC) N := by
  rw [coupledGcdRatioExpression_eq_contourRecovered_add_endpoint HZ HC F,
    estermannInteriorRecoveredAggregate_eq_extracted]

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannKernelExtraction
