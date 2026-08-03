import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperH15ContourTraceModes

/-!
# The resolved H15 contour/trace ledger

The three literal modes isolated in `BCFLogTaperH15ContourTraceModes` do not
by themselves form the complete contour identity.  This file names the
remaining *physical* terms rather than defining them as the negative of a
normalization defect.

The right-line dual aggregate is split into its already named `m = 0` part
and its exact complement.  The endpoint-completed expression is likewise
split into the original Gram diagonal and its complement.  With the
left-line primal integral and elementary interior restored, these terms
reassemble the complete finite H15 expression exactly.

No trace formula, Eisenstein decomposition, or decay estimate is asserted.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperH15ResolvedTraceLedger

open Complex
open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperCancellationAnatomy
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannAtZeroBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannAtZeroReduction
open RH.Criteria.NymanBeurling.BCFLogTaperBettinConreyAggregate
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannBoundaryAnalysis
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannFiniteFourier
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKernelExtraction
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKuznetsovGate
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKuznetsovProof
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiPhysicalCorrection
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiSeed
open RH.Criteria.NymanBeurling.BCFLogTaperH15ContourTraceModes
open RH.Criteria.NymanBeurling.BCFLogTaperGcd
open RH.Criteria.NymanBeurling.BCFLogTaperSpectral
open RH.Criteria.NymanBeurling.VasyuninGram

/-! ## The four missing physical sectors -/

/-- The signed left-line primal contribution in the real H15 normalization. -/
noncomputable def h15ContourPrimalTotal
    (W : ℂ → ℂ) (σL : ℝ) (N : ℕ) : ℝ :=
  (-(estermannInteriorPairedPrimalAggregate W σL N) /
      (2 * Real.pi)).im

/-- The complete right-line Motohashi seed in the proved `π⁻¹`
normalization. -/
noncomputable def h15ContourDualTotal
    (N : ℕ) (η c : ℝ) : ℝ :=
  (h15MotohashiArithmeticSeedAggregate N η c / Real.pi).im

/-- The exact complement of the literal `m = 0` orbit inside the complete
right-line dual seed.  It is kept as a coupled difference because the
available convergence theorem applies to the completed orbit, not to two
separately estimated infinite series. -/
noncomputable def h15ContourDualNonzeroComplementTotal
    (N : ℕ) (η c : ℝ) : ℝ :=
  h15ContourDualTotal N η c - h15MotohashiZeroTotal N η c

/-- The endpoint-completed sector after removing the literal Gram diagonal,
which was already included among the named modes. -/
noncomputable def h15EndpointDiagonalComplement
    (H : EstermannAtZeroPackage) (N : ℕ) : ℝ :=
  estermannEndpointCompletedExpression H N - h15GramDiagonalTotal N

/-- The non-tautological physical replacement for the formerly abstract
missing sector. -/
noncomputable def h15ContourResolvedComplement
    (H : EstermannAtZeroPackage) (N : ℕ) (η σL c : ℝ) : ℝ :=
  estermannInteriorElementaryExpression N +
    h15ContourPrimalTotal (estermannGaussianEvaluationWeight η) σL N +
    h15ContourDualNonzeroComplementTotal N η c +
    h15EndpointDiagonalComplement H N

/-! ## Canonical gcd localization of the resolved complement -/

/-- Elementary interior contribution in one genuine gcd slice. -/
noncomputable def h15ContourElementaryGcdSlice (N g : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 (N / g),
    ∑ b ∈ Finset.Icc 1 (N / g),
      if Nat.Coprime a b ∧ 2 ≤ a ∧ 2 ≤ b then
        coprimeSliceCoefficient N g a b *
          estermannInteriorElementaryKernel a b
      else 0

/-- Signed left-line primal contribution in one genuine gcd slice. -/
noncomputable def h15ContourPrimalGcdSlice
    (W : ℂ → ℂ) (σL : ℝ) (N g : ℕ) : ℝ :=
  (-(∑ a ∈ Finset.Icc 1 (N / g),
      ∑ b ∈ Finset.Icc 1 (N / g),
        estermannInteriorPairedPrimalSummand W σL N g a b) /
      (2 * Real.pi)).im

/-- Complete right-line Motohashi seed in one genuine gcd slice. -/
noncomputable def h15ContourDualGcdSlice
    (N : ℕ) (η c : ℝ) (g : ℕ) : ℝ :=
  ((∑ q ∈ Finset.Icc 2 (N / g),
      if hq : 0 < q then
        @h15MotohashiTwoSignOrbitalSeries N g q
          ⟨Nat.ne_of_gt hq⟩ η c
      else 0) / Real.pi).im

/-- The coupled nonzero-frequency complement in one gcd slice. -/
noncomputable def h15ContourDualNonzeroComplementGcdSlice
    (N : ℕ) (η c : ℝ) (g : ℕ) : ℝ :=
  h15ContourDualGcdSlice N η c g - h15MotohashiZeroGcdSlice N η c g

/-- Endpoint contribution in one gcd slice after removing the already named
Gram diagonal.  The global linear correction and constant are deliberately
not assigned to an arbitrary block. -/
noncomputable def h15EndpointDiagonalComplementGcdSlice
    (H : EstermannAtZeroPackage) (N g : ℕ) : ℝ :=
  estermannEndpointCoprimeRatioSlice H N g - h15GramDiagonalGcdSlice N g

/-- All genuinely gcd-local terms missing from the original three-mode
ledger. -/
noncomputable def h15ContourResolvedComplementGcdSlice
    (H : EstermannAtZeroPackage) (N : ℕ) (η σL c : ℝ) (g : ℕ) : ℝ :=
  h15ContourElementaryGcdSlice N g +
    h15ContourPrimalGcdSlice (estermannGaussianEvaluationWeight η) σL N g +
    h15ContourDualNonzeroComplementGcdSlice N η c g +
    h15EndpointDiagonalComplementGcdSlice H N g

/-- The resolved complement localized in the same canonical dyadic gcd
blocks as the named modes. -/
noncomputable def h15ContourResolvedComplementBlockMode
    (H : EstermannAtZeroPackage) (N : ℕ) (η σL c : ℝ) (k : ℕ) : ℝ :=
  ∑ g ∈ h15TraceDyadicGcdBlock N k,
    h15ContourResolvedComplementGcdSlice H N η σL c g

theorem sum_h15ContourElementaryGcdSlice (N : ℕ) :
    (∑ g ∈ Finset.Icc 1 N, h15ContourElementaryGcdSlice N g) =
      estermannInteriorElementaryExpression N := by
  rfl

theorem sum_h15ContourPrimalGcdSlice
    (W : ℂ → ℂ) (σL : ℝ) (N : ℕ) :
    (∑ g ∈ Finset.Icc 1 N, h15ContourPrimalGcdSlice W σL N g) =
      h15ContourPrimalTotal W σL N := by
  classical
  let φ : ℂ →+ ℝ :=
    { toFun := fun z => (-z / (2 * Real.pi)).im
      map_zero' := by simp
      map_add' := by
        intro x y
        rw [neg_add_rev, add_comm (-y) (-x), add_div, Complex.add_im] }
  unfold h15ContourPrimalGcdSlice h15ContourPrimalTotal
    estermannInteriorPairedPrimalAggregate h15FiniteInteriorAggregate
  change (∑ g ∈ Finset.Icc 1 N, φ
      (∑ a ∈ Finset.Icc 1 (N / g),
        ∑ b ∈ Finset.Icc 1 (N / g),
          estermannInteriorPairedPrimalSummand W σL N g a b)) =
    φ (∑ g ∈ Finset.Icc 1 N,
      ∑ a ∈ Finset.Icc 1 (N / g),
        ∑ b ∈ Finset.Icc 1 (N / g),
          estermannInteriorPairedPrimalSummand W σL N g a b)
  exact (map_sum φ _ _).symm

theorem sum_h15ContourDualGcdSlice
    (N : ℕ) (η c : ℝ) :
    (∑ g ∈ Finset.Icc 1 N, h15ContourDualGcdSlice N η c g) =
      h15ContourDualTotal N η c := by
  classical
  let φ : ℂ →+ ℝ :=
    { toFun := fun z => (z / Real.pi).im
      map_zero' := by simp
      map_add' := by
        intro x y
        rw [add_div, Complex.add_im] }
  unfold h15ContourDualGcdSlice h15ContourDualTotal
    h15MotohashiArithmeticSeedAggregate
  change (∑ g ∈ Finset.Icc 1 N, φ
      (∑ q ∈ Finset.Icc 2 (N / g),
        if hq : 0 < q then
          @h15MotohashiTwoSignOrbitalSeries N g q
            ⟨Nat.ne_of_gt hq⟩ η c
        else 0)) =
    φ (∑ g ∈ Finset.Icc 1 N,
      ∑ q ∈ Finset.Icc 2 (N / g),
        if hq : 0 < q then
          @h15MotohashiTwoSignOrbitalSeries N g q
            ⟨Nat.ne_of_gt hq⟩ η c
        else 0)
  exact (map_sum φ _ _).symm

theorem sum_h15ContourDualNonzeroComplementGcdSlice
    (N : ℕ) (η c : ℝ) :
    (∑ g ∈ Finset.Icc 1 N,
      h15ContourDualNonzeroComplementGcdSlice N η c g) =
        h15ContourDualNonzeroComplementTotal N η c := by
  unfold h15ContourDualNonzeroComplementGcdSlice
    h15ContourDualNonzeroComplementTotal
  rw [Finset.sum_sub_distrib, sum_h15ContourDualGcdSlice]
  rfl

theorem sum_h15EndpointDiagonalComplementGcdSlice
    (H : EstermannAtZeroPackage) (N : ℕ) :
    (∑ g ∈ Finset.Icc 1 N,
      h15EndpointDiagonalComplementGcdSlice H N g) =
        h15EndpointDiagonalComplement H N -
          h15LinearEndpointCorrection N := by
  unfold h15EndpointDiagonalComplementGcdSlice
    h15EndpointDiagonalComplement h15LinearEndpointCorrection
    estermannEndpointCompletedExpression h15GramDiagonalTotal
  rw [Finset.sum_sub_distrib]
  ring

theorem sum_h15ContourResolvedComplementGcdSlice
    (H : EstermannAtZeroPackage) (N : ℕ) (η σL c : ℝ) :
    (∑ g ∈ Finset.Icc 1 N,
      h15ContourResolvedComplementGcdSlice H N η σL c g) =
        h15ContourResolvedComplement H N η σL c -
          h15LinearEndpointCorrection N := by
  unfold h15ContourResolvedComplementGcdSlice
    h15ContourResolvedComplement
  simp_rw [Finset.sum_add_distrib]
  rw [sum_h15ContourElementaryGcdSlice,
    sum_h15ContourPrimalGcdSlice,
    sum_h15ContourDualNonzeroComplementGcdSlice,
    sum_h15EndpointDiagonalComplementGcdSlice]
  ring

theorem sum_h15ContourResolvedComplementBlockMode
    (H : EstermannAtZeroPackage) (N : ℕ) (η σL c : ℝ) :
    (∑ k ∈ h15TraceDyadicGcdIndices N,
      h15ContourResolvedComplementBlockMode H N η σL c k) =
        h15ContourResolvedComplement H N η σL c -
          h15LinearEndpointCorrection N := by
  unfold h15ContourResolvedComplementBlockMode
  rw [sum_h15TraceDyadicGcdBlocks N
    (h15ContourResolvedComplementGcdSlice H N η σL c)]
  exact sum_h15ContourResolvedComplementGcdSlice H N η σL c

/-! ## Exact contour bookkeeping -/

/-- The imaginary part of the physical contour correction is exactly the
signed primal term plus the already named intrinsic residue. -/
theorem h15MotohashiExplicitPhysicalCorrection_im
    (W : ℂ → ℂ) (σL : ℝ) (N : ℕ) :
    (h15MotohashiExplicitPhysicalCorrection W σL N).im =
      h15ContourPrimalTotal W σL N + h15ContourResidueTotal W N := by
  rw [h15ContourResidueTotal_eq_neg_zeroResidueAggregate_im]
  unfold h15MotohashiExplicitPhysicalCorrection h15ContourPrimalTotal
  simp only [Complex.sub_im, Complex.neg_im, Complex.div_im]
  ring

/-- The extracted contour kernel contains precisely the complete dual seed,
the left-line primal term, and the intrinsic residue. -/
theorem estermannInteriorExtractedKernelAggregate_im_eq_traceLedger
    (N : ℕ) (η σL c : ℝ) (hη : 0 < η) (hc : 1 < c) :
    (estermannInteriorExtractedKernelAggregate
        (estermannGaussianEvaluationWeight η) σL c N).im =
      h15ContourDualTotal N η c +
        h15ContourPrimalTotal (estermannGaussianEvaluationWeight η) σL N +
        h15ContourResidueTotal (estermannGaussianEvaluationWeight η) N := by
  rw [estermannInteriorExtractedKernelAggregate_eq_seed_div_pi_add_correction
    N η σL c hη hc]
  rw [Complex.add_im,
    h15MotohashiExplicitPhysicalCorrection_im]
  unfold h15ContourDualTotal
  ring

/-- Exact global trace normalization: named residue/zero/diagonal modes plus
the resolved physical complement recover the complete H15 expression.

This is an equality to the finite H15 energy, not an assertion that the
individual trace sectors sum to zero. -/
theorem coupledGcdRatioExpression_eq_named_add_resolvedComplement
    (N : ℕ) (η σL c : ℝ) (hη : 0 < η) (hc : 1 < c)
    (F : H15EvaluationContourFamily
      (estermannGaussianEvaluationWeight η) σL c) :
    coupledGcdRatioExpression N =
      h15ContourTraceNamedTotal N η c +
        h15ContourResolvedComplement
          rationalAnalyticEstermannAtZeroPackage N η σL c := by
  rw [coupledGcdRatioExpression_eq_extractedKernel_add_endpoint
    rationalHurwitzZeroFormula estermannBernoulliCotangentIdentity F]
  rw [estermannInteriorExtractedKernelAggregate_im_eq_traceLedger
    N η σL c hη hc]
  unfold h15ContourTraceNamedTotal h15ContourResolvedComplement
    h15ContourDualNonzeroComplementTotal h15EndpointDiagonalComplement
    rationalAnalyticEstermannAtZeroPackage
  ring

/-- Equivalent sum-over-blocks form of the complete normalization. -/
theorem coupledGcdRatioExpression_eq_sum_modes_add_resolvedComplement
    (N : ℕ) (η σL c : ℝ) (hη : 0 < η) (hc : 1 < c)
    (F : H15EvaluationContourFamily
      (estermannGaussianEvaluationWeight η) σL c) :
    coupledGcdRatioExpression N =
      (∑ k ∈ h15TraceDyadicGcdIndices N,
        h15ContourTraceBlockMode N η c k) +
          h15ContourResolvedComplement
            rationalAnalyticEstermannAtZeroPackage N η σL c := by
  rw [sum_h15ContourTraceBlockMode]
  exact coupledGcdRatioExpression_eq_named_add_resolvedComplement
    N η σL c hη hc F

/-- Fully block-local form.  Only the original linear correction and
constant remain global; they are not distributed among blocks by an
artificial partition of unity. -/
theorem coupledGcdRatioExpression_eq_namedBlocks_add_resolvedBlocks_add_correction
    (N : ℕ) (η σL c : ℝ) (hη : 0 < η) (hc : 1 < c)
    (F : H15EvaluationContourFamily
      (estermannGaussianEvaluationWeight η) σL c) :
    coupledGcdRatioExpression N =
      (∑ k ∈ h15TraceDyadicGcdIndices N,
        h15ContourTraceBlockMode N η c k) +
      (∑ k ∈ h15TraceDyadicGcdIndices N,
        h15ContourResolvedComplementBlockMode
          rationalAnalyticEstermannAtZeroPackage N η σL c k) +
      h15LinearEndpointCorrection N := by
  rw [sum_h15ContourTraceBlockMode,
    sum_h15ContourResolvedComplementBlockMode]
  rw [coupledGcdRatioExpression_eq_named_add_resolvedComplement
    N η σL c hη hc F]
  ring

/-- The resolved complement is exactly the finite H15 expression minus the
three named sectors.  This theorem is derived from the physical contour
ledger, rather than used as its definition. -/
theorem h15ContourResolvedComplement_eq_coupled_sub_named
    (N : ℕ) (η σL c : ℝ) (hη : 0 < η) (hc : 1 < c)
    (F : H15EvaluationContourFamily
      (estermannGaussianEvaluationWeight η) σL c) :
    h15ContourResolvedComplement
        rationalAnalyticEstermannAtZeroPackage N η σL c =
      coupledGcdRatioExpression N - h15ContourTraceNamedTotal N η c := by
  rw [coupledGcdRatioExpression_eq_named_add_resolvedComplement
    N η σL c hη hc F]
  ring

/-- The earlier defect-completing quantity and the physical contour
complement are different objects.  Their exact discrepancy is the full H15
energy plus the retained linear/endpoint correction. -/
theorem resolvedComplement_sub_missingSector
    (N : ℕ) (η σL c : ℝ) (hη : 0 < η) (hc : 1 < c)
    (F : H15EvaluationContourFamily
      (estermannGaussianEvaluationWeight η) σL c) :
    h15ContourResolvedComplement
        rationalAnalyticEstermannAtZeroPackage N η σL c -
      h15ContourTraceMissingSector N η c =
        coupledGcdRatioExpression N + h15LinearEndpointCorrection N := by
  rw [h15ContourResolvedComplement_eq_coupled_sub_named
    N η σL c hη hc F]
  unfold h15ContourTraceMissingSector
    h15ContourTraceNormalizationDefect
  ring

/-! ## First-cutoff audit of the resolved ledger -/

/-- At the first nontrivial cutoff the full quadratic form consists only of
the universal `G(1,1)` entry. -/
theorem gramQuadraticForm_two :
    gramQuadraticForm 2 = baezDuarteGramEntry 1 1 := by
  classical
  have h12 : Finset.Icc 1 2 = {1, 2} := by decide
  unfold gramQuadraticForm
  rw [h12]
  simp [dirichletCoeff_two_one, dirichletCoeff_two_two]

/-- Hence the literal off-diagonal is zero at `N = 2`. -/
theorem gramOffDiagonal_two : gramOffDiagonal 2 = 0 := by
  unfold gramOffDiagonal
  rw [gramQuadraticForm_two, ← h15GramDiagonalTotal_eq_gramDiagonal,
    h15GramDiagonalTotal_two]
  ring

/-- The exact H15 expression at `N = 2` is the diagonal plus the retained
linear/endpoint correction. -/
theorem coupledGcdRatioExpression_two :
    coupledGcdRatioExpression 2 =
      baezDuarteGramEntry 1 1 + h15LinearEndpointCorrection 2 := by
  rw [coupledGcdRatioExpression_eq_diagonal_offDiagonal_linear,
    ← h15GramDiagonalTotal_eq_gramDiagonal, h15GramDiagonalTotal_two,
    gramOffDiagonal_two]
  unfold h15LinearEndpointCorrection
  ring

/-- The resolved physical complement is exactly the retained correction at
the first cutoff.  Together with the named diagonal it reconstructs the
finite H15 energy, as required. -/
theorem h15ContourResolvedComplement_two
    (η σL c : ℝ) (hη : 0 < η) (hc : 1 < c)
    (F : H15EvaluationContourFamily
      (estermannGaussianEvaluationWeight η) σL c) :
    h15ContourResolvedComplement
        rationalAnalyticEstermannAtZeroPackage 2 η σL c =
      h15LinearEndpointCorrection 2 := by
  rw [h15ContourResolvedComplement_eq_coupled_sub_named
    2 η σL c hη hc F, coupledGcdRatioExpression_two,
    h15ContourTraceNamedTotal_two]
  ring

end RH.Criteria.NymanBeurling.BCFLogTaperH15ResolvedTraceLedger
