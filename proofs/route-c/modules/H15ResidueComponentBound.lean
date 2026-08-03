import RiemannHypothesis.Criteria.NymanBeurling.H15StructuredCorrelationEstimate
import RiemannHypothesis.Criteria.NymanBeurling.H15BBLSMainTerm
import RiemannHypothesis.Criteria.NymanBeurling.H15SmoothComponentBound

/-!
# H15 residue/cutoff-error interface

The current kernel files expose `explicitCutoffResidueComponent` as a
definitionally zero placeholder.  They do not yet contain the infinite
cutoff, boundary correction, or a theorem identifying those corrections with
that placeholder.  This file therefore records the exact algebraic interface
needed once those analytic objects are supplied.  In particular, the
truncation and boundary estimates remain separate fields; the following
aggregation result is unconditional and introduces no analytic assumption
under a new name.
-/

namespace RH.Criteria.NymanBeurling.QuadraticInteraction

open RH.Criteria.NymanBeurling.CutoffMobiusKernels

/-! ## Pairwise residual kernel -/

/-- The pointwise residue after removing the smooth and BBLS main terms. -/
noncomputable def residualQuadraticKernel
    (H : BBLSMainTermResiduePackage) (h k : ℕ) : ℝ :=
  quadraticInteractionKernel h k - smoothPart h k - mainTermValue_of_BBLS H h k

theorem residualQuadraticKernel_eq_definition
    (H : BBLSMainTermResiduePackage) (h k : ℕ) :
    residualQuadraticKernel H h k =
      quadraticInteractionKernel h k - smoothPart h k -
        mainTermValue_of_BBLS H h k := by
  rfl

/-- A pairwise truncation/boundary split for the residual kernel.  The
analytic derivation of these two terms is intentionally not hidden in this
structure. -/
structure ResidualQuadraticKernelSplit
    (H : BBLSMainTermResiduePackage) where
  truncationError : ℕ → ℕ → ℝ
  boundaryError : ℕ → ℕ → ℝ
  residual_eq : ∀ h k : ℕ,
    residualQuadraticKernel H h k = truncationError h k + boundaryError h k

/-- The finite weighted residual associated with a pairwise split. -/
noncomputable def weightedResidualContribution
    (H : BBLSMainTermResiduePackage) (N : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
    cutoffMobiusCoeff N h * cutoffMobiusCoeff N k *
      residualQuadraticKernel H h k

noncomputable def weightedTruncationContribution
    (S : ResidualQuadraticKernelSplit H) (N : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
    cutoffMobiusCoeff N h * cutoffMobiusCoeff N k * S.truncationError h k

noncomputable def weightedBoundaryContribution
    (S : ResidualQuadraticKernelSplit H) (N : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
    cutoffMobiusCoeff N h * cutoffMobiusCoeff N k * S.boundaryError h k

theorem weightedResidualContribution_eq_split
    (S : ResidualQuadraticKernelSplit H) (N : ℕ) :
    weightedResidualContribution H N =
      weightedTruncationContribution S N +
        weightedBoundaryContribution S N := by
  unfold weightedResidualContribution weightedTruncationContribution
    weightedBoundaryContribution
  simp_rw [S.residual_eq]
  simp_rw [mul_add, Finset.sum_add_distrib]

/-! ## Aggregate cutoff/boundary estimates -/

/-- The exact residue-bound shape consumed by the existing H15 assembly. -/
structure ExplicitCutoffResidueComponentEstimate where
  C_residue : ℝ
  C_residue_nonneg : 0 ≤ C_residue
  residue_bound : ∀ N : ℕ,
    |explicitCutoffResidueComponent N| ≤ C_residue / Real.log (N + 2 : ℝ)

/-- The two aggregate error estimates consumed by the H15 residue interface.

The fields are deliberately about separate contributions.  A future analytic
proof may instantiate them from exponential tails and boundary estimates;
this structure itself does not assert either of those estimates. -/
structure ResidueCutoffBoundaryBounds where
  truncationContribution : ℕ → ℝ
  boundaryContribution : ℕ → ℝ
  C_truncation : ℝ
  C_boundary : ℝ
  C_truncation_nonneg : 0 ≤ C_truncation
  C_boundary_nonneg : 0 ≤ C_boundary
  residue_decomposition : ∀ N : ℕ,
    explicitCutoffResidueComponent N =
      truncationContribution N + boundaryContribution N
  truncation_bound : ∀ N : ℕ,
    |truncationContribution N| ≤
      C_truncation / Real.log (N + 2 : ℝ)
  boundary_bound : ∀ N : ℕ,
    |boundaryContribution N| ≤
      C_boundary / Real.log (N + 2 : ℝ)

theorem explicitCutoffResidueComponent_bound_of_cutoff_boundary
    (H : ResidueCutoffBoundaryBounds) (N : ℕ) :
    |explicitCutoffResidueComponent N| ≤
      (H.C_truncation + H.C_boundary) /
        Real.log (N + 2 : ℝ) := by
  have hlog : 0 < Real.log (N + 2 : ℝ) := by
    apply Real.log_pos
    norm_cast
    omega
  rw [H.residue_decomposition N]
  calc
    |H.truncationContribution N + H.boundaryContribution N| ≤
        |H.truncationContribution N| + |H.boundaryContribution N| :=
      abs_add_le _ _
    _ ≤ H.C_truncation / Real.log (N + 2 : ℝ) +
          H.C_boundary / Real.log (N + 2 : ℝ) :=
      add_le_add (H.truncation_bound N) (H.boundary_bound N)
    _ = (H.C_truncation + H.C_boundary) /
          Real.log (N + 2 : ℝ) := by
      ring

/-- The aggregate bounds package in the exact shape consumed by
`quadraticInteractionEstimates_of_weightRestrictedCorrelation`. -/
noncomputable def explicitCutoffResidueComponentEstimate_of_cutoff_boundary
    (H : ResidueCutoffBoundaryBounds) :
    ExplicitCutoffResidueComponentEstimate :=
  { C_residue := H.C_truncation + H.C_boundary
    C_residue_nonneg := add_nonneg H.C_truncation_nonneg H.C_boundary_nonneg
    residue_bound := explicitCutoffResidueComponent_bound_of_cutoff_boundary H }

/-! ## Wiring to the existing restricted-correlation assembly -/

/-- The residue package supplies precisely the two residue arguments expected
by the existing restricted-correlation constructor.  No correlation,
main-term, or smooth estimate is manufactured here. -/
noncomputable def quadraticInteractionEstimates_of_weightRestrictedCorrelation_and_cutoff_boundary
    (Hcorr : FareyCellMobiusCorrelationEstimate_Restricted)
    (HBBLS : BBLS_EstermannContourPackage)
    (D : FareyCellGcdSliceErrorDecomposition_Restricted Hcorr HBBLS.mainTerm)
    (H : ResidueCutoffBoundaryBounds)
    (C_loggamma : ℝ)
    (C_pos :
      0 < C_loggamma +
        (quadraticInteractionDiagonalEstimate_zero.C_diagonal + D.C_error +
          HBBLS.C_main) +
        (H.C_truncation + H.C_boundary))
    (loggamma_bound :
      ∀ N : ℕ,
        |explicitQuadraticLogGammaComponent N| ≤ C_loggamma /
          Real.log (N + 2 : ℝ)) :
    QuadraticInteractionEstimates :=
  quadraticInteractionEstimates_of_weightRestrictedCorrelation
    Hcorr HBBLS D C_loggamma (H.C_truncation + H.C_boundary) C_pos
    loggamma_bound (explicitCutoffResidueComponent_bound_of_cutoff_boundary H)

theorem explicitCutoffResidueComponent_bound_of_cutoff_boundary_nonneg
    (H : ResidueCutoffBoundaryBounds) (N : ℕ) :
    0 ≤ (H.C_truncation + H.C_boundary) /
      Real.log (N + 2 : ℝ) := by
  apply div_nonneg
  · exact add_nonneg H.C_truncation_nonneg H.C_boundary_nonneg
  · exact (Real.log_pos (by norm_cast; omega)).le

/-! ## Current placeholder, made explicit -/

/-- The present repository definition is zero, so it has a formal zero bound.
This theorem is only a placeholder audit: it is not an analytic truncation or
boundary estimate and should not be used as evidence that the future residue
calculation has been discharged. -/
theorem explicitCutoffResidueComponent_placeholder_bound (N : ℕ) :
    |explicitCutoffResidueComponent N| ≤ 0 / Real.log (N + 2 : ℝ) := by
  simp [explicitCutoffResidueComponent]

/-- The zero placeholder gives a split package with both contributions zero.
This is useful for checking the algebraic interface while the genuine
residue definition is still pending. -/
noncomputable def residueCutoffBoundaryBounds_placeholder :
    ResidueCutoffBoundaryBounds := by
  refine
    { truncationContribution := fun _ => 0
      boundaryContribution := fun _ => 0
      C_truncation := 0
      C_boundary := 0
      C_truncation_nonneg := le_rfl
      C_boundary_nonneg := le_rfl
      residue_decomposition := ?_
      truncation_bound := ?_
      boundary_bound := ?_ }
  · intro N
    simp [explicitCutoffResidueComponent]
  · intro N
    simp
  · intro N
    simp

theorem placeholder_residue_estimate_is_zero
    (N : ℕ) :
    |explicitCutoffResidueComponent N| ≤
      (residueCutoffBoundaryBounds_placeholder.C_truncation +
        residueCutoffBoundaryBounds_placeholder.C_boundary) /
        Real.log (N + 2 : ℝ) := by
  simpa [residueCutoffBoundaryBounds_placeholder] using
    explicitCutoffResidueComponent_placeholder_bound N

end RH.Criteria.NymanBeurling.QuadraticInteraction
