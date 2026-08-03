import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperH15ResolvedTraceLedger
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiPoincare

/-!
# Spectral split of the resolved H15 dual complement

The resolved contour ledger identifies the exact object to which a bilinear
Motohashi trace formula must apply:
`h15ContourDualNonzeroComplementTotal`.  This file packages a spectral
decomposition of that object into cuspidal, Eisenstein, and residual sectors
and transports the identity into the complete H15 expression.

The three real-valued parts first give an intentionally weak algebraic
ledger.  A convergent series/integral ledger is stronger bookkeeping but can
still be populated tautologically.  The actual trace-formula boundary below
therefore ties those terms to a convergent H15 Poincare realization and its
geometric coefficient.  The final signed decay remains a separate
RH-strength field.  In particular, no existing generic
`continuousRemainder` is silently renamed as an Eisenstein integral.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperH15ResolvedSpectralSplit

open Complex MeasureTheory ZMod
open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannAtZeroReduction
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKloostermanCompletion
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKuznetsovGate
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKuznetsovProof
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiSeed
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiPoincare
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiSynthesis
open RH.Criteria.NymanBeurling.BCFLogTaperH15ContourTraceModes
open RH.Criteria.NymanBeurling.BCFLogTaperH15ResolvedTraceLedger
open RH.Criteria.NymanBeurling.BCFLogTaperSpectral

/-! ## The minimal bilinear trace-formula field -/

/-- Algebraic ledger expected from an automorphic decomposition of the
completed nonzero-dual H15 sector.  The stronger analytic realization below
supplies its parts as actual convergent series and an integral. -/
structure H15ResolvedDualSpectralDecomposition (η c : ℝ) where
  cuspidalPart : ℕ → ℝ
  eisensteinPart : ℕ → ℝ
  residualPart : ℕ → ℝ
  dual_decomposition : ∀ N : ℕ,
    h15ContourDualNonzeroComplementTotal N η c =
      cuspidalPart N + eisensteinPart N + residualPart N

/-- The algebraic ledger is intentionally not advertised as a trace theorem:
without independent spectral formulas it has this tautological inhabitant. -/
noncomputable def tautologicalResolvedDualSpectralDecomposition
    (η c : ℝ) : H15ResolvedDualSpectralDecomposition η c where
  cuspidalPart := fun _ => 0
  eisensteinPart := fun _ => 0
  residualPart := fun N => h15ContourDualNonzeroComplementTotal N η c
  dual_decomposition := by intro N; ring

/-! ## Convergent spectral ledger interface -/

/-- Convergent cusp/Eisenstein/residual ledger for the H15 nonzero-dual
sector.

The three convergence fields prevent the expressions from using Lean's
totalized value for divergent sums or integrals.  They do not by themselves
certify that the indices and terms come from an automorphic spectrum; that
identification is imposed by the Poincare-linked interface below. -/
structure H15ResolvedBilinearTraceFormulaData
    (η c : ℝ) (CuspIndex ResidualIndex : Type*) where
  cuspTerm : ℕ → CuspIndex → ℂ
  cusp_summable : ∀ N : ℕ, Summable (cuspTerm N)
  eisensteinIntegrand : ℕ → ℝ → ℂ
  eisenstein_integrable : ∀ N : ℕ, Integrable (eisensteinIntegrand N)
  residualTerm : ℕ → ResidualIndex → ℂ
  residual_summable : ∀ N : ℕ, Summable (residualTerm N)
  trace_formula : ∀ N : ℕ,
    h15ContourDualNonzeroComplementTotal N η c =
      (∑' φ : CuspIndex, cuspTerm N φ).re +
        (∫ t : ℝ, eisensteinIntegrand N t).re +
          (∑' r : ResidualIndex, residualTerm N r).re

/-- Convergence alone is not an automorphic certificate: a singleton cusp
index can carry the entire dual complement.  Exposing this inhabitant is an
explicit guard against treating `H15ResolvedBilinearTraceFormulaData` as the
missing Motohashi theorem. -/
noncomputable def tautologicalResolvedBilinearTraceFormulaData
    (η c : ℝ) :
    H15ResolvedBilinearTraceFormulaData η c (Fin 1) (Fin 0) where
  cuspTerm := fun N _ => h15ContourDualNonzeroComplementTotal N η c
  cusp_summable := fun _ => (hasSum_fintype _).summable
  eisensteinIntegrand := fun _ _ => 0
  eisenstein_integrable := fun _ => integrable_zero ℝ ℂ volume
  residualTerm := fun _ _ => 0
  residual_summable := fun _ => (hasSum_fintype _).summable
  trace_formula := by
    intro N
    simp

/-- A convergent series/integral ledger forgets to the algebraic spectral
ledger used by the finite H15 bookkeeping. -/
noncomputable def H15ResolvedBilinearTraceFormulaData.toSpectralDecomposition
    {η c : ℝ} {CuspIndex ResidualIndex : Type*}
    (T : H15ResolvedBilinearTraceFormulaData
      η c CuspIndex ResidualIndex) :
    H15ResolvedDualSpectralDecomposition η c where
  cuspidalPart := fun N => (∑' φ : CuspIndex, T.cuspTerm N φ).re
  eisensteinPart := fun N => (∫ t : ℝ, T.eisensteinIntegrand N t).re
  residualPart := fun N =>
    (∑' r : ResidualIndex, T.residualTerm N r).re
  dual_decomposition := T.trace_formula

/-! ## Poincare-linked automorphic boundary -/

universe u v

/-- A spectral expansion tied to the already specified H15 Poincare seed.

Unlike the convergent ledger above, this equality is stated for the geometric
coefficient of a convergent, cusp-invariant Poincare series whose big-cell
unfolding is the canonical H15 arithmetic seed.  An inhabitant still requires
the external automorphic spectral theorem, but the H15 target can no longer
be discharged merely by renaming the original dual complement. -/
structure H15ResolvedPoincareSpectralExpansionData
    {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
    (H : Subgroup Γ)
    {A : H15ClassicalEstermannData}
    {S : H15MotohashiSeedAdmissibilityData A}
    (P : H15MotohashiPoincareSeedRealizationData (X := X) H A S)
    (CuspIndex ResidualIndex : Type*) where
  cuspTerm : ℕ → CuspIndex → ℂ
  cusp_summable : ∀ N : ℕ, Summable (cuspTerm N)
  eisensteinIntegrand : ℕ → ℝ → ℂ
  eisenstein_integrable : ∀ N : ℕ, Integrable (eisensteinIntegrand N)
  residualTerm : ℕ → ResidualIndex → ℂ
  residual_summable : ∀ N : ℕ, Summable (residualTerm N)
  geometric_spectral_expansion : ∀ N : ℕ,
    (P.geometricCoefficient
        (poincareSeries H (P.seed N) (P.seed_cusp_invariant N))).im -
          h15MotohashiZeroTotal N A.η S.c =
      (∑' φ : CuspIndex, cuspTerm N φ).re +
        (∫ t : ℝ, eisensteinIntegrand N t).re +
          (∑' r : ResidualIndex, residualTerm N r).re

/-- Exact transport from a genuine Poincare-linked spectral expansion to the
resolved H15 nonzero-dual trace formula. -/
noncomputable def
    H15ResolvedPoincareSpectralExpansionData.toBilinearTraceFormulaData
    {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
    {H : Subgroup Γ}
    {A : H15ClassicalEstermannData}
    {S : H15MotohashiSeedAdmissibilityData A}
    {P : H15MotohashiPoincareSeedRealizationData (X := X) H A S}
    {CuspIndex ResidualIndex : Type*}
    (T : H15ResolvedPoincareSpectralExpansionData
      H P CuspIndex ResidualIndex) :
    H15ResolvedBilinearTraceFormulaData
      A.η S.c CuspIndex ResidualIndex where
  cuspTerm := T.cuspTerm
  cusp_summable := T.cusp_summable
  eisensteinIntegrand := T.eisensteinIntegrand
  eisenstein_integrable := T.eisenstein_integrable
  residualTerm := T.residualTerm
  residual_summable := T.residual_summable
  trace_formula N := by
    unfold h15ContourDualNonzeroComplementTotal h15ContourDualTotal
    rw [← P.big_cell_unfolding N]
    exact T.geometric_spectral_expansion N

/-- The complete resolved H15 ledger after inserting a genuine spectral
split of its nonzero-dual sector. -/
noncomputable def h15ResolvedSpectralLedger
    {η c : ℝ} (D : H15ResolvedDualSpectralDecomposition η c)
    (H : EstermannAtZeroPackage) (N : ℕ) (σL : ℝ) : ℝ :=
  estermannInteriorElementaryExpression N +
    h15ContourPrimalTotal (estermannGaussianEvaluationWeight η) σL N +
    D.cuspidalPart N + D.eisensteinPart N + D.residualPart N +
    h15EndpointDiagonalComplement H N

/-- The spectral ledger is exactly the physical resolved complement. -/
theorem h15ResolvedSpectralLedger_eq_resolvedComplement
    {η c : ℝ} (D : H15ResolvedDualSpectralDecomposition η c)
    (H : EstermannAtZeroPackage) (N : ℕ) (σL : ℝ) :
    h15ResolvedSpectralLedger D H N σL =
      h15ContourResolvedComplement H N η σL c := by
  unfold h15ResolvedSpectralLedger h15ContourResolvedComplement
  rw [D.dual_decomposition N]
  ring

/-- Exact complete H15 trace identity after the cusp/Eisenstein/residual
split.  No cancellation estimate is used. -/
theorem coupledGcdRatioExpression_eq_named_add_spectralLedger
    {η c : ℝ} (D : H15ResolvedDualSpectralDecomposition η c)
    (N : ℕ) (σL : ℝ) (hη : 0 < η) (hc : 1 < c)
    (F : H15EvaluationContourFamily
      (estermannGaussianEvaluationWeight η) σL c) :
    coupledGcdRatioExpression N =
      h15ContourTraceNamedTotal N η c +
        h15ResolvedSpectralLedger
          D rationalAnalyticEstermannAtZeroPackage N σL := by
  rw [h15ResolvedSpectralLedger_eq_resolvedComplement]
  exact coupledGcdRatioExpression_eq_named_add_resolvedComplement
    N η σL c hη hc F

/-! ## What the existing coarse trace interface does and does not supply -/

/-- Existing Motohashi trace data gives a valid *coarse* resolved split.  Its
named cuspidal term is retained, but its arithmetic main term, zero-orbit
subtraction, and undifferentiated continuous remainder stay together in the
residual sector.  The Eisenstein sector is set to zero rather than asserted
without a proved identification. -/
noncomputable def coarseResolvedDualSpectralDecomposition
    {A : H15ClassicalEstermannData}
    {S : H15MotohashiSeedAdmissibilityData A}
    (T : H15MotohashiAutomorphicTraceData S) :
    H15ResolvedDualSpectralDecomposition A.η S.c where
  cuspidalPart := T.cuspidalPart
  eisensteinPart := fun _ => 0
  residualPart := fun N =>
    T.arithmeticMain N + T.continuousRemainder N -
      h15MotohashiZeroTotal N A.η S.c
  dual_decomposition N := by
    unfold h15ContourDualNonzeroComplementTotal h15ContourDualTotal
    rw [T.poincare_trace N]
    ring

/-! ## First-cutoff trace constraint -/

/-- Every completed-frequency seed vanishes in the only possible interior
row at `N = 2`, because its unit-numerator weight is identically zero. -/
@[simp]
theorem h15MotohashiArithmeticSeed_two_one_two
    (sign : H15MotohashiSign) (η c : ℝ)
    (n : ℕ) (m : ZMod 2) :
    @h15MotohashiArithmeticSeed 2 1 2 inferInstance
      sign η c n m = 0 := by
  classical
  unfold h15MotohashiArithmeticSeed inverseCoordinateFourierCoefficient
  simp

/-- The complete right-line arithmetic seed therefore vanishes at the first
nontrivial cutoff. -/
theorem h15MotohashiArithmeticSeedAggregate_two (η c : ℝ) :
    h15MotohashiArithmeticSeedAggregate 2 η c = 0 := by
  classical
  have h12 : Finset.Icc 1 2 = {1, 2} := by decide
  unfold h15MotohashiArithmeticSeedAggregate
    h15MotohashiTwoSignOrbitalSeries h15MotohashiSignOrbitalSeries
  rw [h12]
  simp

theorem h15ContourDualTotal_two (η c : ℝ) :
    h15ContourDualTotal 2 η c = 0 := by
  unfold h15ContourDualTotal
  rw [h15MotohashiArithmeticSeedAggregate_two]
  simp

/-- Both the completed dual and its zero orbit vanish, hence so does the
exact nonzero-dual complement. -/
theorem h15ContourDualNonzeroComplementTotal_two (η c : ℝ) :
    h15ContourDualNonzeroComplementTotal 2 η c = 0 := by
  unfold h15ContourDualNonzeroComplementTotal
  rw [h15ContourDualTotal_two, h15MotohashiZeroTotal_two]
  ring

/-- Any genuine cusp/Eisenstein/residual decomposition must satisfy this
first-cutoff normalization constraint. -/
theorem H15ResolvedDualSpectralDecomposition.sum_two
    {η c : ℝ} (D : H15ResolvedDualSpectralDecomposition η c) :
    D.cuspidalPart 2 + D.eisensteinPart 2 + D.residualPart 2 = 0 := by
  rw [← D.dual_decomposition 2,
    h15ContourDualNonzeroComplementTotal_two]

/-- The same first-cutoff constraint written directly for any genuine
analytic trace formula.  It is a useful normalization stop test: cusp,
Eisenstein, and residual contributions must sum to zero at `N = 2`. -/
theorem H15ResolvedBilinearTraceFormulaData.sum_two
    {η c : ℝ} {CuspIndex ResidualIndex : Type*}
    (T : H15ResolvedBilinearTraceFormulaData
      η c CuspIndex ResidualIndex) :
    (∑' φ : CuspIndex, T.cuspTerm 2 φ).re +
        (∫ t : ℝ, T.eisensteinIntegrand 2 t).re +
          (∑' r : ResidualIndex, T.residualTerm 2 r).re = 0 := by
  exact T.toSpectralDecomposition.sum_two

/-- The first-cutoff normalization transported all the way to a
Poincare-linked spectral expansion. -/
theorem H15ResolvedPoincareSpectralExpansionData.sum_two
    {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
    {H : Subgroup Γ}
    {A : H15ClassicalEstermannData}
    {S : H15MotohashiSeedAdmissibilityData A}
    {P : H15MotohashiPoincareSeedRealizationData (X := X) H A S}
    {CuspIndex ResidualIndex : Type*}
    (T : H15ResolvedPoincareSpectralExpansionData
      H P CuspIndex ResidualIndex) :
    (∑' φ : CuspIndex, T.cuspTerm 2 φ).re +
        (∫ t : ℝ, T.eisensteinIntegrand 2 t).re +
          (∑' r : ResidualIndex, T.residualTerm 2 r).re = 0 := by
  exact T.toBilinearTraceFormulaData.sum_two

/-! ## The separated RH-strength field -/

/-- Decay is required only after the named physical modes and all three
spectral sectors have been recombined. -/
structure H15ResolvedSignedSpectralEstimate
    {η c : ℝ} (D : H15ResolvedDualSpectralDecomposition η c)
    (σL : ℝ) where
  C : ℝ
  C_pos : 0 < C
  α : ℝ
  α_pos : 0 < α
  signed_bound : ∀ N : ℕ, 2 ≤ N →
    |h15ContourTraceNamedTotal N η c +
      h15ResolvedSpectralLedger
        D rationalAnalyticEstermannAtZeroPackage N σL| ≤
      C / (Real.log (N : ℝ)) ^ α

/-- A trace decomposition plus the genuinely signed estimate gives the
existing coupled H15 cancellation interface. -/
noncomputable def H15ResolvedSignedSpectralEstimate.toCoupledEstimate
    {η c : ℝ} {D : H15ResolvedDualSpectralDecomposition η c}
    {σL : ℝ} (hη : 0 < η) (hc : 1 < c)
    (F : H15EvaluationContourFamily
      (estermannGaussianEvaluationWeight η) σL c)
    (E : H15ResolvedSignedSpectralEstimate D σL) :
    CoupledLogTaperCancellationEstimate where
  C := E.C
  C_pos := E.C_pos
  α := E.α
  α_pos := E.α_pos
  bound N hN := by
    rw [coupledGcdRatioExpression_eq_named_add_spectralLedger
      D N σL hη hc F]
    exact E.signed_bound N hN

end RH.Criteria.NymanBeurling.BCFLogTaperH15ResolvedSpectralSplit
