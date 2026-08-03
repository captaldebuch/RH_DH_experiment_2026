import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmSeriesBridge

/-!
# Uniform coupled boundary target for H15

The finite hyperbolic reindexing and the autocorrelation--`R₁` series bridge
reduce H15 to one uniform statement.  The statement must retain the finite
von Mangoldt boundary, the incomplete-divisor tail, and Ehm's moment
correction inside a single absolute value.

The structure in this file is an explicit open hypothesis object.  The
theorems prove that it is sufficient for the existing H15 and spectral
vanishing interfaces; they do not manufacture the RH-strength bound.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmUniformBoundary

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmKernel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmHyperbola
open RH.Criteria.NymanBeurling.BCFLogTaperEhmSeriesBridge
open RH.Criteria.NymanBeurling.BCFLogTaperSpectral

/-- The finite, fully coupled boundary expression exposed by hyperbolic
reindexing.  Its two arithmetic pieces are deliberately not bounded
separately. -/
noncomputable def ehmFiniteCoupledBoundaryExpression
    (R1 : ℝ → ℝ) (N J : ℕ) : ℝ :=
  ehmFiniteVonMangoldtBoundaryOuter R1 N +
    ehmFiniteIncompleteDivisorTailOuter R1 N J +
      ehmCoupledRemainder N

/-- At every finite cutoff `J ≥ N`, the coupled boundary expression is
exactly the hyperbolic inversion error plus Ehm's moment correction. -/
theorem ehmFiniteCoupledBoundaryExpression_eq_hyperbolic_add_remainder
    (R1 : ℝ → ℝ) (N J : ℕ) (hN : 2 ≤ N) (hNJ : N ≤ J) :
    ehmFiniteCoupledBoundaryExpression R1 N J =
      ehmFiniteHyperbolicInversionError R1 N J + ehmCoupledRemainder N := by
  rw [ehmFiniteHyperbolicInversionError_eq_boundaryOuter_add_tailOuter
    R1 N J hN hNJ]
  unfold ehmFiniteCoupledBoundaryExpression
  ring

/-- For fixed `N`, the finite coupled boundary expressions converge to the
exact Ehm coupled expression.  This is the rigorous passage `J → ∞`; it is
not uniform in `N`. -/
theorem ehmFiniteCoupledBoundaryExpression_tendsto
    {S1 R1 : ℝ → ℝ} (H : EhmR1SeriesBridge S1 R1)
    (N : ℕ) (hN : 2 ≤ N) :
    Tendsto (fun J : ℕ => ehmFiniteCoupledBoundaryExpression R1 N J)
      atTop
      (𝓝 (ehmInversionError S1 R1 N + ehmCoupledRemainder N)) := by
  have hlimit :=
    (ehmFiniteHyperbolicInversionError_tendsto H N).add_const
      (ehmCoupledRemainder N)
  apply hlimit.congr'
  filter_upwards [eventually_ge_atTop N] with J hNJ
  exact (ehmFiniteCoupledBoundaryExpression_eq_hyperbolic_add_remainder
    R1 N J hN hNJ).symm

/-- The remaining uniform H15 estimate in hyperbolic boundary variables.
For each `N`, one may discard an initial range of `J`, but the same
logarithmic bound must then hold for every larger hyperbolic cutoff.  This
uniformity is exactly what pointwise `J → ∞` convergence does not provide.

This structure is the open RH-strength input, not a proved theorem. -/
structure EhmUniformCoupledBoundaryControl (R1 : ℝ → ℝ) where
  C : ℝ
  C_pos : 0 < C
  α : ℝ
  α_pos : 0 < α
  cutoff : ℕ → ℕ
  cutoff_ge : ∀ N : ℕ, N ≤ cutoff N
  bound : ∀ N : ℕ, 2 ≤ N → ∀ J : ℕ, cutoff N ≤ J →
    |ehmFiniteCoupledBoundaryExpression R1 N J| ≤
      C / (Real.log (N : ℝ)) ^ α

/-- Uniform coupled boundary control passes to the `J → ∞` limit and gives
the exact Ehm cancellation estimate. -/
noncomputable def ehmCoupledCancellation_of_uniformBoundary
    (H : EhmKernelPackage)
    (HS : EhmR1SeriesBridge H.S1 H.R1)
    (HB : EhmUniformCoupledBoundaryControl H.R1) :
    EhmCoupledCancellationEstimate H where
  C := HB.C
  C_pos := HB.C_pos
  α := HB.α
  α_pos := HB.α_pos
  bound N hN := by
    have hlimit := (ehmFiniteCoupledBoundaryExpression_tendsto HS N hN).abs
    apply le_of_tendsto hlimit
    filter_upwards [eventually_ge_atTop (HB.cutoff N)] with J hJ
    exact HB.bound N hN J hJ

/-- Concrete open boundary-control target for the proved Ehm
autocorrelation kernel. -/
abbrev EhmAutocorrelationUniformCoupledBoundaryControl :=
  EhmUniformCoupledBoundaryControl ehmR1

/-- A concrete autocorrelation series bridge and a proof of the uniform
coupled boundary estimate instantiate the project-wide H15 estimate. -/
noncomputable def coupledLogTaperCancellation_of_ehmUniformBoundary
    (HS : EhmAutocorrelationR1SeriesBridge)
    (HB : EhmAutocorrelationUniformCoupledBoundaryControl) :
    CoupledLogTaperCancellationEstimate := by
  let HK : EhmKernelPackage :=
    ehmS1PointwiseKernelPackageProved.toEhmKernelPackage
  exact coupledLogTaperCancellation_of_ehm HK
    (ehmCoupledCancellation_of_uniformBoundary HK HS HB)

/-- Consequently, the same two inputs give spectral vanishing.  All finite
and functional-analytic bridges below this point are already proved. -/
noncomputable def spectralVanishing_of_ehmUniformBoundary
    (HS : EhmAutocorrelationR1SeriesBridge)
    (HB : EhmAutocorrelationUniformCoupledBoundaryControl) :
    SpectralVanishingEstimate :=
  spectralVanishingEstimate_of_coupledLogTaperCancellation
    (coupledLogTaperCancellation_of_ehmUniformBoundary HS HB)

end RH.Criteria.NymanBeurling.BCFLogTaperEhmUniformBoundary
