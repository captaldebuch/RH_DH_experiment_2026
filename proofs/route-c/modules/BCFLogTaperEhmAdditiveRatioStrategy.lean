import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmAdditiveRatioNearFar
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmGate5CoupledReconstruction
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmDirectFeasibility

/-!
# Complete audit interface for the direct additive-ratio strategy

This module records the four work packages of the direct additive-ratio
investigation in one importable place.

* `AR1` is the exact split at `d = 2m`, together with a proved finite
  quadratic-decay majorant for the far ratio sector.
* `AR2` is the exact Vaaler reconstruction in which the smooth, linear,
  endpoint, paired nonzero-frequency, and Vaaler-error pieces remain coupled.
* `AR3` is the unconditional finite hierarchy from the signed target through
  the rowwise `L¹` and diagonal `L²` majorants.
* `AR4` identifies the correction-preserving cross-modulus balance that is
  sufficient to construct the existing Gate-4 dispersion estimate.

The last item is an implication, not a proof of the balance.  Consequently
this file does not assert H15 cancellation or the Riemann hypothesis.  It
states precisely where ordinary rowwise Parseval/large-sieve information
stops and where a bilinear trace or signed cross-modulus theorem must enter.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmAdditiveRatioStrategy

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmAdditiveRatioNearFar
open RH.Criteria.NymanBeurling.BCFLogTaperEhmAdditiveRatioReduction
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCoupledNearCoreTarget
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDirectFeasibility
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmExplicitFarCutoff
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFullVaalerLift
open RH.Criteria.NymanBeurling.BCFLogTaperEhmGate4Dispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmGate4DispersionHierarchy
open RH.Criteria.NymanBeurling.BCFLogTaperEhmGate4Strategy
open RH.Criteria.NymanBeurling.BCFLogTaperEhmGate5CoupledReconstruction
open RH.Criteria.NymanBeurling.BCFLogTaperEhmKernel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmQGeTwoCollapse
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.QuadraticInteraction

/-! ## AR1: exact near/far decomposition -/

/-- Canonical AR1 identity for the concrete Ehm autocorrelation kernel. -/
theorem additiveRatio_AR1_exact_near_far
    (X D U : ℕ) :
    ehmDyadicNearTypeIQGeTwoSeriesLimit
        ehmS1Autocorrelation ehmR1 X D U =
      (∑ N ∈ ehmDyadicNBlock X,
        ehmQGeTwoNearRatioSlice ehmS1Autocorrelation ehmR1 X D U N) +
      (∑ N ∈ ehmDyadicNBlock X,
        ehmQGeTwoFarRatioSlice ehmS1Autocorrelation ehmR1 X D U N) :=
  ehmDyadicNearTypeIQGeTwoSeriesLimit_eq_near_add_far
    ehmS1Autocorrelation ehmR1 X D U

/-- Canonical AR1 far-sector estimate with the concrete constant `8`. -/
theorem additiveRatio_AR1_far_le_weighted_majorant
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (X D U N : ℕ) :
    |ehmQGeTwoFarRatioSlice ehmS1Autocorrelation ehmR1 X D U N| ≤
      ehmQGeTwoFarRatioMajorant 8 X D U N :=
  abs_ehmAutocorrelationQGeTwoFarRatioSlice_le_majorant HS X D U N

/-! ## AR2: correction-preserving Vaaler reconstruction -/

/-- AR2 does not estimate the Bernoulli modes independently.  It rewrites
the original real near core as one complex expression retaining all five
coupled pieces. -/
theorem additiveRatio_AR2_exact_coupled_vaaler_reconstruction
    (V : VaalerSawtoothPackage)
    (hV : VaalerSawtoothHasZeroCoefficient V)
    (H X J U : ℕ) (hX : 1 ≤ X) (hU : U ≤ 2 * X) :
    ((ehmDyadicExplicitCoupledNearCore ehmR1 X
      (ehmExplicitFarCutoff X) J : ℝ) : ℂ) =
        ehmDyadicVaalerGate5CoupledCore V H X J U :=
  ehmDyadicExplicitCutoffCoupledNearCore_eq_gate5CoupledCore
    V hV H X J U hX hU

/-! ## AR3: exact finite hierarchy of available bounds -/

/-- Every presently mechanical rowwise argument factors through this finite
hierarchy.  The first inequality keeps the signed sum, while the last two
discard cross-block cancellation. -/
theorem additiveRatio_AR3_finite_bound_hierarchy
    {V : VaalerSawtoothPackage} {Q X J U Y : ℕ}
    (B : PrimitiveCoupledBlockDecomposition V Q X J U Y) :
    |(highProductCanonicalPrimitiveCoupledCore V Q X J U Y).re| ≤
        primitiveCoupledSignedNorm B ∧
      primitiveCoupledSignedNorm B ≤ primitiveCoupledResidualL1 B ∧
      primitiveCoupledResidualL1 B ≤ primitiveCoupledUncoupledL1 B ∧
      primitiveCoupledResidualL1 B ≤ primitiveCoupledDiagonalMajorant B := by
  exact ⟨abs_re_canonicalCore_le_signedNorm B,
    signedNorm_le_residualL1 B,
    residualL1_le_uncoupledL1 B,
    residualL1_le_diagonalMajorant B⟩

/-! ## AR4: stop test and bilinear fallback target -/

/-- A proved correction-preserving cross-modulus balance supplies exactly
the signed cofinal bound that rowwise Parseval does not provide. -/
theorem additiveRatio_AR4_signed_bound_of_cross_modulus_balance
    {D : PrimitiveCoupledDispersionData}
    (H : EhmCrossModulusBalanceCofinalBound D) :
    D.SignedRealCofinalBound :=
  signedRealCofinalBound_of_crossModulusBalance H

/-- The same AR4 input constructs the proof object consumed by the Gate-4
pipeline.  This is the formal handoff point to a bilinear trace, dispersion,
or automorphic theorem. -/
noncomputable def additiveRatio_AR4_to_gate4_dispersion
    (D : PrimitiveCoupledDispersionData)
    (H : EhmCrossModulusBalanceCofinalBound D) :
    EhmGate4PrimitiveCoupledDispersionEstimate :=
  D.toDispersionEstimate
    (signedRealCofinalBound_of_crossModulusBalance H)

end RH.Criteria.NymanBeurling.BCFLogTaperEhmAdditiveRatioStrategy
