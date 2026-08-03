import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmGate4Strategy

/-!
# Gate 4: correction-coupled finite dispersion interface

This module records the exact finite block interface left by the primitive
reindexing and Parseval audit.  It declares no analytic estimate instance.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmGate4Dispersion

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmExplicitFarCutoff
open RH.Criteria.NymanBeurling.BCFLogTaperEhmGate4Strategy
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTSectorCoupling
open RH.Criteria.NymanBeurling.QuadraticInteraction

/-- A finite block decomposition of the exact canonical Gate-4 core.

The correction and `g = 1` main sector are distributed among the same blocks
as the primitive off-diagonal modes. -/
structure PrimitiveCoupledBlockDecomposition
    (V : VaalerSawtoothPackage) (Q X J U Y : ℕ) where
  blocks : Finset ℕ
  correctionMainShare : ℕ → ℂ
  offDiagonalShare : ℕ → ℂ
  correctionMain_sum :
    (∑ i ∈ blocks, correctionMainShare i) =
      (ehmMSTTHighSectorRetainedCorrection X
        (ehmExplicitFarCutoff X) J U Y : ℂ) -
      highProductPrimitiveMainModes V Q X
        (ehmExplicitFarCutoff X) J Y
  offDiagonal_sum :
    (∑ i ∈ blocks, offDiagonalShare i) =
      highProductPrimitiveOffDiagonalModes V Q X
        (ehmExplicitFarCutoff X) J Y

/-- The coupled residual assigned to one finite block. -/
noncomputable def PrimitiveCoupledBlockDecomposition.blockResidual
    {V : VaalerSawtoothPackage} {Q X J U Y : ℕ}
    (B : PrimitiveCoupledBlockDecomposition V Q X J U Y) (i : ℕ) : ℂ :=
  B.correctionMainShare i - B.offDiagonalShare i

/-- Exact finite reassembly of all correction-coupled blocks. -/
theorem PrimitiveCoupledBlockDecomposition.sum_blockResidual
    {V : VaalerSawtoothPackage} {Q X J U Y : ℕ}
    (B : PrimitiveCoupledBlockDecomposition V Q X J U Y) :
    (∑ i ∈ B.blocks, B.blockResidual i) =
      highProductCanonicalPrimitiveCoupledCore V Q X J U Y := by
  unfold PrimitiveCoupledBlockDecomposition.blockResidual
    highProductCanonicalPrimitiveCoupledCore
  rw [Finset.sum_sub_distrib, B.correctionMain_sum,
    B.offDiagonal_sum]

/-- The remaining Stage-3 analytic input.  An instance must choose finite
blocks (intended to be dyadic `(g,q)` blocks), partition the matching
correction exactly, and prove a signed cofinal dispersion bound. -/
structure EhmGate4PrimitiveCoupledDispersionEstimate where
  V : VaalerSawtoothPackage
  degree : ℕ → ℕ → ℕ
  U : ℕ → ℕ
  productCutoff : ℕ → ℕ → ℕ
  productCutoff_le : ∀ X J, productCutoff X J ≤ X
  etaHigh : ℕ → ℝ
  etaHigh_nonneg : ∀ X, 0 ≤ etaHigh X
  etaHigh_tendsto_zero : Tendsto etaHigh atTop (nhds 0)
  decomposition : ∀ X J,
    PrimitiveCoupledBlockDecomposition V (degree X J) X J
      (U X) (productCutoff X J)
  cofinal_dispersion_bound : ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      ehmExplicitFarCutoff X ≤ J ∧
      |((∑ i ∈ (decomposition X J).blocks,
        (decomposition X J).blockResidual i)).re| ≤
          ((ehmDyadicNBlock X).card : ℝ) * etaHigh X

/-- A genuine correction-coupled dispersion estimate supplies the existing
honest Gate-4/5 cofinal interface. -/
noncomputable def EhmGate4PrimitiveCoupledDispersionEstimate.toCofinalEstimate
    (H : EhmGate4PrimitiveCoupledDispersionEstimate) :
    EhmGate4Gate5CoupledCofinalEstimate where
  V := H.V
  degree := H.degree
  U := H.U
  productCutoff := H.productCutoff
  productCutoff_le := H.productCutoff_le
  etaHigh := H.etaHigh
  etaHigh_nonneg := H.etaHigh_nonneg
  etaHigh_tendsto_zero := H.etaHigh_tendsto_zero
  cofinal_bound X hX := by
    refine (H.cofinal_dispersion_bound X hX).mono ?_
    intro J hJ
    rw [(H.decomposition X J).sum_blockResidual] at hJ
    exact hJ

end RH.Criteria.NymanBeurling.BCFLogTaperEhmGate4Dispersion
