import Mathlib.Data.Real.Sqrt
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmGate4Dispersion
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmGate4Parseval

/-!
# Gate 4: hierarchy of finite dispersion bounds

This module separates three estimates that are often conflated in a
large-sieve argument:

* the exact signed real-part target needed by the current Gate-4 route;
* bounds for the norm or diagonal `L²` majorant, which still discard some
  cancellation; and
* the completely uncoupled `L¹` majorant, which discards all cancellation
  between the correction and primitive off-diagonal modes.

All implications in this file are unconditional finite inequalities.  No
decaying analytic estimate is asserted and no instance of the open Gate-4
dispersion structure is constructed.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmGate4DispersionHierarchy

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmExplicitFarCutoff
open RH.Criteria.NymanBeurling.BCFLogTaperEhmGate4Dispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmGate4Parseval
open RH.Criteria.NymanBeurling.BCFLogTaperEhmGate4Strategy
open RH.Criteria.NymanBeurling.QuadraticInteraction

/-! ## Finite majorants -/

/-- The norm of the signed, correction-coupled block sum. -/
noncomputable def primitiveCoupledSignedNorm
    {V : VaalerSawtoothPackage} {Q X J U Y : ℕ}
    (B : PrimitiveCoupledBlockDecomposition V Q X J U Y) : ℝ :=
  ‖∑ i ∈ B.blocks, B.blockResidual i‖

/-- The `L¹` norm after the residuals have been formed block by block. -/
noncomputable def primitiveCoupledResidualL1
    {V : VaalerSawtoothPackage} {Q X J U Y : ℕ}
    (B : PrimitiveCoupledBlockDecomposition V Q X J U Y) : ℝ :=
  ∑ i ∈ B.blocks, ‖B.blockResidual i‖

/-- The fully uncoupled `L¹` majorant.  This takes norms before subtracting
the off-diagonal share from the correction/main share. -/
noncomputable def primitiveCoupledUncoupledL1
    {V : VaalerSawtoothPackage} {Q X J U Y : ℕ}
    (B : PrimitiveCoupledBlockDecomposition V Q X J U Y) : ℝ :=
  ∑ i ∈ B.blocks,
    (‖B.correctionMainShare i‖ + ‖B.offDiagonalShare i‖)

/-- The diagonal energy left after all cross-block terms are discarded. -/
noncomputable def primitiveCoupledDiagonalEnergy
    {V : VaalerSawtoothPackage} {Q X J U Y : ℕ}
    (B : PrimitiveCoupledBlockDecomposition V Q X J U Y) : ℝ :=
  ∑ i ∈ B.blocks, ‖B.blockResidual i‖ ^ 2

/-- The Cauchy--Schwarz majorant obtained from the diagonal energy. -/
noncomputable def primitiveCoupledDiagonalMajorant
    {V : VaalerSawtoothPackage} {Q X J U Y : ℕ}
    (B : PrimitiveCoupledBlockDecomposition V Q X J U Y) : ℝ :=
  Real.sqrt (B.blocks.card : ℝ) *
    Real.sqrt (primitiveCoupledDiagonalEnergy B)

/-- The exact Gate-4 real-part target is bounded by the norm of the complete
signed block sum.  This step loses only the imaginary component. -/
theorem abs_re_canonicalCore_le_signedNorm
    {V : VaalerSawtoothPackage} {Q X J U Y : ℕ}
    (B : PrimitiveCoupledBlockDecomposition V Q X J U Y) :
    |(highProductCanonicalPrimitiveCoupledCore V Q X J U Y).re| ≤
      primitiveCoupledSignedNorm B := by
  rw [← B.sum_blockResidual]
  exact Complex.abs_re_le_norm _

/-- Triangle inequality after the coupled block residuals have been formed. -/
theorem signedNorm_le_residualL1
    {V : VaalerSawtoothPackage} {Q X J U Y : ℕ}
    (B : PrimitiveCoupledBlockDecomposition V Q X J U Y) :
    primitiveCoupledSignedNorm B ≤ primitiveCoupledResidualL1 B := by
  simpa [primitiveCoupledSignedNorm, primitiveCoupledResidualL1] using
    norm_sum_le B.blocks B.blockResidual

/-- Taking the correction and off-diagonal norms separately is weaker than
forming their signed residual first. -/
theorem residualL1_le_uncoupledL1
    {V : VaalerSawtoothPackage} {Q X J U Y : ℕ}
    (B : PrimitiveCoupledBlockDecomposition V Q X J U Y) :
    primitiveCoupledResidualL1 B ≤ primitiveCoupledUncoupledL1 B := by
  apply Finset.sum_le_sum
  intro i hi
  exact norm_sub_le _ _

/-- Cauchy--Schwarz converts the diagonal energy into an `L¹` majorant. -/
theorem residualL1_le_diagonalMajorant
    {V : VaalerSawtoothPackage} {Q X J U Y : ℕ}
    (B : PrimitiveCoupledBlockDecomposition V Q X J U Y) :
    primitiveCoupledResidualL1 B ≤ primitiveCoupledDiagonalMajorant B := by
  calc
    primitiveCoupledResidualL1 B =
        ∑ i ∈ B.blocks, (1 : ℝ) * ‖B.blockResidual i‖ := by
      simp [primitiveCoupledResidualL1]
    _ ≤ Real.sqrt (∑ i ∈ B.blocks, (1 : ℝ) ^ 2) *
        Real.sqrt (∑ i ∈ B.blocks, ‖B.blockResidual i‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt B.blocks
        (fun _ ↦ (1 : ℝ)) (fun i ↦ ‖B.blockResidual i‖)
    _ = primitiveCoupledDiagonalMajorant B := by
      simp [primitiveCoupledDiagonalMajorant,
        primitiveCoupledDiagonalEnergy]

/-- A completely uncoupled finite estimate is sufficient, but strictly
stronger in architecture than the signed target. -/
theorem abs_re_canonicalCore_le_uncoupledL1
    {V : VaalerSawtoothPackage} {Q X J U Y : ℕ}
    (B : PrimitiveCoupledBlockDecomposition V Q X J U Y) :
    |(highProductCanonicalPrimitiveCoupledCore V Q X J U Y).re| ≤
      primitiveCoupledUncoupledL1 B :=
  (abs_re_canonicalCore_le_signedNorm B).trans
    ((signedNorm_le_residualL1 B).trans (residualL1_le_uncoupledL1 B))

/-- A diagonal mean-square estimate is also sufficient, but it has already
discarded all cross-block terms. -/
theorem abs_re_canonicalCore_le_diagonalMajorant
    {V : VaalerSawtoothPackage} {Q X J U Y : ℕ}
    (B : PrimitiveCoupledBlockDecomposition V Q X J U Y) :
    |(highProductCanonicalPrimitiveCoupledCore V Q X J U Y).re| ≤
      primitiveCoupledDiagonalMajorant B :=
  (abs_re_canonicalCore_le_signedNorm B).trans
    ((signedNorm_le_residualL1 B).trans
      (residualL1_le_diagonalMajorant B))

/-! ## What fixed-modulus Fourier orthogonality supplies -/

/-- Parseval controls any subset of frequencies at one fixed modulus.  The
coefficients are arbitrary complex numbers, so signs are allowed; the output
is nevertheless the nonnegative one-row coefficient energy. -/
theorem primitiveFourierRow_subset_energy_le_parseval
    (X D J Y g q : ℕ) [NeZero q] (s : Finset (ZMod q)) :
    (∑ h ∈ s,
      Complex.normSq (highProductPrimitiveFourierRow X D J Y g q h)) ≤
        highProductPrimitiveParsevalEnergy X D J Y g q := by
  rw [← highProductPrimitiveFourierRow_parseval]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
  intro h _ _
  exact Complex.normSq_nonneg _

/-! ## Cofinal hierarchy -/

/-- Common finite data for comparing candidate Stage-3 bounds. -/
structure PrimitiveCoupledDispersionData where
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

/-- The exact signed real-part estimate required by the current Gate-4
pipeline.  This is the weakest of the cofinal targets below. -/
def PrimitiveCoupledDispersionData.SignedRealCofinalBound
    (D : PrimitiveCoupledDispersionData) : Prop :=
  ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      ehmExplicitFarCutoff X ≤ J ∧
      |(highProductCanonicalPrimitiveCoupledCore D.V (D.degree X J)
        X J (D.U X) (D.productCutoff X J)).re| ≤
          ((ehmDyadicNBlock X).card : ℝ) * D.etaHigh X

/-- A norm bound retains cross-block cancellation, but asks to control both
real and imaginary parts. -/
def PrimitiveCoupledDispersionData.SignedNormCofinalBound
    (D : PrimitiveCoupledDispersionData) : Prop :=
  ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      ehmExplicitFarCutoff X ≤ J ∧
      primitiveCoupledSignedNorm (D.decomposition X J) ≤
        ((ehmDyadicNBlock X).card : ℝ) * D.etaHigh X

/-- A diagonal `L²` route.  It is sufficient only if the Cauchy--Schwarz
majorant itself has the required null rate. -/
def PrimitiveCoupledDispersionData.DiagonalCofinalBound
    (D : PrimitiveCoupledDispersionData) : Prop :=
  ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      ehmExplicitFarCutoff X ≤ J ∧
      primitiveCoupledDiagonalMajorant (D.decomposition X J) ≤
        ((ehmDyadicNBlock X).card : ℝ) * D.etaHigh X

/-- The termwise absolute-value route.  This is the strongest and least
likely target because it discards the correction/off-diagonal coupling. -/
def PrimitiveCoupledDispersionData.UncoupledL1CofinalBound
    (D : PrimitiveCoupledDispersionData) : Prop :=
  ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      ehmExplicitFarCutoff X ≤ J ∧
      primitiveCoupledUncoupledL1 (D.decomposition X J) ≤
        ((ehmDyadicNBlock X).card : ℝ) * D.etaHigh X

/-- A signed norm estimate supplies the exact signed real-part target. -/
theorem PrimitiveCoupledDispersionData.SignedNormCofinalBound.toSignedReal
    {D : PrimitiveCoupledDispersionData}
    (H : D.SignedNormCofinalBound) : D.SignedRealCofinalBound := by
  intro X hX
  refine (H X hX).mono ?_
  intro J hJ
  exact ⟨hJ.1,
    (abs_re_canonicalCore_le_signedNorm (D.decomposition X J)).trans hJ.2⟩

/-- A diagonal estimate implies the signed norm estimate through the finite
Cauchy--Schwarz inequality above. -/
theorem PrimitiveCoupledDispersionData.DiagonalCofinalBound.toSignedNorm
    {D : PrimitiveCoupledDispersionData}
    (H : D.DiagonalCofinalBound) : D.SignedNormCofinalBound := by
  intro X hX
  refine (H X hX).mono ?_
  intro J hJ
  exact ⟨hJ.1,
    ((signedNorm_le_residualL1 (D.decomposition X J)).trans
      (residualL1_le_diagonalMajorant (D.decomposition X J))).trans hJ.2⟩

/-- A completely uncoupled `L¹` estimate also implies the signed norm
estimate, at the cost of discarding every relevant cross term. -/
theorem PrimitiveCoupledDispersionData.UncoupledL1CofinalBound.toSignedNorm
    {D : PrimitiveCoupledDispersionData}
    (H : D.UncoupledL1CofinalBound) : D.SignedNormCofinalBound := by
  intro X hX
  refine (H X hX).mono ?_
  intro J hJ
  exact ⟨hJ.1,
    ((signedNorm_le_residualL1 (D.decomposition X J)).trans
      (residualL1_le_uncoupledL1 (D.decomposition X J))).trans hJ.2⟩

/-- The exact signed cofinal target constructs the existing Stage-3
dispersion interface without strengthening its analytic content. -/
noncomputable def PrimitiveCoupledDispersionData.toDispersionEstimate
    (D : PrimitiveCoupledDispersionData) (H : D.SignedRealCofinalBound) :
    EhmGate4PrimitiveCoupledDispersionEstimate where
  V := D.V
  degree := D.degree
  U := D.U
  productCutoff := D.productCutoff
  productCutoff_le := D.productCutoff_le
  etaHigh := D.etaHigh
  etaHigh_nonneg := D.etaHigh_nonneg
  etaHigh_tendsto_zero := D.etaHigh_tendsto_zero
  decomposition := D.decomposition
  cofinal_dispersion_bound X hX := by
    refine (H X hX).mono ?_
    intro J hJ
    rw [(D.decomposition X J).sum_blockResidual]
    exact hJ

/-- Conversely, every existing Stage-3 estimate determines the comparison
data used by this hierarchy. -/
noncomputable def PrimitiveCoupledDispersionData.ofDispersionEstimate
    (H : EhmGate4PrimitiveCoupledDispersionEstimate) :
    PrimitiveCoupledDispersionData where
  V := H.V
  degree := H.degree
  U := H.U
  productCutoff := H.productCutoff
  productCutoff_le := H.productCutoff_le
  etaHigh := H.etaHigh
  etaHigh_nonneg := H.etaHigh_nonneg
  etaHigh_tendsto_zero := H.etaHigh_tendsto_zero
  decomposition := H.decomposition

/-- The signed target in this module is exactly the bound field of the
existing Stage-3 interface. -/
theorem PrimitiveCoupledDispersionData.signedRealCofinalBound_of_estimate
    (H : EhmGate4PrimitiveCoupledDispersionEstimate) :
    (PrimitiveCoupledDispersionData.ofDispersionEstimate H).SignedRealCofinalBound := by
  intro X hX
  refine (H.cofinal_dispersion_bound X hX).mono ?_
  intro J hJ
  rw [(H.decomposition X J).sum_blockResidual] at hJ
  exact hJ

end RH.Criteria.NymanBeurling.BCFLogTaperEhmGate4DispersionHierarchy
