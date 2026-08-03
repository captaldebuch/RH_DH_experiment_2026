import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmPairedResonance

/-!
# Gate 5: coupled retained terms and paired nonzero modes

This module replaces the normalized nonzero kernel phase by the exact paired
main-plus-near additive row inside the already proved Vaaler reconstruction.
The smooth main term, linear remainder, endpoint correction, paired bilinear
row, and Vaaler error remain in one finite expression throughout.

The identities below contain no asymptotic estimate.  In particular, they do
not bound the paired, resonant, or nonresonant contributions separately.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmGate5CoupledReconstruction

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmAlternativeRoutes
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCoupledNearCoreTarget
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCutoffAverageMainTerm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmExplicitFarCutoff
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFourierResonanceAudit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFullVaalerLift
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPairedAdditiveRows
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPairedResonance
open RH.Criteria.NymanBeurling.BCFLogTaperEhmVaalerAnalyticGate
open RH.Criteria.NymanBeurling.BCFLogTaperEhmVaalerNormalizedCharacters
open RH.Criteria.NymanBeurling.QuadraticInteraction

/-! ## The paired form of all nonzero Vaaler modes -/

/-- The complete nonzero frequency sum after every normalized kernel phase
has been replaced by its single paired main-plus-near additive row. -/
noncomputable def ehmDyadicVaalerPairedNonzeroModes
    (V : VaalerSawtoothPackage) (H X D J : ℕ) : ℂ :=
  ehmDyadicVaalerPairedFrequencyRange
    ((V.frequencies H).erase 0) (V.coefficient H)
    X D J 1 (2 * X)

/-- Exact replacement of the original nonzero kernel modes by paired rows.
The Type-I/II splitting point disappears because the two `m`-ranges have
already been reconstructed as `1 ≤ m ≤ 2X`. -/
theorem ehmDyadicVaalerKernelNormalNonzeroModes_eq_paired
    (V : VaalerSawtoothPackage) (H X D J U : ℕ)
    (hX : 1 ≤ X) (hU : U ≤ 2 * X) :
    ehmDyadicVaalerKernelNormalNonzeroModes V H X D J U =
      ehmDyadicVaalerPairedNonzeroModes V H X D J := by
  rw [ehmDyadicVaalerKernelNormalNonzeroModes_eq_normalized]
  classical
  unfold ehmDyadicVaalerPairedNonzeroModes
    ehmDyadicVaalerPairedFrequencyRange
  apply Finset.sum_congr rfl
  intro h _
  rw [ehmDyadicVaalerNormalizedKernelPhaseForm_eq_pairedAdditiveRows
    h X D J U hX hU]

/-! ## One expression retaining all five coupled pieces -/

/-- Gate 5 normal form.  In order, its terms are the smooth main contribution,
the linear correction, the endpoint correction, the paired bilinear nonzero
mode, and the Vaaler approximation error. -/
noncomputable def ehmDyadicVaalerGate5CoupledCore
    (V : VaalerSawtoothPackage) (H X J U : ℕ) : ℂ :=
  (ehmDyadicKernelNormalCoupledPart ehmR1SmoothPart X
      (ehmExplicitFarCutoff X) J U : ℂ) +
    ((∑ N ∈ ehmDyadicNBlock X, ehmCoupledRemainder N : ℝ) : ℂ) +
    (ehmDyadicEndpointKernelNormalClosed X
      (ehmExplicitFarCutoff X) J U : ℂ) -
    ehmDyadicVaalerPairedNonzeroModes V H X
      (ehmExplicitFarCutoff X) J -
    ehmDyadicVaalerKernelNormalError V H X
      (ehmExplicitFarCutoff X) J U

/-- The Gate 5 expression is definitionally compatible with the previous
reconstructed core after the exact paired-row substitution. -/
theorem ehmDyadicVaalerReconstructedCore_eq_gate5CoupledCore
    (V : VaalerSawtoothPackage) (H X J U : ℕ)
    (hX : 1 ≤ X) (hU : U ≤ 2 * X) :
    ehmDyadicVaalerReconstructedCore V H X J U =
      ehmDyadicVaalerGate5CoupledCore V H X J U := by
  unfold ehmDyadicVaalerReconstructedCore
    ehmDyadicVaalerCenteredNonzeroCharacterResidual
    ehmDyadicVaalerRetainedCorrection
    ehmDyadicVaalerGate5CoupledCore
  rw [ehmDyadicVaalerKernelNormalNonzeroModes_eq_paired
    V H X (ehmExplicitFarCutoff X) J U hX hU]
  push_cast
  ring

/-- Exact finite reconstruction of the original real Ehm near core with all
Gate 5 terms visibly coupled in one complex expression. -/
theorem ehmDyadicExplicitCutoffCoupledNearCore_eq_gate5CoupledCore
    (V : VaalerSawtoothPackage)
    (hV : VaalerSawtoothHasZeroCoefficient V)
    (H X J U : ℕ) (hX : 1 ≤ X) (hU : U ≤ 2 * X) :
    ((ehmDyadicExplicitCoupledNearCore ehmR1 X
      (ehmExplicitFarCutoff X) J : ℝ) : ℂ) =
        ehmDyadicVaalerGate5CoupledCore V H X J U := by
  rw [ehmDyadicExplicitCutoffCoupledNearCore_eq_vaalerReconstruction
    V hV H X J U hU]
  exact ehmDyadicVaalerReconstructedCore_eq_gate5CoupledCore
    V H X J U hX hU

/-! ## Resonant/nonresonant refinement without decoupling -/

/-- The same five-term core with the paired frequency range split exactly at
`m ∣ h*n`.  Both pieces remain inside the original signed expression. -/
noncomputable def ehmDyadicVaalerGate5ResonanceCore
    (V : VaalerSawtoothPackage) (H X J U : ℕ) : ℂ :=
  (ehmDyadicKernelNormalCoupledPart ehmR1SmoothPart X
      (ehmExplicitFarCutoff X) J U : ℂ) +
    ((∑ N ∈ ehmDyadicNBlock X, ehmCoupledRemainder N : ℝ) : ℂ) +
    (ehmDyadicEndpointKernelNormalClosed X
      (ehmExplicitFarCutoff X) J U : ℂ) -
    ehmDyadicVaalerPairedResonantFrequencyRange
      ((V.frequencies H).erase 0) (V.coefficient H)
      X (ehmExplicitFarCutoff X) J 1 (2 * X) -
    ehmDyadicVaalerPairedNonresonantFrequencyRange
      ((V.frequencies H).erase 0) (V.coefficient H)
      X (ehmExplicitFarCutoff X) J 1 (2 * X) -
    ehmDyadicVaalerKernelNormalError V H X
      (ehmExplicitFarCutoff X) J U

/-- Exact refinement of the paired Gate 5 core into resonant and
nonresonant coordinates, with no triangle inequality or separate bound. -/
theorem ehmDyadicVaalerGate5CoupledCore_eq_resonanceCore
    (V : VaalerSawtoothPackage) (H X J U : ℕ) :
    ehmDyadicVaalerGate5CoupledCore V H X J U =
      ehmDyadicVaalerGate5ResonanceCore V H X J U := by
  unfold ehmDyadicVaalerGate5CoupledCore
    ehmDyadicVaalerPairedNonzeroModes
    ehmDyadicVaalerGate5ResonanceCore
  rw [ehmDyadicVaalerPairedFrequencyRange_eq_resonant_add_nonresonant]
  ring

/-- Direct exact reconstruction in the resonance coordinates.  This theorem
does not claim cancellation of either coordinate set. -/
theorem ehmDyadicExplicitCutoffCoupledNearCore_eq_gate5ResonanceCore
    (V : VaalerSawtoothPackage)
    (hV : VaalerSawtoothHasZeroCoefficient V)
    (H X J U : ℕ) (hX : 1 ≤ X) (hU : U ≤ 2 * X) :
    ((ehmDyadicExplicitCoupledNearCore ehmR1 X
      (ehmExplicitFarCutoff X) J : ℝ) : ℂ) =
        ehmDyadicVaalerGate5ResonanceCore V H X J U := by
  rw [ehmDyadicExplicitCutoffCoupledNearCore_eq_gate5CoupledCore
      V hV H X J U hX hU,
    ehmDyadicVaalerGate5CoupledCore_eq_resonanceCore]

end RH.Criteria.NymanBeurling.BCFLogTaperEhmGate5CoupledReconstruction
