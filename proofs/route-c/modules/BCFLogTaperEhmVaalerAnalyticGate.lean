import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmFullVaalerLift

/-!
# Reconstructed nonzero-character gate for the Ehm route

This file substitutes the full Vaaler lift into the exact Ehm route.  The
result keeps the smooth main form, the linear correction, the endpoint
resonances, the nonzero Fourier modes, and the Vaaler error in one identity.

The final two decay estimates are exposed as fields of a structure.  They
are not proved here: the centered nonzero-character estimate is the genuine
signed H15-strength problem, while the Vaaler-error estimate requires an
explicit package and a cutoff choice.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmVaalerAnalyticGate

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmAlternativeRoutes
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCoupledNearCoreTarget
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCutoffAverageMainTerm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmExplicitFarCutoff
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFourierResonanceAudit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFullVaalerLift
open RH.Criteria.NymanBeurling.BCFLogTaperEhmHyperbolicKernelNormalForm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.QuadraticInteraction
open RH.Criteria.NymanBeurling.VasyuninGram

/-! ## Exact reconstruction -/

/-- All non-Fourier terms that must remain coupled to the additive
characters: the smooth form, the dyadic linear correction, and both endpoint
resonance sums. -/
noncomputable def ehmDyadicVaalerRetainedCorrection
    (X J U : ℕ) : ℝ :=
  ehmDyadicKernelNormalCoupledPart ehmR1SmoothPart X
      (ehmExplicitFarCutoff X) J U +
    (∑ N ∈ ehmDyadicNBlock X, ehmCoupledRemainder N) +
    ehmDyadicEndpointKernelNormalClosed X
      (ehmExplicitFarCutoff X) J U

/-- The signed arithmetic object which a reciprocal-phase theorem must
actually control.  It is not the absolute size of the Fourier sum: the
retained main, linear, and endpoint corrections are part of the cancellation. -/
noncomputable def ehmDyadicVaalerCenteredNonzeroCharacterResidual
    (V : VaalerSawtoothPackage) (H X J U : ℕ) : ℂ :=
  (ehmDyadicVaalerRetainedCorrection X J U : ℂ) -
    ehmDyadicVaalerKernelNormalNonzeroModes V H X
      (ehmExplicitFarCutoff X) J U

/-- The exact reconstructed core after also subtracting the accumulated
Vaaler approximation error. -/
noncomputable def ehmDyadicVaalerReconstructedCore
    (V : VaalerSawtoothPackage) (H X J U : ℕ) : ℂ :=
  ehmDyadicVaalerCenteredNonzeroCharacterResidual V H X J U -
    ehmDyadicVaalerKernelNormalError V H X
      (ehmExplicitFarCutoff X) J U

/-- Exact reconstruction of the original real Ehm near core.  This is the
point at which all algebraic work ends and the signed analytic estimate
begins. -/
theorem ehmDyadicExplicitCutoffCoupledNearCore_eq_vaalerReconstruction
    (V : VaalerSawtoothPackage)
    (hV : VaalerSawtoothHasZeroCoefficient V)
    (H X J U : ℕ) (hU : U ≤ 2 * X) :
    ((ehmDyadicExplicitCoupledNearCore ehmR1 X
      (ehmExplicitFarCutoff X) J : ℝ) : ℂ) =
        ehmDyadicVaalerReconstructedCore V H X J U := by
  rw [ehmDyadicExplicitCutoffCoupledNearCore_eq_routeKernelPieces X J U hU]
  push_cast
  rw [ehmDyadicKernelNormalEndpoint_eq_closed,
    ehmDyadicKernelNormalBernoulli_eq_vaaler,
    ehmDyadicVaalerKernelNormalApprox_eq_nonzeroModes V hV]
  unfold ehmDyadicVaalerReconstructedCore
    ehmDyadicVaalerCenteredNonzeroCharacterResidual
    ehmDyadicVaalerRetainedCorrection
  push_cast
  ring

theorem ehmDyadicVaalerReconstructedCore_re
    (V : VaalerSawtoothPackage)
    (hV : VaalerSawtoothHasZeroCoefficient V)
    (H X J U : ℕ) (hU : U ≤ 2 * X) :
    (ehmDyadicVaalerReconstructedCore V H X J U).re =
      ehmDyadicExplicitCoupledNearCore ehmR1 X
        (ehmExplicitFarCutoff X) J := by
  have h := congrArg Complex.re
    (ehmDyadicExplicitCutoffCoupledNearCore_eq_vaalerReconstruction
      V hV H X J U hU)
  simpa using h.symm

/-! ## What ordinary absolute-value bounds can and cannot do -/

/-- The unconditional triangle bound for the nonzero modes.  This is useful
for checking a proposed per-frequency majorant, but by itself it discards the
signed cancellation against `ehmDyadicVaalerRetainedCorrection`. -/
theorem norm_ehmDyadicVaalerKernelNormalNonzeroModes_le
    (V : VaalerSawtoothPackage) (H X D J U : ℕ) :
    ‖ehmDyadicVaalerKernelNormalNonzeroModes V H X D J U‖ ≤
      ∑ h ∈ (V.frequencies H).erase 0,
        ‖V.coefficient H h‖ *
          ‖ehmDyadicVaalerKernelNormalPhaseForm h X D J U‖ := by
  classical
  unfold ehmDyadicVaalerKernelNormalNonzeroModes
  calc
    ‖∑ h ∈ (V.frequencies H).erase 0,
        V.coefficient H h *
          ehmDyadicVaalerKernelNormalPhaseForm h X D J U‖ ≤
      ∑ h ∈ (V.frequencies H).erase 0,
        ‖V.coefficient H h *
          ehmDyadicVaalerKernelNormalPhaseForm h X D J U‖ :=
        norm_sum_le _ _
    _ = ∑ h ∈ (V.frequencies H).erase 0,
        ‖V.coefficient H h‖ *
          ‖ehmDyadicVaalerKernelNormalPhaseForm h X D J U‖ := by
      apply Finset.sum_congr rfl
      intro h _
      rw [norm_mul]

/-! ## The remaining analytic gate -/

/-- A separated formulation of the remaining work.

The character part of `cofinal_bounds` must exploit signed cancellation between the
nonzero reciprocal phases and the retained smooth/linear/endpoint terms.
It is deliberately not replaced by a termwise absolute GCD or phase bound.
The error part is the independent Vaaler truncation-error obligation.  They
are required on the same cofinal set of `J`; two merely frequent sets need
not have frequent intersection. -/
structure EhmDyadicVaalerNonzeroCharacterAnalyticGate where
  V : VaalerSawtoothPackage
  V_zero : VaalerSawtoothHasZeroCoefficient V
  degree : ℕ → ℕ → ℕ
  U : ℕ → ℕ
  U_le : ∀ X, U X ≤ 2 * X
  etaCharacter : ℕ → ℝ
  etaCharacter_nonneg : ∀ X, 0 ≤ etaCharacter X
  etaCharacter_tendsto_zero : Tendsto etaCharacter atTop (nhds 0)
  etaError : ℕ → ℝ
  etaError_nonneg : ∀ X, 0 ≤ etaError X
  etaError_tendsto_zero : Tendsto etaError atTop (nhds 0)
  cofinal_bounds : ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      ehmExplicitFarCutoff X ≤ J ∧
      |(ehmDyadicVaalerCenteredNonzeroCharacterResidual V
        (degree X J) X J (U X)).re| ≤
          ((ehmDyadicNBlock X).card : ℝ) * etaCharacter X ∧
      |(ehmDyadicVaalerKernelNormalError V (degree X J) X
        (ehmExplicitFarCutoff X) J (U X)).re| ≤
          ((ehmDyadicNBlock X).card : ℝ) * etaError X

/-- The separated character/error estimates imply the already-audited
fixed-conductor coupled analytic gate. -/
noncomputable def EhmDyadicVaalerNonzeroCharacterAnalyticGate.toExplicitKernel
    (H : EhmDyadicVaalerNonzeroCharacterAnalyticGate) :
    EhmDyadicExplicitKernelCoupledAnalyticGate where
  U := H.U
  U_le := H.U_le
  eta := fun X ↦ H.etaCharacter X + H.etaError X
  eta_nonneg := fun X ↦
    add_nonneg (H.etaCharacter_nonneg X) (H.etaError_nonneg X)
  eta_tendsto_zero := by
    simpa using H.etaCharacter_tendsto_zero.add H.etaError_tendsto_zero
  cofinal_bound X hX := by
    refine (H.cofinal_bounds X hX).mono ?_
    intro J hbounds
    refine ⟨hbounds.1, ?_⟩
    rw [← ehmDyadicExplicitCutoffCoupledNearCore_eq_kernelTypeI_typeII
      ehmR1 X J (H.U X) (H.U_le X)]
    rw [← ehmDyadicVaalerReconstructedCore_re H.V H.V_zero
      (H.degree X J) X J (H.U X) (H.U_le X)]
    unfold ehmDyadicVaalerReconstructedCore
    calc
      (ehmDyadicVaalerCenteredNonzeroCharacterResidual H.V
          (H.degree X J) X J (H.U X) -
        ehmDyadicVaalerKernelNormalError H.V (H.degree X J) X
          (ehmExplicitFarCutoff X) J (H.U X)).re =
        (ehmDyadicVaalerCenteredNonzeroCharacterResidual H.V
          (H.degree X J) X J (H.U X)).re -
        (ehmDyadicVaalerKernelNormalError H.V (H.degree X J) X
          (ehmExplicitFarCutoff X) J (H.U X)).re := rfl
      _ ≤ |(ehmDyadicVaalerCenteredNonzeroCharacterResidual H.V
            (H.degree X J) X J (H.U X)).re| +
          |(ehmDyadicVaalerKernelNormalError H.V (H.degree X J) X
            (ehmExplicitFarCutoff X) J (H.U X)).re| := by
        have ha := le_abs_self
          (ehmDyadicVaalerCenteredNonzeroCharacterResidual H.V
            (H.degree X J) X J (H.U X)).re
        have hb := neg_le_abs
          (ehmDyadicVaalerKernelNormalError H.V (H.degree X J) X
            (ehmExplicitFarCutoff X) J (H.U X)).re
        linarith
      _ ≤ ((ehmDyadicNBlock X).card : ℝ) * H.etaCharacter X +
          ((ehmDyadicNBlock X).card : ℝ) * H.etaError X :=
        add_le_add hbounds.2.1 hbounds.2.2
      _ = ((ehmDyadicNBlock X).card : ℝ) *
          (H.etaCharacter X + H.etaError X) := by ring

/-- Conditional closure from precisely the two remaining Vaaler-route
estimates.  Constructing the hypothesis is the open analytic problem. -/
theorem baezDuarteCriterion_of_ehmDyadicVaalerNonzeroCharacterAnalyticGate
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (H : EhmDyadicVaalerNonzeroCharacterAnalyticGate) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmDyadicExplicitKernelCoupledAnalyticGate
    HS H.toExplicitKernel

end RH.Criteria.NymanBeurling.BCFLogTaperEhmVaalerAnalyticGate
