import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmMSTTCenteredGate

/-!
# Product-sector coupling of the retained Ehm correction

The first centered MSTT gate kept the complete smooth, linear, and endpoint
correction beside the low-product modes and treated the high-product modes
separately.  That split is formally sufficient but analytically wasteful:
the high modes can cancel against the high-product part of the same retained
correction.

This module splits the completed main correction at the exact product cutoff.
The near-divisor correction is assigned to the high sector; when `Y <= X`
this matches the exact fact that every low paired row is main-only.  Gate 5
then has the sector-coupled form

`(low correction - low modes) + (high correction - high modes) - error`.

No estimate is asserted by the finite identities.  The final structure asks
for the two signed sector estimates and the Vaaler error on one common
cofinal set and proves that they imply the existing H15 analytic gate.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTSectorCoupling

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
open RH.Criteria.NymanBeurling.BCFLogTaperEhmGate5CoupledReconstruction
open RH.Criteria.NymanBeurling.BCFLogTaperEhmHyperbolicKernelNormalForm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTCenteredGate
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTNormalizationAudit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmProductTruncation
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmVaalerAnalyticGate
open RH.Criteria.NymanBeurling.QuadraticInteraction

/-! ## Exact product split of the completed main form -/

private theorem low_union_high_eq_full (J Y : ℕ) :
    ehmDyadicVaalerLowProductRange J Y ∪
        ehmDyadicVaalerHighProductRange J Y =
      Finset.Icc 2 J := by
  ext n
  simp only [Finset.mem_union,
    mem_ehmDyadicVaalerLowProductRange_iff,
    mem_ehmDyadicVaalerHighProductRange_iff, Finset.mem_Icc]
  omega

private theorem low_disjoint_high (J Y : ℕ) :
    Disjoint (ehmDyadicVaalerLowProductRange J Y)
      (ehmDyadicVaalerHighProductRange J Y) := by
  apply Finset.disjoint_left.mpr
  intro n hnLow hnHigh
  have hnY :=
    (mem_ehmDyadicVaalerLowProductRange_iff J Y n).1 hnLow |>.2.2
  have hYn :=
    (mem_ehmDyadicVaalerHighProductRange_iff J Y n).1 hnHigh |>.2.2
  omega

/-- The part of the completed main transform below the product cutoff. -/
noncomputable def ehmMSTTFullMainLowProductJointSum
    (R1 : ℝ → ℝ) (X J Y : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 (2 * X),
    ∑ n ∈ ehmDyadicVaalerLowProductRange J Y,
      ArithmeticFunction.vonMangoldt n *
        ehmDyadicMobiusCutoffCoeff X m * R1 ((n : ℝ) / (m : ℝ))

/-- The complementary part of the completed main transform. -/
noncomputable def ehmMSTTFullMainHighProductJointSum
    (R1 : ℝ → ℝ) (X J Y : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 (2 * X),
    ∑ n ∈ ehmDyadicVaalerHighProductRange J Y,
      ArithmeticFunction.vonMangoldt n *
        ehmDyadicMobiusCutoffCoeff X m * R1 ((n : ℝ) / (m : ℝ))

/-- Exact low/high product split of the completed von-Mangoldt transform. -/
theorem ehmDyadicFullMainJointSum_eq_productLow_add_high
    (R1 : ℝ → ℝ) (X J Y : ℕ) :
    ehmDyadicFullMainJointSum R1 X J =
      ehmMSTTFullMainLowProductJointSum R1 X J Y +
        ehmMSTTFullMainHighProductJointSum R1 X J Y := by
  classical
  unfold ehmDyadicFullMainJointSum
    ehmMSTTFullMainLowProductJointSum
    ehmMSTTFullMainHighProductJointSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [← Finset.sum_union (low_disjoint_high J Y),
    low_union_high_eq_full]

/-- Every hyperbolic near coordinate `d*q` lies in the high-product range
when the cutoff is below the outer scale.  This justifies assigning all near
smooth and endpoint corrections to the high sector. -/
theorem ehmNearProduct_mem_highProductRange
    {X J Y d q : ℕ} (hX : 1 ≤ X) (hY : Y ≤ X)
    (hd : d ∈ Finset.Icc (X + 1) J)
    (hq : q ∈ Finset.Icc 1 J) (hdq : d * q ≤ J) :
    d * q ∈ ehmDyadicVaalerHighProductRange J Y := by
  rw [mem_ehmDyadicVaalerHighProductRange_iff]
  have hdlo := (Finset.mem_Icc.mp hd).1
  have hqpos := (Finset.mem_Icc.mp hq).1
  have hdle : d ≤ d * q := by
    nlinarith
  constructor
  · omega
  exact ⟨hdq, lt_of_le_of_lt hY (lt_of_lt_of_le (by omega) hdle)⟩

/-! ## Retained correction split -/

/-- The correction assigned to the low main sector.  The linear remainder
is kept here because it is the correction paired with the completed main
Möbius--von-Mangoldt transform. -/
noncomputable def ehmMSTTLowSectorRetainedCorrection
    (X J Y : ℕ) : ℝ :=
  ehmMSTTFullMainLowProductJointSum ehmR1SmoothPart X J Y +
    ehmMSTTFullMainLowProductJointSum ehmR1IntegerEndpointPart X J Y +
    ∑ N ∈ ehmDyadicNBlock X, ehmCoupledRemainder N

/-- The complementary correction: high completed-main coordinates together
with every smooth and endpoint near-divisor coordinate. -/
noncomputable def ehmMSTTHighSectorRetainedCorrection
    (X D J U Y : ℕ) : ℝ :=
  ehmMSTTFullMainHighProductJointSum ehmR1SmoothPart X J Y +
    ehmDyadicNearKernelTypeI ehmR1SmoothPart X D J U +
    ehmDyadicNearKernelTypeII ehmR1SmoothPart X D J U +
    ehmMSTTFullMainHighProductJointSum
      ehmR1IntegerEndpointPart X J Y +
    ehmDyadicNearKernelTypeI ehmR1IntegerEndpointPart X D J U +
    ehmDyadicNearKernelTypeII ehmR1IntegerEndpointPart X D J U

/-- The retained correction is exactly the sum of its product sectors. -/
theorem ehmDyadicVaalerRetainedCorrection_eq_lowSector_add_highSector
    (X J U Y : ℕ) :
    ehmDyadicVaalerRetainedCorrection X J U =
      ehmMSTTLowSectorRetainedCorrection X J Y +
        ehmMSTTHighSectorRetainedCorrection X
          (ehmExplicitFarCutoff X) J U Y := by
  unfold ehmDyadicVaalerRetainedCorrection
  rw [← ehmDyadicKernelNormalEndpoint_eq_closed]
  unfold ehmDyadicKernelNormalCoupledPart
    ehmMSTTLowSectorRetainedCorrection
    ehmMSTTHighSectorRetainedCorrection
  rw [ehmDyadicFullMainJointSum_eq_productLow_add_high,
    ehmDyadicFullMainJointSum_eq_productLow_add_high]
  ring

/-! ## Two correction-coupled product sectors -/

/-- Low main rows centered by precisely their own retained correction. -/
noncomputable def ehmMSTTLowSectorCoupledResidual
    (V : VaalerSawtoothPackage) (Q X J Y : ℕ) : ℂ :=
  (ehmMSTTLowSectorRetainedCorrection X J Y : ℂ) -
    ehmDyadicVaalerPairedLowProductModes V Q X
      (ehmExplicitFarCutoff X) J Y

/-- High main and near rows centered by their matching smooth and endpoint
correction. -/
noncomputable def ehmMSTTHighSectorCoupledResidual
    (V : VaalerSawtoothPackage) (Q X J U Y : ℕ) : ℂ :=
  (ehmMSTTHighSectorRetainedCorrection X
    (ehmExplicitFarCutoff X) J U Y : ℂ) -
      ehmDyadicVaalerPairedHighProductModes V Q X
        (ehmExplicitFarCutoff X) J Y

/-- Under the structural cutoff condition, the low coupled residual contains
the main-only MSTT modes and no hidden near-divisor summand. -/
theorem ehmMSTTLowSectorCoupledResidual_eq_main_of_cutoff_le
    (V : VaalerSawtoothPackage) (Q X J Y : ℕ) (hY : Y ≤ X) :
    ehmMSTTLowSectorCoupledResidual V Q X J Y =
      (ehmMSTTLowSectorRetainedCorrection X J Y : ℂ) -
        ehmMSTTMainLowProductModes V Q X J Y := by
  unfold ehmMSTTLowSectorCoupledResidual
  rw [ehmDyadicVaalerPairedLowProductModes_eq_main_of_cutoff_le
    V Q X (ehmExplicitFarCutoff X) J Y hY]

/-- Exact sector-coupled decomposition of the signed nonzero-character
residual. -/
theorem ehmDyadicVaalerCenteredNonzeroCharacterResidual_eq_sectorResiduals
    (V : VaalerSawtoothPackage)
    (Q X J U Y : ℕ) (hX : 1 ≤ X) (hU : U ≤ 2 * X) :
    ehmDyadicVaalerCenteredNonzeroCharacterResidual V Q X J U =
      ehmMSTTLowSectorCoupledResidual V Q X J Y +
        ehmMSTTHighSectorCoupledResidual V Q X J U Y := by
  unfold ehmDyadicVaalerCenteredNonzeroCharacterResidual
    ehmMSTTLowSectorCoupledResidual
    ehmMSTTHighSectorCoupledResidual
  rw [ehmDyadicVaalerKernelNormalNonzeroModes_eq_paired
      V Q X (ehmExplicitFarCutoff X) J U hX hU,
    ehmDyadicVaalerPairedNonzeroModes_eq_low_add_high,
    ehmDyadicVaalerRetainedCorrection_eq_lowSector_add_highSector]
  push_cast
  ring

/-- Exact Gate-5 form with cancellation preserved separately in both
product sectors. -/
theorem ehmDyadicVaalerGate5CoupledCore_eq_sectorResiduals_sub_error
    (V : VaalerSawtoothPackage) (Q X J U Y : ℕ) :
    ehmDyadicVaalerGate5CoupledCore V Q X J U =
      ehmMSTTLowSectorCoupledResidual V Q X J Y +
        ehmMSTTHighSectorCoupledResidual V Q X J U Y -
        ehmDyadicVaalerKernelNormalError V Q X
          (ehmExplicitFarCutoff X) J U := by
  calc
    ehmDyadicVaalerGate5CoupledCore V Q X J U =
        (ehmDyadicVaalerRetainedCorrection X J U : ℂ) -
          ehmDyadicVaalerPairedNonzeroModes V Q X
            (ehmExplicitFarCutoff X) J -
          ehmDyadicVaalerKernelNormalError V Q X
            (ehmExplicitFarCutoff X) J U := by
      unfold ehmDyadicVaalerGate5CoupledCore
        ehmDyadicVaalerRetainedCorrection
      push_cast
      ring
    _ = _ := by
      rw [ehmDyadicVaalerPairedNonzeroModes_eq_low_add_high,
        ehmDyadicVaalerRetainedCorrection_eq_lowSector_add_highSector]
      unfold ehmMSTTLowSectorCoupledResidual
        ehmMSTTHighSectorCoupledResidual
      push_cast
      ring

/-! ## Refined common-cofinal analytic gate -/

/-- The sector-coupled form of the remaining H15 estimate.

For `productCutoff X J <= X`, the low residual contains only completed-main
rows, while all near-divisor rows and their corrections occur in the high
residual.  Both signed cancellations are retained until after the product
split. -/
structure EhmMSTTSectorCoupledAnalyticGate where
  V : VaalerSawtoothPackage
  V_zero : VaalerSawtoothHasZeroCoefficient V
  degree : ℕ → ℕ → ℕ
  U : ℕ → ℕ
  U_le : ∀ X, U X ≤ 2 * X
  productCutoff : ℕ → ℕ → ℕ
  productCutoff_le : ∀ X J, productCutoff X J ≤ X
  etaLow : ℕ → ℝ
  etaLow_nonneg : ∀ X, 0 ≤ etaLow X
  etaLow_tendsto_zero : Tendsto etaLow atTop (nhds 0)
  etaHigh : ℕ → ℝ
  etaHigh_nonneg : ∀ X, 0 ≤ etaHigh X
  etaHigh_tendsto_zero : Tendsto etaHigh atTop (nhds 0)
  etaError : ℕ → ℝ
  etaError_nonneg : ∀ X, 0 ≤ etaError X
  etaError_tendsto_zero : Tendsto etaError atTop (nhds 0)
  cofinal_bounds : ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      ehmExplicitFarCutoff X ≤ J ∧
      |(ehmMSTTLowSectorCoupledResidual V
        (degree X J) X J (productCutoff X J)).re| ≤
          ((ehmDyadicNBlock X).card : ℝ) * etaLow X ∧
      |(ehmMSTTHighSectorCoupledResidual V
        (degree X J) X J (U X) (productCutoff X J)).re| ≤
          ((ehmDyadicNBlock X).card : ℝ) * etaHigh X ∧
      |(ehmDyadicVaalerKernelNormalError V (degree X J) X
        (ehmExplicitFarCutoff X) J (U X)).re| ≤
          ((ehmDyadicNBlock X).card : ℝ) * etaError X

/-- The sector-coupled estimates imply the existing nonzero-character gate. -/
noncomputable def EhmMSTTSectorCoupledAnalyticGate.toNonzeroCharacter
    (H : EhmMSTTSectorCoupledAnalyticGate) :
    EhmDyadicVaalerNonzeroCharacterAnalyticGate where
  V := H.V
  V_zero := H.V_zero
  degree := H.degree
  U := H.U
  U_le := H.U_le
  etaCharacter := fun X ↦ H.etaLow X + H.etaHigh X
  etaCharacter_nonneg := fun X ↦
    add_nonneg (H.etaLow_nonneg X) (H.etaHigh_nonneg X)
  etaCharacter_tendsto_zero := by
    simpa using H.etaLow_tendsto_zero.add H.etaHigh_tendsto_zero
  etaError := H.etaError
  etaError_nonneg := H.etaError_nonneg
  etaError_tendsto_zero := H.etaError_tendsto_zero
  cofinal_bounds X hX := by
    refine (H.cofinal_bounds X hX).mono ?_
    intro J hbounds
    refine ⟨hbounds.1, ?_, hbounds.2.2.2⟩
    rw [ehmDyadicVaalerCenteredNonzeroCharacterResidual_eq_sectorResiduals
      H.V (H.degree X J) X J (H.U X) (H.productCutoff X J)
      (by omega) (H.U_le X)]
    calc
      |(ehmMSTTLowSectorCoupledResidual H.V
          (H.degree X J) X J (H.productCutoff X J) +
        ehmMSTTHighSectorCoupledResidual H.V
          (H.degree X J) X J (H.U X) (H.productCutoff X J)).re| ≤
          |(ehmMSTTLowSectorCoupledResidual H.V
            (H.degree X J) X J (H.productCutoff X J)).re| +
          |(ehmMSTTHighSectorCoupledResidual H.V
            (H.degree X J) X J (H.U X) (H.productCutoff X J)).re| := by
              simpa only [Complex.add_re] using
                (abs_add_le
                  (ehmMSTTLowSectorCoupledResidual H.V
                    (H.degree X J) X J (H.productCutoff X J)).re
                  (ehmMSTTHighSectorCoupledResidual H.V
                    (H.degree X J) X J (H.U X)
                    (H.productCutoff X J)).re)
      _ ≤ ((ehmDyadicNBlock X).card : ℝ) * H.etaLow X +
          ((ehmDyadicNBlock X).card : ℝ) * H.etaHigh X :=
        add_le_add hbounds.2.1 hbounds.2.2.1
      _ = ((ehmDyadicNBlock X).card : ℝ) *
          (H.etaLow X + H.etaHigh X) := by ring

/-- Conditional Báez--Duarte closure from the strongest presently justified
sector-coupled interface. -/
theorem baezDuarteCriterion_of_ehmMSTTSectorCoupledAnalyticGate
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (H : EhmMSTTSectorCoupledAnalyticGate) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmDyadicVaalerNonzeroCharacterAnalyticGate
    HS H.toNonzeroCharacter

end RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTSectorCoupling
