import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmMSTTPrefixRecursion

/-!
# The centered MSTT gate

The exact normalization audit shows that a sum of absolute short-window
MSTT objectives is not the right final target.  The low-product modes must
remain signed against the smooth main term, the linear correction, and the
endpoint resonances.

This file records that corrected architecture.  It splits the complete
centered nonzero-character residual into

* one correction-coupled low-product residual, and
* the signed high-product modes.

The Vaaler approximation error remains a third, independent obligation.
The low-product residual is also expanded through the first recursive
dyadic prefix step without taking absolute values of its constituents.

All identities in the first two sections are finite and unconditional.  The
structure in the final section states the three genuinely analytic bounds
on one common cofinal set and proves that they imply the existing H15
analytic gate.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTCenteredGate

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCoupledNearCoreTarget
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmExplicitFarCutoff
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFullVaalerLift
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFourierResonanceAudit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmGate5CoupledReconstruction
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTLowRows
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTNormalizationAudit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTOptimization
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTPrefixRecursion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTVariation
open RH.Criteria.NymanBeurling.BCFLogTaperEhmProductTruncation
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmVaalerAnalyticGate
open RH.Criteria.NymanBeurling.QuadraticInteraction

/-! ## Exact disappearance of near-divisor rows below the outer scale -/

/-- The main-only low-product row to which the MSTT polynomial-phase
estimate is genuinely applicable. -/
noncomputable def ehmMSTTMainLowProductRow
    (h : ℤ) (X J Y m : ℕ) : ℂ :=
  ∑ n ∈ ehmDyadicVaalerLowProductRange J Y,
    ehmMSTTMainProductWeight X n m *
      ehmVaalerRationalPhase h n 1 m

/-- If the product cutoff lies below the outer scale, the complete paired
low row is definitionally equal to its main-only row. -/
theorem ehmDyadicVaalerPairedLowProductRow_eq_main_of_cutoff_le
    (h : ℤ) (X D J Y m : ℕ) (hY : Y ≤ X) :
    ehmDyadicVaalerPairedLowProductRow h X D J Y m =
      ehmMSTTMainLowProductRow h X J Y m := by
  classical
  unfold ehmDyadicVaalerPairedLowProductRow
    ehmDyadicVaalerPairedProductSummand
    ehmMSTTMainLowProductRow
  apply Finset.sum_congr rfl
  intro n hn
  have hn' := (mem_ehmDyadicVaalerLowProductRange_iff J Y n).1 hn
  have hnX : n ≤ X := hn'.2.2.trans hY
  change ehmMSTTLowProductWeight X D n m *
      ehmVaalerRationalPhase h n 1 m =
    ehmMSTTMainProductWeight X n m *
      ehmVaalerRationalPhase h n 1 m
  rw [ehmMSTTLowProductWeight_eq_main_of_le X D n m
    (by omega) hnX]

/-- Main-only low rows on an arbitrary outer Möbius range. -/
noncomputable def ehmMSTTMainLowProductRowsMRange
    (h : ℤ) (X J Y mLo mHi : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc mLo mHi,
    ((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
      ehmMSTTMainLowProductRow h X J Y m)

/-- The row equality lifts through the signed Möbius range. -/
theorem ehmDyadicVaalerPairedLowProductRowsMRange_eq_main_of_cutoff_le
    (h : ℤ) (X D J Y mLo mHi : ℕ) (hY : Y ≤ X) :
    ehmDyadicVaalerPairedLowProductRowsMRange
        h X D J Y mLo mHi =
      ehmMSTTMainLowProductRowsMRange h X J Y mLo mHi := by
  classical
  unfold ehmDyadicVaalerPairedLowProductRowsMRange
    ehmMSTTMainLowProductRowsMRange
  apply Finset.sum_congr rfl
  intro m _
  rw [ehmDyadicVaalerPairedLowProductRow_eq_main_of_cutoff_le
    h X D J Y m hY]

/-- Main-only low rows lifted through every Vaaler frequency. -/
noncomputable def ehmMSTTMainLowProductModes
    (V : VaalerSawtoothPackage) (Q X J Y : ℕ) : ℂ :=
  ∑ h ∈ (V.frequencies Q).erase 0,
    V.coefficient Q h *
      ehmMSTTMainLowProductRowsMRange h X J Y 1 (2 * X)

/-- Below the outer scale all complete low-product modes are exactly
main-only; every near-divisor row belongs to the high-product gate. -/
theorem ehmDyadicVaalerPairedLowProductModes_eq_main_of_cutoff_le
    (V : VaalerSawtoothPackage) (Q X D J Y : ℕ) (hY : Y ≤ X) :
    ehmDyadicVaalerPairedLowProductModes V Q X D J Y =
      ehmMSTTMainLowProductModes V Q X J Y := by
  classical
  unfold ehmDyadicVaalerPairedLowProductModes
    ehmMSTTMainLowProductModes
  apply Finset.sum_congr rfl
  intro h _
  rw [ehmDyadicVaalerPairedLowProductRowsMRange_eq_main_of_cutoff_le
    h X D J Y 1 (2 * X) hY]

/-! ## The correction-coupled low-product residual -/

/-- The low-product modes retained in the same signed expression as the
smooth, linear, and endpoint corrections.  This, rather than the norm of
the low-product modes alone, is the corrected MSTT target. -/
noncomputable def ehmMSTTCenteredLowProductResidual
    (V : VaalerSawtoothPackage) (Q X J U Y : ℕ) : ℂ :=
  (ehmDyadicVaalerRetainedCorrection X J U : ℂ) -
    ehmDyadicVaalerPairedLowProductModes V Q X
      (ehmExplicitFarCutoff X) J Y

/-- Exact low/high decomposition of the already identified signed
nonzero-character residual. -/
theorem ehmDyadicVaalerCenteredNonzeroCharacterResidual_eq_centeredLow_sub_high
    (V : VaalerSawtoothPackage)
    (Q X J U Y : ℕ) (hX : 1 ≤ X) (hU : U ≤ 2 * X) :
    ehmDyadicVaalerCenteredNonzeroCharacterResidual V Q X J U =
      ehmMSTTCenteredLowProductResidual V Q X J U Y -
        ehmDyadicVaalerPairedHighProductModes V Q X
          (ehmExplicitFarCutoff X) J Y := by
  unfold ehmDyadicVaalerCenteredNonzeroCharacterResidual
    ehmMSTTCenteredLowProductResidual
  rw [ehmDyadicVaalerKernelNormalNonzeroModes_eq_paired
      V Q X (ehmExplicitFarCutoff X) J U hX hU,
    ehmDyadicVaalerPairedNonzeroModes_eq_low_add_high]
  ring

/-- Gate 5 is exactly the centered low-product residual, minus the signed
high-product modes and the Vaaler error. -/
theorem ehmDyadicVaalerGate5CoupledCore_eq_centeredLow_sub_high_sub_error
    (V : VaalerSawtoothPackage) (Q X J U Y : ℕ) :
    ehmDyadicVaalerGate5CoupledCore V Q X J U =
      ehmMSTTCenteredLowProductResidual V Q X J U Y -
        ehmDyadicVaalerPairedHighProductModes V Q X
          (ehmExplicitFarCutoff X) J Y -
        ehmDyadicVaalerKernelNormalError V Q X
          (ehmExplicitFarCutoff X) J U := by
  unfold ehmDyadicVaalerGate5CoupledCore
    ehmMSTTCenteredLowProductResidual
    ehmDyadicVaalerRetainedCorrection
  rw [ehmDyadicVaalerPairedNonzeroModes_eq_low_add_high]
  push_cast
  ring

/-! ## Recursive support without decoupling -/

/-- The centered low-product residual after the first exact halving of the
lower prefix.  Each MSTT block remains inside the signed expression with
the retained correction. -/
noncomputable def ehmMSTTFirstRecursiveCenteredLowProductResidual
    (V : VaalerSawtoothPackage) (Q X J U Y : ℕ) : ℂ :=
  (ehmDyadicVaalerRetainedCorrection X J U : ℂ) -
    ehmDyadicVaalerPairedLowProductPrefixTo V Q X
      (ehmExplicitFarCutoff X) J Y (X / 2) -
    ehmMSTTWeightedLowProductModesBlock V Q X
      (ehmExplicitFarCutoff X) J Y (X / 2) (X / 2) -
    ehmDyadicVaalerPairedLowProductHalvingEndpoint V Q X
      (ehmExplicitFarCutoff X) J Y X -
    ehmMSTTWeightedLowProductModesBlock V Q X
      (ehmExplicitFarCutoff X) J Y X X

/-- The recursive support expansion changes no cancellation target. -/
theorem ehmMSTTCenteredLowProductResidual_eq_firstRecursive
    (V : VaalerSawtoothPackage) (Q X J U Y : ℕ) :
    ehmMSTTCenteredLowProductResidual V Q X J U Y =
      ehmMSTTFirstRecursiveCenteredLowProductResidual V Q X J U Y := by
  unfold ehmMSTTCenteredLowProductResidual
    ehmMSTTFirstRecursiveCenteredLowProductResidual
  rw [ehmDyadicVaalerPairedLowProductModes_eq_prefix_add_upper,
    ehmDyadicVaalerPairedLowProductPrefix_eq_prefixTo,
    ehmDyadicVaalerPairedLowProductPrefixTo_eq_halved]
  ring

/-! ## The corrected three-part analytic interface -/

/-- The best currently justified MSTT architecture.

The product cutoff is required to lie below the original outer scale.  In
that range the near/divisor component of every low-product row vanishes
exactly, so MSTT is applied only to the polynomializable main rows.  The
bound required here is nevertheless the *centered* low residual: taking
absolute values of the low rows before coupling them back to the retained
correction loses the only available normalization.

The low, high, and Vaaler-error estimates must hold on the same cofinal set
of the secondary cutoff `J`. -/
structure EhmMSTTCenteredLowHighAnalyticGate where
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
      |(ehmMSTTCenteredLowProductResidual V
        (degree X J) X J (U X) (productCutoff X J)).re| ≤
          ((ehmDyadicNBlock X).card : ℝ) * etaLow X ∧
      |(ehmDyadicVaalerPairedHighProductModes V (degree X J) X
        (ehmExplicitFarCutoff X) J (productCutoff X J)).re| ≤
          ((ehmDyadicNBlock X).card : ℝ) * etaHigh X ∧
      |(ehmDyadicVaalerKernelNormalError V (degree X J) X
        (ehmExplicitFarCutoff X) J (U X)).re| ≤
          ((ehmDyadicNBlock X).card : ℝ) * etaError X

/-- The centered low/high interface implies the previous exact
nonzero-character gate. -/
noncomputable def EhmMSTTCenteredLowHighAnalyticGate.toNonzeroCharacter
    (H : EhmMSTTCenteredLowHighAnalyticGate) :
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
    rw [
      ehmDyadicVaalerCenteredNonzeroCharacterResidual_eq_centeredLow_sub_high
        H.V (H.degree X J) X J (H.U X) (H.productCutoff X J)
        (by omega) (H.U_le X)]
    calc
      |(ehmMSTTCenteredLowProductResidual H.V
          (H.degree X J) X J (H.U X) (H.productCutoff X J) -
        ehmDyadicVaalerPairedHighProductModes H.V (H.degree X J) X
          (ehmExplicitFarCutoff X) J (H.productCutoff X J)).re| ≤
          |(ehmMSTTCenteredLowProductResidual H.V
            (H.degree X J) X J (H.U X) (H.productCutoff X J)).re| +
          |(ehmDyadicVaalerPairedHighProductModes H.V (H.degree X J) X
            (ehmExplicitFarCutoff X) J (H.productCutoff X J)).re| := by
              simpa only [Complex.sub_re] using
                (abs_sub
                  (ehmMSTTCenteredLowProductResidual H.V
                    (H.degree X J) X J (H.U X)
                    (H.productCutoff X J)).re
                  (ehmDyadicVaalerPairedHighProductModes H.V
                    (H.degree X J) X (ehmExplicitFarCutoff X) J
                    (H.productCutoff X J)).re)
      _ ≤ ((ehmDyadicNBlock X).card : ℝ) * H.etaLow X +
          ((ehmDyadicNBlock X).card : ℝ) * H.etaHigh X :=
        add_le_add hbounds.2.1 hbounds.2.2.1
      _ = ((ehmDyadicNBlock X).card : ℝ) *
          (H.etaLow X + H.etaHigh X) := by ring

/-- Conditional H15 closure from the corrected MSTT decomposition.
Constructing the three cofinal estimates remains the analytic research
problem. -/
theorem baezDuarteCriterion_of_ehmMSTTCenteredLowHighAnalyticGate
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (H : EhmMSTTCenteredLowHighAnalyticGate) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmDyadicVaalerNonzeroCharacterAnalyticGate
    HS H.toNonzeroCharacter

end RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTCenteredGate
