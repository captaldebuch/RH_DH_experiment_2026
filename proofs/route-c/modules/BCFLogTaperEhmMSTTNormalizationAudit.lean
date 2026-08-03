import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmGate5CoupledReconstruction
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmMSTTOptimization

/-!
# Normalization and support audit for the Ehm--MSTT route

The exact H15 target contains one normalization: division by the cardinality
of the outer dyadic cutoff block.  This module records that fact and splits
the complete Gate-5 nonzero modes at the product cutoff and at the outer
Möbius coordinate `m = X`.

The resulting identity exposes two facts which an MSTT closure must respect.

* the dyadic mean supplies exactly the factor `1 / (X + 1)`;
* a short-window argument on `(X,2X]` controls only the upper part of the
  low-product modes.  The prefix `1 <= m <= X`, the high-product modes, the
  retained correction, and the Vaaler error remain in the signed core.

Everything below is a finite identity.  No cancellation estimate is asserted.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTNormalizationAudit

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCoupledNearCoreTarget
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmExplicitFarCutoff
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFullVaalerLift
open RH.Criteria.NymanBeurling.BCFLogTaperEhmGate5CoupledReconstruction
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTLowRows
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTOptimization
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTWindowCover
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPairedAdditiveRows
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPairedResonance
open RH.Criteria.NymanBeurling.BCFLogTaperEhmProductTruncation
open RH.Criteria.NymanBeurling.BCFLogTaperEhmVaalerAnalyticGate
open RH.Criteria.NymanBeurling.QuadraticInteraction

/-! ## The unique dyadic normalization -/

/-- The inclusive cutoff block `[X,2X]` has exactly `X+1` elements. -/
theorem card_ehmDyadicNBlock (X : ℕ) :
    (ehmDyadicNBlock X).card = X + 1 := by
  simp only [ehmDyadicNBlock, Nat.card_Icc]
  omega

/-- Gate 5 divided by the outer-cutoff cardinality. -/
noncomputable def ehmDyadicNormalizedGate5CoupledCore
    (V : VaalerSawtoothPackage) (H X J U : ℕ) : ℝ :=
  (ehmDyadicVaalerGate5CoupledCore V H X J U).re /
    ((ehmDyadicNBlock X).card : ℝ)

/-- Exact reconstruction survives the sole dyadic normalization. -/
theorem ehmDyadicNormalizedGate5CoupledCore_eq_explicitMean
    (V : VaalerSawtoothPackage)
    (hV : VaalerSawtoothHasZeroCoefficient V)
    (H X J U : ℕ) (hX : 1 ≤ X) (hU : U ≤ 2 * X) :
    ehmDyadicNormalizedGate5CoupledCore V H X J U =
      ehmDyadicExplicitCoupledNearCore ehmR1 X
          (ehmExplicitFarCutoff X) J /
        ((ehmDyadicNBlock X).card : ℝ) := by
  have hcore := congrArg Complex.re
    (ehmDyadicExplicitCutoffCoupledNearCore_eq_gate5CoupledCore
      V hV H X J U hX hU)
  unfold ehmDyadicNormalizedGate5CoupledCore
  simpa using congrArg
    (fun z : ℝ => z / ((ehmDyadicNBlock X).card : ℝ)) hcore.symm

/-- A normalized Gate-5 bound is exactly the cardinality-scaled H15 bound;
there is no second factor of `X` hidden in the reconstruction. -/
theorem ehmDyadicNormalizedGate5CoupledCore_le_iff
    (V : VaalerSawtoothPackage) (H X J U : ℕ) (eta : ℝ) :
    ehmDyadicNormalizedGate5CoupledCore V H X J U ≤ eta ↔
      (ehmDyadicVaalerGate5CoupledCore V H X J U).re ≤
        ((ehmDyadicNBlock X).card : ℝ) * eta := by
  have hcard : (0 : ℝ) < ((ehmDyadicNBlock X).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (ehmDyadicNBlock_nonempty X)
  unfold ehmDyadicNormalizedGate5CoupledCore
  simpa [mul_comm] using (div_le_iff₀ hcard)

/-! ## Product truncation lifted through all Vaaler frequencies -/

/-- All retained low-product modes on the complete support `1 <= m <= 2X`. -/
noncomputable def ehmDyadicVaalerPairedLowProductModes
    (V : VaalerSawtoothPackage) (Q X D J Y : ℕ) : ℂ :=
  ∑ h ∈ (V.frequencies Q).erase 0,
    V.coefficient Q h *
      ehmDyadicVaalerPairedLowProductRowsMRange h X D J Y 1 (2 * X)

/-- The complementary high-product modes on the same complete support. -/
noncomputable def ehmDyadicVaalerPairedHighProductModes
    (V : VaalerSawtoothPackage) (Q X D J Y : ℕ) : ℂ :=
  ∑ h ∈ (V.frequencies Q).erase 0,
    V.coefficient Q h *
      ehmDyadicVaalerPairedHighProductRowsMRange h X D J Y 1 (2 * X)

/-- Exact low/high product split of every nonzero Vaaler mode. -/
theorem ehmDyadicVaalerPairedNonzeroModes_eq_low_add_high
    (V : VaalerSawtoothPackage) (Q X D J Y : ℕ) :
    ehmDyadicVaalerPairedNonzeroModes V Q X D J =
      ehmDyadicVaalerPairedLowProductModes V Q X D J Y +
        ehmDyadicVaalerPairedHighProductModes V Q X D J Y := by
  classical
  unfold ehmDyadicVaalerPairedNonzeroModes
    ehmDyadicVaalerPairedFrequencyRange
    ehmDyadicVaalerPairedLowProductModes
    ehmDyadicVaalerPairedHighProductModes
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _
  rw [← mul_add,
    ehmDyadicVaalerPairedAdditiveRowsMRange_eq_low_add_high]

/-! ## The part actually reached by upper-dyadic MSTT windows -/

/-- The low-product prefix which is not contained in the MSTT block
`(X,2X]`. -/
noncomputable def ehmDyadicVaalerPairedLowProductPrefix
    (V : VaalerSawtoothPackage) (Q X D J Y : ℕ) : ℂ :=
  ∑ h ∈ (V.frequencies Q).erase 0,
    V.coefficient Q h *
      ehmDyadicVaalerPairedLowProductRowsMRange h X D J Y 1 X

/-- One complete low-product row is its prefix plus its upper dyadic block. -/
theorem ehmDyadicVaalerPairedLowProductRowsMRange_eq_prefix_add_upper
    (h : ℤ) (X D J Y : ℕ) :
    ehmDyadicVaalerPairedLowProductRowsMRange h X D J Y 1 (2 * X) =
      ehmDyadicVaalerPairedLowProductRowsMRange h X D J Y 1 X +
        ehmMSTTLowProductRowsBlock h X D J Y X X := by
  simpa [ehmDyadicVaalerPairedLowProductRowsMRange,
    ehmMSTTLowProductRowsBlock, ehmMSTTDyadicMBlock, two_mul] using
      (sum_Icc_one_two_mul_eq_low_add_dyadic
        (fun m : ℕ =>
          ((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
            ehmDyadicVaalerPairedLowProductRow h X D J Y m)) X)

/-- Consequently, the weighted MSTT block with base and length `X` is only
the upper half of the complete low-product frequency sum. -/
theorem ehmDyadicVaalerPairedLowProductModes_eq_prefix_add_upper
    (V : VaalerSawtoothPackage) (Q X D J Y : ℕ) :
    ehmDyadicVaalerPairedLowProductModes V Q X D J Y =
      ehmDyadicVaalerPairedLowProductPrefix V Q X D J Y +
        ehmMSTTWeightedLowProductModesBlock V Q X D J Y X X := by
  classical
  unfold ehmDyadicVaalerPairedLowProductModes
    ehmDyadicVaalerPairedLowProductPrefix
    ehmMSTTWeightedLowProductModesBlock
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _
  rw [← mul_add,
    ← ehmDyadicVaalerPairedLowProductRowsMRange_eq_prefix_add_upper]

/-! ## Exact clipped-window reconstruction of the upper block -/

/-- One low-product row restricted to a clipped MSTT window. -/
noncomputable def ehmMSTTLowProductRowsClippedWindow
    (h : ℤ) (N D J Y X H r : ℕ) : ℂ :=
  ∑ m ∈ ehmMSTTClippedWindow X H r,
    ((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
      ehmDyadicVaalerPairedLowProductRow h N D J Y m)

/-- The upper dyadic row is exactly the sum over clipped windows of any
positive common length.  No padded overshoot occurs in this identity. -/
theorem ehmMSTTLowProductRowsUpper_eq_sum_clippedWindows
    (h : ℤ) (N D J Y X H : ℕ) (hH : 1 ≤ H) :
    ehmMSTTLowProductRowsBlock h N D J Y X X =
      ∑ r ∈ Finset.range (ehmMSTTWindowCount X H),
        ehmMSTTLowProductRowsClippedWindow h N D J Y X H r := by
  simpa [ehmMSTTLowProductRowsBlock,
    ehmMSTTLowProductRowsClippedWindow, ehmMSTTDyadicMBlock, two_mul] using
      (sum_ehmMSTTDyadicMBlock_eq_sum_clippedWindows
        (fun m : ℕ =>
          ((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
            ehmDyadicVaalerPairedLowProductRow h N D J Y m)) X H hH)

/-- All Vaaler frequencies on one clipped window. -/
noncomputable def ehmMSTTWeightedLowProductModesClippedWindow
    (V : VaalerSawtoothPackage)
    (Q N D J Y X H r : ℕ) : ℂ :=
  ∑ h ∈ (V.frequencies Q).erase 0,
    V.coefficient Q h *
      ehmMSTTLowProductRowsClippedWindow h N D J Y X H r

/-- The exact upper low-product mode sum is reconstructed by clipped
windows.  This is the finite Gate-3 support identity to which an analytic
short-window estimate must be applied. -/
theorem ehmMSTTWeightedLowProductModesUpper_eq_sum_clippedWindows
    (V : VaalerSawtoothPackage)
    (Q N D J Y X H : ℕ) (hH : 1 ≤ H) :
    ehmMSTTWeightedLowProductModesBlock V Q N D J Y X X =
      ∑ r ∈ Finset.range (ehmMSTTWindowCount X H),
        ehmMSTTWeightedLowProductModesClippedWindow
          V Q N D J Y X H r := by
  classical
  unfold ehmMSTTWeightedLowProductModesBlock
    ehmMSTTWeightedLowProductModesClippedWindow
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  rw [← Finset.mul_sum,
    ← ehmMSTTLowProductRowsUpper_eq_sum_clippedWindows
      h N D J Y X H hH]

/-! ## The fully audited Gate-5 support -/

/-- Gate 5 with the low-product frequency sum replaced by its exact lower
prefix and upper MSTT block.  All other signed constituents remain present. -/
noncomputable def ehmDyadicVaalerGate5MSTTSupportAuditCore
    (V : VaalerSawtoothPackage) (Q X J U Y : ℕ) : ℂ :=
  (ehmDyadicVaalerRetainedCorrection X J U : ℂ) -
    ehmDyadicVaalerPairedLowProductPrefix V Q X
      (ehmExplicitFarCutoff X) J Y -
    ehmMSTTWeightedLowProductModesBlock V Q X
      (ehmExplicitFarCutoff X) J Y X X -
    ehmDyadicVaalerPairedHighProductModes V Q X
      (ehmExplicitFarCutoff X) J Y -
    ehmDyadicVaalerKernelNormalError V Q X
      (ehmExplicitFarCutoff X) J U

/-- Exact support audit of the five-term Gate-5 core.  The upper-dyadic MSTT
term has no independent normalization or cancellation built into this
identity. -/
theorem ehmDyadicVaalerGate5CoupledCore_eq_msttSupportAuditCore
    (V : VaalerSawtoothPackage) (Q X J U Y : ℕ) :
    ehmDyadicVaalerGate5CoupledCore V Q X J U =
      ehmDyadicVaalerGate5MSTTSupportAuditCore V Q X J U Y := by
  unfold ehmDyadicVaalerGate5CoupledCore
    ehmDyadicVaalerGate5MSTTSupportAuditCore
    ehmDyadicVaalerRetainedCorrection
  rw [ehmDyadicVaalerPairedNonzeroModes_eq_low_add_high,
    ehmDyadicVaalerPairedLowProductModes_eq_prefix_add_upper]
  push_cast
  ring

end RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTNormalizationAudit
