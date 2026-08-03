import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmMSTTNormalizationAudit

/-!
# MSTT bounds on the exact clipped dyadic windows

This module applies the polynomial-phase estimate with the hard dyadic
endpoint inserted into the Abel weight.  The generic variation lemma proves
that this cutoff does not increase endpoint-plus-total variation.  Taylor
error is likewise dominated by the corresponding full-window majorant.

Consequently the combined padded objective already bounds the exact sum over
clipped windows, even though the padded full-window sum itself is not the
Gate-5 support.  This closes the finite/analytic clipping part of Gate 3.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTClippedOptimization

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFourierResonanceAudit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTLowRows
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTNormalizationAudit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTOptimization
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTTaylorAccumulation
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTVariation
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTWindowCover
open RH.Criteria.NymanBeurling.BCFLogTaperEhmReciprocalTaylor
open RH.Criteria.NymanBeurling.BCFLogTaperEhmProductTruncation
open RH.Criteria.NymanBeurling.BCFLogTaperMSTTPolynomialPhase
open RH.Criteria.NymanBeurling.QuadraticInteraction

/-! ## Clipped fixed-product columns -/

/-- The complete paired product weight with a hard upper endpoint. -/
noncomputable def ehmMSTTClippedLowProductWeight
    (T N D n m : ℕ) : ℂ :=
  complexUpperCutoffWeight T (ehmMSTTLowProductWeight N D n) m

/-- One exact reciprocal column with the hard endpoint in its weight. -/
noncomputable def ehmMSTTClippedLowProductColumn
    (h : ℤ) (T N D n X H : ℕ) : ℂ :=
  ∑ m ∈ Finset.Ioc X (X + H),
    (((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
      ehmVaalerRationalPhase h n 1 m) *
        ehmMSTTClippedLowProductWeight T N D n m)

noncomputable def ehmMSTTClippedLowProductPolynomialColumn
    (h : ℤ) (T N D n X H K : ℕ) : ℂ :=
  ∑ m ∈ Finset.Ioc X (X + H),
    (((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
      msttPolynomialPhase
        (reciprocalTaylorPolynomial
          ((h : ℝ) * (n : ℝ)) (X : ℝ) K) m) *
        ehmMSTTClippedLowProductWeight T N D n m)

noncomputable def ehmMSTTClippedLowProductTaylorErrorColumn
    (h : ℤ) (T N D n X H K : ℕ) : ℂ :=
  ∑ m ∈ Finset.Ioc X (X + H),
    (((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
      ehmMSTTClippedLowProductWeight T N D n m) *
        (ehmVaalerRationalPhase h n 1 m -
          msttPolynomialPhase
            (reciprocalTaylorPolynomial
              ((h : ℝ) * (n : ℝ)) (X : ℝ) K) m))

theorem ehmMSTTClippedLowProductColumn_eq_polynomial_add_error
    (h : ℤ) (T N D n X H K : ℕ) :
    ehmMSTTClippedLowProductColumn h T N D n X H =
      ehmMSTTClippedLowProductPolynomialColumn h T N D n X H K +
        ehmMSTTClippedLowProductTaylorErrorColumn h T N D n X H K := by
  classical
  unfold ehmMSTTClippedLowProductColumn
    ehmMSTTClippedLowProductPolynomialColumn
    ehmMSTTClippedLowProductTaylorErrorColumn
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  ring

/-! ## No extra clipping loss -/

theorem norm_ehmMSTTClippedLowProductPolynomialColumn_le
    (HM : MSTTMobiusPolynomialPhaseEstimate)
    (h : ℤ) (T N D n : ℕ)
    (logSaving K : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (X H : ℕ)
    (hthreshold : HM.threshold K logSaving epsilon ≤ X)
    (hX : 3 ≤ X) (hH : 1 ≤ H)
    (hHlower :
      Real.rpow (X : ℝ) ((5 / 8 : ℝ) + epsilon) ≤ (H : ℝ))
    (hHupper :
      (H : ℝ) ≤ Real.rpow (X : ℝ) (1 - epsilon)) :
    ‖ehmMSTTClippedLowProductPolynomialColumn
        h T N D n X H K‖ ≤
      ehmMSTTLogSavingPrefactor HM K logSaving X H epsilon *
        complexWeightVariation
          (ehmMSTTLowProductWeight N D n) (X + 1) (X + H) := by
  have hbase := norm_weighted_msttMobiusPolynomialBlock_le
    HM K logSaving epsilon hepsilon X H hthreshold hX hH
      hHlower hHupper
      (reciprocalTaylorPolynomial
        ((h : ℝ) * (n : ℝ)) (X : ℝ) K)
      (reciprocalTaylorPolynomial_natDegree_le _ _ _)
      (ehmMSTTClippedLowProductWeight T N D n)
  unfold ehmMSTTClippedLowProductPolynomialColumn at hbase ⊢
  change _ ≤ ehmMSTTLogSavingPrefactor HM K logSaving X H epsilon * _
  refine hbase.trans ?_
  unfold ehmMSTTLogSavingPrefactor
  apply mul_le_mul_of_nonneg_left
  · exact complexWeightVariation_upperCutoff_le T
      (ehmMSTTLowProductWeight N D n) (X + 1) (X + H) (by omega)
  · exact div_nonneg
      (mul_nonneg (HM.constant_nonneg K logSaving epsilon)
        (Nat.cast_nonneg H))
      (pow_nonneg (Real.log_natCast_nonneg X) _)

theorem norm_ehmMSTTClippedLowProductTaylorErrorColumn_le
    (h : ℤ) (T N D n X H K : ℕ) (hX : 1 ≤ X) :
    ‖ehmMSTTClippedLowProductTaylorErrorColumn
        h T N D n X H K‖ ≤
      ehmMSTTLowProductTaylorErrorMajorant h N D n X H K := by
  classical
  unfold ehmMSTTClippedLowProductTaylorErrorColumn
    ehmMSTTLowProductTaylorErrorMajorant
  calc
    ‖∑ m ∈ Finset.Ioc X (X + H),
        (((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
          ehmMSTTClippedLowProductWeight T N D n m) *
            (ehmVaalerRationalPhase h n 1 m -
              msttPolynomialPhase
                (reciprocalTaylorPolynomial
                  ((h : ℝ) * (n : ℝ)) (X : ℝ) K) m))‖ ≤
      ∑ m ∈ Finset.Ioc X (X + H),
        ‖(((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
          ehmMSTTClippedLowProductWeight T N D n m) *
            (ehmVaalerRationalPhase h n 1 m -
              msttPolynomialPhase
                (reciprocalTaylorPolynomial
                  ((h : ℝ) * (n : ℝ)) (X : ℝ) K) m))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.Ioc X (X + H),
        ‖(((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
          ehmMSTTLowProductWeight N D n m))‖ *
            (2 * Real.pi *
              |reciprocalTaylorRemainder
                ((h : ℝ) * (n : ℝ)) (X : ℝ) K
                  ((m : ℝ) - (X : ℝ))|) := by
      apply Finset.sum_le_sum
      intro m hm
      have hmpos : 0 < m := by
        have hXm := (Finset.mem_Ioc.mp hm).1
        omega
      have hphase :=
        norm_ehmVaalerRationalPhase_sub_reciprocalTaylor_le
          h n m K (X : ℝ)
            (by exact_mod_cast (show X ≠ 0 by omega)) hmpos.ne'
      have hweight :
          ‖(((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
            ehmMSTTClippedLowProductWeight T N D n m))‖ ≤
            ‖(((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
              ehmMSTTLowProductWeight N D n m))‖ := by
        by_cases hmT : m ≤ T
        · simp [ehmMSTTClippedLowProductWeight,
            complexUpperCutoffWeight, hmT]
        · simp [ehmMSTTClippedLowProductWeight,
            complexUpperCutoffWeight, hmT]
          positivity
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left hphase (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_right hweight (by positivity))

theorem norm_ehmMSTTClippedLowProductColumn_le
    (HM : MSTTMobiusPolynomialPhaseEstimate)
    (h : ℤ) (T N D n : ℕ)
    (logSaving K : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (X H : ℕ)
    (hthreshold : HM.threshold K logSaving epsilon ≤ X)
    (hX : 3 ≤ X) (hH : 1 ≤ H)
    (hHlower :
      Real.rpow (X : ℝ) ((5 / 8 : ℝ) + epsilon) ≤ (H : ℝ))
    (hHupper :
      (H : ℝ) ≤ Real.rpow (X : ℝ) (1 - epsilon)) :
    ‖ehmMSTTClippedLowProductColumn h T N D n X H‖ ≤
      ehmMSTTLogSavingPrefactor HM K logSaving X H epsilon *
          complexWeightVariation
            (ehmMSTTLowProductWeight N D n) (X + 1) (X + H) +
        ehmMSTTLowProductTaylorErrorMajorant h N D n X H K := by
  rw [ehmMSTTClippedLowProductColumn_eq_polynomial_add_error]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_ehmMSTTClippedLowProductPolynomialColumn_le
      HM h T N D n logSaving K epsilon hepsilon X H
        hthreshold hX hH hHlower hHupper)
    (norm_ehmMSTTClippedLowProductTaylorErrorColumn_le
      h T N D n X H K (by omega)))

/-! ## Product and frequency reconstruction -/

noncomputable def ehmMSTTClippedLowProductRowsBlock
    (h : ℤ) (T N D J Y X H : ℕ) : ℂ :=
  ∑ n ∈ ehmDyadicVaalerLowProductRange J Y,
    ehmMSTTClippedLowProductColumn h T N D n X H

theorem norm_ehmMSTTClippedLowProductRowsBlock_le_combinedFrequencyCost
    (HM : MSTTMobiusPolynomialPhaseEstimate)
    (h : ℤ) (T N D J Y : ℕ)
    (logSaving K : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (X H : ℕ)
    (hthreshold : HM.threshold K logSaving epsilon ≤ X)
    (hN : 2 ≤ N) (hX : 3 ≤ X) (hH : 1 ≤ H)
    (hHlower :
      Real.rpow (X : ℝ) ((5 / 8 : ℝ) + epsilon) ≤ (H : ℝ))
    (hHupper :
      (H : ℝ) ≤ Real.rpow (X : ℝ) (1 - epsilon)) :
    ‖ehmMSTTClippedLowProductRowsBlock h T N D J Y X H‖ ≤
      ehmMSTTCombinedFrequencyCost
        HM h N D J Y X H K logSaving epsilon := by
  unfold ehmMSTTClippedLowProductRowsBlock
    ehmMSTTCombinedFrequencyCost ehmMSTTCombinedProductCost
  calc
    ‖∑ n ∈ ehmDyadicVaalerLowProductRange J Y,
        ehmMSTTClippedLowProductColumn h T N D n X H‖ ≤
      ∑ n ∈ ehmDyadicVaalerLowProductRange J Y,
        ‖ehmMSTTClippedLowProductColumn h T N D n X H‖ :=
          norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro n _
      refine (norm_ehmMSTTClippedLowProductColumn_le
        HM h T N D n logSaving K epsilon hepsilon X H
          hthreshold hX hH hHlower hHupper).trans ?_
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (complexWeightVariation_ehmMSTTLowProductWeight_le_endpointMajorant
            N D n (X + 1) (X + H) hN (by omega) (by omega))
          (ehmMSTTLogSavingPrefactor_nonneg
            HM K logSaving X H epsilon)
      · exact ehmMSTTLowProductTaylorErrorMajorant_le_blockFactor
          h N D n X H K (by omega)

noncomputable def ehmMSTTWeightedClippedLowProductModesBlock
    (V : VaalerSawtoothPackage)
    (Q T N D J Y X H : ℕ) : ℂ :=
  ∑ h ∈ (V.frequencies Q).erase 0,
    V.coefficient Q h *
      ehmMSTTClippedLowProductRowsBlock h T N D J Y X H

theorem norm_ehmMSTTWeightedClippedLowProductModesBlock_le_objective
    (V : VaalerSawtoothPackage)
    (HM : MSTTMobiusPolynomialPhaseEstimate)
    (Q T N D J Y : ℕ)
    (logSaving K : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (X H : ℕ)
    (hthreshold : HM.threshold K logSaving epsilon ≤ X)
    (hN : 2 ≤ N) (hX : 3 ≤ X) (hH : 1 ≤ H)
    (hHlower :
      Real.rpow (X : ℝ) ((5 / 8 : ℝ) + epsilon) ≤ (H : ℝ))
    (hHupper :
      (H : ℝ) ≤ Real.rpow (X : ℝ) (1 - epsilon)) :
    ‖ehmMSTTWeightedClippedLowProductModesBlock
        V Q T N D J Y X H‖ ≤
      ehmMSTTCombinedLowModeObjective
        V HM Q N D J Y X H K logSaving epsilon := by
  classical
  unfold ehmMSTTWeightedClippedLowProductModesBlock
    ehmMSTTCombinedLowModeObjective
  calc
    ‖∑ h ∈ (V.frequencies Q).erase 0,
        V.coefficient Q h *
          ehmMSTTClippedLowProductRowsBlock h T N D J Y X H‖ ≤
      ∑ h ∈ (V.frequencies Q).erase 0,
        ‖V.coefficient Q h *
          ehmMSTTClippedLowProductRowsBlock h T N D J Y X H‖ :=
            norm_sum_le _ _
    _ = ∑ h ∈ (V.frequencies Q).erase 0,
        ‖V.coefficient Q h‖ *
          ‖ehmMSTTClippedLowProductRowsBlock h T N D J Y X H‖ := by
      apply Finset.sum_congr rfl
      intro h _
      rw [norm_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro h _
      exact mul_le_mul_of_nonneg_left
        (norm_ehmMSTTClippedLowProductRowsBlock_le_combinedFrequencyCost
          HM h T N D J Y logSaving K epsilon hepsilon X H
            hthreshold hN hX hH hHlower hHupper)
        (norm_nonneg _)

/-! ## Identification with the exact clipped cover -/

theorem ehmMSTTClippedLowProductRowsBlock_eq_clippedWindow
    (h : ℤ) (N D J Y X H r : ℕ) :
    ehmMSTTClippedLowProductRowsBlock h (2 * X) N D J Y
        (ehmMSTTWindowStart X H r) H =
      ehmMSTTLowProductRowsClippedWindow h N D J Y X H r := by
  classical
  unfold ehmMSTTClippedLowProductRowsBlock
    ehmMSTTClippedLowProductColumn
    ehmMSTTLowProductRowsClippedWindow
    ehmMSTTClippedWindow ehmMSTTWindow
    ehmMSTTClippedLowProductWeight complexUpperCutoffWeight
    ehmDyadicVaalerPairedLowProductRow
    ehmDyadicVaalerPairedProductSummand ehmMSTTLowProductWeight
  rw [Finset.sum_comm]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _
  split_ifs with hm
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  · simp

theorem ehmMSTTWeightedClippedLowProductModesBlock_eq_clippedWindow
    (V : VaalerSawtoothPackage)
    (Q N D J Y X H r : ℕ) :
    ehmMSTTWeightedClippedLowProductModesBlock V Q (2 * X) N D J Y
        (ehmMSTTWindowStart X H r) H =
      ehmMSTTWeightedLowProductModesClippedWindow
        V Q N D J Y X H r := by
  classical
  unfold ehmMSTTWeightedClippedLowProductModesBlock
    ehmMSTTWeightedLowProductModesClippedWindow
  apply Finset.sum_congr rfl
  intro h _
  rw [ehmMSTTClippedLowProductRowsBlock_eq_clippedWindow]

/-- The combined padded objective controls the exact clipped upper-dyadic
low-mode sum.  Thus clipping introduces no additional Gate-3 majorant. -/
theorem norm_sum_ehmMSTTWeightedLowProductModesClippedWindow_div_card_le
    (V : VaalerSawtoothPackage)
    (HM : MSTTMobiusPolynomialPhaseEstimate)
    (p : EhmMSTTOptimizationParameters)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (X D J : ℕ)
    (hfeasible : p.Feasible HM epsilon X) :
    ‖∑ r ∈ Finset.range (ehmMSTTWindowCount X p.windowLength),
        ehmMSTTWeightedLowProductModesClippedWindow V p.vaalerCutoff
          X D J p.productCutoff X p.windowLength r‖ /
        ((ehmDyadicNBlock X).card : ℝ) ≤
      ehmMSTTNormalizedPaddedDyadicObjective V HM p epsilon X D J := by
  classical
  unfold ehmMSTTNormalizedPaddedDyadicObjective
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    ‖∑ r ∈ Finset.range (ehmMSTTWindowCount X p.windowLength),
        ehmMSTTWeightedLowProductModesClippedWindow V p.vaalerCutoff
          X D J p.productCutoff X p.windowLength r‖ ≤
      ∑ r ∈ Finset.range (ehmMSTTWindowCount X p.windowLength),
        ‖ehmMSTTWeightedLowProductModesClippedWindow V p.vaalerCutoff
          X D J p.productCutoff X p.windowLength r‖ := norm_sum_le _ _
    _ ≤ ∑ r ∈ Finset.range (ehmMSTTWindowCount X p.windowLength),
        ehmMSTTCombinedLowModeObjective V HM p.vaalerCutoff X D J
          p.productCutoff (ehmMSTTWindowStart X p.windowLength r)
          p.windowLength p.taylorDegree p.logSaving epsilon := by
      apply Finset.sum_le_sum
      intro r hr
      have hw := hfeasible.2 r hr
      rw [← ehmMSTTWeightedClippedLowProductModesBlock_eq_clippedWindow]
      exact norm_ehmMSTTWeightedClippedLowProductModesBlock_le_objective
        V HM p.vaalerCutoff (2 * X) X D J p.productCutoff
          p.logSaving p.taylorDegree epsilon hepsilon
          (ehmMSTTWindowStart X p.windowLength r) p.windowLength
          hw.threshold_le hfeasible.1 hw.base_ge_three hw.length_pos
          hw.length_lower hw.length_upper

/-- Equivalent exact-upper-block formulation of the clipped estimate. -/
theorem norm_ehmMSTTWeightedLowProductModesUpper_div_card_le_objective
    (V : VaalerSawtoothPackage)
    (HM : MSTTMobiusPolynomialPhaseEstimate)
    (p : EhmMSTTOptimizationParameters)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (X D J : ℕ)
    (hfeasible : p.Feasible HM epsilon X) :
    ‖ehmMSTTWeightedLowProductModesBlock V p.vaalerCutoff X D J
        p.productCutoff X X‖ /
        ((ehmDyadicNBlock X).card : ℝ) ≤
      ehmMSTTNormalizedPaddedDyadicObjective V HM p epsilon X D J := by
  have hcount : 0 < ehmMSTTWindowCount X p.windowLength := by
    simp [ehmMSTTWindowCount]
  have hr0 : 0 ∈ Finset.range (ehmMSTTWindowCount X p.windowLength) :=
    Finset.mem_range.mpr hcount
  rw [ehmMSTTWeightedLowProductModesUpper_eq_sum_clippedWindows
    V p.vaalerCutoff X D J p.productCutoff X p.windowLength
      (hfeasible.2 0 hr0).length_pos]
  exact norm_sum_ehmMSTTWeightedLowProductModesClippedWindow_div_card_le
    V HM p epsilon hepsilon X D J hfeasible

/-! ## Recursive blocks with distinct arithmetic and window scales -/

/-- The normalized objective for a dyadic `m`-block `(S,2S]` whose paired
Ehm coefficients still have the original outer scale `N`.  Separating `N`
from `S` is essential when the lower prefix is treated recursively. -/
noncomputable def ehmMSTTNormalizedClippedDyadicBlockObjective
    (V : VaalerSawtoothPackage)
    (HM : MSTTMobiusPolynomialPhaseEstimate)
    (p : EhmMSTTOptimizationParameters)
    (epsilon : ℝ) (N S D J : ℕ) : ℝ :=
  (∑ r ∈ Finset.range (ehmMSTTWindowCount S p.windowLength),
      ehmMSTTCombinedLowModeObjective V HM p.vaalerCutoff N D J
        p.productCutoff (ehmMSTTWindowStart S p.windowLength r)
        p.windowLength p.taylorDegree p.logSaving epsilon) /
    ((ehmDyadicNBlock N).card : ℝ)

/-- The generalized objective controls the exact clipped cover of
`(S,2S]`, while normalization remains at the original outer scale `N`. -/
theorem norm_sum_ehmMSTTRecursiveClippedWindows_div_card_le
    (V : VaalerSawtoothPackage)
    (HM : MSTTMobiusPolynomialPhaseEstimate)
    (p : EhmMSTTOptimizationParameters)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (N S D J : ℕ) (hN : 2 ≤ N)
    (hfeasible : p.Feasible HM epsilon S) :
    ‖∑ r ∈ Finset.range (ehmMSTTWindowCount S p.windowLength),
        ehmMSTTWeightedLowProductModesClippedWindow V p.vaalerCutoff
          N D J p.productCutoff S p.windowLength r‖ /
        ((ehmDyadicNBlock N).card : ℝ) ≤
      ehmMSTTNormalizedClippedDyadicBlockObjective
        V HM p epsilon N S D J := by
  classical
  unfold ehmMSTTNormalizedClippedDyadicBlockObjective
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    ‖∑ r ∈ Finset.range (ehmMSTTWindowCount S p.windowLength),
        ehmMSTTWeightedLowProductModesClippedWindow V p.vaalerCutoff
          N D J p.productCutoff S p.windowLength r‖ ≤
      ∑ r ∈ Finset.range (ehmMSTTWindowCount S p.windowLength),
        ‖ehmMSTTWeightedLowProductModesClippedWindow V p.vaalerCutoff
          N D J p.productCutoff S p.windowLength r‖ := norm_sum_le _ _
    _ ≤ ∑ r ∈ Finset.range (ehmMSTTWindowCount S p.windowLength),
        ehmMSTTCombinedLowModeObjective V HM p.vaalerCutoff N D J
          p.productCutoff (ehmMSTTWindowStart S p.windowLength r)
          p.windowLength p.taylorDegree p.logSaving epsilon := by
      apply Finset.sum_le_sum
      intro r hr
      have hw := hfeasible.2 r hr
      rw [← ehmMSTTWeightedClippedLowProductModesBlock_eq_clippedWindow]
      exact norm_ehmMSTTWeightedClippedLowProductModesBlock_le_objective
        V HM p.vaalerCutoff (2 * S) N D J p.productCutoff
          p.logSaving p.taylorDegree epsilon hepsilon
          (ehmMSTTWindowStart S p.windowLength r) p.windowLength
          hw.threshold_le hN hw.base_ge_three hw.length_pos
          hw.length_lower hw.length_upper

/-- Exact-upper-block form of the generalized recursive estimate. -/
theorem norm_ehmMSTTRecursiveLowProductBlock_div_card_le_objective
    (V : VaalerSawtoothPackage)
    (HM : MSTTMobiusPolynomialPhaseEstimate)
    (p : EhmMSTTOptimizationParameters)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (N S D J : ℕ) (hN : 2 ≤ N)
    (hfeasible : p.Feasible HM epsilon S) :
    ‖ehmMSTTWeightedLowProductModesBlock V p.vaalerCutoff N D J
        p.productCutoff S S‖ /
        ((ehmDyadicNBlock N).card : ℝ) ≤
      ehmMSTTNormalizedClippedDyadicBlockObjective
        V HM p epsilon N S D J := by
  have hcount : 0 < ehmMSTTWindowCount S p.windowLength := by
    simp [ehmMSTTWindowCount]
  have hr0 : 0 ∈ Finset.range (ehmMSTTWindowCount S p.windowLength) :=
    Finset.mem_range.mpr hcount
  rw [ehmMSTTWeightedLowProductModesUpper_eq_sum_clippedWindows
    V p.vaalerCutoff N D J p.productCutoff S p.windowLength
      (hfeasible.2 0 hr0).length_pos]
  exact norm_sum_ehmMSTTRecursiveClippedWindows_div_card_le
    V HM p epsilon hepsilon N S D J hN hfeasible

end RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTClippedOptimization
