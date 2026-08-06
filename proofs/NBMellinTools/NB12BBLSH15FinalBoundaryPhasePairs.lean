/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FinalBoundaryCoupledGate

/-!
# NB12zzb: endpoint-pair phase expansion

The literal distinct-modulus correlation is expanded to its original endpoint
positions.  A pointwise complex identity then splits the product of the two
real doubled-character modes into a difference-frequency real part minus a
sum-frequency real part.  All Möbius, taper, terminal, and smooth coefficients
remain inside the same finite pair sum.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate
open Complex

namespace NBMellinTools.NB12

/-! ## Pointwise doubled-character identity -/

noncomputable def h15DoubledDirectAdditivePhase
    (r u q : ℕ) : ℂ :=
  (h15DirectAdditiveReducedUnitPhase .positive r u q) ^ 2

theorem h15PairedDirectCrossMode_eq_doubledPhase_im
    (r u q : ℕ) :
    h15PairedDirectCrossMode r u q =
      (h15DoubledDirectAdditivePhase r u q).im := by
  rfl

theorem mul_im_eq_half_re_mul_conj_sub_re_mul
    (z w : ℂ) :
    z.im * w.im = ((z * conj w).re - (z * w).re) / 2 := by
  simp only [mul_re, conj_re, conj_im]
  ring

/-- Product-to-sum identity for the exact real H15 cross modes. -/
theorem h15PairedDirectCrossMode_mul_eq_difference_sub_sum
    (r u q v q' : ℕ) :
    h15PairedDirectCrossMode r u q * h15PairedDirectCrossMode r v q' =
      (((h15DoubledDirectAdditivePhase r u q *
          conj (h15DoubledDirectAdditivePhase r v q')).re -
        (h15DoubledDirectAdditivePhase r u q *
          h15DoubledDirectAdditivePhase r v q').re) / 2) := by
  rw [h15PairedDirectCrossMode_eq_doubledPhase_im,
    h15PairedDirectCrossMode_eq_doubledPhase_im,
    mul_im_eq_half_re_mul_conj_sub_re_mul]

/-! ## Literal endpoint-pair correlation -/

theorem h15NormalizedBoundaryFixedFrequencyModulusRow_eq_endpointSum
    (N g r U q : ℕ) (hq : 0 < q) :
    h15NormalizedBoundaryFixedFrequencyModulusRow N g r U q =
      ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
        ∑ u ∈ h15NormalizedSuperperiodBoundarySupport U
            (h15SquareDivisorProgressionModulus g d) q,
          h15NormalizedProgressionCoupledBoundaryPointWeight N g U
              (h15SquareDivisorProgressionModulus g d) q d u *
            h15PairedDirectCrossMode r u q := by
  unfold h15NormalizedBoundaryFixedFrequencyModulusRow
  apply Finset.sum_congr rfl
  intro d _hd
  rw [h15NormalizedBoundaryFourierRowValue_eq_pointRow
    N g r U (h15SquareDivisorProgressionModulus g d) q d hq]
  rfl

/-- Fully expanded ordered endpoint-pair correlation across distinct
moduli. -/
noncomputable def h15NormalizedBoundaryEndpointPairCorrelation
    (N g r U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    ∑ q' ∈ (h15BettinChandeeSupportedNatBlock N g Q).erase q,
      ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
        ∑ d' ∈ h15DyadicActivePeriodSquareDivisorIndices g U q',
          ∑ u ∈ h15NormalizedSuperperiodBoundarySupport U
              (h15SquareDivisorProgressionModulus g d) q,
            ∑ v ∈ h15NormalizedSuperperiodBoundarySupport U
                (h15SquareDivisorProgressionModulus g d') q',
              (h15NormalizedProgressionCoupledBoundaryPointWeight N g U
                    (h15SquareDivisorProgressionModulus g d) q d u *
                  h15PairedDirectCrossMode r u q) *
                (h15NormalizedProgressionCoupledBoundaryPointWeight N g U
                    (h15SquareDivisorProgressionModulus g d') q' d' v *
                  h15PairedDirectCrossMode r v q')

theorem h15NormalizedBoundaryExplicitCrossModulusCorrelation_eq_endpointPairs
    {N g r U Q : ℕ} (hQ : 0 < Q) :
    h15NormalizedBoundaryExplicitCrossModulusCorrelation N g r U Q =
      h15NormalizedBoundaryEndpointPairCorrelation N g r U Q := by
  unfold h15NormalizedBoundaryExplicitCrossModulusCorrelation
    h15NormalizedBoundaryEndpointPairCorrelation
  apply Finset.sum_congr rfl
  intro q hqMem
  have hqBounds := mem_h15BettinChandeeSupportedNatBlock.mp hqMem
  have hqPos : 0 < q := hQ.trans_le hqBounds.1
  apply Finset.sum_congr rfl
  intro q' hq'MemErase
  have hq'Mem := Finset.mem_of_mem_erase hq'MemErase
  have hq'Bounds := mem_h15BettinChandeeSupportedNatBlock.mp hq'Mem
  have hq'Pos : 0 < q' := hQ.trans_le hq'Bounds.1
  rw [h15NormalizedBoundaryFixedFrequencyModulusRow_eq_endpointSum
      N g r U q hqPos,
    h15NormalizedBoundaryFixedFrequencyModulusRow_eq_endpointSum
      N g r U q' hq'Pos]
  simp only [Finset.sum_mul_sum]

/-! ## Difference- and sum-frequency aggregates -/

noncomputable def h15NormalizedBoundaryEndpointPairDifferenceFrequency
    (N g r U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    ∑ q' ∈ (h15BettinChandeeSupportedNatBlock N g Q).erase q,
      ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
        ∑ d' ∈ h15DyadicActivePeriodSquareDivisorIndices g U q',
          ∑ u ∈ h15NormalizedSuperperiodBoundarySupport U
              (h15SquareDivisorProgressionModulus g d) q,
            ∑ v ∈ h15NormalizedSuperperiodBoundarySupport U
                (h15SquareDivisorProgressionModulus g d') q',
              (h15NormalizedProgressionCoupledBoundaryPointWeight N g U
                  (h15SquareDivisorProgressionModulus g d) q d u *
                h15NormalizedProgressionCoupledBoundaryPointWeight N g U
                  (h15SquareDivisorProgressionModulus g d') q' d' v) *
                (h15DoubledDirectAdditivePhase r u q *
                  conj (h15DoubledDirectAdditivePhase r v q')).re

noncomputable def h15NormalizedBoundaryEndpointPairSumFrequency
    (N g r U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    ∑ q' ∈ (h15BettinChandeeSupportedNatBlock N g Q).erase q,
      ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
        ∑ d' ∈ h15DyadicActivePeriodSquareDivisorIndices g U q',
          ∑ u ∈ h15NormalizedSuperperiodBoundarySupport U
              (h15SquareDivisorProgressionModulus g d) q,
            ∑ v ∈ h15NormalizedSuperperiodBoundarySupport U
                (h15SquareDivisorProgressionModulus g d') q',
              (h15NormalizedProgressionCoupledBoundaryPointWeight N g U
                  (h15SquareDivisorProgressionModulus g d) q d u *
                h15NormalizedProgressionCoupledBoundaryPointWeight N g U
                  (h15SquareDivisorProgressionModulus g d') q' d' v) *
                (h15DoubledDirectAdditivePhase r u q *
                  h15DoubledDirectAdditivePhase r v q').re

/-- Exact global product-to-sum decomposition. -/
theorem h15NormalizedBoundaryEndpointPairCorrelation_eq_difference_sub_sum
    (N g r U Q : ℕ) :
    h15NormalizedBoundaryEndpointPairCorrelation N g r U Q =
      (h15NormalizedBoundaryEndpointPairDifferenceFrequency N g r U Q -
        h15NormalizedBoundaryEndpointPairSumFrequency N g r U Q) / 2 := by
  unfold h15NormalizedBoundaryEndpointPairCorrelation
    h15NormalizedBoundaryEndpointPairDifferenceFrequency
    h15NormalizedBoundaryEndpointPairSumFrequency
  rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)]
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q' _hq'
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d' _hd'
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u _hu
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v _hv
  have hmode := h15PairedDirectCrossMode_mul_eq_difference_sub_sum r u q v q'
  linear_combination
    (2 *
      h15NormalizedProgressionCoupledBoundaryPointWeight N g U
        (h15SquareDivisorProgressionModulus g d) q d u *
      h15NormalizedProgressionCoupledBoundaryPointWeight N g U
        (h15SquareDivisorProgressionModulus g d') q' d' v) * hmode

/-- Combined exact phase-pair form of the correction-preserving
cross-modulus frontier. -/
theorem h15NormalizedBoundaryExplicitCrossModulusCorrelation_eq_phasePairs
    {N g r U Q : ℕ} (hQ : 0 < Q) :
    h15NormalizedBoundaryExplicitCrossModulusCorrelation N g r U Q =
      (h15NormalizedBoundaryEndpointPairDifferenceFrequency N g r U Q -
        h15NormalizedBoundaryEndpointPairSumFrequency N g r U Q) / 2 := by
  rw [h15NormalizedBoundaryExplicitCrossModulusCorrelation_eq_endpointPairs hQ,
    h15NormalizedBoundaryEndpointPairCorrelation_eq_difference_sub_sum]

end NBMellinTools.NB12
