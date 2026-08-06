/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15TerminalPrefixSuperperiod

/-!
# NB12zp: second Abel transform of the terminal superperiod variation

The first Abel transform leaves a terminal weight multiplying normalized H15
rows.  Those rows have exact zero total on every complete `L`-row block.
Applying finite Abel summation once more therefore produces only cumulative
normalized-row prefixes times adjacent terminal-weight differences: its
terminal mode vanishes algebraically.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius
open Complex

namespace NBMellinTools.NB12

/-! ## Coefficients and weights inside one normalized superperiod -/

noncomputable def h15NormalizedProgressionAbelTerminalWeight
    (N g k q : ℕ) : ℝ :=
  h15NormalizedProgressionEnvelopeIncrement N g k q (q - 1)

noncomputable def h15NormalizedRowSuperperiodAbelPrefix
    (g r j q d i : ℕ) : ℝ :=
  let L := h15SquareDivisorProgressionModulus g d
  ∑ s ∈ Finset.range (i + 1),
    h15PeriodNormalizedProgressionRow g r (j * L + s) q d

noncomputable def h15NormalizedRowSuperperiodTerminalDisplacement
    (N g j q d i : ℕ) : ℝ :=
  let L := h15SquareDivisorProgressionModulus g d
  h15NormalizedProgressionAbelTerminalWeight N g (j * L + i) q -
    h15NormalizedProgressionAbelTerminalWeight N g (j * L) q

noncomputable def h15NormalizedProgressionTerminalSecondAbelSuperperiodRow
    (N g r j q d : ℕ) : ℝ :=
  let L := h15SquareDivisorProgressionModulus g d
  ∑ i ∈ Finset.range (L - 1),
    h15NormalizedRowSuperperiodAbelPrefix g r j q d i *
      (h15NormalizedRowSuperperiodTerminalDisplacement N g j q d i -
        h15NormalizedRowSuperperiodTerminalDisplacement N g j q d (i + 1))

/-- Reindex the established normalized-row zero mode onto `range L`. -/
theorem sum_range_h15PeriodNormalizedProgressionRow_superperiod_eq_zero
    (g r j q d : ℕ) (hq : 0 < q)
    (hL : 0 < h15SquareDivisorProgressionModulus g d)
    (hcop : Nat.Coprime (h15SquareDivisorProgressionModulus g d) q) :
    (∑ s ∈ Finset.range (h15SquareDivisorProgressionModulus g d),
      h15PeriodNormalizedProgressionRow g r
        (j * h15SquareDivisorProgressionModulus g d + s) q d) = 0 := by
  have hzero := sum_h15PeriodNormalizedProgressionRow_superperiod_eq_zero
    g r j q d hq hL hcop
  rw [Finset.sum_Ico_eq_sum_range] at hzero
  have hlength :
      (j + 1) * h15SquareDivisorProgressionModulus g d -
          j * h15SquareDivisorProgressionModulus g d =
        h15SquareDivisorProgressionModulus g d := by
    simp [Nat.add_mul]
  simpa only [hlength] using hzero

/-- Exact second Abel identity on one complete normalized superperiod.  The
endpoint term is zero because the complete normalized-row sum is zero. -/
theorem h15NormalizedProgressionTerminalSuperperiodVariation_eq_secondAbel
    (N g r j q d : ℕ) (hq : 0 < q)
    (hL : 0 < h15SquareDivisorProgressionModulus g d)
    (hcop : Nat.Coprime (h15SquareDivisorProgressionModulus g d) q) :
    (∑ k ∈ Finset.Ico
        (j * h15SquareDivisorProgressionModulus g d)
        ((j + 1) * h15SquareDivisorProgressionModulus g d),
      (h15NormalizedProgressionAbelTerminalWeight N g k q -
        h15NormalizedProgressionAbelTerminalWeight N g
          (j * h15SquareDivisorProgressionModulus g d) q) *
        h15PeriodNormalizedProgressionRow g r k q d) =
      h15NormalizedProgressionTerminalSecondAbelSuperperiodRow
        N g r j q d := by
  let L := h15SquareDivisorProgressionModulus g d
  rw [Finset.sum_Ico_eq_sum_range]
  have hlength : (j + 1) * L - j * L = L := by
    simp [Nat.add_mul]
  rw [hlength]
  have hab := h15_sum_range_succ_mul_eq_endpoint_add_prefix
    (fun s => h15PeriodNormalizedProgressionRow g r (j * L + s) q d)
    (fun s => h15NormalizedRowSuperperiodTerminalDisplacement N g j q d s)
    (L - 1)
  have hsub : L - 1 + 1 = L := Nat.sub_add_cancel hL
  have hzero := sum_range_h15PeriodNormalizedProgressionRow_superperiod_eq_zero
    g r j q d hq hL hcop
  have hzeroL :
      (∑ s ∈ Finset.range L,
        h15PeriodNormalizedProgressionRow g r (j * L + s) q d) = 0 := by
    simpa only [L] using hzero
  unfold h15NormalizedProgressionTerminalSecondAbelSuperperiodRow
  dsimp only
  simp only [hsub, hzeroL, zero_mul, zero_add] at hab
  calc
    (∑ x ∈ Finset.range L,
      (h15NormalizedProgressionAbelTerminalWeight N g (j * L + x) q -
        h15NormalizedProgressionAbelTerminalWeight N g (j * L) q) *
        h15PeriodNormalizedProgressionRow g r (j * L + x) q d) =
      ∑ x ∈ Finset.range L,
        h15PeriodNormalizedProgressionRow g r (j * L + x) q d *
          h15NormalizedRowSuperperiodTerminalDisplacement N g j q d x := by
            apply Finset.sum_congr rfl
            intro x _hx
            unfold h15NormalizedRowSuperperiodTerminalDisplacement
            dsimp only
            ring
    _ = _ := by simpa only [hsub] using hab

/-! ## Dyadic second-Abel row -/

noncomputable def h15NormalizedProgressionTerminalSecondAbelRow
    (N g r U q d : ℕ) : ℝ :=
  let L := h15SquareDivisorProgressionModulus g d
  ∑ j ∈ h15CompleteNormalizedSuperperiodIndices U L q,
    h15NormalizedProgressionTerminalSecondAbelSuperperiodRow
      N g r j q d

theorem h15NormalizedProgressionAbelTerminalSuperperiodVariationRow_eq_secondAbel
    (N g r U q d : ℕ) (hq : 0 < q)
    (hL : 0 < h15SquareDivisorProgressionModulus g d)
    (hcop : Nat.Coprime (h15SquareDivisorProgressionModulus g d) q) :
    h15NormalizedProgressionAbelTerminalSuperperiodVariationRow N g r U q d =
      h15NormalizedProgressionTerminalSecondAbelRow N g r U q d := by
  unfold h15NormalizedProgressionAbelTerminalSuperperiodVariationRow
    h15NormalizedRowSuperperiodVariationDefect
    h15NormalizedProgressionTerminalSecondAbelRow
  dsimp only
  apply Finset.sum_congr rfl
  intro j _hj
  exact h15NormalizedProgressionTerminalSuperperiodVariation_eq_secondAbel
    N g r j q d hq hL hcop

/-! ## Smooth geometry of the second transform -/

/-- The first Abel terminal weight on a complete ordinary period is still
bounded by the dyadic inverse-square scale. -/
theorem abs_h15NormalizedProgressionAbelTerminalWeight_le
    {N g U k q : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g) (hU : 0 < U)
    (hq : 0 < q) (hk : k ∈ h15CompletePeriodIndices U q) :
    |h15NormalizedProgressionAbelTerminalWeight N g k q| ≤
      (1 / (U : ℝ)) ^ 2 := by
  unfold h15NormalizedProgressionAbelTerminalWeight
    h15NormalizedProgressionEnvelopeIncrement
  have hkBounds := (Finset.mem_filter.mp hk).2
  have hkqPos : 0 < k * q := hU.trans_le hkBounds.1
  have hanti := h15SupportedInverseSmoothEnvelope_antitone
    hN hg hkqPos (show k * q ≤ k * q + (q - 1) by omega)
  rw [abs_of_nonpos (sub_nonpos.mpr hanti)]
  have hkUpper : k * q + q ≤ 2 * U := by
    simpa only [Nat.add_mul, one_mul] using hkBounds.2
  have hkqMem : k * q ∈ h15BettinChandeeNatBlock U :=
    Finset.mem_Ico.mpr ⟨hkBounds.1,
      (Nat.lt_add_of_pos_right hq).trans_le hkUpper⟩
  have hleft := h15SupportedInverseSmoothEnvelope_le_of_mem_natBlock
    hN hg hU hkqMem
  have hright := h15SupportedInverseSmoothEnvelope_nonneg
    N g (k * q + (q - 1))
  linarith

/-- Adjacent terminal weights inside a complete normalized superperiod cost
at most twice the inverse-square scale. -/
theorem abs_h15NormalizedRowSuperperiodTerminalDisplacement_sub_succ_le
    {N g U j L q d i : ℕ}
    (hN : 2 ≤ N) (hg : 1 ≤ g) (hU : 0 < U) (hq : 0 < q)
    (hLdef : L = h15SquareDivisorProgressionModulus g d)
    (hj : j ∈ h15CompleteNormalizedSuperperiodIndices U L q)
    (hi : i ∈ Finset.range (L - 1)) :
    |h15NormalizedRowSuperperiodTerminalDisplacement N g j q d i -
        h15NormalizedRowSuperperiodTerminalDisplacement N g j q d (i + 1)| ≤
      2 * (1 / (U : ℝ)) ^ 2 := by
  have hiLt := Finset.mem_range.mp hi
  have hLPos : 0 < L := by omega
  have hki : j * L + i ∈ Finset.Ico (j * L) ((j + 1) * L) := by
    apply Finset.mem_Ico.mpr
    constructor
    · omega
    · have hstep : j * L + i < j * L + L := by omega
      simpa [Nat.add_mul] using hstep
  have hkiSucc : j * L + (i + 1) ∈
      Finset.Ico (j * L) ((j + 1) * L) := by
    apply Finset.mem_Ico.mpr
    constructor
    · omega
    · have hstep : j * L + (i + 1) < j * L + L := by omega
      simpa [Nat.add_mul] using hstep
  have hkSupport : j * L + i ∈
      h15CompleteNormalizedRowSuperperiodSupport U L q := by
    rw [h15CompleteNormalizedRowSuperperiodSupport, Finset.mem_biUnion]
    exact ⟨j, hj, hki⟩
  have hkSuccSupport : j * L + (i + 1) ∈
      h15CompleteNormalizedRowSuperperiodSupport U L q := by
    rw [h15CompleteNormalizedRowSuperperiodSupport, Finset.mem_biUnion]
    exact ⟨j, hj, hkiSucc⟩
  have hk := h15CompleteNormalizedRowSuperperiodSupport_subset_periodIndices
    U L q hq hkSupport
  have hkSucc := h15CompleteNormalizedRowSuperperiodSupport_subset_periodIndices
    U L q hq hkSuccSupport
  have hw := abs_h15NormalizedProgressionAbelTerminalWeight_le
    hN hg hU hq hk
  have hwSucc := abs_h15NormalizedProgressionAbelTerminalWeight_le
    hN hg hU hq hkSucc
  unfold h15NormalizedRowSuperperiodTerminalDisplacement
  dsimp only
  rw [← hLdef]
  calc
    |(h15NormalizedProgressionAbelTerminalWeight N g (j * L + i) q -
          h15NormalizedProgressionAbelTerminalWeight N g (j * L) q) -
        (h15NormalizedProgressionAbelTerminalWeight N g (j * L + (i + 1)) q -
          h15NormalizedProgressionAbelTerminalWeight N g (j * L) q)| =
      |h15NormalizedProgressionAbelTerminalWeight N g (j * L + i) q -
        h15NormalizedProgressionAbelTerminalWeight N g (j * L + (i + 1)) q| := by
          congr 1
          ring
    _ ≤ |h15NormalizedProgressionAbelTerminalWeight N g (j * L + i) q| +
        |h15NormalizedProgressionAbelTerminalWeight N g (j * L + (i + 1)) q| :=
      abs_sub _ _
    _ ≤ 2 * (1 / (U : ℝ)) ^ 2 := by linarith

/-! ## Prefix threshold for the second transform -/

def H15NormalizedRowSuperperiodAbelPrefixBound
    (N g r U Q : ℕ) (P : ℝ) : Prop :=
  0 ≤ P ∧
    ∀ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
      ∀ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
        ∀ j ∈ h15CompleteNormalizedSuperperiodIndices U
          (h15SquareDivisorProgressionModulus g d) q,
          ∀ i ∈ Finset.range
            (h15SquareDivisorProgressionModulus g d - 1),
            |h15NormalizedRowSuperperiodAbelPrefix g r j q d i| ≤ P

theorem abs_h15NormalizedProgressionTerminalSecondAbelSuperperiodRow_le
    {N g r U j q d : ℕ} {P : ℝ}
    (hN : 2 ≤ N) (hg : 1 ≤ g) (hU : 0 < U) (hq : 0 < q)
    (hj : j ∈ h15CompleteNormalizedSuperperiodIndices U
      (h15SquareDivisorProgressionModulus g d) q)
    (hP : 0 ≤ P)
    (hprefix : ∀ i ∈ Finset.range
      (h15SquareDivisorProgressionModulus g d - 1),
        |h15NormalizedRowSuperperiodAbelPrefix g r j q d i| ≤ P) :
    |h15NormalizedProgressionTerminalSecondAbelSuperperiodRow
        N g r j q d| ≤
      (h15SquareDivisorProgressionModulus g d : ℝ) *
        (P * (2 * (1 / (U : ℝ)) ^ 2)) := by
  let L := h15SquareDivisorProgressionModulus g d
  unfold h15NormalizedProgressionTerminalSecondAbelSuperperiodRow
  dsimp only
  calc
    |∑ i ∈ Finset.range (L - 1),
      h15NormalizedRowSuperperiodAbelPrefix g r j q d i *
        (h15NormalizedRowSuperperiodTerminalDisplacement N g j q d i -
          h15NormalizedRowSuperperiodTerminalDisplacement N g j q d (i + 1))| ≤
      ∑ i ∈ Finset.range (L - 1),
        |h15NormalizedRowSuperperiodAbelPrefix g r j q d i *
          (h15NormalizedRowSuperperiodTerminalDisplacement N g j q d i -
            h15NormalizedRowSuperperiodTerminalDisplacement N g j q d (i + 1))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range (L - 1),
        P * (2 * (1 / (U : ℝ)) ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul
        (hprefix i hi)
        (abs_h15NormalizedRowSuperperiodTerminalDisplacement_sub_succ_le
          hN hg hU hq rfl hj hi)
        (abs_nonneg _) hP
    _ = ((L - 1 : ℕ) : ℝ) *
        (P * (2 * (1 / (U : ℝ)) ^ 2)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (L : ℝ) * (P * (2 * (1 / (U : ℝ)) ^ 2)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast Nat.sub_le L 1

/-- For one active divisor row, complete normalized-superperiod geometry
turns the second Abel variation into `2P/(qU)`. -/
theorem abs_h15NormalizedProgressionTerminalSecondAbelRow_le
    {N g r U q d : ℕ} {P : ℝ}
    (hN : 2 ≤ N) (hg : 1 ≤ g) (hU : 0 < U) (hq : 0 < q)
    (hP : 0 ≤ P)
    (hprefix : ∀ j ∈ h15CompleteNormalizedSuperperiodIndices U
      (h15SquareDivisorProgressionModulus g d) q,
      ∀ i ∈ Finset.range
        (h15SquareDivisorProgressionModulus g d - 1),
        |h15NormalizedRowSuperperiodAbelPrefix g r j q d i| ≤ P) :
    |h15NormalizedProgressionTerminalSecondAbelRow N g r U q d| ≤
      2 * P / ((q : ℝ) * (U : ℝ)) := by
  let L := h15SquareDivisorProgressionModulus g d
  unfold h15NormalizedProgressionTerminalSecondAbelRow
  dsimp only
  calc
    |∑ j ∈ h15CompleteNormalizedSuperperiodIndices U L q,
        h15NormalizedProgressionTerminalSecondAbelSuperperiodRow
          N g r j q d| ≤
      ∑ j ∈ h15CompleteNormalizedSuperperiodIndices U L q,
        |h15NormalizedProgressionTerminalSecondAbelSuperperiodRow
          N g r j q d| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ h15CompleteNormalizedSuperperiodIndices U L q,
        (L : ℝ) * (P * (2 * (1 / (U : ℝ)) ^ 2)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact abs_h15NormalizedProgressionTerminalSecondAbelSuperperiodRow_le
        hN hg hU hq hj hP (hprefix j hj)
    _ = ((h15CompleteNormalizedSuperperiodIndices U L q).card : ℝ) *
        ((L : ℝ) * (P * (2 * (1 / (U : ℝ)) ^ 2))) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * P / ((q : ℝ) * (U : ℝ)) := by
      have hcountNat := card_h15CompletePeriodIndices_mul_le U (L * q)
      have hcount :
          ((h15CompleteNormalizedSuperperiodIndices U L q).card : ℝ) *
              ((L : ℝ) * (q : ℝ)) ≤ (U : ℝ) := by
        exact_mod_cast hcountNat
      have hfactor :
          0 ≤ 2 * P / ((U : ℝ) ^ 2 * (q : ℝ)) := by positivity
      have hmul := mul_le_mul_of_nonneg_right hcount hfactor
      calc
        ((h15CompleteNormalizedSuperperiodIndices U L q).card : ℝ) *
            ((L : ℝ) * (P * (2 * (1 / (U : ℝ)) ^ 2))) =
          (((h15CompleteNormalizedSuperperiodIndices U L q).card : ℝ) *
              ((L : ℝ) * (q : ℝ))) *
            (2 * P / ((U : ℝ) ^ 2 * (q : ℝ))) := by
              field_simp
        _ ≤ (U : ℝ) *
            (2 * P / ((U : ℝ) ^ 2 * (q : ℝ))) := hmul
        _ = 2 * P / ((q : ℝ) * (U : ℝ)) := by
          field_simp

/-! ## Full active aggregate and exponent audit -/

noncomputable def h15NormalizedProgressionTerminalSecondAbelAggregate
    (N g r U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
      h15NormalizedProgressionTerminalSecondAbelRow N g r U q d

theorem h15NormalizedProgressionAbelTerminalSuperperiodVariationAggregate_eq_secondAbel
    {N g r U Q : ℕ} (hQ : 0 < Q) :
    h15NormalizedProgressionAbelTerminalSuperperiodVariationAggregate
        N g r U Q =
      h15NormalizedProgressionTerminalSecondAbelAggregate N g r U Q := by
  unfold h15NormalizedProgressionAbelTerminalSuperperiodVariationAggregate
    h15NormalizedProgressionTerminalSecondAbelAggregate
  apply Finset.sum_congr rfl
  intro q hqMem
  have hqBounds := mem_h15BettinChandeeSupportedNatBlock.mp hqMem
  have hqPos : 0 < q := hQ.trans_le hqBounds.1
  apply Finset.sum_congr rfl
  intro d hd
  have hd' := hd
  rw [h15DyadicActivePeriodSquareDivisorIndices,
    Finset.mem_biUnion] at hd'
  obtain ⟨k, _hk, hdk⟩ := hd'
  have hactive := mem_h15ActivePeriodSquareDivisorIndices.mp hdk
  have hLPos : 0 < h15SquareDivisorProgressionModulus g d := by omega
  exact h15NormalizedProgressionAbelTerminalSuperperiodVariationRow_eq_secondAbel
    N g r U q d hqPos hLPos hactive.2.2

/-- The second Abel layer has the same favorable exponent threshold as the
first: a uniform cumulative normalized-row prefix bound `P` costs at most
`4 * τ(g) * P`, independently of the dyadic scales. -/
theorem abs_h15NormalizedProgressionTerminalSecondAbelAggregate_le
    {N g r U Q : ℕ} {P : ℝ}
    (hN : 2 ≤ N) (hg : 1 ≤ g) (hU : 0 < U) (hQ : 0 < Q)
    (hprefix : H15NormalizedRowSuperperiodAbelPrefixBound N g r U Q P) :
    |h15NormalizedProgressionTerminalSecondAbelAggregate N g r U Q| ≤
      4 * (g.divisors.card : ℝ) * P := by
  rcases hprefix with ⟨hP, hprefix⟩
  unfold h15NormalizedProgressionTerminalSecondAbelAggregate
  calc
    |∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
      ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
        h15NormalizedProgressionTerminalSecondAbelRow N g r U q d| ≤
      ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        |∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
          h15NormalizedProgressionTerminalSecondAbelRow N g r U q d| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        4 * (g.divisors.card : ℝ) * P / (q : ℝ) := by
      apply Finset.sum_le_sum
      intro q hqMem
      have hqBounds := mem_h15BettinChandeeSupportedNatBlock.mp hqMem
      have hqPos : 0 < q := hQ.trans_le hqBounds.1
      calc
        |∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
          h15NormalizedProgressionTerminalSecondAbelRow N g r U q d| ≤
          ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
            |h15NormalizedProgressionTerminalSecondAbelRow N g r U q d| :=
              Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
            2 * P / ((q : ℝ) * (U : ℝ)) := by
          apply Finset.sum_le_sum
          intro d hd
          exact abs_h15NormalizedProgressionTerminalSecondAbelRow_le
            hN hg hU hqPos hP (hprefix q hqMem d hd)
        _ = ((h15DyadicActivePeriodSquareDivisorIndices g U q).card : ℝ) *
            (2 * P / ((q : ℝ) * (U : ℝ))) := by
          simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 4 * (g.divisors.card : ℝ) * P / (q : ℝ) := by
          have hd := card_h15DyadicActivePeriodSquareDivisorIndices_le
            (q := q) (show 0 < g by omega) hU
          have hfactor : 0 ≤ 2 * P / ((q : ℝ) * (U : ℝ)) := by positivity
          have hmul := mul_le_mul_of_nonneg_right hd hfactor
          calc
            ((h15DyadicActivePeriodSquareDivisorIndices g U q).card : ℝ) *
                (2 * P / ((q : ℝ) * (U : ℝ))) ≤
              (2 * (U : ℝ)) * (g.divisors.card : ℝ) *
                (2 * P / ((q : ℝ) * (U : ℝ))) := by
                  exact hmul
            _ = 4 * (g.divisors.card : ℝ) * P / (q : ℝ) := by
              field_simp
              ring
    _ ≤ ∑ _q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        4 * (g.divisors.card : ℝ) * P / (Q : ℝ) := by
      apply Finset.sum_le_sum
      intro q hqMem
      have hqBounds := mem_h15BettinChandeeSupportedNatBlock.mp hqMem
      apply div_le_div_of_nonneg_left (by positivity)
        (by positivity : (0 : ℝ) < (Q : ℝ))
      exact_mod_cast hqBounds.1
    _ = ((h15BettinChandeeSupportedNatBlock N g Q).card : ℝ) *
        (4 * (g.divisors.card : ℝ) * P / (Q : ℝ)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Q : ℝ) *
        (4 * (g.divisors.card : ℝ) * P / (Q : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_h15BettinChandeeSupportedNatBlock_le N g Q
    _ = 4 * (g.divisors.card : ℝ) * P := by
      field_simp

/-- Final exact Step 4v-i decomposition: both smooth variation sectors are
now in Abel-prefix form; the only non-variation object is the final coupled
superperiod boundary. -/
theorem h15NormalizedProgressionRowToPointwiseResidual_eq_twoAbel_add_boundary
    {N g r U Q : ℕ} (hQ : 0 < Q) :
    h15NormalizedProgressionRowToPointwiseResidual N g r U Q =
      h15NormalizedProgressionAbelInteriorAggregate N g r U Q +
        h15NormalizedProgressionTerminalSecondAbelAggregate N g r U Q +
        h15NormalizedProgressionCorrectionCoupledSuperperiodBoundaryAggregate
          N g r U Q := by
  rw [h15NormalizedProgressionRowToPointwiseResidual_eq_twoVariations_add_boundary
      hQ,
    h15NormalizedProgressionAbelTerminalSuperperiodVariationAggregate_eq_secondAbel
      hQ]

/-- Quantitative two-prefix consequence.  For fixed `g`, uniform decay of
both exact prefix norms is sufficient for both smooth sectors; only the
already coupled final superperiod boundary is left outside these budgets. -/
theorem abs_h15NormalizedProgressionRowToPointwiseResidual_le_twoPrefixes
    {N g r U Q : ℕ} {P₁ P₂ B : ℝ}
    (hN : 2 ≤ N) (hg : 1 ≤ g) (hU : 0 < U) (hQ : 0 < Q)
    (hprefix₁ : H15NormalizedProgressionAbelPrefixBound N g r U Q P₁)
    (hprefix₂ : H15NormalizedRowSuperperiodAbelPrefixBound N g r U Q P₂)
    (hboundary :
      |h15NormalizedProgressionCorrectionCoupledSuperperiodBoundaryAggregate
        N g r U Q| ≤ B) :
    |h15NormalizedProgressionRowToPointwiseResidual N g r U Q| ≤
      2 * (g.divisors.card : ℝ) * P₁ +
        4 * (g.divisors.card : ℝ) * P₂ + B := by
  rw [h15NormalizedProgressionRowToPointwiseResidual_eq_twoAbel_add_boundary hQ]
  calc
    |h15NormalizedProgressionAbelInteriorAggregate N g r U Q +
        h15NormalizedProgressionTerminalSecondAbelAggregate N g r U Q +
        h15NormalizedProgressionCorrectionCoupledSuperperiodBoundaryAggregate
          N g r U Q| ≤
      |h15NormalizedProgressionAbelInteriorAggregate N g r U Q| +
        |h15NormalizedProgressionTerminalSecondAbelAggregate N g r U Q| +
        |h15NormalizedProgressionCorrectionCoupledSuperperiodBoundaryAggregate
          N g r U Q| := by
            exact (abs_add_le _ _).trans
              (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 2 * (g.divisors.card : ℝ) * P₁ +
        4 * (g.divisors.card : ℝ) * P₂ + B := by
      gcongr
      · exact abs_h15NormalizedProgressionAbelInteriorAggregate_le
          hN hg hU hQ hprefix₁
      · exact abs_h15NormalizedProgressionTerminalSecondAbelAggregate_le
          hN hg hU hQ hprefix₂

end NBMellinTools.NB12
