/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15ArithmeticMass

/-!
# Explicit polynomial cutoff for the H15 ultra-high frequency tail

This file makes the moving cutoff in the H15 three-halves-line remainder
quantitative.  The proved divisor-square estimate gives a power bound on one
dyadic frequency block.  An exact injection of the shifted tail into the
dyadic partition then yields a geometric tail bound.

The cutoff
`2 ^ Nat.clog 2 ((n + 2) ^ 40)` is below `2 * (n + 2) ^ 40`, while the
frequency tail is `O((n + 2)⁻¹⁰)`.  After coupling it to the complete finite
arithmetic ledger, the ultra-high budget is `O((n + 2)⁻⁵)` and therefore
vanishes.  This closes the previously non-quantitative ultra-high sector with
a fixed polynomial threshold.  It does not estimate the retained low and
middle Bettin--Chandee frequency window.
-/

open scoped BigOperators
open Complex Filter Topology

namespace NBMellinTools.NB12

/-- A power majorant for the logarithmic expression in the blockwise
divisor-square estimate.  The constant is intentionally explicit rather than
optimized. -/
theorem h15FrequencyBlockSqMajorant_le_power (R : ℕ) (hR : 1 ≤ R) :
    2 * (1 + Real.log (2 * (R : ℝ))) ^ 3 / (R : ℝ) ≤
      1372 * (R : ℝ) ^ (-1 / 2 : ℝ) := by
  let x : ℝ := 2 * (R : ℝ)
  have hRpos : (0 : ℝ) < (R : ℝ) := by positivity
  have hxpos : 0 < x := by dsimp [x]; positivity
  have hRone : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hxone : 1 ≤ x := by dsimp [x]; linarith
  have hpone : 1 ≤ x ^ (1 / 6 : ℝ) :=
    Real.one_le_rpow hxone (by norm_num)
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hxone
  have hlograw := Real.log_le_rpow_div hxpos.le
    (show (0 : ℝ) < 1 / 6 by norm_num)
  have hlog : Real.log x ≤ 6 * x ^ (1 / 6 : ℝ) := by
    convert hlograw using 1 <;> ring
  have hsum : 1 + Real.log x ≤ 7 * x ^ (1 / 6 : ℝ) := by
    nlinarith
  have hcube : (1 + Real.log x) ^ 3 ≤
      (7 * x ^ (1 / 6 : ℝ)) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hsum 3
  have hrpow : (x ^ (1 / 6 : ℝ)) ^ 3 = x ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_mul_natCast hxpos.le]
    norm_num
  have hxhalf : x ^ (1 / 2 : ℝ) ≤ 2 * (R : ℝ) ^ (1 / 2 : ℝ) := by
    rw [show x = 2 * (R : ℝ) by rfl, Real.mul_rpow (by norm_num) hRpos.le]
    have htwo : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
      have := Real.rpow_le_rpow (show (0 : ℝ) ≤ 2 by norm_num)
        (show (2 : ℝ) ≤ 4 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      norm_num at this ⊢
      exact this
    exact mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hRpos.le _)
  calc
    2 * (1 + Real.log (2 * (R : ℝ))) ^ 3 / (R : ℝ) =
        2 * (1 + Real.log x) ^ 3 / (R : ℝ) := by rfl
    _ ≤ 2 * (7 * x ^ (1 / 6 : ℝ)) ^ 3 / (R : ℝ) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcube (by norm_num)) hRpos.le
    _ = 686 * x ^ (1 / 2 : ℝ) / (R : ℝ) := by
      rw [mul_pow, hrpow]
      ring
    _ ≤ 686 * (2 * (R : ℝ) ^ (1 / 2 : ℝ)) / (R : ℝ) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hxhalf (by norm_num)) hRpos.le
    _ = 1372 * (R : ℝ) ^ (-1 / 2 : ℝ) := by
      rw [show (R : ℝ) ^ (-1 / 2 : ℝ) =
          (R : ℝ) ^ (1 / 2 : ℝ) / (R : ℝ) by
        calc
          (R : ℝ) ^ (-1 / 2 : ℝ) =
              (R : ℝ) ^ ((1 / 2 : ℝ) - 1) := by norm_num
          _ = (R : ℝ) ^ (1 / 2 : ℝ) / (R : ℝ) ^ (1 : ℝ) :=
            Real.rpow_sub hRpos _ _
          _ = (R : ℝ) ^ (1 / 2 : ℝ) / (R : ℝ) := by
            rw [Real.rpow_one]]
      ring

/-- The `L¹` mass of one frequency block has power decay `R⁻¹/⁴`. -/
theorem h15BettinChandeeFrequencyBlockL1_le_power
    (R : ℕ) (hR : 1 ≤ R) :
    h15BettinChandeeFrequencyBlockL1 R ≤
      40 * (R : ℝ) ^ (-1 / 4 : ℝ) := by
  have hsq : h15BettinChandeeFrequencyBlockL1 R ^ 2 ≤
      1372 * (R : ℝ) ^ (-1 / 2 : ℝ) :=
    (h15BettinChandeeFrequencyBlockL1_sq_le_explicit R hR).trans
      (h15FrequencyBlockSqMajorant_le_power R hR)
  have hR0 : 0 ≤ (R : ℝ) := by positivity
  have hrpow : ((R : ℝ) ^ (-1 / 4 : ℝ)) ^ 2 =
      (R : ℝ) ^ (-1 / 2 : ℝ) := by
    rw [← Real.rpow_mul_natCast hR0]
    norm_num
  have hright : 1372 * (R : ℝ) ^ (-1 / 2 : ℝ) ≤
      (40 * (R : ℝ) ^ (-1 / 4 : ℝ)) ^ 2 := by
    rw [mul_pow, hrpow]
    have := Real.rpow_nonneg hR0 (-1 / 2 : ℝ)
    nlinarith
  have hnonneg := h15BettinChandeeFrequencyBlockL1_nonneg R
  have htarget : 0 ≤ 40 * (R : ℝ) ^ (-1 / 4 : ℝ) := by positivity
  nlinarith [hsq.trans hright]

/-- On powers of two the block estimate is a geometric majorant. -/
theorem h15BettinChandeeFrequencyBlockL1_two_pow_le_geometric (k : ℕ) :
    h15BettinChandeeFrequencyBlockL1 (2 ^ k) ≤
      40 * ((2 : ℝ) ^ (-1 / 4 : ℝ)) ^ k := by
  have h := h15BettinChandeeFrequencyBlockL1_le_power
    (2 ^ k) (Nat.one_le_two_pow)
  calc
    h15BettinChandeeFrequencyBlockL1 (2 ^ k) ≤
        40 * (((2 ^ k : ℕ) : ℝ)) ^ (-1 / 4 : ℝ) := h
    _ = 40 * ((2 : ℝ) ^ (-1 / 4 : ℝ)) ^ k := by
      congr 1
      rw [Nat.cast_pow, Nat.cast_ofNat]
      rw [← Real.rpow_natCast_mul (show (0 : ℝ) ≤ 2 by norm_num)]
      rw [mul_comm]
      exact Real.rpow_mul_natCast (show (0 : ℝ) ≤ 2 by norm_num) _ _

/-- The complete dyadic frequency tail admits an explicit geometric bound. -/
theorem h15BettinChandeeDyadicFrequencyTail_le_geometric (J : ℕ) :
    h15BettinChandeeDyadicFrequencyTail J ≤
      40 * ((2 : ℝ) ^ (-1 / 4 : ℝ)) ^ J *
        (1 - (2 : ℝ) ^ (-1 / 4 : ℝ))⁻¹ := by
  let r : ℝ := (2 : ℝ) ^ (-1 / 4 : ℝ)
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := by
    dsimp [r]
    rw [show (-1 / 4 : ℝ) = -(1 / 4 : ℝ) by ring,
      Real.rpow_neg_eq_inv_rpow]
    exact Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num)
  have hgeom : Summable (fun j : ℕ => 40 * r ^ (j + J)) := by
    apply ((summable_geometric_of_lt_one hr0 hr1).mul_left
      (40 * r ^ J)).congr
    intro j
    rw [pow_add]
    ring
  have hblocks : Summable (fun j : ℕ =>
      h15BettinChandeeFrequencyBlockL1 (2 ^ (j + J))) := by
    exact summable_h15BettinChandeeFrequencyBlockL1_two_pow.comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
  calc
    h15BettinChandeeDyadicFrequencyTail J =
        ∑' j : ℕ, h15BettinChandeeFrequencyBlockL1 (2 ^ (j + J)) := rfl
    _ ≤ ∑' j : ℕ, 40 * r ^ (j + J) := by
      apply hblocks.tsum_le_tsum
      · intro j
        simpa [r] using
          h15BettinChandeeFrequencyBlockL1_two_pow_le_geometric (j + J)
      · exact hgeom
    _ = 40 * r ^ J * (1 - r)⁻¹ := by
      rw [show (fun j : ℕ => 40 * r ^ (j + J)) =
          (fun j : ℕ => (40 * r ^ J) * r ^ j) by
        funext j
        rw [pow_add]
        ring]
      rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
    _ = 40 * ((2 : ℝ) ^ (-1 / 4 : ℝ)) ^ J *
        (1 - (2 : ℝ) ^ (-1 / 4 : ℝ))⁻¹ := by rfl

private abbrev H15ShiftedTailSigma (J : ℕ) :=
  Σ k : ℕ, {r : ℕ // r ∈ h15BettinChandeeNatBlock (2 ^ (k + J))}

private def h15ShiftedTailSigmaToNat (J : ℕ) : H15ShiftedTailSigma J → ℕ :=
  fun x => x.2.val

private theorem h15ShiftedTailSigmaToNat_injective (J : ℕ) :
    Function.Injective (h15ShiftedTailSigmaToNat J) := by
  rintro ⟨k, r⟩ ⟨l, s⟩ h
  have hrval : r.val = s.val := h
  have hklog : Nat.log2 r.val = k + J := by
    rw [Nat.log2_eq_log_two]
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · exact (Finset.mem_Ico.mp r.property).1
    · simpa [h15BettinChandeeNatBlock, pow_succ, Nat.mul_comm] using
        (Finset.mem_Ico.mp r.property).2
  have hllog : Nat.log2 s.val = l + J := by
    rw [Nat.log2_eq_log_two]
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · exact (Finset.mem_Ico.mp s.property).1
    · simpa [h15BettinChandeeNatBlock, pow_succ, Nat.mul_comm] using
        (Finset.mem_Ico.mp s.property).2
  have hkl : k = l := by
    have : k + J = l + J := by rw [← hklog, ← hllog, hrval]
    exact Nat.add_right_cancel this
  subst l
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext hrval))

private theorem h15_shifted_frequency_mem_tail_block (J j : ℕ) :
    j + 2 ^ J ∈ h15BettinChandeeNatBlock
      (2 ^ (Nat.log2 (j + 2 ^ J) - J + J)) := by
  let r := j + 2 ^ J
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hJlog : J ≤ Nat.log2 r := by
    rw [Nat.log2_eq_log_two]
    apply Nat.le_log_of_pow_le (by norm_num)
    dsimp [r]
    omega
  have hsub : Nat.log2 r - J + J = Nat.log2 r := Nat.sub_add_cancel hJlog
  rw [hsub]
  simp only [h15BettinChandeeNatBlock, Finset.mem_Ico]
  constructor
  · rw [Nat.log2_eq_log_two]
    exact Nat.pow_log_le_self 2 hrpos.ne'
  · rw [Nat.log2_eq_log_two]
    simpa [pow_succ, Nat.mul_comm] using
      Nat.lt_pow_succ_log_self (b := 2) (by norm_num) r

private def h15ShiftToTailSigma (J : ℕ) (j : ℕ) : H15ShiftedTailSigma J :=
  ⟨Nat.log2 (j + 2 ^ J) - J,
    ⟨j + 2 ^ J, h15_shifted_frequency_mem_tail_block J j⟩⟩

private theorem h15ShiftToTailSigma_injective (J : ℕ) :
    Function.Injective (h15ShiftToTailSigma J) := by
  intro j k h
  have hval := congrArg (fun x : H15ShiftedTailSigma J => x.2.val) h
  dsimp [h15ShiftToTailSigma] at hval
  exact Nat.add_right_cancel hval

private theorem summable_h15ShiftedTailSigma (J : ℕ) :
    Summable (fun x : H15ShiftedTailSigma J =>
      h15BettinChandeeFrequencyCoefficient x.2.val) := by
  have hfrequency : Summable h15BettinChandeeFrequencyCoefficient := by
    simpa [h15BettinChandeeFrequencyCoefficient] using
      summable_bblsThreeHalfDirichletMajorant
  simpa [h15ShiftedTailSigmaToNat] using
    hfrequency.comp_injective (h15ShiftedTailSigmaToNat_injective J)

/-- The shifted tail used by the analytic remainder is contained in the exact
dyadic partition.  This is an indexing theorem, not an asymptotic
replacement. -/
theorem h15ThreeHalfShiftedFrequencyTail_le_dyadicTail (J : ℕ) :
    h15ThreeHalfShiftedFrequencyTail J ≤
      h15BettinChandeeDyadicFrequencyTail J := by
  let f : H15ShiftedTailSigma J → ℝ := fun x =>
    h15BettinChandeeFrequencyCoefficient x.2.val
  have hf : Summable f := summable_h15ShiftedTailSigma J
  have hnonneg : ∀ x, 0 ≤ f x := fun x =>
    h15BettinChandeeFrequencyCoefficient_nonneg x.2.val
  calc
    h15ThreeHalfShiftedFrequencyTail J =
        ∑' j : ℕ, f (h15ShiftToTailSigma J j) := by rfl
    _ ≤ ∑' x : H15ShiftedTailSigma J, f x :=
      tsum_comp_le_tsum_of_inj hf hnonneg (h15ShiftToTailSigma_injective J)
    _ = ∑' k : ℕ, ∑' r : {r : ℕ //
          r ∈ h15BettinChandeeNatBlock (2 ^ (k + J))},
          h15BettinChandeeFrequencyCoefficient r.val := by
      simpa [f] using hf.tsum_sigma
    _ = h15BettinChandeeDyadicFrequencyTail J := by
      unfold h15BettinChandeeDyadicFrequencyTail
      apply tsum_congr
      intro k
      rw [tsum_fintype]
      unfold h15BettinChandeeFrequencyBlockL1
      exact Finset.sum_attach _ _

/-- Explicit geometric decay of the exact shifted H15 frequency tail. -/
theorem h15ThreeHalfShiftedFrequencyTail_le_geometric (J : ℕ) :
    h15ThreeHalfShiftedFrequencyTail J ≤
      40 * ((2 : ℝ) ^ (-1 / 4 : ℝ)) ^ J *
        (1 - (2 : ℝ) ^ (-1 / 4 : ℝ))⁻¹ :=
  (h15ThreeHalfShiftedFrequencyTail_le_dyadicTail J).trans
    (h15BettinChandeeDyadicFrequencyTail_le_geometric J)

/-- Dyadic exponent defining the fixed polynomial H15 cutoff. -/
def h15PolynomialFrequencyExponent (n : ℕ) : ℕ :=
  Nat.clog 2 ((n + 2) ^ 40)

set_option maxHeartbeats 1000000 in
/-- The selected dyadic threshold is genuinely polynomial in `n`.  The
larger heartbeat budget is needed for normalization of the `Nat.clog`
predecessor identity at the fixed exponent forty. -/
theorem h15PolynomialFrequencyThreshold_lt (n : ℕ) :
    2 ^ h15PolynomialFrequencyExponent n < 2 * (n + 2) ^ 40 := by
  let J : ℕ := Nat.clog 2 ((n + 2) ^ 40)
  have hx : 1 < (n + 2) ^ 40 := by
    exact one_lt_pow₀ (by omega) (by norm_num)
  have hJpos : 0 < J := by
    change 0 < Nat.clog 2 ((n + 2) ^ 40)
    exact Nat.clog_pos (b := 2) (n := (n + 2) ^ 40) (by norm_num) hx
  have hpred : 2 ^ J.pred < (n + 2) ^ 40 := by
    apply Nat.pow_lt_of_lt_clog
    change J.pred < J
    exact Nat.pred_lt (Nat.ne_of_gt hJpos)
  have hJ : J.pred + 1 = J := Nat.succ_pred_eq_of_pos hJpos
  calc
    2 ^ h15PolynomialFrequencyExponent n = 2 ^ J := by rfl
    _ = 2 ^ (J.pred + 1) := by rw [hJ]
    _ = 2 * 2 ^ J.pred := by
      rw [pow_succ]
      exact Nat.mul_comm _ _
    _ < 2 * (n + 2) ^ 40 :=
      Nat.mul_lt_mul_of_pos_left hpred (by norm_num)

set_option maxHeartbeats 5000000 in
private theorem h15PolynomialFrequencyPower_le (n : ℕ) :
    ((2 : ℝ) ^ (-1 / 4 : ℝ)) ^ h15PolynomialFrequencyExponent n ≤
      ((n + 2 : ℕ) : ℝ) ^ (-10 : ℝ) := by
  let x : ℕ := n + 2
  let J : ℕ := h15PolynomialFrequencyExponent n
  have hxpos : (0 : ℝ) < (x : ℝ) := by dsimp [x]; positivity
  have hnat : x ^ 40 ≤ 2 ^ J := by
    dsimp [J, h15PolynomialFrequencyExponent]
    exact Nat.le_pow_clog (by norm_num) (x ^ 40)
  have hcast : ((x ^ 40 : ℕ) : ℝ) ≤ ((2 ^ J : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hxnat : 0 < x := by dsimp [x]; omega
  have hxpowpos : (0 : ℝ) < ((x ^ 40 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.pow_pos hxnat : 0 < x ^ 40)
  have hneg := Real.rpow_le_rpow_of_nonpos
    hxpowpos
    hcast (show (-1 / 4 : ℝ) ≤ 0 by norm_num)
  have htwo : (((2 ^ J : ℕ) : ℝ)) ^ (-1 / 4 : ℝ) =
      ((2 : ℝ) ^ (-1 / 4 : ℝ)) ^ J := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    rw [← Real.rpow_natCast_mul (show (0 : ℝ) ≤ 2 by norm_num)]
    rw [mul_comm]
    exact Real.rpow_mul_natCast (show (0 : ℝ) ≤ 2 by norm_num) _ _
  have hx : (((x ^ 40 : ℕ) : ℝ)) ^ (-1 / 4 : ℝ) =
      (x : ℝ) ^ (-10 : ℝ) := by
    rw [Nat.cast_pow]
    rw [← Real.rpow_natCast_mul hxpos.le]
    norm_num
  rw [htwo, hx] at hneg
  simpa [x, J] using hneg

/-- Along the fixed polynomial cutoff, the exact shifted frequency tail is
`O((n+2)⁻¹⁰)`. -/
theorem h15ThreeHalfShiftedFrequencyTail_le_polynomial (n : ℕ) :
    h15ThreeHalfShiftedFrequencyTail (h15PolynomialFrequencyExponent n) ≤
      40 * (((n + 2 : ℕ) : ℝ) ^ (-10 : ℝ)) *
        (1 - (2 : ℝ) ^ (-1 / 4 : ℝ))⁻¹ := by
  have hrinv : 0 ≤ (1 - (2 : ℝ) ^ (-1 / 4 : ℝ))⁻¹ := by
    have hrlt : (2 : ℝ) ^ (-1 / 4 : ℝ) < 1 := by
      rw [show (-1 / 4 : ℝ) = -(1 / 4 : ℝ) by ring,
        Real.rpow_neg_eq_inv_rpow]
      exact Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num)
    positivity
  exact (h15ThreeHalfShiftedFrequencyTail_le_geometric
      (h15PolynomialFrequencyExponent n)).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (h15PolynomialFrequencyPower_le n) (by norm_num))
      hrinv)

/-- The complete arithmetic-frequency budget at the polynomial cutoff. -/
theorem h15ThreeHalfUltraHighCoupledBudget_le_polynomialCutoff (n : ℕ) :
    h15ThreeHalfUltraHighCoupledBudget n
        (h15PolynomialFrequencyExponent n) ≤
      h15ThreeHalfFrequencyConstant *
        ((1 / (((n + 1 : ℕ) : ℝ))) ^ (3 / 2 : ℝ) *
          (2 * Real.pi * ((n + 2 : ℕ) : ℝ) ^ 5)) *
        (40 * (((n + 2 : ℕ) : ℝ) ^ (-10 : ℝ)) *
          (1 - (2 : ℝ) ^ (-1 / 4 : ℝ))⁻¹) *
        h15ThreeHalfVerticalProfileMass := by
  let M : ℝ :=
    h15ThreeHalfFrequencyConstant *
      ((1 / (((n + 1 : ℕ) : ℝ))) ^ (3 / 2 : ℝ) *
        (2 * Real.pi * ((n + 2 : ℕ) : ℝ) ^ 5))
  have hM : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg h15ThreeHalfFrequencyConstant_nonneg
      (mul_nonneg (Real.rpow_nonneg (by positivity) _) (by positivity))
  have htail := h15ThreeHalfShiftedFrequencyTail_le_polynomial n
  have hmul := mul_le_mul_of_nonneg_left htail hM
  have hfinal := mul_le_mul_of_nonneg_right hmul
    h15ThreeHalfVerticalProfileMass_nonneg
  exact (h15ThreeHalfUltraHighCoupledBudget_le_polynomial n
      (h15PolynomialFrequencyExponent n)).trans (by simpa [M] using hfinal)

/-- The same polynomial-cutoff bound controls the actual finite-height
integrated remainder, uniformly in the nonnegative height. -/
theorem norm_h15ThreeHalfHighFrequencyIntegralRemainder_le_polynomialCutoff
    (n : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    ‖h15ThreeHalfHighFrequencyIntegralRemainder n
        (2 ^ h15PolynomialFrequencyExponent n - 1) T‖ ≤
      h15ThreeHalfFrequencyConstant *
        ((1 / (((n + 1 : ℕ) : ℝ))) ^ (3 / 2 : ℝ) *
          (2 * Real.pi * ((n + 2 : ℕ) : ℝ) ^ 5)) *
        (40 * (((n + 2 : ℕ) : ℝ) ^ (-10 : ℝ)) *
          (1 - (2 : ℝ) ^ (-1 / 4 : ℝ))⁻¹) *
        h15ThreeHalfVerticalProfileMass :=
  (norm_h15ThreeHalfHighFrequencyIntegralRemainder_le_budget
      n (h15PolynomialFrequencyExponent n) T hT).trans
    (h15ThreeHalfUltraHighCoupledBudget_le_polynomialCutoff n)

noncomputable def h15PolynomialCutoffDecayConstant : ℝ :=
  h15ThreeHalfFrequencyConstant * (2 * Real.pi) * 40 *
    (1 - (2 : ℝ) ^ (-1 / 4 : ℝ))⁻¹ *
    h15ThreeHalfVerticalProfileMass

theorem h15PolynomialCutoffDecayConstant_nonneg :
    0 ≤ h15PolynomialCutoffDecayConstant := by
  have hrlt : (2 : ℝ) ^ (-1 / 4 : ℝ) < 1 := by
    rw [show (-1 / 4 : ℝ) = -(1 / 4 : ℝ) by ring,
      Real.rpow_neg_eq_inv_rpow]
    exact Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num)
  unfold h15PolynomialCutoffDecayConstant
  have hinv : 0 ≤ (1 - (2 : ℝ) ^ (-1 / 4 : ℝ))⁻¹ :=
    inv_nonneg.mpr (sub_nonneg.mpr hrlt.le)
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg h15ThreeHalfFrequencyConstant_nonneg (by positivity))
        (by norm_num))
      hinv)
    h15ThreeHalfVerticalProfileMass_nonneg

set_option maxHeartbeats 600000 in
/-- After combining exponents, the whole ultra-high budget is bounded by a
constant times `(n+2)⁻⁵`. -/
theorem h15ThreeHalfUltraHighCoupledBudget_le_decayPower (n : ℕ) :
    h15ThreeHalfUltraHighCoupledBudget n
        (h15PolynomialFrequencyExponent n) ≤
      h15PolynomialCutoffDecayConstant *
        (((n + 2 : ℕ) : ℝ) ^ (-5 : ℝ)) := by
  let x : ℝ := ((n + 2 : ℕ) : ℝ)
  let a : ℝ := (1 / (((n + 1 : ℕ) : ℝ))) ^ (3 / 2 : ℝ)
  have hxpos : 0 < x := by dsimp [x]; positivity
  have hbase0 : 0 ≤ 1 / (((n + 1 : ℕ) : ℝ)) := by positivity
  have hbase1 : 1 / (((n + 1 : ℕ) : ℝ)) ≤ 1 := by
    exact (div_le_one (by positivity)).2 (by norm_num)
  have ha : a ≤ 1 := by
    dsimp [a]
    exact Real.rpow_le_one hbase0 hbase1 (by norm_num)
  have hxcombine : x ^ 5 * x ^ (-10 : ℝ) = x ^ (-5 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_add hxpos]
    norm_num
  have hbound := h15ThreeHalfUltraHighCoupledBudget_le_polynomialCutoff n
  have hrearrange :
      h15ThreeHalfFrequencyConstant *
          (a * (2 * Real.pi * x ^ 5)) *
          (40 * x ^ (-10 : ℝ) *
            (1 - (2 : ℝ) ^ (-1 / 4 : ℝ))⁻¹) *
          h15ThreeHalfVerticalProfileMass =
        h15PolynomialCutoffDecayConstant * a * x ^ (-5 : ℝ) := by
    unfold h15PolynomialCutoffDecayConstant
    rw [← hxcombine]
    ring
  have hC : 0 ≤ h15PolynomialCutoffDecayConstant :=
    h15PolynomialCutoffDecayConstant_nonneg
  have hxneg : 0 ≤ x ^ (-5 : ℝ) := Real.rpow_nonneg hxpos.le _
  calc
    h15ThreeHalfUltraHighCoupledBudget n
        (h15PolynomialFrequencyExponent n) ≤
        h15ThreeHalfFrequencyConstant *
          (a * (2 * Real.pi * x ^ 5)) *
          (40 * x ^ (-10 : ℝ) *
            (1 - (2 : ℝ) ^ (-1 / 4 : ℝ))⁻¹) *
          h15ThreeHalfVerticalProfileMass := by
      simpa [a, x] using hbound
    _ = h15PolynomialCutoffDecayConstant * a * x ^ (-5 : ℝ) := hrearrange
    _ ≤ h15PolynomialCutoffDecayConstant * 1 * x ^ (-5 : ℝ) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ha hC) hxneg
    _ = h15PolynomialCutoffDecayConstant *
        (((n + 2 : ℕ) : ℝ) ^ (-5 : ℝ)) := by simp [x]

/-- The complete ultra-high H15 budget vanishes along the explicit polynomial
cutoff. -/
theorem tendsto_h15ThreeHalfUltraHighCoupledBudget_polynomialCutoff_zero :
    Tendsto (fun n : ℕ =>
      h15ThreeHalfUltraHighCoupledBudget n
        (h15PolynomialFrequencyExponent n))
      atTop (nhds 0) := by
  have hx : Tendsto (fun n : ℕ => (((n + 2 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hdecay : Tendsto (fun n : ℕ =>
      (((n + 2 : ℕ) : ℝ) ^ (-5 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (show (0 : ℝ) < 5 by norm_num)).comp hx
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n =>
      h15ThreeHalfUltraHighCoupledBudget_nonneg n
        (h15PolynomialFrequencyExponent n)
  · exact Filter.Eventually.of_forall
      h15ThreeHalfUltraHighCoupledBudget_le_decayPower
  · simpa using
      (show Tendsto (fun _ : ℕ => h15PolynomialCutoffDecayConstant) atTop
          (nhds h15PolynomialCutoffDecayConstant) from tendsto_const_nhds).mul
        hdecay

/-- Hence the actual integrated ultra-high remainder vanishes for every
possibly moving nonnegative contour height.  The estimate is uniform in that
height because the right-hand side is the height-free coupled budget. -/
theorem tendsto_norm_h15ThreeHalfHighFrequencyIntegralRemainder_polynomialCutoff_zero
    (T : ℕ → ℝ) (hT : ∀ n, 0 ≤ T n) :
    Tendsto (fun n : ℕ =>
      ‖h15ThreeHalfHighFrequencyIntegralRemainder n
        (2 ^ h15PolynomialFrequencyExponent n - 1) (T n)‖)
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
  · exact Filter.Eventually.of_forall fun n =>
      norm_h15ThreeHalfHighFrequencyIntegralRemainder_le_budget
        n (h15PolynomialFrequencyExponent n) (T n) (hT n)
  · exact tendsto_h15ThreeHalfUltraHighCoupledBudget_polynomialCutoff_zero

/-! ## Exact splitting of the finite middle window -/

/-- The finite integrated frequency window `K < r ≤ K + J`, with the full
signed H15 row family retained inside the sum. -/
noncomputable def h15BettinChandeeMiddleFrequencyIntegral
    (n K J : ℕ) (T : ℝ) : ℂ :=
  h15BettinChandeeFiniteIntegratedHigh n K J T

/-- The finite middle window is exactly the sum of the already-defined
five-coordinate Bettin--Chandee dyadic fibers. -/
theorem h15BettinChandeeMiddleFrequencyIntegral_eq_dyadicBlocks
    (n K J : ℕ) (T : ℝ) :
    h15BettinChandeeMiddleFrequencyIntegral n K J T =
      ∑ key ∈ h15BettinChandeeDyadicKeys (NB8.logTaperLength n) K J,
        h15BettinChandeeIntegratedDyadicBlock n K J T key := by
  exact (sum_h15BettinChandeeIntegratedDyadicBlocks n K J T).symm

/-- Consequently a finite dyadic block estimate can be summed without any
additional reindexing loss.  The triangle inequality is recorded here only
as the interface for applying the published trilinear theorem blockwise; it
is not used on the correction-coupled low sector. -/
theorem norm_h15BettinChandeeMiddleFrequencyIntegral_le_sum_blocks
    (n K J : ℕ) (T : ℝ) :
    ‖h15BettinChandeeMiddleFrequencyIntegral n K J T‖ ≤
      ∑ key ∈ h15BettinChandeeDyadicKeys (NB8.logTaperLength n) K J,
        ‖h15BettinChandeeIntegratedDyadicBlock n K J T key‖ := by
  rw [h15BettinChandeeMiddleFrequencyIntegral_eq_dyadicBlocks]
  exact norm_sum_le _ _

/-- Splitting a genuine exchanged high remainder after its first `J`
frequencies leaves the high remainder beginning at `K + J + 1`.

This is the exact infinite-series identity needed to ensure that the middle
window is not merely a finite model for the H15 right edge. -/
theorem h15ThreeHalfHighFrequencyIntegralRemainder_eq_middle_add_high
    (n K J : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    h15ThreeHalfHighFrequencyIntegralRemainder n K T =
      h15BettinChandeeMiddleFrequencyIntegral n K J T +
        h15ThreeHalfHighFrequencyIntegralRemainder n (K + J) T := by
  rw [h15ThreeHalfHighFrequencyIntegralRemainder_eq_sum_tsum n K T hT,
    h15ThreeHalfHighFrequencyIntegralRemainder_eq_sum_tsum n (K + J) T hT]
  unfold h15BettinChandeeMiddleFrequencyIntegral
  rw [h15BettinChandeeFiniteIntegratedHigh_eq_row_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  let f : ℕ → ℂ := fun j =>
    ∫ t : ℝ in -T..T,
      bblsActiveThreeHalfFrequencyTerm (h15ContourDamping n)
        (h15LaurentRow i).numerator
        (h15LaurentRow i).denominator
        (h15LaurentRow i).coprime (j + (K + 1)) t
  have hf : Summable f := by
    simpa only [f] using
      summable_intervalIntegral_bblsActiveThreeHalfFrequencyTerm
        n i K T hT
  have hsplit := hf.sum_add_tsum_nat_add J
  calc
    h15LaurentRowWeight i * (∑' j : ℕ, f j) =
        h15LaurentRowWeight i *
          ((∑ j ∈ Finset.range J, f j) + ∑' j : ℕ, f (j + J)) := by
            rw [hsplit]
    _ = h15LaurentRowWeight i * (∑ j ∈ Finset.range J, f j) +
        h15LaurentRowWeight i * (∑' j : ℕ, f (j + J)) := by ring
    _ = h15LaurentRowWeight i *
          (∑ j ∈ Finset.range J,
            ∫ t : ℝ in -T..T,
              bblsActiveThreeHalfFrequencyTerm (h15ContourDamping n)
                (h15LaurentRow i).numerator
                (h15LaurentRow i).denominator
                (h15LaurentRow i).coprime (j + (K + 1)) t) +
        h15LaurentRowWeight i *
          (∑' j : ℕ,
            ∫ t : ℝ in -T..T,
              bblsActiveThreeHalfFrequencyTerm (h15ContourDamping n)
                (h15LaurentRow i).numerator
                (h15LaurentRow i).denominator
                (h15LaurentRow i).coprime (j + ((K + J) + 1)) t) := by
          congr 2
          apply tsum_congr
          intro j
          simp only [f]
          congr 3
          simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-! ## Correction-preserving three-sector decomposition -/

/-- The middle-window contribution to the corrected right edge.  It has no
residue term: the complete correction remains attached to the low sector. -/
noncomputable def h15BettinChandeeMiddleFrequencyRightEdge
    (n K J : ℕ) (T : ℝ) : ℂ :=
  I * h15BettinChandeeMiddleFrequencyIntegral n K J T

/-- Exact low/middle/ultra-high decomposition of the corrected three-halves
right edge.  The residue ledger occurs exactly once, in the first term. -/
theorem h15CorrectedThreeHalfRightEdge_eq_low_add_middle_add_high
    (n K J : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    h15CorrectedThreeHalfRightEdge n T =
      h15CorrectionCoupledLowFrequencyRightEdge n K T +
        h15BettinChandeeMiddleFrequencyRightEdge n K J T +
          h15HighFrequencyRightEdgeRemainder n (K + J) T := by
  rw [h15CorrectedThreeHalfRightEdge_eq_low_add_high n K T]
  unfold h15HighFrequencyRightEdgeRemainder
  rw [h15ThreeHalfHighFrequencyIntegralRemainder_eq_middle_add_high
    n K J T hT]
  unfold h15BettinChandeeMiddleFrequencyRightEdge
  ring

/-! ## Canonical polynomial window -/

/-- The first frequency beyond the correction-coupled low sector.  Choosing
the full log-taper length corresponds to the safe Bettin--Chandee scale
`R=N`, strictly beyond the no-epsilon threshold `N^(3/4)`. -/
def h15CanonicalMiddleLowerCutoff (n : ℕ) : ℕ :=
  NB8.logTaperLength n

/-- The lower endpoint is exactly the canonical Bettin--Chandee cutoff with
the fixed positive margin `eta = 1/4`; it is not an unrelated auxiliary
scale. -/
theorem h15BettinChandeeFrequencyCutoff_one_quarter_eq (n : ℕ) :
    h15BettinChandeeFrequencyCutoff (1 / 4 : ℝ) n =
      h15CanonicalMiddleLowerCutoff n := by
  unfold h15BettinChandeeFrequencyCutoff
    h15CanonicalMiddleLowerCutoff
  norm_num

/-- Last frequency before the proved polynomial ultra-high tail begins. -/
def h15CanonicalMiddleUpperCutoff (n : ℕ) : ℕ :=
  2 ^ h15PolynomialFrequencyExponent n - 1

/-- The canonical polynomial upper cutoff lies beyond the safe lower cutoff. -/
theorem h15CanonicalMiddleLowerCutoff_le_upper (n : ℕ) :
    h15CanonicalMiddleLowerCutoff n ≤ h15CanonicalMiddleUpperCutoff n := by
  let N : ℕ := n + 2
  let J : ℕ := h15PolynomialFrequencyExponent n
  have hN : 1 < N := by dsimp [N]; omega
  have hpow : N ^ 1 < N ^ 40 :=
    Nat.pow_lt_pow_right hN (by omega)
  have hclog : N ^ 40 ≤ 2 ^ J := by
    dsimp [J, h15PolynomialFrequencyExponent, N]
    exact Nat.le_pow_clog (by norm_num) ((n + 2) ^ 40)
  have hlt : N < 2 ^ J := by simpa using hpow.trans_le hclog
  dsimp [h15CanonicalMiddleLowerCutoff,
    h15CanonicalMiddleUpperCutoff, NB8.logTaperLength, N, J] at *
  omega

/-- Number of frequencies in the canonical finite middle window. -/
def h15CanonicalMiddleWindowLength (n : ℕ) : ℕ :=
  h15CanonicalMiddleUpperCutoff n - h15CanonicalMiddleLowerCutoff n

theorem h15CanonicalMiddleLower_add_length (n : ℕ) :
    h15CanonicalMiddleLowerCutoff n + h15CanonicalMiddleWindowLength n =
      h15CanonicalMiddleUpperCutoff n := by
  unfold h15CanonicalMiddleWindowLength
  exact Nat.add_sub_of_le (h15CanonicalMiddleLowerCutoff_le_upper n)

/-- The exact canonical low/middle/ultra-high decomposition.  The last term
is precisely the remainder whose norm has already been proved to tend to
zero for arbitrary moving nonnegative contour height. -/
theorem h15CorrectedThreeHalfRightEdge_eq_canonical_three_sector
    (n : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    h15CorrectedThreeHalfRightEdge n T =
      h15CorrectionCoupledLowFrequencyRightEdge n
          (h15CanonicalMiddleLowerCutoff n) T +
        h15BettinChandeeMiddleFrequencyRightEdge n
          (h15CanonicalMiddleLowerCutoff n)
          (h15CanonicalMiddleWindowLength n) T +
        h15HighFrequencyRightEdgeRemainder n
          (h15CanonicalMiddleUpperCutoff n) T := by
  simpa [h15CanonicalMiddleLower_add_length n] using
    h15CorrectedThreeHalfRightEdge_eq_low_add_middle_add_high n
      (h15CanonicalMiddleLowerCutoff n)
      (h15CanonicalMiddleWindowLength n) T hT

/-- Canonical finite-window dyadic reassembly in the precise normalization
consumed by the next Bettin--Chandee block estimate. -/
theorem h15CanonicalMiddleFrequencyIntegral_eq_dyadicBlocks
    (n : ℕ) (T : ℝ) :
    h15BettinChandeeMiddleFrequencyIntegral n
        (h15CanonicalMiddleLowerCutoff n)
        (h15CanonicalMiddleWindowLength n) T =
      ∑ key ∈ h15BettinChandeeDyadicKeys (NB8.logTaperLength n)
          (h15CanonicalMiddleLowerCutoff n)
          (h15CanonicalMiddleWindowLength n),
        h15BettinChandeeIntegratedDyadicBlock n
          (h15CanonicalMiddleLowerCutoff n)
          (h15CanonicalMiddleWindowLength n) T key :=
  h15BettinChandeeMiddleFrequencyIntegral_eq_dyadicBlocks _ _ _ _

/-! ## Exact remaining analytic interfaces -/

/-- The finite signed Bettin--Chandee middle window vanishes along a chosen
nonnegative contour-height schedule. -/
def H15BettinChandeeMiddleWindowDecay (T : ℕ → ℝ) : Prop :=
  Tendsto (fun n : ℕ =>
    h15BettinChandeeMiddleFrequencyRightEdge n
      (h15CanonicalMiddleLowerCutoff n)
      (h15CanonicalMiddleWindowLength n) (T n))
    atTop (nhds 0)

/-- The complete correction-coupled low sector vanishes.  This interface is
deliberately aggregate-level: it does not ask individual low modes or the
residue correction to be small separately. -/
def H15CorrectionCoupledLowFrequencyDecay (T : ℕ → ℝ) : Prop :=
  Tendsto (fun n : ℕ =>
    h15CorrectionCoupledLowFrequencyRightEdge n
      (h15CanonicalMiddleLowerCutoff n) (T n))
    atTop (nhds 0)

/-- Once the two remaining signed sectors decay, the already-proved
polynomial ultra-high estimate closes the complete corrected right edge. -/
theorem tendsto_h15CorrectedThreeHalfRightEdge_zero_of_middle_of_low
    (T : ℕ → ℝ) (hT : ∀ n, 0 ≤ T n)
    (Hmiddle : H15BettinChandeeMiddleWindowDecay T)
    (Hlow : H15CorrectionCoupledLowFrequencyDecay T) :
    Tendsto (fun n : ℕ => h15CorrectedThreeHalfRightEdge n (T n))
      atTop (nhds 0) := by
  have HhighNorm : Tendsto (fun n : ℕ =>
      ‖h15HighFrequencyRightEdgeRemainder n
        (h15CanonicalMiddleUpperCutoff n) (T n)‖) atTop (nhds 0) := by
    simpa [h15HighFrequencyRightEdgeRemainder,
      h15CanonicalMiddleUpperCutoff, norm_mul] using
      tendsto_norm_h15ThreeHalfHighFrequencyIntegralRemainder_polynomialCutoff_zero
        T hT
  have Hhigh : Tendsto (fun n : ℕ =>
      h15HighFrequencyRightEdgeRemainder n
        (h15CanonicalMiddleUpperCutoff n) (T n)) atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr HhighNorm
  have Hsum := Hlow.add Hmiddle |>.add Hhigh
  have heq : (fun n : ℕ => h15CorrectedThreeHalfRightEdge n (T n)) =
      fun n : ℕ =>
        h15CorrectionCoupledLowFrequencyRightEdge n
            (h15CanonicalMiddleLowerCutoff n) (T n) +
          h15BettinChandeeMiddleFrequencyRightEdge n
            (h15CanonicalMiddleLowerCutoff n)
            (h15CanonicalMiddleWindowLength n) (T n) +
          h15HighFrequencyRightEdgeRemainder n
            (h15CanonicalMiddleUpperCutoff n) (T n) := by
    funext n
    exact h15CorrectedThreeHalfRightEdge_eq_canonical_three_sector
      n (T n) (hT n)
  rw [heq]
  simpa using Hsum

end NBMellinTools.NB12
