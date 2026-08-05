/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15UltraHighTail

/-!
# Adaptive moving-cutoff coupling for the H15 ultra-high budget

The divisor-frequency tail proved in `NB12BBLSH15UltraHighTail` must be
multiplied by the finite arithmetic row budget on the three-halves line.
This file performs the exact stop test: for every cutoff `n`, an adaptively
chosen dyadic frequency threshold makes that complete nonnegative budget at
most `1 / (n + 1)`.  It also proves that this budget dominates the actual
finite-height integrated H15 high-frequency remainder.

The selection is unconditional because the arithmetic row family is finite
for each `n` and the dyadic frequency tail tends to zero.  It is deliberately
non-quantitative.  In particular, it does not prove that the threshold can be
chosen as a fixed power of `n`; that polynomial schedule is the remaining
compatibility condition needed to join this tail to a finite
Bettin--Chandee window.
-/

open scoped BigOperators Topology
open Filter MeasureTheory

namespace NBMellinTools.NB12

/-- The exact Archimedean constant in the bound for one paired frequency.
Unlike the complete-row constant, this does not contain a second copy of the
full divisor Dirichlet majorant. -/
noncomputable def h15ThreeHalfFrequencyConstant : ℝ :=
  4 * Real.sqrt (2 * Real.pi)

theorem h15ThreeHalfFrequencyConstant_nonneg :
    0 ≤ h15ThreeHalfFrequencyConstant := by
  unfold h15ThreeHalfFrequencyConstant
  positivity

/-- The exact absolute divisor-frequency tail beginning at `2^J`. -/
noncomputable def h15ThreeHalfShiftedFrequencyTail (J : ℕ) : ℝ :=
  ∑' j : ℕ, h15BettinChandeeFrequencyCoefficient (j + 2 ^ J)

theorem h15ThreeHalfShiftedFrequencyTail_nonneg (J : ℕ) :
    0 ≤ h15ThreeHalfShiftedFrequencyTail J := by
  unfold h15ThreeHalfShiftedFrequencyTail
  exact tsum_nonneg fun _ => h15BettinChandeeFrequencyCoefficient_nonneg _

/-- The exact shifted frequency tail tends to zero.  This is the form that
occurs in the analytic high-frequency `tsum`, so no dyadic-partition identity
is hidden in the later remainder bound. -/
theorem tendsto_h15ThreeHalfShiftedFrequencyTail_zero :
    Tendsto h15ThreeHalfShiftedFrequencyTail atTop (nhds 0) := by
  let f : ℕ → ℝ := h15BettinChandeeFrequencyCoefficient
  have hf : Summable f := by
    simpa [f, h15BettinChandeeFrequencyCoefficient] using
      summable_bblsThreeHalfDirichletMajorant
  have hpartial : Tendsto (fun K : ℕ => ∑ j ∈ Finset.range K, f j)
      atTop (nhds (∑' j, f j)) := hf.hasSum.tendsto_sum_nat
  have htail : Tendsto (fun K : ℕ => ∑' j : ℕ, f (j + K))
      atTop (nhds 0) := by
    have hsub : Tendsto (fun K : ℕ =>
        (∑' j, f j) - ∑ j ∈ Finset.range K, f j) atTop (nhds 0) := by
      simpa using
        (show Tendsto (fun _ : ℕ => ∑' j, f j) atTop
            (nhds (∑' j, f j)) from tendsto_const_nhds).sub hpartial
    apply hsub.congr'
    filter_upwards [] with K
    have hsum := hf.sum_add_tsum_nat_add K
    linarith
  have hpow : Tendsto (fun J : ℕ => 2 ^ J) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  simpa [h15ThreeHalfShiftedFrequencyTail, f] using htail.comp hpow

/-- Total mass of the common integrable vertical profile on `Re(s)=3/2`. -/
noncomputable def h15ThreeHalfVerticalProfileMass : ℝ :=
  ∫ t : ℝ, h15ThreeHalfPositiveLineRowGrowth.verticalProfile t

theorem h15ThreeHalfVerticalProfileMass_nonneg :
    0 ≤ h15ThreeHalfVerticalProfileMass := by
  unfold h15ThreeHalfVerticalProfileMass
  exact integral_nonneg fun t =>
    h15ThreeHalfPositiveLineRowGrowth.verticalProfile_nonneg t

/-! ## Domination of the actual integrated high-frequency remainder -/

/-- The global `L¹` norm of one paired frequency has the exact separated
majorant used in the coupled budget. -/
theorem integral_norm_bblsActiveThreeHalfFrequencyTerm_le
    {damping : ℝ} (hdamping : 0 < damping)
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q) (r : ℕ) :
    (∫ t : ℝ,
      ‖bblsActiveThreeHalfFrequencyTerm damping a q haq r t‖) ≤
      h15ThreeHalfFrequencyConstant * (q : ℝ) ^ 2 *
        damping ^ (3 / 2 : ℝ) *
        h15BettinChandeeFrequencyCoefficient r *
        h15ThreeHalfVerticalProfileMass := by
  let c : ℝ :=
    h15ThreeHalfFrequencyConstant * (q : ℝ) ^ 2 *
      damping ^ (3 / 2 : ℝ) *
      h15BettinChandeeFrequencyCoefficient r
  have hrow :=
    (integrable_bblsActiveThreeHalfFrequencyTerm
      hdamping a q haq r).norm
  have hmaj : Integrable (fun t : ℝ =>
      c * h15ThreeHalfPositiveLineRowGrowth.verticalProfile t) :=
    h15ThreeHalfPositiveLineRowGrowth.integrable_verticalProfile.const_mul c
  have hle :
      (∫ t : ℝ,
        ‖bblsActiveThreeHalfFrequencyTerm damping a q haq r t‖) ≤
        ∫ t : ℝ,
          c * h15ThreeHalfPositiveLineRowGrowth.verticalProfile t := by
    apply integral_mono hrow hmaj
    intro t
    simpa [c, h15ThreeHalfFrequencyConstant,
      h15BettinChandeeFrequencyCoefficient,
      H15PositiveLineRowGrowth.verticalProfile,
      h15ThreeHalfPositiveLineRowGrowth, mul_assoc] using
        norm_bblsActiveThreeHalfFrequencyTerm_le
          hdamping a q haq r t
  rw [integral_const_mul] at hle
  simpa [c, h15ThreeHalfVerticalProfileMass, mul_assoc] using hle

/-- The same bound holds on every symmetric finite contour window, uniformly
in the height. -/
theorem norm_intervalIntegral_bblsActiveThreeHalfFrequencyTerm_le
    {damping : ℝ} (hdamping : 0 < damping)
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q) (r : ℕ) (T : ℝ) :
    ‖∫ t : ℝ in -T..T,
      bblsActiveThreeHalfFrequencyTerm damping a q haq r t‖ ≤
      h15ThreeHalfFrequencyConstant * (q : ℝ) ^ 2 *
        damping ^ (3 / 2 : ℝ) *
        h15BettinChandeeFrequencyCoefficient r *
        h15ThreeHalfVerticalProfileMass := by
  calc
    ‖∫ t : ℝ in -T..T,
        bblsActiveThreeHalfFrequencyTerm damping a q haq r t‖ ≤
      ∫ t : ℝ in Set.uIoc (-T) T,
        ‖bblsActiveThreeHalfFrequencyTerm damping a q haq r t‖ :=
      intervalIntegral.norm_integral_le_integral_norm_uIoc
    _ ≤ ∫ t : ℝ,
        ‖bblsActiveThreeHalfFrequencyTerm damping a q haq r t‖ :=
      integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        (integrable_bblsActiveThreeHalfFrequencyTerm
          hdamping a q haq r).norm
    _ ≤ _ := integral_norm_bblsActiveThreeHalfFrequencyTerm_le
      hdamping a q haq r

/-- One complete shifted frequency tail in one H15 row is bounded by the
exact shifted scalar tail, uniformly in contour height. -/
theorem norm_tsum_intervalIntegral_bblsActiveThreeHalfFrequencyTerm_le
    {damping : ℝ} (hdamping : 0 < damping)
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q)
    (J : ℕ) (T : ℝ) :
    ‖∑' j : ℕ, ∫ t : ℝ in -T..T,
      bblsActiveThreeHalfFrequencyTerm damping a q haq
        (j + 2 ^ J) t‖ ≤
      h15ThreeHalfFrequencyConstant * (q : ℝ) ^ 2 *
        damping ^ (3 / 2 : ℝ) *
        h15ThreeHalfShiftedFrequencyTail J *
        h15ThreeHalfVerticalProfileMass := by
  let C : ℝ := h15ThreeHalfFrequencyConstant * (q : ℝ) ^ 2 *
    damping ^ (3 / 2 : ℝ) * h15ThreeHalfVerticalProfileMass
  have hcoeff : Summable (fun j : ℕ =>
      h15BettinChandeeFrequencyCoefficient (j + 2 ^ J)) := by
    change Summable (fun j : ℕ =>
      ‖LSeries.term bblsEstermannDivisorCoeff (3 / 2 : ℂ)
        (j + 2 ^ J)‖)
    exact summable_bblsThreeHalfDirichletMajorant.comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
  have hmajor : Summable (fun j : ℕ =>
      C * h15BettinChandeeFrequencyCoefficient (j + 2 ^ J)) :=
    hcoeff.mul_left C
  have hnorm : Summable (fun j : ℕ =>
      ‖∫ t : ℝ in -T..T,
        bblsActiveThreeHalfFrequencyTerm damping a q haq
          (j + 2 ^ J) t‖) := by
    apply hmajor.of_nonneg_of_le
    · intro j
      exact norm_nonneg _
    · intro j
      simpa [C, mul_assoc, mul_left_comm, mul_comm] using
        norm_intervalIntegral_bblsActiveThreeHalfFrequencyTerm_le
          hdamping a q haq (j + 2 ^ J) T
  calc
    ‖∑' j : ℕ, ∫ t : ℝ in -T..T,
        bblsActiveThreeHalfFrequencyTerm damping a q haq
          (j + 2 ^ J) t‖ ≤
      ∑' j : ℕ, ‖∫ t : ℝ in -T..T,
        bblsActiveThreeHalfFrequencyTerm damping a q haq
          (j + 2 ^ J) t‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' j : ℕ,
        C * h15BettinChandeeFrequencyCoefficient (j + 2 ^ J) :=
      Summable.tsum_le_tsum
        (fun j => by
          simpa [C, mul_assoc, mul_left_comm, mul_comm] using
            norm_intervalIntegral_bblsActiveThreeHalfFrequencyTerm_le
              hdamping a q haq (j + 2 ^ J) T)
        hnorm hmajor
    _ = _ := by
      rw [tsum_mul_left]
      unfold h15ThreeHalfShiftedFrequencyTail C
      ring

/-- The exact nonnegative factors left by the absolute ultra-high estimate:
the three-halves functional-equation constant, Abel damping, finite H15
arithmetic row mass, divisor-frequency tail, and vertical-profile mass. -/
noncomputable def h15ThreeHalfUltraHighCoupledBudget
    (n J : ℕ) : ℝ :=
  h15ThreeHalfFrequencyConstant *
    h15ContourDamping n ^ (3 / 2 : ℝ) *
    h15ThreeHalfPositiveLineRowGrowth.arithmeticMass n *
    h15ThreeHalfShiftedFrequencyTail J *
    h15ThreeHalfVerticalProfileMass

theorem h15BettinChandeeDyadicFrequencyTail_nonneg (J : ℕ) :
    0 ≤ h15BettinChandeeDyadicFrequencyTail J := by
  unfold h15BettinChandeeDyadicFrequencyTail
  exact tsum_nonneg fun j =>
    h15BettinChandeeFrequencyBlockL1_nonneg (2 ^ (j + J))

theorem h15ThreeHalfUltraHighCoupledBudget_nonneg (n J : ℕ) :
    0 ≤ h15ThreeHalfUltraHighCoupledBudget n J := by
  unfold h15ThreeHalfUltraHighCoupledBudget
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg
          h15ThreeHalfFrequencyConstant_nonneg
          (Real.rpow_nonneg (h15ContourDamping_pos n).le _))
        (h15ThreeHalfPositiveLineRowGrowth.arithmeticMass_nonneg n))
      (h15ThreeHalfShiftedFrequencyTail_nonneg J))
    h15ThreeHalfVerticalProfileMass_nonneg

/-- The coupled budget is not merely a scalar proxy: it uniformly dominates
the actual finite-height integrated H15 high-frequency remainder beginning at
frequency `2^J`. -/
theorem norm_h15ThreeHalfHighFrequencyIntegralRemainder_le_budget
    (n J : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    ‖h15ThreeHalfHighFrequencyIntegralRemainder n (2 ^ J - 1) T‖ ≤
      h15ThreeHalfUltraHighCoupledBudget n J := by
  classical
  rw [h15ThreeHalfHighFrequencyIntegralRemainder_eq_sum_tsum
    n (2 ^ J - 1) T hT]
  have hpow : 1 ≤ 2 ^ J := one_le_pow₀ (by norm_num)
  simp only [Nat.sub_add_cancel hpow]
  calc
    ‖∑ i : H15LaurentRowIndex (NB8.logTaperLength n),
        h15LaurentRowWeight i *
          (∑' j : ℕ, ∫ t : ℝ in -T..T,
            bblsActiveThreeHalfFrequencyTerm (h15ContourDamping n)
              (h15LaurentRow i).numerator
              (h15LaurentRow i).denominator
              (h15LaurentRow i).coprime (j + 2 ^ J) t)‖ ≤
      ∑ i : H15LaurentRowIndex (NB8.logTaperLength n),
        ‖h15LaurentRowWeight i *
          (∑' j : ℕ, ∫ t : ℝ in -T..T,
            bblsActiveThreeHalfFrequencyTerm (h15ContourDamping n)
              (h15LaurentRow i).numerator
              (h15LaurentRow i).denominator
              (h15LaurentRow i).coprime (j + 2 ^ J) t)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i : H15LaurentRowIndex (NB8.logTaperLength n),
        ‖h15LaurentRowWeight i‖ *
          (h15ThreeHalfFrequencyConstant *
            ((h15LaurentRow i).denominator : ℝ) ^ 2 *
            h15ContourDamping n ^ (3 / 2 : ℝ) *
            h15ThreeHalfShiftedFrequencyTail J *
            h15ThreeHalfVerticalProfileMass) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (norm_tsum_intervalIntegral_bblsActiveThreeHalfFrequencyTerm_le
          (h15ContourDamping_pos n)
          (h15LaurentRow i).numerator
          (h15LaurentRow i).denominator
          (h15LaurentRow i).coprime J T)
        (norm_nonneg _)
    _ = h15ThreeHalfUltraHighCoupledBudget n J := by
      unfold h15ThreeHalfUltraHighCoupledBudget
        H15PositiveLineRowGrowth.arithmeticMass
        h15ThreeHalfPositiveLineRowGrowth
      calc
        (∑ i : H15LaurentRowIndex (NB8.logTaperLength n),
          ‖h15LaurentRowWeight i‖ *
            (h15ThreeHalfFrequencyConstant *
              ((h15LaurentRow i).denominator : ℝ) ^ 2 *
              h15ContourDamping n ^ (3 / 2 : ℝ) *
              h15ThreeHalfShiftedFrequencyTail J *
              h15ThreeHalfVerticalProfileMass)) =
            (∑ i : H15LaurentRowIndex (NB8.logTaperLength n),
              ‖h15LaurentRowWeight i‖ *
                ((h15LaurentRow i).denominator : ℝ) ^ 2) *
              (h15ThreeHalfFrequencyConstant *
                h15ContourDamping n ^ (3 / 2 : ℝ) *
                h15ThreeHalfShiftedFrequencyTail J *
                h15ThreeHalfVerticalProfileMass) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by ring

/-- The same estimate controls the correction-free right-edge remainder;
multiplication by `I` does not change its norm. -/
theorem norm_h15HighFrequencyRightEdgeRemainder_le_budget
    (n J : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    ‖h15HighFrequencyRightEdgeRemainder n (2 ^ J - 1) T‖ ≤
      h15ThreeHalfUltraHighCoupledBudget n J := by
  unfold h15HighFrequencyRightEdgeRemainder
  simpa [norm_mul] using
    norm_h15ThreeHalfHighFrequencyIntegralRemainder_le_budget n J T hT

/-- For each fixed H15 cutoff, the complete coupled ultra-high budget tends
to zero as the dyadic frequency threshold tends to infinity. -/
theorem tendsto_h15ThreeHalfUltraHighCoupledBudget_fixed
    (n : ℕ) :
    Tendsto (h15ThreeHalfUltraHighCoupledBudget n) atTop (nhds 0) := by
  let C : ℝ :=
    h15ThreeHalfFrequencyConstant *
      h15ContourDamping n ^ (3 / 2 : ℝ) *
      h15ThreeHalfPositiveLineRowGrowth.arithmeticMass n
  have htail := tendsto_h15ThreeHalfShiftedFrequencyTail_zero
  have hmul : Tendsto (fun J : ℕ =>
      C * h15ThreeHalfShiftedFrequencyTail J)
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul htail)
  have hout := hmul.mul_const h15ThreeHalfVerticalProfileMass
  have hout' : Tendsto (fun J : ℕ =>
      C * h15ThreeHalfShiftedFrequencyTail J *
        h15ThreeHalfVerticalProfileMass) atTop (nhds 0) := by
    simpa using hout
  apply hout'.congr'
  filter_upwards [] with J
  unfold h15ThreeHalfUltraHighCoupledBudget C
  ring

/-- Every finite arithmetic row budget admits an arbitrarily late dyadic
frequency threshold which makes the coupled tail smaller than
`1 / (n + 1)`. -/
theorem exists_h15ThreeHalfUltraHighAdaptiveCutoff (n : ℕ) :
    ∃ J : ℕ, n ≤ J ∧
      h15ThreeHalfUltraHighCoupledBudget n J ≤
        1 / (((n + 1 : ℕ) : ℝ)) := by
  have heps : 0 < 1 / (((n + 1 : ℕ) : ℝ)) := by positivity
  have hlim := tendsto_h15ThreeHalfUltraHighCoupledBudget_fixed n
  have hevent : ∀ᶠ J : ℕ in atTop,
      h15ThreeHalfUltraHighCoupledBudget n J <
        1 / (((n + 1 : ℕ) : ℝ)) :=
    (tendsto_order.1 hlim).2 _ heps
  rcases (hevent.and (eventually_ge_atTop n)).exists with
    ⟨J, hJsmall, hnJ⟩
  exact ⟨J, hnJ, hJsmall.le⟩

/-- Canonical adaptive threshold selected from the preceding existence
theorem. -/
noncomputable def h15ThreeHalfUltraHighAdaptiveCutoff (n : ℕ) : ℕ :=
  Classical.choose (exists_h15ThreeHalfUltraHighAdaptiveCutoff n)

theorem le_h15ThreeHalfUltraHighAdaptiveCutoff (n : ℕ) :
    n ≤ h15ThreeHalfUltraHighAdaptiveCutoff n :=
  (Classical.choose_spec
    (exists_h15ThreeHalfUltraHighAdaptiveCutoff n)).1

theorem h15ThreeHalfUltraHighAdaptiveCutoff_spec (n : ℕ) :
    h15ThreeHalfUltraHighCoupledBudget n
        (h15ThreeHalfUltraHighAdaptiveCutoff n) ≤
      1 / (((n + 1 : ℕ) : ℝ)) :=
  (Classical.choose_spec
    (exists_h15ThreeHalfUltraHighAdaptiveCutoff n)).2

/-- The actual integrated high-frequency remainder is at most `1/(n+1)` at
the canonical adaptive cutoff, uniformly in every nonnegative contour
height. -/
theorem norm_h15ThreeHalfHighFrequencyIntegralRemainder_adaptive_le
    (n : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    ‖h15ThreeHalfHighFrequencyIntegralRemainder n
        (2 ^ h15ThreeHalfUltraHighAdaptiveCutoff n - 1) T‖ ≤
      1 / (((n + 1 : ℕ) : ℝ)) := by
  exact (norm_h15ThreeHalfHighFrequencyIntegralRemainder_le_budget
    n (h15ThreeHalfUltraHighAdaptiveCutoff n) T hT).trans
      (h15ThreeHalfUltraHighAdaptiveCutoff_spec n)

/-- Therefore the actual integrated H15 ultra-high remainder vanishes along
the adaptive cutoff for any nonnegative height schedule. -/
theorem tendsto_norm_h15ThreeHalfHighFrequencyIntegralRemainder_adaptive_zero
    (T : ℕ → ℝ) (hT : ∀ n, 0 ≤ T n) :
    Tendsto (fun n : ℕ =>
      ‖h15ThreeHalfHighFrequencyIntegralRemainder n
        (2 ^ h15ThreeHalfUltraHighAdaptiveCutoff n - 1) (T n)‖)
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
  · exact Filter.Eventually.of_forall fun n =>
      norm_h15ThreeHalfHighFrequencyIntegralRemainder_adaptive_le
        n (T n) (hT n)
  · simpa [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem tendsto_h15ThreeHalfUltraHighAdaptiveCutoff_atTop :
    Tendsto h15ThreeHalfUltraHighAdaptiveCutoff atTop atTop := by
  exact tendsto_atTop_mono' atTop
    (Filter.Eventually.of_forall le_h15ThreeHalfUltraHighAdaptiveCutoff)
    tendsto_id

/-- The complete coupled budget vanishes along the canonical adaptive
moving cutoff. -/
theorem tendsto_h15ThreeHalfUltraHighCoupledBudget_adaptive_zero :
    Tendsto (fun n : ℕ =>
      h15ThreeHalfUltraHighCoupledBudget n
        (h15ThreeHalfUltraHighAdaptiveCutoff n))
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n =>
      h15ThreeHalfUltraHighCoupledBudget_nonneg n
        (h15ThreeHalfUltraHighAdaptiveCutoff n)
  · exact Filter.Eventually.of_forall
      h15ThreeHalfUltraHighAdaptiveCutoff_spec
  · simpa [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

end NBMellinTools.NB12
