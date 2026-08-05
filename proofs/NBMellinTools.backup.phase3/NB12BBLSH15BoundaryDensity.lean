/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15NormalizedModulusAverage

/-!
# NB12zk: progression-density refinement of the normalized boundary

The crude normalized-superperiod boundary estimate counted every point in
two intervals of length `L*q`, producing `2*L*q`.  Actual boundary points
satisfy `L | u`.  Dividing by `L` shows that each endpoint contains at most
`q+1` relevant points, independently of `L`.

This removes the normalized-modulus factor from the pointwise endpoint
budget.  The subsequent absolute active-divisor sum nevertheless grows like
`U` on balanced blocks, so signed coupling is still required.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius
open Complex

namespace NBMellinTools.NB12

/-! ## Multiples in a short interval -/

def h15MultiplesInInterval (a b L : ℕ) : Finset ℕ :=
  (Finset.Ico a b).filter fun u => L ∣ u

/-- An interval of length at most `L*q` contains at most `q+1` multiples of
positive `L`. -/
theorem card_h15MultiplesInInterval_le
    {a b L q : ℕ} (hL : 0 < L) (hab : b ≤ a + L * q) :
    (h15MultiplesInInterval a b L).card ≤ q + 1 := by
  let t := Finset.Icc (a / L) (a / L + q)
  calc
    (h15MultiplesInInterval a b L).card ≤ t.card := by
      apply Finset.card_le_card_of_injOn (fun u => u / L)
      · intro u hu
        have hu' := Finset.mem_filter.mp hu
        have huRange := Finset.mem_Ico.mp hu'.1
        apply Finset.mem_Icc.mpr
        constructor
        · exact Nat.div_le_div_right huRange.1
        · calc
            u / L ≤ (a + L * q) / L :=
              Nat.div_le_div_right (huRange.2.le.trans hab)
            _ = a / L + q := Nat.add_mul_div_left a q hL
      · intro u hu v hv huv
        have huDvd := (Finset.mem_filter.mp hu).2
        have hvDvd := (Finset.mem_filter.mp hv).2
        change u / L = v / L at huv
        calc
          u = L * (u / L) := (Nat.mul_div_cancel' huDvd).symm
          _ = L * (v / L) := congrArg (fun n => L * n) huv
          _ = v := Nat.mul_div_cancel' hvDvd
    _ ≤ q + 1 := by
      dsimp [t]
      rw [Nat.card_Icc]
      omega

/-! ## Density-refined boundary support -/

def h15NormalizedBoundaryEndpointMajorant
    (U L q : ℕ) : Finset ℕ :=
  h15MultiplesInInterval U (U + L * q) L ∪
    h15MultiplesInInterval (2 * U - L * q) (2 * U) L

theorem h15NormalizedSuperperiodBoundarySupport_subset_densityMajorant
    (U L q : ℕ) (hLq : 0 < L * q) :
    h15NormalizedSuperperiodBoundarySupport U L q ⊆
      h15NormalizedBoundaryEndpointMajorant U L q := by
  intro u hu
  have huEndpoints :=
    h15NormalizedSuperperiodBoundarySupport_subset_endpointIntervals
      U L q hLq hu
  have huDvd := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hu).1).2
  rcases Finset.mem_union.mp huEndpoints with hleft | hright
  · apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨hleft, huDvd⟩
  · apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨hright, huDvd⟩

/-- The true endpoint support has cardinality independent of `L`. -/
theorem card_h15NormalizedSuperperiodBoundarySupport_le_density
    (U L q : ℕ) (hL : 0 < L) (hq : 0 < q) :
    (h15NormalizedSuperperiodBoundarySupport U L q).card ≤
      2 * (q + 1) := by
  calc
    (h15NormalizedSuperperiodBoundarySupport U L q).card ≤
        (h15NormalizedBoundaryEndpointMajorant U L q).card :=
      Finset.card_le_card
        (h15NormalizedSuperperiodBoundarySupport_subset_densityMajorant
          U L q (Nat.mul_pos hL hq))
    _ ≤ (h15MultiplesInInterval U (U + L * q) L).card +
        (h15MultiplesInInterval (2 * U - L * q) (2 * U) L).card :=
      Finset.card_union_le _ _
    _ ≤ (q + 1) + (q + 1) := by
      apply Nat.add_le_add
      · exact card_h15MultiplesInInterval_le hL (by omega)
      · exact card_h15MultiplesInInterval_le hL (by omega)
    _ = 2 * (q + 1) := by omega

/-- Density-refined smooth endpoint estimate for one normalized row. -/
theorem abs_h15DyadicNormalizedSuperperiodBoundaryDefect_smooth_le_density
    {N g r d U L q : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g)
    (hU : 0 < U) (hL : 0 < L) (hq : 0 < q) :
    |h15DyadicNormalizedSuperperiodBoundaryDefect r U L q
        (h15NormalizedProgressionSmoothWeight N g d)| ≤
      (2 * (q + 1) : ℝ) * (1 / (U : ℝ)) ^ 2 := by
  unfold h15DyadicNormalizedSuperperiodBoundaryDefect
  calc
    |∑ u ∈ h15NormalizedSuperperiodBoundarySupport U L q,
        h15NormalizedProgressionSmoothWeight N g d u *
          h15PairedDirectCrossMode r u q| ≤
      ∑ u ∈ h15NormalizedSuperperiodBoundarySupport U L q,
        |h15NormalizedProgressionSmoothWeight N g d u *
          h15PairedDirectCrossMode r u q| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _u ∈ h15NormalizedSuperperiodBoundarySupport U L q,
        (1 / (U : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro u hu
      rw [abs_mul]
      calc
        |h15NormalizedProgressionSmoothWeight N g d u| *
            |h15PairedDirectCrossMode r u q| ≤
          (1 / (U : ℝ)) ^ 2 * 1 :=
            mul_le_mul
              (abs_h15NormalizedProgressionSmoothWeight_le_of_mem
                hN hg hU (Finset.mem_sdiff.mp hu).1)
              (abs_h15PairedDirectCrossMode_le_one r u q hq)
              (abs_nonneg _) (by positivity)
        _ = (1 / (U : ℝ)) ^ 2 := mul_one _
    _ = ((h15NormalizedSuperperiodBoundarySupport U L q).card : ℝ) *
        (1 / (U : ℝ)) ^ 2 := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * (q + 1) : ℝ) * (1 / (U : ℝ)) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_h15NormalizedSuperperiodBoundarySupport_le_density
        U L q hL hq

/-! ## Revised global exponent audit -/

noncomputable def h15NormalizedSuperperiodDensityBoundaryBudget
    (U q : ℕ) : ℝ :=
  (2 * (q + 1) : ℝ) * (1 / (U : ℝ)) ^ 2

theorem card_h15DyadicActivePeriodSquareDivisorIndices_le
    {g U q : ℕ} (hg : 0 < g) (hU : 0 < U) :
    ((h15DyadicActivePeriodSquareDivisorIndices g U q).card : ℝ) ≤
      (2 * U : ℝ) * (g.divisors.card : ℝ) := by
  have hfiber := sum_h15DyadicActive_eq_normalizedModulusFibers
    g U q (fun _ => (1 : ℝ))
  have hfiber' :
      ((h15DyadicActivePeriodSquareDivisorIndices g U q).card : ℝ) =
        ∑ L ∈ h15ActiveNormalizedModuli g U q,
          ((h15ActiveNormalizedModulusFiber g U q L).card : ℝ) := by
    simpa [Finset.sum_const, nsmul_eq_mul] using hfiber
  rw [hfiber']
  calc
    (∑ L ∈ h15ActiveNormalizedModuli g U q,
        ((h15ActiveNormalizedModulusFiber g U q L).card : ℝ)) ≤
      ∑ _L ∈ h15ActiveNormalizedModuli g U q,
        (g.divisors.card : ℝ) := by
          apply Finset.sum_le_sum
          intro L _
          exact_mod_cast card_h15ActiveNormalizedModulusFiber_le_divisors
            (U := U) (q := q) (L := L) hg
    _ = ((h15ActiveNormalizedModuli g U q).card : ℝ) *
        (g.divisors.card : ℝ) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * U : ℝ) * (g.divisors.card : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_h15ActiveNormalizedModuli_le hg hU

noncomputable def h15NormalizedDensityBoundaryRowBudget
    (g U q : ℕ) : ℝ :=
  ∑ _d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
    h15NormalizedSuperperiodDensityBoundaryBudget U q

theorem h15NormalizedDensityBoundaryRowBudget_le
    {g U q : ℕ} (hg : 0 < g) (hU : 0 < U) :
    h15NormalizedDensityBoundaryRowBudget g U q ≤
      4 * (g.divisors.card : ℝ) * ((q : ℝ) + 1) / (U : ℝ) := by
  unfold h15NormalizedDensityBoundaryRowBudget
    h15NormalizedSuperperiodDensityBoundaryBudget
  rw [show (∑ _d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
      (2 * (q + 1) : ℝ) * (1 / (U : ℝ)) ^ 2) =
    ((h15DyadicActivePeriodSquareDivisorIndices g U q).card : ℝ) *
      ((2 * (q + 1) : ℝ) * (1 / (U : ℝ)) ^ 2) by
        simp [Finset.sum_const, nsmul_eq_mul]]
  have hcard := card_h15DyadicActivePeriodSquareDivisorIndices_le
    (q := q) hg hU
  calc
    ((h15DyadicActivePeriodSquareDivisorIndices g U q).card : ℝ) *
        ((2 * (q + 1) : ℝ) * (1 / (U : ℝ)) ^ 2) ≤
      ((2 * U : ℝ) * (g.divisors.card : ℝ)) *
        ((2 * (q + 1) : ℝ) * (1 / (U : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 4 * (g.divisors.card : ℝ) * ((q : ℝ) + 1) / (U : ℝ) := by
      have hU0 : (U : ℝ) ≠ 0 := by positivity
      field_simp
      ring

noncomputable def h15NormalizedDensityBoundaryAbsoluteBudget
    (N g U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    h15NormalizedDensityBoundaryRowBudget g U q

/-- After exploiting progression density, the absolute block grows only
linearly rather than quadratically on `Q=U`; it still does not decay. -/
theorem h15NormalizedDensityBoundaryAbsoluteBudget_le
    {N g U Q : ℕ} (hg : 0 < g) (hU : 0 < U)
    (hQU : Q ≤ U) :
    h15NormalizedDensityBoundaryAbsoluteBudget N g U Q ≤
      8 * (g.divisors.card : ℝ) * (Q : ℝ) := by
  unfold h15NormalizedDensityBoundaryAbsoluteBudget
  calc
    (∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        h15NormalizedDensityBoundaryRowBudget g U q) ≤
      ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        4 * (g.divisors.card : ℝ) * ((q : ℝ) + 1) / (U : ℝ) := by
          apply Finset.sum_le_sum
          intro q _
          exact h15NormalizedDensityBoundaryRowBudget_le hg hU
    _ ≤ ∑ _q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        8 * (g.divisors.card : ℝ) := by
          apply Finset.sum_le_sum
          intro q hq
          have hqBounds := mem_h15BettinChandeeSupportedNatBlock.mp hq
          have hqOne : ((q : ℝ) + 1) ≤ 2 * (U : ℝ) := by
            exact_mod_cast (hqBounds.2.1.trans_le
              (Nat.mul_le_mul_left 2 hQU))
          have hUreal : 0 < (U : ℝ) := by positivity
          apply (div_le_iff₀ hUreal).2
          nlinarith [show 0 ≤ (g.divisors.card : ℝ) by positivity]
    _ = ((h15BettinChandeeSupportedNatBlock N g Q).card : ℝ) *
        (8 * (g.divisors.card : ℝ)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Q : ℝ) * (8 * (g.divisors.card : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_h15BettinChandeeSupportedNatBlock_le N g Q
    _ = 8 * (g.divisors.card : ℝ) * (Q : ℝ) := by ring

theorem h15NormalizedDensityBoundaryAbsoluteBudget_balanced_le
    {N g U : ℕ} (hg : 0 < g) (hU : 0 < U) :
    h15NormalizedDensityBoundaryAbsoluteBudget N g U U ≤
      8 * (g.divisors.card : ℝ) * (U : ℝ) :=
  h15NormalizedDensityBoundaryAbsoluteBudget_le hg hU le_rfl

noncomputable def h15NormalizedDensityBoundaryAbsoluteBalancedExponent : ℝ := 1

theorem h15NormalizedDensityBoundaryAbsoluteBalancedExponent_not_neg :
    ¬ h15NormalizedDensityBoundaryAbsoluteBalancedExponent < 0 := by
  norm_num [h15NormalizedDensityBoundaryAbsoluteBalancedExponent]

end NBMellinTools.NB12
