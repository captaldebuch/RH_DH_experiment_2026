/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15NormalizedSuperperiod

/-!
# NB12zj: active normalized-modulus average and boundary stop test

The normalized `L*q` completion leaves the absolute endpoint budget
`2*L*q/U^2`, where `L=d^2/gcd(d^2,g)`.  This file reindexes the active
divisor family by `L` and audits that budget before any signed estimate is
invoked.

Every active modulus satisfies `2 <= L < 2*U` and `Coprime L q`.  For fixed
`L`, the map `d |-> gcd(d^2,g)` is injective, so the fiber has cardinality at
most the number of divisors of `g`.  These facts are unconditional finite
arithmetic.  Their resulting absolute bound grows on balanced blocks; hence
the endpoint ledger cannot be closed by this multiplicity estimate alone.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius
open Complex

namespace NBMellinTools.NB12

/-! ## Active normalized moduli and fibers -/

def h15ActiveNormalizedModuli
    (g U q : ℕ) : Finset ℕ :=
  (h15DyadicActivePeriodSquareDivisorIndices g U q).image fun d =>
    h15SquareDivisorProgressionModulus g d

def h15ActiveNormalizedModulusFiber
    (g U q L : ℕ) : Finset ℕ :=
  (h15DyadicActivePeriodSquareDivisorIndices g U q).filter fun d =>
    h15SquareDivisorProgressionModulus g d = L

theorem mem_h15ActiveNormalizedModuli
    {g U q L : ℕ} :
    L ∈ h15ActiveNormalizedModuli g U q ↔
      ∃ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
        h15SquareDivisorProgressionModulus g d = L := by
  simp [h15ActiveNormalizedModuli]

theorem mem_h15ActiveNormalizedModulusFiber
    {g U q L d : ℕ} :
    d ∈ h15ActiveNormalizedModulusFiber g U q L ↔
      d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q ∧
        h15SquareDivisorProgressionModulus g d = L := by
  simp [h15ActiveNormalizedModulusFiber]

/-- Every active normalized modulus occurs as a genuine divisor progression
inside `[U,2U)`. -/
theorem activeNormalizedModulus_bounds
    {g U q d : ℕ} (hg : 0 < g) (hU : 0 < U)
    (hd : d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q) :
    2 ≤ h15SquareDivisorProgressionModulus g d ∧
      h15SquareDivisorProgressionModulus g d < 2 * U ∧
      Nat.Coprime (h15SquareDivisorProgressionModulus g d) q := by
  rw [h15DyadicActivePeriodSquareDivisorIndices, Finset.mem_biUnion] at hd
  rcases hd with ⟨k, hk, hdk⟩
  have hkBounds := (Finset.mem_filter.mp hk).2
  have hdActive := mem_h15ActivePeriodSquareDivisorIndices.mp hdk
  obtain ⟨u, hu, hdu⟩ := Finset.mem_biUnion.mp hdActive.1
  have hu' := Finset.mem_filter.mp hu
  have huRange := Finset.mem_Ico.mp hu'.1
  have huPos : 0 < u := hU.trans_le (hkBounds.1.trans huRange.1)
  have hdPos := pos_of_mem_h15SquareDivisorSupport hdu
  have hgu : g * u ≠ 0 := Nat.mul_ne_zero hg.ne' huPos.ne'
  have hinc : d ^ 2 ∣ g * u :=
    (mem_h15SquareDivisorSupport_iff hgu).mp hdu
  have hLdvd : h15SquareDivisorProgressionModulus g d ∣ u :=
    (h15_sq_dvd_mul_iff_progressionModulus_dvd hdPos).mp hinc
  have hLle : h15SquareDivisorProgressionModulus g d ≤ u :=
    Nat.le_of_dvd huPos hLdvd
  refine ⟨hdActive.2.1, ?_, hdActive.2.2⟩
  exact hLle.trans_lt (huRange.2.trans_le hkBounds.2)

theorem activeNormalizedModuli_subset_Ico
    {g U q : ℕ} (hg : 0 < g) (hU : 0 < U) :
    h15ActiveNormalizedModuli g U q ⊆ Finset.Ico 2 (2 * U) := by
  intro L hL
  obtain ⟨d, hd, rfl⟩ := mem_h15ActiveNormalizedModuli.mp hL
  exact Finset.mem_Ico.mpr
    ⟨(activeNormalizedModulus_bounds hg hU hd).1,
      (activeNormalizedModulus_bounds hg hU hd).2.1⟩

theorem card_h15ActiveNormalizedModuli_le
    {g U q : ℕ} (hg : 0 < g) (hU : 0 < U) :
    (h15ActiveNormalizedModuli g U q).card ≤ 2 * U := by
  calc
    (h15ActiveNormalizedModuli g U q).card ≤
        (Finset.Ico 2 (2 * U)).card :=
      Finset.card_le_card (activeNormalizedModuli_subset_Ico hg hU)
    _ ≤ 2 * U := by simp

/-! ## Fiber multiplicity -/

theorem activeNormalizedModulusFiber_commonFactor_injective
    {g U q L : ℕ} :
    Set.InjOn (fun d => h15SquareDivisorCommonFactor g d)
      (h15ActiveNormalizedModulusFiber g U q L : Set ℕ) := by
  intro a ha b hb hab
  have ha' := mem_h15ActiveNormalizedModulusFiber.mp ha
  have hb' := mem_h15ActiveNormalizedModulusFiber.mp hb
  have haDvd := h15SquareDivisorCommonFactor_dvd_sq g a
  have hbDvd := h15SquareDivisorCommonFactor_dvd_sq g b
  apply Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0)
  calc
    a ^ 2 = h15SquareDivisorProgressionModulus g a *
        h15SquareDivisorCommonFactor g a := by
      exact (Nat.div_mul_cancel haDvd).symm
    _ = L * h15SquareDivisorCommonFactor g a := by rw [ha'.2]
    _ = L * h15SquareDivisorCommonFactor g b := by
      exact congrArg (fun c => L * c) hab
    _ = h15SquareDivisorProgressionModulus g b *
        h15SquareDivisorCommonFactor g b := by rw [hb'.2]
    _ = b ^ 2 := Nat.div_mul_cancel hbDvd

theorem card_h15ActiveNormalizedModulusFiber_le_divisors
    {g U q L : ℕ} (hg : 0 < g) :
    (h15ActiveNormalizedModulusFiber g U q L).card ≤ g.divisors.card := by
  apply Finset.card_le_card_of_injOn
    (fun d => h15SquareDivisorCommonFactor g d)
  · intro d hd
    exact Nat.mem_divisors.mpr
      ⟨h15SquareDivisorCommonFactor_dvd_g g d, hg.ne'⟩
  · exact activeNormalizedModulusFiber_commonFactor_injective

/-! ## Exact fiberwise sum -/

theorem sum_h15DyadicActive_eq_normalizedModulusFibers
    (g U q : ℕ) (F : ℕ → ℝ) :
    (∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
        F (h15SquareDivisorProgressionModulus g d)) =
      ∑ L ∈ h15ActiveNormalizedModuli g U q,
        (h15ActiveNormalizedModulusFiber g U q L).card * F L := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := h15DyadicActivePeriodSquareDivisorIndices g U q)
    (t := h15ActiveNormalizedModuli g U q)
    (g := fun d => h15SquareDivisorProgressionModulus g d)
    (fun d hd => Finset.mem_image.mpr ⟨d, hd, rfl⟩)
    (fun d => F (h15SquareDivisorProgressionModulus g d))]
  apply Finset.sum_congr rfl
  intro L hL
  rw [Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr
  · simp [h15ActiveNormalizedModulusFiber]
  · intro d hd
    have hdEq := (Finset.mem_filter.mp hd).2
    rw [hdEq]
    ring

/-! ## Absolute normalized-modulus budget -/

theorem sum_h15ActiveProgressionModulus_le
    {g U q : ℕ} (hg : 0 < g) (hU : 0 < U) :
    (∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
        (h15SquareDivisorProgressionModulus g d : ℝ)) ≤
      4 * (g.divisors.card : ℝ) * (U : ℝ) ^ 2 := by
  rw [sum_h15DyadicActive_eq_normalizedModulusFibers]
  calc
    (∑ L ∈ h15ActiveNormalizedModuli g U q,
        ((h15ActiveNormalizedModulusFiber g U q L).card : ℝ) * (L : ℝ)) ≤
      ∑ _L ∈ h15ActiveNormalizedModuli g U q,
        (g.divisors.card : ℝ) * (2 * U : ℝ) := by
          apply Finset.sum_le_sum
          intro L hL
          have hLRange := Finset.mem_Ico.mp
            (activeNormalizedModuli_subset_Ico hg hU hL)
          apply mul_le_mul
          · exact_mod_cast card_h15ActiveNormalizedModulusFiber_le_divisors
              (U := U) (q := q) (L := L) hg
          · exact_mod_cast hLRange.2.le
          · positivity
          · positivity
    _ = ((h15ActiveNormalizedModuli g U q).card : ℝ) *
        ((g.divisors.card : ℝ) * (2 * U : ℝ)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * U : ℝ) *
        ((g.divisors.card : ℝ) * (2 * U : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_h15ActiveNormalizedModuli_le hg hU
    _ = 4 * (g.divisors.card : ℝ) * (U : ℝ) ^ 2 := by ring

/-- Total absolute superperiod-boundary ledger on one modulus row. -/
noncomputable def h15NormalizedModulusBoundaryRowBudget
    (g U q : ℕ) : ℝ :=
  ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
    h15NormalizedSuperperiodBoundaryBudget U
      (h15SquareDivisorProgressionModulus g d) q

theorem h15NormalizedModulusBoundaryRowBudget_le
    {g U q : ℕ} (hg : 0 < g) (hU : 0 < U) :
    h15NormalizedModulusBoundaryRowBudget g U q ≤
      8 * (g.divisors.card : ℝ) * (q : ℝ) := by
  unfold h15NormalizedModulusBoundaryRowBudget
    h15NormalizedSuperperiodBoundaryBudget
  have hsum := sum_h15ActiveProgressionModulus_le
    (q := q) hg hU
  have hfactor : 0 ≤ (2 * (q : ℝ)) * (1 / (U : ℝ)) ^ 2 := by positivity
  calc
    (∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
        (2 * (h15SquareDivisorProgressionModulus g d * q) : ℝ) *
          (1 / (U : ℝ)) ^ 2) =
      ((2 * (q : ℝ)) * (1 / (U : ℝ)) ^ 2) *
        ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
          (h15SquareDivisorProgressionModulus g d : ℝ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro d _
            ring
    _ ≤ ((2 * (q : ℝ)) * (1 / (U : ℝ)) ^ 2) *
        (4 * (g.divisors.card : ℝ) * (U : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hsum hfactor
    _ = 8 * (g.divisors.card : ℝ) * (q : ℝ) := by
      have hU0 : (U : ℝ) ≠ 0 := by positivity
      field_simp
      ring

/-- Absolute boundary ledger over the supported dyadic modulus block. -/
noncomputable def h15NormalizedModulusBoundaryAbsoluteBudget
    (N g U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    h15NormalizedModulusBoundaryRowBudget g U q

theorem h15NormalizedModulusBoundaryAbsoluteBudget_le
    {N g U Q : ℕ} (hg : 0 < g) (hU : 0 < U) (hQ : 0 < Q) :
    h15NormalizedModulusBoundaryAbsoluteBudget N g U Q ≤
      16 * (g.divisors.card : ℝ) * (Q : ℝ) ^ 2 := by
  unfold h15NormalizedModulusBoundaryAbsoluteBudget
  calc
    (∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        h15NormalizedModulusBoundaryRowBudget g U q) ≤
      ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        8 * (g.divisors.card : ℝ) * (q : ℝ) := by
          apply Finset.sum_le_sum
          intro q _
          exact h15NormalizedModulusBoundaryRowBudget_le hg hU
    _ ≤ ∑ _q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        16 * (g.divisors.card : ℝ) * (Q : ℝ) := by
          apply Finset.sum_le_sum
          intro q hq
          have hqBounds := mem_h15BettinChandeeSupportedNatBlock.mp hq
          have hqLe : (q : ℝ) ≤ 2 * (Q : ℝ) := by
            exact_mod_cast hqBounds.2.1.le
          nlinarith [show 0 ≤ (g.divisors.card : ℝ) by positivity]
    _ = ((h15BettinChandeeSupportedNatBlock N g Q).card : ℝ) *
        (16 * (g.divisors.card : ℝ) * (Q : ℝ)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Q : ℝ) *
        (16 * (g.divisors.card : ℝ) * (Q : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_h15BettinChandeeSupportedNatBlock_le N g Q
    _ = 16 * (g.divisors.card : ℝ) * (Q : ℝ) ^ 2 := by ring

theorem h15NormalizedModulusBoundaryAbsoluteBudget_balanced_le
    {N g U : ℕ} (hg : 0 < g) (hU : 0 < U) :
    h15NormalizedModulusBoundaryAbsoluteBudget N g U U ≤
      16 * (g.divisors.card : ℝ) * (U : ℝ) ^ 2 :=
  h15NormalizedModulusBoundaryAbsoluteBudget_le hg hU hU

/-- Exponent produced by the fiber-cardinality absolute audit on balanced
blocks.  It is growth, not decay. -/
noncomputable def h15NormalizedModulusBoundaryAbsoluteBalancedExponent : ℝ := 2

theorem h15NormalizedModulusBoundaryAbsoluteBalancedExponent_not_neg :
    ¬ h15NormalizedModulusBoundaryAbsoluteBalancedExponent < 0 := by
  norm_num [h15NormalizedModulusBoundaryAbsoluteBalancedExponent]

end NBMellinTools.NB12
