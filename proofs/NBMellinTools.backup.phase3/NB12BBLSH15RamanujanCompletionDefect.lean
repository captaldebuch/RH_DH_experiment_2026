/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PairedDirectKernel

/-!
# NB12ze: completion defects for the weighted H15 Ramanujan cross mode

The paired-kernel stop test reduced the possible gain from keeping both
Estermann orientations together to a signed weighted Ramanujan correlation.
This file performs the next exact finite step.

Every dyadic numerator block is partitioned into complete modulus periods and
a boundary support.  On each complete period a constant reference weight
cancels exactly, leaving only the variation of the genuine H15 weight inside
that period.  The original cross correlation is therefore the sum of exactly
two defects:

* the within-period variation defect;
* the incomplete boundary defect.

The endpoint support is then shown to have at most `2q` points, giving the
explicit H15 endpoint bound `2q/U²`.  No decay estimate for the remaining
within-period variation defect is assumed or proved.  The decomposition makes
that next analytic stop test precise without discarding endpoints or replacing
the H15 coefficient by a uniform weight.
-/

open scoped BigOperators Topology LSeries.notation
open Complex

namespace NBMellinTools.NB12

/-! ## Natural representatives of complete reduced residue systems -/

/-- Reduced natural representatives modulo `q`. -/
def h15ReducedResidues (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter fun u => Nat.Coprime u q

/-- Reindexing a reduced natural residue system by the units of `ZMod q`. -/
theorem sum_h15ReducedResidues_eq_sum_units
    {q : ℕ} [NeZero q] (F : ℕ → ℝ) :
    (∑ u ∈ h15ReducedResidues q, F u) =
      ∑ v : (ZMod q)ˣ, F (v : ZMod q).val := by
  classical
  apply Finset.sum_bij
    (fun u hu => ZMod.unitOfCoprime u (Finset.mem_filter.mp hu).2)
  · intro u hu
    simp
  · intro a ha b hb hab
    have habZ : (a : ZMod q) = (b : ZMod q) :=
      congrArg Units.val hab
    have habVal := congrArg ZMod.val habZ
    have haLt : a < q := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    have hbLt : b < q := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt haLt,
      Nat.mod_eq_of_lt hbLt] using habVal
  · intro v _
    let u : ℕ := (v : ZMod q).val
    have huLt : u < q := ZMod.val_lt (v : ZMod q)
    have huCoprime : Nat.Coprime u q := ZMod.val_coe_unit_coprime v
    refine ⟨u, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr huLt, huCoprime⟩, ?_⟩
    apply Units.ext
    exact ZMod.natCast_zmod_val (v : ZMod q)
  · intro u hu
    apply congrArg F
    have huLt : u < q := Finset.mem_range.mp (Finset.mem_filter.mp hu).1
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt huLt]

/-- The real cross mode produced by the exact paired direct-kernel norm
square. -/
noncomputable def h15PairedDirectCrossMode
    (r u q : ℕ) : ℝ :=
  ((h15DirectAdditiveReducedUnitPhase .positive r u q) ^ 2).im

/-- On a reduced positive-modulus row, the cross mode is the imaginary part
of the doubled direct additive character. -/
theorem h15PairedDirectCrossMode_of_coprime
    (r u q : ℕ) [NeZero q] (huq : Nat.Coprime u q) :
    h15PairedDirectCrossMode r u q =
      (ZMod.stdAddChar ((2 * (r : ZMod q)) * (u : ZMod q))).im := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  unfold h15PairedDirectCrossMode
  rw [h15DirectAdditiveReducedUnitPhase_of_coprime _ _ _ _ huq]
  unfold h15DirectAdditiveUnitPhase
  simp only [hq.ne', dite_false]
  rw [pow_two, ← AddChar.map_add_eq_mul]
  apply congrArg Complex.im
  apply congrArg ZMod.stdAddChar
  ring

@[simp] theorem h15PairedDirectCrossMode_of_not_coprime
    (r u q : ℕ) (huq : ¬ Nat.Coprime u q) :
    h15PairedDirectCrossMode r u q = 0 := by
  simp [h15PairedDirectCrossMode,
    h15DirectAdditiveReducedUnitPhase_of_not_coprime _ _ _ _ huq]

/-- The paired direct cross mode is pointwise bounded by one. -/
theorem abs_h15PairedDirectCrossMode_le_one
    (r u q : ℕ) (hq : 0 < q) :
    |h15PairedDirectCrossMode r u q| ≤ 1 := by
  by_cases huq : Nat.Coprime u q
  · letI : NeZero q := ⟨hq.ne'⟩
    rw [h15PairedDirectCrossMode_of_coprime r u q huq]
    calc
      |(ZMod.stdAddChar
          ((2 * (r : ZMod q)) * (u : ZMod q))).im| ≤
          ‖ZMod.stdAddChar
            ((2 * (r : ZMod q)) * (u : ZMod q))‖ :=
        Complex.abs_im_le_norm _
      _ = 1 := AddChar.norm_apply _ _
  · rw [h15PairedDirectCrossMode_of_not_coprime r u q huq, abs_zero]
    exact zero_le_one

/-- The complete natural reduced-residue cross mode vanishes. -/
theorem sum_h15ReducedResidues_crossMode_eq_zero
    (r q : ℕ) (hq : 0 < q) :
    (∑ u ∈ h15ReducedResidues q,
        h15PairedDirectCrossMode r u q) = 0 := by
  letI : NeZero q := ⟨hq.ne'⟩
  rw [sum_h15ReducedResidues_eq_sum_units]
  calc
    (∑ v : (ZMod q)ˣ,
        h15PairedDirectCrossMode r (v : ZMod q).val q) =
      ∑ v : (ZMod q)ˣ,
        ((ZMod.stdAddChar ((v : ZMod q) * (r : ZMod q)) : ℂ) ^ 2).im := by
          apply Finset.sum_congr rfl
          intro v _
          have hv := ZMod.val_coe_unit_coprime v
          rw [h15PairedDirectCrossMode_of_coprime r _ q hv]
          congr 1
          rw [ZMod.natCast_zmod_val]
          rw [pow_two, ← AddChar.map_add_eq_mul]
          apply congrArg ZMod.stdAddChar
          ring
    _ = 0 := sum_units_sq_stdAddChar_im_eq_zero (r : ZMod q)

/-! ## Complete natural periods -/

/-- The reduced natural representatives in the `k`-th complete period of
length `q`. -/
def h15ReducedNaturalPeriod (k q : ℕ) : Finset ℕ :=
  (Finset.Ico (k * q) ((k + 1) * q)).filter fun u => Nat.Coprime u q

/-- Translation by one modulus period preserves the cross mode. -/
theorem h15PairedDirectCrossMode_add_period
    (r u k q : ℕ) (hq : 0 < q) :
    h15PairedDirectCrossMode r (k * q + u) q =
      h15PairedDirectCrossMode r u q := by
  letI : NeZero q := ⟨hq.ne'⟩
  have hcop : Nat.Coprime (k * q + u) q ↔ Nat.Coprime u q := by
    rw [Nat.add_comm (k * q) u]
    exact Nat.coprime_add_mul_right_left u q k
  by_cases huq : Nat.Coprime u q
  · have hshift : Nat.Coprime (k * q + u) q := hcop.mpr huq
    rw [h15PairedDirectCrossMode_of_coprime r _ q hshift,
      h15PairedDirectCrossMode_of_coprime r u q huq]
    congr 1
    simp
  · have hshift : ¬ Nat.Coprime (k * q + u) q := by
      exact fun h => huq (hcop.mp h)
    simp [h15PairedDirectCrossMode_of_not_coprime r _ q hshift,
      h15PairedDirectCrossMode_of_not_coprime r u q huq]

/-- Every complete translated reduced-residue period has zero unweighted
cross mode. -/
theorem sum_h15ReducedNaturalPeriod_crossMode_eq_zero
    (r k q : ℕ) (hq : 0 < q) :
    (∑ u ∈ h15ReducedNaturalPeriod k q,
        h15PairedDirectCrossMode r u q) = 0 := by
  unfold h15ReducedNaturalPeriod
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_Ico_eq_sum_range]
  have hlength : (k + 1) * q - k * q = q := by
    simp [Nat.add_mul]
  rw [hlength]
  calc
    (∑ u ∈ Finset.range q,
        if Nat.Coprime (k * q + u) q then
          h15PairedDirectCrossMode r (k * q + u) q else 0) =
      ∑ u ∈ h15ReducedResidues q,
        h15PairedDirectCrossMode r u q := by
          unfold h15ReducedResidues
          simp_rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro u hu
          have hcop : Nat.Coprime (k * q + u) q ↔ Nat.Coprime u q := by
            rw [Nat.add_comm (k * q) u]
            exact Nat.coprime_add_mul_right_left u q k
          by_cases huq : Nat.Coprime u q
          · rw [if_pos (hcop.mpr huq), if_pos huq,
              h15PairedDirectCrossMode_add_period r u k q hq]
          · have hshift : ¬ Nat.Coprime (k * q + u) q :=
              fun h => huq (hcop.mp h)
            simp [huq, hshift]
    _ = 0 := sum_h15ReducedResidues_crossMode_eq_zero r q hq

/-! ## Periodwise centering -/

/-- A weighted cross mode on one complete modulus period. -/
noncomputable def h15PeriodWeightedCross
    (r k q : ℕ) (weight : ℕ → ℝ) : ℝ :=
  ∑ u ∈ h15ReducedNaturalPeriod k q,
    weight u * h15PairedDirectCrossMode r u q

/-- The same period after subtracting a constant reference weight. -/
noncomputable def h15PeriodVariationDefect
    (r k q : ℕ) (weight : ℕ → ℝ) (reference : ℝ) : ℝ :=
  ∑ u ∈ h15ReducedNaturalPeriod k q,
    (weight u - reference) * h15PairedDirectCrossMode r u q

/-- Exact constant-mode cancellation on one complete period. -/
theorem h15PeriodWeightedCross_eq_variationDefect
    (r k q : ℕ) (weight : ℕ → ℝ) (reference : ℝ) (hq : 0 < q) :
    h15PeriodWeightedCross r k q weight =
      h15PeriodVariationDefect r k q weight reference := by
  unfold h15PeriodWeightedCross h15PeriodVariationDefect
  have hzero := sum_h15ReducedNaturalPeriod_crossMode_eq_zero r k q hq
  calc
    (∑ u ∈ h15ReducedNaturalPeriod k q,
        weight u * h15PairedDirectCrossMode r u q) =
      ∑ u ∈ h15ReducedNaturalPeriod k q,
        ((weight u - reference) * h15PairedDirectCrossMode r u q +
          reference * h15PairedDirectCrossMode r u q) := by
            apply Finset.sum_congr rfl
            intro u _
            ring
    _ = (∑ u ∈ h15ReducedNaturalPeriod k q,
          (weight u - reference) * h15PairedDirectCrossMode r u q) +
        reference *
          ∑ u ∈ h15ReducedNaturalPeriod k q,
            h15PairedDirectCrossMode r u q := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by rw [hzero, mul_zero, add_zero]

/-! ## Exact dyadic completion support -/

/-- Indices of the complete modulus periods wholly contained in the dyadic
interval `[U,2U)`.  The finite ambient range is deliberately redundant; the
filter contains the exact geometric condition. -/
def h15CompletePeriodIndices (U q : ℕ) : Finset ℕ :=
  (Finset.range (2 * U + 1)).filter fun k =>
    U ≤ k * q ∧ (k + 1) * q ≤ 2 * U

/-- Union of all complete reduced-residue periods wholly contained in the
dyadic numerator block. -/
def h15CompletePeriodSupport (U q : ℕ) : Finset ℕ :=
  (h15CompletePeriodIndices U q).biUnion fun k =>
    h15ReducedNaturalPeriod k q

/-- The incomplete endpoint support left after removing every complete
modulus period. -/
def h15CompletionBoundarySupport (U q : ℕ) : Finset ℕ :=
  h15ReducedDyadicNumeratorBlock U q \ h15CompletePeriodSupport U q

/-- Distinct positive-modulus natural periods are disjoint. -/
theorem h15ReducedNaturalPeriod_pairwiseDisjoint
    (U q : ℕ) :
    Set.PairwiseDisjoint (h15CompletePeriodIndices U q : Set ℕ)
      (fun k => h15ReducedNaturalPeriod k q) := by
  intro k _ l _ hkl
  apply Finset.disjoint_left.mpr
  intro u huk hul
  have hukIco := (Finset.mem_filter.mp huk).1
  have hulIco := (Finset.mem_filter.mp hul).1
  have hkRange := Finset.mem_Ico.mp hukIco
  have hlRange := Finset.mem_Ico.mp hulIco
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · have hmul : (k + 1) * q ≤ l * q :=
      Nat.mul_le_mul_right q (Nat.succ_le_of_lt hlt)
    omega
  · have hmul : (l + 1) * q ≤ k * q :=
      Nat.mul_le_mul_right q (Nat.succ_le_of_lt hgt)
    omega

/-- Every complete-period point lies in the original reduced dyadic block. -/
theorem h15CompletePeriodSupport_subset_reducedDyadic
    (U q : ℕ) :
    h15CompletePeriodSupport U q ⊆
      h15ReducedDyadicNumeratorBlock U q := by
  intro u hu
  rw [h15CompletePeriodSupport, Finset.mem_biUnion] at hu
  rcases hu with ⟨k, hk, huk⟩
  have hkBounds := (Finset.mem_filter.mp hk).2
  have huPeriod := Finset.mem_filter.mp huk
  have huRange := Finset.mem_Ico.mp huPeriod.1
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Ico.mpr ⟨?_, ?_⟩, huPeriod.2⟩
  · exact hkBounds.1.trans huRange.1
  · exact huRange.2.trans_le hkBounds.2

/-- The completion boundary is contained in two endpoint intervals, each of
length at most one modulus. -/
theorem h15CompletionBoundarySupport_subset_endpointIntervals
    (U q : ℕ) (hq : 0 < q) :
    h15CompletionBoundarySupport U q ⊆
      Finset.Ico U (U + q) ∪ Finset.Ico (2 * U - q) (2 * U) := by
  intro u hu
  have huDiff := Finset.mem_sdiff.mp hu
  have huBlock := Finset.mem_filter.mp huDiff.1
  have huRange := Finset.mem_Ico.mp huBlock.1
  by_contra hend
  have hend' :
      ¬ (U ≤ u ∧ u < U + q) ∧
        ¬ (2 * U - q ≤ u ∧ u < 2 * U) := by
    simpa only [Finset.mem_union, Finset.mem_Ico, not_or] using hend
  have hlow : U + q ≤ u := by omega
  have hhigh : u < 2 * U - q := by omega
  let k := u / q
  have hfloor : k * q ≤ u := by
    exact Nat.div_mul_le_self u q
  have hceil : u < (k + 1) * q := by
    simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ u hq
  have hkSucc : (k + 1) * q = k * q + q := by
    simp [Nat.add_mul]
  have hqTwoU : q ≤ 2 * U := by omega
  have hsub : 2 * U - q + q = 2 * U :=
    Nat.sub_add_cancel hqTwoU
  have hkLower : U ≤ k * q := by
    omega
  have hkUpper : (k + 1) * q ≤ 2 * U := by
    omega
  have hkRange : k < 2 * U + 1 := by
    have hkLe : k ≤ u := Nat.div_le_self u q
    omega
  apply huDiff.2
  rw [h15CompletePeriodSupport, Finset.mem_biUnion]
  refine ⟨k, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr hkRange, hkLower, hkUpper⟩, ?_⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Ico.mpr ⟨hfloor, hceil⟩, huBlock.2⟩

/-- At most `2q` natural points remain outside the complete periods.  The
coprimality filter can only decrease this cardinality. -/
theorem card_h15CompletionBoundarySupport_le
    (U q : ℕ) (hq : 0 < q) :
    (h15CompletionBoundarySupport U q).card ≤ 2 * q := by
  calc
    (h15CompletionBoundarySupport U q).card ≤
        (Finset.Ico U (U + q) ∪
          Finset.Ico (2 * U - q) (2 * U)).card :=
      Finset.card_le_card
        (h15CompletionBoundarySupport_subset_endpointIntervals U q hq)
    _ ≤ (Finset.Ico U (U + q)).card +
        (Finset.Ico (2 * U - q) (2 * U)).card :=
      Finset.card_union_le _ _
    _ ≤ q + q := by
      simp only [Nat.card_Ico]
      omega
    _ = 2 * q := by omega

/-- Sums over the complete-period support reindex as sums over the individual
periods. -/
theorem sum_h15CompletePeriodSupport
    (U q : ℕ) (F : ℕ → ℝ) :
    (∑ u ∈ h15CompletePeriodSupport U q, F u) =
      ∑ k ∈ h15CompletePeriodIndices U q,
        ∑ u ∈ h15ReducedNaturalPeriod k q, F u := by
  unfold h15CompletePeriodSupport
  exact Finset.sum_biUnion
    (h15ReducedNaturalPeriod_pairwiseDisjoint U q)

/-- Exact support-level split into complete periods and boundary fragments. -/
theorem sum_h15ReducedDyadic_eq_complete_add_boundary
    (U q : ℕ) (F : ℕ → ℝ) :
    (∑ u ∈ h15ReducedDyadicNumeratorBlock U q, F u) =
      (∑ u ∈ h15CompletePeriodSupport U q, F u) +
        ∑ u ∈ h15CompletionBoundarySupport U q, F u := by
  have hsplit := Finset.sum_sdiff
    (h15CompletePeriodSupport_subset_reducedDyadic U q) (f := F)
  unfold h15CompletionBoundarySupport
  linarith

/-! ## The complete dyadic defect identity -/

/-- The weighted cross mode on the entire reduced dyadic numerator block. -/
noncomputable def h15DyadicWeightedRamanujanCross
    (r U q : ℕ) (weight : ℕ → ℝ) : ℝ :=
  ∑ u ∈ h15ReducedDyadicNumeratorBlock U q,
    weight u * h15PairedDirectCrossMode r u q

/-- Sum of the centered within-period defects over all complete periods. -/
noncomputable def h15DyadicPeriodVariationDefect
    (r U q : ℕ) (weight : ℕ → ℝ) (reference : ℕ → ℝ) : ℝ :=
  ∑ k ∈ h15CompletePeriodIndices U q,
    h15PeriodVariationDefect r k q weight (reference k)

/-- Weighted cross mode on the incomplete endpoint support. -/
noncomputable def h15DyadicBoundaryDefect
    (r U q : ℕ) (weight : ℕ → ℝ) : ℝ :=
  ∑ u ∈ h15CompletionBoundarySupport U q,
    weight u * h15PairedDirectCrossMode r u q

/-- Exact completion-defect decomposition of a weighted dyadic Ramanujan
cross mode.  The constant reference is arbitrary on each full period. -/
theorem h15DyadicWeightedRamanujanCross_eq_variation_add_boundary
    (r U q : ℕ) (weight : ℕ → ℝ) (reference : ℕ → ℝ)
    (hq : 0 < q) :
    h15DyadicWeightedRamanujanCross r U q weight =
      h15DyadicPeriodVariationDefect r U q weight reference +
        h15DyadicBoundaryDefect r U q weight := by
  unfold h15DyadicWeightedRamanujanCross
    h15DyadicPeriodVariationDefect h15DyadicBoundaryDefect
  rw [sum_h15ReducedDyadic_eq_complete_add_boundary]
  rw [sum_h15CompletePeriodSupport U q]
  apply congrArg (fun x : ℝ => x +
    ∑ u ∈ h15CompletionBoundarySupport U q,
      weight u * h15PairedDirectCrossMode r u q)
  apply Finset.sum_congr rfl
  intro k _
  exact h15PeriodWeightedCross_eq_variationDefect
    r k q weight (reference k) hq

/-! ## Instantiation with the actual H15 inverse coefficient -/

/-- The actual H15 inverse coefficient, extended by zero away from its
finite cutoff support. -/
noncomputable def h15SupportedInverseCoefficient
    (N g u : ℕ) : ℂ :=
  if g * u ≤ N then
    (h15BettinChandeeInverseCoefficient N g u : ℂ)
  else 0

/-- Its exact real squared weight. -/
noncomputable def h15SupportedInverseSquareWeight
    (N g u : ℕ) : ℝ :=
  if g * u ≤ N then
    h15BettinChandeeInverseCoefficient N g u ^ 2
  else 0

/-- The complex norm-square agrees exactly with the real squared H15 weight. -/
theorem normSq_h15SupportedInverseCoefficient
    (N g u : ℕ) :
    Complex.normSq (h15SupportedInverseCoefficient N g u) =
      h15SupportedInverseSquareWeight N g u := by
  unfold h15SupportedInverseCoefficient h15SupportedInverseSquareWeight
  split_ifs
  · rw [Complex.normSq_ofReal]
    ring
  · exact Complex.normSq_zero

/-- On a positive dyadic block, the genuine supported H15 square weight is
bounded by the inverse square of the block scale. -/
theorem h15SupportedInverseSquareWeight_le
    {N g U u : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g) (hU : 0 < U)
    (hu : u ∈ h15ReducedDyadicNumeratorBlock U q) :
    h15SupportedInverseSquareWeight N g u ≤
      (1 / (U : ℝ)) ^ 2 := by
  unfold h15SupportedInverseSquareWeight
  split_ifs with hsupport
  · have huSupported :
        u ∈ h15BettinChandeeSupportedNatBlock N g U := by
      apply Finset.mem_filter.mpr
      exact ⟨(Finset.mem_filter.mp hu).1, hsupport⟩
    rw [← sq_abs]
    exact pow_le_pow_left₀
      (abs_nonneg (h15BettinChandeeInverseCoefficient N g u))
      (abs_h15BettinChandeeInverseCoefficient_le
        hN hg hU huSupported) 2
  · positivity

/-- The paired-kernel cross correlation with the genuine supported H15
inverse coefficient is exactly the dyadic weighted Ramanujan correlation. -/
theorem h15PairedDirectCrossCorrelation_supported_eq_dyadic
    (N g r U q : ℕ) :
    h15PairedDirectCrossCorrelation r U q
        (h15SupportedInverseCoefficient N g) =
      h15DyadicWeightedRamanujanCross r U q
        (h15SupportedInverseSquareWeight N g) := by
  unfold h15PairedDirectCrossCorrelation
    h15DyadicWeightedRamanujanCross h15PairedDirectCrossMode
  apply Finset.sum_congr rfl
  intro u _
  rw [normSq_h15SupportedInverseCoefficient]

/-- Canonical period reference: the supported H15 squared weight at the
left endpoint of that period. -/
noncomputable def h15SupportedPeriodReferenceWeight
    (N g q k : ℕ) : ℝ :=
  h15SupportedInverseSquareWeight N g (k * q)

/-- Final exact H15 completion ledger.  The paired cross term is *only* the
sum of within-period variation and incomplete-boundary defects. -/
theorem h15PairedDirectCrossCorrelation_supported_eq_completionDefects
    (N g r U q : ℕ) (hq : 0 < q) :
    h15PairedDirectCrossCorrelation r U q
        (h15SupportedInverseCoefficient N g) =
      h15DyadicPeriodVariationDefect r U q
          (h15SupportedInverseSquareWeight N g)
          (h15SupportedPeriodReferenceWeight N g q) +
        h15DyadicBoundaryDefect r U q
          (h15SupportedInverseSquareWeight N g) := by
  rw [h15PairedDirectCrossCorrelation_supported_eq_dyadic]
  exact h15DyadicWeightedRamanujanCross_eq_variation_add_boundary
    r U q (h15SupportedInverseSquareWeight N g)
      (h15SupportedPeriodReferenceWeight N g q) hq

/-- Explicit endpoint estimate supplied by the two-fragment completion
geometry.  It is useful when `q` is small compared with `U`, but by itself it
does not control the within-period variation defect. -/
theorem abs_h15DyadicBoundaryDefect_supported_le
    {N g r U q : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g)
    (hU : 0 < U) (hq : 0 < q) :
    |h15DyadicBoundaryDefect r U q
        (h15SupportedInverseSquareWeight N g)| ≤
      (2 * q : ℝ) * (1 / (U : ℝ)) ^ 2 := by
  unfold h15DyadicBoundaryDefect
  calc
    |∑ u ∈ h15CompletionBoundarySupport U q,
        h15SupportedInverseSquareWeight N g u *
          h15PairedDirectCrossMode r u q| ≤
      ∑ u ∈ h15CompletionBoundarySupport U q,
        |h15SupportedInverseSquareWeight N g u *
          h15PairedDirectCrossMode r u q| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _u ∈ h15CompletionBoundarySupport U q,
        (1 / (U : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro u hu
      rw [abs_mul]
      have huBlock : u ∈ h15ReducedDyadicNumeratorBlock U q :=
        (Finset.mem_sdiff.mp hu).1
      have hweight := h15SupportedInverseSquareWeight_le
        (q := q) hN hg hU huBlock
      have hweightNonneg :
          0 ≤ h15SupportedInverseSquareWeight N g u := by
        unfold h15SupportedInverseSquareWeight
        split_ifs <;> positivity
      rw [abs_of_nonneg hweightNonneg]
      calc
        h15SupportedInverseSquareWeight N g u *
            |h15PairedDirectCrossMode r u q| ≤
          h15SupportedInverseSquareWeight N g u * 1 :=
            mul_le_mul_of_nonneg_left
              (abs_h15PairedDirectCrossMode_le_one r u q hq)
              hweightNonneg
        _ ≤ (1 / (U : ℝ)) ^ 2 := by simpa using hweight
    _ = ((h15CompletionBoundarySupport U q).card : ℝ) *
        (1 / (U : ℝ)) ^ 2 := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * q : ℝ) * (1 / (U : ℝ)) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact_mod_cast card_h15CompletionBoundarySupport_le U q hq

end NBMellinTools.NB12
