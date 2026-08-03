/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15SquarefreeGCDStratification

/-!
# NB12zi: normalized `Lq` superperiod completion

After gcd normalization, every active square-divisor row has the form

`L | u`, `Coprime u q`, `Im e(2*r*u/q)`,

with `Coprime L q`.  Its true arithmetic period is therefore `L*q`.  This
file proves that the unweighted row vanishes on every complete natural
`L*q` superperiod.  It then performs the exact dyadic completion into full
superperiods, a within-superperiod variation defect, and two boundary
fragments.

The boundary contains at most `2*(L*q)` natural points.  For the genuine H15
smooth inverse-square envelope this gives the explicit bound
`2*(L*q)/U^2`.  This is exact finite arithmetic; the signed sum of the
variation defects remains the analytic input required for H15.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius
open Complex

namespace NBMellinTools.NB12

/-! ## One complete normalized superperiod -/

/-- Natural points in the `j`-th interval of length `L*q` which lie in the
progression `L | u` and are reduced modulo `q`. -/
def h15NormalizedProgressionSuperperiod
    (j L q : ℕ) : Finset ℕ :=
  (Finset.Ico (j * (L * q)) ((j + 1) * (L * q))).filter fun u =>
    L ∣ u ∧ Nat.Coprime u q

theorem mem_h15NormalizedProgressionSuperperiod
    {j L q u : ℕ} :
    u ∈ h15NormalizedProgressionSuperperiod j L q ↔
      j * (L * q) ≤ u ∧ u < (j + 1) * (L * q) ∧
        L ∣ u ∧ Nat.Coprime u q := by
  simp [h15NormalizedProgressionSuperperiod, and_assoc]

/-- Multiplication by `L` moves the direct additive character from the
numerator variable to the frequency variable. -/
theorem h15PairedDirectCrossMode_mul_progression
    (r L v q : ℕ) (hq : 0 < q) (hLq : Nat.Coprime L q)
    (hvq : Nat.Coprime v q) :
    h15PairedDirectCrossMode r (L * v) q =
      h15PairedDirectCrossMode (r * L) v q := by
  letI : NeZero q := ⟨hq.ne'⟩
  rw [h15PairedDirectCrossMode_of_coprime r (L * v) q
      (hLq.mul_left hvq),
    h15PairedDirectCrossMode_of_coprime (r * L) v q hvq]
  congr 1
  apply congrArg ZMod.stdAddChar
  push_cast
  ring

/-- Reindex one normalized superperiod by `u=L*v`. -/
theorem sum_h15NormalizedProgressionSuperperiod_eq_reducedPeriod
    (j L q : ℕ) (F : ℕ → ℝ) (hL : 0 < L)
    (hLq : Nat.Coprime L q) :
    (∑ u ∈ h15NormalizedProgressionSuperperiod j L q, F u) =
      ∑ v ∈ h15ReducedNaturalPeriod j q, F (L * v) := by
  classical
  symm
  apply Finset.sum_bij (fun v _ ↦ L * v)
  · intro v hv
    have hv' := Finset.mem_filter.mp hv
    have hvRange := Finset.mem_Ico.mp hv'.1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ico.mpr ⟨?_, ?_⟩, ⟨dvd_mul_right L v, ?_⟩⟩
    · simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
        Nat.mul_le_mul_left L hvRange.1
    · simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
        Nat.mul_lt_mul_of_pos_left hvRange.2 hL
    · exact hLq.mul_left hv'.2
  · intro a ha b hb hab
    exact Nat.eq_of_mul_eq_mul_left hL hab
  · intro u hu
    have hu' := Finset.mem_filter.mp hu
    have huRange := Finset.mem_Ico.mp hu'.1
    rcases hu'.2.1 with ⟨v, rfl⟩
    have hvRange : j * q ≤ v ∧ v < (j + 1) * q := by
      constructor
      · apply Nat.le_of_mul_le_mul_left _ hL
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using huRange.1
      · have hmul : L * v < L * ((j + 1) * q) := by
          simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
            huRange.2
        exact (Nat.mul_lt_mul_left hL).mp hmul
    have hvq : Nat.Coprime v q :=
      Nat.Coprime.of_dvd_left (dvd_mul_left v L) hu'.2.2
    refine ⟨v, Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr hvRange, hvq⟩, rfl⟩
  · intro v hv
    rfl

/-- Exact zero mode on every complete normalized `L*q` superperiod. -/
theorem sum_h15NormalizedProgressionSuperperiod_crossMode_eq_zero
    (r j L q : ℕ) (hL : 0 < L) (hq : 0 < q)
    (hLq : Nat.Coprime L q) :
    (∑ u ∈ h15NormalizedProgressionSuperperiod j L q,
        h15PairedDirectCrossMode r u q) = 0 := by
  rw [sum_h15NormalizedProgressionSuperperiod_eq_reducedPeriod
    j L q (fun u => h15PairedDirectCrossMode r u q) hL hLq]
  calc
    (∑ v ∈ h15ReducedNaturalPeriod j q,
        h15PairedDirectCrossMode r (L * v) q) =
      ∑ v ∈ h15ReducedNaturalPeriod j q,
        h15PairedDirectCrossMode (r * L) v q := by
          apply Finset.sum_congr rfl
          intro v hv
          exact h15PairedDirectCrossMode_mul_progression r L v q hq hLq
            (Finset.mem_filter.mp hv).2
    _ = 0 := sum_h15ReducedNaturalPeriod_crossMode_eq_zero
      (r * L) j q hq

/-- The progression points in one ordinary `q`-period. -/
def h15NormalizedProgressionQPeriod
    (k L q : ℕ) : Finset ℕ :=
  (h15ReducedNaturalPeriod k q).filter fun u => L ∣ u

/-- Ordinary natural `q`-periods are pairwise disjoint on every index set. -/
theorem h15ReducedNaturalPeriod_pairwiseDisjoint_on
    (s : Finset ℕ) (q : ℕ) :
    Set.PairwiseDisjoint (s : Set ℕ) (fun k => h15ReducedNaturalPeriod k q) := by
  intro k _ l _ hkl
  apply Finset.disjoint_left.mpr
  intro u huk hul
  have hukRange := Finset.mem_Ico.mp (Finset.mem_filter.mp huk).1
  have hulRange := Finset.mem_Ico.mp (Finset.mem_filter.mp hul).1
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · have hmul : (k + 1) * q ≤ l * q :=
      Nat.mul_le_mul_right q (Nat.succ_le_of_lt hlt)
    omega
  · have hmul : (l + 1) * q ≤ k * q :=
      Nat.mul_le_mul_right q (Nat.succ_le_of_lt hgt)
    omega

/-- The `L` consecutive ordinary periods are exactly one normalized
superperiod. -/
theorem biUnion_h15NormalizedProgressionQPeriod_eq_superperiod
    (j L q : ℕ) (hq : 0 < q) :
    (Finset.Ico (j * L) ((j + 1) * L)).biUnion
        (fun k => h15NormalizedProgressionQPeriod k L q) =
      h15NormalizedProgressionSuperperiod j L q := by
  ext u
  constructor
  · intro hu
    rw [Finset.mem_biUnion] at hu
    rcases hu with ⟨k, hk, huk⟩
    have hkRange := Finset.mem_Ico.mp hk
    have huk' := Finset.mem_filter.mp huk
    have huPeriod := Finset.mem_filter.mp huk'.1
    have huRange := Finset.mem_Ico.mp huPeriod.1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ico.mpr ⟨?_, ?_⟩, huk'.2, huPeriod.2⟩
    · calc
        j * (L * q) = (j * L) * q := by ring
        _ ≤ k * q := Nat.mul_le_mul_right q hkRange.1
        _ ≤ u := huRange.1
    · calc
        u < (k + 1) * q := huRange.2
        _ ≤ ((j + 1) * L) * q :=
          Nat.mul_le_mul_right q (Nat.succ_le_of_lt hkRange.2)
        _ = (j + 1) * (L * q) := by ring
  · intro hu
    have hu' := Finset.mem_filter.mp hu
    have huRange := Finset.mem_Ico.mp hu'.1
    let k := u / q
    have hkLower : j * L ≤ k := by
      apply (Nat.le_div_iff_mul_le hq).2
      simpa [Nat.mul_assoc] using huRange.1
    have hkUpper : k < (j + 1) * L := by
      apply (Nat.div_lt_iff_lt_mul hq).2
      simpa [Nat.mul_assoc] using huRange.2
    have hfloor : k * q ≤ u := Nat.div_mul_le_self u q
    have hceil : u < (k + 1) * q := by
      simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ u hq
    rw [Finset.mem_biUnion]
    refine ⟨k, Finset.mem_Ico.mpr ⟨hkLower, hkUpper⟩, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr ⟨hfloor, hceil⟩, hu'.2.2⟩,
        hu'.2.1⟩

/-- A normalized row is the Möbius coefficient times its progression
support sum. -/
theorem h15PeriodNormalizedProgressionRow_eq_supportSum
    (g r k q d : ℕ) :
    h15PeriodNormalizedProgressionRow g r k q d =
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        ∑ u ∈ h15NormalizedProgressionQPeriod k
            (h15SquareDivisorProgressionModulus g d) q,
          h15PairedDirectCrossMode r u q := by
  unfold h15PeriodNormalizedProgressionRow
    h15NormalizedProgressionQPeriod
  rw [Finset.mul_sum]
  simp_rw [Finset.sum_filter]

/-- `L` consecutive normalized rows form a complete superperiod and cancel
exactly.  This theorem connects the superperiod geometry directly to the row
introduced by gcd stratification. -/
theorem sum_h15PeriodNormalizedProgressionRow_superperiod_eq_zero
    (g r j q d : ℕ) (hq : 0 < q)
    (hL : 0 < h15SquareDivisorProgressionModulus g d)
    (hcop : Nat.Coprime (h15SquareDivisorProgressionModulus g d) q) :
    (∑ k ∈ Finset.Ico
        (j * h15SquareDivisorProgressionModulus g d)
        ((j + 1) * h15SquareDivisorProgressionModulus g d),
      h15PeriodNormalizedProgressionRow g r k q d) = 0 := by
  let L := h15SquareDivisorProgressionModulus g d
  simp_rw [h15PeriodNormalizedProgressionRow_eq_supportSum]
  rw [← Finset.mul_sum]
  have hdisjoint : Set.PairwiseDisjoint
      (Finset.Ico (j * L) ((j + 1) * L) : Set ℕ)
      (fun k => h15NormalizedProgressionQPeriod k L q) := by
    apply (h15ReducedNaturalPeriod_pairwiseDisjoint_on
      (Finset.Ico (j * L) ((j + 1) * L)) q).mono
    intro k
    exact Finset.filter_subset _ _
  rw [← Finset.sum_biUnion hdisjoint]
  rw [biUnion_h15NormalizedProgressionQPeriod_eq_superperiod j L q hq]
  rw [sum_h15NormalizedProgressionSuperperiod_crossMode_eq_zero
    r j L q hL hq hcop, mul_zero]

/-! ## Completion of the actual `q`-period row sequence -/

/-- Indices of the complete `L*q` superperiods contained in `[U,2U)`. -/
def h15CompleteNormalizedSuperperiodIndices
    (U L q : ℕ) : Finset ℕ :=
  h15CompletePeriodIndices U (L * q)

/-- Ordinary `q`-period indices covered by complete `L`-row superperiods. -/
def h15CompleteNormalizedRowSuperperiodSupport
    (U L q : ℕ) : Finset ℕ :=
  (h15CompleteNormalizedSuperperiodIndices U L q).biUnion fun j =>
    Finset.Ico (j * L) ((j + 1) * L)

/-- Ordinary complete `q`-period indices not covered by a full block of `L`
consecutive rows. -/
def h15NormalizedRowSuperperiodBoundary
    (U L q : ℕ) : Finset ℕ :=
  h15CompletePeriodIndices U q \
    h15CompleteNormalizedRowSuperperiodSupport U L q

theorem h15NormalizedRowIndexBlocks_pairwiseDisjoint
    (U L q : ℕ) :
    Set.PairwiseDisjoint
      (h15CompleteNormalizedSuperperiodIndices U L q : Set ℕ)
      (fun j => Finset.Ico (j * L) ((j + 1) * L)) := by
  intro j _ k _ hjk
  apply Finset.disjoint_left.mpr
  intro n hnj hnk
  have hnjRange := Finset.mem_Ico.mp hnj
  have hnkRange := Finset.mem_Ico.mp hnk
  rcases lt_or_gt_of_ne hjk with hjklt | hkjlt
  · have hmul : (j + 1) * L ≤ k * L :=
      Nat.mul_le_mul_right L (Nat.succ_le_of_lt hjklt)
    omega
  · have hmul : (k + 1) * L ≤ j * L :=
      Nat.mul_le_mul_right L (Nat.succ_le_of_lt hkjlt)
    omega

theorem h15CompleteNormalizedRowSuperperiodSupport_subset_periodIndices
    (U L q : ℕ) (hq : 0 < q) :
    h15CompleteNormalizedRowSuperperiodSupport U L q ⊆
      h15CompletePeriodIndices U q := by
  intro k hk
  rw [h15CompleteNormalizedRowSuperperiodSupport,
    Finset.mem_biUnion] at hk
  rcases hk with ⟨j, hj, hkj⟩
  have hjBounds := (Finset.mem_filter.mp hj).2
  have hkRange := Finset.mem_Ico.mp hkj
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr ?_, ?_, ?_⟩
  · have hkqLe : k * q ≤ 2 * U := by
      exact (calc
        k * q < ((j + 1) * L) * q :=
          Nat.mul_lt_mul_of_pos_right hkRange.2 hq
        _ = (j + 1) * (L * q) := by ring
        _ ≤ 2 * U := hjBounds.2).le
    have hkLe : k ≤ k * q := by
      simpa using Nat.mul_le_mul_left k (show 1 ≤ q by omega)
    omega
  · calc
      U ≤ j * (L * q) := hjBounds.1
      _ = (j * L) * q := by ring
      _ ≤ k * q := Nat.mul_le_mul_right q hkRange.1
  · calc
      (k + 1) * q ≤ ((j + 1) * L) * q :=
        Nat.mul_le_mul_right q (Nat.succ_le_of_lt hkRange.2)
      _ = (j + 1) * (L * q) := by ring
      _ ≤ 2 * U := hjBounds.2

theorem sum_h15CompleteNormalizedRowSuperperiodSupport
    (U L q : ℕ) (F : ℕ → ℝ) :
    (∑ k ∈ h15CompleteNormalizedRowSuperperiodSupport U L q, F k) =
      ∑ j ∈ h15CompleteNormalizedSuperperiodIndices U L q,
        ∑ k ∈ Finset.Ico (j * L) ((j + 1) * L), F k := by
  unfold h15CompleteNormalizedRowSuperperiodSupport
  exact Finset.sum_biUnion
    (h15NormalizedRowIndexBlocks_pairwiseDisjoint U L q)

theorem sum_h15CompletePeriodIndices_eq_rowSuperperiod_add_boundary
    (U L q : ℕ) (F : ℕ → ℝ) (hq : 0 < q) :
    (∑ k ∈ h15CompletePeriodIndices U q, F k) =
      (∑ k ∈ h15CompleteNormalizedRowSuperperiodSupport U L q, F k) +
        ∑ k ∈ h15NormalizedRowSuperperiodBoundary U L q, F k := by
  have hsplit := Finset.sum_sdiff
    (h15CompleteNormalizedRowSuperperiodSupport_subset_periodIndices
      U L q hq) (f := F)
  unfold h15NormalizedRowSuperperiodBoundary
  linarith

noncomputable def h15NormalizedRowSuperperiodVariationDefect
    (g r U q d : ℕ) (weight reference : ℕ → ℝ) : ℝ :=
  let L := h15SquareDivisorProgressionModulus g d
  ∑ j ∈ h15CompleteNormalizedSuperperiodIndices U L q,
    ∑ k ∈ Finset.Ico (j * L) ((j + 1) * L),
      (weight k - reference j) *
        h15PeriodNormalizedProgressionRow g r k q d

noncomputable def h15NormalizedRowSuperperiodBoundaryDefect
    (g r U q d : ℕ) (weight : ℕ → ℝ) : ℝ :=
  let L := h15SquareDivisorProgressionModulus g d
  ∑ k ∈ h15NormalizedRowSuperperiodBoundary U L q,
    weight k * h15PeriodNormalizedProgressionRow g r k q d

/-- Exact completion of the already formalized normalized row with its
genuine periodwise weight retained. -/
theorem h15NormalizedProgressionRowWeightedSum_eq_variation_add_boundary
    (g r U q d : ℕ) (weight reference : ℕ → ℝ)
    (hq : 0 < q)
    (hL : 0 < h15SquareDivisorProgressionModulus g d)
    (hcop : Nat.Coprime (h15SquareDivisorProgressionModulus g d) q) :
    (∑ k ∈ h15CompletePeriodIndices U q,
      weight k * h15PeriodNormalizedProgressionRow g r k q d) =
      h15NormalizedRowSuperperiodVariationDefect
          g r U q d weight reference +
        h15NormalizedRowSuperperiodBoundaryDefect g r U q d weight := by
  let L := h15SquareDivisorProgressionModulus g d
  unfold h15NormalizedRowSuperperiodVariationDefect
    h15NormalizedRowSuperperiodBoundaryDefect
  rw [sum_h15CompletePeriodIndices_eq_rowSuperperiod_add_boundary
    U L q (fun k => weight k *
      h15PeriodNormalizedProgressionRow g r k q d) hq]
  rw [sum_h15CompleteNormalizedRowSuperperiodSupport U L q]
  apply congrArg (fun x : ℝ => x +
    ∑ k ∈ h15NormalizedRowSuperperiodBoundary U L q,
      weight k * h15PeriodNormalizedProgressionRow g r k q d)
  apply Finset.sum_congr rfl
  intro j _
  have hzero := sum_h15PeriodNormalizedProgressionRow_superperiod_eq_zero
    g r j q d hq hL hcop
  calc
    (∑ k ∈ Finset.Ico (j * L) ((j + 1) * L),
        weight k * h15PeriodNormalizedProgressionRow g r k q d) =
      ∑ k ∈ Finset.Ico (j * L) ((j + 1) * L),
        ((weight k - reference j) *
            h15PeriodNormalizedProgressionRow g r k q d +
          reference j * h15PeriodNormalizedProgressionRow g r k q d) := by
            apply Finset.sum_congr rfl
            intro k _
            ring
    _ = (∑ k ∈ Finset.Ico (j * L) ((j + 1) * L),
          (weight k - reference j) *
            h15PeriodNormalizedProgressionRow g r k q d) +
        reference j *
          ∑ k ∈ Finset.Ico (j * L) ((j + 1) * L),
            h15PeriodNormalizedProgressionRow g r k q d := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by rw [hzero, mul_zero, add_zero]

/-! ## Exact dyadic superperiod completion -/

/-- All progression points lying in complete normalized superperiods. -/
def h15CompleteNormalizedSuperperiodSupport
    (U L q : ℕ) : Finset ℕ :=
  (h15CompleteNormalizedSuperperiodIndices U L q).biUnion fun j =>
    h15NormalizedProgressionSuperperiod j L q

/-- The normalized progression inside the original dyadic numerator block. -/
def h15NormalizedProgressionDyadicSupport
    (U L q : ℕ) : Finset ℕ :=
  (h15ReducedDyadicNumeratorBlock U q).filter fun u => L ∣ u

/-- Progression points in the two incomplete endpoint superperiods. -/
def h15NormalizedSuperperiodBoundarySupport
    (U L q : ℕ) : Finset ℕ :=
  h15NormalizedProgressionDyadicSupport U L q \
    h15CompleteNormalizedSuperperiodSupport U L q

/-- Distinct normalized superperiods are disjoint. -/
theorem h15NormalizedProgressionSuperperiod_pairwiseDisjoint
    (U L q : ℕ) :
    Set.PairwiseDisjoint
      (h15CompleteNormalizedSuperperiodIndices U L q : Set ℕ)
      (fun j => h15NormalizedProgressionSuperperiod j L q) := by
  intro j _ k _ hjk
  apply Finset.disjoint_left.mpr
  intro u huj huk
  have hujRange := Finset.mem_Ico.mp (Finset.mem_filter.mp huj).1
  have hukRange := Finset.mem_Ico.mp (Finset.mem_filter.mp huk).1
  rcases lt_or_gt_of_ne hjk with hjklt | hkjlt
  · have hmul : (j + 1) * (L * q) ≤ k * (L * q) :=
      Nat.mul_le_mul_right (L * q) (Nat.succ_le_of_lt hjklt)
    omega
  · have hmul : (k + 1) * (L * q) ≤ j * (L * q) :=
      Nat.mul_le_mul_right (L * q) (Nat.succ_le_of_lt hkjlt)
    omega

/-- Every complete-superperiod point is in the normalized dyadic support. -/
theorem h15CompleteNormalizedSuperperiodSupport_subset_dyadic
    (U L q : ℕ) :
    h15CompleteNormalizedSuperperiodSupport U L q ⊆
      h15NormalizedProgressionDyadicSupport U L q := by
  intro u hu
  rw [h15CompleteNormalizedSuperperiodSupport, Finset.mem_biUnion] at hu
  rcases hu with ⟨j, hj, huj⟩
  have hjBounds := (Finset.mem_filter.mp hj).2
  have huj' := Finset.mem_filter.mp huj
  have huRange := Finset.mem_Ico.mp huj'.1
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_filter.mpr
    ⟨Finset.mem_Ico.mpr ⟨?_, ?_⟩, huj'.2.2⟩, huj'.2.1⟩
  · exact hjBounds.1.trans huRange.1
  · exact huRange.2.trans_le hjBounds.2

/-- The normalized boundary lies in two intervals of length `L*q`. -/
theorem h15NormalizedSuperperiodBoundarySupport_subset_endpointIntervals
    (U L q : ℕ) (hLq : 0 < L * q) :
    h15NormalizedSuperperiodBoundarySupport U L q ⊆
      Finset.Ico U (U + L * q) ∪
        Finset.Ico (2 * U - L * q) (2 * U) := by
  intro u hu
  have huDiff := Finset.mem_sdiff.mp hu
  have huBlock := Finset.mem_filter.mp huDiff.1
  have huReduced := Finset.mem_filter.mp huBlock.1
  have huRange := Finset.mem_Ico.mp huReduced.1
  by_contra hend
  have hend' :
      ¬ (U ≤ u ∧ u < U + L * q) ∧
        ¬ (2 * U - L * q ≤ u ∧ u < 2 * U) := by
    simpa only [Finset.mem_union, Finset.mem_Ico, not_or] using hend
  have hlow : U + L * q ≤ u := by omega
  have hhigh : u < 2 * U - L * q := by omega
  let j := u / (L * q)
  have hfloor : j * (L * q) ≤ u := Nat.div_mul_le_self u (L * q)
  have hceil : u < (j + 1) * (L * q) := by
    simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ u hLq
  have hsucc : (j + 1) * (L * q) = j * (L * q) + L * q := by
    simp [Nat.add_mul]
  have hmodTwoU : L * q ≤ 2 * U := by omega
  have hsub : 2 * U - L * q + L * q = 2 * U :=
    Nat.sub_add_cancel hmodTwoU
  have hjLower : U ≤ j * (L * q) := by omega
  have hjUpper : (j + 1) * (L * q) ≤ 2 * U := by omega
  have hjRange : j < 2 * U + 1 := by
    have hjLe : j ≤ u := Nat.div_le_self u (L * q)
    omega
  apply huDiff.2
  rw [h15CompleteNormalizedSuperperiodSupport, Finset.mem_biUnion]
  refine ⟨j, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr hjRange, hjLower, hjUpper⟩, ?_⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Ico.mpr ⟨hfloor, hceil⟩,
      huBlock.2, huReduced.2⟩

/-- Crude geometric boundary cardinality.  The progression filter can only
decrease the size of the two endpoint intervals. -/
theorem card_h15NormalizedSuperperiodBoundarySupport_le
    (U L q : ℕ) (hLq : 0 < L * q) :
    (h15NormalizedSuperperiodBoundarySupport U L q).card ≤
      2 * (L * q) := by
  calc
    (h15NormalizedSuperperiodBoundarySupport U L q).card ≤
        (Finset.Ico U (U + L * q) ∪
          Finset.Ico (2 * U - L * q) (2 * U)).card :=
      Finset.card_le_card
        (h15NormalizedSuperperiodBoundarySupport_subset_endpointIntervals
          U L q hLq)
    _ ≤ (Finset.Ico U (U + L * q)).card +
        (Finset.Ico (2 * U - L * q) (2 * U)).card :=
      Finset.card_union_le _ _
    _ ≤ L * q + L * q := by
      simp only [Nat.card_Ico]
      omega
    _ = 2 * (L * q) := by omega

/-- Reindex a sum on the complete support by its pairwise-disjoint
superperiods. -/
theorem sum_h15CompleteNormalizedSuperperiodSupport
    (U L q : ℕ) (F : ℕ → ℝ) :
    (∑ u ∈ h15CompleteNormalizedSuperperiodSupport U L q, F u) =
      ∑ j ∈ h15CompleteNormalizedSuperperiodIndices U L q,
        ∑ u ∈ h15NormalizedProgressionSuperperiod j L q, F u := by
  unfold h15CompleteNormalizedSuperperiodSupport
  exact Finset.sum_biUnion
    (h15NormalizedProgressionSuperperiod_pairwiseDisjoint U L q)

/-- Exact support split into complete `L*q` superperiods and boundary. -/
theorem sum_h15NormalizedProgressionDyadic_eq_complete_add_boundary
    (U L q : ℕ) (F : ℕ → ℝ) :
    (∑ u ∈ h15NormalizedProgressionDyadicSupport U L q, F u) =
      (∑ u ∈ h15CompleteNormalizedSuperperiodSupport U L q, F u) +
        ∑ u ∈ h15NormalizedSuperperiodBoundarySupport U L q, F u := by
  have hsplit := Finset.sum_sdiff
    (h15CompleteNormalizedSuperperiodSupport_subset_dyadic U L q) (f := F)
  unfold h15NormalizedSuperperiodBoundarySupport
  linarith

/-! ## Correction-preserving variation identity -/

noncomputable def h15NormalizedSuperperiodWeightedCross
    (r j L q : ℕ) (weight : ℕ → ℝ) : ℝ :=
  ∑ u ∈ h15NormalizedProgressionSuperperiod j L q,
    weight u * h15PairedDirectCrossMode r u q

noncomputable def h15NormalizedSuperperiodVariationDefect
    (r j L q : ℕ) (weight : ℕ → ℝ) (reference : ℝ) : ℝ :=
  ∑ u ∈ h15NormalizedProgressionSuperperiod j L q,
    (weight u - reference) * h15PairedDirectCrossMode r u q

theorem h15NormalizedSuperperiodWeightedCross_eq_variationDefect
    (r j L q : ℕ) (weight : ℕ → ℝ) (reference : ℝ)
    (hL : 0 < L) (hq : 0 < q) (hcop : Nat.Coprime L q) :
    h15NormalizedSuperperiodWeightedCross r j L q weight =
      h15NormalizedSuperperiodVariationDefect r j L q weight reference := by
  unfold h15NormalizedSuperperiodWeightedCross
    h15NormalizedSuperperiodVariationDefect
  have hzero := sum_h15NormalizedProgressionSuperperiod_crossMode_eq_zero
    r j L q hL hq hcop
  calc
    (∑ u ∈ h15NormalizedProgressionSuperperiod j L q,
        weight u * h15PairedDirectCrossMode r u q) =
      ∑ u ∈ h15NormalizedProgressionSuperperiod j L q,
        ((weight u - reference) * h15PairedDirectCrossMode r u q +
          reference * h15PairedDirectCrossMode r u q) := by
            apply Finset.sum_congr rfl
            intro u _
            ring
    _ = (∑ u ∈ h15NormalizedProgressionSuperperiod j L q,
          (weight u - reference) * h15PairedDirectCrossMode r u q) +
        reference *
          ∑ u ∈ h15NormalizedProgressionSuperperiod j L q,
            h15PairedDirectCrossMode r u q := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by rw [hzero, mul_zero, add_zero]

noncomputable def h15DyadicNormalizedProgressionWeightedCross
    (r U L q : ℕ) (weight : ℕ → ℝ) : ℝ :=
  ∑ u ∈ h15NormalizedProgressionDyadicSupport U L q,
    weight u * h15PairedDirectCrossMode r u q

noncomputable def h15DyadicNormalizedSuperperiodVariationDefect
    (r U L q : ℕ) (weight : ℕ → ℝ) (reference : ℕ → ℝ) : ℝ :=
  ∑ j ∈ h15CompleteNormalizedSuperperiodIndices U L q,
    h15NormalizedSuperperiodVariationDefect r j L q weight (reference j)

noncomputable def h15DyadicNormalizedSuperperiodBoundaryDefect
    (r U L q : ℕ) (weight : ℕ → ℝ) : ℝ :=
  ∑ u ∈ h15NormalizedSuperperiodBoundarySupport U L q,
    weight u * h15PairedDirectCrossMode r u q

/-- The full normalized dyadic row is exactly variation plus boundary; the
constant mode is removed only after its exact zero has been retained. -/
theorem h15DyadicNormalizedProgressionWeightedCross_eq_variation_add_boundary
    (r U L q : ℕ) (weight : ℕ → ℝ) (reference : ℕ → ℝ)
    (hL : 0 < L) (hq : 0 < q) (hcop : Nat.Coprime L q) :
    h15DyadicNormalizedProgressionWeightedCross r U L q weight =
      h15DyadicNormalizedSuperperiodVariationDefect
          r U L q weight reference +
        h15DyadicNormalizedSuperperiodBoundaryDefect r U L q weight := by
  unfold h15DyadicNormalizedProgressionWeightedCross
    h15DyadicNormalizedSuperperiodVariationDefect
    h15DyadicNormalizedSuperperiodBoundaryDefect
  rw [sum_h15NormalizedProgressionDyadic_eq_complete_add_boundary]
  rw [sum_h15CompleteNormalizedSuperperiodSupport U L q]
  apply congrArg (fun x : ℝ => x +
    ∑ u ∈ h15NormalizedSuperperiodBoundarySupport U L q,
      weight u * h15PairedDirectCrossMode r u q)
  apply Finset.sum_congr rfl
  intro j _
  exact h15NormalizedSuperperiodWeightedCross_eq_variationDefect
    r j L q weight (reference j) hL hq hcop

/-! ## The H15 smooth-envelope boundary budget -/

/-- The Möbius-signed smooth weight of one normalized divisor row. -/
noncomputable def h15NormalizedProgressionSmoothWeight
    (N g d u : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
    h15SupportedInverseSmoothEnvelope N g u

theorem abs_h15NormalizedProgressionSmoothWeight_le_of_mem
    {N g d U L q u : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g)
    (hU : 0 < U) (hu : u ∈ h15NormalizedProgressionDyadicSupport U L q) :
    |h15NormalizedProgressionSmoothWeight N g d u| ≤
      (1 / (U : ℝ)) ^ 2 := by
  have huReduced := (Finset.mem_filter.mp hu).1
  have huBlock : u ∈ h15BettinChandeeNatBlock U :=
    (Finset.mem_filter.mp huReduced).1
  have henv := h15SupportedInverseSmoothEnvelope_le_of_mem_natBlock
    hN hg hU huBlock
  have henvNonneg := h15SupportedInverseSmoothEnvelope_nonneg N g u
  unfold h15NormalizedProgressionSmoothWeight
  rw [abs_mul, abs_of_nonneg henvNonneg]
  calc
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
        h15SupportedInverseSmoothEnvelope N g u ≤
      1 * (1 / (U : ℝ)) ^ 2 := by
        apply mul_le_mul
        · exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
        · exact henv
        · exact henvNonneg
        · norm_num
    _ = (1 / (U : ℝ)) ^ 2 := one_mul _

/-- Absolute endpoint cost for one normalized divisor row after `L*q`
completion. -/
theorem abs_h15DyadicNormalizedSuperperiodBoundaryDefect_smooth_le
    {N g r d U L q : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g)
    (hU : 0 < U) (hL : 0 < L) (hq : 0 < q) :
    |h15DyadicNormalizedSuperperiodBoundaryDefect r U L q
        (h15NormalizedProgressionSmoothWeight N g d)| ≤
      (2 * (L * q) : ℝ) * (1 / (U : ℝ)) ^ 2 := by
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
                hN hg hU
                ((Finset.mem_sdiff.mp hu).1))
              (abs_h15PairedDirectCrossMode_le_one r u q hq)
              (abs_nonneg _) (by positivity)
        _ = (1 / (U : ℝ)) ^ 2 := mul_one _
    _ = ((h15NormalizedSuperperiodBoundarySupport U L q).card : ℝ) *
        (1 / (U : ℝ)) ^ 2 := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * (L * q) : ℝ) * (1 / (U : ℝ)) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_h15NormalizedSuperperiodBoundarySupport_le
        U L q (Nat.mul_pos hL hq)

/-- Explicit boundary budget isolated by normalized completion. -/
noncomputable def h15NormalizedSuperperiodBoundaryBudget
    (U L q : ℕ) : ℝ :=
  (2 * (L * q) : ℝ) * (1 / (U : ℝ)) ^ 2

/-- On a balanced modulus row `q=U`, the crude boundary budget is exactly
`2L/U`.  Hence superperiod completion alone is not uniform in the normalized
progression modulus. -/
theorem h15NormalizedSuperperiodBoundaryBudget_balanced
    {U L : ℕ} (hU : 0 < U) :
    h15NormalizedSuperperiodBoundaryBudget U L U =
      (2 * L : ℝ) / (U : ℝ) := by
  unfold h15NormalizedSuperperiodBoundaryBudget
  have hU0 : (U : ℝ) ≠ 0 := by positivity
  field_simp

/-- A modulus-average for the normalized progression factors is the exact
additional finite input needed to turn the endpoint ledger into decay. -/
def h15DyadicActivePeriodSquareDivisorIndices
    (g U q : ℕ) : Finset ℕ :=
  (h15CompletePeriodIndices U q).biUnion fun k =>
    h15ActivePeriodSquareDivisorIndices g k q

structure H15NormalizedProgressionBoundaryAverage where
  C : ℝ
  η : ℝ
  C_nonneg : 0 ≤ C
  η_pos : 0 < η
  bound : ∀ {N g U Q : ℕ},
    2 ≤ N → 1 ≤ g → 0 < U → 0 < Q → Q ≤ U →
    (∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
      ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
        h15NormalizedSuperperiodBoundaryBudget U
          (h15SquareDivisorProgressionModulus g d) q) ≤
      C / (U : ℝ) ^ η

/-- The remaining signed within-superperiod estimate, stated independently
of the endpoint average so the two mechanisms cannot be conflated. -/
structure H15NormalizedSuperperiodVariationPowerSaving where
  C : ℝ
  η : ℝ
  C_nonneg : 0 ≤ C
  η_pos : 0 < η
  bound : ∀ {N g r U Q : ℕ},
    2 ≤ N → 1 ≤ g → 0 < U → 0 < Q → Q ≤ U →
    |∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
      ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
        h15DyadicNormalizedSuperperiodVariationDefect r U
          (h15SquareDivisorProgressionModulus g d) q
          (h15NormalizedProgressionSmoothWeight N g d)
          (fun j => h15NormalizedProgressionSmoothWeight N g d
            (j * (h15SquareDivisorProgressionModulus g d * q)))| ≤
      C / (U : ℝ) ^ η

end NBMellinTools.NB12
