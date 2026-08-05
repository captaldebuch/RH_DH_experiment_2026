/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15BoundaryDensity

/-!
# NB12zl: active-incidence extension by zero

The normalized H15 progression aggregate is initially indexed by a divisor
set which depends on the ordinary `q`-period index `k`.  The signed
superperiod decomposition instead needs one common divisor index on the
whole dyadic block.  This file proves the missing compatibility statement:
a divisor which is active somewhere in the dyadic block contributes the
zero normalized row in every period where it is not active.

The proof uses only the exact normalization

`d^2 ∣ g*u ↔ h15SquareDivisorProgressionModulus g d ∣ u`.

No absolute value, analytic estimate, or cancellation hypothesis is used.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius
open Complex

namespace NBMellinTools.NB12

/-! ## A row outside its incidence support is zero -/

/-- If a positive divisor index does not occur anywhere on one positive
natural `q`-period, its normalized progression row is exactly zero. -/
theorem h15PeriodNormalizedProgressionRow_eq_zero_of_not_mem_periodIndices
    {g r k q d : ℕ} (hg : 0 < g) (hkq : 0 < k * q) (hd : 0 < d)
    (hnot : d ∉ h15PeriodSquareDivisorIndices g k q) :
    h15PeriodNormalizedProgressionRow g r k q d = 0 := by
  unfold h15PeriodNormalizedProgressionRow
  apply Finset.sum_eq_zero
  intro u hu
  rw [if_neg]
  intro hLdvd
  apply hnot
  rw [h15PeriodSquareDivisorIndices, Finset.mem_biUnion]
  refine ⟨u, hu, ?_⟩
  have huRange := Finset.mem_Ico.mp (Finset.mem_filter.mp hu).1
  have huPos : 0 < u := hkq.trans_le huRange.1
  have hgu : g * u ≠ 0 := Nat.mul_ne_zero hg.ne' huPos.ne'
  apply (mem_h15SquareDivisorSupport_iff hgu).2
  exact (h15_sq_dvd_mul_iff_progressionModulus_dvd hd).2 hLdvd

/-! ## Extension from the moving active set to its dyadic union -/

/-- A divisor active somewhere in the dyadic block has period-independent
conditions `2 ≤ L` and `Coprime L q`.  Hence, if it is not active in a
particular positive period, it is absent from that period's incidence set
and its normalized row vanishes.

This is the extension-by-zero lemma required before the `k,d` incidence can
be transposed in the signed Step 4v aggregate. -/
theorem h15PeriodNormalizedProgressionRow_eq_zero_of_mem_dyadic_not_active
    {g r k q d U : ℕ} (hg : 0 < g) (hkq : 0 < k * q)
    (hd : d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q)
    (hnot : d ∉ h15ActivePeriodSquareDivisorIndices g k q) :
    h15PeriodNormalizedProgressionRow g r k q d = 0 := by
  rw [h15DyadicActivePeriodSquareDivisorIndices,
    Finset.mem_biUnion] at hd
  obtain ⟨j, _hj, hdj⟩ := hd
  have hdj' := mem_h15ActivePeriodSquareDivisorIndices.mp hdj
  obtain ⟨u, _hu, hdu⟩ := Finset.mem_biUnion.mp hdj'.1
  have hdPos : 0 < d := pos_of_mem_h15SquareDivisorSupport hdu
  have hnotIndex : d ∉ h15PeriodSquareDivisorIndices g k q := by
    intro hdk
    apply hnot
    exact mem_h15ActivePeriodSquareDivisorIndices.mpr
      ⟨hdk, hdj'.2.1, hdj'.2.2⟩
  exact h15PeriodNormalizedProgressionRow_eq_zero_of_not_mem_periodIndices
    hg hkq hdPos hnotIndex

/-! ## Exact transpose of the active incidence relation -/

/-- A finite row family supported on the moving active-divisor sets can be
extended by zero to their dyadic union and then transposed.  This lemma is
pure finite algebra: it neither takes absolute values nor changes the row
coefficients. -/
theorem sum_h15ActivePeriod_eq_sum_dyadicActive
    (g U q : ℕ) (F : ℕ → ℕ → ℝ)
    (hzero : ∀ k ∈ h15CompletePeriodIndices U q,
      ∀ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
        d ∉ h15ActivePeriodSquareDivisorIndices g k q → F k d = 0) :
    (∑ k ∈ h15CompletePeriodIndices U q,
      ∑ d ∈ h15ActivePeriodSquareDivisorIndices g k q, F k d) =
      ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
        ∑ k ∈ h15CompletePeriodIndices U q, F k d := by
  classical
  calc
    (∑ k ∈ h15CompletePeriodIndices U q,
        ∑ d ∈ h15ActivePeriodSquareDivisorIndices g k q, F k d) =
        ∑ k ∈ h15CompletePeriodIndices U q,
          ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
            F k d := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_subset
      · intro d hd
        rw [h15DyadicActivePeriodSquareDivisorIndices,
          Finset.mem_biUnion]
        exact ⟨k, hk, hd⟩
      · intro d hd hnot
        exact hzero k hk d hd hnot
    _ = ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
        ∑ k ∈ h15CompletePeriodIndices U q, F k d := by
      rw [Finset.sum_comm]

/-- Exact signed `k,d` transpose for the genuine normalized progression
rows and an arbitrary real period weight.  Membership in a positive dyadic
period supplies the positivity needed by the extension-by-zero theorem. -/
theorem sum_weighted_h15ActivePeriodNormalizedRows_eq_sum_dyadicActive
    {g r U q : ℕ} (hg : 0 < g) (hU : 0 < U) (weight : ℕ → ℝ) :
    (∑ k ∈ h15CompletePeriodIndices U q,
      weight k *
        ∑ d ∈ h15ActivePeriodSquareDivisorIndices g k q,
          h15PeriodNormalizedProgressionRow g r k q d) =
      ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
        ∑ k ∈ h15CompletePeriodIndices U q,
          weight k * h15PeriodNormalizedProgressionRow g r k q d := by
  classical
  simp_rw [Finset.mul_sum]
  apply sum_h15ActivePeriod_eq_sum_dyadicActive
  intro k hk d hd hnot
  have hkBounds := (Finset.mem_filter.mp hk).2
  have hkqPos : 0 < k * q := hU.trans_le hkBounds.1
  rw [h15PeriodNormalizedProgressionRow_eq_zero_of_mem_dyadic_not_active
    hg hkqPos hd hnot, mul_zero]

/-- The complete normalized H15 aggregate, with its original signed smooth
weight, equals the divisor-first dyadic incidence sum.  This is the exact
Step 4v-b input for applying the row-level superperiod identity without
discarding either the variation term or the endpoint correction. -/
theorem h15NormalizedProgressionAggregate_eq_dyadicActiveTranspose
    {N g r U Q : ℕ} (hg : 0 < g) (hU : 0 < U) :
    h15NormalizedProgressionAggregate N g r U Q =
      ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
          ∑ k ∈ h15CompletePeriodIndices U q,
            h15SupportedInverseSmoothEnvelope N g (k * q) *
              h15PeriodNormalizedProgressionRow g r k q d := by
  unfold h15NormalizedProgressionAggregate
  apply Finset.sum_congr rfl
  intro q _hq
  exact sum_weighted_h15ActivePeriodNormalizedRows_eq_sum_dyadicActive
    hg hU (fun k => h15SupportedInverseSmoothEnvelope N g (k * q))

/-! ## Coupled variation-plus-boundary assembly -/

/-- The exact signed output of normalized superperiod completion after the
active-incidence transpose.  Variation and endpoint boundary remain inside
the same `q,d` summand; this definition intentionally performs no triangle
inequality and no separate absolute majorization.

The reference value is the smooth envelope sampled at the left endpoint
`j*(L*q)` of the normalized superperiod. -/
noncomputable def h15NormalizedProgressionCoupledVariationBoundaryAggregate
    (N g r U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
      (h15NormalizedRowSuperperiodVariationDefect g r U q d
          (fun k => h15SupportedInverseSmoothEnvelope N g (k * q))
          (fun j => h15SupportedInverseSmoothEnvelope N g
            (j * (h15SquareDivisorProgressionModulus g d * q))) +
        h15NormalizedRowSuperperiodBoundaryDefect g r U q d
          (fun k => h15SupportedInverseSmoothEnvelope N g (k * q)))

/-- Exact Step 4v-c assembly.  The complete normalized H15 progression
aggregate is the correction-coupled sum of its within-superperiod variation
and retained endpoint boundary.  In particular, the equality is established
before taking an absolute value, so the endpoint term remains available for
signed cancellation against the variation term. -/
theorem h15NormalizedProgressionAggregate_eq_coupledVariationBoundary
    {N g r U Q : ℕ} (hg : 0 < g) (hU : 0 < U) (hQ : 0 < Q) :
    h15NormalizedProgressionAggregate N g r U Q =
      h15NormalizedProgressionCoupledVariationBoundaryAggregate
        N g r U Q := by
  rw [h15NormalizedProgressionAggregate_eq_dyadicActiveTranspose hg hU]
  unfold h15NormalizedProgressionCoupledVariationBoundaryAggregate
  apply Finset.sum_congr rfl
  intro q hq
  have hqBounds := mem_h15BettinChandeeSupportedNatBlock.mp hq
  have hqPos : 0 < q := hQ.trans_le hqBounds.1
  apply Finset.sum_congr rfl
  intro d hd
  have hd' := hd
  rw [h15DyadicActivePeriodSquareDivisorIndices,
    Finset.mem_biUnion] at hd'
  obtain ⟨k, _hk, hdk⟩ := hd'
  have hactive := mem_h15ActivePeriodSquareDivisorIndices.mp hdk
  have hLPos : 0 < h15SquareDivisorProgressionModulus g d := by
    omega
  exact h15NormalizedProgressionRowWeightedSum_eq_variation_add_boundary
    g r U q d
      (fun k => h15SupportedInverseSmoothEnvelope N g (k * q))
      (fun j => h15SupportedInverseSmoothEnvelope N g
        (j * (h15SquareDivisorProgressionModulus g d * q)))
      hqPos hLPos hactive.2.2

/-! ## Exact row-to-pointwise bridge and its residual -/

/-- Progression points belonging to the complete ordinary `q`-periods used
by the row aggregate.  This support is deliberately smaller than
`h15NormalizedProgressionDyadicSupport`: the latter also contains the two
incomplete outer `q`-period fragments. -/
def h15NormalizedCompletePeriodProgressionSupport
    (U L q : ℕ) : Finset ℕ :=
  (h15CompletePeriodIndices U q).biUnion fun k =>
    h15NormalizedProgressionQPeriod k L q

/-- The pointwise form of the row weight.  On the `k`-th complete period it
is exactly `μ(d)` times the smooth envelope frozen at `k*q`. -/
noncomputable def h15NormalizedProgressionPeriodFrozenWeight
    (N g d q u : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
    h15SupportedInverseSmoothEnvelope N g ((u / q) * q)

/-- A point in the normalized `k`-th `q`-period has quotient `u/q=k`. -/
theorem natDiv_eq_periodIndex_of_mem_h15NormalizedProgressionQPeriod
    {k L q u : ℕ}
    (hu : u ∈ h15NormalizedProgressionQPeriod k L q) :
    u / q = k := by
  have huPeriod := (Finset.mem_filter.mp hu).1
  have huRange := Finset.mem_Ico.mp (Finset.mem_filter.mp huPeriod).1
  exact Nat.div_eq_of_lt_le huRange.1 huRange.2

/-- One divisor-first row sum is exactly a pointwise sum on the complete
period support with the period-frozen Möbius weight.  This is the faithful
pointwise realization of the row object; replacing the frozen weight by its
value at `u` would be a different expression. -/
theorem sum_h15WeightedNormalizedRows_eq_frozenPointwise
    {N g r U q d : ℕ} :
    (∑ k ∈ h15CompletePeriodIndices U q,
      h15SupportedInverseSmoothEnvelope N g (k * q) *
        h15PeriodNormalizedProgressionRow g r k q d) =
      ∑ u ∈ h15NormalizedCompletePeriodProgressionSupport U
          (h15SquareDivisorProgressionModulus g d) q,
        h15NormalizedProgressionPeriodFrozenWeight N g d q u *
          h15PairedDirectCrossMode r u q := by
  classical
  unfold h15NormalizedCompletePeriodProgressionSupport
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [h15PeriodNormalizedProgressionRow_eq_supportSum,
      ← mul_assoc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    rw [h15NormalizedProgressionPeriodFrozenWeight,
      natDiv_eq_periodIndex_of_mem_h15NormalizedProgressionQPeriod hu]
    ring
  · apply (h15ReducedNaturalPeriod_pairwiseDisjoint_on
      (h15CompletePeriodIndices U q) q).mono
    intro k
    exact Finset.filter_subset _ _

/-- The full normalized aggregate in its exact frozen pointwise form. -/
noncomputable def h15NormalizedProgressionFrozenPointwiseAggregate
    (N g r U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
      ∑ u ∈ h15NormalizedCompletePeriodProgressionSupport U
          (h15SquareDivisorProgressionModulus g d) q,
        h15NormalizedProgressionPeriodFrozenWeight N g d q u *
          h15PairedDirectCrossMode r u q

theorem h15NormalizedProgressionAggregate_eq_frozenPointwise
    {N g r U Q : ℕ} (hg : 0 < g) (hU : 0 < U) :
    h15NormalizedProgressionAggregate N g r U Q =
      h15NormalizedProgressionFrozenPointwiseAggregate N g r U Q := by
  rw [h15NormalizedProgressionAggregate_eq_dyadicActiveTranspose hg hU]
  unfold h15NormalizedProgressionFrozenPointwiseAggregate
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro d _hd
  exact sum_h15WeightedNormalizedRows_eq_frozenPointwise

/-- The pre-completion pointwise aggregate with the unfrozen smooth H15
weight and the full normalized dyadic support. -/
noncomputable def h15NormalizedProgressionSmoothPointwiseAggregate
    (N g r U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
      h15DyadicNormalizedProgressionWeightedCross r U
        (h15SquareDivisorProgressionModulus g d) q
        (h15NormalizedProgressionSmoothWeight N g d)

/-- Exact discrepancy between the genuine full pointwise object and the
period-frozen complete-row object.  It includes both smooth unfreezing and
the incomplete outer `q`-periods; no claim that it vanishes is made. -/
noncomputable def h15NormalizedProgressionRowToPointwiseResidual
    (N g r U Q : ℕ) : ℝ :=
  h15NormalizedProgressionSmoothPointwiseAggregate N g r U Q -
    h15NormalizedProgressionFrozenPointwiseAggregate N g r U Q

/-- Pointwise superperiod completion of the unfrozen smooth aggregate, with
variation and boundary retained inside each active `q,d` summand. -/
noncomputable def h15NormalizedProgressionPointwiseCoupledAggregate
    (N g r U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
      (h15DyadicNormalizedSuperperiodVariationDefect r U
          (h15SquareDivisorProgressionModulus g d) q
          (h15NormalizedProgressionSmoothWeight N g d)
          (fun j => h15NormalizedProgressionSmoothWeight N g d
            (j * (h15SquareDivisorProgressionModulus g d * q))) +
        h15DyadicNormalizedSuperperiodBoundaryDefect r U
          (h15SquareDivisorProgressionModulus g d) q
          (h15NormalizedProgressionSmoothWeight N g d))

theorem h15NormalizedProgressionSmoothPointwiseAggregate_eq_coupled
    {N g r U Q : ℕ} (hQ : 0 < Q) :
    h15NormalizedProgressionSmoothPointwiseAggregate N g r U Q =
      h15NormalizedProgressionPointwiseCoupledAggregate N g r U Q := by
  unfold h15NormalizedProgressionSmoothPointwiseAggregate
    h15NormalizedProgressionPointwiseCoupledAggregate
  apply Finset.sum_congr rfl
  intro q hq
  have hqBounds := mem_h15BettinChandeeSupportedNatBlock.mp hq
  have hqPos : 0 < q := hQ.trans_le hqBounds.1
  apply Finset.sum_congr rfl
  intro d hd
  have hd' := hd
  rw [h15DyadicActivePeriodSquareDivisorIndices,
    Finset.mem_biUnion] at hd'
  obtain ⟨k, _hk, hdk⟩ := hd'
  have hactive := mem_h15ActivePeriodSquareDivisorIndices.mp hdk
  have hLPos : 0 < h15SquareDivisorProgressionModulus g d := by omega
  exact h15DyadicNormalizedProgressionWeightedCross_eq_variation_add_boundary
    r U (h15SquareDivisorProgressionModulus g d) q
      (h15NormalizedProgressionSmoothWeight N g d)
      (fun j => h15NormalizedProgressionSmoothWeight N g d
        (j * (h15SquareDivisorProgressionModulus g d * q)))
      hLPos hqPos hactive.2.2

/-- Corrected Step 4v-d bridge.  The row-indexed coupled expression agrees
with the full pointwise coupled expression only after adding the explicit
row-to-pointwise residual.  This theorem records, rather than hides, the
frozen-weight and endpoint-support mismatch. -/
theorem h15CoupledVariationBoundary_add_rowToPointwiseResidual
    {N g r U Q : ℕ} (hg : 0 < g) (hU : 0 < U) (hQ : 0 < Q) :
    h15NormalizedProgressionCoupledVariationBoundaryAggregate N g r U Q +
        h15NormalizedProgressionRowToPointwiseResidual N g r U Q =
      h15NormalizedProgressionPointwiseCoupledAggregate N g r U Q := by
  rw [← h15NormalizedProgressionAggregate_eq_coupledVariationBoundary
      hg hU hQ,
    h15NormalizedProgressionAggregate_eq_frozenPointwise hg hU,
    ← h15NormalizedProgressionSmoothPointwiseAggregate_eq_coupled hQ]
  unfold h15NormalizedProgressionRowToPointwiseResidual
  ring

/-! ## Exact decomposition of the row-to-pointwise residual -/

/-- Progression points in the incomplete outer ordinary `q`-periods.  This
is the part of the genuine pointwise support which is absent from the
complete-period row realization. -/
def h15NormalizedIncompletePeriodProgressionSupport
    (U L q : ℕ) : Finset ℕ :=
  h15NormalizedProgressionDyadicSupport U L q \
    h15NormalizedCompletePeriodProgressionSupport U L q

/-- Filtering the union of complete ordinary periods by `L ∣ u` is exactly
the complete-period normalized progression support. -/
theorem h15NormalizedCompletePeriodProgressionSupport_eq_filter
    (U L q : ℕ) :
    h15NormalizedCompletePeriodProgressionSupport U L q =
      (h15CompletePeriodSupport U q).filter fun u => L ∣ u := by
  ext u
  simp only [h15NormalizedCompletePeriodProgressionSupport,
    h15CompletePeriodSupport, h15NormalizedProgressionQPeriod,
    Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨k, hk, hu, hLu⟩
    exact ⟨⟨k, hk, hu⟩, hLu⟩
  · rintro ⟨⟨k, hk, hu⟩, hLu⟩
    exact ⟨k, hk, hu, hLu⟩

/-- Complete-period normalized progression support lies in the genuine
normalized dyadic support. -/
theorem h15NormalizedCompletePeriodProgressionSupport_subset_dyadic
    (U L q : ℕ) :
    h15NormalizedCompletePeriodProgressionSupport U L q ⊆
      h15NormalizedProgressionDyadicSupport U L q := by
  intro u hu
  rw [h15NormalizedCompletePeriodProgressionSupport_eq_filter] at hu
  rw [h15NormalizedProgressionDyadicSupport]
  exact Finset.mem_filter.mpr
    ⟨h15CompletePeriodSupport_subset_reducedDyadic U q
      (Finset.mem_filter.mp hu).1,
      (Finset.mem_filter.mp hu).2⟩

/-- The missing normalized support is precisely the established ordinary
completion boundary, with the progression condition retained. -/
theorem h15NormalizedIncompletePeriodProgressionSupport_eq_filter_boundary
    (U L q : ℕ) :
    h15NormalizedIncompletePeriodProgressionSupport U L q =
      (h15CompletionBoundarySupport U q).filter fun u => L ∣ u := by
  rw [h15NormalizedIncompletePeriodProgressionSupport,
    h15NormalizedCompletePeriodProgressionSupport_eq_filter,
    h15NormalizedProgressionDyadicSupport, h15CompletionBoundarySupport]
  ext u
  simp only [Finset.mem_sdiff, Finset.mem_filter]
  aesop

/-- Exact split of the normalized dyadic support into complete ordinary
periods and the filtered endpoint fragments. -/
theorem sum_h15NormalizedProgressionDyadic_eq_completePeriod_add_incomplete
    (U L q : ℕ) (F : ℕ → ℝ) :
    (∑ u ∈ h15NormalizedProgressionDyadicSupport U L q, F u) =
      (∑ u ∈ h15NormalizedCompletePeriodProgressionSupport U L q, F u) +
        ∑ u ∈ h15NormalizedIncompletePeriodProgressionSupport U L q, F u := by
  have hsplit := Finset.sum_sdiff
    (h15NormalizedCompletePeriodProgressionSupport_subset_dyadic U L q)
    (f := F)
  unfold h15NormalizedIncompletePeriodProgressionSupport
  linarith

/-- Smooth-envelope variation caused solely by unfreezing the row weight
inside the complete ordinary periods. -/
noncomputable def h15NormalizedProgressionSmoothUnfreezingRow
    (N g r U L q d : ℕ) : ℝ :=
  ∑ u ∈ h15NormalizedCompletePeriodProgressionSupport U L q,
    (h15NormalizedProgressionSmoothWeight N g d u -
      h15NormalizedProgressionPeriodFrozenWeight N g d q u) *
        h15PairedDirectCrossMode r u q

/-- The genuine smooth contribution on the two incomplete ordinary
`q`-period fragments. -/
noncomputable def h15NormalizedProgressionIncompleteEndpointRow
    (N g r U L q d : ℕ) : ℝ :=
  ∑ u ∈ h15NormalizedIncompletePeriodProgressionSupport U L q,
    h15NormalizedProgressionSmoothWeight N g d u *
      h15PairedDirectCrossMode r u q

/-- Row-level exact residual split: smooth unfreezing on the complete
periods plus the retained incomplete-period endpoint contribution. -/
theorem h15DyadicSmooth_sub_frozen_eq_unfreezing_add_incomplete
    (N g r U L q d : ℕ) :
    h15DyadicNormalizedProgressionWeightedCross r U L q
        (h15NormalizedProgressionSmoothWeight N g d) -
      (∑ u ∈ h15NormalizedCompletePeriodProgressionSupport U L q,
        h15NormalizedProgressionPeriodFrozenWeight N g d q u *
          h15PairedDirectCrossMode r u q) =
      h15NormalizedProgressionSmoothUnfreezingRow N g r U L q d +
        h15NormalizedProgressionIncompleteEndpointRow N g r U L q d := by
  unfold h15DyadicNormalizedProgressionWeightedCross
  rw [sum_h15NormalizedProgressionDyadic_eq_completePeriod_add_incomplete]
  unfold h15NormalizedProgressionSmoothUnfreezingRow
    h15NormalizedProgressionIncompleteEndpointRow
  calc
    ((∑ u ∈ h15NormalizedCompletePeriodProgressionSupport U L q,
          h15NormalizedProgressionSmoothWeight N g d u *
            h15PairedDirectCrossMode r u q) +
        ∑ u ∈ h15NormalizedIncompletePeriodProgressionSupport U L q,
          h15NormalizedProgressionSmoothWeight N g d u *
            h15PairedDirectCrossMode r u q) -
        ∑ u ∈ h15NormalizedCompletePeriodProgressionSupport U L q,
          h15NormalizedProgressionPeriodFrozenWeight N g d q u *
            h15PairedDirectCrossMode r u q =
      ((∑ u ∈ h15NormalizedCompletePeriodProgressionSupport U L q,
          h15NormalizedProgressionSmoothWeight N g d u *
            h15PairedDirectCrossMode r u q) -
        ∑ u ∈ h15NormalizedCompletePeriodProgressionSupport U L q,
          h15NormalizedProgressionPeriodFrozenWeight N g d q u *
            h15PairedDirectCrossMode r u q) +
        ∑ u ∈ h15NormalizedIncompletePeriodProgressionSupport U L q,
          h15NormalizedProgressionSmoothWeight N g d u *
            h15PairedDirectCrossMode r u q := by ring
    _ = _ := by
      rw [← Finset.sum_sub_distrib]
      apply congrArg (fun x : ℝ => x +
        ∑ u ∈ h15NormalizedIncompletePeriodProgressionSupport U L q,
          h15NormalizedProgressionSmoothWeight N g d u *
            h15PairedDirectCrossMode r u q)
      apply Finset.sum_congr rfl
      intro u _hu
      ring

/-- The smooth-unfreezing row is an ordinary-period variation sum.  This
exhibits the first residual piece in the same local geometry as the earlier
Ramanujan smooth-envelope defect, but with the fixed divisor-row Möbius
coefficient and progression filter retained. -/
theorem h15NormalizedProgressionSmoothUnfreezingRow_eq_periods
    (N g r U L q d : ℕ) :
    h15NormalizedProgressionSmoothUnfreezingRow N g r U L q d =
      ∑ k ∈ h15CompletePeriodIndices U q,
        ∑ u ∈ h15NormalizedProgressionQPeriod k L q,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
            (h15SupportedInverseSmoothEnvelope N g u -
              h15SupportedInverseSmoothEnvelope N g (k * q)) *
              h15PairedDirectCrossMode r u q := by
  classical
  unfold h15NormalizedProgressionSmoothUnfreezingRow
    h15NormalizedCompletePeriodProgressionSupport
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro k _hk
    apply Finset.sum_congr rfl
    intro u hu
    rw [h15NormalizedProgressionSmoothWeight,
      h15NormalizedProgressionPeriodFrozenWeight,
      natDiv_eq_periodIndex_of_mem_h15NormalizedProgressionQPeriod hu]
    ring
  · apply (h15ReducedNaturalPeriod_pairwiseDisjoint_on
      (h15CompletePeriodIndices U q) q).mono
    intro k
    exact Finset.filter_subset _ _

/-- The second residual row is exactly the smooth H15 weight on the old
ordinary-period completion boundary, restricted to `L ∣ u`. -/
theorem h15NormalizedProgressionIncompleteEndpointRow_eq_filter_boundary
    (N g r U L q d : ℕ) :
    h15NormalizedProgressionIncompleteEndpointRow N g r U L q d =
      ∑ u ∈ (h15CompletionBoundarySupport U q).filter (fun u => L ∣ u),
        h15NormalizedProgressionSmoothWeight N g d u *
          h15PairedDirectCrossMode r u q := by
  unfold h15NormalizedProgressionIncompleteEndpointRow
  rw [h15NormalizedIncompletePeriodProgressionSupport_eq_filter_boundary]

/-- The incomplete normalized progression contains at most the `2q` points
of the established ordinary-period completion boundary. -/
theorem card_h15NormalizedIncompletePeriodProgressionSupport_le
    (U L q : ℕ) (hq : 0 < q) :
    (h15NormalizedIncompletePeriodProgressionSupport U L q).card ≤ 2 * q := by
  rw [h15NormalizedIncompletePeriodProgressionSupport_eq_filter_boundary]
  exact (Finset.card_filter_le _ _).trans
    (card_h15CompletionBoundarySupport_le U q hq)

/-- Absolute endpoint audit for one residual row.  This estimate preserves
the sharper ordinary-period factor `2q`, rather than the normalized
superperiod factor `2(q+1)`. -/
theorem abs_h15NormalizedProgressionIncompleteEndpointRow_le
    {N g r U L q d : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g)
    (hU : 0 < U) (hq : 0 < q) :
    |h15NormalizedProgressionIncompleteEndpointRow N g r U L q d| ≤
      (2 * q : ℝ) * (1 / (U : ℝ)) ^ 2 := by
  unfold h15NormalizedProgressionIncompleteEndpointRow
  calc
    |∑ u ∈ h15NormalizedIncompletePeriodProgressionSupport U L q,
        h15NormalizedProgressionSmoothWeight N g d u *
          h15PairedDirectCrossMode r u q| ≤
      ∑ u ∈ h15NormalizedIncompletePeriodProgressionSupport U L q,
        |h15NormalizedProgressionSmoothWeight N g d u *
          h15PairedDirectCrossMode r u q| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _u ∈ h15NormalizedIncompletePeriodProgressionSupport U L q,
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
    _ = ((h15NormalizedIncompletePeriodProgressionSupport U L q).card : ℝ) *
        (1 / (U : ℝ)) ^ 2 := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * q : ℝ) * (1 / (U : ℝ)) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_h15NormalizedIncompletePeriodProgressionSupport_le
        U L q hq

/-- Full signed smooth-unfreezing aggregate. -/
noncomputable def h15NormalizedProgressionSmoothUnfreezingAggregate
    (N g r U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
      h15NormalizedProgressionSmoothUnfreezingRow N g r U
        (h15SquareDivisorProgressionModulus g d) q d

/-- Full signed contribution of the incomplete ordinary-period fragments. -/
noncomputable def h15NormalizedProgressionIncompleteEndpointAggregate
    (N g r U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
      h15NormalizedProgressionIncompleteEndpointRow N g r U
        (h15SquareDivisorProgressionModulus g d) q d

/-- The full incomplete-period residual is controlled by the already
audited density boundary budget.  The latter grows linearly on balanced
blocks, so this theorem is a stop test rather than a decay result. -/
theorem abs_h15NormalizedProgressionIncompleteEndpointAggregate_le_densityBudget
    {N g r U Q : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g)
    (hU : 0 < U) (hQ : 0 < Q) :
    |h15NormalizedProgressionIncompleteEndpointAggregate N g r U Q| ≤
      h15NormalizedDensityBoundaryAbsoluteBudget N g U Q := by
  unfold h15NormalizedProgressionIncompleteEndpointAggregate
    h15NormalizedDensityBoundaryAbsoluteBudget
    h15NormalizedDensityBoundaryRowBudget
    h15NormalizedSuperperiodDensityBoundaryBudget
  calc
    |∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
          h15NormalizedProgressionIncompleteEndpointRow N g r U
            (h15SquareDivisorProgressionModulus g d) q d| ≤
      ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        |∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
          h15NormalizedProgressionIncompleteEndpointRow N g r U
            (h15SquareDivisorProgressionModulus g d) q d| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
          |h15NormalizedProgressionIncompleteEndpointRow N g r U
            (h15SquareDivisorProgressionModulus g d) q d| := by
      apply Finset.sum_le_sum
      intro q _hq
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        ∑ _d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
          (2 * (q + 1) : ℝ) * (1 / (U : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro q hqMem
      have hqBounds := mem_h15BettinChandeeSupportedNatBlock.mp hqMem
      have hqPos : 0 < q := hQ.trans_le hqBounds.1
      apply Finset.sum_le_sum
      intro d _hd
      calc
        |h15NormalizedProgressionIncompleteEndpointRow N g r U
            (h15SquareDivisorProgressionModulus g d) q d| ≤
          (2 * q : ℝ) * (1 / (U : ℝ)) ^ 2 :=
            abs_h15NormalizedProgressionIncompleteEndpointRow_le
              hN hg hU hqPos
        _ ≤ (2 * (q + 1) : ℝ) * (1 / (U : ℝ)) ^ 2 := by
          gcongr
          norm_num
    _ = _ := rfl

theorem abs_h15NormalizedProgressionIncompleteEndpointAggregate_le
    {N g r U Q : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g)
    (hU : 0 < U) (hQ : 0 < Q) (hQU : Q ≤ U) :
    |h15NormalizedProgressionIncompleteEndpointAggregate N g r U Q| ≤
      8 * (g.divisors.card : ℝ) * (Q : ℝ) :=
  (abs_h15NormalizedProgressionIncompleteEndpointAggregate_le_densityBudget
    hN hg hU hQ).trans
      (h15NormalizedDensityBoundaryAbsoluteBudget_le
        (Nat.zero_lt_of_lt hg) hU hQU)

/-- Exact Step 4v-e decomposition of the row-to-pointwise residual.  Both
pieces remain signed; no absolute estimate is used. -/
theorem h15NormalizedProgressionRowToPointwiseResidual_eq_unfreezing_add_incomplete
    (N g r U Q : ℕ) :
    h15NormalizedProgressionRowToPointwiseResidual N g r U Q =
      h15NormalizedProgressionSmoothUnfreezingAggregate N g r U Q +
        h15NormalizedProgressionIncompleteEndpointAggregate N g r U Q := by
  classical
  unfold h15NormalizedProgressionRowToPointwiseResidual
    h15NormalizedProgressionSmoothPointwiseAggregate
    h15NormalizedProgressionFrozenPointwiseAggregate
    h15NormalizedProgressionSmoothUnfreezingAggregate
    h15NormalizedProgressionIncompleteEndpointAggregate
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _hd
  exact h15DyadicSmooth_sub_frozen_eq_unfreezing_add_incomplete
    N g r U (h15SquareDivisorProgressionModulus g d) q d

end NBMellinTools.NB12
