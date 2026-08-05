/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15ActiveIncidence

/-!
# NB12zm: correction-coupled Abel representation of the H15 residual

The row-to-pointwise residual has already been split exactly into smooth
unfreezing on complete ordinary `q`-periods and two incomplete endpoint
fragments.  This file applies finite summation by parts to the unfreezing
piece.  Its coefficients are zero-padded rather than enlarged: the Möbius
factor, progression constraint, and additive character all stay inside the
same partial sum.

The terminal Abel contribution is then coupled to the incomplete endpoint
before any absolute value is taken.  The output is an exact decomposition
into an interior first-difference term and one correction-coupled boundary
ledger.  No decay estimate is asserted here.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius
open Complex

namespace NBMellinTools.NB12

/-! ## Generic finite Abel identity -/

/-- One-dimensional finite summation by parts in inclusive-prefix form. -/
theorem h15_sum_range_succ_mul_eq_endpoint_add_prefix
    (a K : ℕ → ℝ) (M : ℕ) :
    (∑ i ∈ Finset.range (M + 1), a i * K i) =
      (∑ i ∈ Finset.range (M + 1), a i) * K M +
        ∑ i ∈ Finset.range M,
          (∑ j ∈ Finset.range (i + 1), a j) * (K i - K (i + 1)) := by
  have h := Finset.sum_range_by_parts K a (M + 1)
  simp only [smul_eq_mul, Nat.add_sub_cancel] at h
  calc
    (∑ i ∈ Finset.range (M + 1), a i * K i) =
        ∑ i ∈ Finset.range (M + 1), K i * a i := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = K M * (∑ i ∈ Finset.range (M + 1), a i) -
        ∑ i ∈ Finset.range M,
          (K (i + 1) - K i) * (∑ j ∈ Finset.range (i + 1), a j) := h
    _ = _ := by
      rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      · ring
      apply Finset.sum_congr rfl
      intro i _hi
      ring

/-! ## One complete ordinary period -/

/-- Zero-padded signed arithmetic coefficient on the translated period.
It retains `μ(d)`, the progression condition `L ∣ kq+i`, coprimality, and
the direct additive character in one coefficient. -/
noncomputable def h15NormalizedProgressionAbelCoefficient
    (r k L q d i : ℕ) : ℝ :=
  if Nat.Coprime (k * q + i) q ∧ L ∣ k * q + i then
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      h15PairedDirectCrossMode r (k * q + i) q
  else 0

/-- Smooth-envelope displacement from the left endpoint of one ordinary
`q`-period. -/
noncomputable def h15NormalizedProgressionEnvelopeIncrement
    (N g k q i : ℕ) : ℝ :=
  h15SupportedInverseSmoothEnvelope N g (k * q + i) -
    h15SupportedInverseSmoothEnvelope N g (k * q)

/-- Inclusive arithmetic prefix entering finite Abel summation. -/
noncomputable def h15NormalizedProgressionAbelPrefix
    (r k L q d i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (i + 1),
    h15NormalizedProgressionAbelCoefficient r k L q d j

/-- Reindex one filtered progression-period variation as a zero-padded sum
on `range q`. -/
theorem sum_h15NormalizedProgressionPeriod_unfreezing_eq_range
    (N g r k L q d : ℕ) :
    (∑ u ∈ h15NormalizedProgressionQPeriod k L q,
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        (h15SupportedInverseSmoothEnvelope N g u -
          h15SupportedInverseSmoothEnvelope N g (k * q)) *
          h15PairedDirectCrossMode r u q) =
      ∑ i ∈ Finset.range q,
        h15NormalizedProgressionAbelCoefficient r k L q d i *
          h15NormalizedProgressionEnvelopeIncrement N g k q i := by
  unfold h15NormalizedProgressionQPeriod h15ReducedNaturalPeriod
    h15NormalizedProgressionAbelCoefficient
    h15NormalizedProgressionEnvelopeIncrement
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_Ico_eq_sum_range]
  have hlength : (k + 1) * q - k * q = q := by
    simp [Nat.add_mul]
  rw [hlength]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hcop : Nat.Coprime (k * q + i) q
  · by_cases hdiv : L ∣ k * q + i
    · simp [hdiv]
      ring
    · simp [hdiv]
  · simp [hcop]

/-- Exact Abel transform of one complete ordinary progression period. -/
theorem sum_h15NormalizedProgressionPeriod_unfreezing_eq_abel
    (N g r k L q d : ℕ) :
    (∑ u ∈ h15NormalizedProgressionQPeriod k L q,
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        (h15SupportedInverseSmoothEnvelope N g u -
          h15SupportedInverseSmoothEnvelope N g (k * q)) *
          h15PairedDirectCrossMode r u q) =
      (∑ i ∈ Finset.range q,
        h15NormalizedProgressionAbelCoefficient r k L q d i) *
          h15NormalizedProgressionEnvelopeIncrement N g k q (q - 1) +
        ∑ i ∈ Finset.range (q - 1),
          h15NormalizedProgressionAbelPrefix r k L q d i *
            (h15NormalizedProgressionEnvelopeIncrement N g k q i -
              h15NormalizedProgressionEnvelopeIncrement N g k q (i + 1)) := by
  rw [sum_h15NormalizedProgressionPeriod_unfreezing_eq_range]
  cases q with
  | zero => simp [h15NormalizedProgressionAbelPrefix]
  | succ M =>
      simpa [h15NormalizedProgressionAbelPrefix] using
        h15_sum_range_succ_mul_eq_endpoint_add_prefix
          (h15NormalizedProgressionAbelCoefficient r k L (M + 1) d)
          (h15NormalizedProgressionEnvelopeIncrement N g k (M + 1)) M

/-! ## Dyadic rows and correction-coupled boundary -/

/-- Interior first-difference contribution after Abel summation. -/
noncomputable def h15NormalizedProgressionAbelInteriorRow
    (N g r U L q d : ℕ) : ℝ :=
  ∑ k ∈ h15CompletePeriodIndices U q,
    ∑ i ∈ Finset.range (q - 1),
      h15NormalizedProgressionAbelPrefix r k L q d i *
        (h15NormalizedProgressionEnvelopeIncrement N g k q i -
          h15NormalizedProgressionEnvelopeIncrement N g k q (i + 1))

/-- Terminal contribution from all complete ordinary periods. -/
noncomputable def h15NormalizedProgressionAbelTerminalRow
    (N g r U L q d : ℕ) : ℝ :=
  ∑ k ∈ h15CompletePeriodIndices U q,
    (∑ i ∈ Finset.range q,
      h15NormalizedProgressionAbelCoefficient r k L q d i) *
        h15NormalizedProgressionEnvelopeIncrement N g k q (q - 1)

theorem h15NormalizedProgressionSmoothUnfreezingRow_eq_abel
    (N g r U L q d : ℕ) :
    h15NormalizedProgressionSmoothUnfreezingRow N g r U L q d =
      h15NormalizedProgressionAbelTerminalRow N g r U L q d +
        h15NormalizedProgressionAbelInteriorRow N g r U L q d := by
  rw [h15NormalizedProgressionSmoothUnfreezingRow_eq_periods]
  unfold h15NormalizedProgressionAbelTerminalRow
    h15NormalizedProgressionAbelInteriorRow
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  exact sum_h15NormalizedProgressionPeriod_unfreezing_eq_abel
    N g r k L q d

/-- The Abel terminal and incomplete ordinary-period endpoint are retained
as one signed correction-coupled boundary row. -/
noncomputable def h15NormalizedProgressionCorrectionCoupledAbelBoundaryRow
    (N g r U L q d : ℕ) : ℝ :=
  h15NormalizedProgressionAbelTerminalRow N g r U L q d +
    h15NormalizedProgressionIncompleteEndpointRow N g r U L q d

/-- Full signed Abel interior aggregate. -/
noncomputable def h15NormalizedProgressionAbelInteriorAggregate
    (N g r U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
      h15NormalizedProgressionAbelInteriorRow N g r U
        (h15SquareDivisorProgressionModulus g d) q d

/-- Full correction-coupled Abel boundary aggregate. -/
noncomputable def h15NormalizedProgressionCorrectionCoupledAbelBoundaryAggregate
    (N g r U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
      h15NormalizedProgressionCorrectionCoupledAbelBoundaryRow N g r U
        (h15SquareDivisorProgressionModulus g d) q d

/-- Exact Step 4v-f identity: the entire row-to-pointwise residual is an
Abel interior plus one signed boundary ledger. -/
theorem h15NormalizedProgressionRowToPointwiseResidual_eq_abelInterior_add_boundary
    (N g r U Q : ℕ) :
    h15NormalizedProgressionRowToPointwiseResidual N g r U Q =
      h15NormalizedProgressionAbelInteriorAggregate N g r U Q +
        h15NormalizedProgressionCorrectionCoupledAbelBoundaryAggregate
          N g r U Q := by
  rw [h15NormalizedProgressionRowToPointwiseResidual_eq_unfreezing_add_incomplete]
  unfold h15NormalizedProgressionSmoothUnfreezingAggregate
    h15NormalizedProgressionIncompleteEndpointAggregate
    h15NormalizedProgressionAbelInteriorAggregate
    h15NormalizedProgressionCorrectionCoupledAbelBoundaryAggregate
    h15NormalizedProgressionCorrectionCoupledAbelBoundaryRow
  simp_rw [h15NormalizedProgressionSmoothUnfreezingRow_eq_abel]
  simp_rw [Finset.sum_add_distrib]
  ring

/-- The previous row-coupled expression, Abel interior, and Abel boundary
together recover the genuine pointwise coupled H15 aggregate. -/
theorem h15CoupledVariationBoundary_add_abelInterior_add_boundary
    {N g r U Q : ℕ} (hg : 0 < g) (hU : 0 < U) (hQ : 0 < Q) :
    h15NormalizedProgressionCoupledVariationBoundaryAggregate N g r U Q +
        h15NormalizedProgressionAbelInteriorAggregate N g r U Q +
        h15NormalizedProgressionCorrectionCoupledAbelBoundaryAggregate
          N g r U Q =
      h15NormalizedProgressionPointwiseCoupledAggregate N g r U Q := by
  have hbridge := h15CoupledVariationBoundary_add_rowToPointwiseResidual
    (N := N) (g := g) (r := r) (U := U) (Q := Q) hg hU hQ
  rw [h15NormalizedProgressionRowToPointwiseResidual_eq_abelInterior_add_boundary]
    at hbridge
  linarith

end NBMellinTools.NB12
