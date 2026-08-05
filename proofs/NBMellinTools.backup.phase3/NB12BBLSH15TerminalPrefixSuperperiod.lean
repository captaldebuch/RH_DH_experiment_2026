/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15AbelVariationThreshold

/-!
# NB12zo: terminal Abel prefixes on normalized superperiods

The terminal coefficient of one ordinary `q`-period is not a new arithmetic
object: for the active progression modulus it is exactly the normalized H15
row already proved to have zero mean across `L` consecutive periods.  This
file records that identification and reapplies the normalized-superperiod
completion to the weighted terminal Abel sum.

Thus the terminal constant mode cancels exactly.  Its varying smooth weight
becomes a within-superperiod variation, while the uncovered terminal rows
and the incomplete pointwise endpoints remain in one signed boundary ledger.
No decay estimate is asserted.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius
open Complex

namespace NBMellinTools.NB12

/-! ## Terminal prefix identification -/

/-- The complete zero-padded Abel coefficient sum is exactly the normalized
H15 progression row when `L` is the row's progression modulus. -/
theorem sum_h15NormalizedProgressionAbelCoefficient_eq_normalizedRow
    (g r k q d : ℕ) :
    (∑ i ∈ Finset.range q,
      h15NormalizedProgressionAbelCoefficient r k
        (h15SquareDivisorProgressionModulus g d) q d i) =
      h15PeriodNormalizedProgressionRow g r k q d := by
  rw [h15PeriodNormalizedProgressionRow_eq_supportSum]
  unfold h15NormalizedProgressionAbelCoefficient
    h15NormalizedProgressionQPeriod h15ReducedNaturalPeriod
  rw [Finset.mul_sum]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_Ico_eq_sum_range]
  have hlength : (k + 1) * q - k * q = q := by
    simp [Nat.add_mul]
  rw [hlength]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hcop : Nat.Coprime (k * q + i) q
  · by_cases hdiv : h15SquareDivisorProgressionModulus g d ∣ k * q + i
    · simp [hdiv]
    · simp [hdiv]
  · simp [hcop]

/-- The terminal zero-padded prefixes have exact mean zero over every
complete normalized superperiod. -/
theorem sum_h15NormalizedProgressionAbelTerminalPrefix_superperiod_eq_zero
    (g r j q d : ℕ) (hq : 0 < q)
    (hL : 0 < h15SquareDivisorProgressionModulus g d)
    (hcop : Nat.Coprime (h15SquareDivisorProgressionModulus g d) q) :
    (∑ k ∈ Finset.Ico
        (j * h15SquareDivisorProgressionModulus g d)
        ((j + 1) * h15SquareDivisorProgressionModulus g d),
      ∑ i ∈ Finset.range q,
        h15NormalizedProgressionAbelCoefficient r k
          (h15SquareDivisorProgressionModulus g d) q d i) = 0 := by
  simp_rw [sum_h15NormalizedProgressionAbelCoefficient_eq_normalizedRow]
  exact sum_h15PeriodNormalizedProgressionRow_superperiod_eq_zero
    g r j q d hq hL hcop

/-! ## Recompletion of the varying terminal mode -/

/-- Within-superperiod variation left after the terminal constant mode has
cancelled. -/
noncomputable def h15NormalizedProgressionAbelTerminalSuperperiodVariationRow
    (N g r U q d : ℕ) : ℝ :=
  let L := h15SquareDivisorProgressionModulus g d
  h15NormalizedRowSuperperiodVariationDefect g r U q d
    (fun k => h15NormalizedProgressionEnvelopeIncrement N g k q (q - 1))
    (fun j => h15NormalizedProgressionEnvelopeIncrement N g (j * L) q (q - 1))

/-- The uncovered terminal rows and incomplete pointwise endpoints retained
as one signed normalized-superperiod boundary. -/
noncomputable def h15NormalizedProgressionCorrectionCoupledSuperperiodBoundaryRow
    (N g r U q d : ℕ) : ℝ :=
  let L := h15SquareDivisorProgressionModulus g d
  h15NormalizedRowSuperperiodBoundaryDefect g r U q d
      (fun k => h15NormalizedProgressionEnvelopeIncrement N g k q (q - 1)) +
    h15NormalizedProgressionIncompleteEndpointRow N g r U L q d

/-- Exact row-level Step 4v-h identity.  The terminal prefix constant mode
vanishes over complete normalized superperiods; only its smooth variation
and the coupled outer boundary remain. -/
theorem h15NormalizedProgressionCorrectionCoupledAbelBoundaryRow_eq_superperiod
    (N g r U q d : ℕ) (hq : 0 < q)
    (hL : 0 < h15SquareDivisorProgressionModulus g d)
    (hcop : Nat.Coprime (h15SquareDivisorProgressionModulus g d) q) :
    h15NormalizedProgressionCorrectionCoupledAbelBoundaryRow N g r U
        (h15SquareDivisorProgressionModulus g d) q d =
      h15NormalizedProgressionAbelTerminalSuperperiodVariationRow
          N g r U q d +
        h15NormalizedProgressionCorrectionCoupledSuperperiodBoundaryRow
          N g r U q d := by
  unfold h15NormalizedProgressionCorrectionCoupledAbelBoundaryRow
    h15NormalizedProgressionAbelTerminalRow
    h15NormalizedProgressionAbelTerminalSuperperiodVariationRow
    h15NormalizedProgressionCorrectionCoupledSuperperiodBoundaryRow
  simp_rw [sum_h15NormalizedProgressionAbelCoefficient_eq_normalizedRow]
  have hdecomp := h15NormalizedProgressionRowWeightedSum_eq_variation_add_boundary
    g r U q d
      (fun k => h15NormalizedProgressionEnvelopeIncrement N g k q (q - 1))
      (fun j => h15NormalizedProgressionEnvelopeIncrement N g
        (j * h15SquareDivisorProgressionModulus g d) q (q - 1))
      hq hL hcop
  calc
    (∑ k ∈ h15CompletePeriodIndices U q,
        h15PeriodNormalizedProgressionRow g r k q d *
          h15NormalizedProgressionEnvelopeIncrement N g k q (q - 1)) +
        h15NormalizedProgressionIncompleteEndpointRow N g r U
          (h15SquareDivisorProgressionModulus g d) q d =
      (∑ k ∈ h15CompletePeriodIndices U q,
        h15NormalizedProgressionEnvelopeIncrement N g k q (q - 1) *
          h15PeriodNormalizedProgressionRow g r k q d) +
        h15NormalizedProgressionIncompleteEndpointRow N g r U
          (h15SquareDivisorProgressionModulus g d) q d := by
            apply congrArg (fun x : ℝ => x +
              h15NormalizedProgressionIncompleteEndpointRow N g r U
                (h15SquareDivisorProgressionModulus g d) q d)
            apply Finset.sum_congr rfl
            intro k _hk
            ring
    _ = _ := by rw [hdecomp]; ring

/-! ## Full active aggregate -/

noncomputable def h15NormalizedProgressionAbelTerminalSuperperiodVariationAggregate
    (N g r U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
      h15NormalizedProgressionAbelTerminalSuperperiodVariationRow
        N g r U q d

noncomputable def h15NormalizedProgressionCorrectionCoupledSuperperiodBoundaryAggregate
    (N g r U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
      h15NormalizedProgressionCorrectionCoupledSuperperiodBoundaryRow
        N g r U q d

/-- The complete terminal/incomplete Abel boundary is exactly a
normalized-superperiod smooth variation plus one smaller uncovered-row and
pointwise-endpoint ledger. -/
theorem h15NormalizedProgressionCorrectionCoupledAbelBoundaryAggregate_eq_superperiod
    {N g r U Q : ℕ} (hQ : 0 < Q) :
    h15NormalizedProgressionCorrectionCoupledAbelBoundaryAggregate
        N g r U Q =
      h15NormalizedProgressionAbelTerminalSuperperiodVariationAggregate
          N g r U Q +
        h15NormalizedProgressionCorrectionCoupledSuperperiodBoundaryAggregate
          N g r U Q := by
  unfold h15NormalizedProgressionCorrectionCoupledAbelBoundaryAggregate
    h15NormalizedProgressionAbelTerminalSuperperiodVariationAggregate
    h15NormalizedProgressionCorrectionCoupledSuperperiodBoundaryAggregate
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hqMem
  have hqBounds := mem_h15BettinChandeeSupportedNatBlock.mp hqMem
  have hqPos : 0 < q := hQ.trans_le hqBounds.1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hd' := hd
  rw [h15DyadicActivePeriodSquareDivisorIndices,
    Finset.mem_biUnion] at hd'
  obtain ⟨k, _hk, hdk⟩ := hd'
  have hactive := mem_h15ActivePeriodSquareDivisorIndices.mp hdk
  have hLPos : 0 < h15SquareDivisorProgressionModulus g d := by
    omega
  exact h15NormalizedProgressionCorrectionCoupledAbelBoundaryRow_eq_superperiod
    N g r U q d hqPos hLPos hactive.2.2

/-- Refined Step 4v-h residual decomposition.  Both smooth variations are
explicit; all geometry not covered by complete normalized superperiods is
confined to one final signed boundary ledger. -/
theorem h15NormalizedProgressionRowToPointwiseResidual_eq_twoVariations_add_boundary
    {N g r U Q : ℕ} (hQ : 0 < Q) :
    h15NormalizedProgressionRowToPointwiseResidual N g r U Q =
      h15NormalizedProgressionAbelInteriorAggregate N g r U Q +
        h15NormalizedProgressionAbelTerminalSuperperiodVariationAggregate
          N g r U Q +
        h15NormalizedProgressionCorrectionCoupledSuperperiodBoundaryAggregate
          N g r U Q := by
  rw [h15NormalizedProgressionRowToPointwiseResidual_eq_abelInterior_add_boundary,
    h15NormalizedProgressionCorrectionCoupledAbelBoundaryAggregate_eq_superperiod
      hQ]
  ring

end NBMellinTools.NB12
