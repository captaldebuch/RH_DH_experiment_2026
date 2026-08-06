/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FinalBoundaryCongruenceShells

/-!
# NB12zzh: correction-preserving congruence-shell majorants

This file identifies the weakest pointwise absolute shell-majorant route to
the final dispersion gate.  Crucially, the collision defect remains in the
same inequality as the shell budget.  The resulting equivalence is also a
stop test: choosing more elaborate pointwise majorants cannot improve on the
canonical sum of absolute signed shell ledgers.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate
open Complex

namespace NBMellinTools.NB12

/-- Canonical absolute budget of the already signed difference-minus-sum
congruence shells.  The sign coupling inside each shell is retained, while
cancellation between distinct shells is discarded. -/
noncomputable def h15NormalizedBoundaryAbsoluteSignedShellBudget
    (N g r U Q : ℕ) : ℝ :=
  ∑ e : Fin (h15BoundarySpacingShellCount Q),
    |h15NormalizedBoundarySignedCongruenceShellLedger N g r U Q e|

theorem h15NormalizedBoundaryAbsoluteSignedShellBudget_nonneg
    (N g r U Q : ℕ) :
    0 ≤ h15NormalizedBoundaryAbsoluteSignedShellBudget N g r U Q := by
  unfold h15NormalizedBoundaryAbsoluteSignedShellBudget
  exact Finset.sum_nonneg (fun _e _he => abs_nonneg _)

theorem sum_signedShells_le_absoluteSignedShellBudget
    (N g r U Q : ℕ) :
    (∑ e : Fin (h15BoundarySpacingShellCount Q),
        h15NormalizedBoundarySignedCongruenceShellLedger N g r U Q e) ≤
      h15NormalizedBoundaryAbsoluteSignedShellBudget N g r U Q := by
  unfold h15NormalizedBoundaryAbsoluteSignedShellBudget
  calc
    (∑ e : Fin (h15BoundarySpacingShellCount Q),
        h15NormalizedBoundarySignedCongruenceShellLedger N g r U Q e) ≤
        |∑ e : Fin (h15BoundarySpacingShellCount Q),
          h15NormalizedBoundarySignedCongruenceShellLedger N g r U Q e| :=
      le_abs_self _
    _ ≤ ∑ e : Fin (h15BoundarySpacingShellCount Q),
        |h15NormalizedBoundarySignedCongruenceShellLedger N g r U Q e| :=
      Finset.abs_sum_le_sum_abs _ _

/-- A pointwise absolute shell-majorant certificate.  Its total estimate is
correction preserving: the collision defect is not estimated separately or
dropped. -/
def H15CorrectionCoupledCongruenceShellMajorant
    (N g r U Q : ℕ) (Delta : ℝ) : Prop :=
  ∃ B : Fin (h15BoundarySpacingShellCount Q) → ℝ,
    (∀ e, |h15NormalizedBoundarySignedCongruenceShellLedger N g r U Q e| ≤ B e) ∧
      (∑ e, B e) +
          h15NormalizedBoundaryPhaseCollisionDefect N g r U Q ≤
        Delta * h15NormalizedBoundaryCrossModulusFrequencyEnergy N g U Q

/-- The canonical absolute shell budget is the minimal possible pointwise
majorant total.  Thus no alternative pointwise absolute majorant can evade
this stop test. -/
theorem h15CorrectionCoupledCongruenceShellMajorant_iff_absoluteBudget
    (N g r U Q : ℕ) (Delta : ℝ) :
    H15CorrectionCoupledCongruenceShellMajorant N g r U Q Delta ↔
      h15NormalizedBoundaryAbsoluteSignedShellBudget N g r U Q +
          h15NormalizedBoundaryPhaseCollisionDefect N g r U Q ≤
        Delta * h15NormalizedBoundaryCrossModulusFrequencyEnergy N g U Q := by
  constructor
  · rintro ⟨B, hB, htotal⟩
    have hsum :
        h15NormalizedBoundaryAbsoluteSignedShellBudget N g r U Q ≤
          ∑ e : Fin (h15BoundarySpacingShellCount Q), B e := by
      unfold h15NormalizedBoundaryAbsoluteSignedShellBudget
      exact Finset.sum_le_sum (fun e _he => hB e)
    linarith
  · intro hbudget
    refine ⟨fun e =>
      |h15NormalizedBoundarySignedCongruenceShellLedger N g r U Q e|,
      ?_, ?_⟩
    · exact fun _e => le_rfl
    · simpa only [h15NormalizedBoundaryAbsoluteSignedShellBudget] using hbudget

/-- Any correction-preserving pointwise shell majorant with a nonnegative
dispersion coefficient supplies the exact H15 cross-modulus dispersion gate. -/
theorem h15CorrectionCoupledCrossModulusFrequencyDispersion_of_shellMajorant
    {N g r U Q : ℕ} (hQ : 0 < Q) {Delta : ℝ} (hDelta : 0 ≤ Delta)
    (hmajorant :
      H15CorrectionCoupledCongruenceShellMajorant N g r U Q Delta) :
    H15CorrectionCoupledCrossModulusFrequencyDispersion N g r U Q Delta := by
  rw [h15CorrectionCoupledCrossModulusFrequencyDispersion_iff_signedShells hQ]
  refine ⟨hDelta, ?_⟩
  rw [h15CorrectionCoupledCongruenceShellMajorant_iff_absoluteBudget] at hmajorant
  have hshell := sum_signedShells_le_absoluteSignedShellBudget N g r U Q
  linarith

/-- Direct form of the absolute-budget route, useful when the analytic input
already estimates the canonical shell sum. -/
theorem h15CorrectionCoupledCrossModulusFrequencyDispersion_of_absoluteShellBudget
    {N g r U Q : ℕ} (hQ : 0 < Q) {Delta : ℝ} (hDelta : 0 ≤ Delta)
    (hbudget :
      h15NormalizedBoundaryAbsoluteSignedShellBudget N g r U Q +
          h15NormalizedBoundaryPhaseCollisionDefect N g r U Q ≤
        Delta * h15NormalizedBoundaryCrossModulusFrequencyEnergy N g U Q) :
    H15CorrectionCoupledCrossModulusFrequencyDispersion N g r U Q Delta := by
  apply h15CorrectionCoupledCrossModulusFrequencyDispersion_of_shellMajorant
    hQ hDelta
  rw [h15CorrectionCoupledCongruenceShellMajorant_iff_absoluteBudget]
  exact hbudget

end NBMellinTools.NB12
