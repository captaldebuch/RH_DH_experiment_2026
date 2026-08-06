/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FinalBoundaryShellMajorant

/-!
# NB12zzi: signed arithmetic blocks of congruence shells

Exact residue-distance shells are grouped into quotient windows of width `K`.
This retains cancellation between shells inside each window.  The complete
signed ledger is unchanged, while the blockwise absolute budget can only be
smaller than the shellwise absolute budget.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate
open Complex

namespace NBMellinTools.NB12

def h15BoundarySpacingBlockCount (Q K : ℕ) : ℕ :=
  h15BoundarySpacingShellCount Q / K + 1

theorem h15BoundarySpacingShell_div_lt_blockCount
    {Q K : ℕ} (e : Fin (h15BoundarySpacingShellCount Q)) :
    e.val / K < h15BoundarySpacingBlockCount Q K := by
  unfold h15BoundarySpacingBlockCount
  exact Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt e.isLt))

noncomputable def h15NormalizedBoundarySignedCongruenceShellBlock
    (N g r U Q K : ℕ) (j : Fin (h15BoundarySpacingBlockCount Q K)) : ℝ :=
  ∑ e : Fin (h15BoundarySpacingShellCount Q) with e.val / K = j.val,
    h15NormalizedBoundarySignedCongruenceShellLedger N g r U Q e

theorem h15NormalizedBoundaryPhaseSeparatedLedger_eq_sum_shellBlocks
    {N g r U Q K : ℕ} (hQ : 0 < Q) :
    h15NormalizedBoundaryPhaseSeparatedLedger N g r U Q =
      ∑ j : Fin (h15BoundarySpacingBlockCount Q K),
        h15NormalizedBoundarySignedCongruenceShellBlock N g r U Q K j := by
  rw [h15NormalizedBoundaryPhaseSeparatedLedger_eq_sum_signedShells hQ]
  unfold h15NormalizedBoundarySignedCongruenceShellBlock
  let blockOf (e : Fin (h15BoundarySpacingShellCount Q)) :
      Fin (h15BoundarySpacingBlockCount Q K) :=
    ⟨e.val / K, h15BoundarySpacingShell_div_lt_blockCount e⟩
  simpa only [blockOf, Fin.ext_iff] using
    (Finset.sum_fiberwise
      (Finset.univ : Finset (Fin (h15BoundarySpacingShellCount Q)))
      blockOf
      (fun e =>
        h15NormalizedBoundarySignedCongruenceShellLedger N g r U Q e)).symm

noncomputable def h15NormalizedBoundaryAbsoluteSignedShellBlockBudget
    (N g r U Q K : ℕ) : ℝ :=
  ∑ j : Fin (h15BoundarySpacingBlockCount Q K),
    |h15NormalizedBoundarySignedCongruenceShellBlock N g r U Q K j|

theorem h15NormalizedBoundaryAbsoluteSignedShellBlockBudget_nonneg
    (N g r U Q K : ℕ) :
    0 ≤ h15NormalizedBoundaryAbsoluteSignedShellBlockBudget N g r U Q K := by
  unfold h15NormalizedBoundaryAbsoluteSignedShellBlockBudget
  exact Finset.sum_nonneg (fun _j _hj => abs_nonneg _)

theorem h15NormalizedBoundaryAbsoluteSignedShellBlockBudget_le_shellBudget
    (N g r U Q K : ℕ) :
    h15NormalizedBoundaryAbsoluteSignedShellBlockBudget N g r U Q K ≤
      h15NormalizedBoundaryAbsoluteSignedShellBudget N g r U Q := by
  unfold h15NormalizedBoundaryAbsoluteSignedShellBlockBudget
    h15NormalizedBoundarySignedCongruenceShellBlock
    h15NormalizedBoundaryAbsoluteSignedShellBudget
  let blockOf (e : Fin (h15BoundarySpacingShellCount Q)) :
      Fin (h15BoundarySpacingBlockCount Q K) :=
    ⟨e.val / K, h15BoundarySpacingShell_div_lt_blockCount e⟩
  calc
    (∑ j : Fin (h15BoundarySpacingBlockCount Q K),
        |∑ e : Fin (h15BoundarySpacingShellCount Q) with e.val / K = j.val,
          h15NormalizedBoundarySignedCongruenceShellLedger N g r U Q e|) ≤
        ∑ j : Fin (h15BoundarySpacingBlockCount Q K),
          ∑ e : Fin (h15BoundarySpacingShellCount Q) with e.val / K = j.val,
            |h15NormalizedBoundarySignedCongruenceShellLedger N g r U Q e| := by
      exact Finset.sum_le_sum (fun _j _hj => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ e : Fin (h15BoundarySpacingShellCount Q),
          |h15NormalizedBoundarySignedCongruenceShellLedger N g r U Q e| := by
      simpa only [blockOf, Fin.ext_iff] using
        (Finset.sum_fiberwise
          (Finset.univ : Finset (Fin (h15BoundarySpacingShellCount Q)))
          blockOf
          (fun e =>
            |h15NormalizedBoundarySignedCongruenceShellLedger N g r U Q e|))

theorem sum_signedShellBlocks_le_absoluteSignedShellBlockBudget
    (N g r U Q K : ℕ) :
    (∑ j : Fin (h15BoundarySpacingBlockCount Q K),
        h15NormalizedBoundarySignedCongruenceShellBlock N g r U Q K j) ≤
      h15NormalizedBoundaryAbsoluteSignedShellBlockBudget N g r U Q K := by
  unfold h15NormalizedBoundaryAbsoluteSignedShellBlockBudget
  calc
    (∑ j : Fin (h15BoundarySpacingBlockCount Q K),
        h15NormalizedBoundarySignedCongruenceShellBlock N g r U Q K j) ≤
        |∑ j : Fin (h15BoundarySpacingBlockCount Q K),
          h15NormalizedBoundarySignedCongruenceShellBlock N g r U Q K j| :=
      le_abs_self _
    _ ≤ ∑ j : Fin (h15BoundarySpacingBlockCount Q K),
        |h15NormalizedBoundarySignedCongruenceShellBlock N g r U Q K j| :=
      Finset.abs_sum_le_sum_abs _ _

/-- A correction-preserving blockwise absolute estimate is sufficient for the
original dispersion gate.  Unlike the shellwise estimate, it retains signed
cancellation among all residue distances in each width-`K` block. -/
theorem h15CorrectionCoupledCrossModulusFrequencyDispersion_of_absoluteShellBlockBudget
    {N g r U Q K : ℕ} (hQ : 0 < Q) {Delta : ℝ} (hDelta : 0 ≤ Delta)
    (hbudget :
      h15NormalizedBoundaryAbsoluteSignedShellBlockBudget N g r U Q K +
          h15NormalizedBoundaryPhaseCollisionDefect N g r U Q ≤
        Delta * h15NormalizedBoundaryCrossModulusFrequencyEnergy N g U Q) :
    H15CorrectionCoupledCrossModulusFrequencyDispersion N g r U Q Delta := by
  rw [h15CorrectionCoupledCrossModulusFrequencyDispersion_iff_phaseSeparated hQ,
    h15NormalizedBoundaryPhaseSeparatedLedger_eq_sum_shellBlocks hQ]
  constructor
  · exact hDelta
  · have hblocks :=
      sum_signedShellBlocks_le_absoluteSignedShellBlockBudget N g r U Q K
    linarith

end NBMellinTools.NB12
