/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FinalBoundaryShellBlocks

/-!
# NB12zzj: shell-block endpoints and the uniform decay interface

The block budget lies between the absolute value of the complete signed ledger
and the pointwise shell budget.  Width parameter `K = 0` is the canonical
single-block sentinel (natural-number division by zero is zero), so it retains
all cross-shell cancellation.

The final section packages the exact uniform analytic data needed as `N`
varies.  It requires decay of `Delta * energy`, not merely `Delta`, because
that product is the actual squared Fourier-boundary scale.
-/

open Filter
open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate
open Complex

namespace NBMellinTools.NB12

theorem abs_h15NormalizedBoundaryPhaseSeparatedLedger_le_shellBlockBudget
    {N g r U Q K : ℕ} (hQ : 0 < Q) :
    |h15NormalizedBoundaryPhaseSeparatedLedger N g r U Q| ≤
      h15NormalizedBoundaryAbsoluteSignedShellBlockBudget N g r U Q K := by
  calc
    |h15NormalizedBoundaryPhaseSeparatedLedger N g r U Q| =
        |∑ j : Fin (h15BoundarySpacingBlockCount Q K),
          h15NormalizedBoundarySignedCongruenceShellBlock N g r U Q K j| :=
      congrArg abs
        (h15NormalizedBoundaryPhaseSeparatedLedger_eq_sum_shellBlocks hQ)
    _ ≤ h15NormalizedBoundaryAbsoluteSignedShellBlockBudget N g r U Q K := by
      unfold h15NormalizedBoundaryAbsoluteSignedShellBlockBudget
      exact Finset.abs_sum_le_sum_abs _ _

/-- Every arithmetic blocking interpolates between the fully signed aggregate
and the pointwise absolute shell budget. -/
theorem h15NormalizedBoundaryShellBlockBudget_sandwich
    {N g r U Q K : ℕ} (hQ : 0 < Q) :
    |h15NormalizedBoundaryPhaseSeparatedLedger N g r U Q| ≤
        h15NormalizedBoundaryAbsoluteSignedShellBlockBudget N g r U Q K ∧
      h15NormalizedBoundaryAbsoluteSignedShellBlockBudget N g r U Q K ≤
        h15NormalizedBoundaryAbsoluteSignedShellBudget N g r U Q :=
  ⟨abs_h15NormalizedBoundaryPhaseSeparatedLedger_le_shellBlockBudget hQ,
    h15NormalizedBoundaryAbsoluteSignedShellBlockBudget_le_shellBudget
      N g r U Q K⟩

@[simp] theorem h15BoundarySpacingBlockCount_zero (Q : ℕ) :
    h15BoundarySpacingBlockCount Q 0 = 1 := by
  simp [h15BoundarySpacingBlockCount]

theorem h15NormalizedBoundarySignedCongruenceShellBlock_zero_eq_phaseSeparated
    {N g r U Q : ℕ} (hQ : 0 < Q) :
    h15NormalizedBoundarySignedCongruenceShellBlock N g r U Q 0
        ⟨0, by simp⟩ =
      h15NormalizedBoundaryPhaseSeparatedLedger N g r U Q := by
  rw [h15NormalizedBoundaryPhaseSeparatedLedger_eq_sum_signedShells hQ]
  unfold h15NormalizedBoundarySignedCongruenceShellBlock
  simp

/-- At the single-block endpoint, the block budget is exactly the absolute
value of the complete signed separated ledger. -/
theorem h15NormalizedBoundaryAbsoluteSignedShellBlockBudget_zero_eq
    {N g r U Q : ℕ} (hQ : 0 < Q) :
    h15NormalizedBoundaryAbsoluteSignedShellBlockBudget N g r U Q 0 =
      |h15NormalizedBoundaryPhaseSeparatedLedger N g r U Q| := by
  classical
  unfold h15NormalizedBoundaryAbsoluteSignedShellBlockBudget
  let j0 : Fin (h15BoundarySpacingBlockCount Q 0) := ⟨0, by simp⟩
  have hj : ∀ j : Fin (h15BoundarySpacingBlockCount Q 0), j = j0 := by
    intro j
    apply Fin.ext
    have hjlt := j.isLt
    have hjlt' : j.val < 1 := by
      simpa only [h15BoundarySpacingBlockCount, Nat.div_zero, zero_add] using hjlt
    change j.val = 0
    omega
  have huniv :
      (Finset.univ : Finset (Fin (h15BoundarySpacingBlockCount Q 0))) =
        {j0} := by
    ext j
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact hj j
  rw [huniv, Finset.sum_singleton]
  exact congrArg abs
    (h15NormalizedBoundarySignedCongruenceShellBlock_zero_eq_phaseSeparated hQ)

/-- Uniform correction-coupled shell-block input along the natural cutoff.
The functions `g`, `r`, `U`, `Q`, and `K` allow the already formalized H15
parameters and block width to move with `N`. -/
structure H15CorrectionCoupledShellBlockDecayData
    (g r U Q K : ℕ → ℕ) where
  Delta : ℕ → ℝ
  q_pos : ∀ N, 0 < Q N
  delta_nonneg : ∀ N, 0 ≤ Delta N
  block_budget : ∀ N,
    h15NormalizedBoundaryAbsoluteSignedShellBlockBudget
          N (g N) (r N) (U N) (Q N) (K N) +
        h15NormalizedBoundaryPhaseCollisionDefect
          N (g N) (r N) (U N) (Q N) ≤
      Delta N * h15NormalizedBoundaryCrossModulusFrequencyEnergy
        N (g N) (U N) (Q N)
  scaled_tendsto_zero :
    Tendsto
      (fun N =>
        Delta N * h15NormalizedBoundaryCrossModulusFrequencyEnergy
          N (g N) (U N) (Q N))
      atTop (nhds 0)

theorem H15CorrectionCoupledShellBlockDecayData.dispersion
    {g r U Q K : ℕ → ℕ}
    (H : H15CorrectionCoupledShellBlockDecayData g r U Q K) (N : ℕ) :
    H15CorrectionCoupledCrossModulusFrequencyDispersion
      N (g N) (r N) (U N) (Q N) (H.Delta N) := by
  exact
    h15CorrectionCoupledCrossModulusFrequencyDispersion_of_absoluteShellBlockBudget
      (H.q_pos N) (H.delta_nonneg N) (H.block_budget N)

noncomputable def H15CorrectionCoupledShellBlockDecayData.boundaryScale
    {g r U Q K : ℕ → ℕ}
    (H : H15CorrectionCoupledShellBlockDecayData g r U Q K) (N : ℕ) : ℝ :=
  Real.sqrt
    (H.Delta N * h15NormalizedBoundaryCrossModulusFrequencyEnergy
      N (g N) (U N) (Q N))

theorem H15CorrectionCoupledShellBlockDecayData.boundaryScale_tendsto_zero
    {g r U Q K : ℕ → ℕ}
    (H : H15CorrectionCoupledShellBlockDecayData g r U Q K) :
    Tendsto H.boundaryScale atTop (nhds 0) := by
  simpa only [H15CorrectionCoupledShellBlockDecayData.boundaryScale,
    Real.sqrt_zero] using H.scaled_tendsto_zero.sqrt

theorem H15CorrectionCoupledShellBlockDecayData.fourierEstimate
    {g r U Q K : ℕ → ℕ}
    (H : H15CorrectionCoupledShellBlockDecayData g r U Q K) (N : ℕ) :
    H15CorrectionCoupledFinalBoundaryFourierEstimate
      N (g N) (r N) (U N) (Q N) (H.boundaryScale N) := by
  exact
    h15CorrectionCoupledFinalBoundaryFourierEstimate_of_crossModulusDispersion
      (H.dispersion N)

end NBMellinTools.NB12
