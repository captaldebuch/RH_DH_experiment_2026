/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FinalBoundaryExplicitCorrelation

/-!
# NB12zy: four-sector expansion of the endpoint correlation

Each complete modulus row is split exactly into its uncovered terminal-Abel
boundary and its incomplete smooth endpoint.  The literal distinct-modulus
correlation is then expanded into terminal-terminal, terminal-smooth,
smooth-terminal, and smooth-smooth sectors, without estimating any sector or
discarding its sign.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate
open Complex

namespace NBMellinTools.NB12

theorem sum_erase_mul_eq_mul_sum_sub_diagonal
    {ι : Type} [DecidableEq ι] (s : Finset ι) (f g : ι → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s.erase i, f i * g j) =
      (∑ i ∈ s, f i) * (∑ j ∈ s, g j) -
        ∑ i ∈ s, f i * g i := by
  calc
    (∑ i ∈ s, ∑ j ∈ s.erase i, f i * g j) =
        ∑ i ∈ s, f i * (∑ j ∈ s.erase i, g j) := by
      simp only [Finset.mul_sum]
    _ = ∑ i ∈ s, (f i * (∑ j ∈ s, g j) - f i * g i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have herase := Finset.sum_erase_add s g hi
      rw [← herase]
      ring
    _ = (∑ i ∈ s, f i) * (∑ j ∈ s, g j) -
        ∑ i ∈ s, f i * g i := by
      rw [Finset.sum_sub_distrib, Finset.sum_mul]

theorem sum_erase_mul_comm
    {ι : Type} [DecidableEq ι] (s : Finset ι) (f g : ι → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s.erase i, f i * g j) =
      ∑ i ∈ s, ∑ j ∈ s.erase i, g i * f j := by
  rw [sum_erase_mul_eq_mul_sum_sub_diagonal,
    sum_erase_mul_eq_mul_sum_sub_diagonal]
  simp only [mul_comm]

/-! ## Fixed-modulus terminal and smooth rows -/

noncomputable def h15NormalizedBoundaryTerminalModulusRow
    (N g r U q : ℕ) : ℝ :=
  ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
    h15NormalizedProgressionTerminalRowBoundaryLift N g r U
      (h15SquareDivisorProgressionModulus g d) q d

noncomputable def h15NormalizedBoundaryIncompleteSmoothModulusRow
    (N g r U q : ℕ) : ℝ :=
  ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
    h15NormalizedProgressionIncompleteEndpointRow N g r U
      (h15SquareDivisorProgressionModulus g d) q d

/-- Exact correction-preserving fixed-modulus split. -/
theorem h15NormalizedBoundaryFixedFrequencyModulusRow_eq_terminal_add_smooth
    (N g r U q : ℕ) (hq : 0 < q) :
    h15NormalizedBoundaryFixedFrequencyModulusRow N g r U q =
      h15NormalizedBoundaryTerminalModulusRow N g r U q +
        h15NormalizedBoundaryIncompleteSmoothModulusRow N g r U q := by
  unfold h15NormalizedBoundaryFixedFrequencyModulusRow
    h15NormalizedBoundaryTerminalModulusRow
    h15NormalizedBoundaryIncompleteSmoothModulusRow
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [h15NormalizedBoundaryFourierRowValue_eq_pointRow
      N g r U (h15SquareDivisorProgressionModulus g d) q d hq,
    ← h15NormalizedProgressionCorrectionCoupledSuperperiodBoundaryRow_eq_pointwise
      N g r U q d hq]
  unfold h15NormalizedProgressionCorrectionCoupledSuperperiodBoundaryRow
  dsimp only
  change
    h15NormalizedRowSuperperiodBoundaryDefect g r U q d
        (fun k => h15NormalizedProgressionAbelTerminalWeight N g k q) +
      h15NormalizedProgressionIncompleteEndpointRow N g r U
        (h15SquareDivisorProgressionModulus g d) q d = _
  rw [h15NormalizedRowSuperperiodBoundaryDefect_eq_pointLift]

/-! ## Four literal distinct-modulus sectors -/

noncomputable def h15NormalizedBoundaryTerminalTerminalCorrelation
    (N g r U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    ∑ q' ∈ (h15BettinChandeeSupportedNatBlock N g Q).erase q,
      h15NormalizedBoundaryTerminalModulusRow N g r U q *
        h15NormalizedBoundaryTerminalModulusRow N g r U q'

noncomputable def h15NormalizedBoundaryTerminalSmoothCorrelation
    (N g r U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    ∑ q' ∈ (h15BettinChandeeSupportedNatBlock N g Q).erase q,
      h15NormalizedBoundaryTerminalModulusRow N g r U q *
        h15NormalizedBoundaryIncompleteSmoothModulusRow N g r U q'

noncomputable def h15NormalizedBoundarySmoothTerminalCorrelation
    (N g r U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    ∑ q' ∈ (h15BettinChandeeSupportedNatBlock N g Q).erase q,
      h15NormalizedBoundaryIncompleteSmoothModulusRow N g r U q *
        h15NormalizedBoundaryTerminalModulusRow N g r U q'

noncomputable def h15NormalizedBoundarySmoothSmoothCorrelation
    (N g r U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    ∑ q' ∈ (h15BettinChandeeSupportedNatBlock N g Q).erase q,
      h15NormalizedBoundaryIncompleteSmoothModulusRow N g r U q *
        h15NormalizedBoundaryIncompleteSmoothModulusRow N g r U q'

/-- Exact four-sector expansion of the complete signed cross-modulus
correlation. -/
theorem h15NormalizedBoundaryExplicitCrossModulusCorrelation_eq_fourSectors
    {N g r U Q : ℕ} (hQ : 0 < Q) :
    h15NormalizedBoundaryExplicitCrossModulusCorrelation N g r U Q =
      h15NormalizedBoundaryTerminalTerminalCorrelation N g r U Q +
        h15NormalizedBoundaryTerminalSmoothCorrelation N g r U Q +
        h15NormalizedBoundarySmoothTerminalCorrelation N g r U Q +
        h15NormalizedBoundarySmoothSmoothCorrelation N g r U Q := by
  unfold h15NormalizedBoundaryExplicitCrossModulusCorrelation
    h15NormalizedBoundaryTerminalTerminalCorrelation
    h15NormalizedBoundaryTerminalSmoothCorrelation
    h15NormalizedBoundarySmoothTerminalCorrelation
    h15NormalizedBoundarySmoothSmoothCorrelation
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hqMem
  have hqBounds := mem_h15BettinChandeeSupportedNatBlock.mp hqMem
  have hqPos : 0 < q := hQ.trans_le hqBounds.1
  apply Finset.sum_congr rfl
  intro q' hq'MemErase
  have hq'Mem := Finset.mem_of_mem_erase hq'MemErase
  have hq'Bounds := mem_h15BettinChandeeSupportedNatBlock.mp hq'Mem
  have hq'Pos : 0 < q' := hQ.trans_le hq'Bounds.1
  rw [h15NormalizedBoundaryFixedFrequencyModulusRow_eq_terminal_add_smooth
      N g r U q hqPos,
    h15NormalizedBoundaryFixedFrequencyModulusRow_eq_terminal_add_smooth
      N g r U q' hq'Pos]
  ring

/-- The two mixed ordered sectors coincide by interchanging the two distinct
moduli. -/
theorem h15NormalizedBoundaryTerminalSmoothCorrelation_eq_smoothTerminal
    (N g r U Q : ℕ) :
    h15NormalizedBoundaryTerminalSmoothCorrelation N g r U Q =
      h15NormalizedBoundarySmoothTerminalCorrelation N g r U Q := by
  unfold h15NormalizedBoundaryTerminalSmoothCorrelation
    h15NormalizedBoundarySmoothTerminalCorrelation
  exact sum_erase_mul_comm
    (h15BettinChandeeSupportedNatBlock N g Q)
    (h15NormalizedBoundaryTerminalModulusRow N g r U)
    (h15NormalizedBoundaryIncompleteSmoothModulusRow N g r U)

/-- Equivalent three-sector form, with the mixed term counted twice. -/
theorem h15NormalizedBoundaryExplicitCrossModulusCorrelation_eq_threeSectors
    {N g r U Q : ℕ} (hQ : 0 < Q) :
    h15NormalizedBoundaryExplicitCrossModulusCorrelation N g r U Q =
      h15NormalizedBoundaryTerminalTerminalCorrelation N g r U Q +
        2 * h15NormalizedBoundaryTerminalSmoothCorrelation N g r U Q +
        h15NormalizedBoundarySmoothSmoothCorrelation N g r U Q := by
  rw [h15NormalizedBoundaryExplicitCrossModulusCorrelation_eq_fourSectors hQ,
    ← h15NormalizedBoundaryTerminalSmoothCorrelation_eq_smoothTerminal]
  ring

end NBMellinTools.NB12
