import Mathlib

open Complex Real MeasureTheory Set Filter Topology InnerProductSpace

noncomputable section

namespace Beurling

/-- Shift operator on sequence space l²(ℕ) / Hardy space H²(𝔻). -/
def shift (a : ℕ → ℂ) : ℕ → ℂ := fun n => if n = 0 then 0 else a (n - 1)

/-- A closed subspace of H² is shift-invariant if it is closed under the shift operator. -/
def IsShiftInvariant (M : Submodule ℂ (ℕ → ℂ)) : Prop :=
  ∀ a ∈ M, shift a ∈ M

end Beurling
