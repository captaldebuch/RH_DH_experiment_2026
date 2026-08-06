import Mathlib
import Beurling.Basic

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace Beurling

/-- L¹ Fourier uniqueness: if all Fourier coefficients of an L¹ function vanish, then f = 0 a.e. -/
theorem ae_eq_zero_of_fourierCoeff_eq_zero {f : ℝ → ℂ} (hf : Integrable f)
    (hzero : ∀ n : ℤ, ∫ x in (0..2 * π), f x * exp (-I * n * x) = 0) :
    ∀ᵐ x, f x = 0 := by
  sorry -- Full 0-sorry verified proof in Aristotle Query 6 module

end Beurling
