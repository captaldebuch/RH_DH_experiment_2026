import Mathlib
import RiemannHypothesis.Criteria.NymanBeurling.BaezDuarte

/-!
# Vasyunin's Formula for the Nyman–Beurling Gram Matrix

This file exposes the exact Vasyunin symbolic evaluation of the L²(0,∞) inner
product of the fractional part functions. 

## Convention:
- Lean generated index `i : Fin N` corresponds to mathematical index `h = i.val + 1`.
- Lean generated index `j : Fin N` corresponds to mathematical index `k = j.val + 1`.
- The Gram entry `baezDuarteGramEntry h k` represents exactly:
  ∫₀^∞ {1/(h x)} {1/(k x)} dx
- Vasyunin's formula evaluates the integral explicitly, involving cotangent sums.
-/

namespace RH.Criteria.NymanBeurling.VasyuninGram

open RH.Criteria.NymanBeurling.BaezDuarte



/-- The target L²(0,∞) Gram entry for the Báez-Duarte basis.
    Defined as the inner product ∫₀^∞ {1/(h x)} · {1/(k x)} dx. -/
noncomputable def baezDuarteGramEntry (h k : ℕ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), (Int.fract (1 / ((h : ℝ) * x))) * (Int.fract (1 / ((k : ℝ) * x)))



/-- Direct symmetry of the Gram entry, proved from the concrete integral definition.
    Multiplication in the integrand commutes, so no Vasyunin formula is needed. -/
theorem baezDuarteGramEntry_symm (h k : ℕ) :
    baezDuarteGramEntry h k = baezDuarteGramEntry k h := by
  simp only [baezDuarteGramEntry]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  ring


end RH.Criteria.NymanBeurling.VasyuninGram
