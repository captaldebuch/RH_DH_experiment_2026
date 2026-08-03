import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannFunctionalEquation

/-!
# Route B6: the normalized pre-Voronoi contour identity

The normalized Estermann functional equation is lifted here to an exact
weighted identity on every vertical line `0 < c`, `c != 1`.  This is the
unconditional input to a smoothed Voronoi proof.

No contour shift is claimed.  Turning the right-hand integral into Bessel (or
inverse-Mellin) kernels still requires decay, pole bookkeeping, and horizontal
boundary estimates.  Mathlib currently has no analytic Bessel-function or
Kuznetsov infrastructure, so those steps remain explicit research gates.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi

open Complex MeasureTheory ZMod
open scoped Real
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannFunctionalEquation
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannHurwitz

/-- A point on the vertical line of real part `c`. -/
noncomputable def estermannVerticalPoint (c t : ℝ) : ℂ :=
  (c : ℂ) + (t : ℂ) * Complex.I

@[simp] theorem estermannVerticalPoint_re (c t : ℝ) :
    (estermannVerticalPoint c t).re = c := by
  simp [estermannVerticalPoint]

/-- The fully normalized right-hand side of the Estermann functional
equation. -/
noncomputable def estermannNormalizedDualValue
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q) (s : ℂ) : ℂ :=
  (q : ℂ) ^ (s - 1) * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
    (Complex.exp (Real.pi * Complex.I * s / 2) *
        ZMod.LFunction (estermannOuterDualCoefficient a q hcop s) s +
      Complex.exp (-Real.pi * Complex.I * s / 2) *
        ZMod.LFunction
          (fun k : ZMod q => estermannOuterDualCoefficient a q hcop s (-k)) s)

/-- Pointwise normalized functional equation, packaged for contour use. -/
theorem estermannContinuation_one_sub_eq_normalizedDual
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q) {s : ℂ}
    (hs : ∀ n : ℕ, s ≠ -n) (hs1 : s ≠ 1) :
    estermannHurwitzContinuation a q (1 - s) =
      estermannNormalizedDualValue a q hcop s := by
  exact estermannHurwitzContinuation_one_sub_normalized
    a q hcop hs hs1

/-- The primal weighted vertical integral before a Voronoi contour shift. -/
noncomputable def estermannPrimalVerticalIntegral
    (a q : ℕ) [NeZero q] (c : ℝ) (W : ℂ → ℂ) : ℂ :=
  ∫ t : ℝ, W (estermannVerticalPoint c t) *
    estermannHurwitzContinuation a q
      (1 - estermannVerticalPoint c t)

/-- The normalized dual weighted vertical integral. -/
noncomputable def estermannDualVerticalIntegral
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q)
    (c : ℝ) (W : ℂ → ℂ) : ℂ :=
  ∫ t : ℝ, W (estermannVerticalPoint c t) *
    estermannNormalizedDualValue a q hcop
      (estermannVerticalPoint c t)

/-- Exact pre-Voronoi identity on a positive vertical line away from the pole
at one.  Since the integrands agree pointwise, this theorem needs no
integrability assumptions; later contour movement will require them. -/
theorem estermannPrimalVerticalIntegral_eq_dual
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q)
    (c : ℝ) (hc : 0 < c) (hc1 : c ≠ 1) (W : ℂ → ℂ) :
    estermannPrimalVerticalIntegral a q c W =
      estermannDualVerticalIntegral a q hcop c W := by
  unfold estermannPrimalVerticalIntegral estermannDualVerticalIntegral
  apply integral_congr_ae
  filter_upwards [] with t
  apply congrArg (W (estermannVerticalPoint c t) * ·)
  apply estermannContinuation_one_sub_eq_normalizedDual a q hcop
  · intro n hn
    have hre := congrArg Complex.re hn
    norm_num [estermannVerticalPoint] at hre
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  · intro hs
    have hre := congrArg Complex.re hs
    simp only [estermannVerticalPoint_re, one_re] at hre
    exact hc1 hre

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi
