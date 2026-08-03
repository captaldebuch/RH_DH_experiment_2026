import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCRootAsymptoticExtraction
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Route C: Bettin--Conrey's saddle integral

Lemma 3 in Bettin--Conrey, *A reciprocity formula for a cotangent sum*, studies

`J_n(A, alpha) = integral_0^infinity
  u^(n + alpha - 1) exp(-u) exp(-A*sqrt u) du`.

The nonzero complex parameter `A` creates the root-exponential factor used in
the central Taylor coefficient estimate.  This file fixes the exact Lean
normalization, proves the undeformed `A = 0` Gamma identity, and verifies its
`alpha = 1` Stirling asymptotic from Mathlib.  These results are the baseline
for the remaining steepest-descent deformation; they do not postulate that
deformation or the final coefficient bound.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleIntegral

open Filter MeasureTheory Set
open scoped Asymptotics

/-- The complex saddle integral in Bettin--Conrey's Lemma 3.  The real power
is evaluated only on `u > 0`, so this agrees there with the paper's
`u^alpha u^n du/u` normalization. -/
noncomputable def routeCSaddleIntegral (A : ℂ) (alpha : ℝ) (n : ℕ) : ℂ :=
  ∫ u : ℝ in Ioi 0,
    ((Real.rpow u ((n : ℝ) + alpha - 1) * Real.exp (-u) : ℝ) : ℂ) *
      Complex.exp (-A * (Real.sqrt u : ℂ))

/-- The undeformed real saddle integral. -/
noncomputable def routeCSaddleIntegralZero (alpha : ℝ) (n : ℕ) : ℝ :=
  ∫ u : ℝ in Ioi 0,
    Real.rpow u ((n : ℝ) + alpha - 1) * Real.exp (-u)

theorem routeCSaddleIntegralZero_eq_gamma (alpha : ℝ) (n : ℕ)
    (hpos : 0 < (n : ℝ) + alpha) :
    routeCSaddleIntegralZero alpha n = Real.Gamma ((n : ℝ) + alpha) := by
  rw [Real.Gamma_eq_integral hpos]
  unfold routeCSaddleIntegralZero
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  exact mul_comm _ _

theorem routeCSaddleIntegral_zero_eq_ofReal (alpha : ℝ) (n : ℕ) :
    routeCSaddleIntegral 0 alpha n =
      (routeCSaddleIntegralZero alpha n : ℂ) := by
  unfold routeCSaddleIntegral routeCSaddleIntegralZero
  simp only [zero_mul, neg_zero, Complex.exp_zero, mul_one]
  exact integral_complex_ofReal

/-- At `alpha = 1`, the undeformed saddle is exactly `n!`. -/
theorem routeCSaddleIntegralZero_one_eq_factorial (n : ℕ) :
    routeCSaddleIntegralZero 1 n = (n.factorial : ℝ) := by
  rw [routeCSaddleIntegralZero_eq_gamma 1 n (by positivity)]
  convert Real.Gamma_nat_eq_factorial n using 1

/-- The `A = 0`, `alpha = 1` case of the paper's saddle asymptotic is exactly
Mathlib's Stirling theorem.  This verifies the normalization before the
nonzero complex saddle is introduced. -/
theorem routeCSaddleIntegralZero_one_isEquivalent_stirling :
    (fun n : ℕ => routeCSaddleIntegralZero 1 n) ~[atTop]
      (fun n : ℕ =>
        Real.sqrt (2 * n * Real.pi) *
          ((n : ℝ) / Real.exp 1) ^ n) := by
  simpa only [routeCSaddleIntegralZero_one_eq_factorial] using
    Stirling.factorial_isEquivalent_stirling

/-- The precise remaining analytic target from Lemma 3: after division by
the displayed leading saddle term, the complex integral tends to one.  This
is a proposition, not an axiom or an asserted theorem. -/
def RouteCSaddleIntegralAsymptoticTarget (A : ℂ) (alpha : ℝ) : Prop :=
  Tendsto
    (fun n : ℕ =>
      routeCSaddleIntegral A alpha n /
        ((Real.sqrt (2 * Real.pi) : ℂ) * Complex.exp (A ^ 2 / 8) *
          Complex.exp (-A * (Real.sqrt n : ℂ)) *
          Complex.exp (-(n : ℝ)) *
          ((Real.rpow n ((n : ℝ) + alpha - 1 / 2) : ℝ) : ℂ)))
    atTop (nhds 1)

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleIntegral
