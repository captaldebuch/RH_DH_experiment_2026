import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorMultiResidueRectangle

/-!
# Route C: reflection of the Taylor horizontal integrand

The finite residue rectangle leaves an asymptotic question on its horizontal
edges.  Estimating the two zeta factors and the sine denominator separately
hides the available exponential decay.  This module first performs the
exact algebraic cancellation dictated by the zeta functional equation.

Off the real axis, the factor `cos (pi * (1-s) / 2)` in the functional
equation is `sin (pi*s/2)`.  It cancels the corresponding factor in
`sin (pi*s)`.  The remaining quotient contains `Gamma (1-s)` and
`1 / cos (pi*s/2)`, each of which supplies half of the required intrinsic
horizontal decay.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorHorizontalReflection

open Complex
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorMultiResidueRectangle
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorResidues
open RH.Criteria.NymanBeurling.H14ZetaFETransport

/-- The reflected form of the central Taylor integrand.  This is the form in
which horizontal decay is visible. -/
noncomputable def bettinConreyGZeroReflectedIntegrand
    (u s : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ)) ^ (s - 1) * Complex.Gamma (1 - s) *
      riemannZeta (1 - s) ^ 2 /
        Complex.cos ((Real.pi : ℂ) * s / 2) * u ^ (-s)

theorem sin_pi_mul_eq_two_mul_halfAngle (s : ℂ) :
    Complex.sin ((Real.pi : ℂ) * s) =
      2 * Complex.sin ((Real.pi : ℂ) * s / 2) *
        Complex.cos ((Real.pi : ℂ) * s / 2) := by
  calc
    Complex.sin ((Real.pi : ℂ) * s) =
        Complex.sin (2 * ((Real.pi : ℂ) * s / 2)) := by
          congr 1
          ring
    _ = _ := Complex.sin_two_mul _

theorem cos_pi_mul_one_sub_div_two_eq_sin_halfAngle (s : ℂ) :
    Complex.cos ((Real.pi : ℂ) * (1 - s) / 2) =
      Complex.sin ((Real.pi : ℂ) * s / 2) := by
  rw [show (Real.pi : ℂ) * (1 - s) / 2 =
      (Real.pi : ℂ) / 2 - (Real.pi : ℂ) * s / 2 by ring]
  exact Complex.cos_pi_div_two_sub _

theorem sin_halfAngle_ne_zero_of_im_ne_zero
    {s : ℂ} (hs : s.im ≠ 0) :
    Complex.sin ((Real.pi : ℂ) * s / 2) ≠ 0 := by
  have hfull := sin_pi_mul_ne_zero_of_im_ne_zero hs
  intro hhalf
  apply hfull
  rw [sin_pi_mul_eq_two_mul_halfAngle, hhalf]
  ring

theorem cos_halfAngle_ne_zero_of_im_ne_zero
    {s : ℂ} (hs : s.im ≠ 0) :
    Complex.cos ((Real.pi : ℂ) * s / 2) ≠ 0 := by
  have hfull := sin_pi_mul_ne_zero_of_im_ne_zero hs
  intro hhalf
  apply hfull
  rw [sin_pi_mul_eq_two_mul_halfAngle, hhalf]
  ring

/-- Exact functional-equation reflection of the literal Mellin integrand.
No estimate is used: the half-angle factor is cancelled algebraically. -/
theorem bettinConreyGZeroMeromorphicIntegrand_eq_reflected
    (u s : ℂ) (hs : s.im ≠ 0) :
    bettinConreyGZeroMeromorphicIntegrand u s =
      bettinConreyGZeroReflectedIntegrand u s := by
  have hsin := sin_halfAngle_ne_zero_of_im_ne_zero hs
  have hcos := cos_halfAngle_ne_zero_of_im_ne_zero hs
  have hfe := riemannZeta_eq_zetaFEFactor_mul (w := s) hs
  unfold bettinConreyGZeroMeromorphicIntegrand
    bettinConreyGZeroReflectedIntegrand
  rw [hfe]
  unfold zetaFEFactor
  rw [cos_pi_mul_one_sub_div_two_eq_sin_halfAngle,
    sin_pi_mul_eq_two_mul_halfAngle]
  field_simp [hsin, hcos]

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorHorizontalReflection
