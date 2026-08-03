import RiemannHypothesis.Criteria.NymanBeurling.H14FEFactorBound

/-!
# Route C: exact Gamma norms on the two central half-lines

This file isolates the Gamma-function input needed for the raw (non-Gaussian)
Bettin--Conrey Abel contour.  The positive half-line identity is Euler reflection
plus conjugation.  The negative half-line identity follows exactly from the Gamma
recurrence, so no version of Stirling's formula is used.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCGammaHalfLines

open Complex
open RH.Criteria.NymanBeurling.H14ZetaFETransport

/-- Exact squared Gamma norm on the central line `Re s = 1/2`. -/
theorem norm_Gamma_half_add_I_mul_sq (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℝ) + Complex.I * t)‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * t) := by
  exact normSq_gamma_half_add_I_mul t

/-- Exact squared Gamma norm on the shifted line `Re s = -1/2`.

This is the vertical-line input used after moving the Bettin--Conrey contour.
The extra factor `1 / (1/4 + t^2)` is supplied by the Gamma recurrence.
-/
theorem norm_Gamma_neg_half_add_I_mul_sq (t : ℝ) :
    ‖Complex.Gamma (-(1 / 2 : ℝ) + Complex.I * t)‖ ^ 2 =
      Real.pi /
        (Real.cosh (Real.pi * t) * ((1 / 2 : ℝ) ^ 2 + t ^ 2)) := by
  let z : ℂ := -(1 / 2 : ℝ) + Complex.I * t
  have hz : z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [z] at hre
  have hshift : z + 1 = (1 / 2 : ℝ) + Complex.I * t := by
    dsimp [z]
    push_cast
    ring
  have hrec := Complex.Gamma_add_one z hz
  rw [hshift] at hrec
  have hrecNorm := congrArg (fun w : ℂ ↦ ‖w‖ ^ 2) hrec
  change ‖Complex.Gamma ((1 / 2 : ℝ) + Complex.I * t)‖ ^ 2 =
    ‖z * Complex.Gamma z‖ ^ 2 at hrecNorm
  rw [norm_mul, mul_pow] at hrecNorm
  have hzNorm : ‖z‖ ^ 2 = (1 / 2 : ℝ) ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm]
    change Complex.normSq (-(1 / 2 : ℝ) + Complex.I * t) = _
    rw [show (-(1 / 2 : ℝ) + Complex.I * t : ℂ) =
        ((-(1 / 2 : ℝ) : ℝ) : ℂ) + t * Complex.I by
      push_cast
      ring]
    rw [Complex.normSq_add_mul_I]
    ring
  rw [norm_Gamma_half_add_I_mul_sq, hzNorm] at hrecNorm
  dsimp [z] at hrecNorm
  have hquad : (0 : ℝ) < (1 / 2 : ℝ) ^ 2 + t ^ 2 := by positivity
  have hcosh : Real.cosh (Real.pi * t) ≠ 0 :=
    ne_of_gt (Real.cosh_pos _)
  calc
    ‖Complex.Gamma (-(1 / 2 : ℝ) + Complex.I * t)‖ ^ 2 =
        (Real.pi / Real.cosh (Real.pi * t)) /
          ((1 / 2 : ℝ) ^ 2 + t ^ 2) := by
      apply (eq_div_iff hquad.ne').2
      nlinarith [hrecNorm]
    _ = Real.pi /
        (Real.cosh (Real.pi * t) * ((1 / 2 : ℝ) ^ 2 + t ^ 2)) := by
      field_simp

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCGammaHalfLines
