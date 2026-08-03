import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCGammaShiftedLines

/-!
# Route C: the functional-equation factor on Taylor remainder lines

The Taylor remainder for `g₀` contains `ζ(s)^2` on the discrete lines
`Re s = 1/2-n`.  The reflected zeta factor is uniformly bounded, so the
remaining task is an exact norm calculation for the functional-equation
factor.  On these half-integer lines the calculation uses only the Gamma
recurrence and the already proved half-angle identity.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorFEFactor

open Complex
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCGammaHalfLines
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCGammaShiftedLines
open RH.Criteria.NymanBeurling.H14ZetaFETransport

/-- The Gamma argument in the functional equation at the `n`-th Taylor
remainder line. -/
noncomputable def routeCTaylorReflectedPoint (n : ℕ) (t : ℝ) : ℂ :=
  1 - routeCGammaShiftedPoint n t

theorem routeCTaylorReflectedPoint_zero (t : ℝ) :
    routeCTaylorReflectedPoint 0 t =
      (1 / 2 : ℝ) + I * (-t) := by
  simp [routeCTaylorReflectedPoint, routeCGammaShiftedPoint]
  ring

theorem routeCTaylorReflectedPoint_succ (n : ℕ) (t : ℝ) :
    routeCTaylorReflectedPoint (n + 1) t =
      routeCTaylorReflectedPoint n t + 1 := by
  unfold routeCTaylorReflectedPoint routeCGammaShiftedPoint
  push_cast
  ring

theorem routeCTaylorReflectedPoint_ne_zero (n : ℕ) (t : ℝ) :
    routeCTaylorReflectedPoint n t ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp [routeCTaylorReflectedPoint, routeCGammaShiftedPoint] at hre
  have hn : (0 : ℝ) ≤ n := by positivity
  linarith

theorem norm_routeCTaylorReflectedPoint_sq (n : ℕ) (t : ℝ) :
    ‖routeCTaylorReflectedPoint n t‖ ^ 2 =
      ((n : ℝ) + 1 / 2) ^ 2 + t ^ 2 := by
  rw [Complex.sq_norm]
  unfold routeCTaylorReflectedPoint routeCGammaShiftedPoint
  rw [show
      ((1 : ℂ) - ((((1 / 2 : ℝ) - n : ℝ) : ℂ) + I * (t : ℂ))) =
        (((n : ℝ) + 1 / 2 : ℝ) : ℂ) + (-t : ℝ) * I by
          push_cast
          ring]
  rw [Complex.normSq_add_mul_I]
  ring

/-- Exact Gamma norm on the reflected positive half-integer line. -/
theorem norm_Gamma_routeCTaylorReflectedPoint_sq (n : ℕ) (t : ℝ) :
    ‖Complex.Gamma (routeCTaylorReflectedPoint n t)‖ ^ 2 =
      (∏ j ∈ Finset.range n,
          (((j : ℝ) + 1 / 2) ^ 2 + t ^ 2)) *
        (Real.pi / Real.cosh (Real.pi * t)) := by
  induction n with
  | zero =>
      have h := norm_Gamma_half_add_I_mul_sq (-t)
      rw [routeCTaylorReflectedPoint_zero]
      simpa [Real.cosh_neg] using h
  | succ n ih =>
      have hg := Complex.Gamma_add_one
        (routeCTaylorReflectedPoint n t)
        (routeCTaylorReflectedPoint_ne_zero n t)
      rw [← routeCTaylorReflectedPoint_succ] at hg
      rw [hg, norm_mul, mul_pow,
        norm_routeCTaylorReflectedPoint_sq, ih,
        Finset.prod_range_succ]
      ring

/-- The trigonometric factor in the functional equation has the same norm
as the shifted half-angle sine. -/
theorem norm_cos_reflectedHalfAngle_sq (n : ℕ) (t : ℝ) :
    ‖Complex.cos ((Real.pi : ℂ) *
        routeCTaylorReflectedPoint n t / 2)‖ ^ 2 =
      Real.cosh (Real.pi * t) / 2 := by
  have harg :
      (Real.pi : ℂ) * routeCTaylorReflectedPoint n t / 2 =
        (Real.pi : ℂ) / 2 -
          (Real.pi : ℂ) * routeCGammaShiftedPoint n t / 2 := by
    unfold routeCTaylorReflectedPoint
    ring
  rw [harg, Complex.cos_pi_div_two_sub]
  exact norm_sin_taylorHalfAngle_sq n t

/-- Exact squared norm of the zeta functional-equation factor on every
Taylor remainder line.  The result is a finite polynomial in `t`, times a
radial constant depending only on the line index. -/
theorem norm_zetaFEFactor_routeCGammaShiftedPoint_sq
    (n : ℕ) (t : ℝ) :
    ‖zetaFEFactor (routeCGammaShiftedPoint n t)‖ ^ 2 =
      2 *
        ((2 * Real.pi : ℝ) ^ (-((n : ℝ) + 1 / 2))) ^ 2 *
        (∏ j ∈ Finset.range n,
          (((j : ℝ) + 1 / 2) ^ 2 + t ^ 2)) * Real.pi := by
  have hbase : 0 < (2 * Real.pi : ℝ) := by positivity
  have hcosh : Real.cosh (Real.pi * t) ≠ 0 :=
    (Real.cosh_pos _).ne'
  unfold zetaFEFactor
  rw [norm_mul, norm_mul, norm_mul, mul_pow, mul_pow, mul_pow]
  rw [show ‖(2 : ℂ)‖ = 2 by norm_num]
  have hbaseCast : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hbaseCast, Complex.norm_cpow_eq_rpow_re_of_pos hbase]
  have hre :
      (routeCGammaShiftedPoint n t - 1).re =
        -((n : ℝ) + 1 / 2) := by
    simp [routeCGammaShiftedPoint]
    ring
  rw [hre]
  rw [show 1 - routeCGammaShiftedPoint n t =
      routeCTaylorReflectedPoint n t by rfl]
  rw [norm_Gamma_routeCTaylorReflectedPoint_sq,
    norm_cos_reflectedHalfAngle_sq]
  field_simp [hcosh]

/-- Polynomial vertical bound for the actual `ζ(s)^2` factor in the shifted
`g₀` integrand.  The exceptional point `t=0` is immaterial for the later
line integral and is the only point excluded by the present functional-
equation API. -/
theorem norm_riemannZeta_shiftedPoint_sq_le
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : t ≠ 0) :
    ‖riemannZeta (routeCGammaShiftedPoint n t) ^ 2‖ ≤
      162 *
        ((2 * Real.pi : ℝ) ^ (-((n : ℝ) + 1 / 2))) ^ 2 *
        (∏ j ∈ Finset.range n,
          (((j : ℝ) + 1 / 2) ^ 2 + t ^ 2)) * Real.pi := by
  have him : (routeCGammaShiftedPoint n t).im ≠ 0 := by
    simpa [routeCGammaShiftedPoint] using ht
  have hfe := riemannZeta_eq_zetaFEFactor_mul him
  have hz := norm_riemannZeta_one_sub_shiftedPoint_le n hn t
  have hzsq :
      ‖riemannZeta (1 - routeCGammaShiftedPoint n t)‖ ^ 2 ≤ 81 := by
    nlinarith [norm_nonneg
      (riemannZeta (1 - routeCGammaShiftedPoint n t))]
  calc
    ‖riemannZeta (routeCGammaShiftedPoint n t) ^ 2‖ =
        ‖zetaFEFactor (routeCGammaShiftedPoint n t)‖ ^ 2 *
          ‖riemannZeta
            (1 - routeCGammaShiftedPoint n t)‖ ^ 2 := by
      rw [norm_pow, hfe, norm_mul, mul_pow]
    _ ≤ ‖zetaFEFactor (routeCGammaShiftedPoint n t)‖ ^ 2 * 81 :=
      mul_le_mul_of_nonneg_left hzsq (sq_nonneg _)
    _ = 162 *
        ((2 * Real.pi : ℝ) ^ (-((n : ℝ) + 1 / 2))) ^ 2 *
        (∏ j ∈ Finset.range n,
          (((j : ℝ) + 1 / 2) ^ 2 + t ^ 2)) * Real.pi := by
      rw [norm_zetaFEFactor_routeCGammaShiftedPoint_sq]
      ring

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorFEFactor
