import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCGammaHalfLines

/-!
# Route C: Gamma norms on every shifted Taylor contour

The finite Taylor contour for `g₀` moves from `Re s = -1/2` to
`Re s = -2M-1/2`.  This module extends the previously proved central
half-line identity to every negative half-integer line by iterating the
Gamma recurrence.  The result is exact and retains the complete polynomial
denominator; no Stirling asymptotic is used.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCGammaShiftedLines

open Complex
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCGammaHalfLines
open RH.Criteria.NymanBeurling.H14ZetaFETransport

/-- The half-integer vertical point obtained after `n` unit shifts left from
`Re s = 1/2`.  The Taylor remainder line is obtained with `n = 2M+1`. -/
noncomputable def routeCGammaShiftedPoint (n : ℕ) (t : ℝ) : ℂ :=
  ((1 / 2 : ℝ) - n : ℝ) + I * t

theorem routeCGammaShiftedPoint_zero (t : ℝ) :
    routeCGammaShiftedPoint 0 t = (1 / 2 : ℝ) + I * t := by
  simp [routeCGammaShiftedPoint]

theorem routeCGammaShiftedPoint_succ_add_one (n : ℕ) (t : ℝ) :
    routeCGammaShiftedPoint (n + 1) t + 1 =
      routeCGammaShiftedPoint n t := by
  unfold routeCGammaShiftedPoint
  push_cast
  ring

theorem routeCGammaShiftedPoint_succ_ne_zero (n : ℕ) (t : ℝ) :
    routeCGammaShiftedPoint (n + 1) t ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp [routeCGammaShiftedPoint] at hre
  have hn : (0 : ℝ) ≤ n := by positivity
  linarith

/-- Squared norm of one linear Gamma-recurrence factor. -/
theorem norm_routeCGammaShiftedPoint_sq (n : ℕ) (t : ℝ) :
    ‖routeCGammaShiftedPoint n t‖ ^ 2 =
      ((1 / 2 : ℝ) - n) ^ 2 + t ^ 2 := by
  rw [Complex.sq_norm]
  unfold routeCGammaShiftedPoint
  rw [show ((((1 / 2 : ℝ) - n : ℝ) : ℂ) + I * (t : ℂ)) =
      (((1 / 2 : ℝ) - n : ℝ) : ℂ) + (t : ℂ) * I by ring]
  rw [Complex.normSq_add_mul_I]

/-- Exact product identity on every shifted half-integer line.  It is kept
in denominator-free form, which is the stable input for subsequent contour
majorants. -/
theorem norm_Gamma_shiftedPoint_sq_mul_prod (n : ℕ) (t : ℝ) :
    ‖Complex.Gamma (routeCGammaShiftedPoint n t)‖ ^ 2 *
        ∏ j ∈ Finset.range n,
          (((1 / 2 : ℝ) - n + j) ^ 2 + t ^ 2) =
      Real.pi / Real.cosh (Real.pi * t) := by
  induction n with
  | zero =>
      simpa [routeCGammaShiftedPoint_zero] using
        norm_Gamma_half_add_I_mul_sq t
  | succ n ih =>
      let z := routeCGammaShiftedPoint (n + 1) t
      have hz : z ≠ 0 := routeCGammaShiftedPoint_succ_ne_zero n t
      have hrec := Complex.Gamma_add_one z hz
      rw [routeCGammaShiftedPoint_succ_add_one] at hrec
      have hrecNorm := congrArg (fun w : ℂ => ‖w‖ ^ 2) hrec
      change ‖Complex.Gamma (routeCGammaShiftedPoint n t)‖ ^ 2 =
        ‖z * Complex.Gamma z‖ ^ 2 at hrecNorm
      rw [norm_mul, mul_pow] at hrecNorm
      have hzNorm : ‖z‖ ^ 2 =
          ((1 / 2 : ℝ) - (n + 1 : ℕ)) ^ 2 + t ^ 2 := by
        simpa [z] using norm_routeCGammaShiftedPoint_sq (n + 1) t
      rw [hzNorm] at hrecNorm
      dsimp [z] at hrecNorm
      rw [Finset.prod_range_succ']
      simp only [Nat.cast_zero, add_zero]
      have htail :
          (∏ x ∈ Finset.range n,
              ((1 / 2 - ↑(n + 1) + ↑(x + 1)) ^ 2 + t ^ 2)) =
            ∏ x ∈ Finset.range n,
              ((1 / 2 - ↑n + ↑x) ^ 2 + t ^ 2) := by
        apply Finset.prod_congr rfl
        intro j _hj
        congr 2
        push_cast
        ring
      rw [htail]
      calc
        ‖Complex.Gamma (routeCGammaShiftedPoint (n + 1) t)‖ ^ 2 *
              ((∏ x ∈ Finset.range n,
                  (((1 / 2 : ℝ) - n + x) ^ 2 + t ^ 2)) *
                (((1 / 2 : ℝ) - (n + 1 : ℕ)) ^ 2 + t ^ 2)) =
            (((1 / 2 : ℝ) - (n + 1 : ℕ)) ^ 2 + t ^ 2) *
              ‖Complex.Gamma (routeCGammaShiftedPoint (n + 1) t)‖ ^ 2 *
                ∏ x ∈ Finset.range n,
                  (((1 / 2 : ℝ) - n + x) ^ 2 + t ^ 2) := by ring
        _ = ‖Complex.Gamma (routeCGammaShiftedPoint n t)‖ ^ 2 *
              ∏ x ∈ Finset.range n,
                (((1 / 2 : ℝ) - n + x) ^ 2 + t ^ 2) := by
                  rw [← hrecNorm]
        _ = Real.pi / Real.cosh (Real.pi * t) := ih

theorem quarter_le_routeCGammaShiftedQuadratic
    (n j : ℕ) (hj : j < n) (t : ℝ) :
    (1 / 4 : ℝ) ≤ ((1 / 2 : ℝ) - n + j) ^ 2 + t ^ 2 := by
  have hjR : (j : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hj)
  have hlinear : (1 / 2 : ℝ) - n + j ≤ -(1 / 2 : ℝ) := by
    linarith
  nlinarith [sq_nonneg t]

theorem routeCGammaShiftedQuadraticProduct_pos (n : ℕ) (t : ℝ) :
    0 < ∏ j ∈ Finset.range n,
      (((1 / 2 : ℝ) - n + j) ^ 2 + t ^ 2) := by
  apply Finset.prod_pos
  intro j hj
  have hjlt := Finset.mem_range.mp hj
  exact lt_of_lt_of_le (by norm_num)
    (quarter_le_routeCGammaShiftedQuadratic n j hjlt t)

/-- Division form of the shifted-line identity.  Positivity of every
half-integer recurrence factor is proved rather than hidden in a field
simplification. -/
theorem norm_Gamma_shiftedPoint_sq (n : ℕ) (t : ℝ) :
    ‖Complex.Gamma (routeCGammaShiftedPoint n t)‖ ^ 2 =
      (Real.pi / Real.cosh (Real.pi * t)) /
        ∏ j ∈ Finset.range n,
          (((1 / 2 : ℝ) - n + j) ^ 2 + t ^ 2) := by
  apply (eq_div_iff (routeCGammaShiftedQuadraticProduct_pos n t).ne').2
  exact norm_Gamma_shiftedPoint_sq_mul_prod n t

private theorem normSq_sin_cos_taylorHalfAngle_zero (t : ℝ) :
    Complex.normSq (Complex.sin ((Real.pi : ℂ) *
        routeCGammaShiftedPoint 0 t / 2)) =
        Real.cosh (Real.pi * t) / 2 ∧
      Complex.normSq (Complex.cos ((Real.pi : ℂ) *
        routeCGammaShiftedPoint 0 t / 2)) =
        Real.cosh (Real.pi * t) / 2 := by
  have harg : (Real.pi : ℂ) * routeCGammaShiftedPoint 0 t / 2 =
      (Real.pi / 4 : ℂ) + (Real.pi * t / 2 : ℝ) * I := by
    unfold routeCGammaShiftedPoint
    push_cast
    ring
  rw [harg, Complex.sin_add_mul_I, Complex.cos_add_mul_I]
  have hquarter : (Real.pi / 4 : ℂ) = ((Real.pi / 4 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hquarter, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
    ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul,
    ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  rw [show
      ((Real.sin (Real.pi / 4) * Real.cosh (Real.pi * t / 2) : ℝ) : ℂ) +
          (Real.cos (Real.pi / 4) * Real.sinh (Real.pi * t / 2) : ℝ) * I =
        ((Real.sin (Real.pi / 4) * Real.cosh (Real.pi * t / 2) : ℝ) : ℂ) +
          (Real.cos (Real.pi / 4) * Real.sinh (Real.pi * t / 2) : ℝ) * I by rfl,
    show
      ((Real.cos (Real.pi / 4) * Real.cosh (Real.pi * t / 2) : ℝ) : ℂ) -
          (Real.sin (Real.pi / 4) * Real.sinh (Real.pi * t / 2) : ℝ) * I =
        ((Real.cos (Real.pi / 4) * Real.cosh (Real.pi * t / 2) : ℝ) : ℂ) +
          (-Real.sin (Real.pi / 4) * Real.sinh (Real.pi * t / 2) : ℝ) * I by
            push_cast
            ring]
  rw [Complex.normSq_add_mul_I, Complex.normSq_add_mul_I,
    Real.sin_pi_div_four, Real.cos_pi_div_four]
  rw [show Real.pi * t = 2 * (Real.pi * t / 2) by ring,
    Real.cosh_two_mul]
  constructor <;> ring_nf <;>
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The half-angle sine and cosine denominators have the same exact norm on
every shifted Taylor contour.  Moving one line left swaps sine and cosine,
so the identity is independent of the shift index. -/
theorem normSq_sin_cos_taylorHalfAngle (n : ℕ) (t : ℝ) :
    Complex.normSq (Complex.sin ((Real.pi : ℂ) *
        routeCGammaShiftedPoint n t / 2)) =
        Real.cosh (Real.pi * t) / 2 ∧
      Complex.normSq (Complex.cos ((Real.pi : ℂ) *
        routeCGammaShiftedPoint n t / 2)) =
        Real.cosh (Real.pi * t) / 2 := by
  induction n with
  | zero => exact normSq_sin_cos_taylorHalfAngle_zero t
  | succ n ih =>
      have harg : (Real.pi : ℂ) * routeCGammaShiftedPoint (n + 1) t / 2 =
          (Real.pi : ℂ) * routeCGammaShiftedPoint n t / 2 -
            (Real.pi : ℂ) / 2 := by
        rw [← routeCGammaShiftedPoint_succ_add_one n t]
        ring
      rw [harg, Complex.sin_sub_pi_div_two,
        Complex.cos_sub_pi_div_two]
      simpa using And.intro ih.2 ih.1

theorem norm_sin_taylorHalfAngle_sq (n : ℕ) (t : ℝ) :
    ‖Complex.sin ((Real.pi : ℂ) *
        routeCGammaShiftedPoint n t / 2)‖ ^ 2 =
      Real.cosh (Real.pi * t) / 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  exact (normSq_sin_cos_taylorHalfAngle n t).1

theorem sin_taylorHalfAngle_ne_zero (n : ℕ) (t : ℝ) :
    Complex.sin ((Real.pi : ℂ) *
      routeCGammaShiftedPoint n t / 2) ≠ 0 := by
  intro h
  have hnorm := norm_sin_taylorHalfAngle_sq n t
  rw [h, norm_zero, zero_pow (by norm_num)] at hnorm
  have hcosh : 0 < Real.cosh (Real.pi * t) := Real.cosh_pos _
  linarith

/-- On every genuine remainder line (`n ≥ 1`), the reflected zeta factor is
uniformly inside its absolutely convergent half-plane. -/
theorem norm_riemannZeta_one_sub_shiftedPoint_le
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    ‖riemannZeta (1 - routeCGammaShiftedPoint n t)‖ ≤ 9 := by
  apply norm_riemannZeta_le_of_re_ge
  simp [routeCGammaShiftedPoint]
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

theorem norm_riemannZeta_one_sub_shiftedPoint_sq_le
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    ‖riemannZeta (1 - routeCGammaShiftedPoint n t) ^ 2‖ ≤ 81 := by
  rw [norm_pow]
  nlinarith [norm_nonneg
    (riemannZeta (1 - routeCGammaShiftedPoint n t)),
    norm_riemannZeta_one_sub_shiftedPoint_le n hn t]

/-- Exact principal-power norm on a shifted Taylor line.  This isolates the
radial Taylor order `n-1/2` from the angular vertical cost. -/
theorem norm_cpow_neg_routeCGammaShiftedPoint
    (u : ℂ) (hu : u ≠ 0) (n : ℕ) (t : ℝ) :
    ‖u ^ (-routeCGammaShiftedPoint n t)‖ =
      ‖u‖ ^ ((n : ℝ) - 1 / 2) * Real.exp (Complex.arg u * t) := by
  rw [Complex.norm_cpow_of_ne_zero hu]
  simp [routeCGammaShiftedPoint]
  rw [Real.exp_neg, div_inv_eq_mul]

/-- On a closed angular sector, the principal power has precisely the
expected exponential loss and no additional vertical factor. -/
theorem norm_cpow_neg_routeCGammaShiftedPoint_le
    (u : ℂ) (hu : u ≠ 0) (n : ℕ) (t θ : ℝ)
    (harg : |Complex.arg u| ≤ θ) :
    ‖u ^ (-routeCGammaShiftedPoint n t)‖ ≤
      ‖u‖ ^ ((n : ℝ) - 1 / 2) * Real.exp (θ * |t|) := by
  rw [norm_cpow_neg_routeCGammaShiftedPoint u hu n t]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (norm_nonneg _) _)
  apply Real.exp_le_exp.mpr
  calc
    Complex.arg u * t ≤ |Complex.arg u| * |t| := by
      simpa [abs_mul] using le_abs_self (Complex.arg u * t)
    _ ≤ θ * |t| := mul_le_mul_of_nonneg_right harg (abs_nonneg t)

/-- Specialization to the line `Re s = -2M-1/2` used by the order-`M`
Taylor remainder. -/
theorem norm_Gamma_taylorRemainderLine_sq_mul_prod (M : ℕ) (t : ℝ) :
    ‖Complex.Gamma (routeCGammaShiftedPoint (2 * M + 1) t)‖ ^ 2 *
        ∏ j ∈ Finset.range (2 * M + 1),
          (((1 / 2 : ℝ) - (2 * M + 1 : ℕ) + j) ^ 2 + t ^ 2) =
      Real.pi / Real.cosh (Real.pi * t) :=
  norm_Gamma_shiftedPoint_sq_mul_prod (2 * M + 1) t

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCGammaShiftedLines
