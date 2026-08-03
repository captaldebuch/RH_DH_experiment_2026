import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannH15MellinAssembly

/-!
# Route B9.2: global H15 Mellin sum--integral exchange

This file proves the analytic interchange deliberately omitted from the
pointwise assembly module.  Euler's integral bounds `Gamma (c+it)` on every
fixed positive vertical line, and the Gaussian evaluation weight absorbs the
opposite-sign `cos (πs)` growth.  A generic `LSeries` Tonelli theorem then
exchanges each absolutely convergent Dirichlet series with the full vertical
integral.  The final theorem lifts both signs through the entire finite H15
`(g,q)` aggregate for every fixed `N`.

The exchange is performed on the natural additive coefficients.  Exact
Kloosterman completion from WP1 can therefore be applied afterwards without
assuming absolute summability of completed Kloosterman modes.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannGlobalExchange

open Complex LSeries MeasureTheory Set
open scoped LSeries.notation
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannInverseMellin
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannFourToTwoCollapse
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannH15MellinAssembly
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannSeries

theorem norm_Gamma_vertical_le_real_Gamma
    (c t : ℝ) (hc : 0 < c) :
    ‖Complex.Gamma (estermannVerticalPoint c t)‖ ≤ Real.Gamma c := by
  have hs : 0 < (estermannVerticalPoint c t).re := by
    simpa using hc
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral]
  calc
    ‖∫ x : ℝ in Ioi 0,
        ((-x).exp : ℂ) * (x : ℂ) ^ (estermannVerticalPoint c t - 1)‖ ≤
      ∫ x : ℝ in Ioi 0,
        ‖((-x).exp : ℂ) *
          (x : ℂ) ^ (estermannVerticalPoint c t - 1)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ x : ℝ in Ioi 0, Real.exp (-x) * x ^ (c - 1) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp [estermannVerticalPoint]
    _ = Real.Gamma c := by
      rw [Real.Gamma_eq_integral hc]

noncomputable def estermannDualGammaVerticalBound
    (q : ℕ) (c : ℝ) : ℝ :=
  Real.rpow (q : ℝ) (c - 1) *
    Real.rpow (2 * Real.pi) (-c) * Real.Gamma c

theorem norm_estermannDualGammaFactor_vertical_le
    (q : ℕ) [NeZero q] (c t : ℝ) (hc : 0 < c) :
    ‖estermannDualGammaFactor q (estermannVerticalPoint c t)‖ ≤
      estermannDualGammaVerticalBound q c := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2cast : (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by
    push_cast
    rfl
  unfold estermannDualGammaFactor estermannDualGammaVerticalBound
  simp only [norm_mul]
  rw [← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hq,
    h2cast,
    Complex.norm_cpow_eq_rpow_re_of_pos h2pi]
  simp only [estermannVerticalPoint, sub_re, add_re, ofReal_re,
    mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero,
    neg_re]
  let A : ℝ := Real.rpow (q : ℝ) (c - 1) *
    Real.rpow (2 * Real.pi) (-c)
  have hA : 0 ≤ A := mul_nonneg
    (Real.rpow_nonneg hq.le (c - 1))
    (Real.rpow_nonneg h2pi.le (-c))
  have hmul :
      A * ‖Complex.Gamma (estermannVerticalPoint c t)‖ ≤
        A * Real.Gamma c :=
    mul_le_mul_of_nonneg_left
      (norm_Gamma_vertical_le_real_Gamma c t hc) hA
  simpa [estermannVerticalPoint] using hmul

noncomputable def estermannCollapsedVerticalBound
    (q : ℕ) (c : ℝ) : ℝ :=
  estermannDualGammaVerticalBound q c ^ 2 *
    (Real.rpow (q : ℝ) (-c) * (q : ℝ) * Real.rpow (q : ℝ) c)

theorem norm_estermannCollapsedCommonFactor_vertical_le
    (q : ℕ) [NeZero q] (c t : ℝ) (hc : 0 < c) :
    ‖estermannCollapsedCommonFactor q (estermannVerticalPoint c t)‖ ≤
      estermannCollapsedVerticalBound q c := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hG := norm_estermannDualGammaFactor_vertical_le q c t hc
  have hQ :
      ‖(q : ℂ) ^ (-estermannVerticalPoint c t) * (q : ℂ) *
          (q : ℂ) ^ (estermannVerticalPoint c t)‖ =
        Real.rpow (q : ℝ) (-c) * (q : ℝ) * Real.rpow (q : ℝ) c := by
    rw [norm_mul, norm_mul, ← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos hq,
      Complex.norm_cpow_eq_rpow_re_of_pos hq]
    simp [estermannVerticalPoint]
  unfold estermannCollapsedCommonFactor estermannCollapsedVerticalBound
  rw [norm_mul, norm_mul, hQ, pow_two]
  have hQnonneg :
      0 ≤ Real.rpow (q : ℝ) (-c) * (q : ℝ) * Real.rpow (q : ℝ) c := by
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hq.le _) (Nat.cast_nonneg _))
      (Real.rpow_nonneg hq.le _)
  have hBnonneg : 0 ≤ estermannDualGammaVerticalBound q c := by
    unfold estermannDualGammaVerticalBound
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hq.le _)
        (Real.rpow_nonneg (by positivity : 0 ≤ 2 * Real.pi) _))
      (Real.Gamma_pos_of_pos hc).le
  exact mul_le_mul_of_nonneg_right
    (mul_self_le_mul_self (norm_nonneg _) hG) hQnonneg

theorem norm_complex_cos_le_exp_abs_im (z : ℂ) :
    ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  have hpos : 0 < (2 : ℝ) := by norm_num
  have hneg : Real.exp (-z.im) ≤ Real.exp |z.im| := by
    rw [Real.exp_le_exp]
    exact neg_le_abs _
  have hpos' : Real.exp z.im ≤ Real.exp |z.im| := by
    rw [Real.exp_le_exp]
    exact le_abs_self _
  unfold Complex.cos
  rw [norm_div]
  norm_num
  rw [show -(z * I) = (-z) * I by ring]
  apply (div_le_iff₀ hpos).2
  calc
    ‖Complex.exp (z * I) + Complex.exp (-z * I)‖ ≤
        ‖Complex.exp (z * I)‖ + ‖Complex.exp (-z * I)‖ := norm_add_le _ _
    _ = Real.exp (-z.im) + Real.exp z.im := by
      rw [Complex.norm_exp, Complex.norm_exp]
      simp [Complex.mul_re]
    _ ≤ Real.exp |z.im| + Real.exp |z.im| := add_le_add hneg hpos'
    _ = Real.exp |z.im| * 2 := by ring

theorem norm_estermannGaussianEvaluationWeight_vertical_le
    (η c t : ℝ) (hc : 1 < c) :
    ‖estermannGaussianEvaluationWeight η (estermannVerticalPoint c t)‖ ≤
      (Real.exp (η * (c - 1) ^ 2) / (c - 1)) *
        Real.exp (-η * t ^ 2) := by
  have hcpos : 0 < c - 1 := sub_pos.mpr hc
  have hden : c - 1 ≤
      ‖estermannVerticalPoint c t - (1 : ℂ)‖ := by
    calc
      c - 1 = |(estermannVerticalPoint c t - (1 : ℂ)).re| := by
        simp [estermannVerticalPoint, abs_of_pos hcpos]
      _ ≤ ‖estermannVerticalPoint c t - (1 : ℂ)‖ :=
        Complex.abs_re_le_norm _
  unfold estermannGaussianEvaluationWeight estermannEvaluationWeight
  rw [norm_div, norm_estermannGaussianDamping_vertical]
  calc
    Real.exp (η * ((c - 1) ^ 2 - t ^ 2)) /
        ‖estermannVerticalPoint c t - (1 : ℂ)‖ ≤
      Real.exp (η * ((c - 1) ^ 2 - t ^ 2)) / (c - 1) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le hcpos hden
    _ = (Real.exp (η * (c - 1) ^ 2) / (c - 1)) *
        Real.exp (-η * t ^ 2) := by
      rw [show η * ((c - 1) ^ 2 - t ^ 2) =
          η * (c - 1) ^ 2 + (-η * t ^ 2) by ring,
        Real.exp_add]
      ring

noncomputable def h15SameSignVerticalMajorantConstant
    (η c : ℝ) (q : ℕ) : ℝ :=
  2 * estermannCollapsedVerticalBound q c *
    (Real.exp (η * (c - 1) ^ 2) / (c - 1))

theorem norm_h15SameSignMellinFactor_vertical_le
    (η c t : ℝ) (q : ℕ) [NeZero q] (hc : 1 < c) :
    ‖h15SameSignMellinFactor (estermannGaussianEvaluationWeight η) q
        (estermannVerticalPoint c t)‖ ≤
      h15SameSignVerticalMajorantConstant η c q *
        Real.exp (-η * t ^ 2) := by
  have hc0 : 0 < c := lt_trans (by norm_num) hc
  have hW := norm_estermannGaussianEvaluationWeight_vertical_le η c t hc
  have hC := norm_estermannCollapsedCommonFactor_vertical_le q c t hc0
  have hB : 0 ≤ estermannCollapsedVerticalBound q c := by
    unfold estermannCollapsedVerticalBound
    exact mul_nonneg (sq_nonneg _)
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
          (Nat.cast_nonneg _))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hE : 0 ≤ Real.exp (η * (c - 1) ^ 2) / (c - 1) := by
    exact div_nonneg (Real.exp_pos _).le (sub_pos.mpr hc).le
  have hG : 0 ≤ Real.exp (-η * t ^ 2) := (Real.exp_pos _).le
  unfold h15SameSignMellinFactor h15SameSignVerticalMajorantConstant
  rw [norm_mul, norm_mul]
  norm_num
  calc
    ‖estermannGaussianEvaluationWeight η (estermannVerticalPoint c t)‖ *
        (2 * ‖estermannCollapsedCommonFactor q
          (estermannVerticalPoint c t)‖) ≤
      (Real.exp (η * (c - 1) ^ 2) / (c - 1) *
          Real.exp (-η * t ^ 2)) *
        (2 * estermannCollapsedVerticalBound q c) := by
          exact mul_le_mul hW (mul_le_mul_of_nonneg_left hC (by norm_num))
            (mul_nonneg (by norm_num) (norm_nonneg _))
            (mul_nonneg hE hG)
    _ = (2 * estermannCollapsedVerticalBound q c *
          (Real.exp (η * (c - 1) ^ 2) / (c - 1))) *
        Real.exp (-(η * t ^ 2)) := by
          rw [neg_mul]
          ring

theorem norm_cos_pi_vertical_le (c t : ℝ) :
    ‖Complex.cos (Real.pi * estermannVerticalPoint c t)‖ ≤
      Real.exp (Real.pi * |t|) := by
  have h := norm_complex_cos_le_exp_abs_im
    (Real.pi * estermannVerticalPoint c t)
  simpa [estermannVerticalPoint, abs_mul, abs_of_pos Real.pi_pos] using h

theorem pi_mul_abs_le_quadratic (η t : ℝ) (hη : 0 < η) :
    Real.pi * |t| ≤
      η / 2 * t ^ 2 + Real.pi ^ 2 / (2 * η) := by
  have hs : 0 ≤ (η * |t| - Real.pi) ^ 2 := sq_nonneg _
  have hden : 0 < 2 * η := mul_pos (by norm_num) hη
  rw [show η / 2 * t ^ 2 + Real.pi ^ 2 / (2 * η) =
      (η ^ 2 * t ^ 2 + Real.pi ^ 2) / (2 * η) by
        field_simp]
  apply (le_div_iff₀ hden).2
  nlinarith [sq_abs t]

theorem gaussian_absorption
    (η t : ℝ) (hη : 0 < η) :
    Real.exp (-η * t ^ 2) * Real.exp (Real.pi * |t|) ≤
      Real.exp (Real.pi ^ 2 / (2 * η)) *
        Real.exp (-(η / 2) * t ^ 2) := by
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have h := pi_mul_abs_le_quadratic η t hη
  nlinarith

noncomputable def h15OppositeSignVerticalMajorantConstant
    (η c : ℝ) (q : ℕ) : ℝ :=
  2 * estermannCollapsedVerticalBound q c *
    (Real.exp (η * (c - 1) ^ 2) / (c - 1)) *
      Real.exp (Real.pi ^ 2 / (2 * η))

theorem norm_h15OppositeSignMellinFactor_vertical_le
    (η c t : ℝ) (q : ℕ) [NeZero q] (hη : 0 < η) (hc : 1 < c) :
    ‖h15OppositeSignMellinFactor (estermannGaussianEvaluationWeight η) q
        (estermannVerticalPoint c t)‖ ≤
      h15OppositeSignVerticalMajorantConstant η c q *
        Real.exp (-(η / 2) * t ^ 2) := by
  have hc0 : 0 < c := lt_trans (by norm_num) hc
  have hW := norm_estermannGaussianEvaluationWeight_vertical_le η c t hc
  have hC := norm_estermannCollapsedCommonFactor_vertical_le q c t hc0
  have hCos := norm_cos_pi_vertical_le c t
  have hB : 0 ≤ estermannCollapsedVerticalBound q c := by
    unfold estermannCollapsedVerticalBound
    exact mul_nonneg (sq_nonneg _)
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
          (Nat.cast_nonneg _))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hE : 0 ≤ Real.exp (η * (c - 1) ^ 2) / (c - 1) := by
    exact div_nonneg (Real.exp_pos _).le (sub_pos.mpr hc).le
  unfold h15OppositeSignMellinFactor
    h15OppositeSignVerticalMajorantConstant
  rw [norm_mul, norm_mul, norm_mul]
  norm_num
  calc
    ‖estermannGaussianEvaluationWeight η (estermannVerticalPoint c t)‖ *
        (2 * ‖Complex.cos (Real.pi * estermannVerticalPoint c t)‖ *
          ‖estermannCollapsedCommonFactor q
            (estermannVerticalPoint c t)‖) ≤
      ((Real.exp (η * (c - 1) ^ 2) / (c - 1)) *
          Real.exp (-η * t ^ 2)) *
        (2 * Real.exp (Real.pi * |t|) *
          estermannCollapsedVerticalBound q c) := by
            gcongr
    _ = (2 * estermannCollapsedVerticalBound q c *
          (Real.exp (η * (c - 1) ^ 2) / (c - 1))) *
        (Real.exp (-η * t ^ 2) * Real.exp (Real.pi * |t|)) := by ring
    _ ≤ (2 * estermannCollapsedVerticalBound q c *
          (Real.exp (η * (c - 1) ^ 2) / (c - 1))) *
        (Real.exp (Real.pi ^ 2 / (2 * η)) *
          Real.exp (-(η / 2) * t ^ 2)) := by
            exact mul_le_mul_of_nonneg_left (gaussian_absorption η t hη)
              (mul_nonneg (mul_nonneg (by positivity) hB) hE)
    _ = 2 * estermannCollapsedVerticalBound q c *
        (Real.exp (η * (c - 1) ^ 2) / (c - 1)) *
        Real.exp (Real.pi ^ 2 / (2 * η)) *
          Real.exp (-(η / 2 * t ^ 2)) := by
            rw [neg_mul]
            ring

theorem continuous_estermannGaussianEvaluationWeight_vertical
    (η c : ℝ) (hc : 1 < c) :
    Continuous (fun t : ℝ =>
      estermannGaussianEvaluationWeight η (estermannVerticalPoint c t)) := by
  have hs : Continuous (fun t : ℝ => estermannVerticalPoint c t) := by
    unfold estermannVerticalPoint
    fun_prop
  have hden : ∀ t : ℝ, estermannVerticalPoint c t - (1 : ℂ) ≠ 0 := by
    intro t h
    have hre := congrArg Complex.re h
    simp [estermannVerticalPoint] at hre
    linarith
  unfold estermannGaussianEvaluationWeight estermannEvaluationWeight
    estermannGaussianDamping
  exact (Complex.continuous_exp.comp
    (continuous_const.mul ((hs.sub continuous_const).pow 2))).div
      (hs.sub continuous_const) hden

theorem continuous_estermannCollapsedCommonFactor_vertical
    (c : ℝ) (q : ℕ) [NeZero q] (hc : 0 < c) :
    Continuous (fun t : ℝ =>
      estermannCollapsedCommonFactor q (estermannVerticalPoint c t)) := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have h2pi : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
  have hs : Continuous (fun t : ℝ => estermannVerticalPoint c t) := by
    unfold estermannVerticalPoint
    fun_prop
  have hGamma : Continuous (fun t : ℝ =>
      Complex.Gamma (estermannVerticalPoint c t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    apply (Complex.continuousAt_Gamma _ ?_).comp hs.continuousAt
    intro m hm
    have hre := congrArg Complex.re hm
    simp [estermannVerticalPoint] at hre
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hDual : Continuous (fun t : ℝ =>
      estermannDualGammaFactor q (estermannVerticalPoint c t)) := by
    unfold estermannDualGammaFactor
    exact (((hs.sub continuous_const).const_cpow (Or.inl hq)).mul
      (hs.neg.const_cpow (Or.inl h2pi))).mul hGamma
  unfold estermannCollapsedCommonFactor
  exact (hDual.mul hDual).mul
    (((hs.neg.const_cpow (Or.inl hq)).mul continuous_const).mul
      (hs.const_cpow (Or.inl hq)))

theorem continuous_h15SameSignMellinFactor_vertical
    (η c : ℝ) (q : ℕ) [NeZero q] (hc : 1 < c) :
    Continuous (fun t : ℝ =>
      h15SameSignMellinFactor (estermannGaussianEvaluationWeight η) q
        (estermannVerticalPoint c t)) := by
  unfold h15SameSignMellinFactor
  exact (continuous_estermannGaussianEvaluationWeight_vertical η c hc).mul
    (continuous_const.mul
      (continuous_estermannCollapsedCommonFactor_vertical c q
        (lt_trans (by norm_num) hc)))

theorem continuous_h15OppositeSignMellinFactor_vertical
    (η c : ℝ) (q : ℕ) [NeZero q] (hc : 1 < c) :
    Continuous (fun t : ℝ =>
      h15OppositeSignMellinFactor (estermannGaussianEvaluationWeight η) q
        (estermannVerticalPoint c t)) := by
  have hs : Continuous (fun t : ℝ => estermannVerticalPoint c t) := by
    unfold estermannVerticalPoint
    fun_prop
  unfold h15OppositeSignMellinFactor
  exact (continuous_estermannGaussianEvaluationWeight_vertical η c hc).mul
    ((continuous_const.mul (Complex.continuous_cos.comp
      (continuous_const.mul hs))).mul
        (continuous_estermannCollapsedCommonFactor_vertical c q
          (lt_trans (by norm_num) hc)))

theorem integrable_h15SameSignMellinFactor_vertical
    (η c : ℝ) (q : ℕ) [NeZero q] (hη : 0 < η) (hc : 1 < c) :
    Integrable (fun t : ℝ =>
      h15SameSignMellinFactor (estermannGaussianEvaluationWeight η) q
        (estermannVerticalPoint c t)) := by
  apply Integrable.mono'
    ((integrable_exp_neg_mul_sq hη).const_mul
      (h15SameSignVerticalMajorantConstant η c q))
    (continuous_h15SameSignMellinFactor_vertical η c q hc).aestronglyMeasurable
  filter_upwards [] with t
  exact norm_h15SameSignMellinFactor_vertical_le η c t q hc

theorem integrable_h15OppositeSignMellinFactor_vertical
    (η c : ℝ) (q : ℕ) [NeZero q] (hη : 0 < η) (hc : 1 < c) :
    Integrable (fun t : ℝ =>
      h15OppositeSignMellinFactor (estermannGaussianEvaluationWeight η) q
        (estermannVerticalPoint c t)) := by
  have hη2 : 0 < η / 2 := div_pos hη (by norm_num)
  apply Integrable.mono'
    ((integrable_exp_neg_mul_sq hη2).const_mul
      (h15OppositeSignVerticalMajorantConstant η c q))
    (continuous_h15OppositeSignMellinFactor_vertical η c q hc).aestronglyMeasurable
  filter_upwards [] with t
  exact norm_h15OppositeSignMellinFactor_vertical_le η c t q hη hc

theorem norm_LSeries_term_vertical
    (a : ℕ → ℂ) (c t : ℝ) (n : ℕ) :
    ‖LSeries.term a (estermannVerticalPoint c t) n‖ =
      ‖LSeries.term a (c : ℂ) n‖ := by
  by_cases hn : n = 0
  · simp [hn]
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
      norm_div, norm_div, ← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos hnpos,
      Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
    simp [estermannVerticalPoint]

theorem continuous_LSeries_term_vertical
    (a : ℕ → ℂ) (c : ℝ) (n : ℕ) :
    Continuous (fun t : ℝ =>
      LSeries.term a (estermannVerticalPoint c t) n) := by
  by_cases hn : n = 0
  · subst n
    simpa using (continuous_const : Continuous fun _ : ℝ => (0 : ℂ))
  · simp only [LSeries.term_of_ne_zero hn]
    have hncast : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hs : Continuous fun t : ℝ => estermannVerticalPoint c t := by
      unfold estermannVerticalPoint
      fun_prop
    have hpow : Continuous fun t : ℝ =>
        (n : ℂ) ^ (estermannVerticalPoint c t) :=
      hs.const_cpow (Or.inl hncast)
    exact continuous_const.div hpow fun _ => cpow_ne_zero_iff.mpr (Or.inl hncast)

theorem integrable_mul_LSeries_term_vertical
    (F : ℝ → ℂ) (a : ℕ → ℂ) (c : ℝ)
    (hF : Integrable F) (n : ℕ) :
    Integrable (fun t : ℝ =>
      F t * LSeries.term a (estermannVerticalPoint c t) n) := by
  apply hF.mul_bdd
  · exact (continuous_LSeries_term_vertical a c n).aestronglyMeasurable
  · filter_upwards [] with t
    exact (norm_LSeries_term_vertical a c t n).le

theorem integral_norm_mul_LSeries_term_vertical
    (F : ℝ → ℂ) (a : ℕ → ℂ) (c : ℝ) (n : ℕ) :
    (∫ t : ℝ,
        ‖F t * LSeries.term a (estermannVerticalPoint c t) n‖) =
      (∫ t : ℝ, ‖F t‖) * ‖LSeries.term a (c : ℂ) n‖ := by
  calc
    (∫ t : ℝ,
        ‖F t * LSeries.term a (estermannVerticalPoint c t) n‖) =
      ∫ t : ℝ, ‖F t‖ * ‖LSeries.term a (c : ℂ) n‖ := by
        apply integral_congr_ae
        filter_upwards [] with t
        rw [norm_mul, norm_LSeries_term_vertical]
    _ = (∫ t : ℝ, ‖F t‖) *
        ‖LSeries.term a (c : ℂ) n‖ := by rw [integral_mul_const]

theorem summable_integral_norm_mul_LSeries_term_vertical
    (F : ℝ → ℂ) (a : ℕ → ℂ) (c : ℝ)
    (_hF : Integrable F) (ha : LSeriesSummable a (c : ℂ)) :
    Summable fun n : ℕ =>
      ∫ t : ℝ,
        ‖F t * LSeries.term a (estermannVerticalPoint c t) n‖ := by
  have haNorm : Summable fun n : ℕ =>
      ‖LSeries.term a (c : ℂ) n‖ := by
    rw [summable_norm_iff]
    exact ha
  have hmul := Summable.mul_left (∫ t : ℝ, ‖F t‖) haNorm
  exact hmul.congr fun n =>
    (integral_norm_mul_LSeries_term_vertical F a c n).symm

/-- Global termwise integration for a vertical `LSeries`, assuming only an
integrable common factor and absolute convergence on the real line `c`. -/
theorem integral_mul_LSeries_vertical_eq_tsum_integral
    (F : ℝ → ℂ) (a : ℕ → ℂ) (c : ℝ)
    (hF : Integrable F) (ha : LSeriesSummable a (c : ℂ)) :
    (∫ t : ℝ,
        F t * LSeries a (estermannVerticalPoint c t)) =
      ∑' n : ℕ, ∫ t : ℝ,
        F t * LSeries.term a (estermannVerticalPoint c t) n := by
  rw [show (fun t : ℝ => F t * LSeries a (estermannVerticalPoint c t)) =
      fun t : ℝ => ∑' n : ℕ,
        F t * LSeries.term a (estermannVerticalPoint c t) n by
    funext t
    unfold LSeries
    rw [tsum_mul_left]]
  exact (integral_tsum_of_summable_integral_norm
    (integrable_mul_LSeries_term_vertical F a c hF)
    (summable_integral_norm_mul_LSeries_term_vertical F a c hF ha)).symm

theorem integrable_mul_LSeries_vertical
    (F : ℝ → ℂ) (a : ℕ → ℂ) (c : ℝ)
    (hF : Integrable F) (ha : LSeriesSummable a (c : ℂ)) :
    Integrable (fun t : ℝ =>
      F t * LSeries a (estermannVerticalPoint c t)) := by
  let C : ℝ := ∑' n : ℕ, ‖LSeries.term a (c : ℂ) n‖
  have haNorm : Summable fun n : ℕ => ‖LSeries.term a (c : ℂ) n‖ := by
    rw [summable_norm_iff]
    exact ha
  have haNormVertical (t : ℝ) : Summable fun n : ℕ =>
      ‖LSeries.term a (estermannVerticalPoint c t) n‖ :=
    haNorm.congr fun n => (norm_LSeries_term_vertical a c t n).symm
  have hmeasLS : AEStronglyMeasurable (fun t : ℝ =>
      LSeries a (estermannVerticalPoint c t)) := by
    unfold LSeries
    exact AEStronglyMeasurable.tsum fun n =>
      (continuous_LSeries_term_vertical a c n).aestronglyMeasurable
  apply Integrable.mono' (hF.norm.const_mul C)
    (hF.1.mul hmeasLS)
  filter_upwards [] with t
  change ‖F t * LSeries a (estermannVerticalPoint c t)‖ ≤ C * ‖F t‖
  rw [norm_mul]
  rw [mul_comm C]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  unfold LSeries
  calc
    ‖∑' n : ℕ, LSeries.term a (estermannVerticalPoint c t) n‖ ≤
        ∑' n : ℕ, ‖LSeries.term a (estermannVerticalPoint c t) n‖ :=
      norm_tsum_le_tsum_norm (haNormVertical t)
    _ = C := by
      unfold C
      apply tsum_congr
      intro n
      exact norm_LSeries_term_vertical a c t n

theorem h15SameSignCoefficient_summable
    (N g q : ℕ) [NeZero q] {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (h15SameSignCoefficient N g q) s := by
  classical
  rw [h15SameSignCoefficient_eq_finsetSum]
  apply LSeriesSummable.sum
  intro a _
  by_cases hcop : Nat.Coprime a q
  · unfold h15SameSignNaturalCoefficient
    rw [dif_pos hcop]
    exact (estermannCoeff_summable _ _ hs).smul _
  · simp [h15SameSignNaturalCoefficient, hcop]

theorem h15OppositeSignCoefficient_summable
    (N g q : ℕ) [NeZero q] {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (h15OppositeSignCoefficient N g q) s := by
  classical
  rw [h15OppositeSignCoefficient_eq_finsetSum]
  apply LSeriesSummable.sum
  intro a _
  by_cases hcop : Nat.Coprime a q
  · unfold h15OppositeSignNaturalCoefficient
    rw [dif_pos hcop]
    exact (estermannCoeff_summable _ _ hs).smul _
  · simp [h15OppositeSignNaturalCoefficient, hcop]

theorem h15SameSign_global_exchange
    (N g q : ℕ) [NeZero q] (η c : ℝ) (hη : 0 < η) (hc : 1 < c) :
    (∫ t : ℝ,
        h15SameSignMellinFactor (estermannGaussianEvaluationWeight η) q
            (estermannVerticalPoint c t) *
          h15SameSignDirichletSeries N g q
            (estermannVerticalPoint c t)) =
      ∑' n : ℕ, ∫ t : ℝ,
        h15SameSignMellinFactor (estermannGaussianEvaluationWeight η) q
            (estermannVerticalPoint c t) *
          LSeries.term (h15SameSignCoefficient N g q)
            (estermannVerticalPoint c t) n := by
  apply integral_mul_LSeries_vertical_eq_tsum_integral
  · exact integrable_h15SameSignMellinFactor_vertical η c q hη hc
  · apply h15SameSignCoefficient_summable
    simpa using hc

theorem h15OppositeSign_global_exchange
    (N g q : ℕ) [NeZero q] (η c : ℝ) (hη : 0 < η) (hc : 1 < c) :
    (∫ t : ℝ,
        h15OppositeSignMellinFactor (estermannGaussianEvaluationWeight η) q
            (estermannVerticalPoint c t) *
          h15OppositeSignDirichletSeries N g q
            (estermannVerticalPoint c t)) =
      ∑' n : ℕ, ∫ t : ℝ,
        h15OppositeSignMellinFactor (estermannGaussianEvaluationWeight η) q
            (estermannVerticalPoint c t) *
          LSeries.term (h15OppositeSignCoefficient N g q)
            (estermannVerticalPoint c t) n := by
  apply integral_mul_LSeries_vertical_eq_tsum_integral
  · exact integrable_h15OppositeSignMellinFactor_vertical η c q hη hc
  · apply h15OppositeSignCoefficient_summable
    simpa using hc

noncomputable def h15SameSignTermwiseVerticalIntegral
    (N g q : ℕ) [NeZero q] (η c : ℝ) : ℂ :=
  ∑' n : ℕ, ∫ t : ℝ,
    h15SameSignMellinFactor (estermannGaussianEvaluationWeight η) q
        (estermannVerticalPoint c t) *
      LSeries.term (h15SameSignCoefficient N g q)
        (estermannVerticalPoint c t) n

noncomputable def h15OppositeSignTermwiseVerticalIntegral
    (N g q : ℕ) [NeZero q] (η c : ℝ) : ℂ :=
  ∑' n : ℕ, ∫ t : ℝ,
    h15OppositeSignMellinFactor (estermannGaussianEvaluationWeight η) q
        (estermannVerticalPoint c t) *
      LSeries.term (h15OppositeSignCoefficient N g q)
        (estermannVerticalPoint c t) n

noncomputable def h15TwoSignTermwiseVerticalIntegral
    (N g q : ℕ) [NeZero q] (η c : ℝ) : ℂ :=
  h15SameSignTermwiseVerticalIntegral N g q η c +
    h15OppositeSignTermwiseVerticalIntegral N g q η c

theorem integrable_h15TwoSignAdditiveIntegrand_vertical
    (N g q : ℕ) [NeZero q] (η c : ℝ) (hη : 0 < η) (hc : 1 < c) :
    Integrable (fun t : ℝ =>
      h15TwoSignAdditiveIntegrand N g q
        (estermannGaussianEvaluationWeight η)
        (estermannVerticalPoint c t)) := by
  unfold h15TwoSignAdditiveIntegrand h15SameSignDirichletSeries
    h15OppositeSignDirichletSeries
  apply Integrable.add
  · apply integrable_mul_LSeries_vertical
    · exact integrable_h15SameSignMellinFactor_vertical η c q hη hc
    · apply h15SameSignCoefficient_summable
      simpa using hc
  · apply integrable_mul_LSeries_vertical
    · exact integrable_h15OppositeSignMellinFactor_vertical η c q hη hc
    · apply h15OppositeSignCoefficient_summable
      simpa using hc

theorem h15TwoSign_global_exchange
    (N g q : ℕ) [NeZero q] (η c : ℝ) (hη : 0 < η) (hc : 1 < c) :
    (∫ t : ℝ,
      h15TwoSignAdditiveIntegrand N g q
        (estermannGaussianEvaluationWeight η)
        (estermannVerticalPoint c t)) =
      h15TwoSignTermwiseVerticalIntegral N g q η c := by
  unfold h15TwoSignAdditiveIntegrand h15TwoSignTermwiseVerticalIntegral
    h15SameSignTermwiseVerticalIntegral h15OppositeSignTermwiseVerticalIntegral
  rw [integral_add]
  · rw [h15SameSign_global_exchange N g q η c hη hc,
      h15OppositeSign_global_exchange N g q η c hη hc]
  · unfold h15SameSignDirichletSeries
    apply integrable_mul_LSeries_vertical
    · exact integrable_h15SameSignMellinFactor_vertical η c q hη hc
    · apply h15SameSignCoefficient_summable
      simpa using hc
  · unfold h15OppositeSignDirichletSeries
    apply integrable_mul_LSeries_vertical
    · exact integrable_h15OppositeSignMellinFactor_vertical η c q hη hc
    · apply h15OppositeSignCoefficient_summable
      simpa using hc

noncomputable def h15InteriorTwoSignAdditiveIntegrand
    (N : ℕ) (W : ℂ → ℂ) (s : ℂ) : ℂ :=
  ∑ g ∈ Finset.Icc 1 N,
    ∑ q ∈ Finset.Icc 2 (N / g),
      if hq : 0 < q then
        @h15TwoSignAdditiveIntegrand N g q
          ⟨Nat.ne_of_gt hq⟩ W s
      else 0

noncomputable def h15InteriorTermwiseVerticalIntegral
    (N : ℕ) (η c : ℝ) : ℂ :=
  ∑ g ∈ Finset.Icc 1 N,
    ∑ q ∈ Finset.Icc 2 (N / g),
      if hq : 0 < q then
        @h15TwoSignTermwiseVerticalIntegral N g q
          ⟨Nat.ne_of_gt hq⟩ η c
      else 0

theorem h15InteriorNaturalDualIntegrand_eq_twoSignAdditive
    (N : ℕ) (W : ℂ → ℂ) {s : ℂ} (hs : 1 < s.re) :
    h15InteriorNaturalDualIntegrand N W s =
      h15InteriorTwoSignAdditiveIntegrand N W s := by
  classical
  unfold h15InteriorNaturalDualIntegrand
    h15InteriorTwoSignAdditiveIntegrand
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro q hqmem
  have hq : 0 < q := by
    have := (Finset.mem_Icc.mp hqmem).1
    omega
  rw [dif_pos hq, dif_pos hq]
  exact @h15NaturalNumeratorDualIntegrand_eq_twoSignAdditive N g q
    ⟨Nat.ne_of_gt hq⟩ W s hs

theorem integrable_h15ConditionalTwoSignRow_vertical
    (N g q : ℕ) (η c : ℝ) (hη : 0 < η) (hc : 1 < c) :
    Integrable (fun t : ℝ =>
      if hq : 0 < q then
        @h15TwoSignAdditiveIntegrand N g q
          ⟨Nat.ne_of_gt hq⟩ (estermannGaussianEvaluationWeight η)
          (estermannVerticalPoint c t)
      else 0) := by
  by_cases hq : 0 < q
  · simp only [dif_pos hq]
    exact @integrable_h15TwoSignAdditiveIntegrand_vertical N g q
      ⟨Nat.ne_of_gt hq⟩ η c hη hc
  · simp only [dif_neg hq]
    exact integrable_zero ℝ ℂ volume

theorem integrable_h15InteriorTwoSignAdditiveIntegrand_vertical
    (N : ℕ) (η c : ℝ) (hη : 0 < η) (hc : 1 < c) :
    Integrable (fun t : ℝ =>
      h15InteriorTwoSignAdditiveIntegrand N
        (estermannGaussianEvaluationWeight η)
        (estermannVerticalPoint c t)) := by
  unfold h15InteriorTwoSignAdditiveIntegrand
  apply integrable_finsetSum
  intro g _
  apply integrable_finsetSum
  intro q _
  exact integrable_h15ConditionalTwoSignRow_vertical N g q η c hη hc

theorem integral_h15InteriorTwoSignAdditive_eq_rowIntegrals
    (N : ℕ) (η c : ℝ) (hη : 0 < η) (hc : 1 < c) :
    (∫ t : ℝ,
      h15InteriorTwoSignAdditiveIntegrand N
        (estermannGaussianEvaluationWeight η)
        (estermannVerticalPoint c t)) =
      ∑ g ∈ Finset.Icc 1 N,
        ∑ q ∈ Finset.Icc 2 (N / g),
          if hq : 0 < q then
            ∫ t : ℝ,
              @h15TwoSignAdditiveIntegrand N g q
                ⟨Nat.ne_of_gt hq⟩
                (estermannGaussianEvaluationWeight η)
                (estermannVerticalPoint c t)
          else 0 := by
  unfold h15InteriorTwoSignAdditiveIntegrand
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro g hg
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro q hqmem
      by_cases hq : 0 < q <;> simp [hq]
    · intro q hqmem
      exact integrable_h15ConditionalTwoSignRow_vertical N g q η c hη hc
  · intro g hg
    apply integrable_finsetSum
    intro q hqmem
    exact integrable_h15ConditionalTwoSignRow_vertical N g q η c hη hc

/-- The full fixed-`N` global exchange.  The infinite Dirichlet sums are
exchanged with the complete vertical integral before the finite H15
`(g,q)` aggregation is rewritten into completed Kloosterman coordinates. -/
theorem h15Interior_global_sum_integral_exchange
    (N : ℕ) (η c : ℝ) (hη : 0 < η) (hc : 1 < c) :
    (∫ t : ℝ,
      h15InteriorNaturalDualIntegrand N
        (estermannGaussianEvaluationWeight η)
        (estermannVerticalPoint c t)) =
      h15InteriorTermwiseVerticalIntegral N η c := by
  calc
    (∫ t : ℝ,
      h15InteriorNaturalDualIntegrand N
        (estermannGaussianEvaluationWeight η)
        (estermannVerticalPoint c t)) =
      ∫ t : ℝ,
        h15InteriorTwoSignAdditiveIntegrand N
          (estermannGaussianEvaluationWeight η)
          (estermannVerticalPoint c t) := by
            apply integral_congr_ae
            filter_upwards [] with t
            apply h15InteriorNaturalDualIntegrand_eq_twoSignAdditive
            simpa [estermannVerticalPoint] using hc
    _ = ∑ g ∈ Finset.Icc 1 N,
        ∑ q ∈ Finset.Icc 2 (N / g),
          if hq : 0 < q then
            ∫ t : ℝ,
              @h15TwoSignAdditiveIntegrand N g q
                ⟨Nat.ne_of_gt hq⟩
                (estermannGaussianEvaluationWeight η)
                (estermannVerticalPoint c t)
          else 0 :=
      integral_h15InteriorTwoSignAdditive_eq_rowIntegrals N η c hη hc
    _ = h15InteriorTermwiseVerticalIntegral N η c := by
      unfold h15InteriorTermwiseVerticalIntegral
      apply Finset.sum_congr rfl
      intro g _
      apply Finset.sum_congr rfl
      intro q hqmem
      have hq : 0 < q := by
        have := (Finset.mem_Icc.mp hqmem).1
        omega
      rw [dif_pos hq, dif_pos hq]
      exact @h15TwoSign_global_exchange N g q
        ⟨Nat.ne_of_gt hq⟩ η c hη hc

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannGlobalExchange
