import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCAbelRightLine

/-!
# Route C: the scalar Hurwitz bound on the reflected Abel line

This module supplies the scalar source estimate left open by the right-line
reduction.  At `s = -1/2 + it`, the Hurwitz functional equation reflects to
`3/2 - it`, where both exponential zeta functions are absolutely convergent.
Their common norm is controlled by one constant-coefficient `LSeries` mass.
The exponential factors in the functional equation then cancel the intrinsic
Gamma decay proved in the Abel Mellin module.

The result is an unconditional inhabitant of
`HurwitzFixedVerticalLineGrowth (-1/2)` with no modulus loss and linear
vertical growth.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelHurwitzGrowth

open Complex Filter Topology
open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannContourShift
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVerticalBounds
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelMellin
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelReflectionWeight
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelRightLine
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelRightLine.HurwitzFixedVerticalLineGrowth

/-- The absolutely convergent norm mass of the constant Dirichlet series on
`Re(s)=3/2`.  It is the common majorant for every additive phase. -/
noncomputable def unitThreeHalvesNormMass : ℝ :=
  ∑' n : ℕ, ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) (3 / 2 : ℂ) n‖

theorem summable_unitThreeHalvesNorm :
    Summable (fun n : ℕ =>
      ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) (3 / 2 : ℂ) n‖) := by
  exact (LSeriesSummable_of_bounded_of_one_lt_re
    (m := 1) (fun n hn => by simp) (s := (3 / 2 : ℂ)) (by norm_num)).norm

theorem unitThreeHalvesNormMass_nonneg :
    0 ≤ unitThreeHalvesNormMass := by
  unfold unitThreeHalvesNormMass
  exact tsum_nonneg fun _ => norm_nonneg _

set_option maxHeartbeats 800000 in
/-- Every rational additive zeta on the reflected line is bounded by the
same absolutely convergent norm mass. -/
theorem norm_expZeta_three_halves_sub_I_mul_le
    (q : ℕ) [NeZero q] (r : ZMod q) (t : ℝ) :
    ‖HurwitzZeta.expZeta (ZMod.toAddCircle r)
        (((3 / 2 : ℝ) : ℂ) - (t : ℂ) * I)‖ ≤
      unitThreeHalvesNormMass := by
  let s : ℂ := ((3 / 2 : ℝ) : ℂ) - (t : ℂ) * I
  have hs : 1 < s.re := by
    dsimp [s]
    norm_num
  rw [ZMod.toAddCircle_apply]
  let coeff : ℕ → ℂ := fun n =>
    Complex.exp (2 * Real.pi * I * (r.val / q : ℝ) * n)
  have hsum : LSeriesHasSum coeff s
      (HurwitzZeta.expZeta (r.val / q : ℝ) s) := by
    simpa [coeff] using
      (HurwitzZeta.LSeriesHasSum_exp (r.val / q : ℝ) hs)
  rw [← hsum.LSeries_eq]
  unfold LSeries unitThreeHalvesNormMass
  calc
    ‖∑' n : ℕ,
        LSeries.term coeff s n‖ ≤
      ∑' n : ℕ,
        ‖LSeries.term coeff s n‖ :=
      norm_tsum_le_tsum_norm hsum.LSeriesSummable.norm
    _ = ∑' n : ℕ,
        ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) (3 / 2 : ℂ) n‖ := by
      apply tsum_congr
      intro n
      rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
      split_ifs with hn
      · rfl
      · simp [coeff, s, Complex.norm_exp]

/-- Either exponential factor in the Hurwitz functional equation has at
most the symmetric growth `exp (pi |t| / 2)`. -/
theorem norm_exp_neg_pi_I_mul_threeHalves_sub_I_mul_div_two_le
    (t : ℝ) :
    ‖Complex.exp
        (-Real.pi * I *
          (((3 / 2 : ℝ) : ℂ) - (t : ℂ) * I) / 2)‖ ≤
      Real.exp (Real.pi * |t| / 2) := by
  rw [Complex.norm_exp, Real.exp_le_exp]
  simp only [div_eq_mul_inv, Complex.neg_re, Complex.mul_re,
    Complex.sub_re]
  norm_num
  have ht : -|t| ≤ t := neg_abs_le t
  nlinarith [Real.pi_pos]

theorem norm_exp_pi_I_mul_threeHalves_sub_I_mul_div_two_le
    (t : ℝ) :
    ‖Complex.exp
        (Real.pi * I *
          (((3 / 2 : ℝ) : ℂ) - (t : ℂ) * I) / 2)‖ ≤
      Real.exp (Real.pi * |t| / 2) := by
  rw [Complex.norm_exp, Real.exp_le_exp]
  simp only [div_eq_mul_inv, Complex.mul_re, Complex.sub_re]
  norm_num
  have ht : t ≤ |t| := le_abs_self t
  nlinarith [Real.pi_pos]

/-- Gamma's intrinsic decay exactly absorbs the worst of the two exponential
factors in the Hurwitz functional equation. -/
theorem norm_Gamma_threeHalves_sub_I_mul_mul_exp_le (t : ℝ) :
    ‖Complex.Gamma
        (((3 / 2 : ℝ) : ℂ) - (t : ℂ) * I)‖ *
        Real.exp (Real.pi * |t| / 2) ≤
      Real.sqrt (2 * Real.pi) * (1 + |t|) := by
  have harg :
      (((3 / 2 : ℝ) : ℂ) - (t : ℂ) * I) =
        ((3 / 2 : ℝ) : ℂ) + I * (-t : ℝ) := by
    push_cast
    ring
  rw [harg]
  have hGamma := norm_Gamma_three_halves_add_I_mul_le_majorant (-t)
  have hexp : 0 ≤ Real.exp (Real.pi * |t| / 2) :=
    (Real.exp_pos _).le
  have hmul := mul_le_mul_of_nonneg_right hGamma hexp
  unfold gammaThreeHalvesMajorant at hmul
  calc
    ‖Complex.Gamma
        (((3 / 2 : ℝ) : ℂ) + I * (-t : ℝ))‖ *
        Real.exp (Real.pi * |t| / 2) ≤
      (Real.sqrt (2 * Real.pi) * (1 + |-t|) *
        Real.exp (-(Real.pi / 2) * |-t|)) *
          Real.exp (Real.pi * |t| / 2) := hmul
    _ = Real.sqrt (2 * Real.pi) * (1 + |t|) := by
      rw [abs_neg, mul_assoc, ← Real.exp_add]
      have : -(Real.pi / 2) * |t| + Real.pi * |t| / 2 = 0 := by ring
      rw [this, Real.exp_zero, mul_one]

/-- The explicit constant in the reflected-line Hurwitz estimate. -/
noncomputable def hurwitzNegativeHalfGrowthConstant : ℝ :=
  2 * Real.rpow (2 * Real.pi) (-(3 / 2 : ℝ)) *
    Real.sqrt (2 * Real.pi) * unitThreeHalvesNormMass

theorem hurwitzNegativeHalfGrowthConstant_nonneg :
    0 ≤ hurwitzNegativeHalfGrowthConstant := by
  unfold hurwitzNegativeHalfGrowthConstant
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num)
        (Real.rpow_nonneg (by positivity) _))
      (Real.sqrt_nonneg _))
    unitThreeHalvesNormMass_nonneg

set_option maxHeartbeats 800000 in
/-- The scalar Hurwitz zeta has uniform linear growth on the complete line
`Re(s)=-1/2`, uniformly over all rational parameters and moduli. -/
theorem norm_hurwitzZeta_negative_half_add_I_mul_le
    (q : ℕ) [NeZero q] (r : ZMod q) (t : ℝ) :
    ‖HurwitzZeta.hurwitzZeta (ZMod.toAddCircle r)
        (estermannVerticalPoint (-1 / 2 : ℝ) t)‖ ≤
      hurwitzNegativeHalfGrowthConstant * (1 + |t|) := by
  let s : ℂ := ((3 / 2 : ℝ) : ℂ) - (t : ℂ) * I
  let x : UnitAddCircle := ZMod.toAddCircle r
  have hsNat : ∀ n : ℕ, s ≠ -n := by
    intro n h
    have hre := congrArg Complex.re h
    norm_num [s] at hre
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [s] at hre
  have htarget :
      estermannVerticalPoint (-1 / 2 : ℝ) t = 1 - s := by
    unfold estermannVerticalPoint
    dsimp [s]
    push_cast
    ring
  rw [htarget, HurwitzZeta.hurwitzZeta_one_sub x hsNat (Or.inr hs1)]
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2cast : (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by
    push_cast
    rfl
  have hpow :
      ‖(2 * Real.pi : ℂ) ^ (-s)‖ =
        Real.rpow (2 * Real.pi) (-(3 / 2 : ℝ)) := by
    rw [h2cast, Complex.norm_cpow_eq_rpow_re_of_pos h2pi]
    simp [s]
  have hzetaPos :
      ‖HurwitzZeta.expZeta x s‖ ≤ unitThreeHalvesNormMass := by
    simpa [x, s] using norm_expZeta_three_halves_sub_I_mul_le q r t
  have hzetaNeg :
      ‖HurwitzZeta.expZeta (-x) s‖ ≤ unitThreeHalvesNormMass := by
    simpa [x, s] using norm_expZeta_three_halves_sub_I_mul_le q (-r) t
  have hexpNeg :=
    norm_exp_neg_pi_I_mul_threeHalves_sub_I_mul_div_two_le t
  have hexpPos :=
    norm_exp_pi_I_mul_threeHalves_sub_I_mul_div_two_le t
  have hexpNonneg : 0 ≤ Real.exp (Real.pi * |t| / 2) :=
    (Real.exp_pos _).le
  have hmassNonneg : 0 ≤ unitThreeHalvesNormMass :=
    unitThreeHalvesNormMass_nonneg
  have hbracket :
      ‖Complex.exp (-Real.pi * I * s / 2) *
          HurwitzZeta.expZeta x s +
        Complex.exp (Real.pi * I * s / 2) *
          HurwitzZeta.expZeta (-x) s‖ ≤
        2 * Real.exp (Real.pi * |t| / 2) *
          unitThreeHalvesNormMass := by
    calc
      ‖Complex.exp (-Real.pi * I * s / 2) *
          HurwitzZeta.expZeta x s +
        Complex.exp (Real.pi * I * s / 2) *
          HurwitzZeta.expZeta (-x) s‖ ≤
        ‖Complex.exp (-Real.pi * I * s / 2)‖ *
            ‖HurwitzZeta.expZeta x s‖ +
          ‖Complex.exp (Real.pi * I * s / 2)‖ *
            ‖HurwitzZeta.expZeta (-x) s‖ := by
        simpa only [norm_mul] using norm_add_le
          (Complex.exp (-Real.pi * I * s / 2) *
            HurwitzZeta.expZeta x s)
          (Complex.exp (Real.pi * I * s / 2) *
            HurwitzZeta.expZeta (-x) s)
      _ ≤ Real.exp (Real.pi * |t| / 2) * unitThreeHalvesNormMass +
          Real.exp (Real.pi * |t| / 2) * unitThreeHalvesNormMass := by
        apply add_le_add
        · exact mul_le_mul hexpNeg hzetaPos (norm_nonneg _) hexpNonneg
        · exact mul_le_mul hexpPos hzetaNeg (norm_nonneg _) hexpNonneg
      _ = 2 * Real.exp (Real.pi * |t| / 2) *
          unitThreeHalvesNormMass := by ring
  have hGammaExp := norm_Gamma_threeHalves_sub_I_mul_mul_exp_le t
  have hpowNonneg :
      0 ≤ Real.rpow (2 * Real.pi) (-(3 / 2 : ℝ)) :=
    Real.rpow_nonneg h2pi.le _
  have hGammaNonneg : 0 ≤ ‖Complex.Gamma s‖ := norm_nonneg _
  rw [norm_mul, norm_mul, hpow]
  calc
    Real.rpow (2 * Real.pi) (-(3 / 2 : ℝ)) *
        ‖Complex.Gamma s‖ *
        ‖Complex.exp (-Real.pi * I * s / 2) *
            HurwitzZeta.expZeta x s +
          Complex.exp (Real.pi * I * s / 2) *
            HurwitzZeta.expZeta (-x) s‖ ≤
      Real.rpow (2 * Real.pi) (-(3 / 2 : ℝ)) *
        ‖Complex.Gamma s‖ *
        (2 * Real.exp (Real.pi * |t| / 2) *
          unitThreeHalvesNormMass) := by
      apply mul_le_mul_of_nonneg_left hbracket
      exact mul_nonneg hpowNonneg hGammaNonneg
    _ = (2 * Real.rpow (2 * Real.pi) (-(3 / 2 : ℝ)) *
          unitThreeHalvesNormMass) *
        (‖Complex.Gamma s‖ *
          Real.exp (Real.pi * |t| / 2)) := by ring
    _ ≤ (2 * Real.rpow (2 * Real.pi) (-(3 / 2 : ℝ)) *
          unitThreeHalvesNormMass) *
        (Real.sqrt (2 * Real.pi) * (1 + |t|)) := by
      apply mul_le_mul_of_nonneg_left
      · simpa [s] using hGammaExp
      · positivity
    _ = hurwitzNegativeHalfGrowthConstant * (1 + |t|) := by
      unfold hurwitzNegativeHalfGrowthConstant
      ring

/-- The promised unconditional scalar package.  It has no modulus loss and
only linear loss in the vertical parameter. -/
noncomputable def hurwitzNegativeHalfFixedLineGrowth :
    HurwitzFixedVerticalLineGrowth (-1 / 2 : ℝ) where
  C := hurwitzNegativeHalfGrowthConstant
  C_nonneg := hurwitzNegativeHalfGrowthConstant_nonneg
  qExponent := 0
  tDegree := 1
  bound q _ r t := by
    simpa using norm_hurwitzZeta_negative_half_add_I_mul_le q r t

/-- Consequently the complete finite-Hurwitz Estermann continuation has the
polynomial bound required by the right-line Abel integrability theorem. -/
noncomputable def estermannNegativeHalfPolynomialGrowth
    (a q : ℕ) [NeZero q] : EstermannNegativeHalfPolynomialGrowth a q :=
  toNegativeHalfEstermannGrowth hurwitzNegativeHalfFixedLineGrowth a q

/-- In particular, the complete normalized right edge of the raw Abel
rectangle is unconditionally Bochner integrable. -/
theorem integrable_normalizedAbel_rightVertical
    (x : ℝ) (hx : 0 < x) (a q : ℕ) [NeZero q] :
    MeasureTheory.Integrable (fun t : ℝ =>
      estermannWeightedIntegrand a q
        (bettinConreyNormalizedAbelReflectionWeight x)
        (estermannVerticalPoint (3 / 2 : ℝ) t)) :=
  (estermannNegativeHalfPolynomialGrowth a q).right_integrable hx

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelHurwitzGrowth
