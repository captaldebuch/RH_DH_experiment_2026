import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleRootAbsorption

/-!
# Route C: pointwise Gaussian limit in the central saddle window

Put `u = n + sqrt(n) * t`.  This module identifies the two normalized phase
coordinates appearing in the central Bettin--Conrey saddle integral:

* the entropy exponent tends to `-t^2/2`;
* the square-root displacement tends to `t/2`.

Both statements are proved from explicit `O_t(n⁻¹/²)` inequalities, not from
an asymptotic package.  Exact coordinate identities link the normalized
quantities back to the original `u` variable.  Combining the two limits gives
pointwise convergence of the normalized complex profile to its Gaussian
profile.  Uniform domination and passage under the integral remain separate
next steps.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleNearPointwise

open Filter
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleCentralWindow

noncomputable def routeCSaddleInvSqrtNat (n : ℕ) : ℝ :=
  (Real.sqrt (n : ℝ))⁻¹

theorem tendsto_routeCSaddleInvSqrtNat_zero :
    Tendsto routeCSaddleInvSqrtNat atTop (nhds 0) := by
  unfold routeCSaddleInvSqrtNat
  exact tendsto_inv_atTop_zero.comp
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

theorem tendsto_div_sqrt_nat_zero (t : ℝ) :
    Tendsto (fun n : ℕ => t / Real.sqrt (n : ℝ)) atTop (nhds 0) := by
  simpa only [div_eq_mul_inv, routeCSaddleInvSqrtNat, mul_zero] using
    tendsto_routeCSaddleInvSqrtNat_zero.const_mul t

theorem eventually_abs_div_sqrt_nat_lt_half (t : ℝ) :
    ∀ᶠ n : ℕ in atTop, |t / Real.sqrt (n : ℝ)| < 1 / 2 := by
  have h := (tendsto_div_sqrt_nat_zero t).abs
  exact (tendsto_order.1 h).2 (1 / 2) (by norm_num)

noncomputable def routeCSaddleScaledEntropy (t : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) *
    (Real.log (1 + t / Real.sqrt (n : ℝ)) -
      t / Real.sqrt (n : ℝ))

noncomputable def routeCSaddleScaledRootShift (t : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (n : ℝ) *
    (Real.sqrt (1 + t / Real.sqrt (n : ℝ)) - 1)

theorem routeCSaddleScaledEntropy_eq_saddle_coordinate
    (t : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    routeCSaddleScaledEntropy t n =
      (n : ℝ) * Real.log
        (((n : ℝ) + Real.sqrt (n : ℝ) * t) / (n : ℝ)) -
        Real.sqrt (n : ℝ) * t := by
  let s := Real.sqrt (n : ℝ)
  have hnR : 0 < (n : ℝ) := by positivity
  have hs : 0 < s := Real.sqrt_pos.2 hnR
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
  unfold routeCSaddleScaledEntropy
  change (n : ℝ) * (Real.log (1 + t / s) - t / s) =
    (n : ℝ) * Real.log (((n : ℝ) + s * t) / (n : ℝ)) - s * t
  have harg : ((n : ℝ) + s * t) / (n : ℝ) = 1 + t / s := by
    rw [← hs2]
    field_simp
  rw [harg]
  rw [← hs2]
  field_simp

theorem routeCSaddleScaledRootShift_eq_saddle_coordinate
    (t : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (ht : -Real.sqrt (n : ℝ) < t) :
    routeCSaddleScaledRootShift t n =
      Real.sqrt ((n : ℝ) + Real.sqrt (n : ℝ) * t) -
        Real.sqrt (n : ℝ) := by
  let s := Real.sqrt (n : ℝ)
  have hnR : 0 < (n : ℝ) := by positivity
  have hs : 0 < s := Real.sqrt_pos.2 hnR
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
  have hfactor : (n : ℝ) + s * t =
      (n : ℝ) * (1 + t / s) := by
    rw [← hs2]
    field_simp
  have harg : 0 ≤ 1 + t / s := by
    rw [show 1 + t / s = (s + t) / s by field_simp]
    exact (div_pos (by dsimp [s] at ht ⊢; linarith) hs).le
  unfold routeCSaddleScaledRootShift
  change s * (Real.sqrt (1 + t / s) - 1) =
    Real.sqrt ((n : ℝ) + s * t) - s
  rw [hfactor, Real.sqrt_mul hnR.le]
  ring

theorem abs_routeCSaddleScaledEntropy_add_half_sq_le
    (t : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hw : |t / Real.sqrt (n : ℝ)| < 1 / 2) :
    |routeCSaddleScaledEntropy t n + t ^ 2 / 2| ≤
      2 * |t| ^ 3 / Real.sqrt (n : ℝ) := by
  let s := Real.sqrt (n : ℝ)
  let w := t / s
  have hnR : 0 < (n : ℝ) := by positivity
  have hs : 0 < s := Real.sqrt_pos.2 hnR
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
  have hw' : |w| < 1 := by dsimp [w, s]; linarith
  have hlocal := abs_routeCSaddleEntropy_add_one_add_half_sq_le hw'
  have hrewrite : routeCSaddleScaledEntropy t n + t ^ 2 / 2 =
      (n : ℝ) * (routeCSaddleEntropy w + 1 + w ^ 2 / 2) := by
    unfold routeCSaddleScaledEntropy routeCSaddleEntropy
    dsimp [w, s]
    field_simp
    nlinarith
  rw [hrewrite, abs_mul, abs_of_pos hnR]
  have hfirst := mul_le_mul_of_nonneg_left hlocal hnR.le
  calc
    (n : ℝ) * |routeCSaddleEntropy w + 1 + w ^ 2 / 2| ≤
        (n : ℝ) * (|w| ^ 3 / (1 - |w|)) := hfirst
    _ ≤ (n : ℝ) * (|w| ^ 3 * 2) := by
      have hden : 1 / (1 - |w|) ≤ (2 : ℝ) := by
        rw [div_le_iff₀ (by linarith : 0 < 1 - |w|)]
        linarith
      rw [div_eq_mul_inv]
      gcongr
      simpa only [one_div] using hden
    _ = 2 * |t| ^ 3 / Real.sqrt (n : ℝ) := by
      change (n : ℝ) * (|t / s| ^ 3 * 2) = 2 * |t| ^ 3 / s
      rw [abs_div, abs_of_pos hs]
      field_simp
      rw [← hs2]
      ring

theorem routeCSaddleScaledEntropy_tendsto (t : ℝ) :
    Tendsto (routeCSaddleScaledEntropy t) atTop (nhds (-(t ^ 2) / 2)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hupper : Tendsto (fun n : ℕ =>
      2 * |t| ^ 3 / Real.sqrt (n : ℝ)) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, routeCSaddleInvSqrtNat, mul_zero] using
      tendsto_routeCSaddleInvSqrtNat_zero.const_mul (2 * |t| ^ 3)
  apply squeeze_zero' (g := fun n : ℕ =>
    2 * |t| ^ 3 / Real.sqrt (n : ℝ))
  · filter_upwards with n
    exact abs_nonneg _
  · filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩,
      eventually_abs_div_sqrt_nat_lt_half t] with n hn hw
    rw [Real.dist_eq]
    convert abs_routeCSaddleScaledEntropy_add_half_sq_le t n hn hw using 1
    ring
  · exact hupper

theorem abs_routeCSaddleScaledRootShift_sub_half_le
    (t : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hw : |t / Real.sqrt (n : ℝ)| < 1 / 2) :
    |routeCSaddleScaledRootShift t n - t / 2| ≤
      t ^ 2 / (2 * Real.sqrt (n : ℝ)) := by
  let s := Real.sqrt (n : ℝ)
  let w := t / s
  have hnR : 0 < (n : ℝ) := by positivity
  have hs : 0 < s := Real.sqrt_pos.2 hnR
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
  have hwneg : -1 < w := by
    have habs : |w| < 1 / 2 := by simpa [w, s] using hw
    linarith [neg_abs_le w]
  have hlocal := abs_sqrt_one_add_sub_one_sub_half_le hwneg
  have hrewrite : routeCSaddleScaledRootShift t n - t / 2 =
      s * (Real.sqrt (1 + w) - 1 - w / 2) := by
    unfold routeCSaddleScaledRootShift
    dsimp [w, s]
    field_simp
  rw [hrewrite, abs_mul, abs_of_pos hs]
  calc
    s * |Real.sqrt (1 + w) - 1 - w / 2| ≤ s * (w ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hlocal hs.le
    _ = t ^ 2 / (2 * Real.sqrt (n : ℝ)) := by
      change s * ((t / s) ^ 2 / 2) = t ^ 2 / (2 * s)
      field_simp

theorem routeCSaddleScaledRootShift_tendsto (t : ℝ) :
    Tendsto (routeCSaddleScaledRootShift t) atTop (nhds (t / 2)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hupper : Tendsto (fun n : ℕ =>
      t ^ 2 / (2 * Real.sqrt (n : ℝ))) atTop (nhds 0) := by
    have h := tendsto_routeCSaddleInvSqrtNat_zero.const_mul (t ^ 2 / 2)
    simpa [routeCSaddleInvSqrtNat, div_eq_mul_inv, mul_inv_rev,
      mul_assoc, mul_comm] using h
  apply squeeze_zero' (g := fun n : ℕ =>
    t ^ 2 / (2 * Real.sqrt (n : ℝ)))
  · filter_upwards with n
    exact abs_nonneg _
  · filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩,
      eventually_abs_div_sqrt_nat_lt_half t] with n hn hw
    rw [Real.dist_eq]
    exact abs_routeCSaddleScaledRootShift_sub_half_le t n hn hw
  · exact hupper

noncomputable def routeCSaddleNearPhase
    (A : ℂ) (t : ℝ) (n : ℕ) : ℂ :=
  (routeCSaddleScaledEntropy t n : ℂ) -
    A * (routeCSaddleScaledRootShift t n : ℂ)

noncomputable def routeCSaddleGaussianPhase (A : ℂ) (t : ℝ) : ℂ :=
  ((-(t ^ 2) / 2 : ℝ) : ℂ) - A * ((t / 2 : ℝ) : ℂ)

theorem routeCSaddleNearPhase_tendsto (A : ℂ) (t : ℝ) :
    Tendsto (routeCSaddleNearPhase A t) atTop
      (nhds (routeCSaddleGaussianPhase A t)) := by
  unfold routeCSaddleNearPhase routeCSaddleGaussianPhase
  exact ((Complex.continuous_ofReal.tendsto _).comp
    (routeCSaddleScaledEntropy_tendsto t)).sub
      (tendsto_const_nhds.mul
        ((Complex.continuous_ofReal.tendsto _).comp
          (routeCSaddleScaledRootShift_tendsto t)))

noncomputable def routeCSaddleNearNormalizedProfile
    (A : ℂ) (t : ℝ) (n : ℕ) : ℂ :=
  ((1 / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) *
    Complex.exp (-(A ^ 2) / 8) * Complex.exp (routeCSaddleNearPhase A t n)

noncomputable def routeCSaddleGaussianProfile (A : ℂ) (t : ℝ) : ℂ :=
  ((1 / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) *
    Complex.exp (-(A ^ 2) / 8) * Complex.exp (routeCSaddleGaussianPhase A t)

theorem routeCSaddleNearNormalizedProfile_tendsto
    (A : ℂ) (t : ℝ) :
    Tendsto (routeCSaddleNearNormalizedProfile A t) atTop
      (nhds (routeCSaddleGaussianProfile A t)) := by
  unfold routeCSaddleNearNormalizedProfile routeCSaddleGaussianProfile
  exact (tendsto_const_nhds.mul tendsto_const_nhds).mul
    (Complex.continuous_exp.continuousAt.tendsto.comp
      (routeCSaddleNearPhase_tendsto A t))

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleNearPointwise
