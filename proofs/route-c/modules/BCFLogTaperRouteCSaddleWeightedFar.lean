import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleFarEntropy

/-!
# Route C: weighted far-sector factorization

The entropy gap cannot be spent in full before integration: doing so discards
the residual Gamma profile that controls `u -> 0` and `u -> infinity`.  This
file proves the exact weighted factorization and introduces a parameter
`theta >= 0`.  A fraction `theta` of the entropy supplies the far-sector
factor

`exp (-theta * n * c_delta)`,

while the remaining fraction `1-theta` stays inside the integrable saddle
profile.  A second parameter `epsilon > 0` gives the tunable Young estimate

`||A|| * sqrt u <= epsilon*u + ||A||^2/(4*epsilon)`.

No integration estimate or asymptotic assertion is made here.  The next step
is to integrate the retained profile and optimize `theta` and `epsilon`.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleWeightedFar

open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleCentralWindow
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleIntegrability
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleFarEntropy

/-- Exact extraction of the natural saddle scale. -/
theorem routeCSaddleBase_factorization
    {u : ℝ} {n : ℕ} (alpha : ℝ) (hu : 0 < u) (hn : 0 < n) :
    Real.rpow u ((n : ℝ) + alpha - 1) * Real.exp (-u) =
      (Real.rpow n ((n : ℝ) + alpha - 1) * Real.exp (-(n : ℝ))) *
        Real.rpow (u / (n : ℝ)) (alpha - 1) *
          Real.exp ((n : ℝ) * routeCSaddleRate (u / (n : ℝ))) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hv : 0 < u / (n : ℝ) := div_pos hu hnR
  have huv : u = (n : ℝ) * (u / (n : ℝ)) := by field_simp
  have hlog :
      Real.log u = Real.log (n : ℝ) + Real.log (u / (n : ℝ)) := by
    calc
      Real.log u = Real.log ((n : ℝ) * (u / (n : ℝ))) :=
        congrArg Real.log huv
      _ = Real.log (n : ℝ) + Real.log (u / (n : ℝ)) :=
        Real.log_mul (ne_of_gt hnR) (ne_of_gt hv)
  rw [show Real.rpow u ((n : ℝ) + alpha - 1) =
      Real.exp (Real.log u * ((n : ℝ) + alpha - 1)) from
        Real.rpow_def_of_pos hu _,
    show Real.rpow (n : ℝ) ((n : ℝ) + alpha - 1) =
      Real.exp (Real.log (n : ℝ) * ((n : ℝ) + alpha - 1)) from
        Real.rpow_def_of_pos hnR _,
    show Real.rpow (u / (n : ℝ)) (alpha - 1) =
      Real.exp (Real.log (u / (n : ℝ)) * (alpha - 1)) from
        Real.rpow_def_of_pos hv _]
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [routeCSaddleRate, hlog]
  field_simp [ne_of_gt hnR]
  ring

theorem norm_routeCSaddleIntegrand_le_rescaled
    (A : ℂ) (alpha : ℝ) {u : ℝ} {n : ℕ}
    (hu : 0 < u) (hn : 0 < n) :
    ‖routeCSaddleIntegrand A alpha n u‖ ≤
      ((Real.rpow n ((n : ℝ) + alpha - 1) * Real.exp (-(n : ℝ))) *
        Real.rpow (u / (n : ℝ)) (alpha - 1) *
          Real.exp ((n : ℝ) * routeCSaddleRate (u / (n : ℝ)))) *
            Real.exp (‖A‖ * Real.sqrt u) := by
  have hbase_nonneg :
      0 ≤ Real.rpow u ((n : ℝ) + alpha - 1) * Real.exp (-u) :=
    mul_nonneg (Real.rpow_nonneg hu.le _) (Real.exp_nonneg _)
  rw [routeCSaddleIntegrand, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hbase_nonneg]
  calc
    (Real.rpow u ((n : ℝ) + alpha - 1) * Real.exp (-u)) *
        ‖Complex.exp (-A * (Real.sqrt u : ℂ))‖
      ≤ (Real.rpow u ((n : ℝ) + alpha - 1) * Real.exp (-u)) *
          Real.exp (‖A‖ * Real.sqrt u) :=
        mul_le_mul_of_nonneg_left
          (norm_exp_neg_mul_sqrt_le A u) hbase_nonneg
    _ = _ := by rw [routeCSaddleBase_factorization alpha hu hn]

/-- Tunable Young inequality for the complex square-root perturbation. -/
theorem norm_mul_sqrt_le_epsilon_add_sq_div
    (A : ℂ) {epsilon u : ℝ} (hepsilon : 0 < epsilon) (hu : 0 ≤ u) :
    ‖A‖ * Real.sqrt u ≤
      epsilon * u + ‖A‖ ^ 2 / (4 * epsilon) := by
  have hsqrt_sq : (Real.sqrt u) ^ 2 = u := Real.sq_sqrt hu
  have hden : 0 < 4 * epsilon := by positivity
  rw [show epsilon * u + ‖A‖ ^ 2 / (4 * epsilon) =
      (4 * epsilon ^ 2 * u + ‖A‖ ^ 2) / (4 * epsilon) by
    field_simp]
  rw [le_div_iff₀ hden]
  nlinarith [sq_nonneg (2 * epsilon * Real.sqrt u - ‖A‖)]

/-- Spend only a fraction `theta` of the entropy gap, retaining the remaining
rate inside the weighted profile. -/
theorem norm_routeCSaddleIntegrand_far_le_split
    (A : ℂ) (alpha theta delta : ℝ) {u : ℝ} {n : ℕ}
    (hu : u ∈ routeCSaddleFarSet delta n) (hn : 0 < n)
    (hd0 : 0 < delta) (hd1 : delta < 1) (htheta : 0 ≤ theta) :
    ‖routeCSaddleIntegrand A alpha n u‖ ≤
      (Real.rpow n ((n : ℝ) + alpha - 1) * Real.exp (-(n : ℝ))) *
        Real.rpow (u / (n : ℝ)) (alpha - 1) *
          Real.exp (-(theta * (n : ℝ) * routeCSaddleEntropyGap delta)) *
            Real.exp (((1 - theta) * (n : ℝ)) *
              routeCSaddleRate (u / (n : ℝ)) + ‖A‖ * Real.sqrt u) := by
  have hraw := norm_routeCSaddleIntegrand_le_rescaled A alpha hu.1 hn
  have hrate := routeCSaddleFar_rate_le_neg_entropyGap hn hd0 hd1 hu
  have hthetaN : 0 ≤ theta * (n : ℝ) :=
    mul_nonneg htheta (Nat.cast_nonneg n)
  have hexp :
      Real.exp ((theta * (n : ℝ)) *
          routeCSaddleRate (u / (n : ℝ))) ≤
        Real.exp (-(theta * (n : ℝ) *
          routeCSaddleEntropyGap delta)) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hrate hthetaN
    nlinarith
  have hcoeff : 0 ≤
      (Real.rpow n ((n : ℝ) + alpha - 1) * Real.exp (-(n : ℝ))) *
        Real.rpow (u / (n : ℝ)) (alpha - 1) :=
    mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        (Real.exp_nonneg _))
      (Real.rpow_nonneg
        (div_nonneg hu.1.le (Nat.cast_nonneg n)) _)
  calc
    ‖routeCSaddleIntegrand A alpha n u‖ ≤
        ((Real.rpow n ((n : ℝ) + alpha - 1) * Real.exp (-(n : ℝ))) *
          Real.rpow (u / (n : ℝ)) (alpha - 1) *
            Real.exp ((n : ℝ) * routeCSaddleRate (u / (n : ℝ)))) *
              Real.exp (‖A‖ * Real.sqrt u) := hraw
    _ = ((Real.rpow n ((n : ℝ) + alpha - 1) * Real.exp (-(n : ℝ))) *
          Real.rpow (u / (n : ℝ)) (alpha - 1)) *
        (Real.exp ((theta * (n : ℝ)) *
            routeCSaddleRate (u / (n : ℝ))) *
          Real.exp (((1 - theta) * (n : ℝ)) *
            routeCSaddleRate (u / (n : ℝ)) + ‖A‖ * Real.sqrt u)) := by
      rw [mul_assoc, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ ((Real.rpow n ((n : ℝ) + alpha - 1) * Real.exp (-(n : ℝ))) *
          Real.rpow (u / (n : ℝ)) (alpha - 1)) *
        (Real.exp (-(theta * (n : ℝ) *
            routeCSaddleEntropyGap delta)) *
          Real.exp (((1 - theta) * (n : ℝ)) *
            routeCSaddleRate (u / (n : ℝ)) + ‖A‖ * Real.sqrt u)) := by
      gcongr
    _ = _ := by ring

/-- The split after applying the tunable Young inequality.  This is the form
that can be converted into an explicit Gamma integral. -/
theorem norm_routeCSaddleIntegrand_far_le_split_young
    (A : ℂ) (alpha theta delta epsilon : ℝ) {u : ℝ} {n : ℕ}
    (hu : u ∈ routeCSaddleFarSet delta n) (hn : 0 < n)
    (hd0 : 0 < delta) (hd1 : delta < 1) (htheta : 0 ≤ theta)
    (hepsilon : 0 < epsilon) :
    ‖routeCSaddleIntegrand A alpha n u‖ ≤
      (Real.rpow n ((n : ℝ) + alpha - 1) * Real.exp (-(n : ℝ))) *
        Real.rpow (u / (n : ℝ)) (alpha - 1) *
          Real.exp (-(theta * (n : ℝ) * routeCSaddleEntropyGap delta)) *
            Real.exp (((1 - theta) * (n : ℝ)) *
              routeCSaddleRate (u / (n : ℝ)) +
                epsilon * u + ‖A‖ ^ 2 / (4 * epsilon)) := by
  calc
    ‖routeCSaddleIntegrand A alpha n u‖ ≤
        (Real.rpow n ((n : ℝ) + alpha - 1) * Real.exp (-(n : ℝ))) *
          Real.rpow (u / (n : ℝ)) (alpha - 1) *
            Real.exp (-(theta * (n : ℝ) *
              routeCSaddleEntropyGap delta)) *
              Real.exp (((1 - theta) * (n : ℝ)) *
                routeCSaddleRate (u / (n : ℝ)) + ‖A‖ * Real.sqrt u) :=
      norm_routeCSaddleIntegrand_far_le_split
        A alpha theta delta hu hn hd0 hd1 htheta
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left
      · apply Real.exp_le_exp.mpr
        nlinarith [norm_mul_sqrt_le_epsilon_add_sq_div
          A hepsilon hu.1.le]
      · exact mul_nonneg
          (mul_nonneg
            (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
              (Real.exp_nonneg _))
            (Real.rpow_nonneg
              (div_nonneg hu.1.le (Nat.cast_nonneg n)) _))
          (Real.exp_nonneg _)

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleWeightedFar
