import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleFarGamma
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Route C: explicit optimization of the far-saddle Gamma bound

The general far-sector estimate contains `Gamma ((1-theta)*n + alpha)`.
For the central Bettin--Conrey row `alpha = 1`, choose `theta = 1/2`.
Then the Gamma argument is `n/2 + 1`.  Legendre duplication and monotonicity
of Gamma on `[2, infinity)` compress its square to an ordinary factorial.
Consequently Mathlib's existing factorial Stirling theorem is sufficient; no
new affine-real-argument Gamma asymptotic is needed.

The tunable Young parameter is chosen as `epsilon = c_delta/8`, where
`c_delta` is the positive far-window entropy gap.  This choice is admissible
and leaves the strict exponential contraction

`exp (-c_delta) < 2 * (1/2 - epsilon)`.

The final theorems bound the genuine far integral, and its square, by this
specialized Gamma/factorial majorant.  The next step is the remaining
factorial-Stirling limit after division by the principal saddle scale.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleFarOptimization

open MeasureTheory Set
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleCentralWindow
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleFarEntropy
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleWeightedFar
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleFarGamma

theorem routeCSaddleRetainedShape_half (n : ℕ) :
    routeCSaddleRetainedShape 1 (1 / 2) n = (n : ℝ) / 2 + 1 := by
  unfold routeCSaddleRetainedShape
  ring

theorem routeCSaddleRetainedRate_half (epsilon : ℝ) :
    routeCSaddleRetainedRate (1 / 2) epsilon = 1 / 2 - epsilon := by
  unfold routeCSaddleRetainedRate
  ring

/-- The Young parameter retaining enough of the entropy gap after the
`theta = 1/2` split. -/
noncomputable def routeCSaddleHalfEntropyEpsilon (delta : ℝ) : ℝ :=
  routeCSaddleEntropyGap delta / 8

theorem routeCSaddleEntropyGap_lt_one
    {delta : ℝ} (hd0 : 0 < delta) (hd1 : delta < 1) :
    routeCSaddleEntropyGap delta < 1 := by
  have hmin : routeCSaddleEntropyGap delta ≤
      -(routeCSaddleRate (1 + delta)) := min_le_right _ _
  have hlog : 0 ≤ Real.log (1 + delta) :=
    Real.log_nonneg (by linarith)
  rw [routeCSaddleRate] at hmin
  linarith

theorem routeCSaddleHalfEntropyEpsilon_pos
    {delta : ℝ} (hd0 : 0 < delta) (hd1 : delta < 1) :
    0 < routeCSaddleHalfEntropyEpsilon delta := by
  unfold routeCSaddleHalfEntropyEpsilon
  exact div_pos (routeCSaddleEntropyGap_pos hd0 hd1) (by norm_num)

theorem routeCSaddleHalfEntropyEpsilon_lt_half
    {delta : ℝ} (hd0 : 0 < delta) (hd1 : delta < 1) :
    routeCSaddleHalfEntropyEpsilon delta < 1 / 2 := by
  unfold routeCSaddleHalfEntropyEpsilon
  have hc := routeCSaddleEntropyGap_lt_one hd0 hd1
  linarith

/-- The optimized retained rate still beats the entropy factor.  After
squaring the saddle estimate, this is precisely the geometric base that has
to be strictly below one. -/
theorem exp_neg_entropyGap_lt_double_retainedRate
    {delta : ℝ} (hd0 : 0 < delta) (hd1 : delta < 1) :
    Real.exp (-routeCSaddleEntropyGap delta) <
      2 * (1 / 2 - routeCSaddleHalfEntropyEpsilon delta) := by
  let c := routeCSaddleEntropyGap delta
  have hc0 : 0 < c := routeCSaddleEntropyGap_pos hd0 hd1
  have hc1 : c < 1 := routeCSaddleEntropyGap_lt_one hd0 hd1
  have hexp : 1 + c < Real.exp c := by
    simpa [add_comm] using Real.add_one_lt_exp hc0.ne'
  have hinv : (Real.exp c)⁻¹ < (1 + c)⁻¹ :=
    (inv_lt_inv₀ (by positivity) (by positivity)).2 hexp
  have halg : (1 + c)⁻¹ < 1 - c / 4 := by
    rw [inv_lt_iff_one_lt_mul₀ (by positivity)]
    nlinarith [mul_pos hc0
      (sub_pos.mpr (hc1.trans (by norm_num : (1 : ℝ) < 3)))]
  rw [Real.exp_neg]
  calc
    (Real.exp c)⁻¹ < (1 + c)⁻¹ := hinv
    _ < 1 - c / 4 := halg
    _ = 2 * (1 / 2 - routeCSaddleHalfEntropyEpsilon delta) := by
      unfold routeCSaddleHalfEntropyEpsilon c
      ring

/-- Duplication compresses the affine Gamma value to the factorial sequence.
This is sharp enough at exponential scale and avoids a separate real-Gamma
Stirling development. -/
theorem gamma_half_square_le_duplication (n : ℕ) (hn : 2 ≤ n) :
    Real.Gamma ((n : ℝ) / 2 + 1) ^ 2 ≤
      ((n + 1).factorial : ℝ) *
        Real.rpow 2 (-((n : ℝ) + 1)) * Real.sqrt Real.pi := by
  let q : ℝ := (n : ℝ) / 2 + 1
  have hq2 : 2 ≤ q := by
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    dsimp [q]
    linarith
  have hqmem : q ∈ Ici (2 : ℝ) := hq2
  have hqhalfmem : q + 1 / 2 ∈ Ici (2 : ℝ) :=
    hq2.trans (by linarith)
  have hmono : Real.Gamma q ≤ Real.Gamma (q + 1 / 2) :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn hqmem hqhalfmem (by linarith)
  have hqpos : 0 ≤ Real.Gamma q :=
    (Real.Gamma_pos_of_pos (lt_of_lt_of_le (by norm_num) hq2)).le
  calc
    Real.Gamma ((n : ℝ) / 2 + 1) ^ 2 = Real.Gamma q * Real.Gamma q := by
      rw [pow_two]
    _ ≤ Real.Gamma q * Real.Gamma (q + 1 / 2) :=
      mul_le_mul_of_nonneg_left hmono hqpos
    _ = Real.Gamma (2 * q) * Real.rpow 2 (1 - 2 * q) * Real.sqrt Real.pi :=
      Real.Gamma_mul_Gamma_add_half q
    _ = ((n + 1).factorial : ℝ) *
        Real.rpow 2 (-((n : ℝ) + 1)) * Real.sqrt Real.pi := by
      have harg : 2 * q = ((n + 1 : ℕ) : ℝ) + 1 := by
        dsimp [q]
        push_cast
        ring
      have hexp : 1 - (((n + 1 : ℕ) : ℝ) + 1) =
          -((n : ℝ) + 1) := by
        push_cast
        ring
      rw [harg, Real.Gamma_nat_eq_factorial, hexp]

/-- All non-Gamma factors in the specialized far majorant. -/
noncomputable def routeCSaddleHalfGammaPrefactor
    (A : ℂ) (delta epsilon : ℝ) (n : ℕ) : ℝ :=
  (Real.rpow n (n : ℝ) * Real.exp (-(n : ℝ))) *
    Real.exp (-((1 / 2 : ℝ) * (n : ℝ) * routeCSaddleEntropyGap delta)) *
      Real.exp (‖A‖ ^ 2 / (4 * epsilon)) *
        (Real.exp ((1 / 2 : ℝ) * (n : ℝ)) *
          Real.rpow n (-((n : ℝ) / 2)) *
            Real.rpow (1 / (1 / 2 - epsilon)) ((n : ℝ) / 2 + 1))

/-- The `theta = 1/2`, `alpha = 1` Gamma majorant. -/
noncomputable def routeCSaddleHalfGammaMajorant
    (A : ℂ) (delta epsilon : ℝ) (n : ℕ) : ℝ :=
  routeCSaddleHalfGammaPrefactor A delta epsilon n *
    Real.Gamma ((n : ℝ) / 2 + 1)

theorem routeCSaddleHalfGammaPrefactor_nonneg
    (A : ℂ) (delta epsilon : ℝ) (n : ℕ)
    (hepsilon : epsilon < 1 / 2) :
    0 ≤ routeCSaddleHalfGammaPrefactor A delta epsilon n := by
  unfold routeCSaddleHalfGammaPrefactor
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
          (Real.exp_nonneg _))
        (Real.exp_nonneg _))
      (Real.exp_nonneg _))
    (mul_nonneg
      (mul_nonneg (Real.exp_nonneg _)
        (Real.rpow_nonneg (Nat.cast_nonneg n) _))
      (Real.rpow_nonneg (by positivity) _))

theorem routeCSaddleHalfGammaMajorant_nonneg
    (A : ℂ) (delta epsilon : ℝ) (n : ℕ)
    (hepsilon : epsilon < 1 / 2) :
    0 ≤ routeCSaddleHalfGammaMajorant A delta epsilon n := by
  unfold routeCSaddleHalfGammaMajorant
  exact mul_nonneg
    (routeCSaddleHalfGammaPrefactor_nonneg A delta epsilon n hepsilon)
    (Real.Gamma_pos_of_pos (by positivity)).le

theorem routeCSaddleHalfGammaMajorant_sq_le_factorial
    (A : ℂ) (delta epsilon : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    routeCSaddleHalfGammaMajorant A delta epsilon n ^ 2 ≤
      routeCSaddleHalfGammaPrefactor A delta epsilon n ^ 2 *
        (((n + 1).factorial : ℝ) *
          Real.rpow 2 (-((n : ℝ) + 1)) * Real.sqrt Real.pi) := by
  rw [routeCSaddleHalfGammaMajorant, mul_pow]
  exact mul_le_mul_of_nonneg_left (gamma_half_square_le_duplication n hn)
    (sq_nonneg _)

/-- Specialized closed Gamma bound for the genuine far-sector integral. -/
theorem norm_routeCSaddleFarIntegral_one_le_halfGamma
    (A : ℂ) (delta epsilon : ℝ) (n : ℕ)
    (hn : 2 ≤ n) (hd0 : 0 < delta) (hd1 : delta < 1)
    (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2) :
    ‖routeCSaddleFarIntegral A 1 delta n‖ ≤
      routeCSaddleHalfGammaMajorant A delta epsilon n := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hq : 0 < routeCSaddleRetainedShape 1 (1 / 2) n := by
    rw [routeCSaddleRetainedShape_half]
    positivity
  have hb : 0 < routeCSaddleRetainedRate (1 / 2) epsilon := by
    rw [routeCSaddleRetainedRate_half]
    linarith
  have h := norm_routeCSaddleFarIntegral_le_gamma
    A 1 (1 / 2) delta epsilon n hn0 hd0 hd1 (by norm_num) he0 hq hb
  rw [routeCSaddleHalfGammaMajorant, routeCSaddleHalfGammaPrefactor]
  convert h using 1
  all_goals
    simp only [routeCSaddleRetainedShape_half, routeCSaddleRetainedRate_half]
    ring_nf

/-- Factorial-only squared bound for the genuine far-sector integral. -/
theorem norm_routeCSaddleFarIntegral_one_sq_le_factorial
    (A : ℂ) (delta epsilon : ℝ) (n : ℕ)
    (hn : 2 ≤ n) (hd0 : 0 < delta) (hd1 : delta < 1)
    (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2) :
    ‖routeCSaddleFarIntegral A 1 delta n‖ ^ 2 ≤
      routeCSaddleHalfGammaPrefactor A delta epsilon n ^ 2 *
        (((n + 1).factorial : ℝ) *
          Real.rpow 2 (-((n : ℝ) + 1)) * Real.sqrt Real.pi) := by
  have hnorm := norm_routeCSaddleFarIntegral_one_le_halfGamma
    A delta epsilon n hn hd0 hd1 he0 he1
  have hsq : ‖routeCSaddleFarIntegral A 1 delta n‖ ^ 2 ≤
      routeCSaddleHalfGammaMajorant A delta epsilon n ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (routeCSaddleHalfGammaMajorant_nonneg A delta epsilon n he1)).2 hnorm
  exact hsq.trans
    (routeCSaddleHalfGammaMajorant_sq_le_factorial A delta epsilon n hn)

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleFarOptimization
