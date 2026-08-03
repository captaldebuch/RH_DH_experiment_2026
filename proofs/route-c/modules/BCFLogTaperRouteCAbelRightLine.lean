import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCAbelContourLimit
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannVerticalBounds

/-!
# Route C: intrinsic decay on the right Abel line

On the right side `Re(s) = 3/2`, the reflected Abel weight contains
`Gamma (-1/2-it)`.  Its intrinsic exponential decay makes the complete
Estermann row integrable as soon as the continuation on `Re(u) = -1/2` has
polynomial growth.  This module proves that implication and isolates the
remaining scalar Hurwitz-growth theorem.

No horizontal-edge estimate and no Abel boundary value is asserted here.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelRightLine

open Complex Filter MeasureTheory Set Topology
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannBoundaryAnalysis
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannContourShift
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannHurwitz
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVerticalBounds
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelMellin
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelReflectionWeight
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCGammaHalfLines

/-- A polynomial times a two-sided exponential. -/
noncomputable def abelPolynomialExponentialMajorant
    (degree : ℕ) (rate : ℝ) (t : ℝ) : ℝ :=
  (1 + |t|) ^ degree * Real.exp (-rate * |t|)

/-- Every polynomial is integrable against a positive two-sided exponential.
This is the reusable scalar fact needed after multiplying vertical growth by
the intrinsic Gamma decay. -/
theorem integrable_abelPolynomialExponentialMajorant
    (degree : ℕ) {rate : ℝ} (hrate : 0 < rate) :
    Integrable (abelPolynomialExponentialMajorant degree rate) := by
  have hmono : ∀ k : ℕ, IntegrableOn
      (fun x : ℝ => x ^ k * Real.exp (-rate * x)) (Ioi 0) := by
    intro k
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (k : ℝ)) (b := rate)
      (by have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k; linarith)
      (by norm_num) hrate
    convert h using 1
    ext x
    simp only [Real.rpow_natCast, Real.rpow_one]
  have hpos : IntegrableOn
      (fun x : ℝ => (1 + x) ^ degree * Real.exp (-rate * x))
      (Ioi 0) := by
    rw [show (fun x : ℝ => (1 + x) ^ degree * Real.exp (-rate * x)) =
        fun x : ℝ =>
          ∑ k ∈ Finset.range (degree + 1),
            ((Nat.choose degree k : ℕ) : ℝ) *
              (x ^ (degree - k) * Real.exp (-rate * x)) by
      funext x
      rw [add_pow]
      simp only [one_pow, one_mul]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring]
    exact integrable_finsetSum (μ := volume.restrict (Ioi 0)) _ fun k _ =>
      (hmono (degree - k)).const_mul _
  have hposAbs : IntegrableOn
      (abelPolynomialExponentialMajorant degree rate) (Ioi 0) := by
    refine hpos.congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hx' : 0 < x := hx
    simp only [abelPolynomialExponentialMajorant, abs_of_pos hx']
  have hnegAbs : IntegrableOn
      (abelPolynomialExponentialMajorant degree rate) (Iio 0) := by
    rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
    simpa only [Function.comp_def, abelPolynomialExponentialMajorant,
      abs_neg, neg_preimage, neg_Iio, neg_zero] using hposAbs
  rw [← integrableOn_univ, ← Iio_union_Ici, integrableOn_union]
  refine ⟨hnegAbs, ?_⟩
  rwa [integrableOn_Ici_iff_integrableOn_Ioi]

/-- A convenient explicit majorant for Gamma on `Re(s) = -1/2`. -/
noncomputable def gammaNegativeHalfMajorant (t : ℝ) : ℝ :=
  Real.sqrt (8 * Real.pi) * Real.exp (-(Real.pi / 2) * |t|)

theorem gammaNegativeHalfMajorant_nonneg (t : ℝ) :
    0 ≤ gammaNegativeHalfMajorant t := by
  unfold gammaNegativeHalfMajorant
  positivity

/-- Intrinsic exponential decay of Gamma on the right reflected line. -/
theorem norm_Gamma_neg_half_add_I_mul_le_majorant (t : ℝ) :
    ‖Complex.Gamma (-(1 / 2 : ℝ) + Complex.I * t)‖ ≤
      gammaNegativeHalfMajorant t := by
  have hcosh : 0 < Real.cosh (Real.pi * t) := Real.cosh_pos _
  have hexp : 0 < Real.exp (Real.pi * |t|) := Real.exp_pos _
  have habs : |Real.pi * t| = Real.pi * |t| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
  have hcoshLower : Real.exp (Real.pi * |t|) ≤
      2 * Real.cosh (Real.pi * t) := by
    rw [← habs]
    exact exp_abs_le_two_mul_cosh (Real.pi * t)
  have hinv : 1 / Real.cosh (Real.pi * t) ≤
      2 * Real.exp (-(Real.pi * |t|)) := by
    rw [Real.exp_neg]
    apply (div_le_iff₀ hcosh).2
    calc
      1 = (Real.exp (Real.pi * |t|))⁻¹ *
          Real.exp (Real.pi * |t|) := by
            rw [inv_mul_cancel₀ hexp.ne']
      _ ≤ (Real.exp (Real.pi * |t|))⁻¹ *
          (2 * Real.cosh (Real.pi * t)) :=
            mul_le_mul_of_nonneg_left hcoshLower (inv_nonneg.mpr hexp.le)
      _ = 2 * (Real.exp (Real.pi * |t|))⁻¹ *
          Real.cosh (Real.pi * t) := by ring
  have hquad : (1 / 4 : ℝ) ≤ (1 / 2 : ℝ) ^ 2 + t ^ 2 := by nlinarith [sq_nonneg t]
  have hden : 0 < (1 / 2 : ℝ) ^ 2 + t ^ 2 := by positivity
  have hsquare :
      ‖Complex.Gamma (-(1 / 2 : ℝ) + Complex.I * t)‖ ^ 2 ≤
        gammaNegativeHalfMajorant t ^ 2 := by
    rw [norm_Gamma_neg_half_add_I_mul_sq]
    unfold gammaNegativeHalfMajorant
    have hsqrt : Real.sqrt (8 * Real.pi) ^ 2 = 8 * Real.pi := by
      rw [Real.sq_sqrt]
      positivity
    rw [mul_pow, hsqrt]
    rw [show Real.exp (-(Real.pi / 2) * |t|) ^ 2 =
        Real.exp (-(Real.pi * |t|)) by
      rw [← Real.exp_nat_mul]
      congr 1
      ring]
    have hratio :
        Real.pi /
            (Real.cosh (Real.pi * t) * ((1 / 2 : ℝ) ^ 2 + t ^ 2)) ≤
          8 * Real.pi * Real.exp (-(Real.pi * |t|)) := by
      calc
        Real.pi /
              (Real.cosh (Real.pi * t) * ((1 / 2 : ℝ) ^ 2 + t ^ 2)) =
            (Real.pi / Real.cosh (Real.pi * t)) /
              ((1 / 2 : ℝ) ^ 2 + t ^ 2) := by field_simp
        _ ≤ (Real.pi * (2 * Real.exp (-(Real.pi * |t|)))) /
              ((1 / 2 : ℝ) ^ 2 + t ^ 2) := by
            apply div_le_div_of_nonneg_right _ hden.le
            have hmul := mul_le_mul_of_nonneg_left hinv Real.pi_pos.le
            simpa [div_eq_mul_inv] using hmul
        _ ≤ (Real.pi * (2 * Real.exp (-(Real.pi * |t|)))) /
              (1 / 4 : ℝ) := by
            exact div_le_div_of_nonneg_left (by positivity) (by norm_num) hquad
        _ = 8 * Real.pi * Real.exp (-(Real.pi * |t|)) := by ring
    exact hratio
  nlinarith [norm_nonneg
    (Complex.Gamma (-(1 / 2 : ℝ) + Complex.I * t)),
    gammaNegativeHalfMajorant_nonneg t]

/-- The exact classical scalar input required on the reflected Estermann
line.  It is weaker than a full strip theorem and is therefore the right
interface for proving right-line integrability first. -/
structure EstermannNegativeHalfPolynomialGrowth
    (a q : ℕ) [NeZero q] where
  C : ℝ
  C_nonneg : 0 ≤ C
  degree : ℕ
  bound : ∀ t : ℝ,
    ‖estermannHurwitzContinuation a q
        (estermannVerticalPoint (-1 / 2 : ℝ) t)‖ ≤
      C * (1 + |t|) ^ degree

/-- The explicit fixed-line constant obtained from the finite Hurwitz
majorant. -/
noncomputable def negativeHalfEstermannConstant
    (H : HurwitzFixedVerticalLineGrowth (-1 / 2 : ℝ)) (q : ℕ) : ℝ :=
  Real.rpow (q : ℝ) (1 / 2 : ℝ) ^ 2 *
    ((q : ℝ) * (H.C * (q : ℝ) ^ H.qExponent)) ^ 2

theorem negativeHalfEstermannConstant_nonneg
    (H : HurwitzFixedVerticalLineGrowth (-1 / 2 : ℝ)) (q : ℕ) :
    0 ≤ negativeHalfEstermannConstant H q := by
  unfold negativeHalfEstermannConstant
  positivity

/-- A scalar Hurwitz bound on `Re(s)=-1/2` supplies the exact polynomial
Estermann input needed by the right Abel line. -/
noncomputable def HurwitzFixedVerticalLineGrowth.toNegativeHalfEstermannGrowth
    (H : HurwitzFixedVerticalLineGrowth (-1 / 2 : ℝ))
    (a q : ℕ) [NeZero q] :
    EstermannNegativeHalfPolynomialGrowth a q where
  C := negativeHalfEstermannConstant H q
  C_nonneg := negativeHalfEstermannConstant_nonneg H q
  degree := 2 * H.tDegree
  bound := by
    intro t
    calc
      ‖estermannHurwitzContinuation a q
          (estermannVerticalPoint (-1 / 2 : ℝ) t)‖ ≤
          Real.rpow (q : ℝ) (-(-1 / 2 : ℝ)) ^ 2 *
            ((q : ℝ) * H.pointMajorant q t) ^ 2 :=
        H.estermann_norm_le a q t
      _ = negativeHalfEstermannConstant H q *
          (1 + |t|) ^ (2 * H.tDegree) := by
        unfold HurwitzFixedVerticalLineGrowth.pointMajorant
          negativeHalfEstermannConstant
        rw [show -(-1 / 2 : ℝ) = (1 / 2 : ℝ) by ring]
        rw [show 2 * H.tDegree = H.tDegree * 2 by omega, pow_mul]
        ring

/-- The complete reflected right-line integrand is continuous.  The line
meets neither a Gamma pole nor the Hurwitz pole. -/
theorem continuous_normalizedAbel_rightVerticalIntegrand
    (x : ℝ) (hx : 0 < x) (a q : ℕ) [NeZero q] :
    Continuous (fun t : ℝ =>
      estermannWeightedIntegrand a q
        (bettinConreyNormalizedAbelReflectionWeight x)
        (estermannVerticalPoint (3 / 2 : ℝ) t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  let s : ℝ → ℂ := fun u => estermannVerticalPoint (3 / 2 : ℝ) u
  have hs : ContinuousAt s t := by
    dsimp [s, estermannVerticalPoint]
    fun_prop
  have hreflect : ContinuousAt (fun u : ℝ => 1 - s u) t := by
    fun_prop
  have hgammaPoint : ContinuousAt Complex.Gamma (1 - s t) := by
    apply Complex.continuousAt_Gamma
    intro n hn
    have hre := congrArg Complex.re hn
    norm_num [s, estermannVerticalPoint] at hre
    cases n with
    | zero => norm_num at hre
    | succ n =>
        have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_num
        norm_num at hre
        linarith
  have hgamma : ContinuousAt (fun u : ℝ => Complex.Gamma (1 - s u)) t :=
    by
      change ContinuousAt
        (Complex.Gamma ∘ (fun u : ℝ => 1 - s u)) t
      exact @ContinuousAt.comp' ℝ ℂ ℂ _ _ _
        (fun u : ℝ => 1 - s u) Complex.Gamma t hgammaPoint hreflect
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hpow : ContinuousAt (fun u : ℝ => (x : ℂ) ^ (s u - 1)) t :=
    (continuousAt_const_cpow hx0).comp (by fun_prop)
  have hDPoint : ContinuousAt (estermannHurwitzContinuation a q) (1 - s t) := by
    exact (differentiableAt_estermannHurwitzContinuation a q (by
      intro heq
      have hre := congrArg Complex.re heq
      norm_num [s, estermannVerticalPoint] at hre)).continuousAt
  have hD : ContinuousAt
      (fun u : ℝ => estermannHurwitzContinuation a q (1 - s u)) t :=
    by
      change ContinuousAt
        (estermannHurwitzContinuation a q ∘
          (fun u : ℝ => 1 - s u)) t
      exact @ContinuousAt.comp' ℝ ℂ ℂ _ _ _
        (fun u : ℝ => 1 - s u) (estermannHurwitzContinuation a q) t
          hDPoint hreflect
  have htotal := (hgamma.mul hpow).neg.mul hD
  change ContinuousAt (fun u : ℝ =>
    -(Complex.Gamma (1 - s u) * (x : ℂ) ^ (s u - 1)) *
      estermannHurwitzContinuation a q (1 - s u)) t at htotal
  simpa [s, estermannWeightedIntegrand,
    bettinConreyNormalizedAbelReflectionWeight,
    bettinConreyRawAbelReflectionWeight] using htotal

/-- Explicit majorant for the complete right-line integrand. -/
noncomputable def EstermannNegativeHalfPolynomialGrowth.rightMajorant
    {a q : ℕ} [NeZero q]
    (H : EstermannNegativeHalfPolynomialGrowth a q)
    (x : ℝ) (t : ℝ) : ℝ :=
  (Real.rpow x (1 / 2 : ℝ) * Real.sqrt (8 * Real.pi) * H.C) *
    abelPolynomialExponentialMajorant H.degree (Real.pi / 2) t

theorem EstermannNegativeHalfPolynomialGrowth.rightMajorant_nonneg
    {a q : ℕ} [NeZero q]
    (H : EstermannNegativeHalfPolynomialGrowth a q)
    {x : ℝ} (hx : 0 < x) (t : ℝ) :
    0 ≤ H.rightMajorant x t := by
  unfold rightMajorant abelPolynomialExponentialMajorant
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hx.le _) (Real.sqrt_nonneg _))
      H.C_nonneg)
    (mul_nonneg (pow_nonneg (by positivity) _) (Real.exp_nonneg _))

/-- Polynomial growth of the Estermann continuation is absorbed by the
intrinsic Gamma decay on the reflected right line. -/
theorem EstermannNegativeHalfPolynomialGrowth.norm_rightIntegrand_le
    {a q : ℕ} [NeZero q]
    (H : EstermannNegativeHalfPolynomialGrowth a q)
    {x : ℝ} (hx : 0 < x) (t : ℝ) :
    ‖estermannWeightedIntegrand a q
        (bettinConreyNormalizedAbelReflectionWeight x)
        (estermannVerticalPoint (3 / 2 : ℝ) t)‖ ≤
      H.rightMajorant x t := by
  have hgammaArg :
      1 - estermannVerticalPoint (3 / 2 : ℝ) t =
        (-(1 / 2 : ℝ) : ℂ) + Complex.I * (-t : ℂ) := by
    unfold estermannVerticalPoint
    push_cast
    ring
  have hGamma :
      ‖Complex.Gamma
          ((-(1 / 2 : ℝ) : ℂ) + Complex.I * (-t : ℂ))‖ ≤
        Real.sqrt (8 * Real.pi) *
          Real.exp (-(Real.pi / 2) * |t|) := by
    convert norm_Gamma_neg_half_add_I_mul_le_majorant (-t) using 1 <;>
      simp [gammaNegativeHalfMajorant, abs_neg, mul_comm]
  have hD :
      ‖estermannHurwitzContinuation a q
          ((-(1 / 2 : ℝ) : ℂ) + Complex.I * (-t : ℂ))‖ ≤
        H.C * (1 + |-t|) ^ H.degree := by
    convert H.bound (-t) using 1
    unfold estermannVerticalPoint
    push_cast
    ring_nf
  have hxpow : 0 ≤ Real.rpow x (1 / 2 : ℝ) := Real.rpow_nonneg hx.le _
  have hgammaNonneg :
      0 ≤ Real.sqrt (8 * Real.pi) *
        Real.exp (-(Real.pi / 2) * |t|) := by positivity
  unfold estermannWeightedIntegrand
    bettinConreyNormalizedAbelReflectionWeight
    bettinConreyRawAbelReflectionWeight
  rw [norm_mul, norm_neg, norm_mul]
  rw [hgammaArg]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [estermannVerticalPoint_re, sub_re, one_re]
  norm_num
  have hprod := mul_le_mul hGamma hD (norm_nonneg _) hgammaNonneg
  have htotal := mul_le_mul_of_nonneg_left hprod hxpow
  unfold rightMajorant abelPolynomialExponentialMajorant
  simpa [abs_neg, mul_assoc, mul_left_comm, mul_comm] using htotal

/-- The right vertical line is genuinely Bochner integrable from the single
fixed-line polynomial-growth input. -/
theorem EstermannNegativeHalfPolynomialGrowth.right_integrable
    {a q : ℕ} [NeZero q]
    (H : EstermannNegativeHalfPolynomialGrowth a q)
    {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ =>
      estermannWeightedIntegrand a q
        (bettinConreyNormalizedAbelReflectionWeight x)
        (estermannVerticalPoint (3 / 2 : ℝ) t)) := by
  have hmajor : Integrable (H.rightMajorant x) := by
    unfold rightMajorant
    exact (integrable_abelPolynomialExponentialMajorant H.degree
      (by positivity : 0 < Real.pi / 2)).const_mul _
  apply Integrable.mono' hmajor
  · exact (continuous_normalizedAbel_rightVerticalIntegrand x hx a q).aestronglyMeasurable
  · filter_upwards [] with t
    exact H.norm_rightIntegrand_le hx t

/-! ## Coupled horizontal decay -/

/-- The standard polynomial-times-exponential profile for the two
horizontal edges.  Unlike a Gaussian profile, this is intrinsic to the raw
Abel contour. -/
noncomputable def abelHorizontalPolynomialExponentialMajorant
    (C : ℝ) (degree : ℕ) (rate T : ℝ) : ℝ :=
  C * T ^ degree * Real.exp (-rate * T)

theorem tendsto_abelHorizontalPolynomialExponentialMajorant
    (C : ℝ) (degree : ℕ) {rate : ℝ} (hrate : 0 < rate) :
    Tendsto (abelHorizontalPolynomialExponentialMajorant C degree rate)
      atTop (𝓝 0) := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (degree : ℝ) rate hrate
  have h' : Tendsto
      (fun T : ℝ => T ^ degree * Real.exp (-rate * T))
      atTop (𝓝 0) := by
    simpa [Real.rpow_natCast] using h
  have hmul := (tendsto_const_nhds.mul h' : Tendsto
    (fun T : ℝ => C * (T ^ degree * Real.exp (-rate * T)))
    atTop (𝓝 (C * 0)))
  have heq :
      abelHorizontalPolynomialExponentialMajorant C degree rate =
        fun T : ℝ => C * (T ^ degree * Real.exp (-rate * T)) := by
    funext T
    unfold abelHorizontalPolynomialExponentialMajorant
    ring
  rw [heq]
  simpa using hmul

/-- A source-level eventual strip estimate for the coupled upper and lower
edges.  The same majorant is used before the two oriented edges are added,
so their coupling is retained. -/
structure BettinConreyAbelHorizontalPolynomialDecay
    (x : ℝ) (a q : ℕ) [NeZero q] where
  C : ℝ
  C_nonneg : 0 ≤ C
  degree : ℕ
  rate : ℝ
  rate_pos : 0 < rate
  eventual_bound : ∀ᶠ T : ℝ in atTop,
    1 ≤ T ∧
      HasSymmetricHorizontalBoundAt
        (estermannWeightedIntegrand a q
          (bettinConreyNormalizedAbelReflectionWeight x))
        (-1 / 2 : ℝ) (3 / 2 : ℝ)
        (abelHorizontalPolynomialExponentialMajorant C degree rate) T

/-- The source strip estimate gives the exact coupled horizontal limit used
by the infinite contour. -/
theorem BettinConreyAbelHorizontalPolynomialDecay.horizontal_pair_vanishes
    {x : ℝ} {a q : ℕ} [NeZero q]
    (H : BettinConreyAbelHorizontalPolynomialDecay x a q) :
    Tendsto
      (symmetricHorizontalEdges
        (estermannWeightedIntegrand a q
          (bettinConreyNormalizedAbelReflectionWeight x))
        (-1 / 2 : ℝ) (3 / 2 : ℝ)) atTop (𝓝 0) := by
  apply horizontal_pair_vanishes_of_eventual_majorant
    (estermannWeightedIntegrand a q
      (bettinConreyNormalizedAbelReflectionWeight x))
    (-1 / 2 : ℝ) (3 / 2 : ℝ)
    (abelHorizontalPolynomialExponentialMajorant H.C H.degree H.rate)
    (by norm_num)
  · filter_upwards [H.eventual_bound] with T hT
    exact ⟨by linarith [hT.1], hT.2⟩
  · exact tendsto_abelHorizontalPolynomialExponentialMajorant
      H.C H.degree H.rate_pos

/-- The exact classical data now sufficient for the infinite Abel contour:
one fixed-line polynomial estimate and one eventual coupled strip estimate.
-/
structure BettinConreyAbelClassicalDecayData
    (x : ℝ) (a q : ℕ) [NeZero q] where
  right : EstermannNegativeHalfPolynomialGrowth a q
  horizontal : BettinConreyAbelHorizontalPolynomialDecay x a q

/-- The classical fixed-line and strip estimates discharge both remaining
fields of `BettinConreyAbelContourLimitData`. -/
noncomputable def BettinConreyAbelClassicalDecayData.toContourLimitData
    {x : ℝ} (hx : 0 < x) {a q : ℕ} [NeZero q]
    (H : BettinConreyAbelClassicalDecayData x a q) :
    RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelContourLimit.BettinConreyAbelContourLimitData
      x a q where
  right_integrable := H.right.right_integrable hx
  horizontal_pair_vanishes := H.horizontal.horizontal_pair_vanishes

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelRightLine
