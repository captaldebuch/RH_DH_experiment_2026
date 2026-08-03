import Mathlib.NumberTheory.Harmonic.GammaDeriv
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCAbelFinitePart
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCAbelReciprocalRay

/-!
# Route C: the complex Abel damping sector

Inversion of the rational Bettin--Conrey boundary does not preserve a real
Abel parameter.  It produces a complex parameter `u` with positive real part.
This file extends the reflected Mellin weight from positive real damping to
arbitrary nonzero complex damping (with the principal logarithm), computes
its two Laurent data exactly, and proves the sectorial power estimate needed
on the reflected vertical line.

The remaining analytic input is the complex inverse-Mellin identity itself.
Nothing in this file assumes that identity or an Abel boundary value.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelComplexDamping

open Complex Filter MeasureTheory Set Topology
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannContourShift
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannHurwitz
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelMellin
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelReflectionWeight
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelReciprocalRay
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelRightLine

/-- The reflected Abel--Mellin weight for a nonzero complex damping
parameter, normalized to have residue one at `s = 1`. -/
noncomputable def bettinConreyComplexAbelReflectionWeight
    (u s : ℂ) : ℂ :=
  -(Complex.Gamma (1 - s) * u ^ (s - 1))

/-- The complex definition extends the earlier positive-real definition
definitionally. -/
theorem complexAbelReflectionWeight_ofReal
    (x : ℝ) (s : ℂ) :
    bettinConreyComplexAbelReflectionWeight (x : ℂ) s =
      bettinConreyNormalizedAbelReflectionWeight x s := by
  rfl

theorem differentiableAt_complexAbelReflectionWeight_zero
    {u : ℂ} (hu : u ≠ 0) :
    DifferentiableAt ℂ (bettinConreyComplexAbelReflectionWeight u) 0 := by
  unfold bettinConreyComplexAbelReflectionWeight
  apply DifferentiableAt.neg
  apply DifferentiableAt.mul
  · have hinner : DifferentiableAt ℂ (fun s : ℂ => 1 - s) 0 := by
      fun_prop
    have hgamma : DifferentiableAt ℂ Complex.Gamma (1 - (0 : ℂ)) := by
      simpa using Complex.differentiableAt_Gamma_one
    simpa using (hgamma.comp (f := fun s : ℂ => 1 - s) 0 hinner)
  · exact (differentiableAt_id.sub_const 1).const_cpow (Or.inl hu)

/-- Exact value at the reflected Estermann double pole. -/
theorem complexAbelReflectionWeight_zero (u : ℂ) :
    bettinConreyComplexAbelReflectionWeight u 0 = -u⁻¹ := by
  simp [bettinConreyComplexAbelReflectionWeight, Complex.Gamma_one,
    Complex.cpow_neg_one]

/-- The derivative at zero contains the principal complex logarithm.  This
is the exact Laurent correction required on the reciprocal complex ray. -/
theorem deriv_complexAbelReflectionWeight_zero
    {u : ℂ} (hu : u ≠ 0) :
    deriv (bettinConreyComplexAbelReflectionWeight u) 0 =
      -u⁻¹ *
        (((Real.eulerMascheroniConstant : ℝ) : ℂ) + Complex.log u) := by
  have hinner : HasDerivAt (fun s : ℂ => 1 - s) (-1) 0 := by
    convert (hasDerivAt_const (x := (0 : ℂ)) (c := (1 : ℂ))).sub
      (hasDerivAt_id (x := (0 : ℂ))) using 1
    ring
  have houter : HasDerivAt Complex.Gamma
      (-((Real.eulerMascheroniConstant : ℝ) : ℂ))
      (1 - (0 : ℂ)) := by
    simpa using Complex.hasDerivAt_Gamma_one
  have hgammaRaw := HasDerivAt.comp
    (𝕜 := ℂ) (𝕜' := ℂ) (x := (0 : ℂ)) houter hinner
  have hgamma : HasDerivAt
      (fun s : ℂ => Complex.Gamma (1 - s))
      ((Real.eulerMascheroniConstant : ℝ) : ℂ) 0 := by
    convert hgammaRaw using 1
    ring
  have hshift : HasDerivAt (fun s : ℂ => s - 1) 1 0 := by
    simpa using (hasDerivAt_id (x := (0 : ℂ))).sub_const 1
  have hpowRaw := hshift.const_cpow (c := u) (Or.inl hu)
  have hpow : HasDerivAt (fun s : ℂ => u ^ (s - 1))
      (u⁻¹ * Complex.log u) 0 := by
    convert hpowRaw using 1
    simp only [zero_sub, Complex.cpow_neg_one, mul_one]
  have hnormalized := (hgamma.mul hpow).neg
  change HasDerivAt
    (fun s : ℂ => -(Complex.Gamma (1 - s) * u ^ (s - 1))) _ 0
      at hnormalized
  unfold bettinConreyComplexAbelReflectionWeight
  rw [hnormalized.deriv]
  norm_num [Complex.cpow_neg_one, Complex.Gamma_one]
  ring

/-- The normalization at `s=1` is independent of the direction from which
the nonzero complex damping approaches zero. -/
theorem hasUnitResidueAtOne_complexAbelReflectionWeight
    {u : ℂ} (hu : u ≠ 0) :
    HasUnitResidueAtOne (bettinConreyComplexAbelReflectionWeight u) := by
  unfold HasUnitResidueAtOne
  have hsub : Tendsto (fun s : ℂ => 1 - s)
      (𝓝[≠] (1 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
    simpa using
      (((hasDerivAt_const (x := (1 : ℂ)) (c := (1 : ℂ))).sub
        (hasDerivAt_id (x := (1 : ℂ)))).tendsto_nhdsNE (by norm_num))
  have hgamma : Tendsto
      (fun s : ℂ => (1 - s) * Complex.Gamma (1 - s))
      (𝓝[≠] (1 : ℂ)) (𝓝 1) :=
    Complex.tendsto_self_mul_Gamma_nhds_zero.comp hsub
  have hpow : Tendsto (fun s : ℂ => u ^ (s - 1))
      (𝓝[≠] (1 : ℂ)) (𝓝 1) := by
    have hcont : ContinuousAt (fun s : ℂ => u ^ (s - 1)) 1 :=
      (continuousAt_const_cpow hu).comp
        (continuousAt_id.sub continuousAt_const)
    simpa using hcont.tendsto.mono_left inf_le_left
  have hproduct := hgamma.mul hpow
  apply (show Tendsto
      (fun s : ℂ => ((1 - s) * Complex.Gamma (1 - s)) * u ^ (s - 1))
      (𝓝[≠] (1 : ℂ)) (𝓝 1) by simpa using hproduct).congr'
  filter_upwards with s
  unfold bettinConreyComplexAbelReflectionWeight
  ring

/-- Explicit residue coefficient for the complex-damped Estermann row. -/
theorem complexAbelWeightedResidueCoefficient_eq
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q)
    {u : ℂ} (hu : u ≠ 0) :
    estermannWeightedResidueCoefficient a q
        (bettinConreyComplexAbelReflectionWeight u) =
      (-u⁻¹ *
          (((Real.eulerMascheroniConstant : ℝ) : ℂ) + Complex.log u)) *
          (q : ℂ)⁻¹ +
        u⁻¹ * estermannSimplePoleCoefficient a q := by
  rw [estermannWeightedResidueCoefficient_eq a q hcop,
    deriv_complexAbelReflectionWeight_zero hu,
    complexAbelReflectionWeight_zero]
  ring

/-! ## Sectorial vertical control -/

/-- Exact norm of the complex power on the reflected right line. -/
theorem norm_complexAbelCpow_rightLine
    {u : ℂ} (hu : u ≠ 0) (t : ℝ) :
    ‖u ^ (estermannVerticalPoint (3 / 2 : ℝ) t - 1)‖ =
      ‖u‖ ^ (1 / 2 : ℝ) / Real.exp (Complex.arg u * t) := by
  rw [Complex.norm_cpow_of_ne_zero hu]
  congr 2 <;> norm_num [estermannVerticalPoint]

/-- Inside a sector, the angular part of the complex power costs at most
`exp(theta*|t|)`. -/
theorem norm_complexAbelCpow_rightLine_le
    {u : ℂ} (hu : u ≠ 0) {theta : ℝ}
    (harg : |Complex.arg u| ≤ theta) (t : ℝ) :
    ‖u ^ (estermannVerticalPoint (3 / 2 : ℝ) t - 1)‖ ≤
      ‖u‖ ^ (1 / 2 : ℝ) * Real.exp (theta * |t|) := by
  rw [norm_complexAbelCpow_rightLine hu]
  rw [div_eq_mul_inv, ← Real.exp_neg]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (norm_nonneg _) _)
  apply Real.exp_le_exp.mpr
  calc
    -(Complex.arg u * t) ≤ |-(Complex.arg u * t)| := le_abs_self _
    _ = |Complex.arg u| * |t| := by rw [abs_neg, abs_mul]
    _ ≤ theta * |t| :=
      mul_le_mul_of_nonneg_right harg (abs_nonneg t)

/-- Sectorial majorant for the complete reflected Estermann integrand. -/
noncomputable def complexAbelRightMajorant
    {a q : ℕ} [NeZero q]
    (H : EstermannNegativeHalfPolynomialGrowth a q)
    (u : ℂ) (theta t : ℝ) : ℝ :=
  (‖u‖ ^ (1 / 2 : ℝ) * Real.sqrt (8 * Real.pi) * H.C) *
    abelPolynomialExponentialMajorant H.degree
      (Real.pi / 2 - theta) t

/-- Polynomial Estermann growth remains integrable for every closed sector
strictly inside the right half-plane. -/
theorem EstermannNegativeHalfPolynomialGrowth.norm_complexRightIntegrand_le
    {a q : ℕ} [NeZero q]
    (H : EstermannNegativeHalfPolynomialGrowth a q)
    {u : ℂ} (hu : u ≠ 0) {theta : ℝ}
    (harg : |Complex.arg u| ≤ theta) (t : ℝ) :
    ‖estermannWeightedIntegrand a q
        (bettinConreyComplexAbelReflectionWeight u)
        (estermannVerticalPoint (3 / 2 : ℝ) t)‖ ≤
      complexAbelRightMajorant H u theta t := by
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
        H.C * (1 + |t|) ^ H.degree := by
    convert H.bound (-t) using 1
    · unfold estermannVerticalPoint
      push_cast
      ring_nf
    · rw [abs_neg]
  have hpow := norm_complexAbelCpow_rightLine_le hu harg t
  have hGammaNonneg :
      0 ≤ Real.sqrt (8 * Real.pi) *
        Real.exp (-(Real.pi / 2) * |t|) := by positivity
  have hpowNonneg :
      0 ≤ ‖u‖ ^ (1 / 2 : ℝ) * Real.exp (theta * |t|) := by
    positivity
  unfold estermannWeightedIntegrand
    bettinConreyComplexAbelReflectionWeight
  rw [norm_mul, norm_neg, norm_mul, hgammaArg]
  have hfirst := mul_le_mul hGamma hpow
    (norm_nonneg _) hGammaNonneg
  have htotal := mul_le_mul hfirst hD
    (norm_nonneg _) (mul_nonneg hGammaNonneg hpowNonneg)
  unfold complexAbelRightMajorant
    abelPolynomialExponentialMajorant
  calc
    ‖Complex.Gamma
          ((-(1 / 2 : ℝ) : ℂ) + Complex.I * (-t : ℂ))‖ *
          ‖u ^ (estermannVerticalPoint (3 / 2 : ℝ) t - 1)‖ *
        ‖estermannHurwitzContinuation a q
          ((-(1 / 2 : ℝ) : ℂ) + Complex.I * (-t : ℂ))‖ ≤
        (Real.sqrt (8 * Real.pi) *
            Real.exp (-(Real.pi / 2) * |t|)) *
          (‖u‖ ^ (1 / 2 : ℝ) * Real.exp (theta * |t|)) *
          (H.C * (1 + |t|) ^ H.degree) := htotal
    _ = (‖u‖ ^ (1 / 2 : ℝ) * Real.sqrt (8 * Real.pi) * H.C) *
          ((1 + |t|) ^ H.degree *
            Real.exp (-(Real.pi / 2 - theta) * |t|)) := by
      have hexp :
          Real.exp (-(Real.pi / 2) * |t|) *
              Real.exp (theta * |t|) =
            Real.exp (-(Real.pi / 2 - theta) * |t|) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [← hexp]
      ring

/-- The sectorial majorant is integrable with a uniform positive angular
gap from the imaginary axis. -/
theorem integrable_complexAbelRightMajorant
    {a q : ℕ} [NeZero q]
    (H : EstermannNegativeHalfPolynomialGrowth a q)
    (u : ℂ) {theta : ℝ} (htheta : theta < Real.pi / 2) :
    Integrable (complexAbelRightMajorant H u theta) := by
  unfold complexAbelRightMajorant
  exact (integrable_abelPolynomialExponentialMajorant H.degree
    (sub_pos.mpr htheta)).const_mul _

/-- The complete complex-damped right-line integrand is continuous for every
nonzero damping parameter. -/
theorem continuous_complexAbel_rightVerticalIntegrand
    {u : ℂ} (hu : u ≠ 0) (a q : ℕ) [NeZero q] :
    Continuous (fun t : ℝ =>
      estermannWeightedIntegrand a q
        (bettinConreyComplexAbelReflectionWeight u)
        (estermannVerticalPoint (3 / 2 : ℝ) t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  let s : ℝ → ℂ := fun v => estermannVerticalPoint (3 / 2 : ℝ) v
  have hs : ContinuousAt s t := by
    dsimp [s, estermannVerticalPoint]
    fun_prop
  have hreflect : ContinuousAt (fun v : ℝ => 1 - s v) t := by
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
  have hgamma : ContinuousAt
      (fun v : ℝ => Complex.Gamma (1 - s v)) t := by
    change ContinuousAt
      (Complex.Gamma ∘ (fun v : ℝ => 1 - s v)) t
    exact @ContinuousAt.comp' ℝ ℂ ℂ _ _ _
      (fun v : ℝ => 1 - s v) Complex.Gamma t hgammaPoint hreflect
  have hpow : ContinuousAt (fun v : ℝ => u ^ (s v - 1)) t :=
    (continuousAt_const_cpow hu).comp (by fun_prop)
  have hDPoint : ContinuousAt (estermannHurwitzContinuation a q)
      (1 - s t) := by
    exact (differentiableAt_estermannHurwitzContinuation a q (by
      intro heq
      have hre := congrArg Complex.re heq
      norm_num [s, estermannVerticalPoint] at hre)).continuousAt
  have hD : ContinuousAt
      (fun v : ℝ => estermannHurwitzContinuation a q (1 - s v)) t := by
    change ContinuousAt
      (estermannHurwitzContinuation a q ∘
        (fun v : ℝ => 1 - s v)) t
    exact @ContinuousAt.comp' ℝ ℂ ℂ _ _ _
      (fun v : ℝ => 1 - s v) (estermannHurwitzContinuation a q) t
        hDPoint hreflect
  have htotal := (hgamma.mul hpow).neg.mul hD
  change ContinuousAt (fun v : ℝ =>
    -(Complex.Gamma (1 - s v) * u ^ (s v - 1)) *
      estermannHurwitzContinuation a q (1 - s v)) t at htotal
  simpa [s, estermannWeightedIntegrand,
    bettinConreyComplexAbelReflectionWeight] using htotal

/-- The complete complex-damped right line is Bochner integrable throughout
every strict right-half-plane sector. -/
theorem EstermannNegativeHalfPolynomialGrowth.complex_right_integrable
    {a q : ℕ} [NeZero q]
    (H : EstermannNegativeHalfPolynomialGrowth a q)
    {u : ℂ} (hu : u ≠ 0) {theta : ℝ}
    (harg : |Complex.arg u| ≤ theta)
    (htheta : theta < Real.pi / 2) :
    Integrable (fun t : ℝ =>
      estermannWeightedIntegrand a q
        (bettinConreyComplexAbelReflectionWeight u)
        (estermannVerticalPoint (3 / 2 : ℝ) t)) := by
  have hmajor := integrable_complexAbelRightMajorant H u htheta
  apply Integrable.mono' hmajor
  · exact (continuous_complexAbel_rightVerticalIntegrand hu a q).aestronglyMeasurable
  · filter_upwards [] with t
    exact EstermannNegativeHalfPolynomialGrowth.norm_complexRightIntegrand_le
      H hu harg t

/-- The `u`-independent mass of the sectorial right-line majorant. -/
noncomputable def complexAbelRightLineConstant
    {a q : ℕ} [NeZero q]
    (H : EstermannNegativeHalfPolynomialGrowth a q)
    (theta : ℝ) : ℝ :=
  (Real.sqrt (8 * Real.pi) * H.C) *
    ∫ t : ℝ, abelPolynomialExponentialMajorant H.degree
      (Real.pi / 2 - theta) t

/-- The reflected vertical integral costs only `|u|^(1/2)`, uniformly in a
fixed strict sector. -/
theorem norm_complexAbelRightLine_le
    {a q : ℕ} [NeZero q]
    (H : EstermannNegativeHalfPolynomialGrowth a q)
    {u : ℂ} (hu : u ≠ 0) {theta : ℝ}
    (harg : |Complex.arg u| ≤ theta)
    (htheta : theta < Real.pi / 2) :
    ‖estermannPrimalVerticalIntegral a q (3 / 2 : ℝ)
        (bettinConreyComplexAbelReflectionWeight u)‖ ≤
      ‖u‖ ^ (1 / 2 : ℝ) * complexAbelRightLineConstant H theta := by
  let f : ℝ → ℂ := fun t =>
    estermannWeightedIntegrand a q
      (bettinConreyComplexAbelReflectionWeight u)
      (estermannVerticalPoint (3 / 2 : ℝ) t)
  have hmajor := integrable_complexAbelRightMajorant H u htheta
  have hnorm : ‖∫ t : ℝ, f t‖ ≤
      ∫ t : ℝ, complexAbelRightMajorant H u theta t := by
    apply norm_integral_le_of_norm_le hmajor
    filter_upwards [] with t
    exact EstermannNegativeHalfPolynomialGrowth.norm_complexRightIntegrand_le
      H hu harg t
  unfold estermannPrimalVerticalIntegral
  change ‖∫ t : ℝ, f t‖ ≤ _
  calc
    ‖∫ t : ℝ, f t‖ ≤
        ∫ t : ℝ, complexAbelRightMajorant H u theta t := hnorm
    _ = ‖u‖ ^ (1 / 2 : ℝ) *
        complexAbelRightLineConstant H theta := by
      unfold complexAbelRightMajorant complexAbelRightLineConstant
      rw [integral_const_mul]
      ring

/-! ## The reciprocal ray lies in a fixed sector -/

/-- For `0 < delta ≤ 1`, the reciprocal damping ray stays in the closed
sector of half-angle `pi/4`.  This is the uniform angular gap needed to keep
half of Gamma's exponential decay. -/
theorem reciprocalComplexDamping_abs_arg_le_pi_div_four
    (h k : ℕ) {delta : ℝ}
    (hh : 0 < h) (hk : 0 < k) (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1) :
    |Complex.arg (bettinConreyReciprocalComplexDamping h k delta)| ≤
      Real.pi / 4 := by
  let u := bettinConreyReciprocalComplexDamping h k delta
  have hre : 0 < u.re := by
    dsimp [u]
    rw [bettinConreyReciprocalComplexDamping_re]
    exact bettinConreyReciprocalRealDamping_pos h k hh hk hdelta
  have him : u.im < 0 := by
    dsimp [u]
    rw [bettinConreyReciprocalComplexDamping_im]
    unfold bettinConreyReciprocalPhaseDrift
    have : 0 < 2 * Real.pi * ((k : ℝ) / (h : ℝ)) * delta ^ 2 /
        (1 + delta ^ 2) := by positivity
    linarith
  have hargNeg : Complex.arg u < 0 := Complex.arg_neg_iff.2 him
  have hargLower : -(Real.pi / 4) ≤ Complex.arg u := by
    by_contra hnot
    have hargLt : Complex.arg u < -(Real.pi / 4) := lt_of_not_ge hnot
    have hleft : -(Real.pi / 2) < Complex.arg u :=
      Complex.neg_pi_div_two_lt_arg_iff.2 (Or.inl hre)
    have hright : -(Real.pi / 4) < Real.pi / 2 := by
      linarith [Real.pi_pos]
    have htanLt := Real.tan_lt_tan_of_lt_of_lt_pi_div_two
      hleft hright hargLt
    have htanU : Real.tan (Complex.arg u) = -delta := by
      rw [Complex.tan_arg]
      dsimp [u]
      exact reciprocalComplexDamping_im_div_re
        h k hh hk hdelta
    have htanQuarter : Real.tan (-(Real.pi / 4)) = -1 := by
      rw [Real.tan_neg, Real.tan_pi_div_four]
    rw [htanU, htanQuarter] at htanLt
    linarith
  rw [abs_of_neg hargNeg]
  linarith

/-- The explicit reciprocal ray is dominated by the integrable half-angle
`pi/4` majorant, uniformly for small positive `delta`. -/
theorem norm_reciprocalComplexRightIntegrand_le
    {a q : ℕ} [NeZero q]
    (H : EstermannNegativeHalfPolynomialGrowth a q)
    (h k : ℕ) {delta : ℝ}
    (hh : 0 < h) (hk : 0 < k) (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1) (t : ℝ) :
    ‖estermannWeightedIntegrand a q
        (bettinConreyComplexAbelReflectionWeight
          (bettinConreyReciprocalComplexDamping h k delta))
        (estermannVerticalPoint (3 / 2 : ℝ) t)‖ ≤
      complexAbelRightMajorant H
        (bettinConreyReciprocalComplexDamping h k delta)
        (Real.pi / 4) t := by
  have hu : bettinConreyReciprocalComplexDamping h k delta ≠ 0 := by
    intro hu
    have hre := congrArg Complex.re hu
    rw [bettinConreyReciprocalComplexDamping_re] at hre
    have hpos := bettinConreyReciprocalRealDamping_pos
      h k hh hk hdelta
    simp only [Complex.zero_re] at hre
    linarith
  exact EstermannNegativeHalfPolynomialGrowth.norm_complexRightIntegrand_le H hu
    (reciprocalComplexDamping_abs_arg_le_pi_div_four
      h k hh hk hdelta hdeltaOne) t

/-- The reflected vertical integral on the actual reciprocal complex ray
vanishes unconditionally.  This is the complex analogue of the fixed-twist
square-root estimate. -/
theorem tendsto_reciprocalComplexAbelRightLine_zero
    {a q : ℕ} [NeZero q]
    (H : EstermannNegativeHalfPolynomialGrowth a q)
    (h k : ℕ) (hh : 0 < h) (hk : 0 < k) :
    Tendsto (fun delta : ℝ =>
        estermannPrimalVerticalIntegral a q (3 / 2 : ℝ)
          (bettinConreyComplexAbelReflectionWeight
            (bettinConreyReciprocalComplexDamping h k delta)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  let u : ℝ → ℂ := bettinConreyReciprocalComplexDamping h k
  have huZero : Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    tendsto_bettinConreyReciprocalComplexDamping_zero h k
  have hnormZero : Tendsto (fun delta : ℝ => ‖u delta‖)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa using huZero.norm
  have hrpowAt : Tendsto (fun x : ℝ => x ^ (1 / 2 : ℝ))
      (nhds (0 : ℝ)) (nhds 0) := by
    simpa [Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)] using
      (Real.continuousAt_rpow_const 0 (1 / 2 : ℝ)
        (Or.inr (by norm_num))).tendsto
  have hrpowZero : Tendsto (fun delta : ℝ => ‖u delta‖ ^ (1 / 2 : ℝ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    hrpowAt.comp hnormZero
  have hprofile : Tendsto (fun delta : ℝ =>
      ‖u delta‖ ^ (1 / 2 : ℝ) *
        complexAbelRightLineConstant H (Real.pi / 4))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa using hrpowZero.mul_const
      (complexAbelRightLineConstant H (Real.pi / 4))
  have hdeltaLe : ∀ᶠ delta : ℝ in
      nhdsWithin (0 : ℝ) (Set.Ioi 0), delta ≤ 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
      nhdsWithin_le_nhds |>.mono fun _ h => h.le
  apply squeeze_zero_norm'
  · filter_upwards [self_mem_nhdsWithin, hdeltaLe] with delta hdelta hdeltaOne
    have hu : u delta ≠ 0 := by
      intro huEq
      have hre := congrArg Complex.re huEq
      dsimp [u] at hre
      rw [bettinConreyReciprocalComplexDamping_re] at hre
      have hpos := bettinConreyReciprocalRealDamping_pos
        h k hh hk hdelta
      linarith
    exact norm_complexAbelRightLine_le H hu
      (reciprocalComplexDamping_abs_arg_le_pi_div_four
        h k hh hk hdelta hdeltaOne)
      (by linarith [Real.pi_pos])
  · exact hprofile

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelComplexDamping
