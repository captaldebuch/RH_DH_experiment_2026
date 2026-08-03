import Mathlib.NumberTheory.Harmonic.GammaDeriv
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannFiniteFourier
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCAbelHurwitzPLGrowth

/-!
# Route C: the fixed-twist Abel finite part

The unconditional two-pole rectangle gives an exact identity between one
exponentially damped Estermann row, its Laurent residue at zero, its value at
zero, and a reflected vertical integral.  This module proves that the
reflected integral tends to zero with the sharp elementary factor `x^(1/2)`.
Consequently the residue-subtracted damped row converges to the genuine
continued Estermann value at zero.

This is the fixed-additive-twist component of the rational Abel boundary.  It
does not replace the still coupled task of comparing the second Lambert row
along `-1 / (h/k * (1 + i*delta))` with a fixed rational additive twist.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelFinitePart

open Complex Filter MeasureTheory Topology
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannAtZeroBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannContourShift
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannFiniteFourier
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannHurwitz
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi
open RH.Criteria.NymanBeurling.BCFLogTaperRationalSineEndpoint
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelHurwitzGrowth
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelHurwitzPLGrowth
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelMellin
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelReflectionWeight
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelRightLine
open RH.Criteria.NymanBeurling.VasyuninGram

/-- The `x`-independent norm mass left after extracting the factor
`x^(1/2)` from the reflected right-line majorant. -/
noncomputable def abelFixedTwistRightLineConstant
    (a q : ℕ) [NeZero q] : ℝ :=
  let H := estermannNegativeHalfPolynomialGrowth a q
  (Real.sqrt (8 * Real.pi) * H.C) *
    ∫ t : ℝ,
      abelPolynomialExponentialMajorant H.degree (Real.pi / 2) t

theorem abelFixedTwistRightLineConstant_nonneg
    (a q : ℕ) [NeZero q] :
    0 ≤ abelFixedTwistRightLineConstant a q := by
  let H := estermannNegativeHalfPolynomialGrowth a q
  have hbase : 0 ≤ ∫ t : ℝ,
      abelPolynomialExponentialMajorant H.degree (Real.pi / 2) t :=
    integral_nonneg fun t => by
      unfold abelPolynomialExponentialMajorant
      positivity
  unfold abelFixedTwistRightLineConstant
  dsimp only
  exact mul_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) H.C_nonneg) hbase

/-- The transformed vertical integral costs exactly a square-root power of
the Abel damping parameter.  All dependence on the additive twist is kept in
the fixed finite constant. -/
theorem norm_abelFixedTwistRightLine_le
    (a q : ℕ) [NeZero q] {x : ℝ} (hx : 0 < x) :
    ‖estermannPrimalVerticalIntegral a q (3 / 2 : ℝ)
        (bettinConreyNormalizedAbelReflectionWeight x)‖ ≤
      Real.rpow x (1 / 2 : ℝ) *
        abelFixedTwistRightLineConstant a q := by
  let H := estermannNegativeHalfPolynomialGrowth a q
  let f : ℝ → ℂ := fun t =>
    estermannWeightedIntegrand a q
      (bettinConreyNormalizedAbelReflectionWeight x)
      (estermannVerticalPoint (3 / 2 : ℝ) t)
  have hmajor : Integrable (H.rightMajorant x) := by
    unfold EstermannNegativeHalfPolynomialGrowth.rightMajorant
    exact (integrable_abelPolynomialExponentialMajorant H.degree
      (by positivity : 0 < Real.pi / 2)).const_mul _
  have hnorm : ‖∫ t : ℝ, f t‖ ≤ ∫ t : ℝ, H.rightMajorant x t := by
    apply norm_integral_le_of_norm_le hmajor
    filter_upwards [] with t
    exact H.norm_rightIntegrand_le hx t
  unfold estermannPrimalVerticalIntegral
  change ‖∫ t : ℝ, f t‖ ≤ _
  calc
    ‖∫ t : ℝ, f t‖ ≤ ∫ t : ℝ, H.rightMajorant x t := hnorm
    _ = Real.rpow x (1 / 2 : ℝ) *
        abelFixedTwistRightLineConstant a q := by
      unfold EstermannNegativeHalfPolynomialGrowth.rightMajorant
        abelFixedTwistRightLineConstant
      dsimp only [H]
      rw [integral_const_mul]
      ring

/-- The reflected side of the non-Gaussian Abel rectangle vanishes as the
damping tends to zero from the right. -/
theorem tendsto_abelFixedTwistRightLine_zero
    (a q : ℕ) [NeZero q] :
    Tendsto (fun x : ℝ =>
        estermannPrimalVerticalIntegral a q (3 / 2 : ℝ)
          (bettinConreyNormalizedAbelReflectionWeight x))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hrpow : Tendsto (fun x : ℝ => Real.rpow x (1 / 2 : ℝ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hcont :=
      (Real.continuousAt_rpow_const 0 (1 / 2 : ℝ) (Or.inr (by norm_num))).tendsto
    simpa [Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)] using
      hcont.mono_left inf_le_left
  have hprofile : Tendsto (fun x : ℝ =>
      Real.rpow x (1 / 2 : ℝ) *
        abelFixedTwistRightLineConstant a q)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa using hrpow.mul_const (abelFixedTwistRightLineConstant a q)
  apply squeeze_zero_norm'
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact norm_abelFixedTwistRightLine_le a q hx
  · exact hprofile

/-! ## Explicit Laurent normalization -/

/-- The derivative at the Estermann double-pole location records exactly
the logarithmic Abel divergence. -/
theorem deriv_normalizedAbelReflectionWeight_zero
    {x : ℝ} (hx : 0 < x) :
    deriv (bettinConreyNormalizedAbelReflectionWeight x) 0 =
      -(x : ℂ)⁻¹ *
        (((Real.eulerMascheroniConstant : ℝ) : ℂ) +
          (Real.log x : ℂ)) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hinner : HasDerivAt (fun s : ℂ => 1 - s) (-1) 0 := by
    convert (hasDerivAt_const (x := (0 : ℂ)) (c := (1 : ℂ))).sub
      (hasDerivAt_id (x := (0 : ℂ))) using 1
    ring
  have houter : HasDerivAt Complex.Gamma
      (-((Real.eulerMascheroniConstant : ℝ) : ℂ))
      (1 - (0 : ℂ)) := by
    simpa using Complex.hasDerivAt_Gamma_one
  have hgammaRaw := HasDerivAt.comp
    (𝕜 := ℂ) (𝕜' := ℂ) (x := (0 : ℂ))
    houter hinner
  have hgamma : HasDerivAt
      (fun s : ℂ => Complex.Gamma (1 - s))
      ((Real.eulerMascheroniConstant : ℝ) : ℂ) 0 := by
    convert hgammaRaw using 1
    ring
  have hshift : HasDerivAt (fun s : ℂ => s - 1) 1 0 := by
    simpa using (hasDerivAt_id (x := (0 : ℂ))).sub_const 1
  have hpowRaw := hshift.const_cpow (c := (x : ℂ)) (Or.inl hx0)
  have hpow : HasDerivAt (fun s : ℂ => (x : ℂ) ^ (s - 1))
      ((x : ℂ)⁻¹ * (Real.log x : ℂ)) 0 := by
    convert hpowRaw using 1
    · simp only [zero_sub, Complex.cpow_neg_one, mul_one]
      rw [← Complex.ofReal_log hx.le]
  have hraw := hgamma.mul hpow
  have hnormalized := hraw.neg
  change HasDerivAt
    (fun s : ℂ =>
      -(Complex.Gamma (1 - s) * (x : ℂ) ^ (s - 1))) _ 0 at hnormalized
  unfold bettinConreyNormalizedAbelReflectionWeight
    bettinConreyRawAbelReflectionWeight
  rw [hnormalized.deriv]
  norm_num [Complex.cpow_neg_one, Complex.Gamma_one]
  ring

/-- For a reduced additive twist the entire divergent residue is now
explicit: a logarithmic term divided by `x*q`, plus the fixed simple Laurent
coefficient divided by `x`. -/
theorem normalizedAbelWeightedResidueCoefficient_eq
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q)
    {x : ℝ} (hx : 0 < x) :
    estermannWeightedResidueCoefficient a q
        (bettinConreyNormalizedAbelReflectionWeight x) =
      (-(x : ℂ)⁻¹ *
          (((Real.eulerMascheroniConstant : ℝ) : ℂ) +
            (Real.log x : ℂ))) * (q : ℂ)⁻¹ +
        (x : ℂ)⁻¹ * estermannSimplePoleCoefficient a q := by
  rw [estermannWeightedResidueCoefficient_eq a q hcop,
    deriv_normalizedAbelReflectionWeight_zero hx,
    normalizedAbelReflectionWeight_zero]
  ring

/-- The exact fixed-twist Abel finite-part theorem.  After subtracting the
Laurent residue forced by the double pole at one, the damped divisor row
converges to the analytically continued Estermann value at zero. -/
theorem tendsto_dampedEstermann_sub_residue_zero
    (a q : ℕ) [NeZero q] :
    Tendsto (fun x : ℝ =>
        dampedEstermannLambertSeries a q x -
          estermannWeightedResidueCoefficient a q
            (bettinConreyNormalizedAbelReflectionWeight x))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (estermannHurwitzContinuation a q 0)) := by
  have hright := tendsto_abelFixedTwistRightLine_zero a q
  have htarget : Tendsto (fun x : ℝ =>
      estermannHurwitzContinuation a q 0 -
        estermannPrimalVerticalIntegral a q (3 / 2 : ℝ)
          (bettinConreyNormalizedAbelReflectionWeight x) /
            (2 * Real.pi : ℝ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (estermannHurwitzContinuation a q 0)) := by
    simpa using tendsto_const_nhds.sub
      (hright.div_const (2 * Real.pi : ℝ))
  apply htarget.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hcontour := rightVertical_eq_damped_add_residues
    (x := x) hx a q
  have hpi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
  push_cast at hcontour ⊢
  field_simp [hpi]
  linear_combination -hcontour

/-- At the inverse additive frequency used by the H15 Vasyunin convention,
the fixed-twist Abel finite part is exactly the finite cotangent value.  All
analytic continuation and all finite Fourier algebra in this statement are
unconditional theorems. -/
theorem tendsto_inverseDampedEstermann_sub_residue_cotangent
    (a q : ℕ) (ha : 0 < a) (hq : 0 < q)
    (hcop : Nat.Coprime a q) :
    letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
    Tendsto (fun x : ℝ =>
        dampedEstermannLambertSeries (inverseResidue a q) q x -
          estermannWeightedResidueCoefficient (inverseResidue a q) q
            (bettinConreyNormalizedAbelReflectionWeight x))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((1 / 4 : ℂ) - Complex.I / 2 *
        (cotangentSumVFormula a q : ℂ))) := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have hlim := tendsto_dampedEstermann_sub_residue_zero
    (inverseResidue a q) q
  let HZ : HurwitzZetaZeroFormula :=
    (hurwitzZetaZeroNonzeroFormula_of_rationalSineZetaOne
      rationalSineZetaOneFormula).toZeroFormula
  have hvalue :
      estermannHurwitzContinuation (inverseResidue a q) q 0 =
        (1 / 4 : ℂ) - Complex.I / 2 *
          (cotangentSumVFormula a q : ℂ) := by
    rw [estermannHurwitzContinuation_zero_eq_bernoulliFinite HZ]
    change inverseEstermannBernoulliFiniteValue a q = _
    exact estermannBernoulliCotangentIdentity.value_eq
      a q ha hq hcop
  simpa [hvalue] using hlim

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelFinitePart
