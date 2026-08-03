import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCAbelMellin
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannContourShift
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour

/-!
# Route C: the reflected Abel--Mellin weight

After the change of variables `u = 1 - s`, the undamped Abel--Mellin
integrand carries the weight

`Gamma (1 - u) * x ^ (u - 1)`.

Its residue at `u = 1` is `-1`.  The negated weight therefore has the
unit-residue normalization used by the Estermann two-pole contour package.
This file records both conventions and the exact sign relating them.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelReflectionWeight

open Complex Filter Set
open scoped Topology
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannContourShift
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannHurwitz

/-- The raw weight obtained from the substitution `u = 1 - s` in the
Abel--Mellin integral. -/
noncomputable def bettinConreyRawAbelReflectionWeight
    (x : ℝ) (s : ℂ) : ℂ :=
  Complex.Gamma (1 - s) * (x : ℂ) ^ (s - 1)

/-- The sign-normalized reflected weight.  Its residue at `s = 1` is one. -/
noncomputable def bettinConreyNormalizedAbelReflectionWeight
    (x : ℝ) (s : ℂ) : ℂ :=
  -bettinConreyRawAbelReflectionWeight x s

theorem normalizedAbelReflectionWeight_eq_neg_raw
    (x : ℝ) (s : ℂ) :
    bettinConreyNormalizedAbelReflectionWeight x s =
      -bettinConreyRawAbelReflectionWeight x s := by
  rfl

/-- The raw reflected weight is holomorphic at the double-pole location
`s = 0`; the only Gamma pole in the working strip occurs at `s = 1`. -/
theorem differentiableAt_rawAbelReflectionWeight_zero
    (x : ℝ) (hx : 0 < x) :
    DifferentiableAt ℂ (bettinConreyRawAbelReflectionWeight x) 0 := by
  have hx0 : (x : ℂ) ≠ 0 := by
    exact_mod_cast hx.ne'
  unfold bettinConreyRawAbelReflectionWeight
  apply DifferentiableAt.mul
  · have hinner : DifferentiableAt ℂ (fun s : ℂ => 1 - s) 0 := by
      fun_prop
    have hgamma : DifferentiableAt ℂ Complex.Gamma (1 - (0 : ℂ)) := by
      simpa using Complex.differentiableAt_Gamma_one
    simpa using (hgamma.comp (f := fun s : ℂ => 1 - s) 0 hinner)
  · exact (differentiableAt_id.sub_const 1).const_cpow (Or.inl hx0)

theorem differentiableAt_normalizedAbelReflectionWeight_zero
    (x : ℝ) (hx : 0 < x) :
    DifferentiableAt ℂ (bettinConreyNormalizedAbelReflectionWeight x) 0 := by
  exact (differentiableAt_rawAbelReflectionWeight_zero x hx).neg

/-- Exact value of the raw weight at the reflected Estermann double pole. -/
theorem rawAbelReflectionWeight_zero
    (x : ℝ) :
    bettinConreyRawAbelReflectionWeight x 0 = (x : ℂ)⁻¹ := by
  simp [bettinConreyRawAbelReflectionWeight, Complex.Gamma_one,
    Complex.cpow_neg_one]

/-- Exact value of the normalized weight at the reflected Estermann double
pole.  This minus sign propagates into the leading Laurent coefficient. -/
theorem normalizedAbelReflectionWeight_zero
    (x : ℝ) :
    bettinConreyNormalizedAbelReflectionWeight x 0 = -(x : ℂ)⁻¹ := by
  simp [bettinConreyNormalizedAbelReflectionWeight,
    rawAbelReflectionWeight_zero]

/-- The raw Gamma weight has residue `-1` at `s = 1`. -/
theorem rawAbelReflectionWeight_residue_one
    (x : ℝ) (hx : 0 < x) :
    Tendsto
      (fun s : ℂ => (s - 1) * bettinConreyRawAbelReflectionWeight x s)
      (𝓝[≠] (1 : ℂ)) (𝓝 (-1)) := by
  have hx0 : (x : ℂ) ≠ 0 := by
    exact_mod_cast hx.ne'
  have hsub : Tendsto (fun s : ℂ => 1 - s)
      (𝓝[≠] (1 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
    simpa using
      (((hasDerivAt_const (x := (1 : ℂ)) (c := (1 : ℂ))).sub
        (hasDerivAt_id (x := (1 : ℂ)))).tendsto_nhdsNE (by norm_num))
  have hgamma : Tendsto
      (fun s : ℂ => (1 - s) * Complex.Gamma (1 - s))
      (𝓝[≠] (1 : ℂ)) (𝓝 1) :=
    Complex.tendsto_self_mul_Gamma_nhds_zero.comp hsub
  have hpow : Tendsto (fun s : ℂ => (x : ℂ) ^ (s - 1))
      (𝓝[≠] (1 : ℂ)) (𝓝 1) := by
    have hcont : ContinuousAt (fun s : ℂ => (x : ℂ) ^ (s - 1)) 1 :=
      (continuousAt_const_cpow hx0).comp
        ((continuousAt_id.sub continuousAt_const))
    simpa using hcont.tendsto.mono_left inf_le_left
  have hproduct := hgamma.mul hpow
  apply (show Tendsto
      (fun s : ℂ => -(((1 - s) * Complex.Gamma (1 - s)) *
        (x : ℂ) ^ (s - 1)))
      (𝓝[≠] (1 : ℂ)) (𝓝 (-1)) by simpa using hproduct.neg).congr'
  filter_upwards with s
  unfold bettinConreyRawAbelReflectionWeight
  ring

/-- The negated reflected weight has exactly the unit residue expected by
the evaluation-contour interface. -/
theorem hasUnitResidueAtOne_normalizedAbelReflectionWeight
    (x : ℝ) (hx : 0 < x) :
    HasUnitResidueAtOne (bettinConreyNormalizedAbelReflectionWeight x) := by
  unfold HasUnitResidueAtOne bettinConreyNormalizedAbelReflectionWeight
  simpa only [mul_neg, neg_neg] using
    (rawAbelReflectionWeight_residue_one x hx).neg

/-- The normalized Estermann integrand is the negative of the raw reflected
Abel--Mellin integrand.  This is the global sign required when the contour is
reoriented after `u = 1 - s`. -/
theorem normalizedWeightedIntegrand_eq_neg_rawReflected
    (a q : ℕ) [NeZero q] (x : ℝ) (s : ℂ) :
    estermannWeightedIntegrand a q
        (bettinConreyNormalizedAbelReflectionWeight x) s =
      -(bettinConreyRawAbelReflectionWeight x s *
        estermannHurwitzContinuation a q (1 - s)) := by
  simp [estermannWeightedIntegrand,
    bettinConreyNormalizedAbelReflectionWeight]

/-- For a reduced numerator the leading double-pole coefficient is
`-1 / (x q)` in the unit-residue convention. -/
theorem normalizedWeightedDoublePoleCoefficient_eq
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q)
    (x : ℝ) :
    estermannWeightedDoublePoleCoefficient a q
        (bettinConreyNormalizedAbelReflectionWeight x) =
      -(x : ℂ)⁻¹ * (q : ℂ)⁻¹ := by
  rw [estermannWeightedDoublePoleCoefficient,
    normalizedAbelReflectionWeight_zero,
    estermannDoublePoleCoefficient_eq_inv_modulus a q hcop]

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelReflectionWeight
