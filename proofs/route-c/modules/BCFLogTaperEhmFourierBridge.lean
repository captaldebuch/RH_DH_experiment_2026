import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmPeriodicL2
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmIntegralSeriesAssembly
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Fourier bridge for Ehm's centered sawtooth

This module proves the one-period Fourier calculation underlying Ehm's
Proposition 5.1 and records the correct polarized Parseval identity for two
`L²` functions on the circle.

The result deliberately does not identify the separately defined Gram
autocorrelation with `∑ k, R₁(kx)`.  That is the remaining global value
identity, not a definition that may be substituted into Parseval.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmFourierBridge

open MeasureTheory Real Set AddCircle Filter
open scoped BigOperators ENNReal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmIntegralSeriesAssembly
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPeriodicL2

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- A circle representative of the centered fractional part.  Its value at
the endpoint is immaterial in `L²`; the interval coefficient theorem below
uses the precise `Ioc` convention. -/
noncomputable def ehmCenteredSawtoothCircle : AddCircle (1 : ℝ) → ℂ :=
  AddCircle.liftIoc (p := (1 : ℝ)) 0
    (fun x : ℝ => ((Int.fract x - (1 / 2 : ℝ) : ℝ) : ℂ))

/-- On one fundamental interval, the centered fractional part agrees almost
everywhere with the affine function `x - 1/2`. -/
theorem ehmCenteredSawtooth_ae_eq_linear :
    (fun x : ℝ => ((Int.fract x - (1 / 2 : ℝ) : ℝ) : ℂ))
      =ᵐ[volume.restrict (Ioc 0 1)]
      (fun x : ℝ => ((x - (1 / 2 : ℝ) : ℝ) : ℂ)) := by
  change ∀ᵐ (x : ℝ) ∂volume.restrict (Ioc 0 1),
    ((Int.fract x - (1 / 2 : ℝ) : ℝ) : ℂ) =
      ((x - (1 / 2 : ℝ) : ℝ) : ℂ)
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [show ∀ᵐ x : ℝ, x ≠ 1 by
    simp [ae_iff, measure_singleton]] with x hx
  intro hmem
  have hxlt : x < 1 := lt_of_le_of_ne hmem.2 hx
  rw [Int.fract_eq_self.mpr ⟨hmem.1.le, hxlt⟩]

private theorem linear_fourierCoeffOn_nonzero (m : ℤ) (hm : m ≠ 0) :
    fourierCoeffOn (show (0 : ℝ) < 1 by norm_num)
      (fun x : ℝ => ((x - (1 / 2 : ℝ) : ℝ) : ℂ)) m =
      Complex.I / (2 * Real.pi * (m : ℂ)) := by
  have hconst : fourierCoeffOn (show (0 : ℝ) < 1 by norm_num)
      (fun _ : ℝ => (1 : ℂ)) m = 0 := by
    letI : Fact (0 < (1 : ℝ) - 0) := ⟨by norm_num⟩
    unfold fourierCoeffOn
    have heq : AddCircle.liftIoc (p := ((1 : ℝ) - 0)) 0
        (fun _ : ℝ => (1 : ℂ)) =
        fun _ : AddCircle ((1 : ℝ) - 0) => 1 := by rfl
    rw [heq, show (fun _ : AddCircle ((1 : ℝ) - 0) => (1 : ℂ)) = fourier 0 by
      funext x
      simp]
    rw [fourierCoeff_fourier]
    simp [hm]
  rw [fourierCoeffOn_of_hasDerivAt (by norm_num) hm
    (f' := fun _ => 1)]
  · rw [hconst]
    simp
    field_simp [Real.pi_ne_zero, hm]
  · intro x hx
    simpa using ((hasDerivAt_id (x : ℂ)).comp_ofReal.sub_const (1 / 2 : ℂ))
  · exact intervalIntegrable_const

private theorem linear_fourierCoeffOn_zero :
    fourierCoeffOn (show (0 : ℝ) < 1 by norm_num)
      (fun x : ℝ => ((x - (1 / 2 : ℝ) : ℝ) : ℂ)) 0 = 0 := by
  rw [fourierCoeffOn_eq_integral]
  norm_num
  have hreal : (∫ x : ℝ in 0..1, x - (1 / 2 : ℝ)) = 0 := by
    calc
      (∫ x : ℝ in 0..1, x - (1 / 2 : ℝ)) =
          (∫ x : ℝ in 0..1, x) -
            (∫ _x : ℝ in 0..1, (1 / 2 : ℝ)) := by
        exact intervalIntegral.integral_sub
          (continuous_id.intervalIntegrable 0 1)
          (continuous_const.intervalIntegrable 0 1)
      _ = 0 := by norm_num [integral_id]
  have hcomplex := congrArg Complex.ofReal hreal
  rw [← intervalIntegral.integral_ofReal] at hcomplex
  simpa using hcomplex

/-- Exact Fourier coefficient of the centered sawtooth on `[0,1]`.  The
zero mode vanishes, and each nonzero mode has the standard `I/(2πm)`
normalization. -/
theorem ehmCenteredSawtooth_fourierCoeffOn (m : ℤ) :
    fourierCoeffOn (show (0 : ℝ) < 1 by norm_num)
      (fun x : ℝ => ((Int.fract x - (1 / 2 : ℝ) : ℝ) : ℂ)) m =
      if m = 0 then 0 else Complex.I / (2 * Real.pi * (m : ℂ)) := by
  have hcongr := congrFun
    (fourierCoeffOn_congr_ae (by norm_num)
      ehmCenteredSawtooth_ae_eq_linear) m
  rcases eq_or_ne m 0 with rfl | hm
  · simpa using hcongr.trans linear_fourierCoeffOn_zero
  · rw [if_neg hm]
    exact hcongr.trans (linear_fourierCoeffOn_nonzero m hm)

/-! ## The concrete finite `φ₁` functions in `L²` -/

/-- The finite Ehm series, bundled as a function on the unit circle. -/
noncomputable def ehmPhi1PartialCircle (K : ℕ) : AddCircle (1 : ℝ) → ℂ :=
  AddCircle.liftIoc (p := (1 : ℝ)) 0
    (fun x : ℝ => (ehmPhi1Partial K x : ℂ))

private theorem ehmPhi1Partial_memLp_Ioc (K : ℕ) :
    MemLp (fun x : ℝ => (ehmPhi1Partial K x : ℂ)) 2
      (volume.restrict (Ioc 0 1)) := by
  have hmeas : Measurable (fun x : ℝ => (ehmPhi1Partial K x : ℂ)) := by
    unfold ehmPhi1Partial ehmCenteredFractionalPart
    fun_prop
  apply MemLp.of_bound hmeas.aestronglyMeasurable (K : ℝ)
  filter_upwards with x
  rw [Complex.norm_real]
  unfold ehmPhi1Partial
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    (∑ k ∈ Finset.Icc 1 K,
        |ehmCenteredFractionalPart ((k : ℝ) * x) / (k : ℝ)|) ≤
        ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkpos : 0 < k :=
        lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hk).1
      have hkRpos : (0 : ℝ) < k := by exact_mod_cast hkpos
      have hkRone : (1 : ℝ) ≤ k := by
        exact_mod_cast (Finset.mem_Icc.mp hk).1
      have hc : |ehmCenteredFractionalPart ((k : ℝ) * x)| ≤ 1 := by
        rw [abs_le]
        unfold ehmCenteredFractionalPart
        constructor <;>
          linarith [Int.fract_nonneg ((k : ℝ) * x),
            (Int.fract_lt_one ((k : ℝ) * x)).le]
      rw [abs_div]
      have hkabs : |(k : ℝ)| = (k : ℝ) := abs_of_pos hkRpos
      rw [hkabs]
      exact (div_le_one (by positivity)).mpr
        (hc.trans hkRone)
    _ = K := by simp

theorem ehmPhi1PartialCircle_memLp (K : ℕ) :
    MemLp (ehmPhi1PartialCircle K) 2
      (@AddCircle.haarAddCircle (1 : ℝ) inferInstance) := by
  have hIoc : MemLp (fun x : ℝ => (ehmPhi1Partial K x : ℂ)) 2
      (volume.restrict (Ioc 0 (0 + (1 : ℝ)))) := by
    simpa only [zero_add] using ehmPhi1Partial_memLp_Ioc K
  exact hIoc.memLp_liftIoc.haarAddCircle

/-- The concrete `K`-th Ehm partial sum as an element of circle `L²`. -/
noncomputable def ehmPhi1PartialL2 (K : ℕ) :
    Lp ℂ 2 (@AddCircle.haarAddCircle (1 : ℝ) inferInstance) :=
  (ehmPhi1PartialCircle_memLp K).toLp (ehmPhi1PartialCircle K)

/-- The remaining Fourier-convergence target after the coefficient and
square-summability theorems.  Its field is intentionally not asserted here:
it must be proved by collecting the dilated sawtooth coefficients and
passing to the `L²` limit. -/
structure EhmPhi1L2Convergence where
  tendsto_periodic :
    Tendsto ehmPhi1PartialL2 atTop (nhds periodicEhmKernelL2)

/-- Polarized Parseval on the unit circle.  This is the precise replacement
for an unqualified formula `∫ f*g = ∑ f̂*ĝ`: the Hilbert-space inner
product fixes the required conjugation convention. -/
theorem weightedIntegralAutocorrelation
    (f g : Lp ℂ 2 (@AddCircle.haarAddCircle 1 inferInstance)) :
    (∫ t : AddCircle (1 : ℝ),
        inner ℂ (f t) (g t) ∂AddCircle.haarAddCircle) =
      ∑' k : ℤ, inner ℂ (fourierCoeff f k) (fourierCoeff g k) := by
  rw [← MeasureTheory.L2.inner_def]
  calc
    inner ℂ f g = inner ℂ ((@fourierBasis 1 inferInstance).repr f)
        ((@fourierBasis 1 inferInstance).repr g) :=
      ((@fourierBasis 1 inferInstance).repr.inner_map_map f g).symm
    _ = ∑' k : ℤ,
        inner ℂ ((@fourierBasis 1 inferInstance).repr f k)
          ((@fourierBasis 1 inferInstance).repr g k) := lp.inner_eq_tsum _ _
    _ = _ := by
      apply tsum_congr
      intro k
      rw [fourierBasis_repr, fourierBasis_repr]

end RH.Criteria.NymanBeurling.BCFLogTaperEhmFourierBridge
