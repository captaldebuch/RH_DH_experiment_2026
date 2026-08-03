import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannContourShift

/-!
# Route B7.1: Bettin--Conrey reciprocity normalization at `a = 0`

Bettin--Conrey's master reciprocity contains the correction

`a * k ^ a * ζ (1 - a) / (π * h)`.

The factor `a` cancels the pole of `ζ(1-a)`, leaving the nonzero Vasyunin
limit `-1 / (π h)`.  This file proves that normalization from Mathlib's
residue theorem.  It also records the Laurent finite part of the *unscaled*
meromorphic quotient as an auxiliary theorem, but that quotient is not the
correction displayed in the reciprocity formula.

This is a local normalization theorem, not the signed cross-modulus estimate.
It explains why the reciprocity correction has to remain coupled to the
cotangent/period-function terms when Route B is specialized to H15.

References:

* S. Bettin and B. Conrey, *Period functions and cotangent sums*,
  Algebra & Number Theory 7 (2013), Theorem 4.
* J. S. Auli, A. Bayad, M. Beck, *Reciprocity Theorems for Bettin--Conrey
  Sums*, Theorem 1.1, arXiv:1601.06839.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperBettinConreyReciprocity

open Complex Filter Topology

/-- The unscaled meromorphic quotient underlying the correction.  It has a
simple pole at `a = 0`, but is not by itself the term displayed in the
Bettin--Conrey reciprocity formula. -/
noncomputable def bettinConreyMeromorphicCorrection
    (a : ℂ) (h k : ℕ) : ℂ :=
  (k : ℂ) ^ a * riemannZeta (1 - a) /
    ((Real.pi : ℂ) * (h : ℂ))

/-- The literal correction displayed in Bettin--Conrey Theorem 4. -/
noncomputable def bettinConreyCorrection
    (a : ℂ) (h k : ℕ) : ℂ :=
  a * bettinConreyMeromorphicCorrection a h k

/-- The source correction is exactly `a` times the unscaled meromorphic
quotient. -/
theorem bettinConreyCorrection_eq_mul_meromorphic
    (a : ℂ) (h k : ℕ) :
    bettinConreyCorrection a h k =
      a * bettinConreyMeromorphicCorrection a h k :=
  rfl

/-- The exact positive-rational normalization of Bettin--Conrey's master
reciprocity.  This is a proposition-valued interface, not an assertion that
the paper's analytic construction has already been formalized.  In
particular, no inhabitant is declared here.

The negative reciprocal in the second cotangent sum, its exponent `1 + a`,
and the leading factor `a` in `bettinConreyCorrection` are intentionally
visible so that later Route-B code cannot silently change conventions. -/
def MasterReciprocityStatement
    (cotangentSum : ℂ → ℝ → ℂ) (periodFunction : ℂ → ℂ → ℂ) : Prop :=
  ∀ (a : ℂ) (h k : ℕ), a ≠ 0 → 0 < h → 0 < k → Nat.Coprime h k →
    cotangentSum a ((h : ℝ) / (k : ℝ)) -
        (((k : ℂ) / (h : ℂ)) ^ (1 + a)) *
          cotangentSum a (-((k : ℝ) / (h : ℝ))) +
        bettinConreyCorrection a h k =
      -I * riemannZeta (-a) *
        periodFunction a (((h : ℝ) / (k : ℝ) : ℝ) : ℂ)

/-- Data needed to instantiate the local Bettin--Conrey identity inside a
future cotangent/automorphic formalization.  This does not include, and cannot
replace, the global signed Möbius cross-modulus estimate. -/
structure MasterReciprocityPackage where
  cotangentSum : ℂ → ℝ → ℂ
  periodFunction : ℂ → ℂ → ℂ
  reciprocity : MasterReciprocityStatement cotangentSum periodFunction

/-- The affine involution `a ↦ 1 - a` sends the punctured neighborhood of
zero to the punctured neighborhood of one. -/
theorem tendsto_one_sub_punctured_zero :
    Tendsto (fun a : ℂ => 1 - a) (𝓝[≠] 0) (𝓝[≠] 1) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hcontinuous : ContinuousAt (fun a : ℂ => 1 - a) 0 := by
      fun_prop
    have hle : 𝓝[≠] (0 : ℂ) ≤ 𝓝 0 := inf_le_left
    simpa using hcontinuous.tendsto.mono_left hle
  · filter_upwards [eventually_mem_nhdsWithin] with a ha
    simpa using ha

/-- The pole of `ζ` at one exactly cancels the factor `a`, with the minus
sign forced by the change of variables `s = 1 - a`. -/
theorem tendsto_mul_riemannZeta_one_sub :
    Tendsto (fun a : ℂ => a * riemannZeta (1 - a))
      (𝓝[≠] 0) (𝓝 (-1)) := by
  have hz := riemannZeta_residue_one.comp tendsto_one_sub_punctured_zero
  convert hz.neg using 1
  · funext a
    simp only [Function.comp_apply]
    ring

/-- For positive integer parameters, the complete source correction has the
nonzero Vasyunin limit `-1 / (π h)`. -/
theorem tendsto_bettinConreyCorrection_zero
    (h k : ℕ) (_hh : 0 < h) (hk : 0 < k) :
    Tendsto (fun a : ℂ => bettinConreyCorrection a h k)
      (𝓝[≠] 0) (𝓝 (-1 / ((Real.pi : ℂ) * (h : ℂ)))) := by
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hpow : Tendsto (fun a : ℂ => (k : ℂ) ^ a)
      (𝓝[≠] 0) (𝓝 1) := by
    have hcontinuous : ContinuousAt (fun a : ℂ => (k : ℂ) ^ a) 0 :=
      continuousAt_const_cpow hk0
    simpa using hcontinuous.tendsto.mono_left inf_le_left
  have hprod := hpow.mul tendsto_mul_riemannZeta_one_sub
  convert hprod.div_const ((Real.pi : ℂ) * (h : ℂ)) using 1
  · funext a
    simp only [bettinConreyCorrection,
      bettinConreyMeromorphicCorrection]
    ring
  · simp

/-- After the pole `-1 / (π h a)` is subtracted, the *unscaled* quotient has
finite part `(γ - log k) / (π h)`.  This auxiliary Laurent coefficient must
not be substituted for the central value of the scaled source correction. -/
theorem tendsto_bettinConreyMeromorphicCorrection_finitePart
    (h k : ℕ) (_hh : 0 < h) (hk : 0 < k) :
    Tendsto
      (fun a : ℂ =>
        bettinConreyMeromorphicCorrection a h k +
          1 / (((Real.pi : ℂ) * (h : ℂ)) * a))
      (𝓝[≠] 0)
      (𝓝 (((Real.eulerMascheroniConstant : ℂ) -
          Complex.log (k : ℂ)) /
        ((Real.pi : ℂ) * (h : ℂ)))) := by
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hpow : Tendsto (fun a : ℂ => (k : ℂ) ^ a)
      (𝓝[≠] 0) (𝓝 1) := by
    have hcontinuous : ContinuousAt (fun a : ℂ => (k : ℂ) ^ a) 0 :=
      continuousAt_const_cpow hk0
    simpa using hcontinuous.tendsto.mono_left inf_le_left
  have hzeta : Tendsto
      (fun a : ℂ => riemannZeta (1 - a) + 1 / a)
      (𝓝[≠] 0) (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
    have hz := tendsto_riemannZeta_sub_one_div.comp
      tendsto_one_sub_punctured_zero
    convert hz using 1
    funext a
    simp only [Function.comp_apply]
    congr 1
    field_simp
    ring
  have hderiv : HasDerivAt (fun a : ℂ => (k : ℂ) ^ a)
      (Complex.log (k : ℂ)) 0 := by
    convert (hasDerivAt_id (𝕜 := ℂ) (0 : ℂ)).const_cpow (c := (k : ℂ))
      (Or.inl hk0) using 1 <;> simp
  have hslope : Tendsto
      (fun a : ℂ => (1 - (k : ℂ) ^ a) / a)
      (𝓝[≠] 0) (𝓝 (-Complex.log (k : ℂ))) := by
    have hs := hderiv.tendsto_slope.neg
    convert hs using 1
    funext a
    rw [slope_def_field]
    simp
    ring
  have hnumerator := (hpow.mul hzeta).add hslope
  have hrewrite :
      (fun a : ℂ =>
        bettinConreyMeromorphicCorrection a h k +
          1 / (((Real.pi : ℂ) * (h : ℂ)) * a)) =
        fun a : ℂ =>
          ((k : ℂ) ^ a * (riemannZeta (1 - a) + 1 / a) +
              (1 - (k : ℂ) ^ a) / a) /
            ((Real.pi : ℂ) * (h : ℂ)) := by
    funext a
    unfold bettinConreyMeromorphicCorrection
    ring
  rw [hrewrite]
  convert hnumerator.div_const ((Real.pi : ℂ) * (h : ℂ)) using 1 <;> ring

end RH.Criteria.NymanBeurling.BCFLogTaperBettinConreyReciprocity
