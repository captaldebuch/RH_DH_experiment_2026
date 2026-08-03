import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannFunctionalEquation

/-!
# Route B5: the exact analytic-to-Vasyunin special-value bridge

Mathlib's `HurwitzZetaValues` explicitly records the `s = 0` Hurwitz formula
as a remaining TODO because its present method would require a conditionally
convergent Fourier series.  This module therefore isolates two precise,
independent special-value inputs:

1. the periodic Hurwitz value `zeta(0,x) = 1/2 - x`, with the separate
   Riemann-zeta value at the zero residue;
2. the finite Bernoulli/additive-character sum evaluation as the Vasyunin
   cotangent sum, with the required inverse residue made explicit.

Given those two inputs, the genuine analytic Estermann continuation inhabits
the already-used `EstermannAtZeroPackage`.  No analytic or arithmetic gap is
hidden in that conversion.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannAtZeroBridge

open Complex HurwitzZeta ZMod
open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannAtZeroReduction
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannFunctionalEquation
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannHurwitz
open RH.Criteria.NymanBeurling.BCFLogTaperSpectral
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.VasyuninGram

/-- The first periodic Bernoulli function in the convention matching the
Hurwitz zeta continuation.  At the zero residue this uses `zeta(0)=-1/2`. -/
noncomputable def periodicBernoulliOneValue
    {q : ℕ} [NeZero q] (j : ZMod q) : ℂ :=
  if j = 0 then -(1 : ℂ) / 2
  else (1 : ℂ) / 2 - (j.val : ℂ) / (q : ℂ)

/-- Exact missing Mathlib endpoint theorem for Hurwitz zeta at zero. -/
structure HurwitzZetaZeroFormula where
  value_eq : ∀ {q : ℕ} [NeZero q] (j : ZMod q),
    HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) 0 =
      periodicBernoulliOneValue j

/-- The zero residue is already covered by Mathlib's value
`riemannZeta 0 = -1/2`; it is not part of the missing endpoint analysis. -/
theorem hurwitzZeta_zero_at_zero_residue
    (q : ℕ) [NeZero q] :
    HurwitzZeta.hurwitzZeta
        (ZMod.toAddCircle (0 : ZMod q)) 0 =
      periodicBernoulliOneValue (0 : ZMod q) := by
  simp [periodicBernoulliOneValue, HurwitzZeta.hurwitzZeta_zero,
    riemannZeta_zero]

/-- The genuinely missing part of the endpoint formula: nonzero residue
classes only. -/
structure HurwitzZetaZeroNonzeroFormula where
  value_eq : ∀ {q : ℕ} [NeZero q] (j : ZMod q), j ≠ 0 →
    HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) 0 =
      periodicBernoulliOneValue j

/-- The exact conditionally convergent Fourier endpoint needed for rational
points.  This is the `k = 0` case deliberately excluded from Mathlib's
`sinZeta_two_mul_nat_add_one`: equivalently,

`sum_{n >= 1} sin(2*pi*n*j/q)/n = pi*(1/2-j/q)`.

Keeping this statement separate makes the remaining harmonic-analysis task
reusable outside the Estermann development. -/
structure RationalSineZetaOneFormula where
  value_eq : ∀ {q : ℕ} [NeZero q] (j : ZMod q), j ≠ 0 →
    HurwitzZeta.sinZeta (ZMod.toAddCircle j) 1 =
      (Real.pi : ℂ) * ((1 : ℂ) / 2 - (j.val : ℂ) / (q : ℂ))

/-- The rational sine-series endpoint implies the missing nonzero Hurwitz
value.  The even Hurwitz part vanishes away from the zero residue, while its
odd part at zero is `sinZeta(1)/pi` by the functional equation. -/
def hurwitzZetaZeroNonzeroFormula_of_rationalSineZetaOne
    (H : RationalSineZetaOneFormula) : HurwitzZetaZeroNonzeroFormula where
  value_eq := by
    intro q _ j hj
    rw [HurwitzZeta.hurwitzZeta]
    rw [HurwitzZeta.hurwitzZetaEven_apply_zero,
      if_neg (ZMod.toAddCircle_eq_zero.not.mpr hj), zero_add]
    have hs : ∀ n : ℕ, (1 : ℂ) ≠ -n := by
      intro n hn
      have := congrArg Complex.re hn
      norm_num at this
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hodd := HurwitzZeta.hurwitzZetaOdd_one_sub
      (ZMod.toAddCircle j) hs
    norm_num [Complex.cpow_neg] at hodd
    rw [hodd, H.value_eq j hj]
    simp only [periodicBernoulliOneValue, if_neg hj]
    have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp

/-- The nonzero-residue endpoint formula plus Mathlib's Riemann-zeta value
give the complete periodic endpoint package. -/
def HurwitzZetaZeroNonzeroFormula.toZeroFormula
    (H : HurwitzZetaZeroNonzeroFormula) : HurwitzZetaZeroFormula where
  value_eq := by
    intro q _ j
    by_cases hj : j = 0
    · subst j
      exact hurwitzZeta_zero_at_zero_residue q
    · exact H.value_eq j hj

/-- The finite Bernoulli/additive-character value obtained after substituting
the Hurwitz zero formula into the double continuation. -/
noncomputable def estermannBernoulliFiniteValue
    (a q : ℕ) [NeZero q] : ℂ :=
  ∑ j : ZMod q,
    (∑ k : ZMod q,
      estermannResiduePhase a j k * periodicBernoulliOneValue k) *
      periodicBernoulliOneValue j

/-- The representative of the inverse of `a` modulo `q`.  For a reduced
fraction this is the unique residue `aInv` satisfying `a * aInv = 1` in
`ZMod q`.  The inverse is essential: with the project's convention

`V(a,q) = sum_j {ja/q} cot(pi*j/q)`,

the classical relation is `c₀(a/q) = -V(a⁻¹,q)`.  Consequently the analytic
Estermann value which represents `V(a,q)` is `D(0,a⁻¹/q)`, not `D(0,a/q)`. -/
noncomputable def inverseResidue (a q : ℕ) [NeZero q] : ℕ :=
  ((a : ZMod q)⁻¹).val

/-- For a reduced fraction, `inverseResidue` is genuinely inverse modulo the
denominator. -/
theorem inverseResidue_mul_mod_eq_one
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q) :
    ((inverseResidue a q * a : ℕ) : ZMod q) = 1 := by
  simpa [inverseResidue] using ZMod.val_inv_mul hcop

/-- The Bernoulli value at the inverse additive frequency. -/
noncomputable def inverseEstermannBernoulliFiniteValue
    (a q : ℕ) [NeZero q] : ℂ :=
  estermannBernoulliFiniteValue (inverseResidue a q) q

/-- The Hurwitz endpoint formula reduces the analytic value at zero to a
completely finite Bernoulli sum. -/
theorem estermannHurwitzContinuation_zero_eq_bernoulliFinite
    (H : HurwitzZetaZeroFormula) (a q : ℕ) [NeZero q] :
    estermannHurwitzContinuation a q 0 =
      estermannBernoulliFiniteValue a q := by
  rw [estermannHurwitzContinuation_eq_finiteSum]
  unfold estermannHurwitzFiniteSum estermannBernoulliFiniteValue
  simp only [neg_zero, cpow_zero, one_mul]
  simp_rw [H.value_eq]

/-- The remaining finite Fourier/cotangent calculation in the normalization
used by the H15 Vasyunin kernel.  This contains no analytic continuation:
both sides are explicit finite expressions.  Notice the inverse residue on
the left; omitting it gives a false statement for general reduced fractions
(already at `a/q = 2/7`). -/
structure EstermannBernoulliCotangentIdentity where
  value_eq : ∀ (a q : ℕ) (_ : 0 < a) (hq : 0 < q), Nat.Coprime a q →
    @inverseEstermannBernoulliFiniteValue a q
        (show NeZero q from ⟨Nat.ne_of_gt hq⟩) =
      (1 / 4 : ℂ) - Complex.I / 2 * (cotangentSumVFormula a q : ℂ)

/-- The analytic continuation evaluated at zero, extended harmlessly by zero
at the invalid modulus `q = 0`. -/
noncomputable def analyticEstermannAtZeroValue (a q : ℕ) : ℂ :=
  if hq : q = 0 then 0
  else @estermannHurwitzContinuation
    (@inverseResidue a q ⟨hq⟩) q ⟨hq⟩ 0

/-- At every positive modulus, the preceding total definition is the genuine
Hurwitz-continuation value. -/
theorem analyticEstermannAtZeroValue_eq
    (a q : ℕ) (hq : 0 < q) :
    analyticEstermannAtZeroValue a q =
      @estermannHurwitzContinuation
        (@inverseResidue a q ⟨Nat.ne_of_gt hq⟩) q
          ⟨Nat.ne_of_gt hq⟩ 0 := by
  simp [analyticEstermannAtZeroValue, Nat.ne_of_gt hq]

/-- The two exact endpoint inputs identify the genuine analytic continuation
with the Vasyunin normalization used by Route B1. -/
noncomputable def analyticEstermannAtZeroPackage
    (HZ : HurwitzZetaZeroFormula)
    (HC : EstermannBernoulliCotangentIdentity) :
    EstermannAtZeroPackage where
  value := analyticEstermannAtZeroValue
  value_eq_vasyunin := by
    intro a q ha hq hcop
    rw [analyticEstermannAtZeroValue_eq a q hq]
    letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
    rw [estermannHurwitzContinuation_zero_eq_bernoulliFinite HZ]
    change inverseEstermannBernoulliFiniteValue a q = _
    exact HC.value_eq a q ha hq hcop

/-- With the endpoint formulas supplied, the complete coupled H15 expression
is exactly the one formed from genuine analytic Estermann values. -/
theorem coupledGcdRatioExpression_eq_analyticEstermann
    (HZ : HurwitzZetaZeroFormula)
    (HC : EstermannBernoulliCotangentIdentity) (N : ℕ) :
    coupledGcdRatioExpression N =
      estermannCoupledExpression
        (analyticEstermannAtZeroPackage HZ HC) N :=
  coupledGcdRatioExpression_eq_estermannCoupledExpression
    (analyticEstermannAtZeroPackage HZ HC) N

/-- The exact signed automorphic estimate, once proved for the genuine
analytic Estermann package, supplies spectral vanishing.  This theorem is the
honest endpoint of the Route-B formal reduction. -/
noncomputable def spectralVanishingEstimate_of_analyticEstermannCancellation
    (HZ : HurwitzZetaZeroFormula)
    (HC : EstermannBernoulliCotangentIdentity)
    (E : EstermannCoupledCancellationEstimate
      (analyticEstermannAtZeroPackage HZ HC)) :
    SpectralVanishingEstimate :=
  spectralVanishingEstimate_of_coupledLogTaperCancellation
    (E.toCoupledLogTaper (analyticEstermannAtZeroPackage HZ HC))

/-- The same signed analytic estimate closes the Báez--Duarte criterion. -/
theorem baezDuarteCriterion_of_analyticEstermannCancellation
    (HZ : HurwitzZetaZeroFormula)
    (HC : EstermannBernoulliCotangentIdentity)
    (E : EstermannCoupledCancellationEstimate
      (analyticEstermannAtZeroPackage HZ HC)) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_spectralVanishing
    (spectralVanishingEstimate_of_analyticEstermannCancellation HZ HC E)

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannAtZeroBridge
