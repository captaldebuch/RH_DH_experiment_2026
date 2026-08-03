import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZeta
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannAtZeroReduction

/-!
# Route B2: the classical Estermann Dirichlet series

This module constructs the genuine Dirichlet series

`D(s,a/q) = sum_{n >= 1} d(n) exp(2*pi*i*a*n/q) / n^s`

on its half-plane of absolute convergence.  The divisor coefficient is defined
as the Dirichlet convolution `1 * 1`; this makes convergence for `re s > 1` a
direct consequence of the already formalized zeta L-series product.

This file does not yet identify the series with its Hurwitz-zeta continuation
or with the formal special value used in the Route-B1 reduction.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannSeries

open Complex LSeries
open scoped BigOperators LSeries.notation

/-- The complex additive character `exp(2*pi*i*a*n/q)`. -/
noncomputable def estermannAdditivePhase (a q n : ℕ) : ℂ :=
  Complex.exp
    ((((2 * Real.pi * (a : ℝ) / (q : ℝ) * (n : ℝ) : ℝ) : ℂ) * Complex.I))

/-- Additive characters have unit norm. -/
@[simp] theorem norm_estermannAdditivePhase (a q n : ℕ) :
    ‖estermannAdditivePhase a q n‖ = 1 := by
  simp [estermannAdditivePhase, Complex.norm_exp]

/-- For a positive modulus, the explicit exponential is Mathlib's standard
additive character on `ZMod q`. -/
theorem estermannAdditivePhase_eq_stdAddChar (a q n : ℕ) [NeZero q] :
    estermannAdditivePhase a q n =
      ZMod.stdAddChar ((a * n : ℕ) : ZMod q) := by
  rw [ZMod.stdAddChar_apply]
  have h := ZMod.toCircle_intCast (N := q) ((a * n : ℕ) : ℤ)
  have h' : ((ZMod.toCircle ((a * n : ℕ) : ZMod q) : Circle) : ℂ) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a * n : ℂ) / (q : ℂ)) := by
    simpa using h
  rw [h']
  unfold estermannAdditivePhase
  congr 1
  push_cast
  field_simp

/-- The divisor-counting sequence, expressed canonically as `1 * 1`. -/
noncomputable def estermannDivisorCoeff : ℕ → ℂ :=
  (1 : ℕ → ℂ) ⍟ (1 : ℕ → ℂ)

/-- The convolution coefficient is the usual number of positive divisors. -/
theorem estermannDivisorCoeff_apply (n : ℕ) :
    estermannDivisorCoeff n = (n.divisors.card : ℂ) := by
  rw [estermannDivisorCoeff, LSeries.convolution_def]
  simp only [Pi.one_apply, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [← Nat.map_div_right_divisors, Finset.card_map]

/-- The coefficient of the classical Estermann Dirichlet series. -/
noncomputable def estermannCoeff (a q n : ℕ) : ℂ :=
  estermannDivisorCoeff n * estermannAdditivePhase a q n

/-- Twisting by the additive character does not change coefficient norms. -/
@[simp] theorem norm_estermannCoeff (a q n : ℕ) :
    ‖estermannCoeff a q n‖ = ‖estermannDivisorCoeff n‖ := by
  simp [estermannCoeff]

/-- The classical Estermann series on its Dirichlet-series half-plane.

As for every `LSeries`, the definition is a `tsum`; its mathematical series
interpretation is supplied below under `1 < re s`.
-/
noncomputable def estermannDirichletSeries (a q : ℕ) (s : ℂ) : ℂ :=
  LSeries (estermannCoeff a q) s

/-- The untwisted divisor L-series converges absolutely for `re s > 1`. -/
theorem estermannDivisorCoeff_summable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable estermannDivisorCoeff s := by
  exact (LSeriesSummable_one_iff.mpr hs).convolution
    (LSeriesSummable_one_iff.mpr hs)

/-- Absolute convergence of the classical Estermann series for `re s > 1`. -/
theorem estermannCoeff_summable (a q : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (estermannCoeff a q) s := by
  rw [LSeriesSummable, ← summable_norm_iff]
  have h := (estermannDivisorCoeff_summable hs)
  rw [LSeriesSummable, ← summable_norm_iff] at h
  exact h.congr fun n => by
    by_cases hn : n = 0 <;> simp [LSeries.term_def, hn]

/-- The defining Dirichlet series has the declared Estermann value on
`re s > 1`. -/
theorem estermannDirichletSeries_hasSum (a q : ℕ) {s : ℂ}
    (hs : 1 < s.re) :
    LSeriesHasSum (estermannCoeff a q) s
      (estermannDirichletSeries a q s) := by
  exact (estermannCoeff_summable a q hs).LSeriesHasSum

/-- Written without the `LSeriesHasSum` abbreviation, the defining series is
the sum of the expected nonzero-index terms. -/
theorem hasSum_estermannDirichletSeries (a q : ℕ) {s : ℂ}
    (hs : 1 < s.re) :
    HasSum (fun n : ℕ =>
      if n = 0 then 0 else estermannCoeff a q n / (n : ℂ) ^ s)
      (estermannDirichletSeries a q s) := by
  simpa [LSeriesHasSum, LSeries.term_def] using
    estermannDirichletSeries_hasSum a q hs

/-! ## Absolutely convergent double-series form -/

/-- The product-indexed term before residue-class decomposition. -/
noncomputable def estermannDoubleTerm
    (a q : ℕ) (s : ℂ) (p : ℕ × ℕ) : ℂ :=
  estermannAdditivePhase a q (p.1 * p.2) *
    LSeries.term (1 : ℕ → ℂ) s p.1 * LSeries.term (1 : ℕ → ℂ) s p.2

/-- The product-indexed Estermann series is absolutely summable on
`re s > 1`. -/
theorem estermannDoubleTerm_summable (a q : ℕ) {s : ℂ}
    (hs : 1 < s.re) :
    Summable (estermannDoubleTerm a q s) := by
  have hbase := summable_mul_of_summable_norm
    (LSeriesSummable_one_iff.mpr hs).norm
    (LSeriesSummable_one_iff.mpr hs).norm
  exact hbase.norm.of_norm_bounded fun p => by
    simp [estermannDoubleTerm]

/-- A coefficient term is the sum of the product-indexed terms in its
multiplication fiber. -/
theorem term_estermannCoeff_eq_fiberTsum
    (a q : ℕ) (s : ℂ) (n : ℕ) :
    LSeries.term (estermannCoeff a q) s n =
      ∑' (p : (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {n}),
        estermannDoubleTerm a q s p := by
  have hterm :
      LSeries.term (estermannCoeff a q) s n =
        estermannAdditivePhase a q n *
          LSeries.term estermannDivisorCoeff s n := by
    by_cases hn : n = 0
    · simp [hn]
    · simp [LSeries.term_of_ne_zero hn, estermannCoeff]
      ring
  rw [hterm, estermannDivisorCoeff, LSeries.term_convolution']
  rw [← tsum_mul_left]
  apply tsum_congr
  intro p
  have hp : p.val.1 * p.val.2 = n := by
    have hp' := p.property
    change p.val.1 * p.val.2 ∈ ({n} : Set ℕ) at hp'
    exact Set.mem_singleton_iff.mp hp'
  have hphase : estermannAdditivePhase a q n =
      estermannAdditivePhase a q (p.val.1 * p.val.2) := by
    rw [hp]
  unfold estermannDoubleTerm
  rw [hphase]
  ring

/-- On `re s > 1`, the single Estermann L-series equals its absolutely
convergent product-indexed double series. -/
theorem estermannDirichletSeries_eq_tsum_prod
    (a q : ℕ) {s : ℂ} (hs : 1 < s.re) :
    estermannDirichletSeries a q s =
      ∑' p : ℕ × ℕ, estermannDoubleTerm a q s p := by
  unfold estermannDirichletSeries LSeries
  have hfiber :=
    (estermannDoubleTerm_summable a q hs).hasSum.tsum_fiberwise
      (fun p : ℕ × ℕ => p.1 * p.2)
  apply HasSum.tsum_eq
  convert hfiber using 1
  ext n
  exact term_estermannCoeff_eq_fiberTsum a q s n

/-- At additive frequency zero the Estermann series is `zeta(s)^2`. -/
theorem estermannDirichletSeries_zero (q : ℕ) {s : ℂ}
    (hs : 1 < s.re) :
    estermannDirichletSeries 0 q s = riemannZeta s ^ 2 := by
  calc
    estermannDirichletSeries 0 q s = LSeries estermannDivisorCoeff s := by
      apply LSeries_congr
      intro n _
      simp [estermannCoeff, estermannAdditivePhase]
    _ = LSeries (1 : ℕ → ℂ) s * LSeries (1 : ℕ → ℂ) s :=
      LSeries_convolution'
        (LSeriesSummable_one_iff.mpr hs)
        (LSeriesSummable_one_iff.mpr hs)
    _ = riemannZeta s ^ 2 := by
      rw [LSeries_one_eq_riemannZeta hs]
      ring

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannSeries
