/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSInfiniteAbel
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# NB12g: the Estermann-compatible BBLS Abel regulator

The independent regulator from `NB12BBLSInfiniteAbel` assigns the pair
`(m, ell)` the weight `rho^m * sigma^ell`.  Its coefficient after grouping
by `n = m * ell` is therefore a genuine two-variable divisor polynomial; it
is not the classical Estermann coefficient `d(n)` times a function of `n`.

This file introduces the complementary product-frequency regulator

`tau^(m*ell)`.

It is absolutely summable for `|tau| < 1` and, after exact divisor
regrouping, its coefficient is precisely

`d(n) * tau^n`.

Thus `tau = exp(-x)` gives the classical exponentially damped Estermann
Lambert series.  This is the correct regularization for the later Mellin
transform and Estermann functional equation.  No functional equation,
contour shift, boundary passage `tau -> 1`, or signed H15 estimate is claimed
here.
-/

open scoped BigOperators Topology LSeries.notation
open Complex LSeries

namespace NBMellinTools.NB12

/-! ## Product-frequency Abel series -/

/-- A BBLS product term with damping depending only on the product
frequency `m*ell`. -/
noncomputable def bblsProductAbelTerm
    (tau : ℝ) (x : ℝ) (p : ℕ+ × ℕ+) : ℂ :=
  ((tau ^ ((p.1 : ℕ) * (p.2 : ℕ)) : ℝ) : ℂ) *
    (bblsAdditiveCharacter ((p.1 : ℕ) * (p.2 : ℕ)) x /
      (((((p.1 : ℕ) * (p.2 : ℕ)) : ℝ)) : ℂ))

/-- Pointwise geometric majorant for the product-frequency Abel term. -/
theorem norm_bblsProductAbelTerm_le
    (tau : ℝ) (x : ℝ) (p : ℕ+ × ℕ+) :
    ‖bblsProductAbelTerm tau x p‖ ≤
      |tau| ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by
  have hnNat : 1 ≤ (p.1 : ℕ) * (p.2 : ℕ) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero p.1.ne_zero p.2.ne_zero)
  have hnReal : (1 : ℝ) ≤ (p.1 : ℝ) * (p.2 : ℝ) := by
    exact_mod_cast hnNat
  have hdenom :
      ‖bblsAdditiveCharacter ((p.1 : ℕ) * (p.2 : ℕ)) x /
          (((((p.1 : ℕ) * (p.2 : ℕ)) : ℝ)) : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_bblsAdditiveCharacter]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    exact (div_le_one (by positivity)).mpr hnReal
  unfold bblsProductAbelTerm
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_pow]
  have hcoefficient : 0 ≤ |tau| ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by
    positivity
  calc
    |tau| ^ ((p.1 : ℕ) * (p.2 : ℕ)) *
        ‖bblsAdditiveCharacter ((p.1 : ℕ) * (p.2 : ℕ)) x /
          ↑((((p.1 : ℕ) * (p.2 : ℕ)) : ℝ))‖ ≤
        |tau| ^ ((p.1 : ℕ) * (p.2 : ℕ)) * 1 :=
      mul_le_mul_of_nonneg_left hdenom hcoefficient
    _ = |tau| ^ ((p.1 : ℕ) * (p.2 : ℕ)) := mul_one _

/-- The product-frequency majorant is summable in the open unit disc. -/
theorem summable_bblsProductAbelMajorant
    (tau : ℝ) (htau : |tau| < 1) :
    Summable (fun p : ℕ+ × ℕ+ =>
      |tau| ^ ((p.1 : ℕ) * (p.2 : ℕ))) := by
  have hnorm : ‖|tau|‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg tau)] using htau
  simpa using
    (summable_prod_mul_pow (k := 0) (r := |tau|) hnorm)

/-- Absolute summability of the product-frequency Abel BBLS series. -/
theorem summable_bblsProductAbelTerm
    (tau : ℝ) (x : ℝ) (htau : |tau| < 1) :
    Summable (bblsProductAbelTerm tau x) :=
  (summable_bblsProductAbelMajorant tau htau).of_norm_bounded
    (norm_bblsProductAbelTerm_le tau x)

/-- The infinite product-frequency Abel BBLS sum. -/
noncomputable def bblsProductAbelSum (tau : ℝ) (x : ℝ) : ℂ :=
  ∑' p : ℕ+ × ℕ+, bblsProductAbelTerm tau x p

/-! ## Exact divisor coefficient -/

/-- The product-frequency Abel weight on one divisor antidiagonal. -/
noncomputable def bblsProductAbelDivisorWeight
    (tau : ℝ) (n : ℕ+) : ℝ :=
  ∑ p : Nat.divisorsAntidiagonal (n : ℕ),
    tau ^ (p.1.1 * p.1.2)

/-- The divisor antidiagonal has the same cardinality as the positive
divisor finset. -/
theorem card_divisorsAntidiagonal_eq_card_divisors (n : ℕ+) :
    Fintype.card (Nat.divisorsAntidiagonal (n : ℕ)) =
      (n : ℕ).divisors.card := by
  have h := congrArg Finset.card
    (Nat.map_div_right_divisors (n := (n : ℕ)))
  simpa using h.symm

/-- Exact coefficient collapse: product-frequency damping preserves the
classical divisor coefficient. -/
theorem bblsProductAbelDivisorWeight_eq
    (tau : ℝ) (n : ℕ+) :
    bblsProductAbelDivisorWeight tau n =
      ((n : ℕ).divisors.card : ℝ) * tau ^ (n : ℕ) := by
  classical
  unfold bblsProductAbelDivisorWeight
  calc
    (∑ p : Nat.divisorsAntidiagonal (n : ℕ),
        tau ^ (p.1.1 * p.1.2)) =
        ∑ _p : Nat.divisorsAntidiagonal (n : ℕ),
          tau ^ (n : ℕ) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Nat.mem_divisorsAntidiagonal.mp p.property).1]
    _ = (Fintype.card (Nat.divisorsAntidiagonal (n : ℕ)) : ℝ) *
          tau ^ (n : ℕ) := by simp
    _ = ((n : ℕ).divisors.card : ℝ) * tau ^ (n : ℕ) := by
      rw [card_divisorsAntidiagonal_eq_card_divisors]

/-- Divisor-frequency term after product-frequency Abel regrouping. -/
noncomputable def bblsProductAbelDivisorTerm
    (tau : ℝ) (x : ℝ) (n : ℕ+) : ℂ :=
  (bblsProductAbelDivisorWeight tau n : ℂ) *
    (bblsAdditiveCharacter (n : ℕ) x / (((n : ℝ) : ℂ)))

/-- Exact product-to-divisor regrouping for the Estermann-compatible Abel
regulator. -/
theorem bblsProductAbelSum_eq_divisorSum
    (tau : ℝ) (x : ℝ) (htau : |tau| < 1) :
    bblsProductAbelSum tau x =
      ∑' n : ℕ+, bblsProductAbelDivisorTerm tau x n := by
  have hprod := summable_bblsProductAbelTerm tau x htau
  have hsigmaSum : Summable
      (fun z : Σ n : ℕ+, Nat.divisorsAntidiagonal (n : ℕ) =>
        bblsProductAbelTerm tau x (sigmaAntidiagonalEquivProd z)) :=
    sigmaAntidiagonalEquivProd.summable_iff.mpr hprod
  unfold bblsProductAbelSum
  rw [← sigmaAntidiagonalEquivProd.tsum_eq]
  rw [Summable.tsum_sigma hsigmaSum]
  apply tsum_congr
  intro n
  rw [tsum_fintype]
  unfold bblsProductAbelDivisorTerm bblsProductAbelDivisorWeight
  simp only [Complex.ofReal_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hproduct := (Nat.mem_divisorsAntidiagonal.mp p.property).1
  have hproductReal :
      ((p.1.1 : ℕ) : ℝ) * ((p.1.2 : ℕ) : ℝ) = ((n : ℕ) : ℝ) := by
    exact_mod_cast hproduct
  simp only [bblsProductAbelTerm, sigmaAntidiagonalEquivProd,
    divisorsAntidiagonalFactors, Equiv.coe_fn_mk, PNat.mk_coe]
  rw [hproduct, hproductReal]

/-- The regrouped divisor-frequency series is absolutely summable. -/
theorem summable_bblsProductAbelDivisorTerm
    (tau : ℝ) (x : ℝ) (htau : |tau| < 1) :
    Summable (bblsProductAbelDivisorTerm tau x) := by
  have hprod := summable_bblsProductAbelTerm tau x htau
  have hsigmaSum : Summable
      (fun z : Σ n : ℕ+, Nat.divisorsAntidiagonal (n : ℕ) =>
        bblsProductAbelTerm tau x (sigmaAntidiagonalEquivProd z)) :=
    sigmaAntidiagonalEquivProd.summable_iff.mpr hprod
  have houter : Summable (fun n : ℕ+ =>
      ∑' p : Nat.divisorsAntidiagonal (n : ℕ),
        bblsProductAbelTerm tau x
          (sigmaAntidiagonalEquivProd ⟨n, p⟩)) :=
    hsigmaSum.sigma
  apply houter.congr
  intro n
  rw [tsum_fintype]
  unfold bblsProductAbelDivisorTerm bblsProductAbelDivisorWeight
  simp only [Complex.ofReal_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hproduct := (Nat.mem_divisorsAntidiagonal.mp p.property).1
  have hproductReal :
      ((p.1.1 : ℕ) : ℝ) * ((p.1.2 : ℕ) : ℝ) = ((n : ℕ) : ℝ) := by
    exact_mod_cast hproduct
  simp only [bblsProductAbelTerm, sigmaAntidiagonalEquivProd,
    divisorsAntidiagonalFactors, Equiv.coe_fn_mk, PNat.mk_coe]
  rw [hproduct, hproductReal]

/-! ## Classical Estermann compatibility -/

/-- At a positive rational phase, the explicit BBLS exponential is
Mathlib's standard additive character on `ZMod q`. -/
theorem bblsAdditiveCharacter_rat_eq_stdAddChar
    (a q n : ℕ) [NeZero q] :
    bblsAdditiveCharacter n ((a : ℝ) / (q : ℝ)) =
      ZMod.stdAddChar ((a * n : ℕ) : ZMod q) := by
  rw [ZMod.stdAddChar_apply]
  have h := ZMod.toCircle_intCast (N := q) ((a * n : ℕ) : ℤ)
  have h' : ((ZMod.toCircle ((a * n : ℕ) : ZMod q) : Circle) : ℂ) =
      Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * (a * n : ℂ) / (q : ℂ)) := by
    simpa using h
  rw [h']
  unfold bblsAdditiveCharacter
  congr 1
  push_cast
  field_simp

/-- The classical divisor coefficient, canonically expressed as `1 * 1`. -/
noncomputable def bblsEstermannDivisorCoeff : ℕ → ℂ :=
  LSeries.convolution (1 : ℕ → ℂ) (1 : ℕ → ℂ)

/-- The convolution coefficient is the ordinary divisor count. -/
theorem bblsEstermannDivisorCoeff_apply (n : ℕ) :
    bblsEstermannDivisorCoeff n = (n.divisors.card : ℂ) := by
  rw [bblsEstermannDivisorCoeff, LSeries.convolution_def]
  simp only [Pi.one_apply, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [← Nat.map_div_right_divisors, Finset.card_map]

/-- The classical Estermann coefficient at a real additive phase. -/
noncomputable def bblsEstermannCoeff (x : ℝ) (n : ℕ) : ℂ :=
  bblsEstermannDivisorCoeff n * bblsAdditiveCharacter n x

/-- Twisting by the additive character preserves coefficient norms. -/
@[simp] theorem norm_bblsEstermannCoeff (x : ℝ) (n : ℕ) :
    ‖bblsEstermannCoeff x n‖ = ‖bblsEstermannDivisorCoeff n‖ := by
  simp [bblsEstermannCoeff]

/-- The classical Estermann Dirichlet series on its initial half-plane. -/
noncomputable def bblsEstermannDirichletSeries (x : ℝ) (s : ℂ) : ℂ :=
  LSeries (bblsEstermannCoeff x) s

/-- The untwisted divisor series is absolutely convergent for `Re s > 1`. -/
theorem bblsEstermannDivisorCoeff_summable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable bblsEstermannDivisorCoeff s := by
  exact (LSeriesSummable_one_iff.mpr hs).convolution
    (LSeriesSummable_one_iff.mpr hs)

/-- Absolute convergence of the classical Estermann series on `Re s > 1`. -/
theorem bblsEstermannCoeff_summable (x : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (bblsEstermannCoeff x) s := by
  rw [LSeriesSummable, ← summable_norm_iff]
  have h := bblsEstermannDivisorCoeff_summable hs
  rw [LSeriesSummable, ← summable_norm_iff] at h
  exact h.congr fun n => by
    by_cases hn : n = 0 <;> simp [LSeries.term_def, hn]

/-- The defining series has the declared Estermann value on `Re s > 1`. -/
theorem bblsEstermannDirichletSeries_hasSum
    (x : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (bblsEstermannCoeff x) s
      (bblsEstermannDirichletSeries x s) :=
  (bblsEstermannCoeff_summable x hs).LSeriesHasSum

/-- The product-frequency Abel divisor term is exactly the classical
Estermann coefficient at `s = 1`, multiplied by `tau^n`. -/
theorem bblsProductAbelDivisorTerm_eq_estermann
    (tau : ℝ) (x : ℝ) (n : ℕ+) :
    bblsProductAbelDivisorTerm tau x n =
      LSeries.term (bblsEstermannCoeff x) 1 (n : ℕ) *
        (tau ^ (n : ℕ) : ℝ) := by
  rw [bblsProductAbelDivisorTerm, bblsProductAbelDivisorWeight_eq]
  rw [LSeries.term_of_ne_zero n.ne_zero]
  simp [bblsEstermannCoeff, bblsEstermannDivisorCoeff_apply]
  ring

/-- For positive exponential damping, product-frequency Abel damping is
exactly `exp(-x*n)` after divisor regrouping. -/
theorem bblsProductAbelDivisorTerm_exp
    (damping phase : ℝ) (n : ℕ+) :
    bblsProductAbelDivisorTerm (Real.exp (-damping)) phase n =
      LSeries.term (bblsEstermannCoeff phase) 1 (n : ℕ) *
        Real.exp (-(damping * (n : ℕ))) := by
  rw [bblsProductAbelDivisorTerm_eq_estermann]
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  ring_nf

/-- Exact BBLS-to-Estermann Lambert-series bridge. -/
theorem bblsProductAbelSum_eq_estermannLambert
    (damping phase : ℝ) (hdamping : 0 < damping) :
    bblsProductAbelSum (Real.exp (-damping)) phase =
      ∑' n : ℕ+,
        LSeries.term (bblsEstermannCoeff phase) 1 (n : ℕ) *
          Real.exp (-(damping * (n : ℕ))) := by
  have htau : |Real.exp (-damping)| < 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos hdamping)
  rw [bblsProductAbelSum_eq_divisorSum _ _ htau]
  apply tsum_congr
  intro n
  exact bblsProductAbelDivisorTerm_exp damping phase n

/-! ## The independent regulator is genuinely different -/

/-- At product frequency `2`, equal independent dampers produce the weight
`2*r^3`, not the classical product-frequency weight `2*r^2`. -/
theorem bblsInfiniteAbelDivisorWeight_two (r : ℝ) :
    bblsInfiniteAbelDivisorWeight r r ⟨2, by norm_num⟩ = 2 * r ^ 3 := by
  change (∑ p : Nat.divisorsAntidiagonal 2,
    r ^ p.1.1 * r ^ p.1.2) = 2 * r ^ 3
  rw [show (∑ p : Nat.divisorsAntidiagonal 2,
        r ^ p.1.1 * r ^ p.1.2) =
      ∑ p ∈ Nat.divisorsAntidiagonal 2, r ^ p.1 * r ^ p.2 by
    exact (Nat.divisorsAntidiagonal 2).sum_attach
      (fun p : ℕ × ℕ => r ^ p.1 * r ^ p.2)]
  have htwo : Nat.divisorsAntidiagonal 2 = {(1, 2), (2, 1)} := by
    decide
  rw [htwo]
  norm_num
  ring

/-- A concrete certificate that the independent and product-frequency Abel
coefficients cannot be silently identified. -/
theorem independentAbel_not_productAbel_at_half_two :
    bblsInfiniteAbelDivisorWeight (1 / 2) (1 / 2) ⟨2, by norm_num⟩ ≠
      ((2 : ℕ).divisors.card : ℝ) * (1 / 2 : ℝ) ^ 2 := by
  rw [bblsInfiniteAbelDivisorWeight_two]
  have hcard : (2 : ℕ).divisors.card = 2 := by decide
  rw [hcard]
  norm_num

end NBMellinTools.NB12
