/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSAbelRegularization
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# NB12f: infinite double-Abel BBLS expansion

This file passes from the finite double-Abel regularization to an infinite
series in the open bidisc `|rho| < 1`, `|sigma| < 1`.  Positive frequencies
are indexed by `PNat`, so the product frequency is never zero.

The main results are:

* absolute summability of the double product series;
* a uniform geometric majorant on every closed sub-bidisc;
* exact regrouping by the product frequency through the divisor
  antidiagonal;
* summability of the resulting divisor-frequency series.

No boundary passage to `(1,1)`, integral exchange, Estermann functional
equation, or signed asymptotic estimate is asserted here.
-/

open scoped BigOperators Topology
open MeasureTheory

namespace NBMellinTools.NB12

/-! ## Positive-frequency product series -/

/-- A term of the infinite double-Abel BBLS product series. -/
noncomputable def bblsInfiniteAbelProductTerm
    (rho sigma : ℝ) (x : ℝ) (p : ℕ+ × ℕ+) : ℂ :=
  ((rho ^ (p.1 : ℕ) * sigma ^ (p.2 : ℕ) : ℝ) : ℂ) *
    (bblsAdditiveCharacter ((p.1 : ℕ) * (p.2 : ℕ)) x /
      (((((p.1 : ℕ) * (p.2 : ℕ)) : ℝ)) : ℂ))

/-- The additive character has unit norm. -/
@[simp] theorem norm_bblsAdditiveCharacter (n : ℕ) (x : ℝ) :
    ‖bblsAdditiveCharacter n x‖ = 1 := by
  unfold bblsAdditiveCharacter
  simpa using
    (Complex.norm_exp_ofReal_mul_I
      (2 * Real.pi * (n : ℝ) * x))

/-- Pointwise geometric majorant for the infinite double-Abel term. -/
theorem norm_bblsInfiniteAbelProductTerm_le
    (rho sigma : ℝ) (x : ℝ) (p : ℕ+ × ℕ+) :
    ‖bblsInfiniteAbelProductTerm rho sigma x p‖ ≤
      |rho| ^ (p.1 : ℕ) * |sigma| ^ (p.2 : ℕ) := by
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
  unfold bblsInfiniteAbelProductTerm
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow, abs_pow]
  have hcoefficient :
      0 ≤ |rho| ^ (p.1 : ℕ) * |sigma| ^ (p.2 : ℕ) := by positivity
  calc
    |rho| ^ (p.1 : ℕ) * |sigma| ^ (p.2 : ℕ) *
        ‖bblsAdditiveCharacter ((p.1 : ℕ) * (p.2 : ℕ)) x /
          ↑((((p.1 : ℕ) * (p.2 : ℕ)) : ℝ))‖ ≤
        |rho| ^ (p.1 : ℕ) * |sigma| ^ (p.2 : ℕ) * 1 :=
      mul_le_mul_of_nonneg_left hdenom hcoefficient
    _ = |rho| ^ (p.1 : ℕ) * |sigma| ^ (p.2 : ℕ) := mul_one _

/-- The product geometric majorant is summable in the open bidisc. -/
theorem summable_bblsAbelGeometricMajorant
    (rho sigma : ℝ) (hrho : |rho| < 1) (hsigma : |sigma| < 1) :
    Summable (fun p : ℕ+ × ℕ+ =>
      |rho| ^ (p.1 : ℕ) * |sigma| ^ (p.2 : ℕ)) := by
  have hr : Summable (fun m : ℕ+ => |rho| ^ (m : ℕ)) :=
    (summable_geometric_of_lt_one (abs_nonneg rho) hrho).subtype _
  have hs : Summable (fun ell : ℕ+ => |sigma| ^ (ell : ℕ)) :=
    (summable_geometric_of_lt_one (abs_nonneg sigma) hsigma).subtype _
  apply (summable_prod_of_nonneg (α := ℕ+) (β := ℕ+) (fun p =>
    mul_nonneg (pow_nonneg (abs_nonneg rho) (p.1 : ℕ))
      (pow_nonneg (abs_nonneg sigma) (p.2 : ℕ)))).2
  constructor
  · intro m
    exact Summable.mul_left (|rho| ^ (m : ℕ)) hs
  · have htsum (m : ℕ+) :
        (∑' ell : ℕ+, |rho| ^ (m : ℕ) * |sigma| ^ (ell : ℕ)) =
          |rho| ^ (m : ℕ) * ∑' ell : ℕ+, |sigma| ^ (ell : ℕ) :=
        hs.tsum_mul_left _
    simp_rw [htsum]
    exact Summable.mul_right (∑' ell : ℕ+, |sigma| ^ (ell : ℕ)) hr

/-- Absolute summability of the infinite double-Abel BBLS product. -/
theorem summable_bblsInfiniteAbelProductTerm
    (rho sigma : ℝ) (x : ℝ) (hrho : |rho| < 1) (hsigma : |sigma| < 1) :
    Summable (bblsInfiniteAbelProductTerm rho sigma x) :=
  (summable_bblsAbelGeometricMajorant rho sigma hrho hsigma).of_norm_bounded
    (norm_bblsInfiniteAbelProductTerm_le rho sigma x)

/-- Infinite double-Abel BBLS product sum. -/
noncomputable def bblsInfiniteAbelProductSum
    (rho sigma : ℝ) (x : ℝ) : ℂ :=
  ∑' p : ℕ+ × ℕ+, bblsInfiniteAbelProductTerm rho sigma x p

/-! ## Uniform closed-sub-bidisc domination -/

/-- A common summable majorant for all parameters in the closed sub-bidisc
`|rho| <= r`, `|sigma| <= s`, where `r,s < 1`. -/
theorem norm_bblsInfiniteAbelProductTerm_le_closedSubdisc
    (rho sigma r s : ℝ) (x : ℝ) (p : ℕ+ × ℕ+)
    (hrho : |rho| ≤ r) (hsigma : |sigma| ≤ s) :
    ‖bblsInfiniteAbelProductTerm rho sigma x p‖ ≤
      r ^ (p.1 : ℕ) * s ^ (p.2 : ℕ) := by
  calc
    ‖bblsInfiniteAbelProductTerm rho sigma x p‖ ≤
        |rho| ^ (p.1 : ℕ) * |sigma| ^ (p.2 : ℕ) :=
      norm_bblsInfiniteAbelProductTerm_le rho sigma x p
    _ ≤ r ^ (p.1 : ℕ) * s ^ (p.2 : ℕ) := by
      have hrnonneg : 0 ≤ r := (abs_nonneg rho).trans hrho
      have hsnonneg : 0 ≤ s := (abs_nonneg sigma).trans hsigma
      exact mul_le_mul
        (pow_le_pow_left₀ (abs_nonneg rho) hrho _)
        (pow_le_pow_left₀ (abs_nonneg sigma) hsigma _)
        (pow_nonneg (abs_nonneg sigma) _)
        (pow_nonneg hrnonneg _)

/-- The common closed-sub-bidisc majorant is summable. -/
theorem summable_bblsClosedSubdiscMajorant
    (r s : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Summable (fun p : ℕ+ × ℕ+ =>
      r ^ (p.1 : ℕ) * s ^ (p.2 : ℕ)) := by
  have hrabs : |r| < 1 := by simpa [abs_of_nonneg hr0] using hr1
  have hsabs : |s| < 1 := by simpa [abs_of_nonneg hs0] using hs1
  simpa [abs_of_nonneg hr0, abs_of_nonneg hs0] using
    summable_bblsAbelGeometricMajorant r s hrabs hsabs

/-! ## Exchange with finite-measure phase integrals -/

/-- Every fixed positive-frequency summand is continuous in the additive
phase variable. -/
theorem continuous_bblsInfiniteAbelProductTerm
    (rho sigma : ℝ) (p : ℕ+ × ℕ+) :
    Continuous (fun x : ℝ => bblsInfiniteAbelProductTerm rho sigma x p) := by
  unfold bblsInfiniteAbelProductTerm bblsAdditiveCharacter
  fun_prop

/-- The infinite double-Abel product may be exchanged with integration over
any finite-measure set of phases.  This is the additive-phase
exchange only; it does not claim the later Mellin/Estermann contour exchange. -/
theorem integral_bblsInfiniteAbelProductSum
    (rho sigma : ℝ) (s : Set ℝ)
    (hμs : volume s < ⊤) (hrho : |rho| < 1) (hsigma : |sigma| < 1) :
    ∫ x in s, bblsInfiniteAbelProductSum rho sigma x =
      ∑' p : ℕ+ × ℕ+,
        ∫ x in s, bblsInfiniteAbelProductTerm rho sigma x p := by
  let majorant : ℕ+ × ℕ+ → ℝ := fun p =>
    |rho| ^ (p.1 : ℕ) * |sigma| ^ (p.2 : ℕ)
  have hmajorant : Summable majorant :=
    summable_bblsAbelGeometricMajorant rho sigma hrho hsigma
  have htermIntegrable (p : ℕ+ × ℕ+) :
      Integrable (fun x : ℝ => bblsInfiniteAbelProductTerm rho sigma x p)
        (volume.restrict s) := by
    exact IntegrableOn.of_bound hμs
      (continuous_bblsInfiniteAbelProductTerm rho sigma p).aestronglyMeasurable
      (majorant p)
      (Filter.Eventually.of_forall fun x =>
        norm_bblsInfiniteAbelProductTerm_le rho sigma x p)
  have hconstIntegrable (p : ℕ+ × ℕ+) :
      Integrable (fun _x : ℝ => majorant p) (volume.restrict s) := by
    exact integrableOn_const hμs.ne
  have hintegralNormBound (p : ℕ+ × ℕ+) :
      (∫ x, ‖bblsInfiniteAbelProductTerm rho sigma x p‖
          ∂(volume.restrict s)) ≤ majorant p * volume.real s := by
    calc
      (∫ x, ‖bblsInfiniteAbelProductTerm rho sigma x p‖
          ∂(volume.restrict s)) ≤
          ∫ _x : ℝ, majorant p ∂(volume.restrict s) := by
        exact integral_mono_ae (htermIntegrable p).norm (hconstIntegrable p)
          (Filter.Eventually.of_forall fun x =>
            norm_bblsInfiniteAbelProductTerm_le rho sigma x p)
      _ = majorant p * volume.real s := by
        rw [MeasureTheory.integral_const]
        simp [smul_eq_mul, mul_comm]
  have hintegralNormSummable : Summable (fun p : ℕ+ × ℕ+ =>
      ∫ x, ‖bblsInfiniteAbelProductTerm rho sigma x p‖
        ∂(volume.restrict s)) :=
    (hmajorant.mul_right (volume.real s)).of_nonneg_of_le
      (fun _ => integral_nonneg fun _ => norm_nonneg _)
      hintegralNormBound
  unfold bblsInfiniteAbelProductSum
  exact (integral_tsum_of_summable_integral_norm
    htermIntegrable hintegralNormSummable).symm

/-! ## Exact regrouping by product frequency -/

/-- Abel weight on the divisor antidiagonal of a positive frequency. -/
noncomputable def bblsInfiniteAbelDivisorWeight
    (rho sigma : ℝ) (n : ℕ+) : ℝ :=
  ∑ p : Nat.divisorsAntidiagonal (n : ℕ),
    rho ^ p.1.1 * sigma ^ p.1.2

/-- The product-frequency term obtained after exact divisor regrouping. -/
noncomputable def bblsInfiniteAbelDivisorTerm
    (rho sigma : ℝ) (x : ℝ) (n : ℕ+) : ℂ :=
  (bblsInfiniteAbelDivisorWeight rho sigma n : ℂ) *
    (bblsAdditiveCharacter (n : ℕ) x / (((n : ℝ) : ℂ)))

/-- Exact infinite product-to-divisor expansion in the open Abel bidisc. -/
theorem bblsInfiniteAbelProductSum_eq_divisorSum
    (rho sigma : ℝ) (x : ℝ) (hrho : |rho| < 1) (hsigma : |sigma| < 1) :
    bblsInfiniteAbelProductSum rho sigma x =
      ∑' n : ℕ+, bblsInfiniteAbelDivisorTerm rho sigma x n := by
  have hprod := summable_bblsInfiniteAbelProductTerm rho sigma x hrho hsigma
  have hsigmaSum : Summable
      (fun z : Σ n : ℕ+, Nat.divisorsAntidiagonal (n : ℕ) =>
        bblsInfiniteAbelProductTerm rho sigma x
          (sigmaAntidiagonalEquivProd z)) :=
    sigmaAntidiagonalEquivProd.summable_iff.mpr hprod
  unfold bblsInfiniteAbelProductSum
  rw [← sigmaAntidiagonalEquivProd.tsum_eq]
  rw [Summable.tsum_sigma hsigmaSum]
  apply tsum_congr
  intro n
  rw [tsum_fintype]
  unfold bblsInfiniteAbelDivisorTerm bblsInfiniteAbelDivisorWeight
  simp only [Complex.ofReal_sum, Complex.ofReal_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hproduct := (Nat.mem_divisorsAntidiagonal.mp p.property).1
  have hproductReal :
      ((p.1.1 : ℕ) : ℝ) * ((p.1.2 : ℕ) : ℝ) = ((n : ℕ) : ℝ) := by
    exact_mod_cast hproduct
  simp only [bblsInfiniteAbelProductTerm, sigmaAntidiagonalEquivProd,
    divisorsAntidiagonalFactors, Equiv.coe_fn_mk, PNat.mk_coe]
  rw [hproduct, hproductReal, Complex.ofReal_mul]

/-- The divisor-frequency expansion is summable whenever both Abel parameters
lie in the open unit disc. -/
theorem summable_bblsInfiniteAbelDivisorTerm
    (rho sigma : ℝ) (x : ℝ) (hrho : |rho| < 1) (hsigma : |sigma| < 1) :
    Summable (bblsInfiniteAbelDivisorTerm rho sigma x) := by
  have hprod := summable_bblsInfiniteAbelProductTerm rho sigma x hrho hsigma
  have hsigmaSum : Summable
      (fun z : Σ n : ℕ+, Nat.divisorsAntidiagonal (n : ℕ) =>
        bblsInfiniteAbelProductTerm rho sigma x
          (sigmaAntidiagonalEquivProd z)) :=
    sigmaAntidiagonalEquivProd.summable_iff.mpr hprod
  have houter : Summable (fun n : ℕ+ =>
      ∑' p : Nat.divisorsAntidiagonal (n : ℕ),
        bblsInfiniteAbelProductTerm rho sigma x
          (sigmaAntidiagonalEquivProd ⟨n, p⟩)) :=
    hsigmaSum.sigma
  apply houter.congr
  intro n
  rw [tsum_fintype]
  unfold bblsInfiniteAbelDivisorTerm bblsInfiniteAbelDivisorWeight
  simp only [Complex.ofReal_sum, Complex.ofReal_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hproduct := (Nat.mem_divisorsAntidiagonal.mp p.property).1
  have hproductReal :
      ((p.1.1 : ℕ) : ℝ) * ((p.1.2 : ℕ) : ℝ) = ((n : ℕ) : ℝ) := by
    exact_mod_cast hproduct
  simp only [bblsInfiniteAbelProductTerm, sigmaAntidiagonalEquivProd,
    divisorsAntidiagonalFactors, Equiv.coe_fn_mk, PNat.mk_coe]
  rw [hproduct, hproductReal, Complex.ofReal_mul]

end NBMellinTools.NB12
