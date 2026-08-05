/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSDivisorExpansion

/-!
# NB12e: double Abel regularization of the finite BBLS divisor expansion

The product-to-divisor collapse in `NB12BBLSDivisorExpansion` is finite and
undamped.  This file introduces two independent Abel parameters, one for each
positive frequency in the product `n = m * ell`.

The central result is an exact weighted fiber identity.  Its specialization to
the BBLS additive character shows that the Abel-regularized coefficient still
depends only on the product frequency and the global cutoffs, not on the
moving rational row.  At the boundary `(rho, sigma) = (1, 1)` it reduces
exactly to the restricted-divisor coefficient from the previous file.

Everything here remains finite.  No infinite sum, contour shift, Estermann
functional equation, or signed asymptotic estimate is asserted.
-/

open Filter
open scoped BigOperators Topology

namespace NBMellinTools.NB12

/-! ## Weighted hyperbolic fibers -/

/-- Sum of an arbitrary weight over the representations `n = m * ell` inside
the truncated BBLS hyperbola. -/
def bblsRestrictedFiberWeight
    {R : Type*} [AddCommMonoid R]
    (M U L n : ℕ) (weight : ℕ × ℕ → R) : R :=
  ∑ ml ∈ (bblsProductPairs M U L).filter
    (fun ml => ml.1 * ml.2 = n), weight ml

/-- Exact finite weighted product-to-frequency reindexing. -/
theorem sum_weighted_bblsProductPairs_eq_sum_restrictedFiberWeight
    {R : Type*} [CommSemiring R]
    (M U L : ℕ) (weight : ℕ × ℕ → R) (phase : ℕ → R) :
    (∑ m ∈ Finset.Ioc M U, ∑ ell ∈ Finset.Icc 1 L,
      weight (m, ell) * phase (m * ell)) =
        ∑ n ∈ Finset.Icc 1 (U * L),
          bblsRestrictedFiberWeight M U L n weight * phase n := by
  classical
  let s := bblsProductPairs M U L
  let t := Finset.Icc 1 (U * L)
  let product : ℕ × ℕ → ℕ := fun ml => ml.1 * ml.2
  have hmap : ∀ ml ∈ s, product ml ∈ t := by
    intro ml hml
    exact bblsProduct_mem_frequencyRange hml
  have hfiber := Finset.sum_fiberwise_of_maps_to hmap
    (fun ml => weight ml * phase (product ml))
  calc
    (∑ m ∈ Finset.Ioc M U, ∑ ell ∈ Finset.Icc 1 L,
        weight (m, ell) * phase (m * ell)) =
        ∑ ml ∈ s, weight ml * phase (product ml) := by
          unfold s bblsProductPairs product
          rw [← Finset.sum_product']
          rfl
    _ = ∑ n ∈ t, ∑ ml ∈ s with product ml = n,
          weight ml * phase (product ml) := hfiber.symm
    _ = ∑ n ∈ t,
          bblsRestrictedFiberWeight M U L n weight * phase n := by
      apply Finset.sum_congr rfl
      intro n hn
      calc
        (∑ ml ∈ s with product ml = n,
            weight ml * phase (product ml)) =
            ∑ ml ∈ s with product ml = n,
              weight ml * phase n := by
          apply Finset.sum_congr rfl
          intro ml hml
          simp only [Finset.mem_filter] at hml
          rw [hml.2]
        _ = (∑ ml ∈ s with product ml = n, weight ml) * phase n := by
          rw [Finset.sum_mul]
        _ = bblsRestrictedFiberWeight M U L n weight * phase n := by
          unfold bblsRestrictedFiberWeight s product
          rfl
    _ = ∑ n ∈ Finset.Icc 1 (U * L),
          bblsRestrictedFiberWeight M U L n weight * phase n := by
      rfl

/-! ## Two Abel parameters -/

/-- Product Abel weight `rho^m * sigma^ell`. -/
noncomputable def bblsAbelPairWeight
    (rho sigma : ℝ) (ml : ℕ × ℕ) : ℝ :=
  rho ^ ml.1 * sigma ^ ml.2

/-- Restricted-divisor coefficient with independent Abel damping in the two
frequency variables. -/
noncomputable def bblsAbelRestrictedDivisorWeight
    (rho sigma : ℝ) (M U L n : ℕ) : ℝ :=
  bblsRestrictedFiberWeight M U L n (bblsAbelPairWeight rho sigma)

/-- Removing both Abel dampers recovers the exact restricted-divisor
multiplicity. -/
@[simp] theorem bblsAbelRestrictedDivisorWeight_one_one
    (M U L n : ℕ) :
    bblsAbelRestrictedDivisorWeight 1 1 M U L n =
      bblsRestrictedDivisorMultiplicity M U L n := by
  classical
  simp [bblsAbelRestrictedDivisorWeight, bblsAbelPairWeight,
    bblsRestrictedFiberWeight, bblsRestrictedDivisorMultiplicity]

/-- The Abel coefficient is a continuous polynomial in the two damping
parameters. -/
theorem continuous_bblsAbelRestrictedDivisorWeight
    (M U L n : ℕ) :
    Continuous (fun p : ℝ × ℝ =>
      bblsAbelRestrictedDivisorWeight p.1 p.2 M U L n) := by
  classical
  unfold bblsAbelRestrictedDivisorWeight bblsRestrictedFiberWeight
    bblsAbelPairWeight
  fun_prop

/-- Coefficientwise Abel boundary passage. -/
theorem tendsto_bblsAbelRestrictedDivisorWeight_one_one
    (M U L n : ℕ) :
    Tendsto
      (fun p : ℝ × ℝ =>
        bblsAbelRestrictedDivisorWeight p.1 p.2 M U L n)
      (nhds (1, 1))
      (nhds (bblsRestrictedDivisorMultiplicity M U L n : ℝ)) := by
  have h :=
    (continuous_bblsAbelRestrictedDivisorWeight M U L n).continuousAt
      (x := (1, 1))
  change Tendsto
    (fun p : ℝ × ℝ =>
      bblsAbelRestrictedDivisorWeight p.1 p.2 M U L n)
    (nhds (1, 1))
    (nhds (bblsAbelRestrictedDivisorWeight 1 1 M U L n)) at h
  rw [bblsAbelRestrictedDivisorWeight_one_one] at h
  exact h

/-- In the closed unit bidisc, the damped coefficient is bounded by the
number of representations in its fiber. -/
theorem abs_bblsAbelRestrictedDivisorWeight_le
    (rho sigma : ℝ) (M U L n : ℕ)
    (hrho : |rho| ≤ 1) (hsigma : |sigma| ≤ 1) :
    |bblsAbelRestrictedDivisorWeight rho sigma M U L n| ≤
      bblsRestrictedDivisorMultiplicity M U L n := by
  classical
  unfold bblsAbelRestrictedDivisorWeight bblsRestrictedFiberWeight
    bblsAbelPairWeight bblsRestrictedDivisorMultiplicity
  calc
    |∑ ml ∈ (bblsProductPairs M U L).filter
        (fun ml => ml.1 * ml.2 = n), rho ^ ml.1 * sigma ^ ml.2| ≤
        ∑ ml ∈ (bblsProductPairs M U L).filter
          (fun ml => ml.1 * ml.2 = n),
            |rho ^ ml.1 * sigma ^ ml.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ml ∈ (bblsProductPairs M U L).filter
          (fun ml => ml.1 * ml.2 = n), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro ml hml
      rw [abs_mul, abs_pow, abs_pow]
      exact mul_le_one₀
        (pow_le_one₀ (abs_nonneg rho) hrho)
        (pow_nonneg (abs_nonneg sigma) ml.2)
        (pow_le_one₀ (abs_nonneg sigma) hsigma)
    _ = (((bblsProductPairs M U L).filter
          (fun ml => ml.1 * ml.2 = n)).card : ℝ) := by simp

/-- Normalized double-Abel coefficient after the product-frequency collapse. -/
noncomputable def bblsAbelRestrictedDivisorCoefficient
    (rho sigma : ℝ) (M U L n : ℕ) : ℝ :=
  bblsAbelRestrictedDivisorWeight rho sigma M U L n / (n : ℝ)

/-- The divisor-function majorant is uniform in both Abel parameters throughout
the closed unit bidisc. -/
theorem abs_bblsAbelRestrictedDivisorCoefficient_le
    (rho sigma : ℝ) (M U L n : ℕ) (hn : 0 < n)
    (hrho : |rho| ≤ 1) (hsigma : |sigma| ≤ 1) :
    |bblsAbelRestrictedDivisorCoefficient rho sigma M U L n| ≤
      (n.divisors.card : ℝ) / (n : ℝ) := by
  unfold bblsAbelRestrictedDivisorCoefficient
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hmultR :
      (bblsRestrictedDivisorMultiplicity M U L n : ℝ) ≤
        (n.divisors.card : ℝ) := by
    exact_mod_cast
      bblsRestrictedDivisorMultiplicity_le_divisorsCard M U L n hn
  rw [abs_div]
  rw [abs_of_pos hnR]
  exact div_le_div_of_nonneg_right
    ((abs_bblsAbelRestrictedDivisorWeight_le
      rho sigma M U L n hrho hsigma).trans hmultR)
    hnR.le

/-- Uniform finite `ℓ²` majorant for the double-Abel divisor coefficients. -/
theorem sum_sq_bblsAbelRestrictedDivisorCoefficient_le
    (rho sigma : ℝ) (M U L A B : ℕ) (hA : 0 < A)
    (hrho : |rho| ≤ 1) (hsigma : |sigma| ≤ 1) :
    (∑ n ∈ Finset.Icc A B,
      bblsAbelRestrictedDivisorCoefficient rho sigma M U L n ^ 2) ≤
        ∑ n ∈ Finset.Icc A B,
          ((n.divisors.card : ℝ) / (n : ℝ)) ^ 2 := by
  apply Finset.sum_le_sum
  intro n hn
  have hnpos : 0 < n := hA.trans_le (Finset.mem_Icc.mp hn).1
  have hcoeff := abs_bblsAbelRestrictedDivisorCoefficient_le
    rho sigma M U L n hnpos hrho hsigma
  have hsquare :
      |bblsAbelRestrictedDivisorCoefficient rho sigma M U L n| ^ 2 ≤
        ((n.divisors.card : ℝ) / (n : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hcoeff 2
  simpa [sq_abs] using hsquare

/-! ## Exact Abel-regularized additive-character expansion -/

/-- Finite BBLS exponential product with independent Abel damping. -/
noncomputable def bblsFiniteAbelExponentialProductSum
    (rho sigma : ℝ) (M U L : ℕ) (x : ℝ) : ℂ :=
  ∑ m ∈ Finset.Ioc M U, ∑ ell ∈ Finset.Icc 1 L,
    ((rho ^ m * sigma ^ ell : ℝ) : ℂ) *
      (bblsAdditiveCharacter (m * ell) x /
        (((m * ell : ℕ) : ℝ) : ℂ))

/-- Divisor-frequency form of the double-Abel finite product. -/
noncomputable def bblsFiniteAbelExponentialDivisorSum
    (rho sigma : ℝ) (M U L : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (U * L),
    (bblsAbelRestrictedDivisorWeight rho sigma M U L n : ℂ) *
      (bblsAdditiveCharacter n x / (((n : ℕ) : ℝ) : ℂ))

/-- Exact finite double-Abel product-to-divisor identity. -/
theorem bblsFiniteAbelExponentialProductSum_eq_divisorSum
    (rho sigma : ℝ) (M U L : ℕ) (x : ℝ) :
    bblsFiniteAbelExponentialProductSum rho sigma M U L x =
      bblsFiniteAbelExponentialDivisorSum rho sigma M U L x := by
  classical
  unfold bblsFiniteAbelExponentialProductSum
    bblsFiniteAbelExponentialDivisorSum
    bblsAbelRestrictedDivisorWeight bblsAbelPairWeight
    bblsRestrictedFiberWeight
  simpa using
    (sum_weighted_bblsProductPairs_eq_sum_restrictedFiberWeight
      (R := ℂ) M U L
      (fun ml : ℕ × ℕ =>
        ((rho ^ ml.1 * sigma ^ ml.2 : ℝ) : ℂ))
      (fun n : ℕ =>
        bblsAdditiveCharacter n x / (((n : ℕ) : ℝ) : ℂ)))

/-- At the Abel boundary the regularized product is exactly the undamped
finite BBLS exponential product. -/
@[simp] theorem bblsFiniteAbelExponentialProductSum_one_one
    (M U L : ℕ) (x : ℝ) :
    bblsFiniteAbelExponentialProductSum 1 1 M U L x =
      bblsFiniteExponentialProductSum M U L x := by
  simp [bblsFiniteAbelExponentialProductSum,
    bblsFiniteExponentialProductSum]

/-- The whole finite Abel-regularized product converges to its undamped
boundary value. -/
theorem tendsto_bblsFiniteAbelExponentialProductSum_one_one
    (M U L : ℕ) (x : ℝ) :
    Tendsto
      (fun p : ℝ × ℝ =>
        bblsFiniteAbelExponentialProductSum p.1 p.2 M U L x)
      (nhds (1, 1))
      (nhds (bblsFiniteExponentialProductSum M U L x)) := by
  have hcontinuous : Continuous (fun p : ℝ × ℝ =>
      bblsFiniteAbelExponentialProductSum p.1 p.2 M U L x) := by
    classical
    simp_rw [bblsFiniteAbelExponentialProductSum_eq_divisorSum]
    unfold bblsFiniteAbelExponentialDivisorSum
    apply continuous_finsetSum
    intro n hn
    exact
      (Complex.continuous_ofReal.comp
        (continuous_bblsAbelRestrictedDivisorWeight M U L n)).mul
          continuous_const
  have h := hcontinuous.continuousAt (x := (1, 1))
  change Tendsto
    (fun p : ℝ × ℝ =>
      bblsFiniteAbelExponentialProductSum p.1 p.2 M U L x)
    (nhds (1, 1))
    (nhds (bblsFiniteAbelExponentialProductSum 1 1 M U L x)) at h
  rw [bblsFiniteAbelExponentialProductSum_one_one] at h
  exact h

end NBMellinTools.NB12
