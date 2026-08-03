/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSSignedBlocks

/-!
# NB12d: finite product-to-divisor expansion of the BBLS tail

The Fourier expansion of the BBLS rational harmonic tail contains products
of two positive frequencies.  This file performs the finite hyperbolic
reindexing `n = m * ell` exactly.

The resulting multiplicity depends only on the product frequency `n` and on
the three global cutoffs.  In particular it is independent of the moving
rational row `(h,k)`.  This is the coefficient-separation property required
before an Estermann reciprocity or Bettin--Chandee trilinear estimate can be
applied.

No infinite series, sum--integral exchange, or asymptotic estimate is used in
this file.
-/

open scoped BigOperators

namespace NBMellinTools.NB12

/-! ## Finite hyperbolic fibers -/

/-- Positive product indices with `M < m <= U` and `1 <= ell <= L`. -/
def bblsProductPairs (M U L : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ioc M U).product (Finset.Icc 1 L)

/-- Number of representations `n = m * ell` inside the truncated BBLS
hyperbola.  This is a restricted divisor multiplicity. -/
def bblsRestrictedDivisorMultiplicity (M U L n : ℕ) : ℕ :=
  ((bblsProductPairs M U L).filter (fun ml => ml.1 * ml.2 = n)).card

/-- The restricted product multiplicity is bounded by the ordinary divisor
count.  This is the basic `ℓ²` majorant required by a later trilinear-form
estimate. -/
theorem bblsRestrictedDivisorMultiplicity_le_divisorsCard
    (M U L n : ℕ) (hn : 0 < n) :
    bblsRestrictedDivisorMultiplicity M U L n ≤ n.divisors.card := by
  classical
  unfold bblsRestrictedDivisorMultiplicity
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro ml hml
    change ml ∈ (bblsProductPairs M U L).filter
      (fun ml => ml.1 * ml.2 = n) at hml
    simp only [Finset.mem_filter] at hml
    change ml.1 ∈ n.divisors
    rw [Nat.mem_divisors]
    exact ⟨⟨ml.2, hml.2.symm⟩, hn.ne'⟩
  · intro ml hml ml' hml' hfirst
    change ml ∈ (bblsProductPairs M U L).filter
      (fun ml => ml.1 * ml.2 = n) at hml
    change ml' ∈ (bblsProductPairs M U L).filter
      (fun ml => ml.1 * ml.2 = n) at hml'
    simp only [Finset.mem_filter] at hml hml'
    apply Prod.ext hfirst
    have hp : 0 < ml.1 := by
      have hpair : ml.1 ∈ Finset.Ioc M U ∧ ml.2 ∈ Finset.Icc 1 L := by
        simpa [bblsProductPairs] using hml.1
      have := (Finset.mem_Ioc.mp hpair.1).1
      omega
    apply Nat.eq_of_mul_eq_mul_left hp
    calc
      ml.1 * ml.2 = n := hml.2
      _ = ml'.1 * ml'.2 := hml'.2.symm
      _ = ml.1 * ml'.2 := by rw [hfirst]

/-- Normalized separated coefficient appearing after the product-frequency
collapse. -/
noncomputable def bblsRestrictedDivisorCoefficient
    (M U L n : ℕ) : ℝ :=
  (bblsRestrictedDivisorMultiplicity M U L n : ℝ) / (n : ℝ)

/-- The normalized restricted coefficient is bounded by the usual normalized
divisor count. -/
theorem abs_bblsRestrictedDivisorCoefficient_le
    (M U L n : ℕ) (hn : 0 < n) :
    |bblsRestrictedDivisorCoefficient M U L n| ≤
      (n.divisors.card : ℝ) / (n : ℝ) := by
  have hmult := bblsRestrictedDivisorMultiplicity_le_divisorsCard M U L n hn
  unfold bblsRestrictedDivisorCoefficient
  rw [abs_of_nonneg (by positivity)]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hmult) (by positivity)

/-- Finite dyadic `ℓ²` control of the separated coefficient by the classical
divisor-square majorant. -/
theorem sum_sq_bblsRestrictedDivisorCoefficient_le
    (M U L A B : ℕ) (hA : 0 < A) :
    (∑ n ∈ Finset.Icc A B,
      bblsRestrictedDivisorCoefficient M U L n ^ 2) ≤
        ∑ n ∈ Finset.Icc A B,
          ((n.divisors.card : ℝ) / (n : ℝ)) ^ 2 := by
  apply Finset.sum_le_sum
  intro n hn
  have hnpos : 0 < n := hA.trans_le (Finset.mem_Icc.mp hn).1
  have hcoeff := abs_bblsRestrictedDivisorCoefficient_le M U L n hnpos
  rw [abs_of_nonneg (by
    unfold bblsRestrictedDivisorCoefficient
    positivity)] at hcoeff
  exact pow_le_pow_left₀ (by
    unfold bblsRestrictedDivisorCoefficient
    positivity) hcoeff 2

/-- Every represented product is positive and at most `U * L`. -/
theorem bblsProduct_mem_frequencyRange
    {M U L : ℕ} {ml : ℕ × ℕ} (hml : ml ∈ bblsProductPairs M U L) :
    ml.1 * ml.2 ∈ Finset.Icc 1 (U * L) := by
  have hp : ml.1 ∈ Finset.Ioc M U ∧ ml.2 ∈ Finset.Icc 1 L := by
    simpa [bblsProductPairs] using hml
  have hm := Finset.mem_Ioc.mp hp.1
  have hell := Finset.mem_Icc.mp hp.2
  simp only [Finset.mem_Icc]
  constructor
  · have hmpos : 0 < ml.1 := by omega
    have : 0 < ml.1 * ml.2 := Nat.mul_pos hmpos hell.1
    omega
  · exact Nat.mul_le_mul hm.2 hell.2

/-- Generic finite product-to-frequency reindexing.  The theorem is stated in
an arbitrary additive commutative monoid so that the real sine and complex
exponential forms are immediate specializations. -/
theorem sum_bblsProductPairs_eq_sum_restrictedDivisorMultiplicity
    {R : Type*} [AddCommMonoid R]
    (M U L : ℕ) (phase : ℕ → R) :
    (∑ m ∈ Finset.Ioc M U, ∑ ell ∈ Finset.Icc 1 L,
      phase (m * ell)) =
        ∑ n ∈ Finset.Icc 1 (U * L),
          bblsRestrictedDivisorMultiplicity M U L n • phase n := by
  classical
  let s := bblsProductPairs M U L
  let t := Finset.Icc 1 (U * L)
  let product : ℕ × ℕ → ℕ := fun ml => ml.1 * ml.2
  have hmap : ∀ ml ∈ s, product ml ∈ t := by
    intro ml hml
    exact bblsProduct_mem_frequencyRange hml
  have hfiber := Finset.sum_fiberwise_of_maps_to hmap (phase ∘ product)
  calc
    (∑ m ∈ Finset.Ioc M U, ∑ ell ∈ Finset.Icc 1 L,
        phase (m * ell)) =
        ∑ ml ∈ s, (phase ∘ product) ml := by
          unfold s bblsProductPairs product
          rw [← Finset.sum_product']
          rfl
    _ = ∑ n ∈ t, ∑ ml ∈ s with product ml = n,
          (phase ∘ product) ml := hfiber.symm
    _ = ∑ n ∈ t,
          bblsRestrictedDivisorMultiplicity M U L n • phase n := by
      apply Finset.sum_congr rfl
      intro n hn
      have hconst :
          (∑ ml ∈ s with product ml = n, (phase ∘ product) ml) =
            ∑ _ml ∈ s.filter (fun ml => product ml = n), phase n := by
        apply Finset.sum_congr rfl
        intro ml hml
        simp only [Finset.mem_filter] at hml
        simp [hml.2]
      rw [hconst, Finset.sum_const]
      unfold bblsRestrictedDivisorMultiplicity s product
      rfl
    _ = ∑ n ∈ Finset.Icc 1 (U * L),
          bblsRestrictedDivisorMultiplicity M U L n • phase n := by
      rfl

/-! ## Real sine expansion -/

/-- Finite doubly truncated Fourier contribution to the raw BBLS harmonic
tail.  The factor `1 / (m * ell)` is already absorbed into the product
frequency. -/
noncomputable def bblsFiniteSineProductSum
    (M U L : ℕ) (x : ℝ) : ℝ :=
  ∑ m ∈ Finset.Ioc M U, ∑ ell ∈ Finset.Icc 1 L,
    -(Real.sin (2 * Real.pi * ((m * ell : ℕ) : ℝ) * x) /
      (Real.pi * ((m * ell : ℕ) : ℝ)))

/-- The same finite sum after exact divisor-frequency collapse. -/
noncomputable def bblsFiniteSineDivisorSum
    (M U L : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (U * L),
    (bblsRestrictedDivisorMultiplicity M U L n : ℝ) *
      -(Real.sin (2 * Real.pi * (n : ℝ) * x) /
        (Real.pi * (n : ℝ)))

/-- Exact finite product-to-divisor identity in the sine normalization used by
the BBLS sawtooth expansion. -/
theorem bblsFiniteSineProductSum_eq_divisorSum
    (M U L : ℕ) (x : ℝ) :
    bblsFiniteSineProductSum M U L x =
      bblsFiniteSineDivisorSum M U L x := by
  unfold bblsFiniteSineProductSum bblsFiniteSineDivisorSum
  simpa [nsmul_eq_mul] using
    (sum_bblsProductPairs_eq_sum_restrictedDivisorMultiplicity
      M U L
      (fun n : ℕ =>
        -(Real.sin (2 * Real.pi * (n : ℝ) * x) /
          (Real.pi * (n : ℝ)))))

/-! ## Complex exponential expansion -/

/-- The standard additive character at the real phase `n*x`. -/
noncomputable def bblsAdditiveCharacter (n : ℕ) (x : ℝ) : ℂ :=
  Complex.exp
    (((2 * Real.pi * (n : ℝ) * x : ℝ) : ℂ) * Complex.I)

/-- Finite doubly truncated complex exponential sum before reindexing. -/
noncomputable def bblsFiniteExponentialProductSum
    (M U L : ℕ) (x : ℝ) : ℂ :=
  ∑ m ∈ Finset.Ioc M U, ∑ ell ∈ Finset.Icc 1 L,
    bblsAdditiveCharacter (m * ell) x /
      (((m * ell : ℕ) : ℝ) : ℂ)

/-- The separated divisor-frequency form of the finite complex sum. -/
noncomputable def bblsFiniteExponentialDivisorSum
    (M U L : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (U * L),
    (bblsRestrictedDivisorMultiplicity M U L n : ℂ) *
      (bblsAdditiveCharacter n x / (((n : ℕ) : ℝ) : ℂ))

/-- Exact finite complex product-to-divisor expansion.  The coefficient of
`exp(2*pi*i*n*x)` depends only on `n,M,U,L`. -/
theorem bblsFiniteExponentialProductSum_eq_divisorSum
    (M U L : ℕ) (x : ℝ) :
    bblsFiniteExponentialProductSum M U L x =
      bblsFiniteExponentialDivisorSum M U L x := by
  unfold bblsFiniteExponentialProductSum bblsFiniteExponentialDivisorSum
  simpa [nsmul_eq_mul] using
    (sum_bblsProductPairs_eq_sum_restrictedDivisorMultiplicity
      M U L
      (fun n : ℕ =>
        bblsAdditiveCharacter n x / (((n : ℕ) : ℝ) : ℂ)))

end NBMellinTools.NB12
