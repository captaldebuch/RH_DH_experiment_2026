import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmProductTruncation

/-!
# MSTT polynomial-phase interface for the H15 route

This module records the exact short-interval shape of the Möbius part of
Matomäki--Shao--Tao--Teräväinen, Theorem 1.1(i), specialized to polynomial
phases on the circle:

<https://arxiv.org/abs/2204.03754>

The published theorem is a deep external result and is not currently in
Mathlib.  To avoid introducing an axiom, it is represented here by an
explicit hypothesis structure.  The module then proves, unconditionally,
the finite Abel-summation transfer from maximal polynomial-phase sums to
complex weights of bounded discrete variation.

No instance of the external estimate is asserted in this file.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperMSTTPolynomialPhase

open scoped BigOperators Topology

/-! ## Polynomial phases and short blocks -/

/-- The circle nilsequence `e(P(n))` attached to a real polynomial. -/
noncomputable def msttPolynomialPhase (P : Polynomial ℝ) (n : ℕ) : ℂ :=
  Complex.exp
    ((((2 * Real.pi * P.eval (n : ℝ) : ℝ) : ℂ) * Complex.I))

/-- The Möbius--polynomial sum on the interval `(X, X+H]`. -/
noncomputable def msttMobiusPolynomialBlock
    (P : Polynomial ℝ) (X H : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc X (X + H),
    (((ArithmeticFunction.moebius n : ℤ) : ℂ) * msttPolynomialPhase P n)

theorem norm_msttPolynomialPhase (P : Polynomial ℝ) (n : ℕ) :
    ‖msttPolynomialPhase P n‖ = 1 := by
  unfold msttPolynomialPhase
  exact Complex.norm_exp_ofReal_mul_I _

/-! ## Exact external theorem interface -/

/--
The maximal polynomial-phase consequence of MSTT Theorem 1.1(i).

For fixed degree `d`, logarithmic saving `A`, and `epsilon`, the constant
and threshold are uniform in the polynomial coefficients, the scale `X`,
the admissible interval length `H`, and every prefix length `K <= H`.

The lower exponent is exactly `5/8 + epsilon`; the upper exponent is
`1 - epsilon`.  The prefix-uniform formulation is a direct specialization
of the starred maximal norm used in the paper.
-/
structure MSTTMobiusPolynomialPhaseEstimate where
  constant : ℕ → ℕ → ℝ → ℝ
  threshold : ℕ → ℕ → ℝ → ℕ
  constant_nonneg : ∀ d A epsilon, 0 ≤ constant d A epsilon
  maximal_prefix_bound :
    ∀ d A : ℕ, ∀ epsilon : ℝ,
      0 < epsilon →
      ∀ X H : ℕ,
        threshold d A epsilon ≤ X →
        3 ≤ X →
        1 ≤ H →
        Real.rpow (X : ℝ) ((5 / 8 : ℝ) + epsilon) ≤ (H : ℝ) →
        (H : ℝ) ≤ Real.rpow (X : ℝ) (1 - epsilon) →
        ∀ P : Polynomial ℝ,
          P.natDegree ≤ d →
          ∀ K : ℕ, K ≤ H →
            ‖msttMobiusPolynomialBlock P X K‖ ≤
              constant d A epsilon * (H : ℝ) /
                (Real.log (X : ℝ)) ^ A

/-! ## Complex Abel summation and variation -/

/-- Exact finite Abel summation on a natural interval, with complex
coefficients and weights. -/
theorem finite_abel_sum_Icc_mul_eq_endpoint_add_sum_partial
    (a w : ℕ → ℂ) (A B : ℕ) (hAB : A ≤ B) :
    (∑ n ∈ Finset.Icc A B, a n * w n) =
      (∑ j ∈ Finset.Icc A B, a j) * w (B + 1) +
        ∑ n ∈ Finset.Icc A B,
          (∑ j ∈ Finset.Icc A n, a j) * (w n - w (n + 1)) := by
  induction B, hAB using Nat.le_induction with
  | base =>
      simp
      ring
  | succ B hAB ih =>
      have hAB' : A ≤ B + 1 := by omega
      rw [Finset.sum_Icc_succ_top hAB', Finset.sum_Icc_succ_top hAB',
        Finset.sum_Icc_succ_top hAB']
      rw [ih]
      rw [Finset.sum_Icc_succ_top hAB']
      ring

/-- Endpoint plus total discrete variation of a complex weight on
`[A,B]`. -/
noncomputable def complexWeightVariation
    (w : ℕ → ℂ) (A B : ℕ) : ℝ :=
  ‖w (B + 1)‖ + ∑ n ∈ Finset.Icc A B, ‖w n - w (n + 1)‖

theorem complexWeightVariation_nonneg
    (w : ℕ → ℂ) (A B : ℕ) :
    0 ≤ complexWeightVariation w A B := by
  unfold complexWeightVariation
  positivity

/-- Maximal partial-sum control transfers to a weighted sum with the exact
endpoint-plus-variation loss. -/
theorem norm_sum_Icc_mul_le_partialBound_mul_variation
    (a w : ℕ → ℂ) (A B : ℕ) (M : ℝ)
    (hAB : A ≤ B)
    (hpartial : ∀ n ∈ Finset.Icc A B,
      ‖∑ j ∈ Finset.Icc A n, a j‖ ≤ M) :
    ‖∑ n ∈ Finset.Icc A B, a n * w n‖ ≤
      M * complexWeightVariation w A B := by
  rw [finite_abel_sum_Icc_mul_eq_endpoint_add_sum_partial a w A B hAB]
  calc
    ‖(∑ j ∈ Finset.Icc A B, a j) * w (B + 1) +
        ∑ n ∈ Finset.Icc A B,
          (∑ j ∈ Finset.Icc A n, a j) * (w n - w (n + 1))‖ ≤
      ‖(∑ j ∈ Finset.Icc A B, a j) * w (B + 1)‖ +
        ‖∑ n ∈ Finset.Icc A B,
          (∑ j ∈ Finset.Icc A n, a j) * (w n - w (n + 1))‖ :=
        norm_add_le _ _
    _ ≤ ‖(∑ j ∈ Finset.Icc A B, a j) * w (B + 1)‖ +
        ∑ n ∈ Finset.Icc A B,
          ‖(∑ j ∈ Finset.Icc A n, a j) * (w n - w (n + 1))‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ M * ‖w (B + 1)‖ +
        ∑ n ∈ Finset.Icc A B, M * ‖w n - w (n + 1)‖ := by
      gcongr with n hn
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hpartial B
          (Finset.mem_Icc.mpr ⟨hAB, le_rfl⟩)) (norm_nonneg _)
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hpartial n hn) (norm_nonneg _)
    _ = M * complexWeightVariation w A B := by
      unfold complexWeightVariation
      rw [← Finset.mul_sum]
      ring

private theorem Icc_succ_eq_Ioc (X Y : ℕ) :
    Finset.Icc (X + 1) Y = Finset.Ioc X Y := by
  ext n
  simp

/-- Weighted short-block consequence of the MSTT maximal estimate.

This theorem is entirely formal once an `MSTTMobiusPolynomialPhaseEstimate`
is supplied.  The only loss is the exact discrete variation of `w`.
-/
theorem norm_weighted_msttMobiusPolynomialBlock_le
    (HM : MSTTMobiusPolynomialPhaseEstimate)
    (d A : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (X H : ℕ)
    (hthreshold : HM.threshold d A epsilon ≤ X)
    (hX : 3 ≤ X) (hH : 1 ≤ H)
    (hHlower :
      Real.rpow (X : ℝ) ((5 / 8 : ℝ) + epsilon) ≤ (H : ℝ))
    (hHupper :
      (H : ℝ) ≤ Real.rpow (X : ℝ) (1 - epsilon))
    (P : Polynomial ℝ) (hdegree : P.natDegree ≤ d)
    (w : ℕ → ℂ) :
    ‖∑ n ∈ Finset.Ioc X (X + H),
        ((((ArithmeticFunction.moebius n : ℤ) : ℂ) *
          msttPolynomialPhase P n) * w n)‖ ≤
      (HM.constant d A epsilon * (H : ℝ) /
          (Real.log (X : ℝ)) ^ A) *
        complexWeightVariation w (X + 1) (X + H) := by
  have hAB : X + 1 ≤ X + H := by omega
  rw [← Icc_succ_eq_Ioc X (X + H)]
  apply norm_sum_Icc_mul_le_partialBound_mul_variation
    (fun n ↦ (((ArithmeticFunction.moebius n : ℤ) : ℂ) *
      msttPolynomialPhase P n)) w (X + 1) (X + H)
    (HM.constant d A epsilon * (H : ℝ) /
      (Real.log (X : ℝ)) ^ A) hAB
  · intro n hn
    have hnlo : X + 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnle : n ≤ X + H := (Finset.mem_Icc.mp hn).2
    let K := n - X
    have hK : K ≤ H := by
      dsimp [K]
      omega
    have hXK : X + K = n := by
      dsimp [K]
      omega
    have hsum :
        (∑ j ∈ Finset.Icc (X + 1) n,
          (((ArithmeticFunction.moebius j : ℤ) : ℂ) *
            msttPolynomialPhase P j)) =
          msttMobiusPolynomialBlock P X K := by
      unfold msttMobiusPolynomialBlock
      rw [← Icc_succ_eq_Ioc X (X + K), hXK]
    rw [hsum]
    exact HM.maximal_prefix_bound d A epsilon hepsilon X H
      hthreshold hX hH hHlower hHupper P hdegree K hK

end RH.Criteria.NymanBeurling.BCFLogTaperMSTTPolynomialPhase
