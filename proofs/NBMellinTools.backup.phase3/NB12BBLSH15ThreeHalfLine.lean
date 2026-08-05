/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15MajorantAudit

/-!
# NB12v: unconditional H15 row growth on the reflected three-halves line

The central-line vertical package does not directly control the right edge
needed by the residue-capturing rectangle.  This file instead fixes
`Re(s)=3/2`.  After the Estermann functional equation the two dual series are
then evaluated in their absolutely convergent half-plane.

The construction is unconditional.  It produces an inhabitant of
`H15PositiveLineRowGrowth` with modulus exponent `2`, vertical polynomial
degree `2`, and the intrinsic exponential factor `exp (-pi*|t|/2)`.

This does not by itself prove a cutoff-uniform aggregate bound.  The remaining
absolute arithmetic mass is exactly the `CutoffBudget` isolated in the
preceding module; its modulus-square loss is deliberately visible.
-/

open scoped BigOperators Topology LSeries.notation
open Complex Filter MeasureTheory LSeries

namespace NBMellinTools.NB12

/-! ## Uniform absolute convergence of the dual series -/

/-- The fixed line to the right of both reflected poles. -/
noncomputable def bblsEstermannThreeHalfPoint (t : ℝ) : ℂ :=
  (3 / 2 : ℝ) + Complex.I * t

/-- A numerator- and modulus-independent majorant for the Estermann series on
`Re(s)=3/2`. -/
noncomputable def bblsThreeHalfDirichletMajorant : ℝ :=
  ∑' n : ℕ, ‖LSeries.term bblsEstermannDivisorCoeff (3 / 2 : ℂ) n‖

theorem summable_bblsThreeHalfDirichletMajorant :
    Summable (fun n : ℕ =>
      ‖LSeries.term bblsEstermannDivisorCoeff (3 / 2 : ℂ) n‖) := by
  have h := bblsEstermannDivisorCoeff_summable
    (s := (3 / 2 : ℂ)) (by norm_num)
  rw [LSeriesSummable, ← summable_norm_iff] at h
  exact h

theorem bblsThreeHalfDirichletMajorant_nonneg :
    0 ≤ bblsThreeHalfDirichletMajorant := by
  unfold bblsThreeHalfDirichletMajorant
  exact tsum_nonneg fun _ => norm_nonneg _

/-- Additive twisting and the imaginary coordinate do not change the norm of
one Dirichlet-series term. -/
theorem norm_bblsEstermann_term_threeHalfPoint
    (phase : ℝ) (n : ℕ) (t : ℝ) :
    ‖LSeries.term (bblsEstermannCoeff phase)
        (bblsEstermannThreeHalfPoint t) n‖ =
      ‖LSeries.term bblsEstermannDivisorCoeff (3 / 2 : ℂ) n‖ := by
  simp only [LSeries.norm_term_eq, norm_bblsEstermannCoeff]
  congr 2
  norm_num [bblsEstermannThreeHalfPoint]

/-- Absolute convergence gives a bound uniform in numerator, modulus, and
vertical frequency. -/
theorem norm_bblsEstermannHurwitzContinuation_threeHalf_le
    (a q : ℕ) [NeZero q] (t : ℝ) :
    ‖bblsEstermannHurwitzContinuation a q
        (bblsEstermannThreeHalfPoint t)‖ ≤
      bblsThreeHalfDirichletMajorant := by
  have hs : 1 < (bblsEstermannThreeHalfPoint t).re := by
    norm_num [bblsEstermannThreeHalfPoint]
  rw [bblsEstermannHurwitzContinuation_eq_dirichletSeries a q hs]
  unfold bblsEstermannDirichletSeries LSeries
  have hsum : Summable (fun n : ℕ =>
      LSeries.term (bblsEstermannCoeff ((a : ℝ) / (q : ℝ)))
        (bblsEstermannThreeHalfPoint t) n) :=
    bblsEstermannCoeff_summable _ hs
  calc
    ‖∑' n : ℕ, LSeries.term
        (bblsEstermannCoeff ((a : ℝ) / (q : ℝ)))
        (bblsEstermannThreeHalfPoint t) n‖ ≤
      ∑' n : ℕ, ‖LSeries.term
        (bblsEstermannCoeff ((a : ℝ) / (q : ℝ)))
        (bblsEstermannThreeHalfPoint t) n‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ = bblsThreeHalfDirichletMajorant := by
      unfold bblsThreeHalfDirichletMajorant
      apply tsum_congr
      intro n
      exact norm_bblsEstermann_term_threeHalfPoint _ n t

/-! ## Transport of the classical functional-equation factor -/

theorem bblsEstermannThreeHalfPoint_eq_add_one (t : ℝ) :
    bblsEstermannThreeHalfPoint t = bblsEstermannCentralPoint t + 1 := by
  unfold bblsEstermannThreeHalfPoint bblsEstermannCentralPoint
  push_cast
  ring

/-- The classical factor at `3/2+it` is the central factor times the exact
modulus-square and archimedean shift. -/
theorem bblsEstermannClassicalFactor_threeHalf_eq
    (q : ℕ) [NeZero q] (t : ℝ) :
    bblsEstermannClassicalFactor q (bblsEstermannThreeHalfPoint t) =
      (q : ℂ) ^ (2 : ℂ) * (2 * Real.pi : ℂ) ^ (-2 : ℂ) *
        bblsEstermannCentralPoint t ^ 2 *
          bblsEstermannClassicalFactor q
            (bblsEstermannCentralPoint t) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  have hb0 : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hz0 : bblsEstermannCentralPoint t ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [bblsEstermannCentralPoint] at hre
  rw [bblsEstermannThreeHalfPoint_eq_add_one]
  unfold bblsEstermannClassicalFactor
  rw [show 2 * (bblsEstermannCentralPoint t + 1) - 1 =
      (2 * bblsEstermannCentralPoint t - 1) + 2 by ring]
  rw [Complex.cpow_add _ _ hq0]
  rw [show -2 * (bblsEstermannCentralPoint t + 1) =
      -2 * bblsEstermannCentralPoint t + (-2) by ring]
  rw [Complex.cpow_add _ _ hb0]
  rw [Complex.Gamma_add_one _ hz0]
  ring

theorem norm_bblsEstermannCentralPoint_le (t : ℝ) :
    ‖bblsEstermannCentralPoint t‖ ≤ 1 + |t| := by
  unfold bblsEstermannCentralPoint
  calc
    ‖(((1 / 2 : ℝ) : ℂ)) + Complex.I * (t : ℂ)‖ ≤
      ‖(((1 / 2 : ℝ) : ℂ))‖ + ‖Complex.I * (t : ℂ)‖ :=
        norm_add_le _ _
    _ = (1 / 2 : ℝ) + |t| := by simp [Real.norm_eq_abs]
    _ ≤ 1 + |t| := by linarith

/-- The unweighted functional-equation factor costs `q^2` and a quadratic
vertical polynomial on the three-halves line. -/
theorem norm_bblsEstermannClassicalFactor_threeHalf_le
    (q : ℕ) [NeZero q] (t : ℝ) :
    ‖bblsEstermannClassicalFactor q (bblsEstermannThreeHalfPoint t)‖ ≤
      (q : ℝ) ^ 2 * (1 + |t|) ^ 2 := by
  rw [bblsEstermannClassicalFactor_threeHalf_eq]
  simp only [norm_mul, norm_pow]
  simp
  have hb : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hbpow : ‖(2 * (Real.pi : ℂ)) ^ (-2 : ℂ)‖ ≤ 1 := by
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by
      push_cast
      rfl]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos
      (by positivity : 0 < 2 * Real.pi)]
    exact Real.rpow_le_one_of_one_le_of_nonpos hb (by norm_num)
  have hf := norm_bblsEstermannClassicalFactor_central_le_one q t
  have hz := norm_bblsEstermannCentralPoint_le t
  calc
    (q : ℝ) ^ 2 * ‖(2 * (Real.pi : ℂ)) ^ (-2 : ℂ)‖ *
        ‖bblsEstermannCentralPoint t‖ ^ 2 *
        ‖bblsEstermannClassicalFactor q
          (bblsEstermannCentralPoint t)‖ ≤
      (q : ℝ) ^ 2 * 1 * (1 + |t|) ^ 2 * 1 := by gcongr
    _ = (q : ℝ) ^ 2 * (1 + |t|) ^ 2 := by ring

theorem cos_pi_mul_bblsEstermannThreeHalfPoint (t : ℝ) :
    Complex.cos ((Real.pi : ℂ) * bblsEstermannThreeHalfPoint t) =
      -Complex.cos ((Real.pi : ℂ) * bblsEstermannCentralPoint t) := by
  rw [bblsEstermannThreeHalfPoint_eq_add_one]
  rw [show (Real.pi : ℂ) * (bblsEstermannCentralPoint t + 1) =
      (Real.pi : ℂ) * bblsEstermannCentralPoint t + Real.pi by ring]
  rw [Complex.cos_add, Complex.cos_pi, Complex.sin_pi]
  ring

/-- The cosine-weighted factor has the same polynomial/modulus loss because
the central Gamma decay absorbs the cosine growth. -/
theorem norm_bblsEstermannClassicalFactor_mul_cos_threeHalf_le
    (q : ℕ) [NeZero q] (t : ℝ) :
    ‖bblsEstermannClassicalFactor q (bblsEstermannThreeHalfPoint t) *
        Complex.cos ((Real.pi : ℂ) * bblsEstermannThreeHalfPoint t)‖ ≤
      (q : ℝ) ^ 2 * (1 + |t|) ^ 2 := by
  rw [bblsEstermannClassicalFactor_threeHalf_eq,
    cos_pi_mul_bblsEstermannThreeHalfPoint]
  rw [show
    ((q : ℂ) ^ (2 : ℂ) * (2 * Real.pi : ℂ) ^ (-2 : ℂ) *
        bblsEstermannCentralPoint t ^ 2 *
          bblsEstermannClassicalFactor q (bblsEstermannCentralPoint t)) *
        -Complex.cos ((Real.pi : ℂ) * bblsEstermannCentralPoint t) =
      -((q : ℂ) ^ (2 : ℂ) * (2 * Real.pi : ℂ) ^ (-2 : ℂ) *
        bblsEstermannCentralPoint t ^ 2) *
        (bblsEstermannClassicalFactor q (bblsEstermannCentralPoint t) *
          Complex.cos ((Real.pi : ℂ) * bblsEstermannCentralPoint t)) by
        ring]
  simp only [norm_neg, norm_mul, norm_pow]
  simp
  have hb : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hbpow : ‖(2 * (Real.pi : ℂ)) ^ (-2 : ℂ)‖ ≤ 1 := by
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by
      push_cast
      rfl]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos
      (by positivity : 0 < 2 * Real.pi)]
    exact Real.rpow_le_one_of_one_le_of_nonpos hb (by norm_num)
  have hf := norm_bblsEstermannClassicalFactor_mul_cos_central_le q t
  have hf' :
      ‖bblsEstermannClassicalFactor q (bblsEstermannCentralPoint t)‖ *
        ‖Complex.cos ((Real.pi : ℂ) * bblsEstermannCentralPoint t)‖ ≤
          1 := by
    simpa only [norm_mul] using hf
  have hz := norm_bblsEstermannCentralPoint_le t
  calc
    (q : ℝ) ^ 2 * ‖(2 * (Real.pi : ℂ)) ^ (-2 : ℂ)‖ *
        ‖bblsEstermannCentralPoint t‖ ^ 2 *
        (‖bblsEstermannClassicalFactor q
          (bblsEstermannCentralPoint t)‖ *
            ‖Complex.cos ((Real.pi : ℂ) *
              bblsEstermannCentralPoint t)‖) ≤
      (q : ℝ) ^ 2 * 1 * (1 + |t|) ^ 2 * 1 := by gcongr
    _ = (q : ℝ) ^ 2 * (1 + |t|) ^ 2 := by ring

/-! ## The complete active row -/

/-- Gamma recurrence rewrites the active reflected weight in its most useful
global form away from zero. -/
theorem bblsActiveReflectedWeight_div_eq_Gamma_neg_mul_cpow
    {damping : ℝ} {s : ℂ} (hs : s ≠ 0) :
    bblsActiveReflectedWeight damping s / s =
      Complex.Gamma (-s) * (damping : ℂ) ^ s := by
  have hneg : -s ≠ 0 := neg_ne_zero.mpr hs
  have hrec := Complex.Gamma_add_one (-s) hneg
  have harg : -s + 1 = 1 - s := by ring
  rw [harg] at hrec
  unfold bblsActiveReflectedWeight
  rw [hrec]
  field_simp [hs]

theorem one_le_norm_bblsEstermannThreeHalfPoint (t : ℝ) :
    1 ≤ ‖bblsEstermannThreeHalfPoint t‖ := by
  calc
    (1 : ℝ) ≤ |(bblsEstermannThreeHalfPoint t).re| := by
      norm_num [bblsEstermannThreeHalfPoint]
    _ ≤ ‖bblsEstermannThreeHalfPoint t‖ := Complex.abs_re_le_norm _

/-- The remaining active Gamma factor retains the half-line exponential
decay. -/
theorem norm_Gamma_neg_bblsEstermannThreeHalfPoint_le (t : ℝ) :
    ‖Complex.Gamma (-bblsEstermannThreeHalfPoint t)‖ ≤
      2 * gammaHalfMajorant t := by
  let s := bblsEstermannThreeHalfPoint t
  have hs0 : -s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [s, bblsEstermannThreeHalfPoint] at hre
  have hrec := Complex.Gamma_add_one (-s) hs0
  have harg : -s + 1 = bblsEstermannLeftPoint (-t) := by
    unfold s bblsEstermannThreeHalfPoint bblsEstermannLeftPoint
    push_cast
    ring
  rw [harg] at hrec
  have hnorm := congrArg norm hrec
  rw [norm_mul, norm_neg] at hnorm
  have hsone : 1 ≤ ‖s‖ := one_le_norm_bblsEstermannThreeHalfPoint t
  have hleft := norm_Gamma_bblsEstermannLeftPoint_le (-t)
  have heven : gammaHalfMajorant (-t) = gammaHalfMajorant t := by
    simp [gammaHalfMajorant]
  rw [heven] at hleft
  nlinarith [norm_nonneg (Complex.Gamma (-s))]

/-- Exact dual expression for the active row at `Re(s)=3/2`. -/
theorem bblsActiveReflectedExpression_threeHalf_eq_dual
    {damping : ℝ}
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q) (t : ℝ) :
    bblsActiveReflectedExpression damping a q
        (bblsEstermannThreeHalfPoint t) =
      Complex.Gamma (-bblsEstermannThreeHalfPoint t) *
        (damping : ℂ) ^ (bblsEstermannThreeHalfPoint t) *
        (bblsEstermannClassicalFactor q
            (bblsEstermannThreeHalfPoint t) *
          bblsEstermannHurwitzContinuation
            (bblsEstermannInverseNumerator a q haq) q
            (bblsEstermannThreeHalfPoint t) +
         (bblsEstermannClassicalFactor q
            (bblsEstermannThreeHalfPoint t) *
              Complex.cos ((Real.pi : ℂ) *
                bblsEstermannThreeHalfPoint t)) *
          bblsEstermannHurwitzContinuation
            (bblsEstermannNegativeInverseNumerator a q haq) q
            (bblsEstermannThreeHalfPoint t)) := by
  have hs0 : bblsEstermannThreeHalfPoint t ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [bblsEstermannThreeHalfPoint] at hre
  have hsneg : ∀ n : ℕ, bblsEstermannThreeHalfPoint t ≠ -n := by
    intro n h
    have hre := congrArg Complex.re h
    norm_num [bblsEstermannThreeHalfPoint] at hre
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hs1 : bblsEstermannThreeHalfPoint t ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [bblsEstermannThreeHalfPoint] at hre
  unfold bblsActiveReflectedExpression
  rw [bblsActiveReflectedWeight_div_eq_Gamma_neg_mul_cpow hs0]
  rw [bblsEstermannHurwitzContinuation_one_sub_classical_nat
    a q haq hsneg hs1]
  ring

/-- The unconditional modulus-explicit row bound at `Re(s)=3/2`. -/
theorem norm_bblsActiveReflectedExpression_threeHalf_le
    {damping : ℝ} (hdamping : 0 < damping)
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q) (t : ℝ) :
    ‖bblsActiveReflectedExpression damping a q
        (bblsEstermannThreeHalfPoint t)‖ ≤
      (4 * Real.sqrt (2 * Real.pi) * bblsThreeHalfDirichletMajorant) *
        (q : ℝ) ^ 2 * damping ^ (3 / 2 : ℝ) *
        bblsPolynomialExponentialMajorant 2 (Real.pi / 2) t := by
  rw [bblsActiveReflectedExpression_threeHalf_eq_dual
    a q haq t]
  let s := bblsEstermannThreeHalfPoint t
  let G := Complex.Gamma (-s)
  let P := bblsEstermannHurwitzContinuation
    (bblsEstermannInverseNumerator a q haq) q s
  let M := bblsEstermannHurwitzContinuation
    (bblsEstermannNegativeInverseNumerator a q haq) q s
  let F := bblsEstermannClassicalFactor q s
  let C := Complex.cos ((Real.pi : ℂ) * s)
  have hG : ‖G‖ ≤ 2 * gammaHalfMajorant t :=
    norm_Gamma_neg_bblsEstermannThreeHalfPoint_le t
  have hd : ‖(damping : ℂ) ^ s‖ = damping ^ (3 / 2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hdamping]
    norm_num [s, bblsEstermannThreeHalfPoint]
  have hF : ‖F‖ ≤ (q : ℝ) ^ 2 * (1 + |t|) ^ 2 :=
    norm_bblsEstermannClassicalFactor_threeHalf_le q t
  have hFC : ‖F * C‖ ≤ (q : ℝ) ^ 2 * (1 + |t|) ^ 2 :=
    norm_bblsEstermannClassicalFactor_mul_cos_threeHalf_le q t
  have hP : ‖P‖ ≤ bblsThreeHalfDirichletMajorant :=
    norm_bblsEstermannHurwitzContinuation_threeHalf_le _ q t
  have hM : ‖M‖ ≤ bblsThreeHalfDirichletMajorant :=
    norm_bblsEstermannHurwitzContinuation_threeHalf_le _ q t
  have hK : 0 ≤ bblsThreeHalfDirichletMajorant :=
    bblsThreeHalfDirichletMajorant_nonneg
  have hgamma : 0 ≤ gammaHalfMajorant t := by
    unfold gammaHalfMajorant
    positivity
  have hq : 0 ≤ (q : ℝ) ^ 2 := by positivity
  have ht : 0 ≤ (1 + |t|) ^ 2 := by positivity
  have hdpow : 0 ≤ damping ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg hdamping.le _
  change ‖G * (damping : ℂ) ^ s * (F * P + (F * C) * M)‖ ≤ _
  calc
    ‖G * (damping : ℂ) ^ s * (F * P + (F * C) * M)‖ ≤
      ‖G‖ * ‖(damping : ℂ) ^ s‖ *
        (‖F‖ * ‖P‖ + ‖F * C‖ * ‖M‖) := by
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [norm_mul] using
          norm_add_le (F * P) ((F * C) * M))
        (mul_nonneg (norm_nonneg G)
          (norm_nonneg ((damping : ℂ) ^ s)))
    _ ≤ (2 * gammaHalfMajorant t) * damping ^ (3 / 2 : ℝ) *
        (((q : ℝ) ^ 2 * (1 + |t|) ^ 2) *
            bblsThreeHalfDirichletMajorant +
          ((q : ℝ) ^ 2 * (1 + |t|) ^ 2) *
            bblsThreeHalfDirichletMajorant) := by
      rw [hd]
      gcongr
    _ = (4 * Real.sqrt (2 * Real.pi) *
          bblsThreeHalfDirichletMajorant) *
        (q : ℝ) ^ 2 * damping ^ (3 / 2 : ℝ) *
        bblsPolynomialExponentialMajorant 2 (Real.pi / 2) t := by
      unfold gammaHalfMajorant bblsPolynomialExponentialMajorant
      ring

/-! ## Canonical H15 instantiation -/

/-- A fully constructed positive-line row-growth package for the actual H15
family.  Its modulus exponent `2` is the quantitative output of the
functional equation. -/
noncomputable def h15ThreeHalfPositiveLineRowGrowth :
    H15PositiveLineRowGrowth where
  σ := 3 / 2
  sigma_pos := by norm_num
  sigma_lt_two := by norm_num
  modulusExponent := 2
  tExponent := 2
  constant := 4 * Real.sqrt (2 * Real.pi) *
    bblsThreeHalfDirichletMajorant
  constant_nonneg := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      bblsThreeHalfDirichletMajorant_nonneg
  bound n i t := by
    have hrow := norm_bblsActiveReflectedExpression_threeHalf_le
      (h15ContourDamping_pos n)
      (h15LaurentRow i).numerator (h15LaurentRow i).denominator
      (h15LaurentRow i).coprime t
    have hdamp : h15ContourDamping n ^ (3 / 2 : ℝ) ≤
        (1 / ((n + 1 : ℕ) : ℝ)) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow (le_of_lt (h15ContourDamping_pos n))
        (h15ContourDamping_le_one_div n) (by norm_num)
    have hprofile :
        0 ≤ bblsPolynomialExponentialMajorant 2 (Real.pi / 2) t := by
      unfold bblsPolynomialExponentialMajorant
      positivity
    have hconstant :
        0 ≤ 4 * Real.sqrt (2 * Real.pi) *
          bblsThreeHalfDirichletMajorant := by
      exact mul_nonneg
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
        bblsThreeHalfDirichletMajorant_nonneg
    have hreplace :
        (4 * Real.sqrt (2 * Real.pi) *
              bblsThreeHalfDirichletMajorant) *
            ((h15LaurentRow i).denominator : ℝ) ^ 2 *
            h15ContourDamping n ^ (3 / 2 : ℝ) *
            bblsPolynomialExponentialMajorant 2 (Real.pi / 2) t ≤
          (4 * Real.sqrt (2 * Real.pi) *
              bblsThreeHalfDirichletMajorant) *
            ((h15LaurentRow i).denominator : ℝ) ^ 2 *
            (1 / ((n + 1 : ℕ) : ℝ)) ^ (3 / 2 : ℝ) *
            bblsPolynomialExponentialMajorant 2 (Real.pi / 2) t := by
      apply mul_le_mul_of_nonneg_right _ hprofile
      apply mul_le_mul_of_nonneg_left hdamp
      exact mul_nonneg hconstant (by positivity)
    simpa [bblsEstermannThreeHalfPoint, mul_comm] using
      hrow.trans hreplace

/-- The resulting exact pointwise bound for the complete finite H15
aggregate. -/
theorem norm_h15ActiveContourAggregate_threeHalf_le
    (n : ℕ) (t : ℝ) :
    ‖h15ActiveContourAggregate n
        ((3 / 2 : ℝ) + (t : ℂ) * I)‖ ≤
      h15ThreeHalfPositiveLineRowGrowth.aggregateMajorant n t := by
  exact h15ThreeHalfPositiveLineRowGrowth
    |>.norm_h15ActiveContourAggregate_le_aggregateMajorant n t

/-- Every finite H15 aggregate is unconditionally integrable on the
three-halves line.  Uniformity in the cutoff is a separate question. -/
theorem integrable_h15ActiveContourAggregate_threeHalf (n : ℕ) :
    Integrable (fun t : ℝ =>
      h15ActiveContourAggregate n
        ((3 / 2 : ℝ) + (t : ℂ) * I)) := by
  have hmajorant :=
    h15ThreeHalfPositiveLineRowGrowth.integrable_aggregateMajorant n
  have hcontinuous : Continuous (fun t : ℝ =>
      h15ActiveContourAggregate n
        ((3 / 2 : ℝ) + (t : ℂ) * I)) :=
    continuous_h15ActiveContourAggregate_vertical n (3 / 2)
      (by norm_num) (by norm_num)
  apply hmajorant.mono' hcontinuous.aestronglyMeasurable
  filter_upwards with t
  simpa [Real.norm_eq_abs,
    abs_of_nonneg
      (h15ThreeHalfPositiveLineRowGrowth.aggregateMajorant_nonneg n t)] using
    norm_h15ActiveContourAggregate_threeHalf_le n t

/-- The exact remaining absolute-value gate on this line. -/
abbrev H15ThreeHalfAbsoluteCutoffBudget : Type :=
  h15ThreeHalfPositiveLineRowGrowth.CutoffBudget

/-- Supplying the remaining arithmetic budget produces the fixed-line
integrable majorant required for the right edge. -/
theorem h15ActiveIntegrableMajorantAt_threeHalf
    (B : H15ThreeHalfAbsoluteCutoffBudget) :
    H15ActiveIntegrableMajorantAt (3 / 2) := by
  simpa [h15ThreeHalfPositiveLineRowGrowth] using
    h15ThreeHalfPositiveLineRowGrowth
      |>.activeIntegrableMajorantAt_of_cutoffBudget B

end NBMellinTools.NB12
