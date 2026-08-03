/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSEstermannDualCollapse

/-!
# NB12m: Archimedean vertical kernel after Estermann duality

This file proves the exact central-line bounds supplied by the Gamma and
cosine factors in the classical Estermann functional equation.  It also
includes the extra Gamma factor from the shifted Abel--Mellin integrand on
the left line `Re(w) = -1/2`.

The resulting majorants are exponentially integrable.  What remains open is
a polynomial vertical-growth theorem for the two rational Estermann twists;
that missing arithmetic input is stated explicitly at the end of the file.
-/

open scoped BigOperators Topology LSeries.notation
open Complex MeasureTheory Set

namespace NBMellinTools.NB12

/-! ## Central cosine and hyperbolic comparison -/

/-- The central point used on the dual side. -/
noncomputable def bblsEstermannCentralPoint (t : ℝ) : ℂ :=
  (1 / 2 : ℝ) + Complex.I * t

/-- The corresponding left Mellin line, so that `s = -w` after replacing
`t` by `-t`. -/
noncomputable def bblsEstermannLeftPoint (t : ℝ) : ℂ :=
  (-1 / 2 : ℝ) + Complex.I * t

/-- Exact cosine value on the critical line. -/
theorem cos_pi_mul_bblsEstermannCentralPoint (t : ℝ) :
    Complex.cos ((Real.pi : ℂ) * bblsEstermannCentralPoint t) =
      -(Real.sinh (Real.pi * t) : ℂ) * Complex.I := by
  rw [show (Real.pi : ℂ) * bblsEstermannCentralPoint t =
      (Real.pi / 2 : ℂ) + (Real.pi * t : ℂ) * Complex.I by
        unfold bblsEstermannCentralPoint
        push_cast
        ring]
  rw [Complex.cos_add_mul_I]
  rw [show Complex.cos ((Real.pi : ℂ) / 2) = 0 by
      have h : (Real.pi : ℂ) / 2 = ((Real.pi / 2 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [h, ← Complex.ofReal_cos]
      norm_num,
    show Complex.sin ((Real.pi : ℂ) / 2) = 1 by
      have h : (Real.pi : ℂ) / 2 = ((Real.pi / 2 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [h, ← Complex.ofReal_sin]
      norm_num]
  simp [Complex.ofReal_sinh]

/-- Exact cosine norm on the critical line. -/
theorem norm_cos_pi_mul_bblsEstermannCentralPoint (t : ℝ) :
    ‖Complex.cos ((Real.pi : ℂ) * bblsEstermannCentralPoint t)‖ =
      |Real.sinh (Real.pi * t)| := by
  rw [cos_pi_mul_bblsEstermannCentralPoint]
  simp only [norm_mul, norm_neg, norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs]

/-- The elementary hyperbolic inequality needed for cancellation between
Gamma decay and cosine growth. -/
theorem abs_sinh_le_cosh (x : ℝ) : |Real.sinh x| ≤ Real.cosh x := by
  have hcosh := Real.cosh_pos x
  have hsq := Real.cosh_sq_sub_sinh_sq x
  have habsSq : |Real.sinh x| ^ 2 = Real.sinh x ^ 2 := sq_abs _
  nlinarith [abs_nonneg (Real.sinh x)]

/-! ## The classical factor on the critical line -/

/-- Exact norm of the scalar Estermann factor on `Re(s)=1/2`. -/
theorem norm_bblsEstermannClassicalFactor_central
    (q : ℕ) [NeZero q] (t : ℝ) :
    ‖bblsEstermannClassicalFactor q (bblsEstermannCentralPoint t)‖ =
      1 / Real.cosh (Real.pi * t) := by
  have hq : 0 < q := NeZero.pos q
  have hbase : 0 < 2 * Real.pi := by positivity
  unfold bblsEstermannClassicalFactor bblsEstermannCentralPoint
  rw [norm_mul, norm_mul, norm_mul, norm_pow]
  rw [Complex.norm_natCast_cpow_of_pos hq]
  rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by
    push_cast
    rfl]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hbase]
  have hqexp :
      (2 * ((1 / 2 : ℝ) + Complex.I * t) - 1 : ℂ).re = 0 := by
    norm_num
  have hbaseexp :
      (-2 * ((1 / 2 : ℝ) + Complex.I * t) : ℂ).re = -1 := by
    norm_num
  rw [hqexp, hbaseexp, Real.rpow_zero, Real.rpow_neg_one]
  rw [norm_Gamma_half_add_I_mul_sq]
  norm_num
  have hc : Real.cosh (Real.pi * t) ≠ 0 := (Real.cosh_pos _).ne'
  field_simp [Real.pi_ne_zero, hc]

/-- The cosine-weighted scalar is uniformly bounded by one: the exponential
growth of cosine is exactly cancelled by the squared Gamma factor. -/
theorem norm_bblsEstermannClassicalFactor_mul_cos_central_le
    (q : ℕ) [NeZero q] (t : ℝ) :
    ‖bblsEstermannClassicalFactor q (bblsEstermannCentralPoint t) *
        Complex.cos ((Real.pi : ℂ) * bblsEstermannCentralPoint t)‖ ≤ 1 := by
  rw [norm_mul, norm_bblsEstermannClassicalFactor_central,
    norm_cos_pi_mul_bblsEstermannCentralPoint]
  have hc : 0 < Real.cosh (Real.pi * t) := Real.cosh_pos _
  simpa [one_div, div_eq_mul_inv, mul_comm] using
    (div_le_one hc).2 (abs_sinh_le_cosh (Real.pi * t))

/-- The unweighted scalar retains the full hyperbolic decay. -/
theorem norm_bblsEstermannClassicalFactor_central_le_one
    (q : ℕ) [NeZero q] (t : ℝ) :
    ‖bblsEstermannClassicalFactor q (bblsEstermannCentralPoint t)‖ ≤ 1 := by
  rw [norm_bblsEstermannClassicalFactor_central]
  exact (div_le_one (Real.cosh_pos _)).2 (Real.one_le_cosh _)

/-! ## The additional Abel--Mellin Gamma factor -/

/-- Recurrence relation between Gamma on the left line and the central
line. -/
theorem Gamma_bblsEstermannCentralPoint_eq_left_mul
    (t : ℝ) :
    Complex.Gamma (bblsEstermannCentralPoint t) =
      bblsEstermannLeftPoint t *
        Complex.Gamma (bblsEstermannLeftPoint t) := by
  have hw : bblsEstermannLeftPoint t ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [bblsEstermannLeftPoint] at hre
  have hrec := Complex.Gamma_add_one (bblsEstermannLeftPoint t) hw
  convert hrec using 1
  unfold bblsEstermannCentralPoint bblsEstermannLeftPoint
  push_cast
  ring_nf

/-- The left-line linear factor has norm at least `1/2`. -/
theorem one_half_le_norm_bblsEstermannLeftPoint (t : ℝ) :
    (1 / 2 : ℝ) ≤ ‖bblsEstermannLeftPoint t‖ := by
  calc
    (1 / 2 : ℝ) = |(bblsEstermannLeftPoint t).re| := by
      norm_num [bblsEstermannLeftPoint]
    _ ≤ ‖bblsEstermannLeftPoint t‖ := Complex.abs_re_le_norm _

/-- Gamma on the left line is at most twice Gamma on the central line. -/
theorem norm_Gamma_bblsEstermannLeftPoint_le
    (t : ℝ) :
    ‖Complex.Gamma (bblsEstermannLeftPoint t)‖ ≤
      2 * gammaHalfMajorant t := by
  have hrec := congrArg norm (Gamma_bblsEstermannCentralPoint_eq_left_mul t)
  rw [norm_mul] at hrec
  have hhalf := one_half_le_norm_bblsEstermannLeftPoint t
  have hcentral :
      ‖Complex.Gamma (bblsEstermannCentralPoint t)‖ ≤
        gammaHalfMajorant t := by
    simpa [bblsEstermannCentralPoint] using
      norm_Gamma_half_add_I_mul_le_majorant t
  nlinarith [norm_nonneg (Complex.Gamma (bblsEstermannLeftPoint t))]

/-- Integrable Archimedean majorant after including the left-line Gamma. -/
noncomputable def bblsEstermannLeftArchimedeanMajorant (t : ℝ) : ℝ :=
  2 * gammaHalfMajorant t

theorem integrable_bblsEstermannLeftArchimedeanMajorant :
    Integrable bblsEstermannLeftArchimedeanMajorant := by
  unfold bblsEstermannLeftArchimedeanMajorant
  exact integrable_gammaHalfMajorant.const_mul 2

/-- The more rapidly decaying unweighted dual coefficient. -/
theorem norm_Gamma_left_mul_classicalFactor_central_le
    (q : ℕ) [NeZero q] (t : ℝ) :
    ‖Complex.Gamma (bblsEstermannLeftPoint t) *
        bblsEstermannClassicalFactor q (bblsEstermannCentralPoint t)‖ ≤
      bblsEstermannLeftArchimedeanMajorant t /
        Real.cosh (Real.pi * t) := by
  rw [norm_mul, norm_bblsEstermannClassicalFactor_central]
  unfold bblsEstermannLeftArchimedeanMajorant
  simpa [div_eq_mul_inv] using
    (mul_le_mul_of_nonneg_right
      (norm_Gamma_bblsEstermannLeftPoint_le t)
      (le_of_lt (one_div_pos.mpr (Real.cosh_pos (Real.pi * t)))))

/-- The cosine-weighted dual coefficient still has an integrable Gamma
majorant after the cancellation of one exponential factor. -/
theorem norm_Gamma_left_mul_classicalFactor_mul_cos_central_le
    (q : ℕ) [NeZero q] (t : ℝ) :
    ‖Complex.Gamma (bblsEstermannLeftPoint t) *
        (bblsEstermannClassicalFactor q (bblsEstermannCentralPoint t) *
          Complex.cos ((Real.pi : ℂ) * bblsEstermannCentralPoint t))‖ ≤
      bblsEstermannLeftArchimedeanMajorant t := by
  rw [norm_mul]
  calc
    _ ≤ ‖Complex.Gamma (bblsEstermannLeftPoint t)‖ * 1 :=
      mul_le_mul_of_nonneg_left
        (norm_bblsEstermannClassicalFactor_mul_cos_central_le q t)
        (norm_nonneg _)
    _ ≤ _ := by
      simpa [bblsEstermannLeftArchimedeanMajorant] using
        norm_Gamma_bblsEstermannLeftPoint_le t

/-! ## Honest remaining arithmetic input -/

/-- A polynomial vertical-growth package for the two inverse rational
Estermann twists.  This is the precise input still needed to combine the
integrable Archimedean kernel with the arithmetic factor globally. -/
structure BBLSEstermannCentralPolynomialGrowth where
  exponent : ℕ
  qExponent : ℕ
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  bound : ∀ (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q) (t : ℝ),
    ‖bblsEstermannHurwitzContinuation
        (bblsEstermannInverseNumerator a q haq) q
        (bblsEstermannCentralPoint t)‖ +
      ‖bblsEstermannHurwitzContinuation
        (bblsEstermannNegativeInverseNumerator a q haq) q
        (bblsEstermannCentralPoint t)‖ ≤
      constant * (q : ℝ) ^ qExponent * (1 + |t|) ^ exponent

/-- The complete left-line dual expression after inserting the classical
functional equation, but before the Abel factor `delta^(-w)`. -/
noncomputable def bblsEstermannLeftDualExpression
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q) (t : ℝ) : ℂ :=
  Complex.Gamma (bblsEstermannLeftPoint t) *
    bblsEstermannClassicalFactor q (bblsEstermannCentralPoint t) *
      (bblsEstermannHurwitzContinuation
          (bblsEstermannInverseNumerator a q haq) q
          (bblsEstermannCentralPoint t) +
        Complex.cos ((Real.pi : ℂ) * bblsEstermannCentralPoint t) *
          bblsEstermannHurwitzContinuation
            (bblsEstermannNegativeInverseNumerator a q haq) q
            (bblsEstermannCentralPoint t))

/-- Exact transfer bound: all Archimedean growth has been reduced to the
integrable left Gamma majorant, while the two arithmetic twists remain
inside one positive norm sum. -/
theorem norm_bblsEstermannLeftDualExpression_le
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q) (t : ℝ) :
    ‖bblsEstermannLeftDualExpression a q haq t‖ ≤
      bblsEstermannLeftArchimedeanMajorant t *
        (‖bblsEstermannHurwitzContinuation
            (bblsEstermannInverseNumerator a q haq) q
            (bblsEstermannCentralPoint t)‖ +
          ‖bblsEstermannHurwitzContinuation
            (bblsEstermannNegativeInverseNumerator a q haq) q
            (bblsEstermannCentralPoint t)‖) := by
  let P := bblsEstermannHurwitzContinuation
    (bblsEstermannInverseNumerator a q haq) q
    (bblsEstermannCentralPoint t)
  let M := bblsEstermannHurwitzContinuation
    (bblsEstermannNegativeInverseNumerator a q haq) q
    (bblsEstermannCentralPoint t)
  let G := Complex.Gamma (bblsEstermannLeftPoint t)
  let F := bblsEstermannClassicalFactor q (bblsEstermannCentralPoint t)
  let C := Complex.cos ((Real.pi : ℂ) * bblsEstermannCentralPoint t)
  have hP : ‖G * F‖ ≤
      bblsEstermannLeftArchimedeanMajorant t /
        Real.cosh (Real.pi * t) := by
    exact norm_Gamma_left_mul_classicalFactor_central_le q t
  have hM : ‖G * (F * C)‖ ≤
      bblsEstermannLeftArchimedeanMajorant t := by
    exact norm_Gamma_left_mul_classicalFactor_mul_cos_central_le q t
  have hcoshInv : 1 / Real.cosh (Real.pi * t) ≤ 1 :=
    (div_le_one (Real.cosh_pos _)).2 (Real.one_le_cosh _)
  have hmajorant : 0 ≤ bblsEstermannLeftArchimedeanMajorant t := by
    unfold bblsEstermannLeftArchimedeanMajorant gammaHalfMajorant
    positivity
  change ‖G * F * (P + C * M)‖ ≤ _
  calc
    ‖G * F * (P + C * M)‖ = ‖(G * F) * P + (G * (F * C)) * M‖ := by
      congr 1
      ring
    _ ≤ ‖G * F‖ * ‖P‖ + ‖G * (F * C)‖ * ‖M‖ := by
      simpa only [norm_mul] using
        norm_add_le ((G * F) * P) ((G * (F * C)) * M)
    _ ≤ (bblsEstermannLeftArchimedeanMajorant t /
          Real.cosh (Real.pi * t)) * ‖P‖ +
        bblsEstermannLeftArchimedeanMajorant t * ‖M‖ :=
      add_le_add
        (mul_le_mul_of_nonneg_right hP (norm_nonneg P))
        (mul_le_mul_of_nonneg_right hM (norm_nonneg M))
    _ ≤ bblsEstermannLeftArchimedeanMajorant t * (‖P‖ + ‖M‖) := by
      have hfirst :
          bblsEstermannLeftArchimedeanMajorant t /
              Real.cosh (Real.pi * t) ≤
            bblsEstermannLeftArchimedeanMajorant t := by
        calc
          _ = bblsEstermannLeftArchimedeanMajorant t *
              (1 / Real.cosh (Real.pi * t)) := by ring
          _ ≤ bblsEstermannLeftArchimedeanMajorant t * 1 :=
            mul_le_mul_of_nonneg_left hcoshInv hmajorant
          _ = _ := mul_one _
      calc
        _ ≤ bblsEstermannLeftArchimedeanMajorant t * ‖P‖ +
            bblsEstermannLeftArchimedeanMajorant t * ‖M‖ :=
          add_le_add
            (mul_le_mul_of_nonneg_right hfirst (norm_nonneg P)) le_rfl
        _ = _ := by ring

/-- A polynomial-growth package immediately gives a completely explicit
pointwise majorant for the shifted dual expression. -/
theorem norm_bblsEstermannLeftDualExpression_le_of_polynomialGrowth
    (H : BBLSEstermannCentralPolynomialGrowth)
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q) (t : ℝ) :
    ‖bblsEstermannLeftDualExpression a q haq t‖ ≤
      H.constant * (q : ℝ) ^ H.qExponent *
        bblsEstermannLeftArchimedeanMajorant t *
        (1 + |t|) ^ H.exponent := by
  calc
    _ ≤ bblsEstermannLeftArchimedeanMajorant t *
        (‖bblsEstermannHurwitzContinuation
            (bblsEstermannInverseNumerator a q haq) q
            (bblsEstermannCentralPoint t)‖ +
          ‖bblsEstermannHurwitzContinuation
            (bblsEstermannNegativeInverseNumerator a q haq) q
            (bblsEstermannCentralPoint t)‖) :=
      norm_bblsEstermannLeftDualExpression_le a q haq t
    _ ≤ bblsEstermannLeftArchimedeanMajorant t *
        (H.constant * (q : ℝ) ^ H.qExponent *
          (1 + |t|) ^ H.exponent) :=
      mul_le_mul_of_nonneg_left (H.bound a q haq t) (by
        unfold bblsEstermannLeftArchimedeanMajorant gammaHalfMajorant
        positivity)
    _ = _ := by ring

end NBMellinTools.NB12
