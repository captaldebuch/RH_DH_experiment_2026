/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSHurwitzFunctionalEquation

/-!
# NB12l: collapse of the finite Fourier dual to rational Estermann twists

The normalized two-level functional equation still contains congruence
`LFunction`s of DFT-transformed Hurwitz coefficients.  This file expands
those finite objects and identifies them exactly with the two rational
Estermann continuations having inverse numerators.

This is finite algebra.  No contour shift, growth estimate, or signed H15
cancellation is asserted.
-/

open scoped BigOperators LSeries.notation
open AddChar Complex LSeries HurwitzZeta ZMod

namespace NBMellinTools.NB12

/-! ## A numerator living directly in `ZMod q` -/

/-- The same finite double-Hurwitz continuation, with its numerator supplied
directly as a residue class. -/
noncomputable def bblsEstermannZModContinuation
    {q : ℕ} [NeZero q] (b : ZMod q) (s : ℂ) : ℂ :=
  ZMod.LFunction
    (fun j : ZMod q =>
      ZMod.LFunction
        (fun k : ZMod q => ZMod.stdAddChar (b * j * k)) s)
    s

/-- A natural numerator and its residue-class version define the same
continuation. -/
theorem bblsEstermannZModContinuation_natCast
    (a q : ℕ) [NeZero q] (s : ℂ) :
    bblsEstermannZModContinuation (q := q) (a : ZMod q) s =
      bblsEstermannHurwitzContinuation a q s := by
  rfl

/-- The inverse numerator as an actual residue class. -/
noncomputable def bblsEstermannInverseResidue
    (a : ℕ) {q : ℕ} (haq : Nat.Coprime a q) : ZMod q :=
  ((ZMod.unitOfCoprime a haq)⁻¹ : (ZMod q)ˣ).val

/-- Canonical natural representative of the inverse residue. -/
noncomputable def bblsEstermannInverseNumerator
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q) : ℕ :=
  (bblsEstermannInverseResidue a haq).val

/-- Canonical natural representative of the negative inverse residue. -/
noncomputable def bblsEstermannNegativeInverseNumerator
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q) : ℕ :=
  (-bblsEstermannInverseResidue a haq).val

@[simp] theorem bblsEstermannInverseNumerator_cast
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q) :
    (bblsEstermannInverseNumerator a q haq : ZMod q) =
      bblsEstermannInverseResidue a haq := by
  exact ZMod.natCast_zmod_val _

@[simp] theorem bblsEstermannNegativeInverseNumerator_cast
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q) :
    (bblsEstermannNegativeInverseNumerator a q haq : ZMod q) =
      -bblsEstermannInverseResidue a haq := by
  exact ZMod.natCast_zmod_val _

theorem bblsEstermannInverseFrequency_eq_mul
    (a : ℕ) {q : ℕ} (haq : Nat.Coprime a q) (k : ZMod q) :
    bblsEstermannInverseFrequency a haq k =
      bblsEstermannInverseResidue a haq * k := by
  rfl

@[simp] theorem bblsEstermannInverseResidue_mul
    (a : ℕ) {q : ℕ} (haq : Nat.Coprime a q) :
    bblsEstermannInverseResidue a haq * (a : ZMod q) = 1 := by
  unfold bblsEstermannInverseResidue
  rw [← ZMod.coe_unitOfCoprime a haq]
  exact Units.inv_mul _

/-! ## One DFT-Hurwitz row is one inverse rational twist -/

/-- The congruence L-function of a multiplied DFT-Hurwitz row collapses to
one rational Estermann continuation.  The DFT minus sign changes `b` to
`-b`; the factor `q^s` compensates for one rather than two Hurwitz levels. -/
theorem LFunction_dft_bblsEstermannHurwitzCoefficient_mul
    {q : ℕ} [NeZero q] (b : ZMod q) (s : ℂ) :
    ZMod.LFunction
        (fun k : ZMod q =>
          ZMod.dft (bblsEstermannHurwitzCoefficient (q := q) s) (b * k)) s =
      (q : ℂ) ^ s *
        bblsEstermannZModContinuation (q := q) (-b) s := by
  let H : ZMod q → ℂ := bblsEstermannHurwitzCoefficient (q := q) s
  let Q : ℂ := (q : ℂ) ^ (-s)
  have hq : (q : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne q)
  have hpow : (q : ℂ) ^ s * Q = 1 := by
    change (q : ℂ) ^ s * (q : ℂ) ^ (-s) = 1
    rw [← Complex.cpow_add s (-s) hq]
    simp
  unfold bblsEstermannZModContinuation
    bblsEstermannHurwitzCoefficient
  simp only [ZMod.LFunction, ZMod.dft_def, smul_eq_mul]
  change Q *
      (∑ k : ZMod q,
        (∑ j : ZMod q,
          ZMod.stdAddChar (-(j * (b * k))) *
            HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) s) *
          HurwitzZeta.hurwitzZeta (ZMod.toAddCircle k) s) = _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hphase (j k : ZMod q) :
      ZMod.stdAddChar (-(j * (b * k))) =
        ZMod.stdAddChar ((-b) * j * k) := by
    congr 1
    ring
  simp_rw [hphase]
  have hsum :
      (∑ j : ZMod q, ∑ k : ZMod q,
        ZMod.stdAddChar ((-b) * j * k) *
          HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) s *
          HurwitzZeta.hurwitzZeta (ZMod.toAddCircle k) s) =
        ∑ j : ZMod q,
          (∑ k : ZMod q,
            ZMod.stdAddChar ((-b) * j * k) *
              HurwitzZeta.hurwitzZeta (ZMod.toAddCircle k) s) *
            HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) s := by
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsum]
  have hfactor :
      (∑ j : ZMod q,
        (Q * ∑ k : ZMod q,
          ZMod.stdAddChar ((-b) * j * k) *
            HurwitzZeta.hurwitzZeta (ZMod.toAddCircle k) s) *
          HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) s) =
        Q * ∑ j : ZMod q,
          (∑ k : ZMod q,
            ZMod.stdAddChar ((-b) * j * k) *
              HurwitzZeta.hurwitzZeta (ZMod.toAddCircle k) s) *
            HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) s := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hfactor]
  conv_rhs => rw [← mul_assoc, hpow, one_mul]

/-- The reflected multiplied row collapses to the positive inverse twist. -/
theorem LFunction_dft_bblsEstermannHurwitzCoefficient_neg_mul
    {q : ℕ} [NeZero q] (b : ZMod q) (s : ℂ) :
    ZMod.LFunction
        (fun k : ZMod q =>
          ZMod.dft (bblsEstermannHurwitzCoefficient (q := q) s) (-(b * k))) s =
      (q : ℂ) ^ s *
        bblsEstermannZModContinuation (q := q) b s := by
  simpa only [neg_mul, neg_neg] using
    (LFunction_dft_bblsEstermannHurwitzCoefficient_mul
      (q := q) (-b) s)

/-! ## Linearity at the finite congruence level -/

theorem LFunction_linear_combination_bbls
    {q : ℕ} [NeZero q] (A B : ℂ) (f g : ZMod q → ℂ) (s : ℂ) :
    ZMod.LFunction (fun k => A * f k + B * g k) s =
      A * ZMod.LFunction f s + B * ZMod.LFunction g s := by
  unfold ZMod.LFunction
  have hsum :
      (∑ k : ZMod q,
        (A * f k + B * g k) *
          HurwitzZeta.hurwitzZeta (ZMod.toAddCircle k) s) =
        A * (∑ k : ZMod q,
          f k * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle k) s) +
        B * (∑ k : ZMod q,
          g k * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle k) s) := by
    calc
      _ = ∑ k : ZMod q,
          (A * (f k * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle k) s) +
            B * (g k * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle k) s)) := by
            apply Finset.sum_congr rfl
            intro k _
            ring
      _ = (∑ k : ZMod q,
            A * (f k * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle k) s)) +
          ∑ k : ZMod q,
            B * (g k * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle k) s) :=
            Finset.sum_add_distrib
      _ = _ := by rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [hsum]
  ring

/-! ## Collapse of the complete normalized dual coefficient -/

/-- The first outer dual L-function is a linear combination of the negative
and positive inverse rational Estermann twists. -/
theorem LFunction_bblsEstermannOuterDualCoefficient
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q) (s : ℂ) :
    ZMod.LFunction (bblsEstermannOuterDualCoefficient a q haq s) s =
      bblsEstermannOuterPositiveFactor q s *
          ((q : ℂ) ^ s *
            bblsEstermannZModContinuation
              (-bblsEstermannInverseResidue a haq) s) +
        bblsEstermannOuterNegativeFactor q s *
          ((q : ℂ) ^ s *
            bblsEstermannZModContinuation
              (bblsEstermannInverseResidue a haq) s) := by
  unfold bblsEstermannOuterDualCoefficient
  rw [LFunction_linear_combination_bbls]
  simp only [bblsEstermannInverseFrequency_eq_mul]
  rw [LFunction_dft_bblsEstermannHurwitzCoefficient_mul,
    LFunction_dft_bblsEstermannHurwitzCoefficient_neg_mul]

/-- Reflecting the outer coefficient swaps the positive and negative inverse
rational twists. -/
theorem LFunction_bblsEstermannOuterDualCoefficient_comp_neg
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q) (s : ℂ) :
    ZMod.LFunction
        (fun k : ZMod q =>
          bblsEstermannOuterDualCoefficient a q haq s (-k)) s =
      bblsEstermannOuterPositiveFactor q s *
          ((q : ℂ) ^ s *
            bblsEstermannZModContinuation
              (bblsEstermannInverseResidue a haq) s) +
        bblsEstermannOuterNegativeFactor q s *
          ((q : ℂ) ^ s *
            bblsEstermannZModContinuation
              (-bblsEstermannInverseResidue a haq) s) := by
  unfold bblsEstermannOuterDualCoefficient
  rw [LFunction_linear_combination_bbls]
  simp only [bblsEstermannInverseFrequency_eq_mul, mul_neg, neg_neg]
  rw [LFunction_dft_bblsEstermannHurwitzCoefficient_neg_mul,
    LFunction_dft_bblsEstermannHurwitzCoefficient_mul]

/-! ## Correction-compatible dual functional equation -/

/-- Exact functional equation after the remaining dual congruence
L-functions have been collapsed to two rational Estermann continuations.
The formula is intentionally left in exponential form, before any cosine
rewriting, so every sign remains traceable to Mathlib's DFT convention. -/
theorem bblsEstermannHurwitzContinuation_one_sub_dualCollapse
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q) {s : ℂ}
    (hs : ∀ n : ℕ, s ≠ -n) (hs1 : s ≠ 1) :
    bblsEstermannHurwitzContinuation a q (1 - s) =
      (q : ℂ) ^ (s - 1) * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
        (Complex.exp (Real.pi * Complex.I * s / 2) *
            (bblsEstermannOuterPositiveFactor q s *
                ((q : ℂ) ^ s *
                  bblsEstermannZModContinuation
                    (-bblsEstermannInverseResidue a haq) s) +
              bblsEstermannOuterNegativeFactor q s *
                ((q : ℂ) ^ s *
                  bblsEstermannZModContinuation
                    (bblsEstermannInverseResidue a haq) s)) +
          Complex.exp (-Real.pi * Complex.I * s / 2) *
            (bblsEstermannOuterPositiveFactor q s *
                ((q : ℂ) ^ s *
                  bblsEstermannZModContinuation
                    (bblsEstermannInverseResidue a haq) s) +
              bblsEstermannOuterNegativeFactor q s *
                ((q : ℂ) ^ s *
                  bblsEstermannZModContinuation
                    (-bblsEstermannInverseResidue a haq) s))) := by
  rw [bblsEstermannHurwitzContinuation_one_sub_normalized
    a q haq hs hs1]
  rw [LFunction_bblsEstermannOuterDualCoefficient,
    LFunction_bblsEstermannOuterDualCoefficient_comp_neg]

/-! ## Classical cosine form -/

/-- The common scalar in the classical Estermann functional equation. -/
noncomputable def bblsEstermannClassicalFactor
    (q : ℕ) (s : ℂ) : ℂ :=
  2 * (q : ℂ) ^ (2 * s - 1) * (2 * Real.pi : ℂ) ^ (-2 * s) *
    Complex.Gamma s ^ 2

theorem bblsEstermannOuterPositiveFactor_eq
    (q : ℕ) [NeZero q] (s : ℂ) :
    bblsEstermannOuterPositiveFactor q s =
      (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
        Complex.exp (Real.pi * Complex.I * s / 2) := by
  have hq : (q : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne q)
  have hscalar :
      (q : ℂ) ^ (s - 1) * (q : ℂ) ^ (-s) * (q : ℂ) = 1 := by
    calc
      (q : ℂ) ^ (s - 1) * (q : ℂ) ^ (-s) * (q : ℂ) =
          (q : ℂ) ^ ((s - 1) + (-s)) * (q : ℂ) := by
            rw [Complex.cpow_add _ _ hq]
      _ = (q : ℂ) ^ (-(1 : ℂ)) * (q : ℂ) := by
            congr 2
            ring
      _ = 1 := by
            rw [Complex.cpow_neg_one]
            exact inv_mul_cancel₀ hq
  unfold bblsEstermannOuterPositiveFactor
  calc
    _ = ((q : ℂ) ^ (s - 1) * (q : ℂ) ^ (-s) * (q : ℂ)) *
        ((2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
          Complex.exp (Real.pi * Complex.I * s / 2)) := by ring
    _ = _ := by rw [hscalar, one_mul]

theorem bblsEstermannOuterNegativeFactor_eq
    (q : ℕ) [NeZero q] (s : ℂ) :
    bblsEstermannOuterNegativeFactor q s =
      (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
        Complex.exp (-Real.pi * Complex.I * s / 2) := by
  have hq : (q : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne q)
  have hscalar :
      (q : ℂ) ^ (s - 1) * (q : ℂ) ^ (-s) * (q : ℂ) = 1 := by
    calc
      (q : ℂ) ^ (s - 1) * (q : ℂ) ^ (-s) * (q : ℂ) =
          (q : ℂ) ^ ((s - 1) + (-s)) * (q : ℂ) := by
            rw [Complex.cpow_add _ _ hq]
      _ = (q : ℂ) ^ (-(1 : ℂ)) * (q : ℂ) := by
            congr 2
            ring
      _ = 1 := by
            rw [Complex.cpow_neg_one]
            exact inv_mul_cancel₀ hq
  unfold bblsEstermannOuterNegativeFactor
  calc
    _ = ((q : ℂ) ^ (s - 1) * (q : ℂ) ^ (-s) * (q : ℂ)) *
        ((2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
          Complex.exp (-Real.pi * Complex.I * s / 2)) := by ring
    _ = _ := by rw [hscalar, one_mul]

theorem bblsEstermann_halfExponent_mul_neg_eq_one (s : ℂ) :
    Complex.exp (Real.pi * Complex.I * s / 2) *
      Complex.exp (-Real.pi * Complex.I * s / 2) = 1 := by
  rw [← Complex.exp_add]
  have : Real.pi * Complex.I * s / 2 +
      -Real.pi * Complex.I * s / 2 = (0 : ℂ) := by ring
  rw [this, Complex.exp_zero]

theorem bblsEstermann_halfExponent_sq_sum_eq_cos (s : ℂ) :
    Complex.exp (Real.pi * Complex.I * s / 2) ^ 2 +
      Complex.exp (-Real.pi * Complex.I * s / 2) ^ 2 =
        2 * Complex.cos (Real.pi * s) := by
  rw [pow_two, ← Complex.exp_add, pow_two, ← Complex.exp_add]
  have hpos :
      Real.pi * Complex.I * s / 2 + Real.pi * Complex.I * s / 2 =
        (Real.pi * s) * Complex.I := by ring
  have hneg :
      -Real.pi * Complex.I * s / 2 + -Real.pi * Complex.I * s / 2 =
        -(Real.pi * s) * Complex.I := by ring
  rw [hpos, hneg]
  unfold Complex.cos
  ring

/-- The scalar algebra which converts the two-level exponential equation to
the standard cosine combination. -/
theorem bblsEstermann_dual_scalar_identity
    (q : ℕ) [NeZero q] (s P M : ℂ) :
    (q : ℂ) ^ (s - 1) * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
        (Complex.exp (Real.pi * Complex.I * s / 2) *
            (bblsEstermannOuterPositiveFactor q s * ((q : ℂ) ^ s * M) +
              bblsEstermannOuterNegativeFactor q s * ((q : ℂ) ^ s * P)) +
          Complex.exp (-Real.pi * Complex.I * s / 2) *
            (bblsEstermannOuterPositiveFactor q s * ((q : ℂ) ^ s * P) +
              bblsEstermannOuterNegativeFactor q s * ((q : ℂ) ^ s * M))) =
      bblsEstermannClassicalFactor q s *
        (P + Complex.cos (Real.pi * s) * M) := by
  rw [bblsEstermannOuterPositiveFactor_eq,
    bblsEstermannOuterNegativeFactor_eq]
  have hq : (q : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne q)
  have hqpow :
      (q : ℂ) ^ (s - 1) * (q : ℂ) ^ s =
        (q : ℂ) ^ (2 * s - 1) := by
    rw [← Complex.cpow_add _ _ hq]
    congr 1
    ring
  have hbase : (2 * Real.pi : ℂ) ≠ 0 := by
    norm_num [Real.pi_ne_zero]
  have harch :
      (2 * Real.pi : ℂ) ^ (-s) * (2 * Real.pi : ℂ) ^ (-s) =
        (2 * Real.pi : ℂ) ^ (-2 * s) := by
    rw [← Complex.cpow_add _ _ hbase]
    congr 1
    ring
  have hcross := bblsEstermann_halfExponent_mul_neg_eq_one s
  have hcos := bblsEstermann_halfExponent_sq_sum_eq_cos s
  let ep : ℂ := Complex.exp (Real.pi * Complex.I * s / 2)
  let em : ℂ := Complex.exp (-Real.pi * Complex.I * s / 2)
  let A : ℂ := (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s
  have htrig :
      ep * (ep * M + em * P) + em * (ep * P + em * M) =
        2 * (P + Complex.cos (Real.pi * s) * M) := by
    calc
      ep * (ep * M + em * P) + em * (ep * P + em * M) =
          2 * (ep * em) * P + (ep ^ 2 + em ^ 2) * M := by ring
      _ = 2 * (P + Complex.cos (Real.pi * s) * M) := by
        change 2 *
            (Complex.exp (Real.pi * Complex.I * s / 2) *
              Complex.exp (-Real.pi * Complex.I * s / 2)) * P +
            (Complex.exp (Real.pi * Complex.I * s / 2) ^ 2 +
              Complex.exp (-Real.pi * Complex.I * s / 2) ^ 2) * M = _
        rw [hcross, hcos]
        ring
  unfold bblsEstermannClassicalFactor
  calc
    _ = ((q : ℂ) ^ (s - 1) * (q : ℂ) ^ s) * (A * A) *
        (ep * (ep * M + em * P) + em * (ep * P + em * M)) := by
          dsimp [A, ep, em]
          ring
    _ = (q : ℂ) ^ (2 * s - 1) *
        ((2 * Real.pi : ℂ) ^ (-2 * s) * Complex.Gamma s ^ 2) *
          (2 * (P + Complex.cos (Real.pi * s) * M)) := by
            rw [hqpow, htrig]
            change (q : ℂ) ^ (2 * s - 1) *
                (((2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s) *
                  ((2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s)) * _ = _
            rw [show
              ((2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s) *
                  ((2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s) =
                ((2 * Real.pi : ℂ) ^ (-s) *
                  (2 * Real.pi : ℂ) ^ (-s)) * Complex.Gamma s ^ 2 by ring]
            rw [harch]
    _ = 2 * (q : ℂ) ^ (2 * s - 1) *
        (2 * Real.pi : ℂ) ^ (-2 * s) * Complex.Gamma s ^ 2 *
          (P + Complex.cos (Real.pi * s) * M) := by ring

/-- Classical rational Estermann functional equation in cosine form.  The
two dual twists have the inverse residue numerator and its negative. -/
theorem bblsEstermannHurwitzContinuation_one_sub_classical
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q) {s : ℂ}
    (hs : ∀ n : ℕ, s ≠ -n) (hs1 : s ≠ 1) :
    bblsEstermannHurwitzContinuation a q (1 - s) =
      bblsEstermannClassicalFactor q s *
        (bblsEstermannZModContinuation
            (bblsEstermannInverseResidue a haq) s +
          Complex.cos (Real.pi * s) *
            bblsEstermannZModContinuation
              (-bblsEstermannInverseResidue a haq) s) := by
  rw [bblsEstermannHurwitzContinuation_one_sub_dualCollapse
    a q haq hs hs1]
  exact bblsEstermann_dual_scalar_identity q s
    (bblsEstermannZModContinuation
      (bblsEstermannInverseResidue a haq) s)
    (bblsEstermannZModContinuation
      (-bblsEstermannInverseResidue a haq) s)

/-- The same classical functional equation written entirely with the active
natural-numerator Estermann continuation. -/
theorem bblsEstermannHurwitzContinuation_one_sub_classical_nat
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q) {s : ℂ}
    (hs : ∀ n : ℕ, s ≠ -n) (hs1 : s ≠ 1) :
    bblsEstermannHurwitzContinuation a q (1 - s) =
      bblsEstermannClassicalFactor q s *
        (bblsEstermannHurwitzContinuation
            (bblsEstermannInverseNumerator a q haq) q s +
          Complex.cos (Real.pi * s) *
            bblsEstermannHurwitzContinuation
              (bblsEstermannNegativeInverseNumerator a q haq) q s) := by
  rw [bblsEstermannHurwitzContinuation_one_sub_classical
    a q haq hs hs1]
  rw [← bblsEstermannZModContinuation_natCast
      (bblsEstermannInverseNumerator a q haq) q s,
    ← bblsEstermannZModContinuation_natCast
      (bblsEstermannNegativeInverseNumerator a q haq) q s]
  simp

end NBMellinTools.NB12
