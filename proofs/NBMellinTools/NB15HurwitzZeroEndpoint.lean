/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB15RationalSineEndpoint
import NBMellinTools.NB12BBLSHurwitzDecomposition

/-!
# Rational Hurwitz zeta at zero

The rational sine endpoint supplies the `s = 0` Hurwitz value omitted from
Mathlib's general negative-integer theorem.  It is then substituted into the
actual active BBLS finite Hurwitz continuation.
-/

open Complex HurwitzZeta ZMod
open scoped BigOperators

namespace NBMellinTools.NB15

open NBMellinTools.NB12

/-- Periodic first Bernoulli value in the convention of Hurwitz zeta. -/
noncomputable def periodicBernoulliOneValue
    {q : ℕ} [NeZero q] (j : ZMod q) : ℂ :=
  if j = 0 then -(1 : ℂ) / 2
  else (1 : ℂ) / 2 - (j.val : ℂ) / (q : ℂ)

theorem hurwitzZeta_zero_at_zero_residue
    (q : ℕ) [NeZero q] :
    HurwitzZeta.hurwitzZeta (ZMod.toAddCircle (0 : ZMod q)) 0 =
      periodicBernoulliOneValue (0 : ZMod q) := by
  simp [periodicBernoulliOneValue, HurwitzZeta.hurwitzZeta_zero,
    riemannZeta_zero]

/-- The missing nonzero rational Hurwitz endpoint, proved from the analytic
rational sine endpoint. -/
theorem hurwitzZeta_rational_apply_zero_of_ne_zero
    {q : ℕ} [NeZero q] (j : ZMod q) (hj : j ≠ 0) :
    HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) 0 =
      periodicBernoulliOneValue j := by
  rw [HurwitzZeta.hurwitzZeta]
  rw [HurwitzZeta.hurwitzZetaEven_apply_zero,
    if_neg (ZMod.toAddCircle_eq_zero.not.mpr hj), zero_add]
  have hs : ∀ n : ℕ, (1 : ℂ) ≠ -n := by
    intro n hn
    have hre := congrArg Complex.re hn
    norm_num at hre
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hodd := HurwitzZeta.hurwitzZetaOdd_one_sub
    (ZMod.toAddCircle j) hs
  norm_num [Complex.cpow_neg] at hodd
  rw [hodd, sinZeta_rational_apply_one j hj]
  simp only [periodicBernoulliOneValue, if_neg hj]
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-- Complete rational Hurwitz value at zero. -/
theorem hurwitzZeta_rational_apply_zero
    {q : ℕ} [NeZero q] (j : ZMod q) :
    HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) 0 =
      periodicBernoulliOneValue j := by
  by_cases hj : j = 0
  · subst j
    exact hurwitzZeta_zero_at_zero_residue q
  · exact hurwitzZeta_rational_apply_zero_of_ne_zero j hj

/-- The finite Bernoulli expression produced by the active double Hurwitz
continuation at zero. -/
noncomputable def bblsEstermannBernoulliFiniteValue
    (a q : ℕ) [NeZero q] : ℂ :=
  ∑ j : ZMod q,
    (∑ k : ZMod q,
      bblsEstermannResiduePhase a j k * periodicBernoulliOneValue k) *
      periodicBernoulliOneValue j

/-- The genuine active Hurwitz--Estermann continuation at zero is exactly
the finite Bernoulli double sum. -/
theorem bblsEstermannHurwitzContinuation_zero_eq_bernoulliFinite
    (a q : ℕ) [NeZero q] :
    bblsEstermannHurwitzContinuation a q 0 =
      bblsEstermannBernoulliFiniteValue a q := by
  rw [bblsEstermannHurwitzContinuation_eq_finiteSum]
  unfold bblsEstermannHurwitzFiniteSum
    bblsEstermannBernoulliFiniteValue
  simp only [neg_zero, cpow_zero, one_mul]
  simp_rw [hurwitzZeta_rational_apply_zero]

/-- Natural representative of the inverse residue used by the active H15
rows. -/
noncomputable def inverseResidue (a q : ℕ) [NeZero q] : ℕ :=
  ((a : ZMod q)⁻¹).val

theorem inverseResidue_mul_mod_eq_one
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q) :
    ((inverseResidue a q * a : ℕ) : ZMod q) = 1 := by
  simpa [inverseResidue] using ZMod.val_inv_mul hcop

/-- Genuine inverse-frequency Estermann value, still represented as a finite
Bernoulli sum.  The next theorem must evaluate this finite sum as a Vasyunin
cotangent row. -/
theorem bblsInverseEstermann_zero_eq_bernoulliFinite
    (a q : ℕ) [NeZero q] :
    bblsEstermannHurwitzContinuation (inverseResidue a q) q 0 =
      bblsEstermannBernoulliFiniteValue (inverseResidue a q) q :=
  bblsEstermannHurwitzContinuation_zero_eq_bernoulliFinite _ _

end NBMellinTools.NB15
