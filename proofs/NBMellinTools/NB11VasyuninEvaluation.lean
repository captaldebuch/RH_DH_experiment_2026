/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB10VasyuninReduction
import RiemannHypothesis.Criteria.NymanBeurling.BBLSAutocorrelation

/-!
# NB11: classical pointwise Vasyunin evaluation

This module constructs the `VasyuninGramEvaluation` input isolated in NB10.
Only the rational BBLS period-reduction chain is imported.  Its promoted
source omits the unrelated generic real-parameter Proposition 21 declaration
that carried the sole `sorry` in the historical source file.

The proof has three exact stages:

1. invert the positive-half-line Gram integral;
2. unfold it into rational periodic blocks;
3. apply the proved BBLS rational autocorrelation/cotangent evaluation.

No cancellation or asymptotic decay claim is made here.
-/

open MeasureTheory Set

namespace NBMellinTools.NB11

open NBMellinTools.NB9
open NBMellinTools.NB10

open RH.Criteria.NymanBeurling.VasyuninGram

/-- The active zero-based Gram entry is definitionally the classical positive
denominator entry at `j+1,k+1`. -/
theorem bdGram_eq_classicalGramEntry (j k : ℕ) :
    bdGram j k = baezDuarteGramEntry (j + 1) (k + 1) := by
  unfold bdGram NBMellinTools.NB2.rhoBD baezDuarteGramEntry
  norm_num [Nat.cast_add]

/-- Inversion substitution on the positive half-line, specialized from
Mathlib's `integral_comp_rpow_Ioi` at exponent `-1`. -/
theorem setIntegral_Ioi_inv_substitution (f : ℝ → ℝ) :
    (∫ x in Ioi (0 : ℝ), f (1 / x)) =
      ∫ t in Ioi (0 : ℝ), f t * (1 / t ^ 2) := by
  have hsub := MeasureTheory.integral_comp_rpow_Ioi
    (g := fun y : ℝ => f (1 / y)) (p := (-1 : ℝ)) (by norm_num)
  symm
  calc
    (∫ t in Ioi (0 : ℝ), f t * (1 / t ^ 2)) =
        ∫ t in Ioi (0 : ℝ),
          (|(-1 : ℝ)| * t ^ ((-1 : ℝ) - 1)) •
            (fun y : ℝ => f (1 / y)) (t ^ (-1 : ℝ)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have ht0 : t ≠ 0 := ne_of_gt ht
      change f t * (1 / t ^ 2) =
        (|(-1 : ℝ)| * t ^ ((-1 : ℝ) - 1)) •
          f (1 / (t ^ (-1 : ℝ)))
      rw [show (-1 : ℝ) - 1 = -2 by norm_num,
        Real.rpow_neg ht.le, Real.rpow_two, Real.rpow_neg_one]
      simp only [abs_neg, abs_one, one_mul, smul_eq_mul]
      field_simp [ht0]
    _ = ∫ x in Ioi (0 : ℝ), f (1 / x) := hsub

/-- The classical Gram entry after the inversion `x ↦ 1/t`. -/
theorem classicalGramEntry_eq_bblsIntegral
    (h k : ℕ) (hh : 0 < h) (hk : 0 < k) :
    baezDuarteGramEntry h k =
      ∫ t in Ioi (0 : ℝ),
        Int.fract (t / (h : ℝ)) * Int.fract (t / (k : ℝ)) / t ^ 2 := by
  have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold baezDuarteGramEntry
  calc
    (∫ x in Ioi (0 : ℝ),
        Int.fract (1 / ((h : ℝ) * x)) *
          Int.fract (1 / ((k : ℝ) * x))) =
        ∫ x in Ioi (0 : ℝ),
          (fun t : ℝ =>
            Int.fract (t / (h : ℝ)) * Int.fract (t / (k : ℝ))) (1 / x) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hx0 : x ≠ 0 := ne_of_gt hx
      have hfirst : (1 / x) / (h : ℝ) = 1 / ((h : ℝ) * x) := by
        field_simp [hh0, hx0]
      have hsecond : (1 / x) / (k : ℝ) = 1 / ((k : ℝ) * x) := by
        field_simp [hk0, hx0]
      change
        Int.fract (1 / ((h : ℝ) * x)) * Int.fract (1 / ((k : ℝ) * x)) =
          Int.fract ((1 / x) / (h : ℝ)) * Int.fract ((1 / x) / (k : ℝ))
      rw [hfirst, hsecond]
    _ = ∫ t in Ioi (0 : ℝ),
          (Int.fract (t / (h : ℝ)) * Int.fract (t / (k : ℝ))) *
            (1 / t ^ 2) :=
      setIntegral_Ioi_inv_substitution
        (fun t : ℝ => Int.fract (t / (h : ℝ)) * Int.fract (t / (k : ℝ)))
    _ = ∫ t in Ioi (0 : ℝ),
          Int.fract (t / (h : ℝ)) * Int.fract (t / (k : ℝ)) / t ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      ring

/-- The promoted classical formula and NB10 use the same cotangent
normalization. -/
theorem classicalFormula_eq_activeFormula (j k : ℕ) :
    vasyuninBEntryFormula (j + 1) (k + 1) =
      vasyuninGramFormula j k := by
  unfold vasyuninBEntryFormula vasyuninGramFormula
    cotangentSumVFormula cotangentTermV
    vasyuninCotangentSum cotangentTerm
  rfl

/-- Axiom-free pointwise Vasyunin evaluation in the active zero-based
normalization. -/
theorem bdGram_eq_vasyuninGramFormula (j k : ℕ) :
    bdGram j k = vasyuninGramFormula j k := by
  have hj : 0 < j + 1 := Nat.succ_pos j
  have hk : 0 < k + 1 := Nat.succ_pos k
  calc
    bdGram j k = baezDuarteGramEntry (j + 1) (k + 1) :=
      bdGram_eq_classicalGramEntry j k
    _ = ∫ t in Ioi (0 : ℝ),
          Int.fract (t / ((j + 1 : ℕ) : ℝ)) *
            Int.fract (t / ((k + 1 : ℕ) : ℝ)) / t ^ 2 :=
      classicalGramEntry_eq_bblsIntegral (j + 1) (k + 1) hj hk
    _ = (∑' n : ℕ, ∫ s in Ioc (0 : ℝ) (Nat.lcm (j + 1) (k + 1) : ℝ),
          Int.fract (s / ((j + 1 : ℕ) : ℝ)) *
            Int.fract (s / ((k + 1 : ℕ) : ℝ)) /
              ((n : ℝ) * (Nat.lcm (j + 1) (k + 1) : ℝ) + s) ^ 2) :=
      (bbls_period_unfolding (j + 1) (k + 1) hj hk).symm
    _ = vasyuninBEntry (j + 1) (k + 1) :=
      bbls_tsum_eq_vasyuninBEntry (j + 1) (k + 1) hj hk
    _ = vasyuninBEntryFormula (j + 1) (k + 1) := rfl
    _ = vasyuninGramFormula j k := classicalFormula_eq_activeFormula j k

/-- The classical input isolated in NB10 is now constructed. -/
noncomputable def vasyuninGramEvaluation : VasyuninGramEvaluation where
  gram_formula := bdGram_eq_vasyuninGramFormula

/-- Unconditional exact reduction of the active log-taper error to the fully
coupled Vasyunin expression.  Only the subsequent decay remains open. -/
theorem logTaperL2Error_eq_vasyuninCoupledExpression (n : ℕ) :
    NBMellinTools.NB8.logTaperL2Error n =
      vasyuninCoupledExpression
        (NBMellinTools.NB8.logTaperLength n)
        (NBMellinTools.NB8.logTaperCoeffs n) :=
  NBMellinTools.NB10.logTaperL2Error_eq_vasyuninCoupledExpression
    vasyuninGramEvaluation n

/-- The sole remaining input in the active Vasyunin route is coupled decay. -/
theorem riemannHypothesis_of_vasyuninCoupledDecay
    (hdecay : LogTaperVasyuninCoupledDecay) :
    RiemannHypothesis :=
  NBMellinTools.NB10.riemannHypothesis_of_vasyuninCoupledDecay
    vasyuninGramEvaluation hdecay

end NBMellinTools.NB11
