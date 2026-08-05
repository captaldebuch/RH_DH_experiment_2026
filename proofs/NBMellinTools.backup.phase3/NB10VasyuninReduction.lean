/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB9QuadraticExpansion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# NB10: correction-preserving Vasyunin reduction

This file records the classical Vasyunin expression for the Gram entries in
the zero-based normalization used by the active package and proves the finite
algebra that follows from that pointwise identity.

The pointwise integral evaluation is deliberately exposed as the structure
`VasyuninGramEvaluation`.  The historical Route C implementation of that
evaluation imports a period-reduction theorem whose dependency graph contains
an unresolved `sorry`; it is therefore not imported here as a proved result.

No decay or cancellation estimate is proved in this file.  In particular, the
constant, logarithmic, cotangent, and retained linear pieces remain inside one
signed expression throughout.
-/

open Filter
open scoped BigOperators

namespace NBMellinTools.NB10

open NBMellinTools.NB8
open NBMellinTools.NB9

/-- The elementary cotangent occurring in Vasyunin's finite sum. -/
noncomputable def cotangentTerm (a k : ℕ) : ℝ :=
  Real.cos (Real.pi * (a : ℝ) / (k : ℝ)) /
    Real.sin (Real.pi * (a : ℝ) / (k : ℝ))

/-- Vasyunin's finite cotangent sum
`V(h,k) = ∑_{1 ≤ a < k} {ah/k} cot(πa/k)`. -/
noncomputable def vasyuninCotangentSum (h k : ℕ) : ℝ :=
  ∑ a ∈ Finset.Ico 1 k,
    Int.fract (((a * h : ℕ) : ℝ) / (k : ℝ)) * cotangentTerm a k

/-- Vasyunin's explicit expression for the active zero-based Gram entry.
The denominators represented by indices `j,k` are `j+1,k+1`. -/
noncomputable def vasyuninGramFormula (j k : ℕ) : ℝ :=
  let h : ℝ := (j + 1 : ℕ)
  let q : ℝ := (k + 1 : ℕ)
  (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / 2 *
      (1 / h + 1 / q) +
    (q - h) / (2 * h * q) * Real.log (h / q) -
    Real.pi / (2 * h * q) *
      (vasyuninCotangentSum (j + 1) (k + 1) +
        vasyuninCotangentSum (k + 1) (j + 1))

/-- The exact classical pointwise Gram evaluation, isolated as an input until
its historical period-reduction proof has been repaired and ported. -/
structure VasyuninGramEvaluation : Prop where
  gram_formula : ∀ j k : ℕ, bdGram j k = vasyuninGramFormula j k

/-- Constant part of the finite Vasyunin bilinear form. -/
noncomputable def vasyuninConstantTerm
    (N : ℕ) (coeffs : Fin N → ℝ) : ℝ :=
  ∑ j : Fin N, ∑ k : Fin N,
    coeffs j * coeffs k *
      ((Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / 2 *
        (1 / ((j.val + 1 : ℕ) : ℝ) + 1 / ((k.val + 1 : ℕ) : ℝ)))

/-- Elementary logarithmic-ratio part of the finite Vasyunin form. -/
noncomputable def vasyuninLogRatioTerm
    (N : ℕ) (coeffs : Fin N → ℝ) : ℝ :=
  ∑ j : Fin N, ∑ k : Fin N,
    coeffs j * coeffs k *
      ((((k.val + 1 : ℕ) : ℝ) - ((j.val + 1 : ℕ) : ℝ)) /
          (2 * ((j.val + 1 : ℕ) : ℝ) * ((k.val + 1 : ℕ) : ℝ)) *
        Real.log
          (((j.val + 1 : ℕ) : ℝ) / ((k.val + 1 : ℕ) : ℝ)))

/-- The two oriented cotangent sums, kept together exactly as they occur in
the pointwise formula. -/
noncomputable def vasyuninCotangentTerm
    (N : ℕ) (coeffs : Fin N → ℝ) : ℝ :=
  ∑ j : Fin N, ∑ k : Fin N,
    coeffs j * coeffs k *
      (-Real.pi /
          (2 * ((j.val + 1 : ℕ) : ℝ) * ((k.val + 1 : ℕ) : ℝ)) *
        (vasyuninCotangentSum (j.val + 1) (k.val + 1) +
          vasyuninCotangentSum (k.val + 1) (j.val + 1)))

/-- The complete correction-preserving Vasyunin expression. -/
noncomputable def vasyuninCoupledExpression
    (N : ℕ) (coeffs : Fin N → ℝ) : ℝ :=
  bdCorrectionTerm N coeffs +
    vasyuninConstantTerm N coeffs +
    vasyuninLogRatioTerm N coeffs +
    vasyuninCotangentTerm N coeffs

private theorem weighted_vasyunin_split
    (a b : ℝ) (j k : ℕ) :
    a * b * vasyuninGramFormula j k =
      a * b *
        ((Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / 2 *
          (1 / ((j + 1 : ℕ) : ℝ) + 1 / ((k + 1 : ℕ) : ℝ))) +
      a * b *
        ((((k + 1 : ℕ) : ℝ) - ((j + 1 : ℕ) : ℝ)) /
          (2 * ((j + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ)) *
          Real.log (((j + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ))) +
      a * b *
        (-Real.pi /
          (2 * ((j + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ)) *
          (vasyuninCotangentSum (j + 1) (k + 1) +
            vasyuninCotangentSum (k + 1) (j + 1))) := by
  unfold vasyuninGramFormula
  dsimp only
  ring

/-- Assuming only the pointwise classical evaluation, the complete Gram term
is exactly the sum of its constant, logarithmic, and cotangent pieces. -/
theorem bdGramTerm_eq_vasyunin_terms
    (H : VasyuninGramEvaluation) (N : ℕ) (coeffs : Fin N → ℝ) :
    bdGramTerm N coeffs =
      vasyuninConstantTerm N coeffs +
        vasyuninLogRatioTerm N coeffs +
        vasyuninCotangentTerm N coeffs := by
  classical
  unfold bdGramTerm vasyuninConstantTerm vasyuninLogRatioTerm
    vasyuninCotangentTerm
  simp_rw [H.gram_formula, weighted_vasyunin_split,
    Finset.sum_add_distrib]

/-- Exact correction-preserving cotangent reduction of the active quadratic
form.  No summand is bounded separately. -/
theorem bdQuadraticForm_eq_vasyuninCoupledExpression
    (H : VasyuninGramEvaluation) (N : ℕ) (coeffs : Fin N → ℝ) :
    bdQuadraticForm N coeffs = vasyuninCoupledExpression N coeffs := by
  rw [bdQuadraticForm_eq_correction_add_gram,
    bdGramTerm_eq_vasyunin_terms H]
  unfold vasyuninCoupledExpression
  ring

/-- Specialization of the exact reduction to the NB8 logarithmic taper. -/
theorem logTaperL2Error_eq_vasyuninCoupledExpression
    (H : VasyuninGramEvaluation) (n : ℕ) :
    logTaperL2Error n =
      vasyuninCoupledExpression
        (logTaperLength n) (logTaperCoeffs n) := by
  rw [logTaperL2Error_eq_quadraticForm,
    bdQuadraticForm_eq_vasyuninCoupledExpression H]

/-- The explicit coupled cotangent-side decay target.  This is open. -/
def LogTaperVasyuninCoupledDecay : Prop :=
  Tendsto
    (fun n : ℕ =>
      vasyuninCoupledExpression
        (logTaperLength n) (logTaperCoeffs n))
    atTop (nhds 0)

/-- Once the classical pointwise formula is available, the active NB8 decay
target is equivalent to decay of the complete coupled Vasyunin expression. -/
theorem logTaperL2Decay_iff_vasyuninCoupledDecay
    (H : VasyuninGramEvaluation) :
    LogTaperL2Decay ↔ LogTaperVasyuninCoupledDecay := by
  unfold LogTaperL2Decay LogTaperVasyuninCoupledDecay
  apply tendsto_congr'
  exact Eventually.of_forall
    (logTaperL2Error_eq_vasyuninCoupledExpression H)

/-- Conditional endpoint for the cotangent route.  The two explicit inputs
are the classical pointwise evaluation and the genuinely hard signed decay. -/
theorem riemannHypothesis_of_vasyuninCoupledDecay
    (H : VasyuninGramEvaluation)
    (hdecay : LogTaperVasyuninCoupledDecay) :
    RiemannHypothesis :=
  NBMellinTools.NB8.riemannHypothesis_of_logTaperL2Decay
    ((logTaperL2Decay_iff_vasyuninCoupledDecay H).2 hdecay)

end NBMellinTools.NB10
