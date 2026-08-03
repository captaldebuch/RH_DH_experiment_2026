/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB10VasyuninReduction

/-!
# NB11: smooth and log-ratio terms decay under Mertens/PNT bounds

This file isolates the non-cotangent smooth components of the coupled
Vasyunin expression:
  `vasyuninSmoothTerm = bdCorrectionTerm + vasyuninConstantTerm + vasyuninLogRatioTerm`

It proves that the coupled expression decomposes algebraically into:
  `vasyuninCoupledExpression = vasyuninSmoothTerm + vasyuninCotangentTerm`

The proposition `SmoothMertensDecay` names the required convergence. This
file does not prove it from the Prime Number Theorem; it proves only the exact
algebraic assembly once that analytic input is supplied.
-/

open Filter
open scoped BigOperators

namespace NBMellinTools.NB11

open NBMellinTools.NB8
open NBMellinTools.NB9
open NBMellinTools.NB10

/-- The smooth (non-cotangent) part of the finite coupled Vasyunin expression. -/
noncomputable def vasyuninSmoothTerm
    (N : ℕ) (coeffs : Fin N → ℝ) : ℝ :=
  bdCorrectionTerm N coeffs +
    vasyuninConstantTerm N coeffs +
    vasyuninLogRatioTerm N coeffs

/-- The coupled Vasyunin expression decomposes into the smooth term plus the
cotangent term. -/
theorem vasyuninCoupledExpression_eq_smooth_add_cotangent
    (N : ℕ) (coeffs : Fin N → ℝ) :
    vasyuninCoupledExpression N coeffs =
      vasyuninSmoothTerm N coeffs +
        vasyuninCotangentTerm N coeffs := by
  unfold vasyuninCoupledExpression vasyuninSmoothTerm
  ring

/-- The classical Mertens / PNT asymptotic statement: the smooth and log-ratio
terms of the explicit log-taper family converge to zero as `n → ∞`. -/
def SmoothMertensDecay : Prop :=
  Tendsto
    (fun n : ℕ =>
      vasyuninSmoothTerm
        (logTaperLength n) (logTaperCoeffs n))
    atTop (nhds 0)

/-- When the smooth component and the cotangent component both decay, the
complete coupled Vasyunin expression decays to zero. -/
theorem tendsto_vasyuninCoupledExpression_of_smooth_and_cotangent
    (hsmooth : SmoothMertensDecay)
    (hcot : Tendsto
      (fun n : ℕ => vasyuninCotangentTerm (logTaperLength n) (logTaperCoeffs n))
      atTop (nhds 0)) :
    LogTaperVasyuninCoupledDecay := by
  unfold LogTaperVasyuninCoupledDecay SmoothMertensDecay at *
  have heq : (fun n : ℕ => vasyuninCoupledExpression (logTaperLength n) (logTaperCoeffs n)) =
      (fun n : ℕ => vasyuninSmoothTerm (logTaperLength n) (logTaperCoeffs n) +
                    vasyuninCotangentTerm (logTaperLength n) (logTaperCoeffs n)) := by
    ext n
    exact vasyuninCoupledExpression_eq_smooth_add_cotangent _ _
  rw [heq]
  have hsum := Tendsto.add hsmooth hcot
  rw [add_zero] at hsum
  exact hsum

end NBMellinTools.NB11
