/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB2BaseMellin
import NBMellinTools.NB9QuadraticExpansion
import NBMellinTools.FourierCompatibility

/-!
# Certified Mellin normalization of the NB8 log taper

This module fixes the exact coefficient, sign, cutoff, and critical-line
normalizations of the active NB8 target.  It deliberately distinguishes the
physical Mellin numerator of the certified Nyman--Beurling residual from the
functional-equation-transformed Estermann expressions on `Re s = 3/2`.

No decay estimate is proved here.
-/

open MeasureTheory Set Complex
open scoped BigOperators

namespace NBMellinTools.NB15

open NBMellinTools.NB2
open NBMellinTools.NB8

/-- The positive Dirichlet-polynomial coefficient corresponding to NB8's
negative Nyman--Beurling coefficient. -/
noncomputable def certifiedDirichletCoeff
    (n : ℕ) (k : Fin (logTaperLength n)) : ℝ :=
  -logTaperCoeffs n k

/-- The active NB8 coefficient written in the standard BCF log-taper form. -/
theorem logTaperCoeffs_eq_bcfForm
    (n : ℕ) (k : Fin (logTaperLength n)) :
    logTaperCoeffs n k =
      -((ArithmeticFunction.moebius (k.val + 1) : ℤ) : ℝ) *
        (1 - Real.log ((k.val + 1 : ℕ) : ℝ) /
          Real.log ((logTaperLength n : ℕ) : ℝ)) := by
  have hN : (0 : ℝ) < (logTaperLength n : ℕ) := by
    exact_mod_cast (show 0 < logTaperLength n by
      unfold logTaperLength
      omega)
  have hk : (0 : ℝ) < (k.val + 1 : ℕ) := by positivity
  unfold logTaperCoeffs
  rw [Real.log_div (ne_of_gt hN) (ne_of_gt hk)]
  have hlog : Real.log ((logTaperLength n : ℕ) : ℝ) ≠ 0 := by
    apply ne_of_gt
    apply Real.log_pos
    exact_mod_cast (show 1 < logTaperLength n by
      unfold logTaperLength
      omega)
  field_simp

/-- Consequently, negating NB8's approximation coefficient gives the usual
positive Möbius log taper in the Dirichlet polynomial. -/
theorem certifiedDirichletCoeff_eq
    (n : ℕ) (k : Fin (logTaperLength n)) :
    certifiedDirichletCoeff n k =
      ((ArithmeticFunction.moebius (k.val + 1) : ℤ) : ℝ) *
        (1 - Real.log ((k.val + 1 : ℕ) : ℝ) /
          Real.log ((logTaperLength n : ℕ) : ℝ)) := by
  rw [certifiedDirichletCoeff, logTaperCoeffs_eq_bcfForm]
  ring

/-- The finite positive-sign Dirichlet polynomial paired with the active NB8
Nyman--Beurling residual. -/
noncomputable def certifiedDirichletPolynomial (n : ℕ) (s : ℂ) : ℂ :=
  ∑ k : Fin (logTaperLength n),
    (certifiedDirichletCoeff n k : ℂ) *
      ((((k.val + 1 : ℕ) : ℝ) : ℂ) ^ (-s))

/-- The literal complexification of the active certified NB8 residual. -/
noncomputable def certifiedResidual (n : ℕ) (x : ℝ) : ℂ :=
  ((chi01 x - bdApprox (logTaperLength n) (logTaperCoeffs n) x : ℝ) : ℂ)

/-- The physical critical-line point used by the Mellin--Plancherel bridge. -/
noncomputable def certifiedCriticalLinePoint (t : ℝ) : ℂ :=
  ((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)

theorem certifiedCriticalLinePoint_re (t : ℝ) :
    (certifiedCriticalLinePoint t).re = 1 / 2 := by
  simp [certifiedCriticalLinePoint]

theorem certifiedCriticalLinePoint_ne_zero (t : ℝ) :
    certifiedCriticalLinePoint t ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num [certifiedCriticalLinePoint] at hre

/-- The exact critical-line expression whose squared norm is the spectral
form of the active NB8 residual.  This definition does not identify it with
the transformed Estermann `3/2`-line aggregate. -/
noncomputable def certifiedCriticalLineNumerator (n : ℕ) (t : ℝ) : ℂ :=
  (1 - riemannZeta (certifiedCriticalLinePoint t) *
      certifiedDirichletPolynomial n (certifiedCriticalLinePoint t)) /
    certifiedCriticalLinePoint t

/-- NB8's energy is exactly the squared norm of the literal certified
residual.  This is the physical-space side of the future Mellin--Plancherel
identity and fixes the real-to-complex normalization. -/
theorem logTaperL2Error_eq_certifiedResidual_normSq (n : ℕ) :
    logTaperL2Error n =
      ∫ x in Ioi (0 : ℝ), ‖certifiedResidual n x‖ ^ 2 := by
  unfold logTaperL2Error BaezDuarteL2Error certifiedResidual
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Replacing the active NB8 coefficients by their standard BCF form does not
change the certified physical energy. -/
theorem logTaperL2Error_eq_bcfCoefficientEnergy (n : ℕ) :
    logTaperL2Error n =
      BaezDuarteL2Error (logTaperLength n)
        (fun k =>
          -((ArithmeticFunction.moebius (k.val + 1) : ℤ) : ℝ) *
            (1 - Real.log ((k.val + 1 : ℕ) : ℝ) /
              Real.log ((logTaperLength n : ℕ) : ℝ))) := by
  unfold logTaperL2Error
  congr 1
  funext k
  exact logTaperCoeffs_eq_bcfForm n k

end NBMellinTools.NB15
