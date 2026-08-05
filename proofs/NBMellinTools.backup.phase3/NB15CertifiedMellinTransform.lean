/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB15CertifiedMellinNormalization
import Mathlib.Analysis.MellinInversion

/-!
# Mellin transform of the certified NB8 log-taper residual

This file performs the unconditional finite sum--integral assembly omitted by
the normalization module.  It proves the exact physical critical-strip and
critical-line Mellin numerator identities.  It still makes no identification
with the functional-equation-transformed Estermann `3/2`-line aggregate.
-/

open MeasureTheory Set Complex
open scoped BigOperators

namespace NBMellinTools.NB15

open NBMellinTools.NB2
open NBMellinTools.NB8

private noncomputable def mellinKernel (s : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (s - 1)

private noncomputable def rhoMellinIntegrand
    (k : ℕ) (s : ℂ) (x : ℝ) : ℂ :=
  mellinKernel s x * ((rhoBD k x : ℝ) : ℂ)

private theorem rho_mellin_integrableOn_Ioc01
    {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    IntegrableOn (rhoMellinIntegrand k s) (Ioc (0 : ℝ) 1) := by
  have hk := intervalIntegral.intervalIntegrable_cpow'
    (r := s - 1) (a := (0 : ℝ)) (b := 1) (by
      rw [Complex.sub_re, Complex.one_re]
      linarith)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hk
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => ((rhoBD k x : ℝ) : ℂ))
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (NBMellinTools.NB9.measurable_rhoBD k).complex_ofReal.aestronglyMeasurable.restrict
  have hbound : ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      ‖((rhoBD k x : ℝ) : ℂ)‖ ≤ (1 : ℝ) := by
    filter_upwards with x
    simpa only [Complex.norm_real] using
      NBMellinTools.NB9.norm_rhoBD_le_one k x
  have hmul := hk.mul_bdd hmeas hbound
  simpa [rhoMellinIntegrand, mellinKernel, smul_eq_mul] using hmul

private theorem rho_mellin_integrableOn_Ioi_one
    {s : ℂ} (hs : s.re < 1) (k : ℕ) :
    IntegrableOn (rhoMellinIntegrand k s) (Ioi (1 : ℝ)) := by
  have hcpow : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (s - 2)) (Ioi (1 : ℝ)) := by
    apply integrableOn_Ioi_cpow_of_lt
    · change s.re - 2 < -1
      linarith
    · exact one_pos
  have ha : (0 : ℂ) ≠ (((k : ℝ) + 1 : ℝ) : ℂ) := by
    intro h
    have h' : ((k : ℝ) + 1) = 0 := by exact_mod_cast h
    have hpos : 0 < ((k : ℝ) + 1) := by positivity
    linarith
  have hmodel : IntegrableOn
      (fun x : ℝ => (((k : ℝ) + 1 : ℝ) : ℂ)⁻¹ * (x : ℂ) ^ (s - 2))
      (Ioi (1 : ℝ)) :=
    hcpow.const_mul _
  apply hmodel.congr_fun _ measurableSet_Ioi
  intro x hx
  have hx0 : (x : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans zero_lt_one hx))
  dsimp [rhoMellinIntegrand, mellinKernel]
  rw [rhoBD_eq_one_div_of_one_lt k hx]
  simp only [Complex.ofReal_div, Complex.ofReal_mul]
  rw [show s - 2 = (s - 1) - 1 by ring,
    Complex.cpow_sub (s - 1) 1 hx0, Complex.cpow_one]
  field_simp
  simp

private theorem rho_mellin_integrableOn_Ioi_zero
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (k : ℕ) :
    IntegrableOn (rhoMellinIntegrand k s) (Ioi (0 : ℝ)) := by
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  exact (rho_mellin_integrableOn_Ioc01 hs0 k).union
    (rho_mellin_integrableOn_Ioi_one hs1 k)

private theorem bdApprox_mellin_integrableOn
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (N : ℕ) (coeffs : Fin N → ℝ) :
    IntegrableOn
      (fun x : ℝ => mellinKernel s x * ((bdApprox N coeffs x : ℝ) : ℂ))
      (Ioi (0 : ℝ)) := by
  have hsum : IntegrableOn
      (fun x : ℝ => ∑ k : Fin N,
        mellinKernel s x * (coeffs k : ℂ) * (rhoBD k.val x : ℂ))
      (Ioi (0 : ℝ)) := by
    apply MeasureTheory.integrable_finsetSum (Finset.univ : Finset (Fin N))
    intro k hk
    have h := rho_mellin_integrableOn_Ioi_zero hs0 hs1 k.val
    simpa [mellinKernel, rhoMellinIntegrand, smul_eq_mul, mul_assoc,
      mul_left_comm, mul_comm] using h.const_mul (coeffs k : ℂ)
  apply hsum.congr_fun _ measurableSet_Ioi
  intro x hx
  unfold bdApprox
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

private theorem chi_mellin_integrableOn
    {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn
      (fun x : ℝ => mellinKernel s x * ((chi01 x : ℝ) : ℂ))
      (Ioi (0 : ℝ)) := by
  have hk := intervalIntegral.intervalIntegrable_cpow'
    (r := s - 1) (a := (0 : ℝ)) (b := 1) (by
      rw [Complex.sub_re, Complex.one_re]
      linarith)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hk
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  have hlocal : IntegrableOn
      (fun x : ℝ => mellinKernel s x * ((chi01 x : ℝ) : ℂ))
      (Ioc (0 : ℝ) 1) := by
    apply hk.congr_fun _ measurableSet_Ioc
    intro x hx
    have hchi : chi01 x = 1 := by
      simp [chi01, hx.1, hx.2]
    simp [mellinKernel, hchi]
  have htail : IntegrableOn
      (fun x : ℝ => mellinKernel s x * ((chi01 x : ℝ) : ℂ))
      (Ioi (1 : ℝ)) := by
    apply integrableOn_zero.congr_fun _ measurableSet_Ioi
    intro x hx
    have hx' : 1 < x := hx
    have hchi : chi01 x = 0 := by
      simp [chi01, not_le_of_gt hx']
    simp [hchi]
  exact hlocal.union htail

private theorem mellin_sub_chi_bdApprox
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (N : ℕ) (coeffs : Fin N → ℝ) :
    mellin (fun x : ℝ => ((chi01 x - bdApprox N coeffs x : ℝ) : ℂ)) s =
      mellin (fun x : ℝ => (chi01 x : ℂ)) s -
        mellin (fun x : ℝ => (bdApprox N coeffs x : ℂ)) s := by
  have hchi := chi_mellin_integrableOn (s := s) hs0
  have hbd := bdApprox_mellin_integrableOn hs0 hs1 N coeffs
  unfold mellin
  simp only [smul_eq_mul]
  have hsub := MeasureTheory.integral_sub hchi hbd
  change (∫ x in Ioi (0 : ℝ), mellinKernel s x *
      (((chi01 x - bdApprox N coeffs x : ℝ) : ℂ))) =
    (∫ x in Ioi (0 : ℝ), mellinKernel s x * ((chi01 x : ℝ) : ℂ)) -
      ∫ x in Ioi (0 : ℝ), mellinKernel s x *
        ((bdApprox N coeffs x : ℝ) : ℂ)
  have hfun :
      (fun x : ℝ => mellinKernel s x *
        (((chi01 x - bdApprox N coeffs x : ℝ) : ℂ))) =
      (fun x : ℝ => mellinKernel s x * ((chi01 x : ℝ) : ℂ) -
        mellinKernel s x * ((bdApprox N coeffs x : ℝ) : ℂ)) := by
    funext x
    rw [Complex.ofReal_sub]
    ring
  rw [hfun]
  exact hsub

/-- Mellin transform of an arbitrary finite active Báez--Duarte approximant.
All integrability needed for the finite exchange is proved above. -/
theorem mellin_bdApprox_eq_sum
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (N : ℕ) (coeffs : Fin N → ℝ) :
    mellin (fun x : ℝ => (bdApprox N coeffs x : ℂ)) s =
      ∑ i : Fin N,
        (coeffs i : ℂ) *
          (-(riemannZeta s) /
            (s * ((((i.val + 1 : ℕ) : ℝ) : ℂ) ^ s))) := by
  unfold mellin bdApprox
  rw [show (fun x : ℝ => (x : ℂ) ^ (s - 1) •
      (↑(∑ k, coeffs k * rhoBD k.val x) : ℂ)) =
      (fun x : ℝ => ∑ k : Fin N,
        (x : ℂ) ^ (s - 1) * (coeffs k : ℂ) *
          (rhoBD k.val x : ℂ)) by
        funext x
        push_cast
        simp only [smul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [show (fun x : ℝ => (x : ℂ) ^ (s - 1) *
        (coeffs k : ℂ) * (rhoBD k.val x : ℂ)) =
        (fun x : ℝ => (coeffs k : ℂ) *
          ((x : ℂ) ^ (s - 1) * (rhoBD k.val x : ℂ))) by
          funext x
          ring]
    rw [MeasureTheory.integral_const_mul]
    rw [show (∫ x in Ioi (0 : ℝ),
        (x : ℂ) ^ (s - 1) * (rhoBD k.val x : ℂ)) =
        mellin (fun x : ℝ => (rhoBD k.val x : ℂ)) s by rfl]
    rw [mellin_rhoBD k.val hs0 hs1]
  · intro k hk
    have h := rho_mellin_integrableOn_Ioi_zero hs0 hs1 k.val
    simpa [rhoMellinIntegrand, mellinKernel, smul_eq_mul,
      mul_assoc, mul_left_comm, mul_comm] using
      h.const_mul (coeffs k : ℂ)

/-- Mellin transform of NB8's finite approximation, expressed through its
positive-sign certified Dirichlet polynomial. -/
theorem mellin_certifiedApproximant_eq
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (n : ℕ) :
    mellin (fun x : ℝ =>
      (bdApprox (logTaperLength n) (logTaperCoeffs n) x : ℂ)) s =
      riemannZeta s * certifiedDirichletPolynomial n s / s := by
  rw [mellin_bdApprox_eq_sum hs0 hs1]
  unfold certifiedDirichletPolynomial certifiedDirichletCoeff
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hbase : ((((i.val + 1 : ℕ) : ℝ) : ℂ) ^ s) ≠ 0 := by
    apply Complex.cpow_ne_zero_iff.mpr
    left
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num at hre
    have hi0 : (0 : ℝ) ≤ i.val := by positivity
    linarith
  rw [Complex.cpow_neg]
  field_simp [hbase]
  push_cast
  ring

/-- Exact physical Mellin numerator identity for the certified NB8 residual
throughout the open critical strip. -/
theorem mellin_certifiedResidual_eq
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (n : ℕ) :
    mellin (certifiedResidual n) s =
      (1 - riemannZeta s * certifiedDirichletPolynomial n s) / s := by
  unfold certifiedResidual
  rw [mellin_sub_chi_bdApprox hs0 hs1
      (logTaperLength n) (logTaperCoeffs n),
    mellin_chi01 hs0,
    mellin_certifiedApproximant_eq hs0 hs1 n]
  field_simp

/-- Exact pointwise critical-line normalization of the active NB8 residual. -/
theorem mellin_certifiedResidual_criticalLine (n : ℕ) (t : ℝ) :
    mellin (certifiedResidual n) (certifiedCriticalLinePoint t) =
      certifiedCriticalLineNumerator n t := by
  unfold certifiedCriticalLineNumerator
  apply mellin_certifiedResidual_eq
  · rw [certifiedCriticalLinePoint_re]
    norm_num
  · rw [certifiedCriticalLinePoint_re]
    norm_num

end NBMellinTools.NB15
