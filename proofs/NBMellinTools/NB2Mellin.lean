/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Phase NB2: elementary Mellin bridge

This file contains the part of the Nyman--Beurling Mellin calculation that is
independent of Mellin--Plancherel and Hardy-space arguments.  It proves the
transform of `χ_(0,1]` and reduces every Báez--Duarte generator to the single
fractional-part transform supplied by the zeta/Euler--Maclaurin calculation.

The `_of_base` results below are reusable algebraic assembly lemmas.  Their
analytic input is discharged unconditionally on `0 < Re s < 1` in
`NB2BaseMellin`, which supplies the canonical theorems `mellin_rhoBase`,
`mellin_rhoTheta`, and `mellin_rhoBD`.
-/

open MeasureTheory Set Complex intervalIntegral

namespace NBMellinTools.NB2

/-- The characteristic function of `(0, 1]` used in the Nyman--Beurling model. -/
noncomputable def chi01 (x : ℝ) : ℝ :=
  if 0 < x ∧ x ≤ 1 then 1 else 0

/-- The undilated fractional-part generator `x ↦ {1/x}`. -/
noncomputable def rhoBase (x : ℝ) : ℝ :=
  Int.fract (1 / x)

/-- The classical Nyman generator `ρ_θ(x) = {θ/x}`. -/
noncomputable def rhoTheta (θ x : ℝ) : ℝ :=
  Int.fract (θ / x)

/-- The zero-based Báez--Duarte generator.  Index `k` represents dilation
`k + 1`, hence the classical function `x ↦ {1 / ((k + 1)x)}`. -/
noncomputable def rhoBD (k : ℕ) (x : ℝ) : ℝ :=
  Int.fract (1 / ((k + 1 : ℝ) * x))

/-- `chi01`, coerced to `ℂ`, is the indicator of `(0, 1]`. -/
theorem chi01_eq_indicator (x : ℝ) :
    ((chi01 x : ℝ) : ℂ) =
      (Ioc (0 : ℝ) 1).indicator (fun _ ↦ (1 : ℂ)) x := by
  by_cases h : 0 < x ∧ x ≤ 1
  · simp [chi01, h, Set.mem_Ioc]
  · simp [chi01, h, Set.mem_Ioc]

/-- The exact Mellin transform of `χ_(0,1]` on its half-plane of convergence. -/
theorem mellin_chi01 {s : ℂ} (hs : 0 < s.re) :
    mellin (fun x : ℝ ↦ ((chi01 x : ℝ) : ℂ)) s = 1 / s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  have hre : (-1 : ℝ) < (s - 1).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  unfold mellin
  simp only [smul_eq_mul]
  have hcongr :
      (∫ t : ℝ in Ioi (0 : ℝ),
          (t : ℂ) ^ (s - 1) * ((chi01 t : ℝ) : ℂ)) =
        ∫ t : ℝ in Ioi (0 : ℝ),
          (Ioc (0 : ℝ) 1).indicator
            (fun u : ℝ ↦ (u : ℂ) ^ (s - 1)) t := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t _
    change (t : ℂ) ^ (s - 1) * ((chi01 t : ℝ) : ℂ) =
      (Ioc (0 : ℝ) 1).indicator
        (fun u : ℝ ↦ (u : ℂ) ^ (s - 1)) t
    rw [chi01_eq_indicator]
    by_cases h : t ∈ Ioc (0 : ℝ) 1
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      ring
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
      ring
  rw [hcongr, MeasureTheory.setIntegral_indicator measurableSet_Ioc,
    show Ioi (0 : ℝ) ∩ Ioc (0 : ℝ) 1 = Ioc (0 : ℝ) 1 from
      Set.inter_eq_self_of_subset_right (fun _ hx ↦ hx.1),
    ← intervalIntegral.integral_of_le zero_le_one,
    integral_cpow (Or.inl hre)]
  rw [show (s - 1 : ℂ) + 1 = s from by ring,
    show ((1 : ℝ) : ℂ) = 1 from by norm_num,
    show ((0 : ℝ) : ℂ) = 0 from by norm_num,
    Complex.one_cpow, Complex.zero_cpow hs0]
  ring

/-- A positive-parameter Nyman generator is a dilation of `rhoBase`. -/
theorem rhoTheta_eq_rhoBase_comp {θ : ℝ} (hθ : 0 < θ) (x : ℝ) :
    rhoTheta θ x = rhoBase (θ⁻¹ * x) := by
  unfold rhoTheta rhoBase
  congr 1
  by_cases hx : x = 0
  · simp [hx]
  · field_simp

/-- Mellin scaling for the classical generator `ρ_θ`. -/
theorem mellin_rhoTheta_eq_scaled_base {θ : ℝ} (hθ : 0 < θ) (s : ℂ) :
    mellin (fun x : ℝ ↦ (rhoTheta θ x : ℂ)) s =
      (((θ⁻¹ : ℝ) : ℂ) ^ (-s)) •
        mellin (fun x : ℝ ↦ (rhoBase x : ℂ)) s := by
  simpa only [rhoTheta_eq_rhoBase_comp hθ] using
    (mellin_comp_mul_left (fun x : ℝ ↦ (rhoBase x : ℂ)) s
      (inv_pos.mpr hθ))

/-- Exact `ρ_θ` formula once the base fractional-part transform is available. -/
theorem mellin_rhoTheta_of_base
    {θ : ℝ} (hθ : 0 < θ) (s : ℂ)
    (hbase : mellin (fun x : ℝ ↦ (rhoBase x : ℂ)) s =
      -(riemannZeta s) / s) :
    mellin (fun x : ℝ ↦ (rhoTheta θ x : ℂ)) s =
      (θ : ℂ) ^ s * (-(riemannZeta s) / s) := by
  rw [mellin_rhoTheta_eq_scaled_base hθ, hbase, smul_eq_mul]
  have harg : Complex.arg (θ : ℂ) ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hθ.le]
    exact Real.pi_ne_zero.symm
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg,
    Complex.cpow_neg, inv_inv]

/-- Each integer generator is the base generator after a positive dilation. -/
theorem rhoBD_eq_rhoBase_comp (k : ℕ) (x : ℝ) :
    rhoBD k x = rhoBase (((k + 1 : ℕ) : ℝ) * x) := by
  simp [rhoBD, rhoBase, Nat.cast_add, Nat.cast_one]

/-- Mellin scaling reduces every integer generator to the base generator. -/
theorem mellin_rhoBD_eq_scaled_base (k : ℕ) (s : ℂ) :
    mellin (fun x : ℝ ↦ (rhoBD k x : ℂ)) s =
      (((((k + 1 : ℕ) : ℝ) : ℂ) ^ (-s))) •
        mellin (fun x : ℝ ↦ (rhoBase x : ℂ)) s := by
  have hk : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
  simpa only [rhoBD_eq_rhoBase_comp, Nat.cast_add, Nat.cast_one,
    Complex.ofReal_natCast] using
    (mellin_comp_mul_left (fun x : ℝ ↦ (rhoBase x : ℂ)) s hk)

/-- Inversion converts the base generator to the Mellin transform of the
ordinary fractional-part function. -/
theorem mellin_rhoBase_eq_mellin_fract_inv (s : ℂ) :
    mellin (fun x : ℝ ↦ (rhoBase x : ℂ)) s =
      mellin (fun x : ℝ ↦ ((Int.fract x : ℝ) : ℂ)) (-s : ℂ) := by
  simpa [rhoBase, one_div] using
    (mellin_comp_inv (fun x : ℝ ↦ ((Int.fract x : ℝ) : ℂ)) s)

/-- Exact assembly of the Báez--Duarte generator formula from the one base
fractional-part Mellin evaluation.  The hypothesis is precisely the output
needed from the zeta/Euler--Maclaurin side of the project. -/
theorem mellin_rhoBD_of_base
    (k : ℕ) (s : ℂ)
    (hbase : mellin (fun x : ℝ ↦ (rhoBase x : ℂ)) s =
      -(riemannZeta s) / s) :
    mellin (fun x : ℝ ↦ (rhoBD k x : ℂ)) s =
      -(riemannZeta s) /
        (s * ((((k + 1 : ℕ) : ℝ) : ℂ) ^ s)) := by
  rw [mellin_rhoBD_eq_scaled_base, hbase]
  rw [smul_eq_mul, Complex.cpow_neg]
  field_simp

end NBMellinTools.NB2
