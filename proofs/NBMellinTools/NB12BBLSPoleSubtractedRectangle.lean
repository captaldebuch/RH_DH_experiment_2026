/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PoleDiagnostic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exact correction-preserving rectangle subtraction

This module ports the exact rational rectangle geometry into the active
`NBMellinTools` chain. A simple pole strictly inside the symmetric rectangle
contributes exactly `2 * π * I`; a double pole contributes zero. These
formulas are assembled with Cauchy--Goursat for a holomorphic regularized
remainder.  The final section adds the active H15 triple-pole ledger.

No residue theorem, asymptotic estimate, or cancellation hypothesis is
assumed.
-/

namespace NBMellinTools.NB12

open Complex Filter Set Topology MeasureTheory
open scoped Interval Real

/-! ## Oriented rectangle edges -/

noncomputable def rectangularLowerEdge
    (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  ∫ x : ℝ in z.re..w.re, f (x + z.im * I)

noncomputable def rectangularUpperEdge
    (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  -∫ x : ℝ in z.re..w.re, f (x + w.im * I)

noncomputable def rectangularRightEdge
    (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  I * ∫ y : ℝ in z.im..w.im, f (w.re + y * I)

noncomputable def rectangularLeftEdge
    (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  -(I * ∫ y : ℝ in z.im..w.im, f (z.re + y * I))

noncomputable def rectangularBoundaryIntegral
    (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  rectangularLowerEdge f z w + rectangularUpperEdge f z w +
    rectangularRightEdge f z w + rectangularLeftEdge f z w

noncomputable def symmetricLowerCorner (σ T : ℝ) : ℂ :=
  (σ : ℂ) - (T : ℂ) * I

noncomputable def symmetricUpperCorner (σ T : ℝ) : ℂ :=
  (σ : ℂ) + (T : ℂ) * I

noncomputable def symmetricHorizontalEdges
    (f : ℂ → ℂ) (σL σR T : ℝ) : ℂ :=
  rectangularLowerEdge f (symmetricLowerCorner σL T)
      (symmetricUpperCorner σR T) +
    rectangularUpperEdge f (symmetricLowerCorner σL T)
      (symmetricUpperCorner σR T)

theorem rectangularBoundaryIntegral_eq_zero
    (f : ℂ → ℂ) (z w : ℂ)
    (hf : DifferentiableOn ℂ f
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    rectangularBoundaryIntegral f z w = 0 := by
  simpa [rectangularBoundaryIntegral, rectangularLowerEdge,
    rectangularUpperEdge, rectangularRightEdge, rectangularLeftEdge,
    smul_eq_mul] using
      (Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w hf)


theorem simplePoleHorizontalPair (p σL σR T : ℝ) (hT : 0 < T) :
    rectangularLowerEdge (fun s : ℂ => (s - (p : ℂ))⁻¹)
        (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) +
      rectangularUpperEdge (fun s : ℂ => (s - (p : ℂ))⁻¹)
        (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) =
      (2 * I : ℂ) *
        ((Real.arctan ((σR - p) / T) -
          Real.arctan ((σL - p) / T) : ℝ) : ℂ) := by
  have hminus : Continuous (fun x : ℝ =>
      (((x : ℂ) - (T : ℂ) * I - (p : ℂ))⁻¹)) := by
    apply Continuous.inv₀ (by fun_prop)
    intro x hx
    have hi := congrArg Complex.im hx
    simp at hi
    linarith
  have hplus : Continuous (fun x : ℝ =>
      (((x : ℂ) + (T : ℂ) * I - (p : ℂ))⁻¹)) := by
    apply Continuous.inv₀ (by fun_prop)
    intro x hx
    have hi := congrArg Complex.im hx
    simp at hi
    linarith
  have hreal :
      (∫ x : ℝ in σL..σR, (T ^ 2 + (x - p) ^ 2)⁻¹) =
        T⁻¹ * (Real.arctan ((σR - p) / T) -
          Real.arctan ((σL - p) / T)) := by
    rw [intervalIntegral.integral_comp_sub_right
      (f := fun x : ℝ => (T ^ 2 + x ^ 2)⁻¹)]
    exact integral_inv_sq_add_sq hT.ne'
  have hcoe := intervalIntegral.integral_ofReal
    (a := σL) (b := σR) (μ := MeasureTheory.volume)
    (f := fun x : ℝ => (T ^ 2 + (x - p) ^ 2)⁻¹)
  simp only [rectangularLowerEdge, rectangularUpperEdge,
    symmetricLowerCorner, symmetricUpperCorner]
  simp [Complex.mul_re, Complex.mul_im]
  change
    (∫ x : ℝ in σL..σR,
        ((x : ℂ) - (T : ℂ) * I - (p : ℂ))⁻¹) -
      ∫ x : ℝ in σL..σR,
        ((x : ℂ) + (T : ℂ) * I - (p : ℂ))⁻¹ = _
  rw [← intervalIntegral.integral_sub
    (hminus.intervalIntegrable σL σR) (hplus.intervalIntegrable σL σR)]
  calc
    (∫ x : ℝ in σL..σR,
        ((x : ℂ) - (T : ℂ) * I - (p : ℂ))⁻¹ -
          ((x : ℂ) + (T : ℂ) * I - (p : ℂ))⁻¹) =
      ∫ x : ℝ in σL..σR,
        (2 * T * I) *
          (((T ^ 2 + (x - p) ^ 2)⁻¹ : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro x _
      have hdiv :
        ((x : ℂ) - (T : ℂ) * I - (p : ℂ))⁻¹ -
            ((x : ℂ) + (T : ℂ) * I - (p : ℂ))⁻¹ =
          (2 * T * I) /
            ((T ^ 2 + (x - p) ^ 2 : ℝ) : ℂ) := by
          have hden : T ^ 2 + (x - p) ^ 2 ≠ 0 := by positivity
          have hm : (x : ℂ) - (T : ℂ) * I - (p : ℂ) ≠ 0 := by
            intro h
            have hi := congrArg Complex.im h
            simp at hi
            linarith
          have hp : (x : ℂ) + (T : ℂ) * I - (p : ℂ) ≠ 0 := by
            intro h
            have hi := congrArg Complex.im h
            simp at hi
            linarith
          have hden' : T ^ 2 - x * p * 2 + x ^ 2 + p ^ 2 ≠ 0 := by
            convert hden using 1 <;> ring
          have hdenC :
              ((T ^ 2 - x * p * 2 + x ^ 2 + p ^ 2 : ℝ) : ℂ) ≠ 0 := by
            exact_mod_cast hden'
          field_simp [hm, hp, hden, hden', hdenC]
          ring_nf
          field_simp [hdenC]
          ring_nf
          rw [I_sq]
          push_cast
          ring
      change
        ((x : ℂ) - (T : ℂ) * I - (p : ℂ))⁻¹ -
            ((x : ℂ) + (T : ℂ) * I - (p : ℂ))⁻¹ =
          (2 * T * I) * (((T ^ 2 + (x - p) ^ 2)⁻¹ : ℝ) : ℂ)
      rw [hdiv, div_eq_mul_inv]
      congr 1
      norm_cast
    _ = (2 * T * I) *
        (∫ x : ℝ in σL..σR,
          (((T ^ 2 + (x - p) ^ 2)⁻¹ : ℝ) : ℂ)) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (2 * T * I) *
        ((∫ x : ℝ in σL..σR,
          ((T ^ 2 + (x - p) ^ 2)⁻¹ : ℝ)) : ℂ) := by
      rw [hcoe]
    _ = (2 * I : ℂ) *
        ((Real.arctan ((σR - p) / T) -
          Real.arctan ((σL - p) / T) : ℝ) : ℂ) := by
      rw [hcoe, hreal]
      push_cast
      field_simp [hT.ne']
  simp [Complex.ofReal_arctan]

theorem simplePolePositiveVertical (α T : ℝ) (hα : 0 < α) :
    I * (∫ y : ℝ in -T..T,
      (((α : ℂ) + (y : ℂ) * I)⁻¹)) =
      (2 * I : ℂ) * (Real.arctan (T / α) : ℂ) := by
  have hden : ∀ y : ℝ, α ^ 2 + y ^ 2 ≠ 0 := by
    intro y
    positivity
  have hpoint : ∀ y : ℝ,
      (((α : ℂ) + (y : ℂ) * I)⁻¹) =
        ((α / (α ^ 2 + y ^ 2) : ℝ) : ℂ) -
          ((y / (α ^ 2 + y ^ 2) : ℝ) : ℂ) * I := by
    intro y
    apply Complex.ext
    · rw [Complex.inv_re, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero,
        Complex.sub_re, Complex.ofReal_im, zero_mul, sub_zero]
      rw [show ((y : ℂ) * I).im = y by simp]
      ring
    · rw [Complex.inv_im, Complex.normSq_apply]
      simp only [Complex.add_im, Complex.add_re, Complex.ofReal_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero,
        Complex.sub_im, Complex.ofReal_re, zero_mul, neg_zero,
        zero_add, sub_zero]
      rw [show ((y : ℂ) * I).re = 0 by simp]
      ring
  have hodd :
      (∫ y : ℝ in -T..T, y / (α ^ 2 + y ^ 2)) = 0 := by
    have hcomp := intervalIntegral.integral_comp_neg
      (a := -T) (b := T) (f := fun y : ℝ => y / (α ^ 2 + y ^ 2))
    simp only [neg_neg] at hcomp
    have hneg :
        (∫ y : ℝ in -T..T, (-y) / (α ^ 2 + (-y) ^ 2)) =
          -(∫ y : ℝ in -T..T, y / (α ^ 2 + y ^ 2)) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro y _
      ring
    rw [hneg] at hcomp
    linarith
  have hreal :
      (∫ y : ℝ in -T..T, α / (α ^ 2 + y ^ 2)) =
        2 * Real.arctan (T / α) := by
    change (∫ y : ℝ in -T..T, α * (α ^ 2 + y ^ 2)⁻¹) = _
    rw [intervalIntegral.integral_const_mul]
    rw [integral_inv_sq_add_sq hα.ne']
    rw [show (-T) / α = -(T / α) by ring]
    rw [Real.arctan_neg]
    field_simp [hα.ne']
    ring
  rw [intervalIntegral.integral_congr (fun y _ => hpoint y)]
  have hcont1 : Continuous (fun y : ℝ => α / (α ^ 2 + y ^ 2)) := by
    fun_prop (disch := aesop)
  have hcont2 : Continuous (fun y : ℝ => y / (α ^ 2 + y ^ 2)) := by
    fun_prop (disch := aesop)
  have hcont1C : Continuous
      (fun y : ℝ => ((α / (α ^ 2 + y ^ 2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hcont1
  have hcont2C : Continuous
      (fun y : ℝ => ((y / (α ^ 2 + y ^ 2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hcont2
  rw [intervalIntegral.integral_sub
    (f := fun y : ℝ => ((α / (α ^ 2 + y ^ 2) : ℝ) : ℂ))
    (g := fun y : ℝ => ((y / (α ^ 2 + y ^ 2) : ℝ) : ℂ) * I)
    (hcont1C.intervalIntegrable (-T) T)
    ((hcont2C.mul continuous_const).intervalIntegrable (-T) T)]
  rw [intervalIntegral.integral_mul_const]
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
  rw [hreal, hodd]
  simp
  ring

theorem simplePoleNegativeVertical (α T : ℝ) (hα : 0 < α) :
    -(I * (∫ y : ℝ in -T..T,
      (((-(α : ℂ)) + (y : ℂ) * I)⁻¹))) =
      (2 * I : ℂ) * (Real.arctan (T / α) : ℂ) := by
  have hpoint : ∀ y : ℝ,
      ((-(α : ℂ)) + (y : ℂ) * I)⁻¹ =
        -(((α : ℂ) + ((-y : ℝ) : ℂ) * I)⁻¹) := by
    intro y
    have hbase : (-(α : ℂ)) + (y : ℂ) * I =
        -((α : ℂ) + ((-y : ℝ) : ℂ) * I) := by
      push_cast
      ring
    rw [hbase, inv_neg]
  have hcomp := intervalIntegral.integral_comp_neg
    (a := -T) (b := T)
    (f := fun y : ℝ => (((α : ℂ) + (y : ℂ) * I)⁻¹))
  simp only [neg_neg] at hcomp
  rw [intervalIntegral.integral_congr (fun y _ => hpoint y)]
  rw [intervalIntegral.integral_neg]
  rw [hcomp]
  convert simplePolePositiveVertical α T hα using 1 <;> ring

theorem rectangularBoundaryIntegral_simplePole
    (p σL σR T : ℝ) (hL : σL < p) (hR : p < σR) (hT : 0 < T) :
    rectangularBoundaryIntegral (fun s : ℂ => (s - (p : ℂ))⁻¹)
      (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) =
        2 * Real.pi * I := by
  have hright :
      rectangularRightEdge (fun s : ℂ => (s - (p : ℂ))⁻¹)
          (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) =
        (2 * I : ℂ) * (Real.arctan (T / (σR - p)) : ℂ) := by
    convert simplePolePositiveVertical (σR - p) T (sub_pos.mpr hR) using 1 <;>
      simp [rectangularRightEdge, symmetricLowerCorner,
        symmetricUpperCorner, mul_comm] <;> ring
  have hleft :
      rectangularLeftEdge (fun s : ℂ => (s - (p : ℂ))⁻¹)
          (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) =
        (2 * I : ℂ) * (Real.arctan (T / (p - σL)) : ℂ) := by
    convert simplePoleNegativeVertical (p - σL) T (sub_pos.mpr hL) using 1 <;>
      simp [rectangularLeftEdge, symmetricLowerCorner,
        symmetricUpperCorner, mul_comm] <;> ring
  rw [show rectangularBoundaryIntegral
      (fun s : ℂ => (s - (p : ℂ))⁻¹)
      (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) =
        symmetricHorizontalEdges (fun s : ℂ => (s - (p : ℂ))⁻¹)
          σL σR T +
        rectangularRightEdge (fun s : ℂ => (s - (p : ℂ))⁻¹)
          (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) +
        rectangularLeftEdge (fun s : ℂ => (s - (p : ℂ))⁻¹)
          (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) by
    rfl]
  unfold symmetricHorizontalEdges
  rw [simplePoleHorizontalPair p σL σR T hT, hright, hleft]
  have hTL : 0 < (p - σL) / T := div_pos (sub_pos.mpr hL) hT
  have hTR : 0 < (σR - p) / T := div_pos (sub_pos.mpr hR) hT
  have hdivL : T / (p - σL) = ((p - σL) / T)⁻¹ := by
    field_simp [hT.ne', (sub_pos.mpr hL).ne']
  have hdivR : T / (σR - p) = ((σR - p) / T)⁻¹ := by
    field_simp [hT.ne', (sub_pos.mpr hR).ne']
  rw [hdivL, hdivR]
  rw [Real.arctan_inv_of_pos hTL, Real.arctan_inv_of_pos hTR]
  rw [show (σL - p) / T = -((p - σL) / T) by ring,
    Real.arctan_neg]
  push_cast
  ring

theorem integral_doublePole_horizontal
    (c p : ℂ) (a b : ℝ)
    (hne : ∀ x ∈ Set.uIcc a b, (x : ℂ) + c - p ≠ 0) :
    (∫ x : ℝ in a..b, (((x : ℂ) + c - p)⁻¹) ^ 2) =
      -(((b : ℂ) + c - p)⁻¹) -
        (-(((a : ℂ) + c - p)⁻¹)) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    have hg : HasDerivAt (fun z : ℂ => z + c - p) 1 (x : ℂ) := by
      convert ((hasDerivAt_id (x := (x : ℂ))).add_const c).sub_const p using 1 <;>
        simp
    have hi := (hg.inv (hne x hx)).neg
    convert hi.comp_ofReal using 1 <;> simp <;> ring
  · have hcont : Continuous (fun x : ℝ => (x : ℂ) + c - p) := by
      fun_prop
    exact ((hcont.continuousOn.inv₀ hne).pow 2).intervalIntegrable

theorem integral_doublePole_vertical
    (c p : ℂ) (a b : ℝ)
    (hne : ∀ y ∈ Set.uIcc a b, c + (y : ℂ) * I - p ≠ 0) :
    (∫ y : ℝ in a..b, I * ((c + (y : ℂ) * I - p)⁻¹) ^ 2) =
      -((c + (b : ℂ) * I - p)⁻¹) -
        (-((c + (a : ℂ) * I - p)⁻¹)) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro y hy
    have hg : HasDerivAt (fun z : ℂ => c + z * I - p) I (y : ℂ) := by
      convert (((hasDerivAt_id (x := (y : ℂ))).mul_const I).const_add c).sub_const p using 1 <;>
        simp <;> ring
    have hi := (hg.inv (hne y hy)).neg
    convert hi.comp_ofReal using 1 <;> simp <;> ring
  · have hcont : Continuous (fun y : ℝ => c + (y : ℂ) * I - p) := by
      fun_prop
    exact ((continuousOn_const.mul
      ((hcont.continuousOn.inv₀ hne).pow 2)).intervalIntegrable)

theorem rectangularBoundaryIntegral_doublePole
    (p σL σR T : ℝ) (hL : σL < p) (hR : p < σR) (hT : 0 < T) :
    rectangularBoundaryIntegral
      (fun s : ℂ => ((s - (p : ℂ))⁻¹) ^ 2)
      (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) = 0 := by
  let ll : ℂ := (σL : ℂ) - (T : ℂ) * I
  let lr : ℂ := (σR : ℂ) - (T : ℂ) * I
  let ul : ℂ := (σL : ℂ) + (T : ℂ) * I
  let ur : ℂ := (σR : ℂ) + (T : ℂ) * I
  have hminus : ∀ x : ℝ, (x : ℂ) - (T : ℂ) * I - (p : ℂ) ≠ 0 := by
    intro x h
    have hi := congrArg Complex.im h
    simp at hi
    linarith
  have hplus : ∀ x : ℝ, (x : ℂ) + (T : ℂ) * I - (p : ℂ) ≠ 0 := by
    intro x h
    have hi := congrArg Complex.im h
    simp at hi
    linarith
  have hright0 : ∀ y : ℝ, (σR : ℂ) + (y : ℂ) * I - (p : ℂ) ≠ 0 := by
    intro y h
    have hr := congrArg Complex.re h
    simp at hr
    linarith
  have hleft0 : ∀ y : ℝ, (σL : ℂ) + (y : ℂ) * I - (p : ℂ) ≠ 0 := by
    intro y h
    have hr := congrArg Complex.re h
    simp at hr
    linarith
  have hlower :
      rectangularLowerEdge
        (fun s : ℂ => ((s - (p : ℂ))⁻¹) ^ 2)
        (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) =
          -(lr - (p : ℂ))⁻¹ - (-(ll - (p : ℂ))⁻¹) := by
    convert integral_doublePole_horizontal (-(T : ℂ) * I) (p : ℂ) σL σR
      (fun x _ => by convert hminus x using 1 <;> ring) using 1 <;>
      simp [rectangularLowerEdge, symmetricLowerCorner,
        symmetricUpperCorner, ll, lr] <;> ring
  have hupper :
      rectangularUpperEdge
        (fun s : ℂ => ((s - (p : ℂ))⁻¹) ^ 2)
        (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) =
          -(-(ur - (p : ℂ))⁻¹ - (-(ul - (p : ℂ))⁻¹)) := by
    convert congrArg Neg.neg
      (integral_doublePole_horizontal ((T : ℂ) * I) (p : ℂ) σL σR
        (fun x _ => hplus x)) using 1 <;>
      simp [rectangularUpperEdge, symmetricLowerCorner,
        symmetricUpperCorner, ul, ur] <;> ring
  have hrightEdge :
      rectangularRightEdge
        (fun s : ℂ => ((s - (p : ℂ))⁻¹) ^ 2)
        (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) =
          -(ur - (p : ℂ))⁻¹ - (-(lr - (p : ℂ))⁻¹) := by
    convert integral_doublePole_vertical (σR : ℂ) (p : ℂ) (-T) T
      (fun y _ => hright0 y) using 1 <;>
      simp [rectangularRightEdge, symmetricLowerCorner,
        symmetricUpperCorner, intervalIntegral.integral_const_mul,
        lr, ur, mul_comm] <;> ring
  have hleftEdge :
      rectangularLeftEdge
        (fun s : ℂ => ((s - (p : ℂ))⁻¹) ^ 2)
        (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) =
          -(-(ul - (p : ℂ))⁻¹ - (-(ll - (p : ℂ))⁻¹)) := by
    convert congrArg Neg.neg
      (integral_doublePole_vertical (σL : ℂ) (p : ℂ) (-T) T
        (fun y _ => hleft0 y)) using 1 <;>
      simp [rectangularLeftEdge, symmetricLowerCorner,
        symmetricUpperCorner, intervalIntegral.integral_const_mul,
        ll, ul, mul_comm] <;> ring
  unfold rectangularBoundaryIntegral
  rw [hlower, hupper, hrightEdge, hleftEdge]
  ring

/-! A cubic pole also has zero rectangular boundary integral.  We prove this
directly from the primitive `-1 / (2 (s-p)^2)`, so no general residue theorem
is imported. -/

theorem integral_triplePole_horizontal
    (c p : ℂ) (a b : ℝ)
    (hne : ∀ x ∈ Set.uIcc a b, (x : ℂ) + c - p ≠ 0) :
    (∫ x : ℝ in a..b, (((x : ℂ) + c - p)⁻¹) ^ 3) =
      (-(2 : ℂ)⁻¹ * (((b : ℂ) + c - p)⁻¹) ^ 2) -
        (-(2 : ℂ)⁻¹ * (((a : ℂ) + c - p)⁻¹) ^ 2) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    have hg : HasDerivAt (fun z : ℂ => z + c - p) 1 (x : ℂ) := by
      convert ((hasDerivAt_id (x := (x : ℂ))).add_const c).sub_const p using 1 <;>
        simp
    have hi := (hg.inv (hne x hx)).pow 2
    have hscaled := hi.const_mul (-(2 : ℂ)⁻¹)
    convert hscaled.comp_ofReal using 1 <;> simp <;> field_simp <;> ring
  · have hcont : Continuous (fun x : ℝ => (x : ℂ) + c - p) := by
      fun_prop
    exact ((hcont.continuousOn.inv₀ hne).pow 3).intervalIntegrable

theorem integral_triplePole_vertical
    (c p : ℂ) (a b : ℝ)
    (hne : ∀ y ∈ Set.uIcc a b, c + (y : ℂ) * I - p ≠ 0) :
    (∫ y : ℝ in a..b, I * ((c + (y : ℂ) * I - p)⁻¹) ^ 3) =
      (-(2 : ℂ)⁻¹ * ((c + (b : ℂ) * I - p)⁻¹) ^ 2) -
        (-(2 : ℂ)⁻¹ * ((c + (a : ℂ) * I - p)⁻¹) ^ 2) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro y hy
    have hg : HasDerivAt (fun z : ℂ => c + z * I - p) I (y : ℂ) := by
      convert (((hasDerivAt_id (x := (y : ℂ))).mul_const I).const_add c).sub_const p using 1 <;>
        simp <;> ring
    have hi := (hg.inv (hne y hy)).pow 2
    have hscaled := hi.const_mul (-(2 : ℂ)⁻¹)
    convert hscaled.comp_ofReal using 1 <;> simp <;> field_simp <;> ring
  · have hcont : Continuous (fun y : ℝ => c + (y : ℂ) * I - p) := by
      fun_prop
    exact ((continuousOn_const.mul
      ((hcont.continuousOn.inv₀ hne).pow 3)).intervalIntegrable)

theorem rectangularBoundaryIntegral_triplePole
    (p σL σR T : ℝ) (hL : σL < p) (hR : p < σR) (hT : 0 < T) :
    rectangularBoundaryIntegral
      (fun s : ℂ => ((s - (p : ℂ))⁻¹) ^ 3)
      (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) = 0 := by
  let ll : ℂ := (σL : ℂ) - (T : ℂ) * I
  let lr : ℂ := (σR : ℂ) - (T : ℂ) * I
  let ul : ℂ := (σL : ℂ) + (T : ℂ) * I
  let ur : ℂ := (σR : ℂ) + (T : ℂ) * I
  have hminus : ∀ x : ℝ, (x : ℂ) - (T : ℂ) * I - (p : ℂ) ≠ 0 := by
    intro x h
    have hi := congrArg Complex.im h
    simp at hi
    linarith
  have hplus : ∀ x : ℝ, (x : ℂ) + (T : ℂ) * I - (p : ℂ) ≠ 0 := by
    intro x h
    have hi := congrArg Complex.im h
    simp at hi
    linarith
  have hright0 : ∀ y : ℝ, (σR : ℂ) + (y : ℂ) * I - (p : ℂ) ≠ 0 := by
    intro y h
    have hr := congrArg Complex.re h
    simp at hr
    linarith
  have hleft0 : ∀ y : ℝ, (σL : ℂ) + (y : ℂ) * I - (p : ℂ) ≠ 0 := by
    intro y h
    have hr := congrArg Complex.re h
    simp at hr
    linarith
  let P : ℂ → ℂ := fun z => -(2 : ℂ)⁻¹ * ((z - (p : ℂ))⁻¹) ^ 2
  have hlower :
      rectangularLowerEdge (fun s : ℂ => ((s - (p : ℂ))⁻¹) ^ 3)
          (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) =
        P lr - P ll := by
    convert integral_triplePole_horizontal (-(T : ℂ) * I) (p : ℂ) σL σR
      (fun x _ => by convert hminus x using 1 <;> ring) using 1 <;>
      simp [rectangularLowerEdge, symmetricLowerCorner,
        symmetricUpperCorner, P, ll, lr] <;> ring
  have hupper :
      rectangularUpperEdge (fun s : ℂ => ((s - (p : ℂ))⁻¹) ^ 3)
          (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) =
        -(P ur - P ul) := by
    convert congrArg Neg.neg
      (integral_triplePole_horizontal ((T : ℂ) * I) (p : ℂ) σL σR
        (fun x _ => hplus x)) using 1 <;>
      simp [rectangularUpperEdge, symmetricLowerCorner,
        symmetricUpperCorner, P, ul, ur] <;> ring
  have hrightEdge :
      rectangularRightEdge (fun s : ℂ => ((s - (p : ℂ))⁻¹) ^ 3)
          (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) =
        P ur - P lr := by
    convert integral_triplePole_vertical (σR : ℂ) (p : ℂ) (-T) T
      (fun y _ => hright0 y) using 1 <;>
      simp [rectangularRightEdge, symmetricLowerCorner,
        symmetricUpperCorner, intervalIntegral.integral_const_mul,
        P, lr, ur, mul_comm] <;> ring
  have hleftEdge :
      rectangularLeftEdge (fun s : ℂ => ((s - (p : ℂ))⁻¹) ^ 3)
          (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) =
        -(P ul - P ll) := by
    convert congrArg Neg.neg
      (integral_triplePole_vertical (σL : ℂ) (p : ℂ) (-T) T
        (fun y _ => hleft0 y)) using 1 <;>
      simp [rectangularLeftEdge, symmetricLowerCorner,
        symmetricUpperCorner, intervalIntegral.integral_const_mul,
        P, ll, ul, mul_comm] <;> ring
  unfold rectangularBoundaryIntegral
  rw [hlower, hupper, hrightEdge, hleftEdge]
  ring

theorem rectangularBoundaryIntegral_add
    (f g : ℂ → ℂ) (z w : ℂ) (hf : Continuous f) (hg : Continuous g) :
    rectangularBoundaryIntegral (fun s => f s + g s) z w =
      rectangularBoundaryIntegral f z w + rectangularBoundaryIntegral g z w := by
  have hfl : Continuous (fun x : ℝ => f (x + z.im * I)) := by fun_prop
  have hgl : Continuous (fun x : ℝ => g (x + z.im * I)) := by fun_prop
  have hfu : Continuous (fun x : ℝ => f (x + w.im * I)) := by fun_prop
  have hgu : Continuous (fun x : ℝ => g (x + w.im * I)) := by fun_prop
  have hfr : Continuous (fun y : ℝ => f (w.re + y * I)) := by fun_prop
  have hgr : Continuous (fun y : ℝ => g (w.re + y * I)) := by fun_prop
  have hfle : Continuous (fun y : ℝ => f (z.re + y * I)) := by fun_prop
  have hgle : Continuous (fun y : ℝ => g (z.re + y * I)) := by fun_prop
  unfold rectangularBoundaryIntegral rectangularLowerEdge rectangularUpperEdge
    rectangularRightEdge rectangularLeftEdge
  rw [intervalIntegral.integral_add
    (hfl.intervalIntegrable _ _) (hgl.intervalIntegrable _ _)]
  rw [intervalIntegral.integral_add
    (hfu.intervalIntegrable _ _) (hgu.intervalIntegrable _ _)]
  rw [intervalIntegral.integral_add
    (hfr.intervalIntegrable _ _) (hgr.intervalIntegrable _ _)]
  rw [intervalIntegral.integral_add
    (hfle.intervalIntegrable _ _) (hgle.intervalIntegrable _ _)]
  ring

theorem rectangularBoundaryIntegral_const_mul
    (c : ℂ) (f : ℂ → ℂ) (z w : ℂ) :
    rectangularBoundaryIntegral (fun s => c * f s) z w =
      c * rectangularBoundaryIntegral f z w := by
  unfold rectangularBoundaryIntegral rectangularLowerEdge rectangularUpperEdge
    rectangularRightEdge rectangularLeftEdge
  simp_rw [intervalIntegral.integral_const_mul]
  ring

theorem rectangularBoundaryIntegral_add_symmetric
    (f g : ℂ → ℂ) (σL σR T : ℝ)
    (hfm : Continuous (fun x : ℝ => f ((x : ℂ) - (T : ℂ) * I)))
    (hgm : Continuous (fun x : ℝ => g ((x : ℂ) - (T : ℂ) * I)))
    (hfp : Continuous (fun x : ℝ => f ((x : ℂ) + (T : ℂ) * I)))
    (hgp : Continuous (fun x : ℝ => g ((x : ℂ) + (T : ℂ) * I)))
    (hfl : Continuous (fun y : ℝ => f ((σL : ℂ) + (y : ℂ) * I)))
    (hgl : Continuous (fun y : ℝ => g ((σL : ℂ) + (y : ℂ) * I)))
    (hfr : Continuous (fun y : ℝ => f ((σR : ℂ) + (y : ℂ) * I)))
    (hgr : Continuous (fun y : ℝ => g ((σR : ℂ) + (y : ℂ) * I))) :
    rectangularBoundaryIntegral (fun s => f s + g s)
        (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) =
      rectangularBoundaryIntegral f
          (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) +
        rectangularBoundaryIntegral g
          (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) := by
  unfold rectangularBoundaryIntegral rectangularLowerEdge rectangularUpperEdge
    rectangularRightEdge rectangularLeftEdge symmetricLowerCorner
    symmetricUpperCorner
  simp [Complex.mul_re, Complex.mul_im]
  simp only [← sub_eq_add_neg]
  rw [intervalIntegral.integral_add
    (hfm.intervalIntegrable _ _) (hgm.intervalIntegrable _ _)]
  rw [intervalIntegral.integral_add
    (hfp.intervalIntegrable _ _) (hgp.intervalIntegrable _ _)]
  rw [intervalIntegral.integral_add
    (hfr.intervalIntegrable _ _) (hgr.intervalIntegrable _ _)]
  rw [intervalIntegral.integral_add
    (hfl.intervalIntegrable _ _) (hgl.intervalIntegrable _ _)]
  ring

structure TwoPoleRectangleSubtractionData (f : ℂ → ℂ) where
  regularized : ℂ → ℂ
  doubleCoefficient : ℂ
  residueAtZero : ℂ
  residueAtOne : ℂ
  decomposition : ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
    f s = regularized s +
      doubleCoefficient * (s⁻¹) ^ 2 +
      residueAtZero * s⁻¹ + residueAtOne * (s - 1)⁻¹

/-- The original global package is retained for entire regularized
remainders such as the Gaussian kernel. -/
structure TwoPoleRectangleSubtraction (f : ℂ → ℂ)
    extends TwoPoleRectangleSubtractionData f where
  regularized_differentiable : Differentiable ℂ regularized

theorem TwoPoleRectangleSubtractionData.boundary_eq_of_differentiableOn
    {f : ℂ → ℂ} (H : TwoPoleRectangleSubtractionData f)
    (σL σR T : ℝ) (hL : σL < 0) (hR : 1 < σR) (hT : 0 < T)
    (hregOn : DifferentiableOn ℂ H.regularized
      ([[σL, σR]] ×ℂ [[-T, T]])) :
    rectangularBoundaryIntegral f
      (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) =
        2 * Real.pi * I * (H.residueAtZero + H.residueAtOne) := by
  let z := symmetricLowerCorner σL T
  let w := symmetricUpperCorner σR T
  let polePart : ℂ → ℂ := fun s =>
    H.doubleCoefficient * (s⁻¹) ^ 2 +
      H.residueAtZero * s⁻¹ + H.residueAtOne * (s - 1)⁻¹
  have hσ : σL ≤ σR :=
    le_of_lt (lt_trans hL (lt_trans zero_lt_one hR))
  have hminus0 : ∀ x : ℝ,
      (x : ℂ) - (T : ℂ) * I ≠ 0 := by
    intro x hx
    have hi := congrArg Complex.im hx
    simp at hi
    linarith
  have hminus1 : ∀ x : ℝ,
      (x : ℂ) - (T : ℂ) * I ≠ 1 := by
    intro x hx
    have hi := congrArg Complex.im hx
    simp at hi
    linarith
  have hplus0 : ∀ x : ℝ,
      (x : ℂ) + (T : ℂ) * I ≠ 0 := by
    intro x hx
    have hi := congrArg Complex.im hx
    simp at hi
    linarith
  have hplus1 : ∀ x : ℝ,
      (x : ℂ) + (T : ℂ) * I ≠ 1 := by
    intro x hx
    have hi := congrArg Complex.im hx
    simp at hi
    linarith
  have hleft0 : ∀ y : ℝ,
      (σL : ℂ) + (y : ℂ) * I ≠ 0 := by
    intro y hy
    have hr := congrArg Complex.re hy
    simp at hr
    linarith
  have hleft1 : ∀ y : ℝ,
      (σL : ℂ) + (y : ℂ) * I ≠ 1 := by
    intro y hy
    have hr := congrArg Complex.re hy
    simp at hr
    linarith
  have hright0 : ∀ y : ℝ,
      (σR : ℂ) + (y : ℂ) * I ≠ 0 := by
    intro y hy
    have hr := congrArg Complex.re hy
    simp at hr
    linarith
  have hright1 : ∀ y : ℝ,
      (σR : ℂ) + (y : ℂ) * I ≠ 1 := by
    intro y hy
    have hr := congrArg Complex.re hy
    simp at hr
    linarith
  have hdecMinus (x : ℝ) :
      f ((x : ℂ) - (T : ℂ) * I) =
        H.regularized ((x : ℂ) - (T : ℂ) * I) +
          polePart ((x : ℂ) - (T : ℂ) * I) := by
    simpa [polePart, add_assoc] using
      H.decomposition ((x : ℂ) - (T : ℂ) * I) (hminus0 x) (hminus1 x)
  have hdecPlus (x : ℝ) :
      f ((x : ℂ) + (T : ℂ) * I) =
        H.regularized ((x : ℂ) + (T : ℂ) * I) +
          polePart ((x : ℂ) + (T : ℂ) * I) := by
    simpa [polePart, add_assoc] using
      H.decomposition ((x : ℂ) + (T : ℂ) * I) (hplus0 x) (hplus1 x)
  have hdecLeft (y : ℝ) :
      f ((σL : ℂ) + (y : ℂ) * I) =
        H.regularized ((σL : ℂ) + (y : ℂ) * I) +
          polePart ((σL : ℂ) + (y : ℂ) * I) := by
    simpa [polePart, add_assoc] using
      H.decomposition ((σL : ℂ) + (y : ℂ) * I) (hleft0 y) (hleft1 y)
  have hdecRight (y : ℝ) :
      f ((σR : ℂ) + (y : ℂ) * I) =
        H.regularized ((σR : ℂ) + (y : ℂ) * I) +
          polePart ((σR : ℂ) + (y : ℂ) * I) := by
    simpa [polePart, add_assoc] using
      H.decomposition ((σR : ℂ) + (y : ℂ) * I) (hright0 y) (hright1 y)
  have hboundary_congr :
      rectangularBoundaryIntegral f z w =
        rectangularBoundaryIntegral (fun s => H.regularized s + polePart s) z w := by
    unfold rectangularBoundaryIntegral rectangularLowerEdge rectangularUpperEdge
      rectangularRightEdge rectangularLeftEdge z w symmetricLowerCorner
      symmetricUpperCorner
    simp [Complex.mul_re, Complex.mul_im]
    simp only [← sub_eq_add_neg]
    have hm : (∫ x : ℝ in σL..σR,
        f ((x : ℂ) - (T : ℂ) * I)) =
        ∫ x : ℝ in σL..σR,
          H.regularized ((x : ℂ) - (T : ℂ) * I) +
            polePart ((x : ℂ) - (T : ℂ) * I) := by
      exact intervalIntegral.integral_congr (fun x _ => hdecMinus x)
    have hp : (∫ x : ℝ in σL..σR,
        f ((x : ℂ) + (T : ℂ) * I)) =
        ∫ x : ℝ in σL..σR,
          H.regularized ((x : ℂ) + (T : ℂ) * I) +
            polePart ((x : ℂ) + (T : ℂ) * I) := by
      exact intervalIntegral.integral_congr (fun x _ => hdecPlus x)
    have hl : (∫ y : ℝ in -T..T,
        f ((σL : ℂ) + (y : ℂ) * I)) =
        ∫ y : ℝ in -T..T,
          H.regularized ((σL : ℂ) + (y : ℂ) * I) +
            polePart ((σL : ℂ) + (y : ℂ) * I) := by
      exact intervalIntegral.integral_congr (fun y _ => hdecLeft y)
    have hr : (∫ y : ℝ in -T..T,
        f ((σR : ℂ) + (y : ℂ) * I)) =
        ∫ y : ℝ in -T..T,
          H.regularized ((σR : ℂ) + (y : ℂ) * I) +
            polePart ((σR : ℂ) + (y : ℂ) * I) := by
      exact intervalIntegral.integral_congr (fun y _ => hdecRight y)
    rw [hm, hp, hl, hr]
  have hpMinus : Continuous (fun x : ℝ =>
      polePart ((x : ℂ) - (T : ℂ) * I)) := by
    unfold polePart
    have hp : Continuous (fun x : ℝ => (x : ℂ) - (T : ℂ) * I) := by fun_prop
    exact (continuous_const.mul ((hp.inv₀ hminus0).pow 2)).add
      (continuous_const.mul (hp.inv₀ hminus0)) |>.add
        (continuous_const.mul ((hp.sub continuous_const).inv₀
          (fun x h => (hminus1 x) (sub_eq_zero.mp h))))
  have hpPlus : Continuous (fun x : ℝ =>
      polePart ((x : ℂ) + (T : ℂ) * I)) := by
    unfold polePart
    have hp : Continuous (fun x : ℝ => (x : ℂ) + (T : ℂ) * I) := by fun_prop
    exact (continuous_const.mul ((hp.inv₀ hplus0).pow 2)).add
      (continuous_const.mul (hp.inv₀ hplus0)) |>.add
        (continuous_const.mul ((hp.sub continuous_const).inv₀
          (fun x h => (hplus1 x) (sub_eq_zero.mp h))))
  have hpLeft : Continuous (fun y : ℝ =>
      polePart ((σL : ℂ) + (y : ℂ) * I)) := by
    unfold polePart
    have hp : Continuous (fun y : ℝ => (σL : ℂ) + (y : ℂ) * I) := by fun_prop
    exact (continuous_const.mul ((hp.inv₀ hleft0).pow 2)).add
      (continuous_const.mul (hp.inv₀ hleft0)) |>.add
        (continuous_const.mul ((hp.sub continuous_const).inv₀
          (fun y h => (hleft1 y) (sub_eq_zero.mp h))))
  have hpRight : Continuous (fun y : ℝ =>
      polePart ((σR : ℂ) + (y : ℂ) * I)) := by
    unfold polePart
    have hp : Continuous (fun y : ℝ => (σR : ℂ) + (y : ℂ) * I) := by fun_prop
    exact (continuous_const.mul ((hp.inv₀ hright0).pow 2)).add
      (continuous_const.mul (hp.inv₀ hright0)) |>.add
        (continuous_const.mul ((hp.sub continuous_const).inv₀
          (fun y h => (hright1 y) (sub_eq_zero.mp h))))
  have hadd :
      rectangularBoundaryIntegral (fun s => H.regularized s + polePart s) z w =
        rectangularBoundaryIntegral H.regularized z w +
          rectangularBoundaryIntegral polePart z w := by
    unfold rectangularBoundaryIntegral rectangularLowerEdge rectangularUpperEdge
      rectangularRightEdge rectangularLeftEdge z w symmetricLowerCorner
      symmetricUpperCorner
    simp [Complex.mul_re, Complex.mul_im]
    simp only [← sub_eq_add_neg]
    have hrm : IntervalIntegrable (fun x : ℝ =>
        H.regularized ((x : ℂ) - (T : ℂ) * I)) volume σL σR := by
      apply ContinuousOn.intervalIntegrable
      exact hregOn.continuousOn.comp (by fun_prop) (by
        intro x hx
        simpa [mem_reProdIm] using hx)
    have hrp : IntervalIntegrable (fun x : ℝ =>
        H.regularized ((x : ℂ) + (T : ℂ) * I)) volume σL σR := by
      apply ContinuousOn.intervalIntegrable
      exact hregOn.continuousOn.comp (by fun_prop) (by
        intro x hx
        simpa [mem_reProdIm] using hx)
    have hrl : IntervalIntegrable (fun y : ℝ =>
        H.regularized ((σL : ℂ) + (y : ℂ) * I)) volume (-T) T := by
      apply ContinuousOn.intervalIntegrable
      exact hregOn.continuousOn.comp (by fun_prop) (by
        intro y hy
        simpa [mem_reProdIm, uIcc_of_le hσ] using And.intro hσ hy)
    have hrr : IntervalIntegrable (fun y : ℝ =>
        H.regularized ((σR : ℂ) + (y : ℂ) * I)) volume (-T) T := by
      apply ContinuousOn.intervalIntegrable
      exact hregOn.continuousOn.comp (by fun_prop) (by
        intro y hy
        simpa [mem_reProdIm, uIcc_of_le hσ] using And.intro hσ hy)
    rw [intervalIntegral.integral_add
      (f := fun x : ℝ => H.regularized ((x : ℂ) - (T : ℂ) * I))
      (g := fun x : ℝ => polePart ((x : ℂ) - (T : ℂ) * I))
      hrm
      (hpMinus.intervalIntegrable σL σR)]
    rw [intervalIntegral.integral_add
      (f := fun x : ℝ => H.regularized ((x : ℂ) + (T : ℂ) * I))
      (g := fun x : ℝ => polePart ((x : ℂ) + (T : ℂ) * I))
      hrp
      (hpPlus.intervalIntegrable σL σR)]
    rw [intervalIntegral.integral_add
      (f := fun y : ℝ => H.regularized ((σR : ℂ) + (y : ℂ) * I))
      (g := fun y : ℝ => polePart ((σR : ℂ) + (y : ℂ) * I))
      hrr
      (hpRight.intervalIntegrable (-T) T)]
    rw [intervalIntegral.integral_add
      (f := fun y : ℝ => H.regularized ((σL : ℂ) + (y : ℂ) * I))
      (g := fun y : ℝ => polePart ((σL : ℂ) + (y : ℂ) * I))
      hrl
      (hpLeft.intervalIntegrable (-T) T)]
    ring
  rw [hboundary_congr]
  rw [hadd]
  rw [rectangularBoundaryIntegral_eq_zero H.regularized z w (by
    simpa [z, w, symmetricLowerCorner, symmetricUpperCorner] using hregOn)]
  have hd0 : rectangularBoundaryIntegral (fun s : ℂ => (s⁻¹) ^ 2) z w = 0 := by
    simpa [z, w] using rectangularBoundaryIntegral_doublePole
      0 σL σR T hL (lt_trans zero_lt_one hR) hT
  have hs0 : rectangularBoundaryIntegral (fun s : ℂ => s⁻¹) z w =
      2 * Real.pi * I := by
    simpa [z, w] using rectangularBoundaryIntegral_simplePole
      0 σL σR T hL (lt_trans zero_lt_one hR) hT
  have hs1 : rectangularBoundaryIntegral (fun s : ℂ => (s - 1)⁻¹) z w =
      2 * Real.pi * I := by
    simpa [z, w] using rectangularBoundaryIntegral_simplePole
      1 σL σR T (lt_trans hL zero_lt_one) hR hT
  let d : ℂ → ℂ := fun s => H.doubleCoefficient * (s⁻¹) ^ 2
  let b : ℂ → ℂ := fun s => H.residueAtZero * s⁻¹
  let c : ℂ → ℂ := fun s => H.residueAtOne * (s - 1)⁻¹
  have hpathMinus : Continuous (fun x : ℝ => (x : ℂ) - (T : ℂ) * I) := by fun_prop
  have hpathPlus : Continuous (fun x : ℝ => (x : ℂ) + (T : ℂ) * I) := by fun_prop
  have hpathLeft : Continuous (fun y : ℝ => (σL : ℂ) + (y : ℂ) * I) := by fun_prop
  have hpathRight : Continuous (fun y : ℝ => (σR : ℂ) + (y : ℂ) * I) := by fun_prop
  have h0m := hpathMinus.inv₀ hminus0
  have h0p := hpathPlus.inv₀ hplus0
  have h0l := hpathLeft.inv₀ hleft0
  have h0r := hpathRight.inv₀ hright0
  have h1m := (hpathMinus.sub continuous_const).inv₀
    (fun x h => (hminus1 x) (sub_eq_zero.mp h))
  have h1p := (hpathPlus.sub continuous_const).inv₀
    (fun x h => (hplus1 x) (sub_eq_zero.mp h))
  have h1l := (hpathLeft.sub continuous_const).inv₀
    (fun y h => (hleft1 y) (sub_eq_zero.mp h))
  have h1r := (hpathRight.sub continuous_const).inv₀
    (fun y h => (hright1 y) (sub_eq_zero.mp h))
  have hdb : rectangularBoundaryIntegral (fun s => d s + b s)
      (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) =
      rectangularBoundaryIntegral d
          (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) +
        rectangularBoundaryIntegral b
          (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) := by
    apply rectangularBoundaryIntegral_add_symmetric d b σL σR T
    all_goals
      dsimp [d, b]
      first
      | exact continuous_const.mul (h0m.pow 2)
      | exact continuous_const.mul h0m
      | exact continuous_const.mul (h0p.pow 2)
      | exact continuous_const.mul h0p
      | exact continuous_const.mul (h0l.pow 2)
      | exact continuous_const.mul h0l
      | exact continuous_const.mul (h0r.pow 2)
      | exact continuous_const.mul h0r
  have hdbc : rectangularBoundaryIntegral (fun s => (d s + b s) + c s)
      (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) =
      rectangularBoundaryIntegral (fun s => d s + b s)
          (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) +
        rectangularBoundaryIntegral c
          (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) := by
    apply rectangularBoundaryIntegral_add_symmetric (fun s => d s + b s) c σL σR T
    all_goals
      dsimp [d, b, c]
      first
      | exact (continuous_const.mul (h0m.pow 2)).add (continuous_const.mul h0m)
      | exact continuous_const.mul h1m
      | exact (continuous_const.mul (h0p.pow 2)).add (continuous_const.mul h0p)
      | exact continuous_const.mul h1p
      | exact (continuous_const.mul (h0l.pow 2)).add (continuous_const.mul h0l)
      | exact continuous_const.mul h1l
      | exact (continuous_const.mul (h0r.pow 2)).add (continuous_const.mul h0r)
      | exact continuous_const.mul h1r
  have hexpand : rectangularBoundaryIntegral polePart z w =
      H.doubleCoefficient * rectangularBoundaryIntegral
          (fun s : ℂ => (s⁻¹) ^ 2) z w +
        H.residueAtZero * rectangularBoundaryIntegral
          (fun s : ℂ => s⁻¹) z w +
        H.residueAtOne * rectangularBoundaryIntegral
          (fun s : ℂ => (s - 1)⁻¹) z w := by
    change rectangularBoundaryIntegral (fun s => (d s + b s) + c s) z w = _
    rw [show rectangularBoundaryIntegral (fun s => (d s + b s) + c s) z w =
        rectangularBoundaryIntegral (fun s => d s + b s) z w +
          rectangularBoundaryIntegral c z w by simpa [z, w] using hdbc]
    rw [show rectangularBoundaryIntegral (fun s => d s + b s) z w =
        rectangularBoundaryIntegral d z w + rectangularBoundaryIntegral b z w by
          simpa [z, w] using hdb]
    dsimp [d, b, c]
    rw [rectangularBoundaryIntegral_const_mul,
      rectangularBoundaryIntegral_const_mul,
      rectangularBoundaryIntegral_const_mul]
  rw [hexpand, hd0, hs0, hs1]
  ring

/-- The globally holomorphic package remains a convenient special case of
the localized rectangle theorem. -/
theorem TwoPoleRectangleSubtraction.boundary_eq
    {f : ℂ → ℂ} (H : TwoPoleRectangleSubtraction f)
    (σL σR T : ℝ) (hL : σL < 0) (hR : 1 < σR) (hT : 0 < T) :
    rectangularBoundaryIntegral f
      (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) =
        2 * Real.pi * I * (H.residueAtZero + H.residueAtOne) := by
  exact H.toTwoPoleRectangleSubtractionData.boundary_eq_of_differentiableOn
    σL σR T hL hR hT
    H.regularized_differentiable.differentiableOn

/-! ## Triple-plus-simple correction ledger -/

/-- Data for a correction-preserving rectangle with the actual active H15
pole inventory. The `boundary_split` field is only finite integral
linearity; the analytic input is exposed in `regularized_differentiableOn`. -/
structure TriplePlusSimpleRectangleSubtractionData
    (f : ℂ → ℂ) (σL σR T : ℝ) where
  regularized : ℂ → ℂ
  thirdCoefficient : ℂ
  secondCoefficient : ℂ
  residueAtZero : ℂ
  residueAtOne : ℂ
  decomposition : ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
    f s = regularized s +
      thirdCoefficient * (s⁻¹) ^ 3 +
      secondCoefficient * (s⁻¹) ^ 2 +
      residueAtZero * s⁻¹ + residueAtOne * (s - 1)⁻¹
  regularized_differentiableOn : DifferentiableOn ℂ regularized
    ([[(σL : ℂ).re, (σR : ℂ).re]] ×ℂ [[-T, T]])
  boundary_split :
    rectangularBoundaryIntegral f
        (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) =
      rectangularBoundaryIntegral regularized
          (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) +
        thirdCoefficient * rectangularBoundaryIntegral
          (fun s : ℂ => (s⁻¹) ^ 3)
          (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) +
        secondCoefficient * rectangularBoundaryIntegral
          (fun s : ℂ => (s⁻¹) ^ 2)
          (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) +
        residueAtZero * rectangularBoundaryIntegral
          (fun s : ℂ => s⁻¹)
          (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) +
        residueAtOne * rectangularBoundaryIntegral
          (fun s : ℂ => (s - 1)⁻¹)
          (symmetricLowerCorner σL T) (symmetricUpperCorner σR T)

/-- Exact conservation law: cubic and quadratic subtractions contribute
nothing to a closed rectangle; only the two simple residues survive. -/
theorem TriplePlusSimpleRectangleSubtractionData.boundary_eq
    {f : ℂ → ℂ} {σL σR T : ℝ}
    (H : TriplePlusSimpleRectangleSubtractionData f σL σR T)
    (hL : σL < 0) (hR : 1 < σR) (hT : 0 < T) :
    rectangularBoundaryIntegral f
      (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) =
        2 * Real.pi * I * (H.residueAtZero + H.residueAtOne) := by
  have hreg : rectangularBoundaryIntegral H.regularized
      (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) = 0 := by
    apply rectangularBoundaryIntegral_eq_zero
    simpa [symmetricLowerCorner, symmetricUpperCorner] using
      H.regularized_differentiableOn
  have h3 : rectangularBoundaryIntegral (fun s : ℂ => (s⁻¹) ^ 3)
      (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) = 0 := by
    simpa using rectangularBoundaryIntegral_triplePole 0 σL σR T hL
      (lt_trans zero_lt_one hR) hT
  have h2 : rectangularBoundaryIntegral (fun s : ℂ => (s⁻¹) ^ 2)
      (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) = 0 := by
    simpa using rectangularBoundaryIntegral_doublePole 0 σL σR T hL
      (lt_trans zero_lt_one hR) hT
  have h0 : rectangularBoundaryIntegral (fun s : ℂ => s⁻¹)
      (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) =
        2 * Real.pi * I := by
    simpa using rectangularBoundaryIntegral_simplePole 0 σL σR T hL
      (lt_trans zero_lt_one hR) hT
  have h1 : rectangularBoundaryIntegral (fun s : ℂ => (s - 1)⁻¹)
      (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) =
        2 * Real.pi * I := by
    exact rectangularBoundaryIntegral_simplePole 1 σL σR T
      (lt_trans hL zero_lt_one) hR hT
  rw [H.boundary_split, hreg, h3, h2, h0, h1]
  ring

/-! ## Actual finite pole subtraction at `s = 0` -/

noncomputable def bblsPoleSubtractedFiniteAggregate
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (hdamping : 0 < damping)
    (weight : ι → ℂ) (row : ι → BBLSReducedRational) : ℂ → ℂ :=
  bblsFiniteLocalRemainder damping hdamping weight row

theorem analyticAt_bblsPoleSubtractedFiniteAggregate
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (hdamping : 0 < damping)
    (weight : ι → ℂ) (row : ι → BBLSReducedRational) :
    AnalyticAt ℂ
      (bblsPoleSubtractedFiniteAggregate damping hdamping weight row) 0 :=
  analyticAt_bblsFiniteLocalRemainder damping hdamping weight row

theorem bblsFiniteActiveAggregate_sub_three_poles
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (hdamping : 0 < damping)
    (weight : ι → ℂ) (row : ι → BBLSReducedRational)
    {s : ℂ} (hs : s ≠ 0) :
    bblsFiniteActiveAggregate damping weight row s -
        (bblsFiniteThirdOrderAggregate weight row / s ^ 3 +
          bblsFiniteSecondOrderAggregate damping weight row / s ^ 2 +
          bblsFiniteFirstOrderAggregate damping hdamping weight row / s) =
      bblsPoleSubtractedFiniteAggregate damping hdamping weight row s := by
  rw [bblsFiniteActiveAggregate_eq_collectedLaurent
    damping hdamping weight row hs]
  unfold bblsPoleSubtractedFiniteAggregate
  ring

/-! ## The additional `s = 1` residue and a joint Abel schedule -/

noncomputable def bblsFiniteAdditionalResidueAmplitude
    {ι : Type*} [Fintype ι]
    (weight : ι → ℂ) (row : ι → BBLSReducedRational) : ℂ :=
  ∑ i, weight i * bblsEstermannHurwitzContinuation
    (row i).numerator (row i).denominator 0

noncomputable def bblsFiniteAdditionalResidue
    {ι : Type*} [Fintype ι]
  (damping : ℝ) (weight : ι → ℂ)
    (row : ι → BBLSReducedRational) : ℂ :=
  (damping : ℂ) * bblsFiniteAdditionalResidueAmplitude weight row

/-- The residue of the complete finite signed active aggregate at `s=1` is
the signed aggregate of the row residues. -/
theorem tendsto_bblsFiniteActiveAggregate_residue_one
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (hdamping : 0 < damping)
    (weight : ι → ℂ) (row : ι → BBLSReducedRational) :
    Tendsto (fun s : ℂ =>
      (s - 1) * bblsFiniteActiveAggregate damping weight row s)
      (nhdsWithin (1 : ℂ) {1}ᶜ)
      (nhds (bblsFiniteAdditionalResidue damping weight row)) := by
  have hi (i : ι) : Tendsto
      (fun s : ℂ => weight i *
        ((s - 1) * bblsActiveReflectedExpression damping
          (row i).numerator (row i).denominator s))
      (nhdsWithin (1 : ℂ) {1}ᶜ)
      (nhds (weight i * ((damping : ℂ) *
        bblsEstermannHurwitzContinuation
          (row i).numerator (row i).denominator 0))) :=
    tendsto_const_nhds.mul
      (tendsto_bblsActiveReflectedExpression_residue_one
        damping hdamping (row i).numerator (row i).denominator)
  have hsum := tendsto_finsetSum (Finset.univ : Finset ι)
    (fun i _ => hi i)
  convert hsum using 1
  · funext s
    unfold bblsFiniteActiveAggregate
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · unfold bblsFiniteAdditionalResidue
      bblsFiniteAdditionalResidueAmplitude
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem tendsto_bblsFiniteAdditionalResidue_zero
    {ι : Type*} [Fintype ι]
    (weight : ι → ℂ) (row : ι → BBLSReducedRational) :
    Tendsto (fun damping : ℝ =>
      bblsFiniteAdditionalResidue damping weight row)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
  have hcont : ContinuousAt (fun damping : ℝ =>
      bblsFiniteAdditionalResidue damping weight row) 0 := by
    unfold bblsFiniteAdditionalResidue
    fun_prop
  convert hcont.tendsto.mono_left inf_le_left using 1 <;>
    simp [bblsFiniteAdditionalResidue]

/-- An adaptive positive Abel parameter. It gives an unconditional joint
path in `(N,delta)` without claiming a uniform-in-`N` Estermann bound. -/
noncomputable def bblsAdaptiveResidueDamping (n : ℕ) (amplitude : ℂ) : ℝ :=
  1 / (((n + 1 : ℕ) : ℝ) * (1 + ‖amplitude‖))

theorem bblsAdaptiveResidueDamping_pos (n : ℕ) (amplitude : ℂ) :
    0 < bblsAdaptiveResidueDamping n amplitude := by
  unfold bblsAdaptiveResidueDamping
  positivity

theorem bblsAdaptiveResidueDamping_le (n : ℕ) (amplitude : ℂ) :
    bblsAdaptiveResidueDamping n amplitude ≤ 1 / ((n + 1 : ℕ) : ℝ) := by
  unfold bblsAdaptiveResidueDamping
  have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have ha : 1 ≤ 1 + ‖amplitude‖ :=
    le_add_of_nonneg_right (norm_nonneg amplitude)
  have hm : ((n + 1 : ℕ) : ℝ) ≤
      ((n + 1 : ℕ) : ℝ) * (1 + ‖amplitude‖) := by
    simpa using mul_le_mul_of_nonneg_left ha hn.le
  exact one_div_le_one_div_of_le hn hm

theorem norm_bblsAdaptiveAdditionalResidue_le
    (n : ℕ) (amplitude : ℂ) :
    ‖((bblsAdaptiveResidueDamping n amplitude : ℝ) : ℂ) * amplitude‖ ≤
      1 / ((n + 1 : ℕ) : ℝ) := by
  rw [norm_mul, Complex.norm_real]
  rw [Real.norm_eq_abs, abs_of_pos
    (bblsAdaptiveResidueDamping_pos n amplitude)]
  have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  calc
    bblsAdaptiveResidueDamping n amplitude * ‖amplitude‖ ≤
        bblsAdaptiveResidueDamping n amplitude * (1 + ‖amplitude‖) := by
      apply mul_le_mul_of_nonneg_left
      · linarith [norm_nonneg amplitude]
      · exact (bblsAdaptiveResidueDamping_pos n amplitude).le
    _ = 1 / ((n + 1 : ℕ) : ℝ) := by
      unfold bblsAdaptiveResidueDamping
      have ha : 0 < 1 + ‖amplitude‖ := by positivity
      field_simp [hn.ne', ha.ne']

theorem tendsto_bblsAdaptiveResidueDamping_zero
    (amplitude : ℕ → ℂ) :
    Tendsto (fun n => bblsAdaptiveResidueDamping n (amplitude n))
      atTop (nhds 0) := by
  have hmajor : Tendsto (fun n : ℕ =>
      (1 : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (nhds 0) :=
    by simpa [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0))
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n =>
      (bblsAdaptiveResidueDamping_pos n (amplitude n)).le
  · exact Filter.Eventually.of_forall fun n =>
      bblsAdaptiveResidueDamping_le n (amplitude n)
  · exact hmajor

theorem tendsto_bblsAdaptiveAdditionalResidue_zero
    (amplitude : ℕ → ℂ) :
    Tendsto (fun n =>
      ((bblsAdaptiveResidueDamping n (amplitude n) : ℝ) : ℂ) * amplitude n)
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hmajor : Tendsto (fun n : ℕ =>
      (1 : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (nhds 0) :=
    by simpa [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0))
  rw [Metric.tendsto_atTop] at hmajor
  obtain ⟨N, hN⟩ := hmajor ε hε
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_zero_right]
  have htail := hN n hn
  have hnonneg : 0 ≤ (1 : ℝ) / ((n + 1 : ℕ) : ℝ) := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at htail
  exact lt_of_le_of_lt
    (norm_bblsAdaptiveAdditionalResidue_le n (amplitude n)) htail

noncomputable def h15AdditionalResidueAmplitude (n : ℕ) : ℂ :=
  bblsFiniteAdditionalResidueAmplitude
    (h15LaurentRowWeight (N := NB8.logTaperLength n))
    (h15LaurentRow (N := NB8.logTaperLength n))

/-- Along an explicit adaptive Abel schedule, the complete finite H15
`s=1` residue vanishes. This is a joint limit, not a uniform-in-`N` bound. -/
theorem tendsto_h15AdditionalResidue_adaptive_zero :
    Tendsto (fun n =>
      ((bblsAdaptiveResidueDamping n (h15AdditionalResidueAmplitude n) : ℝ) : ℂ) *
        h15AdditionalResidueAmplitude n)
      atTop (nhds 0) :=
  tendsto_bblsAdaptiveAdditionalResidue_zero h15AdditionalResidueAmplitude

/-! ## Full correction ledger -/

/-- The complete separately conserved ledger. The elementary/endpoint term
is deliberately a parameter until the H15 numerator completion identifies
the active Estermann interior with the full quadratic expression. -/
noncomputable def bblsFullCorrectionLedger
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (hdamping : 0 < damping)
    (retainedCorrection elementaryEndpoint : ℂ)
    (weight : ι → ℂ) (row : ι → BBLSReducedRational) : ℂ :=
  retainedCorrection +
    bblsFiniteFirstOrderAggregate damping hdamping weight row +
    bblsFiniteAdditionalResidue damping weight row + elementaryEndpoint

/-- Exact four-sector decomposition of the ledger: the correction--finite
part gap, the zero-pole Taylor coupling, the one-pole Abel residue, and the
elementary/endpoint completion. -/
theorem bblsFullCorrectionLedger_eq_four_sectors
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (hdamping : 0 < damping)
    (retainedCorrection elementaryEndpoint : ℂ)
    (weight : ι → ℂ) (row : ι → BBLSReducedRational) :
    bblsFullCorrectionLedger damping hdamping retainedCorrection
        elementaryEndpoint weight row =
      bblsCorrectionFinitePartGap damping hdamping retainedCorrection weight row +
        bblsFirstOrderPolarResidual damping weight row +
        bblsFiniteAdditionalResidue damping weight row + elementaryEndpoint := by
  unfold bblsFullCorrectionLedger
  rw [← bblsGlobalCorrectionGap_eq_exact_add_polarResidual
    damping hdamping retainedCorrection weight row]
  rfl

/-- A normalized rectangle decomposition with the correction kept outside
the pole-subtracted interior.  This is the exact interface consumed by the
Bettin--Chandee exponent test. -/
structure BBLSCorrectionPreservingRectangleData
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (hdamping : 0 < damping)
    (retainedCorrection : ℂ)
    (weight : ι → ℂ) (row : ι → BBLSReducedRational) where
  normalizedRectangleValue : ℂ
  poleSubtractedInterior : ℂ
  elementaryEndpoint : ℂ
  decomposition :
    normalizedRectangleValue =
      bblsFullCorrectionLedger damping hdamping retainedCorrection
        elementaryEndpoint weight row + poleSubtractedInterior

/-- The rectangle value can equivalently be read as four explicit ledger
sectors plus the analytic interior. This proves that pole subtraction does
not discard the retained correction. -/
theorem BBLSCorrectionPreservingRectangleData.decomposition_expanded
    {ι : Type*} [Fintype ι]
    {damping : ℝ} {hdamping : 0 < damping}
    {retainedCorrection : ℂ}
    {weight : ι → ℂ} {row : ι → BBLSReducedRational}
    (H : BBLSCorrectionPreservingRectangleData damping hdamping
      retainedCorrection weight row) :
    H.normalizedRectangleValue =
      bblsCorrectionFinitePartGap damping hdamping retainedCorrection weight row +
        bblsFirstOrderPolarResidual damping weight row +
        bblsFiniteAdditionalResidue damping weight row +
        H.elementaryEndpoint + H.poleSubtractedInterior := by
  rw [H.decomposition,
    bblsFullCorrectionLedger_eq_four_sectors]

end NBMellinTools.NB12
