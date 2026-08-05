/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSHurwitzDecomposition
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Analysis.Analytic.Order

/-!
# NB12j: Laurent coefficients of the rational BBLS Estermann continuation

This file removes the double pole at `s=1` from the finite double-Hurwitz
continuation constructed in `NB12BBLSHurwitzDecomposition`.  It proves the
first-order Laurent quotient and evaluates the simple-pole coefficient of a
reduced rational twist as

`2 * (EulerGamma - log q) / q`.

These are local meromorphic identities.  No contour shift, Abel-boundary
passage, correction matching, or signed H15 decay is claimed.
-/

open scoped BigOperators Topology LSeries.notation
open Complex Filter LSeries HurwitzZeta Topology ZMod

namespace NBMellinTools.NB12

/-! ## A pole-removed Hurwitz factor -/

/-- The holomorphic part of one Hurwitz factor at `s=1`, in Mathlib's
Gamma-normalized convention. -/
noncomputable def bblsHurwitzRegularPart
    (x : UnitAddCircle) (s : ℂ) : ℂ :=
  HurwitzZeta.hurwitzZeta x s -
    1 / (s - 1) / Complex.Gammaℝ s

/-- A globally defined replacement for `(s-1) * zeta(s,x)` at its pole. -/
noncomputable def bblsHurwitzPoleRemovedFactor
    (x : UnitAddCircle) (s : ℂ) : ℂ :=
  (Complex.Gammaℝ s)⁻¹ + (s - 1) * bblsHurwitzRegularPart x s

/-- The pole-removed Hurwitz factor is differentiable at `s=1`. -/
theorem differentiableAt_bblsHurwitzPoleRemovedFactor
    (x : UnitAddCircle) :
    DifferentiableAt ℂ (bblsHurwitzPoleRemovedFactor x) 1 := by
  unfold bblsHurwitzPoleRemovedFactor bblsHurwitzRegularPart
  exact Complex.differentiable_Gammaℝ_inv.differentiableAt.add
    ((differentiableAt_id.sub_const 1).mul
      (HurwitzZeta.differentiableAt_hurwitzZeta_sub_one_div x))

/-- Away from `s=1`, the pole-removed factor is exactly `(s-1)zeta(s,x)`. -/
theorem bblsHurwitzPoleRemovedFactor_eq_mul_hurwitzZeta
    (x : UnitAddCircle) {s : ℂ} (hs : s ≠ 1) :
    bblsHurwitzPoleRemovedFactor x s =
      (s - 1) * HurwitzZeta.hurwitzZeta x s := by
  unfold bblsHurwitzPoleRemovedFactor bblsHurwitzRegularPart
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hcancel :
      (s - 1) * (1 / (s - 1) / Complex.Gammaℝ s) =
        1 / Complex.Gammaℝ s := by
    calc
      (s - 1) * (1 / (s - 1) / Complex.Gammaℝ s) =
          ((s - 1) * (s - 1)⁻¹) / Complex.Gammaℝ s := by
            simp only [one_div]
            ring
      _ = 1 / Complex.Gammaℝ s := by rw [mul_inv_cancel₀ hs']
  rw [mul_sub, hcancel]
  ring

/-- Every pole-removed Hurwitz factor has value one at `s=1`. -/
theorem bblsHurwitzPoleRemovedFactor_one (x : UnitAddCircle) :
    bblsHurwitzPoleRemovedFactor x 1 = 1 := by
  simp [bblsHurwitzPoleRemovedFactor, Complex.Gammaℝ_one]

/-! ## The holomorphic Estermann numerator -/

/-- A holomorphic numerator for the possible double pole.  Away from one it
is exactly `(s-1)^2 D(s,a/q)`. -/
noncomputable def bblsEstermannPoleRemovedNumerator
    (a q : ℕ) [NeZero q] (s : ℂ) : ℂ :=
  (q : ℂ) ^ (-s) *
    ∑ j : ZMod q,
      ((q : ℂ) ^ (-s) *
          ∑ k : ZMod q,
            bblsEstermannResiduePhase a j k *
              bblsHurwitzPoleRemovedFactor (ZMod.toAddCircle k) s) *
        bblsHurwitzPoleRemovedFactor (ZMod.toAddCircle j) s

/-- The pole-removed Estermann numerator is differentiable at one. -/
theorem differentiableAt_bblsEstermannPoleRemovedNumerator
    (a q : ℕ) [NeZero q] :
    DifferentiableAt ℂ (bblsEstermannPoleRemovedNumerator a q) 1 := by
  unfold bblsEstermannPoleRemovedNumerator
  have hq : DifferentiableAt ℂ (fun s : ℂ => (q : ℂ) ^ (-s)) 1 := by
    fun_prop
  apply hq.mul
  apply DifferentiableAt.fun_sum
  intro j _
  apply DifferentiableAt.mul
  · apply hq.mul
    apply DifferentiableAt.fun_sum
    intro k _
    exact (differentiableAt_bblsHurwitzPoleRemovedFactor
      (ZMod.toAddCircle k)).const_mul _
  · exact differentiableAt_bblsHurwitzPoleRemovedFactor
      (ZMod.toAddCircle j)

/-- The numerator value at one is the leading double-pole coefficient. -/
theorem bblsEstermannPoleRemovedNumerator_one
    (a q : ℕ) [NeZero q] :
    bblsEstermannPoleRemovedNumerator a q 1 =
      bblsEstermannDoublePoleCoefficient a q := by
  unfold bblsEstermannPoleRemovedNumerator
    bblsEstermannDoublePoleCoefficient
  simp [bblsHurwitzPoleRemovedFactor, Complex.Gammaℝ_one]

/-- Exact agreement of the holomorphic numerator with the original
continuation away from its pole. -/
theorem bblsEstermannPoleRemovedNumerator_eq
    (a q : ℕ) [NeZero q] {s : ℂ} (hs : s ≠ 1) :
    bblsEstermannPoleRemovedNumerator a q s =
      (s - 1) ^ 2 * bblsEstermannHurwitzContinuation a q s := by
  unfold bblsEstermannPoleRemovedNumerator
    bblsEstermannHurwitzContinuation ZMod.LFunction
  simp_rw [bblsHurwitzPoleRemovedFactor_eq_mul_hurwitzZeta _ hs]
  simp only [Finset.mul_sum, Finset.sum_mul]
  ring_nf

/-- The simple Laurent coefficient is the derivative of the pole-removed
numerator at one. -/
noncomputable def bblsEstermannSimplePoleCoefficient
    (a q : ℕ) [NeZero q] : ℂ :=
  deriv (bblsEstermannPoleRemovedNumerator a q) 1

/-- The first-order Laurent quotient tends to the simple-pole coefficient. -/
theorem bblsEstermannHurwitzContinuation_simplePole_limit
    (a q : ℕ) [NeZero q] :
    Tendsto
      (fun s : ℂ =>
        ((s - 1) ^ 2 * bblsEstermannHurwitzContinuation a q s -
            bblsEstermannDoublePoleCoefficient a q) / (s - 1))
      (nhdsWithin (1 : ℂ) ({1}ᶜ : Set ℂ))
      (nhds (bblsEstermannSimplePoleCoefficient a q)) := by
  have hderiv :=
    (differentiableAt_bblsEstermannPoleRemovedNumerator a q).hasDerivAt
  rw [hasDerivAt_iff_tendsto_slope] at hderiv
  apply hderiv.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : s ≠ 1 := by simpa using hs
  rw [slope_def_field]
  rw [bblsEstermannPoleRemovedNumerator_eq a q hs1,
    bblsEstermannPoleRemovedNumerator_one]

/-! ## Evaluation for a reduced rational twist -/

/-- At the zero residue, the derivative of the pole-removed Hurwitz factor
is Euler's constant. -/
theorem hasDerivAt_bblsHurwitzPoleRemovedFactor_zero :
    HasDerivAt (bblsHurwitzPoleRemovedFactor (0 : UnitAddCircle))
      (Real.eulerMascheroniConstant : ℂ) 1 := by
  have hgammaInv : HasDerivAt (fun s : ℂ => (Complex.Gammaℝ s)⁻¹)
      (((Real.eulerMascheroniConstant : ℂ) +
        Complex.log (4 * Real.pi)) / 2) 1 := by
    have h := Complex.hasDerivAt_Gammaℝ_one.inv
      (by rw [Complex.Gammaℝ_one]; norm_num)
    convert h using 1
    rw [Complex.Gammaℝ_one]
    ring
  have hregular : DifferentiableAt ℂ
      (bblsHurwitzRegularPart (0 : UnitAddCircle)) 1 :=
    HurwitzZeta.differentiableAt_hurwitzZeta_sub_one_div 0
  have hlinear := ((hasDerivAt_id (x := (1 : ℂ))).sub_const 1).mul
    hregular.hasDerivAt
  have hsum := hgammaInv.add hlinear
  convert hsum using 1
  simp only [bblsHurwitzRegularPart, sub_self, zero_mul, div_zero,
    one_mul, id_eq]
  rw [HurwitzZeta.hurwitzZeta_zero, riemannZeta_one]
  ring

/-- Orthogonality in the inner residue variable. -/
theorem sum_bblsEstermannResiduePhase_inner
    (a q : ℕ) [NeZero q] (j : ZMod q) :
    ∑ k : ZMod q, bblsEstermannResiduePhase a j k =
      if (a : ZMod q) * j = 0 then (q : ℂ) else 0 := by
  simpa [bblsEstermannResiduePhase, mul_assoc, mul_comm, mul_left_comm]
    using AddChar.sum_mulShift ((a : ZMod q) * j)
      (ZMod.isPrimitive_stdAddChar q)

/-- Orthogonality in the outer residue variable. -/
theorem sum_bblsEstermannResiduePhase_outer
    (a q : ℕ) [NeZero q] (k : ZMod q) :
    ∑ j : ZMod q, bblsEstermannResiduePhase a j k =
      if (a : ZMod q) * k = 0 then (q : ℂ) else 0 := by
  rw [← sum_bblsEstermannResiduePhase_inner a q k]
  apply Finset.sum_congr rfl
  intro j _
  unfold bblsEstermannResiduePhase
  apply congrArg ZMod.stdAddChar
  ring

/-- Character orthogonality with an arbitrary weight on the second residue. -/
theorem sum_sum_bblsEstermannResiduePhase_mul_right
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q)
    (f : ZMod q → ℂ) :
    ∑ j : ZMod q, ∑ k : ZMod q,
        bblsEstermannResiduePhase a j k * f k = (q : ℂ) * f 0 := by
  classical
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, sum_bblsEstermannResiduePhase_outer]
  have ha : IsUnit (a : ZMod q) :=
    (ZMod.isUnit_iff_coprime a q).2 haq
  have hz : ∀ k : ZMod q, (a : ZMod q) * k = 0 ↔ k = 0 := by
    intro k
    exact ha.mul_right_eq_zero
  simp only [hz]
  simp

/-- Character orthogonality with an arbitrary weight on the first residue. -/
theorem sum_sum_bblsEstermannResiduePhase_mul_left
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q)
    (f : ZMod q → ℂ) :
    ∑ j : ZMod q,
        (∑ k : ZMod q, bblsEstermannResiduePhase a j k) * f j =
      (q : ℂ) * f 0 := by
  classical
  simp_rw [sum_bblsEstermannResiduePhase_inner]
  have ha : IsUnit (a : ZMod q) :=
    (ZMod.isUnit_iff_coprime a q).2 haq
  have hz : ∀ j : ZMod q, (a : ZMod q) * j = 0 ↔ j = 0 := by
    intro j
    exact ha.mul_right_eq_zero
  simp only [hz]
  simp

/-- Derivative of the modulus factor `q^(-s)` at one. -/
theorem hasDerivAt_bbls_modulus_cpow_neg (q : ℕ) [NeZero q] :
    HasDerivAt (fun s : ℂ => (q : ℂ) ^ (-s))
      (-Complex.log (q : ℂ) * (q : ℂ)⁻¹) 1 := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  have hraw := (hasDerivAt_neg' (1 : ℂ)).const_cpow
    (c := (q : ℂ)) (Or.inl hq)
  convert hraw using 1
  · rw [Complex.cpow_neg_one]
    ring

/-- The classical simple Laurent coefficient of a reduced rational
Estermann twist. -/
theorem bblsEstermannSimplePoleCoefficient_eq
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q) :
    bblsEstermannSimplePoleCoefficient a q =
      2 * ((Real.eulerMascheroniConstant : ℂ) - Complex.log (q : ℂ)) /
        (q : ℂ) := by
  let H : ZMod q → ℂ → ℂ := fun r =>
    bblsHurwitzPoleRemovedFactor (ZMod.toAddCircle r)
  let dH : ZMod q → ℂ := fun r => deriv (H r) 1
  let Q : ℂ → ℂ := fun s => (q : ℂ) ^ (-s)
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  have hQ : HasDerivAt Q
      (-Complex.log (q : ℂ) * (q : ℂ)⁻¹) 1 :=
    hasDerivAt_bbls_modulus_cpow_neg q
  have hH (r : ZMod q) : HasDerivAt (H r) (dH r) 1 := by
    exact (differentiableAt_bblsHurwitzPoleRemovedFactor
      (ZMod.toAddCircle r)).hasDerivAt
  have hH0 : dH 0 = (Real.eulerMascheroniConstant : ℂ) := by
    change deriv
      (bblsHurwitzPoleRemovedFactor (ZMod.toAddCircle (0 : ZMod q))) 1 = _
    rw [map_zero]
    exact HasDerivAt.deriv hasDerivAt_bblsHurwitzPoleRemovedFactor_zero
  have hinner (j : ZMod q) : HasDerivAt
      (fun s : ℂ => Q s * ∑ k : ZMod q,
        bblsEstermannResiduePhase a j k * H k s)
      ((-Complex.log (q : ℂ) * (q : ℂ)⁻¹) *
          (∑ k : ZMod q, bblsEstermannResiduePhase a j k) +
        (q : ℂ)⁻¹ *
          (∑ k : ZMod q, bblsEstermannResiduePhase a j k * dH k)) 1 := by
    have hsum : HasDerivAt
        (fun s : ℂ => ∑ k : ZMod q,
          bblsEstermannResiduePhase a j k * H k s)
        (∑ k : ZMod q, bblsEstermannResiduePhase a j k * dH k) 1 := by
      exact HasDerivAt.fun_sum fun k _ => (hH k).const_mul _
    convert hQ.mul hsum using 1
    · simp only [Q, H, bblsHurwitzPoleRemovedFactor_one, mul_one]
      rw [Complex.cpow_neg_one]
  have hbody (j : ZMod q) : HasDerivAt
      (fun s : ℂ =>
        (Q s * ∑ k : ZMod q,
          bblsEstermannResiduePhase a j k * H k s) * H j s)
      (((-Complex.log (q : ℂ) * (q : ℂ)⁻¹) *
            (∑ k : ZMod q, bblsEstermannResiduePhase a j k) +
          (q : ℂ)⁻¹ *
            (∑ k : ZMod q,
              bblsEstermannResiduePhase a j k * dH k)) +
        ((q : ℂ)⁻¹ *
            (∑ k : ZMod q, bblsEstermannResiduePhase a j k)) * dH j) 1 := by
    convert (hinner j).mul (hH j) using 1
    · simp only [H, bblsHurwitzPoleRemovedFactor_one, mul_one]
      simp [Q, Complex.cpow_neg_one]
  have htotal : HasDerivAt (bblsEstermannPoleRemovedNumerator a q)
      ((-Complex.log (q : ℂ) * (q : ℂ)⁻¹) *
          (∑ j : ZMod q, (q : ℂ)⁻¹ *
            (∑ k : ZMod q, bblsEstermannResiduePhase a j k)) +
        (q : ℂ)⁻¹ *
          (∑ j : ZMod q,
            (((-Complex.log (q : ℂ) * (q : ℂ)⁻¹) *
                (∑ k : ZMod q, bblsEstermannResiduePhase a j k) +
              (q : ℂ)⁻¹ *
                (∑ k : ZMod q,
                  bblsEstermannResiduePhase a j k * dH k)) +
            ((q : ℂ)⁻¹ *
                (∑ k : ZMod q,
                  bblsEstermannResiduePhase a j k)) * dH j))) 1 := by
    have hsum := HasDerivAt.fun_sum fun j (_ : j ∈ Finset.univ) => hbody j
    have hraw := hQ.mul hsum
    change HasDerivAt (fun s : ℂ =>
      Q s * ∑ j : ZMod q,
        (Q s * ∑ k : ZMod q,
          bblsEstermannResiduePhase a j k * H k s) * H j s) _ 1
    convert hraw using 1
    simp only [H, bblsHurwitzPoleRemovedFactor_one, mul_one]
    rw [show Q 1 = (q : ℂ)⁻¹ by simp [Q, Complex.cpow_neg_one]]
  rw [bblsEstermannSimplePoleCoefficient, htotal.deriv]
  have hlead :
      (∑ j : ZMod q, (q : ℂ)⁻¹ *
        (∑ k : ZMod q, bblsEstermannResiduePhase a j k)) =
          (q : ℂ)⁻¹ * (q : ℂ) := by
    rw [← Finset.mul_sum,
      sum_bblsEstermannResiduePhase_of_coprime a q haq]
  have hA :
      (∑ j : ZMod q,
        (-Complex.log (q : ℂ) * (q : ℂ)⁻¹) *
          (∑ k : ZMod q, bblsEstermannResiduePhase a j k)) =
        (-Complex.log (q : ℂ) * (q : ℂ)⁻¹) * (q : ℂ) := by
    rw [← Finset.mul_sum,
      sum_bblsEstermannResiduePhase_of_coprime a q haq]
  have hB :
      (∑ j : ZMod q, (q : ℂ)⁻¹ *
        (∑ k : ZMod q, bblsEstermannResiduePhase a j k * dH k)) =
          (q : ℂ)⁻¹ * ((q : ℂ) * dH 0) := by
    rw [← Finset.mul_sum,
      sum_sum_bblsEstermannResiduePhase_mul_right a q haq dH]
  have hC :
      (∑ j : ZMod q,
        ((q : ℂ)⁻¹ *
          (∑ k : ZMod q, bblsEstermannResiduePhase a j k)) * dH j) =
          (q : ℂ)⁻¹ * ((q : ℂ) * dH 0) := by
    calc
      _ = (q : ℂ)⁻¹ *
          (∑ j : ZMod q,
            (∑ k : ZMod q, bblsEstermannResiduePhase a j k) * dH j) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = _ := by
        rw [sum_sum_bblsEstermannResiduePhase_mul_left a q haq dH]
  have hsumderiv :
      (∑ j : ZMod q,
        (((-Complex.log (q : ℂ) * (q : ℂ)⁻¹) *
              (∑ k : ZMod q, bblsEstermannResiduePhase a j k) +
            (q : ℂ)⁻¹ *
              (∑ k : ZMod q,
                bblsEstermannResiduePhase a j k * dH k)) +
          ((q : ℂ)⁻¹ *
              (∑ k : ZMod q,
                bblsEstermannResiduePhase a j k)) * dH j)) =
        (-Complex.log (q : ℂ) * (q : ℂ)⁻¹) * (q : ℂ) +
          (q : ℂ)⁻¹ * ((q : ℂ) * dH 0) +
          (q : ℂ)⁻¹ * ((q : ℂ) * dH 0) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [hA, hB, hC]
  rw [hlead, hsumderiv, hH0]
  field_simp [hq]
  ring

/-! ## A globally differentiable finite part -/

/-- The pole-removed Hurwitz factor is entire. -/
theorem differentiable_bblsHurwitzPoleRemovedFactor
    (x : UnitAddCircle) :
    Differentiable ℂ (bblsHurwitzPoleRemovedFactor x) := by
  intro s
  by_cases hs : s = 1
  · subst s
    exact differentiableAt_bblsHurwitzPoleRemovedFactor x
  · unfold bblsHurwitzPoleRemovedFactor bblsHurwitzRegularPart
    have hprincipal : DifferentiableAt ℂ
        (fun z : ℂ => 1 / (z - 1) / Complex.Gammaℝ z) s := by
      convert (((differentiableAt_const (c := (1 : ℂ))).div
        (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hs)).mul
          Complex.differentiable_Gammaℝ_inv.differentiableAt) using 1
    exact Complex.differentiable_Gammaℝ_inv.differentiableAt.add
      ((differentiableAt_id.sub_const 1).mul
        ((HurwitzZeta.differentiableAt_hurwitzZeta x hs).sub
          hprincipal))

/-- The finite double-Hurwitz pole-removed numerator is entire. -/
theorem differentiable_bblsEstermannPoleRemovedNumerator
    (a q : ℕ) [NeZero q] :
    Differentiable ℂ (bblsEstermannPoleRemovedNumerator a q) := by
  intro s
  unfold bblsEstermannPoleRemovedNumerator
  have hq : DifferentiableAt ℂ (fun z : ℂ => (q : ℂ) ^ (-z)) s := by
    fun_prop
  apply hq.mul
  apply DifferentiableAt.fun_sum
  intro j _
  apply DifferentiableAt.mul
  · apply hq.mul
    apply DifferentiableAt.fun_sum
    intro k _
    exact (differentiable_bblsHurwitzPoleRemovedFactor
      (ZMod.toAddCircle k) s).const_mul _
  · exact differentiable_bblsHurwitzPoleRemovedFactor
      (ZMod.toAddCircle j) s

/-- An entire complex function admits a globally differentiable second-order
Taylor quotient at zero. -/
theorem exists_differentiable_secondOrderQuotient_bbls
    (N : ℂ → ℂ) (hN : Differentiable ℂ N) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ z : ℂ,
      N z = N 0 + z * deriv N 0 + z ^ 2 * F z := by
  have hAnalyticOn : AnalyticOnNhd ℂ N Set.univ :=
    (Complex.analyticOnNhd_iff_differentiableOn isOpen_univ).2
      hN.differentiableOn
  have hAnalytic : AnalyticAt ℂ N 0 :=
    hAnalyticOn 0 (Set.mem_univ 0)
  rcases hAnalytic.exists_eq_sum_add_pow_mul 2 with ⟨F, hFa, hEq⟩
  have hEq' : ∀ z : ℂ,
      N z = N 0 + z * deriv N 0 + z ^ 2 * F z := by
    intro z
    simpa [Finset.sum_range_succ, iteratedDeriv_zero,
      iteratedDeriv_one, add_assoc] using hEq z
  have hFdiff : Differentiable ℂ F := by
    intro z
    by_cases hz : z = 0
    · subst z
      exact hFa.differentiableAt
    · let Q : ℂ → ℂ := fun w =>
        (N w - N 0 - w * deriv N 0) / w ^ 2
      have hQ : DifferentiableAt ℂ Q z := by
        unfold Q
        exact (((hN z).sub (differentiableAt_const (c := N 0))).sub
          (differentiableAt_id.mul_const (deriv N 0))).div
            (differentiableAt_id.pow 2) (pow_ne_zero 2 hz)
      have hFQ : F =ᶠ[𝓝 z] Q := by
        filter_upwards [eventually_ne_nhds hz] with w hw
        have heq := hEq' w
        unfold Q
        rw [eq_div_iff (pow_ne_zero 2 hw)]
        rw [heq]
        ring
      exact hQ.congr_of_eventuallyEq hFQ
  exact ⟨F, hFdiff, hEq'⟩

/-- An entire complex function admits a globally differentiable second-order
Taylor quotient at one. -/
theorem exists_differentiable_secondOrderQuotientAtOne_bbls
    (N : ℂ → ℂ) (hN : Differentiable ℂ N) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ z : ℂ,
      N z = N 1 + (z - 1) * deriv N 1 + (z - 1) ^ 2 * F z := by
  let M : ℂ → ℂ := fun u => N (1 + u)
  have hM : Differentiable ℂ M := by
    intro u
    unfold M
    fun_prop
  rcases exists_differentiable_secondOrderQuotient_bbls M hM with
    ⟨R, hR, hExpansion⟩
  have hderiv : deriv M 0 = deriv N 1 := by
    have hN' : HasDerivAt N (deriv N 1) ((1 : ℂ) + 0) := by
      simpa using (hN 1).hasDerivAt
    have hcomp := HasDerivAt.comp_const_add (1 : ℂ) 0 hN'
    simpa [M] using hcomp.deriv
  let F : ℂ → ℂ := fun z => R (z - 1)
  have hF : Differentiable ℂ F := by
    intro z
    unfold F
    fun_prop
  refine ⟨F, hF, ?_⟩
  intro z
  have h := hExpansion (z - 1)
  rw [hderiv] at h
  simpa [M, F] using h

/-- A contour-ready Laurent package for a reduced rational Estermann twist.
The finite part is globally differentiable, not merely defined by a
punctured limit. -/
theorem exists_bblsEstermannDifferentiableFinitePart
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      ∀ {s : ℂ}, s ≠ 1 →
        bblsEstermannHurwitzContinuation a q s =
          (q : ℂ)⁻¹ / (s - 1) ^ 2 +
            (2 * ((Real.eulerMascheroniConstant : ℂ) -
                Complex.log (q : ℂ)) / (q : ℂ)) / (s - 1) +
              F s := by
  let N : ℂ → ℂ := bblsEstermannPoleRemovedNumerator a q
  have hN : Differentiable ℂ N :=
    differentiable_bblsEstermannPoleRemovedNumerator a q
  rcases exists_differentiable_secondOrderQuotientAtOne_bbls N hN with
    ⟨F, hF, hExpansion⟩
  refine ⟨F, hF, ?_⟩
  intro s hs
  have hNvalue : N 1 = (q : ℂ)⁻¹ := by
    change bblsEstermannPoleRemovedNumerator a q 1 = _
    rw [bblsEstermannPoleRemovedNumerator_one,
      bblsEstermannDoublePoleCoefficient_of_coprime a q haq]
  have hNderiv : deriv N 1 =
      2 * ((Real.eulerMascheroniConstant : ℂ) -
        Complex.log (q : ℂ)) / (q : ℂ) := by
    change bblsEstermannSimplePoleCoefficient a q = _
    exact bblsEstermannSimplePoleCoefficient_eq a q haq
  have hNeq := hExpansion s
  rw [hNvalue, hNderiv] at hNeq
  have hremoved := bblsEstermannPoleRemovedNumerator_eq a q hs
  change N s = _ at hremoved
  rw [hNeq] at hremoved
  have hsm1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  apply (mul_left_cancel₀ (pow_ne_zero 2 hsm1))
  rw [← hremoved]
  field_simp [hsm1]

end NBMellinTools.NB12
