/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FinalBoundaryIntervalCompletionGate

/-!
# NB12zzr: Parseval ledger for completed H15 interval coefficients

This is the first quantitative audit after literal interval completion.  The
inverse-coordinate Fourier coefficients satisfy exact finite Parseval on the
unit-supported input.  Removing the zero mode therefore leaves total unit
energy minus the squared signed endpoint mass.

No Kloosterman bound is used here.
-/

open AddChar Complex ZMod
open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate

namespace NBMellinTools.NB12

/-! ## Generic inverse-coordinate Parseval -/

theorem sum_h15InverseCoordinateCharacterPair
    (q : ℕ) [NeZero q] (y z : (ZMod q)ˣ) :
    (∑ m : ZMod q,
        conj (ZMod.stdAddChar (-(m * (y : ZMod q)))) *
          ZMod.stdAddChar (-(m * (z : ZMod q)))) =
      if z = y then (q : ℂ) else 0 := by
  simpa only [mul_neg, neg_inj, Units.val_inj] using
    (sum_h15OrdinaryCharacterPair q
      (-(y : ZMod q)) (-(z : ZMod q)))

/-- Exact Parseval identity for the inverse-coordinate coefficients. -/
theorem sum_normSq_h15InverseCoordinateFourierCoefficient
    (q : ℕ) [NeZero q] (A : (ZMod q)ˣ → ℂ) :
    ∑ m : ZMod q,
        Complex.normSq (h15InverseCoordinateFourierCoefficient A m) =
      (q : ℝ) * ∑ x : (ZMod q)ˣ, Complex.normSq (A x) := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [Complex.normSq_eq_conj_mul_self]
  unfold h15InverseCoordinateFourierCoefficient
  calc
    (∑ m : ZMod q,
        conj (∑ y : (ZMod q)ˣ,
            A (y⁻¹) * ZMod.stdAddChar (-(m * (y : ZMod q)))) *
          (∑ z : (ZMod q)ˣ,
            A (z⁻¹) * ZMod.stdAddChar (-(m * (z : ZMod q))))) =
      ∑ m : ZMod q, ∑ y : (ZMod q)ˣ, ∑ z : (ZMod q)ˣ,
        (conj (A (y⁻¹)) * A (z⁻¹)) *
          (conj (ZMod.stdAddChar (-(m * (y : ZMod q)))) *
            ZMod.stdAddChar (-(m * (z : ZMod q)))) := by
      apply Fintype.sum_congr
      intro m
      simp_rw [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
      apply Fintype.sum_congr
      intro y
      apply Fintype.sum_congr
      intro z
      ring
    _ = ∑ y : (ZMod q)ˣ, ∑ z : (ZMod q)ˣ,
        (conj (A (y⁻¹)) * A (z⁻¹)) *
          (∑ m : ZMod q,
            conj (ZMod.stdAddChar (-(m * (y : ZMod q)))) *
              ZMod.stdAddChar (-(m * (z : ZMod q)))) := by
      rw [Finset.sum_comm]
      apply Fintype.sum_congr
      intro y
      rw [Finset.sum_comm]
      apply Fintype.sum_congr
      intro z
      rw [Finset.mul_sum]
    _ = ∑ y : (ZMod q)ˣ, ∑ z : (ZMod q)ˣ,
        conj (A (y⁻¹)) * A (z⁻¹) *
          (if z = y then (q : ℂ) else 0) := by
      simp_rw [sum_h15InverseCoordinateCharacterPair]
    _ = (q : ℂ) * ∑ y : (ZMod q)ˣ,
        conj (A (y⁻¹)) * A (y⁻¹) := by
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte]
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro y
      ring
    _ = (q : ℂ) * ∑ x : (ZMod q)ˣ, conj (A x) * A x := by
      exact congrArg (fun z : ℂ => (q : ℂ) * z)
        (Equiv.sum_comp (Equiv.inv ((ZMod q)ˣ))
          (fun x => conj (A x) * A x))

/-- Energy in the nonzero inverse-coordinate frequencies. -/
noncomputable def h15InverseCoordinateNonzeroEnergy
    {q : ℕ} [NeZero q] (A : (ZMod q)ˣ → ℂ) : ℝ :=
  ∑ m ∈ (Finset.univ.erase (0 : ZMod q)),
    Complex.normSq (h15InverseCoordinateFourierCoefficient A m)

/-- Exact mean-removal formula.  The only automatic saving in coefficient
energy is the squared signed zero mode; all remaining decay must come from
the H15 weights or the Kloosterman kernel. -/
theorem h15InverseCoordinateNonzeroEnergy_eq_total_sub_zero
    (q : ℕ) [NeZero q] (A : (ZMod q)ˣ → ℂ) :
    h15InverseCoordinateNonzeroEnergy A =
      (q : ℝ) * ∑ x : (ZMod q)ˣ, Complex.normSq (A x) -
        Complex.normSq (∑ x : (ZMod q)ˣ, A x) := by
  classical
  unfold h15InverseCoordinateNonzeroEnergy
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun m : ZMod q =>
      Complex.normSq (h15InverseCoordinateFourierCoefficient A m))
    (by simp : (0 : ZMod q) ∈ Finset.univ)
  have hinv :
      (∑ y : (ZMod q)ˣ, A (y⁻¹)) = ∑ x : (ZMod q)ˣ, A x :=
    Equiv.sum_comp (Equiv.inv ((ZMod q)ˣ)) A
  calc
    (∑ m ∈ Finset.univ.erase (0 : ZMod q),
        Complex.normSq (h15InverseCoordinateFourierCoefficient A m)) =
        (∑ m : ZMod q,
          Complex.normSq (h15InverseCoordinateFourierCoefficient A m)) -
          Complex.normSq (h15InverseCoordinateFourierCoefficient A 0) := by
      linarith
    _ = (q : ℝ) * ∑ x : (ZMod q)ˣ, Complex.normSq (A x) -
          Complex.normSq (∑ x : (ZMod q)ˣ, A x) := by
      rw [sum_normSq_h15InverseCoordinateFourierCoefficient,
        h15InverseCoordinateFourierCoefficient_zero, hinv]

/-! ## Literal H15 interval specialization -/

noncomputable def h15IntervalInverseCoordinateCoefficientEnergy
    (orientation : H15IntervalCompletionOrientation)
    (N g r U L' q q' d' u K j : ℕ) [NeZero q'] : ℝ :=
  ∑ m : ZMod q',
    Complex.normSq
      (h15InverseCoordinateFourierCoefficient
        (h15IntervalEndpointUnitWeight orientation
          N g r U L' q q' d' u K j) m)

noncomputable def h15IntervalEndpointUnitL2Mass
    (orientation : H15IntervalCompletionOrientation)
    (N g r U L' q q' d' u K j : ℕ) [NeZero q'] : ℝ :=
  ∑ x : (ZMod q')ˣ,
    Complex.normSq
      (h15IntervalEndpointUnitWeight orientation
        N g r U L' q q' d' u K j x)

theorem h15IntervalInverseCoordinateCoefficientEnergy_eq
    (orientation : H15IntervalCompletionOrientation)
    (N g r U L' q q' d' u K j : ℕ) [NeZero q'] :
    h15IntervalInverseCoordinateCoefficientEnergy orientation
        N g r U L' q q' d' u K j =
      (q' : ℝ) * h15IntervalEndpointUnitL2Mass orientation
        N g r U L' q q' d' u K j := by
  unfold h15IntervalInverseCoordinateCoefficientEnergy
    h15IntervalEndpointUnitL2Mass
  exact sum_normSq_h15InverseCoordinateFourierCoefficient q'
    (h15IntervalEndpointUnitWeight orientation
      N g r U L' q q' d' u K j)

theorem h15IntervalInverseCoordinateNonzeroEnergy_eq
    (orientation : H15IntervalCompletionOrientation)
    (N g r U L' q q' d' u K j : ℕ) [NeZero q'] :
    h15InverseCoordinateNonzeroEnergy
        (h15IntervalEndpointUnitWeight orientation
          N g r U L' q q' d' u K j) =
      (q' : ℝ) * h15IntervalEndpointUnitL2Mass orientation
          N g r U L' q q' d' u K j -
        Complex.normSq
          (∑ v ∈ h15NormalizedSuperperiodBoundarySupport U L' q',
            if h15IntervalCompletionPredicate orientation
                r u q v q' K j then
              (h15NormalizedProgressionCoupledBoundaryPointWeight
                N g U L' q' d' v : ℂ)
            else 0) := by
  rw [h15InverseCoordinateNonzeroEnergy_eq_total_sub_zero]
  unfold h15IntervalEndpointUnitL2Mass
  rw [sum_h15IntervalEndpointUnitWeight]

end NBMellinTools.NB12
