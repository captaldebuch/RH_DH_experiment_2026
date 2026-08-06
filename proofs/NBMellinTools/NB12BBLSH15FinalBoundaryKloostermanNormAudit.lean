/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FinalBoundaryIntervalCompletionNormBound

/-!
# NB12zzt: Kloosterman mean-square stop test for literal H15 completion

The Kloosterman kernel has an exact frequency mean square.  Together with
inverse-coordinate Parseval, ordinary Cauchy--Schwarz therefore returns the
same modulus scale as the direct endpoint bound.  This module records the
finite identities without asserting Weil or cross-modulus cancellation.
-/

open AddChar Complex ZMod
open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate

namespace NBMellinTools.NB12

/-- The Kloosterman sum is an inverse-coordinate Fourier coefficient of a
unit-modulus additive seed, evaluated at the negated frequency. -/
theorem h15KloostermanSum_eq_inverseCoordinateFourierCoefficient_neg
    (q : ℕ) [NeZero q] (n m : ZMod q) :
    h15KloostermanSum n m =
      h15InverseCoordinateFourierCoefficient
        (fun x : (ZMod q)ˣ => ZMod.stdAddChar (n * (x : ZMod q))) (-m) := by
  classical
  unfold h15KloostermanSum h15InverseCoordinateFourierCoefficient
  calc
    (∑ x : (ZMod q)ˣ,
        ZMod.stdAddChar
          (n * (x : ZMod q) +
            m * ((x⁻¹ : (ZMod q)ˣ) : ZMod q))) =
      ∑ y : (ZMod q)ˣ,
        ZMod.stdAddChar
          (n * ((y⁻¹ : (ZMod q)ˣ) : ZMod q) + m * (y : ZMod q)) := by
        exact (Equiv.sum_comp (Equiv.inv ((ZMod q)ˣ))
          (fun x : (ZMod q)ˣ =>
            ZMod.stdAddChar
              (n * (x : ZMod q) +
                m * ((x⁻¹ : (ZMod q)ˣ) : ZMod q)))).symm
    _ = ∑ y : (ZMod q)ˣ,
        ZMod.stdAddChar (n * ((y⁻¹ : (ZMod q)ˣ) : ZMod q)) *
          ZMod.stdAddChar (-((-m) * (y : ZMod q))) := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [← AddChar.map_add_eq_mul]
      apply congrArg ZMod.stdAddChar
      ring

/-- Exact frequency mean square of one Kloosterman row. -/
theorem sum_normSq_h15KloostermanSum
    (q : ℕ) [NeZero q] (n : ZMod q) :
    ∑ m : ZMod q, Complex.normSq (h15KloostermanSum n m) =
      (q : ℝ) * Fintype.card ((ZMod q)ˣ) := by
  rw [show (∑ m : ZMod q, Complex.normSq (h15KloostermanSum n m)) =
      ∑ k : ZMod q, Complex.normSq (h15KloostermanSum n (-k)) by
    exact (Equiv.sum_comp (Equiv.neg (ZMod q))
      (fun m : ZMod q => Complex.normSq (h15KloostermanSum n m))).symm]
  simp_rw [h15KloostermanSum_eq_inverseCoordinateFourierCoefficient_neg]
  simp only [neg_neg]
  rw [sum_normSq_h15InverseCoordinateFourierCoefficient]
  congr 1
  calc
    (∑ x : (ZMod q)ˣ,
        Complex.normSq (ZMod.stdAddChar (n * (x : ZMod q)))) =
      ∑ _x : (ZMod q)ˣ, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro x _hx
        rw [ZMod.stdAddChar_apply]
        exact Circle.normSq_coe _
    _ = Fintype.card ((ZMod q)ˣ) := by simp

/-- Nonzero-frequency Kloosterman energy. -/
noncomputable def h15KloostermanNonzeroEnergy
    {q : ℕ} [NeZero q] (n : ZMod q) : ℝ :=
  ∑ m ∈ Finset.univ.erase (0 : ZMod q),
    Complex.normSq (h15KloostermanSum n m)

theorem h15KloostermanNonzeroEnergy_le
    (q : ℕ) [NeZero q] (n : ZMod q) :
    h15KloostermanNonzeroEnergy n ≤
      (q : ℝ) * Fintype.card ((ZMod q)ˣ) := by
  unfold h15KloostermanNonzeroEnergy
  calc
    (∑ m ∈ Finset.univ.erase (0 : ZMod q),
        Complex.normSq (h15KloostermanSum n m)) ≤
      ∑ m : ZMod q, Complex.normSq (h15KloostermanSum n m) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.erase_subset _ _
        · intro _m _hm _hnot
          exact Complex.normSq_nonneg _
    _ = _ := sum_normSq_h15KloostermanSum q n

theorem card_units_zmod_le (q : ℕ) [NeZero q] :
    Fintype.card ((ZMod q)ˣ) ≤ q := by
  have h := Fintype.card_le_of_injective
    (fun x : (ZMod q)ˣ => (x : ZMod q)) Units.val_injective
  simpa using h

/-- The elementary modulus-only form of the Kloosterman energy bound. -/
theorem h15KloostermanNonzeroEnergy_le_sq
    (q : ℕ) [NeZero q] (n : ZMod q) :
    h15KloostermanNonzeroEnergy n ≤ (q : ℝ) ^ 2 := by
  calc
    h15KloostermanNonzeroEnergy n ≤
        (q : ℝ) * Fintype.card ((ZMod q)ˣ) :=
      h15KloostermanNonzeroEnergy_le q n
    _ ≤ (q : ℝ) * q := by
      gcongr
      exact_mod_cast card_units_zmod_le q
    _ = (q : ℝ) ^ 2 := by ring

/-- Finite complex Cauchy--Schwarz in squared-norm form. -/
theorem normSq_sum_mul_le_sum_normSq_mul_sum_normSq
    {ι : Type*} (s : Finset ι) (A B : ι → ℂ) :
    Complex.normSq (∑ i ∈ s, A i * B i) ≤
      (∑ i ∈ s, Complex.normSq (A i)) *
        ∑ i ∈ s, Complex.normSq (B i) := by
  rw [Complex.normSq_eq_norm_sq]
  calc
    ‖∑ i ∈ s, A i * B i‖ ^ 2 ≤
        (∑ i ∈ s, ‖A i * B i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ = (∑ i ∈ s, ‖A i‖ * ‖B i‖) ^ 2 := by
      simp_rw [norm_mul]
    _ ≤ (∑ i ∈ s, ‖A i‖ ^ 2) * ∑ i ∈ s, ‖B i‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖A i‖) (fun i => ‖B i‖)
    _ = (∑ i ∈ s, Complex.normSq (A i)) *
        ∑ i ∈ s, Complex.normSq (B i) := by
      simp_rw [Complex.normSq_eq_norm_sq]

/-- The nonzero numerator in one completed H15 interval row. -/
noncomputable def h15IntervalNonzeroKloostermanNumerator
    (orientation : H15IntervalCompletionOrientation)
    (N g r U L' q q' d' u K j : ℕ) [NeZero q'] : ℂ :=
  ∑ m ∈ Finset.univ.erase (0 : ZMod q'),
    h15InverseCoordinateFourierCoefficient
        (h15IntervalEndpointUnitWeight orientation
          N g r U L' q q' d' u K j) m *
      h15KloostermanSum
        (h15IntervalCompletionFrequency orientation r) m

/-- Plain frequency Cauchy--Schwarz factors the nonzero completed numerator
into the two exact energies.  This is the quantitative baseline against which
any signed Kloosterman improvement must be measured. -/
theorem normSq_h15IntervalNonzeroKloostermanNumerator_le
    (orientation : H15IntervalCompletionOrientation)
    (N g r U L' q q' d' u K j : ℕ) [NeZero q'] :
    Complex.normSq
        (h15IntervalNonzeroKloostermanNumerator orientation
          N g r U L' q q' d' u K j) ≤
      h15InverseCoordinateNonzeroEnergy
          (h15IntervalEndpointUnitWeight orientation
            N g r U L' q q' d' u K j) *
        h15KloostermanNonzeroEnergy
          (q := q') (h15IntervalCompletionFrequency orientation r) := by
  unfold h15IntervalNonzeroKloostermanNumerator
    h15InverseCoordinateNonzeroEnergy h15KloostermanNonzeroEnergy
  exact normSq_sum_mul_le_sum_normSq_mul_sum_normSq
    (Finset.univ.erase (0 : ZMod q'))
    (fun m => h15InverseCoordinateFourierCoefficient
      (h15IntervalEndpointUnitWeight orientation
        N g r U L' q q' d' u K j) m)
    (fun m => h15KloostermanSum
      (h15IntervalCompletionFrequency orientation r) m)

/-- The nonzero coefficient energy is bounded by the total coefficient
energy. -/
theorem h15InverseCoordinateNonzeroEnergy_le_total
    (q : ℕ) [NeZero q] (A : (ZMod q)ˣ → ℂ) :
    h15InverseCoordinateNonzeroEnergy A ≤
      ∑ m : ZMod q,
        Complex.normSq (h15InverseCoordinateFourierCoefficient A m) := by
  unfold h15InverseCoordinateNonzeroEnergy
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.erase_subset _ _
  · intro _m _hm _hnot
    exact Complex.normSq_nonneg _

/-- Plain Parseval/Cauchy--Schwarz bound for the literal nonzero numerator.
It exposes the full `q'^2` Kloosterman frequency cost before the external
completion factor `1/q'` is applied. -/
theorem normSq_h15IntervalNonzeroKloostermanNumerator_le_explicit
    (orientation : H15IntervalCompletionOrientation)
    (N g r U L' q q' d' u K j : ℕ) [NeZero q']
    (hN : 2 ≤ N) (hg : 1 ≤ g) (hU : 0 < U)
    (hL' : 0 < L') (hq' : 0 < q') (hLq' : Nat.Coprime L' q') :
    Complex.normSq
        (h15IntervalNonzeroKloostermanNumerator orientation
          N g r U L' q q' d' u K j) ≤
      ((4 * q' * (q' + 1) : ℝ) * (1 / (U : ℝ)) ^ 4) *
        (q' : ℝ) ^ 2 := by
  calc
    Complex.normSq
        (h15IntervalNonzeroKloostermanNumerator orientation
          N g r U L' q q' d' u K j) ≤
      h15InverseCoordinateNonzeroEnergy
          (h15IntervalEndpointUnitWeight orientation
            N g r U L' q q' d' u K j) *
        h15KloostermanNonzeroEnergy
          (q := q') (h15IntervalCompletionFrequency orientation r) :=
      normSq_h15IntervalNonzeroKloostermanNumerator_le orientation
        N g r U L' q q' d' u K j
    _ ≤ h15IntervalInverseCoordinateCoefficientEnergy orientation
          N g r U L' q q' d' u K j * (q' : ℝ) ^ 2 := by
      apply mul_le_mul
      · exact h15InverseCoordinateNonzeroEnergy_le_total q'
          (h15IntervalEndpointUnitWeight orientation
            N g r U L' q q' d' u K j)
      · exact h15KloostermanNonzeroEnergy_le_sq q'
          (h15IntervalCompletionFrequency orientation r)
      · unfold h15KloostermanNonzeroEnergy
        exact Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)
      · unfold h15IntervalInverseCoordinateCoefficientEnergy
        exact Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)
    _ ≤ ((4 * q' * (q' + 1) : ℝ) * (1 / (U : ℝ)) ^ 4) *
          (q' : ℝ) ^ 2 := by
      gcongr
      exact h15IntervalInverseCoordinateCoefficientEnergy_le_explicit
        orientation N g r U L' q q' d' u K j
          hN hg hU hL' hq' hLq'

/-- After the exact completion normalization `1/q'`, elementary
Parseval/Cauchy--Schwarz returns precisely the coefficient-energy scale.  In
particular it supplies no additional power of the modulus. -/
theorem normSq_h15ComplexIntervalEndpointNonzeroMode_le_explicit
    (orientation : H15IntervalCompletionOrientation)
    (N g r U L' q q' d' u K j : ℕ) [NeZero q']
    (hN : 2 ≤ N) (hg : 1 ≤ g) (hU : 0 < U)
    (hL' : 0 < L') (hq' : 0 < q') (hLq' : Nat.Coprime L' q') :
    Complex.normSq
        (h15ComplexIntervalEndpointNonzeroMode orientation
          N g r U L' q q' d' u K j) ≤
      (4 * q' * (q' + 1) : ℝ) * (1 / (U : ℝ)) ^ 4 := by
  have hnum :=
    normSq_h15IntervalNonzeroKloostermanNumerator_le_explicit
      orientation N g r U L' q q' d' u K j
        hN hg hU hL' hq' hLq'
  unfold h15IntervalNonzeroKloostermanNumerator at hnum
  unfold h15ComplexIntervalEndpointNonzeroMode
  rw [Complex.normSq_mul, Complex.normSq_inv, Complex.normSq_natCast]
  calc
    ((q' : ℝ) * q')⁻¹ *
        Complex.normSq
          (∑ m ∈ Finset.univ.erase (0 : ZMod q'),
            h15InverseCoordinateFourierCoefficient
                (h15IntervalEndpointUnitWeight orientation
                  N g r U L' q q' d' u K j) m *
              h15KloostermanSum
                (h15IntervalCompletionFrequency orientation r) m) ≤
      ((q' : ℝ) * q')⁻¹ *
        (((4 * q' * (q' + 1) : ℝ) * (1 / (U : ℝ)) ^ 4) *
          (q' : ℝ) ^ 2) := by
        gcongr
    _ = (4 * q' * (q' + 1) : ℝ) * (1 / (U : ℝ)) ^ 4 := by
      have hqR : (q' : ℝ) ≠ 0 := by exact_mod_cast hq'.ne'
      field_simp

end NBMellinTools.NB12
