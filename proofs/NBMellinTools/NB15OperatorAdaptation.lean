/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import Mathlib

/-!
# NB15: Operator adaptation — index type, amplitudes and weights (Phase 1)

This module supplies the concrete finite model on which the Phase 2–4 spectral
analysis is carried out.  (The historical Phase 1 source file was not present in
this repository, so the objects it was supposed to provide are set up here
explicitly; every later statement is a theorem about *these* definitions.)

The model is the standard finite Gram/ledger model:

* indices `ik = (q, k, j)` carry a modulus `q + 1`, and a frequency
  `freq(ik) = (k+1)(j+1)` obtained from a divisor-hyperbola parametrisation
  `r = a·b`;
* the operator amplitude attached to an index is
  `a(ik) = w(ik) · e(-t·log freq(ik))`, a phase of modulus one times the
  ledger-normalised weight
  `w(ik) = ((N+1)(q+1)(k+1)(j+1))⁻¹` (the factor `(N+1)⁻¹` is the ledger
  normalisation, `N = n` being the truncation parameter).

The two facts exported here and used downstream are that `‖a(ik)‖ = w(ik)`
and that the total energy `∑ w(ik)²` is at most `8/(N+1)²`.
-/

open scoped BigOperators
open Complex

namespace NBMellinTools.NB12

/-! ## The additive character -/

/-- The additive character `e(x) = exp(2πi x)`. -/
noncomputable def h15Phase (x : ℝ) : ℂ := Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

@[simp] theorem h15Phase_norm (x : ℝ) : ‖h15Phase x‖ = 1 := by
  simp [h15Phase, Complex.norm_exp]

theorem h15Phase_add (x y : ℝ) : h15Phase (x + y) = h15Phase x * h15Phase y := by
  unfold h15Phase
  rw [← Complex.exp_add]
  push_cast
  ring_nf

/-- On integers the character is trivial. -/
@[simp] theorem h15Phase_intCast (m : ℤ) : h15Phase (m : ℝ) = 1 := by
  unfold h15Phase
  push_cast
  rw [show ((2 : ℂ) * Real.pi * m) * Complex.I = m * (2 * Real.pi * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I m

/-- `e(x)` raised to a natural power. -/
theorem h15Phase_pow (x : ℝ) (b : ℕ) : (h15Phase x) ^ b = h15Phase (b * x) := by
  unfold h15Phase
  rw [← Complex.exp_nat_mul]
  push_cast
  ring_nf

/-- `e(x) = 1` exactly when `x` is an integer. -/
theorem h15Phase_eq_one_iff (x : ℝ) : h15Phase x = 1 ↔ ∃ m : ℤ, x = m := by
  unfold h15Phase
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hk' : ((2 * Real.pi * x : ℝ) : ℂ) = ((k * (2 * Real.pi) : ℝ) : ℂ) := by
      push_cast at hk ⊢
      field_simp at hk ⊢
      linear_combination hk
    have hk'' : (2 * Real.pi * x : ℝ) = (k * (2 * Real.pi) : ℝ) := by exact_mod_cast hk'
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp at hk''
    exact hk''
  · rintro ⟨m, rfl⟩
    exact ⟨m, by push_cast; ring⟩

/-! ## The index type -/

/-- Index set of the truncated operator: a modulus index in `Fin n`, and a
divisor-hyperbola pair `(k, j)` in `Fin K × Fin J`. -/
abbrev H15ResonantOperatorIndex (n K J : ℕ) : Type := Fin n × Fin K × Fin J

variable {n K J : ℕ}

/-- The modulus attached to an index, `q + 1 ≥ 1`. -/
def h15Modulus (ik : H15ResonantOperatorIndex n K J) : ℕ := (ik.1 : ℕ) + 1

/-- The physical frequency attached to an index, `r = (k+1)(j+1)`. -/
def h15Freq (ik : H15ResonantOperatorIndex n K J) : ℕ :=
  ((ik.2.1 : ℕ) + 1) * ((ik.2.2 : ℕ) + 1)

theorem h15Modulus_pos (ik : H15ResonantOperatorIndex n K J) : 0 < h15Modulus ik := by
  simp [h15Modulus]

theorem h15Modulus_le (ik : H15ResonantOperatorIndex n K J) : h15Modulus ik ≤ n := by
  simp only [h15Modulus]
  exact ik.1.2

theorem h15Freq_pos (ik : H15ResonantOperatorIndex n K J) : 0 < h15Freq ik := by
  simp [h15Freq]

/-! ## Weights and amplitudes -/

/-- The ledger-normalised weight of an index. -/
noncomputable def h15Weight (ik : H15ResonantOperatorIndex n K J) : ℝ :=
  (((n : ℝ) + 1) * (((ik.1 : ℕ) : ℝ) + 1) * (((ik.2.1 : ℕ) : ℝ) + 1) * (((ik.2.2 : ℕ) : ℝ) + 1))⁻¹

theorem h15Weight_pos (ik : H15ResonantOperatorIndex n K J) : 0 < h15Weight ik := by
  unfold h15Weight
  positivity

theorem h15Weight_nonneg (ik : H15ResonantOperatorIndex n K J) : 0 ≤ h15Weight ik :=
  (h15Weight_pos ik).le

/-- The operator amplitude: normalised weight times the Mellin phase `r^{-it}`. -/
noncomputable def h15ResonantOperatorAmplitude (t : ℝ)
    (ik : H15ResonantOperatorIndex n K J) : ℂ :=
  (h15Weight ik : ℂ) * h15Phase (-t * Real.log (h15Freq ik))

@[simp] theorem h15ResonantOperatorAmplitude_norm (t : ℝ)
    (ik : H15ResonantOperatorIndex n K J) :
    ‖h15ResonantOperatorAmplitude t ik‖ = h15Weight ik := by
  simp [h15ResonantOperatorAmplitude, abs_of_pos (h15Weight_pos ik)]

/-! ## Total energy bound -/

/-- Telescoping estimate: `∑_{m<M} (m+1)^{-2} ≤ 2 - 1/M`. -/
theorem h15InvSqSum_le (M : ℕ) :
    ∑ m ∈ Finset.range M, (((m : ℝ) + 1) ^ 2)⁻¹ ≤ 2 - 1 / (M : ℝ) := by
  induction M with
  | zero => norm_num
  | succ M ih =>
      rw [Finset.sum_range_succ]
      rcases Nat.eq_zero_or_pos M with rfl | hM
      · norm_num
      · have hM' : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
        have h1 : (0 : ℝ) < (M : ℝ) := by linarith
        have h2 : (0 : ℝ) < (M : ℝ) + 1 := by linarith
        have key : (((M : ℝ) + 1) ^ 2)⁻¹ ≤ 1 / (M : ℝ) - 1 / ((M : ℝ) + 1) := by
          rw [div_sub_div _ _ (ne_of_gt h1) (ne_of_gt h2), inv_le_iff_one_le_mul₀ (by positivity)]
          field_simp
          nlinarith
        push_cast
        linarith

/-- Basic convergence estimate: `∑_{m<M} (m+1)^{-2} ≤ 2`. -/
theorem h15InvSqSum_le_two (M : ℕ) :
    ∑ m ∈ Finset.range M, (((m : ℝ) + 1) ^ 2)⁻¹ ≤ 2 := by
  have h := h15InvSqSum_le M
  have h0 : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
  linarith

theorem h15InvSqSum_fin_le_two (M : ℕ) :
    ∑ m : Fin M, ((((m : ℕ) : ℝ) + 1) ^ 2)⁻¹ ≤ 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun m => (((m : ℝ) + 1) ^ 2)⁻¹) M]
  exact h15InvSqSum_le_two M

/-- Total energy of the amplitudes: at most `8/(N+1)²`. -/
theorem h15WeightSq_sum_le (n K J : ℕ) :
    ∑ ik : H15ResonantOperatorIndex n K J, (h15Weight ik) ^ 2 ≤ 8 / (((n : ℝ) + 1) ^ 2) := by
  have hLHS : ∑ ik : H15ResonantOperatorIndex n K J, (h15Weight ik) ^ 2
      = ∑ q : Fin n, ∑ k : Fin K, ∑ j : Fin J,
        ((((n : ℝ) + 1) ^ 2)⁻¹ * ((((q : ℕ) : ℝ) + 1) ^ 2)⁻¹ * ((((k : ℕ) : ℝ) + 1) ^ 2)⁻¹ *
          ((((j : ℕ) : ℝ) + 1) ^ 2)⁻¹) := by
    simp only [Fintype.sum_prod_type, h15Weight, mul_pow, mul_inv, inv_pow]
  rw [hLHS]
  calc ∑ q : Fin n, ∑ k : Fin K, ∑ j : Fin J,
        ((((n : ℝ) + 1) ^ 2)⁻¹ * ((((q : ℕ) : ℝ) + 1) ^ 2)⁻¹ * ((((k : ℕ) : ℝ) + 1) ^ 2)⁻¹ *
          ((((j : ℕ) : ℝ) + 1) ^ 2)⁻¹)
      ≤ ∑ q : Fin n, ∑ k : Fin K,
        ((((n : ℝ) + 1) ^ 2)⁻¹ * ((((q : ℕ) : ℝ) + 1) ^ 2)⁻¹ * ((((k : ℕ) : ℝ) + 1) ^ 2)⁻¹ * 2) := by
        refine Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun k _ => ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (h15InvSqSum_fin_le_two J) (by positivity)
    _ ≤ ∑ q : Fin n, ((((n : ℝ) + 1) ^ 2)⁻¹ * ((((q : ℕ) : ℝ) + 1) ^ 2)⁻¹ * 4) := by
        refine Finset.sum_le_sum fun q _ => ?_
        have hrw : ∑ k : Fin K, ((((n : ℝ) + 1) ^ 2)⁻¹ * ((((q : ℕ) : ℝ) + 1) ^ 2)⁻¹ *
              ((((k : ℕ) : ℝ) + 1) ^ 2)⁻¹ * 2)
            = ((((n : ℝ) + 1) ^ 2)⁻¹ * ((((q : ℕ) : ℝ) + 1) ^ 2)⁻¹ * 2) *
              ∑ k : Fin K, ((((k : ℕ) : ℝ) + 1) ^ 2)⁻¹ := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        rw [hrw]
        have := mul_le_mul_of_nonneg_left (h15InvSqSum_fin_le_two K) (by positivity :
          (0 : ℝ) ≤ (((n : ℝ) + 1) ^ 2)⁻¹ * ((((q : ℕ) : ℝ) + 1) ^ 2)⁻¹ * 2)
        linarith
    _ ≤ 8 / (((n : ℝ) + 1) ^ 2) := by
        have hrw : ∑ q : Fin n, ((((n : ℝ) + 1) ^ 2)⁻¹ * ((((q : ℕ) : ℝ) + 1) ^ 2)⁻¹ * 4)
            = ((((n : ℝ) + 1) ^ 2)⁻¹ * 4) * ∑ q : Fin n, ((((q : ℕ) : ℝ) + 1) ^ 2)⁻¹ := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun q _ => by ring
        rw [hrw]
        have h2 := mul_le_mul_of_nonneg_left (h15InvSqSum_fin_le_two n)
          (by positivity : (0 : ℝ) ≤ (((n : ℝ) + 1) ^ 2)⁻¹ * 4)
        have h3 : (((n : ℝ) + 1) ^ 2)⁻¹ * 4 * 2 = 8 / (((n : ℝ) + 1) ^ 2) := by
          field_simp; ring
        linarith

theorem h15WeightSq_sum_nonneg (n K J : ℕ) :
    0 ≤ ∑ ik : H15ResonantOperatorIndex n K J, (h15Weight ik) ^ 2 :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

end NBMellinTools.NB12
