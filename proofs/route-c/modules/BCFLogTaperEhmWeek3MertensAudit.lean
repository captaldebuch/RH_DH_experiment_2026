import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmWeek3Closure
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmRectangularInstantiation
import RiemannHypothesis.Criteria.NymanBeurling.MobiusSummatoryClassical

/-!
# Week 3 audit: classical Mertens input in the Ehm rectangle

The shifted near-core Möbius rectangle has prefixes which factor into two
one-dimensional Mertens increments.  This module identifies each increment
exactly as a difference of the standard summatory function and inserts the
existing classical Mertens API.

The resulting theorem is the strongest direct consequence of separate
one-dimensional Mertens bounds.  It controls the isolated near rectangle
after absolute values are taken.  It does not construct the Week-3 signed
cancellation package, because the full H15 target must retain cancellation
with the completed main and linear correction.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmWeek3MertensAudit

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRectangularAbel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRectangularInstantiation
open RH.Criteria.NymanBeurling.MobiusSummatory

/-- A shifted inclusive Möbius prefix is the corresponding interval sum. -/
theorem ehmShiftedMertensPrefix_eq_sum_Icc
    (a K : ℕ) :
    ehmShiftedMertensPrefix a K =
      ∑ n ∈ Finset.Icc a (a + K),
        ((ArithmeticFunction.moebius n : ℤ) : ℝ) := by
  unfold ehmShiftedMertensPrefix
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  have hlength : a + K + 1 - a = K + 1 := by omega
  rw [hlength]

/-- Exact realization of a shifted prefix as a Mertens increment. -/
theorem ehmShiftedMertensPrefix_eq_mobiusSummatory_sub
    (a K : ℕ) (ha : 0 < a) :
    ehmShiftedMertensPrefix a K =
      mobiusSummatory (a + K) - mobiusSummatory (a - 1) := by
  rw [ehmShiftedMertensPrefix_eq_sum_Icc]
  have hle : a - 1 ≤ a + K := by omega
  have h := sum_Icc_succ_eq_sum_Icc_one_sub
    (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℝ))
    (a - 1) (a + K) hle
  have hsucc : a - 1 + 1 = a := by omega
  simpa only [hsucc, mobiusSummatory] using h

/-- The pointwise majorant supplied by the existing classical Mertens API. -/
noncomputable def ehmClassicalMertensMajorant
    (H : ClassicalMertensAPI) (N : ℕ) : ℝ :=
  H.C_M * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 3

theorem ehmClassicalMertensMajorant_nonneg
    (H : ClassicalMertensAPI) (N : ℕ) :
    0 ≤ ehmClassicalMertensMajorant H N := by
  unfold ehmClassicalMertensMajorant
  have hlog : 0 < Real.log (N + 2 : ℝ) := by
    apply Real.log_pos
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  exact div_nonneg
    (mul_nonneg H.C_M_pos.le (Nat.cast_nonneg N))
    (pow_nonneg hlog.le 3)

/-- Classical one-dimensional Mertens cancellation bounds every shifted
increment by the sum of its two endpoint majorants. -/
theorem abs_ehmShiftedMertensPrefix_le_classical
    (H : ClassicalMertensAPI) (a K : ℕ) (ha : 0 < a) :
    |ehmShiftedMertensPrefix a K| ≤
      ehmClassicalMertensMajorant H (a + K) +
        ehmClassicalMertensMajorant H (a - 1) := by
  rw [ehmShiftedMertensPrefix_eq_mobiusSummatory_sub a K ha]
  calc
    |mobiusSummatory (a + K) - mobiusSummatory (a - 1)| ≤
        |mobiusSummatory (a + K)| + |mobiusSummatory (a - 1)| :=
      abs_sub _ _
    _ ≤ ehmClassicalMertensMajorant H (a + K) +
          ehmClassicalMertensMajorant H (a - 1) := by
      exact add_le_add (H.mertens_bound (a + K))
        (H.mertens_bound (a - 1))

/-- The resulting product estimate for every exact H15 rectangular prefix.
This is a valid bound for the isolated near array, but it contains no
main/correction compensation. -/
theorem abs_rectangularPrefix_ehmShiftedNearArithmeticCoeff_le_classical
    (H : ClassicalMertensAPI) (X i j : ℕ) :
    |rectangularPrefix (ehmShiftedNearArithmeticCoeff X) i j| ≤
      (ehmClassicalMertensMajorant H (i + 1) +
          ehmClassicalMertensMajorant H 0) *
        (ehmClassicalMertensMajorant H (X + 1 + j) +
          ehmClassicalMertensMajorant H X) := by
  rw [rectangularPrefix_ehmShiftedNearArithmeticCoeff, abs_mul]
  have hi : |ehmShiftedMertensPrefix 1 i| ≤
      ehmClassicalMertensMajorant H (i + 1) +
        ehmClassicalMertensMajorant H 0 := by
    simpa [Nat.add_comm] using
      (abs_ehmShiftedMertensPrefix_le_classical H 1 i (by omega))
  have hj : |ehmShiftedMertensPrefix (X + 1) j| ≤
      ehmClassicalMertensMajorant H (X + 1 + j) +
        ehmClassicalMertensMajorant H X := by
    simpa using
      (abs_ehmShiftedMertensPrefix_le_classical H (X + 1) j (by omega))
  exact mul_le_mul
    hi hj
    (abs_nonneg _)
    (add_nonneg
      (ehmClassicalMertensMajorant_nonneg H (i + 1))
      (ehmClassicalMertensMajorant_nonneg H 0))

/-- Insert the classical prefix estimate into the generic rectangular Abel
transfer.  The conclusion deliberately concerns only the shifted near
rectangle; adding the retained correction by a triangle inequality would
discard the cancellation required by H15. -/
theorem abs_ehmShiftedNearRectangularSum_le_classical_mul_variation
    (H : ClassicalMertensAPI) (R1 : ℝ → ℝ)
    (X J M L : ℕ) (B : ℝ)
    (hB : ∀ i ≤ M, ∀ j ≤ L,
      (ehmClassicalMertensMajorant H (i + 1) +
          ehmClassicalMertensMajorant H 0) *
        (ehmClassicalMertensMajorant H (X + 1 + j) +
          ehmClassicalMertensMajorant H X) ≤ B) :
    |ehmShiftedNearRectangularSum R1 X J M L| ≤
      B * rectangularVariation
        (ehmShiftedNearCompleteKernel R1 X J) M L := by
  apply abs_rectangularSum_le_discrepancy_mul_variation
  intro i hi j hj
  exact (abs_rectangularPrefix_ehmShiftedNearArithmeticCoeff_le_classical
    H X i j).trans (hB i hi j hj)

end RH.Criteria.NymanBeurling.BCFLogTaperEhmWeek3MertensAudit
