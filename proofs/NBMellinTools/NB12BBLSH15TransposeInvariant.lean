/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15DoublyLocalizedOrientation

/-!
# NB12zzzb: literal H15 invariance under orientation transpose

The preceding support audit constructed the involution which swaps primitive
`a` and `q` and toggles the Estermann orientation.  This file proves that the
actual arithmetic data are unchanged by that involution: validity, Laurent
weight, reduced rational row, post-functional-equation variables, and the
separated direct-additive frequency summand.

Consequently the orientation-one contribution on `(U,Q)` is not a new
analytic sector.  It is exactly the orientation-zero contribution on `(Q,U)`
after finite reindexing.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius

namespace NBMellinTools.NB12

@[simp] theorem h15LaurentRowValid_transpose {N : ℕ}
    (i : H15LaurentRowIndex N) :
    h15LaurentRowValid (h15LaurentTranspose i) ↔
      h15LaurentRowValid i := by
  unfold h15LaurentRowValid
  simp only [h15LaurentG_transpose, h15LaurentA_transpose,
    h15LaurentQ_transpose]
  constructor
  · rintro ⟨hgq, hga, hq, ha, hcop⟩
    exact ⟨hga, hgq, ha, hq, hcop.symm⟩
  · rintro ⟨hga, hgq, ha, hq, hcop⟩
    exact ⟨hgq, hga, hq, ha, hcop.symm⟩

@[simp] theorem h15LaurentRowWeight_transpose {N : ℕ}
    (i : H15LaurentRowIndex N) :
    h15LaurentRowWeight (h15LaurentTranspose i) =
      h15LaurentRowWeight i := by
  classical
  by_cases hvalid : h15LaurentRowValid i
  · have hvalidT : h15LaurentRowValid (h15LaurentTranspose i) :=
      (h15LaurentRowValid_transpose i).2 hvalid
    rw [h15LaurentRowWeight, if_pos hvalidT]
    rw [h15LaurentRowWeight, if_pos hvalid]
    simp only [h15LaurentG_transpose, h15LaurentA_transpose,
      h15LaurentQ_transpose]
    push_cast
    ring
  · rw [h15LaurentRowWeight, if_neg (by
      simpa only [h15LaurentRowValid_transpose] using hvalid)]
    rw [h15LaurentRowWeight, if_neg hvalid]

@[simp] theorem h15LaurentReducedDenominator_transpose {N : ℕ}
    (i : H15LaurentRowIndex N) :
    h15LaurentReducedDenominator (h15LaurentTranspose i) =
      h15LaurentReducedDenominator i := by
  rcases i with ⟨g, a, q, orientation⟩
  fin_cases orientation <;> rfl

@[simp] theorem h15LaurentRow_transpose {N : ℕ}
    (i : H15LaurentRowIndex N) :
    h15LaurentRow (h15LaurentTranspose i) = h15LaurentRow i := by
  rcases i with ⟨g, a, q, orientation⟩
  fin_cases orientation <;> rfl

@[simp] theorem h15BettinChandeeInverseVariable_transpose {N : ℕ}
    (i : H15LaurentRowIndex N) :
    h15BettinChandeeInverseVariable (h15LaurentTranspose i) =
      h15BettinChandeeInverseVariable i := by
  rcases i with ⟨g, a, q, orientation⟩
  fin_cases orientation <;> rfl

@[simp] theorem h15BettinChandeeModulusVariable_transpose {N : ℕ}
    (i : H15LaurentRowIndex N) :
    h15BettinChandeeModulusVariable (h15LaurentTranspose i) =
      h15BettinChandeeModulusVariable i := by
  rcases i with ⟨g, a, q, orientation⟩
  fin_cases orientation <;> rfl

@[simp] theorem h15DirectAdditiveSeparatedSummand_transpose
    {N : ℕ} (damping : ℝ) (i : H15LaurentRowIndex N)
    (r : ℕ) (t : ℝ) :
    h15DirectAdditiveSeparatedSummand N damping
        (h15LaurentTranspose i) r t =
      h15DirectAdditiveSeparatedSummand N damping i r t := by
  simp [h15DirectAdditiveSeparatedSummand]

@[simp] theorem h15DirectAdditiveFixedHeightSummand_transpose
    {N : ℕ} (damping : ℝ) (i : H15LaurentRowIndex N)
    (r : ℕ) (t : ℝ) :
    h15DirectAdditiveFixedHeightSummand N damping
        (h15LaurentTranspose i, r) t =
      h15DirectAdditiveFixedHeightSummand N damping (i, r) t := by
  classical
  by_cases hvalid : h15LaurentRowValid i
  · have hvalidT : h15LaurentRowValid (h15LaurentTranspose i) :=
      (h15LaurentRowValid_transpose i).2 hvalid
    rw [h15DirectAdditiveFixedHeightSummand, if_pos hvalidT]
    rw [h15DirectAdditiveFixedHeightSummand, if_pos hvalid]
    exact h15DirectAdditiveSeparatedSummand_transpose damping i r t
  · have hvalidT : ¬ h15LaurentRowValid (h15LaurentTranspose i) := by
      simpa only [h15LaurentRowValid_transpose] using hvalid
    simp [h15DirectAdditiveFixedHeightSummand, hvalid, hvalidT]

/-- Literal orientation-one direct-additive slices are exactly
orientation-zero slices on the transposed dyadic block. -/
theorem sum_orientationOne_directAdditive_eq_orientationZero_swapped
    {N g U Q : ℕ} (damping : ℝ) (r : ℕ) (t : ℝ) :
    ∑ i ∈ h15DoublyLocalizedOrientationOneIndices N g U Q,
        h15DirectAdditiveFixedHeightSummand N damping (i, r) t =
      ∑ i ∈ h15DoublyLocalizedOrientationZeroIndices N g Q U,
        h15DirectAdditiveFixedHeightSummand N damping (i, r) t := by
  rw [← sum_orientationOne_comp_transpose_eq_sum_orientationZero
    (f := fun i =>
      h15DirectAdditiveFixedHeightSummand N damping (i, r) t)]
  apply Finset.sum_congr rfl
  intro i _hi
  exact (h15DirectAdditiveFixedHeightSummand_transpose damping i r t).symm

end NBMellinTools.NB12
