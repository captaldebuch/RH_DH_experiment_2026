import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeRows

/-!
# Quantitative stop test for cumulative reciprocal-phase rows

This module records both the rowwise triangle-inequality cost and the dyadic
mean-square cost.  The two estimates start from the same exact row
decomposition, making their losses directly comparable.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeRowBounds

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativePhase
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeRows

/-- Active outer rows at the index `k`. -/
def ehmPrimeCumulativeRowNBlock (X k : ℕ) : Finset ℕ :=
  (ehmDyadicNBlock X).filter (fun N ↦ N ≤ k)

/-- Norm of the inverse-log coefficient on one outer row. -/
noncomputable def ehmPrimeCumulativeRowCoeffNorm (N : ℕ) : ℝ :=
  ‖((1 / Real.log (N : ℝ) : ℝ) : ℂ)‖

/-- Cost obtained by applying the triangle inequality row by row. -/
noncomputable def ehmPrimeCumulativeRowL1Cost
    (h : ℤ) (X k : ℕ) : ℝ :=
  ‖(1 / ((((k + 1 : ℕ) : ℝ) : ℂ)))‖ *
    ∑ N ∈ ehmPrimeCumulativeRowNBlock X k,
      ehmPrimeCumulativeRowCoeffNorm N *
        ‖ehmPrimeTaperedReciprocalPhaseRow h k N‖

/-- Squared `ℓ²` mass of the outer inverse-log coefficients. -/
noncomputable def ehmPrimeCumulativeRowCoeffSquareMass
    (X k : ℕ) : ℝ :=
  ∑ N ∈ ehmPrimeCumulativeRowNBlock X k,
    (ehmPrimeCumulativeRowCoeffNorm N) ^ 2

/-- Squared `ℓ²` energy of the reciprocal-phase rows. -/
noncomputable def ehmPrimeCumulativeRowSquareEnergy
    (h : ℤ) (X k : ℕ) : ℝ :=
  ∑ N ∈ ehmPrimeCumulativeRowNBlock X k,
    ‖ehmPrimeTaperedReciprocalPhaseRow h k N‖ ^ 2

/-- Cost supplied by Cauchy--Schwarz in the outer cutoff. -/
noncomputable def ehmPrimeCumulativeRowL2Cost
    (h : ℤ) (X k : ℕ) : ℝ :=
  ‖(1 / ((((k + 1 : ℕ) : ℝ) : ℂ)))‖ *
    Real.sqrt (ehmPrimeCumulativeRowCoeffSquareMass X k) *
      Real.sqrt (ehmPrimeCumulativeRowSquareEnergy h X k)

/-- Exact row decomposition followed by the rowwise triangle inequality. -/
theorem norm_ehmPrimeCumulativeNormalizedPhaseForm_le_rowL1Cost
    (h : ℤ) (X k : ℕ) :
    ‖ehmPrimeCumulativeNormalizedPhaseForm h X k‖ ≤
      ehmPrimeCumulativeRowL1Cost h X k := by
  rw [ehmPrimeCumulativeNormalizedPhaseForm_eq_taperedRows, norm_mul]
  unfold ehmPrimeCumulativeRowL1Cost ehmPrimeCumulativeRowNBlock
    ehmPrimeCumulativeRowCoeffNorm
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    ‖∑ N ∈ (ehmDyadicNBlock X).filter (fun N ↦ N ≤ k),
        ((1 / Real.log (N : ℝ) : ℝ) : ℂ) *
          ehmPrimeTaperedReciprocalPhaseRow h k N‖ ≤
      ∑ N ∈ (ehmDyadicNBlock X).filter (fun N ↦ N ≤ k),
        ‖((1 / Real.log (N : ℝ) : ℝ) : ℂ) *
          ehmPrimeTaperedReciprocalPhaseRow h k N‖ :=
      norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro N _
      rw [norm_mul]

/-- Exact row decomposition followed by Cauchy--Schwarz in `N`. -/
theorem norm_ehmPrimeCumulativeNormalizedPhaseForm_le_rowL2Cost
    (h : ℤ) (X k : ℕ) :
    ‖ehmPrimeCumulativeNormalizedPhaseForm h X k‖ ≤
      ehmPrimeCumulativeRowL2Cost h X k := by
  rw [ehmPrimeCumulativeNormalizedPhaseForm_eq_taperedRows, norm_mul]
  unfold ehmPrimeCumulativeRowL2Cost
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    ‖∑ N ∈ ehmPrimeCumulativeRowNBlock X k,
        ((1 / Real.log (N : ℝ) : ℝ) : ℂ) *
          ehmPrimeTaperedReciprocalPhaseRow h k N‖ ≤
      ∑ N ∈ ehmPrimeCumulativeRowNBlock X k,
        ehmPrimeCumulativeRowCoeffNorm N *
          ‖ehmPrimeTaperedReciprocalPhaseRow h k N‖ := by
      calc
        ‖∑ N ∈ ehmPrimeCumulativeRowNBlock X k,
            ((1 / Real.log (N : ℝ) : ℝ) : ℂ) *
              ehmPrimeTaperedReciprocalPhaseRow h k N‖ ≤
          ∑ N ∈ ehmPrimeCumulativeRowNBlock X k,
            ‖((1 / Real.log (N : ℝ) : ℝ) : ℂ) *
              ehmPrimeTaperedReciprocalPhaseRow h k N‖ :=
          norm_sum_le _ _
        _ = _ := by
          unfold ehmPrimeCumulativeRowCoeffNorm
          apply Finset.sum_congr rfl
          intro N _
          rw [norm_mul]
    _ ≤ Real.sqrt (ehmPrimeCumulativeRowCoeffSquareMass X k) *
        Real.sqrt (ehmPrimeCumulativeRowSquareEnergy h X k) := by
      simpa [ehmPrimeCumulativeRowCoeffSquareMass,
        ehmPrimeCumulativeRowSquareEnergy] using
          Real.sum_mul_le_sqrt_mul_sqrt
            (ehmPrimeCumulativeRowNBlock X k)
            ehmPrimeCumulativeRowCoeffNorm
            (fun N ↦ ‖ehmPrimeTaperedReciprocalPhaseRow h k N‖)

/-- A uniform row bound propagates through the explicit `L¹` outer cost. -/
theorem ehmPrimeCumulativeRowL1Cost_le_of_uniform
    (h : ℤ) (X k : ℕ) (B : ℝ)
    (hrow : ∀ N ∈ ehmPrimeCumulativeRowNBlock X k,
      ‖ehmPrimeTaperedReciprocalPhaseRow h k N‖ ≤ B) :
    ehmPrimeCumulativeRowL1Cost h X k ≤
      ‖(1 / ((((k + 1 : ℕ) : ℝ) : ℂ)))‖ *
        ∑ N ∈ ehmPrimeCumulativeRowNBlock X k,
          ehmPrimeCumulativeRowCoeffNorm N * B := by
  unfold ehmPrimeCumulativeRowL1Cost
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.sum_le_sum
  intro N hN
  exact mul_le_mul_of_nonneg_left (hrow N hN)
    (by exact norm_nonneg _)

/-- A mean-square row estimate propagates through the `L²` outer cost. -/
theorem ehmPrimeCumulativeRowL2Cost_le_of_energy
    (h : ℤ) (X k : ℕ) (E : ℝ)
    (hE : ehmPrimeCumulativeRowSquareEnergy h X k ≤ E) :
    ehmPrimeCumulativeRowL2Cost h X k ≤
      ‖(1 / ((((k + 1 : ℕ) : ℝ) : ℂ)))‖ *
        Real.sqrt (ehmPrimeCumulativeRowCoeffSquareMass X k) *
          Real.sqrt E := by
  unfold ehmPrimeCumulativeRowL2Cost
  gcongr

end RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeRowBounds
