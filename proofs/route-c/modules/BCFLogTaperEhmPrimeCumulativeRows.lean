import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeAmplitude

/-!
# Row decomposition of the cumulative reciprocal phase

Interchanging the cumulative outer-cutoff sum with the Möbius sum expresses
each normalized phase as a finite average of ordinary log-tapered
reciprocal-phase rows.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeRows

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFourierResonanceAudit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativePhase
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeTaper

/-- One natural length-`N` logarithmically tapered reciprocal-phase row. -/
noncomputable def ehmPrimeTaperedReciprocalPhaseRow
    (h : ℤ) (k N : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 N,
    ((((ArithmeticFunction.moebius m : ℤ) : ℝ) * weight N m : ℝ) : ℂ) *
      ehmVaalerRationalPhase h (k + 1) 1 m

private theorem sum_Icc_extend_upper
    {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (N B : ℕ) (hNB : N ≤ B) :
    (∑ m ∈ Finset.Icc 1 N, f m) =
      ∑ m ∈ Finset.Icc 1 B, if m ≤ N then f m else 0 := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext m
    simp only [Finset.mem_Icc, Finset.mem_filter]
    omega
  · intro m _
    rfl

private theorem ofReal_ehmPrimeCumulativeOuterTaper
    (X k m : ℕ) :
    (ehmPrimeCumulativeOuterTaper X k m : ℂ) =
      ∑ N ∈ (ehmDyadicNBlock X).filter (fun N ↦ N ≤ k),
        if m ≤ N then
          ((weight N m / Real.log (N : ℝ) : ℝ) : ℂ)
        else 0 := by
  unfold ehmPrimeCumulativeOuterTaper
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro N _
  by_cases hmN : m ≤ N
  · simp [hmN]
  · simp [hmN]

/-- Exact row decomposition of the normalized cumulative phase. -/
theorem ehmPrimeCumulativeNormalizedPhaseForm_eq_taperedRows
    (h : ℤ) (X k : ℕ) :
    ehmPrimeCumulativeNormalizedPhaseForm h X k =
      (1 / ((((k + 1 : ℕ) : ℝ) : ℂ))) *
        ∑ N ∈ (ehmDyadicNBlock X).filter (fun N ↦ N ≤ k),
          ((1 / Real.log (N : ℝ) : ℝ) : ℂ) *
            ehmPrimeTaperedReciprocalPhaseRow h k N := by
  classical
  unfold ehmPrimeCumulativeNormalizedPhaseForm
  congr 1
  simp_rw [ofReal_ehmPrimeCumulativeOuterTaper]
  let muC : ℕ → ℂ := fun m ↦
    (((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ)
  let taperC : ℕ → ℕ → ℂ := fun N m ↦
    ((weight N m / Real.log (N : ℝ) : ℝ) : ℂ)
  calc
    (∑ m ∈ Finset.Icc 1 (2 * X),
        ((muC m *
            (∑ N ∈ (ehmDyadicNBlock X).filter (fun N ↦ N ≤ k),
              (if m ≤ N then
                taperC N m
              else 0))) *
          ehmVaalerRationalPhase h (k + 1) 1 m)) =
      ∑ m ∈ Finset.Icc 1 (2 * X),
        ∑ N ∈ (ehmDyadicNBlock X).filter (fun N ↦ N ≤ k),
          (if m ≤ N then
            (muC m * taperC N m) *
              ehmVaalerRationalPhase h (k + 1) 1 m
          else 0) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro N _
      by_cases hmN : m ≤ N
      · simp only [if_pos hmN]
      · simp [hmN]
    _ = ∑ N ∈ (ehmDyadicNBlock X).filter (fun N ↦ N ≤ k),
        ∑ m ∈ Finset.Icc 1 (2 * X),
          (if m ≤ N then
            (muC m * taperC N m) *
              ehmVaalerRationalPhase h (k + 1) 1 m
          else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ N ∈ (ehmDyadicNBlock X).filter (fun N ↦ N ≤ k),
        ((1 / Real.log (N : ℝ) : ℝ) : ℂ) *
          ehmPrimeTaperedReciprocalPhaseRow h k N := by
      apply Finset.sum_congr rfl
      intro N hN
      unfold ehmPrimeTaperedReciprocalPhaseRow
      rw [sum_Icc_extend_upper
        (fun m ↦
          ((((ArithmeticFunction.moebius m : ℤ) : ℝ) * weight N m : ℝ) : ℂ) *
            ehmVaalerRationalPhase h (k + 1) 1 m)
        N (2 * X) (Finset.mem_Icc.mp (Finset.mem_filter.mp hN).1).2]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      by_cases hmN : m ≤ N
      · simp only [if_pos hmN]
        unfold muC taperC
        push_cast
        ring
      · simp [hmN]

end RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeRows
