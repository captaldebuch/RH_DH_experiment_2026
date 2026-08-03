import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeRowBounds

/-!
# Outer-cutoff variation of a tapered reciprocal-phase row

Adjacent outer rows share the same constant taper mode.  Their difference
therefore contains only a small inverse-log increment multiplying a
log-weighted reciprocal-phase Möbius sum.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeRowVariation

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFourierResonanceAudit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeRows

/-- Log-weighted reciprocal-phase row controlling variation in `N`. -/
noncomputable def ehmPrimeLogWeightedReciprocalPhaseRow
    (h : ℤ) (k N : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 N,
    ((((ArithmeticFunction.moebius m : ℤ) : ℝ) *
      Real.log (m : ℝ) : ℝ) : ℂ) *
        ehmVaalerRationalPhase h (k + 1) 1 m

/-- Exact adjacent-row difference.  The new endpoint at `m=N+1` contributes
zero because the logarithmic taper vanishes at its own cutoff. -/
theorem ehmPrimeTaperedReciprocalPhaseRow_succ_sub
    (h : ℤ) (k N : ℕ) (hN : 2 ≤ N) :
    ehmPrimeTaperedReciprocalPhaseRow h k (N + 1) -
        ehmPrimeTaperedReciprocalPhaseRow h k N =
      ((1 / Real.log (N : ℝ) -
        1 / Real.log ((N + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
          ehmPrimeLogWeightedReciprocalPhaseRow h k N := by
  classical
  unfold ehmPrimeTaperedReciprocalPhaseRow
  rw [Finset.sum_Icc_succ_top (by omega)]
  rw [weight_cutoff (by omega)]
  norm_num
  rw [← Finset.sum_sub_distrib]
  unfold ehmPrimeLogWeightedReciprocalPhaseRow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [weight_of_two_le (hN.trans (Nat.le_succ N)),
    weight_of_two_le hN]
  push_cast
  ring

end RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeRowVariation
