import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmCutoffAverageReindex

/-!
# The completed main term in the signed Ehm cutoff average

This file executes the algebraic part of Priority 2.  Completing the divisor
coefficient recombines the low region `j ≤ N` and the high region `N < j`
into one full von-Mangoldt transform.  Averaging over the outer cutoff then
isolates a one-variable logarithmic taper multiplying the fixed Möbius sign.

Consequently, the cutoff average does not by itself supply sign cancellation:
the genuine analytic problem remains the coupled Möbius--von-Mangoldt kernel,
the omitted-divisor correction, and the linear remainder.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmCutoffAverageMainTerm

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmBoundaryResearch
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmSignedAverage
open RH.Criteria.NymanBeurling.BCFLogTaperEhmUniformBoundary
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCutoffAverageReindex

private theorem sum_Icc_extend_upper
    (f : ℕ → ℝ) (a n u : ℕ) (hnu : n ≤ u) :
    (∑ k ∈ Finset.Icc a n, f k) =
      ∑ k ∈ Finset.Icc a u, if k ≤ n then f k else 0 := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext k
    simp only [Finset.mem_Icc, Finset.mem_filter]
    omega
  · intro k _
    rfl

/-- The positive-log-taper average left after the outer cutoff has been
summed.  No Möbius factor is included in this definition. -/
noncomputable def ehmDyadicLogTaperAverage (X m : ℕ) : ℝ :=
  ∑ N ∈ ehmDyadicNBlock X,
    if m ≤ N then weight N m / Real.log (N : ℝ) else 0

/-- The complete cutoff coefficient in the full von-Mangoldt main term. -/
noncomputable def ehmDyadicMobiusCutoffCoeff (X m : ℕ) : ℝ :=
  ∑ N ∈ ehmDyadicNBlock X,
    if m ≤ N then
      dirichletCoeff N m / ((m : ℝ) * Real.log (N : ℝ))
    else 0

/-- Averaging in `N` leaves the Möbius sign fixed and only smooths its
logarithmic taper. -/
theorem ehmDyadicMobiusCutoffCoeff_eq_moebius_mul_average
    (X m : ℕ) :
    ehmDyadicMobiusCutoffCoeff X m =
      (((ArithmeticFunction.moebius m : ℤ) : ℝ) / (m : ℝ)) *
        ehmDyadicLogTaperAverage X m := by
  classical
  unfold ehmDyadicMobiusCutoffCoeff ehmDyadicLogTaperAverage
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N _
  by_cases hmN : m ≤ N
  · simp only [hmN, if_true, dirichletCoeff]
    ring_nf
  · simp [hmN]

/-- On a genuine dyadic block the cutoff average multiplying the Möbius sign
is nonnegative.  Thus any signed saving in the completed main form must use
arithmetic cancellation in `m` (and its coupling to the correction terms),
not oscillation of this cutoff weight. -/
theorem ehmDyadicLogTaperAverage_nonneg
    (X m : ℕ) (hX : 2 ≤ X) (hm : 1 ≤ m) :
    0 ≤ ehmDyadicLogTaperAverage X m := by
  classical
  unfold ehmDyadicLogTaperAverage
  apply Finset.sum_nonneg
  intro N hNmem
  by_cases hmN : m ≤ N
  · simp only [hmN, if_true]
    have hN2 : 2 ≤ N := hX.trans (Finset.mem_Icc.mp hNmem).1
    have hlogN : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hlogm0 : 0 ≤ Real.log (m : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hm)
    have hlogmN : Real.log (m : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by exact_mod_cast (show 0 < m by omega))
        (by exact_mod_cast hmN)
    have hweight : 0 ≤ weight N m := by
      rw [weight_of_two_le hN2]
      have hratio : Real.log (m : ℝ) / Real.log (N : ℝ) ≤ 1 :=
        (div_le_one hlogN).2 hlogmN
      linarith
    exact div_nonneg hweight hlogN.le
  · simp [hmN]

/-- The reindexed full von-Mangoldt main term. -/
noncomputable def ehmDyadicFullMainJointSum
    (R1 : ℝ → ℝ) (X J : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 (2 * X), ∑ j ∈ Finset.Icc 2 J,
    ArithmeticFunction.vonMangoldt j *
      ehmDyadicMobiusCutoffCoeff X m * R1 ((j : ℝ) / (m : ℝ))

/-- Exact finite reindexing of the completed main term. -/
theorem sum_ehmFiniteFullVonMangoldtTransformOuter_eq_joint
    (R1 : ℝ → ℝ) (X J : ℕ) :
    (∑ N ∈ ehmDyadicNBlock X,
        ehmFiniteFullVonMangoldtTransformOuter R1 N J) =
      ehmDyadicFullMainJointSum R1 X J := by
  classical
  unfold ehmFiniteFullVonMangoldtTransformOuter
    ehmFiniteFullVonMangoldtTransform ehmDyadicFullMainJointSum
    ehmDyadicMobiusCutoffCoeff
  simp_rw [Finset.mul_sum]
  calc
    (∑ N ∈ ehmDyadicNBlock X, ∑ m ∈ Finset.Icc 1 N,
        ∑ j ∈ Finset.Icc 2 J,
          dirichletCoeff N m / (m : ℝ) *
            (ArithmeticFunction.vonMangoldt j / Real.log (N : ℝ) *
              R1 ((j : ℝ) * (1 / (m : ℝ))))) =
      ∑ N ∈ ehmDyadicNBlock X, ∑ m ∈ Finset.Icc 1 (2 * X),
        ∑ j ∈ Finset.Icc 2 J,
          if m ≤ N then
            dirichletCoeff N m / (m : ℝ) *
              (ArithmeticFunction.vonMangoldt j / Real.log (N : ℝ) *
                R1 ((j : ℝ) * (1 / (m : ℝ))))
          else 0 := by
      apply Finset.sum_congr rfl
      intro N hNmem
      have hNU : N ≤ 2 * X := (Finset.mem_Icc.mp hNmem).2
      rw [sum_Icc_extend_upper
        (fun m => ∑ j ∈ Finset.Icc 2 J,
          dirichletCoeff N m / (m : ℝ) *
            (ArithmeticFunction.vonMangoldt j / Real.log (N : ℝ) *
              R1 ((j : ℝ) * (1 / (m : ℝ)))))
        1 N (2 * X) hNU]
      apply Finset.sum_congr rfl
      intro m _
      by_cases hmN : m ≤ N <;> simp [hmN]
    _ = ∑ m ∈ Finset.Icc 1 (2 * X), ∑ j ∈ Finset.Icc 2 J,
        ∑ N ∈ ehmDyadicNBlock X,
          if m ≤ N then
            dirichletCoeff N m / (m : ℝ) *
              (ArithmeticFunction.vonMangoldt j / Real.log (N : ℝ) *
                R1 ((j : ℝ) * (1 / (m : ℝ))))
          else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro N _
      by_cases hmN : m ≤ N
      · simp only [hmN, if_true]
        ring_nf
      · simp [hmN]

/-- The full signed dyadic boundary in completed-divisor variables.  This is
the smallest exact coupled target presently available: the first term is the
Möbius--von-Mangoldt main form, the second is the signed omitted-divisor
correction, and the third is the linear remainder. -/
theorem sum_ehmFiniteCoupledBoundaryExpression_eq_fullMain_sub_missing
    (R1 : ℝ → ℝ) (X J : ℕ) (hX : 2 ≤ X) (hJ : 2 * X ≤ J) :
    (∑ N ∈ ehmDyadicNBlock X,
        ehmFiniteCoupledBoundaryExpression R1 N J) =
      ehmDyadicFullMainJointSum R1 X J -
        (∑ N ∈ ehmDyadicNBlock X,
          ehmFiniteMissingDivisorTailOuter R1 N J) +
        ∑ N ∈ ehmDyadicNBlock X, ehmCoupledRemainder N := by
  calc
    (∑ N ∈ ehmDyadicNBlock X,
        ehmFiniteCoupledBoundaryExpression R1 N J) =
      ∑ N ∈ ehmDyadicNBlock X,
        (ehmFiniteFullVonMangoldtTransformOuter R1 N J -
          ehmFiniteMissingDivisorTailOuter R1 N J +
          ehmCoupledRemainder N) := by
      apply Finset.sum_congr rfl
      intro N hNmem
      exact ehmFiniteCoupledBoundaryExpression_eq_fullOuter_sub_missing_add_remainder
        R1 N J (hX.trans (Finset.mem_Icc.mp hNmem).1)
        ((Finset.mem_Icc.mp hNmem).2.trans hJ)
    _ = (∑ N ∈ ehmDyadicNBlock X,
          ehmFiniteFullVonMangoldtTransformOuter R1 N J) -
        (∑ N ∈ ehmDyadicNBlock X,
          ehmFiniteMissingDivisorTailOuter R1 N J) +
        ∑ N ∈ ehmDyadicNBlock X, ehmCoupledRemainder N := by
      simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = _ := by
      rw [sum_ehmFiniteFullVonMangoldtTransformOuter_eq_joint]

/-! ## Exact completed-main closure interface -/

/-- The remaining one-sided signed estimate after exact divisor completion
and cutoff reindexing.  This is an explicit open analytic hypothesis, not an
asserted estimate. -/
structure EhmDyadicCompletedMainSignedAverageVanishing where
  eta : ℕ → ℝ
  eta_nonneg : ∀ X, 0 ≤ eta X
  eta_tendsto_zero : Tendsto eta atTop (nhds 0)
  cofinal_sum_bound : ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      2 * X ≤ J ∧
      (ehmDyadicFullMainJointSum BCFLogTaperEhm.ehmR1 X J -
          (∑ N ∈ ehmDyadicNBlock X,
            ehmFiniteMissingDivisorTailOuter BCFLogTaperEhm.ehmR1 N J) +
          ∑ N ∈ ehmDyadicNBlock X, ehmCoupledRemainder N) ≤
        ((ehmDyadicNBlock X).card : ℝ) * eta X

/-- The completed-main estimate is exactly sufficient for the signed finite
boundary average required by the double-cofinal closure. -/
noncomputable def EhmDyadicCompletedMainSignedAverageVanishing.toBoundaryAverage
    (H : EhmDyadicCompletedMainSignedAverageVanishing) :
    EhmDyadicSignedBoundaryAverageVanishing where
  eta := H.eta
  eta_nonneg := H.eta_nonneg
  eta_tendsto_zero := H.eta_tendsto_zero
  cofinal_sum_bound X hX :=
    (H.cofinal_sum_bound X hX).mono fun J hJ ↦ by
      rw [sum_ehmFiniteCoupledBoundaryExpression_eq_fullMain_sub_missing
        BCFLogTaperEhm.ehmR1 X J hX hJ.1]
      exact hJ.2

/-- The new completed-main target feeds the already verified
Báez--Duarte closure without any additional analytic assumptions. -/
theorem baezDuarteCriterion_of_ehmDyadicCompletedMainSignedAverage
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (H : EhmDyadicCompletedMainSignedAverageVanishing) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmDyadicSignedBoundaryAverage HS
    H.toBoundaryAverage

end RH.Criteria.NymanBeurling.BCFLogTaperEhmCutoffAverageMainTerm
