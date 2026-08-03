import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmHighSectorCompensation

/-!
# Abel summation for the centered-prime high sector

This file rewrites the exact high-sector fluctuation `Λ - 1` in terms of
finite centered Chebyshev increments.  It is the common algebraic input for
two distinct analytic audits:

* classical estimates for `ψ(x) - x`, and
* the explicit formula in terms of zeta zeros.

No estimate for either input is assumed here.  In particular, the retained
mean-prime completion remains outside the rowwise absolute values.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeDiscrepancyAbel

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmHighSectorCompensation

/-- The centered von Mangoldt coefficient on the interval immediately above
`N`, indexed from zero. -/
noncomputable def ehmCenteredPrimeShiftedCoeff (N i : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt (N + i + 1) - 1

/-- The first `K` centered Chebyshev coefficients above `N`.  Analytically
this is `ψ(N+K) - ψ(N) - K`. -/
noncomputable def ehmCenteredChebyshevIncrement (N K : ℕ) : ℝ :=
  ∑ i ∈ Finset.range K, ehmCenteredPrimeShiftedCoeff N i

/-- The global integer-point prime discrepancy `ψ(k)-k`, written without
introducing any asymptotic prime number theorem. -/
noncomputable def ehmPrimeDiscrepancy (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k,
    (ArithmeticFunction.vonMangoldt (i + 1) - 1)

/-- A shifted centered Chebyshev increment is the exact difference of the
global prime discrepancy at its two endpoints. -/
theorem ehmCenteredChebyshevIncrement_eq_discrepancy_sub
    (N K : ℕ) :
    ehmCenteredChebyshevIncrement N K =
      ehmPrimeDiscrepancy (N + K) - ehmPrimeDiscrepancy N := by
  unfold ehmCenteredChebyshevIncrement ehmCenteredPrimeShiftedCoeff
    ehmPrimeDiscrepancy
  rw [Finset.sum_range_add]
  ring

/-- The shifted `R₁` row paired with the centered prime discrepancy. -/
noncomputable def ehmCenteredPrimeShiftedKernel (N m i : ℕ) : ℝ :=
  ehmR1 (((N + i + 1 : ℕ) : ℝ) / (m : ℝ))

/-- A single centered-prime row, before the outer Möbius/log-taper weight. -/
noncomputable def ehmCenteredPrimeShiftedRow (N m K : ℕ) : ℝ :=
  ∑ i ∈ Finset.range K,
    ehmCenteredPrimeShiftedKernel N m i *
      ehmCenteredPrimeShiftedCoeff N i

/-- The exact Abel transform of a centered-prime row. -/
noncomputable def ehmCenteredPrimeAbelRow (N m K : ℕ) : ℝ :=
  ehmCenteredPrimeShiftedKernel N m (K - 1) *
      ehmCenteredChebyshevIncrement N K -
    ∑ i ∈ Finset.range (K - 1),
      (ehmCenteredPrimeShiftedKernel N m (i + 1) -
          ehmCenteredPrimeShiftedKernel N m i) *
        ehmCenteredChebyshevIncrement N (i + 1)

/-- Finite summation by parts for the centered von Mangoldt row. -/
theorem ehmCenteredPrimeShiftedRow_eq_abel
    (N m K : ℕ) :
    ehmCenteredPrimeShiftedRow N m K =
      ehmCenteredPrimeAbelRow N m K := by
  unfold ehmCenteredPrimeShiftedRow ehmCenteredPrimeAbelRow
    ehmCenteredChebyshevIncrement
  simpa only [smul_eq_mul] using
    Finset.sum_range_by_parts
      (ehmCenteredPrimeShiftedKernel N m)
      (ehmCenteredPrimeShiftedCoeff N) K

/-- The termwise Abel majorant.  It records exactly where a classical
pointwise estimate for `ψ(x)-x` loses the signed outer cancellation. -/
noncomputable def ehmCenteredPrimeAbelMajorant (N m K : ℕ) : ℝ :=
  |ehmCenteredPrimeShiftedKernel N m (K - 1)| *
      |ehmCenteredChebyshevIncrement N K| +
    ∑ i ∈ Finset.range (K - 1),
      |ehmCenteredPrimeShiftedKernel N m (i + 1) -
          ehmCenteredPrimeShiftedKernel N m i| *
        |ehmCenteredChebyshevIncrement N (i + 1)|

/-- Ordinary Abel summation followed by absolute values.  The inequality is
useful as a stop test, but is intentionally not used to separate the retained
mean-prime correction from the centered tail. -/
theorem abs_ehmCenteredPrimeShiftedRow_le_majorant
    (N m K : ℕ) :
    |ehmCenteredPrimeShiftedRow N m K| ≤
      ehmCenteredPrimeAbelMajorant N m K := by
  rw [ehmCenteredPrimeShiftedRow_eq_abel]
  unfold ehmCenteredPrimeAbelRow ehmCenteredPrimeAbelMajorant
  calc
    |ehmCenteredPrimeShiftedKernel N m (K - 1) *
          ehmCenteredChebyshevIncrement N K -
        ∑ i ∈ Finset.range (K - 1),
          (ehmCenteredPrimeShiftedKernel N m (i + 1) -
              ehmCenteredPrimeShiftedKernel N m i) *
            ehmCenteredChebyshevIncrement N (i + 1)| ≤
        |ehmCenteredPrimeShiftedKernel N m (K - 1) *
          ehmCenteredChebyshevIncrement N K| +
        |∑ i ∈ Finset.range (K - 1),
          (ehmCenteredPrimeShiftedKernel N m (i + 1) -
              ehmCenteredPrimeShiftedKernel N m i) *
            ehmCenteredChebyshevIncrement N (i + 1)| := abs_sub _ _
    _ ≤ |ehmCenteredPrimeShiftedKernel N m (K - 1) *
          ehmCenteredChebyshevIncrement N K| +
        ∑ i ∈ Finset.range (K - 1),
          |(ehmCenteredPrimeShiftedKernel N m (i + 1) -
              ehmCenteredPrimeShiftedKernel N m i) *
            ehmCenteredChebyshevIncrement N (i + 1)| := by
          gcongr
          exact Finset.abs_sum_le_sum_abs
            (fun i ↦
              (ehmCenteredPrimeShiftedKernel N m (i + 1) -
                  ehmCenteredPrimeShiftedKernel N m i) *
                ehmCenteredChebyshevIncrement N (i + 1))
            (Finset.range (K - 1))
    _ = _ := by
      rw [abs_mul]
      apply congrArg₂ (· + ·) rfl
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul]

/-- Reindex an interval row `N < j ≤ J` by its length `J-N`. -/
theorem ehmCenteredPrimeIntervalRow_eq_shifted
    (N m J : ℕ) (hNJ : N ≤ J) :
    (∑ j ∈ Finset.Icc (N + 1) J,
      (ArithmeticFunction.vonMangoldt j - 1) *
        ehmR1 ((j : ℝ) / (m : ℝ))) =
      ehmCenteredPrimeShiftedRow N m (J - N) := by
  unfold ehmCenteredPrimeShiftedRow
    ehmCenteredPrimeShiftedKernel ehmCenteredPrimeShiftedCoeff
  rw [← Finset.Ico_add_one_right_eq_Icc]
  rw [Finset.sum_Ico_eq_sum_range]
  have hsub : J + 1 - (N + 1) = J - N := by omega
  rw [hsub]
  apply Finset.sum_congr rfl
  intro i _
  have hij : N + 1 + i = N + i + 1 := by omega
  rw [hij]
  ring

/-- The complete centered high tail after Abel summation in the prime
variable.  The outer coefficients are not estimated termwise. -/
noncomputable def ehmFiniteCenteredPrimeAbelTail (N J : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N,
    (dirichletCoeff N m / (m : ℝ) / Real.log N) *
      ehmCenteredPrimeAbelRow N m (J - N)

/-- Exact centered-Chebyshev representation of the high tail. -/
theorem ehmFiniteVonMangoldtHighCenteredTail_eq_abel
    (N J : ℕ) (hNJ : N ≤ J) :
    ehmFiniteVonMangoldtHighCenteredTail N J =
      ehmFiniteCenteredPrimeAbelTail N J := by
  classical
  unfold ehmFiniteVonMangoldtHighCenteredTail
    ehmFiniteCenteredPrimeAbelTail
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← ehmCenteredPrimeShiftedRow_eq_abel]
  rw [← ehmCenteredPrimeIntervalRow_eq_shifted N m J hNJ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The full retained target in its exact Abel-summed form.  This is the
shared starting point for the classical and explicit-formula routes. -/
theorem ehmRetainedCenteredPrimeExpression_eq_abel
    (N J : ℕ) (hNJ : N ≤ J) :
    ehmFiniteMeanPrimeCompletedDefect N J +
        ehmFiniteVonMangoldtHighCenteredTail N J =
      ehmFiniteMeanPrimeCompletedDefect N J +
        ehmFiniteCenteredPrimeAbelTail N J := by
  rw [ehmFiniteVonMangoldtHighCenteredTail_eq_abel N J hNJ]

end RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeDiscrepancyAbel
