import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmPrimePrefixCollapse

/-!
# Cumulative outer taper for the prime remainder kernel

The lower-triangular prefix still has a variable inner range `m ≤ N`.
This module interchanges the finite `N,m` sums and factors the Möbius
coefficient.  The result is a single Möbius transform against an explicit
cumulative logarithmic taper.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeTaper

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimePrefixCollapse
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeRemainderKernel

/-- The cumulative contribution of outer cutoffs `N ∈ [X,2X]` with
`N ≤ k` and `m ≤ N`. -/
noncomputable def ehmPrimeCumulativeOuterTaper
    (X k m : ℕ) : ℝ :=
  ∑ N ∈ (ehmDyadicNBlock X).filter (fun N ↦ N ≤ k),
    if m ≤ N then weight N m / Real.log N else 0

/-- Positive-sign lower-triangular `R₁` transform before the global minus
sign in the prefix formula. -/
noncomputable def ehmPrimeFilteredR1Kernel
    (X k : ℕ) : ℂ :=
  ∑ N ∈ (ehmDyadicNBlock X).filter (fun N ↦ N ≤ k),
    ∑ m ∈ Finset.Icc 1 N,
      ((dirichletCoeff N m / (m : ℝ) / Real.log N : ℝ) : ℂ) *
        (ehmR1 (((k + 1 : ℕ) : ℝ) / (m : ℝ)) : ℂ)

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

/-- Exact interchange of the variable-range double sum. -/
theorem ehmPrimeFilteredR1Kernel_eq_cumulativeMobius
    (X k : ℕ) :
    ehmPrimeFilteredR1Kernel X k =
      ∑ m ∈ Finset.Icc 1 (2 * X),
        ((((ArithmeticFunction.moebius m : ℤ) : ℝ) / (m : ℝ) : ℝ) : ℂ) *
          (ehmPrimeCumulativeOuterTaper X k m : ℂ) *
            (ehmR1 (((k + 1 : ℕ) : ℝ) / (m : ℝ)) : ℂ) := by
  classical
  unfold ehmPrimeFilteredR1Kernel ehmPrimeCumulativeOuterTaper
  calc
    (∑ N ∈ (ehmDyadicNBlock X).filter (fun N ↦ N ≤ k),
        ∑ m ∈ Finset.Icc 1 N,
          ((dirichletCoeff N m / (m : ℝ) / Real.log N : ℝ) : ℂ) *
            (ehmR1 (((k + 1 : ℕ) : ℝ) / (m : ℝ)) : ℂ)) =
      ∑ N ∈ (ehmDyadicNBlock X).filter (fun N ↦ N ≤ k),
        ∑ m ∈ Finset.Icc 1 (2 * X),
          if m ≤ N then
            ((dirichletCoeff N m / (m : ℝ) / Real.log N : ℝ) : ℂ) *
              (ehmR1 (((k + 1 : ℕ) : ℝ) / (m : ℝ)) : ℂ)
          else 0 := by
        apply Finset.sum_congr rfl
        intro N hN
        exact sum_Icc_extend_upper
          (fun m ↦
            ((dirichletCoeff N m / (m : ℝ) / Real.log N : ℝ) : ℂ) *
              (ehmR1 (((k + 1 : ℕ) : ℝ) / (m : ℝ)) : ℂ))
          N (2 * X) (Finset.mem_Icc.mp (Finset.mem_filter.mp hN).1).2
    _ = ∑ m ∈ Finset.Icc 1 (2 * X),
        ∑ N ∈ (ehmDyadicNBlock X).filter (fun N ↦ N ≤ k),
          if m ≤ N then
            ((dirichletCoeff N m / (m : ℝ) / Real.log N : ℝ) : ℂ) *
              (ehmR1 (((k + 1 : ℕ) : ℝ) / (m : ℝ)) : ℂ)
          else 0 := by
        rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m _
      push_cast
      rw [Finset.mul_sum]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro N _
      by_cases hmN : m ≤ N
      · simp only [if_pos hmN]
        unfold dirichletCoeff
        push_cast
        ring
      · simp [hmN]

/-- The interior prefix is one cumulative-taper Möbius transform. -/
theorem ehmPrimeDyadicAbelKernelPrefix_eq_cumulativeMobius
    (X J k : ℕ) (hJ : 2 * X ≤ J) (hkX : X ≤ k) (hkJ : k < J) :
    ehmPrimeDyadicAbelKernelPrefix X J k =
      -∑ m ∈ Finset.Icc 1 (2 * X),
        ((((ArithmeticFunction.moebius m : ℤ) : ℝ) / (m : ℝ) : ℝ) : ℂ) *
          (ehmPrimeCumulativeOuterTaper X k m : ℂ) *
            (ehmR1 (((k + 1 : ℕ) : ℝ) / (m : ℝ)) : ℂ) := by
  rw [ehmPrimeDyadicAbelKernelPrefix_eq_filtered X J k hJ hkX hkJ]
  change -ehmPrimeFilteredR1Kernel X k = _
  rw [ehmPrimeFilteredR1Kernel_eq_cumulativeMobius]

end RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeTaper
