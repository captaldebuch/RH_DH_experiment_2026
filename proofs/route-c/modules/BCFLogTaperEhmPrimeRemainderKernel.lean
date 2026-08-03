import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmPrimeTruncatedFormula

/-!
# Global signed Abel kernel for the truncated prime remainder

This module reindexes the complete dyadic remainder transport before taking
absolute values.  For each prime index `k`, all outer cutoffs `N` and Möbius
rows `m` are first combined into one signed coefficient.  Only the norm of
that global coefficient enters the resulting operator majorant.

This is strictly more faithful than summing rowwise Abel majorants and is the
natural quantitative stop test for the common-height explicit formula.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeRemainderKernel

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCorrectionMatching
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeTruncatedFormula

/-- Coefficient of `u(k)` in a single finite Abel row.  Upper endpoint,
lower endpoint, and difference contributions retain their relative signs. -/
noncomputable def ehmPrimeAbelKernelAtom
    (N m J k : ℕ) : ℂ :=
  (if k = J then (ehmR1 ((J : ℝ) / (m : ℝ)) : ℂ) else 0) -
    (if k = N then (ehmR1 ((N : ℝ) / (m : ℝ)) : ℂ) else 0) -
      if N ≤ k ∧ k < J then
        (ehmR1 (((k + 1 : ℕ) : ℝ) / (m : ℝ)) : ℂ) -
          (ehmR1 ((k : ℝ) / (m : ℝ)) : ℂ)
      else 0

private theorem sum_Icc_indicator_eq_single
    {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) (X J a : ℕ) (ha : a ∈ Finset.Icc X J) :
    (∑ k ∈ Finset.Icc X J, if k = a then f k else 0) = f a := by
  classical
  simp [ha]

private theorem sum_Icc_interval_indicator_eq_Ico
    {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) (X N J : ℕ) (hXN : X ≤ N) :
    (∑ k ∈ Finset.Icc X J, if N ≤ k ∧ k < J then f k else 0) =
      ∑ k ∈ Finset.Ico N J, f k := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
    omega
  · intro k _
    rfl

/-- Abel summation on a finite natural interval, with prefixes starting at
the lower endpoint. -/
private theorem finite_abel_sum_Icc_mul_eq_endpoint_add_sum_partial
    (a w : ℕ → ℂ) (A B : ℕ) (hAB : A ≤ B) :
    (∑ n ∈ Finset.Icc A B, a n * w n) =
      (∑ j ∈ Finset.Icc A B, a j) * w (B + 1) +
        ∑ n ∈ Finset.Icc A B,
          (∑ j ∈ Finset.Icc A n, a j) * (w n - w (n + 1)) := by
  induction B, hAB using Nat.le_induction with
  | base =>
      simp
      ring
  | succ B hAB ih =>
      have hAB' : A ≤ B + 1 := by omega
      rw [Finset.sum_Icc_succ_top hAB', Finset.sum_Icc_succ_top hAB',
        Finset.sum_Icc_succ_top hAB']
      rw [ih]
      rw [Finset.sum_Icc_succ_top hAB']
      ring

/-- Exact coefficient expansion of one Abel row on any ambient interval
containing `[N,J]`. -/
theorem ehmPrimeAbelMode_eq_kernel_sum
    (u : ℕ → ℂ) (X N m J : ℕ) (hXN : X ≤ N) (hNJ : N ≤ J) :
    ehmPrimeAbelMode u N m J =
      ∑ k ∈ Finset.Icc X J, u k * ehmPrimeAbelKernelAtom N m J k := by
  classical
  have hJmem : J ∈ Finset.Icc X J := by
    exact Finset.mem_Icc.mpr ⟨hXN.trans hNJ, le_rfl⟩
  have hNmem : N ∈ Finset.Icc X J := by
    exact Finset.mem_Icc.mpr ⟨hXN, hNJ⟩
  unfold ehmPrimeAbelMode ehmPrimeAbelKernelAtom
  simp_rw [mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib]
  rw [sum_Icc_indicator_eq_single
      (fun k ↦ u k * (ehmR1 ((J : ℝ) / (m : ℝ)) : ℂ)) X J J hJmem]
  rw [sum_Icc_indicator_eq_single
      (fun k ↦ u k * (ehmR1 ((N : ℝ) / (m : ℝ)) : ℂ)) X J N hNmem]
  rw [sum_Icc_interval_indicator_eq_Ico
      (fun k ↦ u k *
        ((ehmR1 (((k + 1 : ℕ) : ℝ) / (m : ℝ)) : ℂ) -
          (ehmR1 ((k : ℝ) / (m : ℝ)) : ℂ))) X N J hXN]
  rw [← Finset.sum_sub_distrib]
  simp_rw [mul_sub]

/-- A constant discrepancy mode is annihilated by one complete Abel row. -/
theorem ehmPrimeAbelMode_one_eq_zero
    (N m J : ℕ) (hNJ : N ≤ J) :
    ehmPrimeAbelMode (fun _ ↦ (1 : ℂ)) N m J = 0 := by
  unfold ehmPrimeAbelMode
  simp only [one_mul]
  rw [Finset.sum_Ico_eq_sum_range]
  have hs := Finset.sum_range_sub
    (fun k : ℕ ↦
      (ehmR1 (((N + k : ℕ) : ℝ) / (m : ℝ)) : ℂ)) (J - N)
  simp only [Nat.add_assoc]
  rw [hs, Nat.add_sub_of_le hNJ]
  simp

/-- Complete dyadic Abel transport of an arbitrary complex mode. -/
noncomputable def ehmPrimeDyadicAbelAggregate
    (u : ℕ → ℂ) (X J : ℕ) : ℂ :=
  ∑ N ∈ ehmDyadicNBlock X, ehmPrimeHighAggregateMode u N J

/-- The signed coefficient of `u(k)` after combining every outer cutoff and
Möbius row. -/
noncomputable def ehmPrimeDyadicAbelKernelCoeff
    (X J k : ℕ) : ℂ :=
  ∑ N ∈ ehmDyadicNBlock X, ∑ m ∈ Finset.Icc 1 N,
    ((dirichletCoeff N m / (m : ℝ) / Real.log N : ℝ) : ℂ) *
      ehmPrimeAbelKernelAtom N m J k

/-- Exact global coefficient expansion.  All arithmetic signs in `(N,m)`
are combined before the coefficient at `k` is exposed. -/
theorem ehmPrimeDyadicAbelAggregate_eq_kernel_sum
    (u : ℕ → ℂ) (X J : ℕ) (hJ : 2 * X ≤ J) :
    ehmPrimeDyadicAbelAggregate u X J =
      ∑ k ∈ Finset.Icc X J,
        u k * ehmPrimeDyadicAbelKernelCoeff X J k := by
  classical
  unfold ehmPrimeDyadicAbelAggregate ehmPrimeHighAggregateMode
    ehmPrimeDyadicAbelKernelCoeff
  calc
    (∑ N ∈ ehmDyadicNBlock X, ∑ m ∈ Finset.Icc 1 N,
        ((dirichletCoeff N m / (m : ℝ) / Real.log N : ℝ) : ℂ) *
          ehmPrimeAbelMode u N m J) =
      ∑ N ∈ ehmDyadicNBlock X, ∑ m ∈ Finset.Icc 1 N,
        ((dirichletCoeff N m / (m : ℝ) / Real.log N : ℝ) : ℂ) *
          (∑ k ∈ Finset.Icc X J,
            u k * ehmPrimeAbelKernelAtom N m J k) := by
        apply Finset.sum_congr rfl
        intro N hNmem
        apply Finset.sum_congr rfl
        intro m _
        rw [ehmPrimeAbelMode_eq_kernel_sum u X N m J
          (Finset.mem_Icc.mp hNmem).1
          ((Finset.mem_Icc.mp hNmem).2.trans hJ)]
    _ = ∑ N ∈ ehmDyadicNBlock X, ∑ m ∈ Finset.Icc 1 N,
        ∑ k ∈ Finset.Icc X J,
          u k *
            (((dirichletCoeff N m / (m : ℝ) / Real.log N : ℝ) : ℂ) *
              ehmPrimeAbelKernelAtom N m J k) := by
        apply Finset.sum_congr rfl
        intro N _
        apply Finset.sum_congr rfl
        intro m _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
    _ = ∑ k ∈ Finset.Icc X J, ∑ N ∈ ehmDyadicNBlock X,
        ∑ m ∈ Finset.Icc 1 N,
          u k *
            (((dirichletCoeff N m / (m : ℝ) / Real.log N : ℝ) : ℂ) *
              ehmPrimeAbelKernelAtom N m J k) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro N _
        rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro N _
      rw [Finset.mul_sum]

/-- The globally aggregated Abel kernel has exact total mass zero.  This is
the algebraic form of the machine-precision cancellation seen in the kernel
diagnostic; it is independent of any prime estimate. -/
theorem sum_ehmPrimeDyadicAbelKernelCoeff_eq_zero
    (X J : ℕ) (hJ : 2 * X ≤ J) :
    (∑ k ∈ Finset.Icc X J, ehmPrimeDyadicAbelKernelCoeff X J k) = 0 := by
  have hkernel := ehmPrimeDyadicAbelAggregate_eq_kernel_sum
    (fun _ ↦ (1 : ℂ)) X J hJ
  have haggregate :
      ehmPrimeDyadicAbelAggregate (fun _ ↦ (1 : ℂ)) X J = 0 := by
    classical
    unfold ehmPrimeDyadicAbelAggregate ehmPrimeHighAggregateMode
    apply Finset.sum_eq_zero
    intro N hN
    apply Finset.sum_eq_zero
    intro m _
    rw [ehmPrimeAbelMode_one_eq_zero N m J
      ((Finset.mem_Icc.mp hN).2.trans hJ), mul_zero]
  rw [haggregate] at hkernel
  simpa using hkernel.symm

/-- Since the global kernel has zero mass, any constant may be subtracted
from the discrepancy mode before estimating it. -/
theorem ehmPrimeDyadicAbelAggregate_eq_centered_kernel_sum
    (u : ℕ → ℂ) (c : ℂ) (X J : ℕ) (hJ : 2 * X ≤ J) :
    ehmPrimeDyadicAbelAggregate u X J =
      ∑ k ∈ Finset.Icc X J,
        (u k - c) * ehmPrimeDyadicAbelKernelCoeff X J k := by
  rw [ehmPrimeDyadicAbelAggregate_eq_kernel_sum u X J hJ]
  have hzero := sum_ehmPrimeDyadicAbelKernelCoeff_eq_zero X J hJ
  calc
    (∑ k ∈ Finset.Icc X J,
        u k * ehmPrimeDyadicAbelKernelCoeff X J k) =
      (∑ k ∈ Finset.Icc X J,
        ((u k - c) * ehmPrimeDyadicAbelKernelCoeff X J k +
          c * ehmPrimeDyadicAbelKernelCoeff X J k)) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
    _ = (∑ k ∈ Finset.Icc X J,
          (u k - c) * ehmPrimeDyadicAbelKernelCoeff X J k) +
        c * (∑ k ∈ Finset.Icc X J,
          ehmPrimeDyadicAbelKernelCoeff X J k) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by rw [hzero, mul_zero, add_zero]

/-- Prefix of the global signed Abel kernel. -/
noncomputable def ehmPrimeDyadicAbelKernelPrefix
    (X J k : ℕ) : ℂ :=
  ∑ j ∈ Finset.Icc X k, ehmPrimeDyadicAbelKernelCoeff X J j

/-- A second exact Abel transform uses the zero total mass to replace the
size of the prime remainder by its discrete variation. -/
theorem ehmPrimeDyadicAbelAggregate_eq_variation_kernel_sum
    (u : ℕ → ℂ) (X J : ℕ) (hJ : 2 * X ≤ J) :
    ehmPrimeDyadicAbelAggregate u X J =
      ∑ k ∈ Finset.Icc X J,
        ehmPrimeDyadicAbelKernelPrefix X J k * (u k - u (k + 1)) := by
  have hXJ : X ≤ J := by omega
  rw [ehmPrimeDyadicAbelAggregate_eq_kernel_sum u X J hJ]
  calc
    (∑ k ∈ Finset.Icc X J,
        u k * ehmPrimeDyadicAbelKernelCoeff X J k) =
      ∑ k ∈ Finset.Icc X J,
        ehmPrimeDyadicAbelKernelCoeff X J k * u k := by
        apply Finset.sum_congr rfl
        intro k _
        ring
    _ = (∑ k ∈ Finset.Icc X J,
          ehmPrimeDyadicAbelKernelCoeff X J k) * u (J + 1) +
        ∑ k ∈ Finset.Icc X J,
          ehmPrimeDyadicAbelKernelPrefix X J k * (u k - u (k + 1)) := by
        exact finite_abel_sum_Icc_mul_eq_endpoint_add_sum_partial
          (ehmPrimeDyadicAbelKernelCoeff X J) u X J hXJ
    _ = _ := by
      rw [sum_ehmPrimeDyadicAbelKernelCoeff_eq_zero X J hJ,
        zero_mul, zero_add]

/-- The truncated explicit-formula remainder is exactly the global Abel
aggregate of its common-height remainder mode. -/
theorem ehmPrimeTruncatedRemainderDyadicAggregate_eq_abelAggregate
    (H : EhmPrimeDiscrepancyTruncatedModeData)
    (Y X J : ℕ) :
    ehmPrimeTruncatedRemainderDyadicAggregate H Y X J =
      ehmPrimeDyadicAbelAggregate (H.remainderMode Y) X J := by
  rfl

/-- Weighted `ℓ¹` size of the already-aggregated signed Abel kernel. -/
noncomputable def ehmPrimeDyadicAbelWeightedKernelCost
    (r : ℕ → ℝ) (X J : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc X J,
    r k * ‖ehmPrimeDyadicAbelKernelCoeff X J k‖

/-- Weighted cost after exploiting exact zero mass and applying a second
Abel transform.  Its input is an envelope for discrete variation rather
than an envelope for the values of the mode. -/
noncomputable def ehmPrimeDyadicAbelVariationKernelCost
    (v : ℕ → ℝ) (X J : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc X J,
    v k * ‖ehmPrimeDyadicAbelKernelPrefix X J k‖

/-- A pointwise envelope for a mode bounds its dyadic Abel transport by the
weighted norm of the global signed coefficients.  No absolute value is taken
before the `(N,m)` aggregation defining those coefficients. -/
theorem norm_ehmPrimeDyadicAbelAggregate_le_weightedKernelCost
    (u : ℕ → ℂ) (r : ℕ → ℝ) (X J : ℕ)
    (hJ : 2 * X ≤ J)
    (hu : ∀ k ∈ Finset.Icc X J, ‖u k‖ ≤ r k) :
    ‖ehmPrimeDyadicAbelAggregate u X J‖ ≤
      ehmPrimeDyadicAbelWeightedKernelCost r X J := by
  rw [ehmPrimeDyadicAbelAggregate_eq_kernel_sum u X J hJ]
  unfold ehmPrimeDyadicAbelWeightedKernelCost
  calc
    ‖∑ k ∈ Finset.Icc X J,
        u k * ehmPrimeDyadicAbelKernelCoeff X J k‖ ≤
      ∑ k ∈ Finset.Icc X J,
        ‖u k * ehmPrimeDyadicAbelKernelCoeff X J k‖ :=
      norm_sum_le _ _
    _ = ∑ k ∈ Finset.Icc X J,
        ‖u k‖ * ‖ehmPrimeDyadicAbelKernelCoeff X J k‖ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [norm_mul]
    _ ≤ ∑ k ∈ Finset.Icc X J,
        r k * ‖ehmPrimeDyadicAbelKernelCoeff X J k‖ := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_right (hu k hk) (norm_nonneg _)

/-- Variation-envelope bound for the globally centered kernel. -/
theorem norm_ehmPrimeDyadicAbelAggregate_le_variationKernelCost
    (u : ℕ → ℂ) (v : ℕ → ℝ) (X J : ℕ)
    (hJ : 2 * X ≤ J)
    (hu : ∀ k ∈ Finset.Icc X J, ‖u k - u (k + 1)‖ ≤ v k) :
    ‖ehmPrimeDyadicAbelAggregate u X J‖ ≤
      ehmPrimeDyadicAbelVariationKernelCost v X J := by
  rw [ehmPrimeDyadicAbelAggregate_eq_variation_kernel_sum u X J hJ]
  unfold ehmPrimeDyadicAbelVariationKernelCost
  calc
    ‖∑ k ∈ Finset.Icc X J,
        ehmPrimeDyadicAbelKernelPrefix X J k * (u k - u (k + 1))‖ ≤
      ∑ k ∈ Finset.Icc X J,
        ‖ehmPrimeDyadicAbelKernelPrefix X J k * (u k - u (k + 1))‖ :=
      norm_sum_le _ _
    _ = ∑ k ∈ Finset.Icc X J,
        ‖u k - u (k + 1)‖ *
          ‖ehmPrimeDyadicAbelKernelPrefix X J k‖ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [norm_mul, mul_comm]
    _ ≤ ∑ k ∈ Finset.Icc X J,
        v k * ‖ehmPrimeDyadicAbelKernelPrefix X J k‖ := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_right (hu k hk) (norm_nonneg _)

/-- Specialization to the actual common-height explicit-formula remainder. -/
theorem norm_ehmPrimeTruncatedRemainderDyadicAggregate_le_kernelCost
    (H : EhmPrimeDiscrepancyTruncatedModeData)
    (r : ℕ → ℝ) (Y X J : ℕ)
    (hJ : 2 * X ≤ J)
    (hrem : ∀ k ∈ Finset.Icc X J, ‖H.remainderMode Y k‖ ≤ r k) :
    ‖ehmPrimeTruncatedRemainderDyadicAggregate H Y X J‖ ≤
      ehmPrimeDyadicAbelWeightedKernelCost r X J := by
  rw [ehmPrimeTruncatedRemainderDyadicAggregate_eq_abelAggregate]
  exact norm_ehmPrimeDyadicAbelAggregate_le_weightedKernelCost
    (H.remainderMode Y) r X J hJ hrem

/-- The actual common-height explicit-formula remainder can therefore be
controlled through its discrete variation. -/
theorem norm_ehmPrimeTruncatedRemainderDyadicAggregate_le_variationKernelCost
    (H : EhmPrimeDiscrepancyTruncatedModeData)
    (v : ℕ → ℝ) (Y X J : ℕ)
    (hJ : 2 * X ≤ J)
    (hrem : ∀ k ∈ Finset.Icc X J,
      ‖H.remainderMode Y k - H.remainderMode Y (k + 1)‖ ≤ v k) :
    ‖ehmPrimeTruncatedRemainderDyadicAggregate H Y X J‖ ≤
      ehmPrimeDyadicAbelVariationKernelCost v X J := by
  rw [ehmPrimeTruncatedRemainderDyadicAggregate_eq_abelAggregate]
  exact norm_ehmPrimeDyadicAbelAggregate_le_variationKernelCost
    (H.remainderMode Y) v X J hJ hrem

end RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeRemainderKernel
