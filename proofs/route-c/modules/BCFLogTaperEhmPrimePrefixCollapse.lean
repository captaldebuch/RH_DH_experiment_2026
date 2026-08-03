import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmPrimeRemainderVariation

/-!
# Lower-triangular collapse of the global prime remainder kernel

The prefix of one Abel atom telescopes completely.  Away from the terminal
endpoint it is simply the negative `R₁` value at the next prime index.  This
module proves that identity and exposes the resulting lower-triangular form
of the global signed prefix kernel.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimePrefixCollapse

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeRemainderKernel

/-- The complete coefficient atom has zero total mass. -/
theorem sum_ehmPrimeAbelKernelAtom_eq_zero
    (X N m J : ℕ) (hXN : X ≤ N) (hNJ : N ≤ J) :
    (∑ k ∈ Finset.Icc X J, ehmPrimeAbelKernelAtom N m J k) = 0 := by
  have hkernel := ehmPrimeAbelMode_eq_kernel_sum
    (fun _ ↦ (1 : ℂ)) X N m J hXN hNJ
  rw [ehmPrimeAbelMode_one_eq_zero N m J hNJ] at hkernel
  simpa using hkernel.symm

/-- Exact prefix of one Abel atom.  The three cases are encoded by the
single indicator on the right. -/
theorem sum_ehmPrimeAbelKernelAtom_prefix
    (X N m J k : ℕ)
    (hXN : X ≤ N) (hNJ : N ≤ J) (hk : k ∈ Finset.Icc X J) :
    (∑ j ∈ Finset.Icc X k, ehmPrimeAbelKernelAtom N m J j) =
      if N ≤ k ∧ k < J then
        -(ehmR1 (((k + 1 : ℕ) : ℝ) / (m : ℝ)) : ℂ)
      else 0 := by
  classical
  by_cases hkJ : k = J
  · subst k
    rw [sum_ehmPrimeAbelKernelAtom_eq_zero X N m J hXN hNJ]
    simp
  · have hkmem := Finset.mem_Icc.mp hk
    have hkJlt : k < J := lt_of_le_of_ne hkmem.2 hkJ
    by_cases hNk : N ≤ k
    · have hXk : X ≤ k := hkmem.1
      have hsame :
          (∑ j ∈ Finset.Icc X k, ehmPrimeAbelKernelAtom N m J j) =
            ∑ j ∈ Finset.Icc X k,
              ehmPrimeAbelKernelAtom N m (k + 1) j := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjJ : j < J := (Finset.mem_Icc.mp hj).2.trans_lt hkJlt
        have hjk : j < k + 1 := Nat.lt_succ_of_le (Finset.mem_Icc.mp hj).2
        simp [ehmPrimeAbelKernelAtom, ne_of_lt hjJ, ne_of_lt hjk,
          hjJ, hjk]
      have hzero := sum_ehmPrimeAbelKernelAtom_eq_zero
        X N m (k + 1) hXN (hNk.trans (Nat.le_succ k))
      have htop :
          ehmPrimeAbelKernelAtom N m (k + 1) (k + 1) =
            (ehmR1 (((k + 1 : ℕ) : ℝ) / (m : ℝ)) : ℂ) := by
        have hne : k + 1 ≠ N := by omega
        simp [ehmPrimeAbelKernelAtom, hne]
      rw [Finset.sum_Icc_succ_top (hXk.trans (Nat.le_succ k)), htop] at hzero
      rw [if_pos ⟨hNk, hkJlt⟩, hsame]
      linear_combination hzero
    · rw [if_neg (by simp [hNk])]
      apply Finset.sum_eq_zero
      intro j hj
      have hjN : j < N :=
        (Finset.mem_Icc.mp hj).2.trans_lt (Nat.lt_of_not_ge hNk)
      have hjJ : j < J := hjN.trans_le hNJ
      simp [ehmPrimeAbelKernelAtom, ne_of_lt hjJ, ne_of_lt hjN,
        not_le_of_gt hjN]

/-- Global prefix written as a sum of its lower-triangular one-row
contributions. -/
theorem ehmPrimeDyadicAbelKernelPrefix_eq_lowerTriangular
    (X J k : ℕ) (hJ : 2 * X ≤ J) (hk : k ∈ Finset.Icc X J) :
    ehmPrimeDyadicAbelKernelPrefix X J k =
      ∑ N ∈ ehmDyadicNBlock X, ∑ m ∈ Finset.Icc 1 N,
        ((dirichletCoeff N m / (m : ℝ) / Real.log N : ℝ) : ℂ) *
          (if N ≤ k ∧ k < J then
            -(ehmR1 (((k + 1 : ℕ) : ℝ) / (m : ℝ)) : ℂ)
          else 0) := by
  classical
  unfold ehmPrimeDyadicAbelKernelPrefix ehmPrimeDyadicAbelKernelCoeff
  calc
    (∑ j ∈ Finset.Icc X k, ∑ N ∈ ehmDyadicNBlock X,
        ∑ m ∈ Finset.Icc 1 N,
          ((dirichletCoeff N m / (m : ℝ) / Real.log N : ℝ) : ℂ) *
            ehmPrimeAbelKernelAtom N m J j) =
      ∑ N ∈ ehmDyadicNBlock X, ∑ m ∈ Finset.Icc 1 N,
        ((dirichletCoeff N m / (m : ℝ) / Real.log N : ℝ) : ℂ) *
          (∑ j ∈ Finset.Icc X k, ehmPrimeAbelKernelAtom N m J j) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro N _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro m _
        rw [Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro N hN
      apply Finset.sum_congr rfl
      intro m _
      rw [sum_ehmPrimeAbelKernelAtom_prefix X N m J k
        (Finset.mem_Icc.mp hN).1 ((Finset.mem_Icc.mp hN).2.trans hJ) hk]

/-- The complete dyadic Abel transport in its explicit lower-triangular
variation form. -/
theorem ehmPrimeDyadicAbelAggregate_eq_lowerTriangularVariation
    (u : ℕ → ℂ) (X J : ℕ) (hJ : 2 * X ≤ J) :
    ehmPrimeDyadicAbelAggregate u X J =
      ∑ k ∈ Finset.Icc X J,
        (∑ N ∈ ehmDyadicNBlock X, ∑ m ∈ Finset.Icc 1 N,
          ((dirichletCoeff N m / (m : ℝ) / Real.log N : ℝ) : ℂ) *
            (if N ≤ k ∧ k < J then
              -(ehmR1 (((k + 1 : ℕ) : ℝ) / (m : ℝ)) : ℂ)
            else 0)) *
          (u k - u (k + 1)) := by
  rw [ehmPrimeDyadicAbelAggregate_eq_variation_kernel_sum u X J hJ]
  apply Finset.sum_congr rfl
  intro k hk
  rw [ehmPrimeDyadicAbelKernelPrefix_eq_lowerTriangular X J k hJ hk]

/-- On every interior index, the global prefix is independent of the far
cutoff except for the requirement `k < J`.  Only outer cutoffs `N ≤ k`
contribute. -/
theorem ehmPrimeDyadicAbelKernelPrefix_eq_filtered
    (X J k : ℕ) (hJ : 2 * X ≤ J) (hkX : X ≤ k) (hkJ : k < J) :
    ehmPrimeDyadicAbelKernelPrefix X J k =
      -∑ N ∈ (ehmDyadicNBlock X).filter (fun N ↦ N ≤ k),
        ∑ m ∈ Finset.Icc 1 N,
          ((dirichletCoeff N m / (m : ℝ) / Real.log N : ℝ) : ℂ) *
            (ehmR1 (((k + 1 : ℕ) : ℝ) / (m : ℝ)) : ℂ) := by
  classical
  rw [ehmPrimeDyadicAbelKernelPrefix_eq_lowerTriangular X J k hJ
    (Finset.mem_Icc.mpr ⟨hkX, hkJ.le⟩)]
  rw [Finset.sum_filter, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro N hN
  by_cases hNk : N ≤ k
  · have hpair : N ≤ k ∧ k < J := ⟨hNk, hkJ⟩
    rw [if_pos hNk]
    simp only [if_pos hpair]
    simp_rw [mul_neg]
    rw [Finset.sum_neg_distrib]
  · simp [hNk]

/-- The terminal prefix vanishes exactly. -/
theorem ehmPrimeDyadicAbelKernelPrefix_terminal
    (X J : ℕ) (hJ : 2 * X ≤ J) :
    ehmPrimeDyadicAbelKernelPrefix X J J = 0 := by
  rw [ehmPrimeDyadicAbelKernelPrefix_eq_lowerTriangular X J J hJ
    (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)]
  simp

end RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimePrefixCollapse
