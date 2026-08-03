import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmDyadicFarTail

/-!
# Reindexing the sole remaining signed Ehm near core

At the common divisor cutoff supplied by the far-tail theorem, the only open
analytic term is the signed near core.  This file moves the dyadic cutoff `N`
inside its complementary-divisor sum and exposes the cutoff-averaged
coefficient multiplying the reciprocal kernel.

The result is an exact finite identity.  It displays the remaining object as

```text
full Möbius--von-Mangoldt joint form
  - near Möbius bilinear joint form
  + linear remainder.
```

No cancellation estimate is asserted.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicNearCoreReindex

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmComplementarySector
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCutoffAverageMainTerm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicCommonSplit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicFarTail
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmSignedAverage

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

private theorem sum_Icc_succ_extend_lower
    (f : ℕ → ℝ) (X N D : ℕ) (hXN : X ≤ N) :
    (∑ d ∈ Finset.Icc (N + 1) D, f d) =
      ∑ d ∈ Finset.Icc (X + 1) D, if N < d then f d else 0 := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext d
    simp only [Finset.mem_Icc, Finset.mem_filter]
    omega
  · intro d _
    rfl

/-- The signed cutoff average multiplying the near complementary divisor
pair `(m,d)`.  Its summand contains the product of the two BCF Möbius
coefficients at the same outer cutoff. -/
noncomputable def ehmDyadicNearCutoffCoeff
    (X m d : ℕ) : ℝ :=
  ∑ N ∈ ehmDyadicNBlock X,
    if m ≤ N then
      if N < d then
        dirichletCoeff N m / (m : ℝ) * dirichletCoeff N d
      else 0
    else 0

/-- The explicitly reindexed signed near complementary form. -/
noncomputable def ehmDyadicNearComplementaryJointSum
    (R1 : ℝ → ℝ) (X D J : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 (2 * X), ∑ d ∈ Finset.Icc (X + 1) D,
    ∑ q ∈ Finset.Icc 1 J,
      if d * q ≤ J then
        ehmDyadicNearCutoffCoeff X m d *
          R1 (((d * q : ℕ) : ℝ) / (m : ℝ))
      else 0

/-- The dyadic sum of common-cutoff near complementary sectors is exactly
the joint `(m,d,q)` form with the cutoff average isolated in its coefficient. -/
theorem sum_ehmFiniteComplementaryDivisorNearOuter_eq_joint
    (R1 : ℝ → ℝ) (X D J : ℕ) :
    (∑ N ∈ ehmDyadicNBlock X,
        ehmFiniteComplementaryDivisorNearOuter R1 N D J) =
      ehmDyadicNearComplementaryJointSum R1 X D J := by
  classical
  unfold ehmFiniteComplementaryDivisorNearOuter
    ehmFiniteComplementaryDivisorNearSum
    ehmDyadicNearComplementaryJointSum ehmDyadicNearCutoffCoeff
  simp_rw [Finset.mul_sum]
  calc
    (∑ N ∈ ehmDyadicNBlock X, ∑ m ∈ Finset.Icc 1 N,
        ∑ d ∈ Finset.Icc (N + 1) D, ∑ q ∈ Finset.Icc 1 J,
          dirichletCoeff N m / (m : ℝ) *
            (if d * q ≤ J then
              dirichletCoeff N d *
                R1 (((d * q : ℕ) : ℝ) * (1 / (m : ℝ)))
            else 0)) =
      ∑ N ∈ ehmDyadicNBlock X, ∑ m ∈ Finset.Icc 1 (2 * X),
        ∑ d ∈ Finset.Icc (X + 1) D, ∑ q ∈ Finset.Icc 1 J,
          if m ≤ N then
            if N < d then
              dirichletCoeff N m / (m : ℝ) *
                (if d * q ≤ J then
                  dirichletCoeff N d *
                    R1 (((d * q : ℕ) : ℝ) * (1 / (m : ℝ)))
                else 0)
            else 0
          else 0 := by
      apply Finset.sum_congr rfl
      intro N hNmem
      have hXN : X ≤ N := (Finset.mem_Icc.mp hNmem).1
      have hNU : N ≤ 2 * X := (Finset.mem_Icc.mp hNmem).2
      rw [sum_Icc_extend_upper
        (fun m => ∑ d ∈ Finset.Icc (N + 1) D, ∑ q ∈ Finset.Icc 1 J,
          dirichletCoeff N m / (m : ℝ) *
            (if d * q ≤ J then
              dirichletCoeff N d *
                R1 (((d * q : ℕ) : ℝ) * (1 / (m : ℝ)))
            else 0)) 1 N (2 * X) hNU]
      apply Finset.sum_congr rfl
      intro m _
      by_cases hmN : m ≤ N
      · simp only [hmN, if_true]
        rw [sum_Icc_succ_extend_lower
          (fun d => ∑ q ∈ Finset.Icc 1 J,
            dirichletCoeff N m / (m : ℝ) *
              (if d * q ≤ J then
                dirichletCoeff N d *
                  R1 (((d * q : ℕ) : ℝ) * (1 / (m : ℝ)))
              else 0)) X N D hXN]
        apply Finset.sum_congr rfl
        intro d _
        by_cases hNd : N < d <;> simp [hNd]
      · simp [hmN]
    _ = ∑ m ∈ Finset.Icc 1 (2 * X),
        ∑ d ∈ Finset.Icc (X + 1) D, ∑ q ∈ Finset.Icc 1 J,
          ∑ N ∈ ehmDyadicNBlock X,
            if m ≤ N then
              if N < d then
                dirichletCoeff N m / (m : ℝ) *
                  (if d * q ≤ J then
                    dirichletCoeff N d *
                      R1 (((d * q : ℕ) : ℝ) * (1 / (m : ℝ)))
                  else 0)
              else 0
            else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro q _
      by_cases hdq : d * q ≤ J
      · simp only [hdq, if_true]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro N _
        by_cases hmN : m ≤ N <;> by_cases hNd : N < d
        all_goals simp [hmN, hNd]
        all_goals ring_nf
      · simp [hdq]

/-- The signed common near core in its final explicit finite coordinates. -/
theorem ehmDyadicCommonNearCoreSum_eq_explicit
    (R1 : ℝ → ℝ) (X D J : ℕ) :
    ehmDyadicCommonNearCoreSum R1 X D J =
      ehmDyadicFullMainJointSum R1 X J -
        ehmDyadicNearComplementaryJointSum R1 X D J +
        ∑ N ∈ ehmDyadicNBlock X, ehmCoupledRemainder N := by
  unfold ehmDyadicCommonNearCoreSum
    ehmFiniteComplementaryDivisorNearCore
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum_ehmFiniteFullVonMangoldtTransformOuter_eq_joint,
    sum_ehmFiniteComplementaryDivisorNearOuter_eq_joint]

/-! ## Final explicit signed target -/

/-- The sole open near-core estimate stated directly for the explicit main
minus near-bilinear plus linear expression. -/
structure EhmDyadicExplicitNearCoreSignedAverageVanishing where
  eta : ℕ → ℝ
  eta_nonneg : ∀ X, 0 ≤ eta X
  eta_tendsto_zero : Tendsto eta atTop (nhds 0)
  cofinal_bound : ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      ehmDyadicUniformFarTailVanishing.D X ≤ J ∧
      (ehmDyadicFullMainJointSum ehmR1 X J -
          ehmDyadicNearComplementaryJointSum ehmR1 X
            (ehmDyadicUniformFarTailVanishing.D X) J +
          ∑ N ∈ ehmDyadicNBlock X, ehmCoupledRemainder N) ≤
        ((ehmDyadicNBlock X).card : ℝ) * eta X

/-- The explicit estimate is definitionally sufficient for the sole
remaining common-near-core package. -/
noncomputable def EhmDyadicExplicitNearCoreSignedAverageVanishing.toNearCore
    (H : EhmDyadicExplicitNearCoreSignedAverageVanishing) :
    EhmDyadicCommonNearCoreSignedAverageVanishing where
  eta := H.eta
  eta_nonneg := H.eta_nonneg
  eta_tendsto_zero := H.eta_tendsto_zero
  cofinal_bound X hX :=
    (H.cofinal_bound X hX).mono fun J hJ ↦ by
      rw [ehmDyadicCommonNearCoreSum_eq_explicit ehmR1 X
        (ehmDyadicUniformFarTailVanishing.D X) J]
      exact hJ

/-- Closing the explicit signed form closes the Báez--Duarte criterion through
the already verified far-tail and double-cofinal chain. -/
theorem baezDuarteCriterion_of_ehmDyadicExplicitNearCoreSignedAverage
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (H : EhmDyadicExplicitNearCoreSignedAverageVanishing) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmDyadicCommonNearCoreSignedAverage HS
    H.toNearCore

end RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicNearCoreReindex
