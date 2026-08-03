import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmSignedAverage

/-!
# Reindexing the signed Ehm cutoff average

This file executes Priority 1 of the double-cofinal research programme.  We
specialize the exact near/far decomposition to the natural cutoffs
`D(N)=N` and `M(N)=N`, and then move the dyadic cutoff variable `N` to the
innermost position in the low and high bilinear blocks.

The low joint sum has the range

```text
X <= N <= 2X,  m <= N,  j <= N,
```

while the high joint sum has

```text
X <= N <= 2X,  m <= N < j <= J.
```

All identities are finite and exact.  The coupled remainder and the
complementary far subtraction are retained with their original signs.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmCutoffAverageReindex

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmBoundaryTail
open RH.Criteria.NymanBeurling.BCFLogTaperEhmComplementarySector
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDispersionBlocks
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmSignedAverage
open RH.Criteria.NymanBeurling.BCFLogTaperEhmUniformBoundary

/-! ## Generic finite reindexing lemmas -/

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

private theorem sum_Icc_succ_extend_lower_two
    (f : ℕ → ℝ) (n u : ℕ) (hn : 2 ≤ n) :
    (∑ k ∈ Finset.Icc (n + 1) u, f k) =
      ∑ k ∈ Finset.Icc 2 u, if n < k then f k else 0 := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext k
    simp only [Finset.mem_Icc, Finset.mem_filter]
    omega
  · intro k _
    rfl

private theorem sum_comm_three
    (S T U : Finset ℕ) (f : ℕ → ℕ → ℕ → ℝ) :
    (∑ s ∈ S, ∑ t ∈ T, ∑ u ∈ U, f s t u) =
      ∑ t ∈ T, ∑ u ∈ U, ∑ s ∈ S, f s t u := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.sum_comm]

/-! ## Natural pointwise decomposition -/

/-- At `D=N`, the near-dispersion coefficient has no removed divisor term. -/
theorem ehmNearDispersionCoeff_self (N j : ℕ) :
    ehmNearDispersionCoeff N N j =
      ArithmeticFunction.vonMangoldt j / Real.log (N : ℝ) := by
  simp [ehmNearDispersionCoeff]

/-- The low product block for the natural split `D=M=N`. -/
noncomputable def ehmFiniteNaturalLowBlock
    (R1 : ℝ → ℝ) (N J : ℕ) : ℝ :=
  ehmFiniteLogTaperConvolutionBlock R1 N J 1 N 2 N

/-- The high product block for the natural split `D=M=N`. -/
noncomputable def ehmFiniteNaturalHighBlock
    (R1 : ℝ → ℝ) (N J : ℕ) : ℝ :=
  ehmFiniteNearDispersionBlock R1 N N J 1 N (N + 1) J

/-- The exact natural near/far expression after the two empty upper-`m`
rectangles have been removed. -/
noncomputable def ehmFiniteNaturalNearFarExpression
    (R1 : ℝ → ℝ) (N J : ℕ) : ℝ :=
  ehmFiniteNaturalLowBlock R1 N J +
    ehmFiniteNaturalHighBlock R1 N J +
    ehmCoupledRemainder N -
    ehmFiniteComplementaryDivisorFarOuter R1 N N J

theorem ehmFiniteNearFarDispersionExpression_self_eq_natural
    (R1 : ℝ → ℝ) (N J : ℕ) :
    ehmFiniteNearFarDispersionExpression R1 N N J N =
      ehmFiniteNaturalNearFarExpression R1 N J := by
  unfold ehmFiniteNearFarDispersionExpression
    ehmFiniteNaturalNearFarExpression
    ehmFiniteNaturalLowBlock ehmFiniteNaturalHighBlock
    ehmFiniteLogTaperConvolutionBlock ehmFiniteNearDispersionBlock
  have hempty : Finset.Icc (N + 1) N = ∅ := by
    ext m
    simp
  rw [hempty]
  simp

/-- The original finite boundary is exactly the natural four-term
decomposition whenever the common hyperbolic cutoff dominates `N`. -/
theorem ehmFiniteCoupledBoundaryExpression_eq_natural
    (R1 : ℝ → ℝ) (N J : ℕ) (hN : 2 ≤ N) (hNJ : N ≤ J) :
    ehmFiniteCoupledBoundaryExpression R1 N J =
      ehmFiniteNaturalNearFarExpression R1 N J := by
  rw [ehmFiniteCoupledBoundaryExpression_eq_nearFarDispersion
    R1 N N J N hN le_rfl le_rfl hNJ,
    ehmFiniteNearFarDispersionExpression_self_eq_natural]

/-! ## Joint low and high cutoff sums -/

/-- Low convolution block with `N` moved inside the `(m,j)` rectangle. -/
noncomputable def ehmDyadicLowJointSum
    (R1 : ℝ → ℝ) (X : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 (2 * X), ∑ j ∈ Finset.Icc 2 (2 * X),
    ∑ N ∈ ehmDyadicNBlock X,
      if m ≤ N then
        if j ≤ N then
          dirichletCoeff N m / (m : ℝ) *
            (ehmLogTaperDivisorCoeff N j * R1 ((j : ℝ) / (m : ℝ)))
        else 0
      else 0

/-- High von-Mangoldt block with `N` moved inside the `(m,j)` rectangle. -/
noncomputable def ehmDyadicHighJointSum
    (R1 : ℝ → ℝ) (X J : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 (2 * X), ∑ j ∈ Finset.Icc 2 J,
    ∑ N ∈ ehmDyadicNBlock X,
      if m ≤ N then
        if N < j then
          dirichletCoeff N m / (m : ℝ) *
            (ArithmeticFunction.vonMangoldt j / Real.log (N : ℝ) *
              R1 ((j : ℝ) / (m : ℝ)))
        else 0
      else 0

/-- Exact reindexing of the dyadic sum of natural low blocks. -/
theorem sum_ehmFiniteNaturalLowBlock_eq_joint
    (R1 : ℝ → ℝ) (X J : ℕ) :
    (∑ N ∈ ehmDyadicNBlock X, ehmFiniteNaturalLowBlock R1 N J) =
      ehmDyadicLowJointSum R1 X := by
  classical
  unfold ehmFiniteNaturalLowBlock ehmFiniteLogTaperConvolutionBlock
    ehmDyadicLowJointSum
  simp_rw [Finset.mul_sum]
  calc
    (∑ N ∈ ehmDyadicNBlock X, ∑ m ∈ Finset.Icc 1 N,
        ∑ j ∈ Finset.Icc 2 N,
          dirichletCoeff N m / (m : ℝ) *
            (ehmLogTaperDivisorCoeff N j * R1 ((j : ℝ) / (m : ℝ)))) =
      ∑ N ∈ ehmDyadicNBlock X, ∑ m ∈ Finset.Icc 1 (2 * X),
        ∑ j ∈ Finset.Icc 2 (2 * X),
          if m ≤ N then
            if j ≤ N then
              dirichletCoeff N m / (m : ℝ) *
                (ehmLogTaperDivisorCoeff N j * R1 ((j : ℝ) / (m : ℝ)))
            else 0
          else 0 := by
      apply Finset.sum_congr rfl
      intro N hNmem
      have hNU : N ≤ 2 * X := (Finset.mem_Icc.mp hNmem).2
      rw [sum_Icc_extend_upper
        (fun m => ∑ j ∈ Finset.Icc 2 N,
          dirichletCoeff N m / (m : ℝ) *
            (ehmLogTaperDivisorCoeff N j * R1 ((j : ℝ) / (m : ℝ))))
        1 N (2 * X) hNU]
      apply Finset.sum_congr rfl
      intro m _
      by_cases hmN : m ≤ N
      · simp only [hmN, if_true]
        rw [sum_Icc_extend_upper
          (fun j => dirichletCoeff N m / (m : ℝ) *
            (ehmLogTaperDivisorCoeff N j * R1 ((j : ℝ) / (m : ℝ))))
          2 N (2 * X) hNU]
      · simp [hmN]
    _ = _ := sum_comm_three
      (ehmDyadicNBlock X) (Finset.Icc 1 (2 * X))
      (Finset.Icc 2 (2 * X)) _

/-- Exact reindexing of the dyadic sum of natural high blocks. -/
theorem sum_ehmFiniteNaturalHighBlock_eq_joint
    (R1 : ℝ → ℝ) (X J : ℕ) (hX : 2 ≤ X) :
    (∑ N ∈ ehmDyadicNBlock X, ehmFiniteNaturalHighBlock R1 N J) =
      ehmDyadicHighJointSum R1 X J := by
  classical
  unfold ehmFiniteNaturalHighBlock ehmFiniteNearDispersionBlock
    ehmDyadicHighJointSum
  simp_rw [ehmNearDispersionCoeff_self, Finset.mul_sum]
  calc
    (∑ N ∈ ehmDyadicNBlock X, ∑ m ∈ Finset.Icc 1 N,
        ∑ j ∈ Finset.Icc (N + 1) J,
          dirichletCoeff N m / (m : ℝ) *
            (ArithmeticFunction.vonMangoldt j / Real.log (N : ℝ) *
              R1 ((j : ℝ) / (m : ℝ)))) =
      ∑ N ∈ ehmDyadicNBlock X, ∑ m ∈ Finset.Icc 1 (2 * X),
        ∑ j ∈ Finset.Icc 2 J,
          if m ≤ N then
            if N < j then
              dirichletCoeff N m / (m : ℝ) *
                (ArithmeticFunction.vonMangoldt j / Real.log (N : ℝ) *
                  R1 ((j : ℝ) / (m : ℝ)))
            else 0
          else 0 := by
      apply Finset.sum_congr rfl
      intro N hNmem
      have hNU : N ≤ 2 * X := (Finset.mem_Icc.mp hNmem).2
      have hN2 : 2 ≤ N := hX.trans (Finset.mem_Icc.mp hNmem).1
      rw [sum_Icc_extend_upper
        (fun m => ∑ j ∈ Finset.Icc (N + 1) J,
          dirichletCoeff N m / (m : ℝ) *
            (ArithmeticFunction.vonMangoldt j / Real.log (N : ℝ) *
              R1 ((j : ℝ) / (m : ℝ))))
        1 N (2 * X) hNU]
      apply Finset.sum_congr rfl
      intro m _
      by_cases hmN : m ≤ N
      · simp only [hmN, if_true]
        rw [sum_Icc_succ_extend_lower_two
          (fun j => dirichletCoeff N m / (m : ℝ) *
            (ArithmeticFunction.vonMangoldt j / Real.log (N : ℝ) *
              R1 ((j : ℝ) / (m : ℝ)))) N J hN2]
      · simp [hmN]
    _ = _ := sum_comm_three
      (ehmDyadicNBlock X) (Finset.Icc 1 (2 * X))
      (Finset.Icc 2 J) _

/-! ## Exposed cutoff-averaged arithmetic coefficients -/

/-- The signed cutoff average multiplying the low reciprocal kernel at the
pair `(m,j)`. -/
noncomputable def ehmDyadicLowCutoffCoeff (X m j : ℕ) : ℝ :=
  ∑ N ∈ ehmDyadicNBlock X,
    if m ≤ N then
      if j ≤ N then
        dirichletCoeff N m / (m : ℝ) * ehmLogTaperDivisorCoeff N j
      else 0
    else 0

/-- The signed cutoff average multiplying the high von-Mangoldt reciprocal
kernel at `(m,j)`. -/
noncomputable def ehmDyadicHighCutoffCoeff (X m j : ℕ) : ℝ :=
  ∑ N ∈ ehmDyadicNBlock X,
    if m ≤ N then
      if N < j then
        dirichletCoeff N m /
          ((m : ℝ) * Real.log (N : ℝ))
      else 0
    else 0

/-- The low joint sum is a reciprocal-kernel bilinear form with the entire
cutoff dependence isolated in `ehmDyadicLowCutoffCoeff`. -/
theorem ehmDyadicLowJointSum_eq_cutoffCoeff
    (R1 : ℝ → ℝ) (X : ℕ) :
    ehmDyadicLowJointSum R1 X =
      ∑ m ∈ Finset.Icc 1 (2 * X), ∑ j ∈ Finset.Icc 2 (2 * X),
        ehmDyadicLowCutoffCoeff X m j * R1 ((j : ℝ) / (m : ℝ)) := by
  classical
  unfold ehmDyadicLowJointSum ehmDyadicLowCutoffCoeff
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro N _
  by_cases hmN : m ≤ N <;> by_cases hjN : j ≤ N <;> simp [hmN, hjN] <;> ring

/-- The high joint sum is a von-Mangoldt reciprocal-kernel form with the
cutoff dependence isolated in `ehmDyadicHighCutoffCoeff`. -/
theorem ehmDyadicHighJointSum_eq_cutoffCoeff
    (R1 : ℝ → ℝ) (X J : ℕ) :
    ehmDyadicHighJointSum R1 X J =
      ∑ m ∈ Finset.Icc 1 (2 * X), ∑ j ∈ Finset.Icc 2 J,
        ArithmeticFunction.vonMangoldt j *
          ehmDyadicHighCutoffCoeff X m j *
            R1 ((j : ℝ) / (m : ℝ)) := by
  classical
  unfold ehmDyadicHighJointSum ehmDyadicHighCutoffCoeff
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro N _
  by_cases hmN : m ≤ N <;> by_cases hNj : N < j <;> simp [hmN, hNj] <;> ring

/-! ## Complete signed dyadic identity -/

/-- The entire signed dyadic finite boundary after exact cutoff reindexing.
Only the low and high main blocks are rearranged; the coupled remainder and
far subtraction remain untouched. -/
theorem sum_ehmFiniteCoupledBoundaryExpression_eq_joint
    (R1 : ℝ → ℝ) (X J : ℕ) (hX : 2 ≤ X) (hJ : 2 * X ≤ J) :
    (∑ N ∈ ehmDyadicNBlock X,
        ehmFiniteCoupledBoundaryExpression R1 N J) =
      ehmDyadicLowJointSum R1 X +
        ehmDyadicHighJointSum R1 X J +
        (∑ N ∈ ehmDyadicNBlock X, ehmCoupledRemainder N) -
        (∑ N ∈ ehmDyadicNBlock X,
          ehmFiniteComplementaryDivisorFarOuter R1 N N J) := by
  calc
    (∑ N ∈ ehmDyadicNBlock X,
        ehmFiniteCoupledBoundaryExpression R1 N J) =
      ∑ N ∈ ehmDyadicNBlock X,
        ehmFiniteNaturalNearFarExpression R1 N J := by
      apply Finset.sum_congr rfl
      intro N hNmem
      exact ehmFiniteCoupledBoundaryExpression_eq_natural R1 N J
        (hX.trans (Finset.mem_Icc.mp hNmem).1)
        ((Finset.mem_Icc.mp hNmem).2.trans hJ)
    _ = (∑ N ∈ ehmDyadicNBlock X, ehmFiniteNaturalLowBlock R1 N J) +
        (∑ N ∈ ehmDyadicNBlock X, ehmFiniteNaturalHighBlock R1 N J) +
        (∑ N ∈ ehmDyadicNBlock X, ehmCoupledRemainder N) -
        (∑ N ∈ ehmDyadicNBlock X,
          ehmFiniteComplementaryDivisorFarOuter R1 N N J) := by
      unfold ehmFiniteNaturalNearFarExpression
      simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ = _ := by
      rw [sum_ehmFiniteNaturalLowBlock_eq_joint,
        sum_ehmFiniteNaturalHighBlock_eq_joint R1 X J hX]

/-- The complete cutoff-averaged identity with both arithmetic coefficients
exposed.  This is the exact finite target for Priority 2: cancellation must be
proved in the two displayed signed coefficient kernels together with the
coupled remainder and complementary far subtraction. -/
theorem sum_ehmFiniteCoupledBoundaryExpression_eq_cutoffCoeff
    (R1 : ℝ → ℝ) (X J : ℕ) (hX : 2 ≤ X) (hJ : 2 * X ≤ J) :
    (∑ N ∈ ehmDyadicNBlock X,
        ehmFiniteCoupledBoundaryExpression R1 N J) =
      (∑ m ∈ Finset.Icc 1 (2 * X), ∑ j ∈ Finset.Icc 2 (2 * X),
        ehmDyadicLowCutoffCoeff X m j * R1 ((j : ℝ) / (m : ℝ))) +
      (∑ m ∈ Finset.Icc 1 (2 * X), ∑ j ∈ Finset.Icc 2 J,
        ArithmeticFunction.vonMangoldt j *
          ehmDyadicHighCutoffCoeff X m j * R1 ((j : ℝ) / (m : ℝ))) +
      (∑ N ∈ ehmDyadicNBlock X, ehmCoupledRemainder N) -
      (∑ N ∈ ehmDyadicNBlock X,
        ehmFiniteComplementaryDivisorFarOuter R1 N N J) := by
  rw [sum_ehmFiniteCoupledBoundaryExpression_eq_joint R1 X J hX hJ,
    ehmDyadicLowJointSum_eq_cutoffCoeff,
    ehmDyadicHighJointSum_eq_cutoffCoeff]

end RH.Criteria.NymanBeurling.BCFLogTaperEhmCutoffAverageReindex
