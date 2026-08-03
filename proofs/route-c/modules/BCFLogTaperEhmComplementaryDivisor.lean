import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmBoundaryResearch

/-!
# Complementary-divisor hyperbola for the Ehm boundary

The completed-divisor reduction leaves a signed correction supported on
divisors `d > N`.  This module reindexes that correction as the complementary
finite hyperbolic sector `N < d` and `d * q ≤ J`.

The result is an exact finite identity.  In particular, it does not estimate
the complementary sector termwise and therefore does not discard the Möbius
and log-taper signs needed by the remaining H15 cancellation problem.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmComplementaryDivisor

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmBoundaryResearch
open RH.Criteria.NymanBeurling.BCFLogTaperEhmUniformBoundary

/-- The omitted-divisor correction written directly as the complementary
hyperbolic sector `N < d` and `d*q ≤ J`. -/
noncomputable def ehmFiniteComplementaryDivisorHyperbolicSum
    (R1 : ℝ → ℝ) (N J : ℕ) (x : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc (N + 1) J, ∑ q ∈ Finset.Icc 1 J,
    if d * q ≤ J then
      dirichletCoeff N d * R1 (((d * q : ℕ) : ℝ) * x)
    else 0

/-- Multiplication by `d > N` identifies a complementary hyperbolic row
with the multiples of `d` in `[N+1,J]`. -/
private theorem complementaryHyperbolicRow_eq_divisibleRow
    (f : ℕ → ℝ) (N d J : ℕ) (hNd : N < d) :
    (∑ q ∈ Finset.Icc 1 J, if d * q ≤ J then f (d * q) else 0) =
      ∑ j ∈ Finset.Icc (N + 1) J, if d ∣ j then f j else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_bij (fun q _ => d * q)
  · intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hqIcc, hdqJ⟩
    rcases Finset.mem_Icc.mp hqIcc with ⟨hq1, _⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_Icc.mpr
      constructor
      · have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq1
        have hdle : d ≤ d * q := by
          simpa using Nat.mul_le_mul_left d hq1
        omega
      · exact hdqJ
    · exact dvd_mul_right d q
  · intro a _ b _ hab
    exact Nat.mul_left_cancel (by omega) hab
  · intro j hj
    rcases Finset.mem_filter.mp hj with ⟨hjIcc, hdj⟩
    rcases Finset.mem_Icc.mp hjIcc with ⟨hjlo, hjJ⟩
    refine ⟨j / d, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_Icc.mpr
        constructor
        · exact Nat.div_pos (Nat.le_of_dvd (by omega) hdj) (by omega)
        · exact (Nat.div_le_self j d).trans hjJ
      · rw [Nat.mul_div_cancel' hdj]
        exact hjJ
    · exact Nat.mul_div_cancel' hdj
  · intro q _
    rfl

/-- For `j ≤ J`, the divisors of `j` exceeding `N` are exactly the
divisible indices in `[N+1,J]`. -/
private theorem complementaryDivisors_filter_eq
    (N J j : ℕ) (hjpos : 0 < j) (hjJ : j ≤ J) :
    (Finset.Icc (N + 1) J).filter (fun d => d ∣ j) =
      j.divisors.filter (fun d => N < d) := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hdlo, hdJ⟩, hdj⟩
    exact ⟨⟨hdj, Nat.ne_of_gt hjpos⟩, by omega⟩
  · rintro ⟨⟨hdj, _⟩, hNd⟩
    have hdjle : d ≤ j := Nat.le_of_dvd hjpos hdj
    exact ⟨⟨by omega, hdjle.trans hjJ⟩, hdj⟩

/-- Exact complementary-divisor reindexing of the missing tail. -/
theorem ehmFiniteMissingDivisorTail_eq_complementaryHyperbolic
    (R1 : ℝ → ℝ) (N J : ℕ) (x : ℝ) :
    ehmFiniteMissingDivisorTail R1 N J x =
      ehmFiniteComplementaryDivisorHyperbolicSum R1 N J x := by
  classical
  unfold ehmFiniteMissingDivisorTail
    ehmFiniteComplementaryDivisorHyperbolicSum
  calc
    (∑ j ∈ Finset.Icc (N + 1) J,
        ehmLogTaperMissingDivisorCoeff N j * R1 ((j : ℝ) * x)) =
        ∑ j ∈ Finset.Icc (N + 1) J,
          ∑ d ∈ Finset.Icc (N + 1) J,
            if d ∣ j then
              dirichletCoeff N d * R1 ((j : ℝ) * x)
            else 0 := by
      apply Finset.sum_congr rfl
      intro j hjmem
      have hjpos : 0 < j := by
        have := (Finset.mem_Icc.mp hjmem).1
        omega
      have hjJ : j ≤ J := (Finset.mem_Icc.mp hjmem).2
      rw [← Finset.sum_filter,
        complementaryDivisors_filter_eq N J j hjpos hjJ]
      unfold ehmLogTaperMissingDivisorCoeff
      rw [Finset.sum_mul, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d _
      by_cases hNd : N < d <;> simp [hNd]
    _ = ∑ d ∈ Finset.Icc (N + 1) J,
          ∑ j ∈ Finset.Icc (N + 1) J,
            if d ∣ j then
              dirichletCoeff N d * R1 ((j : ℝ) * x)
            else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ Finset.Icc (N + 1) J,
          ∑ q ∈ Finset.Icc 1 J,
            if d * q ≤ J then
              dirichletCoeff N d * R1 (((d * q : ℕ) : ℝ) * x)
            else 0 := by
      apply Finset.sum_congr rfl
      intro d hdmem
      have hNd : N < d := by
        have := (Finset.mem_Icc.mp hdmem).1
        omega
      exact (complementaryHyperbolicRow_eq_divisibleRow
        (fun j => dirichletCoeff N d * R1 ((j : ℝ) * x))
        N d J hNd).symm

/-- Outer BCF sum of the complementary hyperbolic sector. -/
noncomputable def ehmFiniteComplementaryDivisorHyperbolicOuter
    (R1 : ℝ → ℝ) (N J : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, dirichletCoeff N m / (m : ℝ) *
    ehmFiniteComplementaryDivisorHyperbolicSum
      R1 N J (1 / (m : ℝ))

/-- The missing-divisor outer correction is exactly the complementary
hyperbolic sector inserted into the outer BCF sum. -/
theorem ehmFiniteMissingDivisorTailOuter_eq_complementaryHyperbolicOuter
    (R1 : ℝ → ℝ) (N J : ℕ) :
    ehmFiniteMissingDivisorTailOuter R1 N J =
      ehmFiniteComplementaryDivisorHyperbolicOuter R1 N J := by
  classical
  unfold ehmFiniteMissingDivisorTailOuter
    ehmFiniteComplementaryDivisorHyperbolicOuter
  apply Finset.sum_congr rfl
  intro m _
  rw [ehmFiniteMissingDivisorTail_eq_complementaryHyperbolic]

/-- The completed finite boundary expressed as a full von Mangoldt
transform minus the complementary hyperbolic sector, with the linear moment
remainder still coupled under the same sign pattern. -/
theorem ehmFiniteCoupledBoundaryExpression_eq_fullOuter_sub_complementary_add_remainder
    (R1 : ℝ → ℝ) (N J : ℕ) (hN : 2 ≤ N) (hNJ : N ≤ J) :
    ehmFiniteCoupledBoundaryExpression R1 N J =
      ehmFiniteFullVonMangoldtTransformOuter R1 N J -
        ehmFiniteComplementaryDivisorHyperbolicOuter R1 N J +
          ehmCoupledRemainder N := by
  rw [ehmFiniteCoupledBoundaryExpression_eq_fullOuter_sub_missing_add_remainder
    R1 N J hN hNJ,
    ehmFiniteMissingDivisorTailOuter_eq_complementaryHyperbolicOuter]

end RH.Criteria.NymanBeurling.BCFLogTaperEhmComplementaryDivisor
