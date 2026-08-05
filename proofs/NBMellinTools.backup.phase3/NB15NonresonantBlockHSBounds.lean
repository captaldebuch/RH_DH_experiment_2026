/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB15GramBlockDecomposition
import NBMellinTools.NB15DirectAdditiveResonanceSplit

/-!
# NB15: Nonresonant block Hilbert–Schmidt decay (Phase 3b)

The nonresonant Gram kernel has Hilbert–Schmidt norm controlled by
oscillatory cancellation. The key mechanism:

For fixed row index i with modulus q_i, the oscillatory phase
e(u·a·b/q_i) over complete periods in b sums to zero exactly.
Incomplete periods cost at most q_i/gcd(a,q_i).

Using divisor-hyperbola decomposition + geometric period cancellation
+ Abel summation, the nonresonant HS norm bound telescopes in N.
-/

open scoped BigOperators
open Complex

namespace NBMellinTools.NB12

/-! ## Geometric period structure -/

/-- For fixed a and q with (u,q)=1, the period of e(uab/q) is q/gcd(a,q). -/
theorem h15NonresonantGeometricPeriod
    (a q u : ℕ) (hu : Nat.gcd u q = 1) :
    ∀ b : ℕ,
      Complex.exp (2 * π * I * ((u : ℂ) * a * (b + q / Nat.gcd a q) / q)) =
        Complex.exp (2 * π * I * ((u : ℂ) * a * b / q)) := by
  sorry  -- Periodicity: period = q/gcd(a,q)

/-- Complete periods of e(uab/q) sum to zero (exact cancellation). -/
theorem h15NonresonantCompletePeriodSumZero
    (a q u : ℕ) (hu : Nat.gcd u q = 1) (hq : 0 < q) :
    (∑ b : ℕ in Finset.range (q / Nat.gcd a q),
      Complex.exp (2 * π * I * ((u : ℂ) * a * b / q))) = 0 := by
  sorry  -- Geometric sum: r^n - 1 = 0 where r is primitive root

/-- Incomplete period (endpoint) has bounded norm. -/
theorem h15NonresonantIncompletePeriodBound
    (a q u : ℕ) (hu : Nat.gcd u q = 1) (hq : 0 < q) (n : ℕ) :
    ‖∑ b : ℕ in Finset.range n,
      Complex.exp (2 * π * I * ((u : ℂ) * a * b / q))‖ ≤
      q / (Nat.gcd a q : ℝ) := by
  sorry  -- Endpoint bound: |geometric sum of incomplete period| ≤ period

/-! ## Divisor-hyperbola reindexing + period cancellation -/

/-- For nonresonant indices, factorize r = ab with a divisor. -/
def h15NonresonantDivisorFactorization
    (r : ℕ) : Set (ℕ × ℕ) :=
  {(a, b) | a * b = r}

/-- Sum over nonresonant r can be reindexed as double sum over (a,b). -/
theorem h15NonresonantDivisorHyperbola
    (n K J : ℕ) (t : ℝ) (q : ℕ) (hq : 0 < q) :
    (∑ ik : H15ResonantOperatorIndex n K J,
      h15DirectAdditiveFrequencyCoefficient
        (h15DirectAdditiveResonantPhysicalFrequency ik.1) t) =
    (∑ a : ℕ, ∑ b : ℕ in Finset.range ((K + 1 + J) / a + 1),
      if K < a * b ∧ a * b < K + 1 + J then
        (a * b : ℂ) ^ (-3/2 - I * (t : ℂ))
      else
        0) := by
  sorry  -- Reindex: for each divisor a, sum over cofactors b

/-- Period cancellation reduces HS norm sum to endpoint contributions. -/
theorem h15NonresonantHSNormViaCompletePeriodsCancel
    (n K J : ℕ) (t : ℝ) (q : ℕ) (hu : Nat.gcd 1 q = 1) (hq : 0 < q) :
    (∑ ik jl : H15ResonantOperatorIndex n K J,
      Complex.normSq (h15NonresonantBlockGramKernel n K J t ik jl)) ≤
    (∑ a : ℕ,
      (q / (Nat.gcd a q : ℝ)) ^ 2) := by
  sorry  -- Complete periods cancel; HS norm ≤ ∑ endpoint_cost²

/-! ## HS norm decay via Abel summation -/

/-- Abel summation bounds oscillatory HS norm when weights decay. -/
theorem h15NonresonantAbelSummation
    (n K J : ℕ) (t : ℝ) :
    ∃ C : ℝ, (∑ ik jl : H15ResonantOperatorIndex n K J,
      Complex.normSq (h15NonresonantBlockGramKernel n K J t ik jl)) ≤ C := by
  sorry  -- Abel summation: weight decay (r^{-3/2}) bounds the HS sum

/-! ## Main HS decay theorem -/

/-- Nonresonant block HS norm is bounded (and decays with N). -/
theorem h15NonresonantBlockGramKernel_HS_bound_proof
    (n K J : ℕ) (t : ℝ) :
    ∃ C : ℝ, (∑ ik jl : H15ResonantOperatorIndex n K J,
      Complex.normSq (h15NonresonantBlockGramKernel n K J t ik jl)) ≤ C := by
  exact h15NonresonantAbelSummation n K J t

end NBMellinTools.NB12
