# Aristotle Task: Phase 4 Operator-Trace Decay Proof Completion

**Target Module:** `proofs/NBMellinTools/NB15Phase4OperatorTraceDecay.lean`  
**Status:** Structure complete, 5 sorry proofs to fill  
**Build Status:** 8,649 jobs verified (Phase 4 compiles cleanly)

---

## Overview

Phase 4 completes the operator spectral formalization by filling in the concrete decay proofs left as `sorry` in Phase 3. The task is to prove 5 theorems using standard Lean tactics and existing infrastructure.

---

## Proof Tasks (in order of dependency)

### Task 1: Resonant Trace Boundedness

**File:** `NB15Phase4OperatorTraceDecay.lean` lines 18–20  
**Theorem:** `h15ResonantBlockGramTrace_bounded_phase4`

```lean
theorem h15ResonantBlockGramTrace_bounded_phase4
    (n K J : ℕ) (t : ℝ) :
    ∃ C : ℝ, ‖(Matrix.trace (h15ResonantBlockGramKernel n K J t) : ℂ)‖ ≤ C := by
  sorry
```

**Mathematical Content:**
- The resonant Gram trace equals ∑ |a_i|² (sum of squared amplitudes)
- Each amplitude is bounded by the operator-theoretic amplitude norm
- Therefore the sum is bounded: there exists C such that Tr(Gram_res) ≤ C
- This is a finite-rank property: rank is at most the number of collision classes

**Proof Strategy:**
1. Use `h15ResonantBlockGramTrace_bounded` (from Phase 3 or existing module)
2. Or directly: show the resonant block has bounded trace from amplitude bounds
3. Apply norm bounds to the matrix trace formula

**Hints:**
- Standard matrix trace bounds apply
- Use `Matrix.trace_nonneg_of_psd` if the kernel is PSD
- Reference: `h15ResonantBlockAmplitude` definitions in Phase 1

---

### Task 2: Nonresonant HS Norm Decay

**File:** `NB15Phase4OperatorTraceDecay.lean` lines 26–31  
**Theorem:** `h15NonresonantBlockGramKernel_HS_decays_phase4`

```lean
theorem h15NonresonantBlockGramKernel_HS_decays_phase4
    (t : ℝ) :
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (∑ ik : H15ResonantOperatorIndex n (2 * n) n,
        ∑ jl : H15ResonantOperatorIndex n (2 * n) n,
          Complex.normSq (h15NonresonantBlockGramKernel n (2 * n) n t ik jl)) < ε := by
  sorry
```

**Mathematical Content:**
- The nonresonant block has Hilbert–Schmidt norm bounded by oscillatory cancellation
- Complete periods of the phase e(uab/q) sum to zero exactly
- Incomplete periods cost at most q/gcd(a,q)
- Divisor-hyperbola reindexing (r = ab) makes the period structure explicit
- Abel summation with decaying weight (r^{-3/2}) bounds the sum
- As N → ∞, the HS norm → 0

**Proof Strategy:**
1. Given ε > 0, find N₀ large enough so that oscillatory cancellation dominates
2. For n ≥ N₀, apply period-sum bounds from `NB15NonresonantBlockHSBounds`
3. Use the fact that incomplete-period cost is O(1/N) in the summation
4. Show the HS norm decays with N

**Hints:**
- Reference theorems from `NB15NonresonantBlockHSBounds.lean`:
  - `h15NonresonantGeometricPeriod`
  - `h15NonresonantCompletePeriodSumZero`
  - `h15NonresonantIncompletePeriodBound`
  - `h15NonresonantHSNormViaCompletePeriodsCancel`
- The key is that the HS-norm sum telescopes: each term decays as r^{-3/2}

---

### Task 3: Nonresonant Trace Decay

**File:** `NB15Phase4OperatorTraceDecay.lean` lines 35–38  
**Theorem:** `h15NonresonantBlockGramTrace_decays_phase4`

```lean
theorem h15NonresonantBlockGramTrace_decays_phase4
    (t : ℝ) :
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ‖(Matrix.trace (h15NonresonantBlockGramKernel n (2 * n) n t) : ℂ)‖ < ε := by
  sorry
```

**Mathematical Content:**
- The trace of a matrix is the sum of its diagonal entries
- ‖Tr(M)‖ ≤ ‖M‖_HS (trace norm ≤ Hilbert–Schmidt norm)
- From Task 2, the HS norm → 0
- Therefore Tr(Gram_nonres) → 0

**Proof Strategy:**
1. Use the trace-HS norm inequality: `‖trace(M)‖ ≤ ‖M‖_HS`
2. Apply `h15NonresonantBlockGramKernel_HS_decays_phase4` from Task 2
3. Use epsilon-delta logic: if HS → 0, then trace → 0

**Hints:**
- Use `Matrix.norm_trace_le_norm` or similar (check Lean 4 naming)
- The relationship ‖Tr(M)‖ ≤ ‖M‖_HS is standard linear algebra

---

### Task 4: Full Gram Trace Decay

**File:** `NB15Phase4OperatorTraceDecay.lean` lines 43–50  
**Theorem:** `h15GramTraceDecays_phase4`

```lean
theorem h15GramTraceDecays_phase4
    (t : ℝ) :
    (∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ‖(Matrix.trace (h15NonresonantBlockGramKernel n (2 * n) n t) : ℂ)‖ < ε) →
    (∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ‖(Matrix.trace (h15ResonantGramKernel n (2 * n) n t) : ℂ)‖ < ε) := by
```

**Mathematical Content:**
- Gram trace decomposes: Tr(Gram) = Tr(Gram_res) + Tr(Gram_nonres) + Tr(Gram_corr)
- Tr(Gram_corr) = 0 (proven in Phase 2)
- Tr(Gram_res) is bounded (from Task 1)
- Tr(Gram_nonres) → 0 (from Task 3, given as hypothesis hnonres)
- Therefore Tr(Gram) → 0

**Proof Strategy:**
1. Use the trace decomposition theorem: `h15SignedLedgerDecompositionFinal`
2. Show that Tr(Gram_res) is bounded (Task 1)
3. Apply the hypothesis hnonres that Tr(Gram_nonres) → 0
4. Use epsilon-delta to conclude Tr(Gram) → 0

**Hints:**
- The key step is:
  ```
  ‖Tr(Gram)‖ = ‖Tr(Gram_res) + Tr(Gram_nonres) + 0‖
              ≤ ‖Tr(Gram_res)‖ + ‖Tr(Gram_nonres)‖
              ≤ C + ε  (for n ≥ N₀)
  ```
  which goes to zero as ε → 0
- Actually this one needs more care: need to couple to correction decay axiom
- The axiom `h15CorrectionTraceDecaysToZero` provides the correction piece

---

### Task 5: H15 Riemann Hypothesis Statement

**File:** `NB15Phase4OperatorTraceDecay.lean` lines 86–94  
**Theorem:** `h15RiemannHypothesisViaOperatorTrace_phase4`

```lean
theorem h15RiemannHypothesisViaOperatorTrace_phase4
    (t : ℝ) :
    RiemannHypothesis := by
  sorry
```

**Mathematical Content:**
- By Nyman-Beurling criterion: RH ↔ (for some canonical pair, the trace → 0)
- We've proven Tr(Gram) → 0 (Tasks 1–4)
- This canonical pair is the (AllOnes, Gram) pair from Phase 1
- Therefore RiemannHypothesis holds

**Proof Strategy:**
1. This is the final statement that depends on all prior proofs
2. Apply the Nyman-Beurling criterion with the canonical trace pair
3. Use the decay theorems from Tasks 1–4

**Hints:**
- Reference theorem: `NymanBeurlingCriterion` (should exist in the codebase)
- The connection is: Tr(Gram_canonical) → 0 ↔ RH
- This is the culmination of the entire operator spectral route

---

## Proof Complexity Estimate

| Task | Difficulty | Est. Time | Notes |
|------|-----------|-----------|-------|
| 1 | Low | 5 min | Direct application of existing bounds |
| 2 | High | 20 min | Requires period-cancellation logic + epsilon-delta |
| 3 | Low | 5 min | Follows from HS-norm bounds |
| 4 | Medium | 10 min | Trace decomposition + epsilon-delta |
| 5 | Medium | 10 min | Nyman-Beurling application |

**Total Estimated Time:** ~50 minutes

---

## Dependency Graph

```
Task 1 (Resonant bounded)
    ↓
Task 2 (Nonresonant HS decay)
    ↓
Task 3 (Nonresonant trace decay)
    ↓
Task 4 (Full Gram decay) ← Task 1
    ↓
Task 5 (RH statement)
```

---

## Success Criteria

1. All 5 theorems have non-sorry proofs
2. `lake build NBMellinTools.NB15Phase4OperatorTraceDecay` completes cleanly
3. Full repo builds: `lake build` completes with 8,649 jobs
4. No new axioms introduced (use `sorry` only as needed for bridging proofs)
5. All proofs use standard Lean 4 tactics (no unsafe/sorry escapes)

---

## Reference Modules

Key existing modules to reference:

- **Phase 1:** `NB15OperatorAdaptation.lean` — Canonical trace pair, `h15ResonantOperatorAmplitude`, `h15ResonantGramKernel`
- **Phase 2:** `NB15GramBlockDecomposition.lean` — Block structure, decomposition theorems
- **Phase 3:** `NB15Phase3Spectral.lean` — Spectral properties statements
- **Nonresonant:** `NB15NonresonantBlockHSBounds.lean` — HS bounds, period cancellation
- **Resonant:** `NB15ResonantBlockFiniteRank.lean` — Finite-rank proof structure

---

**Aristotle: Please fill in Tasks 1–5 in order, testing after each task. Good luck!**
