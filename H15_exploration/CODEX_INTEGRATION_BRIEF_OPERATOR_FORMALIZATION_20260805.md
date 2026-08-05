# Codex Integration Brief: H15 Operator Formalization (Path A)
**Date:** 2026-08-05  
**Status:** Ready for implementation  
**Foundation:** Aristotle's five verified Lean modules  
**Timeline:** 2–3 weeks to isolated RH-strength gate

---

## Strategy: Build on Aristotle's Verified Foundation

Aristotle has formalized the **operator-trace mathematics** in five clean, verified Lean modules. Your task is to **adapt, integrate, and extend** these modules to the H15-specific types and complete the block decomposition.

**Key principle:** Do NOT rewrite what Aristotle proved. Adapt and build upward.

---

## Aristotle's Foundation (What You're Starting With)

### Module 1: `OperatorTrace.lean` (Core Trace Identities)
**Provides:**
- `dirichletConv_eq_trace`: Dirichlet convolution is a trace on collision lattice
- `collisionKernel_eq_gram`: Collision kernel is `A^H A` (nonnegative)
- `collisionSum_eq_trace`: Collision sum equals `Tr(A^H A · E)` with E rank-1
- `collisionSum_eq_sum_normSq`: Sum of squared norms form
- `collisionSum_nonneg`: Nonnegativity via Gram structure
- `H15Sum_eq_trace`, `H15Sum_split`: H15 sum as trace and block split
- `rank_rowBlock_le`: Finite-rank factorization with rank bound

**You will:** Map H15 indices `(q, d, r, u)` to the collision lattice; prove the H15 kernel specializes to this structure.

---

### Module 2: `CharacterSpectrum.lean` (Character Sums as Spectra)
**Provides:**
- `circulant_mulVec_ech`: Eigenvector property for circulant operators
- `dft_mul_conjTranspose`: `F F^† = q · I` (Parseval identity)
- `dft_mul_circulant`: Spectral decomposition `F C_a = diagonal(λ) F`
- Sum of eigenvalues = `Tr(C_a) = q · a(0)`
- Determinant as product of eigenvalues

**You will:** Connect H15's additive phase `e(ur/q)` to character eigenvalues; use spectral decomposition to understand oscillatory cancellation.

---

### Module 3: `MobiusMatrix.lean` (Möbius Inversion as Operator)
**Provides:**
- `M Z = I` and `Z M = I`: Möbius and zeta matrices are inverses
- Invertibility theorems
- Vector form of Möbius inversion: `M · (Z v) = v`
- Trace theorems: `Tr(M) = τ(n)`, `Tr(Z) = τ(n)`

**You will:** Ground H15's Möbius weights `μ(d)` in the operator formalism; prove the weight structure is consistent with Möbius invertibility.

---

### Module 4: `FredholmTrace.lean` (Trace Bounds & Perturbations)
**Provides:**
- `trace_eq_sum_normSq`: `Tr(A^H A) = ∑ ‖A_ij‖²`
- `HS_norm_def`: Hilbert–Schmidt norm as sum of squared singular values
- `trace_cauchySchwarz`: `‖Tr(A^H B)‖ ≤ ‖A‖_HS · ‖B‖_HS`
- `det_I_plus_rank1`: `det(I + K) = 1 + Tr(K)` for rank-1 K
- Bounds on perturbations supported on small sets

**You will:** Use Fredholm machinery to bound the correction perturbation; prove trace convergence from HS norm convergence.

---

### Module 5: `H15Resonance.lean` (Resonance Collapse & Exact Annihilation)
**Provides:**
- Summing `u` over complete residue system annihilates nonresonant indices exactly
- `resonant_sum = ∑_{q|r} q · μ(d) · w`
- Resonant sum equals trace of resonant block
- `rank_resonant ≤ number of resonant indices`

**You will:** Extend this to prove the nonresonant block is Hilbert–Schmidt; connect annihilation to period cancellation.

---

## Your Integration Tasks (5 Phases)

### Phase 1: Index Adaptation & Kernel Specialization
**Goal:** Map H15 active indices to Aristotle's collision structure

**File:** `NB15OperatorAdaption.lean`

**Tasks:**
1. Define `H15OperatorIndex := {(i, r) : H15LaurentRowIndex N × ℕ // i ∈ active_set}`
2. Instantiate Aristotle's collision lattice for H15 indices
3. Define H15-specific kernel:
   ```lean
   def h15OperatorKernel (ξ η : H15OperatorIndex) : ℂ :=
     μ(d_ξ).conj * μ(d_η) * 
     w_N(i_ξ) * w_N(i_η) *
     h15DirectAdditiveReducedUnitPhase(.positive) r_ξ u_ξ q_ξ *
     conj(h15DirectAdditiveReducedUnitPhase(.negative) r_η u_η q_η) *
     h15DirectAdditiveFrequencyCoefficient(r_ξ, t) *
     conj(h15DirectAdditiveFrequencyCoefficient(r_η, t))
   ```
4. **Prove:** `h15OperatorKernel` specializes to Aristotle's `collisionKernel` when restricted to resonant indices

**Stop Test 1 (Kernel Uniqueness):**
- Prove the kernel is uniquely determined by H15 weights, phases, and coefficients
- If the kernel cannot be written uniquely, vacuity test fails → abort

**Timeline:** 3–4 days

---

### Phase 2: Operator Definition & Trace Identity
**Goal:** Define the operator and prove exact trace identity

**File:** `NB15TransferOperator.lean`

**Tasks:**
1. Define the linear map:
   ```lean
   def h15TransferOperator (n K J : ℕ) (t : ℝ) : 
       LinearMap ℂ (lp 2 (fun _ : H15OperatorIndex n => ℂ))
   ```
2. Apply Aristotle's `OperatorTrace.H15Sum_eq_trace` to prove:
   ```lean
   theorem h15SignedLedger_eq_trace (n K J : ℕ) (T : ℝ) :
     h15SignedLedger n K J T = Tr(h15TransferOperator n K J T)
   ```
3. Break down the trace identity:
   ```lean
   theorem trace_decomposition :
     Tr(T_N) = Tr(R_N) + Tr(O_N) + Tr(C_N)
   ```
   where R, O, C are resonant, oscillatory, correction blocks

**Stop Test 1 (Kernel Uniqueness):** 
- Verify the kernel is determined uniquely by the trace identity
- If two kernels give the same trace, vacuity test fails

**Timeline:** 3–4 days

---

### Phase 3: Resonant Block Finalization
**Goal:** Prove resonant block is finite-rank and compute its trace

**File:** `NB15ResonantBlockOperator.lean`

**Tasks:**
1. Define resonant subspace:
   ```lean
   def resonantIndices : Finset (H15OperatorIndex n) :=
     h15BettinChandeeResonantMiddleSupport n K J
   ```
2. Apply `NB15DirectAdditiveResonantQuotient.lean` (WP1j) to prove phase collapses to `1 + cos(πs)` on this block
3. Use Aristotle's `collisionKernel_eq_gram` to show resonant block is `A^H A` on the collision graph:
   ```lean
   theorem resonantBlock_eq_gram :
     (R_N : Matrix _ _ ℂ) = A^H * A
     where A is the incidence matrix of collision relation qk = q'ℓ
   ```
4. Apply `collisionSum_eq_sum_normSq` to get:
   ```lean
   Tr(R_N) = ∑_k ‖∑_{collision_class k} entry‖²
   ```
5. Connect to `NB15DirectAdditiveResonantFixedHeight.lean` (WP1k) collision ledger:
   ```lean
   theorem resonantTrace_eq_collisionLedger :
     Tr(R_N) = h15BettinChandeeResonantQuotientDiagonal + 
               h15BettinChandeeResonantQuotientCollisionOffDiagonal
   ```

**Stop Test 2 (Resonant Finite-Rank):**
- Prove `rank(R_N) ≤ numberOfCollisionClasses`
- If rank is unbounded, the decomposition fails

**Timeline:** 2–3 days

---

### Phase 4: Non-Resonant Block Analysis
**Goal:** Prove non-resonant block is Hilbert–Schmidt with decaying norm

**File:** `NB15NonResonantBlockOperator.lean`

**Tasks:**
1. Define non-resonant subspace:
   ```lean
   def nonResonantIndices : Finset (H15OperatorIndex n) :=
     h15BettinChandeeNonresonantMiddleSupport n K J
   ```
2. Extract phase oscillation property from `NB15DirectAdditiveResonanceSplit.lean`:
   ```lean
   theorem nonResonantPhaseOscillates :
     ∀ ξ ∈ nonResonantIndices,
       h15DirectAdditiveReducedUnitPhase(.positive) r_ξ u_ξ q_ξ ≠ 1 ∧
       h15DirectAdditiveReducedUnitPhase(.negative) r_ξ u_ξ q_ξ ≠ 1
   ```
3. Apply Aristotle's `trace_cauchySchwarz` to bound off-diagonal entries:
   ```lean
   theorem nonResonantOffDiagonal_HS_bound :
     ∑_{ξ,η ∈ nonResonantIndices, ξ ≠ η} 
       ‖h15OperatorKernel ξ η‖² ≤ geom_series(decay_rate)
   ```
4. Use divisor-hyperbola structure + geometric period cancellation:
   - For fixed `a`, the period of `e(uab/q)` is `q/gcd(a,q)`
   - Complete periods cancel exactly
   - Incomplete endpoints cost at most `q/gcd(a,q)`
   - Apply Aristotle's Fredholm machinery to bound perturbations

**Stop Test 3 (Non-Resonant HS Decay):**
- Prove `‖O_N‖_HS → 0` as N → ∞
- If HS norm doesn't decay, the oscillatory block cannot be isolated

**Timeline:** 5–7 days (most complex; uses period cancellation + geometric series)

---

### Phase 5: Correction Block & Spectral Decay
**Goal:** Isolate correction block as low-rank perturbation; prove trace convergence

**File:** `NB15CorrectionBlockOperator.lean` + `NB15SpectralDecay.lean`

**Tasks:**
1. Define correction subspace (low-frequency + endpoint indices):
   ```lean
   def correctionIndices : Finset (H15OperatorIndex n) :=
     lowFrequencyIndices ∪ endpointParameterIndices
   ```
2. Apply Aristotle's rank-1 Fredholm formula:
   ```lean
   theorem correctionBlockRank :
     rank(C_N) ≤ |{active q}| = O(N^{3/4+η})
   ```
3. Use Aristotle's perturbation bounds:
   ```lean
   theorem correctionTraceBound :
     ‖Tr(C_N)‖ ≤ ‖C_N‖_HS * cardinality_bound
   ```
4. **Assemble final spectral decay theorem:**
   ```lean
   theorem h15SpectralDecay :
     Tr(T_N) = Tr(R_N) + Tr(O_N) + Tr(C_N)
     where:
       Tr(R_N) is finite (arithmetic sum, no decay)
       Tr(O_N) → 0 (HS norm → 0)
       Tr(C_N) → 0 is the RH-strength gate (hypothesis, not yet proved)
   ```

**Stop Test 4 (Correction Low-Rank):**
- Verify `rank(C_N) ≤ O(N^{3/4+η})`
- If correction is full-rank, isolation fails

**The Final Open Problem:**
- **Hypothesis:** `Tr(C_N) → 0` (correction decay)
- This is the RH-strength gate, now isolated as a single low-rank property
- If true, H15 is proved
- If false, the correction couples to something we haven't captured

**Timeline:** 4–5 days

---

## Build Pipeline

```
Week 1:
  Phase 1 (Kernel adaptation)      [3–4 days]
  Phase 2 (Operator definition)    [3–4 days]
  Checkpoint: lake build ✓, trace identity proved ✓

Week 2:
  Phase 3 (Resonant block)         [2–3 days]
  Phase 4 (Non-resonant block)     [5–7 days, most complex]
  Checkpoint: lake build ✓, both blocks decomposed ✓

Week 3:
  Phase 5a (Correction block)      [2–3 days]
  Phase 5b (Spectral decay)        [2–3 days]
  Final: lake build ✓, correction decay isolated as RH gate ✓
```

---

## Stop Tests & Contingency

| Test | Phase | What Happens If It Fails |
|------|-------|--------------------------|
| **Kernel uniqueness** | 2 | Operator identity is vacuous; abort operator approach, fall back to divisor-hyperbola (1-week delay) |
| **Resonant finite-rank** | 3 | Resonant block is not a finite sum; decomposition fails; abort (1-week delay) |
| **Non-resonant HS decay** | 4 | Oscillatory block norm doesn't converge; abort operator approach (2-3 week delay, switch to classical bounds) |
| **Correction low-rank** | 5 | Correction is full-rank; gate isolation fails; abort (2-3 week delay) |

---

## Aristotle's Modules: Usage Guide

### What You Can Use Directly
- All five modules compile and verify
- `dirichletConv_eq_trace`, `collisionSum_eq_trace` are drop-in lemmas
- `rank_rowBlock_le` gives rank bounds immediately
- `trace_cauchySchwarz` applies to H15 indices after adaptation

### What You Need to Adapt
- Index types: Aristotle uses generic types; rewrite for H15 indices
- Kernel definitions: Aristotle has abstract `K`; specialize to H15 phases + weights
- Block decomposition: Aristotle has abstract blocks; specialize to resonant/nonresonant/correction

### What Aristotle Did NOT Do
- Did NOT prove nonresonant HS norm → 0 (only structure)
- Did NOT connect period cancellation to Hilbert–Schmidt (your task)
- Did NOT prove correction trace → 0 (leaves as hypothesis)

---

## Files to Create (Codex's New Modules)

1. **`NB15OperatorAdaption.lean`** — H15 indices, kernel specialization
2. **`NB15TransferOperator.lean`** — Operator definition, trace identity
3. **`NB15ResonantBlockOperator.lean`** — Resonant block structure, finite-rank proof
4. **`NB15NonResonantBlockOperator.lean`** — Oscillatory block, HS decay (hardest)
5. **`NB15CorrectionBlockOperator.lean`** — Correction subspace, rank bound
6. **`NB15SpectralDecay.lean`** — Final theorem, RH-strength gate isolation

---

## Import Structure

```lean
import NBMellinTools.NB15DirectAdditiveResonanceSplit
import NBMellinTools.NB15DirectAdditiveResonantQuotient
import NBMellinTools.NB15DirectAdditiveResonantFixedHeight
import RequestProject.OperatorTrace
import RequestProject.CharacterSpectrum
import RequestProject.MobiusMatrix
import RequestProject.FredholmTrace
import RequestProject.H15Resonance
```

---

## Success Criteria

✅ **Week 1:** Kernel uniqueness proved; trace identity holds  
✅ **Week 2:** Resonant block finite-rank; non-resonant HS structure characterized  
✅ **Week 3:** Correction isolated as low-rank; RH-strength gate explicit  
✅ **Overall:** `lake build` passes; 0 sorry; only standard axioms; H15 proof structure = (resonant arithmetic + nonresonant HS decay + correction trace decay)

---

## The Honest Remaining Problem

Aristotle proved the **structure and formalism** of the operator approach. You must prove the **spectral decay** of the nonresonant and correction blocks.

The nonresonant block decay depends on:
1. Divisor-hyperbola reindexing (already outlined by you)
2. Geometric period cancellation (exact: `∑_{b=1}^{complete period} e(uab/q) = 0` when `(u,q)=1`)
3. Incomplete endpoint bound (period = `q/gcd(a,q)`)
4. Hilbert–Schmidt norm convergence (geometric series in N)

The correction block decay is the RH-strength gate — it remains a hypothesis once isolated.

If either fails to formalize, the operator structure is sound but this formalization route doesn't yield RH. Fallback: divisor-hyperbola + classical bounds (proven machinery, longer but more conservative).

---

## Questions for You Before Starting

1. **Should Codex integrate Aristotle's modules directly, or rewrite specialized versions?**
   - Direct integration: faster, but types might not align perfectly
   - Rewrite: cleaner, but more work

2. **Should we assume the nonresonant HS decay will work, or prove contingencies?**
   - Proceed full steam: efficient, high risk if fails
   - Parallel divisor-hyperbola: safer hedge, takes 1-2 extra weeks

3. **For the correction block, should we formalize it as a hypothesis or attempt a proof?**
   - Hypothesis: clear gate, honest about what remains
   - Proof attempt: ambitious, might discover it's true or provably false

---

## Recommended: Proceed with Path A

You have:
- ✅ Mathematical framework (operator spectral decomposition)
- ✅ Verified foundation (Aristotle's five modules, 0 sorry)
- ✅ Honest problem decomposition (three blocks with clear roles)
- ✅ Built-in error detection (four stop tests)

**Start Phase 1 immediately.** If any stop test fails, abort quickly and fall back (only 1-week loss).

If all tests pass through Phase 3 (by end of Week 2), the nonresonant decay becomes your main focus. If that yields to the divisor-hyperbola machinery, H15 is isolated down to a single low-rank property: correction decay.

That's as close to a clean frontier as this problem gets.
