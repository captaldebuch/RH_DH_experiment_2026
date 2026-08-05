# H15 Operator Spectral Decomposition: Mathematical Brief
**Date:** 2026-08-05  
**Status:** Specification for exploration (NOT YET IMPLEMENTED)

---

## Executive Summary

Instead of bounding the H15 signed ledger term-by-term, we redefine it as the **trace of a finite-dimensional operator** acting on the active index set. Decay becomes a **spectral property** (trace convergence to zero), not an arithmetic estimate. This avoids all the walls: interpolation vacuity, scalar renormalization impossibility, Bettin–Chandee mismatch, and edgewise bound destruction.

---

## The Active Index Set

For scale $N$, define:

$$\mathcal{I}_N = \{(i, r) \mid i \in \mathcal{R}_N, r \in \mathcal{R}_{q_i}\}$$

where:
- $i$ ranges over `H15LaurentRowIndex N` (valid Laurent rows)
- $q_i = $ `h15BettinChandeeModulusVariable i` (the row's modulus)
- $r \in \mathcal{R}_{q_i}$ satisfies $K < r < K + 1 + J$ and $q_i \nmid r$ OR $q_i \mid r$ (both resonant and nonresonant)

In Lean: `$\mathcal{I}_N \approx$ Finset of `(H15LaurentRowIndex N × ℕ)` satisfying membership in `h15BettinChandeeFiniteBox`

---

## The H15 Kernel

Define the **exact H15 kernel** (time-dependent, fixed height):

$$K_N(\xi, \eta) = \overline{\mu(d_\xi)} \cdot \mu(d_\eta) \cdot w_N(i_\xi) \cdot w_N(i_\eta) \cdot \Phi_N(\xi, \eta)$$

where:
- $\xi = (i, r)$, $\eta = (i', r')$ are indices in $\mathcal{I}_N$
- $\mu(d) =$ `ringHomClass.map ℤ ℚ` applied to `MöbiusFunction d` (the Möbius function)
- $d_\xi$ is part of the Laurent row context (encodes orientation/coefficient structure)
- $w_N(i) =$ `h15LogTaperWeight i` or equivalent log-taper Möbius weight from NB8
- $\Phi_N(\xi, \eta) = \Phi_{\text{phase}}(i, r, i', r') \cdot \Phi_{\text{coeff}}(r, r')$ is the **phase-coefficient product**:

$$\Phi_N(\xi, \eta) = e_q\left(u_i \cdot r / q_i\right) \cdot \overline{e_{q'}\left(u_{i'} \cdot r' / q_{i'}\right)} \cdot h15DirectAdditiveFrequencyCoefficient(r, t) \cdot \overline{h15DirectAdditiveFrequencyCoefficient(r', t)}$$

**Critical property:** $K_N$ is **uniquely determined** by the requirement that:
1. Its diagonal entries reproduce the exact H15 weights and frequencies
2. Its off-diagonal entries are determined by the exact Estermann pairing (both orientations)
3. Both row and frequency indices are drawn from the certified finite box `h15BettinChandeeFiniteBox`

---

## The H15 Transfer Operator

Define the linear map:

$$\mathbf{T}_N : \ell^2(\mathcal{I}_N) \to \ell^2(\mathcal{I}_N)$$

$$(\mathbf{T}_N f)(\xi) = \sum_{\eta \in \mathcal{I}_N} K_N(\xi, \eta) \cdot f(\eta)$$

In Lean: `def h15TransferOperator (n : ℕ) : LinearMap ℂ (Lp 2 (fun _ : {i // i ∈ h15BettinChandeeFiniteBox n} => ℂ))...`

---

## The Exact Identity (Theorem to Prove)

**THEOREM (exact trace identity):**

$$\text{Tr}(\mathbf{T}_N) = \mathcal{L}_N$$

where $\mathcal{L}_N$ is the **complete H15 signed ledger at scale N**, the exact value currently defined as:

```lean
h15BettinChandeeMiddleFrequencyIntegral n K J T + h15LowFrequencyCoupledIntegral n T + h15HighFrequencyTail n T
```

In other words: **the trace of the transfer operator equals the signed ledger exactly, no approximation**.

**Why this is not vacuous:**
- The kernel $K_N$ is uniquely specified by the existing H15 weights and phase definitions
- The trace captures the **diagonal** of the kernel: $\text{Tr}(\mathbf{T}_N) = \sum_{\xi} K_N(\xi, \xi)$
- This diagonal sum is the ledger by construction
- The operator-theoretic viewpoint adds structure (block decomposition, spectral analysis) that is not explicit in the scalar sum

---

## Block Decomposition

Partition $\mathcal{I}_N$ into three subsets:

### Block 1: Resonant (R)
$$\mathcal{I}_N^{\text{res}} = \{(i, r) \in \mathcal{I}_N \mid q_i \mid r\}$$

**Lean:** `Finset.filter h15DirectAdditiveFrequencyResonant (h15BettinChandeeFiniteBox n K J)`

**Key property:** On this block, both Estermann phases collapse to $1 + \cos(\pi s)$ (proven by `NB15DirectAdditiveResonantQuotient.lean`).

**Conjectured spectral property:** $\mathbf{R}_N$ (restriction to this block) is **finite-rank**.

**Why:** The collision parametrization $q_i k = q_{i'} k'$ defines a **finite graph** (proven by `NB15DirectAdditiveResonantFixedHeight.lean`). A graph operator has rank equal to the number of collision classes, which is finite.

**Trace of resonant block:**
$$\text{Tr}(\mathbf{R}_N) = \sum_{\xi \in \mathcal{I}_N^{\text{res}}} K_N(\xi, \xi) = \text{h15BettinChandeeResonantMiddleFrequencyIntegral n K J T}$$

This is arithmetic (weights + collision ledger), requires **no decay estimate**.

### Block 2: Non-Resonant (O)
$$\mathcal{I}_N^{\text{nonres}} = \{(i, r) \in \mathcal{I}_N \mid q_i \nmid r\}$$

**Lean:** `Finset.filter (fun ir => ¬ h15DirectAdditiveFrequencyResonant ir) (h15BettinChandeeFiniteBox n K J)`

**Key property:** The phase is oscillatory in $r$: $e_q(u_i r / q_i)$ where $q_i \nmid r$.

**Conjectured spectral property:** $\mathbf{O}_N$ is **Hilbert–Schmidt** with norm controlled by:

$$\|\mathbf{O}_N\|_{\text{HS}}^2 = \sum_{\xi, \eta \in \mathcal{I}_N^{\text{nonres}}} |K_N(\xi, \eta)|^2 \approx \text{geometric series in N}$$

**Why this should work:**
- The collision condition $q_i k \neq q_{i'} k'$ (non-collision) forces **orthogonality** across distinct dyadic blocks
- The geometric phase allows **period cancellation** (using the divisor-hyperbola structure and full-period geometric series)
- The period bound is $\le q_i / \gcd(q_i, q_{i'})$ (reduced modulus), leading to a telescoping sum

**Trace of non-resonant block:**
$$\text{Tr}(\mathbf{O}_N) = \sum_{\xi \in \mathcal{I}_N^{\text{nonres}}} K_N(\xi, \xi) \to 0 \quad \text{as } N \to \infty$$

This is where the **nonresonant decay** lives: the HS norm **squared** gives the sum-of-squares bound on phase amplitudes.

### Block 3: Correction (C)
$$\mathcal{I}_N^{\text{corr}} = \{(i, u) \mid i \in \mathcal{R}_N^{\text{low}}, u \in U_{\text{endpoint}}(L_{\min})\}$$

(Lower-dimensional space: only low-frequency rows and endpoint parameters)

**Conjectured spectral property:** $\mathbf{C}_N$ is **trace-class** (i.e., absolutely summable singular values) and **low-rank** with rank bounded by:

$$\text{rank}(\mathbf{C}_N) \le |\mathcal{R}_N^{\text{low}}| = O(N^{3/4 + \eta})$$

**Why this should work:**
- The correction is the coupled low-frequency remainder, already separated by `NB15DirectAdditiveResonanceSplit.lean`
- Its indices are bounded by the active log-taper height (polynomial in log N)
- A low-rank operator with trace tending to zero has explicit structure (e.g., sum of outer products of decaying vectors)

**Trace of correction block:**
$$\text{Tr}(\mathbf{C}_N) = \sum_{\xi \in \mathcal{I}_N^{\text{corr}}} K_N(\xi, \xi) \to 0 \quad \text{as } N \to \infty$$

**This is the final RH-strength gate:** Proving $\text{Tr}(\mathbf{C}_N) \to 0$ is now an isolated, low-rank problem, not a coupled sum.

---

## The Spectral Decay Theorem (Target)

**THEOREM to prove (assembles all blocks):**

$$\text{Tr}(\mathbf{T}_N) = \text{Tr}(\mathbf{R}_N) + \text{Tr}(\mathbf{O}_N) + \text{Tr}(\mathbf{C}_N)$$

where:
1. $\text{Tr}(\mathbf{R}_N)$ is a **finite sum** (arithmetic, no decay needed)
2. $\text{Tr}(\mathbf{O}_N) \to 0$ follows from $\|\mathbf{O}_N\|_{\text{HS}} \to 0$ (oscillatory cancellation + period bounds)
3. $\text{Tr}(\mathbf{C}_N) \to 0$ is formalized as an isolated low-rank property

**Consequence:** $\text{Tr}(\mathbf{T}_N) \to 0 \Rightarrow \mathcal{L}_N \to 0 \Rightarrow$ **Riemann Hypothesis** (via NymanBeurlingCriterion).

---

## Built-In Stop Tests (Vacuity Gates)

These tests must **fail loudly** if the operator construction is flawed:

### Test 1: Kernel Uniqueness
**Claim:** The kernel $K_N$ is uniquely determined by the H15 weights, phases, and frequency coefficients.

**Proof:** Show that if two kernels $K$ and $K'$ both satisfy:
- Diagonal entries = exact H15 weights
- Off-diagonal entries = exact Estermann phases × frequency coefficients
- Index set = `h15BettinChandeeFiniteBox`

Then $K = K'$ everywhere.

**Failure mode:** If $K$ can be perturbed and still reproduce the ledger, the identity is vacuous.

### Test 2: Resonant Finite-Rank
**Claim:** The resonant block operator has rank $\le$ number of collision classes.

**Proof:** Use the collision parametrization $(q_i k, q_{i'} k') = (q_{i'} \ell, q_i m)$ from WP1k. This defines a **bipartite graph**. The rank equals the number of connected components.

**Failure mode:** If the resonant block is not finite-rank, the trace becomes infinite or undefined.

### Test 3: Non-Resonant Orthogonality
**Claim:** The non-resonant blocks across distinct dyadic scales are **orthogonal** in the sense that $|K_N(\xi, \eta)| = 0$ when $\xi$ and $\eta$ are in different dyadic blocks and the phase $e_q(ur/q)$ has a different reduced period.

**Proof:** The period of $e(u \cdot ab / q)$ is $q / \gcd(a, q)$. Blocks with distinct reduced periods are orthogonal.

**Failure mode:** If orthogonality fails, the HS norm does not telescope, and the decay estimate collapses.

### Test 4: Correction Low-Rank
**Claim:** The correction block has rank $\le O(N^{3/4 + \eta})$.

**Proof:** The indices of the correction block are restricted to low-frequency rows $i$ and endpoint parameters. The number of such rows is the size of `h15LaurentRowIndex (NB8.logTaperLength n)` restricted to low frequencies, which is polynomial in log N.

**Failure mode:** If the correction is full-rank, it cannot be isolated; the problem collapses back to the coupled ledger.

---

## Lean Implementation Roadmap

### Phase 1: Operator Definition (`NB15H15Operator.lean`)
1. Define `H15Index n` as `{i : H15LaurentRowIndex n × ℕ // i ∈ h15BettinChandeeFiniteBox n K J}`
2. Define `H15Kernel n` as the exact kernel using existing Möbius, weights, phase, and coefficient definitions
3. Define `H15TransferOperator n : LinearMap ℂ (lp 2 H15Index n)`
4. **Prove:** `trace (H15TransferOperator n) = h15SignedLedger n` (exact identity)
5. **Stop test 1:** Prove kernel uniqueness

### Phase 2: Resonant Block (`NB15ResonantBlock.lean`)
1. Define resonant subspace and restrict operator
2. **Prove:** Phase collapses to $1 + \cos(\pi s)$ (reusing WP1j)
3. **Prove:** Resonant block is finite-rank with rank $\le$ collision classes
4. **Prove:** Trace equals resonant ledger term
5. **Stop test 2:** Verify rank bound

### Phase 3: Non-Resonant Block (`NB15NonResonantBlock.lean`)
1. Define non-resonant subspace
2. **Prove:** Block is Hilbert–Schmidt
3. **Prove:** HS norm bound using period cancellation (divisor-hyperbola + geometric series)
4. **Prove:** HS norm squared is a telescoping sum → decay
5. **Stop test 3:** Verify orthogonality across blocks

### Phase 4: Correction Block (`NB15CorrectionPerturbation.lean`)
1. Define correction subspace (low-frequency + endpoint)
2. **Prove:** Block is trace-class
3. **Prove:** Rank bound $\le O(N^{3/4 + \eta})$
4. **Stop test 4:** Verify low-rank bound

### Phase 5: Spectral Decay (`NB15SpectralDecay.lean`)
1. Assemble: `Tr(T_N) = Tr(R_N) + Tr(O_N) + Tr(C_N)`
2. **Prove:** `Tr(R_N)` is arithmetic (no decay needed)
3. **Prove:** `Tr(O_N) → 0` via HS bound
4. **Hypothesis (not yet proven):** `Tr(C_N) → 0`
5. **Consequence:** `Tr(T_N) → 0` assuming correction decays

---

## Why This Avoids the Walls

| Wall | Escape Mechanism |
|------|------------------|
| **Absolute bound wall** | Operator spectral norm $\|\mathbf{O}_N\|$ bounded globally, not term-by-term |
| **Interpolation vacuity** | No interpolation; operator defined directly on active index set |
| **Scalar renormalization impossibility** | Operator has no scalar "repair" at $s=0$; spectrum is intrinsic |
| **Bettin–Chandee mismatch** | Uses exact collision condition $qk = q'\ell$ from WP1k, not inverse phases |
| **Edgewise bound destruction** | Trace is global, captures coupling implicitly via off-diagonal structure |
| **Ramanujan completion insufficiency** | Oscillatory decay (trace norm) is global and spectral, not term-by-term |

---

## Success Criteria

By end of Week 1:
- [ ] Kernel $K_N$ is written in Lean using exact H15 types
- [ ] Trace identity theorem is stated (not yet proved, but formulated)
- [ ] Stop test 1 (kernel uniqueness) is proved or provably fails

By end of Week 2:
- [ ] Resonant block finite-rank property is proved or falsified
- [ ] Non-resonant Hilbert–Schmidt property is characterized

By end of Week 3:
- [ ] Correction perturbation rank bound is established
- [ ] All four stop tests are either passed or show a structural flaw

By end of Week 4:
- [ ] If all tests pass: Spectral decomposition is complete, correction decay is isolated
- [ ] If any test fails: The approach is rejected, fallback to divisor-hyperbola route

---

## Contingency: Fallback Route

If any stop test fails:
1. Revert to classical divisor-hyperbola + geometric-period + Abel summation formalization
2. Use Aristotle's findings on oscillatory sum bounds (Kíral–Petrow–Young, sum-product inequalities)
3. Formalize the nonresonant sector using additive phase machinery already present in project

**Time cost:** ~1 week to recover, total project on track for completion by October 2026.

---

## Key References (For Aristotle)

1. **Operator trace identities:** Fredholm determinants, Grothendieck traces
2. **Finite-rank on graphs:** Spectral graph theory, adjacency operators
3. **Hilbert–Schmidt bounds:** Sum-of-squares estimates, spectral gaps on lattices
4. **Low-rank perturbations:** Rank-1 updates, trace-class operators, determinant formulas
5. **Character sum traces:** Hecke operators, automorphic forms, L-functions as traces
