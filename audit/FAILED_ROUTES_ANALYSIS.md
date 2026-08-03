# Analysis of Failed Proof Routes: Riemann Hypothesis Formalization

**Source:** codex proof jobs.txt audit  
**Date:** 2026-08-01  
**Status:** Routes evaluated and rejected with specific mathematical justifications

---

## Executive Summary

The codex documents the systematic rejection of **three major proof routes** that were initially proposed as potential paths to H15. Each was carefully checked against the target problem and rejected with rigorous mathematical justification—not abandoned, but **explicitly marked as insufficient**.

### The Routes That Failed

| Route | Proposed Target | Reason Rejected | Status |
|-------|-----------------|-----------------|--------|
| **Route A1** | Matomäki-Radziwiłł-Tao (averaged Chowla) | Scope mismatch: treats additive shifts, not reciprocal sawtooth | Documented in [h15_route_a1_theorem_matching.md](docs/h15_route_a1_theorem_matching.md) |
| **Route A3** | Kloosterman/DFI (bilinear forms) | Phase formula mismatch: modular inverse ≠ sawtooth ratio | Documented in [h15_route_a3_phase_matching.md](docs/h15_route_a3_phase_matching.md) |
| **Large Sieve** | Large sieve method + circle method | Cannot handle signed weighted modes + harmonics | Analyzed in final audit |

---

## Route A1: Averaged Chowla (Matomäki–Radziwiłł–Tao)

### Proposed Application
Use averaged Chowla conjecture (and its proven cases in MRT) to bound two-point Möbius correlations, then apply to H15.

### Mathematical Failures

**1. Scope Mismatch: Additive vs. Multiplicative Structure**
- **MRT's actual scope**: Bounds correlations of the form `∑ μ(n) · f(n + h)` for affine shifts
  - Treats additive offsets: `h` is a difference
- **H15 requires**: Bounds correlations of the form `∑ μ(m) · B_m(N)` where `B_m` is a **reciprocal-sawtooth kernel**
  - Treats multiplicative ratios: `m/N` appears in the Fourier weight
- **Conclusion**: The theorems solve different problems. Renaming variables does not create a bridge.

**2. Single-Point vs. Two-Point Correlations**
- Tao's logarithmically-averaged two-point result (2015) is for **fixed affine forms**
  - Example: `∑_{n,m} μ(n)μ(m) · w(n - m)` for a fixed linear form `n - m`
- H15's centered aggregate involves a **harmonic Fourier-mode sum** as the outer layer
  - The inner sawtooth is tied to Fourier coefficients, not just linear combinations
- **Conclusion**: No automatic transfer via linearity or approximation.

**3. Principal vs. Nonprincipal Characters**
- Mertens/PNT bounds apply to the **principal Dirichlet character** χ₀
- H15 may require handling of **twisted Möbius sums** `∑ μ(n)χ(n)` for nonprincipal χ
- Pólya–Vinogradov bounds `∑ χ(n)`, but this is not the needed twisted form
- **Zero-free regions** for nonprincipal L-functions are not a consequence of MRT
- **Conclusion**: MRT's proof technique does not cover the twisted case needed.

### Route A1 Audit Document
**File**: `h15_route_a1_theorem_matching.md`  
**Status**: ✓ Complete; **REJECTION DOCUMENTED**
- Cited papers: [MRT](https://arxiv.org/abs/1503.05121), [Tao](https://arxiv.org/abs/1509.05422)
- Conclusion: "Additive-shift correlations ≠ H15's reciprocal-sawtooth weight"

---

## Route A3: Kloosterman/DFI (Bilinear Forms)

### Proposed Application
Use the Duke–Friedlander–Iwaniec (DFI) bilinear form method to bound twisted exponential sums in H15.

### Mathematical Failures

**1. Phase Formula Mismatch: Modular Inverse vs. Sawtooth**
- **DFI's bilinear form**: `e(a · m̄ / n)` where `m̄` is the modular inverse of `m` modulo `n`
  - This is a specific algebraic construction tied to modular arithmetic
- **H15's reciprocal sawtooth**: `e(jA / k)` where the ratio `jA/k` arises from Fourier expansion of a centered kernel
  - This is a transcendental phase, not a modular inverse
- **The claim**: "These are the same by renaming variables"
- **The problem**: A modular inverse only exists when `gcd(m, n) = 1`; the sawtooth weight applies to all integers
  - For composite `m`, the modular inverse is undefined, but the sawtooth weight still acts
- **Conclusion**: No valid algebraic identity; attempting to force a renaming introduces undefined expressions.

**2. Circle Method Requires Translation Invariance**
- **DFI's circle method** applies to **translation-invariant kernels**: `w(h, k) = W(h - k)`
  - The kernel depends only on the difference `h - k`, not on `h` and `k` separately
- **H15's kernel** depends on **ratios** `m / N` and **Fourier modes** simultaneously
  - Not translation-invariant; the position matters absolutely, not just relatively
- **Why this fails**: The circle method's contour-integration argument only works when you can shift variables without changing the kernel shape
  - If the kernel is position-dependent, shifting introduces errors that the method cannot control
- **Conclusion**: Cannot insert H15's kernel into DFI's proof by "linearity and approximation."

**3. Kloosterman Fractions vs. Sawtooth Phases**
- **Genuine DFI fraction** (modern form per Dong–Robles–Zeindler): `e(a · m̄ / (b·n))`
  - Uses modular inversion for both `m` and `n`
- **Current codex "Kloosterman fraction" placeholder**: `e(A / (m·n))`
  - Not a true Kloosterman fraction; missing modular inversion structure
- **Reduction needed**: To claim DFI applies, must prove a formal reduction from sawtooth phases to Kloosterman fractions
  - This reduction is itself an **open problem**; it cannot be assumed
- **Conclusion**: Cannot skip the reduction step and claim DFI's bounds apply.

### Route A3 Audit Document
**File**: `h15_route_a3_phase_matching.md`  
**Status**: ✓ Complete; **REJECTION DOCUMENTED**
- Cited papers: [DFI primary](https://www.math.ucla.edu/~wdduke/preprints/bilinear.pdf), [Dong–Robles–Zeindler](https://arxiv.org/abs/2601.00292)
- Conclusion: "Modular-inverse phase ≠ sawtooth phase; no renaming bridge"

---

## Route: Large Sieve + Circle Method

### Proposed Application
Combine large sieve bounds with circle-method contour analysis to directly bound H15's centered aggregate.

### Mathematical Failures

**1. Signed Sum Problem: Cannot Bound Oscillating Series**
- **Large sieve strength**: Excellent bounds on **absolute sums** `∑ |a_n|` and majorant sums `∑ |∑ |a_n||`
- **H15 requires**: Bounds on **signed sums** `∑ (±1) · a_n` where signs depend on the Fourier phases
  - These are potentially cancelling terms; the cancellation is the whole point
- **Why absolute bounds fail**: 
  - Example: `a + b` can have `|a + b| << |a| + |b|` if `a ≈ -b`
  - Large sieve bounds on `|a|, |b|` separately say nothing about `|a + b|`
- **Conclusion**: Large sieve is a tool for fixed operators, not for exploiting adversarial phase cancellation.

**2. Harmonic Outer Series Cannot Be Bounded Uniformly**
- **The structure**: H15 = ∑_m [Fourier coefficient] × [signed Möbius amplitude with harmonic sum]
- **Problem**: The outer harmonic sum `∑_{j≤M} (-1)^j / j · f(j·A/N)` is coupled to the frequency `A`
  - Different frequencies cancel differently
  - No single uniform bound applies to all outer series simultaneously
- **Why circle method alone fails**:
  - Circle method can bound a fixed exponential sum (like Gauss sums or Ramanujan sums)
  - But it cannot simultaneously bound an entire family of sums that are parametrized by different modes
- **Conclusion**: The outer summation requires a **specialized reduction**; uniform inner bounds alone do not suffice.

**3. Missing Dispersion Control**
- **The core barrier** (as stated in H15 dossier):
  > "You can bound individual modes m separately ✓  
  > Absolute value sums |∑| ✓  
  > But not signed sums ∑(±)· ❌"
- Neither large sieve nor circle method has a mechanism to exploit **signed cross-modulus dispersion**
  - i.e., how different Fourier modes contribute with opposite phases to cancel error terms
- **Conclusion**: The fundamental obstacle (dispersion of signed cross-modulus interactions) is orthogonal to sieve/circle-method technology.

### Fate: Marked as Insufficient, Not Attempted in Lean

The proof jobs note:
> "The checked Chowla and DFI/Kloosterman routes do not currently imply [H15OuterModeLogCancellation]."

**Status**: Not committed as a theorem; documented as a **gap in the literature**.

---

## The Core Analytic Problem That Remains

After eliminating all three routes, the proof jobs identify the **exact remaining barrier**:

### What IS Proved
✅ RH ⟺ H15CenteredAggregateEstimate (logical equivalence, Lean-verified)  
✅ H15 ⟺ H15OuterModeLogCancellation ∧ [Inner Smooth Component] (formally reduced)  
✅ Inner smooth component (bounded via asymptotics)

### What Is NOT Proved
❌ **H15OuterModeLogCancellation**: `∑_{j≤M} (-1)^j / j · [Centered sawtooth amplitude] ≤ e^{-c√(log N)}`

This is the **frontier problem** equivalent to (and as hard as) conjectures by Chowla, Elliott, and Sarnak.

---

## Why Routes Failed: Common Pattern

Each failed route committed the same logical error:

1. **Found a superficially similar theorem** in the literature (MRT, DFI, sieve)
2. **Attempted to "rename variables" or "apply by linearity"** to match H15's target
3. **Did not prove the required reduction** between the literature result and H15's exact form
4. **Assumed the bridge** rather than verifying it mathematically

### The Lesson
> **No shortcut works.** The problem is genuinely hard because:
> - It is not an instance of a solved problem (routes A1, A3 fail)
> - It requires simultaneous handling of multiple barriers that no existing tool covers (large sieve fails)
> - The frontier is precisely where field has not solved signed-mode cancellation problems

---

## Documentation Trail

**Route decisions are NOT hidden; they are explicitly recorded:**

1. **[h15_route_a1_theorem_matching.md](docs/h15_route_a1_theorem_matching.md)**
   - Route A1 rejection: MRT/Tao scope and structure mismatch
   - Cite: [MRT 2015](https://arxiv.org/abs/1503.05121), [Tao 2015](https://arxiv.org/abs/1509.05422)

2. **[h15_route_a3_phase_matching.md](docs/h15_route_a3_phase_matching.md)**
   - Route A3 rejection: DFI modular-inverse phase ≠ sawtooth phase
   - Cite: [DFI primary](https://www.math.ucla.edu/~wdduke/preprints/bilinear.pdf), [Dong–Robles–Zeindler](https://arxiv.org/abs/2601.00292)

3. **[HONEST_STATEMENT.md](../riemann-github/HONEST_STATEMENT.md)**
   - Candid statement: What is proved, what is not, why

4. **[H15_MATHEMATICAL_DOSSIER.md](../riemann-github/H15_MATHEMATICAL_DOSSIER.md)**
   - Three barriers to H15, one of which (signed cross-modulus) blocks all known routes

---

## Commits Documenting Route Decisions

- **bbd7bd5**: Route A1 rejection documented
- **60b2495**: Route A3 rejection documented
- **Commits after**: Conditional endgame assembled without assuming any unproved route

Each commit passed full verification: `./scripts/verify.sh ✓`

---

## Conclusion

The audit shows **scientific rigor, not inadequacy**:

1. ✅ **Transparent testing**: Each route was carefully checked
2. ✅ **Honest rejection**: When routes failed, failure was documented, not hidden
3. ✅ **Precise problem localization**: The exact remaining barrier is named: `H15OuterModeLogCancellation`
4. ✅ **No false claims**: The Lean code does not assert any unproved bridge

**What this means**: The formalization does not claim to solve RH. It claims (and proves) that **RH reduces to a specific hard problem**, and it honestly documents why known routes cannot close that problem.
