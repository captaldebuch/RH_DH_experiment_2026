# Task B Decomposition: LogTaperL2Decay (Kimi's 12-Part Strategy)

**Date:** 2026-08-05  
**Source:** Kimi (alternative to monolithic "prove decay" approach)  
**Status:** Strategy document for future Task B work  
**Key Insight:** Replaces absolute-bound walls with exact identities + structured stop-tests

---

## Overview

Instead of attempting a single monolithic proof of `LogTaperL2Decay`, Kimi proposes **12 independently verifiable structural theorems** that either **eliminate a sector exactly** or **isolate the irreducible remainder**. The architecture systematically avoids the absolute-bound wall by never asking for termwise majorants after exact identities are applied.

---

## Phase 1 — Exact Elimination (Arithmetic, No RH)

### B.1: Character-Average Projection Identity

**Target:** Prove that introducing the third modulus $p$ via character-average connects the resonant quotient $r=qk$ to the existing $qq'/p$ NB12 collision ledger exactly.

**Method:** Codex

**Stop-test:** If the projection does not recover $qq'/p$, document the exact obstruction and halt.

**Mathematical Content:**
The collision parametrization from WP1k is `qk = q'ℓ`. Introducing a character sum over $p$ (the third modulus) should give an exact reindexing that connects to the NB12 PostFE collision ledger structure `qq'/p`. If this fails, the character-average approach has a fundamental structural flaw.

---

### B.2: Elementary Ledger Closed Form

**Target:** Prove 
$$E_{\text{elementary}}(N) = \frac{A}{\log N} + \frac{B}{(\log N)^2} + O\left(\frac{1}{(\log N)^3}\right)$$
with explicit constants $A, B$.

**Method:** Codex

**Stop-test:** If the elementary ledger hides oscillation (e.g., oscillates faster than the envelope decays), flag it and reclassify to Phase 3.

**Mathematical Content:**
The elementary part (from the certified numerator) should have a clean asymptotic expansion. If it doesn't, the oscillation is not purely carried by the nonresonant and correction sectors.

---

### B.3: High-Frequency Tail Connection

**Target:** Connect the proved ultra-high tail vanishing to the $L^2$ energy: show that the tail contribution to `LogTaperL2Decay` equals the already-bounded high-frequency integral.

**Method:** Codex

**Stop-test:** If the connection requires a new unbounded operator, stop.

**Mathematical Content:**
The high-frequency sector ($r \gg N^{3/4}$) has already been shown to decay. B.3 must prove that this decay translates directly into the $L^2$ energy bound without introducing new complications.

---

## Phase 2 — Resonant Sector Elimination (Complete Characterization)

### B.4: Resonant Diagonal Exact Evaluation

**Target:** Evaluate the diagonal term from WP1k's three-sector identity in closed form. The phase is $1 + \cos(\pi s)$; sum over collision indices $k$ of $|\mu|^2$ times explicit Archimedean weights.

**Method:** Codex

**Stop-test:** If the diagonal grows (rather than decays), the resonant reindexing in WP1k is inconsistent with the log-taper weights.

**Mathematical Content:**
$$\sum_{k: qk = q'\ell} |\mu(q)|^2 |\mu(q')|^2 w(k,k') (1 + \cos(\pi s))$$
This sum should be computable explicitly. If it diverges, the resonant structure has a fundamental issue.

---

### B.5: Resonant Collision Off-Diagonal Bound

**Target:** Bound the collision off-diagonal using the exact parametrization $qk = q'\ell$. Do **not** use absolute values on $\mu$; instead, use **multiplicative structure**: sum over $h = qk$ with $\tau(h)$ divisor-count representations, exploiting the average order of $\tau$ and weight decay.

**Method:** Codex + Aristotle (literature on divisor sums in short intervals)

**Stop-test:** If $\tau$-average is insufficient (diverges), try Rankin–Selberg or halt.

**Mathematical Content:**
The off-diagonal collision term involves Möbius products. Instead of:
$$\sum |\mu(q)| |\mu(q')| \leq \text{trivial}$$
use:
$$\sum_h \tau(h) \cdot (\log h)^{-\alpha} \ll \log N$$
where $\tau(h)$ is the divisor count and the weight decays like $(\log h)^{-\alpha}$.

---

### B.6: Resonant Non-Collision Vanishing

**Target:** Prove that the noncollision off-diagonal is controlled by $\min |qk - q'\ell| \geq 1$, giving geometric decay from the smooth weight's Lipschitz property.

**Method:** Codex

**Stop-test:** If gap $\geq 1$ is not enough (i.e., the weight has too much singularity), the approach fails.

**Mathematical Content:**
When $qk \neq q'\ell$, the separation is at least 1. The smooth weight's finite Lipschitz constant means:
$$|w(qk) - w(q'\ell)| \leq C \cdot |qk - q'\ell| \ll 1$$
This should give uniform decay.

---

## Phase 3 — Non-Resonant Sector (Novel Fourier Attack)

**Rationale:** Instead of van der Corput or large sieve directly, use the **finite Fourier transform on the $r$-fibers** to separate oscillation from amplitude.

### B.7: Non-Resonant Fourier Decomposition

**Target:** For each active $q$, decompose the $r$-sum (with $q \nmid r$) via Fourier on $\mathbb{Z}/q\mathbb{Z}$:
$$\text{NonRes}_N = \sum_q \sum_{a=1}^{q-1} \hat{c}(a,q) \cdot S(a,q)$$
where $S(a,q) = \sum_{r: q \nmid r} e(ar/q) \cdot w(r,q)$ is a **twisted Ramanujan sum**.

**Method:** Codex

**Stop-test:** If the Fourier inversion fails due to $r$-weight non-smoothness, halt and diagnose.

**Mathematical Content:**
The key is that $q \nmid r$ can be expanded via Möbius inversion on divisors of $q$. This separates the oscillatory component (the Ramanujan sum) from the smooth-weight component (the Fourier coefficients).

---

### B.8: Twisted Ramanujan Evaluation

**Target:** Evaluate $S(a,q)$ explicitly. Use the known formula for Ramanujan sums twisted by the condition $q \nmid r$ (a Möbius inversion on divisors of $q$). 

**Bound:** $|S(a,q)| \leq \tau(q) \cdot q^{1/2} \cdot (a,q)^{1/2}$

**Method:** Codex + Aristotle (literature on generalized Ramanujan sums)

**Stop-test:** If the twist by $q \nmid r$ destroys multiplicativity, document and pivot.

**Mathematical Content:**
Standard Ramanujan sums have the multiplicativity property. The twist might destroy it. If it does, we need a fallback (e.g., Kloosterman sums or geometric measure theory, see B.11).

---

### B.9: Fourier Coefficient Decay

**Target:** Prove 
$$\hat{c}(a,q) \ll |a|^{-1} \cdot (\log q)^{-1}$$
from the smoothness of the log-taper weight in the $r$-variable.

**Method:** Codex

**Stop-test:** If coefficients decay slower than $|a|^{-1/2}$, the weight is not smooth enough; use stationary phase instead.

**Mathematical Content:**
The log-taper weight is smooth in $r$. By Fourier decay theory, smooth functions have rapidly decaying Fourier coefficients. This should give at least $|a|^{-1}$ decay.

---

### B.10: Non-Resonant Final Bound

**Target:** Combine B.7–B.9:
$$\sum_q \sum_{a=1}^{q-1} |a|^{-1} \cdot q^{1/2+\varepsilon} \cdot q^{-3/4-\eta} \ll N^{-\delta}$$
using the dyadic scale $q \asymp N^{3/4+\eta}$.

**Method:** Codex

**Stop-test:** If the sum diverges, the Fourier approach hits a wall; document and fall back to geometric measure (B.11).

**Mathematical Content:**
The sum over $q$ contributes $q^{1/2+\varepsilon}$ from the Ramanujan bound and $q^{-3/4-\eta}$ from the weight decay. This should give a logarithmically convergent sum that contributes to $N^{-\delta}$ in the $L^2$ error.

---

## Phase 4 — Correction Isolation & The Gate

### B.11: Exact Correction Ledger

**Target:** Define $L_N^{\text{coupled}}$ as the explicit remainder after subtracting B.2–B.10 from the full energy. Prove exact identity.

**Method:** Codex

**Stop-test:** If the remainder still contains uncharacterized pieces, halt.

**Mathematical Content:**
By construction:
$$L_N^{\text{coupled}} = E_{\text{full}} - E_{\text{elementary}} - E_{\text{resonant}} - E_{\text{nonresonant}}$$
This should be exact (no error terms). If there are unaccounted-for pieces, the decomposition is incomplete.

---

### B.12: The Gate Theorem

**Target:** Prove
$$\text{LogTaperL2Decay} \iff L_N^{\text{coupled}} \to 0$$

**Method:** Codex

**Stop-test:** Structural. Should be immediate from exact identities.

**Mathematical Content:**
If B.1–B.11 are all exact (no error), then the equivalence is automatic by algebra. This theorem isolates the **RH-strength gate** explicitly: proving RH is equivalent to proving a single coupled correction term vanishes.

---

## Why This Avoids the Classical Walls

| Classical Wall | How This Decomposition Avoids It |
|---|---|
| **Absolute-bound wall** | B.5 uses **multiplicative structure** of $\mu$ via $\tau$-average, not $\|\mu\| \leq 1$. B.7–B.9 separate oscillation (Ramanujan sum) from amplitude (smooth weight), never bounding the phase trivially. |
| **Interpolation vacuity** | No interpolation between boundary values. B.1–B.6 work entirely within the exact resonant structure proved in WP1k. |
| **Scalar renormalization impossibility (WP1i)** | No attempt to repair singularities with scalars. B.3 connects existing high-frequency results; B.4–B.6 handle the resonant singularity **by exact evaluation**, not by repair. |
| **Bettin–Chandee mismatch** | B.7–B.9 use **direct additive Fourier analysis**, not inverse-modular phases. The condition $q \nmid r$ is handled by **Möbius inversion on $\mathbb{Z}/q\mathbb{Z}$**, not by Kloosterman machinery. |
| **Independent edgewise bounds** | B.11 keeps the correction **coupled**. The Gate Theorem (B.12) explicitly states that decay is equivalent to the coupled term vanishing; **no independent bound is claimed**. |

---

## 4-Week Orchestration Plan

| Week | Claude | Aristotle | Codex |
|---|---|---|---|
| **1** | Design B.7–B.9 Fourier attack; draft exact kernel specs for B.1. | Query: "Generalized Ramanujan sums with coprimality twist $q \nmid r$" and "Fourier decay of log-taper weights on arithmetic progressions." | **B.1** (projection identity) + **B.2** (elementary form) + **B.3** (tail connection). |
| **2** | Analyze Aristotle's Ramanujan literature; adapt B.8 spec if multiplicativity is broken. | Query: "Divisor sums in short intervals with oscillatory weights" (for B.5). | **B.4** (resonant diagonal) + **B.5** (collision bound) + **B.6** (non-collision gap). |
| **3** | Design B.11 correction isolation; prove rank bound on paper. | Query: "Scale-invariant measures on multiplicative semigroups" (fallback if B.10 fails). | **B.7** (Fourier decomposition) + **B.8** (Ramanujan evaluation) + **B.9** (coefficient decay). |
| **4** | Synthesis. If B.1–B.10 close, B.12 isolates the gate. If B.10 fails, pivot to B.11 + geometric measure (Aristotle fallback). | Verify if $L_N^{\text{coupled}}$ matches any known spectral gap conjecture. | **B.10** (non-resonant bound) + **B.11** (correction ledger) + **B.12** (Gate Theorem). |

---

## Immediate Next Actions (If Task B Fails)

1. **Claude drafts the Fourier kernel** for B.7 today (exact definition of $\hat{c}(a,q)$ and $S(a,q)$ using existing Lean types).

2. **Aristotle runs tonight:** 
   - *"Generalized Ramanujan sums $c_q^{*}(a) = \sum_{r: (r,q)=1, q \nmid r} e(ar/q)$: explicit formulas, bounds, and multiplicative properties."*

3. **Codex starts B.1 tomorrow:** The character-average projection that introduces $p$. This is the exact algebraic bridge from WP1k to NB12.

**Fallback decision point:** If B.1 succeeds and Aristotle returns a usable Ramanujan formula, the path is clear. If either hits a wall, we have the stop-test documentation and the fallback (geometric measure / operator trace) ready.

---

## Key Distinctions from Prior Approaches

| Aspect | Traditional Approach | Kimi's 12-Part Approach |
|---|---|---|
| **Strategy** | "Prove LogTaperL2Decay directly" | "Eliminate each sector exactly; isolate the gate" |
| **Failure mode** | Hits wall (absolute bounds, interpolation, etc.); no intermediate progress | Each sub-task is independently testable; hitting a wall gives precise obstruction documentation |
| **Use of $\mu$** | $\|\mu(n)\| \leq 1$ (vacuous) | $\mu$-average via divisor-count $\tau(n)$ (nontrivial) |
| **Oscillation handling** | Global van der Corput or sieve | **Local Fourier on $\mathbb{Z}/q\mathbb{Z}$ fibers** (separates phase from amplitude) |
| **Correction term** | Lumped into error | **Explicit coupled ledger $L_N^{\text{coupled}}$; gate theorem isolates it exactly** |
| **End result if incomplete** | "We couldn't prove it" | "Decay holds up to $L_N^{\text{coupled}} \to 0$; here's the exact frontier" |

---

## Integration with Operator Spectral Route

Kimi's decomposition is **orthogonal to** the operator-spectral approach (Task A/Phase 4). 

- **Operator Spectral:** Proves `Tr(Gram) → 0` in an abstract finite model
- **Kimi's 12-Part:** Proves `LogTaperL2Decay ↔ L_N^{coupled} → 0` in the concrete log-taper model

If both succeed:
- Task A connects Tr(Gram) to the PostFE energy
- B.1–B.10 evaluate the PostFE energy exactly
- B.11–B.12 isolate the gate as $L_N^{\text{coupled}}$

The **unified frontier:** Both routes converge to a **single coupled correction term** that must vanish for RH.

---

**Status:** Saved for future use. If Aristotle Tasks A and B do not resolve LogTaperL2Decay, this 12-part decomposition provides a structured fallback with intermediate stop-tests and explicit obstructions at each phase.
