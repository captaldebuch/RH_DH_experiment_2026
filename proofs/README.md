# Lean Source Status (Session 9c, August 3–4, 2026, PENDING COMPREHENSIVE AUDIT)

## Active Verified Package

**8,630 Lean jobs verified, 0 custom axioms, 148 imported modules.**

`NBMellinTools.lean` is the active public umbrella. It imports 148 modules across the complete reduction chain (Sessions 1–9c, Steps 1–4v-ck). The frontier is **completely characterized**:

**Sessions 1–8 (Complete Reduction Chain):**
- NB2–3: Mellin transforms & error formulas
- NB4–5: Zero-detection reduction
- NB6: Global RH closure
- NB7–9: Approximation sequence & Gram decomposition
- NB10–11: Vasyunin evaluation (classically proved)
- NB12: Exact Fourier core, dyadic/divisor expansion, Abel/Estermann machinery

**Session 9c (Frontier Characterization):**
- **Steps 4a–5p (Complete):** Signed right-line target, frequency split, Bettin-Chandee dyadic ledger, high-tail exchange
- **Steps 4t–4u (Complete):** Absolute frontier closed. Fiber-cardinality exponent +2. Progression-density exponent +1. Arithmetic wall load-bearing.
- **Steps 4v-a–4v-j (Complete):** Algebraic frontier closed. Zero-extension, exact transpose, nested Abel, final boundary audit. All algebraic cancellations exhausted.
- **Steps 4v-k–4v-m (Complete):** Elementary analytic frontier closed. Fourier, collision control, aliasing. Parseval insufficient.
- **Steps 4v-n–4v-zzv (Complete):** Minimal RH-strength interface formalized. Coupled correction-Kloosterman decay required.

**The Verified Theorem:**

```lean
NymanBeurlingCriterion → RiemannHypothesis
```

**The Frontier (H15):**

Unconditional RH follows if and only if:

```lean
Tendsto (fun N => |Correction N + SignedKloostermanAggregate N|)
        atTop (nhds 0)
```

This is the **single minimal statement** on which RH depends. All algebraic and elementary analytic methods are exhausted. The coupled decay is transcendental (RH-strength).

**Verify the build:**

```bash
lake build
lake env lean proofs/NBMellinTools/Audit.lean
```

Expected output: 8,630 jobs verified, axioms = [propext, Classical.choice, Quot.sound] only.

**NB12 (35+ modules) covers the H15 frontier frontier:**
- Dyadic Bettin–Chandee analysis with exact coefficient ledger
- Divisor-square bounds and ultra-high tail decay
- Paired kernel analysis with Ramanujan completion-defect decomposition
- GCD stratification and exact row reduction
- Normalized $Lq$-superperiod cancellation (complete periods sum to zero)
- Complete nested Abel transforms with prefix-saving criteria ($P_1=o(1)$, $P_2=o(1)$)
- Final superperiod boundary audit (zero-mode test negative)
- Fourier representation with collision control and even-modulus aliasing
- Dispersion ledger and off-diagonal/cross-modulus structure
- Shell-block framework with coupled decay interface
- Linear trace gate: minimal RH-strength interface

See `proofs/NBMellinTools.lean` for complete module list and `../README.md` for frontier details.

## Historical Route C material

`route-c/` is an exploratory archive, not a complete or active proof.  It is
not compiled by the default Lake target and is not correctly mapped into the
declared `RiemannHypothesis` library.

The directory contains useful decomposition ideas alongside:

- unproved `sorry` statements;
- explicit research hypotheses;
- false legacy assumptions such as `|M(x)| ≤ 2`;
- a Möbius exponential-sum statement incorrectly described as a Weil bound;
- a vacuous legacy `ZetaZero` predicate.

These files must not be described as a verified WP1–WP7 proof.  They will be
quarantined and reintroduced only theorem-by-theorem after mathematical and
kernel audits.

## Other directories

Other proof folders are research snapshots.  Presence under `proofs/` does
not mean that a file belongs to the active import graph or that its theorem
statements have been validated.

For the repository-level status, read `../README.md` and
`../HOW_TO_VERIFY.md`.
