# Formalization of the Nyman–Beurling Criterion & Riemann Hypothesis Equivalence in Lean 4

**Status: Conditionally Connected Bridge (August 8, 2026)**

This repository contains a machine-checked Lean 4 formalization of the **Nyman–Beurling Criterion** and its conditional connection to the **Riemann Hypothesis (RH)**.

---

## ⚠️ Critical Disclaimer & Status

- **Unconditional Proof**: We prove unconditionally that Báez-Duarte generator density implies the non-vanishing of $\zeta(s)$ on $\Re(s) > 1/2$ (`baezDuarte_criterion_implies_rh`, 0 custom axioms, 0 open hypotheses, 0 sorries).
- **Conditional Bridge**: The reduction from Condition H15 to RH is formalized as a **real conditional bridge** requiring two explicit unproved hypotheses:
  1. `H15CoupledVariationBoundaryDecay`: Bounding the coupled variation of signed Möbius-weighted cross-terms along contour boundaries.
  2. `H15PointwiseAggregateToLogTaperTransfer`: Transporting pointwise aggregate decay of cotangent sums to $L^2(0,1]$ density of log-taper generators $\rho_a(x)$.
- **Next Frontier**: The transfer proposition (`H15PointwiseAggregateToLogTaperTransfer`) is the immediate next frontier for conditional formal progress, not Green–Tao higher uniformity.

---

## 📁 Repository Organization

```text
riemann-hypothesis/
├── lakefile.toml                  # Lean 4 build configuration
├── lean-toolchain                 # Pinned Lean toolchain (v4.28.0)
├── LICENSE                        # Apache 2.0 License
├── README.md                      # High-level summary & build instructions
├── GITHUB_FILES_MANIFEST.md       # Complete manifest of all tracked repository files
├── .gitignore                     # Ignore build caches (.lake, .olean)
├── proofs/
│   ├── Beurling/                  # Beurling Shift-Invariant Subspace library (Query 6)
│   ├── RiemannHypothesis/HardySpace/ # Hardy Space H² & Inner-Outer Factorization (Query 7)
│   ├── NBMellinTools/             # Mellin-Plancherel & Forward Direction machinery (Queries E, F, 5)
│   ├── NBMellinTools.lean         # NBMellinTools umbrella module
│   ├── RiemannHypothesis.lean     # RiemannHypothesis umbrella module
│   └── AristotleResults.lean     # Verified query result summary module
├── docs/
│   ├── HONEST_STATEMENT.md        # Honest statement & vacuity audit documentation
│   ├── H15_MATHEMATICAL_DOSSIER.md# Mathematical dossier on Condition H15
│   ├── FORMALIZATION_COMPLETE.md  # Detailed formalization status report
│   └── HOW_TO_VERIFY.md           # 5-step independent verification protocol
└── papers/
    ├── PAPER1_LEAN.tex            # Paper 1: Lean 4 Formalization of Nyman-Beurling
    └── PAPER2_METHODS.tex         # Paper 2: Vacuity Detection & Self-Applied Leiden Framework
```

---

## 🏔️ What Is Proved vs. NOT Proved

### What Is PROVED (Kernel-Verified, 0 Sorries, 0 Custom Axioms)
1. **Forward Direction ($\text{Criterion} \implies \text{RH}$)**:
   - `baezDuarte_criterion_implies_rh`: Unconditional proof using direct generator Mellin transforms.
2. **Mellin--Plancherel $L^2$ Isometry**:
   - `mellin_plancherel_critical_line`: Concrete unitary isometry on $\Re(s) = 1/2$.
3. **Beurling's Shift-Invariant Subspace Theorem**:
   - `beurling_shift_invariant_subspace`: Full characterization of closed invariant subspaces in $H^2(\mathbb{D})$.
4. **Inner-Outer Factorization**:
   - `inner_outer_factorization`: Factorization $f = B \cdot G$ on $\{\Re z > 1/2\}$.

### What Is NOT Proved (Explicit Open Hypotheses)
1. **`H15CoupledVariationBoundaryDecay`**: Bounding coupled signed cross-terms along contour boundaries.
2. **`H15PointwiseAggregateToLogTaperTransfer`**: Transporting pointwise aggregate cotangent decay to log-taper $L^2$ norms.
3. **Unconditional RH**: We do *not* prove RH unconditionally.

---

## ⚙️ How to Build & Verify

```bash
# Clone repository
git clone https://github.com/captaldebuch/RH_DH_experiment_2026.git
cd RH_DH_experiment_2026

# Build all libraries
lake build
```

---

## 📜 License

Licensed under the Apache License, Version 2.0 ([`LICENSE`](LICENSE)).
