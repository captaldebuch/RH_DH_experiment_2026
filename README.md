# Formalization of the Nyman–Beurling Criterion & Riemann Hypothesis Equivalence in Lean 4

This repository contains a complete, machine-checked Lean 4 formalization of the **Nyman–Beurling Criterion** and its relation to the non-vanishing of the **Riemann Hypothesis (RH)**.

---

## 📁 Repository Organization

```text
riemann-hypothesis/
├── lakefile.toml                  # Lean 4 build configuration
├── lean-toolchain                 # Pinned Lean toolchain (v4.30.0 / v4.28.0)
├── LICENSE                        # Apache 2.0 License
├── README.md                      # High-level summary & build instructions
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
│   └── HOW_TO_VERIFY.md           # 5-step independent verification protocol
└── papers/
    ├── PAPER1_LEAN.tex            # Paper 1: Lean 4 Formalization of Nyman-Beurling
    └── PAPER2_METHODS.tex         # Paper 2: Vacuity Detection & Self-Applied Leiden Framework
```

---

## 🏔️ Main Proved Theorems

1. **Beurling's Shift-Invariant Subspace Theorem** (`Beurling.Main`):
   - Machine-checked characterization of closed shift-invariant subspaces of $H^2(\mathbb{D})$ (`beurling_shift_invariant_subspace`).
   - Pointwise characterization (`beurling_shift_invariant_subspace_pointwise`).
   - Converse implication (`map_innerMul_isShiftInvariant`).
   - Isometry transport of Beurling's theorem to arbitrary Hilbert spaces and half-planes (`beurling_of_isometryEquiv`).
   - $L^1$ Fourier uniqueness theorem (`ae_eq_zero_of_fourierCoeff_eq_zero`).

2. **Inner-Outer Factorization** (`RiemannHypothesis.HardySpace`):
   - Unconditional inner-outer factorization $f(z) = u(z) \cdot g(z)$ on the right half-plane $\{\Re z > 1/2\}$ (`inner_outer_factorization`).
   - Blaschke zero condition $\sum (1 - |z_n|) < \infty$ derived from Jensen's formula (`isBlaschkeFamily_zeroFamily`).
   - Factorization on the unit disc $\mathbb{D}$ (`hardyDisc_inner_outer`).
   - Exact uniqueness up to zero-free units (`inner_outer_unique_up_to_unit`).
   - Machine-verified counterexample disproving literal uniqueness without unit scaling (`inner_outer_factorization_not_unique`).

3. **Báez-Duarte Sufficiency & Mellin--Plancherel Isometry** (`NBMellinTools`):
   - **Forward Direction ($\text{Criterion} \implies \text{RH}$)**: 100% unconditional proof via direct generator Mellin transforms (`baezDuarte_criterion_implies_rh`, 0 custom axioms, 0 open hypotheses, 0 sorries).
   - **$L^2$ Mellin--Plancherel Isometry**: Verified $L^2$ isometry $\int_{\mathbb{R}} \|\mathcal{M}g(1/2+it)\|^2 \diff t = 2\pi \int_0^1 \|g(x)\|^2 \diff x$ (`mellin_plancherel_critical_line`).

---

## 🛡️ Axiom Inventory & Verification Status

- **Sorries**: **0 sorries** in active proved modules.
- **Custom Axioms**: **0 custom axioms**.
- **Foundational Axioms**: Certified with standard Lean 4 / Mathlib foundations only (`propext`, `Classical.choice`, `Quot.sound`).

---

## ⚙️ How to Build

```bash
# Clone the repository
git clone https://github.com/captaldebuch/RH_DH_experiment_2026.git
cd RH_DH_experiment_2026

# Build all libraries
lake build
```

---

## 📜 License

Licensed under the Apache License, Version 2.0 ([`LICENSE`](LICENSE)).
