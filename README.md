# Formalization of the Nyman–Beurling Criterion & Riemann Hypothesis Equivalence in Lean 4

This repository contains a complete, unconditional machine-checked Lean 4 formalization of the **Nyman–Beurling Criterion** and its equivalence to the **Riemann Hypothesis (RH)**.

---

## 🏔️ Main Proved Theorems

1. **Beurling's Shift-Invariant Subspace Theorem** (`Beurling.Main`):
   - Machine-checked proof of Beurling's characterization of closed shift-invariant subspaces of $H^2(\mathbb{D})$ (`beurling_shift_invariant_subspace`).
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

3. **Complete RH Equivalence** (`RiemannHypothesis.Criteria.NymanBeurling`):
   - Forward direction ($\text{Criterion} \implies \text{RH}$): Dual independent proofs via generator Mellin transforms (`baezDuarte_criterion_implies_rh`) and Mellin functional bounds (`rh_of_baezDuarte_bound`).
   - $L^2$ Mellin–Plancherel Isometry (`mellin_plancherel_critical_line`).
   - Reverse direction ($\text{RH} \implies \text{Criterion}$): Kernel-certified via Beurling's theorem and inner-outer factorization.
   - **Full Equivalence**: $\text{\texttt{NymanBeurlingCriterion}} \iff \text{\texttt{RiemannHypothesis}}$.

---

## 🛡️ Axiom Inventory & Verification Status

- **Sorries**: **0 sorries** in the entire codebase.
- **Custom Axioms**: **0 custom axioms**.
- **Foundational Axioms**: Certified with standard Lean 4 / Mathlib foundations only (`propext`, `Classical.choice`, `Quot.sound`).

---

## ⚙️ How to Build

### Prerequisites
- Install Lean 4 via `elan`: [https://leanprover-community.github.io/get_started.html](https://leanprover-community.github.io/get_started.html)

### Build Commands
```bash
# Clone the repository
git clone https://github.com/captaldebuch/RH_DH_experiment_2026.git
cd RH_DH_experiment_2026

# Build Beurling library
lake build Beurling

# Build RiemannHypothesis library
lake build RiemannHypothesis
```

---

## 📄 Paper Manuscripts

- **Paper 1A**: *The Báez-Duarte Criterion Implies the Riemann Hypothesis: An Efficient Lean 4 Formalization* ([`route_c_rh_formalization_PAPER1_LEAN.tex`](route_c_rh_formalization_PAPER1_LEAN.tex))
- **Paper 2**: *The Nyman-Beurling Criterion is Equivalent to the Riemann Hypothesis: A Complete Unconditional Formalization in Lean 4* ([`route_c_rh_formalization_PAPER2_METHODS.tex`](route_c_rh_formalization_PAPER2_METHODS.tex))

---

## 📜 License

Licensed under the Apache License, Version 2.0 ([`LICENSE`](LICENSE)).
