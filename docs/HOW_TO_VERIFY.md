# How to Verify the Lean 4 Formalization

This document describes the 5 integrity checks required to independently verify the formalization.

---

## 1. Prerequisites

- **Lean 4 Version**: Pinned to `v4.30.0` (or `v4.28.0`) in `lean-toolchain`.
- **Package Manager**: `elan` ([https://leanprover-community.github.io/get_started.html](https://leanprover-community.github.io/get_started.html)).

---

## 2. Five Verification Checks

### Check 1: Clean Build
```bash
# Clone the repository
git clone https://github.com/captaldebuch/RH_DH_experiment_2026.git
cd RH_DH_experiment_2026

# Build all targets
lake build
```
Verify that `lake build` exits cleanly with code `0`.

### Check 2: Axiom Footprint Verification
```bash
# Run axiom audit across verified modules
lake env lean proofs/NBMellinTools/Audit.lean
```
Verify that the output reports **0 custom axioms** (`[propext, Classical.choice, Quot.sound]` only).

### Check 3: Check for Sorries
```bash
# Search for any unresolved sorry statements in active proofs
grep -rn "sorry" proofs/Beurling/ proofs/RiemannHypothesis/ proofs/NBMellinTools/
```
Verify that no `sorry` declarations exist in active proved modules.

### Check 4: Verify Non-Vacuous Criterion Formulation
Verify that `NymanBeurlingCriterion` explicitly contains the linear span of dilated fractional parts $\rho_a(x) = \{a/x\} - a\{1/x\}$ in $L^2(0,1]$:
$$\chi_{(0,1]} \in \overline{\operatorname{span}_{\mathbb{C}} \{\rho_a : a \in (0,1]\}}^{L^2(0,1]} \iff \text{RiemannHypothesis}$$

### Check 5: Verify Structured Inhabitation Boundary
Verify that `HardyHalfPlaneInfrastructure` is declared as an explicit 5-field structured hypothesis (`NB15HardySpaceAxioms.lean`), separating the unconditional forward proof ($\text{BaezDuarteCriterion} \implies \text{RiemannHypothesis}$) from half-plane Hardy space inhabitation.
