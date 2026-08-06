# Beurling Library

This library formalizes **Beurling's Shift-Invariant Subspace Theorem** on Hardy spaces $H^2$.

## Files

- **`Basic.lean`**: Definitions of shift-invariant closed subspaces in $H^2(\mathbb{D})$ and shift operators.
- **`FourierUniqueness.lean`**: $L^1$ Fourier uniqueness theorem (`ae_eq_zero_of_fourierCoeff_eq_zero`).
- **`Main.lean`**: Beurling's shift-invariant subspace theorem (`beurling_shift_invariant_subspace`) and converse (`map_innerMul_isShiftInvariant`).
- **`DiscExtension.lean`**: Isometry transport of Beurling's theorem to arbitrary Hilbert spaces and half-planes (`beurling_of_isometryEquiv`).
