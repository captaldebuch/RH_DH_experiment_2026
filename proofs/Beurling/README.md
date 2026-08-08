# Beurling's shift-invariant subspace theorem

This directory contains a complete, `sorry`-free Lean 4 proof of Beurling's theorem on
shift-invariant subspaces of the Hardy space `H²`, together with the infrastructure it needs.

## Files

| file | contents |
|---|---|
| `Basic.lean` | The Hilbert space `L²(𝕋)` (circle with Haar probability measure), multiplication by an a.e.-unimodular function as a linear isometry (`mulL2`), the shift operator (`shiftL2`), the closed subspaces `HardyFrom N` and the Hardy space `Hardy2 = HardyFrom 0`, and the fact that `H²` is the closed span of the characters `zⁿ`, `n ≥ 0`. |
| `FourierUniqueness.lean` | The `L¹` uniqueness theorem for Fourier coefficients on the circle: an integrable function all of whose Fourier coefficients vanish is `0` a.e. (`ae_eq_zero_of_fourierCoeff_eq_zero`). |
| `Main.lean` | Inner functions (`IsInner`), Beurling's theorem (`beurling_shift_invariant_subspace`), its pointwise restatement (`beurling_shift_invariant_subspace_pointwise`), and the converse (`map_innerMul_isShiftInvariant`). |
| `DiscExtension.lean` | The analytic extension of an `L²(𝕋)` function to the open unit disc via its nonnegative Fourier coefficients, and its analyticity (`analyticOnNhd_discExt`). |

## Statement

`Beurling.beurling_shift_invariant_subspace`: if `M` is a submodule of `L²(𝕋)` with

* `M ≤ Hardy2` (`M` is contained in `H²`),
* `IsClosed (M : Set L2C)`,
* `∀ f ∈ M, shiftL2 f ∈ M` (invariance under `f ↦ z · f`),

then either `M = ⊥`, or there is an inner function `e` (an element of `H²` with `|e| = 1` a.e. on
the circle) such that `M = e · H²`.

`Beurling.beurling_of_isometryEquiv` restates the theorem for an arbitrary Hilbert space equipped
with an isometric isomorphism onto `L²(𝕋)` carrying the given operator to the shift; this is how
the result can be applied to a Hardy space of a half-plane once such an isometry is available.

The converse, `Beurling.map_innerMul_isShiftInvariant`, states that `e · H²` is indeed a closed
shift-invariant subspace of `H²` for every inner `e`, so the theorem is a characterization.

All results are proved from Mathlib alone and use only the standard axioms
`propext`, `Classical.choice`, `Quot.sound`.

## Model, and scope

The theorem is proved for the Hardy space of the **unit disc** in its boundary-value model:
`H²` is realized as the closed subspace of `L²(𝕋)` of functions whose negative Fourier
coefficients vanish, and the shift is multiplication by the character `z = fourier 1`.  This is
the classical setting of Beurling's theorem, and inner functions appear in it as the elements of
`H²` of modulus one a.e. on the circle.

Not covered here:

* the transfer of the theorem to `H²({Re s > 1/2})` along the conformal map of the half-plane
  onto the disc (this needs the Cayley-transform isometry between the two Hardy spaces);
* the identification of an inner function with its analytic extension (only analyticity of the
  extension is proved in `DiscExtension.lean`; the boundary-value correspondence is Fatou's
  theorem, which is not in Mathlib);
* inner–outer factorization.

## Proof outline

The Wold decomposition is not needed.  Writing `S` for the shift and `N` for the closure of
`S(M)`:

1. If `M = N` then `M ⊆ zⁿ H²` for every `n`, so `M = 0`.  Hence, if `M ≠ 0`, there is a unit
   vector `e ∈ M` orthogonal to `N` (a *wandering vector*), obtained by subtracting from an
   element of `M ∖ N` its orthogonal projection onto `N`.
2. `⟪e, zⁿ e⟫ = 0` for `n ≥ 1` and `‖e‖ = 1` say exactly that all Fourier coefficients of
   `|e|² − 1` vanish; by the `L¹` uniqueness theorem, `|e| = 1` a.e., i.e. `e` is inner.
3. For `f ∈ M`, the function `g = ē f` lies in `L²` and its negative Fourier coefficients are the
   inner products `⟪e, zⁿ f⟫ = 0` (`n ≥ 1`), so `g ∈ H²` and `f = e g`.  Hence `M ⊆ e · H²`.
4. Conversely `e · zⁿ = Sⁿ e ∈ M` for `n ≥ 0`, and `H²` is the closed span of the `zⁿ`, so
   `e · H² ⊆ M` because `M` is closed and multiplication by `e` is continuous.

## Mathlib gaps encountered

* No `L¹` uniqueness theorem for Fourier coefficients on `AddCircle` (only the `L²` Hilbert-basis
  statement); proved here from Stone–Weierstrass and outer approximation of closed sets.
* No multiplication operator on `Lp` by a bounded/unimodular function; constructed here
  (`Beurling.mulL2`).
* No Wold decomposition, wandering-subspace theory, or Hardy-space API (`H²`, inner functions,
  Blaschke products, Fatou's theorem, inner–outer factorization).

## Build note

The Mathlib checkout vendored with this project is built for toolchain `v4.28.0`, while the
project's `lean-toolchain` requested `v4.30.0`, so nothing could be compiled as delivered.  The
`lean-toolchain` file has been pinned to `leanprover/lean4:v4.28.0` to match the vendored
Mathlib.  Build this development with

```
lake build Beurling
```

Two pre-existing files of the `NBMellinTools`/`RiemannHypothesis` libraries
(`NB4ZeroDetection.lean`, `VasyuninCotangentRecognition.lean`) do not compile against this
(slightly older) Mathlib, because they use lemma names introduced after it; they were left
untouched.
