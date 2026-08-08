# Inner–outer factorization in Hardy space

This directory contains a self-contained, `sorry`-free development of Blaschke products and of
the factorization `f = (Blaschke product) × (zero-free analytic function)` for Hardy space
functions, first on the unit disc and then, by transport along the Cayley map, on the half-plane
`{z : ℂ | 1/2 < z.re}`.

## Files

| file | contents |
| --- | --- |
| `BlaschkeFactor.lean` | the elementary Blaschke factor `b_a`, its zeros, modulus bound, analyticity, and the factorization `z - a = b_a(z) · u_a(z)` with `u_a` zero-free |
| `BlaschkeProduct.lean` | `IsBlaschkeFamily`, `blaschkeProduct`, locally uniform convergence, analyticity, `‖B‖ ≤ 1`, and the splitting of `B` into a finite product times a tail close to `1` |
| `BlaschkeZeros.lean` | the order of vanishing of a Blaschke product at a point equals the number of members of the family equal to it |
| `HardyDisc.lean` | `MemHardyDisc`, the enumeration of the zeros with multiplicity, and the **Blaschke condition** `∑ (1 - ‖zₙ‖) < ∞`, proved from Jensen's formula |
| `InnerOuterDisc.lean` | factorization of a nonzero `H²(𝔻)` function as Blaschke product times zero-free analytic function |
| `InnerOuterHalfPlane.lean` | the Cayley transform, `MemHardyHalfPlane`, `IsInnerFunction`, `IsOuterFunction`, the factorization theorem `inner_outer_factorization`, the correct uniqueness statement, and a proof that literal uniqueness is **false** |

## What is proved, and what is not

Proved, without `sorry` and using only Mathlib's own axioms:

* Blaschke products converge, are analytic and bounded by one on the disc, and have prescribed
  zeros with prescribed multiplicities.
* The zeros of a nonzero `H²` function of the disc satisfy the Blaschke condition.
* Every nonzero `H²` function of the disc, and of the half-plane `{re z > 1/2}`, is the product
  of a Blaschke product and a zero-free analytic function.
* Two such factorizations differ by a zero-free analytic unit; in particular the zero sets of the
  two Blaschke factors coincide.
* The literal uniqueness statement (that `B` and `G` are determined by `f`) is false.

Not formalized, because the underlying theory is absent from Mathlib:

* Boundary values of `H²` functions on the circle / on the line `re z = 1/2`, and the Poisson
  representation of `log|g|` by its boundary values.  Consequently the classical notion of an
  *outer* function is replaced here by "analytic and zero-free", and no singular inner factor is
  produced.  A full inner–outer factorization would decompose the inner part further as
  (Blaschke product) × (singular inner function).
* The equivalence of `MemHardyHalfPlane` (defined here by transport along the Cayley map) with
  the classical definition through uniformly bounded integrals over the vertical lines
  `re z = σ`.

## Build

The vendored Mathlib in this repository is compiled with Lean `v4.28.0`, so `lean-toolchain`
was set accordingly.  Build with

```
lake build RiemannHypothesis.HardySpace.InnerOuterHalfPlane
```
