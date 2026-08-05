# Physical/Estermann singularity mismatch

Date: 2026-08-03

## Result

The raw certified Mellin numerator and the raw active H15 Estermann aggregate
cannot be the same one-variable meromorphic function.

The result is formalized in
`proofs/NBMellinTools/NB15PhysicalContourSingularityMismatch.lean`.

## Physical side

Write

```text
P_n(s) = (1 - zeta(s) A_n(s)) / s.
```

The finite Dirichlet polynomial `A_n` is continuous at zero, and zeta is
holomorphic there. Therefore the regular numerator is continuous at zero and

```text
lim_(s -> 0, s != 0) s^3 P_n(s) = 0.
```

The Lean theorem is
`tendsto_cubic_mul_certifiedMellinNumerator_zero`.

## Estermann side

The exact four-mode Laurent decomposition already proved in NB12 gives

```text
H_n(s) = regular_n(s)
  + A_{-3}(n)/s^3
  + A_{-2}(n)/s^2
  + A_{-1}(n)/s
  + R_1(n)/(s-1).
```

Using analyticity of the all-poles-removed part, the new module proves

```text
lim_(s -> 0, s != 0) s^3 H_n(s) = A_{-3}(n).
```

The coefficient `A_{-3}(2)` was already proved nonzero. Hence

```text
certifiedMellinNumerator 2 != h15ActiveContourAggregate 2.
```

This is the theorem
`certifiedMellinNumerator_two_ne_h15ActiveContourAggregate`.

## Stronger normalization stop test

The module proves more: there is no scalar factor `M(s)` continuous at zero
such that, away from `0` and `1`,

```text
M(s) * P_2(s) = H_2(s).
```

Indeed, cubic renormalization of the left side still tends to zero, whereas
the right side tends to the nonzero cubic coefficient. This is
`no_continuous_scalar_normalization_at_zero`.

## Interpretation

The proposed completed-integrand route is not merely missing a constant. Any
valid transformation must contain at least one of the following:

1. a genuinely singular completion factor carrying the missing pole order;
2. explicit subtraction and separate transport of the cubic and quadratic
   Laurent modes;
3. a contour-residue or boundary-projection operator rather than pointwise
   equality of the raw functions.

This is consistent with the existing correction-preserving rectangle, where
the polar ledger is kept separately from the pole-removed interior.

The result does not rule out a properly completed two-variable kernel. It
rules out the naive raw identification and every regular scalar repair.

## Correct next target

The next work package should audit the roles of the two complex variables.
The physical Mellin variable and the Mellin--Barnes contour variable must not
be conflated. The target should be a parameterized transform

```text
T_n(u, w)
```

where `u` is the physical spectral parameter and `w` is the contour-shift
parameter. It must prove an exact residue/boundary statement that recovers
the physical numerator from the `w`-contour while the Estermann rows occur on
the transformed boundary. The cubic, quadratic, first-order, and `w=1`
ledgers must remain explicit.

Before any asymptotic estimate, this transform must pass three tests:

1. variable-role consistency;
2. singular-order consistency at `w=0,1`;
3. exact recovery of the certified NB8 numerator, including normalization.

## Verification

The dedicated target built successfully with 8,540 jobs. The full
`lake build` completed successfully with 8,649 jobs. `#print axioms` on the
four principal theorems reported only `propext`, `Classical.choice`, and
`Quot.sound`; the module contains no project axiom or `sorry`.
