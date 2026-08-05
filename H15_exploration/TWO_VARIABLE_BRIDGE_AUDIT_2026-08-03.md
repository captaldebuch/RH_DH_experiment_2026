# Two-variable bridge audit

Date: 2026-08-03

## Result

The proposed pointwise bridge `T_n(u,w)` must be corrected at the level of
mathematical type. The physical critical-line numerator is linear. The
certified energy arises only after Hermitian pairing and integration. The
active Estermann aggregate, by contrast, already belongs to the quadratic
Gram decomposition and enters the certified energy through its undamped
`w = 1` residue.

The new module is
`proofs/NBMellinTools/NB15TwoVariableBridgeAudit.lean`.

## Stop test: two slices are not a bridge

For arbitrary functions `F,G : C -> C`, the additive splice

```text
T(u,w) = F(u) + G(w) - F(u0)
```

has `T(u0,w) = G(w)`. If the one scalar corner condition
`G(w0) = F(u0)` holds, it also has `T(u,w0) = F(u)`. Thus two prescribed
slices, even with visibly different variable names, carry no analytic or
arithmetic content beyond compatibility at their intersection.

Conversely, the theorem
`twoBoundarySlices_force_cornerCompatibility` proves that every exact pair
of slices must satisfy that corner condition.

The certified singularity mismatch from WP1i implies

```text
exists s, certifiedMellinNumerator 2 s
  != h15ActiveContourAggregate 2 s.
```

At such an anchor there is no two-variable function having the whole
physical function as one slice and the whole raw Estermann aggregate as the
other. This is `exists_anchor_with_no_raw_twoBoundaryBridge`.

This does not prohibit a genuine transform or operator. It proves that such
a transform cannot be certified merely by its two raw slices.

## The three pre-tests

### 1. Variable-role consistency

The valid formula keeps two different variables:

- `t : R` is the physical spectral height and is integrated over the
  critical line;
- `w : C` is the auxiliary Mellin--Barnes variable and is used for Laurent
  and residue operations.

No substitution `t = w` occurs.

### 2. Singularity-order consistency

The active auxiliary contour retains both certified local modes:

```text
lim_(w -> 0, w != 0) w^3 H_n(w) = A_{-3}(n),
lim_(w -> 1, w != 1) (w-1) H_n(w) = R_1(n).
```

These are `h15AuxiliaryContour_cubicPole` and
`h15AuxiliaryResidueCarrier_tendsto`. The cubic, quadratic, and first-order
zero-pole ledger is not attached to the physical numerator.

### 3. Exact physical recovery

The theorem `h15PhysicalNumerator_exactRecovery` proves, with all existing
normalizations,

```text
certifiedMellinNumerator n (1/2 + i*t)
  = certifiedCriticalLineNumerator n t.
```

Its Hermitian diagonal is `h15PhysicalPairingDensity`.

## The certified bridge

The non-vacuous finite statement is an integral/residue identity, not a
pointwise equality of raw functions:

```text
(1/(2*pi)) * integral_R h15PhysicalPairingDensity(n,t) dt
  = h15CertifiedElementaryEndpointLedger(n)
      + Im(delta_n^(-1) * h15GlobalAdditionalResidue(n)).
```

This is `h15PhysicalPairingIntegral_eq_contourResidueLedger`. It follows
from the independently proved Mellin--Plancherel identity and the exact
finite Estermann/Vasyunin row assembly. It is unconditional and preserves
the inverse-damping factor.

## Consequence for the roadmap

A common pointwise `T_n(u,w)` is neither established nor needed to identify
the finite energy. The meaningful next transformation problem is narrower:

1. start from the undamped residue amplitude already occurring in the exact
   energy formula;
2. express it by the complete PostFE transform, including every frequency,
   dyadic block, endpoint, and polar mode;
3. prove the required global sum--integral and Abel-boundary exchanges;
4. preserve the inverse adaptive-damping factor;
5. isolate the resulting signed decay estimate.

Equivalently, the next exact target is an integral representation or exact
evaluation of `h15UndampedPostFEBridgeDefect`, not another boundary
interpolant.

Even that exact transformation will not prove RH. The final signed decay of
the complete correction-coupled expression remains the RH-strength gate.

## Verification

The dedicated source typechecks with `lake env lean`. The public umbrella
still builds successfully with 8,649 jobs; this exploration module is not
imported there. The four principal theorems depend only on `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorry` or project-specific
axiom.
