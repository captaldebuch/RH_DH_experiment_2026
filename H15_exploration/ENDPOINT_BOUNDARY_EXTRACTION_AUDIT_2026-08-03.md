# Endpoint boundary extraction audit

## Exact result

`NB15EndpointBoundaryExtraction.lean` evaluates the finite contour
normalization left open by WP1k.  For every admissible rectangle, define

```text
B(n, sigmaL, T)
  = (2*pi*I)^(-1) * closedBoundary(activeH15Aggregate).
```

Lean proves

```text
B = globalFirstOrderCoefficient + globalAdditionalResidue.
```

Therefore the damped `s = 1` residue and the undamped endpoint are exactly

```text
globalAdditionalResidue = B - globalFirstOrderCoefficient

additionalResidueAmplitude
  = damping^(-1) * (B - globalFirstOrderCoefficient).
```

This is the correct complete-transform formula.  The inverse damping acts
after the complete closed-boundary normalization and the first-order
subtraction.  It cannot be attached to one frequency, one dyadic block, or
one vertical edge.

## Edge expansion

The same normalized boundary is proved equal to

```text
(2*pi*I)^(-1) *
  (horizontalPair + I*rightVerticalIntegral - I*leftVerticalIntegral).
```

This retains all three boundary sectors inside the inverse-damped
expression.  The normalized value is independent of the admissible left
line and finite height, as required by the residue theorem.

## Certified energy

The physical energy now has the exact full-boundary formula

```text
logTaperL2Error
  = certifiedElementaryEndpointLedger
      + im(damping^(-1) * (B - globalFirstOrderCoefficient)).
```

No pointwise physical/Estermann identification and no quadratic PostFE
substitution occurs.

## Stop test

If the first-order subtraction is omitted, the error is exactly

```text
damping^(-1) * globalFirstOrderCoefficient.
```

Since the damping tends to zero, this is not a harmless bookkeeping error.
Any termwise estimate of the closed boundary before the first-order
subtraction risks amplifying the wrong quantity.

## What remains open

The finite extraction is exact, but it does not supply cancellation.  The
formula reduces immediately to the already known undamped endpoint
amplitude; it does not make that amplitude small.

The next analytic target must estimate the **centered boundary numerator**

```text
normalizedCompleteContourBoundary - globalFirstOrderCoefficient
```

at a rate strong enough to survive multiplication by `damping^(-1)`, while
remaining coupled to the certified elementary endpoint ledger.  Bounding
the right, left, horizontal, or first-order pieces separately is not
justified by the present identities.

## Verification

- direct Lean typecheck: successful;
- no `sorry` or custom axiom declaration in the module;
- no files staged or committed.
