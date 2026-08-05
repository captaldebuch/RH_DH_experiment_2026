# Undamped PostFE defect representation audit

## Result

The exploration module
`proofs/NBMellinTools/NB15UndampedDefectRepresentation.lean` constructs the
complete **linear** functional-equation transform.  For an arbitrary cutoff
`K`, it contains

1. every canonical dyadic block in each frequency `r <= K`;
2. the genuine infinite Estermann-frequency tail above `K`;
3. the complete `s = 0` first-order and `s = 1` additional-residue ledger;
4. the original adaptive damping inside each transformed row.

The exact theorem is

```text
h15CompleteLinearPostFERightEdge n K T
  = h15CorrectedThreeHalfRightEdge n T.
```

It follows formally that the left side is independent of `K`.  The rectangle
identity further gives

```text
completeLinearPostFERightEdge
  = I * leftVerticalIntegral - symmetricHorizontalEdges.
```

Thus no dyadic block or Estermann frequency is missing.  The remaining
problem is a contour-boundary normalization problem.

## Correction stop test

Deleting the correction does not give an equivalent transform.  Lean proves
the exact difference

```text
completeLinearPostFERightEdge - uncorrectedAllFrequencyTransform
  = -(2*pi*I*contourResidueLedger).
```

The ledger expands as the sum of the first-order zero-pole coefficient and
the additional one-pole residue.  The cubic and quadratic Laurent data are
not residues of the closed contour; they remain encoded in the active
meromorphic aggregate and must not be added to the residue ledger a second
time.

## Linear versus quadratic levels

The audit corrects a defect in the previous task description.
`h15GlobalPostFEJointCorrectionTransform n r t` is not the complete contour
transform.  It is a fixed-frequency, fixed-height quadratic projection whose
coefficients already contain products of Laurent-row data.  The functional
equation and the right-edge contour act first on the linear signed aggregate.

The old bridge defect therefore has the exact decomposition

```text
undampedPostFEBridgeDefect
  = endpointToLinearPostFEDefect
      + linearToQuadraticPostFEMismatch.
```

The first term compares the inverse-damping-rescaled `s = 1` residue with the
complete linear right edge.  The second compares that linear edge with the
quadratic fixed-height projection.  Neither term is proved to vanish.

The certified energy can now be stated without changing levels:

```text
logTaperL2Error
  = certifiedElementaryEndpointLedger
      + im(completeLinearPostFERightEdge)
      + endpointToLinearPostFEDefect.
```

## What this does not prove

- It does not identify the undamped residue with the corrected right edge.
- It does not identify a linear contour integral with a quadratic projection.
- It does not prove any signed asymptotic decay.
- It does not prove the Riemann hypothesis.

## Correct next target

WP1l should analyze the endpoint-to-linear defect in its exact rectangle
form:

```text
im(damping^(-1) * globalAdditionalResidue)
  - im(I * leftVerticalIntegral - symmetricHorizontalEdges).
```

The first stop test is to determine whether an existing Abel/rectangle limit
evaluates this expression exactly.  If not, it must remain as the first
analytic gate.  Only after it is controlled should the project attempt to
relate the complete linear transform to the quadratic PostFE pairing matrix.

## Verification

- direct Lean typecheck: successful;
- no `sorry` or custom axiom declaration in the module;
- no files staged or committed.
