# Certified correction-preserving H15 rectangle audit

## Result

`proofs/NBMellinTools/NB15CorrectionPreservingRectangle.lean` constructs the
generic correction-preserving rectangle package for the literal finite H15
row family.

Unlike the generic interface, the constructed fields are not arbitrary:

```text
normalized rectangle
  = certified NB8 correction
    + certified non-correction endpoint
    + (2*pi*i)^(-1) * boundary(active H15 aggregate),

pole-subtracted interior
  = (2*pi*i)^(-1) * boundary(all-poles-removed H15 aggregate).
```

The active boundary is evaluated by the genuine H15 rectangle theorem.  The
pole-subtracted boundary is zero by holomorphy.  Consequently the package
expands exactly into:

1. correction--finite-part gap;
2. first-order polar residual;
3. damped additional `s = 1` residue;
4. certified elementary/endpoint completion.

## Physical-energy connection

The module also proves

```text
certifiedCriticalLineEnergy n
  = h15CertifiedElementaryEndpointLedger n
      + im((h15ContourDamping n)^(-1)
          * h15GlobalAdditionalResidue n).
```

This is an exact equality obtained by combining the certified
Mellin--Plancherel theorem with the finite Estermann endpoint assembly.  It
does not divide an asymptotic estimate by the damping; it merely records the
already exact finite identity.

## What remains open

The closed rectangle is a contour identity in the Estermann contour
variable.  The certified numerator is a boundary function in the physical
Mellin variable.  No theorem yet identifies an oriented edge of the former
with the latter.

The next required object is therefore a genuine two-variable completed
integrand with both properties:

1. its physical `L²` boundary is `certifiedCriticalLineNumerator`;
2. its right contour edge is `h15ActiveContourAggregate`, with the four
   certified ledger sectors retained.

Until this common object is constructed, the rectangle package is not an
asymptotic decay theorem and gives no proof of RH.
