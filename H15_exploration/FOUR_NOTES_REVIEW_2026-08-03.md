# Review of the four Hilbert/contour/ledger/spectral notes

## Overall verdict

The notes contain one exact principle already implemented, one directly
useful proposal for the next bridge, one excellent bookkeeping discipline,
and one substantially premature automorphic route.

1. The finite Hilbert-space embedding is mathematically correct, but it does
   not identify the certified H15 object with the Estermann/PostFE object.
2. The completed two-variable Mellin proposal is the most relevant new idea.
3. The `bulk + labelled ledger` invariant is the correct proof discipline.
4. An Eisenstein/Kuznetsov expansion cannot be invoked until an actual
   automorphic kernel or Poincare series realizing the H15 coefficients has
   been constructed and its test-function hypotheses proved.

None of the notes supplies signed asymptotic decay or proves RH.

## Note 1: exact Hilbert-space embedding

For positive weights `w_j`, disjoint measurable cells of measure `w_j` do
give an exact isometry from the finite weighted space into `L²`.  Polarization
then preserves every signed cross term.  The finite matrix criterion

```text
A* V A = W
```

is also the exact criterion for a weighted isometry.

This principle is already realized more specifically in
`NB15VerticalFrequencyPairing.lean`.  That file proves

```text
normSq(sum of all frequency/block terms)
  = sum over all ordered frequency/block pairings
```

both pointwise and after integration over every compact vertical interval.
It retains diagonal, cross-frequency, cross-block, and simultaneous
cross-frequency/cross-block terms.

The abstract cell or Haar embedding would therefore be a faithful model, but
not a new H15 bridge.  It forgets the actual Gamma factors, additive phases,
residue terms, and contour normalization.  An arbitrary isometry preserves a
Gram matrix but does not prove that two arithmetically defined Gram matrices
are equal.

One wording in the note needs care.  If the ledgers are embedded into
orthogonal components of a Hilbert direct sum, their mutual cross terms are
zero.  To obtain the displayed cross-term formula, one must first apply the
signed synthesis map into a common target space and then take its norm.  The
direct-sum storage and the signed synthesis operation are distinct maps.

NUFFT and Bluestein are appropriate only for numerical diagnostics here.
They cannot prove the missing analytic identification; certified numerics can
only validate finite instances within explicit error bounds.

## Note 2: completed two-variable Mellin bridge

This is the strongest part of the proposal.  It correctly separates:

- the physical Mellin variable on `Re s = 1/2`;
- a contour/Estermann variable moved to an absolutely convergent right line;
- the full principal parts of crossed poles;
- finite Ramanujan/gcd algebra performed before limiting operations;
- an `L²` boundary-value statement when pointwise convergence is unavailable.

It matches the active target after
`NB15CertifiedMellinPlancherel.lean`: the physical critical-line energy is now
certified, while the two-variable contour normalization is still absent.

Two corrections are essential.

First, a functional equation cannot generally be applied to an arbitrary
finite truncation of a Dirichlet series.  In the present project, the safe
finite object is the outer finite H15 row family whose individual Estermann
or finite Hurwitz continuation identities are exact.  A truncated inner
Dirichlet series does not inherit the full Estermann functional equation
without an explicit remainder.

Second, the proposed two-variable object must be defined from the literal
certified numerator and the already verified H15 row data.  A structure with
arbitrary fields named `criticalBulk` and `rightLineBulk` would merely restate
the desired equality.

## Note 3: correction ledger conservation

The invariant

```text
old bulk + old ledger = new bulk + new ledger
```

is exactly the correct design rule.  It agrees with the existing four-sector
ledger in `NB12BBLSPoleSubtractedRectangle.lean`:

1. correction--finite-part gap;
2. first-order polar/Taylor residual;
3. additional `s = 1` residue;
4. elementary/endpoint completion.

At the time of the intake, `BBLSCorrectionPreservingRectangleData` recorded
this desired decomposition but had no certified correction/endpoint
inhabitant.  The underlying literal-row rectangle theorem was already proved
in `NB12BBLSH15Rectangle.lean`.  The follow-up module
`NB15CorrectionPreservingRectangle.lean` now constructs the interface from
that genuine boundary integral, the actual pole-subtracted boundary, the NB8
retained correction, and the certified non-correction endpoint.  Thus the
finite closed-contour ledger is now concrete.  The still-missing theorem is
the identification of an oriented vertical edge with the physical
critical-line boundary value.

The note's schematic formula

```text
D(s) = chi(s) D*(1-s) + P(s)
```

must not be assumed generically.  Whether an additive `P` occurs, and its
exact form, depends on the completed Estermann normalization.  Contour
residues, constant modes, and endpoint terms should remain separately typed
until the exact row-level identity identifies them.

The discussion of a cutoff `floor(sqrt(t/(2*pi)))` concerns
Riemann--Siegel-type truncations.  The active H15 frequency cutoff `K` is an
external finite parameter, not presently that discontinuous function of
`t`.  A jump ledger is needed only if a future proof deliberately introduces
such a height-dependent cutoff.

## Note 4: automorphic decomposition

The note is correct that a dyadic partition has no Eisenstein expansion by
itself.  The expansion belongs to an automorphic kernel into which the dyadic
weights have been inserted.

No such H15 automorphic kernel is presently constructed.  Moreover, the
active compatibility audit proves two concrete obstructions to an immediate
published-tool application:

- the literal post-functional-equation phase is direct, while the immediate
  Bettin--Chandee inverse-residue phase is not obtained by relabelling;
- the audited fixed-frequency exponent gives no saving in the low modes.

The exact coefficients also retain joint modulus--frequency dependence.
Therefore ordinary separated-coefficient Kuznetsov is not yet available.
Regularized Rankin--Selberg or bilinear spectral reciprocity remains a
possible later route, but only after the contour normalization and an actual
automorphic realization have been proved.

## Recommended next target

Do not add another abstract Hilbert embedding and do not start an Eisenstein
expansion.  The actual H15 correction-preserving closed rectangle has now
been constructed.  The next target is its physical vertical-edge
normalization.

The work package should:

1. define one completed, parameterized two-variable integrand whose physical
   boundary is the certified NB8 numerator and whose contour rows are the
   literal finite H15 Estermann rows;
2. identify its oriented left edge with that physical boundary in `L²`;
3. identify its right edge with the existing active H15 aggregate, retaining
   the now-certified four-sector ledger;
4. prove the horizontal-edge limit and the right-line sum--integral exchange
   with one fixed regulator;
5. only then square, integrate, and compare with the already certified
   critical-line energy.

The next stop test is exact: if no common two-variable integrand has both the
certified NB8 boundary and the already constructed H15 rectangle boundary,
then the present NB12 PostFE family is not the contour image of the NB8
numerator and must be corrected before any decay estimate is attempted.
