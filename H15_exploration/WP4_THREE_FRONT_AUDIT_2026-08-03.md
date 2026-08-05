# WP4 three-front proposal: mathematical and formal audit

Date: 2026-08-03

## Verdict

The proposal correctly focuses attention on a boundary normalization, but its
stated success condition is insufficient. There are two distinct issues.

First, contour deformation is linear in a meromorphic function, whereas the
certified Nyman--Beurling energy contains

```text
|F(1/2+it)|^2.
```

This is not a holomorphic function of one complex variable. A residue
calculation for `F` therefore does not by itself transport its squared norm.
The correct analytic object is a sesquilinear kernel in two independent
complex variables,

```text
K_F(z,w) = conjugate(F(conjugate(z))) * F(w).
```

Its conjugate diagonal is `normSq (F(s))`. A valid contour proof must control
this two-variable object (or prove an equivalent Hilbert-space boundary-value
theorem), not merely interpolate one-variable endpoint values.

Second, the endpoint conditions alone are vacuous. Given arbitrary functions
`left right : R -> C`, the affine formula

```text
((3/2)-sigma) * left(t) + (sigma-(1/2)) * right(t)
```

has the requested values at `sigma=1/2` and `sigma=3/2`. It supplies no
holomorphy, functional equation, pole structure, residue identity, or decay.
Consequently a `Function.extend` or abstract interpolation construction cannot
close the physical H15 bridge.

These two stop tests are formalized in
`proofs/NBMellinTools/NB15CompletedPairingKernel.lean`.

## What is now proved

The new module proves, with no project axiom and no `sorry`:

1. `affineBoundaryInterpolator_half` and
   `affineBoundaryInterpolator_threeHalf` for arbitrary endpoint data;
2. the same trivial interpolation specialized to the literal certified NB8
   numerator and the literal H15 right-line aggregate;
3. `completedPairingKernel_conj_diagonal`, identifying the conjugate diagonal
   of the two-variable pairing with `Complex.normSq`;
4. `certifiedCriticalLineEnergy_eq_pairingDiagonalIntegral`, expressing the
   already certified energy exactly as the real diagonal integral of the
   physical two-variable kernel;
5. `h15ActiveContourPairingKernel_threeHalfDiagonal`, identifying the right
   diagonal with the squared norm of the full signed H15 aggregate.

This is a type correction and a non-vacuity test. It does not assert that the
two kernels are analytic continuations of one another.

## Audit of the proposed tasks

### A1: completed-integrand interface

The boundary-only version is rejected by the compiled affine-interpolation
stop test. It should be replaced by a two-variable package requiring:

- separate meromorphy/holomorphy in both variables on the relevant product
  domains;
- the physical conjugate-diagonal identity;
- the exact H15 right-edge diagonal identity;
- the same regulator and correction/residue ledger on both sides;
- horizontal-boundary disappearance and justified sum--integral exchange.

Existence of such a package remains open.

### A2: certified pole locations

The useful content already exists in `NB12BBLSH15Rectangle.lean`. The theorem
`h15ActiveContourAggregate_eq_all_poles_removed` gives the exact displayed
four-term polar decomposition: cubic, quadratic, and simple terms at `s=0`,
plus the additional simple term at `s=1`. The pole-removed part is analytic
for real part below `2`.

Care is required with the word "exact". The project proves that the cubic
coefficient is nonzero at cutoff `n=2`, and gives a quadratic non-vanishing
stop test for particular damping values. This does not prove that every
displayed coefficient is nonzero for every cutoff. The correct uniform claim
is therefore an exact Laurent decomposition with **possible poles of the
displayed orders**, plus the already certified specialized non-removability
results.

### A3: rectangle boundary theorem

This is already proved. The theorem
`rectangularBoundaryIntegral_h15ActiveContourAggregate` evaluates the closed
boundary as the complete two-residue ledger. The stronger operational form
`h15CorrectedThreeHalfRightEdge_eq_left_sub_horizontal` keeps the correction
inside the signed identity and transfers the corrected right edge to the left
edge minus the horizontal pair.

Neither theorem identifies the left edge with the physical NB8 numerator.

### B1: manual interpolation

Rejected. `Function.extend`, affine interpolation, or holomorphic
interpolation from values on two vertical lines does not construct the needed
meromorphic functional equation. In general, arbitrary boundary data on two
lines are not the boundary values of one meromorphic function with prescribed
poles and growth.

### C1 and D1: decay candidates and numerics

Useful only as diagnostics. They cannot turn an unproved normalization into
an identity, and finite numerical decay cannot prove the limiting signed
estimate. They should follow, not precede, construction of a non-vacuous
common kernel.

## Correct next theorem

The next exact target is a **two-variable normalization theorem**. It must
construct a single separately meromorphic kernel (or an equivalent bounded
operator family) whose two certified boundary realizations are:

```text
physical boundary:
  conjugate(certifiedMellinNumerator n s) * certifiedMellinNumerator n s

H15 contour boundary:
  conjugate(h15ActiveContourAggregate n s) *
    h15ActiveContourAggregate n s,
```

with the four-sector correction ledger retained. The theorem must also
specify the exact normalizing factors and regulator before any limiting
argument.

Even success here would not prove RH automatically. One would still need:

1. a legitimate two-variable contour or boundary-value theorem;
2. vanishing horizontal terms and global sum--integral exchange;
3. a signed asymptotic estimate forcing the resulting certified energy to
   tend to zero.

The last item is the genuine RH-strength gate.

## Verification

`lake build NBMellinTools.NB15CompletedPairingKernel` completed successfully
with 8,539 jobs. The full `lake build` completed successfully with 8,649
jobs. `#print axioms` on the four representative theorems reported only
`propext`, `Classical.choice`, and `Quot.sound`; there is no project axiom or
`sorry` in the new module.
