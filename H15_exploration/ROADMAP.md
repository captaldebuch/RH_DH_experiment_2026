# H15 exploration roadmap

## Status and scope

This directory tracks work that is deliberately excluded from the public
`NBMellinTools` umbrella until its definitions and analytic inputs are proved.
It must not be described as an unconditional proof of the Riemann hypothesis.

The Claude NB16--NB20 scaffold was removed rather than repaired because its
Kuznetsov, Poisson, Möbius, and dispersion declarations did not encode the
claimed mathematics.  Some were tautologies, one target was inconsistent,
and the final theorem depended on `sorryAx`.

The replacement exploration module is:

- `proofs/NBMellinTools/NB15JointLedgerUnification.lean`
- `proofs/NBMellinTools/NB15PreFEAssembly.lean`
- `proofs/NBMellinTools/NB15GCDReindex.lean`
- `proofs/NBMellinTools/NB15DirichletAbelBoundary.lean`
- `proofs/NBMellinTools/NB15RationalSineEndpoint.lean`
- `proofs/NBMellinTools/NB15HurwitzZeroEndpoint.lean`
- `proofs/NBMellinTools/NB15EstermannVasyuninAtZero.lean`
- `proofs/NBMellinTools/NB15EstermannGramAssembly.lean`
- `proofs/NBMellinTools/NB15EstermannRowAssembly.lean`
- `proofs/NBMellinTools/NB15GlobalPostFEAssembly.lean`
- `proofs/NBMellinTools/NB15VerticalFrequencyPairing.lean`
- `proofs/NBMellinTools/NB15CorrectionPreservingRectangle.lean`
- `proofs/NBMellinTools/NB15AristotleRouteAudit.lean`
- `proofs/NBMellinTools/NB15DirectAdditiveResonanceSplit.lean`
- `proofs/NBMellinTools/NB15DirectAdditiveResonantQuotient.lean`

It is separately buildable but is not imported by `proofs/NBMellinTools.lean`.

## What is now proved

### 1. Certified Nyman--Beurling endpoint

The active NB8 route defines the exact log-taper energy

```lean
NB8.logTaperL2Error : ℕ → ℝ
```

and proves

```lean
NB8.LogTaperL2Decay → RiemannHypothesis
```

without asserting the decay hypothesis.

### 2. Exact local PostFE energy

NB12 defines the literal parameterized energy

```lean
NB12.h15PostFEActualVaryingRowEnergy
  frequencySupport n g U Q t
```

and proves its correction-preserving normal form

```text
actual energy
  = affine norm imbalance
    + 2 * (signed constant mode
           + signed static non-diagonal gap
           + signed harmonic ledger).
```

The factor `2` and the signed grouping are part of the theorem.  They must not
be replaced by four separately nonnegative majorants.

### 3. Exact NB15 parameterization

NB15 now aliases the four literal NB12 expressions through
`NB15.PostFEParameters` and proves

```lean
NB15.jointResidualEnergy_eq_actualVaryingRowEnergy
```

with no `sorry` and no new axiom.

### 4. Honest Nyman--Beurling specialization interface

NB15 defines

```lean
NB15.IsNymanBeurlingEnergySpecialization parameters
```

to mean that the chosen PostFE family is pointwise identical to
`NB8.logTaperL2Error`.  Under this explicit certificate, NB15 proves the exact
pointwise equality, transports decay, and invokes the already certified NB8
implication to RH.

No inhabitant of this specialization predicate is currently constructed.
That is intentional: the present NB12 files prove local PostFE identities but
do not yet prove the global stage-by-stage assembly into the NB8 energy.

## The actual remaining programme

### WP1a -- Certified pre-FE source (complete)

`NB15PreFEAssembly.lean` now proves that `NB8.logTaperL2Error` is exactly the
complete NB11/NB10 Vasyunin assembly, splits its cotangent sector into the
gcd-primitive interior and the retained endpoint complement, and verifies
the active NB12 log-taper and row-weight normalizations.  See
`PRE_FE_ASSEMBLY_AUDIT_2026-08-03.md`.

This does not yet identify the analytic NB12 Laurent aggregate with the
interior Vasyunin sector.  That identification is the next exact target.

### WP1b -- Exact gcd reindexing (complete)

`NB15GCDReindex.lean` proves, without analytic assumptions:

1. exact one-based identification of the NB9 Gram term;
2. Gram homogeneity
   `G(g*a,g*q) = g⁻¹ G(a,q)`;
3. bijective reindexing by `g = gcd(h,k)` and the coprime quotient pair;
4. unconditional replacement of each primitive Gram entry by the NB11
   Vasyunin formula;
5. exact separation of the `a,q >= 2` interior and the primitive endpoint
   complement;
6. the certified identity

```text
NB8.logTaperL2Error n
  = preFECorrection n
      + oneBasedVasyuninInterior (n+2)
      + oneBasedVasyuninEndpoint (n+2).
```

### WP1c -- Genuine rational Estermann endpoint (complete)

The active endpoint is no longer a special-value hypothesis:

1. `NB15DirichletAbelBoundary.lean` proves the reusable real
   Dirichlet--Abelian boundary theorem;
2. `NB15RationalSineEndpoint.lean` proves the actual analytic identity
   `sinZeta(j/q, 1) = π(1/2-j/q)` for nonzero residues;
3. `NB15HurwitzZeroEndpoint.lean` derives the actual rational Hurwitz value
   at zero and substitutes it into the active finite Hurwitz continuation;
4. `NB15EstermannVasyuninAtZero.lean` proves the complete finite DFT and the
   genuine active endpoint

```text
D(0, inverse(a)/q) = 1/4 - (i/2) V(a,q)
```

   for positive reduced rows;
5. `NB15EstermannGramAssembly.lean` replaces both Vasyunin orientations by
   those active Estermann values and proves

```text
NB8.logTaperL2Error n
  = preFECorrection n
      + oneBasedEstermannInterior (n+2)
      + oneBasedVasyuninEndpoint (n+2).
```

All five modules contain no `sorry` or project axiom. Their audited public
endpoints depend only on `propext`, `Classical.choice`, and `Quot.sound`.

The remaining WP1 bridge is therefore not a gcd-indexing or special-value
question. It is the exact global contour/functional-equation assembly that
connects this certified Estermann interior, while retaining the correction
and endpoint sectors, to the local NB12 PostFE transform.

### WP1d -- Exact NB12 row and residue-amplitude assembly (complete)

`NB15EstermannRowAssembly.lean` proves that the two orientations of every
primitive interior row are exactly the two orientations of NB12's actual
finite H15 Laurent row family. Invalid rows remain in the common finite
cube with zero weight. It then proves the global finite reindexing

```text
oneBasedEstermannSpecialValueInterior N
  = h15LaurentEstermannZeroAggregate N.
```

The latter aggregate is identified with the imaginary part of NB12's
literal additional-residue amplitude:

```text
h15LaurentEstermannZeroAggregate (n+2)
  = im (h15AdditionalResidueAmplitude n).
```

Consequently the certified energy has the exact contour-vocabulary form

```text
NB8.logTaperL2Error n
  = h15CertifiedElementaryEndpointLedger n
      + im (h15AdditionalResidueAmplitude n).
```

This gives a definitive stop test. The proved adaptive contour bound controls
`h15ContourDamping n * h15AdditionalResidueAmplitude n`, whereas the energy
contains the undamped amplitude. Since the damping tends to zero, its
vanishing cannot be divided through to obtain energy decay. The next bridge
must preserve and evaluate the undamped amplitude together with the
elementary/endpoint ledger; adaptive residue suppression alone is not it.

The same module makes the obstruction exact:

```text
inverse(h15ContourDamping n) * h15GlobalAdditionalResidue n
  = h15AdditionalResidueAmplitude n.
```

Thus the contour residue does recover the energy sector, but only after the
precise inverse-damping loss is restored.

### WP1e -- Canonical global PostFE block assembly (complete)

`NB15GlobalPostFEAssembly.lean` constructs the canonical dyadic scale
`2 ^ log2 x`, the complete finite block support, and the exact fiber of rows
in each endpoint-aligned block. It proves that these fibers are precisely the
existing NB12 localizations and that their weighted sum is the full Laurent
row cube.

The linear functional-equation side is now genuinely global:

```text
h15ThreeHalfLowFrequencyAggregate n K t
  = sum r in range (K+1), h15GlobalPostFELinearFrequencySlice n r t.
```

No Laurent row, gcd slice, orientation, or dyadic primitive scale is omitted.
Frequency `r`, height `t`, and the finite cutoff `K` remain visible.

The quadratic audit also retains the exact ordered cross-block ledger:

```text
normSq(global linear slice)
  = sum_blocks normSq(local slice) + signed crossBlockInteraction.
```

Thus summing local quadratic estimates alone is not a global Plancherel
identity; it omits a concrete signed interaction term.

The same module also sums the literal local joint correction transforms and
proves their exact blockwise identity

```text
globalCenteredLiftDefect
  = globalMeanZeroVariation - globalJointCorrectionTransform.
```

The audit gives a decisive type-level stop test. The certified Estermann
amplitude is a **linear** global row sum at `s = 0`; the joint correction
transform is a **quadratic** fixed-frequency, fixed-height projection. Finite
dyadic assembly does not identify them. Their difference is retained as
`h15UndampedPostFEBridgeDefect`, and the certified energy satisfies

```text
logTaperL2Error
  = elementaryEndpointLedger
      + globalJointCorrectionTransform
      + undampedPostFEBridgeDefect.
```

The equivalent formula using `h15GlobalAdditionalResidue` retains the inverse
adaptive damping explicitly. Thus no damped residue estimate is being divided
through.

### WP1f -- Certified Mellin--Plancherel and the missing contour normalization

`NB15VerticalFrequencyPairing.lean` proves the exact compact-height finite
pairing.  It flattens the genuine low-frequency aggregate over the
finite product

```text
range (K+1) × canonical PostFE dyadic blocks
```

and proves pointwise and after integration on `[-T,T]`:

```text
integral normSq(complete low-frequency aggregate)
  = sum_(frequency,block) sum_(frequency',block')
      integral Re(conj(local term) * local term').
```

This is an equality, not an upper bound.  It retains diagonal terms,
cross-frequency terms, cross-block terms, and terms which are simultaneously
cross-frequency and cross-block.  Continuity and compact-interval
integrability of every entry are proved from the existing Gamma-decaying
NB12 frequency terms.

The standard Mellin--Plancherel bridge is now proved in the active hierarchy,
not merely inherited from the old worktree.  The relevant modules are
`FourierCompatibility.lean` and
`MellinPlancherelPositiveHalfLine.lean`.

`NB15CertifiedMellinNormalization.lean` proves in the active hierarchy that:

1. NB8's coefficient is exactly
   `-μ(k+1) * (1 - log(k+1)/log(n+2))`;
2. its negation is the usual positive-sign BCF Dirichlet coefficient;
3. `NB8.logTaperL2Error n` is exactly the complex squared norm of the literal
   certified residual.

`NB15CertifiedMellinTransform.lean` now assembles the already proved NB2
generator transforms into the pointwise identity

```text
Mellin(certifiedResidual)(1/2+it)
  = (1 - zeta(1/2+it) * certifiedDirichletPolynomial(1/2+it)) /(1/2+it)
```

with all finite sum--integral exchanges proved.

`NB15CertifiedMellinPlancherel.lean` proves all NB8-specific measurability,
`L²`, tail, and log-pullback `L¹` estimates and obtains the exact identity

```text
logTaperL2Error n
  = (1/(2*pi)) * integral_R
      norm(certifiedCriticalLineNumerator n t)^2 dt.
```

This completes the physical Mellin--Plancherel bridge unconditionally at each
finite stage.  It does **not** identify that critical-line numerator with the
present Estermann three-halves-line aggregate.  Therefore the finite pairing
theorem is still not a specialization of the certified NB8 energy.

The remaining exact bridge is no longer a finite indexing or finite
Plancherel-expansion problem. It must identify the globally assembled
Estermann object with the Mellin transform (or an exactly normalized contour
image) of the certified residual. Candidate mechanisms are:

1. a vertical Plancherel identity, including the exact measure and all
   Archimedean normalizations;
2. the now-proved explicit frequency pairing followed by the `t`-integral,
   together with an exact theorem identifying its input function;
3. a correction-preserving contour identity which evaluates the undamped
   endpoint amplitude before any adaptive-damping limit.

Required deliverable: an exact kernel-normalization identity connecting the
physical Mellin residual to `h15ThreeHalfLowFrequencyAggregate` plus its high
tail and conserved residue/endpoint ledger.  It must then yield an exact
identity for `h15UndampedPostFEBridgeDefect`, or prove that the proposed
quadratic PostFE family is not the image of the linear contour aggregate. A
pointwise identity at one `(r,t)`, or the finite pairing identity alone,
cannot close this work package.

### WP1g -- Certified correction-preserving closed rectangle (complete)

`NB15CorrectionPreservingRectangle.lean` instantiates the generic rectangle
ledger with no arbitrary analytic functions:

- the active bulk is the literal H15 finite Estermann row aggregate;
- the pole-subtracted bulk is `h15AllPoleRemoved`;
- the retained correction is the actual NB8 `preFECorrection`;
- the remaining elementary endpoint is the certified elementary Gram sector
  plus the retained primitive endpoint sector.

The normalized closed boundary is defined from the genuine boundary
integral.  Using `rectangularBoundaryIntegral_h15ActiveContourAggregate` and
the zero boundary of `h15AllPoleRemoved`, the module constructs an actual
inhabitant of `BBLSCorrectionPreservingRectangleData` and proves its expanded
four-sector ledger.

It also combines the Mellin--Plancherel theorem with the certified residue
assembly:

```text
certifiedCriticalLineEnergy n
  = certifiedElementaryEndpointLedger n
      + im(damping(n)^(-1) * globalAdditionalResidue(n)).
```

This exposes rather than removes the inverse-damping loss.  The closed
rectangle still does not identify either oriented vertical edge with the
certified critical-line numerator.  The next target is a common
two-variable completed integrand and an `L²` boundary-value theorem linking
the physical edge to the existing H15 contour edge.

### WP1h -- Quadratic contour type and boundary-only stop test (complete)

`NB15CompletedPairingKernel.lean` corrects the type of the proposed WP4
completed integrand. A one-variable meromorphic contour argument acts
linearly, but the certified energy contains a squared norm. The module
therefore defines the separately variable sesquilinear kernel

```text
K_F(z,w) = conjugate(F(conjugate(z))) * F(w)
```

and proves that its conjugate diagonal is exactly `normSq (F(s))`. It then
constructs the literal physical and H15 contour kernels and proves:

```text
certifiedCriticalLineEnergy n
  = (1/(2*pi)) * integral_R Re(K_physical(conj(s_t),s_t))

K_H15(conj(3/2+it),3/2+it)
  = normSq(h15VerticalAggregate n (3/2) t).
```

The same module proves a decisive non-vacuity stop test: arbitrary left and
right boundary functions admit a naive affine interpolation with the desired
values at `sigma=1/2` and `sigma=3/2`. Thus endpoint equalities alone, and in
particular a `Function.extend` construction, contain no analytic information.
They do not imply meromorphy, a functional equation, residue matching, or
energy decay.

Tasks labelled "pole locations" and "rectangle identity" in the later WP4
proposal are not new gates. Their valid content already exists in
`NB12BBLSH15Rectangle.lean` and `NB12BBLSH15SignedRightLine.lean`. The next
open target is a non-vacuous, separately meromorphic two-variable
normalization (or equivalent operator boundary theorem) between the physical
pairing kernel and the active H15 pairing kernel, with one common regulator
and the certified correction ledger. Even such an identity must still be
followed by a genuine signed asymptotic decay estimate.

### WP1i -- Physical/contour singularity-order stop test (complete)

`NB15PhysicalContourSingularityMismatch.lean` compares the local orders at
zero of the two raw functions proposed for the completed bridge. It proves

```text
lim_(s -> 0, s != 0) s^3 * certifiedMellinNumerator(n,s) = 0

lim_(s -> 0, s != 0) s^3 * h15ActiveContourAggregate(n,s)
  = h15GlobalThirdOrderCoefficient(n).
```

Since the second limit is nonzero at `n=2`, the two functions are formally
unequal. More strongly, no scalar multiplier continuous at zero can turn the
physical numerator into the active Estermann aggregate away from the two
displayed poles.

Thus the missing normalization is not a constant or regular interpolation.
It must use a singular completion factor, explicit polar subtraction with a
separately transported ledger, or a genuine residue/boundary-projection
operator. The next target must also separate the physical spectral variable
from the auxiliary Mellin--Barnes contour variable; treating both as the same
complex variable is incompatible with the certified Laurent data.

### WP1j -- Two-variable bridge type audit (complete; target corrected)

`NB15TwoVariableBridgeAudit.lean` tests the proposed role-differentiated
bridge before introducing another analytic interface. It proves that two
prescribed slices of a function `T(u,w)` force only their scalar corner
compatibility. Conversely, once that compatibility holds, the explicit
additive splice

```text
T(u,w) = physical(u) + contour(w) - physical(u0)
```

realizes both slices. Therefore raw two-slice recovery is as non-diagnostic
as the affine boundary interpolation rejected in WP1h.

The WP1i function inequality supplies a certified anchor at `n=2` where no
two-variable function can simultaneously contain the entire raw physical
function and raw Estermann aggregate as intersecting slices. The two sides
must first be compared at their correct mathematical levels.

The module then proves all three valid pre-tests with the variables kept
separate:

1. the physical critical-line numerator is recovered exactly in the real
   spectral variable `t`;
2. the auxiliary complex variable `w` retains the cubic pole at zero and the
   additional residue at one;
3. the Hermitian physical diagonal, after integration in `t`, equals the
   certified elementary ledger plus the inverse-damping-rescaled `w=1`
   residue.

Thus the genuine finite bridge is already the exact integral/residue
identity

```text
(1/(2*pi)) * integral physicalPairingDensity
  = certifiedElementaryEndpointLedger
      + im(damping^(-1) * globalAdditionalResidue).
```

A common pointwise `T_n(u,w)` is not justified and is not required for this
finite equality. The corrected next target is an exact complete-transform
representation of `h15UndampedPostFEBridgeDefect`: transport the undamped
residue amplitude through all frequencies and dyadic blocks while retaining
the polar/endpoint ledger and inverse-damping factor. Only after that exact
identity may a signed decay estimate be attempted.

### WP1k -- Complete linear PostFE transform and two-defect audit (complete)

`NB15UndampedDefectRepresentation.lean` assembles every canonical dyadic
block and every Estermann frequency, including the genuine infinite high
tail. It proves that this complete linear assembly is exactly the corrected
three-halves right edge and is independent of the arbitrary low/high cutoff:

```text
completeLinearPostFERightEdge n K T
  = correctedThreeHalfRightEdge n T.
```

The full first-order/additional-residue ledger is retained. The stop test
proves that omitting it changes the transform by exactly
`-2*pi*I*contourResidueLedger`.

The audit also corrects the proposed target's mathematical level. The
functional equation acts on a linear aggregate, whereas
`globalPostFEJointCorrectionTransform n r t` is a fixed-frequency,
fixed-height quadratic projection. Lean proves the exact decomposition

```text
undampedPostFEBridgeDefect
  = endpointToLinearPostFEDefect
      + linearToQuadraticPostFEMismatch.
```

Consequently the quadratic object is not an exact complete-transform
representation of the undamped residue. The inverse damping remains explicit
in the endpoint-to-linear term. The complete linear edge also equals the
oriented left vertical edge minus the horizontal pair, so the corrected WP1l
target is to evaluate or control that residue-versus-boundary expression.

No decay theorem is obtained in WP1k.

### WP1l -- Exact endpoint extraction from the complete boundary (complete)

`NB15EndpointBoundaryExtraction.lean` proves the correct finite contour
normalization. If `B_n(σ_L,T)` denotes the closed active H15 boundary divided
by `2*pi*I`, then every admissible rectangle satisfies

```text
B_n = globalFirstOrderCoefficient n + globalAdditionalResidue n.
```

Consequently

```text
additionalResidueAmplitude n
  = damping(n)^(-1) * (B_n - globalFirstOrderCoefficient n).
```

The complete boundary is also expanded exactly as the horizontal pair plus
the oriented right vertical edge minus the oriented left vertical edge. Its
normalized value is independent of the admissible left line and height.

The correction stop test proves that omitting the first-order subtraction
introduces exactly
`damping(n)^(-1) * globalFirstOrderCoefficient n`. Since the damping tends
to zero, that omission cannot be treated as a negligible normalization
choice.

WP1l closes the finite endpoint normalization but proves no cancellation.
The corrected WP1m target is a signed estimate for the centered boundary
numerator `B_n - globalFirstOrderCoefficient n`, strong enough to survive
inverse damping and coupled to the certified elementary endpoint ledger.
Separate absolute estimates on the individual edges are not a substitute.

### WP1m -- Exact coupled-boundary decay interface and three-sector handoff (complete)

`NB15CoupledBoundaryDecay.lean` fixes the admissible rectangle
`sigma_L = -1`, `T = 1` and defines the literal centered numerator

```text
normalizedCompleteBoundary n (-1) 1 - globalFirstOrderCoefficient n.
```

It proves that inverse damping recovers the undamped additional-residue
amplitude and that the complete signed expression

```text
certifiedElementaryEndpointLedger n
  + im (damping(n)^(-1) * centeredBoundaryNumerator n)
```

is pointwise equal to `NB8.logTaperL2Error n`.  Hence
`H15CertifiedCoupledBoundaryDecay` is proved exactly equivalent to
`NB8.LogTaperL2Decay`, and its implication to the Riemann hypothesis is now
formal plumbing with no specialization assumption.

The same module adapts the endpoint-cancellation lemma to discrete `atTop`
limits.  This split is explicitly optional: it requires a genuine prior
evaluation of the elementary ledger and does not make the analytic estimate
easier by definition.

Most importantly, the module gives the non-tautological frequency handoff.
It enlarges the low sector by the elementary ledger and the complete
endpoint-to-linear contour defect, and proves the exact decomposition

```text
certified energy
  = correction-coupled low/endpoint sector
      + im(finite Bettin--Chandee middle window)
      + im(proved ultra-high tail).
```

The ultra-high term already tends to zero.  Therefore the exact remaining
analytic inputs for this route are:

1. `H15CertifiedCorrectionCoupledLowEndpointDecay T`; and
2. the existing `H15BettinChandeeMiddleWindowDecay T`.

These two hypotheses imply `H15CertifiedCoupledBoundaryDecay` and hence RH.
Neither is inhabited in the project.  The first deliberately retains the
correction, inverse damping, and contour-transfer defect inside one signed
expression.

A follow-up stop test rules out the degenerate height schedule.  At `T = 0`
the middle and high integrals vanish identically and the enlarged low sector
is exactly the original certified energy.  The route therefore now requires
`H15DivergingContourHeightSchedule T`: every height is positive and
`T n -> infinity`.

For such a schedule, after assuming finite-middle decay, Lean proves

```text
H15CertifiedCorrectionCoupledLowEndpointDecay T
  <-> H15CertifiedCoupledBoundaryDecay.
```

This is the correct quantitative stop test.  Removing the proved ultra-high
tail does not make the surviving low/endpoint estimate elementary; it remains
the complete H15 analytic gate modulo the finite middle window.

### WP1n -- Signed analytic estimates (open)

Prove one of the following without additional axioms:

1. the complete `H15CertifiedCoupledBoundaryDecay` directly; or
2. for one positive cofinal height schedule `T`, both the correction-coupled
   low/endpoint decay and the finite Bettin--Chandee middle-window decay.

The second route may use the already-certified ultra-high tail automatically.
Decay of the corrected right edge alone is insufficient because it omits the
endpoint-to-linear defect and elementary ledger.

### WP1o -- Aristotle phase and resonance audit (complete)

`NB15AristotleRouteAudit.lean` applies Aristotle's conditional phase decision
tree to the actual H15 definitions.  It proves by a concrete reduced example
that the post-functional-equation direct phase is not the Bettin--Chandee
inverse-residue phase.  It also proves that, on every reduced row, the direct
phase is identically one whenever the modulus divides the frequency, in both
orientations.

The consequences are:

1. the proposed coupled-denominator Bettin--Chandee shortcut is unavailable;
2. higher-derivative van der Corput tests are blind to the literal linear
   phase and the first-derivative test degenerates on `q | r`;
3. Euler--Maclaurin can organize smooth endpoint data but cannot be applied
   directly to the Möbius/log-taper coefficient;
4. the elementary direct large sieve still saves only above the quadratic
   frequency threshold.

`NB15DirectAdditiveResonanceSplit.lean` then performs the exact next step.  It
partitions the literal integrated finite middle window into the signed
`q | r` and `q ∤ r` sectors before taking norms, and refines the certified
energy identity to

```text
energy
  = correction-coupled low/endpoint
      + im(resonant middle)
      + im(nonresonant middle)
      + im(proved ultra-high tail).
```

The correction remains entirely inside the low/endpoint expression.  The
follow-up module `NB15DirectAdditiveResonantQuotient.lean` proves the exact
linear reindexing `r=q*k` and shows that the paired phase on every valid
resonant row reduces to `1 + cos(pi*s)`.

`NB15DirectAdditiveResonantFixedHeight.lean` now supplies the missing
intermediate layer. It defines the quotient aggregate before integration,
proves the exact finite sum--interval-integral interchange, and expands its
pointwise norm square into diagonal and ordered cross-pair terms. The
cross-pair term is then split exactly into equal and unequal physical
frequencies. The actual equality relation is `q_i*k=q_j*l`. Writing
`d=gcd(q_i,q_j)`, Lean proves that it is equivalent to one common multiplier
`h` with `k=(q_j/d)*h` and `l=(q_i/d)*h`. The unequal-frequency term remains
present at fixed height; no orthogonality or decay is assumed.

This audit also corrects the proposed quotient-fiber bridge: the row-level
quotient is `r/q`, whereas the existing norm-square collision quotient is
`q*q'/p`.  They are different objects.  Any bridge must first expand the
resonant linear integral quadratically and derive its collision variables;
they cannot be identified by renaming the quotient.

The next exact target is the character-average projection connecting this
fixed-height three-sector expansion to the older post-FE collision ledger.
That projection must introduce its own modulus `p` and prove where the
quotient `q*q'/p` comes from. Only after this theorem may the two quotient
ledgers be compared. In parallel, the nonresonant sector may be tested
against additive/geometric estimates.
See `ARISTOTLE_ROUTE_AUDIT_2026-08-04.md`.

### WP1p -- Nonresonant divisor hyperbola and complete periods (algebra complete)

`NB15NonresonantDivisorHyperbola.lean` implements the first two stages of
the corrected nonresonant route on the literal H15 expression.  It proves:

1. the exact support identity
   `K + 1 ≤ r < K + 1 + J` together with `q ∤ r`;
2. the exact expansion of the Estermann divisor coefficient into positive
   factor pairs `r = a*b`;
3. the full signed H15 identity retaining
   `(a*b)^(-(3/2+it)) * e_q(±uab)` before taking a norm;
4. an exact slicing by the first factor `a`; and
5. exact cancellation of every complete modulus-`q` block in `b`, for both
   orientations, when `(u,q)=1` and `q ∤ a`.

The targeted build succeeds with 8,634 jobs and the module contains no
`sorry` or project axiom.  It remains outside the active public umbrella,
as do the other NB15 exploration modules.

This is an algebraic success, not a decay theorem.  The next quantitative
stop test is to sharpen the period to `q / gcd(a,q)`, control the two
incomplete boundary fragments, apply finite Abel summation to the complex
weight `(a*b)^(-(3/2+it))`, and total the resulting costs over `a,q,g`.
Only a negative global exponent would close the nonresonant middle sector.
The resonant correction-coupled sector remains independently open.

### WP1q -- Operator Phase 1 stop test (qualified success)

`NB15OperatorAdaptation.lean` constructs a finite operator model directly
from the genuine fixed-height resonant H15 amplitude. The five Aristotle
operator modules advertised by the August 5 integration brief are absent
from both supplied archives, so no claim from those modules is used.

The new module proves that the active amplitudes reassemble the existing
fixed-height quotient aggregate and that the canonical Gram kernel is unique
relative to those amplitudes. With the fixed all-ones observable it proves
the exact identity

```text
Tr(AllOnes * Gram) = normSq(fixed-height resonant aggregate).
```

It also proves the decisive stop test:

```text
re Tr(Gram) = resonant diagonal,
re Tr(collision-projected Gram) = resonant diagonal.
```

Thus an ordinary trace loses all cross terms, including the collision cross
terms. A separate `2 × 2` witness proves formally that trace is not injective.
The operator route may continue only with a canonical **kernel/observable
pair**; the bare assertion that a scalar is the trace of some operator is
vacuous.

Phase 2 must now transport the already certified full energy decomposition to
canonical matrix coefficients without choosing matrices by their desired
trace. See `OPERATOR_PHASE1_STOP_TEST_20260805.md`.

### WP2 -- Prove the global specialization identity

Provisional goal:

```lean
theorem isNymanBeurlingEnergySpecialization_actual :
  NB15.IsNymanBeurlingEnergySpecialization actualParameters
```

or the corrected aggregate/integral analogue determined by WP1.

Required ingredients:

- the NB9 correction-plus-Gram identity;
- the NB10 Vasyunin evaluation;
- the complete NB12 correction ledger, including endpoint and zero modes;
- exact finite reindexing and all normalization constants;
- if required by WP1, the Abel-boundary, contour-shift,
  functional-equation, and sum--integral identities connecting the original
  Vasyunin expression to the PostFE side.

No Kuznetsov formula, numerical calibration, or decay bound belongs in this
work package.  A contour or integral identity does belong here if it is part
of the exact equality rather than an estimate.

Success criterion: `lake env lean` verifies the theorem with no `sorryAx`.

### WP3 -- Identify the single signed analytic target

Only after WP2, rewrite the certified NB8 energy in the smallest exact signed
form supported by NB12.  The target should retain the correction inside the
same expression as the oscillatory terms.

Candidate outputs include:

- the quotient-fiber signed ledger;
- a correction-preserving Estermann boundary expression;
- a finite dyadic dispersion aggregate.

The result of WP3 is a proposition or structure containing one explicit decay
estimate.  It is not to be split into independently vanishing cuspidal,
Eisenstein, and Kloosterman terms unless an exact trace identity proves that
such a split preserves the correction.

### WP4 -- Analytic route selection

Evaluate the exact WP3 target against these routes:

1. Direct Ehm/Abel signed dispersion.
2. Bettin--Chandee trilinear inverse-phase bounds after a verified exponent
   and coefficient-norm test.
3. Correction-preserving Estermann/Voronoi reciprocity.
4. A genuinely bilinear Kuznetsov or Motohashi trace formula, but only after
   the modulus-frequency dependence and admissibility conditions are stated
   exactly.

For each route, record either a proved estimate or a formal stop test.  Do not
replace a failed signed estimate by termwise absolute bounds.

### WP5 -- Conditional closure and, only if available, unconditional closure

Once the WP3 decay estimate is proved:

1. derive `Tendsto NB15.jointResidualEnergy atTop (nhds 0)`;
2. use the WP2 specialization identity to obtain `NB8.LogTaperL2Decay`;
3. apply `NB8.riemannHypothesis_of_logTaperL2Decay`.

Until the WP3 estimate is proved without assumptions, the final theorem must
remain conditional.

## Immediate priorities

1. Use the now-proved exact critical-line energy identity as the physical
   source of every subsequent contour transformation.
2. Use
   `logTaperL2Error_eq_elementaryEndpoint_add_additionalResidueAmplitude_im`
   as the certified finite Estermann-side endpoint.
3. Prove a correction-preserving contour/kernel normalization connecting the
   critical-line numerator to the **complete** PostFE object: low-frequency
   aggregate, high tail, polar ledger, additional residue, and elementary
   endpoint.
4. State each vertical integral, limit, and Abel boundary operation
   separately; do not infer a global equality from a pointwise or truncated
   formula.
5. Preserve the elementary/endpoint ledger and the inverse-damping factor
   through the complete transformation.
6. Only after that equality, isolate the smallest signed decay estimate for the undamped
   amplitude-plus-ledger expression.

The audited Gemini intake and corrections are recorded in
`GEMINI_CONTRIBUTION_AUDIT_2026-08-03.md`.

## Verification policy

Exploration files are checked separately:

```bash
lake env lean proofs/NBMellinTools/NB15JointLedgerUnification.lean
```

The public package is checked independently:

```bash
lake build
lake env lean proofs/NBMellinTools/Audit.lean
```

Before an exploration module may return to the public umbrella:

1. it contains no `sorry`;
2. its public endpoints do not depend on `sorryAx` or project axioms;
3. every named analytic transform is an actual definition, not an arbitrary
   real-valued placeholder;
4. every asymptotic theorem is connected to the exact H15/NB8 expression;
5. the documentation states clearly which estimates remain hypotheses.
