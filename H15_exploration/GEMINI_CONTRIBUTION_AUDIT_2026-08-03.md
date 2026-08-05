# Audit of the Gemini H15 inventory

Date: 2026-08-03

This note checks the report
`h15_exploration/H15_proved_theorems_and_elements_report.md` against the
current Lean sources.  The original report is retained outside this repository
for provenance.  This is the corrected version to use for planning work in
`riemann-github`.

## Conclusions

Gemini correctly identified the most important logical fact: the public
NB8--NB14 development does not contain an unconditional proof of the Riemann
hypothesis, and the NB15 exploration has no inhabitant of
`IsNymanBeurlingEnergySpecialization`.

The report is also right that the NB12 corpus contains a large amount of exact,
useful finite algebra.  However, four claims need correction before the report
can guide the next implementation.

## Corrections

### 1. Current NB12 file count

At this snapshot there are 149 files matching
`proofs/NBMellinTools/NB12*.lean`, not 151.  A textual audit finds no `sorry`,
`sorryAx`, project `axiom`, or `opaque` declaration in those 149 files.  This
is a source-level fact; it does not turn hypothesis structures declared in
those files into constructed analytic estimates.

### 2. The Burnol calibration is synthetic

`scripts/burnol_calibration.py` does not evaluate the literal NB12 ledgers.  It
defines

```text
A_N = 1.5 / log N
C_N = 0.8 / log N
G_N = 1.2 / log N
H_N = 2.1 / log N.
```

Consequently its displayed joint value is exactly `5.6 / log N`, and division
by the hard-coded Burnol coefficient `0.0461914 / log N` gives the constant
ratio

```text
5.6 / 0.0461914 = 121.2346887...
```

for every test point.  The JSON output therefore contains no numerical
evidence about the true NB8 energy or the parameterized NB12 expressions.  It
must be labelled model/synthetic data and must not be cited as calibration or
non-vacuity evidence.

### 3. Several named “bounds” are open interfaces or stop tests

The following distinctions are essential.

- `H15GCDStratifiedProgressionPowerSaving` is a structure containing the
  desired signed estimate.  No inhabitant is constructed.  The proved result
  is an exact gcd reindexing and a transfer from that hypothesis to an earlier
  power-saving hypothesis.  The same file proves that the available absolute
  balanced exponent is zero, not negative.
- `H15DirectAdditiveLargeSieve`,
  `H15SignedThreeHalfL1Tightness`,
  `H15PostFEConstantModeModulusDecayData`, and
  `H15SignedSquareDivisorPowerSaving` are likewise analytic input structures,
  not completed estimates.
- `NB12BBLSH15FinalBoundaryKloostermanNormAudit.lean` proves exact Parseval and
  Cauchy--Schwarz baselines.  Its conclusion is negative for closure: after
  completion it supplies no extra modulus power.
- `NB12BBLSH15BettinChandeeAudit.lean` is also a stop test.  The audited
  Bettin--Chandee exponents decay only above the frequency threshold
  `R > N^(3/4)`.  They do not control the fixed or low-frequency sector.

Thus Bettin--Chandee 2015 is relevant to a high-frequency subrange, but the
current formal audit rules out describing it as the direct solution to the
retained finite middle window.

### 4. WP1--WP2 are not known to be purely finite algebra

The exact active chain currently has two disconnected sides.

On the certified side:

```text
NB8.logTaperL2Error
  = NB9.bdQuadraticForm
  = NB11.vasyuninCoupledExpression.
```

NB11 constructs the pointwise `VasyuninGramEvaluation`; this part is
unconditional.  Only decay of the coupled Vasyunin expression is open.

On the PostFE side:

```text
NB12.h15PostFEActualVaryingRowEnergy frequencySupport n g U Q t
  = sum over r in frequencySupport of
      (h15PostFEActualJointCorrectionTransform n g U Q r t)^2
  = affine + 2 * (constant + collision + harmonic).
```

This is a local, fixed-`t`, fixed-block energy.  By contrast,
`NB8.logTaperL2Error` is the original global positive-half-line integral.  No
current theorem identifies one local PostFE tuple with that global energy,
nor is there a theorem assembling all blocks and the spectral integration.

Accordingly the present NB15 predicate

```lean
IsNymanBeurlingEnergySpecialization
  (parameters : ℕ → PostFEParameters)
```

is an honest conditional interface, but its *shape is provisional*.  A single
tuple per stage is not justified.  The correct realization may require a
finite block sum, a vertical integral, a limiting contour identity, or all
three.  The global transform must be derived before claiming that WP2 is
finite bookkeeping.

## Verified reusable results

The following items are genuine proved results and should remain in the active
inventory.

1. The NB8 log-taper decay target implies the Riemann hypothesis.
2. NB9 gives the exact correction-plus-Gram expansion.
3. NB11 gives the unconditional Vasyunin Gram evaluation and the exact coupled
   cotangent expression.
4. NB12 gives exact finite Laurent ledgers, Abel regularization, Estermann
   compatibility, pole subtraction, and many finite reindexings.
5. The PostFE local energy has the exact correction-preserving four-component
   normal form, including the factor `2`.
6. The divisor-square dyadic estimate and the ultra-high frequency tail bound
   are proved; the latter does not touch the retained low/middle sector.
7. The cubic-pole diagnostic is nonzero, so the polar/correction ledger cannot
   be discarded.
8. The absolute-majorant, Kloosterman-norm, direct-phase, and
   Bettin--Chandee-exponent audits precisely document why the immediate
   absolute or separated-coefficient routes do not close H15.

## Correct next target

Do not try to inhabit the current scalar NB15 specialization by choosing
ad-hoc values of `g`, `U`, `Q`, `t`, or `frequencySupport`.

First construct an exact assembly map with these checkpoints:

1. Start from the unconditional NB11 identity for
   `vasyuninCoupledExpression`.
2. Identify the exact finite H15 Laurent-row numerator already used by the
   NB12 contour modules, including both orientations and the retained
   `bdCorrectionTerm`.
3. Prove the pre-functional-equation equality between the Vasyunin cotangent
   aggregate and that complete Laurent-row numerator.
4. State explicitly every subsequent analytic operation: Abel boundary,
   contour displacement, functional equation, vertical integration, and
   dyadic/block assembly.
5. Define the global PostFE energy only after those operations determine its
   actual index and measure type.
6. Replace the provisional scalar NB15 predicate with the resulting exact
   aggregate and prove its equality to `NB8.logTaperL2Error`.

Only then should the signed decay problem be transferred to the PostFE normal
form.

## Literature consequence

The immediate literature priority is not to apply Bettin--Chandee blindly.
The first priority is to identify the exact global transform on which a paper
would act.  Once that object exists, the already proved exponent and phase
audits should be rerun against it.  The present audits show:

- the literal PostFE phase is direct rather than the inverse phase required by
  the immediate Bettin--Chandee substitution;
- fixed and low frequencies receive no saving from the audited exponents;
- a future successful result must preserve the joint coefficient and the
  correction ledger.

This keeps Bettin--Chandee, Estermann/Voronoi, and Motohashi/Kuznetsov as
possible analytic inputs without claiming that any currently cited theorem
already proves the missing H15 estimate.
