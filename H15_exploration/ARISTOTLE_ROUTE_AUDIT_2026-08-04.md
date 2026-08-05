# Aristotle Path A/B audit against the certified H15 phase

**Date:** 2026-08-04  
**Lean stop test:** `proofs/NBMellinTools/NB15AristotleRouteAudit.lean`  
**Status:** phase diagnosis complete; direct Bettin--Chandee activation rejected

## Executive result

The Aristotle reports are useful literature surveys, but they explicitly say
that the H15 context was absent from their workspace. Their conclusions are
therefore a conditional decision tree. Applying that tree to the actual Lean
definitions gives a definitive answer:

\[
  \boxed{\text{the post-FE H15 phase is }e_q(\pm r u),
  \text{ not }e_q(\pm r\bar u).}
\]

It is a direct additive product phase with a variable modulus. It is not the
coupled-denominator phase `e(theta*h/(mn))` for which Aristotle found a cheap
reciprocity reduction to Bettin--Chandee.

The reason is structural. An H15 Laurent row already stores the inverse
residue `u^{-1} mod q`. The Estermann functional equation inverts that row
numerator again, so the two inversions cancel.

## Machine-checked results

The existing source already proves the general collapse in
`NB12BBLSH15BettinChandeeInstantiation.lean`:

- `bblsEstermannInverseResidue_h15InverseResidueNumerator`;
- `bblsAdditiveCharacter_h15_doubleInverse_eq_directPhase`;
- `h15PostFunctionalEquationPhaseIsDirect`;
- the orientation-zero and orientation-one row specializations.

The new audit adds three non-vacuous tests:

1. `h15DirectPhase_ne_bettinChandeeInversePhase_example` proves that at
   `(r,u,q)=(1,2,5)` the direct H15 phase differs from the inverse-residue
   Bettin--Chandee phase.
2. `h15DirectAdditiveUnitPhase_eq_one_of_modulus_dvd_frequency` proves that
   both orientations are exactly constant when `q | r` on a reduced row.
3. `h15Aristotle_directLargeSieve_quadratic_stopTest` records that the
   elementary direct-additive large-sieve exponent is zero at the quadratic
   transition; saving occurs only above it.

This supplies an explicit counterexample, an exact resonance family, and a
quantitative stop test.

## Path B: Bettin--Chandee

### Verdict

**Not directly applicable to the certified H15 post-FE block.**

Bettin--Chandee Theorem 1 estimates separated coefficients against a genuine
inverse-residue phase. Reindexing `u` by `u^{-1} mod q` restores that phase,
but changes an H15 coefficient `alpha(u)` into
`alpha(u^{-1} mod q)`. This now depends jointly on the residue variable and
the modulus, so it no longer has the separated coefficient form required by
the theorem.

The perturbation allowance in Bettin--Chandee Remark 1 does not repair this:
it tolerates a smooth phase perturbation after the inverse-residue structure
is present; it does not turn a direct phase into an inverse phase while
preserving coefficient separation.

The Aristotle report's negative criterion is nevertheless valuable:
amplification gains power only when a genuine multiplicative inverse survives
to the terminal complete sum. For H15 it does not.

## Path A1: Euler--Maclaurin

### Formalization sketch

A reusable theorem would package

\[
 \sum_{a<n\le b}f(n)
 = \int_a^b f(x)\,dx
 + \frac{f(a)+f(b)}2
 + \sum_{j=1}^{K}\frac{B_{2j}}{(2j)!}
   \bigl(f^{(2j-1)}(b)-f^{(2j-1)}(a)\bigr)
 + R_K
\]

together with an explicit integral bound for `R_K`. The endpoint terms are
coupled differences, so this is useful infrastructure for the smooth
Archimedean and contour weights.

### H15 stop test

The actual primitive-variable coefficient contains

\[
  \frac{\mu(gu)}{u}\frac{\log(N/(gu))}{\log N}.
\]

This is not the restriction of a smooth function to the integers. Direct
Euler--Maclaurin on the complete H15 row is therefore invalid. One must first
separate the arithmetic coefficient, typically by Abel summation. The price
is a uniform bound for Möbius partial sums, possibly with an additive twist;
that is analytic input rather than Euler--Maclaurin bookkeeping.

**Use:** smooth endpoint/contour sectors after arithmetic separation.  
**Not proved by it:** signed Möbius cancellation or complete low-sector decay.

## Path A2: stationary phase / van der Corput

### Formalization sketch

The reusable missing infrastructure is:

- a first-derivative Kuzmin--Landau estimate, uniform in an additive rational
  shift;
- second- and higher-derivative van der Corput tests;
- a parameter-uniform stationary-phase theorem with explicit endpoint error.

For a smooth phase `phi(x)=r*x/q+psi(x)`, all derivatives of order at least
two come only from `psi`, while the first-derivative bound depends on the
distance of `r/q+psi'(x)` to an integer.

### H15 stop test

For the literal direct phase `r*u/q`, the phase is linear in `u`. Hence all
derivatives of order at least two vanish. The first-derivative estimate
degenerates exactly on `q | r`, where Lean proves the phase is identically
one. In addition, the Möbius/log-taper coefficient is not a smooth amplitude
to which ordinary stationary phase applies directly.

**Use:** nonresonant smooth pieces after coefficient separation.  
**Not proved by it:** the resonant quotient fibers or their retained
correction.

## Path A3: reciprocity

### Formalization sketch

The elementary identity

\[
 a\bar m/n+a\bar n/m-a/(mn)\in\mathbb Z
\]

is already formalized in Aristotle's isolated `Reciprocity.lean` project and
is a good reusable finite-arithmetic lemma.

### H15 stop test

That identity starts with inverse residues. The certified post-FE H15 phase
has none. Applying `u -> u^{-1}` recreates the same joint `(u,q)` coefficient
dependence that blocks Bettin--Chandee. Bettin--Conrey period-function
reciprocity remains structurally relevant on the **pre-FE** Estermann/Vasyunin
side, but using it must preserve the elementary endpoint ledger and still
requires a signed asymptotic estimate.

**Use:** an exact pre-FE transformation or a correction-preserving Voronoi
route.  
**Not proved by it:** post-FE separated trilinear decay.

## Tractability ranking

| Rank | Target | Lean tractability | H15 payoff now |
|---|---|---:|---:|
| 1 | Exact resonant/nonresonant decomposition and quotient-fiber handoff | High; finite algebra already developed | Highest |
| 2 | Kuzmin--Landau / finite geometric bound on nonresonant smooth rows | Medium | Limited to nonresonant sector |
| 3 | Explicit Euler--Maclaurin with coupled endpoint remainder | Medium | Useful infrastructure, not closure |
| 4 | Elementary Kloosterman reciprocity | High | Already known; phase mismatch limits use |
| 5 | Uniform stationary phase with endpoint coalescence | Low | Large infrastructure; does not handle Möbius coefficients by itself |

## Correct next target

Do not start a general Euler--Maclaurin or stationary-phase library as if it
were already an H15 proof. The next H15-specific target is:

1. connect the direct row resonance `q | r` to the existing correction-coupled
   quotient-fiber ledgers;
2. split the complete finite middle window exactly into resonant and
   nonresonant signed sectors;
3. prove the best elementary estimate on the nonresonant sector;
4. leave the resonant sector and its correction in one signed expression;
5. run an exponent test before importing further analytic machinery.

The new `NB15DirectAdditiveResonantQuotient.lean` module completes the linear
reindexing `r=q*k` and proves that both orientations collapse to the
phase-free factor `1+cos(pi*s)` on the resonant support.

The project also contains later-stage quotient infrastructure in
`NB12BBLSH15PostFEDegenerateQuotientLedger.lean`, but its quotient is
`q*q'/p` and is produced only after a quadratic collision expansion. It is
not the row-level quotient `r/q`.

`NB15DirectAdditiveResonantFixedHeight.lean` now completes the honest
fixed-height expansion. It proves the finite sum--integral interchange, the
diagonal/ordered-cross-pair norm-square identity, the exact
collision/noncollision partition, and the gcd-reduced common-multiplier
parametrization of `q*k=q'*l`. This is a useful stop test: `q*q'/p` still does
not occur in the literal square. Its modulus `p` belongs to the later
character-average/correction projection. The next bridge must formalize that
projection and derive the existing NB12 collision ledger from it; direct
identification remains a type and variable-role error.

## Honest conclusion

Aristotle found useful references and correctly described when each classical
method can work. It did not receive the actual H15 source, and its statement
that all three Path A techniques directly close H15 is too strong. After
specialization:

- the cheap Bettin--Chandee route fails the exact phase test;
- Euler--Maclaurin and stationary phase can treat smooth/nonresonant pieces;
- the signed resonant Möbius/correction ledger remains the genuine gate.

No unconditional H15 decay or RH theorem is obtained by this audit.
