# H15 operator route — Phase 1 stop test

**Date:** 2026-08-05  
**Lean module:** `proofs/NBMellinTools/NB15OperatorAdaptation.lean`  
**Status:** Phase 1 completed with a mandatory correction to the integration brief

## Intake correction

`CODEX_INTEGRATION_BRIEF_OPERATOR_FORMALIZATION_20260805.md` and
`PATH_A_DECISION_CHECKPOINT_20260805.md` say that Aristotle supplied five
verified modules:

- `RequestProject.OperatorTrace`;
- `RequestProject.CharacterSpectrum`;
- `RequestProject.MobiusMatrix`;
- `RequestProject.FredholmTrace`;
- `RequestProject.H15Resonance`.

They are not present in either supplied Aristotle archive. `PATH_A_RESULTS`
contains only an essentially empty `RequestProject/Main.lean`; `PATH_B_RESULTS`
contains an essentially empty `Main.lean` and one `Reciprocity.lean`. The five
modules therefore cannot be treated as verified dependencies.

Phase 1 was instead implemented directly from the genuine H15 definitions in
`NB15DirectAdditiveResonantFixedHeight.lean`.

## Canonical object constructed

For the exact finite support

```text
h15DirectAdditiveResonantQuotientPairSupport n K J,
```

the new module defines:

1. `H15ResonantOperatorIndex n K J`, the subtype of active row/quotient
   indices;
2. `h15ResonantOperatorAmplitude n K J t`, the literal signed H15
   fixed-height summand;
3. `h15ResonantGramKernel`, the canonical kernel
   `conj(A_i) * A_j`;
4. `h15ResonantCollisionKernel`, its projection to equal physical
   frequencies; and
5. `h15AllOnesTestMatrix`, a fixed coefficient-independent observable.

The amplitude is not a new arbitrary function. It includes the existing
Möbius/log-taper row weight, orientation, inverse residue, physical frequency,
and contour damping.

## Exact results

Lean proves:

```text
sum(active amplitudes)
  = h15BettinChandeeResonantQuotientFixedHeightAggregate,
```

and

```text
Tr(AllOnes * Gram)
  = normSq(h15BettinChandeeResonantQuotientFixedHeightAggregate).
```

Thus the complete fixed-height quadratic expression has a canonical finite
trace realization once both the Gram kernel and the observable are specified.
All diagonal, collision-cross, and noncollision-cross terms are retained.

## Stop-test result

The naive operator claim does **not** pass unchanged.

Lean proves that

```text
re Tr(Gram) = resonantDiagonal
re Tr(CollisionKernel) = resonantDiagonal.
```

The collision projection does not make its cross terms appear in the ordinary
trace. They occur only in the full matrix coefficient sum, equivalently in
`Tr(AllOnes * CollisionKernel)`. A concrete `2 × 2` off-diagonal matrix is also
proved nonzero while having the same trace as zero, formally certifying that
trace values do not determine kernels.

Consequently the slogan

```text
H15 sum = Tr(T_N)
```

is vacuous unless `T_N` and the test observable are derived canonically from
the certified H15 amplitude. The valid Phase 1 output is a **tested trace
pair** `(AllOnes, Gram)`, not a bare transfer operator.

## Decision

Phase 1 is a qualified success:

- **pass:** exact canonical amplitude and Gram specialization;
- **pass:** exact trace-pair recovery of the full resonant fixed-height
  energy;
- **pass:** formal vacuity and diagonal-only stop tests;
- **fail as originally written:** ordinary trace of the Gram/collision kernel
  is not the collision energy.

The operator route may continue to Phase 2 only with the observable carried as
part of the structure. Phase 2 should prove a decomposition of the exact
trace pair corresponding to the already certified resonant/nonresonant and
correction-coupled decomposition. It must not define three arbitrary matrices
merely by forcing their traces to have the desired values.

## Verification

```text
lake build NBMellinTools.NB15OperatorAdaptation
Build completed successfully (8636 jobs).
```

The new module contains no `sorry` and introduces no project axiom. It remains
outside the public umbrella. No file was staged or committed.

