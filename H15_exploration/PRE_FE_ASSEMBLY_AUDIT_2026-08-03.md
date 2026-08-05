# Certified pre-functional-equation assembly audit

## Result

`NB15PreFEAssembly.lean` fixes the source side of the H15 comparison without
assuming that one local PostFE block is the global Nyman--Beurling energy.

The exact proved chain is

```text
NB8.logTaperL2Error n
  = NB10.vasyuninCoupledExpression (n + 2) (NB8.logTaperCoeffs n)
  = preFECorrection n
      + preFEConstant n
      + preFELogRatio n
      + preFEInteriorCotangent n
      + preFEEndpointCotangent n.
```

The first equality is the unconditional NB11 Vasyunin evaluation.  The
second is a finite partition of the two-orientation cotangent sum according
to whether the gcd-reduced denominator pair is in the primitive interior
`a,q >= 2` or in its endpoint complement.

## Exact normalization table

| Certified source datum | Active NB12 datum | Proved relation |
|---|---|---|
| cutoff `n + 2` | `logTaperLength n` | definitional |
| coefficient at denominator `k+1` | `h15NaturalLogTaperCoeff (n+2) (k+1)` | exact equality |
| primitive variables | `h15LaurentA`, `h15LaurentQ` | same `a,q >= 2` support condition |
| gcd slice | `h15LaurentG` | same positive natural coordinate |
| oriented row coefficient | `h15LaurentRowWeight` | exact `c(ga)c(gq) pi/(g a q)` equality on valid support |
| endpoint sector | absent from active Laurent rows | retained explicitly as `preFEEndpointCotangent` |

The factor `pi/(g a q)` in an oriented NB12 row is correct.  Two orientations
are required to reproduce the symmetric pair of Vasyunin sums.  The endpoint
sector is not represented by `h15LaurentRowValid`, which intentionally
requires both primitive variables to be at least two.

## What this rules out

A single tuple

```lean
NB15.PostFEParameters
```

cannot be asserted to represent the global NB8 energy merely from the local
NB12 PostFE normal form.  The certified source contains all gcd slices and an
explicit primitive endpoint sector, whereas one PostFE tuple is one local
frequency/block evaluation.

## Next exact target

The next bridge must prove a finite gcd reindexing of the complete Gram term:

```text
sum over h,k in [1,N]
  = sum over g and coprime a,q with ga,gq <= N.
```

After applying the NB11 Vasyunin formula and Gram homogeneity, this must be
split into:

1. the two oriented primitive interior rows (`a,q >= 2`);
2. the primitive endpoint rows (`a = 1` or `q = 1`);
3. the elementary constant and logarithmic pieces;
4. the original `bdCorrectionTerm`.

Only then should the primitive interior be identified with the analytic
special value of `bblsEstermannHurwitzContinuation` at zero.  The finite DFT
calculation in the archived Route C sources is useful, but the active project
still needs the analytic Hurwitz-at-zero endpoint theorem or an equivalent
Abel-boundary proof.  A merely formal function assigned the value
`1/4 - i V(a,q)/2` is not an analytic Estermann continuation.

## Verification

```bash
lake env lean proofs/NBMellinTools/NB15PreFEAssembly.lean
```

passes with no errors.  The module contains no `sorry`, `axiom`, or `opaque`
declaration and remains outside the public umbrella.
