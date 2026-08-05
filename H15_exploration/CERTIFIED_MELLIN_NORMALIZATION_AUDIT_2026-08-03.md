# Certified Mellin normalization audit

## Result

The active exploration module
`proofs/NBMellinTools/NB15CertifiedMellinNormalization.lean` fixes the exact
cutoff, coefficient sign, and physical residual used by NB8.

For `N = n + 2` and denominator `m = k + 1`, it proves

```text
NB8.logTaperCoeffs n k
  = -mu(m) * (1 - log(m) / log(N)).
```

Thus its negation is exactly the positive Möbius coefficient in the standard
BCF Dirichlet polynomial.  It also proves

```text
NB8.logTaperL2Error n
  = integral_(0,infinity) norm(certifiedResidual n x)^2 dx.
```

The real-to-complex coercion introduces no scale factor.

## Restored generic theorem

`proofs/NBMellinTools/FourierCompatibility.lean` has been restored from the
previous verified worktree into the active source layout.  It proves:

1. almost-everywhere compatibility of Mathlib's pointwise Fourier integral
   and its `Lp` Fourier transform on `L1 ∩ L2`;
2. exact Fourier Plancherel for such representatives;
3. the exact `2*pi` Jacobian for the critical-line frequency coordinate.

## Necessary distinction

The certified critical-line numerator is

```text
(1 - zeta(s) * certifiedDirichletPolynomial n s) / s,
  s = 1/2 + i*t.
```

This is the Mellin transform of the physical NB8 residual.  The existing
`h15ThreeHalfLowFrequencyAggregate` is instead a functional-equation-
transformed Estermann object on `Re s = 3/2`.  They are not definitionally or
pointwise identical.  No theorem in the active project currently equates
them, and this audit does not claim such an equality.

## Pointwise Mellin theorem

`proofs/NBMellinTools/NB15CertifiedMellinTransform.lean` now assembles the
public NB2 identities `mellin_chi01` and `mellin_rhoBD` through the finite NB8
approximant and proves

```text
mellin certifiedResidual (1/2 + i*t)
  = certifiedCriticalLineNumerator n t.
```

The integrability needed for the finite sum--integral exchange is proved in
the same file; it is not assumed.

## Global Mellin--Plancherel theorem

`proofs/NBMellinTools/MellinPlancherelPositiveHalfLine.lean` proves a reusable
half-line theorem.  For a measurable `f : ℝ → ℂ` in `L²(0,∞)` whose
logarithmic pullback is integrable, it proves

```text
integral_(0,infinity) norm(f x)^2 dx
  = (1/(2*pi)) * integral_R
      norm(Mellin(f)(1/2+i*t))^2 dt.
```

The logarithmic change of variables, the `L²` transport, the pointwise
Mellin/Fourier identity, and the `2*pi` frequency normalization are all
proved in that module.

`proofs/NBMellinTools/NB15CertifiedMellinPlancherel.lean` discharges the
hypotheses for the literal finite NB8 residual.  In particular, it proves
measurability and `L²(0,∞)` membership, and proves `L¹(ℝ)` integrability of
the logarithmic pullback by separating the exact reciprocal tail from the
bounded compact-side contribution.  The resulting theorem is

```text
NB8.logTaperL2Error n
  = (1/(2*pi)) * integral_R
      norm(certifiedCriticalLineNumerator n t)^2 dt.
```

This is an exact unconditional equality for every finite `n`.  The subsequent
contour theorem must still connect this physical critical-line object to the
complete Estermann right-line object while conserving all residues and
endpoints.

## Logical status

- coefficient normalization: proved;
- physical residual norm identity: proved;
- generic Fourier compatibility: proved;
- pointwise Mellin residual identity in the active module: proved;
- reusable positive-half-line Mellin--Plancherel theorem: proved;
- global Mellin--Plancherel energy identity for the certified residual: proved;
- equality with the Estermann `3/2`-line aggregate: open;
- signed asymptotic decay: open;
- Riemann hypothesis: not proved.

## Verification

- `lake build NBMellinTools.FourierCompatibility`: successful;
- `lake build NBMellinTools.NB15CertifiedMellinNormalization`: successful;
- `lake build NBMellinTools.NB15CertifiedMellinTransform`: successful;
- `lake build NBMellinTools.MellinPlancherelPositiveHalfLine`: successful;
- `lake build NBMellinTools.NB15CertifiedMellinPlancherel`: successful;
- full `lake build`: successful after restoring Fourier compatibility;
- no `sorry` or project axiom occurs in these five modules;
- audited theorem dependencies are only `propext`, `Classical.choice`, and
  `Quot.sound`.
