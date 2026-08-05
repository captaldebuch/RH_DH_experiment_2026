# H15 vertical frequency-pairing audit

## Result

The exploration module
`proofs/NBMellinTools/NB15VerticalFrequencyPairing.lean` proves the exact
finite-height quadratic expansion of the globally assembled NB12
low-frequency Estermann object.

For the finite support

```text
P(n,K) = range (K+1) × h15GlobalPostFEBlockSupport(logTaperLength n),
```

write `F_p(t)` for the literal localized PostFE frequency term.  The module
proves

```text
h15ThreeHalfLowFrequencyAggregate n K t = ∑ p in P(n,K), F_p(t)
```

and hence the complete pointwise pairing identity

```text
normSq(h15ThreeHalfLowFrequencyAggregate n K t)
  = ∑ p in P(n,K), ∑ q in P(n,K), Re(conj(F_p(t)) * F_q(t)).
```

Every `F_p` and every pair kernel is continuous.  Finite-interval integration
therefore gives the exact theorem

```text
h15TruncatedLowFrequencyVerticalEnergy n K T
  = h15TruncatedGlobalPostFEFrequencyPairing n K T.
```

No triangle inequality, diagonal truncation, or absolute majorant is used.

## What the identity preserves

The right side includes all four interaction classes:

1. same frequency, same block;
2. same frequency, different blocks;
3. different frequencies, same block;
4. different frequencies, different blocks.

This matters because the previously proved local PostFE quadratic objects do
not by themselves include the full signed global interaction matrix.

## What remains open

The project already contains an unconditional Mellin--Plancherel theorem for
the physical BCF residual.  The new identity concerns a different function:
the functional-equation-transformed Estermann aggregate on the
three-halves line.  No proved theorem currently identifies these two
functions, their measures, or all Archimedean normalization factors.

The next target is therefore an exact kernel-normalization/contour theorem:

```text
Mellin transform of certified residual
  = normalized complete Estermann right-line object
      + explicitly conserved residue/endpoint modes.
```

Only after that identity is proved can the new pairing matrix be inserted
into the certified Nyman--Beurling energy.  The high-frequency tail and the
residue/endpoint ledger must remain attached during the passage to the full
line.

## Logical status

- finite pairing identity: proved;
- compact-interval integrability: proved;
- equality with certified NB8 energy: not proved;
- signed asymptotic decay: not proved;
- Riemann hypothesis: not obtained from this module.
