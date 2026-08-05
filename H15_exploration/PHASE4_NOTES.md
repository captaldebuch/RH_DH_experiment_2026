# Phase 4 — status notes

## What was found

The repository contained only two Lean sources, `NB15Phase3Spectral.lean` and
`NB15Phase4OperatorTraceDecay.lean`.  All modules they depend on
(`NB15OperatorAdaptation`, `NB15GramBlockDecomposition`,
`NB15NonresonantBlockHSBounds`, …) were absent, so nothing compiled: Phase 3's
`import NBMellinTools.NB15GramBlockDecomposition` could not be resolved, and the
library glob in `lakefile.toml` did not cover the `NBMellinTools.*` modules.

## What was done

* `lakefile.toml`: the `proofs` library now has `srcDir = "proofs"` and
  `globs = ["NBMellinTools.+"]`, so `lake build NBMellinTools.NB15Phase4OperatorTraceDecay`
  resolves.
* The missing infrastructure was reconstructed explicitly, in three new modules.
  Everything in them is proved, with no `sorry` and no new axioms:
  * `NB15OperatorAdaptation.lean` — the additive character `e(x) = exp(2πix)`,
    the index type `H15ResonantOperatorIndex n K J = Fin n × Fin K × Fin J`
    (modulus index `q`, divisor-hyperbola pair `(k, j)`, frequency
    `r = (k+1)(j+1)`), the ledger-normalised weight
    `w(ik) = ((N+1)(q+1)(k+1)(j+1))⁻¹`, the amplitude
    `a(ik) = w(ik)·e(-t log r)`, and the energy bound `∑ w(ik)² ≤ 8/(N+1)²`.
  * `NB15NonresonantBlockHSBounds.lean` — the oscillatory cancellation input:
    periodicity of `e(mb/q)` in `b`, exact vanishing of a complete period when
    `q ∤ m`, reduction of `S(m,q,B)` to `S(m,q,B mod q)`, the incomplete-period
    bound `‖S(m,q,B)‖ ≤ q`, and the averaged form `‖S(m,q,B)/B‖ ≤ q/B`.
  * `NB15GramBlockDecomposition.lean` — the three blocks (resonant `q ∣ r-r'`,
    nonresonant with the normalised oscillatory average, traceless correction),
    the Gram kernel as their sum, the trace decomposition, the resonant trace
    identity `Tr(Gram_res) = ∑ w(ik)²` with the bound `8/(N+1)²`, and the
    Hilbert–Schmidt bound for the nonresonant block, `≤ 64/(N+1)⁴` for the
    Phase 4 truncation `K = 2n`, `J = n`.
* `NB15Phase3Spectral.lean`: its three `sorry`s (finite rank, HS bound, trace
  decomposition) are now proved.  The pre-existing `axiom
  h15CorrectionTraceDecaysToZero` was left untouched; note that its statement is
  `∀ n K J t, True`, so it carries no information.  No Phase 4 theorem depends
  on it.
* `NB15Phase4OperatorTraceDecay.lean`: Tasks 1–4 are proved as stated.

## Task 5

Task 5 asked for `RiemannHypothesis` outright.  That is not provable from the
material in this development: what Phases 1–4 establish is decay of the trace of
a concrete finite Gram model, and the bridge "trace decay ⇒ RH" is the
Nyman–Beurling criterion, which is formalised neither in Mathlib nor here.  The
original statement is therefore kept verbatim in a comment, with an explanation,
and the theorem `h15RiemannHypothesisViaOperatorTrace_phase4` now takes the
criterion as an explicit hypothesis `hNB` and applies it to the unconditionally
proved decay `h15GramTraceDecays_unconditional`.

## Verification

`lake build` completes successfully (8031 jobs).  No `sorry` occurs in any
proof, and `#print axioms` for every Phase 4 theorem reports only
`propext`, `Classical.choice`, `Quot.sound`.
