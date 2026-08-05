# Report: bridging the PostFE energy route to the Nyman–Beurling `L²` integral

## What was asked

Prove `IsNymanBeurlingEnergySpecialization` (`NB15JointLedgerUnification.lean`, line 100),
i.e. exhibit a family of PostFE parameters whose NB12 *varying row energy*, summed over all
dyadic blocks, gcd strata and frequency shells, equals

`∫₀^∞ |χ_{(0,1]}(x) − ∑_{k<N} c_k(N) ρ_k(x)|² dx`

for the NB8 Möbius log-taper coefficients `c_k`.

## State of the delivered repository

The repository contains seven `.lean` files that are *fragments* of the larger `NBMellinTools`
package.  Every one of them imports modules that are **not** part of the repository:

| file | missing import |
| --- | --- |
| `BaezDuarteTail.lean` | `NBMellinTools.NB2Mellin` |
| `NB7ApproximationSequence.lean` | `NBMellinTools.NB6GlobalClosure` |
| `NB8LogTaperTarget.lean` | `NBMellinTools.NB7ApproximationSequence` (as a `NBMellinTools.*` module) |
| `NB15GramBlockDecomposition.lean` | `NBMellinTools.NB15NonresonantBlockHSBounds` |
| `NB15OperatorAdaptation.lean`, `NB15Phase4OperatorTraceDecay.lean` | `NBMellinTools.NB15Phase3Spectral` |
| `NB15JointLedgerUnification.lean` | `NBMellinTools.NB8LogTaperTarget`, `NBMellinTools.NB12BBLSH15PostFECompleteHarmonicNormalForm` |

Consequently none of these files elaborates here (`lake build` fails with
`unknown module prefix 'NBMellinTools'`), and in particular the definitions occurring in the
target predicate — `NB12.h15PostFEActualVaryingRowEnergy` and the four NB12 ledger components —
are unavailable.  Their statements cannot be inspected, so the literal predicate at
`NB15JointLedgerUnification.lean:100` cannot be discharged (nor even type-checked) in this
repository.  Inventing definitions under the NB12 names would make any resulting theorem a
statement about invented objects, so that route was deliberately avoided; the user's files were
left untouched apart from one explanatory comment.

## What was proved instead

A new, fully self-contained module `NB16DyadicGcdShellLedger.lean` (imports only `Mathlib`,
namespace `NBMellinTools.NB16`) proves, **without `sorry` and with only the standard axioms
`propext`, `Classical.choice`, `Quot.sound`**, the measure-theoretic half of the requested
bridge: the exact identification of the Nyman–Beurling `L²` integral with a sum of explicit
local energies over a complete partition into dyadic blocks, gcd strata and frequency shells.

The Báez–Duarte objects are repeated verbatim from the shipped files
(`chi01`, `rhoBD k x = {1/((k+1)x)}`, `bdApprox`, `BaezDuarteL2Error`, `logTaperLength`,
`logTaperCoeffs`, `logTaperL2Error`) so that the statements match the active package.

Main contents.

1. **Integrability.**  `integrableOn_Ioi_of_bdd_of_inv_sq`: a measurable function bounded on
   `(0,1]` and `O(x⁻²)` on `(1,∞)` is integrable on `(0,∞)`.  Applied to `χ²`, `χ·ρ_k` and
   `ρ_j·ρ_k` (`integrableOn_chi01_sq`, `integrableOn_chi01_mul_rhoBD`,
   `integrableOn_rhoBD_mul_rhoBD`), using that above `1` each generator is exactly `1/((k+1)x)`.
2. **Exact quadratic expansion** (`baezDuarteL2Error_eq_expansion`):
   `E(N,c) = 1 − 2∑_k c_k b_k + ∑_j∑_k c_j c_k G_{jk}`, with `b_k = ∫₀^∞ χ ρ_k`,
   `G_{jk} = ∫₀^∞ ρ_j ρ_k` and constant part `∫₀^∞ χ² = |(0,1]| = 1` (`integral_chi01_sq`).
3. **Local (varying row) energies** (`localEnergy`, `baezDuarteL2Error_eq_sum_localEnergy`):
   the Gram term is carried by the pair `(j,k)`, the `χ`-pairing is shared among the `N` pairs of
   a row and the constant mass among all `N²` pairs, so that
   `E(N,c) = ∑_{(j,k) ∈ Fin N × Fin N} localEnergy (j,k)` exactly.
4. **The ledger partition** (`ledgerTag`, `ledgerTags`, `ledgerTag_mem_ledgerTags`): each pair is
   tagged by its two dyadic scales `⌊log₂(j+1)⌋, ⌊log₂(k+1)⌋`, its gcd stratum
   `gcd(j+1,k+1)`, and its frequency shell `(gcd(j+1,N), gcd(k+1,N))` — a pair of divisors of the
   common cutoff `N`.  Refibring the sum along this tag gives the ledger identity
   `baezDuarteL2Error_eq_ledger_sum` and, written out as five explicit summations,
   `baezDuarteL2Error_eq_ledger_nested_sum`:

   `∫₀^∞ |χ − ∑ c_k ρ_k|² = ∑_{a} ∑_{b} ∑_{d} ∑_{u|N} ∑_{v|N} cellEnergy (a,b,d,u,v)`.
5. **Specialization** (`logTaperLedgerEnergy_eq_logTaperL2Error`,
   `isNymanBeurlingEnergySpecialization_ledger`): for the NB8 Möbius log-taper coefficients the
   ledger total is exactly `logTaperL2Error n` at every stage, which inhabits the (NB16 form of
   the) specialization predicate.
6. **Transport** (`nymanBeurlingCriterion_of_ledgerEnergy_tendsto_zero`): since the identity is an
   equality, decay of the ledger is decay of the certified `L²` error and yields the
   finite-approximation Nyman–Beurling criterion.  No unconditional analytic claim is made: decay
   remains the open input.

## What remains

Identifying the NB12 PostFE parameters `(frequencySupport, n, g, U, Q, t)` whose
`h15PostFEActualVaryingRowEnergy` equals the cell energies above.  This requires the NB12 modules,
which are not present here; once they are available, `NB16.baezDuarteL2Error_eq_ledger_sum`
supplies the analytic side of that identification.
