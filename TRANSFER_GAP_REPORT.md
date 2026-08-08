# TRANSFER GAP REPORT — H15 Pointwise Aggregate → NB8 Log-Taper Energy

**Task S deliverable (option B).**  All quotes below are verbatim from this
repository; every line number refers to the file as shipped in `proofs/`
(the copy in `riemann-github/proofs/` is byte-identical for all files quoted
here).  Nothing was reconstructed, and no proxy H15 object was introduced.

**Verdict.**  The transfer cannot be proved, and it cannot even be *stated*
using existing declarations: the named target `H15PointwiseAggregateToLogTaperTransfer`
does not exist in the repository, and neither does `H15CoupledVariationBoundaryDecay`
or `H15SmoothPointwiseAggregateDecay`.  Beyond nomenclature, there is a real
mathematical gap: **no theorem in this repository relates any object of the
NB12 H15 *progression* branch to `NB8.logTaperL2Error`**, and the two families
are not even indexed by the same data.  Section 5 names the missing theorem and
gives its exact Lean type; Section 6 classifies the gap.

---

## Phase 1 — Exact definitions (quoted)

### 1.1 `NBMellinTools.NB8.logTaperL2Error`

`proofs/NBMellinTools/NB8LogTaperTarget.lean`, lines 35–51:

```lean
/-- The total cutoff used at sequence index `n`; it starts at `2`, so the
normalizing logarithm is nonzero and positive. -/
def logTaperLength (n : ℕ) : ℕ := n + 2

/-- The explicit real Möbius log-taper coefficients, indexed by denominators
`k + 1` in the range `1, ..., n + 2`. -/
noncomputable def logTaperCoeffs
    (n : ℕ) (k : Fin (logTaperLength n)) : ℝ :=
  -((ArithmeticFunction.moebius (k.val + 1) : ℤ) : ℝ) *
    (Real.log
        (((logTaperLength n : ℕ) : ℝ) / ((k.val + 1 : ℕ) : ℝ)) /
      Real.log ((logTaperLength n : ℕ) : ℝ))

/-- The exact `L²(0,∞)` error of the explicit log-taper approximant. -/
noncomputable def logTaperL2Error (n : ℕ) : ℝ :=
  BaezDuarteL2Error (logTaperLength n) (logTaperCoeffs n)
```

with (`proofs/NBMellinTools/BaezDuarteTail.lean`, lines 29–31)

```lean
noncomputable def BaezDuarteL2Error
    (N : ℕ) (coeffs : Fin N → ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), (chi01 x - bdApprox N coeffs x) ^ 2
```

### 1.2 `NBMellinTools.NB8.LogTaperL2Decay`

`proofs/NBMellinTools/NB8LogTaperTarget.lean`, lines 52–54:

```lean
/-- The concrete open analytic target for this coefficient family. -/
def LogTaperL2Decay : Prop :=
  Tendsto logTaperL2Error atTop (nhds 0)
```

### 1.3 `h15NormalizedProgressionSmoothPointwiseAggregate`

This is the actual name (there is no `h15SmoothPointwiseAggregate`).
`proofs/NBMellinTools/NB12BBLSH15ActiveIncidence.lean`, lines 285–293:

```lean
/-- The pre-completion pointwise aggregate with the unfrozen smooth H15
weight and the full normalized dyadic support. -/
noncomputable def h15NormalizedProgressionSmoothPointwiseAggregate
    (N g r U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
      h15DyadicNormalizedProgressionWeightedCross r U
        (h15SquareDivisorProgressionModulus g d) q
        (h15NormalizedProgressionSmoothWeight N g d)
```

Unfolding its ingredients:

* `proofs/NBMellinTools/NB12BBLSH15NormalizedSuperperiod.lean:557`
  ```lean
  noncomputable def h15DyadicNormalizedProgressionWeightedCross
      (r U L q : ℕ) (weight : ℕ → ℝ) : ℝ :=
    ∑ u ∈ h15NormalizedProgressionDyadicSupport U L q,
      weight u * h15PairedDirectCrossMode r u q
  ```
* `proofs/NBMellinTools/NB12BBLSH15NormalizedSuperperiod.lean:597`
  ```lean
  noncomputable def h15NormalizedProgressionSmoothWeight
      (N g d u : ℕ) : ℝ :=
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      h15SupportedInverseSmoothEnvelope N g u
  ```
* `proofs/NBMellinTools/NB12BBLSH15RamanujanVariationAudit.lean:68`
  ```lean
  noncomputable def h15SupportedInverseSmoothEnvelope
      (N g u : ℕ) : ℝ :=
    if g * u ≤ N then
      (Real.log ((N : ℝ) / ((g * u : ℕ) : ℝ)) /
          Real.log (N : ℝ)) ^ 2 / (u : ℝ) ^ 2
    else 0
  ```
* `proofs/NBMellinTools/NB12BBLSH15RamanujanCompletionDefect.lean:75`
  ```lean
  noncomputable def h15PairedDirectCrossMode
      (r u q : ℕ) : ℝ :=
    ((h15DirectAdditiveReducedUnitPhase .positive r u q) ^ 2).im
  ```
* `proofs/NBMellinTools/NB12BBLSH15BettinChandeeLedger.lean:402`
  ```lean
  def h15BettinChandeeSupportedNatBlock (N g X : ℕ) : Finset ℕ :=
    (h15BettinChandeeNatBlock X).filter (fun x => g * x ≤ N)
  ```

So, in mathematical notation, with `L_d = d²/gcd(g,d²)` and `e(x) = e^{2πix}`,

```
A(N,g,r,U,Q) = Σ_{q∈[Q,2Q), gq≤N} Σ_{d active} μ(d) ·
                 Σ_{u∈[U,2U), (u,q)=1, L_d | u}
                    (log(N/(gu))/log N)² / u² · Im e(2ru/q).
```

It is a **real, finite, signed bilinear block sum** over two dyadic ranges,
attached to one gcd slice `g` and one additive frequency `r`.

### 1.4 `H15PointwiseAggregateToLogTaperTransfer`

**MISSING.**  There is no file `NB20H15RHBridge.lean` (or any variant) and no
declaration of that name:

```
$ rg -n "H15PointwiseAggregateToLogTaperTransfer" proofs riemann-github/proofs h15_exploration docs
(no matches)
```

The same search returns nothing for `H15CoupledVariationBoundaryDecay` and for
`H15SmoothPointwiseAggregateDecay`.  The nearest **existing** declarations are:

| Requested name | Nearest existing declaration | Location |
|---|---|---|
| `H15CoupledVariationBoundaryDecay` | `h15NormalizedProgressionCoupledVariationBoundaryAggregate` (an ℝ-valued aggregate, *not* a decay `Prop`) | `NB12BBLSH15ActiveIncidence.lean:163` |
| — | `H15CertifiedCoupledBoundaryDecay` (a decay `Prop`, but of the *contour* energy, not of the progression aggregate) | `NB15CoupledBoundaryDecay.lean:95` |
| `H15SmoothPointwiseAggregateDecay` | `h15NormalizedProgressionSmoothPointwiseAggregate` (aggregate only; no decay `Prop` anywhere) | `NB12BBLSH15ActiveIncidence.lean:287` |

Consequently the Phase-4 statement of Task S cannot be typed against this
repository as written.

---

## Phase 2 — Existing theorems in the two branches

**(a) Certified branch — reaches `NB8.logTaperL2Error` (all proved).**

| Theorem | Location | Claim |
|---|---|---|
| `h15CertifiedCoupledBoundaryEnergy_eq_logTaperL2Error` | `NB15CoupledBoundaryDecay.lean:82` | the certified contour energy **equals** `logTaperL2Error n`, pointwise in `n` |
| `h15CertifiedCoupledBoundaryDecay_iff_logTaperL2Decay` | `NB15CoupledBoundaryDecay.lean:98` | the two decay targets are equivalent |
| `riemannHypothesis_of_h15CertifiedCoupledBoundaryDecay` | `NB15CoupledBoundaryDecay.lean:116` | that decay implies `RiemannHypothesis` |
| `h15CertifiedCoupledBoundaryDecay_of_lowEndpoint_of_middle` | `NB15CoupledBoundaryDecay.lean:269` | low sector + Bettin–Chandee middle window ⟹ certified decay (ultra-high tail proved) |
| `riemannHypothesis_of_logTaperL2Decay` | `NB8LogTaperTarget.lean:74` | `LogTaperL2Decay` ⟹ `RiemannHypothesis` |
| `logTaperL2Error_eq_quadraticForm`, `logTaperL2Decay_iff_correction_add_gram_tendsto` | `NB9QuadraticExpansion.lean:311, 326` | Gram/correction expansion of the same energy |
| `h15BettinChandeeMiddleFrequencyIntegral_eq_dyadicBlocks` | `NB12BBLSH15FrequencyTailRate.lean:515` | the middle window is the sum of the five-coordinate Bettin–Chandee dyadic blocks |
| `H15BettinChandeeMiddleWindowDecay` | `NB12BBLSH15FrequencyTailRate.lean:698` | the remaining middle-window analytic gate |

**(b) Progression branch — the H15 aggregates (all proved, all internal).**

| Theorem | Location | Claim |
|---|---|---|
| `h15RamanujanSignedSquareDivisorAggregate_eq_normalizedProgression` | `NB12BBLSH15SquarefreeGCDStratification.lean:396` | square-divisor expansion = normalized progression aggregate |
| `h15NormalizedProgressionAggregate_eq_coupledVariationBoundary` |  `NB12BBLSH15ActiveIncidence.lean:179` | row aggregate = coupled variation + boundary |
| `h15NormalizedProgressionAggregate_eq_frozenPointwise` | `NB12BBLSH15ActiveIncidence.lean:273` | row aggregate = frozen pointwise aggregate |
| `h15NormalizedProgressionSmoothPointwiseAggregate_eq_coupled` | `NB12BBLSH15ActiveIncidence.lean:318` | smooth pointwise aggregate = pointwise coupled aggregate |
| `h15CoupledVariationBoundary_add_rowToPointwiseResidual` | `NB12BBLSH15ActiveIncidence.lean:347` | row-coupled + residual = pointwise-coupled (**Task Q terminus**) |
| `h15NormalizedProgressionRowToPointwiseResidual_eq_unfreezing_add_incomplete` | `NB12BBLSH15ActiveIncidence.lean:653` | exact split of that residual |
| `h15CoupledVariationBoundary_add_abelInterior_add_boundary` | `NB12BBLSH15CorrectionCoupledAbel.lean:211` | Abel form of the same identity |
| `h15PairedDirectWeightedMass_eq_baseline_add_cross` | `NB12BBLSH15PairedDirectKernel.lean:274` | `‖paired kernel‖²`-mass = baseline mass + `2 sinh(πt)` × cross correlation |
| `h15PairedDirectCrossCorrelation_supported_eq_completionDefects` | `NB12BBLSH15RamanujanCompletionDefect.lean:487` | the cross correlation with the genuine H15 coefficient = variation + boundary defects |

**(c) Transfer theorems between (a) and (b): none.**

A repository-wide search finds **no file** that mentions both a progression-branch
object and the NB8 energy:

```
$ for f in $(rg -l "h15Normalized" proofs); do rg -q "logTaperL2Error|h15Certified|LogTaperL2Decay" $f && echo $f; done
proofs/NBMellinTools/NB15CorrectionPreservingRectangle.lean
proofs/NBMellinTools/NB15EndpointBoundaryExtraction.lean
proofs/NBMellinTools/NB15CoupledBoundaryDecay.lean
```

and in those three files the only `h15Normalized…` names occurring are the
*contour* objects `h15NormalizedClosedRectangleValue`,
`h15NormalizedPoleSubtractedBoundary`, `h15NormalizedCompleteContourBoundary` —
none of them is a progression aggregate.  Likewise

```
$ rg -l "PairedDirect" proofs/NBMellinTools/*.lean | xargs rg -l "logTaperL2Error|h15Certified|BaezDuarte"
(no matches)
```

No Mellin or Fourier transfer identity between the two branches exists.

---

## Phase 3 — Relationship between the two quantities

Answer: **(E) — unrelated without an additional identity.**  Not merely
"unproved in the library": as they stand the two objects are not comparable,
for four independent reasons.

1. **Different index data.**  `logTaperL2Error : ℕ → ℝ` is a function of the
   single stage index `n` (cutoff `N = n+2`).  The aggregate
   `h15NormalizedProgressionSmoothPointwiseAggregate : ℕ → ℕ → ℕ → ℕ → ℕ → ℝ`
   depends on `(N, g, r, U, Q)`.  No canonical schedule
   `n ↦ (g n, r n, U n, Q n)` is fixed anywhere in the repository.  Any transfer
   statement must first choose one, and that choice is part of the missing
   theorem, not a normalization constant.

2. **The aggregate is one *block* of one *piece*.**  On the certified side, the
   only place where Bettin–Chandee dyadic data occurs is the middle window,
   `h15BettinChandeeIntegratedDyadicBlock n K J T key`
   (`NB12BBLSH15BettinChandeeLedger.lean:259`) summed over the five-coordinate
   keys `H15BettinChandeeDyadicKey` = (gcd slice, inverse scale, modulus scale,
   frequency scale, orientation) (`ibid.:132`, `:140`).  A single value of
   `(g, r, U, Q)` corresponds to *one* such key (with `U`, `Q` the dyadic scales
   and `r` one frequency).  Reaching `logTaperL2Error n` therefore requires
   summing the transferred bound over all keys of
   `h15BettinChandeeDyadicKeys (logTaperLength n) K J`, over the frequency range
   `r ∈ Ico (K+1) (K+1+J)`, **and** adding the low sector and the endpoint
   ledger.  None of these summations is available for the progression aggregate.

3. **Different analytic type: pointwise cross term vs. vertical integral.**
   The certified block is a *contour integral*,
   ```lean
   noncomputable def h15BettinChandeeIntegratedSummand
       (n : ℕ) (T : ℝ) (ir : H15LaurentRowIndex (logTaperLength n) × ℕ) : ℂ :=
     h15LaurentRowWeight ir.1 *
       ∫ t : ℝ in -T..T,
         bblsActiveThreeHalfFrequencyTerm (h15ContourDamping n) …
   ```
   (`NB12BBLSH15BettinChandeeLedger.lean:249`), a complex quantity whose
   imaginary part enters the energy.  The progression aggregate is
   `t`-independent: by `h15PairedDirectWeightedMass_eq_baseline_add_cross`
   (`NB12BBLSH15PairedDirectKernel.lean:274`) it is exactly the arithmetic
   factor of the **cross term** of `‖paired kernel‖²`, whose `t`-dependence has
   been factored out into `2·sinh(πt)`.  Passing from control of that cross term
   to control of the signed vertical integral needs (i) a Cauchy–Schwarz /
   large-sieve step from the squared mass to the linear signed sum, and
   (ii) integration in `t` against `sinh(πt)`, which **grows** on the height
   schedule `T n → ∞` used by
   `h15CertifiedCoupledBoundaryDecay_of_lowEndpoint_of_middle`
   (`NB15CoupledBoundaryDecay.lean:269`).  This is where the real analytic cost
   sits.

4. **Different coefficient weights.**  The progression aggregate carries the
   *squared* envelope `(log(N/(gu))/log N)²/u²`
   (`h15SupportedInverseSquareWeight`, `NB12BBLSH15RamanujanCompletionDefect.lean:428`),
   while the certified row weight is the *product* of two different coefficients,
   `(π/g) · α_inv(N,g,·) · α_mod(N,g,·)`
   (`NB12BBLSH15BettinChandeeLedger.lean:96–105`).  These agree only on the
   diagonal of the paired-kernel expansion; off it, an extra identity is needed.

Answers to the specific questions:

* **A. Same object up to normalization?** No (points 1–4).
* **B/C. One an upper/lower bound on the other?** No such inequality exists in
  the repository, and none can hold unconditionally: for `N < g·Q` the supported
  block is empty and the aggregate is identically `0`, while `logTaperL2Error n`
  is unchanged.  This is now *proved*:
  `NBMellinTools.NB20.h15NormalizedProgressionSmoothPointwiseAggregate_eq_zero_of_cutoff_lt`
  (`proofs/NBMellinTools/NB20H15PointwiseAggregateTransferAudit.lean`).
* **D. Asymptotically equivalent?** Not meaningful before a schedule is fixed;
  and for the degenerate schedules of point B the aggregate tends to `0` with no
  information about the energy (`…_of_cutoff_lt_schedule`, same file).
* **E. Unrelated without an additional identity?** **Yes** — this is the correct
  answer.

### A proved consequence (Task S by-product)

The audit file `proofs/NBMellinTools/NB20H15PointwiseAggregateTransferAudit.lean`
records the sharp form of point B.  With

```lean
def H15UnrestrictedPointwiseAggregateTransfer : Prop :=
  ∀ g r U Q : ℕ → ℕ,
    Tendsto (fun n : ℕ =>
        h15NormalizedProgressionSmoothPointwiseAggregate
          (logTaperLength n) (g n) (r n) (U n) (Q n))
      atTop (nhds 0) →
    LogTaperL2Decay
```

it is proved (no `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound`)
that

```lean
theorem h15UnrestrictedPointwiseAggregateTransfer_iff_logTaperL2Decay :
    H15UnrestrictedPointwiseAggregateTransfer ↔ LogTaperL2Decay
```

i.e. the schedule-free reading of the requested transfer is **equivalent to the
open NB8 target itself** — it carries no arithmetic content, because the
schedule `g = 1`, `Q n = n + 3` satisfies its hypothesis vacuously.  Any useful
transfer theorem must therefore carry an admissibility constraint on the
schedule (at minimum `g n * Q n ≤ logTaperLength n`) together with a genuine
identity; the constraint alone is not enough.

---

## Phase 4 — Proof attempt

Not possible, and not attempted as stated: the goal
`H15PointwiseAggregateToLogTaperTransfer g r U Q` does not exist (Phase 1.4),
and the hypothesis `H15CoupledVariationBoundaryDecay g r U Q` does not exist
either.  Writing either of them would mean inventing the objects that this task
explicitly forbids inventing.

What *was* proved instead is the honest audit above, plus the two degeneracy
lemmas it rests on.  These are the only new mathematical statements added by
this task; they are in `proofs/NBMellinTools/NB20H15PointwiseAggregateTransferAudit.lean`
and use only declarations already present in `NB8LogTaperTarget.lean` and
`NB12BBLSH15ActiveIncidence.lean`.

---

## Phase 5 — The missing theorem

### 5.1 Name

`h15BettinChandeeDyadicBlock_eq_pointwiseProgressionAggregate`
(the *identity* step), followed by
`h15MiddleWindow_of_pointwiseProgressionAggregate` (the *assembly* step).
Only the pair of them yields a statable
`H15PointwiseAggregateToLogTaperTransfer`.

### 5.2 What the identity must claim

In mathematical notation: for the canonical middle window at stage `n`, with
cutoff `N = n+2`, damping `h15ContourDamping n`, height `T`, and for each
Bettin–Chandee key `key = (g, log₂U, log₂Q, log₂r, ε)`,

```
Im ( h15BettinChandeeIntegratedDyadicBlock n K J T key )
   =  ∫_{-T}^{T}  c(n,t) ·  A(N, g, r, U, Q)  dt   +  (diagonal/baseline term)
```

where `c(n,t)` is the explicit archimedean factor already isolated by
`h15PairedDirectWeightedMass_eq_baseline_add_cross` (it contains
`sinh(π t)`), and `A` is `h15NormalizedProgressionSmoothPointwiseAggregate`.
Equivalently: *the arithmetic content of one damped vertical Bettin–Chandee
block is the H15 progression aggregate of that block, integrated against the
explicit three-halves-line kernel.*

### 5.3 Lean type of the missing identity

```lean
theorem h15BettinChandeeDyadicBlock_eq_pointwiseProgressionAggregate
    (n K J : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (key : NBMellinTools.NB12.H15BettinChandeeDyadicKey) :
    (NBMellinTools.NB12.h15BettinChandeeIntegratedDyadicBlock n K J T key).im =
      (∫ t : ℝ in -T..T,
          NBMellinTools.NB12.h15PairedHyperbolicCoefficient t *
            NBMellinTools.NB12.h15NormalizedProgressionSmoothPointwiseAggregate
              (NBMellinTools.NB8.logTaperLength n)
              key.gcdSlice (2 ^ key.frequencyScale)
              (2 ^ key.inverseScale) (2 ^ key.modulusScale)) +
        h15BettinChandeeDyadicBlockDiagonal n K J T key
```

(the last summand being the baseline/diagonal part of
`h15PairedDirectWeightedMass_eq_baseline_add_cross`, which also does not yet
exist as a declaration).

### 5.4 Lean type of the resulting transfer

Once 5.3 and the key/frequency summation are available, the transfer becomes
statable in the shape Task S asked for — but with an **admissible schedule**,
which the audit theorem of Phase 3 shows to be indispensable:

```lean
def H15AdmissibleSchedule (g r U Q : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, 0 < g n ∧ 0 < U n ∧ 0 < Q n ∧
    g n * Q n ≤ NBMellinTools.NB8.logTaperLength n

def H15PointwiseAggregateToLogTaperTransfer (g r U Q : ℕ → ℕ) : Prop :=
  H15AdmissibleSchedule g r U Q →
  Tendsto (fun n : ℕ =>
      NBMellinTools.NB12.h15NormalizedProgressionSmoothPointwiseAggregate
        (NBMellinTools.NB8.logTaperLength n) (g n) (r n) (U n) (Q n))
    atTop (nhds 0) →
  NBMellinTools.NB8.LogTaperL2Decay
```

Even this is **not** the right target on its own: a qualitative
`Tendsto … 0` for one block cannot be summed over the `≍ (log N)⁴`-many keys
and the `J`-many frequencies.  The honest target is quantitative, e.g. a
power-saving bound

```lean
∀ ε > 0, ∃ C, ∀ N g r U Q, admissible … →
  |h15NormalizedProgressionSmoothPointwiseAggregate N g r U Q| ≤
    C * (Q : ℝ) * (U : ℝ) ^ (-(1/2 : ℝ) + ε) * …
```

uniform in `(g, r, U, Q)`, which is exactly the Bettin–Chandee-type input the
repository's own audits (`NB12BBLSH15BettinChandeeAudit.lean`,
`NB12BBLSH15PostFEBilinearExponentAudit.lean`) record as unavailable from the
published estimate over the whole tail.

### 5.5 Gap classification

| Candidate | Verdict |
|---|---|
| Normalization constant adjustment | **No.**  The two objects have different index sets, different weights and different analytic type. |
| Asymptotic equivalence proof | **No.**  They are not asymptotically comparable before a schedule is fixed, and for degenerate schedules the aggregate vanishes identically (proved). |
| Mellin/Fourier inversion identity | **Partly — this is the first missing piece.**  What is missing is the vertical (Mellin-line) evaluation identifying the damped Bettin–Chandee block integral with the `t`-integral of the arithmetic cross term (§5.3).  All the algebra of the cross term exists (`NB12BBLSH15PairedDirectKernel.lean`); the *contour-to-arithmetic* identification does not. |
| Missing analytic continuation | **No.**  The continuation/rectangle work is already done in `NB12BBLSH15Rectangle.lean`, `NB15CorrectionPreservingRectangle.lean`, `NB15EndpointBoundaryExtraction.lean`. |
| **Something else (dominant obstruction)** | **Yes:** a *uniform quantitative* bilinear estimate for the H15 progression aggregate, plus the summation of that estimate over the five-coordinate dyadic keys, the frequency range and the `sinh(π t)`-weighted height integral.  In short: a large-sieve/Cauchy–Schwarz step from the squared paired-kernel mass to the signed vertical integral, uniform in `(g, r, U, Q)` — new analytic machinery, not a bookkeeping identity. |

---

## Appendix — reproducibility notes (environment)

The repository as shipped does not compile against the Mathlib pinned in this
environment; the following **pre-existing** obstacles were found and repaired so
that the NB8/NB12 chain could actually be built and the results above checked.
All repairs are mechanical compatibility fixes; no mathematical statement was
weakened.

1. Mathlib renames (`camelCase` → `snake_case` in this Mathlib version):
   `integral_finsetSum`, `integrable_finsetSum`, `tendsto_finsetSum`,
   `continuous_finsetSum` — updated in
   `NB4ZeroDetection.lean`, `NB9QuadraticExpansion.lean`,
   `route-c/modules/BBLSPhiOne.lean` and others.
2. `Measurable.tsum` / `AEMeasurable.tsum` do not exist in this Mathlib.  Two
   proofs were rewritten to obtain measurability of a `tsum` as a pointwise
   limit of its measurable partial sums
   (`route-c/modules/VasyuninCotangentRecognition.lean`, new lemma
   `measurable_realTrigammaSeriesNat`; `NB12BBLSH15FrequencyIntegral.lean`).
3. `Finset.card_le_card_of_injOn` now takes membership in the coerced set;
   `NB12BBLSH15BoundaryDensity.lean` adjusted.
4. The module `RiemannHypothesis.Basic.CriticalStrip`, imported by
   `proofs/route-c/modules/BaezDuarte.lean`, is **absent from this snapshot**,
   and the `route-c` modules are not stored under the directory matching their
   module names, so `lake` cannot build them.  For verification only, the single
   name used (`RH.Basic.RiemannHypothesis`) was supplied out-of-tree as Mathlib's
   `RiemannHypothesis`; nothing in the NB8/NB12/NB20 chain depends on it (the
   axiom check below is clean).
5. The root `lakefile.toml` of this snapshot contains Lean-DSL text rather than
   TOML, so `lake` cannot configure the workspace.  Per the task's constraints it
   was left untouched; the chain was built by invoking `lean` directly in
   dependency order.
6. One pre-existing `sorry` remains in the closure, in
   `proofs/route-c/modules/VasyuninPeriodReduction.lean:131` (documented there by
   the authors).  The theorems added by this task do not depend on it.

Axiom check for everything added by this task:

```
'NBMellinTools.NB20.h15BettinChandeeSupportedNatBlock_eq_empty_of_cutoff_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'NBMellinTools.NB20.h15NormalizedProgressionSmoothPointwiseAggregate_eq_zero_of_cutoff_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'NBMellinTools.NB20.h15NormalizedProgressionFrozenPointwiseAggregate_eq_zero_of_cutoff_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'NBMellinTools.NB20.tendsto_h15SmoothPointwiseAggregate_of_cutoff_lt_schedule' depends on axioms: [propext, Classical.choice, Quot.sound]
'NBMellinTools.NB20.h15UnrestrictedPointwiseAggregateTransfer_iff_logTaperL2Decay' depends on axioms: [propext, Classical.choice, Quot.sound]
'NBMellinTools.NB20.riemannHypothesis_of_h15UnrestrictedPointwiseAggregateTransfer' depends on axioms: [propext, Classical.choice, Quot.sound]
```
