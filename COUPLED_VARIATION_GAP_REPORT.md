# COUPLED_VARIATION_GAP_REPORT

**Task R — Coupled Variation / Boundary Decay of the H15 branch**

All Lean statements referenced here are in the repository and compile in this
snapshot (Lean 4.28.0 + Mathlib, kernel-checked, no `sorry`, axioms
`propext / Classical.choice / Quot.sound` only). New material is in

* `proofs/NBMellinTools/NB12BBLSH15CoupledVariationBoundaryDecay.lean`.

---

## Phase 0 — Result in one paragraph

`H15CoupledVariationBoundaryDecay` is **not** an auxiliary sub-estimate that
Green–Tao-type input could discharge. The repository's own exact identities
show that the coupled variation/boundary aggregate *equals* the full signed
square-divisor aggregate of the H15 branch. So its decay is **logically
equivalent** to the open H15 signed estimate itself
(`H15SignedSquareDivisorPowerSaving`), and cannot be strictly easier. This
equivalence is now proved formally. What the existing machinery does supply
unconditionally is the absolute divisor budget `Q/U` (balanced value `1`,
exponent `0`), i.e. no decay at all.

---

## Phase 1 — Exact definitions

### 1a. `H15CoupledVariationBoundaryDecay`

**There is no declaration of this name anywhere in the repository, and there
is no file `NB20H15RHBridge.lean`.** Verified by exhaustive search over all
813 `.lean` files (`rg -n "CoupledVariation" -g '*.lean'`,
`find . -name "NB20*"`). The identifier occurs only in prose:

* `README.md:31` — `+ H15CoupledVariationBoundaryDecay (UNPROVEN — Task R)`
* `README.md:40` — `❌ H15CoupledVariationBoundaryDecay (the first missing bridge)`

The formal object that the name refers to is the *aggregate* below. To make
the proposition statable, this task adds the predicate (it is a definition of
a decay statement about the pre-existing aggregate, not a reconstruction of
any H15 object):

`proofs/NBMellinTools/NB12BBLSH15CoupledVariationBoundaryDecay.lean:173`
```lean
def H15SubexponentialDecay (F : ℕ → ℝ) : Prop :=
  ∃ C > 0, ∃ c > 0, ∀ N : ℕ, 2 ≤ N →
    |F N| ≤ C * Real.exp (-c * Real.sqrt (Real.log (N : ℝ)))
```
`... .lean:235`
```lean
def H15CoupledVariationBoundaryDecay (g r U Q : ℕ → ℕ) : Prop :=
  H15SubexponentialDecay fun N =>
    h15NormalizedProgressionCoupledVariationBoundaryAggregate
      N (g N) (r N) (U N) (Q N)
```

### 1b. `h15NormalizedProgressionCoupledVariationBoundaryAggregate`

**File:** `proofs/NBMellinTools/NB12BBLSH15ActiveIncidence.lean`, **lines
156–172** (identical copy at
`riemann-github/proofs/NBMellinTools/NB12BBLSH15ActiveIncidence.lean:163`):

```lean
/-- The exact signed output of normalized superperiod completion after the
active-incidence transpose.  Variation and endpoint boundary remain inside
the same `q,d` summand; this definition intentionally performs no triangle
inequality and no separate absolute majorization.

The reference value is the smooth envelope sampled at the left endpoint
`j*(L*q)` of the normalized superperiod. -/
noncomputable def h15NormalizedProgressionCoupledVariationBoundaryAggregate
    (N g r U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
      (h15NormalizedRowSuperperiodVariationDefect g r U q d
          (fun k => h15SupportedInverseSmoothEnvelope N g (k * q))
          (fun j => h15SupportedInverseSmoothEnvelope N g
            (j * (h15SquareDivisorProgressionModulus g d * q))) +
        h15NormalizedRowSuperperiodBoundaryDefect g r U q d
          (fun k => h15SupportedInverseSmoothEnvelope N g (k * q)))
```

Its two constituents (`proofs/NBMellinTools/NB12BBLSH15NormalizedSuperperiod.lean:322`
and `:330`):

```lean
noncomputable def h15NormalizedRowSuperperiodVariationDefect
    (g r U q d : ℕ) (weight reference : ℕ → ℝ) : ℝ :=
  let L := h15SquareDivisorProgressionModulus g d
  ∑ j ∈ h15CompleteNormalizedSuperperiodIndices U L q,
    ∑ k ∈ Finset.Ico (j * L) ((j + 1) * L),
      (weight k - reference j) *
        h15PeriodNormalizedProgressionRow g r k q d

noncomputable def h15NormalizedRowSuperperiodBoundaryDefect
    (g r U q d : ℕ) (weight : ℕ → ℝ) : ℝ :=
  let L := h15SquareDivisorProgressionModulus g d
  ∑ k ∈ h15NormalizedRowSuperperiodBoundary U L q,
    weight k * h15PeriodNormalizedProgressionRow g r k q d
```

---

## Phase 2 — Related theorems already in the repository

| Theorem / structure | Location | What it does |
|---|---|---|
| `h15NormalizedProgressionAggregate_eq_coupledVariationBoundary` | `proofs/NBMellinTools/NB12BBLSH15ActiveIncidence.lean:179` | **Exact identity:** full normalized progression aggregate `=` coupled variation + boundary aggregate (for `0<g, 0<U, 0<Q`). |
| `h15RamanujanSignedSquareDivisorAggregate_eq_normalizedProgression` | `proofs/NBMellinTools/NB12BBLSH15SquarefreeGCDStratification.lean:396` | Exact identity: signed square-divisor aggregate `=` normalized progression aggregate. |
| `abs_h15RamanujanSignedSquareDivisorAggregate_le_budget` | `proofs/NBMellinTools/NB12BBLSH15SquarefreeDivisorExpansion.lean:506` | Triangle inequality to the absolute divisor budget. |
| `h15RamanujanSquareDivisorAbsoluteBudget_le` | `…SquarefreeDivisorExpansion.lean:516` | Budget `≤ Q/U` (this is the repository's "divisor growth budget"). |
| `h15RamanujanSquareDivisorAbsoluteBudget_balanced_le` | `…SquarefreeDivisorExpansion.lean:542` | Balanced value `≤ 1`. |
| `h15RamanujanSquareDivisorAbsoluteBalancedExponent_not_neg` | `…SquarefreeDivisorExpansion.lean:554` | Records that the absolute route yields exponent `0`, never negative. |
| `H15SignedSquareDivisorPowerSaving` | `…SquarefreeDivisorExpansion.lean:560` | The **open** lower-middle gate: `|signed aggregate| ≤ C/U^η`, `η>0`. |
| `H15GCDStratifiedProgressionPowerSaving` (+ `.toSquareDivisor`) | `…SquarefreeGCDStratification.lean:443, 455` | Equivalent restatement of the same gate after gcd normalization. |
| `abs_h15DyadicNormalizedSuperperiodBoundaryDefect_smooth_le` | `…NormalizedSuperperiod.lean:628` | Absolute endpoint cost of one row: `≤ 2Lq/U²`. |
| `h15NormalizedSuperperiodBoundaryBudget` (+ `_balanced`) | `…NormalizedSuperperiod.lean:668, 675` | The endpoint budget `2Lq/U²`, balanced value `2L/U` — *not uniform in the progression modulus `L`*. |
| `H15NormalizedProgressionBoundaryAverage` | `…NormalizedSuperperiod.lean:690` | Gate demanding a power saving for the **sum of endpoint budgets**. |
| `H15NormalizedSuperperiodVariationPowerSaving` | `…NormalizedSuperperiod.lean:705` | Gate demanding a power saving for the **signed variation aggregate** (smooth weight). |
| `h15CoupledVariationBoundary_add_rowToPointwiseResidual` | `…ActiveIncidence.lean:347` | coupled (row) + row-to-pointwise residual `=` pointwise coupled aggregate. |
| `h15NormalizedProgressionRowToPointwiseResidual_eq_abelInterior_add_boundary` | `proofs/NBMellinTools/NB12BBLSH15CorrectionCoupledAbel.lean:193` | Residual `=` Abel interior + correction-coupled Abel boundary. |
| `h15CoupledVariationBoundary_add_abelInterior_add_boundary` | `…CorrectionCoupledAbel.lean:211` | The three-term exact assembly (this is the Task M / Query I "correction-coupled Abel identity"). |

**Green–Tao.** The strings `GreenTaoQuadraticMobiusPackage`,
`DivisorGrowthBudget`, and even `Green-Tao` do **not** occur in any `.lean`
file of this repository. `Green-Tao` occurs only in `README.md` prose. There
is therefore no formal Green–Tao quadratic Möbius orthogonality package to
apply, and the requested theorem

```lean
theorem H15CoupledVariationBoundaryDecay_of_GreenTao
  (HGT : GreenTaoQuadraticMobiusPackage) (HDiv : DivisorGrowthBudget) …
```

cannot even be *stated* against the existing formalization: two of its three
hypotheses name objects that do not exist. (Writing them from scratch would
be exactly the "reconstruction" the task forbids.)

---

## Phase 3 — Which source supplies the control?

**Answer: E — none of the above; the gap is identified, and it is not a
missing lemma but a logical equivalence with the open gate.**

* **A. Green–Tao package:** absent from the formalization (see above).
* **B. Divisor growth budget (Task M / Query I fibers):** present, and now
  applied to the coupled aggregate. It gives `Q/U`, i.e. balanced exponent
  `0`. This is proved, and it is *provably* not decay.
* **C. Correction-coupled Abel identity + one of the above:** the Abel
  identity is an exact identity, not an estimate; combined with (B) it still
  gives exponent `0`. What the Abel identity *does* buy is now recorded as a
  formal interface (see Phase 6, `H15PointwiseCoupledAggregateDecay_of_…`).
* **D. Something else in the formalization:** the only other candidates are
  the two superperiod gates `H15NormalizedSuperperiodVariationPowerSaving`
  and `H15NormalizedProgressionBoundaryAverage`, which are themselves
  unproven gates (they are `structure`s to be inhabited, not theorems). We
  do prove that these two together control the *pointwise* coupled aggregate
  (Phase 6), so they are the correct next targets — but they are hypotheses,
  not machinery.

---

## Phase 4 — What was proved instead (formal, `sorry`-free)

File `proofs/NBMellinTools/NB12BBLSH15CoupledVariationBoundaryDecay.lean`.

1. **Exact identification** (line 60):
   ```lean
   theorem h15NormalizedProgressionCoupledVariationBoundaryAggregate_eq_signedSquareDivisor
       {N g r U Q : ℕ} (hg : 0 < g) (hU : 0 < U) (hQ : 0 < Q) :
       h15NormalizedProgressionCoupledVariationBoundaryAggregate N g r U Q =
         h15RamanujanSignedSquareDivisorAggregate N g r U Q
   ```

2. **What the divisor budget gives** (lines 84, 94, 111):
   `|coupled| ≤ Q/U`; balanced `|coupled| ≤ 1`;
   `h15CoupledVariationBoundaryAbsoluteBalancedExponent = 0` is not negative.

3. **Equivalence with the open gate** (lines 120–169):
   `H15CoupledVariationBoundaryPowerSaving` ↔ `H15SignedSquareDivisorPowerSaving`
   (`nonempty_H15CoupledVariationBoundaryPowerSaving_iff`, line 163).

4. **Equivalence of the subexponential decay propositions** (line 252):
   ```lean
   theorem H15CoupledVariationBoundaryDecay_iff_signedSquareDivisorDecay
       {g r U Q : ℕ → ℕ}
       (hg : ∀ N, 2 ≤ N → 0 < g N) (hU : ∀ N, 2 ≤ N → 0 < U N)
       (hQ : ∀ N, 2 ≤ N → 0 < Q N) :
       H15CoupledVariationBoundaryDecay g r U Q ↔
         H15SignedSquareDivisorAggregateDecay g r U Q
   ```

`#print axioms` for every theorem above: `[propext, Classical.choice, Quot.sound]`.

---

## Phase 5 — Gap identification

### 5.1 Which term does not decay under the available input?

The **signed within-superperiod variation term**, summed over the active
divisor index and the modulus block:

$$
\mathcal V(N,g,r,U,Q)\;=\;\sum_{q}\;\sum_{d}\;\sum_{j}\;\sum_{k=jL}^{(j+1)L-1}
\Bigl(w_N(kq)-w_N(jLq)\Bigr)\,R_{g,r}(k,q,d),
\qquad L=L(g,d),
$$

with

* `w_N(u) = h15SupportedInverseSmoothEnvelope N g u = (log(N/(gu))/log N)² / u²`
  (`…RamanujanVariationAudit.lean:68`),
* `R_{g,r}(k,q,d) = h15PeriodNormalizedProgressionRow g r k q d`
  (`…SquarefreeGCDStratification.lean:188`), i.e. `μ(d)` times the sum of the
  paired direct cross mode over the reduced `q`-period `k` restricted to
  `L ∣ u`,
* `L(g,d) = h15SquareDivisorProgressionModulus g d`
  (`…SquarefreeGCDStratification.lean:39`).

**Precise name of the failing term:** the `q,d`-summed
`h15NormalizedRowSuperperiodVariationDefect` inside
`h15NormalizedProgressionCoupledVariationBoundaryAggregate`
(`…ActiveIncidence.lean:167–170`); in the smooth-weight (pointwise)
normalization the same object is
`h15DyadicNormalizedSuperperiodVariationDefect`
(`…NormalizedSuperperiod.lean:562`), whose control is exactly the unproven
gate `H15NormalizedSuperperiodVariationPowerSaving`
(`…NormalizedSuperperiod.lean:705`).

The retained endpoint term
`h15NormalizedRowSuperperiodBoundaryDefect` is *not* the obstruction in the
same sense: it is majorizable termwise by the explicit budget `2Lq/U²`
(`…NormalizedSuperperiod.lean:628`). Its difficulty is of a different type —
the budget is not uniform in the progression modulus `L`
(`h15NormalizedSuperperiodBoundaryBudget_balanced`: balanced value `2L/U`),
so summing it over the active divisor set requires the separate averaging
gate `H15NormalizedProgressionBoundaryAverage`.

### 5.2 What estimate would bound it?

A **signed** power saving of the shape

$$
\Bigl|\sum_{q\le Q}\ \sum_{d\ \text{active}}\ \sum_{j}\ \sum_{k\in[jL,(j+1)L)}
\bigl(w_N(kq)-w_N(jLq)\bigr) R_{g,r}(k,q,d)\Bigr| \;\le\; C\,U^{-\eta},
\qquad \eta>0,
$$

**uniform in `N ≥ 2`, `g ≥ 1`, `Q ≤ U`** — i.e. exactly an inhabitant of
`H15NormalizedSuperperiodVariationPowerSaving`. By the equivalence proved in
Phase 4 (item 3/4), any such estimate for the row-normalized aggregate is
equivalent to inhabiting `H15SignedSquareDivisorPowerSaving`, the H15 gate
itself.

What is *not* enough, and why (all of this is formal in the repository):

* termwise absolute values: `|μ(d)| ≤ 1`, `|cross mode| ≤ 1`,
  `|w_N| ≤ U⁻²` give `Q/U`, i.e. exponent `0`
  (`…SquarefreeDivisorExpansion.lean:516, 542, 554`, and for the coupled
  aggregate `…CoupledVariationBoundaryDecay.lean:84, 94, 111`);
* Abel summation on the unfreezing part is an exact identity, so it moves
  mass between an interior first-difference term and a boundary ledger
  without producing any saving (`…CorrectionCoupledAbel.lean:193, 211`);
* the divisor-first transpose and inactive-row pruning are exact
  reindexings and preserve the absolute exponent
  (`h15GCDStratifiedAbsoluteBalancedExponent_not_neg`,
  `…SquarefreeGCDStratification.lean:473`).

### 5.3 Type of failure

* **Not** a normalization issue. The weight is the genuine H15 smooth
  envelope, the reference point is the superperiod left endpoint, and the
  variation/boundary split is an exact identity proved before any absolute
  value is taken. Changing the reference point moves mass between the two
  terms but cannot change their sum, which is the full aggregate.
* **Not** a missing Kloosterman/Weil/Van der Corput bound in the narrow
  sense: those bound individual exponential sums, and the repository's
  three-case audit already assumes them. The obstruction survives *after*
  any per-`(q,d)` bound, because the required saving is in the **joint
  signed sum over the modulus `q`, the square-divisor index `d`, and the
  period index `k` simultaneously**; every step that separates these
  variables costs exactly the power that must be saved.
* **Not** a failure of Green–Tao "to cover this aggregate" in a form one
  could point to inside this repository: no Green–Tao input is formalized
  here at all. Even granting a quadratic-Möbius orthogonality package, it
  would have to be applied to a *signed cross-modulus* aggregate, i.e. to a
  correlation of `μ(d)` with the paired direct cross mode averaged over
  moduli — that is the "signed cross-modulus dispersion" barrier described
  in `H15_MATHEMATICAL_DOSSIER.md`.
* **What it actually is:** a *logical* identification. The coupled
  variation/boundary aggregate is the H15 signed aggregate. Task R's target
  is therefore equivalent to the open frontier estimate, and no amount of
  bookkeeping on the coupled decomposition can be strictly cheaper.

---

## Phase 6 — Positive by-products (also formal)

Also proved in
`proofs/NBMellinTools/NB12BBLSH15CoupledVariationBoundaryDecay.lean`:

* `abs_sum_h15DyadicNormalizedSuperperiodBoundaryDefect_le_budget` (line 274) —
  the boundary half of the pointwise coupled aggregate is dominated by the
  repository's endpoint budget sum.
* `abs_h15NormalizedProgressionPointwiseCoupledAggregate_le` (line 303) and
  `H15PointwiseCoupledAggregatePowerSaving.ofVariationAndBoundaryAverage`
  (line 347) — the two named superperiod gates
  (`H15NormalizedSuperperiodVariationPowerSaving`,
  `H15NormalizedProgressionBoundaryAverage`) together yield a power saving
  for the **pointwise** coupled aggregate with exponent `min(η_V, η_B)`.
  This isolates the exact pair of missing inputs on the pointwise side.
* Decay-calculus interface with the Task Q objects (lines 377–424):
  `H15PointwiseCoupledAggregateDecay_of_coupled_and_abel` and
  `H15CoupledVariationBoundaryDecay_of_pointwise_and_abel`, both obtained
  from the exact three-term Abel assembly. These make precise the sense in
  which the Task Q terminus, the Task R proposition, and the two Abel
  aggregates combine.

**Unverified heuristic (flagged as such, not proved):** the endpoint budget
sum appearing in `H15NormalizedProgressionBoundaryAverage` is a sum of
*nonnegative* terms `2Lq/U²` over active `d`; since `L(g,d)` grows like `d²`
and `d` ranges up to about `√(gU)`, that sum plausibly grows with `U` at the
balanced scale `Q = U`, in which case that gate would be unsatisfiable and
the boundary term too would have to be kept signed. This has **not** been
verified in Lean and should be treated as a conjecture about the shape of
the gate, not a result.

---

## Build note

`lakefile.toml` in this repository contains Lean-syntax configuration, so
`lake` cannot parse it; the file was left untouched as required. The H15
chain was compiled directly with `lean` via
`scripts/build_h15_chain.py <module>` (oleans land in `.leanbuild/`).
Compiling the chain in Lean 4.28.0 required small version-drift fixes to
existing files (Mathlib renames `integrable_finsetSum → integrable_finset_sum`,
`integral_finsetSum → integral_finset_sum`,
`tendsto_finsetSum → tendsto_finset_sum`,
`continuous_finsetSum → continuous_finset_sum`; replacements for the
now-absent `Measurable.tsum` / `AEMeasurable.tsum` by explicit
partial-sum-limit arguments; a `Finset.card_le_card_of_injOn` coercion
update; one `simp`-brittle step made explicit). The module
`RiemannHypothesis.Basic.CriticalStrip` is imported by
`proofs/route-c/modules/BaezDuarte.lean` but its source is **absent from this
snapshot**; `scripts/compat/RiemannHypothesis/Basic/CriticalStrip.lean`
supplies it as `RH.Basic.RiemannHypothesis := Mathlib's RiemannHypothesis`,
with no axioms. None of the results reported here mention that declaration,
and their `#print axioms` output confirms no `sorryAx` and no custom axioms.
