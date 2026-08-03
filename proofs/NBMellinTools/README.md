# NBMellinTools: Verified Modules

**Active, kernel-verified Lean modules for the Riemann Hypothesis reduction.**

Status: 148 imported modules, 0 custom axioms

---

## Core Module Inventory (selected)

| Module | What It Proves | Lines | Status |
|--------|---|---|---|
| **NB2BaseMellin.lean** | Mellin transform identities & Báez–Duarte error formula | 500+ | ✅ |
| **NB2Mellin.lean** | Alternative Mellin formulation | 300+ | ✅ |
| **NB2ApproximationAlgebra.lean** | Approximation sequence algebra | 400+ | ✅ |
| **NB3MellinContinuity.lean** | Mellin transform continuity properties | 250+ | ✅ |
| **NB4ZeroDetection.lean** | Zero-detection reduction chain | 350+ | ✅ |
| **NB5FunctionalEquationClosure.lean** | Functional equation closure to critical strip | 300+ | ✅ |
| **NB6GlobalClosure.lean** | Global RH closure (Mathlib interface) | 200+ | ✅ |
| **NB7ApproximationSequence.lean** | Vanishing-error sequence equivalence | 250+ | ✅ |
| **NB8LogTaperTarget.lean** | Log-taper coefficient definitions & target | 400+ | ✅ |
| **NB9QuadraticExpansion.lean** | Gram expansion & error decomposition | 350+ | ✅ |
| **NB10VasyuninReduction.lean** | Vasyunin reduction infrastructure | 300+ | ✅ |
| **NB11VasyuninEvaluation.lean** | Classical pointwise Vasyunin evaluation (✨ newly proved) | 450+ | ✅ |
| **NB12VaalerTail.lean** | High-mode Vaaler bounds (scaffold) | 200+ | 🟡 |
| **NB13BilinearReduction.lean** | Master reduction theorem & frontier problem | 400+ | ✅ |
| **NB14BettinEhmCollapse.lean** | Exact q≥2 collapse to (d,m) bilinear | 300+ | ✅ |
| **NB12BBLSCorrectionBridge.lean** | Complete signed Laurent aggregate and exact global correction gap | 260+ | ✅ |
| **NB12BBLSOnePoleRemoval.lean** | Constructive removal of `s=0,1`; finite contour identity on `Re(s)<2` | 500+ | ✅ |
| **NB12BBLSH15Rectangle.lean** | Four-pole rectangle specialized to the actual H15 Möbius/log-taper rows | 200+ | ✅ |
| **NB12BBLSH15MajorantAudit.lean** | Exact Abel exponent split and factored positive-line majorant | 200+ | ✅ |
| **NB12BBLSH15ThreeHalfLine.lean** | Unconditional `Re(s)=3/2` Estermann row growth and fixed-cutoff integrability | 400+ | ✅ |
| **NB12BBLSH15SignedRightLine.lean** | Correction-preserving rectangle transfer and signed compact/tail `L¹` gate | 170+ | ✅ |
| **NB12BBLSH15BettinChandeeAudit.lean** | Exact H15 coefficient factorization and balanced Bettin--Chandee exponent stop test | 170+ | ✅ |
| **NB12BBLSH15FrequencySplit.lean** | Exact Estermann low/high split with the complete correction ledger retained on the low side | 250+ | ✅ |
| **NB12BBLSH15FrequencyIntegral.lean** | Global and finite-window high-frequency `tsum`–integral exchange; exact identification of the algebraic high remainder | 500+ | ✅ |
| **NB12BBLSH15BettinChandeeLedger.lean** | Both-orientation dyadic reassembly, exact supported coefficient masses, complete phase-factor audit, and hybrid ultra-high cutoff | 700+ | ✅ |
| **NB12BBLSDivisorSquareDyadic.lean** | Elementary four-factor injection and explicit divisor-square dyadic bound with constant 2 | 380+ | ✅ |
| **NB12BBLSH15UltraHighTail.lean** | Cauchy--Schwarz block `L¹` bound, dyadic summability, and vanishing frequency-only ultra-high tail | 220+ | ✅ |
| **NB12BBLSH15MovingCutoff.lean** | Exact shifted-frequency budget, uniform domination of the actual integrated remainder, adaptive cutoff selection, and cofinal vanishing | 400+ | ✅ |
| **NB12BBLSH15ArithmeticMass.lean** | Explicit `2π(n+2)^5` row-mass bound and polynomial ledger for the actual ultra-high integral remainder | 230+ | ✅ |
| **NB12BBLSH15FrequencyTailRate.lean** | Explicit polynomial ultra-high decay plus the exact correction-preserving low/middle/ultra-high split and canonical finite middle-window interfaces | 700+ | ✅ |
| **NB12BBLSH15BettinChandeeInstantiation.lean** | Exact double-inversion phase stop test; proves that actual H15 dual phases are direct additive rather than Bettin--Chandee Kloosterman fractions | 400+ | ✅ |
| **NB12BBLSH15DirectAdditiveReassembly.lean** | Exact fixed-height separated H15 summand, unitary `q^(2it)`/`r^(-it)` coefficient budgets, and quadratic-threshold additive large-sieve stop test | 400 | ✅ |
| **NB12BBLSH15PairedDirectKernel.lean** | Exact paired-orientation norm square, complete reduced-residue cancellation, and isolation of the surviving weighted Ramanujan cross correlation | 300+ | ✅ |
| **NB12BBLSH15RamanujanCompletionDefect.lean** | Exact full-period cancellation, completion-defect identity, at-most-`2q` boundary support, and explicit `2q/U²` endpoint bound | 500+ | ✅ |
| **NB12BBLSH15RamanujanVariationAudit.lean** | Exact smooth/squarefree variation split and balanced absolute-completion stop test with exponent zero | 400+ | ✅ |
| **NB12BBLSH15SquarefreeDivisorExpansion.lean** | Exact `mu^2` square-divisor expansion, signed progression-row reindexing, and second balanced exponent-zero stop test | 500+ | ✅ |
| **NB12BBLSH15SquarefreeGCDStratification.lean** | Exact gcd normalization, inactive-row pruning, active progression form, and normalized balanced stop test | 400+ | ✅ |
| **NB12BBLSH15NormalizedSuperperiod.lean** | Exact `Lq`-superperiod cancellation, weighted row completion, `2Lq/U²` boundary bound, and normalized-modulus stop test | 600+ | ✅ |
| **NB12BBLSH15NormalizedModulusAverage.lean** | Exact active-`L` fiber reindexing, multiplicity `≤τ(g)`, and absolute balanced exponent-growth stop test | 250+ | ✅ |
| **NB12BBLSH15BoundaryDensity.lean** | Sharp endpoint density `≤2(q+1)`, refined smooth boundary bound, and linear-growth balanced stop test | 250+ | ✅ |
| **NB12BBLSH15ActiveIncidence.lean** | Exact extension by zero from moving periodwise active divisor sets to their common dyadic union | 80 | ✅ |
| **NB12BBLSH15FinalBoundaryLinearTraceGate.lean** | Minimal correction-coupled linear trace target equal to the completed boundary square | 150+ | ✅ |
| **NB12BBLSH15FinalBoundaryLinearTraceCompatibility.lean** | Exact trace-to-residual bridge and raw-contour cutoff mismatch stop test | 100+ | ✅ |
| **NB12BBLSH15FinalBoundaryLinearTraceDecay.lean** | Moving trace-scale decay implies decay of the genuine active residual | 80+ | ✅ |
| **NB12BBLSH15LocalizedLaurentProjection.lean** | Exact fixed-`g`, dyadic-`q` Laurent support projection with complementary-row ledger | 110+ | ✅ |
| **NB12BBLSH15LocalizedFrequencySplit.lean** | Localized functional equation, finite frequency slices, and exact direct-additive realization | 160+ | ✅ |
| **NB12BBLSH15LocalizedQuadraticProjection.lean** | Exact recovery of the full endpoint boundary from the centered paired-kernel norm square | 110+ | ✅ |
| **NB12BBLSH15DoublyLocalizedOrientation.lean** | Exact `(g,U,Q)` support and post-functional-equation orientation audit | 100+ | ✅ |
| **NB12BBLSH15TransposeInvariant.lean** | Literal transpose invariance of row validity, weight, reduced row, post-FE variables, and summand | 150+ | ✅ |
| **NB12BBLSH15OrientationNormalizedQuadratic.lean** | Raw-block transpose identity and corrected endpoint-aligned post-FE block `2F(U,Q)` | 200+ | ✅ |
| **NB12BBLSH15PostFECoefficientExpansion.lean** | Exact centered block expansion into diagonal incidence mismatch and signed ordered cross-row dispersion | 280+ | ✅ |
| **NB12BBLSH15PostFEIncidenceCollection.lean** | Exact collection of endpoint and Laurent diagonal coefficients by the common arithmetic key `(u,q)` | 220+ | ✅ |
| **NB12BBLSH15PostFEUnionMismatch.lean** | Exact zero-extension to the common union support and canonical signed mismatch-minus-dispersion identity | 170+ | ✅ |
| **NB12BBLSH15PostFERamanujanCompletion.lean** | Exact residue-class collection; canonical fiber-mean centering; complete cross-mode residue cancellation; incomplete trace identified as the negative missing-residue trace | 418 | ✅ |
| **NB12BBLSH15PostFECrossRowResidueAlignment.lean** | Exact ordered-pair residue collection and support stop test: dispersion is actual–actual while the linear trace is missing-residue supported | 181 | ✅ |
| **NB12BBLSH15PostFEGlobalBoundaryTransfer.lean** | Exact collection of complex ordered-pair scalars, residue-pair kernel separation, four signed phase populations, and correction-coupled global boundary-transfer frontier | 340+ | ✅ |
| **NB12BBLSH15PostFECommonAdditivePhase.lean** | Exact common-modulus additive-character normalization of all four ordered populations and doubled-character normalization of the retained missing-residue trace | 370+ | ✅ |
| **NB12BBLSH15PostFEBilinearExponentAudit.lean** | Exact post-collection ranges and L¹ mass ledger; common modulus `qq' ~ Q²`; formal inverse-phase and direct-additive pair exponent stop tests | 220+ | ✅ |
| **NB12BBLSH15PostFEJointTransformInterface.lean** | Generic joint-coefficient transform retaining all four phase populations and the missing-residue correction; moving-scale decay package and centered-defect implication | 260+ | ✅ |
| **NB12BBLSH15PostFEFrequencyGram.lean** | Exact reassembly into missing and four-orientation pair atoms; correction-preserving finite frequency Gram sectors | 250+ | ✅ |
| **NB12BBLSH15PostFEFrequencyOrthogonality.lean** | Exact complete-period difference/sum character kernels and collision criteria on `ZMod` | 160+ | ✅ |
| **NB12BBLSH15PostFEFrequencyProductKernels.lean** | Real/imaginary product kernels and their exact collision-indicator formulas | 250+ | ✅ |
| **NB12BBLSH15PostFEFrequencyCollisionGram.lean** | Abstract common-period correction energy and explicit signed collision Gram | 220+ | ✅ |
| **NB12BBLSH15PostFEFrequencyLift.lean** | Literal H15 base frequencies and exact lift from a denominator to a positive multiple | 130+ | ✅ |
| **NB12BBLSH15PostFEReducedMissingSupport.lean** | Removes non-coprime zero atoms from the missing trace without changing the correction transform | 150+ | ✅ |
| **NB12BBLSH15PostFEReducedPairSupport.lean** | Removes non-coprime zero atoms from all four pair populations and preserves the complete transform | 160+ | ✅ |
| **NB12BBLSH15PostFECommonSuperperiod.lean** | Positive product-square period, denominator divisibility, and reusable character lift to a common `ZMod` | 190+ | ✅ |
| **NB12BBLSH15PostFELiteralLiftedFrequencies.lean** | Total literal missing/pair frequency lifts and exact phase recovery on reduced supports | 130+ | ✅ |
| **NB12BBLSH15PostFELiteralCommonPeriodValue.lean** | Four-orientation literal correction transform as one common-period value | 210+ | ✅ |
| **NB12BBLSH15PostFELiteralCollisionEnergy.lean** | Frozen-row full-period energy and explicit literal collision indicators | 190+ | ✅ |
| **NB12BBLSH15PostFECoefficientFrequencyFactorization.lean** | Common divisor-frequency norm-square factor in pair and Laurent coefficients | 160+ | ✅ |
| **NB12BBLSH15PostFEResidueFrequencyFactorization.lean** | Exact affine factorization of residue mismatches and fiber means | 90+ | ✅ |
| **NB12BBLSH15PostFEAffineFrequencyTransform.lean** | Complete signed transform equals endpoint plus explicit divisor-square weight times Laurent/pair transform | 160+ | ✅ |
| **NB12BBLSH15PostFEWeightedAffineEnergy.lean** | Actual varying-row energy equals endpoint square plus twice the signed weighted mixed sector plus weighted Laurent/pair square | 120+ | ✅ |
| **NB12BBLSH15PostFESignedCorrelationDefects.lean** | Sharp Cauchy bound; exact norm-imbalance plus antiparallel-alignment defect decomposition and asymptotic equivalence | 190+ | ✅ |
| **NB12BBLSH15PostFESignedMixedExpansion.lean** | Literal split of the weighted mixed sector into the missing-residue trace and all four signed Estermann pair populations; exact alignment-residual equivalence | 180+ | ✅ |
| **NB12BBLSH15PostFESignedMixedAtoms.lean** | Exact atom-level reindexing of both signed mixed ledgers with the divisor-square weight, four orientation signs, and Archimedean normalization retained | 210+ | ✅ |
| **NB12BBLSH15PostFEWeightedCollisionSplit.lean** | Orientation-first partition of the weighted atom correlations into equal/opposite-frequency collisions and retained off-diagonal ledgers; no false orthogonality claim | 280+ | ✅ |
| **NB12BBLSH15PostFECollisionMatchingAudit.lean** | Exact collision-mismatch and signed off-diagonal ledgers; full energy normal form and sufficient three-limit vanishing theorem | 160+ | ✅ |
| **NB12BBLSH15PostFECollisionCongruenceClassification.lean** | Lifted collision iff explicit numerator congruence/divisibility; exact diagonal/incidence, same-modulus alias, and cross-modulus ledger partitions | 380+ | ✅ |
| **NB12BBLSH15PostFEReducedSupportNumerators.lean** | Cancels the common-period factor exactly; evaluates missing and oriented-pair native numerators; reduces actual-support collisions to least-common-multiple congruences | 260+ | ✅ |
| **NB12BBLSH15PostFENativeCollisionDiophantineAudit.lean** | Odd-modulus missing collisions reduce to literal diagonal/opposite residues; even moduli retain exactly the half-modulus two-torsion alternatives | 200+ | ✅ |
| **NB12BBLSH15PostFESignedMissingPairNativeCongruences.lean** | Exact left/right endpoint native-`lcm` reduction and all eight signed missing–pair product-modulus congruence alternatives; incidence is not assumed to imply collision | 300+ | ✅ |
| **NB12BBLSH15PostFEExternalMissingPairCongruenceShells.lean** | External missing modulus `p`: exact gcd-reduced coprime lift multipliers, named equal/opposite shells at `lcm p (qq')`, and actual-support instantiation | 200+ | ✅ |
| **NB12BBLSH15PostFEExternalShellCountingStopTest.lean** | Coprime-shell divisibility extraction and exact count `(p-1)/(p/gcd(p,qq'))+1` of admissible missing native residues | 180+ | ✅ |
| **NB12BBLSH15PostFEExternalShellDensityDegeneracy.lean** | Exact multiplier-one criterion `p ∣ qq'`, full-support consequence, and an external `(6,2,3)` counterexample to uniform density saving | 100+ | ✅ |
| **NB12BBLSH15PostFEActualSupportDegenerateSector.lean** | Exact signed split of the actual cross-modulus collision ledger into `p ∣ qq'` full-density and `p ∤ qq'` favorable sectors | 170+ | ✅ |

**Legend:** ✅ = Verified, 🟡 = Scaffold (needs genuine bounds)

---

## How to Read These Modules

### **For Reviewers:**
1. Start with **NB2BaseMellin.lean** — understand the foundation
2. Follow the dependency chain: NB3 → NB4 → NB5 → NB6
3. Jump to **NB8LogTaperTarget.lean** — understand the target
4. Review **NB11VasyuninEvaluation.lean** — the newest work
5. Check **NB13BilinearReduction.lean** — the frontier

### **For Contributors Fixing NB12:**
1. Read **NB12VaalerTail.lean** — understand current structure
2. Read **NB8LogTaperTarget.lean** — understand what NB12 must bound
3. Read **NB11VasyuninEvaluation.lean** — understand the decomposition pattern
4. Implement actual Vaaler polynomial approximation
5. Update the high-mode bound

### **For Frontier Problem Research:**
1. Read **NB13BilinearReduction.lean** — exact problem statement
2. Read [../docs/H15_MATHEMATICAL_DOSSIER.md](../docs/H15_MATHEMATICAL_DOSSIER.md) — why it's hard
3. Read [../docs/FAILED_ROUTES_ANALYSIS.md](../docs/FAILED_ROUTES_ANALYSIS.md) — what doesn't work

---

## Key Files

| File | Purpose |
|---|---|
| **Audit.lean** | Verification script (`lake env lean Audit.lean` to check axioms) |
| **NBMellinTools.lean** | Umbrella that imports all verified modules |

---

## Axiom Verification

```bash
cd /path/to/riemann-github
lake build
lake env lean proofs/NBMellinTools/Audit.lean
```

**Expected output:**
```
All theorems depend on: [propext, Classical.choice, Quot.sound]
```

These are Lean's standard logical axioms, not custom mathematical assumptions.

---

## Building a New Module

If you add a new module (e.g., NB15Something.lean):

1. **Create the file** with proper header docstring
2. **Add it to Audit.lean** so it's verified
3. **Import in NBMellinTools.lean** to include it in the umbrella
4. **Run verification:**
   ```bash
   lake build
   lake env lean proofs/NBMellinTools/Audit.lean
   ```
5. **Ensure zero new axioms**

---

## Dependencies

**Build order** (rough):
```
NB2 (Mellin transforms)
  ↓
NB3 (continuity)
  ↓
NB4 (zero-detection)
  ↓
NB5 (functional equation)
  ↓
NB6 (global closure)
  ↓
NB7 (approximation sequence)
  ↓
NB8 (log-taper target)
  ├→ NB9 (Gram expansion)
  ├→ NB10 (Vasyunin infrastructure)
  └→ NB11 (Vasyunin evaluation)
      └→ NB12 (Vaaler tail)
          └→ NB13 (master reduction)
              └→ NB14 (collapse)
```

---

## Status

**Verified:** Complete umbrella and axiom-audit imports

**Build:** Clean; 8,630 jobs in the latest verified build

**Axioms:** 0 custom axioms

**Remaining:** estimate one exact coefficient-level expression: the
canonical fiber-mean-zero endpoint/Laurent coefficient variation plus its
mean-weighted negative missing-residue trace, minus the signed ordered
cross-row dispersion.  The
ultra-high sector, functional-equation split, endpoint completion, `(g,U,Q)`
support, orientation transpose, post-FE alignment, coefficient expansion, and
arithmetic-key and residue-class collection are verified.  The complete
cross-mode residue mean cancels exactly.  The ordered dispersion is now
collected by residue-key pairs and its support is proved disjoint from the
missing-residue support in each coordinate.  The final analytic decay remains
open and is RH-strength.

**Next work:**
- Partition the actual H15 external support into the degenerate sector
  `p ∣ qq'` and the favorable sector `p ∤ qq'`, retaining signed coefficients
- Test whether actual support and Möbius/log-taper weights suppress the
  full-density degenerate sector
- Test whether the literal diagonal and colliding endpoint-incidence sectors reproduce
  an explicit part of the norm product
- Retain and estimate every surviving even-modulus alias, cross-modulus
  collision, and signed weighted off-diagonal sector

See [../CONTRIBUTING.md](../CONTRIBUTING.md) for details on all three targets.

---

**Last Updated:** August 3, 2026
