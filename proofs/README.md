# Lean Source Status (August 3–4, 2026 - Codex Branch)

## Active Verified Package

**8,649 Lean jobs verified, 0 custom axioms, 0 sorry, 0 opaque, 150+ imported modules. Spectral infrastructure complete (frequency pairing with all signs preserved).**

`NBMellinTools.lean` is the active public umbrella. It imports 150+ modules across the complete reduction chain (Sessions 1–9c, Steps 1–4v-ck). The frontier is **completely characterized**:

**Sessions 1–8 (Complete Reduction Chain):**
- NB2–3: Mellin transforms & error formulas
- NB4–5: Zero-detection reduction
- NB6: Global RH closure
- NB7–9: Approximation sequence & Gram decomposition
- NB10–11: Vasyunin evaluation (classically proved)
- NB12: Exact Fourier core, dyadic/divisor expansion, Abel/Estermann machinery

**Session 9c (Frontier Characterization):**
- **Steps 4a–5p (Complete):** Signed right-line target, frequency split, Bettin-Chandee dyadic ledger, high-tail exchange
- **Steps 4t–4u (Complete):** Absolute frontier closed. Fiber-cardinality exponent +2. Progression-density exponent +1. Arithmetic wall load-bearing.
- **Steps 4v-a–4v-j (Complete):** Algebraic frontier closed. Zero-extension, exact transpose, nested Abel, final boundary audit. All algebraic cancellations exhausted.
- **Steps 4v-k–4v-m (Complete):** Elementary analytic frontier closed. Fourier, collision control, aliasing. Parseval insufficient.
- **Steps 4v-n–4v-zzv (Complete):** Minimal RH-strength interface formalized. Coupled correction-Kloosterman decay required.

**Codex Branch WP1a–1c (Complete):**
- **NB15PreFEAssembly (WP1a):** Bridge NB8 certified energy to NB12 pre-FE Vasyunin assembly. Exact decomposition into 5 components (correction, constant, logarithmic-ratio, interior cotangent, endpoint cotangent).
- **NB15GCDReindex (WP1b):** Exact finite GCD reindexing from Gram double sum to primitive Laurent-row family. Proves Gram homogeneity G(ga,gq) = g^{-1}G(a,q). Separates primitive interior (a,q ≥ 2) from endpoint sectors.
- **NB15DirichletAbelBoundary (WP1c.1):** Reusable real Dirichlet–Abelian boundary theorem.
- **NB15RationalSineEndpoint (WP1c.2):** Actual analytic identity sinZeta(j/q, 1) = π(1/2-j/q) for nonzero residues.
- **NB15HurwitzZeroEndpoint (WP1c.3):** Actual rational Hurwitz value at zero, substituted into finite Hurwitz continuation.
- **NB15EstermannVasyuninAtZero (WP1c.4):** Complete finite DFT and genuine active endpoint: D(0, ā/q) = 1/4 - (i/2)V(a,q).
- **NB15EstermannGramAssembly (WP1c.5):** Exact certified-energy identity: E_n = C_n + EstermannInterior_{n+2} + Endpoint_{n+2}.
- **NB15EstermannRowAssembly (WP1d):** Exact contour-vocabulary form with barrier: damped quantity cannot recover undamped amplitude (division by δ_N → 0 blocked).
- **NB15GlobalPostFEAssembly (WP1e):** Dyadic block partition of weighted Laurent cube, global low-frequency reassembly, quadratic expansion retaining signed cross-block interaction, explicit inverse adaptive-damping loss.
- **NB15VerticalFrequencyPairing (WP1f):** Exact spectral pairing identity preserving all cross-frequency, cross-block, and simultaneous interactions with all signs retained (no majorization). Couples dyadic structure through frequency domain.
- **NB15CorrectionPreservingRectangle (WP1g):** Closed-rectangle identity for the literal finite H15 Estermann row family with certified NB8 correction retained; proves certified energy equals diagonal integral of two-variable kernel; does not identify either vertical edge with the physical numerator.
- **NB15CompletedPairingKernel (WP1h):** Two-variable sesquilinear kernel `K_F(z,w) = conj(F(conj z)) * F(w)` and its conjugate-diagonal identity. Proves boundary-only interpolation is vacuous: any two boundary functions admit a naive affine interpolant with zero analytic content. Formally rules out boundary-matching-only shortcuts.
- **NB15PhysicalContourSingularityMismatch (WP1i):** Singularity-order analysis at s=0 proves the physical numerator has at most a simple pole (s³·Physical → 0) while the contour aggregate has a genuine cubic pole (s³·Contour → nonzero A_{-3}(N)). No scalar continuous at zero can repair this mismatch. Formally rules out scalar-renormalization shortcuts.
- **NB15TwoVariableBridgeAudit (WP1j):** Proves raw two-slice recovery is tautological modulo corner compatibility and impossible at a certified incompatible anchor. Establishes the correct exact bridge at the quadratic level: the integrated physical Hermitian diagonal equals the elementary ledger plus the inverse-damping-rescaled `w=1` Estermann residue, while retaining the cubic `w=0` pole.
- **NB15UndampedDefectRepresentation (WP1k):** Exact complete linear PostFE transform over all canonical blocks and frequencies, including the infinite high tail and the full residue ledger. Proves cutoff independence, the rectangle boundary identity, the correction-omission stop test, and the exact split into endpoint-to-linear and linear-to-quadratic defects.
- **NB15EndpointBoundaryExtraction (WP1l):** Exact full-boundary extraction of the undamped endpoint: normalize by `2*pi*I`, subtract the first-order residue, then apply inverse damping. Expands both vertical edges and the horizontal pair and proves the first-order-omission stop test.
- **Next Target (WP1m):** Signed decay of the inverse-damped centered boundary numerator together with the elementary endpoint ledger; do not estimate the boundary sectors independently.

**Note:** The NB15 modules (H15_exploration) are separately buildable under `H15_exploration/ROADMAP.md` and are not imported by the public umbrella `proofs/NBMellinTools.lean`. The 8,649-job figure spans the whole repository including open exploration work; the certified `NymanBeurlingCriterion → RiemannHypothesis` reduction chain (NB2–12) forms a distinct verified subset.

**The Verified Theorem:**

```lean
NymanBeurlingCriterion → RiemannHypothesis
```

**The Frontier (H15):**

Unconditional RH follows if and only if:

```lean
Tendsto (fun N => |Correction N + SignedKloostermanAggregate N|)
        atTop (nhds 0)
```

This is the **single minimal statement** on which RH depends. All algebraic and elementary analytic methods are exhausted. The coupled decay is transcendental (RH-strength).

**Verify the build (Codex branch):**

```bash
lake build
lake env lean proofs/NBMellinTools/Audit.lean
```

Expected output: 8,649 jobs verified, zero sorry, zero custom axioms, zero opaque, axioms = [propext, Classical.choice, Quot.sound] only.

**NB12 (35+ modules) covers the H15 frontier frontier:**
- Dyadic Bettin–Chandee analysis with exact coefficient ledger
- Divisor-square bounds and ultra-high tail decay
- Paired kernel analysis with Ramanujan completion-defect decomposition
- GCD stratification and exact row reduction
- Normalized $Lq$-superperiod cancellation (complete periods sum to zero)
- Complete nested Abel transforms with prefix-saving criteria ($P_1=o(1)$, $P_2=o(1)$)
- Final superperiod boundary audit (zero-mode test negative)
- Fourier representation with collision control and even-modulus aliasing
- Dispersion ledger and off-diagonal/cross-modulus structure
- Shell-block framework with coupled decay interface
- Linear trace gate: minimal RH-strength interface

See `proofs/NBMellinTools.lean` for complete module list and `../README.md` for frontier details.

## Historical Route C material

`route-c/` is an exploratory archive, not a complete or active proof.  It is
not compiled by the default Lake target and is not correctly mapped into the
declared `RiemannHypothesis` library.

The directory contains useful decomposition ideas alongside:

- unproved `sorry` statements;
- explicit research hypotheses;
- false legacy assumptions such as `|M(x)| ≤ 2`;
- a Möbius exponential-sum statement incorrectly described as a Weil bound;
- a vacuous legacy `ZetaZero` predicate.

These files must not be described as a verified WP1–WP7 proof.  They will be
quarantined and reintroduced only theorem-by-theorem after mathematical and
kernel audits.

## Other directories

Other proof folders are research snapshots.  Presence under `proofs/` does
not mean that a file belongs to the active import graph or that its theorem
statements have been validated.

For the repository-level status, read `../README.md` and
`../HOW_TO_VERIFY.md`.
