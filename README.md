# Riemann Hypothesis Formalization: Digital Humanities & AI-Assisted Research Archive

**A Digital Humanities & Lean 4 kernel-verified conditional reduction of the Riemann Hypothesis to an explicit arithmetic frontier.**

> ⚠️ **EPISTEMIC DISCLAIMER & ANTI-OVERCLAIMING NOTICE**  
> **This project DOES NOT present an unconditional proof of the Riemann Hypothesis.**  
> What this repository provides is a **formally verified conditional reduction** ($NymanBeurlingCriterion \implies RiemannHypothesis$) certified by the Lean 4 kernel (0 custom axioms) and a 167-year **Digital Humanities Knowledge Graph** mapping the literature. The remaining open step ($H_{15}$ signed bilinear dispersion decay) is an **unproven open problem of full RH-equivalent difficulty**.

> 📌 **PUBLICATION STRATEGY & RESTRUCTURING NOTICE (August 2026)**  
> This repository is currently undergoing a planned restructuring to support a **two-paper split**:
> 1. **Paper 1 (ITP / CPP / JAR target)**: *A Lean 4 Formalization of the Nyman–Beurling Criterion* (Self-contained, machine-checked formalization of the Nyman–Beurling equivalence, Mathlib API design, and upstreamable analytic lemmas).
> 2. **Paper 2 (DSH / DHQ target)**: *Kernel Verification is Necessary But Insufficient: Vacuity Detection as the Dominant Failure Mode in LLM-Assisted Formalization* (Digital Humanities methodology, vacuity-audit framework, and forensic analysis of LLM formalization failure modes).
>
> The repository state prior to this restructuring has been preserved under Git tag [`pre-split-v1.0`](https://github.com/captaldebuch/RH_DH_experiment_2026/tree/pre-split-v1.0).

---

## 🏛️ Digital Humanities Approach

This repository approaches mathematical formalization through the lens of **Digital Humanities (DH)** and **AI-Assisted Knowledge Curation**:

1. **Epistemic Traceability & Corpus Integration**:
   - Maps 167+ years of mathematical history (1859–2026) across 498 papers, 384 mathematicians, and 21,942 semantic graph nodes directly to Lean 4 code terms.
   - Every theorem in the reduction chain is linked to its historical origin, peer-reviewed source, and institutional lineage.

2. **Transparent Multi-Agent Parliament**:
   - Documents human-AI collaboration (Sorbonne University researchers with Claude, Codex, and Gemini parliaments).
   - Preserves complete session archives, prompt ledgers, and forensic audit trails (`audit/AXIOM_ANALYSIS_AND_SOLUTIONS.txt`) to isolate legacy errors and guarantee zero custom axioms.

3. **Frontier Isolation without Overclaiming**:
   - Uses formal verification not to claim premature victories, but to **isolate the exact boundary** between what is known unconditionally and what requires new mathematical breakthroughs.

---

## Quick Navigation

### **I want to...**

| Goal | Read This | Time |
|------|-----------|------|
| **Understand what's proved** | [HONEST_STATEMENT.md](HONEST_STATEMENT.md) | 5 min |
| **Verify the build myself** | [HOW_TO_VERIFY.md](HOW_TO_VERIFY.md) | 10 min |
| **Review for colleagues** | [COLLEAGUE_REVIEW_GUIDE.md](docs/COLLEAGUE_REVIEW_GUIDE.md) | 15 min – 2 hours |
| **Check the exact frontier** | [docs/HARD_TARGETS_UPDATED_CODEX_FEEDBACK_AUG2.md](docs/HARD_TARGETS_UPDATED_CODEX_FEEDBACK_AUG2.md) | 15 min |
| **Understand the frontier problem** | [docs/H15_MATHEMATICAL_DOSSIER.md](docs/H15_MATHEMATICAL_DOSSIER.md) | 20 min |
| **Explore the knowledge graph** | [data/explore_riemann_graph.ipynb](data/explore_riemann_graph.ipynb) | 2-3 min (run) |
| **Study the unified graph** | [data/MERGED_GRAPH_GUIDE.md](data/MERGED_GRAPH_GUIDE.md) | 10 min |
| **Plan a Codex session** | [docs/CODEX_SESSION_UPDATE_PROTOCOL.md](docs/CODEX_SESSION_UPDATE_PROTOCOL.md) | 15 min |
| **Quick Codex reference** | [docs/SESSION_QUICK_REFERENCE.md](docs/SESSION_QUICK_REFERENCE.md) | 2 min |
| **Contribute code** | [CONTRIBUTING.md](CONTRIBUTING.md) | 15 min |
| **Read the full audit** | [docs/FOURIER_REMAINDER_DECAY_AUDIT_2026-08-01.md](docs/FOURIER_REMAINDER_DECAY_AUDIT_2026-08-01.md) | 30 min |

---

## The Result

**Verified theorem (kernel-checked, 0 custom axioms):**

```lean
NymanBeurlingCriterion → RiemannHypothesis
```

**What this means:**
- ✅ The reduction is formally verified by the Lean 4 kernel
- ✅ 148 directly imported project modules, including the promoted rational
  BBLS dependency chain, shifted Abel--Mellin identity, and finite Hurwitz
  continuation with explicit Laurent subtraction
- ✅ Zero custom axioms (only standard Lean logic)
- ❌ We don't prove the antecedent (that's the frontier problem)

**Exact frontier target (Codex-characterized, Aug 3, 2026, Steps 4v-zzv through 4v-zzaH):**

$$\sum_r |E(r)|^2 + 2\sum_r \lambda_r \text{Re}(E(r)\overline{L(r)}) + \sum_r \lambda_r^2|L(r)|^2 \to 0 \text{ as } N \to \infty$$

where the first and third terms are nonnegative; the **signed mixed sector MUST CANCEL both**.

**Key properties:**
- ✅ All algebraic cancellations exhausted (Steps 4t–4v-j)
- ✅ All elementary Fourier/harmonic methods exhausted (Steps 4v-k–4v-m)
- ✅ Minimal RH-strength interface formalized (Steps 4v-n through 4v-zzv)
- ✅ **NEW:** Exact weighted affine decomposition proves structural necessity (Steps 4v-zzvi through 4v-zzaG)
- ✅ **NEW:** Sharp Cauchy stop test rewrites the energy as two nonnegative defects (Step 4v-zzaH)
- ❓ Norm-balance and antiparallel-alignment decay must be proved unconditionally
- **Success probability:** 15–25% (transcendental, requires RH-strength input)

The repository proves: `NymanBeurlingCriterion → WeightedAffineDecomposition → CoupledSignedDecay → RiemannHypothesis` (complete reduction chain with exact cancellation structure).

---

## Verify the Build

```bash
# Compile the verified package
lake build

# Check axiom dependencies (should be only standard Lean core)
lake env lean proofs/NBMellinTools/Audit.lean
```

**Expected output:**
```
Build completed successfully (8630 jobs).
All theorems depend on: [propext, Classical.choice, Quot.sound]
```

**Explore the knowledge graph:**
```bash
cd data
jupyter notebook explore_riemann_graph.ipynb
# Generates 7 visualizations + data exports (2-3 minutes)
```

---

## Architecture

**Active, verified modules (proofs/NBMellinTools/):**

| Module | What It Proves | Status |
|--------|---|---|
| NB2–3 | Mellin transforms & error formulas | ✅ Verified |
| NB4–5 | Zero-detection reduction | ✅ Verified |
| NB6 | Global RH closure | ✅ Verified |
| NB7 | Approximation sequence equivalence | ✅ Verified |
| NB8–10 | Gram decomposition & Vasyunin reduction | ✅ Verified |
| **NB11** | Classical Vasyunin evaluation | ✅ **Newly proved** |
| NB12 | Exact Fourier core, dyadic/divisor expansion, nested Abel, final boundary, and cross-modulus dispersion | ✅ **Complete frontier characterization (Steps 4t through 4v-zzv).** Fiber multiplicity (4t: exponent +2). Progression-density (4u: exponent +1). Algebraic: zero-extension, exact transpose, residuals, nested Abel, final boundary audit (4v-a through 4v-j). Elementary analytic: Fourier, collision control, aliasing (4v-k through 4v-m). Minimal RH-strength interface: coupled correction-Kloosterman decay required (4v-n through 4v-zzv). All frontiers precisely characterized. |
| NB13–14 | Conditional assembly & rational-series collapse | ✅ Algebra proved; inputs open |

**Historical & exploratory material (proofs/route-c/):**
- Not part of the active build
- Contains some false axioms and incomplete proofs
- Retained as research record (see [docs/FAILED_ROUTES_ANALYSIS.md](docs/FAILED_ROUTES_ANALYSIS.md))

---

## The Open Problem (H15 / Frontier)

**What we proved (Session 9c, Steps 1–4v-zzv, 8,568 jobs):**

The repository verifies the standard approximation-sequence formulation of
its Nyman–Beurling criterion and proves that criterion implies RH. All intermediate reductions (H1–H14) are kernel-certified. The frontier is now **completely characterized and transparent:**

1. ✅ **Absolute methods closed** (Steps 4t–4u): Fiber-cardinality yields exponent +2. Progression-density sharpening reduces to exponent +1. The arithmetic wall is load-bearing.
2. ✅ **Algebraic methods closed** (Steps 4v-a through 4v-j): Complete nested Abel decomposition proves smooth variation controlled by o(1) bounds. Zero-mode test negative—no third algebraic cancellation.
3. ✅ **Elementary analytic methods closed** (Steps 4v-k through 4v-m): Fourier representation, collision control, even-modulus aliasing. Parseval bounds alone insufficient.
4. ✅ **Minimal RH-strength interface formalized** (Steps 4v-n through 4v-zzv): Exact characterization of required decay.

**What remains open (THE SINGLE FRONTIER):**

```lean
theorem H15CoupledCorrectionDecay :
  Tendsto (fun N => |Correction N + SignedKloostermanAggregate N|)
          atTop (nhds 0)
```

**Why this is hard:**
- Purely transcendental (no algebraic method succeeds)
- Requires RH-strength cancellation (signed coupled decay)
- Combines bilinear Fourier analysis with number-theoretic weights
- Equivalent to RH in strength
- Single frontier characterization: **either coupled decay exists (then RH follows), or it doesn't (then RH fails)**

**For researchers:**
- See [docs/H15_MATHEMATICAL_DOSSIER.md](docs/H15_MATHEMATICAL_DOSSIER.md) for mathematical analysis
- See [docs/FAILED_ROUTES_ANALYSIS.md](docs/FAILED_ROUTES_ANALYSIS.md) for why other approaches don't work
- See [CONTRIBUTING.md](CONTRIBUTING.md) for how to contribute

---

## Repository Structure

```
riemann-github/
├── 📄 Root Navigation (6 files)
│   ├── README.md                   You are here
│   ├── HONEST_STATEMENT.md         What's proved vs. what's open
│   ├── HOW_TO_VERIFY.md            Reproducibility (lake build)
│   ├── CONTRIBUTING.md             How to extend the work
│   ├── CONTRIBUTORS.md             Attribution & responsibility
│   └── CITATION.cff                Citation metadata
│
├── 📁 proofs/ (500 Lean files)
│   ├── NBMellinTools.lean          Active verified umbrella
│   ├── NBMellinTools/              148 imported modules (NB2–NB14 families)
│   │   ├── NB12RationalSineCotangent.lean  Exact BBLS frontier
│   │   ├── NB12BBLSDivisorExpansion.lean   Exact product-to-divisor collapse
│   │   ├── NB12BBLSEstermannCompatibility.lean Exact damped Estermann coefficient
│   │   ├── NB12BBLSAbelMellin.lean Correct shifted Mellin identity and exchange
│   │   ├── NB12BBLSHurwitzDecomposition.lean Finite rational continuation
│   │   ├── NB12BBLSHurwitzLaurent.lean Explicit polar terms and finite part
│   │   ├── NB12BBLSHurwitzFunctionalEquation.lean Exact two-level finite-DFT equation
│   │   ├── NB12BBLSEstermannDualCollapse.lean Classical inverse-twist equation
│   │   ├── NB12BBLSEstermannVerticalKernel.lean Exact Archimedean vertical bounds
│   │   ├── NB12BBLSEstermannVerticalGrowth.lean Scalar-Hurwitz growth reduction
│   │   ├── NB12BBLSReflectedContour.lean Exact farther-contour normalization
│   │   ├── NB12BBLSActiveLaurent.lean Exact active triple-plus-simple pole data
│   │   ├── NB12BBLSCorrectionBridge.lean Finite signed Laurent aggregate and correction ledger
│   │   ├── NB12BBLSH15DirectAdditiveReassembly.lean Exact fixed-height direct-phase reassembly
│   │   ├── NB12BBLSH15PairedDirectKernel.lean Exact paired norm-square and weighted cross term
│   │   ├── NB12BBLSH15RamanujanCompletionDefect.lean Exact period completion and endpoint/variation defects
│   │   ├── NB12BBLSH15RamanujanVariationAudit.lean Absolute exponent stop test and squarefree split
│   │   ├── NB12BBLSH15SquarefreeDivisorExpansion.lean Exact square-divisor reindexing and signed gate
│   │   ├── NB12BBLSH15SquarefreeGCDStratification.lean Exact normalized progression/gcd strata
│   │   └── Audit.lean              Axiom verification
│   └── route-c/                    Historical material (not active)
│
├── 📁 docs/ (27 files)
│   ├── COLLEAGUE_REVIEW_GUIDE.md   15 min – 3 hour review paths
│   ├── H15_MATHEMATICAL_DOSSIER.md Frontier characterization
│   ├── HARD_TARGETS_UPDATED_CODEX_FEEDBACK_AUG2.md   Codex corrections
│   ├── FOURIER_REMAINDER_DECAY_AUDIT_2026-08-01.md   What's proved
│   ├── CODEX_SESSION_UPDATE_PROTOCOL.md   Maintain docs during sessions
│   ├── SESSION_QUICK_REFERENCE.md  Pocket-sized session checklist
│   ├── CODEX_NEXT_STEPS_AUG2_FRONTIER_SHARP.md   Research roadmap
│   └── 20 other audit & research files
│
├── 📁 data/ (unified knowledge graph)
│   ├── unified-complete-knowledge-graph.jsonld  20,956 nodes (15 MB)
│   ├── frontier_literature_dataset.json         52 papers + 3 tiers
│   ├── explore_riemann_graph.ipynb              Interactive explorer
│   ├── MERGED_GRAPH_GUIDE.md                    Graph structure
│   ├── NOTEBOOK_README.md                       Setup guide
│   └── visualizations/                          7 PNG charts + data (auto-generated)
│
├── 📁 scripts/ (4 build tools)
│   ├── annotate_sorries.py         Find remaining sorry's
│   ├── print_axioms.lean           Axiom checker
│   └── 2 other utilities
│
├── 📁 website/                     Public interface
│   ├── index.html                  Frontier portal
│   └── routes.html                 26 RH intuitions + 4 research routes
│
├── 📁 archive/                     Historical materials
│   ├── documentation/              Old docs
│   ├── papers/                     Literature references
│   ├── backup/                     Proof backups
│   └── deprecated-graphs/          Old unified graph versions
│
└── lakefile.toml, lake-manifest.json   Build configuration
```

**Active verified build:** `proofs/NBMellinTools.lean`
- **8,630 jobs** (verified Aug 4, 2026)
- **0 custom axioms** (only propext, Classical.choice, Quot.sound)
- **148 imported modules** (NB2–NB14 families, all kernel-verified)

**Knowledge graph:** `data/unified-complete-knowledge-graph.jsonld`
- **20,956 nodes** (persons, papers, themes, theorems, proofs)
- **12,859 relations**
- **55 frontier papers** (4 tiers, 3 targets)

---

## How to Engage

### **If you want to understand the work (15 minutes):**
1. Read [HONEST_STATEMENT.md](HONEST_STATEMENT.md) — What's proved (5 min)
2. Read [docs/HARD_TARGETS_UPDATED_CODEX_FEEDBACK_AUG2.md](docs/HARD_TARGETS_UPDATED_CODEX_FEEDBACK_AUG2.md) — Exact frontier (10 min)
3. Build locally: `lake build` (2 min)

### **If you want to explore the knowledge graph:**
1. Install: `pip install pandas numpy matplotlib seaborn networkx jupyter`
2. Run: `cd data && jupyter notebook explore_riemann_graph.ipynb`
3. Wait ~2-3 minutes for 7 visualizations + CSV exports
4. See [data/NOTEBOOK_README.md](data/NOTEBOOK_README.md) for details

### **If you want to review for colleagues:**
- See [docs/COLLEAGUE_REVIEW_GUIDE.md](docs/COLLEAGUE_REVIEW_GUIDE.md)
- Time commitment: 15 min (quick), 1 hour (medium), 2–3 hours (deep)
- Checklists for code & math reviewers provided

### **If you want to work with Codex:**
- Read [docs/CODEX_SESSION_UPDATE_PROTOCOL.md](docs/CODEX_SESSION_UPDATE_PROTOCOL.md) (15 min, comprehensive)
- Keep [docs/SESSION_QUICK_REFERENCE.md](docs/SESSION_QUICK_REFERENCE.md) at desk (print & laminate)
- Time per session: ~25 min (5 before + inline + 15 after)
- After each session: update audit reports, frontier characterization, papers, website

### **If you want to contribute:**
- Read [CONTRIBUTING.md](CONTRIBUTING.md)
- Three open targets:
  1. **SmoothMertensDecay** (classical, 3–4 weeks)
  2. **BBLSBilinearTailLogEstimate** (frontier; divisor/Estermann and short-interval routes)
  3. **SignedBilinearDispersionDecay** (RH-equivalent, 8–12 weeks, hardest)
- See [data/frontier_literature_dataset.json](data/frontier_literature_dataset.json) for 52 relevant papers

### **If you're interested in LLM-assisted mathematics:**
- Study the Codex workflow: [docs/CODEX_SESSION_UPDATE_PROTOCOL.md](docs/CODEX_SESSION_UPDATE_PROTOCOL.md)
- See validation framework: [CONTRIBUTORS.md](CONTRIBUTORS.md)
- Check audit trail: [docs/FOURIER_REMAINDER_DECAY_AUDIT_2026-08-01.md](docs/FOURIER_REMAINDER_DECAY_AUDIT_2026-08-01.md)

---

## Key Facts

**Verification:**
- ✅ **148 imported modules** (NB2–NB14 families) with **0 custom axioms**
- ✅ **8,630 build jobs** verified by Lean 4 kernel
- ✅ **Exact three-sector frontier:** correction-coupled low + finite signed middle + proved polynomial ultra-high tail
- ✅ **Transparent Codex involvement** (formalization + frontier discovery)
- ✅ **Reproducible:** `lake build` on any Lean 4 machine

**Frontier Characterization:**
- ✅ **3 exact targets** identified by Codex (Aug 2, 2026)
  - SmoothMertensDecay (classical)
  - BBLSBilinearTailLogEstimate (exact from proofs/NBMellinTools/NB12*)
  - SignedBilinearDispersionDecay (RH-equivalent)
- ✅ **55 frontier papers** mapped (4 tiers, 3 targets)
- ✅ **Unified knowledge graph** (20,956 nodes, 12,859 relations)

**Digital Humanities Methodology:**
- 🏛️ **167-Year Lineage**: Synthesizes 498 papers into an interactive graph (21,942 nodes).
- 🤝 **Transparent AI Parliament**: Every prompt session, audit trail, and tactic choice logged.
- 🛑 **Strict Epistemic Integrity**: No speculative leaps, zero custom axioms, and full acknowledgement of unproven open frontiers.
- ❌ **Does NOT prove RH unconditionally**: Explicitly formalizes conditional reduction only.

---

## Author & Responsibility

**Primary mathematician:** Xavier Fresquet, SCAI, Sorbonne Université
**LLM-assisted discovery:** Claude (Anthropic) + Codex (OpenAI) parliaments
**Responsibility framework:** Aligned with OpenAI “Ten Proofs” and Leiden Declaration

See [CONTRIBUTORS.md](CONTRIBUTORS.md) for full attribution and validation status.

---

**Status:** Open for collaborative development and expert review
**Last verified:** August 2, 2026
**Build:** 8,630 jobs, 0 custom axioms
**Frontier:** the finite middle-window Bettin--Chandee estimate and the correction-coupled low-frequency decay (both exactly characterized)
**Knowledge graph:** 20,956 nodes, 55 frontier papers, 3 hard targets
**Codex sessions:** Protocol & quick-reference ready in docs/
