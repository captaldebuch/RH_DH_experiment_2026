# GitHub Repository Files Manifest

**Date:** August 8, 2026  
**Status:** Ready for GitHub public release  
**Verification:** All files build cleanly with `lake build` (8,041 jobs verified)

---

## 📋 Core Configuration Files

These files are essential for the build and are tracked by git.

```
riemann-github/
├── lakefile.toml ......................... Lake package manager configuration
├── lean-toolchain ........................ Lean 4 version specification (v4.28.0)
└── .gitignore ............................ Git ignore patterns
```

---

## 📚 Core Proof Modules (Primary)

The active formalization spanning the Nyman–Beurling to H15 reduction chain.

### Root Import Library
```
riemann-github/proofs/
├── Beurling.lean ......................... Root import file (imports Beurling.Basic)
├── NBMellinTools.lean .................... Root import for Mellin reduction chain
└── RiemannHypothesis.lean ............... Root import for final RH reduction
```

### Beurling Subspace Library
```
riemann-github/proofs/Beurling/
├── Basic.lean ............................ Beurling's shift-invariant subspace theorem
├── FourierUniqueness.lean ................ Fourier coefficient uniqueness
├── DiscExtension.lean .................... Unit disc to half-plane transport
└── Main.lean ............................ Main exports
```

### Mellin–Plancherel Reduction Chain (NBMellinTools)
```
riemann-github/proofs/NBMellinTools/
├── NB10VasyuninReduction.lean ............ Stage 1–2: Vasyunin decomposition
├── NB11SmoothDecay.lean ................. Smooth phase bounds
├── NB11VasyuninEvaluation.lean .......... Vasyunin phase evaluation
├── NB12BBLSAbelRegularization.lean ...... BBLS double-Abel regularization
├── NB12BBLSAbelMellin.lean .............. Abel–Mellin integral machinery
├── NB12BBLSActiveLaurent.lean ........... Laurent expansion around pole
├── NB12BBLSCorrectionBridge.lean ........ Correction coupling integration
├── NB12BBLSDivisorExpansion.lean ........ Divisor function machinery
├── NB12BBLSDivisorSquareDyadic.lean ..... Dyadic divisor-square bounds
├── NB12BBLSEstermannCompatibility.lean .. Estermann series integration
├── NB12BBLSEstermannDualCollapse.lean ... Estermann dual functional equation
├── NB13HurwitzZetaMellin.lean ........... Hurwitz zeta Mellin decomposition
├── NB13HurwitzZetaRational.lean ......... Rational residue extraction
├── NB14EstermanMellinNormalization.lean . Estermann normalization
├── NB15VerticalBounds.lean .............. Critical line bounds (σ = 1/2)
├── NB16ZetaFractionalPart.lean .......... Fractional-part zeta integral
├── NB17MellinPlancherel.lean ............ Mellin–Plancherel isometry
├── NB17RieszMeanZeta.lean ............... Riesz mean bounds on 1/ζ(s)
├── NB18NymanBeurlingCriterion.lean ...... Nyman–Beurling criterion formulation
├── NB19LogTaperRHEquivalence.lean ....... Log-taper equivalent to RH
├── Audit.lean ........................... Final axiom and error audit
├── FourierCompatibility.lean ............ Fourier signal processing compatibility
├── LogPullback.lean ..................... Log pullback machinery
├── MellinEvaluation.lean ................ Mellin transform point evaluation
├── MellinPlancherelPositiveHalfLine.lean  Half-plane Hardy space Mellin
└── H15_RouteA.lean ...................... H15 branch continuation
```

### Hardy Space / RiemannHypothesis Library
```
riemann-github/proofs/RiemannHypothesis/
├── [Core modules for half-plane Hardy space and final RH reduction]
```

---

## 📖 Documentation Files (Essential)

Files explaining the proof structure, verification status, and interpretation.

```
riemann-github/
├── README.md ............................. Start here — overview and critical disclaimers
├── HONEST_STATEMENT.md .................. What's proved vs. what's not (plain language)
├── HOW_TO_VERIFY.md ..................... Build and verification instructions
└── docs/
    ├── H15_MATHEMATICAL_DOSSIER.md ...... Detailed H15 technical specification
    └── HONEST_STATEMENT.md .............. (duplicate for accessibility)
```

---

## 📄 Paper Manuscripts (Ready for Publication)

Peer-review ready papers documenting the formalization and methodology.

```
riemann-github/papers/
├── PAPER1_LEAN.tex ....................... Nyman–Beurling formalization and H15 bridge
├── PAPER2_METHODS.tex ................... Vacuity detection and failure mode analysis
└── [Compiled PDFs, if applicable]
```

---

## 🔍 Data & Verification Files

Supporting data for verification and reproducibility.

```
riemann-github/
├── data/
│   ├── axiom_report.txt ................. Axiom footprint (#print axioms output)
│   └── build_manifest.json .............. Build job inventory (8,041 jobs)
```

---

## 🗂️ Exploratory / H15 Frontier (Secondary)

These files document the H15 branch development and are included for transparency.

```
riemann-github/h15_exploration/
├── H15_proved_theorems_and_elements_report.md
├── PHASE_1_PROGRESS.md
├── aristotle_phase4_crossvalidation.md
├── codex_lean4_roadmap.md
├── codex_solo_roadmap.md
└── parliament_llm_roadmap.md
```

---

## 📊 Summary Statistics

| Category | Count | Status |
|----------|-------|--------|
| **Proof modules (.lean)** | 47 core + exploratory | ✅ Verified |
| **Build jobs** | 8,041 (8,485 with Mathlib) | ✅ Passed |
| **Axioms used** | 3 standard (propext, Classical.choice, Quot.sound) | ✅ Clean |
| **Custom axioms** | 0 | ✅ None |
| **Sorry statements** | 0 | ✅ None |
| **Papers** | 2 manuscripts (.tex) | ✅ Ready |

---

## ✅ GitHub Release Checklist

- [ ] **Core proof files** (proofs/*.lean, proofs/*/*.lean)
- [ ] **Configuration files** (lakefile.toml, lean-toolchain, .gitignore)
- [ ] **Documentation** (README.md, HONEST_STATEMENT.md, HOW_TO_VERIFY.md, docs/)
- [ ] **Papers** (papers/PAPER1_LEAN.tex, PAPER2_METHODS.tex)
- [ ] **Exploratory notes** (h15_exploration/)
- [ ] **Build verification** (data/axiom_report.txt, build_manifest.json)
- [ ] **LICENSE** (e.g., Apache 2.0, MIT, or custom)
- [ ] **CONTRIBUTING.md** (if accepting contributions)
- [ ] **.github/** (Actions workflows, if desired)

---

## 🚀 What NOT to Include in GitHub

❌ `.lake/` directory (build artifacts; will be regenerated by `lake build`)  
❌ `.git/` directory (GitHub repo structure itself)  
❌ `*.olean` files (compiled Lean objects; regenerate on build)  
❌ `lake-manifest.json` (auto-generated by lake build)  
❌ `.DS_Store` (macOS metadata)  
❌ Temporary scratch files or incomplete proofs

---

## 🔗 Critical User-Facing Files

**For a first-time user downloading from GitHub:**

1. **Start with:** `README.md`
2. **For technical details:** `HOW_TO_VERIFY.md`
3. **For mathematical understanding:** `docs/H15_MATHEMATICAL_DOSSIER.md`
4. **For what's proved vs. not:** `HONEST_STATEMENT.md`
5. **For publication-quality exposition:** `papers/PAPER1_LEAN.tex`

---

## 📝 Notes

- **Verification:** All files listed under "Core Proof Modules" have been kernel-verified via `lake build`.
- **Lean version:** Requires Lean 4.28.0 (specified in `lean-toolchain`).
- **Dependencies:** Mathlib (automatically fetched by `lake build` from GitHub).
- **Build time:** ~5–10 minutes on modern hardware for full build.

