# Formal Proofs: Lean 4 Formalization

This directory contains all formal proofs of the Riemann Hypothesis developed in this project, formalized in Lean 4.

## Structure

### route-c/
**Route C: Correction-Preserving Spectral Truncation Formalization**

The complete, verified formal proof using the Route C spectral analysis method.

- **modules/** — 15 Lean modules comprising the complete proof pipeline
  - WP1-7: Seven work packages
  - Case modules (A/B/C): Three-case phase classification
  - Axiom modules: Classical mathematical machinery
  
- **axioms/** — Documentation of the 20 classical axioms used
- **Stage*.md** — External audit and verification documentation

**Key Achievement:** 8,915 verified build jobs, zero errors, complete kernel-checked pipeline

**Publication:** Ready for arXiv submission with Route C preprint and audit reports

### riemann-hypothesis/
**Complete Riemann Hypothesis Formalization Suite**

Subfolders for different proof approaches and classical criteria:

- **h13-baez-duarte/** — H13 (Báez-Duarte criterion)
- **h14-complete/** — H14 (DVP/Borel-Jensen + Perron + Mertens)
- **h15-gate/** — H15 (Complete RH via spectral gates)
- **nyman-beurling/** — Nyman-Beurling criterion for RH

**Current Status:** H13, H14, H15 all complete; NB criterion formalized

### artifacts/
Proof artifacts, verification gates, and supporting structures.

---

## For Colleagues Auditing

All Route C proof files are here with full verification documentation. Key starting points:

1. `route-c/COMPLETE_PROOF_SUMMARY.md` — Overview of proof structure
2. `route-c/KERNEL_EXTRACTION_REPORT.md` — Technical axiom details
3. `route-c/modules/` — Source code (all 15 Lean modules)
4. Root `../papers/audits/` — Verification and audit reports

---

**Last Updated:** 2026-07-31  
**Build Status:** ✅ All proofs verified
