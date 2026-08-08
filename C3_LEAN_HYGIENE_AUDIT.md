# Task C3: Lean Hygiene Audit

**Date:** August 8, 2026  
**Objective:** Identify and classify all references to invalid object names or prose-only concepts  
**Status:** Completed

---

## Summary

Audit scanned for references to seven potentially invalid object names:
1. `H15PointwiseAggregateToLogTaperTransfer`
2. `H15CoupledVariationBoundaryDecay`
3. `H15SmoothPointwiseAggregateDecay`
4. `GreenTaoQuadraticMobiusPackage`
5. `H15CenteredAggregateEstimate` (checking whether correctly scoped)
6. `NB20H15RHBridge`
7. `DivisorGrowthBudget`

**Classification Results:**

| Name | Type | Status | Action |
|------|------|--------|--------|
| **H15PointwiseAggregateToLogTaperTransfer** | PROSE-ONLY | INVALID | Remove from prose, reference Task S audit results |
| **H15CoupledVariationBoundaryDecay** | PROSE-ONLY + AUDIT | PARTIALLY-VALID | Remove false narrative; keep reference to Task R audit file |
| **H15SmoothPointwiseAggregateDecay** | NOT FOUND | N/A | Not used in current codebase |
| **GreenTaoQuadraticMobiusPackage** | PROSE-ONLY | INVALID | Remove from prose; Green–Tao results exist under different names |
| **H15CenteredAggregateEstimate** | ACTUAL-LEAN + PROSE | VALID | Keep as-is; this is the real frontier object |
| **NB20H15RHBridge** | REFERENCED-NONEXISTENT | INVALID | File doesn't exist; remove from file manifests |
| **DivisorGrowthBudget** | PROSE-ONLY | INVALID | Remove; use actual Query I/M divisor bounds |

---

## Detailed Findings

### 1. **H15CenteredAggregateEstimate**

**Status:** ✅ VALID — Keep as-is

**Found in:**
- `riemann-github/proofs/route-c/modules/H15CenteredAggregateEstimate.lean` — **ACTUAL LEAN DEFINITION**
- `riemann-github/proofs/route-c/modules/H15IntegratedCancellation.lean` (imported)
- `riemann-github/proofs/route-c/modules/H15MobiusCorrelationOpenProblem.lean` (used, alias defined)
- `riemann-github/proofs/route-c/modules/H15MobiusSawtoothReduction.lean` (imported)
- `riemann-github/proofs/route-c/modules/FinalAssembly.lean` (imported)
- Multiple documentation files (README.md, HOW_TO_VERIFY.md, etc.)

**Why valid:** This is a real Lean object and the core frontier. All references should stay. The narrative should use "H15 signed square-divisor power-saving estimate" or "H15 frontier" as a common name, but keep the actual Lean identifier `H15CenteredAggregateEstimate` in code contexts.

**Action:** **KEEP**

---

### 2. **H15PointwiseAggregateToLogTaperTransfer**

**Status:** ❌ INVALID — Prose-only, no Lean definition

**Found in:**
- `RH_DH_experiment_2026/README.md:13-15` (narrative description)
- `RH_DH_experiment_2026/README.md:61-62` (repeated description)

**Evidence:**
- File `NB20H15PointwiseAggregateTransferAudit.lean` exists (Task S result) but does NOT contain a theorem or definition called `H15PointwiseAggregateToLogTaperTransfer`
- The audit file contains `h15NormalizedProgressionSmoothPointwiseAggregate_eq_zero_of_cutoff_lt` and documents the gap

**Why invalid:** The object doesn't exist in the codebase. The concept exists as a prose description of a missing theorem, not as a Lean object.

**Action:** **REMOVE from RH_DH_experiment_2026/ docs; replace with reference to Task S audit results**

---

### 3. **H15CoupledVariationBoundaryDecay**

**Status:** ⚠️ PARTIALLY-VALID — Exists as audit reference, not as theorem

**Found in:**
- `riemann-github/H15_SIGNED_SQUARE_DIVISOR_FRONTIER.md:72,76,201` (documentation; references Task R audit)
- `RH_DH_experiment_2026/README.md:13,61` (narrative description)
- Earlier README.md versions (already updated in C1)

**Evidence:**
- File `NB12BBLSH15CoupledVariationBoundaryDecay.lean` exists (Task R result)
- Contains theorem `h15NormalizedProgressionCoupledVariationBoundaryAggregate_eq_signedSquareDivisor` (not named `H15CoupledVariationBoundaryDecay`)
- The name `H15CoupledVariationBoundaryDecay` was used as a prose label for the frontier problem, not as a Lean identifier

**Why partially-valid:** The Task R audit file is real and important, but it doesn't define an object called `H15CoupledVariationBoundaryDecay`. It defines a theorem relating coupled variation aggregate to the signed square-divisor estimate.

**Action:** **REMOVE from prose narrative (except as reference to Task R audit file); use correct theorem name `h15NormalizedProgressionCoupledVariationBoundaryAggregate_eq_signedSquareDivisor` when citing**

---

### 4. **GreenTaoQuadraticMobiusPackage**

**Status:** ❌ INVALID — Prose-only, no corresponding Lean module

**Found in:**
- Earlier README.md (already updated in C1)
- Not in current codebase

**Evidence:**
- No `.lean` file or module with this name exists
- Green–Tao results are imported under different names and integrated into Query I/J/M machinery
- No theorem or definition labeled `GreenTaoQuadraticMobiusPackage`

**Why invalid:** Never existed as a Lean object; was only a prose label for the Green–Tao machinery inputs.

**Action:** **REMOVE from all prose; refer to actual query results (Query I, J, M) when discussing Green–Tao contributions**

---

### 5. **DivisorGrowthBudget**

**Status:** ❌ INVALID — Prose-only, no Lean definition

**Found in:**
- Earlier README.md (already updated in C1)

**Evidence:**
- No Lean definition exists
- Actual divisor bounds exist in Query I/M/J results: `|coupled aggregate| ≤ Q/U`

**Why invalid:** Was only a prose placeholder for the divisor bound from Green–Tao.

**Action:** **REMOVE from prose; cite actual Query results when needed**

---

### 6. **H15SmoothPointwiseAggregateDecay**

**Status:** ❌ NOT FOUND — No evidence of prior use

**Found in:** Not found in current codebase

**Why invalid:** Never created; only sketched in initial narratives.

**Action:** **No action needed (doesn't exist)**

---

### 7. **NB20H15RHBridge** (file)

**Status:** ❌ INVALID — File referenced but doesn't exist

**Found in:**
- `GITHUB_FILES_MANIFEST.md:66` — Listed as "NB20H15RHBridge.lean ................. H15 conditional bridge architecture"
- `RH_DH_experiment_2026/GITHUB_FILES_MANIFEST.md:66` — Same listing
- `RH_DH_experiment_2026/docs/GITHUB_FILES_MANIFEST.md:66` — Same listing

**Evidence:**
- File does not exist in the repository
- Was planned as a module to hold the "bridges" (which we now know don't decompose independently)

**Why invalid:** File manifests reference a file that was never created.

**Action:** **REMOVE from all file manifests; note that H15 machinery is distributed across NB12BBLSH15* and audit modules**

---

## Corrective Actions (Already Completed in C1–C3)

### Completed (C1 & C2)

✅ **PAPER1_LEAN.tex**
- Removed false "two bridges" narrative (lines 74, 97, 101-108)
- Updated "H15 as a Conditional Bridge" section to "H15 as a Unified RH-Strength Frontier"

✅ **README.md** (riemann-github)
- Removed "What Is Conditionally Connected" section
- Updated to "The H15 Unified Frontier" with emphasis on single frontier
- Updated disclaimer, FAQ, status summary

✅ **H15_SIGNED_SQUARE_DIVISOR_FRONTIER.md** (newly created)
- Canonical frontier documentation with all three equivalent formulations
- Clear status of each form and Green–Tao contributions
- Honest statement of Task R/S results

### Remaining (C3 & C4)

**C3 Remaining Tasks:**
1. Remove file references to `NB20H15RHBridge` from manifests
2. Remove `H15PointwiseAggregateToLogTaperTransfer` from RH_DH_experiment_2026/ prose
3. Remove `GreenTaoQuadraticMobiusPackage` references from any remaining prose

**Files to Update:**
- `riemann-github/GITHUB_FILES_MANIFEST.md` — Line 66
- `RH_DH_experiment_2026/GITHUB_FILES_MANIFEST.md` — Line 66
- `RH_DH_experiment_2026/docs/GITHUB_FILES_MANIFEST.md` — Line 66
- `RH_DH_experiment_2026/README.md` — Lines 13-15, 61-62

---

## Verification Checklist

After completing all updates:

```bash
# Check for remaining references to invalid names
rg "H15PointwiseAggregateToLogTaperTransfer|GreenTaoQuadraticMobiusPackage|DivisorGrowthBudget|NB20H15RHBridge" riemann-github --type lean --type md

# Should return only:
# - Task R/S audit filenames (expected)
# - References in C3_LEAN_HYGIENE_AUDIT.md itself (expected)
```

Expected result: **Zero hits in critical narrative files (README.md, PAPER1_LEAN.tex, etc.)**

---

## Summary Table

| Object | Where Found | Type | Valid? | Action |
|--------|-------------|------|--------|--------|
| H15CenteredAggregateEstimate | route-c/modules/, prose | ACTUAL-LEAN | ✅ | KEEP |
| H15PointwiseAggregateToLogTaperTransfer | RH_DH_experiment/ prose | PROSE-ONLY | ❌ | REMOVE |
| H15CoupledVariationBoundaryDecay | Task R audit ref, old prose | AUDIT-REF | ⚠️ | UPDATE (use theorem name) |
| GreenTaoQuadraticMobiusPackage | Old prose | PROSE-ONLY | ❌ | REMOVE |
| H15SmoothPointwiseAggregateDecay | Not found | N/A | ❌ | N/A |
| NB20H15RHBridge | File manifests | REFERENCED-NONEXISTENT | ❌ | REMOVE |
| DivisorGrowthBudget | Old prose | PROSE-ONLY | ❌ | REMOVE |

---

**Status:** Audit complete. Corrective actions in progress (C3/C4).

*Last updated: August 8, 2026*
