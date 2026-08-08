# Missing Files Audit — Aristotle Downloads vs. Current Repository

**Date:** August 8, 2026  
**Status:** Complete inventory

---

## Summary

**Total files downloaded:** 230+ Lean files + 20+ markdown reports  
**Files present in downloads:** ✅ ALL  
**Files missing from current riemann-github:** See below

---

## What Was Downloaded (All Present ✅)

### Task R & S Audit Files
```
riemann-github_aristotle/proofs/NBMellinTools/
├── NB12BBLSH15CoupledVariationBoundaryDecay.lean ✅ (Task R audit)
├── NB20H15PointwiseAggregateTransferAudit.lean ✅ (Task S audit)
└── [150+ other NB12/NB15/NB19/NB20 modules] ✅
```

**Reports:**
- COUPLED_VARIATION_GAP_REPORT.md ✅
- TRANSFER_GAP_REPORT.md ✅

### Query 6 (Beurling)
```
project_aristotle/proofs/Beurling/
├── Basic.lean ✅
├── DiscExtension.lean ✅
├── FourierUniqueness.lean ✅
├── Main.lean ✅
└── README.md ✅
```

### Query 7 (Inner-Outer Hardy Space)
```
project_aristotle/proofs/RiemannHypothesis/HardySpace/
├── BlaschkeFactor.lean ✅
├── BlaschkeProduct.lean ✅
├── BlaschkeZeros.lean ✅
├── HardyDisc.lean ✅
├── InnerOuterDisc.lean ✅
├── InnerOuterHalfPlane.lean ✅
└── README.md ✅
```

---

## Files Missing From Current riemann-github Repository

### Category 1: New Audit Modules (Need to be Added)

**From Task R & S:**
```
proofs/NBMellinTools/
├── NB12BBLSH15CoupledVariationBoundaryDecay.lean (NEW, from Aristotle)
└── NB20H15PointwiseAggregateTransferAudit.lean (NEW, from Aristotle)
```

**Status:** Both exist in download, not yet in current riemann-github  
**Action:** COPY to riemann-github/proofs/NBMellinTools/

---

### Category 2: Beurling Module (Need to be Added)

**Current riemann-github:**
```
riemann-github/proofs/
├── Beurling.lean (root import, exists)
└── Beurling/
    ├── Basic.lean
    ├── DiscExtension.lean
    ├── FourierUniqueness.lean
    └── Main.lean
```

**Status:** Files exist in current repo  
**Verify:** Check if they match the Aristotle versions (may be outdated)

---

### Category 3: Hardy Space Inner-Outer (New — Not in Current Repo)

**Should be in:**
```
proofs/RiemannHypothesis/HardySpace/
├── BlaschkeFactor.lean (MISSING — from Aristotle)
├── BlaschkeProduct.lean (MISSING — from Aristotle)
├── BlaschkeZeros.lean (MISSING — from Aristotle)
├── HardyDisc.lean (MISSING — from Aristotle)
├── InnerOuterDisc.lean (MISSING — from Aristotle)
├── InnerOuterHalfPlane.lean (MISSING — from Aristotle)
└── README.md (MISSING — from Aristotle)
```

**Status:** These 6 modules + README are completely new from Query 7  
**Action:** CREATE `proofs/RiemannHypothesis/HardySpace/` directory and COPY all 7 files

---

### Category 4: Pre-Existing Files Not in Download (But in riemann-github)

These exist in the current repo but NOT in Aristotle downloads (as expected):

```
riemann-github/proofs/
├── NBMellinTools.lean (root import)
├── RiemannHypothesis.lean (root import)
├── route-c/ (all 360+ files)
├── riemann-hypothesis/
├── artifacts/
└── [other existing modules]
```

**Status:** These are pre-existing, not from Aristotle  
**Action:** NO ACTION (keep as-is)

---

## Files Needing Verification (May Need Updates)

### Beurling Module
Current riemann-github may have stale versions. Need to check:
```bash
diff -u riemann-github/proofs/Beurling/Basic.lean \
         aristotle_downloads/project_aristotle/proofs/Beurling/Basic.lean
```

If different, the Aristotle version is more recent and should replace.

---

## Gap Reports That Should Exist

**Already delivered in downloads:**
- COUPLED_VARIATION_GAP_REPORT.md ✅ (in riemann-github_aristotle/)
- TRANSFER_GAP_REPORT.md ✅ (in riemann-github_aristotle/)

**Should be copied to riemann-github root:**
```
riemann-github/
├── COUPLED_VARIATION_GAP_REPORT.md (from download)
└── TRANSFER_GAP_REPORT.md (from download)
```

---

## Integration Checklist

### Must Add (New Files from Aristotle)
- [ ] Copy `NB12BBLSH15CoupledVariationBoundaryDecay.lean` (Task R)
- [ ] Copy `NB20H15PointwiseAggregateTransferAudit.lean` (Task S)
- [ ] Create directory `proofs/RiemannHypothesis/HardySpace/`
- [ ] Copy all 6 Hardy space modules (Query 7)
- [ ] Copy HardySpace/README.md
- [ ] Copy COUPLED_VARIATION_GAP_REPORT.md to root
- [ ] Copy TRANSFER_GAP_REPORT.md to root

### Must Verify (Existing Files)
- [ ] Compare Beurling files with Aristotle versions (use diff)
- [ ] If different, replace with Aristotle versions
- [ ] Check if Beurling/README.md needs update

### Must Check (Build/Imports)
- [ ] Verify lakefile.toml includes new modules
- [ ] Check import statements in root modules
- [ ] Run `lake build` to confirm everything compiles
- [ ] Verify no new sorry/admit introduced

---

## File Locations for Integration

### Source (Current Location)
```
/Users/xavierfresquet/Documents/Musicologie/CAPTAL-LAB/4-MISC/math/riemann/riemann-github/aristotle_downloads/
├── riemann-github_aristotle/proofs/NBMellinTools/NB12BBLSH15CoupledVariationBoundaryDecay.lean
├── riemann-github_aristotle/proofs/NBMellinTools/NB20H15PointwiseAggregateTransferAudit.lean
├── riemann-github_aristotle/COUPLED_VARIATION_GAP_REPORT.md
├── riemann-github_aristotle/TRANSFER_GAP_REPORT.md
├── project_aristotle/proofs/Beurling/*.lean
└── project_aristotle/proofs/RiemannHypothesis/HardySpace/*.lean
```

### Destination (Target riemann-github)
```
/Users/xavierfresquet/Documents/Musicologie/CAPTAL-LAB/4-MISC/math/riemann/riemann-github/
├── proofs/NBMellinTools/NB12BBLSH15CoupledVariationBoundaryDecay.lean
├── proofs/NBMellinTools/NB20H15PointwiseAggregateTransferAudit.lean
├── proofs/RiemannHypothesis/HardySpace/[6 files + README]
├── COUPLED_VARIATION_GAP_REPORT.md
└── TRANSFER_GAP_REPORT.md
```

---

## Summary for User

**What needs to be added to riemann-github:**

1. **2 new audit modules** (Task R & S)
   - `NB12BBLSH15CoupledVariationBoundaryDecay.lean`
   - `NB20H15PointwiseAggregateTransferAudit.lean`

2. **6 new Hardy space modules** (Query 7 Inner-Outer)
   - `BlaschkeFactor.lean`
   - `BlaschkeProduct.lean`
   - `BlaschkeZeros.lean`
   - `HardyDisc.lean`
   - `InnerOuterDisc.lean`
   - `InnerOuterHalfPlane.lean`

3. **2 gap report documents**
   - `COUPLED_VARIATION_GAP_REPORT.md`
   - `TRANSFER_GAP_REPORT.md`

4. **1 Hardy space README**
   - `proofs/RiemannHypothesis/HardySpace/README.md`

5. **Verify/update Beurling module** (if Aristotle version is different)

---

**Total new files to integrate:** ~12 files (8 Lean + 4 docs)

---

*Prepared: August 8, 2026*  
*Ready for integration*
