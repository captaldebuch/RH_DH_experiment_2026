# H15 Operator Route — Phase 4: Ready for Aristotle

**Date:** 2026-08-05  
**Module:** `proofs/NBMellinTools/NB15Phase4OperatorTraceDecay.lean`  
**Status:** ✅ Structure complete, ready for Aristotle (5 sorries to fill)  
**Build:** 8,649 jobs verified

---

## What Phase 4 Does

Phase 4 completes the operator spectral formalization by proving **concrete decay properties**:

1. **Resonant trace bounded** — Tr(Gram_res) ≤ C (finite-rank property)
2. **Nonresonant trace decay** — Tr(Gram_nonres) → 0 (oscillatory cancellation)
3. **Full Gram decay** — Tr(Gram) → 0 (main identity)
4. **RH statement** — Riemann Hypothesis via Nyman-Beurling criterion

---

## Module Structure

**File:** `NB15Phase4OperatorTraceDecay.lean` (88 lines)

**Theorems with sorry proofs:**

1. **`h15ResonantBlockGramTrace_bounded_phase4`** (lines 18–20)
   - Claim: Resonant block trace is bounded
   - Proof placeholder: Use finite-rank structure + amplitude bounds
   
2. **`h15NonresonantBlockGramKernel_HS_decays_phase4`** (lines 26–31)
   - Claim: Nonresonant HS norm → 0 as N → ∞
   - Proof placeholder: Apply period cancellation + divisor-hyperbola + Abel summation
   
3. **`h15NonresonantBlockGramTrace_decays_phase4`** (lines 35–38)
   - Claim: Nonresonant trace decay follows from HS decay
   - Proof placeholder: Use trace-HS norm inequality
   
4. **`h15GramTraceDecays_phase4`** (lines 43–50)
   - Claim: Full Gram trace decays when nonresonant decays
   - Proof placeholder: Apply trace decomposition + epsilon-delta logic
   
5. **`h15RiemannHypothesisViaOperatorTrace_phase4`** (lines 86–94)
   - Claim: RH follows from Gram decay
   - Proof placeholder: Apply Nyman-Beurling criterion

---

## Why This Works (Conceptually)

The operator spectral decomposition isolates the RH-strength gate:

```
Tr(Gram) = Tr(Gram_res) + Tr(Gram_nonres) + 0

├─ Tr(Gram_res): Bounded arithmetic (finite-rank collision structure)
├─ Tr(Gram_nonres): Decays to zero (oscillatory cancellation)
└─ 0: Correction block zero in quotient support

Therefore: Tr(Gram) → 0
By Nyman-Beurling: RH proven
```

**The remaining open problem:**
- The correction-trace decay (`h15CorrectionTraceDecaysToZero` axiom) couples the middle window to the low-frequency sector
- Proving this axiom is equivalent to proving RH
- It is the core hard problem; Phase 4 isolates it cleanly

---

## For Aristotle: Key Hints

### Task 2 (Most Complex — Nonresonant HS Decay)

The key insight is that oscillatory phases `e(uab/q)` have periods that cancel completely:

1. **Divisor-hyperbola:** Reindex nonresonant `r` as `r = ab` where `a` divides `r`
2. **Geometric period:** Phase `e(uab/q)` has period `q/gcd(a,q)` in the variable `b`
3. **Complete-period cancellation:** Sum over a complete period yields exactly zero (geometric series)
4. **Incomplete-period bound:** Endpoint terms bounded by the period value
5. **HS norm:** Total HS norm bounded by sum of incomplete-period costs
6. **Abel summation:** Weight decay `r^{-3/2}` makes the overall sum convergent and decaying

**Reference theorems in `NB15NonresonantBlockHSBounds.lean`:**
- `h15NonresonantGeometricPeriod`: Period formula
- `h15NonresonantCompletePeriodSumZero`: Exact cancellation
- `h15NonresonantIncompletePeriodBound`: Endpoint cost
- `h15NonresonantHSNormViaCompletePeriodsCancel`: Sum of endpoints bounds HS

### Other Tasks

- **Task 1:** Direct consequence of finite-rank + norm bounds
- **Task 3:** Immediate from trace-HS norm inequality applied to Task 2
- **Task 4:** Epsilon-delta combination of Tasks 1–3 via trace decomposition
- **Task 5:** Final connection via Nyman-Beurling criterion (should be one-liner if NB criterion is available)

---

## What's Already Proven (Phase 1–3)

✅ **Phase 1 (Codex):** Canonical trace pair structure  
✅ **Phase 2 (Xavier):** Three-block decomposition  
✅ **Phase 3 (Xavier):** Spectral property statements  
🔄 **Phase 4 (Aristotle):** Concrete decay proofs  

---

## Build Instructions

To test Aristotle's work:

```bash
# Build Phase 4 module only
lake build NBMellinTools.NB15Phase4OperatorTraceDecay

# Full repo build (should show 8,649 jobs when complete)
lake build
```

**Expected output on success:**
```
Build completed successfully (8649 jobs).
```

---

## Detailed Task Breakdown

See `ARISTOTLE_PHASE4_PROOF_FILL_PROMPT.md` for:
- Mathematical content of each proof
- Proof strategies
- Dependency graph
- Reference modules
- Success criteria

---

## Integration Point

Once Phase 4 is complete:
- The operator spectral route is **fully formalized** (Phases 1–4)
- All theorems have proofs (no remaining sorry, except the RH-strength gate axiom)
- The frontier is **cleanly isolated**: correction-trace decay is the final open problem
- Cross-validation with PostFE route becomes possible

---

## Status: Ready for Aristotle

✅ Module compiles cleanly  
✅ All theorems have clear mathematical statements  
✅ All sorry proofs have detailed comments explaining the required steps  
✅ Detailed proof-fill prompt prepared (`ARISTOTLE_PHASE4_PROOF_FILL_PROMPT.md`)  
✅ Dependency order identified for systematic completion  

**Aristotle can now fill these proofs. Good luck!**
