# Aristotle Task W — Exact Canonical H15SignedSquareDivisorPowerSaving Statement

**Date:** August 8, 2026  
**Objective:** Formalize the unified H15 frontier as a single, canonical Lean definition/theorem  
**Constraints:** No reconstruction; consolidate existing definitions; hard rule enforcement  
**Expected Output:** H15SignedSquareDivisorPowerSaving definition or gap report

---

## Background

Task R proved that three apparent sub-goals collapse to one:
- Coupled variation decay ≡ Signed square-divisor power-saving
- Pointwise residual decay ≡ Signed square-divisor power-saving  
- Log-taper transfer ≡ Signed square-divisor power-saving

Task W formalizes the UNIFIED object: a single definition that unifies all three.

---

## Current State of H15 Definitions

### Existing in Code:
1. **H15CenteredAggregateEstimate** 
   - Location: `proofs/route-c/modules/H15CenteredAggregateEstimate.lean:119`
   - Type: Structure with residual bounds, sawtooth bounds, log-gamma bounds
   - Status: Real object, but may not be the "signed square-divisor" form

2. **h15NormalizedProgressionCoupledVariationBoundaryAggregate**
   - Location: `NB12BBLSH15ActiveIncidence.lean:156–172`
   - Type: Concrete computation (sum over q, d, k)
   - Status: Proved equivalent to signed-square-divisor (Task R)

3. **h15RamanujanSignedSquareDivisorAggregate**
   - Location: Likely exists; Task R references it
   - Type: Should be the Möbius-weighted divisor form
   - Status: Used as RHS of Task R equivalence

### Missing (Possibly):
- A definition explicitly called `H15SignedSquareDivisorPowerSaving` or `H15SignedSquareDivisor`
- Unified statement covering all three forms

---

## Task W: What To Define

**Hard Rule 1:** Before defining anything NEW, locate and quote existing definitions.

**Hard Rule 2:** If three definitions exist separately, propose a unifying type/structure.

**Hard Rule 3:** Do NOT modify existing code; create new canonical definition that references existing ones.

### Primary Goal

Define or formalize:
```lean
-- Option A: Simple conjunction of three equivalent propositions
def H15SignedSquareDivisorPowerSaving : Prop :=
  ∃ C c > 0, ∀ N ≥ 2,
    |∑ (q in B(N,g,Q)), ∑ (d in D(g,U,q)), μ(d) * h15_cross_term(N,g,r,U,Q)| 
      ≤ C * exp(-c * sqrt(log N))

-- Option B: Structure collecting all three forms
structure H15SignedSquareDivisorPowerSaving where
  (rowPointwiseResidualDecay : RiemannHypothesisStrengthDecay ...)
  (coupledVariationBoundaryDecay : RiemannHypothesisStrengthDecay ...)
  (pointwiseLogTaperTransfer : RiemannHypothesisStrengthDecay ...)
  (equivalence : ...)  -- proof that all three are the same problem

-- Option C: Direct formalization
theorem h15SignedSquareDivisorPowerSaving_exact_statement :
  H15CenteredAggregateEstimate ↔ [formal union of three forms]
```

### Sub-Goals (If Primary Blocked)

1. **Locate h15RamanujanSignedSquareDivisorAggregate:**
   - File and line number
   - Type signature
   - Definition (equation or proof)

2. **Compare with H15CenteredAggregateEstimate:**
   - Are they the same object with different names?
   - Quote which components match
   - What's the precise relationship?

3. **Unify the three forms:**
   - Create a single type that encompasses all three formulations
   - Show they are logically equivalent (reference Task R/U)

4. **Name it canonically:**
   - Propose final name: H15SignedSquareDivisorPowerSaving (or alternative)
   - Ensure it's used consistently in all three forms

---

## Deliverables

### If Successful (Canonical Definition Created)
- New file: `proofs/NBMellinTools/NB24H15SignedSquareDivisorCanonical.lean`
- Definition: `H15SignedSquareDivisorPowerSaving` (or agreed-upon name)
- Theorem: `h15SignedSquareDivisor_unified_definition` (zero sorry)
- Equivalences proved to all three forms (reference Tasks R/U/V)
- Axioms: Only propext, Classical.choice, Quot.sound

**Export:** Include in root `NBMellinTools.lean` so it's visible to all downstream code

### If Unsuccessful (Existing Definition Sufficient)
- New file: `H15_CANONICAL_DEFINITION_GAP_REPORT.md`
- Report structure:
  1. Existing definition that serves as canonical (quote location)
  2. Why it unifies all three forms
  3. Recommendation: Use `[name]` as canonical reference going forward
  4. If not yet unified: missing theorem for unification

---

## Hard Rules

❌ **Do NOT:**
- Create a new definition if one already exists
- Invent new concepts
- Skip quoting locations

✅ **DO:**
- Search existing code for `SignedSquareDivisor`, `H15Centered`, `Ramanujan`
- Quote exact file:line for every definition
- Propose a single, clear canonical name
- Prove equivalence to all three forms (or cite Tasks R/U/V)

---

## Estimated Complexity

- **If definition exists:** 1–2 hours (locate, verify, create wrapper)
- **If needs creation:** 2–3 hours (consolidate three forms, prove equivalences)
- **If equivalences already in code:** 1 hour (document and expose)

---

## Success Criteria

✅ **Success:** Single canonical definition with three equivalent formulations, zero sorry  
⚠️ **Partial Success:** Existing definition identified as canonical with clear documentation  
❌ **Failure:** Definitions incompatible (should not happen given Task R)

---

## Research Impact

The canonical definition provides:
1. **Single focal point:** Reference for all future work on H15
2. **Honest statement:** Explicit form of the open frontier problem
3. **Publication basis:** The core object to cite in papers

---

## Notes

- Task R has already proved Form 2 ↔ Form 3
- Task U (if successful) will prove Form 1 ↔ Form 2 ↔ Form 3
- Task V (if successful) will explain why Green–Tao can't close the frontier
- Task W is the synthesis: formalize the unified object

---

*Task W ready for submission*
