# Aristotle Task U — Verify Equivalence of Three H15 Formulations

**Date:** August 8, 2026  
**Objective:** Formally verify that three mathematical formulations of the H15 frontier are logically equivalent  
**Constraints:** No reconstruction; use exact definitions from code; hard rule enforcement  
**Expected Output:** One equivalence theorem or gap report naming missing bridges

---

## Background

Task R proved:
```
h15NormalizedProgressionCoupledVariationBoundaryAggregate_eq_signedSquareDivisor :
  H15CoupledVariationBoundaryDecay ↔ H15SignedSquareDivisorPowerSaving
```

This unified the frontier from "two independent problems" to one. Task U formalizes that ALL THREE forms are equivalent.

---

## The Three Forms

### Form 1: Row-to-Pointwise Residual Decay
**Mathematical statement:**
Decay of the residual after splitting into smooth and endpoint components:
$$\text{residual} = \text{row aggregate} - \text{pointwise aggregate}$$

**Lean location:** `NB12BBLSH15ActiveIncidence.lean:273–293` (pointwise aggregate definition)

**Definition name:** `h15NormalizedProgressionSmoothPointwiseAggregate`

**Decay requirement:** Subexponential (RH-strength)

### Form 2: Coupled Variation / Boundary Aggregate Decay
**Mathematical statement:**
Decay of the normalized superperiod completion (variation + boundary terms):
$$\text{coupled} = h15NormalizedProgressionCoupledVariationBoundaryAggregate$$

**Lean location:** `NB12BBLSH15ActiveIncidence.lean:156–172`

**Already proved equivalent to Form 3 by Task R:**
```
h15NormalizedProgressionCoupledVariationBoundaryAggregate_eq_signedSquareDivisor
```

### Form 3: Pointwise Aggregate to Log-Taper Energy Transfer
**Mathematical statement:**
Transfer from H15 dyadic blocks to certified Nyman–Beurling log-taper energy:
$$h15NormalizedProgressionSmoothPointwiseAggregate \rightarrow \text{NB8.logTaperL2Error}$$

**Lean location:** `NB8LogTaperTarget.lean:49–54` (logTaperL2Error, LogTaperL2Decay)

**Definition name:** `NB8.logTaperL2Error`

**Status:** No direct theorem exists; Task S proved this is vacuous without schedule constraint

---

## Task U: What To Prove

**Hard Rule 1:** Quote exact file paths and line numbers when referencing any definition.

**Hard Rule 2:** Use only existing definitions. Do NOT reconstruct or proxy-invent missing pieces.

**Hard Rule 3:** If equivalence cannot be established, provide gap report naming the exact missing theorem and its type signature.

### Primary Goal

Prove or disprove:
```lean
theorem h15_frontier_equivalence_three_forms :
  (∃ C c > 0, ∀ N ≥ 2,
    |h15NormalizedProgressionSmoothPointwiseAggregate N g r U Q| ≤ C * exp(-c * sqrt(log N)))  -- Form 1
  ↔
  (∃ C c > 0, ∀ N ≥ 2,
    |h15NormalizedProgressionCoupledVariationBoundaryAggregate N g r U Q| ≤ C * exp(-c * sqrt(log N)))  -- Form 2
  ↔
  (∃ C c > 0, ∀ N ≥ 2,
    |h15NormalizedProgressionSmoothPointwiseAggregate N g r U Q| ≤ C * exp(-c * sqrt(log N)))  -- Form 3
```

### Sub-Goals (If Primary Blocked)

1. **Form 1 ↔ Form 2:**
   - Is `row_aggregate - pointwise_aggregate` expressible in terms of coupled variation?
   - Quote: where is the residual computation in code?

2. **Form 2 ↔ Form 3:**
   - Does coupled variation aggregate ↔ pointwise aggregate (already proved by Task R)?
   - Confirm the identity used in Task R proof

3. **Form 3 decay:**
   - Can pointwise aggregate reach log-taper energy without schedule constraint?
   - Quote: where would this identity exist?

---

## Deliverables

### If Successful (Proof Found)
- New file: `proofs/NBMellinTools/NB22H15EquivalenceThreeFormulations.lean`
- Theorem: `h15_frontier_equivalence_three_forms` (sorry-free)
- Axioms: Only propext, Classical.choice, Quot.sound

### If Unsuccessful (Gap Found)
- New file: `H15_EQUIVALENCE_THREE_FORMS_GAP_REPORT.md`
- Report structure:
  1. Which equivalences hold (with line numbers)
  2. Which equivalence fails
  3. Missing theorem required (exact type signature)
  4. Why it's missing (structural obstacle, new machinery, disconnected definitions)

---

## Hard Rules

❌ **Do NOT:**
- Reconstruct missing definitions
- Invent proxy theorems
- State equivalence without proof
- Skip quoting file paths/line numbers

✅ **DO:**
- Use only existing code definitions
- Quote exact locations (file:line)
- State gaps precisely if proof fails
- Provide executable Lean code (no sorry)

---

## Estimated Complexity

- **If equivalence trivial:** 1–2 hours (high-level theorem assembly)
- **If equivalence needs work:** 3–4 hours (trace three pathways, identify mismatches)
- **If gap found:** 1–2 hours (report writing, type signature extraction)

---

## Success Criteria

✅ **Success:** Theorem proved with zero sorry, only standard axioms  
⚠️ **Partial Success:** Gap identified and precisely specified  
❌ **Failure:** Equivalence proved false (should not happen given Task R)

---

*Task U ready for submission*
