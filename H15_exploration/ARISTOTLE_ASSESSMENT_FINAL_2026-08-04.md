# Aristotle Nonresonant Survey: Final Assessment
**Date:** 2026-08-04, 20:45 UTC  
**Status:** Analysis implemented through exact hyperbola reindexing and
complete modulus-period cancellation.

---

## What Aristotle Did Well

✅ **Correctly diagnosed the linear phase structure** — the nonresonant sum has an additive phase `e(ur/q)` that is linear in the summation variable, not the multiplicative/nonlinear phases for which tools like uniform stationary phase or Kloosterman hyper-bilinear estimates are designed.

✅ **Identified which classical tools do NOT apply:**
- Uniform stationary phase (Kíral–Petrow–Young, arXiv:1710.00916) — designed for nonlinear oscillatory integrals; would only be relevant after a transformation creates nonlinear Archimedean phase
- Bilinear hyper-Kloosterman estimates (Kowalski–Michel–Sawin, Annals 2017) — target more complex phases, not elementary additive ones
- Direct Ramanujan-sum replacement — works for complete periods, not incomplete frequency intervals

✅ **Surveys comprehensive modern tooling** — papers on exponential sums, van der Corput bounds, geometric/sum-product methods are genuine references

---

## What Needs Correction

❌ **Overstated the direct Ramanujan-sum conclusion.** Aristotle suggested: "Replace the nonresonant sum by Ramanujan sums via classical bounds."

**Why this fails on the actual H15 nonresonant sum:**
1. Frequencies are **incomplete**: `r ∈ [K+1, K+J]` filtered by `q ∤ r`, not all residues mod q
2. Each frequency carries a **nonconstant Estermann divisor coefficient**: `d(r)·r^{-3/2-it}`
3. Row numerator `u` is coprime to `q`, but frequency `r` need not be — only `q ∤ r` is known

The sum is not a complete Ramanujan sum `c_q(r)`, so direct substitution does not work.

---

## What Was Already Tested

The project already implemented the complete-period/Ramanujan strategy for the weighted numerator:

**Module:** `NB12BBLSH15RamanujanCompletionDefect.lean`
- Line 399: Exact variation-plus-boundary completion
- Line 487: Exact specialization to genuine H15 weights
- Completion budget: `2Q/U + 4Q²/U²`
- Stop test (Q=U): produces only constant bound **6**, no decay

**Conclusion:** Ramanujan completion alone is **insufficient** — already formally tested and rejected via stop test.

---

## The Best Actionable Consequence

**Divisor-hyperbola decomposition with geometric-period analysis:**

$$\sum_{\substack{K<r\le K+J\\q\nmid r}} d(r)\,r^{-3/2-it}\,e(ur/q) = \sum_a\ \sum_{\substack{b:\ K<ab\le K+J\\q\nmid ab}} (ab)^{-3/2-it}\,e(uab/q)$$

**Key observation:** For fixed `a`, the inner phase `e(uab/q)` is purely geometric.

Since `(u,q) = 1`, its reduced period is:
$$q_a = \frac{q}{\gcd(a,q)}$$

**What works here:**
- Complete periods in `b` cancel **exactly**
- Incomplete endpoint costs at most `q_a`
- Abel summation preserves the weight `b^{-3/2-it}` (not replaced by absolute majorant)
- This is considerably more faithful than invoking Bettin–Chandee or hyper-Kloosterman directly

---

## Recommended Lean Formalization Sequence

1. ✅ **Exact divisor-hyperbola reindexing proved** in
   `NB15NonresonantDivisorHyperbola.lean`
2. ✅ **Complete modulus-`q` cancellation proved** for the geometric phase
   `e(uab/q)` in both orientations
3. **Prove the incomplete geometric endpoint bound** using `q/gcd(a,q)` as the period
4. **Apply finite Abel summation** to the weight `b^{-3/2-it}` on the incomplete tail
5. **Sum over a, q, g** and run the exponent test against the complete H15 ledger

This route is more direct and faithful than invoking high-powered bilinear forms designed for different phase structures.

---

## Honest Scope Assessment

| Item | Status | Why It Matters |
|------|--------|----------------|
| **Ramanujan complete-period strategy** | ❌ Tested, insufficient | Already proven to yield only constant bound 6, not decay |
| **Direct Bettin–Chandee or Kloosterman replacement** | ❌ Does not apply | Phase is linear additive, not the nonlinear/multiplicative structures those tools target |
| **Uniform stationary phase** | ❌ Premature | Relevant only after transformation creates nonlinear Archimedean phase |
| **Divisor-hyperbola + geometric period** | ✅ **Recommended next target** | Preserves weight structure, exploits exact period cancellation, compatible with Abel summation |

---

## The Remaining Gate

Even if the divisor-hyperbola nonresonant route succeeds, the project still faces its principal challenge:

**The resonant sector** (`q | r`, where phase becomes exactly `1 + cos(π·s)`)

- Already separated by `NB15DirectAdditiveResonanceSplit.lean` and `NB15DirectAdditiveResonantFixedHeight.lean`
- Is **coupled to the retained correction ledger** — cannot be bounded in isolation
- Requires either:
  - Proving the correction decays sufficiently (RH-strength bound), or
  - A genuine signed integration showing the correction's coupling preserves cancellation

This remains the RH-strength gate, independent of whether the nonresonant sector succeeds.

---

## Final Verdict

- **Aristotle's survey:** Useful reference compilation and phase-structure diagnosis, not independent new mathematics
- **Direct conclusion (Ramanujan replacement):** Needs correction; the actual sum is incomplete and weighted
- **Best contribution:** Identification of the divisor-hyperbola + geometric-period route as more faithful than high-powered bilinear tools
- **Impact on timeline:** Provides a clearer, more precise formalization target for the nonresonant sector, but does not change the fact that the resonant sector's coupling to the correction ledger is the principal gate

The exact algebraic part of this assessment is now mechanically verified.
No nonresonant decay estimate is claimed.

---

## Recommended Next Steps

**Parallel tracks:**

1. **Codex:** Continue on character-average projection → collision-ledger bridge (the precise next target for the resonant sector)

2. **If formalizing the nonresonant sector:** Use divisor-hyperbola + geometric-period + Abel summation route (Aristotle's best diagnosis), not direct Ramanujan or bilinear replacement

3. **Validation:** Any nonresonant route must:
   - Preserve the weight `b^{-3/2-it}` through Abel summation, not introduce absolute-value majorants
   - Account for the incomplete interval `[K+1, K+J]` exactly
   - Pass the same exponent test as the resonant/correction sectors

4. **Priority:** Resonant sector → collision ledger bridge is the actual RH-strength gate; nonresonant success is necessary but not sufficient
