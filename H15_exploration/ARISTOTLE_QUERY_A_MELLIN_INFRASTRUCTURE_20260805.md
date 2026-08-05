# Aristotle Query A: Mellin Transform Infrastructure for the RH Gate

**Date:** 2026-08-05  
**Scope:** Formalize the Mellin-Plancherel isometry and the Mellin transform of the fractional-part generator  
**Estimated effort:** 3–4 hours  
**Axioms:** Only Mathlib, `propext`, `Classical.choice`, `Quot.sound`

---

## CONTEXT & MOTIVATION

The Task B frontier characterization reduces LogTaperL2Decay to a statement about Riesz means of `1/ζ(s)` on the critical line (Re s = 1/2):

```
LogTaperL2Decay ⟺ ∑_{k<N} (1 − k/N) μ(k+1) log(N/(k+1))/(k+1) · (k+1)^{−(1/2+it)}
                   converges to 1/ζ(1/2+it) as N → ∞ 
                   in weighted L²(ℝ, dt/|1/2+it|²)
```

This frontier statement is made **rigorous** via the Mellin-Plancherel isometry:

**Classical statement:**
```
∫₀^∞ f(x) g(x) dx = (1/2πi) ∫_{Re s = c} f̂(s) ĝ(1−s) ds,
where f̂(s) = ∫₀^∞ f(x) x^{s−1} dx is the Mellin transform.
```

For our purposes:
- `f(x) = χ_{[0,1]}(x)` (indicator function)
- `g(x) = ∑_{k<N} c_k(N) ρ_k(x)` (approximant)
- `ρ_k(x) = {1/((k+1)x)}` (fractional-part generators)

The Mellin transform turns the L²(ℝ) error into a sum of Mellin transforms evaluated on the critical line, and **those Mellin transforms are evaluations of ζ**.

---

## TASK SPECIFICATION

### **Part 1: Mellin Transform of Elementary Functions**

**Goal:** Establish Mellin transforms for the building blocks of our problem.

#### 1.1: Mellin Transform of Indicator Function

**Classical statement:**
```
∫₀^∞ χ_{[0,1]}(x) · x^{s−1} dx = 1/s   for 0 < Re s < ∞
```

**Proof approach:**
```
= ∫₀¹ x^{s−1} dx 
= [x^s/s]₀¹ 
= 1/s
```

**Lean formalization needed:**
```lean
theorem mellin_indicator_unit_interval (s : ℂ) (hs : 0 < s.re) :
    ∫ x in Ioc 0 1, x ^ (s - 1) = 1 / s := by
  sorry
```

**Dependencies:** `∫₀¹ x^{s−1}` convergence for Re s > 0

#### 1.2: Mellin Transform of Reciprocal Function

**Classical statement:**
```
∫₀^∞ {1/(nx)} · x^{s−1} dx = −ζ(s) / (s · n^s)   for 0 < Re s < 1, n ≥ 1
```

where `{y} = y − ⌊y⌋` is the fractional part.

**Proof approach (classical):**
```
{1/(nx)} = 1/(nx) − ⌊1/(nx)⌋
         = ∑_{k=1}^∞ (1_{k·n ≤ 1/x < (k+1)n})  [indicator for each floor piece]

∫₀^∞ {1/(nx)} x^{s−1} dx 
= ∑_{k=1}^∞ ∫_0^∞ 1_{k·n ≤ 1/x} x^{s−1} dx
= ∑_{k=1}^∞ ∫_0^{1/(kn)} x^{s−1} dx    [invert the inequality]
= ∑_{k=1}^∞ (1/(kn))^s / s
= (1/s) · (1/n^s) · ∑_{k=1}^∞ 1/k^s
= −ζ(s) / (s · n^s)    [using analytic continuation of ζ]
```

**Lean formalization needed:**
```lean
theorem mellin_fractional_reciprocal (n : ℕ) (hn : 0 < n) (s : ℂ) 
    (hs_re : 0 < s.re) (hs_re_lt_one : s.re < 1) :
    ∫ x in Ioi 0, (fract (1 / (n * x))) * x ^ (s - 1) = 
      − Nat.zeta s / (s * n ^ s) := by
  sorry
  where fract x := x - Int.floor x
```

**Dependencies:** 
- Fractional part definition and properties
- Series representation of ζ(s) for Re s > 1 and analytic continuation to 0 < Re s < 1
- Interchanging sum and integral (Fubini/Tonelli)

---

### **Part 2: Mellin-Plancherel Isometry**

**Goal:** Formalize the Mellin-Plancherel duality.

#### 2.1: L² Isometry on Logarithmic Scale

**Classical statement:**
```
For f ∈ L²(ℝ⁺, dx), define F(s) = ∫₀^∞ f(x) x^{s−1} dx (Mellin transform).

Then: ∫₀^∞ |f(x)|² dx = (1/2π) ∫_ℝ |F(1/2 + it)|² dt
```

This is the Mellin-Plancherel isometry. It relates L²-norm on (0,∞) with dx measure to L²-norm on the vertical line Re s = 1/2 with dt measure.

**Lean formalization needed:**
```lean
theorem mellin_plancherel_isometry (f : ℝ → ℂ) 
    (hf_meas : AEStronglyMeasurable f) 
    (hf_L2 : ∫⁻ x in Ioi 0, ‖f x‖₊ ^ 2 ≠ ∞) :
    ∫ x in Ioi 0, ‖f x‖ ^ 2 = 
      (1 / (2 * π)) * ∫ t in univ, 
        ‖∫ x in Ioi 0, f x * x ^ (Complex.ofReal (1 / 2) + I * t - 1)‖ ^ 2 := by
  sorry
```

**Dependencies:**
- Plancherel-type theorems (classical Fourier analysis on ℝ⁺ with Haar measure)
- Contour integration / analytic continuation machinery
- Possibly new Mathlib development

**Note:** This is the most sophisticated piece and may require significant infrastructure.

#### 2.2: Specialized Form for Our Problem

**Goal:** Concrete instance for the specific f, g in the LogTaperL2Decay problem.

```lean
theorem mellin_plancherel_for_log_taper (N : ℕ) (hn : 0 < N) :
    ∫ x in Ioi 0, 
      ‖χ_{[0,1]}(x) - ∑ k : Fin N, c_k(N) * ρ_k(x)‖ ^ 2 =
    (1 / (2 * π)) * ∫ t : ℝ,
      ‖1 / (1/2 + I*t) + Nat.zeta (1/2 + I*t) * D_N(1/2 + I*t)‖ ^ 2 / 
      ‖1/2 + I*t‖ ^ 2 := by
  sorry
  where D_N(s) = ∑ k : Fin N, c_k(N) * (k+1) ^ (-s)
```

This directly connects the L² integral (LHS) to the Riesz-mean statement on the critical line (RHS).

---

### **Part 3: Mellin Inversion Formula**

**Goal:** Enable going backward from Mellin transform to original function.

#### 3.1: Bromwich Inversion Formula

**Classical statement:**
```
If F(s) = ∫₀^∞ f(x) x^{s−1} dx, then:

f(x) = (1/2πi) ∫_{c−i∞}^{c+i∞} F(s) x^{−s} ds

where c > max(Re s : s is a singularity of F).
```

**Lean formalization needed:**
```lean
theorem mellin_inversion_bromwich (f : ℝ → ℂ) (F : ℂ → ℂ) (c : ℝ) 
    (hf : Continuous f) (hF : ∀ s, F s = ∫ x in Ioi 0, f x * x ^ (s - 1))
    (h_singularities : ∀ s, F.Singularity s → s.re ≤ c) :
    ∀ x > 0, f x = (1 / (2 * π * I)) * 
      ∫ t : ℝ, F (c + I * t) * x ^ (-(c + I * t)) := by
  sorry
```

**Dependencies:** 
- Contour integration in complex plane
- Residue theorem
- Analyticity conditions on F

#### 3.2: Vertical Line Integration (Critical for RH)

**Goal:** Handle integration on Re s = 1/2 specifically.

```lean
theorem mellin_inversion_vertical_line (f : ℝ → ℂ) (F : ℂ → ℂ) 
    (hf : Continuous f) 
    (hF : ∀ s, F s = ∫ x in Ioi 0, f x * x ^ (s - 1))
    (h_no_singularities : ∀ s, s.re ≥ 1/2 → ¬ F.Singularity s) :
    ∀ x > 0, f x = (1 / (2 * π * I)) * 
      ∫ t : ℝ, F (1/2 + I * t) * x ^ (-(1/2 + I * t)) := by
  sorry
```

This is the form we use: if F has no singularities on/right of the critical line, we can shift the inversion contour there.

---

## DELIVERABLES

### **Scope A (Minimum viable):**
1. ✅ Mellin transforms of χ_{[0,1]} and {1/(nx)} (Parts 1.1, 1.2)
2. ✅ Mellin-Plancherel isometry statement (Part 2.1)
3. ✅ Bromwich inversion formula (Part 3.1)

**Estimated effort:** 2–3 hours  
**Use case:** Establish the equivalence between L² error and critical-line integral

### **Scope B (Recommended):**
Scope A + 
4. ✅ Concrete instance for log-taper (Part 2.2)
5. ✅ Vertical-line inversion (Part 3.2)

**Estimated effort:** 3–4 hours  
**Use case:** Directly transform LogTaperL2Decay into a statement about 1/ζ on Re s = 1/2

---

## AXIOMS & CONSTRAINTS

- **No custom axioms.** Only `propext`, `Classical.choice`, `Quot.sound` (already in use).
- **Mathlib only.** No external libraries except standard Lean 4 and Mathlib.
- **No sorry.** All proofs must be machine-checked; no deferred steps.
- **Clean integration.** Output as `NBMellinTools.NB17MellinTransform` and related modules, buildable in isolation.

---

## SUCCESS CRITERIA

1. ✅ **Compiles:** `lake build NBMellinTools.NB17MellinTransform` completes with no errors or sorry.
2. ✅ **No sorry:** Every theorem statement has a complete proof.
3. ✅ **Usability:** Can apply Mellin-Plancherel to directly rewrite the LogTaperL2Decay error as `(1/2π) ∫_ℝ |1 + ζ(s) D_N(s)|² / |s|² dt` on Re s = 1/2.
4. ✅ **Axioms clean:** Output of `#print axioms` shows only the standard three.
5. ✅ **Documentation:** Each theorem includes a comment explaining its classical source and role in the RH gate characterization.

---

## CLASSICAL REFERENCES

- Tichmarsh, E.C. (1986). *The Theory of the Riemann Zeta-Function* (2nd ed.). Oxford University Press. 
  - Ch. 2: Mellin transform and Fourier inversion
  - Ch. 5: Mellin transforms of L-functions
  - Ch. 6: Zero-free regions via Mellin methods

- Bateman & Knopp (1989). *Handbook of Mathematical Functions*.
  - Ch. 11: Mellin transform tables

- Ingham, A.E. (1932). *The Distribution of Prime Numbers*. 
  - Ch. II: Mellin inversion on vertical lines

---

## EXPECTED OUTCOMES

**If successful:**
- LogTaperL2Decay is equivalent to a rigorous statement about Riesz means of 1/ζ on the critical line.
- The frontier is now **transparently** framed in Mellin-transform language, which connects naturally to ζ's analytic properties.
- Route 1 is open: can now attempt to formalize results about zero-free regions and their implications for Riesz-mean asymptotics.

**If partial (infrastructure blocks):**
- Document which steps are blocked and why (e.g., "Mellin-Plancherel requires Fourier analysis on ℝ⁺ that Mathlib doesn't have yet").
- Propose minimal new Mathlib infrastructure needed.

**If infrastructure proves too deep:**
- Fall back to Routes B/C (Riesz asymptotics or second-moment collision) using classical bounds without full Mellin machinery.

---

## NEXT QUERY (IF THIS SUCCEEDS)

Once Query A is complete, **Query B** will target the Riesz-mean asymptotics directly:

*"Using the Mellin-Plancherel isometry from Query A, formalize the dependence of Riesz-mean convergence on zero-free regions of ζ. Identify the exact frontier: what statement about ζ's zeros would prove/disprove LogTaperL2Decay?"*

---

## SUBMISSION INSTRUCTIONS

Submit this as a single Aristotle task:

```
Project name: NB17 Mellin Transform Infrastructure
Task: Formalize Mellin-Plancherel isometry and Mellin transforms of χ_{[0,1]} 
      and fractional-part {1/(nx)}. See attached specification for full scope.
Deadline: Next 4 hours
Scope: Parts 1 (minimum) or 1+2+3 (recommended)
Success criterion: Implements all threaded theorems with no sorry; 
                  rewrite LogTaperL2Decay as critical-line integral
Axioms: Only Mathlib + propext/Classical.choice/Quot.sound
```

---

**Status:** Ready for submission.
