# Status report: `LogTaperL2Decay` (NB8)

**Verdict: not proved, and not provable by the elementary route.  The statement
implies the Riemann hypothesis, and the analysis below locates the exact point
where an RH-strength input is unavoidable.  Everything on the unconditional
side of that point has been formalised, with no `sorry` and no new axioms, in
`NB8LogTaperScope.lean`.**

## 0. State of the repository

The uploaded project is a fragment of a larger package.  Every source file
imports `NBMellinTools.*` modules that are **absent** from the extract, so
before this session *nothing in the project compiled*:

| file | missing import |
|---|---|
| `BaezDuarteTail.lean` | `NBMellinTools.NB2Mellin` |
| `NB7ApproximationSequence.lean` | `NBMellinTools.NB6GlobalClosure` |
| `NB8LogTaperTarget.lean` | (via NB7) `NBMellinTools.NB6GlobalClosure` |
| `NB15GramBlockDecomposition.lean` | `NBMellinTools.NB15NonresonantBlockHSBounds` |
| `NB15JointLedgerUnification.lean` | `NBMellinTools.NB12BBLSH15…` |
| `NB15Phase4OperatorTraceDecay.lean` | `NBMellinTools.NB15Phase3Spectral` |

Following the precedent already set inside the repository by
`NB15OperatorAdaptation.lean` ("the historical Phase 1 source file was not
present in this repository, so the objects it was supposed to provide are set
up here explicitly"), this session reconstructs the *definitional* part of the
missing NB2 file:

* new file `NBMellinTools/NB2Mellin.lean` defines `chi01 x = 1_{x ≤ 1}` and the
  zero-based Báez–Duarte generator `rhoBD k x = {1/((k+1)x)}` — exactly the
  forms forced by the existing proofs in `BaezDuarteTail.lean` — plus basic
  measurability/boundedness lemmas.  With it, **`BaezDuarteTail.lean` now
  compiles unchanged.**

The missing `NB6GlobalClosure` is *not* reconstructed: its content is the
classical Nyman–Beurling implication "criterion ⇒ RH", a deep theorem which is
neither in Mathlib nor provable here.  Adding it as an `axiom` or as a
`sorry`-ed theorem would only manufacture a fake chain to `RiemannHypothesis`,
so `NB7ApproximationSequence.lean` and `NB8LogTaperTarget.lean` remain
unbuildable, and the new work is self-contained in `NB8LogTaperScope.lean`
(which repeats the NB8 definitions verbatim in namespace
`NBMellinTools.NB8Scope`).

## 1. What is now proved unconditionally

All statements below are about the *literal* NB8 objects
(`bdApprox`, `BaezDuarteL2Error`, `logTaperCoeffs`, …) and are machine-checked
in `NB8LogTaperScope.lean` (axioms: `propext`, `Classical.choice`, `Quot.sound`
only).

1. **The problem is well posed.** `integrableOn_sq_bdError`: for every `N` and
   every coefficient vector, `(χ - ∑ c_k ρ_k)²` is integrable on `(0,∞)`.
   This matters: in Lean `∫` of a non-integrable function is `0` by convention,
   so without this lemma a "vanishing error" statement could be vacuous.
2. **Exact tail splitting.** `baezDuarteL2Error_eq_split`:
   `error = ∫_0^1 (1 - A)² + S²` where `S = ∑ c_k/(k+1)`, because on `(1,∞)`
   the approximant is exactly `S/x`.
3. **Gram expansion (steps 1–3 of the programme).**
   `baezDuarteL2Error_eq_gram`:
   `error = 1 - 2 ∑_k c_k m_k + ∑_{j,k} c_j c_k G_{jk}`,
   with `m_k = ⟨χ, ρ_k⟩ = ∫_0^1 ρ_k` and `G_{jk} = ⟨ρ_j, ρ_k⟩`.
   `bdGram_eq` splits each Gram entry as
   `G_{jk} = ∫_0^1 ρ_j ρ_k + 1/((j+1)(k+1))`.
4. **Moments in closed form.** `bdMoment_eq`:
   `m_k = (log (k+1) + m_0)/(k+1)`, `m_0 = ∫_0^1 {1/x} dx`
   (classically `m_0 = 1 - γ`; that identification is not needed and not
   formalised).
5. **Two rigorous lower bounds ("obstructions").**
   * `sq_tailScalar_le_baezDuarteL2Error` : `S² ≤ error`;
   * `sq_moment_le_baezDuarteL2Error` : `(1 - ∑ c_k m_k)² ≤ error`
     (Cauchy–Schwarz on the unit interval).
6. **No finite stage is ever exact.** `baezDuarteL2Error_pos`:
   `0 < BaezDuarteL2Error N c` for **every** `N` and **every** coefficient
   vector.  Proof: on a short interval just left of `1/N!` all generators
   `ρ_k`, `k < N`, are simultaneously `≤ δ`, so the approximant is `≤ 1/2`
   there while the target is `1`.  Consequently the Nyman–Beurling infimum is
   never attained, and `LogTaperL2Decay` is an irreducibly asymptotic
   statement: no finite computation, however large, can certify it (nor can a
   `decide`/`native_decide` style argument).
7. **What `LogTaperL2Decay` forces.** Specialising 5. to the log-taper
   coefficients (`logTaper_moebius_tail_tendsto_zero`,
   `logTaper_moebius_moment_tendsto_neg_one`), `LogTaperL2Decay` implies
   * `(1/log N) ∑_{m ≤ N} μ(m) log(N/m)/m → 0`, and
   * `(1/log N) ∑_{m ≤ N} μ(m) log(N/m)(log m + m_0)/m → -1`.

## 2. The frontier, precisely

Write `n_k = k+1`, `D_N(s) = ∑_{k<N} c_k n_k^{-s}`.  For `0 < Re s < 1` one has
the classical Mellin transforms

```
∫_0^∞ χ_{[0,1]}(x) x^{s-1} dx = 1/s ,
∫_0^∞ {1/(n x)}   x^{s-1} dx = -ζ(s)/(s n^s)
```

(the second is the identity recorded in the NB8 header, and it is the reason
the minus sign appears in `logTaperCoeffs`).  Mellin–Plancherel on the line
`Re s = 1/2` therefore turns the NB8 error into

```
BaezDuarteL2Error N c = (1/2π) ∫_ℝ |1 + ζ(s) D_N(s)|² / |s|² dt ,   s = 1/2 + it.
```

For the Möbius log-taper,
`D_N(s) = -(1/log N) ∑_{m ≤ N} μ(m) log(N/m) m^{-s}` is precisely the
first-order Riesz (logarithmic Cesàro) mean of the Dirichlet series
`∑ μ(m) m^{-s} = 1/ζ(s)`.  Hence

> **`LogTaperL2Decay` ⟺ the Riesz-mean partial sums of `1/ζ` converge to
> `1/ζ(1/2+it)` in the weighted space `L²(ℝ, dt/|1/2+it|²)`.**

That convergence needs `1/ζ` to be well behaved on the closed half plane
`Re s ≥ 1/2`, i.e. it needs `ζ` to have no zeros with `Re s > 1/2`: if
`ζ(ρ) = 0` with `Re ρ > 1/2`, the linear functional `f ↦ (mellin f)(ρ)` kills
every `ρ_k` but not `χ_{[0,1]}`, so the error stays bounded away from `0`.
This is the classical Nyman–Beurling obstruction, and it is *the* structural
reason why no elementary argument can succeed:

* every step in §1 is a finite-dimensional or purely measure-theoretic
  manipulation, and none of them sees the zeros of `ζ`;
* the only remaining quantity is the asymptotics of the Gram quadratic form of
  item 3.  Its compact entries, after the inversion `x ↦ 1/x`, are
  `∫_1^∞ {u/j}{u/k} du/u²`, whose closed forms are the Vasyunin/Dedekind
  cotangent sums attached to `j/k`.  The `N → ∞` behaviour of
  `∑_{j,k ≤ N} μ(j)μ(k) (…)_{jk}` is governed by the correlation of the Möbius
  function with these `gcd`-type weights, which by the Mellin identity above is
  literally an assertion about `1/ζ` on `Re s = 1/2`.

So the frontier is exactly: **the Gram-form asymptotics = a zero-free region.**
An "elementary" proof of `LogTaperL2Decay` would prove RH; conversely no
elementary manipulation of the generators can supply the missing input.

## 3. Necessary vs. sufficient

| statement | status |
|---|---|
| `S_N = ∑ c_k/(k+1) → 0` (Möbius tail) | **necessary**, proved here to follow from `LogTaperL2Decay`; classically true (Mertens/PNT-strength), so it does not obstruct |
| `∑ c_k m_k → 1` (first moment) | **necessary**, proved here; classically true |
| all finite-dimensional moment conditions of this kind | necessary; each is a *single* linear functional, hence far from sufficient |
| error `→ 0` for the *specific* Möbius log-taper family | **the target**; implies RH |
| `inf_c error → 0` (Nyman–Beurling/Báez–Duarte criterion) | equivalent to RH |
| RH ⇒ the target | plausible and expected in the literature for this mollifier, but a separate (also unformalised) theorem: RH gives the criterion, not automatically this particular coefficient family |

In particular the direction actually used by the package
(`LogTaperL2Decay → NymanBeurlingCriterion`) is the cheap one; it is reproved
self-containedly here as `nymanBeurlingCriterion_of_logTaperL2Decay`.  The
expensive one, `NymanBeurlingCriterion → RiemannHypothesis`, lives in the
missing `NB6GlobalClosure` and is not available in this repository.

## 4. What a Lean proof would require (roadmap)

None of the following is currently in Mathlib; each is a substantial project in
its own right:

1. the Mellin–Plancherel isometry `L²((0,∞), dx) ≅ L²(Re s = 1/2, dt/2π)`;
2. the Mellin transform of the fractional-part generator,
   `∫_0^∞ {1/(nx)} x^{s-1} dx = -ζ(s)/(s n^s)` on `0 < Re s < 1`, with `ζ`
   given by its analytic continuation;
3. a quantitative theory of Riesz means of `1/ζ` on vertical lines
   (this is where RH enters and where the argument must fail without it);
4. for the converse direction, the vanishing functional `f ↦ (mellin f)(ρ)` at
   a hypothetical off-line zero, i.e. the Nyman–Beurling implication itself.

Items 1–2 are formalisable with effort and are the natural next milestones;
item 3 is RH.

## 5. Numerical consistency check (not formally verified)

A floating-point evaluation of the two necessary conditions of §1.7 (Möbius
sieve up to `N = 2·10⁵`) gives

```
N        (1/log N) Σ μ(m) log(N/m)/m      (1/log N) Σ μ(m) log(N/m)(log m + m₀)/m
100          0.2174                          -0.656
1000         0.1448                          -0.771
10⁴          0.1086                          -0.829
10⁵          0.0869                          -0.863
2·10⁵        0.0819                          -0.871
```

consistent with the required limits `0` and `-1` (both approached at rate
`≍ 1/log N`).  This is an unverified numerical exploration, included only as a
sanity check that the log-taper family is not ruled out by the two proved
obstructions; it is **not** evidence for `LogTaperL2Decay`.
