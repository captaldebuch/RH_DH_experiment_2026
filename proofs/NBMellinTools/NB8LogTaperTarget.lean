/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB7ApproximationSequence
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# NB8: the explicit Möbius log-taper target

This file records one concrete coefficient family suggested by the
Báez--Duarte/Bettin--Conrey--Farmer programme.  At stage `n`, the cutoff is
`N = n + 2` and the coefficient attached to the generator with denominator
`k + 1` is

`-μ(k + 1) log(N / (k + 1)) / log N`.

The minus sign matches the Mellin convention of `rhoBD` in this package:
`mellin rhoBD = -ζ(s)/(s n^s)`.

The proposition `LogTaperL2Decay` is the exact statement that these explicit
approximants have vanishing project `L²` error.  It is **not proved here** and
is not claimed equivalent to RH.  The theorems below prove only that it is a
sufficient input for the verified NB7-to-RH chain.
-/

open Filter

namespace NBMellinTools.NB8

open NBMellinTools.NB2
open NBMellinTools.NB7

/-- The total cutoff used at sequence index `n`; it starts at `2`, so the
normalizing logarithm is nonzero and positive. -/
def logTaperLength (n : ℕ) : ℕ := n + 2

/-- The explicit real Möbius log-taper coefficients, indexed by denominators
`k + 1` in the range `1, ..., n + 2`. -/
noncomputable def logTaperCoeffs
    (n : ℕ) (k : Fin (logTaperLength n)) : ℝ :=
  -((ArithmeticFunction.moebius (k.val + 1) : ℤ) : ℝ) *
    (Real.log
        (((logTaperLength n : ℕ) : ℝ) / ((k.val + 1 : ℕ) : ℝ)) /
      Real.log ((logTaperLength n : ℕ) : ℝ))

/-- The exact `L²(0,∞)` error of the explicit log-taper approximant. -/
noncomputable def logTaperL2Error (n : ℕ) : ℝ :=
  BaezDuarteL2Error (logTaperLength n) (logTaperCoeffs n)

/-- The concrete open analytic target for this coefficient family. -/
def LogTaperL2Decay : Prop :=
  Tendsto logTaperL2Error atTop (nhds 0)

/-- Vanishing of the explicit log-taper error constructs the generic certified
approximation sequence expected by NB7. -/
noncomputable def logTaperApproximationSequence
    (hdecay : LogTaperL2Decay) :
    BaezDuarteApproximationSequence where
  length := logTaperLength
  coeffs := logTaperCoeffs
  error_tendsto_zero := hdecay

/-- The explicit log-taper decay is sufficient for the active
Nyman--Beurling criterion. -/
theorem nymanBeurlingCriterion_of_logTaperL2Decay
    (hdecay : LogTaperL2Decay) :
    NymanBeurlingCriterion :=
  nymanBeurlingCriterion_of_approximationSequence
    (logTaperApproximationSequence hdecay)

/-- The precise conditional endpoint for the explicit log-taper route. -/
theorem riemannHypothesis_of_logTaperL2Decay
    (hdecay : LogTaperL2Decay) :
    RiemannHypothesis :=
  riemannHypothesis_of_approximationSequence
    (logTaperApproximationSequence hdecay)

end NBMellinTools.NB8
