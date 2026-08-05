/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12VaalerTail
import NBMellinTools.NB11VasyuninEvaluation

/-!
# NB13: the signed bilinear dispersion reduction to RH

This file establishes a conditional assembly theorem from three named
components. It does not prove any of those analytic components.

Using NB11's proved classical evaluation, this file proves:

`SmoothMertensDecay → FourierRemainderDecay →`
`SignedBilinearDispersionDecay → RiemannHypothesis`.

These are sufficient hypotheses. No converse or equivalence with RH is
asserted. NB12 now gives a genuine exact finite Fourier decomposition, but
neither the remainder decay nor the signed finite-core decay is proved.
-/

open Filter
open scoped BigOperators

namespace NBMellinTools.NB13

open NBMellinTools.NB6
open NBMellinTools.NB8
open NBMellinTools.NB9
open NBMellinTools.NB10
open NBMellinTools.NB11
open NBMellinTools.NB12

/-- Decay of NB12's genuine finite Fourier core at the proposed cutoff. -/
def SignedBilinearDispersionDecay : Prop :=
  Tendsto
    (fun n : ℕ =>
      vasyuninLowModeCore
        (logTaperLength n) (logTaperCoeffs n) (vaalerModeCutoff n))
    atTop (nhds 0)

/-- The coupled Vasyunin decay holds under Mertens smooth decay and signed
bilinear dispersion decay. -/
theorem logTaperVasyuninCoupledDecay_of_smooth_and_bilinear
    (hsmooth : SmoothMertensDecay)
    (hrem : FourierRemainderDecay)
    (hdisp : SignedBilinearDispersionDecay) :
    LogTaperVasyuninCoupledDecay := by
  have hcot : Tendsto
      (fun n : ℕ => vasyuninCotangentTerm (logTaperLength n) (logTaperCoeffs n))
      atTop (nhds 0) :=
    tendsto_vasyuninCotangentTerm_of_low_mode hdisp hrem
  exact tendsto_vasyuninCoupledExpression_of_smooth_and_cotangent hsmooth hcot

/-- The explicit log-taper error vanishes under smooth decay, Fourier
remainder decay, and signed finite-core dispersion. -/
theorem logTaperL2Decay_of_reduction
    (hsmooth : SmoothMertensDecay)
    (hrem : FourierRemainderDecay)
    (hdisp : SignedBilinearDispersionDecay) :
    LogTaperL2Decay := by
  rw [logTaperL2Decay_iff_vasyuninCoupledDecay vasyuninGramEvaluation]
  exact logTaperVasyuninCoupledDecay_of_smooth_and_bilinear hsmooth hrem hdisp

/-- Conditional analytic reduction: the three named decay inputs imply the
global Riemann Hypothesis. -/
theorem riemannHypothesis_of_analytic_reduction
    (hsmooth : SmoothMertensDecay)
    (hrem : FourierRemainderDecay)
    (hdisp : SignedBilinearDispersionDecay) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_logTaperL2Decay
  exact logTaperL2Decay_of_reduction hsmooth hrem hdisp

end NBMellinTools.NB13
