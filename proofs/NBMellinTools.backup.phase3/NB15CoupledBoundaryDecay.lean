/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB15EndpointBoundaryExtraction

/-!
# The exact H15 coupled-boundary decay target

The finite contour normalization has already been proved in
`NB15EndpointBoundaryExtraction`.  This file fixes one admissible rectangle
and packages the resulting expression as the literal certified NB8 energy.

The analytic target deliberately keeps together

* the elementary/endpoint ledger;
* the inverse adaptive damping;
* the complete normalized boundary; and
* the first-order residue subtraction.

Taking limits of these pieces separately is not assumed.  The only open input
is decay of their signed coupled sum, and that proposition is proved exactly
equivalent to `NB8.LogTaperL2Decay`.  Consequently the final implication to
the Riemann hypothesis contains no hidden specialization hypothesis.
-/

open Filter

namespace NBMellinTools.NB15

open NBMellinTools.NB8
open NBMellinTools.NB12

/-! ## Canonical finite boundary expression -/

/-- The centered normalized H15 boundary on the fixed admissible rectangle
with left line `Re(s) = -1` and height `1`.

Rectangle independence is already proved, so this choice removes irrelevant
auxiliary schedules from the final asymptotic target. -/
noncomputable def h15CanonicalCenteredBoundaryNumerator (n : ℕ) : ℂ :=
  h15NormalizedCompleteContourBoundary n (-1) 1 -
    h15GlobalFirstOrderCoefficient n

/-- The real undamped boundary contribution occurring in the certified
Nyman--Beurling energy.  The imaginary part and norm are taken only after the
inverse-damped centered numerator has been assembled. -/
noncomputable def h15CanonicalCenteredBoundaryContribution (n : ℕ) : ℝ :=
  ((h15ContourDamping n : ℂ)⁻¹ *
    h15CanonicalCenteredBoundaryNumerator n).im

/-- The complete signed H15 boundary expression.  This is not a proxy: below
it is proved pointwise equal to `NB8.logTaperL2Error`. -/
noncomputable def h15CertifiedCoupledBoundaryEnergy (n : ℕ) : ℝ :=
  h15CertifiedElementaryEndpointLedger n +
    h15CanonicalCenteredBoundaryContribution n

/-- The canonical centered boundary is exactly the damped additional residue.
This specializes the rectangle-independent extraction theorem. -/
theorem h15CanonicalCenteredBoundaryNumerator_eq_globalAdditionalResidue
    (n : ℕ) :
    h15CanonicalCenteredBoundaryNumerator n =
      h15GlobalAdditionalResidue n := by
  unfold h15CanonicalCenteredBoundaryNumerator
  symm
  exact h15GlobalAdditionalResidue_eq_normalizedBoundary_sub_firstOrder
    n (-1) 1 (by norm_num) (by norm_num)

/-- Restoring the inverse damping recovers the literal undamped endpoint
amplitude, including its sign and complex phase. -/
theorem h15CanonicalCenteredBoundaryContribution_eq_amplitude_im
    (n : ℕ) :
    h15CanonicalCenteredBoundaryContribution n =
      (h15AdditionalResidueAmplitude n).im := by
  unfold h15CanonicalCenteredBoundaryContribution
  rw [h15CanonicalCenteredBoundaryNumerator_eq_globalAdditionalResidue,
    h15ContourDamping_inv_mul_globalAdditionalResidue]

/-- Pointwise certification of the coupled boundary expression as the exact
NB8 log-taper energy. -/
theorem h15CertifiedCoupledBoundaryEnergy_eq_logTaperL2Error (n : ℕ) :
    h15CertifiedCoupledBoundaryEnergy n = logTaperL2Error n := by
  unfold h15CertifiedCoupledBoundaryEnergy
  rw [h15CanonicalCenteredBoundaryContribution_eq_amplitude_im]
  exact
    (logTaperL2Error_eq_elementaryEndpoint_add_additionalResidueAmplitude_im
      n).symm

/-! ## The exact open asymptotic target -/

/-- Decay of the complete signed, correction-preserving H15 boundary
expression.  This is the single analytic gate; no decay of either summand is
required separately. -/
def H15CertifiedCoupledBoundaryDecay : Prop :=
  Tendsto h15CertifiedCoupledBoundaryEnergy atTop (nhds 0)

/-- The coupled-boundary target is exactly the active NB8 target. -/
theorem h15CertifiedCoupledBoundaryDecay_iff_logTaperL2Decay :
    H15CertifiedCoupledBoundaryDecay ↔ LogTaperL2Decay := by
  unfold H15CertifiedCoupledBoundaryDecay LogTaperL2Decay
  have hfun : h15CertifiedCoupledBoundaryEnergy = logTaperL2Error := by
    funext n
    exact h15CertifiedCoupledBoundaryEnergy_eq_logTaperL2Error n
  rw [hfun]

/-- The exact H15 boundary decay supplies the certified Nyman--Beurling
log-taper decay. -/
theorem logTaperL2Decay_of_h15CertifiedCoupledBoundaryDecay
    (hdecay : H15CertifiedCoupledBoundaryDecay) :
    LogTaperL2Decay :=
  h15CertifiedCoupledBoundaryDecay_iff_logTaperL2Decay.mp hdecay

/-- Conditional endpoint of the present H15 route.  The only hypothesis is
the explicit coupled-boundary decay proposition above. -/
theorem riemannHypothesis_of_h15CertifiedCoupledBoundaryDecay
    (hdecay : H15CertifiedCoupledBoundaryDecay) :
    RiemannHypothesis :=
  riemannHypothesis_of_logTaperL2Decay
    (logTaperL2Decay_of_h15CertifiedCoupledBoundaryDecay hdecay)

/-! ## Optional endpoint splitting -/

/-- Generic discrete cancellation identity.  If one summand has a certified
endpoint, decay of the coupled sum is equivalent to convergence of the other
summand to the opposite endpoint. -/
theorem tendsto_add_zero_iff_tendsto_neg_of_tendsto_atTop
    {first second : ℕ → ℝ} {endpoint : ℝ}
    (hfirst : Tendsto first atTop (nhds endpoint)) :
    Tendsto (fun n => first n + second n) atTop (nhds 0) ↔
      Tendsto second atTop (nhds (-endpoint)) := by
  constructor
  · intro hcoupled
    simpa using hcoupled.sub hfirst
  · intro hsecond
    simpa using hfirst.add hsecond

/-- If the elementary endpoint ledger is evaluated separately, the remaining
analytic target is convergence of the centered boundary contribution to the
opposite endpoint.  This theorem is an optional decomposition, not an
assertion that such separate evaluation is easier. -/
theorem h15CertifiedCoupledBoundaryDecay_iff_centeredBoundaryLimit
    {endpoint : ℝ}
    (hendpoint : Tendsto h15CertifiedElementaryEndpointLedger atTop
      (nhds endpoint)) :
    H15CertifiedCoupledBoundaryDecay ↔
      Tendsto h15CanonicalCenteredBoundaryContribution atTop
        (nhds (-endpoint)) := by
  unfold H15CertifiedCoupledBoundaryDecay h15CertifiedCoupledBoundaryEnergy
  exact tendsto_add_zero_iff_tendsto_neg_of_tendsto_atTop hendpoint

/-- A nonzero certified endpoint prevents a separate zero-limit claim for the
elementary ledger. -/
theorem not_tendsto_elementaryEndpoint_zero_of_limit_ne_zero
    {endpoint : ℝ}
    (hendpoint : Tendsto h15CertifiedElementaryEndpointLedger atTop
      (nhds endpoint))
    (hendpoint_ne : endpoint ≠ 0) :
    ¬ Tendsto h15CertifiedElementaryEndpointLedger atTop (nhds 0) := by
  intro hzero
  exact hendpoint_ne (tendsto_nhds_unique hendpoint hzero)

/-! ## Honest low/middle/high route -/

/-- A non-vacuous contour-height schedule.  Positivity makes every symmetric
interval genuine, while cofinality prevents the frequency decomposition from
being certified at the degenerate height `T = 0`. -/
structure H15DivergingContourHeightSchedule (T : ℕ → ℝ) : Prop where
  tendsto_atTop : Tendsto T atTop atTop
  positive : ∀ n, 0 < T n

/-- The low-frequency sector enlarged by exactly the two real terms that the
right-edge split does not contain: the certified elementary/endpoint ledger
and the endpoint-to-linear contour defect.  Keeping these three terms signed
inside one expression prevents the correction from being lost to separate
absolute-value estimates. -/
noncomputable def h15CertifiedCorrectionCoupledLowEndpointSector
    (n : ℕ) (T : ℝ) : ℝ :=
  h15CertifiedElementaryEndpointLedger n +
    h15EndpointToLinearPostFEDefect n
      (h15CanonicalMiddleLowerCutoff n) T +
    (h15CorrectionCoupledLowFrequencyRightEdge n
      (h15CanonicalMiddleLowerCutoff n) T).im

/-- Exact decomposition of the certified energy into the enlarged signed low
sector, the finite Bettin--Chandee middle window, and the already-controlled
ultra-high tail. -/
theorem h15CertifiedCoupledBoundaryEnergy_eq_lowEndpoint_add_middle_add_high
    (n : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    h15CertifiedCoupledBoundaryEnergy n =
      h15CertifiedCorrectionCoupledLowEndpointSector n T +
        (h15BettinChandeeMiddleFrequencyRightEdge n
          (h15CanonicalMiddleLowerCutoff n)
          (h15CanonicalMiddleWindowLength n) T).im +
        (h15HighFrequencyRightEdgeRemainder n
          (h15CanonicalMiddleUpperCutoff n) T).im := by
  rw [h15CertifiedCoupledBoundaryEnergy_eq_logTaperL2Error,
    logTaperL2Error_eq_elementaryEndpoint_add_completeLinearPostFE_add_defect
      n (h15CanonicalMiddleLowerCutoff n) T,
    h15CompleteLinearPostFERightEdge_eq_correctedRightEdge,
    h15CorrectedThreeHalfRightEdge_eq_canonical_three_sector n T hT]
  unfold h15CertifiedCorrectionCoupledLowEndpointSector
  simp only [Complex.add_im]
  ring

/-- Degenerate-height stop test.  At height zero both the finite middle
window and the high remainder vanish, so the enlarged low sector is exactly
the original certified energy.  Thus allowing the zero schedule would give
no analytic decomposition at all. -/
theorem h15CertifiedCorrectionCoupledLowEndpointSector_zero_height_eq_energy
    (n : ℕ) :
    h15CertifiedCorrectionCoupledLowEndpointSector n 0 =
      h15CertifiedCoupledBoundaryEnergy n := by
  have hsplit :=
    h15CertifiedCoupledBoundaryEnergy_eq_lowEndpoint_add_middle_add_high
      n 0 (by norm_num)
  have hmiddle :
      h15BettinChandeeMiddleFrequencyRightEdge n
          (h15CanonicalMiddleLowerCutoff n)
          (h15CanonicalMiddleWindowLength n) 0 = 0 := by
    simp [h15BettinChandeeMiddleFrequencyRightEdge,
      h15BettinChandeeMiddleFrequencyIntegral,
      h15BettinChandeeFiniteIntegratedHigh,
      h15BettinChandeeIntegratedSummand]
  have hhigh :
      h15HighFrequencyRightEdgeRemainder n
          (h15CanonicalMiddleUpperCutoff n) 0 = 0 := by
    simp [h15HighFrequencyRightEdgeRemainder,
      h15ThreeHalfHighFrequencyIntegralRemainder,
      h15TruncatedVerticalIntegral, h15ThreeHalfLowFrequencyIntegral]
  rw [hmiddle, hhigh] at hsplit
  simpa using hsplit.symm

/-- The precise low-frequency analytic gate needed by the three-sector route.
It is stronger and more faithful than decay of the right-edge low modes alone
because it retains the endpoint ledger and the contour transfer defect. -/
def H15CertifiedCorrectionCoupledLowEndpointDecay (T : ℕ → ℝ) : Prop :=
  Tendsto (fun n : ℕ =>
    h15CertifiedCorrectionCoupledLowEndpointSector n (T n))
    atTop (nhds 0)

/-- The imaginary part of the canonical ultra-high right-edge remainder
tends to zero along every nonnegative height schedule. -/
theorem tendsto_h15CanonicalHighFrequencyRightEdgeRemainder_im_zero
    (T : ℕ → ℝ) (hT : ∀ n, 0 ≤ T n) :
    Tendsto (fun n : ℕ =>
      (h15HighFrequencyRightEdgeRemainder n
        (h15CanonicalMiddleUpperCutoff n) (T n)).im)
      atTop (nhds 0) := by
  have HhighNorm : Tendsto (fun n : ℕ =>
      ‖h15HighFrequencyRightEdgeRemainder n
        (h15CanonicalMiddleUpperCutoff n) (T n)‖)
      atTop (nhds 0) := by
    simpa [h15HighFrequencyRightEdgeRemainder,
      h15CanonicalMiddleUpperCutoff, norm_mul] using
      tendsto_norm_h15ThreeHalfHighFrequencyIntegralRemainder_polynomialCutoff_zero
        T hT
  have Hhigh : Tendsto (fun n : ℕ =>
      h15HighFrequencyRightEdgeRemainder n
        (h15CanonicalMiddleUpperCutoff n) (T n))
      atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr HhighNorm
  simpa using (Complex.continuous_im.tendsto 0).comp Hhigh

/-- The proved ultra-high tail together with two explicit signed inputs closes
the exact coupled-boundary target.  This is the non-tautological handoff for
the analytic programme: the low hypothesis preserves all corrections, and
the middle hypothesis is precisely the existing Bettin--Chandee window. -/
theorem h15CertifiedCoupledBoundaryDecay_of_lowEndpoint_of_middle
    (T : ℕ → ℝ) (hT : H15DivergingContourHeightSchedule T)
    (Hlow : H15CertifiedCorrectionCoupledLowEndpointDecay T)
    (Hmiddle : H15BettinChandeeMiddleWindowDecay T) :
    H15CertifiedCoupledBoundaryDecay := by
  have hTnonneg : ∀ n, 0 ≤ T n := fun n => (hT.positive n).le
  have HmiddleIm : Tendsto (fun n : ℕ =>
      (h15BettinChandeeMiddleFrequencyRightEdge n
        (h15CanonicalMiddleLowerCutoff n)
        (h15CanonicalMiddleWindowLength n) (T n)).im)
      atTop (nhds 0) := by
    simpa using (Complex.continuous_im.tendsto 0).comp Hmiddle
  have HhighIm : Tendsto (fun n : ℕ =>
      (h15HighFrequencyRightEdgeRemainder n
        (h15CanonicalMiddleUpperCutoff n) (T n)).im)
      atTop (nhds 0) :=
    tendsto_h15CanonicalHighFrequencyRightEdgeRemainder_im_zero T hTnonneg
  unfold H15CertifiedCoupledBoundaryDecay
  have heq : h15CertifiedCoupledBoundaryEnergy = fun n : ℕ =>
      h15CertifiedCorrectionCoupledLowEndpointSector n (T n) +
        (h15BettinChandeeMiddleFrequencyRightEdge n
          (h15CanonicalMiddleLowerCutoff n)
          (h15CanonicalMiddleWindowLength n) (T n)).im +
        (h15HighFrequencyRightEdgeRemainder n
          (h15CanonicalMiddleUpperCutoff n) (T n)).im := by
    funext n
    exact
      h15CertifiedCoupledBoundaryEnergy_eq_lowEndpoint_add_middle_add_high
        n (T n) (hTnonneg n)
  rw [heq]
  simpa using (Hlow.add HmiddleIm |>.add HhighIm)

/-- Once the finite middle window decays, the enlarged low/endpoint target is
equivalent to the complete H15 boundary target.  This is an important stop
test: the low gate has not become elementary merely because the proved high
tail was removed. -/
theorem h15CertifiedCorrectionCoupledLowEndpointDecay_iff_boundaryDecay
    (T : ℕ → ℝ) (hT : H15DivergingContourHeightSchedule T)
    (Hmiddle : H15BettinChandeeMiddleWindowDecay T) :
    H15CertifiedCorrectionCoupledLowEndpointDecay T ↔
      H15CertifiedCoupledBoundaryDecay := by
  constructor
  · intro Hlow
    exact h15CertifiedCoupledBoundaryDecay_of_lowEndpoint_of_middle
      T hT Hlow Hmiddle
  · intro Hfull
    have hTnonneg : ∀ n, 0 ≤ T n := fun n => (hT.positive n).le
    have HmiddleIm : Tendsto (fun n : ℕ =>
        (h15BettinChandeeMiddleFrequencyRightEdge n
          (h15CanonicalMiddleLowerCutoff n)
          (h15CanonicalMiddleWindowLength n) (T n)).im)
        atTop (nhds 0) := by
      simpa using (Complex.continuous_im.tendsto 0).comp Hmiddle
    have HhighIm :=
      tendsto_h15CanonicalHighFrequencyRightEdgeRemainder_im_zero T hTnonneg
    unfold H15CertifiedCorrectionCoupledLowEndpointDecay
    have heq : (fun n : ℕ =>
        h15CertifiedCorrectionCoupledLowEndpointSector n (T n)) =
        fun n : ℕ =>
          h15CertifiedCoupledBoundaryEnergy n -
            (h15BettinChandeeMiddleFrequencyRightEdge n
              (h15CanonicalMiddleLowerCutoff n)
              (h15CanonicalMiddleWindowLength n) (T n)).im -
            (h15HighFrequencyRightEdgeRemainder n
              (h15CanonicalMiddleUpperCutoff n) (T n)).im := by
      funext n
      have hsplit :=
        h15CertifiedCoupledBoundaryEnergy_eq_lowEndpoint_add_middle_add_high
          n (T n) (hTnonneg n)
      linarith
    rw [heq]
    unfold H15CertifiedCoupledBoundaryDecay at Hfull
    simpa using (Hfull.sub HmiddleIm |>.sub HhighIm)

end NBMellinTools.NB15
