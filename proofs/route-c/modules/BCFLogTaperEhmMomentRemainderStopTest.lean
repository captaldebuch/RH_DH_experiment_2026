import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmMacLeod
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmRetainedCorrectionAudit

/-!
# Raw-moment stop test for the retained Ehm correction

The small-cutoff diagnostic suggested that Ehm's four-moment remainder might
itself be inverse-linear.  A scalable diagnostic rejects that separated
route.  This file records the exact six-raw-moment normal form and then
restores the only analytically valid target: the finite von-Mangoldt main and
the moment normal form remain inside one absolute value.

All results here are finite identities and implications.  No sign or decay
estimate for the moment remainder is asserted.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmMomentRemainderStopTest

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmBoundaryResearch
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmExplicitFarCutoff
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRetainedCorrectionAudit

/-! ## Six raw moments -/

/-- Log-tapered zeroth Mertens moment in raw-prefix coordinates. -/
noncomputable def ehmRawTaperedM0 (N : ℕ) : ℝ :=
  rawMobiusMoment 0 N - rawMobiusMoment 1 N / Real.log N

/-- Log-tapered first Mertens moment in raw-prefix coordinates. -/
noncomputable def ehmRawTaperedM1 (N : ℕ) : ℝ :=
  rawMobiusMoment 1 N - rawMobiusMoment 2 N / Real.log N

/-- Log-tapered zeroth harmonic moment in raw-prefix coordinates. -/
noncomputable def ehmRawTaperedL0 (N : ℕ) : ℝ :=
  rawMobiusHarmonicMoment 0 N -
    rawMobiusHarmonicMoment 1 N / Real.log N

/-- Log-tapered first harmonic moment in raw-prefix coordinates. -/
noncomputable def ehmRawTaperedL1 (N : ℕ) : ℝ :=
  rawMobiusHarmonicMoment 1 N -
    rawMobiusHarmonicMoment 2 N / Real.log N

theorem ehmRawTaperedM0_eq_ehmM (N : ℕ) (hN : 2 ≤ N) :
    ehmRawTaperedM0 N = ehmM 0 N := by
  simpa [ehmRawTaperedM0] using (ehmM_eq_rawMobiusMoments 0 N hN).symm

theorem ehmRawTaperedM1_eq_ehmM (N : ℕ) (hN : 2 ≤ N) :
    ehmRawTaperedM1 N = ehmM 1 N := by
  simpa [ehmRawTaperedM1] using (ehmM_eq_rawMobiusMoments 1 N hN).symm

theorem ehmRawTaperedL0_eq_ehmL (N : ℕ) (hN : 2 ≤ N) :
    ehmRawTaperedL0 N = ehmL 0 N := by
  simpa [ehmRawTaperedL0] using
    (ehmL_eq_rawMobiusHarmonicMoments 0 N hN).symm

theorem ehmRawTaperedL1_eq_ehmL (N : ℕ) (hN : 2 ≤ N) :
    ehmRawTaperedL1 N = ehmL 1 N := by
  simpa [ehmRawTaperedL1] using
    (ehmL_eq_rawMobiusHarmonicMoments 1 N hN).symm

/-- The four-moment correction displayed entirely through the six raw
Möbius prefix sums of log-degrees zero, one, and two. -/
noncomputable def ehmMomentRemainderRawNormalForm (N : ℕ) : ℝ :=
  ehmRawTaperedL1 N +
      (1 - Real.eulerMascheroniConstant) * ehmRawTaperedL0 N + 1 +
    ehmRawTaperedM0 N *
      (ehmK * ehmRawTaperedL0 N + (ehmRawTaperedL1 N + 1) / 2) -
    (ehmRawTaperedM1 N * ehmRawTaperedL0 N) / 2

/-- Exact raw-moment normal form of Ehm's coupled remainder. -/
theorem ehmMomentRemainderRawNormalForm_eq_coupledRemainder
    (N : ℕ) (hN : 2 ≤ N) :
    ehmMomentRemainderRawNormalForm N = ehmCoupledRemainder N := by
  unfold ehmMomentRemainderRawNormalForm ehmCoupledRemainder
  rw [ehmRawTaperedM0_eq_ehmM N hN,
    ehmRawTaperedM1_eq_ehmM N hN,
    ehmRawTaperedL0_eq_ehmL N hN,
    ehmRawTaperedL1_eq_ehmL N hN]

/-! ## Corrected compensation target -/

/-- The raw-moment form is not estimated separately.  It is recombined with
the complete finite von-Mangoldt transform at the same outer cutoff. -/
noncomputable def ehmFiniteMainMomentCompensationDefect
    (R1 : ℝ → ℝ) (N J : ℕ) : ℝ :=
  ehmFiniteFullVonMangoldtTransformOuter R1 N J +
    ehmMomentRemainderRawNormalForm N

/-- The corrected main--moment defect is exactly the indivisible retained
correction summand from the outer-cutoff audit. -/
theorem ehmFiniteMainMomentCompensationDefect_eq_retainedSummand
    (R1 : ℝ → ℝ) (N J : ℕ) (hN : 2 ≤ N) :
    ehmFiniteMainMomentCompensationDefect R1 N J =
      ehmFiniteRetainedCorrectionSummand R1 N J := by
  unfold ehmFiniteMainMomentCompensationDefect
    ehmFiniteRetainedCorrectionSummand
  rw [ehmMomentRemainderRawNormalForm_eq_coupledRemainder N hN]

/-- The validated inverse-cutoff research target.  Unlike the numerically
rejected remainder-only route, the finite main and all six raw moments remain
coupled inside the absolute value. -/
structure EhmRetainedCorrectionMainMomentInverseCutoffBound where
  C : ℝ
  C_nonneg : 0 ≤ C
  coupled_bound : ∀ X N J : ℕ, 2 ≤ X →
    N ∈ ehmDyadicNBlock X → ehmExplicitFarCutoff X ≤ J →
    |ehmFiniteMainMomentCompensationDefect ehmR1 N J| ≤ C / (N : ℝ)

/-- The explicit main--moment target instantiates the generic retained
correction inverse-cutoff package. -/
noncomputable def
    EhmRetainedCorrectionMainMomentInverseCutoffBound.toInverseCutoff
    (H : EhmRetainedCorrectionMainMomentInverseCutoffBound) :
    EhmRetainedCorrectionInverseCutoffBound where
  C := H.C
  C_nonneg := H.C_nonneg
  pointwise_bound X N J hX hN hJ := by
    rw [← ehmFiniteMainMomentCompensationDefect_eq_retainedSummand
      ehmR1 N J (hX.trans (Finset.mem_Icc.mp hN).1)]
    exact H.coupled_bound X N J hX hN hJ

/-- Consequently, a proof of the corrected coupled target supplies the
uniform signed correction estimate with normalized rate `C / X`. -/
noncomputable def
    EhmRetainedCorrectionMainMomentInverseCutoffBound.toSignedSublinear
    (H : EhmRetainedCorrectionMainMomentInverseCutoffBound) :
    EhmRetainedCorrectionSignedSublinearBound :=
  H.toInverseCutoff.toOuterL1.toSigned

end RH.Criteria.NymanBeurling.BCFLogTaperEhmMomentRemainderStopTest
