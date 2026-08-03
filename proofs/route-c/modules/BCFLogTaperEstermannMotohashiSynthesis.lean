import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannBilinearTraceTarget
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannKuznetsovProof
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiPhysicalCorrection

/-!
# Motohashi/Poincare synthesis interface for the H15 bilinear trace target

Ordinary Kuznetsov accepts fixed arithmetic frequencies and a test function
depending on the summed modulus.  The completed H15 coefficient instead
contains the joint inverse phase `e_q(-m*a⁻¹)`.  Motohashi's more general
Poincare-series framework is structurally capable of starting from a seed on
the big Bruhat cell, but applying it to H15 requires several distinct facts.

This file keeps those facts separate:

1. the extracted contour kernel must split into the physical zero-corrected
   bilinear aggregate and its primal/residue completion;
2. that aggregate must admit a Poincare/automorphic trace decomposition;
3. the arithmetic main term and physical completion must jointly match the
   retained elementary and endpoint correction; and
4. the complete signed cuspidal-plus-continuous remainder must decay.

The first three fields are identity/normalization obligations.  The fourth is
the RH-strength analytic estimate.  No instance of either structure is
declared here.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiSynthesis

open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannAtZeroReduction
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannBilinearTraceTarget
open RH.Criteria.NymanBeurling.BCFLogTaperBettinConreyAggregate
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKernelExtraction
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKuznetsovGate
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKuznetsovProof
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiPhysicalCorrection
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiSeed

/-- The complete real expression occurring in the existing signed Route-B
target, with the classical contour data fixed by `A`. -/
noncomputable def h15MotohashiCompletedExpression
    (A : H15ClassicalEstermannData) (N : ℕ) : ℝ :=
  estermannInteriorElementaryExpression N +
    (estermannInteriorExtractedKernelAggregate
      (estermannGaussianEvaluationWeight A.η) A.σL A.σR N).im +
    estermannEndpointCompletedExpression
      rationalAnalyticEstermannAtZeroPackage N

/-- The analytic realization still required after the exact finite seed
unfolding.  `orbital_summable` prevents Lean's totalized `tsum` from hiding a
divergent series.  `physical_decomposition` is the inverse-Mellin/line-shift
identity relating the extracted contour kernel to the canonical arithmetic
seed aggregate and its retained primal/residue correction. -/
structure H15MotohashiSeedAdmissibilityData
    (A : H15ClassicalEstermannData) where
  c : ℝ
  c_gt_one : 1 < c
  orbital_summable : ∀ (N g q : ℕ) [NeZero q]
      (sign : H15MotohashiSign),
    Summable (fun n : ℕ =>
      ∑ m : ZMod q, h15MotohashiArithmeticSeed
        N g q sign A.η c n m)
  physicalCorrection : ℕ → ℂ
  physical_decomposition : ∀ N : ℕ,
    (estermannInteriorExtractedKernelAggregate
      (estermannGaussianEvaluationWeight A.η) A.σL A.σR N) =
        h15MotohashiArithmeticSeedAggregate N A.η c / Real.pi +
          physicalCorrection N

/-- After the summability theorem in BT1-A, the sole remaining physical-seed
input is the contour-line realization itself. -/
structure H15MotohashiPhysicalRealizationData
    (A : H15ClassicalEstermannData) where
  c : ℝ
  c_gt_one : 1 < c
  physicalCorrection : ℕ → ℂ
  physical_decomposition : ∀ N : ℕ,
    (estermannInteriorExtractedKernelAggregate
      (estermannGaussianEvaluationWeight A.η) A.σL A.σR N) =
        h15MotohashiArithmeticSeedAggregate N A.η c / Real.pi +
          physicalCorrection N

/-- BT1-B supplies the physical realization canonically.  The right contour
line is read from the classical contour family, while the correction is the
explicit left-line-plus-zero-residue aggregate. -/
noncomputable def h15ClassicalMotohashiPhysicalRealization
    (A : H15ClassicalEstermannData) :
    H15MotohashiPhysicalRealizationData A where
  c := A.σR
  c_gt_one :=
    (A.contours.data 1 2 (by norm_num) (by norm_num)).right_of_one
  physicalCorrection N :=
    h15MotohashiExplicitPhysicalCorrection
      (estermannGaussianEvaluationWeight A.η) A.σL N
  physical_decomposition N :=
    estermannInteriorExtractedKernelAggregate_eq_seed_div_pi_add_correction
      N A.η A.σL A.σR A.η_pos
        (A.contours.data 1 2 (by norm_num) (by norm_num)).right_of_one

/-- Gaussian summability discharges the analytic-series field automatically;
only a genuine physical contour realization must be supplied. -/
noncomputable def H15MotohashiPhysicalRealizationData.toSeedAdmissibility
    {A : H15ClassicalEstermannData}
    (P : H15MotohashiPhysicalRealizationData A) :
    H15MotohashiSeedAdmissibilityData A where
  c := P.c
  c_gt_one := P.c_gt_one
  orbital_summable N g q _ sign :=
    h15MotohashiArithmeticSeed_orbit_summable
      N g q sign A.η P.c A.η_pos P.c_gt_one
  physicalCorrection := P.physicalCorrection
  physical_decomposition := P.physical_decomposition

/-- All seed summability and physical contour-realization obligations are
therefore discharged by the existing classical Gaussian contour package. -/
noncomputable def h15ClassicalMotohashiSeedAdmissibility
    (A : H15ClassicalEstermannData) :
    H15MotohashiSeedAdmissibilityData A :=
  (h15ClassicalMotohashiPhysicalRealization A).toSeedAdmissibility

/-- The Motohashi trace and correction obligations after admissibility and
physical realization have been separated out.  The trace is asserted only
for the canonical seed aggregate proved in BT1-A. -/
structure H15MotohashiAutomorphicTraceData
    {A : H15ClassicalEstermannData}
    (S : H15MotohashiSeedAdmissibilityData A) where
  arithmeticMain : ℕ → ℝ
  cuspidalPart : ℕ → ℝ
  continuousRemainder : ℕ → ℝ
  poincare_trace : ∀ N : ℕ,
    (h15MotohashiArithmeticSeedAggregate N A.η S.c / Real.pi).im =
      arithmeticMain N + cuspidalPart N + continuousRemainder N
  correction_matching : ∀ N : ℕ,
    estermannInteriorElementaryExpression N + arithmeticMain N +
      (S.physicalCorrection N).im +
      estermannEndpointCompletedExpression
        rationalAnalyticEstermannAtZeroPackage N = 0

/-- The exact literature-synthesis data needed before a spectral estimate
can be invoked.

`physical_realization` is the remaining line-shift/inverse-Mellin bridge.
`poincare_trace` is the Motohashi-style geometric-to-spectral identity.
`correction_matching` requires the trace main term to cancel the elementary
and endpoint terms exactly. -/
structure H15MotohashiPoincareTraceData
    (A : H15ClassicalEstermannData) where
  c : ℝ
  c_gt_one : 1 < c
  arithmeticMain : ℕ → ℝ
  cuspidalPart : ℕ → ℝ
  continuousRemainder : ℕ → ℝ
  physicalCorrection : ℕ → ℂ
  physical_realization : ∀ N : ℕ,
    (estermannInteriorExtractedKernelAggregate
      (estermannGaussianEvaluationWeight A.η) A.σL A.σR N).im =
        (h15InteriorZeroCorrectedBilinearKernelAggregate
          N A.η c / Real.pi).im + (physicalCorrection N).im
  poincare_trace : ∀ N : ℕ,
    (h15InteriorZeroCorrectedBilinearKernelAggregate
      N A.η c / Real.pi).im =
      arithmeticMain N + cuspidalPart N + continuousRemainder N
  correction_matching : ∀ N : ℕ,
    estermannInteriorElementaryExpression N + arithmeticMain N +
      (physicalCorrection N).im +
      estermannEndpointCompletedExpression
        rationalAnalyticEstermannAtZeroPackage N = 0

/-- Exact completion-aware reduction for the canonical seed.  The primal-line
and residue completion remains inside `physicalCorrection` until it is matched
with the arithmetic main term and retained H15 correction. -/
theorem h15MotohashiCompletedExpression_eq_signedSpectralRemainder_of_seedTrace
    {A : H15ClassicalEstermannData}
    {S : H15MotohashiSeedAdmissibilityData A}
    (T : H15MotohashiAutomorphicTraceData S) (N : ℕ) :
    h15MotohashiCompletedExpression A N =
      T.cuspidalPart N + T.continuousRemainder N := by
  unfold h15MotohashiCompletedExpression
  rw [S.physical_decomposition N]
  simp only [Complex.add_im]
  rw [T.poincare_trace N]
  calc
    estermannInteriorElementaryExpression N +
          (T.arithmeticMain N + T.cuspidalPart N +
            T.continuousRemainder N + (S.physicalCorrection N).im) +
          estermannEndpointCompletedExpression
            rationalAnalyticEstermannAtZeroPackage N =
        (estermannInteriorElementaryExpression N + T.arithmeticMain N +
          (S.physicalCorrection N).im +
          estermannEndpointCompletedExpression
            rationalAnalyticEstermannAtZeroPackage N) +
          (T.cuspidalPart N + T.continuousRemainder N) := by ring
    _ = T.cuspidalPart N + T.continuousRemainder N := by
      rw [T.correction_matching N]
      ring

/-- Once the physical realization, trace formula, and correction matching
are available, the original completed H15 expression is exactly the signed
cuspidal-plus-continuous remainder.  No triangle inequality is used. -/
theorem h15MotohashiCompletedExpression_eq_signedSpectralRemainder
    {A : H15ClassicalEstermannData}
    (T : H15MotohashiPoincareTraceData A) (N : ℕ) :
    h15MotohashiCompletedExpression A N =
      T.cuspidalPart N + T.continuousRemainder N := by
  unfold h15MotohashiCompletedExpression
  rw [T.physical_realization N, T.poincare_trace N]
  calc
    estermannInteriorElementaryExpression N +
          (T.arithmeticMain N + T.cuspidalPart N +
            T.continuousRemainder N + (T.physicalCorrection N).im) +
          estermannEndpointCompletedExpression
            rationalAnalyticEstermannAtZeroPackage N =
        (estermannInteriorElementaryExpression N + T.arithmeticMain N +
          (T.physicalCorrection N).im +
          estermannEndpointCompletedExpression
            rationalAnalyticEstermannAtZeroPackage N) +
          (T.cuspidalPart N + T.continuousRemainder N) := by ring
    _ = T.cuspidalPart N + T.continuousRemainder N := by
      rw [T.correction_matching N]
      ring

/-- The sole decay input after the Motohashi trace and correction identities
have been established.  The two spectral pieces remain coupled inside one
absolute value. -/
structure H15MotohashiSignedSpectralEstimate
    {A : H15ClassicalEstermannData}
    (T : H15MotohashiPoincareTraceData A) where
  C : ℝ
  C_pos : 0 < C
  α : ℝ
  α_pos : 0 < α
  signed_spectral_bound : ∀ N : ℕ, 2 ≤ N →
    |T.cuspidalPart N + T.continuousRemainder N| ≤
      C / (Real.log (N : ℝ)) ^ α

/-- The corresponding signed estimate for the canonical completion-aware
seed trace. -/
structure H15MotohashiAutomorphicSignedSpectralEstimate
    {A : H15ClassicalEstermannData}
    {S : H15MotohashiSeedAdmissibilityData A}
    (T : H15MotohashiAutomorphicTraceData S) where
  C : ℝ
  C_pos : 0 < C
  α : ℝ
  α_pos : 0 < α
  signed_spectral_bound : ∀ N : ℕ, 2 ≤ N →
    |T.cuspidalPart N + T.continuousRemainder N| ≤
      C / (Real.log (N : ℝ)) ^ α

/-- The completion-aware seed synthesis populates the existing Route-B
signed estimate without discarding the primal/residue correction. -/
noncomputable def H15MotohashiAutomorphicSignedSpectralEstimate.toSignedEstimate
    {A : H15ClassicalEstermannData}
    {S : H15MotohashiSeedAdmissibilityData A}
    {T : H15MotohashiAutomorphicTraceData S}
    (H : H15MotohashiAutomorphicSignedSpectralEstimate T) :
    SignedCorrectionCoupledKuznetsovEstimate A where
  C := H.C
  C_pos := H.C_pos
  α := H.α
  α_pos := H.α_pos
  signed_bound N hN := by
    change |h15MotohashiCompletedExpression A N| ≤
      H.C / (Real.log (N : ℝ)) ^ H.α
    rw [h15MotohashiCompletedExpression_eq_signedSpectralRemainder_of_seedTrace
      T N]
    exact H.signed_spectral_bound N hN

/-- The four Motohashi synthesis obligations construct exactly the existing
signed correction-coupled Kuznetsov estimate. -/
noncomputable def H15MotohashiSignedSpectralEstimate.toSignedEstimate
    {A : H15ClassicalEstermannData}
    {T : H15MotohashiPoincareTraceData A}
    (H : H15MotohashiSignedSpectralEstimate T) :
    SignedCorrectionCoupledKuznetsovEstimate A where
  C := H.C
  C_pos := H.C_pos
  α := H.α
  α_pos := H.α_pos
  signed_bound N hN := by
    change |h15MotohashiCompletedExpression A N| ≤
      H.C / (Real.log (N : ℝ)) ^ H.α
    rw [h15MotohashiCompletedExpression_eq_signedSpectralRemainder T N]
    exact H.signed_spectral_bound N hN

/-- Consequently the completed Motohashi synthesis closes the existing
Báez-Duarte criterion pipeline.  This theorem is conditional on the explicit
proof-carrying structures above and introduces no axiom. -/
theorem baezDuarteCriterion_of_motohashiSynthesis
    (A : H15ClassicalEstermannData)
    (T : H15MotohashiPoincareTraceData A)
    (H : H15MotohashiSignedSpectralEstimate T) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_signedCorrectionCoupledKuznetsov
    A H.toSignedEstimate

/-- Completion-aware canonical-seed version of the final reduction. -/
theorem baezDuarteCriterion_of_motohashiSeedSynthesis
    (A : H15ClassicalEstermannData)
    (S : H15MotohashiSeedAdmissibilityData A)
    (T : H15MotohashiAutomorphicTraceData S)
    (H : H15MotohashiAutomorphicSignedSpectralEstimate T) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_signedCorrectionCoupledKuznetsov
    A H.toSignedEstimate

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiSynthesis
