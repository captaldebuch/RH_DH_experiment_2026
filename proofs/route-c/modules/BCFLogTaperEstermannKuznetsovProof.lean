import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannKuznetsovGate

/-!
# Route B8.1: the exact signed Kuznetsov proof target

This file does not assert a Kuznetsov estimate.  It packages the final target
using the kernel actually extracted from the proved two-pole contour:

* the normalized right-line dual integral;
* the left-line primal integral;
* the canonical residue at zero;
* the elementary interior terms; and
* the endpoint, linear correction, and constant.

An inhabitant must prove decay of this complete signed expression.  The
conversion to the existing Route-B closure gate is proved below, so no further
algebra or contour remainder remains after that estimate.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannKuznetsovProof

open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannAtZeroReduction
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannAtZeroBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannFiniteFourier
open RH.Criteria.NymanBeurling.BCFLogTaperBettinConreyAggregate
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannBoundaryAnalysis
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKernelExtraction
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKuznetsovGate

/-- The classical analytic part of Route B, separated from the final signed
estimate.  Constructing this package requires the local two-pole contour and
its Gaussian bounds, but does not itself assert any H15 cancellation. -/
structure H15ClassicalEstermannData where
  η : ℝ
  η_pos : 0 < η
  σL : ℝ
  σR : ℝ
  contours : H15AsymptoticGaussianContourFamilyData
    (estermannGaussianEvaluationWeight η) σL σR

/-- The single RH-strength estimate after all classical contour data have
been fixed.  The constants and their positivity are explicit bookkeeping;
`signed_bound` is the sole cancellation assertion. -/
structure SignedCorrectionCoupledKuznetsovEstimate
    (A : H15ClassicalEstermannData) where
  C : ℝ
  C_pos : 0 < C
  α : ℝ
  α_pos : 0 < α
  signed_bound : ∀ N : ℕ, 2 ≤ N →
    |estermannInteriorElementaryExpression N +
        (estermannInteriorExtractedKernelAggregate
          (estermannGaussianEvaluationWeight A.η) A.σL A.σR N).im +
        estermannEndpointCompletedExpression
          rationalAnalyticEstermannAtZeroPackage N| ≤
      C / (Real.log (N : ℝ)) ^ α

/-- All analytic contour data plus the one genuinely RH-strength signed
kernel estimate.  No instance is declared. -/
structure SignedKuznetsovProofData where
  η : ℝ
  η_pos : 0 < η
  σL : ℝ
  σR : ℝ
  contours : H15AsymptoticGaussianContourFamilyData
    (estermannGaussianEvaluationWeight η) σL σR
  C : ℝ
  C_pos : 0 < C
  α : ℝ
  α_pos : 0 < α
  signed_bound : ∀ N : ℕ, 2 ≤ N →
    |estermannInteriorElementaryExpression N +
        (estermannInteriorExtractedKernelAggregate
          (estermannGaussianEvaluationWeight η) σL σR N).im +
        estermannEndpointCompletedExpression
          rationalAnalyticEstermannAtZeroPackage N| ≤
      C / (Real.log (N : ℝ)) ^ α

/-- Recombine the publication-safe split packages into the original closure
record.  This theorem contains no analytic argument. -/
noncomputable def SignedCorrectionCoupledKuznetsovEstimate.toProofData
    {A : H15ClassicalEstermannData}
    (H : SignedCorrectionCoupledKuznetsovEstimate A) :
    SignedKuznetsovProofData where
  η := A.η
  η_pos := A.η_pos
  σL := A.σL
  σR := A.σR
  contours := A.contours
  C := H.C
  C_pos := H.C_pos
  α := H.α
  α_pos := H.α_pos
  signed_bound := H.signed_bound

/-- A genuine proof of the extracted signed estimate supplies exactly the
previous one-field Estermann/Kuznetsov closure gate. -/
noncomputable def SignedKuznetsovProofData.toSignedGate
    (H : SignedKuznetsovProofData) : SignedEstermannKuznetsovGate where
  cancellation := by
    let F : H15EvaluationContourFamily
        (estermannGaussianEvaluationWeight H.η) H.σL H.σR :=
      H.contours.toEvaluationContourFamily
    refine
      { C := H.C
        C_pos := H.C_pos
        α := H.α
        α_pos := H.α_pos
        bound := ?_ }
    intro N hN
    rw [← coupledGcdRatioExpression_eq_estermannCoupledExpression
      rationalAnalyticEstermannAtZeroPackage]
    rw [coupledGcdRatioExpression_eq_extractedKernel_add_endpoint
      rationalHurwitzZeroFormula estermannBernoulliCotangentIdentity F]
    exact H.signed_bound N hN

/-- The extracted signed theorem therefore closes the Báez--Duarte
criterion, with all dependencies visible. -/
theorem baezDuarteCriterion_of_signedKuznetsovProofData
    (H : SignedKuznetsovProofData) : BaezDuarteCriterion :=
  baezDuarteCriterion_of_signedEstermannKuznetsov H.toSignedGate

/-- Publication form of the final implication: once a classical contour
package is fixed, the one signed correction-coupled estimate implies the
Báez--Duarte criterion.  No reverse implication is asserted. -/
theorem baezDuarteCriterion_of_signedCorrectionCoupledKuznetsov
    (A : H15ClassicalEstermannData)
    (H : SignedCorrectionCoupledKuznetsovEstimate A) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_signedKuznetsovProofData H.toProofData

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannKuznetsovProof
