import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannKloosterman

/-!
# Route B8.3: the exact two-sign spectral proof target

The normalized Estermann dual value contains both positive and negative
outer frequencies.  A valid Kuznetsov bridge must therefore retain a
same-sign term, an opposite-sign term, and the diagonal/continuous spectral
remainder.  This file packages that exact decomposition separately from the
question whether the spectral remainder reproduces the elementary and
endpoint-completed H15 correction.

The final assembly theorem is proved.  No inverse-Mellin identity, trace
formula, correction match, or decay estimate is asserted.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannTwoSignTarget

open RH.Criteria.NymanBeurling.BCFLogTaperEstermannAtZeroBridge
open RH.Criteria.NymanBeurling.BCFLogTaperBettinConreyAggregate
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKernelExtraction
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKuznetsovGate
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKuznetsovProof

/-- Exact output expected from inverse Mellin followed by the two signs of
the Kuznetsov formula.  `spectralRemainder` includes every diagonal and
continuous-spectrum contribution; none may be discarded. -/
structure TwoSignKuznetsovDecomposition
    (A : H15ClassicalEstermannData) where
  sameSign : ℕ → ℝ
  oppositeSign : ℕ → ℝ
  spectralRemainder : ℕ → ℝ
  kernel_identity : ∀ N : ℕ,
    (estermannInteriorExtractedKernelAggregate
      (estermannGaussianEvaluationWeight A.η) A.σL A.σR N).im =
      sameSign N + oppositeSign N + spectralRemainder N

/-- The correction-comparison problem after the trace formula.  It records
exactly what remains when the spectral diagonal/continuous part is combined
with the elementary and endpoint-completed H15 terms. -/
structure SpectralCorrectionMatching
    (A : H15ClassicalEstermannData)
    (D : TwoSignKuznetsovDecomposition A) where
  correctionRemainder : ℕ → ℝ
  matching_identity : ∀ N : ℕ,
    estermannInteriorElementaryExpression N + D.spectralRemainder N +
        estermannEndpointCompletedExpression
          rationalAnalyticEstermannAtZeroPackage N =
      correctionRemainder N

/-- The signed estimate which remains after the exact kernel decomposition
and correction comparison.  This still permits cancellation between the two
Kuznetsov signs and the unmatched correction remainder. -/
structure SignedTwoSignKuznetsovEstimate
    {A : H15ClassicalEstermannData}
    (D : TwoSignKuznetsovDecomposition A)
    (M : SpectralCorrectionMatching A D) where
  C : ℝ
  C_pos : 0 < C
  α : ℝ
  α_pos : 0 < α
  bound : ∀ N : ℕ, 2 ≤ N →
    |D.sameSign N + D.oppositeSign N + M.correctionRemainder N| ≤
      C / (Real.log (N : ℝ)) ^ α

/-- Exact assembly of the two-sign spectral route.  The proof is only ring
reassociation plus the two supplied identities; in particular it introduces
no analytic remainder of its own. -/
noncomputable def SignedTwoSignKuznetsovEstimate.toCorrectionCoupledEstimate
    {A : H15ClassicalEstermannData}
    {D : TwoSignKuznetsovDecomposition A}
    {M : SpectralCorrectionMatching A D}
    (H : SignedTwoSignKuznetsovEstimate D M) :
    SignedCorrectionCoupledKuznetsovEstimate A where
  C := H.C
  C_pos := H.C_pos
  α := H.α
  α_pos := H.α_pos
  signed_bound := by
    intro N hN
    rw [D.kernel_identity N]
    calc
      |estermannInteriorElementaryExpression N +
          (D.sameSign N + D.oppositeSign N + D.spectralRemainder N) +
          estermannEndpointCompletedExpression
            rationalAnalyticEstermannAtZeroPackage N| =
        |D.sameSign N + D.oppositeSign N +
          (estermannInteriorElementaryExpression N +
            D.spectralRemainder N +
            estermannEndpointCompletedExpression
              rationalAnalyticEstermannAtZeroPackage N)| := by ring
      _ = |D.sameSign N + D.oppositeSign N +
          M.correctionRemainder N| := by rw [M.matching_identity N]
      _ ≤ H.C / (Real.log (N : ℝ)) ^ H.α := H.bound N hN

/-- Consequently the exact two-sign route implies the Báez--Duarte
criterion.  This is a one-way conditional theorem. -/
theorem baezDuarteCriterion_of_twoSignKuznetsov
    (A : H15ClassicalEstermannData)
    (D : TwoSignKuznetsovDecomposition A)
    (M : SpectralCorrectionMatching A D)
    (H : SignedTwoSignKuznetsovEstimate D M) :
    RH.Criteria.NymanBeurling.BaezDuarte.BaezDuarteCriterion :=
  baezDuarteCriterion_of_signedCorrectionCoupledKuznetsov A
    H.toCorrectionCoupledEstimate

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannTwoSignTarget
