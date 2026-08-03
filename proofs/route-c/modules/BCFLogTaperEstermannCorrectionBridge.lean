import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannKloostermanCompletion
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannTwoSignTarget

/-!
# Route B8.7: explicit correction bridge after Kloosterman completion

The finite completion exposes a degenerate zero mode.  A trace formula then
adds a diagonal and an Eisenstein contribution.  This module prevents those
pieces from being hidden inside an unnamed spectral remainder: it gives each
one a field and proves the formal passage to the existing two-sign H15 target.

The correction identity itself remains a field.  In particular, this file
does **not** assert that the zero mode and Eisenstein spectrum reproduce
`2 L_N + 1`; proving the displayed `correction_identity` is the remaining
analytic bookkeeping problem before the final signed estimate.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannCorrectionBridge

open RH.Criteria.NymanBeurling.BCFLogTaperEstermannAtZeroBridge
open RH.Criteria.NymanBeurling.BCFLogTaperBettinConreyAggregate
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKernelExtraction
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKuznetsovGate
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKuznetsovProof
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannTwoSignTarget

/-- Fully separated output expected from the two Kloosterman trace formulas.
`zeroMode` is the aggregate of the `m=0` Ramanujan terms from finite
completion.  `remainingSpectrum` includes any term not belonging to the
named cusp, diagonal, or Eisenstein sectors. -/
structure CompletedKuznetsovDecomposition
    (A : H15ClassicalEstermannData) where
  sameSign : ℕ → ℝ
  oppositeSign : ℕ → ℝ
  zeroMode : ℕ → ℝ
  diagonal : ℕ → ℝ
  eisenstein : ℕ → ℝ
  remainingSpectrum : ℕ → ℝ
  kernel_identity : ∀ N : ℕ,
    (estermannInteriorExtractedKernelAggregate
      (estermannGaussianEvaluationWeight A.η) A.σL A.σR N).im =
      sameSign N + oppositeSign N + zeroMode N + diagonal N +
        eisenstein N + remainingSpectrum N

/-- Forgetting the internal spectral split recovers the exact interface
already consumed by the H15 assembly theorem. -/
noncomputable def CompletedKuznetsovDecomposition.toTwoSign
    {A : H15ClassicalEstermannData}
    (D : CompletedKuznetsovDecomposition A) :
    TwoSignKuznetsovDecomposition A where
  sameSign := D.sameSign
  oppositeSign := D.oppositeSign
  spectralRemainder := fun N =>
    D.zeroMode N + D.diagonal N + D.eisenstein N + D.remainingSpectrum N
  kernel_identity := by
    intro N
    rw [D.kernel_identity N]
    ring

/-- Exact correction bookkeeping after the zero, diagonal, Eisenstein, and
remaining spectral terms have all been exposed.  The remainder is retained
inside the final signed estimate rather than bounded termwise. -/
structure CompletedSpectralCorrectionMatching
    {A : H15ClassicalEstermannData}
    (D : CompletedKuznetsovDecomposition A) where
  correctionRemainder : ℕ → ℝ
  correction_identity : ∀ N : ℕ,
    estermannInteriorElementaryExpression N + D.zeroMode N + D.diagonal N +
        D.eisenstein N + D.remainingSpectrum N +
        estermannEndpointCompletedExpression
          rationalAnalyticEstermannAtZeroPackage N =
      correctionRemainder N

/-- The explicit componentwise correction bridge supplies the previous
spectral-correction interface with no loss or extra remainder. -/
noncomputable def CompletedSpectralCorrectionMatching.toSpectralMatching
    {A : H15ClassicalEstermannData}
    {D : CompletedKuznetsovDecomposition A}
    (M : CompletedSpectralCorrectionMatching D) :
    SpectralCorrectionMatching A D.toTwoSign where
  correctionRemainder := M.correctionRemainder
  matching_identity := by
    intro N
    change
      estermannInteriorElementaryExpression N +
          (D.zeroMode N + D.diagonal N + D.eisenstein N +
            D.remainingSpectrum N) +
          estermannEndpointCompletedExpression
            rationalAnalyticEstermannAtZeroPackage N =
        M.correctionRemainder N
    calc
      estermannInteriorElementaryExpression N +
          (D.zeroMode N + D.diagonal N + D.eisenstein N +
            D.remainingSpectrum N) +
          estermannEndpointCompletedExpression
            rationalAnalyticEstermannAtZeroPackage N =
        estermannInteriorElementaryExpression N + D.zeroMode N +
          D.diagonal N + D.eisenstein N + D.remainingSpectrum N +
          estermannEndpointCompletedExpression
            rationalAnalyticEstermannAtZeroPackage N := by ring
      _ = M.correctionRemainder N := M.correction_identity N

/-- A decay estimate for the two cusp signs coupled to the fully exposed
correction remainder is exactly the existing final signed estimate. -/
noncomputable def signedTwoSignEstimate_of_completed
    {A : H15ClassicalEstermannData}
    {D : CompletedKuznetsovDecomposition A}
    (M : CompletedSpectralCorrectionMatching D)
    (C α : ℝ) (C_pos : 0 < C) (α_pos : 0 < α)
    (bound : ∀ N : ℕ, 2 ≤ N →
      |D.sameSign N + D.oppositeSign N + M.correctionRemainder N| ≤
        C / (Real.log (N : ℝ)) ^ α) :
    SignedTwoSignKuznetsovEstimate D.toTwoSign M.toSpectralMatching where
  C := C
  C_pos := C_pos
  α := α
  α_pos := α_pos
  bound := bound

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannCorrectionBridge
