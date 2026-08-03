import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmPrimeDiscrepancyAbel

/-!
# Explicit-formula interface for the centered-prime high sector

The finite Abel identity is unconditional.  This module records the next
analytic layer without pretending that an ordinary pointwise bound for
`ψ(x)-x` is sufficient.  Endpoint and trivial-zero modes are kept separate
until they are recombined with the retained mean-prime correction; the
nontrivial-zero contribution is represented by its symmetric limit.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeExplicitFormula

open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmExplicitFarCutoff
open RH.Criteria.NymanBeurling.BCFLogTaperEhmHighSectorCompensation

/-- Data supplied by an exact explicit formula for the finite centered high
tail.  `symmetricZeroMode` includes its convergence convention; no termwise
absolute convergence is asserted. -/
structure EhmHighTailExplicitFormulaData where
  endpointMode : ℕ → ℕ → ℂ
  trivialZeroMode : ℕ → ℕ → ℂ
  symmetricZeroMode : ℕ → ℕ → ℂ
  decomposition : ∀ N J : ℕ, 2 ≤ N → N ≤ J →
    (ehmFiniteVonMangoldtHighCenteredTail N J : ℂ) =
      endpointMode N J + trivialZeroMode N J + symmetricZeroMode N J

/-- The elementary explicit-formula modes after the retained deterministic
completion is reattached. -/
noncomputable def ehmHighTailUnmatchedElementaryMode
    (H : EhmHighTailExplicitFormulaData) (N J : ℕ) : ℂ :=
  (ehmFiniteMeanPrimeCompletedDefect N J : ℂ) +
    H.endpointMode N J + H.trivialZeroMode N J

/-- Exact recombination of the explicit formula with the retained
mean-prime completion. -/
theorem retainedExpression_eq_elementary_add_symmetricZero
    (H : EhmHighTailExplicitFormulaData)
    (N J : ℕ) (hN : 2 ≤ N) (hNJ : N ≤ J) :
    ((ehmFiniteMeanPrimeCompletedDefect N J +
        ehmFiniteVonMangoldtHighCenteredTail N J : ℝ) : ℂ) =
      ehmHighTailUnmatchedElementaryMode H N J +
        H.symmetricZeroMode N J := by
  push_cast
  rw [H.decomposition N J hN hNJ]
  unfold ehmHighTailUnmatchedElementaryMode
  ring

/-- The genuine Route B input.  The elementary modes and symmetric zero
aggregate remain under one norm; bounding them separately is deliberately
not part of this interface. -/
structure EhmHighTailSignedZeroCancellation
    (H : EhmHighTailExplicitFormulaData) where
  C : ℝ
  C_nonneg : 0 ≤ C
  coupled_bound : ∀ X N J : ℕ, 2 ≤ X →
    N ∈ ehmDyadicNBlock X → ehmExplicitFarCutoff X ≤ J →
    ‖ehmHighTailUnmatchedElementaryMode H N J +
        H.symmetricZeroMode N J‖ ≤ C / (N : ℝ)

/-- A signed explicit-formula estimate discharges the already isolated
centered-prime compensation interface. -/
noncomputable def EhmHighTailSignedZeroCancellation.toCenteredPrime
    {H : EhmHighTailExplicitFormulaData}
    (HZ : EhmHighTailSignedZeroCancellation H) :
    EhmRetainedCorrectionCenteredPrimeCompensationBound where
  C := HZ.C
  C_nonneg := HZ.C_nonneg
  coupled_bound X N J hX hN hJ := by
    have hNtwo : 2 ≤ N := hX.trans (Finset.mem_Icc.mp hN).1
    have hNJ : N ≤ J :=
      (Finset.mem_Icc.mp hN).2.trans
        ((two_mul_le_ehmExplicitFarCutoff X).trans hJ)
    have hid := retainedExpression_eq_elementary_add_symmetricZero
      H N J hNtwo hNJ
    rw [← Real.norm_eq_abs]
    rw [← Complex.norm_real]
    rw [hid]
    exact HZ.coupled_bound X N J hX hN hJ

end RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeExplicitFormula
