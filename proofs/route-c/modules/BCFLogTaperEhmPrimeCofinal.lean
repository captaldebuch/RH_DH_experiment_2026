import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCorrectionMatching
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmSignedAverage

/-!
# Completed explicit prime profiles at the cofinal H15 strength

The explicit-formula profile constructed in
`BCFLogTaperEhmPrimeCorrectionMatching` represents the retained
von-Mangoldt--moment summand.  The finite hyperbolic boundary contains one
additional signed term: the missing-divisor tail.  Thus the exact finite H15
object is

`natural defect + completed profile transport - missing-divisor tail`.

This module proves that identity and transports it to the weakest existing
double-cofinal and signed-dyadic H15 interfaces.  In particular, none of the
endpoint, trivial-zero, symmetric-zero, moment, or missing-divisor terms is
estimated separately.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCofinal

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmBoundaryResearch
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmHighSectorCompensation
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMacLeodCompensation
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCorrectionMatching
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRetainedCorrectionAudit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmSignedAverage
open RH.Criteria.NymanBeurling.BCFLogTaperEhmUniformBoundary

/-- The completed explicit-formula profile in the exact finite hyperbolic
boundary normalization.  The missing-divisor term retains its original minus
sign and stays under the same norm as every explicit-formula mode. -/
noncomputable def ehmPrimeCompletedBoundaryProfile
    (H : EhmPrimeDiscrepancyExplicitModeData) (N J : ℕ) : ℂ :=
  (ehmFiniteNaturalCutoffDefect N : ℂ) +
    ehmPrimeHighAggregateMode (ehmPrimeCompletedExplicitProfile H) N J -
      (ehmFiniteMissingDivisorTailOuter ehmR1 N J : ℂ)

/-- The completed profile before the missing-divisor subtraction is exactly
the retained correction summand. -/
theorem ofReal_ehmFiniteRetainedCorrectionSummand_eq_completedProfile
    (H : EhmPrimeDiscrepancyExplicitModeData)
    (N J : ℕ) (hN : 2 ≤ N) (hNJ : N ≤ J) :
    (ehmFiniteRetainedCorrectionSummand ehmR1 N J : ℂ) =
      (ehmFiniteNaturalCutoffDefect N : ℂ) +
        ehmPrimeHighAggregateMode
          (ehmPrimeCompletedExplicitProfile H) N J := by
  rw [← ehmFiniteMacLeodCompensationDefect_eq_retainedSummand
    ehmR1 N J hN]
  rw [ehmFiniteMacLeodCompensationDefect_eq_meanPrime_add_centered
    N J hN hNJ]
  exact retainedExpression_eq_natural_add_completedProfile H N J hN hNJ

/-- Exact finite bridge.  This is the identity needed before any cofinal
estimate may be transferred to H15. -/
theorem ofReal_ehmFiniteCoupledBoundaryExpression_eq_completedBoundaryProfile
    (H : EhmPrimeDiscrepancyExplicitModeData)
    (N J : ℕ) (hN : 2 ≤ N) (hNJ : N ≤ J) :
    (ehmFiniteCoupledBoundaryExpression ehmR1 N J : ℂ) =
      ehmPrimeCompletedBoundaryProfile H N J := by
  rw [ehmFiniteCoupledBoundaryExpression_eq_fullOuter_sub_missing_add_remainder
    ehmR1 N J hN hNJ]
  have hret :=
    ofReal_ehmFiniteRetainedCorrectionSummand_eq_completedProfile
      H N J hN hNJ
  unfold ehmFiniteRetainedCorrectionSummand at hret
  unfold ehmPrimeCompletedBoundaryProfile
  push_cast at hret ⊢
  linear_combination hret

/-- Real-part version of the exact finite bridge, convenient for signed
outer-cutoff averaging. -/
theorem completedBoundaryProfile_re
    (H : EhmPrimeDiscrepancyExplicitModeData)
    (N J : ℕ) (hN : 2 ≤ N) (hNJ : N ≤ J) :
    (ehmPrimeCompletedBoundaryProfile H N J).re =
      ehmFiniteCoupledBoundaryExpression ehmR1 N J := by
  rw [← ofReal_ehmFiniteCoupledBoundaryExpression_eq_completedBoundaryProfile
    H N J hN hNJ]
  simp

/-! ## Double-cofinal formulation -/

/-- The weakest completed-profile target: choose arbitrarily large outer
cutoffs `N`, and require smallness only at cofinally many hyperbolic cutoffs.
Every correction and explicit-formula mode remains inside one complex norm. -/
structure EhmCompletedProfileDoubleCofinalVanishing
    (H : EhmPrimeDiscrepancyExplicitModeData) where
  cofinally_small : ∀ ε : ℝ, 0 < ε → ∀ N₀ : ℕ,
    ∃ N : ℕ, N₀ ≤ N ∧ 2 ≤ N ∧
      ∃ᶠ J : ℕ in atTop,
        ‖ehmPrimeCompletedBoundaryProfile H N J‖ < ε

/-- Completed-profile double-cofinal cancellation gives exactly the existing
finite-boundary interface. -/
noncomputable def EhmCompletedProfileDoubleCofinalVanishing.toBoundary
    {H : EhmPrimeDiscrepancyExplicitModeData}
    (HP : EhmCompletedProfileDoubleCofinalVanishing H) :
    EhmDoubleCofinalBoundaryVanishing ehmR1 where
  cofinally_small ε hε N₀ := by
    rcases HP.cofinally_small ε hε N₀ with
      ⟨N, hN₀, hN, hfreq⟩
    refine ⟨N, hN₀, hN, ?_⟩
    exact (hfreq.and_eventually (eventually_ge_atTop N)).mono fun J hJ ↦ by
      rw [← Real.norm_eq_abs, ← Complex.norm_real]
      rw [ofReal_ehmFiniteCoupledBoundaryExpression_eq_completedBoundaryProfile
        H N J hN hJ.2]
      exact hJ.1

/-- Conversely, the ordinary double-cofinal boundary package yields the
completed-profile package for every valid explicit-formula decomposition.
Hence the new formulation does not strengthen H15. -/
noncomputable def EhmDoubleCofinalBoundaryVanishing.toCompletedProfile
    (H : EhmPrimeDiscrepancyExplicitModeData)
    (HB : EhmDoubleCofinalBoundaryVanishing ehmR1) :
    EhmCompletedProfileDoubleCofinalVanishing H where
  cofinally_small ε hε N₀ := by
    rcases HB.cofinally_small ε hε N₀ with
      ⟨N, hN₀, hN, hfreq⟩
    refine ⟨N, hN₀, hN, ?_⟩
    exact (hfreq.and_eventually (eventually_ge_atTop N)).mono fun J hJ ↦ by
      rw [← ofReal_ehmFiniteCoupledBoundaryExpression_eq_completedBoundaryProfile
        H N J hN hJ.2]
      simpa [Complex.norm_real, Real.norm_eq_abs] using hJ.1

/-- Completed-profile double-cofinal cancellation closes the existing
Báez--Duarte route, conditional only on the already isolated rational
autocorrelation series bridge. -/
theorem baezDuarteCriterion_of_ehmCompletedProfileDoubleCofinal
    {H : EhmPrimeDiscrepancyExplicitModeData}
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (HP : EhmCompletedProfileDoubleCofinalVanishing H) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmDoubleCofinal HS HP.toBoundary

/-! ## Signed dyadic formulation -/

/-- A one-sided signed dyadic estimate for the real part of the complete
profile.  The complex expression is real by the exact finite bridge, but
using `.re` exposes precisely the quantity consumed by the existing signed
boundary-average theorem. -/
structure EhmCompletedProfileDyadicSignedAverageVanishing
    (H : EhmPrimeDiscrepancyExplicitModeData) where
  eta : ℕ → ℝ
  eta_nonneg : ∀ X, 0 ≤ eta X
  eta_tendsto_zero : Tendsto eta atTop (nhds 0)
  cofinal_sum_bound : ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      (∑ N ∈ ehmDyadicNBlock X,
        (ehmPrimeCompletedBoundaryProfile H N J).re) ≤
        ((ehmDyadicNBlock X).card : ℝ) * eta X

/-- The signed completed-profile mean is exactly the existing signed finite
boundary mean once the hyperbolic cutoff lies beyond the dyadic block. -/
noncomputable def EhmCompletedProfileDyadicSignedAverageVanishing.toBoundaryAverage
    {H : EhmPrimeDiscrepancyExplicitModeData}
    (HP : EhmCompletedProfileDyadicSignedAverageVanishing H) :
    EhmDyadicSignedBoundaryAverageVanishing where
  eta := HP.eta
  eta_nonneg := HP.eta_nonneg
  eta_tendsto_zero := HP.eta_tendsto_zero
  cofinal_sum_bound X hX := by
    have hlate : ∀ᶠ J : ℕ in atTop, 2 * X ≤ J := eventually_ge_atTop (2 * X)
    exact ((HP.cofinal_sum_bound X hX).and_eventually hlate).mono fun J hJ ↦ by
      calc
        (∑ N ∈ ehmDyadicNBlock X,
            ehmFiniteCoupledBoundaryExpression ehmR1 N J) =
            ∑ N ∈ ehmDyadicNBlock X,
              (ehmPrimeCompletedBoundaryProfile H N J).re := by
              apply Finset.sum_congr rfl
              intro N hNmem
              rw [completedBoundaryProfile_re H N J
                (hX.trans (Finset.mem_Icc.mp hNmem).1)
                ((Finset.mem_Icc.mp hNmem).2.trans hJ.2)]
        _ ≤ ((ehmDyadicNBlock X).card : ℝ) * HP.eta X := hJ.1

/-- The signed dyadic completed-profile target is therefore sufficient for
the Báez--Duarte criterion. -/
theorem baezDuarteCriterion_of_ehmCompletedProfileDyadicSignedAverage
    {H : EhmPrimeDiscrepancyExplicitModeData}
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (HP : EhmCompletedProfileDyadicSignedAverageVanishing H) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmDyadicSignedBoundaryAverage HS
    HP.toBoundaryAverage

end RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCofinal
