import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCofinal
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmCutoffAverageMainTerm

/-!
# Collapse of the completed explicit prime profile

Keeping every explicit-formula mode is analytically honest, but it also has
an exact algebraic consequence: the completed profile is independent of the
chosen decomposition and is simply the finite Chebyshev function `ψ`.

This module proves that collapse, transports it through the common Abel
operator, and identifies the resulting signed dyadic target with the already
existing completed-main target.  Thus an explicit-formula decomposition is a
change of coordinates, not by itself a new cancellation estimate.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeProfileCollapse

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmBoundaryResearch
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCutoffAverageMainTerm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmHighSectorCompensation
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCorrectionMatching
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeDiscrepancyAbel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmSignedAverage
open RH.Criteria.NymanBeurling.BCFLogTaperEhmUniformBoundary

/-- The integer-point Chebyshev function
`ψ(k) = ∑_{1 ≤ n ≤ k} Λ(n)`. -/
noncomputable def ehmPrimeChebyshevValue (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, ArithmeticFunction.vonMangoldt (i + 1)

/-- The centered discrepancy is exactly `ψ(k) - k`. -/
theorem ehmPrimeDiscrepancy_add_natCast (k : ℕ) :
    ehmPrimeDiscrepancy k + (k : ℝ) = ehmPrimeChebyshevValue k := by
  unfold ehmPrimeDiscrepancy ehmPrimeChebyshevValue
  rw [show (k : ℝ) = ∑ _i ∈ Finset.range k, (1 : ℝ) by simp]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Successive Chebyshev values differ by the new von Mangoldt coefficient. -/
theorem ehmPrimeChebyshevValue_succ (k : ℕ) :
    ehmPrimeChebyshevValue (k + 1) =
      ehmPrimeChebyshevValue k + ArithmeticFunction.vonMangoldt (k + 1) := by
  unfold ehmPrimeChebyshevValue
  rw [Finset.sum_range_succ]

/-- Every exact endpoint/trivial/zero decomposition gives the same complete
profile: the complex embedding of `ψ(k)`. -/
theorem ehmPrimeCompletedExplicitProfile_eq_chebyshev
    (H : EhmPrimeDiscrepancyExplicitModeData) (k : ℕ) :
    ehmPrimeCompletedExplicitProfile H k =
      (ehmPrimeChebyshevValue k : ℂ) := by
  unfold ehmPrimeCompletedExplicitProfile
  simp only [Pi.add_apply]
  calc
    (k : ℂ) + H.endpointMode k + H.trivialZeroMode k +
        H.symmetricZeroMode k =
      (k : ℂ) + (ehmPrimeDiscrepancy k : ℂ) := by
        rw [H.decomposition]
        ring
    _ = (ehmPrimeChebyshevValue k : ℂ) := by
      have h := congrArg (fun x : ℝ ↦ (x : ℂ))
        (ehmPrimeDiscrepancy_add_natCast k)
      push_cast at h
      simpa [add_comm] using h

/-- Consequently the complete profile does not depend on which exact
explicit-formula decomposition was chosen. -/
theorem ehmPrimeCompletedExplicitProfile_independent
    (H₁ H₂ : EhmPrimeDiscrepancyExplicitModeData) :
    ehmPrimeCompletedExplicitProfile H₁ =
      ehmPrimeCompletedExplicitProfile H₂ := by
  funext k
  rw [ehmPrimeCompletedExplicitProfile_eq_chebyshev,
    ehmPrimeCompletedExplicitProfile_eq_chebyshev]

/-- The completed finite boundary is independent of the chosen exact
endpoint/trivial/symmetric-zero decomposition.  Thus those named modes are
coordinates for the same finite profile, not functionally independent pieces
of an irreducible decomposition. -/
theorem ehmPrimeCompletedBoundaryProfile_independent
    (H₁ H₂ : EhmPrimeDiscrepancyExplicitModeData) (N J : ℕ) :
    ehmPrimeCompletedBoundaryProfile H₁ N J =
      ehmPrimeCompletedBoundaryProfile H₂ N J := by
  unfold ehmPrimeCompletedBoundaryProfile
  rw [ehmPrimeCompletedExplicitProfile_independent H₁ H₂]

/-- Abel transport of `ψ` recovers the full von Mangoldt interval row. -/
theorem ehmPrimeAbelMode_chebyshev_eq_interval
    (N m J : ℕ) (hNJ : N ≤ J) :
    ehmPrimeAbelMode (fun k ↦ (ehmPrimeChebyshevValue k : ℂ)) N m J =
      ∑ j ∈ Finset.Icc (N + 1) J,
        (ArithmeticFunction.vonMangoldt j : ℂ) *
          (ehmR1 ((j : ℝ) / (m : ℝ)) : ℂ) := by
  induction J, hNJ using Nat.le_induction with
  | base =>
      simp [ehmPrimeAbelMode]
  | succ J hNJ ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      rw [← ih]
      unfold ehmPrimeAbelMode
      rw [Finset.sum_Ico_succ_top hNJ]
      simp only
      rw [ehmPrimeChebyshevValue_succ]
      push_cast
      ring

/-- Aggregating the Chebyshev Abel rows over the tapered Möbius coefficient
recovers the original finite von Mangoldt high tail. -/
theorem ehmPrimeHighAggregateMode_chebyshev_eq_highTail
    (N J : ℕ) (hNJ : N ≤ J) :
    ehmPrimeHighAggregateMode
        (fun k ↦ (ehmPrimeChebyshevValue k : ℂ)) N J =
      (ehmFiniteVonMangoldtHighTail N J : ℂ) := by
  classical
  unfold ehmPrimeHighAggregateMode ehmFiniteVonMangoldtHighTail
  rw [Finset.sum_comm]
  push_cast
  apply Finset.sum_congr rfl
  intro m _
  rw [ehmPrimeAbelMode_chebyshev_eq_interval N m J hNJ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The complete explicit-profile transport is therefore just the original
high von Mangoldt tail. -/
theorem ehmPrimeHighAggregateMode_completedProfile_eq_highTail
    (H : EhmPrimeDiscrepancyExplicitModeData)
    (N J : ℕ) (hNJ : N ≤ J) :
    ehmPrimeHighAggregateMode
        (ehmPrimeCompletedExplicitProfile H) N J =
      (ehmFiniteVonMangoldtHighTail N J : ℂ) := by
  have hfun : ehmPrimeCompletedExplicitProfile H =
      fun k ↦ (ehmPrimeChebyshevValue k : ℂ) := by
    funext k
    exact ehmPrimeCompletedExplicitProfile_eq_chebyshev H k
  rw [hfun, ehmPrimeHighAggregateMode_chebyshev_eq_highTail N J hNJ]

/-- Normal form of the completed boundary profile with all explicit modes
collapsed.  This exposes the exact natural-defect/high-tail/missing-tail
coupling and contains no reference to a zero decomposition. -/
theorem ehmPrimeCompletedBoundaryProfile_eq_natural_high_sub_missing
    (H : EhmPrimeDiscrepancyExplicitModeData)
    (N J : ℕ) (hNJ : N ≤ J) :
    ehmPrimeCompletedBoundaryProfile H N J =
      (ehmFiniteNaturalCutoffDefect N : ℂ) +
        (ehmFiniteVonMangoldtHighTail N J : ℂ) -
          (ehmFiniteMissingDivisorTailOuter ehmR1 N J : ℂ) := by
  unfold ehmPrimeCompletedBoundaryProfile
  rw [ehmPrimeHighAggregateMode_completedProfile_eq_highTail H N J hNJ]

/-- Once the finite interval is valid, the apparently complex completed
profile is real.  The complex coordinates only record an explicit-formula
decomposition; the exact reassembled boundary has no residual imaginary
mode. -/
theorem ehmPrimeCompletedBoundaryProfile_im_eq_zero
    (H : EhmPrimeDiscrepancyExplicitModeData)
    (N J : ℕ) (hNJ : N ≤ J) :
    (ehmPrimeCompletedBoundaryProfile H N J).im = 0 := by
  rw [ehmPrimeCompletedBoundaryProfile_eq_natural_high_sub_missing
    H N J hNJ]
  simp

/-! ## Dyadic target comparison -/

/-- The signed dyadic sum of completed profiles is exactly the established
completed main, missing-divisor correction, and moment remainder expression. -/
theorem sum_completedBoundaryProfile_re_eq_fullMain_sub_missing
    (H : EhmPrimeDiscrepancyExplicitModeData)
    (X J : ℕ) (hX : 2 ≤ X) (hJ : 2 * X ≤ J) :
    (∑ N ∈ ehmDyadicNBlock X,
        (ehmPrimeCompletedBoundaryProfile H N J).re) =
      ehmDyadicFullMainJointSum ehmR1 X J -
        (∑ N ∈ ehmDyadicNBlock X,
          ehmFiniteMissingDivisorTailOuter ehmR1 N J) +
        ∑ N ∈ ehmDyadicNBlock X, ehmCoupledRemainder N := by
  calc
    (∑ N ∈ ehmDyadicNBlock X,
        (ehmPrimeCompletedBoundaryProfile H N J).re) =
      ∑ N ∈ ehmDyadicNBlock X,
        ehmFiniteCoupledBoundaryExpression ehmR1 N J := by
          apply Finset.sum_congr rfl
          intro N hNmem
          exact completedBoundaryProfile_re H N J
            (hX.trans (Finset.mem_Icc.mp hNmem).1)
            ((Finset.mem_Icc.mp hNmem).2.trans hJ)
    _ = _ := sum_ehmFiniteCoupledBoundaryExpression_eq_fullMain_sub_missing
      ehmR1 X J hX hJ

/-- The older completed-main signed estimate directly yields the
completed-profile estimate for every exact explicit decomposition. -/
noncomputable def EhmDyadicCompletedMainSignedAverageVanishing.toCompletedProfile
    (H : EhmPrimeDiscrepancyExplicitModeData)
    (HM : EhmDyadicCompletedMainSignedAverageVanishing) :
    EhmCompletedProfileDyadicSignedAverageVanishing H where
  eta := HM.eta
  eta_nonneg := HM.eta_nonneg
  eta_tendsto_zero := HM.eta_tendsto_zero
  cofinal_sum_bound X hX :=
    (HM.cofinal_sum_bound X hX).mono fun J hJ ↦ by
      rw [sum_completedBoundaryProfile_re_eq_fullMain_sub_missing
        H X J hX hJ.1]
      exact hJ.2

/-- Conversely, the completed-profile signed estimate gives the older
completed-main interface.  Hence the two analytic gates are equivalent. -/
noncomputable def EhmCompletedProfileDyadicSignedAverageVanishing.toCompletedMain
    {H : EhmPrimeDiscrepancyExplicitModeData}
    (HP : EhmCompletedProfileDyadicSignedAverageVanishing H) :
    EhmDyadicCompletedMainSignedAverageVanishing where
  eta := HP.eta
  eta_nonneg := HP.eta_nonneg
  eta_tendsto_zero := HP.eta_tendsto_zero
  cofinal_sum_bound X hX := by
    have hlate : ∀ᶠ J : ℕ in atTop, 2 * X ≤ J := eventually_ge_atTop (2 * X)
    exact ((HP.cofinal_sum_bound X hX).and_eventually hlate).mono fun J hJ ↦ by
      refine ⟨hJ.2, ?_⟩
      rw [← sum_completedBoundaryProfile_re_eq_fullMain_sub_missing
        H X J hX hJ.2]
      exact hJ.1

end RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeProfileCollapse
