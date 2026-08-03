import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmPrimeExplicitFormula

/-!
# Correction matching for explicit prime-discrepancy modes

This module upgrades the shifted Abel identity to the global discrepancy
`A(k) = ψ(k) - k`.  It then defines one linear Abel transport for every
explicit-formula mode.  Consequently endpoint, trivial-zero, and symmetric
zero contributions are all derived by the same operator.

The actual Riemann--von Mangoldt formula and the final signed zero estimate
remain analytic inputs.  All mode assembly below is exact finite algebra.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCorrectionMatching

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmExplicitFarCutoff
open RH.Criteria.NymanBeurling.BCFLogTaperEhmHighSectorCompensation
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeDiscrepancyAbel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeExplicitFormula

/-- The global-discrepancy form of one real Abel row.  The `k=N` term is
essential: removing it changes the lower endpoint from `f(N)` to `f(N+1)`. -/
noncomputable def ehmCenteredPrimeGlobalAbelRow
    (N m J : ℕ) : ℝ :=
  ehmPrimeDiscrepancy J * ehmR1 ((J : ℝ) / (m : ℝ)) -
    ehmPrimeDiscrepancy N * ehmR1 ((N : ℝ) / (m : ℝ)) -
    ∑ k ∈ Finset.Ico N J,
      ehmPrimeDiscrepancy k *
        (ehmR1 (((k + 1 : ℕ) : ℝ) / (m : ℝ)) -
          ehmR1 ((k : ℝ) / (m : ℝ)))

/-- Successive global discrepancies differ by the centered von Mangoldt
coefficient at the new endpoint. -/
theorem ehmPrimeDiscrepancy_succ (k : ℕ) :
    ehmPrimeDiscrepancy (k + 1) =
      ehmPrimeDiscrepancy k +
        (ArithmeticFunction.vonMangoldt (k + 1) - 1) := by
  unfold ehmPrimeDiscrepancy
  rw [Finset.sum_range_succ]

/-- Exact global Abel summation on `N < j ≤ J`. -/
theorem ehmCenteredPrimeIntervalRow_eq_globalAbel
    (N m J : ℕ) (hNJ : N ≤ J) :
    (∑ j ∈ Finset.Icc (N + 1) J,
      (ArithmeticFunction.vonMangoldt j - 1) *
        ehmR1 ((j : ℝ) / (m : ℝ))) =
      ehmCenteredPrimeGlobalAbelRow N m J := by
  induction J, hNJ using Nat.le_induction with
  | base =>
      simp [ehmCenteredPrimeGlobalAbelRow]
  | succ J hNJ ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      rw [ih]
      unfold ehmCenteredPrimeGlobalAbelRow
      rw [Finset.sum_Ico_succ_top hNJ]
      rw [ehmPrimeDiscrepancy_succ]
      ring

/-- The shifted and global Abel rows are exactly the same finite object. -/
theorem ehmCenteredPrimeAbelRow_eq_global
    (N m J : ℕ) (hNJ : N ≤ J) :
    ehmCenteredPrimeAbelRow N m (J - N) =
      ehmCenteredPrimeGlobalAbelRow N m J := by
  rw [← ehmCenteredPrimeShiftedRow_eq_abel]
  rw [← ehmCenteredPrimeIntervalRow_eq_shifted N m J hNJ]
  exact ehmCenteredPrimeIntervalRow_eq_globalAbel N m J hNJ

/-- Complex-linear Abel transport of an arbitrary discrepancy mode. -/
noncomputable def ehmPrimeAbelMode
    (u : ℕ → ℂ) (N m J : ℕ) : ℂ :=
  u J * (ehmR1 ((J : ℝ) / (m : ℝ)) : ℂ) -
    u N * (ehmR1 ((N : ℝ) / (m : ℝ)) : ℂ) -
    ∑ k ∈ Finset.Ico N J,
      u k *
        ((ehmR1 (((k + 1 : ℕ) : ℝ) / (m : ℝ)) : ℂ) -
          (ehmR1 ((k : ℝ) / (m : ℝ)) : ℂ))

/-- Abel transport is additive in the discrepancy mode. -/
theorem ehmPrimeAbelMode_add
    (u v : ℕ → ℂ) (N m J : ℕ) :
    ehmPrimeAbelMode (u + v) N m J =
      ehmPrimeAbelMode u N m J + ehmPrimeAbelMode v N m J := by
  classical
  unfold ehmPrimeAbelMode
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

/-- The real global Abel row embeds into the complex mode transport of the
global prime discrepancy. -/
theorem ofReal_ehmCenteredPrimeGlobalAbelRow
    (N m J : ℕ) :
    (ehmCenteredPrimeGlobalAbelRow N m J : ℂ) =
      ehmPrimeAbelMode (fun k ↦ (ehmPrimeDiscrepancy k : ℂ)) N m J := by
  classical
  unfold ehmCenteredPrimeGlobalAbelRow ehmPrimeAbelMode
  push_cast
  rfl

/-- Transport a discrepancy mode through every logarithmically tapered
Möbius row. -/
noncomputable def ehmPrimeHighAggregateMode
    (u : ℕ → ℂ) (N J : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 N,
    ((dirichletCoeff N m / (m : ℝ) / Real.log N : ℝ) : ℂ) *
      ehmPrimeAbelMode u N m J

/-- The aggregate transport remains additive. -/
theorem ehmPrimeHighAggregateMode_add
    (u v : ℕ → ℂ) (N J : ℕ) :
    ehmPrimeHighAggregateMode (u + v) N J =
      ehmPrimeHighAggregateMode u N J +
        ehmPrimeHighAggregateMode v N J := by
  classical
  unfold ehmPrimeHighAggregateMode
  simp_rw [ehmPrimeAbelMode_add, mul_add]
  exact Finset.sum_add_distrib

/-- The Abel transform of the linear discrepancy `k ↦ k` is exactly the
unit-coefficient interval row. -/
theorem ehmPrimeAbelMode_natCast_eq_interval
    (N m J : ℕ) (hNJ : N ≤ J) :
    ehmPrimeAbelMode (fun k ↦ (k : ℂ)) N m J =
      ∑ j ∈ Finset.Icc (N + 1) J,
        (ehmR1 ((j : ℝ) / (m : ℝ)) : ℂ) := by
  induction J, hNJ using Nat.le_induction with
  | base =>
      simp [ehmPrimeAbelMode]
  | succ J hNJ ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      rw [← ih]
      unfold ehmPrimeAbelMode
      rw [Finset.sum_Ico_succ_top hNJ]
      push_cast
      ring

/-- The deterministic unit high tail is the aggregate transport of the
linear discrepancy mode. -/
theorem ofReal_ehmFiniteVonMangoldtHighUnitTail_eq_natAggregate
    (N J : ℕ) (hNJ : N ≤ J) :
    (ehmFiniteVonMangoldtHighUnitTail N J : ℂ) =
      ehmPrimeHighAggregateMode (fun k ↦ (k : ℂ)) N J := by
  classical
  unfold ehmFiniteVonMangoldtHighUnitTail ehmPrimeHighAggregateMode
  rw [Finset.sum_comm]
  push_cast
  apply Finset.sum_congr rfl
  intro m _
  rw [ehmPrimeAbelMode_natCast_eq_interval N m J hNJ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The centered high tail is the aggregate Abel transport of the global
prime discrepancy. -/
theorem ofReal_ehmFiniteVonMangoldtHighCenteredTail_eq_aggregate
    (N J : ℕ) (hNJ : N ≤ J) :
    (ehmFiniteVonMangoldtHighCenteredTail N J : ℂ) =
      ehmPrimeHighAggregateMode
        (fun k ↦ (ehmPrimeDiscrepancy k : ℂ)) N J := by
  rw [ehmFiniteVonMangoldtHighCenteredTail_eq_abel N J hNJ]
  unfold ehmFiniteCenteredPrimeAbelTail ehmPrimeHighAggregateMode
  push_cast
  apply Finset.sum_congr rfl
  intro m _
  rw [ehmCenteredPrimeAbelRow_eq_global N m J hNJ]
  rw [← ofReal_ehmCenteredPrimeGlobalAbelRow]

/-- A pointwise explicit-formula decomposition of the integer prime
discrepancy.  The symmetric zero mode carries its convergence convention. -/
structure EhmPrimeDiscrepancyExplicitModeData where
  endpointMode : ℕ → ℂ
  trivialZeroMode : ℕ → ℂ
  symmetricZeroMode : ℕ → ℂ
  decomposition : ∀ k : ℕ,
    (ehmPrimeDiscrepancy k : ℂ) =
      endpointMode k + trivialZeroMode k + symmetricZeroMode k

/-- Pointwise explicit-formula data induce the high-tail decomposition by
one and the same Abel transport. -/
noncomputable def EhmPrimeDiscrepancyExplicitModeData.toHighTail
    (H : EhmPrimeDiscrepancyExplicitModeData) :
    EhmHighTailExplicitFormulaData where
  endpointMode N J := ehmPrimeHighAggregateMode H.endpointMode N J
  trivialZeroMode N J := ehmPrimeHighAggregateMode H.trivialZeroMode N J
  symmetricZeroMode N J := ehmPrimeHighAggregateMode H.symmetricZeroMode N J
  decomposition N J _ hNJ := by
    rw [ofReal_ehmFiniteVonMangoldtHighCenteredTail_eq_aggregate N J hNJ]
    have hfun :
        (fun k ↦ (ehmPrimeDiscrepancy k : ℂ)) =
          H.endpointMode + H.trivialZeroMode + H.symmetricZeroMode := by
      funext k
      exact H.decomposition k
    rw [hfun, ehmPrimeHighAggregateMode_add,
      ehmPrimeHighAggregateMode_add]

/-- For pointwise explicit-formula data, the unmatched elementary mode is
the natural-cutoff defect plus one aggregate transport of the complete
elementary profile `k + endpoint(k) + trivial(k)`.  This is the concrete
correction-matching target. -/
theorem unmatchedElementaryMode_toHighTail_eq_natural_add_aggregate
    (H : EhmPrimeDiscrepancyExplicitModeData)
    (N J : ℕ) (hNJ : N ≤ J) :
    ehmHighTailUnmatchedElementaryMode H.toHighTail N J =
      (ehmFiniteNaturalCutoffDefect N : ℂ) +
        ehmPrimeHighAggregateMode
          ((fun k : ℕ ↦ (k : ℂ)) + H.endpointMode + H.trivialZeroMode) N J := by
  unfold ehmHighTailUnmatchedElementaryMode
    EhmPrimeDiscrepancyExplicitModeData.toHighTail
    ehmFiniteMeanPrimeCompletedDefect
  push_cast
  rw [ofReal_ehmFiniteVonMangoldtHighUnitTail_eq_natAggregate N J hNJ]
  rw [ehmPrimeHighAggregateMode_add, ehmPrimeHighAggregateMode_add]
  ring

/-- The complete explicit profile.  The zero mode remains coupled to the
linear, endpoint, and trivial modes; this is the normal form that survives
the elementary correction-matching stop test. -/
noncomputable def ehmPrimeCompletedExplicitProfile
    (H : EhmPrimeDiscrepancyExplicitModeData) : ℕ → ℂ :=
  (fun k : ℕ ↦ (k : ℂ)) + H.endpointMode + H.trivialZeroMode +
    H.symmetricZeroMode

/-- The full retained expression is the natural-cutoff defect plus the Abel
transport of the complete explicit profile.  No mode is bounded separately. -/
theorem retainedExpression_eq_natural_add_completedProfile
    (H : EhmPrimeDiscrepancyExplicitModeData)
    (N J : ℕ) (hN : 2 ≤ N) (hNJ : N ≤ J) :
    ((ehmFiniteMeanPrimeCompletedDefect N J +
        ehmFiniteVonMangoldtHighCenteredTail N J : ℝ) : ℂ) =
      (ehmFiniteNaturalCutoffDefect N : ℂ) +
        ehmPrimeHighAggregateMode
          (ehmPrimeCompletedExplicitProfile H) N J := by
  rw [retainedExpression_eq_elementary_add_symmetricZero
    H.toHighTail N J hN hNJ]
  rw [unmatchedElementaryMode_toHighTail_eq_natural_add_aggregate
    H N J hNJ]
  unfold ehmPrimeCompletedExplicitProfile
    EhmPrimeDiscrepancyExplicitModeData.toHighTail
  simp_rw [ehmPrimeHighAggregateMode_add]
  ring

/-- Honest post-audit target: cancellation is required only after every
explicit-formula mode and the natural-cutoff defect have been reassembled. -/
structure EhmHighTailCompletedProfileCancellation
    (H : EhmPrimeDiscrepancyExplicitModeData) where
  C : ℝ
  C_nonneg : 0 ≤ C
  bound : ∀ X N J : ℕ, 2 ≤ X →
    N ∈ ehmDyadicNBlock X → ehmExplicitFarCutoff X ≤ J →
    ‖(ehmFiniteNaturalCutoffDefect N : ℂ) +
        ehmPrimeHighAggregateMode
          (ehmPrimeCompletedExplicitProfile H) N J‖ ≤ C / (N : ℝ)

/-- Completed-profile cancellation directly supplies the original signed
Route B interface, without the rejected separate elementary matching step. -/
noncomputable def EhmHighTailCompletedProfileCancellation.toSigned
    {H : EhmPrimeDiscrepancyExplicitModeData}
    (HC : EhmHighTailCompletedProfileCancellation H) :
    EhmHighTailSignedZeroCancellation H.toHighTail where
  C := HC.C
  C_nonneg := HC.C_nonneg
  coupled_bound X N J hX hN hJ := by
    have hNtwo : 2 ≤ N := hX.trans (Finset.mem_Icc.mp hN).1
    have hNJ : N ≤ J :=
      (Finset.mem_Icc.mp hN).2.trans
        ((two_mul_le_ehmExplicitFarCutoff X).trans hJ)
    rw [unmatchedElementaryMode_toHighTail_eq_natural_add_aggregate
      H N J hNJ]
    change ‖(ehmFiniteNaturalCutoffDefect N : ℂ) +
        ehmPrimeHighAggregateMode
          ((fun k : ℕ ↦ (k : ℂ)) + H.endpointMode + H.trivialZeroMode) N J +
        ehmPrimeHighAggregateMode H.symmetricZeroMode N J‖ ≤ HC.C / (N : ℝ)
    rw [add_assoc, ← ehmPrimeHighAggregateMode_add]
    simpa [ehmPrimeCompletedExplicitProfile] using
      HC.bound X N J hX hN hJ

/-! ## Exact correction matching and the remaining signed zero estimate -/

/-- The elementary explicit-formula modes reproduce the retained
mean-prime correction exactly. -/
structure EhmHighTailExplicitCorrectionMatching
    (H : EhmHighTailExplicitFormulaData) : Prop where
  matched : ∀ N J : ℕ, 2 ≤ N → N ≤ J →
    ehmHighTailUnmatchedElementaryMode H N J = 0

/-- Under exact correction matching, the complete retained expression is
precisely the symmetric nontrivial-zero mode. -/
theorem retainedExpression_eq_symmetricZero_of_matching
    {H : EhmHighTailExplicitFormulaData}
    (HM : EhmHighTailExplicitCorrectionMatching H)
    (N J : ℕ) (hN : 2 ≤ N) (hNJ : N ≤ J) :
    ((ehmFiniteMeanPrimeCompletedDefect N J +
        ehmFiniteVonMangoldtHighCenteredTail N J : ℝ) : ℂ) =
      H.symmetricZeroMode N J := by
  rw [retainedExpression_eq_elementary_add_symmetricZero H N J hN hNJ]
  rw [HM.matched N J hN hNJ, zero_add]

/-- The post-matching analytic problem, with no elementary correction left
outside the signed zero aggregate. -/
structure EhmHighTailSymmetricZeroCancellation
    (H : EhmHighTailExplicitFormulaData) where
  C : ℝ
  C_nonneg : 0 ≤ C
  bound : ∀ X N J : ℕ, 2 ≤ X →
    N ∈ ehmDyadicNBlock X → ehmExplicitFarCutoff X ≤ J →
    ‖H.symmetricZeroMode N J‖ ≤ C / (N : ℝ)

/-- Correction matching plus signed zero cancellation supply the previous
one-field Route B interface. -/
noncomputable def EhmHighTailSymmetricZeroCancellation.toSigned
    {H : EhmHighTailExplicitFormulaData}
    (HM : EhmHighTailExplicitCorrectionMatching H)
    (HZ : EhmHighTailSymmetricZeroCancellation H) :
    EhmHighTailSignedZeroCancellation H where
  C := HZ.C
  C_nonneg := HZ.C_nonneg
  coupled_bound X N J hX hN hJ := by
    have hNtwo : 2 ≤ N := hX.trans (Finset.mem_Icc.mp hN).1
    have hNJ : N ≤ J :=
      (Finset.mem_Icc.mp hN).2.trans
        ((two_mul_le_ehmExplicitFarCutoff X).trans hJ)
    rw [HM.matched N J hNtwo hNJ, zero_add]
    exact HZ.bound X N J hX hN hJ

end RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCorrectionMatching
