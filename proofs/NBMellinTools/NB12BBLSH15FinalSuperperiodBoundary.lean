/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15TerminalSecondAbel

/-!
# NB12zq: exact audit of the final correction-coupled superperiod boundary

The boundary left after the two finite Abel transforms has two descriptions:

* uncovered complete ordinary `q`-rows; and
* incomplete ordinary-period endpoints.

This file proves that their point supports are disjoint and that their union
is exactly the normalized `L*q`-superperiod boundary.  It then rewrites the
two contributions as one signed pointwise sum on that support.

The final categorical stop test is negative: even for a genuine active H15
row, the unweighted boundary character mode need not vanish.  Thus no third
exact zero-mode cancellation is available merely from period geometry; the
final boundary must remain inside the signed analytic estimate.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius
open Complex

namespace NBMellinTools.NB12

/-! ## Exact point support -/

/-- Progression points lying in complete ordinary `q`-periods whose row is
not covered by a complete normalized `L*q` superperiod. -/
def h15NormalizedRowSuperperiodBoundaryPointSupport
    (U L q : ℕ) : Finset ℕ :=
  (h15NormalizedRowSuperperiodBoundary U L q).biUnion fun k =>
    h15NormalizedProgressionQPeriod k L q

/-- Pointwise complete normalized superperiod support is exactly the lift of
the corresponding complete row support. -/
theorem h15CompleteNormalizedSuperperiodSupport_eq_rowLift
    (U L q : ℕ) (hq : 0 < q) :
    h15CompleteNormalizedSuperperiodSupport U L q =
      (h15CompleteNormalizedRowSuperperiodSupport U L q).biUnion fun k =>
        h15NormalizedProgressionQPeriod k L q := by
  ext u
  constructor
  · intro hu
    rw [h15CompleteNormalizedSuperperiodSupport, Finset.mem_biUnion] at hu
    rcases hu with ⟨j, hj, huj⟩
    have hu' : u ∈
        (Finset.Ico (j * L) ((j + 1) * L)).biUnion
          (fun k => h15NormalizedProgressionQPeriod k L q) := by
      rw [biUnion_h15NormalizedProgressionQPeriod_eq_superperiod j L q hq]
      exact huj
    rw [Finset.mem_biUnion] at hu'
    rcases hu' with ⟨k, hk, huk⟩
    rw [Finset.mem_biUnion]
    refine ⟨k, ?_, huk⟩
    rw [h15CompleteNormalizedRowSuperperiodSupport, Finset.mem_biUnion]
    exact ⟨j, hj, hk⟩
  · intro hu
    rw [Finset.mem_biUnion] at hu
    rcases hu with ⟨k, hk, huk⟩
    rw [h15CompleteNormalizedRowSuperperiodSupport,
      Finset.mem_biUnion] at hk
    rcases hk with ⟨j, hj, hkj⟩
    rw [h15CompleteNormalizedSuperperiodSupport, Finset.mem_biUnion]
    refine ⟨j, hj, ?_⟩
    rw [← biUnion_h15NormalizedProgressionQPeriod_eq_superperiod j L q hq,
      Finset.mem_biUnion]
    exact ⟨k, hkj, huk⟩

/-- The lifted uncovered rows are precisely the complete-period progression
points left after deleting all complete normalized superperiods. -/
theorem h15NormalizedRowSuperperiodBoundaryPointSupport_eq_sdiff
    (U L q : ℕ) (hq : 0 < q) :
    h15NormalizedRowSuperperiodBoundaryPointSupport U L q =
      h15NormalizedCompletePeriodProgressionSupport U L q \
        h15CompleteNormalizedSuperperiodSupport U L q := by
  ext u
  constructor
  · intro hu
    rw [h15NormalizedRowSuperperiodBoundaryPointSupport,
      Finset.mem_biUnion] at hu
    rcases hu with ⟨k, hk, huk⟩
    have hkBoundary := Finset.mem_sdiff.mp hk
    apply Finset.mem_sdiff.mpr
    constructor
    · rw [h15NormalizedCompletePeriodProgressionSupport,
        Finset.mem_biUnion]
      exact ⟨k, hkBoundary.1, huk⟩
    · intro huComplete
      rw [h15CompleteNormalizedSuperperiodSupport_eq_rowLift U L q hq,
        Finset.mem_biUnion] at huComplete
      rcases huComplete with ⟨k', hkComplete, huk'⟩
      have hku := natDiv_eq_periodIndex_of_mem_h15NormalizedProgressionQPeriod huk
      have hk'u := natDiv_eq_periodIndex_of_mem_h15NormalizedProgressionQPeriod huk'
      apply hkBoundary.2
      have hkk' : k = k' := hku.symm.trans hk'u
      simpa only [hkk'] using hkComplete
  · intro hu
    have hu' := Finset.mem_sdiff.mp hu
    rw [h15NormalizedCompletePeriodProgressionSupport,
      Finset.mem_biUnion] at hu'
    rcases hu'.1 with ⟨k, hk, huk⟩
    rw [h15NormalizedRowSuperperiodBoundaryPointSupport,
      Finset.mem_biUnion]
    refine ⟨k, Finset.mem_sdiff.mpr ⟨hk, ?_⟩, huk⟩
    intro hkComplete
    apply hu'.2
    rw [h15CompleteNormalizedSuperperiodSupport_eq_rowLift U L q hq,
      Finset.mem_biUnion]
    exact ⟨k, hkComplete, huk⟩

/-- The uncovered complete-row lift and the incomplete ordinary-period
support are disjoint. -/
theorem h15NormalizedBoundaryPointSupports_disjoint
    (U L q : ℕ) (hq : 0 < q) :
    Disjoint (h15NormalizedRowSuperperiodBoundaryPointSupport U L q)
      (h15NormalizedIncompletePeriodProgressionSupport U L q) := by
  rw [Finset.disjoint_left]
  intro u huRow huIncomplete
  have huRow' := Finset.mem_sdiff.mp
    (show u ∈ h15NormalizedCompletePeriodProgressionSupport U L q \
        h15CompleteNormalizedSuperperiodSupport U L q by
      rw [← h15NormalizedRowSuperperiodBoundaryPointSupport_eq_sdiff
        U L q hq]
      exact huRow)
  exact (Finset.mem_sdiff.mp huIncomplete).2 huRow'.1

/-- Exact final-support identity: the two retained ledgers form a disjoint
partition of the normalized superperiod boundary. -/
theorem h15NormalizedRowBoundary_union_incomplete_eq_superperiodBoundary
    (U L q : ℕ) (hq : 0 < q) :
    h15NormalizedRowSuperperiodBoundaryPointSupport U L q ∪
        h15NormalizedIncompletePeriodProgressionSupport U L q =
      h15NormalizedSuperperiodBoundarySupport U L q := by
  rw [h15NormalizedRowSuperperiodBoundaryPointSupport_eq_sdiff U L q hq]
  ext u
  have hcompleteSubset :=
    h15NormalizedCompletePeriodProgressionSupport_subset_dyadic U L q
  have hsuperSubset :
      h15CompleteNormalizedSuperperiodSupport U L q ⊆
        h15NormalizedCompletePeriodProgressionSupport U L q := by
    rw [h15CompleteNormalizedSuperperiodSupport_eq_rowLift U L q hq]
    intro v hv
    rw [Finset.mem_biUnion] at hv
    rcases hv with ⟨k, hk, hvk⟩
    rw [h15NormalizedCompletePeriodProgressionSupport,
      Finset.mem_biUnion]
    exact ⟨k,
      h15CompleteNormalizedRowSuperperiodSupport_subset_periodIndices
        U L q hq hk,
      hvk⟩
  simp only [Finset.mem_union, Finset.mem_sdiff,
    h15NormalizedIncompletePeriodProgressionSupport,
    h15NormalizedSuperperiodBoundarySupport]
  constructor
  · rintro (⟨huComplete, huNotSuper⟩ | ⟨huDyadic, huNotComplete⟩)
    · exact ⟨hcompleteSubset huComplete, huNotSuper⟩
    · exact ⟨huDyadic, fun huSuper => huNotComplete (hsuperSubset huSuper)⟩
  · rintro ⟨huDyadic, huNotSuper⟩
    by_cases huComplete :
        u ∈ h15NormalizedCompletePeriodProgressionSupport U L q
    · exact Or.inl ⟨huComplete, huNotSuper⟩
    · exact Or.inr ⟨huDyadic, huComplete⟩

/-! ## One signed pointwise boundary ledger -/

/-- Pointwise lift of the uncovered complete-row boundary. -/
noncomputable def h15NormalizedProgressionTerminalRowBoundaryLift
    (N g r U L q d : ℕ) : ℝ :=
  ∑ k ∈ h15NormalizedRowSuperperiodBoundary U L q,
    ∑ u ∈ h15NormalizedProgressionQPeriod k L q,
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        h15NormalizedProgressionAbelTerminalWeight N g k q *
          h15PairedDirectCrossMode r u q

/-- The row-indexed boundary defect is exactly its pointwise progression
lift; no absolute values or discarded signs enter this reindexing. -/
theorem h15NormalizedRowSuperperiodBoundaryDefect_eq_pointLift
    (N g r U q d : ℕ) :
    h15NormalizedRowSuperperiodBoundaryDefect g r U q d
        (fun k => h15NormalizedProgressionAbelTerminalWeight N g k q) =
      h15NormalizedProgressionTerminalRowBoundaryLift N g r U
        (h15SquareDivisorProgressionModulus g d) q d := by
  unfold h15NormalizedRowSuperperiodBoundaryDefect
    h15NormalizedProgressionTerminalRowBoundaryLift
  dsimp only
  apply Finset.sum_congr rfl
  intro k _hk
  rw [h15PeriodNormalizedProgressionRow_eq_supportSum,
    ← Finset.mul_sum]
  ring

/-- The pointwise coefficient on the final normalized-superperiod boundary.
On uncovered complete ordinary periods it is the terminal first-Abel
increment; on the incomplete ordinary-period support it is the original
smooth H15 weight. -/
noncomputable def h15NormalizedProgressionCoupledBoundaryPointWeight
    (N g U L q d u : ℕ) : ℝ :=
  if u ∈ h15NormalizedCompletePeriodProgressionSupport U L q then
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      h15NormalizedProgressionAbelTerminalWeight N g (u / q) q
  else
    h15NormalizedProgressionSmoothWeight N g d u

/-- The entire final boundary as one signed sum on its exact point support. -/
noncomputable def h15NormalizedProgressionCoupledBoundaryPointRow
    (N g r U L q d : ℕ) : ℝ :=
  ∑ u ∈ h15NormalizedSuperperiodBoundarySupport U L q,
    h15NormalizedProgressionCoupledBoundaryPointWeight N g U L q d u *
      h15PairedDirectCrossMode r u q

theorem sum_h15NormalizedRowBoundaryPointSupport_eq_terminalLift
    (N g r U L q d : ℕ) :
    (∑ u ∈ h15NormalizedRowSuperperiodBoundaryPointSupport U L q,
      h15NormalizedProgressionCoupledBoundaryPointWeight N g U L q d u *
        h15PairedDirectCrossMode r u q) =
      h15NormalizedProgressionTerminalRowBoundaryLift N g r U L q d := by
  classical
  unfold h15NormalizedRowSuperperiodBoundaryPointSupport
    h15NormalizedProgressionTerminalRowBoundaryLift
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro k hk
    have hkComplete := (Finset.mem_sdiff.mp hk).1
    apply Finset.sum_congr rfl
    intro u hu
    have huComplete :
        u ∈ h15NormalizedCompletePeriodProgressionSupport U L q := by
      rw [h15NormalizedCompletePeriodProgressionSupport,
        Finset.mem_biUnion]
      exact ⟨k, hkComplete, hu⟩
    rw [h15NormalizedProgressionCoupledBoundaryPointWeight,
      if_pos huComplete,
      natDiv_eq_periodIndex_of_mem_h15NormalizedProgressionQPeriod hu]
  · apply (h15ReducedNaturalPeriod_pairwiseDisjoint_on
      (h15NormalizedRowSuperperiodBoundary U L q) q).mono
    intro k
    exact Finset.filter_subset _ _

theorem sum_h15NormalizedIncompleteSupport_eq_smoothBoundary
    (N g r U L q d : ℕ) :
    (∑ u ∈ h15NormalizedIncompletePeriodProgressionSupport U L q,
      h15NormalizedProgressionCoupledBoundaryPointWeight N g U L q d u *
        h15PairedDirectCrossMode r u q) =
      h15NormalizedProgressionIncompleteEndpointRow N g r U L q d := by
  unfold h15NormalizedProgressionIncompleteEndpointRow
  apply Finset.sum_congr rfl
  intro u hu
  have huNotComplete := (Finset.mem_sdiff.mp hu).2
  rw [h15NormalizedProgressionCoupledBoundaryPointWeight,
    if_neg huNotComplete]

/-- Exact row-level Step 4v-j identity.  The formerly separate uncovered-row
and incomplete-endpoint terms are one correction-preserving signed sum on
the normalized-superperiod boundary. -/
theorem h15NormalizedProgressionCorrectionCoupledSuperperiodBoundaryRow_eq_pointwise
    (N g r U q d : ℕ) (hq : 0 < q) :
    h15NormalizedProgressionCorrectionCoupledSuperperiodBoundaryRow
        N g r U q d =
      h15NormalizedProgressionCoupledBoundaryPointRow N g r U
        (h15SquareDivisorProgressionModulus g d) q d := by
  let L := h15SquareDivisorProgressionModulus g d
  unfold h15NormalizedProgressionCorrectionCoupledSuperperiodBoundaryRow
    h15NormalizedProgressionCoupledBoundaryPointRow
  dsimp only
  change
    h15NormalizedRowSuperperiodBoundaryDefect g r U q d
        (fun k => h15NormalizedProgressionAbelTerminalWeight N g k q) +
      h15NormalizedProgressionIncompleteEndpointRow N g r U L q d = _
  rw [← h15NormalizedRowBoundary_union_incomplete_eq_superperiodBoundary
      U L q hq,
    Finset.sum_union (h15NormalizedBoundaryPointSupports_disjoint U L q hq),
    sum_h15NormalizedRowBoundaryPointSupport_eq_terminalLift,
    sum_h15NormalizedIncompleteSupport_eq_smoothBoundary,
    h15NormalizedRowSuperperiodBoundaryDefect_eq_pointLift]

/-- Full active-incidence version of the single-support final boundary. -/
noncomputable def h15NormalizedProgressionCoupledBoundaryPointAggregate
    (N g r U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
      h15NormalizedProgressionCoupledBoundaryPointRow N g r U
        (h15SquareDivisorProgressionModulus g d) q d

theorem h15NormalizedProgressionCorrectionCoupledSuperperiodBoundaryAggregate_eq_pointwise
    {N g r U Q : ℕ} (hQ : 0 < Q) :
    h15NormalizedProgressionCorrectionCoupledSuperperiodBoundaryAggregate
        N g r U Q =
      h15NormalizedProgressionCoupledBoundaryPointAggregate N g r U Q := by
  unfold h15NormalizedProgressionCorrectionCoupledSuperperiodBoundaryAggregate
    h15NormalizedProgressionCoupledBoundaryPointAggregate
  apply Finset.sum_congr rfl
  intro q hqMem
  have hqBounds := mem_h15BettinChandeeSupportedNatBlock.mp hqMem
  have hqPos : 0 < q := hQ.trans_le hqBounds.1
  apply Finset.sum_congr rfl
  intro d _hd
  exact
    h15NormalizedProgressionCorrectionCoupledSuperperiodBoundaryRow_eq_pointwise
      N g r U q d hqPos

/-! ## Constant-mode stop test -/

/-- The unweighted character mode on the exact final point support. -/
noncomputable def h15NormalizedSuperperiodBoundaryConstantMode
    (r U L q : ℕ) : ℝ :=
  ∑ u ∈ h15NormalizedSuperperiodBoundarySupport U L q,
    h15PairedDirectCrossMode r u q

/-- A genuine active H15 row with normalized modulus `L=2`. -/
theorem h15_two_mem_dyadicActivePeriodSquareDivisorIndices_two_five_three :
    2 ∈ h15DyadicActivePeriodSquareDivisorIndices 2 5 3 := by
  rw [h15DyadicActivePeriodSquareDivisorIndices, Finset.mem_biUnion]
  refine ⟨2, ?_, ?_⟩
  · norm_num [h15CompletePeriodIndices]
  · rw [mem_h15ActivePeriodSquareDivisorIndices]
    refine ⟨?_, ?_, ?_⟩
    · rw [h15PeriodSquareDivisorIndices, Finset.mem_biUnion]
      refine ⟨8, ?_, ?_⟩
      · norm_num [h15ReducedNaturalPeriod]
      · rw [mem_h15SquareDivisorSupport_iff (by norm_num : 2 * 8 ≠ 0)]
        norm_num
    · norm_num [h15SquareDivisorProgressionModulus,
        h15SquareDivisorCommonFactor]
    · norm_num [h15SquareDivisorProgressionModulus,
        h15SquareDivisorCommonFactor]

theorem h15SquareDivisorProgressionModulus_two_two :
    h15SquareDivisorProgressionModulus 2 2 = 2 := by
  decide

/-- Its final normalized-superperiod boundary consists of one point. -/
theorem h15NormalizedSuperperiodBoundarySupport_five_two_three :
    h15NormalizedSuperperiodBoundarySupport 5 2 3 = {8} := by
  decide

/-- Exact value of the surviving character at that point. -/
theorem h15PairedDirectCrossMode_one_eight_three :
    h15PairedDirectCrossMode 1 8 3 = Real.sqrt 3 / 2 := by
  have hcop : Nat.Coprime 8 3 := by norm_num
  letI : NeZero 3 := ⟨by norm_num⟩
  rw [h15PairedDirectCrossMode_of_coprime 1 8 3 hcop]
  change (ZMod.stdAddChar ((2 : ZMod 3) * ((1 : ℕ) : ZMod 3) *
    ((8 : ℕ) : ZMod 3))).im = _
  rw [show (2 : ZMod 3) * ((1 : ℕ) : ZMod 3) * ((8 : ℕ) : ZMod 3) =
    (1 : ZMod 3) by decide]
  change (ZMod.stdAddChar ((1 : ℤ) : ZMod 3)).im = _
  rw [ZMod.stdAddChar_coe (N := 3) (1 : ℤ)]
  norm_num only [Int.cast_one, Int.cast_ofNat]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (1 : ℂ) / (3 : ℂ) =
    ((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, mul_zero, mul_one, zero_add]
  rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
    Real.sin_pi_sub, Real.sin_pi_div_three]
  simp

/-- The final boundary has no universal exact zero mode, even on a genuine
active row.  This is the formal Step 4v-j stop test. -/
theorem h15NormalizedSuperperiodBoundaryConstantMode_one_five_two_three_ne_zero :
    h15NormalizedSuperperiodBoundaryConstantMode 1 5 2 3 ≠ 0 := by
  rw [h15NormalizedSuperperiodBoundaryConstantMode,
    h15NormalizedSuperperiodBoundarySupport_five_two_three]
  simp only [Finset.sum_singleton,
    h15PairedDirectCrossMode_one_eight_three]
  positivity

/-! ## Refined residual identity and the remaining signed gate -/

/-- The two Abel interiors plus the exact pointwise final boundary. -/
theorem h15NormalizedProgressionRowToPointwiseResidual_eq_twoAbel_add_pointBoundary
    {N g r U Q : ℕ} (hQ : 0 < Q) :
    h15NormalizedProgressionRowToPointwiseResidual N g r U Q =
      h15NormalizedProgressionAbelInteriorAggregate N g r U Q +
        h15NormalizedProgressionTerminalSecondAbelAggregate N g r U Q +
        h15NormalizedProgressionCoupledBoundaryPointAggregate N g r U Q := by
  rw [h15NormalizedProgressionRowToPointwiseResidual_eq_twoAbel_add_boundary
      hQ,
    h15NormalizedProgressionCorrectionCoupledSuperperiodBoundaryAggregate_eq_pointwise
      hQ]

/-- Exact remaining analytic hypothesis after the support and constant-mode
audit.  It deliberately keeps both endpoint sectors in their single signed
pointwise expression. -/
def H15CorrectionCoupledFinalBoundaryEstimate
    (N g r U Q : ℕ) (B : ℝ) : Prop :=
  0 ≤ B ∧
    |h15NormalizedProgressionCoupledBoundaryPointAggregate N g r U Q| ≤ B

/-- Complete Step 4v-j sufficient estimate.  The final boundary is not
bounded termwise; it enters through its correction-coupled signed norm. -/
theorem abs_h15NormalizedProgressionRowToPointwiseResidual_le_finalBoundaryGate
    {N g r U Q : ℕ} {P₁ P₂ B : ℝ}
    (hN : 2 ≤ N) (hg : 1 ≤ g) (hU : 0 < U) (hQ : 0 < Q)
    (hprefix₁ : H15NormalizedProgressionAbelPrefixBound N g r U Q P₁)
    (hprefix₂ : H15NormalizedRowSuperperiodAbelPrefixBound N g r U Q P₂)
    (hboundary : H15CorrectionCoupledFinalBoundaryEstimate N g r U Q B) :
    |h15NormalizedProgressionRowToPointwiseResidual N g r U Q| ≤
      2 * (g.divisors.card : ℝ) * P₁ +
        4 * (g.divisors.card : ℝ) * P₂ + B := by
  apply abs_h15NormalizedProgressionRowToPointwiseResidual_le_twoPrefixes
    hN hg hU hQ hprefix₁ hprefix₂
  rw [h15NormalizedProgressionCorrectionCoupledSuperperiodBoundaryAggregate_eq_pointwise
    hQ]
  exact hboundary.2

end NBMellinTools.NB12
