import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmCompletedBlockResidue
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmSignedTransferAudit
import RiemannHypothesis.Criteria.NymanBeurling.RHBridge

/-!
# The global correction laboratory

This file certifies the logical frontier of the completed-block programme.
For a finite family of contour modes it defines

* the truncated and full global correction defects;
* the zero-extended mismatch and its prefix potential;
* the exact finite Abel/coboundary identity; and
* a cofinal closure contract in which the signed physical sum and the
  global correction defect are controlled on the same hyperbolic cutoffs.

The prefix construction proves that every finite mismatch is formally a
coboundary.  Its terminal value is, however, exactly the original global
defect.  Thus this universal telescoping is bookkeeping rather than an
analytic cancellation theorem.

The final contract allows an approximate defect.  Exact global matching is
the special case in which its defect majorant is zero.  The contract still
contains the H15-strength signed physical-sum estimate, and the conversion to
RH keeps both the rational-series bridge and the forward Nyman--Beurling
bridge explicit.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmGlobalCorrectionLaboratory

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCompletedBlockResidue
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCoupledNearCoreTarget
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCutoffAverageMainTerm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicCorrectionAbel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmEarlyBlockCorrection
open RH.Criteria.NymanBeurling.BCFLogTaperEhmExplicitFarCutoff
open RH.Criteria.NymanBeurling.BCFLogTaperEhmHyperbolicKernelNormalForm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRectangularInstantiation

/-! ## WP0: finite and global defects -/

/-- The correction mismatch accumulated only through dyadic index `K`. -/
noncomputable def ehmCompletedBlockTruncatedDefect
    (R1 : ℝ → ℝ) (X J L K : ℕ)
    (A : EhmDyadicCorrectionAllocation X L)
    (Z : EhmCompletedBlockContourModes) : ℝ :=
  ∑ k ∈ ehmEarlyDyadicDIndices X L K,
    ehmCompletedBlockCorrectionMismatch R1 X J L A Z k

/-- A truncated defect is the truncated physical mass minus precisely the
correction mass allocated to the same blocks. -/
theorem ehmCompletedBlockTruncatedDefect_eq
    (R1 : ℝ → ℝ) (X J L K : ℕ)
    (A : EhmDyadicCorrectionAllocation X L)
    (Z : EhmCompletedBlockContourModes) :
    ehmCompletedBlockTruncatedDefect R1 X J L K A Z =
      (∑ k ∈ ehmEarlyDyadicDIndices X L K,
        ehmCompletedBlockPhysicalMode Z k) -
      (∑ k ∈ ehmEarlyDyadicDIndices X L K, A.weight k) *
        ehmH15RetainedCorrection R1 X J := by
  classical
  unfold ehmCompletedBlockTruncatedDefect
    ehmCompletedBlockCorrectionMismatch
  rw [Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_mul]

/-- The full, allocation-independent global correction defect. -/
noncomputable def ehmCompletedBlockGlobalDefect
    (R1 : ℝ → ℝ) (X J L : ℕ)
    (Z : EhmCompletedBlockContourModes) : ℝ :=
  (∑ k ∈ ehmShiftedDyadicDIndices X L,
    ehmCompletedBlockPhysicalMode Z k) -
    ehmH15RetainedCorrection R1 X J

/-- Summing any unit-mass allocation's local mismatches produces the same
global defect. -/
theorem sum_mismatch_eq_globalDefect
    (R1 : ℝ → ℝ) (X J L : ℕ)
    (A : EhmDyadicCorrectionAllocation X L)
    (Z : EhmCompletedBlockContourModes) :
    (∑ k ∈ ehmShiftedDyadicDIndices X L,
      ehmCompletedBlockCorrectionMismatch R1 X J L A Z k) =
      ehmCompletedBlockGlobalDefect R1 X J L Z := by
  exact sum_ehmCompletedBlockCorrectionMismatch R1 X J L A Z

/-- Global matching is exactly zero global defect.  This is a finite
normalization equivalence, not an asymptotic decay statement. -/
theorem globalDefect_eq_zero_iff
    (R1 : ℝ → ℝ) (X J L : ℕ)
    (Z : EhmCompletedBlockContourModes) :
    ehmCompletedBlockGlobalDefect R1 X J L Z = 0 ↔
      (∑ k ∈ ehmShiftedDyadicDIndices X L,
        ehmCompletedBlockPhysicalMode Z k) =
        ehmH15RetainedCorrection R1 X J := by
  unfold ehmCompletedBlockGlobalDefect
  exact sub_eq_zero

/-! ## WP1: the universal finite coboundary ledger -/

/-- Extend the finite mismatch by zero outside the actual dyadic index set. -/
noncomputable def ehmCompletedBlockExtendedMismatch
    (R1 : ℝ → ℝ) (X J L : ℕ)
    (A : EhmDyadicCorrectionAllocation X L)
    (Z : EhmCompletedBlockContourModes) (k : ℕ) : ℝ :=
  if k ∈ ehmShiftedDyadicDIndices X L then
    ehmCompletedBlockCorrectionMismatch R1 X J L A Z k
  else 0

/-- Prefix potential of the zero-extended mismatch. -/
noncomputable def ehmCompletedBlockMismatchPrefix
    (R1 : ℝ → ℝ) (X J L : ℕ)
    (A : EhmDyadicCorrectionAllocation X L)
    (Z : EhmCompletedBlockContourModes) (r : ℕ) : ℝ :=
  ∑ k ∈ Finset.range r,
    ehmCompletedBlockExtendedMismatch R1 X J L A Z k

theorem ehmCompletedBlockMismatchPrefix_zero
    (R1 : ℝ → ℝ) (X J L : ℕ)
    (A : EhmDyadicCorrectionAllocation X L)
    (Z : EhmCompletedBlockContourModes) :
    ehmCompletedBlockMismatchPrefix R1 X J L A Z 0 = 0 := by
  simp [ehmCompletedBlockMismatchPrefix]

/-- Every finite mismatch sequence is tautologically the discrete derivative
of its prefix potential. -/
theorem ehmCompletedBlockMismatchPrefix_succ_sub
    (R1 : ℝ → ℝ) (X J L r : ℕ)
    (A : EhmDyadicCorrectionAllocation X L)
    (Z : EhmCompletedBlockContourModes) :
    ehmCompletedBlockMismatchPrefix R1 X J L A Z (r + 1) -
        ehmCompletedBlockMismatchPrefix R1 X J L A Z r =
      ehmCompletedBlockExtendedMismatch R1 X J L A Z r := by
  unfold ehmCompletedBlockMismatchPrefix
  rw [Finset.sum_range_succ]
  ring

/-- On an actual block, the correction-completed transform is the physical
transform minus the discrete derivative of the prefix potential. -/
theorem correctionCompletedBlock_eq_physical_sub_prefixDifference
    (R1 : ℝ → ℝ) (X J M L k : ℕ)
    (A : EhmDyadicCorrectionAllocation X L)
    (Z : EhmCompletedBlockContourModes)
    (hk : k ∈ ehmShiftedDyadicDIndices X L) :
    ehmCorrectionCompletedDyadicAbelBlock R1 X J M L A k =
      ehmCompletedBlockPhysicalTransform R1 X J M L Z k -
        (ehmCompletedBlockMismatchPrefix R1 X J L A Z (k + 1) -
          ehmCompletedBlockMismatchPrefix R1 X J L A Z k) := by
  rw [ehmCompletedBlockMismatchPrefix_succ_sub]
  simp only [ehmCompletedBlockExtendedMismatch, hk, if_true]
  exact ehmCorrectionCompletedDyadicAbelBlock_eq_physical_sub_mismatch
    R1 X J M L k A Z

/-- At the finite supremum, the prefix potential is exactly the full sum of
local mismatches. -/
theorem ehmCompletedBlockMismatchPrefix_terminal_eq_sum
    (R1 : ℝ → ℝ) (X J L : ℕ)
    (A : EhmDyadicCorrectionAllocation X L)
    (Z : EhmCompletedBlockContourModes) :
    ehmCompletedBlockMismatchPrefix R1 X J L A Z
        (ehmAllDyadicCutoff X L + 1) =
      ∑ k ∈ ehmShiftedDyadicDIndices X L,
        ehmCompletedBlockCorrectionMismatch R1 X J L A Z k := by
  classical
  unfold ehmCompletedBlockMismatchPrefix
    ehmCompletedBlockExtendedMismatch
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun hk ↦ hk.2
    · intro hk
      exact ⟨by
        have hle := le_ehmAllDyadicCutoff_of_mem hk
        omega, hk⟩
  · intro k _
    rfl

/-- The terminal prefix is exactly the original global correction defect. -/
theorem ehmCompletedBlockMismatchPrefix_terminal_eq_globalDefect
    (R1 : ℝ → ℝ) (X J L : ℕ)
    (A : EhmDyadicCorrectionAllocation X L)
    (Z : EhmCompletedBlockContourModes) :
    ehmCompletedBlockMismatchPrefix R1 X J L A Z
        (ehmAllDyadicCutoff X L + 1) =
      ehmCompletedBlockGlobalDefect R1 X J L Z := by
  rw [ehmCompletedBlockMismatchPrefix_terminal_eq_sum,
    sum_mismatch_eq_globalDefect]

/-- Consequently the universal coboundary closes at its upper endpoint if
and only if the original global matching statement already holds. -/
theorem ehmCompletedBlockMismatchPrefix_terminal_eq_zero_iff
    (R1 : ℝ → ℝ) (X J L : ℕ)
    (A : EhmDyadicCorrectionAllocation X L)
    (Z : EhmCompletedBlockContourModes) :
    ehmCompletedBlockMismatchPrefix R1 X J L A Z
        (ehmAllDyadicCutoff X L + 1) = 0 ↔
      (∑ k ∈ ehmShiftedDyadicDIndices X L,
        ehmCompletedBlockPhysicalMode Z k) =
        ehmH15RetainedCorrection R1 X J := by
  rw [ehmCompletedBlockMismatchPrefix_terminal_eq_globalDefect]
  exact globalDefect_eq_zero_iff R1 X J L Z

/-- Exact summation by parts for a test function against the finite defect.
The terminal prefix is the boundary term; global matching removes only this
term and does not bound the remaining variation-weighted prefixes. -/
theorem sum_weight_mul_extendedMismatch_by_parts
    (R1 : ℝ → ℝ) (X J L : ℕ)
    (A : EhmDyadicCorrectionAllocation X L)
    (Z : EhmCompletedBlockContourModes)
    (phi : ℕ → ℝ) :
    let B := ehmAllDyadicCutoff X L
    (∑ k ∈ Finset.range (B + 1),
        phi k * ehmCompletedBlockExtendedMismatch R1 X J L A Z k) =
      phi B * ehmCompletedBlockMismatchPrefix R1 X J L A Z (B + 1) -
        ∑ k ∈ Finset.range B, (phi (k + 1) - phi k) *
          ehmCompletedBlockMismatchPrefix R1 X J L A Z (k + 1) := by
  dsimp only
  simpa only [smul_eq_mul, Nat.add_sub_cancel] using
    (Finset.sum_range_by_parts phi
      (ehmCompletedBlockExtendedMismatch R1 X J L A Z)
      (ehmAllDyadicCutoff X L + 1))

/-- Two opposite spikes are the minimal finite countermodel to the claim
that zero total defect controls intermediate prefixes. -/
def globalCorrectionTwoSpike (T : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then T else if k = 1 then -T else 0

theorem sum_globalCorrectionTwoSpike (T : ℝ) :
    (∑ k ∈ Finset.range 2, globalCorrectionTwoSpike T k) = 0 := by
  norm_num [globalCorrectionTwoSpike, Finset.sum_range_succ]

theorem firstPrefix_globalCorrectionTwoSpike (T : ℝ) :
    (∑ k ∈ Finset.range 1, globalCorrectionTwoSpike T k) = T := by
  norm_num [globalCorrectionTwoSpike, Finset.sum_range_succ]

/-! ## WP2 baseline: finite smoothing does not hide the boundary -/

/-- A finite semigroup-weighted mismatch polynomial.  This is an algebraic
baseline; a genuine H15 smoothing route must still derive its deformed
correction independently from the contour. -/
noncomputable def ehmCompletedBlockSmoothedDefect
    (R1 : ℝ → ℝ) (X J L : ℕ)
    (A : EhmDyadicCorrectionAllocation X L)
    (Z : EhmCompletedBlockContourModes)
    (lambda : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (ehmAllDyadicCutoff X L + 1),
    Real.exp (-t * lambda k) *
      ehmCompletedBlockExtendedMismatch R1 X J L A Z k

/-- The physical boundary `t=0` of every finite smoothing is exactly the
unsmoothed global defect, independently of the chosen scale `lambda`. -/
theorem ehmCompletedBlockSmoothedDefect_zero
    (R1 : ℝ → ℝ) (X J L : ℕ)
    (A : EhmDyadicCorrectionAllocation X L)
    (Z : EhmCompletedBlockContourModes)
    (lambda : ℕ → ℝ) :
    ehmCompletedBlockSmoothedDefect R1 X J L A Z lambda 0 =
      ehmCompletedBlockGlobalDefect R1 X J L Z := by
  unfold ehmCompletedBlockSmoothedDefect
  simp only [zero_mul, neg_zero, Real.exp_zero, one_mul]
  exact ehmCompletedBlockMismatchPrefix_terminal_eq_globalDefect
    R1 X J L A Z

/-! ## Certified cofinal frontier and closure chain -/

/-- The exact identity used by the cofinal contract: the H15 near core is
the signed physical transform minus the global correction defect. -/
theorem ehmDyadicExplicitCoupledNearCore_eq_physical_sub_globalDefect
    (R1 : ℝ → ℝ) (X J : ℕ)
    (Z : EhmCompletedBlockContourModes) (hX : 1 ≤ X) :
    ehmDyadicExplicitCoupledNearCore R1 X (ehmExplicitFarCutoff X) J =
      (∑ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
        ehmCompletedBlockPhysicalTransform R1 X J
          (ehmH15NearMMax X) (ehmH15NearDMax X) Z k) -
      ehmCompletedBlockGlobalDefect R1 X J (ehmH15NearDMax X) Z := by
  rw [ehmDyadicExplicitCoupledNearCore_eq_physical_sub_geometricMismatch
    R1 X J Z hX, sum_ehmGeometricCompletedBlockMismatch]
  rfl

/-- Machine-auditable frontier contract.  The physical sum and the global
defect are bounded on the same frequent set of hyperbolic cutoffs.  Keeping
them in one predicate avoids the invalid intersection of two merely
frequent sets.

The `modes` field remains an interface for a future contour localization;
constructing it from actual residue, zero, and diagonal formulas is part of
the analytic problem. -/
structure EhmCompletedBlockGlobalCofinalDecay where
  modes : ℕ → ℕ → EhmCompletedBlockContourModes
  etaPhysical : ℕ → ℝ
  etaPhysical_nonneg : ∀ X, 0 ≤ etaPhysical X
  etaPhysical_tendsto_zero : Tendsto etaPhysical atTop (nhds 0)
  etaDefect : ℕ → ℝ
  etaDefect_nonneg : ∀ X, 0 ≤ etaDefect X
  etaDefect_tendsto_zero : Tendsto etaDefect atTop (nhds 0)
  cofinal_joint_bound : ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      ehmExplicitFarCutoff X ≤ J ∧
      (∑ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
        ehmCompletedBlockPhysicalTransform ehmR1 X J
          (ehmH15NearMMax X) (ehmH15NearDMax X) (modes X J) k) ≤
        ((ehmDyadicNBlock X).card : ℝ) * etaPhysical X ∧
      |ehmCompletedBlockGlobalDefect ehmR1 X J
        (ehmH15NearDMax X) (modes X J)| ≤
        ((ehmDyadicNBlock X).card : ℝ) * etaDefect X

/-- The joint physical/defect contract yields the existing signed kernel
gate with null majorant `etaPhysical + etaDefect`. -/
noncomputable def EhmCompletedBlockGlobalCofinalDecay.toKernelGate
    (H : EhmCompletedBlockGlobalCofinalDecay) :
    EhmDyadicExplicitKernelCoupledAnalyticGate where
  U := fun X ↦ 2 * X
  U_le := fun _ ↦ le_rfl
  eta := fun X ↦ H.etaPhysical X + H.etaDefect X
  eta_nonneg X := add_nonneg (H.etaPhysical_nonneg X)
    (H.etaDefect_nonneg X)
  eta_tendsto_zero := by
    simpa using H.etaPhysical_tendsto_zero.add H.etaDefect_tendsto_zero
  cofinal_bound X hX :=
    (H.cofinal_joint_bound X hX).mono fun J hJ ↦ by
      refine ⟨hJ.1, ?_⟩
      rw [← ehmDyadicExplicitCutoffCoupledNearCore_eq_kernelTypeI_typeII
        ehmR1 X J (2 * X) le_rfl]
      rw [ehmDyadicExplicitCoupledNearCore_eq_physical_sub_globalDefect
        ehmR1 X J (H.modes X J) (by omega)]
      calc
        (∑ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
            ehmCompletedBlockPhysicalTransform ehmR1 X J
              (ehmH15NearMMax X) (ehmH15NearDMax X) (H.modes X J) k) -
            ehmCompletedBlockGlobalDefect ehmR1 X J
              (ehmH15NearDMax X) (H.modes X J) ≤
          (∑ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
            ehmCompletedBlockPhysicalTransform ehmR1 X J
              (ehmH15NearMMax X) (ehmH15NearDMax X) (H.modes X J) k) +
            |ehmCompletedBlockGlobalDefect ehmR1 X J
              (ehmH15NearDMax X) (H.modes X J)| := by
                linarith [neg_le_abs (ehmCompletedBlockGlobalDefect ehmR1 X J
                  (ehmH15NearDMax X) (H.modes X J))]
        _ ≤ ((ehmDyadicNBlock X).card : ℝ) * H.etaPhysical X +
            ((ehmDyadicNBlock X).card : ℝ) * H.etaDefect X :=
              add_le_add hJ.2.1 hJ.2.2
        _ = ((ehmDyadicNBlock X).card : ℝ) *
            (H.etaPhysical X + H.etaDefect X) := by ring

/-- The certified frontier contract implies the Báez--Duarte criterion once
the rational `R₁`-series bridge is supplied. -/
theorem baezDuarteCriterion_of_globalCorrectionCofinalDecay
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (H : EhmCompletedBlockGlobalCofinalDecay) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmDyadicExplicitKernelCoupledAnalyticGate
    HS H.toKernelGate

/-- Full RH handoff with both independent analytic bridges explicit.  No
global-correction package is silently identified with RH. -/
theorem riemannHypothesis_of_globalCorrectionCofinalDecay
    (hNB : RH.Criteria.NymanBeurling.RHBridge.NBForward)
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (H : EhmCompletedBlockGlobalCofinalDecay) :
    RH.Basic.RiemannHypothesis :=
  hNB (nymanBeurlingCriterion_iff_baezDuarteCriterion.mpr
    (baezDuarteCriterion_of_globalCorrectionCofinalDecay HS H))

end RH.Criteria.NymanBeurling.BCFLogTaperEhmGlobalCorrectionLaboratory
