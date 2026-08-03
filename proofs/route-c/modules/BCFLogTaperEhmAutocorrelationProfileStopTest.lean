import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmReferenceProfiles

/-!
# Stop test for the autocorrelation reference profile

The positive-projected `R₁` profile is aligned with the exact Ehm divisor
blocks.  This file expands its approximation error without inequalities.
For a raw signed block `A_k`, retained correction `C`, and allocation weight
`w_k`, the completed block is `A_k + w_k C`, while the reference is `A_k⁺`.
Consequently

`completed_k - reference_k = w_k C - A_k⁻`.

Thus the profile route is exactly a transport problem: the nonnegative
allocation must reproduce the negative mass of the raw Ehm blocks.  The
global mass mismatch `|C - ∑ A_k⁻|` is an unavoidable lower bound.  No decay
of this mismatch is asserted here.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmAutocorrelationProfileStopTest

open Filter
open scoped BigOperators Topology
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCoupledNearCoreTarget
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicCorrectionAbel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmEarlyBlockCorrection
open RH.Criteria.NymanBeurling.BCFLogTaperEhmExplicitFarCutoff
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRectangularInstantiation
open RH.Criteria.NymanBeurling.BCFLogTaperEhmReferenceProfiles

/-- Total negative mass of the raw signed `R₁` Ehm blocks, before the
retained correction is allocated. -/
noncomputable def ehmAutocorrelationRawNegativeMass (X J : ℕ) : ℝ :=
  ∑ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
    (ehmShiftedDyadicNearBlockSum ehmR1 X J
      (ehmH15NearMMax X) (ehmH15NearDMax X) k)⁻

theorem ehmAutocorrelationRawNegativeMass_nonneg (X J : ℕ) :
    0 ≤ ehmAutocorrelationRawNegativeMass X J := by
  unfold ehmAutocorrelationRawNegativeMass
  exact Finset.sum_nonneg fun k _ ↦ negPart_nonneg _

/-- Total absolute mass of the raw signed `R₁` Ehm blocks. -/
noncomputable def ehmAutocorrelationRawL1Mass (X J : ℕ) : ℝ :=
  ∑ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
    |ehmShiftedDyadicNearBlockSum ehmR1 X J
      (ehmH15NearMMax X) (ehmH15NearDMax X) k|

theorem ehmAutocorrelationRawNegativeMass_le_rawL1Mass (X J : ℕ) :
    ehmAutocorrelationRawNegativeMass X J ≤
      ehmAutocorrelationRawL1Mass X J := by
  unfold ehmAutocorrelationRawNegativeMass ehmAutocorrelationRawL1Mass
  apply Finset.sum_le_sum
  intro k _
  simpa using negPart_le_abs_sub_reference
    (ehmShiftedDyadicNearBlockSum ehmR1 X J
      (ehmH15NearMMax X) (ehmH15NearDMax X) k) 0 (le_refl 0)

@[simp]
theorem ehmAutocorrelationPositiveReferenceProfile_value
    (X J k : ℕ) :
    ehmAutocorrelationPositiveReferenceProfile.value X J k =
      (ehmShiftedDyadicNearBlockSum ehmR1 X J
        (ehmH15NearMMax X) (ehmH15NearDMax X) k)⁺ := by
  rfl

/-- Pointwise expansion of the autocorrelation-profile error. -/
theorem completed_sub_autocorrelationReference_eq_allocated_sub_negPart
    (X J k : ℕ)
    (A : EhmDyadicCorrectionAllocation X (ehmH15NearDMax X)) :
    ehmCorrectionCompletedDyadicAbelBlock ehmR1 X J
        (ehmH15NearMMax X) (ehmH15NearDMax X) A k -
        ehmAutocorrelationPositiveReferenceProfile.value X J k =
      A.weight k * ehmH15RetainedCorrection ehmR1 X J -
        (ehmShiftedDyadicNearBlockSum ehmR1 X J
          (ehmH15NearMMax X) (ehmH15NearDMax X) k)⁻ := by
  rw [ehmAutocorrelationPositiveReferenceProfile_value]
  unfold ehmCorrectionCompletedDyadicAbelBlock
  rw [← ehmShiftedDyadicNearBlockSum_eq_abel]
  linarith [posPart_sub_negPart
    (ehmShiftedDyadicNearBlockSum ehmR1 X J
      (ehmH15NearMMax X) (ehmH15NearDMax X) k)]

/-- Exact global `L¹` transport cost for the autocorrelation reference. -/
theorem ehmReferenceProfileL1Deviation_autocorrelation_eq
    (X J : ℕ)
    (A : EhmDyadicCorrectionAllocation X (ehmH15NearDMax X)) :
    ehmReferenceProfileL1Deviation
        ehmAutocorrelationPositiveReferenceProfile X J A =
      ∑ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
        |A.weight k * ehmH15RetainedCorrection ehmR1 X J -
          (ehmShiftedDyadicNearBlockSum ehmR1 X J
            (ehmH15NearMMax X) (ehmH15NearDMax X) k)⁻| := by
  unfold ehmReferenceProfileL1Deviation
  apply Finset.sum_congr rfl
  intro k _
  rw [completed_sub_autocorrelationReference_eq_allocated_sub_negPart]

/-- The signed sum of the block mismatches is the difference between the
retained correction and the total raw negative mass. -/
theorem sum_allocated_sub_negPart_eq_correction_sub_rawNegativeMass
    (X J : ℕ)
    (A : EhmDyadicCorrectionAllocation X (ehmH15NearDMax X)) :
    (∑ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
      (A.weight k * ehmH15RetainedCorrection ehmR1 X J -
        (ehmShiftedDyadicNearBlockSum ehmR1 X J
          (ehmH15NearMMax X) (ehmH15NearDMax X) k)⁻)) =
      ehmH15RetainedCorrection ehmR1 X J -
        ehmAutocorrelationRawNegativeMass X J := by
  unfold ehmAutocorrelationRawNegativeMass
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, A.mass_one, one_mul]

/-- Allocation-independent stop test: no nonnegative unit-mass allocation
can make the profile deviation smaller than the global mass mismatch. -/
theorem abs_correction_sub_rawNegativeMass_le_autocorrelationL1
    (X J : ℕ)
    (A : EhmDyadicCorrectionAllocation X (ehmH15NearDMax X)) :
    |ehmH15RetainedCorrection ehmR1 X J -
        ehmAutocorrelationRawNegativeMass X J| ≤
      ehmReferenceProfileL1Deviation
        ehmAutocorrelationPositiveReferenceProfile X J A := by
  rw [ehmReferenceProfileL1Deviation_autocorrelation_eq,
    ← sum_allocated_sub_negPart_eq_correction_sub_rawNegativeMass X J A]
  exact Finset.abs_sum_le_sum_abs _ _

/-- If the retained correction is nonpositive, every transport mismatch has
the same sign and the `L¹` cost is exactly `rawNegativeMass - correction`.
In this regime the profile creates no hidden cancellation. -/
theorem ehmReferenceProfileL1Deviation_autocorrelation_eq_of_correction_nonpos
    (X J : ℕ)
    (A : EhmDyadicCorrectionAllocation X (ehmH15NearDMax X))
    (hC : ehmH15RetainedCorrection ehmR1 X J ≤ 0) :
    ehmReferenceProfileL1Deviation
        ehmAutocorrelationPositiveReferenceProfile X J A =
      ehmAutocorrelationRawNegativeMass X J -
        ehmH15RetainedCorrection ehmR1 X J := by
  rw [ehmReferenceProfileL1Deviation_autocorrelation_eq]
  unfold ehmAutocorrelationRawNegativeMass
  calc
    (∑ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
        |A.weight k * ehmH15RetainedCorrection ehmR1 X J -
          (ehmShiftedDyadicNearBlockSum ehmR1 X J
            (ehmH15NearMMax X) (ehmH15NearDMax X) k)⁻|) =
      ∑ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
        ((ehmShiftedDyadicNearBlockSum ehmR1 X J
          (ehmH15NearMMax X) (ehmH15NearDMax X) k)⁻ -
          A.weight k * ehmH15RetainedCorrection ehmR1 X J) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [abs_of_nonpos]
      · ring
      · exact sub_nonpos.mpr
          ((mul_nonpos_of_nonneg_of_nonpos (A.weight_nonneg k) hC).trans
            (negPart_nonneg _))
    _ = (∑ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
          (ehmShiftedDyadicNearBlockSum ehmR1 X J
            (ehmH15NearMMax X) (ehmH15NearDMax X) k)⁻) -
        ehmH15RetainedCorrection ehmR1 X J := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, A.mass_one, one_mul]

/-- Allocation-free upper bound.  It shows that the positive-projection
profile is controlled by the same uncoupled absolute mass as the original
triangle route; the profile alone does not manufacture cancellation. -/
theorem ehmReferenceProfileL1Deviation_autocorrelation_le
    (X J : ℕ)
    (A : EhmDyadicCorrectionAllocation X (ehmH15NearDMax X)) :
    ehmReferenceProfileL1Deviation
        ehmAutocorrelationPositiveReferenceProfile X J A ≤
      |ehmH15RetainedCorrection ehmR1 X J| +
        ehmAutocorrelationRawNegativeMass X J := by
  rw [ehmReferenceProfileL1Deviation_autocorrelation_eq]
  calc
    (∑ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
      |A.weight k * ehmH15RetainedCorrection ehmR1 X J -
        (ehmShiftedDyadicNearBlockSum ehmR1 X J
          (ehmH15NearMMax X) (ehmH15NearDMax X) k)⁻|) ≤
      ∑ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
        (A.weight k * |ehmH15RetainedCorrection ehmR1 X J| +
          (ehmShiftedDyadicNearBlockSum ehmR1 X J
            (ehmH15NearMMax X) (ehmH15NearDMax X) k)⁻) := by
      apply Finset.sum_le_sum
      intro k _
      calc
        |A.weight k * ehmH15RetainedCorrection ehmR1 X J -
            (ehmShiftedDyadicNearBlockSum ehmR1 X J
              (ehmH15NearMMax X) (ehmH15NearDMax X) k)⁻| ≤
          |A.weight k * ehmH15RetainedCorrection ehmR1 X J| +
            |(ehmShiftedDyadicNearBlockSum ehmR1 X J
              (ehmH15NearMMax X) (ehmH15NearDMax X) k)⁻| :=
          abs_sub _ _
        _ = A.weight k * |ehmH15RetainedCorrection ehmR1 X J| +
            (ehmShiftedDyadicNearBlockSum ehmR1 X J
              (ehmH15NearMMax X) (ehmH15NearDMax X) k)⁻ := by
          rw [abs_mul, abs_of_nonneg (A.weight_nonneg k),
            abs_of_nonneg (negPart_nonneg _)]
    _ = |ehmH15RetainedCorrection ehmR1 X J| +
        ehmAutocorrelationRawNegativeMass X J := by
      unfold ehmAutocorrelationRawNegativeMass
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, A.mass_one, one_mul]

/-- The signed global core is bounded by the raw block `L¹` mass plus the
retained correction. -/
theorem abs_coupledNearCore_le_rawL1Mass_add_correction
    (X J : ℕ) (hX : 1 ≤ X) :
    |ehmDyadicExplicitCoupledNearCore ehmR1 X
        (ehmExplicitFarCutoff X) J| ≤
      ehmAutocorrelationRawL1Mass X J +
        |ehmH15RetainedCorrection ehmR1 X J| := by
  let A := ehmGeometricCorrectionAllocation X (ehmH15NearDMax X)
  rw [← sum_ehmCorrectionCompletedDyadicAbelBlock_eq_coupledNearCore
    ehmR1 X J A hX]
  calc
    |∑ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
        ehmCorrectionCompletedDyadicAbelBlock ehmR1 X J
          (ehmH15NearMMax X) (ehmH15NearDMax X) A k| =
      |(∑ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
          ehmShiftedDyadicNearBlockSum ehmR1 X J
            (ehmH15NearMMax X) (ehmH15NearDMax X) k) +
        ehmH15RetainedCorrection ehmR1 X J| := by
      congr 1
      unfold ehmCorrectionCompletedDyadicAbelBlock
      rw [Finset.sum_add_distrib, ← Finset.sum_mul,
        A.mass_one, one_mul]
      simp_rw [← ehmShiftedDyadicNearBlockSum_eq_abel]
    _ ≤ |∑ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
        ehmShiftedDyadicNearBlockSum ehmR1 X J
            (ehmH15NearMMax X) (ehmH15NearDMax X) k| +
        |ehmH15RetainedCorrection ehmR1 X J| := abs_add_le _ _
    _ ≤ (∑ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
          |ehmShiftedDyadicNearBlockSum ehmR1 X J
            (ehmH15NearMMax X) (ehmH15NearDMax X) k|) +
        |ehmH15RetainedCorrection ehmR1 X J| :=
      by
        have hsum := Finset.abs_sum_le_sum_abs
          (fun k ↦ ehmShiftedDyadicNearBlockSum ehmR1 X J
            (ehmH15NearMMax X) (ehmH15NearDMax X) k)
          (ehmShiftedDyadicDIndices X (ehmH15NearDMax X))
        linarith
    _ = ehmAutocorrelationRawL1Mass X J +
        |ehmH15RetainedCorrection ehmR1 X J| := by
      rfl

/-! ## A precise sufficient target, and its limitation -/

/-- Sublinear uncoupled mass is sufficient for both the global signed-core
field and the autocorrelation-profile deviation.  This is a clean target,
but it is not yet an improvement over the original triangle estimate. -/
structure EhmAutocorrelationRawL1SublinearBound where
  eta : ℕ → ℝ
  eta_nonneg : ∀ X, 0 ≤ eta X
  eta_tendsto_zero : Tendsto eta atTop (nhds 0)
  cofinal_bound : ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      ehmExplicitFarCutoff X ≤ J ∧
      ehmAutocorrelationRawL1Mass X J +
          |ehmH15RetainedCorrection ehmR1 X J| ≤
        ((ehmDyadicNBlock X).card : ℝ) * eta X

/-- The uncoupled sublinear target instantiates the complete `L¹` reference
package with the fixed geometric allocation. -/
noncomputable def EhmAutocorrelationRawL1SublinearBound.toReferenceL1Decay
    (H : EhmAutocorrelationRawL1SublinearBound) :
    EhmReferenceProfileL1Decay where
  profile := ehmAutocorrelationPositiveReferenceProfile
  allocation X := ehmGeometricCorrectionAllocation X (ehmH15NearDMax X)
  etaCore := H.eta
  etaCore_nonneg := H.eta_nonneg
  etaCore_tendsto_zero := H.eta_tendsto_zero
  etaL1 := H.eta
  etaL1_nonneg := H.eta_nonneg
  etaL1_tendsto_zero := H.eta_tendsto_zero
  cofinal_core_and_reference_bound X hX :=
    (H.cofinal_bound X hX).mono fun J hJ ↦ by
      refine ⟨hJ.1, ?_, ?_⟩
      · exact (abs_coupledNearCore_le_rawL1Mass_add_correction X J
          (by omega)).trans hJ.2
      · calc
          ehmReferenceProfileL1Deviation
              ehmAutocorrelationPositiveReferenceProfile X J
              (ehmGeometricCorrectionAllocation X (ehmH15NearDMax X)) ≤
            |ehmH15RetainedCorrection ehmR1 X J| +
              ehmAutocorrelationRawNegativeMass X J :=
            ehmReferenceProfileL1Deviation_autocorrelation_le X J _
          _ ≤ ehmAutocorrelationRawL1Mass X J +
              |ehmH15RetainedCorrection ehmR1 X J| := by
            linarith [ehmAutocorrelationRawNegativeMass_le_rawL1Mass X J]
          _ ≤ ((ehmDyadicNBlock X).card : ℝ) * H.eta X := hJ.2

/-- Conditional closure from the now-explicit uncoupled stop-test target. -/
theorem baezDuarteCriterion_of_ehmAutocorrelationRawL1SublinearBound
    (H : EhmAutocorrelationRawL1SublinearBound) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmReferenceProfileL1Decay H.toReferenceL1Decay

/-- A practical two-track formulation.  The raw block `L¹` estimate is only
required cofinally in `J`, whereas the elementary/main correction estimate
is uniform for every admissible `J`.  This asymmetry permits combination
without the invalid intersection of two merely frequent sets. -/
structure EhmAutocorrelationSeparatedSublinearBounds where
  etaRaw : ℕ → ℝ
  etaRaw_nonneg : ∀ X, 0 ≤ etaRaw X
  etaRaw_tendsto_zero : Tendsto etaRaw atTop (nhds 0)
  etaCorrection : ℕ → ℝ
  etaCorrection_nonneg : ∀ X, 0 ≤ etaCorrection X
  etaCorrection_tendsto_zero : Tendsto etaCorrection atTop (nhds 0)
  cofinal_raw_bound : ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      ehmExplicitFarCutoff X ≤ J ∧
      ehmAutocorrelationRawL1Mass X J ≤
        ((ehmDyadicNBlock X).card : ℝ) * etaRaw X
  uniform_correction_bound : ∀ X J : ℕ, 2 ≤ X →
    ehmExplicitFarCutoff X ≤ J →
    |ehmH15RetainedCorrection ehmR1 X J| ≤
      ((ehmDyadicNBlock X).card : ℝ) * etaCorrection X

/-- The two-track target supplies the combined raw `L¹` target on the same
cofinal set. -/
noncomputable def EhmAutocorrelationSeparatedSublinearBounds.toRawL1Bound
    (H : EhmAutocorrelationSeparatedSublinearBounds) :
    EhmAutocorrelationRawL1SublinearBound where
  eta := fun X ↦ H.etaRaw X + H.etaCorrection X
  eta_nonneg X := add_nonneg (H.etaRaw_nonneg X)
    (H.etaCorrection_nonneg X)
  eta_tendsto_zero := by
    simpa using H.etaRaw_tendsto_zero.add H.etaCorrection_tendsto_zero
  cofinal_bound X hX :=
    (H.cofinal_raw_bound X hX).mono fun J hJ ↦ by
      refine ⟨hJ.1, ?_⟩
      calc
        ehmAutocorrelationRawL1Mass X J +
            |ehmH15RetainedCorrection ehmR1 X J| ≤
          ((ehmDyadicNBlock X).card : ℝ) * H.etaRaw X +
            ((ehmDyadicNBlock X).card : ℝ) * H.etaCorrection X :=
          add_le_add hJ.2 (H.uniform_correction_bound X J hX hJ.1)
        _ = ((ehmDyadicNBlock X).card : ℝ) *
            (H.etaRaw X + H.etaCorrection X) := by ring

/-- Conditional closure from the separated raw/correction programme. -/
theorem baezDuarteCriterion_of_ehmAutocorrelationSeparatedSublinearBounds
    (H : EhmAutocorrelationSeparatedSublinearBounds) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmAutocorrelationRawL1SublinearBound
    H.toRawL1Bound

/-! ## Necessary asymptotic consequence of an `L¹` profile package -/

/-- Any successful autocorrelation-profile `L¹` package must in particular
make the allocation-independent global mass mismatch small on the same
cofinal set. -/
theorem EhmReferenceProfileL1Decay.autocorrelation_massMatching_necessary
    (H : EhmReferenceProfileL1Decay)
    (hprofile : H.profile = ehmAutocorrelationPositiveReferenceProfile)
    (X : ℕ) (hX : 2 ≤ X) :
    ∃ᶠ J : ℕ in atTop,
      ehmExplicitFarCutoff X ≤ J ∧
      |ehmH15RetainedCorrection ehmR1 X J -
          ehmAutocorrelationRawNegativeMass X J| ≤
        ((ehmDyadicNBlock X).card : ℝ) * H.etaL1 X := by
  exact (H.cofinal_core_and_reference_bound X hX).mono fun J hJ ↦ by
    refine ⟨hJ.1, ?_⟩
    rw [hprofile] at hJ
    exact (abs_correction_sub_rawNegativeMass_le_autocorrelationL1
      X J (H.allocation X)).trans hJ.2.2

end RH.Criteria.NymanBeurling.BCFLogTaperEhmAutocorrelationProfileStopTest
