import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmCorrectionTriangleLoss
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperH15ContourTraceModes

/-!
# Nonnegative reference profiles for the correction-completed Ehm blocks

This file formalizes the valid part of the reference-profile strategy.  A
nonnegative profile controls the negative mass of the completed blocks by
its `L¹` approximation error.  An `L²` estimate also suffices, but only with
the Cauchy--Schwarz factor equal to the square root of the number of blocks.

Three concrete candidates are recorded:

* the positive projection of the genuine contour-residue block mode;
* the genuine Gram-diagonal block mode, which is already nonnegative; and
* the positive projection of the exact `R₁` Ehm dyadic block.

The projections in the first and third candidates are essential: the
complex residue produces a signed real mode after projection, and an `R₁`
block is also not nonnegative merely by its origin.  The contour profile is
only a sampled candidate, because the contour modes use dyadic gcd blocks
whereas the Ehm decomposition uses dyadic divisor blocks.  No unproved
identification of these two partitions is made.

Reference approximation controls only the minority-sign part of the H15
gate.  The global signed-core estimate remains a separate field in both the
`L¹` and `L²` packages below.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmReferenceProfiles

open Complex
open Filter
open scoped BigOperators Topology
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCorrectionTriangleLoss
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCoupledNearCoreTarget
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicCorrectionAbel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmExplicitFarCutoff
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRectangularInstantiation
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
open RH.Criteria.NymanBeurling.BCFLogTaperH15ContourTraceModes
open RH.Criteria.NymanBeurling.VasyuninGram
open RH.Criteria.NymanBeurling.RHBridge

/-! ## Abstract nonnegative profiles and finite transfer inequalities -/

/-- A block profile with a proved pointwise nonnegativity certificate. -/
structure EhmNonnegativeReferenceProfile where
  value : ℕ → ℕ → ℕ → ℝ
  nonneg : ∀ X J k, 0 ≤ value X J k

/-- `L¹` deviation of the correction-completed Ehm blocks from a reference
profile. -/
noncomputable def ehmReferenceProfileL1Deviation
    (P : EhmNonnegativeReferenceProfile) (X J : ℕ)
    (A : EhmDyadicCorrectionAllocation X (ehmH15NearDMax X)) : ℝ :=
  ∑ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
    |ehmCorrectionCompletedDyadicAbelBlock ehmR1 X J
        (ehmH15NearMMax X) (ehmH15NearDMax X) A k - P.value X J k|

/-- Euclidean (`L²`) deviation norm on the finite Ehm block set. -/
noncomputable def ehmReferenceProfileL2Deviation
    (P : EhmNonnegativeReferenceProfile) (X J : ℕ)
    (A : EhmDyadicCorrectionAllocation X (ehmH15NearDMax X)) : ℝ :=
  Real.sqrt
    (∑ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
      (ehmCorrectionCompletedDyadicAbelBlock ehmR1 X J
          (ehmH15NearMMax X) (ehmH15NearDMax X) A k - P.value X J k) ^ 2)

/-- The square-root block-count loss appearing in the finite `L² → L¹`
embedding. -/
noncomputable def ehmReferenceProfileBlockCountSqrt (X : ℕ) : ℝ :=
  Real.sqrt
    ((ehmShiftedDyadicDIndices X (ehmH15NearDMax X)).card : ℝ)

/-- A nonnegative reference absorbs the negative part of a real number up
to the pointwise approximation error. -/
theorem negPart_le_abs_sub_reference
    (b p : ℝ) (hp : 0 ≤ p) :
    b⁻ ≤ |b - p| := by
  by_cases hb : 0 ≤ b
  · simp [hb]
  · have hb' : b ≤ 0 := le_of_not_ge hb
    have hsub : b - p ≤ 0 := sub_nonpos.mpr (hb'.trans hp)
    rw [negPart_of_nonpos hb', abs_of_nonpos hsub]
    linarith

/-- The minority-sign mass is at most the `L¹` distance from any
nonnegative reference profile.  This is the central finite transfer lemma. -/
theorem ehmCorrectionCompletedMinorityMass_le_referenceL1
    (P : EhmNonnegativeReferenceProfile) (X J : ℕ)
    (A : EhmDyadicCorrectionAllocation X (ehmH15NearDMax X)) :
    min (ehmCorrectionCompletedPositiveMass ehmR1 X J A)
        (ehmCorrectionCompletedNegativeMass ehmR1 X J A) ≤
      ehmReferenceProfileL1Deviation P X J A := by
  calc
    min (ehmCorrectionCompletedPositiveMass ehmR1 X J A)
        (ehmCorrectionCompletedNegativeMass ehmR1 X J A) ≤
        ehmCorrectionCompletedNegativeMass ehmR1 X J A := min_le_right _ _
    _ ≤ ehmReferenceProfileL1Deviation P X J A := by
      unfold ehmCorrectionCompletedNegativeMass
        ehmReferenceProfileL1Deviation
      apply Finset.sum_le_sum
      intro k hk
      exact negPart_le_abs_sub_reference _ _ (P.nonneg X J k)

/-- Correct finite `L² → L¹` transfer.  The square-root block-count factor
cannot in general be omitted. -/
theorem ehmReferenceProfileL1Deviation_le_sqrtCard_mul_L2
    (P : EhmNonnegativeReferenceProfile) (X J : ℕ)
    (A : EhmDyadicCorrectionAllocation X (ehmH15NearDMax X)) :
    ehmReferenceProfileL1Deviation P X J A ≤
      ehmReferenceProfileBlockCountSqrt X *
        ehmReferenceProfileL2Deviation P X J A := by
  let s := ehmShiftedDyadicDIndices X (ehmH15NearDMax X)
  let e : ℕ → ℝ := fun k ↦
    ehmCorrectionCompletedDyadicAbelBlock ehmR1 X J
      (ehmH15NearMMax X) (ehmH15NearDMax X) A k - P.value X J k
  calc
    ehmReferenceProfileL1Deviation P X J A =
        ∑ k ∈ s, (1 : ℝ) * |e k| := by
      simp [ehmReferenceProfileL1Deviation, s, e]
    _ ≤ Real.sqrt (∑ k ∈ s, (1 : ℝ) ^ 2) *
        Real.sqrt (∑ k ∈ s, |e k| ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt s (fun _ ↦ (1 : ℝ)) (fun k ↦ |e k|)
    _ = ehmReferenceProfileBlockCountSqrt X *
        ehmReferenceProfileL2Deviation P X J A := by
      simp only [one_pow]
      simp [ehmReferenceProfileBlockCountSqrt,
        ehmReferenceProfileL2Deviation, s, e, sq_abs]

/-! ## Three corrected concrete candidates -/

/-- **Option A, corrected.**  The positive projection of the genuine
contour-residue block mode.  The numerical block label is sampled on the Ehm
index set; no equality between the gcd and divisor partitions is asserted. -/
noncomputable def ehmResiduePositiveReferenceProfile
    (η : ℝ) : EhmNonnegativeReferenceProfile where
  value X _ k :=
    (h15ContourResidueBlockMode
      (estermannGaussianEvaluationWeight η) (2 * X) k)⁺
  nonneg _ _ _ := posPart_nonneg _

/-- Every diagonal Gram slice is nonnegative directly from its integral
definition. -/
theorem h15GramDiagonalGcdSlice_nonneg (N g : ℕ) :
    0 ≤ h15GramDiagonalGcdSlice N g := by
  unfold h15GramDiagonalGcdSlice baezDuarteGramEntry
  have hgram : 0 ≤
      ∫ x in Set.Ioi (0 : ℝ),
        Int.fract (1 / ((g : ℝ) * x)) * Int.fract (1 / ((g : ℝ) * x)) := by
    exact MeasureTheory.integral_nonneg fun x ↦ mul_self_nonneg _
  exact mul_nonneg (mul_self_nonneg _) hgram

/-- The genuine Gram-diagonal block mode is nonnegative. -/
theorem h15GramDiagonalBlockMode_nonneg (N k : ℕ) :
    0 ≤ h15GramDiagonalBlockMode N k := by
  unfold h15GramDiagonalBlockMode
  exact Finset.sum_nonneg fun g _ ↦ h15GramDiagonalGcdSlice_nonneg N g

/-- Gram diagonal restricted to the exact shifted Ehm divisor fiber
`d = X + 1 + j`.  This avoids identifying the whole gcd partition with the
Ehm divisor partition. -/
noncomputable def ehmNearGramDiagonalReferenceValue (X k : ℕ) : ℝ :=
  ∑ j ∈ ehmShiftedDyadicDBlock X (ehmH15NearDMax X) k,
    h15GramDiagonalGcdSlice (2 * X) (X + 1 + j)

/-- The Ehm-fibered near diagonal is nonnegative. -/
theorem ehmNearGramDiagonalReferenceValue_nonneg (X k : ℕ) :
    0 ≤ ehmNearGramDiagonalReferenceValue X k := by
  unfold ehmNearGramDiagonalReferenceValue
  exact Finset.sum_nonneg fun j _ ↦
    h15GramDiagonalGcdSlice_nonneg (2 * X) (X + 1 + j)

/-- **Option B.**  The exact near Gram diagonal on the shifted Ehm divisor
fiber.  Unlike the residue and autocorrelation candidates, no positive
projection is needed. -/
noncomputable def ehmDiagonalReferenceProfile :
    EhmNonnegativeReferenceProfile where
  value X _ k := ehmNearGramDiagonalReferenceValue X k
  nonneg X _ k := ehmNearGramDiagonalReferenceValue_nonneg X k

/-- **Option C, corrected.**  The positive projection of the exact signed
`R₁` Ehm dyadic block.  This keeps the autocorrelation coordinate and avoids
the false assertion that the raw block is nonnegative. -/
noncomputable def ehmAutocorrelationPositiveReferenceProfile :
    EhmNonnegativeReferenceProfile where
  value X J k :=
    (ehmShiftedDyadicNearBlockSum ehmR1 X J
      (ehmH15NearMMax X) (ehmH15NearDMax X) k)⁺
  nonneg _ _ _ := posPart_nonneg _

/-! ## Analytic packages and the exact closure boundary -/

/-- An `L¹` reference-profile estimate sufficient for the full minority-mass
package.  Notice that signed global-core decay is retained as an independent
field. -/
structure EhmReferenceProfileL1Decay where
  profile : EhmNonnegativeReferenceProfile
  allocation : ∀ X : ℕ,
    EhmDyadicCorrectionAllocation X (ehmH15NearDMax X)
  etaCore : ℕ → ℝ
  etaCore_nonneg : ∀ X, 0 ≤ etaCore X
  etaCore_tendsto_zero : Tendsto etaCore atTop (nhds 0)
  etaL1 : ℕ → ℝ
  etaL1_nonneg : ∀ X, 0 ≤ etaL1 X
  etaL1_tendsto_zero : Tendsto etaL1 atTop (nhds 0)
  cofinal_core_and_reference_bound : ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      ehmExplicitFarCutoff X ≤ J ∧
      |ehmDyadicExplicitCoupledNearCore ehmR1 X
        (ehmExplicitFarCutoff X) J| ≤
          ((ehmDyadicNBlock X).card : ℝ) * etaCore X ∧
      ehmReferenceProfileL1Deviation profile X J (allocation X) ≤
        ((ehmDyadicNBlock X).card : ℝ) * etaL1 X

/-- A valid `L¹` reference-profile estimate supplies minority-mass decay. -/
noncomputable def EhmReferenceProfileL1Decay.toMinorityMassDecay
    (H : EhmReferenceProfileL1Decay) :
    EhmCorrectionMinorityMassDecay where
  allocation := H.allocation
  etaCore := H.etaCore
  etaCore_nonneg := H.etaCore_nonneg
  etaCore_tendsto_zero := H.etaCore_tendsto_zero
  etaMinority := H.etaL1
  etaMinority_nonneg := H.etaL1_nonneg
  etaMinority_tendsto_zero := H.etaL1_tendsto_zero
  cofinal_core_and_minority_bound X hX :=
    (H.cofinal_core_and_reference_bound X hX).mono fun J hJ ↦ by
      refine ⟨hJ.1, hJ.2.1, ?_⟩
      exact (ehmCorrectionCompletedMinorityMass_le_referenceL1
        H.profile X J (H.allocation X)).trans hJ.2.2

/-- Correctly normalized `L²` profile package.  Its vanishing hypothesis is
on `sqrt(number of blocks) * etaL2`, not merely on `etaL2`. -/
structure EhmReferenceProfileL2Decay where
  profile : EhmNonnegativeReferenceProfile
  allocation : ∀ X : ℕ,
    EhmDyadicCorrectionAllocation X (ehmH15NearDMax X)
  etaCore : ℕ → ℝ
  etaCore_nonneg : ∀ X, 0 ≤ etaCore X
  etaCore_tendsto_zero : Tendsto etaCore atTop (nhds 0)
  etaL2 : ℕ → ℝ
  etaL2_nonneg : ∀ X, 0 ≤ etaL2 X
  normalized_etaL2_tendsto_zero :
    Tendsto (fun X ↦ ehmReferenceProfileBlockCountSqrt X * etaL2 X)
      atTop (nhds 0)
  cofinal_core_and_reference_bound : ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      ehmExplicitFarCutoff X ≤ J ∧
      |ehmDyadicExplicitCoupledNearCore ehmR1 X
        (ehmExplicitFarCutoff X) J| ≤
          ((ehmDyadicNBlock X).card : ℝ) * etaCore X ∧
      ehmReferenceProfileL2Deviation profile X J (allocation X) ≤
        ((ehmDyadicNBlock X).card : ℝ) * etaL2 X

/-- `L²` control gives the `L¹` package with the unavoidable square-root
block-count loss. -/
noncomputable def EhmReferenceProfileL2Decay.toL1Decay
    (H : EhmReferenceProfileL2Decay) : EhmReferenceProfileL1Decay where
  profile := H.profile
  allocation := H.allocation
  etaCore := H.etaCore
  etaCore_nonneg := H.etaCore_nonneg
  etaCore_tendsto_zero := H.etaCore_tendsto_zero
  etaL1 := fun X ↦ ehmReferenceProfileBlockCountSqrt X * H.etaL2 X
  etaL1_nonneg X := mul_nonneg (Real.sqrt_nonneg _) (H.etaL2_nonneg X)
  etaL1_tendsto_zero := H.normalized_etaL2_tendsto_zero
  cofinal_core_and_reference_bound X hX :=
    (H.cofinal_core_and_reference_bound X hX).mono fun J hJ ↦ by
      refine ⟨hJ.1, hJ.2.1, ?_⟩
      calc
        ehmReferenceProfileL1Deviation H.profile X J (H.allocation X) ≤
            ehmReferenceProfileBlockCountSqrt X *
              ehmReferenceProfileL2Deviation H.profile X J (H.allocation X) :=
          ehmReferenceProfileL1Deviation_le_sqrtCard_mul_L2
            H.profile X J (H.allocation X)
        _ ≤ ehmReferenceProfileBlockCountSqrt X *
            (((ehmDyadicNBlock X).card : ℝ) * H.etaL2 X) :=
          mul_le_mul_of_nonneg_left hJ.2.2 (Real.sqrt_nonneg _)
        _ = ((ehmDyadicNBlock X).card : ℝ) *
            (ehmReferenceProfileBlockCountSqrt X * H.etaL2 X) := by ring

/-- Conditional Báez--Duarte closure from an `L¹` reference-profile package. -/
theorem baezDuarteCriterion_of_ehmReferenceProfileL1Decay
    (H : EhmReferenceProfileL1Decay) : BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmCorrectionMinorityMassDecay
    H.toMinorityMassDecay

/-- Conditional Báez--Duarte closure from a correctly normalized `L²`
reference-profile package. -/
theorem baezDuarteCriterion_of_ehmReferenceProfileL2Decay
    (H : EhmReferenceProfileL2Decay) : BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmReferenceProfileL1Decay H.toL1Decay

/-- Nyman--Beurling closure from the `L¹` profile package. -/
theorem nymanBeurlingCriterion_of_ehmReferenceProfileL1Decay
    (H : EhmReferenceProfileL1Decay) : NymanBeurlingCriterion :=
  nymanBeurlingCriterion_of_ehmCorrectionMinorityMassDecay
    H.toMinorityMassDecay

/-- Nyman--Beurling closure from the correctly normalized `L²` package. -/
theorem nymanBeurlingCriterion_of_ehmReferenceProfileL2Decay
    (H : EhmReferenceProfileL2Decay) : NymanBeurlingCriterion :=
  nymanBeurlingCriterion_of_ehmReferenceProfileL1Decay H.toL1Decay

/-- RH closure needs the independently packaged forward Nyman--Beurling
implication.  Reference-profile positivity does not supply this field. -/
theorem riemannHypothesis_of_ehmReferenceProfileL1Decay_of_NBForward
    (hNB : NBForward) (H : EhmReferenceProfileL1Decay) :
    RH.Basic.RiemannHypothesis :=
  hNB (nymanBeurlingCriterion_of_ehmReferenceProfileL1Decay H)

/-- `L²` version of the conditional RH closure. -/
theorem riemannHypothesis_of_ehmReferenceProfileL2Decay_of_NBForward
    (hNB : NBForward) (H : EhmReferenceProfileL2Decay) :
    RH.Basic.RiemannHypothesis :=
  hNB (nymanBeurlingCriterion_of_ehmReferenceProfileL2Decay H)

end RH.Criteria.NymanBeurling.BCFLogTaperEhmReferenceProfiles
