import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmEarlyBlockCorrection
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmWeek3Closure

/-!
# Exact triangle loss for correction-completed Ehm blocks

The geometric stop test previously used common sign as a sufficient way to
remove the triangle inequality introduced by dyadic localization.  This file
shows that common sign is exactly the zero-loss case and replaces that rigid
condition by a quantitative nonnegative defect.

For any correction allocation, the sum of absolute completed blocks is

`|coupled near core| + triangle loss`.

Thus the direct arithmetic route needs precisely two estimates on one cofinal
set of hyperbolic cutoffs: decay of the signed global core and decay of the
localization loss.  Perfect sign coherence sets the second term to zero, but
is stronger than necessary.  No decay estimate is asserted in this file.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmCorrectionTriangleLoss

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCoupledNearCoreTarget
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicCorrectionAbel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmEarlyBlockCorrection
open RH.Criteria.NymanBeurling.BCFLogTaperEhmExplicitFarCutoff
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRectangularInstantiation
open RH.Criteria.NymanBeurling.BCFLogTaperEhmWeek3Closure
open RH.Criteria.NymanBeurling.RHBridge

/-! ## Equality in the finite real triangle inequality -/

/-- Equality between the sum of absolute values and the absolute value of the
sum holds exactly when all terms have a common weak sign.  This includes the
zero family in both alternatives. -/
theorem finset_sum_abs_eq_abs_sum_iff_common_sign
    {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, |f i|) = |∑ i ∈ s, f i| ↔
      (∀ i ∈ s, 0 ≤ f i) ∨ (∀ i ∈ s, f i ≤ 0) := by
  classical
  constructor
  · intro h
    by_cases hsum : 0 ≤ ∑ i ∈ s, f i
    · left
      have hzero : (∑ i ∈ s, (|f i| - f i)) = 0 := by
        rw [Finset.sum_sub_distrib, h, abs_of_nonneg hsum]
        ring
      have hterms := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ ↦ sub_nonneg.mpr (le_abs_self (f i)))).mp hzero
      intro i hi
      exact abs_eq_self.mp (sub_eq_zero.mp (hterms i hi))
    · right
      have hsum' : ∑ i ∈ s, f i ≤ 0 := le_of_not_ge hsum
      have hzero : (∑ i ∈ s, (|f i| + f i)) = 0 := by
        rw [Finset.sum_add_distrib, h, abs_of_nonpos hsum']
        ring
      have hterms := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ ↦ by linarith [neg_le_abs (f i)])).mp hzero
      intro i hi
      have hiZero := hterms i hi
      have hiAbs : |f i| = -f i := by linarith
      exact abs_eq_neg_self.mp hiAbs
  · rintro (hnonneg | hnonpos)
    · have hsum : 0 ≤ ∑ i ∈ s, f i := Finset.sum_nonneg hnonneg
      rw [abs_of_nonneg hsum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_of_nonneg (hnonneg i hi)]
    · have hsum : ∑ i ∈ s, f i ≤ 0 := Finset.sum_nonpos hnonpos
      rw [abs_of_nonpos hsum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_of_nonpos (hnonpos i hi)]

/-- Quantitative form of the equality theorem: triangle loss is twice the
smaller of the total positive and negative masses. -/
theorem finset_sum_abs_sub_abs_sum_eq_two_mul_min_sign_mass
    {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, |f i|) - |∑ i ∈ s, f i| =
      2 * min (∑ i ∈ s, (f i)⁺) (∑ i ∈ s, (f i)⁻) := by
  classical
  have habs : (∑ i ∈ s, |f i|) =
      (∑ i ∈ s, (f i)⁺) + (∑ i ∈ s, (f i)⁻) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 0 ≤ f i
    · simp [hi, abs_of_nonneg hi]
    · have hi' : f i ≤ 0 := le_of_not_ge hi
      simp [hi', abs_of_nonpos hi']
  have hsum : (∑ i ∈ s, f i) =
      (∑ i ∈ s, (f i)⁺) - (∑ i ∈ s, (f i)⁻) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact (posPart_sub_negPart (f i)).symm
  rw [habs, hsum]
  by_cases hle : (∑ i ∈ s, (f i)⁺) ≤ (∑ i ∈ s, (f i)⁻)
  · rw [abs_of_nonpos (sub_nonpos.mpr hle), min_eq_left hle]
    ring
  · have hge : (∑ i ∈ s, (f i)⁻) ≤ (∑ i ∈ s, (f i)⁺) :=
      le_of_not_ge hle
    rw [abs_of_nonneg (sub_nonneg.mpr hge), min_eq_right hge]
    ring

/-! ## The exact H15 localization defect -/

/-- Excess introduced by applying the triangle inequality after attaching
the allocated correction shares to the dyadic Abel blocks. -/
noncomputable def ehmCorrectionCompletedTriangleLoss
    (R1 : ℝ → ℝ) (X J : ℕ)
    (A : EhmDyadicCorrectionAllocation X (ehmH15NearDMax X)) : ℝ :=
  (∑ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
    |ehmCorrectionCompletedDyadicAbelBlock R1 X J
      (ehmH15NearMMax X) (ehmH15NearDMax X) A k|) -
    |ehmDyadicExplicitCoupledNearCore R1 X
      (ehmExplicitFarCutoff X) J|

/-- Total positive mass among correction-completed dyadic blocks. -/
noncomputable def ehmCorrectionCompletedPositiveMass
    (R1 : ℝ → ℝ) (X J : ℕ)
    (A : EhmDyadicCorrectionAllocation X (ehmH15NearDMax X)) : ℝ :=
  ∑ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
    (ehmCorrectionCompletedDyadicAbelBlock R1 X J
      (ehmH15NearMMax X) (ehmH15NearDMax X) A k)⁺

/-- Total negative mass among correction-completed dyadic blocks. -/
noncomputable def ehmCorrectionCompletedNegativeMass
    (R1 : ℝ → ℝ) (X J : ℕ)
    (A : EhmDyadicCorrectionAllocation X (ehmH15NearDMax X)) : ℝ :=
  ∑ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
    (ehmCorrectionCompletedDyadicAbelBlock R1 X J
      (ehmH15NearMMax X) (ehmH15NearDMax X) A k)⁻

/-- Triangle loss is nonnegative for every allocation. -/
theorem ehmCorrectionCompletedTriangleLoss_nonneg
    (R1 : ℝ → ℝ) (X J : ℕ)
    (A : EhmDyadicCorrectionAllocation X (ehmH15NearDMax X))
    (hX : 1 ≤ X) :
    0 ≤ ehmCorrectionCompletedTriangleLoss R1 X J A := by
  unfold ehmCorrectionCompletedTriangleLoss
  rw [← sum_ehmCorrectionCompletedDyadicAbelBlock_eq_coupledNearCore
    R1 X J A hX]
  exact sub_nonneg.mpr (Finset.abs_sum_le_sum_abs _ _)

/-- Exact decomposition of the localized absolute cost into the global
signed core and the nonnegative triangle loss. -/
theorem sum_abs_completed_eq_abs_coupled_add_triangleLoss
    (R1 : ℝ → ℝ) (X J : ℕ)
    (A : EhmDyadicCorrectionAllocation X (ehmH15NearDMax X)) :
    (∑ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
      |ehmCorrectionCompletedDyadicAbelBlock R1 X J
        (ehmH15NearMMax X) (ehmH15NearDMax X) A k|) =
      |ehmDyadicExplicitCoupledNearCore R1 X
        (ehmExplicitFarCutoff X) J| +
        ehmCorrectionCompletedTriangleLoss R1 X J A := by
  unfold ehmCorrectionCompletedTriangleLoss
  ring

/-- The dyadic localization has zero triangle loss if and only if all
correction-completed blocks have a common weak sign. -/
theorem ehmCorrectionCompletedTriangleLoss_eq_zero_iff_common_sign
    (R1 : ℝ → ℝ) (X J : ℕ)
    (A : EhmDyadicCorrectionAllocation X (ehmH15NearDMax X))
    (hX : 1 ≤ X) :
    ehmCorrectionCompletedTriangleLoss R1 X J A = 0 ↔
      (∀ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
        0 ≤ ehmCorrectionCompletedDyadicAbelBlock R1 X J
          (ehmH15NearMMax X) (ehmH15NearDMax X) A k) ∨
      (∀ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
        ehmCorrectionCompletedDyadicAbelBlock R1 X J
          (ehmH15NearMMax X) (ehmH15NearDMax X) A k ≤ 0) := by
  unfold ehmCorrectionCompletedTriangleLoss
  rw [sub_eq_zero]
  rw [← sum_ehmCorrectionCompletedDyadicAbelBlock_eq_coupledNearCore
    R1 X J A hX]
  exact finset_sum_abs_eq_abs_sum_iff_common_sign
    (ehmShiftedDyadicDIndices X (ehmH15NearDMax X))
    (fun k ↦ ehmCorrectionCompletedDyadicAbelBlock R1 X J
      (ehmH15NearMMax X) (ehmH15NearDMax X) A k)

/-- Exact quantitative target: the localization loss is twice the minority
sign mass.  Hence asymptotic sign coherence, rather than literal common sign
on every block, is sufficient. -/
theorem ehmCorrectionCompletedTriangleLoss_eq_two_mul_min_sign_mass
    (R1 : ℝ → ℝ) (X J : ℕ)
    (A : EhmDyadicCorrectionAllocation X (ehmH15NearDMax X))
    (hX : 1 ≤ X) :
    ehmCorrectionCompletedTriangleLoss R1 X J A =
      2 * min (ehmCorrectionCompletedPositiveMass R1 X J A)
        (ehmCorrectionCompletedNegativeMass R1 X J A) := by
  unfold ehmCorrectionCompletedTriangleLoss
    ehmCorrectionCompletedPositiveMass ehmCorrectionCompletedNegativeMass
  rw [← sum_ehmCorrectionCompletedDyadicAbelBlock_eq_coupledNearCore
    R1 X J A hX]
  exact finset_sum_abs_sub_abs_sum_eq_two_mul_min_sign_mass
    (ehmShiftedDyadicDIndices X (ehmH15NearDMax X))
    (fun k ↦ ehmCorrectionCompletedDyadicAbelBlock R1 X J
      (ehmH15NearMMax X) (ehmH15NearDMax X) A k)

/-! ## Weakest two-component dyadic target -/

/-- A quantitative relaxation of exact sign coherence.

Both estimates are required on the same frequent set, so no invalid
intersection of merely cofinal subsequences occurs.  The allocation depends
on `X` but not on the oscillatory cutoff `J`.  Constructing this structure is
the remaining signed H15-strength problem. -/
structure EhmCorrectionTriangleLossDecay where
  allocation : ∀ X : ℕ,
    EhmDyadicCorrectionAllocation X (ehmH15NearDMax X)
  etaCore : ℕ → ℝ
  etaCore_nonneg : ∀ X, 0 ≤ etaCore X
  etaCore_tendsto_zero : Tendsto etaCore atTop (nhds 0)
  etaLoss : ℕ → ℝ
  etaLoss_nonneg : ∀ X, 0 ≤ etaLoss X
  etaLoss_tendsto_zero : Tendsto etaLoss atTop (nhds 0)
  cofinal_core_and_loss_bound : ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      ehmExplicitFarCutoff X ≤ J ∧
      |ehmDyadicExplicitCoupledNearCore ehmR1 X
        (ehmExplicitFarCutoff X) J| ≤
          ((ehmDyadicNBlock X).card : ℝ) * etaCore X ∧
      ehmCorrectionCompletedTriangleLoss ehmR1 X J (allocation X) ≤
        ((ehmDyadicNBlock X).card : ℝ) * etaLoss X

/-- A global-core bound together with a vanishing localization loss is
exactly sufficient for the existing correction-coupled Abel gate. -/
noncomputable def EhmCorrectionTriangleLossDecay.toDyadicDecay
    (H : EhmCorrectionTriangleLossDecay) :
    EhmDyadicCorrectionCoupledAbelDecay where
  eta := fun X ↦ H.etaCore X + H.etaLoss X
  eta_nonneg X := add_nonneg (H.etaCore_nonneg X) (H.etaLoss_nonneg X)
  eta_tendsto_zero := by
    simpa using H.etaCore_tendsto_zero.add H.etaLoss_tendsto_zero
  allocation := H.allocation
  cofinal_completed_block_bound X hX :=
    (H.cofinal_core_and_loss_bound X hX).mono fun J hJ ↦ by
      refine ⟨hJ.1, ?_⟩
      rw [sum_abs_completed_eq_abs_coupled_add_triangleLoss]
      calc
        |ehmDyadicExplicitCoupledNearCore ehmR1 X
              (ehmExplicitFarCutoff X) J| +
            ehmCorrectionCompletedTriangleLoss ehmR1 X J (H.allocation X) ≤
          ((ehmDyadicNBlock X).card : ℝ) * H.etaCore X +
            ((ehmDyadicNBlock X).card : ℝ) * H.etaLoss X :=
              add_le_add hJ.2.1 hJ.2.2
        _ = ((ehmDyadicNBlock X).card : ℝ) *
            (H.etaCore X + H.etaLoss X) := by ring

/-- Conversely, the original completed-block estimate controls both pieces.
This direction uses the same cofinal set, and therefore does not make an
invalid intersection of two frequent sets. -/
noncomputable def ehmDyadicDecayToTriangleLossDecay
    (H : EhmDyadicCorrectionCoupledAbelDecay) :
    EhmCorrectionTriangleLossDecay where
  allocation := H.allocation
  etaCore := H.eta
  etaCore_nonneg := H.eta_nonneg
  etaCore_tendsto_zero := H.eta_tendsto_zero
  etaLoss := H.eta
  etaLoss_nonneg := H.eta_nonneg
  etaLoss_tendsto_zero := H.eta_tendsto_zero
  cofinal_core_and_loss_bound X hX :=
    (H.cofinal_completed_block_bound X hX).mono fun J hJ ↦ by
      refine ⟨hJ.1, ?_, ?_⟩
      · rw [← sum_ehmCorrectionCompletedDyadicAbelBlock_eq_coupledNearCore
          ehmR1 X J (H.allocation X) (by omega)]
        exact (Finset.abs_sum_le_sum_abs _ _).trans hJ.2
      · unfold ehmCorrectionCompletedTriangleLoss
        have hcore : 0 ≤ |ehmDyadicExplicitCoupledNearCore ehmR1 X
            (ehmExplicitFarCutoff X) J| := abs_nonneg _
        linarith

/-- The triangle-loss formulation is an exact reformulation at the level of
existence of analytic packages.  It exposes where localization spends the
cancellation without claiming a stronger theorem. -/
theorem nonempty_ehmCorrectionTriangleLossDecay_iff_dyadicDecay :
    Nonempty EhmCorrectionTriangleLossDecay ↔
      Nonempty EhmDyadicCorrectionCoupledAbelDecay := by
  constructor
  · rintro ⟨H⟩
    exact ⟨H.toDyadicDecay⟩
  · rintro ⟨H⟩
    exact ⟨ehmDyadicDecayToTriangleLossDecay H⟩

/-! ## Minority-sign formulation -/

/-- Direct analytic interface suggested by the exact sign-mass formula.  It
permits mixed signs, provided the smaller sign sector has sublinear total
mass.  The core and minority bounds are deliberately imposed on the same
frequent set. -/
structure EhmCorrectionMinorityMassDecay where
  allocation : ∀ X : ℕ,
    EhmDyadicCorrectionAllocation X (ehmH15NearDMax X)
  etaCore : ℕ → ℝ
  etaCore_nonneg : ∀ X, 0 ≤ etaCore X
  etaCore_tendsto_zero : Tendsto etaCore atTop (nhds 0)
  etaMinority : ℕ → ℝ
  etaMinority_nonneg : ∀ X, 0 ≤ etaMinority X
  etaMinority_tendsto_zero : Tendsto etaMinority atTop (nhds 0)
  cofinal_core_and_minority_bound : ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      ehmExplicitFarCutoff X ≤ J ∧
      |ehmDyadicExplicitCoupledNearCore ehmR1 X
        (ehmExplicitFarCutoff X) J| ≤
          ((ehmDyadicNBlock X).card : ℝ) * etaCore X ∧
      min (ehmCorrectionCompletedPositiveMass ehmR1 X J (allocation X))
          (ehmCorrectionCompletedNegativeMass ehmR1 X J (allocation X)) ≤
        ((ehmDyadicNBlock X).card : ℝ) * etaMinority X

/-- Minority-sign decay controls the exact triangle loss, with the expected
factor two. -/
noncomputable def EhmCorrectionMinorityMassDecay.toTriangleLossDecay
    (H : EhmCorrectionMinorityMassDecay) :
    EhmCorrectionTriangleLossDecay where
  allocation := H.allocation
  etaCore := H.etaCore
  etaCore_nonneg := H.etaCore_nonneg
  etaCore_tendsto_zero := H.etaCore_tendsto_zero
  etaLoss := fun X ↦ 2 * H.etaMinority X
  etaLoss_nonneg X := mul_nonneg (by norm_num) (H.etaMinority_nonneg X)
  etaLoss_tendsto_zero := by
    simpa using (tendsto_const_nhds.mul H.etaMinority_tendsto_zero :
      Tendsto (fun X ↦ 2 * H.etaMinority X) atTop (nhds (2 * 0)))
  cofinal_core_and_loss_bound X hX :=
    (H.cofinal_core_and_minority_bound X hX).mono fun J hJ ↦ by
      refine ⟨hJ.1, hJ.2.1, ?_⟩
      rw [ehmCorrectionCompletedTriangleLoss_eq_two_mul_min_sign_mass
        ehmR1 X J (H.allocation X) (by omega)]
      calc
        2 * min
            (ehmCorrectionCompletedPositiveMass ehmR1 X J (H.allocation X))
            (ehmCorrectionCompletedNegativeMass ehmR1 X J (H.allocation X)) ≤
          2 * (((ehmDyadicNBlock X).card : ℝ) * H.etaMinority X) :=
            mul_le_mul_of_nonneg_left hJ.2.2 (by norm_num)
        _ = ((ehmDyadicNBlock X).card : ℝ) *
            (2 * H.etaMinority X) := by ring

/-- Triangle-loss decay also controls the minority-sign mass.  Reusing the
same majorant is harmless because the loss is twice a nonnegative mass. -/
noncomputable def ehmTriangleLossDecayToMinorityMassDecay
    (H : EhmCorrectionTriangleLossDecay) :
    EhmCorrectionMinorityMassDecay where
  allocation := H.allocation
  etaCore := H.etaCore
  etaCore_nonneg := H.etaCore_nonneg
  etaCore_tendsto_zero := H.etaCore_tendsto_zero
  etaMinority := H.etaLoss
  etaMinority_nonneg := H.etaLoss_nonneg
  etaMinority_tendsto_zero := H.etaLoss_tendsto_zero
  cofinal_core_and_minority_bound X hX :=
    (H.cofinal_core_and_loss_bound X hX).mono fun J hJ ↦ by
      refine ⟨hJ.1, hJ.2.1, ?_⟩
      have hpos : 0 ≤
          ehmCorrectionCompletedPositiveMass ehmR1 X J (H.allocation X) :=
        Finset.sum_nonneg fun k _ ↦ posPart_nonneg _
      have hneg : 0 ≤
          ehmCorrectionCompletedNegativeMass ehmR1 X J (H.allocation X) :=
        Finset.sum_nonneg fun k _ ↦ negPart_nonneg _
      have hmin : 0 ≤ min
          (ehmCorrectionCompletedPositiveMass ehmR1 X J (H.allocation X))
          (ehmCorrectionCompletedNegativeMass ehmR1 X J (H.allocation X)) :=
        le_min hpos hneg
      have hloss := hJ.2.2
      rw [ehmCorrectionCompletedTriangleLoss_eq_two_mul_min_sign_mass
        ehmR1 X J (H.allocation X) (by omega)] at hloss
      linarith

/-- Minority-mass decay is exactly the triangle-loss formulation at package
existence level. -/
theorem nonempty_ehmCorrectionMinorityMassDecay_iff_triangleLossDecay :
    Nonempty EhmCorrectionMinorityMassDecay ↔
      Nonempty EhmCorrectionTriangleLossDecay := by
  constructor
  · rintro ⟨H⟩
    exact ⟨H.toTriangleLossDecay⟩
  · rintro ⟨H⟩
    exact ⟨ehmTriangleLossDecayToMinorityMassDecay H⟩

/-- Direct Week 3 closure from the minority-sign target. -/
theorem baezDuarteCriterion_of_ehmCorrectionMinorityMassDecay
    (H : EhmCorrectionMinorityMassDecay) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_h15Week3CorrectionCoupledAbelCancellation
    H.toTriangleLossDecay.toDyadicDecay

theorem nymanBeurlingCriterion_of_ehmCorrectionMinorityMassDecay
    (H : EhmCorrectionMinorityMassDecay) :
    NymanBeurlingCriterion :=
  nymanBeurlingCriterion_iff_baezDuarteCriterion.mpr
    (baezDuarteCriterion_of_ehmCorrectionMinorityMassDecay H)

theorem riemannHypothesis_of_ehmCorrectionMinorityMassDecay_of_NBForward
    (hNB : NBForward) (H : EhmCorrectionMinorityMassDecay) :
    RH.Basic.RiemannHypothesis :=
  hNB (nymanBeurlingCriterion_of_ehmCorrectionMinorityMassDecay H)

/-- Week 3 closure with the proved rational autocorrelation bridge already
inserted. -/
theorem baezDuarteCriterion_of_ehmCorrectionTriangleLossDecay
    (H : EhmCorrectionTriangleLossDecay) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_h15Week3CorrectionCoupledAbelCancellation
    H.toDyadicDecay

theorem nymanBeurlingCriterion_of_ehmCorrectionTriangleLossDecay
    (H : EhmCorrectionTriangleLossDecay) :
    NymanBeurlingCriterion :=
  nymanBeurlingCriterion_iff_baezDuarteCriterion.mpr
    (baezDuarteCriterion_of_ehmCorrectionTriangleLossDecay H)

theorem riemannHypothesis_of_ehmCorrectionTriangleLossDecay_of_NBForward
    (hNB : NBForward) (H : EhmCorrectionTriangleLossDecay) :
    RH.Basic.RiemannHypothesis :=
  hNB (nymanBeurlingCriterion_of_ehmCorrectionTriangleLossDecay H)

end RH.Criteria.NymanBeurling.BCFLogTaperEhmCorrectionTriangleLoss
