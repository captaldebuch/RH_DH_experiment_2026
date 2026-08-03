import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmAutocorrelationProfileStopTest
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmCutoffAverageMainTerm

/-!
# Outer-cutoff audit of the retained Ehm correction

The retained correction is not an elementary remainder.  It is a signed sum
over `N ∈ [X,2X]`, and each summand couples a finite von-Mangoldt transform to
Ehm's four-moment correction.  This file exposes that exact summand without
separating its two constituents.

It also measures the additional triangle loss incurred by taking absolute
values across the outer cutoff `N`.  This gives a hierarchy of honest
analytic targets:

* the weakest target bounds the signed retained correction itself;
* a stronger target bounds the sum of absolute coupled `N`-summands;
* splitting the von-Mangoldt and moment pieces is stronger still and is not
  used here.

No asymptotic estimate is asserted.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmRetainedCorrectionAudit

open Filter
open scoped BigOperators Topology
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmAutocorrelationProfileStopTest
open RH.Criteria.NymanBeurling.BCFLogTaperEhmBoundaryResearch
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCorrectionTriangleLoss
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCutoffAverageMainTerm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicCorrectionAbel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmExplicitFarCutoff

/-- The indivisible retained-correction contribution at one outer cutoff.
The finite von-Mangoldt transform and the four-moment correction retain their
relative sign. -/
noncomputable def ehmFiniteRetainedCorrectionSummand
    (R1 : ℝ → ℝ) (N J : ℕ) : ℝ :=
  ehmFiniteFullVonMangoldtTransformOuter R1 N J +
    ehmCoupledRemainder N

/-- The dyadic retained correction is exactly the signed sum of its
correction-completed outer-cutoff summands. -/
theorem sum_ehmFiniteRetainedCorrectionSummand_eq_retainedCorrection
    (R1 : ℝ → ℝ) (X J : ℕ) :
    (∑ N ∈ ehmDyadicNBlock X,
      ehmFiniteRetainedCorrectionSummand R1 N J) =
      ehmH15RetainedCorrection R1 X J := by
  unfold ehmFiniteRetainedCorrectionSummand ehmH15RetainedCorrection
  rw [Finset.sum_add_distrib,
    sum_ehmFiniteFullVonMangoldtTransformOuter_eq_joint]

/-- Absolute mass after preserving the main/moment coupling within each
outer cutoff but discarding cancellation between distinct cutoffs. -/
noncomputable def ehmRetainedCorrectionOuterL1Mass
    (R1 : ℝ → ℝ) (X J : ℕ) : ℝ :=
  ∑ N ∈ ehmDyadicNBlock X,
    |ehmFiniteRetainedCorrectionSummand R1 N J|

/-- Positive mass among the correction-completed outer-cutoff summands. -/
noncomputable def ehmRetainedCorrectionOuterPositiveMass
    (R1 : ℝ → ℝ) (X J : ℕ) : ℝ :=
  ∑ N ∈ ehmDyadicNBlock X,
    (ehmFiniteRetainedCorrectionSummand R1 N J)⁺

/-- Negative mass among the correction-completed outer-cutoff summands. -/
noncomputable def ehmRetainedCorrectionOuterNegativeMass
    (R1 : ℝ → ℝ) (X J : ℕ) : ℝ :=
  ∑ N ∈ ehmDyadicNBlock X,
    (ehmFiniteRetainedCorrectionSummand R1 N J)⁻

/-- Exact loss from applying the triangle inequality across the outer cutoff
after the von-Mangoldt and moment terms have been coupled at each `N`. -/
noncomputable def ehmRetainedCorrectionOuterTriangleLoss
    (R1 : ℝ → ℝ) (X J : ℕ) : ℝ :=
  ehmRetainedCorrectionOuterL1Mass R1 X J -
    |ehmH15RetainedCorrection R1 X J|

theorem abs_retainedCorrection_le_outerL1Mass
    (R1 : ℝ → ℝ) (X J : ℕ) :
    |ehmH15RetainedCorrection R1 X J| ≤
      ehmRetainedCorrectionOuterL1Mass R1 X J := by
  rw [← sum_ehmFiniteRetainedCorrectionSummand_eq_retainedCorrection]
  exact Finset.abs_sum_le_sum_abs _ _

theorem ehmRetainedCorrectionOuterTriangleLoss_nonneg
    (R1 : ℝ → ℝ) (X J : ℕ) :
    0 ≤ ehmRetainedCorrectionOuterTriangleLoss R1 X J := by
  exact sub_nonneg.mpr (abs_retainedCorrection_le_outerL1Mass R1 X J)

/-- The outer-cutoff triangle loss is exactly twice the minority sign mass.
This is the quantitative test for whether the per-`N` localization is safe. -/
theorem ehmRetainedCorrectionOuterTriangleLoss_eq_two_mul_min_sign_mass
    (R1 : ℝ → ℝ) (X J : ℕ) :
    ehmRetainedCorrectionOuterTriangleLoss R1 X J =
      2 * min (ehmRetainedCorrectionOuterPositiveMass R1 X J)
        (ehmRetainedCorrectionOuterNegativeMass R1 X J) := by
  unfold ehmRetainedCorrectionOuterTriangleLoss
    ehmRetainedCorrectionOuterL1Mass
    ehmRetainedCorrectionOuterPositiveMass
    ehmRetainedCorrectionOuterNegativeMass
  rw [← sum_ehmFiniteRetainedCorrectionSummand_eq_retainedCorrection]
  exact finset_sum_abs_sub_abs_sum_eq_two_mul_min_sign_mass
    (ehmDyadicNBlock X)
    (fun N ↦ ehmFiniteRetainedCorrectionSummand R1 N J)

/-- There is no outer-cutoff triangle loss exactly when all coupled
summands have one common weak sign. -/
theorem ehmRetainedCorrectionOuterTriangleLoss_eq_zero_iff_common_sign
    (R1 : ℝ → ℝ) (X J : ℕ) :
    ehmRetainedCorrectionOuterTriangleLoss R1 X J = 0 ↔
      (∀ N ∈ ehmDyadicNBlock X,
        0 ≤ ehmFiniteRetainedCorrectionSummand R1 N J) ∨
      (∀ N ∈ ehmDyadicNBlock X,
        ehmFiniteRetainedCorrectionSummand R1 N J ≤ 0) := by
  unfold ehmRetainedCorrectionOuterTriangleLoss
    ehmRetainedCorrectionOuterL1Mass
  rw [sub_eq_zero,
    ← sum_ehmFiniteRetainedCorrectionSummand_eq_retainedCorrection]
  exact finset_sum_abs_eq_abs_sum_iff_common_sign
    (ehmDyadicNBlock X)
    (fun N ↦ ehmFiniteRetainedCorrectionSummand R1 N J)

/-- Exact reconstruction of the stronger outer `L¹` target from the signed
correction and its localization loss. -/
theorem outerL1Mass_eq_abs_retainedCorrection_add_triangleLoss
    (R1 : ℝ → ℝ) (X J : ℕ) :
    ehmRetainedCorrectionOuterL1Mass R1 X J =
      |ehmH15RetainedCorrection R1 X J| +
        ehmRetainedCorrectionOuterTriangleLoss R1 X J := by
  unfold ehmRetainedCorrectionOuterTriangleLoss
  ring

/-! ## Modular analytic targets -/

/-- Weakest standalone target for the retained correction.  Uniformity in
`J` is what allows this estimate to be combined with a merely cofinal raw
block estimate without intersecting two frequent sets. -/
structure EhmRetainedCorrectionSignedSublinearBound where
  eta : ℕ → ℝ
  eta_nonneg : ∀ X, 0 ≤ eta X
  eta_tendsto_zero : Tendsto eta atTop (nhds 0)
  uniform_bound : ∀ X J : ℕ, 2 ≤ X →
    ehmExplicitFarCutoff X ≤ J →
    |ehmH15RetainedCorrection ehmR1 X J| ≤
      ((ehmDyadicNBlock X).card : ℝ) * eta X

/-- Stronger, more local target: the absolute mass of the already-coupled
per-`N` summands is sublinear uniformly in the hyperbolic cutoff. -/
structure EhmRetainedCorrectionOuterL1SublinearBound where
  eta : ℕ → ℝ
  eta_nonneg : ∀ X, 0 ≤ eta X
  eta_tendsto_zero : Tendsto eta atTop (nhds 0)
  uniform_bound : ∀ X J : ℕ, 2 ≤ X →
    ehmExplicitFarCutoff X ≤ J →
    ehmRetainedCorrectionOuterL1Mass ehmR1 X J ≤
      ((ehmDyadicNBlock X).card : ℝ) * eta X

/-- Concrete scalar target suggested by the finite audit: every already
coupled outer-cutoff summand is `O(1/N)`, uniformly in the hyperbolic cutoff.
This estimate is not asserted, but unlike the averaged package its required
normalization is now explicit. -/
structure EhmRetainedCorrectionInverseCutoffBound where
  C : ℝ
  C_nonneg : 0 ≤ C
  pointwise_bound : ∀ X N J : ℕ, 2 ≤ X →
    N ∈ ehmDyadicNBlock X → ehmExplicitFarCutoff X ≤ J →
    |ehmFiniteRetainedCorrectionSummand ehmR1 N J| ≤ C / (N : ℝ)

/-- An inverse-cutoff estimate sums to `O(1)` on `[X,2X]`; after the
project's normalization by the block cardinality, its decay function is
exactly `C / X`. -/
noncomputable def EhmRetainedCorrectionInverseCutoffBound.toOuterL1
    (H : EhmRetainedCorrectionInverseCutoffBound) :
    EhmRetainedCorrectionOuterL1SublinearBound where
  eta := fun X ↦ H.C / (X : ℝ)
  eta_nonneg X := div_nonneg H.C_nonneg (Nat.cast_nonneg X)
  eta_tendsto_zero := by
    have hcast : Tendsto (fun X : ℕ ↦ (X : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun X : ℕ ↦ ((X : ℝ))⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp hcast
    simpa [div_eq_mul_inv] using hinv.const_mul H.C
  uniform_bound X J hX hJ := by
    unfold ehmRetainedCorrectionOuterL1Mass
    calc
      (∑ N ∈ ehmDyadicNBlock X,
          |ehmFiniteRetainedCorrectionSummand ehmR1 N J|) ≤
        ∑ N ∈ ehmDyadicNBlock X, H.C / (N : ℝ) := by
          apply Finset.sum_le_sum
          intro N hN
          exact H.pointwise_bound X N J hX hN hJ
      _ ≤ ∑ _N ∈ ehmDyadicNBlock X, H.C / (X : ℝ) := by
          apply Finset.sum_le_sum
          intro N hN
          have hXR : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
          have hXN : (X : ℝ) ≤ N := by
            exact_mod_cast (Finset.mem_Icc.mp hN).1
          exact div_le_div_of_nonneg_left H.C_nonneg hXR hXN
      _ = ((ehmDyadicNBlock X).card : ℝ) * (H.C / (X : ℝ)) := by
          simp

/-- The per-cutoff `L¹` estimate implies the weakest signed correction
target, without separating the coupled summands. -/
def EhmRetainedCorrectionOuterL1SublinearBound.toSigned
    (H : EhmRetainedCorrectionOuterL1SublinearBound) :
    EhmRetainedCorrectionSignedSublinearBound where
  eta := H.eta
  eta_nonneg := H.eta_nonneg
  eta_tendsto_zero := H.eta_tendsto_zero
  uniform_bound X J hX hJ :=
    (abs_retainedCorrection_le_outerL1Mass ehmR1 X J).trans
      (H.uniform_bound X J hX hJ)

/-- The raw dyadic block estimate isolated from the retained correction. -/
structure EhmAutocorrelationRawL1CofinalBound where
  eta : ℕ → ℝ
  eta_nonneg : ∀ X, 0 ≤ eta X
  eta_tendsto_zero : Tendsto eta atTop (nhds 0)
  cofinal_bound : ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      ehmExplicitFarCutoff X ≤ J ∧
      ehmAutocorrelationRawL1Mass X J ≤
        ((ehmDyadicNBlock X).card : ℝ) * eta X

/-- A cofinal raw estimate and a uniform signed correction estimate assemble
the separated autocorrelation programme on one valid cofinal set. -/
noncomputable def assembleAutocorrelationSeparatedSublinearBounds
    (HR : EhmAutocorrelationRawL1CofinalBound)
    (HC : EhmRetainedCorrectionSignedSublinearBound) :
    EhmAutocorrelationSeparatedSublinearBounds where
  etaRaw := HR.eta
  etaRaw_nonneg := HR.eta_nonneg
  etaRaw_tendsto_zero := HR.eta_tendsto_zero
  etaCorrection := HC.eta
  etaCorrection_nonneg := HC.eta_nonneg
  etaCorrection_tendsto_zero := HC.eta_tendsto_zero
  cofinal_raw_bound := HR.cofinal_bound
  uniform_correction_bound := HC.uniform_bound

/-- Conditional closure from the modular raw/correction targets. -/
theorem baezDuarteCriterion_of_ehmRawL1_and_retainedCorrection
    (HR : EhmAutocorrelationRawL1CofinalBound)
    (HC : EhmRetainedCorrectionSignedSublinearBound) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmAutocorrelationSeparatedSublinearBounds
    (assembleAutocorrelationSeparatedSublinearBounds HR HC)

end RH.Criteria.NymanBeurling.BCFLogTaperEhmRetainedCorrectionAudit
