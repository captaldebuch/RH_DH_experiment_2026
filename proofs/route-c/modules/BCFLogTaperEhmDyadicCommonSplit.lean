import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmCutoffAverageMainTerm

/-!
# A common near/far split for the signed dyadic Ehm average

This file carries the complementary-sector estimate into the double-cofinal
dyadic setting.  A common divisor cutoff `D` is used for every
`N ∈ [X,2X]`.  The near core remains signed.  Only the rigorously isolated
far complementary sector is replaced by Ehm's quadratic-decay majorant and,
subsequently, by an explicit divisor-tail mass.

No decay of that tail mass is asserted here.  Its uniform vanishing is the
next analytic subproblem.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicCommonSplit

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmComplementarySector
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmSignedAverage
open RH.Criteria.NymanBeurling.BCFLogTaperEhmUniformBoundary

/-- The signed sum of common-cutoff near cores on a dyadic block. -/
noncomputable def ehmDyadicCommonNearCoreSum
    (R1 : ℝ → ℝ) (X D J : ℕ) : ℝ :=
  ∑ N ∈ ehmDyadicNBlock X,
    ehmFiniteComplementaryDivisorNearCore R1 N D J

/-- The sum of Ehm's nonnegative pointwise far-sector majorants. -/
noncomputable def ehmDyadicCommonFarMajorantSum
    (X D J : ℕ) : ℝ :=
  ∑ N ∈ ehmDyadicNBlock X,
    ehmComplementaryDivisorFarMajorant 8 N D J

/-- The explicit dyadic divisor-tail mass left after applying the routine
outer-coefficient and reciprocal-square estimates. -/
noncomputable def ehmDyadicCommonDivisorTailMass
    (X D J : ℕ) : ℝ :=
  ∑ N ∈ ehmDyadicNBlock X,
    16 * (N : ℝ) ^ 2 *
      ∑ d ∈ Finset.Icc (D + 1) J,
        |dirichletCoeff N d| / (d : ℝ) ^ 2

/-- Exact dyadic near/far identity with a common divisor cutoff. -/
theorem sum_ehmFiniteCoupledBoundaryExpression_eq_commonNear_sub_far
    (R1 : ℝ → ℝ) (X D J : ℕ)
    (hX : 2 ≤ X) (hD : 2 * X ≤ D) (hJ : D ≤ J) :
    (∑ N ∈ ehmDyadicNBlock X,
        ehmFiniteCoupledBoundaryExpression R1 N J) =
      ehmDyadicCommonNearCoreSum R1 X D J -
        (∑ N ∈ ehmDyadicNBlock X,
          ehmFiniteComplementaryDivisorFarOuter R1 N D J) := by
  unfold ehmDyadicCommonNearCoreSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro N hNmem
  have hN2 : 2 ≤ N := hX.trans (Finset.mem_Icc.mp hNmem).1
  have hND : N ≤ D := (Finset.mem_Icc.mp hNmem).2.trans hD
  exact ehmFiniteCoupledBoundaryExpression_eq_nearCore_sub_far
    R1 N D J hN2 hND hJ

/-- The absolute value of the summed far sector is controlled by the sum of
the pointwise Ehm majorants. -/
theorem abs_sum_ehmFiniteComplementaryDivisorFarOuter_le_majorant
    (X D J : ℕ) :
    |∑ N ∈ ehmDyadicNBlock X,
        ehmFiniteComplementaryDivisorFarOuter ehmR1 N D J| ≤
      ehmDyadicCommonFarMajorantSum X D J := by
  calc
    |∑ N ∈ ehmDyadicNBlock X,
        ehmFiniteComplementaryDivisorFarOuter ehmR1 N D J| ≤
      ∑ N ∈ ehmDyadicNBlock X,
        |ehmFiniteComplementaryDivisorFarOuter ehmR1 N D J| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      unfold ehmDyadicCommonFarMajorantSum
      apply Finset.sum_le_sum
      intro N _
      exact abs_ehmFiniteComplementaryDivisorFarOuter_ehmR1_le N D J

/-- On a genuine dyadic block, the far majorant is bounded by the explicit
common divisor-tail mass. -/
theorem ehmDyadicCommonFarMajorantSum_le_divisorTailMass
    (X D J : ℕ) (hX : 2 ≤ X) :
    ehmDyadicCommonFarMajorantSum X D J ≤
      ehmDyadicCommonDivisorTailMass X D J := by
  unfold ehmDyadicCommonFarMajorantSum ehmDyadicCommonDivisorTailMass
  apply Finset.sum_le_sum
  intro N hNmem
  exact ehmComplementaryDivisorFarMajorant_le_divisorTail N D J
    (hX.trans (Finset.mem_Icc.mp hNmem).1)

/-- Unconditional one-sided reduction for the signed dyadic boundary.  The
near core keeps every arithmetic sign; the only unsigned loss is the explicit
far divisor-tail mass. -/
theorem sum_ehmFiniteCoupledBoundaryExpression_le_commonNear_add_tailMass
    (X D J : ℕ) (hX : 2 ≤ X) (hD : 2 * X ≤ D) (hJ : D ≤ J) :
    (∑ N ∈ ehmDyadicNBlock X,
        ehmFiniteCoupledBoundaryExpression ehmR1 N J) ≤
      ehmDyadicCommonNearCoreSum ehmR1 X D J +
        ehmDyadicCommonDivisorTailMass X D J := by
  rw [sum_ehmFiniteCoupledBoundaryExpression_eq_commonNear_sub_far
    ehmR1 X D J hX hD hJ]
  let F := ∑ N ∈ ehmDyadicNBlock X,
    ehmFiniteComplementaryDivisorFarOuter ehmR1 N D J
  have hF : |F| ≤ ehmDyadicCommonDivisorTailMass X D J :=
    (abs_sum_ehmFiniteComplementaryDivisorFarOuter_le_majorant X D J).trans
      (ehmDyadicCommonFarMajorantSum_le_divisorTailMass X D J hX)
  have hneg : -F ≤ |F| := neg_le_abs F
  linarith

/-! ## The next exact analytic interface -/

/-- A common-cutoff signed near-core estimate plus a uniform vanishing bound
for the explicitly isolated divisor tail.  Both functions are required to be
null; no theorem below constructs this package. -/
structure EhmDyadicCommonSplitSignedAverageVanishing where
  D : ℕ → ℕ
  D_ge : ∀ X, 2 * X ≤ D X
  etaNear : ℕ → ℝ
  etaNear_nonneg : ∀ X, 0 ≤ etaNear X
  etaNear_tendsto_zero : Tendsto etaNear atTop (nhds 0)
  etaFar : ℕ → ℝ
  etaFar_nonneg : ∀ X, 0 ≤ etaFar X
  etaFar_tendsto_zero : Tendsto etaFar atTop (nhds 0)
  near_cofinal_bound : ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      D X ≤ J ∧
      ehmDyadicCommonNearCoreSum ehmR1 X (D X) J ≤
        ((ehmDyadicNBlock X).card : ℝ) * etaNear X
  far_uniform_bound : ∀ X : ℕ, 2 ≤ X → ∀ J : ℕ, D X ≤ J →
    ehmDyadicCommonDivisorTailMass X (D X) J ≤
      ((ehmDyadicNBlock X).card : ℝ) * etaFar X

/-- The common-split package supplies the signed boundary-average package
with majorant `etaNear + etaFar`. -/
noncomputable def EhmDyadicCommonSplitSignedAverageVanishing.toBoundaryAverage
    (H : EhmDyadicCommonSplitSignedAverageVanishing) :
    EhmDyadicSignedBoundaryAverageVanishing where
  eta := fun X ↦ H.etaNear X + H.etaFar X
  eta_nonneg X := add_nonneg (H.etaNear_nonneg X) (H.etaFar_nonneg X)
  eta_tendsto_zero := by
    convert H.etaNear_tendsto_zero.add H.etaFar_tendsto_zero using 1
    simp
  cofinal_sum_bound X hX :=
    (H.near_cofinal_bound X hX).mono fun J hJ ↦ by
      calc
        (∑ N ∈ ehmDyadicNBlock X,
            ehmFiniteCoupledBoundaryExpression ehmR1 N J) ≤
          ehmDyadicCommonNearCoreSum ehmR1 X (H.D X) J +
            ehmDyadicCommonDivisorTailMass X (H.D X) J :=
          sum_ehmFiniteCoupledBoundaryExpression_le_commonNear_add_tailMass
            X (H.D X) J hX (H.D_ge X) hJ.1
        _ ≤ ((ehmDyadicNBlock X).card : ℝ) * H.etaNear X +
            ((ehmDyadicNBlock X).card : ℝ) * H.etaFar X :=
          add_le_add hJ.2 (H.far_uniform_bound X hX J hJ.1)
        _ = ((ehmDyadicNBlock X).card : ℝ) *
            (H.etaNear X + H.etaFar X) := by ring

/-- Once the signed near-core and routine far-tail bounds are supplied, the
existing exact chain closes the Báez--Duarte criterion. -/
theorem baezDuarteCriterion_of_ehmDyadicCommonSplitSignedAverage
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (H : EhmDyadicCommonSplitSignedAverageVanishing) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmDyadicSignedBoundaryAverage HS
    H.toBoundaryAverage

end RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicCommonSplit
