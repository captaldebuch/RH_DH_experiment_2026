import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmDyadicNearCoreReindex

/-!
# The indivisible signed Ehm near-core target

The final near-core expression contains three pieces which must not be
estimated independently: the completed Möbius--von-Mangoldt main form, the
near complementary Möbius bilinear form, and the linear remainder.  This
module freezes their signed combination as one definition and restates the
dyadic closure hypothesis only for that coupled object.

No triangle inequality or termwise absolute value occurs in this reduction.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmCoupledNearCoreTarget

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCutoffAverageMainTerm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicCommonSplit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicFarTail
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicNearCoreReindex
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge

/-- The complete signed dyadic near core.  The ordering and signs of its
three constituents are part of the definition. -/
noncomputable def ehmDyadicExplicitCoupledNearCore
    (R1 : ℝ → ℝ) (X D J : ℕ) : ℝ :=
  ehmDyadicFullMainJointSum R1 X J -
    ehmDyadicNearComplementaryJointSum R1 X D J +
    ∑ N ∈ ehmDyadicNBlock X, ehmCoupledRemainder N

/-- The previously derived common near core is exactly the indivisible
coupled object. -/
theorem ehmDyadicCommonNearCoreSum_eq_coupled
    (R1 : ℝ → ℝ) (X D J : ℕ) :
    ehmDyadicCommonNearCoreSum R1 X D J =
      ehmDyadicExplicitCoupledNearCore R1 X D J := by
  rw [ehmDyadicCommonNearCoreSum_eq_explicit]
  rfl

/-- The sole open signed estimate stated without exposing separate fields or
bounds for the three constituents. -/
structure EhmDyadicCoupledNearCoreSignedAverageVanishing where
  eta : ℕ → ℝ
  eta_nonneg : ∀ X, 0 ≤ eta X
  eta_tendsto_zero : Tendsto eta atTop (nhds 0)
  cofinal_bound : ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      ehmDyadicUniformFarTailVanishing.D X ≤ J ∧
      ehmDyadicExplicitCoupledNearCore ehmR1 X
          (ehmDyadicUniformFarTailVanishing.D X) J ≤
        ((ehmDyadicNBlock X).card : ℝ) * eta X

/-- The indivisible coupled estimate supplies the explicit three-term
interface, without applying inequalities to any constituent. -/
noncomputable def EhmDyadicCoupledNearCoreSignedAverageVanishing.toExplicit
    (H : EhmDyadicCoupledNearCoreSignedAverageVanishing) :
    EhmDyadicExplicitNearCoreSignedAverageVanishing where
  eta := H.eta
  eta_nonneg := H.eta_nonneg
  eta_tendsto_zero := H.eta_tendsto_zero
  cofinal_bound X hX :=
    (H.cofinal_bound X hX).mono fun J hJ ↦ by
      simpa [ehmDyadicExplicitCoupledNearCore] using hJ

/-- The coupled target feeds the verified far-tail and Báez--Duarte closure
without any additional analytic estimate. -/
theorem baezDuarteCriterion_of_ehmDyadicCoupledNearCoreSignedAverage
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (H : EhmDyadicCoupledNearCoreSignedAverageVanishing) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmDyadicExplicitNearCoreSignedAverage HS
    H.toExplicit

end RH.Criteria.NymanBeurling.BCFLogTaperEhmCoupledNearCoreTarget
