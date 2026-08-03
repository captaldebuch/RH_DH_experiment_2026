import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmTypeIISplit

/-!
# The irreducible signed Type-I/II gate in the Ehm route

The finite reductions preceding this file are unconditional.  They isolate a
completed main form, two Möbius bilinear ranges, and the linear Ehm remainder.
The remaining analytic problem is to bound their **signed sum** on a cofinal
set of hyperbolic cutoffs.  Separate absolute-value estimates are deliberately
not fields of the structure below: they would destroy the cancellation which
the H15 argument needs.

This file does not assert the estimate.  It gives its smallest current formal
interface and proves that it is exactly equivalent to the previously frozen
coupled near-core target.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmTypeIIAnalyticGate

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCoupledNearCoreTarget
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCutoffAverageMainTerm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicFarTail
open RH.Criteria.NymanBeurling.BCFLogTaperEhmTypeIISplit

/-- The exact remaining analytic estimate in Type-I/II coordinates.

The threshold may depend on the dyadic scale.  All four terms remain under a
single signed upper bound.  In particular, the interface does not request
decay of either Type-I or Type-II separately. -/
structure EhmDyadicTypeIICoupledAnalyticGate where
  U : ℕ → ℕ
  U_le : ∀ X, U X ≤ 2 * X
  eta : ℕ → ℝ
  eta_nonneg : ∀ X, 0 ≤ eta X
  eta_tendsto_zero : Tendsto eta atTop (nhds 0)
  cofinal_bound : ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      ehmDyadicUniformFarTailVanishing.D X ≤ J ∧
      (ehmDyadicFullMainJointSum ehmR1 X J +
          ehmDyadicNearTypeI ehmR1 X
            (ehmDyadicUniformFarTailVanishing.D X) J (U X) +
          ehmDyadicNearTypeII ehmR1 X
            (ehmDyadicUniformFarTailVanishing.D X) J (U X) +
          ∑ N ∈ ehmDyadicNBlock X, ehmCoupledRemainder N) ≤
        ((ehmDyadicNBlock X).card : ℝ) * eta X

/-- The Type-I/II gate is sufficient for the indivisible coupled near-core
estimate by the exact finite partition, with no inequality applied during
the conversion. -/
noncomputable def EhmDyadicTypeIICoupledAnalyticGate.toCoupledNearCore
    (H : EhmDyadicTypeIICoupledAnalyticGate) :
    EhmDyadicCoupledNearCoreSignedAverageVanishing where
  eta := H.eta
  eta_nonneg := H.eta_nonneg
  eta_tendsto_zero := H.eta_tendsto_zero
  cofinal_bound X hX :=
    (H.cofinal_bound X hX).mono fun J hJ ↦ by
      rw [ehmDyadicExplicitCoupledNearCore_eq_typeI_typeII
        ehmR1 X (ehmDyadicUniformFarTailVanishing.D X) J (H.U X)
          (H.U_le X)]
      exact hJ

/-- Conversely, the already frozen coupled target supplies this Type-I/II
interface by choosing the harmless threshold `U(X) = X`.  Thus the new gate
is a coordinate system for the open estimate, not an easier hidden claim. -/
noncomputable def EhmDyadicCoupledNearCoreSignedAverageVanishing.toTypeIIGate
    (H : EhmDyadicCoupledNearCoreSignedAverageVanishing) :
    EhmDyadicTypeIICoupledAnalyticGate where
  U := fun X ↦ X
  U_le := fun X ↦ by omega
  eta := H.eta
  eta_nonneg := H.eta_nonneg
  eta_tendsto_zero := H.eta_tendsto_zero
  cofinal_bound X hX :=
    (H.cofinal_bound X hX).mono fun J hJ ↦ by
      rw [ehmDyadicExplicitCoupledNearCore_eq_typeI_typeII
        ehmR1 X (ehmDyadicUniformFarTailVanishing.D X) J X (by omega)] at hJ
      exact hJ

end RH.Criteria.NymanBeurling.BCFLogTaperEhmTypeIIAnalyticGate
