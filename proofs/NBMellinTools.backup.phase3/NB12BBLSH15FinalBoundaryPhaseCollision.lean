/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FinalBoundaryPhasePairs

/-!
# NB12zzc: exact collision/separated split for endpoint phase pairs

The difference- and sum-frequency endpoint populations are partitioned at
the level of their exact complex phases.  Collision means that the relevant
unit phase is exactly `1`; the complementary sector is retained as one signed
sum.  This is an algebraic partition only: no absolute value or unproved
spacing estimate is introduced.

The final identity shows precisely what a phase-spacing argument must prove.
If the collision ledger does not reproduce the negative modulus-block
diagonal, its defect must remain coupled to the separated phase pairs.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate
open Complex

namespace NBMellinTools.NB12

abbrev H15EndpointPairPhase :=
  ℕ → ℕ → ℕ → ℕ → ℕ → ℝ

abbrev H15EndpointPairPredicate :=
  ℕ → ℕ → ℕ → ℕ → ℕ → Prop

/-! ## A reusable filtered endpoint-pair aggregate -/

noncomputable def h15NormalizedBoundaryEndpointPairPhaseAggregate
    (N g r U Q : ℕ) (phase : H15EndpointPairPhase) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    ∑ q' ∈ (h15BettinChandeeSupportedNatBlock N g Q).erase q,
      ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
        ∑ d' ∈ h15DyadicActivePeriodSquareDivisorIndices g U q',
          ∑ u ∈ h15NormalizedSuperperiodBoundarySupport U
              (h15SquareDivisorProgressionModulus g d) q,
            ∑ v ∈ h15NormalizedSuperperiodBoundarySupport U
                (h15SquareDivisorProgressionModulus g d') q',
              (h15NormalizedProgressionCoupledBoundaryPointWeight N g U
                  (h15SquareDivisorProgressionModulus g d) q d u *
                h15NormalizedProgressionCoupledBoundaryPointWeight N g U
                  (h15SquareDivisorProgressionModulus g d') q' d' v) *
                phase r u q v q'

noncomputable def h15NormalizedBoundaryEndpointPairFilteredPhaseAggregate
    (N g r U Q : ℕ) (phase : H15EndpointPairPhase)
    (P : H15EndpointPairPredicate) : ℝ := by
  classical
  exact
    ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
      ∑ q' ∈ (h15BettinChandeeSupportedNatBlock N g Q).erase q,
        ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
          ∑ d' ∈ h15DyadicActivePeriodSquareDivisorIndices g U q',
            ∑ u ∈ h15NormalizedSuperperiodBoundarySupport U
                (h15SquareDivisorProgressionModulus g d) q,
              ∑ v ∈ (h15NormalizedSuperperiodBoundarySupport U
                  (h15SquareDivisorProgressionModulus g d') q').filter
                    (fun v => P r u q v q'),
                (h15NormalizedProgressionCoupledBoundaryPointWeight N g U
                    (h15SquareDivisorProgressionModulus g d) q d u *
                  h15NormalizedProgressionCoupledBoundaryPointWeight N g U
                    (h15SquareDivisorProgressionModulus g d') q' d' v) *
                  phase r u q v q'

/-- Exact signed partition of any endpoint-pair phase aggregate. -/
theorem h15NormalizedBoundaryEndpointPairPhaseAggregate_eq_filtered_add_complement
    (N g r U Q : ℕ) (phase : H15EndpointPairPhase)
    (P : H15EndpointPairPredicate) :
    h15NormalizedBoundaryEndpointPairPhaseAggregate N g r U Q phase =
      h15NormalizedBoundaryEndpointPairFilteredPhaseAggregate
          N g r U Q phase P +
        h15NormalizedBoundaryEndpointPairFilteredPhaseAggregate
          N g r U Q phase (fun r u q v q' => ¬ P r u q v q') := by
  classical
  unfold h15NormalizedBoundaryEndpointPairPhaseAggregate
    h15NormalizedBoundaryEndpointPairFilteredPhaseAggregate
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q' _hq'
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d' _hd'
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _hu
  simpa only using (Finset.sum_filter_add_sum_filter_not
    (h15NormalizedSuperperiodBoundarySupport U
      (h15SquareDivisorProgressionModulus g d') q')
    (fun v => P r u q v q')
    (fun v =>
      (h15NormalizedProgressionCoupledBoundaryPointWeight N g U
          (h15SquareDivisorProgressionModulus g d) q d u *
        h15NormalizedProgressionCoupledBoundaryPointWeight N g U
          (h15SquareDivisorProgressionModulus g d') q' d' v) *
        phase r u q v q')).symm

/-! ## Exact sum and difference collisions -/

noncomputable def h15DifferenceEndpointPairPhase
    (r u q v q' : ℕ) : ℝ :=
  (h15DoubledDirectAdditivePhase r u q *
    conj (h15DoubledDirectAdditivePhase r v q')).re

noncomputable def h15SumEndpointPairPhase
    (r u q v q' : ℕ) : ℝ :=
  (h15DoubledDirectAdditivePhase r u q *
    h15DoubledDirectAdditivePhase r v q').re

noncomputable def h15DifferenceEndpointPairCollision
    (r u q v q' : ℕ) : Prop :=
  h15DoubledDirectAdditivePhase r u q *
      conj (h15DoubledDirectAdditivePhase r v q') = 1

noncomputable def h15SumEndpointPairCollision
    (r u q v q' : ℕ) : Prop :=
  h15DoubledDirectAdditivePhase r u q *
      h15DoubledDirectAdditivePhase r v q' = 1

theorem h15DifferenceEndpointPairPhase_eq_one_of_collision
    {r u q v q' : ℕ}
    (h : h15DifferenceEndpointPairCollision r u q v q') :
    h15DifferenceEndpointPairPhase r u q v q' = 1 := by
  unfold h15DifferenceEndpointPairCollision at h
  unfold h15DifferenceEndpointPairPhase
  rw [h]
  rfl

theorem h15SumEndpointPairPhase_eq_one_of_collision
    {r u q v q' : ℕ}
    (h : h15SumEndpointPairCollision r u q v q') :
    h15SumEndpointPairPhase r u q v q' = 1 := by
  unfold h15SumEndpointPairCollision at h
  unfold h15SumEndpointPairPhase
  rw [h]
  rfl

noncomputable def h15NormalizedBoundaryDifferenceCollisionLedger
    (N g r U Q : ℕ) : ℝ :=
  h15NormalizedBoundaryEndpointPairFilteredPhaseAggregate N g r U Q
    h15DifferenceEndpointPairPhase h15DifferenceEndpointPairCollision

noncomputable def h15NormalizedBoundaryDifferenceSeparatedLedger
    (N g r U Q : ℕ) : ℝ :=
  h15NormalizedBoundaryEndpointPairFilteredPhaseAggregate N g r U Q
    h15DifferenceEndpointPairPhase
    (fun r u q v q' => ¬ h15DifferenceEndpointPairCollision r u q v q')

noncomputable def h15NormalizedBoundarySumCollisionLedger
    (N g r U Q : ℕ) : ℝ :=
  h15NormalizedBoundaryEndpointPairFilteredPhaseAggregate N g r U Q
    h15SumEndpointPairPhase h15SumEndpointPairCollision

noncomputable def h15NormalizedBoundarySumSeparatedLedger
    (N g r U Q : ℕ) : ℝ :=
  h15NormalizedBoundaryEndpointPairFilteredPhaseAggregate N g r U Q
    h15SumEndpointPairPhase
    (fun r u q v q' => ¬ h15SumEndpointPairCollision r u q v q')

/-- Pure signed endpoint-weight mass on a filtered pair population. -/
noncomputable def h15NormalizedBoundaryEndpointPairFilteredWeightMass
    (N g r U Q : ℕ) (P : H15EndpointPairPredicate) : ℝ :=
  h15NormalizedBoundaryEndpointPairFilteredPhaseAggregate N g r U Q
    (fun _r _u _q _v _q' => 1) P

/-- On the exact difference-collision sector the phase is identically one,
so its complete contribution is the signed endpoint-weight mass. -/
theorem h15NormalizedBoundaryDifferenceCollisionLedger_eq_weightMass
    (N g r U Q : ℕ) :
    h15NormalizedBoundaryDifferenceCollisionLedger N g r U Q =
      h15NormalizedBoundaryEndpointPairFilteredWeightMass N g r U Q
        h15DifferenceEndpointPairCollision := by
  classical
  unfold h15NormalizedBoundaryDifferenceCollisionLedger
    h15NormalizedBoundaryEndpointPairFilteredWeightMass
    h15NormalizedBoundaryEndpointPairFilteredPhaseAggregate
  apply Finset.sum_congr rfl
  intro q _hq
  apply Finset.sum_congr rfl
  intro q' _hq'
  apply Finset.sum_congr rfl
  intro d _hd
  apply Finset.sum_congr rfl
  intro d' _hd'
  apply Finset.sum_congr rfl
  intro u _hu
  apply Finset.sum_congr rfl
  intro v hv
  have hcollision :
      h15DifferenceEndpointPairCollision r u q v q' :=
    (Finset.mem_filter.mp hv).2
  rw [h15DifferenceEndpointPairPhase_eq_one_of_collision hcollision]

/-- The same exact evaluation holds for the sum-frequency collision sector. -/
theorem h15NormalizedBoundarySumCollisionLedger_eq_weightMass
    (N g r U Q : ℕ) :
    h15NormalizedBoundarySumCollisionLedger N g r U Q =
      h15NormalizedBoundaryEndpointPairFilteredWeightMass N g r U Q
        h15SumEndpointPairCollision := by
  classical
  unfold h15NormalizedBoundarySumCollisionLedger
    h15NormalizedBoundaryEndpointPairFilteredWeightMass
    h15NormalizedBoundaryEndpointPairFilteredPhaseAggregate
  apply Finset.sum_congr rfl
  intro q _hq
  apply Finset.sum_congr rfl
  intro q' _hq'
  apply Finset.sum_congr rfl
  intro d _hd
  apply Finset.sum_congr rfl
  intro d' _hd'
  apply Finset.sum_congr rfl
  intro u _hu
  apply Finset.sum_congr rfl
  intro v hv
  have hcollision : h15SumEndpointPairCollision r u q v q' :=
    (Finset.mem_filter.mp hv).2
  rw [h15SumEndpointPairPhase_eq_one_of_collision hcollision]

theorem h15NormalizedBoundaryEndpointPairDifferenceFrequency_eq_collision_add_separated
    (N g r U Q : ℕ) :
    h15NormalizedBoundaryEndpointPairDifferenceFrequency N g r U Q =
      h15NormalizedBoundaryDifferenceCollisionLedger N g r U Q +
        h15NormalizedBoundaryDifferenceSeparatedLedger N g r U Q := by
  change
    h15NormalizedBoundaryEndpointPairPhaseAggregate N g r U Q
        h15DifferenceEndpointPairPhase = _
  exact h15NormalizedBoundaryEndpointPairPhaseAggregate_eq_filtered_add_complement
    N g r U Q h15DifferenceEndpointPairPhase
      h15DifferenceEndpointPairCollision

theorem h15NormalizedBoundaryEndpointPairSumFrequency_eq_collision_add_separated
    (N g r U Q : ℕ) :
    h15NormalizedBoundaryEndpointPairSumFrequency N g r U Q =
      h15NormalizedBoundarySumCollisionLedger N g r U Q +
        h15NormalizedBoundarySumSeparatedLedger N g r U Q := by
  change
    h15NormalizedBoundaryEndpointPairPhaseAggregate N g r U Q
        h15SumEndpointPairPhase = _
  exact h15NormalizedBoundaryEndpointPairPhaseAggregate_eq_filtered_add_complement
    N g r U Q h15SumEndpointPairPhase h15SumEndpointPairCollision

/-! ## Collision defect and the surviving signed spacing gate -/

noncomputable def h15NormalizedBoundaryPhaseCollisionLedger
    (N g r U Q : ℕ) : ℝ :=
  (h15NormalizedBoundaryDifferenceCollisionLedger N g r U Q -
    h15NormalizedBoundarySumCollisionLedger N g r U Q) / 2

noncomputable def h15NormalizedBoundaryPhaseSeparatedLedger
    (N g r U Q : ℕ) : ℝ :=
  (h15NormalizedBoundaryDifferenceSeparatedLedger N g r U Q -
    h15NormalizedBoundarySumSeparatedLedger N g r U Q) / 2

/-- The full distinct-modulus correlation is collision plus separated phase
mass, with no loss of sign. -/
theorem h15NormalizedBoundaryExplicitCrossModulusCorrelation_eq_collision_add_separated
    {N g r U Q : ℕ} (hQ : 0 < Q) :
    h15NormalizedBoundaryExplicitCrossModulusCorrelation N g r U Q =
      h15NormalizedBoundaryPhaseCollisionLedger N g r U Q +
        h15NormalizedBoundaryPhaseSeparatedLedger N g r U Q := by
  rw [h15NormalizedBoundaryExplicitCrossModulusCorrelation_eq_phasePairs hQ,
    h15NormalizedBoundaryEndpointPairDifferenceFrequency_eq_collision_add_separated,
    h15NormalizedBoundaryEndpointPairSumFrequency_eq_collision_add_separated]
  unfold h15NormalizedBoundaryPhaseCollisionLedger
    h15NormalizedBoundaryPhaseSeparatedLedger
  ring

/-- Exact defect left when the phase-collision ledger is compared with the
nonnegative modulus-block diagonal. -/
noncomputable def h15NormalizedBoundaryPhaseCollisionDefect
    (N g r U Q : ℕ) : ℝ :=
  h15NormalizedBoundaryFixedFrequencyModulusBlockDiagonal N g r U Q +
    h15NormalizedBoundaryPhaseCollisionLedger N g r U Q

/-- After exact collision extraction, the original dispersion gate is
equivalent to one signed bound on the separated phase pairs coupled to the
collision defect. -/
theorem h15CorrectionCoupledCrossModulusFrequencyDispersion_iff_phaseSeparated
    {N g r U Q : ℕ} (hQ : 0 < Q) (Delta : ℝ) :
    H15CorrectionCoupledCrossModulusFrequencyDispersion N g r U Q Delta ↔
      0 ≤ Delta ∧
        h15NormalizedBoundaryPhaseSeparatedLedger N g r U Q ≤
          Delta * h15NormalizedBoundaryCrossModulusFrequencyEnergy N g U Q -
            h15NormalizedBoundaryPhaseCollisionDefect N g r U Q := by
  rw [h15CorrectionCoupledCrossModulusFrequencyDispersion_iff_explicitCorrelation
    N g r U Q Delta]
  unfold H15CorrectionCoupledExplicitCrossModulusCompensation
  rw [h15NormalizedBoundaryExplicitCrossModulusCorrelation_eq_collision_add_separated
    hQ]
  unfold h15NormalizedBoundaryPhaseCollisionDefect
  constructor <;> rintro ⟨hDelta, h⟩ <;> refine ⟨hDelta, ?_⟩ <;> linarith

end NBMellinTools.NB12
