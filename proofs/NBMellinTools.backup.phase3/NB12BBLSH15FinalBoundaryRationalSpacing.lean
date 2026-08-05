/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FinalBoundaryRationalCollision

/-!
# NB12zze: tunable near/far rational spacing ledger

The common-modulus collision congruences are refined by the least cyclic
distance between their residues modulo `q*q'`.  The noncollision population
is split at an arbitrary natural threshold `H`, before taking absolute values.
The resulting exact identity is the correct input format for a spacing or
additive-large-sieve estimate.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate
open Complex

namespace NBMellinTools.NB12

/-! ## Cyclic residue distance -/

def h15CyclicResidueDistance (M a b : ℕ) : ℕ :=
  let d := Nat.dist (a % M) (b % M)
  min d (M - d)

theorem h15CyclicResidueDistance_eq_zero_iff_modEq
    {M a b : ℕ} (hM : 0 < M) :
    h15CyclicResidueDistance M a b = 0 ↔ a ≡ b [MOD M] := by
  unfold h15CyclicResidueDistance Nat.ModEq
  let d := Nat.dist (a % M) (b % M)
  have ha : a % M < M := Nat.mod_lt _ hM
  have hb : b % M < M := Nat.mod_lt _ hM
  have hdlt : d < M := by
    dsimp only [d]
    unfold Nat.dist
    omega
  constructor
  · intro h
    by_cases hd : d ≤ M - d
    · rw [min_eq_left hd] at h
      exact Nat.eq_of_dist_eq_zero h
    · rw [min_eq_right (Nat.le_of_not_ge hd)] at h
      have hMd : M ≤ d := Nat.sub_eq_zero_iff_le.mp h
      omega
  · intro h
    have hd0 : d = 0 := Nat.dist_eq_zero h
    change min d (M - d) = 0
    simp [hd0]

def h15DifferenceEndpointPairCyclicDistance
    (r u q v q' : ℕ) : ℕ :=
  h15CyclicResidueDistance (q * q')
    (2 * u * r * q') (2 * v * r * q)

def h15SumEndpointPairCyclicDistance
    (r u q v q' : ℕ) : ℕ :=
  h15CyclicResidueDistance (q * q')
    (2 * u * r * q' + 2 * v * r * q) 0

theorem h15DifferenceEndpointPairCyclicDistance_eq_zero_iff_collision
    {r u q v q' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (huq : Nat.Coprime u q) (hvq' : Nat.Coprime v q') :
    h15DifferenceEndpointPairCyclicDistance r u q v q' = 0 ↔
      h15DifferenceEndpointPairCollision r u q v q' := by
  unfold h15DifferenceEndpointPairCyclicDistance
  rw [h15CyclicResidueDistance_eq_zero_iff_modEq
    (Nat.mul_pos hq hq')]
  exact (h15DifferenceEndpointPairCollision_iff_modEq
    hq hq' huq hvq').symm

theorem h15SumEndpointPairCyclicDistance_eq_zero_iff_collision
    {r u q v q' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (huq : Nat.Coprime u q) (hvq' : Nat.Coprime v q') :
    h15SumEndpointPairCyclicDistance r u q v q' = 0 ↔
      h15SumEndpointPairCollision r u q v q' := by
  unfold h15SumEndpointPairCyclicDistance
  rw [h15CyclicResidueDistance_eq_zero_iff_modEq
    (Nat.mul_pos hq hq')]
  exact (h15SumEndpointPairCollision_iff_modEq_zero
    hq hq' huq hvq').symm

/-! ## A reusable refinement of a filtered population -/

theorem h15NormalizedBoundaryEndpointPairFilteredPhaseAggregate_eq_split
    (N g r U Q : ℕ) (phase : H15EndpointPairPhase)
    (P R : H15EndpointPairPredicate) :
    h15NormalizedBoundaryEndpointPairFilteredPhaseAggregate
        N g r U Q phase P =
      h15NormalizedBoundaryEndpointPairFilteredPhaseAggregate
          N g r U Q phase (fun r u q v q' => P r u q v q' ∧ R r u q v q') +
        h15NormalizedBoundaryEndpointPairFilteredPhaseAggregate
          N g r U Q phase
            (fun r u q v q' => P r u q v q' ∧ ¬ R r u q v q') := by
  classical
  unfold h15NormalizedBoundaryEndpointPairFilteredPhaseAggregate
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
  simpa only [Finset.filter_filter, and_assoc] using
    (Finset.sum_filter_add_sum_filter_not
      ((h15NormalizedSuperperiodBoundarySupport U
        (h15SquareDivisorProgressionModulus g d') q').filter
          (fun v => P r u q v q'))
      (fun v => R r u q v q')
      (fun v =>
        (h15NormalizedProgressionCoupledBoundaryPointWeight N g U
            (h15SquareDivisorProgressionModulus g d) q d u *
          h15NormalizedProgressionCoupledBoundaryPointWeight N g U
            (h15SquareDivisorProgressionModulus g d') q' d' v) *
          phase r u q v q')).symm

/-! ## Near and far signed ledgers -/

noncomputable def h15NormalizedBoundaryDifferenceNearLedger
    (N g r U Q H : ℕ) : ℝ :=
  h15NormalizedBoundaryEndpointPairFilteredPhaseAggregate N g r U Q
    h15DifferenceEndpointPairPhase
    (fun r u q v q' =>
      ¬ h15DifferenceEndpointPairCollision r u q v q' ∧
        h15DifferenceEndpointPairCyclicDistance r u q v q' ≤ H)

noncomputable def h15NormalizedBoundaryDifferenceFarLedger
    (N g r U Q H : ℕ) : ℝ :=
  h15NormalizedBoundaryEndpointPairFilteredPhaseAggregate N g r U Q
    h15DifferenceEndpointPairPhase
    (fun r u q v q' =>
      ¬ h15DifferenceEndpointPairCollision r u q v q' ∧
        ¬ h15DifferenceEndpointPairCyclicDistance r u q v q' ≤ H)

noncomputable def h15NormalizedBoundarySumNearLedger
    (N g r U Q H : ℕ) : ℝ :=
  h15NormalizedBoundaryEndpointPairFilteredPhaseAggregate N g r U Q
    h15SumEndpointPairPhase
    (fun r u q v q' =>
      ¬ h15SumEndpointPairCollision r u q v q' ∧
        h15SumEndpointPairCyclicDistance r u q v q' ≤ H)

noncomputable def h15NormalizedBoundarySumFarLedger
    (N g r U Q H : ℕ) : ℝ :=
  h15NormalizedBoundaryEndpointPairFilteredPhaseAggregate N g r U Q
    h15SumEndpointPairPhase
    (fun r u q v q' =>
      ¬ h15SumEndpointPairCollision r u q v q' ∧
        ¬ h15SumEndpointPairCyclicDistance r u q v q' ≤ H)

theorem h15NormalizedBoundaryDifferenceSeparatedLedger_eq_near_add_far
    (N g r U Q H : ℕ) :
    h15NormalizedBoundaryDifferenceSeparatedLedger N g r U Q =
      h15NormalizedBoundaryDifferenceNearLedger N g r U Q H +
        h15NormalizedBoundaryDifferenceFarLedger N g r U Q H := by
  exact h15NormalizedBoundaryEndpointPairFilteredPhaseAggregate_eq_split
    N g r U Q h15DifferenceEndpointPairPhase
    (fun r u q v q' => ¬ h15DifferenceEndpointPairCollision r u q v q')
    (fun r u q v q' =>
      h15DifferenceEndpointPairCyclicDistance r u q v q' ≤ H)

theorem h15NormalizedBoundarySumSeparatedLedger_eq_near_add_far
    (N g r U Q H : ℕ) :
    h15NormalizedBoundarySumSeparatedLedger N g r U Q =
      h15NormalizedBoundarySumNearLedger N g r U Q H +
        h15NormalizedBoundarySumFarLedger N g r U Q H := by
  exact h15NormalizedBoundaryEndpointPairFilteredPhaseAggregate_eq_split
    N g r U Q h15SumEndpointPairPhase
    (fun r u q v q' => ¬ h15SumEndpointPairCollision r u q v q')
    (fun r u q v q' => h15SumEndpointPairCyclicDistance r u q v q' ≤ H)

noncomputable def h15NormalizedBoundaryPhaseNearLedger
    (N g r U Q H : ℕ) : ℝ :=
  (h15NormalizedBoundaryDifferenceNearLedger N g r U Q H -
    h15NormalizedBoundarySumNearLedger N g r U Q H) / 2

noncomputable def h15NormalizedBoundaryPhaseFarLedger
    (N g r U Q H : ℕ) : ℝ :=
  (h15NormalizedBoundaryDifferenceFarLedger N g r U Q H -
    h15NormalizedBoundarySumFarLedger N g r U Q H) / 2

theorem h15NormalizedBoundaryPhaseSeparatedLedger_eq_near_add_far
    (N g r U Q H : ℕ) :
    h15NormalizedBoundaryPhaseSeparatedLedger N g r U Q =
      h15NormalizedBoundaryPhaseNearLedger N g r U Q H +
        h15NormalizedBoundaryPhaseFarLedger N g r U Q H := by
  unfold h15NormalizedBoundaryPhaseSeparatedLedger
    h15NormalizedBoundaryPhaseNearLedger
    h15NormalizedBoundaryPhaseFarLedger
  rw [h15NormalizedBoundaryDifferenceSeparatedLedger_eq_near_add_far,
    h15NormalizedBoundarySumSeparatedLedger_eq_near_add_far]
  ring

/-- Exact collision/near/far expansion at every threshold. -/
theorem h15NormalizedBoundaryExplicitCrossModulusCorrelation_eq_collision_add_near_add_far
    {N g r U Q H : ℕ} (hQ : 0 < Q) :
    h15NormalizedBoundaryExplicitCrossModulusCorrelation N g r U Q =
      h15NormalizedBoundaryPhaseCollisionLedger N g r U Q +
        h15NormalizedBoundaryPhaseNearLedger N g r U Q H +
          h15NormalizedBoundaryPhaseFarLedger N g r U Q H := by
  rw [h15NormalizedBoundaryExplicitCrossModulusCorrelation_eq_collision_add_separated
    hQ,
    h15NormalizedBoundaryPhaseSeparatedLedger_eq_near_add_far]
  ring

/-- The exact remaining dispersion gate after a tunable spacing split. -/
theorem h15CorrectionCoupledCrossModulusFrequencyDispersion_iff_phaseNearFar
    {N g r U Q H : ℕ} (hQ : 0 < Q) (Delta : ℝ) :
    H15CorrectionCoupledCrossModulusFrequencyDispersion N g r U Q Delta ↔
      0 ≤ Delta ∧
        h15NormalizedBoundaryPhaseNearLedger N g r U Q H +
            h15NormalizedBoundaryPhaseFarLedger N g r U Q H ≤
          Delta * h15NormalizedBoundaryCrossModulusFrequencyEnergy N g U Q -
            h15NormalizedBoundaryPhaseCollisionDefect N g r U Q := by
  rw [h15CorrectionCoupledCrossModulusFrequencyDispersion_iff_phaseSeparated
    hQ]
  rw [h15NormalizedBoundaryPhaseSeparatedLedger_eq_near_add_far]

end NBMellinTools.NB12
