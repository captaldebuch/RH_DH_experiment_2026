/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FinalBoundaryRationalSpacing

/-!
# NB12zzf: elementary spacing-cardinality stop test

The exact spacing ledger is tested against the currently available endpoint
geometry.  At threshold zero the reduced near-noncollision sector is empty,
as it must be.  At a positive threshold, however, subset cardinality alone
gives only the old `2*(q+1)` endpoint bound and no factor depending on the
spacing threshold.  Therefore the existing geometric estimates cannot close
the near sector; a genuine arithmetic shell estimate is required.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate
open Complex

namespace NBMellinTools.NB12

noncomputable def h15ReducedDifferenceNearEndpointSupport
    (r u q U L q' H : ℕ) : Finset ℕ := by
  classical
  exact (h15NormalizedSuperperiodBoundarySupport U L q').filter
    (fun v => Nat.Coprime v q' ∧
      ¬ h15DifferenceEndpointPairCollision r u q v q' ∧
        h15DifferenceEndpointPairCyclicDistance r u q v q' ≤ H)

noncomputable def h15ReducedSumNearEndpointSupport
    (r u q U L q' H : ℕ) : Finset ℕ := by
  classical
  exact (h15NormalizedSuperperiodBoundarySupport U L q').filter
    (fun v => Nat.Coprime v q' ∧
      ¬ h15SumEndpointPairCollision r u q v q' ∧
        h15SumEndpointPairCyclicDistance r u q v q' ≤ H)

noncomputable def h15ReducedDifferenceFarEndpointSupport
    (r u q U L q' H : ℕ) : Finset ℕ := by
  classical
  exact (h15NormalizedSuperperiodBoundarySupport U L q').filter
    (fun v => Nat.Coprime v q' ∧
      ¬ h15DifferenceEndpointPairCollision r u q v q' ∧
        ¬ h15DifferenceEndpointPairCyclicDistance r u q v q' ≤ H)

noncomputable def h15ReducedSumFarEndpointSupport
    (r u q U L q' H : ℕ) : Finset ℕ := by
  classical
  exact (h15NormalizedSuperperiodBoundarySupport U L q').filter
    (fun v => Nat.Coprime v q' ∧
      ¬ h15SumEndpointPairCollision r u q v q' ∧
        ¬ h15SumEndpointPairCyclicDistance r u q v q' ≤ H)

/-- Any spacing-filtered endpoint family inherits only the full endpoint
cardinality from the current geometric input. -/
theorem card_filter_h15NormalizedSuperperiodBoundarySupport_le_density
    {U L q : ℕ} (hL : 0 < L) (hq : 0 < q)
    (P : ℕ → Prop) [DecidablePred P] :
    ((h15NormalizedSuperperiodBoundarySupport U L q).filter P).card ≤
      2 * (q + 1) := by
  exact (Finset.card_filter_le _ _).trans
    (card_h15NormalizedSuperperiodBoundarySupport_le_density U L q hL hq)

theorem card_h15ReducedDifferenceNearEndpointSupport_le
    {r u q U L q' H : ℕ} (hL : 0 < L) (hq' : 0 < q') :
    (h15ReducedDifferenceNearEndpointSupport r u q U L q' H).card ≤
      2 * (q' + 1) := by
  classical
  unfold h15ReducedDifferenceNearEndpointSupport
  exact card_filter_h15NormalizedSuperperiodBoundarySupport_le_density hL hq' _

theorem card_h15ReducedSumNearEndpointSupport_le
    {r u q U L q' H : ℕ} (hL : 0 < L) (hq' : 0 < q') :
    (h15ReducedSumNearEndpointSupport r u q U L q' H).card ≤
      2 * (q' + 1) := by
  classical
  unfold h15ReducedSumNearEndpointSupport
  exact card_filter_h15NormalizedSuperperiodBoundarySupport_le_density hL hq' _

theorem card_h15ReducedDifferenceFarEndpointSupport_le
    {r u q U L q' H : ℕ} (hL : 0 < L) (hq' : 0 < q') :
    (h15ReducedDifferenceFarEndpointSupport r u q U L q' H).card ≤
      2 * (q' + 1) := by
  classical
  unfold h15ReducedDifferenceFarEndpointSupport
  exact card_filter_h15NormalizedSuperperiodBoundarySupport_le_density hL hq' _

theorem card_h15ReducedSumFarEndpointSupport_le
    {r u q U L q' H : ℕ} (hL : 0 < L) (hq' : 0 < q') :
    (h15ReducedSumFarEndpointSupport r u q U L q' H).card ≤
      2 * (q' + 1) := by
  classical
  unfold h15ReducedSumFarEndpointSupport
  exact card_filter_h15NormalizedSuperperiodBoundarySupport_le_density hL hq' _

/-- There are no reduced difference pairs which are simultaneously an exact
zero-distance pair and a noncollision. -/
theorem h15ReducedDifferenceNearEndpointSupport_zero
    {r u q U L q' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (huq : Nat.Coprime u q) :
    h15ReducedDifferenceNearEndpointSupport r u q U L q' 0 = ∅ := by
  classical
  unfold h15ReducedDifferenceNearEndpointSupport
  rw [Finset.filter_eq_empty_iff]
  intro v _hv
  rintro ⟨hvq', hnot, hdist⟩
  have hzero :
      h15DifferenceEndpointPairCyclicDistance r u q v q' = 0 := by
    omega
  exact hnot
    ((h15DifferenceEndpointPairCyclicDistance_eq_zero_iff_collision
      hq hq' huq hvq').1 hzero)

/-- The analogous zero-threshold sum sector is empty. -/
theorem h15ReducedSumNearEndpointSupport_zero
    {r u q U L q' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (huq : Nat.Coprime u q) :
    h15ReducedSumNearEndpointSupport r u q U L q' 0 = ∅ := by
  classical
  unfold h15ReducedSumNearEndpointSupport
  rw [Finset.filter_eq_empty_iff]
  intro v _hv
  rintro ⟨hvq', hnot, hdist⟩
  have hzero : h15SumEndpointPairCyclicDistance r u q v q' = 0 := by
    omega
  exact hnot
    ((h15SumEndpointPairCyclicDistance_eq_zero_iff_collision
      hq hq' huq hvq').1 hzero)

end NBMellinTools.NB12
