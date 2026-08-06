/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FinalBoundaryRationalSpacingAudit

/-!
# NB12zzg: signed weighted congruence-shell decomposition

Every separated endpoint pair is assigned to its exact nonzero cyclic-residue
shell.  Since supported moduli satisfy `q,q' < 2Q`, fewer than `4Q^2` shells
cover the complete population.  The decomposition retains all signs and H15
weights and produces the precise shellwise analytic gate.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate
open Complex

namespace NBMellinTools.NB12

def h15BoundarySpacingShellCount (Q : ℕ) : ℕ :=
  4 * Q ^ 2

theorem h15CyclicResidueDistance_lt_modulus
    {M a b : ℕ} (hM : 0 < M) :
    h15CyclicResidueDistance M a b < M := by
  unfold h15CyclicResidueDistance
  have ha : a % M < M := Nat.mod_lt _ hM
  have hb : b % M < M := Nat.mod_lt _ hM
  have hd : Nat.dist (a % M) (b % M) < M := by
    unfold Nat.dist
    omega
  exact (min_le_left _ _).trans_lt hd

theorem h15DifferenceEndpointPairCyclicDistance_lt_shellCount
    {N g r Q q q' u v : ℕ} (hQ : 0 < Q)
    (hq : q ∈ h15BettinChandeeSupportedNatBlock N g Q)
    (hq' : q' ∈ h15BettinChandeeSupportedNatBlock N g Q) :
    h15DifferenceEndpointPairCyclicDistance r u q v q' <
      h15BoundarySpacingShellCount Q := by
  have hqb := mem_h15BettinChandeeSupportedNatBlock.mp hq
  have hq'b := mem_h15BettinChandeeSupportedNatBlock.mp hq'
  have hqPos : 0 < q := hQ.trans_le hqb.1
  have hq'Pos : 0 < q' := hQ.trans_le hq'b.1
  have hdist := h15CyclicResidueDistance_lt_modulus
    (a := 2 * u * r * q') (b := 2 * v * r * q)
    (Nat.mul_pos hqPos hq'Pos)
  unfold h15DifferenceEndpointPairCyclicDistance
    h15BoundarySpacingShellCount at *
  have hprod : q * q' < 4 * Q ^ 2 := by
    nlinarith [hqb.2.1, hq'b.2.1]
  exact hdist.trans hprod

theorem h15SumEndpointPairCyclicDistance_lt_shellCount
    {N g r Q q q' u v : ℕ} (hQ : 0 < Q)
    (hq : q ∈ h15BettinChandeeSupportedNatBlock N g Q)
    (hq' : q' ∈ h15BettinChandeeSupportedNatBlock N g Q) :
    h15SumEndpointPairCyclicDistance r u q v q' <
      h15BoundarySpacingShellCount Q := by
  have hqb := mem_h15BettinChandeeSupportedNatBlock.mp hq
  have hq'b := mem_h15BettinChandeeSupportedNatBlock.mp hq'
  have hqPos : 0 < q := hQ.trans_le hqb.1
  have hq'Pos : 0 < q' := hQ.trans_le hq'b.1
  have hdist := h15CyclicResidueDistance_lt_modulus
    (a := 2 * u * r * q' + 2 * v * r * q) (b := 0)
    (Nat.mul_pos hqPos hq'Pos)
  unfold h15SumEndpointPairCyclicDistance
    h15BoundarySpacingShellCount at *
  have hprod : q * q' < 4 * Q ^ 2 := by
    nlinarith [hqb.2.1, hq'b.2.1]
  exact hdist.trans hprod

/-! ## Exact shell ledgers -/

noncomputable def h15NormalizedBoundaryDifferenceShellLedger
    (N g r U Q : ℕ) (e : Fin (h15BoundarySpacingShellCount Q)) : ℝ :=
  h15NormalizedBoundaryEndpointPairFilteredPhaseAggregate N g r U Q
    h15DifferenceEndpointPairPhase
    (fun r u q v q' =>
      ¬ h15DifferenceEndpointPairCollision r u q v q' ∧
        h15DifferenceEndpointPairCyclicDistance r u q v q' = e)

noncomputable def h15NormalizedBoundarySumShellLedger
    (N g r U Q : ℕ) (e : Fin (h15BoundarySpacingShellCount Q)) : ℝ :=
  h15NormalizedBoundaryEndpointPairFilteredPhaseAggregate N g r U Q
    h15SumEndpointPairPhase
    (fun r u q v q' =>
      ¬ h15SumEndpointPairCollision r u q v q' ∧
        h15SumEndpointPairCyclicDistance r u q v q' = e)

theorem h15NormalizedBoundaryDifferenceSeparatedLedger_eq_sum_shells
    {N g r U Q : ℕ} (hQ : 0 < Q) :
    h15NormalizedBoundaryDifferenceSeparatedLedger N g r U Q =
      ∑ e : Fin (h15BoundarySpacingShellCount Q),
        h15NormalizedBoundaryDifferenceShellLedger N g r U Q e := by
  classical
  unfold h15NormalizedBoundaryDifferenceSeparatedLedger
    h15NormalizedBoundaryDifferenceShellLedger
    h15NormalizedBoundaryEndpointPairFilteredPhaseAggregate
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q' hq'Erase
  have hq'Mem := Finset.mem_of_mem_erase hq'Erase
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d' _hd'
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _hu
  let shellOf (v : ℕ) : Fin (h15BoundarySpacingShellCount Q) :=
    ⟨h15DifferenceEndpointPairCyclicDistance r u q v q',
      h15DifferenceEndpointPairCyclicDistance_lt_shellCount hQ hq hq'Mem⟩
  simpa only [Finset.filter_filter, and_assoc, shellOf, Fin.ext_iff] using
    (Finset.sum_fiberwise
      ((h15NormalizedSuperperiodBoundarySupport U
        (h15SquareDivisorProgressionModulus g d') q').filter
          (fun v => ¬ h15DifferenceEndpointPairCollision r u q v q'))
      shellOf
      (fun v =>
        (h15NormalizedProgressionCoupledBoundaryPointWeight N g U
            (h15SquareDivisorProgressionModulus g d) q d u *
          h15NormalizedProgressionCoupledBoundaryPointWeight N g U
            (h15SquareDivisorProgressionModulus g d') q' d' v) *
          h15DifferenceEndpointPairPhase r u q v q'))

theorem h15NormalizedBoundarySumSeparatedLedger_eq_sum_shells
    {N g r U Q : ℕ} (hQ : 0 < Q) :
    h15NormalizedBoundarySumSeparatedLedger N g r U Q =
      ∑ e : Fin (h15BoundarySpacingShellCount Q),
        h15NormalizedBoundarySumShellLedger N g r U Q e := by
  classical
  unfold h15NormalizedBoundarySumSeparatedLedger
    h15NormalizedBoundarySumShellLedger
    h15NormalizedBoundaryEndpointPairFilteredPhaseAggregate
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q' hq'Erase
  have hq'Mem := Finset.mem_of_mem_erase hq'Erase
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d' _hd'
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _hu
  let shellOf (v : ℕ) : Fin (h15BoundarySpacingShellCount Q) :=
    ⟨h15SumEndpointPairCyclicDistance r u q v q',
      h15SumEndpointPairCyclicDistance_lt_shellCount hQ hq hq'Mem⟩
  simpa only [Finset.filter_filter, and_assoc, shellOf, Fin.ext_iff] using
    (Finset.sum_fiberwise
      ((h15NormalizedSuperperiodBoundarySupport U
        (h15SquareDivisorProgressionModulus g d') q').filter
          (fun v => ¬ h15SumEndpointPairCollision r u q v q'))
      shellOf
      (fun v =>
        (h15NormalizedProgressionCoupledBoundaryPointWeight N g U
            (h15SquareDivisorProgressionModulus g d) q d u *
          h15NormalizedProgressionCoupledBoundaryPointWeight N g U
            (h15SquareDivisorProgressionModulus g d') q' d' v) *
          h15SumEndpointPairPhase r u q v q'))

noncomputable def h15NormalizedBoundarySignedCongruenceShellLedger
    (N g r U Q : ℕ) (e : Fin (h15BoundarySpacingShellCount Q)) : ℝ :=
  (h15NormalizedBoundaryDifferenceShellLedger N g r U Q e -
    h15NormalizedBoundarySumShellLedger N g r U Q e) / 2

theorem h15NormalizedBoundaryPhaseSeparatedLedger_eq_sum_signedShells
    {N g r U Q : ℕ} (hQ : 0 < Q) :
    h15NormalizedBoundaryPhaseSeparatedLedger N g r U Q =
      ∑ e : Fin (h15BoundarySpacingShellCount Q),
        h15NormalizedBoundarySignedCongruenceShellLedger N g r U Q e := by
  unfold h15NormalizedBoundaryPhaseSeparatedLedger
    h15NormalizedBoundarySignedCongruenceShellLedger
  rw [h15NormalizedBoundaryDifferenceSeparatedLedger_eq_sum_shells hQ,
    h15NormalizedBoundarySumSeparatedLedger_eq_sum_shells hQ,
    ← Finset.sum_div, Finset.sum_sub_distrib]

/-- The final correction-coupled gate in exact shellwise form. -/
theorem h15CorrectionCoupledCrossModulusFrequencyDispersion_iff_signedShells
    {N g r U Q : ℕ} (hQ : 0 < Q) (Delta : ℝ) :
    H15CorrectionCoupledCrossModulusFrequencyDispersion N g r U Q Delta ↔
      0 ≤ Delta ∧
        (∑ e : Fin (h15BoundarySpacingShellCount Q),
            h15NormalizedBoundarySignedCongruenceShellLedger N g r U Q e) ≤
          Delta * h15NormalizedBoundaryCrossModulusFrequencyEnergy N g U Q -
            h15NormalizedBoundaryPhaseCollisionDefect N g r U Q := by
  rw [h15CorrectionCoupledCrossModulusFrequencyDispersion_iff_phaseSeparated
    hQ,
    h15NormalizedBoundaryPhaseSeparatedLedger_eq_sum_signedShells hQ]

end NBMellinTools.NB12
