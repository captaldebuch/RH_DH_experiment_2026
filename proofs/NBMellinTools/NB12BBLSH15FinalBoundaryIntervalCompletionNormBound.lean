/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FinalBoundaryIntervalCompletionNorm

/-!
# NB12zzs: sharp fiber bound for completed H15 interval coefficients

The literal interval predicate only removes endpoint points.  Consequently
the two-point residue-fiber theorem survives the interval restriction.  This
file transfers that geometry to the unit-coordinate coefficient used by the
Kloosterman completion.
-/

open AddChar Complex ZMod
open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate

namespace NBMellinTools.NB12

/-- A total unit-valued coordinate for the normalized endpoint support.  Its
off-support value is irrelevant; totality lets `Finset.sum_fiberwise` apply
without a dependent membership argument. -/
noncomputable def h15NormalizedBoundarySupportUnit
    (U L q v : ℕ) [NeZero q] : (ZMod q)ˣ :=
  if hv : v ∈ h15NormalizedSuperperiodBoundarySupport U L q then
    ZMod.unitOfCoprime v
      (coprime_of_mem_h15NormalizedSuperperiodBoundarySupport hv)
  else 1

theorem h15NormalizedBoundarySupportUnit_eq_of_mem
    {U L q v : ℕ} [NeZero q]
    (hv : v ∈ h15NormalizedSuperperiodBoundarySupport U L q) :
    h15NormalizedBoundarySupportUnit U L q v =
      ZMod.unitOfCoprime v
        (coprime_of_mem_h15NormalizedSuperperiodBoundarySupport hv) := by
  simp [h15NormalizedBoundarySupportUnit, hv]

theorem coe_h15NormalizedBoundarySupportUnit_of_mem
    {U L q v : ℕ} [NeZero q]
    (hv : v ∈ h15NormalizedSuperperiodBoundarySupport U L q) :
    ((h15NormalizedBoundarySupportUnit U L q v : (ZMod q)ˣ) : ZMod q) = v := by
  rw [h15NormalizedBoundarySupportUnit_eq_of_mem hv,
    ZMod.coe_unitOfCoprime]

/-- Pointwise squared mass after imposing the literal H15 interval predicate,
but before folding the endpoint points into residue classes. -/
noncomputable def h15IntervalEndpointPointL2Mass
    (orientation : H15IntervalCompletionOrientation)
    (N g r U L' q q' d' u K j : ℕ) : ℝ :=
  ∑ v ∈ h15NormalizedSuperperiodBoundarySupport U L' q',
    if h15IntervalCompletionPredicate orientation r u q v q' K j then
      (h15NormalizedProgressionCoupledBoundaryPointWeight
        N g U L' q' d' v) ^ 2
    else 0

/-- The collected unit coefficient is exactly a real fiber sum. -/
theorem h15IntervalEndpointUnitWeight_eq_ofReal_fiberSum
    (orientation : H15IntervalCompletionOrientation)
    (N g r U L' q q' d' u K j : ℕ) [NeZero q']
    (x : (ZMod q')ˣ) :
    h15IntervalEndpointUnitWeight orientation
        N g r U L' q q' d' u K j x =
      ((∑ v ∈
          (h15NormalizedSuperperiodBoundarySupport U L' q').filter
            (fun v => h15NormalizedBoundarySupportUnit U L' q' v = x),
        if h15IntervalCompletionPredicate orientation r u q v q' K j then
          h15NormalizedProgressionCoupledBoundaryPointWeight
            N g U L' q' d' v
        else 0 : ℝ) : ℂ) := by
  classical
  unfold h15IntervalEndpointUnitWeight
  push_cast
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v hv
  have hvq' :=
    coprime_of_mem_h15NormalizedSuperperiodBoundarySupport hv
  rw [h15NormalizedBoundarySupportUnit_eq_of_mem hv]
  simp only [dif_pos hvq']
  by_cases hx : ZMod.unitOfCoprime v hvq' = x <;>
    by_cases hp : h15IntervalCompletionPredicate
      orientation r u q v q' K j <;> simp [hx, hp]

/-- Every support-unit fiber still has at most two points. -/
theorem card_h15NormalizedBoundarySupportUnitFiber_le_two
    {U L q : ℕ} [NeZero q] (hL : 0 < L) (hq : 0 < q)
    (hLq : Nat.Coprime L q) (x : (ZMod q)ˣ) :
    ((h15NormalizedSuperperiodBoundarySupport U L q).filter
      (fun v => h15NormalizedBoundarySupportUnit U L q v = x)).card ≤ 2 := by
  calc
    ((h15NormalizedSuperperiodBoundarySupport U L q).filter
        (fun v => h15NormalizedBoundarySupportUnit U L q v = x)).card ≤
      ((h15NormalizedSuperperiodBoundarySupport U L q).filter
        (fun v : ℕ => (v : ZMod q) = (x : ZMod q))).card := by
      apply Finset.card_le_card
      intro v hv
      rw [Finset.mem_filter] at hv ⊢
      refine ⟨hv.1, ?_⟩
      rw [← coe_h15NormalizedBoundarySupportUnit_of_mem hv.1]
      exact congrArg Units.val hv.2
    _ ≤ 2 :=
      card_h15NormalizedBoundaryResidueFiber_le_two hL hq hLq (x : ZMod q)

/-- The interval restriction preserves the sharp factor-two collision bound.
No absolute value is taken before points in the same residue fiber are
collected. -/
theorem h15IntervalEndpointUnitL2Mass_le_two_mul_pointL2Mass
    (orientation : H15IntervalCompletionOrientation)
    (N g r U L' q q' d' u K j : ℕ) [NeZero q']
    (hL' : 0 < L') (hq' : 0 < q') (hLq' : Nat.Coprime L' q') :
    h15IntervalEndpointUnitL2Mass orientation
        N g r U L' q q' d' u K j ≤
      2 * h15IntervalEndpointPointL2Mass orientation
        N g r U L' q q' d' u K j := by
  classical
  unfold h15IntervalEndpointUnitL2Mass
    h15IntervalEndpointPointL2Mass
  calc
    (∑ x : (ZMod q')ˣ,
        Complex.normSq
          (h15IntervalEndpointUnitWeight orientation
            N g r U L' q q' d' u K j x)) ≤
      ∑ x : (ZMod q')ˣ,
        2 * ∑ v ∈
          (h15NormalizedSuperperiodBoundarySupport U L' q').filter
            (fun v => h15NormalizedBoundarySupportUnit U L' q' v = x),
          (if h15IntervalCompletionPredicate orientation
              r u q v q' K j then
            h15NormalizedProgressionCoupledBoundaryPointWeight
              N g U L' q' d' v
          else 0) ^ 2 := by
      apply Finset.sum_le_sum
      intro x _hx
      rw [h15IntervalEndpointUnitWeight_eq_ofReal_fiberSum,
        Complex.normSq_ofReal]
      calc
        (∑ v ∈
            (h15NormalizedSuperperiodBoundarySupport U L' q').filter
              (fun v => h15NormalizedBoundarySupportUnit U L' q' v = x),
          if h15IntervalCompletionPredicate orientation
              r u q v q' K j then
            h15NormalizedProgressionCoupledBoundaryPointWeight
              N g U L' q' d' v
          else 0) *
            (∑ v ∈
              (h15NormalizedSuperperiodBoundarySupport U L' q').filter
                (fun v => h15NormalizedBoundarySupportUnit U L' q' v = x),
              if h15IntervalCompletionPredicate orientation
                  r u q v q' K j then
                h15NormalizedProgressionCoupledBoundaryPointWeight
                  N g U L' q' d' v
              else 0) ≤
          (((h15NormalizedSuperperiodBoundarySupport U L' q').filter
            (fun v => h15NormalizedBoundarySupportUnit U L' q' v = x)).card : ℝ) *
            ∑ v ∈
              (h15NormalizedSuperperiodBoundarySupport U L' q').filter
                (fun v => h15NormalizedBoundarySupportUnit U L' q' v = x),
              (if h15IntervalCompletionPredicate orientation
                  r u q v q' K j then
                h15NormalizedProgressionCoupledBoundaryPointWeight
                  N g U L' q' d' v
              else 0) ^ 2 := by
            simpa only [sq] using
              (sq_sum_le_card_mul_sum_sq
                (s := (h15NormalizedSuperperiodBoundarySupport U L' q').filter
                  (fun v => h15NormalizedBoundarySupportUnit U L' q' v = x))
                (f := fun v =>
                  if h15IntervalCompletionPredicate orientation
                      r u q v q' K j then
                    h15NormalizedProgressionCoupledBoundaryPointWeight
                      N g U L' q' d' v
                  else 0))
        _ ≤ 2 * ∑ v ∈
              (h15NormalizedSuperperiodBoundarySupport U L' q').filter
                (fun v => h15NormalizedBoundarySupportUnit U L' q' v = x),
              (if h15IntervalCompletionPredicate orientation
                  r u q v q' K j then
                h15NormalizedProgressionCoupledBoundaryPointWeight
                  N g U L' q' d' v
              else 0) ^ 2 := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast
              card_h15NormalizedBoundarySupportUnitFiber_le_two
                hL' hq' hLq' x
          · positivity
    _ = 2 * ∑ v ∈ h15NormalizedSuperperiodBoundarySupport U L' q',
        (if h15IntervalCompletionPredicate orientation
            r u q v q' K j then
          h15NormalizedProgressionCoupledBoundaryPointWeight
            N g U L' q' d' v
        else 0) ^ 2 := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_fiberwise
        (h15NormalizedSuperperiodBoundarySupport U L' q')
        (fun v : ℕ => h15NormalizedBoundarySupportUnit U L' q' v)
        (fun v =>
          (if h15IntervalCompletionPredicate orientation
              r u q v q' K j then
            h15NormalizedProgressionCoupledBoundaryPointWeight
              N g U L' q' d' v
          else 0) ^ 2)
    _ = 2 * ∑ v ∈ h15NormalizedSuperperiodBoundarySupport U L' q',
        if h15IntervalCompletionPredicate orientation
            r u q v q' K j then
          (h15NormalizedProgressionCoupledBoundaryPointWeight
            N g U L' q' d' v) ^ 2
        else 0 := by
      congr 1
      apply Finset.sum_congr rfl
      intro v _hv
      split_ifs <;> simp

/-- Exact Parseval plus the two-point geometry gives the sharp literal
interval coefficient-energy estimate. -/
theorem h15IntervalInverseCoordinateCoefficientEnergy_le
    (orientation : H15IntervalCompletionOrientation)
    (N g r U L' q q' d' u K j : ℕ) [NeZero q']
    (hL' : 0 < L') (hq' : 0 < q') (hLq' : Nat.Coprime L' q') :
    h15IntervalInverseCoordinateCoefficientEnergy orientation
        N g r U L' q q' d' u K j ≤
      2 * (q' : ℝ) * h15IntervalEndpointPointL2Mass orientation
        N g r U L' q q' d' u K j := by
  rw [h15IntervalInverseCoordinateCoefficientEnergy_eq]
  calc
    (q' : ℝ) * h15IntervalEndpointUnitL2Mass orientation
        N g r U L' q q' d' u K j ≤
      (q' : ℝ) *
        (2 * h15IntervalEndpointPointL2Mass orientation
          N g r U L' q q' d' u K j) := by
      gcongr
      exact h15IntervalEndpointUnitL2Mass_le_two_mul_pointL2Mass
        orientation N g r U L' q q' d' u K j hL' hq' hLq'
    _ = _ := by ring

/-- Interval filtering can only decrease the pointwise squared mass. -/
theorem h15IntervalEndpointPointL2Mass_le_boundaryPointL2Mass
    (orientation : H15IntervalCompletionOrientation)
    (N g r U L' q q' d' u K j : ℕ) :
    h15IntervalEndpointPointL2Mass orientation
        N g r U L' q q' d' u K j ≤
      h15NormalizedBoundaryPointL2Mass N g U L' q' d' := by
  unfold h15IntervalEndpointPointL2Mass
    h15NormalizedBoundaryPointL2Mass
  apply Finset.sum_le_sum
  intro v _hv
  split_ifs
  · exact le_rfl
  · positivity

/-- Fully explicit coefficient-energy scale for one literal interval row.
The completion costs `q'`, the two-endpoint folding costs `2`, and boundary
density contributes another factor `2 * (q' + 1)`. -/
theorem h15IntervalInverseCoordinateCoefficientEnergy_le_explicit
    (orientation : H15IntervalCompletionOrientation)
    (N g r U L' q q' d' u K j : ℕ) [NeZero q']
    (hN : 2 ≤ N) (hg : 1 ≤ g) (hU : 0 < U)
    (hL' : 0 < L') (hq' : 0 < q') (hLq' : Nat.Coprime L' q') :
    h15IntervalInverseCoordinateCoefficientEnergy orientation
        N g r U L' q q' d' u K j ≤
      (4 * q' * (q' + 1) : ℝ) * (1 / (U : ℝ)) ^ 4 := by
  calc
    h15IntervalInverseCoordinateCoefficientEnergy orientation
        N g r U L' q q' d' u K j ≤
      2 * (q' : ℝ) * h15IntervalEndpointPointL2Mass orientation
        N g r U L' q q' d' u K j :=
      h15IntervalInverseCoordinateCoefficientEnergy_le orientation
        N g r U L' q q' d' u K j hL' hq' hLq'
    _ ≤ 2 * (q' : ℝ) *
        h15NormalizedBoundaryPointL2Mass N g U L' q' d' := by
      gcongr
      exact h15IntervalEndpointPointL2Mass_le_boundaryPointL2Mass
        orientation N g r U L' q q' d' u K j
    _ ≤ 2 * (q' : ℝ) *
        ((2 * (q' + 1) : ℝ) * (1 / (U : ℝ)) ^ 4) := by
      gcongr
      exact h15NormalizedBoundaryPointL2Mass_le hN hg hU hL' hq'
    _ = (4 * q' * (q' + 1) : ℝ) * (1 / (U : ℝ)) ^ 4 := by
      ring

end NBMellinTools.NB12
