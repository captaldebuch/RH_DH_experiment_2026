/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FinalBoundaryFiniteCompletion

/-!
# NB12zzo: finite completion of a literal H15 interval row

For fixed outer endpoint data `(q,d,u)` and a fixed interval block, the inner
endpoint variable `v` is collected on the unit group modulo `q'`.  The doubled
H15 phase is an ordinary additive character at frequency `-2r` in the
difference sector and `2r` in the sum sector.  The generic inverse-coordinate
completion therefore applies exactly.

The result retains the degenerate Ramanujan mode and the nonzero Kloosterman
modes as two separate terms.  No estimate of either term is asserted.
-/

open AddChar Complex ZMod
open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate

namespace NBMellinTools.NB12

/-! ## The two interval-row orientations -/

inductive H15IntervalCompletionOrientation
  | difference
  | sum
  deriving DecidableEq

def h15IntervalCompletionPredicate
    (orientation : H15IntervalCompletionOrientation)
    (r u q v q' K j : ℕ) : Prop :=
  match orientation with
  | .difference =>
      ¬ h15DifferenceEndpointPairCollision r u q v q' ∧
        h15DifferenceEndpointPairCyclicDistance r u q v q' / K = j
  | .sum =>
      ¬ h15SumEndpointPairCollision r u q v q' ∧
        h15SumEndpointPairCyclicDistance r u q v q' / K = j

noncomputable instance h15IntervalCompletionPredicate_decidable
    (orientation : H15IntervalCompletionOrientation)
    (r u q v q' K j : ℕ) :
    Decidable (h15IntervalCompletionPredicate orientation r u q v q' K j) :=
  Classical.propDecidable _

def h15IntervalCompletionFrequency
    {q' : ℕ} [NeZero q']
    (orientation : H15IntervalCompletionOrientation) (r : ℕ) : ZMod q' :=
  match orientation with
  | .difference => -(2 * (r : ZMod q'))
  | .sum => 2 * (r : ZMod q')

/-! ## The literal doubled H15 phase -/

theorem h15DoubledDirectAdditivePhase_eq_stdAddChar
    (r v q' : ℕ) [NeZero q'] (hvq' : Nat.Coprime v q') :
    h15DoubledDirectAdditivePhase r v q' =
      ZMod.stdAddChar ((2 * (r : ZMod q')) * (v : ZMod q')) := by
  unfold h15DoubledDirectAdditivePhase
  rw [h15DirectAdditiveReducedUnitPhase_of_coprime _ _ _ _ hvq']
  have hq' : q' ≠ 0 := NeZero.ne q'
  simp only [h15DirectAdditiveUnitPhase, hq', dite_false]
  rw [pow_two, ← AddChar.map_add_eq_mul]
  congr 1
  ring

theorem h15IntervalCompletionCharacter_eq_phase
    (orientation : H15IntervalCompletionOrientation)
    (r v q' : ℕ) [NeZero q'] (hvq' : Nat.Coprime v q') :
    ZMod.stdAddChar
        (h15IntervalCompletionFrequency orientation r * (v : ZMod q')) =
      match orientation with
      | .difference => conj (h15DoubledDirectAdditivePhase r v q')
      | .sum => h15DoubledDirectAdditivePhase r v q' := by
  cases orientation with
  | difference =>
      simp only [h15IntervalCompletionFrequency]
      rw [h15DoubledDirectAdditivePhase_eq_stdAddChar r v q' hvq',
        ← AddChar.map_neg_eq_conj]
      congr 1
      ring
  | sum =>
      simp only [h15IntervalCompletionFrequency]
      rw [h15DoubledDirectAdditivePhase_eq_stdAddChar r v q' hvq']

/-! ## Collection on the inner unit coordinate -/

/-- The complete signed H15 inner-endpoint coefficient collected on one unit
class modulo `q'`.  Membership in the interval block is kept inside the
coefficient before any completion or absolute value is taken. -/
noncomputable def h15IntervalEndpointUnitWeight
    (orientation : H15IntervalCompletionOrientation)
    (N g r U L' q q' d' u K j : ℕ) [NeZero q']
    (x : (ZMod q')ˣ) : ℂ :=
  ∑ v ∈ h15NormalizedSuperperiodBoundarySupport U L' q',
    if hvq' : Nat.Coprime v q' then
      if h15IntervalCompletionPredicate
          orientation r u q v q' K j then
        if ZMod.unitOfCoprime v hvq' = x then
          (h15NormalizedProgressionCoupledBoundaryPointWeight
            N g U L' q' d' v : ℂ)
        else 0
      else 0
    else 0

/-- Exact recovery of the filtered natural endpoint sum from the collected
unit-group coefficient. -/
theorem sum_h15IntervalEndpointUnitWeight_mul_character
    (orientation : H15IntervalCompletionOrientation)
    (N g r U L' q q' d' u K j : ℕ) [NeZero q'] :
    (∑ x : (ZMod q')ˣ,
        h15IntervalEndpointUnitWeight orientation
            N g r U L' q q' d' u K j x *
          ZMod.stdAddChar
            (h15IntervalCompletionFrequency orientation r *
              (x : ZMod q'))) =
      ∑ v ∈ h15NormalizedSuperperiodBoundarySupport U L' q',
        if h15IntervalCompletionPredicate orientation r u q v q' K j then
          (h15NormalizedProgressionCoupledBoundaryPointWeight
              N g U L' q' d' v : ℂ) *
            ZMod.stdAddChar
              (h15IntervalCompletionFrequency orientation r *
                (v : ZMod q'))
        else 0 := by
  classical
  unfold h15IntervalEndpointUnitWeight
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  have hvq' :=
    coprime_of_mem_h15NormalizedSuperperiodBoundarySupport hv
  simp only [dif_pos hvq']
  by_cases hblock :
      h15IntervalCompletionPredicate orientation r u q v q' K j
  · simp [hblock, ZMod.coe_unitOfCoprime]
  · simp [hblock]

/-- The literal complex interval row, with the original doubled H15 phase. -/
noncomputable def h15ComplexIntervalEndpointRow
    (orientation : H15IntervalCompletionOrientation)
    (N g r U L' q q' d' u K j : ℕ) [NeZero q'] : ℂ :=
  ∑ v ∈ h15NormalizedSuperperiodBoundarySupport U L' q',
    if h15IntervalCompletionPredicate orientation r u q v q' K j then
      (h15NormalizedProgressionCoupledBoundaryPointWeight
          N g U L' q' d' v : ℂ) *
        match orientation with
        | .difference => conj (h15DoubledDirectAdditivePhase r v q')
        | .sum => h15DoubledDirectAdditivePhase r v q'
    else 0

/-- Removing the character leaves exactly the signed endpoint mass of the
same interval block.  This is the coefficient which controls the degenerate
completion mode. -/
theorem sum_h15IntervalEndpointUnitWeight
    (orientation : H15IntervalCompletionOrientation)
    (N g r U L' q q' d' u K j : ℕ) [NeZero q'] :
    (∑ x : (ZMod q')ˣ,
        h15IntervalEndpointUnitWeight orientation
          N g r U L' q q' d' u K j x) =
      ∑ v ∈ h15NormalizedSuperperiodBoundarySupport U L' q',
        if h15IntervalCompletionPredicate orientation r u q v q' K j then
          (h15NormalizedProgressionCoupledBoundaryPointWeight
            N g U L' q' d' v : ℂ)
        else 0 := by
  classical
  unfold h15IntervalEndpointUnitWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  have hvq' :=
    coprime_of_mem_h15NormalizedSuperperiodBoundarySupport hv
  simp only [dif_pos hvq']
  by_cases hblock :
      h15IntervalCompletionPredicate orientation r u q v q' K j
  · simp [hblock]
  · simp [hblock]

/-- The inverse-coordinate zero Fourier coefficient is precisely the signed
mass of the original H15 endpoint interval.  In particular, inversion of the
unit coordinate creates no extra correction term. -/
theorem h15IntervalInverseCoordinateFourierCoefficient_zero_eq_endpointMass
    (orientation : H15IntervalCompletionOrientation)
    (N g r U L' q q' d' u K j : ℕ) [NeZero q'] :
    h15InverseCoordinateFourierCoefficient (q := q')
        (h15IntervalEndpointUnitWeight orientation
          N g r U L' q q' d' u K j) 0 =
      ∑ v ∈ h15NormalizedSuperperiodBoundarySupport U L' q',
        if h15IntervalCompletionPredicate orientation r u q v q' K j then
          (h15NormalizedProgressionCoupledBoundaryPointWeight
            N g U L' q' d' v : ℂ)
        else 0 := by
  rw [h15InverseCoordinateFourierCoefficient_zero]
  calc
    (∑ y : (ZMod q')ˣ,
        h15IntervalEndpointUnitWeight orientation
          N g r U L' q q' d' u K j (y⁻¹)) =
        ∑ x : (ZMod q')ˣ,
          h15IntervalEndpointUnitWeight orientation
            N g r U L' q q' d' u K j x :=
      Equiv.sum_comp (Equiv.inv ((ZMod q')ˣ))
        (h15IntervalEndpointUnitWeight orientation
          N g r U L' q q' d' u K j)
    _ = _ := sum_h15IntervalEndpointUnitWeight orientation
      N g r U L' q q' d' u K j

theorem h15ComplexIntervalEndpointRow_eq_unitAdditiveSum
    (orientation : H15IntervalCompletionOrientation)
    (N g r U L' q q' d' u K j : ℕ) [NeZero q'] :
    h15ComplexIntervalEndpointRow orientation
        N g r U L' q q' d' u K j =
      ∑ x : (ZMod q')ˣ,
        h15IntervalEndpointUnitWeight orientation
            N g r U L' q q' d' u K j x *
          ZMod.stdAddChar
            (h15IntervalCompletionFrequency orientation r *
              (x : ZMod q')) := by
  rw [sum_h15IntervalEndpointUnitWeight_mul_character]
  unfold h15ComplexIntervalEndpointRow
  apply Finset.sum_congr rfl
  intro v hv
  have hvq' :=
    coprime_of_mem_h15NormalizedSuperperiodBoundarySupport hv
  by_cases hblock :
      h15IntervalCompletionPredicate orientation r u q v q' K j
  · simp only [hblock, if_true]
    rw [h15IntervalCompletionCharacter_eq_phase orientation r v q' hvq']
  · simp [hblock]

/-! ## Exact zero/nonzero completion of the H15 row -/

noncomputable def h15ComplexIntervalEndpointZeroMode
    (orientation : H15IntervalCompletionOrientation)
    (N g r U L' q q' d' u K j : ℕ) [NeZero q'] : ℂ :=
  (q' : ℂ)⁻¹ *
    (h15InverseCoordinateFourierCoefficient (q := q')
        (h15IntervalEndpointUnitWeight orientation
          N g r U L' q q' d' u K j) 0 *
      h15RamanujanSum (q := q')
        (h15IntervalCompletionFrequency orientation r))

noncomputable def h15ComplexIntervalEndpointNonzeroMode
    (orientation : H15IntervalCompletionOrientation)
    (N g r U L' q q' d' u K j : ℕ) [NeZero q'] : ℂ :=
  (q' : ℂ)⁻¹ *
    ∑ m ∈ (Finset.univ.erase (0 : ZMod q')),
      h15InverseCoordinateFourierCoefficient (q := q')
          (h15IntervalEndpointUnitWeight orientation
            N g r U L' q q' d' u K j) m *
        h15KloostermanSum (q := q')
          (h15IntervalCompletionFrequency orientation r) m

/-- The completed zero mode in explicit H15 variables: signed endpoint mass
times a Ramanujan factor, divided by the inner modulus. -/
theorem h15ComplexIntervalEndpointZeroMode_eq_endpointMass_mul_ramanujan
    (orientation : H15IntervalCompletionOrientation)
    (N g r U L' q q' d' u K j : ℕ) [NeZero q'] :
    h15ComplexIntervalEndpointZeroMode orientation
        N g r U L' q q' d' u K j =
      (q' : ℂ)⁻¹ *
        ((∑ v ∈ h15NormalizedSuperperiodBoundarySupport U L' q',
            if h15IntervalCompletionPredicate orientation
                r u q v q' K j then
              (h15NormalizedProgressionCoupledBoundaryPointWeight
                N g U L' q' d' v : ℂ)
            else 0) *
          h15RamanujanSum (q := q')
            (h15IntervalCompletionFrequency orientation r)) := by
  unfold h15ComplexIntervalEndpointZeroMode
  rw [h15IntervalInverseCoordinateFourierCoefficient_zero_eq_endpointMass]

/-- Literal H15 interval-row completion.  The equality is finite and exact;
the Ramanujan zero mode is retained next to the nonzero inverse-frequency
sector. -/
theorem h15ComplexIntervalEndpointRow_eq_zeroMode_add_nonzero
    (orientation : H15IntervalCompletionOrientation)
    (N g r U L' q q' d' u K j : ℕ) [NeZero q'] :
    h15ComplexIntervalEndpointRow orientation
        N g r U L' q q' d' u K j =
      h15ComplexIntervalEndpointZeroMode orientation
          N g r U L' q q' d' u K j +
        h15ComplexIntervalEndpointNonzeroMode orientation
          N g r U L' q q' d' u K j := by
  rw [h15ComplexIntervalEndpointRow_eq_unitAdditiveSum]
  unfold h15ComplexIntervalEndpointZeroMode
    h15ComplexIntervalEndpointNonzeroMode
  exact h15UnitAdditiveSum_eq_zeroMode_add_nonzero (q := q')
    (h15IntervalEndpointUnitWeight orientation
      N g r U L' q q' d' u K j)
    (h15IntervalCompletionFrequency orientation r)

end NBMellinTools.NB12
