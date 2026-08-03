import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannCompletionLift

/-!
# Route B8.9: H15 numerator-residue completion

For fixed H15 scale `N`, gcd slice `g`, and modulus `q`, the natural
numerators `a` need not give distinct residue classes modulo `q`.  This module
collects all repeated representatives into an exact weight on `(ZMod q)ˣ`
and applies the inverse-coordinate Kloosterman completion to that weight.

This is the first H15-specific finite instantiation of the generic completion
machinery.  The frequency `n` remains arbitrary, so the theorem can later be
applied termwise to a regularised inverse-Mellin expansion.  No exchange of an
infinite series with an integral is performed here.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannH15NumeratorCompletion

open AddChar Complex ZMod
open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKloosterman
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKloostermanCompletion

/-- Aggregate every admissible natural numerator which represents the same
unit residue modulo `q`. -/
noncomputable def h15UnitNumeratorWeight
    (N g q : ℕ) [NeZero q] (x : (ZMod q)ˣ) : ℂ :=
  ∑ a ∈ Finset.Icc 2 (N / g),
    if hcop : Nat.Coprime a q then
      if x = ZMod.unitOfCoprime a hcop then
        estermannInteriorValueCoefficient N g a q
      else 0
    else 0

/-- Summing the collected unit weight recovers exactly the original finite
sum over natural coprime numerators, including repeated residue
representatives. -/
theorem sum_h15UnitNumeratorWeight_mul_phase
    (N g q : ℕ) [NeZero q] (n : ZMod q) :
    (∑ x : (ZMod q)ˣ,
        h15UnitNumeratorWeight N g q x *
          ZMod.stdAddChar (n * (x : ZMod q))) =
      ∑ a ∈ Finset.Icc 2 (N / g),
        if Nat.Coprime a q then
          estermannInteriorValueCoefficient N g a q *
            ZMod.stdAddChar (n * (a : ZMod q))
        else 0 := by
  classical
  unfold h15UnitNumeratorWeight
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hcop : Nat.Coprime a q
  · simp only [dif_pos hcop, if_pos hcop]
    simp [ZMod.coe_unitOfCoprime]
  · simp only [dif_neg hcop, if_neg hcop]
    simp

/-- Exact H15 numerator completion at one modulus and one reciprocal-series
frequency. -/
theorem h15NumeratorAdditiveSum_eq_kloostermanCompletion
    (N g q : ℕ) [NeZero q] (n : ZMod q) :
    (∑ a ∈ Finset.Icc 2 (N / g),
        if Nat.Coprime a q then
          estermannInteriorValueCoefficient N g a q *
            ZMod.stdAddChar (n * (a : ZMod q))
        else 0) =
      (q : ℂ)⁻¹ *
        ∑ m : ZMod q,
          inverseCoordinateFourierCoefficient
              (h15UnitNumeratorWeight N g q) m *
            kloostermanSum n m := by
  rw [← sum_h15UnitNumeratorWeight_mul_phase]
  exact unitAdditiveSum_eq_kloostermanCompletion
    (h15UnitNumeratorWeight N g q) n

/-- The H15 numerator completion with its Ramanujan zero mode and nonzero
Kloosterman frequencies displayed separately. -/
theorem h15NumeratorAdditiveSum_eq_zero_add_nonzero
    (N g q : ℕ) [NeZero q] (n : ZMod q) :
    (∑ a ∈ Finset.Icc 2 (N / g),
        if Nat.Coprime a q then
          estermannInteriorValueCoefficient N g a q *
            ZMod.stdAddChar (n * (a : ZMod q))
        else 0) =
      (q : ℂ)⁻¹ *
        (inverseCoordinateFourierCoefficient
            (h15UnitNumeratorWeight N g q) 0 * ramanujanSum n) +
      (q : ℂ)⁻¹ *
        ∑ m ∈ (Finset.univ.erase (0 : ZMod q)),
          inverseCoordinateFourierCoefficient
              (h15UnitNumeratorWeight N g q) m *
            kloostermanSum n m := by
  rw [h15NumeratorAdditiveSum_eq_kloostermanCompletion]
  rw [kloostermanCompletion_eq_zeroMode_add_nonzero]
  ring

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannH15NumeratorCompletion
