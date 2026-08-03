import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannH15NumeratorCompletion

/-!
# Route B9.0: normalization bridges for the H15 Mellin--Kuznetsov route

The H15 special value is evaluated at the least residue representing the
inverse of a natural numerator.  Applying the four-to-two Estermann
functional equation inverts that residue once more.  The resulting natural
representative need not equal the original numerator when the latter is at
least the modulus, but the two are equal in `ZMod q`.

This file records that residue-level equality and its two coefficient
consequences.  These are normalization identities only: they use neither an
infinite sum/integral exchange nor a trace formula.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannNormalization

open Complex ZMod
open RH.Criteria.NymanBeurling.BCFLogTaperBettinConreyAggregate
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannFourToTwoCollapse
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannSeries

/-- Inverting the canonical inverse-residue numerator recovers the original
numerator as a residue class.  Natural-number equality would be false when
the numerator is not the least representative modulo `q`. -/
theorem positiveDualNumerator_inverseResidue_cast
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q) :
    (estermannPositiveDualNumerator
        (inverseResidueNumerator a q hcop) q
        (inverseResidueNumerator_coprime a q hcop) : ZMod q) =
      (a : ZMod q) := by
  rw [positiveDualNumerator_cast]
  have hinvunit :
      ZMod.unitOfCoprime (inverseResidueNumerator a q hcop)
          (inverseResidueNumerator_coprime a q hcop) =
        (ZMod.unitOfCoprime a hcop)⁻¹ := by
    apply Units.ext
    change (inverseResidueNumerator a q hcop : ZMod q) =
      (((ZMod.unitOfCoprime a hcop)⁻¹ : (ZMod q)ˣ) : ZMod q)
    unfold inverseResidueNumerator
    exact ZMod.natCast_zmod_val _
  rw [hinvunit]
  simp [ZMod.coe_unitOfCoprime]

/-- The negative dual numerator is the negative of the original H15
numerator as a residue class. -/
theorem negativeDualNumerator_inverseResidue_cast
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q) :
    (estermannNegativeDualNumerator
        (inverseResidueNumerator a q hcop) q
        (inverseResidueNumerator_coprime a q hcop) : ZMod q) =
      -(a : ZMod q) := by
  rw [negativeDualNumerator_cast]
  have hinvunit :
      ZMod.unitOfCoprime (inverseResidueNumerator a q hcop)
          (inverseResidueNumerator_coprime a q hcop) =
        (ZMod.unitOfCoprime a hcop)⁻¹ := by
    apply Units.ext
    change (inverseResidueNumerator a q hcop : ZMod q) =
      (((ZMod.unitOfCoprime a hcop)⁻¹ : (ZMod q)ˣ) : ZMod q)
    unfold inverseResidueNumerator
    exact ZMod.natCast_zmod_val _
  rw [hinvunit]
  simp [ZMod.coe_unitOfCoprime]

/-- The positive Estermann coefficient produced by the functional equation
has exactly the H15 additive phase `e_q(na)`. -/
theorem estermannCoeff_positiveDual_inverseResidue
    (a q n : ℕ) [NeZero q] (hcop : Nat.Coprime a q) :
    estermannCoeff
        (estermannPositiveDualNumerator
          (inverseResidueNumerator a q hcop) q
          (inverseResidueNumerator_coprime a q hcop)) q n =
      estermannDivisorCoeff n *
        ZMod.stdAddChar ((n : ZMod q) * (a : ZMod q)) := by
  unfold estermannCoeff
  rw [estermannAdditivePhase_eq_stdAddChar]
  congr 1
  apply congrArg ZMod.stdAddChar
  push_cast
  rw [positiveDualNumerator_inverseResidue_cast]
  ring

/-- The negative Estermann coefficient produced by the functional equation
has exactly the H15 additive phase `e_q(-na)`. -/
theorem estermannCoeff_negativeDual_inverseResidue
    (a q n : ℕ) [NeZero q] (hcop : Nat.Coprime a q) :
    estermannCoeff
        (estermannNegativeDualNumerator
          (inverseResidueNumerator a q hcop) q
          (inverseResidueNumerator_coprime a q hcop)) q n =
      estermannDivisorCoeff n *
        ZMod.stdAddChar (-((n : ZMod q) * (a : ZMod q))) := by
  unfold estermannCoeff
  rw [estermannAdditivePhase_eq_stdAddChar]
  congr 1
  apply congrArg ZMod.stdAddChar
  push_cast
  rw [negativeDualNumerator_inverseResidue_cast]
  ring

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannNormalization
