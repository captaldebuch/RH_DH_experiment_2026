import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannKuznetsovProof

/-!
# Route B8.2: finite Kloosterman infrastructure

The extracted Estermann dual kernel must eventually be identified with a
Bessel transform of classical Kloosterman sums before a Kuznetsov formula can
be applied.  Mathlib currently has no Kloosterman-sum definition, so this file
starts the required arithmetic layer with the complete sum over units of
`ZMod q`.

Only finite algebra is proved here: symmetry, the zero-frequency value, and
the triangle-inequality bound.  No Weil or Kuznetsov estimate is asserted.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannKloosterman

open AddChar Complex ZMod
open scoped BigOperators

/-- The classical Kloosterman sum on two residue frequencies. -/
noncomputable def kloostermanSum
    {q : ℕ} [NeZero q] (m n : ZMod q) : ℂ :=
  ∑ x : (ZMod q)ˣ,
    ZMod.stdAddChar (m * (x : ZMod q) + n * ((x⁻¹ : (ZMod q)ˣ) : ZMod q))

/-- Interchanging the two frequencies corresponds to inversion of the unit
summation variable. -/
theorem kloostermanSum_comm
    {q : ℕ} [NeZero q] (m n : ZMod q) :
    kloostermanSum m n = kloostermanSum n m := by
  classical
  unfold kloostermanSum
  apply Fintype.sum_equiv (Equiv.inv (ZMod q)ˣ)
  intro x
  congr 1
  simp only [Equiv.inv_apply, inv_inv]
  ring

/-- At zero frequency every summand is one, so the sum is Euler's totient. -/
@[simp] theorem kloostermanSum_zero_zero
    (q : ℕ) [NeZero q] :
    @kloostermanSum q _ 0 0 = (q.totient : ℂ) := by
  classical
  simp [kloostermanSum, ZMod.card_units_eq_totient]

/-- The unconditional finite triangle bound.  This deliberately does not
pretend to be the square-root cancellation supplied by Weil's theorem. -/
theorem norm_kloostermanSum_le_totient
    {q : ℕ} [NeZero q] (m n : ZMod q) :
    ‖kloostermanSum m n‖ ≤ (q.totient : ℝ) := by
  classical
  unfold kloostermanSum
  calc
    ‖∑ x : (ZMod q)ˣ,
        ZMod.stdAddChar
          (m * (x : ZMod q) + n * ((x⁻¹ : (ZMod q)ˣ) : ZMod q))‖ ≤
      ∑ x : (ZMod q)ˣ,
        ‖ZMod.stdAddChar
          (m * (x : ZMod q) + n * ((x⁻¹ : (ZMod q)ˣ) : ZMod q))‖ :=
        norm_sum_le _ _
    _ = ∑ _x : (ZMod q)ˣ, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [ZMod.stdAddChar_apply, Circle.norm_coe]
    _ = (q.totient : ℝ) := by
      simp [ZMod.card_units_eq_totient]

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannKloosterman
