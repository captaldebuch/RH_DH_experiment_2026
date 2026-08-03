import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannNormalization

/-!
# Route B9.1: full H15 two-sign Mellin integrand assembly

This file inserts the canonical H15 inverse-residue numerator into the
four-to-two Estermann functional equation.  On `Re(s) > 1`, it assembles the
complete finite numerator sum into two additive Dirichlet series, applies the
proved inverse-coordinate Kloosterman completion frequency by frequency, and
lifts the identity through the full finite `(g,q)` interior aggregate.

The same-sign, opposite-sign, Ramanujan zero-mode, and nonzero Kloosterman
sectors remain separate.  No infinite series is exchanged with an integral,
no Bessel transform is introduced, and no spectral estimate is asserted.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannH15MellinAssembly

open AddChar Complex LSeries ZMod
open scoped BigOperators LSeries.notation
open RH.Criteria.NymanBeurling.BCFLogTaperBettinConreyAggregate
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannFourToTwoCollapse
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannH15NumeratorCompletion
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKloosterman
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKloostermanCompletion
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannNormalization
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannSeries
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi

/-! ## Additive coefficients -/

/-- The positive-phase coefficient `d(n) Σ_a C(a,q)e_q(na)`. -/
noncomputable def h15SameSignCoefficient
    (N g q : ℕ) [NeZero q] (n : ℕ) : ℂ :=
  estermannDivisorCoeff n *
    ∑ a ∈ Finset.Icc 2 (N / g),
      if Nat.Coprime a q then
        estermannInteriorValueCoefficient N g a q *
          ZMod.stdAddChar ((n : ZMod q) * (a : ZMod q))
      else 0

/-- The negative-phase coefficient `d(n) Σ_a C(a,q)e_q(-na)`. -/
noncomputable def h15OppositeSignCoefficient
    (N g q : ℕ) [NeZero q] (n : ℕ) : ℂ :=
  estermannDivisorCoeff n *
    ∑ a ∈ Finset.Icc 2 (N / g),
      if Nat.Coprime a q then
        estermannInteriorValueCoefficient N g a q *
          ZMod.stdAddChar (-((n : ZMod q) * (a : ZMod q)))
      else 0

/-- The same-sign coefficient is the finite sum of the natural dual
Estermann coefficients returned by the functional equation. -/
theorem h15SameSignCoefficient_eq_naturalDualSum
    (N g q n : ℕ) [NeZero q] :
    h15SameSignCoefficient N g q n =
      ∑ a ∈ Finset.Icc 2 (N / g),
        if hcop : Nat.Coprime a q then
          estermannInteriorValueCoefficient N g a q *
            estermannCoeff
              (estermannPositiveDualNumerator
                (inverseResidueNumerator a q hcop) q
                (inverseResidueNumerator_coprime a q hcop)) q n
        else 0 := by
  classical
  unfold h15SameSignCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hcop : Nat.Coprime a q
  · rw [if_pos hcop, dif_pos hcop,
      estermannCoeff_positiveDual_inverseResidue]
    ring
  · rw [if_neg hcop, dif_neg hcop]
    simp

/-- The opposite-sign coefficient is the corresponding finite sum of
negative dual Estermann coefficients. -/
theorem h15OppositeSignCoefficient_eq_naturalDualSum
    (N g q n : ℕ) [NeZero q] :
    h15OppositeSignCoefficient N g q n =
      ∑ a ∈ Finset.Icc 2 (N / g),
        if hcop : Nat.Coprime a q then
          estermannInteriorValueCoefficient N g a q *
            estermannCoeff
              (estermannNegativeDualNumerator
                (inverseResidueNumerator a q hcop) q
                (inverseResidueNumerator_coprime a q hcop)) q n
        else 0 := by
  classical
  unfold h15OppositeSignCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hcop : Nat.Coprime a q
  · rw [if_pos hcop, dif_pos hcop,
      estermannCoeff_negativeDual_inverseResidue]
    ring
  · rw [if_neg hcop, dif_neg hcop]
    simp

/-- Collection of repeated natural numerators into the H15 unit weight in
the same-sign channel. -/
theorem h15SameSignCoefficient_eq_unitWeight
    (N g q n : ℕ) [NeZero q] :
    h15SameSignCoefficient N g q n =
      estermannDivisorCoeff n *
        ∑ x : (ZMod q)ˣ,
          h15UnitNumeratorWeight N g q x *
            ZMod.stdAddChar ((n : ZMod q) * (x : ZMod q)) := by
  unfold h15SameSignCoefficient
  rw [sum_h15UnitNumeratorWeight_mul_phase]

/-- Collection of repeated natural numerators in the opposite-sign
channel. -/
theorem h15OppositeSignCoefficient_eq_unitWeight
    (N g q n : ℕ) [NeZero q] :
    h15OppositeSignCoefficient N g q n =
      estermannDivisorCoeff n *
        ∑ x : (ZMod q)ˣ,
          h15UnitNumeratorWeight N g q x *
            ZMod.stdAddChar (-(n : ZMod q) * (x : ZMod q)) := by
  unfold h15OppositeSignCoefficient
  rw [sum_h15UnitNumeratorWeight_mul_phase]
  apply congrArg (estermannDivisorCoeff n * ·)
  apply Finset.sum_congr rfl
  intro a _
  by_cases hcop : Nat.Coprime a q
  · rw [if_pos hcop, if_pos hcop]
    congr 1
    apply congrArg ZMod.stdAddChar
    ring
  · rw [if_neg hcop, if_neg hcop]

/-! ## Absolutely convergent two-series assembly -/

noncomputable def h15SameSignNaturalCoefficient
    (N g q a : ℕ) [NeZero q] : ℕ → ℂ :=
  if hcop : Nat.Coprime a q then
    fun n => estermannInteriorValueCoefficient N g a q *
      estermannCoeff
        (estermannPositiveDualNumerator
          (inverseResidueNumerator a q hcop) q
          (inverseResidueNumerator_coprime a q hcop)) q n
  else 0

noncomputable def h15OppositeSignNaturalCoefficient
    (N g q a : ℕ) [NeZero q] : ℕ → ℂ :=
  if hcop : Nat.Coprime a q then
    fun n => estermannInteriorValueCoefficient N g a q *
      estermannCoeff
        (estermannNegativeDualNumerator
          (inverseResidueNumerator a q hcop) q
          (inverseResidueNumerator_coprime a q hcop)) q n
  else 0

theorem h15SameSignCoefficient_eq_finsetSum
    (N g q : ℕ) [NeZero q] :
    h15SameSignCoefficient N g q =
      ∑ a ∈ Finset.Icc 2 (N / g),
        h15SameSignNaturalCoefficient N g q a := by
  funext n
  rw [h15SameSignCoefficient_eq_naturalDualSum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  unfold h15SameSignNaturalCoefficient
  by_cases hcop : Nat.Coprime a q
  · rw [dif_pos hcop, dif_pos hcop]
  · rw [dif_neg hcop, dif_neg hcop]
    rfl

theorem h15OppositeSignCoefficient_eq_finsetSum
    (N g q : ℕ) [NeZero q] :
    h15OppositeSignCoefficient N g q =
      ∑ a ∈ Finset.Icc 2 (N / g),
        h15OppositeSignNaturalCoefficient N g q a := by
  funext n
  rw [h15OppositeSignCoefficient_eq_naturalDualSum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  unfold h15OppositeSignNaturalCoefficient
  by_cases hcop : Nat.Coprime a q
  · rw [dif_pos hcop, dif_pos hcop]
  · rw [dif_neg hcop, dif_neg hcop]
    rfl

noncomputable def h15SameSignDirichletSeries
    (N g q : ℕ) [NeZero q] (s : ℂ) : ℂ :=
  LSeries (h15SameSignCoefficient N g q) s

noncomputable def h15OppositeSignDirichletSeries
    (N g q : ℕ) [NeZero q] (s : ℂ) : ℂ :=
  LSeries (h15OppositeSignCoefficient N g q) s

noncomputable def h15SameSignNaturalDirichletAggregate
    (N g q : ℕ) [NeZero q] (s : ℂ) : ℂ :=
  ∑ a ∈ Finset.Icc 2 (N / g),
    if hcop : Nat.Coprime a q then
      estermannInteriorValueCoefficient N g a q *
        estermannDirichletSeries
          (estermannPositiveDualNumerator
            (inverseResidueNumerator a q hcop) q
            (inverseResidueNumerator_coprime a q hcop)) q s
    else 0

noncomputable def h15OppositeSignNaturalDirichletAggregate
    (N g q : ℕ) [NeZero q] (s : ℂ) : ℂ :=
  ∑ a ∈ Finset.Icc 2 (N / g),
    if hcop : Nat.Coprime a q then
      estermannInteriorValueCoefficient N g a q *
        estermannDirichletSeries
          (estermannNegativeDualNumerator
            (inverseResidueNumerator a q hcop) q
            (inverseResidueNumerator_coprime a q hcop)) q s
    else 0

theorem h15SameSignDirichletSeries_eq_naturalAggregate
    (N g q : ℕ) [NeZero q] {s : ℂ} (hs : 1 < s.re) :
    h15SameSignDirichletSeries N g q s =
      h15SameSignNaturalDirichletAggregate N g q s := by
  classical
  unfold h15SameSignDirichletSeries
  rw [h15SameSignCoefficient_eq_finsetSum]
  rw [LSeries_sum]
  · unfold h15SameSignNaturalDirichletAggregate
    apply Finset.sum_congr rfl
    intro a _
    by_cases hcop : Nat.Coprime a q
    · simp only [h15SameSignNaturalCoefficient, dif_pos hcop]
      change LSeries
          (estermannInteriorValueCoefficient N g a q •
            estermannCoeff
              (estermannPositiveDualNumerator
                (inverseResidueNumerator a q hcop) q
                (inverseResidueNumerator_coprime a q hcop)) q) s = _
      rw [LSeries_smul]
      rfl
    · simp [h15SameSignNaturalCoefficient, hcop]
  · intro a _
    by_cases hcop : Nat.Coprime a q
    · unfold h15SameSignNaturalCoefficient
      rw [dif_pos hcop]
      change LSeriesSummable
        (estermannInteriorValueCoefficient N g a q •
          estermannCoeff
            (estermannPositiveDualNumerator
              (inverseResidueNumerator a q hcop) q
              (inverseResidueNumerator_coprime a q hcop)) q) s
      exact (estermannCoeff_summable _ _ hs).smul _
    · simp [h15SameSignNaturalCoefficient, hcop]

theorem h15OppositeSignDirichletSeries_eq_naturalAggregate
    (N g q : ℕ) [NeZero q] {s : ℂ} (hs : 1 < s.re) :
    h15OppositeSignDirichletSeries N g q s =
      h15OppositeSignNaturalDirichletAggregate N g q s := by
  classical
  unfold h15OppositeSignDirichletSeries
  rw [h15OppositeSignCoefficient_eq_finsetSum]
  rw [LSeries_sum]
  · unfold h15OppositeSignNaturalDirichletAggregate
    apply Finset.sum_congr rfl
    intro a _
    by_cases hcop : Nat.Coprime a q
    · simp only [h15OppositeSignNaturalCoefficient, dif_pos hcop]
      change LSeries
          (estermannInteriorValueCoefficient N g a q •
            estermannCoeff
              (estermannNegativeDualNumerator
                (inverseResidueNumerator a q hcop) q
                (inverseResidueNumerator_coprime a q hcop)) q) s = _
      rw [LSeries_smul]
      rfl
    · simp [h15OppositeSignNaturalCoefficient, hcop]
  · intro a _
    by_cases hcop : Nat.Coprime a q
    · unfold h15OppositeSignNaturalCoefficient
      rw [dif_pos hcop]
      change LSeriesSummable
        (estermannInteriorValueCoefficient N g a q •
          estermannCoeff
            (estermannNegativeDualNumerator
              (inverseResidueNumerator a q hcop) q
              (inverseResidueNumerator_coprime a q hcop)) q) s
      exact (estermannCoeff_summable _ _ hs).smul _
    · simp [h15OppositeSignNaturalCoefficient, hcop]

/-! ## The full Mellin--Barnes integrand at one modulus -/

noncomputable def h15NaturalNumeratorDualIntegrand
    (N g q : ℕ) [NeZero q] (W : ℂ → ℂ) (s : ℂ) : ℂ :=
  ∑ a ∈ Finset.Icc 2 (N / g),
    if hcop : Nat.Coprime a q then
      estermannInteriorValueCoefficient N g a q * W s *
        estermannNormalizedDualValue
          (inverseResidueNumerator a q hcop) q
          (inverseResidueNumerator_coprime a q hcop) s
    else 0

noncomputable def h15SameSignMellinFactor
    (W : ℂ → ℂ) (q : ℕ) (s : ℂ) : ℂ :=
  W s * (2 * estermannCollapsedCommonFactor q s)

noncomputable def h15OppositeSignMellinFactor
    (W : ℂ → ℂ) (q : ℕ) (s : ℂ) : ℂ :=
  W s *
    (2 * Complex.cos (Real.pi * s) *
      estermannCollapsedCommonFactor q s)

noncomputable def h15TwoSignAdditiveIntegrand
    (N g q : ℕ) [NeZero q] (W : ℂ → ℂ) (s : ℂ) : ℂ :=
  h15SameSignMellinFactor W q s *
      h15SameSignDirichletSeries N g q s +
    h15OppositeSignMellinFactor W q s *
      h15OppositeSignDirichletSeries N g q s

/-- Pointwise full-numerator four-to-two assembly on the absolute-convergence
half-plane. -/
theorem h15NaturalNumeratorDualIntegrand_eq_twoSignAdditive
    (N g q : ℕ) [NeZero q] (W : ℂ → ℂ) {s : ℂ}
    (hs : 1 < s.re) :
    h15NaturalNumeratorDualIntegrand N g q W s =
      h15TwoSignAdditiveIntegrand N g q W s := by
  classical
  unfold h15NaturalNumeratorDualIntegrand h15TwoSignAdditiveIntegrand
    h15SameSignMellinFactor h15OppositeSignMellinFactor
  rw [h15SameSignDirichletSeries_eq_naturalAggregate _ _ _ hs,
    h15OppositeSignDirichletSeries_eq_naturalAggregate _ _ _ hs]
  unfold h15SameSignNaturalDirichletAggregate
    h15OppositeSignNaturalDirichletAggregate
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hcop : Nat.Coprime a q
  · rw [dif_pos hcop, dif_pos hcop, dif_pos hcop]
    rw [estermannNormalizedDualValue_eq_classical_four_to_two
      (inverseResidueNumerator a q hcop) q
      (inverseResidueNumerator_coprime a q hcop) hs]
    ring
  · rw [dif_neg hcop, dif_neg hcop, dif_neg hcop]
    ring

/-! ## Exact frequencywise Kloosterman completion -/

noncomputable def h15SameSignCompletedCoefficient
    (N g q : ℕ) [NeZero q] (n : ℕ) : ℂ :=
  estermannDivisorCoeff n * (q : ℂ)⁻¹ *
    ∑ m : ZMod q,
      inverseCoordinateFourierCoefficient
          (h15UnitNumeratorWeight N g q) m *
        kloostermanSum (n : ZMod q) m

noncomputable def h15OppositeSignCompletedCoefficient
    (N g q : ℕ) [NeZero q] (n : ℕ) : ℂ :=
  estermannDivisorCoeff n * (q : ℂ)⁻¹ *
    ∑ m : ZMod q,
      inverseCoordinateFourierCoefficient
          (h15UnitNumeratorWeight N g q) m *
        kloostermanSum (-(n : ZMod q)) m

theorem h15SameSignCoefficient_eq_completed
    (N g q n : ℕ) [NeZero q] :
    h15SameSignCoefficient N g q n =
      h15SameSignCompletedCoefficient N g q n := by
  unfold h15SameSignCoefficient h15SameSignCompletedCoefficient
  rw [h15NumeratorAdditiveSum_eq_kloostermanCompletion]
  ring

theorem h15OppositeSignCoefficient_eq_completed
    (N g q n : ℕ) [NeZero q] :
    h15OppositeSignCoefficient N g q n =
      h15OppositeSignCompletedCoefficient N g q n := by
  unfold h15OppositeSignCoefficient h15OppositeSignCompletedCoefficient
  have hphase := h15NumeratorAdditiveSum_eq_kloostermanCompletion
    N g q (-(n : ZMod q))
  have hphase' :
      (∑ a ∈ Finset.Icc 2 (N / g),
        if Nat.Coprime a q then
          estermannInteriorValueCoefficient N g a q *
            ZMod.stdAddChar (-((n : ZMod q) * (a : ZMod q)))
        else 0) =
        (q : ℂ)⁻¹ *
          ∑ m : ZMod q,
            inverseCoordinateFourierCoefficient
                (h15UnitNumeratorWeight N g q) m *
              kloostermanSum (-(n : ZMod q)) m := by
    rw [← hphase]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hcop : Nat.Coprime a q
    · rw [if_pos hcop, if_pos hcop]
      congr 1
      apply congrArg ZMod.stdAddChar
      ring
    · rw [if_neg hcop, if_neg hcop]
  rw [hphase']
  ring

noncomputable def h15SameSignCompletedDirichletSeries
    (N g q : ℕ) [NeZero q] (s : ℂ) : ℂ :=
  LSeries (h15SameSignCompletedCoefficient N g q) s

noncomputable def h15OppositeSignCompletedDirichletSeries
    (N g q : ℕ) [NeZero q] (s : ℂ) : ℂ :=
  LSeries (h15OppositeSignCompletedCoefficient N g q) s

theorem h15SameSignDirichletSeries_eq_completed
    (N g q : ℕ) [NeZero q] (s : ℂ) :
    h15SameSignDirichletSeries N g q s =
      h15SameSignCompletedDirichletSeries N g q s := by
  unfold h15SameSignDirichletSeries h15SameSignCompletedDirichletSeries
  congr 1
  funext n
  exact h15SameSignCoefficient_eq_completed N g q n

theorem h15OppositeSignDirichletSeries_eq_completed
    (N g q : ℕ) [NeZero q] (s : ℂ) :
    h15OppositeSignDirichletSeries N g q s =
      h15OppositeSignCompletedDirichletSeries N g q s := by
  unfold h15OppositeSignDirichletSeries
    h15OppositeSignCompletedDirichletSeries
  congr 1
  funext n
  exact h15OppositeSignCoefficient_eq_completed N g q n

noncomputable def h15TwoSignCompletedIntegrand
    (N g q : ℕ) [NeZero q] (W : ℂ → ℂ) (s : ℂ) : ℂ :=
  h15SameSignMellinFactor W q s *
      h15SameSignCompletedDirichletSeries N g q s +
    h15OppositeSignMellinFactor W q s *
      h15OppositeSignCompletedDirichletSeries N g q s

theorem h15TwoSignAdditiveIntegrand_eq_completed
    (N g q : ℕ) [NeZero q] (W : ℂ → ℂ) (s : ℂ) :
    h15TwoSignAdditiveIntegrand N g q W s =
      h15TwoSignCompletedIntegrand N g q W s := by
  unfold h15TwoSignAdditiveIntegrand h15TwoSignCompletedIntegrand
  rw [h15SameSignDirichletSeries_eq_completed,
    h15OppositeSignDirichletSeries_eq_completed]

/-- The requested full fixed-modulus bridge from the original H15 numerator
to the two completed Mellin channels. -/
theorem h15NaturalNumeratorDualIntegrand_eq_completed
    (N g q : ℕ) [NeZero q] (W : ℂ → ℂ) {s : ℂ}
    (hs : 1 < s.re) :
    h15NaturalNumeratorDualIntegrand N g q W s =
      h15TwoSignCompletedIntegrand N g q W s := by
  rw [h15NaturalNumeratorDualIntegrand_eq_twoSignAdditive _ _ _ W hs,
    h15TwoSignAdditiveIntegrand_eq_completed]

/-! ## Zero and nonzero completed modes -/

noncomputable def h15SameSignZeroModeCoefficient
    (N g q : ℕ) [NeZero q] (n : ℕ) : ℂ :=
  estermannDivisorCoeff n * (q : ℂ)⁻¹ *
    (inverseCoordinateFourierCoefficient
        (h15UnitNumeratorWeight N g q) 0 *
      ramanujanSum (n : ZMod q))

noncomputable def h15SameSignNonzeroModeCoefficient
    (N g q : ℕ) [NeZero q] (n : ℕ) : ℂ :=
  estermannDivisorCoeff n * (q : ℂ)⁻¹ *
    ∑ m ∈ (Finset.univ.erase (0 : ZMod q)),
      inverseCoordinateFourierCoefficient
          (h15UnitNumeratorWeight N g q) m *
        kloostermanSum (n : ZMod q) m

noncomputable def h15OppositeSignZeroModeCoefficient
    (N g q : ℕ) [NeZero q] (n : ℕ) : ℂ :=
  estermannDivisorCoeff n * (q : ℂ)⁻¹ *
    (inverseCoordinateFourierCoefficient
        (h15UnitNumeratorWeight N g q) 0 *
      ramanujanSum (-(n : ZMod q)))

noncomputable def h15OppositeSignNonzeroModeCoefficient
    (N g q : ℕ) [NeZero q] (n : ℕ) : ℂ :=
  estermannDivisorCoeff n * (q : ℂ)⁻¹ *
    ∑ m ∈ (Finset.univ.erase (0 : ZMod q)),
      inverseCoordinateFourierCoefficient
          (h15UnitNumeratorWeight N g q) m *
        kloostermanSum (-(n : ZMod q)) m

theorem h15SameSignCompletedCoefficient_eq_zero_add_nonzero
    (N g q n : ℕ) [NeZero q] :
    h15SameSignCompletedCoefficient N g q n =
      h15SameSignZeroModeCoefficient N g q n +
        h15SameSignNonzeroModeCoefficient N g q n := by
  unfold h15SameSignCompletedCoefficient h15SameSignZeroModeCoefficient
    h15SameSignNonzeroModeCoefficient
  rw [kloostermanCompletion_eq_zeroMode_add_nonzero]
  ring

theorem h15OppositeSignCompletedCoefficient_eq_zero_add_nonzero
    (N g q n : ℕ) [NeZero q] :
    h15OppositeSignCompletedCoefficient N g q n =
      h15OppositeSignZeroModeCoefficient N g q n +
        h15OppositeSignNonzeroModeCoefficient N g q n := by
  unfold h15OppositeSignCompletedCoefficient
    h15OppositeSignZeroModeCoefficient
    h15OppositeSignNonzeroModeCoefficient
  rw [kloostermanCompletion_eq_zeroMode_add_nonzero]
  ring

/-! ## Full finite H15 interior aggregate -/

/-- The full ordered H15 interior aggregate before finite completion.  The
modulus positivity branch is definitionally active on the summation range;
it only supplies the local `NeZero` instance. -/
noncomputable def h15InteriorNaturalDualIntegrand
    (N : ℕ) (W : ℂ → ℂ) (s : ℂ) : ℂ :=
  ∑ g ∈ Finset.Icc 1 N,
    ∑ q ∈ Finset.Icc 2 (N / g),
      if hq : 0 < q then
        @h15NaturalNumeratorDualIntegrand N g q
          ⟨Nat.ne_of_gt hq⟩ W s
      else 0

/-- The same full ordered interior after exact completion of every modulus
row. -/
noncomputable def h15InteriorTwoSignCompletedIntegrand
    (N : ℕ) (W : ℂ → ℂ) (s : ℂ) : ℂ :=
  ∑ g ∈ Finset.Icc 1 N,
    ∑ q ∈ Finset.Icc 2 (N / g),
      if hq : 0 < q then
        @h15TwoSignCompletedIntegrand N g q
          ⟨Nat.ne_of_gt hq⟩ W s
      else 0

/-- Finite aggregation introduces no remainder: every ordered interior row
is exactly the two-sign completed row. -/
theorem h15InteriorNaturalDualIntegrand_eq_completed
    (N : ℕ) (W : ℂ → ℂ) {s : ℂ} (hs : 1 < s.re) :
    h15InteriorNaturalDualIntegrand N W s =
      h15InteriorTwoSignCompletedIntegrand N W s := by
  classical
  unfold h15InteriorNaturalDualIntegrand
    h15InteriorTwoSignCompletedIntegrand
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro q hqmem
  have hq : 0 < q := by
    have := (Finset.mem_Icc.mp hqmem).1
    omega
  rw [dif_pos hq, dif_pos hq]
  exact @h15NaturalNumeratorDualIntegrand_eq_completed N g q
    ⟨Nat.ne_of_gt hq⟩ W s hs

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannH15MellinAssembly
