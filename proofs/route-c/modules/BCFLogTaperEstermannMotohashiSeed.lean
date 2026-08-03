import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannBilinearTraceTarget

/-!
# BT1-A: the finite H15 Motohashi seed and its exact unfolding

Before introducing an automorphic quotient, the H15 seed has a canonical
finite arithmetic part: a sign, divisor frequency `n`, completed frequency
`m : ZMod q`, inverse-coordinate Fourier coefficient, Kloosterman sum, and
physical Mellin--Barnes kernel.

This file proves its exact finite-orbit unfolding.  The `m = 0` mode is
displayed separately and the final aggregate keeps both signs.  No
automorphy, Poincare convergence, trace formula, or decay estimate is
asserted.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiSeed

open Complex MeasureTheory ZMod
open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannBilinearTraceTarget
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannGlobalExchange
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannH15MellinAssembly
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannH15NumeratorCompletion
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKloosterman
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKloostermanCompletion
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannRegularizedKernels
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannSeries
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi

/-- The two Kloosterman/Mellin branches produced by the Estermann functional
equation. -/
inductive H15MotohashiSign
  | same
  | opposite
  deriving DecidableEq

/-- Arithmetic frequency in the Kloosterman sum for a selected sign. -/
def h15MotohashiSignedFrequency
    (sign : H15MotohashiSign) (q n : ℕ) [NeZero q] : ZMod q :=
  match sign with
  | .same => (n : ZMod q)
  | .opposite => -(n : ZMod q)

/-- The physical Mellin--Barnes kernel for a selected sign. -/
noncomputable def h15MotohashiSignedKernel
    (sign : H15MotohashiSign) (η c : ℝ) (q n : ℕ) : ℂ :=
  match sign with
  | .same => h15SameSignMellinKernel η c q n
  | .opposite => h15OppositeSignMellinKernel η c q n

/-- The existing zero-corrected coefficient, selected without changing its
zero/nonzero completion convention. -/
noncomputable def h15MotohashiZeroCorrectedCoefficient
    (sign : H15MotohashiSign) (N g q : ℕ) [NeZero q] (n : ℕ) : ℂ :=
  match sign with
  | .same => h15SameSignZeroCorrectedBilinearCoefficient N g q n
  | .opposite => h15OppositeSignZeroCorrectedBilinearCoefficient N g q n

/-- The finite arithmetic big-cell seed at completed frequency `m`.  The
physical kernel is included so that its orbit unfolds directly to H15. -/
noncomputable def h15MotohashiArithmeticSeed
    (N g q : ℕ) [NeZero q] (sign : H15MotohashiSign)
    (η c : ℝ) (n : ℕ) (m : ZMod q) : ℂ :=
  estermannDivisorCoeff n * (q : ℂ)⁻¹ *
      inverseCoordinateFourierCoefficient
        (h15UnitNumeratorWeight N g q) m *
      kloostermanSum (h15MotohashiSignedFrequency sign q n) m *
    ((2 * Real.pi : ℂ) * h15MotohashiSignedKernel sign η c q n)

/-- The zero orbit is explicit; it is not passed silently to a trace formula
that excludes degenerate Kloosterman modes. -/
theorem h15MotohashiArithmeticSeed_zero_eq
    (N g q : ℕ) [NeZero q] (sign : H15MotohashiSign)
    (η c : ℝ) (n : ℕ) :
    h15MotohashiArithmeticSeed N g q sign η c n 0 =
      (match sign with
        | .same => h15SameSignZeroModeCoefficient N g q n
        | .opposite => h15OppositeSignZeroModeCoefficient N g q n) *
        ((2 * Real.pi : ℂ) * h15MotohashiSignedKernel sign η c q n) := by
  cases sign <;>
    simp only [h15MotohashiArithmeticSeed, h15MotohashiSignedFrequency,
      h15MotohashiSignedKernel]
  · unfold h15SameSignZeroModeCoefficient
    rw [kloostermanSum_zero_eq_ramanujanSum]
    ring
  · unfold h15OppositeSignZeroModeCoefficient
    rw [kloostermanSum_zero_eq_ramanujanSum]
    ring

/-- Exact zero/nonzero orbit ledger for the finite completed frequency. -/
theorem h15MotohashiArithmeticSeed_orbit_eq_zero_add_nonzero
    (N g q : ℕ) [NeZero q] (sign : H15MotohashiSign)
    (η c : ℝ) (n : ℕ) :
    (∑ m : ZMod q, h15MotohashiArithmeticSeed N g q sign η c n m) =
      h15MotohashiArithmeticSeed N g q sign η c n 0 +
        ∑ m ∈ (Finset.univ.erase (0 : ZMod q)),
          h15MotohashiArithmeticSeed N g q sign η c n m := by
  calc
    (∑ m : ZMod q, h15MotohashiArithmeticSeed N g q sign η c n m) =
        (∑ m ∈ (Finset.univ.erase (0 : ZMod q)),
          h15MotohashiArithmeticSeed N g q sign η c n m) +
          h15MotohashiArithmeticSeed N g q sign η c n 0 :=
      (Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod q))).symm
    _ = h15MotohashiArithmeticSeed N g q sign η c n 0 +
        ∑ m ∈ (Finset.univ.erase (0 : ZMod q)),
          h15MotohashiArithmeticSeed N g q sign η c n m := by
      rw [add_comm]

/-- Unfolding the finite completed-frequency orbit gives exactly the existing
zero-corrected coefficient times its physical kernel. -/
theorem h15MotohashiArithmeticSeed_orbit_eq_zeroCorrected
    (N g q : ℕ) [NeZero q] (sign : H15MotohashiSign)
    (η c : ℝ) (n : ℕ) :
    (∑ m : ZMod q, h15MotohashiArithmeticSeed N g q sign η c n m) =
      h15MotohashiZeroCorrectedCoefficient sign N g q n *
        ((2 * Real.pi : ℂ) * h15MotohashiSignedKernel sign η c q n) := by
  cases sign <;>
    simp only [h15MotohashiArithmeticSeed, h15MotohashiSignedFrequency,
      h15MotohashiSignedKernel, h15MotohashiZeroCorrectedCoefficient]
  · rw [h15SameSignZeroCorrectedBilinearCoefficient_eq_completed]
    unfold h15SameSignCompletedCoefficient
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _
    ring
  · rw [h15OppositeSignZeroCorrectedBilinearCoefficient_eq_completed]
    unfold h15OppositeSignCompletedCoefficient
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _
    ring

/-- Gaussian damping and absolute convergence on `Re(s) = c > 1` make the
orbital `n`-series genuinely summable.  Thus the later `tsum` does not rely on
Lean's default value for a divergent series. -/
theorem h15MotohashiArithmeticSeed_orbit_summable
    (N g q : ℕ) [NeZero q] (sign : H15MotohashiSign)
    (η c : ℝ) (hη : 0 < η) (hc : 1 < c) :
    Summable (fun n : ℕ =>
      ∑ m : ZMod q, h15MotohashiArithmeticSeed
        N g q sign η c n m) := by
  cases sign
  · let F : ℝ → ℂ := fun t =>
      h15SameSignMellinFactor (estermannGaussianEvaluationWeight η) q
        (estermannVerticalPoint c t)
    let a : ℕ → ℂ := h15SameSignCoefficient N g q
    have hF : Integrable F := by
      exact integrable_h15SameSignMellinFactor_vertical η c q hη hc
    have ha : LSeriesSummable a (c : ℂ) := by
      exact h15SameSignCoefficient_summable N g q (by simpa using hc)
    have hHas := hasSum_integral_of_summable_integral_norm
      (fun n => integrable_mul_LSeries_term_vertical F a c hF n)
      (summable_integral_norm_mul_LSeries_term_vertical F a c hF ha)
    refine hHas.summable.congr ?_
    intro n
    dsimp [F, a]
    rw [h15MotohashiArithmeticSeed_orbit_eq_zeroCorrected]
    simp only [h15MotohashiZeroCorrectedCoefficient,
      h15MotohashiSignedKernel]
    rw [h15SameSignZeroCorrectedBilinearCoefficient_eq_completed]
    by_cases hn : n = 0
    · subst n
      simp
    · exact integral_sameSignTerm_eq_completedKernel N g q η c hn
  · let F : ℝ → ℂ := fun t =>
      h15OppositeSignMellinFactor (estermannGaussianEvaluationWeight η) q
        (estermannVerticalPoint c t)
    let a : ℕ → ℂ := h15OppositeSignCoefficient N g q
    have hF : Integrable F := by
      exact integrable_h15OppositeSignMellinFactor_vertical η c q hη hc
    have ha : LSeriesSummable a (c : ℂ) := by
      exact h15OppositeSignCoefficient_summable N g q (by simpa using hc)
    have hHas := hasSum_integral_of_summable_integral_norm
      (fun n => integrable_mul_LSeries_term_vertical F a c hF n)
      (summable_integral_norm_mul_LSeries_term_vertical F a c hF ha)
    refine hHas.summable.congr ?_
    intro n
    dsimp [F, a]
    rw [h15MotohashiArithmeticSeed_orbit_eq_zeroCorrected]
    simp only [h15MotohashiZeroCorrectedCoefficient,
      h15MotohashiSignedKernel]
    rw [h15OppositeSignZeroCorrectedBilinearCoefficient_eq_completed]
    by_cases hn : n = 0
    · subst n
      simp
    · exact integral_oppositeSignTerm_eq_completedKernel N g q η c hn
/-- The orbital Dirichlet/Mellin series of one sign.  The completed-frequency
orbit remains finite inside each term, so no global sum exchange occurs. -/
noncomputable def h15MotohashiSignOrbitalSeries
    (N g q : ℕ) [NeZero q] (sign : H15MotohashiSign)
    (η c : ℝ) : ℂ :=
  ∑' n : ℕ, ∑ m : ZMod q,
    h15MotohashiArithmeticSeed N g q sign η c n m

theorem h15MotohashiSignOrbitalSeries_eq_zeroCorrected
    (N g q : ℕ) [NeZero q] (sign : H15MotohashiSign)
    (η c : ℝ) :
    h15MotohashiSignOrbitalSeries N g q sign η c =
      match sign with
      | .same => h15SameSignZeroCorrectedBilinearKernelSeries N g q η c
      | .opposite => h15OppositeSignZeroCorrectedBilinearKernelSeries N g q η c := by
  cases sign
  · unfold h15MotohashiSignOrbitalSeries
      h15SameSignZeroCorrectedBilinearKernelSeries
    apply tsum_congr
    intro n
    exact h15MotohashiArithmeticSeed_orbit_eq_zeroCorrected
      N g q .same η c n
  · unfold h15MotohashiSignOrbitalSeries
      h15OppositeSignZeroCorrectedBilinearKernelSeries
    apply tsum_congr
    intro n
    exact h15MotohashiArithmeticSeed_orbit_eq_zeroCorrected
      N g q .opposite η c n

/-- Both functional-equation signs, retained as a single arithmetic orbit. -/
noncomputable def h15MotohashiTwoSignOrbitalSeries
    (N g q : ℕ) [NeZero q] (η c : ℝ) : ℂ :=
  h15MotohashiSignOrbitalSeries N g q .same η c +
    h15MotohashiSignOrbitalSeries N g q .opposite η c

theorem h15MotohashiTwoSignOrbitalSeries_eq_zeroCorrected
    (N g q : ℕ) [NeZero q] (η c : ℝ) :
    h15MotohashiTwoSignOrbitalSeries N g q η c =
      h15TwoSignZeroCorrectedBilinearKernelSeries N g q η c := by
  unfold h15MotohashiTwoSignOrbitalSeries
    h15TwoSignZeroCorrectedBilinearKernelSeries
  rw [h15MotohashiSignOrbitalSeries_eq_zeroCorrected,
    h15MotohashiSignOrbitalSeries_eq_zeroCorrected]

/-- The complete finite-`N` arithmetic seed aggregate over gcd slices and
moduli. -/
noncomputable def h15MotohashiArithmeticSeedAggregate
    (N : ℕ) (η c : ℝ) : ℂ :=
  ∑ g ∈ Finset.Icc 1 N,
    ∑ q ∈ Finset.Icc 2 (N / g),
      if hq : 0 < q then
        @h15MotohashiTwoSignOrbitalSeries N g q
          ⟨Nat.ne_of_gt hq⟩ η c
      else 0

/-- BT1-A finite unfolding: the canonical H15 arithmetic seed recovers the
full zero-corrected bilinear aggregate exactly. -/
theorem h15MotohashiArithmeticSeedAggregate_eq_zeroCorrected
    (N : ℕ) (η c : ℝ) :
    h15MotohashiArithmeticSeedAggregate N η c =
      h15InteriorZeroCorrectedBilinearKernelAggregate N η c := by
  classical
  unfold h15MotohashiArithmeticSeedAggregate
    h15InteriorZeroCorrectedBilinearKernelAggregate
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro q hqmem
  have hq : 0 < q := by
    exact lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp hqmem).1
  rw [dif_pos hq, dif_pos hq]
  exact @h15MotohashiTwoSignOrbitalSeries_eq_zeroCorrected N g q
    ⟨Nat.ne_of_gt hq⟩ η c

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiSeed
